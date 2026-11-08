/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedCalendarMarkedPath
public import Bandits.Support.ReferenceGeneratedCalendarJointRebase
public import Bandits.Support.ReferenceGeneratedCalendarPathAgreement
public import Bandits.Support.ReferenceInitialStoppedCalendar
public import Bandits.Support.ReferenceFixedIDSourceSection

/-!
# Exhaustive terminal generated-calendar samples

The tags below retain the actual raw no-call, initially stopped, and generated
calendar samples, including their full original analytical tapes. Measures are
unnormalized on each source event. Only localization at the original positive
identification atom is normalized.

Sources: ZIP4 `06_interruptions.tex:391-426`,
`04_slow_fast_learner.tex:142-215,323-390`, and
`08_main_theorem.tex:78-109`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal Classical BigOperators
open Bandits.Support ConstructorDimensions
open ReferenceFirstLiveChronologicalPrefixFoundation
open ReferenceGeneratedRankCalendarFoundation
open ReferenceGeneratedCalendarResidualBlock
open ReferenceGeneratedCalendarPathAgreement
open ReferenceGeneratedCalendarJointRebase
open ReferencePostInvocationPrefixLocality (branchEvent)
open ReferenceSourcePrefixHistoryFiltration (sourcePrefix)

namespace Bandits.Support.ReferenceExhaustiveGeneratedCalendarSourceLaw

variable {p : ConstructorDimensions.Parameters}

abbrev Source := BootstrapPrivateRoundStreams.SourceInput
abbrev Auxiliary := ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray

local instance sourceMeasurableSpace : MeasurableSpace (Source p) := by
  change MeasurableSpace (CompletePublicTable.PublishedOutput p ×
    BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

local instance optionMeasurableSpace {A : Type*} [MeasurableSpace A] :
    MeasurableSpace (Option A) := LaterAssignmentStartMeasurability.optionMeasurableSpace
local instance slowSetMeasurableSpace : MeasurableSpace (SlowSet p) := ⊤
local instance slowSetDiscrete : DiscreteMeasurableSpace (SlowSet p) := ⟨fun _ => trivial⟩

private theorem measurable_sigma_mk {I : Type*} {B : I → Type*}
    [∀ i, MeasurableSpace (B i)] (i : I) : Measurable (Sigma.mk i : B i → Sigma B) :=
  measurable_iff_le_map.mpr (iInf_le _ i)

private theorem measurable_sigma_elim {I X : Type*} {B : I → Type*}
    [∀ i, MeasurableSpace (B i)] [MeasurableSpace X]
    (f : Sigma B → X) (hf : ∀ i, Measurable (fun x : B i => f ⟨i, x⟩)) : Measurable f := by
  intro U hU
  apply MeasurableSpace.measurableSet_iInf.mpr
  intro i
  exact hf i hU

private theorem measurable_present_get {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]
    (f : X → Option A) (hf : Measurable f) (h : ∀ x, (f x).isSome = true) :
    Measurable (fun x => (f x).get (h x)) := by
  have he : MeasurableEmbedding (@Sum.inl A PUnit) :=
    ⟨Sum.inl_injective, measurable_inl, fun _ hs => hs.inl_image⟩
  apply he.measurable_comp_iff.mp
  convert (comap_measurable (Equiv.optionEquivSumPUnit A)).comp hf using 1
  funext x
  cases hx : f x with
  | none => have := h x; simp only [hx, Option.isSome_none, Bool.false_eq_true] at this
  | some a => simp only [Function.comp_apply, hx]; rfl

/-- Finite labels for the existing raw alternatives, including zero-mass ones. -/
inductive Component (p : ConstructorDimensions.Parameters)
  | noCall
  | stopped (u t : Fin p.T)
  | generated (b : Bool) (u t : Fin p.T)
  deriving DecidableEq, Fintype

variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)

local notation "mu" => BootstrapPrivateRoundStreams.sourceInputLaw p
local notation "alpha" => ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p
local notation "N" => ReferenceFirstCollectionAuxiliarySeeds.noCollectionCallEvent rate rewards C_star C_h
local notation "S" => ReferenceInitialStoppedCalendar.initialStoppedEvent rate rewards C_star C_h
local notation "B" => branchEvent rate rewards C_star C_h
local notation "firstCell" => ReferenceFirstCollectionAuxiliarySeeds.actualCollectionCallCell rate rewards C_star C_h

/-- Actual original-source event of a raw component. -/
def componentEvent : Component p → Set (Source p)
  | .noCall => N
  | .stopped u t => S u t
  | .generated b u t => B b u t

theorem measurableSet_componentEvent (i : Component p) :
    MeasurableSet (componentEvent rate rewards C_star C_h i) := by
  cases i with
  | noCall => exact ReferenceFirstCollectionAuxiliarySeeds.measurableSet_noCollectionCallEvent rate rewards C_star C_h
  | stopped u t => exact ReferenceInitialStoppedCalendar.measurableSet_initialStoppedEvent rate rewards C_star C_h u t
  | generated b u t =>
    cases b with
    | false => exact ReferenceFirstLiveCollectionPathJoin.measurableSet_firstLiveCollectionEvent rate rewards C_star C_h u t
    | true => exact ReferenceFirstCollectionRenewalAuxiliaryLaw.measurableSet_renewalCallEvent rate rewards C_star C_h u t

private theorem branch_subset_firstCell (b : Bool) (u t : Fin p.T) :
    B b u t ⊆ firstCell u t := by
  intro z hz
  cases b with
  | false => exact (ReferenceFirstLiveCollectionPathJoin.firstLiveCollectionEvent_facts rate rewards C_star C_h u t z hz).1
  | true => exact hz.1

/-- The stored incoming ledger supplies the boundary; the actual complete
word supplies a present numerical PRE. No missing-PRE alternative is added. -/
theorem firstCell_refinement (u t : Fin p.T) (z : Source p) (hz : z ∈ firstCell u t) :
    z ∈ S u t ∨ z ∈ B false u t ∨ z ∈ B true u t := by
  obtain ⟨n, r, theta, hr, htime, _har, hcall, _⟩ :=
    ReferenceFirstCollectionCallStoredBounds.firstCell_stored_bounds rate rewards C_star C_h u t z hz
  obtain ⟨payload, ledger, saved, hcoord, _⟩ :=
    (ReferenceFirstCollectionSamplerCall.collectionCallAt_spec r u theta).mp hcall
  have hg := ReferenceFirstCollectionRenewalAuxiliaryLaw.oldFreezeAt?_eq_of_record
    rate rewards C_star C_h t z r (List.mem_of_getElem? hr) htime payload ledger saved hcoord
  by_cases hle : ledger.freezeAt ≤ t.val + 1
  · exact Or.inr (Or.inr ⟨hz, ledger.freezeAt, hg, hle⟩)
  · have hcorrected : z ∈ ReferenceFirstCollectionCorrectedSliceNumericalPrefix.correctedCell
        rate rewards C_star C_h u t := ⟨hz, ledger.freezeAt, hg, by omega⟩
    have hd := ReferenceFirstCollectionLogicalNumericalAlignment.firstCall_dates rate rewards C_star C_h u t z hz
    have hp := (ReferenceFirstCollectionLogicalNumericalAlignment.originalWord_calendar_prefix rate rewards C_star C_h z
      (ReferenceFirstCollectionLogicalNumericalAlignment.firstCall_launch rate rewards C_star C_h u t z hz)
      t.castSucc (by simpa only [Fin.val_castSucc] using hd.1.trans hd.2.1.le)).2.2
    let W := ReferenceActualCollectionHiddenRefreshPath.actualOriginalWord rate rewards C_star C_h z
      (ReferenceFirstCollectionLogicalNumericalAlignment.firstCall_launch rate rewards C_star C_h u t z hz)
    let o := ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
      (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate)
        (W.take (t.val - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)))
    have ho : ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout rate rewards C_star C_h t.val z = some o := by
      simp only [Fin.val_castSucc] at hp
      rw [ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout, hp]
      rfl
    cases hs : o.2.1 with
    | false =>
      right; left
      change z ∈ ReferenceFirstLiveCollectionPathJoin.firstLiveCollectionEvent rate rewards C_star C_h u t
      rw [ReferenceFirstLiveCollectionPathJoin.firstLiveCollectionEvent_eq_correctedCell]
      exact ⟨hcorrected, o, ho, hs⟩
    | true => exact Or.inl ⟨hcorrected, o, ho, hs⟩

theorem componentEvent_cover : (⋃ i, componentEvent rate rewards C_star C_h i) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro z
  rcases ReferenceFirstCollectionSamplerOutputLaw.firstCell_cover_or_noCall rate rewards C_star C_h z with hn | ⟨u, t, hz⟩
  · exact Set.mem_iUnion.mpr ⟨.noCall, hn⟩
  · rcases firstCell_refinement rate rewards C_star C_h u t z hz with hs | hb | hb
    · exact Set.mem_iUnion.mpr ⟨.stopped u t, hs⟩
    · exact Set.mem_iUnion.mpr ⟨.generated false u t, hb⟩
    · exact Set.mem_iUnion.mpr ⟨.generated true u t, hb⟩

private theorem firstCell_tags (u t u' t' : Fin p.T) (z : Source p)
    (h : z ∈ firstCell u t) (h' : z ∈ firstCell u' t') : (u, t) = (u', t') :=
  Option.some.inj (h.symm.trans h')

private theorem branch_false_true_disjoint (u t : Fin p.T) : Disjoint (B false u t) (B true u t) := by
  apply Set.disjoint_left.mpr
  intro z hf ht
  change z ∈ ReferenceFirstLiveCollectionPathJoin.firstLiveCollectionEvent rate rewards C_star C_h u t at hf
  rw [ReferenceFirstLiveCollectionPathJoin.firstLiveCollectionEvent_eq_correctedCell] at hf
  obtain ⟨g, hg, hgt⟩ := hf.1.2
  obtain ⟨g', hg', hle⟩ := ht.2
  have heq : g = g' := Option.some.inj (hg.symm.trans hg')
  omega

theorem componentEvent_pairwise : Pairwise (fun i j => Disjoint (componentEvent rate rewards C_star C_h i) (componentEvent rate rewards C_star C_h j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro z hi hj
  have hn (u t : Fin p.T) (hN : z ∈ N) (hF : z ∈ firstCell u t) : False :=
    Set.disjoint_left.mp (ReferenceFirstCollectionSamplerOutputLaw.noCall_disjoint_firstCell rate rewards C_star C_h u t) hN hF
  cases i with
  | noCall =>
    cases j with
    | noCall => exact hij rfl
    | stopped u t => exact hn u t hi hj.1.1
    | generated b u t => exact hn u t hi (branch_subset_firstCell rate rewards C_star C_h b u t hj)
  | stopped u t =>
    cases j with
    | noCall => exact hn u t hj hi.1.1
    | stopped u' t' =>
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (firstCell_tags rate rewards C_star C_h u t u' t' z hi.1.1 hj.1.1)
      exact hij rfl
    | generated b u' t' =>
      exact Set.disjoint_left.mp
        (ReferenceInitialStoppedCalendar.initialStoppedEvent_disjoint_branch rate rewards C_star C_h u t u' t' b) hi hj
  | generated b u t =>
    have hfi := branch_subset_firstCell rate rewards C_star C_h b u t hi
    cases j with
    | noCall => exact hn u t hj hfi
    | stopped u' t' =>
      exact Set.disjoint_left.mp
        (ReferenceInitialStoppedCalendar.initialStoppedEvent_disjoint_branch rate rewards C_star C_h u' t' u t b) hj hi
    | generated b' u' t' =>
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (firstCell_tags rate rewards C_star C_h u t u' t' z hfi
        (branch_subset_firstCell rate rewards C_star C_h b' u' t' hj))
      cases b <;> cases b'
      · exact hij rfl
      · exact Set.disjoint_left.mp (branch_false_true_disjoint rate rewards C_star C_h u t) hi hj
      · exact Set.disjoint_left.mp (branch_false_true_disjoint rate rewards C_star C_h u t) hj hi
      · exact hij rfl

/-- Finite disjoint refinement of any source measure, with the actual events. -/
theorem sum_restrict_componentEvent (nu : Measure (Source p)) :
    Measure.sum (fun i => nu.restrict (componentEvent rate rewards C_star C_h i)) = nu := by
  rw [← Measure.restrict_iUnion (componentEvent_pairwise rate rewards C_star C_h)
    (measurableSet_componentEvent rate rewards C_star C_h), componentEvent_cover, Measure.restrict_univ]

/-- Raw payloads are the existing objects, without forgetting any vectors or tape. -/
abbrev Payload : Component p → Type
  | .noCall => ↥N × Auxiliary p
  | .stopped u t => ReferenceInitialStoppedCalendar.StoppedSource rate rewards C_star C_h u t × Auxiliary p
  | .generated b u t => CalendarSample rate rewards C_star C_h b u t (p.T - (t.val + 1))

instance payloadMeasurableSpace (i : Component p) : MeasurableSpace (Payload rate rewards C_star C_h i) := by
  cases i <;> unfold Payload <;> infer_instance

/-- The literal disjoint finite-tag raw carrier. -/
abbrev Omega := Sigma (Payload rate rewards C_star C_h)

variable (control0 : ContinuousLearningRows.TimeControl p)

def componentLaw : (i : Component p) → Measure (Payload rate rewards C_star C_h i)
  | .noCall => ((mu).comap Subtype.val).prod alpha
  | .stopped u t => ReferenceInitialStoppedCalendar.initialStoppedSourceLaw rate rewards C_star C_h u t
  | .generated b u t => generatedCalendarLaw rate rewards C_star C_h control0 b u t (Fin.last p.T) t.isLt

/-- The original raw components are injected with their exact original masses. -/
def terminalLaw : Measure (Omega rate rewards C_star C_h) :=
  Measure.sum (fun i => (componentLaw rate rewards C_star C_h control0 i).map (Sigma.mk i))

def componentSource : (i : Component p) → Payload rate rewards C_star C_h i → Source p
  | .noCall, w => w.1.val
  | .stopped _ _, w => w.1.val
  | .generated b u t, w => calendarCurrentSource rate rewards C_star C_h control0 b u t
      (p.T - (t.val + 1)) (by omega) w

theorem measurable_componentSource (i : Component p) :
    Measurable (componentSource rate rewards C_star C_h control0 i) := by
  cases i with
  | noCall => exact measurable_subtype_coe.comp measurable_fst
  | stopped u t => exact measurable_subtype_coe.comp measurable_fst
  | generated b u t => exact measurable_calendarCurrentSource rate rewards C_star C_h control0 b u t _ _

def terminalSource (w : Omega rate rewards C_star C_h) : Source p :=
  componentSource rate rewards C_star C_h control0 w.1 w.2

theorem measurable_terminalSource : Measurable (terminalSource rate rewards C_star C_h control0) :=
  measurable_sigma_elim _ (measurable_componentSource rate rewards C_star C_h control0)

theorem noCallLaw_originalPair :
    (componentLaw rate rewards C_star C_h control0 .noCall).map (fun w => (w.1.val, w.2)) =
      ((mu).restrict N).prod alpha := by
  change ((((mu).comap (Subtype.val : ↥N → Source p)).prod alpha).map (Prod.map Subtype.val id)) = _
  rw [← Measure.map_prod_map _ _ measurable_subtype_coe measurable_id, Measure.map_id,
    map_comap_subtype_coe (ReferenceFirstCollectionAuxiliarySeeds.measurableSet_noCollectionCallEvent rate rewards C_star C_h)]

theorem componentLaw_map_source (i : Component p) :
    (componentLaw rate rewards C_star C_h control0 i).map (componentSource rate rewards C_star C_h control0 i) =
      (mu).restrict (componentEvent rate rewards C_star C_h i) := by
  cases i with
  | noCall =>
    have h := congrArg Measure.fst (noCallLaw_originalPair rate rewards C_star C_h control0)
    rw [Measure.fst, Measure.map_map measurable_fst
      ((show Measurable (fun w : Payload rate rewards C_star C_h .noCall => w.1.val) from measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd)] at h
    rw [Measure.fst_prod] at h
    exact h
  | stopped u t =>
    have h := congrArg Measure.fst (ReferenceInitialStoppedCalendar.initialStoppedSourceLaw_originalPair rate rewards C_star C_h u t)
    rw [Measure.fst_map_prodMk (show Measurable (fun w : ReferenceInitialStoppedCalendar.StoppedSource rate rewards C_star C_h u t × Auxiliary p => w.1.val) from measurable_subtype_coe.comp measurable_fst) measurable_snd, Measure.fst_prod] at h
    exact h
  | generated b u t => exact generatedCalendarLaw_map_currentSource rate rewards C_star C_h control0 b u t (Fin.last p.T) t.isLt

theorem terminalLaw_map_source :
    (terminalLaw rate rewards C_star C_h control0).map (terminalSource rate rewards C_star C_h control0) = mu := by
  rw [terminalLaw, Measure.map_sum (measurable_terminalSource rate rewards C_star C_h control0).aemeasurable]
  simp_rw [Measure.map_map (measurable_terminalSource rate rewards C_star C_h control0) (measurable_sigma_mk _)]
  change Measure.sum (fun i => (componentLaw rate rewards C_star C_h control0 i).map
    (componentSource rate rewards C_star C_h control0 i)) = _
  simp_rw [componentLaw_map_source]
  exact sum_restrict_componentEvent rate rewards C_star C_h mu

/-- Extract only the already proved present list from the existing observer. -/
def taggedStoredList {n : Fin (p.T + 1)} (o : TaggedPrefix rate n) : List (LogicalCell p rate) :=
  ((o.2.val.2.2.2).get o.2.property).2

theorem measurable_taggedStoredList (n : Fin (p.T + 1)) :
    Measurable (taggedStoredList (p := p) rate (n := n)) := by
  apply measurable_sigma_elim
  intro s
  exact (measurable_present_get
    (fun x : PresentPrefix rate s n => x.val.2.2.2)
    measurable_subtype_coe.snd.snd.snd (fun x => x.property)).snd

/-- The common readout keeps the complete original tape, not just label zero. -/
def componentReadout : (i : Component p) → Payload rate rewards C_star C_h i →
    ReferenceInitialStoppedCalendar.Observer rate
  | .noCall, w => (w.1.val, (w.2,
      ReferenceFirstCollectionLogicalPrefixExtension.extendedPast rate rewards C_star C_h (Fin.last p.T) (w.1.val, w.2)))
  | .stopped u t, w => (w.1.val, (w.2,
      ReferenceInitialStoppedCalendar.initialStoppedPast rate rewards C_star C_h control0 u t (Fin.last p.T) w))
  | .generated b u t, w =>
      (calendarCurrentSource rate rewards C_star C_h control0 b u t (p.T - (t.val + 1)) (by omega) w,
        ((calendarOriginalLift rate rewards C_star C_h b u t (p.T - (t.val + 1)) w).1.2,
          (calendarStoredState rate rewards C_star C_h control0 b u t (p.T - (t.val + 1)) (by omega) w).2))

theorem measurable_componentReadout (i : Component p) :
    Measurable (componentReadout rate rewards C_star C_h control0 i) := by
  cases i with
  | noCall =>
    exact (measurable_subtype_coe.comp measurable_fst).prodMk
      (measurable_snd.prodMk ((ReferenceFirstCollectionLogicalPrefixExtension.measurable_extendedPast
        rate rewards C_star C_h control0 (Fin.last p.T)).comp
          ((measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd)))
  | stopped u t =>
    exact (measurable_subtype_coe.comp measurable_fst).prodMk
      (measurable_snd.prodMk (ReferenceInitialStoppedCalendar.measurable_initialStoppedPast
        rate rewards C_star C_h control0 u t (Fin.last p.T)))
  | generated b u t =>
    exact (measurable_calendarCurrentSource rate rewards C_star C_h control0 b u t _ _).prodMk
      ((measurable_calendarOriginalLift rate rewards C_star C_h b u t _).fst.snd.prodMk
        ((measurable_taggedStoredList rate _).comp
          (measurable_calendarObservation rate rewards C_star C_h control0 b u t _ _)))

def terminalReadout (w : Omega rate rewards C_star C_h) : ReferenceInitialStoppedCalendar.Observer rate :=
  componentReadout rate rewards C_star C_h control0 w.1 w.2

theorem measurable_terminalReadout : Measurable (terminalReadout rate rewards C_star C_h control0) :=
  measurable_sigma_elim _ (measurable_componentReadout rate rewards C_star C_h control0)

theorem terminalReadout_source (w : Omega rate rewards C_star C_h) :
    (terminalReadout rate rewards C_star C_h control0 w).1 = terminalSource rate rewards C_star C_h control0 w := by
  rcases w with ⟨i, w⟩
  cases i <;> rfl

/-- The full correlated common-observer law. Its raw carrier remains available. -/
def terminalReadoutLaw : Measure (ReferenceInitialStoppedCalendar.Observer rate) :=
  (terminalLaw rate rewards C_star C_h control0).map (terminalReadout rate rewards C_star C_h control0)

theorem terminalReadoutLaw_source :
    (terminalReadoutLaw rate rewards C_star C_h control0).map Prod.fst = mu := by
  rw [terminalReadoutLaw, Measure.map_map measurable_fst
    (measurable_terminalReadout rate rewards C_star C_h control0)]
  simpa only [Function.comp_def, terminalReadout_source] using
    terminalLaw_map_source rate rewards C_star C_h control0

/-- Exact graph law of the full original no-call source/tape pair. -/
theorem noCallLaw_readout :
    (componentLaw rate rewards C_star C_h control0 .noCall).map
      (componentReadout rate rewards C_star C_h control0 .noCall) =
      (((mu).restrict N).prod alpha).map (fun za =>
        (za.1, (za.2, ReferenceFirstCollectionLogicalPrefixExtension.extendedPast
          rate rewards C_star C_h (Fin.last p.T) za))) := by
  rw [← noCallLaw_originalPair rate rewards C_star C_h control0]
  exact (Measure.map_map
    (measurable_fst.prodMk (measurable_snd.prodMk
      (ReferenceFirstCollectionLogicalPrefixExtension.measurable_extendedPast rate rewards C_star C_h control0 (Fin.last p.T))))
    ((show Measurable (fun w : Payload rate rewards C_star C_h .noCall => w.1.val) from
      measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd)
    (μ := componentLaw rate rewards C_star C_h control0 .noCall)).symm

/-- The stopped graph is the admitted full-source chronological law. -/
theorem stoppedLaw_readout (u t : Fin p.T) :
    (componentLaw rate rewards C_star C_h control0 (.stopped u t)).map
      (componentReadout rate rewards C_star C_h control0 (.stopped u t)) =
      ReferenceInitialStoppedCalendar.initialStoppedChronologicalLaw rate rewards C_star C_h control0 u t (Fin.last p.T) :=
  ReferenceInitialStoppedCalendar.initialStopped_fullSource_jointLaw rate rewards C_star C_h control0 u t (Fin.last p.T) t.isLt.le

/-- Consume the full joint raw/archive rebase and project its retained raw
sample to the common readout. The nested raw sample already contains the
whole archived list; no independent source/archive marginals are multiplied. -/
theorem generatedLaw_readout (b : Bool) (u t : Fin p.T) :
    (componentLaw rate rewards C_star C_h control0 (.generated b u t)).map
      (componentReadout rate rewards C_star C_h control0 (.generated b u t)) =
      (generatedCalendarJointSpliceLaw rate rewards C_star C_h control0 b u t (Fin.last p.T) t.isLt).map
        (fun x => componentReadout rate rewards C_star C_h control0 (.generated b u t) x.1) := by
  rw [← generatedCalendarLaw_joint_rebase rate rewards C_star C_h control0 b u t (Fin.last p.T) t.isLt]
  exact (Measure.map_map
    ((measurable_componentReadout rate rewards C_star C_h control0 (.generated b u t)).comp measurable_fst)
    (measurable_id.prodMk (measurable_generatedCalendarObservation rate rewards C_star C_h control0 b u t
      (Fin.last p.T) t.isLt))).symm

/-- Componentwise readout equation for the exhaustive law. -/
theorem terminalReadoutLaw_components :
    terminalReadoutLaw rate rewards C_star C_h control0 =
      Measure.sum (fun i => (componentLaw rate rewards C_star C_h control0 i).map
        (componentReadout rate rewards C_star C_h control0 i)) := by
  rw [terminalReadoutLaw, terminalLaw,
    Measure.map_sum (measurable_terminalReadout rate rewards C_star C_h control0).aemeasurable]
  simp_rw [Measure.map_map (measurable_terminalReadout rate rewards C_star C_h control0) (measurable_sigma_mk _)]
  rfl

/-- Normalize only the original ID atom on each actual terminal source. -/
def fixedIDComponentLaw (ids : CompletePublicTable.IDArray p) (i : Component p) :
    Measure (Payload rate rewards C_star C_h i) :=
  (CompletePublicTable.idArrayMeasure p {ids})⁻¹ •
    (componentLaw rate rewards C_star C_h control0 i).restrict
      (componentSource rate rewards C_star C_h control0 i ⁻¹'
        ReferenceFixedIDSourceSection.fixedIDSourceSection ids)

private theorem idAtom_ne_zero (ids : CompletePublicTable.IDArray p) :
    CompletePublicTable.idArrayMeasure p {ids} ≠ 0 := by
  have hp := ReferenceFixedIDSourceSection.idArrayAtom_positive (p := p) ids
  exact (ENNReal.toReal_pos_iff.mp hp).1.ne'

theorem fixedIDComponentLaw_map_source (ids : CompletePublicTable.IDArray p) (i : Component p) :
    (fixedIDComponentLaw rate rewards C_star C_h control0 ids i).map
      (componentSource rate rewards C_star C_h control0 i) =
      (ReferenceFixedIDSourceSection.fixedIDSourceLaw ids).restrict (componentEvent rate rewards C_star C_h i) := by
  rw [fixedIDComponentLaw, Measure.map_smul _ ((measurable_componentSource rate rewards C_star C_h control0 i).aemeasurable),
    ← Measure.restrict_map (measurable_componentSource rate rewards C_star C_h control0 i)
      (ReferenceFixedIDSourceSection.measurable_fixedIDSourceSection ids), componentLaw_map_source,
    Measure.restrict_comm,
    ReferenceFixedIDSourceSection.sourceInputLaw_restrict_fixedIDSourceSection,
    Measure.restrict_smul, smul_smul,
    ENNReal.inv_mul_cancel (idAtom_ne_zero ids)
      (ReferenceFixedIDSourceSection.idArrayAtom_lt_top (p := p) ids).ne, one_smul]
  exact ReferenceFixedIDSourceSection.measurable_fixedIDSourceSection ids

/-- The same injections and raw payloads after localization. -/
def fixedIDTerminalLaw (ids : CompletePublicTable.IDArray p) : Measure (Omega rate rewards C_star C_h) :=
  Measure.sum (fun i => (fixedIDComponentLaw rate rewards C_star C_h control0 ids i).map (Sigma.mk i))

theorem fixedIDTerminalLaw_map_source (ids : CompletePublicTable.IDArray p) :
    (fixedIDTerminalLaw rate rewards C_star C_h control0 ids).map
      (terminalSource rate rewards C_star C_h control0) = ReferenceFixedIDSourceSection.fixedIDSourceLaw ids := by
  rw [fixedIDTerminalLaw, Measure.map_sum (measurable_terminalSource rate rewards C_star C_h control0).aemeasurable]
  simp_rw [Measure.map_map (measurable_terminalSource rate rewards C_star C_h control0) (measurable_sigma_mk _)]
  change Measure.sum (fun i => (fixedIDComponentLaw rate rewards C_star C_h control0 ids i).map
    (componentSource rate rewards C_star C_h control0 i)) = _
  simp_rw [fixedIDComponentLaw_map_source]
  exact sum_restrict_componentEvent rate rewards C_star C_h _

/-- Equivalent global restriction, with no normalization by component mass. -/
theorem fixedIDTerminalLaw_eq_restrict (ids : CompletePublicTable.IDArray p) :
    fixedIDTerminalLaw rate rewards C_star C_h control0 ids =
      (CompletePublicTable.idArrayMeasure p {ids})⁻¹ •
        (terminalLaw rate rewards C_star C_h control0).restrict
          (terminalSource rate rewards C_star C_h control0 ⁻¹'
            ReferenceFixedIDSourceSection.fixedIDSourceSection ids) := by
  have hE := (ReferenceFixedIDSourceSection.measurable_fixedIDSourceSection (p := p) ids).preimage
    (measurable_terminalSource rate rewards C_star C_h control0)
  rw [fixedIDTerminalLaw, terminalLaw, Measure.restrict_sum _ hE]
  simp_rw [Measure.restrict_map (measurable_sigma_mk _) hE]
  simp only [fixedIDComponentLaw]
  rw [Measure.sum_fintype, Measure.sum_fintype, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact Measure.map_smul _ (measurable_sigma_mk i).aemeasurable

def fixedIDReadoutLaw (ids : CompletePublicTable.IDArray p) : Measure (ReferenceInitialStoppedCalendar.Observer rate) :=
  (fixedIDTerminalLaw rate rewards C_star C_h control0 ids).map (terminalReadout rate rewards C_star C_h control0)

theorem fixedIDReadoutLaw_source (ids : CompletePublicTable.IDArray p) :
    (fixedIDReadoutLaw rate rewards C_star C_h control0 ids).map Prod.fst =
      ReferenceFixedIDSourceSection.fixedIDSourceLaw ids := by
  rw [fixedIDReadoutLaw, Measure.map_map measurable_fst (measurable_terminalReadout rate rewards C_star C_h control0)]
  simpa only [Function.comp_def, terminalReadout_source] using
    fixedIDTerminalLaw_map_source rate rewards C_star C_h control0 ids

/-- Original-source tests transfer through the actual terminal source only. -/
theorem terminalLaw_source_test (F : Source p → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ w, F (terminalSource rate rewards C_star C_h control0 w) ∂terminalLaw rate rewards C_star C_h control0) =
      ∫⁻ z, F z ∂mu := by
  rw [← lintegral_map hF (measurable_terminalSource rate rewards C_star C_h control0), terminalLaw_map_source]

theorem fixedIDTerminalLaw_source_test (ids : CompletePublicTable.IDArray p) (F : Source p → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ w, F (terminalSource rate rewards C_star C_h control0 w) ∂fixedIDTerminalLaw rate rewards C_star C_h control0 ids) =
      ∫⁻ z, F z ∂ReferenceFixedIDSourceSection.fixedIDSourceLaw ids := by
  rw [← lintegral_map hF (measurable_terminalSource rate rewards C_star C_h control0), fixedIDTerminalLaw_map_source]

theorem fixedIDTerminalLaw_integrable_source_iff (ids : CompletePublicTable.IDArray p)
    (F : Source p → ℝ) (hF : Measurable F) :
    Integrable (fun w => F (terminalSource rate rewards C_star C_h control0 w))
      (fixedIDTerminalLaw rate rewards C_star C_h control0 ids) ↔
        Integrable F (ReferenceFixedIDSourceSection.fixedIDSourceLaw ids) := by
  rw [← fixedIDTerminalLaw_map_source rate rewards C_star C_h control0 ids]
  exact (integrable_map_measure hF.aestronglyMeasurable
    (measurable_terminalSource rate rewards C_star C_h control0).aemeasurable).symm

theorem fixedIDTerminalLaw_source_integral (ids : CompletePublicTable.IDArray p)
    (F : Source p → ℝ) (hF : Measurable F) :
    (∫ w, F (terminalSource rate rewards C_star C_h control0 w) ∂fixedIDTerminalLaw rate rewards C_star C_h control0 ids) =
      ∫ z, F z ∂ReferenceFixedIDSourceSection.fixedIDSourceLaw ids := by
  rw [← fixedIDTerminalLaw_map_source rate rewards C_star C_h control0 ids]
  exact (integral_map (measurable_terminalSource rate rewards C_star C_h control0).aemeasurable
    hF.aestronglyMeasurable).symm

/-- At the horizon the killed-law survival event is exactly actual no-call. -/
theorem noCallBefore_terminal_iff (z : Source p) :
    ReferenceFirstCollectionLogicalPrefixExtension.NoCallBefore rate rewards C_star C_h (Fin.last p.T) z ↔ z ∈ N := by
  constructor
  · intro hall
    rcases ReferenceFirstCollectionSamplerOutputLaw.firstCell_cover_or_noCall rate rewards C_star C_h z with hn | ⟨u, t, ht⟩
    · exact hn
    · obtain ⟨_n, r, theta, _hr, _htime, har, hc, _⟩ :=
        ReferenceFirstCollectionCurrentNumericalCell.firstCell_record rate rewards C_star C_h u t z ht
      have hn := (ReferenceFirstCollectionLogicalPrefixExtension.noCallAt_iff_callAt_none rate rewards C_star C_h t z).mp (hall t t.isLt)
      rw [ReferenceCalendarCollectionCallControlLaw.callAt, har, Option.bind_some, hc] at hn
      cases hn
  · intro hn q _hq
    rw [ReferenceFirstCollectionLogicalPrefixExtension.noCallAt_iff_callAt_none,
      ReferenceCalendarCollectionCallControlLaw.callAt]
    cases hr : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h q z with
    | none => rfl
    | some r =>
      have hm : r ∈ ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h := by
        unfold ReferenceSourcePrefixHistoryFiltration.actualRecord at hr
        split at hr
        · exact List.mem_of_getElem? hr
        · cases hr
      have hp := (ReferenceFirstCollectionSamplerCall.firstCollectionCall_none_iff (rate := rate) rewards C_star C_h z).mp hn r hm
      exact (ReferenceFirstCollectionSamplerCall.collectionCallAt_none_iff r).mpr hp

/-- Full-tape no-call graph projects to the existing killed observer; no
label-one tape is reconstructed from that coarse observer. -/
theorem noCallLaw_coarse :
    ((componentLaw rate rewards C_star C_h control0 .noCall).map
      (componentReadout rate rewards C_star C_h control0 .noCall)).map
        (ReferenceInitialStoppedCalendar.coarseProjection rate) =
      ReferenceFirstCollectionLogicalPrefixExtension.betaPre rate rewards C_star C_h control0 (Fin.last p.T) := by
  rw [noCallLaw_readout,
    Measure.map_map (ReferenceInitialStoppedCalendar.measurable_coarseProjection rate)
      (measurable_fst.prodMk (measurable_snd.prodMk
        (ReferenceFirstCollectionLogicalPrefixExtension.measurable_extendedPast rate rewards C_star C_h control0 (Fin.last p.T))))]
  have hE : N ×ˢ (Set.univ : Set (Auxiliary p)) =
      {za : Source p × Auxiliary p | ReferenceFirstCollectionLogicalPrefixExtension.NoCallBefore rate rewards C_star C_h (Fin.last p.T) za.1} := by
    ext za
    simp only [Set.mem_prod, Set.mem_univ, and_true, Set.mem_ofPred_eq, noCallBefore_terminal_iff]
  rw [Measure.restrict_prod_eq_prod_univ, hE]
  convert ReferenceFirstCollectionLogicalPrefixExtension.extendedObservation_map_restrict_eq_betaPre
    rate rewards C_star C_h control0 (Fin.last p.T) using 1
  congr 1
  funext za
  dsimp only [Function.comp_def, ReferenceInitialStoppedCalendar.coarseProjection,
    ReferenceFirstCollectionLogicalPrefixExtension.extendedObservation, Fin.val_last]
  rw [ReferenceSourcePrefixHistoryFiltration.sourcePrefix_eq_self control0 p.T le_rfl]

/-- Every calendar insertion preserves exactly the original ID and private
coordinates. Equality of whole original and current sources is not asserted. -/
theorem calendarCurrentSource_original_ids_private (b : Bool) (u t : Fin p.T)
    (k : ℕ) (hk : t.val + 1 + k ≤ p.T)
    (w : CalendarSample rate rewards C_star C_h b u t k) :
    (calendarCurrentSource rate rewards C_star C_h control0 b u t k hk w).1.1 =
        (calendarOriginalLift rate rewards C_star C_h b u t k w).1.1.val.1.1 ∧
      (calendarCurrentSource rate rewards C_star C_h control0 b u t k hk w).2 =
        (calendarOriginalLift rate rewards C_star C_h b u t k w).1.1.val.2 := by
  induction k with
  | zero =>
    change ReferencePostInvocationPrefixLocality.BranchLift rate rewards C_star C_h b u t at w
    change (ReferencePostInvocationPrefixLocality.branchObservation rate rewards C_star C_h control0 b u t t.succ w).1.1.1.2.1.1 = _ ∧
      (ReferencePostInvocationPrefixLocality.branchObservation rate rewards C_star C_h control0 b u t t.succ w).1.1.1.2.2 = _
    rw [ReferencePostInvocationKilledJointLaw.branchObservation_source]
    cases b with
    | false => exact (ReferenceFirstCollectionRenewalVectorInsertion.insert_identity_private_selector t w.1.1.val w.2).imp_right fun h => h.1
    | true => exact (ReferenceFirstCollectionRenewalVectorInsertion.insert_identity_private_selector t w.1.1.val w.2).imp_right fun h => h.1
  | succ k ih =>
    change CalendarSample rate rewards C_star C_h b u t k × AssignmentParameterFibreKernel.AssignmentVector p at w
    have hprev := ih (by omega) w.1
    rw [calendarCurrentSource_succ rate rewards C_star C_h control0 b u t k (by omega)]
    split
    · have hi := ReferenceFirstCollectionRenewalVectorInsertion.insert_identity_private_selector
        (⟨t.val + 1 + k, by omega⟩ : Fin p.T)
        (calendarCurrentSource rate rewards C_star C_h control0 b u t k (by omega) w.1) w.2
      exact ⟨hi.1.trans hprev.1, hi.2.1.trans hprev.2⟩
    · exact hprev

local notation "start " z:max => ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
local notation "records " z:max => ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
local notation "live " za:max => firstLiveChronologicalPrefix rate rewards C_star C_h za
local notation "past" => ReferenceFirstCollectionLogicalPrefixExtension.extendedPast rate rewards C_star C_h
local notation "stateAt" => ReferenceFirstCollectionLogicalPrefixExtension.extendedPrefixStateAux rate rewards C_star C_h
local notation "Q" => ReferenceFirstLaunchNumericalCell.queueParameters rate
local notation "originalWord" => ReferenceActualCollectionHiddenRefreshPath.actualOriginalWord rate rewards C_star C_h
local notation "cut " z:max => ReferenceFirstCollectionLogicalPrefixExtension.collectionStart rate rewards C_star C_h z

private theorem live_readout_input (r : Record rate)
    (cell : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell r)
    (d : RecordedQueueRun.RoundInput p.K)
    (hd : ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 r = some d) : cell.input = d := by
  obtain ⟨selected, ho, hs, _hsigma, _hlive, hinput⟩ :=
    ReferenceLaterLiveNumericalReadout.laterLiveReadout_some 0 r d hd
  have heq : selected = cell.selected := Option.some.inj (hs.symm.trans cell.selection_actual)
  subst selected
  have hstates : ReferenceLaterLiveNumericalReadout.preparedStates r ho = cell.states := by
    funext i
    have h := (ReferenceLaterLiveNumericalReadout.prepared_configuration r ho i).symm.trans (cell.ordinary i)
    injection h
  rw [cell.input_eq, hinput, hstates]

/-- The canonical first-LIVE word is the prefix of the actual original word
on any produced launch, including paths with no first invocation. -/
theorem originalWord_liveWord (z : Source p)
    (hl : ∃ active, ReferenceCorrectedInitializationLaunch.correctedLaunch rate z rewards C_star C_h = some active) :
    ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells rate rewards C_star C_h z =
      (originalWord z hl).take (ReferenceFirstLiveOverflowReadout.wholeFirstLiveLength rate rewards C_star C_h z) := by
  have hc := (ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing rate z rewards C_star C_h).mp
    (by rw [Classical.choose_spec hl]; rfl)
  have hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true := hc
  obtain ⟨_seed, _hstart, hcells⟩ := ReferenceCompleteFirstPhaseObservationRecovery.actualFirstLiveRawObservationIdentity
    rate rewards C_star C_h z hcross
  have hwindow : ReferenceFirstWindowNumericalStream.actualFirstLiveWindow rate z rewards C_star C_h hcross
      (p.T - start z) (ReferenceCompleteFirstPhaseObservationRecovery.firstPhaseSpan rate rewards C_star C_h z) =
      ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow rate rewards C_star C_h z := by
    unfold ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
    change ReferenceFirstLiveConfirmationHistory.firstLiveWindow _ = ReferenceFirstLiveConfirmationHistory.firstLiveWindow _
    rw [← ReferenceCompleteFirstPhaseObservationRecovery.completeSuffixRecords_eq_actualFirstLiveRun rate rewards C_star C_h z hcross]
  have hprefix : ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow rate rewards C_star C_h z <+: records z := List.takeWhile_prefix _
  have hmap := ReferenceFirstCollectionLogicalNumericalAlignment.originalWord_record_map rate rewards C_star C_h z hl
  have hlen := congrArg List.length hmap
  simp only [List.length_map] at hlen
  apply List.ext_getElem
  · rw [wholeFirstLiveCells_length, List.length_take, ← hlen]
    change _ = min (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow rate rewards C_star C_h z).length _
    rw [Nat.min_eq_left hprefix.length_le]
  · intro k hk hk'
    have hkw : k < (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow rate rewards C_star C_h z).length := by
      simpa only [wholeFirstLiveCells_length] using hk
    have hkR := hkw.trans_le hprefix.length_le
    have hkW : k < (originalWord z hl).length := by omega
    obtain ⟨_, _, _, _, _, _, hread, _⟩ := hcells ⟨k, by rw [hwindow]; exact hkw⟩
    simp only [hwindow] at hread
    have hinput := live_readout_input rate _ (wholeLiveCell rate rewards C_star C_h z _ (List.getElem_mem hkw)) _ hread
    rw [wholeLiveCell_input_eq rate rewards C_star C_h z ⟨k, hkw⟩] at hinput
    have he := congrArg (fun L => L[k]?) hmap
    simp only [List.getElem?_map, List.getElem?_eq_getElem hkR,
      List.getElem?_eq_getElem hkW, Option.map_some] at he
    rw [← hprefix.getElem hkw] at he
    simp only [ReferenceFirstCollectionCurrentRetainedGate.cell0, hread, Option.some_or] at he
    have heq := Option.some.inj (Option.some.inj he)
    simpa only [List.getElem_take] using hinput.trans heq

private theorem live_time (z : Source p) (a : Auxiliary p) (k : ℕ) (hk : k < (live (z, a)).length) :
    ((live (z, a))[k]).time.val = start z + k := by
  have hkw : k < (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow rate rewards C_star C_h z).length := by
    simpa only [firstLiveChronologicalPrefix_length, ReferenceFirstLiveOverflowReadout.wholeFirstLiveLength] using hk
  rw [ReferenceFirstLiveChronologicalPrefixCausality.firstLiveChronologicalPrefix_cellTime rate rewards C_star C_h z a ⟨k, hkw⟩]
  have hp : ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow rate rewards C_star C_h z <+: records z := List.takeWhile_prefix _
  have hr : (records z)[k]? = some (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow rate rewards C_star C_h z)[k] := by
    rw [List.getElem?_eq_getElem (hkw.trans_le hp.length_le), ← hp.getElem hkw]
  exact ReferenceFirstCollectionRenewalRecordingFeedback.complete_record_time rate z rewards C_star C_h k _ hr

private theorem live_past_chronology (z : Source p) (a : Auxiliary p) (n : ℕ) (hn : n ≤ p.T) (hcut : n ≤ cut z) :
    (stateAt n hn (z, a)).2.Pairwise (fun e f => e.time.val < f.time.val) ∧
      (∀ e ∈ (stateAt n hn (z, a)).2, start z ≤ e.time.val ∧ e.time.val < n) ∧
      ∀ q : Fin p.T, start z ≤ q.val → q.val < n → ∃ e ∈ (stateAt n hn (z, a)).2, e.time = q := by
  rw [ReferenceFirstCollectionLogicalPrefixExtension.extendedPrefixStateAux_before_collectionStart rate rewards C_star C_h n hn z a hcut,
    ReferenceFirstLiveChronologicalPrefixCausality.calendarPast_eq_take_elapsed]
  have hlen : (live (z, a)).length = cut z - start z := by
    rw [firstLiveChronologicalPrefix_length]
    simp only [ReferenceFirstCollectionLogicalPrefixExtension.collectionStart, Nat.add_sub_cancel_left]
  refine ⟨?_, ?_, ?_⟩
  · apply List.pairwise_iff_getElem.mpr
    intro i j hi hj hij
    have hi' : i < (live (z, a)).length := by simp only [List.length_take] at hi; omega
    have hj' : j < (live (z, a)).length := by simp only [List.length_take] at hj; omega
    simp only [List.getElem_take, live_time rate rewards C_star C_h z a i hi', live_time rate rewards C_star C_h z a j hj']
    omega
  · intro e he
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp he
    have hk' : k < (live (z, a)).length := by simp only [List.length_take] at hk; omega
    have hkn : k < n - start z := by simp only [List.length_take] at hk; omega
    simp only [List.getElem_take, live_time rate rewards C_star C_h z a k hk']
    omega
  · intro q hsq hqn
    have hk : q.val - start z < ((live (z, a)).take (n - start z)).length := by rw [List.length_take, hlen]; omega
    refine ⟨_, List.getElem_mem hk, Fin.ext ?_⟩
    simp only [List.getElem_take]
    rw [live_time rate rewards C_star C_h z a _ (by rw [hlen]; omega)]
    omega

/-- No-call horizon completion is proved by the actual prefix recursion;
no first-invocation completion theorem is applied on this branch. -/
theorem noCallPast_chronology (z : Source p) (hz : z ∈ N) (a : Auxiliary p)
    (hl : ∃ active, ReferenceCorrectedInitializationLaunch.correctedLaunch rate z rewards C_star C_h = some active)
    (n : Fin (p.T + 1)) :
    (past n (z, a)).Pairwise (fun e f => e.time.val < f.time.val) ∧
      (∀ e ∈ past n (z, a), start z ≤ e.time.val ∧ e.time.val < n.val) ∧
      ∀ q : Fin p.T, start z ≤ q.val → q.val < n.val →
        (q.val < cut z ∨ ∃ hk : q.val - start z < (originalWord z hl).length,
          (originalWord z hl)[q.val - start z].enabled = true) → ∃ e ∈ past n (z, a), e.time = q := by
  have hend : ReferenceFirstCollectionPrecallCalendarSupport.firstCallBoundary rate rewards C_star C_h z = p.T := by
    rw [ReferenceFirstCollectionPrecallCalendarSupport.firstCallBoundary, hz]
  have hall : ∀ m (hm : m ≤ p.T),
      (stateAt m hm (z, a)).2.Pairwise (fun e f => e.time.val < f.time.val) ∧
      (∀ e ∈ (stateAt m hm (z, a)).2, start z ≤ e.time.val ∧ e.time.val < m) ∧
      ∀ q : Fin p.T, start z ≤ q.val → q.val < m →
        (q.val < cut z ∨ ∃ hk : q.val - start z < (originalWord z hl).length,
          (originalWord z hl)[q.val - start z].enabled = true) → ∃ e ∈ (stateAt m hm (z, a)).2, e.time = q := by
    intro m
    induction m with
    | zero => intro hm; exact ⟨List.Pairwise.nil, fun _ he => (List.not_mem_nil he).elim, fun q _ hq => (Nat.not_lt_zero _ hq).elim⟩
    | succ m ih =>
      intro hm
      by_cases hcut : m + 1 ≤ cut z
      · have hp := live_past_chronology rate rewards C_star C_h z a (m + 1) hm hcut
        exact ⟨hp.1, hp.2.1, fun q hs hq _ => hp.2.2 q hs hq⟩
      let q : Fin p.T := ⟨m, Nat.lt_of_succ_le hm⟩
      obtain ⟨r, hr, hmem⟩ := ReferenceFirstCollectionLogicalPrefixExtension.actualDomain_of_collection_interval
        rate rewards C_star C_h q z (by dsimp only [q]; omega) (by rw [hend]; exact q.isLt)
      obtain ⟨U, _hU, hstep⟩ := ReferenceFirstCollectionLogicalPrefixExtension.generated_collection_step rate rewards C_star C_h q z a r hr hmem
      let I := ReferenceFirstCollectionOneRoundLogicalCell.actualInput rewards C_star C_h z q r hr hmem
      let e := ReferenceFirstCollectionOneRoundLogicalCell.cellWithScalar rewards C_star C_h z q r hr hmem U
        (ReferenceFirstLiveCalendarMarkedTransition.labelZero a) (ReferenceSourceFastScalarDisintegration.sourceFastScalar p q z) (a (q, 1))
      have heTime : e.time = q := rfl
      have hp := ih (Nat.le_of_succ_le hm)
      obtain ⟨hkW, hsq, _hrtime, _hpast, hinput⟩ := ReferenceFirstCollectionLogicalNumericalAlignment.originalWord_collection_data
        rate rewards C_star C_h z hl q r hr hmem
      change I = _ at hinput
      change stateAt (m + 1) hm (z, a) = if I.enabled then
        (some e.nextSlowSet, (stateAt m (Nat.le_of_succ_le hm) (z, a)).2 ++ [e]) else stateAt m (Nat.le_of_succ_le hm) (z, a) at hstep
      cases hc : I.enabled with
      | false =>
        simp only [hc, Bool.false_eq_true, ite_false] at hstep
        rw [hstep]
        refine ⟨hp.1, fun f hf => ⟨(hp.2.1 f hf).1, by have := (hp.2.1 f hf).2; omega⟩, ?_⟩
        intro v hsv hvn hv
        have hvold : v.val < m := by
          by_contra h
          have hvq : v = q := Fin.ext (by dsimp only [q]; omega)
          subst v
          rcases hv with hv | ⟨hk, hv⟩
          · dsimp only [q] at hv; omega
          · rw [← hinput, hc] at hv; cases hv
        exact hp.2.2 v hsv hvold hv
      | true =>
        simp only [hc, ite_true] at hstep
        rw [hstep]
        refine ⟨List.pairwise_append.mpr ⟨hp.1, by simp, ?_⟩, ?_, ?_⟩
        · intro f hf g hg
          rw [List.mem_singleton.mp hg, heTime]
          exact (hp.2.1 f hf).2
        · intro f hf
          rcases List.mem_append.mp hf with hf | hf
          · exact ⟨(hp.2.1 f hf).1, by have := (hp.2.1 f hf).2; omega⟩
          · rw [List.mem_singleton.mp hf, heTime]
            exact ⟨hsq, by dsimp only [q]; omega⟩
        · intro v hsv hvn hv
          by_cases hvold : v.val < m
          · obtain ⟨f, hf, hfv⟩ := hp.2.2 v hsv hvold hv
            exact ⟨f, List.mem_append_left _ hf, hfv⟩
          · have hvq : v = q := Fin.ext (by dsimp only [q]; omega)
            exact ⟨e, List.mem_append_right _ (List.mem_singleton_self e), heTime.trans hvq.symm⟩
  exact hall n.val (Nat.le_of_lt_succ n.isLt)

/-- The nominal enabled flag precedes analytical overflow gating. -/
def nominalEnabled (q : Fin p.T) (z : Source p) : Bool :=
  ((ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h q z).bind
    (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate)).any RecordedQueueRun.RoundInput.enabled

/-- Every entry of the actual prefix has the full original-word update,
including enabled zero arrivals and PRE-gated detecting updates. -/
theorem originalPast_cell_data (z : Source p)
    (hl : ∃ active, ReferenceCorrectedInitializationLaunch.correctedLaunch rate z rewards C_star C_h = some active)
    (a : Auxiliary p) (n : Fin (p.T + 1)) (e : LogicalCell p rate) (he : e ∈ past n (z, a)) :
    let W := originalWord z hl
    ∃ hk : e.time.val - start z < W.length,
      W[e.time.val - start z].enabled = true ∧
      e.numerical = ReferenceLaterCollectionSourceReadoutMeasurability.numericalCoordinates W[e.time.val - start z] ∧
      e.before = RecordedQueueRun.run Q (W.take (e.time.val - start z)) ∧
      e.after = RecordedQueueRun.run Q (W.take (e.time.val + 1 - start z)) ∧
      e.arrivals = RecordedQueueRun.acceptedRecord Q e.before W[e.time.val - start z] ∧
      e.service = (fun j => RecordedQueueRun.recordService (4 * (Q).n) (e.before.registers j) (e.arrivals j)) ∧
      ∀ j, e.service j ≤ 4 * (Q).n ∧ e.after.registers j =
        QueueReplay.transition (4 * (Q).n) (e.before.registers j) (e.arrivals j) := by
  dsimp only
  by_cases hlive : e ∈ live (z, a)
  · obtain ⟨k, hk, hke⟩ := List.mem_iff_getElem.mp hlive
    have hkw : k < (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow rate rewards C_star C_h z).length := by
      simpa only [firstLiveChronologicalPrefix_length, ReferenceFirstLiveOverflowReadout.wholeFirstLiveLength] using hk
    have hkLive := hk
    let W := originalWord z hl
    let ell := ReferenceFirstLiveOverflowReadout.wholeFirstLiveLength rate rewards C_star C_h z
    have hv := originalWord_liveWord rate rewards C_star C_h z hl
    have hp : ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow rate rewards C_star C_h z <+: records z := List.takeWhile_prefix _
    have hlen : ell ≤ W.length := by rw [ReferenceActualCollectionHiddenRefreshPath.actualOriginalWord_length]; exact hp.length_le
    have hkw : k < ell := hkw
    have hk : k < W.length := hkw.trans_le hlen
    have htake (m : ℕ) (hm : m ≤ ell) :
        (ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells rate rewards C_star C_h z).take m = W.take m := by
      rw [hv, List.take_take, Nat.min_eq_left hm]
    have hround : (ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells rate rewards C_star C_h z)[k]'(by
        rw [wholeFirstLiveCells_length]; exact hkw) = W[k] := by simp only [hv, List.getElem_take]; rfl
    have hcell := firstLiveChronologicalPrefix_get rate rewards C_star C_h z a ⟨k, hkw⟩
    have hci := wholeLiveCell_input_eq rate rewards C_star C_h z ⟨k, hkw⟩
    dsimp only at hcell hci
    have hen : W[k].enabled = true := by
      rw [← hround]
      exact (congrArg RecordedQueueRun.RoundInput.enabled hci).symm.trans
        (wholeLiveCell rate rewards C_star C_h z _ (List.getElem_mem hkw)).enabled
    have htime := live_time rate rewards C_star C_h z a k hkLive
    rw [hke] at htime hcell
    have hi : e.time.val - start z = k := by omega
    have hi' : e.time.val + 1 - start z = k + 1 := by omega
    rw [hi, hi', hcell]
    dsimp only [appendLogicalCell]
    rw [htake _ hkw.le, hci, hround]
    refine ⟨hk, hen, rfl, rfl, ?_, rfl, rfl, ?_⟩
    · rw [← List.take_append_getElem hk, RecordedSlowRefresh.run_append_singleton]
    · intro j
      exact ⟨RecordedQueueRun.recordService_le_capacity _ _ _, rfl⟩
  · obtain ⟨q, r, hr, hm, _U, _hqn, _hU, hen, htime, _hphysical,
        hnum, hbefore, hafter, harr, hservice, _hslow, _hfast, _hproposal, _hnext, hall⟩ :=
      ReferenceFirstCollectionLogicalPrefixExtension.generated_collection_cell_fields rate rewards C_star C_h n z a e he hlive
    obtain ⟨hk, hsq, _hrtime, hpast, hinput⟩ := ReferenceFirstCollectionLogicalNumericalAlignment.originalWord_collection_data
      rate rewards C_star C_h z hl q r hr hm
    rw [hinput] at hen hnum
    rw [hpast] at hbefore
    rw [hpast, hinput] at hafter harr hservice
    have hrun : RecordedQueueRun.step Q (RecordedQueueRun.run Q ((originalWord z hl).take (q.val - start z)))
        (originalWord z hl)[q.val - start z] = RecordedQueueRun.run Q ((originalWord z hl).take (q.val + 1 - start z)) := by
      rw [Nat.sub_add_comm hsq, ← List.take_append_getElem hk, RecordedSlowRefresh.run_append_singleton]
    rw [htime]
    refine ⟨hk, hen, hnum, hbefore, hafter.trans hrun, ?_, ?_, hall⟩
    · rw [hbefore]; exact harr
    · rw [hbefore, harr]; exact hservice

/-- No launch and terminal launch both retain the literal empty calendar. -/
theorem past_empty_of_terminal_start (z : Source p) (a : Auxiliary p) (hs : start z = p.T) :
    past (Fin.last p.T) (z, a) = [] := by
  change (stateAt p.T le_rfl (z, a)).2 = []
  have h := ReferenceFirstCollectionLogicalPrefixExtension.extendedPrefixStateAux_before_collectionStart
    rate rewards C_star C_h p.T le_rfl z a (by dsimp only [ReferenceFirstCollectionLogicalPrefixExtension.collectionStart]; omega)
  simpa only [ReferenceFirstLiveChronologicalPrefixCausality.calendarPast_eq_take_elapsed,
    hs, Nat.sub_self, List.take_zero] using h

theorem past_empty_of_no_launch (z : Source p) (a : Auxiliary p)
    (hn : ReferenceCorrectedInitializationLaunch.correctedLaunch rate z rewards C_star C_h = none) :
    past (Fin.last p.T) (z, a) = [] :=
  past_empty_of_terminal_start rate rewards C_star C_h z a
    (ReferenceCompletePhysicalHistory.correctedLaunch_none_start_eq_T rate z rewards C_star C_h hn)

/-- No-call coverage uses the NOMINAL input flag, including after overflow. -/
theorem noCallPast_enabled_iff (z : Source p) (hz : z ∈ N) (a : Auxiliary p)
    (q : Fin p.T) :
    (∃ e ∈ past (Fin.last p.T) (z, a), e.time = q) ↔ nominalEnabled rate rewards C_star C_h q z = true := by
  cases hl : ReferenceCorrectedInitializationLaunch.correctedLaunch rate z rewards C_star C_h with
  | none =>
    rw [past_empty_of_no_launch rate rewards C_star C_h z a hl]
    have hr := ReferenceSourcePrefixHistoryFiltration.actualRecord_eq_none_of_terminal_start rate rewards C_star C_h q z
      (ReferenceCompletePhysicalHistory.correctedLaunch_none_start_eq_T rate z rewards C_star C_h hl)
    simp only [nominalEnabled, hr, Option.bind_none, Option.any_none, Bool.false_eq_true, List.not_mem_nil, false_and, exists_false]
  | some active =>
    let hlaunch : ∃ active, ReferenceCorrectedInitializationLaunch.correctedLaunch rate z rewards C_star C_h = some active := ⟨active, hl⟩
    have hc := noCallPast_chronology rate rewards C_star C_h z hz a hlaunch (Fin.last p.T)
    constructor
    · rintro ⟨e, he, rfl⟩
      have hs := (hc.2.1 e he).1
      obtain ⟨hk, hen, _⟩ := originalPast_cell_data rate rewards C_star C_h z hlaunch a (Fin.last p.T) e he
      obtain ⟨hk', hinput⟩ := ReferenceGeneratedCalendarMarkedPath.originalWord_inputAt rate rewards C_star C_h z hlaunch e.time hs
      simp only [nominalEnabled, hinput, Option.any_some, hen]
    · intro hen
      have hs : start z ≤ q.val := by
        by_contra h
        have hr := ReferenceSourcePrefixHistoryFiltration.actualRecord_eq_none_of_future_start rate rewards C_star C_h q z (by omega)
        simp only [nominalEnabled, hr, Option.bind_none, Option.any_none, Bool.false_eq_true] at hen
      obtain ⟨hk, hinput⟩ := ReferenceGeneratedCalendarMarkedPath.originalWord_inputAt rate rewards C_star C_h z hlaunch q hs
      have hW : (originalWord z hlaunch)[q.val - start z].enabled = true := by
        simpa only [nominalEnabled, hinput, Option.any_some] using hen
      exact hc.2.2 q hs q.isLt (Or.inr ⟨hk, hW⟩)

/-- The terminal no-call numerical prefix retains every original optional
slot. Presence is produced by the admitted precall calendar theorem. -/
theorem noCall_terminal_prefix (z : Source p) (hz : z ∈ N)
    (hl : ∃ active, ReferenceCorrectedInitializationLaunch.correctedLaunch rate z rewards C_star C_h = some active) :
    ReferenceFirstCollectionPrecallCalendarSupport.precallCells? rate rewards C_star C_h p.T z = some (originalWord z hl) ∧
      ReferenceFirstCollectionPrecallCalendarSupport.precallSlots rate rewards C_star C_h p.T z = (originalWord z hl).map some := by
  have hn : ReferenceFirstCollectionSamplerCall.firstCollectionCall rate rewards C_star C_h z = none := hz
  have hcut : ReferenceFirstCollectionPrecallCalendarSupport.cutBoundary rate rewards C_star C_h p.T z = p.T := by
    simp only [ReferenceFirstCollectionPrecallCalendarSupport.cutBoundary,
      ReferenceFirstCollectionPrecallCalendarSupport.firstCallBoundary, hn, Nat.min_self]
  have hc := (ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing rate z rewards C_star C_h).mp
    (by rw [Classical.choose_spec hl]; rfl)
  have hby : ReferenceSourcePrefixHistoryFiltration.actualLaunchBy rate rewards C_star C_h
      (ReferenceFirstCollectionPrecallCalendarSupport.cutBoundary rate rewards C_star C_h p.T z) z := by
    rw [hcut]
    exact ⟨hc, ReferenceCompletePhysicalHistory.physicalStart_le_T rate z rewards C_star C_h⟩
  obtain ⟨L, hL, _hlen, hslots, _hactual⟩ := ReferenceFirstCollectionPrecallCalendarSupport.precallPrefix_present
    rate rewards C_star C_h p.T le_rfl z hby
  have hfull := (ReferenceFirstCollectionPrecallCalendarSupport.precallSlots_terminal_no_call rate rewards C_star C_h z hz).trans
    (ReferenceFirstCollectionLogicalNumericalAlignment.originalWord_record_map rate rewards C_star C_h z hl)
  have hLW : L = originalWord z hl := by
    have heq := hslots.symm.trans hfull
    exact (List.map_injective_iff.mpr (Option.some_injective _)) heq
  exact ⟨hLW ▸ hL, hfull⟩

/-- Every raw component's actual readout is chronological, including all
no-call alternatives and every archived generated segment. -/
theorem terminalReadout_chronology (w : Omega rate rewards C_star C_h) :
    (terminalReadout rate rewards C_star C_h control0 w).2.2.Pairwise (fun e f => e.time.val < f.time.val) := by
  rcases w with ⟨i, w⟩
  cases i with
  | noCall =>
    cases hl : ReferenceCorrectedInitializationLaunch.correctedLaunch rate w.1.val rewards C_star C_h with
    | none => rw [show (terminalReadout rate rewards C_star C_h control0 ⟨.noCall, w⟩).2.2 = [] from
        past_empty_of_no_launch rate rewards C_star C_h w.1.val w.2 hl]; exact List.Pairwise.nil
    | some active => exact (noCallPast_chronology rate rewards C_star C_h w.1.val w.1.property w.2 ⟨active, hl⟩ (Fin.last p.T)).1
  | stopped u t => exact (ReferenceInitialStoppedCalendar.initialStoppedPast_chronology rate rewards C_star C_h control0 u t (Fin.last p.T) w).1
  | generated b u t => exact (ReferenceGeneratedCalendarNativePreservation.calendarObservation_chronology
      rate rewards C_star C_h control0 b u t _ _ w).1

private theorem chronological_length (H : List (LogicalCell p rate))
    (hH : H.Pairwise (fun e f => e.time.val < f.time.val)) : H.length ≤ p.T := by
  have hn : (H.map LogicalCell.time).Nodup := by
    rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
    exact hH.imp fun h => Fin.ne_of_val_ne (Nat.ne_of_lt h)
  simpa only [List.length_map, Fintype.card_fin] using hn.length_le_card

/-- Signed comparison with a fixed comparator, over the literal entire list. -/
def signedGap (S0 : ProductSetLaw.ProductSet p.K p.m) (H : List (LogicalCell p rate)) : ℝ :=
  (H.map (fun e => (∑ i ∈ S0.val, ((rewards e.time i).val : ℝ) / (D p : ℝ)) -
    ReferenceInitialStoppedCalendar.cellReward rate rewards e)).sum

private theorem gridReward_bounds (q : Fin p.T) (i : Fin p.K) :
    0 ≤ ((rewards q i).val : ℝ) / (D p : ℝ) ∧ ((rewards q i).val : ℝ) / (D p : ℝ) ≤ 1 := by
  refine ⟨div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _), (div_le_one (Nat.cast_pos.mpr (D_pos p))).mpr ?_⟩
  exact_mod_cast Nat.le_of_lt_succ (rewards q i).isLt

private theorem setReward_bounds (U : Finset (Fin p.K)) (q : Fin p.T) :
    0 ≤ ∑ i ∈ U, ((rewards q i).val : ℝ) / (D p : ℝ) ∧
      (∑ i ∈ U, ((rewards q i).val : ℝ) / (D p : ℝ)) ≤ (U.card : ℝ) := by
  refine ⟨Finset.sum_nonneg (fun i _ => (gridReward_bounds rewards q i).1), ?_⟩
  simpa only [Finset.sum_const, nsmul_eq_mul, mul_one] using
    Finset.sum_le_sum (fun i (_hi : i ∈ U) => (gridReward_bounds rewards q i).2)

/-- The same bounded auxiliary actions remain present after overflow. -/
theorem cellReward_bounds (e : LogicalCell p rate) :
    0 ≤ ReferenceInitialStoppedCalendar.cellReward rate rewards e ∧
      ReferenceInitialStoppedCalendar.cellReward rate rewards e ≤ p.m := by
  have hs := setReward_bounds rewards e.slowSet.val e.time
  have hf := gridReward_bounds rewards e.time e.fastArm
  have hm : ((p.m - 1 : ℕ) : ℝ) + 1 = (p.m : ℝ) := by
    exact_mod_cast Nat.sub_add_cancel (show 1 ≤ p.m by have := p.two_le_m; omega)
  simp only [ReferenceInitialStoppedCalendar.cellReward]
  refine ⟨add_nonneg hs.1 hf.1, ?_⟩
  calc
    _ ≤ (e.slowSet.val.card : ℝ) + 1 := add_le_add hs.2 hf.2
    _ = p.m := by rw [(Finset.mem_powersetCard.mp e.slowSet.property).2, hm]

private theorem signedGap_abs_le_length (S0 : ProductSetLaw.ProductSet p.K p.m) (H : List (LogicalCell p rate)) :
    |signedGap rate rewards S0 H| ≤ (p.m : ℝ) * H.length := by
  induction H with
  | nil => simp only [signedGap, List.map_nil, List.sum_nil, abs_zero, List.length_nil, Nat.cast_zero, mul_zero, le_refl]
  | cons e H ih =>
    have hc := setReward_bounds rewards S0.val e.time
    rw [(Finset.mem_powersetCard.mp S0.property).2] at hc
    have he := cellReward_bounds rate rewards e
    have hb : |(∑ i ∈ S0.val, ((rewards e.time i).val : ℝ) / (D p : ℝ)) -
        ReferenceInitialStoppedCalendar.cellReward rate rewards e| ≤ p.m :=
      abs_le.mpr ⟨by linarith only [hc.1, he.2], by linarith only [hc.2, he.1]⟩
    change |((∑ i ∈ S0.val, ((rewards e.time i).val : ℝ) / (D p : ℝ)) -
      ReferenceInitialStoppedCalendar.cellReward rate rewards e) + signedGap rate rewards S0 H| ≤ _
    calc
      _ ≤ _ := abs_add_le _ _
      _ ≤ (p.m : ℝ) + (p.m : ℝ) * H.length := add_le_add hb ih
      _ = _ := by simp only [List.length_cons, Nat.cast_add, Nat.cast_one]; ring

theorem terminalReadout_signedGap_bound (S0 : ProductSetLaw.ProductSet p.K p.m) (w : Omega rate rewards C_star C_h) :
    |signedGap rate rewards S0 (terminalReadout rate rewards C_star C_h control0 w).2.2| ≤ (p.m : ℝ) * p.T := by
  exact (signedGap_abs_le_length rate rewards S0 _).trans (mul_le_mul_of_nonneg_left
    (Nat.cast_le.mpr (chronological_length rate _ (terminalReadout_chronology rate rewards C_star C_h control0 w))) (Nat.cast_nonneg _))

instance terminalLaw_probability : IsProbabilityMeasure (terminalLaw rate rewards C_star C_h control0) := by
  constructor
  have h := congrArg (fun nu : Measure (Source p) => nu Set.univ) (terminalLaw_map_source rate rewards C_star C_h control0)
  simpa only [Measure.map_apply (measurable_terminalSource rate rewards C_star C_h control0) MeasurableSet.univ,
    Set.preimage_univ, measure_univ] using h

instance fixedIDTerminalLaw_probability (ids : CompletePublicTable.IDArray p) :
    IsProbabilityMeasure (fixedIDTerminalLaw rate rewards C_star C_h control0 ids) := by
  constructor
  have h := congrArg (fun nu : Measure (Source p) => nu Set.univ) (fixedIDTerminalLaw_map_source rate rewards C_star C_h control0 ids)
  simpa only [Measure.map_apply (measurable_terminalSource rate rewards C_star C_h control0) MeasurableSet.univ,
    Set.preimage_univ, measure_univ] using h

private instance sumMeasurableSingleton {A V : Type*} [MeasurableSpace A] [MeasurableSpace V]
    [MeasurableSingletonClass A] [MeasurableSingletonClass V] : MeasurableSingletonClass (A ⊕ V) where
  measurableSet_singleton x := by
    cases x with
    | inl a => simpa only [Set.image_singleton] using (MeasurableSet.singleton a).inl_image
    | inr b => simpa only [Set.image_singleton] using (MeasurableSet.singleton b).inr_image

private instance listMeasurableSingleton {A : Type*} [MeasurableSpace A] [MeasurableSingletonClass A] :
    MeasurableSingletonClass (List A) where
  measurableSet_singleton L := by
    have hinj : Function.Injective (ReferenceActiveHorizonMeasurability.listObservationCoordinates (α := A)) := by
      intro left right h
      apply List.ext_getElem (congrArg Prod.fst h)
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

/-- Measurability uses only finite reward marks; continuous cell coordinates
keep the original measurable structures. -/
theorem measurable_signedGap (S0 : ProductSetLaw.ProductSet p.K p.m) : Measurable (signedGap rate rewards S0) := by
  let mark : LogicalCell p rate → Fin p.T × (SlowSet p × Fin p.K) := fun e => (e.time, (e.slowSet, e.fastArm))
  have hm : Measurable mark := ReferenceFirstLiveChronologicalPrefixMeasurability.measurable_logicalCell_time.prodMk
    (ReferenceFirstLiveChronologicalPrefixMeasurability.measurable_logicalCell_slowSet.mono le_rfl le_top |>.prodMk
      ReferenceFirstLiveChronologicalPrefixMeasurability.measurable_logicalCell_fastArm)
  let F : List (Fin p.T × (SlowSet p × Fin p.K)) → ℝ := fun L =>
    (L.map (fun e => (∑ i ∈ S0.val, ((rewards e.1 i).val : ℝ) / (D p : ℝ)) -
      ((∑ i ∈ e.2.1.val, ((rewards e.1 i).val : ℝ) / (D p : ℝ)) + ((rewards e.1 e.2.2).val : ℝ) / (D p : ℝ)))).sum
  have hF : Measurable F := measurable_of_countable F
  convert hF.comp (ReferenceActiveHorizonMeasurability.measurable_list_map id measurable_id mark hm) using 1
  funext H
  simp only [Function.comp_def, id_eq, F, mark, signedGap, List.map_map, ReferenceInitialStoppedCalendar.cellReward]

/-- The entire signed readout is integrable on both the raw and common
observer laws, with or without the SAME original ID restriction. -/
theorem integrable_signedGap (ids : Option (CompletePublicTable.IDArray p))
    (S0 : ProductSetLaw.ProductSet p.K p.m) :
    Integrable (fun w => signedGap rate rewards S0 (terminalReadout rate rewards C_star C_h control0 w).2.2)
      (ids.elim (terminalLaw rate rewards C_star C_h control0) (fixedIDTerminalLaw rate rewards C_star C_h control0)) ∧
    Integrable (fun o : ReferenceInitialStoppedCalendar.Observer rate => signedGap rate rewards S0 o.2.2)
      (ids.elim (terminalReadoutLaw rate rewards C_star C_h control0) (fixedIDReadoutLaw rate rewards C_star C_h control0)) := by
  have hraw : Integrable (fun w => signedGap rate rewards S0 (terminalReadout rate rewards C_star C_h control0 w).2.2)
      (ids.elim (terminalLaw rate rewards C_star C_h control0) (fixedIDTerminalLaw rate rewards C_star C_h control0)) := by
    cases ids <;> dsimp only [Option.elim] <;>
      apply Integrable.of_bound ((measurable_signedGap rate rewards S0).comp
        (measurable_terminalReadout rate rewards C_star C_h control0).snd.snd).aestronglyMeasurable ((p.m : ℝ) * p.T) <;>
      exact Filter.Eventually.of_forall fun w => by
        simpa only [Real.norm_eq_abs, Function.comp_apply] using terminalReadout_signedGap_bound rate rewards C_star C_h control0 S0 w
  refine ⟨hraw, ?_⟩
  cases ids <;> exact (integrable_map_measure
    ((measurable_signedGap rate rewards S0).comp measurable_snd.snd).aestronglyMeasurable
    (measurable_terminalReadout rate rewards C_star C_h control0).aemeasurable).mpr hraw

/-- The retained original physical input, before any assignment insertions. -/
def componentOriginalSource : (i : Component p) → Payload rate rewards C_star C_h i → Source p
  | .noCall, w => w.1.val
  | .stopped _ _, w => w.1.val
  | .generated b u t, w => (calendarOriginalLift rate rewards C_star C_h b u t (p.T - (t.val + 1)) w).1.1.val

def originalSource (w : Omega rate rewards C_star C_h) : Source p :=
  componentOriginalSource rate rewards C_star C_h w.1 w.2

theorem terminalSource_original_ids_private (w : Omega rate rewards C_star C_h) :
    (terminalSource rate rewards C_star C_h control0 w).1.1 = (originalSource rate rewards C_star C_h w).1.1 ∧
      (terminalSource rate rewards C_star C_h control0 w).2 = (originalSource rate rewards C_star C_h w).2 := by
  rcases w with ⟨i, w⟩
  cases i with
  | noCall => exact ⟨rfl, rfl⟩
  | stopped u t => exact ⟨rfl, rfl⟩
  | generated b u t => exact calendarCurrentSource_original_ids_private rate rewards C_star C_h control0 b u t _ _ w

/-- The terminal restriction fixes precisely the original identification array. -/
theorem fixedIDTerminalSource_iff_original (ids : CompletePublicTable.IDArray p) (w : Omega rate rewards C_star C_h) :
    terminalSource rate rewards C_star C_h control0 w ∈ ReferenceFixedIDSourceSection.fixedIDSourceSection ids ↔
      originalSource rate rewards C_star C_h w ∈ ReferenceFixedIDSourceSection.fixedIDSourceSection ids := by
  change (terminalSource rate rewards C_star C_h control0 w).1.1 = ids ↔ _
  rw [(terminalSource_original_ids_private rate rewards C_star C_h control0 w).1]
  rfl

private theorem run_disabled_step (L : List (RecordedQueueRun.RoundInput p.K))
    (c : RecordedQueueRun.RoundInput p.K) (hc : c.enabled = false) :
    let st := RecordedQueueRun.run Q L
    (RecordedQueueRun.step Q st c).registers = st.registers ∧
      (RecordedQueueRun.step Q st c).overflow = st.overflow ∧
      ∀ j, (RecordedQueueRun.step Q st c).records j = st.records j ++ [(false, 0)] := by
  dsimp only
  have hh := ReferenceFirstCollectionRenewalFutureNumericalPrefix.disabled_step_registers_and_records
    rate (RecordedQueueRun.run Q L) c hc
  refine ⟨hh.1, ?_, fun j => congrFun hh.2 j⟩
  apply Bool.eq_iff_iff.mpr
  have ha := RecordedQueueRun.run_overflow_iff_cutoff Q (L ++ [c])
  rw [RecordedSlowRefresh.run_append_singleton, hh.1] at ha
  exact ha.trans (RecordedQueueRun.run_overflow_iff_cutoff Q L).symm

private theorem disabled_interval_completion (W : List (RecordedQueueRun.RoundInput p.K)) (m n : ℕ)
    (hmn : m ≤ n) (hn : n ≤ W.length)
    (hd : ∀ k (hk : k < W.length), m ≤ k → k < n → W[k].enabled = false) :
    let A := RecordedQueueRun.run Q (W.take m)
    let st := RecordedQueueRun.run Q (W.take n)
    st.registers = A.registers ∧ st.overflow = A.overflow ∧
      ∀ j, st.records j = A.records j ++ List.replicate (n - m) (false, 0) := by
  revert hn hd
  induction hmn with
  | refl => intro _ _; exact ⟨rfl, rfl, fun j => by simp only [Nat.sub_self, List.replicate_zero, List.append_nil]⟩
  | @step n hmn ih =>
    intro hn hd
    have hk : n < W.length := by omega
    have hi := ih (by omega) (fun k hk hmk hkn => hd k hk hmk (by omega))
    have hs := run_disabled_step rate (W.take n) W[n] (hd n hk hmn (by omega))
    dsimp only at hi hs ⊢
    rw [← List.take_append_getElem hk, RecordedSlowRefresh.run_append_singleton]
    refine ⟨hs.1.trans hi.1, hs.2.1.trans hi.2.1, ?_⟩
    intro j
    rw [hs.2.2 j, hi.2.2 j, List.append_assoc]
    have hcount : n.succ - m = (n - m) + 1 := (Nat.succ_sub hmn).trans (Nat.succ_eq_add_one _)
    rw [hcount, List.replicate_succ']

/-- The no-call terminal POST includes one false/zero numerical record for
EVERY omitted disabled date. Full run-state equality across a gap is avoided. -/
theorem noCallPast_terminal_padding (z : Source p) (hz : z ∈ N) (a : Auxiliary p)
    (hl : ∃ active, ReferenceCorrectedInitializationLaunch.correctedLaunch rate z rewards C_star C_h = some active)
    (hne : past (Fin.last p.T) (z, a) ≠ []) :
    let W := originalWord z hl
    let st := RecordedQueueRun.run Q W
    ∃ e, (past (Fin.last p.T) (z, a)).getLast? = some e ∧
      st.registers = e.after.registers ∧ st.overflow = e.after.overflow ∧
      ∀ j, st.records j = e.after.records j ++ List.replicate (p.T - (e.time.val + 1)) (false, 0) := by
  dsimp only
  let W := originalWord z hl
  let H := past (Fin.last p.T) (z, a)
  have hp := noCallPast_chronology rate rewards C_star C_h z hz a hl (Fin.last p.T)
  cases hlast : H.getLast? with
  | none => exact (hne (List.getLast?_eq_none_iff.mp hlast)).elim
  | some e =>
    obtain ⟨pre, hpre⟩ := List.getLast?_eq_some_iff.mp hlast
    have he : e ∈ H := by rw [hpre]; exact List.mem_append_right _ (List.mem_singleton_self e)
    have hb := hp.2.1 e he
    have hmax : ∀ f ∈ H, f.time.val ≤ e.time.val := by
      intro f hf
      have hpair : H.Pairwise (fun f g => f.time.val ≤ g.time.val) := hp.1.imp fun h => h.le
      have h := hpair.rel_getLast_of_rel_getLast_getLast hf (Nat.le_refl _)
      simpa only [hpre, List.getLast_append_singleton] using h
    have hlen : W.length = p.T - start z := by
      rw [ReferenceActualCollectionHiddenRefreshPath.actualOriginalWord_length, ReferenceCompletePhysicalHistory.completeSuffixRecords_length]
    have hd : ∀ k (hk : k < W.length), e.time.val + 1 - start z ≤ k → k < W.length → W[k].enabled = false := by
      intro k hk heq _hk
      let q : Fin p.T := ⟨start z + k, by rw [hlen] at hk; omega⟩
      cases hflag : W[k].enabled with
      | false => rfl
      | true =>
        have hs : start z ≤ q.val := Nat.le_add_right _ _
        obtain ⟨hki, hi⟩ := ReferenceGeneratedCalendarMarkedPath.originalWord_inputAt rate rewards C_star C_h z hl q hs
        have hnom : nominalEnabled rate rewards C_star C_h q z = true := by
          simpa only [nominalEnabled, hi, Option.any_some, q, Nat.add_sub_cancel_left] using hflag
        obtain ⟨f, hf, ht⟩ := (noCallPast_enabled_iff rate rewards C_star C_h z hz a q).mpr hnom
        have hfm := hmax f hf
        rw [ht] at hfm
        dsimp only [q] at hfm
        omega
    have hc := disabled_interval_completion rate W (e.time.val + 1 - start z) W.length
      (by rw [hlen]; have := e.time.isLt; omega) le_rfl hd
    obtain ⟨_hk, _hen, _hnum, _hbefore, hafter, _⟩ := originalPast_cell_data rate rewards C_star C_h z hl a (Fin.last p.T) e he
    dsimp only at hc
    rw [List.take_length, ← hafter] at hc
    have hgap : W.length - (e.time.val + 1 - start z) = p.T - (e.time.val + 1) := by rw [hlen]; omega
    rw [hgap] at hc
    exact ⟨e, rfl, hc⟩

/-- Read a date by filtering the actual list, with no selected or default
logical action at an absent date. -/
def dateSignedGap (S0 : ProductSetLaw.ProductSet p.K p.m) (q : Fin p.T)
    (H : List (LogicalCell p rate)) : ℝ :=
  signedGap rate rewards S0 (H.filter (fun e => e.time == q))

private theorem dateSignedGap_cons (S0 : ProductSetLaw.ProductSet p.K p.m) (q : Fin p.T)
    (e : LogicalCell p rate) (H : List (LogicalCell p rate)) :
    dateSignedGap rate rewards S0 q (e :: H) =
      (if e.time = q then (∑ i ∈ S0.val, ((rewards e.time i).val : ℝ) / (D p : ℝ)) -
        ReferenceInitialStoppedCalendar.cellReward rate rewards e else 0) + dateSignedGap rate rewards S0 q H := by
  by_cases ht : e.time = q <;> simp only [dateSignedGap, List.filter_cons, beq_iff_eq, ht,
    ite_true, ite_false, signedGap, List.map_cons, List.sum_cons, zero_add]

/-- Exact full-calendar decomposition of the signed literal list. -/
theorem signedGap_eq_sum_dates (S0 : ProductSetLaw.ProductSet p.K p.m) (H : List (LogicalCell p rate)) :
    signedGap rate rewards S0 H = ∑ q : Fin p.T, dateSignedGap rate rewards S0 q H := by
  induction H with
  | nil => simp only [signedGap, dateSignedGap, List.filter_nil, List.map_nil, List.sum_nil, Finset.sum_const_zero]
  | cons e H ih =>
    simp_rw [dateSignedGap_cons]
    rw [Finset.sum_add_distrib, ← ih]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    rfl

/-- Localization of the correlated readout is the same positive ID section
as localization of the raw law. The archive and tape remain jointly retained. -/
theorem fixedIDReadoutLaw_eq_restrict (ids : CompletePublicTable.IDArray p) :
    fixedIDReadoutLaw rate rewards C_star C_h control0 ids =
      (CompletePublicTable.idArrayMeasure p {ids})⁻¹ •
        (terminalReadoutLaw rate rewards C_star C_h control0).restrict
          (Prod.fst ⁻¹' ReferenceFixedIDSourceSection.fixedIDSourceSection ids) := by
  have hE := (ReferenceFixedIDSourceSection.measurable_fixedIDSourceSection (p := p) ids).preimage
    (measurable_fst : Measurable (Prod.fst : ReferenceInitialStoppedCalendar.Observer rate → Source p))
  have hpre : terminalReadout rate rewards C_star C_h control0 ⁻¹'
      (Prod.fst ⁻¹' ReferenceFixedIDSourceSection.fixedIDSourceSection ids) =
        terminalSource rate rewards C_star C_h control0 ⁻¹' ReferenceFixedIDSourceSection.fixedIDSourceSection ids := by
    ext w
    simp only [Set.mem_preimage, terminalReadout_source]
  rw [fixedIDReadoutLaw, fixedIDTerminalLaw_eq_restrict,
    Measure.map_smul _ (measurable_terminalReadout rate rewards C_star C_h control0).aemeasurable,
    ← hpre, ← Measure.restrict_map (measurable_terminalReadout rate rewards C_star C_h control0) hE]
  rfl

private theorem chronological_time_injective (H : List (LogicalCell p rate))
    (hH : H.Pairwise (fun e f => e.time.val < f.time.val))
    (e f : LogicalCell p rate) (he : e ∈ H) (hf : f ∈ H) (ht : e.time = f.time) : e = f := by
  have hn : (H.map LogicalCell.time).Nodup := by
    rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
    exact hH.imp fun h => Fin.ne_of_val_ne (Nat.ne_of_lt h)
  exact List.inj_on_of_nodup_map hn he hf ht

/-- A stopped calendar's strict prefix is the original first-call prefix.
Only the suffix constructors are appended at and after the call date. -/
theorem stoppedPast_strict_prefix (u t : Fin p.T)
    (w : Payload rate rewards C_star C_h (.stopped u t))
    (n : Fin (p.T + 1)) (e : LogicalCell p rate)
    (he : e ∈ ReferenceInitialStoppedCalendar.initialStoppedPast rate rewards C_star C_h control0 u t n w)
    (het : e.time.val < t.val) : e ∈ past t.castSucc (w.1.val, w.2) := by
  have hall : ∀ k (hk : k ≤ p.T),
      e ∈ ReferenceInitialStoppedCalendar.calendarPastAux rate rewards C_star C_h control0 t k hk (w.1.val, w.2) →
      e ∈ past t.castSucc (w.1.val, w.2) := by
    intro k
    induction k with
    | zero => intro _ h; exact (List.not_mem_nil h).elim
    | succ k ih =>
      intro hk h
      by_cases hkt : k < t.val
      · rw [ReferenceInitialStoppedCalendar.calendarPastAux, ite_eq_left hkt] at h
        exact (ReferenceFirstCollectionLogicalPrefixExtension.extendedPrefixStateAux_prefix
          rate rewards C_star C_h t.val t.isLt.le (k + 1) (by omega) (w.1.val, w.2)).subset h
      · let q : Fin p.T := ⟨k, by omega⟩
        change e ∈ ReferenceInitialStoppedCalendar.initialStoppedPast rate rewards C_star C_h control0 u t q.succ w at h
        rw [ReferenceInitialStoppedCalendar.initialStoppedPast_succ rate rewards C_star C_h control0 u t q (by dsimp only [q]; omega)] at h
        rcases List.mem_append.mp h with h | h
        · exact ih (by omega) h
        · split at h
          · have heq := List.mem_singleton.mp h
            have ht : e.time = q := congrArg LogicalCell.time heq
            have hv := congrArg Fin.val ht
            dsimp only [q] at hv
            omega
          · exact (List.not_mem_nil h).elim
  exact hall n.val (Nat.le_of_lt_succ n.isLt) he

/-- Complete enabled-date coverage of the actual initially stopped path. -/
theorem stoppedPast_enabled_iff (u t : Fin p.T)
    (w : Payload rate rewards C_star C_h (.stopped u t)) (q : Fin p.T) :
    (∃ e ∈ (componentReadout rate rewards C_star C_h control0 (.stopped u t) w).2.2, e.time = q) ↔
      nominalEnabled rate rewards C_star C_h q w.1.val = true := by
  have hf := w.1.property.1.1
  have hpre := ReferenceInitialStoppedCalendar.initialStoppedPast_retains_prefix
    rate rewards C_star C_h control0 u t (Fin.last p.T) t.isLt.le w
  by_cases hqt : q.val < t.val
  · constructor
    · rintro ⟨e, he, ht⟩
      apply (ReferenceGeneratedCalendarMarkedPath.firstPast_enabled_iff rate rewards C_star C_h u t
        w.1.val hf w.2 t.castSucc le_rfl q hqt).mp
      exact ⟨e, stoppedPast_strict_prefix rate rewards C_star C_h control0 u t w (Fin.last p.T) e he (ht ▸ hqt), ht⟩
    · intro hen
      obtain ⟨e, he, ht⟩ := (ReferenceGeneratedCalendarMarkedPath.firstPast_enabled_iff
        rate rewards C_star C_h u t w.1.val hf w.2 t.castSucc le_rfl q hqt).mpr hen
      exact ⟨e, hpre.subset he, ht⟩
  · have htq : t.val ≤ q.val := by omega
    have hr := ReferenceInitialStoppedCalendar.suffixRecord_spec rate rewards C_star C_h u t q htq w.1
    have hn : nominalEnabled rate rewards C_star C_h q w.1.val =
        (ReferenceInitialStoppedCalendar.suffixInput rate rewards C_star C_h u t q htq w.1).enabled := by
      simp only [nominalEnabled, hr.1, Option.bind_some, hr.2.2, Option.any_some]
    rw [hn]
    constructor
    · rintro ⟨e, he, rfl⟩
      exact (ReferenceInitialStoppedCalendar.initialStoppedPast_suffix_fields
        rate rewards C_star C_h control0 u t (Fin.last p.T) w e he htq).1
    · intro hen
      exact ⟨_, ReferenceInitialStoppedCalendar.initialStoppedPast_enabled_mem
        rate rewards C_star C_h control0 u t q htq (Fin.last p.T) q.isLt w hen, rfl⟩

/-- Every nominal enabled date, and only such a date, occurs in the readout. -/
theorem terminalReadout_enabled_iff (w : Omega rate rewards C_star C_h) (q : Fin p.T) :
    (∃ e ∈ (terminalReadout rate rewards C_star C_h control0 w).2.2, e.time = q) ↔
      nominalEnabled rate rewards C_star C_h q (terminalSource rate rewards C_star C_h control0 w) = true := by
  rcases w with ⟨i, w⟩
  cases i with
  | noCall => exact noCallPast_enabled_iff rate rewards C_star C_h w.1.val w.1.property w.2 q
  | stopped u t => exact stoppedPast_enabled_iff rate rewards C_star C_h control0 u t w q
  | generated b u t =>
    exact ReferenceGeneratedCalendarMarkedPath.calendar_enabled_iff
      rate rewards C_star C_h control0 b u t _ _ w q (by have := q.isLt; omega)

/-- All components use the nominal schedule, even after logical overflow. -/
theorem terminalReadout_unique_enabled (w : Omega rate rewards C_star C_h) (q : Fin p.T) :
    (∃! e : LogicalCell p rate, e ∈ (terminalReadout rate rewards C_star C_h control0 w).2.2 ∧ e.time = q) ↔
      nominalEnabled rate rewards C_star C_h q (terminalSource rate rewards C_star C_h control0 w) = true := by
  have hc := terminalReadout_chronology rate rewards C_star C_h control0 w
  have he := terminalReadout_enabled_iff rate rewards C_star C_h control0 w q
  constructor
  · rintro ⟨e, heq, _⟩; exact he.mp ⟨e, heq⟩
  · intro hen
    obtain ⟨e, hem, ht⟩ := he.mpr hen
    exact ⟨e, ⟨hem, ht⟩, fun f hf => chronological_time_injective rate _ hc f e hf.1 hem (hf.2.trans ht.symm)⟩

/-- The signed sum contains the unique cell at EVERY nominal enabled date,
including the prescribed continuation after overflow. -/
theorem terminalReadout_signedGap_eq_nominal_dates
    (S0 : ProductSetLaw.ProductSet p.K p.m) (w : Omega rate rewards C_star C_h) :
    let Z := terminalSource rate rewards C_star C_h control0 w
    let H := (terminalReadout rate rewards C_star C_h control0 w).2.2
    signedGap rate rewards S0 H = ∑ q : Fin p.T,
      if nominalEnabled rate rewards C_star C_h q Z then dateSignedGap rate rewards S0 q H else 0 := by
  dsimp only
  rw [signedGap_eq_sum_dates]
  apply Finset.sum_congr rfl
  intro q _hq
  cases hq : nominalEnabled rate rewards C_star C_h q (terminalSource rate rewards C_star C_h control0 w) with
  | true => rfl
  | false =>
    have hnot : ¬∃ e ∈ (terminalReadout rate rewards C_star C_h control0 w).2.2, e.time = q := by
      rw [terminalReadout_enabled_iff, hq]
      exact Bool.false_ne_true
    have hfilter : ((terminalReadout rate rewards C_star C_h control0 w).2.2).filter (fun e => e.time == q) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro e he
      have ht : e.time ≠ q := fun ht => hnot ⟨e, he, ht⟩
      simpa only [beq_iff_eq] using ht
    simp only [dateSignedGap, hfilter, signedGap, List.map_nil, List.sum_nil, Bool.false_eq_true, ite_false]

/-- Each omitted disabled physical date appends its numerical false/zero
record while preserving registers and the overflow flag. -/
theorem originalWord_disabled_padding (z : Source p)
    (hl : ∃ active, ReferenceCorrectedInitializationLaunch.correctedLaunch rate z rewards C_star C_h = some active)
    (q : Fin p.T) (hsq : start z ≤ q.val) (hd : nominalEnabled rate rewards C_star C_h q z = false) :
    let W := originalWord z hl
    let R := RecordedQueueRun.run Q (W.take (q.val - start z))
    let R' := RecordedQueueRun.run Q (W.take (q.val + 1 - start z))
    R'.registers = R.registers ∧ R'.overflow = R.overflow ∧
      ∀ j, R'.records j = R.records j ++ [(false, 0)] := by
  obtain ⟨hi, hinput⟩ := ReferenceGeneratedCalendarMarkedPath.originalWord_inputAt rate rewards C_star C_h z hl q hsq
  have hen : (originalWord z hl)[q.val - start z].enabled = false := by
    simpa only [nominalEnabled, hinput, Option.any_some] using hd
  dsimp only
  rw [Nat.sub_add_comm hsq, ← List.take_append_getElem hi, RecordedSlowRefresh.run_append_singleton]
  exact run_disabled_step rate _ _ hen

private theorem firstPast_stopped (z : Source p) (a : Auxiliary p) (n : Fin (p.T + 1))
    (e : LogicalCell p rate) (he : e ∈ past n (z, a)) (hstop : e.before.overflow = true) :
    e.slowSet = frozenSlowSet p ∧ e.fastArm = frozenFastArm p ∧
      e.proposal = false ∧ e.nextSlowSet = frozenSlowSet p := by
  by_cases hlive : e ∈ live (z, a)
  · obtain ⟨i, hi, hie⟩ := List.mem_iff_getElem.mp hlive
    have hiw : i < (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow rate rewards C_star C_h z).length := by
      simpa only [firstLiveChronologicalPrefix_length, ReferenceFirstLiveOverflowReadout.wholeFirstLiveLength] using hi
    have heq := hie.symm.trans (firstLiveChronologicalPrefix_get rate rewards C_star C_h z a ⟨i, hiw⟩)
    rw [heq] at hstop ⊢
    let R := RecordedQueueRun.run Q ((ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells rate rewards C_star C_h z).take i)
    change R.overflow = true at hstop
    have h := appendLogicalCell_after_overflow
      ((ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow rate rewards C_star C_h z)[i])
      (wholeLiveCell rate rewards C_star C_h z _ (List.getElem_mem hiw)) R a hstop
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩
  · obtain ⟨_q, _r, _hr, _hm, _U, _hqn, _hU, _hen, _ht, _hp,
        _hn, hb, _ha, _harr, _hservice, hs, hf, hproposal, hnext, _hall⟩ :=
      ReferenceFirstCollectionLogicalPrefixExtension.generated_collection_cell_fields rate rewards C_star C_h n z a e he hlive
    have hov := (congrArg RecordedQueueRun.RunState.overflow hb).symm.trans hstop
    rw [hs, hf, hproposal, hnext, hov]
    simp only [ite_true, Bool.not_true, Bool.and_false, Bool.false_and, and_self]

private theorem measurableEmbedding_sigma_mk {I : Type*} {Fibre : I → Type*}
    [∀ i, MeasurableSpace (Fibre i)] (i : I) : MeasurableEmbedding (Sigma.mk i : Fibre i → Sigma Fibre) := by
  refine ⟨fun _ _ h => by cases h; rfl, measurable_sigma_mk i, ?_⟩
  intro U hU
  apply MeasurableSpace.measurableSet_iInf.mpr
  intro j
  change MeasurableSet ((Sigma.mk j) ⁻¹' ((Sigma.mk i) '' U))
  by_cases hji : j = i
  · subst j
    rwa [Set.preimage_image_eq _ (show Function.Injective (Sigma.mk i : Fibre i → Sigma Fibre) from fun _ _ h => by cases h; rfl)]
  · have he : (Sigma.mk j) ⁻¹' ((Sigma.mk i) '' U) = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro x ⟨y, _hy, hy⟩
      exact hji (congrArg Sigma.fst hy).symm
    rw [he]
    exact MeasurableSet.empty

/-- Simultaneous whole-calendar characterization, before or after restricting
by the SAME original ID atom (`none` is the original law). All launches,
words, source fields and complete nominal coverage are produced internally.
No conditional innovation or auxiliary expectation law is asserted. -/
theorem ae_terminal_marked_path (ids : Option (CompletePublicTable.IDArray p)) :
    ∀ᵐ w ∂ids.elim (terminalLaw rate rewards C_star C_h control0)
      (fixedIDTerminalLaw rate rewards C_star C_h control0),
      let Z := terminalSource rate rewards C_star C_h control0 w
      let H := (terminalReadout rate rewards C_star C_h control0 w).2.2
      H.Pairwise (fun e f => e.time.val < f.time.val) ∧
      (∀ q : Fin p.T, (∃! e : LogicalCell p rate, e ∈ H ∧ e.time = q) ↔
        nominalEnabled rate rewards C_star C_h q Z = true) ∧
      ((ReferenceCorrectedInitializationLaunch.correctedLaunch rate Z rewards C_star C_h = none ∧ H = []) ∨
        ∃ hl : ∃ active, ReferenceCorrectedInitializationLaunch.correctedLaunch rate Z rewards C_star C_h = some active,
          let W := originalWord Z hl
          (∀ e ∈ H,
            (∃ r, ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h e.time Z = some r ∧
              e.physical = ReferenceActiveHorizonMeasurability.roundRecordCode r) ∧
            e.before = RecordedQueueRun.run Q (W.take (e.time.val - start Z)) ∧
            e.after = RecordedQueueRun.run Q (W.take (e.time.val + 1 - start Z)) ∧
            ∃ hi : e.time.val - start Z < W.length,
              W[e.time.val - start Z].enabled = true ∧
              e.numerical = ReferenceLaterCollectionSourceReadoutMeasurability.numericalCoordinates W[e.time.val - start Z] ∧
              e.arrivals = RecordedQueueRun.acceptedRecord Q e.before W[e.time.val - start Z] ∧
              e.service = (fun j => RecordedQueueRun.recordService (4 * (Q).n) (e.before.registers j) (e.arrivals j)) ∧
              (∀ j, e.service j ≤ 4 * (Q).n ∧ e.after.registers j =
                QueueReplay.transition (4 * (Q).n) (e.before.registers j) (e.arrivals j)) ∧
              (e.before.overflow = true → e.slowSet = frozenSlowSet p ∧ e.fastArm = frozenFastArm p ∧
                e.proposal = false ∧ e.nextSlowSet = frozenSlowSet p))) := by
  have hac : ids.elim (terminalLaw rate rewards C_star C_h control0)
      (fixedIDTerminalLaw rate rewards C_star C_h control0) ≪ terminalLaw rate rewards C_star C_h control0 := by
    cases ids with
    | none => exact Measure.AbsolutelyContinuous.rfl
    | some ids =>
      dsimp only [Option.elim]
      rw [fixedIDTerminalLaw_eq_restrict]
      exact Measure.smul_absolutelyContinuous.trans Measure.absolutelyContinuous_restrict
  apply hac.ae_le
  refine (Filter.Eventually.of_forall (terminalReadout_chronology rate rewards C_star C_h control0)).and ?_
  refine (Filter.Eventually.of_forall (terminalReadout_unique_enabled rate rewards C_star C_h control0)).and ?_
  rw [terminalLaw]
  apply Measure.ae_sum_iff.mpr
  intro i
  apply (measurableEmbedding_sigma_mk i).ae_map_iff.mpr
  cases i with
  | noCall =>
    apply Filter.Eventually.of_forall
    intro w
    by_cases hn : ReferenceCorrectedInitializationLaunch.correctedLaunch rate w.1.val rewards C_star C_h = none
    · exact Or.inl ⟨hn, past_empty_of_no_launch rate rewards C_star C_h w.1.val w.2 hn⟩
    · let hl := Option.ne_none_iff_exists'.mp hn
      refine Or.inr ⟨hl, ?_⟩
      dsimp only
      intro e he
      obtain ⟨hi, hen, hnum, hb, ha, harr, hservice, hall⟩ :=
        originalPast_cell_data rate rewards C_star C_h w.1.val hl w.2 (Fin.last p.T) e he
      exact ⟨ReferenceGeneratedCalendarMarkedPath.firstPast_physical rate rewards C_star C_h w.1.val w.2 (Fin.last p.T) e he,
        hb, ha, hi, hen, hnum, harr, hservice, hall,
        firstPast_stopped rate rewards C_star C_h w.1.val w.2 (Fin.last p.T) e he⟩
  | stopped u t =>
    apply Filter.Eventually.of_forall
    intro w
    refine Or.inr ⟨ReferenceFirstCollectionLogicalNumericalAlignment.firstCall_launch
      rate rewards C_star C_h u t w.1.val w.1.property.1.1, ?_⟩
    dsimp only
    intro e he
    by_cases het : e.time.val < t.val
    · have hp := stoppedPast_strict_prefix rate rewards C_star C_h control0 u t w (Fin.last p.T) e he het
      obtain ⟨hi, hen, hn, hb, ha, harr, hservice, hall⟩ := originalPast_cell_data rate rewards C_star C_h
        w.1.val (ReferenceFirstCollectionLogicalNumericalAlignment.firstCall_launch rate rewards C_star C_h u t w.1.val w.1.property.1.1)
        w.2 t.castSucc e hp
      exact ⟨ReferenceGeneratedCalendarMarkedPath.firstPast_physical rate rewards C_star C_h w.1.val w.2 t.castSucc e hp,
        hb, ha, hi, hen, hn, harr, hservice, hall,
        firstPast_stopped rate rewards C_star C_h w.1.val w.2 t.castSucc e hp⟩
    · have hte : t.val ≤ e.time.val := by omega
      obtain ⟨hen, heq⟩ := ReferenceInitialStoppedCalendar.initialStoppedPast_suffix_fields
        rate rewards C_star C_h control0 u t (Fin.last p.T) w e he hte
      have hr := ReferenceInitialStoppedCalendar.suffixRecord_spec rate rewards C_star C_h u t e.time hte w.1
      have ha := ReferenceInitialStoppedCalendar.suffixCell_after rate rewards C_star C_h u t e.time hte w.1
      have hf := ReferenceInitialStoppedCalendar.suffixCell_frozen rate rewards C_star C_h u t e.time hte w.1
      refine ⟨⟨_, hr.1, congrArg LogicalCell.physical heq⟩, congrArg LogicalCell.before heq,
        (congrArg LogicalCell.after heq).trans ha,
        ReferenceInitialStoppedCalendar.suffix_index_lt rate rewards C_star C_h u t e.time hte w.1,
        hen, congrArg LogicalCell.numerical heq, ?_, ?_, ?_, ?_⟩
      · change e.arrivals = RecordedQueueRun.acceptedRecord Q e.before
          (ReferenceInitialStoppedCalendar.suffixInput rate rewards C_star C_h u t e.time hte w.1)
        rw [congrArg LogicalCell.arrivals heq, congrArg LogicalCell.before heq]
        rfl
      · rw [congrArg LogicalCell.service heq, congrArg LogicalCell.before heq,
          congrArg LogicalCell.arrivals heq]
        rfl
      · intro j
        have h := hf.2.2.2.2 j
        rw [congrArg LogicalCell.service heq, congrArg LogicalCell.arrivals heq,
          congrArg LogicalCell.before heq, congrArg LogicalCell.after heq]
        exact ⟨by rw [h.2.1]; exact Nat.zero_le _, by rw [h.1, h.2.2.1]; rfl⟩
      · intro _hs
        exact ⟨congrArg LogicalCell.slowSet heq, congrArg LogicalCell.fastArm heq,
          congrArg LogicalCell.proposal heq, congrArg LogicalCell.nextSlowSet heq⟩
  | generated b u t =>
    filter_upwards [ReferenceGeneratedCalendarMarkedPath.ae_generatedCalendarLaw_terminal_marked_path
      rate rewards C_star C_h control0 b u t] with w hw
    refine Or.inr ⟨ReferenceFirstCollectionLogicalNumericalAlignment.firstCall_launch
      rate rewards C_star C_h u t _ hw.1, ?_⟩
    dsimp only
    intro e he
    obtain ⟨hp, hb, ha, hi, hen, hnum, harr, hservice, hall, hstop, _horigin⟩ := hw.2.2.2.1 e he
    exact ⟨hp, hb, ha, hi, hen, hnum, harr, hservice, hall, fun hs =>
      ⟨(hstop hs).1, (hstop hs).2.1, (hstop hs).2.2.1, (hstop hs).2.2.2.1⟩⟩
end Bandits.Support.ReferenceExhaustiveGeneratedCalendarSourceLaw

end
