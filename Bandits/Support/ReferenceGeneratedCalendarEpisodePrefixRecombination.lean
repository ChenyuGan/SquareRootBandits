/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceExhaustiveGeneratedCalendarSourceLaw

import Mathlib.Tactic

/-!
# Original-source recombination before the first collection call

All maps below read the same exhaustive raw terminal calendar. In particular,
the original physical source is retained separately from the source after
assignment-vector insertions, and the auxiliary array retains both labels at
every calendar date. Restrictions before the first call are unnormalized.

Sources: ZIP4 `04_slow_fast_learner.tex:176-215,323-390`,
`06_interruptions.tex:391-426`, and `08_main_theorem.tex:78-109`.
These are internal joint-law and archive identities, not an episode slow-set
law or a manuscript closure.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal Classical
open Bandits.Support ConstructorDimensions
open ReferenceFirstLiveChronologicalPrefixFoundation
open ReferenceGeneratedRankCalendarFoundation
open ReferenceGeneratedCalendarPathAgreement
open ReferenceGeneratedCalendarMarkedPath
open ReferenceGeneratedCalendarNativePreservation (calendarNativePrelist)
open ReferencePostInvocationSupportedDisintegration (branchLaw)
open ReferenceSourcePrefixHistoryFiltration (sourcePrefix)

namespace Bandits.Support.ReferenceGeneratedCalendarEpisodePrefixRecombination

variable {p : ConstructorDimensions.Parameters}

abbrev Source := BootstrapPrivateRoundStreams.SourceInput
abbrev Auxiliary := ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray

local instance sourceMeasurableSpace : MeasurableSpace (Source p) := by
  change MeasurableSpace (CompletePublicTable.PublishedOutput p ×
    BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

local instance optionMeasurableSpace {A : Type*} [MeasurableSpace A] :
    MeasurableSpace (Option A) := LaterAssignmentStartMeasurability.optionMeasurableSpace

private theorem measurable_sigma_mk {I : Type*} {B : I → Type*}
    [∀ i, MeasurableSpace (B i)] (i : I) : Measurable (Sigma.mk i : B i → Sigma B) :=
  measurable_iff_le_map.mpr (iInf_le _ i)

private theorem measurable_sigma_elim {I Y : Type*} {B : I → Type*}
    [∀ i, MeasurableSpace (B i)] [MeasurableSpace Y]
    (f : Sigma B → Y) (hf : ∀ i, Measurable (fun x : B i => f ⟨i, x⟩)) : Measurable f := by
  intro U hU
  apply MeasurableSpace.measurableSet_iInf.mpr
  intro i
  exact hf i hU

variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
  (control0 : ContinuousLearningRows.TimeControl p)

local notation "mu" => BootstrapPrivateRoundStreams.sourceInputLaw p
local notation "alpha" => ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p
local notation "Lambda" => ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalLaw rate rewards C_star C_h control0
local notation "Z0" => ReferenceExhaustiveGeneratedCalendarSourceLaw.originalSource rate rewards C_star C_h
local notation "past" => ReferenceFirstCollectionLogicalPrefixExtension.extendedPast rate rewards C_star C_h

/-- The full original auxiliary array read from the actual terminal observer. -/
def auxiliary (w : ReferenceExhaustiveGeneratedCalendarSourceLaw.Omega rate rewards C_star C_h) : Auxiliary p :=
  (ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalReadout rate rewards C_star C_h control0 w).2.1

/-- The actual terminal archive, restricted to dates strictly below `n`. -/
def archiveBefore (n : Fin (p.T + 1)) (w : ReferenceExhaustiveGeneratedCalendarSourceLaw.Omega rate rewards C_star C_h) :
    List (LogicalCell p rate) :=
  (ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalReadout rate rewards C_star C_h control0 w).2.2.filter
    (fun e => e.time.val < n.val)

/-- The literal predictable event on the original source. -/
def beforeFirstCall (n : Fin (p.T + 1)) : Set (ReferenceExhaustiveGeneratedCalendarSourceLaw.Omega rate rewards C_star C_h) :=
  {w | ReferenceFirstCollectionLogicalPrefixExtension.NoCallBefore rate rewards C_star C_h n (Z0 w)}

/-- Original physical input and the complete original auxiliary tape, read jointly. -/
def originalPair (w : ReferenceExhaustiveGeneratedCalendarSourceLaw.Omega rate rewards C_star C_h) : Source p × Auxiliary p :=
  (Z0 w, auxiliary rate rewards C_star C_h control0 w)

/-- The same original pair on each literal raw branch payload. -/
def componentOriginalPair (i : ReferenceExhaustiveGeneratedCalendarSourceLaw.Component p) (w : ReferenceExhaustiveGeneratedCalendarSourceLaw.Payload rate rewards C_star C_h i) :
    Source p × Auxiliary p :=
  (ReferenceExhaustiveGeneratedCalendarSourceLaw.componentOriginalSource rate rewards C_star C_h i w,
    (ReferenceExhaustiveGeneratedCalendarSourceLaw.componentReadout rate rewards C_star C_h control0 i w).2.1)

theorem measurable_componentOriginalPair (i : ReferenceExhaustiveGeneratedCalendarSourceLaw.Component p) :
    Measurable (componentOriginalPair rate rewards C_star C_h control0 i) := by
  cases i with
  | noCall => exact (measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd
  | stopped u t => exact (measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd
  | generated b u t =>
    exact ((measurable_calendarOriginalLift rate rewards C_star C_h b u t _).fst.fst.subtype_val).prodMk
      (measurable_calendarOriginalLift rate rewards C_star C_h b u t _).fst.snd

theorem measurable_originalPair : Measurable (originalPair rate rewards C_star C_h control0) :=
  measurable_sigma_elim _ (measurable_componentOriginalPair rate rewards C_star C_h control0)

include control0 in
theorem measurable_originalSource : Measurable (ReferenceExhaustiveGeneratedCalendarSourceLaw.originalSource rate rewards C_star C_h) :=
  (measurable_originalPair rate rewards C_star C_h control0).fst

theorem measurable_auxiliary : Measurable (auxiliary rate rewards C_star C_h control0) :=
  (ReferenceExhaustiveGeneratedCalendarSourceLaw.measurable_terminalReadout rate rewards C_star C_h control0).snd.fst

include control0 in
theorem measurableSet_beforeFirstCall (n : Fin (p.T + 1)) :
    MeasurableSet (beforeFirstCall rate rewards C_star C_h n) :=
  (ReferenceFirstCollectionLogicalPrefixExtension.measurableSet_noCallBefore rate rewards C_star C_h control0 n).preimage
    (measurable_originalSource rate rewards C_star C_h control0)

private theorem branchLaw_originalPair (b : Bool) (u t : Fin p.T) :
    (branchLaw rate rewards C_star C_h control0 b u t).map
      (fun w => (w.1.1.val, w.1.2)) =
      ((mu).restrict (ReferenceExhaustiveGeneratedCalendarSourceLaw.componentEvent rate rewards C_star C_h (.generated b u t))).prod alpha := by
  cases b with
  | false =>
    change (ReferenceFirstNextInvocationJointLift.nonrenewedLiftLaw rate rewards C_star C_h u t control0).map
      ((Prod.map Subtype.val id) ∘ Prod.fst) = _
    rw [← Measure.map_map (measurable_subtype_coe.prodMap measurable_id) measurable_fst,
      ReferenceFirstNextInvocationJointLift.nonrenewedLiftLaw_map_fst]
    change (((ReferenceFirstNextInvocationJointLift.eventSourceLaw rate rewards C_star C_h u t).prod alpha).map
      (Prod.map Subtype.val id)) = _
    rw [← Measure.map_prod_map _ _ measurable_subtype_coe measurable_id, Measure.map_id]
    congr 1
    exact map_comap_subtype_coe
      (ReferenceFirstLiveCollectionPathJoin.measurableSet_firstLiveCollectionEvent rate rewards C_star C_h u t) _
  | true =>
    change (ReferenceFirstCollectionRenewalFibreExtension.renewalLiftLaw rate rewards C_star C_h u t).map
      ((Prod.map Subtype.val id) ∘ Prod.fst) = _
    rw [← Measure.map_map (measurable_subtype_coe.prodMap measurable_id) measurable_fst,
      ReferenceFirstCollectionRenewalFibreExtension.renewalLiftLaw_map_fst]
    change (((ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t).prod alpha).map
      (Prod.map Subtype.val id)) = _
    rw [← Measure.map_prod_map _ _ measurable_subtype_coe measurable_id, Measure.map_id,
      ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw_map_val]
    rfl

/-- Each raw component retains the original whole source and whole tape jointly. -/
theorem componentLaw_map_originalPair (i : ReferenceExhaustiveGeneratedCalendarSourceLaw.Component p) :
    (ReferenceExhaustiveGeneratedCalendarSourceLaw.componentLaw rate rewards C_star C_h control0 i).map
      (componentOriginalPair rate rewards C_star C_h control0 i) =
      ((mu).restrict (ReferenceExhaustiveGeneratedCalendarSourceLaw.componentEvent rate rewards C_star C_h i)).prod alpha := by
  cases i with
  | noCall => exact ReferenceExhaustiveGeneratedCalendarSourceLaw.noCallLaw_originalPair rate rewards C_star C_h control0
  | stopped u t => exact ReferenceInitialStoppedCalendar.initialStoppedSourceLaw_originalPair rate rewards C_star C_h u t
  | generated b u t =>
    change (generatedCalendarLaw rate rewards C_star C_h control0 b u t (Fin.last p.T) t.isLt).map
      ((fun w => (w.1.1.val, w.1.2)) ∘ calendarOriginalLift rate rewards C_star C_h b u t _) = _
    have hf : Measurable (fun w : ReferencePostInvocationPrefixLocality.BranchLift
        rate rewards C_star C_h b u t => (w.1.1.val, w.1.2)) :=
      (measurable_fst.fst.subtype_val).prodMk measurable_fst.snd
    calc
      _ = ((generatedCalendarLaw rate rewards C_star C_h control0 b u t
          (Fin.last p.T) t.isLt).map (calendarOriginalLift rate rewards C_star C_h b u t _)).map
          (fun w => (w.1.1.val, w.1.2)) :=
        (Measure.map_map hf (measurable_calendarOriginalLift rate rewards C_star C_h b u t _)).symm
      _ = _ := by
        rw [generatedCalendarLaw_map_originalLift]
        exact branchLaw_originalPair rate rewards C_star C_h control0 b u t

/-- Exhaustive unnormalized recombination recovers the full original product law. -/
theorem terminalLaw_map_originalPair :
    (Lambda).map (originalPair rate rewards C_star C_h control0) = (mu).prod alpha := by
  rw [ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalLaw, Measure.map_sum (measurable_originalPair rate rewards C_star C_h control0).aemeasurable]
  simp_rw [Measure.map_map (measurable_originalPair rate rewards C_star C_h control0) (measurable_sigma_mk _)]
  change Measure.sum (fun i => (ReferenceExhaustiveGeneratedCalendarSourceLaw.componentLaw rate rewards C_star C_h control0 i).map
    (componentOriginalPair rate rewards C_star C_h control0 i)) = _
  simp_rw [componentLaw_map_originalPair]
  rw [← Measure.prod_sum_left, ReferenceExhaustiveGeneratedCalendarSourceLaw.sum_restrict_componentEvent]

open ReferenceFirstCollectionLogicalPrefixExtension

private theorem liveTag_time (q : Fin p.T) (z : Source p) (a : Auxiliary p)
    (e : LogicalCell p rate) (he : ReferenceFirstLiveCalendarMarkedTransition.currentCellTag rate rewards C_star C_h q (z, a) = .inr e) :
    e.time = q := by
  rw [ReferenceFirstLiveCalendarMarkedTransition.currentCellTag_eq_lookup] at he
  split at he
  next hs =>
    unfold ReferenceActiveHorizonMeasurability.listObservationAt at he
    cases hg : (firstLiveChronologicalPrefix rate rewards C_star C_h (z, a))[q.val -
        ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h]? with
    | none => rw [hg] at he; cases he
    | some d =>
      rw [hg] at he
      cases Sum.inr.inj he
      obtain ⟨hi, hd⟩ := List.getElem?_eq_some_iff.mp hg
      have hiw : q.val - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h <
          (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow rate rewards C_star C_h z).length := by
        simpa only [firstLiveChronologicalPrefix_length,
          ReferenceFirstLiveOverflowReadout.wholeFirstLiveLength] using hi
      have ht := ReferenceFirstLiveChronologicalPrefixCausality.firstLiveChronologicalPrefix_cellTime
        rate rewards C_star C_h z a ⟨_, hiw⟩
      rw [hd] at ht
      have hp : ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow rate rewards C_star C_h z <+:
          ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h :=
        List.takeWhile_prefix _
      have hr : (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[q.val - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h]? =
          some ((ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow rate rewards C_star C_h z)[q.val - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h]'hiw) := by
        rw [List.getElem?_eq_getElem (hiw.trans_le hp.length_le), ← hp.getElem hiw]
      have htime := ReferenceFirstCollectionRenewalRecordingFeedback.complete_record_time
        rate z rewards C_star C_h _ _ hr
      apply Fin.ext
      rw [ht, htime]
      omega
  next => cases he

private theorem collectionCell_time (q : Fin p.T) (U : SlowSet p) (za : Source p × Auxiliary p)
    (e : LogicalCell p rate) (he : collectionCellAt rate rewards C_star C_h q U za = some e) :
    e.time = q := by
  unfold collectionCellAt ReferenceFirstCollectionOneRoundLogicalCell.sourceCell? at he
  split at he
  · dsimp only at he
    unfold ReferenceFirstCollectionOneRoundLogicalCell.cellWithScalar? at he
    split at he
    · rw [← Option.some.inj he]
      rfl
    · cases he
  · cases he

private theorem prefixCandidate_time (q : Fin p.T) (za : Source p × Auxiliary p)
    (S : Option (SlowSet p) × List (LogicalCell p rate)) (e : LogicalCell p rate)
    (he : prefixCandidate (ReferenceFirstLiveCalendarMarkedTransition.currentCellTag rate rewards C_star C_h q)
      (fun v => collectionCellAt rate rewards C_star C_h q v.1 v.2) za S = some e) : e.time = q := by
  unfold prefixCandidate at he
  cases ht : ReferenceFirstLiveCalendarMarkedTransition.currentCellTag rate rewards C_star C_h q za with
  | inr c =>
    rw [ht] at he
    cases Option.some.inj he
    exact liveTag_time rate rewards C_star C_h q za.1 za.2 e ht
  | inl u =>
    rw [ht] at he
    cases hU : S.1 with
    | none => rw [hU] at he; cases he
    | some U =>
      rw [hU] at he
      exact collectionCell_time rate rewards C_star C_h q U za e he

/-- Every entry of the literal extended recursion is strictly in its past. -/
theorem extendedPast_time_lt (n : Fin (p.T + 1)) (za : Source p × Auxiliary p) :
    ∀ e ∈ past n za, e.time.val < n.val := by
  have hall : ∀ k (hk : k ≤ p.T), ∀ e ∈
      (extendedPrefixStateAux rate rewards C_star C_h k hk za).2, e.time.val < k := by
    intro k
    induction k with
    | zero => intro hk e he; cases he
    | succ k ih =>
      intro hk e he
      let q : Fin p.T := ⟨k, Nat.lt_of_succ_le hk⟩
      let S := extendedPrefixStateAux rate rewards C_star C_h k (Nat.le_of_succ_le hk) za
      change e ∈ (prefixStep (fun c : LogicalCell p rate => c.nextSlowSet)
        (ReferenceFirstLiveCalendarMarkedTransition.currentCellTag rate rewards C_star C_h q)
        (fun v => collectionCellAt rate rewards C_star C_h q v.1 v.2) za S).2 at he
      unfold prefixStep at he
      cases hc : prefixCandidate (ReferenceFirstLiveCalendarMarkedTransition.currentCellTag rate rewards C_star C_h q)
          (fun v => collectionCellAt rate rewards C_star C_h q v.1 v.2) za S with
      | none =>
        rw [hc] at he
        exact (ih _ e he).trans (Nat.lt_succ_self _)
      | some c =>
        rw [hc] at he
        rcases List.mem_append.mp he with he | he
        · exact (ih _ e he).trans (Nat.lt_succ_self _)
        · rw [List.mem_singleton.mp he, prefixCandidate_time rate rewards C_star C_h q za S c hc]
          exact Nat.lt_succ_self _
  exact hall n.val (Nat.le_of_lt_succ n.isLt)

/-- Filtering the actual extended recursion recovers every shorter strict prefix. -/
theorem extendedPast_filter (n m : Fin (p.T + 1)) (hnm : n.val ≤ m.val)
    (za : Source p × Auxiliary p) :
    (past m za).filter (fun e => e.time.val < n.val) = past n za := by
  have hall : ∀ k (hk : k ≤ p.T) (hnk : n.val ≤ k),
      ((extendedPrefixStateAux rate rewards C_star C_h k hk za).2.filter
        (fun e => e.time.val < n.val)) = past n za := by
    intro k hk hnk
    induction hnk with
    | refl =>
      exact List.filter_eq_self.mpr (fun e he =>
        decide_eq_true (extendedPast_time_lt rate rewards C_star C_h n za e he))
    | @step k hnk ih =>
      let q : Fin p.T := ⟨k, Nat.lt_of_succ_le hk⟩
      let S := extendedPrefixStateAux rate rewards C_star C_h k (Nat.le_of_succ_le hk) za
      change ((prefixStep (fun c : LogicalCell p rate => c.nextSlowSet)
        (ReferenceFirstLiveCalendarMarkedTransition.currentCellTag rate rewards C_star C_h q)
        (fun v => collectionCellAt rate rewards C_star C_h q v.1 v.2) za S).2.filter
          (fun e => e.time.val < n.val)) = _
      unfold prefixStep
      cases hc : prefixCandidate (ReferenceFirstLiveCalendarMarkedTransition.currentCellTag rate rewards C_star C_h q)
          (fun v => collectionCellAt rate rewards C_star C_h q v.1 v.2) za S with
      | none =>
        exact ih (Nat.le_of_succ_le hk)
      | some c =>
        have ht := prefixCandidate_time rate rewards C_star C_h q za S c hc
        have hn : ¬ c.time.val < n.val := by rw [ht]; exact Nat.not_lt_of_ge hnk
        simp only [List.filter_append, List.filter_cons, decide_eq_false hn,
          Bool.false_eq_true, ↓reduceIte, List.filter_nil, List.append_nil]
        exact ih (Nat.le_of_succ_le hk)
  exact hall m.val (Nat.le_of_lt_succ m.isLt) hnm

private theorem noCallBefore_le_firstCell (u t : Fin p.T) (z : Source p)
    (hz : z ∈ ReferenceFirstCollectionAuxiliarySeeds.actualCollectionCallCell rate rewards C_star C_h u t)
    (n : Fin (p.T + 1)) (hn : NoCallBefore rate rewards C_star C_h n z) : n.val ≤ t.val := by
  by_contra h
  have ht : t.val < n.val := by omega
  have hb := (ReferenceFirstCollectionPrecallCalendarSupport.before_cut_iff_no_call_through
    rate rewards C_star C_h t z).mpr (fun v hv =>
      (noCallAt_iff_callAt_none rate rewards C_star C_h v z).mp (hn v (hv.trans_lt ht)))
  rw [ReferenceFirstCollectionPrecallCalendarSupport.firstCallBoundary_on_firstCell
    rate rewards C_star C_h u t z hz] at hb
  exact (Nat.lt_irrefl _ hb)

private theorem root_prelist_original (b : Bool) (u t : Fin p.T)
    (w : CalendarSample rate rewards C_star C_h b u t 0) :
    calendarNativePrelist rate rewards C_star C_h control0 b u t 0 (by omega) w =
      past t.castSucc ((calendarOriginalLift rate rewards C_star C_h b u t 0 w).1.1.val,
        (calendarOriginalLift rate rewards C_star C_h b u t 0 w).1.2) := by
  cases b with
  | false =>
    change (ReferenceFirstNextInvocationJointLift.EventSource rate rewards C_star C_h u t × Auxiliary p) ×
      AssignmentParameterFibreKernel.AssignmentVector p at w
    unfold calendarNativePrelist
    rw [calendarObservation_initial rate rewards C_star C_h control0 false u t (by omega) w]
    change (ReferenceFirstNextInstallationTransitionLaw.postHistory
      (ReferenceFirstNextInstallationTransitionLaw.nonrenewedTransition rate rewards C_star C_h control0 u t w)).dropLast = _
    rw [ReferenceFirstNextInstallationTransitionLaw.nonrenewedTransition_postHistory, List.dropLast_concat]
    rfl
  | true =>
    change ReferenceFirstCollectionRenewalInstallationCoupling.RenewalLift rate rewards C_star C_h u t at w
    unfold calendarNativePrelist
    rw [calendarObservation_initial rate rewards C_star C_h control0 true u t (by omega) w]
    change (ReferenceFirstNextInstallationTransitionLaw.postHistory
      (ReferenceFirstNextInstallationTransitionLaw.renewedTransition rate rewards C_star C_h control0 u t w)).dropLast = _
    rw [ReferenceFirstNextInstallationTransitionLaw.renewedTransition_postHistory, List.dropLast_concat]
    rfl

private theorem rootCell_time (b : Bool) (u t : Fin p.T)
    (w : CalendarSample rate rewards C_star C_h b u t 0) :
    (calendarRootCell rate rewards C_star C_h control0 b u t w).time = t := by
  cases b <;> exact ReferenceFirstNextInstallationCellFactors.actualFirstCell_time
    rate rewards C_star C_h control0 t _ _

/-- The full generated archive consumes its original pre-root list. Later
assignment insertions and every later optional cell leave this strict prefix intact. -/
theorem generated_archiveBefore (b : Bool) (u t : Fin p.T) (n : Fin (p.T + 1))
    (hnt : n.val ≤ t.val) (k : ℕ) (hk : t.val + 1 + k ≤ p.T)
    (w : CalendarSample rate rewards C_star C_h b u t k) :
    ((calendarStoredState rate rewards C_star C_h control0 b u t k hk w).2.filter
      (fun e => e.time.val < n.val)) =
      past n ((calendarOriginalLift rate rewards C_star C_h b u t k w).1.1.val,
        (calendarOriginalLift rate rewards C_star C_h b u t k w).1.2) := by
  induction k with
  | zero =>
    rw [(calendarObservation_root rate rewards C_star C_h control0 b u t hk w).2.1]
    have hn : ¬ (calendarRootCell rate rewards C_star C_h control0 b u t w).time.val < n.val := by
      rw [rootCell_time rate rewards C_star C_h control0 b u t w]
      exact Nat.not_lt_of_ge hnt
    simp only [List.filter_append, List.filter_cons, decide_eq_false hn,
      Bool.false_eq_true, ↓reduceIte, List.filter_nil, List.append_nil]
    rw [root_prelist_original rate rewards C_star C_h control0 b u t w]
    exact extendedPast_filter rate rewards C_star C_h n t.castSucc hnt _
  | succ k ih =>
    change CalendarSample rate rewards C_star C_h b u t k ×
      AssignmentParameterFibreKernel.AssignmentVector p at w
    rw [calendarStoredState_succ rate rewards C_star C_h control0 b u t k (by omega) w.1 w.2]
    cases hc : calendarStepCell rate rewards C_star C_h control0 b u t k (by omega) w.1 w.2 with
    | none => exact ih (by omega) w.1
    | some e =>
      have ht := calendarStepCell_time rate rewards C_star C_h control0 b u t k (by omega) w.1 w.2 e hc
      have hn : ¬ e.time.val < n.val := by rw [ht]; dsimp; omega
      simp only [List.filter_append, List.filter_cons, decide_eq_false hn,
        Bool.false_eq_true, ↓reduceIte, List.filter_nil, List.append_nil]
      exact ih (by omega) w.1

/-- The initially stopped branch retains the identical strict prefix, including
the first overflow update when it occurs before the first call. -/
theorem stopped_archiveBefore (u t : Fin p.T) (n : Fin (p.T + 1)) (hnt : n.val ≤ t.val)
    (w : ReferenceInitialStoppedCalendar.StoppedSource rate rewards C_star C_h u t × Auxiliary p) :
    ((ReferenceInitialStoppedCalendar.initialStoppedPast rate rewards C_star C_h control0 u t
      (Fin.last p.T) w).filter (fun e => e.time.val < n.val)) = past n (w.1.val, w.2) := by
  have hall : ∀ k (hk : k ≤ p.T) (htk : t.val ≤ k),
      ((ReferenceInitialStoppedCalendar.calendarPastAux rate rewards C_star C_h control0 t k hk
        (w.1.val, w.2)).filter (fun e => e.time.val < n.val)) = past n (w.1.val, w.2) := by
    intro k hk htk
    induction htk with
    | refl =>
      rw [ReferenceInitialStoppedCalendar.calendarPastAux_before rate rewards C_star C_h control0 t
        t.val hk le_rfl]
      exact extendedPast_filter rate rewards C_star C_h n t.castSucc hnt _
    | @step k htk ih =>
      let q : Fin p.T := ⟨k, Nat.lt_of_succ_le hk⟩
      change ((ReferenceInitialStoppedCalendar.initialStoppedPast rate rewards C_star C_h control0 u t
        q.succ w).filter (fun e => e.time.val < n.val)) = _
      rw [ReferenceInitialStoppedCalendar.initialStoppedPast_succ rate rewards C_star C_h control0 u t q htk w]
      have hn : ¬ (ReferenceInitialStoppedCalendar.suffixCell rate rewards C_star C_h u t q htk w.1).time.val < n.val := by
        change ¬ k < n.val
        exact Nat.not_lt_of_ge (hnt.trans htk)
      split
      · simp only [List.filter_append, List.filter_cons, decide_eq_false hn,
          Bool.false_eq_true, ↓reduceIte, List.filter_nil, List.append_nil]
        exact ih (Nat.le_of_succ_le hk)
      · simp only [List.append_nil]
        exact ih (Nat.le_of_succ_le hk)
  exact hall p.T le_rfl t.isLt.le

/-- Pointwise join of the actual archive with the SAME original whole source
and whole auxiliary tape. Every raw component, including null components, is covered. -/
theorem archiveBefore_eq_extendedPast (n : Fin (p.T + 1))
    (w : ReferenceExhaustiveGeneratedCalendarSourceLaw.Omega rate rewards C_star C_h)
    (hw : w ∈ beforeFirstCall rate rewards C_star C_h n) :
    archiveBefore rate rewards C_star C_h control0 n w =
      past n (originalPair rate rewards C_star C_h control0 w) := by
  rcases w with ⟨i, w⟩
  cases i with
  | noCall => exact extendedPast_filter rate rewards C_star C_h n (Fin.last p.T) (Nat.le_of_lt_succ n.isLt) _
  | stopped u t =>
    exact stopped_archiveBefore rate rewards C_star C_h control0 u t n
      (noCallBefore_le_firstCell rate rewards C_star C_h u t w.1.val w.1.property.1.1 n hw) w
  | generated b u t =>
    have hz : (calendarOriginalLift rate rewards C_star C_h b u t (p.T - (t.val + 1)) w).1.1.val ∈
        ReferenceFirstCollectionAuxiliarySeeds.actualCollectionCallCell rate rewards C_star C_h u t := by
      cases b with
      | false => exact (ReferenceFirstLiveCollectionPathJoin.firstLiveCollectionEvent_facts
          rate rewards C_star C_h u t _ (calendarOriginalLift rate rewards C_star C_h false u t _ w).1.1.property).1
      | true => exact (calendarOriginalLift rate rewards C_star C_h true u t _ w).1.1.property.1
    exact generated_archiveBefore rate rewards C_star C_h control0 b u t n
      (noCallBefore_le_firstCell rate rewards C_star C_h u t _ hz n hw) _ (by omega) w

private instance sumSingleton {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSingletonClass A] [MeasurableSingletonClass B] : MeasurableSingletonClass (A ⊕ B) where
  measurableSet_singleton x := by
    cases x with
    | inl a => simpa only [Set.image_singleton] using (MeasurableSet.singleton a).inl_image
    | inr b => simpa only [Set.image_singleton] using (MeasurableSet.singleton b).inr_image

private instance listSingleton {A : Type*} [MeasurableSpace A]
    [MeasurableSingletonClass A] : MeasurableSingletonClass (List A) where
  measurableSet_singleton L := by
    have hi : Function.Injective (ReferenceActiveHorizonMeasurability.listObservationCoordinates (α := A)) := by
      intro B C h
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
    simp only [Set.mem_singleton_iff, Set.mem_preimage, hi.eq_iff]

private theorem measurable_list_take {A : Type*} [MeasurableSpace A] (n : ℕ) :
    Measurable (fun L : List A => L.take n) := by
  have hc := ReferenceActiveHorizonMeasurability.measurable_listObservationCoordinates (α := A)
  apply measurable_comap_iff.mpr
  change Measurable (fun L : List A => (((L.take n).length),
    fun j => ReferenceActiveHorizonMeasurability.listObservationAt (L.take n) j))
  simp only [List.length_take]
  apply ((measurable_of_countable (fun k : ℕ => min n k)).comp hc.fst).prodMk
  apply measurable_pi_iff.mpr
  intro j
  by_cases hj : j < n
  · simpa only [Function.comp_def, ReferenceActiveHorizonMeasurability.listObservationCoordinates,
      ReferenceActiveHorizonMeasurability.listObservationAt, List.getElem?_take, hj, ite_true] using
        (measurable_pi_apply j).comp hc.snd
  · have heq : (fun L : List A => ReferenceActiveHorizonMeasurability.listObservationAt (L.take n) j) =
        fun _ => (Sum.inl () : Unit ⊕ A) := by
      funext L
      simp only [ReferenceActiveHorizonMeasurability.listObservationAt, List.getElem?_take, hj, ite_false]
    rw [heq]
    exact measurable_const

private theorem chronological_filter_eq_take (H : List (LogicalCell p rate))
    (hH : H.Pairwise (fun e f => e.time.val < f.time.val)) (n : ℕ) :
    H.filter (fun e => e.time.val < n) = H.take (H.filter (fun e => e.time.val < n)).length := by
  induction H with
  | nil => rfl
  | cons e H ih =>
    obtain ⟨heH, hH⟩ := List.pairwise_cons.mp hH
    by_cases he : e.time.val < n
    · simp only [List.filter_cons, decide_eq_true he, ite_true, List.length_cons, List.take_succ_cons]
      exact congrArg (List.cons e) (ih hH)
    · have hf : H.filter (fun e => e.time.val < n) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro c hc
        have ht := heH c hc
        simpa only [decide_eq_true_eq] using (show ¬ c.time.val < n by omega)
      simp only [List.filter_cons, decide_eq_false he, Bool.false_eq_true, ite_false,
        hf, List.length_nil, List.take_zero]

/-- The strict-prefix projection is measurable in the original continuous cell spaces. -/
theorem measurable_archiveBefore (n : Fin (p.T + 1)) :
    Measurable (archiveBefore rate rewards C_star C_h control0 n) := by
  let H := fun w => (ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalReadout
    rate rewards C_star C_h control0 w).2.2
  have hH : Measurable H :=
    (ReferenceExhaustiveGeneratedCalendarSourceLaw.measurable_terminalReadout rate rewards C_star C_h control0).snd.snd
  have ht : Measurable (fun w => (H w).map LogicalCell.time) :=
    ReferenceActiveHorizonMeasurability.measurable_list_map H hH _
      ReferenceFirstLiveChronologicalPrefixMeasurability.measurable_logicalCell_time
  have hc : Measurable (fun w => (((H w).map LogicalCell.time).filter
      (fun t => t.val < n.val)).length) :=
    (measurable_of_countable (fun L : List (Fin p.T) => (L.filter (fun t : Fin p.T => t.val < n.val)).length)).comp ht
  have htake : Measurable (fun v : ℕ × List (LogicalCell p rate) => v.2.take v.1) :=
    measurable_from_prod_countable_right (fun k => measurable_list_take k)
  convert htake.comp (hc.prodMk hH) using 1
  funext w
  change (H w).filter (fun e => e.time.val < n.val) = _
  rw [chronological_filter_eq_take rate (H w)
    (ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalReadout_chronology rate rewards C_star C_h control0 w)]
  simp only [Function.comp_apply, List.filter_map, List.length_map, Function.comp_def]

/-- All three entries of the actual archive graph, including the whole tape. -/
def originalArchiveGraph (n : Fin (p.T + 1))
    (w : ReferenceExhaustiveGeneratedCalendarSourceLaw.Omega rate rewards C_star C_h) :
    ReferenceInitialStoppedCalendar.Observer rate :=
  (Z0 w, (auxiliary rate rewards C_star C_h control0 w,
    archiveBefore rate rewards C_star C_h control0 n w))

/-- The canonical graph on the same original source/tape pair. -/
def extendedPastGraph (n : Fin (p.T + 1)) (za : Source p × Auxiliary p) :
    ReferenceInitialStoppedCalendar.Observer rate := (za.1, (za.2, past n za))

theorem measurable_originalArchiveGraph (n : Fin (p.T + 1)) :
    Measurable (originalArchiveGraph rate rewards C_star C_h control0 n) :=
  (measurable_originalSource rate rewards C_star C_h control0).prodMk
    ((measurable_auxiliary rate rewards C_star C_h control0).prodMk
      (measurable_archiveBefore rate rewards C_star C_h control0 n))

include control0 in
theorem measurable_extendedPastGraph (n : Fin (p.T + 1)) :
    Measurable (extendedPastGraph rate rewards C_star C_h n) :=
  measurable_fst.prodMk (measurable_snd.prodMk
    (measurable_extendedPast rate rewards C_star C_h control0 n))

/-- Restricting by the predictable event retains its exact, unnormalized mass. -/
theorem terminalLaw_restrict_map_originalPair (n : Fin (p.T + 1)) :
    ((Lambda).restrict (beforeFirstCall rate rewards C_star C_h n)).map
      (originalPair rate rewards C_star C_h control0) =
      ((mu).prod alpha).restrict {za | NoCallBefore rate rewards C_star C_h n za.1} := by
  rw [← terminalLaw_map_originalPair rate rewards C_star C_h control0]
  exact (Measure.restrict_map (μ := Lambda)
    (measurable_originalPair rate rewards C_star C_h control0)
    (s := {za : Source p × Auxiliary p | NoCallBefore rate rewards C_star C_h n za.1})
    ((measurableSet_noCallBefore rate rewards C_star C_h control0 n).preimage measurable_fst)).symm

/-- Full joint graph equality, against arbitrary measurable tests of the source,
the entire auxiliary array, and the actual strict pre-first-call archive. -/
theorem terminalLaw_restrict_map_originalArchiveGraph (n : Fin (p.T + 1)) :
    ((Lambda).restrict (beforeFirstCall rate rewards C_star C_h n)).map
      (originalArchiveGraph rate rewards C_star C_h control0 n) =
      (((mu).prod alpha).restrict {za | NoCallBefore rate rewards C_star C_h n za.1}).map
        (extendedPastGraph rate rewards C_star C_h n) := by
  calc
    _ = ((Lambda).restrict (beforeFirstCall rate rewards C_star C_h n)).map
        ((extendedPastGraph rate rewards C_star C_h n) ∘
          originalPair rate rewards C_star C_h control0) := by
      apply Measure.map_congr
      filter_upwards [ae_restrict_mem (measurableSet_beforeFirstCall rate rewards C_star C_h control0 n)] with w hw
      exact congrArg (fun L => (Z0 w, (auxiliary rate rewards C_star C_h control0 w, L)))
        (archiveBefore_eq_extendedPast rate rewards C_star C_h control0 n w hw)
    _ = _ := by
      rw [← Measure.map_map (measurable_extendedPastGraph rate rewards C_star C_h control0 n)
        (measurable_originalPair rate rewards C_star C_h control0), terminalLaw_restrict_map_originalPair]

/-- Arbitrary nonnegative Borel joint tests of all three retained entries. -/
theorem terminalLaw_archive_joint_test (n : Fin (p.T + 1))
    (Phi : ReferenceInitialStoppedCalendar.Observer rate → ℝ≥0∞) (hPhi : Measurable Phi) :
    (∫⁻ w, Phi (originalArchiveGraph rate rewards C_star C_h control0 n w)
      ∂(Lambda).restrict (beforeFirstCall rate rewards C_star C_h n)) =
      ∫⁻ za, Phi (extendedPastGraph rate rewards C_star C_h n za)
        ∂((mu).prod alpha).restrict {za | NoCallBefore rate rewards C_star C_h n za.1} := by
  rw [← lintegral_map hPhi (measurable_originalArchiveGraph rate rewards C_star C_h control0 n),
    terminalLaw_restrict_map_originalArchiveGraph,
    lintegral_map hPhi (measurable_extendedPastGraph rate rewards C_star C_h control0 n)]

/-- Forget the unused label-one coordinates only after retaining the full graph. -/
def observationProjection (n : Fin (p.T + 1)) (v : ReferenceInitialStoppedCalendar.Observer rate) :
    Observation rate :=
  (sourcePrefix control0 n.val v.1,
    (ReferenceFirstLiveCalendarMarkedTransition.labelZero v.2.1, v.2.2))

/-- The accepted observer with its list read from the actual terminal archive. -/
def prefixObservation (n : Fin (p.T + 1))
    (w : ReferenceExhaustiveGeneratedCalendarSourceLaw.Omega rate rewards C_star C_h) : Observation rate :=
  observationProjection rate control0 n (originalArchiveGraph rate rewards C_star C_h control0 n w)

/-- Original current physical control and the ONE current label-one scalar. -/
def currentInnovation (q : Fin p.T)
    (w : ReferenceExhaustiveGeneratedCalendarSourceLaw.Omega rate rewards C_star C_h) :
    ContinuousLearningRows.TimeControl p × ContinuousControlSlice.Scalar :=
  (ReferenceSourceCurrentControlFreshness.u_t p q (Z0 w),
    auxiliary rate rewards C_star C_h control0 w (q, 1))

theorem measurable_observationProjection (n : Fin (p.T + 1)) :
    Measurable (observationProjection rate control0 n) :=
  ((ReferenceSourcePrefixHistoryFiltration.measurable_sourcePrefix control0 n.val).comp measurable_fst).prodMk
    (((ReferenceFirstLiveCalendarMarkedTransition.measurable_labelZero p).comp measurable_snd.fst).prodMk
      measurable_snd.snd)

theorem measurable_prefixObservation (n : Fin (p.T + 1)) :
    Measurable (prefixObservation rate rewards C_star C_h control0 n) :=
  (measurable_observationProjection rate control0 n).comp
    (measurable_originalArchiveGraph rate rewards C_star C_h control0 n)

theorem measurable_currentInnovation (q : Fin p.T) :
    Measurable (currentInnovation rate rewards C_star C_h control0 q) :=
  ((ReferenceSourceCurrentControlFreshness.measurable_u_t q).comp
    (measurable_originalSource rate rewards C_star C_h control0)).prodMk
    ((measurable_pi_apply (q, 1)).comp (measurable_auxiliary rate rewards C_star C_h control0))

/-- The actual archive observer equals the existing extended observer before
any first call, on the same original pair. -/
theorem prefixObservation_eq_extendedObservation (n : Fin (p.T + 1))
    (w : ReferenceExhaustiveGeneratedCalendarSourceLaw.Omega rate rewards C_star C_h)
    (hw : w ∈ beforeFirstCall rate rewards C_star C_h n) :
    prefixObservation rate rewards C_star C_h control0 n w =
      extendedObservation rate rewards C_star C_h control0 n
        (originalPair rate rewards C_star C_h control0 w) := by
  exact congrArg (fun H => (sourcePrefix control0 n.val (Z0 w),
    (ReferenceFirstLiveCalendarMarkedTransition.labelZero (auxiliary rate rewards C_star C_h control0 w), H)))
      (archiveBefore_eq_extendedPast rate rewards C_star C_h control0 n w hw)

/-- The no-call restriction is already decided by this actual before-draw observer. -/
theorem beforeFirstCall_eq_observation_preimage (n : Fin (p.T + 1)) :
    beforeFirstCall rate rewards C_star C_h n =
      prefixObservation rate rewards C_star C_h control0 n ⁻¹'
        {o | NoCallBefore rate rewards C_star C_h n o.1} := by
  ext w
  exact noCallBefore_sourcePrefix rate rewards C_star C_h control0 n (Z0 w)

/-- The graph's observer projection is the exact unnormalized killed law. -/
theorem terminalLaw_restrict_map_prefixObservation (n : Fin (p.T + 1)) :
    ((Lambda).restrict (beforeFirstCall rate rewards C_star C_h n)).map
      (prefixObservation rate rewards C_star C_h control0 n) = betaPre rate rewards C_star C_h control0 n := by
  calc
    _ = (((Lambda).restrict (beforeFirstCall rate rewards C_star C_h n)).map
        (originalArchiveGraph rate rewards C_star C_h control0 n)).map
          (observationProjection rate control0 n) :=
      (Measure.map_map (measurable_observationProjection rate control0 n)
        (measurable_originalArchiveGraph rate rewards C_star C_h control0 n)).symm
    _ = _ := by
      rw [terminalLaw_restrict_map_originalArchiveGraph,
        Measure.map_map (measurable_observationProjection rate control0 n)
          (measurable_extendedPastGraph rate rewards C_star C_h control0 n)]
      exact extendedObservation_map_restrict_eq_betaPre rate rewards C_star C_h control0 n

private theorem enlarged_restrict_innovation_product (q : Fin p.T) :
    (((mu).prod alpha).restrict {za | NoCallBefore rate rewards C_star C_h q.castSucc za.1}).map
      (fun za => (extendedObservation rate rewards C_star C_h control0 q.castSucc za,
        (ReferenceSourceCurrentControlFreshness.u_t p q za.1, za.2 (q, 1)))) =
      (betaPre rate rewards C_star C_h control0 q.castSucc).prod
        (ReferenceFirstLiveCalendarMarkedTransition.calendarInnovationLaw p) := by
  let f := extendedObservation rate rewards C_star C_h control0 q.castSucc
  let D : Set (Observation rate) := {o | NoCallBefore rate rewards C_star C_h q.castSucc o.1}
  let j := fun za : Source p × Auxiliary p =>
    (f za, (ReferenceSourceCurrentControlFreshness.u_t p q za.1, za.2 (q, 1)))
  have hf : Measurable f := measurable_extendedObservation rate rewards C_star C_h control0 q.castSucc
  have hj : Measurable j := hf.prodMk
    (((ReferenceSourceCurrentControlFreshness.measurable_u_t q).comp measurable_fst).prodMk
      ((measurable_pi_apply (q, 1)).comp measurable_snd))
  have hD : MeasurableSet D :=
    (measurableSet_noCallBefore rate rewards C_star C_h control0 q.castSucc).preimage measurable_fst
  have hE : f ⁻¹' D = {za | NoCallBefore rate rewards C_star C_h q.castSucc za.1} := by
    ext za
    exact (noCallBefore_sourcePrefix rate rewards C_star C_h control0 q.castSucc za.1).symm
  have hJ : j ⁻¹' (D ×ˢ Set.univ) = f ⁻¹' D := by
    rw [Set.prod_univ]
    rfl
  calc
    _ = (((mu).prod alpha).map j).restrict (D ×ˢ Set.univ) := by
      rw [Measure.restrict_map hj (hD.prod MeasurableSet.univ), hJ, hE]
    _ = ((((mu).prod alpha).map f).restrict D).prod
        (ReferenceFirstLiveCalendarMarkedTransition.calendarInnovationLaw p) := by
      have hp := extendedObservation_current_innovation_product rate rewards C_star C_h control0 q
      change ((mu).prod alpha).map j = (((mu).prod alpha).map f).prod
        (ReferenceFirstLiveCalendarMarkedTransition.calendarInnovationLaw p) at hp
      rw [hp, ← Measure.restrict_prod_eq_prod_univ]
    _ = _ := by
      have hb : (((mu).prod alpha).restrict {za | NoCallBefore rate rewards C_star C_h q.castSucc za.1}).map f =
          betaPre rate rewards C_star C_h control0 q.castSucc :=
        extendedObservation_map_restrict_eq_betaPre rate rewards C_star C_h control0 q.castSucc
      rw [Measure.restrict_map hf hD, hE, hb]

private def graphInnovationProjection (q : Fin p.T) (v : ReferenceInitialStoppedCalendar.Observer rate) :
    Observation rate × (ContinuousLearningRows.TimeControl p × ContinuousControlSlice.Scalar) :=
  (observationProjection rate control0 q.castSucc v,
    (ReferenceSourceCurrentControlFreshness.u_t p q v.1, v.2.1 (q, 1)))

private theorem measurable_graphInnovationProjection (q : Fin p.T) :
    Measurable (graphInnovationProjection rate control0 q) :=
  (measurable_observationProjection rate control0 q.castSucc).prodMk
    (((ReferenceSourceCurrentControlFreshness.measurable_u_t q).comp measurable_fst).prodMk
      ((measurable_pi_apply (q, 1)).comp measurable_snd.fst))

/-- On the genuine killed prefix, the ORIGINAL current physical control and
one residual scalar have their independent prescribed joint innovation law. -/
theorem terminalLaw_restrict_map_prefixObservation_innovation (q : Fin p.T) :
    ((Lambda).restrict (beforeFirstCall rate rewards C_star C_h q.castSucc)).map
      (fun w => (prefixObservation rate rewards C_star C_h control0 q.castSucc w,
        currentInnovation rate rewards C_star C_h control0 q w)) =
      (betaPre rate rewards C_star C_h control0 q.castSucc).prod
        (ReferenceFirstLiveCalendarMarkedTransition.calendarInnovationLaw p) := by
  calc
    _ = (((Lambda).restrict (beforeFirstCall rate rewards C_star C_h q.castSucc)).map
        (originalArchiveGraph rate rewards C_star C_h control0 q.castSucc)).map
          (graphInnovationProjection rate control0 q) :=
      (Measure.map_map (measurable_graphInnovationProjection rate control0 q)
        (measurable_originalArchiveGraph rate rewards C_star C_h control0 q.castSucc)).symm
    _ = _ := by
      rw [terminalLaw_restrict_map_originalArchiveGraph,
        Measure.map_map (measurable_graphInnovationProjection rate control0 q)
          (measurable_extendedPastGraph rate rewards C_star C_h control0 q.castSucc)]
      exact enlarged_restrict_innovation_product rate rewards C_star C_h control0 q

/-- Nonnegative tests of the actual observer and the original current innovation. -/
theorem terminalLaw_prefix_innovation_test (q : Fin p.T)
    (Phi : Observation rate × (ContinuousLearningRows.TimeControl p × ContinuousControlSlice.Scalar) → ℝ≥0∞)
    (hPhi : Measurable Phi) :
    (∫⁻ w, Phi (prefixObservation rate rewards C_star C_h control0 q.castSucc w,
      currentInnovation rate rewards C_star C_h control0 q w)
      ∂(Lambda).restrict (beforeFirstCall rate rewards C_star C_h q.castSucc)) =
      ∫⁻ v, Phi v ∂(betaPre rate rewards C_star C_h control0 q.castSucc).prod
        (ReferenceFirstLiveCalendarMarkedTransition.calendarInnovationLaw p) := by
  rw [← lintegral_map hPhi ((measurable_prefixObservation rate rewards C_star C_h control0 q.castSucc).prodMk
    (measurable_currentInnovation rate rewards C_star C_h control0 q)),
    terminalLaw_restrict_map_prefixObservation_innovation]

/-- Localization fixes exactly the original ID array, even after insertions. -/
theorem fixedIDTerminalLaw_eq_original_restrict (ids : CompletePublicTable.IDArray p) :
    ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDTerminalLaw rate rewards C_star C_h control0 ids =
      (CompletePublicTable.idArrayMeasure p {ids})⁻¹ •
        (Lambda).restrict (Z0 ⁻¹' ReferenceFixedIDSourceSection.fixedIDSourceSection ids) := by
  have hE : ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalSource rate rewards C_star C_h control0 ⁻¹'
        ReferenceFixedIDSourceSection.fixedIDSourceSection ids =
      Z0 ⁻¹' ReferenceFixedIDSourceSection.fixedIDSourceSection ids := by
    ext w
    exact ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDTerminalSource_iff_original
      rate rewards C_star C_h control0 ids w
  rw [ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDTerminalLaw_eq_restrict, hE]

private theorem idAtom_ne_zero (ids : CompletePublicTable.IDArray p) :
    CompletePublicTable.idArrayMeasure p {ids} ≠ 0 :=
  (ENNReal.toReal_pos_iff.mp (ReferenceFixedIDSourceSection.idArrayAtom_positive (p := p) ids)).1.ne'

/-- The fixed-ID joint law is derived by normalizing only its positive original
ID atom. The original private arrays, original selecting scalar, and full tape remain. -/
theorem fixedIDTerminalLaw_map_originalPair (ids : CompletePublicTable.IDArray p) :
    (ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDTerminalLaw rate rewards C_star C_h control0 ids).map
      (originalPair rate rewards C_star C_h control0) =
      (ReferenceFixedIDSourceSection.fixedIDSourceLaw ids).prod alpha := by
  let D : Set (Source p × Auxiliary p) :=
    {za | za.1 ∈ ReferenceFixedIDSourceSection.fixedIDSourceSection ids}
  have hD : MeasurableSet D :=
    (ReferenceFixedIDSourceSection.measurable_fixedIDSourceSection ids).preimage measurable_fst
  rw [fixedIDTerminalLaw_eq_original_restrict,
    Measure.map_smul _ (measurable_originalPair rate rewards C_star C_h control0).aemeasurable]
  change (CompletePublicTable.idArrayMeasure p {ids})⁻¹ •
    (((Lambda).restrict ((originalPair rate rewards C_star C_h control0) ⁻¹' D)).map
      (originalPair rate rewards C_star C_h control0)) = _
  rw [← Measure.restrict_map (measurable_originalPair rate rewards C_star C_h control0) hD,
    terminalLaw_map_originalPair]
  have hrect : D = ReferenceFixedIDSourceSection.fixedIDSourceSection ids ×ˢ (Set.univ : Set (Auxiliary p)) :=
    Set.prod_univ.symm
  rw [hrect, ← Measure.restrict_prod_eq_prod_univ,
    ReferenceFixedIDSourceSection.sourceInputLaw_restrict_fixedIDSourceSection,
    Measure.prod_smul_left, smul_smul,
    ENNReal.inv_mul_cancel (idAtom_ne_zero ids)
      (ReferenceFixedIDSourceSection.idArrayAtom_lt_top (p := p) ids).ne, one_smul]

/-- The same original-source restriction remains unnormalized after fixing IDs. -/
theorem fixedIDTerminalLaw_restrict_map_originalPair (ids : CompletePublicTable.IDArray p)
    (n : Fin (p.T + 1)) :
    ((ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDTerminalLaw rate rewards C_star C_h control0 ids).restrict
      (beforeFirstCall rate rewards C_star C_h n)).map (originalPair rate rewards C_star C_h control0) =
      ((ReferenceFixedIDSourceSection.fixedIDSourceLaw ids).prod alpha).restrict
        {za | NoCallBefore rate rewards C_star C_h n za.1} := by
  rw [← fixedIDTerminalLaw_map_originalPair rate rewards C_star C_h control0 ids]
  exact (Measure.restrict_map
    (μ := ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDTerminalLaw rate rewards C_star C_h control0 ids)
    (measurable_originalPair rate rewards C_star C_h control0)
    (s := {za : Source p × Auxiliary p | NoCallBefore rate rewards C_star C_h n za.1})
    ((measurableSet_noCallBefore rate rewards C_star C_h control0 n).preimage measurable_fst)).symm

/-- Full fixed-original-ID archive graph, derived from the genuine raw law. -/
theorem fixedIDTerminalLaw_restrict_map_originalArchiveGraph (ids : CompletePublicTable.IDArray p)
    (n : Fin (p.T + 1)) :
    ((ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDTerminalLaw rate rewards C_star C_h control0 ids).restrict
      (beforeFirstCall rate rewards C_star C_h n)).map (originalArchiveGraph rate rewards C_star C_h control0 n) =
      (((ReferenceFixedIDSourceSection.fixedIDSourceLaw ids).prod alpha).restrict
        {za | NoCallBefore rate rewards C_star C_h n za.1}).map (extendedPastGraph rate rewards C_star C_h n) := by
  calc
    _ = ((ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDTerminalLaw rate rewards C_star C_h control0 ids).restrict
        (beforeFirstCall rate rewards C_star C_h n)).map
        ((extendedPastGraph rate rewards C_star C_h n) ∘ originalPair rate rewards C_star C_h control0) := by
      apply Measure.map_congr
      filter_upwards [ae_restrict_mem (measurableSet_beforeFirstCall rate rewards C_star C_h control0 n)] with w hw
      exact congrArg (fun L => (Z0 w, (auxiliary rate rewards C_star C_h control0 w, L)))
        (archiveBefore_eq_extendedPast rate rewards C_star C_h control0 n w hw)
    _ = _ := by
      rw [← Measure.map_map (measurable_extendedPastGraph rate rewards C_star C_h control0 n)
        (measurable_originalPair rate rewards C_star C_h control0), fixedIDTerminalLaw_restrict_map_originalPair]

/-- The killed observer law localized at the original positive ID atom. No
call/no-call component, date, or future tag contributes a normalization factor. -/
def fixedIDBetaPre (ids : CompletePublicTable.IDArray p) (n : Fin (p.T + 1)) : Measure (Observation rate) :=
  (CompletePublicTable.idArrayMeasure p {ids})⁻¹ •
    (betaPre rate rewards C_star C_h control0 n).restrict
      {o | o.1 ∈ ReferenceFixedIDSourceSection.fixedIDSourceSection ids}

private theorem fixedIDTerminalLaw_restrict_eq (ids : CompletePublicTable.IDArray p) (n : Fin (p.T + 1)) :
    (ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDTerminalLaw rate rewards C_star C_h control0 ids).restrict
      (beforeFirstCall rate rewards C_star C_h n) =
      (CompletePublicTable.idArrayMeasure p {ids})⁻¹ •
        ((Lambda).restrict (beforeFirstCall rate rewards C_star C_h n)).restrict
          (Z0 ⁻¹' ReferenceFixedIDSourceSection.fixedIDSourceSection ids) := by
  rw [fixedIDTerminalLaw_eq_original_restrict, Measure.restrict_smul,
    Measure.restrict_comm (measurableSet_beforeFirstCall rate rewards C_star C_h control0 n)]

/-- Exact killed-beta projection on the original-fixed-ID raw calendar. -/
theorem fixedIDTerminalLaw_restrict_map_prefixObservation (ids : CompletePublicTable.IDArray p)
    (n : Fin (p.T + 1)) :
    ((ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDTerminalLaw rate rewards C_star C_h control0 ids).restrict
      (beforeFirstCall rate rewards C_star C_h n)).map (prefixObservation rate rewards C_star C_h control0 n) =
      fixedIDBetaPre rate rewards C_star C_h control0 ids n := by
  let D : Set (Observation rate) := {o | o.1 ∈ ReferenceFixedIDSourceSection.fixedIDSourceSection ids}
  have hD : MeasurableSet D :=
    (ReferenceFixedIDSourceSection.measurable_fixedIDSourceSection ids).preimage measurable_fst
  rw [fixedIDTerminalLaw_restrict_eq,
    Measure.map_smul _ (measurable_prefixObservation rate rewards C_star C_h control0 n).aemeasurable]
  change (CompletePublicTable.idArrayMeasure p {ids})⁻¹ •
    ((((Lambda).restrict (beforeFirstCall rate rewards C_star C_h n)).restrict
      (prefixObservation rate rewards C_star C_h control0 n ⁻¹' D)).map
        (prefixObservation rate rewards C_star C_h control0 n)) = _
  rw [← Measure.restrict_map (measurable_prefixObservation rate rewards C_star C_h control0 n) hD,
    terminalLaw_restrict_map_prefixObservation]
  rfl

/-- Fixing original IDs preserves the joint current-control/ONE-scalar law;
the no-call prefix stays killed and unnormalized. -/
theorem fixedIDTerminalLaw_restrict_map_prefixObservation_innovation (ids : CompletePublicTable.IDArray p)
    (q : Fin p.T) :
    ((ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDTerminalLaw rate rewards C_star C_h control0 ids).restrict
      (beforeFirstCall rate rewards C_star C_h q.castSucc)).map
      (fun w => (prefixObservation rate rewards C_star C_h control0 q.castSucc w,
        currentInnovation rate rewards C_star C_h control0 q w)) =
      (fixedIDBetaPre rate rewards C_star C_h control0 ids q.castSucc).prod
        (ReferenceFirstLiveCalendarMarkedTransition.calendarInnovationLaw p) := by
  have : IsFiniteMeasure (betaPre rate rewards C_star C_h control0 q.castSucc) :=
    ⟨(betaPre_mass_le_one rate rewards C_star C_h control0 q.castSucc).trans_lt ENNReal.one_lt_top⟩
  let D : Set (Observation rate) := {o | o.1 ∈ ReferenceFixedIDSourceSection.fixedIDSourceSection ids}
  let g := fun w => (prefixObservation rate rewards C_star C_h control0 q.castSucc w,
    currentInnovation rate rewards C_star C_h control0 q w)
  have hD : MeasurableSet D :=
    (ReferenceFixedIDSourceSection.measurable_fixedIDSourceSection ids).preimage measurable_fst
  have hg : Measurable g := (measurable_prefixObservation rate rewards C_star C_h control0 q.castSucc).prodMk
    (measurable_currentInnovation rate rewards C_star C_h control0 q)
  have hG : g ⁻¹' (D ×ˢ Set.univ) = Z0 ⁻¹' ReferenceFixedIDSourceSection.fixedIDSourceSection ids := by
    rw [Set.prod_univ]
    rfl
  rw [fixedIDTerminalLaw_restrict_eq, Measure.map_smul _ hg.aemeasurable,
    ← hG, ← Measure.restrict_map hg (hD.prod MeasurableSet.univ)]
  have hprod := terminalLaw_restrict_map_prefixObservation_innovation rate rewards C_star C_h control0 q
  change (((Lambda).restrict (beforeFirstCall rate rewards C_star C_h q.castSucc)).map g) = _ at hprod
  rw [hprod, ← Measure.restrict_prod_eq_prod_univ, ← Measure.prod_smul_left]
  rfl

/-- Arbitrary full-tape/archive Borel tests after original-ID localization. -/
theorem fixedIDTerminalLaw_archive_joint_test (ids : CompletePublicTable.IDArray p) (n : Fin (p.T + 1))
    (Phi : ReferenceInitialStoppedCalendar.Observer rate → ℝ≥0∞) (hPhi : Measurable Phi) :
    (∫⁻ w, Phi (originalArchiveGraph rate rewards C_star C_h control0 n w)
      ∂(ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDTerminalLaw rate rewards C_star C_h control0 ids).restrict
        (beforeFirstCall rate rewards C_star C_h n)) =
      ∫⁻ za, Phi (extendedPastGraph rate rewards C_star C_h n za)
        ∂((ReferenceFixedIDSourceSection.fixedIDSourceLaw ids).prod alpha).restrict
          {za | NoCallBefore rate rewards C_star C_h n za.1} := by
  rw [← lintegral_map hPhi (measurable_originalArchiveGraph rate rewards C_star C_h control0 n),
    fixedIDTerminalLaw_restrict_map_originalArchiveGraph,
    lintegral_map hPhi (measurable_extendedPastGraph rate rewards C_star C_h control0 n)]

/-- Borel observer/innovation tests on the same original-fixed-ID experiment. -/
theorem fixedIDTerminalLaw_prefix_innovation_test (ids : CompletePublicTable.IDArray p) (q : Fin p.T)
    (Phi : Observation rate × (ContinuousLearningRows.TimeControl p × ContinuousControlSlice.Scalar) → ℝ≥0∞)
    (hPhi : Measurable Phi) :
    (∫⁻ w, Phi (prefixObservation rate rewards C_star C_h control0 q.castSucc w,
      currentInnovation rate rewards C_star C_h control0 q w)
      ∂(ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDTerminalLaw rate rewards C_star C_h control0 ids).restrict
        (beforeFirstCall rate rewards C_star C_h q.castSucc)) =
      ∫⁻ v, Phi v ∂(fixedIDBetaPre rate rewards C_star C_h control0 ids q.castSucc).prod
        (ReferenceFirstLiveCalendarMarkedTransition.calendarInnovationLaw p) := by
  rw [← lintegral_map hPhi ((measurable_prefixObservation rate rewards C_star C_h control0 q.castSucc).prodMk
    (measurable_currentInnovation rate rewards C_star C_h control0 q)),
    fixedIDTerminalLaw_restrict_map_prefixObservation_innovation]

end Bandits.Support.ReferenceGeneratedCalendarEpisodePrefixRecombination
