/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedCalendarEpisodePrefixRecombination
public import Bandits.Support.ReferenceGeneratedCalendarRoundLaw

import Mathlib.Tactic

/-!
# Initial slow-set draw at the actual finite launch

Sources: ZIP4 `04_slow_fast_learner.tex:176-215,323-390`,
`06_interruptions.tex:391-426`, and `08_main_theorem.tex:78-109`.

The launch is read from the same exhaustive terminal source. Its actual
archived birth cell has zero numerical PRE and empty strict history. Future
first-call, no-call and stopped tags are recombined before evaluating laws.
These are internal initialization results, not manuscript closure.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal Classical
open Bandits.Support ConstructorDimensions
open ReferenceFirstLiveChronologicalPrefixFoundation
open ReferenceSourcePrefixHistoryFiltration (sourcePrefix)

namespace Bandits.Support.ReferenceGeneratedCalendarLaunchSlowInitialization

variable {p : ConstructorDimensions.Parameters}

local instance sourceMeasurableSpace :
    MeasurableSpace (BootstrapPrivateRoundStreams.SourceInput p) := by
  change MeasurableSpace (CompletePublicTable.PublishedOutput p ×
    BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

local instance slowSetMeasurableSpace : MeasurableSpace (SlowSet p) := ⊤

local instance slowSetDiscrete : DiscreteMeasurableSpace (SlowSet p) := ⟨fun _ => trivial⟩

variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
  (control0 : ContinuousLearningRows.TimeControl p)

local notation "Source" => BootstrapPrivateRoundStreams.SourceInput p
local notation "Auxiliary" => ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p
local notation "Omega" => ReferenceExhaustiveGeneratedCalendarSourceLaw.Omega rate rewards C_star C_h
local notation "Z" => ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalSource rate rewards C_star C_h control0
local notation "archive " w:max =>
  Prod.snd (Prod.snd (ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalReadout
    rate rewards C_star C_h control0 w))
local notation "past" => ReferenceFirstCollectionLogicalPrefixExtension.extendedPast rate rewards C_star C_h
local notation "start " z:max => ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
local notation "launch" => ReferenceGeneratedDownAmbiguityMeasurability.generatedLaunchFiberSet
  (rate := rate) rewards C_star C_h
local notation "live" => firstLiveChronologicalPrefix rate rewards C_star C_h
local notation "Q" => ReferenceFirstLaunchNumericalCell.queueParameters rate
local notation "draw" => CanonicalAssignmentVector.canonicalSlowSampler p.two_le_m p.m_lt_K
  (fun _ => 1) (fun _ => 1) (by intro _; norm_num) (by intro _; norm_num)
local notation "vector " c:max =>
  ContinuousControlSlice.assignmentVector (Prod.fst c)
local notation "current" => ReferenceSourceCurrentControlFreshness.u_t p

omit control0 in
private def birthSource (s : Fin p.T) (z : Source) (hz : z ∈ launch s.val) :
    ReferenceFirstLiveBirthChronologicalReadout.SourceStratum rate rewards C_star C_h
      (ActualInitializationPhysicalStep.selectedRowIndex p z) s :=
  ⟨z, rfl, hz.1, hz.2⟩

include control0 in
private theorem launch_prefix (s : Fin p.T) (z : Source) (hz : z ∈ launch s.val)
    (a : Auxiliary) :
    ∃ e : LogicalCell p rate, past s.succ (z, a) = [e] ∧
      e.time = s ∧ e.before = RecordedQueueRun.initialState p.K ∧
      e.slowSet = draw (vector (current s z)) := by
  let z0 := birthSource rate rewards C_star C_h s z hz
  have hpos := ReferenceFirstLiveBirthChronologicalReadout.actual_birth_chronological_prefix_positive
    rate rewards C_star C_h _ s z0
  have hread := ReferenceFirstLiveBirthChronologicalReadout.actual_birth_chronological_entry_readout
    rate rewards C_star C_h _ s control0 z0 a
  let e := (live (z, a))[0]'(by rw [firstLiveChronologicalPrefix_length]; exact hpos)
  have hcol : s.val + 1 ≤ ReferenceFirstCollectionLogicalPrefixExtension.collectionStart
      rate rewards C_star C_h z := by
    change s.val + 1 ≤ start z + ReferenceFirstLiveOverflowReadout.wholeFirstLiveLength
      rate rewards C_star C_h z
    change 0 < (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow rate rewards C_star C_h z).length at hpos
    rw [hz.2]
    unfold ReferenceFirstLiveOverflowReadout.wholeFirstLiveLength
    omega
  have hp := ReferenceFirstCollectionLogicalPrefixExtension.extendedPrefixStateAux_before_collectionStart
    rate rewards C_star C_h (s.val + 1) (by have := s.isLt; omega) z a hcol
  have hpast : past s.succ (z, a) = [e] := by
    change (ReferenceFirstCollectionLogicalPrefixExtension.extendedPrefixStateAux
      rate rewards C_star C_h (s.val + 1) _ (z, a)).2 = _
    rw [hp, ReferenceFirstLiveChronologicalPrefixCausality.calendarPast_eq_take_elapsed, hz.2]
    have he : 0 < (live (z, a)).length := by rw [firstLiveChronologicalPrefix_length]; exact hpos
    simp only [Nat.add_sub_cancel_left]
    cases hl : live (z, a) with
    | nil => simp only [hl, List.length_nil, Nat.lt_irrefl] at he
    | cons c cs => simp only [e, hl, List.take_succ_cons, List.take_zero, List.getElem_cons_zero]
  refine ⟨e, hpast, hread.1, hread.2.2.2.1, ?_⟩
  have hs := hread.2.2.2.2.2.2.2.1
  exact hs.trans (ReferenceFirstLaunchOriginalAuxiliaryReward.actualFirstSlowSet_eq_canonical
    rate rewards C_star C_h _ s control0 z0)

omit control0 in
private theorem launch_past_empty (s : Fin p.T) (z : Source) (hz : z ∈ launch s.val)
    (a : Auxiliary) : past s.castSucc (z, a) = [] := by
  have hp := ReferenceFirstCollectionLogicalPrefixExtension.extendedPrefixStateAux_before_collectionStart
    rate rewards C_star C_h s.val s.isLt.le z a (by
      change s.val ≤ start z + _
      rw [hz.2]
      omega)
  simpa only [ReferenceFirstCollectionLogicalPrefixExtension.extendedPast,
    Fin.val_castSucc, ReferenceFirstLiveChronologicalPrefixCausality.calendarPast_eq_take_elapsed,
    hz.2, Nat.sub_self, List.take_zero] using hp

private theorem launch_head_mem_past (s : Fin p.T) (z : Source)
    (a : Auxiliary) (n : Fin (p.T + 1)) (hsn : s.val < n.val)
    (e : LogicalCell p rate) (he : past s.succ (z, a) = [e]) : e ∈ past n (z, a) := by
  have hp := ReferenceFirstCollectionLogicalPrefixExtension.extendedPrefixStateAux_prefix
    rate rewards C_star C_h n.val (Nat.le_of_lt_succ n.isLt) (s.val + 1) hsn (z, a)
  change past s.succ (z, a) <+: past n (z, a) at hp
  rw [he] at hp
  exact hp.subset (List.mem_singleton_self e)

private theorem terminal_contains_launch_prefix (s : Fin p.T) (w : Omega)
    (hz : Z w ∈ launch s.val) (e : LogicalCell p rate)
    (he : past s.succ (Z w,
      ReferenceGeneratedCalendarEpisodePrefixRecombination.auxiliary rate rewards C_star C_h control0 w) = [e]) :
    e ∈ archive w := by
  rcases w with ⟨i, w⟩
  cases i with
  | noCall =>
    exact launch_head_mem_past rate rewards C_star C_h s _ w.2 (Fin.last p.T) s.isLt e he
  | stopped u t =>
    have hd := ReferenceFirstCollectionLogicalNumericalAlignment.firstCall_dates
      rate rewards C_star C_h u t w.1.val w.1.property.1.1
    have hst : s.val < t.val := by
      have hstart : start w.1.val = s.val := hz.2
      rw [hstart] at hd
      omega
    have hm := launch_head_mem_past rate rewards C_star C_h s w.1.val w.2 t.castSucc hst e he
    exact (ReferenceInitialStoppedCalendar.initialStoppedPast_retains_prefix rate rewards C_star C_h
      control0 u t (Fin.last p.T) t.isLt.le w).subset hm
  | generated b u t =>
    let z := Z ⟨.generated b u t, w⟩
    let a := (ReferenceGeneratedRankCalendarFoundation.calendarOriginalLift rate rewards C_star C_h
      b u t (p.T - (t.val + 1)) w).1.2
    have hf := ReferenceGeneratedCalendarLivePayoff.calendarCurrentSource_firstCell
      rate rewards C_star C_h control0 b u t _ (by omega) w
    have hd := ReferenceFirstCollectionLogicalNumericalAlignment.firstCall_dates
      rate rewards C_star C_h u t z hf
    have hst : s.val < t.val := by
      have hstart : start z = s.val := hz.2
      rw [hstart] at hd
      omega
    have hm := launch_head_mem_past rate rewards C_star C_h s z a t.castSucc hst e he
    exact (ReferenceGeneratedCalendarMarkedPath.calendar_archived_full_root_past rate rewards C_star C_h
      control0 b u t _ (by omega) w).subset hm

/-- The actual finite launch has one present enabled birth mark. Its strict
archive is empty, its PRE is the genuine zero state, and its slow set is the
canonical image of the original selected-row whole assignment vector on the
same terminal source. This covers every exhaustive component pointwise. -/
theorem terminal_launch_initialization (s : Fin p.T) (w : Omega)
    (hz : Z w ∈ launch s.val) :
    ReferenceGeneratedCalendarEpisodePrefixRecombination.archiveBefore
      rate rewards C_star C_h control0 s.castSucc w = [] ∧
    ∃! e : LogicalCell p rate, e ∈ archive w ∧ e.time = s ∧
      e.numerical.1 = true ∧ e.before = RecordedQueueRun.initialState p.K ∧
      e.slowSet = draw (vector (current s (Z w))) := by
  obtain ⟨e, hpast, ht, hb, hslow⟩ := launch_prefix rate rewards C_star C_h control0 s (Z w) hz
    (ReferenceGeneratedCalendarEpisodePrefixRecombination.auxiliary rate rewards C_star C_h control0 w)
  have hm := terminal_contains_launch_prefix rate rewards C_star C_h control0 s w hz e hpast
  have hen := (ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalReadout_enabled_iff
    rate rewards C_star C_h control0 w s).mp ⟨e, hm, ht⟩
  obtain ⟨d, _hd, huniq⟩ :=
    (ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalReadout_unique_enabled
      rate rewards C_star C_h control0 w s).mpr hen
  have hnum : e.numerical.1 = true :=
    ReferenceGeneratedCalendarMarkedPath.firstPast_enabled rate rewards C_star C_h _ _ s.succ e
      (by rw [hpast]; exact List.mem_singleton_self _)
  constructor
  · apply List.filter_eq_nil_iff.mpr
    intro f hf
    simp only [decide_eq_true_eq, Fin.val_castSucc]
    intro hlt
    have hfen := (ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalReadout_enabled_iff
      rate rewards C_star C_h control0 w f.time).mp ⟨f, hf, rfl⟩
    have hbefore : f.time.val < start (Z w) := by rw [hz.2]; exact hlt
    simp only [ReferenceExhaustiveGeneratedCalendarSourceLaw.nominalEnabled,
      ReferenceSourcePrefixHistoryFiltration.actualRecord_eq_none_of_future_start
        rate rewards C_star C_h f.time (Z w) hbefore,
      Option.bind_none, Option.any_none, Bool.false_eq_true] at hfen
  · refine ⟨e, ⟨hm, ht, hnum, hb, hslow⟩, ?_⟩
    intro f hf
    exact (huniq f ⟨hf.1, hf.2.1⟩).trans (huniq e ⟨hm, ht⟩).symm

/-- Clear numerical PRE at launch is produced from the actual complete word;
no supplied trace, clear-state premise, or sampler-success hypothesis occurs. -/
theorem terminal_launch_numerical (s : Fin p.T) (w : Omega)
    (hz : Z w ∈ launch s.val) :
    ReferencePostInvocationNoncallGeometry.prefixNumerical rate rewards C_star C_h s.castSucc (Z w) =
      some (RecordedQueueRun.initialState p.K) ∧
    (∀ i, RecordedQueueRun.scoreWeight Q (RecordedQueueRun.initialState p.K) i = 1) ∧
    (RecordedQueueRun.initialState p.K).overflow = false := by
  have hl : ∃ active, ReferenceCorrectedInitializationLaunch.correctedLaunch rate (Z w) rewards C_star C_h = some active :=
    ⟨_, ReferenceLocalReleaseGateChronology.sourceSeed_launch rate (Z w) rewards C_star C_h hz.1⟩
  have hp := ReferencePostInvocationNoncallGeometry.prefixNumerical_actualWord
    rate rewards C_star C_h s.castSucc (Z w) hl (by rw [hz.2]; exact le_rfl)
  refine ⟨?_, ?_, rfl⟩
  · simpa only [Fin.val_castSucc, hz.2, Nat.sub_self, List.take_zero,
      RecordedQueueRun.run, RecordedQueueRun.execute] using hp
  · intro i
    simp only [RecordedQueueRun.scoreWeight, RecordedQueueRun.initialState,
      ScoreWeights.scoreWeight, pow_zero]

omit rewards C_star C_h control0 in
private theorem initialPMF_eq_unit :
    RecordedSlowRefresh.recordedSlowPMF p Q (RecordedQueueRun.initialState p.K)
      (RecordedQueueRun.scoreWeight Q (RecordedQueueRun.initialState p.K))
      (RecordedSlowRefresh.scoreWeight_pos Q (RecordedQueueRun.initialState p.K)) =
      CanonicalOrientedSetLaw.slowSetPMF (fun _ => 1) (fun _ => 1)
        p.two_le_m p.m_lt_K (by intro _; norm_num) (by intro _; norm_num) := by
  have hw : RecordedQueueRun.scoreWeight Q (RecordedQueueRun.initialState p.K) = fun _ => 1 := by
    funext i
    simp only [RecordedQueueRun.scoreWeight, RecordedQueueRun.initialState,
      ScoreWeights.scoreWeight, pow_zero]
  unfold RecordedSlowRefresh.recordedSlowPMF
  simp only [hw]

omit rate rewards C_star C_h control0 in
private theorem measurable_control_draw :
    Measurable (fun c : ContinuousLearningRows.TimeControl p => draw (vector c)) :=
  (CanonicalAssignmentVector.measurable_canonicalSlowSampler p.two_le_m p.m_lt_K
    (fun _ => 1) (fun _ => 1) (by intro _; norm_num) (by intro _; norm_num)).comp
    ((ContinuousControlSlice.measurable_assignmentVector p.m p.K).comp measurable_fst)

omit rewards C_star C_h control0 in
private theorem control_draw_law :
    (ContinuousLearningRows.timeControlLaw p).map
      (fun c : ContinuousLearningRows.TimeControl p => draw (vector c)) =
      (RecordedSlowRefresh.recordedSlowPMF p Q (RecordedQueueRun.initialState p.K)
        (RecordedQueueRun.scoreWeight Q (RecordedQueueRun.initialState p.K))
        (RecordedSlowRefresh.scoreWeight_pos Q (RecordedQueueRun.initialState p.K))).toMeasure := by
  rw [initialPMF_eq_unit]
  change (ContinuousLearningRows.timeControlLaw p).map
    (draw ∘ ContinuousControlSlice.assignmentVector ∘ Prod.fst) = _
  rw [← Measure.map_map (CanonicalAssignmentVector.measurable_canonicalSlowSampler
    p.two_le_m p.m_lt_K (fun _ => 1) (fun _ => 1) (by intro _; norm_num) (by intro _; norm_num))
    ((ContinuousControlSlice.measurable_assignmentVector p.m p.K).comp measurable_fst)]
  rw [← Measure.map_map (ContinuousControlSlice.measurable_assignmentVector p.m p.K) measurable_fst]
  rw [ContinuousLearningRows.timeControlLaw, (measurePreserving_fst
    (μ := ContinuousControlSlice.sliceLaw p.m p.K)
    (ν := ContinuousLearningRows.affineSamplesLaw p)).map_eq,
    ContinuousControlSlice.map_assignmentVector]
  exact CanonicalAssignmentVector.assignmentLaw_map_canonicalSlowSampler
    p.two_le_m p.m_lt_K (fun _ => 1) (fun _ => 1) (by intro _; norm_num) (by intro _; norm_num)

omit rate rewards C_star C_h control0 in
private theorem fixedIDSourceLaw_eq_normalized_restrict (ids : CompletePublicTable.IDArray p) :
    ReferenceFixedIDSourceSection.fixedIDSourceLaw ids =
      (CompletePublicTable.idArrayMeasure p {ids})⁻¹ •
        (BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
          (ReferenceFixedIDSourceSection.fixedIDSourceSection ids) := by
  rw [ReferenceFixedIDSourceSection.sourceInputLaw_restrict_fixedIDSourceSection,
    smul_smul, ENNReal.inv_mul_cancel
      (ENNReal.toReal_pos_iff.mp (ReferenceFixedIDSourceSection.idArrayAtom_positive (p := p) ids)).1.ne'
      (ReferenceFixedIDSourceSection.idArrayAtom_lt_top (p := p) ids).ne, one_smul]

omit rate rewards C_star C_h in
private theorem fixedID_prefix_control_product (ids : CompletePublicTable.IDArray p) (s : Fin p.T) :
    (ReferenceFixedIDSourceSection.fixedIDSourceLaw ids).map
      (fun z => (sourcePrefix control0 s.val z, current s z)) =
      ((ReferenceFixedIDSourceSection.fixedIDSourceLaw ids).map (sourcePrefix control0 s.val)).prod
        (ContinuousLearningRows.timeControlLaw p) := by
  let D := ReferenceFixedIDSourceSection.fixedIDSourceSection (p := p) ids
  let E : Set (Source × ContinuousLearningRows.TimeControl p) := D ×ˢ Set.univ
  have hD : MeasurableSet D := ReferenceFixedIDSourceSection.measurable_fixedIDSourceSection ids
  have hE : MeasurableSet E := hD.prod MeasurableSet.univ
  have hpair := (ReferenceSourcePrefixHistoryFiltration.measurable_sourcePrefix control0 s.val).prodMk
    (ReferenceSourceCurrentControlFreshness.measurable_u_t s)
  have he : (fun z => (sourcePrefix control0 s.val z, current s z)) ⁻¹' E = D := by
    ext z
    simp only [E, D, Set.mem_preimage, Set.mem_prod, Set.mem_univ, and_true,
      ReferenceFixedIDSourceSection.fixedIDSourceSection, Set.mem_ofPred_eq,
      ReferenceSourcePrefixHistoryFiltration.sourcePrefix_ids]
  have hd : sourcePrefix control0 s.val ⁻¹' D = D := by
    ext z
    exact Iff.rfl
  let mu := BootstrapPrivateRoundStreams.sourceInputLaw p
  let c := (CompletePublicTable.idArrayMeasure p {ids})⁻¹
  calc
    _ = c • (mu.restrict D).map (fun z => (sourcePrefix control0 s.val z, current s z)) := by
      rw [fixedIDSourceLaw_eq_normalized_restrict, Measure.map_smul _ hpair.aemeasurable]
    _ = c • ((mu.map (fun z => (sourcePrefix control0 s.val z, current s z))).restrict E) := by
      rw [Measure.restrict_map hpair hE, he]
    _ = (c • ((mu.map (sourcePrefix control0 s.val)).restrict D)).prod
        (ContinuousLearningRows.timeControlLaw p) := by
      rw [ReferenceFirstLiveCalendarMarkedTransition.sourcePrefix_currentControl_product,
        show E = D ×ˢ Set.univ from rfl, ← Measure.restrict_prod_eq_prod_univ,
        Measure.prod_smul_left]
    _ = _ := by
      rw [Measure.restrict_map (ReferenceSourcePrefixHistoryFiltration.measurable_sourcePrefix control0 s.val) hD,
        hd, ← Measure.map_smul _ (ReferenceSourcePrefixHistoryFiltration.measurable_sourcePrefix control0 s.val).aemeasurable]
      rw [fixedIDSourceLaw_eq_normalized_restrict]

omit rewards C_star C_h in
private theorem source_prefix_slow_product (ids : Option (CompletePublicTable.IDArray p)) (s : Fin p.T) :
    (ids.elim (BootstrapPrivateRoundStreams.sourceInputLaw p)
      ReferenceFixedIDSourceSection.fixedIDSourceLaw).map
      (fun z => (sourcePrefix control0 s.val z, draw (vector (current s z)))) =
      ((ids.elim (BootstrapPrivateRoundStreams.sourceInputLaw p)
        ReferenceFixedIDSourceSection.fixedIDSourceLaw).map (sourcePrefix control0 s.val)).prod
      (RecordedSlowRefresh.recordedSlowPMF p Q (RecordedQueueRun.initialState p.K)
        (RecordedQueueRun.scoreWeight Q (RecordedQueueRun.initialState p.K))
        (RecordedSlowRefresh.scoreWeight_pos Q (RecordedQueueRun.initialState p.K))).toMeasure := by
  have hsource : (ids.elim (BootstrapPrivateRoundStreams.sourceInputLaw p)
      ReferenceFixedIDSourceSection.fixedIDSourceLaw).map
      (fun z => (sourcePrefix control0 s.val z, current s z)) =
      ((ids.elim (BootstrapPrivateRoundStreams.sourceInputLaw p)
        ReferenceFixedIDSourceSection.fixedIDSourceLaw).map (sourcePrefix control0 s.val)).prod
        (ContinuousLearningRows.timeControlLaw p) := by
    cases ids with
    | none => exact ReferenceFirstLiveCalendarMarkedTransition.sourcePrefix_currentControl_product control0 s
    | some ids => exact fixedID_prefix_control_product control0 ids s
  let mu := ids.elim (BootstrapPrivateRoundStreams.sourceInputLaw p)
    ReferenceFixedIDSourceSection.fixedIDSourceLaw
  let g := fun c : ContinuousLearningRows.TimeControl p => draw (vector c)
  calc
    _ = (mu.map (fun z => (sourcePrefix control0 s.val z, current s z))).map (Prod.map id g) := by
      rw [Measure.map_map (measurable_id.prodMap measurable_control_draw)
        ((ReferenceSourcePrefixHistoryFiltration.measurable_sourcePrefix control0 s.val).prodMk
          (ReferenceSourceCurrentControlFreshness.measurable_u_t s))]
      rfl
    _ = ((mu.map (sourcePrefix control0 s.val)).prod (ContinuousLearningRows.timeControlLaw p)).map
        (Prod.map id g) := by rw [hsource]
    _ = (mu.map (sourcePrefix control0 s.val)).prod
        ((ContinuousLearningRows.timeControlLaw p).map g) := by
      rw [← Measure.map_prod_map _ _ measurable_id measurable_control_draw, Measure.map_id]
    _ = _ := by rw [control_draw_law rate]

omit rewards C_star C_h in
private theorem source_prefix_slow_cylinder (ids : Option (CompletePublicTable.IDArray p))
    (s : Fin p.T) (U : SlowSet p) (F : Source → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ z, F (sourcePrefix control0 s.val z) *
      (if draw (vector (current s z)) = U then 1 else 0)
      ∂ids.elim (BootstrapPrivateRoundStreams.sourceInputLaw p)
        ReferenceFixedIDSourceSection.fixedIDSourceLaw) =
    ∫⁻ z, F (sourcePrefix control0 s.val z) *
      RecordedSlowRefresh.recordedSlowPMF p Q (RecordedQueueRun.initialState p.K)
        (RecordedQueueRun.scoreWeight Q (RecordedQueueRun.initialState p.K))
        (RecordedSlowRefresh.scoreWeight_pos Q (RecordedQueueRun.initialState p.K)) U
      ∂ids.elim (BootstrapPrivateRoundStreams.sourceInputLaw p)
        ReferenceFixedIDSourceSection.fixedIDSourceLaw := by
  let mu := ids.elim (BootstrapPrivateRoundStreams.sourceInputLaw p)
    ReferenceFixedIDSourceSection.fixedIDSourceLaw
  let P := RecordedSlowRefresh.recordedSlowPMF p Q (RecordedQueueRun.initialState p.K)
    (RecordedQueueRun.scoreWeight Q (RecordedQueueRun.initialState p.K))
    (RecordedSlowRefresh.scoreWeight_pos Q (RecordedQueueRun.initialState p.K))
  let I : SlowSet p → ℝ≥0∞ := fun V => if V = U then 1 else 0
  have hI : Measurable I := measurable_const.ite
    (measurableSet_eq_fun measurable_id measurable_const) measurable_const
  have htest : Measurable (fun x : Source × SlowSet p => F x.1 * I x.2) :=
    (hF.comp measurable_fst).mul (hI.comp measurable_snd)
  have hpair : Measurable (fun z : Source =>
      (sourcePrefix control0 s.val z, draw (vector (current s z)))) :=
    (ReferenceSourcePrefixHistoryFiltration.measurable_sourcePrefix control0 s.val).prodMk
      (measurable_control_draw.comp (ReferenceSourceCurrentControlFreshness.measurable_u_t s))
  have hi : (∫⁻ V, I V ∂P.toMeasure) = P U := by
    have heI : I = ({U} : Set (SlowSet p)).indicator (fun _ => (1 : ℝ≥0∞)) := by
      funext V
      simp only [I, Set.indicator, Set.mem_singleton_iff]
    rw [heI, lintegral_indicator_const (measurableSet_singleton U), one_mul,
      PMF.toMeasure_apply_singleton P U (measurableSet_singleton U)]
  calc
    _ = ∫⁻ x : Source × SlowSet p, F x.1 * I x.2
        ∂(mu.map (sourcePrefix control0 s.val)).prod P.toMeasure := by
      rw [← source_prefix_slow_product rate control0 ids s, lintegral_map htest hpair]
    _ = (∫⁻ z, F z ∂mu.map (sourcePrefix control0 s.val)) * P U := by
      rw [lintegral_prod_mul hF.aemeasurable hI.aemeasurable, hi]
    _ = _ := by
      rw [lintegral_map hF (ReferenceSourcePrefixHistoryFiltration.measurable_sourcePrefix control0 s.val)]
      exact (lintegral_mul_const (μ := mu) (P U)
        (show Measurable (fun z => F (sourcePrefix control0 s.val z)) from
          hF.comp (ReferenceSourcePrefixHistoryFiltration.measurable_sourcePrefix control0 s.val))).symm

private theorem launch_filter (s : Fin p.T) (w : Omega) (e : LogicalCell p rate)
    (hem : e ∈ archive w) (het : e.time = s)
    (heb : e.before = RecordedQueueRun.initialState p.K) :
    (archive w).filter (fun f => decide (f.time = s ∧ f.before.overflow = false)) = [e] := by
  let L := (archive w).filter (fun f => decide (f.time = s ∧ f.before.overflow = false))
  have he : e ∈ L := by
    exact List.mem_filter.mpr ⟨hem, by simp only [het, heb, RecordedQueueRun.initialState,
      and_self, decide_true]⟩
  have hnodup : L.Nodup := by
    exact ((ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalReadout_chronology
      rate rewards C_star C_h control0 w).filter _).imp (fun hab heq => by
        cases heq
        exact (Nat.lt_irrefl _ hab))
  have hunique : ∀ f ∈ L, f = e := by
    intro f hf
    obtain ⟨hfm, hft, _hfb⟩ := (by
      simpa only [L, List.mem_filter, decide_eq_true_eq] using hf :
        f ∈ archive w ∧ f.time = s ∧ f.before.overflow = false)
    have hen := (ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalReadout_enabled_iff
      rate rewards C_star C_h control0 w s).mp ⟨e, hem, het⟩
    obtain ⟨d, _, hd⟩ := (ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalReadout_unique_enabled
      rate rewards C_star C_h control0 w s).mpr hen
    exact (hd f ⟨hfm, hft⟩).trans (hd e ⟨hem, het⟩).symm
  change L = [e]
  cases hL : L with
  | nil => simp only [hL, List.not_mem_nil] at he
  | cons f fs =>
    have hf : f = e := hunique f (by rw [hL]; exact List.mem_cons_self)
    subst f
    cases fs with
    | nil => rfl
    | cons g gs =>
      have hg : g = e := hunique g (by rw [hL]; exact List.mem_cons_of_mem _ List.mem_cons_self)
      rw [hL, List.nodup_cons] at hnodup
      exact (hnodup.1 (by rw [hg]; exact List.mem_cons_self)).elim

/-- Before-draw initial slow-set cylinder on the actual finite launch stratum.
`none` is the raw exhaustive law; `some ids` is each original fixed-ID law.
The test reads exactly the source prefix and the actual strict archive.
Every future component is already recombined, and the PMF is evaluated on the
actual archived numerical PRE with its current weights as the new anchor. -/
theorem terminal_launch_slow_cylinder (ids : Option (CompletePublicTable.IDArray p))
    (s : Fin p.T) (U : SlowSet p)
    (Phi : Source × List (LogicalCell p rate) → ℝ≥0∞) (hPhi : Measurable Phi) :
    (∫⁻ w, Phi (sourcePrefix control0 s.val (Z w),
        ReferenceGeneratedCalendarEpisodePrefixRecombination.archiveBefore
          rate rewards C_star C_h control0 s.castSucc w) *
      ((((archive w).filter (fun e => decide (e.time = s ∧ e.before.overflow = false))).map
        (fun e => if e.slowSet = U then (1 : ℝ≥0∞) else 0)).sum)
      ∂(ids.elim (ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalLaw rate rewards C_star C_h control0)
        (ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDTerminalLaw rate rewards C_star C_h control0)).restrict
          (Z ⁻¹' launch s.val)) =
    ∫⁻ w, Phi (sourcePrefix control0 s.val (Z w),
        ReferenceGeneratedCalendarEpisodePrefixRecombination.archiveBefore
          rate rewards C_star C_h control0 s.castSucc w) *
      ((((archive w).filter (fun e => decide (e.time = s ∧ e.before.overflow = false))).map
        (fun e => RecordedSlowRefresh.recordedSlowPMF p Q e.before
          (RecordedQueueRun.scoreWeight Q e.before)
          (RecordedSlowRefresh.scoreWeight_pos Q e.before) U)).sum)
      ∂(ids.elim (ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalLaw rate rewards C_star C_h control0)
        (ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDTerminalLaw rate rewards C_star C_h control0)).restrict
          (Z ⁻¹' launch s.val) := by
  let lambda := ids.elim (ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalLaw rate rewards C_star C_h control0)
    (ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDTerminalLaw rate rewards C_star C_h control0)
  let mu := ids.elim (BootstrapPrivateRoundStreams.sourceInputLaw p)
    ReferenceFixedIDSourceSection.fixedIDSourceLaw
  let D : Set Omega := Z ⁻¹' launch s.val
  let G : Source → ℝ≥0∞ := fun z => Phi (sourcePrefix control0 s.val z, [])
  let F : Source → ℝ≥0∞ := fun z => if z ∈ launch s.val then Phi (z, []) else 0
  let I : Source → ℝ≥0∞ := fun z => if draw (vector (current s z)) = U then 1 else 0
  let mass := RecordedSlowRefresh.recordedSlowPMF p Q (RecordedQueueRun.initialState p.K)
    (RecordedQueueRun.scoreWeight Q (RecordedQueueRun.initialState p.K))
    (RecordedSlowRefresh.scoreWeight_pos Q (RecordedQueueRun.initialState p.K)) U
  have hZ := ReferenceExhaustiveGeneratedCalendarSourceLaw.measurable_terminalSource rate rewards C_star C_h control0
  have hlaunch := ReferenceGeneratedDownAmbiguityMeasurability.measurableSet_generatedLaunchFiberSet
    (rate := rate) rewards C_star C_h s.val
  have hD : MeasurableSet D := hlaunch.preimage hZ
  have hG : Measurable G := hPhi.comp
    ((ReferenceSourcePrefixHistoryFiltration.measurable_sourcePrefix control0 s.val).prodMk measurable_const)
  have hF : Measurable F := (hPhi.comp (measurable_id.prodMk measurable_const)).ite hlaunch measurable_const
  have hI : Measurable I := measurable_const.ite
    (measurableSet_eq_fun
      (measurable_control_draw.comp (ReferenceSourceCurrentControlFreshness.measurable_u_t s))
      measurable_const) measurable_const
  have hGL : Measurable (fun z => G z * I z) := hG.mul hI
  have hGR : Measurable (fun z => G z * mass) := hG.mul measurable_const
  have hmap : lambda.map Z = mu := by
    cases ids with
    | none =>
      exact ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalLaw_map_source
        rate rewards C_star C_h control0
    | some ids =>
      exact ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDTerminalLaw_map_source
        rate rewards C_star C_h control0 ids
  have hrestrict : (lambda.restrict D).map Z = mu.restrict (launch s.val) := by
    rw [← hmap, Measure.restrict_map hZ hlaunch]
  have hFp (z : Source) : F (sourcePrefix control0 s.val z) = if z ∈ launch s.val then G z else 0 := by
    dsimp only [F, G]
    rw [← ReferenceSourcePrefixHistoryFiltration.actualLaunchStratum_factor
      rate rewards C_star C_h control0 s.val s.isLt.le s.val le_rfl z]
  have hloc : (∫⁻ z, G z * I z ∂mu.restrict (launch s.val)) =
      ∫⁻ z, G z * mass ∂mu.restrict (launch s.val) := by
    rw [← lintegral_indicator hlaunch, ← lintegral_indicator hlaunch]
    have hleft : (launch s.val).indicator (fun z => G z * I z) =
        fun z => F (sourcePrefix control0 s.val z) * I z := by
      funext z
      rw [hFp]
      by_cases hz : z ∈ launch s.val <;>
        simp only [Set.indicator, hz, ite_true, ite_false, zero_mul]
    have hright : (launch s.val).indicator (fun z => G z * mass) =
        fun z => F (sourcePrefix control0 s.val z) * mass := by
      funext z
      rw [hFp]
      by_cases hz : z ∈ launch s.val <;>
        simp only [Set.indicator, hz, ite_true, ite_false, zero_mul]
    rw [hleft, hright]
    exact source_prefix_slow_cylinder rate control0 ids s U F hF
  calc
    _ = ∫⁻ w, G (Z w) * I (Z w) ∂lambda.restrict D := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem hD] with w hw
      obtain ⟨hpast, e, ⟨hem, het, _hen, heb, hes⟩, _⟩ :=
        terminal_launch_initialization rate rewards C_star C_h control0 s w hw
      have hf := launch_filter rate rewards C_star C_h control0 s w e hem het heb
      simp only [hf, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        add_zero, hpast, hes, G, I]
    _ = ∫⁻ z, G z * I z ∂mu.restrict (launch s.val) := by
      rw [← lintegral_map hGL hZ, hrestrict]
    _ = ∫⁻ z, G z * mass ∂mu.restrict (launch s.val) := hloc
    _ = ∫⁻ w, G (Z w) * mass ∂lambda.restrict D := by
      rw [← lintegral_map hGR hZ, hrestrict]
    _ = _ := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem hD] with w hw
      obtain ⟨hpast, e, ⟨hem, het, _hen, heb, _hes⟩, _⟩ :=
        terminal_launch_initialization rate rewards C_star C_h control0 s w hw
      have hf := launch_filter rate rewards C_star C_h control0 s w e hem het heb
      simp only [hf, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        add_zero, hpast, heb, G, mass]

end Bandits.Support.ReferenceGeneratedCalendarLaunchSlowInitialization

end
