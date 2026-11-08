/-
Copyright (c) 2026 Bandits formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedCalendarEpisodeTransitionCore
public import Bandits.Support.ReferenceGeneratedCalendarPrefixLiveFast
public import Bandits.Support.ReferenceGeneratedCalendarPrefixProposalErasure

/-!
# Actual-source first-LIVE support on the original erased prefix experiment

Sources: ZIP4 `04_slow_fast_learner.tex:329-390` and
`06_interruptions.tex:391-426`.

This module derives the strict LAUNCH seed, complete native PRE and replay
alignment, chronological support, actual LIVE readout, original phase coverage,
and birth initialization on the same original erased-prefix experiment. The
raw measure and every fixed-ID measure retain all source and private coordinates.
It supplies support for a later transition assembly; it asserts no incoming-set
law, transition-law assembly, manuscript closure or main-regret closure.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal Classical BigOperators
open Bandits.Support ConstructorDimensions
open ReferenceFirstLiveChronologicalPrefixFoundation
open ReferenceFirstLiveChronologicalPrefixMeasurability
open ReferenceGeneratedCalendarEpisodeHistoryTransport
open ReferenceGeneratedCalendarEpisodeTransitionCore
open ReferenceGeneratedCalendarPrefixProposalErasure
open ReferenceGeneratedCalendarEpisodePrefixRecombination
open ReferenceFirstCollectionLogicalPrefixExtension
open ReferenceFirstLiveCalendarMarkedTransition
open ReferenceGeneratedCalendarEpisodeSlowLaw
open ReferenceOriginalCalendarEpisodeChronology
open RecordedQuantizedEstimateReplay
open ContinuousControlSlice (Scalar scalarLaw)

namespace Bandits.Support.ReferenceGeneratedCalendarFirstLiveSourceSupport

variable {p : ConstructorDimensions.Parameters}

local instance sourceMeasurableSpace : MeasurableSpace (BootstrapPrivateRoundStreams.SourceInput p) := by
  change MeasurableSpace (CompletePublicTable.PublishedOutput p ×
    BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

local instance optionMeasurableSpace {A : Type*} [MeasurableSpace A] :
    MeasurableSpace (Option A) := LaterAssignmentStartMeasurability.optionMeasurableSpace

local instance slowSetMeasurableSpace : MeasurableSpace (SlowSet p) :=
  Subtype.instMeasurableSpace

attribute [local instance] ReferenceRankInstallationPostUpdateProposalLaw.optionSingleton
  ReferenceRankInstallationPostUpdateProposalLaw.listMeasurableSingleton
  ReferenceRankInstallationPostUpdateProposalLaw.sumMeasurableSingleton

variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
  (control0 : ContinuousLearningRows.TimeControl p)

local notation "Obs" => ReferenceFirstLiveCalendarMarkedTransition.Observation p rate
local notation "Innovation" => ContinuousLearningRows.TimeControl p × Scalar
local notation "Aux" => ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p
local notation "Lambda" => ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalLaw
  rate rewards C_star C_h control0
local notation "Q" => ReferenceFirstLaunchNumericalCell.queueParameters rate


/- Local notation abbreviates the accepted literal expressions only. -/
local notation "S₀" => RecordedQueueRun.initialState p.K
local notation "liveWindow" => ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow rate rewards C_star C_h
local notation "liveCells" => ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells rate rewards C_star C_h
local notation "nativePRE" => ReferencePostInvocationNoncallGeometry.prefixNumerical rate rewards C_star C_h
local notation "srcHistory" => prefixSourceHistory rate control0
local notation "sourceReplay" => sourceEpisodeReplay rate rewards C_star C_h
local notation "LiveSource" => LiveCalendarSource rate rewards C_star C_h
local notation "liveEntry" => liveCalendarEntry rate rewards C_star C_h
local notation "liveIndex" => liveCalendarIndex rate rewards C_star C_h
local notation "srcMark" => prefixCurrentMark rate rewards C_star C_h
local notation "insertControl" => ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p
local notation "srcPrefix" => ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0


omit rewards C_star C_h in
/-- Erasing the proposal retains the entire pre-round source history. -/
theorem prefixSourceHistory_eraseProposal (s q : Fin p.T) (o : Obs) :
    srcHistory s q (eraseProposal q o) =
      srcHistory s q o := rfl

omit rewards C_star C_h in
/-- Refilling that coordinate also leaves the complete history unchanged. -/
theorem prefixSourceHistory_refillProposal (s q : Fin p.T) (v : Obs × Scalar) :
    srcHistory s q (refillProposal q v) =
      srcHistory s q v.1 := rfl

/-- Before the first invocation, an original episode opportunity can only be
LAUNCH. Its strict numerical seed is produced as the complete zero state,
including empty accepted-record arrays; no seed or anchor equality is assumed. -/
theorem sourceStartEvent_beforeFirstCall_seed (s q : Fin p.T) (hsq : s.val ≤ q.val)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hno : ReferenceFirstCollectionLogicalPrefixExtension.NoCallBefore
      rate rewards C_star C_h q.succ z)
    (hs : z ∈ sourceStartEvent rate rewards C_star C_h s) :
    ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h = s.val ∧
      nativePRE s.castSucc
        (srcPrefix s.val z) =
          some (S₀) := by
  have hcall : ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h s z = none :=
    (ReferenceFirstCollectionLogicalPrefixExtension.noCallAt_iff_callAt_none
      rate rewards C_star C_h s z).mp (hno s (by change s.val < q.val + 1; omega))
  have hlaunch : z ∈ ReferenceGeneratedDownAmbiguityMeasurability.generatedLaunchFiberSet
      (rate := rate) rewards C_star C_h s.val := by
    rcases hs.1 with hl | ⟨hc, _⟩
    · exact hl
    · rw [hcall] at hc
      cases hc
  refine ⟨hlaunch.2, ?_⟩
  obtain ⟨rho, _, _⟩ := sourceStartEvent_episode_birth rate rewards C_star C_h s z hs
  have hl := complete_record_launch rate rewards C_star C_h z rho
  rw [← ReferencePostInvocationPrefixLocality.prefixNumerical_sourcePrefix
      rate rewards C_star C_h control0 s.castSucc s.val le_rfl z,
    ReferencePostInvocationNoncallGeometry.prefixNumerical_actualWord
      rate rewards C_star C_h s.castSucc z hl hlaunch.2.le]
  simp only [Fin.val_castSucc, hlaunch.2, Nat.sub_self, List.take_zero]
  rfl

/-- The same strict LAUNCH seed in the actual terminal history. Future source
insertions are removed only using the proved original-prefix agreement, on
the actual `q.succ` no-call event. This is pointwise on every component. -/
theorem terminal_beforeFirstCall_seed (s q : Fin p.T) (hsq : s.val ≤ q.val)
    (w : ReferenceExhaustiveGeneratedCalendarSourceLaw.Omega rate rewards C_star C_h)
    (hw : w ∈ beforeFirstCall rate rewards C_star C_h q.succ)
    (hs : w ∈ episodeStartEvent rate rewards C_star C_h control0 s) :
    nativePRE s.castSucc
      (sourceEstimateHistory rate rewards C_star C_h control0 s q w).1.1 =
        some (S₀) := by
  have hpre : w ∈ beforeFirstCall rate rewards C_star C_h s.castSucc :=
    fun t ht => hw t (by change t.val < q.val + 1; change t.val < s.val at ht; omega)
  have hp := sourcePrefix_terminal_original rate rewards C_star C_h control0 s.castSucc w hpre
  simp only [Fin.val_castSucc] at hp
  have hs0 : ReferenceExhaustiveGeneratedCalendarSourceLaw.originalSource
      rate rewards C_star C_h w ∈ sourceStartEvent rate rewards C_star C_h s := by
    rw [sourceStartEvent_sourcePrefix rate rewards C_star C_h control0 s, ← hp]
    exact (sourceStartEvent_sourcePrefix rate rewards C_star C_h control0 s _).mp hs
  have hseed := (sourceStartEvent_beforeFirstCall_seed rate rewards C_star C_h control0 s q hsq
    (ReferenceExhaustiveGeneratedCalendarSourceLaw.originalSource rate rewards C_star C_h w) hw hs0).2
  change nativePRE s.castSucc
    (srcPrefix s.val
      (ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalSource rate rewards C_star C_h control0 w)) = _
  rw [hp]
  exact hseed

/-- The actual first-LIVE native view has the anchor of the same produced
LAUNCH seed. The original physical record, selected view, episode origin and
clear seed are derived inside the proof. -/
theorem liveCalendar_native_anchor (s q : Fin p.T) (hsq : s.val ≤ q.val)
    (hq : q.val + 1 < FollowerCutoffScan.gridBoundary p rate.eta.val s)
    (z : LiveSource q)
    (hno : ReferenceFirstCollectionLogicalPrefixExtension.NoCallBefore
      rate rewards C_star C_h q.succ z.val)
    (hs : z.val ∈ sourceStartEvent rate rewards C_star C_h s)
    (hc : (nativePRE q.castSucc z.val).any (fun S => !S.overflow) = true) :
    let k := liveIndex q z
    let r := (liveWindow z.val)[k.val]
    let cell := ReferenceFirstLiveChronologicalPrefixFoundation.wholeLiveCell
      rate rewards C_star C_h z.val r (List.getElem_mem k.isLt)
    nativePRE s.castSucc
        (srcPrefix s.val z.val) =
          some (S₀) ∧
      cell.selected.view.payload.anchor = RecordedQueueRun.scoreWeight Q (S₀) := by
  intro k r cell
  have hseed := (sourceStartEvent_beforeFirstCall_seed rate rewards C_star C_h control0 s q hsq
    z.val hno hs).2
  refine ⟨hseed, ?_⟩
  have hp : liveWindow z.val <+:
      ReferenceCompletePhysicalHistory.completeSuffixRecords rate z.val rewards C_star C_h :=
    List.takeWhile_prefix _
  have hk := k.isLt.trans_le hp.length_le
  have hstart := ((ReferenceFirstLiveCalendarMarkedTransition.currentCellGate_iff
    rate rewards C_star C_h q z.val).mp z.property).1
  have hr : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h q z.val =
      some r := by
    rw [ReferenceSourcePrefixHistoryFiltration.actualRecord, ite_eq_left hstart]
    change (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z.val rewards C_star C_h)[k.val]? = some r
    rw [List.getElem?_eq_getElem hk, ← hp.getElem k.isLt]
  obtain ⟨rho0, ht, hb0⟩ := sourceStartEvent_episode_birth rate rewards C_star C_h s z.val hs
  have hcover : EpisodeCovers
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z.val rewards C_star C_h)[rho0.val] q :=
    ⟨hb0, ht ▸ hsq, ht ▸ hq⟩
  have hen := (nominalEnabled_iff_unique_episode rate rewards C_star C_h z.val q).mpr
    ⟨rho0, hcover, fun other ho =>
      complete_episode_interval_at_most_one rate rewards C_star C_h z.val q other rho0 ho hcover⟩
  obtain ⟨rho, P, r', c, v, hr', _, _, _, huniq, hb, _, _, hv, ha, _⟩ :=
    nominalEnabled_episode_data rate rewards C_star C_h z.val q hen
  have hrr : r' = r := Option.some.inj (hr'.symm.trans hr)
  subst r'
  have hvv : v = cell.selected := Option.some.inj (hv.symm.trans cell.selection_actual)
  subst v
  have hroot := huniq rho0 hcover
  rw [← hroot] at hb
  obtain ⟨A, hA, _, hanchor⟩ := episode_anchor_of_cover rate rewards C_star C_h control0
    z.val q rho0 P hcover hb hc
  rw [ht] at hA
  have hAi := Option.some.inj (hA.symm.trans hseed)
  subst A
  exact ha.trans hanchor

/-- The complete numerical PRE match is produced on the original erased
experiment. Both source gates and the current no-call gate are retained.
The seed and replay equations are conclusions, for raw and every fixed ID. -/
theorem ae_erased_prefix_retained_pre
    (ids : Option (CompletePublicTable.IDArray p)) (s q : Fin p.T)
    (hsq : s.val ≤ q.val) :
    ∀ᵐ v ∂(((ids.elim (betaPre rate rewards C_star C_h control0 q.castSucc)
      (fun id => fixedIDBetaPre rate rewards C_star C_h control0 id q.castSucc)).map
        (eraseProposal q)).prod scalarLaw).prod (calendarInnovationLaw p),
      let h := srcHistory s q v.1.1
      noCallAt rate rewards C_star C_h q v.1.1.1 →
      h.1.1 ∈ sourceStartEvent rate rewards C_star C_h s →
      h ∈ sourceHistoryRetained rate rewards C_star C_h s q →
      nativePRE
          s.castSucc h.1.1 = some (S₀) ∧
        (srcMark q (refillProposal q v.1, v.2)).map
          LogicalCell.before = sourceReplay s q h := by
  let μ := ids.elim Lambda
    (ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDTerminalLaw rate rewards C_star C_h control0)
  let β := ids.elim (betaPre rate rewards C_star C_h control0 q.castSucc)
    (fun id => fixedIDBetaPre rate rewards C_star C_h control0 id q.castSucc)
  let g := fun w => (prefixObservation rate rewards C_star C_h control0 q.castSucc w,
    currentInnovation rate rewards C_star C_h control0 q w)
  let P : Obs × Innovation → Prop := fun v =>
    let h := srcHistory s q v.1
    noCallAt rate rewards C_star C_h q v.1.1 →
    h.1.1 ∈ sourceStartEvent rate rewards C_star C_h s →
    h ∈ sourceHistoryRetained rate rewards C_star C_h s q →
    nativePRE
        s.castSucc h.1.1 = some (S₀) ∧
      (srcMark q v).map LogicalCell.before =
        sourceReplay s q h
  have hh : Measurable (fun v : Obs × Innovation => srcHistory s q v.1) :=
    (measurable_prefixSourceHistory rate control0 s q).comp measurable_fst
  have hm : Measurable (fun v : Obs × Innovation =>
      (srcMark q v).map LogicalCell.before) :=
    LaterAssignmentFullOutputMeasurability.measurable_optionMap _ measurable_logicalCell_before _
      (measurable_prefixCurrentMark rate rewards C_star C_h control0 q)
  have hP : MeasurableSet {v | P v} := by
    have he := (measurableSet_eq_fun
      ((ReferencePostInvocationPrefixLocality.measurable_prefixNumerical
        rate rewards C_star C_h s.castSucc).comp hh.fst.fst)
        (measurable_const (a := some (S₀)))).inter
      (measurableSet_eq_fun hm
        ((measurable_sourceEpisodeReplay rate rewards C_star C_h s q).comp hh))
    have hr := (measurableSet_sourceHistoryRetained rate rewards C_star C_h s q).preimage hh
    have hs := (measurableSet_sourceStartEvent rate rewards C_star C_h control0 s).preimage hh.fst.fst
    have hn : MeasurableSet {v : Obs × Innovation | noCallAt rate rewards C_star C_h q v.1.1} :=
      (measurableSet_noCallAt rate rewards C_star C_h control0 q).preimage measurable_fst.fst
    convert hn.compl.union (hs.compl.union (hr.compl.union he)) using 1
    ext v
    simp only [P, Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff,
      Set.mem_preimage, Set.mem_ofPred_eq, Function.comp_apply, imp_iff_not_or]
  have hg : Measurable g :=
    (measurable_prefixObservation rate rewards C_star C_h control0 q.castSucc).prodMk
      (measurable_currentInnovation rate rewards C_star C_h control0 q)
  have hprod : (μ.restrict (beforeFirstCall rate rewards C_star C_h q.castSucc)).map g =
      β.prod (calendarInnovationLaw p) := by
    cases ids with
    | none =>
      exact terminalLaw_restrict_map_prefixObservation_innovation rate rewards C_star C_h control0 q
    | some id =>
      exact fixedIDTerminalLaw_restrict_map_prefixObservation_innovation rate rewards C_star C_h control0 id q
  have hraw : ∀ᵐ v ∂β.prod (calendarInnovationLaw p), P v := by
    rw [← hprod]
    apply (ae_map_iff hg.aemeasurable hP).mpr
    apply (ae_restrict_iff' (measurableSet_beforeFirstCall rate rewards C_star C_h control0 q.castSucc)).mpr
    filter_upwards [ae_retained_source_input rate rewards C_star C_h control0 ids,
      ae_retainedEvent_sourceHistory rate rewards C_star C_h control0 ids] with w hw hr
    intro hpre
    dsimp only [P, g]
    rw [prefixSourceHistory_actual rate rewards C_star C_h control0 s q hsq w hpre]
    intro hno hs hret
    have hsucc : w ∈ beforeFirstCall rate rewards C_star C_h q.succ := by
      apply (noCallBefore_succ rate rewards C_star C_h q _).mpr
      refine ⟨hpre, ?_⟩
      exact (noCallAt_sourcePrefix rate rewards C_star C_h control0 q q.val le_rfl _).mpr hno
    have hstart : w ∈ episodeStartEvent rate rewards C_star C_h control0 s := by
      rw [episodeStartEvent_eq_history_preimage]
      exact hs
    have hret' := (hr s q hstart).mpr hret
    obtain ⟨e, _, _, he, _, _, _, hrep, _⟩ := hw s q hstart hret'
    refine ⟨terminal_beforeFirstCall_seed rate rewards C_star C_h control0 s q hsq w hsucc hstart, ?_⟩
    rw [prefixCurrentMark_actual rate rewards C_star C_h control0 q w hsucc, he, hrep]
    rfl
  let split : Obs → Obs × Scalar := fun o => (eraseProposal q o, currentProposal q o)
  have hsplit : Measurable split := (measurable_eraseProposal q).prodMk (measurable_currentProposal q)
  let r : (Obs × Scalar) × Innovation → Obs × Innovation :=
    fun v => (refillProposal q v.1, v.2)
  have hr : Measurable r :=
    ((measurable_refillProposal q).comp measurable_fst).prodMk measurable_snd
  have hmap : (β.prod (calendarInnovationLaw p)).map (Prod.map split id) =
      ((β.map (eraseProposal q)).prod scalarLaw).prod (calendarInnovationLaw p) := by
    rw [← Measure.map_prod_map β (calendarInnovationLaw p) hsplit measurable_id,
      Measure.map_id, betaPre_currentProposal_erasure_product rate rewards C_star C_h control0 ids q]
  have htransport : ∀ᵐ v ∂((β.map (eraseProposal q)).prod scalarLaw).prod
      (calendarInnovationLaw p), P (r v) := by
    rw [← hmap]
    apply (ae_map_iff (hsplit.prodMap measurable_id).aemeasurable (hP.preimage hr)).mpr
    filter_upwards [hraw] with v hv
    change P (refillProposal q (eraseProposal q v.1, currentProposal q v.1), v.2)
    rw [refillProposal_erase_current]
    exact hv
  exact htransport


/-- The original erased observer has a strict chronological past and the
original strict no-call support, before any live or retention restriction. -/
theorem ae_erased_prefix_past_noCall
    (ids : Option (CompletePublicTable.IDArray p)) (q : Fin p.T) :
    ∀ᵐ o ∂(ids.elim (betaPre rate rewards C_star C_h control0 q.castSucc)
      (fun id => fixedIDBetaPre rate rewards C_star C_h control0 id q.castSucc)).map
        (eraseProposal q),
      (∀ e ∈ o.2.2, e.time.val < q.val) ∧
        NoCallBefore rate rewards C_star C_h q.castSucc o.1 := by
  let P : Obs → Prop := fun o => (∀ e ∈ o.2.2, e.time.val < q.val) ∧
    NoCallBefore rate rewards C_star C_h q.castSucc o.1
  have hP : MeasurableSet {o | P o} := by
    have ht : Measurable (fun o : Obs => o.2.2.map LogicalCell.time) :=
      ReferenceActiveHorizonMeasurability.measurable_list_map _ measurable_snd.snd
        _ measurable_logicalCell_time
    have hb := (measurable_of_countable (fun L : List (Fin p.T) =>
      L.all (fun t => decide (t.val < q.val)))).comp ht
    have hlist : MeasurableSet {o : Obs | ∀ e ∈ o.2.2, e.time.val < q.val} := by
      simpa only [List.all_map, List.all_eq_true, Function.comp_apply, decide_eq_true_eq] using
        measurableSet_eq_fun hb (measurable_const (a := true))
    exact hlist.inter ((measurableSet_noCallBefore rate rewards C_star C_h control0 q.castSucc).preimage
      measurable_fst)
  have hraw : ∀ᵐ o ∂betaPre rate rewards C_star C_h control0 q.castSucc, P o := by
    rw [← extendedObservation_map_restrict_eq_betaPre rate rewards C_star C_h control0 q.castSucc]
    apply (ae_map_iff (measurable_extendedObservation rate rewards C_star C_h control0 q.castSucc).aemeasurable hP).mpr
    filter_upwards [ae_restrict_mem ((measurableSet_noCallBefore
      rate rewards C_star C_h control0 q.castSucc).preimage measurable_fst)] with za hza
    exact ⟨extendedPast_time_lt rate rewards C_star C_h q.castSucc za,
      (noCallBefore_sourcePrefix rate rewards C_star C_h control0 q.castSucc za.1).mp hza⟩
  have hids : ∀ᵐ o ∂ids.elim (betaPre rate rewards C_star C_h control0 q.castSucc)
      (fun id => fixedIDBetaPre rate rewards C_star C_h control0 id q.castSucc), P o := by
    cases ids with
    | none => exact hraw
    | some id => exact Measure.ae_smul_measure (hraw.filter_mono ae_restrict_le) _
  apply (ae_map_iff (measurable_eraseProposal q).aemeasurable hP).mpr
  exact hids

/-- The source-characterized current live record is the original record
at the current calendar date, including the final physical date. -/
theorem liveCalendar_actual_record (q : Fin p.T)
    (z : LiveSource q) :
    let k := liveIndex q z
    ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h q z.val =
      some (liveWindow z.val)[k.val] := by
  intro k
  have hp : liveWindow z.val <+:
      ReferenceCompletePhysicalHistory.completeSuffixRecords rate z.val rewards C_star C_h :=
    List.takeWhile_prefix _
  have hs := ((currentCellGate_iff rate rewards C_star C_h q z.val).mp z.property).1
  rw [ReferenceSourcePrefixHistoryFiltration.actualRecord, ite_eq_left hs]
  change (ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate z.val rewards C_star C_h)[k.val]? = _
  rw [List.getElem?_eq_getElem (k.isLt.trans_le hp.length_le), ← hp.getElem k.isLt]

omit control0 in
/-- The actual live entry retains its original physical calendar time. -/
theorem liveCalendarEntry_time (q : Fin p.T)
    (z : LiveSource q) (a : Aux) :
    (liveEntry q z a).time = q := by
  let k := liveIndex q z
  have ht := ReferenceFirstLiveChronologicalPrefixCausality.firstLiveChronologicalPrefix_cellTime
    rate rewards C_star C_h z.val a k
  change (liveEntry q z a).time = _ at ht
  rw [ht]
  apply Fin.ext
  have htime := (wholeLiveCell_geometry rate rewards C_star C_h z.val k).2.2.1
  have hs := ((currentCellGate_iff rate rewards C_star C_h q z.val).mp z.property).1
  dsimp only [k, liveCalendarIndex] at htime ⊢
  omega

omit control0 in
/-- The actual whole-window LIVE cell is the source's zero-start numerical
readout, with its full input rather than only its score weights. -/
theorem wholeLiveCell_readout
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (liveWindow z).length) :
    let W := liveWindow z
    let cell := wholeLiveCell rate rewards C_star C_h z W[k.val] (List.getElem_mem k.isLt)
    ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 W[k.val] = some cell.input := by
  intro W cell
  have hp : W <+: ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h :=
    List.takeWhile_prefix _
  obtain ⟨hc, _, _⟩ := ReferenceLaterLiveNumericalReadout.source_record_prefix
    rate rewards C_star C_h z ⟨k.val, k.isLt.trans_le hp.length_le⟩
  obtain ⟨_, hstart, _⟩ := ReferenceCompleteFirstPhaseObservationRecovery.actualFirstLiveRawObservationIdentity
    rate rewards C_star C_h z hc
  have hsigma : 0 < cell.selected.view.payload.sigma.val := by
    rw [(wholeLiveCell_geometry rate rewards C_star C_h z k).2.1]
    exact hstart
  have ho : ReferenceLaterLiveNumericalReadout.preparedOrdinary W[k.val] := by
    intro i
    rw [cell.ordinary i]
    rfl
  have hstates : ReferenceLaterLiveNumericalReadout.preparedStates W[k.val] ho = cell.states := by
    funext i
    exact (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
      ((ReferenceLaterLiveNumericalReadout.prepared_configuration W[k.val] ho i).symm.trans
        (cell.ordinary i))).1
  unfold ReferenceLaterLiveNumericalReadout.laterLiveReadout
  simp only [cell.selection_actual]
  rw [ite_eq_left ⟨hsigma, cell.assignment_live⟩, dite_eq_left ho, hstates, cell.input_eq]

include control0 in
omit control0 in
/-- The complete original numerical prefix at a LIVE date is the actual
entry's PRE, including all registers and accepted-record arrays. -/
theorem liveCalendarEntry_prefixNumerical (q : Fin p.T)
    (z : LiveSource q) (a : Aux) :
    nativePRE q.castSucc z.val =
      some (liveEntry q z a).before := by
  let W := liveWindow z.val
  let C := liveCells z.val
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z.val rewards C_star C_h
  let k := liveIndex q z
  have hp : W <+: R := List.takeWhile_prefix _
  have hk : k.val < R.length := k.isLt.trans_le hp.length_le
  have hl := complete_record_launch rate rewards C_star C_h z.val ⟨k.val, hk⟩
  let L := ReferenceActualCollectionHiddenRefreshPath.actualOriginalWord rate rewards C_star C_h z.val hl
  have hmap := ReferenceFirstCollectionLogicalNumericalAlignment.originalWord_record_map
    rate rewards C_star C_h z.val hl
  have hcells : W.map (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate) = C.map some := by
    apply List.ext_getElem
    · simp only [List.length_map, C, W, wholeFirstLiveCells_length]
    · intro j hj hj'
      have hjW : j < W.length := by simpa only [List.length_map] using hj
      let c := wholeLiveCell rate rewards C_star C_h z.val W[j] (List.getElem_mem hjW)
      have hread := wholeLiveCell_readout rate rewards C_star C_h z.val ⟨j, hjW⟩
      simp only [List.getElem_map]
      rw [ReferenceFirstCollectionCurrentRetainedGate.cell0, hread, Option.some_or]
      exact congrArg some (wholeLiveCell_input_eq rate rewards C_star C_h z.val ⟨j, hjW⟩)
  have hword : C = L.take W.length := by
    apply List.map_injective_iff.mpr (Option.some_injective _)
    rw [← hcells, List.map_take, ← hmap, ← List.map_take]
    exact congrArg (List.map (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate))
      (List.prefix_iff_eq_take.mp hp)
  have hs := ((currentCellGate_iff rate rewards C_star C_h q z.val).mp z.property).1
  rw [ReferencePostInvocationNoncallGeometry.prefixNumerical_actualWord
    rate rewards C_star C_h q.castSucc z.val hl hs]
  have hpre := (firstLiveChronologicalPrefix_queue_states rate rewards C_star C_h z.val a k).1
  change (liveEntry q z a).before =
    RecordedQueueRun.run Q (C.take k.val) at hpre
  rw [hpre, hword, List.take_take, Nat.min_eq_left k.isLt.le]
  rfl

include control0 in
/-- The current LIVE mark is the complete actual live entry after the
literal whole-control insertion. Strict-past support excludes a duplicate
current-date mark. Neither the seed nor a numerical match is assumed. -/
theorem prefixCurrentMark_live (q : Fin p.T) (o : Obs)
    (hg : currentCellGate rate rewards C_star C_h q o.1 = true)
    (hpast : ∀ e ∈ o.2.2, e.time.val < q.val)
    (x : Scalar) (ux : Innovation) :
    srcMark q (refillProposal q (o, x), ux) =
      some (liveEntry q
        ⟨insertControl q o.1 ux.1,
          (currentCellGate_replace_current rate rewards C_star C_h control0 q o.1 ux.1).trans hg⟩
        (roundAuxiliary q ((refillProposal q (o, x)).2.1, ux.2))) := by
  let z : LiveSource q :=
    ⟨insertControl q o.1 ux.1,
      (currentCellGate_replace_current rate rewards C_star C_h control0 q o.1 ux.1).trans hg⟩
  let a := roundAuxiliary q ((refillProposal q (o, x)).2.1, ux.2)
  let e := liveEntry q z a
  have hp : o.2.2.find? (fun e => e.time == q) = none := by
    apply List.find?_eq_none.mpr
    intro c hc h
    exact (hpast c hc).ne (congrArg Fin.val (beq_iff_eq.mp h))
  have ht : e.time = q := liveCalendarEntry_time rate rewards C_star C_h q z a
  change ((extendedPrefixStep rate rewards C_star C_h q (z.val, a)
    (incomingFromList rate o.2.2, o.2.2)).2.find? (fun e => e.time == q)) = some e
  unfold extendedPrefixStep prefixStep prefixCandidate
  rw [currentCellTag_live rate rewards C_star C_h q z a]
  change (o.2.2 ++ [e]).find? (fun c => c.time == q) = some e
  simp only [List.find?_append, hp, Option.none_or, List.find?_cons, ht, beq_self_eq_true]


include control0 in
/-- The whole original PRE ignores insertion of the current full control. -/
theorem prefixNumerical_replace_current (q : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (u : ContinuousLearningRows.TimeControl p) :
    nativePRE q.castSucc
      (insertControl q z u) =
    nativePRE q.castSucc z := by
  rw [ReferencePostInvocationPrefixLocality.prefixNumerical_sourcePrefix
    rate rewards C_star C_h control0 q.castSucc q.val le_rfl,
    ReferenceGeneratedCalendarPrefixLiveFast.sourcePrefix_replace_current control0,
    ← ReferencePostInvocationPrefixLocality.prefixNumerical_sourcePrefix
      rate rewards C_star C_h control0 q.castSucc q.val le_rfl]

/-- The erased original observer itself determines the full native LIVE PRE.
The support and AE replay match are produced from the original raw or fixed-ID
experiment. No numerical equality or law of the incoming set is an input. -/
theorem ae_erased_prefix_live_replay
    (ids : Option (CompletePublicTable.IDArray p)) (s q : Fin p.T)
    (hsq : s.val ≤ q.val) :
    ∀ᵐ o ∂(ids.elim (betaPre rate rewards C_star C_h control0 q.castSucc)
      (fun id => fixedIDBetaPre rate rewards C_star C_h control0 id q.castSucc)).map
        (eraseProposal q),
      (∀ e ∈ o.2.2, e.time.val < q.val) ∧
      NoCallBefore rate rewards C_star C_h q.castSucc o.1 ∧
      (let h := srcHistory s q o
       currentCellGate rate rewards C_star C_h q o.1 = true →
       noCallAt rate rewards C_star C_h q o.1 →
       h.1.1 ∈ sourceStartEvent rate rewards C_star C_h s →
       h ∈ sourceHistoryRetained rate rewards C_star C_h s q →
       nativePRE
           s.castSucc h.1.1 = some (S₀) ∧
       nativePRE
           q.castSucc o.1 = sourceReplay s q h) := by
  have hp := Measure.ae_ae_of_ae_prod (ae_erased_prefix_retained_pre
    rate rewards C_star C_h control0 ids s q hsq)
  have hp' := Measure.ae_ae_of_ae_prod hp
  filter_upwards [ae_erased_prefix_past_noCall rate rewards C_star C_h control0 ids q, hp'] with o ho hp
  refine ⟨ho.1, ho.2, ?_⟩
  dsimp only
  intro hg hn hs hr
  obtain ⟨x, hx⟩ := hp.exists
  obtain ⟨ux, hux⟩ := hx.exists
  obtain ⟨hseed, hpre⟩ := hux hn hs hr
  refine ⟨hseed, ?_⟩
  rw [prefixCurrentMark_live rate rewards C_star C_h control0 q o hg ho.1 x ux,
    Option.map_some] at hpre
  let z : LiveSource q :=
    ⟨insertControl q o.1 ux.1,
      (currentCellGate_replace_current rate rewards C_star C_h control0 q o.1 ux.1).trans hg⟩
  have he := liveCalendarEntry_prefixNumerical rate rewards C_star C_h q z
    (roundAuxiliary q ((refillProposal q (o, x)).2.1, ux.2))
  change nativePRE q.castSucc
    (insertControl q o.1 ux.1) = _ at he
  rw [prefixNumerical_replace_current rate rewards C_star C_h control0] at he
  exact he.trans hpre


omit control0 in
/-- A present actual LIVE source supplies its genuine launched-source event. -/
theorem liveCalendar_launchBy (q : Fin p.T)
    (z : LiveSource q) :
    ReferenceSourcePrefixHistoryFiltration.actualLaunchBy rate rewards C_star C_h q.val z.val := by
  refine ⟨?_, ((currentCellGate_iff rate rewards C_star C_h q z.val).mp z.property).1⟩
  cases hc : (ReferenceCompletePhysicalHistory.generatedBoundary rate z.val rewards C_star C_h).crossing with
  | some c => rfl
  | none =>
      have hw := (ReferenceFirstLiveOverflowReadout.wholeFirstLive_no_launch
        rate rewards C_star C_h z.val hc).1
      have hk := ((currentCellGate_iff rate rewards C_star C_h q z.val).mp z.property).2
      rw [hw, List.length_nil] at hk
      exact False.elim (Nat.not_lt_zero _ hk)

include control0 in
/-- Whole-current-control insertion preserves the actual first launch time.
Both launch events are derived from their unchanged actual LIVE gates. -/
theorem liveCalendar_start_replace_current (q : Fin p.T)
    (z : LiveSource q) (u : ContinuousLearningRows.TimeControl p) :
    ReferenceCompletePhysicalHistory.physicalStart rate
        (insertControl q z.val u) rewards C_star C_h =
      ReferenceCompletePhysicalHistory.physicalStart rate z.val rewards C_star C_h := by
  let zu : LiveSource q :=
    ⟨insertControl q z.val u,
      (currentCellGate_replace_current rate rewards C_star C_h control0 q z.val u).trans z.property⟩
  have h0 := (ReferenceSourcePrefixHistoryFiltration.sourcePrefix_preserves_actual_launch
    rate rewards C_star C_h control0 q.val q.isLt.le z.val
      (liveCalendar_launchBy rate rewards C_star C_h q z)).1
  have hu := (ReferenceSourcePrefixHistoryFiltration.sourcePrefix_preserves_actual_launch
    rate rewards C_star C_h control0 q.val q.isLt.le zu.val
      (liveCalendar_launchBy rate rewards C_star C_h q zu)).1
  change ReferenceCompletePhysicalHistory.physicalStart rate
      (insertControl q z.val u) rewards C_star C_h = _ at hu
  rw [ReferenceGeneratedCalendarPrefixLiveFast.sourcePrefix_replace_current control0] at hu
  exact hu.trans h0.symm

include control0 in
/-- The original first-LIVE gate is exactly birth and the two original
positive-offset phases. Failed launch, prelaunch and exited-window sources
are excluded by the literal gate, without a coverage hypothesis. -/
theorem currentCellGate_iff_sourcePhases (q : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p) :
    currentCellGate rate rewards C_star C_h q z = true ↔
      z ∈ ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h q 2 ∨
      z ∈ ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h q 3 ∨
      z ∈ ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h q 4 := by
  constructor
  · intro hg
    have hl := liveCalendar_launchBy rate rewards C_star C_h q ⟨z, hg⟩
    have hgeom := (currentCellGate_iff rate rewards C_star C_h q z).mp hg
    obtain ⟨which, hw⟩ := ReferenceFirstLiveSourcePhasePartition.source_phases_exhaustive
      rate rewards C_star C_h q z
    fin_cases which
    · change (ReferenceCompletePhysicalHistory.generatedBoundary rate z rewards C_star C_h).crossing = none at hw
      have hcross := hl.1
      rw [hw] at hcross
      cases hcross
    · exact False.elim (Nat.not_lt_of_ge hgeom.1 hw.2)
    · exact Or.inl hw
    · exact Or.inr (Or.inl hw)
    · exact Or.inr (Or.inr hw)
    · exact False.elim (Nat.not_lt_of_ge hw.2.2 hgeom.2)
  · rintro (hb | hp | he)
    · apply (currentCellGate_iff rate rewards C_star C_h q z).mpr
      refine ⟨hb.2.ge, ?_⟩
      simpa only [hb.2, Nat.sub_self] using
        ReferenceFirstLiveSourcePhasePartition.source_birth_window_pos rate rewards C_star C_h q control0 z hb
    · rcases hp with ⟨_, hpos, hk, _⟩
      exact (currentCellGate_iff rate rewards C_star C_h q z).mpr ⟨hpos.le, hk⟩
    · rcases he with ⟨_, hpos, hk, _⟩
      exact (currentCellGate_iff rate rewards C_star C_h q z).mpr ⟨hpos.le, hk⟩


/-- At an actual first-LIVE birth the original erased observer contains no
chronological cells. This follows from its original enlarged-source map,
without a supplied empty-history or supported-observer premise. -/
theorem ae_erased_birth_past
    (ids : Option (CompletePublicTable.IDArray p)) (q : Fin p.T) :
    ∀ᵐ o ∂(ids.elim (betaPre rate rewards C_star C_h control0 q.castSucc)
      (fun id => fixedIDBetaPre rate rewards C_star C_h control0 id q.castSucc)).map
        (eraseProposal q),
      currentCellGate rate rewards C_star C_h q o.1 = true →
      ReferenceCompletePhysicalHistory.physicalStart rate o.1 rewards C_star C_h = q.val →
      o.2.2 = [] := by
  let P : Obs → Prop := fun o => currentCellGate rate rewards C_star C_h q o.1 = true →
    ReferenceCompletePhysicalHistory.physicalStart rate o.1 rewards C_star C_h = q.val → o.2.2 = []
  have hP : MeasurableSet {o | P o} := by
    have hg : MeasurableSet {o : Obs | currentCellGate rate rewards C_star C_h q o.1 = true} :=
      ((measurable_currentCellGate rate rewards C_star C_h q).comp measurable_fst)
        (measurableSet_singleton true)
    have hb : MeasurableSet {o : Obs |
        ReferenceCompletePhysicalHistory.physicalStart rate o.1 rewards C_star C_h = q.val} :=
      ((ReferenceCompleteSuffixInputMeasurability.measurable_physicalStart
        rate rewards C_star C_h).comp measurable_fst) (measurableSet_singleton q.val)
    have hlen : Measurable (fun o : Obs => o.2.2.length) :=
      measurable_fst.comp
        (ReferenceActiveHorizonMeasurability.measurable_listObservationCoordinates.comp measurable_snd.snd)
    have hnil : MeasurableSet {o : Obs | o.2.2 = []} := by
      convert hlen (measurableSet_singleton 0) using 1
      ext o
      exact List.eq_nil_iff_length_eq_zero
    convert hg.compl.union (hb.compl.union hnil) using 1
    ext o
    simp only [P, Set.mem_union, Set.mem_compl_iff, Set.mem_ofPred_eq, imp_iff_not_or]
  have horiginal (za : BootstrapPrivateRoundStreams.SourceInput p × Aux) :
      P (extendedObservation rate rewards C_star C_h control0 q.castSucc za) := by
    intro hg hb
    have hg0 : currentCellGate rate rewards C_star C_h q za.1 = true :=
      (currentCellGate_sourcePrefix rate rewards C_star C_h control0 q za.1).trans hg
    let z : LiveSource q := ⟨za.1, hg0⟩
    have hstart := (ReferenceSourcePrefixHistoryFiltration.sourcePrefix_preserves_actual_launch
      rate rewards C_star C_h control0 q.val q.isLt.le za.1
        (liveCalendar_launchBy rate rewards C_star C_h q z)).1
    have hb0 : ReferenceCompletePhysicalHistory.physicalStart rate za.1 rewards C_star C_h = q.val :=
      hstart.trans hb
    exact congrArg (fun o : Obs => o.2.2)
      (ReferenceGeneratedCalendarPrefixLiveFast.extendedObservation_at_start
        rate rewards C_star C_h control0 q za.1 za.2 hb0)
  have hraw : ∀ᵐ o ∂betaPre rate rewards C_star C_h control0 q.castSucc, P o := by
    rw [← extendedObservation_map_restrict_eq_betaPre rate rewards C_star C_h control0 q.castSucc]
    apply (ae_map_iff (measurable_extendedObservation rate rewards C_star C_h control0 q.castSucc).aemeasurable hP).mpr
    exact Filter.Eventually.of_forall horiginal
  have hids : ∀ᵐ o ∂ids.elim (betaPre rate rewards C_star C_h control0 q.castSucc)
      (fun id => fixedIDBetaPre rate rewards C_star C_h control0 id q.castSucc), P o := by
    cases ids with
    | none => exact hraw
    | some id => exact Measure.ae_smul_measure (hraw.filter_mono ae_restrict_le) _
  apply (ae_map_iff (measurable_eraseProposal q).aemeasurable hP).mpr
  exact hids

/-- Actual retained birth forces the episode date to be the physical birth
and produces empty history, the complete initial seed and zero numerical PRE.
The birth may occur at any physical date. -/
theorem ae_erased_birth_initialization
    (ids : Option (CompletePublicTable.IDArray p)) (s q : Fin p.T)
    (hsq : s.val ≤ q.val) :
    ∀ᵐ o ∂(ids.elim (betaPre rate rewards C_star C_h control0 q.castSucc)
      (fun id => fixedIDBetaPre rate rewards C_star C_h control0 id q.castSucc)).map
        (eraseProposal q),
      currentCellGate rate rewards C_star C_h q o.1 = true →
        ReferenceCompletePhysicalHistory.physicalStart rate o.1 rewards C_star C_h = q.val →
        noCallAt rate rewards C_star C_h q o.1 →
        (srcHistory s q o).1.1 ∈ sourceStartEvent rate rewards C_star C_h s →
        srcHistory s q o ∈ sourceHistoryRetained rate rewards C_star C_h s q →
        s = q ∧ o.2.2 = [] ∧
          nativePRE s.castSucc
            (srcHistory s q o).1.1 = some (S₀) ∧
          sourceReplay s q (srcHistory s q o) =
            some (S₀) := by
  filter_upwards [ae_erased_prefix_live_replay rate rewards C_star C_h control0 ids s q hsq,
    ae_erased_birth_past rate rewards C_star C_h control0 ids q] with o ho hp
  intro hg hb hn hs hr
  have hno : NoCallBefore rate rewards C_star C_h q.succ o.1 :=
    (noCallBefore_succ rate rewards C_star C_h q o.1).mpr ⟨ho.2.1, hn⟩
  have hs0 : o.1 ∈ sourceStartEvent rate rewards C_star C_h s :=
    (sourceStartEvent_sourcePrefix rate rewards C_star C_h control0 s o.1).mpr hs
  have hlaunch := (sourceStartEvent_beforeFirstCall_seed
    rate rewards C_star C_h control0 s q hsq o.1 hno hs0).1
  have hsq' : s = q := Fin.ext (hlaunch.symm.trans hb)
  obtain ⟨hseed, hprefix⟩ := ho.2.2 hg hn hs hr
  let z : LiveSource q := ⟨o.1, hg⟩
  have hbefore := ReferenceGeneratedCalendarPrefixLiveFast.currentCellTag_birth_before
    rate rewards C_star C_h q o.1 ReferenceFirstLiveActualRefreshTestLaw.auxiliarySection
    (liveEntry q z ReferenceFirstLiveActualRefreshTestLaw.auxiliarySection)
    (currentCellTag_live rate rewards C_star C_h q z ReferenceFirstLiveActualRefreshTestLaw.auxiliarySection) hb
  have hnum := liveCalendarEntry_prefixNumerical rate rewards C_star C_h q z ReferenceFirstLiveActualRefreshTestLaw.auxiliarySection
  rw [hbefore] at hnum
  exact ⟨hsq', hp hg hb, hseed, hprefix.symm.trans hnum⟩

end Bandits.Support.ReferenceGeneratedCalendarFirstLiveSourceSupport
