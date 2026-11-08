/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedCalendarRetainedFastCore
import Bandits.Support.ReferenceGeneratedCalendarEpisodeTransitionCore

/-!
# The actual later CALL FAST test

Sources: ZIP4 `04_slow_fast_learner.tex:16-37,96-114,140-215,323-390`
and `06_interruptions.tex:391-426`.

The calculation retains the complete current assignment vector and integrates
the correlated recorder/FAST pair through its second marginal. The history is
the accepted strict source history, before the current estimate and FAST draw.
Only the original ID atom is normalized in the fixed-ID statement.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal Classical BigOperators
open Bandits.Support ConstructorDimensions
open ReferenceFirstLiveChronologicalPrefixFoundation
open ReferenceFirstLiveChronologicalPrefixMeasurability
open ReferencePostInvocationNoncallGeometry
open ReferencePostInvocationPrefixLocality
open ReferencePostInvocationGeneratedAlignment
open ReferenceGeneratedInvocationCallSplice
open ReferenceGeneratedRankCalendarFoundation
open ReferenceGeneratedCalendarResidualBlock
open ReferenceGeneratedCalendarNativePreservation
open ReferenceGeneratedCalendarPathAgreement
open ReferenceGeneratedCalendarMarkedPath
open ReferenceGeneratedCalendarJointRebase
open ReferenceGeneratedCalendarRoundInnovation
open ReferenceGeneratedCalendarEpisodeSlowLaw
open ReferenceGeneratedCalendarEpisodeHistoryTransport
open ReferenceOriginalCalendarEpisodeChronology
open ReferenceSourcePrefixHistoryFiltration (sourcePrefix actualRecord)
open ReferenceFirstLaunchNumericalCell (queueParameters)
open RecordedQueueRun (scoreWeight)
open CanonicalFastSampling (FastArm)

namespace Bandits.Support.ReferenceGeneratedCalendarLaterCallFast

variable {p : ConstructorDimensions.Parameters}

local instance sourceMeasurableSpace :
    MeasurableSpace (BootstrapPrivateRoundStreams.SourceInput p) := by
  change MeasurableSpace (CompletePublicTable.PublishedOutput p ×
    BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

local instance optionMeasurableSpace {A : Type*} [MeasurableSpace A] :
    MeasurableSpace (Option A) := LaterAssignmentStartMeasurability.optionMeasurableSpace

local instance slowSetMeasurableSpace : MeasurableSpace (SlowSet p) :=
  Subtype.instMeasurableSpace

attribute [local instance] ReferenceRankInstallationPostUpdateProposalLaw.listMeasurableSingleton
  ReferenceRankInstallationPostUpdateProposalLaw.sumMeasurableSingleton
  ReferenceRankInstallationRecorderFoundation.optionSingleton

variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
  (control0 : ContinuousLearningRows.TimeControl p)

local notation "Q" => queueParameters rate
local notation "Source" => BootstrapPrivateRoundStreams.SourceInput p
local notation "Vector" => AssignmentParameterFibreKernel.AssignmentVector p
local notation "Past" => Source × (SlowSet p × List (LogicalCell p rate))
local notation "Pair" => ReferenceRankInstallationRecorderFastSourceLaw.RecorderFastOutput p

omit rate rewards C_star C_h control0 in
private theorem measurable_list_getElem? {A : Type*} [MeasurableSpace A] (k : ℕ) :
    Measurable (fun L : List A => L[k]?) := by
  have htag : Measurable (fun L : List A =>
      ReferenceActiveHorizonMeasurability.listObservationAt L k) := (measurable_pi_apply k).comp
    (ReferenceActiveHorizonMeasurability.measurable_listObservationCoordinates (α := A)).snd
  have hdecode : Measurable (Sum.elim (fun _ : Unit => (none : Option A)) some) :=
    measurable_fun_sum measurable_const
      (LaterAssignmentFullOutputMeasurability.measurable_some_of_measurable _ measurable_id)
  convert hdecode.comp htag using 1
  funext L
  simp only [Function.comp_apply, ReferenceActiveHorizonMeasurability.listObservationAt]
  cases L[k]? <;> rfl

omit rewards C_star C_h control0 in
private theorem measurable_find_time (q : Fin p.T) :
    Measurable (fun L : List (LogicalCell p rate) => L.find? (fun e => e.time == q)) := by
  have ht := ReferenceActiveHorizonMeasurability.measurable_list_map id measurable_id
    LogicalCell.time (measurable_logicalCell_time (rate := rate))
  have hn := (measurable_of_countable (fun L : List (Fin p.T) =>
    L.findIdx (fun t => t == q))).comp ht
  have hg : Measurable (fun nL : ℕ × List (LogicalCell p rate) => nL.2[nL.1]?) :=
    measurable_from_prod_countable_right (fun n => measurable_list_getElem? n)
  convert hg.comp (hn.prodMk measurable_id) using 1
  funext L
  simp only [Function.comp_apply, List.find?_eq_getElem?_findIdx, List.findIdx_map, id_eq]
  rfl

omit rate rewards C_star C_h control0 in
private theorem measurable_list_take {A : Type*} [MeasurableSpace A] (n : ℕ) :
    Measurable (fun L : List A => L.take n) := by
  have hc := ReferenceActiveHorizonMeasurability.measurable_listObservationCoordinates (α := A)
  apply measurable_comap_iff.mpr
  change Measurable (fun L : List A => ((L.take n).length,
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

omit rewards C_star C_h control0 in
private theorem chronological_filter_eq_take (L : List (LogicalCell p rate))
    (hL : L.Pairwise (fun e f => e.time.val < f.time.val)) (n : ℕ) :
    L.filter (fun e => e.time.val < n) =
      L.take (((L.map LogicalCell.time).filter (fun t => t.val < n)).length) := by
  have h : L.filter (fun e => e.time.val < n) =
      L.take (L.filter (fun e => e.time.val < n)).length := by
    induction L with
    | nil => rfl
    | cons e L ih =>
      obtain ⟨heL, hL⟩ := List.pairwise_cons.mp hL
      by_cases he : e.time.val < n
      · simp only [List.filter_cons, decide_eq_true he, ite_true,
          List.length_cons, List.take_succ_cons]
        exact congrArg (List.cons e) (ih hL)
      · have hf : L.filter (fun e => e.time.val < n) = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro c hc
          have ht := heL c hc
          simpa only [decide_eq_true_eq] using (show ¬ c.time.val < n by omega)
        simp only [List.filter_cons, decide_eq_false he, Bool.false_eq_true, ite_false,
          hf, List.length_nil, List.take_zero]
  rw [h]
  apply congrArg (fun m => L.take m)
  rw [List.filter_map, List.length_map]
  rfl

/-- A measurable expression for the accepted history on a chronological
past. The equality below identifies it with the existing calendar observer. -/
private def historyFromPast (s q : Fin p.T) (a : Past) : History rate s q :=
  ((sourcePrefix control0 s.val a.1,
    a.2.2.take (((a.2.2.map LogicalCell.time).filter (fun t => t.val < s.val)).length)),
    fun v => sourceOptionalEstimate rate (a.2.2.find? (fun e => e.time == v.val)))

private theorem measurable_historyFromPast (s q : Fin p.T) :
    Measurable (historyFromPast rate control0 s q) := by
  have ht := ReferenceActiveHorizonMeasurability.measurable_list_map
    (fun a : Past => a.2.2) measurable_snd.snd LogicalCell.time
    (measurable_logicalCell_time (rate := rate))
  have hn := (measurable_of_countable (fun L : List (Fin p.T) =>
    (L.filter (fun t => t.val < s.val)).length)).comp ht
  have htake : Measurable (fun v : ℕ × List (LogicalCell p rate) => v.2.take v.1) :=
    measurable_from_prod_countable_right (fun n => measurable_list_take n)
  exact (((ReferenceSourcePrefixHistoryFiltration.measurable_sourcePrefix control0 s.val).comp
    measurable_fst).prodMk (htake.comp (hn.prodMk measurable_snd.snd))).prodMk
      (measurable_pi_iff.mpr fun v => (measurable_sourceOptionalEstimate rate).comp
        ((measurable_find_time rate v.val).comp measurable_snd.snd))

variable (b0 : Bool) (u0 t0 : Fin p.T)

local notation "Sample" => CalendarSample rate rewards C_star C_h b0 u0 t0
local notation "current" => calendarCurrentSource rate rewards C_star C_h control0 b0 u0 t0
local notation "observe" => calendarObservation rate rewards C_star C_h control0 b0 u0 t0
local notation "past" => calendarRoundPast rate rewards C_star C_h control0 b0 u0 t0
local notation "law" => calendarLaw rate rewards C_star C_h control0 b0 u0 t0
local notation "call" => calendarCallFlag rate rewards C_star C_h control0 b0 u0 t0
local notation "pending" => calendarPendingFlags rate rewards C_star C_h control0 b0 u0 t0
local notation "history" => calendarSourceHistory rate rewards C_star C_h control0 b0 u0 t0

private theorem historyFromPast_calendar (s q : Fin p.T) (hsq : s.val ≤ q.val)
    (k : ℕ) (hk : t0.val + 1 + k ≤ p.T) (hq : q.val = t0.val + 1 + k) (w : Sample k) :
    historyFromPast rate control0 s q (past k hk w) = history s q k hk w := by
  have hchron := (calendarObservation_chronology rate rewards C_star C_h control0 b0 u0 t0 k hk w).1
  change (calendarStoredState rate rewards C_star C_h control0 b0 u0 t0 k hk w).2.Pairwise
    (fun e f => e.time.val < f.time.val) at hchron
  unfold historyFromPast calendarSourceHistory calendarRoundPast
  rw [ReferenceSourcePrefixHistoryFiltration.sourcePrefix_sourcePrefix control0 s.val _ (by omega)]
  dsimp only
  rw [← chronological_filter_eq_take rate _ hchron s.val]

private def viewFromPast (q : Fin p.T) (a : Past × Vector) :
    Option (ReferenceDownReception.ChoiceTimeView p rate.eta) :=
  ReferenceRankInstallationRecorderFoundation.viewFromHistory rate rewards C_star C_h control0 q
    (ReferenceRankInstallationRecorderFoundation.prefixVectorHistory rate rewards C_star C_h control0 q
      (a.1.1, a.2))

private theorem measurable_viewFromPast (q : Fin p.T) :
    Measurable (viewFromPast rate rewards C_star C_h control0 q) :=
  (ReferenceRankInstallationRecorderFoundation.measurable_viewFromHistory rate rewards C_star C_h control0 q).comp
    ((ReferenceRankInstallationRecorderFoundation.measurable_prefixVectorHistory rate rewards C_star C_h control0 q).comp
      (measurable_fst.fst.prodMk measurable_snd))

private theorem viewFromPast_calendar (k : ℕ) (hk : t0.val + 1 + k < p.T)
    (w : Sample k) (v : Vector) (hc : call k (by omega) w = true) :
    let q : Fin p.T := ⟨t0.val + 1 + k, hk⟩
    let z := calendarInvocationSource rate rewards C_star C_h control0 b0 u0 t0 k hk w v hc
    viewFromPast rate rewards C_star C_h control0 q (past k hk.le w, v) =
      some (nativeSourceCell rate rewards C_star C_h q z).selected.view := by
  dsimp only
  let q : Fin p.T := ⟨t0.val + 1 + k, hk⟩
  let z := calendarInvocationSource rate rewards C_star C_h control0 b0 u0 t0 k hk w v hc
  have hh := ReferenceRankInstallationRecorderFoundation.history_eq_prefixVectorHistory_of_installation
    rate rewards C_star C_h control0 (nativeRank rate rewards C_star C_h q z.val) q z.val
      (native_installation rate rewards C_star C_h q z)
  have hp : sourcePrefix control0 q.val z.val = (past k hk.le w).1 :=
    ReferenceFirstCollectionOldRecorderFoundation.sourcePrefix_replaceCurrent control0 q q.val le_rfl _ _
  have hv : ReferenceFirstCollectionSamplerOutputLaw.currentAssignmentVector q z.val = v :=
    ReferenceFirstCollectionRenewalVectorInsertion.av_insert _ _ v
  rw [hp, hv] at hh
  rw [viewFromPast, ← hh, ← ReferenceRankInstallationRecorderFoundation.actualInstallationView_eq_history]
  exact nativeCell_view rate rewards C_star C_h control0 q z

/-- The gate on the actual strict history supplies the native clear PRE and
the SAME strict seed and operative anchor. All facts are pointwise. -/
private theorem call_history_parameters (s : Fin p.T) (k : ℕ)
    (hk : t0.val + 1 + k < p.T) (hs : s.val ≤ t0.val + 1 + k)
    (w : Sample k) (v : Vector) (hc : call k (by omega) w = true)
    (hstart : (history s ⟨t0.val + 1 + k, hk⟩ k hk.le w).1.1 ∈
      sourceStartEvent rate rewards C_star C_h s)
    (hret : history s ⟨t0.val + 1 + k, hk⟩ k hk.le w ∈
      sourceHistoryRetained rate rewards C_star C_h s ⟨t0.val + 1 + k, hk⟩) :
    let q : Fin p.T := ⟨t0.val + 1 + k, hk⟩
    let z := calendarInvocationSource rate rewards C_star C_h control0 b0 u0 t0 k hk w v hc
    (pending k (by omega) w).2 = true ∧
      ∃ A : RecordedQueueRun.RunState p.K,
        prefixNumerical rate rewards C_star C_h s.castSucc (history s q k hk.le w).1.1 = some A ∧
        sourceEpisodeReplay rate rewards C_star C_h s q (history s q k hk.le w) =
          some (nativeBefore rate rewards C_star C_h control0 q z) ∧
        (nativeSourceCell rate rewards C_star C_h q z).selected.view.payload.anchor = scoreWeight Q A := by
  dsimp only
  let q : Fin p.T := ⟨t0.val + 1 + k, hk⟩
  let z := calendarInvocationSource rate rewards C_star C_h control0 b0 u0 t0 k hk w v hc
  let h := history s q k hk.le w
  obtain ⟨hsq, hq, hclear⟩ := hret
  have hreplay := ReferenceGeneratedCalendarEpisodeTransitionCore.calendarSourceHistory_replay
    rate rewards C_star C_h control0 b0 u0 t0 s q hsq k hk.le le_rfl w hstart hq
  have hnum := calendarObservation_numerical rate rewards C_star C_h control0 b0 u0 t0 k hk.le w
  change (observe k hk.le w).2.val.2.2.1 =
    prefixNumerical rate rewards C_star C_h q.castSucc (current k hk.le w) at hnum
  have hpend : (pending k (by omega) w).2 = true := by
    change (observe k hk.le w).2.val.2.2.1.any (fun S => !S.overflow) = true
    rw [hnum, ← hreplay]
    exact hclear
  have hp : sourcePrefix control0 q.val z.val = sourcePrefix control0 q.val (current k hk.le w) :=
    ReferenceFirstCollectionOldRecorderFoundation.sourcePrefix_replaceCurrent control0 q q.val le_rfl _ _
  have hsz : sourcePrefix control0 s.val z.val = h.1.1 := by
    change sourcePrefix control0 s.val z.val = sourcePrefix control0 s.val (current k hk.le w)
    have hh := congrArg (sourcePrefix control0 s.val) hp
    simpa only [ReferenceSourcePrefixHistoryFiltration.sourcePrefix_sourcePrefix control0 s.val q.val hs] using hh
  have hpre : prefixNumerical rate rewards C_star C_h q.castSucc z.val =
      prefixNumerical rate rewards C_star C_h q.castSucc (current k hk.le w) := by
    rw [prefixNumerical_sourcePrefix rate rewards C_star C_h control0 q.castSucc q.val le_rfl z.val,
      hp, ← prefixNumerical_sourcePrefix rate rewards C_star C_h control0 q.castSucc q.val le_rfl]
  have hS : sourceEpisodeReplay rate rewards C_star C_h s q h =
      some (nativeBefore rate rewards C_star C_h control0 q z) :=
    hreplay.trans (hpre.symm.trans (nativeBefore_prefix rate rewards C_star C_h control0 q z))
  have hstartz : z.val ∈ sourceStartEvent rate rewards C_star C_h s :=
    (sourceStartEvent_sourcePrefix rate rewards C_star C_h control0 s z.val).mpr (hsz ▸ hstart)
  obtain ⟨input, hi, hen, _hr, _hrates, _hn, _hb, _ha⟩ :=
    calendarInvocationCell_actualInput rate rewards C_star C_h control0 b0 u0 t0 k hk w v hc
  have henabled : ReferenceExhaustiveGeneratedCalendarSourceLaw.nominalEnabled
      rate rewards C_star C_h q z.val = true := by
    change ((actualRecord rate rewards C_star C_h q z.val).bind
      (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate)).any (fun c => c.enabled) = true
    rw [hi, Option.any_some, hen]
  obtain ⟨rho, P, r, c, sel, hr, _hc, _hen, hcover, huniq, hb, _hPuniq,
      _hbefore, hsel, hanchor, _hrate, _hgrid, _hclock⟩ :=
    nominalEnabled_episode_data rate rewards C_star C_h z.val q henabled
  obtain ⟨rho0, ht0, hbirth0⟩ := sourceStartEvent_episode_birth
    rate rewards C_star C_h s z.val hstartz
  have hcover0 : EpisodeCovers
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z.val rewards C_star C_h)[rho0.val] q :=
    ⟨hbirth0, ht0 ▸ hsq, ht0 ▸ hq⟩
  have hrho := huniq rho0 hcover0
  have ht : (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z.val rewards C_star C_h)[rho.val].input.time = s := by
    simpa only [hrho] using ht0
  have hclearz : (prefixNumerical rate rewards C_star C_h q.castSucc z.val).any
      (fun S => !S.overflow) = true := by
    rw [hpre, ← hreplay]
    exact hclear
  obtain ⟨A, hA, _hAc, hPA⟩ := episode_anchor_of_cover
    rate rewards C_star C_h control0 z.val q rho P hcover hb hclearz
  rw [ht, hsz] at hA
  have hrecord : r = nativeRecord rate rewards C_star C_h q z :=
    Option.some.inj (hr.symm.trans (nativeSourceCell_spec rate rewards C_star C_h q z).1)
  subst r
  have hselEq : sel = (nativeSourceCell rate rewards C_star C_h q z).selected :=
    Option.some.inj (hsel.symm.trans (nativeSourceCell rate rewards C_star C_h q z).selection_actual)
  subst sel
  exact ⟨hpend, A, hA, hS, hanchor.trans hPA⟩

local notation "G" => fun (s q : Fin p.T) (h : History rate s q) =>
  Prod.fst (Prod.fst h) ∈ sourceStartEvent rate rewards C_star C_h s ∧
    h ∈ sourceHistoryRetained rate rewards C_star C_h s q

include control0 in
private theorem measurableSet_good_history (s q : Fin p.T) :
    MeasurableSet {h : History rate s q | G s q h} :=
  ((measurableSet_sourceStartEvent rate rewards C_star C_h control0 s).preimage
    measurable_fst.fst).inter (measurableSet_sourceHistoryRetained rate rewards C_star C_h s q)

private def slowFromPast (q : Fin p.T) (a : Past × Vector) : Option (SlowSet p) :=
  (viewFromPast rate rewards C_star C_h control0 q a).map (fun v => v.payload.slowSet)

private theorem measurable_slowFromPast (q : Fin p.T) :
    Measurable (slowFromPast rate rewards C_star C_h control0 q) := by
  have hp : Measurable (fun v : ReferenceDownReception.ChoiceTimeView p rate.eta => v.payload) :=
    (comap_measurable ReferenceDownReceptionMeasurability.choiceTimeViewObservation).fst
  have ho := (comap_measurable (LaterAssignmentStartMeasurability.payloadObservation
    (p := p) (eta := rate.eta))).comp hp
  have hu : Measurable (fun v : ReferenceDownReception.ChoiceTimeView p rate.eta => v.payload.slowSet) :=
    ho.snd.snd.fst.subtype_mk
  exact LaterAssignmentFullOutputMeasurability.measurable_optionMap _ hu _
    (measurable_viewFromPast rate rewards C_star C_h control0 q)

omit rate rewards C_star C_h control0 b0 u0 t0 in
private theorem measurable_optional {A X Y : Type*} [MeasurableSpace A]
    [MeasurableSpace X] [MeasurableSpace Y] [Zero Y]
    (f : A × X → Y) (hf : Measurable f) :
    Measurable (fun v : Option A × X => v.1.elim 0 (fun a => f (a, v.2))) := by
  have h := (hf.sumElim (measurable_const : Measurable (fun _ : PUnit × X => (0 : Y)))).comp
    (MeasurableEquiv.sumProdDistrib A PUnit X).measurable_toFun
  have hp := h.comp (((comap_measurable (Equiv.optionEquivSumPUnit A)).comp
    measurable_fst).prodMk measurable_snd)
  convert hp using 1
  funext v
  rcases v with ⟨a, x⟩
  cases a <;> rfl

private def callActualTest (s q : Fin p.T)
    (Phi : History rate s q × (SlowSet p × Fin p.K) → ℝ≥0∞)
    (x : (Past × Vector) × Pair) : ℝ≥0∞ :=
  let h := historyFromPast rate control0 s q x.1.1
  if G s q h then (slowFromPast rate rewards C_star C_h control0 q x.1).elim 0
    (fun U => x.2.2.elim 0 (fun j => Phi (h, (U, j)))) else 0

private def callMeanTest (s q : Fin p.T)
    (Phi : History rate s q × (SlowSet p × Fin p.K) → ℝ≥0∞)
    (x : (Past × Vector) × Pair) : ℝ≥0∞ :=
  let h := historyFromPast rate control0 s q x.1.1
  if G s q h then (slowFromPast rate rewards C_star C_h control0 q x.1).elim 0
    (fun U => ReferenceGeneratedCalendarRetainedFastCore.historyFastTest
      rate rewards C_star C_h s q Phi h U) else 0

private theorem measurable_callActualTest (s q : Fin p.T)
    (Phi : History rate s q × (SlowSet p × Fin p.K) → ℝ≥0∞) (hPhi : Measurable Phi) :
    Measurable (callActualTest rate rewards C_star C_h control0 s q Phi) := by
  have hj : Measurable (fun x : Option (Fin p.K) × (History rate s q × SlowSet p) =>
      x.1.elim 0 (fun j => Phi (x.2.1, (x.2.2, j)))) := by
    apply measurable_from_prod_countable_right
    intro j
    cases j with
    | none => exact measurable_const
    | some j => exact hPhi.comp (measurable_fst.prodMk (measurable_snd.prodMk measurable_const))
  have hU := measurable_optional
    (fun x : SlowSet p × (History rate s q × Option (Fin p.K)) =>
      x.2.2.elim 0 (fun j => Phi (x.2.1, (x.1, j))))
    (hj.comp (measurable_snd.snd.prodMk (measurable_snd.fst.prodMk measurable_fst)))
  have hh : Measurable (fun x : (Past × Vector) × Pair =>
      historyFromPast rate control0 s q x.1.1) :=
    (measurable_historyFromPast rate control0 s q).comp measurable_fst.fst
  exact (hU.comp (((measurable_slowFromPast rate rewards C_star C_h control0 q).comp
    measurable_fst).prodMk (hh.prodMk measurable_snd.snd))).ite
      ((measurableSet_good_history rate rewards C_star C_h control0 s q).preimage hh) measurable_const

private theorem measurable_callMeanTest (s q : Fin p.T)
    (Phi : History rate s q × (SlowSet p × Fin p.K) → ℝ≥0∞) (hPhi : Measurable Phi) :
    Measurable (callMeanTest rate rewards C_star C_h control0 s q Phi) := by
  have hU := measurable_optional
    (fun x : SlowSet p × History rate s q =>
      ReferenceGeneratedCalendarRetainedFastCore.historyFastTest rate rewards C_star C_h s q Phi x.2 x.1)
    ((ReferenceGeneratedCalendarRetainedFastCore.measurable_historyFastTest
      rate rewards C_star C_h s q Phi hPhi).comp (measurable_snd.prodMk measurable_fst))
  have hh : Measurable (fun x : (Past × Vector) × Pair =>
      historyFromPast rate control0 s q x.1.1) :=
    (measurable_historyFromPast rate control0 s q).comp measurable_fst.fst
  exact (hU.comp (((measurable_slowFromPast rate rewards C_star C_h control0 q).comp
    measurable_fst).prodMk hh)).ite
      ((measurableSet_good_history rate rewards C_star C_h control0 s q).preimage hh) measurable_const

omit rate rewards C_star C_h control0 b0 u0 t0 in
private theorem lintegral_fast_second_marginal (U : SlowSet p) (K : Measure Pair)
    (P : PMF (FastArm U))
    (hm : K.map Prod.snd = P.toMeasure.map (fun j => some j.val))
    (f : Fin p.K → ℝ≥0∞) :
    (∫⁻ y, y.2.elim 0 f ∂K) = ∑ j : FastArm U, f j.val * P j := by
  let g : Option (Fin p.K) → ℝ≥0∞ := fun j => j.elim 0 f
  have hg : Measurable g := measurable_of_finite _
  calc
    _ = ∫⁻ j, g j ∂K.map Prod.snd := (lintegral_map hg measurable_snd).symm
    _ = ∫⁻ j, g (some j.val) ∂P.toMeasure := by
      rw [hm, lintegral_map hg (measurable_of_finite (fun j : FastArm U => some j.val))]
    _ = _ := by
      rw [lintegral_fintype]
      apply Finset.sum_congr rfl
      intro j _hj
      rw [PMF.toMeasure_apply_singleton _ j (measurableSet_singleton j)]
      rfl

omit rewards C_star C_h control0 b0 u0 t0 in
private theorem collectionFastPMF_eq_numerical (A S : RecordedQueueRun.RunState p.K)
    (anchor : Fin p.K → ℝ) (ha : ∀ i, 0 < anchor i)
    (hanchor : anchor = scoreWeight Q A) (U : SlowSet p) :
    ReferencePostInvocationCollectionNativeLaw.collectionFastPMF rate anchor (scoreWeight Q S)
      ha (RecordedSlowRefresh.scoreWeight_pos Q S) U =
        ReferenceGeneratedCalendarRetainedFastCore.numericalFastPMF rate A S U := by
  subst anchor
  rfl

omit control0 b0 u0 t0 in
private theorem historyFastTest_eq_sum (s q : Fin p.T)
    (Phi : History rate s q × (SlowSet p × Fin p.K) → ℝ≥0∞)
    (h : History rate s q) (U : SlowSet p) (A S : RecordedQueueRun.RunState p.K)
    (hA : prefixNumerical rate rewards C_star C_h s.castSucc h.1.1 = some A)
    (hS : sourceEpisodeReplay rate rewards C_star C_h s q h = some S) :
    ReferenceGeneratedCalendarRetainedFastCore.historyFastTest rate rewards C_star C_h s q Phi h U =
      ∑ j : FastArm U, Phi (h, (U, j.val)) *
        ReferenceGeneratedCalendarRetainedFastCore.numericalFastPMF rate A S U j := by
  rw [ReferenceGeneratedCalendarRetainedFastCore.historyFastTest, hA, hS]

private theorem call_kernel_test (s : Fin p.T) (k : ℕ)
    (hk : t0.val + 1 + k < p.T) (hs : s.val ≤ t0.val + 1 + k)
    (w : Sample k) (v : Vector) (hc : call k (by omega) w = true)
    (hclear : (pending k (by omega) w).2 = true)
    (Phi : History rate s ⟨t0.val + 1 + k, hk⟩ × (SlowSet p × Fin p.K) → ℝ≥0∞) :
    let q : Fin p.T := ⟨t0.val + 1 + k, hk⟩
    let K := calendarRecorderFastKernel rate rewards C_star C_h control0 q (past k hk.le w) v
    (∫⁻ y, callActualTest rate rewards C_star C_h control0 s q Phi ((past k hk.le w, v), y) ∂K) =
      ∫⁻ y, callMeanTest rate rewards C_star C_h control0 s q Phi ((past k hk.le w, v), y) ∂K := by
  dsimp only
  let q : Fin p.T := ⟨t0.val + 1 + k, hk⟩
  let z := calendarInvocationSource rate rewards C_star C_h control0 b0 u0 t0 k hk w v hc
  let view := (nativeSourceCell rate rewards C_star C_h q z).selected.view
  let h := history s q k hk.le w
  let K := calendarRecorderFastKernel rate rewards C_star C_h control0 q (past k hk.le w) v
  have hh := historyFromPast_calendar rate rewards C_star C_h control0 b0 u0 t0 s q hs k hk.le rfl w
  have hv := viewFromPast_calendar rate rewards C_star C_h control0 b0 u0 t0 k hk w v hc
  have hslow : slowFromPast rate rewards C_star C_h control0 q (past k hk.le w, v) =
      some view.payload.slowSet := by
    rw [slowFromPast, hv]
    rfl
  change (∫⁻ y : Pair, if G s q (historyFromPast rate control0 s q (past k hk.le w)) then
    (slowFromPast rate rewards C_star C_h control0 q (past k hk.le w, v)).elim 0
      (fun U => y.2.elim 0 (fun j => Phi (historyFromPast rate control0 s q (past k hk.le w), (U, j))))
    else 0 ∂K) = ∫⁻ _ : Pair, if G s q (historyFromPast rate control0 s q (past k hk.le w)) then
      (slowFromPast rate rewards C_star C_h control0 q (past k hk.le w, v)).elim 0
        (fun U => ReferenceGeneratedCalendarRetainedFastCore.historyFastTest rate rewards C_star C_h s q Phi
          (historyFromPast rate control0 s q (past k hk.le w)) U) else 0 ∂K
  by_cases hg : G s q (historyFromPast rate control0 s q (past k hk.le w))
  · simp_rw [ite_eq_left hg, hslow, Option.elim_some, hh]
    have hG : G s q h := (congrArg (fun x => G s q x) hh).mp hg
    obtain ⟨_hclear, A, hA, hS, hanchor⟩ := call_history_parameters
      rate rewards C_star C_h control0 b0 u0 t0 s k hk hs w v hc hG.1 hG.2
    have : IsProbabilityMeasure K := by
      dsimp only [K, calendarRecorderFastKernel]
      infer_instance
    have hm := ReferenceGeneratedCalendarRetainedFastCore.calendar_call_fast_marginal
      rate rewards C_star C_h control0 b0 u0 t0 k hk w v hc hclear
    have hpmf := collectionFastPMF_eq_numerical rate A
      (nativeBefore rate rewards C_star C_h control0 q z) view.payload.anchor view.payload.anchor_pos
      hanchor view.payload.slowSet
    have hmean := historyFastTest_eq_sum rate rewards C_star C_h s q Phi h view.payload.slowSet A
      (nativeBefore rate rewards C_star C_h control0 q z) hA hS
    rw [lintegral_const, measure_univ, mul_one]
    exact (lintegral_fast_second_marginal view.payload.slowSet K _ hm
      (fun j => Phi (h, (view.payload.slowSet, j)))).trans
        ((congrArg (fun P : PMF (FastArm view.payload.slowSet) =>
          ∑ j : FastArm view.payload.slowSet, Phi (h, (view.payload.slowSet, j.val)) * P j) hpmf).trans hmean.symm)
  · simp_rw [ite_eq_right hg]

private theorem call_test_readouts (s : Fin p.T) (k : ℕ)
    (hk : t0.val + 1 + k < p.T) (hs : s.val ≤ t0.val + 1 + k)
    (w : Sample k) (v : Vector) (hc : call k (by omega) w = true)
    (hclear : (pending k (by omega) w).2 = true)
    (Phi : History rate s ⟨t0.val + 1 + k, hk⟩ × (SlowSet p × Fin p.K) → ℝ≥0∞) :
    let q : Fin p.T := ⟨t0.val + 1 + k, hk⟩
    let h := history s q k hk.le w
    let e := calendarStepCell rate rewards C_star C_h control0 b0 u0 t0 k hk w v
    let y := ReferenceRankInstallationRecorderFastLaw.actualMarkerReservedFast rate rewards C_star C_h q
      (current (k + 1) (by omega) (w, v))
    callActualTest rate rewards C_star C_h control0 s q Phi ((past k hk.le w, v), y) =
      (if G s q h then e.elim 0 (fun c => Phi (h, (c.slowSet, c.fastArm))) else 0) ∧
    callMeanTest rate rewards C_star C_h control0 s q Phi ((past k hk.le w, v), y) =
      (if G s q h then e.elim 0 (fun c => ReferenceGeneratedCalendarRetainedFastCore.historyFastTest
        rate rewards C_star C_h s q Phi h c.slowSet) else 0) := by
  dsimp only
  let q : Fin p.T := ⟨t0.val + 1 + k, hk⟩
  let z := calendarInvocationSource rate rewards C_star C_h control0 b0 u0 t0 k hk w v hc
  let c := calendarInvocationCell rate rewards C_star C_h control0 b0 u0 t0 k hk w v hc
  have he : calendarStepCell rate rewards C_star C_h control0 b0 u0 t0 k hk w v = some c := by
    rw [calendarStepCell, dite_eq_left hc]
  have hsource : current (k + 1) (by omega) (w, v) = z.val := by
    rw [calendarCurrentSource_succ rate rewards C_star C_h control0 b0 u0 t0 k hk, ite_eq_left hc]
    rfl
  have hr := calendarInvocationCell_recorderFast_readouts
    rate rewards C_star C_h control0 b0 u0 t0 k hk w v hc hclear
  have hslow : slowFromPast rate rewards C_star C_h control0 q (past k hk.le w, v) = some c.slowSet := by
    rw [slowFromPast, viewFromPast_calendar rate rewards C_star C_h control0 b0 u0 t0 k hk w v hc,
      Option.map_some, ← hr.2]
  have hh := historyFromPast_calendar rate rewards C_star C_h control0 b0 u0 t0 s q hs k hk.le rfl w
  constructor
  · change (if G s q (historyFromPast rate control0 s q (past k hk.le w)) then
      (slowFromPast rate rewards C_star C_h control0 q (past k hk.le w, v)).elim 0
        (fun U => (ReferenceRankInstallationRecorderFastLaw.actualMarkerReservedFast rate rewards C_star C_h q
          (current (k + 1) (by omega) (w, v))).2.elim 0
            (fun j => Phi (historyFromPast rate control0 s q (past k hk.le w), (U, j)))) else 0) = _
    rw [hh, hslow, hsource, hr.1, he]
    rfl
  · change (if G s q (historyFromPast rate control0 s q (past k hk.le w)) then
      (slowFromPast rate rewards C_star C_h control0 q (past k hk.le w, v)).elim 0
        (fun U => ReferenceGeneratedCalendarRetainedFastCore.historyFastTest rate rewards C_star C_h s q Phi
          (historyFromPast rate control0 s q (past k hk.le w)) U) else 0) = _
    rw [hh, hslow, he]
    rfl

private theorem call_outer_readouts (s : Fin p.T) (k : ℕ)
    (hk : t0.val + 1 + k < p.T) (hs : s.val ≤ t0.val + 1 + k)
    (wv : Sample k × Vector)
    (Phi : History rate s ⟨t0.val + 1 + k, hk⟩ × (SlowSet p × Fin p.K) → ℝ≥0∞) :
    let q : Fin p.T := ⟨t0.val + 1 + k, hk⟩
    let h := history s q k hk.le wv.1
    let e := calendarStepCell rate rewards C_star C_h control0 b0 u0 t0 k hk wv.1 wv.2
    let y := ReferenceRankInstallationRecorderFastLaw.actualMarkerReservedFast rate rewards C_star C_h q
      (current (k + 1) (by omega) wv)
    ((if wv.1 ∈ calendarActiveEvent rate rewards C_star C_h control0 b0 u0 t0 k hk then
        callActualTest rate rewards C_star C_h control0 s q Phi ((past k hk.le wv.1, wv.2), y) else 0) =
      if call k (by omega) wv.1 = true ∧ G s q h then
        e.elim 0 (fun c => Phi (h, (c.slowSet, c.fastArm))) else 0) ∧
    ((if wv.1 ∈ calendarActiveEvent rate rewards C_star C_h control0 b0 u0 t0 k hk then
        callMeanTest rate rewards C_star C_h control0 s q Phi ((past k hk.le wv.1, wv.2), y) else 0) =
      if call k (by omega) wv.1 = true ∧ G s q h then
        e.elim 0 (fun c => ReferenceGeneratedCalendarRetainedFastCore.historyFastTest
          rate rewards C_star C_h s q Phi h c.slowSet) else 0) := by
  dsimp only
  by_cases ha : wv.1 ∈ calendarActiveEvent rate rewards C_star C_h control0 b0 u0 t0 k hk
  · have hr := call_test_readouts rate rewards C_star C_h control0 b0 u0 t0 s k hk hs
      wv.1 wv.2 ha.1 ha.2 Phi
    simpa only [ite_eq_left ha, ha.1, true_and] using hr
  · have hbad : ¬ (call k (by omega) wv.1 = true ∧
        G s ⟨t0.val + 1 + k, hk⟩ (history s ⟨t0.val + 1 + k, hk⟩ k hk.le wv.1)) := by
      intro hg
      exact ha ⟨hg.1, (call_history_parameters rate rewards C_star C_h control0 b0 u0 t0
        s k hk hs wv.1 wv.2 hg.1 hg.2.1 hg.2.2).1⟩
    simp only [ite_eq_right ha, ite_eq_right hbad, and_self]

private theorem calendar_call_fast_test_raw (s : Fin p.T) (k : ℕ)
    (hk : t0.val + 1 + k < p.T) (hs : s.val ≤ t0.val + 1 + k)
    (Phi : History rate s ⟨t0.val + 1 + k, hk⟩ × (SlowSet p × Fin p.K) → ℝ≥0∞)
    (hPhi : Measurable Phi) :
    let q : Fin p.T := ⟨t0.val + 1 + k, hk⟩
    (∫⁻ wv : Sample k × Vector,
      if call k (by omega) wv.1 = true ∧ G s q (history s q k hk.le wv.1) then
        (calendarStepCell rate rewards C_star C_h control0 b0 u0 t0 k hk wv.1 wv.2).elim 0
          (fun e => Phi (history s q k hk.le wv.1, (e.slowSet, e.fastArm))) else 0
      ∂law (k + 1) (by omega)) =
    ∫⁻ wv : Sample k × Vector,
      if call k (by omega) wv.1 = true ∧ G s q (history s q k hk.le wv.1) then
        (calendarStepCell rate rewards C_star C_h control0 b0 u0 t0 k hk wv.1 wv.2).elim 0
          (fun e => ReferenceGeneratedCalendarRetainedFastCore.historyFastTest
            rate rewards C_star C_h s q Phi (history s q k hk.le wv.1) e.slowSet) else 0
      ∂law (k + 1) (by omega) := by
  dsimp only
  let q : Fin p.T := ⟨t0.val + 1 + k, hk⟩
  let A := callActualTest rate rewards C_star C_h control0 s q Phi
  let M := callMeanTest rate rewards C_star C_h control0 s q Phi
  have hslow : (slowSetMeasurableSpace : MeasurableSpace (SlowSet p)) = ⊤ :=
    top_unique (fun E _ => (Set.to_countable E).measurableSet)
  have hA := calendarLaw_call_recorderFast_test rate rewards C_star C_h control0 b0 u0 t0 k hk A
    (by
      convert measurable_callActualTest rate rewards C_star C_h control0 s q Phi hPhi using 1
      congr 4
      exact hslow.symm)
  have hM := calendarLaw_call_recorderFast_test rate rewards C_star C_h control0 b0 u0 t0 k hk M
    (by
      convert measurable_callMeanTest rate rewards C_star C_h control0 s q Phi hPhi using 1
      congr 4
      exact hslow.symm)
  have hinner :
      (∫⁻ w, if w ∈ calendarActiveEvent rate rewards C_star C_h control0 b0 u0 t0 k hk then
        ∫⁻ a, ∫⁻ v, ∫⁻ y, A ((past k hk.le w, v), y)
          ∂calendarRecorderFastKernel rate rewards C_star C_h control0 q (past k hk.le w) v
          ∂calendarExtensionKernel rate rewards C_star C_h control0 b0 u0 t0 k (by omega)
            (calendarFillPair rate rewards C_star C_h b0 u0 t0 q k (w, a))
          ∂ReferencePostInvocationKilledJointLaw.auxiliaryPairLaw else 0
        ∂(law k hk.le).map (calendarEraseInnovation rate rewards C_star C_h control0 b0 u0 t0 q
          (by change t0.val < t0.val + 1 + k; omega) k)) =
      ∫⁻ w, if w ∈ calendarActiveEvent rate rewards C_star C_h control0 b0 u0 t0 k hk then
        ∫⁻ a, ∫⁻ v, ∫⁻ y, M ((past k hk.le w, v), y)
          ∂calendarRecorderFastKernel rate rewards C_star C_h control0 q (past k hk.le w) v
          ∂calendarExtensionKernel rate rewards C_star C_h control0 b0 u0 t0 k (by omega)
            (calendarFillPair rate rewards C_star C_h b0 u0 t0 q k (w, a))
          ∂ReferencePostInvocationKilledJointLaw.auxiliaryPairLaw else 0
        ∂(law k hk.le).map (calendarEraseInnovation rate rewards C_star C_h control0 b0 u0 t0 q
          (by change t0.val < t0.val + 1 + k; omega) k) := by
    apply lintegral_congr
    intro w
    by_cases hw : w ∈ calendarActiveEvent rate rewards C_star C_h control0 b0 u0 t0 k hk
    · rw [ite_eq_left hw, ite_eq_left hw]
      apply lintegral_congr
      intro a
      apply lintegral_congr
      intro v
      exact call_kernel_test rate rewards C_star C_h control0 b0 u0 t0 s k hk hs w v hw.1 hw.2 Phi
    · rw [ite_eq_right hw, ite_eq_right hw]
  have hAM := hA.trans (hinner.trans hM.symm)
  refine Eq.trans ?_ (hAM.trans ?_)
  · apply lintegral_congr
    intro wv
    exact (call_outer_readouts rate rewards C_star C_h control0 b0 u0 t0 s k hk hs wv Phi).1.symm
  · apply lintegral_congr
    intro wv
    exact (call_outer_readouts rate rewards C_star C_h control0 b0 u0 t0 s k hk hs wv Phi).2

private theorem historyFastTest_indicator_source (s q : Fin p.T) (E : Set Source)
    (Phi : History rate s q × (SlowSet p × Fin p.K) → ℝ≥0∞)
    (h : History rate s q) (U : SlowSet p) :
    ReferenceGeneratedCalendarRetainedFastCore.historyFastTest rate rewards C_star C_h s q
        (fun x => if x.1.1.1 ∈ E then Phi x else 0) h U =
      if h.1.1 ∈ E then
        ReferenceGeneratedCalendarRetainedFastCore.historyFastTest rate rewards C_star C_h s q Phi h U else 0 := by
  unfold ReferenceGeneratedCalendarRetainedFastCore.historyFastTest
  split <;> by_cases hi : h.1.1 ∈ E <;>
    simp only [hi, ite_true, ite_false, zero_mul, Finset.sum_const_zero]

omit rate rewards C_star C_h control0 b0 u0 t0 in
private theorem option_gated_indicator {A : Type*} (P R : Prop) [Decidable P] [Decidable R]
    (c : Option A) (f : A → ℝ≥0∞) :
    (if P then if R then c.elim 0 f else 0 else 0) =
      if R then c.elim 0 (fun a => if P then f a else 0) else 0 := by
  split_ifs <;> cases c <;> rfl

private theorem step_source_ids (s : Fin p.T) (k : ℕ)
    (hk : t0.val + 1 + k < p.T) (wv : Sample k × Vector) :
    (current (k + 1) (by omega) wv).1.1 =
      (history s ⟨t0.val + 1 + k, hk⟩ k hk.le wv.1).1.1.1.1 := by
  change (current (k + 1) (by omega) wv).1.1 = (current k hk.le wv.1).1.1
  rw [calendarCurrentSource_succ rate rewards C_star C_h control0 b0 u0 t0 k hk]
  split <;> rfl

/-- FAST evaluation on actual later CALLs, under the raw calendar law and
every original fixed-ID unnormalized law. The source opportunity and incoming
retention gates produce the clear PRE, strict seed and operative anchor inside
the proof. The entire assignment vector remains in the original carrier. -/
theorem calendar_call_fast_test (ids : Option (CompletePublicTable.IDArray p))
    (b0 : Bool) (u0 t0 s : Fin p.T) (k : ℕ)
    (hk : t0.val + 1 + k < p.T) (hs : s.val ≤ t0.val + 1 + k)
    (Phi : History rate s ⟨t0.val + 1 + k, hk⟩ × (SlowSet p × Fin p.K) → ℝ≥0∞)
    (hPhi : Measurable Phi) :
    let q : Fin p.T := ⟨t0.val + 1 + k, hk⟩
    let gamma : Measure (CalendarSample rate rewards C_star C_h b0 u0 t0 k × Vector) := ids.elim (calendarLaw rate rewards C_star C_h control0 b0 u0 t0 (k + 1) (by omega))
      (fun id => (CompletePublicTable.idArrayMeasure p {id})⁻¹ •
        (calendarLaw rate rewards C_star C_h control0 b0 u0 t0 (k + 1) (by omega)).restrict
          ((calendarCurrentSource rate rewards C_star C_h control0 b0 u0 t0 (k + 1) (by omega)) ⁻¹'
            ReferenceFixedIDSourceSection.fixedIDSourceSection id))
    (∫⁻ wv : CalendarSample rate rewards C_star C_h b0 u0 t0 k × Vector,
      if calendarCallFlag rate rewards C_star C_h control0 b0 u0 t0 k (by omega) wv.1 = true ∧
          G s q (calendarSourceHistory rate rewards C_star C_h control0 b0 u0 t0 s q k hk.le wv.1) then
        (calendarStepCell rate rewards C_star C_h control0 b0 u0 t0 k hk wv.1 wv.2).elim 0
          (fun e => Phi (calendarSourceHistory rate rewards C_star C_h control0 b0 u0 t0 s q k hk.le wv.1,
            (e.slowSet, e.fastArm))) else 0 ∂gamma) =
    ∫⁻ wv : CalendarSample rate rewards C_star C_h b0 u0 t0 k × Vector,
      if calendarCallFlag rate rewards C_star C_h control0 b0 u0 t0 k (by omega) wv.1 = true ∧
          G s q (calendarSourceHistory rate rewards C_star C_h control0 b0 u0 t0 s q k hk.le wv.1) then
        (calendarStepCell rate rewards C_star C_h control0 b0 u0 t0 k hk wv.1 wv.2).elim 0
          (fun e => ReferenceGeneratedCalendarRetainedFastCore.historyFastTest rate rewards C_star C_h s q Phi
            (calendarSourceHistory rate rewards C_star C_h control0 b0 u0 t0 s q k hk.le wv.1) e.slowSet)
        else 0 ∂gamma := by
  dsimp only
  cases ids with
  | none => exact calendar_call_fast_test_raw rate rewards C_star C_h control0 b0 u0 t0 s k hk hs Phi hPhi
  | some id =>
    let q : Fin p.T := ⟨t0.val + 1 + k, hk⟩
    let E : Set Source := ReferenceFixedIDSourceSection.fixedIDSourceSection id
    let PhiID : History rate s q × (SlowSet p × Fin p.K) → ℝ≥0∞ :=
      fun x => if x.1.1.1 ∈ E then Phi x else 0
    have hPhiID : Measurable PhiID := hPhi.ite
      ((ReferenceFixedIDSourceSection.measurable_fixedIDSourceSection id).preimage
        measurable_fst.fst.fst) measurable_const
    let mu : Measure (CalendarSample rate rewards C_star C_h b0 u0 t0 k × Vector) :=
      calendarLaw rate rewards C_star C_h control0 b0 u0 t0 (k + 1) (by omega)
    let J : Set (CalendarSample rate rewards C_star C_h b0 u0 t0 k × Vector) :=
      (calendarCurrentSource rate rewards C_star C_h control0 b0 u0 t0 (k + 1) (by omega)) ⁻¹' E
    let H : CalendarSample rate rewards C_star C_h b0 u0 t0 k × Vector → History rate s q :=
      fun wv => calendarSourceHistory rate rewards C_star C_h control0 b0 u0 t0 s q k hk.le wv.1
    let C : CalendarSample rate rewards C_star C_h b0 u0 t0 k × Vector → Option (LogicalCell p rate) :=
      fun wv => calendarStepCell rate rewards C_star C_h control0 b0 u0 t0 k hk wv.1 wv.2
    let B : CalendarSample rate rewards C_star C_h b0 u0 t0 k × Vector → Bool :=
      fun wv => calendarCallFlag rate rewards C_star C_h control0 b0 u0 t0 k (by omega) wv.1
    let actual := fun (Psi : History rate s q × (SlowSet p × Fin p.K) → ℝ≥0∞)
        (wv : CalendarSample rate rewards C_star C_h b0 u0 t0 k × Vector) =>
      if B wv = true ∧ G s q (H wv) then
        (C wv).elim 0 (fun e => Psi (H wv, (e.slowSet, e.fastArm))) else 0
    let mean := fun (Psi : History rate s q × (SlowSet p × Fin p.K) → ℝ≥0∞)
        (wv : CalendarSample rate rewards C_star C_h b0 u0 t0 k × Vector) =>
      if B wv = true ∧ G s q (H wv) then
        (C wv).elim 0 (fun e => ReferenceGeneratedCalendarRetainedFastCore.historyFastTest
          rate rewards C_star C_h s q Psi (H wv) e.slowSet) else 0
    have hraw : (∫⁻ wv, actual PhiID wv ∂mu) = ∫⁻ wv, mean PhiID wv ∂mu :=
      calendar_call_fast_test_raw rate rewards C_star C_h control0 b0 u0 t0 s k hk hs PhiID hPhiID
    have hE : MeasurableSet J :=
      (ReferenceFixedIDSourceSection.measurable_fixedIDSourceSection id).preimage
        (measurable_calendarCurrentSource rate rewards C_star C_h control0 b0 u0 t0 (k + 1) (by omega))
    have hids (wv : CalendarSample rate rewards C_star C_h b0 u0 t0 k × Vector) :
        wv ∈ J ↔ (H wv).1.1 ∈ E := by
      change (calendarCurrentSource rate rewards C_star C_h control0 b0 u0 t0 (k + 1) (by omega) wv).1.1 = id ↔
        (calendarSourceHistory rate rewards C_star C_h control0 b0 u0 t0 s q k hk.le wv.1).1.1.1.1 = id
      rw [step_source_ids rate rewards C_star C_h control0 b0 u0 t0 s k hk wv]
    have hL : J.indicator (actual Phi) = actual PhiID := by
      funext wv
      change (if wv ∈ J then
        (if B wv = true ∧ G s q (H wv) then
          (C wv).elim 0 (fun e => Phi (H wv, (e.slowSet, e.fastArm))) else 0) else 0) =
        if B wv = true ∧ G s q (H wv) then
          (C wv).elim 0 (fun e => if (H wv).1.1 ∈ E then Phi (H wv, (e.slowSet, e.fastArm)) else 0) else 0
      rw [propext (hids wv)]
      exact option_gated_indicator _ _ _ _
    have hM : J.indicator (mean Phi) = mean PhiID := by
      funext wv
      change (if wv ∈ J then
        (if B wv = true ∧ G s q (H wv) then
          (C wv).elim 0 (fun e => ReferenceGeneratedCalendarRetainedFastCore.historyFastTest
            rate rewards C_star C_h s q Phi (H wv) e.slowSet) else 0) else 0) =
        if B wv = true ∧ G s q (H wv) then
          (C wv).elim 0 (fun e => ReferenceGeneratedCalendarRetainedFastCore.historyFastTest
            rate rewards C_star C_h s q PhiID (H wv) e.slowSet) else 0
      rw [propext (hids wv)]
      have hf : (fun e : LogicalCell p rate =>
          ReferenceGeneratedCalendarRetainedFastCore.historyFastTest rate rewards C_star C_h s q PhiID (H wv) e.slowSet) =
          fun e => if (H wv).1.1 ∈ E then
            ReferenceGeneratedCalendarRetainedFastCore.historyFastTest rate rewards C_star C_h s q Phi (H wv) e.slowSet else 0 :=
        funext fun e => historyFastTest_indicator_source rate rewards C_star C_h s q E Phi (H wv) e.slowSet
      exact (option_gated_indicator ((H wv).1.1 ∈ E) (B wv = true ∧ G s q (H wv)) (C wv)
        (fun e => ReferenceGeneratedCalendarRetainedFastCore.historyFastTest rate rewards C_star C_h s q Phi
          (H wv) e.slowSet)).trans
            (congrArg (fun f : LogicalCell p rate → ℝ≥0∞ =>
              if B wv = true ∧ G s q (H wv) then (C wv).elim 0 f else 0) hf).symm
    have hfixed :
        (∫⁻ wv, actual Phi wv ∂(CompletePublicTable.idArrayMeasure p {id})⁻¹ • mu.restrict J) =
          ∫⁻ wv, mean Phi wv ∂(CompletePublicTable.idArrayMeasure p {id})⁻¹ • mu.restrict J := by
      rw [lintegral_smul_measure, lintegral_smul_measure]
      apply congrArg (fun a : ℝ≥0∞ => (CompletePublicTable.idArrayMeasure p {id})⁻¹ * a)
      rw [← lintegral_indicator hE, ← lintegral_indicator hE, hL, hM]
      exact hraw
    exact hfixed

end Bandits.Support.ReferenceGeneratedCalendarLaterCallFast
