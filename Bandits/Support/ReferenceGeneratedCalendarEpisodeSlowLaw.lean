/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedCalendarEpisodePrefixRecombination
public import Bandits.Support.ReferenceGeneratedCalendarRoundLaw
public import Bandits.Support.ReferenceGeneratedCalendarLaunchSlowInitialization
public import Bandits.Support.ReferenceGeneratedCalendarLaterRenewalSlowInitialization
public import Bandits.Support.ReferenceOriginalCalendarEpisodeChronology

import Mathlib.Tactic

/-!
# Actual episode histories, numerical replay, and first-renewal initialization

Sources: ZIP4 `04_slow_fast_learner.tex:176-215,323-390`,
`06_interruptions.tex:391-426`, and `08_main_theorem.tex:78-109`.

The observers below read the existing raw terminal sample. A missing mark has
zero estimate; it does not acquire a numerical state. The estimate uses the
incoming overflow flag, so the first detecting UPDATE is included. Continuous
reward and rate coordinates retain their original Borel spaces.

The first-renewal initializer is mined from the preserved unaccepted parent.
The single start/estimate-history schema now reconstructs every actual episode
PRE and its fixed-anchor mass, with actual original-record coverage and a
retained-event history version. Initialization and local innovation laws are
distinct from the open stochastic induction; no manuscript closure is asserted.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal Classical BigOperators
open Bandits.Support ConstructorDimensions
open ReferenceFirstLiveChronologicalPrefixFoundation
open ReferenceFirstLiveChronologicalPrefixMeasurability
open ReferenceSourcePrefixHistoryFiltration (sourcePrefix)

namespace Bandits.Support.ReferenceGeneratedCalendarEpisodeSlowLaw

variable {p : ConstructorDimensions.Parameters}

abbrev Source := BootstrapPrivateRoundStreams.SourceInput
abbrev Estimate (p : ConstructorDimensions.Parameters) := Fin p.K → ℝ

local instance sourceMeasurableSpace : MeasurableSpace (Source p) := by
  change MeasurableSpace (CompletePublicTable.PublishedOutput p ×
    BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

local instance optionMeasurableSpace {A : Type*} [MeasurableSpace A] :
    MeasurableSpace (Option A) := LaterAssignmentStartMeasurability.optionMeasurableSpace

local instance slowSetMeasurableSpace : MeasurableSpace (SlowSet p) := Subtype.instMeasurableSpace
local instance slowSetDiscrete : DiscreteMeasurableSpace (SlowSet p) := by infer_instance

attribute [local instance] ReferenceRankInstallationPostUpdateProposalLaw.listMeasurableSingleton
  ReferenceRankInstallationPostUpdateProposalLaw.sumMeasurableSingleton

local instance optionSingleton {A : Type*} [MeasurableSpace A]
    [MeasurableSingletonClass A] : MeasurableSingletonClass (Option A) where
  measurableSet_singleton a := by
    have h := (comap_measurable (Equiv.optionEquivSumPUnit A))
      (measurableSet_singleton ((Equiv.optionEquivSumPUnit A) a))
    convert h using 1
    ext b
    simp only [Set.mem_singleton_iff, Set.mem_preimage]
    exact (Equiv.optionEquivSumPUnit A).injective.eq_iff.symm

variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
  (control0 : ContinuousLearningRows.TimeControl p)

local notation "Omega" => ReferenceExhaustiveGeneratedCalendarSourceLaw.Omega rate rewards C_star C_h
local notation "Z" => ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalSource rate rewards C_star C_h control0
local notation "Q" => ReferenceFirstLaunchNumericalCell.queueParameters rate

/-- The literal terminal archive, with no branch tag or new source. -/
def archive (w : Omega) : List (LogicalCell p rate) :=
  (ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalReadout rate rewards C_star C_h control0 w).2.2

theorem measurable_archive : Measurable (archive rate rewards C_star C_h control0) :=
  (ReferenceExhaustiveGeneratedCalendarSourceLaw.measurable_terminalReadout
    rate rewards C_star C_h control0).snd.snd

private theorem measurable_list_getElem? {A : Type*} [MeasurableSpace A] (k : ℕ) :
    Measurable (fun L : List A => L[k]?) := by
  have htag : Measurable (fun L : List A =>
      ReferenceActiveHorizonMeasurability.listObservationAt L k) :=
    (measurable_pi_apply k).comp
      ReferenceActiveHorizonMeasurability.measurable_listObservationCoordinates.snd
  have hdecode : Measurable (Sum.elim (fun _ : Unit => (none : Option A)) some) :=
    measurable_fun_sum measurable_const
      (LaterAssignmentFullOutputMeasurability.measurable_some_of_measurable _ measurable_id)
  convert hdecode.comp htag using 1
  funext L
  simp only [Function.comp_apply, ReferenceActiveHorizonMeasurability.listObservationAt]
  cases L[k]? <;> rfl

private theorem measurable_find_time (q : Fin p.T) :
    Measurable (fun H : List (LogicalCell p rate) => H.find? (fun e => e.time == q)) := by
  have ht : Measurable (fun H : List (LogicalCell p rate) => H.map LogicalCell.time) :=
    ReferenceActiveHorizonMeasurability.measurable_list_map id measurable_id _
      measurable_logicalCell_time
  have hn : Measurable (fun H : List (LogicalCell p rate) =>
      (H.map LogicalCell.time).findIdx (fun t => t == q)) :=
    (measurable_of_countable (fun L : List (Fin p.T) => L.findIdx (fun t => t == q))).comp ht
  have hg : Measurable (fun nH : ℕ × List (LogicalCell p rate) => nH.2[nH.1]?) :=
    measurable_from_prod_countable_right (fun n => measurable_list_getElem? n)
  convert hg.comp (hn.prodMk measurable_id) using 1
  funext H
  simp only [Function.comp_apply, List.find?_eq_getElem?_findIdx, List.findIdx_map, id_eq]
  rfl

/-- The actual optional mark at a physical date. No enabled or success gate is
inserted into the search. -/
def currentMark (q : Fin p.T) (w : Omega) : Option (LogicalCell p rate) :=
  (archive rate rewards C_star C_h control0 w).find? (fun e => e.time == q)

theorem measurable_currentMark (q : Fin p.T) :
    Measurable (currentMark rate rewards C_star C_h control0 q) :=
  (measurable_find_time rate q).comp (measurable_archive rate rewards C_star C_h control0)

private theorem find_time_eq_some (H : List (LogicalCell p rate))
    (hH : H.Pairwise (fun e f => e.time.val < f.time.val))
    (q : Fin p.T) (e : LogicalCell p rate) :
    H.find? (fun f => f.time == q) = some e ↔ e ∈ H ∧ e.time = q := by
  induction H with
  | nil => simp
  | cons f H ih =>
    obtain ⟨hf, hH⟩ := List.pairwise_cons.mp hH
    by_cases hq : f.time = q
    · simp only [List.find?_cons, hq, beq_self_eq_true, Option.some.injEq]
      constructor
      · intro he
        subst e
        exact ⟨List.mem_cons_self, hq⟩
      · rintro ⟨he, het⟩
        rcases List.mem_cons.mp he with he | he
        · exact he.symm
        · have hlt := hf e he
          rw [hq, het] at hlt
          exact (Nat.lt_irrefl _ hlt).elim
    · simp only [List.find?_cons, beq_eq_false_iff_ne.mpr hq]
      rw [ih hH]
      constructor
      · rintro ⟨he, ht⟩
        exact ⟨List.mem_cons_of_mem _ he, ht⟩
      · rintro ⟨he, ht⟩
        rcases List.mem_cons.mp he with he | he
        · exact (hq ((congrArg LogicalCell.time he).symm.trans ht)).elim
        · exact ⟨he, ht⟩

/-- Each present readout is precisely the unique archived cell at that date. -/
theorem currentMark_eq_some_iff (q : Fin p.T) (w : Omega) (e : LogicalCell p rate) :
    currentMark rate rewards C_star C_h control0 q w = some e ↔
      e ∈ archive rate rewards C_star C_h control0 w ∧ e.time = q :=
  find_time_eq_some rate _
    (ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalReadout_chronology
      rate rewards C_star C_h control0 w) q e

/-- Presence is exactly nominal enablement, including after logical overflow. -/
theorem currentMark_isSome_iff (q : Fin p.T) (w : Omega) :
    (currentMark rate rewards C_star C_h control0 q w).isSome = true ↔
      ReferenceExhaustiveGeneratedCalendarSourceLaw.nominalEnabled
        rate rewards C_star C_h q (Z w) = true := by
  rw [Option.isSome_iff_exists]
  simp_rw [currentMark_eq_some_iff]
  exact ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalReadout_enabled_iff
    rate rewards C_star C_h control0 w q

/-- The actual terminal marks and original-record episode intervals have
exactly the same unique calendar partition, without an auxiliary run. -/
theorem currentMark_unique_episode (q : Fin p.T) (w : Omega) :
    (currentMark rate rewards C_star C_h control0 q w).isSome = true ↔
      ∃! rho : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords rate (Z w) rewards C_star C_h).length,
        ReferenceOriginalCalendarEpisodeChronology.EpisodeCovers
          (ReferenceCompletePhysicalHistory.completeSuffixRecords rate (Z w) rewards C_star C_h)[rho.val] q :=
  (currentMark_isSome_iff rate rewards C_star C_h control0 q w).trans
    (ReferenceOriginalCalendarEpisodeChronology.nominalEnabled_iff_unique_episode rate rewards C_star C_h (Z w) q)

/-- The manuscript raw estimate, gated by the actual incoming numerical flag.
Zero rewards reveal no recorder label in this observer. -/
def cellEstimate (e : LogicalCell p rate) (i : Fin p.K) : ℝ :=
  if e.before.overflow then 0 else
    if e.numerical.1 then
      if e.numerical.2.1 = some i then e.numerical.2.2.1 i / e.numerical.2.2.2 i else 0
    else 0

theorem measurable_cellEstimate : Measurable (cellEstimate rate) := by
  apply measurable_pi_iff.mpr
  intro i
  have hn := measurable_logicalCell_numerical (rate := rate)
  have hb : Measurable (fun e : LogicalCell p rate => e.before.overflow) :=
    (measurable_of_countable RecordedQueueRun.RunState.overflow).comp measurable_logicalCell_before
  have hr := (measurable_pi_apply i).comp hn.snd.snd.fst
  have hx := (measurable_pi_apply i).comp hn.snd.snd.snd
  exact measurable_const.ite ((measurableSet_singleton true).preimage hb)
    (((hr.div hx).ite ((measurableSet_singleton (some i)).preimage hn.snd.fst)
      measurable_const).ite ((measurableSet_singleton true).preimage hn.fst) measurable_const)

/-- Absent means zero estimate, without an invented PRE or POST state. -/
def optionalEstimate : Option (LogicalCell p rate) → Estimate p
  | none => 0
  | some e => cellEstimate rate e

theorem measurable_optionalEstimate : Measurable (optionalEstimate rate) := by
  have hm : Measurable (Sum.elim (cellEstimate rate) (fun _ : PUnit => (0 : Estimate p))) :=
    measurable_fun_sum (measurable_cellEstimate rate) measurable_const
  convert hm.comp (comap_measurable (Equiv.optionEquivSumPUnit (LogicalCell p rate))) using 1
  funext e
  cases e <;> rfl

/-- The estimate at an actual calendar date on the SAME raw sample. -/
def estimateAt (q : Fin p.T) (w : Omega) : Estimate p :=
  optionalEstimate rate (currentMark rate rewards C_star C_h control0 q w)

theorem measurable_estimateAt (q : Fin p.T) :
    Measurable (estimateAt rate rewards C_star C_h control0 q) :=
  (measurable_optionalEstimate rate).comp (measurable_currentMark rate rewards C_star C_h control0 q)

/-- The analytical observer before the date-`s` initial draw. It contains only
the selected-row strict source prefix and the strict actual archive. -/
def startHistory (s : Fin p.T) (w : Omega) : Source p × List (LogicalCell p rate) :=
  (sourcePrefix control0 s.val (Z w),
    ReferenceGeneratedCalendarEpisodePrefixRecombination.archiveBefore
      rate rewards C_star C_h control0 s.castSucc w)

theorem measurable_startHistory (s : Fin p.T) :
    Measurable (startHistory rate rewards C_star C_h control0 s) :=
  ReferenceGeneratedCalendarLaterRenewalSlowInitialization.measurable_literal_history
    rate rewards C_star C_h control0 s

/-- Exactly the dates whose estimates precede the tested round in this episode. -/
abbrev EstimateDates (s q : Fin p.T) := {v : Fin p.T // s.val ≤ v.val ∧ v.val < q.val}

/-- Literal estimate-only history. In particular, there is no current slow
set, recorder, FAST, proposal, future tape, or branch tag in the observation. -/
def estimateHistory (s q : Fin p.T) (w : Omega) :
    (Source p × List (LogicalCell p rate)) × (EstimateDates s q → Estimate p) :=
  (startHistory rate rewards C_star C_h control0 s w,
    fun v => estimateAt rate rewards C_star C_h control0 v.val w)

theorem measurable_estimateHistory (s q : Fin p.T) :
    Measurable (estimateHistory rate rewards C_star C_h control0 s q) :=
  (measurable_startHistory rate rewards C_star C_h control0 s).prodMk
    (measurable_pi_iff.mpr fun v => measurable_estimateAt rate rewards C_star C_h control0 v.val)

section EstimateReplay

omit rewards C_star C_h control0 in
/-- The raw estimate on one actual numerical input. Its definition contains no
recorder information beyond the resulting real vector. -/
def inputEstimate (S : RecordedQueueRun.RunState p.K)
    (c : RecordedQueueRun.RoundInput p.K) (i : Fin p.K) : ℝ :=
  if S.overflow then 0 else if c.enabled then
    if c.recordedArm = some i then c.reward i / c.rate i else 0
  else 0

omit rewards C_star C_h control0 in
/-- The queue record reconstructed from PRE and the raw estimate. ENABLED
zero estimates still produce a true record and hence service the old queue. -/
def estimateRecord (S : RecordedQueueRun.RunState p.K) (enabled : Bool)
    (x : Estimate p) (i : Fin p.K) : Bool × ℕ :=
  if S.overflow then (false, 0) else
    if enabled then (true, Nat.floor (((Q).n : ℝ) * x i)) else (false, 0)

omit rewards C_star C_h control0 in
/-- Literal full-state replay, including input histories and absorbing
overflow, from the estimate and the schedule's enabled flag. -/
def estimateStep (S : RecordedQueueRun.RunState p.K) (enabled : Bool) (x : Estimate p) :
    RecordedQueueRun.RunState p.K :=
  let recs := estimateRecord rate S enabled x
  let registers := fun i => QueueReplay.transition (4 * (Q).n) (S.registers i) (recs i)
  ⟨registers, S.overflow || decide (∃ i, 32 * (registers i).2 > (Q).D),
    fun i => S.records i ++ [recs i]⟩

omit rewards C_star C_h control0 in
theorem estimateRecord_inputEstimate (S : RecordedQueueRun.RunState p.K)
    (c : RecordedQueueRun.RoundInput p.K) :
    estimateRecord rate S c.enabled (inputEstimate S c) =
      RecordedQueueRun.acceptedRecord Q S c := by
  funext i
  cases hs : S.overflow <;> cases hen : c.enabled <;>
    simp only [estimateRecord, inputEstimate, RecordedQueueRun.acceptedRecord,
      hs, hen, Bool.false_eq_true, ite_false, ite_true]
  by_cases hi : c.recordedArm = some i
  · simp only [hi, ite_true, RecordedQueueRun.quantizedArrival, mul_div_assoc]
  · simp only [hi, ite_false, RecordedQueueRun.quantizedArrival, mul_zero, Nat.floor_zero]

omit rewards C_star C_h control0 in
/-- Numerical UPDATE factors through the raw estimate, not through its label. -/
theorem estimateStep_inputEstimate (S : RecordedQueueRun.RunState p.K)
    (c : RecordedQueueRun.RoundInput p.K) :
    estimateStep rate S c.enabled (inputEstimate S c) = RecordedQueueRun.step Q S c := by
  unfold estimateStep RecordedQueueRun.step
  rw [estimateRecord_inputEstimate]

omit rewards C_star C_h control0 in
theorem measurable_estimateRecord : Measurable (fun v :
    (RecordedQueueRun.RunState p.K × Bool) × Estimate p => estimateRecord rate v.1.1 v.1.2 v.2) := by
  apply measurable_pi_iff.mpr
  intro i
  have hs : Measurable (fun v : (RecordedQueueRun.RunState p.K × Bool) × Estimate p => v.1.1.overflow) :=
    (measurable_of_countable RecordedQueueRun.RunState.overflow).comp measurable_fst.fst
  have hx : Measurable (fun v : (RecordedQueueRun.RunState p.K × Bool) × Estimate p =>
      Nat.floor (((Q).n : ℝ) * v.2 i)) :=
    Nat.measurable_floor.comp (measurable_const.mul ((measurable_pi_apply i).comp measurable_snd))
  exact measurable_const.ite ((measurableSet_singleton true).preimage hs)
    ((measurable_const.prodMk hx).ite
      ((measurableSet_singleton true).preimage measurable_fst.snd) measurable_const)

omit rewards C_star C_h control0 in
theorem measurable_estimateStep : Measurable (fun v :
    (RecordedQueueRun.RunState p.K × Bool) × Estimate p => estimateStep rate v.1.1 v.1.2 v.2) := by
  let f : RecordedQueueRun.RunState p.K × (Fin p.K → Bool × ℕ) → RecordedQueueRun.RunState p.K :=
    fun v =>
      let registers := fun i => QueueReplay.transition (4 * (Q).n) (v.1.registers i) (v.2 i)
      ⟨registers, v.1.overflow || decide (∃ i, 32 * (registers i).2 > (Q).D),
        fun i => v.1.records i ++ [v.2 i]⟩
  exact (measurable_of_countable f).comp
    (measurable_fst.fst.prodMk (measurable_estimateRecord rate))

omit rewards C_star C_h control0 in
theorem estimateStep_enabled_zero (S : RecordedQueueRun.RunState p.K)
    (hs : S.overflow = false) (i : Fin p.K) :
    (estimateStep rate S true 0).registers i =
      ((S.registers i).1 + min (4 * (Q).n) (S.registers i).2,
        (S.registers i).2 - min (4 * (Q).n) (S.registers i).2) := by
  simp only [estimateStep, estimateRecord, hs, Bool.false_eq_true, ite_false, ite_true,
    Pi.zero_apply, mul_zero, Nat.floor_zero]
  exact QueueReplay.transition_enabled_zero_arrival _ _ _

end EstimateReplay

/-- On both exhaustive laws, the actual archived numerical UPDATE is exactly
the estimate replay. The same physical word supplies PRE, POST, accepted
arrivals and all-arm service. No clear-PRE or successful-sampler premise is
imposed on this result. -/
theorem ae_estimate_numerical_update (ids : Option (CompletePublicTable.IDArray p)) :
    ∀ᵐ w ∂ids.elim
      (ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalLaw rate rewards C_star C_h control0)
      (ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDTerminalLaw rate rewards C_star C_h control0),
      ∀ (q : Fin p.T) (e : LogicalCell p rate),
        currentMark rate rewards C_star C_h control0 q w = some e →
          e.numerical.1 = true ∧
          ReferencePostInvocationNoncallGeometry.prefixNumerical rate rewards C_star C_h q.castSucc (Z w) =
            some e.before ∧
          ReferencePostInvocationNoncallGeometry.prefixNumerical rate rewards C_star C_h q.succ (Z w) =
            some e.after ∧
          e.arrivals = estimateRecord rate e.before true
            (estimateAt rate rewards C_star C_h control0 q w) ∧
          e.after = estimateStep rate e.before true
            (estimateAt rate rewards C_star C_h control0 q w) ∧
          e.service = (fun i => RecordedQueueRun.recordService (4 * (Q).n)
            (e.before.registers i) (estimateRecord rate e.before true
              (estimateAt rate rewards C_star C_h control0 q w) i)) := by
  filter_upwards [ReferenceExhaustiveGeneratedCalendarSourceLaw.ae_terminal_marked_path
    rate rewards C_star C_h control0 ids] with w hw
  intro q e he
  obtain ⟨hem, het⟩ := (currentMark_eq_some_iff rate rewards C_star C_h control0 q w e).mp he
  rcases hw.2.2 with hn | ⟨hl, hdata⟩
  · have hnil : archive rate rewards C_star C_h control0 w = [] := hn.2
    rw [hnil] at hem
    exact (List.not_mem_nil hem).elim
  · obtain ⟨⟨r, hr, _hphysical⟩, hb, ha, hi, hen, hnum, harr, hservice, _hregisters, _hstop⟩ :=
      hdata e hem
    let W := ReferenceActualCollectionHiddenRefreshPath.actualOriginalWord
      rate rewards C_star C_h (Z w) hl
    let start := ReferenceCompletePhysicalHistory.physicalStart rate (Z w) rewards C_star C_h
    have hs : start ≤ e.time.val := by
      by_contra hs
      unfold ReferenceSourcePrefixHistoryFiltration.actualRecord at hr
      rw [ite_eq_right hs] at hr
      cases hr
    let c := W[e.time.val - start]'hi
    have hnumc : e.numerical = ReferenceLaterCollectionSourceReadoutMeasurability.numericalCoordinates c := hnum
    have henc : c.enabled = true := hen
    have hx : estimateAt rate rewards C_star C_h control0 q w = inputEstimate e.before c := by
      rw [estimateAt, he]
      change cellEstimate rate e = inputEstimate e.before c
      funext i
      unfold cellEstimate
      rw [hnumc]
      rfl
    have hstep : e.after = RecordedQueueRun.step Q e.before c := by
      have hsucc : e.time.val + 1 - start = e.time.val - start + 1 := by omega
      rw [ha, hsucc, ← List.take_append_getElem hi,
        RecordedSlowRefresh.run_append_singleton, ← hb]
    have hrec : e.arrivals = estimateRecord rate e.before true
        (estimateAt rate rewards C_star C_h control0 q w) := by
      rw [hx, ← henc, estimateRecord_inputEstimate]
      exact harr
    refine ⟨(congrArg Prod.fst hnumc).trans henc, ?_, ?_, hrec, ?_, ?_⟩
    · have hp := ReferencePostInvocationNoncallGeometry.prefixNumerical_actualWord
        rate rewards C_star C_h e.time.castSucc (Z w) hl hs
      simpa only [← het, Fin.val_castSucc, hb] using hp
    · have hp := ReferencePostInvocationNoncallGeometry.prefixNumerical_actualWord
        rate rewards C_star C_h e.time.succ (Z w) hl (by change start ≤ e.time.val + 1; omega)
      simpa only [← het, Fin.val_succ, ha] using hp
    · rw [hx, ← henc, estimateStep_inputEstimate]
      exact hstep
    · rw [← hrec]
      exact hservice

section EpisodeOpportunity

private theorem measurable_optionIsSome {A : Type*} [MeasurableSpace A] :
    Measurable (Option.isSome : Option A → Bool) := by
  have h : Measurable (Sum.elim (fun _ : A => true) (fun _ : PUnit => false)) :=
    measurable_fun_sum measurable_const measurable_const
  convert h.comp (comap_measurable (Equiv.optionEquivSumPUnit A)) using 1
  funext a
  cases a <;> rfl

omit control0 in
/-- Read the old collection boundary from the actual incoming state, before
the sampler is invoked. Other incoming modes and absent records stay absent. -/
def incomingFreezeAt (s : Fin p.T) (z : Source p) : Option ℕ :=
  (ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h s z).bind
    (fun code => ReferenceFirstCollectionRenewalAuxiliaryLaw.coordinatorFreezeAt? rate code.1)

omit control0 in
theorem measurable_incomingFreezeAt (s : Fin p.T) :
    Measurable (incomingFreezeAt rate rewards C_star C_h s) := by
  have hf : Measurable (fun code : ReferenceActivePhysicalStepMeasurability.StateCode p rate =>
      ReferenceFirstCollectionRenewalAuxiliaryLaw.coordinatorFreezeAt? rate code.1) :=
    (ReferenceFirstCollectionRenewalAuxiliaryLaw.measurable_coordinatorFreezeAt? rate).comp measurable_fst
  have h : Measurable (Sum.elim
      (fun code : ReferenceActivePhysicalStepMeasurability.StateCode p rate =>
        ReferenceFirstCollectionRenewalAuxiliaryLaw.coordinatorFreezeAt? rate code.1)
      (fun _ : PUnit => (none : Option ℕ))) :=
    measurable_fun_sum hf measurable_const
  have he : incomingFreezeAt rate rewards C_star C_h s = fun z : Source p =>
      Sum.elim (fun code : ReferenceActivePhysicalStepMeasurability.StateCode p rate =>
        ReferenceFirstCollectionRenewalAuxiliaryLaw.coordinatorFreezeAt? rate code.1)
        (fun _ : PUnit => (none : Option ℕ))
        ((Equiv.optionEquivSumPUnit _) (ReferenceSourcePrefixHistoryFiltration.incoming
          rate rewards C_star C_h s z)) := by
    funext z
    unfold incomingFreezeAt
    cases ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h s z <;> rfl
  rw [he]
  exact h.comp ((comap_measurable
    (Equiv.optionEquivSumPUnit (ReferenceActivePhysicalStepMeasurability.StateCode p rate))).comp
      (ReferenceSourcePrefixHistoryFiltration.measurable_incoming rate rewards C_star C_h s))

theorem incomingFreezeAt_sourcePrefix (s : Fin p.T) (z : Source p) :
    incomingFreezeAt rate rewards C_star C_h s z =
      incomingFreezeAt rate rewards C_star C_h s (sourcePrefix control0 s.val z) := by
  unfold incomingFreezeAt
  rw [ReferenceSourcePrefixHistoryFiltration.incoming_factor rate rewards C_star C_h control0 s z]

omit control0 in
/-- The literal ledger boundary on a collection record. This does not test a
successful installation or look at the round's outcome. -/
theorem incomingFreezeAt_of_record (s : Fin p.T) (z : Source p)
    (r : Record rate)
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h s z = some r)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate) (saved : Option (Fin p.T × Bool))
    (hcoord : r.input.state.coordinator = .collection payload ledger saved) :
    incomingFreezeAt rate rewards C_star C_h s z = some ledger.freezeAt := by
  simp only [incomingFreezeAt, ReferenceSourcePrefixHistoryFiltration.incoming, hr, Option.map_some,
    Option.bind_some, ReferenceActivePhysicalStepMeasurability.encodeState, hcoord,
    ReferenceActivePhysicalStepMeasurability.encodeCoordinator,
    ReferenceFirstCollectionRenewalAuxiliaryLaw.coordinatorFreezeAt?]

omit control0 in
/-- Actual launch or actual renewal opportunity, on clear numerical PRE.
The call selector is tested before its draw; retained invocations before the
old boundary do not satisfy the renewal branch. -/
def sourceStartEvent (s : Fin p.T) : Set (Source p) :=
  {z | (z ∈ ReferenceGeneratedDownAmbiguityMeasurability.generatedLaunchFiberSet
        (rate := rate) rewards C_star C_h s.val ∨
      ((ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h s z).isSome = true ∧
        (incomingFreezeAt rate rewards C_star C_h s z).any (fun g => decide (g ≤ s.val + 1)) = true)) ∧
    (ReferencePostInvocationNoncallGeometry.prefixNumerical rate rewards C_star C_h s.castSucc z).any
      (fun S => !S.overflow) = true}

include control0 in
theorem measurableSet_sourceStartEvent (s : Fin p.T) :
    MeasurableSet (sourceStartEvent rate rewards C_star C_h s) := by
  have hc : Measurable (ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h s) :=
    (ReferenceCalendarCollectionCallControlLaw.callAt_measurable
      rate rewards C_star C_h control0 s).mono
        ((ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).le (s.val + 1)) le_rfl
  have hg : Measurable (fun z : Source p =>
      (incomingFreezeAt rate rewards C_star C_h s z).any (fun g => decide (g ≤ s.val + 1))) :=
    (measurable_of_countable (fun g : Option ℕ => g.any (fun n => decide (n ≤ s.val + 1)))).comp
      (measurable_incomingFreezeAt rate rewards C_star C_h s)
  have hp : Measurable (fun z : Source p =>
      (ReferencePostInvocationNoncallGeometry.prefixNumerical rate rewards C_star C_h s.castSucc z).any
        (fun S => !S.overflow)) :=
    (measurable_of_countable (fun o : Option (RecordedQueueRun.RunState p.K) =>
      o.any (fun S : RecordedQueueRun.RunState p.K => !S.overflow))).comp
      (ReferencePostInvocationPrefixLocality.measurable_prefixNumerical rate rewards C_star C_h s.castSucc)
  exact ((ReferenceGeneratedDownAmbiguityMeasurability.measurableSet_generatedLaunchFiberSet
      (rate := rate) rewards C_star C_h s.val).union
    (((measurableSet_singleton true).preimage (measurable_optionIsSome.comp hc)).inter
      ((measurableSet_singleton true).preimage hg))).inter
        ((measurableSet_singleton true).preimage hp)

/-- Every gate of the opportunity is determined before the initial draw. -/
theorem sourceStartEvent_sourcePrefix (s : Fin p.T) (z : Source p) :
    z ∈ sourceStartEvent rate rewards C_star C_h s ↔
      sourcePrefix control0 s.val z ∈ sourceStartEvent rate rewards C_star C_h s := by
  unfold sourceStartEvent
  change (_ ∨ (_ ∧ _)) ∧ _ ↔ (_ ∨ (_ ∧ _)) ∧ _
  rw [← ReferenceSourcePrefixHistoryFiltration.actualLaunchStratum_factor
      rate rewards C_star C_h control0 s.val s.isLt.le s.val le_rfl z,
    ← ReferenceCalendarCollectionCallControlLaw.callAt_factor rate rewards C_star C_h control0 s z,
    ← incomingFreezeAt_sourcePrefix rate rewards C_star C_h control0 s z,
    ← ReferencePostInvocationPrefixLocality.prefixNumerical_sourcePrefix
      rate rewards C_star C_h control0 s.castSucc s.val le_rfl z]

/-- The actual pre-draw episode opportunity on the original exhaustive space. -/
def episodeStartEvent (s : Fin p.T) : Set Omega :=
  Z ⁻¹' sourceStartEvent rate rewards C_star C_h s

theorem episodeStartEvent_eq_history_preimage (s : Fin p.T) :
    episodeStartEvent rate rewards C_star C_h control0 s =
      startHistory rate rewards C_star C_h control0 s ⁻¹'
        {h | h.1 ∈ sourceStartEvent rate rewards C_star C_h s} := by
  ext w
  exact sourceStartEvent_sourcePrefix rate rewards C_star C_h control0 s (Z w)

omit control0 in
/-- The two old-boundary observers agree on the SAME actual collection
record. Membership and the calendar timestamp are derived before either
observer is rewritten. -/
theorem incomingFreezeAt_eq_oldFreezeAt_on_call (s : Fin p.T) (z : Source p)
    (hc : (ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h s z).isSome = true) :
    incomingFreezeAt rate rewards C_star C_h s z =
      ReferenceFirstCollectionRenewalAuxiliaryLaw.oldFreezeAt? rate rewards C_star C_h s z := by
  obtain ⟨⟨u, theta⟩, hcall⟩ := Option.isSome_iff_exists.mp hc
  obtain ⟨r, hr, hrc⟩ := Option.bind_eq_some_iff.mp hcall
  obtain ⟨P, ledger, saved, hcoord, _, _⟩ :=
    (ReferenceFirstCollectionSamplerCall.collectionCallAt_spec r u theta).mp hrc
  obtain ⟨k, _, hk, _⟩ := ReferencePostInvocationGeneratedAlignment.actualRecord_index
    rate rewards C_star C_h s z r hr
  have hmem : r ∈ ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h :=
    hk ▸ List.getElem_mem k.isLt
  have ht := (ReferenceCalendarLaterSamplerOutputSections.actualRecord_fields
    rate rewards C_star C_h s z r hr).2.2.1
  rw [incomingFreezeAt_of_record rate rewards C_star C_h s z r hr P ledger saved hcoord,
    ReferenceFirstCollectionRenewalAuxiliaryLaw.oldFreezeAt?_eq_of_record
      rate rewards C_star C_h s z r hmem ht P ledger saved hcoord]

private theorem call_pending_empty (r : Record rate) (u : Fin p.T)
    (theta : AssignmentParameterFibreKernel.Theta p)
    (hc : ReferenceFirstCollectionSamplerCall.collectionCallAt r = some (u, theta))
    (P : ReferenceActivePhysicalStep.Payload rate) (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (saved : Option (Fin p.T × Bool))
    (hcoord : r.input.state.coordinator = .collection P ledger saved) : ledger.pending = ∅ := by
  obtain ⟨P', ledger', saved', heq, _, hp⟩ :=
    (ReferenceFirstCollectionSamplerCall.collectionCallAt_spec r u theta).mp hc
  rw [hcoord] at heq
  cases heq
  by_contra hn
  have hne := Finset.nonempty_iff_ne_empty.mpr hn
  simp only [ReferenceLaterSamplerParameterMeasurability.parameters?,
    ReferenceLaterAssignmentFibreStep.parameters?, hcoord] at hp
  split at hp
  · unfold ReferenceLaterAssignmentFibreStep.collectionParameters? at hp
    split at hp
    · cases hp
    · split at hp
      · simp only [ReferenceActivePhysicalStep.collectionInput, hne, ite_true] at hp
        cases hp
      · cases hp
  · cases hp

open ReferenceOriginalCalendarEpisodeChronology in
/-- Every literal pre-draw opportunity is an actual original episode birth.
The suffix index is produced and its calendar time is identified explicitly;
it is never used as a substitute calendar date. -/
theorem sourceStartEvent_episode_birth (s : Fin p.T) (z : Source p)
    (hs : z ∈ sourceStartEvent rate rewards C_star C_h s) :
    ∃ rho : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).length,
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[rho.val].input.time = s ∧
      ReferenceCompleteEpisodeAnchorOrigin.IsEpisodeAnchorBirth
        (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[rho.val] := by
  rcases hs.1 with hlaunch | ⟨hcall, hfreeze⟩
  · have hlen := ReferenceCompletePhysicalHistory.completeSuffixRecords_length rate z rewards C_star C_h
    let rho : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).length :=
      ⟨0, by rw [hlen, hlaunch.2]; have := s.isLt; omega⟩
    refine ⟨rho, ?_, (complete_episode_birth_iff_launch_or_renewal
      rate rewards C_star C_h z rho).mpr (Or.inl rfl)⟩
    apply Fin.ext
    simpa only [rho, Nat.add_zero, hlaunch.2] using
      ReferenceAssignmentFollowerMassSteps.complete_record_time rate rewards C_star C_h z rho
  · obtain ⟨⟨u, theta⟩, hc⟩ := Option.isSome_iff_exists.mp hcall
    obtain ⟨r, hr, hrc⟩ := Option.bind_eq_some_iff.mp hc
    obtain ⟨P, ledger, saved, hcoord, _, _⟩ :=
      (ReferenceFirstCollectionSamplerCall.collectionCallAt_spec r u theta).mp hrc
    obtain ⟨rho, _, hrecord, _⟩ := ReferencePostInvocationGeneratedAlignment.actualRecord_index
      rate rewards C_star C_h s z r hr
    have ht := (ReferenceCalendarLaterSamplerOutputSections.actualRecord_fields
      rate rewards C_star C_h s z r hr).2.2.1
    have hg : ledger.freezeAt ≤ s.val + 1 := by
      rw [incomingFreezeAt_of_record rate rewards C_star C_h s z r hr P ledger saved hcoord,
        Option.any_some, decide_eq_true_eq] at hfreeze
      exact hfreeze
    refine ⟨rho, hrecord ▸ ht, ?_⟩
    apply (complete_episode_birth_iff_launch_or_renewal rate rewards C_star C_h z rho).mpr
    right
    rw [hrecord]
    exact ⟨P, ledger, saved, hcoord,
      call_pending_empty rate r u theta hrc P ledger saved hcoord, ht ▸ hg⟩

end EpisodeOpportunity

section FirstRenewalInitialization

open ReferenceFirstNextInstallationCellFactors
open ReferenceGeneratedRankCalendarFoundation
open ReferenceGeneratedCalendarPathAgreement
open ReferenceGeneratedCalendarRootRoundLaw

private abbrev InitErased (s : Fin p.T) :=
  _root_.Bandits.Support.ReferenceFirstLiveActualRefreshTestLaw.ErasedAuxiliaryArray s

local notation "eraseLaw" => _root_.Bandits.Support.ReferenceFirstLiveActualRefreshTestLaw.erasedAuxiliaryLaw
local notation "insertInit" => _root_.Bandits.Support.ReferenceFirstLiveActualRefreshTestLaw.insertActualRefreshCoordinate
local notation "zeroScalar" => _root_.Bandits.Support.ReferenceFirstLiveActualRefreshTestLaw.scalarZero

omit rewards C_star C_h control0 in
/-- The prescribed initial PMF with current weights as the new anchor. -/
def initialMass (S : RecordedQueueRun.RunState p.K) (U : SlowSet p) : ℝ≥0∞ :=
  RecordedSlowRefresh.recordedSlowPMF p Q S (RecordedQueueRun.scoreWeight Q S)
    (RecordedSlowRefresh.scoreWeight_pos Q S) U

omit control0 in
/-- An unnormalized PRE-retained test. An absent physical prefix contributes
no mass and is never replaced by an invented numerical state. -/
def preRetainedTest (s : Fin p.T) (z : Source p)
    (f : RecordedQueueRun.RunState p.K → ℝ≥0∞) : ℝ≥0∞ :=
  match ReferencePostInvocationNoncallGeometry.prefixNumerical rate rewards C_star C_h s.castSucc z with
  | none => 0
  | some S => if S.overflow then 0 else f S

private theorem prefixNumerical_firstBefore (s : Fin p.T)
    (z : FirstInvocationSource rate rewards C_star C_h s) :
    ReferencePostInvocationNoncallGeometry.prefixNumerical rate rewards C_star C_h s.castSucc z.val =
      some (firstBefore rate rewards C_star C_h control0 s z) := by
  have hr := (firstSourceCell_spec rate rewards C_star C_h s z).1
  have hs : ReferenceCompletePhysicalHistory.physicalStart rate z.val rewards C_star C_h ≤ s.val := by
    by_contra hs
    unfold ReferenceSourcePrefixHistoryFiltration.actualRecord at hr
    rw [ite_eq_right hs] at hr
    cases hr
  have hp := ReferencePostInvocationNoncallGeometry.prefixNumerical_actualWord rate rewards C_star C_h s.castSucc
    z.val (ReferencePostInvocationGeneratedAlignment.firstInvocation_launch rate rewards C_star C_h s z) hs
  simpa only [Fin.val_castSucc, rootBefore_originalWord] using hp

private theorem rootRenewal_prefixBefore (u s : Fin p.T)
    (w : CalendarSample rate rewards C_star C_h true u s 0) :
    ReferencePostInvocationNoncallGeometry.prefixNumerical rate rewards C_star C_h s.castSucc
      (rootBeforeInitialization rate rewards C_star C_h control0 s (w.1.1.val, w.1.2)).1 =
        some (calendarRootCell rate rewards C_star C_h control0 true u s w).before := by
  let z := rootInstalledSource rate rewards C_star C_h true u s w.1.1 w.2
  have hp : sourcePrefix control0 s.val z.val = sourcePrefix control0 s.val w.1.1.val :=
    congrArg Prod.fst (rootInstalledSource_history rate rewards C_star C_h control0 true u s w.1.1 w.2)
  have hn := prefixNumerical_firstBefore rate rewards C_star C_h control0 s z
  rw [ReferencePostInvocationPrefixLocality.prefixNumerical_sourcePrefix rate rewards C_star C_h control0
    s.castSucc s.val le_rfl z.val, hp] at hn
  exact hn

private theorem measurable_preRetainedTest (s : Fin p.T)
    (f : (Source p × List (LogicalCell p rate)) × SlowSet p → RecordedQueueRun.RunState p.K → ℝ≥0∞)
    (hf : Measurable (fun v : ((Source p × List (LogicalCell p rate)) × SlowSet p) ×
      RecordedQueueRun.RunState p.K => f v.1 v.2)) :
    Measurable (fun v : (Source p × List (LogicalCell p rate)) × SlowSet p =>
      preRetainedTest rate rewards C_star C_h s v.1.1 (f v)) := by
  let A := RecordedQueueRun.RunState p.K
  let X := (Source p × List (LogicalCell p rate)) × SlowSet p
  let g : A × X → ℝ≥0∞ := fun v => if v.1.overflow then 0 else f v.2 v.1
  have hg : Measurable g := measurable_const.ite
    ((measurableSet_singleton true).preimage
      ((measurable_of_countable RecordedQueueRun.RunState.overflow).comp measurable_fst))
    (hf.comp (measurable_snd.prodMk measurable_fst))
  have hsum : Measurable (Sum.elim g (fun _ : PUnit × X => (0 : ℝ≥0∞))) :=
    measurable_fun_sum hg measurable_const
  let equiv := ReferenceCollectionDispatchMeasurability.optionPairEquiv A X
  have hpre := (ReferencePostInvocationPrefixLocality.measurable_prefixNumerical
    rate rewards C_star C_h s.castSucc).comp (measurable_fst.fst : Measurable (fun v : X => v.1.1))
  convert hsum.comp (equiv.measurable.comp (hpre.prodMk measurable_id)) using 1
  funext v
  dsimp only [Function.comp_apply, id_eq]
  unfold preRetainedTest
  cases ReferencePostInvocationNoncallGeometry.prefixNumerical rate rewards C_star C_h s.castSucc v.1.1 <;> rfl

/-- First-renewal initialization on the actual generated root: arbitrary
joint tests of the true before-draw archive/prefix, with the current numerical
weight as BOTH current and anchor weight. The clear gate is PRE, hence this
also includes a first detecting overflow UPDATE at the root. The branch mass
is unnormalized; the tested first-call event is already past at this draw. -/
theorem calendarLaw_first_renewal_initial_cylinder (u s : Fin p.T) (U : SlowSet p)
    (Phi : Source p × List (LogicalCell p rate) → ℝ≥0∞) (hPhi : Measurable Phi) :
    (∫⁻ w : CalendarSample rate rewards C_star C_h true u s 0,
      if (calendarRootCell rate rewards C_star C_h control0 true u s w).before.overflow then 0 else
        Phi (rootBeforeInitialization rate rewards C_star C_h control0 s (w.1.1.val, w.1.2)) *
          (if (calendarRootCell rate rewards C_star C_h control0 true u s w).slowSet = U then 1 else 0)
      ∂calendarLaw rate rewards C_star C_h control0 true u s 0 (by omega)) =
    ∫⁻ w : CalendarSample rate rewards C_star C_h true u s 0,
      if (calendarRootCell rate rewards C_star C_h control0 true u s w).before.overflow then 0 else
        Phi (rootBeforeInitialization rate rewards C_star C_h control0 s (w.1.1.val, w.1.2)) *
          initialMass rate (calendarRootCell rate rewards C_star C_h control0 true u s w).before U
      ∂calendarLaw rate rewards C_star C_h control0 true u s 0 (by omega) := by
  let H := Source p × List (LogicalCell p rate)
  let F : (H × SlowSet p) → ℝ≥0∞ := fun v =>
    preRetainedTest rate rewards C_star C_h s v.1.1 (fun _ => Phi v.1 * if v.2 = U then 1 else 0)
  let G : (H × SlowSet p) → ℝ≥0∞ := fun v =>
    preRetainedTest rate rewards C_star C_h s v.1.1 (fun S => Phi v.1 * initialMass rate S U)
  have hF : Measurable F := measurable_preRetainedTest rate rewards C_star C_h s _
    ((hPhi.comp measurable_fst.fst).mul
      (measurable_const.ite ((measurableSet_singleton U).preimage measurable_fst.snd) measurable_const))
  have hG : Measurable G := measurable_preRetainedTest rate rewards C_star C_h s _
    ((hPhi.comp measurable_fst.fst).mul ((measurable_of_countable (fun S => initialMass rate S U)).comp measurable_snd))
  let project : (H × ((Source p × InitErased s) × SlowSet p)) → H × SlowSet p :=
    fun v => (v.1, v.2.2)
  have hproject : Measurable project := measurable_fst.prodMk measurable_snd.snd
  have htest := calendarLaw_root_initializer_test rate rewards C_star C_h control0 u s
    (F ∘ project) (hF.comp hproject)
  have hmass := calendarLaw_root_initializer_test rate rewards C_star C_h control0 u s
    (G ∘ project) (hG.comp hproject)
  let evaluate (f : H × SlowSet p → ℝ≥0∞) :=
    ∫⁻ z, ∫⁻ e : InitErased s, ∫⁻ V,
      f (rootBeforeInitialization rate rewards C_star C_h control0 s
        (z.val, insertInit s e zeroScalar), V)
      ∂(ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSlowSetPMF rate rewards C_star C_h u s z).toMeasure
      ∂eraseLaw s ∂ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u s
  have hright : evaluate F = evaluate G := by
    apply lintegral_congr
    intro z
    apply lintegral_congr
    intro e
    let z0 := renewedFirstSource rate rewards C_star C_h s u z
    let S := firstBefore rate rewards C_star C_h control0 s z0
    have hp := prefixNumerical_firstBefore rate rewards C_star C_h control0 s z0
    have hp' : ReferencePostInvocationNoncallGeometry.prefixNumerical rate rewards C_star C_h s.castSucc
        (sourcePrefix control0 s.val z.val) = some S := by
      rw [← ReferencePostInvocationPrefixLocality.prefixNumerical_sourcePrefix
        rate rewards C_star C_h control0 s.castSucc s.val le_rfl z.val]
      exact hp
    have hm : S.overflow = false →
        ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSlowSetPMF rate rewards C_star C_h u s z =
          RecordedSlowRefresh.recordedSlowPMF p Q S (RecordedQueueRun.scoreWeight Q S)
            (RecordedSlowRefresh.scoreWeight_pos Q S) := by
      intro hs
      have hw := rootRenewal_initialWeight rate rewards C_star C_h control0 u s z hs
      unfold ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSlowSetPMF RecordedSlowRefresh.recordedSlowPMF
      congr 1
    change (∫⁻ V, (match ReferencePostInvocationNoncallGeometry.prefixNumerical rate rewards C_star C_h s.castSucc
      (sourcePrefix control0 s.val z.val) with
      | none => 0
      | some S => if S.overflow then 0 else Phi _ * if V = U then 1 else 0) ∂_) =
      ∫⁻ V, (match ReferencePostInvocationNoncallGeometry.prefixNumerical rate rewards C_star C_h s.castSucc
      (sourcePrefix control0 s.val z.val) with
      | none => 0
      | some S => if S.overflow then 0 else Phi _ * initialMass rate S U) ∂_
    rw [hp']
    cases hs : S.overflow with
    | true => simp only [hs, ite_true, lintegral_zero]
    | false =>
      simp only [hs, Bool.false_eq_true, ite_false]
      rw [hm hs]
      rw [lintegral_fintype, lintegral_fintype]
      simp only [initialMass, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq',
        Finset.mem_univ, ite_true]
      rw [← Finset.mul_sum]
      simp_rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
      rw [← tsum_fintype (L := .unconditional _), PMF.tsum_coe, mul_one]
  have heq := htest.trans (hright.trans hmass.symm)
  calc
    _ = ∫⁻ w : CalendarSample rate rewards C_star C_h true u s 0,
        F (rootBeforeInitialization rate rewards C_star C_h control0 s (w.1.1.val, w.1.2),
          ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalAuxiliarySample rate rewards C_star C_h u s w.1.1 w.1.2)
        ∂calendarLaw rate rewards C_star C_h control0 true u s 0 (by omega) := by
      apply lintegral_congr_ae
      filter_upwards [ae_calendarLaw_root_renewal_initialSlowSet rate rewards C_star C_h control0 u s] with w hw
      dsimp only [Function.comp_apply, project, F, preRetainedTest]
      rw [rootRenewal_prefixBefore rate rewards C_star C_h control0 u s w]
      cases hs : (calendarRootCell rate rewards C_star C_h control0 true u s w).before.overflow with
      | true => simp only [hs, ite_true]
      | false => simp only [hs, Bool.false_eq_true, ite_false, hw hs]
    _ = _ := heq
    _ = _ := by
      apply lintegral_congr
      intro w
      dsimp only [Function.comp_apply, project, G, preRetainedTest]
      rw [rootRenewal_prefixBefore rate rewards C_star C_h control0 u s w]

open ReferenceGeneratedCalendarResidualBlock

private theorem generated_startHistory_root (u s : Fin p.T)
    (w : ReferenceExhaustiveGeneratedCalendarSourceLaw.Payload rate rewards C_star C_h (.generated true u s)) :
    startHistory rate rewards C_star C_h control0 s ⟨.generated true u s, w⟩ =
      rootBeforeInitialization rate rewards C_star C_h control0 s
        ((calendarOriginalLift rate rewards C_star C_h true u s _ w).1.1.val,
          (calendarOriginalLift rate rewards C_star C_h true u s _ w).1.2) := by
  let k := p.T - (s.val + 1)
  have hk : s.val + 1 + k ≤ p.T := by dsimp only [k]; omega
  let root := calendarAncestor rate rewards C_star C_h true u s k 0 (Nat.zero_le _) w
  have hroot : root = calendarOriginalLift rate rewards C_star C_h true u s k w :=
    calendarAncestor_original rate rewards C_star C_h true u s k 0 (Nat.zero_le _) w
  have hp := (calendarObservation_ancestor_preserves rate rewards C_star C_h control0 true u s
    k hk w 0 (Nat.zero_le _)).2.1
  have hsmall := congrArg (sourcePrefix control0 s.val) hp
  simp only [Nat.add_zero, ReferenceSourcePrefixHistoryFiltration.sourcePrefix_sourcePrefix
    control0 s.val (s.val + 1) (Nat.le_succ _)] at hsmall
  change sourcePrefix control0 s.val (calendarCurrentSource rate rewards C_star C_h control0 true u s k hk w) =
    sourcePrefix control0 s.val (calendarCurrentSource rate rewards C_star C_h control0 true u s 0 (by omega) root) at hsmall
  have hinit : sourcePrefix control0 s.val
      (calendarCurrentSource rate rewards C_star C_h control0 true u s 0 (by omega) root) =
        sourcePrefix control0 s.val root.1.1.val :=
    congrArg Prod.fst (rootInstalledSource_history rate rewards C_star C_h control0 true u s root.1.1 root.2)
  refine Prod.ext ?_ ?_
  · exact hsmall.trans (hinit.trans (congrArg (fun v : CalendarSample rate rewards C_star C_h true u s 0 =>
      sourcePrefix control0 s.val v.1.1.val) hroot))
  · exact ReferenceGeneratedCalendarEpisodePrefixRecombination.generated_archiveBefore
      rate rewards C_star C_h control0 true u s s.castSucc le_rfl k hk w

/-- The initial slow set in a renewed first-call episode is the SAME mark
archived in the exhaustive terminal sample, after every later insertion. -/
theorem generated_first_renewal_currentMark (u s : Fin p.T)
    (w : ReferenceExhaustiveGeneratedCalendarSourceLaw.Payload rate rewards C_star C_h (.generated true u s)) :
    currentMark rate rewards C_star C_h control0 s ⟨.generated true u s, w⟩ =
      some (calendarRootCell rate rewards C_star C_h control0 true u s
        (calendarOriginalLift rate rewards C_star C_h true u s _ w)) := by
  let k := p.T - (s.val + 1)
  have hk : s.val + 1 + k ≤ p.T := by dsimp only [k]; omega
  let root := calendarAncestor rate rewards C_star C_h true u s k 0 (Nat.zero_le _) w
  have hroot : root = calendarOriginalLift rate rewards C_star C_h true u s k w :=
    calendarAncestor_original rate rewards C_star C_h true u s k 0 (Nat.zero_le _) w
  rw [← hroot]
  apply (currentMark_eq_some_iff rate rewards C_star C_h control0 s _ _).mpr
  constructor
  · have hp := (calendarObservation_ancestor_preserves rate rewards C_star C_h control0 true u s
      k hk w 0 (Nat.zero_le _)).1
    apply hp.subset
    rw [(calendarObservation_root rate rewards C_star C_h control0 true u s (by omega) root).2.1]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  · exact actualFirstCell_time rate rewards C_star C_h control0 s _ _

omit rewards C_star C_h control0 in
/-- A retained initial-set cylinder on an optional ACTUAL mark. Absence has
zero mass without specifying any state or slow set on that branch. -/
def initialSetCylinder (U : SlowSet p) (e : Option (LogicalCell p rate)) : ℝ≥0∞ :=
  match e with
  | none => 0
  | some e => if e.before.overflow then 0 else if e.slowSet = U then 1 else 0

omit rewards C_star C_h control0 in
/-- The matching retained numerical initial mass on that SAME optional mark. -/
def initialMassCylinder (U : SlowSet p) (e : Option (LogicalCell p rate)) : ℝ≥0∞ :=
  match e with
  | none => 0
  | some e => if e.before.overflow then 0 else initialMass rate e.before U

/-- A first-renewal INITIAL cylinder on the actual exhaustive component.
This transports the before-draw law through every real ancestor kernel and
tests the actual terminal archive mark and actual terminal strict history.
It is an initialization result; it does not assert preservation at later dates. -/
theorem componentLaw_first_renewal_initial_cylinder (u s : Fin p.T) (U : SlowSet p)
    (Phi : Source p × List (LogicalCell p rate) → ℝ≥0∞) (hPhi : Measurable Phi) :
    (∫⁻ w : ReferenceExhaustiveGeneratedCalendarSourceLaw.Payload rate rewards C_star C_h (.generated true u s),
      Phi (startHistory rate rewards C_star C_h control0 s ⟨.generated true u s, w⟩) *
        initialSetCylinder rate U (currentMark rate rewards C_star C_h control0 s ⟨.generated true u s, w⟩)
      ∂ReferenceExhaustiveGeneratedCalendarSourceLaw.componentLaw rate rewards C_star C_h control0 (.generated true u s)) =
    ∫⁻ w : ReferenceExhaustiveGeneratedCalendarSourceLaw.Payload rate rewards C_star C_h (.generated true u s),
      Phi (startHistory rate rewards C_star C_h control0 s ⟨.generated true u s, w⟩) *
        initialMassCylinder rate U (currentMark rate rewards C_star C_h control0 s ⟨.generated true u s, w⟩)
      ∂ReferenceExhaustiveGeneratedCalendarSourceLaw.componentLaw rate rewards C_star C_h control0 (.generated true u s) := by
  let S := ReferencePostInvocationPrefixLocality.BranchLift rate rewards C_star C_h true u s
  let H := fun w : S => rootBeforeInitialization rate rewards C_star C_h control0 s (w.1.1.val, w.1.2)
  let cell := calendarRootCell rate rewards C_star C_h control0 true u s
  let F : S → ℝ≥0∞ := fun w => Phi (H w) * initialSetCylinder rate U (some (cell w))
  let G : S → ℝ≥0∞ := fun w => Phi (H w) * initialMassCylinder rate U (some (cell w))
  have hH : Measurable H := (measurable_rootBeforeInitialization rate rewards C_star C_h control0 s).comp
    ((measurable_fst.fst.subtype_val).prodMk measurable_fst.snd)
  have hcell := measurable_calendarRootCell rate rewards C_star C_h control0 true u s
  have hpre : Measurable (fun w : S => (cell w).before.overflow) :=
    (measurable_of_countable RecordedQueueRun.RunState.overflow).comp
      (measurable_logicalCell_before.comp hcell)
  have hslow : Measurable (fun w : S => (cell w).slowSet) :=
    (measurable_logicalCell_slowSet.comp hcell).mono le_rfl le_top
  have hF : Measurable F := (hPhi.comp hH).mul
    (measurable_const.ite ((measurableSet_singleton true).preimage hpre)
      (measurable_const.ite ((measurableSet_singleton U).preimage hslow) measurable_const))
  have hG : Measurable G := (hPhi.comp hH).mul
    (measurable_const.ite ((measurableSet_singleton true).preimage hpre)
      ((measurable_of_countable (fun S => initialMass rate S U)).comp (measurable_logicalCell_before.comp hcell)))
  have hroot : (∫⁻ w, F w ∂calendarLaw rate rewards C_star C_h control0 true u s 0 (by omega)) =
      ∫⁻ w, G w ∂calendarLaw rate rewards C_star C_h control0 true u s 0 (by omega) := by
    simpa only [F, G, initialSetCylinder, initialMassCylinder, mul_ite, mul_zero, mul_one] using
      calendarLaw_first_renewal_initial_cylinder rate rewards C_star C_h control0 u s U Phi hPhi
  have hf (w : ReferenceExhaustiveGeneratedCalendarSourceLaw.Payload rate rewards C_star C_h (.generated true u s)) :
      Phi (startHistory rate rewards C_star C_h control0 s ⟨.generated true u s, w⟩) *
        initialSetCylinder rate U (currentMark rate rewards C_star C_h control0 s ⟨.generated true u s, w⟩) =
          F (calendarOriginalLift rate rewards C_star C_h true u s _ w) := by
    rw [generated_startHistory_root, generated_first_renewal_currentMark]
  have hg (w : ReferenceExhaustiveGeneratedCalendarSourceLaw.Payload rate rewards C_star C_h (.generated true u s)) :
      Phi (startHistory rate rewards C_star C_h control0 s ⟨.generated true u s, w⟩) *
        initialMassCylinder rate U (currentMark rate rewards C_star C_h control0 s ⟨.generated true u s, w⟩) =
          G (calendarOriginalLift rate rewards C_star C_h true u s _ w) := by
    rw [generated_startHistory_root, generated_first_renewal_currentMark]
  simp_rw [hf, hg]
  rw [ReferenceExhaustiveGeneratedCalendarSourceLaw.componentLaw, generatedCalendarLaw]
  simp only [Fin.val_last]
  rw [← lintegral_map hF (measurable_calendarOriginalLift rate rewards C_star C_h true u s _),
    ← lintegral_map hG (measurable_calendarOriginalLift rate rewards C_star C_h true u s _),
    calendarLaw_map_originalLift]
  exact hroot

end FirstRenewalInitialization

section TerminalInitialization

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

private theorem measurable_optional_zero (f : LogicalCell p rate → ℝ≥0∞) (hf : Measurable f) :
    Measurable (fun e : Option (LogicalCell p rate) => match e with | none => 0 | some e => f e) := by
  have hm : Measurable (Sum.elim f (fun _ : PUnit => (0 : ℝ≥0∞))) :=
    measurable_fun_sum hf measurable_const
  convert hm.comp (comap_measurable (Equiv.optionEquivSumPUnit (LogicalCell p rate))) using 1
  funext e
  cases e <;> rfl

omit rewards C_star C_h control0 in
theorem measurable_initialSetCylinder (U : SlowSet p) : Measurable (initialSetCylinder rate U) := by
  apply measurable_optional_zero
  have hpre : Measurable (fun e : LogicalCell p rate => e.before.overflow) :=
    (measurable_of_countable RecordedQueueRun.RunState.overflow).comp measurable_logicalCell_before
  exact measurable_const.ite ((measurableSet_singleton true).preimage hpre)
    (measurable_const.ite ((measurableSet_singleton U).preimage
      (measurable_logicalCell_slowSet.mono le_rfl le_top)) measurable_const)

omit rewards C_star C_h control0 in
theorem measurable_initialMassCylinder (U : SlowSet p) : Measurable (initialMassCylinder rate U) := by
  apply measurable_optional_zero
  have hpre : Measurable (fun e : LogicalCell p rate => e.before.overflow) :=
    (measurable_of_countable RecordedQueueRun.RunState.overflow).comp measurable_logicalCell_before
  exact measurable_const.ite ((measurableSet_singleton true).preimage hpre)
    ((measurable_of_countable (fun S => initialMass rate S U)).comp measurable_logicalCell_before)

/-- The before-draw history retains the original IDs and the complete original
private arrays and selecting scalar, even after all vector insertions. -/
theorem startHistory_original_background (s : Fin p.T) (w : Omega) :
    (startHistory rate rewards C_star C_h control0 s w).1.1.1 =
      (ReferenceExhaustiveGeneratedCalendarSourceLaw.originalSource rate rewards C_star C_h w).1.1 ∧
    (startHistory rate rewards C_star C_h control0 s w).1.2 =
      (ReferenceExhaustiveGeneratedCalendarSourceLaw.originalSource rate rewards C_star C_h w).2 :=
  ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalSource_original_ids_private rate rewards C_star C_h control0 w

private theorem terminalLaw_component_test (i : ReferenceExhaustiveGeneratedCalendarSourceLaw.Component p)
    (F : Omega → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ w : Omega, if w.1 = i then F w else 0
      ∂ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalLaw rate rewards C_star C_h control0) =
      ∫⁻ w, F ⟨i, w⟩ ∂ReferenceExhaustiveGeneratedCalendarSourceLaw.componentLaw rate rewards C_star C_h control0 i := by
  let G : Omega → ℝ≥0∞ := fun w => if w.1 = i then F w else 0
  have hG : Measurable G := measurable_sigma_elim _ (fun j => by
    by_cases hj : j = i
    · subst j
      simpa only [G, ite_true, Function.comp_def] using hF.comp (measurable_sigma_mk i)
    · simpa only [G, hj, ite_false] using (measurable_const : Measurable
        (fun _ : ReferenceExhaustiveGeneratedCalendarSourceLaw.Payload rate rewards C_star C_h j => (0 : ℝ≥0∞))))
  change (∫⁻ w, G w ∂_) = _
  rw [ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalLaw, lintegral_sum_measure]
  simp_rw [lintegral_map hG (measurable_sigma_mk _)]
  rw [tsum_eq_single i]
  · simp only [G, ite_true]
  · intro j hj
    simp only [G, hj, ite_false, lintegral_zero]

private theorem terminalLaw_first_renewal_initial_cylinder_raw (u s : Fin p.T) (U : SlowSet p)
    (Phi : Source p × List (LogicalCell p rate) → ℝ≥0∞) (hPhi : Measurable Phi) :
    (∫⁻ w : Omega, if w.1 = .generated true u s then
      Phi (startHistory rate rewards C_star C_h control0 s w) *
        initialSetCylinder rate U (currentMark rate rewards C_star C_h control0 s w) else 0
      ∂ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalLaw rate rewards C_star C_h control0) =
    ∫⁻ w : Omega, if w.1 = .generated true u s then
      Phi (startHistory rate rewards C_star C_h control0 s w) *
        initialMassCylinder rate U (currentMark rate rewards C_star C_h control0 s w) else 0
      ∂ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalLaw rate rewards C_star C_h control0 := by
  let F : Omega → ℝ≥0∞ := fun w => Phi (startHistory rate rewards C_star C_h control0 s w) *
    initialSetCylinder rate U (currentMark rate rewards C_star C_h control0 s w)
  let G : Omega → ℝ≥0∞ := fun w => Phi (startHistory rate rewards C_star C_h control0 s w) *
    initialMassCylinder rate U (currentMark rate rewards C_star C_h control0 s w)
  have hF : Measurable F := (hPhi.comp (measurable_startHistory rate rewards C_star C_h control0 s)).mul
    ((measurable_initialSetCylinder rate U).comp (measurable_currentMark rate rewards C_star C_h control0 s))
  have hG : Measurable G := (hPhi.comp (measurable_startHistory rate rewards C_star C_h control0 s)).mul
    ((measurable_initialMassCylinder rate U).comp (measurable_currentMark rate rewards C_star C_h control0 s))
  exact (terminalLaw_component_test rate rewards C_star C_h control0 (.generated true u s) F hF).trans
    ((componentLaw_first_renewal_initial_cylinder rate rewards C_star C_h control0 u s U Phi hPhi).trans
      (terminalLaw_component_test rate rewards C_star C_h control0 (.generated true u s) G hG).symm)

/-- First-renewal initialization on BOTH actual terminal laws. The fixed-ID
case normalizes only the original positive ID atom. All physical/private
coordinates and the original raw sample are retained. This is the initial
date of a renewed FIRST-call episode, not the later-date episode law. -/
theorem terminalLaw_first_renewal_initial_cylinder (ids : Option (CompletePublicTable.IDArray p))
    (u s : Fin p.T) (U : SlowSet p)
    (Phi : Source p × List (LogicalCell p rate) → ℝ≥0∞) (hPhi : Measurable Phi) :
    (∫⁻ w : Omega, if w.1 = .generated true u s then
      Phi (startHistory rate rewards C_star C_h control0 s w) *
        initialSetCylinder rate U (currentMark rate rewards C_star C_h control0 s w) else 0
      ∂ids.elim (ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalLaw rate rewards C_star C_h control0)
        (ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDTerminalLaw rate rewards C_star C_h control0)) =
    ∫⁻ w : Omega, if w.1 = .generated true u s then
      Phi (startHistory rate rewards C_star C_h control0 s w) *
        initialMassCylinder rate U (currentMark rate rewards C_star C_h control0 s w) else 0
      ∂ids.elim (ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalLaw rate rewards C_star C_h control0)
        (ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDTerminalLaw rate rewards C_star C_h control0) := by
  cases ids with
  | none => exact terminalLaw_first_renewal_initial_cylinder_raw rate rewards C_star C_h control0 u s U Phi hPhi
  | some ids =>
    let PhiID : Source p × List (LogicalCell p rate) → ℝ≥0∞ :=
      fun h => if h.1.1.1 = ids then Phi h else 0
    have hPhiID : Measurable PhiID := hPhi.ite
      ((measurableSet_singleton ids).preimage measurable_fst.fst.fst) measurable_const
    have hraw := terminalLaw_first_renewal_initial_cylinder_raw rate rewards C_star C_h control0 u s U PhiID hPhiID
    let A : Set Omega := (ReferenceExhaustiveGeneratedCalendarSourceLaw.originalSource rate rewards C_star C_h) ⁻¹'
      ReferenceFixedIDSourceSection.fixedIDSourceSection ids
    have hA : MeasurableSet A :=
      (measurableSet_singleton ids).preimage
        (ReferenceGeneratedCalendarEpisodePrefixRecombination.measurable_originalSource
          rate rewards C_star C_h control0).fst.fst
    dsimp only [Option.elim]
    rw [ReferenceGeneratedCalendarEpisodePrefixRecombination.fixedIDTerminalLaw_eq_original_restrict,
      lintegral_smul_measure, lintegral_smul_measure]
    congr 1
    rw [← lintegral_indicator hA, ← lintegral_indicator hA]
    convert hraw using 1 <;> apply lintegral_congr <;> intro w <;>
      have hid := (startHistory_original_background rate rewards C_star C_h control0 s w).1 <;>
      by_cases hi : (ReferenceExhaustiveGeneratedCalendarSourceLaw.originalSource rate rewards C_star C_h w).1.1 = ids <;>
      by_cases ht : w.1 = .generated true u s <;>
      simp only [PhiID, hid, hi, ht, ite_true, ite_false, zero_mul, Set.indicator,
        A, Set.mem_preimage, ReferenceFixedIDSourceSection.fixedIDSourceSection, Set.mem_ofPred_eq]

end TerminalInitialization

section ChronologicalReplay

/-- Chronological finite fold of precisely the already exposed estimates.
The optional strict-prefix seed retains the complete queue machine, including
its record lists and absorbing overflow. Every date inside the actual episode
is enabled, even when its raw estimate is zero. -/
def replayPrefix (s q : Fin p.T)
    (h : (Source p × List (LogicalCell p rate)) × (EstimateDates s q → Estimate p))
    (n : ℕ) (hn : n ≤ q.val - s.val) : Option (RecordedQueueRun.RunState p.K) :=
  (List.finRange n).foldl (fun state i => state.map (fun S =>
    estimateStep rate S true (h.2 ⟨⟨s.val + i.val, by have := i.isLt; omega⟩,
      by change s.val ≤ s.val + i.val; omega,
      by change s.val + i.val < q.val; have := i.isLt; omega⟩)))
    (ReferencePostInvocationNoncallGeometry.prefixNumerical rate rewards C_star C_h s.castSucc h.1.1)

omit control0 in
theorem replayPrefix_succ (s q : Fin p.T)
    (h : (Source p × List (LogicalCell p rate)) × (EstimateDates s q → Estimate p))
    (n : ℕ) (hn : n + 1 ≤ q.val - s.val) :
    replayPrefix rate rewards C_star C_h s q h (n + 1) hn =
      (replayPrefix rate rewards C_star C_h s q h n (by omega)).map (fun S =>
        estimateStep rate S true (h.2 ⟨⟨s.val + n, by omega⟩, by change s.val ≤ s.val + n; omega,
          by change s.val + n < q.val; omega⟩)) := by
  simp only [replayPrefix, List.finRange_succ_last, List.foldl_append, List.foldl_map,
    List.foldl_cons, List.foldl_nil]
  rfl

omit control0 in
theorem measurable_replayPrefix (s q : Fin p.T) (n : ℕ) (hn : n ≤ q.val - s.val) :
    Measurable (fun h => replayPrefix rate rewards C_star C_h s q h n hn) := by
  induction n with
  | zero =>
    exact (ReferencePostInvocationPrefixLocality.measurable_prefixNumerical
      rate rewards C_star C_h s.castSucc).comp measurable_fst.fst
  | succ n ih =>
    simp_rw [replayPrefix_succ]
    have hm : Measurable (fun v : Option (RecordedQueueRun.RunState p.K) × Estimate p =>
        v.1.map (fun S => estimateStep rate S true v.2)) := by
      apply measurable_from_prod_countable_right
      intro state
      cases state with
      | none => exact measurable_const
      | some S =>
        exact LaterAssignmentFullOutputMeasurability.measurable_some_of_measurable _
          ((measurable_estimateStep rate).comp
            ((measurable_const.prodMk measurable_const).prodMk measurable_id))
    exact hm.comp ((ih (by omega)).prodMk ((measurable_pi_apply
      (⟨⟨s.val + n, by omega⟩, by change s.val ≤ s.val + n; omega,
          by change s.val + n < q.val; omega⟩ : EstimateDates s q)).comp measurable_snd))

/-- Full numerical PRE reconstructed from the single estimate-history schema. -/
def episodeReplay (s q : Fin p.T)
    (h : (Source p × List (LogicalCell p rate)) × (EstimateDates s q → Estimate p)) :
    Option (RecordedQueueRun.RunState p.K) :=
  replayPrefix rate rewards C_star C_h s q h (q.val - s.val) le_rfl

omit control0 in
theorem measurable_episodeReplay (s q : Fin p.T) :
    Measurable (episodeReplay rate rewards C_star C_h s q) :=
  measurable_replayPrefix rate rewards C_star C_h s q _ _

/-- The fixed-anchor slow-set mass read from the strict numerical seed and
current reconstructed PRE. Optional absence contributes zero cylinder mass;
no artificial queue state or anchor is inserted. -/
def episodeMass (s q : Fin p.T)
    (h : (Source p × List (LogicalCell p rate)) × (EstimateDates s q → Estimate p))
    (U : SlowSet p) : ℝ≥0∞ :=
  match ReferencePostInvocationNoncallGeometry.prefixNumerical rate rewards C_star C_h s.castSucc h.1.1,
      episodeReplay rate rewards C_star C_h s q h with
  | some A, some S => RecordedSlowRefresh.recordedSlowPMF p Q S
      (RecordedQueueRun.scoreWeight Q A) (RecordedSlowRefresh.scoreWeight_pos Q A) U
  | _, _ => 0

omit control0 in
theorem measurable_episodeMass (s q : Fin p.T) (U : SlowSet p) :
    Measurable (fun h => episodeMass rate rewards C_star C_h s q h U) := by
  let f : Option (RecordedQueueRun.RunState p.K) × Option (RecordedQueueRun.RunState p.K) → ℝ≥0∞ :=
    fun v => match v.1, v.2 with
    | some A, some S => RecordedSlowRefresh.recordedSlowPMF p Q S
        (RecordedQueueRun.scoreWeight Q A) (RecordedSlowRefresh.scoreWeight_pos Q A) U
    | _, _ => 0
  exact (measurable_of_countable f).comp
    (((ReferencePostInvocationPrefixLocality.measurable_prefixNumerical
      rate rewards C_star C_h s.castSucc).comp measurable_fst.fst).prodMk
        (measurable_episodeReplay rate rewards C_star C_h s q))

open ReferenceOriginalCalendarEpisodeChronology in
/-- Every actual episode, at every date before its operative endpoint, has
its whole numerical PRE determined by the strict start prefix and past raw
estimates. Coverage of all intermediate dates is produced by the original
record partition. No incoming-clear assumption is needed for this replay. -/
theorem ae_episodeReplay_of_cover (ids : Option (CompletePublicTable.IDArray p)) :
    ∀ᵐ w ∂ids.elim
      (ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalLaw rate rewards C_star C_h control0)
      (ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDTerminalLaw rate rewards C_star C_h control0),
      ∀ (rho : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate (Z w) rewards C_star C_h).length) (q : Fin p.T),
        let r := (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate (Z w) rewards C_star C_h)[rho.val]
        EpisodeCovers r q →
          episodeReplay rate rewards C_star C_h r.input.time q
            (estimateHistory rate rewards C_star C_h control0 r.input.time q w) =
          ReferencePostInvocationNoncallGeometry.prefixNumerical rate rewards C_star C_h q.castSucc (Z w) := by
  filter_upwards [ae_estimate_numerical_update rate rewards C_star C_h control0 ids] with w hw
  intro rho q
  dsimp only
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate (Z w) rewards C_star C_h
  let s := R[rho.val].input.time
  intro hcover
  change EpisodeCovers R[rho.val] q at hcover
  have hsq : s.val ≤ q.val := hcover.2.1
  have fold_eq (n : ℕ) (hn : n ≤ q.val - s.val) :
      replayPrefix rate rewards C_star C_h s q
        (estimateHistory rate rewards C_star C_h control0 s q w) n hn =
      ReferencePostInvocationNoncallGeometry.prefixNumerical rate rewards C_star C_h
        ⟨s.val + n, by omega⟩ (Z w) := by
    induction n with
    | zero =>
      exact (ReferencePostInvocationPrefixLocality.prefixNumerical_sourcePrefix
        rate rewards C_star C_h control0 s.castSucc s.val le_rfl (Z w)).symm
    | succ n ih =>
      let v : Fin p.T := ⟨s.val + n, by omega⟩
      have hv : EpisodeCovers R[rho.val] v := ⟨hcover.1, by dsimp only [v]; omega,
        by have hg := hcover.2.2; change q.val + 1 < FollowerCutoffScan.gridBoundary p rate.eta.val s at hg;
           change s.val + n + 1 < FollowerCutoffScan.gridBoundary p rate.eta.val s; omega⟩
      have hen := (nominalEnabled_iff_unique_episode rate rewards C_star C_h (Z w) v).mpr
        ⟨rho, hv, fun other ho => complete_episode_interval_at_most_one
          rate rewards C_star C_h (Z w) v other rho ho hv⟩
      obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp
        ((currentMark_isSome_iff rate rewards C_star C_h control0 v w).mpr hen)
      obtain ⟨_, hb, ha, _, hstep, _⟩ := hw v e he
      rw [replayPrefix_succ, ih (by omega)]
      change (ReferencePostInvocationNoncallGeometry.prefixNumerical
        rate rewards C_star C_h v.castSucc (Z w)).map _ = _
      rw [hb, Option.map_some]
      exact (congrArg some hstep.symm).trans ha.symm
  have heq := fold_eq (q.val - s.val) le_rfl
  have hq : (⟨s.val + (q.val - s.val), by omega⟩ : Fin (p.T + 1)) = q.castSucc :=
    Fin.ext (Nat.add_sub_of_le hsq)
  simpa only [episodeReplay, hq] using heq

open ReferenceOriginalCalendarEpisodeChronology in
/-- The opportunity's actual original birth covers every date in its fixed
interval. Both its unique suffix origin and unique terminal mark are produced. -/
theorem episodeStartEvent_unique_coverage (s q : Fin p.T) (w : Omega)
    (hs : w ∈ episodeStartEvent rate rewards C_star C_h control0 s)
    (hsq : s.val ≤ q.val)
    (hq : q.val + 1 < FollowerCutoffScan.gridBoundary p rate.eta.val s) :
    (∃! rho : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate (Z w) rewards C_star C_h).length,
      EpisodeCovers (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate (Z w) rewards C_star C_h)[rho.val] q) ∧
    ∃! e : LogicalCell p rate, currentMark rate rewards C_star C_h control0 q w = some e := by
  obtain ⟨rho, ht, hb⟩ := sourceStartEvent_episode_birth rate rewards C_star C_h s (Z w) hs
  have hcover : EpisodeCovers (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate (Z w) rewards C_star C_h)[rho.val] q := ⟨hb, ht ▸ hsq, ht ▸ hq⟩
  have huniq := (nominalEnabled_iff_unique_episode rate rewards C_star C_h (Z w) q).mpr
    ⟨rho, hcover, fun other ho => complete_episode_interval_at_most_one
      rate rewards C_star C_h (Z w) q other rho ho hcover⟩
  refine ⟨(nominalEnabled_iff_unique_episode rate rewards C_star C_h (Z w) q).mp huniq, ?_⟩
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp
    ((currentMark_isSome_iff rate rewards C_star C_h control0 q w).mpr huniq)
  exact ⟨e, he, fun f hf => Option.some.inj (hf.symm.trans he)⟩

/-- Episode-wide replay on every actual start, for BOTH original terminal
laws. The caller supplies only calendar membership, never a desired history,
state, mark, successful sampler, or coverage premise. -/
theorem ae_episodeReplay (ids : Option (CompletePublicTable.IDArray p)) :
    ∀ᵐ w ∂ids.elim
      (ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalLaw rate rewards C_star C_h control0)
      (ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDTerminalLaw rate rewards C_star C_h control0),
      ∀ (s q : Fin p.T), w ∈ episodeStartEvent rate rewards C_star C_h control0 s →
        s.val ≤ q.val → q.val + 1 < FollowerCutoffScan.gridBoundary p rate.eta.val s →
          episodeReplay rate rewards C_star C_h s q
            (estimateHistory rate rewards C_star C_h control0 s q w) =
          ReferencePostInvocationNoncallGeometry.prefixNumerical rate rewards C_star C_h q.castSucc (Z w) := by
  filter_upwards [ae_episodeReplay_of_cover rate rewards C_star C_h control0 ids] with w hw
  intro s q hs hsq hq
  obtain ⟨rho, ht, hb⟩ := sourceStartEvent_episode_birth rate rewards C_star C_h s (Z w) hs
  have h := hw rho q ⟨hb, ht ▸ hsq, ht ▸ hq⟩
  rw [ht] at h
  exact h

open ReferenceOriginalCalendarEpisodeChronology in
/-- The fixed physical episode anchor is the weight of the SAME strict seed
stored by the history observer. Current PRE-clear produces the earlier clear
seed; physical weights after overflow are never identified with stopped ones. -/
theorem episode_anchor_of_cover (z : Source p) (q : Fin p.T)
    (rho : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).length)
    (P : ReferenceActivePhysicalStep.Payload rate)
    (hcover : EpisodeCovers (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[rho.val] q)
    (hb : ReferenceAssignmentPayloadPersistence.InstallationBirth
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[rho.val] P)
    (hclear : (ReferencePostInvocationNoncallGeometry.prefixNumerical
      rate rewards C_star C_h q.castSucc z).any (fun S => !S.overflow) = true) :
    let s := (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[rho.val].input.time
    ∃ S : RecordedQueueRun.RunState p.K,
      ReferencePostInvocationNoncallGeometry.prefixNumerical rate rewards C_star C_h s.castSucc
        (sourcePrefix control0 s.val z) = some S ∧
      S.overflow = false ∧ P.anchor = RecordedQueueRun.scoreWeight Q S := by
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let s := R[rho.val].input.time
  let start := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  let hl := complete_record_launch rate rewards C_star C_h z rho
  let W := ReferenceActualCollectionHiddenRefreshPath.actualOriginalWord rate rewards C_star C_h z hl
  have ht : s.val = start + rho.val :=
    ReferenceAssignmentFollowerMassSteps.complete_record_time rate rewards C_star C_h z rho
  have hs : start ≤ s.val := by omega
  have hp := ReferencePostInvocationNoncallGeometry.prefixNumerical_actualWord
    rate rewards C_star C_h q.castSucc z hl (hs.trans hcover.2.1)
  rw [hp, Option.any_some, Bool.not_eq_true'] at hclear
  obtain ⟨hseed, hanchor, _⟩ := complete_episode_pre_clear_restoration
    rate rewards C_star C_h z q rho P hcover hb hclear
  refine ⟨RecordedQueueRun.run Q (W.take rho.val), ?_, hseed, hanchor⟩
  rw [← ReferencePostInvocationPrefixLocality.prefixNumerical_sourcePrefix
    rate rewards C_star C_h control0 s.castSucc s.val le_rfl z,
    ReferencePostInvocationNoncallGeometry.prefixNumerical_actualWord
      rate rewards C_star C_h s.castSucc z hl hs]
  change some (RecordedQueueRun.run Q (W.take (s.val - start))) = _
  rw [ht, Nat.add_sub_cancel_left]

end ChronologicalReplay

/-- The actual incoming-clear retention event inside the episode's fixed
source endpoint. Only PRE is tested; numerical POST is deliberately absent. -/
def retainedEvent (s q : Fin p.T) : Set Omega :=
  {w | s.val ≤ q.val ∧ q.val + 1 < FollowerCutoffScan.gridBoundary p rate.eta.val s ∧
    (ReferencePostInvocationNoncallGeometry.prefixNumerical rate rewards C_star C_h q.castSucc (Z w)).any
      (fun S => !S.overflow) = true}

theorem measurableSet_retainedEvent (s q : Fin p.T) :
    MeasurableSet (retainedEvent rate rewards C_star C_h control0 s q) := by
  have hp : Measurable (fun w : Omega =>
      (ReferencePostInvocationNoncallGeometry.prefixNumerical rate rewards C_star C_h q.castSucc (Z w)).any
        (fun S => !S.overflow)) :=
    (measurable_of_countable (fun o : Option (RecordedQueueRun.RunState p.K) =>
      o.any (fun S : RecordedQueueRun.RunState p.K => !S.overflow))).comp
        ((ReferencePostInvocationPrefixLocality.measurable_prefixNumerical rate rewards C_star C_h q.castSucc).comp
          (ReferenceExhaustiveGeneratedCalendarSourceLaw.measurable_terminalSource rate rewards C_star C_h control0))
  exact (MeasurableSet.const _).inter ((MeasurableSet.const _).inter
    ((measurableSet_singleton true).preimage hp))

/-- At a present actual mark, retention is exactly the incoming mark flag.
The detecting overflow UPDATE satisfies this event whenever its PRE is clear. -/
theorem ae_retainedEvent_currentMark (ids : Option (CompletePublicTable.IDArray p)) :
    ∀ᵐ w ∂ids.elim
      (ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalLaw rate rewards C_star C_h control0)
      (ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDTerminalLaw rate rewards C_star C_h control0),
      ∀ (s q : Fin p.T) (e : LogicalCell p rate), currentMark rate rewards C_star C_h control0 q w = some e →
        (w ∈ retainedEvent rate rewards C_star C_h control0 s q ↔
          s.val ≤ q.val ∧ q.val + 1 < FollowerCutoffScan.gridBoundary p rate.eta.val s ∧ e.before.overflow = false) := by
  filter_upwards [ae_estimate_numerical_update rate rewards C_star C_h control0 ids] with w hw
  intro s q e he
  have hp := (hw q e he).2.1
  simp only [retainedEvent, Set.mem_ofPred_eq, hp, Option.any_some, Bool.not_eq_true']

/-- The sigma field generated by precisely the before-draw history and the
strictly earlier estimates. It is a sub-sigma field of the original raw
sample's Borel field, rather than supplied filtration data. -/
abbrev estimateHistorySpace (s q : Fin p.T) : MeasurableSpace Omega :=
  MeasurableSpace.comap (estimateHistory rate rewards C_star C_h control0 s q) inferInstance

/-- All PRE registers, record lists and the overflow flag have a version
measurable in exactly the estimate-generated sigma field. -/
theorem measurable_episodeReplay_history (s q : Fin p.T) :
    Measurable[estimateHistorySpace rate rewards C_star C_h control0 s q]
      (fun w => episodeReplay rate rewards C_star C_h s q
        (estimateHistory rate rewards C_star C_h control0 s q w)) :=
  (measurable_episodeReplay rate rewards C_star C_h s q).comp
    (comap_measurable (estimateHistory rate rewards C_star C_h control0 s q))

/-- Revealing a longer estimate prefix enlarges exactly this history field. -/
theorem estimateHistorySpace_mono (s q r : Fin p.T) (hqr : q.val ≤ r.val) :
    estimateHistorySpace rate rewards C_star C_h control0 s q ≤
      estimateHistorySpace rate rewards C_star C_h control0 s r := by
  let project : ((Source p × List (LogicalCell p rate)) × (EstimateDates s r → Estimate p)) →
      ((Source p × List (LogicalCell p rate)) × (EstimateDates s q → Estimate p)) :=
    fun h => (h.1, fun v => h.2 ⟨v.val, v.property.1, v.property.2.trans_le hqr⟩)
  have hp : Measurable project := measurable_fst.prodMk (measurable_pi_iff.mpr fun v =>
    (measurable_pi_apply (⟨v.val, v.property.1, v.property.2.trans_le hqr⟩ : EstimateDates s r)).comp measurable_snd)
  exact MeasurableSpace.comap_le_comap_of_eq_comp project hp rfl

/-- The actual opportunity is already decided in every estimate-history
field for this start, without revealing the current initial draw. -/
theorem measurableSet_episodeStartEvent_history (s q : Fin p.T) :
    MeasurableSet[estimateHistorySpace rate rewards C_star C_h control0 s q]
      (episodeStartEvent rate rewards C_star C_h control0 s) := by
  rw [episodeStartEvent_eq_history_preimage]
  exact ((measurableSet_sourceStartEvent rate rewards C_star C_h control0 s).preimage measurable_fst).preimage
    (measurable_fst.comp (comap_measurable (estimateHistory rate rewards C_star C_h control0 s q)))

/-- The measurable incoming-clear gate computed solely from E. It tests
PRE and therefore retains the first detecting overflow UPDATE. -/
def historyRetained (s q : Fin p.T) : Set
    ((Source p × List (LogicalCell p rate)) × (EstimateDates s q → Estimate p)) :=
  {h | s.val ≤ q.val ∧ q.val + 1 < FollowerCutoffScan.gridBoundary p rate.eta.val s ∧
    (episodeReplay rate rewards C_star C_h s q h).any (fun S => !S.overflow) = true}

omit control0 in
theorem measurableSet_historyRetained (s q : Fin p.T) :
    MeasurableSet (historyRetained rate rewards C_star C_h s q) :=
  (MeasurableSet.const _).inter ((MeasurableSet.const _).inter
    ((measurableSet_singleton true).preimage
      ((measurable_of_countable (fun o : Option (RecordedQueueRun.RunState p.K) =>
        o.any (fun S : RecordedQueueRun.RunState p.K => !S.overflow))).comp
          (measurable_episodeReplay rate rewards C_star C_h s q))))

/-- On every actual episode start, the retained event has this E-measurable
version under BOTH terminal laws, simultaneously at every calendar date. -/
theorem ae_retainedEvent_history (ids : Option (CompletePublicTable.IDArray p)) :
    ∀ᵐ w ∂ids.elim
      (ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalLaw rate rewards C_star C_h control0)
      (ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDTerminalLaw rate rewards C_star C_h control0),
      ∀ (s q : Fin p.T), w ∈ episodeStartEvent rate rewards C_star C_h control0 s →
        (w ∈ retainedEvent rate rewards C_star C_h control0 s q ↔
          estimateHistory rate rewards C_star C_h control0 s q w ∈
            historyRetained rate rewards C_star C_h s q) := by
  filter_upwards [ae_episodeReplay rate rewards C_star C_h control0 ids] with w hw
  intro s q hs
  by_cases hsq : s.val ≤ q.val
  · by_cases hq : q.val + 1 < FollowerCutoffScan.gridBoundary p rate.eta.val s
    · simp only [retainedEvent, historyRetained, Set.mem_ofPred_eq, hw s q hs hsq hq]
    · simp only [retainedEvent, historyRetained, Set.mem_ofPred_eq, hq, false_and, and_false]
  · simp only [retainedEvent, historyRetained, Set.mem_ofPred_eq, hsq, false_and]

open ReferenceOriginalCalendarEpisodeChronology in
/-- The history-computed mass equals the prescribed PMF at actual numerical
PRE. The mark, original birth, payload and clear strict-prefix seed are all
produced here; no desired state, anchor, coverage or sampling success is an
input. This identifies the mass, without asserting a conditional slow-set law. -/
theorem ae_episodeMass_actual (ids : Option (CompletePublicTable.IDArray p)) :
    ∀ᵐ w ∂ids.elim
      (ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalLaw rate rewards C_star C_h control0)
      (ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDTerminalLaw rate rewards C_star C_h control0),
      ∀ (s q : Fin p.T), w ∈ episodeStartEvent rate rewards C_star C_h control0 s →
        w ∈ retainedEvent rate rewards C_star C_h control0 s q →
        ∃ (e : LogicalCell p rate)
          (rho : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords rate (Z w) rewards C_star C_h).length)
          (P : ReferenceActivePhysicalStep.Payload rate) (A : RecordedQueueRun.RunState p.K),
          currentMark rate rewards C_star C_h control0 q w = some e ∧
          (ReferenceCompletePhysicalHistory.completeSuffixRecords rate (Z w) rewards C_star C_h)[rho.val].input.time = s ∧
          ReferenceAssignmentPayloadPersistence.InstallationBirth
            (ReferenceCompletePhysicalHistory.completeSuffixRecords rate (Z w) rewards C_star C_h)[rho.val] P ∧
          ReferencePostInvocationNoncallGeometry.prefixNumerical rate rewards C_star C_h s.castSucc
            (startHistory rate rewards C_star C_h control0 s w).1 = some A ∧
          A.overflow = false ∧ P.anchor = RecordedQueueRun.scoreWeight Q A ∧
          ∀ U : SlowSet p, episodeMass rate rewards C_star C_h s q
            (estimateHistory rate rewards C_star C_h control0 s q w) U =
            RecordedSlowRefresh.recordedSlowPMF p Q e.before P.anchor P.anchor_pos U := by
  filter_upwards [ae_episodeReplay rate rewards C_star C_h control0 ids,
    ae_estimate_numerical_update rate rewards C_star C_h control0 ids] with w hrep hup
  intro s q hs hret
  obtain ⟨hsq, hq, hclear⟩ := hret
  obtain ⟨e, he, _⟩ := (episodeStartEvent_unique_coverage rate rewards C_star C_h control0 s q w hs hsq hq).2
  obtain ⟨rho, ht, hbirth⟩ := sourceStartEvent_episode_birth rate rewards C_star C_h s (Z w) hs
  obtain ⟨P, hP, _⟩ := episode_birth_payload_unique _ hbirth
  have hcover : EpisodeCovers (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate (Z w) rewards C_star C_h)[rho.val] q := ⟨hbirth, ht ▸ hsq, ht ▸ hq⟩
  obtain ⟨A, hA, hAc, hanchor⟩ := episode_anchor_of_cover
    rate rewards C_star C_h control0 (Z w) q rho P hcover hP hclear
  rw [ht] at hA
  refine ⟨e, rho, P, A, he, ht, hP, hA, hAc, hanchor, ?_⟩
  intro U
  change ReferencePostInvocationNoncallGeometry.prefixNumerical rate rewards C_star C_h s.castSucc
    (estimateHistory rate rewards C_star C_h control0 s q w).1.1 = some A at hA
  rw [episodeMass, hA, hrep s q hs hsq hq, (hup q e he).2.1]
  simp only [hanchor]

section CommonEstimateKernel

attribute [local instance]
  ReferenceRankInstallationRecorderFoundation.outcomeMeasurableSpace
  ReferenceRankInstallationRecorderFoundation.outcomeDiscreteMeasurableSpace
  ReferenceRankInstallationRecorderFoundation.outcomeOptionMeasurableSpace
  ReferenceRankInstallationRecorderFastLaw.reservedMarkerMeasurableSpace

omit C_star C_h control0 in
/-- The common CALL estimate for one recorder outcome, with the actual
frozen rates and complete fixed grid reward table. -/
def callMarkerEstimate (q : Fin p.T) (v : ReferenceDownReception.ChoiceTimeView p rate.eta)
    (S : RecordedQueueRun.RunState p.K) (o : Option (Fin p.K)) (i : Fin p.K) : ℝ :=
  if S.overflow then 0 else if o = some i then
    (((rewards q i).val : ℝ) / (D p : ℝ)) / v.payload.rate i else 0

omit C_star C_h control0 in
/-- Estimate read from the complete accepted numerical CALL update. Its
incoming overflow gate comes from that update, not from physical markers. -/
def callUpdateEstimate (q : Fin p.T) (v : ReferenceDownReception.ChoiceTimeView p rate.eta)
    (u : ReferenceRankInstallationCommonUpdateJointLaw.PairUpdate p) (i : Fin p.K) : ℝ :=
  match u.2 with
  | none => 0
  | some n => if n.beforeOverflow then 0 else if u.1.1 = some (some i) then
      (((rewards q i).val : ℝ) / (D p : ℝ)) / v.payload.rate i else 0

omit C_star C_h control0 in
/-- The evaluated complete numerical CALL kernel has the common raw-estimate
law. Only the recorder marginal is used; FAST remains correlated with it.
This kernel identity still needs the episode-history tower to establish
conditional slow-set preservation. -/
theorem commonUpdateKernel_estimate_map (q : Fin p.T)
    (v : ReferenceDownReception.ChoiceTimeView p rate.eta)
    (valid : CoordinatorLocalArmChoice.ChoiceInputsValid v.payload v.cutoff q v.complementWeights)
    (S : RecordedQueueRun.RunState p.K) :
    (ReferenceRankInstallationCommonUpdateJointLaw.commonUpdateKernel rate rewards q v valid
      (some (S.registers, S.overflow, S.records))).map (callUpdateEstimate rate rewards q v) =
    (RecordedRoundMoments.recordingOutcomePMF
      (SnapshotRecordingKernel.recordingRates p rate.eta.val rate.eta.property rate.sourceCap
        v.payload.anchor v.payload.anchor_pos)).toMeasure.map (callMarkerEstimate rate rewards q v S) := by
  let output := ReferenceRankInstallationSourceKernelComposition.installationRecorderFastOutputKernel rate q v valid
  let before := some (S.registers, S.overflow, S.records)
  let outer : Option (Option (Fin p.K)) → Estimate p := fun o => callMarkerEstimate rate rewards q v S o.join
  have he : Measurable (callUpdateEstimate rate rewards q v) := measurable_of_countable _
  have ho : Measurable outer := measurable_of_countable _
  have hm := ReferenceRankInstallationCommonUpdateJointLaw.measurable_commonUpdateKernelMap rate rewards q v before
  have hpoint : (fun z : ReferenceRankInstallationCommonUpdateJointLaw.Pair p =>
      callUpdateEstimate rate rewards q v (z,
        ReferenceRankInstallationCommonUpdateJointLaw.updateFromPair rate rewards q v before z)) =
      outer ∘ Prod.fst := by
    funext z i
    rcases z with ⟨o, j⟩
    cases o <;> cases hs : S.overflow <;>
      simp only [callUpdateEstimate, callMarkerEstimate, outer, before,
        ReferenceRankInstallationCommonUpdateJointLaw.updateFromPair,
        ReferenceRankInstallationCommonUpdateJointLaw.rawArrivalsFromPair,
        ReferenceRankInstallationPostUpdateProposalLaw.numericalUpdateFromReadouts,
        ReferenceFirstLivePostUpdateProposalLaw.numericalUpdateFields,
        Option.map_none, Option.map_some, Option.bind_some, Option.join_none, Option.join_some,
        Function.comp_apply, hs, Bool.false_eq_true, ite_true, ite_false, reduceCtorEq, Option.some.injEq]
  change (output.map (fun z => (z,
    ReferenceRankInstallationCommonUpdateJointLaw.updateFromPair rate rewards q v before z))).map _ = _
  rw [Measure.map_map he hm]
  change output.map (fun z => callUpdateEstimate rate rewards q v
    (z, ReferenceRankInstallationCommonUpdateJointLaw.updateFromPair rate rewards q v before z)) = _
  rw [hpoint, ← Measure.map_map ho measurable_fst,
    (ReferenceRankInstallationSourceKernelComposition.installationRecorderFastOutputKernel_marginals rate q v valid).1,
    Measure.map_map ho (measurable_of_countable (fun o : Option (Fin p.K) => some o))]
  rfl

end CommonEstimateKernel

end Bandits.Support.ReferenceGeneratedCalendarEpisodeSlowLaw
