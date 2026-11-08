/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedCalendarEpisodeTransitionCore
public import Bandits.Support.ReferenceGeneratedCalendarLaterCallFast
public import Bandits.Support.ReferenceGeneratedCalendarLaterNoncallFast
public import Bandits.Support.ReferenceGeneratedCalendarPrefixCollectionFast
public import Bandits.Support.ReferenceGeneratedCalendarPrefixLiveFast
public import Bandits.Support.ReferenceGeneratedCalendarRetainedFastCore

/-!
# Retained terminal FAST assembly

Sources: ZIP4 `04_slow_fast_learner.tex:16-37,96-114,140-215,323-390`
and `06_interruptions.tex:391-426`.

All component measures below keep their original masses. The current slow set
is retained as an observation; its distribution is not prescribed.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal Classical BigOperators
open Bandits.Support ConstructorDimensions
open ReferenceFirstLiveChronologicalPrefixFoundation
open ReferenceFirstLiveChronologicalPrefixMeasurability
open ReferenceGeneratedCalendarEpisodeSlowLaw
open ReferenceGeneratedCalendarEpisodeHistoryTransport
open ReferenceGeneratedCalendarEpisodePrefixRecombination
open ReferenceGeneratedCalendarEpisodeTransitionCore
open ReferenceGeneratedCalendarRetainedFastCore
open ReferenceGeneratedRankCalendarFoundation
open ReferenceGeneratedCalendarResidualBlock
open ReferenceGeneratedCalendarPathAgreement
open ReferenceGeneratedCalendarMarkedPath
open ReferenceGeneratedCalendarNativePreservation
open ReferencePostInvocationNoncallGeometry
open ReferenceSourcePrefixHistoryFiltration (sourcePrefix)
open CanonicalFastSampling (FastArm)

namespace Bandits.Support.ReferenceGeneratedCalendarRetainedFastTerminalLaw

variable {p : ConstructorDimensions.Parameters}

local instance sourceMeasurableSpace : MeasurableSpace (BootstrapPrivateRoundStreams.SourceInput p) := by
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

local notation "Omega" => ReferenceExhaustiveGeneratedCalendarSourceLaw.Omega rate rewards C_star C_h
local notation "Q" => ReferenceFirstLaunchNumericalCell.queueParameters rate
local notation "Lambda" ids => Option.elim ids
  (ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalLaw rate rewards C_star C_h control0)
  (ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDTerminalLaw rate rewards C_star C_h control0)

omit control0 in
def historyDomain (s q : Fin p.T) : Set (History rate s q) :=
  {h | h.1.1 ∈ sourceStartEvent rate rewards C_star C_h s ∧
    h ∈ sourceHistoryRetained rate rewards C_star C_h s q}

include control0 in
private theorem measurableSet_historyDomain (s q : Fin p.T) :
    MeasurableSet (historyDomain rate rewards C_star C_h s q) :=
  ((measurableSet_sourceStartEvent rate rewards C_star C_h control0 s).preimage
    measurable_fst.fst).inter (measurableSet_sourceHistoryRetained rate rewards C_star C_h s q)

omit control0 in
def actualTest (s q : Fin p.T)
    (Phi : History rate s q × (SlowSet p × Fin p.K) → ℝ≥0∞) (y : History rate s q × (Estimate p × Option (LogicalCell p rate))) : ℝ≥0∞ :=
  if y.1 ∈ historyDomain rate rewards C_star C_h s q then
    y.2.2.elim 0 (fun e => Phi (y.1, (e.slowSet, e.fastArm))) else 0

omit control0 in
def meanTest (s q : Fin p.T)
    (Phi : History rate s q × (SlowSet p × Fin p.K) → ℝ≥0∞) (y : History rate s q × (Estimate p × Option (LogicalCell p rate))) : ℝ≥0∞ :=
  if y.1 ∈ historyDomain rate rewards C_star C_h s q then
    y.2.2.elim 0 (fun e => historyFastTest rate rewards C_star C_h s q Phi y.1 e.slowSet) else 0

omit rewards C_star C_h control0 in
private theorem measurable_optional {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [Zero Y] (f : LogicalCell p rate × X → Y) (hf : Measurable f) :
    Measurable (fun v : Option (LogicalCell p rate) × X =>
      v.1.elim 0 (fun e => f (e, v.2))) := by
  have h := (hf.sumElim (measurable_const : Measurable (fun _ : PUnit × X => (0 : Y)))).comp
    (MeasurableEquiv.sumProdDistrib (LogicalCell p rate) PUnit X).measurable_toFun
  have hp := h.comp (((comap_measurable (Equiv.optionEquivSumPUnit (LogicalCell p rate))).comp
    measurable_fst).prodMk measurable_snd)
  convert hp using 1
  funext v
  rcases v with ⟨e, x⟩
  cases e <;> rfl

include control0 in
private theorem measurable_actualTest (s q : Fin p.T)
    (Phi : History rate s q × (SlowSet p × Fin p.K) → ℝ≥0∞) (hPhi : Measurable Phi) :
    Measurable (actualTest rate rewards C_star C_h s q Phi) := by
  have hU : Measurable (fun e : LogicalCell p rate => e.slowSet) :=
    measurable_logicalCell_slowSet.mono le_rfl le_top
  have hf := measurable_optional rate
    (fun v : LogicalCell p rate × History rate s q => Phi (v.2, (v.1.slowSet, v.1.fastArm)))
    (hPhi.comp (measurable_snd.prodMk ((hU.comp measurable_fst).prodMk
      (measurable_logicalCell_fastArm.comp measurable_fst))))
  exact (hf.comp (measurable_snd.snd.prodMk measurable_fst)).ite
    ((measurableSet_historyDomain rate rewards C_star C_h control0 s q).preimage measurable_fst)
    measurable_const

include control0 in
private theorem measurable_meanTest (s q : Fin p.T)
    (Phi : History rate s q × (SlowSet p × Fin p.K) → ℝ≥0∞) (hPhi : Measurable Phi) :
    Measurable (meanTest rate rewards C_star C_h s q Phi) := by
  have hU : Measurable (fun e : LogicalCell p rate => e.slowSet) :=
    measurable_logicalCell_slowSet.mono le_rfl le_top
  have hf := measurable_optional rate
    (fun v : LogicalCell p rate × History rate s q =>
      historyFastTest rate rewards C_star C_h s q Phi v.2 v.1.slowSet)
    ((measurable_historyFastTest rate rewards C_star C_h s q Phi hPhi).comp
      (measurable_snd.prodMk (hU.comp measurable_fst)))
  exact (hf.comp (measurable_snd.snd.prodMk measurable_fst)).ite
    ((measurableSet_historyDomain rate rewards C_star C_h control0 s q).preimage measurable_fst)
    measurable_const

omit control0 in
private theorem gate_split (s q : Fin p.T) (h : History rate s q) (P : Prop) [Decidable P]
    (a : ℝ≥0∞) :
    (if P then if h ∈ historyDomain rate rewards C_star C_h s q then a else 0 else 0) =
      if P ∧ h.1.1 ∈ sourceStartEvent rate rewards C_star C_h s ∧
        h ∈ sourceHistoryRetained rate rewards C_star C_h s q then a else 0 := by
  by_cases hp : P <;> by_cases hs : h.1.1 ∈ sourceStartEvent rate rewards C_star C_h s <;>
    by_cases hr : h ∈ sourceHistoryRetained rate rewards C_star C_h s q <;>
    simp only [historyDomain, Set.mem_ofPred_eq, hp, hs, hr, and_true, and_false,
      ite_true, ite_false]

/-- The two accepted later branch laws exhaust the actual Boolean call flag.
The last physical date is included without requiring a successor in `Fin T`. -/
theorem calendar_later_fast_test (ids : Option (CompletePublicTable.IDArray p))
    (b : Bool) (u t s : Fin p.T) (k : ℕ)
    (hk : t.val + 1 + k < p.T) (hs : s.val ≤ t.val + 1 + k)
    (Phi : History rate s ⟨t.val + 1 + k, hk⟩ × (SlowSet p × Fin p.K) → ℝ≥0∞)
    (hPhi : Measurable Phi) :
    (∫⁻ w, actualTest rate rewards C_star C_h s ⟨t.val + 1 + k, hk⟩ Phi
        (calendarStepSourceJoint rate rewards C_star C_h control0 b u t s k hk w)
      ∂ids.elim (calendarLaw rate rewards C_star C_h control0 b u t (k + 1) (by omega))
        (fun id => (CompletePublicTable.idArrayMeasure p {id})⁻¹ •
          (calendarLaw rate rewards C_star C_h control0 b u t (k + 1) (by omega)).restrict
            ((calendarCurrentSource rate rewards C_star C_h control0 b u t (k + 1) (by omega)) ⁻¹'
              ReferenceFixedIDSourceSection.fixedIDSourceSection id))) =
    ∫⁻ w, meanTest rate rewards C_star C_h s ⟨t.val + 1 + k, hk⟩ Phi
        (calendarStepSourceJoint rate rewards C_star C_h control0 b u t s k hk w)
      ∂ids.elim (calendarLaw rate rewards C_star C_h control0 b u t (k + 1) (by omega))
        (fun id => (CompletePublicTable.idArrayMeasure p {id})⁻¹ •
          (calendarLaw rate rewards C_star C_h control0 b u t (k + 1) (by omega)).restrict
            ((calendarCurrentSource rate rewards C_star C_h control0 b u t (k + 1) (by omega)) ⁻¹'
              ReferenceFixedIDSourceSection.fixedIDSourceSection id)) := by
  let q : Fin p.T := ⟨t.val + 1 + k, hk⟩
  let gamma : Measure (CalendarSample rate rewards C_star C_h b u t k ×
      AssignmentParameterFibreKernel.AssignmentVector p) := ids.elim (calendarLaw rate rewards C_star C_h control0 b u t (k + 1) (by omega))
    (fun id => (CompletePublicTable.idArrayMeasure p {id})⁻¹ •
      (calendarLaw rate rewards C_star C_h control0 b u t (k + 1) (by omega)).restrict
        ((calendarCurrentSource rate rewards C_star C_h control0 b u t (k + 1) (by omega)) ⁻¹'
          ReferenceFixedIDSourceSection.fixedIDSourceSection id))
  let A := fun w => actualTest rate rewards C_star C_h s q Phi
    (calendarStepSourceJoint rate rewards C_star C_h control0 b u t s k hk w)
  let B := fun w => meanTest rate rewards C_star C_h s q Phi
    (calendarStepSourceJoint rate rewards C_star C_h control0 b u t s k hk w)
  let flag := fun w : CalendarSample rate rewards C_star C_h b u t k ×
      AssignmentParameterFibreKernel.AssignmentVector p =>
    calendarCallFlag rate rewards C_star C_h control0 b u t k (by omega) w.1
  have hA : Measurable A := (measurable_actualTest rate rewards C_star C_h control0 s q Phi hPhi).comp
    (measurable_calendarStepSourceJoint rate rewards C_star C_h control0 b u t s k hk)
  have hB : Measurable B := (measurable_meanTest rate rewards C_star C_h control0 s q Phi hPhi).comp
    (measurable_calendarStepSourceJoint rate rewards C_star C_h control0 b u t s k hk)
  have hf : Measurable flag := (measurable_calendarCallFlag rate rewards C_star C_h control0 b u t k (by omega)).comp
    measurable_fst
  have hcall := ReferenceGeneratedCalendarLaterCallFast.calendar_call_fast_test
    rate rewards C_star C_h control0 ids b u t s k hk hs Phi hPhi
  have hnon := ReferenceGeneratedCalendarLaterNoncallFast.calendarLaw_later_noncall_fast_test
    rate rewards C_star C_h control0 ids b u t s k hk hs Phi hPhi
  have hsplit (f : CalendarSample rate rewards C_star C_h b u t k ×
      AssignmentParameterFibreKernel.AssignmentVector p → ℝ≥0∞) :
      f = (fun w => if flag w = true then f w else 0) +
        (fun w => if flag w = false then f w else 0) := by
    funext w
    change f w = (if flag w = true then f w else 0) + (if flag w = false then f w else 0)
    cases flag w <;> simp only [Bool.false_eq_true, Bool.true_eq_false,
      ite_false, ite_true, zero_add, add_zero]
  change (∫⁻ w, A w ∂gamma) = ∫⁻ w, B w ∂gamma
  rw [hsplit A, hsplit B]
  simp only [Pi.add_apply]
  have hAt : Measurable (fun w => if flag w = true then A w else 0) :=
    hA.ite (measurableSet_eq_fun hf measurable_const) measurable_const
  have hBt : Measurable (fun w => if flag w = true then B w else 0) :=
    hB.ite (measurableSet_eq_fun hf measurable_const) measurable_const
  rw [lintegral_add_left hAt, lintegral_add_left hBt]
  apply congrArg₂ (· + ·)
  · convert hcall using 1 <;> apply lintegral_congr <;> intro w <;>
      dsimp only [A, B, actualTest, meanTest, calendarStepSourceJoint, flag, q] <;>
      exact gate_split rate rewards C_star C_h s ⟨t.val + 1 + k, hk⟩
        (calendarSourceHistory rate rewards C_star C_h control0 b u t s ⟨t.val + 1 + k, hk⟩ k hk.le w.1) _ _
  · convert hnon using 1 <;> apply lintegral_congr <;> intro w <;>
      dsimp only [A, B, actualTest, meanTest, calendarStepSourceJoint, flag, q] <;>
      exact gate_split rate rewards C_star C_h s ⟨t.val + 1 + k, hk⟩
        (calendarSourceHistory rate rewards C_star C_h control0 b u t s ⟨t.val + 1 + k, hk⟩ k hk.le w.1) _ _

/-- Transport the assembled later law to the original terminal component. -/
theorem generated_component_later_fast_test (ids : Option (CompletePublicTable.IDArray p))
    (b : Bool) (u t s : Fin p.T) (k : ℕ)
    (hk : t.val + 1 + k < p.T) (hs : s.val ≤ t.val + 1 + k)
    (Phi : History rate s ⟨t.val + 1 + k, hk⟩ × (SlowSet p × Fin p.K) → ℝ≥0∞)
    (hPhi : Measurable Phi) :
    (∫⁻ w, actualTest rate rewards C_star C_h s ⟨t.val + 1 + k, hk⟩ Phi
        (terminalSourceJoint rate rewards C_star C_h control0 s ⟨t.val + 1 + k, hk⟩ ⟨.generated b u t, w⟩)
      ∂ids.elim (ReferenceExhaustiveGeneratedCalendarSourceLaw.componentLaw rate rewards C_star C_h control0 (.generated b u t))
        (fun id => ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDComponentLaw
          rate rewards C_star C_h control0 id (.generated b u t))) =
    ∫⁻ w, meanTest rate rewards C_star C_h s ⟨t.val + 1 + k, hk⟩ Phi
        (terminalSourceJoint rate rewards C_star C_h control0 s ⟨t.val + 1 + k, hk⟩ ⟨.generated b u t, w⟩)
      ∂ids.elim (ReferenceExhaustiveGeneratedCalendarSourceLaw.componentLaw rate rewards C_star C_h control0 (.generated b u t))
        (fun id => ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDComponentLaw
          rate rewards C_star C_h control0 id (.generated b u t)) := by
  rw [generated_component_source_joint_step_test rate rewards C_star C_h control0 b u t ids s k hk hs
    _ (measurable_actualTest rate rewards C_star C_h control0 s _ Phi hPhi),
    generated_component_source_joint_step_test rate rewards C_star C_h control0 b u t ids s k hk hs
      _ (measurable_meanTest rate rewards C_star C_h control0 s _ Phi hPhi)]
  exact calendar_later_fast_test rate rewards C_star C_h control0 ids b u t s k hk hs Phi hPhi

section RootAssembly

open ReferenceGeneratedCalendarRootRoundLaw
open ReferenceFirstNextInstallationCellFactors
open ReferenceFirstNextInstallationTransitionLaw
open ReferenceFirstLiveActualRefreshTestLaw

variable (b : Bool) (u t : Fin p.T)

local notation "Root" => CalendarSample rate rewards C_star C_h b u t 0
local notation "rootCell" => calendarRootCell rate rewards C_star C_h control0 b u t
local notation "rootHistory" => calendarSourceHistory rate rewards C_star C_h control0 b u t
local notation "rootJoint" => calendarRootSourceJoint rate rewards C_star C_h control0 b u t
local notation "restore" => rootRestore rate rewards C_star C_h control0 b u t

private theorem root_history_clear (s : Fin p.T) (hs : s.val ≤ t.val) (w : Root)
    (hw : rootHistory s t 0 (by omega) w ∈ historyDomain rate rewards C_star C_h s t) :
    (rootCell w).before.overflow = false := by
  have hp := calendarSourceHistory_root_replay rate rewards C_star C_h control0 b u t s hs w hw.1 hw.2.2.1
  have hc := hw.2.2.2
  rw [hp, Option.any_some, Bool.not_eq_true'] at hc
  exact hc

private theorem root_slowSet (w : Root) :
    (rootCell w).slowSet = if (rootCell w).before.overflow then frozenSlowSet p else
      (firstSourceCell rate rewards C_star C_h t
        (rootInstalledSource rate rewards C_star C_h b u t w.1.1 w.2)).selected.view.payload.slowSet := by
  cases b <;> rfl

private theorem root_history_fast (s : Fin p.T) (hs : s.val ≤ t.val) (w : Root)
    (hw : rootHistory s t 0 (by omega) w ∈ historyDomain rate rewards C_star C_h s t)
    (Phi : History rate s t × (SlowSet p × Fin p.K) → ℝ≥0∞) :
    let z := rootInstalledSource rate rewards C_star C_h b u t w.1.1 w.2
    let view := (firstSourceCell rate rewards C_star C_h t z).selected.view
    historyFastTest rate rewards C_star C_h s t Phi (rootHistory s t 0 (by omega) w) (rootCell w).slowSet =
      ∑ j : FastArm view.payload.slowSet,
        Phi (rootHistory s t 0 (by omega) w, (view.payload.slowSet, j.val)) *
          ReferencePostInvocationCollectionNativeLaw.collectionFastPMF rate view.payload.anchor
            (RecordedQueueRun.scoreWeight Q (firstBefore rate rewards C_star C_h control0 t z))
            view.payload.anchor_pos (RecordedSlowRefresh.scoreWeight_pos Q _) view.payload.slowSet j := by
  dsimp only
  let z := rootInstalledSource rate rewards C_star C_h b u t w.1.1 w.2
  let h := rootHistory s t 0 (by omega) w
  have hsource : calendarCurrentSource rate rewards C_star C_h control0 b u t 0 (by omega) w = z.val :=
    by cases b <;> rfl
  have hpre := calendarSourceHistory_root_replay rate rewards C_star C_h control0 b u t s hs w hw.1 hw.2.2.1
  have hbefore : (rootCell w).before = firstBefore rate rewards C_star C_h control0 t z :=
    by cases b <;> rfl
  have hstart : z.val ∈ sourceStartEvent rate rewards C_star C_h s := by
    rw [← hsource]
    exact (sourceStartEvent_sourcePrefix rate rewards C_star C_h control0 s _).mpr hw.1
  obtain ⟨A, hA, _hAc, ha⟩ := rootSource_episode_anchor rate rewards C_star C_h control0 t
    s hs hw.2.2.1 z hstart (hbefore ▸ root_history_clear rate rewards C_star C_h control0 b u t s hs w hw)
  have hseed : prefixNumerical rate rewards C_star C_h s.castSucc h.1.1 = some A := by
    change prefixNumerical rate rewards C_star C_h s.castSucc
      (sourcePrefix control0 s.val (calendarCurrentSource rate rewards C_star C_h control0 b u t 0 (by omega) w)) = _
    rw [hsource]
    exact hA
  have hU : (rootCell w).slowSet = (firstSourceCell rate rewards C_star C_h t z).selected.view.payload.slowSet := by
    have hc := root_history_clear rate rewards C_star C_h control0 b u t s hs w hw
    rw [root_slowSet rate rewards C_star C_h control0 b u t w, hc]
    rfl
  change sourceEpisodeReplay rate rewards C_star C_h s t h = some (rootCell w).before at hpre
  change historyFastTest rate rewards C_star C_h s t Phi h (rootCell w).slowSet =
    ∑ j : FastArm (firstSourceCell rate rewards C_star C_h t z).selected.view.payload.slowSet,
      Phi (h, ((firstSourceCell rate rewards C_star C_h t z).selected.view.payload.slowSet, j.val)) *
        ReferencePostInvocationCollectionNativeLaw.collectionFastPMF rate
          (firstSourceCell rate rewards C_star C_h t z).selected.view.payload.anchor
          (RecordedQueueRun.scoreWeight Q (firstBefore rate rewards C_star C_h control0 t z))
          _ _ _ j
  simp only [historyFastTest, hseed, hpre]
  rw [hU, hbefore]
  simp only [numericalFastPMF, ha]

private theorem generated_component_root_fast_test_raw (s : Fin p.T) (hs : s.val ≤ t.val)
    (Phi : History rate s t × (SlowSet p × Fin p.K) → ℝ≥0∞) (hPhi : Measurable Phi) :
    (∫⁻ w, actualTest rate rewards C_star C_h s t Phi
        (terminalSourceJoint rate rewards C_star C_h control0 s t ⟨.generated b u t, w⟩)
      ∂ReferenceExhaustiveGeneratedCalendarSourceLaw.componentLaw rate rewards C_star C_h control0 (.generated b u t)) =
    ∫⁻ w, meanTest rate rewards C_star C_h s t Phi
        (terminalSourceJoint rate rewards C_star C_h control0 s t ⟨.generated b u t, w⟩)
      ∂ReferenceExhaustiveGeneratedCalendarSourceLaw.componentLaw rate rewards C_star C_h control0 (.generated b u t) := by
  let Psi : History rate s t × (SlowSet p × Fin p.K) → ℝ≥0∞ :=
    fun y => if y.1 ∈ historyDomain rate rewards C_star C_h s t then Phi y else 0
  have hPsi : Measurable Psi := hPhi.ite
    ((measurableSet_historyDomain rate rewards C_star C_h control0 s t).preimage measurable_fst) measurable_const
  let F : History rate s t × (Estimate p × Option (LogicalCell p rate)) → ℝ≥0∞ := fun y =>
    y.2.2.elim 0 (fun e => if e.before.overflow = false then Psi (y.1, (e.slowSet, e.fastArm)) else 0)
  have hF : Measurable F := by
    have hU : Measurable (fun e : LogicalCell p rate => e.slowSet) :=
      measurable_logicalCell_slowSet.mono le_rfl le_top
    have hf := measurable_optional rate
      (fun v : LogicalCell p rate × History rate s t =>
        if v.1.before.overflow = false then Psi (v.2, (v.1.slowSet, v.1.fastArm)) else 0)
      ((hPsi.comp (measurable_snd.prodMk ((hU.comp measurable_fst).prodMk
        (measurable_logicalCell_fastArm.comp measurable_fst)))).ite
          (((measurable_of_countable (fun S : RecordedQueueRun.RunState p.K => S.overflow)).comp
            (measurable_logicalCell_before.comp measurable_fst)) (measurableSet_singleton false)) measurable_const)
    exact hf.comp (measurable_snd.snd.prodMk measurable_fst)
  have hA := generated_component_source_joint_native_root_test rate rewards C_star C_h control0 b u t
    none s hs _ (measurable_actualTest rate rewards C_star C_h control0 s t Phi hPhi)
  have hFroot := generated_component_source_joint_native_root_test rate rewards C_star C_h control0 b u t
    none s hs F hF
  have hB := generated_component_source_joint_native_root_test rate rewards C_star C_h control0 b u t
    none s hs _ (measurable_meanTest rate rewards C_star C_h control0 s t Phi hPhi)
  have hfast := ReferenceGeneratedCalendarRetainedFastCore.generated_component_root_fast_test
    rate rewards C_star C_h control0 b u t none s hs Psi hPsi
  have hAF : (∫⁻ w, actualTest rate rewards C_star C_h s t Phi (rootJoint s w)
      ∂calendarLaw rate rewards C_star C_h control0 b u t 0 (by omega)) =
      ∫⁻ w, F (rootJoint s w) ∂calendarLaw rate rewards C_star C_h control0 b u t 0 (by omega) := by
    apply lintegral_congr
    intro w
    by_cases hw : rootHistory s t 0 (by omega) w ∈ historyDomain rate rewards C_star C_h s t
    · have hc := root_history_clear rate rewards C_star C_h control0 b u t s hs w hw
      simp only [actualTest, F, calendarRootSourceJoint, Psi, hw, hc, ite_true, Option.elim_some]
    · simp only [actualTest, F, calendarRootSourceJoint, Psi, hw, ite_false, Option.elim_some, ite_self]
  refine hA.trans (hAF.trans (hFroot.symm.trans (hfast.trans ?_)))
  let B := fun w : Root => meanTest rate rewards C_star C_h s t Phi (rootJoint s w)
  have hBm : Measurable B := (measurable_meanTest rate rewards C_star C_h control0 s t Phi hPhi).comp
    (measurable_calendarRootSourceJoint rate rewards C_star C_h control0 b u t s)
  refine Eq.trans ?_ hB.symm
  change _ = ∫⁻ w, B w ∂calendarLaw rate rewards C_star C_h control0 b u t 0 (by omega)
  rw [calendarLaw_root_refill_test rate rewards C_star C_h control0 b u t B hBm]
  apply Finset.sum_congr rfl
  intro j _
  apply lintegral_congr
  intro r
  apply lintegral_congr
  intro a
  apply lintegral_congr
  intro v
  let w0 := restore j r a v control0 scalarZero
  have hconst (c : ContinuousLearningRows.TimeControl p) (x : ContinuousControlSlice.Scalar) :
      B (restore j r a v c x) = B w0 := by
    obtain ⟨hh, hU⟩ := Prod.mk.inj
      (rootRestore_sourceHistory_nonuse rate rewards C_star C_h control0 b u t s hs j r a v c x)
    simp only [B, meanTest, calendarRootSourceJoint, Option.elim_some, hh, hU, w0]
    rfl
  simp_rw [hconst]
  simp only [lintegral_const, measure_univ, mul_one, Option.elim_none]
  let z0 := rootInstalledSource rate rewards C_star C_h b u t w0.1.1 w0.2
  let view := (firstSourceCell rate rewards C_star C_h t z0).selected.view
  change (if (firstBefore rate rewards C_star C_h control0 t z0).overflow = false then
    ∑ j : FastArm view.payload.slowSet,
      Psi (rootHistory s t 0 (by omega) w0, (view.payload.slowSet, j.val)) *
        ReferencePostInvocationCollectionNativeLaw.collectionFastPMF rate view.payload.anchor
          (RecordedQueueRun.scoreWeight Q (firstBefore rate rewards C_star C_h control0 t z0))
          view.payload.anchor_pos (RecordedSlowRefresh.scoreWeight_pos Q _) view.payload.slowSet j
    else 0) = B w0
  by_cases hw : rootHistory s t 0 (by omega) w0 ∈ historyDomain rate rewards C_star C_h s t
  · have hc := root_history_clear rate rewards C_star C_h control0 b u t s hs w0 hw
    have hbefore : (rootCell w0).before = firstBefore rate rewards C_star C_h control0 t
        (rootInstalledSource rate rewards C_star C_h b u t w0.1.1 w0.2) := by cases b <;> rfl
    rw [hbefore] at hc
    change (firstBefore rate rewards C_star C_h control0 t z0).overflow = false at hc
    simp only [Psi, hw, ite_true, hc, B, meanTest, calendarRootSourceJoint, Option.elim_some]
    exact (root_history_fast rate rewards C_star C_h control0 b u t s hs w0 hw Phi).symm
  · simp only [Psi, hw, ite_false, zero_mul, Finset.sum_const_zero,
      B, meanTest, calendarRootSourceJoint, Option.elim_some, ite_self]

end RootAssembly

section PrefixAssembly

open ReferenceFirstCollectionLogicalPrefixExtension
open ReferenceFirstLiveCalendarMarkedTransition

local notation "O" => ReferenceFirstLiveCalendarMarkedTransition.Observation p rate
local notation "Aux" => ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p
local notation "Innovation" => ContinuousLearningRows.TimeControl p × ContinuousControlSlice.Scalar
local notation "beta" => fun (ids : Option (CompletePublicTable.IDArray p)) (q : Fin p.T) =>
  Option.elim ids (betaPre rate rewards C_star C_h control0 (Fin.castSucc q))
    (fun id => fixedIDBetaPre rate rewards C_star C_h control0 id (Fin.castSucc q))

omit control0 in
private def liveBranch (q : Fin p.T) (v : O × Innovation) : Option (LogicalCell p rate) :=
  Sum.elim (fun _ => none) some (currentCellTag rate rewards C_star C_h q (extensionInput rate q v).1)

omit control0 in
private theorem measurable_liveBranch (q : Fin p.T) :
    Measurable (liveBranch rate rewards C_star C_h q) :=
  (measurable_const.sumElim
    (LaterAssignmentFullOutputMeasurability.measurable_some_of_measurable _ measurable_id)).comp
      ((measurable_currentCellTag rate rewards C_star C_h q).comp (measurable_extensionInput rate q).fst)

private theorem prefix_mark_branches (q : Fin p.T) (za : BootstrapPrivateRoundStreams.SourceInput p × Aux)
    (f : LogicalCell p rate → ℝ≥0∞) :
    let v := (extendedObservation rate rewards C_star C_h control0 q.castSucc za,
      (ReferenceSourceCurrentControlFreshness.u_t p q za.1, za.2 (q, 1)))
    (prefixCurrentMark rate rewards C_star C_h q v).elim 0 f =
      (liveBranch rate rewards C_star C_h q v).elim 0 f +
        (ReferenceGeneratedCalendarPrefixCollectionFast.collectionBranch rate rewards C_star C_h q v).elim 0 f := by
  dsimp only
  let v := (extendedObservation rate rewards C_star C_h control0 q.castSucc za,
    (ReferenceSourceCurrentControlFreshness.u_t p q za.1, za.2 (q, 1)))
  let d := extensionInput rate q v
  let c := prefixCandidate (currentCellTag rate rewards C_star C_h q)
    (fun x => collectionCellAt rate rewards C_star C_h q x.1 x.2) d.1 d.2
  let L := v.1.2.2
  have hL : ∀ e ∈ L, e.time.val < q.val :=
    extendedPast_time_lt rate rewards C_star C_h q.castSucc za
  have hnone : L.find? (fun e => e.time == q) = none := by
    apply List.find?_eq_none.mpr
    intro e he htime
    have ht := hL e he
    rw [beq_iff_eq.mp htime] at ht
    exact Nat.lt_irrefl _ ht
  have hlist : (extensionSample rate rewards C_star C_h q v).2.2 = L ++ c.toList := by
    change (prefixStep (fun e : LogicalCell p rate => e.nextSlowSet)
      (currentCellTag rate rewards C_star C_h q)
      (fun x => collectionCellAt rate rewards C_star C_h q x.1 x.2) d.1 d.2).2 = _
    unfold prefixStep
    dsimp only [c]
    split <;> rename_i hc <;> simp only [hc, Option.toList_none, Option.toList_some, List.append_nil] <;> rfl
  have hactual : (extensionSample rate rewards C_star C_h q v).2.2 =
      extendedPast rate rewards C_star C_h q.succ za :=
    congrArg (fun o : O => o.2.2) (extensionSample_actual rate rewards C_star C_h control0 q za)
  have hmark : prefixCurrentMark rate rewards C_star C_h q v = c := by
    unfold prefixCurrentMark
    rw [hlist, List.find?_append, hnone, Option.none_or]
    cases hc : c with
    | none => rfl
    | some e =>
      have hmem : e ∈ extendedPast rate rewards C_star C_h q.succ za := by
        rw [← hactual, hlist, hc, Option.toList_some]
        exact List.mem_append_right _ (List.mem_singleton_self _)
      have hupper := extendedPast_time_lt rate rewards C_star C_h q.succ za e hmem
      have hfilter := extendedPast_filter rate rewards C_star C_h q.castSucc q.succ (by simp only [Fin.val_castSucc, Fin.val_succ]; omega) za
      simp only [Fin.val_castSucc] at hfilter
      have hLdef : L = extendedPast rate rewards C_star C_h q.castSucc za := rfl
      rw [← hLdef] at hfilter
      have hself : L.filter (fun e => e.time.val < q.val) = L :=
        List.filter_eq_self.mpr (fun e he => decide_eq_true (hL e he))
      have hlower : q.val ≤ e.time.val := by
        by_contra hnot
        have hlt : e.time.val < q.val := by omega
        rw [← hactual, hlist, hc, Option.toList_some, List.filter_append, hself] at hfilter
        simp only [List.filter_cons, decide_eq_true hlt, List.filter_nil, ite_true] at hfilter
        have hn : L.length + 1 = L.length := by
          simpa only [List.length_append, List.length_singleton] using congrArg List.length hfilter
        omega
      have ht : e.time = q := Fin.ext (by simp only [Fin.val_succ] at hupper; omega)
      simp only [Option.toList_some, List.find?_cons, ht, beq_self_eq_true]
  rw [hmark]
  change c.elim 0 f = _
  dsimp only [c, liveBranch, ReferenceGeneratedCalendarPrefixCollectionFast.collectionBranch]
  cases htag : currentCellTag rate rewards C_star C_h q d.1 with
  | inr e => simp only [prefixCandidate, htag, Sum.elim_inr, Option.elim_some, Option.elim_none, add_zero]
  | inl a =>
    simp only [prefixCandidate, htag, Sum.elim_inl, Option.elim_none, zero_add]
    cases d.2.1 <;> rfl

private theorem prefix_branch_integral (ids : Option (CompletePublicTable.IDArray p)) (q : Fin p.T)
    (f : O × LogicalCell p rate → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ v : O × Innovation, if noCallAt rate rewards C_star C_h q v.1.1 then
        (prefixCurrentMark rate rewards C_star C_h q v).elim 0 (fun e => f (v.1, e)) else 0
      ∂(beta ids q).prod (calendarInnovationLaw p)) =
    (∫⁻ v : O × Innovation, if noCallAt rate rewards C_star C_h q v.1.1 then
        (liveBranch rate rewards C_star C_h q v).elim 0 (fun e => f (v.1, e)) else 0
      ∂(beta ids q).prod (calendarInnovationLaw p)) +
    ∫⁻ v : O × Innovation, if noCallAt rate rewards C_star C_h q v.1.1 then
        (ReferenceGeneratedCalendarPrefixCollectionFast.collectionBranch rate rewards C_star C_h q v).elim 0
          (fun e => f (v.1, e)) else 0 ∂(beta ids q).prod (calendarInnovationLaw p) := by
  have hm := measurable_optional rate (fun x : LogicalCell p rate × O => f (x.2, x.1))
    (hf.comp (measurable_snd.prodMk measurable_fst))
  let F (c : O × Innovation → Option (LogicalCell p rate)) := fun v : O × Innovation =>
    if noCallAt rate rewards C_star C_h q v.1.1 then (c v).elim 0 (fun e => f (v.1, e)) else 0
  have hF (c : O × Innovation → Option (LogicalCell p rate)) (hc : Measurable c) : Measurable (F c) :=
    (hm.comp (hc.prodMk measurable_fst)).ite
      ((measurableSet_noCallAt rate rewards C_star C_h control0 q).preimage measurable_fst.fst) measurable_const
  let A := F (prefixCurrentMark rate rewards C_star C_h q)
  let B := F (liveBranch rate rewards C_star C_h q)
  let C := F (ReferenceGeneratedCalendarPrefixCollectionFast.collectionBranch rate rewards C_star C_h q)
  have hA := hF _ (measurable_prefixCurrentMark rate rewards C_star C_h control0 q)
  have hB := hF _ (measurable_liveBranch rate rewards C_star C_h q)
  have hC := hF _ (ReferenceGeneratedCalendarPrefixCollectionFast.measurable_collectionBranch
    rate rewards C_star C_h control0 q)
  let j := fun za : BootstrapPrivateRoundStreams.SourceInput p × Aux =>
    (extendedObservation rate rewards C_star C_h control0 q.castSucc za,
      (ReferenceSourceCurrentControlFreshness.u_t p q za.1, za.2 (q, 1)))
  have hj : Measurable j :=
    (measurable_extendedObservation rate rewards C_star C_h control0 q.castSucc).prodMk
      (((ReferenceSourceCurrentControlFreshness.measurable_u_t q).comp measurable_fst).prodMk
        ((measurable_pi_apply (q, 1)).comp measurable_snd))
  have hmap := ReferenceGeneratedCalendarPrefixLiveFast.originalSource_restrict_map_observation_innovation
    rate rewards C_star C_h control0 ids q
  change (∫⁻ v, A v ∂(beta ids q).prod (calendarInnovationLaw p)) =
    (∫⁻ v, B v ∂(beta ids q).prod (calendarInnovationLaw p)) +
      ∫⁻ v, C v ∂(beta ids q).prod (calendarInnovationLaw p)
  rw [← hmap, lintegral_map hA hj, lintegral_map hB hj, lintegral_map hC hj]
  have hcompB : Measurable (fun za => B (j za)) := hB.comp hj
  rw [← lintegral_add_left hcompB]
  apply lintegral_congr
  intro za
  dsimp only [A, B, C, F]
  by_cases hc : noCallAt rate rewards C_star C_h q (j za).1.1
  · simp only [hc, ite_true]
    exact prefix_mark_branches rate rewards C_star C_h control0 q za (fun e => f ((j za).1, e))
  · simp only [hc, ite_false, zero_add]

private theorem beforeFirstCall_joint_test (ids : Option (CompletePublicTable.IDArray p))
    (s q : Fin p.T) (hsq : s.val ≤ q.val)
    (F : History rate s q × (Estimate p × Option (LogicalCell p rate)) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ w, if w ∈ beforeFirstCall rate rewards C_star C_h q.succ then
        F (terminalSourceJoint rate rewards C_star C_h control0 s q w) else 0 ∂Lambda ids) =
    ∫⁻ v : O × Innovation, if noCallAt rate rewards C_star C_h q v.1.1 then
      F (prefixSourceJoint rate rewards C_star C_h control0 s q v) else 0
      ∂(beta ids q).prod (calendarInnovationLaw p) := by
  let test : O × Innovation → ℝ≥0∞ := fun v => if noCallAt rate rewards C_star C_h q v.1.1 then
    F (prefixSourceJoint rate rewards C_star C_h control0 s q v) else 0
  have ht : Measurable test := (hF.comp (measurable_prefixSourceJoint rate rewards C_star C_h control0 s q)).ite
    ((measurableSet_noCallAt rate rewards C_star C_h control0 q).preimage measurable_fst.fst) measurable_const
  have hpred (w : Omega) : w ∈ beforeFirstCall rate rewards C_star C_h q.succ ↔
      w ∈ beforeFirstCall rate rewards C_star C_h q.castSucc ∧
        noCallAt rate rewards C_star C_h q (prefixObservation rate rewards C_star C_h control0 q.castSucc w).1 :=
    (noCallBefore_succ rate rewards C_star C_h q
      (ReferenceExhaustiveGeneratedCalendarSourceLaw.originalSource rate rewards C_star C_h w)).trans
      (and_congr Iff.rfl (noCallAt_sourcePrefix rate rewards C_star C_h control0 q q.val le_rfl _))
  calc
    _ = ∫⁻ w, test (prefixObservation rate rewards C_star C_h control0 q.castSucc w,
        currentInnovation rate rewards C_star C_h control0 q w)
        ∂(Lambda ids).restrict (beforeFirstCall rate rewards C_star C_h q.castSucc) := by
      rw [← lintegral_indicator (measurableSet_beforeFirstCall rate rewards C_star C_h control0 q.castSucc)]
      apply lintegral_congr
      intro w
      by_cases hs : w ∈ beforeFirstCall rate rewards C_star C_h q.succ
      · obtain ⟨hp, hc⟩ := (hpred w).mp hs
        simp only [hs, ite_true, Set.indicator_apply, hp, test, hc,
          prefixSourceJoint_actual rate rewards C_star C_h control0 s q hsq w hs]
      · by_cases hp : w ∈ beforeFirstCall rate rewards C_star C_h q.castSucc
        · have hc : ¬ noCallAt rate rewards C_star C_h q
              (prefixObservation rate rewards C_star C_h control0 q.castSucc w).1 :=
            fun hc => hs ((hpred w).mpr ⟨hp, hc⟩)
          simp only [hs, ite_false, Set.indicator_apply, hp, ite_true, test, hc]
        · simp only [hs, ite_false, Set.indicator_apply, hp]
    _ = _ := by
      cases ids with
      | none => exact terminalLaw_prefix_innovation_test rate rewards C_star C_h control0 q test ht
      | some id => exact fixedIDTerminalLaw_prefix_innovation_test rate rewards C_star C_h control0 id q test ht

private theorem prefix_seed_initial (s q : Fin p.T) (hsq : s.val ≤ q.val) (w : Omega)
    (hw : w ∈ beforeFirstCall rate rewards C_star C_h q.succ)
    (hs : (sourceEstimateHistory rate rewards C_star C_h control0 s q w).1.1 ∈
      sourceStartEvent rate rewards C_star C_h s) :
    prefixNumerical rate rewards C_star C_h s.castSucc
      (sourceEstimateHistory rate rewards C_star C_h control0 s q w).1.1 =
      some (RecordedQueueRun.initialState p.K) := by
  let z := (sourceEstimateHistory rate rewards C_star C_h control0 s q w).1.1
  have hbefore : w ∈ beforeFirstCall rate rewards C_star C_h s.castSucc := by
    intro v hv
    exact hw v (by simp only [Fin.val_castSucc] at hv; simp only [Fin.val_succ]; omega)
  have hp : z = sourcePrefix control0 s.val
      (ReferenceExhaustiveGeneratedCalendarSourceLaw.originalSource rate rewards C_star C_h w) :=
    terminalSource_prefix_beforeFirstCall rate rewards C_star C_h control0 s.castSucc w hbefore
  have hno : noCallAt rate rewards C_star C_h s z := by
    rw [hp]
    exact (noCallAt_sourcePrefix rate rewards C_star C_h control0 s s.val le_rfl _).mp
      (hw s (by simp only [Fin.val_succ]; omega))
  have hlaunch : z ∈ ReferenceGeneratedDownAmbiguityMeasurability.generatedLaunchFiberSet
      (rate := rate) rewards C_star C_h s.val := by
    rcases hs.1 with hl | ⟨hc, _⟩
    · exact hl
    · rw [(noCallAt_iff_callAt_none rate rewards C_star C_h s z).mp hno] at hc
      cases hc
  have hz : ∃ active, ReferenceCorrectedInitializationLaunch.correctedLaunch rate z rewards C_star C_h = some active :=
    Option.isSome_iff_exists.mp
      ((ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing rate z rewards C_star C_h).mpr hlaunch.1)
  have hn := prefixNumerical_actualWord rate rewards C_star C_h s.castSucc z hz
    (by simpa only [Fin.val_castSucc, hlaunch.2] using le_refl s.val)
  simpa only [Fin.val_castSucc, hlaunch.2, Nat.sub_self, List.take_zero, RecordedQueueRun.run, RecordedQueueRun.execute] using hn

private theorem ae_historyDomain (ids : Option (CompletePublicTable.IDArray p)) :
    ∀ᵐ w ∂Lambda ids, ∀ s q : Fin p.T,
      sourceEstimateHistory rate rewards C_star C_h control0 s q w ∈
          historyDomain rate rewards C_star C_h s q ↔
        w ∈ retainedDomain rate rewards C_star C_h control0 s q := by
  filter_upwards [ae_retainedEvent_sourceHistory rate rewards C_star C_h control0 ids] with w hw
  intro s q
  have hs := sourceStartEvent_sourcePrefix rate rewards C_star C_h control0 s
    (ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalSource rate rewards C_star C_h control0 w)
  change (_ ∧ _) ↔ (_ ∧ _)
  constructor
  · rintro ⟨hst, hr⟩
    have hstart := hs.mpr hst
    exact ⟨hstart, (hw s q hstart).mpr hr⟩
  · rintro ⟨hst, hr⟩
    exact ⟨hs.mp hst, (hw s q hst).mp hr⟩

omit control0 in
private def clearTest (s q : Fin p.T)
    (Phi : History rate s q × (SlowSet p × Fin p.K) → ℝ≥0∞)
    (y : History rate s q × (Estimate p × Option (LogicalCell p rate))) : ℝ≥0∞ :=
  y.2.2.elim 0 (fun e => if e.before.overflow = false then Phi (y.1, (e.slowSet, e.fastArm)) else 0)

omit control0 in
private def unitMeanTest (s q : Fin p.T)
    (Phi : History rate s q × (SlowSet p × Fin p.K) → ℝ≥0∞)
    (y : History rate s q × (Estimate p × Option (LogicalCell p rate))) : ℝ≥0∞ :=
  y.2.2.elim 0 (fun e => if e.before.overflow = false then
    ∑ j : FastArm e.slowSet, Phi (y.1, (e.slowSet, j.val)) *
      ReferenceGeneratedCalendarPrefixCollectionFast.unitFastPMF rate e.before e.slowSet j else 0)

omit rewards C_star C_h control0 in
private theorem measurable_clearTest (s q : Fin p.T)
    (Phi : History rate s q × (SlowSet p × Fin p.K) → ℝ≥0∞) (hPhi : Measurable Phi) :
    Measurable (clearTest rate s q Phi) := by
  have hU : Measurable (fun e : LogicalCell p rate => e.slowSet) :=
    measurable_logicalCell_slowSet.mono le_rfl le_top
  have hf := measurable_optional rate
    (fun v : LogicalCell p rate × History rate s q =>
      if v.1.before.overflow = false then Phi (v.2, (v.1.slowSet, v.1.fastArm)) else 0)
    ((hPhi.comp (measurable_snd.prodMk ((hU.comp measurable_fst).prodMk
      (measurable_logicalCell_fastArm.comp measurable_fst)))).ite
        (((measurable_of_countable (fun S : RecordedQueueRun.RunState p.K => S.overflow)).comp
          (measurable_logicalCell_before.comp measurable_fst)) (measurableSet_singleton false)) measurable_const)
  exact hf.comp (measurable_snd.snd.prodMk measurable_fst)

omit rewards C_star C_h control0 in
private theorem measurable_unitMeanTest (s q : Fin p.T)
    (Phi : History rate s q × (SlowSet p × Fin p.K) → ℝ≥0∞) (hPhi : Measurable Phi) :
    Measurable (unitMeanTest rate s q Phi) := by
  let f : History rate s q × (RecordedQueueRun.RunState p.K × SlowSet p) → ℝ≥0∞ := fun v =>
    if v.2.1.overflow = false then ∑ j : FastArm v.2.2,
      Phi (v.1, (v.2.2, j.val)) *
        ReferenceGeneratedCalendarPrefixCollectionFast.unitFastPMF rate v.2.1 v.2.2 j else 0
  have hf : Measurable f := by
    apply measurable_from_prod_countable_left
    rintro ⟨S, U⟩
    dsimp only [f]
    by_cases hc : S.overflow = false
    · simp only [hc, ite_true]
      exact Finset.measurable_sum Finset.univ (fun j _ =>
        (hPhi.comp (measurable_id.prodMk (measurable_const (a := (U, j.val))))).mul measurable_const)
    · simp only [hc]
      exact measurable_const
  have hU : Measurable (fun e : LogicalCell p rate => e.slowSet) :=
    measurable_logicalCell_slowSet.mono le_rfl le_top
  have hg := measurable_optional rate
    (fun v : LogicalCell p rate × History rate s q => f (v.2, (v.1.before, v.1.slowSet)))
    (hf.comp (measurable_snd.prodMk
      ((measurable_logicalCell_before.comp measurable_fst).prodMk (hU.comp measurable_fst))))
  exact hg.comp (measurable_snd.snd.prodMk measurable_fst)

/-- Before the first invocation, LIVE and COLLECTION retain the same original
observer, current innovation, incoming set, and incoming overflow gate. -/
theorem terminalLaw_beforeFirstCall_fast_test (ids : Option (CompletePublicTable.IDArray p))
    (s q : Fin p.T) (hsq : s.val ≤ q.val)
    (Phi : History rate s q × (SlowSet p × Fin p.K) → ℝ≥0∞) (hPhi : Measurable Phi) :
    (∫⁻ w, if w ∈ beforeFirstCall rate rewards C_star C_h q.succ then
        actualTest rate rewards C_star C_h s q Phi
          (terminalSourceJoint rate rewards C_star C_h control0 s q w) else 0 ∂Lambda ids) =
    ∫⁻ w, if w ∈ beforeFirstCall rate rewards C_star C_h q.succ then
        meanTest rate rewards C_star C_h s q Phi
          (terminalSourceJoint rate rewards C_star C_h control0 s q w) else 0 ∂Lambda ids := by
  let PhiG : History rate s q × (SlowSet p × Fin p.K) → ℝ≥0∞ := fun y =>
    if y.1 ∈ historyDomain rate rewards C_star C_h s q then Phi y else 0
  have hPhiG : Measurable PhiG := hPhi.ite
    ((measurableSet_historyDomain rate rewards C_star C_h control0 s q).preimage measurable_fst) measurable_const
  let Psi : O × (SlowSet p × Fin p.K) → ℝ≥0∞ := fun y =>
    PhiG (prefixSourceHistory rate control0 s q y.1, y.2)
  have hPsi : Measurable Psi := hPhiG.comp
    (((measurable_prefixSourceHistory rate control0 s q).comp measurable_fst).prodMk measurable_snd)
  let f : O × LogicalCell p rate → ℝ≥0∞ := fun v =>
    ReferenceGeneratedCalendarPrefixCollectionFast.retainedFastTest rate Psi v.1 (some v.2)
  let g : O × LogicalCell p rate → ℝ≥0∞ := fun v =>
    ReferenceGeneratedCalendarPrefixCollectionFast.averagedFastTest rate Psi v.1 (some v.2)
  have hpair : Measurable (fun v : O × LogicalCell p rate => (v.1, some v.2)) :=
    measurable_fst.prodMk (LaterAssignmentFullOutputMeasurability.measurable_some_of_measurable _ measurable_snd)
  have hf : Measurable f :=
    (ReferenceGeneratedCalendarPrefixCollectionFast.measurable_retainedFastTest rate Psi hPsi).comp hpair
  have hg : Measurable g :=
    (ReferenceGeneratedCalendarPrefixCollectionFast.measurable_averagedFastTest rate Psi hPsi).comp hpair
  have ha := prefix_branch_integral rate rewards C_star C_h control0 ids q f hf
  have hb := prefix_branch_integral rate rewards C_star C_h control0 ids q g hg
  have hl := ReferenceGeneratedCalendarPrefixLiveFast.prefix_live_fast_lintegral
    rate rewards C_star C_h control0 ids q Psi hPsi
  have hc := ReferenceGeneratedCalendarPrefixCollectionFast.betaPre_collection_fast_joint_lintegral
    rate rewards C_star C_h control0 ids q Psi hPsi
  have hnative :
      (∫⁻ w, if w ∈ beforeFirstCall rate rewards C_star C_h q.succ then
        clearTest rate s q PhiG (terminalSourceJoint rate rewards C_star C_h control0 s q w) else 0 ∂Lambda ids) =
      ∫⁻ w, if w ∈ beforeFirstCall rate rewards C_star C_h q.succ then
        unitMeanTest rate s q PhiG (terminalSourceJoint rate rewards C_star C_h control0 s q w) else 0 ∂Lambda ids := by
    rw [beforeFirstCall_joint_test rate rewards C_star C_h control0 ids s q hsq _ (measurable_clearTest rate s q PhiG hPhiG),
      beforeFirstCall_joint_test rate rewards C_star C_h control0 ids s q hsq _ (measurable_unitMeanTest rate s q PhiG hPhiG)]
    refine Eq.trans ?_ (ha.trans ((congrArg₂ (· + ·) hl hc).trans (hb.symm.trans ?_)))
    · apply lintegral_congr
      intro v
      by_cases hn : noCallAt rate rewards C_star C_h q v.1.1
      · simp only [hn, ite_true]
        dsimp only [clearTest, unitMeanTest, prefixSourceJoint]
        cases prefixCurrentMark rate rewards C_star C_h q v <;> rfl
      · simp only [hn, ite_false]
    · apply lintegral_congr
      intro v
      by_cases hn : noCallAt rate rewards C_star C_h q v.1.1
      · simp only [hn, ite_true]
        dsimp only [clearTest, unitMeanTest, prefixSourceJoint]
        cases prefixCurrentMark rate rewards C_star C_h q v <;> rfl
      · simp only [hn, ite_false]
  have hpoint : ∀ᵐ w ∂Lambda ids,
      (if w ∈ beforeFirstCall rate rewards C_star C_h q.succ then
        actualTest rate rewards C_star C_h s q Phi (terminalSourceJoint rate rewards C_star C_h control0 s q w) else 0) =
      (if w ∈ beforeFirstCall rate rewards C_star C_h q.succ then
        clearTest rate s q PhiG (terminalSourceJoint rate rewards C_star C_h control0 s q w) else 0) ∧
      (if w ∈ beforeFirstCall rate rewards C_star C_h q.succ then
        meanTest rate rewards C_star C_h s q Phi (terminalSourceJoint rate rewards C_star C_h control0 s q w) else 0) =
      (if w ∈ beforeFirstCall rate rewards C_star C_h q.succ then
        unitMeanTest rate s q PhiG (terminalSourceJoint rate rewards C_star C_h control0 s q w) else 0) := by
    filter_upwards [ae_historyDomain rate rewards C_star C_h control0 ids,
      ae_retained_fast_parameters rate rewards C_star C_h control0 ids] with w hdomain hparam
    by_cases hw : w ∈ beforeFirstCall rate rewards C_star C_h q.succ
    · simp only [hw, ite_true]
      by_cases hG : sourceEstimateHistory rate rewards C_star C_h control0 s q w ∈
          historyDomain rate rewards C_star C_h s q
      · obtain ⟨e, _rho, _P, A, he, _ht, _hb, _birth, hA, _hAc, _ha, hS, hclear, _hen, _henv⟩ :=
          hparam s q ((hdomain s q).mp hG)
        have hi := prefix_seed_initial rate rewards C_star C_h control0 s q hsq w hw hG.1
        have hAi : A = RecordedQueueRun.initialState p.K := Option.some.inj (hA.symm.trans hi)
        subst A
        have hunit : RecordedQueueRun.scoreWeight Q (RecordedQueueRun.initialState p.K) = fun _ => 1 := by
          funext i
          simp only [RecordedQueueRun.scoreWeight, RecordedQueueRun.initialState, ScoreWeights.scoreWeight, pow_zero]
        simp only [actualTest, meanTest, clearTest, unitMeanTest, terminalSourceJoint, he, Option.elim_some,
          PhiG, hG, ite_true, hclear, historyFastTest, hA, hS, numericalFastPMF, hunit,
          ReferenceGeneratedCalendarPrefixCollectionFast.unitFastPMF, and_self]
      · dsimp only [actualTest, meanTest, clearTest, unitMeanTest, terminalSourceJoint]
        cases currentMark rate rewards C_star C_h control0 q w <;>
          simp only [Option.elim_none, Option.elim_some, PhiG, hG, ite_false, zero_mul,
            Finset.sum_const_zero, ite_self, and_self]
    · simp only [hw, ite_false, and_self]
  exact (lintegral_congr_ae (hpoint.mono fun _ h => h.1)).trans
    (hnative.trans (lintegral_congr_ae (hpoint.mono fun _ h => h.2)).symm)

end PrefixAssembly

section TerminalAssembly

private theorem measurable_sigma_mk {I : Type*} {B : I → Type*}
    [∀ i, MeasurableSpace (B i)] (i : I) : Measurable (Sigma.mk i : B i → Sigma B) :=
  measurable_iff_le_map.mpr (iInf_le _ i)

private theorem component_ae {P : Omega → Prop}
    (hP : ∀ᵐ w ∂ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalLaw rate rewards C_star C_h control0, P w)
    (i : ReferenceExhaustiveGeneratedCalendarSourceLaw.Component p) :
    ∀ᵐ w ∂ReferenceExhaustiveGeneratedCalendarSourceLaw.componentLaw rate rewards C_star C_h control0 i, P ⟨i, w⟩ := by
  exact ae_of_ae_map (measurable_sigma_mk i).aemeasurable
    ((Measure.ae_sum_iff.mp hP) i)

private theorem terminal_components (F : Omega → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ w, F w ∂ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalLaw rate rewards C_star C_h control0) =
      ∑' i : ReferenceExhaustiveGeneratedCalendarSourceLaw.Component p,
        ∫⁻ w, F ⟨i, w⟩ ∂ReferenceExhaustiveGeneratedCalendarSourceLaw.componentLaw rate rewards C_star C_h control0 i := by
  rw [ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalLaw, lintegral_sum_measure]
  apply tsum_congr
  intro i
  exact lintegral_map hF (measurable_sigma_mk i)

private theorem generated_beforeFirstCall (b : Bool) (u t q : Fin p.T)
    (w : ReferenceExhaustiveGeneratedCalendarSourceLaw.Payload rate rewards C_star C_h (.generated b u t)) :
    (⟨.generated b u t, w⟩ : Omega) ∈ beforeFirstCall rate rewards C_star C_h q.succ ↔ q.val < t.val := by
  have hf : (ReferenceExhaustiveGeneratedCalendarSourceLaw.originalSource rate rewards C_star C_h
      ⟨.generated b u t, w⟩) ∈
      ReferenceFirstCollectionAuxiliarySeeds.actualCollectionCallCell rate rewards C_star C_h u t := by
    cases b with
    | false => exact (ReferenceFirstLiveCollectionPathJoin.firstLiveCollectionEvent_facts
        rate rewards C_star C_h u t _ (calendarOriginalLift rate rewards C_star C_h false u t _ w).1.1.property).1
    | true => exact (calendarOriginalLift rate rewards C_star C_h true u t _ w).1.1.property.1
  exact (ReferenceGeneratedCalendarLaterRenewalSlowInitialization.noCallBefore_on_firstCell
    rate rewards C_star C_h u t _ hf q.succ).trans (by simp only [Fin.val_succ]; omega)

private theorem terminal_history_fast_test_raw (s q : Fin p.T) (hsq : s.val ≤ q.val)
    (Phi : History rate s q × (SlowSet p × Fin p.K) → ℝ≥0∞) (hPhi : Measurable Phi) :
    (∫⁻ w, actualTest rate rewards C_star C_h s q Phi
        (terminalSourceJoint rate rewards C_star C_h control0 s q w)
      ∂ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalLaw rate rewards C_star C_h control0) =
    ∫⁻ w, meanTest rate rewards C_star C_h s q Phi
        (terminalSourceJoint rate rewards C_star C_h control0 s q w)
      ∂ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalLaw rate rewards C_star C_h control0 := by
  let A := fun w : Omega => actualTest rate rewards C_star C_h s q Phi
    (terminalSourceJoint rate rewards C_star C_h control0 s q w)
  let B := fun w : Omega => meanTest rate rewards C_star C_h s q Phi
    (terminalSourceJoint rate rewards C_star C_h control0 s q w)
  let E := beforeFirstCall rate rewards C_star C_h q.succ
  have hE : MeasurableSet E := measurableSet_beforeFirstCall rate rewards C_star C_h control0 q.succ
  have hA : Measurable A := (measurable_actualTest rate rewards C_star C_h control0 s q Phi hPhi).comp
    (measurable_terminalSourceJoint rate rewards C_star C_h control0 s q)
  have hB : Measurable B := (measurable_meanTest rate rewards C_star C_h control0 s q Phi hPhi).comp
    (measurable_terminalSourceJoint rate rewards C_star C_h control0 s q)
  have hafter :
      (∫⁻ w, if w ∈ E then 0 else A w
        ∂ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalLaw rate rewards C_star C_h control0) =
      ∫⁻ w, if w ∈ E then 0 else B w
        ∂ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalLaw rate rewards C_star C_h control0 := by
    have hAa : Measurable (fun w => if w ∈ E then (0 : ℝ≥0∞) else A w) := measurable_const.ite hE hA
    have hBa : Measurable (fun w => if w ∈ E then (0 : ℝ≥0∞) else B w) := measurable_const.ite hE hB
    rw [terminal_components rate rewards C_star C_h control0 _ hAa,
      terminal_components rate rewards C_star C_h control0 _ hBa]
    apply tsum_congr
    intro i
    cases i with
    | noCall =>
      apply lintegral_congr
      intro w
      have hn : (⟨.noCall, w⟩ : Omega) ∈ E := by
        intro v _hv
        exact (ReferenceExhaustiveGeneratedCalendarSourceLaw.noCallBefore_terminal_iff
          rate rewards C_star C_h w.1.val).mpr w.1.property v v.isLt
      simp only [hn, ite_true]
    | stopped u t =>
      by_cases hqt : q.val < t.val
      · apply lintegral_congr
        intro w
        have hn : (⟨.stopped u t, w⟩ : Omega) ∈ E := by
          intro v hv
          exact ReferenceInitialStoppedCalendar.initialStoppedEvent_noCallBefore
            rate rewards C_star C_h u t w.1.val w.1.property v
              (by simp only [Fin.val_succ] at hv; simp only [Fin.val_castSucc]; omega)
        simp only [hn, ite_true]
      · have htq : t.val ≤ q.val := by omega
        have hdom := component_ae rate rewards C_star C_h control0
          (ae_historyDomain rate rewards C_star C_h control0 none) (.stopped u t)
        have hpar := component_ae rate rewards C_star C_h control0
          (ae_retained_fast_parameters rate rewards C_star C_h control0 none) (.stopped u t)
        apply lintegral_congr_ae
        filter_upwards [hdom, hpar] with w hdomain hparam
        have hG : sourceEstimateHistory rate rewards C_star C_h control0 s q ⟨.stopped u t, w⟩ ∉
            historyDomain rate rewards C_star C_h s q := by
          intro hG
          obtain ⟨e, _rho, _P, _S, he, ht, _hb, _birth, _hA, _hAc, _ha, _hS, hc, _hen, _env⟩ :=
            hparam s q ((hdomain s q).mp hG)
          have hm := ((currentMark_eq_some_iff rate rewards C_star C_h control0 q ⟨.stopped u t, w⟩ e).mp he).1
          have hte : t.val ≤ e.time.val := by rw [ht]; exact htq
          have heq := (ReferenceInitialStoppedCalendar.initialStoppedPast_suffix_fields
            rate rewards C_star C_h control0 u t (Fin.last p.T) w e hm hte).2
          have hstop : e.before.overflow = true := by
            rw [heq]
            exact ReferenceInitialStoppedCalendar.suffixBefore_stopped rate rewards C_star C_h u t e.time hte w.1
          rw [hc] at hstop
          cases hstop
        dsimp only [A, B, actualTest, meanTest, terminalSourceJoint]
        simp only [hG, ite_false, ite_self]
    | generated b u t =>
      by_cases hqt : q.val < t.val
      · apply lintegral_congr
        intro w
        have hn := (generated_beforeFirstCall rate rewards C_star C_h b u t q w).mpr hqt
        simp only [E, hn, ite_true]
      · have hn (w) : (⟨.generated b u t, w⟩ : Omega) ∉ E :=
          fun h => hqt ((generated_beforeFirstCall rate rewards C_star C_h b u t q w).mp h)
        simp_rw [ite_eq_right (hn _)]
        by_cases heq : q = t
        · subst q
          exact generated_component_root_fast_test_raw rate rewards C_star C_h control0 b u t s hsq Phi hPhi
        · have htq : t.val < q.val := by
            have hne : q.val ≠ t.val := fun h => heq (Fin.ext h)
            omega
          obtain ⟨k, hk⟩ : ∃ k : ℕ, t.val + 1 + k = q.val := ⟨q.val - t.val - 1, by omega⟩
          have hkT : t.val + 1 + k < p.T := by omega
          have hdate : (⟨t.val + 1 + k, hkT⟩ : Fin p.T) = q := Fin.ext hk
          cases hdate
          exact generated_component_later_fast_test rate rewards C_star C_h control0 none b u t s k hkT hsq Phi hPhi
  have hbefore := terminalLaw_beforeFirstCall_fast_test rate rewards C_star C_h control0 none s q hsq Phi hPhi
  have hsplit (f : Omega → ℝ≥0∞) :
      f = (fun w => if w ∈ E then f w else 0) + (fun w => if w ∈ E then 0 else f w) := by
    funext w
    by_cases hw : w ∈ E <;> simp only [Pi.add_apply, hw, ite_true, ite_false, zero_add, add_zero]
  change (∫⁻ w, A w ∂ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalLaw rate rewards C_star C_h control0) =
    ∫⁻ w, B w ∂ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalLaw rate rewards C_star C_h control0
  rw [hsplit A, hsplit B]
  simp only [Pi.add_apply]
  have hAb : Measurable (fun w => if w ∈ E then A w else 0) := hA.ite hE measurable_const
  have hBb : Measurable (fun w => if w ∈ E then B w else 0) := hB.ite hE measurable_const
  rw [lintegral_add_left hAb, lintegral_add_left hBb]
  exact congrArg₂ (· + ·) hbefore hafter

end TerminalAssembly

omit control0 in
private theorem historyFastTest_indicator_source (s q : Fin p.T)
    (D : Set (BootstrapPrivateRoundStreams.SourceInput p))
    (Phi : History rate s q × (SlowSet p × Fin p.K) → ℝ≥0∞) (h : History rate s q) (U : SlowSet p) :
    historyFastTest rate rewards C_star C_h s q
      (fun y => if y.1.1.1 ∈ D then Phi y else 0) h U =
      if h.1.1 ∈ D then historyFastTest rate rewards C_star C_h s q Phi h U else 0 := by
  unfold historyFastTest
  split <;> by_cases hi : h.1.1 ∈ D <;>
    simp only [hi, ite_true, ite_false, zero_mul, Finset.sum_const_zero]

omit control0 in
private theorem actualTest_indicator_source (s q : Fin p.T)
    (D : Set (BootstrapPrivateRoundStreams.SourceInput p))
    (Phi : History rate s q × (SlowSet p × Fin p.K) → ℝ≥0∞)
    (y : History rate s q × (Estimate p × Option (LogicalCell p rate))) :
    actualTest rate rewards C_star C_h s q (fun v => if v.1.1.1 ∈ D then Phi v else 0) y =
      if y.1.1.1 ∈ D then actualTest rate rewards C_star C_h s q Phi y else 0 := by
  unfold actualTest
  by_cases hi : y.1.1.1 ∈ D <;>
    by_cases hg : y.1 ∈ historyDomain rate rewards C_star C_h s q <;> cases y.2.2 <;>
    simp only [hi, hg, ite_true, ite_false, Option.elim_none, Option.elim_some]

omit control0 in
private theorem meanTest_indicator_source (s q : Fin p.T)
    (D : Set (BootstrapPrivateRoundStreams.SourceInput p))
    (Phi : History rate s q × (SlowSet p × Fin p.K) → ℝ≥0∞)
    (y : History rate s q × (Estimate p × Option (LogicalCell p rate))) :
    meanTest rate rewards C_star C_h s q (fun v => if v.1.1.1 ∈ D then Phi v else 0) y =
      if y.1.1.1 ∈ D then meanTest rate rewards C_star C_h s q Phi y else 0 := by
  unfold meanTest
  by_cases hi : y.1.1.1 ∈ D <;>
    by_cases hg : y.1 ∈ historyDomain rate rewards C_star C_h s q <;> cases y.2.2 <;>
    simp only [hi, hg, ite_true, ite_false, Option.elim_none, Option.elim_some,
      historyFastTest_indicator_source]

private theorem terminal_history_fast_test (ids : Option (CompletePublicTable.IDArray p))
    (s q : Fin p.T) (Phi : History rate s q × (SlowSet p × Fin p.K) → ℝ≥0∞) (hPhi : Measurable Phi) :
    (∫⁻ w, actualTest rate rewards C_star C_h s q Phi
        (terminalSourceJoint rate rewards C_star C_h control0 s q w) ∂Lambda ids) =
      ∫⁻ w, meanTest rate rewards C_star C_h s q Phi
        (terminalSourceJoint rate rewards C_star C_h control0 s q w) ∂Lambda ids := by
  by_cases hsq : s.val ≤ q.val
  · cases ids with
    | none => exact terminal_history_fast_test_raw rate rewards C_star C_h control0 s q hsq Phi hPhi
    | some id =>
      let D := ReferenceFixedIDSourceSection.fixedIDSourceSection id
      let PhiID : History rate s q × (SlowSet p × Fin p.K) → ℝ≥0∞ :=
        fun y => if y.1.1.1 ∈ D then Phi y else 0
      have hPhiID : Measurable PhiID := hPhi.ite
        ((ReferenceFixedIDSourceSection.measurable_fixedIDSourceSection id).preimage measurable_fst.fst.fst)
        measurable_const
      have hraw := terminal_history_fast_test_raw rate rewards C_star C_h control0 s q hsq PhiID hPhiID
      dsimp only [PhiID] at hraw
      simp_rw [actualTest_indicator_source, meanTest_indicator_source] at hraw
      have hID := (ReferenceFixedIDSourceSection.measurable_fixedIDSourceSection id).preimage
        (ReferenceExhaustiveGeneratedCalendarSourceLaw.measurable_terminalSource rate rewards C_star C_h control0)
      rw [Option.elim_some, ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDTerminalLaw_eq_restrict,
        lintegral_smul_measure, lintegral_smul_measure]
      apply congrArg (fun x : ℝ≥0∞ => (CompletePublicTable.idArrayMeasure p {id})⁻¹ * x)
      rw [← lintegral_indicator hID, ← lintegral_indicator hID]
      exact hraw
  · apply lintegral_congr
    intro w
    have hG : sourceEstimateHistory rate rewards C_star C_h control0 s q w ∉
        historyDomain rate rewards C_star C_h s q := fun h => hsq h.2.1
    dsimp only [actualTest, meanTest, terminalSourceJoint]
    simp only [hG, ite_false]

/-- Actual retained H/U/FAST joint-test law, raw and at every original ID.
The history and incoming slow set on the right are those of the same mark.
Only the original ID atom is normalized; the retained event is not. -/
theorem terminalLaw_retained_fast_test (ids : Option (CompletePublicTable.IDArray p))
    (s q : Fin p.T) (Phi : History rate s q × (SlowSet p × Fin p.K) → ℝ≥0∞) (hPhi : Measurable Phi) :
    (∫⁻ w in retainedDomain rate rewards C_star C_h control0 s q,
      (currentMark rate rewards C_star C_h control0 q w).elim 0
        (fun e => Phi (sourceEstimateHistory rate rewards C_star C_h control0 s q w, (e.slowSet, e.fastArm)))
      ∂Lambda ids) =
    ∫⁻ w in retainedDomain rate rewards C_star C_h control0 s q,
      (currentMark rate rewards C_star C_h control0 q w).elim 0
        (fun e => historyFastTest rate rewards C_star C_h s q Phi
          (sourceEstimateHistory rate rewards C_star C_h control0 s q w) e.slowSet) ∂Lambda ids := by
  have hE := measurableSet_retainedDomain rate rewards C_star C_h control0 s q
  rw [← lintegral_indicator hE, ← lintegral_indicator hE]
  refine (lintegral_congr_ae ?_).trans
    ((terminal_history_fast_test rate rewards C_star C_h control0 ids s q Phi hPhi).trans
      (lintegral_congr_ae ?_))
  · filter_upwards [ae_historyDomain rate rewards C_star C_h control0 ids] with w hw
    dsimp only [Set.indicator_apply, actualTest, terminalSourceJoint]
    rw [propext (hw s q)]
    rfl
  · filter_upwards [ae_historyDomain rate rewards C_star C_h control0 ids] with w hw
    dsimp only [Set.indicator_apply, meanTest, terminalSourceJoint]
    rw [propext (hw s q)]
    rfl

section RewardAssembly

omit control0 in
private theorem historyFastTest_ofReal_reward (s q : Fin p.T)
    (g : History rate s q × SlowSet p → ℝ) (hg : ∀ v, 0 ≤ g v)
    (h : History rate s q) (U : SlowSet p) :
    historyFastTest rate rewards C_star C_h s q
      (fun v => ENNReal.ofReal (g (v.1, v.2.1) *
        ((∑ i ∈ v.2.1.val, ((rewards q i).val : ℝ) / (D p : ℝ)) +
          ((rewards q v.2.2).val : ℝ) / (D p : ℝ)))) h U =
      ENNReal.ofReal (g (h, U) * historyFastReward rate rewards C_star C_h s q h U) := by
  unfold historyFastTest historyFastReward
  split
  · next A S hA hS =>
      let r : FastArm U → ℝ := fun j =>
        (∑ i ∈ U.val, ((rewards q i).val : ℝ) / (D p : ℝ)) +
          ((rewards q j.val).val : ℝ) / (D p : ℝ)
      have hr (j : FastArm U) : 0 ≤ r j :=
        (MixedAuxiliaryReward.oneRoundAuxiliaryReward_bounds
          (fun i => ((rewards q i).val : ℝ) / (D p : ℝ))
          (ReferenceGeneratedCalendarQuantizedRoundKernel.gridReward_mem rewards q) U j).1
      have heq : g (h, U) * numericalFastReward rate rewards q A S U =
          ∑ j : FastArm U, (g (h, U) * r j) * (numericalFastPMF rate A S U j).toReal := by
        unfold numericalFastReward
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        dsimp only [r]
        ring
      rw [heq, ENNReal.ofReal_sum_of_nonneg (fun j _ =>
        mul_nonneg (mul_nonneg (hg _) (hr j)) ENNReal.toReal_nonneg)]
      apply Finset.sum_congr rfl
      intro j _
      rw [ENNReal.ofReal_mul (mul_nonneg (hg _) (hr j)),
        ENNReal.ofReal_toReal ((numericalFastPMF rate A S U).apply_ne_top j)]
  · simp only [mul_zero, ENNReal.ofReal_zero]

private theorem terminalLaw_retained_reward_nonneg (ids : Option (CompletePublicTable.IDArray p))
    (s q : Fin p.T) (g : History rate s q × SlowSet p → ℝ) (hg : Measurable g)
    (hgn : ∀ v, 0 ≤ g v) (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ v, ‖g v‖ ≤ C) :
    (∫ w in retainedDomain rate rewards C_star C_h control0 s q,
      actualRewardTest rate rewards C_star C_h control0 s q g w ∂Lambda ids) =
    ∫ w in retainedDomain rate rewards C_star C_h control0 s q,
      meanRewardTest rate rewards C_star C_h control0 s q g w ∂Lambda ids := by
  let r : SlowSet p × Fin p.K → ℝ := fun v =>
    (∑ i ∈ v.1.val, ((rewards q i).val : ℝ) / (D p : ℝ)) +
      ((rewards q v.2).val : ℝ) / (D p : ℝ)
  let Phi : History rate s q × (SlowSet p × Fin p.K) → ℝ≥0∞ :=
    fun v => ENNReal.ofReal (g (v.1, v.2.1) * r v.2)
  have hPhi : Measurable Phi :=
    ((hg.comp (measurable_fst.prodMk measurable_snd.fst)).mul
      ((measurable_of_finite r).comp measurable_snd)).ennreal_ofReal
  have hlaw := terminalLaw_retained_fast_test rate rewards C_star C_h control0 ids s q Phi hPhi
  have hactual (w : Omega) :
      (currentMark rate rewards C_star C_h control0 q w).elim 0 (fun e =>
        Phi (sourceEstimateHistory rate rewards C_star C_h control0 s q w, (e.slowSet, e.fastArm))) =
      ENNReal.ofReal (actualRewardTest rate rewards C_star C_h control0 s q g w) := by
    cases he : currentMark rate rewards C_star C_h control0 q w with
    | none => simp only [he, Option.elim_none, actualRewardTest, ENNReal.ofReal_zero]
    | some e =>
      have ht := ((currentMark_eq_some_iff rate rewards C_star C_h control0 q w e).mp he).2
      simp only [he, Option.elim_some, actualRewardTest, ReferenceInitialStoppedCalendar.cellReward, ht, Phi, r]
  have hmean (w : Omega) :
      (currentMark rate rewards C_star C_h control0 q w).elim 0 (fun e =>
        historyFastTest rate rewards C_star C_h s q Phi
          (sourceEstimateHistory rate rewards C_star C_h control0 s q w) e.slowSet) =
      ENNReal.ofReal (meanRewardTest rate rewards C_star C_h control0 s q g w) := by
    cases he : currentMark rate rewards C_star C_h control0 q w with
    | none => simp only [he, Option.elim_none, meanRewardTest, ENNReal.ofReal_zero]
    | some e =>
      simp only [he, Option.elim_some, meanRewardTest]
      exact historyFastTest_ofReal_reward rate rewards C_star C_h s q g hgn _ e.slowSet
  simp_rw [hactual, hmean] at hlaw
  have hAn : ∀ w : Omega, 0 ≤ actualRewardTest rate rewards C_star C_h control0 s q g w := by
    intro w
    unfold actualRewardTest
    split
    · exact le_rfl
    · exact mul_nonneg (hgn _) (ReferenceExhaustiveGeneratedCalendarSourceLaw.cellReward_bounds rate rewards _).1
  have hBn : ∀ w : Omega, 0 ≤ meanRewardTest rate rewards C_star C_h control0 s q g w := by
    intro w
    unfold meanRewardTest
    split
    · exact le_rfl
    · exact mul_nonneg (hgn _) (historyFastReward_bounds rate rewards C_star C_h s q _ _).1
  have hAi := integrable_actualRewardTest rate rewards C_star C_h control0 ids s q g hg C hC hbound
  have hBi := integrable_meanRewardTest rate rewards C_star C_h control0 ids s q g hg C hC hbound
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hAn) hAi.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hBn) hBi.aestronglyMeasurable]
  exact congrArg ENNReal.toReal hlaw

/-- Bounded signed multipliers of the literal reward, on the same retained
terminal event and under the same raw or original fixed-ID law. -/
theorem terminalLaw_retained_reward_test (ids : Option (CompletePublicTable.IDArray p))
    (s q : Fin p.T) (g : History rate s q × SlowSet p → ℝ) (hg : Measurable g)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ v, ‖g v‖ ≤ C) :
    (∫ w in retainedDomain rate rewards C_star C_h control0 s q,
      actualRewardTest rate rewards C_star C_h control0 s q g w ∂Lambda ids) =
    ∫ w in retainedDomain rate rewards C_star C_h control0 s q,
      meanRewardTest rate rewards C_star C_h control0 s q g w ∂Lambda ids := by
  let gp := fun v => max (g v) 0
  let gn := fun v => max (-g v) 0
  have hgp : Measurable gp := hg.max measurable_const
  have hgn : Measurable gn := hg.neg.max measurable_const
  have hgp0 (v) : 0 ≤ gp v := le_max_right _ _
  have hgn0 (v) : 0 ≤ gn v := le_max_right _ _
  have hgpC (v) : ‖gp v‖ ≤ C := by
    rw [Real.norm_of_nonneg (hgp0 v)]
    exact max_le ((le_abs_self (g v)).trans (by simpa only [Real.norm_eq_abs] using hbound v)) hC
  have hgnC (v) : ‖gn v‖ ≤ C := by
    rw [Real.norm_of_nonneg (hgn0 v)]
    exact max_le ((le_abs_self (-g v)).trans
      (by simpa only [abs_neg, Real.norm_eq_abs] using hbound v)) hC
  have hsplit (v) : g v = gp v - gn v := (max_zero_sub_max_neg_zero_eq_self (g v)).symm
  have hA : actualRewardTest rate rewards C_star C_h control0 s q g =
      actualRewardTest rate rewards C_star C_h control0 s q gp -
        actualRewardTest rate rewards C_star C_h control0 s q gn := by
    funext w
    simp only [Pi.sub_apply]
    cases he : currentMark rate rewards C_star C_h control0 q w <;>
      simp only [actualRewardTest, he, sub_self, ← sub_mul, ← hsplit]
  have hB : meanRewardTest rate rewards C_star C_h control0 s q g =
      meanRewardTest rate rewards C_star C_h control0 s q gp -
        meanRewardTest rate rewards C_star C_h control0 s q gn := by
    funext w
    simp only [Pi.sub_apply]
    cases he : currentMark rate rewards C_star C_h control0 q w <;>
      simp only [meanRewardTest, he, sub_self, ← sub_mul, ← hsplit]
  rw [hA, hB]
  simp only [Pi.sub_apply]
  rw [integral_sub
    (integrable_actualRewardTest rate rewards C_star C_h control0 ids s q gp hgp C hC hgpC)
    (integrable_actualRewardTest rate rewards C_star C_h control0 ids s q gn hgn C hC hgnC),
    integral_sub
      (integrable_meanRewardTest rate rewards C_star C_h control0 ids s q gp hgp C hC hgpC)
      (integrable_meanRewardTest rate rewards C_star C_h control0 ids s q gn hgn C hC hgnC)]
  rw [terminalLaw_retained_reward_nonneg rate rewards C_star C_h control0 ids s q gp hgp hgp0 C hC hgpC,
    terminalLaw_retained_reward_nonneg rate rewards C_star C_h control0 ids s q gn hgn hgn0 C hC hgnC]

/-- The unweighted literal cell reward has the accepted finite FAST mean. -/
theorem terminalLaw_retained_cellReward_test (ids : Option (CompletePublicTable.IDArray p))
    (s q : Fin p.T) :
    (∫ w in retainedDomain rate rewards C_star C_h control0 s q,
      (currentMark rate rewards C_star C_h control0 q w).elim 0
        (ReferenceInitialStoppedCalendar.cellReward rate rewards) ∂Lambda ids) =
    ∫ w in retainedDomain rate rewards C_star C_h control0 s q,
      (currentMark rate rewards C_star C_h control0 q w).elim 0
        (fun e => historyFastReward rate rewards C_star C_h s q
          (sourceEstimateHistory rate rewards C_star C_h control0 s q w) e.slowSet) ∂Lambda ids := by
  have h := terminalLaw_retained_reward_test rate rewards C_star C_h control0 ids s q
    (fun _ => 1) measurable_const 1 zero_le_one (fun _ => by simp only [norm_one, le_refl])
  convert h using 1 <;> apply integral_congr_ae <;> filter_upwards [] with w <;>
    cases he : currentMark rate rewards C_star C_h control0 q w <;>
    simp only [actualRewardTest, meanRewardTest, he, Option.elim_none, Option.elim_some, one_mul]

/-- Actual finite and continuous reward conversions use the same strict seed,
complete incoming PRE, incoming set, and operative selected anchor. -/
theorem ae_retained_reward_conversions (ids : Option (CompletePublicTable.IDArray p)) :
    ∀ᵐ w ∂Lambda ids, ∀ (s q : Fin p.T),
      w ∈ retainedDomain rate rewards C_star C_h control0 s q →
      ∃ (e : LogicalCell p rate) (A : RecordedQueueRun.RunState p.K)
        (hlo : ∀ i, RecordedQueueRun.scoreWeight Q A i ≤ RecordedQueueRun.scoreWeight Q e.before i)
        (hhi : ∀ i, RecordedQueueRun.scoreWeight Q e.before i ≤ 2 * RecordedQueueRun.scoreWeight Q A i),
        currentMark rate rewards C_star C_h control0 q w = some e ∧
        prefixNumerical rate rewards C_star C_h s.castSucc
          (sourceEstimateHistory rate rewards C_star C_h control0 s q w).1.1 = some A ∧
        sourceEpisodeReplay rate rewards C_star C_h s q
          (sourceEstimateHistory rate rewards C_star C_h control0 s q w) = some e.before ∧
        (∃ (r : Record rate) (v : ReferenceActivePhysicalStep.Selection r.input),
          ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h q
            (ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalSource rate rewards C_star C_h control0 w) = some r ∧
          r.output.preparation.coordinator.selection = some v ∧
          v.view.payload.anchor = RecordedQueueRun.scoreWeight Q A) ∧
        historyFastReward rate rewards C_star C_h s q
            (sourceEstimateHistory rate rewards C_star C_h control0 s q w) e.slowSet =
          ∫ j : FastArm e.slowSet, MixedAuxiliaryReward.oneRoundAuxiliaryReward
            (fun i => ((rewards q i).val : ℝ) / (D p : ℝ)) e.slowSet j
            ∂(numericalFastPMF rate A e.before e.slowSet).toMeasure ∧
        historyFastReward rate rewards C_star C_h s q
            (sourceEstimateHistory rate rewards C_star C_h control0 s q w) e.slowSet =
          ∫ x : ContinuousCategorical.Scalar, MixedAuxiliaryReward.oneRoundAuxiliaryReward
            (fun i => ((rewards q i).val : ℝ) / (D p : ℝ)) e.slowSet
            (CanonicalFastSampling.sampleFast p rate.eta.val rate.eta.property rate.sourceCap
              (RecordedQueueRun.scoreWeight Q A) (RecordedQueueRun.scoreWeight Q e.before)
              (RecordedSlowRefresh.scoreWeight_pos Q A) (RecordedSlowRefresh.scoreWeight_pos Q e.before)
              hlo hhi e.slowSet x) ∂ContinuousCategorical.uniform := by
  filter_upwards [ae_retained_fast_parameters rate rewards C_star C_h control0 ids,
    ae_retained_selected_anchor rate rewards C_star C_h control0 ids] with w hparam hselected
  intro s q hE
  obtain ⟨e, _rho, _P, A, he, _ht, _hb, _birth, hA, _hAc, _ha, hS, _hSc, _hen, henv⟩ := hparam s q hE
  obtain ⟨e', A', r, _c, v, he', hA', _hS', hr, _hc, _hcen, hv, ha, _henv'⟩ := hselected s q hE
  have hee : e' = e := Option.some.inj (he'.symm.trans he)
  have hAA : A' = A := Option.some.inj (hA'.symm.trans hA)
  subst e'
  subst A'
  let hlo := fun i => (henv i).1
  let hhi := fun i => (henv i).2.le
  have hm : historyFastReward rate rewards C_star C_h s q
      (sourceEstimateHistory rate rewards C_star C_h control0 s q w) e.slowSet =
      numericalFastReward rate rewards q A e.before e.slowSet := by
    simp only [historyFastReward, hA, hS]
  exact ⟨e, A, hlo, hhi, he, hA, hS, ⟨r, v, hr, hv, ha⟩,
    hm.trans (numericalFastReward_eq_integral rate rewards q A e.before e.slowSet),
    hm.trans (numericalFastReward_eq_continuous rate rewards q A e.before hlo hhi e.slowSet)⟩

end RewardAssembly

end Bandits.Support.ReferenceGeneratedCalendarRetainedFastTerminalLaw
