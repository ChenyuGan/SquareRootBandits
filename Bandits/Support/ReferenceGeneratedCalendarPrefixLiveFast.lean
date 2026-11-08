/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedCalendarEpisodeHistoryTransport

import Mathlib.Tactic

/-!
# Original-source first-LIVE FAST joint-test evaluation

Sources: ZIP4 `04_slow_fast_learner.tex:16-37,96-114,140-215,323-390`
and `06_interruptions.tex:391-426`.

The original killed observer law retains arbitrary nonnegative tests, the
whole source and label-zero array, and the no-call gate at the current date.
The evaluation covers birth and both positive-offset first-LIVE branches.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal Classical BigOperators
open Bandits.Support ConstructorDimensions
open ReferenceFirstLiveChronologicalPrefixFoundation
open ReferenceFirstLiveChronologicalPrefixMeasurability
open ReferenceFirstCollectionLogicalPrefixExtension
open ReferenceFirstLiveCalendarMarkedTransition
open ReferenceSourcePrefixHistoryFiltration

namespace Bandits.Support.ReferenceGeneratedCalendarPrefixLiveFast

variable {p : ConstructorDimensions.Parameters}

local instance sourceMeasurableSpace : MeasurableSpace (BootstrapPrivateRoundStreams.SourceInput p) := by
  change MeasurableSpace (CompletePublicTable.PublishedOutput p ×
    BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

local instance optionMeasurableSpace {A : Type*} [MeasurableSpace A] :
    MeasurableSpace (Option A) := LaterAssignmentStartMeasurability.optionMeasurableSpace

local instance slowSetMeasurableSpace : MeasurableSpace (SlowSet p) :=
  Subtype.instMeasurableSpace

local instance slowSetDiscrete : DiscreteMeasurableSpace (SlowSet p) := by infer_instance

attribute [local instance] ReferenceRankInstallationPostUpdateProposalLaw.listMeasurableSingleton
  ReferenceRankInstallationPostUpdateProposalLaw.sumMeasurableSingleton

variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
  (control0 : ContinuousLearningRows.TimeControl p)

local notation "O" => ReferenceFirstLiveCalendarMarkedTransition.Observation p rate
local notation "Tag" => ReferenceFirstLiveCalendarMarkedTransition.CurrentCellTag p rate
local notation "Aux" => ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p
local notation "Omega" => ReferenceExhaustiveGeneratedCalendarSourceLaw.Omega rate rewards C_star C_h
local notation "obs" => extendedObservation rate rewards C_star C_h control0
local notation "tag" => currentCellTag rate rewards C_star C_h
local notation "pre" => NoCallBefore rate rewards C_star C_h
local notation "noCall" => noCallAt rate rewards C_star C_h
local notation "oldPair" => ReferenceGeneratedCalendarEpisodePrefixRecombination.originalPair
  rate rewards C_star C_h control0
local notation "oldObs" => ReferenceGeneratedCalendarEpisodePrefixRecombination.prefixObservation
  rate rewards C_star C_h control0
local notation "oldFresh" => ReferenceGeneratedCalendarEpisodePrefixRecombination.currentInnovation
  rate rewards C_star C_h control0
local notation "beforeCall" => ReferenceGeneratedCalendarEpisodePrefixRecombination.beforeFirstCall
  rate rewards C_star C_h
local notation "mu" => fun (ids : Option (CompletePublicTable.IDArray p)) => Option.elim ids (enlargedSourceLaw p)
  (fun id => Measure.prod (ReferenceFixedIDSourceSection.fixedIDSourceLaw id)
    (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p))
local notation "lambda" => fun (ids : Option (CompletePublicTable.IDArray p)) => Option.elim ids
  (ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalLaw rate rewards C_star C_h control0)
  (fun id => ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDTerminalLaw
    rate rewards C_star C_h control0 id)
local notation "beta" => fun (ids : Option (CompletePublicTable.IDArray p)) (q : Fin p.T) => Option.elim ids
  (betaPre rate rewards C_star C_h control0 (Fin.castSucc q))
  (fun id => ReferenceGeneratedCalendarEpisodePrefixRecombination.fixedIDBetaPre
    rate rewards C_star C_h control0 id (Fin.castSucc q))

/-- Restore the actual current tag from the existing observer and its original
innovation. No support, numerical truth or successful-sampling premise occurs. -/
theorem currentCellTag_extensionInput_actual (q : Fin p.T) (za : BootstrapPrivateRoundStreams.SourceInput p × Aux) :
    tag q (extensionInput rate q
      (obs q.castSucc za, (ReferenceSourceCurrentControlFreshness.u_t p q za.1,
        za.2 (q, 1)))).1 = tag q za := by
  have hs := prefix_successor_restore control0 q za.1
  change sourcePrefix control0 (q.val + 1) za.1 =
    ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p q
      (sourcePrefix control0 q.val za.1)
      (ReferenceSourceCurrentControlFreshness.u_t p q za.1) at hs
  change tag q
    (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p q
      (sourcePrefix control0 q.val za.1)
      (ReferenceSourceCurrentControlFreshness.u_t p q za.1),
      roundAuxiliary q (labelZero za.2, za.2 (q, 1))) = tag q za
  rw [← hs]
  calc
    _ = tag q (sourcePrefix control0 (q.val + 1) za.1, za.2) :=
      currentCellTag_auxiliary_ext rate rewards C_star C_h q _ _ _ (by
        simp only [roundAuxiliary, show (1 : Fin 2) ≠ 0 by decide, ite_false, ite_true])
    _ = _ := (currentCellTag_sourcePrefix rate rewards C_star C_h control0 q za.1 za.2).symm

/-- The joint innovation law on the actual original source, with both original
ID choices and the killed, unnormalized strict-prefix restriction. -/
theorem originalSource_restrict_map_observation_innovation
    (ids : Option (CompletePublicTable.IDArray p)) (q : Fin p.T) :
    ((mu ids).restrict {za | pre q.castSucc za.1}).map
      (fun za => (obs q.castSucc za,
        (ReferenceSourceCurrentControlFreshness.u_t p q za.1, za.2 (q, 1)))) =
      (beta ids q).prod (calendarInnovationLaw p) := by
  let j := fun za : BootstrapPrivateRoundStreams.SourceInput p × Aux => (obs q.castSucc za,
    (ReferenceSourceCurrentControlFreshness.u_t p q za.1, za.2 (q, 1)))
  have hj : Measurable j :=
    (measurable_extendedObservation rate rewards C_star C_h control0 (Fin.castSucc q)).prodMk
      (((ReferenceSourceCurrentControlFreshness.measurable_u_t q).comp measurable_fst).prodMk
        ((measurable_pi_apply (q, 1)).comp measurable_snd))
  have hp : ((lambda ids).restrict (beforeCall q.castSucc)).map oldPair =
      (mu ids).restrict {za | pre q.castSucc za.1} := by
    cases ids with
    | none =>
        exact ReferenceGeneratedCalendarEpisodePrefixRecombination.terminalLaw_restrict_map_originalPair
          rate rewards C_star C_h control0 q.castSucc
    | some id =>
        exact ReferenceGeneratedCalendarEpisodePrefixRecombination.fixedIDTerminalLaw_restrict_map_originalPair
          rate rewards C_star C_h control0 id q.castSucc
  calc
    _ = (((lambda ids).restrict (beforeCall q.castSucc)).map oldPair).map j := by rw [hp]
    _ = ((lambda ids).restrict (beforeCall q.castSucc)).map (j ∘ oldPair) :=
      Measure.map_map hj
        (ReferenceGeneratedCalendarEpisodePrefixRecombination.measurable_originalPair
          rate rewards C_star C_h control0)
    _ = ((lambda ids).restrict (beforeCall q.castSucc)).map
        (fun w => (oldObs q.castSucc w, oldFresh q w)) := by
      apply Measure.map_congr
      filter_upwards [ae_restrict_mem
        (ReferenceGeneratedCalendarEpisodePrefixRecombination.measurableSet_beforeFirstCall
          rate rewards C_star C_h control0 (Fin.castSucc q))] with w hw
      exact Prod.ext
        (ReferenceGeneratedCalendarEpisodePrefixRecombination.prefixObservation_eq_extendedObservation
          rate rewards C_star C_h control0 q.castSucc w hw).symm rfl
    _ = _ := by
      cases ids with
      | none =>
          exact ReferenceGeneratedCalendarEpisodePrefixRecombination.terminalLaw_restrict_map_prefixObservation_innovation
            rate rewards C_star C_h control0 q
      | some id =>
          exact ReferenceGeneratedCalendarEpisodePrefixRecombination.fixedIDTerminalLaw_restrict_map_prefixObservation_innovation
            rate rewards C_star C_h control0 id q

/-- The current no-call test advances the source restriction to `q.succ`,
which still exists on the last physical date. The complete tag is retained. -/
theorem noCall_currentTag_lintegral
    (ids : Option (CompletePublicTable.IDArray p)) (q : Fin p.T)
    (F : O × Tag → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ v, if noCall q v.1.1 then
      F (v.1, tag q (extensionInput rate q v).1) else 0
      ∂(beta ids q).prod (calendarInnovationLaw p)) =
    ∫⁻ za, F (obs q.castSucc za, tag q za)
      ∂(mu ids).restrict {za | pre q.succ za.1} := by
  let G := fun v : O × (ContinuousLearningRows.TimeControl p × ContinuousControlSlice.Scalar) =>
    if noCall q v.1.1 then F (v.1, tag q (extensionInput rate q v).1) else 0
  have hG : Measurable G :=
    (hF.comp (measurable_fst.prodMk
      ((measurable_currentCellTag rate rewards C_star C_h q).comp
        (measurable_fst.comp (measurable_extensionInput rate q))))).ite
      ((measurableSet_noCallAt rate rewards C_star C_h control0 q).preimage
        (measurable_fst.comp measurable_fst)) measurable_const
  rw [← originalSource_restrict_map_observation_innovation rate rewards C_star C_h control0 ids q]
  change (∫⁻ v, G v ∂_) = _
  have hj : Measurable (fun za : BootstrapPrivateRoundStreams.SourceInput p × Aux =>
      (obs q.castSucc za,
        (ReferenceSourceCurrentControlFreshness.u_t p q za.1, za.2 (q, 1)))) :=
    (measurable_extendedObservation rate rewards C_star C_h control0 q.castSucc).prodMk
      (((ReferenceSourceCurrentControlFreshness.measurable_u_t q).comp measurable_fst).prodMk
        ((measurable_pi_apply (q, 1)).comp measurable_snd))
  rw [lintegral_map hG hj]
  have hpre : MeasurableSet {za : BootstrapPrivateRoundStreams.SourceInput p × Aux |
      pre q.castSucc za.1} :=
    (measurableSet_noCallBefore rate rewards C_star C_h control0 q.castSucc).preimage measurable_fst
  have hsucc : MeasurableSet {za : BootstrapPrivateRoundStreams.SourceInput p × Aux |
      pre q.succ za.1} :=
    (measurableSet_noCallBefore rate rewards C_star C_h control0 q.succ).preimage measurable_fst
  rw [← lintegral_indicator hpre, ← lintegral_indicator hsucc]
  apply lintegral_congr
  intro za
  change (if pre q.castSucc za.1 then
    (if noCall q (sourcePrefix control0 q.val za.1) then
      F (obs q.castSucc za, tag q (extensionInput rate q
        (obs q.castSucc za, (ReferenceSourceCurrentControlFreshness.u_t p q za.1,
          za.2 (q, 1)))).1) else 0) else 0) =
    if pre q.succ za.1 then F (obs q.castSucc za, tag q za) else 0
  rw [currentCellTag_extensionInput_actual]
  rw [← noCallAt_sourcePrefix rate rewards C_star C_h control0 q q.val le_rfl za.1,
    noCallBefore_succ]
  by_cases hp : pre q.castSucc za.1 <;> by_cases hq : noCall q za.1 <;>
    simp only [hp, hq, and_self, false_and, and_false, ite_true, ite_false]

/-- No call through `q` is already a test of the strictly prior physical
source prefix, since the invocation at `q` is decided before its control. -/
theorem noCallThrough_sourcePrefix (q : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p) :
    pre q.succ z ↔ pre q.succ (sourcePrefix control0 q.val z) := by
  unfold NoCallBefore
  apply forall_congr'
  intro t
  exact imp_congr_right (fun ht => noCallAt_sourcePrefix rate rewards C_star C_h control0
    t q.val (by simp only [Fin.val_succ] at ht; omega) z)

local notation "Q" => ReferenceFirstLaunchNumericalCell.queueParameters rate
local notation "kappa" => ReferencePostInvocationCollectionNativeLaw.collectionFastPMF
  rate (fun _ => 1)

private theorem measurable_dependent_fast_sum
    {X : Type*} [MeasurableSpace X]
    (mass : (S : RecordedQueueRun.RunState p.K) → (U : SlowSet p) →
      CanonicalFastSampling.FastArm U → ℝ≥0∞)
    (Phi : X × (SlowSet p × Fin p.K) → ℝ≥0∞) (hPhi : Measurable Phi) :
    Measurable (fun v : X × (RecordedQueueRun.RunState p.K × SlowSet p) =>
      ∑ j : CanonicalFastSampling.FastArm v.2.2,
        Phi (v.1, (v.2.2, j.val)) * mass v.2.1 v.2.2 j) := by
  apply measurable_from_prod_countable_left
  intro a
  change Measurable (fun o : X => ∑ j : CanonicalFastSampling.FastArm a.2,
    Phi (o, (a.2, j.val)) * mass a.1 a.2 j)
  apply Finset.measurable_sum
  intro j _
  exact (hPhi.comp (measurable_id.prodMk measurable_const)).mul measurable_const

private theorem measurable_cell_observation
    {X : Type*} [MeasurableSpace X] :
    Measurable (fun v : X × LogicalCell p rate =>
      (v.1, (v.2.before, v.2.slowSet))) := by
  exact measurable_fst.prodMk
    (((measurable_logicalCell_before (p := p) (rate := rate)).comp measurable_snd).prodMk
      (((measurable_logicalCell_slowSet (p := p) (rate := rate)).mono le_rfl le_top).comp measurable_snd))

private theorem measurable_cell_fast_sum
    {X : Type*} [MeasurableSpace X]
    (mass : (S : RecordedQueueRun.RunState p.K) → (U : SlowSet p) →
      CanonicalFastSampling.FastArm U → ℝ≥0∞)
    (Phi : X × (SlowSet p × Fin p.K) → ℝ≥0∞) (hPhi : Measurable Phi) :
    Measurable (fun v : X × LogicalCell p rate =>
      ∑ j : CanonicalFastSampling.FastArm v.2.slowSet,
        Phi (v.1, (v.2.slowSet, j.val)) * mass v.2.before v.2.slowSet j) := by
  let f : X × (RecordedQueueRun.RunState p.K × SlowSet p) → ℝ≥0∞ := fun v =>
    ∑ j : CanonicalFastSampling.FastArm v.2.2,
      Phi (v.1, (v.2.2, j.val)) * mass v.2.1 v.2.2 j
  let g : X × LogicalCell p rate → X × (RecordedQueueRun.RunState p.K × SlowSet p) :=
    fun v => (v.1, (v.2.before, v.2.slowSet))
  have hf : Measurable f := measurable_dependent_fast_sum (p := p) (X := X) mass Phi hPhi
  have hg : Measurable g := measurable_cell_observation (p := p) (X := X) rate
  change Measurable (f ∘ g)
  exact hf.comp hg

/-- The literal finite FAST average is Borel in the observer and complete
incoming cell. Only the existing countable numerical state is discrete. -/
theorem measurable_fastAverage
    (Phi : O × (SlowSet p × Fin p.K) → ℝ≥0∞) (hPhi : Measurable Phi) :
    Measurable (fun v : O × LogicalCell p rate =>
      ∑ j : CanonicalFastSampling.FastArm v.2.slowSet,
        Phi (v.1, (v.2.slowSet, j.val)) *
          kappa (RecordedQueueRun.scoreWeight Q v.2.before) (fun _ => zero_lt_one)
            (RecordedSlowRefresh.scoreWeight_pos Q v.2.before) v.2.slowSet j) := by
  exact measurable_cell_fast_sum (p := p) (X := O) rate (fun S U j =>
    kappa (RecordedQueueRun.scoreWeight Q S) (fun _ => zero_lt_one)
      (RecordedSlowRefresh.scoreWeight_pos Q S) U j) Phi hPhi

private theorem measurable_clearLiveTest {X : Type*} [MeasurableSpace X]
    (F : X × LogicalCell p rate → ℝ≥0∞) (hF : Measurable F) :
    Measurable (fun v : X × Tag => Sum.elim (fun _ => 0)
      (fun e => if e.before.overflow = false then F (v.1, e) else 0) v.2) := by
  have ht : Measurable (fun v : X × LogicalCell p rate =>
      if v.2.before.overflow = false then F v else 0) := hF.ite
    (((measurable_of_countable (fun S : RecordedQueueRun.RunState p.K => S.overflow)).comp
      (measurable_logicalCell_before.comp measurable_snd)) (measurableSet_singleton false)) measurable_const
  convert (measurable_const.sumElim ht).comp
    (MeasurableEquiv.prodSumDistrib X Unit (LogicalCell p rate)).measurable using 1
  funext v
  rcases v with ⟨o, c⟩
  cases c <;> rfl

private theorem measurable_originalSource_test (q : Fin p.T)
    (F : O × LogicalCell p rate → ℝ≥0∞) (hF : Measurable F) :
    Measurable (fun za : BootstrapPrivateRoundStreams.SourceInput p × Aux =>
      Sum.elim (fun _ => 0) (fun e => if e.before.overflow = false then
        F (obs q.castSucc za, e) else 0) (tag q za)) :=
  (measurable_clearLiveTest rate F hF).comp
    ((measurable_extendedObservation rate rewards C_star C_h control0 q.castSucc).prodMk
      (measurable_currentCellTag rate rewards C_star C_h q))

/-- Arbitrary nonnegative joint tests of the actual retained first-LIVE arm,
on the original enlarged source and with no call through the current date. -/
theorem joint_test_originalSource
    (ids : Option (CompletePublicTable.IDArray p)) (q : Fin p.T)
    (Phi : O × (SlowSet p × Fin p.K) → ℝ≥0∞) (hPhi : Measurable Phi) :
    (∫⁻ v, if noCall q v.1.1 then
      (Sum.elim (fun _ => none) some (tag q (extensionInput rate q v).1)).elim 0
        (fun e => if e.before.overflow = false then
          Phi (v.1, (e.slowSet, e.fastArm)) else 0)
      else 0 ∂(beta ids q).prod (calendarInnovationLaw p)) =
    ∫⁻ za, (Sum.elim (fun _ => none) some (tag q za)).elim 0
      (fun e => if e.before.overflow = false then
        Phi (obs q.castSucc za, (e.slowSet, e.fastArm)) else 0)
      ∂(mu ids).restrict {za | pre q.succ za.1} := by
  let F : O × LogicalCell p rate → ℝ≥0∞ := fun v => Phi (v.1, (v.2.slowSet, v.2.fastArm))
  have hF : Measurable F := hPhi.comp (measurable_fst.prodMk
    (((measurable_logicalCell_slowSet.mono le_rfl le_top).comp measurable_snd).prodMk
      (measurable_logicalCell_fastArm.comp measurable_snd)))
  have h := noCall_currentTag_lintegral rate rewards C_star C_h control0 ids q
    (fun v => Sum.elim (fun _ => 0)
      (fun e => if e.before.overflow = false then F (v.1, e) else 0) v.2)
    (measurable_clearLiveTest rate F hF)
  convert h using 1 <;> apply lintegral_congr <;> intro v
  · by_cases hc : noCall q v.1.1
    · simp only [hc, ite_true]
      cases tag q (extensionInput rate q v).1 <;> rfl
    · simp only [hc, ite_false]
  · cases tag q v <;> rfl

/-- The proposed FAST average has exactly the same original-source transport.
The slow set and PRE on its right remain those of the same actual cell. -/
theorem averaged_test_originalSource
    (ids : Option (CompletePublicTable.IDArray p)) (q : Fin p.T)
    (Phi : O × (SlowSet p × Fin p.K) → ℝ≥0∞) (hPhi : Measurable Phi) :
    (∫⁻ v, if noCall q v.1.1 then
      (Sum.elim (fun _ => none) some (tag q (extensionInput rate q v).1)).elim 0
        (fun e => if e.before.overflow = false then
          ∑ j : CanonicalFastSampling.FastArm e.slowSet,
            Phi (v.1, (e.slowSet, j.val)) *
              kappa (RecordedQueueRun.scoreWeight Q e.before) (fun _ => zero_lt_one)
                (RecordedSlowRefresh.scoreWeight_pos Q e.before) e.slowSet j
          else 0)
      else 0 ∂(beta ids q).prod (calendarInnovationLaw p)) =
    ∫⁻ za, (Sum.elim (fun _ => none) some (tag q za)).elim 0
      (fun e => if e.before.overflow = false then
        ∑ j : CanonicalFastSampling.FastArm e.slowSet,
          Phi (obs q.castSucc za, (e.slowSet, j.val)) *
            kappa (RecordedQueueRun.scoreWeight Q e.before) (fun _ => zero_lt_one)
              (RecordedSlowRefresh.scoreWeight_pos Q e.before) e.slowSet j
        else 0)
      ∂(mu ids).restrict {za | pre q.succ za.1} := by
  let F : O × LogicalCell p rate → ℝ≥0∞ := fun v =>
    ∑ j : CanonicalFastSampling.FastArm v.2.slowSet,
      Phi (v.1, (v.2.slowSet, j.val)) *
        kappa (RecordedQueueRun.scoreWeight Q v.2.before) (fun _ => zero_lt_one)
          (RecordedSlowRefresh.scoreWeight_pos Q v.2.before) v.2.slowSet j
  have h := noCall_currentTag_lintegral rate rewards C_star C_h control0 ids q
    (fun v => Sum.elim (fun _ => 0)
      (fun e => if e.before.overflow = false then F (v.1, e) else 0) v.2)
    (measurable_clearLiveTest rate F (measurable_fastAverage rate Phi hPhi))
  convert h using 1 <;> apply lintegral_congr <;> intro v
  · by_cases hc : noCall q v.1.1
    · simp only [hc, ite_true]
      cases tag q (extensionInput rate q v).1 <;> rfl
    · simp only [hc, ite_false]
  · cases tag q v <;> rfl

/-- Presence of the actual tag supplies the chronological index and the full
PRE state from the same zero-origin first-LIVE queue fold. -/
theorem currentCellTag_inr_before (q : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (a : Aux)
    (e : LogicalCell p rate) (he : tag q (z, a) = Sum.inr e) :
    ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h ≤ q.val ∧
      q.val - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h <
        (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow rate rewards C_star C_h z).length ∧
      e.before = RecordedQueueRun.run Q
        ((ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells rate rewards C_star C_h z).take
          (q.val - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)) := by
  have he' := he
  rw [currentCellTag_eq_lookup] at he'
  have hs : ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h ≤ q.val := by
    by_contra hn
    rw [ite_eq_right hn] at he'
    cases he'
  rw [ite_eq_left hs] at he'
  let n := q.val - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  let path := firstLiveChronologicalPrefix rate rewards C_star C_h (z, a)
  have hn : n < path.length := by
    by_contra h
    rw [ReferenceActiveHorizonMeasurability.listObservationAt,
      List.getElem?_eq_none (Nat.le_of_not_gt h)] at he'
    cases he'
  have hwhole : n < (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
      rate rewards C_star C_h z).length := by
    simpa only [path, firstLiveChronologicalPrefix_length,
      ReferenceFirstLiveOverflowReadout.wholeFirstLiveLength] using hn
  have hentry : path[n]'hn = e := by
    have hx : ReferenceActiveHorizonMeasurability.listObservationAt path n = Sum.inr e := he'
    unfold ReferenceActiveHorizonMeasurability.listObservationAt at hx
    rw [List.getElem?_eq_getElem hn] at hx
    exact Sum.inr.inj hx
  refine ⟨hs, hwhole, ?_⟩
  rw [← hentry]
  exact (firstLiveChronologicalPrefix_queue_states rate rewards C_star C_h z a ⟨n, hwhole⟩).1

/-- A present birth cell has the actual initial PRE, regardless of the
recorder outcome or the post-update overflow flag. -/
theorem currentCellTag_birth_before (q : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (a : Aux)
    (e : LogicalCell p rate) (he : tag q (z, a) = Sum.inr e)
    (hbirth : ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h = q.val) :
    e.before = RecordedQueueRun.initialState p.K := by
  simpa only [hbirth, Nat.sub_self, List.take_zero, RecordedQueueRun.run,
    RecordedQueueRun.execute] using (currentCellTag_inr_before rate rewards C_star C_h q z a e he).2.2

/-- On an actual LIVE tag, the accepted extended observer's list is exactly
the strict chronological LIVE past, before collection can append anything. -/
theorem extendedObservation_live (q : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (a : Aux)
    (e : LogicalCell p rate) (he : tag q (z, a) = Sum.inr e) :
    obs q.castSucc (z, a) =
      (sourcePrefix control0 q.val z, (labelZero a,
        ReferenceFirstLiveChronologicalPrefixCausality.calendarPast rate rewards C_star C_h (z, a) q.val)) := by
  obtain ⟨hs, hk, _⟩ := currentCellTag_inr_before rate rewards C_star C_h q z a e he
  have hbefore : q.val ≤ collectionStart rate rewards C_star C_h z := by
    unfold collectionStart ReferenceFirstLiveOverflowReadout.wholeFirstLiveLength
    omega
  have hp : extendedPast rate rewards C_star C_h q.castSucc (z, a) =
      ReferenceFirstLiveChronologicalPrefixCausality.calendarPast rate rewards C_star C_h (z, a) q.val :=
    extendedPrefixStateAux_before_collectionStart rate rewards C_star C_h
      q.val (Nat.le_of_lt q.isLt) z a hbefore
  exact congrArg (fun L => (sourcePrefix control0 q.val z, (labelZero a, L))) hp

/-- The observer at its actual first launch contains no previous logical
cells, and still retains the entire original label-zero array. -/
theorem extendedObservation_at_start (q : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (a : Aux)
    (hstart : ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h = q.val) :
    obs q.castSucc (z, a) = (sourcePrefix control0 q.val z, (labelZero a, [])) := by
  have hbefore : q.val ≤ collectionStart rate rewards C_star C_h z := by
    unfold collectionStart
    rw [hstart]
    exact Nat.le_add_right _ _
  have hp : extendedPast rate rewards C_star C_h q.castSucc (z, a) =
      ReferenceFirstLiveChronologicalPrefixCausality.calendarPast rate rewards C_star C_h (z, a) q.val :=
    extendedPrefixStateAux_before_collectionStart rate rewards C_star C_h
      q.val (Nat.le_of_lt q.isLt) z a hbefore
  rw [ReferenceFirstLiveChronologicalPrefixCausality.calendarPast_eq_take_elapsed,
    hstart, Nat.sub_self, List.take_zero] at hp
  exact congrArg (fun L => (sourcePrefix control0 q.val z, (labelZero a, L))) hp

/-- Arbitrary current full-control insertion preserves the actual strict
physical source prefix. This concerns the existing continuous rows only. -/
theorem sourcePrefix_replace_current (q : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (u : ContinuousLearningRows.TimeControl p) :
    sourcePrefix control0 q.val
      (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p q z u) =
      sourcePrefix control0 q.val z := by
  exact ReferenceFirstLiveActualFlagSections.sourcePrefix_replace_current control0 q z u

/-- The remaining original-source test splits into exactly birth and positive
offset. Prelaunch and absent tags contribute zero by their literal branches. -/
theorem originalSource_birth_add_positive
    (ids : Option (CompletePublicTable.IDArray p)) (q : Fin p.T)
    (F : O × LogicalCell p rate → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ za, Sum.elim (fun _ => 0) (fun e => F (obs q.castSucc za, e)) (tag q za)
      ∂(mu ids).restrict {za | pre q.succ za.1}) =
    (∫⁻ za, if ReferenceCompletePhysicalHistory.physicalStart rate za.1 rewards C_star C_h = q.val then
      Sum.elim (fun _ => 0) (fun e => F (obs q.castSucc za, e)) (tag q za) else 0
      ∂(mu ids).restrict {za | pre q.succ za.1}) +
    ∫⁻ za, if ReferenceCompletePhysicalHistory.physicalStart rate za.1 rewards C_star C_h < q.val then
      Sum.elim (fun _ => 0) (fun e => F (obs q.castSucc za, e)) (tag q za) else 0
      ∂(mu ids).restrict {za | pre q.succ za.1} := by
  let T : O × Tag → ℝ≥0∞ := fun v => Sum.elim (fun _ => 0) (fun e => F (v.1, e)) v.2
  have hT : Measurable T := by
    convert (measurable_const.sumElim hF).comp
      (MeasurableEquiv.prodSumDistrib O Unit (LogicalCell p rate)).measurable using 1
    funext v
    rcases v with ⟨o, c⟩
    cases c <;> rfl
  let f := fun za : BootstrapPrivateRoundStreams.SourceInput p × Aux => T (obs q.castSucc za, tag q za)
  have hf : Measurable f := hT.comp
    ((measurable_extendedObservation rate rewards C_star C_h control0 q.castSucc).prodMk
      (measurable_currentCellTag rate rewards C_star C_h q))
  have hb : MeasurableSet {za : BootstrapPrivateRoundStreams.SourceInput p × Aux |
      ReferenceCompletePhysicalHistory.physicalStart rate za.1 rewards C_star C_h = q.val} :=
    ((ReferenceCompleteSuffixInputMeasurability.measurable_physicalStart
      rate rewards C_star C_h).comp measurable_fst) (measurableSet_singleton q.val)
  have hf0 : Measurable (fun za : BootstrapPrivateRoundStreams.SourceInput p × Aux =>
      if ReferenceCompletePhysicalHistory.physicalStart rate za.1 rewards C_star C_h = q.val
      then f za else 0) := hf.ite hb measurable_const
  rw [← lintegral_add_left hf0]
  apply lintegral_congr
  intro za
  change f za = (if ReferenceCompletePhysicalHistory.physicalStart rate za.1 rewards C_star C_h = q.val
      then f za else 0) +
    (if ReferenceCompletePhysicalHistory.physicalStart rate za.1 rewards C_star C_h < q.val
      then f za else 0)
  by_cases hb : ReferenceCompletePhysicalHistory.physicalStart rate za.1 rewards C_star C_h = q.val
  · simp only [hb, lt_self_iff_false, ite_true, ite_false, add_zero]
  · by_cases hp : ReferenceCompletePhysicalHistory.physicalStart rate za.1 rewards C_star C_h < q.val
    · simp only [hb, hp, ite_false, ite_true, zero_add]
    · dsimp only [f, T]
      rw [currentCellTag_eq_lookup, ite_eq_right (by omega)]
      simp only [Sum.elim_inl, hb, hp, ite_false, add_zero]

section PositiveSource

variable (row : Fin (ConstructorDimensions.M p)) (q : Fin p.T)
  (s : ℕ) (hs : s ≤ q.val)

local notation "Tagged" => ReferenceFirstLiveChronologicalProposalLaw.TaggedSource
  rate rewards C_star C_h row q s hs control0
local notation "entry" => ReferenceFirstLiveChronologicalProposalLaw.chronologicalCurrentEntry
  rate rewards C_star C_h row q s hs control0
local notation "remainder" => ReferenceFirstLiveCanonicalProposalJointLaw.originalLiveRemainder
  rate rewards C_star C_h row q s hs control0
local notation "nativePast" => ReferenceFirstLivePostUpdateProposalLaw.liveNumericalPast
  rate rewards C_star C_h row q s hs control0

private theorem actualCell_payload_of_input_eq
    {record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)}
    (cell : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell record)
    {input : ReferenceActivePhysicalStep.RoundInput p rate} (hi : record.input = input)
    (selected : ReferenceActivePhysicalStep.Selection input)
    (hselected : (ReferenceActivePhysicalStep.prepare input).coordinator.selection = some selected) :
    cell.selected.view.payload = selected.view.payload := by
  cases hi
  have hc : (ReferenceActivePhysicalStep.prepare record.input).coordinator.selection = some cell.selected := by
    simpa only [record.output_eq, ReferenceActivePhysicalStep.step] using cell.selection_actual
  exact congrArg (fun sel => sel.view.payload) (Option.some.inj (hc.symm.trans hselected))

/-- Both positive-offset original branches supply the actual complete PRE,
including all records. This is an identity, with no clear-state input. -/
theorem originalSource_positive_before (z : Tagged) (a : Aux) :
    nativePast (remainder z) =
      ((entry z a).before.registers, (entry z a).before.overflow, (entry z a).before.records) := by
  let source := ReferenceFirstLiveChronologicalProposalLaw.chronologicalSource
    rate rewards C_star C_h row q s hs control0 z
  let k := ReferenceFirstLiveChronologicalProposalLaw.chronologicalCurrentIndex
    rate rewards C_star C_h row q s hs control0 z
  have hb : (entry z a).before = RecordedQueueRun.run Q
      ((ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells
        rate rewards C_star C_h source.val).take (q.val - s)) :=
    (firstLiveChronologicalPrefix_queue_states rate rewards C_star C_h source.val a k).1
  rw [hb]
  exact ReferenceFirstLiveCanonicalProposalJointLaw.originalSource_numerical_prefix
    rate rewards C_star C_h row q s hs control0 z

/-- The gate on the same chronological entry produces the native clear input;
the reserved FAST remains the original current-control readout on both branches. -/
theorem originalSource_positive_clear_reservedFast (z : Tagged) (a : Aux)
    (hpre : (entry z a).before.overflow = false) :
    ReferenceFirstLivePostUpdateProposalLaw.liveReservedFastOption
      rate rewards C_star C_h row q s hs control0
      (remainder z,
        ReferenceFirstLiveRecordingSourceCylinder.originalControl
          rate rewards C_star C_h row q s hs (Sum.elim Subtype.val Subtype.val z)) =
      some (entry z a).fastArm := by
  have hn := originalSource_positive_before rate rewards C_star C_h control0 row q s hs z a
  have hc : (nativePast (remainder z)).2.1 = false :=
    (congrArg (fun n : ReferenceFirstLiveChronologicalPairIdentity.NumericalPast (p := p) => n.2.1) hn).trans hpre
  exact (ReferenceFirstLiveChronologicalPairIdentity.originalSource_clear_chronological_pair_cell
    rate rewards C_star C_h row q s hs control0 z a hc).2.2.2.1

/-- The intrinsic positive-offset entry is precisely the original current tag,
for continuing pending and empty pending alike. -/
theorem currentCellTag_original_positive (z : Tagged) (a : Aux) :
    tag q ((Sum.elim Subtype.val Subtype.val z).val, a) = Sum.inr (entry z a) := by
  let source := ReferenceFirstLiveChronologicalProposalLaw.chronologicalSource
    rate rewards C_star C_h row q s hs control0 z
  let k := ReferenceFirstLiveChronologicalProposalLaw.chronologicalCurrentIndex
    rate rewards C_star C_h row q s hs control0 z
  have hstart : ReferenceCompletePhysicalHistory.physicalStart rate source.val rewards C_star C_h = s :=
    source.property.2.2
  have hk : q.val - s < (firstLiveChronologicalPrefix rate rewards C_star C_h (source.val, a)).length := by
    rw [firstLiveChronologicalPrefix_length]
    exact k.isLt
  rw [currentCellTag_eq_lookup, show ReferenceCompletePhysicalHistory.physicalStart rate
    (Sum.elim Subtype.val Subtype.val z).val rewards C_star C_h = s from hstart,
    ite_eq_left hs]
  change ReferenceActiveHorizonMeasurability.listObservationAt
    (firstLiveChronologicalPrefix rate rewards C_star C_h (source.val, a)) (q.val - s) = _
  rw [ReferenceActiveHorizonMeasurability.listObservationAt, List.getElem?_eq_getElem hk]
  rfl

/-- The actual cell's clear gate identifies its SAME incoming slow set,
unit first-launch anchor and complete numerical weight vector on both
positive-offset source branches. No such identifications are assumed. -/
theorem originalSource_positive_parameters (z : Tagged) (a : Aux)
    (hpre : (entry z a).before.overflow = false) :
    let x := remainder z
    let payload := ReferenceFirstLiveCanonicalProposalJointLaw.livePayload
      rate rewards C_star C_h row q s hs control0 x
    (entry z a).slowSet = payload.slowSet ∧
      payload.anchor = (fun _ => 1) ∧
      ReferenceFirstLiveCanonicalProposalJointLaw.liveNumericalWeights
        rate rewards C_star C_h row q s hs control0 x =
        RecordedQueueRun.scoreWeight Q (entry z a).before := by
  intro x payload
  let source := ReferenceFirstLiveChronologicalProposalLaw.chronologicalSource
    rate rewards C_star C_h row q s hs control0 z
  let k := ReferenceFirstLiveChronologicalProposalLaw.chronologicalCurrentIndex
    rate rewards C_star C_h row q s hs control0 z
  let r := (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
    rate rewards C_star C_h source.val)[k.val]'k.isLt
  let cell := wholeLiveCell rate rewards C_star C_h source.val r (List.getElem_mem k.isLt)
  let state := RecordedQueueRun.run Q
    ((ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells rate rewards C_star C_h source.val).take k.val)
  let u := ReferenceFirstLiveRecordingSourceCylinder.originalControl rate rewards C_star C_h row q s hs source
  have hret : ReferenceFirstLivePostUpdateProposalLaw.liveRetained
      rate rewards C_star C_h row q s hs control0 x =
      ReferenceFirstLiveRecordingSourceCylinder.sourceRetained
        rate rewards C_star C_h row q s hs control0 source := by
    cases z <;> rfl
  obtain ⟨selected, hselected, hpayload⟩ :=
    ReferenceFirstLiveCanonicalProposalJointLaw.livePayload_selected_at_control
      rate rewards C_star C_h row q s hs control0 x u
  have hinput : ReferenceFirstLiveRecordingReadoutMeasurability.sourceInputAtControl
      (ReferenceFirstLivePostUpdateProposalLaw.liveRetained
        rate rewards C_star C_h row q s hs control0 x) u =
      (ReferenceFirstLiveRecordingSourceCylinder.originalCurrentRecord
        rate rewards C_star C_h row q s hs control0 source).input := by
    rw [hret]
    exact ReferenceFirstLiveRecordingSourceCylinder.sourceInputAtControl_eq_original
      rate rewards C_star C_h row q s hs control0 source
  have hrecord : r = ReferenceFirstLiveRecordingSourceCylinder.originalCurrentRecord
      rate rewards C_star C_h row q s hs control0 source :=
    ReferenceFirstLiveChronologicalProposalLaw.chronologicalCurrentEntry_originalRecord
      rate rewards C_star C_h row q s hs control0 z
  have hpayload : cell.selected.view.payload = payload :=
    (actualCell_payload_of_input_eq rate cell
      ((congrArg ReferenceActivePhysicalHorizon.RoundRecord.input hrecord).trans hinput.symm)
      selected hselected).trans hpayload
  have he : entry z a = appendLogicalCell r cell state a :=
    ReferenceFirstLiveChronologicalProposalLaw.chronologicalCurrentEntry_eq_append
      rate rewards C_star C_h row q s hs control0 z a
  have hc : state.overflow = false := by
    simpa only [he, appendLogicalCell] using hpre
  refine ⟨?_, ?_, ?_⟩
  · rw [he]
    simp only [appendLogicalCell, hc, Bool.false_eq_true, ite_false, hpayload]
  · exact funext (ReferenceFirstLiveCanonicalProposalJointLaw.livePayload_anchor_unit
      rate rewards C_star C_h row q s hs control0 x)
  · have hn := originalSource_positive_before rate rewards C_star C_h control0 row q s hs z a
    funext i
    unfold ReferenceFirstLiveCanonicalProposalJointLaw.liveNumericalWeights
    rw [hn]
    rfl

/-- The whole original observer on either positive branch is a projection of
its accepted native remainder and auxiliary array. In particular no current
FAST, recorder or full-control coordinate has entered this observation. -/
theorem originalSource_positive_observation (z : Tagged) (a : Aux) :
    obs q.castSucc ((Sum.elim Subtype.val Subtype.val z).val, a) =
      (sourcePrefix control0 q.val
        (ReferenceFirstLivePastPairKernelTransport.canonicalRestoredSource
          rate rewards C_star C_h row q s hs control0 (remainder z)),
       (labelZero a,
        (ReferenceFirstLivePastPairKernelTransport.recorderFastPastObservation
          rate rewards C_star C_h row q s hs control0
          (remainder z, (control0.2, a))).1.1)) := by
  let source := ReferenceFirstLiveChronologicalProposalLaw.chronologicalSource
    rate rewards C_star C_h row q s hs control0 z
  let x := remainder z
  let u := ReferenceFirstLiveRecordingSourceCylinder.originalControl rate rewards C_star C_h row q s hs source
  let canonical := ReferenceFirstLiveRecordingSourceCylinder.sourceRecover
    rate rewards C_star C_h row q s hs control0
      (ReferenceFirstLivePostUpdateProposalLaw.liveRetained rate rewards C_star C_h row q s hs control0 x, control0)
  have hret : ReferenceFirstLivePostUpdateProposalLaw.liveRetained
      rate rewards C_star C_h row q s hs control0 x =
      ReferenceFirstLiveRecordingSourceCylinder.sourceRetained
        rate rewards C_star C_h row q s hs control0 source := by
    cases z <;> rfl
  have hr : canonical.val = ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p q source.val control0 := by
    change (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p row q).symm
      (control0, (ReferenceFirstLivePostUpdateProposalLaw.liveRetained
        rate rewards C_star C_h row q s hs control0 x).val) = _
    rw [hret, ReferenceFirstLiveRecordingSourceCylinder.sourceRetained,
      ReferenceTotalSourceDisintegration.sourceRetainedInput_val]
    exact ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_replaceSourceControl
      p row q source.val control0 source.property.1
  have ha : ReferenceFirstLiveRecordingSourceCylinder.sourceRecover
      rate rewards C_star C_h row q s hs control0
        (ReferenceFirstLivePostUpdateProposalLaw.liveRetained
          rate rewards C_star C_h row q s hs control0 x, u) = source := by
    rw [hret]
    exact ReferenceFirstLiveRecordingSourceCylinder.sourceRecover_sourceSplit
      rate rewards C_star C_h row q s hs control0 source
  have hp := ReferenceFirstLivePastPairKernelTransport.restoredCalendarPast_control_independent
    rate rewards C_star C_h row q s hs control0 x u control0 a
  change ReferenceFirstLiveChronologicalPrefixCausality.calendarPast rate rewards C_star C_h
    ((ReferenceFirstLiveRecordingSourceCylinder.sourceRecover rate rewards C_star C_h row q s hs control0
      (ReferenceFirstLivePostUpdateProposalLaw.liveRetained rate rewards C_star C_h row q s hs control0 x, u)).val, a) q.val =
    ReferenceFirstLiveChronologicalPrefixCausality.calendarPast rate rewards C_star C_h (canonical.val, a) q.val at hp
  rw [ha] at hp
  change obs q.castSucc (source.val, a) = _
  rw [extendedObservation_live rate rewards C_star C_h control0 q source.val a (entry z a)
    (currentCellTag_original_positive rate rewards C_star C_h control0 row q s hs z a)]
  apply Prod.ext
  · change sourcePrefix control0 q.val source.val = sourcePrefix control0 q.val canonical.val
    rw [hr, sourcePrefix_replace_current]
  · exact Prod.ext rfl hp

local notation "LiveX" => ReferenceFirstLivePostUpdateProposalLaw.LiveRemainder
  rate rewards C_star C_h row q s hs control0
local notation "payload" => ReferenceFirstLiveCanonicalProposalJointLaw.livePayload
  rate rewards C_star C_h row q s hs control0
local notation "reserved" => ReferenceFirstLivePostUpdateProposalLaw.liveReservedFastOption
  rate rewards C_star C_h row q s hs control0
local notation "nativeState" => fun x : LiveX =>
  (RecordedQueueRun.RunState.mk (Prod.fst (nativePast x))
    (Prod.fst (Prod.snd (nativePast x))) (Prod.snd (Prod.snd (nativePast x))))
local notation "sourceOf" => fun z : Tagged => Subtype.val (Sum.elim Subtype.val Subtype.val z)
local notation "positiveLaw" =>
  Measure.map Sum.inl (ReferenceFirstLiveRecordingSourceCylinder.branchSourceMeasure
    rate rewards C_star C_h row q s hs control0) +
  Measure.map Sum.inr (ReferenceFirstLiveEmptyPendingMarkerLaw.muEmpty
    rate rewards C_star C_h row q s hs control0)
local notation "remainderLaw" =>
  Measure.map Sum.inl (ReferenceFirstLiveRecordingSourceCylinder.branchRemainderMeasure
    rate rewards C_star C_h row q s hs control0) +
  Measure.map Sum.inr (ReferenceFirstLiveEmptyPendingMarkerLaw.nuEmpty
    rate rewards C_star C_h row q s hs control0)

private theorem positive_reserved_fast_lintegral (x : LiveX) (F : Fin p.K → ℝ≥0∞) :
    (∫⁻ u, if (nativePast x).2.1 = false then (reserved (x, u)).elim 0 F else 0
      ∂ContinuousLearningRows.timeControlLaw p) =
    if (nativePast x).2.1 = false then
      ∑ j : CanonicalFastSampling.FastArm (payload x).slowSet, F j.val *
        kappa (RecordedQueueRun.scoreWeight Q (nativeState x)) (fun _ => zero_lt_one)
          (RecordedSlowRefresh.scoreWeight_pos Q (nativeState x)) (payload x).slowSet j else 0 := by
  by_cases hc : (nativePast x).2.1 = false
  · obtain ⟨hp, hl, hu, hm⟩ := ReferenceFirstLiveCanonicalProposalJointLaw.liveReservedFastOption_marginal
      rate rewards C_star C_h row q s hs control0 x hc
    let f : Option (Fin p.K) → ℝ≥0∞ := fun j => j.elim 0 F
    have hf : Measurable f := measurable_of_finite _
    simp only [hc, ite_true]
    have hreserved : Measurable (fun u : ContinuousLearningRows.TimeControl p => reserved (x, u)) :=
      (ReferenceFirstLivePostUpdateProposalLaw.measurable_liveReservedFastOption
        rate rewards C_star C_h row q s hs control0).comp (measurable_const.prodMk measurable_id)
    rw [← lintegral_map hf hreserved, hm,
      lintegral_map hf (measurable_of_finite _), lintegral_fintype]
    apply Finset.sum_congr rfl
    intro j _
    rw [PMF.toMeasure_apply_singleton _ j (measurableSet_singleton j)]
    congr 1
    rw [CanonicalFastSampling.qGammaPMF_apply,
      ReferencePostInvocationCollectionNativeLaw.collectionFastPMF_apply]
    apply congrArg ENNReal.ofReal
    unfold CanonicalFastSampling.qGamma ReferencePostInvocationNoncallGeometry.collectionFastMass
    rw [FastComplementLocality.localConditionalFastMass_eq_conditionalFastLaw]
    unfold FiniteOrientationDisintegration.conditionalFastLaw
    rw [show (payload x).anchor = (fun _ => 1) from funext
      (ReferenceFirstLiveCanonicalProposalJointLaw.livePayload_anchor_unit
        rate rewards C_star C_h row q s hs control0 x)]
    rfl
    exact RecordedSlowRefresh.scoreWeight_pos Q (nativeState x)
  · simp only [hc, Bool.true_eq_false, ite_false, lintegral_zero]

/-- Both original positive-offset restrictions, with their full original
observer and computed incoming clear gate. The FAST marginal is taken only
after the actual recorder has been integrated out. -/
theorem actual_positive_currentTag_fast_lintegral (a : Aux)
    (Phi : O × (SlowSet p × Fin p.K) → ℝ≥0∞) (hPhi : Measurable Phi) :
    (∫⁻ z : Tagged, if (entry z a).before.overflow = false then
      Phi (obs q.castSucc (sourceOf z, a), ((entry z a).slowSet, (entry z a).fastArm))
      else 0 ∂positiveLaw) =
    ∫⁻ z : Tagged, if (entry z a).before.overflow = false then
      ∑ j : CanonicalFastSampling.FastArm (entry z a).slowSet,
        Phi (obs q.castSucc (sourceOf z, a), ((entry z a).slowSet, j.val)) *
          kappa (RecordedQueueRun.scoreWeight Q (entry z a).before)
            (fun _ => zero_lt_one) (RecordedSlowRefresh.scoreWeight_pos Q (entry z a).before)
            (entry z a).slowSet j
      else 0 ∂positiveLaw := by
  let split : Tagged → LiveX × ContinuousLearningRows.TimeControl p := fun z =>
    (remainder z, ReferenceFirstLiveRecordingSourceCylinder.originalControl
      rate rewards C_star C_h row q s hs (Sum.elim Subtype.val Subtype.val z))
  have hsplit : Measurable split := by
    apply measurable_fun_sum
    · exact (measurable_inl.prodMap measurable_id).comp
        (ReferenceFirstLiveRecordingSourceCylinder.measurable_branchSourceSplit
          rate rewards C_star C_h row q s hs control0)
    · exact (measurable_inr.prodMap measurable_id).comp
        (ReferenceFirstLiveEmptyPendingMarkerLaw.measurable_emptySourceSplit
          rate rewards C_star C_h row q s hs control0)
  have hmap : (positiveLaw).map split = (remainderLaw).prod (ContinuousLearningRows.timeControlLaw p) := by
    rw [Measure.map_add _ _ hsplit, Measure.add_prod]
    congr 1
    · rw [Measure.map_map hsplit measurable_inl]
      change Measure.map ((Prod.map Sum.inl id) ∘
        ReferenceFirstLiveRecordingSourceCylinder.branchSourceSplit
          rate rewards C_star C_h row q s hs control0) _ = _
      rw [← Measure.map_map (measurable_inl.prodMap measurable_id)
        (ReferenceFirstLiveRecordingSourceCylinder.measurable_branchSourceSplit
          rate rewards C_star C_h row q s hs control0),
        ReferenceFirstLiveRecordingSourceCylinder.branchSourceSplit_product,
        ← Measure.map_prod_map _ _ measurable_inl measurable_id, Measure.map_id]
    · rw [Measure.map_map hsplit measurable_inr]
      change Measure.map ((Prod.map Sum.inr id) ∘
        ReferenceFirstLiveEmptyPendingMarkerLaw.emptySourceSplit
          rate rewards C_star C_h row q s hs control0) _ = _
      rw [← Measure.map_map (measurable_inr.prodMap measurable_id)
        (ReferenceFirstLiveEmptyPendingMarkerLaw.measurable_emptySourceSplit
          rate rewards C_star C_h row q s hs control0),
        ReferenceFirstLiveEmptyPendingMarkerLaw.emptySourceSplit_product,
        ← Measure.map_prod_map _ _ measurable_inr measurable_id, Measure.map_id]
  let o : LiveX → O := fun x =>
    (sourcePrefix control0 q.val (ReferenceFirstLivePastPairKernelTransport.canonicalRestoredSource
      rate rewards C_star C_h row q s hs control0 x),
      (labelZero a, (ReferenceFirstLivePastPairKernelTransport.recorderFastPastObservation
        rate rewards C_star C_h row q s hs control0 (x, (control0.2, a))).1.1))
  have ho : Measurable o := by
    have hsource : Measurable (ReferenceFirstLivePastPairKernelTransport.canonicalRestoredSource
        rate rewards C_star C_h row q s hs control0) := (measurable_subtype_coe.comp
      (ReferenceFirstLiveRecordingSourceCylinder.measurable_sourceRecover
        rate rewards C_star C_h row q s hs control0)).comp
      ((ReferenceFirstLivePostUpdateProposalLaw.measurable_liveRetained
        rate rewards C_star C_h row q s hs control0).prodMk measurable_const)
    exact ((measurable_sourcePrefix control0 q.val).comp hsource).prodMk
      (measurable_const.prodMk (measurable_fst.comp (measurable_fst.comp
        ((ReferenceFirstLivePastPairKernelTransport.measurable_recorderFastPastObservation
          rate rewards C_star C_h row q s hs control0).comp
          (measurable_id.prodMk measurable_const)))))
  have hU : Measurable (fun x : LiveX => (payload x).slowSet) := by
    apply measurable_fun_sum
    · exact (ReferenceCollectionDispatchMeasurability.measurable_payloadSlowSet.comp
        ReferenceFirstLiveRecordingReadoutMeasurability.measurable_selectedBaselinePayload)
    · exact (ReferenceCollectionDispatchMeasurability.measurable_payloadSlowSet.comp
        ReferenceFirstLiveEmptyPendingMarkerLaw.measurable_selectedBaselinePayload)
  have hS : Measurable nativeState :=
    (measurable_of_countable (fun n : ReferenceFirstLiveChronologicalPairIdentity.NumericalPast (p := p) =>
      (⟨n.1, n.2.1, n.2.2⟩ : RecordedQueueRun.RunState p.K))).comp
      (ReferenceFirstLivePostUpdateProposalLaw.measurable_liveNumericalPast
        rate rewards C_star C_h row q s hs control0)
  let R : LiveX × ContinuousLearningRows.TimeControl p → ℝ≥0∞ := fun xu =>
    if (nativeState xu.1).overflow = false then
      (reserved xu).elim 0 (fun j => Phi (o xu.1, ((payload xu.1).slowSet, j))) else 0
  let A : LiveX → ℝ≥0∞ := fun x => if (nativeState x).overflow = false then
    ∑ j : CanonicalFastSampling.FastArm (payload x).slowSet,
      Phi (o x, ((payload x).slowSet, j.val)) *
        kappa (RecordedQueueRun.scoreWeight Q (nativeState x)) (fun _ => zero_lt_one)
          (RecordedSlowRefresh.scoreWeight_pos Q (nativeState x)) (payload x).slowSet j else 0
  have hclear : MeasurableSet {x : LiveX | (nativeState x).overflow = false} :=
    ReferenceFirstLiveCanonicalProposalJointLaw.measurableSet_liveClear
      rate rewards C_star C_h row q s hs control0
  have hR : Measurable R := by
    have hg : Measurable (fun v : LiveX × Option (Fin p.K) =>
        v.2.elim 0 (fun j => Phi (o v.1, ((payload v.1).slowSet, j)))) := by
      apply measurable_from_prod_countable_left
      intro j
      cases j with
      | none => exact measurable_const
      | some j => exact hPhi.comp (ho.prodMk (hU.prodMk measurable_const))
    exact (hg.comp (measurable_fst.prodMk
      (ReferenceFirstLivePostUpdateProposalLaw.measurable_liveReservedFastOption
        rate rewards C_star C_h row q s hs control0))).ite
      (hclear.preimage measurable_fst) measurable_const
  have hA : Measurable A :=
    ((measurable_dependent_fast_sum (X := O) (fun S U j =>
      kappa (RecordedQueueRun.scoreWeight Q S) (fun _ => zero_lt_one)
        (RecordedSlowRefresh.scoreWeight_pos Q S) U j) Phi hPhi).comp
      (ho.prodMk (hS.prodMk hU))).ite hclear measurable_const
  have hlocal (x : LiveX) : (∫⁻ u, R (x, u) ∂ContinuousLearningRows.timeControlLaw p) = A x :=
    positive_reserved_fast_lintegral rate rewards C_star C_h control0 row q s hs x
      (fun j => Phi (o x, ((payload x).slowSet, j)))
  have hbefore (z : Tagged) : nativeState (remainder z) = (entry z a).before := by
    have h := originalSource_positive_before rate rewards C_star C_h control0 row q s hs z a
    exact congrArg (fun n : ReferenceFirstLiveChronologicalPairIdentity.NumericalPast (p := p) =>
      (⟨n.1, n.2.1, n.2.2⟩ : RecordedQueueRun.RunState p.K)) h
  have hflag (z : Tagged) : (nativePast (remainder z)).2.1 = (entry z a).before.overflow :=
    congrArg RecordedQueueRun.RunState.overflow (hbefore z)
  have hleft (z : Tagged) : R (split z) =
      if (entry z a).before.overflow = false then
        Phi (obs q.castSucc (sourceOf z, a), ((entry z a).slowSet, (entry z a).fastArm)) else 0 := by
    dsimp only [R, split]
    by_cases hc : (entry z a).before.overflow = false
    · obtain ⟨hU, _, _⟩ := originalSource_positive_parameters rate rewards C_star C_h control0 row q s hs z a hc
      rw [ite_eq_left ((hflag z).trans hc), ite_eq_left hc,
        originalSource_positive_clear_reservedFast rate rewards C_star C_h control0 row q s hs z a hc,
        Option.elim_some, ← hU]
      exact congrArg (fun o => Phi (o, ((entry z a).slowSet, (entry z a).fastArm)))
        (originalSource_positive_observation rate rewards C_star C_h control0 row q s hs z a).symm
    · rw [ite_eq_right (fun hx => hc ((hflag z).symm.trans hx)), ite_eq_right hc]
  have hright (z : Tagged) : A (split z).1 =
      if (entry z a).before.overflow = false then
        ∑ j : CanonicalFastSampling.FastArm (entry z a).slowSet,
          Phi (obs q.castSucc (sourceOf z, a), ((entry z a).slowSet, j.val)) *
            kappa (RecordedQueueRun.scoreWeight Q (entry z a).before) (fun _ => zero_lt_one)
              (RecordedSlowRefresh.scoreWeight_pos Q (entry z a).before) (entry z a).slowSet j else 0 := by
    dsimp only [A, split]
    by_cases hc : (entry z a).before.overflow = false
    · obtain ⟨hU, _, _⟩ := originalSource_positive_parameters rate rewards C_star C_h control0 row q s hs z a hc
      rw [ite_eq_left ((hflag z).trans hc), ite_eq_left hc]
      let average := fun (o' : O) (S : RecordedQueueRun.RunState p.K) (U : SlowSet p) =>
        ∑ j : CanonicalFastSampling.FastArm U, Phi (o', (U, j.val)) *
          kappa (RecordedQueueRun.scoreWeight Q S) (fun _ => zero_lt_one)
            (RecordedSlowRefresh.scoreWeight_pos Q S) U j
      have hoz : o (remainder z) = obs q.castSucc (sourceOf z, a) :=
        (originalSource_positive_observation rate rewards C_star C_h control0 row q s hs z a).symm
      change average (o (remainder z)) (nativeState (remainder z)) (payload (remainder z)).slowSet = _
      rw [hoz]
      exact congrArg₂ (average (obs q.castSucc (sourceOf z, a))) (hbefore z) hU.symm
    · rw [ite_eq_right (fun hx => hc ((hflag z).symm.trans hx)), ite_eq_right hc]
  simp_rw [← hleft, ← hright]
  change (∫⁻ z, R (split z) ∂positiveLaw) = ∫⁻ z, (A ∘ Prod.fst) (split z) ∂positiveLaw
  rw [← lintegral_map hR hsplit, ← lintegral_map (hA.comp measurable_fst) hsplit, hmap,
    lintegral_prod _ hR.aemeasurable, lintegral_prod _ (hA.comp measurable_fst).aemeasurable]
  apply lintegral_congr
  intro x
  rw [hlocal]
  simp only [Function.comp_apply, lintegral_const, measure_univ, mul_one]

end PositiveSource

section BirthSource

open ReferenceFirstLiveBirthJointSourceLaw
open ReferenceFirstLaunchRecordingSourceLaw
open ReferenceFirstLaunchRecordingPhysicalMarker

variable (row : Fin (ConstructorDimensions.M p)) (q : Fin p.T)

local notation "X0" => ReferenceFirstLaunchRecordingPhysicalMarker.RetainedStart
  rate rewards C_star C_h row q control0
local notation "V0" => ReferenceFirstLaunchRecordingPhysicalMarker.AssignmentVector p
local notation "D0" => ReferenceFirstLaunchRecordingPhysicalMarker.NonAssignmentControl p
local notation "Z0" => ReferenceFirstLiveBirthJointSourceLaw.BirthSource p rate rewards C_star C_h row q
local notation "coords0" => ReferenceFirstLaunchRecordingSourceLaw.sourceCoordinates
  rate rewards C_star C_h row q control0
local notation "mu0" => ReferenceTotalSourceDisintegration.sourceStratumMeasure
  rate rewards C_star C_h q (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex row q)
local notation "nu0" => ReferenceRetainedSourceCoupling.retainedRemainderMeasure
  rate rewards C_star C_h row q q.val le_rfl control0
local notation "U0" => fun v : V0 => AssignmentStartPayload.Input.slowSet
  (ReferenceDownReception.ChoiceTimeView.payload (birthView rate q v))

private theorem birthPairOnSlice_measurable (v : V0) :
    Measurable (birthPairOnSlice rate q v) := by
  let view := birthView rate q v
  let valid := birthView_valid rate q v
  let W := ReferenceFirstWindowNumericalStream.sourceWeights view.payload view.complementWeights
  have hrec : Measurable (ReferenceRankInstallationRecorderFoundation.installationRecordingMap
      rate q view valid) := by
    unfold ReferenceRankInstallationRecorderFoundation.installationRecordingMap
    exact SnapshotRecordingKernel.measurable_recordingMap p
      (.live view.payload.assignment
        (ReferenceRankInstallationRecorderFoundation.installationSnapshot view.payload.assignment))
      rate.eta.val rate.eta.property rate.sourceCap view.payload.anchor W view.payload.anchor_pos
      (ReferenceFirstWindowNumericalStream.sourceWeights_pos view.payload view.complementWeights view.cutoff q valid)
      (ReferenceFirstWindowNumericalStream.sourceWeights_lower view.payload view.complementWeights view.cutoff q valid)
      (ReferenceFirstWindowNumericalStream.sourceWeights_upper view.payload view.complementWeights view.cutoff q valid) true
  exact hrec.prodMk (measurable_subtype_coe.comp
    (ReferenceRankInstallationRecorderFastLaw.measurable_reservedFastAtView rate q view valid))

private theorem birthPairKernel_fast (v : V0) :
    (birthPairKernel rate q v).map Prod.snd =
      (kappa (RecordedQueueRun.scoreWeight Q (RecordedQueueRun.initialState p.K))
        (fun _ => zero_lt_one)
        (RecordedSlowRefresh.scoreWeight_pos Q (RecordedQueueRun.initialState p.K)) (U0 v)).toMeasure.map
          (fun j => j.val) := by
  let view := birthView rate q v
  let valid := birthView_valid rate q v
  have hres := ReferenceRankInstallationRecorderFastLaw.measurable_reservedFastAtView rate q view valid
  rw [birthPairKernel, Measure.map_map measurable_snd (birthPairOnSlice_measurable rate q v)]
  change (ContinuousControlSlice.sliceLaw p.m p.K).map
    ((fun j : CanonicalFastSampling.FastArm (U0 v) => j.val) ∘
      ReferenceRankInstallationRecorderFastLaw.reservedFastAtView rate q view valid) = _
  rw [← Measure.map_map measurable_subtype_coe hres,
    ReferenceRankInstallationRecorderFastLaw.reservedFastAtView_pushforward]
  have ha : view.payload.anchor = fun _ => 1 := by
    funext i
    simp only [view, birthView, ReferenceFirstLiveBirthChronologicalReadout.unitBirthView,
      AssignmentStartPayload.Input.ofFirstAssignment, FirstAssignmentLaunch.Input.anchor]
  have hw : ReferenceFirstWindowNumericalStream.sourceWeights view.payload view.complementWeights =
      fun _ => 1 := by
    funext i
    unfold ReferenceFirstWindowNumericalStream.sourceWeights
    split_ifs <;> simp only [view, birthView,
      ReferenceFirstLiveBirthChronologicalReadout.unitBirthView,
      AssignmentStartPayload.Input.ofFirstAssignment, FirstAssignmentLaunch.Input.anchor]
  have hi : RecordedQueueRun.scoreWeight Q (RecordedQueueRun.initialState p.K) = fun _ => 1 :=
    funext (fun _ => by simp only [RecordedQueueRun.scoreWeight, RecordedQueueRun.initialState,
      ScoreWeights.scoreWeight, pow_zero])
  apply congrArg (fun M : PMF (CanonicalFastSampling.FastArm (U0 v)) =>
    M.toMeasure.map (fun j => j.val))
  apply PMF.ext
  intro j
  rw [CanonicalFastSampling.qGammaPMF_apply,
    ReferencePostInvocationCollectionNativeLaw.collectionFastPMF_apply]
  apply congrArg ENNReal.ofReal
  unfold CanonicalFastSampling.qGamma ReferencePostInvocationNoncallGeometry.collectionFastMass
  rw [FastComplementLocality.localConditionalFastMass_eq_conditionalFastLaw]
  unfold FiniteOrientationDisintegration.conditionalFastLaw
  rw [ha, hw, hi]
  exact RecordedSlowRefresh.scoreWeight_pos Q (RecordedQueueRun.initialState p.K)

/-- Arbitrary nonnegative tests of the whole original birth remainder, whole
assignment vector and actual reserved FAST arm. The original recorder/FAST
pair is marginalized only after its accepted nonassignment pushforward. -/
theorem actual_birth_fast_lintegral
    (F : X0 × (V0 × Fin p.K) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ z, F ((coords0 z).1, ((coords0 z).2.1,
      (ReferenceFirstLaunchOriginalAuxiliaryReward.actualFirstFastArm
        rate rewards C_star C_h row q control0 z).val)) ∂mu0) =
    ∫⁻ z, ∑ j : CanonicalFastSampling.FastArm (U0 (coords0 z).2.1),
      F ((coords0 z).1, ((coords0 z).2.1, j.val)) *
        kappa (RecordedQueueRun.scoreWeight Q (RecordedQueueRun.initialState p.K))
          (fun _ => zero_lt_one)
          (RecordedSlowRefresh.scoreWeight_pos Q (RecordedQueueRun.initialState p.K))
          (U0 (coords0 z).2.1) j ∂mu0 := by
  let split := LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p
  let back : X0 × (V0 × D0) → X0 × ContinuousLearningRows.TimeControl p :=
    Prod.map id split.symm
  let out := fun c : X0 × (V0 × D0) =>
    birthObservation rate rewards C_star C_h row q control0 (back c)
  have ho : Measurable out :=
    (measurable_birthObservation rate rewards C_star C_h row q control0).comp
      (measurable_id.prodMap split.symm.measurable)
  have hout (x : X0) (v : V0) (d : D0) :
      out (x, (v, d)) = (x, (v, birthPairOnSlice rate q v (currentControl v d).1)) := by
    change (x, ((split (split.symm (v, d))).1,
      birthPairOnSlice rate q (split (split.symm (v, d))).1 (split.symm (v, d)).1)) = _
    rw [split.apply_symm_apply]
    rfl
  let R := fun c : X0 × (V0 × D0) => F ((out c).1, ((out c).2.1, (out c).2.2.2))
  have hR : Measurable R := hF.comp
    ((measurable_fst.comp ho).prodMk
      ((measurable_fst.comp (measurable_snd.comp ho)).prodMk
        (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp ho)))))
  let A := fun c : X0 × (V0 × D0) =>
    ∑ j : CanonicalFastSampling.FastArm (U0 c.2.1),
      F (c.1, (c.2.1, j.val)) *
        kappa (RecordedQueueRun.scoreWeight Q (RecordedQueueRun.initialState p.K))
          (fun _ => zero_lt_one)
          (RecordedSlowRefresh.scoreWeight_pos Q (RecordedQueueRun.initialState p.K)) (U0 c.2.1) j
  have hU : Measurable (U0) := by
    exact (CanonicalAssignmentVector.measurable_canonicalSlowSampler p.two_le_m p.m_lt_K
      (fun _ => 1) (fun _ => 1) (fun _ => zero_lt_one) (fun _ => zero_lt_one)).mono le_rfl le_top
  let F' : (X0 × V0) × (SlowSet p × Fin p.K) → ℝ≥0∞ := fun w =>
    F (w.1.1, (w.1.2, w.2.2))
  have hF' : Measurable F' := hF.comp
    ((measurable_fst.comp measurable_fst).prodMk
      ((measurable_snd.comp measurable_fst).prodMk (measurable_snd.comp measurable_snd)))
  have hA : Measurable A := by
    let mass := fun (_S : RecordedQueueRun.RunState p.K) (U : SlowSet p) (j : CanonicalFastSampling.FastArm U) =>
      kappa (RecordedQueueRun.scoreWeight Q (RecordedQueueRun.initialState p.K))
        (fun _ => zero_lt_one)
        (RecordedSlowRefresh.scoreWeight_pos Q (RecordedQueueRun.initialState p.K)) U j
    let g : X0 × (V0 × D0) → (X0 × V0) × (RecordedQueueRun.RunState p.K × SlowSet p) :=
      fun c => ((c.1, c.2.1), (RecordedQueueRun.initialState p.K, U0 c.2.1))
    have hg : Measurable g :=
      (measurable_fst.prodMk (measurable_fst.comp measurable_snd)).prodMk
        (measurable_const.prodMk (hU.comp (measurable_fst.comp measurable_snd)))
    let f : (X0 × V0) × (RecordedQueueRun.RunState p.K × SlowSet p) → ℝ≥0∞ := fun w =>
      ∑ j : CanonicalFastSampling.FastArm w.2.2,
        F' (w.1, (w.2.2, j.val)) * mass w.2.1 w.2.2 j
    have hf : Measurable f := measurable_dependent_fast_sum (p := p) mass F' hF'
    change Measurable (f ∘ g)
    exact hf.comp hg
  have hlocal (x : X0) (v : V0) :
      (∫⁻ d, R (x, (v, d)) ∂nonAssignmentLaw p) = A (x, (v, (split control0).2)) := by
    let pair := fun d : D0 => birthPairOnSlice rate q v (currentControl v d).1
    have hp : Measurable pair :=
      (birthPairOnSlice_measurable rate q v).comp
        (measurable_fst.comp (split.symm.measurable.comp (measurable_const.prodMk measurable_id)))
    let G : BirthPair p → ℝ≥0∞ := fun y => F (x, (v, y.2))
    have hG : Measurable G := hF.comp
      (measurable_const.prodMk (measurable_const.prodMk measurable_snd))
    calc
      _ = ∫⁻ d, G (pair d) ∂nonAssignmentLaw p := by
        apply lintegral_congr
        intro d
        simp only [R, hout, G, pair]
      _ = ∫⁻ y, G y ∂(nonAssignmentLaw p).map pair := (lintegral_map hG hp).symm
      _ = ∫⁻ y, G y ∂birthPairKernel rate q v := by rw [birthPairKernel_eq_nonassignment]
      _ = ∫⁻ j, F (x, (v, j)) ∂(birthPairKernel rate q v).map Prod.snd :=
        (lintegral_map (hF.comp (measurable_const.prodMk
          (measurable_const.prodMk measurable_id))) measurable_snd).symm
      _ = ∫⁻ j : CanonicalFastSampling.FastArm (U0 v), F (x, (v, j.val))
          ∂(kappa (RecordedQueueRun.scoreWeight Q (RecordedQueueRun.initialState p.K))
            (fun _ => zero_lt_one)
            (RecordedSlowRefresh.scoreWeight_pos Q (RecordedQueueRun.initialState p.K)) (U0 v)).toMeasure := by
        have hFin : Measurable (fun j : Fin p.K => F (x, (v, j))) := measurable_of_finite _
        rw [birthPairKernel_fast rate q v]
        exact lintegral_map hFin measurable_subtype_coe
      _ = _ := by
        rw [lintegral_fintype]
        dsimp only [A]
        apply Finset.sum_congr rfl
        intro j _
        rw [PMF.toMeasure_apply_singleton _ j (measurableSet_singleton j)]
  have hactual (z : Z0) : R (coords0 z) = F ((coords0 z).1, ((coords0 z).2.1,
      (ReferenceFirstLaunchOriginalAuxiliaryReward.actualFirstFastArm
        rate rewards C_star C_h row q control0 z).val)) := by
    rw [show coords0 z = ((coords0 z).1, ((coords0 z).2.1, (coords0 z).2.2)) from rfl]
    simp only [R, hout]
    have hp : (ReferenceFirstLaunchRecordingSourceLaw.sourceMarker
        rate rewards C_star C_h row q control0 z,
        (ReferenceFirstLaunchOriginalAuxiliaryReward.actualFirstFastArm
          rate rewards C_star C_h row q control0 z).val) =
        birthPairOnSlice rate q (coords0 z).2.1
          (currentControl (coords0 z).2.1 (coords0 z).2.2).1 :=
      ReferenceFirstLiveBirthChronologicalReadout.actual_birth_pair_eq_unitBirthPair
        rate rewards C_star C_h row q control0 z
    exact congrArg (fun j : Fin p.K => F ((coords0 z).1, ((coords0 z).2.1, j)))
      (congrArg Prod.snd hp).symm
  rw [show (fun z : Z0 => F ((coords0 z).1, ((coords0 z).2.1,
    (ReferenceFirstLaunchOriginalAuxiliaryReward.actualFirstFastArm
      rate rewards C_star C_h row q control0 z).val))) = R ∘ coords0 from
        funext (fun z => (hactual z).symm)]
  change (∫⁻ z, R (coords0 z) ∂mu0) = ∫⁻ z, A (coords0 z) ∂mu0
  rw [← lintegral_map hR (measurable_sourceCoordinates rate rewards C_star C_h row q control0),
    ← lintegral_map hA (measurable_sourceCoordinates rate rewards C_star C_h row q control0),
    map_sourceCoordinates]
  rw [lintegral_prod _ hR.aemeasurable, lintegral_prod _ hA.aemeasurable]
  apply lintegral_congr
  intro x
  have hRx : Measurable (fun y : V0 × D0 => R (x, y)) := hR.comp measurable_prodMk_left
  have hAx : Measurable (fun y : V0 × D0 => A (x, y)) := hA.comp measurable_prodMk_left
  rw [lintegral_prod _ hRx.aemeasurable, lintegral_prod _ hAx.aemeasurable]
  apply lintegral_congr
  intro v
  rw [hlocal]
  change A (x, (v, (split control0).2)) = ∫⁻ _ : D0, A (x, (v, (split control0).2)) ∂nonAssignmentLaw p
  rw [lintegral_const, measure_univ, mul_one]

/-- Erasing the original current control at birth preserves the complete
observer, including the original label-zero array and its empty prior list. -/
theorem birth_observation_coordinates (z : Z0) (a : Aux) :
    obs q.castSucc (z.val, a) =
      obs q.castSucc ((restoreSource rate rewards C_star C_h row q control0
        ((coords0 z).1, control0)).val, a) := by
  let restored := restoreSource rate rewards C_star C_h row q control0 ((coords0 z).1, control0)
  have hr : restored.val = ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p q z.val control0 := by
    change (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p row q).symm
      (control0, (ReferenceTotalSourceDisintegration.sourceRetainedInput
        rate rewards C_star C_h q control0
        (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex row q) z).val) = _
    rw [ReferenceTotalSourceDisintegration.sourceRetainedInput_val]
    exact ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_replaceSourceControl
      p row q z.val control0 z.property.1
  rw [extendedObservation_at_start rate rewards C_star C_h control0 q z.val a z.property.2.2,
    extendedObservation_at_start rate rewards C_star C_h control0 q restored.val a restored.property.2.2]
  rw [hr, sourcePrefix_replace_current]

/-- The unbounded birth-source evaluation with the exact complete prefix
observer and the actual incoming slow set and original FAST arm. The auxiliary
array is arbitrary; it is neither discarded nor normalized. -/
theorem actual_birth_observer_fast_lintegral (a : Aux)
    (Phi : O × (SlowSet p × Fin p.K) → ℝ≥0∞) (hPhi : Measurable Phi) :
    (∫⁻ z, Phi (obs q.castSucc (z.val, a),
      (ReferenceFirstLaunchOriginalAuxiliaryReward.actualFirstSlowSet
        rate rewards C_star C_h row q control0 z,
       (ReferenceFirstLaunchOriginalAuxiliaryReward.actualFirstFastArm
        rate rewards C_star C_h row q control0 z).val)) ∂mu0) =
    ∫⁻ z, ∑ j : CanonicalFastSampling.FastArm
        (ReferenceFirstLaunchOriginalAuxiliaryReward.actualFirstSlowSet
          rate rewards C_star C_h row q control0 z),
      Phi (obs q.castSucc (z.val, a),
        (ReferenceFirstLaunchOriginalAuxiliaryReward.actualFirstSlowSet
          rate rewards C_star C_h row q control0 z, j.val)) *
        kappa (RecordedQueueRun.scoreWeight Q (RecordedQueueRun.initialState p.K))
          (fun _ => zero_lt_one)
          (RecordedSlowRefresh.scoreWeight_pos Q (RecordedQueueRun.initialState p.K))
          (ReferenceFirstLaunchOriginalAuxiliaryReward.actualFirstSlowSet
            rate rewards C_star C_h row q control0 z) j ∂mu0 := by
  let o := fun x : X0 => obs q.castSucc
    ((restoreSource rate rewards C_star C_h row q control0 (x, control0)).val, a)
  have ho : Measurable o :=
    (measurable_extendedObservation rate rewards C_star C_h control0 q.castSucc).comp
      ((measurable_subtype_coe.comp
        ((measurable_restoreSource rate rewards C_star C_h row q control0).comp
          (measurable_id.prodMk measurable_const))).prodMk measurable_const)
  have hU : Measurable U0 :=
    (CanonicalAssignmentVector.measurable_canonicalSlowSampler p.two_le_m p.m_lt_K
      (fun _ => 1) (fun _ => 1) (fun _ => zero_lt_one) (fun _ => zero_lt_one)).mono le_rfl le_top
  let G : X0 × (V0 × Fin p.K) → ℝ≥0∞ := fun c =>
    Phi (o c.1, (U0 c.2.1, c.2.2))
  have hG : Measurable G := hPhi.comp
    ((ho.comp measurable_fst).prodMk
      ((hU.comp (measurable_fst.comp measurable_snd)).prodMk
        (measurable_snd.comp measurable_snd)))
  have hs (z : Z0) : ReferenceFirstLaunchOriginalAuxiliaryReward.actualFirstSlowSet
      rate rewards C_star C_h row q control0 z = U0 (coords0 z).2.1 :=
    ReferenceFirstLaunchOriginalAuxiliaryReward.actualFirstSlowSet_eq_canonical
      rate rewards C_star C_h row q control0 z
  have h := actual_birth_fast_lintegral rate rewards C_star C_h control0 row q G hG
  convert h using 1 <;> apply lintegral_congr <;> intro z
  · change Phi (obs q.castSucc (z.val, a),
        (ReferenceFirstLaunchOriginalAuxiliaryReward.actualFirstSlowSet
          rate rewards C_star C_h row q control0 z,
         (ReferenceFirstLaunchOriginalAuxiliaryReward.actualFirstFastArm
          rate rewards C_star C_h row q control0 z).val)) =
      Phi (o (coords0 z).1, (U0 (coords0 z).2.1,
        (ReferenceFirstLaunchOriginalAuxiliaryReward.actualFirstFastArm
          rate rewards C_star C_h row q control0 z).val))
    exact congrArg Phi (Prod.ext
      (birth_observation_coordinates rate rewards C_star C_h control0 row q z a)
      (Prod.ext (hs z) rfl))
  · rw [birth_observation_coordinates rate rewards C_star C_h control0 row q z a, hs z]

/-- The actual birth tag supplies its initial PRE and original pair fields,
on every source in the original launch stratum. -/
theorem actual_birth_tag_fields (z : Z0) (a : Aux) :
    ∃ e : LogicalCell p rate, tag q (z.val, a) = Sum.inr e ∧
      e.before = RecordedQueueRun.initialState p.K ∧
      e.slowSet = ReferenceFirstLaunchOriginalAuxiliaryReward.actualFirstSlowSet
        rate rewards C_star C_h row q control0 z ∧
      e.fastArm = (ReferenceFirstLaunchOriginalAuxiliaryReward.actualFirstFastArm
        rate rewards C_star C_h row q control0 z).val := by
  have hk := ReferenceFirstLiveBirthChronologicalReadout.actual_birth_chronological_prefix_positive
    rate rewards C_star C_h row q z
  let path := firstLiveChronologicalPrefix rate rewards C_star C_h (z.val, a)
  have hn : 0 < path.length := by
    rw [firstLiveChronologicalPrefix_length]
    exact hk
  let e := path[0]'hn
  have ht : tag q (z.val, a) = Sum.inr e := by
    rw [currentCellTag_eq_lookup,
      show ReferenceCompletePhysicalHistory.physicalStart rate z.val rewards C_star C_h = q.val from z.property.2.2,
      ite_eq_left (Nat.le_refl _), Nat.sub_self]
    change ReferenceActiveHorizonMeasurability.listObservationAt path 0 = _
    rw [ReferenceActiveHorizonMeasurability.listObservationAt, List.getElem?_eq_getElem hn]
  obtain ⟨_, _, _, hb, _, _, _, hs, hf, _⟩ :=
    ReferenceFirstLiveBirthChronologicalReadout.actual_birth_chronological_entry_readout
      rate rewards C_star C_h row q control0 z a
  exact ⟨e, ht, hb, hs, hf⟩

/-- The literal actual-tag FAST evaluation on the original birth-source
measure, with the same observer and same cell on both sides. -/
theorem actual_birth_currentTag_fast_lintegral (a : Aux)
    (Phi : O × (SlowSet p × Fin p.K) → ℝ≥0∞) (hPhi : Measurable Phi) :
    (∫⁻ z, (Sum.elim (fun _ => none) some (tag q (z.val, a))).elim 0
      (fun e => if e.before.overflow = false then
        Phi (obs q.castSucc (z.val, a), (e.slowSet, e.fastArm)) else 0) ∂mu0) =
    ∫⁻ z, (Sum.elim (fun _ => none) some (tag q (z.val, a))).elim 0
      (fun e => if e.before.overflow = false then
        ∑ j : CanonicalFastSampling.FastArm e.slowSet,
          Phi (obs q.castSucc (z.val, a), (e.slowSet, j.val)) *
            kappa (RecordedQueueRun.scoreWeight Q e.before) (fun _ => zero_lt_one)
              (RecordedSlowRefresh.scoreWeight_pos Q e.before) e.slowSet j
        else 0) ∂mu0 := by
  have h := actual_birth_observer_fast_lintegral rate rewards C_star C_h control0 row q a Phi hPhi
  convert h using 1 <;> apply lintegral_congr <;> intro z
  · obtain ⟨e, ht, hb, hs, hf⟩ := actual_birth_tag_fields rate rewards C_star C_h control0 row q z a
    have hc : e.before.overflow = false := hb ▸ rfl
    simp only [ht, Sum.elim_inr, Option.elim_some, ite_eq_left hc, hs, hf]
  · obtain ⟨e, ht, hb, hs, _⟩ := actual_birth_tag_fields rate rewards C_star C_h control0 row q z a
    have hc : e.before.overflow = false := hb ▸ rfl
    simp only [ht, Sum.elim_inr, Option.elim_some]
    rw [ite_eq_left hc]
    let average := fun (S : RecordedQueueRun.RunState p.K) (U : SlowSet p) =>
      ∑ j : CanonicalFastSampling.FastArm U,
        Phi (obs q.castSucc (z.val, a), (U, j.val)) *
          kappa (RecordedQueueRun.scoreWeight Q S) (fun _ => zero_lt_one)
            (RecordedSlowRefresh.scoreWeight_pos Q S) U j
    exact congrArg₂ average hb hs

/-- The birth contribution with the SAME unnormalized no-call-through-current
restriction as the original-source reduction. The restriction is inserted as
a measurable observer test, without a numerical or source-law premise. -/
theorem actual_birth_currentTag_fast_lintegral_restrict (a : Aux)
    (Phi : O × (SlowSet p × Fin p.K) → ℝ≥0∞) (hPhi : Measurable Phi) :
    (∫⁻ z, (Sum.elim (fun _ => none) some (tag q (z.val, a))).elim 0
      (fun e => if e.before.overflow = false then
        Phi (obs q.castSucc (z.val, a), (e.slowSet, e.fastArm)) else 0)
      ∂(mu0).restrict {z | pre q.succ z.val}) =
    ∫⁻ z, (Sum.elim (fun _ => none) some (tag q (z.val, a))).elim 0
      (fun e => if e.before.overflow = false then
        ∑ j : CanonicalFastSampling.FastArm e.slowSet,
          Phi (obs q.castSucc (z.val, a), (e.slowSet, j.val)) *
            kappa (RecordedQueueRun.scoreWeight Q e.before) (fun _ => zero_lt_one)
              (RecordedSlowRefresh.scoreWeight_pos Q e.before) e.slowSet j
        else 0)
      ∂(mu0).restrict {z | pre q.succ z.val} := by
  let Psi : O × (SlowSet p × Fin p.K) → ℝ≥0∞ := fun v =>
    if pre q.succ v.1.1 then Phi v else 0
  have hPsi : Measurable Psi := hPhi.ite
    ((measurableSet_noCallBefore rate rewards C_star C_h control0 q.succ).preimage
      (measurable_fst.comp measurable_fst)) measurable_const
  have h := actual_birth_currentTag_fast_lintegral rate rewards C_star C_h control0 row q a Psi hPsi
  have hS : MeasurableSet {z : Z0 | pre q.succ z.val} :=
    (measurableSet_noCallBefore rate rewards C_star C_h control0 q.succ).preimage measurable_subtype_coe
  rw [← lintegral_indicator hS, ← lintegral_indicator hS]
  convert h using 1 <;> apply lintegral_congr <;> intro z
  · have hp : pre q.succ (obs q.castSucc (z.val, a)).1 ↔ pre q.succ z.val :=
      (noCallThrough_sourcePrefix rate rewards C_star C_h control0 q z.val).symm
    obtain ⟨e, ht, _, _, _⟩ := actual_birth_tag_fields rate rewards C_star C_h control0 row q z a
    by_cases hc : pre q.succ z.val <;> by_cases hb : e.before.overflow = false <;>
      simp only [Set.indicator, Set.mem_ofPred_eq, Psi, hp, ht, Sum.elim_inr,
        Option.elim_some, hc, hb, ite_true, ite_false, ite_self, Bool.true_eq_false]
  · have hp : pre q.succ (obs q.castSucc (z.val, a)).1 ↔ pre q.succ z.val :=
      (noCallThrough_sourcePrefix rate rewards C_star C_h control0 q z.val).symm
    obtain ⟨e, ht, _, _, _⟩ := actual_birth_tag_fields rate rewards C_star C_h control0 row q z a
    by_cases hc : pre q.succ z.val <;> by_cases hb : e.before.overflow = false <;>
      simp only [Set.indicator, Set.mem_ofPred_eq, Psi, hp, ht, Sum.elim_inr,
        Option.elim_some, hc, hb, ite_true, ite_false, zero_mul, Finset.sum_const_zero,
        ite_self, Bool.true_eq_false]

end BirthSource

/-- Evaluation on the original physical source law, retaining an arbitrary
original auxiliary array. All source phases are integrated with their
inherited masses, including absent and already-exited paths. -/
theorem originalSource_fast_lintegral (q : Fin p.T) (a : Aux)
    (Phi : O × (SlowSet p × Fin p.K) → ℝ≥0∞) (hPhi : Measurable Phi) :
    (∫⁻ z : BootstrapPrivateRoundStreams.SourceInput p,
      Sum.elim (fun _ => 0) (fun e => if e.before.overflow = false then
        Phi (obs q.castSucc (z, a), (e.slowSet, e.fastArm)) else 0) (tag q (z, a))
      ∂BootstrapPrivateRoundStreams.sourceInputLaw p) =
    ∫⁻ z : BootstrapPrivateRoundStreams.SourceInput p,
      Sum.elim (fun _ => 0) (fun e => if e.before.overflow = false then
        ∑ j : CanonicalFastSampling.FastArm e.slowSet,
          Phi (obs q.castSucc (z, a), (e.slowSet, j.val)) *
            kappa (RecordedQueueRun.scoreWeight Q e.before) (fun _ => zero_lt_one)
              (RecordedSlowRefresh.scoreWeight_pos Q e.before) e.slowSet j else 0) (tag q (z, a))
      ∂BootstrapPrivateRoundStreams.sourceInputLaw p := by
  let F : O × LogicalCell p rate → ℝ≥0∞ := fun v => Phi (v.1, (v.2.slowSet, v.2.fastArm))
  let G : O × LogicalCell p rate → ℝ≥0∞ := fun v =>
    ∑ j : CanonicalFastSampling.FastArm v.2.slowSet,
      Phi (v.1, (v.2.slowSet, j.val)) *
        kappa (RecordedQueueRun.scoreWeight Q v.2.before) (fun _ => zero_lt_one)
          (RecordedSlowRefresh.scoreWeight_pos Q v.2.before) v.2.slowSet j
  let f := fun z : BootstrapPrivateRoundStreams.SourceInput p =>
    Sum.elim (fun _ => 0) (fun e => if e.before.overflow = false then
      F (obs q.castSucc (z, a), e) else 0) (tag q (z, a))
  let g := fun z : BootstrapPrivateRoundStreams.SourceInput p =>
    Sum.elim (fun _ => 0) (fun e => if e.before.overflow = false then
      G (obs q.castSucc (z, a), e) else 0) (tag q (z, a))
  have hF : Measurable F := hPhi.comp (measurable_fst.prodMk
    (((measurable_logicalCell_slowSet.mono le_rfl le_top).comp measurable_snd).prodMk
      (measurable_logicalCell_fastArm.comp measurable_snd)))
  have hf : Measurable f := (measurable_originalSource_test rate rewards C_star C_h control0 q F hF).comp
    (measurable_id.prodMk measurable_const)
  have hg : Measurable g := (measurable_originalSource_test rate rewards C_star C_h control0 q G
    (measurable_fastAverage rate Phi hPhi)).comp (measurable_id.prodMk measurable_const)
  have hzero (i : Fin 6) (hi : i = 0 ∨ i = 1 ∨ i = 5) :
      (∫⁻ z, f z ∂(BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
        (ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h q i)) =
      ∫⁻ z, g z ∂(BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
        (ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h q i) := by
    apply setLIntegral_congr_fun
      (ReferenceFirstLiveSourcePhasePartition.measurableSet_sourcePhase rate rewards C_star C_h q control0 i)
    intro z hz
    have hn : currentCellGate rate rewards C_star C_h q z ≠ true := by
      intro hc
      obtain ⟨hs, hk⟩ := (currentCellGate_iff rate rewards C_star C_h q z).mp hc
      rcases hi with rfl | rfl | rfl
      · have hw := (ReferenceFirstLiveOverflowReadout.wholeFirstLive_no_launch
          rate rewards C_star C_h z hz).1
        rw [hw, List.length_nil] at hk
        exact Nat.not_lt_zero _ hk
      · exact Nat.not_le_of_gt hz.2 hs
      · exact Nat.not_lt_of_ge hz.2.2 hk
    dsimp only [f, g]
    rw [currentCellTag_absent rate rewards C_star C_h q z hn a]
    rfl
  have hbirth (row : Fin (ConstructorDimensions.M p)) :
      (∫⁻ z, f z ∂(ReferenceTotalSourceDisintegration.sourceStratumMeasure rate rewards C_star C_h q
        (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex row q)).map Subtype.val) =
      ∫⁻ z, g z ∂(ReferenceTotalSourceDisintegration.sourceStratumMeasure rate rewards C_star C_h q
        (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex row q)).map Subtype.val := by
    rw [lintegral_map hf measurable_subtype_coe, lintegral_map hg measurable_subtype_coe]
    have h := actual_birth_currentTag_fast_lintegral rate rewards C_star C_h control0 row q a Phi hPhi
    convert h using 1 <;> apply lintegral_congr <;> intro z <;>
      dsimp only [f, g, F, G] <;> cases tag q (z.val, a) <;> rfl
  have hpositive (row : Fin (ConstructorDimensions.M p)) (v : Fin (q.val + 1)) :
      let s := v.val
      let hs := Nat.lt_succ_iff.mp v.isLt
      let m := (ReferenceFirstLiveRecordingSourceCylinder.branchSourceMeasure rate rewards C_star C_h row q s hs control0).map
        (ReferenceFirstLiveBranchIntegralTransport.forgetBranch rate rewards C_star C_h row q s hs control0) +
        (ReferenceFirstLiveEmptyPendingMarkerLaw.muEmpty rate rewards C_star C_h row q s hs control0).map
          (ReferenceFirstLiveSourcePhasePartition.forgetEmpty rate rewards C_star C_h row q s hs control0)
      (∫⁻ z, f z ∂m) = ∫⁻ z, g z ∂m := by
    intro s hs m
    let src := fun z : ReferenceFirstLiveChronologicalProposalLaw.TaggedSource rate rewards C_star C_h row q s hs control0 =>
      (Sum.elim Subtype.val Subtype.val z).val
    have hsrc : Measurable src := measurable_subtype_coe.comp
      (measurable_subtype_coe.sumElim measurable_subtype_coe)
    have hm : m = ((ReferenceFirstLiveRecordingSourceCylinder.branchSourceMeasure
          rate rewards C_star C_h row q s hs control0).map Sum.inl +
        (ReferenceFirstLiveEmptyPendingMarkerLaw.muEmpty rate rewards C_star C_h row q s hs control0).map Sum.inr).map src := by
      rw [Measure.map_add _ _ hsrc, Measure.map_map hsrc measurable_inl, Measure.map_map hsrc measurable_inr]
      rfl
    rw [hm, lintegral_map hf hsrc, lintegral_map hg hsrc]
    have h := actual_positive_currentTag_fast_lintegral rate rewards C_star C_h control0 row q s hs a Phi hPhi
    convert h using 1 <;> apply lintegral_congr <;> intro z <;>
      dsimp only [f, g, src] <;>
      rw [currentCellTag_original_positive rate rewards C_star C_h control0 row q s hs z a] <;> rfl
  change (∫⁻ z, f z ∂BootstrapPrivateRoundStreams.sourceInputLaw p) =
    ∫⁻ z, g z ∂BootstrapPrivateRoundStreams.sourceInputLaw p
  rw [ReferenceFirstLiveCalendarIntegralAssembly.original_source_measure_decomposition
    rate rewards C_star C_h q control0]
  simp only [lintegral_add_measure, lintegral_finsetSum_measure]
  dsimp only at hpositive
  simp only [lintegral_add_measure] at hpositive
  simp only [hzero 0 (Or.inl rfl), hzero 1 (Or.inr (Or.inl rfl)),
    hzero 5 (Or.inr (Or.inr rfl)), hbirth, hpositive]

/-- The actual first-LIVE FAST joint-test law on the original killed observer
measure, for the raw law and every original fixed-ID section. Birth and both
positive-offset branches retain the same incoming slow set and full PRE. -/
theorem prefix_live_fast_lintegral
    (ids : Option (CompletePublicTable.IDArray p)) (q : Fin p.T)
    (Phi : O × (SlowSet p × Fin p.K) → ℝ≥0∞) (hPhi : Measurable Phi) :
    (∫⁻ v, if noCall q v.1.1 then
      (Sum.elim (fun _ => none) some (tag q (extensionInput rate q v).1)).elim 0
        (fun e => if e.before.overflow = false then Phi (v.1, (e.slowSet, e.fastArm)) else 0)
      else 0 ∂(beta ids q).prod (calendarInnovationLaw p)) =
    ∫⁻ v, if noCall q v.1.1 then
      (Sum.elim (fun _ => none) some (tag q (extensionInput rate q v).1)).elim 0
        (fun e => if e.before.overflow = false then
          ∑ j : CanonicalFastSampling.FastArm e.slowSet,
            Phi (v.1, (e.slowSet, j.val)) *
              kappa (RecordedQueueRun.scoreWeight Q e.before) (fun _ => zero_lt_one)
                (RecordedSlowRefresh.scoreWeight_pos Q e.before) e.slowSet j else 0)
      else 0 ∂(beta ids q).prod (calendarInnovationLaw p) := by
  rw [joint_test_originalSource rate rewards C_star C_h control0 ids q Phi hPhi,
    averaged_test_originalSource rate rewards C_star C_h control0 ids q Phi hPhi]
  let E : Set (BootstrapPrivateRoundStreams.SourceInput p) :=
    ids.elim Set.univ (ReferenceFixedIDSourceSection.fixedIDSourceSection (p := p))
  let c : ℝ≥0∞ := ids.elim 1 (fun id => (CompletePublicTable.idArrayMeasure p {id})⁻¹)
  have hE : MeasurableSet E := by
    cases ids with
    | none => exact MeasurableSet.univ
    | some id => exact ReferenceFixedIDSourceSection.measurable_fixedIDSourceSection id
  have hmu : mu ids = c • (enlargedSourceLaw p).restrict {za | za.1 ∈ E} := by
    cases ids with
    | none => simp only [E, c, Option.elim_none, Set.mem_univ, Set.ofPred_true, Measure.restrict_univ, one_smul]
    | some id =>
      have hfix : ReferenceFixedIDSourceSection.fixedIDSourceLaw id =
          (CompletePublicTable.idArrayMeasure p {id})⁻¹ •
            (BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
              (ReferenceFixedIDSourceSection.fixedIDSourceSection id) := by
        rw [ReferenceFixedIDSourceSection.sourceInputLaw_restrict_fixedIDSourceSection,
          smul_smul, ENNReal.inv_mul_cancel
            (ENNReal.toReal_pos_iff.mp (ReferenceFixedIDSourceSection.idArrayAtom_positive (p := p) id)).1.ne'
            (ReferenceFixedIDSourceSection.idArrayAtom_lt_top (p := p) id).ne, one_smul]
      change (ReferenceFixedIDSourceSection.fixedIDSourceLaw id).prod _ = _
      rw [hfix, Measure.prod_smul_left, Measure.restrict_prod_eq_prod_univ, Set.prod_univ]
      rfl
  let S : Set (BootstrapPrivateRoundStreams.SourceInput p × Aux) := {za | pre q.succ za.1 ∧ za.1 ∈ E}
  have hP : MeasurableSet {za : BootstrapPrivateRoundStreams.SourceInput p × Aux | pre q.succ za.1} :=
    (measurableSet_noCallBefore rate rewards C_star C_h control0 q.succ).preimage measurable_fst
  have hS : MeasurableSet S := hP.inter (hE.preimage measurable_fst)
  let Psi : O × (SlowSet p × Fin p.K) → ℝ≥0∞ := fun v =>
    if pre q.succ v.1.1 ∧ v.1.1 ∈ E then Phi v else 0
  have hPsi : Measurable Psi := hPhi.ite
    (((measurableSet_noCallBefore rate rewards C_star C_h control0 q.succ).inter hE).preimage
      (measurable_fst.comp measurable_fst)) measurable_const
  let F : O × LogicalCell p rate → ℝ≥0∞ := fun v => Phi (v.1, (v.2.slowSet, v.2.fastArm))
  let G : O × LogicalCell p rate → ℝ≥0∞ := fun v =>
    ∑ j : CanonicalFastSampling.FastArm v.2.slowSet,
      Phi (v.1, (v.2.slowSet, j.val)) *
        kappa (RecordedQueueRun.scoreWeight Q v.2.before) (fun _ => zero_lt_one)
          (RecordedSlowRefresh.scoreWeight_pos Q v.2.before) v.2.slowSet j
  let f := fun za : BootstrapPrivateRoundStreams.SourceInput p × Aux =>
    Sum.elim (fun _ => 0) (fun e => if e.before.overflow = false then F (obs q.castSucc za, e) else 0) (tag q za)
  let g := fun za : BootstrapPrivateRoundStreams.SourceInput p × Aux =>
    Sum.elim (fun _ => 0) (fun e => if e.before.overflow = false then G (obs q.castSucc za, e) else 0) (tag q za)
  have hF : Measurable F := hPhi.comp (measurable_fst.prodMk
    (((measurable_logicalCell_slowSet.mono le_rfl le_top).comp measurable_snd).prodMk
      (measurable_logicalCell_fastArm.comp measurable_snd)))
  have hf : Measurable f := measurable_originalSource_test rate rewards C_star C_h control0 q F hF
  have hg : Measurable g := measurable_originalSource_test rate rewards C_star C_h control0 q G
    (measurable_fastAverage rate Phi hPhi)
  have hgate (z : BootstrapPrivateRoundStreams.SourceInput p) :
      (pre q.succ (sourcePrefix control0 q.val z) ∧ sourcePrefix control0 q.val z ∈ E) ↔
        (pre q.succ z ∧ z ∈ E) := by
    rw [← noCallThrough_sourcePrefix rate rewards C_star C_h control0 q z]
    cases ids <;> rfl
  have hraw : (∫⁻ za, f za ∂(enlargedSourceLaw p).restrict S) =
      ∫⁻ za, g za ∂(enlargedSourceLaw p).restrict S := by
    rw [← lintegral_indicator hS, ← lintegral_indicator hS]
    change (∫⁻ za, S.indicator f za ∂(BootstrapPrivateRoundStreams.sourceInputLaw p).prod
        (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p)) =
      ∫⁻ za, S.indicator g za ∂(BootstrapPrivateRoundStreams.sourceInputLaw p).prod
        (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p)
    rw [lintegral_prod_symm _ (hf.indicator hS).aemeasurable,
      lintegral_prod_symm _ (hg.indicator hS).aemeasurable]
    apply lintegral_congr
    intro a
    have h := originalSource_fast_lintegral rate rewards C_star C_h control0 q a Psi hPsi
    convert h using 1 <;> apply lintegral_congr <;> intro z <;>
      dsimp only [f, g, F, G] <;>
      cases ht : tag q (z, a) with
      | inl u => simp only [Set.indicator, S, ht, Sum.elim_inl, ite_self]
      | inr e =>
        by_cases hs : pre q.succ z ∧ z ∈ E <;> by_cases hc : e.before.overflow = false <;>
          simp only [Set.indicator, S, Set.mem_ofPred_eq, ht, Sum.elim_inr, Psi,
            show (obs q.castSucc (z, a)).1 = sourcePrefix control0 q.val z from rfl,
            hgate z, hs, hc, and_self, ite_self, ite_true, ite_false, Bool.true_eq_false, zero_mul, Finset.sum_const_zero]
  have htarget : (∫⁻ za, f za ∂(mu ids).restrict {za | pre q.succ za.1}) =
      ∫⁻ za, g za ∂(mu ids).restrict {za | pre q.succ za.1} := by
    rw [hmu, Measure.restrict_smul, Measure.restrict_restrict hP,
      lintegral_smul_measure, lintegral_smul_measure]
    exact congrArg (c * ·) hraw
  convert htarget using 1 <;> apply lintegral_congr <;> intro za <;>
    dsimp only [f, g, F, G] <;> cases tag q za <;> rfl

end Bandits.Support.ReferenceGeneratedCalendarPrefixLiveFast
