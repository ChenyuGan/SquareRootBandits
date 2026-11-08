/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedCalendarOverflowTail
public import Bandits.Support.ReferenceOriginalCalendarFixedIDLearningMean

import Mathlib.Tactic

/-!
# Retained current-marginal reward on the actual terminal archive

The numerical observable below reads the incoming queue state of every
PRE-clear archived cell. It is distinct from the logical slow/FAST payoff.
The original full numerical prefix identifies both its weights and its gate;
unique enabled-date coverage supplies the converse calendar join.

Sources: ZIP4 `04_slow_fast_learner.tex:176-215,323-393`,
`06_interruptions.tex:391-426`, and `08_main_theorem.tex:78-109`.
These are internal numerical identities and estimates, not a slow-set law,
logical reward comparison, or source-facing regret closure.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped Classical BigOperators
open Bandits.Support ConstructorDimensions
open ReferenceFirstLiveChronologicalPrefixFoundation (LogicalCell)
open ReferenceExhaustiveGeneratedCalendarSourceLaw
  (Omega terminalSource terminalReadout terminalLaw fixedIDTerminalLaw nominalEnabled)
open ReferenceFirstCollectionCorrectedSliceNumericalPrefix (prefixInputs prefixReadout)
open ReferenceFirstCollectionRenewalIncomingQueueMeasurability (stateReadout)
open ReferenceOriginalCalendarCarriedStoppedEnergy (actualCellAt activeUpdateAt)
open ReferenceOriginalCalendarLiveCollectionWeightedDrift (thetaAt)
open ReferenceOriginalCalendarFixedIDNonfirstLearning (retainedRewardGap roundedRewardAt)
open ReferenceOriginalCalendarFixedIDLearningMean (retainedRoundedLearningSum)

namespace Bandits.Support.ReferenceGeneratedCalendarRetainedMarginalBridge

variable {p : Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
  (control0 : ContinuousLearningRows.TimeControl p)

local notation "Q" => ReferenceFirstLaunchNumericalCell.queueParameters rate
local notation "start " z:max => ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
local notation "word" => ReferenceActualCollectionHiddenRefreshPath.actualOriginalWord rate rewards C_star C_h

local instance sourceMeasurableSpace : MeasurableSpace (BootstrapPrivateRoundStreams.SourceInput p) := by
  change MeasurableSpace (CompletePublicTable.PublishedOutput p ×
    BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

/-- Comparator minus the current product-set inclusion-marginal reward,
read literally from this cell's incoming numerical state. -/
def cellMarginalGap (S : ProductSetLaw.ProductSet p.K p.m)
    (e : LogicalCell p rate) : ℝ :=
  (∑ i ∈ S.val, ((rewards e.time i).val : ℝ) / (D p : ℝ)) -
    ∑ i : Fin p.K,
      ProductSetLaw.theta p.m (RecordedQueueRun.scoreWeight Q e.before) i *
        ((rewards e.time i).val : ℝ) / (D p : ℝ)

/-- Literal PRE-clear numerical marginal sum on the full terminal archive.
The first detecting UPDATE has incoming flag false and is retained. -/
def retainedMarginalGap (S : ProductSetLaw.ProductSet p.K p.m)
    (w : Omega rate rewards C_star C_h) : ℝ :=
  (((terminalReadout rate rewards C_star C_h control0 w).2.2.filter
    (fun e => e.before.overflow = false)).map (cellMarginalGap rate rewards S)).sum

/-- At every actual date after launch, the strict original prefix is the
matching prefix of the same unique whole original numerical word. -/
private theorem originalPrefix_atDate
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hl : ∃ active, ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate z rewards C_star C_h = some active)
    (q : Fin p.T) (hsq : start z ≤ q.val) :
    prefixInputs rate rewards C_star C_h q.val z =
      some ((word z hl).take (q.val - start z)) := by
  have hn : q.val - start z ≤
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).length := by
    rw [ReferenceCompletePhysicalHistory.completeSuffixRecords_length]
    have := q.isLt
    omega
  have h := ReferenceActualCollectionHiddenRefreshPath.actualOriginalWord_prefix
    rate rewards C_star C_h z hl (q.val - start z) hn
  rwa [Nat.add_sub_of_le hsq] at h

/-- The actual archived PRE state, current marginal, and numerical input
agree with the original full-prefix observations. This holds under the raw
terminal law and under every original fixed-ID terminal law. -/
theorem ae_terminal_cell_alignment (ids : Option (CompletePublicTable.IDArray p)) :
    ∀ᵐ w ∂ids.elim (terminalLaw rate rewards C_star C_h control0)
      (fixedIDTerminalLaw rate rewards C_star C_h control0),
      let z := terminalSource rate rewards C_star C_h control0 w
      ∀ e ∈ (terminalReadout rate rewards C_star C_h control0 w).2.2,
        (∃ past, prefixInputs rate rewards C_star C_h e.time.val z = some past ∧
          e.before = RecordedQueueRun.run Q past) ∧
        prefixReadout rate rewards C_star C_h e.time.val z = some (stateReadout e.before) ∧
        (∀ i, thetaAt rate rewards C_star C_h e.time.val i z =
          ProductSetLaw.theta p.m (RecordedQueueRun.scoreWeight Q e.before) i) ∧
        (∃ c, actualCellAt rate rewards C_star C_h e.time z = some c ∧ c.enabled = true ∧
          e.numerical = ReferenceLaterCollectionSourceReadoutMeasurability.numericalCoordinates c) ∧
        (activeUpdateAt rate rewards C_star C_h e.time z ↔ e.before.overflow = false) := by
  filter_upwards [ReferenceExhaustiveGeneratedCalendarSourceLaw.ae_terminal_marked_path
    rate rewards C_star C_h control0 ids] with w hw
  dsimp only
  intro e he
  rcases hw.2.2 with hnone | ⟨hl, hpath⟩
  · rw [hnone.2] at he
    exact (List.not_mem_nil he).elim
  · obtain ⟨⟨r, hr, _hphysical⟩, hb, _ha, hi, hen, hnum, _harr, _hservice, _hall, _hfrozen⟩ :=
      hpath e he
    let z := terminalSource rate rewards C_star C_h control0 w
    have hs : start z ≤ e.time.val := by
      by_contra hs
      have hrnone := ReferenceSourcePrefixHistoryFiltration.actualRecord_eq_none_of_future_start
        rate rewards C_star C_h e.time z (Nat.lt_of_not_ge hs)
      rw [hrnone] at hr
      cases hr
    have hp := originalPrefix_atDate rate rewards C_star C_h z hl e.time hs
    obtain ⟨_hi, hc⟩ := ReferenceGeneratedCalendarMarkedPath.originalWord_inputAt
      rate rewards C_star C_h z hl e.time hs
    change actualCellAt rate rewards C_star C_h e.time z =
      some (word z hl)[e.time.val - start z] at hc
    have hread : prefixReadout rate rewards C_star C_h e.time.val z =
        some (stateReadout e.before) := by
      unfold prefixReadout
      rw [hp, Option.map_some, ← hb]
    refine ⟨⟨_, hp, hb⟩, hread, ?_, ⟨_, hc, hen, hnum⟩, ?_⟩
    · intro i
      unfold thetaAt
      rw [hp, Option.elim_some, ← hb]
    · constructor
      · rintro ⟨o, c, ho, _hc, hclear, _hen⟩
        have hoeq := Option.some.inj (ho.symm.trans hread)
        rw [hoeq] at hclear
        exact hclear
      · intro hclear
        exact ⟨_, _, hread, hc, hclear, hen⟩

/-- Two-way retained coverage: every original active update has its unique
actual archived cell with a clear incoming flag, and every such cell is an
original active update. No decoder or tail-event gate is used. -/
theorem ae_terminal_retained_unique_iff (ids : Option (CompletePublicTable.IDArray p)) :
    ∀ᵐ w ∂ids.elim (terminalLaw rate rewards C_star C_h control0)
      (fixedIDTerminalLaw rate rewards C_star C_h control0),
      ∀ q : Fin p.T,
        (∃! e : LogicalCell p rate,
          e ∈ (terminalReadout rate rewards C_star C_h control0 w).2.2 ∧
            e.time = q ∧ e.before.overflow = false) ↔
        activeUpdateAt rate rewards C_star C_h q
          (terminalSource rate rewards C_star C_h control0 w) := by
  filter_upwards [ae_terminal_cell_alignment rate rewards C_star C_h control0 ids] with w hw
  intro q
  constructor
  · rintro ⟨e, ⟨he, ht, hc⟩, _hu⟩
    have ha := (hw e he).2.2.2.2.mpr hc
    rwa [ht] at ha
  · intro ha
    have hn : nominalEnabled rate rewards C_star C_h q
        (terminalSource rate rewards C_star C_h control0 w) = true := by
      obtain ⟨o, c, _ho, hc, _hclear, hen⟩ := ha
      change (actualCellAt rate rewards C_star C_h q
        (terminalSource rate rewards C_star C_h control0 w)).any RecordedQueueRun.RoundInput.enabled = true
      rw [hc, Option.any_some, hen]
    obtain ⟨e, ⟨he, ht⟩, hu⟩ :=
      (ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalReadout_unique_enabled
        rate rewards C_star C_h control0 w q).mpr hn
    have hc := (hw e he).2.2.2.2.mp (ht ▸ ha)
    exact ⟨e, ⟨he, ht, hc⟩, fun f hf => hu f ⟨hf.1, hf.2.1⟩⟩

/-- The literal archive sum is exactly the already accepted original-calendar
rounded-learning sum. The proof uses both directions of retained-date coverage,
including dates with zero recorded arrivals and the first overflow update. -/
theorem ae_retainedMarginalGap_eq_retainedRoundedLearningSum
    (ids : Option (CompletePublicTable.IDArray p)) (S : ProductSetLaw.ProductSet p.K p.m) :
    ∀ᵐ w ∂ids.elim (terminalLaw rate rewards C_star C_h control0)
      (fixedIDTerminalLaw rate rewards C_star C_h control0),
      retainedMarginalGap rate rewards C_star C_h control0 S w =
        retainedRoundedLearningSum rate rewards C_star C_h S
          (terminalSource rate rewards C_star C_h control0 w) := by
  filter_upwards [ae_terminal_cell_alignment rate rewards C_star C_h control0 ids,
    ae_terminal_retained_unique_iff rate rewards C_star C_h control0 ids] with w hcell hcoverage
  let z := terminalSource rate rewards C_star C_h control0 w
  let H := (terminalReadout rate rewards C_star C_h control0 w).2.2
  let L := H.filter (fun e => e.before.overflow = false)
  let dates := L.map LogicalCell.time
  let g := fun q : Fin p.T => retainedRewardGap rate rewards C_star C_h S q z
  have hn : dates.Nodup := by
    rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
    exact ((ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalReadout_chronology
      rate rewards C_star C_h control0 w).filter _).imp
        (fun h => Fin.ne_of_val_ne (Nat.ne_of_lt h))
  have hvalues : ∀ e ∈ L, cellMarginalGap rate rewards S e = g e.time := by
    intro e he
    obtain ⟨hem, hclear⟩ := List.mem_filter.mp he
    have hc := hcell e hem
    have ha := hc.2.2.2.2.mpr (of_decide_eq_true hclear)
    have hmem : z ∈ {z | activeUpdateAt rate rewards C_star C_h e.time z} := ha
    dsimp only [g, retainedRewardGap]
    rw [Set.indicator_of_mem hmem]
    unfold cellMarginalGap roundedRewardAt ReferenceFirstCollectionOldRecorderFoundation.roundedReward
    simp only [z, hc.2.2.1, mul_div_assoc]
  have hm : L.map (cellMarginalGap rate rewards S) = dates.map g := by
    rw [List.map_map]
    exact List.map_congr_left hvalues
  change (L.map (cellMarginalGap rate rewards S)).sum = ∑ q : Fin p.T, g q
  rw [hm, ← List.sum_toFinset g hn]
  apply Finset.sum_subset (Finset.subset_univ dates.toFinset)
  intro q _hq hq
  have hnot : ¬ activeUpdateAt rate rewards C_star C_h q z := by
    intro ha
    obtain ⟨e, ⟨he, ht, hclear⟩, _hu⟩ := (hcoverage q).mpr ha
    apply hq
    apply List.mem_toFinset.mpr
    apply List.mem_map.mpr
    refine ⟨e, List.mem_filter.mpr ⟨he, ?_⟩, ht⟩
    simp only [hclear, decide_true]
  have hmem : z ∉ {z | activeUpdateAt rate rewards C_star C_h q z} := hnot
  exact Set.indicator_of_notMem hmem _

private instance sumMeasurableSingleton {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSingletonClass A] [MeasurableSingletonClass B] : MeasurableSingletonClass (A ⊕ B) where
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

private theorem measurable_archiveMarginalGap (S : ProductSetLaw.ProductSet p.K p.m) :
    Measurable (fun H : List (LogicalCell p rate) =>
      ((H.filter (fun e => e.before.overflow = false)).map (cellMarginalGap rate rewards S)).sum) := by
  let mark : LogicalCell p rate → Fin p.T × RecordedQueueRun.RunState p.K :=
    fun e => (e.time, e.before)
  have hm : Measurable mark :=
    ReferenceFirstLiveChronologicalPrefixMeasurability.measurable_logicalCell_time.prodMk
      ReferenceFirstLiveChronologicalPrefixMeasurability.measurable_logicalCell_before
  let F : List (Fin p.T × RecordedQueueRun.RunState p.K) → ℝ := fun L =>
    ((L.filter (fun e => e.2.overflow = false)).map (fun e =>
      (∑ i ∈ S.val, ((rewards e.1 i).val : ℝ) / (D p : ℝ)) -
        ∑ i : Fin p.K, ProductSetLaw.theta p.m (RecordedQueueRun.scoreWeight Q e.2) i *
          ((rewards e.1 i).val : ℝ) / (D p : ℝ))).sum
  have hF : Measurable F := measurable_of_countable F
  convert hF.comp (ReferenceActiveHorizonMeasurability.measurable_list_map id measurable_id mark hm) using 1
  funext H
  simp only [Function.comp_apply, id_eq, F, List.filter_map, List.map_map,
    Function.comp_def, mark]
  rfl

/-- Only the date and countable integer queue state are used as discrete
marks. All continuous source and cell coordinates retain their Borel spaces. -/
theorem measurable_retainedMarginalGap (S : ProductSetLaw.ProductSet p.K p.m) :
    Measurable (retainedMarginalGap rate rewards C_star C_h control0 S) :=
  (measurable_archiveMarginalGap rate rewards S).comp
    (ReferenceExhaustiveGeneratedCalendarSourceLaw.measurable_terminalReadout
      rate rewards C_star C_h control0).snd.snd

private theorem cellMarginalGap_abs_le (S : ProductSetLaw.ProductSet p.K p.m)
    (e : LogicalCell p rate) : |cellMarginalGap rate rewards S e| ≤ p.m := by
  let r := fun i : Fin p.K => ((rewards e.time i).val : ℝ) / (D p : ℝ)
  let theta := ProductSetLaw.theta p.m (RecordedQueueRun.scoreWeight Q e.before)
  have hr i : 0 ≤ r i ∧ r i ≤ 1 :=
    ReferenceFirstCollectionOldRecorderFoundation.roundedReward_bounds rewards e.time i
  have ht i : 0 ≤ theta i :=
    (RecordedMarginalGrowth.state_theta_pos Q e.before i (by have := p.two_le_m; omega) p.m_lt_K).le
  have hc : 0 ≤ ∑ i ∈ S.val, r i ∧ (∑ i ∈ S.val, r i) ≤ p.m := by
    refine ⟨Finset.sum_nonneg (fun i _ => (hr i).1), ?_⟩
    have h := Finset.sum_le_sum (fun i (_hi : i ∈ S.val) => (hr i).2)
    simpa only [Finset.sum_const, nsmul_eq_mul, mul_one,
      (Finset.mem_powersetCard.mp S.property).2] using h
  have hw : 0 ≤ ∑ i : Fin p.K, theta i * r i ∧
      (∑ i : Fin p.K, theta i * r i) ≤ p.m := by
    refine ⟨Finset.sum_nonneg (fun i _ => mul_nonneg (ht i) (hr i).1), ?_⟩
    calc
      _ ≤ ∑ i : Fin p.K, theta i := Finset.sum_le_sum
        (fun i _ => mul_le_of_le_one_right (ht i) (hr i).2)
      _ = _ := RecordedMarginalGrowth.state_sum_theta_eq_m Q e.before
        (by have := p.two_le_m; omega) p.m_lt_K
  unfold cellMarginalGap
  simp_rw [mul_div_assoc]
  exact abs_le.mpr ⟨by linarith only [hc.1, hw.2], by linarith only [hc.2, hw.1]⟩

private theorem archiveMarginalGap_abs_le_length (S : ProductSetLaw.ProductSet p.K p.m)
    (H : List (LogicalCell p rate)) :
    |(H.map (cellMarginalGap rate rewards S)).sum| ≤ (p.m : ℝ) * H.length := by
  induction H with
  | nil => simp only [List.map_nil, List.sum_nil, abs_zero, List.length_nil, Nat.cast_zero, mul_zero, le_refl]
  | cons e H ih =>
    simp only [List.map_cons, List.sum_cons]
    calc
      _ ≤ _ := abs_add_le _ _
      _ ≤ (p.m : ℝ) + (p.m : ℝ) * H.length :=
        add_le_add (cellMarginalGap_abs_le rate rewards S e) ih
      _ = _ := by simp only [List.length_cons, Nat.cast_add, Nat.cast_one]; ring

/-- A uniform numerical bound on the actual archive, including every
exceptional component, with no assumed payoff bound. -/
theorem retainedMarginalGap_abs_le (S : ProductSetLaw.ProductSet p.K p.m)
    (w : Omega rate rewards C_star C_h) :
    |retainedMarginalGap rate rewards C_star C_h control0 S w| ≤ (p.m : ℝ) * p.T := by
  have hn : ((terminalReadout rate rewards C_star C_h control0 w).2.2.map LogicalCell.time).Nodup := by
    rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
    exact (ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalReadout_chronology
      rate rewards C_star C_h control0 w).imp (fun h => Fin.ne_of_val_ne (Nat.ne_of_lt h))
  have hlen : (terminalReadout rate rewards C_star C_h control0 w).2.2.length ≤ p.T := by
    simpa only [List.length_map, Fintype.card_fin] using hn.length_le_card
  apply (archiveMarginalGap_abs_le_length rate rewards S _).trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  exact Nat.cast_le.mpr ((List.length_filter_le _ _).trans hlen)

/-- Integrability on the raw law and every original fixed-ID law. -/
theorem integrable_retainedMarginalGap (ids : Option (CompletePublicTable.IDArray p))
    (S : ProductSetLaw.ProductSet p.K p.m) :
    Integrable (retainedMarginalGap rate rewards C_star C_h control0 S)
      (ids.elim (terminalLaw rate rewards C_star C_h control0)
        (fixedIDTerminalLaw rate rewards C_star C_h control0)) := by
  cases ids <;> dsimp only [Option.elim] <;>
    apply Integrable.of_bound
      (measurable_retainedMarginalGap rate rewards C_star C_h control0 S).aestronglyMeasurable
      ((p.m : ℝ) * p.T) <;>
    exact Filter.Eventually.of_forall fun w => by
      simpa only [Real.norm_eq_abs] using
        retainedMarginalGap_abs_le rate rewards C_star C_h control0 S w

/-- The exact integral transport uses the SAME original source and fixed ID
array, keeping the complete rows and private arrays of the accepted law. -/
theorem retainedMarginalGap_fixedID_integral
    (ids : CompletePublicTable.IDArray p) (S : ProductSetLaw.ProductSet p.K p.m) :
    (∫ w, retainedMarginalGap rate rewards C_star C_h control0 S w
      ∂fixedIDTerminalLaw rate rewards C_star C_h control0 ids) =
    ∫ z, retainedRoundedLearningSum rate rewards C_star C_h S z
      ∂ReferenceFixedIDSourceSection.fixedIDSourceLaw ids := by
  have heq := ae_retainedMarginalGap_eq_retainedRoundedLearningSum
    rate rewards C_star C_h control0 (some ids) S
  dsimp only [Option.elim] at heq
  rw [integral_congr_ae heq]
  have hi := (ReferenceOriginalCalendarFixedIDLearningMean.retainedRoundedLearningSum_fixedID_mean
    rate rewards C_star C_h control0 ids S).1
  have himap : Integrable (retainedRoundedLearningSum rate rewards C_star C_h S)
      ((fixedIDTerminalLaw rate rewards C_star C_h control0 ids).map
        (terminalSource rate rewards C_star C_h control0)) := by
    rw [ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDTerminalLaw_map_source]
    exact hi
  rw [← integral_map
    (ReferenceExhaustiveGeneratedCalendarSourceLaw.measurable_terminalSource
      rate rewards C_star C_h control0).aemeasurable himap.aestronglyMeasurable,
    ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDTerminalLaw_map_source]

/-- The accepted original numerical mean, transported to the actual terminal
archive for EVERY original ID array and fixed comparator. No logical slow-set
law or numerical estimate is an input. -/
theorem retainedMarginalGap_fixedID_mean
    (ids : CompletePublicTable.IDArray p) (S : ProductSetLaw.ProductSet p.K p.m) :
    Integrable (retainedMarginalGap rate rewards C_star C_h control0 S)
      (fixedIDTerminalLaw rate rewards C_star C_h control0 ids) ∧
    (∫ w, retainedMarginalGap rate rewards C_star C_h control0 S w
      ∂fixedIDTerminalLaw rate rewards C_star C_h control0 ids) ≤
      (2 * Real.log (Nat.choose p.K p.m : ℝ) + (p.m : ℝ) / 16) / rate.eta.val +
      (16 * (p.m : ℝ) ^ 2 + (16 / 11 : ℝ) * CanonicalRecordingRates.R p +
        32 * (p.m : ℝ)) * rate.eta.val * p.T +
      (p.m : ℝ) * p.T / (rate.eta.val * D p) := by
  refine ⟨integrable_retainedMarginalGap rate rewards C_star C_h control0 (some ids) S, ?_⟩
  rw [retainedMarginalGap_fixedID_integral]
  exact (ReferenceOriginalCalendarFixedIDLearningMean.retainedRoundedLearningSum_fixedID_mean
    rate rewards C_star C_h control0 ids S).2

end Bandits.Support.ReferenceGeneratedCalendarRetainedMarginalBridge

end
