/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceExhaustiveGeneratedCalendarSourceLaw
public import Bandits.Support.ReferenceOriginalCalendarFixedIDOverflowBound

import Mathlib.Tactic

/-!
# Overflow tail of the exhaustive generated signed auxiliary sum

The retained readout filters on the incoming flag, and therefore includes the
first detecting update. Both readouts use the full existing terminal archive.
The actual original numerical prefix identifies the tail event; the original
fixed-ID source bound then pays for its bounded signed continuation.

Sources: ZIP4 `04_slow_fast_learner.tex:176-215,323-390`,
`06_interruptions.tex:391-426`, and `08_main_theorem.tex:78-109`.
These are internal auxiliary bounds, not a retained-mean or main-regret bound.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped Classical BigOperators
open Bandits.Support ConstructorDimensions
open ReferenceFirstLiveChronologicalPrefixFoundation

namespace Bandits.Support.ReferenceGeneratedCalendarOverflowTail

variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
  (control0 : ContinuousLearningRows.TimeControl p)

local notation "Q" => ReferenceFirstLaunchNumericalCell.queueParameters rate
local notation "start " z:max => ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
local notation "word" => ReferenceActualCollectionHiddenRefreshPath.actualOriginalWord rate rewards C_star C_h
local notation "overflowEvent" => ReferenceOriginalNumericalFirstOverflowLocator.observedNumericalOverflowEvent rate rewards C_star C_h

local instance sourceMeasurableSpace : MeasurableSpace (ReferenceExhaustiveGeneratedCalendarSourceLaw.Source p) := by
  change MeasurableSpace (CompletePublicTable.PublishedOutput p ×
    BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

local instance slowSetMeasurableSpace : MeasurableSpace (SlowSet p) := ⊤
local instance slowSetDiscrete : DiscreteMeasurableSpace (SlowSet p) := ⟨fun _ => trivial⟩

/-- An overflowing prefix of the actual original word gives a present
normalized-backlog observation on the same original source. -/
theorem originalPrefix_overflow_mem_observedNumericalOverflowEvent
    (z : ReferenceExhaustiveGeneratedCalendarSourceLaw.Source p)
    (hl : ∃ active, ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate z rewards C_star C_h = some active)
    (n : ℕ) (hn : n ≤ (word z hl).length)
    (hov : (RecordedQueueRun.run Q ((word z hl).take n)).overflow = true) :
    z ∈ overflowEvent := by
  have hlen := ReferenceActualCollectionHiddenRefreshPath.actualOriginalWord_length
    rate rewards C_star C_h z hl
  have hnR : n ≤ (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length := by
    rwa [← hlen]
  have hp := ReferenceActualCollectionHiddenRefreshPath.actualOriginalWord_prefix
    rate rewards C_star C_h z hl n hnR
  have hs := ReferenceCompletePhysicalHistory.physicalStart_le_T rate z rewards C_star C_h
  have hR := ReferenceCompletePhysicalHistory.completeSuffixRecords_length
    rate z rewards C_star C_h
  have hdate : start z + n ≤ p.T := by omega
  obtain ⟨a, ha⟩ := (RecordedQueueRun.run_overflow_iff_cutoff Q _).mp hov
  refine ⟨start z + n, hdate,
    ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
      (RecordedQueueRun.run Q ((word z hl).take n)), ?_, a, ?_⟩
  · unfold ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout
    rw [hp]
    rfl
  · exact (RecordedQueueRun.overflowCutoff_iff Q _).mpr ha

/-- Every actual incoming-overflow cell forces the literal numerical detector.
The absent-launch branch has an empty archive. No reverse implication is used. -/
theorem ae_incomingOverflow_implies_observedNumericalOverflowEvent
    (ids : Option (CompletePublicTable.IDArray p)) :
    ∀ᵐ w ∂ids.elim (ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalLaw rate rewards C_star C_h control0)
      (ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDTerminalLaw rate rewards C_star C_h control0),
      ∀ e ∈ (ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalReadout rate rewards C_star C_h control0 w).2.2,
        e.before.overflow = true →
          ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalSource rate rewards C_star C_h control0 w ∈ overflowEvent := by
  filter_upwards [ReferenceExhaustiveGeneratedCalendarSourceLaw.ae_terminal_marked_path rate rewards C_star C_h control0 ids] with w hw
  intro e he hov
  rcases hw.2.2 with hnone | ⟨hl, hpath⟩
  · rw [hnone.2] at he
    exact False.elim (List.not_mem_nil he)
  · obtain ⟨_hphysical, hb, _ha, hi, _hen, _hnum, _harr, _hservice, _hall, _hfrozen⟩ := hpath e he
    apply originalPrefix_overflow_mem_observedNumericalOverflowEvent rate rewards C_star C_h
      (ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalSource rate rewards C_star C_h control0 w) hl
      (e.time.val - start (ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalSource rate rewards C_star C_h control0 w))
      (Nat.le_of_lt hi)
    rwa [← hb]

/-- Literal PRE-clear signed readout; the first detecting UPDATE is retained. -/
def retainedSignedGap (S : ProductSetLaw.ProductSet p.K p.m)
    (w : ReferenceExhaustiveGeneratedCalendarSourceLaw.Omega rate rewards C_star C_h) : ℝ :=
  ReferenceExhaustiveGeneratedCalendarSourceLaw.signedGap rate rewards S
    ((ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalReadout rate rewards C_star C_h control0 w).2.2.filter
      (fun e => e.before.overflow = false))

/-- Literal complementary signed continuation on every incoming-overflow date. -/
def overflowTailSignedGap (S : ProductSetLaw.ProductSet p.K p.m)
    (w : ReferenceExhaustiveGeneratedCalendarSourceLaw.Omega rate rewards C_star C_h) : ℝ :=
  ReferenceExhaustiveGeneratedCalendarSourceLaw.signedGap rate rewards S
    ((ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalReadout rate rewards C_star C_h control0 w).2.2.filter
      (fun e => e.before.overflow = true))

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

private theorem measurable_signedGap_filter (S : ProductSetLaw.ProductSet p.K p.m) (b : Bool) :
    Measurable (fun H : List (LogicalCell p rate) =>
      ReferenceExhaustiveGeneratedCalendarSourceLaw.signedGap rate rewards S (H.filter (fun e => e.before.overflow = b))) := by
  let mark : LogicalCell p rate → Fin p.T × (SlowSet p × (Fin p.K × Bool)) :=
    fun e => (e.time, (e.slowSet, (e.fastArm, e.before.overflow)))
  have hover : Measurable (fun e : LogicalCell p rate => e.before.overflow) :=
    (measurable_of_countable (fun r : RecordedQueueRun.RunState p.K => r.overflow)).comp
      ReferenceFirstLiveChronologicalPrefixMeasurability.measurable_logicalCell_before
  have hm : Measurable mark :=
    ReferenceFirstLiveChronologicalPrefixMeasurability.measurable_logicalCell_time.prodMk
      (ReferenceFirstLiveChronologicalPrefixMeasurability.measurable_logicalCell_slowSet.mono le_rfl le_top |>.prodMk
        (ReferenceFirstLiveChronologicalPrefixMeasurability.measurable_logicalCell_fastArm.prodMk hover))
  let F : List (Fin p.T × (SlowSet p × (Fin p.K × Bool))) → ℝ := fun L =>
    (L.map (fun e => if e.2.2.2 = b then
      (∑ i ∈ S.val, ((rewards e.1 i).val : ℝ) / (D p : ℝ)) -
        ((∑ i ∈ e.2.1.val, ((rewards e.1 i).val : ℝ) / (D p : ℝ)) +
          ((rewards e.1 e.2.2.1).val : ℝ) / (D p : ℝ)) else 0)).sum
  have hF : Measurable F := measurable_of_countable F
  convert hF.comp (ReferenceActiveHorizonMeasurability.measurable_list_map id measurable_id mark hm) using 1
  funext H
  change ReferenceExhaustiveGeneratedCalendarSourceLaw.signedGap rate rewards S (H.filter (fun e => e.before.overflow = b)) = F (H.map mark)
  induction H with
  | nil => simp only [List.filter_nil, ReferenceExhaustiveGeneratedCalendarSourceLaw.signedGap, List.map_nil, List.sum_nil, F]
  | cons e H ih =>
    by_cases he : e.before.overflow = b
    · simpa only [List.filter_cons, he, decide_true, ite_true,
        ReferenceExhaustiveGeneratedCalendarSourceLaw.signedGap, List.map_cons, List.sum_cons, F, mark,
        ReferenceInitialStoppedCalendar.cellReward] using congrArg
          (fun x => ((∑ i ∈ S.val, ((rewards e.time i).val : ℝ) / (D p : ℝ)) -
            ReferenceInitialStoppedCalendar.cellReward rate rewards e) + x) ih
    · simpa only [List.filter_cons, he, decide_false, Bool.false_eq_true, ite_false,
        ReferenceExhaustiveGeneratedCalendarSourceLaw.signedGap, List.map_cons, List.sum_cons, F, mark, zero_add] using ih

theorem measurable_retainedSignedGap (S : ProductSetLaw.ProductSet p.K p.m) :
    Measurable (retainedSignedGap rate rewards C_star C_h control0 S) :=
  (measurable_signedGap_filter rate rewards S false).comp
    (ReferenceExhaustiveGeneratedCalendarSourceLaw.measurable_terminalReadout rate rewards C_star C_h control0).snd.snd

theorem measurable_overflowTailSignedGap (S : ProductSetLaw.ProductSet p.K p.m) :
    Measurable (overflowTailSignedGap rate rewards C_star C_h control0 S) :=
  (measurable_signedGap_filter rate rewards S true).comp
    (ReferenceExhaustiveGeneratedCalendarSourceLaw.measurable_terminalReadout rate rewards C_star C_h control0).snd.snd

private theorem comparatorReward_bounds (S : ProductSetLaw.ProductSet p.K p.m) (q : Fin p.T) :
    0 ≤ ∑ i ∈ S.val, ((rewards q i).val : ℝ) / (D p : ℝ) ∧
      (∑ i ∈ S.val, ((rewards q i).val : ℝ) / (D p : ℝ)) ≤ p.m := by
  have hb (i : Fin p.K) : 0 ≤ ((rewards q i).val : ℝ) / (D p : ℝ) ∧
      ((rewards q i).val : ℝ) / (D p : ℝ) ≤ 1 := by
    refine ⟨div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _),
      (div_le_one (Nat.cast_pos.mpr (D_pos p))).mpr ?_⟩
    exact_mod_cast Nat.le_of_lt_succ (rewards q i).isLt
  refine ⟨Finset.sum_nonneg (fun i _ => (hb i).1), ?_⟩
  have hs := Finset.sum_le_sum (fun i (_hi : i ∈ S.val) => (hb i).2)
  simpa only [Finset.sum_const, nsmul_eq_mul, mul_one,
    (Finset.mem_powersetCard.mp S.property).2] using hs

private theorem signedGap_abs_le_length (S : ProductSetLaw.ProductSet p.K p.m)
    (H : List (LogicalCell p rate)) :
    |ReferenceExhaustiveGeneratedCalendarSourceLaw.signedGap rate rewards S H| ≤ (p.m : ℝ) * H.length := by
  induction H with
  | nil => simp only [ReferenceExhaustiveGeneratedCalendarSourceLaw.signedGap, List.map_nil, List.sum_nil, abs_zero,
      List.length_nil, Nat.cast_zero, mul_zero, le_refl]
  | cons e H ih =>
    have hc := comparatorReward_bounds rewards S e.time
    have he := ReferenceExhaustiveGeneratedCalendarSourceLaw.cellReward_bounds rate rewards e
    have hb : |(∑ i ∈ S.val, ((rewards e.time i).val : ℝ) / (D p : ℝ)) -
        ReferenceInitialStoppedCalendar.cellReward rate rewards e| ≤ p.m :=
      abs_le.mpr ⟨by linarith only [hc.1, he.2], by linarith only [hc.2, he.1]⟩
    change |((∑ i ∈ S.val, ((rewards e.time i).val : ℝ) / (D p : ℝ)) -
      ReferenceInitialStoppedCalendar.cellReward rate rewards e) + ReferenceExhaustiveGeneratedCalendarSourceLaw.signedGap rate rewards S H| ≤ _
    calc
      _ ≤ _ := abs_add_le _ _
      _ ≤ (p.m : ℝ) + (p.m : ℝ) * H.length := add_le_add hb ih
      _ = _ := by simp only [List.length_cons, Nat.cast_add, Nat.cast_one]; ring

private theorem chronological_length (H : List (LogicalCell p rate))
    (hH : H.Pairwise (fun e f => e.time.val < f.time.val)) : H.length ≤ p.T := by
  have hn : (H.map LogicalCell.time).Nodup := by
    rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
    exact hH.imp fun h => Fin.ne_of_val_ne (Nat.ne_of_lt h)
  simpa only [List.length_map, Fintype.card_fin] using hn.length_le_card

private theorem terminal_signedGap_filter_bound (S : ProductSetLaw.ProductSet p.K p.m)
    (b : Bool) (w : ReferenceExhaustiveGeneratedCalendarSourceLaw.Omega rate rewards C_star C_h) :
    |ReferenceExhaustiveGeneratedCalendarSourceLaw.signedGap rate rewards S
      ((ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalReadout rate rewards C_star C_h control0 w).2.2.filter
        (fun e => e.before.overflow = b))| ≤ (p.m : ℝ) * p.T := by
  apply (signedGap_abs_le_length rate rewards S _).trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  exact Nat.cast_le.mpr ((List.length_filter_le _ _).trans
    (chronological_length rate _ (ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalReadout_chronology rate rewards C_star C_h control0 w)))

theorem retainedSignedGap_abs_le (S : ProductSetLaw.ProductSet p.K p.m)
    (w : ReferenceExhaustiveGeneratedCalendarSourceLaw.Omega rate rewards C_star C_h) :
    |retainedSignedGap rate rewards C_star C_h control0 S w| ≤ (p.m : ℝ) * p.T :=
  terminal_signedGap_filter_bound rate rewards C_star C_h control0 S false w

theorem overflowTailSignedGap_abs_le (S : ProductSetLaw.ProductSet p.K p.m)
    (w : ReferenceExhaustiveGeneratedCalendarSourceLaw.Omega rate rewards C_star C_h) :
    |overflowTailSignedGap rate rewards C_star C_h control0 S w| ≤ (p.m : ℝ) * p.T :=
  terminal_signedGap_filter_bound rate rewards C_star C_h control0 S true w

theorem integrable_retainedSignedGap (ids : Option (CompletePublicTable.IDArray p))
    (S : ProductSetLaw.ProductSet p.K p.m) :
    Integrable (retainedSignedGap rate rewards C_star C_h control0 S)
      (ids.elim (ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalLaw rate rewards C_star C_h control0)
        (ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDTerminalLaw rate rewards C_star C_h control0)) := by
  cases ids <;> dsimp only [Option.elim] <;>
    apply Integrable.of_bound
      (measurable_retainedSignedGap rate rewards C_star C_h control0 S).aestronglyMeasurable
      ((p.m : ℝ) * p.T) <;>
    exact Filter.Eventually.of_forall fun w => by
      simpa only [Real.norm_eq_abs] using retainedSignedGap_abs_le rate rewards C_star C_h control0 S w

theorem integrable_overflowTailSignedGap (ids : Option (CompletePublicTable.IDArray p))
    (S : ProductSetLaw.ProductSet p.K p.m) :
    Integrable (overflowTailSignedGap rate rewards C_star C_h control0 S)
      (ids.elim (ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalLaw rate rewards C_star C_h control0)
        (ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDTerminalLaw rate rewards C_star C_h control0)) := by
  cases ids <;> dsimp only [Option.elim] <;>
    apply Integrable.of_bound
      (measurable_overflowTailSignedGap rate rewards C_star C_h control0 S).aestronglyMeasurable
      ((p.m : ℝ) * p.T) <;>
    exact Filter.Eventually.of_forall fun w => by
      simpa only [Real.norm_eq_abs] using overflowTailSignedGap_abs_le rate rewards C_star C_h control0 S w

/-- The full signed sum partitions into PRE-clear and incoming-overflow terms.
No sign is discarded in either part. -/
theorem signedGap_eq_retained_add_overflowTail (S : ProductSetLaw.ProductSet p.K p.m)
    (w : ReferenceExhaustiveGeneratedCalendarSourceLaw.Omega rate rewards C_star C_h) :
    ReferenceExhaustiveGeneratedCalendarSourceLaw.signedGap rate rewards S
        (ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalReadout rate rewards C_star C_h control0 w).2.2 =
      retainedSignedGap rate rewards C_star C_h control0 S w +
        overflowTailSignedGap rate rewards C_star C_h control0 S w := by
  unfold retainedSignedGap overflowTailSignedGap ReferenceExhaustiveGeneratedCalendarSourceLaw.signedGap
  symm
  simpa only [Bool.eq_true_eq_not_eq_false] using
    (List.sum_map_filter_add_sum_map_filter_not
      (fun e : LogicalCell p rate => e.before.overflow = false)
      (fun e => (∑ i ∈ S.val, ((rewards e.time i).val : ℝ) / (D p : ℝ)) -
        ReferenceInitialStoppedCalendar.cellReward rate rewards e)
      (ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalReadout rate rewards C_star C_h control0 w).2.2)

/-- Outside the actual numerical detector the complementary archive is empty;
on the detector its signed sum is at most `m*T`. -/
theorem ae_overflowTailSignedGap_le_indicator
    (ids : Option (CompletePublicTable.IDArray p)) (S : ProductSetLaw.ProductSet p.K p.m) :
    ∀ᵐ w ∂ids.elim (ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalLaw rate rewards C_star C_h control0)
      (ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDTerminalLaw rate rewards C_star C_h control0),
      overflowTailSignedGap rate rewards C_star C_h control0 S w ≤
        (ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalSource rate rewards C_star C_h control0 ⁻¹'
          overflowEvent).indicator (fun _ => (p.m : ℝ) * p.T) w := by
  filter_upwards [ae_incomingOverflow_implies_observedNumericalOverflowEvent
    rate rewards C_star C_h control0 ids] with w hw
  by_cases hevent : ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalSource
      rate rewards C_star C_h control0 w ∈ overflowEvent
  · have hmem : w ∈ ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalSource
        rate rewards C_star C_h control0 ⁻¹' overflowEvent := hevent
    rw [Set.indicator_of_mem hmem]
    exact (le_abs_self _).trans (overflowTailSignedGap_abs_le rate rewards C_star C_h control0 S w)
  · have hnil : (ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalReadout
        rate rewards C_star C_h control0 w).2.2.filter (fun e => e.before.overflow = true) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro e he hov
      exact hevent (hw e he (of_decide_eq_true hov))
    have hmem : w ∉ ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalSource
        rate rewards C_star C_h control0 ⁻¹' overflowEvent := hevent
    simp only [Set.indicator_of_notMem hmem, overflowTailSignedGap, hnil,
      ReferenceExhaustiveGeneratedCalendarSourceLaw.signedGap, List.map_nil, List.sum_nil, le_refl]

/-- The full all-enabled signed auxiliary readout is at most its retained
readout plus `m*T` times the same-source numerical-event indicator. -/
theorem ae_signedGap_le_retained_add_overflowIndicator
    (ids : Option (CompletePublicTable.IDArray p)) (S : ProductSetLaw.ProductSet p.K p.m) :
    ∀ᵐ w ∂ids.elim (ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalLaw rate rewards C_star C_h control0)
      (ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDTerminalLaw rate rewards C_star C_h control0),
      ReferenceExhaustiveGeneratedCalendarSourceLaw.signedGap rate rewards S
          (ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalReadout rate rewards C_star C_h control0 w).2.2 ≤
        retainedSignedGap rate rewards C_star C_h control0 S w +
          (ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalSource rate rewards C_star C_h control0 ⁻¹'
            overflowEvent).indicator (fun _ => (p.m : ℝ) * p.T) w := by
  filter_upwards [ae_overflowTailSignedGap_le_indicator rate rewards C_star C_h control0 ids S] with w hw
  rw [signedGap_eq_retained_add_overflowTail]
  exact add_le_add le_rfl hw

/-- The actual terminal source map transports the numerical event to the
original fixed-ID section, where its accepted bound holds for every ID array. -/
theorem fixedIDTerminalLaw_overflowEvent_le_inv_N_sq (ids : CompletePublicTable.IDArray p) :
    (ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDTerminalLaw rate rewards C_star C_h control0 ids).real
        (ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalSource rate rewards C_star C_h control0 ⁻¹'
          overflowEvent) ≤ 1 / (N p : ℝ) ^ 2 := by
  have hE := ReferenceOriginalCalendarNumericalOverflowBound.measurableSet_observedNumericalOverflowEvent
    rate rewards C_star C_h
  calc
    _ = (ReferenceFixedIDSourceSection.fixedIDSourceLaw ids).real overflowEvent := by
      rw [← ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDTerminalLaw_map_source
        rate rewards C_star C_h control0 ids,
        map_measureReal_apply
          (ReferenceExhaustiveGeneratedCalendarSourceLaw.measurable_terminalSource rate rewards C_star C_h control0) hE]
    _ ≤ _ := ReferenceOriginalCalendarFixedIDOverflowBound.observedNumericalOverflowEvent_fixedIDSourceLaw_le_inv_N_sq
      rate rewards C_star C_h control0 ids

/-- Remove the actual incoming-overflow signed tail at cost at most `m*T/N²`
under the same original fixed-ID terminal law. All source/event alignment,
measurability and integrability obligations are discharged internally. -/
theorem fixedID_integral_signedGap_le_retained_add_inv_N_sq
    (ids : CompletePublicTable.IDArray p) (S : ProductSetLaw.ProductSet p.K p.m) :
    (∫ w, ReferenceExhaustiveGeneratedCalendarSourceLaw.signedGap rate rewards S
        (ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalReadout rate rewards C_star C_h control0 w).2.2
      ∂ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDTerminalLaw rate rewards C_star C_h control0 ids) ≤
      (∫ w, ReferenceExhaustiveGeneratedCalendarSourceLaw.signedGap rate rewards S
        ((ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalReadout rate rewards C_star C_h control0 w).2.2.filter
          (fun e => e.before.overflow = false))
        ∂ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDTerminalLaw rate rewards C_star C_h control0 ids) +
      ((p.m : ℝ) * p.T) / (N p : ℝ) ^ 2 := by
  let ν := ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDTerminalLaw rate rewards C_star C_h control0 ids
  let E := ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalSource rate rewards C_star C_h control0 ⁻¹' overflowEvent
  have hE : MeasurableSet E :=
    (ReferenceOriginalCalendarNumericalOverflowBound.measurableSet_observedNumericalOverflowEvent
      rate rewards C_star C_h).preimage
      (ReferenceExhaustiveGeneratedCalendarSourceLaw.measurable_terminalSource rate rewards C_star C_h control0)
  have hfull := (ReferenceExhaustiveGeneratedCalendarSourceLaw.integrable_signedGap
    rate rewards C_star C_h control0 (some ids) S).1
  have hret := integrable_retainedSignedGap rate rewards C_star C_h control0 (some ids) S
  have hind : Integrable (E.indicator (fun _ => (p.m : ℝ) * p.T)) ν :=
    (integrable_const _).indicator hE
  have hmono := integral_mono_ae hfull (hret.add hind)
    (ae_signedGap_le_retained_add_overflowIndicator rate rewards C_star C_h control0 (some ids) S)
  simp only [Pi.add_apply] at hmono
  rw [integral_add hret hind, integral_indicator_const _ hE, smul_eq_mul] at hmono
  change (∫ w, ReferenceExhaustiveGeneratedCalendarSourceLaw.signedGap rate rewards S
      (ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalReadout rate rewards C_star C_h control0 w).2.2 ∂ν) ≤
    (∫ w, retainedSignedGap rate rewards C_star C_h control0 S w ∂ν) +
      ((p.m : ℝ) * p.T) / (N p : ℝ) ^ 2
  calc
    _ ≤ (∫ w, retainedSignedGap rate rewards C_star C_h control0 S w ∂ν) +
        ν.real E * ((p.m : ℝ) * p.T) := hmono
    _ ≤ _ := add_le_add le_rfl (by
      calc
        ν.real E * ((p.m : ℝ) * p.T) ≤ (1 / (N p : ℝ) ^ 2) * ((p.m : ℝ) * p.T) :=
          mul_le_mul_of_nonneg_right
            (fixedIDTerminalLaw_overflowEvent_le_inv_N_sq rate rewards C_star C_h control0 ids)
            (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
        _ = ((p.m : ℝ) * p.T) / (N p : ℝ) ^ 2 := by ring)

end Bandits.Support.ReferenceGeneratedCalendarOverflowTail

end
