/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveChronologicalLaw
public import Bandits.Support.ReferenceFirstLiveBirthJointSourceLaw

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.Probability.Kernel.Integral

/-!
# First-LIVE marked calendar transition

The literal source-retaining observation has its original product initial law
and an explicit Borel innovation/residual probability kernel. The all-source
bounded joint-test successor identity keeps complete logical cells, every
label-zero coordinate and the original full current control. The actual
pre-choice cell gate and the PRE-overflow/proposal residual are reconstructed
from the accepted source scan. Finite iteration and manuscript closure are
not asserted here.

Sources: `sources/zip4/manuscript/06_interruptions.tex:381-426`,
`sources/zip4/manuscript/04_slow_fast_learner.tex:142-215,323-366`, and
`sources/zip4/manuscript/08_main_theorem.tex:78-109`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support
open Bandits.Support.ConstructorDimensions
open Bandits.Support.ContinuousControlSlice
open Bandits.Support.ReferenceFirstCollectionAuxiliarySeeds
open Bandits.Support.ReferenceFirstLiveChronologicalPrefixFoundation
open Bandits.Support.ReferenceFirstLiveChronologicalPrefixCausality
open Bandits.Support.ReferenceFirstLiveActualRefreshTestLaw
open Bandits.Support.ReferenceSourcePrefixHistoryFiltration

namespace Bandits.Support.ReferenceFirstLiveCalendarMarkedTransition

variable {p : ConstructorDimensions.Parameters}

abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev RewardTable := ActualInitializationPhysicalStep.GridRewardTable
abbrev Source (p : ConstructorDimensions.Parameters) :=
  BootstrapPrivateRoundStreams.SourceInput p
abbrev AuxiliaryArray (p : ConstructorDimensions.Parameters) :=
  ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p
abbrev LabelZeroArray (p : ConstructorDimensions.Parameters) :=
  Fin p.T → ContinuousControlSlice.Scalar
abbrev Cell (p : ConstructorDimensions.Parameters) (rate : RateInput p) :=
  LogicalCell p rate
abbrev Observation (p : ConstructorDimensions.Parameters) (rate : RateInput p) :=
  Source p × (LabelZeroArray p × List (Cell p rate))
abbrev EnlargedSource (p : ConstructorDimensions.Parameters) := Source p × AuxiliaryArray p

/-- Keep the original label-zero scalar at every calendar date. -/
public def labelZero (a : AuxiliaryArray p) : LabelZeroArray p :=
  fun t => a (t, 0)

public theorem measurable_labelZero (p : ConstructorDimensions.Parameters) :
    Measurable (labelZero (p := p)) := by
  apply Measurable.of_eval
  intro t
  exact measurable_pi_apply (t, 0)

/-- The original label-zero marginal of the analytical auxiliary array. -/
public def labelZeroLaw (p : ConstructorDimensions.Parameters) :
    Measure (LabelZeroArray p) :=
  (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p).map labelZero

instance labelZeroLaw_probability (p : ConstructorDimensions.Parameters) :
    IsProbabilityMeasure (labelZeroLaw p) := by
  constructor
  rw [labelZeroLaw, Measure.map_apply (measurable_labelZero p) MeasurableSet.univ]
  simp

/-- The original source and the full independent auxiliary array. -/
public def enlargedSourceLaw (p : ConstructorDimensions.Parameters) :
    Measure (EnlargedSource p) :=
  (BootstrapPrivateRoundStreams.sourceInputLaw p).prod
    (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p)

instance enlargedSourceLaw_probability (p : ConstructorDimensions.Parameters) :
    IsProbabilityMeasure (enlargedSourceLaw p) := by
  change IsProbabilityMeasure
    ((BootstrapPrivateRoundStreams.sourceInputLaw p).prod
      (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p))
  infer_instance

/-- The literal observation at calendar offset `n`: replace only the
unobserved suffix of the selected source control, retain every original
label-zero coordinate, and keep the complete logical-cell list strictly in
the calendar past. -/
public def observationAt (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (n : ℕ) (za : EnlargedSource p) : Observation p rate :=
  (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n za.1,
    (labelZero za.2,
      ReferenceFirstLiveChronologicalPrefixCausality.calendarPast
        rate rewards C_star C_h za n))

/-- The map above is Borel at every in-horizon date.  The full source prefix,
label-zero auxiliary path, and complete calendar past are all retained. -/
public theorem measurable_observationAt (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) :
    Measurable (observationAt rate rewards C_star C_h control0 t.val) := by
  have hc : Measurable (fun za : EnlargedSource p =>
      ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val za.1) :=
    (ReferenceSourcePrefixHistoryFiltration.measurable_sourcePrefix control0 t.val).comp
      measurable_fst
  have ha : Measurable (fun za : EnlargedSource p => labelZero za.2) := by
    apply Measurable.of_eval
    intro u
    exact (measurable_pi_apply (u, 0)).comp measurable_snd
  have hp := ReferenceFirstLiveActualRefreshTestLaw.measurable_calendarPast
    rate rewards C_star C_h t
  exact hc.prodMk (ha.prodMk hp)

/-- The complete selected-row control at the current date is fresh given the
same original source prefix used by the calendar observation. -/
public theorem sourcePrefix_currentControl_product
    (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T) :
    (BootstrapPrivateRoundStreams.sourceInputLaw p).map
        (fun z =>
          (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z,
            ReferenceSourceCurrentControlFreshness.u_t p t z)) =
      ((BootstrapPrivateRoundStreams.sourceInputLaw p).map
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val)).prod
        (ContinuousLearningRows.timeControlLaw p) := by
  have hreplace : ReferenceSourceCurrentControlFreshness.c_t p control0 t =
      ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val := by
    funext z
    exact (ReferenceSourcePrefixHistoryFiltration.sourcePrefix_eq_suffix
      control0 t.val t.isLt z).symm
  rw [← hreplace]
  exact ReferenceSourceCurrentControlFreshness.source_joint_prefix_control control0 t

/-- At the horizon every cell of the canonical path belongs to the calendar
past, so this observation stores the whole chronological prefix. -/
public theorem calendarPast_horizon (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (za : EnlargedSource p) :
    ReferenceFirstLiveChronologicalPrefixCausality.calendarPast
      rate rewards C_star C_h za p.T =
        ReferenceFirstLiveChronologicalPrefixFoundation.firstLiveChronologicalPrefix
          rate rewards C_star C_h za := by
  unfold ReferenceFirstLiveChronologicalPrefixCausality.calendarPast
  apply List.takeWhile_eq_self_iff.mpr
  intro cell hcell
  exact decide_eq_true cell.time.isLt

/-- Terminal source retention is exact: `c_T` is the original source and
`H_T` is the full first-LIVE chronological prefix. -/
public theorem observationAt_horizon (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (za : EnlargedSource p) :
    observationAt rate rewards C_star C_h control0 p.T za =
      (za.1,
        (labelZero za.2,
          ReferenceFirstLiveChronologicalPrefixFoundation.firstLiveChronologicalPrefix
            rate rewards C_star C_h za)) := by
  simp only [observationAt,
    ReferenceSourcePrefixHistoryFiltration.sourcePrefix_eq_self control0 p.T le_rfl,
    calendarPast_horizon rate rewards C_star C_h za]

/-- The terminal observation is Borel, using the already established
whole-prefix measurability. -/
public theorem measurable_observationAt_horizon (rate : RateInput p)
    (rewards : RewardTable p) (C_star C_h : ℝ)
    (control0 : ContinuousLearningRows.TimeControl p) :
    Measurable (observationAt rate rewards C_star C_h control0 p.T) := by
  have ha : Measurable (fun za : EnlargedSource p => labelZero za.2) := by
    apply Measurable.of_eval
    intro t
    exact (measurable_pi_apply (t, 0)).comp measurable_snd
  have hp :=
    ReferenceFirstLiveChronologicalPrefixMeasurability.measurable_firstLiveChronologicalPrefix
      rate rewards C_star C_h
  have hsource : Measurable (fun za : EnlargedSource p => za.1) := measurable_fst
  have hterminal : Measurable (fun za : EnlargedSource p =>
      ReferenceFirstLiveChronologicalPrefixFoundation.firstLiveChronologicalPrefix
        rate rewards C_star C_h za) := hp
  have hobs : observationAt rate rewards C_star C_h control0 p.T =
      fun za => (za.1,
        (labelZero za.2,
          ReferenceFirstLiveChronologicalPrefixFoundation.firstLiveChronologicalPrefix
            rate rewards C_star C_h za)) := by
    funext za
    exact observationAt_horizon rate rewards C_star C_h control0 za
  rw [hobs]
  exact hsource.prodMk (ha.prodMk hterminal)

/-- At the initial calendar boundary the retained chronological history is
empty, including on no-launch and terminal-launch sources. -/
public theorem calendarPast_zero (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (za : EnlargedSource p) :
    ReferenceFirstLiveChronologicalPrefixCausality.calendarPast
      rate rewards C_star C_h za 0 = [] := by
  unfold ReferenceFirstLiveChronologicalPrefixCausality.calendarPast
  cases ReferenceFirstLiveChronologicalPrefixFoundation.firstLiveChronologicalPrefix
      rate rewards C_star C_h za <;> simp

/-- The literal initial law required by finite iteration. -/
public def initialCalendarLaw (rate : RateInput p)
    (control0 : ContinuousLearningRows.TimeControl p) :
    Measure (Observation p rate) :=
  ((BootstrapPrivateRoundStreams.sourceInputLaw p).map
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 0)).prod
    ((labelZeroLaw (p := p)).prod
      (Measure.dirac ([] : List (Cell p rate))))

/-- The initial observation has exactly the original prefix, label-zero
auxiliary marginal, and empty chronological history. -/
public theorem observationAt_zero_map (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p) :
    (enlargedSourceLaw (p := p)).map
        (observationAt rate rewards C_star C_h control0 0) =
      initialCalendarLaw rate control0 := by
  let μ := BootstrapPrivateRoundStreams.sourceInputLaw p
  let ν := ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p
  let c0 := ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 0
  let a0 := labelZero (p := p)
  let g : AuxiliaryArray p → LabelZeroArray p × List (Cell p rate) :=
    fun a => (a0 a, [])
  have hc0 : Measurable c0 :=
    ReferenceSourcePrefixHistoryFiltration.measurable_sourcePrefix control0 0
  have ha0 : Measurable a0 := by
    apply Measurable.of_eval
    intro u
    exact measurable_pi_apply (u, 0)
  have hg : Measurable g := ha0.prodMk measurable_const
  have hzero : ∀ za : EnlargedSource p,
      observationAt rate rewards C_star C_h control0 0 za =
        (c0 za.1, g za.2) := by
    intro za
    simp [observationAt, c0, g, a0, calendarPast_zero rate rewards C_star C_h za]
  have haux : ν.map g =
      (labelZeroLaw p).prod (Measure.dirac ([] : List (Cell p rate))) := by
    rw [Measure.prod_dirac]
    change ν.map (fun a => (labelZero a, [])) =
      (ν.map labelZero).map (fun x => (x, []))
    exact (Measure.map_map measurable_prodMk_right ha0).symm
  calc
    (enlargedSourceLaw (p := p)).map
        (observationAt rate rewards C_star C_h control0 0) =
        (μ.prod ν).map (Prod.map c0 g) := by
          apply Measure.map_congr
          filter_upwards with za
          exact hzero za
    _ = (μ.map c0).prod (ν.map g) :=
      (Measure.map_prod_map μ ν hc0 hg).symm
    _ = initialCalendarLaw rate control0 := by
      rw [haux]
      rfl

/-- The enlarged source is a probability measure, so bounded Borel tests of
any in-horizon observation are integrable on the original source product. -/
public theorem integrable_bounded_observation_test (rate : RateInput p)
    (rewards : RewardTable p) (C_star C_h : ℝ)
    (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T)
    (Phi : Observation p rate → ℝ) (hPhi : Measurable Phi)
    (B : ℝ) (hB : ∀ x, ‖Phi x‖ ≤ B) :
    Integrable (fun za => Phi (observationAt rate rewards C_star C_h control0 t.val za))
      (enlargedSourceLaw (p := p)) := by
  exact Integrable.of_bound
    ((hPhi.comp (measurable_observationAt rate rewards C_star C_h control0 t)).aestronglyMeasurable)
    B (Filter.Eventually.of_forall fun za => hB
      (observationAt rate rewards C_star C_h control0 t.val za))

/-- An absent current cell is tagged separately from every complete cell. -/
abbrev CurrentCellTag (p : ConstructorDimensions.Parameters) (rate : RateInput p) :=
  Unit ⊕ Cell p rate

/-- Read the next entry after the strict calendar past. An absent entry is
actual absence in the canonical path, rather than a fabricated logical cell. -/
public def currentCellTag (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T) (za : EnlargedSource p) : CurrentCellTag p rate :=
  ReferenceActiveHorizonMeasurability.listObservationAt
    (calendarPast rate rewards C_star C_h za (t.val + 1))
    (calendarPast rate rewards C_star C_h za t.val).length

private theorem measurable_calendarPast_boundary (rate : RateInput p)
    (rewards : RewardTable p) (C_star C_h : ℝ) (n : ℕ) (hn : n ≤ p.T) :
    Measurable (fun za : EnlargedSource p => calendarPast rate rewards C_star C_h za n) := by
  by_cases h : n < p.T
  · exact ReferenceFirstLiveActualRefreshTestLaw.measurable_calendarPast
      rate rewards C_star C_h ⟨n, h⟩
  · have heq : n = p.T := by omega
    subst n
    have hfun : (fun za : EnlargedSource p => calendarPast rate rewards C_star C_h za p.T) =
        firstLiveChronologicalPrefix rate rewards C_star C_h := by
      funext za
      exact calendarPast_horizon rate rewards C_star C_h za
    rw [hfun]
    exact ReferenceFirstLiveChronologicalPrefixMeasurability.measurable_firstLiveChronologicalPrefix
      rate rewards C_star C_h

/-- Current-cell lookup is Borel in the original full continuous source. -/
public theorem measurable_currentCellTag (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T) :
    Measurable (currentCellTag rate rewards C_star C_h t) := by
  have hp := measurable_calendarPast_boundary rate rewards C_star C_h (t.val + 1) (by omega)
  have hh := ReferenceFirstLiveActualRefreshTestLaw.measurable_calendarPast
    rate rewards C_star C_h t
  have hc := ReferenceActiveHorizonMeasurability.measurable_listObservationCoordinates.comp hp
  have hl := measurable_fst.comp
    (ReferenceActiveHorizonMeasurability.measurable_listObservationCoordinates.comp hh)
  have heval : Measurable (fun v : ℕ × (ℕ → Unit ⊕ Cell p rate) => v.2 v.1) :=
    measurable_from_prod_countable_right fun n => measurable_pi_apply n
  exact heval.comp (hl.prodMk (measurable_snd.comp hc))

/-- The lookup is exactly the ordinary calendar-position lookup when launch
has occurred, and is absent before launch. This includes all cutoff cases. -/
public theorem currentCellTag_eq_lookup (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T) (z : Source p) (a : AuxiliaryArray p) :
    currentCellTag rate rewards C_star C_h t (z, a) =
      if ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h ≤ t.val then
        ReferenceActiveHorizonMeasurability.listObservationAt
          (firstLiveChronologicalPrefix rate rewards C_star C_h (z, a))
          (t.val - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
      else Sum.inl () := by
  let path := firstLiveChronologicalPrefix rate rewards C_star C_h (z, a)
  let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  simp only [currentCellTag, calendarPast_eq_take_elapsed, List.length_take]
  change ReferenceActiveHorizonMeasurability.listObservationAt
      (path.take (t.val + 1 - s)) (min (t.val - s) path.length) =
    if s ≤ t.val then ReferenceActiveHorizonMeasurability.listObservationAt path (t.val - s)
    else Sum.inl ()
  by_cases hs : s ≤ t.val
  · rw [ite_eq_left hs]
    have hn : t.val + 1 - s = (t.val - s) + 1 := by omega
    rw [hn]
    unfold ReferenceActiveHorizonMeasurability.listObservationAt
    by_cases hk : t.val - s < path.length
    · rw [Nat.min_eq_left (Nat.le_of_lt hk), List.getElem?_take]
      simp only [Nat.lt_succ_self, ite_true]
    · rw [Nat.min_eq_right (by omega), List.getElem?_eq_none (by simp),
        List.getElem?_eq_none (by omega)]
  · rw [ite_eq_right hs]
    have hn : t.val + 1 - s = 0 := by omega
    simp only [hn, List.take_zero, ReferenceActiveHorizonMeasurability.listObservationAt,
      List.getElem?_nil]

/-- The literal calendar successor appends exactly the current complete cell,
or appends nothing on genuine absence. -/
public theorem calendarPast_successor (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T) (za : EnlargedSource p) :
    calendarPast rate rewards C_star C_h za (t.val + 1) =
      calendarPast rate rewards C_star C_h za t.val ++
        match currentCellTag rate rewards C_star C_h t za with
        | .inl _ => []
        | .inr e => [e] := by
  rcases za with ⟨z, a⟩
  rw [currentCellTag_eq_lookup]
  simp only [calendarPast_eq_take_elapsed]
  let path := firstLiveChronologicalPrefix rate rewards C_star C_h (z, a)
  let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  change path.take (t.val + 1 - s) = path.take (t.val - s) ++
    match (if s ≤ t.val then
      ReferenceActiveHorizonMeasurability.listObservationAt path (t.val - s) else Sum.inl ()) with
    | .inl _ => []
    | .inr e => [e]
  by_cases hs : s ≤ t.val
  · rw [ite_eq_left hs]
    have hn : t.val + 1 - s = (t.val - s) + 1 := by omega
    rw [hn, List.take_add_one]
    cases hget : path[t.val - s]?
      <;> simp only [ReferenceActiveHorizonMeasurability.listObservationAt, hget, Option.toList]
  · rw [ite_eq_right hs]
    have hn : t.val + 1 - s = 0 := by omega
    have hm : t.val - s = 0 := by omega
    simp only [hn, hm, List.take_zero, List.append_nil]

/-- Replacing the unobserved source suffix after the current date preserves
the current complete cell, including actual absence. -/
public theorem currentCellTag_sourcePrefix (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) (z : Source p) (a : AuxiliaryArray p) :
    currentCellTag rate rewards C_star C_h t (z, a) =
      currentCellTag rate rewards C_star C_h t
        (sourcePrefix control0 (t.val + 1) z, a) := by
  have hnext := calendarPast_sourcePrefix rate rewards C_star C_h control0
    (t.val + 1) (by omega) z a
  have hpast := calendarPast_sourcePrefix rate rewards C_star C_h control0 t.val
    (Nat.le_of_lt t.isLt) z a
  have hpast' := calendarPast_sourcePrefix rate rewards C_star C_h control0 t.val
    (Nat.le_of_lt t.isLt) (sourcePrefix control0 (t.val + 1) z) a
  rw [sourcePrefix_sourcePrefix control0 t.val (t.val + 1) (by omega)] at hpast'
  simp only [currentCellTag, hnext, hpast.trans hpast'.symm]

/-- One source-correct local auxiliary innovation: all other label-one
coordinates are unused by this date's cell and are set to the fixed scalar
section. Label zero is kept outside this sampler in the observation. -/
public def innovationAuxiliary (t : Fin p.T) (x : ContinuousControlSlice.Scalar) :
    AuxiliaryArray p :=
  Function.update (auxiliarySection (p := p)) (t, 1) x

public theorem measurable_innovationAuxiliary (t : Fin p.T) :
    Measurable (innovationAuxiliary (p := p) t) := by
  classical
  apply Measurable.of_eval
  intro q
  by_cases hq : q = (t, 1)
  · simp only [innovationAuxiliary, hq, Function.update_self]
    exact measurable_id
  · simp only [innovationAuxiliary, Function.update_of_ne hq]
    exact measurable_const

/-- Only the scalar at the actual current date enters the complete current
cell. Earlier auxiliary draws remain in the retained list, not in this cell. -/
public theorem currentCellTag_auxiliary_ext (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T) (z : Source p) (a b : AuxiliaryArray p)
    (hab : a (t, 1) = b (t, 1)) :
    currentCellTag rate rewards C_star C_h t (z, a) =
      currentCellTag rate rewards C_star C_h t (z, b) := by
  rw [currentCellTag_eq_lookup, currentCellTag_eq_lookup]
  split
  · let k := t.val - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
    let W := ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow rate rewards C_star C_h z
    change ReferenceActiveHorizonMeasurability.listObservationAt
        (firstLiveChronologicalPrefix rate rewards C_star C_h (z, a)) k =
      ReferenceActiveHorizonMeasurability.listObservationAt
        (firstLiveChronologicalPrefix rate rewards C_star C_h (z, b)) k
    by_cases hk : k < W.length
    · have hka : k < (firstLiveChronologicalPrefix rate rewards C_star C_h (z, a)).length := by
        simpa only [firstLiveChronologicalPrefix_length,
          ReferenceFirstLiveOverflowReadout.wholeFirstLiveLength] using hk
      have hkb : k < (firstLiveChronologicalPrefix rate rewards C_star C_h (z, b)).length := by
        simpa only [firstLiveChronologicalPrefix_length,
          ReferenceFirstLiveOverflowReadout.wholeFirstLiveLength] using hk
      have ht : (W[k]).input.time = t := by
        apply Fin.ext
        have hg := wholeLiveCell_geometry rate rewards C_star C_h z ⟨k, hk⟩
        have htime := hg.2.2.1
        change (W[k]).input.time.val =
          ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + k at htime
        dsimp only [k] at htime ⊢
        omega
      dsimp only [W] at ht
      simp only [ReferenceActiveHorizonMeasurability.listObservationAt,
        List.getElem?_eq_getElem hka, List.getElem?_eq_getElem hkb]
      congr 1
      rw [firstLiveChronologicalPrefix_get rate rewards C_star C_h z a ⟨k, hk⟩,
        firstLiveChronologicalPrefix_get rate rewards C_star C_h z b ⟨k, hk⟩]
      simp only [appendLogicalCell, ht, hab]
    · have hka : (firstLiveChronologicalPrefix rate rewards C_star C_h (z, a)).length ≤ k := by
        simpa only [firstLiveChronologicalPrefix_length,
          ReferenceFirstLiveOverflowReadout.wholeFirstLiveLength] using Nat.le_of_not_gt hk
      have hkb : (firstLiveChronologicalPrefix rate rewards C_star C_h (z, b)).length ≤ k := by
        simpa only [firstLiveChronologicalPrefix_length,
          ReferenceFirstLiveOverflowReadout.wholeFirstLiveLength] using Nat.le_of_not_gt hk
      simp only [ReferenceActiveHorizonMeasurability.listObservationAt,
        List.getElem?_eq_none hka, List.getElem?_eq_none hkb]
  · rfl

/-- The canonical current cell is recovered from the original scalar, without
retaining that scalar in its own residual test. -/
public theorem currentCellTag_innovation (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T) (z : Source p) (a : AuxiliaryArray p) :
    currentCellTag rate rewards C_star C_h t (z, a) =
      currentCellTag rate rewards C_star C_h t
        (z, innovationAuxiliary t (a (t, 1))) := by
  apply currentCellTag_auxiliary_ext
  simp only [innovationAuxiliary, Function.update_self]

/-- Append an actual current cell; an absent calendar entry leaves the list
unchanged. No physical or numerical field of a present cell is projected out. -/
public def appendCurrentTag {rate : RateInput p} (history : List (Cell p rate)) : CurrentCellTag p rate →
    List (Cell p rate)
  | .inl _ => history
  | .inr entry => history ++ [entry]

private theorem measurable_append_singleton {α : Type*} [MeasurableSpace α] :
    Measurable (fun v : List α × α => v.1 ++ [v.2]) := by
  apply measurable_comap_iff.mpr
  have hc := ReferenceActiveHorizonMeasurability.measurable_listObservationCoordinates.comp
    (measurable_fst : Measurable (Prod.fst : List α × α → List α))
  have hl : Measurable (fun v : List α × α => v.1.length) := measurable_fst.comp hc
  have hlen : Measurable (fun v : List α × α => (v.1 ++ [v.2]).length) := by
    simpa only [List.length_append, List.length_singleton, Function.comp_def] using
      (measurable_of_countable (fun n : ℕ => n + 1)).comp hl
  apply hlen.prodMk
  apply Measurable.of_eval
  intro k
  have hlt : MeasurableSet {v : List α × α | k < v.1.length} :=
    (MeasurableSet.of_discrete : MeasurableSet {n : ℕ | k < n}).preimage hl
  have heq : MeasurableSet {v : List α × α | k = v.1.length} :=
    (MeasurableSet.of_discrete : MeasurableSet {n : ℕ | k = n}).preimage hl
  have hlookup := (measurable_pi_apply k).comp (measurable_snd.comp hc)
  have hm : Measurable (fun v : List α × α => if k < v.1.length then
      ReferenceActiveHorizonMeasurability.listObservationAt v.1 k else
      if k = v.1.length then Sum.inr v.2 else Sum.inl ()) :=
    hlookup.ite hlt ((measurable_inr.comp measurable_snd).ite heq measurable_const)
  convert hm using 1
  funext v
  change ReferenceActiveHorizonMeasurability.listObservationAt (v.1 ++ [v.2]) k = _
  unfold ReferenceActiveHorizonMeasurability.listObservationAt
  by_cases hk : k < v.1.length
  · rw [ite_eq_left hk, List.getElem?_append_left hk]
  · rw [ite_eq_right hk, List.getElem?_append_right (by omega)]
    by_cases he : k = v.1.length
    · simp only [he, Nat.sub_self, List.getElem?_cons_zero, ite_true]
    · rw [ite_eq_right he, List.getElem?_eq_none (by simp; omega)]

public theorem measurable_appendCurrentTag (rate : RateInput p) :
    Measurable (fun v : List (Cell p rate) × CurrentCellTag p rate =>
      appendCurrentTag v.1 v.2) := by
  have hm : Measurable (Sum.elim
      (fun v : List (Cell p rate) × Unit => v.1)
      (fun v : List (Cell p rate) × Cell p rate => v.1 ++ [v.2])) :=
    measurable_fst.sumElim measurable_append_singleton
  convert hm.comp (MeasurableEquiv.prodSumDistrib _ _ _).measurable using 1
  funext v
  rcases v with ⟨history, tag⟩
  cases tag <;> rfl

/-- The local innovation law uses the original full current-control law and
one independent label-one uniform. In particular unused controls are kept. -/
public def calendarInnovationLaw (p : ConstructorDimensions.Parameters) :
    Measure (ContinuousLearningRows.TimeControl p × ContinuousControlSlice.Scalar) :=
  (ContinuousLearningRows.timeControlLaw p).prod ContinuousControlSlice.scalarLaw

instance calendarInnovationLaw_probability (p : ConstructorDimensions.Parameters) :
    IsProbabilityMeasure (calendarInnovationLaw p) := by
  unfold calendarInnovationLaw
  infer_instance

/-- A single marked calendar innovation. The source insertion keeps every
coordinate of `u`; the local scalar affects only the actual current cell's
next slow set. The old complete history is retained literally. -/
public def calendarTransitionSample (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T)
    (v : Observation p rate ×
      (ContinuousLearningRows.TimeControl p × ContinuousControlSlice.Scalar)) :
    Observation p rate :=
  let c' := ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t v.1.1 v.2.1
  (c', (v.1.2.1, appendCurrentTag v.1.2.2
    (currentCellTag rate rewards C_star C_h t (c', innovationAuxiliary t v.2.2))))

public theorem measurable_calendarTransitionSample (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T) :
    Measurable (calendarTransitionSample rate rewards C_star C_h t) := by
  let D := Observation p rate ×
    (ContinuousLearningRows.TimeControl p × ContinuousControlSlice.Scalar)
  have hc : Measurable (fun v : D =>
      ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t v.1.1 v.2.1) :=
    (ReferenceSourcePhysicalFlagConditionalLaw.measurable_replaceSourceControl p t).comp
    ((measurable_fst.comp measurable_fst).prodMk (measurable_fst.comp measurable_snd))
  have hx : Measurable (fun v : D => innovationAuxiliary t v.2.2) :=
    (measurable_innovationAuxiliary (p := p) t).comp
    (measurable_snd.comp measurable_snd)
  have htag := (measurable_currentCellTag rate rewards C_star C_h t).comp (hc.prodMk hx)
  have hh := (measurable_appendCurrentTag rate).comp
    ((measurable_snd.comp (measurable_snd.comp measurable_fst)).prodMk htag)
  exact hc.prodMk ((measurable_fst.comp (measurable_snd.comp measurable_fst)).prodMk hh)

/-- The Borel innovation kernel on the same source-retaining observation.
This appends one local cell; it does not sample a whole replacement path. -/
public def calendarTransitionKernel (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T) :
    ProbabilityTheory.Kernel (Observation p rate) (Observation p rate) :=
  ProbabilityTheory.Kernel.mapOfMeasurable
    (ProbabilityTheory.Kernel.prod ProbabilityTheory.Kernel.id
      (ProbabilityTheory.Kernel.const (Observation p rate) (calendarInnovationLaw p)))
    (calendarTransitionSample rate rewards C_star C_h t)
    (measurable_calendarTransitionSample rate rewards C_star C_h t)

instance calendarTransitionKernel_markov (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T) :
    ProbabilityTheory.IsMarkovKernel (calendarTransitionKernel rate rewards C_star C_h t) := by
  unfold calendarTransitionKernel
  rw [ProbabilityTheory.Kernel.mapOfMeasurable_eq_map]
  exact ProbabilityTheory.Kernel.IsMarkovKernel.map _
    (measurable_calendarTransitionSample rate rewards C_star C_h t)

/-- The raw innovation formula, retaining the full original control even
on absent or frozen branches. -/
public theorem calendarTransitionKernel_apply (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T) (w : Observation p rate) :
    calendarTransitionKernel rate rewards C_star C_h t w =
      (calendarInnovationLaw p).map
        (fun ux => calendarTransitionSample rate rewards C_star C_h t (w, ux)) := by
  change (((ProbabilityTheory.Kernel.prod ProbabilityTheory.Kernel.id
      (ProbabilityTheory.Kernel.const (Observation p rate) (calendarInnovationLaw p))) w).map
      (calendarTransitionSample rate rewards C_star C_h t)) = _
  rw [ProbabilityTheory.Kernel.prod_apply, ProbabilityTheory.Kernel.id_apply,
    ProbabilityTheory.Kernel.const_apply, Measure.dirac_prod,
    Measure.map_map (measurable_calendarTransitionSample rate rewards C_star C_h t)
      measurable_prodMk_left]
  rfl

/-- Exact reconstruction on every original source: the next retained source
is obtained by inserting its same full current control, and the next list by
using its same single current auxiliary scalar. -/
public theorem calendarTransitionSample_actual (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) (za : EnlargedSource p) :
    calendarTransitionSample rate rewards C_star C_h t
      (observationAt rate rewards C_star C_h control0 t.val za,
        (ReferenceSourceCurrentControlFreshness.u_t p t za.1, za.2 (t, 1))) =
      observationAt rate rewards C_star C_h control0 (t.val + 1) za := by
  have hsource := prefix_successor_restore control0 t za.1
  change sourcePrefix control0 (t.val + 1) za.1 =
    ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
      (sourcePrefix control0 t.val za.1)
      (ReferenceSourceCurrentControlFreshness.u_t p t za.1) at hsource
  have htag := (currentCellTag_sourcePrefix rate rewards C_star C_h control0 t za.1 za.2).trans
    (currentCellTag_innovation rate rewards C_star C_h t
      (sourcePrefix control0 (t.val + 1) za.1) za.2)
  simp only [calendarTransitionSample, observationAt, ← hsource, ← htag]
  congr 2
  have hn := (calendarPast_successor rate rewards C_star C_h t za).symm
  cases htag' : currentCellTag rate rewards C_star C_h t za <;>
    simpa only [htag', appendCurrentTag, List.append_nil] using hn

private theorem measurePreserving_reorder
    {α β γ δ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] [MeasurableSpace δ]
    (a : Measure α) (b : Measure β) (c : Measure γ) (d : Measure δ)
    [IsProbabilityMeasure a] [IsProbabilityMeasure b]
    [IsProbabilityMeasure c] [IsProbabilityMeasure d] :
    MeasurePreserving (fun v : (α × β) × (γ × δ) => ((v.1.1, v.2.1), (v.1.2, v.2.2)))
      ((a.prod b).prod (c.prod d)) ((a.prod c).prod (b.prod d)) := by
  have h1 := measurePreserving_prodAssoc a b (c.prod d)
  have h2 := (MeasurePreserving.id a).prod (measurePreserving_prodAssoc b c d).symm
  have h3 := (MeasurePreserving.id a).prod
    ((Measure.measurePreserving_swap (μ := b) (ν := c)).prod (MeasurePreserving.id d))
  have h4 := (MeasurePreserving.id a).prod (measurePreserving_prodAssoc c b d)
  have h5 := (measurePreserving_prodAssoc a c (b.prod d)).symm
  exact h5.comp (h4.comp (h3.comp (h2.comp h1)))

/-- Reconstruct the same strict-past observation from the source prefix and
the auxiliary array with only the current label-one scalar erased. -/
public def observationFromErasure (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T)
    (v : Source p × ErasedAuxiliaryArray (p := p) t) : Observation p rate :=
  let a := insertActualRefreshCoordinate t v.2 scalarZero
  (v.1, (labelZero a, calendarPast rate rewards C_star C_h (v.1, a) t.val))

public theorem measurable_observationFromErasure (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T) :
    Measurable (observationFromErasure rate rewards C_star C_h t) := by
  have ha : Measurable (fun v : Source p × ErasedAuxiliaryArray (p := p) t =>
      insertActualRefreshCoordinate t v.2 scalarZero) :=
    (measurable_insertActualRefreshCoordinate t).comp (measurable_snd.prodMk measurable_const)
  exact measurable_fst.prodMk (((measurable_labelZero p).comp ha).prodMk
    ((ReferenceFirstLiveActualRefreshTestLaw.measurable_calendarPast rate rewards C_star C_h t).comp
      (measurable_fst.prodMk ha)))

private theorem split_insert_original (t : Fin p.T) (a : AuxiliaryArray p) :
    insertActualRefreshCoordinate t (actualRefreshScalarSplit t a).1
      (actualRefreshScalarSplit t a).2 = a :=
  (actualRefreshScalarSplit_symm_apply t (actualRefreshScalarSplit t a)).symm.trans
    ((actualRefreshScalarSplit t).symm_apply_apply a)

private theorem split_scalar (t : Fin p.T) (a : AuxiliaryArray p) :
    (actualRefreshScalarSplit t a).2 = a (t, 1) := by
  have h := congrArg (fun b : AuxiliaryArray p => b (t, 1)) (split_insert_original t a)
  simpa only [insertActualRefreshCoordinate, dite_true] using h

/-- Erasure removes only the scalar to be integrated now. Every label-zero
coordinate and the complete strict-past logical list are recovered. -/
public theorem observationFromErasure_actual (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) (za : EnlargedSource p) :
    observationFromErasure rate rewards C_star C_h t
      (sourcePrefix control0 t.val za.1, (actualRefreshScalarSplit t za.2).1) =
        observationAt rate rewards C_star C_h control0 t.val za := by
  let a := insertActualRefreshCoordinate t (actualRefreshScalarSplit t za.2).1 scalarZero
  have hcoord (q : ReferenceFirstCollectionAuxiliarySeeds.Coordinate p) (hq : q ≠ (t, 1)) :
      a q = za.2 q := by
    rw [← split_insert_original t za.2]
    simp only [a, insertActualRefreshCoordinate, hq, dite_false]
  have hlabel : labelZero a = labelZero za.2 := by
    funext u
    exact hcoord (u, 0) (by intro h; have := congrArg Prod.snd h; exact Fin.zero_ne_one this)
  have hpast := calendarPast_auxiliary_ext rate rewards C_star C_h
    (sourcePrefix control0 t.val za.1) a za.2 t.val (by
      intro u hu
      apply hcoord
      intro heq
      have hut : u = t := congrArg Prod.fst heq
      subst u
      omega)
  have hsource := calendarPast_sourcePrefix rate rewards C_star C_h control0 t.val
    (Nat.le_of_lt t.isLt) za.1 za.2
  change (sourcePrefix control0 t.val za.1, (labelZero a,
      calendarPast rate rewards C_star C_h (sourcePrefix control0 t.val za.1, a) t.val)) = _
  rw [hlabel, hpast, ← hsource]
  rfl

/-- The full current control and the single current label-one scalar are
jointly fresh given the retained source, all label-zero coordinates and the
complete strict-past list. No eventual launch or cutoff event is conditioned on. -/
public theorem observation_current_innovation_product (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T) :
    (enlargedSourceLaw p).map (fun za =>
        (observationAt rate rewards C_star C_h control0 t.val za,
          (ReferenceSourceCurrentControlFreshness.u_t p t za.1, za.2 (t, 1)))) =
      ((enlargedSourceLaw p).map
        (observationAt rate rewards C_star C_h control0 t.val)).prod
        (calendarInnovationLaw p) := by
  let μ := BootstrapPrivateRoundStreams.sourceInputLaw p
  let ν := ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p
  let μc := μ.map (sourcePrefix control0 t.val)
  let μe := erasedAuxiliaryLaw (p := p) t
  let μu := ContinuousLearningRows.timeControlLaw p
  let μx := ContinuousControlSlice.scalarLaw
  let f := fun z : Source p => (sourcePrefix control0 t.val z,
    ReferenceSourceCurrentControlFreshness.u_t p t z)
  have hf : Measurable f :=
    (measurable_sourcePrefix control0 t.val).prodMk
      (ReferenceSourceCurrentControlFreshness.measurable_u_t t)
  have hsource : MeasurePreserving f μ (μc.prod μu) :=
    ⟨hf, sourcePrefix_currentControl_product control0 t⟩
  have haux := measurePreserving_actualRefreshScalarSplit (p := p) t
  have hsplit := hsource.prod haux
  have hreorder := measurePreserving_reorder μc μu μe μx
  let g := fun v : Source p × ErasedAuxiliaryArray (p := p) t =>
    observationFromErasure rate rewards C_star C_h t v
  have hg : Measurable g := measurable_observationFromErasure rate rewards C_star C_h t
  have hobs : MeasurePreserving g (μc.prod μe) ((μc.prod μe).map g) := ⟨hg, rfl⟩
  have hfull := (hobs.prod (MeasurePreserving.id (μu.prod μx))).comp
    (hreorder.comp hsplit)
  have hjoint : (enlargedSourceLaw p).map (fun za =>
        (observationAt rate rewards C_star C_h control0 t.val za,
          (ReferenceSourceCurrentControlFreshness.u_t p t za.1, za.2 (t, 1)))) =
      ((μc.prod μe).map g).prod (calendarInnovationLaw p) := by
    convert hfull.map_eq using 1
    congr 1
    funext za
    apply Prod.ext
    · exact (observationFromErasure_actual rate rewards C_star C_h control0 t za).symm
    · exact Prod.ext rfl (split_scalar t za.2).symm
    rfl
  have hu : Measurable (fun za : EnlargedSource p =>
      (ReferenceSourceCurrentControlFreshness.u_t p t za.1, za.2 (t, 1))) :=
    ((ReferenceSourceCurrentControlFreshness.measurable_u_t t).comp measurable_fst).prodMk
      ((measurable_pi_apply (t, 1)).comp measurable_snd)
  have hmarg := congrArg Measure.fst hjoint
  rw [Measure.fst_map_prodMk
      (measurable_observationAt rate rewards C_star C_h control0 t)
      hu, Measure.fst_prod] at hmarg
  rw [hmarg]
  exact hjoint

/-- Bounded Borel observation tests are integrable against every transition
measure, including transitions from states outside the original law's support. -/
public theorem integrable_calendarTransitionKernel_test (rate : RateInput p)
    (rewards : RewardTable p) (C_star C_h : ℝ) (t : Fin p.T)
    (Phi : Observation p rate → ℝ) (hPhi : Measurable Phi)
    (B : ℝ) (hB : ∀ w, ‖Phi w‖ ≤ B) (w : Observation p rate) :
    Integrable Phi (calendarTransitionKernel rate rewards C_star C_h t w) :=
  Integrable.of_bound hPhi.aestronglyMeasurable B (Filter.Eventually.of_forall hB)

/-- Integrating a Borel real test against the innovation kernel is Borel. -/
public theorem measurable_calendarTransitionKernel_test (rate : RateInput p)
    (rewards : RewardTable p) (C_star C_h : ℝ) (t : Fin p.T)
    (Phi : Observation p rate → ℝ) (hPhi : Measurable Phi) :
    Measurable (fun w => ∫ y, Phi y ∂calendarTransitionKernel rate rewards C_star C_h t w) := by
  have hf := hPhi.comp (measurable_calendarTransitionSample rate rewards C_star C_h t)
  have heq : (fun w => ∫ y, Phi y ∂calendarTransitionKernel rate rewards C_star C_h t w) =
      fun w => ∫ ux, Phi (calendarTransitionSample rate rewards C_star C_h t (w, ux))
        ∂calendarInnovationLaw p := by
    funext w
    rw [calendarTransitionKernel_apply]
    exact integral_map
      ((measurable_calendarTransitionSample rate rewards C_star C_h t).comp
        measurable_prodMk_left).aemeasurable hPhi.aestronglyMeasurable
  rw [heq]
  exact hf.stronglyMeasurable.integral_prod_right'.measurable

/-- The transition preserves the uniform bound of an arbitrary joint test. -/
public theorem norm_calendarTransitionKernel_test_le (rate : RateInput p)
    (rewards : RewardTable p) (C_star C_h : ℝ) (t : Fin p.T)
    (Phi : Observation p rate → ℝ) (B : ℝ) (hB : ∀ w, ‖Phi w‖ ≤ B)
    (w : Observation p rate) :
    ‖∫ y, Phi y ∂calendarTransitionKernel rate rewards C_star C_h t w‖ ≤ B := by
  simpa only [probReal_univ, mul_one] using
    (norm_integral_le_of_norm_le_const (μ := calendarTransitionKernel rate rewards C_star C_h t w)
      (Filter.Eventually.of_forall hB))

/-- The right-hand side of the all-source successor identity is integrable. -/
public theorem integrable_calendarTransitionKernel_observation_test (rate : RateInput p)
    (rewards : RewardTable p) (C_star C_h : ℝ)
    (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T)
    (Phi : Observation p rate → ℝ) (hPhi : Measurable Phi)
    (B : ℝ) (hB : ∀ w, ‖Phi w‖ ≤ B) :
    Integrable (fun za => ∫ y, Phi y ∂calendarTransitionKernel rate rewards C_star C_h t
      (observationAt rate rewards C_star C_h control0 t.val za)) (enlargedSourceLaw p) := by
  apply Integrable.of_bound
    (((measurable_calendarTransitionKernel_test rate rewards C_star C_h t Phi hPhi).comp
      (measurable_observationAt rate rewards C_star C_h control0 t)).aestronglyMeasurable) B
  exact Filter.Eventually.of_forall fun za =>
    norm_calendarTransitionKernel_test_le rate rewards C_star C_h t Phi B hB
      (observationAt rate rewards C_star C_h control0 t.val za)

/-- The one-step bounded JOINT-test identity on the original whole source
product. The test may use the retained original source, every label-zero
coordinate and every field of every logical cell. No branch law, history or
factorization premise is supplied by the caller. -/
public theorem bounded_joint_test_successor (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T)
    (Phi : Observation p rate → ℝ) (hPhi : Measurable Phi)
    (B : ℝ) (hB : ∀ w, ‖Phi w‖ ≤ B) :
    (∫ za, Phi (observationAt rate rewards C_star C_h control0 (t.val + 1) za)
        ∂enlargedSourceLaw p) =
      ∫ za, (∫ y, Phi y ∂calendarTransitionKernel rate rewards C_star C_h t
        (observationAt rate rewards C_star C_h control0 t.val za)) ∂enlargedSourceLaw p := by
  let θ := observationAt rate rewards C_star C_h control0 t.val
  let fresh := fun za : EnlargedSource p =>
    (ReferenceSourceCurrentControlFreshness.u_t p t za.1, za.2 (t, 1))
  let F := fun v : Observation p rate ×
      (ContinuousLearningRows.TimeControl p × ContinuousControlSlice.Scalar) =>
    Phi (calendarTransitionSample rate rewards C_star C_h t v)
  have hθ : Measurable θ := measurable_observationAt rate rewards C_star C_h control0 t
  have hfresh : Measurable fresh :=
    ((ReferenceSourceCurrentControlFreshness.measurable_u_t t).comp measurable_fst).prodMk
      ((measurable_pi_apply (t, 1)).comp measurable_snd)
  have hF : Measurable F := hPhi.comp
    (measurable_calendarTransitionSample rate rewards C_star C_h t)
  have hFi : Integrable F
      (((enlargedSourceLaw p).map θ).prod (calendarInnovationLaw p)) :=
    Integrable.of_bound hF.aestronglyMeasurable B
      (Filter.Eventually.of_forall fun v => hB
        (calendarTransitionSample rate rewards C_star C_h t v))
  calc
    _ = ∫ za, F (θ za, fresh za) ∂enlargedSourceLaw p := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun za =>
        (congrArg Phi (calendarTransitionSample_actual
          rate rewards C_star C_h control0 t za)).symm
    _ = ∫ v, F v ∂(enlargedSourceLaw p).map (fun za => (θ za, fresh za)) :=
      (integral_map (hθ.prodMk hfresh).aemeasurable hF.aestronglyMeasurable).symm
    _ = ∫ v, F v ∂(((enlargedSourceLaw p).map θ).prod (calendarInnovationLaw p)) := by
      rw [observation_current_innovation_product rate rewards C_star C_h control0 t]
    _ = ∫ w, (∫ ux, F (w, ux) ∂calendarInnovationLaw p)
        ∂(enlargedSourceLaw p).map θ := integral_prod F hFi
    _ = ∫ za, (∫ ux, F (θ za, ux) ∂calendarInnovationLaw p) ∂enlargedSourceLaw p :=
      integral_map hθ.aemeasurable
        hF.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with za
      rw [calendarTransitionKernel_apply]
      exact (integral_map
        ((measurable_calendarTransitionSample rate rewards C_star C_h t).comp
          measurable_prodMk_left).aemeasurable hPhi.aestronglyMeasurable).symm

/-- The actual local residual producer. Its gate is PRE overflow, followed
by the physical proposal; a detecting POST overflow does not suppress refresh. -/
public def logicalCellResidualLaw (rate : RateInput p) (r : Record rate)
    (cell : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell r)
    (state : RecordedQueueRun.RunState p.K) : Measure (SlowSet p) :=
  if state.overflow then Measure.dirac (frozenSlowSet p) else
    if FollowerCutoffScan.completeRowProposalBit p rate.eta.val r.input.row r.input.time then
      (RecordedSlowRefresh.residualPMF p
        (ReferenceFirstLaunchNumericalCell.queueParameters rate) state cell.input
        cell.selected.view.payload.anchor cell.selected.view.payload.anchor_pos).toMeasure
    else Measure.dirac cell.selected.view.payload.slowSet

instance logicalCellResidualLaw_probability (rate : RateInput p) (r : Record rate)
    (cell : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell r)
    (state : RecordedQueueRun.RunState p.K) :
    IsProbabilityMeasure (logicalCellResidualLaw rate r cell state) := by
  unfold logicalCellResidualLaw
  split <;> infer_instance

private theorem measurable_fixed_residualDraw (rate : RateInput p)
    (state : RecordedQueueRun.RunState p.K) (round : RecordedQueueRun.RoundInput p.K)
    (anchor : Fin p.K → ℝ) (hanchor : ∀ i, 0 < anchor i) :
    Measurable (residualDraw rate state round anchor hanchor) := by
  have hm := ReferenceFirstLiveChronologicalPrefixMeasurability.measurable_residualDraw_of_measurable_residualMass
    rate (fun _ => state) (fun _ => round) (fun _ => anchor) (fun _ => hanchor)
    id measurable_id (fun _ => measurable_const)
  exact hm.mono le_rfl le_top

/-- The local scalar sampler has the true residual PMF, including zero atoms. -/
public theorem residualDraw_map (rate : RateInput p)
    (state : RecordedQueueRun.RunState p.K) (round : RecordedQueueRun.RoundInput p.K)
    (anchor : Fin p.K → ℝ) (hanchor : ∀ i, 0 < anchor i) :
    scalarLaw.map (residualDraw rate state round anchor hanchor) =
      (RecordedSlowRefresh.residualPMF p
        (ReferenceFirstLaunchNumericalCell.queueParameters rate) state round anchor hanchor).toMeasure := by
  let masses := fun k => RecordedSlowRefresh.residualMass p
    (ReferenceFirstLaunchNumericalCell.queueParameters rate) state round anchor hanchor
    (slowSetEnumeration p k)
  have hsum : ∑ k, masses k = 1 := by
    dsimp only [masses]
    rw [Equiv.sum_comp]
    exact RecordedSlowRefresh.residualMass_sum_eq_one p _ _ _ _ _
  apply Measure.ext_of_singleton
  intro U
  rw [Measure.map_apply (measurable_fixed_residualDraw rate state round anchor hanchor)
    (measurableSet_singleton U), PMF.toMeasure_apply_singleton _ U (measurableSet_singleton U),
    RecordedSlowRefresh.residualPMF_apply]
  have hfibre : residualDraw rate state round anchor hanchor ⁻¹' {U} =
      ContinuousCategorical.sample (slowSet_card_pos p) masses hsum ⁻¹'
        {(slowSetEnumeration p).symm U} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, residualDraw, masses]
    exact ((slowSetEnumeration p).eq_symm_apply).symm
  rw [hfibre]
  change ContinuousCategorical.uniform
    (ContinuousCategorical.sample (slowSet_card_pos p) masses hsum ⁻¹'
      {(slowSetEnumeration p).symm U}) = _
  simpa only [Equiv.apply_symm_apply] using
    ContinuousCategorical.uniform_sample_singleton (slowSet_card_pos p)
    (fun k => RecordedSlowRefresh.residualMass_nonneg p _ _ _ _ _ (slowSetEnumeration p k))
    hsum ((slowSetEnumeration p).symm U)

/-- Changing the residual outcome changes only `nextSlowSet`. The complete
original physical, numerical, all-arm service, queue and proposal fields stay. -/
public def logicalCellWithNext (rate : RateInput p) (r : Record rate)
    (cell : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell r)
    (state : RecordedQueueRun.RunState p.K) (U : SlowSet p) : Cell p rate :=
  { appendLogicalCell r cell state auxiliarySection with nextSlowSet := U }

public theorem logicalCellWithNext_beforeRefresh (rate : RateInput p) (r : Record rate)
    (cell : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell r)
    (state : RecordedQueueRun.RunState p.K) (U : SlowSet p) :
    (logicalCellWithNext rate r cell state U).beforeRefreshFields =
      (appendLogicalCell r cell state auxiliarySection).beforeRefreshFields := rfl

/-- The local innovation is exactly a complete-cell append from the actual
residual measure, with the frozen and retained-set dirac branches included. -/
public theorem appendLogicalCell_residual_law (rate : RateInput p) (r : Record rate)
    (cell : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell r)
    (state : RecordedQueueRun.RunState p.K) :
    scalarLaw.map (fun x => appendLogicalCell r cell state (innovationAuxiliary r.input.time x)) =
      (logicalCellResidualLaw rate r cell state).map (logicalCellWithNext rate r cell state) := by
  have he : Measurable (logicalCellWithNext rate r cell state) := measurable_of_countable _
  cases hs : state.overflow with
  | true =>
      have hleft : (fun x => appendLogicalCell r cell state
          (innovationAuxiliary r.input.time x)) = fun _ =>
            logicalCellWithNext rate r cell state (frozenSlowSet p) := by
        funext x
        simp only [appendLogicalCell, logicalCellWithNext, hs, Bool.not_true,
          Bool.false_and, ite_true]
      rw [hleft]
      simp only [logicalCellResidualLaw, hs, ite_true, Measure.map_const,
        measure_univ, one_smul, Measure.map_dirac' he]
  | false =>
      cases hp : FollowerCutoffScan.completeRowProposalBit p rate.eta.val r.input.row r.input.time with
      | false =>
          have hleft : (fun x => appendLogicalCell r cell state
              (innovationAuxiliary r.input.time x)) = fun _ =>
                logicalCellWithNext rate r cell state cell.selected.view.payload.slowSet := by
            funext x
            simp only [appendLogicalCell, logicalCellWithNext, hs, hp, Bool.not_false,
              Bool.true_and, Bool.false_eq_true, ite_false]
          rw [hleft]
          simp only [logicalCellResidualLaw, hs, hp, Bool.false_eq_true, ite_false,
            Measure.map_const, measure_univ, one_smul, Measure.map_dirac' he]
      | true =>
          have hleft : (fun x => appendLogicalCell r cell state
              (innovationAuxiliary r.input.time x)) =
              (logicalCellWithNext rate r cell state) ∘
                residualDraw rate state cell.input cell.selected.view.payload.anchor
                  cell.selected.view.payload.anchor_pos := by
            funext x
            simp only [Function.comp_def, appendLogicalCell, logicalCellWithNext, hs, hp,
              Bool.not_false, Bool.true_and, Bool.false_eq_true, ite_false, ite_true,
              innovationAuxiliary, Function.update_self]
          rw [hleft, ← Measure.map_map he (measurable_fixed_residualDraw rate state cell.input
            cell.selected.view.payload.anchor cell.selected.view.payload.anchor_pos), residualDraw_map]
          simp only [logicalCellResidualLaw, hs, hp, Bool.false_eq_true, ite_false, ite_true]

/-- Actual first-LIVE calendar membership, excluding the PRE physical cutoff
and retaining birth, positive pending and empty-pending dates. -/
public def currentCellGate (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T) (z : Source p) : Bool :=
  Sum.elim (fun _ => false) (fun _ => true)
    (currentCellTag rate rewards C_star C_h t (z, auxiliarySection))

public theorem measurable_currentCellGate (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T) :
    Measurable (currentCellGate rate rewards C_star C_h t) :=
  (measurable_const.sumElim measurable_const).comp
    ((measurable_currentCellTag rate rewards C_star C_h t).comp
      (measurable_id.prodMk measurable_const))

/-- Exact membership characterization in the original physical window. -/
public theorem currentCellGate_iff (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T) (z : Source p) :
    currentCellGate rate rewards C_star C_h t z = true ↔
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h ≤ t.val ∧
      t.val - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h <
        (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow rate rewards C_star C_h z).length := by
  rw [currentCellGate, currentCellTag_eq_lookup]
  split
  · rename_i hs
    simp only [hs, true_and]
    let path := firstLiveChronologicalPrefix rate rewards C_star C_h (z, auxiliarySection)
    let k := t.val - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
    have hlen := firstLiveChronologicalPrefix_length rate rewards C_star C_h (z, auxiliarySection)
    change path.length = _ at hlen
    change (Sum.elim (fun _ => false) (fun _ => true)
      (ReferenceActiveHorizonMeasurability.listObservationAt path k)) = true ↔ _
    by_cases hk : k < path.length
    · rw [ReferenceActiveHorizonMeasurability.listObservationAt, List.getElem?_eq_getElem hk]
      simp only [Sum.elim_inr, true_iff]
      simpa only [hlen, ReferenceFirstLiveOverflowReadout.wholeFirstLiveLength] using hk
    · rw [ReferenceActiveHorizonMeasurability.listObservationAt, List.getElem?_eq_none (by omega)]
      simp only [Sum.elim_inl, Bool.false_eq_true, false_iff]
      simpa only [hlen, ReferenceFirstLiveOverflowReadout.wholeFirstLiveLength] using hk
  · rename_i hs
    simp only [Sum.elim_inl, Bool.false_eq_true, hs, false_and]

private theorem currentCellGate_false_of_not_launch (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T) (z : Source p)
    (hz : ¬ actualLaunchBy rate rewards C_star C_h t.val z) :
    currentCellGate rate rewards C_star C_h t z = false := by
  apply Bool.eq_false_iff.mpr
  intro hg
  obtain ⟨hs, hk⟩ := (currentCellGate_iff rate rewards C_star C_h t z).mp hg
  have hc : (ReferenceCompletePhysicalHistory.generatedBoundary rate z rewards C_star C_h).crossing =
      none := by
    cases h : (ReferenceCompletePhysicalHistory.generatedBoundary rate z rewards C_star C_h).crossing
    · rfl
    · exact False.elim (hz ⟨by simp only [h, Option.isSome_some], hs⟩)
  have hw := (ReferenceFirstLiveOverflowReadout.wholeFirstLive_no_launch
    rate rewards C_star C_h z hc).1
  rw [hw] at hk
  exact Nat.not_lt_zero _ hk

private theorem sourcePrefix_replace_current (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) (z : Source p) (u : ContinuousLearningRows.TimeControl p) :
    sourcePrefix control0 t.val (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z u) =
      sourcePrefix control0 t.val z := by
  open ReferenceFixedTimeSourceControlCoupling in
  apply Prod.ext
  · refine Prod.ext rfl ?_
    funext q
    by_cases hq : q = ActualInitializationPhysicalStep.selectedRowIndex p z
    · subst q
      simp only [sourcePrefix, replaceSourceControl, sourceCoordinatorIndex,
        ActualInitializationPhysicalStep.selectedRowIndex, Function.update_self]
      refine Prod.ext rfl ?_
      funext v
      by_cases hv : v.val < t.val
      · have hvt : v ≠ t := by intro h; subst v; exact (Nat.lt_irrefl _) hv
        simp only [hv, ite_true, Function.update_of_ne hvt]
      · simp only [hv, ite_false]
    · have hq' : q ≠ sourceCoordinatorIndex p z := hq
      simp only [sourcePrefix, replaceSourceControl, sourceCoordinatorIndex,
        ActualInitializationPhysicalStep.selectedRowIndex] at hq hq' ⊢
      rw [Function.update_of_ne hq, Function.update_of_ne hq, Function.update_of_ne hq]
  · rfl

/-- Actual calendar membership is unchanged by arbitrary current full-control
insertion. The positive-date case consumes the accepted continuing/empty
partition on the SAME source stratum, rather than assuming a history match. -/
public theorem currentCellGate_replace_current (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) (z : Source p) (u : ContinuousLearningRows.TimeControl p) :
    currentCellGate rate rewards C_star C_h t
      (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z u) =
        currentCellGate rate rewards C_star C_h t z := by
  classical
  let z' := ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z u
  have hp : sourcePrefix control0 t.val z' = sourcePrefix control0 t.val z :=
    sourcePrefix_replace_current control0 t z u
  have hl : actualLaunchBy rate rewards C_star C_h t.val z' ↔
      actualLaunchBy rate rewards C_star C_h t.val z := by
    rw [actualLaunchBy_factor rate rewards C_star C_h control0 t.val (Nat.le_of_lt t.isLt) z',
      actualLaunchBy_factor rate rewards C_star C_h control0 t.val (Nat.le_of_lt t.isLt) z, hp]
  by_cases hz : actualLaunchBy rate rewards C_star C_h t.val z
  · have hz' := hl.mpr hz
    have hs := (sourcePrefix_preserves_actual_launch rate rewards C_star C_h control0 t.val
      (Nat.le_of_lt t.isLt) z hz).1
    have hs' := (sourcePrefix_preserves_actual_launch rate rewards C_star C_h control0 t.val
      (Nat.le_of_lt t.isLt) z' hz').1
    rw [hp] at hs'
    have hstart : ReferenceCompletePhysicalHistory.physicalStart rate z' rewards C_star C_h =
        ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h := hs'.trans hs.symm
    apply Bool.eq_iff_iff.mpr
    rw [currentCellGate_iff, currentCellGate_iff, hstart]
    by_cases he : t.val = ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
    · have hb := ReferenceFirstLiveSourcePhasePartition.source_birth_window_pos
        rate rewards C_star C_h t control0 z ⟨hz.1, he⟩
      have hb' := ReferenceFirstLiveSourcePhasePartition.source_birth_window_pos
        rate rewards C_star C_h t control0 z' ⟨hz'.1, he.trans hstart.symm⟩
      simp only [he, Nat.sub_self, le_refl, true_and]
      exact iff_of_true hb' hb
    · let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
      let q := BootstrapPrivateRoundStreams.sourceCoordinatorIndex p z
      let i := ReferenceFirstLiveRecordingSourceCylinder.stratumIndex q t s hz.2
      let Z := ReferenceTotalSourceDisintegration.SourceStratum rate rewards C_star C_h t i
      let left : Z := ⟨z, rfl, hz.1, rfl⟩
      let right : Z := ⟨z', rfl, hz'.1, hstart⟩
      have hret : ReferenceFirstLiveRecordingSourceCylinder.sourceRetained
          rate rewards C_star C_h q t s hz.2 control0 left =
          ReferenceFirstLiveRecordingSourceCylinder.sourceRetained
            rate rewards C_star C_h q t s hz.2 control0 right := by
        apply Subtype.ext
        rw [ReferenceFirstLiveRecordingSourceCylinder.sourceRetained,
          ReferenceTotalSourceDisintegration.sourceRetainedInput_val,
          ReferenceFirstLiveRecordingSourceCylinder.sourceRetained,
          ReferenceTotalSourceDisintegration.sourceRetainedInput_val]
        have hr := ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_replaceSourceControl
          p q t z u rfl
        have h := congrArg (fun v =>
          (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t v).2) hr
        rw [MeasurableEquiv.apply_symm_apply] at h
        exact h
      have hleft := ReferenceFirstLiveSourcePhasePartition.source_positive_cell_iff_branches
        rate rewards C_star C_h q t s hz.2 control0 left
      have hright := ReferenceFirstLiveSourcePhasePartition.source_positive_cell_iff_branches
        rate rewards C_star C_h q t s hz.2 control0 right
      rw [hret] at hleft
      have hpos : 0 < t.val - s := by
        have hle := hz.2
        dsimp only [s]
        omega
      have hw := hright.trans hleft.symm
      simpa only [left, right, hpos, true_and, hz.2] using hw
  · rw [currentCellGate_false_of_not_launch rate rewards C_star C_h t z hz,
      currentCellGate_false_of_not_launch rate rewards C_star C_h t z' (fun h => hz (hl.mp h))]

/-- The actual cell gate factors through the strictly prior retained source. -/
public theorem currentCellGate_sourcePrefix (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) (z : Source p) :
    currentCellGate rate rewards C_star C_h t z =
      currentCellGate rate rewards C_star C_h t (sourcePrefix control0 t.val z) := by
  change Sum.elim _ _ (currentCellTag rate rewards C_star C_h t (z, auxiliarySection)) = _
  rw [currentCellTag_sourcePrefix rate rewards C_star C_h control0]
  change currentCellGate rate rewards C_star C_h t (sourcePrefix control0 (t.val + 1) z) = _
  rw [prefix_successor_restore control0 t z,
    currentCellGate_replace_current rate rewards C_star C_h control0]

/-- The exact source-characterized domain of a present current calendar cell. -/
abbrev LiveCalendarSource (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T) :=
  {z : Source p // currentCellGate rate rewards C_star C_h t z = true}

/-- The actual current position, computed from launch and proved membership. -/
public def liveCalendarIndex (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T)
    (z : LiveCalendarSource rate rewards C_star C_h t) :
    Fin (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow rate rewards C_star C_h z.val).length :=
  ⟨t.val - ReferenceCompletePhysicalHistory.physicalStart rate z.val rewards C_star C_h,
    ((currentCellGate_iff rate rewards C_star C_h t z.val).mp z.property).2⟩

/-- The complete current cell on its actual source domain. -/
public def liveCalendarEntry (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T)
    (z : LiveCalendarSource rate rewards C_star C_h t) (a : AuxiliaryArray p) : Cell p rate :=
  let k := liveCalendarIndex rate rewards C_star C_h t z
  (firstLiveChronologicalPrefix rate rewards C_star C_h (z.val, a))[k.val]'(by
    rw [firstLiveChronologicalPrefix_length]; exact k.isLt)

public theorem currentCellTag_live (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T)
    (z : LiveCalendarSource rate rewards C_star C_h t) (a : AuxiliaryArray p) :
    currentCellTag rate rewards C_star C_h t (z.val, a) =
      Sum.inr (liveCalendarEntry rate rewards C_star C_h t z a) := by
  rw [currentCellTag_eq_lookup, ite_eq_left
    ((currentCellGate_iff rate rewards C_star C_h t z.val).mp z.property).1]
  let k := liveCalendarIndex rate rewards C_star C_h t z
  have hk : k.val < (firstLiveChronologicalPrefix rate rewards C_star C_h (z.val, a)).length := by
    simpa only [firstLiveChronologicalPrefix_length,
      ReferenceFirstLiveOverflowReadout.wholeFirstLiveLength] using k.isLt
  change ReferenceActiveHorizonMeasurability.listObservationAt _ k.val = _
  simp only [ReferenceActiveHorizonMeasurability.listObservationAt, List.getElem?_eq_getElem hk]
  rfl

public theorem measurable_liveCalendarEntry (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T) :
    Measurable (fun v : LiveCalendarSource rate rewards C_star C_h t × AuxiliaryArray p =>
      liveCalendarEntry rate rewards C_star C_h t v.1 v.2) := by
  have hinr : MeasurableEmbedding (@Sum.inr Unit (Cell p rate)) :=
    ⟨Sum.inr_injective, measurable_inr, fun _ hs => hs.inr_image⟩
  apply hinr.measurable_comp_iff.mp
  have hm : Measurable (fun v : LiveCalendarSource rate rewards C_star C_h t × AuxiliaryArray p =>
      currentCellTag rate rewards C_star C_h t (v.1.val, v.2)) :=
    (measurable_currentCellTag rate rewards C_star C_h t).comp
    ((measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd)
  simpa only [currentCellTag_live, Function.comp_def] using hm

/-- The actual source-derived residual measure, using the same whole-window
cell, zero-origin strict-PRE state and physical anchor as the chronological scan. -/
public def liveCalendarResidualLaw (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T)
    (z : LiveCalendarSource rate rewards C_star C_h t) : Measure (SlowSet p) :=
  let k := liveCalendarIndex rate rewards C_star C_h t z
  let r := (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
    rate rewards C_star C_h z.val)[k.val]
  logicalCellResidualLaw rate r
    (wholeLiveCell rate rewards C_star C_h z.val r (List.getElem_mem k.isLt))
    (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate)
      ((ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells
        rate rewards C_star C_h z.val).take k.val))

instance liveCalendarResidualLaw_probability (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T)
    (z : LiveCalendarSource rate rewards C_star C_h t) :
    IsProbabilityMeasure (liveCalendarResidualLaw rate rewards C_star C_h t z) := by
  unfold liveCalendarResidualLaw
  infer_instance

/-- Keep every actual before-refresh field and change only the next set. -/
public def liveCalendarCellWithNext (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T)
    (z : LiveCalendarSource rate rewards C_star C_h t) (U : SlowSet p) : Cell p rate :=
  { liveCalendarEntry rate rewards C_star C_h t z auxiliarySection with nextSlowSet := U }

/-- The SAME innovation used by the transition kernel is the explicit actual
residual measure, keeping all complete before-refresh fields. -/
public theorem liveCalendarEntry_residual_law (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T)
    (z : LiveCalendarSource rate rewards C_star C_h t) :
    scalarLaw.map (fun x => liveCalendarEntry rate rewards C_star C_h t z (innovationAuxiliary t x)) =
      (liveCalendarResidualLaw rate rewards C_star C_h t z).map
        (liveCalendarCellWithNext rate rewards C_star C_h t z) := by
  let k := liveCalendarIndex rate rewards C_star C_h t z
  let r := (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow rate rewards C_star C_h z.val)[k.val]
  have ht : r.input.time = t := by
    apply Fin.ext
    have htime := (wholeLiveCell_geometry rate rewards C_star C_h z.val k).2.2.1
    have hs := ((currentCellGate_iff rate rewards C_star C_h t z.val).mp z.property).1
    change r.input.time.val =
      ReferenceCompletePhysicalHistory.physicalStart rate z.val rewards C_star C_h + k.val at htime
    dsimp only [k, liveCalendarIndex] at htime
    omega
  have h := appendLogicalCell_residual_law rate r
    (wholeLiveCell rate rewards C_star C_h z.val r (List.getElem_mem k.isLt))
    (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate)
      ((ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells rate rewards C_star C_h z.val).take k.val))
  rw [ht] at h
  unfold liveCalendarCellWithNext
  simp only [liveCalendarEntry, firstLiveChronologicalPrefix_get, liveCalendarResidualLaw]
  unfold logicalCellWithNext at h
  exact h

/-- An absent actual cell remains absent for every auxiliary array. -/
public theorem currentCellTag_absent (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T) (z : Source p)
    (hz : currentCellGate rate rewards C_star C_h t z ≠ true) (a : AuxiliaryArray p) :
    currentCellTag rate rewards C_star C_h t (z, a) = Sum.inl () := by
  rw [currentCellTag_eq_lookup]
  split
  · rename_i hs
    have hk : (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
        rate rewards C_star C_h z).length ≤
        t.val - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h := by
      apply Nat.le_of_not_gt
      intro h
      exact hz ((currentCellGate_iff rate rewards C_star C_h t z).mpr ⟨hs, h⟩)
    have hp : (firstLiveChronologicalPrefix rate rewards C_star C_h (z, a)).length ≤
        t.val - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h := by
      simpa only [firstLiveChronologicalPrefix_length,
        ReferenceFirstLiveOverflowReadout.wholeFirstLiveLength] using hk
    simp only [ReferenceActiveHorizonMeasurability.listObservationAt, List.getElem?_eq_none hp]
  · rfl

/-- Complete before-refresh fields of the residual cell are the actual fields
for every original auxiliary array, including the detecting overflow update. -/
public theorem liveCalendarCellWithNext_beforeRefresh (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T)
    (z : LiveCalendarSource rate rewards C_star C_h t) (a : AuxiliaryArray p) (U : SlowSet p) :
    (liveCalendarCellWithNext rate rewards C_star C_h t z U).beforeRefreshFields =
      (liveCalendarEntry rate rewards C_star C_h t z a).beforeRefreshFields := by
  simp only [liveCalendarCellWithNext, liveCalendarEntry, firstLiveChronologicalPrefix_get,
    LogicalCell.beforeRefreshFields, appendLogicalCell]

private theorem liveCalendar_residual_integral (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T) (z : LiveCalendarSource rate rewards C_star C_h t)
    (G : Cell p rate → ℝ) (hG : Measurable G) :
    (∫ x, G (liveCalendarEntry rate rewards C_star C_h t z (innovationAuxiliary t x)) ∂scalarLaw) =
      ∫ U, G (liveCalendarCellWithNext rate rewards C_star C_h t z U)
        ∂liveCalendarResidualLaw rate rewards C_star C_h t z := by
  let sample := fun x => liveCalendarEntry rate rewards C_star C_h t z (innovationAuxiliary t x)
  have hpair : Measurable (fun x : ContinuousControlSlice.Scalar =>
      (z, innovationAuxiliary t x)) :=
    measurable_const.prodMk (measurable_innovationAuxiliary t)
  have hs : Measurable sample :=
    (measurable_liveCalendarEntry rate rewards C_star C_h t).comp hpair
  calc
    _ = ∫ e, G e ∂scalarLaw.map sample := (integral_map hs.aemeasurable hG.aestronglyMeasurable).symm
    _ = ∫ e, G e ∂(liveCalendarResidualLaw rate rewards C_star C_h t z).map
        (liveCalendarCellWithNext rate rewards C_star C_h t z) := by
      rw [liveCalendarEntry_residual_law]
    _ = _ := integral_map (measurable_of_countable _).aemeasurable hG.aestronglyMeasurable

/-- The explicit raw-control/residual formula for the SAME transition kernel.
The gate uses the retained pre-choice source; all original control coordinates
are inserted on both branches. The inner residual is the actual frozen dirac,
true residual PMF, or retained-set dirac, in that order. -/
public theorem calendarTransitionKernel_residual_formula (rate : RateInput p)
    (rewards : RewardTable p) (C_star C_h : ℝ)
    (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T)
    (Phi : Observation p rate → ℝ) (hPhi : Measurable Phi)
    (B : ℝ) (hB : ∀ w, ‖Phi w‖ ≤ B) (w : Observation p rate) :
    (∫ y, Phi y ∂calendarTransitionKernel rate rewards C_star C_h t w) =
      ∫ u, (if hg : currentCellGate rate rewards C_star C_h t w.1 = true then
        let z : LiveCalendarSource rate rewards C_star C_h t :=
          ⟨ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t w.1 u,
            (currentCellGate_replace_current rate rewards C_star C_h control0 t w.1 u).trans hg⟩
        ∫ U, Phi (z.val, (w.2.1, w.2.2 ++
          [liveCalendarCellWithNext rate rewards C_star C_h t z U]))
          ∂liveCalendarResidualLaw rate rewards C_star C_h t z
      else Phi (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t w.1 u,
        (w.2.1, w.2.2))) ∂ContinuousLearningRows.timeControlLaw p := by
  let F := fun ux : ContinuousLearningRows.TimeControl p × ContinuousControlSlice.Scalar =>
    Phi (calendarTransitionSample rate rewards C_star C_h t (w, ux))
  have hF : Measurable F := hPhi.comp
    ((measurable_calendarTransitionSample rate rewards C_star C_h t).comp measurable_prodMk_left)
  have hFi : Integrable F (calendarInnovationLaw p) :=
    Integrable.of_bound hF.aestronglyMeasurable B
      (Filter.Eventually.of_forall fun ux => hB (calendarTransitionSample rate rewards C_star C_h t (w, ux)))
  have hsample : Measurable (fun ux : ContinuousLearningRows.TimeControl p × ContinuousControlSlice.Scalar =>
      calendarTransitionSample rate rewards C_star C_h t (w, ux)) :=
    (measurable_calendarTransitionSample rate rewards C_star C_h t).comp measurable_prodMk_left
  rw [calendarTransitionKernel_apply, integral_map hsample.aemeasurable hPhi.aestronglyMeasurable]
  change (∫ ux, F ux ∂calendarInnovationLaw p) = _
  rw [calendarInnovationLaw, integral_prod F hFi]
  apply integral_congr_ae
  filter_upwards with u
  by_cases hg : currentCellGate rate rewards C_star C_h t w.1 = true
  · rw [dite_eq_left hg]
    let z : LiveCalendarSource rate rewards C_star C_h t :=
      ⟨ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t w.1 u,
        (currentCellGate_replace_current rate rewards C_star C_h control0 t w.1 u).trans hg⟩
    let G := fun e : Cell p rate => Phi (z.val, (w.2.1, w.2.2 ++ [e]))
    have hG : Measurable G := hPhi.comp
      (measurable_const.prodMk (measurable_const.prodMk
        (measurable_append_singleton.comp (measurable_const.prodMk measurable_id))))
    have heq : (fun x => F (u, x)) = fun x =>
        G (liveCalendarEntry rate rewards C_star C_h t z (innovationAuxiliary t x)) := by
      funext x
      change Phi (_, (_, appendCurrentTag _
        (currentCellTag rate rewards C_star C_h t (z.val, innovationAuxiliary t x)))) = _
      rw [currentCellTag_live]
      rfl
    rw [heq]
    exact liveCalendar_residual_integral rate rewards C_star C_h t z G hG
  · rw [dite_eq_right hg]
    have hz : currentCellGate rate rewards C_star C_h t
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t w.1 u) ≠ true := by
      rw [currentCellGate_replace_current rate rewards C_star C_h control0]
      exact hg
    have heq : (fun x => F (u, x)) = fun _ : ContinuousControlSlice.Scalar =>
        Phi (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t w.1 u, (w.2.1, w.2.2)) := by
      funext x
      simp only [F, calendarTransitionSample, currentCellTag_absent rate rewards C_star C_h t _ hz,
        appendCurrentTag]
    rw [heq, integral_const, probReal_univ, one_smul]

/-- The local scalar entry on the exact present-source carrier. -/
public def liveCalendarScalarEntry (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T)
    (v : LiveCalendarSource rate rewards C_star C_h t × ContinuousControlSlice.Scalar) : Cell p rate :=
  liveCalendarEntry rate rewards C_star C_h t v.1 (innovationAuxiliary (p := p) t v.2)

private theorem measurable_liveCalendarScalarEntry (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T) :
    Measurable (liveCalendarScalarEntry rate rewards C_star C_h t) := by
  change Measurable ((fun v : LiveCalendarSource rate rewards C_star C_h t × AuxiliaryArray p =>
      liveCalendarEntry rate rewards C_star C_h t v.1 v.2) ∘
    fun v : LiveCalendarSource rate rewards C_star C_h t × ContinuousControlSlice.Scalar =>
      (v.1, innovationAuxiliary (p := p) t v.2))
  have hpair : Measurable (fun v : LiveCalendarSource rate rewards C_star C_h t ×
      ContinuousControlSlice.Scalar => (v.1, innovationAuxiliary (p := p) t v.2)) :=
    measurable_fst.prodMk ((measurable_innovationAuxiliary (p := p) t).comp measurable_snd)
  exact (measurable_liveCalendarEntry rate rewards C_star C_h t).comp hpair

public theorem measurable_liveCalendarNext (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T) :
    Measurable ((LogicalCell.nextSlowSet (p := p) (rate := rate)) ∘
      liveCalendarScalarEntry rate rewards C_star C_h t) := by
  have hnext : Measurable (fun e : Cell p rate => e.nextSlowSet) :=
    (ReferenceFirstLiveChronologicalPrefixMeasurability.measurable_logicalCell_nextSlowSet
      (p := p) (rate := rate)).mono le_rfl le_top
  exact hnext.comp (measurable_liveCalendarScalarEntry rate rewards C_star C_h t)

/-- Scalar representation of the explicit residual, proved from its actual
complete-cell law rather than imposed as the definition of that residual. -/
public theorem liveCalendarResidualLaw_eq_map_next (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T) (z : LiveCalendarSource rate rewards C_star C_h t) :
    liveCalendarResidualLaw rate rewards C_star C_h t z = scalarLaw.map (fun x =>
      (liveCalendarEntry rate rewards C_star C_h t z (innovationAuxiliary (p := p) t x)).nextSlowSet) := by
  have hnext : Measurable (fun e : Cell p rate => e.nextSlowSet) :=
    (ReferenceFirstLiveChronologicalPrefixMeasurability.measurable_logicalCell_nextSlowSet
      (p := p) (rate := rate)).mono le_rfl le_top
  have hpair : Measurable (fun x : ContinuousControlSlice.Scalar => (z, innovationAuxiliary (p := p) t x)) :=
    measurable_const.prodMk (measurable_innovationAuxiliary (p := p) t)
  have hs : Measurable (fun x : ContinuousControlSlice.Scalar =>
      liveCalendarEntry rate rewards C_star C_h t z (innovationAuxiliary (p := p) t x)) :=
    (measurable_liveCalendarEntry rate rewards C_star C_h t).comp hpair
  have h := congrArg (fun μ : Measure (Cell p rate) => μ.map (fun e => e.nextSlowSet))
    (liveCalendarEntry_residual_law rate rewards C_star C_h t z)
  rw [Measure.map_map hnext hs, Measure.map_map hnext (measurable_of_countable _)] at h
  change scalarLaw.map (fun x =>
    (liveCalendarEntry rate rewards C_star C_h t z (innovationAuxiliary (p := p) t x)).nextSlowSet) =
      (liveCalendarResidualLaw rate rewards C_star C_h t z).map id at h
  rw [Measure.map_id] at h
  exact h.symm

/-- The explicit actual residual measures form a Borel probability kernel
on the exact present-cell source carrier; there is no off-domain slow-set choice. -/
public def liveCalendarResidualKernel (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T) :
    ProbabilityTheory.Kernel (LiveCalendarSource rate rewards C_star C_h t) (SlowSet p) :=
  ProbabilityTheory.Kernel.mapOfMeasurable
    (ProbabilityTheory.Kernel.prod ProbabilityTheory.Kernel.id
      (ProbabilityTheory.Kernel.const (LiveCalendarSource rate rewards C_star C_h t) scalarLaw))
    ((LogicalCell.nextSlowSet (p := p) (rate := rate)) ∘
      liveCalendarScalarEntry rate rewards C_star C_h t)
    (measurable_liveCalendarNext rate rewards C_star C_h t)

instance liveCalendarResidualKernel_markov (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T) :
    ProbabilityTheory.IsMarkovKernel (liveCalendarResidualKernel rate rewards C_star C_h t) := by
  unfold liveCalendarResidualKernel
  rw [ProbabilityTheory.Kernel.mapOfMeasurable_eq_map]
  exact ProbabilityTheory.Kernel.IsMarkovKernel.map _
    (measurable_liveCalendarNext rate rewards C_star C_h t)

/-- The Borel residual kernel is exactly the explicit actual branch measure. -/
public theorem liveCalendarResidualKernel_apply (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T) (z : LiveCalendarSource rate rewards C_star C_h t) :
    liveCalendarResidualKernel rate rewards C_star C_h t z =
      liveCalendarResidualLaw rate rewards C_star C_h t z := by
  change (((ProbabilityTheory.Kernel.prod ProbabilityTheory.Kernel.id
    (ProbabilityTheory.Kernel.const (LiveCalendarSource rate rewards C_star C_h t) scalarLaw)) z).map
      ((LogicalCell.nextSlowSet (p := p) (rate := rate)) ∘
        liveCalendarScalarEntry rate rewards C_star C_h t)) = _
  rw [ProbabilityTheory.Kernel.prod_apply, ProbabilityTheory.Kernel.id_apply,
    ProbabilityTheory.Kernel.const_apply, Measure.dirac_prod,
    Measure.map_map (measurable_liveCalendarNext rate rewards C_star C_h t) measurable_prodMk_left]
  exact (liveCalendarResidualLaw_eq_map_next rate rewards C_star C_h t z).symm

end Bandits.Support.ReferenceFirstLiveCalendarMarkedTransition

end
