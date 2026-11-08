/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveCanonicalProposalJointLaw
public import Bandits.Support.ReferenceFirstLiveChronologicalPrefixMeasurability
public import Bandits.Support.ReferenceFirstLiveChronologicalPrefixCausality

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.Tactic

/-!
# Complete-past recorder and reserved FAST law on first-LIVE branches

For the positive-offset continuing and empty-pending original-source
restrictions, this module retains the complete chronological calendar past,
the tagged same-source remainder, the current affine family, the entire
independent auxiliary array, and the computed strict-past numerical readout.
The current physical slice remains the tested output together with the
correlated recorder/reserved-FAST pair.

Sources: `sources/zip4/manuscript/06_interruptions.tex:381-397`,
`sources/zip4/manuscript/04_slow_fast_learner.tex:142-215,323-366`, and
`sources/zip4/manuscript/08_main_theorem.tex:78-109`.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace Bandits.Support.ReferenceFirstLivePastPairKernelTransport

open ReferenceFirstLiveCanonicalProposalJointLaw
open ReferenceFirstLiveChronologicalPrefixFoundation
open ReferenceFirstLiveChronologicalPrefixCausality
open ReferenceFirstLiveChronologicalPrefixMeasurability
open ReferenceFirstLivePostUpdateProposalLaw

variable {p : ConstructorDimensions.Parameters}

abbrev RateInput := ReferenceFirstLiveCanonicalProposalJointLaw.RateInput
abbrev RewardTable := ReferenceFirstLiveCanonicalProposalJointLaw.RewardTable
abbrev SourceInput := ReferenceFirstLiveChronologicalPrefixFoundation.SourceInput
abbrev AuxiliaryArray := ReferenceFirstLiveChronologicalPrefixFoundation.AuxiliaryArray
abbrev LiveRemainder (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (q : Fin (ConstructorDimensions.M p)) (t : Fin p.T)
    (s : ℕ) (hs : s ≤ t.val) (control0 : ContinuousLearningRows.TimeControl p) :=
  ReferenceFirstLivePostUpdateProposalLaw.LiveRemainder
    rate rewards C_star C_h q t s hs control0

variable (rate : RateInput p) (rewards : RewardTable p)
  (C_star C_h : ℝ) (q : Fin (ConstructorDimensions.M p)) (t : Fin p.T)
  (s : ℕ) (hs : s ≤ t.val) (control0 : ContinuousLearningRows.TimeControl p)

abbrev NumericalPast :=
  (Fin p.K → ℕ × ℕ) × (Bool × (Fin p.K → List (Bool × ℕ)))

abbrev RecorderFastPair := Option (Fin p.K) × Option (Fin p.K)

abbrev PastObservation :=
  (List (LogicalCell p rate) × LiveRemainder rate rewards C_star C_h q t s hs control0) ×
    (ContinuousLearningRows.AffineSamples p ×
      (AuxiliaryArray p × NumericalPast (p := p)))

abbrev PastObservationPair := PastObservation rate rewards C_star C_h q t s hs control0 ×
  RecorderFastPair (p := p)

abbrev PastPairBase :=
  ((LiveRemainder rate rewards C_star C_h q t s hs control0 ×
      ContinuousLearningRows.AffineSamples p) × RecorderFastPair (p := p))

private abbrev FixedRemainder :=
  ReferenceFirstLiveRecordingReadoutMeasurability.SourceX
    rate rewards C_star C_h q t s hs control0

private abbrev SourcePlus :=
  ReferenceFirstLiveRecordingSourceCylinder.SourcePlus
    rate rewards C_star C_h q t s hs control0

private abbrev EmptySource :=
  ReferenceFirstLiveEmptyPendingMarkerLaw.Zempty
    rate rewards C_star C_h q t s hs control0

/-- The source point obtained by restoring the fixed baseline current
control to the same retained original-source remainder. -/
public def canonicalRestoredSource
    (x : LiveRemainder rate rewards C_star C_h q t s hs control0) : SourceInput p :=
  (ReferenceFirstLiveRecordingSourceCylinder.sourceRecover
    rate rewards C_star C_h q t s hs control0
    (liveRetained rate rewards C_star C_h q t s hs control0 x, control0)).val

/-- The actual calendar-past value obtained by restoring the given whole
current control to the unchanged source remainder. -/
public def restoredCalendarPast
    (x : LiveRemainder rate rewards C_star C_h q t s hs control0)
    (u : ContinuousLearningRows.TimeControl p) (aux : AuxiliaryArray p) :
    List (LogicalCell p rate) :=
  calendarPast rate rewards C_star C_h
    ((ReferenceFirstLiveRecordingSourceCylinder.sourceRecover
      rate rewards C_star C_h q t s hs control0
      (liveRetained rate rewards C_star C_h q t s hs control0 x, u)).val, aux) t.val

/-- The Borel complete-past observation used for arbitrary tests. It retains
the tagged source remainder, the entire current affine family, all auxiliary
coordinates, and the exact computed PRE numerical state. -/
public def recorderFastPastObservation
    (input : LiveRemainder rate rewards C_star C_h q t s hs control0 ×
      (ContinuousLearningRows.AffineSamples p × AuxiliaryArray p)) :
    ((List (LogicalCell p rate) × LiveRemainder rate rewards C_star C_h q t s hs control0) ×
      (ContinuousLearningRows.AffineSamples p ×
        (AuxiliaryArray p × NumericalPast (p := p)))) :=
  let x := input.1
  let family := input.2.1
  let aux := input.2.2
  ((calendarPast rate rewards C_star C_h
      (canonicalRestoredSource rate rewards C_star C_h q t s hs control0 x, aux) t.val, x),
    (family, (aux, liveNumericalPast rate rewards C_star C_h q t s hs control0 x)))

/-- The same observation evaluated at a restored, whole original current
control. -/
public def recorderFastPastObservationAtControl
    (input : LiveRemainder rate rewards C_star C_h q t s hs control0 ×
      (ContinuousLearningRows.TimeControl p × AuxiliaryArray p)) :
    ((List (LogicalCell p rate) × LiveRemainder rate rewards C_star C_h q t s hs control0) ×
      (ContinuousLearningRows.AffineSamples p ×
        (AuxiliaryArray p × NumericalPast (p := p)))) :=
  let x := input.1
  let u := input.2.1
  let aux := input.2.2
  ((restoredCalendarPast rate rewards C_star C_h q t s hs control0 x u aux, x),
    (u.2, (aux, liveNumericalPast rate rewards C_star C_h q t s hs control0 x)))

/-- The actual source calendar past is invariant under replacement of the
entire current physical slice when the same remainder, affine family and
auxiliary array are retained. -/
public theorem restoredCalendarPast_control_independent
    (x : LiveRemainder rate rewards C_star C_h q t s hs control0)
    (u v : ContinuousLearningRows.TimeControl p) (aux : AuxiliaryArray p) :
    restoredCalendarPast rate rewards C_star C_h q t s hs control0 x u aux =
      restoredCalendarPast rate rewards C_star C_h q t s hs control0 x v aux := by
  let left := ReferenceFirstLiveRecordingSourceCylinder.sourceRecover
    rate rewards C_star C_h q t s hs control0
    (liveRetained rate rewards C_star C_h q t s hs control0 x, u)
  let right := ReferenceFirstLiveRecordingSourceCylinder.sourceRecover
    rate rewards C_star C_h q t s hs control0
    (liveRetained rate rewards C_star C_h q t s hs control0 x, v)
  have hprefix : ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val left.val =
      ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val right.val := by
    let rem := (liveRetained rate rewards C_star C_h q t s hs control0 x).val
    have hleftSelected :
        ActualInitializationPhysicalStep.selectedRowIndex p left.val = q := left.property.1
    have hrightSelected :
        ActualInitializationPhysicalStep.selectedRowIndex p right.val = q := right.property.1
    have hleftId : left.val.1.1 = rem.1.1 :=
      ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_symm_id p q t u rem
    have hrightId : right.val.1.1 = rem.1.1 :=
      ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_symm_id p q t v rem
    have hleftPrivate : left.val.2 = rem.2 :=
      ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_symm_private p q t u rem
    have hrightPrivate : right.val.2 = rem.2 :=
      ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_symm_private p q t v rem
    apply Prod.ext
    · apply Prod.ext
      · exact hleftId.trans hrightId.symm
      · funext j
        by_cases hj : j = q
        · subst j
          apply Prod.ext
          · have hleftForward :
                ((ReferenceSourcePrefixHistoryFiltration.sourcePrefix
                  control0 t.val left.val).1.2 q).1 = rem.1.2.1.1 := by
              exact (ReferenceSourcePrefixHistoryFiltration.sourcePrefix_forward
                control0 t.val left.val q).trans
                (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_symm_forward
                  p q t u rem)
            have hrightForward :
                ((ReferenceSourcePrefixHistoryFiltration.sourcePrefix
                  control0 t.val right.val).1.2 q).1 = rem.1.2.1.1 := by
              exact (ReferenceSourcePrefixHistoryFiltration.sourcePrefix_forward
                control0 t.val right.val q).trans
                (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_symm_forward
                  p q t v rem)
            exact hleftForward.trans hrightForward.symm
          · funext w
            have hleftControl :
                ((ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val left.val).1.2 q).2 w =
                  if w.val < t.val then (left.val.1.2 q).2 w else control0 := by
              have h := ReferenceSourcePrefixHistoryFiltration.sourcePrefix_control
                control0 t.val left.val w
              simpa only [hleftSelected] using h
            have hrightControl :
                ((ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val right.val).1.2 q).2 w =
                  if w.val < t.val then (right.val.1.2 q).2 w else control0 := by
              have h := ReferenceSourcePrefixHistoryFiltration.sourcePrefix_control
                control0 t.val right.val w
              simpa only [hrightSelected] using h
            rw [hleftControl, hrightControl]
            by_cases hw : w.val < t.val
            · simp only [ite_eq_left hw]
              have hwne : w ≠ t := by
                intro h
                have hval := congrArg Fin.val h
                omega
              have hleftBefore : (left.val.1.2 q).2 w =
                  rem.1.2.1.2 ⟨w, hwne⟩ := by
                change ((((ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t).symm
                  (u, rem)).1.2 q).2 w) = rem.1.2.1.2 ⟨w, hwne⟩
                exact ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_symm_otherTime
                  p q t u rem ⟨w, hwne⟩
              have hrightBefore : (right.val.1.2 q).2 w =
                  rem.1.2.1.2 ⟨w, hwne⟩ := by
                change ((((ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t).symm
                  (v, rem)).1.2 q).2 w) = rem.1.2.1.2 ⟨w, hwne⟩
                exact ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_symm_otherTime
                  p q t v rem ⟨w, hwne⟩
              exact hleftBefore.trans hrightBefore.symm
            · simp only [hw, ↓reduceIte]
        · have hleftOther : j ≠ ActualInitializationPhysicalStep.selectedRowIndex p left.val := by
            simpa only [hleftSelected] using hj
          have hrightOther : j ≠ ActualInitializationPhysicalStep.selectedRowIndex p right.val := by
            simpa only [hrightSelected] using hj
          have hleftPrefix := ReferenceSourcePrefixHistoryFiltration.sourcePrefix_otherRow
            control0 t.val left.val j hleftOther
          have hrightPrefix := ReferenceSourcePrefixHistoryFiltration.sourcePrefix_otherRow
            control0 t.val right.val j hrightOther
          have hleftRow : left.val.1.2 j = rem.1.2.2 ⟨j, hj⟩ := by
            change (((ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t).symm
              (u, rem)).1.2 j) = rem.1.2.2 ⟨j, hj⟩
            exact ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_symm_otherRow
              p q t u rem ⟨j, hj⟩
          have hrightRow : right.val.1.2 j = rem.1.2.2 ⟨j, hj⟩ := by
            change (((ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t).symm
              (v, rem)).1.2 j) = rem.1.2.2 ⟨j, hj⟩
            exact ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_symm_otherRow
              p q t v rem ⟨j, hj⟩
          exact hleftPrefix.trans
            (hleftRow.trans (hrightRow.symm.trans hrightPrefix.symm))
    · calc
        _ = left.val.2 :=
          ReferenceSourcePrefixHistoryFiltration.sourcePrefix_private control0 t.val left.val
        _ = rem.2 := hleftPrivate
        _ = right.val.2 := hrightPrivate.symm
        _ = _ :=
          (ReferenceSourcePrefixHistoryFiltration.sourcePrefix_private control0 t.val right.val).symm
  change calendarPast rate rewards C_star C_h (left.val, aux) t.val =
    calendarPast rate rewards C_star C_h (right.val, aux) t.val
  rw [calendarPast_sourcePrefix rate rewards C_star C_h control0 t.val
        (Nat.le_of_lt t.isLt) left.val aux,
      calendarPast_sourcePrefix rate rewards C_star C_h control0 t.val
        (Nat.le_of_lt t.isLt) right.val aux,
      hprefix]

private theorem measurable_list_take_variable
    {α : Type*} [MeasurableSpace α] {X : Type*} [MeasurableSpace X]
    (records : X → List α) (hrecords : Measurable records)
    (count : X → ℕ) (hcount : Measurable count) :
    Measurable (fun x => (records x).take (count x)) := by
  have hc :=
    (ReferenceActiveHorizonMeasurability.measurable_listObservationCoordinates
      (α := α)).comp hrecords
  apply measurable_comap_iff.mpr
  change Measurable (fun x =>
    (((records x).take (count x)).length,
      fun j => ReferenceActiveHorizonMeasurability.listObservationAt
        ((records x).take (count x)) j))
  simp only [List.length_take]
  have hlength : Measurable (fun x => min (count x) (records x).length) :=
    (measurable_of_countable (fun z : ℕ × ℕ => min z.1 z.2)).comp
      (hcount.prodMk (measurable_fst.comp hc))
  apply hlength.prodMk
  apply measurable_pi_iff.mpr
  intro j
  have hbefore : MeasurableSet {x | j < count x} := measurableSet_lt measurable_const hcount
  apply measurable_of_restrict_of_restrict_compl hbefore
  · have htag := (measurable_pi_apply j).comp (measurable_snd.comp hc)
    have heq : ({x | j < count x}.domRestrict
        (fun x => ReferenceActiveHorizonMeasurability.listObservationAt (records x) j)) =
        (fun x : {x | j < count x} =>
          ReferenceActiveHorizonMeasurability.listObservationAt
            ((records x).take (count x)) j) := by
      funext x
      have hx : j < count x.val := by
        simpa only [Set.mem_ofPred_eq] using x.property
      simp only [Set.domRestrict, ReferenceActiveHorizonMeasurability.listObservationAt,
        List.getElem?_take, ite_eq_left hx]
    change Measurable (fun x : {x | j < count x} =>
      ReferenceActiveHorizonMeasurability.listObservationAt
        ((records x).take (count x)) j)
    rw [← heq]
    exact htag.comp measurable_subtype_coe
  · have heq : (fun x : ↥{x | ¬ j < count x} =>
        ReferenceActiveHorizonMeasurability.listObservationAt
          ((records x.val).take (count x.val)) j) = fun _ => (Sum.inl () : Unit ⊕ α) := by
      funext x
      simp only [ReferenceActiveHorizonMeasurability.listObservationAt,
        List.getElem?_take]
      rw [ite_eq_right x.property]
    change Measurable (fun x : ↥{x | ¬ j < count x} =>
      ReferenceActiveHorizonMeasurability.listObservationAt
        ((records x.val).take (count x.val)) j)
    rw [heq]
    exact measurable_const

/-- The complete calendar-past list is Borel in the original source and
auxiliary array, using the accepted full-path measurability and actual
calendar cutoff. -/
private theorem measurable_calendarPast_local :
    Measurable (fun z : SourceInput p × AuxiliaryArray p =>
      calendarPast rate rewards C_star C_h z t.val) := by
  have hpath :=
    measurable_firstLiveChronologicalPrefix rate rewards C_star C_h
  have hstart : Measurable (fun z : SourceInput p × AuxiliaryArray p =>
      ReferenceCompletePhysicalHistory.physicalStart rate z.1 rewards C_star C_h) :=
    (ReferenceCompleteSuffixInputMeasurability.measurable_physicalStart
      rate rewards C_star C_h).comp measurable_fst
  have hcount : Measurable (fun z : SourceInput p × AuxiliaryArray p =>
      t.val - ReferenceCompletePhysicalHistory.physicalStart rate z.1 rewards C_star C_h) :=
    (measurable_of_countable (fun n : ℕ => t.val - n)).comp hstart
  have hEq : (fun z : SourceInput p × AuxiliaryArray p =>
      calendarPast rate rewards C_star C_h z t.val) =
      (fun z => (firstLiveChronologicalPrefix rate rewards C_star C_h z).take
        (t.val - ReferenceCompletePhysicalHistory.physicalStart rate z.1 rewards C_star C_h)) := by
    funext z
    exact calendarPast_eq_take_elapsed rate rewards C_star C_h z.1 z.2 t.val
  rw [hEq]
  exact measurable_list_take_variable
    (firstLiveChronologicalPrefix rate rewards C_star C_h) hpath _ hcount

public theorem measurable_recorderFastPastObservation :
    Measurable (recorderFastPastObservation rate rewards C_star C_h q t s hs control0) := by
  let source := canonicalRestoredSource rate rewards C_star C_h q t s hs control0
  have hsource : Measurable source := by
    exact (measurable_subtype_coe.comp
      (ReferenceFirstLiveRecordingSourceCylinder.measurable_sourceRecover
        rate rewards C_star C_h q t s hs control0)).comp
      ((measurable_liveRetained rate rewards C_star C_h q t s hs control0).prodMk
        measurable_const)
  have hpast : Measurable (fun xa : LiveRemainder rate rewards C_star C_h q t s hs control0 ×
      AuxiliaryArray p =>
        calendarPast rate rewards C_star C_h (source xa.1, xa.2) t.val) := by
    exact (measurable_calendarPast_local rate rewards C_star C_h t).comp
      ((hsource.comp measurable_fst).prodMk measurable_snd)
  have hnum : Measurable (liveNumericalPast rate rewards C_star C_h q t s hs control0) :=
    measurable_liveNumericalPast rate rewards C_star C_h q t s hs control0
  change Measurable (fun xa : LiveRemainder rate rewards C_star C_h q t s hs control0 ×
      (ContinuousLearningRows.AffineSamples p × AuxiliaryArray p) => _)
  exact ((hpast.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd))).prodMk
      measurable_fst).prodMk
    ((measurable_fst.comp measurable_snd).prodMk
      ((measurable_snd.comp measurable_snd).prodMk
        (hnum.comp measurable_fst)))

public theorem measurable_recorderFastPastObservationAtControl :
    Measurable (recorderFastPastObservationAtControl
      rate rewards C_star C_h q t s hs control0) := by
  have hpast : Measurable (fun xu : LiveRemainder rate rewards C_star C_h q t s hs control0 ×
      (ContinuousLearningRows.TimeControl p × AuxiliaryArray p) =>
        restoredCalendarPast rate rewards C_star C_h q t s hs control0
          xu.1 xu.2.1 xu.2.2) := by
    let source : Measurable (fun xu : LiveRemainder rate rewards C_star C_h q t s hs control0 ×
        (ContinuousLearningRows.TimeControl p × AuxiliaryArray p) =>
          (ReferenceFirstLiveRecordingSourceCylinder.sourceRecover
            rate rewards C_star C_h q t s hs control0
            (liveRetained rate rewards C_star C_h q t s hs control0 xu.1, xu.2.1)).val) := by
      exact (measurable_subtype_coe.comp
        (ReferenceFirstLiveRecordingSourceCylinder.measurable_sourceRecover
          rate rewards C_star C_h q t s hs control0)).comp
        (((measurable_liveRetained rate rewards C_star C_h q t s hs control0).comp
            measurable_fst).prodMk (measurable_fst.comp measurable_snd))
    exact (measurable_calendarPast_local rate rewards C_star C_h t).comp
      (source.prodMk (measurable_snd.comp measurable_snd))
  have hnum := measurable_liveNumericalPast rate rewards C_star C_h q t s hs control0
  exact (hpast.prodMk measurable_fst).prodMk
    ((measurable_snd.comp (measurable_fst.comp measurable_snd)).prodMk
      ((measurable_snd.comp measurable_snd).prodMk (hnum.comp measurable_fst)))

public theorem recorderFastPastObservation_slice_invariant
    (x : LiveRemainder rate rewards C_star C_h q t s hs control0)
    (slice slice' : CanonicalRecordingSlice.Slice p.m p.K)
    (family : ContinuousLearningRows.AffineSamples p) (aux : AuxiliaryArray p) :
    recorderFastPastObservationAtControl rate rewards C_star C_h q t s hs control0
      (x, ((slice, family), aux)) =
    recorderFastPastObservationAtControl rate rewards C_star C_h q t s hs control0
      (x, ((slice', family), aux)) := by
  simp only [recorderFastPastObservationAtControl]
  rw [restoredCalendarPast_control_independent]

/-- Attach the actual complete-past readout after the accepted joint-pair
pushforward, retaining the source affine family and all auxiliary entries. -/
public def attachPastObservation
    (y : PastPairBase rate rewards C_star C_h q t s hs control0 × AuxiliaryArray p) :
    PastObservationPair rate rewards C_star C_h q t s hs control0 :=
  (recorderFastPastObservation rate rewards C_star C_h q t s hs control0
      (Prod.mk y.1.1.1 (Prod.mk y.1.1.2 y.2)), y.1.2)

public theorem measurable_attachPastObservation :
    Measurable (attachPastObservation rate rewards C_star C_h q t s hs control0) := by
  have hobs := measurable_recorderFastPastObservation rate rewards C_star C_h q t s hs control0
  have hin : Measurable (fun y : PastPairBase rate rewards C_star C_h q t s hs control0 ×
      AuxiliaryArray p => Prod.mk y.1.1.1 (Prod.mk y.1.1.2 y.2)) := by
    fun_prop
  exact (hobs.comp hin).prodMk (measurable_snd.comp measurable_fst)

/-- On a literal continuing source point, the observation's past is the
complete calendar past of that same original source and auxiliary array. -/
public theorem continuingPastObservation_sourcePast
    (z : ReferenceFirstLiveRecordingSourceCylinder.SourcePlus
      rate rewards C_star C_h q t s hs control0)
    (aux : AuxiliaryArray p) :
    (recorderFastPastObservation rate rewards C_star C_h q t s hs control0
      (Prod.mk
        (Sum.inl (ReferenceFirstLiveRecordingSourceCylinder.branchSourceSplit
          rate rewards C_star C_h q t s hs control0 z).1)
        (Prod.mk ((ReferenceFirstLiveRecordingSourceCylinder.branchSourceSplit
          rate rewards C_star C_h q t s hs control0 z).2).2 aux))).1.1 =
      calendarPast rate rewards C_star C_h (z.val, aux) t.val := by
  let split := ReferenceFirstLiveRecordingSourceCylinder.branchSourceSplit
    rate rewards C_star C_h q t s hs control0 z
  let x : LiveRemainder rate rewards C_star C_h q t s hs control0 := .inl split.1
  have hrecover := ReferenceFirstLiveRecordingSourceCylinder.branchSourceSplit_recover
    rate rewards C_star C_h q t s hs control0 z
  have hpast := restoredCalendarPast_control_independent
    rate rewards C_star C_h q t s hs control0 x split.2 control0 aux
  change calendarPast rate rewards C_star C_h
      (canonicalRestoredSource rate rewards C_star C_h q t s hs control0 x, aux) t.val =
    calendarPast rate rewards C_star C_h (z.val, aux) t.val
  rw [← hrecover]
  exact hpast.symm

/-- On a literal empty-pending source point, the observation's past is the
complete calendar past of that same original source and auxiliary array. -/
public theorem emptyPastObservation_sourcePast
    (z : ReferenceFirstLiveEmptyPendingMarkerLaw.Zempty
      rate rewards C_star C_h q t s hs control0)
    (aux : AuxiliaryArray p) :
    (recorderFastPastObservation rate rewards C_star C_h q t s hs control0
      (Prod.mk
        (Sum.inr (ReferenceFirstLiveEmptyPendingMarkerLaw.emptySourceSplit
          rate rewards C_star C_h q t s hs control0 z).1)
        (Prod.mk ((ReferenceFirstLiveEmptyPendingMarkerLaw.emptySourceSplit
          rate rewards C_star C_h q t s hs control0 z).2).2 aux))).1.1 =
      calendarPast rate rewards C_star C_h (z.val, aux) t.val := by
  let split := ReferenceFirstLiveEmptyPendingMarkerLaw.emptySourceSplit
    rate rewards C_star C_h q t s hs control0 z
  let x : LiveRemainder rate rewards C_star C_h q t s hs control0 := .inr split.1
  have hrecover := ReferenceFirstLiveEmptyPendingMarkerLaw.emptySourceSplit_recover
    rate rewards C_star C_h q t s hs control0 z
  have hpast := restoredCalendarPast_control_independent
    rate rewards C_star C_h q t s hs control0 x split.2 control0 aux
  change calendarPast rate rewards C_star C_h
      (canonicalRestoredSource rate rewards C_star C_h q t s hs control0 x, aux) t.val =
    calendarPast rate rewards C_star C_h (z.val, aux) t.val
  rw [← hrecover]
  exact hpast.symm

/-- Producting an accepted original-source pair pushforward with the unchanged
auxiliary-uniform law and postcomposing with the locally derived observation. -/
private theorem attach_auxiliary_product_pushforward
    {Z X : Type*} [MeasurableSpace Z] [MeasurableSpace X]
    (μ : Measure Z) (ν : Measure X)
    (base : Z → PastPairBase rate rewards C_star C_h q t s hs control0)
    (reference : X × ContinuousLearningRows.TimeControl p →
      PastPairBase rate rewards C_star C_h q t s hs control0)
    (hbase : μ.map base =
      (ν.prod (ContinuousLearningRows.timeControlLaw p)).map reference)
    (hbaseMeasurable : Measurable base)
    (actual : Z × AuxiliaryArray p →
      PastObservationPair rate rewards C_star C_h q t s hs control0)
    (hactual : ∀ z aux, actual (z, aux) =
      attachPastObservation rate rewards C_star C_h q t s hs control0 (base z, aux))
    :
    (μ.prod (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p)).map actual =
      (((ν.prod (ContinuousLearningRows.timeControlLaw p)).map reference).prod
        (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p)).map
          (attachPastObservation rate rewards C_star C_h q t s hs control0) := by
  let auxLaw := ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p
  let f := fun za : Z × AuxiliaryArray p => (base za.1, za.2)
  have hf : Measurable f :=
    (hbaseMeasurable.comp measurable_fst).prodMk measurable_snd
  have hprod : (μ.prod auxLaw).map f =
      ((ν.prod (ContinuousLearningRows.timeControlLaw p)).map reference).prod auxLaw := by
    change (μ.prod auxLaw).map (Prod.map base id) = _
    rw [← Measure.map_prod_map μ auxLaw hbaseMeasurable measurable_id,
      Measure.map_id, hbase]
  have hcompose : actual =
      attachPastObservation rate rewards C_star C_h q t s hs control0 ∘ f := by
    funext za
    exact hactual za.1 za.2
  have hattach := measurable_attachPastObservation rate rewards C_star C_h q t s hs control0
  calc
    (μ.prod auxLaw).map actual = ((μ.prod auxLaw).map f).map
        (attachPastObservation rate rewards C_star C_h q t s hs control0) := by
          rw [hcompose]
          exact (Measure.map_map hattach hf).symm
    _ = (((ν.prod (ContinuousLearningRows.timeControlLaw p)).map reference).prod auxLaw).map
        (attachPastObservation rate rewards C_star C_h q t s hs control0) := by rw [hprod]

/-- The actual continuing source and its full auxiliary array, mapped to the
complete-past observation and the same physical recorder/FAST pair. -/
public def continuingPastPairTestMap
    (za : ReferenceFirstLiveRecordingSourceCylinder.SourcePlus
      rate rewards C_star C_h q t s hs control0 × AuxiliaryArray p) :
    PastObservationPair rate rewards C_star C_h q t s hs control0 :=
  let split := ReferenceFirstLiveRecordingSourceCylinder.branchSourceSplit
    rate rewards C_star C_h q t s hs control0 za.1
  let x : LiveRemainder rate rewards C_star C_h q t s hs control0 := .inl split.1
  (recorderFastPastObservation rate rewards C_star C_h q t s hs control0
      (x, (split.2.2, za.2)),
    liveMarkerFastPair rate rewards C_star C_h q t s hs control0 (x, split.2))

private def continuingPastPairBaseMap
    (z : ReferenceFirstLiveRecordingSourceCylinder.SourcePlus
      rate rewards C_star C_h q t s hs control0) :
    PastPairBase rate rewards C_star C_h q t s hs control0 :=
  let split := ReferenceFirstLiveRecordingSourceCylinder.branchSourceSplit
    rate rewards C_star C_h q t s hs control0 z
  let x : LiveRemainder rate rewards C_star C_h q t s hs control0 := .inl split.1
  ((x, split.2.2), liveMarkerFastPair rate rewards C_star C_h q t s hs control0 (x, split.2))

public def continuingPastPairReferenceMap
    (xu : ReferenceFirstLiveRecordingReadoutMeasurability.XPlus
        rate rewards C_star C_h q t s hs control0 × ContinuousLearningRows.TimeControl p) :
    PastPairBase rate rewards C_star C_h q t s hs control0 :=
  let x : LiveRemainder rate rewards C_star C_h q t s hs control0 := .inl xu.1
  ((x, xu.2.2), liveMarkerFastPair rate rewards C_star C_h q t s hs control0
    (x, (xu.2.1, control0.2)))

public theorem measurable_continuingPastPairTestMap :
    Measurable (continuingPastPairTestMap rate rewards C_star C_h q t s hs control0) := by
  let split := ReferenceFirstLiveRecordingSourceCylinder.branchSourceSplit
    rate rewards C_star C_h q t s hs control0
  let tag : ReferenceFirstLiveRecordingReadoutMeasurability.XPlus
      rate rewards C_star C_h q t s hs control0 →
      LiveRemainder rate rewards C_star C_h q t s hs control0 := Sum.inl
  have hsplit := ReferenceFirstLiveRecordingSourceCylinder.measurable_branchSourceSplit
    rate rewards C_star C_h q t s hs control0
  have hbase : Measurable (continuingPastPairBaseMap rate rewards C_star C_h q t s hs control0) := by
    exact ((((measurable_inl.comp measurable_fst).prodMk
      (measurable_snd.comp measurable_snd)).prodMk
      ((measurable_liveMarkerFastPair rate rewards C_star C_h q t s hs control0).comp
        ((measurable_inl.comp measurable_fst).prodMk measurable_snd))).comp hsplit)
  have hmap : continuingPastPairTestMap rate rewards C_star C_h q t s hs control0 =
      fun za => attachPastObservation rate rewards C_star C_h q t s hs control0
        (continuingPastPairBaseMap rate rewards C_star C_h q t s hs control0 za.1, za.2) := by
    funext za
    rfl
  rw [hmap]
  exact (measurable_attachPastObservation rate rewards C_star C_h q t s hs control0).comp
    ((hbase.comp measurable_fst).prodMk measurable_snd)

/-- Exact unnormalized product-measure transport of the actual continuing
source pair, after attaching the locally constructed complete-past test data. -/
public theorem continuingSource_past_pair_pushforward :
    let μ := ReferenceFirstLiveRecordingSourceCylinder.branchSourceMeasure
      rate rewards C_star C_h q t s hs control0
    let ν := ReferenceFirstLiveRecordingSourceCylinder.branchRemainderMeasure
      rate rewards C_star C_h q t s hs control0
    (μ.prod (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p)).map
        (continuingPastPairTestMap rate rewards C_star C_h q t s hs control0) =
      (((ν.prod (ContinuousLearningRows.timeControlLaw p)).map
        (continuingPastPairReferenceMap rate rewards C_star C_h q t s hs control0)).prod
        (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p)).map
          (attachPastObservation rate rewards C_star C_h q t s hs control0) := by
  let μ := ReferenceFirstLiveRecordingSourceCylinder.branchSourceMeasure
    rate rewards C_star C_h q t s hs control0
  let ν := ReferenceFirstLiveRecordingSourceCylinder.branchRemainderMeasure
    rate rewards C_star C_h q t s hs control0
  let split := ReferenceFirstLiveRecordingSourceCylinder.branchSourceSplit
    rate rewards C_star C_h q t s hs control0
  let tag : ReferenceFirstLiveRecordingReadoutMeasurability.XPlus
      rate rewards C_star C_h q t s hs control0 →
      LiveRemainder rate rewards C_star C_h q t s hs control0 := Sum.inl
  let pair := fun xu : ReferenceFirstLiveRecordingReadoutMeasurability.XPlus
      rate rewards C_star C_h q t s hs control0 × ContinuousLearningRows.TimeControl p =>
    liveMarkerFastPair rate rewards C_star C_h q t s hs control0
    (tag xu.1, xu.2)
  let base := continuingPastPairBaseMap rate rewards C_star C_h q t s hs control0
  let reference := continuingPastPairReferenceMap rate rewards C_star C_h q t s hs control0
  have hbase : μ.map base =
      (ν.prod (ContinuousLearningRows.timeControlLaw p)).map reference :=
    continuingSource_pair_affine_pushforward rate rewards C_star C_h q t s hs control0
  have hsplit := ReferenceFirstLiveRecordingSourceCylinder.measurable_branchSourceSplit
    rate rewards C_star C_h q t s hs control0
  have hbaseMeasurable : Measurable base := by
    exact ((((measurable_inl.comp measurable_fst).prodMk
      (measurable_snd.comp measurable_snd)).prodMk
      ((measurable_liveMarkerFastPair rate rewards C_star C_h q t s hs control0).comp
        ((measurable_inl.comp measurable_fst).prodMk measurable_snd))).comp hsplit)
  have hactual : ∀ z aux,
      continuingPastPairTestMap rate rewards C_star C_h q t s hs control0 (z, aux) =
        attachPastObservation rate rewards C_star C_h q t s hs control0 (base z, aux) := by
    intro z aux
    rfl
  exact attach_auxiliary_product_pushforward rate rewards C_star C_h q t s hs control0
    μ ν base reference hbase hbaseMeasurable
    (continuingPastPairTestMap rate rewards C_star C_h q t s hs control0) hactual

/-- The actual empty-pending source and its full auxiliary array, mapped to
the complete-past observation and the same physical recorder/FAST pair. -/
public def emptyPastPairTestMap
    (za : ReferenceFirstLiveEmptyPendingMarkerLaw.Zempty
      rate rewards C_star C_h q t s hs control0 × AuxiliaryArray p) :
    PastObservationPair rate rewards C_star C_h q t s hs control0 :=
  let split := ReferenceFirstLiveEmptyPendingMarkerLaw.emptySourceSplit
    rate rewards C_star C_h q t s hs control0 za.1
  let x : LiveRemainder rate rewards C_star C_h q t s hs control0 := .inr split.1
  (recorderFastPastObservation rate rewards C_star C_h q t s hs control0
      (x, (split.2.2, za.2)),
    liveMarkerFastPair rate rewards C_star C_h q t s hs control0 (x, split.2))

private def emptyPastPairBaseMap
    (z : ReferenceFirstLiveEmptyPendingMarkerLaw.Zempty
      rate rewards C_star C_h q t s hs control0) :
    PastPairBase rate rewards C_star C_h q t s hs control0 :=
  let split := ReferenceFirstLiveEmptyPendingMarkerLaw.emptySourceSplit
    rate rewards C_star C_h q t s hs control0 z
  let x : LiveRemainder rate rewards C_star C_h q t s hs control0 := .inr split.1
  ((x, split.2.2), liveMarkerFastPair rate rewards C_star C_h q t s hs control0 (x, split.2))

public def emptyPastPairReferenceMap
    (xu : ReferenceFirstLiveEmptyPendingMarkerLaw.Xempty
        rate rewards C_star C_h q t s hs control0 × ContinuousLearningRows.TimeControl p) :
    PastPairBase rate rewards C_star C_h q t s hs control0 :=
  let x : LiveRemainder rate rewards C_star C_h q t s hs control0 := .inr xu.1
  ((x, xu.2.2), liveMarkerFastPair rate rewards C_star C_h q t s hs control0
    (x, (xu.2.1, control0.2)))

public theorem measurable_emptyPastPairTestMap :
    Measurable (emptyPastPairTestMap rate rewards C_star C_h q t s hs control0) := by
  let split := ReferenceFirstLiveEmptyPendingMarkerLaw.emptySourceSplit
    rate rewards C_star C_h q t s hs control0
  let tag : ReferenceFirstLiveEmptyPendingMarkerLaw.Xempty
      rate rewards C_star C_h q t s hs control0 →
      LiveRemainder rate rewards C_star C_h q t s hs control0 := Sum.inr
  have hsplit := ReferenceFirstLiveEmptyPendingMarkerLaw.measurable_emptySourceSplit
    rate rewards C_star C_h q t s hs control0
  have hbase : Measurable (emptyPastPairBaseMap rate rewards C_star C_h q t s hs control0) := by
    exact ((((measurable_inr.comp measurable_fst).prodMk
      (measurable_snd.comp measurable_snd)).prodMk
      ((measurable_liveMarkerFastPair rate rewards C_star C_h q t s hs control0).comp
        ((measurable_inr.comp measurable_fst).prodMk measurable_snd))).comp hsplit)
  have hmap : emptyPastPairTestMap rate rewards C_star C_h q t s hs control0 =
      fun za => attachPastObservation rate rewards C_star C_h q t s hs control0
        (emptyPastPairBaseMap rate rewards C_star C_h q t s hs control0 za.1, za.2) := by
    funext za
    rfl
  rw [hmap]
  exact (measurable_attachPastObservation rate rewards C_star C_h q t s hs control0).comp
    ((hbase.comp measurable_fst).prodMk measurable_snd)

/-- Exact unnormalized product-measure transport of the actual empty source
pair, after attaching the locally constructed complete-past test data. -/
public theorem emptySource_past_pair_pushforward :
    let μ := ReferenceFirstLiveEmptyPendingMarkerLaw.muEmpty
      rate rewards C_star C_h q t s hs control0
    let ν := ReferenceFirstLiveEmptyPendingMarkerLaw.nuEmpty
      rate rewards C_star C_h q t s hs control0
    (μ.prod (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p)).map
        (emptyPastPairTestMap rate rewards C_star C_h q t s hs control0) =
      (((ν.prod (ContinuousLearningRows.timeControlLaw p)).map
        (emptyPastPairReferenceMap rate rewards C_star C_h q t s hs control0)).prod
        (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p)).map
          (attachPastObservation rate rewards C_star C_h q t s hs control0) := by
  let μ := ReferenceFirstLiveEmptyPendingMarkerLaw.muEmpty
    rate rewards C_star C_h q t s hs control0
  let ν := ReferenceFirstLiveEmptyPendingMarkerLaw.nuEmpty
    rate rewards C_star C_h q t s hs control0
  let split := ReferenceFirstLiveEmptyPendingMarkerLaw.emptySourceSplit
    rate rewards C_star C_h q t s hs control0
  let tag : ReferenceFirstLiveEmptyPendingMarkerLaw.Xempty
      rate rewards C_star C_h q t s hs control0 →
      LiveRemainder rate rewards C_star C_h q t s hs control0 := Sum.inr
  let pair := fun xu : ReferenceFirstLiveEmptyPendingMarkerLaw.Xempty
      rate rewards C_star C_h q t s hs control0 × ContinuousLearningRows.TimeControl p =>
    liveMarkerFastPair rate rewards C_star C_h q t s hs control0
    (tag xu.1, xu.2)
  let base := emptyPastPairBaseMap rate rewards C_star C_h q t s hs control0
  let reference := emptyPastPairReferenceMap rate rewards C_star C_h q t s hs control0
  have hbase : μ.map base =
      (ν.prod (ContinuousLearningRows.timeControlLaw p)).map reference :=
    emptySource_pair_affine_pushforward rate rewards C_star C_h q t s hs control0
  have hsplit := ReferenceFirstLiveEmptyPendingMarkerLaw.measurable_emptySourceSplit
    rate rewards C_star C_h q t s hs control0
  have hbaseMeasurable : Measurable base := by
    exact ((((measurable_inr.comp measurable_fst).prodMk
      (measurable_snd.comp measurable_snd)).prodMk
      ((measurable_liveMarkerFastPair rate rewards C_star C_h q t s hs control0).comp
        ((measurable_inr.comp measurable_fst).prodMk measurable_snd))).comp hsplit)
  have hactual : ∀ z aux,
      emptyPastPairTestMap rate rewards C_star C_h q t s hs control0 (z, aux) =
        attachPastObservation rate rewards C_star C_h q t s hs control0 (base z, aux) := by
    intro z aux
    rfl
  exact attach_auxiliary_product_pushforward rate rewards C_star C_h q t s hs control0
    μ ν base reference hbase hbaseMeasurable
    (emptyPastPairTestMap rate rewards C_star C_h q t s hs control0) hactual

abbrev SliceKernelInput :=
  LiveRemainder rate rewards C_star C_h q t s hs control0 ×
    ContinuousLearningRows.AffineSamples p

/-- The actual same-remainder slice kernel uses the measurable physical
marker/reserved-FAST pair representative on the original slice. -/
public def actualSlicePairKernel
    (xf : SliceKernelInput rate rewards C_star C_h q t s hs control0) :
    Measure (RecorderFastPair (p := p)) :=
  (ContinuousControlSlice.sliceLaw p.m p.K).map
    (fun slice => liveMarkerFastPair rate rewards C_star C_h q t s hs control0
      (xf.1, (slice, xf.2)))

/-- Every finite atom of the actual slice kernel is Borel in the remainder
and affine family. This is derived from the actual measurable representative. -/
public theorem measurable_actualSlicePairKernel_atom
    (atom : RecorderFastPair (p := p)) :
    Measurable (fun xf : SliceKernelInput rate rewards C_star C_h q t s hs control0 =>
      actualSlicePairKernel rate rewards C_star C_h q t s hs control0 xf {atom}) := by
  let encode := fun y : SliceKernelInput rate rewards C_star C_h q t s hs control0 ×
      CanonicalRecordingSlice.Slice p.m p.K =>
    liveMarkerFastPair rate rewards C_star C_h q t s hs control0
      (y.1.1, (y.2, y.1.2))
  have hencode : Measurable encode := by
    have hinput : Measurable (fun y : SliceKernelInput rate rewards C_star C_h q t s hs control0 ×
        CanonicalRecordingSlice.Slice p.m p.K =>
        Prod.mk y.1.1 (Prod.mk y.2 y.1.2)) := by fun_prop
    exact (measurable_liveMarkerFastPair rate rewards C_star C_h q t s hs control0).comp hinput
  have hatom : MeasurableSet ({atom} : Set (RecorderFastPair (p := p))) :=
    measurableSet_singleton atom
  have hpreimage : MeasurableSet (encode ⁻¹' ({atom} : Set (RecorderFastPair (p := p)))) :=
    hatom.preimage hencode
  have hsection : Measurable (fun xf : SliceKernelInput
      rate rewards C_star C_h q t s hs control0 =>
      (ContinuousControlSlice.sliceLaw p.m p.K)
        (Prod.mk xf ⁻¹' (encode ⁻¹' ({atom} : Set (RecorderFastPair (p := p)))))) :=
    measurable_measure_prodMk_left hpreimage
  have hkernel : (fun xf : SliceKernelInput rate rewards C_star C_h q t s hs control0 =>
      actualSlicePairKernel rate rewards C_star C_h q t s hs control0 xf {atom}) =
      (fun xf => (ContinuousControlSlice.sliceLaw p.m p.K)
        (Prod.mk xf ⁻¹' (encode ⁻¹' ({atom} : Set (RecorderFastPair (p := p)))))) := by
    funext xf
    change (Measure.map (encode ∘ Prod.mk xf)
      (ContinuousControlSlice.sliceLaw p.m p.K)) {atom} = _
    rw [Measure.map_apply (hencode.comp measurable_prodMk_left) hatom]
    rfl
  rw [hkernel]
  exact hsection

/-- On the computed clear PRE event, the actual pair kernel equals the
accepted correlated canonical joint law at the actual ALL-arm numerical
weights and payload anchor. The recorder and FAST marginals, and every pair
atom (including `none` and zero-mass atoms), follow from this joint equality. -/
public theorem liveRemainder_clear_slice_pair_kernel_law
    (x : LiveRemainder rate rewards C_star C_h q t s hs control0)
    (hclear : (liveNumericalPast rate rewards C_star C_h q t s hs control0 x).2.1 = false) :
    let payload := livePayload rate rewards C_star C_h q t s hs control0 x
    let W := liveNumericalWeights rate rewards C_star C_h q t s hs control0 x
    ∃ (hpos : ∀ a, 0 < W a) (hlower : ∀ a, payload.anchor a ≤ W a)
      (hupper : ∀ a, W a ≤ 2 * payload.anchor a)
      (snapshot : ActiveRoundActions.Snapshot payload.assignment),
      actualSlicePairKernel rate rewards C_star C_h q t s hs control0 (x, control0.2) =
        (FastRewardSliceLaw.liveRecordingFastPushforward p rate.eta.val rate.eta.property
          rate.sourceCap payload.anchor W payload.anchor_pos hpos hlower hupper
          payload.assignment snapshot).map retainOptionalFast ∧
      (actualSlicePairKernel rate rewards C_star C_h q t s hs control0
        (x, control0.2)).map Prod.fst =
          (RecordedRoundMoments.recordingOutcomePMF
            (SnapshotRecordingKernel.recordingRates p rate.eta.val rate.eta.property rate.sourceCap
              payload.anchor payload.anchor_pos)).toMeasure ∧
      (actualSlicePairKernel rate rewards C_star C_h q t s hs control0
        (x, control0.2)).map Prod.snd =
          (CanonicalFastSampling.qGammaPMF p rate.eta.val rate.eta.property rate.sourceCap
            payload.anchor W payload.anchor_pos hpos hlower hupper payload.slowSet).toMeasure.map
              (fun arm => some arm.val) ∧
      ∀ marker fast : Option (Fin p.K),
        actualSlicePairKernel rate rewards C_star C_h q t s hs control0
          (x, control0.2) {(marker, fast)} =
        ((FastRewardSliceLaw.liveRecordingFastPushforward p rate.eta.val rate.eta.property
          rate.sourceCap payload.anchor W payload.anchor_pos hpos hlower hupper
          payload.assignment snapshot).map retainOptionalFast) {(marker, fast)} := by
  intro payload W
  obtain ⟨hpos, hlower, hupper, snapshot, _, _, _, hfamily⟩ :=
    liveRemainder_canonical_joint_law rate rewards C_star C_h q t s hs control0 x hclear
  have hpair := hfamily control0.2
  have hfst : (actualSlicePairKernel rate rewards C_star C_h q t s hs control0
      (x, control0.2)).map Prod.fst =
      (RecordedRoundMoments.recordingOutcomePMF
        (SnapshotRecordingKernel.recordingRates p rate.eta.val rate.eta.property rate.sourceCap
          (livePayload rate rewards C_star C_h q t s hs control0 x).anchor
          (livePayload rate rewards C_star C_h q t s hs control0 x).anchor_pos)).toMeasure := by
    calc
      _ = ((FastRewardSliceLaw.liveRecordingFastPushforward p rate.eta.val rate.eta.property
          rate.sourceCap payload.anchor W payload.anchor_pos hpos hlower hupper
          payload.assignment snapshot).map retainOptionalFast).map Prod.fst :=
            congrArg (fun μ : Measure (RecorderFastPair (p := p)) => μ.map Prod.fst) hpair
      _ = (FastRewardSliceLaw.liveRecordingFastPushforward p rate.eta.val rate.eta.property
          rate.sourceCap payload.anchor W payload.anchor_pos hpos hlower hupper
          payload.assignment snapshot).map Prod.fst := by
            rw [Measure.map_map measurable_fst (measurable_of_finite retainOptionalFast)]
            rfl
      _ = _ := FastRewardSliceLaw.liveRecordingFastPushforward_fst p rate.eta.val
        rate.eta.property rate.sourceCap payload.anchor W payload.anchor_pos hpos hlower hupper
        payload.assignment snapshot
  have hfast : (actualSlicePairKernel rate rewards C_star C_h q t s hs control0
      (x, control0.2)).map Prod.snd =
      (CanonicalFastSampling.qGammaPMF p rate.eta.val rate.eta.property rate.sourceCap
        payload.anchor W payload.anchor_pos hpos hlower hupper payload.slowSet).toMeasure.map
          (fun arm => some arm.val) := by
    calc
      _ = ((FastRewardSliceLaw.liveRecordingFastPushforward p rate.eta.val rate.eta.property
          rate.sourceCap payload.anchor W payload.anchor_pos hpos hlower hupper
          payload.assignment snapshot).map retainOptionalFast).map Prod.snd :=
            congrArg (fun μ : Measure (RecorderFastPair (p := p)) => μ.map Prod.snd) hpair
      _ = (FastRewardSliceLaw.liveRecordingFastPushforward p rate.eta.val rate.eta.property
          rate.sourceCap payload.anchor W payload.anchor_pos hpos hlower hupper
          payload.assignment snapshot).map (fun z => some z.2.val) := by
            rw [Measure.map_map measurable_snd (measurable_of_finite retainOptionalFast)]
            rfl
      _ = ((FastRewardSliceLaw.liveRecordingFastPushforward p rate.eta.val rate.eta.property
          rate.sourceCap payload.anchor W payload.anchor_pos hpos hlower hupper
          payload.assignment snapshot).map Prod.snd).map (fun arm => some arm.val) := by
            rw [Measure.map_map (measurable_of_finite (fun arm :
              CanonicalFastSampling.FastArm
                (SnapshotRecordingKernel.assignmentSlowSet p payload.assignment) => some arm.val))
              measurable_snd]
            rfl
      _ = _ := by
        rw [FastRewardSliceLaw.liveRecordingFastPushforward_snd,
          CoordinatorRecorderComplementBridge.assignmentSlowSet_eq_payload payload]
  refine ⟨hpos, hlower, hupper, snapshot, hpair, hfst, hfast, ?_⟩
  intro marker fast
  exact congrArg (fun μ : Measure (RecorderFastPair (p := p)) => μ {(marker, fast)}) hpair

/-- The accepted optional FAST marginal has no mass at `none`; consequently
every recorder atom paired with an absent FAST coordinate has zero mass. -/
public theorem liveRemainder_clear_slice_pair_none_fast_zero
    (x : LiveRemainder rate rewards C_star C_h q t s hs control0)
    (hclear : (liveNumericalPast rate rewards C_star C_h q t s hs control0 x).2.1 = false) :
    (actualSlicePairKernel rate rewards C_star C_h q t s hs control0
      (x, control0.2)).map Prod.snd {none} = 0 ∧
    ∀ marker : Option (Fin p.K),
      actualSlicePairKernel rate rewards C_star C_h q t s hs control0
        (x, control0.2) {(marker, none)} = 0 := by
  let payload := livePayload rate rewards C_star C_h q t s hs control0 x
  let W := liveNumericalWeights rate rewards C_star C_h q t s hs control0 x
  have hlaw := liveRemainder_clear_slice_pair_kernel_law rate rewards C_star C_h q t s hs control0
    x hclear
  dsimp only [payload, W] at hlaw
  obtain ⟨hpos, hlower, hupper, _snapshot, _, _, hfast, _⟩ := hlaw
  have hcanonicalNone :
      (CanonicalFastSampling.qGammaPMF p rate.eta.val rate.eta.property rate.sourceCap
        payload.anchor W payload.anchor_pos hpos hlower hupper payload.slowSet).toMeasure.map
          (fun arm => some arm.val) {none} = 0 := by
    rw [Measure.map_apply (measurable_of_finite (fun arm :
      CanonicalFastSampling.FastArm payload.slowSet => some arm.val))
      (measurableSet_singleton none)]
    simp
  have hnone :
      (actualSlicePairKernel rate rewards C_star C_h q t s hs control0
        (x, control0.2)).map Prod.snd {none} = 0 := by
    rw [hfast]
    exact hcanonicalNone
  refine ⟨hnone, ?_⟩
  intro marker
  let μ := actualSlicePairKernel rate rewards C_star C_h q t s hs control0
    (x, control0.2)
  have hsubset : ({(marker, none)} : Set (RecorderFastPair (p := p))) ⊆
      Prod.snd ⁻¹' {none} := by
    intro pair hp
    rcases Set.mem_singleton_iff.mp hp with rfl
    rfl
  have hpreimage : μ (Prod.snd ⁻¹' {none}) =
      (μ.map Prod.snd) {none} := by
    rw [Measure.map_apply measurable_snd (measurableSet_singleton none)]
  apply le_antisymm
  · calc
      μ {(marker, none)} ≤ μ (Prod.snd ⁻¹' {none}) :=
        measure_mono hsubset
      _ = (μ.map Prod.snd) {none} := hpreimage
      _ = 0 := hnone
  · exact bot_le

/-- A bounded Borel test transports through an exact finite-measure
pushforward, with its integrability discharged on both measures. -/
private theorem bounded_test_integral_transport
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsFiniteMeasure μ]
    (f : α → β) (hf : Measurable f) (hpush : μ.map f = ν)
    (F : β → ℝ) (hF : Measurable F) (C : ℝ) (hC : ∀ y, ‖F y‖ ≤ C) :
    Integrable (fun x => F (f x)) μ ∧ Integrable F ν ∧
      (∫ x, F (f x) ∂μ) = ∫ y, F y ∂ν := by
  have hfinite : IsFiniteMeasure ν := by
    rw [← hpush]
    infer_instance
  let := hfinite
  have htarget : Integrable F ν :=
    Integrable.of_bound hF.aestronglyMeasurable C (Filter.Eventually.of_forall hC)
  have htargetMap : Integrable F (μ.map f) := by rw [hpush]; exact htarget
  have hsource : Integrable (fun x => F (f x)) μ := htargetMap.comp_measurable hf
  have htransport := MeasureTheory.integral_map (μ := μ) (φ := f) hf.aemeasurable
    (f := F) hF.aestronglyMeasurable
  rw [hpush] at htransport
  exact ⟨hsource, htarget, htransport.symm⟩

/-- The actual same-remainder slice kernel with its realized complete-past
observation and full auxiliary array retained as part of the output. -/
public def actualObservedSlicePairKernel
    (xfu : LiveRemainder rate rewards C_star C_h q t s hs control0 ×
      (ContinuousLearningRows.AffineSamples p × AuxiliaryArray p)) :
    Measure (PastObservationPair rate rewards C_star C_h q t s hs control0) :=
  (ContinuousControlSlice.sliceLaw p.m p.K).map
    (fun slice =>
      (recorderFastPastObservation rate rewards C_star C_h q t s hs control0 xfu,
        liveMarkerFastPair rate rewards C_star C_h q t s hs control0
          (xfu.1, (slice, xfu.2.1))))

/-- The full observed kernel is the observation-preserving image of the
accepted correlated canonical joint law on the computed clear PRE event. -/
public theorem liveRemainder_clear_observed_slice_pair_kernel_law
    (xfu : LiveRemainder rate rewards C_star C_h q t s hs control0 ×
      (ContinuousLearningRows.AffineSamples p × AuxiliaryArray p))
    (hclear : (liveNumericalPast rate rewards C_star C_h q t s hs control0 xfu.1).2.1 = false) :
    let payload := livePayload rate rewards C_star C_h q t s hs control0 xfu.1
    let W := liveNumericalWeights rate rewards C_star C_h q t s hs control0 xfu.1
    ∃ (hpos : ∀ a, 0 < W a) (hlower : ∀ a, payload.anchor a ≤ W a)
      (hupper : ∀ a, W a ≤ 2 * payload.anchor a)
      (snapshot : ActiveRoundActions.Snapshot payload.assignment),
      actualObservedSlicePairKernel rate rewards C_star C_h q t s hs control0 xfu =
        (FastRewardSliceLaw.liveRecordingFastPushforward p rate.eta.val rate.eta.property
          rate.sourceCap payload.anchor W payload.anchor_pos hpos hlower hupper
          payload.assignment snapshot).map (fun pair =>
            (recorderFastPastObservation rate rewards C_star C_h q t s hs control0 xfu,
              retainOptionalFast pair)) ∧
      ∀ atom : PastObservationPair rate rewards C_star C_h q t s hs control0,
        actualObservedSlicePairKernel rate rewards C_star C_h q t s hs control0 xfu {atom} =
          ((FastRewardSliceLaw.liveRecordingFastPushforward p rate.eta.val rate.eta.property
            rate.sourceCap payload.anchor W payload.anchor_pos hpos hlower hupper
            payload.assignment snapshot).map (fun pair =>
              (recorderFastPastObservation rate rewards C_star C_h q t s hs control0 xfu,
                retainOptionalFast pair))) {atom} := by
  intro payload W
  obtain ⟨hpos, hlower, hupper, snapshot, _, _, _, hfamily⟩ :=
    liveRemainder_canonical_joint_law rate rewards C_star C_h q t s hs control0 xfu.1 hclear
  let observation := recorderFastPastObservation rate rewards C_star C_h q t s hs control0 xfu
  let promote := fun pair : RecorderFastPair (p := p) => (observation, pair)
  have hpromote : Measurable promote := measurable_const.prodMk measurable_id
  have hpairMeasurable : Measurable (fun slice =>
      liveMarkerFastPair rate rewards C_star C_h q t s hs control0
        (xfu.1, (slice, xfu.2.1))) :=
    (measurable_liveMarkerFastPair rate rewards C_star C_h q t s hs control0).comp
      (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have hpair := hfamily xfu.2.1
  have hkernel : actualObservedSlicePairKernel rate rewards C_star C_h q t s hs control0 xfu =
      ((ContinuousControlSlice.sliceLaw p.m p.K).map
        (fun slice => liveMarkerFastPair rate rewards C_star C_h q t s hs control0
          (xfu.1, (slice, xfu.2.1)))).map promote := by
    simp only [actualObservedSlicePairKernel, observation, promote]
    calc
      _ = (ContinuousControlSlice.sliceLaw p.m p.K).map
          (promote ∘ fun slice => liveMarkerFastPair rate rewards C_star C_h q t s hs control0
            (xfu.1, (slice, xfu.2.1))) := by rfl
      _ = ((ContinuousControlSlice.sliceLaw p.m p.K).map
          (fun slice => liveMarkerFastPair rate rewards C_star C_h q t s hs control0
            (xfu.1, (slice, xfu.2.1)))).map promote :=
        (Measure.map_map hpromote hpairMeasurable).symm
  have hcanonical :
      ((ContinuousControlSlice.sliceLaw p.m p.K).map
        (fun slice => liveMarkerFastPair rate rewards C_star C_h q t s hs control0
          (xfu.1, (slice, xfu.2.1)))).map promote =
        (FastRewardSliceLaw.liveRecordingFastPushforward p rate.eta.val rate.eta.property
          rate.sourceCap payload.anchor W payload.anchor_pos hpos hlower hupper
          payload.assignment snapshot).map (fun pair =>
            (observation, retainOptionalFast pair)) := by
    calc
      _ = ((FastRewardSliceLaw.liveRecordingFastPushforward p rate.eta.val rate.eta.property
          rate.sourceCap payload.anchor W payload.anchor_pos hpos hlower hupper
          payload.assignment snapshot).map retainOptionalFast).map promote := by rw [hpair]
      _ = (FastRewardSliceLaw.liveRecordingFastPushforward p rate.eta.val rate.eta.property
          rate.sourceCap payload.anchor W payload.anchor_pos hpos hlower hupper
          payload.assignment snapshot).map (promote ∘ retainOptionalFast) :=
        Measure.map_map hpromote (measurable_of_finite retainOptionalFast)
      _ = _ := by rfl
  refine ⟨hpos, hlower, hupper, snapshot, hkernel.trans hcanonical, ?_⟩
  intro atom
  exact congrArg (fun μ : Measure (PastObservationPair rate rewards C_star C_h q t s hs control0) =>
    μ {atom}) (hkernel.trans hcanonical)

/-- Every bounded Borel test of the realized full observation and the
correlated recorder/FAST output is integrable under the original slice law,
with the exact unnormalized integral of its canonical observed image. -/
public theorem liveRemainder_clear_bounded_observed_slice_pair_test
    (xfu : LiveRemainder rate rewards C_star C_h q t s hs control0 ×
      (ContinuousLearningRows.AffineSamples p × AuxiliaryArray p))
    (hclear : (liveNumericalPast rate rewards C_star C_h q t s hs control0 xfu.1).2.1 = false)
    (F : PastObservationPair rate rewards C_star C_h q t s hs control0 → ℝ)
    (hF : Measurable F) (C : ℝ) (hC : ∀ y, ‖F y‖ ≤ C) :
    let payload := livePayload rate rewards C_star C_h q t s hs control0 xfu.1
    let W := liveNumericalWeights rate rewards C_star C_h q t s hs control0 xfu.1
    ∃ (hpos : ∀ a, 0 < W a) (hlower : ∀ a, payload.anchor a ≤ W a)
      (hupper : ∀ a, W a ≤ 2 * payload.anchor a)
      (snapshot : ActiveRoundActions.Snapshot payload.assignment),
      Integrable (fun slice => F
        (recorderFastPastObservation rate rewards C_star C_h q t s hs control0 xfu,
          liveMarkerFastPair rate rewards C_star C_h q t s hs control0
            (xfu.1, (slice, xfu.2.1))))
        (ContinuousControlSlice.sliceLaw p.m p.K) ∧
      Integrable F
        ((FastRewardSliceLaw.liveRecordingFastPushforward p rate.eta.val rate.eta.property
          rate.sourceCap payload.anchor W payload.anchor_pos hpos hlower hupper
          payload.assignment snapshot).map (fun pair =>
            (recorderFastPastObservation rate rewards C_star C_h q t s hs control0 xfu,
              retainOptionalFast pair))) ∧
      (∫ slice, F
        (recorderFastPastObservation rate rewards C_star C_h q t s hs control0 xfu,
          liveMarkerFastPair rate rewards C_star C_h q t s hs control0
            (xfu.1, (slice, xfu.2.1))) ∂(ContinuousControlSlice.sliceLaw p.m p.K)) =
      ∫ y, F y ∂((FastRewardSliceLaw.liveRecordingFastPushforward p
          rate.eta.val rate.eta.property rate.sourceCap payload.anchor W payload.anchor_pos
          hpos hlower hupper payload.assignment snapshot).map (fun pair =>
            (recorderFastPastObservation rate rewards C_star C_h q t s hs control0 xfu,
              retainOptionalFast pair))) := by
  intro payload W
  obtain ⟨hpos, hlower, hupper, snapshot, hpush, _⟩ :=
    liveRemainder_clear_observed_slice_pair_kernel_law rate rewards C_star C_h q t s hs control0
      xfu hclear
  let f := fun slice : CanonicalRecordingSlice.Slice p.m p.K =>
    (recorderFastPastObservation rate rewards C_star C_h q t s hs control0 xfu,
      liveMarkerFastPair rate rewards C_star C_h q t s hs control0
        (xfu.1, (slice, xfu.2.1)))
  let ν := (FastRewardSliceLaw.liveRecordingFastPushforward p rate.eta.val rate.eta.property
    rate.sourceCap payload.anchor W payload.anchor_pos hpos hlower hupper payload.assignment snapshot).map
      (fun pair => (recorderFastPastObservation rate rewards C_star C_h q t s hs control0 xfu,
        retainOptionalFast pair))
  have hf : Measurable f :=
    ((measurable_recorderFastPastObservation rate rewards C_star C_h q t s hs control0).comp
        measurable_const).prodMk
      ((measurable_liveMarkerFastPair rate rewards C_star C_h q t s hs control0).comp
        (measurable_const.prodMk (measurable_id.prodMk measurable_const)))
  have hpush' : (ContinuousControlSlice.sliceLaw p.m p.K).map f = ν := by
    simpa only [f, ν, actualObservedSlicePairKernel] using hpush
  have htransport := bounded_test_integral_transport
    (ContinuousControlSlice.sliceLaw p.m p.K) ν f hf hpush' F hF C hC
  refine ⟨hpos, hlower, hupper, snapshot, htransport.1, htransport.2.1, ?_⟩
  simpa only [ν] using htransport.2.2


/-- For every bounded Borel test of the complete past, retained original
remainder, affine family, full auxiliary array, and correlated pair, the
continuing original-source product integral equals its unnormalized
remainder/control reference integral. -/
public theorem continuingSource_bounded_past_pair_test
    (F : PastObservationPair rate rewards C_star C_h q t s hs control0 → ℝ)
    (hF : Measurable F) (C : ℝ) (hC : ∀ y, ‖F y‖ ≤ C) :
    let μ := ReferenceFirstLiveRecordingSourceCylinder.branchSourceMeasure
      rate rewards C_star C_h q t s hs control0
    let ν := ReferenceFirstLiveRecordingSourceCylinder.branchRemainderMeasure
      rate rewards C_star C_h q t s hs control0
    let aux := ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p
    let reference := (((ν.prod (ContinuousLearningRows.timeControlLaw p)).map
      (continuingPastPairReferenceMap rate rewards C_star C_h q t s hs control0)).prod aux).map
        (attachPastObservation rate rewards C_star C_h q t s hs control0)
    Integrable (fun za => F (continuingPastPairTestMap rate rewards C_star C_h q t s hs control0 za))
      (μ.prod aux) ∧ Integrable F reference ∧
      (∫ za, F (continuingPastPairTestMap rate rewards C_star C_h q t s hs control0 za)
        ∂(μ.prod aux)) = ∫ y, F y ∂reference := by
  let μ := ReferenceFirstLiveRecordingSourceCylinder.branchSourceMeasure
    rate rewards C_star C_h q t s hs control0
  let ν := ReferenceFirstLiveRecordingSourceCylinder.branchRemainderMeasure
    rate rewards C_star C_h q t s hs control0
  let aux := ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p
  let reference := (((ν.prod (ContinuousLearningRows.timeControlLaw p)).map
    (continuingPastPairReferenceMap rate rewards C_star C_h q t s hs control0)).prod aux).map
      (attachPastObservation rate rewards C_star C_h q t s hs control0)
  have hpush := continuingSource_past_pair_pushforward rate rewards C_star C_h q t s hs control0
  have hpush' : (μ.prod aux).map
      (continuingPastPairTestMap rate rewards C_star C_h q t s hs control0) = reference := by
    simpa only [μ, ν, aux, reference] using hpush
  exact bounded_test_integral_transport (μ.prod aux) reference
    (continuingPastPairTestMap rate rewards C_star C_h q t s hs control0)
    (measurable_continuingPastPairTestMap rate rewards C_star C_h q t s hs control0)
    hpush' F hF C hC

/-- The corresponding exact unnormalized bounded-test integral for the
distinct empty-pending original-source stratum. -/
public theorem emptySource_bounded_past_pair_test
    (F : PastObservationPair rate rewards C_star C_h q t s hs control0 → ℝ)
    (hF : Measurable F) (C : ℝ) (hC : ∀ y, ‖F y‖ ≤ C) :
    let μ := ReferenceFirstLiveEmptyPendingMarkerLaw.muEmpty
      rate rewards C_star C_h q t s hs control0
    let ν := ReferenceFirstLiveEmptyPendingMarkerLaw.nuEmpty
      rate rewards C_star C_h q t s hs control0
    let aux := ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p
    let reference := (((ν.prod (ContinuousLearningRows.timeControlLaw p)).map
      (emptyPastPairReferenceMap rate rewards C_star C_h q t s hs control0)).prod aux).map
        (attachPastObservation rate rewards C_star C_h q t s hs control0)
    Integrable (fun za => F (emptyPastPairTestMap rate rewards C_star C_h q t s hs control0 za))
      (μ.prod aux) ∧ Integrable F reference ∧
      (∫ za, F (emptyPastPairTestMap rate rewards C_star C_h q t s hs control0 za)
        ∂(μ.prod aux)) = ∫ y, F y ∂reference := by
  let μ := ReferenceFirstLiveEmptyPendingMarkerLaw.muEmpty
    rate rewards C_star C_h q t s hs control0
  let ν := ReferenceFirstLiveEmptyPendingMarkerLaw.nuEmpty
    rate rewards C_star C_h q t s hs control0
  let aux := ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p
  let reference := (((ν.prod (ContinuousLearningRows.timeControlLaw p)).map
    (emptyPastPairReferenceMap rate rewards C_star C_h q t s hs control0)).prod aux).map
      (attachPastObservation rate rewards C_star C_h q t s hs control0)
  have hpush := emptySource_past_pair_pushforward rate rewards C_star C_h q t s hs control0
  have hpush' : (μ.prod aux).map
      (emptyPastPairTestMap rate rewards C_star C_h q t s hs control0) = reference := by
    simpa only [μ, ν, aux, reference] using hpush
  exact bounded_test_integral_transport (μ.prod aux) reference
    (emptyPastPairTestMap rate rewards C_star C_h q t s hs control0)
    (measurable_emptyPastPairTestMap rate rewards C_star C_h q t s hs control0)
    hpush' F hF C hC

/-- Restricting a bounded Borel test to the computed clear-PRE event is
derived from the full source transport. The event is read from the numerical
PRE field of the same complete-past observation. -/
public theorem continuingSource_clear_bounded_past_pair_test
    (F : PastObservationPair rate rewards C_star C_h q t s hs control0 → ℝ)
    (hF : Measurable F) (C : ℝ) (hC : ∀ y, ‖F y‖ ≤ C) :
    let μ := ReferenceFirstLiveRecordingSourceCylinder.branchSourceMeasure
      rate rewards C_star C_h q t s hs control0
    let ν := ReferenceFirstLiveRecordingSourceCylinder.branchRemainderMeasure
      rate rewards C_star C_h q t s hs control0
    let aux := ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p
    let reference := (((ν.prod (ContinuousLearningRows.timeControlLaw p)).map
      (continuingPastPairReferenceMap rate rewards C_star C_h q t s hs control0)).prod aux).map
        (attachPastObservation rate rewards C_star C_h q t s hs control0)
    Integrable (fun za =>
      if (continuingPastPairTestMap rate rewards C_star C_h q t s hs control0 za).1.2.2.2.2.1 = false
      then F (continuingPastPairTestMap rate rewards C_star C_h q t s hs control0 za) else 0)
      (μ.prod aux) ∧
    Integrable (fun y =>
      if y.1.2.2.2.2.1 = false then F y else 0) reference ∧
    (∫ za, (if (continuingPastPairTestMap rate rewards C_star C_h q t s hs control0 za).1.2.2.2.2.1 = false
      then F (continuingPastPairTestMap rate rewards C_star C_h q t s hs control0 za) else 0)
      ∂(μ.prod aux)) =
    ∫ y, (if y.1.2.2.2.2.1 = false then F y else 0) ∂reference := by
  let clear := fun y : PastObservationPair rate rewards C_star C_h q t s hs control0 =>
    y.1.2.2.2.2.1 = false
  let G := fun y => if clear y then F y else 0
  have hbool : Measurable (fun y :
      PastObservationPair rate rewards C_star C_h q t s hs control0 => y.1.2.2.2.2.1) := by
    fun_prop
  have hclear : MeasurableSet {y :
      PastObservationPair rate rewards C_star C_h q t s hs control0 | clear y} :=
    measurableSet_eq_fun hbool measurable_const
  have hG : Measurable G := Measurable.ite hclear hF measurable_const
  have hGbound : ∀ y, ‖G y‖ ≤ C + 1 := by
    intro y
    by_cases hy : clear y
    · simp only [G, hy, ↓reduceIte]
      exact le_trans (hC y) (by linarith)
    · simp only [G, hy, ↓reduceIte, norm_zero]
      have hCnonneg : 0 ≤ C := le_trans (norm_nonneg (F y)) (hC y)
      linarith
  have hsource := continuingSource_bounded_past_pair_test rate rewards C_star C_h q t s hs
    control0 G hG (C + 1) hGbound
  simpa only [G, clear] using hsource

/-- The same internally derived clear-PRE restriction on the distinct
empty-pending source stratum. -/
public theorem emptySource_clear_bounded_past_pair_test
    (F : PastObservationPair rate rewards C_star C_h q t s hs control0 → ℝ)
    (hF : Measurable F) (C : ℝ) (hC : ∀ y, ‖F y‖ ≤ C) :
    let μ := ReferenceFirstLiveEmptyPendingMarkerLaw.muEmpty
      rate rewards C_star C_h q t s hs control0
    let ν := ReferenceFirstLiveEmptyPendingMarkerLaw.nuEmpty
      rate rewards C_star C_h q t s hs control0
    let aux := ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p
    let reference := (((ν.prod (ContinuousLearningRows.timeControlLaw p)).map
      (emptyPastPairReferenceMap rate rewards C_star C_h q t s hs control0)).prod aux).map
        (attachPastObservation rate rewards C_star C_h q t s hs control0)
    Integrable (fun za =>
      if (emptyPastPairTestMap rate rewards C_star C_h q t s hs control0 za).1.2.2.2.2.1 = false
      then F (emptyPastPairTestMap rate rewards C_star C_h q t s hs control0 za) else 0)
      (μ.prod aux) ∧
    Integrable (fun y =>
      if y.1.2.2.2.2.1 = false then F y else 0) reference ∧
    (∫ za, (if (emptyPastPairTestMap rate rewards C_star C_h q t s hs control0 za).1.2.2.2.2.1 = false
      then F (emptyPastPairTestMap rate rewards C_star C_h q t s hs control0 za) else 0)
      ∂(μ.prod aux)) =
    ∫ y, (if y.1.2.2.2.2.1 = false then F y else 0) ∂reference := by
  let clear := fun y : PastObservationPair rate rewards C_star C_h q t s hs control0 =>
    y.1.2.2.2.2.1 = false
  let G := fun y => if clear y then F y else 0
  have hbool : Measurable (fun y :
      PastObservationPair rate rewards C_star C_h q t s hs control0 => y.1.2.2.2.2.1) := by
    fun_prop
  have hclear : MeasurableSet {y :
      PastObservationPair rate rewards C_star C_h q t s hs control0 | clear y} :=
    measurableSet_eq_fun hbool measurable_const
  have hG : Measurable G := Measurable.ite hclear hF measurable_const
  have hGbound : ∀ y, ‖G y‖ ≤ C + 1 := by
    intro y
    by_cases hy : clear y
    · simp only [G, hy, ↓reduceIte]
      exact le_trans (hC y) (by linarith)
    · simp only [G, hy, ↓reduceIte, norm_zero]
      have hCnonneg : 0 ≤ C := le_trans (norm_nonneg (F y)) (hC y)
      linarith
  have hsource := emptySource_bounded_past_pair_test rate rewards C_star C_h q t s hs
    control0 G hG (C + 1) hGbound
  simpa only [G, clear] using hsource

end Bandits.Support.ReferenceFirstLivePastPairKernelTransport

end
