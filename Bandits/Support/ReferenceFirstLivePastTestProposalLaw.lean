/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveChronologicalPrefixMeasurability
public import Bandits.Support.ReferenceFirstLiveChronologicalPrefixCausality
public import Bandits.Support.ReferenceFirstLivePostUpdateProposalLaw

import Mathlib.MeasureTheory.Integral.Prod

/-!
# Complete strict-past tests for the original first-live proposal

The test observation retains the accepted calendar past, the tagged original
remainder, every current nonproposal control, the full independent auxiliary
array, and the actual current pre-proposal readout. The proposal identity is
transported on the original unnormalized source restrictions.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace Bandits.Support.ReferenceFirstLivePastTestProposalLaw

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev RewardTable := ActualInitializationPhysicalStep.GridRewardTable
abbrev TimeControl := ContinuousLearningRows.TimeControl
abbrev SourceInput := BootstrapPrivateRoundStreams.SourceInput
abbrev AuxiliaryArray := ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray

open ReferenceFirstLiveChronologicalPrefixFoundation
open ReferenceFirstLivePostUpdateProposalLaw

variable {p : Parameters} (rate : RateInput p) (rewards : RewardTable p)
  (C_star C_h : ℝ) (q : Fin (ConstructorDimensions.M p)) (t : Fin p.T)
  (s : ℕ) (hs : s ≤ t.val) (control0 : TimeControl p)

private def takeList {α : Type*} (z : ℕ × List α) : List α := z.2.take z.1

private theorem measurable_takeList {α : Type*} [MeasurableSpace α] :
    Measurable (takeList (α := α)) := by
  apply measurable_comap_iff.mpr
  change Measurable (fun z : ℕ × List α =>
    ((z.2.take z.1).length,
      fun k => ReferenceActiveHorizonMeasurability.listObservationAt (z.2.take z.1) k))
  have hcoordinates : Measurable
      (fun z : ℕ × List α =>
        ReferenceActiveHorizonMeasurability.listObservationCoordinates z.2) :=
    ReferenceActiveHorizonMeasurability.measurable_listObservationCoordinates.comp
      measurable_snd
  have hlength : Measurable (fun z : ℕ × List α => (z.2.take z.1).length) := by
    have hmin : Measurable (fun n : ℕ × ℕ => min n.1 n.2) := measurable_of_countable _
    convert hmin.comp
      (measurable_fst.prodMk
        (measurable_fst.comp hcoordinates)) using 1
    funext z
    exact List.length_take
  have hentry (k : ℕ) : Measurable (fun z : ℕ × List α =>
      ReferenceActiveHorizonMeasurability.listObservationAt (z.2.take z.1) k) := by
    have hsource : Measurable (fun z : ℕ × List α =>
        ReferenceActiveHorizonMeasurability.listObservationAt z.2 k) :=
      (measurable_pi_apply k).comp
        (measurable_snd.comp hcoordinates)
    have hcut : MeasurableSet {z : ℕ × List α | k < z.1} :=
      measurableSet_lt measurable_const measurable_fst
    have hpiece : Measurable (fun z : ℕ × List α =>
        if k < z.1 then
          ReferenceActiveHorizonMeasurability.listObservationAt z.2 k
        else (Sum.inl () : Unit ⊕ α)) := hsource.ite hcut measurable_const
    have heq : (fun z : ℕ × List α =>
        ReferenceActiveHorizonMeasurability.listObservationAt (z.2.take z.1) k) =
      fun z => if k < z.1 then
        ReferenceActiveHorizonMeasurability.listObservationAt z.2 k
      else (Sum.inl () : Unit ⊕ α) := by
      funext z
      by_cases hk : k < z.1
      · simp [ReferenceActiveHorizonMeasurability.listObservationAt, hk]
      · simp [ReferenceActiveHorizonMeasurability.listObservationAt, hk]
    rw [heq]
    exact hpiece
  apply hlength.prodMk
  apply measurable_pi_iff.mpr
  intro k
  exact hentry k

/-- The complete accepted calendar past is Borel at every fixed calendar
time. The proof uses the path's measured length and each tagged list index. -/
theorem measurable_calendarPast (n : ℕ) :
    Measurable (ReferenceFirstLiveChronologicalPrefixCausality.calendarPast
      rate rewards C_star C_h · n) := by
  have hpath :=
    ReferenceFirstLiveChronologicalPrefixMeasurability.measurable_firstLiveChronologicalPrefix
      rate rewards C_star C_h
  have hstart : Measurable (fun z : SourceInput p × AuxiliaryArray p =>
      ReferenceCompletePhysicalHistory.physicalStart rate z.1 rewards C_star C_h) :=
    (ReferenceCompleteSuffixInputMeasurability.measurable_physicalStart
      rate rewards C_star C_h).comp measurable_fst
  have hsub : Measurable (fun z : ℕ × ℕ => z.1 - z.2) := measurable_of_countable _
  have hcount : Measurable (fun z : SourceInput p × AuxiliaryArray p =>
      n - ReferenceCompletePhysicalHistory.physicalStart rate z.1 rewards C_star C_h) :=
    hsub.comp (measurable_const.prodMk hstart)
  have hpair : Measurable (fun z : SourceInput p × AuxiliaryArray p =>
      (n - ReferenceCompletePhysicalHistory.physicalStart rate z.1 rewards C_star C_h,
        ReferenceFirstLiveChronologicalPrefixFoundation.firstLiveChronologicalPrefix
          rate rewards C_star C_h z)) := hcount.prodMk hpath
  have htake := measurable_takeList.comp hpair
  have heq : (fun z : SourceInput p × AuxiliaryArray p =>
      ReferenceFirstLiveChronologicalPrefixCausality.calendarPast
        rate rewards C_star C_h z n) =
    fun z => takeList (n - ReferenceCompletePhysicalHistory.physicalStart
      rate z.1 rewards C_star C_h,
      ReferenceFirstLiveChronologicalPrefixFoundation.firstLiveChronologicalPrefix
        rate rewards C_star C_h z) := by
    funext z
    exact (ReferenceFirstLiveChronologicalPrefixCausality.calendarPast_eq_take_elapsed
      rate rewards C_star C_h z.1 z.2 n)
  rw [heq]
  exact htake

abbrev LiveRemainder {p : Parameters} (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (q : Fin (ConstructorDimensions.M p)) (t : Fin p.T)
    (s : ℕ) (hs : s ≤ t.val) (control0 : TimeControl p) :=
  ReferenceFirstLivePostUpdateProposalLaw.LiveRemainder
    rate rewards C_star C_h q t s hs control0
abbrev PropRestControl (p : Parameters) :=
  ReferenceFirstLivePostUpdateProposalLaw.PropRestControl p
abbrev FullReadout (p : Parameters) := Option (Fin p.K) ×
  (Option (Fin p.K) × ReferenceFirstLivePostUpdateProposalLaw.NumericalUpdateFields p)
abbrev PastTestObservation {p : Parameters} (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (q : Fin (ConstructorDimensions.M p)) (t : Fin p.T)
    (s : ℕ) (hs : s ≤ t.val) (control0 : TimeControl p) :=
  List (LogicalCell p rate) ×
    (LiveRemainder rate rewards C_star C_h q t s hs control0 ×
      (PropRestControl p × (AuxiliaryArray p × FullReadout p)) )

/-- Restore the same current-control remainder to the fixed original control
and read its strict calendar past. -/
def fixedControlPast (x : LiveRemainder rate rewards C_star C_h q t s hs control0)
    (a : AuxiliaryArray p) :
    List (LogicalCell p rate) :=
  let z := ReferenceFirstLiveRecordingSourceCylinder.sourceRecover rate rewards
    C_star C_h q t s hs control0
    (ReferenceFirstLivePostUpdateProposalLaw.liveRetained rate rewards C_star C_h
      q t s hs control0 x, control0)
  ReferenceFirstLiveChronologicalPrefixCausality.calendarPast
    rate rewards C_star C_h (z.val, a) t.val

theorem measurable_fixedControlPast :
    Measurable (fun xa : LiveRemainder rate rewards C_star C_h q t s hs control0 × AuxiliaryArray p =>
      fixedControlPast rate rewards C_star C_h q t s hs control0 xa.1 xa.2) := by
  have hsource : Measurable (fun xa :
      LiveRemainder rate rewards C_star C_h q t s hs control0 × AuxiliaryArray p =>
      ((ReferenceFirstLiveRecordingSourceCylinder.sourceRecover rate rewards C_star C_h
        q t s hs control0
        (ReferenceFirstLivePostUpdateProposalLaw.liveRetained rate rewards C_star C_h
          q t s hs control0 xa.1, control0)).val, xa.2)) := by
    exact (measurable_subtype_coe.comp
      ((ReferenceFirstLiveRecordingSourceCylinder.measurable_sourceRecover
        rate rewards C_star C_h q t s hs control0).comp
        ((ReferenceFirstLivePostUpdateProposalLaw.measurable_liveRetained
          rate rewards C_star C_h q t s hs control0).comp measurable_fst |>.prodMk
          measurable_const))).prodMk measurable_snd
  have hpast := (measurable_calendarPast rate rewards C_star C_h t.val).comp hsource
  convert hpast using 1
  funext xa
  rfl

private theorem sourcePrefix_replaceSourceControl (source : SourceInput p)
    (u : TimeControl p) :
    ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val
      (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t source u) =
    ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val source := by
  have hindex : ActualInitializationPhysicalStep.selectedRowIndex p
      (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t source u) =
        ActualInitializationPhysicalStep.selectedRowIndex p source := by
    simp [ActualInitializationPhysicalStep.selectedRowIndex,
      ReferenceFixedTimeSourceControlCoupling.replaceSourceControl]
  apply Prod.ext
  · apply Prod.ext
    · rfl
    · funext j
      dsimp only [ReferenceSourcePrefixHistoryFiltration.sourcePrefix]
      rw [hindex]
      by_cases hj : j = ActualInitializationPhysicalStep.selectedRowIndex p source
      · subst j
        apply Prod.ext
        · simp [ReferenceFixedTimeSourceControlCoupling.replaceSourceControl,
            ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex]
        · funext v
          by_cases hv : v.val < t.val
          · have hvt : v ≠ t := by
              intro h
              subst v
              omega
            simp [ReferenceFixedTimeSourceControlCoupling.replaceSourceControl,
              ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex,
              Function.update_of_ne hvt]
          · have hv' : ¬ v < t := by
              intro h
              exact hv (Fin.lt_def.mp h)
            simp [ReferenceFixedTimeSourceControlCoupling.replaceSourceControl,
              ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex,
              hv']
      · simp [ReferenceFixedTimeSourceControlCoupling.replaceSourceControl,
          ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex,
          hj]
  · rfl

private theorem fixedSplit_sourcePrefix_eq (x : ReferenceFirstLiveRecordingReadoutMeasurability.SourceX
    rate rewards C_star C_h q t s hs control0) (u : TimeControl p) :
    ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val
        (ReferenceFirstLiveRecordingSourceCylinder.sourceRecover rate rewards C_star C_h
          q t s hs control0 (x, u)).val =
      ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val
        (ReferenceFirstLiveRecordingSourceCylinder.sourceRecover rate rewards C_star C_h
          q t s hs control0 (x, control0)).val := by
  let e := ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t
  let base := (ReferenceFirstLiveRecordingSourceCylinder.sourceRecover rate rewards C_star C_h
    q t s hs control0 (x, control0)).val
  have hq : ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p base = q := by
    dsimp [base]
    exact ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_symm_coordinatorIndex
      p q t control0 x.1 x.property.1
  have hreplace := ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_replaceSourceControl
    p q t base u hq
  have hbase : (e base).2 = x.val := by
    dsimp [base, e]
    exact congrArg Prod.snd ((e).apply_symm_apply (control0, x.val))
  have hsource : (ReferenceFirstLiveRecordingSourceCylinder.sourceRecover rate rewards C_star C_h
      q t s hs control0 (x, u)).val =
      ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t base u := by
    change (e).symm (u, x.val) = _
    rw [← hbase]
    exact hreplace
  rw [hsource, sourcePrefix_replaceSourceControl]

/-- Whole-current-control restoration identifies the actual source past with
the baseline restoration while retaining the same private arrays and all
noncurrent source coordinates. -/
theorem calendarPast_sourceRecover_fixedControl
    (x : ReferenceFirstLiveRecordingReadoutMeasurability.SourceX
      rate rewards C_star C_h q t s hs control0) (u : TimeControl p)
    (a : AuxiliaryArray p) :
    ReferenceFirstLiveChronologicalPrefixCausality.calendarPast rate rewards C_star C_h
      ((ReferenceFirstLiveRecordingSourceCylinder.sourceRecover rate rewards C_star C_h
          q t s hs control0 (x, u)).val, a) t.val =
    ReferenceFirstLiveChronologicalPrefixCausality.calendarPast rate rewards C_star C_h
      ((ReferenceFirstLiveRecordingSourceCylinder.sourceRecover rate rewards C_star C_h
          q t s hs control0 (x, control0)).val, a) t.val := by
  let left := (ReferenceFirstLiveRecordingSourceCylinder.sourceRecover rate rewards C_star C_h
    q t s hs control0 (x, u)).val
  let right := (ReferenceFirstLiveRecordingSourceCylinder.sourceRecover rate rewards C_star C_h
    q t s hs control0 (x, control0)).val
  calc
    ReferenceFirstLiveChronologicalPrefixCausality.calendarPast rate rewards C_star C_h
        (left, a) t.val =
      ReferenceFirstLiveChronologicalPrefixCausality.calendarPast rate rewards C_star C_h
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val left, a) t.val :=
      ReferenceFirstLiveChronologicalPrefixCausality.calendarPast_sourcePrefix
        rate rewards C_star C_h control0 t.val (Nat.le_of_lt t.isLt) left a
    _ = ReferenceFirstLiveChronologicalPrefixCausality.calendarPast rate rewards C_star C_h
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val right, a) t.val := by
      rw [fixedSplit_sourcePrefix_eq rate rewards C_star C_h q t s hs control0 x u]
    _ = ReferenceFirstLiveChronologicalPrefixCausality.calendarPast rate rewards C_star C_h
        (right, a) t.val :=
      (ReferenceFirstLiveChronologicalPrefixCausality.calendarPast_sourcePrefix
        rate rewards C_star C_h control0 t.val (Nat.le_of_lt t.isLt) right a).symm

theorem continuingSource_calendarPast_restore
    (z : ReferenceFirstLiveRecordingSourceCylinder.SourcePlus
      rate rewards C_star C_h q t s hs control0) (a : AuxiliaryArray p) :
    ReferenceFirstLiveChronologicalPrefixCausality.calendarPast rate rewards C_star C_h
      (z.val.val, a) t.val =
      fixedControlPast rate rewards C_star C_h q t s hs control0
      (.inl (ReferenceFirstLiveRecordingSourceCylinder.branchSourceSplit
        rate rewards C_star C_h q t s hs control0 z).1) a := by
  let split := ReferenceFirstLiveRecordingSourceCylinder.branchSourceSplit
    rate rewards C_star C_h q t s hs control0 z
  have hrec := congrArg Subtype.val
    (ReferenceFirstLiveRecordingSourceCylinder.branchSourceSplit_recover
      rate rewards C_star C_h q t s hs control0 z)
  rw [← hrec]
  exact calendarPast_sourceRecover_fixedControl rate rewards C_star C_h q t s hs control0
    split.1 split.2 a

theorem emptySource_calendarPast_restore
    (z : ReferenceFirstLiveEmptyPendingMarkerLaw.Zempty
      rate rewards C_star C_h q t s hs control0) (a : AuxiliaryArray p) :
    ReferenceFirstLiveChronologicalPrefixCausality.calendarPast rate rewards C_star C_h
      (z.val.val, a) t.val =
      fixedControlPast rate rewards C_star C_h q t s hs control0
      (.inr (ReferenceFirstLiveEmptyPendingMarkerLaw.emptySourceSplit
        rate rewards C_star C_h q t s hs control0 z).1) a := by
  let split := ReferenceFirstLiveEmptyPendingMarkerLaw.emptySourceSplit
    rate rewards C_star C_h q t s hs control0 z
  have hrec := congrArg Subtype.val
    (ReferenceFirstLiveEmptyPendingMarkerLaw.emptySourceSplit_recover
      rate rewards C_star C_h q t s hs control0 z)
  rw [← hrec]
  exact calendarPast_sourceRecover_fixedControl rate rewards C_star C_h q t s hs control0
    split.1 split.2 a

def pastTestBoolIndicator (b : Bool) : ℝ := if b = true then 1 else 0

theorem measurable_pastTestBoolIndicator : Measurable pastTestBoolIndicator :=
  measurable_of_finite _

theorem norm_pastTestBoolIndicator_le_one (b : Bool) :
    ‖pastTestBoolIndicator b‖ ≤ 1 := by
  cases b <;> norm_num [pastTestBoolIndicator]

def continuingPastTestObservation
    (z : ReferenceFirstLiveRecordingSourceCylinder.SourcePlus
      rate rewards C_star C_h q t s hs control0) (a : AuxiliaryArray p) :
    PastTestObservation rate rewards C_star C_h q t s hs control0 :=
  let split := ReferenceFirstLiveRecordingSourceCylinder.branchSourceSplit
    rate rewards C_star C_h q t s hs control0 z
  let nonproposal := ReferenceFirstLivePostUpdateProposalLaw.liveNonpropObservation
    rate rewards C_star C_h q t s hs control0
    (.inl split.1, (ReferenceFirstLivePostUpdateProposalLaw.proposalControlSplit p split.2).2)
  (ReferenceFirstLiveChronologicalPrefixCausality.calendarPast
      rate rewards C_star C_h (z.val.val, a) t.val,
    (nonproposal.1.1, (nonproposal.1.2, (a, nonproposal.2))))

def emptyPastTestObservation
    (z : ReferenceFirstLiveEmptyPendingMarkerLaw.Zempty
      rate rewards C_star C_h q t s hs control0) (a : AuxiliaryArray p) :
    PastTestObservation rate rewards C_star C_h q t s hs control0 :=
  let split := ReferenceFirstLiveEmptyPendingMarkerLaw.emptySourceSplit
    rate rewards C_star C_h q t s hs control0 z
  let nonproposal := ReferenceFirstLivePostUpdateProposalLaw.liveNonpropObservation
    rate rewards C_star C_h q t s hs control0
    (.inr split.1, (ReferenceFirstLivePostUpdateProposalLaw.proposalControlSplit p split.2).2)
  (ReferenceFirstLiveChronologicalPrefixCausality.calendarPast
      rate rewards C_star C_h (z.val.val, a) t.val,
    (nonproposal.1.1, (nonproposal.1.2, (a, nonproposal.2))))

theorem measurable_continuingPastTestObservation :
    Measurable (fun za :
      ReferenceFirstLiveRecordingSourceCylinder.SourcePlus
        rate rewards C_star C_h q t s hs control0 × AuxiliaryArray p =>
      continuingPastTestObservation rate rewards C_star C_h q t s hs control0 za.1 za.2) := by
  let split := ReferenceFirstLiveRecordingSourceCylinder.branchSourceSplit
    rate rewards C_star C_h q t s hs control0
  have hsplit : Measurable (fun za :
      ReferenceFirstLiveRecordingSourceCylinder.SourcePlus
        rate rewards C_star C_h q t s hs control0 × AuxiliaryArray p => split za.1) :=
    (ReferenceFirstLiveRecordingSourceCylinder.measurable_branchSourceSplit
      rate rewards C_star C_h q t s hs control0).comp measurable_fst
  let tag := fun za :
      ReferenceFirstLiveRecordingSourceCylinder.SourcePlus
        rate rewards C_star C_h q t s hs control0 × AuxiliaryArray p =>
      (Sum.inl (split za.1).1 : LiveRemainder rate rewards C_star C_h q t s hs control0)
  have htag : Measurable tag :=
    (measurable_inl.comp (measurable_fst.comp hsplit))
  let rest := fun za :
      ReferenceFirstLiveRecordingSourceCylinder.SourcePlus
        rate rewards C_star C_h q t s hs control0 × AuxiliaryArray p =>
      (ReferenceFirstLivePostUpdateProposalLaw.proposalControlSplit p (split za.1).2).2
  have hrest : Measurable rest :=
    ((ReferenceFirstLivePostUpdateProposalLaw.proposalControlSplit p).measurable.snd.comp
      (measurable_snd.comp hsplit))
  let nonproposal := fun za :
      ReferenceFirstLiveRecordingSourceCylinder.SourcePlus
        rate rewards C_star C_h q t s hs control0 × AuxiliaryArray p =>
      ReferenceFirstLivePostUpdateProposalLaw.liveNonpropObservation
        rate rewards C_star C_h q t s hs control0 (tag za, rest za)
  have hnonproposal : Measurable nonproposal :=
    (ReferenceFirstLivePostUpdateProposalLaw.measurable_liveNonpropObservation
      rate rewards C_star C_h q t s hs control0).comp (htag.prodMk hrest)
  have hpast : Measurable (fun za :
      ReferenceFirstLiveRecordingSourceCylinder.SourcePlus
        rate rewards C_star C_h q t s hs control0 × AuxiliaryArray p =>
      ReferenceFirstLiveChronologicalPrefixCausality.calendarPast rate rewards C_star C_h
        (za.1.val.val, za.2) t.val) := by
    exact (measurable_calendarPast rate rewards C_star C_h t.val).comp
      ((measurable_subtype_coe.comp
        (measurable_subtype_coe.comp measurable_fst)).prodMk
        measurable_snd)
  have hlive : Measurable (fun za => (nonproposal za).1.1) :=
    measurable_fst.comp (measurable_fst.comp hnonproposal)
  have hcontrol : Measurable (fun za => (nonproposal za).1.2) :=
    measurable_snd.comp (measurable_fst.comp hnonproposal)
  have hreadout : Measurable (fun za => (nonproposal za).2) := measurable_snd.comp hnonproposal
  have htail := hlive.prodMk (hcontrol.prodMk (measurable_snd.prodMk hreadout))
  have hobs := hpast.prodMk htail
  change Measurable (fun za =>
    (ReferenceFirstLiveChronologicalPrefixCausality.calendarPast rate rewards C_star C_h
        (za.1.val.val, za.2) t.val,
        ((nonproposal za).1.1,
          ((nonproposal za).1.2, (za.2, (nonproposal za).2)))))
  exact hobs

theorem measurable_emptyPastTestObservation :
    Measurable (fun za :
      ReferenceFirstLiveEmptyPendingMarkerLaw.Zempty
        rate rewards C_star C_h q t s hs control0 × AuxiliaryArray p =>
      emptyPastTestObservation rate rewards C_star C_h q t s hs control0 za.1 za.2) := by
  let split := ReferenceFirstLiveEmptyPendingMarkerLaw.emptySourceSplit
    rate rewards C_star C_h q t s hs control0
  have hsplit : Measurable (fun za :
      ReferenceFirstLiveEmptyPendingMarkerLaw.Zempty
        rate rewards C_star C_h q t s hs control0 × AuxiliaryArray p => split za.1) :=
    (ReferenceFirstLiveEmptyPendingMarkerLaw.measurable_emptySourceSplit
      rate rewards C_star C_h q t s hs control0).comp measurable_fst
  let tag := fun za :
      ReferenceFirstLiveEmptyPendingMarkerLaw.Zempty
        rate rewards C_star C_h q t s hs control0 × AuxiliaryArray p =>
      (Sum.inr (split za.1).1 : LiveRemainder rate rewards C_star C_h q t s hs control0)
  have htag : Measurable tag :=
    (measurable_inr.comp (measurable_fst.comp hsplit))
  let rest := fun za :
      ReferenceFirstLiveEmptyPendingMarkerLaw.Zempty
        rate rewards C_star C_h q t s hs control0 × AuxiliaryArray p =>
      (ReferenceFirstLivePostUpdateProposalLaw.proposalControlSplit p (split za.1).2).2
  have hrest : Measurable rest :=
    ((ReferenceFirstLivePostUpdateProposalLaw.proposalControlSplit p).measurable.snd.comp
      (measurable_snd.comp hsplit))
  let nonproposal := fun za :
      ReferenceFirstLiveEmptyPendingMarkerLaw.Zempty
        rate rewards C_star C_h q t s hs control0 × AuxiliaryArray p =>
      ReferenceFirstLivePostUpdateProposalLaw.liveNonpropObservation
        rate rewards C_star C_h q t s hs control0 (tag za, rest za)
  have hnonproposal : Measurable nonproposal :=
    (ReferenceFirstLivePostUpdateProposalLaw.measurable_liveNonpropObservation
      rate rewards C_star C_h q t s hs control0).comp (htag.prodMk hrest)
  have hpast : Measurable (fun za :
      ReferenceFirstLiveEmptyPendingMarkerLaw.Zempty
        rate rewards C_star C_h q t s hs control0 × AuxiliaryArray p =>
      ReferenceFirstLiveChronologicalPrefixCausality.calendarPast rate rewards C_star C_h
        (za.1.val.val, za.2) t.val) := by
    exact (measurable_calendarPast rate rewards C_star C_h t.val).comp
      ((measurable_subtype_coe.comp
        (measurable_subtype_coe.comp measurable_fst)).prodMk
        measurable_snd)
  have hlive : Measurable (fun za => (nonproposal za).1.1) :=
    measurable_fst.comp (measurable_fst.comp hnonproposal)
  have hcontrol : Measurable (fun za => (nonproposal za).1.2) :=
    measurable_snd.comp (measurable_fst.comp hnonproposal)
  have hreadout : Measurable (fun za => (nonproposal za).2) := measurable_snd.comp hnonproposal
  have htail := hlive.prodMk (hcontrol.prodMk (measurable_snd.prodMk hreadout))
  have hobs := hpast.prodMk htail
  change Measurable (fun za =>
    (ReferenceFirstLiveChronologicalPrefixCausality.calendarPast rate rewards C_star C_h
        (za.1.val.val, za.2) t.val,
        ((nonproposal za).1.1,
          ((nonproposal za).1.2, (za.2, (nonproposal za).2)))))
  exact hobs

private def pastTestSection (F : PastTestObservation rate rewards C_star C_h q t s hs control0 → ℝ)
    (a : AuxiliaryArray p) :
    ((LiveRemainder rate rewards C_star C_h q t s hs control0 × PropRestControl p) ×
      FullReadout p) → ℝ := fun y =>
  F (fixedControlPast rate rewards C_star C_h q t s hs control0 y.1.1 a,
    (y.1.1, (y.1.2, (a, y.2))))

private theorem measurable_pastTestSection
    (F : PastTestObservation rate rewards C_star C_h q t s hs control0 → ℝ)
    (hF : Measurable F) (a : AuxiliaryArray p) :
    Measurable (pastTestSection rate rewards C_star C_h q t s hs control0 F a) := by
  have hlive : Measurable (fun y :
      ((LiveRemainder rate rewards C_star C_h q t s hs control0 × PropRestControl p) ×
        FullReadout p) => y.1.1) :=
    measurable_fst.comp measurable_fst
  have hrest : Measurable (fun y :
      ((LiveRemainder rate rewards C_star C_h q t s hs control0 × PropRestControl p) ×
        FullReadout p) => y.1.2) := measurable_snd.comp measurable_fst
  have hreadout : Measurable (fun y :
      ((LiveRemainder rate rewards C_star C_h q t s hs control0 × PropRestControl p) ×
        FullReadout p) => y.2) := measurable_snd
  have hpast : Measurable (fun y :
      ((LiveRemainder rate rewards C_star C_h q t s hs control0 × PropRestControl p) ×
        FullReadout p) =>
      fixedControlPast rate rewards C_star C_h q t s hs control0 y.1.1 a) := by
    have hpair : Measurable (fun y :
        ((LiveRemainder rate rewards C_star C_h q t s hs control0 × PropRestControl p) ×
          FullReadout p) => (y.1.1, a)) := hlive.prodMk measurable_const
    have hp := (measurable_fixedControlPast rate rewards C_star C_h q t s hs control0).comp hpair
    convert hp using 1
    funext y
    rfl
  exact hF.comp (hpast.prodMk (hlive.prodMk (hrest.prodMk
    (measurable_const.prodMk hreadout))))

def pastTestFullReadout
    (o : PastTestObservation rate rewards C_star C_h q t s hs control0) : FullReadout p :=
  o.2.2.2.2

theorem measurable_pastTestFullReadout :
    Measurable (pastTestFullReadout rate rewards C_star C_h q t s hs control0) := by
  exact measurable_snd.comp (measurable_snd.comp
    (measurable_snd.comp measurable_snd))

def pastTestBeforeOverflow (o : PastTestObservation rate rewards C_star C_h q t s hs control0) :
    Bool := (pastTestFullReadout rate rewards C_star C_h q t s hs control0 o).2.2.beforeOverflow

theorem measurable_pastTestBeforeOverflow :
    Measurable (pastTestBeforeOverflow rate rewards C_star C_h q t s hs control0) := by
  have hfield : Measurable (fun v : FullReadout p => v.2.2.beforeOverflow) :=
    measurable_of_countable _
  exact hfield.comp (measurable_pastTestFullReadout rate rewards C_star C_h q t s hs control0)

def pastTestClearBitIndicator (b : Bool) : ℝ := if b = false then 1 else 0

def pastTestClearIndicator
    (o : PastTestObservation rate rewards C_star C_h q t s hs control0) : ℝ :=
  pastTestClearBitIndicator
    (pastTestBeforeOverflow rate rewards C_star C_h q t s hs control0 o)

theorem measurable_pastTestClearIndicator :
    Measurable (pastTestClearIndicator rate rewards C_star C_h q t s hs control0) :=
  (measurable_of_finite pastTestClearBitIndicator).comp
    (measurable_pastTestBeforeOverflow rate rewards C_star C_h q t s hs control0)

theorem norm_pastTestClearIndicator_le_one
    (o : PastTestObservation rate rewards C_star C_h q t s hs control0) :
    ‖pastTestClearIndicator rate rewards C_star C_h q t s hs control0 o‖ ≤ 1 := by
  by_cases h : pastTestBeforeOverflow rate rewards C_star C_h q t s hs control0 o = false
  · simp [pastTestClearIndicator, pastTestClearBitIndicator, h]
  · simp [pastTestClearIndicator, pastTestClearBitIndicator, h]

def pastTestLogicalProposal (o : PastTestObservation rate rewards C_star C_h q t s hs control0)
    (physicalBit : Bool) : Bool :=
  (pastTestBeforeOverflow rate rewards C_star C_h q t s hs control0 o = false) && physicalBit

private theorem physicalProductIntegral
    {Z : Type*} [MeasurableSpace Z] (μ : Measure Z) [IsFiniteMeasure μ]
    (obs : Z × AuxiliaryArray p → PastTestObservation rate rewards C_star C_h q t s hs control0)
    (hobs : Measurable obs) (bit : Z → Bool) (hbit : Measurable bit)
    (F : PastTestObservation rate rewards C_star C_h q t s hs control0 → ℝ)
    (hF : Measurable F) (C : ℝ) (hC : ∀ o, ‖F o‖ ≤ C)
    (hsection : ∀ a, ∫ z, F (obs (z, a)) * pastTestBoolIndicator (bit z) ∂μ =
      FollowerCutoffScan.proposalHazard p rate.eta.val * ∫ z, F (obs (z, a)) ∂μ) :
    Integrable (fun za => F (obs za)) (μ.prod
      (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p)) ∧
    Integrable (fun za => F (obs za) * pastTestBoolIndicator (bit za.1))
      (μ.prod (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p)) ∧
    (∫ za, F (obs za) * pastTestBoolIndicator (bit za.1) ∂
      μ.prod (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p)) =
      FollowerCutoffScan.proposalHazard p rate.eta.val *
        ∫ za, F (obs za) ∂μ.prod (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p) := by
  let auxLaw := ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p
  let f : Z × AuxiliaryArray p → ℝ := fun za => F (obs za)
  let fbit : Z × AuxiliaryArray p → ℝ := fun za =>
    F (obs za) * pastTestBoolIndicator (bit za.1)
  have hFmeas : Measurable f := hF.comp hobs
  have hbitMeas : Measurable (fun za : Z × AuxiliaryArray p =>
      pastTestBoolIndicator (bit za.1)) :=
    measurable_pastTestBoolIndicator.comp (hbit.comp measurable_fst)
  have hfbMeas : Measurable fbit := hFmeas.mul hbitMeas
  have hFbound : ∀ za, ‖f za‖ ≤ C := fun za => hC (obs za)
  have hfbBound : ∀ za, ‖fbit za‖ ≤ C := by
    intro za
    have hC_nonneg : 0 ≤ C := le_trans (norm_nonneg (F (obs za))) (hC (obs za))
    by_cases hb : bit za.1 = true
    · simp [fbit, pastTestBoolIndicator, hb]
      exact hC (obs za)
    · simp [fbit, pastTestBoolIndicator, hb, hC_nonneg]
  have hfi : Integrable f (μ.prod auxLaw) :=
    Integrable.of_bound hFmeas.aestronglyMeasurable C
      (Filter.Eventually.of_forall hFbound)
  have hfbi : Integrable fbit (μ.prod auxLaw) :=
    Integrable.of_bound hfbMeas.aestronglyMeasurable C
      (Filter.Eventually.of_forall hfbBound)
  have hsections (a : AuxiliaryArray p) :
      (∫ z, fbit (z, a) ∂μ) =
        FollowerCutoffScan.proposalHazard p rate.eta.val * ∫ z, f (z, a) ∂μ := by
    exact hsection a
  refine ⟨hfi, hfbi, ?_⟩
  rw [integral_prod_symm fbit hfbi, integral_prod_symm f hfi]
  calc
    (∫ a, ∫ z, fbit (z, a) ∂μ ∂auxLaw) =
        ∫ a, FollowerCutoffScan.proposalHazard p rate.eta.val *
          ∫ z, f (z, a) ∂μ ∂auxLaw := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hsections
    _ = FollowerCutoffScan.proposalHazard p rate.eta.val *
        ∫ a, ∫ z, f (z, a) ∂μ ∂auxLaw := by rw [integral_const_mul]

theorem continuingSource_completePast_proposal_integral
    (_hpos : s < t.val)
    (F : PastTestObservation rate rewards C_star C_h q t s hs control0 → ℝ)
    (hF : Measurable F) (C : ℝ) (hC : ∀ o, ‖F o‖ ≤ C) :
    let μ := ReferenceFirstLiveRecordingSourceCylinder.branchSourceMeasure
      rate rewards C_star C_h q t s hs control0
    let split := ReferenceFirstLiveRecordingSourceCylinder.branchSourceSplit
      rate rewards C_star C_h q t s hs control0
    let bit := fun z => ReferenceFirstLivePostUpdateProposalLaw.physicalProposalBit rate
      (split z).2
    Integrable (fun za => F (continuingPastTestObservation
      rate rewards C_star C_h q t s hs control0 za.1 za.2))
      (μ.prod (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p)) ∧
    Integrable (fun za => F (continuingPastTestObservation
      rate rewards C_star C_h q t s hs control0 za.1 za.2) *
        pastTestBoolIndicator (bit za.1))
      (μ.prod (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p)) ∧
    (∫ za, F (continuingPastTestObservation
      rate rewards C_star C_h q t s hs control0 za.1 za.2) *
        pastTestBoolIndicator (bit za.1) ∂
      μ.prod (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p)) =
      FollowerCutoffScan.proposalHazard p rate.eta.val *
        ∫ za, F (continuingPastTestObservation
          rate rewards C_star C_h q t s hs control0 za.1 za.2) ∂
          μ.prod (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p) := by
  classical
  dsimp only
  let μ := ReferenceFirstLiveRecordingSourceCylinder.branchSourceMeasure
    rate rewards C_star C_h q t s hs control0
  let split := ReferenceFirstLiveRecordingSourceCylinder.branchSourceSplit
    rate rewards C_star C_h q t s hs control0
  let bit := fun z => ReferenceFirstLivePostUpdateProposalLaw.physicalProposalBit rate
    (split z).2
  let obs := fun za : ReferenceFirstLiveRecordingSourceCylinder.SourcePlus
      rate rewards C_star C_h q t s hs control0 × AuxiliaryArray p =>
    continuingPastTestObservation rate rewards C_star C_h q t s hs control0 za.1 za.2
  let nonproposal := fun z : ReferenceFirstLiveRecordingSourceCylinder.SourcePlus
      rate rewards C_star C_h q t s hs control0 =>
    ReferenceFirstLivePostUpdateProposalLaw.liveNonpropObservation
      rate rewards C_star C_h q t s hs control0
      (.inl (split z).1,
        (ReferenceFirstLivePostUpdateProposalLaw.proposalControlSplit p (split z).2).2)
  have hobs : Measurable obs :=
    measurable_continuingPastTestObservation rate rewards C_star C_h q t s hs control0
  have hbit : Measurable bit :=
    (ReferenceFirstLivePostUpdateProposalLaw.measurable_physicalProposalBit rate).comp
      ((measurable_snd.comp
        (ReferenceFirstLiveRecordingSourceCylinder.measurable_branchSourceSplit
          rate rewards C_star C_h q t s hs control0)))
  have hsection (a : AuxiliaryArray p) :
      (∫ z, F (obs (z, a)) * pastTestBoolIndicator (bit z) ∂μ) =
        FollowerCutoffScan.proposalHazard p rate.eta.val * ∫ z, F (obs (z, a)) ∂μ := by
    let G := pastTestSection rate rewards C_star C_h q t s hs control0 F a
    have hG : Measurable G := measurable_pastTestSection
      rate rewards C_star C_h q t s hs control0 F hF a
    have hGBound : ∀ y, ‖G y‖ ≤ C := fun y => hC _
    have hlaw := ReferenceFirstLivePostUpdateProposalLaw.continuingSource_actualUpdate_integral
      rate rewards C_star C_h q t s hs control0 _hpos G hG C hGBound
    rcases hlaw with ⟨_, _, hlaw⟩
    have hpoint (z : ReferenceFirstLiveRecordingSourceCylinder.SourcePlus
        rate rewards C_star C_h q t s hs control0) :
        G (nonproposal z) = F (obs (z, a)) := by
      let tail : LiveRemainder rate rewards C_star C_h q t s hs control0 ×
          (PropRestControl p × (AuxiliaryArray p × FullReadout p)) :=
        ((nonproposal z).1.1, ((nonproposal z).1.2, (a, (nonproposal z).2)))
      change F (fixedControlPast rate rewards C_star C_h q t s hs control0
          (.inl (split z).1) a, tail) =
        F (ReferenceFirstLiveChronologicalPrefixCausality.calendarPast
          rate rewards C_star C_h (z.val.val, a) t.val, tail)
      exact congrArg (fun past : List (LogicalCell p rate) => F (past, tail))
        (continuingSource_calendarPast_restore rate rewards C_star C_h q t s hs control0
          z a).symm
    calc
      (∫ z, F (obs (z, a)) * pastTestBoolIndicator (bit z) ∂μ) =
          ∫ z, G (nonproposal z) * pastTestBoolIndicator (bit z) ∂μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun z =>
          congrArg (fun v : ℝ => v * pastTestBoolIndicator (bit z)) (hpoint z).symm)
      _ = FollowerCutoffScan.proposalHazard p rate.eta.val * ∫ z, G (nonproposal z) ∂μ := hlaw
      _ = FollowerCutoffScan.proposalHazard p rate.eta.val * ∫ z, F (obs (z, a)) ∂μ := by
        congr 1
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun z => hpoint z)
  exact physicalProductIntegral rate rewards C_star C_h q t s hs control0 μ obs hobs bit hbit
    F hF C hC hsection

theorem emptySource_completePast_proposal_integral
    (_hpos : s < t.val)
    (F : PastTestObservation rate rewards C_star C_h q t s hs control0 → ℝ)
    (hF : Measurable F) (C : ℝ) (hC : ∀ o, ‖F o‖ ≤ C) :
    let μ := ReferenceFirstLiveEmptyPendingMarkerLaw.muEmpty
      rate rewards C_star C_h q t s hs control0
    let split := ReferenceFirstLiveEmptyPendingMarkerLaw.emptySourceSplit
      rate rewards C_star C_h q t s hs control0
    let bit := fun z => ReferenceFirstLivePostUpdateProposalLaw.physicalProposalBit rate
      (split z).2
    Integrable (fun za => F (emptyPastTestObservation
      rate rewards C_star C_h q t s hs control0 za.1 za.2))
      (μ.prod (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p)) ∧
    Integrable (fun za => F (emptyPastTestObservation
      rate rewards C_star C_h q t s hs control0 za.1 za.2) *
        pastTestBoolIndicator (bit za.1))
      (μ.prod (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p)) ∧
    (∫ za, F (emptyPastTestObservation
      rate rewards C_star C_h q t s hs control0 za.1 za.2) *
        pastTestBoolIndicator (bit za.1) ∂
      μ.prod (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p)) =
      FollowerCutoffScan.proposalHazard p rate.eta.val *
        ∫ za, F (emptyPastTestObservation
          rate rewards C_star C_h q t s hs control0 za.1 za.2) ∂
          μ.prod (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p) := by
  classical
  dsimp only
  let μ := ReferenceFirstLiveEmptyPendingMarkerLaw.muEmpty
    rate rewards C_star C_h q t s hs control0
  let split := ReferenceFirstLiveEmptyPendingMarkerLaw.emptySourceSplit
    rate rewards C_star C_h q t s hs control0
  let bit := fun z => ReferenceFirstLivePostUpdateProposalLaw.physicalProposalBit rate
    (split z).2
  let obs := fun za : ReferenceFirstLiveEmptyPendingMarkerLaw.Zempty
      rate rewards C_star C_h q t s hs control0 × AuxiliaryArray p =>
    emptyPastTestObservation rate rewards C_star C_h q t s hs control0 za.1 za.2
  let nonproposal := fun z : ReferenceFirstLiveEmptyPendingMarkerLaw.Zempty
      rate rewards C_star C_h q t s hs control0 =>
    ReferenceFirstLivePostUpdateProposalLaw.liveNonpropObservation
      rate rewards C_star C_h q t s hs control0
      (.inr (split z).1,
        (ReferenceFirstLivePostUpdateProposalLaw.proposalControlSplit p (split z).2).2)
  have hobs : Measurable obs :=
    measurable_emptyPastTestObservation rate rewards C_star C_h q t s hs control0
  have hbit : Measurable bit :=
    (ReferenceFirstLivePostUpdateProposalLaw.measurable_physicalProposalBit rate).comp
      (measurable_snd.comp
        (ReferenceFirstLiveEmptyPendingMarkerLaw.measurable_emptySourceSplit
          rate rewards C_star C_h q t s hs control0))
  have hsection (a : AuxiliaryArray p) :
      (∫ z, F (obs (z, a)) * pastTestBoolIndicator (bit z) ∂μ) =
        FollowerCutoffScan.proposalHazard p rate.eta.val * ∫ z, F (obs (z, a)) ∂μ := by
    let G := pastTestSection rate rewards C_star C_h q t s hs control0 F a
    have hG : Measurable G := measurable_pastTestSection
      rate rewards C_star C_h q t s hs control0 F hF a
    have hGBound : ∀ y, ‖G y‖ ≤ C := fun y => hC _
    have hlaw := ReferenceFirstLivePostUpdateProposalLaw.emptySource_actualUpdate_integral
      rate rewards C_star C_h q t s hs control0 _hpos G hG C hGBound
    rcases hlaw with ⟨_, _, hlaw⟩
    have hpoint (z : ReferenceFirstLiveEmptyPendingMarkerLaw.Zempty
        rate rewards C_star C_h q t s hs control0) :
        G (nonproposal z) = F (obs (z, a)) := by
      let tail : LiveRemainder rate rewards C_star C_h q t s hs control0 ×
          (PropRestControl p × (AuxiliaryArray p × FullReadout p)) :=
        ((nonproposal z).1.1, ((nonproposal z).1.2, (a, (nonproposal z).2)))
      change F (fixedControlPast rate rewards C_star C_h q t s hs control0
          (.inr (split z).1) a, tail) =
        F (ReferenceFirstLiveChronologicalPrefixCausality.calendarPast
          rate rewards C_star C_h (z.val.val, a) t.val, tail)
      exact congrArg (fun past : List (LogicalCell p rate) => F (past, tail))
        (emptySource_calendarPast_restore rate rewards C_star C_h q t s hs control0
          z a).symm
    calc
      (∫ z, F (obs (z, a)) * pastTestBoolIndicator (bit z) ∂μ) =
          ∫ z, G (nonproposal z) * pastTestBoolIndicator (bit z) ∂μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun z =>
          congrArg (fun v : ℝ => v * pastTestBoolIndicator (bit z)) (hpoint z).symm)
      _ = FollowerCutoffScan.proposalHazard p rate.eta.val * ∫ z, G (nonproposal z) ∂μ := hlaw
      _ = FollowerCutoffScan.proposalHazard p rate.eta.val * ∫ z, F (obs (z, a)) ∂μ := by
        congr 1
        apply integral_congr_ae
        exact Filter.Eventually.of_forall hpoint
  exact physicalProductIntegral rate rewards C_star C_h q t s hs control0 μ obs hobs bit hbit
    F hF C hC hsection

theorem continuingPastTestBeforeOverflow_actual
    (z : ReferenceFirstLiveRecordingSourceCylinder.SourcePlus
      rate rewards C_star C_h q t s hs control0) (a : AuxiliaryArray p) :
    pastTestBeforeOverflow rate rewards C_star C_h q t s hs control0
      (continuingPastTestObservation rate rewards C_star C_h q t s hs control0 z a) =
    (ReferenceFirstLivePostUpdateProposalLaw.numericalUpdateFields rate
      (ReferenceFirstLiveNumericalQueueBorel.numericalCountRunReadout
        rate rewards C_star C_h q t s hs control0 z.val)
      (RecordedQueueRun.quantizedArrival
        (ReferenceFirstLaunchNumericalCell.queueParameters rate)
        (ReferenceFirstLiveSourceCellReadout.cell
          rate rewards C_star C_h q t s hs control0 z).input)).beforeOverflow := by
  let split := ReferenceFirstLiveRecordingSourceCylinder.branchSourceSplit
    rate rewards C_star C_h q t s hs control0 z
  have hread := ReferenceFirstLivePostUpdateProposalLaw.liveNonpropObservation_atControl
    rate rewards C_star C_h q t s hs control0 (.inl split.1) split.2
  change (ReferenceFirstLivePostUpdateProposalLaw.liveNonpropObservation
      rate rewards C_star C_h q t s hs control0
      (.inl split.1,
        (ReferenceFirstLivePostUpdateProposalLaw.proposalControlSplit p split.2).2)).2.2.2.beforeOverflow = _
  rw [hread]
  change (ReferenceFirstLivePostUpdateProposalLaw.liveFullPreProposalReadout rate rewards C_star C_h
      q t s hs control0 (.inl split.1, split.2)).2.2.beforeOverflow = _
  simp only [ReferenceFirstLivePostUpdateProposalLaw.liveFullPreProposalReadout]
  rw [ReferenceFirstLivePostUpdateProposalLaw.continuingPreProposalReadout_actual
    rate rewards C_star C_h q t s hs control0 z]

theorem emptyPastTestBeforeOverflow_actual
    (z : ReferenceFirstLiveEmptyPendingMarkerLaw.Zempty
      rate rewards C_star C_h q t s hs control0) (a : AuxiliaryArray p) :
    pastTestBeforeOverflow rate rewards C_star C_h q t s hs control0
      (emptyPastTestObservation rate rewards C_star C_h q t s hs control0 z a) =
    (ReferenceFirstLivePostUpdateProposalLaw.numericalUpdateFields rate
      (ReferenceFirstLiveNumericalQueueBorel.numericalCountRunReadout
        rate rewards C_star C_h q t s hs control0 z.val)
      (RecordedQueueRun.quantizedArrival
        (ReferenceFirstLaunchNumericalCell.queueParameters rate)
        (ReferenceFirstLiveEmptyPendingSourceMoments.cell
          rate rewards C_star C_h q t s hs control0 z))).beforeOverflow := by
  let split := ReferenceFirstLiveEmptyPendingMarkerLaw.emptySourceSplit
    rate rewards C_star C_h q t s hs control0 z
  have hread := ReferenceFirstLivePostUpdateProposalLaw.liveNonpropObservation_atControl
    rate rewards C_star C_h q t s hs control0 (.inr split.1) split.2
  change (ReferenceFirstLivePostUpdateProposalLaw.liveNonpropObservation
      rate rewards C_star C_h q t s hs control0
      (.inr split.1,
        (ReferenceFirstLivePostUpdateProposalLaw.proposalControlSplit p split.2).2)).2.2.2.beforeOverflow = _
  rw [hread]
  change (ReferenceFirstLivePostUpdateProposalLaw.liveFullPreProposalReadout rate rewards C_star C_h
      q t s hs control0 (.inr split.1, split.2)).2.2.beforeOverflow = _
  simp only [ReferenceFirstLivePostUpdateProposalLaw.liveFullPreProposalReadout]
  rw [ReferenceFirstLivePostUpdateProposalLaw.emptyPreProposalReadout_actual
    rate rewards C_star C_h q t s hs control0 z]

private def pastTestClearMul
    (F : PastTestObservation rate rewards C_star C_h q t s hs control0 → ℝ)
    (o : PastTestObservation rate rewards C_star C_h q t s hs control0) : ℝ :=
  F o * pastTestClearIndicator rate rewards C_star C_h q t s hs control0 o

private theorem measurable_pastTestClearMul
    (F : PastTestObservation rate rewards C_star C_h q t s hs control0 → ℝ)
    (hF : Measurable F) :
    Measurable (pastTestClearMul rate rewards C_star C_h q t s hs control0 F) :=
  hF.mul (measurable_pastTestClearIndicator rate rewards C_star C_h q t s hs control0)

private theorem pastTestClearMul_bound
    (F : PastTestObservation rate rewards C_star C_h q t s hs control0 → ℝ)
    (C : ℝ) (hC : ∀ o, ‖F o‖ ≤ C) (o : PastTestObservation rate rewards C_star C_h q t s hs control0) :
    ‖pastTestClearMul rate rewards C_star C_h q t s hs control0 F o‖ ≤ C := by
  have hC_nonneg : 0 ≤ C := le_trans (norm_nonneg (F o)) (hC o)
  by_cases h : pastTestBeforeOverflow rate rewards C_star C_h q t s hs control0 o = false
  · simp [pastTestClearMul, pastTestClearIndicator, pastTestClearBitIndicator, h]
    exact hC o
  · simp [pastTestClearMul, pastTestClearIndicator, pastTestClearBitIndicator, h, hC_nonneg]

theorem pastTest_clearPhysicalIndicator_eq
    (o : PastTestObservation rate rewards C_star C_h q t s hs control0) (bit : Bool) :
    pastTestClearIndicator rate rewards C_star C_h q t s hs control0 o *
        pastTestBoolIndicator bit =
      pastTestBoolIndicator
        (pastTestLogicalProposal rate rewards C_star C_h q t s hs control0 o bit) := by
  cases h : pastTestBeforeOverflow rate rewards C_star C_h q t s hs control0 o <;>
    cases bit <;>
    simp [pastTestClearIndicator, pastTestClearBitIndicator, pastTestLogicalProposal,
      pastTestBoolIndicator, h]

theorem continuingSource_completePast_clearPRE_logical_integral
    (_hpos : s < t.val)
    (F : PastTestObservation rate rewards C_star C_h q t s hs control0 → ℝ)
    (hF : Measurable F) (C : ℝ) (hC : ∀ o, ‖F o‖ ≤ C) :
    let μ := ReferenceFirstLiveRecordingSourceCylinder.branchSourceMeasure
      rate rewards C_star C_h q t s hs control0
    let split := ReferenceFirstLiveRecordingSourceCylinder.branchSourceSplit
      rate rewards C_star C_h q t s hs control0
    let bit := fun z => ReferenceFirstLivePostUpdateProposalLaw.physicalProposalBit rate
      (split z).2
    let obs := fun za : ReferenceFirstLiveRecordingSourceCylinder.SourcePlus
        rate rewards C_star C_h q t s hs control0 × AuxiliaryArray p =>
      continuingPastTestObservation rate rewards C_star C_h q t s hs control0 za.1 za.2
    Integrable (fun za => F (obs za))
      (μ.prod (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p)) ∧
    Integrable (fun za => F (obs za) * pastTestBoolIndicator
      (pastTestLogicalProposal rate rewards C_star C_h q t s hs control0 (obs za) (bit za.1)))
      (μ.prod (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p)) ∧
    (∫ za, F (obs za) * pastTestBoolIndicator
      (pastTestLogicalProposal rate rewards C_star C_h q t s hs control0 (obs za) (bit za.1)) ∂
      μ.prod (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p)) =
      FollowerCutoffScan.proposalHazard p rate.eta.val *
        ∫ za, F (obs za) * pastTestClearIndicator rate rewards C_star C_h q t s hs control0
          (obs za) ∂μ.prod (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p) := by
  classical
  dsimp only
  let μ := ReferenceFirstLiveRecordingSourceCylinder.branchSourceMeasure
    rate rewards C_star C_h q t s hs control0
  let split := ReferenceFirstLiveRecordingSourceCylinder.branchSourceSplit
    rate rewards C_star C_h q t s hs control0
  let bit := fun z => ReferenceFirstLivePostUpdateProposalLaw.physicalProposalBit rate
    (split z).2
  let obs := fun za : ReferenceFirstLiveRecordingSourceCylinder.SourcePlus
      rate rewards C_star C_h q t s hs control0 × AuxiliaryArray p =>
    continuingPastTestObservation rate rewards C_star C_h q t s hs control0 za.1 za.2
  have horiginal := continuingSource_completePast_proposal_integral
    rate rewards C_star C_h q t s hs control0 _hpos F hF C hC
  rcases horiginal with ⟨hFint, _, _⟩
  let G := pastTestClearMul rate rewards C_star C_h q t s hs control0 F
  have hG : Measurable G := measurable_pastTestClearMul rate rewards C_star C_h q t s hs control0 F hF
  have hGBound : ∀ o, ‖G o‖ ≤ C :=
    pastTestClearMul_bound rate rewards C_star C_h q t s hs control0 F C hC
  have hclear := continuingSource_completePast_proposal_integral
    rate rewards C_star C_h q t s hs control0 _hpos G hG C hGBound
  rcases hclear with ⟨_, hclearPhysicalInt, hphysical⟩
  have hpoint (za : ReferenceFirstLiveRecordingSourceCylinder.SourcePlus
      rate rewards C_star C_h q t s hs control0 × AuxiliaryArray p) :
      F (obs za) * pastTestBoolIndicator
          (pastTestLogicalProposal rate rewards C_star C_h q t s hs control0
            (obs za) (bit za.1)) =
        G (obs za) * pastTestBoolIndicator (bit za.1) := by
    rw [← pastTest_clearPhysicalIndicator_eq rate rewards C_star C_h q t s hs control0
      (obs za) (bit za.1)]
    dsimp [G, pastTestClearMul]
    ring
  have hlogicalInt : Integrable (fun za => F (obs za) * pastTestBoolIndicator
      (pastTestLogicalProposal rate rewards C_star C_h q t s hs control0 (obs za) (bit za.1)))
      (μ.prod (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p)) :=
    hclearPhysicalInt.congr (Filter.Eventually.of_forall (fun za => (hpoint za).symm))
  refine ⟨hFint, hlogicalInt, ?_⟩
  calc
    (∫ za, F (obs za) * pastTestBoolIndicator
        (pastTestLogicalProposal rate rewards C_star C_h q t s hs control0 (obs za) (bit za.1)) ∂
      μ.prod (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p)) =
        ∫ za, G (obs za) * pastTestBoolIndicator (bit za.1) ∂
          μ.prod (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hpoint
    _ = FollowerCutoffScan.proposalHazard p rate.eta.val *
        ∫ za, G (obs za) ∂μ.prod (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p) :=
      hphysical
    _ = FollowerCutoffScan.proposalHazard p rate.eta.val *
        ∫ za, F (obs za) * pastTestClearIndicator rate rewards C_star C_h q t s hs control0
          (obs za) ∂μ.prod (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p) := by
      rfl

theorem emptySource_completePast_clearPRE_logical_integral
    (_hpos : s < t.val)
    (F : PastTestObservation rate rewards C_star C_h q t s hs control0 → ℝ)
    (hF : Measurable F) (C : ℝ) (hC : ∀ o, ‖F o‖ ≤ C) :
    let μ := ReferenceFirstLiveEmptyPendingMarkerLaw.muEmpty
      rate rewards C_star C_h q t s hs control0
    let split := ReferenceFirstLiveEmptyPendingMarkerLaw.emptySourceSplit
      rate rewards C_star C_h q t s hs control0
    let bit := fun z => ReferenceFirstLivePostUpdateProposalLaw.physicalProposalBit rate
      (split z).2
    let obs := fun za : ReferenceFirstLiveEmptyPendingMarkerLaw.Zempty
        rate rewards C_star C_h q t s hs control0 × AuxiliaryArray p =>
      emptyPastTestObservation rate rewards C_star C_h q t s hs control0 za.1 za.2
    Integrable (fun za => F (obs za))
      (μ.prod (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p)) ∧
    Integrable (fun za => F (obs za) * pastTestBoolIndicator
      (pastTestLogicalProposal rate rewards C_star C_h q t s hs control0 (obs za) (bit za.1)))
      (μ.prod (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p)) ∧
    (∫ za, F (obs za) * pastTestBoolIndicator
      (pastTestLogicalProposal rate rewards C_star C_h q t s hs control0 (obs za) (bit za.1)) ∂
      μ.prod (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p)) =
      FollowerCutoffScan.proposalHazard p rate.eta.val *
        ∫ za, F (obs za) * pastTestClearIndicator rate rewards C_star C_h q t s hs control0
          (obs za) ∂μ.prod (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p) := by
  classical
  dsimp only
  let μ := ReferenceFirstLiveEmptyPendingMarkerLaw.muEmpty
    rate rewards C_star C_h q t s hs control0
  let split := ReferenceFirstLiveEmptyPendingMarkerLaw.emptySourceSplit
    rate rewards C_star C_h q t s hs control0
  let bit := fun z => ReferenceFirstLivePostUpdateProposalLaw.physicalProposalBit rate
    (split z).2
  let obs := fun za : ReferenceFirstLiveEmptyPendingMarkerLaw.Zempty
      rate rewards C_star C_h q t s hs control0 × AuxiliaryArray p =>
    emptyPastTestObservation rate rewards C_star C_h q t s hs control0 za.1 za.2
  have horiginal := emptySource_completePast_proposal_integral
    rate rewards C_star C_h q t s hs control0 _hpos F hF C hC
  rcases horiginal with ⟨hFint, _, _⟩
  let G := pastTestClearMul rate rewards C_star C_h q t s hs control0 F
  have hG : Measurable G := measurable_pastTestClearMul rate rewards C_star C_h q t s hs control0 F hF
  have hGBound : ∀ o, ‖G o‖ ≤ C :=
    pastTestClearMul_bound rate rewards C_star C_h q t s hs control0 F C hC
  have hclear := emptySource_completePast_proposal_integral
    rate rewards C_star C_h q t s hs control0 _hpos G hG C hGBound
  rcases hclear with ⟨_, hclearPhysicalInt, hphysical⟩
  have hpoint (za : ReferenceFirstLiveEmptyPendingMarkerLaw.Zempty
      rate rewards C_star C_h q t s hs control0 × AuxiliaryArray p) :
      F (obs za) * pastTestBoolIndicator
          (pastTestLogicalProposal rate rewards C_star C_h q t s hs control0
            (obs za) (bit za.1)) =
        G (obs za) * pastTestBoolIndicator (bit za.1) := by
    rw [← pastTest_clearPhysicalIndicator_eq rate rewards C_star C_h q t s hs control0
      (obs za) (bit za.1)]
    dsimp [G, pastTestClearMul]
    ring
  have hlogicalInt : Integrable (fun za => F (obs za) * pastTestBoolIndicator
      (pastTestLogicalProposal rate rewards C_star C_h q t s hs control0 (obs za) (bit za.1)))
      (μ.prod (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p)) :=
    hclearPhysicalInt.congr (Filter.Eventually.of_forall (fun za => (hpoint za).symm))
  refine ⟨hFint, hlogicalInt, ?_⟩
  calc
    (∫ za, F (obs za) * pastTestBoolIndicator
        (pastTestLogicalProposal rate rewards C_star C_h q t s hs control0 (obs za) (bit za.1)) ∂
      μ.prod (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p)) =
        ∫ za, G (obs za) * pastTestBoolIndicator (bit za.1) ∂
          μ.prod (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hpoint
    _ = FollowerCutoffScan.proposalHazard p rate.eta.val *
        ∫ za, G (obs za) ∂μ.prod (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p) :=
      hphysical
    _ = FollowerCutoffScan.proposalHazard p rate.eta.val *
        ∫ za, F (obs za) * pastTestClearIndicator rate rewards C_star C_h q t s hs control0
          (obs za) ∂μ.prod (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p) := by
      rfl

end Bandits.Support.ReferenceFirstLivePastTestProposalLaw

end
