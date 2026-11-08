/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceExhaustiveGeneratedCalendarSourceLaw
public import Bandits.Support.ReferenceGeneratedCalendarLivePayoff
public import Bandits.Support.ReferenceOriginalStoppedTransportFixedIDMean
public import Bandits.Support.ReferenceOriginalStartupFixedIDMean

/-!
# Physical signed accounting on the exhaustive original calendar

Internal pathwise mathematics for ZIP4 `08_main_theorem.tex:78-109`,
`06_interruptions.tex:391-426`, `04_slow_fast_learner.tex:142-215,323-390`,
and `05_binary_transport.tex:293-325`. The physical rewards below are the
complete REFERENCE execution's collision-filtered own observations.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators Classical
open Bandits.Support ConstructorDimensions
open ReferenceFirstLiveChronologicalPrefixFoundation
open ReferencePostInvocationNoncallGeometry

namespace Bandits.Support.ReferenceCompleteOriginalSignedAccounting

variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)

local notation "Source" => BootstrapPrivateRoundStreams.SourceInput p
local notation "Auxiliary" => ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p
local notation "Cell" => LogicalCell p rate
local notation "Record" => ReferenceFirstLiveChronologicalPrefixFoundation.Record rate
local notation "Q" => ReferenceFirstLaunchNumericalCell.queueParameters rate
local notation "recordAt" => ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
local notation "start " z:max => ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
local notation "past" => ReferenceFirstCollectionLogicalPrefixExtension.extendedPast rate rewards C_star C_h
local notation "liveCells" => firstLiveChronologicalPrefix rate rewards C_star C_h
local notation "word" => ReferenceActualCollectionHiddenRefreshPath.actualOriginalWord rate rewards C_star C_h
local notation "bad " z:max => ReferenceCompleteSignedFirstBadCalendar.firstBadDate rate rewards C_star C_h z
local notation "launch " z:max => ReferenceCompleteSignedFirstBadCalendar.actualLaunchRound rate rewards C_star C_h z

/-- The original comparator's reward on the whole row at its actual date. -/
def comparatorReward (S0 : ProductSetLaw.ProductSet p.K p.m) (q : Fin p.T) : ℝ :=
  ∑ a ∈ S0.val, ((rewards q a).val : ℝ) / (D p : ℝ)

/-- The auxiliary reward at a date, read from the literal dated archive.
Disabled dates have an empty filter and contribute zero. -/
def dateAuxiliaryReward (H : List Cell) (q : Fin p.T) : ℝ :=
  ((H.filter (fun e => e.time == q)).map
    (ReferenceInitialStoppedCalendar.cellReward rate rewards)).sum

private theorem actualRecord_has_launch (q : Fin p.T) (z : Source)
    (r : Record) (hr : recordAt q z = some r) :
    ∃ active, ReferenceCorrectedInitializationLaunch.correctedLaunch rate z rewards C_star C_h = some active := by
  cases hl : ReferenceCorrectedInitializationLaunch.correctedLaunch rate z rewards C_star C_h with
  | some active => exact ⟨active, rfl⟩
  | none =>
    obtain ⟨_i, _hi, _hir, hstart⟩ := ReferencePostInvocationGeneratedAlignment.actualRecord_index
      rate rewards C_star C_h q z r hr
    have hs := ReferenceCompletePhysicalHistory.correctedLaunch_none_start_eq_T rate z rewards C_star C_h hl
    have := q.isLt
    omega

/-- Every actual suffix lookup has the reward retained in the complete
physical REFERENCE history at that same date. -/
theorem completeRoundReward_eq_actualRecord (q : Fin p.T) (z : Source)
    (r : Record) (hr : recordAt q z = some r) :
    ReferenceCompletePhysicalRewards.completeRoundReward rate z rewards C_star C_h q =
      r.totalReward := by
  obtain ⟨i, hi, hir, hstart⟩ := ReferencePostInvocationGeneratedAlignment.actualRecord_index
    rate rewards C_star C_h q z r hr
  cases hl : ReferenceCorrectedInitializationLaunch.correctedLaunch rate z rewards C_star C_h with
  | none =>
    have hs := ReferenceCompletePhysicalHistory.correctedLaunch_none_start_eq_T
      rate z rewards C_star C_h hl
    have := q.isLt
    omega
  | some active =>
    let offset : Fin (p.T - start z) := ⟨q.val - start z, by
      have := q.isLt
      omega⟩
    have hq : (⟨start z + offset.val, by
        have := q.isLt
        dsimp only [offset]
        omega⟩ : Fin p.T) = q := by
      apply Fin.ext
      dsimp only [offset]
      omega
    have he := ReferenceCompletePhysicalRewards.completeRoundReward_eq_suffixRecord_totalReward
      rate z rewards C_star C_h active hl offset
    rw [hq] at he
    have hn : ReferenceCorrectedInitializationLaunch.correctedLaunch rate z rewards C_star C_h ≠ none := by
      rw [hl]
      exact Option.some_ne_none _
    have hrecords : ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h =
        (ReferenceCompletePhysicalHistory.correctedSuffixRun rate z rewards C_star C_h hn).records := by
      rw [ReferenceCompletePhysicalHistory.completeSuffixRecords, dite_eq_right hn]
    have hiq : i.val = offset.val := by
      dsimp only [offset]
      omega
    have hlookup := congrArg (fun L : List Record => L[offset.val]?) hrecords
    rw [← hiq, List.getElem?_eq_getElem i.isLt, hir] at hlookup
    have hget : (ReferenceCompletePhysicalHistory.correctedSuffixRun rate z rewards C_star C_h hn).records.get
        ⟨offset.val, by
          rw [ReferenceCompletePhysicalHistory.correctedSuffixRun_record_count]
          exact offset.isLt⟩ = r := by
      simpa only [List.get_eq_getElem, hiq] using (List.getElem?_eq_some_iff.mp hlookup.symm).2
    rw [hget] at he
    exact he

private theorem not_live_of_collection_call (r : Record)
    (sel : ReferenceActivePhysicalStep.Selection r.input)
    (hsel : r.output.preparation.coordinator.selection = some sel)
    (hc : (ReferenceLaterCollectionArrivalReadout.laterCollectionCall 0 r).isSome = true) :
    ¬ CoordinatorLocalArmChoice.assignmentIsLive sel.view.payload sel.view.cutoff r.input.time := by
  have hf := ReferenceCoordinatorRecorderCallCorrespondence.actual_call_frames r
  unfold ReferenceLaterCollectionArrivalReadout.laterCollectionCall at hc
  split at hc
  · cases hd : r.output.preparation.coordinator with
    | first outcome => cases outcome <;> simp only [hd, Option.isSome_none, Bool.false_eq_true] at hc
    | live regs owned base outcome =>
        cases outcome <;> simp only [hd] at hc hsel hf
        all_goals try cases hc
        simp only [ReferenceActivePhysicalStep.DispatchCut.selection,
          ReferenceActivePhysicalStep.selectionAt, dite_true] at hsel
        have he := Option.some.inj hsel
        exact he ▸ hf.1
    | collection payload ledger clock cutoff outcome =>
        cases outcome <;> simp only [hd] at hc hsel hf
        all_goals try cases hc
        simp only [ReferenceActivePhysicalStep.DispatchCut.selection] at hsel
        have he := Option.some.inj hsel
        exact he ▸ hf.1
    | invalidCollectionCutoff => simp only [hd, Option.isSome_none, Bool.false_eq_true] at hc
    | dagger => simp only [hd, Option.isSome_none, Bool.false_eq_true] at hc
  · cases hc

/-- An actual first-prefix mark always uses a fast arm outside its own slow
set, including the prescribed post-overflow continuation. -/
theorem firstPast_fast_outside (z : Source) (a : Auxiliary) (n : Fin (p.T + 1))
    (e : Cell) (he : e ∈ past n (z, a)) : e.fastArm ∉ e.slowSet.val := by
  by_cases hlive : e ∈ liveCells (z, a)
  · obtain ⟨i, hi, hie⟩ := List.mem_iff_getElem.mp hlive
    have hiw : i < (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow rate rewards C_star C_h z).length := by
      simpa only [firstLiveChronologicalPrefix_length, ReferenceFirstLiveOverflowReadout.wholeFirstLiveLength] using hi
    rw [← hie, firstLiveChronologicalPrefix_get rate rewards C_star C_h z a ⟨i, hiw⟩]
    dsimp only [appendLogicalCell]
    split
    · exact frozenFastArm_not_mem p
    · exact (Finset.mem_sdiff.mp (reservedFastArm _ _).property).2
  · obtain ⟨_q, _r, _hr, _hm, _U, _hqn, _hU, _hen, _ht, _hp,
        _hn, _hb, _ha, _harr, _hservice, hs, hf, _hproposal, _hnext, _hall⟩ :=
      ReferenceFirstCollectionLogicalPrefixExtension.generated_collection_cell_fields
        rate rewards C_star C_h n z a e he hlive
    rw [hs, hf]
    split
    · exact frozenFastArm_not_mem p
    · exact (Finset.mem_sdiff.mp (ReferenceFirstCollectionOneRoundLogicalCell.actualFast
        rewards C_star C_h z _ _ _ _ _ _).property).2

/-- A first-prefix cell at an actual LIVE-empty date has the same slow set,
physical FAST action and signed reward. Numerical chronology alone is not
used to infer either action identity. -/
theorem firstPast_live_empty_payoff (z : Source)
    (hl : ∃ active, ReferenceCorrectedInitializationLaunch.correctedLaunch rate z rewards C_star C_h = some active)
    (a : Auxiliary) (n : Fin (p.T + 1)) (q : Fin p.T)
    (hq : q.val + 1 ≤ bad z) (e : Cell) (he : e ∈ past n (z, a)) (het : e.time = q)
    (r : Record) (hr : recordAt q z = some r)
    (sel : ReferenceActivePhysicalStep.Selection r.input)
    (hsel : r.output.preparation.coordinator.selection = some sel)
    (hgate : ReferenceActualLiveEmptySignedRewardCalendar.liveEmptyGate
      (ReferenceActiveHorizonMeasurability.roundRecordCode r)
      (ReferenceLiveDispatchOutputMeasurability.encodeSelection sel)) :
    e.before.overflow = false ∧ e.slowSet = sel.view.payload.slowSet ∧
      e.fastArm = r.actions (ActiveRoundActions.coordinator p.two_le_m) ∧
      ReferenceActualLiveEmptySignedRewardCalendar.observation rate rewards q e.physical =
        some (ReferenceGeneratedCalendarLivePayoff.logicalReward rate rewards e,
          r.totalReward, ReferenceGeneratedCalendarLivePayoff.logicalReward rate rewards e - r.totalReward) := by
  have hlive : CoordinatorLocalArmChoice.assignmentIsLive sel.view.payload sel.view.cutoff r.input.time := by
    have h := ReferenceCoordinatorRecorderCallTrace.live_eq_assignmentIsLive
      (ReferenceActiveHorizonMeasurability.roundRecordCode r)
      (ReferenceLiveDispatchOutputMeasurability.encodeSelection sel) r.input.time rfl
    rw [hgate.1] at h
    exact of_decide_eq_true h.symm
  have hem : e ∈ liveCells (z, a) := by
    by_contra hn
    obtain ⟨t, s, hs, hm, _U, _hqn, _hU, _hen, ht, _rest⟩ :=
      ReferenceFirstCollectionLogicalPrefixExtension.generated_collection_cell_fields
        rate rewards C_star C_h n z a e he hn
    have htq : t = q := ht.symm.trans het
    have hs' : recordAt q z = some s := htq ▸ hs
    have hsr : s = r := Option.some.inj (hs'.symm.trans hr)
    subst s
    obtain ⟨call, _ht, _hread, hc, _rest⟩ :=
      ReferenceFirstCollectionOneRoundLogicalCell.actual_data rewards C_star C_h z t r hs hm
    exact not_live_of_collection_call rate r sel hsel (by rw [hc]; rfl) hlive
  obtain ⟨i, hi, hie⟩ := List.mem_iff_getElem.mp hem
  have hiw : i < (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow rate rewards C_star C_h z).length := by
    simpa only [firstLiveChronologicalPrefix_length, ReferenceFirstLiveOverflowReadout.wholeFirstLiveLength] using hi
  let s := (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow rate rewards C_star C_h z)[i]
  let c := wholeLiveCell rate rewards C_star C_h z s (List.getElem_mem hiw)
  let S := RecordedQueueRun.run Q
    ((ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells rate rewards C_star C_h z).take i)
  have heq : e = appendLogicalCell s c S a :=
    hie.symm.trans (firstLiveChronologicalPrefix_get rate rewards C_star C_h z a ⟨i, hiw⟩)
  have hp := ReferenceGeneratedCalendarMarkedPath.firstPast_physical rate rewards C_star C_h z a n e he
  have hphysical : e.physical = ReferenceActiveHorizonMeasurability.roundRecordCode r := by
    obtain ⟨r', hr', hp⟩ := hp
    rw [het] at hr'
    exact hp.trans (congrArg ReferenceActiveHorizonMeasurability.roundRecordCode
      (Option.some.inj (hr'.symm.trans hr)))
  have hsr : s = r := by
    have htime : s.input.time = q := by rw [heq] at het; exact het
    have hpref : ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow rate rewards C_star C_h z <+:
        ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h := List.takeWhile_prefix _
    have hslookup : recordAt q z = some s := by
      have hidx := ReferenceFirstCollectionRenewalRecordingFeedback.complete_record_time rate z rewards C_star C_h i s
        (by rw [List.getElem?_eq_getElem (hiw.trans_le hpref.length_le), ← hpref.getElem hiw])
      have hival : q.val = start z + i := by rw [← htime]; exact hidx
      rw [ReferenceSourcePrefixHistoryFiltration.actualRecord, ite_eq_left (by omega), hival,
        Nat.add_sub_cancel_left, List.getElem?_eq_getElem (hiw.trans_le hpref.length_le), ← hpref.getElem hiw]
    exact Option.some.inj (hslookup.symm.trans hr)
  subst r
  have hcs : c.selected = sel := Option.some.inj (c.selection_actual.symm.trans hsel)
  obtain ⟨_i, _hi, _hir, hstart⟩ := ReferencePostInvocationGeneratedAlignment.actualRecord_index
    rate rewards C_star C_h q z s hr
  obtain ⟨_hk, _hen, _hnum, hb, _ha, _harr, _hservice, _hall⟩ :=
    ReferenceExhaustiveGeneratedCalendarSourceLaw.originalPast_cell_data
      rate rewards C_star C_h z hl a n e he
  have hS : prefixNumerical rate rewards C_star C_h q.castSucc z = some S := by
    rw [prefixNumerical_actualWord rate rewards C_star C_h q.castSucc z hl hstart]
    have heb : e.before = S := by rw [heq]; rfl
    rw [← heb, hb, het]
    rfl
  have hpre := ReferenceGeneratedCalendarLivePayoff.prefixNumerical_clear_of_inclusive_gate
    rate rewards C_star C_h q z S hS
    (ReferenceCompleteSignedFirstBadCalendar.inclusive_gate_through_first_bad_date rate rewards C_star C_h z q hq)
  have hpay := ReferenceGeneratedCalendarLivePayoff.appendLogicalCell_live_empty_payoff
    rate rewards C_star C_h q z s hr c S a hpre (by rw [hcs]; exact hgate.2)
  rw [heq]
  exact ⟨hpre, hpay.2.2.1.trans (congrArg (fun c => c.view.payload.slowSet) hcs),
    hpay.2.2.2.1, hpay.2.2.2.2.2⟩

/-- Before the first invocation, an actual LIVE selection retrieves an
actual first-prefix cell. Collection dates are excluded by the dispatcher's
own collection call, rather than by an assumed payoff law. -/
theorem firstPast_live_date (z : Source) (a : Auxiliary) (n : Fin (p.T + 1))
    (q : Fin p.T) (hqn : q.val < n.val)
    (hboundary : q.val < ReferenceFirstCollectionPrecallCalendarSupport.firstCallBoundary
      rate rewards C_star C_h z)
    (r : Record) (hr : recordAt q z = some r)
    (sel : ReferenceActivePhysicalStep.Selection r.input)
    (hsel : r.output.preparation.coordinator.selection = some sel)
    (hlive : CoordinatorLocalArmChoice.assignmentIsLive sel.view.payload sel.view.cutoff r.input.time) :
    ∃ e ∈ past n (z, a), e.time = q := by
  obtain ⟨j, hj, hjr, hstart⟩ := ReferencePostInvocationGeneratedAlignment.actualRecord_index
    rate rewards C_star C_h q z r hr
  have hcut : q.val < ReferenceFirstCollectionLogicalPrefixExtension.collectionStart rate rewards C_star C_h z := by
    by_contra h
    obtain ⟨s, hs, hm⟩ := ReferenceFirstCollectionLogicalPrefixExtension.actualDomain_of_collection_interval
      rate rewards C_star C_h q z (Nat.le_of_not_gt h) hboundary
    have hsr : s = r := Option.some.inj (hs.symm.trans hr)
    subst s
    obtain ⟨call, _ht, _hread, hc, _rest⟩ :=
      ReferenceFirstCollectionOneRoundLogicalCell.actual_data rewards C_star C_h z q r hr hm
    exact not_live_of_collection_call rate r sel hsel (by rw [hc]; rfl) hlive
  let W := ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow rate rewards C_star C_h z
  have hi : q.val - start z < W.length := by
    dsimp only [ReferenceFirstCollectionLogicalPrefixExtension.collectionStart,
      ReferenceFirstLiveOverflowReadout.wholeFirstLiveLength] at hcut
    dsimp only [W]
    omega
  let i : Fin W.length := ⟨q.val - start z, hi⟩
  let e := (liveCells (z, a))[i.val]'(by rw [firstLiveChronologicalPrefix_length]; exact i.isLt)
  have hpref : W <+: ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h := List.takeWhile_prefix _
  have hwr : W[i.val] = r := by
    have he := hpref.getElem i.isLt
    have hiq : i.val = j.val := by dsimp only [i]; omega
    exact he.trans (by simpa only [hiq] using hjr)
  have htime : e.time = q := by
    have ht := ReferenceFirstLiveChronologicalPrefixCausality.firstLiveChronologicalPrefix_cellTime
      rate rewards C_star C_h z a i
    change e.time = W[i.val].input.time at ht
    rw [hwr] at ht
    exact ht.trans (ReferenceCalendarLaterSamplerOutputSections.actualRecord_fields
      rate rewards C_star C_h q z r hr).2.2.1
  refine ⟨e, ?_, htime⟩
  apply (ReferenceFirstCollectionLogicalPrefixExtension.extendedPrefixStateAux_prefix
    rate rewards C_star C_h n.val (Nat.le_of_lt_succ n.isLt) (q.val + 1)
    (by omega) (z, a)).subset
  rw [ReferenceFirstCollectionLogicalPrefixExtension.extendedPrefixStateAux_before_collectionStart
    rate rewards C_star C_h (q.val + 1) (by omega) z a (by omega),
    ReferenceFirstLiveChronologicalPrefixCausality.calendarPast_eq_take_elapsed]
  apply List.mem_take_iff_getElem.mpr
  refine ⟨i.val, lt_min ?_ ?_, rfl⟩
  · dsimp only [i]; omega
  · rw [firstLiveChronologicalPrefix_length]; exact i.isLt

/-- An inclusive pre-first-bad date cannot lie in the initially stopped
suffix: that suffix's real numerical PRE already contains the earlier
overflow update. -/
theorem initialStopped_before_root (u t q : Fin p.T)
    (z : ReferenceInitialStoppedCalendar.StoppedSource rate rewards C_star C_h u t)
    (hq : q.val + 1 ≤ bad z.val) : q.val < t.val := by
  by_contra h
  have htq : t.val ≤ q.val := Nat.le_of_not_gt h
  let S := ReferenceInitialStoppedCalendar.suffixBefore rate rewards C_star C_h u t q z
  have hd := ReferenceFirstCollectionLogicalNumericalAlignment.firstCall_dates
    rate rewards C_star C_h u t z.val z.property.1.1
  have hpre : prefixNumerical rate rewards C_star C_h q.castSucc z.val = some S := by
    rw [prefixNumerical_actualWord rate rewards C_star C_h q.castSucc z.val
      (ReferenceFirstCollectionLogicalNumericalAlignment.firstCall_launch
        rate rewards C_star C_h u t z.val z.property.1.1) (by
          change start z.val ≤ q.val
          omega)]
    rfl
  have hclear := ReferenceGeneratedCalendarLivePayoff.prefixNumerical_clear_of_inclusive_gate
    rate rewards C_star C_h q z.val S hpre
    (ReferenceCompleteSignedFirstBadCalendar.inclusive_gate_through_first_bad_date
      rate rewards C_star C_h z.val q hq)
  have hstop := ReferenceInitialStoppedCalendar.suffixBefore_stopped rate rewards C_star C_h u t q htq z
  rw [hclear] at hstop
  exact Bool.false_ne_true hstop

variable (control0 : ContinuousLearningRows.TimeControl p)

open ReferenceExhaustiveGeneratedCalendarSourceLaw

/-- The omitted no-call and initially-stopped cases, together with the
accepted generated case, give the actual LIVE-empty payoff on FINAL `Z`.
The original tape and all terminal components are retained. -/
theorem terminal_live_empty_payoff (w : Omega rate rewards C_star C_h)
    (q : Fin p.T) (hq : q.val + 1 ≤ bad (terminalSource rate rewards C_star C_h control0 w))
    (r : Record) (hr : recordAt q (terminalSource rate rewards C_star C_h control0 w) = some r)
    (sel : ReferenceActivePhysicalStep.Selection r.input)
    (hsel : r.output.preparation.coordinator.selection = some sel)
    (hgate : ReferenceActualLiveEmptySignedRewardCalendar.liveEmptyGate
      (ReferenceActiveHorizonMeasurability.roundRecordCode r)
      (ReferenceLiveDispatchOutputMeasurability.encodeSelection sel)) :
    ∃ e ∈ (terminalReadout rate rewards C_star C_h control0 w).2.2,
      e.time = q ∧ e.physical = ReferenceActiveHorizonMeasurability.roundRecordCode r ∧
      e.before.overflow = false ∧ e.slowSet = sel.view.payload.slowSet ∧
      e.fastArm = r.actions (ActiveRoundActions.coordinator p.two_le_m) ∧
      ReferenceActualLiveEmptySignedRewardCalendar.observation rate rewards q e.physical =
        some (ReferenceGeneratedCalendarLivePayoff.logicalReward rate rewards e,
          r.totalReward, ReferenceGeneratedCalendarLivePayoff.logicalReward rate rewards e - r.totalReward) := by
  have hlive : CoordinatorLocalArmChoice.assignmentIsLive sel.view.payload sel.view.cutoff r.input.time := by
    have h := ReferenceCoordinatorRecorderCallTrace.live_eq_assignmentIsLive
      (ReferenceActiveHorizonMeasurability.roundRecordCode r)
      (ReferenceLiveDispatchOutputMeasurability.encodeSelection sel) r.input.time rfl
    rw [hgate.1] at h
    exact of_decide_eq_true h.symm
  rcases w with ⟨i, w⟩
  cases i with
  | noCall =>
    change recordAt q w.1.val = some r at hr
    have hl := actualRecord_has_launch rate rewards C_star C_h q w.1.val r hr
    obtain ⟨e, he, het⟩ := firstPast_live_date rate rewards C_star C_h w.1.val w.2 (Fin.last p.T)
      q q.isLt (by
        rw [ReferenceFirstCollectionPrecallCalendarSupport.firstCallBoundary, w.1.property]
        exact q.isLt) r hr sel hsel hlive
    have hp := firstPast_live_empty_payoff rate rewards C_star C_h w.1.val hl w.2
      (Fin.last p.T) q hq e he het r hr sel hsel hgate
    obtain ⟨s, hs, hphysical⟩ := ReferenceGeneratedCalendarMarkedPath.firstPast_physical
      rate rewards C_star C_h w.1.val w.2 (Fin.last p.T) e he
    rw [het] at hs
    have hsr : s = r := Option.some.inj (hs.symm.trans hr)
    exact ⟨e, he, het, hphysical.trans (congrArg _ hsr), hp⟩
  | stopped u t =>
    change recordAt q w.1.val = some r at hr
    have hqt := initialStopped_before_root rate rewards C_star C_h u t q w.1 hq
    have hbound := ReferenceFirstCollectionPrecallCalendarSupport.firstCallBoundary_on_firstCell
      rate rewards C_star C_h u t w.1.val w.1.property.1.1
    obtain ⟨e, he, het⟩ := firstPast_live_date rate rewards C_star C_h w.1.val w.2 t.castSucc q hqt
      (by rw [hbound]; exact hqt) r hr sel hsel hlive
    have hl := ReferenceFirstCollectionLogicalNumericalAlignment.firstCall_launch
      rate rewards C_star C_h u t w.1.val w.1.property.1.1
    have hp := firstPast_live_empty_payoff rate rewards C_star C_h w.1.val hl w.2
      t.castSucc q hq e he het r hr sel hsel hgate
    have hem := (ReferenceInitialStoppedCalendar.initialStoppedPast_retains_prefix
      rate rewards C_star C_h control0 u t (Fin.last p.T) t.isLt.le w).subset he
    obtain ⟨s, hs, hphysical⟩ := ReferenceGeneratedCalendarMarkedPath.firstPast_physical
      rate rewards C_star C_h w.1.val w.2 t.castSucc e he
    rw [het] at hs
    have hsr : s = r := Option.some.inj (hs.symm.trans hr)
    exact ⟨e, hem, het, hphysical.trans (congrArg _ hsr), hp⟩
  | generated b u t =>
    obtain ⟨_hscan, e, he, het, hphysical, hpre, hslow, hfast, _hd, hobs⟩ :=
      ReferenceGeneratedCalendarLivePayoff.calendar_all_live_empty_payoff
        rate rewards C_star C_h control0 b u t (p.T - (t.val + 1)) (by omega) w
        q (by have := q.isLt; omega) hq r hr sel hsel hgate
    exact ⟨e, he, het, hphysical, hpre, hslow, hfast, hobs⟩

private theorem appendLogicalCell_fast_outside (r : Record)
    (c : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell r)
    (S : RecordedQueueRun.RunState p.K) (a : Auxiliary) :
    (appendLogicalCell r c S a).fastArm ∉ (appendLogicalCell r c S a).slowSet.val := by
  dsimp only [appendLogicalCell]
  split
  · exact frozenFastArm_not_mem p
  · exact (Finset.mem_sdiff.mp (reservedFastArm r c).property).2

private theorem laterCollectionCell_fast_outside (q : Fin p.T)
    (z : CollectionDateSource rate rewards C_star C_h q) (U : SlowSet p) (a : Auxiliary) :
    (laterCollectionCell rate rewards C_star C_h q z U a).fastArm ∉
      (laterCollectionCell rate rewards C_star C_h q z U a).slowSet.val := by
  dsimp only [laterCollectionCell]
  split
  · exact frozenFastArm_not_mem p
  · exact (Finset.mem_sdiff.mp (collectionFastDraw rate _ _ _ _ U _).property).2

/-- Fast/slow separation is proved from every real constructor, rather than
being supplied as a property of an arbitrary numerical archive. -/
theorem terminal_fast_outside (w : Omega rate rewards C_star C_h) (e : Cell)
    (he : e ∈ (terminalReadout rate rewards C_star C_h control0 w).2.2) :
    e.fastArm ∉ e.slowSet.val := by
  rcases w with ⟨i, w⟩
  cases i with
  | noCall => exact firstPast_fast_outside rate rewards C_star C_h w.1.val w.2 (Fin.last p.T) e he
  | stopped u t =>
    by_cases het : e.time.val < t.val
    · exact firstPast_fast_outside rate rewards C_star C_h w.1.val w.2 t.castSucc e
        (stoppedPast_strict_prefix rate rewards C_star C_h control0 u t w (Fin.last p.T) e he het)
    · obtain ⟨_hen, heq⟩ := ReferenceInitialStoppedCalendar.initialStoppedPast_suffix_fields
        rate rewards C_star C_h control0 u t (Fin.last p.T) w e he (Nat.le_of_not_gt het)
      rw [heq]
      exact frozenFastArm_not_mem p
  | generated b u t =>
    rcases ReferenceGeneratedCalendarMarkedPath.calendar_mark_origins
      rate rewards C_star C_h control0 b u t _ _ w e he with hp | hr | ⟨j, hj, hstep⟩
    · exact firstPast_fast_outside rate rewards C_star C_h _ _ t.castSucc e hp
    · obtain ⟨z, _hz, rfl⟩ := hr
      exact appendLogicalCell_fast_outside rate _ _ _ _
    · rcases hstep with ⟨z, _hz, _hc, rfl⟩ | ⟨_hc, hec⟩
      · exact appendLogicalCell_fast_outside rate _ _ _ _
      · rcases ReferenceGeneratedCalendarMarkedPath.noncallDateCell_constructor
          rate rewards C_star C_h _ _ _ _ e hec with ⟨hz, rfl⟩ | ⟨hz, _hen, rfl⟩
        · exact appendLogicalCell_fast_outside rate _ _ _ _
        · exact laterCollectionCell_fast_outside rate rewards C_star C_h _ _ _ _

private theorem date_filter_singleton (H : List Cell)
    (hH : H.Pairwise (fun e f => e.time.val < f.time.val))
    (e : Cell) (he : e ∈ H) (q : Fin p.T) (het : e.time = q) :
    H.filter (fun f => f.time == q) = [e] := by
  induction H with
  | nil => exact (List.not_mem_nil he).elim
  | cons f H ih =>
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hH
    by_cases hf : f.time = q
    · have hnot (g : Cell) (hg : g ∈ H) : g.time ≠ q := by
        have hlt := hhead g hg
        intro h
        rw [hf, h] at hlt
        exact (Nat.lt_irrefl _ hlt)
      have heq : e = f := by
        rcases List.mem_cons.mp he with h | h
        · exact h
        · exact (hnot e h het).elim
      have hnil : H.filter (fun g => g.time == q) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro g hg
        simpa only [beq_iff_eq] using hnot g hg
      simp only [List.filter_cons, beq_iff_eq, hf, ite_true, hnil, heq]
    · have hem : e ∈ H := (List.mem_cons.mp he).resolve_left (fun h => hf (h ▸ het))
      simp only [List.filter_cons, beq_iff_eq, hf, ite_false]
      exact ih htail hem

/-- The literal archive reward at a present date equals that unique cell's
reward. No decoder or numerical stopping is applied to the filter. -/
theorem dateAuxiliaryReward_eq_cell (w : Omega rate rewards C_star C_h)
    (q : Fin p.T) (e : Cell)
    (he : e ∈ (terminalReadout rate rewards C_star C_h control0 w).2.2) (het : e.time = q) :
    dateAuxiliaryReward rate rewards (terminalReadout rate rewards C_star C_h control0 w).2.2 q =
      ReferenceInitialStoppedCalendar.cellReward rate rewards e := by
  rw [dateAuxiliaryReward, date_filter_singleton rate _
    (terminalReadout_chronology rate rewards C_star C_h control0 w) e he q het]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]

private theorem row_set_reward_le_support (q : Fin p.T) (S : Finset (Fin p.K)) :
    (∑ a ∈ S, (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards q).val a) ≤
      ((ReferenceActualLiveEmptySignedRewardCalendar.positiveArms rewards q).card : ℝ) := by
  let row := ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards q
  calc
    (∑ a ∈ S, row.val a) = ∑ a ∈ S.filter (fun a => 0 < row.val a), row.val a := by
      rw [← Finset.sum_filter_of_ne (p := fun a => 0 < row.val a)
        (fun a _ha hne => lt_of_le_of_ne (row.property a).1 (Ne.symm hne))]
    _ ≤ ∑ _a ∈ S.filter (fun a => 0 < row.val a), (1 : ℝ) :=
      Finset.sum_le_sum (fun a _ha => (row.property a).2)
    _ = ((S.filter (fun a => 0 < row.val a)).card : ℝ) := by simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ ((ReferenceActualLiveEmptySignedRewardCalendar.positiveArms rewards q).card : ℝ) := by
      apply Nat.cast_le.mpr
      apply Finset.card_le_card
      intro a ha
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp ha).2⟩

/-- The actual comparator is bounded by the same capped whole-row support
charge used by the stopped transport observable. -/
theorem comparatorReward_bounds (S0 : ProductSetLaw.ProductSet p.K p.m) (q : Fin p.T) :
    0 ≤ comparatorReward rewards S0 q ∧
      comparatorReward rewards S0 q ≤ ReferenceActualLiveEmptySignedRewardCalendar.liveEmptyCap rewards q := by
  let row := ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards q
  have hcard : S0.val.card = p.m := (Finset.mem_powersetCard.mp S0.property).2
  have hnonneg : 0 ≤ ∑ a ∈ S0.val, row.val a :=
    Finset.sum_nonneg (fun a _ha => (row.property a).1)
  have hm : (∑ a ∈ S0.val, row.val a) ≤ (p.m : ℝ) := by
    calc
      _ ≤ ∑ _a ∈ S0.val, (1 : ℝ) := Finset.sum_le_sum (fun a _ha => (row.property a).2)
      _ = p.m := by simp only [Finset.sum_const, nsmul_eq_mul, mul_one, hcard]
  exact ⟨hnonneg, le_min hm (row_set_reward_le_support rewards q S0.val)⟩

/-- Capped support also bounds every actual auxiliary action, including the
prescribed bounded continuation after the first overflow UPDATE. -/
theorem terminal_cellReward_le_cap (w : Omega rate rewards C_star C_h) (e : Cell)
    (he : e ∈ (terminalReadout rate rewards C_star C_h control0 w).2.2) :
    ReferenceInitialStoppedCalendar.cellReward rate rewards e ≤
      ReferenceActualLiveEmptySignedRewardCalendar.liveEmptyCap rewards e.time := by
  have hf := terminal_fast_outside rate rewards C_star C_h control0 w e he
  have hs : ReferenceInitialStoppedCalendar.cellReward rate rewards e =
      ∑ a ∈ insert e.fastArm e.slowSet.val,
        (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards e.time).val a := by
    rw [Finset.sum_insert hf]
    change (∑ a ∈ e.slowSet.val, _) + _ = _ + ∑ a ∈ e.slowSet.val, _
    exact add_comm _ _
  exact le_min (cellReward_bounds rate rewards e).2
    (hs ▸ row_set_reward_le_support rewards e.time (insert e.fastArm e.slowSet.val))

/-- Actual nominal enabled dates, retaining dates after numerical freezing. -/
def enabledDates (z : Source) : Finset (Fin p.T) :=
  Finset.univ.filter (fun q => nominalEnabled rate rewards C_star C_h q z = true)

theorem dateAuxiliaryReward_bounds (w : Omega rate rewards C_star C_h) (q : Fin p.T) :
    0 ≤ dateAuxiliaryReward rate rewards (terminalReadout rate rewards C_star C_h control0 w).2.2 q ∧
      dateAuxiliaryReward rate rewards (terminalReadout rate rewards C_star C_h control0 w).2.2 q ≤
        ReferenceActualLiveEmptySignedRewardCalendar.liveEmptyCap rewards q := by
  by_cases hen : nominalEnabled rate rewards C_star C_h q
      (terminalSource rate rewards C_star C_h control0 w) = true
  · obtain ⟨e, he, het⟩ := (terminalReadout_enabled_iff rate rewards C_star C_h control0 w q).mpr hen
    rw [dateAuxiliaryReward_eq_cell rate rewards C_star C_h control0 w q e he het]
    exact ⟨(cellReward_bounds rate rewards e).1,
      het ▸ terminal_cellReward_le_cap rate rewards C_star C_h control0 w e he⟩
  · have hn : ((terminalReadout rate rewards C_star C_h control0 w).2.2).filter (fun e => e.time == q) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro e he
      have hne : e.time ≠ q := fun ht => hen
        ((terminalReadout_enabled_iff rate rewards C_star C_h control0 w q).mp ⟨e, he, ht⟩)
      simpa only [beq_iff_eq] using hne
    rw [dateAuxiliaryReward, hn]
    simp only [List.map_nil, List.sum_nil, le_refl, true_and]
    exact le_min (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- The complete signed auxiliary sum is exactly the full nominal-date sum.
In particular this does not use the retained numerical-learning dates. -/
theorem fullSignedAuxiliarySum_eq_signedGap (S0 : ProductSetLaw.ProductSet p.K p.m)
    (w : Omega rate rewards C_star C_h) :
    SignedStoppedRegretAccounting.fullSignedAuxiliarySum
      (enabledDates rate rewards C_star C_h (terminalSource rate rewards C_star C_h control0 w))
      (comparatorReward rewards S0)
      (dateAuxiliaryReward rate rewards (terminalReadout rate rewards C_star C_h control0 w).2.2) =
      signedGap rate rewards S0 (terminalReadout rate rewards C_star C_h control0 w).2.2 := by
  rw [terminalReadout_signedGap_eq_nominal_dates]
  unfold SignedStoppedRegretAccounting.fullSignedAuxiliarySum enabledDates
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro q _hq
  by_cases hen : nominalEnabled rate rewards C_star C_h q
      (terminalSource rate rewards C_star C_h control0 w) = true
  · obtain ⟨e, he, het⟩ := (terminalReadout_enabled_iff rate rewards C_star C_h control0 w q).mpr hen
    rw [ite_eq_left hen, ite_eq_left hen, dateAuxiliaryReward_eq_cell rate rewards C_star C_h control0 w q e he het]
    rw [dateSignedGap, date_filter_singleton rate _
      (terminalReadout_chronology rate rewards C_star C_h control0 w) e he q het]
    simp only [signedGap, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, het]
    rfl
  · rw [ite_eq_right hen, ite_eq_right hen]

theorem actualLaunchRound_eq_start_succ (z : Source) : launch z = start z + 1 := by
  exact (ReferenceFirstLiveInitialTransferStartFields.initial_transfer_start_fields rate rewards C_star C_h z).1

/-- There are no auxiliary entries before the actual generated launch,
including absent and terminal launches. -/
theorem enabledDates_after_launch (z : Source) (q : Fin p.T)
    (hq : q ∈ enabledDates rate rewards C_star C_h z) : launch z ≤ q.val + 1 := by
  have hen := (Finset.mem_filter.mp hq).2
  cases hr : recordAt q z with
  | none => simp only [nominalEnabled, hr, Option.bind_none, Option.any_none, Bool.false_eq_true] at hen
  | some r =>
    obtain ⟨_i, _hi, _hir, hstart⟩ := ReferencePostInvocationGeneratedAlignment.actualRecord_index
      rate rewards C_star C_h q z r hr
    rw [actualLaunchRound_eq_start_succ rate rewards C_star C_h z]
    omega

/-- The boundary observable is the actual strict-launch startup sum. -/
theorem startupReward_eq_startupComparatorCharge (z : Source)
    (S0 : ProductSetLaw.ProductSet p.K p.m) :
    SignedStoppedRegretAccounting.startupReward (comparatorReward rewards S0) (launch z) =
      ReferenceOriginalStartupFixedIDMean.startupComparatorCharge rate z rewards C_star C_h S0.val := by
  rw [ReferenceOriginalStartupFixedIDMean.startupComparatorCharge_eq_launch_sum]
  unfold SignedStoppedRegretAccounting.startupReward SignedStoppedRegretAccounting.startupRounds
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro q _hq
  change (if q.val + 1 < launch z then comparatorReward rewards S0 q else 0) =
    ∑ a ∈ S0.val, if q.val + 1 < launch z then ((rewards q a).val : ℝ) / (D p : ℝ) else 0
  by_cases hq : q.val + 1 < launch z
  · simp only [hq, ite_true, comparatorReward]
  · simp only [hq, ite_false, Finset.sum_const_zero]

private theorem actualRecord_at_suffix_index (z : Source)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).length) :
    let r := (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val]
    recordAt r.input.time z = some r := by
  dsimp only
  have ht := ReferenceFirstCollectionRenewalRecordingFeedback.complete_record_time
    rate z rewards C_star C_h k.val _ (List.getElem?_eq_getElem k.isLt)
  rw [ReferenceSourcePrefixHistoryFiltration.actualRecord, ite_eq_left (by omega), ht,
    Nat.add_sub_cancel_left, List.getElem?_eq_getElem k.isLt]

open ReferenceOriginalCalendarTransferPhaseCover

/-- The generic inclusive interval is exactly the actual stopped suffix
interval. The `Fin T` carrier already imposes the physical horizon. -/
theorem retainedSuffixDates_eq_roundsThroughBad (z : Source) :
    retainedSuffixDates rate rewards C_star C_h z =
      SignedStoppedRegretAccounting.roundsThroughBad p.T (launch z) (bad z) := by
  apply Finset.ext
  intro q
  constructor
  · intro hq
    have h := (Finset.mem_filter.mp hq).2
    change launch z ≤ q.val + 1 ∧ q.val + 1 ≤ min (bad z) p.T at h
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h.1, h.2.trans (min_le_left _ _)⟩
  · intro hq
    have h := (Finset.mem_filter.mp hq).2
    change launch z ≤ q.val + 1 ∧ q.val + 1 ≤ bad z at h
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h.1,
      le_min h.2 (Nat.succ_le_of_lt q.isLt)⟩

/-- The actual one-round charges sum to precisely `J_stop`, with its signed
release term unchanged. -/
theorem stoppedTransportCharge_eq_J_stop (z : Source) :
    SignedStoppedRegretAccounting.stoppedTransportCharge
      (actualDateCalendarCharge rate rewards C_star C_h z) (launch z) (bad z) =
      ReferenceOriginalStoppedTransportFixedIDMean.J_stop rate rewards C_star C_h z := by
  unfold SignedStoppedRegretAccounting.stoppedTransportCharge
  rw [← retainedSuffixDates_eq_roundsThroughBad rate rewards C_star C_h z,
    retained_suffix_dates_eq_calendar_projection]
  exact actual_calendar_projection_signed_sum_eq_phase_sum rate rewards C_star C_h z

/-- The source's stopped pointwise inequality, derived on the same actual
sample. Collection/handover use capped support and nonnegative physical
feedback; release uses its actual dated auxiliary-minus-physical diagnostic. -/
theorem prebad_round_accounting (S0 : ProductSetLaw.ProductSet p.K p.m)
    (w : Omega rate rewards C_star C_h) (q : Fin p.T)
    (hq : q ∈ SignedStoppedRegretAccounting.roundsThroughBad p.T
      (launch (terminalSource rate rewards C_star C_h control0 w))
      (bad (terminalSource rate rewards C_star C_h control0 w))) :
    let Z := terminalSource rate rewards C_star C_h control0 w
    let H := (terminalReadout rate rewards C_star C_h control0 w).2.2
    comparatorReward rewards S0 q -
        ReferenceCompletePhysicalRewards.completeRoundReward rate Z rewards C_star C_h q ≤
      (if q ∈ enabledDates rate rewards C_star C_h Z then
        comparatorReward rewards S0 q - dateAuxiliaryReward rate rewards H q else 0) +
      actualDateCalendarCharge rate rewards C_star C_h Z q := by
  dsimp only
  let Z := terminalSource rate rewards C_star C_h control0 w
  let H := (terminalReadout rate rewards C_star C_h control0 w).2.2
  have hret : q ∈ retainedSuffixDates rate rewards C_star C_h Z := by
    rw [retainedSuffixDates_eq_roundsThroughBad]
    exact hq
  have hqb : q.val + 1 ≤ bad Z := (Finset.mem_filter.mp hq).2.2
  have hy := (ReferenceCompletePhysicalRewards.completeRoundReward_bounds rate Z rewards C_star C_h q).1
  cases hobs : actualDateObservation rate rewards C_star C_h Z q with
  | none =>
    have hcharge : actualDateCalendarCharge rate rewards C_star C_h Z q =
        ReferenceActualLiveEmptySignedRewardCalendar.liveEmptyCap rewards q := by
      rw [actualDateCalendarCharge, hobs]
    change comparatorReward rewards S0 q -
        ReferenceCompletePhysicalRewards.completeRoundReward rate Z rewards C_star C_h q ≤
      (if q ∈ enabledDates rate rewards C_star C_h Z then
        comparatorReward rewards S0 q - dateAuxiliaryReward rate rewards H q else 0) +
      actualDateCalendarCharge rate rewards C_star C_h Z q
    rw [hcharge]
    by_cases hen : q ∈ enabledDates rate rewards C_star C_h Z
    · rw [ite_eq_left hen]
      have hell := (dateAuxiliaryReward_bounds rate rewards C_star C_h control0 w q).2
      change dateAuxiliaryReward rate rewards H q ≤ _ at hell
      linarith only [hell, hy]
    · rw [ite_eq_right hen, zero_add]
      exact (sub_le_self _ hy).trans (comparatorReward_bounds rewards S0 q).2
  | some obs =>
    obtain ⟨a, y, delta⟩ := obs
    have hrelease : q ∈ releasePhaseDates rate rewards C_star C_h Z :=
      (retained_actual_observation_phase_characterization rate rewards C_star C_h Z q hret).2.mp
        ⟨a, y, delta, hobs⟩
    obtain ⟨k, hk, selected, hselected, htime, _hdelta, _hcalendar⟩ :=
      actual_release_date_signed_diagnostic rate rewards C_star C_h Z q hrelease
    let r := (actualRecords rate rewards C_star C_h Z)[k.val]
    have hphase : actualReleaseSelection rate r := (Finset.mem_filter.mp hk).2.2
    obtain ⟨sel, hsel, hlive, hempty⟩ := hphase
    have heq : sel = selected := Option.some.inj (hsel.symm.trans hselected)
    subst selected
    have hr : recordAt q Z = some r := by
      have h := actualRecord_at_suffix_index rate rewards C_star C_h Z k
      change recordAt r.input.time Z = some r at h
      rw [htime] at h
      exact h
    have hgate : ReferenceActualLiveEmptySignedRewardCalendar.liveEmptyGate
        (ReferenceActiveHorizonMeasurability.roundRecordCode r)
        (ReferenceLiveDispatchOutputMeasurability.encodeSelection sel) := by
      refine ⟨?_, hempty⟩
      rw [ReferenceCoordinatorRecorderCallTrace.live_eq_assignmentIsLive _ _ r.input.time rfl]
      exact decide_eq_true hlive
    obtain ⟨e, he, het, hphysical, _hpre, _hslow, _hfast, hpay⟩ :=
      terminal_live_empty_payoff rate rewards C_star C_h control0 w q hqb r hr sel hsel hgate
    have hen : q ∈ enabledDates rate rewards C_star C_h Z :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (terminalReadout_enabled_iff rate rewards C_star C_h control0 w q).mp ⟨e, he, het⟩⟩
    have hell : dateAuxiliaryReward rate rewards H q =
        ReferenceGeneratedCalendarLivePayoff.logicalReward rate rewards e := by
      exact dateAuxiliaryReward_eq_cell rate rewards C_star C_h control0 w q e he het
    have hyp : ReferenceCompletePhysicalRewards.completeRoundReward rate Z rewards C_star C_h q = r.totalReward :=
      completeRoundReward_eq_actualRecord rate rewards C_star C_h q Z r hr
    have hactual : actualDateObservation rate rewards C_star C_h Z q =
        some (ReferenceGeneratedCalendarLivePayoff.logicalReward rate rewards e,
          r.totalReward, ReferenceGeneratedCalendarLivePayoff.logicalReward rate rewards e - r.totalReward) := by
      rw [actualDateObservation, hr]
      change ReferenceActualLiveEmptySignedRewardCalendar.observation rate rewards q
        (ReferenceActiveHorizonMeasurability.roundRecordCode r) = _
      rw [← hphysical]
      exact hpay
    change comparatorReward rewards S0 q -
        ReferenceCompletePhysicalRewards.completeRoundReward rate Z rewards C_star C_h q ≤
      (if q ∈ enabledDates rate rewards C_star C_h Z then
        comparatorReward rewards S0 q - dateAuxiliaryReward rate rewards H q else 0) +
      actualDateCalendarCharge rate rewards C_star C_h Z q
    rw [ite_eq_left hen, hell, hyp, actualDateCalendarCharge, hactual]
    exact le_of_eq (by ring)

/-- Pointwise physical reference accounting on the actual exhaustive sample.
All arrays, launch, first-bad date, phases, feedback and auxiliary actions
come from the SAME original execution and generated calendar. There are no
path-correctness, coverage, payoff or prebad-inequality inputs. -/
theorem reference_accounting (S0 : ProductSetLaw.ProductSet p.K p.m)
    (w : Omega rate rewards C_star C_h) :
    let Z := terminalSource rate rewards C_star C_h control0 w
    let H := (terminalReadout rate rewards C_star C_h control0 w).2.2
    (∑ q : Fin p.T, ∑ a ∈ S0.val, ((rewards q a).val : ℝ) / (D p : ℝ)) -
        ReferenceCompletePhysicalRewards.completeReward rate Z rewards C_star C_h ≤
      ReferenceOriginalStartupFixedIDMean.startupComparatorCharge rate Z rewards C_star C_h S0.val +
        signedGap rate rewards S0 H +
        ReferenceOriginalStoppedTransportFixedIDMean.J_stop rate rewards C_star C_h Z +
        2 * (p.m : ℝ) * (p.T : ℝ) * SignedStoppedRegretAccounting.badWithinHorizon p.T (bad Z) := by
  dsimp only
  let Z := terminalSource rate rewards C_star C_h control0 w
  let H := (terminalReadout rate rewards C_star C_h control0 w).2.2
  let L := launch Z
  let b := bad Z
  let A := enabledDates rate rewards C_star C_h Z
  let c := comparatorReward rewards S0
  let ell := dateAuxiliaryReward rate rewards H
  let y := ReferenceCompletePhysicalRewards.completeRoundReward rate Z rewards C_star C_h
  let charge := actualDateCalendarCharge rate rewards C_star C_h Z
  have hc0 : ∀ q, 0 ≤ c q := fun q => (comparatorReward_bounds rewards S0 q).1
  have hcm : ∀ q, c q ≤ (p.m : ℝ) := fun q =>
    (comparatorReward_bounds rewards S0 q).2.trans (min_le_left _ _)
  have he0 : ∀ q, 0 ≤ ell q := fun q => (dateAuxiliaryReward_bounds rate rewards C_star C_h control0 w q).1
  have hem : ∀ q, ell q ≤ (p.m : ℝ) := fun q =>
    (dateAuxiliaryReward_bounds rate rewards C_star C_h control0 w q).2.trans (min_le_left _ _)
  have hy0 : ∀ q, 0 ≤ y q := fun q =>
    (ReferenceCompletePhysicalRewards.completeRoundReward_bounds rate Z rewards C_star C_h q).1
  have hym : ∀ q, y q ≤ (p.m : ℝ) := fun q =>
    (ReferenceCompletePhysicalRewards.completeRoundReward_bounds rate Z rewards C_star C_h q).2
  have hA : ∀ q ∈ A, L ≤ SignedStoppedRegretAccounting.calendarRound q :=
    fun q hq => enabledDates_after_launch rate rewards C_star C_h Z q hq
  have hL : 1 ≤ L ∧ L ≤ p.T + 1 :=
    ReferenceInitializationRun.launchRound_bounds
      (ReferenceCompletePhysicalHistory.generatedInput rate Z rewards C_star C_h)
  have hmain : SignedStoppedRegretAccounting.physicalCalendarRegret c y ≤
      SignedStoppedRegretAccounting.startupReward c L +
        SignedStoppedRegretAccounting.fullSignedAuxiliarySum A c ell +
        ReferenceOriginalStoppedTransportFixedIDMean.J_stop rate rewards C_star C_h Z +
        2 * (p.m : ℝ) * (p.T : ℝ) * SignedStoppedRegretAccounting.badWithinHorizon p.T b := by
    by_cases hLb : L ≤ b
    · have hpre : ∀ q ∈ SignedStoppedRegretAccounting.roundsThroughBad p.T L b,
          c q - y q ≤ (if q ∈ A then c q - ell q else 0) + charge q :=
        fun q hq => prebad_round_accounting rate rewards C_star C_h control0 S0 w q hq
      have h := SignedStoppedRegretAccounting.signed_stopped_accounting_internal_of_prebad
        L b A (ReferenceCompleteSignedFirstBadCalendar.badRounds rate rewards C_star C_h Z)
        c ell y charge hL hLb
        (ReferenceCompleteSignedFirstBadCalendar.firstBadDate_upper_bound rate rewards C_star C_h Z)
        (ReferenceCompleteSignedFirstBadCalendar.firstBadDate_firstBadCalendar rate rewards C_star C_h Z)
        hA hc0 hcm he0 hem hy0 hym hpre
      have hcharge := stoppedTransportCharge_eq_J_stop rate rewards C_star C_h Z
      change SignedStoppedRegretAccounting.stoppedTransportCharge charge L b = _ at hcharge
      rw [hcharge] at h
      exact h
    · have hbL : b < L := Nat.lt_of_not_ge hLb
      have hbT : b ≤ p.T := by omega
      have hstopEmpty : SignedStoppedRegretAccounting.roundsThroughBad p.T L b = ∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        intro q _hq hq
        change L ≤ q.val + 1 ∧ q.val + 1 ≤ b at hq
        omega
      have hJ : ReferenceOriginalStoppedTransportFixedIDMean.J_stop rate rewards C_star C_h Z = 0 := by
        rw [← stoppedTransportCharge_eq_J_stop rate rewards C_star C_h Z]
        change (∑ q ∈ SignedStoppedRegretAccounting.roundsThroughBad p.T L b, charge q) = 0
        rw [hstopEmpty, Finset.sum_empty]
      have htail : A.filter (fun q => b < SignedStoppedRegretAccounting.calendarRound q) = A := by
        apply Finset.filter_eq_self.mpr
        intro q hq
        have h := hA q hq
        omega
      have hnegative := SignedStoppedRegretAccounting.negative_auxiliary_tail_upper_bound_internal
        A b c ell hc0 hem
      rw [htail] at hnegative
      have hnegSum : (∑ q ∈ A, (ell q - c q)) =
          -SignedStoppedRegretAccounting.fullSignedAuxiliarySum A c ell := by
        unfold SignedStoppedRegretAccounting.fullSignedAuxiliarySum
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro q _hq
        ring
      rw [hnegSum, SignedStoppedRegretAccounting.badWithinHorizon, ite_eq_left hbT, mul_one] at hnegative
      have hphysical : SignedStoppedRegretAccounting.physicalCalendarRegret c y ≤
          (p.m : ℝ) * (p.T : ℝ) := by
        unfold SignedStoppedRegretAccounting.physicalCalendarRegret
        calc
          _ ≤ ∑ _q : Fin p.T, (p.m : ℝ) := by
            apply Finset.sum_le_sum
            intro q _hq
            exact (sub_le_self _ (hy0 q)).trans (hcm q)
          _ = (p.m : ℝ) * (p.T : ℝ) := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            exact mul_comm _ _
      have hstartup : 0 ≤ SignedStoppedRegretAccounting.startupReward c L :=
        Finset.sum_nonneg (fun q _hq => hc0 q)
      rw [hJ, add_zero, SignedStoppedRegretAccounting.badWithinHorizon, ite_eq_left hbT, mul_one]
      linarith only [hphysical, hstartup, hnegative]
  have hstart := startupReward_eq_startupComparatorCharge rate rewards C_star C_h Z S0
  have haux := fullSignedAuxiliarySum_eq_signedGap rate rewards C_star C_h control0 S0 w
  change SignedStoppedRegretAccounting.startupReward c L = _ at hstart
  change SignedStoppedRegretAccounting.fullSignedAuxiliarySum A c ell = _ at haux
  rw [hstart, haux] at hmain
  simpa only [SignedStoppedRegretAccounting.physicalCalendarRegret, Finset.sum_sub_distrib,
    c, comparatorReward, y, ReferenceCompletePhysicalRewards.completeReward] using hmain

/-- The same original-ID localization of the genuine raw terminal law.
Only its original positive ID atom is normalized; no success or future
branch event is conditioned upon. -/
theorem ae_reference_accounting (S0 : ProductSetLaw.ProductSet p.K p.m)
    (ids : Option (CompletePublicTable.IDArray p)) :
    ∀ᵐ w ∂ids.elim (terminalLaw rate rewards C_star C_h control0)
      (fixedIDTerminalLaw rate rewards C_star C_h control0),
    let Z := terminalSource rate rewards C_star C_h control0 w
    let H := (terminalReadout rate rewards C_star C_h control0 w).2.2
    (∑ q : Fin p.T, ∑ a ∈ S0.val, ((rewards q a).val : ℝ) / (D p : ℝ)) -
        ReferenceCompletePhysicalRewards.completeReward rate Z rewards C_star C_h ≤
      ReferenceOriginalStartupFixedIDMean.startupComparatorCharge rate Z rewards C_star C_h S0.val +
        signedGap rate rewards S0 H +
        ReferenceOriginalStoppedTransportFixedIDMean.J_stop rate rewards C_star C_h Z +
        2 * (p.m : ℝ) * (p.T : ℝ) * SignedStoppedRegretAccounting.badWithinHorizon p.T (bad Z) := by
  have hac : ids.elim (terminalLaw rate rewards C_star C_h control0)
      (fixedIDTerminalLaw rate rewards C_star C_h control0) ≪
        terminalLaw rate rewards C_star C_h control0 := by
    cases ids with
    | none => exact Measure.AbsolutelyContinuous.rfl
    | some ids =>
      dsimp only [Option.elim]
      rw [fixedIDTerminalLaw_eq_restrict]
      exact Measure.smul_absolutelyContinuous.trans Measure.absolutelyContinuous_restrict
  exact hac.ae_le (Filter.Eventually.of_forall
    (reference_accounting rate rewards C_star C_h control0 S0))

end Bandits.Support.ReferenceCompleteOriginalSignedAccounting

end
