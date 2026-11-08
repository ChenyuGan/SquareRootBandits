/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCompleteOrdinaryFalseEventObservableLocality
public import Bandits.Support.ReferenceGeneratedSavedWrongFixedIDMean

/-!
# Fixed-ID budget for the full ordinary false-completion event

The full calendar event includes ordinary prelaunch DOWN failures and the
saved postlaunch diagnostics. The prelaunch cohort is joined to the existing
generated DOWN envelope before the fixed-ID probability bounds are combined.
-/

public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.CompletePublicTable
open Bandits.Support.BootstrapPrivateRoundStreams

namespace Bandits.Support.ReferenceCompleteOrdinaryFalseFixedIDBudget

variable {p : Parameters}

/-- The full ordinary false-completion event on the original source carrier. -/
@[expose] def ordinaryWrongCompletionPrefixEvent
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (n : ℕ) : Set (SourceInput p) :=
  {z | ReferenceCompleteOrdinaryFalseEventObservableLocality.ordinaryWrongCompletionPrefix
    rate rewards C_star C_h n z}

/-- Exact calendar split of the actual full-source ordinary false-completion
prefix. The prelaunch scan remains present when the physical suffix is empty. -/
private theorem savedWrongRecordFlag_iff_savedWrongUniqueAccepted
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) :
    ReferenceGeneratedSavedWrongEvent.savedWrongRecordFlag r = true ↔
      ReferenceActiveStoppedPrefixCoupling.saved_wrong_unique_accepted r := by
  simp [ReferenceGeneratedSavedWrongEvent.savedWrongRecordFlag]

theorem ordinaryWrongCompletionPrefix_calendar_split
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (n : ℕ) (z : SourceInput p) :
    ReferenceCompleteOrdinaryFalseEventObservableLocality.ordinaryWrongCompletionPrefix
        rate rewards C_star C_h n z ↔
      (∃ t : Fin p.T, ∃ i : Fin (p.m - 1), t.val < n ∧
        ReferencePrelaunchDownDecisionReadout.prelaunchDownFailureAt
          rate rewards C_star C_h z i t = true) ∨
      z ∈ ReferenceGeneratedSavedWrongEvent.savedWrongSuffixPrefixEvent
        (r := rate) rewards C_star C_h
        (n - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h) := by
  unfold ReferenceCompleteOrdinaryFalseEventObservableLocality.ordinaryWrongCompletionPrefix
  constructor
  · rintro ⟨t, ht, hbad⟩
    rcases (ReferenceCompleteOrdinaryWrongCompletionCharacterization.ordinaryWrongCompletionAt_iff
      rate rewards C_star C_h t z).mp hbad with hpre | ⟨r, hrecord, hflag⟩
    · rcases hpre with ⟨i, hpre⟩
      exact Or.inl ⟨t, i, ht, hpre⟩
    · have hsavedRecord :=
        (savedWrongRecordFlag_iff_savedWrongUniqueAccepted (rate := rate) r).mp hflag
      have hsaved := (ReferenceStrictPastFailureCalendarAlignment.actualRecord_calendarPrefix_exists_iff
        rate rewards C_star C_h z n
        (fun r => ReferenceActiveStoppedPrefixCoupling.saved_wrong_unique_accepted r)).mp
        ⟨t, r, ht, hrecord, hsavedRecord⟩
      exact Or.inr ((ReferenceGeneratedSavedWrongEvent.savedWrongSuffixPrefixEvent_true_iff
        (rate := rate) rewards C_star C_h
        (n - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h) z).2
        hsaved)
  · rintro (⟨t, i, ht, hpre⟩ | hsaved)
    · refine ⟨t, ht, ?_⟩
      exact (ReferenceCompleteOrdinaryWrongCompletionCharacterization.ordinaryWrongCompletionAt_iff
        rate rewards C_star C_h t z).2 (Or.inl ⟨i, hpre⟩)
    · have hrecords :=
        (ReferenceGeneratedSavedWrongEvent.savedWrongSuffixPrefixEvent_true_iff
          (rate := rate) rewards C_star C_h
          (n - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h) z).1
          hsaved
      obtain ⟨t, r, ht, hrecord, hflag⟩ :=
        (ReferenceStrictPastFailureCalendarAlignment.actualRecord_calendarPrefix_exists_iff
          rate rewards C_star C_h z n
          (fun r => ReferenceActiveStoppedPrefixCoupling.saved_wrong_unique_accepted r)).2
          hrecords
      have hflag' :=
        (savedWrongRecordFlag_iff_savedWrongUniqueAccepted (rate := rate) r).mpr hflag
      refine ⟨t, ht, ?_⟩
      exact (ReferenceCompleteOrdinaryWrongCompletionCharacterization.ordinaryWrongCompletionAt_iff
          rate rewards C_star C_h t z).2
          (Or.inr ⟨r, hrecord, hflag'⟩)

private theorem prelaunch_failure_mem_downCohort
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (z : SourceInput p) (i : Fin (p.m - 1)) (r : Fin p.T)
    (hfail : ReferencePrelaunchDownDecisionReadout.prelaunchDownFailureAt
      rate rewards C_star C_h z i r = true) :
    z ∈ ReferenceGeneratedDownCohortFiniteUnion.downCohortUnionEvent
      rate rewards C_star C_h control0 (AffineBatchDecoder.quota p) := by
  classical
  obtain ⟨active, hpref, w, M, hraw, hlength, _hbatchOutput, hsolves,
      _hunique, _hparse, _hencode, _haccept⟩ :=
    ReferencePrelaunchDownDecisionReadout.prelaunchDownFailureAt_completedBatch
      rate rewards C_star C_h z i r hfail
  let x := ReferenceGeneratedPrelaunchDownPrefix.sourceReferenceInput
    rate rewards C_star C_h z
  let own := ReferenceInitializationRun.ownEntry
    (ReferenceInitializationRun.physical x active.val.1.val active.val.1.property.1)
    (PublicDiscreteDraws.followerPlayer p.two_le_m
      (ActualReferenceInitializationBlock.refFollower i)) r
  let bank := active.val.2.2.2.downBatch
  let tr := ReferencePrelaunchFollower.traceAt i x.row active.val.2.1 r own
  let B := bank.pending ++ AffineBatchDecoder.positiveAt p tr r
  let tests := ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix_tests
    rate rewards C_star C_h z i r
  let k := bank.completed.length

  have hEqAll : ∀ e ∈ B, AffineBatchDecoder.equation e.sample w :=
    (AffineBatchDecoder.satisfies_samples_iff B w).mp hsolves

  have hcensus := ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix_census
    rate rewards C_star C_h z i r
  rw [hpref] at hcensus
  dsimp only at hcensus
  rcases hcensus with ⟨_hmap, hpending, _hcompleted, hshort⟩
  change bank.pending.length < AffineBatchDecoder.quota p at hshort
  have hlenSum : bank.pending.length +
      (AffineBatchDecoder.positiveAt p tr r).length = AffineBatchDecoder.quota p := by
    simpa only [B, List.length_append] using hlength
  have hpositiveLe : (AffineBatchDecoder.positiveAt p tr r).length ≤ 1 := by
    simp only [AffineBatchDecoder.positiveAt]
    split <;> simp
  have hpositiveLen : (AffineBatchDecoder.positiveAt p tr r).length = 1 := by
    omega
  have hpendingLen : bank.pending.length = AffineBatchDecoder.quota p - 1 := by
    omega

  obtain ⟨active', hpref', test, htestShape, htestSent, _hnotSent,
      hpretest, hcurrent, _hcoordinatorLearner, _hcoordinatorAction,
      _hfollowerAction⟩ :=
    ReferencePrelaunchDownDecisionReadout.prelaunchDownFailureAt_currentAbsentWord
      rate rewards C_star C_h z i r hfail
  have hactiveEq : active' = active := by
    have h := hpref'.symm.trans hpref
    cases h
    rfl
  subst active'
  have hstep := ReferenceGeneratedPrelaunchDownCohortStep.source_prelaunch_down_active_step_census
    rate rewards C_star C_h z i r
  rw [hpref] at hstep
  dsimp only at hstep
  rcases hstep with ⟨_hstatus, _hstepShort, _hbatchLengths, _hstepPending,
    _hnext, _hbuffer, _hfailureBit, _hcurrentShape, hentryCurrent,
    _hineligible, _hquotaCases, _hunderQuota, _hatQuota, _hflags⟩
  have hcurrent' :
      ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_current_test
        rate rewards C_star C_h z i r = some test := hcurrent
  have hA : ReferenceGeneratedPrelaunchDownCurrentPair.A_r
      rate rewards C_star C_h z i r := by
    simp only [ReferenceGeneratedPrelaunchDownCurrentPair.A_r, hcurrent', Option.isSome_some]
  have hentryPos : ReferenceGeneratedPrelaunchDownCohort.testEntry test ∈
      AffineBatchDecoder.positiveAt p tr r := by
    rw [← hentryCurrent, hcurrent']
    simp
  have hentryBatch : ReferenceGeneratedPrelaunchDownCohort.testEntry test ∈ B := by
    change ReferenceGeneratedPrelaunchDownCohort.testEntry test ∈
      bank.pending ++ AffineBatchDecoder.positiveAt p tr r
    exact List.mem_append.mpr (Or.inr hentryPos)
  have hcurrentEquation := hEqAll (ReferenceGeneratedPrelaunchDownCohort.testEntry test)
    hentryBatch
  have hcurrentHash : AffineChannelLaw.affineHash test.sample w = 1 := by
    have heq := (AffineBatchDecoder.equation_iff_affineHash _ _).mp hcurrentEquation
    simpa only [ReferenceGeneratedPrelaunchDownCohort.testEntry] using heq
  have hhash : AffineChannelLaw.affineHash
      (((z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)).2 r).2 (0, i)) w = 1 := by
    have hsample : test.sample = (x.row.2 r).2 (0, i) := by
      rw [htestShape]
    have hxrow : x.row = z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) := by
      rfl
    rw [hsample, hxrow] at hcurrentHash
    exact hcurrentHash

  have hflags : List.Forall (fun flags => flags.1 ∧ flags.2)
      (ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_current_cohort_flags
        rate rewards C_star C_h z i r w) := by
    have hflagsDef :
        ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_current_cohort_flags
          rate rewards C_star C_h z i r w =
        (tests.map (fun test : ReferenceGeneratedDownBatchCalendar.ExecutedTest p =>
          (test.sent ≠ some w,
            AffineChannelLaw.affineHash test.sample w = 1))).drop
          (AffineBatchDecoder.quota p * k) := by
      simp only [ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_current_cohort_flags,
        hpref, tests, ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix_flags,
        k, bank]
    rw [hflagsDef, ← List.map_drop, List.forall_iff_forall_mem]
    intro flags hflagsMem
    rcases List.mem_map.mp hflagsMem with ⟨test, htest, rfl⟩
    have hsent : test.sent = none := by
      have htestFull := List.mem_of_mem_drop htest
      simp only [tests,
        ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix_tests,
        hpref] at htestFull
      rcases List.mem_filterMap.mp htestFull with ⟨u, _hu, hpretest'⟩
      unfold ReferenceGeneratedPrelaunchDownCohort.prelaunchTest at hpretest'
      split_ifs at hpretest'; cases hpretest'
      simp_all
    have hentryPending : ReferenceGeneratedPrelaunchDownCohort.testEntry test ∈ bank.pending := by
      rw [hpending, ← List.map_drop]
      exact List.mem_map.mpr ⟨test, htest, rfl⟩
    have hentryBatch' : ReferenceGeneratedPrelaunchDownCohort.testEntry test ∈ B := by
      change ReferenceGeneratedPrelaunchDownCohort.testEntry test ∈
        bank.pending ++ AffineBatchDecoder.positiveAt p tr r
      exact List.mem_append.mpr (Or.inl hentryPending)
    have heq := hEqAll (ReferenceGeneratedPrelaunchDownCohort.testEntry test) hentryBatch'
    have hhash' : AffineChannelLaw.affineHash test.sample w = 1 := by
      have h' := (AffineBatchDecoder.equation_iff_affineHash _ _).mp heq
      simpa only [ReferenceGeneratedPrelaunchDownCohort.testEntry] using h'
    exact ⟨by rw [hsent]; simp, hhash'⟩

  have hhistory :=
    ReferenceGeneratedPrelaunchDownHistoricalBirth.source_prelaunch_down_current_birth_history
      rate rewards C_star C_h z i r
  rw [hpref] at hhistory
  dsimp only at hhistory
  obtain ⟨beta, hBeta, hBetaR, hbankBirth, hbirth, _huniqueBirth⟩ := hhistory
  have hBetaLt : beta < p.T := lt_of_le_of_lt hBetaR r.isLt
  let alpha : Fin p.T := ⟨beta, hBetaLt⟩
  have hbirth' : ReferenceGeneratedPrelaunchDownPrefix.birthAt
      rate rewards C_star C_h z i alpha.val alpha.isLt.le k := by
    simpa only [alpha, k] using hbirth
  have hbankBirth' : ReferenceGeneratedPrelaunchDownPrefix.bankBirth
      active.val.2.1 bank = some alpha.val := by
    simpa only [alpha, bank] using hbankBirth
  have hordinal := ReferenceGeneratedDownCohortFiniteUnion.birthAt_ordinal_le
    rate rewards C_star C_h i alpha.val k alpha.isLt.le z hbirth'
  let kFin : Fin (alpha.val + 1) := ⟨k, by omega⟩

  have hhashed : ReferenceGeneratedPrelaunchDownOccurrenceTail.prelaunchDownHashedOccurrence
      rate rewards C_star C_h i alpha.val k (AffineBatchDecoder.quota p)
      alpha.isLt.le w z r := by
    change (ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_past_indicator
        rate rewards C_star C_h z i alpha.val k (AffineBatchDecoder.quota p)
        alpha.isLt.le r w ∧
      ReferenceGeneratedPrelaunchDownCurrentPair.A_r rate rewards C_star C_h z i r) ∧
      AffineChannelLaw.affineHash
        (((z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)).2 r).2 (0, i)) w = 1
    refine ⟨?_, hhash⟩
    refine ⟨?_, hA⟩
    simp only [ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_past_indicator,
      hpref]
    refine ⟨Nat.succ_le_of_lt (AffineBatchDecoder.quota_pos p), le_rfl,
      hBetaR, hbirth', ?_⟩
    exact ⟨rfl, hbankBirth', hpendingLen, hflags⟩

  have hmixed : z ∈ ReferenceGeneratedMixedDownPredecessor.mixedDownDetector
      rate rewards C_star C_h i alpha.val k alpha.isLt.le w control0
      (AffineBatchDecoder.quota p) := by
    have hqpos : 1 ≤ AffineBatchDecoder.quota p :=
      Nat.succ_le_of_lt (AffineBatchDecoder.quota_pos p)
    cases hq : AffineBatchDecoder.quota p with
    | zero => omega
    | succ q =>
      have hmixed' : z ∈ ReferenceGeneratedMixedDownPredecessor.mixedDownDetector
          rate rewards C_star C_h i alpha.val k alpha.isLt.le w control0 (q + 1) := by
        rw [ReferenceGeneratedMixedDownPredecessor.mixedDownDetector_positive
          rate rewards C_star C_h i alpha.val k (q + 1) alpha.isLt.le w
          (by omega) (by omega) control0]
        apply Or.inl
        rw [ReferenceGeneratedPrelaunchDownOccurrenceTail.prelaunchDownDetector_succ]
        exact ⟨r, by simpa [hq] using hhashed⟩
      simpa [hq] using hmixed'

  unfold ReferenceGeneratedDownCohortFiniteUnion.downCohortUnionEvent
  refine Set.mem_iUnion.mpr ⟨i, ?_⟩
  refine Set.mem_iUnion.mpr ⟨alpha, ?_⟩
  refine Set.mem_iUnion.mpr ⟨w, ?_⟩
  apply Or.inl
  refine Set.mem_iUnion.mpr ⟨kFin, ?_⟩
  simpa [kFin] using hmixed

private theorem ordinaryWrongCompletionPrefix_subset_downCohort_union_up
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (n : ℕ) :
    ordinaryWrongCompletionPrefixEvent rate rewards C_star C_h n ⊆
      ReferenceGeneratedDownCohortFiniteUnion.downCohortUnionEvent
          rate rewards C_star C_h control0 (AffineBatchDecoder.quota p) ∪
        ReferenceGeneratedUpFalseTail.generatedUpWrongSuffixPrefixEvent
          (r := rate) rewards C_star C_h p.T := by
  intro z herror
  change ReferenceCompleteOrdinaryFalseEventObservableLocality.ordinaryWrongCompletionPrefix
    rate rewards C_star C_h n z at herror
  rcases (ordinaryWrongCompletionPrefix_calendar_split rate rewards C_star C_h n z).mp
      herror with hpre | hsaved
  · rcases hpre with ⟨t, i, _ht, hfail⟩
    exact Or.inl (prelaunch_failure_mem_downCohort rate rewards C_star C_h control0 z i t hfail)
  · rcases (ReferenceStrictPastFailureCalendarAlignment.savedWrongSuffixPrefixEvent_expanded
      rate rewards C_star C_h z
      (n - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)).mp
      hsaved with hup | hdown
    · rcases hup with ⟨record, hrecord, diagnostic, hdiag, hwrong⟩
      have hrecordSuffix : record ∈
          ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h :=
        List.mem_of_mem_take hrecord
      have hlenSuffix :
          (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).length ≤
            p.T := by
        rw [ReferenceCompletePhysicalHistory.completeSuffixRecords_length]
        have hstart := ReferenceCompletePhysicalHistory.physicalStart_le_T
          rate z rewards C_star C_h
        omega
      have hrecordHorizon : record ∈
          (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).take p.T := by
        rw [List.take_of_length_le hlenSuffix]
        exact hrecordSuffix
      exact Or.inr
        ((ReferenceGeneratedUpFalseTail.generatedUpWrongSuffixPrefixEvent_true_iff
          (rate := rate) rewards C_star C_h p.T z).2
          ⟨record, hrecordHorizon, diagnostic, hdiag, hwrong⟩)
    · rcases hdown with ⟨record, hrecord, i, cut, hcut, hwrong⟩
      have hdownEvent :
          ReferenceGeneratedAllWrongDownEvent.generatedAllWrongDownSourceEvent
            rate rewards C_star C_h z := by
        rw [ReferenceGeneratedAllWrongDownEvent.generatedAllWrongDownSourceEvent_eq_completeSuffixEvent
          rate rewards C_star C_h]
        exact ⟨record, List.mem_of_mem_take hrecord, i, cut, hcut, hwrong⟩
      exact Or.inl
        (ReferenceGeneratedAllWrongDownEvent.generatedAllWrongDownSourceEvent_subset_downCohortUnion
          rate rewards C_star C_h control0 hdownEvent)

/-- The actual full ordinary false-completion event has the original
Dirac-ID probability budget, uniformly over every calendar prefix. -/
theorem ordinaryWrongCompletionPrefix_fixedID_measureReal_le
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (ids : IDArray p) (n : ℕ) :
    (((Measure.dirac ids).prod (completeRowsMeasure p)).prod
      (extendedPrivateLaw p)).real
        (ordinaryWrongCompletionPrefixEvent rate rewards C_star C_h n) ≤
      1 / (2 * (N p : ℝ) ^ 2) := by
  let ν := (((Measure.dirac ids).prod (completeRowsMeasure p)).prod
    (extendedPrivateLaw p))
  let downEvent := ReferenceGeneratedDownCohortFiniteUnion.downCohortUnionEvent
    rate rewards C_star C_h control0 (AffineBatchDecoder.quota p)
  let upEvent := ReferenceGeneratedUpFalseTail.generatedUpWrongSuffixPrefixEvent
    (r := rate) rewards C_star C_h p.T
  have hdownMeas := ReferenceGeneratedDownCohortFiniteUnion.measurableSet_downCohortUnionEvent
    rate rewards C_star C_h control0 (AffineBatchDecoder.quota p) le_rfl
  have _herrorMeas :=
    ReferenceCompleteOrdinaryFalseEventObservableLocality.ordinaryWrongCompletionPrefix_measurableSet
      rate rewards C_star C_h n
  have _hupMeas := ReferenceGeneratedUpFalseTail.measurableSet_generatedUpWrongSuffixPrefixEvent
    (rate := rate) rewards C_star C_h p.T
  have hdownEN : ν.real downEvent ≤ 1 / (4 * (N p : ℝ) ^ 2) := by
    let mass := CompletePublicTable.idArrayMeasure p {ids}
    have h := ReferenceGeneratedAllWrongDownFixedIDTail.downCohortUnionEvent_measure_le_geometric_id
      rate rewards C_star C_h control0 ids (AffineBatchDecoder.quota p) le_rfl
    have htransport := congrArg (fun μ : Measure (SourceInput p) => μ downEvent)
      (ReferenceGeneratedAllWrongDownFixedIDTail.sourceInputLaw_restrict_idCylinder ids)
    rw [Measure.restrict_apply hdownMeas] at htransport
    rw [Set.inter_comm] at htransport
    change ReferenceGeneratedDownCohortFiniteUnion.SourceLaw p
        (ReferenceGeneratedDownFreshIDLocalizedTail.idCylinder ids ∩ downEvent) =
      mass • ν downEvent at htransport
    rw [htransport,
      ReferenceGeneratedAllWrongDownFixedIDTail.sourceInputLaw_idCylinder ids] at h
    have hmass : 0 < mass.toReal :=
      ENNReal.toReal_pos
        (ReferenceGeneratedAllWrongDownFixedIDTail.idArrayMeasure_singleton_ne_zero ids)
        (measure_ne_top _ _)
    have hreal := ENNReal.toReal_mono (by finiteness) h
    simp only [smul_eq_mul, ENNReal.toReal_mul,
      ENNReal.toReal_pow, ENNReal.toReal_div, ENNReal.toReal_one,
      ENNReal.toReal_ofNat, ENNReal.toReal_natCast] at hreal
    have hnormalized : ν.real downEvent ≤
        ((((p.m - 1 : ℕ) : ℝ) * (p.T : ℝ) *
          (2 : ℝ) ^ AffineBatchDecoder.width p) *
          ((1 : ℝ) / 2) ^ AffineBatchDecoder.quota p) := by
      apply (mul_le_mul_iff_right₀ hmass).mp
      simpa only [mass, measureReal_def, mul_comm] using hreal
    have hfactor := ReferenceSuppressedDownTail.quota_union_factor_le p
    have hpow : ((1 : ℝ) / 2) ^ AffineBatchDecoder.quota p =
        (2 ^ AffineBatchDecoder.quota p : ℝ)⁻¹ := by
      rw [one_div, ← inv_pow]
    have hfactor' : ((((p.m - 1 : ℕ) : ℝ) * (p.T : ℝ) *
          (2 : ℝ) ^ AffineBatchDecoder.width p) *
          ((1 : ℝ) / 2) ^ AffineBatchDecoder.quota p) ≤
        1 / (4 * (N p : ℝ) ^ 2) := by
      rw [hpow]
      exact hfactor
    have hnormalized' := hnormalized.trans hfactor'
    simpa only [ν, downEvent] using hnormalized'
  have hup : ν.real upEvent ≤ 1 / (4 * (N p : ℝ) ^ 2) := by
    simpa only [ν, upEvent] using
      ReferenceGeneratedUpFalseFixedIDTail.generatedUpWrongSuffixPrefixEvent_fixedID_measureReal_le
        (rate := rate) rewards C_star C_h control0 p.T ids
  have hsubset := ordinaryWrongCompletionPrefix_subset_downCohort_union_up
    rate rewards C_star C_h control0 n
  have hmono : ν.real (ordinaryWrongCompletionPrefixEvent rate rewards C_star C_h n) ≤
      ν.real (downEvent ∪ upEvent) := measureReal_mono hsubset (by finiteness)
  have hsum : 1 / (4 * (N p : ℝ) ^ 2) + 1 / (4 * (N p : ℝ) ^ 2) =
      1 / (2 * (N p : ℝ) ^ 2) := by
    have hNpos : 0 < (N p : ℝ) := Nat.cast_pos.mpr (N_pos p)
    field_simp [ne_of_gt hNpos]
    ring
  calc
    _ ≤ ν.real (downEvent ∪ upEvent) := by
      simpa only [ν, downEvent, upEvent, ordinaryWrongCompletionPrefixEvent] using hmono
    _ ≤ ν.real downEvent + ν.real upEvent := measureReal_union_le _ _
    _ ≤ 1 / (4 * (N p : ℝ) ^ 2) + 1 / (4 * (N p : ℝ) ^ 2) := add_le_add hdownEN hup
    _ = 1 / (2 * (N p : ℝ) ^ 2) := hsum

end Bandits.Support.ReferenceCompleteOrdinaryFalseFixedIDBudget

end
