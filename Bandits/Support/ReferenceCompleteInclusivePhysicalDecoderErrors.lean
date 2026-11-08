/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCompleteAwaitedBatchSourceCoverage
public import Bandits.Support.ReferenceCompletePhysicalCalendarFirstCrossing
public import Bandits.Support.ReferenceCompleteOrdinaryFalseEventObservableLocality
public import Bandits.Support.ReferenceCompletePrefixReadoutRowLocality

/-!
# Inclusive physical stopping for the complete source decoder errors

The actual source events retain the ordinary saved wrong-completion and the
bidirectional fixed-awaited ambiguity predicates through the first physical
queue-overflow update.  The physical calendar continues to be defined beyond
that first update.
-/

@[expose] public section

noncomputable section

open MeasureTheory Bandits.Support
open Bandits.Support.ConstructorDimensions
open Bandits.Support.CompletePublicTable
open BootstrapPrivateRoundStreams (SourceInput)
open scoped Classical

namespace Bandits.Support.ReferenceCompleteInclusivePhysicalDecoderErrors

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev SourceInput (p : Parameters) := BootstrapPrivateRoundStreams.SourceInput p
abbrev QueueInput (p : Parameters) := RecordedQueueRun.RoundInput p.K
abbrev QueueReadout (p : Parameters) :=
  ReferenceFirstCollectionCurrentQueueReadout.QueueReadout p.K

variable {p : Parameters}

local instance sourceInputMeasurableSpace : MeasurableSpace (SourceInput p) := by
  change MeasurableSpace (CompletePublicTable.PublishedOutput p ×
    BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

local instance optionQueueReadoutMeasurableSpace :
    MeasurableSpace (Option (QueueReadout (p := p))) :=
  ReferenceInitializationMeasurability.optionCountableMeasurableSpace
    (QueueReadout (p := p))

local instance optionQueueReadoutMeasurableSingleton :
    MeasurableSingletonClass (Option (QueueReadout (p := p))) :=
  ReferenceInitializationMeasurability.optionCountableMeasurableSingletonClass
    (QueueReadout (p := p))

variable (rate : RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ)
variable (z : SourceInput p)

local notation "R" => ReferenceCompletePhysicalHistory.completeSuffixRecords
  rate z rewards C_star C_h
local notation "s" => ReferenceCompletePhysicalHistory.physicalStart
  rate z rewards C_star C_h
local notation "QP" => ReferenceFirstLaunchNumericalCell.queueParameters rate

/-- The actual inclusive scan at calendar date `t`: test every physical
post-update boundary no later than `t` on the original complete suffix.  Thus
the record at the first detector date is retained; its detecting post-update
boundary is the following date. -/
public def actualInclusivePhysicalScanGate
    (z : SourceInput p) (t : Fin p.T) : Prop :=
  ∀ h : ℕ, 1 ≤ h → h ≤
          (ReferenceCompletePhysicalHistory.completeSuffixRecords
            rate z rewards C_star C_h).length →
    ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + h ≤ t.val →
    ∀ a : Fin p.K,
      32 * (ReferenceCompletePhysicalCalendarQueueTruth.sourceCalendarReplay
        rate rewards C_star C_h z a h).2 ≤
          (ReferenceFirstLaunchNumericalCell.queueParameters rate).D

/-- The bounded numerical observer keeps missing optional prefixes absent.
Only a present prefix readout can witness overflow. -/
public def numericalOverflowBy
    (t : Fin p.T) (z : SourceInput p) : Prop :=
  ∃ n : ℕ, n ≤ t.val ∧ ∃ o : QueueReadout (p := p),
    ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout
      rate rewards C_star C_h n z = some o ∧
    ∃ a : Fin p.K,
      ((o.1 a).2 : ℝ) /
        ((ReferenceFirstLaunchNumericalCell.queueParameters rate).n : ℝ) >
          1 / (32 * rate.eta.val)

/-- The complete-source ordinary false-completion event with the literal
inclusive physical scan gate.  The ordinary predicate includes both actual
prelaunch decisions and saved suffix-record diagnostics. -/
public def stoppedOrdinaryWrongCompletionEvent : Set (SourceInput p) :=
  {z | ∃ t : Fin p.T,
    actualInclusivePhysicalScanGate rate rewards C_star C_h z t ∧
    ReferenceCompleteOrdinaryWrongCompletionCharacterization.ordinaryWrongCompletionAt
      rate rewards C_star C_h t z}

/-- The complete-source fixed-awaited ambiguity event with the same physical
scan gate, retaining both decoder directions and the original source bank. -/
public def stoppedFixedAwaitedAmbiguityEvent : Set (SourceInput p) :=
  {z | ∃ t : Fin p.T,
    actualInclusivePhysicalScanGate rate rewards C_star C_h z t ∧
    ReferenceCompleteAwaitedBatchSourceCoverage.sourceFixedAwaitedCompletionAt
      rate rewards C_star C_h z t}

/-- The two decoder error branches through the inclusive physical cutoff. -/
public def completeInclusiveDecoderFailureEvent : Set (SourceInput p) :=
  stoppedOrdinaryWrongCompletionEvent rate rewards C_star C_h ∪
    stoppedFixedAwaitedAmbiguityEvent rate rewards C_star C_h

/-- A present numerical prefix has no normalized overflow exactly when none
of its arm backlogs passes the manuscript's strict threshold. -/
public def noNumericalOverflowAt
    (n : ℕ) (z : SourceInput p) : Prop :=
  ∀ o : QueueReadout (p := p),
    ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout
      rate rewards C_star C_h n z = some o →
    ∀ a : Fin p.K,
      ¬ (((o.1 a).2 : ℝ) /
        ((ReferenceFirstLaunchNumericalCell.queueParameters rate).n : ℝ) >
          1 / (32 * rate.eta.val))

/-- Exact finite calendar scan of optional numerical readouts through `t`. -/
public def noNumericalOverflowThrough
    (t : Fin p.T) (z : SourceInput p) : Prop :=
  ∀ n : ℕ, n ≤ t.val → noNumericalOverflowAt rate rewards C_star C_h n z

theorem noNumericalOverflowAt_iff_not_numericalOverflowBy
    (n : ℕ) (z : SourceInput p) :
    noNumericalOverflowAt rate rewards C_star C_h n z ↔
      ¬ ∃ o : QueueReadout (p := p),
        ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout
          rate rewards C_star C_h n z = some o ∧
        ∃ a : Fin p.K,
          ((o.1 a).2 : ℝ) /
            ((ReferenceFirstLaunchNumericalCell.queueParameters rate).n : ℝ) >
              1 / (32 * rate.eta.val) := by
  simp only [noNumericalOverflowAt]
  constructor
  · intro h ⟨o, ho, a, ha⟩
    exact (h o ho a) ha
  · intro h o ho a ha
    exact h ⟨o, ho, a, ha⟩

theorem noNumericalOverflowThrough_iff_not_numericalOverflowBy
    (t : Fin p.T) (z : SourceInput p) :
    noNumericalOverflowThrough rate rewards C_star C_h t z ↔
      ¬ numericalOverflowBy rate rewards C_star C_h t z := by
  constructor
  · intro hnone ⟨n, hnt, o, ho, a, ha⟩
    exact ((noNumericalOverflowAt_iff_not_numericalOverflowBy
      rate rewards C_star C_h n z).mp (hnone n hnt)) ⟨o, ho, a, ha⟩
  · intro hnone n hnt o ho a ha
    apply hnone
    exact ⟨n, hnt, o, ho, a, ha⟩

/-- The literal gate agrees date by date with one fixed least physical
crossing. -/
private theorem actualInclusivePhysicalScanGate_iff_firstOverflowBoundary_of_data
    (t : Fin p.T) (L : List (QueueInput (p := p))) (H : ℕ)
    (hL : L.length = (R).length)
    (hH : H = UnstoppedRecordedQueueComparison.firstOverflowPrefix QP L)
    (hstates : ∀ h, h ≤ (R).length → ∀ a : Fin p.K,
      ReferenceCompletePhysicalCalendarQueueTruth.sourceCalendarReplay
        rate rewards C_star C_h z a (min h H) =
          (RecordedQueueRun.run QP (L.take h)).registers a) :
    actualInclusivePhysicalScanGate rate rewards C_star C_h z t ↔ t.val < s + H := by
  have hRlen : (R).length = p.T - s :=
    ReferenceCompletePhysicalHistory.completeSuffixRecords_length
      rate z rewards C_star C_h
  constructor
  · intro hgate
    by_contra hcut
    have hHboundR : H ≤ (R).length := by omega
    have hHboundL : H ≤ L.length := by rw [hL]; exact hHboundR
    have hcross := UnstoppedRecordedQueueComparison.replay_crosses_overflow_at_first
      QP L (by rw [← hH]; exact hHboundL)
    rcases hcross with ⟨a, hcross⟩
    have hcrossH :
        32 * (UnstoppedRecordedQueueComparison.unstoppedReplay QP L H a).2 >
          (QP).D := by
      rw [← hH] at hcross
      exact hcross
    have hstate := hstates H hHboundR a
    have hstateH :
        ReferenceCompletePhysicalCalendarQueueTruth.sourceCalendarReplay
          rate rewards C_star C_h z a H =
          (RecordedQueueRun.run QP (L.take H)).registers a := by
      simpa only [Nat.min_self] using hstate
    have hcomparison :=
      UnstoppedRecordedQueueComparison.prefix_state_comparison QP L H hHboundL
    have hmin : min H (UnstoppedRecordedQueueComparison.firstOverflowPrefix QP L) = H := by
      rw [← hH]
      exact min_self H
    have hrun :
        (RecordedQueueRun.run QP (L.take H)).registers a =
          UnstoppedRecordedQueueComparison.unstoppedReplay QP L H a := by
      simpa only [hmin] using hcomparison.1 a
    have hactualCross :
        32 * (ReferenceCompletePhysicalCalendarQueueTruth.sourceCalendarReplay
          rate rewards C_star C_h z a H).2 > (QP).D := by
      rw [hstateH, hrun]
      exact hcrossH
    have hfirstPos :=
      UnstoppedRecordedQueueComparison.first_overflow_prefix_pos QP L
    have hHpos : 1 ≤ H := by
      rw [← hH] at hfirstPos
      omega
    have hboundary : s + H ≤ t.val := le_of_not_gt hcut
    have hgateAt := hgate H hHpos hHboundR hboundary a
    exact (not_lt_of_ge hgateAt) hactualCross
  · intro hcut h hpos hlen hdate a
    have hhR : h ≤ (R).length := hlen
    have hhL : h ≤ L.length := by rw [hL]; exact hhR
    have hhfirst : h < H := by omega
    have hnotcross :=
      UnstoppedRecordedQueueComparison.not_replay_crosses_overflow_before_first
        QP L h hpos hhL (by rw [← hH]; exact hhfirst)
    have hstate := hstates h hhR a
    have hstateH :
        ReferenceCompletePhysicalCalendarQueueTruth.sourceCalendarReplay
          rate rewards C_star C_h z a h =
          (RecordedQueueRun.run QP (L.take h)).registers a := by
      have hmin : min h H = h := Nat.min_eq_left (Nat.le_of_lt hhfirst)
      simpa only [hmin] using hstate
    have hcomparison :=
      UnstoppedRecordedQueueComparison.prefix_state_comparison QP L h hhL
    have hmin : min h (UnstoppedRecordedQueueComparison.firstOverflowPrefix QP L) = h := by
      apply min_eq_left
      rw [← hH]
      exact Nat.le_of_lt hhfirst
    have hrun :
        (RecordedQueueRun.run QP (L.take h)).registers a =
          UnstoppedRecordedQueueComparison.unstoppedReplay QP L h a := by
      simpa only [hmin] using hcomparison.1 a
    have hbound :
        32 * (ReferenceCompletePhysicalCalendarQueueTruth.sourceCalendarReplay
          rate rewards C_star C_h z a h).2 ≤ (QP).D := by
      by_contra hbad
      apply hnotcross
      refine ⟨a, ?_⟩
      rw [← hrun, ← hstateH]
      exact Nat.lt_of_not_ge hbad
    exact hbound

/-- The literal gate agrees date by date with the least physical crossing.
When `H` is the first crossing prefix, the gate holds exactly through the
detector record date `s + H - 1`; it fails starting at the post-update
boundary `s + H`.  With no crossing, `H = suffix.length + 1` and all dates
pass. -/
theorem actualInclusivePhysicalScanGate_iff_firstOverflowBoundary
    (t : Fin p.T) :
    match ReferenceCorrectedInitializationLaunch.correctedLaunch
        rate z rewards C_star C_h with
    | none => actualInclusivePhysicalScanGate rate rewards C_star C_h z t
    | some _ =>
        ∃ L : List (QueueInput (p := p)), ∃ H : ℕ,
          H = UnstoppedRecordedQueueComparison.firstOverflowPrefix QP L ∧
          (actualInclusivePhysicalScanGate rate rewards C_star C_h z t ↔
            t.val < s + H) := by
  classical
  cases hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate z rewards C_star C_h with
  | none =>
      have hchar :=
        ReferenceCompletePhysicalCalendarFirstCrossing.actual_physical_first_overflow_characterization
          rate rewards C_star C_h z
      rw [hlaunch] at hchar
      rcases hchar with ⟨hword, _hsT, _hprefix, _hphysical, _hnumerical⟩
      have hwordlen :
          (ReferenceCompletePhysicalCalendarQueueTruth.actualPhysicalWord
            rate rewards C_star C_h z).length = 0 := by
        rw [hword]
        rfl
      have hRlen : (R).length = 0 := by
        rw [← ReferenceCompletePhysicalCalendarQueueTruth.actualPhysicalWord_length
          rate rewards C_star C_h z]
        exact hwordlen
      intro h hpos hlen hdate a
      rw [hRlen] at hlen
      omega
  | some active =>
      have hchar :=
        ReferenceCompletePhysicalCalendarFirstCrossing.actual_physical_first_overflow_characterization
          rate rewards C_star C_h z
      rw [hlaunch] at hchar
      rcases hchar with
        ⟨L, H, hL, hH, _hfinite, _hnoCross, hstates, _hword, _hterminal, _hdetector⟩
      exact ⟨L, H, hH,
        actualInclusivePhysicalScanGate_iff_firstOverflowBoundary_of_data
          rate rewards C_star C_h z t L H hL hH hstates⟩

/-- Exact finite-scan characterization of the literal physical gate by the
original optional numerical prefix readouts.  The first detecting update at
`q` is included through date `q`; its readout appears at `q + 1`. -/
theorem actualInclusivePhysicalScanGate_iff_noNumericalOverflowThrough
    (t : Fin p.T) :
    actualInclusivePhysicalScanGate rate rewards C_star C_h z t ↔
      noNumericalOverflowThrough rate rewards C_star C_h t z := by
  classical
  cases hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate z rewards C_star C_h with
  | none =>
      have hchar :=
        ReferenceCompletePhysicalCalendarFirstCrossing.actual_physical_first_overflow_characterization
          rate rewards C_star C_h z
      rw [hlaunch] at hchar
      rcases hchar with ⟨hword, _hsT, _hprefix, _hphysical, hnoObserved⟩
      have hRlen : (R).length = 0 := by
        have hwordlen :
            (ReferenceCompletePhysicalCalendarQueueTruth.actualPhysicalWord
              rate rewards C_star C_h z).length = 0 := by
          rw [hword]
          rfl
        rw [← ReferenceCompletePhysicalCalendarQueueTruth.actualPhysicalWord_length
          rate rewards C_star C_h z]
        exact hwordlen
      have hnoBy : ¬ numericalOverflowBy rate rewards C_star C_h t z := by
        intro ⟨n, hnt, o, ho, a, ha⟩
        apply hnoObserved
        exact ⟨n, by omega, o, ho, a, ha⟩
      have hnoNumerical :=
        (noNumericalOverflowThrough_iff_not_numericalOverflowBy
          rate rewards C_star C_h t z).2 hnoBy
      constructor
      · intro _
        exact hnoNumerical
      · intro _ h hpos hlen _ a
        rw [hRlen] at hlen
        omega
  | some active =>
      have hchar :=
        ReferenceCompletePhysicalCalendarFirstCrossing.actual_physical_first_overflow_characterization
          rate rewards C_star C_h z
      rw [hlaunch] at hchar
      rcases hchar with
        ⟨L, H, hL, hH, hfinite, _hnoCross, hstates, _hword, _hterminal, hdetector⟩
      have hRlen : (R).length = p.T - s :=
        ReferenceCompletePhysicalHistory.completeSuffixRecords_length
          rate z rewards C_star C_h
      have hgateCut :=
        actualInclusivePhysicalScanGate_iff_firstOverflowBoundary_of_data
          rate rewards C_star C_h z t L H hL hH hstates
      by_cases hHfinite : H ≤ (R).length
      · obtain ⟨q, hqdate, hqpost, hfirst⟩ := hdetector hHfinite
        rcases hfirst with
          ⟨Lq, r, c, arm, _hinputs, _hs, _hslast, _hlen, _hinputsNext,
            _hrecordSource, _hrecordTime, _hactualRecord, _hcell, _hbranch,
            _hread, hreadNext, _hbeforeOverflow, _henabled, _hafterOverflow,
            hthreshold, _hprior, _hpresent, hnoEarlier, _htransition⟩
        have hboundedBy :
            numericalOverflowBy rate rewards C_star C_h t z ↔ q.val + 1 ≤ t.val := by
          constructor
          · rintro ⟨n, hnt, o, ho, a, ha⟩
            by_contra hnot
            have hnlt : n < q.val + 1 := by omega
            exact hnoEarlier n hnlt ⟨o, ho, a, ha⟩
          · intro hpostle
            refine ⟨q.val + 1, hpostle,
              ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
                (RecordedQueueRun.step QP (RecordedQueueRun.run QP Lq) c),
              hreadNext, ?_⟩
            exact ⟨arm, hthreshold⟩
        have hgateCut' :
            actualInclusivePhysicalScanGate rate rewards C_star C_h z t ↔
              t.val < q.val + 1 := by
          rw [← hqpost] at hgateCut
          exact hgateCut
        have hnoBy :
            ¬ numericalOverflowBy rate rewards C_star C_h t z ↔
              t.val < q.val + 1 := by
          rw [hboundedBy]
          omega
        rw [noNumericalOverflowThrough_iff_not_numericalOverflowBy
          rate rewards C_star C_h t z]
        exact hgateCut'.trans hnoBy.symm
      · have hnoPhysical :
            z ∉ ReferenceCompletePhysicalCalendarFirstCrossing.physicalFirstOverflowEvent
              rate rewards C_star C_h := by
          intro hphysical
          exact hHfinite (hfinite.mpr hphysical)
        have hnoObserved :
            z ∉ ReferenceOriginalNumericalFirstOverflowLocator.observedNumericalOverflowEvent
              rate rewards C_star C_h := by
          rw [← ReferenceCompletePhysicalCalendarFirstCrossing.physicalFirstOverflowEvent_eq_observedNumericalOverflowEvent
            rate rewards C_star C_h]
          exact hnoPhysical
        have hnoBy : ¬ numericalOverflowBy rate rewards C_star C_h t z := by
          intro ⟨n, hnt, o, ho, a, ha⟩
          apply hnoObserved
          exact ⟨n, by omega, o, ho, a, ha⟩
        have hcut : t.val < s + H := by omega
        have hgate := hgateCut.mpr hcut
        have hnoNumerical :=
          (noNumericalOverflowThrough_iff_not_numericalOverflowBy
            rate rewards C_star C_h t z).2 hnoBy
        constructor
        · intro _
          exact hnoNumerical
        · intro _
          exact hgate

/-- The bounded original optional-prefix threshold is Borel on the complete
source measurable space.  Missing readouts contribute the empty set. -/
theorem measurableSet_numericalOverflowBy (t : Fin p.T) :
    MeasurableSet {z : SourceInput p |
      numericalOverflowBy rate rewards C_star C_h t z} := by
  have hrepr : {z : SourceInput p |
      numericalOverflowBy rate rewards C_star C_h t z} =
      ⋃ n : ℕ, ⋃ o : QueueReadout (p := p), ⋃ a : Fin p.K,
        if n ≤ t.val ∧
          ((o.1 a).2 : ℝ) /
            ((ReferenceFirstLaunchNumericalCell.queueParameters rate).n : ℝ) >
              1 / (32 * rate.eta.val)
        then {z | ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout
          rate rewards C_star C_h n z = some o} else ∅ := by
    ext z
    constructor
    · rintro ⟨n, hn, o, ho, a, ha⟩
      refine Set.mem_iUnion.mpr ⟨n, Set.mem_iUnion.mpr ⟨o,
        Set.mem_iUnion.mpr ⟨a, ?_⟩⟩⟩
      change z ∈ if n ≤ t.val ∧
        ((o.1 a).2 : ℝ) /
          ((ReferenceFirstLaunchNumericalCell.queueParameters rate).n : ℝ) >
            1 / (32 * rate.eta.val)
        then {z | ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout
          rate rewards C_star C_h n z = some o} else ∅
      rw [ite_eq_left ⟨hn, ha⟩]
      exact ho
    · intro hz
      rcases Set.mem_iUnion.mp hz with ⟨n, hz⟩
      rcases Set.mem_iUnion.mp hz with ⟨o, hz⟩
      rcases Set.mem_iUnion.mp hz with ⟨a, hz⟩
      by_cases htest : n ≤ t.val ∧
          ((o.1 a).2 : ℝ) /
            ((ReferenceFirstLaunchNumericalCell.queueParameters rate).n : ℝ) >
              1 / (32 * rate.eta.val)
      · rw [ite_eq_left htest] at hz
        change ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout
          rate rewards C_star C_h n z = some o at hz
        exact ⟨n, htest.1, o, hz, a, htest.2⟩
      · rw [ite_eq_right htest] at hz
        cases hz
  rw [hrepr]
  refine MeasurableSet.iUnion fun n => MeasurableSet.iUnion fun o =>
    MeasurableSet.iUnion fun a => ?_
  split_ifs with htest
  · exact (ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.measurable_prefixReadout
      rate rewards C_star C_h n) (measurableSet_singleton (some o))
  · exact MeasurableSet.empty

/-- The actual physical gate is Borel because its exact bounded-prefix
characterization uses the existing optional numerical readouts. -/
theorem measurableSet_actualInclusivePhysicalScanGate (t : Fin p.T) :
    MeasurableSet {z : SourceInput p |
      actualInclusivePhysicalScanGate rate rewards C_star C_h z t} := by
  have hEq : {z : SourceInput p |
      actualInclusivePhysicalScanGate rate rewards C_star C_h z t} =
      ({z | numericalOverflowBy rate rewards C_star C_h t z})ᶜ := by
    ext z
    exact (actualInclusivePhysicalScanGate_iff_noNumericalOverflowThrough
      rate rewards C_star C_h z t).trans
        (noNumericalOverflowThrough_iff_not_numericalOverflowBy
          rate rewards C_star C_h t z)
  rw [hEq]
  exact (measurableSet_numericalOverflowBy rate rewards C_star C_h t).compl

/-- The stopped ordinary event has an exact finite-scan characterization by
the source saved-diagnostic observer. -/
theorem stoppedOrdinaryWrongCompletionEvent_iff_savedObserver
    (z : SourceInput p) :
    z ∈ stoppedOrdinaryWrongCompletionEvent rate rewards C_star C_h ↔
      ∃ t : Fin p.T,
        noNumericalOverflowThrough rate rewards C_star C_h t z ∧
        ReferenceCompleteOrdinaryFalseEventObservableLocality.ordinaryWrongCompletionAtObserved
          rate rewards C_star C_h t z = true := by
  constructor
  · rintro ⟨t, hgate, hwrong⟩
    refine ⟨t, ?_, ?_⟩
    · exact (actualInclusivePhysicalScanGate_iff_noNumericalOverflowThrough
        rate rewards C_star C_h z t).mp hgate
    · exact (ReferenceCompleteOrdinaryFalseEventObservableLocality.ordinaryWrongCompletionAt_observed_iff
        rate rewards C_star C_h t z).mp hwrong
  · rintro ⟨t, hprefix, hwrong⟩
    refine ⟨t, ?_, ?_⟩
    · exact (actualInclusivePhysicalScanGate_iff_noNumericalOverflowThrough
        rate rewards C_star C_h z t).mpr hprefix
    · exact (ReferenceCompleteOrdinaryFalseEventObservableLocality.ordinaryWrongCompletionAt_observed_iff
        rate rewards C_star C_h t z).mpr hwrong

/-- The stopped bidirectional ambiguity event is exactly the saved literal
DOWN-or-UP date observer under the same bounded physical scan. -/
theorem stoppedFixedAwaitedAmbiguityEvent_iff_literalObserver
    (z : SourceInput p) :
    z ∈ stoppedFixedAwaitedAmbiguityEvent rate rewards C_star C_h ↔
      ∃ t : Fin p.T,
        noNumericalOverflowThrough rate rewards C_star C_h t z ∧
        ReferenceLiteralSourceDecoderCoverage.S_amb
          rate rewards C_star C_h z t := by
  constructor
  · rintro ⟨t, hgate, hamb⟩
    refine ⟨t,
      (actualInclusivePhysicalScanGate_iff_noNumericalOverflowThrough
        rate rewards C_star C_h z t).mp hgate, ?_⟩
    exact (ReferenceCompleteAwaitedBatchSourceCoverage.sourceFixedAwaitedCompletionAt_iff_literal
      rate rewards C_star C_h z t).mp hamb
  · rintro ⟨t, hprefix, hamb⟩
    refine ⟨t,
      (actualInclusivePhysicalScanGate_iff_noNumericalOverflowThrough
        rate rewards C_star C_h z t).mpr hprefix, ?_⟩
    exact (ReferenceCompleteAwaitedBatchSourceCoverage.sourceFixedAwaitedCompletionAt_iff_literal
      rate rewards C_star C_h z t).mpr hamb

/-- Whole-source Borel measurability of the complete stopped false-completion
event, including the actual prelaunch branch. -/
theorem measurableSet_stoppedOrdinaryWrongCompletionEvent :
    MeasurableSet (stoppedOrdinaryWrongCompletionEvent rate rewards C_star C_h) := by
  have hrepr : stoppedOrdinaryWrongCompletionEvent rate rewards C_star C_h =
      ⋃ t : Fin p.T, {z : SourceInput p |
        actualInclusivePhysicalScanGate rate rewards C_star C_h z t ∧
        ReferenceCompleteOrdinaryWrongCompletionCharacterization.ordinaryWrongCompletionAt
          rate rewards C_star C_h t z} := by
    ext z
    simp [stoppedOrdinaryWrongCompletionEvent]
  rw [hrepr]
  exact MeasurableSet.iUnion fun t =>
    (measurableSet_actualInclusivePhysicalScanGate rate rewards C_star C_h t).inter
      (ReferenceCompleteOrdinaryFalseEventObservableLocality.ordinaryWrongCompletionAt_measurableSet
        rate rewards C_star C_h t)

/-- Whole-source Borel measurability of the complete stopped fixed-awaited
ambiguity event, retaining both directed decoder branches. -/
theorem measurableSet_stoppedFixedAwaitedAmbiguityEvent :
    MeasurableSet (stoppedFixedAwaitedAmbiguityEvent rate rewards C_star C_h) := by
  have hrepr : stoppedFixedAwaitedAmbiguityEvent rate rewards C_star C_h =
      ⋃ t : Fin p.T, {z : SourceInput p |
        actualInclusivePhysicalScanGate rate rewards C_star C_h z t ∧
        ReferenceCompleteAwaitedBatchSourceCoverage.sourceFixedAwaitedCompletionAt
          rate rewards C_star C_h z t} := by
    ext z
    simp [stoppedFixedAwaitedAmbiguityEvent]
  rw [hrepr]
  refine MeasurableSet.iUnion fun t => ?_
  have hdate :
      MeasurableSet {z : SourceInput p |
        ReferenceCompleteAwaitedBatchSourceCoverage.sourceFixedAwaitedCompletionAt
          rate rewards C_star C_h z t} := by
    have hEq : {z : SourceInput p |
        ReferenceCompleteAwaitedBatchSourceCoverage.sourceFixedAwaitedCompletionAt
          rate rewards C_star C_h z t} =
        {z | ReferenceLiteralSourceDecoderCoverage.S_amb
          rate rewards C_star C_h z t} := by
      ext z
      exact (ReferenceCompleteAwaitedBatchSourceCoverage.sourceFixedAwaitedCompletionAt_iff_literal
        rate rewards C_star C_h z t)
    rw [hEq]
    exact ReferenceLiteralAwaitedAmbiguityRowObservation.S_amb_borel
      rate rewards C_star C_h t
  exact (measurableSet_actualInclusivePhysicalScanGate rate rewards C_star C_h t).inter hdate

/-- Borel measurability of the combined two-branch decoder failure event. -/
theorem measurableSet_completeInclusiveDecoderFailureEvent :
    MeasurableSet (completeInclusiveDecoderFailureEvent rate rewards C_star C_h) :=
  (measurableSet_stoppedOrdinaryWrongCompletionEvent rate rewards C_star C_h).union
    (measurableSet_stoppedFixedAwaitedAmbiguityEvent rate rewards C_star C_h)

/-- The bounded optional-prefix overflow observer depends only on public IDs,
the same original private coordinates (including `J`), and the same selected
complete row. -/
theorem numericalOverflowBy_iff_of_source_data
    (t : Fin p.T) (z z' : SourceInput p) (j : Fin (M p))
    (hids : z.1.1 = z'.1.1) (hprivate : z.2 = z'.2)
    (hJ : ActualInitializationPhysicalStep.selectedRowIndex p z = j)
    (hrow : z.1.2 j = z'.1.2 j) :
    numericalOverflowBy rate rewards C_star C_h t z ↔
      numericalOverflowBy rate rewards C_star C_h t z' := by
  unfold numericalOverflowBy
  constructor
  · rintro ⟨n, hnt, o, ho, a, ha⟩
    have hread := ReferenceCompletePrefixReadoutRowLocality.prefixReadout_eq_of_source_data
      rate rewards C_star C_h n z z' j hids hprivate hJ hrow
    exact ⟨n, hnt, o, by rw [← hread]; exact ho, a, ha⟩
  · rintro ⟨n, hnt, o, ho, a, ha⟩
    have hJ' : ActualInitializationPhysicalStep.selectedRowIndex p z' = j := by
      have hscalar : z.2.1.2 = z'.2.1.2 := congrArg (fun e => e.1.2) hprivate
      change PrivateSourceStreams.coordinatorIndex p z'.2.1.2 = j
      rw [← hscalar]
      exact hJ
    have hread := ReferenceCompletePrefixReadoutRowLocality.prefixReadout_eq_of_source_data
      rate rewards C_star C_h n z' z j hids.symm hprivate.symm hJ' hrow.symm
    exact ⟨n, hnt, o, by rw [← hread]; exact ho, a, ha⟩

/-- The literal physical gate has the same selected-row locality as its exact
optional numerical-prefix characterization. -/
theorem actualInclusivePhysicalScanGate_iff_of_source_data
    (t : Fin p.T) (z z' : SourceInput p) (j : Fin (M p))
    (hids : z.1.1 = z'.1.1) (hprivate : z.2 = z'.2)
    (hJ : ActualInitializationPhysicalStep.selectedRowIndex p z = j)
    (hrow : z.1.2 j = z'.1.2 j) :
    actualInclusivePhysicalScanGate rate rewards C_star C_h z t ↔
      actualInclusivePhysicalScanGate rate rewards C_star C_h z' t := by
  have hnum := numericalOverflowBy_iff_of_source_data
    rate rewards C_star C_h t z z' j hids hprivate hJ hrow
  have hleft := actualInclusivePhysicalScanGate_iff_noNumericalOverflowThrough
    rate rewards C_star C_h z t
  have hright := actualInclusivePhysicalScanGate_iff_noNumericalOverflowThrough
    rate rewards C_star C_h z' t
  have hnot := not_congr hnum
  calc
    actualInclusivePhysicalScanGate rate rewards C_star C_h z t ↔
        noNumericalOverflowThrough rate rewards C_star C_h t z := hleft
    _ ↔ noNumericalOverflowThrough rate rewards C_star C_h t z' :=
      (noNumericalOverflowThrough_iff_not_numericalOverflowBy
        rate rewards C_star C_h t z).trans
        (hnot.trans (noNumericalOverflowThrough_iff_not_numericalOverflowBy
          rate rewards C_star C_h t z').symm)
    _ ↔ actualInclusivePhysicalScanGate rate rewards C_star C_h z' t := hright.symm

/-- The complete stopped ordinary event inherits exact source-data locality
from the gate and the actual saved prelaunch/postlaunch date observer. -/
theorem stoppedOrdinaryWrongCompletionEvent_iff_of_source_data
    (z z' : SourceInput p) (j : Fin (M p))
    (hids : z.1.1 = z'.1.1) (hprivate : z.2 = z'.2)
    (hJ : ActualInitializationPhysicalStep.selectedRowIndex p z = j)
    (hrow : z.1.2 j = z'.1.2 j) :
    z ∈ stoppedOrdinaryWrongCompletionEvent rate rewards C_star C_h ↔
      z' ∈ stoppedOrdinaryWrongCompletionEvent rate rewards C_star C_h := by
  change (∃ t : Fin p.T,
      actualInclusivePhysicalScanGate rate rewards C_star C_h z t ∧
      ReferenceCompleteOrdinaryWrongCompletionCharacterization.ordinaryWrongCompletionAt
        rate rewards C_star C_h t z) ↔
    ∃ t : Fin p.T,
      actualInclusivePhysicalScanGate rate rewards C_star C_h z' t ∧
      ReferenceCompleteOrdinaryWrongCompletionCharacterization.ordinaryWrongCompletionAt
        rate rewards C_star C_h t z'
  constructor
  · rintro ⟨t, hgate, hfalse⟩
    refine ⟨t,
      (actualInclusivePhysicalScanGate_iff_of_source_data
        rate rewards C_star C_h t z z' j hids hprivate hJ hrow).mp hgate, ?_⟩
    exact (ReferenceCompleteOrdinaryFalseEventObservableLocality.ordinaryWrongCompletionAt_eq_of_source_data
      rate rewards C_star C_h t z z' j hids hprivate hJ hrow).mp hfalse
  · rintro ⟨t, hgate, hfalse⟩
    refine ⟨t,
      (actualInclusivePhysicalScanGate_iff_of_source_data
        rate rewards C_star C_h t z z' j hids hprivate hJ hrow).mpr hgate, ?_⟩
    exact (ReferenceCompleteOrdinaryFalseEventObservableLocality.ordinaryWrongCompletionAt_eq_of_source_data
      rate rewards C_star C_h t z z' j hids hprivate hJ hrow).mpr hfalse

/-- The stopped fixed-awaited event retains both literal decoder directions
and the same selected-row locality through all present and absent guards. -/
theorem stoppedFixedAwaitedAmbiguityEvent_iff_of_source_data
    (z z' : SourceInput p) (j : Fin (M p))
    (hids : z.1.1 = z'.1.1) (hprivate : z.2 = z'.2)
    (hJ : ActualInitializationPhysicalStep.selectedRowIndex p z = j)
    (hrow : z.1.2 j = z'.1.2 j) :
    z ∈ stoppedFixedAwaitedAmbiguityEvent rate rewards C_star C_h ↔
      z' ∈ stoppedFixedAwaitedAmbiguityEvent rate rewards C_star C_h := by
  change (∃ t : Fin p.T,
      actualInclusivePhysicalScanGate rate rewards C_star C_h z t ∧
      ReferenceCompleteAwaitedBatchSourceCoverage.sourceFixedAwaitedCompletionAt
        rate rewards C_star C_h z t) ↔
    ∃ t : Fin p.T,
      actualInclusivePhysicalScanGate rate rewards C_star C_h z' t ∧
      ReferenceCompleteAwaitedBatchSourceCoverage.sourceFixedAwaitedCompletionAt
        rate rewards C_star C_h z' t
  constructor
  · rintro ⟨t, hgate, hambSource⟩
    refine ⟨t,
      (actualInclusivePhysicalScanGate_iff_of_source_data
        rate rewards C_star C_h t z z' j hids hprivate hJ hrow).mp hgate, ?_⟩
    have hamb := ReferenceLiteralAwaitedAmbiguityRowObservation.S_amb_iff_of_source_data
      rate rewards C_star C_h z z' j t hids hprivate hJ hrow
    have hliteral :=
      (ReferenceCompleteAwaitedBatchSourceCoverage.sourceFixedAwaitedCompletionAt_iff_literal
        rate rewards C_star C_h z t).mp hambSource
    exact (ReferenceCompleteAwaitedBatchSourceCoverage.sourceFixedAwaitedCompletionAt_iff_literal
      rate rewards C_star C_h z' t).mpr (hamb.mp hliteral)
  · rintro ⟨t, hgate, hambSource⟩
    refine ⟨t,
      (actualInclusivePhysicalScanGate_iff_of_source_data
        rate rewards C_star C_h t z z' j hids hprivate hJ hrow).mpr hgate, ?_⟩
    have hamb := ReferenceLiteralAwaitedAmbiguityRowObservation.S_amb_iff_of_source_data
      rate rewards C_star C_h z z' j t hids hprivate hJ hrow
    have hliteral :=
      (ReferenceCompleteAwaitedBatchSourceCoverage.sourceFixedAwaitedCompletionAt_iff_literal
        rate rewards C_star C_h z' t).mp hambSource
    exact (ReferenceCompleteAwaitedBatchSourceCoverage.sourceFixedAwaitedCompletionAt_iff_literal
      rate rewards C_star C_h z t).mpr (hamb.mpr hliteral)

/-- The complete two-branch stopped decoder event has the same exact
whole-source locality. -/
theorem completeInclusiveDecoderFailureEvent_iff_of_source_data
    (z z' : SourceInput p) (j : Fin (M p))
    (hids : z.1.1 = z'.1.1) (hprivate : z.2 = z'.2)
    (hJ : ActualInitializationPhysicalStep.selectedRowIndex p z = j)
    (hrow : z.1.2 j = z'.1.2 j) :
    z ∈ completeInclusiveDecoderFailureEvent rate rewards C_star C_h ↔
      z' ∈ completeInclusiveDecoderFailureEvent rate rewards C_star C_h := by
  change (z ∈ stoppedOrdinaryWrongCompletionEvent rate rewards C_star C_h ∨
      z ∈ stoppedFixedAwaitedAmbiguityEvent rate rewards C_star C_h) ↔
    (z' ∈ stoppedOrdinaryWrongCompletionEvent rate rewards C_star C_h ∨
      z' ∈ stoppedFixedAwaitedAmbiguityEvent rate rewards C_star C_h)
  exact or_congr
    (stoppedOrdinaryWrongCompletionEvent_iff_of_source_data
      rate rewards C_star C_h z z' j hids hprivate hJ hrow)
    (stoppedFixedAwaitedAmbiguityEvent_iff_of_source_data
      rate rewards C_star C_h z z' j hids hprivate hJ hrow)

/-- Replacing every nonselected table row while supplying one identical
complete selected row leaves both stopped source events and their union
unchanged, with the same original private arrays and coordinator index. -/
theorem selectedRow_update_stoppedEvents
    (ids : CompletePublicTable.IDArray p)
    (rows otherRows : CompletePublicTable.CompleteRows p) (j : Fin (M p))
    (rho : CompletePublicTable.CompleteRow p)
    (e : BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
    (hJ : PrivateSourceStreams.coordinatorIndex p e.1.2 = j) :
    (((ids, Function.update rows j rho), e) ∈
        stoppedOrdinaryWrongCompletionEvent rate rewards C_star C_h ↔
      ((ids, Function.update otherRows j rho), e) ∈
        stoppedOrdinaryWrongCompletionEvent rate rewards C_star C_h) ∧
    (((ids, Function.update rows j rho), e) ∈
        stoppedFixedAwaitedAmbiguityEvent rate rewards C_star C_h ↔
      ((ids, Function.update otherRows j rho), e) ∈
        stoppedFixedAwaitedAmbiguityEvent rate rewards C_star C_h) ∧
    (((ids, Function.update rows j rho), e) ∈
        completeInclusiveDecoderFailureEvent rate rewards C_star C_h ↔
      ((ids, Function.update otherRows j rho), e) ∈
        completeInclusiveDecoderFailureEvent rate rewards C_star C_h) := by
  have hselected : ActualInitializationPhysicalStep.selectedRowIndex p
      ((ids, Function.update rows j rho), e) = j := by
    change PrivateSourceStreams.coordinatorIndex p e.1.2 = j
    exact hJ
  have hrow : (Function.update rows j rho) j = (Function.update otherRows j rho) j := by
    simp
  have hfalse := stoppedOrdinaryWrongCompletionEvent_iff_of_source_data
    rate rewards C_star C_h ((ids, Function.update rows j rho), e)
    ((ids, Function.update otherRows j rho), e) j rfl rfl hselected hrow
  have hamb := stoppedFixedAwaitedAmbiguityEvent_iff_of_source_data
    rate rewards C_star C_h ((ids, Function.update rows j rho), e)
    ((ids, Function.update otherRows j rho), e) j rfl rfl hselected hrow
  have hcombined := completeInclusiveDecoderFailureEvent_iff_of_source_data
    rate rewards C_star C_h ((ids, Function.update rows j rho), e)
    ((ids, Function.update otherRows j rho), e) j rfl rfl hselected hrow
  exact ⟨hfalse, hamb, hcombined⟩

/-- Absence of the constructed stopped false event discharges the saved
wrong-unique diagnostic for the same original actual suffix record at every
date that passes the inclusive scan. -/
theorem no_wrong_unique_accepted_at_scanned_actual_record
    (z : SourceInput p) (habsent : z ∉ stoppedOrdinaryWrongCompletionEvent
      rate rewards C_star C_h)
    (t : Fin p.T)
    (hgate : actualInclusivePhysicalScanGate rate rewards C_star C_h z t)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hrecord : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t z = some r) :
    ReferenceActiveStoppedPrefixCoupling.no_wrong_unique_accepted r := by
  have hdate : ¬ ReferenceCompleteOrdinaryWrongCompletionCharacterization.ordinaryWrongCompletionAt
      rate rewards C_star C_h t z := by
    intro hwrong
    exact habsent ⟨t, hgate, hwrong⟩
  have hnotFlag : ReferenceGeneratedSavedWrongEvent.savedWrongRecordFlag r ≠ true := by
    intro hflag
    apply hdate
    exact (ReferenceCompleteOrdinaryWrongCompletionCharacterization.ordinaryWrongCompletionAt_iff
      rate rewards C_star C_h t z).mpr (Or.inr ⟨r, hrecord, hflag⟩)
  have hnotSaved :
      ¬ ReferenceActiveStoppedPrefixCoupling.saved_wrong_unique_accepted r := by
    intro hbad
    have hflag : ReferenceGeneratedSavedWrongEvent.savedWrongRecordFlag r = true ↔
        ReferenceActiveStoppedPrefixCoupling.saved_wrong_unique_accepted r := by
      simp [ReferenceGeneratedSavedWrongEvent.savedWrongRecordFlag]
    exact hnotFlag
      (hflag.mpr hbad)
  exact (ReferenceActiveStoppedPrefixCoupling.no_wrong_unique_accepted_iff r).mpr hnotSaved

/-- On a physical overflow sample, the finite actual suffix prefix extends
through and includes the first detector record. Every actual record through
that date is safe when the constructed stopped false event is absent. -/
theorem no_wrong_unique_accepted_through_actual_first_detector
    (z : SourceInput p)
    (habsent : z ∉ stoppedOrdinaryWrongCompletionEvent rate rewards C_star C_h)
    (hphysical : z ∈
      ReferenceCompletePhysicalCalendarFirstCrossing.physicalFirstOverflowEvent
        rate rewards C_star C_h) :
    ∃ q : Fin p.T,
      z ∈ ReferenceOriginalNumericalFirstOverflowLocator.firstOverflowUpdateAt
        rate rewards C_star C_h q ∧
      ∀ t : Fin p.T, t.val ≤ q.val →
        ∀ r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate),
          ReferenceSourcePrefixHistoryFiltration.actualRecord
            rate rewards C_star C_h t z = some r →
          ReferenceActiveStoppedPrefixCoupling.no_wrong_unique_accepted r := by
  classical
  cases hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate z rewards C_star C_h with
  | none =>
      have hchar :=
        ReferenceCompletePhysicalCalendarFirstCrossing.actual_physical_first_overflow_characterization
          rate rewards C_star C_h z
      rw [hlaunch] at hchar
      rcases hchar with ⟨_, _, _, hnoPhysical, _⟩
      exact (hnoPhysical hphysical).elim
  | some active =>
      have hchar :=
        ReferenceCompletePhysicalCalendarFirstCrossing.actual_physical_first_overflow_characterization
          rate rewards C_star C_h z
      rw [hlaunch] at hchar
      rcases hchar with
        ⟨L, H, hL, hH, hfinite, _hnoCross, hstates, _hword, _hterminal, hdetector⟩
      have hHbound := hfinite.mpr hphysical
      obtain ⟨q, _hqdate, hqpost, hfirst⟩ := hdetector hHbound
      refine ⟨q, hfirst, ?_⟩
      intro t ht r hrecord
      have hgateData :=
        actualInclusivePhysicalScanGate_iff_firstOverflowBoundary_of_data
          rate rewards C_star C_h z t L H hL hH hstates
      have hcut : t.val < ReferenceCompletePhysicalHistory.physicalStart
          rate z rewards C_star C_h + H := by
        rw [← hqpost]
        omega
      have hgate : actualInclusivePhysicalScanGate rate rewards C_star C_h z t :=
        hgateData.mpr hcut
      exact no_wrong_unique_accepted_at_scanned_actual_record
        rate rewards C_star C_h z habsent t hgate r hrecord

/-- If the actual physical suffix never crosses the queue cap, every suffix
date passes the inclusive gate, so absence of the stopped false event
discharges the saved diagnostic through the whole suffix. -/
theorem no_wrong_unique_accepted_all_suffix_dates_of_no_physical_overflow
    (z : SourceInput p)
    (habsent : z ∉ stoppedOrdinaryWrongCompletionEvent rate rewards C_star C_h)
    (hnoPhysical : z ∉
      ReferenceCompletePhysicalCalendarFirstCrossing.physicalFirstOverflowEvent
        rate rewards C_star C_h) :
    ∀ t : Fin p.T,
      ∀ r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate),
        ReferenceSourcePrefixHistoryFiltration.actualRecord
          rate rewards C_star C_h t z = some r →
        ReferenceActiveStoppedPrefixCoupling.no_wrong_unique_accepted r := by
  intro t r hrecord
  have hnoObserved :
      z ∉ ReferenceOriginalNumericalFirstOverflowLocator.observedNumericalOverflowEvent
        rate rewards C_star C_h := by
    rw [← ReferenceCompletePhysicalCalendarFirstCrossing.physicalFirstOverflowEvent_eq_observedNumericalOverflowEvent
      rate rewards C_star C_h]
    exact hnoPhysical
  have hnoBy : ¬ numericalOverflowBy rate rewards C_star C_h t z := by
    intro ⟨n, hnt, o, ho, a, ha⟩
    apply hnoObserved
    exact ⟨n, by omega, o, ho, a, ha⟩
  have hnoThrough := (noNumericalOverflowThrough_iff_not_numericalOverflowBy
    rate rewards C_star C_h t z).2 hnoBy
  have hgate := (actualInclusivePhysicalScanGate_iff_noNumericalOverflowThrough
    rate rewards C_star C_h z t).mpr hnoThrough
  exact no_wrong_unique_accepted_at_scanned_actual_record
    rate rewards C_star C_h z habsent t hgate r hrecord
