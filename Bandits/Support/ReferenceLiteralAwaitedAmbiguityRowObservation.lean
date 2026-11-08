/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceLiteralSourceDecoderCoverage
public import Bandits.Support.ReferenceGeneratedCompleteCalendarObservation

/-!
# Literal awaited ambiguity row observation

This module identifies the physical literal completed-bank predicates with
the existing fixed-awaited readouts, observes their Borel events, and records
their selected-row locality on the original source carrier. It concerns only
the postlaunch `actualRecord` predicates on the whole source input; it does
not characterize the manuscript's global decoder event or a physical stop.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.ReferenceFollowerDownDecoderReplay
open scoped Classical

namespace Bandits.Support.ReferenceLiteralAwaitedAmbiguityRowObservation

variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
variable (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
variable (C_star C_h : ℝ)

abbrev Source := BootstrapPrivateRoundStreams.SourceInput p
abbrev Record := ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)
abbrev Batch := List (AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p))

/-- A physical DOWN completion is exactly the existing completed-bank
readout: the incoming bank, current positive append, quota, and clearing
transition are retained by `physicalDownCompletedAt`. -/
theorem physicalDownCompletedAt_iff_completedDownBatch
    (r : Record (rate := rate)) (i : Fin (p.m - 1)) (W : Batch (p := p)) :
    ReferenceLiteralSourceDecoderCoverage.physicalDownCompletedAt r i W ↔
      ReferenceFirstLiveDownCompletionReadout.completedDownBatch r i = some W := by
  constructor
  · intro h
    obtain ⟨logged, cut, hi, hd, hselected, hstatus, hregister, hdecoder, hbuffer,
      hbank, hlen, hclear, hraw⟩ := h
    have hcut := ReferenceDownCompletedAmbiguityMeasurability.record_downCut_eq_actual
      r i logged cut hi hd
    have hcomp : cut.rawComparison.isSome = true := by
      rw [hcut]
      by_cases hmatches :
          (ActiveFollowerDownAcceptance.currentDecodeStep p i r.input.row r.input.time
            (ReferenceFollowerDownDecoderReplay.preparedOwnObservation r i)
            rate logged).2 =
            ReferenceDownReception.expectedDownFlatWord
              r.output.preparation.coordinator.downView i r.input.row r.input.time
      · simp [ReferenceDownReception.referenceDownCut, hselected, hstatus,
          hregister, hdecoder, hbuffer, hmatches]
      · simp [ReferenceDownReception.referenceDownCut, hselected, hstatus,
          hregister, hdecoder, hbuffer, hmatches]
    have happended :
        ReferenceFirstLiveDownCompletionReadout.appendedDownBatch r i logged = W := by
      simpa only [ReferenceFirstLiveDownCompletionReadout.appendedDownBatch] using hbank.symm
    have hquota : AffineBatchDecoder.quota p ≤
        (ReferenceFirstLiveDownCompletionReadout.appendedDownBatch r i logged).length := by
      rw [happended]
      omega
    exact (ReferenceFirstLiveDownCompletionReadout.completedDownBatch_eq_some_iff r i W).2
      ⟨logged, cut, hi, hd, hcomp, hquota, happended⟩
  · exact ReferenceLiteralSourceDecoderCoverage.physicalDownCompletedAt_of_completedDownBatch
      r i W

/-- A physical UP completion is exactly the existing UP completed-bank
readout, including the selected receiver's carried incoming bank. -/
theorem physicalUpCompletedAt_iff_completedUpBatch
    (r : Record (rate := rate)) (i : Fin (p.m - 1)) (W : Batch (p := p)) :
    ReferenceLiteralSourceDecoderCoverage.physicalUpCompletedAt r i W ↔
      ReferenceCollectionUpFailureReadoutV2.completedUpBatch rate r i = some W := by
  constructor
  · intro h
    obtain ⟨d, hd, hselected, hdomain, heligible, hbank, hlen, hclear, hraw⟩ := h
    have happended : ReferenceCollectionUpFailureReadoutV2.appendedUp rate d = W := by
      simpa only [ReferenceCollectionUpFailureReadoutV2.appendedUp, hselected] using hbank.symm
    have hquota : ReferenceCollectionUpFailureReadoutV2.Q (p := p) ≤
        (ReferenceCollectionUpFailureReadoutV2.appendedUp rate d).length := by
      rw [happended]
      rw [hlen]
    exact (ReferenceCollectionUpFailureReadoutV2.completedUpBatch_eq_some_iff
      rate r i W).2 ⟨d, hd, hselected,
        (CoordinatorUpReception.receptionInputCheck_eq_true_iff d.input).mpr hdomain,
        heligible, hquota, happended⟩
  · intro h
    obtain ⟨d, hd, hselected, hcheck, heligible, hquota, happended⟩ :=
      (ReferenceCollectionUpFailureReadoutV2.completedUpBatch_eq_some_iff rate r i W).mp h
    obtain ⟨hlen, d', hd', hselected', hclear, hraw⟩ :=
      ReferenceCollectionUpFailureReadoutV2.completedUpBatch_spec rate r i W h
    cases hd.symm.trans hd'
    have hbank : W = (d.input.upDecoderBank i).pending ++
        AffineBatchDecoder.positiveAt p (CoordinatorUpReception.traceAt d.input) d.input.time := by
      simpa only [ReferenceCollectionUpFailureReadoutV2.appendedUp, hselected] using happended.symm
    refine ⟨d, hd, hselected,
      (CoordinatorUpReception.receptionInputCheck_eq_true_iff d.input).mp hcheck,
      heligible, hbank, hlen, hclear, hraw⟩

/-- On the whole original source carrier, the literal DOWN ambiguity event
is equivalent to the existing fixed-awaited DOWN failure predicate. -/
theorem literalDownAmbiguityAt_iff_fixedAwaitedDownFailureAt
    (z : Source (p := p)) (t : Fin p.T) :
    ReferenceLiteralSourceDecoderCoverage.literalDownAmbiguityAt
        rate rewards C_star C_h z t ↔
      ReferenceFirstCollectionAwaitedDownFailureReadout.fixedAwaitedDownFailureAt
        rate rewards C_star C_h z t := by
  constructor
  · intro h
    obtain ⟨r, i, w, W, a, hr, hW, hat, hmulti, hentries, hcalendar⟩ := h
    refine ⟨r, i, w, W, a, hr, ?_, hat,
      (ReferenceFirstLiveDownCompletionReadout.multipleSolutions_iff W).mpr hmulti,
      ?_, ?_⟩
    · exact physicalDownCompletedAt_iff_completedDownBatch rate r i W |>.mp hW
    · intro e he
      obtain ⟨ha, ht, heq, re, hre, hrows, hselected, htime, hrewards,
        hsample, hpositive, haw⟩ := hentries e he
      exact ⟨ha, ht, heq, re, hre, hpositive,
        (ReferenceLiteralSourceDecoderCoverage.physicalAwaitedDownAt_iff re i w).mp haw⟩
    · intro v ha ht hchannel
      obtain ⟨rv, hrv, _, _, _, _, haw⟩ := hcalendar v ha ht hchannel
      exact ⟨rv, hrv,
        (ReferenceLiteralSourceDecoderCoverage.physicalAwaitedDownAt_iff rv i w).mp haw⟩
  · intro h
    have h' := ReferenceLiteralSourceDecoderCoverage.literalDownAmbiguityAt_of_fixedAwaitedDownFailureAt
      rate rewards C_star C_h z t h
    exact h'

/-- On the whole original source carrier, the literal UP ambiguity event is
equivalent to the existing fixed-awaited UP failure predicate. -/
theorem literalUpAmbiguityAt_iff_fixedAwaitedUpFailureAt
    (z : Source (p := p)) (t : Fin p.T) :
    ReferenceLiteralSourceDecoderCoverage.literalUpAmbiguityAt
        rate rewards C_star C_h z t ↔
      ReferenceCollectionUpFailureReadoutV2.fixedAwaitedUpFailureAt
        rate rewards C_star C_h z t := by
  constructor
  · intro h
    obtain ⟨r, i, M, W, a, hr, hW, hat, hsigma, hmulti, hentries, hcalendar⟩ := h
    refine ⟨r, i, M, W, a, hr, ?_, hat, hsigma,
      (ReferenceFirstLiveDownCompletionReadout.multipleSolutions_iff W).mpr hmulti,
      ?_, ?_⟩
    · exact physicalUpCompletedAt_iff_completedUpBatch rate r i W |>.mp hW
    · intro e he
      obtain ⟨ha, ht, heq, re, hre, hrows, hselected, htime, hrewards,
        hsample, hpositive, haw⟩ := hentries e he
      exact ⟨ha, ht, heq, re, hre, hpositive,
        (ReferenceLiteralSourceDecoderCoverage.physicalAwaitedUpAt_iff re i M).mp haw⟩
    · intro v ha ht hchannel
      obtain ⟨rv, hrv, _, _, _, _, haw⟩ := hcalendar v ha ht hchannel
      exact ⟨rv, hrv,
        (ReferenceLiteralSourceDecoderCoverage.physicalAwaitedUpAt_iff rv i M).mp haw⟩
  · intro h
    exact ReferenceLiteralSourceDecoderCoverage.literalUpAmbiguityAt_of_fixedAwaitedUpFailureAt
      rate rewards C_star C_h z t h

/-- The existing literal DOWN ambiguity event is Borel on the original
whole-source ambient measurable space. -/
theorem literalDownAmbiguityAt_borel (t : Fin p.T) :
    MeasurableSet {z : Source (p := p) |
      ReferenceLiteralSourceDecoderCoverage.literalDownAmbiguityAt
        rate rewards C_star C_h z t} := by
  have heq : {z : Source (p := p) |
      ReferenceLiteralSourceDecoderCoverage.literalDownAmbiguityAt
        rate rewards C_star C_h z t} =
      {z | ReferenceFirstCollectionAwaitedDownFailureReadout.fixedAwaitedDownFailureAt
        rate rewards C_star C_h z t} := by
    ext z
    exact literalDownAmbiguityAt_iff_fixedAwaitedDownFailureAt
      rate rewards C_star C_h z t
  rw [heq]
  exact ReferenceFirstCollectionAwaitedDownFailureReadout.fixedAwaitedDownFailureAt_borel
    rate rewards C_star C_h t

/-- The existing literal UP ambiguity event is Borel on the original
whole-source ambient measurable space. -/
theorem literalUpAmbiguityAt_borel (t : Fin p.T) :
    MeasurableSet {z : Source (p := p) |
      ReferenceLiteralSourceDecoderCoverage.literalUpAmbiguityAt
        rate rewards C_star C_h z t} := by
  have heq : {z : Source (p := p) |
      ReferenceLiteralSourceDecoderCoverage.literalUpAmbiguityAt
        rate rewards C_star C_h z t} =
      {z | ReferenceCollectionUpFailureReadoutV2.fixedAwaitedUpFailureAt
        rate rewards C_star C_h z t} := by
    ext z
    exact literalUpAmbiguityAt_iff_fixedAwaitedUpFailureAt
      rate rewards C_star C_h z t
  rw [heq]
  exact ReferenceCollectionUpFailureReadoutV2.fixedAwaitedUpFailureAt_borel
    rate rewards C_star C_h t

/-- The literal source ambiguity event is Borel by the two component
equivalences, each proved on its own event. -/
theorem S_amb_borel (t : Fin p.T) :
    MeasurableSet {z : Source (p := p) |
      ReferenceLiteralSourceDecoderCoverage.S_amb rate rewards C_star C_h z t} := by
  change MeasurableSet
    ({z : Source (p := p) | ReferenceLiteralSourceDecoderCoverage.literalDownAmbiguityAt
        rate rewards C_star C_h z t} ∪
      {z | ReferenceLiteralSourceDecoderCoverage.literalUpAmbiguityAt
        rate rewards C_star C_h z t})
  exact (literalDownAmbiguityAt_borel rate rewards C_star C_h t).union
    (literalUpAmbiguityAt_borel rate rewards C_star C_h t)

/-- The literal finite calendar-prefix scan of the existing ambiguity event.
The scan is over `t.val < n`, so `n = t.val + 1` includes the detecting
update. -/
def S_amb_prefix (n : ℕ) (z : Source (p := p)) : Prop :=
  ∃ t : Fin p.T, t.val < n ∧
    ReferenceLiteralSourceDecoderCoverage.S_amb rate rewards C_star C_h z t

/-- Borelness of the literal finite calendar-prefix ambiguity event. -/
theorem S_amb_prefix_borel (n : ℕ) :
    MeasurableSet {z : Source (p := p) | S_amb_prefix rate rewards C_star C_h n z} := by
  have heq : {z : Source (p := p) | S_amb_prefix rate rewards C_star C_h n z} =
      ⋃ t : Fin p.T, {z : Source (p := p) | t.val < n ∧
        ReferenceLiteralSourceDecoderCoverage.S_amb rate rewards C_star C_h z t} := by
    ext z
    simp only [S_amb_prefix, Set.mem_iUnion, Set.mem_ofPred_eq]
  rw [heq]
  exact MeasurableSet.iUnion fun t => by
    by_cases ht : t.val < n
    · simpa only [ht, true_and] using S_amb_borel rate rewards C_star C_h t
    · simp [ht]

private theorem selectedRowIndex_eq_of_private
    (z z' : Source (p := p)) (j : Fin (M p))
    (hprivate : z.2 = z'.2)
    (hJ : ActualInitializationPhysicalStep.selectedRowIndex p z = j) :
    ActualInitializationPhysicalStep.selectedRowIndex p z' = j := by
  have hscalar : z.2.1.2 = z'.2.1.2 := congrArg (fun e => e.1.2) hprivate
  change PrivateSourceStreams.coordinatorIndex p z'.2.1.2 = j
  rw [← hscalar]
  exact hJ

/-- A source-data change preserves the option-valued actual record at a date
and the complete public code for that record. The launch boundary is compared
separately, so none, terminal, and active suffixes all retain their branches. -/
private theorem actualRecord_correspondence_of_source_data
    (z z' : Source (p := p)) (j : Fin (M p)) (t : Fin p.T)
    (hids : z.1.1 = z'.1.1) (hprivate : z.2 = z'.2)
    (hJ : ActualInitializationPhysicalStep.selectedRowIndex p z = j)
    (hrow : z.1.2 j = z'.1.2 j)
    (r : Record (rate := rate))
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t z = some r) :
    ∃ r' : Record (rate := rate),
      ReferenceSourcePrefixHistoryFiltration.actualRecord
        rate rewards C_star C_h t z' = some r' ∧
      ReferenceActiveHorizonMeasurability.roundRecordCode r =
        ReferenceActiveHorizonMeasurability.roundRecordCode r' := by
  have hJ' := selectedRowIndex_eq_of_private z z' j hprivate hJ
  obtain ⟨_, hboundary, _⟩ :=
    ReferenceCompletePhysicalHistory.generatedInput_and_launch_eq_of_source_data
      rate z z' rewards C_star C_h j hids hprivate hJ hrow
  have hstart : ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h =
      ReferenceCompletePhysicalHistory.physicalStart rate z' rewards C_star C_h := by
    simpa only [ReferenceCompletePhysicalHistory.physicalStart,
      ReferenceCompletePhysicalHistory.generatedBoundary] using
      congrArg (fun boundary : ReferenceInitializationRun.Boundary p =>
        ReferenceInitializationRun.elapsed p boundary.completed) hboundary
  have hstartLE : ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h ≤ t.val := by
    by_contra hnot
    have hnone := ReferenceSourcePrefixHistoryFiltration.actualRecord_eq_none_of_future_start
      rate rewards C_star C_h t z (Nat.lt_of_not_ge hnot)
    rw [hnone] at hr
    cases hr
  have hlookup :
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[
        t.val - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h]? =
          some r := by
    simpa only [ReferenceSourcePrefixHistoryFiltration.actualRecord,
      ite_eq_left hstartLE] using hr
  have hcodes :=
    ReferenceGeneratedCompleteCalendarObservation.completeSuffixCode_eq_of_source_data
      (rate := rate) rewards C_star C_h z z' j hids hprivate hJ hrow
  have hcodeLeft :
      (ReferenceGeneratedCompleteCalendarObservation.completeSuffixCode
        (rate := rate) rewards C_star C_h z)[
          t.val - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h]? =
        some (ReferenceActiveHorizonMeasurability.roundRecordCode r) := by
    simp only [ReferenceGeneratedCompleteCalendarObservation.completeSuffixCode,
      List.getElem?_map, hlookup, Option.map_some]
  have hcodeRight :=
    (congrArg (fun codes : List (ReferenceActiveHorizonMeasurability.RoundRecordCode
      (p := p) (rate := rate)) =>
        codes[t.val - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h]?)
      hcodes).symm.trans hcodeLeft
  have hmapRight :
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z' rewards C_star C_h)[
        t.val - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h]?.map
          (ReferenceActiveHorizonMeasurability.roundRecordCode (p := p) (rate := rate)) =
        some (ReferenceActiveHorizonMeasurability.roundRecordCode r) := by
    simpa only [ReferenceGeneratedCompleteCalendarObservation.completeSuffixCode,
      List.getElem?_map] using hcodeRight
  cases hlookup' :
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z' rewards C_star C_h)[
        t.val - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h]? with
  | none => simp [hlookup'] at hmapRight
  | some r' =>
      have hcode : ReferenceActiveHorizonMeasurability.roundRecordCode r' =
          ReferenceActiveHorizonMeasurability.roundRecordCode r := by
        simpa only [hlookup', Option.map_some, Option.some.injEq] using hmapRight
      have hr' : ReferenceSourcePrefixHistoryFiltration.actualRecord
          rate rewards C_star C_h t z' = some r' := by
        have hlookup'' :
            (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z' rewards C_star C_h)[
              t.val - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h]? =
                some r' := by
          simpa only [hstart] using hlookup'
        unfold ReferenceSourcePrefixHistoryFiltration.actualRecord
        rw [← hstart]
        simp only [ite_eq_left hstartLE]
        exact hlookup''
      exact ⟨r', hr', hcode.symm⟩

/-- The actual selected row, round inputs, and only those stored output
projections read by the literal decoder predicates are reconstructed from the
canonical complete code. This does not identify raw records across changed
unselected rows. -/
private theorem recordObservationData_eq_of_source_data
    (z z' : Source (p := p)) (j : Fin (M p)) (t : Fin p.T)
    (hprivate : z.2 = z'.2)
    (hJ : ActualInitializationPhysicalStep.selectedRowIndex p z = j)
    (hrow : z.1.2 j = z'.1.2 j)
    (r r' : Record (rate := rate))
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t z = some r)
    (hr' : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t z' = some r')
    (hcode : ReferenceActiveHorizonMeasurability.roundRecordCode r =
      ReferenceActiveHorizonMeasurability.roundRecordCode r') :
    r.input.state = r'.input.state ∧ r.input.row = r'.input.row ∧
    r.input.time = r'.input.time ∧ r.input.rewards = r'.input.rewards ∧
    r.output.coordinator = r'.output.coordinator ∧
    (∀ i, r.output.followers i = r'.output.followers i) ∧
    (∀ player, r.output.ownEntries player = r'.output.ownEntries player) ∧
    (∀ i, ReferenceFollowerDownDecoderReplay.preparedOwnObservation r i =
      ReferenceFollowerDownDecoderReplay.preparedOwnObservation r' i) ∧
    (ReferenceActivePhysicalStep.dispatch r.input).downView =
      (ReferenceActivePhysicalStep.dispatch r'.input).downView := by
  have hJ' := selectedRowIndex_eq_of_private z z' j hprivate hJ
  obtain ⟨hrows, hselected, htime, hrewards⟩ :=
    ReferenceLiteralSourceDecoderCoverage.actualRecord_original_fields
      rate rewards C_star C_h z t r hr
  obtain ⟨hrows', hselected', htime', hrewards'⟩ :=
    ReferenceLiteralSourceDecoderCoverage.actualRecord_original_fields
      rate rewards C_star C_h z' t r' hr'
  have hinputRow : r.input.row = r'.input.row := by
    change r.input.rows r.input.selected = r'.input.rows r'.input.selected
    rw [hrows, hselected, hrows', hselected', hJ, hJ']
    exact hrow
  have htimeInput : r.input.time = r'.input.time := htime.trans htime'.symm
  have hrewardInput : r.input.rewards = r'.input.rewards := hrewards.trans hrewards'.symm
  let decodeState (code : ReferenceActiveHorizonMeasurability.RoundRecordCode
      (p := p) (rate := rate)) :=
    ReferenceActivePhysicalStepMeasurability.decodeState code.2.1
  let decodeCoordinator (code : ReferenceActiveHorizonMeasurability.RoundRecordCode
      (p := p) (rate := rate)) :=
    ReferenceCollectionServiceTailMeasurability.decodeCollectionObservation
      code.2.2.1.2.2.2.2
  have hstate : r.input.state = r'.input.state := by
    calc
      r.input.state = decodeState (ReferenceActiveHorizonMeasurability.roundRecordCode r) :=
        (ReferenceActiveHorizonMeasurability.roundRecordCode_reconstructs r).1.symm
      _ = decodeState (ReferenceActiveHorizonMeasurability.roundRecordCode r') :=
        congrArg decodeState hcode
      _ = r'.input.state :=
        (ReferenceActiveHorizonMeasurability.roundRecordCode_reconstructs r').1
  have hcoordinator : r.output.coordinator = r'.output.coordinator := by
    calc
      r.output.coordinator = decodeCoordinator
          (ReferenceActiveHorizonMeasurability.roundRecordCode r) :=
        (ReferenceActiveHorizonMeasurability.roundRecordCode_reconstructs r).2.1.symm
      _ = decodeCoordinator (ReferenceActiveHorizonMeasurability.roundRecordCode r') :=
        congrArg decodeCoordinator hcode
      _ = r'.output.coordinator :=
        (ReferenceActiveHorizonMeasurability.roundRecordCode_reconstructs r').2.1
  have hfollower : ∀ i, r.output.followers i = r'.output.followers i := by
    intro i
    calc
      r.output.followers i =
          ReferenceFollowerTailComposition.reconstructFollowerObservable
            ((ReferenceActiveHorizonMeasurability.roundRecordCode r).2.2.2.1 i) :=
        (ReferenceActiveHorizonMeasurability.roundRecordCode_reconstructs r).2.2.1 i |>.symm
      _ = ReferenceFollowerTailComposition.reconstructFollowerObservable
          ((ReferenceActiveHorizonMeasurability.roundRecordCode r').2.2.2.1 i) :=
        congrArg (fun code => ReferenceFollowerTailComposition.reconstructFollowerObservable
          (code.2.2.2.1 i)) hcode
      _ = r'.output.followers i :=
        (ReferenceActiveHorizonMeasurability.roundRecordCode_reconstructs r').2.2.1 i
  have hown : ∀ player, r.output.ownEntries player = r'.output.ownEntries player := by
    intro player
    calc
      r.output.ownEntries player =
          ReferenceActiveHorizonMeasurability.roundRecordCodeOwnEntry
            (ReferenceActiveHorizonMeasurability.roundRecordCode r) player :=
        (ReferenceActiveHorizonMeasurability.roundRecordCode_reconstructs r).2.2.2.2 player |>.symm
      _ = ReferenceActiveHorizonMeasurability.roundRecordCodeOwnEntry
          (ReferenceActiveHorizonMeasurability.roundRecordCode r') player :=
        congrArg (fun code => ReferenceActiveHorizonMeasurability.roundRecordCodeOwnEntry
          code player) hcode
      _ = r'.output.ownEntries player :=
        (ReferenceActiveHorizonMeasurability.roundRecordCode_reconstructs r').2.2.2.2 player
  have hfeedback : r.gridFeedback = r'.gridFeedback := by
    calc
      r.gridFeedback = ReferenceActiveHorizonMeasurability.roundRecordCodeFeedback
          (ReferenceActiveHorizonMeasurability.roundRecordCode r) :=
        (ReferenceActiveHorizonMeasurability.roundRecordCode_front r).2.2.2.symm
      _ = ReferenceActiveHorizonMeasurability.roundRecordCodeFeedback
          (ReferenceActiveHorizonMeasurability.roundRecordCode r') :=
        congrArg ReferenceActiveHorizonMeasurability.roundRecordCodeFeedback hcode
      _ = r'.gridFeedback :=
        (ReferenceActiveHorizonMeasurability.roundRecordCode_front r').2.2.2
  have hownObservation : ∀ i,
      ReferenceFollowerDownDecoderReplay.preparedOwnObservation r i =
        ReferenceFollowerDownDecoderReplay.preparedOwnObservation r' i := by
    intro i
    unfold ReferenceFollowerDownDecoderReplay.preparedOwnObservation
    rw [r.output.preparation.feedback.observations_eq,
      r'.output.preparation.feedback.observations_eq]
    exact congrArg (fun feedback => ActualInitializationPhysicalStep.observationOfGrid p
      (feedback (PublicDiscreteDraws.followerPlayer p.two_le_m i))) hfeedback
  have hdownView : (ReferenceActivePhysicalStep.dispatch r.input).downView =
      (ReferenceActivePhysicalStep.dispatch r'.input).downView := by
    calc
      (ReferenceActivePhysicalStep.dispatch r.input).downView =
          (ReferenceActiveHorizonMeasurability.roundRecordCode r).2.2.1.2.1 :=
        (ReferenceActiveHorizonMeasurability.roundRecordCode_front r).2.1.symm
      _ = (ReferenceActiveHorizonMeasurability.roundRecordCode r').2.2.1.2.1 :=
        congrArg (fun code => code.2.2.1.2.1) hcode
      _ = (ReferenceActivePhysicalStep.dispatch r'.input).downView :=
        (ReferenceActiveHorizonMeasurability.roundRecordCode_front r').2.1
  exact ⟨hstate, hinputRow, htimeInput, hrewardInput, hcoordinator, hfollower,
    hown, hownObservation, hdownView⟩

private theorem recordPreparation_eq_prepare (r : Record (rate := rate)) :
    r.output.preparation = ReferenceActivePhysicalStep.prepare r.input := by
  calc
    r.output.preparation = (ReferenceActivePhysicalStep.step r.input).preparation :=
      congrArg (fun output : ReferenceActivePhysicalStep.RoundOutput r.input =>
        output.preparation) r.output_eq
    _ = ReferenceActivePhysicalStep.prepare r.input := rfl

private theorem preparedChoiceConfiguration_eq_of_input_data
    (r r' : Record (rate := rate)) (i : Fin (p.m - 1))
    (hstate : r.input.state = r'.input.state)
    (hrow : r.input.row = r'.input.row) (htime : r.input.time = r'.input.time) :
    ReferenceFollowerDownDecoderReplay.preparedChoiceConfiguration r i =
      ReferenceFollowerDownDecoderReplay.preparedChoiceConfiguration r' i := by
  change (r.output.preparation.followers.followers i).configuration =
    (r'.output.preparation.followers.followers i).configuration
  rw [recordPreparation_eq_prepare rate r, recordPreparation_eq_prepare rate r']
  change (DeclaredFollowerLocalRound.prepare rate i r.input.row
      (r.input.state.activations i) r.input.time (r.input.active i)
      (r.input.state.followers i)).configuration =
    (DeclaredFollowerLocalRound.prepare rate i r'.input.row
      (r'.input.state.activations i) r'.input.time (r'.input.active i)
      (r'.input.state.followers i)).configuration
  simp only [hstate.symm, hrow.symm, htime.symm]

private theorem actualDownPositives_singleton_eq_of_input_data
    (r r' : Record (rate := rate)) (i : Fin (p.m - 1))
    (hstate : r.input.state = r'.input.state)
    (hrow : r.input.row = r'.input.row) (htime : r.input.time = r'.input.time)
    (hobs : ReferenceFollowerDownDecoderReplay.preparedOwnObservation r i =
      ReferenceFollowerDownDecoderReplay.preparedOwnObservation r' i) :
    ReferenceFollowerDownDecoderReplay.actualDownPositives i [r] =
      ReferenceFollowerDownDecoderReplay.actualDownPositives i [r'] := by
  have hconfiguration := preparedChoiceConfiguration_eq_of_input_data rate r r' i hstate hrow htime
  have hpreparedRow : ReferenceFollowerDownDecoderReplay.preparedChoiceRow r i =
      ReferenceFollowerDownDecoderReplay.preparedChoiceRow r' i := by
    unfold ReferenceFollowerDownDecoderReplay.preparedChoiceRow
    rw [(r.output.preparation.follower_alignment i).1,
      (r'.output.preparation.follower_alignment i).1, hrow]
  have hpreparedTime : ReferenceFollowerDownDecoderReplay.preparedChoiceTime r i =
      ReferenceFollowerDownDecoderReplay.preparedChoiceTime r' i := by
    unfold ReferenceFollowerDownDecoderReplay.preparedChoiceTime
    rw [(r.output.preparation.follower_alignment i).2.2.1,
      (r'.output.preparation.follower_alignment i).2.2.1, htime]
  have hcall : ReferenceFollowerDownDecoderReplay.actualDownCall i r =
      ReferenceFollowerDownDecoderReplay.actualDownCall i r' := by
    simp only [ReferenceFollowerDownDecoderReplay.actualDownCall, hconfiguration,
      hpreparedRow, hpreparedTime, hobs]
  have hcalls : ReferenceFollowerDownDecoderReplay.actualDownCalls i [r] =
      ReferenceFollowerDownDecoderReplay.actualDownCalls i [r'] := by
    unfold ReferenceFollowerDownDecoderReplay.actualDownCalls
    simp only [List.filterMap_cons, List.filterMap_nil, hcall]
  unfold ReferenceFollowerDownDecoderReplay.actualDownPositives
  exact congrArg (ReferenceFollowerDownDecoderReplay.positiveCallEntries) hcalls

private theorem upSent_eq_of_input_data
    (r r' : Record (rate := rate)) (hstate : r.input.state = r'.input.state)
    (hrow : r.input.row = r'.input.row) (htime : r.input.time = r'.input.time) :
    ReferenceActiveAffinePositiveTest.upSent r.input =
      ReferenceActiveAffinePositiveTest.upSent r'.input := by
  rw [ReferenceUpPhysicalHashRule.upSent_eq_configuration,
    ReferenceUpPhysicalHashRule.upSent_eq_configuration]
  have hsender : ReferenceActivePhysicalStep.upSenderIndex r.input =
      ReferenceActivePhysicalStep.upSenderIndex r'.input := by
    rw [ReferenceActiveAffinePositiveTest.upSenderIndex_eq_draw,
      ReferenceActiveAffinePositiveTest.upSenderIndex_eq_draw, hrow, htime]
  have hconfiguration := preparedChoiceConfiguration_eq_of_input_data rate r r'
    (ReferenceActivePhysicalStep.upSenderIndex r'.input) hstate hrow htime
  have hpreparedConfiguration :
      ((ReferenceActivePhysicalStep.prepare r.input).followers.followers
        (ReferenceActivePhysicalStep.upSenderIndex r'.input)).configuration =
      ((ReferenceActivePhysicalStep.prepare r'.input).followers.followers
        (ReferenceActivePhysicalStep.upSenderIndex r'.input)).configuration := by
    rw [← recordPreparation_eq_prepare rate r, ← recordPreparation_eq_prepare rate r']
    exact hconfiguration
  rw [hsender, hpreparedConfiguration]
  simp only [hrow.symm, htime.symm, hstate.symm]

private theorem downSent_eq_of_record_data
    (r r' : Record (rate := rate))
    (hrow : r.input.row = r'.input.row) (htime : r.input.time = r'.input.time)
    (hdownView : (ReferenceActivePhysicalStep.dispatch r.input).downView =
      (ReferenceActivePhysicalStep.dispatch r'.input).downView) :
    ReferenceActiveAffinePositiveTest.downSent r.input =
      ReferenceActiveAffinePositiveTest.downSent r'.input := by
  have hsender : ReferenceActivePhysicalStep.upSenderIndex r.input =
      ReferenceActivePhysicalStep.upSenderIndex r'.input := by
    rw [ReferenceActiveAffinePositiveTest.upSenderIndex_eq_draw,
      ReferenceActiveAffinePositiveTest.upSenderIndex_eq_draw, hrow, htime]
  unfold ReferenceActiveAffinePositiveTest.downSent
  rw [hdownView, hsender, hrow, htime]

private theorem physicalDownCompletedAt_congr
    (r r' : Record (rate := rate)) (i : Fin (p.m - 1)) (W : Batch (p := p))
    (hrow : r.input.row = r'.input.row) (htime : r.input.time = r'.input.time)
    (hfollowers : r.output.followers i = r'.output.followers i)
    (hobs : ReferenceFollowerDownDecoderReplay.preparedOwnObservation r i =
      ReferenceFollowerDownDecoderReplay.preparedOwnObservation r' i) :
    ReferenceLiteralSourceDecoderCoverage.physicalDownCompletedAt r i W ↔
      ReferenceLiteralSourceDecoderCoverage.physicalDownCompletedAt r' i W := by
  constructor
  · intro h
    unfold ReferenceLiteralSourceDecoderCoverage.physicalDownCompletedAt at h ⊢
    simpa only [hfollowers, hrow, htime, hobs] using h
  · intro h
    unfold ReferenceLiteralSourceDecoderCoverage.physicalDownCompletedAt at h ⊢
    simpa only [hfollowers.symm, hrow.symm, htime.symm, hobs.symm] using h

private theorem physicalUpCompletedAt_congr
    (r r' : Record (rate := rate)) (i : Fin (p.m - 1)) (W : Batch (p := p))
    (hcoordinator : r.output.coordinator = r'.output.coordinator) :
    ReferenceLiteralSourceDecoderCoverage.physicalUpCompletedAt r i W ↔
      ReferenceLiteralSourceDecoderCoverage.physicalUpCompletedAt r' i W := by
  constructor
  · intro h
    unfold ReferenceLiteralSourceDecoderCoverage.physicalUpCompletedAt at h ⊢
    simpa only [hcoordinator] using h
  · intro h
    unfold ReferenceLiteralSourceDecoderCoverage.physicalUpCompletedAt at h ⊢
    simpa only [hcoordinator.symm] using h

private theorem physicalAwaitedDownAt_congr
    (r r' : Record (rate := rate)) (i : Fin (p.m - 1))
    (w : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (hrow : r.input.row = r'.input.row) (htime : r.input.time = r'.input.time)
    (hfollowers : r.output.followers i = r'.output.followers i)
    (hdownSent : ReferenceActiveAffinePositiveTest.downSent r.input =
      ReferenceActiveAffinePositiveTest.downSent r'.input) :
    ReferenceLiteralSourceDecoderCoverage.physicalAwaitedDownAt r i w ↔
      ReferenceLiteralSourceDecoderCoverage.physicalAwaitedDownAt r' i w := by
  constructor
  · intro h
    unfold ReferenceLiteralSourceDecoderCoverage.physicalAwaitedDownAt at h ⊢
    simpa only [hrow, htime, hfollowers, hdownSent] using h
  · intro h
    unfold ReferenceLiteralSourceDecoderCoverage.physicalAwaitedDownAt at h ⊢
    simpa only [hrow.symm, htime.symm, hfollowers.symm, hdownSent.symm] using h

private theorem physicalAwaitedUpAt_congr
    (r r' : Record (rate := rate)) (i : Fin (p.m - 1))
    (M : OrdinaryMessageCodec.UpRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (hcoordinator : r.output.coordinator = r'.output.coordinator)
    (hupSent : ReferenceActiveAffinePositiveTest.upSent r.input =
      ReferenceActiveAffinePositiveTest.upSent r'.input) :
    ReferenceLiteralSourceDecoderCoverage.physicalAwaitedUpAt r i M ↔
      ReferenceLiteralSourceDecoderCoverage.physicalAwaitedUpAt r' i M := by
  constructor
  · intro h
    unfold ReferenceLiteralSourceDecoderCoverage.physicalAwaitedUpAt at h ⊢
    simpa only [hcoordinator, hupSent] using h
  · intro h
    unfold ReferenceLiteralSourceDecoderCoverage.physicalAwaitedUpAt at h ⊢
    simpa only [hcoordinator.symm, hupSent.symm] using h

private theorem recordUpPositiveEntries_eq_of_coordinator
    (r r' : Record (rate := rate)) (i : Fin (p.m - 1))
    (hcoordinator : r.output.coordinator = r'.output.coordinator) :
    ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries r i =
      ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries r' i := by
  simp only [ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries, hcoordinator]

private theorem literalDownAmbiguityAt_transfer_of_source_data
    (z z' : Source (p := p)) (j : Fin (M p)) (t : Fin p.T)
    (hids : z.1.1 = z'.1.1) (hprivate : z.2 = z'.2)
    (hJ : ActualInitializationPhysicalStep.selectedRowIndex p z = j)
    (hrow : z.1.2 j = z'.1.2 j) :
    ReferenceLiteralSourceDecoderCoverage.literalDownAmbiguityAt
        rate rewards C_star C_h z t →
      ReferenceLiteralSourceDecoderCoverage.literalDownAmbiguityAt
        rate rewards C_star C_h z' t := by
  intro h
  obtain ⟨r, i, w, W, a, hr, hcomplete, hat, hmulti, hentries, hcalendar⟩ := h
  obtain ⟨r', hr', hcode⟩ := actualRecord_correspondence_of_source_data
    rate rewards C_star C_h z z' j t hids hprivate hJ hrow r hr
  obtain ⟨hstate, hrowRecord, htimeRecord, _, hcoordinator, hfollowers, _,
      hobs, hdownView⟩ := recordObservationData_eq_of_source_data
    rate rewards C_star C_h z z' j t hprivate hJ hrow r r' hr hr' hcode
  have hcomplete' := (physicalDownCompletedAt_congr rate r r' i W hrowRecord
    htimeRecord (hfollowers i) (hobs i)).mp hcomplete
  have hJ' := selectedRowIndex_eq_of_private z z' j hprivate hJ
  have hchannel : ∀ v : Fin p.T,
      ReferenceSelectedAffinePairLaw.selectedChannel p
        ((z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)).2 v).1 =
      ReferenceSelectedAffinePairLaw.selectedChannel p
        ((z'.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z')).2 v).1 := by
    intro v
    rw [hJ, hJ', hrow]
  refine ⟨r', i, w, W, a, hr', hcomplete', hat, hmulti, ?_, ?_⟩
  · intro e he
    obtain ⟨ha, ht, heq, re, hre, _, _, _, _, _, hpositive, haw⟩ := hentries e he
    obtain ⟨re', hre', hcodeRe⟩ := actualRecord_correspondence_of_source_data
      rate rewards C_star C_h z z' j e.time hids hprivate hJ hrow re hre
    obtain ⟨hstateRe, hrowRe, htimeRe, _, hcoordRe, hfollowersRe, _, hobsRe,
      hdownViewRe⟩ := recordObservationData_eq_of_source_data
        rate rewards C_star C_h z z' j e.time hprivate hJ hrow re re' hre hre' hcodeRe
    have hposEq := actualDownPositives_singleton_eq_of_input_data
      rate re re' i hstateRe hrowRe htimeRe (hobsRe i)
    have hpositive' : e ∈ ReferenceFollowerDownDecoderReplay.actualDownPositives i [re'] := by
      rw [← hposEq]
      exact hpositive
    have hrecordFields := ReferenceLiteralSourceDecoderCoverage.actualRecord_original_fields
      rate rewards C_star C_h z' e.time re' hre'
    have hsample := (ReferenceLiteralSourceDecoderCoverage.downPositiveEntry_original_coordinates
      re' i e hpositive').2
    change e.sample = ((re'.input.rows re'.input.selected).2 re'.input.time).2 (0, i) at hsample
    rw [hrecordFields.1, hrecordFields.2.1, hrecordFields.2.2.1] at hsample
    have hdownSent := downSent_eq_of_record_data rate re re' hrowRe htimeRe hdownViewRe
    have haw' := (physicalAwaitedDownAt_congr rate re re' i w hrowRe htimeRe
      (hfollowersRe i) hdownSent).mp haw
    exact ⟨ha, ht, heq, re', hre', hrecordFields.1, hrecordFields.2.1,
      hrecordFields.2.2.1, hrecordFields.2.2.2, hsample, hpositive', haw'⟩
  · intro v ha ht hselectedRight
    have hselectedLeft : ReferenceSelectedAffinePairLaw.selectedChannel p
        ((z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)).2 v).1 = some (0, i) :=
      (hchannel v).trans hselectedRight
    obtain ⟨rv, hrv, _, _, _, _, haw⟩ := hcalendar v ha ht hselectedLeft
    obtain ⟨rv', hrv', hcodeV⟩ := actualRecord_correspondence_of_source_data
      rate rewards C_star C_h z z' j v hids hprivate hJ hrow rv hrv
    obtain ⟨_, hrowV, htimeV, _, _, hfollowersV, _, hobsV, hdownViewV⟩ :=
      recordObservationData_eq_of_source_data
        rate rewards C_star C_h z z' j v hprivate hJ hrow rv rv' hrv hrv' hcodeV
    have hdownSentV := downSent_eq_of_record_data rate rv rv' hrowV htimeV hdownViewV
    have haw' := (physicalAwaitedDownAt_congr rate rv rv' i w hrowV htimeV
      (hfollowersV i) hdownSentV).mp haw
    obtain ⟨hrowsV, hselectedV, htimeFieldsV, hrewardsV⟩ :=
      ReferenceLiteralSourceDecoderCoverage.actualRecord_original_fields
        rate rewards C_star C_h z' v rv' hrv'
    exact ⟨rv', hrv', hrowsV, hselectedV, htimeFieldsV, hrewardsV, haw'⟩

private theorem literalUpAmbiguityAt_transfer_of_source_data
    (z z' : Source (p := p)) (j : Fin (M p)) (t : Fin p.T)
    (hids : z.1.1 = z'.1.1) (hprivate : z.2 = z'.2)
    (hJ : ActualInitializationPhysicalStep.selectedRowIndex p z = j)
    (hrow : z.1.2 j = z'.1.2 j) :
    ReferenceLiteralSourceDecoderCoverage.literalUpAmbiguityAt
        rate rewards C_star C_h z t →
      ReferenceLiteralSourceDecoderCoverage.literalUpAmbiguityAt
        rate rewards C_star C_h z' t := by
  intro h
  obtain ⟨r, i, M, W, a, hr, hcomplete, hat, hsigma, hmulti, hentries, hcalendar⟩ := h
  obtain ⟨r', hr', hcode⟩ := actualRecord_correspondence_of_source_data
    rate rewards C_star C_h z z' j t hids hprivate hJ hrow r hr
  obtain ⟨hstate, hrowRecord, htimeRecord, _, hcoordinator, hfollowers, _,
      hobs, hdownView⟩ := recordObservationData_eq_of_source_data
    rate rewards C_star C_h z z' j t hprivate hJ hrow r r' hr hr' hcode
  have hcomplete' := (physicalUpCompletedAt_congr rate r r' i W hcoordinator).mp hcomplete
  have hJ' := selectedRowIndex_eq_of_private z z' j hprivate hJ
  have hchannel : ∀ v : Fin p.T,
      ReferenceSelectedAffinePairLaw.selectedChannel p
        ((z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)).2 v).1 =
      ReferenceSelectedAffinePairLaw.selectedChannel p
        ((z'.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z')).2 v).1 := by
    intro v
    rw [hJ, hJ', hrow]
  refine ⟨r', i, M, W, a, hr', hcomplete', hat, hsigma, hmulti, ?_, ?_⟩
  · intro e he
    obtain ⟨ha, ht, heq, re, hre, _, _, _, _, _, hpositive, haw⟩ := hentries e he
    obtain ⟨re', hre', hcodeRe⟩ := actualRecord_correspondence_of_source_data
      rate rewards C_star C_h z z' j e.time hids hprivate hJ hrow re hre
    obtain ⟨hstateRe, hrowRe, htimeRe, _, hcoordRe, hfollowersRe, _, hobsRe,
      hdownViewRe⟩ := recordObservationData_eq_of_source_data
        rate rewards C_star C_h z z' j e.time hprivate hJ hrow re re' hre hre' hcodeRe
    have hpositiveEq := recordUpPositiveEntries_eq_of_coordinator rate re re' i hcoordRe
    have hpositive' : e ∈ ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries re' i := by
      rw [← hpositiveEq]
      exact hpositive
    have hrecordFields := ReferenceLiteralSourceDecoderCoverage.actualRecord_original_fields
      rate rewards C_star C_h z' e.time re' hre'
    have hsample := (ReferenceLiteralSourceDecoderCoverage.upPositiveEntry_original_coordinates
      re' i e hpositive').2
    change e.sample = ((re'.input.rows re'.input.selected).2 re'.input.time).2 (1, i) at hsample
    rw [hrecordFields.1, hrecordFields.2.1, hrecordFields.2.2.1] at hsample
    have hupSent := upSent_eq_of_input_data rate re re' hstateRe hrowRe htimeRe
    have haw' := (physicalAwaitedUpAt_congr rate re re' i M hcoordRe hupSent).mp haw
    exact ⟨ha, ht, heq, re', hre', hrecordFields.1, hrecordFields.2.1,
      hrecordFields.2.2.1, hrecordFields.2.2.2, hsample, hpositive', haw'⟩
  · intro v ha ht hselectedRight
    have hselectedLeft : ReferenceSelectedAffinePairLaw.selectedChannel p
        ((z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)).2 v).1 = some (1, i) :=
      (hchannel v).trans hselectedRight
    obtain ⟨rv, hrv, _, _, _, _, haw⟩ := hcalendar v ha ht hselectedLeft
    obtain ⟨rv', hrv', hcodeV⟩ := actualRecord_correspondence_of_source_data
      rate rewards C_star C_h z z' j v hids hprivate hJ hrow rv hrv
    obtain ⟨hstateV, hrowV, htimeV, _, hcoordinatorV, _, _, _, _⟩ :=
      recordObservationData_eq_of_source_data
        rate rewards C_star C_h z z' j v hprivate hJ hrow rv rv' hrv hrv' hcodeV
    have hupSentV := upSent_eq_of_input_data rate rv rv' hstateV hrowV htimeV
    have haw' := (physicalAwaitedUpAt_congr rate rv rv' i M hcoordinatorV hupSentV).mp haw
    obtain ⟨hrowsV, hselectedV, htimeFieldsV, hrewardsV⟩ :=
      ReferenceLiteralSourceDecoderCoverage.actualRecord_original_fields
        rate rewards C_star C_h z' v rv' hrv'
    exact ⟨rv', hrv', hrowsV, hselectedV, htimeFieldsV, hrewardsV, haw'⟩

/-- The existing literal DOWN ambiguity event depends on the original source
through public IDs, original private coordinates, the selected-row index, and
the complete selected row. -/
theorem literalDownAmbiguityAt_iff_of_source_data
    (z z' : Source (p := p)) (j : Fin (M p)) (t : Fin p.T)
    (hids : z.1.1 = z'.1.1) (hprivate : z.2 = z'.2)
    (hJ : ActualInitializationPhysicalStep.selectedRowIndex p z = j)
    (hrow : z.1.2 j = z'.1.2 j) :
    ReferenceLiteralSourceDecoderCoverage.literalDownAmbiguityAt
        rate rewards C_star C_h z t ↔
      ReferenceLiteralSourceDecoderCoverage.literalDownAmbiguityAt
        rate rewards C_star C_h z' t := by
  constructor
  · exact literalDownAmbiguityAt_transfer_of_source_data
      rate rewards C_star C_h z z' j t hids hprivate hJ hrow
  · have hJ' := selectedRowIndex_eq_of_private z z' j hprivate hJ
    exact literalDownAmbiguityAt_transfer_of_source_data
      rate rewards C_star C_h z' z j t hids.symm hprivate.symm hJ' hrow.symm

/-- The existing literal UP ambiguity event depends on the original source
through public IDs, original private coordinates, the selected-row index, and
the complete selected row. -/
theorem literalUpAmbiguityAt_iff_of_source_data
    (z z' : Source (p := p)) (j : Fin (M p)) (t : Fin p.T)
    (hids : z.1.1 = z'.1.1) (hprivate : z.2 = z'.2)
    (hJ : ActualInitializationPhysicalStep.selectedRowIndex p z = j)
    (hrow : z.1.2 j = z'.1.2 j) :
    ReferenceLiteralSourceDecoderCoverage.literalUpAmbiguityAt
        rate rewards C_star C_h z t ↔
      ReferenceLiteralSourceDecoderCoverage.literalUpAmbiguityAt
        rate rewards C_star C_h z' t := by
  constructor
  · exact literalUpAmbiguityAt_transfer_of_source_data
      rate rewards C_star C_h z z' j t hids hprivate hJ hrow
  · have hJ' := selectedRowIndex_eq_of_private z z' j hprivate hJ
    exact literalUpAmbiguityAt_transfer_of_source_data
      rate rewards C_star C_h z' z j t hids.symm hprivate.symm hJ' hrow.symm

/-- The complete literal ambiguity disjunction is invariant under changes to
unselected rows when all original private coordinates and the selected row
are held fixed. -/
theorem S_amb_iff_of_source_data
    (z z' : Source (p := p)) (j : Fin (M p)) (t : Fin p.T)
    (hids : z.1.1 = z'.1.1) (hprivate : z.2 = z'.2)
    (hJ : ActualInitializationPhysicalStep.selectedRowIndex p z = j)
    (hrow : z.1.2 j = z'.1.2 j) :
    ReferenceLiteralSourceDecoderCoverage.S_amb rate rewards C_star C_h z t ↔
      ReferenceLiteralSourceDecoderCoverage.S_amb rate rewards C_star C_h z' t := by
  change ReferenceLiteralSourceDecoderCoverage.literalDownAmbiguityAt
      rate rewards C_star C_h z t ∨
      ReferenceLiteralSourceDecoderCoverage.literalUpAmbiguityAt
        rate rewards C_star C_h z t ↔
    ReferenceLiteralSourceDecoderCoverage.literalDownAmbiguityAt
      rate rewards C_star C_h z' t ∨
      ReferenceLiteralSourceDecoderCoverage.literalUpAmbiguityAt
        rate rewards C_star C_h z' t
  exact or_congr
    (literalDownAmbiguityAt_iff_of_source_data rate rewards C_star C_h
      z z' j t hids hprivate hJ hrow)
    (literalUpAmbiguityAt_iff_of_source_data rate rewards C_star C_h
      z z' j t hids hprivate hJ hrow)

/-- The literal ambiguity scan over `t.val < n` has the same selected-row
locality, including the endpoint `n = t.val + 1`. -/
theorem S_amb_prefix_iff_of_source_data
    (z z' : Source (p := p)) (j : Fin (M p)) (n : ℕ)
    (hids : z.1.1 = z'.1.1) (hprivate : z.2 = z'.2)
    (hJ : ActualInitializationPhysicalStep.selectedRowIndex p z = j)
    (hrow : z.1.2 j = z'.1.2 j) :
    S_amb_prefix rate rewards C_star C_h n z ↔
      S_amb_prefix rate rewards C_star C_h n z' := by
  unfold S_amb_prefix
  constructor
  · rintro ⟨t, htn, hamb⟩
    exact ⟨t, htn,
      (S_amb_iff_of_source_data rate rewards C_star C_h z z' j t
        hids hprivate hJ hrow).mp hamb⟩
  · rintro ⟨t, htn, hamb⟩
    exact ⟨t, htn,
      (S_amb_iff_of_source_data rate rewards C_star C_h z z' j t
        hids hprivate hJ hrow).mpr hamb⟩

/-- Replacing the original selected complete row by one shared row leaves
the literal DOWN, UP, disjunctive, and finite-prefix observations unchanged.
The same original private arrays, including the coordinator index, are used on
both sides. -/
theorem selectedRow_update_observation
    (ids : CompletePublicTable.IDArray p)
    (rows otherRows : CompletePublicTable.CompleteRows p) (j : Fin (M p))
    (rho : CompletePublicTable.CompleteRow p)
    (e : BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
    (hJ : PrivateSourceStreams.coordinatorIndex p e.1.2 = j)
    (t : Fin p.T) (n : ℕ) :
    (ReferenceLiteralSourceDecoderCoverage.literalDownAmbiguityAt rate rewards C_star C_h
        ((ids, Function.update rows j rho), e) t ↔
      ReferenceLiteralSourceDecoderCoverage.literalDownAmbiguityAt rate rewards C_star C_h
        ((ids, Function.update otherRows j rho), e) t) ∧
    (ReferenceLiteralSourceDecoderCoverage.literalUpAmbiguityAt rate rewards C_star C_h
        ((ids, Function.update rows j rho), e) t ↔
      ReferenceLiteralSourceDecoderCoverage.literalUpAmbiguityAt rate rewards C_star C_h
        ((ids, Function.update otherRows j rho), e) t) ∧
    (ReferenceLiteralSourceDecoderCoverage.S_amb rate rewards C_star C_h
        ((ids, Function.update rows j rho), e) t ↔
      ReferenceLiteralSourceDecoderCoverage.S_amb rate rewards C_star C_h
        ((ids, Function.update otherRows j rho), e) t) ∧
    (S_amb_prefix rate rewards C_star C_h n ((ids, Function.update rows j rho), e) ↔
      S_amb_prefix rate rewards C_star C_h n ((ids, Function.update otherRows j rho), e)) := by
  have hrow : (Function.update rows j rho) j = (Function.update otherRows j rho) j := by
    simp
  have hselected : ActualInitializationPhysicalStep.selectedRowIndex p
      ((ids, Function.update rows j rho), e) = j := by
    change PrivateSourceStreams.coordinatorIndex p e.1.2 = j
    exact hJ
  have hids : ids = ids := rfl
  have hprivate : e = e := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact literalDownAmbiguityAt_iff_of_source_data rate rewards C_star C_h
      ((ids, Function.update rows j rho), e)
      ((ids, Function.update otherRows j rho), e) j t hids hprivate hselected hrow
  · exact literalUpAmbiguityAt_iff_of_source_data rate rewards C_star C_h
      ((ids, Function.update rows j rho), e)
      ((ids, Function.update otherRows j rho), e) j t hids hprivate hselected hrow
  · exact S_amb_iff_of_source_data rate rewards C_star C_h
      ((ids, Function.update rows j rho), e)
      ((ids, Function.update otherRows j rho), e) j t hids hprivate hselected hrow
  · exact S_amb_prefix_iff_of_source_data rate rewards C_star C_h
      ((ids, Function.update rows j rho), e)
      ((ids, Function.update otherRows j rho), e) j n hids hprivate hselected hrow

end Bandits.Support.ReferenceLiteralAwaitedAmbiguityRowObservation

end
