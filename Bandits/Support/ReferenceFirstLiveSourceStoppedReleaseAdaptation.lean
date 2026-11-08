/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveSourceStoppedReleaseEndpoint
public import Bandits.Support.ReferenceFirstLiveNumericalPrefixAdaptation
public import Bandits.Support.PhaseServiceWaiting

/-!
# Adaptation of the actual stopped first release

Sources: `sources/zip4/manuscript/05_binary_transport.tex:180-240,293-348`,
`04_slow_fast_learner.tex:140-188,256-264`, `07_public_setup.tex:127-164`,
and `08_main_theorem.tex:29-42,85-100`.

All observations below use the endpoint module's literal support and dates on
the original whole source. The overflow mask tests only earlier updates, so
the first crossing update is retained. These results concern the source-prefix
filtration; they assert no manuscript-history identity or conditional law.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open scoped Classical

namespace Bandits.Support.ReferenceFirstLiveSourceStoppedReleaseAdaptation

open ReferenceFirstLiveSourceStoppedReleaseEndpoint
open ReferenceFirstWindowNumericalStream

variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ)

/-- Both actual strict-past decoder flags persist when the past is extended.
The witnesses remain the same original calendar record or prelaunch decision. -/
theorem actual_decoder_flag_persistent (z : Source p) (a b : ℕ)
    (ha : a ≤ p.T) (hb : b ≤ p.T) (hab : a ≤ b)
    (hflag : actualDecoderFlag rate rewards C_star C_h z a ha = true) :
    actualDecoderFlag rate rewards C_star C_h z b hb = true := by
  simp only [actualDecoderFlag, Bool.or_eq_true] at hflag ⊢
  rcases hflag with hpre | hpost
  · left
    simp only [ReferencePrelaunchDownDecisionReadout.prelaunchPastDecoderFlag,
      decide_eq_true_eq] at hpre ⊢
    obtain ⟨j, i, hj⟩ := hpre
    exact ⟨Fin.castLE hab j, i, hj⟩
  · right
    rw [ReferenceFirstLiveDecoderPastMeasurability.strictPastDecoderFlag_eq_true_iff] at hpost ⊢
    obtain ⟨j, r, hr, hf⟩ := hpost
    exact ⟨Fin.castLE hab j, r, hr, hf⟩

/-- At initialization there are no earlier decoder observations. -/
theorem actual_decoder_flag_zero (z : Source p) :
    actualDecoderFlag rate rewards C_star C_h z 0 (Nat.zero_le _) = false := by
  simp only [actualDecoderFlag,
    ReferencePrelaunchDownDecisionReadout.prelaunchPastDecoderFlag_zero,
    ReferenceFirstLiveDecoderPastMeasurability.strictPastDecoderFlag_zero,
    Bool.false_or]

/-- Persistence reduces the endpoint's all-earlier-flags test to the current
strict-past Boolean. This does not inspect the current round's diagnostics. -/
theorem decoder_cutoff_iff_current_false (t : Fin p.T) (z : Source p) :
    t.val + 1 < decoderFirstExcluded rate rewards C_star C_h z ↔
      actualDecoderFlag rate rewards C_star C_h z t.val (Nat.le_of_lt t.isLt) = false := by
  rw [decoder_cutoff_after_current_iff]
  constructor
  · intro h
    exact h ⟨t.val, Nat.lt_succ_self _⟩
  · intro h j
    cases hj : actualDecoderFlag rate rewards C_star C_h z j.val
        (by have h := j.isLt; omega) with
    | false => rfl
    | true =>
        have htrue := actual_decoder_flag_persistent rate rewards C_star C_h z
          j.val t.val (by have h := j.isLt; omega) (Nat.le_of_lt t.isLt)
          (by have h := j.isLt; omega) hj
        rw [h] at htrue
        cases htrue

private theorem gate_launch_facts (t : Fin p.T) (z : Source p)
    (hg : t.val + 1 ∈ actualGateSupport rate rewards C_star C_h z) :
    (ReferenceCompletePhysicalHistory.generatedBoundary rate z rewards C_star C_h).crossing.isSome = true ∧
      physicalStart rate rewards C_star C_h z ≤ t.val := by
  have he := (actual_gate_support_mem_iff_entry rate rewards C_star C_h z t).mp hg
  have hr : ∃ r, ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t z = some r := by
    cases h : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z with
    | none => simp [ReferenceSourcePrefixHistoryFiltration.entry,
        ReferenceSourcePrefixHistoryFiltration.incoming, h] at he
    | some r => exact ⟨r, rfl⟩
  obtain ⟨r, hr⟩ := hr
  constructor
  · cases hc : (ReferenceCompletePhysicalHistory.generatedBoundary
        rate z rewards C_star C_h).crossing with
    | none =>
        rw [ReferenceSourcePrefixHistoryFiltration.actualRecord_eq_none_of_no_crossing
          rate rewards C_star C_h t z hc] at hr
        cases hr
    | some c => rfl
  · by_contra h
    rw [ReferenceSourcePrefixHistoryFiltration.actualRecord_eq_none_of_future_start
      rate rewards C_star C_h t z (Nat.lt_of_not_ge h)] at hr
    cases hr

section Stratum

variable (q : Fin (M p)) (t : Fin p.T) (s : ℕ) (hs : s ≤ t.val)

local notation "Z" => ReferenceTotalSourceDisintegration.SourceStratum rate rewards C_star C_h t
  (ReferenceFirstLiveRecordingSourceCylinder.stratumIndex q t s hs)
local notation "n" => t.val - s

private theorem whole_records_eq (z : Z) :
    completeRecords rate rewards C_star C_h z.val =
      (actualFirstLiveRun rate z.val rewards C_star C_h
        (ReferenceFirstLiveNumericalPrefixTemporal.sourceStratum_facts
          rate rewards C_star C_h q t s hs z).2.1
        (p.T - s) (by
          have hz := ReferenceFirstLiveNumericalPrefixTemporal.sourceStratum_facts
            rate rewards C_star C_h q t s hs z
          rw [hz.2.2]
          omega)).records := by
  have hz := ReferenceFirstLiveNumericalPrefixTemporal.sourceStratum_facts
    rate rewards C_star C_h q t s hs z
  have hl := ReferenceFirstLaunchNumericalCell.correctedLaunch_eq_some_launchState
    rate z.val rewards C_star C_h hz.2.1
  simpa only [completeRecords, actualFirstLiveRun, physicalStart,
    ReferenceCompletePhysicalHistory.physicalStart,
    ReferenceCompletePhysicalHistory.generatedBoundary,
    ReferenceCompletePhysicalHistory.generatedInput, hz.2.2] using
    ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
      rate z.val rewards C_star C_h _ hl

private theorem whole_window_take (z : Z) :
    (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow rate rewards C_star C_h z.val).take n =
      actualFirstLiveWindow rate z.val rewards C_star C_h
        (ReferenceFirstLiveNumericalPrefixTemporal.sourceStratum_facts
          rate rewards C_star C_h q t s hs z).2.1 n (by
          have hz := ReferenceFirstLiveNumericalPrefixTemporal.sourceStratum_facts
            rate rewards C_star C_h q t s hs z
          rw [hz.2.2]
          omega) := by
  have hz := ReferenceFirstLiveNumericalPrefixTemporal.sourceStratum_facts
    rate rewards C_star C_h q t s hs z
  let initial := ReferenceFirstLaunchNumericalCell.launchState rate z.val rewards C_star C_h hz.2.1
  have hmode := (actualFirstLiveSeed rate z.val rewards C_star C_h hz.2.1).activeAtStart
  obtain ⟨tail, hrecords⟩ := ReferenceCollectionPhaseHistory.run_records_prefix initial z.val.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p z.val) rewards
    (ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z.val rewards C_star C_h rate)).completed)
    n (p.T - s - n) (by rw [hz.2.2]; omega) hmode
  have hcount : n + (p.T - s - n) = p.T - s := by have ht := t.isLt; omega
  have hrecords' : (ReferenceActivePhysicalHorizon.run initial z.val.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p z.val) rewards _ (p.T - s)
      (by rw [hz.2.2]; omega) hmode).records =
        (ReferenceActivePhysicalHorizon.run initial z.val.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p z.val) rewards _ n
          (by rw [hz.2.2]; omega) hmode).records ++ tail := by
    simpa only [hcount] using hrecords
  have hlen := ReferenceActivePhysicalHorizon.run_record_count initial z.val.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p z.val) rewards _ n
    (by rw [hz.2.2]; omega) hmode
  change (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
    (completeRecords rate rewards C_star C_h z.val)).take n = _
  rw [whole_records_eq rate rewards C_star C_h q t s hs z]
  change ((actualFirstLiveRun rate z.val rewards C_star C_h hz.2.1 (p.T - s) _).records.takeWhile
    (fun r => !ReferenceCollectionPhaseHistory.cutoffChosen r.input)).take n = _
  rw [List.take_takeWhile]
  change ((ReferenceActivePhysicalHorizon.run initial z.val.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p z.val) rewards _ (p.T - s) _ hmode).records.take n).takeWhile _ = _
  rw [hrecords', List.take_append_of_le_length (le_of_eq hlen.symm),
    List.take_of_length_le (le_of_eq hlen)]
  rfl

private theorem whole_cells_take (z : Z) :
    (ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells rate rewards C_star C_h z.val).take n =
      actualLiveSourceCells rate z.val rewards C_star C_h
        (ReferenceFirstLiveNumericalPrefixTemporal.sourceStratum_facts
          rate rewards C_star C_h q t s hs z).2.1 n (by
          have hz := ReferenceFirstLiveNumericalPrefixTemporal.sourceStratum_facts
            rate rewards C_star C_h q t s hs z
          rw [hz.2.2]
          omega) := by
  have hz := ReferenceFirstLiveNumericalPrefixTemporal.sourceStratum_facts
    rate rewards C_star C_h q t s hs z
  have hfull : ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z.val rewards C_star C_h rate)).completed +
      (p.T - s) ≤ p.T := by rw [hz.2.2]; omega
  have hpast : ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z.val rewards C_star C_h rate)).completed +
      n ≤ p.T := by rw [hz.2.2]; omega
  let sf : Fin (p.T + 1) := ⟨s, by have ht := t.isLt; omega⟩
  let x : ReferenceFirstLiveOverflowReadout.LaunchFiber rate rewards C_star C_h s :=
    ⟨z.val, hz.2⟩
  have hwhole := ReferenceFirstLiveOverflowReadout.wholeFirstLive_on_fiber
    rate rewards C_star C_h sf x
  have hwindow := whole_window_take rate rewards C_star C_h q t s hs z
  rw [hwhole.1] at hwindow
  rw [hwhole.2]
  change (actualLiveSourceCells rate z.val rewards C_star C_h hz.2.1 (p.T - s) _).take n = _
  change (actualFirstLiveWindow rate z.val rewards C_star C_h hz.2.1 (p.T - s) _).take n = _ at hwindow
  apply List.ext_getElem
  · have h := congrArg List.length hwindow
    simpa only [List.length_take, actualLiveSourceCells_length] using h
  · intro j hja hjb
    have hb : j < min n (actualLiveSourceCells rate z.val rewards C_star C_h hz.2.1
        (p.T - s) hfull).length := by simpa only [List.length_take] using hja
    have hjn : j < n := lt_of_lt_of_le hb (Nat.min_le_left _ _)
    have hjA : j < (actualFirstLiveWindow rate z.val rewards C_star C_h hz.2.1
        (p.T - s) hfull).length := by
      rw [← actualLiveSourceCells_length]
      exact lt_of_lt_of_le hb (Nat.min_le_right _ _)
    have hjB : j < (actualFirstLiveWindow rate z.val rewards C_star C_h hz.2.1 n hpast).length := by
      simpa only [actualLiveSourceCells_length] using hjb
    have he := congrArg (fun records : List (ReferenceActivePhysicalHorizon.RoundRecord
      (p := p) (rate := rate)) => records[j]?) hwindow
    rw [List.getElem?_take_of_lt hjn, List.getElem?_eq_getElem hjA,
      List.getElem?_eq_getElem hjB] at he
    have hr := Option.some.inj he
    have hc : ∀ {r₁ r₂ : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)},
        r₁ = r₂ → (a : ActualLiveSourceCell r₁) → (b : ActualLiveSourceCell r₂) →
          a.input = b.input := by
      intro r₁ r₂ h a b
      cases h
      exact ReferenceFirstLiveNumericalPrefixTemporal.actualLiveSourceCell_input_unique a b
    have hi := hc hr
      (actualLiveSourceCellAt rate z.val rewards C_star C_h hz.2.1 (p.T - s) hfull ⟨j, hjA⟩)
      (actualLiveSourceCellAt rate z.val rewards C_star C_h hz.2.1 n hpast ⟨j, hjB⟩)
    simpa only [actualLiveSourceCells, List.getElem_take, List.getElem_ofFn] using hi

private theorem gate_in_whole_window (z : Z)
    (hg : t.val + 1 ∈ actualGateSupport rate rewards C_star C_h z.val) :
    n < ReferenceFirstLiveOverflowReadout.wholeFirstLiveLength rate rewards C_star C_h z.val := by
  have hz := ReferenceFirstLiveNumericalPrefixTemporal.sourceStratum_facts
    rate rewards C_star C_h q t s hs z
  let initial := ReferenceFirstLaunchNumericalCell.launchState rate z.val rewards C_star C_h hz.2.1
  have hmode := (actualFirstLiveSeed rate z.val rewards C_star C_h hz.2.1).activeAtStart
  have hspan : ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z.val rewards C_star C_h rate)).completed +
      (p.T - s) ≤ p.T := by rw [hz.2.2]; omega
  have hstart : physicalStart rate rewards C_star C_h z.val = s := hz.2.2
  have hg' : t.val + 1 ∈ ReferenceLocalReleaseGateChronology.gateSupport
      (ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z.val rewards C_star C_h rate)).completed)
      (ReferenceActivePhysicalHorizon.run initial z.val.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p z.val) rewards _ (p.T - s) hspan hmode).records := by
    simpa only [actualGateSupport, whole_records_eq rate rewards C_star C_h q t s hs z,
      hstart, actualFirstLiveRun, hz.2.2, initial] using hg
  obtain ⟨j, hjgate, hjtime⟩ := (ReferenceLocalReleaseGateChronology.mem_run_gateSupport
    initial z.val.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z.val)
    rewards _ hmode (p.T - s) hspan _ (t.val + 1)).mp hg'
  have hjn : j.val = n := by rw [hz.2.2] at hjtime; omega
  have hrecord := ReferenceLocalReleaseGateChronology.run_record_at
    initial z.val.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z.val)
    rewards _ hmode (p.T - s) hspan j
  have hjgate' : ReferenceRetainedReleasePhaseObservation.localReleaseGate rate
      (ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z.val rewards C_star C_h rate)).completed)
      ((ReferenceLocalReleaseGateChronology.sourceRun rate z.val rewards C_star C_h hz.2.1
        _ (p.T - s) rfl hspan).records[j.val]'(by
          simpa only [ReferenceLocalReleaseGateChronology.sourceRun,
            ReferenceActivePhysicalHorizon.run_record_count] using j.isLt)).input.time
      (ReferenceActivePhysicalStepMeasurability.encodeState
        ((ReferenceLocalReleaseGateChronology.sourceRun rate z.val rewards C_star C_h hz.2.1
          _ (p.T - s) rfl hspan).records[j.val]'(by
            simpa only [ReferenceLocalReleaseGateChronology.sourceRun,
              ReferenceActivePhysicalHorizon.run_record_count] using j.isLt)).input.state) = true := by
    change ReferenceRetainedReleasePhaseObservation.localReleaseGate rate _
      ((ReferenceActivePhysicalHorizon.run initial z.val.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p z.val) rewards _ (p.T - s)
        hspan hmode).records[j.val]'(by
          rw [ReferenceActivePhysicalHorizon.run_record_count]; exact j.isLt)).input.time
      (ReferenceActivePhysicalStepMeasurability.encodeState
        ((ReferenceActivePhysicalHorizon.run initial z.val.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p z.val) rewards _ (p.T - s)
          hspan hmode).records[j.val]'(by
            rw [ReferenceActivePhysicalHorizon.run_record_count]; exact j.isLt)).input.state) = true
    rw [hrecord]
    exact hjgate
  have hwin := ReferenceFirstLiveSourceReleaseSupport.actual_first_live_gate_in_window
    z.val rewards C_star C_h (p.T - s) hspan hz.2.1 j hjgate'
  change n < (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
    (completeRecords rate rewards C_star C_h z.val)).length
  rw [whole_records_eq rate rewards C_star C_h q t s hs z]
  simpa only [ReferenceLocalReleaseGateChronology.sourceRun,
    ReferenceLocalReleaseGateChronology.sourceSeed, actualFirstLiveRun,
    ReferenceFirstLaunchNumericalCell.launchState, hjn] using hwin

private theorem overflow_cutoff_iff (control0 : ContinuousLearningRows.TimeControl p) (z : Z)
    (hg : t.val + 1 ∈ actualGateSupport rate rewards C_star C_h z.val) :
    t.val + 1 < overflowFirstExcluded rate rewards C_star C_h z.val ↔
      (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate)
        ((actualLiveSourceCells rate z.val rewards C_star C_h
          (ReferenceFirstLiveNumericalPrefixTemporal.sourceStratum_facts
            rate rewards C_star C_h q t s hs z).2.1 (n + 1) (by
            have hz := ReferenceFirstLiveNumericalPrefixTemporal.sourceStratum_facts
              rate rewards C_star C_h q t s hs z
            rw [hz.2.2]
            omega)).take n)).overflow = false := by
  have hz := ReferenceFirstLiveNumericalPrefixTemporal.sourceStratum_facts
    rate rewards C_star C_h q t s hs z
  have hwindow := gate_in_whole_window rate rewards C_star C_h q t s hs z hg
  let sf : Fin (p.T + 1) := ⟨s, by have ht := t.isLt; omega⟩
  let x : ReferenceFirstLiveOverflowReadout.LaunchFiber rate rewards C_star C_h s := ⟨z.val, hz.2⟩
  have hwhole := ReferenceFirstLiveOverflowReadout.wholeFirstLive_on_fiber
    rate rewards C_star C_h sf x
  have hlength : (ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells
      rate rewards C_star C_h z.val).length =
      ReferenceFirstLiveOverflowReadout.wholeFirstLiveLength rate rewards C_star C_h z.val := by
    rw [hwhole.2]
    change (actualLiveSourceCells rate z.val rewards C_star C_h hz.2.1 (p.T - s) _).length = _
    rw [actualLiveSourceCells_length]
    exact congrArg List.length hwhole.1.symm
  have hcross := UnstoppedRecordedQueueComparison.prefix_overflow_iff_first_overflow_prefix_le
    (ReferenceFirstLaunchNumericalCell.queueParameters rate)
    (ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells rate rewards C_star C_h z.val)
    n (by rw [hlength]; omega)
  have hdate : t.val + 1 < overflowFirstExcluded rate rewards C_star C_h z.val ↔
      n < ReferenceFirstLiveOverflowReadout.wholeFirstLiveOverflowPrefix rate rewards C_star C_h z.val := by
    unfold overflowFirstExcluded ReferenceFirstLiveOverflowReadout.wholeFirstLiveOverflowRound
    split_ifs with hk
    · simp only [Option.elim_some, lt_min_iff]
      have hstart : ReferenceCompletePhysicalHistory.physicalStart rate z.val rewards C_star C_h = s := hz.2.2
      rw [hstart]
      have ht := t.isLt
      omega
    · simp only [Option.elim_none]
      have ht := t.isLt
      omega
  rw [hdate]
  have halign := whole_cells_take rate rewards C_star C_h q t s hs z
  have hrun := ReferenceFirstLiveNumericalPrefixTemporal.numerical_run_count_eq
    rate rewards C_star C_h q t s hs control0 z
  rw [← halign] at hrun
  rw [hrun]
  change n < UnstoppedRecordedQueueComparison.firstOverflowPrefix
    (ReferenceFirstLaunchNumericalCell.queueParameters rate)
    (ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells rate rewards C_star C_h z.val) ↔ _
  rw [← Bool.eq_false_eq_not_eq_true, not_congr hcross, not_le]

/-- On the actual raw gate, the stopped support tests both actual decoder
flags and precisely the OLD overflow bit of the existing numerical machine.
The crossing and span proofs are produced from the genuine source stratum. -/
theorem actual_gate_current_mask (control0 : ContinuousLearningRows.TimeControl p) (z : Z)
    (hg : t.val + 1 ∈ actualGateSupport rate rewards C_star C_h z.val) :
    t.val + 1 ∈ actualFirstReleaseSupport rate rewards C_star C_h z.val ↔
      ReferencePrelaunchDownDecisionReadout.prelaunchPastDecoderFlag
        rate rewards C_star C_h z.val t.val (Nat.le_of_lt t.isLt) = false ∧
      ReferenceFirstLiveDecoderPastMeasurability.strictPastDecoderFlag rate rewards C_star C_h
        (physicalStart rate rewards C_star C_h z.val) t.val (Nat.le_of_lt t.isLt) z.val = false ∧
      (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate)
        ((actualLiveSourceCells rate z.val rewards C_star C_h
          (ReferenceFirstLiveNumericalPrefixTemporal.sourceStratum_facts
            rate rewards C_star C_h q t s hs z).2.1 (n + 1) (by
            have hz := ReferenceFirstLiveNumericalPrefixTemporal.sourceStratum_facts
              rate rewards C_star C_h q t s hs z
            rw [hz.2.2]
            omega)).take n)).overflow = false := by
  simp only [actualFirstReleaseSupport, Finset.mem_filter, hg, true_and,
    firstExcluded, lt_min_iff, decoder_cutoff_iff_current_false,
    actualDecoderFlag, Bool.or_eq_false_iff]
  rw [overflow_cutoff_iff rate rewards C_star C_h q t s hs control0 z hg]
  exact and_assoc

/-- The numerical mask on a genuine stratum is adapted for the pullback of
the SAME whole-source field. This is the comap identity, in its valid direction. -/
theorem strict_past_overflow_adapted_on_stratum
    (control0 : ContinuousLearningRows.TimeControl p) :
    MeasurableSet[(ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
      control0 (t.val + 1)).comap (Subtype.val : Z → Source p)]
      {z : Z | (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate)
        ((actualLiveSourceCells rate z.val rewards C_star C_h
          (ReferenceFirstLiveNumericalPrefixTemporal.sourceStratum_facts
            rate rewards C_star C_h q t s hs z).2.1 (n + 1) (by
            have hz := ReferenceFirstLiveNumericalPrefixTemporal.sourceStratum_facts
              rate rewards C_star C_h q t s hs z
            rw [hz.2.2]
            omega)).take n)).overflow = false} := by
  have hfield : (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
      control0 (t.val + 1)).comap (Subtype.val : Z → Source p) =
      (inferInstance : MeasurableSpace (Source p)).comap
        (fun z : Z => ReferenceSourceCurrentControlFreshness.c_t p control0 t z.val) := by
    have hprefix : (fun z : Z => ReferenceSourceCurrentControlFreshness.c_t p control0 t z.val) =
        ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val ∘ Subtype.val := by
      funext z
      exact ReferenceSourcePhysicalFlagConditionalLaw.c_t_eq_sourcePrefix control0 t z.val
    rw [ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration_succ,
      MeasurableSpace.comap_comp, hprefix]
  rw [hfield]
  exact ReferenceFirstLiveNumericalPrefixAdaptation.measurableSet_numericalCountRunOverflowFalse
    rate rewards C_star C_h q t s hs control0

private theorem stratum_supported_adapted (control0 : ContinuousLearningRows.TimeControl p) :
    MeasurableSet[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (t.val + 1)]
      ((Subtype.val : Z → Source p) ''
        {z : Z | t.val + 1 ∈ actualFirstReleaseSupport rate rewards C_star C_h z.val}) := by
  have hm := strict_past_overflow_adapted_on_stratum rate rewards C_star C_h q t s hs control0
  have hg := actual_gate_support_adapted rate rewards C_star C_h control0 t
  have hd := actual_decoder_flag_true_adapted rate rewards C_star C_h control0 t
  have hstratum := first_live_source_stratum_adapted rate rewards C_star C_h control0 q t s hs
  let : MeasurableSpace (Source p) :=
    ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (t.val + 1)
  have hfalse : MeasurableSet
      {z : Source p | actualDecoderFlag rate rewards C_star C_h z t.val (Nat.le_of_lt t.isLt) = false} := by
    convert hd.compl using 1
    ext z
    change (_ = false) ↔ ¬(_ = true)
    rw [Bool.eq_false_eq_not_eq_true]
  have hlocal : MeasurableSet
      {z : Z | t.val + 1 ∈ actualFirstReleaseSupport rate rewards C_star C_h z.val} := by
    have hgate := hg.preimage (measurable_subtype_coe : Measurable (Subtype.val : Z → Source p))
    have hdecoder := hfalse.preimage (measurable_subtype_coe : Measurable (Subtype.val : Z → Source p))
    have heq : {z : Z | t.val + 1 ∈ actualFirstReleaseSupport rate rewards C_star C_h z.val} =
        {z : Z | t.val + 1 ∈ actualGateSupport rate rewards C_star C_h z.val} ∩
        {z : Z | actualDecoderFlag rate rewards C_star C_h z.val t.val (Nat.le_of_lt t.isLt) = false} ∩
        {z : Z | (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate)
          ((actualLiveSourceCells rate z.val rewards C_star C_h
            (ReferenceFirstLiveNumericalPrefixTemporal.sourceStratum_facts
              rate rewards C_star C_h q t s hs z).2.1 (n + 1) (by
              have hz := ReferenceFirstLiveNumericalPrefixTemporal.sourceStratum_facts
                rate rewards C_star C_h q t s hs z
              rw [hz.2.2]
              omega)).take n)).overflow = false} := by
      ext z
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
      by_cases hgate : t.val + 1 ∈ actualGateSupport rate rewards C_star C_h z.val
      · rw [actual_gate_current_mask rate rewards C_star C_h q t s hs control0 z hgate]
        simp only [hgate, true_and, actualDecoderFlag, Bool.or_eq_false_iff, and_assoc]
      · simp only [actualFirstReleaseSupport, Finset.mem_filter, hgate, false_and]
    rw [heq]
    exact (hgate.inter hdecoder).inter hm
  exact MeasurableSet.subtype_image hstratum hlocal

end Stratum

/-- The stopped actual release support is adapted on the whole original
source. The finite launch/selected-row cover is built from actual gate facts. -/
theorem first_release_support_adapted (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) :
    MeasurableSet[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (t.val + 1)]
      {z : Source p | t.val + 1 ∈ actualFirstReleaseSupport rate rewards C_star C_h z} := by
  let strata (q : Fin (M p)) (s : Fin (t.val + 1)) :=
    ReferenceTotalSourceDisintegration.SourceStratum rate rewards C_star C_h t
      (ReferenceFirstLiveRecordingSourceCylinder.stratumIndex q t s.val (Nat.le_of_lt_succ s.isLt))
  have heq : {z : Source p | t.val + 1 ∈ actualFirstReleaseSupport rate rewards C_star C_h z} =
      ⋃ q : Fin (M p), ⋃ s : Fin (t.val + 1),
        (Subtype.val : strata q s → Source p) ''
          {z : strata q s | t.val + 1 ∈ actualFirstReleaseSupport rate rewards C_star C_h z.val} := by
    ext z
    simp only [Set.mem_iUnion, Set.mem_image, Set.mem_ofPred_eq]
    constructor
    · intro h
      have hg := (Finset.mem_filter.mp h).1
      have hz := gate_launch_facts rate rewards C_star C_h t z hg
      let q := ActualInitializationPhysicalStep.selectedRowIndex p z
      let s : Fin (t.val + 1) := ⟨physicalStart rate rewards C_star C_h z, by omega⟩
      have hstratum : z ∈ ReferenceTotalSourcePairCoupling.sourceStratumEvent rate rewards C_star C_h t
          (ReferenceFirstLiveRecordingSourceCylinder.stratumIndex q t s.val (Nat.le_of_lt_succ s.isLt)) := by
        exact ⟨ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex p z,
          hz.1, rfl⟩
      exact ⟨q, s, ⟨z, hstratum⟩, h, rfl⟩
    · rintro ⟨q, s, z', h, rfl⟩
      exact h
  rw [heq]
  exact MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun s =>
    stratum_supported_adapted rate rewards C_star C_h q t s.val (Nat.le_of_lt_succ s.isLt) control0

/-- Pending membership uses the fixed-start pending producer on each actual
launch stratum and the already proved stopped support event. -/
theorem first_release_pending_adapted (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) (i : Fin (p.m - 1)) :
    MeasurableSet[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (t.val + 1)]
      {z : Source p | i ∈ firstReleasePending rate rewards C_star C_h z t} := by
  have hsupport := first_release_support_adapted rate rewards C_star C_h control0 t
  have heq : {z : Source p | i ∈ firstReleasePending rate rewards C_star C_h z t} =
      {z : Source p | t.val + 1 ∈ actualFirstReleaseSupport rate rewards C_star C_h z} ∩
        ⋃ s : Fin (t.val + 1),
          ReferenceGeneratedDownAmbiguityMeasurability.generatedLaunchFiberSet
            (rate := rate) rewards C_star C_h s.val ∩
          {z : Source p | i ∈ ReferenceSourcePrefixHistoryFiltration.pending
            rate rewards C_star C_h s.val t z} := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_iUnion, Set.mem_ofPred_eq]
    by_cases h : t.val + 1 ∈ actualFirstReleaseSupport rate rewards C_star C_h z
    · simp only [firstReleasePending, h, ite_true, true_and]
      constructor
      · intro hi
        have hz := gate_launch_facts rate rewards C_star C_h t z (Finset.mem_filter.mp h).1
        let s : Fin (t.val + 1) := ⟨physicalStart rate rewards C_star C_h z, by omega⟩
        exact ⟨s, ⟨hz.1, rfl⟩, hi⟩
      · rintro ⟨s, hz, hi⟩
        have hstart : physicalStart rate rewards C_star C_h z = s.val := hz.2
        simpa only [hstart] using hi
    · simp only [firstReleasePending, h, ite_false, Finset.notMem_empty, false_and]
  rw [heq]
  apply hsupport.inter
  apply MeasurableSet.iUnion
  intro s
  have hs := ReferenceSourcePrefixHistoryFiltration.actualLaunchStratum_measurable
    rate rewards C_star C_h control0 t s.val (Nat.le_of_lt_succ s.isLt)
  have hp := (measurableSet_mem_finset i).preimage
    (ReferenceSourcePrefixHistoryFiltration.pending_measurable
      rate rewards C_star C_h control0 s.val t)
  exact hs.inter hp

/-- For a nonterminal date, the actual start has occurred exactly when
some supported one-based round no later than that date exists. -/
theorem first_release_sigma_le_iff (z : Source p) (v : ℕ) (hv : v ≤ p.T) :
    firstReleaseSigma rate rewards C_star C_h z ≤ v ↔
      ∃ u : Fin p.T, u.val + 1 ≤ v ∧
        u.val + 1 ∈ actualFirstReleaseSupport rate rewards C_star C_h z := by
  obtain ⟨hinterval, hlow, horder, hhigh⟩ := actual_first_release_interval rate rewards C_star C_h z
  constructor
  · intro hstart
    have hne : (actualFirstReleaseSupport rate rewards C_star C_h z).Nonempty := by
      by_contra hn
      have hempty := Finset.not_nonempty_iff_eq_empty.mp hn
      have he := (empty_first_release_endpoints rate rewards C_star C_h z hempty).1
      omega
    obtain ⟨w, hw⟩ := hne
    rw [hinterval, Finset.mem_Ico] at hw
    let u : Fin p.T := ⟨firstReleaseSigma rate rewards C_star C_h z - 1, by omega⟩
    have hu : u.val + 1 = firstReleaseSigma rate rewards C_star C_h z := by dsimp [u]; omega
    refine ⟨u, by omega, ?_⟩
    rw [hinterval, Finset.mem_Ico, hu]
    omega
  · rintro ⟨u, hu, hmem⟩
    rw [hinterval, Finset.mem_Ico] at hmem
    omega

/-- The actual first excluded endpoint has occurred exactly when an earlier
supported round exists and the current one-based date is unsupported. -/
theorem first_release_theta_le_iff (z : Source p) (v : ℕ) (hv : v ≤ p.T) :
    firstReleaseTheta rate rewards C_star C_h z ≤ v ↔
      (∃ u : Fin p.T, u.val + 1 < v ∧
        u.val + 1 ∈ actualFirstReleaseSupport rate rewards C_star C_h z) ∧
      v ∉ actualFirstReleaseSupport rate rewards C_star C_h z := by
  obtain ⟨hinterval, hlow, horder, hhigh⟩ := actual_first_release_interval rate rewards C_star C_h z
  constructor
  · intro hend
    have hne : (actualFirstReleaseSupport rate rewards C_star C_h z).Nonempty := by
      by_contra hn
      have hempty := Finset.not_nonempty_iff_eq_empty.mp hn
      have he := (empty_first_release_endpoints rate rewards C_star C_h z hempty).2
      omega
    obtain ⟨w, hw⟩ := hne
    rw [hinterval, Finset.mem_Ico] at hw
    let u : Fin p.T := ⟨firstReleaseSigma rate rewards C_star C_h z - 1, by omega⟩
    have hu : u.val + 1 = firstReleaseSigma rate rewards C_star C_h z := by dsimp [u]; omega
    constructor
    · refine ⟨u, by omega, ?_⟩
      rw [hinterval, Finset.mem_Ico, hu]
      omega
    · rw [hinterval, Finset.mem_Ico]
      omega
  · rintro ⟨⟨u, hu, hmem⟩, hnot⟩
    rw [hinterval, Finset.mem_Ico] at hmem hnot
    omega

private theorem supported_before_measurable (control0 : ContinuousLearningRows.TimeControl p)
    (v : ℕ) (strict : Bool) :
    MeasurableSet[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 v]
      {z : Source p | ∃ u : Fin p.T,
        (if strict then u.val + 1 < v else u.val + 1 ≤ v) ∧
        u.val + 1 ∈ actualFirstReleaseSupport rate rewards C_star C_h z} := by
  let : MeasurableSpace (Source p) :=
    ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 v
  have heq : {z : Source p | ∃ u : Fin p.T,
        (if strict then u.val + 1 < v else u.val + 1 ≤ v) ∧
        u.val + 1 ∈ actualFirstReleaseSupport rate rewards C_star C_h z} =
      ⋃ u : Fin p.T, if (if strict then u.val + 1 < v else u.val + 1 ≤ v) then
        {z : Source p | u.val + 1 ∈ actualFirstReleaseSupport rate rewards C_star C_h z} else ∅ := by
    ext z
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨u, hu, hm⟩
      refine ⟨u, ?_⟩
      rw [ite_eq_left hu]
      exact hm
    · rintro ⟨u, hu⟩
      by_cases h : if strict then u.val + 1 < v else u.val + 1 ≤ v
      · rw [ite_eq_left h] at hu
        exact ⟨u, h, hu⟩
      · rw [ite_eq_right h] at hu
        exact hu.elim
  rw [heq]
  apply MeasurableSet.iUnion
  intro u
  by_cases hu : if strict then u.val + 1 < v else u.val + 1 ≤ v
  · rw [ite_eq_left hu]
    have hle : u.val + 1 ≤ v := by
      cases strict with
      | false => exact hu
      | true => exact Nat.le_of_lt hu
    exact (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).mono hle _
      (first_release_support_adapted rate rewards C_star C_h control0 u)
  · rw [ite_eq_right hu]
    exact MeasurableSet.empty

/-- The endpoint module's actual start is a stopping time for the original
source-prefix filtration, including empty and terminal release phases. -/
theorem first_release_sigma_stopping (control0 : ContinuousLearningRows.TimeControl p) :
    PhaseServiceWaiting.IsPreRoundStoppingTime
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0)
      (firstReleaseSigma rate rewards C_star C_h) := by
  intro v
  by_cases hv0 : v = 0
  · subst v
    have heq : {z : Source p | firstReleaseSigma rate rewards C_star C_h z ≤ 0} = ∅ := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      have hlow := (actual_first_release_interval rate rewards C_star C_h z).2.1
      omega
    rw [heq]
    exact @MeasurableSet.empty (Source p)
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 0)
  by_cases hv : v ≤ p.T
  · have heq : {z : Source p | firstReleaseSigma rate rewards C_star C_h z ≤ v} =
        {z : Source p | ∃ u : Fin p.T, u.val + 1 ≤ v ∧
          u.val + 1 ∈ actualFirstReleaseSupport rate rewards C_star C_h z} := by
      ext z
      exact first_release_sigma_le_iff rate rewards C_star C_h z v hv
    rw [heq]
    exact supported_before_measurable rate rewards C_star C_h control0 v false
  · have heq : {z : Source p | firstReleaseSigma rate rewards C_star C_h z ≤ v} = Set.univ := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      obtain ⟨_, _, horder, hhigh⟩ := actual_first_release_interval rate rewards C_star C_h z
      omega
    rw [heq]
    exact MeasurableSet.univ

/-- The endpoint module's actual end is a stopping time. Unsupported dates
after all followers released remain governed by the actual gate interval. -/
theorem first_release_theta_stopping (control0 : ContinuousLearningRows.TimeControl p) :
    PhaseServiceWaiting.IsPreRoundStoppingTime
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0)
      (firstReleaseTheta rate rewards C_star C_h) := by
  intro v
  by_cases hv0 : v = 0
  · subst v
    have heq : {z : Source p | firstReleaseTheta rate rewards C_star C_h z ≤ 0} = ∅ := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      obtain ⟨_, hlow, horder, _⟩ := actual_first_release_interval rate rewards C_star C_h z
      omega
    rw [heq]
    exact @MeasurableSet.empty (Source p)
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 0)
  by_cases hv : v ≤ p.T
  · let current : Fin p.T := ⟨v - 1, by omega⟩
    have hcurrent : current.val + 1 = v := by dsimp [current]; omega
    have heq : {z : Source p | firstReleaseTheta rate rewards C_star C_h z ≤ v} =
        {z : Source p | ∃ u : Fin p.T, u.val + 1 < v ∧
          u.val + 1 ∈ actualFirstReleaseSupport rate rewards C_star C_h z} ∩
        {z : Source p | v ∈ actualFirstReleaseSupport rate rewards C_star C_h z}ᶜ := by
      ext z
      exact first_release_theta_le_iff rate rewards C_star C_h z v hv
    rw [heq]
    have hm := first_release_support_adapted rate rewards C_star C_h control0 current
    rw [hcurrent] at hm
    exact (supported_before_measurable rate rewards C_star C_h control0 v true).inter hm.compl
  · have heq : {z : Source p | firstReleaseTheta rate rewards C_star C_h z ≤ v} = Set.univ := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      have hhigh := (actual_first_release_interval rate rewards C_star C_h z).2.2.2
      omega
    rw [heq]
    exact MeasurableSet.univ

end Bandits.Support.ReferenceFirstLiveSourceStoppedReleaseAdaptation

end
