/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveSourceStoppedHandoverEndpoint
public import Bandits.Support.ReferenceFirstLiveHandoverBoundaryFactorization

/-!
# Strict-past stop mask on the actual first handover

The first excluded source date is tested on the original source, using both
actual decoder flags and the persistent overflow bit of the original numerical
prefix. The current update is excluded from that prefix. No release gate is
assumed. The physical run continues through the horizon.

Sources: `05_binary_transport.tex:180-240,244-281`,
`06_interruptions.tex:431-490`, `appendix_a_local_protocol.tex:100-108,141-157`,
and `04_slow_fast_learner.tex:140-188,245-290`, under `sources/zip4/manuscript/`.
These are internal source-prefix statements, not physical local-history identities.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open scoped Classical

namespace Bandits.Support.ReferenceFirstLiveHandoverNoGateStopMask

open ReferenceFirstLiveSourceStoppedReleaseEndpoint
open ReferenceFirstWindowNumericalStream

variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)

section Stratum

variable (q : Fin (M p)) (s : ℕ) (t : Fin p.T) (hs : s ≤ t.val)

local notation "Z" => ReferenceTotalSourceDisintegration.SourceStratum rate rewards C_star C_h t
  (ReferenceFirstLiveRecordingSourceCylinder.stratumIndex q t s hs)
local notation "n" => t.val - s
local notation "H" => ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0

/-- A genuine pre-acceptance section supplies its own selected-row, crossing,
and start certificates for the existing source stratum. -/
theorem E_before_mem_sourceStratum (i : Fin (p.m - 1)) (z : Source p)
    (hz : z ∈ ReferenceFirstLiveHandoverBoundaryFactorization.E_before rate rewards C_star C_h q s t i) :
    z ∈ ReferenceTotalSourcePairCoupling.sourceStratumEvent rate rewards C_star C_h t
      (ReferenceFirstLiveRecordingSourceCylinder.stratumIndex q t s hs) := by
  exact ⟨(ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex
    p z).trans hz.1, hz.2.1, hz.2.2.1⟩

/-- The accepted-but-unconfirmed section supplies the same genuine stratum;
no successful-trace or no-earlier-overflow premise is added. -/
theorem E_after_mem_sourceStratum (i : Fin (p.m - 1)) (z : Source p)
    (hz : z ∈ ReferenceFirstLiveHandoverBoundaryFactorization.E_after rate rewards C_star C_h q s t i) :
    z ∈ ReferenceTotalSourcePairCoupling.sourceStratumEvent rate rewards C_star C_h t
      (ReferenceFirstLiveRecordingSourceCylinder.stratumIndex q t s hs) := by
  exact ⟨(ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex
    p z).trans hz.1, hz.2.1, hz.2.2.1⟩

/-- Every bounded initial part of the whole window is the existing actual
window for that count. This uses the public complete-suffix identity. -/
theorem whole_window_take (z : Z) (count : ℕ) (hcount : s + count ≤ p.T) :
    (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow rate rewards C_star C_h z.val).take count =
      actualFirstLiveWindow rate z.val rewards C_star C_h
        (ReferenceFirstLiveNumericalPrefixTemporal.sourceStratum_facts rate rewards C_star C_h q t s hs z).2.1 count (by
          rw [(ReferenceFirstLiveNumericalPrefixTemporal.sourceStratum_facts rate rewards C_star C_h q t s hs z).2.2]
          exact hcount) := by
  have hz := ReferenceFirstLiveNumericalPrefixTemporal.sourceStratum_facts rate rewards C_star C_h q t s hs z
  let x : ReferenceFirstLiveOverflowReadout.LaunchFiber rate rewards C_star C_h s :=
    ⟨z.val, hz.2⟩
  have hw := ReferenceFirstLiveOverflowReadout.firstLiveWindow_eq_completeSuffix_take
    rate rewards C_star C_h s count hcount x
  change ((ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate z.val rewards C_star C_h).takeWhile
      (fun r => !ReferenceCollectionPhaseHistory.cutoffChosen r.input)).take count = _
  rw [List.take_takeWhile]
  exact hw.symm

/-- Equality of actual records identifies the whole numerical inputs, including
all reward and rate coordinates, rather than selecting an arbitrary cell. -/
theorem whole_cells_take (z : Z) (count : ℕ) (hcount : s + count ≤ p.T) :
    (ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells rate rewards C_star C_h z.val).take count =
      actualLiveSourceCells rate z.val rewards C_star C_h
        (ReferenceFirstLiveNumericalPrefixTemporal.sourceStratum_facts rate rewards C_star C_h q t s hs z).2.1 count (by
          rw [(ReferenceFirstLiveNumericalPrefixTemporal.sourceStratum_facts rate rewards C_star C_h q t s hs z).2.2]
          exact hcount) := by
  have hz := ReferenceFirstLiveNumericalPrefixTemporal.sourceStratum_facts rate rewards C_star C_h q t s hs z
  have hfull : ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z.val rewards C_star C_h rate)).completed +
      (p.T - s) ≤ p.T := by rw [hz.2.2]; omega
  have hpast : ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z.val rewards C_star C_h rate)).completed +
      count ≤ p.T := by rw [hz.2.2]; exact hcount
  let sf : Fin (p.T + 1) := ⟨s, by omega⟩
  let x : ReferenceFirstLiveOverflowReadout.LaunchFiber rate rewards C_star C_h s :=
    ⟨z.val, hz.2⟩
  have hwhole := ReferenceFirstLiveOverflowReadout.wholeFirstLive_on_fiber
    rate rewards C_star C_h sf x
  have hw := whole_window_take rate rewards C_star C_h q s t hs z count hcount
  rw [hwhole.1] at hw
  rw [hwhole.2]
  change (actualLiveSourceCells rate z.val rewards C_star C_h hz.2.1 (p.T - s) _).take count = _
  change (actualFirstLiveWindow rate z.val rewards C_star C_h hz.2.1 (p.T - s) _).take count = _ at hw
  apply List.ext_getElem
  · have h := congrArg List.length hw
    simpa only [List.length_take, actualLiveSourceCells_length] using h
  · intro j hja hjb
    have hb : j < min count (actualLiveSourceCells rate z.val rewards C_star C_h hz.2.1
        (p.T - s) hfull).length := by simpa only [List.length_take] using hja
    have hjn : j < count := lt_of_lt_of_le hb (Nat.min_le_left _ _)
    have hjA : j < (actualFirstLiveWindow rate z.val rewards C_star C_h hz.2.1
        (p.T - s) hfull).length := by
      rw [← actualLiveSourceCells_length]
      exact lt_of_lt_of_le hb (Nat.min_le_right _ _)
    have hjB : j < (actualFirstLiveWindow rate z.val rewards C_star C_h hz.2.1 count hpast).length := by
      simpa only [actualLiveSourceCells_length] using hjb
    have he := congrArg (fun records : List (ReferenceActivePhysicalHorizon.RoundRecord
      (p := p) (rate := rate)) => records[j]?) hw
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
      (actualLiveSourceCellAt rate z.val rewards C_star C_h hz.2.1 count hpast ⟨j, hjB⟩)
    simpa only [actualLiveSourceCells, List.getElem_take, List.getElem_ofFn] using hi

/-- The current actual window record has index `t-s` in the whole window.
The calendar producer is C's original physical-window theorem. -/
theorem current_in_whole_window (z : Z)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z.val = some r)
    (hw : r ∈ ReferenceFirstLiveSourceStoppedHandoverEndpoint.window rate rewards C_star C_h z.val) :
    n < ReferenceFirstLiveOverflowReadout.wholeFirstLiveLength rate rewards C_star C_h z.val := by
  have hz := ReferenceFirstLiveNumericalPrefixTemporal.sourceStratum_facts rate rewards C_star C_h q t s hs z
  have hl := ReferenceFirstLaunchNumericalCell.correctedLaunch_eq_some_launchState
    rate z.val rewards C_star C_h hz.2.1
  have hrec := ReferenceSourcePrefixHistoryFiltration.actualRecord_on_launch
    rate rewards C_star C_h t z.val _ hl (by
      change ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z.val rewards C_star C_h rate)).completed ≤ t.val
      rw [hz.2.2]
      exact hs)
  have htime : r.input.time.val = t.val := by
    have he := Option.some.inj (hr.symm.trans hrec)
    rw [he]
    dsimp only [ReferenceAssignmentPayloadChronology.actualRunRecordAt,
      ReferenceActivePhysicalHorizon.roundInputAt]
    change ReferenceCompletePhysicalHistory.physicalStart rate z.val rewards C_star C_h +
      (t.val - ReferenceCompletePhysicalHistory.physicalStart rate z.val rewards C_star C_h) = t.val
    have hstart : ReferenceCompletePhysicalHistory.physicalStart rate z.val rewards C_star C_h = s := hz.2.2
    rw [hstart]
    omega
  obtain ⟨k, hk, hkr⟩ := List.mem_iff_getElem.mp hw
  have hcal := (ReferenceFirstLiveSourceStoppedHandoverEndpoint.source_window_record_calendar rate rewards C_star C_h z.val ⟨k, hk⟩).1
  dsimp only at hcal
  rw [hkr, htime] at hcal
  have hstart : physicalStart rate rewards C_star C_h z.val = s := hz.2.2
  rw [hstart] at hcal
  change n < (ReferenceFirstLiveSourceStoppedHandoverEndpoint.window rate rewards C_star C_h z.val).length
  omega

include control0 in
/-- On an actual window record, the date cutoff is exactly the OLD persistent
overflow bit. Earlier crossings remain recorded even if physical queues drain. -/
theorem overflow_cutoff_iff_on_stratum (z : Z)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z.val = some r)
    (hw : r ∈ ReferenceFirstLiveSourceStoppedHandoverEndpoint.window rate rewards C_star C_h z.val) :
    t.val + 1 < overflowFirstExcluded rate rewards C_star C_h z.val ↔
      (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate)
        ((actualLiveSourceCells rate z.val rewards C_star C_h
          (ReferenceFirstLiveNumericalPrefixTemporal.sourceStratum_facts rate rewards C_star C_h q t s hs z).2.1 (n + 1) (by
            rw [(ReferenceFirstLiveNumericalPrefixTemporal.sourceStratum_facts rate rewards C_star C_h q t s hs z).2.2]
            omega)).take n)).overflow = false := by
  have hz := ReferenceFirstLiveNumericalPrefixTemporal.sourceStratum_facts rate rewards C_star C_h q t s hs z
  have hwindow := current_in_whole_window rate rewards C_star C_h q s t hs z r hr hw
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
  have halign := whole_cells_take rate rewards C_star C_h q s t hs z n (by have ht := t.isLt; omega)
  have hrun := ReferenceFirstLiveNumericalPrefixTemporal.numerical_run_count_eq rate rewards C_star C_h q t s hs control0 z
  rw [← halign] at hrun
  rw [hrun]
  change n < UnstoppedRecordedQueueComparison.firstOverflowPrefix
    (ReferenceFirstLaunchNumericalCell.queueParameters rate)
    (ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells rate rewards C_star C_h z.val) ↔ _
  rw [← Bool.eq_false_eq_not_eq_true, not_congr hcross, not_le]

include control0 in
/-- The no-gate mask on a genuine stratum uses both original decoder flags
and precisely the numerical prefix ending before the current update. -/
theorem cutoff_iff_on_stratum (z : Z)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z.val = some r)
    (hw : r ∈ ReferenceFirstLiveSourceStoppedHandoverEndpoint.window rate rewards C_star C_h z.val) :
    t.val + 1 < firstExcluded rate rewards C_star C_h z.val ↔
      ReferencePrelaunchDownDecisionReadout.prelaunchPastDecoderFlag
        rate rewards C_star C_h z.val t.val (Nat.le_of_lt t.isLt) = false ∧
      ReferenceFirstLiveDecoderPastMeasurability.strictPastDecoderFlag rate rewards C_star C_h
        (physicalStart rate rewards C_star C_h z.val) t.val (Nat.le_of_lt t.isLt) z.val = false ∧
      (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate)
        ((actualLiveSourceCells rate z.val rewards C_star C_h
          (ReferenceFirstLiveNumericalPrefixTemporal.sourceStratum_facts rate rewards C_star C_h q t s hs z).2.1 (n + 1) (by
            rw [(ReferenceFirstLiveNumericalPrefixTemporal.sourceStratum_facts rate rewards C_star C_h q t s hs z).2.2]
            omega)).take n)).overflow = false := by
  simp only [firstExcluded, lt_min_iff,
    ReferenceFirstLiveSourceStoppedReleaseAdaptation.decoder_cutoff_iff_current_false,
    actualDecoderFlag, Bool.or_eq_false_iff]
  rw [overflow_cutoff_iff_on_stratum rate rewards C_star C_h control0 q s t hs z r hr hw]
  exact and_assoc


include control0 in
/-- On the actual pre-acceptance section, all crossing and stratum certificates
in the literal numerical prefix are produced from section membership. -/
theorem E_before_cutoff_iff (i : Fin (p.m - 1)) (z : Source p)
    (hz : z ∈ ReferenceFirstLiveHandoverBoundaryFactorization.E_before rate rewards C_star C_h q s t i) :
    let zz : Z := ⟨z, E_before_mem_sourceStratum rate rewards C_star C_h q s t hs i z hz⟩
    t.val + 1 < firstExcluded rate rewards C_star C_h z ↔
      ReferencePrelaunchDownDecisionReadout.prelaunchPastDecoderFlag
        rate rewards C_star C_h z t.val (Nat.le_of_lt t.isLt) = false ∧
      ReferenceFirstLiveDecoderPastMeasurability.strictPastDecoderFlag rate rewards C_star C_h
        (physicalStart rate rewards C_star C_h z) t.val (Nat.le_of_lt t.isLt) z = false ∧
      (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate)
        ((actualLiveSourceCells rate z rewards C_star C_h
          (ReferenceFirstLiveNumericalPrefixTemporal.sourceStratum_facts
            rate rewards C_star C_h q t s hs zz).2.1 (n + 1) (by
            rw [(ReferenceFirstLiveNumericalPrefixTemporal.sourceStratum_facts
              rate rewards C_star C_h q t s hs zz).2.2]
            omega)).take n)).overflow = false := by
  obtain ⟨r, selected, hr, hw, _hselected, _hi, _hbefore⟩ := hz.2.2.2.2
  exact cutoff_iff_on_stratum rate rewards C_star C_h control0 q s t hs
    ⟨z, E_before_mem_sourceStratum rate rewards C_star C_h q s t hs i z hz⟩ r hr hw

include control0 in
/-- The same original-source criterion on the accepted-but-unconfirmed
section; the present round is used only to form a valid `n+1` window. -/
theorem E_after_cutoff_iff (i : Fin (p.m - 1)) (z : Source p)
    (hz : z ∈ ReferenceFirstLiveHandoverBoundaryFactorization.E_after rate rewards C_star C_h q s t i) :
    let zz : Z := ⟨z, E_after_mem_sourceStratum rate rewards C_star C_h q s t hs i z hz⟩
    t.val + 1 < firstExcluded rate rewards C_star C_h z ↔
      ReferencePrelaunchDownDecisionReadout.prelaunchPastDecoderFlag
        rate rewards C_star C_h z t.val (Nat.le_of_lt t.isLt) = false ∧
      ReferenceFirstLiveDecoderPastMeasurability.strictPastDecoderFlag rate rewards C_star C_h
        (physicalStart rate rewards C_star C_h z) t.val (Nat.le_of_lt t.isLt) z = false ∧
      (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate)
        ((actualLiveSourceCells rate z rewards C_star C_h
          (ReferenceFirstLiveNumericalPrefixTemporal.sourceStratum_facts
            rate rewards C_star C_h q t s hs zz).2.1 (n + 1) (by
            rw [(ReferenceFirstLiveNumericalPrefixTemporal.sourceStratum_facts
              rate rewards C_star C_h q t s hs zz).2.2]
            omega)).take n)).overflow = false := by
  obtain ⟨r, selected, hr, hw, _hselected, _hi, _hafter⟩ := hz.2.2.2.2
  exact cutoff_iff_on_stratum rate rewards C_star C_h control0 q s t hs
    ⟨z, E_after_mem_sourceStratum rate rewards C_star C_h q s t hs i z hz⟩ r hr hw

private theorem measurableSet_stopped_section (E : Set (Source p))
    (hE : MeasurableSet[H (t.val + 1)] E)
    (hstratum : ∀ z ∈ E,
      z ∈ ReferenceTotalSourcePairCoupling.sourceStratumEvent rate rewards C_star C_h t
        (ReferenceFirstLiveRecordingSourceCylinder.stratumIndex q t s hs))
    (hwindow : ∀ z ∈ E, ∃ r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate),
      ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some r ∧
        r ∈ ReferenceFirstLiveSourceStoppedHandoverEndpoint.window rate rewards C_star C_h z) :
    MeasurableSet[H (t.val + 1)]
      {z : Source p | z ∈ E ∧ t.val + 1 < firstExcluded rate rewards C_star C_h z} := by
  have hm := ReferenceFirstLiveSourceStoppedReleaseAdaptation.strict_past_overflow_adapted_on_stratum
    rate rewards C_star C_h q t s hs control0
  have hd := actual_decoder_flag_true_adapted rate rewards C_star C_h control0 t
  have hS := first_live_source_stratum_adapted rate rewards C_star C_h control0 q t s hs
  let : MeasurableSpace (Source p) := H (t.val + 1)
  have hfalse : MeasurableSet
      {z : Source p | actualDecoderFlag rate rewards C_star C_h z t.val (Nat.le_of_lt t.isLt) = false} := by
    convert hd.compl using 1
    ext z
    change (_ = false) ↔ ¬(_ = true)
    rw [Bool.eq_false_eq_not_eq_true]
  have hlocal : MeasurableSet
      {z : Z | z.val ∈ E ∧ t.val + 1 < firstExcluded rate rewards C_star C_h z.val} := by
    have hEsub := hE.preimage (measurable_subtype_coe : Measurable (Subtype.val : Z → Source p))
    have hdsub := hfalse.preimage (measurable_subtype_coe : Measurable (Subtype.val : Z → Source p))
    have heq : {z : Z | z.val ∈ E ∧ t.val + 1 < firstExcluded rate rewards C_star C_h z.val} =
        {z : Z | z.val ∈ E} ∩
        {z : Z | actualDecoderFlag rate rewards C_star C_h z.val t.val (Nat.le_of_lt t.isLt) = false} ∩
        {z : Z | (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate)
          ((actualLiveSourceCells rate z.val rewards C_star C_h
            (ReferenceFirstLiveNumericalPrefixTemporal.sourceStratum_facts
              rate rewards C_star C_h q t s hs z).2.1 (n + 1) (by
              rw [(ReferenceFirstLiveNumericalPrefixTemporal.sourceStratum_facts
                rate rewards C_star C_h q t s hs z).2.2]
              omega)).take n)).overflow = false} := by
      ext z
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
      by_cases he : z.val ∈ E
      · obtain ⟨r, hr, hw⟩ := hwindow z.val he
        rw [cutoff_iff_on_stratum rate rewards C_star C_h control0 q s t hs z r hr hw]
        simp only [he, true_and, actualDecoderFlag, Bool.or_eq_false_iff, and_assoc]
      · simp only [he, false_and]
    rw [heq]
    exact (hEsub.inter hdsub).inter hm
  have himage := MeasurableSet.subtype_image hS hlocal
  convert himage using 1
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_image]
  constructor
  · intro hz
    exact ⟨⟨z, hstratum z hz.1⟩, hz, rfl⟩
  · rintro ⟨zz, hz, rfl⟩
    exact hz

include hs in
/-- The literal stopped pre-acceptance section is measurable in the original
whole-source strict-past field. No stopped-section adaptation is assumed. -/
theorem measurableSet_E_before_stopped (i : Fin (p.m - 1)) :
    MeasurableSet[H (t.val + 1)]
      {z : Source p | z ∈ ReferenceFirstLiveHandoverBoundaryFactorization.E_before
        rate rewards C_star C_h q s t i ∧ t.val + 1 < firstExcluded rate rewards C_star C_h z} := by
  apply measurableSet_stopped_section rate rewards C_star C_h control0 q s t hs
    (ReferenceFirstLiveHandoverBoundaryFactorization.E_before rate rewards C_star C_h q s t i)
    (ReferenceFirstLiveHandoverBoundaryFactorization.measurableSet_E_before
      rate rewards C_star C_h control0 q s t hs i)
    (fun z hz => E_before_mem_sourceStratum rate rewards C_star C_h q s t hs i z hz)
  intro z hz
  obtain ⟨r, selected, hr, hw, _hselected, _hi, _hbefore⟩ := hz.2.2.2.2
  exact ⟨r, hr, hw⟩

include hs in
/-- The literal stopped accepted-but-unconfirmed section has the same whole
source adaptation, with every subtype/comap/image transport discharged. -/
theorem measurableSet_E_after_stopped (i : Fin (p.m - 1)) :
    MeasurableSet[H (t.val + 1)]
      {z : Source p | z ∈ ReferenceFirstLiveHandoverBoundaryFactorization.E_after
        rate rewards C_star C_h q s t i ∧ t.val + 1 < firstExcluded rate rewards C_star C_h z} := by
  apply measurableSet_stopped_section rate rewards C_star C_h control0 q s t hs
    (ReferenceFirstLiveHandoverBoundaryFactorization.E_after rate rewards C_star C_h q s t i)
    (ReferenceFirstLiveHandoverBoundaryFactorization.measurableSet_E_after
      rate rewards C_star C_h control0 q s t hs i)
    (fun z hz => E_after_mem_sourceStratum rate rewards C_star C_h q s t hs i z hz)
  intro z hz
  obtain ⟨r, selected, hr, hw, _hselected, _hi, _hafter⟩ := hz.2.2.2.2
  exact ⟨r, hr, hw⟩

end Stratum


/-- Finite selected-row/start transport of the literal stopped pre-acceptance
sections, on the entire original source including all absent-launch branches. -/
theorem measurableSet_E_before_stopped_union (t : Fin p.T) (i : Fin (p.m - 1)) :
    MeasurableSet[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (t.val + 1)]
      {z : Source p | (∃ q : Fin (M p), ∃ s : Fin (t.val + 1),
        z ∈ ReferenceFirstLiveHandoverBoundaryFactorization.E_before
          rate rewards C_star C_h q s.val t i) ∧
        t.val + 1 < firstExcluded rate rewards C_star C_h z} := by
  have hm := MeasurableSet.iUnion fun q : Fin (M p) =>
    MeasurableSet.iUnion fun s : Fin (t.val + 1) =>
      measurableSet_E_before_stopped rate rewards C_star C_h control0 q s.val t
        (Nat.le_of_lt_succ s.isLt) i
  convert hm using 1
  ext z
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨q, s, he⟩, hstop⟩
    exact ⟨q, s, he, hstop⟩
  · rintro ⟨q, s, he, hstop⟩
    exact ⟨⟨q, s, he⟩, hstop⟩

/-- The corresponding finite transport for accepted-but-unconfirmed sections.
The union retains the original private selected row and elapsed start. -/
theorem measurableSet_E_after_stopped_union (t : Fin p.T) (i : Fin (p.m - 1)) :
    MeasurableSet[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (t.val + 1)]
      {z : Source p | (∃ q : Fin (M p), ∃ s : Fin (t.val + 1),
        z ∈ ReferenceFirstLiveHandoverBoundaryFactorization.E_after
          rate rewards C_star C_h q s.val t i) ∧
        t.val + 1 < firstExcluded rate rewards C_star C_h z} := by
  have hm := MeasurableSet.iUnion fun q : Fin (M p) =>
    MeasurableSet.iUnion fun s : Fin (t.val + 1) =>
      measurableSet_E_after_stopped rate rewards C_star C_h control0 q s.val t
        (Nat.le_of_lt_succ s.isLt) i
  convert hm using 1
  ext z
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨q, s, he⟩, hstop⟩
    exact ⟨q, s, he, hstop⟩
  · rintro ⟨q, s, he, hstop⟩
    exact ⟨⟨q, s, he⟩, hstop⟩

end Bandits.Support.ReferenceFirstLiveHandoverNoGateStopMask

end
