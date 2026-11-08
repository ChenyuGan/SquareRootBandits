/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceOriginalInstallationHandoverFreshService
public import Bandits.Support.ReferenceFirstLiveHandoverPhysicalQuota

import Mathlib.Tactic

/-!
# Initial original-handover incoming quota

This module transports the literal initial fixed-installation pending event to
its actual first-live source endpoint and physical service count.

Sources: ZIP4 `05_binary_transport.tex:244-289`,
`06_interruptions.tex:431-490,523-533`, and
`appendix_a_local_protocol.tex:28-64`.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceOriginalFixedInstallationHandoverSupport
open Bandits.Support.ReferenceOriginalInstallationHandoverFreshService
open Bandits.Support.ReferenceFirstLiveHandoverPhysicalQuota
open scoped BigOperators Classical

namespace Bandits.Support.ReferenceOriginalInitialHandoverIncomingQuota

variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ)

local notation "Source" => BootstrapPrivateRoundStreams.SourceInput p

private theorem initial_rawPending_window_index
    (ell t : Fin p.T) (i : Fin (p.m - 1)) (z : Source)
    (hinitial : initialBirthAt rate rewards C_star C_h ell z)
    (hraw : rawPending rate rewards C_star C_h ell t i z) :
    ∃ k : Fin (ReferenceFirstLiveSourceStoppedHandoverEndpoint.window
        rate rewards C_star C_h z).length,
      ((ReferenceFirstLiveSourceStoppedHandoverEndpoint.window
        rate rewards C_star C_h z).get k).input.time = t := by
  rcases hraw with hfirst | hlater
  · obtain ⟨_, _, _, _, _, k, _, ht, _⟩ := hfirst
    exact ⟨k, ht⟩
  · obtain ⟨b, hb, ht, hr, payload, ledger, saved, hc, he, installed, hi, _⟩ := hlater
    exact (initialBirthAt_not_laterBirthAt rate rewards C_star C_h ell z hinitial
      ⟨b, hb, ht, hr, payload, ledger, saved, hc, he, installed, hi⟩).elim

private theorem crossing_of_window_index
    (z : Source)
    (k : Fin (ReferenceFirstLiveSourceStoppedHandoverEndpoint.window
      rate rewards C_star C_h z).length) :
    (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)
      ).crossing.isSome = true := by
  cases hl : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate z rewards C_star C_h with
  | none =>
    have he := ReferenceFirstLiveSourceStoppedHandoverEndpoint.window_eq_nil_of_no_launch
      rate rewards C_star C_h z hl
    rw [he] at k
    exact Fin.elim0 k
  | some active =>
    exact (ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
      rate z rewards C_star C_h).mp (by rw [hl]; rfl)

private theorem window_ambiguity_source
    (z : Source)
    (k : Fin (ReferenceFirstLiveSourceStoppedHandoverEndpoint.window
      rate rewards C_star C_h z).length) (i : Fin (p.m - 1))
    (hamb : ReferenceFirstLiveDownCompletionReadout.completedAmbiguousAfterStart
      (ReferenceFirstLiveSourceStoppedReleaseEndpoint.physicalStart rate rewards C_star C_h z)
      ((ReferenceFirstLiveSourceStoppedHandoverEndpoint.window
        rate rewards C_star C_h z).get k) i) :
    ReferenceCompleteAwaitedBatchSourceCoverage.sourceDownFixedAwaitedCompletionAt
      rate rewards C_star C_h z
      ((ReferenceFirstLiveSourceStoppedHandoverEndpoint.window
        rate rewards C_star C_h z).get k).input.time := by
  classical
  let W := ReferenceFirstLiveSourceStoppedHandoverEndpoint.window rate rewards C_star C_h z
  let r := W.get k
  let start := ReferenceInitializationRun.elapsed p
    (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed
  change ReferenceCompleteAwaitedBatchSourceCoverage.sourceDownFixedAwaitedCompletionAt
    rate rewards C_star C_h z r.input.time
  have hc := crossing_of_window_index rate rewards C_star C_h z k
  have hspan : start + (p.T - start) ≤ p.T := by
    have hs := ReferenceInitializationRun.elapsed_le_T p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed
    dsimp only [start]
    omega
  let R := ReferenceLocalReleaseGateChronology.sourceRun rate z rewards C_star C_h hc
    start (p.T - start) rfl hspan
  have hR : R.records = ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h := by
    exact (ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
      rate z rewards C_star C_h _
      (ReferenceLocalReleaseGateChronology.sourceSeed_launch rate z rewards C_star C_h hc)).symm
  have hW : ReferenceFirstLiveConfirmationHistory.firstLiveWindow R.records = W := by
    change ReferenceFirstLiveConfirmationHistory.firstLiveWindow R.records =
      ReferenceFirstLiveConfirmationHistory.firstLiveWindow _
    rw [hR]
    rfl
  let j : Fin (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R.records).length :=
    ⟨k.val, by rw [hW]; exact k.isLt⟩
  have hr : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R.records)[j.val] = r := by
    simp only [j, hW, r, List.get_eq_getElem]
  have hamb' : ReferenceFirstLiveDownCompletionReadout.completedAmbiguousAfterStart start
      ((ReferenceFirstLiveConfirmationHistory.firstLiveWindow R.records)[j.val]) i := by
    rw [hr]
    exact hamb
  obtain ⟨M, _birth, B, _hMs, _hbirth, _hbt, _hborn, _hfirst,
      hB, horig, _hsolves, hmulti, hcalls⟩ :=
    (ReferenceFirstLiveDownCompletionReadout.actual_first_live_completedAmbiguousAfterStart_iff
      rate z rewards C_star C_h (p.T - start) hc hspan j i).mp hamb'
  rw [hr] at hB
  have htake : R.records.take (k.val + 1) = W.take (k.val + 1) := by
    have hp : W.IsPrefix R.records := by
      rw [← hW]
      exact List.takeWhile_prefix _
    obtain ⟨tail, he⟩ := hp
    rw [← he, List.take_append_of_le_length (Nat.succ_le_of_lt k.isLt)]
  have htime := (ReferenceFirstLiveSourceStoppedHandoverEndpoint.source_window_record_calendar
    rate rewards C_star C_h z k).1
  change r.input.time.val = start + k.val at htime
  have hlookup : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h r.input.time z = some r :=
    (ReferenceFirstLiveSourceStoppedHandoverEndpoint.source_window_record_calendar
      rate rewards C_star C_h z k).2
  have hprefix (q : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
      (hq : q ∈ R.records.take (k.val + 1)) :
      start ≤ q.input.time.val ∧ q.input.time.val ≤ r.input.time.val ∧
      ReferenceSourcePrefixHistoryFiltration.actualRecord
        rate rewards C_star C_h q.input.time z = some q := by
    rw [htake] at hq
    obtain ⟨a, ha, hqa⟩ := List.mem_take_iff_getElem.mp hq
    have haW : a < W.length := by omega
    have hcal := ReferenceFirstLiveSourceStoppedHandoverEndpoint.source_window_record_calendar
      rate rewards C_star C_h z ⟨a, haW⟩
    have heq : W[a] = q := hqa
    have hval : q.input.time.val = start + a := by
      have ht := hcal.1
      change (W.get ⟨a, haW⟩).input.time.val = start + a at ht
      simpa only [List.get_eq_getElem, heq] using ht
    refine ⟨by omega, by omega, ?_⟩
    simpa only [W, List.get_eq_getElem, heq] using hcal.2
  let word := CoordinatorLocalArmChoice.storedDownFlatWord M i
  let a : Fin p.T := ⟨start, by have ht := r.input.time.isLt; omega⟩
  refine ⟨i, word, B, a, ?_, ?_, hmulti, ?_, ?_⟩
  · simp only [ReferenceCompleteAwaitedBatchSourceCoverage.sourceDownCompletedAt, hlookup]
    exact (ReferenceLiteralAwaitedAmbiguityRowObservation.physicalDownCompletedAt_iff_completedDownBatch
      rate r i B).mpr hB
  · change start ≤ r.input.time.val
    omega
  · intro e he
    have hepos : e ∈ ReferenceFollowerDownDecoderReplay.actualDownPositives i
        (R.records.take (k.val + 1)) := horig e he
    simp only [ReferenceFollowerDownDecoderReplay.actualDownPositives,
      ReferenceFollowerDownDecoderReplay.positiveCallEntries,
      ReferenceFollowerDownDecoderReplay.actualDownCalls,
      List.mem_flatMap, List.mem_filterMap] at hepos
    obtain ⟨call, ⟨q, hq, hcall⟩, hecall⟩ := hepos
    have hentry : e.time = call.1 := by
      unfold AffineBatchDecoder.positiveAt at hecall
      split at hecall
      · exact congrArg AffineBatchDecoder.Entry.time (List.mem_singleton.mp hecall)
      · cases hecall
    have hcfields := ReferenceDownCompletedAmbiguityMeasurability.actualDownCall_fields q i call hcall
    have hstamp : e.time = q.input.time := hentry.trans hcfields.1
    obtain ⟨hlo, hhi, hqlookup⟩ := hprefix q hq
    have hdown : ActiveFollowerDownAcceptance.downSelected p i q.input.row q.input.time := by
      have hel : AffineBatchDecoder.eligible call.2 := by
        by_contra hn
        simp only [AffineBatchDecoder.positiveAt, ActiveFollowerDownAcceptance.currentInputExtension,
          hn, ite_false, List.not_mem_nil] at hecall
      exact hcfields.2.2.mp hel.1
    obtain ⟨logged, cut, _hl, _hd, _hc, _hw, hsent, _hacc, _hpos⟩ := hcalls q hq hdown
    refine ⟨?_, ?_, ?_⟩
    · change start ≤ e.time.val
      rw [hstamp]
      exact hlo
    · rw [hstamp]
      exact hhi
    · rw [hstamp]
      simp only [ReferenceCompleteAwaitedBatchSourceCoverage.sourceDownSentAt, hqlookup]
      exact hsent
  · intro v hav hvt hchannel
    change start ≤ v.val at hav
    change v.val ≤ r.input.time.val at hvt
    have hkW : k.val < W.length := k.isLt
    let l : Fin W.length := ⟨v.val - start, by have hk := k.isLt; omega⟩
    let q := W.get l
    have hvq : q.input.time = v := by
      apply Fin.ext
      have hcal := (ReferenceFirstLiveSourceStoppedHandoverEndpoint.source_window_record_calendar
        rate rewards C_star C_h z l).1
      change q.input.time.val = start + l.val at hcal
      dsimp only [l] at hcal
      omega
    have hqmem : q ∈ R.records.take (k.val + 1) := by
      rw [htake]
      apply List.mem_take_iff_getElem.mpr
      exact ⟨l.val, by dsimp only [l]; omega, by simp only [q, List.get_eq_getElem]⟩
    have hqlookup := (hprefix q hqmem).2.2
    rw [hvq] at hqlookup
    have hselected : ActiveFollowerDownAcceptance.downSelected p i q.input.row q.input.time := by
      rw [hvq]
      obtain ⟨hrows, hJ, _, _⟩ := ReferenceCalendarLaterSamplerOutputSections.actualRecord_fields
        rate rewards C_star C_h v z q hqlookup
      have hrow' : q.input.row = z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) := by
        simp only [ReferenceActivePhysicalStep.RoundInput.row, hrows, hJ]
      rw [hrow']
      have hd : PublicDiscreteDraws.slotDraw
          ((z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)).2 v).1 =
          PublicDiscreteDraws.downSlot := by
        unfold ReferenceSelectedAffinePairLaw.selectedChannel
          ReferenceSelectedAffinePairLaw.channelFromDraws at hchannel
        split at hchannel
        · assumption
        · split at hchannel
          · have he := congrArg Prod.fst (Option.some.inj hchannel)
            cases he
          · cases hchannel
      rw [ReferenceSelectedAffinePairLaw.selectedChannel_of_down p _ hd] at hchannel
      exact ⟨hd, (Prod.mk.inj (Option.some.inj hchannel)).2⟩
    obtain ⟨logged, cut, hl, hd, hc, hw, _hsent, hacc, _hpos⟩ := hcalls q hqmem hselected
    have haw : ReferenceFirstCollectionAwaitedDownFailureReadout.awaitedDownAt rate q i word :=
      ⟨logged, cut, hl, hd, hc, hw, hacc⟩
    have hphysical := ReferenceLiteralSourceDecoderCoverage.physicalAwaitedDownAt_of_awaitedDownAt
      q i word haw
    simp only [ReferenceCompleteAwaitedBatchSourceCoverage.sourceDownAwaitedAt, hqlookup]
    exact hphysical

private theorem window_decoder_cutoff_of_firstBad
    (z : Source)
    (k : Fin (ReferenceFirstLiveSourceStoppedHandoverEndpoint.window
      rate rewards C_star C_h z).length)
    (hbad : ((ReferenceFirstLiveSourceStoppedHandoverEndpoint.window
      rate rewards C_star C_h z).get k).input.time.val + 1 ≤
      ReferenceCompleteSignedFirstBadCalendar.firstBadDate rate rewards C_star C_h z) :
    ((ReferenceFirstLiveSourceStoppedHandoverEndpoint.window
      rate rewards C_star C_h z).get k).input.time.val + 1 <
      ReferenceFirstLiveSourceStoppedReleaseEndpoint.decoderFirstExcluded
        rate rewards C_star C_h z := by
  classical
  let W := ReferenceFirstLiveSourceStoppedHandoverEndpoint.window rate rewards C_star C_h z
  let t := (W.get k).input.time
  have htime := (ReferenceFirstLiveSourceStoppedHandoverEndpoint.source_window_record_calendar
    rate rewards C_star C_h z k).1
  have hno (q : Fin p.T) (hqt : q.val < t.val) :
      ¬ ReferenceCompleteSignedFirstBadCalendar.sourceBadAt rate rewards C_star C_h z q := by
    apply ReferenceCompleteSignedFirstBadCalendar.sourceBadAt_false_before_firstBadDate
      rate rewards C_star C_h z q
    change t.val + 1 ≤ _ at hbad
    omega
  have hgate (q : Fin p.T) (hqt : q.val < t.val) :=
    ReferenceCompleteSignedFirstBadCalendar.inclusive_gate_through_first_bad_date
      rate rewards C_star C_h z q (by change t.val + 1 ≤ _ at hbad; omega)
  apply (ReferenceFirstLiveSourceStoppedReleaseEndpoint.decoder_cutoff_after_current_iff
    rate rewards C_star C_h t z).mpr
  intro n
  have hn : n.val ≤ t.val := Nat.le_of_lt_succ n.isLt
  have hpre : ReferencePrelaunchDownDecisionReadout.prelaunchPastDecoderFlag
      rate rewards C_star C_h z n.val (by omega) = false := by
    apply Bool.eq_false_of_not_eq_true
    intro hp
    rw [ReferencePrelaunchDownDecisionReadout.prelaunchPastDecoderFlag, decide_eq_true_eq] at hp
    obtain ⟨j, i, hi⟩ := hp
    let q : Fin p.T := Fin.castLE (show n.val ≤ p.T by omega) j
    have hqt : q.val < t.val := by change j.val < t.val; have hj := j.isLt; omega
    apply hno q hqt
    left
    exact ⟨hgate q hqt,
      (ReferenceCompleteOrdinaryWrongCompletionCharacterization.ordinaryWrongCompletionAt_iff
        rate rewards C_star C_h q z).mpr (Or.inl ⟨i, hi⟩) |> Or.inl⟩
  have hpost : ReferenceFirstLiveDecoderPastMeasurability.strictPastDecoderFlag
      rate rewards C_star C_h
      (ReferenceFirstLiveSourceStoppedReleaseEndpoint.physicalStart rate rewards C_star C_h z)
      n.val (by omega) z = false := by
    apply (ReferenceFirstLiveDecoderPastMeasurability.strictPastDecoderFlag_eq_false_iff
      rate rewards C_star C_h _ n.val (by omega) z).mpr
    intro j r hr
    let q : Fin p.T := Fin.castLE (show n.val ≤ p.T by omega) j
    have hqt : q.val < t.val := by change j.val < t.val; have hj := j.isLt; omega
    apply Bool.eq_false_of_not_eq_true
    intro hf
    rcases (ReferenceFirstLiveDecoderPastMeasurability.retainedDecoderRecordFlag_eq_true_iff
      _ r).mp hf with hsaved | ⟨i, hamb⟩
    · apply hno q hqt
      left
      exact ⟨hgate q hqt, Or.inl
        ((ReferenceCompleteOrdinaryWrongCompletionCharacterization.ordinaryWrongCompletionAt_iff
          rate rewards C_star C_h q z).mpr (Or.inr ⟨r, hr, hsaved⟩))⟩
    · have hs : ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h ≤ q.val := by
        by_contra hnot
        have habsent := ReferenceSourcePrefixHistoryFiltration.actualRecord_eq_none_of_future_start
          rate rewards C_star C_h q z (by omega)
        rw [habsent] at hr
        cases hr
      let l : Fin W.length := ⟨q.val - ReferenceCompletePhysicalHistory.physicalStart
        rate z rewards C_star C_h, by
          have hk : k.val < W.length := k.isLt
          change t.val = ReferenceCompletePhysicalHistory.physicalStart
            rate z rewards C_star C_h + k.val at htime
          omega⟩
      have hlTime : (W.get l).input.time = q := by
        apply Fin.ext
        have hl := (ReferenceFirstLiveSourceStoppedHandoverEndpoint.source_window_record_calendar
          rate rewards C_star C_h z l).1
        change (W.get l).input.time.val = ReferenceCompletePhysicalHistory.physicalStart
          rate z rewards C_star C_h + l.val at hl
        have hlval : l.val = q.val - ReferenceCompletePhysicalHistory.physicalStart
          rate z rewards C_star C_h := rfl
        omega
      have hlLookup := (ReferenceFirstLiveSourceStoppedHandoverEndpoint.source_window_record_calendar
        rate rewards C_star C_h z l).2
      change ReferenceSourcePrefixHistoryFiltration.actualRecord
        rate rewards C_star C_h (W.get l).input.time z = some (W.get l) at hlLookup
      rw [hlTime] at hlLookup
      have he : r = W.get l := Option.some.inj (hr.symm.trans hlLookup)
      subst r
      have hsource := window_ambiguity_source rate rewards C_star C_h z l i hamb
      rw [hlTime] at hsource
      apply hno q hqt
      exact Or.inl ⟨hgate q hqt, Or.inr (Or.inl hsource)⟩
  exact Bool.or_eq_false_iff.mpr ⟨hpre, hpost⟩

private theorem first_live_prefix_inputs
    (z : Source)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)
      ).crossing.isSome = true) :
    (ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells rate rewards C_star C_h z).length =
      ReferenceFirstLiveOverflowReadout.wholeFirstLiveLength rate rewards C_star C_h z ∧
    ∀ h : ℕ, h ≤ ReferenceFirstLiveOverflowReadout.wholeFirstLiveLength
        rate rewards C_star C_h z →
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
        rate rewards C_star C_h
        (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + h) z =
      some ((ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells
        rate rewards C_star C_h z).take h) := by
  classical
  let count := p.T - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  let span := ReferenceCompleteFirstPhaseObservationRecovery.firstPhaseSpan
    rate rewards C_star C_h z
  let W := ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
    rate z rewards C_star C_h hc count span
  let cells := ReferenceFirstWindowNumericalStream.actualLiveSourceCells
    rate z rewards C_star C_h hc count span
  have hW : W = ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
      rate rewards C_star C_h z := by
    dsimp only [W, ReferenceFirstWindowNumericalStream.actualFirstLiveWindow,
      ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow]
    rw [ReferenceCompleteFirstPhaseObservationRecovery.completeSuffixRecords_eq_actualFirstLiveRun
      rate rewards C_star C_h z hc]
  have hcells : ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells
      rate rewards C_star C_h z = cells := by
    unfold ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells
    split
    · rfl
    · rename_i hn
      exact (hn hc).elim
  have hlen : cells.length = W.length :=
    ReferenceFirstWindowNumericalStream.actualLiveSourceCells_length
      rate z rewards C_star C_h hc count span
  obtain ⟨_seed, _hpos, hrecords⟩ :=
    ReferenceCompleteFirstPhaseObservationRecovery.actualFirstLiveRawObservationIdentity
      rate rewards C_star C_h z hc
  have hmap : W.map (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate) = cells.map some := by
    apply List.ext_getElem
    · simp only [List.length_map, hlen]
    · intro j hj _
      have hjW : j < W.length := by simpa only [List.length_map] using hj
      have hfact := hrecords ⟨j, hjW⟩
      obtain ⟨_, _, _, _, _, _, hread, _⟩ := hfact
      simp only [List.getElem_map]
      change ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 W[j] = some cells[j] at hread
      unfold ReferenceFirstCollectionCurrentRetainedGate.cell0
      rw [hread]
      rfl
  refine ⟨?_, ?_⟩
  · rw [hcells, hlen, hW]
    rfl
  · intro h hh
    have hhW : h ≤ W.length := by
      change h ≤ (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
        rate rewards C_star C_h z).length at hh
      rw [hW]
      exact hh
    have htake : (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h).take h = W.take h := by
      have hp : W.IsPrefix (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h) := by
        rw [hW]
        exact List.takeWhile_prefix _
      obtain ⟨tail, he⟩ := hp
      rw [← he, List.take_append_of_le_length hhW]
    have hby : ReferenceSourcePrefixHistoryFiltration.actualLaunchBy rate rewards C_star C_h
        (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + h) z :=
      ⟨hc, Nat.le_add_right _ _⟩
    unfold ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
    rw [ite_eq_left hby]
    change (((ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).take
        (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + h -
          ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)).map
        (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate)).mapM id = _
    rw [Nat.add_sub_cancel_left, htake, List.map_take, hmap, ← List.map_take, hcells]
    simp only [List.mapM_map, Function.comp_def, id_eq]
    generalize cells.take h = xs
    induction xs with
    | nil => rfl
    | cons x xs ih =>
      simp only [List.mapM_cons, ih]
      rfl

private theorem window_overflow_cutoff_of_firstBad
    (z : Source)
    (k : Fin (ReferenceFirstLiveSourceStoppedHandoverEndpoint.window
      rate rewards C_star C_h z).length)
    (hbad : ((ReferenceFirstLiveSourceStoppedHandoverEndpoint.window
      rate rewards C_star C_h z).get k).input.time.val + 1 ≤
      ReferenceCompleteSignedFirstBadCalendar.firstBadDate rate rewards C_star C_h z) :
    ((ReferenceFirstLiveSourceStoppedHandoverEndpoint.window
      rate rewards C_star C_h z).get k).input.time.val + 1 <
      ReferenceFirstLiveSourceStoppedReleaseEndpoint.overflowFirstExcluded
        rate rewards C_star C_h z := by
  classical
  let t := ((ReferenceFirstLiveSourceStoppedHandoverEndpoint.window
    rate rewards C_star C_h z).get k).input.time
  have hgate := ReferenceCompleteSignedFirstBadCalendar.inclusive_gate_through_first_bad_date
    rate rewards C_star C_h z t hbad
  have hsafe := (ReferenceCompleteInclusivePhysicalDecoderErrors.actualInclusivePhysicalScanGate_iff_noNumericalOverflowThrough
    rate rewards C_star C_h z t).mp hgate
  have hno := (ReferenceCompleteInclusivePhysicalDecoderErrors.noNumericalOverflowThrough_iff_not_numericalOverflowBy
    rate rewards C_star C_h t z).mp hsafe
  have hc := crossing_of_window_index rate rewards C_star C_h z k
  obtain ⟨hlen, hpref⟩ := first_live_prefix_inputs rate rewards C_star C_h z hc
  cases hover : ReferenceFirstLiveOverflowReadout.wholeFirstLiveOverflowRound
      rate rewards C_star C_h z with
  | none =>
    change t.val + 1 < _
    simp only [ReferenceFirstLiveSourceStoppedReleaseEndpoint.overflowFirstExcluded,
      hover, Option.elim_none]
    exact Nat.succ_lt_succ t.isLt
  | some v =>
    have hdet := hover
    unfold ReferenceFirstLiveOverflowReadout.wholeFirstLiveOverflowRound at hdet
    split at hdet
    next hcross =>
      have hv := Option.some.inj hdet
      let cells := ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells rate rewards C_star C_h z
      let Q := ReferenceFirstLaunchNumericalCell.queueParameters rate
      let H := UnstoppedRecordedQueueComparison.firstOverflowPrefix Q cells
      have hHlen : H ≤ cells.length := by
        rw [hlen]
        exact hcross
      have hHpos := UnstoppedRecordedQueueComparison.first_overflow_prefix_pos Q cells
      have hcrossing := UnstoppedRecordedQueueComparison.replay_crosses_overflow_at_first Q cells hHlen
      have hnorm := (UnstoppedRecordedQueueComparison.replay_crosses_overflow_iff_normalized
        Q cells H).mp hcrossing
      have hcurrent : t.val < v := by
        by_contra hn
        have hle : v ≤ t.val := Nat.le_of_not_gt hn
        have hinputs := hpref H hcross
        have hv' : ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + H = v := hv
        rw [hv'] at hinputs
        have hread : ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout
            rate rewards C_star C_h v z = some
              (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
                (RecordedQueueRun.run Q (cells.take H))) := by
          simp only [ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout,
            hinputs, Option.map_some]
          rfl
        obtain ⟨arm, harm⟩ := hnorm
        have hregs := (UnstoppedRecordedQueueComparison.prefix_state_comparison Q cells H hHlen).1 arm
        change (RecordedQueueRun.run Q (cells.take H)).registers arm = _ at hregs
        rw [Nat.min_self] at hregs
        apply hno
        refine ⟨v, hle, _, hread, arm, ?_⟩
        change ((RecordedQueueRun.run Q (cells.take H)).registers arm).2 / (Q.n : ℝ) > _
        rw [hregs]
        exact harm
      change t.val + 1 < _
      simp only [ReferenceFirstLiveSourceStoppedReleaseEndpoint.overflowFirstExcluded,
        hover, Option.elim_some, lt_min_iff]
      exact ⟨Nat.succ_lt_succ t.isLt, Nat.succ_lt_succ hcurrent⟩
    next hnone => cases hdet

/-- A positive literal fixed-installation service on the initial branch is
an actual physical DOWN service on the same incoming source record. -/
theorem initial_service_physical
    (ell t : Fin p.T) (i : Fin (p.m - 1)) (z : Source)
    (hinitial : initialBirthAt rate rewards C_star C_h ell z)
    (hservice : X_before rate rewards C_star C_h ell t i z +
      X_after rate rewards C_star C_h ell t i z = 1) :
    ∃ r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate),
      ReferenceSourcePrefixHistoryFiltration.actualRecord
        rate rewards C_star C_h t z = some r ∧
      (beforeDownService rate i r ∨ afterDownService rate i r) := by
  classical
  have hevent :
      (before rate rewards C_star C_h ell t i z ∧
        ReferenceFirstLiveHandoverBoundaryFactorization.V_before
          rate rewards C_star C_h i t z) ∨
      (after rate rewards C_star C_h ell t i z ∧
        ReferenceFirstLiveHandoverBoundaryFactorization.V_after
          rate rewards C_star C_h i t z) := by
    by_cases hb : before rate rewards C_star C_h ell t i z
    · by_cases hv : ReferenceFirstLiveHandoverBoundaryFactorization.V_before
        rate rewards C_star C_h i t z
      · exact Or.inl ⟨hb, hv⟩
      · right
        by_cases ha : after rate rewards C_star C_h ell t i z
        · by_cases hw : ReferenceFirstLiveHandoverBoundaryFactorization.V_after
            rate rewards C_star C_h i t z
          · exact ⟨ha, hw⟩
          · simp only [X_before, X_after, hb, hv, ha, hw, ite_true, ite_false,
              mul_zero, add_zero, zero_ne_one] at hservice
        · simp only [X_before, X_after, hb, hv, ha, ite_true, ite_false,
            mul_zero, zero_mul, add_zero, zero_ne_one] at hservice
    · right
      by_cases ha : after rate rewards C_star C_h ell t i z
      · by_cases hw : ReferenceFirstLiveHandoverBoundaryFactorization.V_after
          rate rewards C_star C_h i t z
        · exact ⟨ha, hw⟩
        · simp only [X_before, X_after, hb, ha, hw, ite_true, ite_false,
            zero_mul, mul_zero, add_zero, zero_ne_one] at hservice
      · simp only [X_before, X_after, hb, ha, ite_false,
          zero_mul, add_zero, zero_ne_one] at hservice
  have hraw : rawPending rate rewards C_star C_h ell t i z := by
    rcases hevent with hb | ha
    · exact hb.1.1.2
    · exact ha.1.1.2
  obtain ⟨k, htime⟩ := initial_rawPending_window_index
    rate rewards C_star C_h ell t i z hinitial hraw
  let r := (ReferenceFirstLiveSourceStoppedHandoverEndpoint.window
    rate rewards C_star C_h z).get k
  have hr : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t z = some r := by
    rw [← htime]
    exact (ReferenceFirstLiveSourceStoppedHandoverEndpoint.source_window_record_calendar
      rate rewards C_star C_h z k).2
  obtain ⟨selected, states, memories, hs, _hlive, _hp, _hrows, _hJ, _hrew,
      hin, hprep, hnone, hfields, _hnr, _hzero⟩ :=
    ReferenceFirstLiveHandoverSnapshotPrefix.actual_window_frame
      rate rewards C_star C_h z (crossing_of_window_index rate rewards C_star C_h z k) k
  obtain ⟨r0, selected0, states0, memories0, choice, choiceMemory,
      hr0, _ht0, _hs0, _hi0, _hc0, _hf0, _hn0, hchoice, hcode⟩ :=
    ReferenceOriginalInstallationHandoverChoiceFrame.rawPending_actual_choice_frame
      rate rewards C_star C_h ell t i z hraw
  have hrr : r0 = r := Option.some.inj (hr0.symm.trans hr)
  subst r0
  have hsame := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
    (hchoice.symm.trans (hprep i))
  have hstatus : preRoundStatus rate rewards C_star C_h t i z =
      some (FollowerDownMeasurability.followerStatusCode (states i).status) := by
    simpa only [hsame.1] using hcode
  refine ⟨r, hr, ?_⟩
  rcases hevent with ⟨hb, vb⟩ | ⟨ha, va⟩
  · left
    have hu : (states i).status = .unoccupied := by
      have he := Option.some.inj (hstatus.symm.trans hb.2)
      cases ht : (states i).status <;>
        simp [FollowerDownMeasurability.followerStatusCode, ht] at he ⊢
    obtain ⟨rv, hrv, hd, hi, hpos⟩ := vb
    have hev : rv = r := Option.some.inj (hrv.symm.trans hr)
    subst rv
    exact ⟨states i, memories i, hin i, (hnone i).mp hu, ⟨hd, hi⟩, hpos⟩
  · right
    have hu : (states i).status ≠ .unoccupied := by
      intro hu
      have he := Option.some.inj (hstatus.symm.trans ha.2)
      simp only [hu, FollowerDownMeasurability.followerStatusCode] at he
      cases he
    obtain ⟨rv, sv, hrv, hsv, hd, hi, hh, hpos⟩ := va
    have hev : rv = r := Option.some.inj (hrv.symm.trans hr)
    subst rv
    have hse : sv = selected := Option.some.inj (hsv.symm.trans hs)
    subst sv
    exact ⟨selected, hs, ⟨states i, memories i, hin i, hfields i hu⟩,
      ⟨hd, hi⟩, hh, hpos⟩

/-- On the actual initial installation branch, a fixed-calendar pending
follower is the same incoming follower in the stopped first-live source
readout, whenever the original inclusive stop mask retains its date. -/
private theorem initial_pending_to_physical_pending_of_beforeExcluded
    (ell s : Fin p.T) (i : Fin (p.m - 1)) (z : Source)
    (hinitial : initialBirthAt rate rewards C_star C_h ell z)
    (hpending : i ∈ pendingSet rate rewards C_star C_h ell s z)
    (hbeforeExcluded : s.val + 1 <
      ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstExcluded
        rate rewards C_star C_h z) :
    s.val + 1 ∈ ReferenceFirstLiveSourceStoppedHandoverEndpoint.supportDates
        rate rewards C_star C_h z ∧
      i ∈ ReferenceFirstLiveSourceStoppedHandoverEndpoint.pendingNat
        rate rewards C_star C_h s.val z := by
  classical
  have hfixed := (mem_pendingSet_iff rate rewards C_star C_h ell s i z).mp hpending
  rcases hfixed with ⟨_hbad, hraw⟩
  have hnotLater := initialBirthAt_not_laterBirthAt rate rewards C_star C_h ell z hinitial
  rcases hraw with hinitialRaw | hlaterRaw
  · rcases hinitialRaw with
      ⟨_birth, _hbirth, _hfirst, _hbirthTime, _hstart, j, hj,
        htime, selected, hselected, hi⟩
    let W := ReferenceOriginalInitialTransferWindowGeometry.rawInitialTransferWindow
      rate rewards C_star C_h z
    let r := W[j.val]
    have hwindowTime :=
      ReferenceOriginalInitialTransferWindowGeometry.raw_window_record_calendar
        rate rewards C_star C_h z j
    have htime' : r.input.time = s := htime
    have hlookup : ReferenceSourcePrefixHistoryFiltration.actualRecord
        rate rewards C_star C_h s z = some r := by
      rw [← htime']
      exact hwindowTime.2
    have hmissing :
        ReferenceFirstLiveSourceStoppedHandoverEndpoint.missing rate r =
          selected.view.pendingAtChoice := by
      unfold ReferenceFirstLiveSourceStoppedHandoverEndpoint.missing
        ReferenceFirstLiveSourceStoppedHandoverEndpoint.actualSelection
      rw [hselected]
      rfl
    have hmissingNonempty :
        (ReferenceFirstLiveSourceStoppedHandoverEndpoint.missing rate r).Nonempty :=
      ⟨i, hmissing ▸ hi⟩
    have hdate : s.val + 1 ∈
        ReferenceFirstLiveSourceStoppedHandoverEndpoint.supportDates
          rate rewards C_star C_h z := by
      apply (ReferenceFirstLiveSourceStoppedHandoverEndpoint.supportDates_mem_iff
        rate rewards C_star C_h z (s.val + 1)).2
      refine ⟨j, ?_, hmissingNonempty, hbeforeExcluded⟩
      change r.input.time.val + 1 = s.val + 1
      rw [htime']
    have hpendingNat :=
      ReferenceFirstLiveSourceStoppedHandoverEndpoint.pendingNat_eq_actual_missing_on_support
        rate rewards C_star C_h z s.val s.isLt hdate
    rw [hlookup] at hpendingNat
    have hpendingNat' :
        ReferenceFirstLiveSourceStoppedHandoverEndpoint.pendingNat
          rate rewards C_star C_h s.val z =
        ReferenceFirstLiveSourceStoppedHandoverEndpoint.missing rate r := by
      simpa only [Option.map_some, Option.getD_some] using hpendingNat
    exact ⟨hdate, hpendingNat' ▸ hmissing ▸ hi⟩
  · rcases hlaterRaw with
      ⟨b, hb, htime, hlookup, payload, ledger, saved, hstate, hempty,
        installed, hinstalled, _j, _hrowTime, _selected, _hselected, _hi⟩
    have hlater : laterBirthAt rate rewards C_star C_h ell z :=
      ⟨b, hb, htime, hlookup, payload, ledger, saved, hstate, hempty,
        installed, hinstalled⟩
    exact (hnotLater hlater).elim

/-- The original inclusive first-bad mask retains precisely the needed strict
past endpoint on the actual initial window. The current detecting update is
included in both masks. -/
theorem initial_pending_before_firstExcluded
    (ell t : Fin p.T) (i : Fin (p.m - 1)) (z : Source)
    (hinitial : initialBirthAt rate rewards C_star C_h ell z)
    (hpending : i ∈ pendingSet rate rewards C_star C_h ell t z) :
    t.val + 1 < ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstExcluded
      rate rewards C_star C_h z := by
  obtain ⟨hbad, hraw⟩ := (mem_pendingSet_iff rate rewards C_star C_h ell t i z).mp hpending
  obtain ⟨k, ht⟩ := initial_rawPending_window_index rate rewards C_star C_h ell t i z hinitial hraw
  have hbad' : ((ReferenceFirstLiveSourceStoppedHandoverEndpoint.window
      rate rewards C_star C_h z).get k).input.time.val + 1 ≤
      ReferenceCompleteSignedFirstBadCalendar.firstBadDate rate rewards C_star C_h z := by
    rw [ht]
    exact hbad
  have hd := window_decoder_cutoff_of_firstBad rate rewards C_star C_h z k hbad'
  have ho := window_overflow_cutoff_of_firstBad rate rewards C_star C_h z k hbad'
  rw [ht] at hd ho
  exact lt_min hd ho

/-- Current original pending membership supplies both physical quota inputs
internally, on the same source and the same unshifted incoming date. -/
theorem initial_pending_to_physical_pending
    (ell t : Fin p.T) (i : Fin (p.m - 1)) (z : Source)
    (hinitial : initialBirthAt rate rewards C_star C_h ell z)
    (hpending : i ∈ pendingSet rate rewards C_star C_h ell t z) :
    t.val + 1 ∈ ReferenceFirstLiveSourceStoppedHandoverEndpoint.supportDates
        rate rewards C_star C_h z ∧
      i ∈ ReferenceFirstLiveSourceStoppedHandoverEndpoint.pendingNat
        rate rewards C_star C_h t.val z := by
  exact initial_pending_to_physical_pending_of_beforeExcluded
    rate rewards C_star C_h ell t i z hinitial hpending
    (initial_pending_before_firstExcluded rate rewards C_star C_h ell t i z hinitial hpending)

/-- Every prefix of the literal fixed-calendar physical service count is
dominated by the accepted stopped count, without an external support or
service-correspondence premise. -/
theorem initial_service_count_le_stoppedServiceSum
    (ell : Fin p.T) (i : Fin (p.m - 1)) (z : Source) (n : ℕ)
    (hinitial : initialBirthAt rate rewards C_star C_h ell z) :
    (∑ s : Fin p.T,
      if s.val < n ∧ i ∈ pendingSet rate rewards C_star C_h ell s z ∧
        X_before rate rewards C_star C_h ell s i z +
          X_after rate rewards C_star C_h ell s i z = 1
      then (1 : ℕ) else 0) ≤
    stoppedServiceSum rate rewards C_star C_h z i n := by
  classical
  unfold stoppedServiceSum
  apply Finset.sum_le_sum
  intro s _
  by_cases hs : s.val < n ∧ i ∈ pendingSet rate rewards C_star C_h ell s z ∧
      X_before rate rewards C_star C_h ell s i z +
        X_after rate rewards C_star C_h ell s i z = 1
  · rw [ite_eq_left hs, ite_eq_left hs.1]
    have hp := (initial_pending_to_physical_pending
      rate rewards C_star C_h ell s i z hinitial hs.2.1).2
    obtain ⟨r, hr, hphysical⟩ := initial_service_physical
      rate rewards C_star C_h ell s i z hinitial hs.2.2
    change 1 ≤ physicalServiceTerm rate rewards C_star C_h z i s
    simp only [physicalServiceTerm, hr, hphysical]
    split
    · exact le_rfl
    · rename_i hnot
      exact (hnot ⟨hp, trivial⟩).elim
  · rw [ite_eq_right hs]
    exact Nat.zero_le _

/-- Strict incoming quota for the literal physical H indicators of the actual
initial installation. No prefix, decoder, overflow, or quota law is supplied;
the incoming event retains the first detecting date inclusively. -/
theorem initial_incoming_quota
    (ell t : Fin p.T) (i : Fin (p.m - 1)) (z : Source)
    (hinitial : initialBirthAt rate rewards C_star C_h ell z)
    (hpending : i ∈ pendingSet rate rewards C_star C_h ell t z) :
    (∑ s : Fin p.T,
      if s.val < t.val ∧ i ∈ pendingSet rate rewards C_star C_h ell s z ∧
        X_before rate rewards C_star C_h ell s i z +
          X_after rate rewards C_star C_h ell s i z = 1
      then (1 : ℕ) else 0) < 2 * AffineBatchDecoder.quota p + 1 := by
  obtain ⟨hdate, hi⟩ := initial_pending_to_physical_pending
    rate rewards C_star C_h ell t i z hinitial hpending
  exact lt_of_le_of_lt
    (initial_service_count_le_stoppedServiceSum rate rewards C_star C_h ell i z t.val hinitial)
    (actualStoppedServiceSum_lt_twoQ_add_one_before_pending
      rate rewards C_star C_h z i t hdate hi)

end Bandits.Support.ReferenceOriginalInitialHandoverIncomingQuota

end
