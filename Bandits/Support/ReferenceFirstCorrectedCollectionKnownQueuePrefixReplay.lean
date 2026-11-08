/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCorrectedNativeUpReplayCalendarJoin

import Mathlib.Tactic

/-!
# Prefixes on the first corrected collection calendar

Sources: ZIP4 `appendix_a_local_protocol.tex:28-64`,
`06_interruptions.tex:40-100,192-233,246-299`, and
`04_slow_fast_learner.tex:157-174`.

One original-source word supplies every shorter physical prefix. Every
actually known current and cutoff register on the first corrected collection
is identified with replay on that same calendar. An assigned known register
supplies a real earlier accepting input in its checked prefix; the literal
physical recorder, start, and filtered receiver identify that input with the
native UP observer. Its zero-prefix value supplies the cutoff seed. Unknown
registers remain optional. These are internal deterministic execution results;
no probability estimate or manuscript closure is asserted.
-/

@[expose] public section
noncomputable section

open Bandits.Support
open ConstructorDimensions
open ReferenceActivePhysicalStep
open ReferenceActivePhysicalHorizon
open ReferenceCollectionSegmentExtraction
open ReferenceFirstCollectionCorrectedSliceNumericalPrefix
open CoordinatorCollectionLedger
open CollectionCheckedExecution

namespace Bandits.Support.ReferenceFirstCorrectedCollectionKnownQueuePrefixReplay

variable {p : ConstructorDimensions.Parameters}

private theorem mapM_id_some {α : Type*} (slots : List (Option α)) (cells : List α)
    (h : slots.mapM id = some cells) : slots = cells.map some := by
  induction slots generalizing cells with
  | nil =>
      have he : cells = [] := (Option.some.inj h).symm
      subst cells
      rfl
  | cons slot slots ih =>
      cases slot with
      | none => simp [List.mapM_cons] at h
      | some a =>
          cases ht : slots.mapM id with
          | none => simp [List.mapM_cons, ht] at h
          | some tail =>
              have he : a :: tail = cells := by
                simpa [List.mapM_cons, ht] using h
              rw [← he, List.map_cons, ← ih tail ht]

private theorem mapM_some_id {α : Type*} (cells : List α) :
    (cells.map some).mapM id = some cells := by
  induction cells with
  | nil => rfl
  | cons cell cells ih =>
      simp only [List.map_cons, List.mapM_cons, ih]
      rfl

private theorem prefixInputs_take
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (n h : ℕ) (G : List (RecordedQueueRun.RoundInput p.K))
    (hG : prefixInputs rate rewards C_star C_h n z = some G)
    (hlaunch : ReferenceSourcePrefixHistoryFiltration.actualLaunchBy
      rate rewards C_star C_h
        (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + h) z)
    (hn : h ≤ n - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h) :
    prefixInputs rate rewards C_star C_h
      (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + h) z =
        some (G.take h) := by
  have hlaunchG := prefixInputs_launch rate rewards C_star C_h n z G hG
  have hsource : sourceStart rate rewards C_star C_h z =
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h := rfl
  have hn' : h ≤ n - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h := by
    simpa only [hsource] using hn
  simp only [prefixInputs, ite_eq_left hlaunchG] at hG
  have hmap := mapM_id_some _ G hG
  have htake := congrArg (List.take h) hmap
  simp only [← List.map_take, List.take_take] at htake
  rw [hsource, Nat.min_eq_left hn'] at htake
  rw [prefixInputs, ite_eq_left hlaunch, hsource,
    Nat.add_sub_cancel_left, htake]
  exact mapM_some_id _

private theorem liveTail_eq_continuingPrefix
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p) :
    ReferenceFirstCollectionCorrectedSliceNumericalPrefix.liveTail
        rate rewards C_star C_h z =
      ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
        rate rewards C_star C_h z
          (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.birthIndex
            rate rewards C_star C_h z + 1) := by
  simp only [ReferenceFirstCollectionCorrectedSliceNumericalPrefix.liveTail,
    ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords,
    ReferenceFirstReplacementLiveFollowerPrefix.continuingTail,
    ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix]
  congr 1
  funext r
  unfold ReferenceCompleteLaterLiveComplementPrefixReplay.continuingTest
    ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen
  cases r.output.preparation.coordinator with
  | live registers owned base outcome => cases outcome <;> rfl
  | first outcome => rfl
  | collection payload ledger clock cutoff outcome => rfl
  | invalidCollectionCutoff => rfl
  | dagger => rfl

/-- The accepted numerical collection join identifies the actual segment,
its source cells, the complete original prefix word, and every physical
source-slot prefix word on one calendar. -/
theorem firstCell_actual_segment_prefix_words
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hz : z ∈ ReferenceFirstCollectionCorrectedSliceNumericalPrefix.correctedCell
      rate rewards C_star C_h u t)
    (he : ReferenceFirstCollectionCorrectedSliceNumericalPrefix.birthIndex
        rate rewards C_star C_h z + 1 +
        (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.liveTail
          rate rewards C_star C_h z).length <
      (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords
        rate rewards C_star C_h z).length) :
    let R := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords
      rate rewards C_star C_h z
    let s := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart
      rate rewards C_star C_h z
    let b := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.birthIndex
      rate rewards C_star C_h z
    let e := b + 1 + (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.liveTail
      rate rewards C_star C_h z).length
    ∃ (L B : List (RecordedQueueRun.RoundInput p.K))
      (c : RecordedQueueRun.RoundInput p.K)
      (birth : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
      (payload : ReferenceActivePhysicalStep.Payload rate)
      (seg : ReferenceCollectionSegmentExtraction.Segment rate)
      (D : List (RecordedQueueRun.RoundInput p.K)),
      ReferenceFirstCollectionCurrentRetainedGate.pastCells?
        rate rewards C_star C_h t z = some L ∧
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
        rate rewards C_star C_h (t.val + 1) z = some (L ++ [c]) ∧
      L.length = b ∧ s + b = t.val ∧ R[b]? = some birth ∧
      ReferenceAssignmentPayloadPersistence.InstallationBirth birth payload ∧
      payload.sigma = t ∧ s < payload.sigma.val ∧
      ReferenceCollectionSegmentExtraction.segmentAt R e = some seg ∧
      seg.entry = R[e] ∧ seg.context.payload = payload ∧
      ReferenceCollectionPhaseHistory.cutoffChosen seg.entry.input = true ∧
      FollowerCutoffScan.firstCutoff p rate.eta.val payload.sigma
        (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
          (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z))) = s + e + 1 ∧
      let A := (L ++ [c]) ++ B
      A.length = e ∧ e ≤ R.length ∧
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
        rate rewards C_star C_h (s + e) z = some A ∧
      D.length = seg.records.length ∧
      (∀ j : Fin seg.records.length,
        ∃ hD : j.val < D.length,
          ReferenceFirstCollectionCurrentRetainedGate.cell0 rate seg.records[j.val] =
            some (D[j.val]'hD)) ∧
      (∀ a h, (seg.records.take h).map
        (ReferenceCollectionRawBufferHistory.physicalQueueRecord seg.context.preLedger a) =
        (D.take h).map (fun cell => (cell.enabled,
          RecordedQueueRun.quantizedArrival
            (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell a))) ∧
      (∀ a h, CollectionKnownQueueContinuation.inputQueueRecords seg.context.preLedger a
        (seg.inputs.take h) = (D.take h).map (fun cell => (cell.enabled,
          RecordedQueueRun.quantizedArrival
            (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell a))) ∧
      s + e + seg.records.length ≤ p.T ∧
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
        rate rewards C_star C_h (s + e + seg.records.length) z = some (A ++ D) ∧
      (∀ a h, ((A ++ D).take h).map (fun cell =>
          UnstoppedRecordedQueueComparison.unstoppedRecord
            (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell a) =
        ((A ++ D).take h).map (fun cell => (cell.enabled,
          RecordedQueueRun.quantizedArrival
            (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell a))) ∧
      (∀ v, v ≤ D.length →
        ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
          rate rewards C_star C_h (s + e + v) z = some (A ++ D.take v)) := by
  classical
  intro R s b e
  change e < R.length at he
  obtain ⟨L, c, birth, hL, _hc, hprefixBirth, hLb, hdateBirth, hb,
    _hbirthTime, _hrows, _hselected, _hrewards, _henabled, _hbirthRead, _hbirthCell,
    _hmode, hcalendar⟩ :=
    ReferenceFirstCorrectedCollectionCalendarNumericalJoin.firstCell_collection_calendar_numerical_values
      rate rewards C_star C_h u t z hz
  obtain ⟨birthR, rout, qout, beta, hbR, _hdateR, _htR, _hrowsR, _hJR,
    _hrewardsR, hbornR, hsigmaR, hlaterR, hliveR, _hcontR⟩ :=
    ReferenceFirstCorrectedReplacementCollectionReadout.firstCell_collection_readout_cover
      rate rewards C_star C_h u t z hz
  have hbirthEq : birthR = birth := Option.some.inj (hbR.symm.trans hb)
  subst birthR
  have hlenR := ReferenceCompletePhysicalHistory.completeSuffixRecords_length
    rate z rewards C_star C_h
  change R.length = p.T - s at hlenR
  have htT : t.val + 1 < p.T := by
    change s + b = t.val at hdateBirth
    change e < R.length at he
    dsimp only [e] at he
    omega
  obtain ⟨_hsigma, hcalendar⟩ := hcalendar rout qout beta hliveR
  obtain ⟨hk, hstate, hlater, _hBlen, heR, _heT, hAlen, _hAdate, hprefixA,
    _hwindow, _hWcells, _rE, _qE, _hpayE, _hstateE, hboundary⟩ := hcalendar htT
  let B := ReferenceCompleteLaterLiveComplementPrefixReplay.prefixCells
    rewards C_star C_h z ⟨b + 1, hk⟩ rout qout beta hstate hlater
  let A := (L ++ [c]) ++ B
  have hW := liveTail_eq_continuingPrefix rate rewards C_star C_h z
  simp only [← hW] at hAlen hprefixA hboundary heR
  change A.length = e at hAlen
  change ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
      rate rewards C_star C_h (s + e) z = some A at hprefixA
  rcases hboundary with hterminal | ⟨_he, seg, _IC, l0, hseg, hentry,
    hpay, hpre, _hIC, _hICdef, _hICchecked, _harmIC, _hIsigmaC,
    hIcut, hIscan, _hfreezeC, _hbaseC, hcutC, _hneC, _hpartC,
    D, hDlen, hDcells, hDwords, _hGlen, _hGbound, hGT, _hGrecords,
    hprefixG, _hGread, _hGdisabled, hGwords, _hGfinal⟩
  · change e = R.length at hterminal
    omega
  refine ⟨L, B, c, birth, rout.payload, seg, D, hL, hprefixBirth, hLb,
    hdateBirth, hb, hbornR, hsigmaR, hlaterR, hseg, hentry, hpay, hcutC, ?_,
    hAlen, heR, hprefixA, hDlen, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hIscan, hIcut]
    rfl
  · intro j
    refine ⟨?_, ?_⟩
    · rw [hDlen]
      exact j.isLt
    · exact (hDcells j).1
  · intro a h
    simpa only [← hpre] using (hDwords a).2.2 h
  · intro a h
    have hh := congrArg (List.take h) (hDwords a).1
    simpa only [CollectionKnownQueueContinuation.inputQueueRecords, List.map_take,
      ← hpre] using hh
  · change s + (e + seg.records.length) ≤ p.T at hGT
    simpa only [← Nat.add_assoc] using hGT
  · change ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
      rate rewards C_star C_h (s + (e + seg.records.length)) z = some (A ++ D) at hprefixG
    simpa only [← Nat.add_assoc] using hprefixG
  · intro a h
    exact (hGwords a).2.2 h
  · intro v hv
    have hfull : ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
        rate rewards C_star C_h (s + (e + D.length)) z = some (A ++ D) := by
      rw [hDlen]
      exact hprefixG
    have hs : s = ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h := rfl
    have hlaunchFull := prefixInputs_launch rate rewards C_star C_h
      (s + (e + D.length)) z (A ++ D) hfull
    have hlaunchPrefix : ReferenceSourcePrefixHistoryFiltration.actualLaunchBy
        rate rewards C_star C_h (s + (e + v)) z := by
      rcases hlaunchFull with ⟨hcross, _hstart⟩
      have htime : ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h ≤
          s + (e + v) := by
        rw [← hs]
        exact Nat.le_add_right s (e + v)
      exact ⟨hcross, htime⟩
    have hn : e + v ≤ (s + (e + D.length)) -
        ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h := by
      rw [hs, Nat.add_sub_cancel_left]
      exact Nat.add_le_add_left hv e
    have htake := prefixInputs_take rate rewards C_star C_h z
      (s + (e + D.length)) (e + v) (A ++ D) hfull hlaunchPrefix hn
    have hlist : (A ++ D).take (e + v) = A ++ D.take v := by
      rw [List.take_append, List.take_of_length_le (by omega), hAlen]
      simp only [Nat.add_sub_cancel_left]
    have htake' : ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
        rate rewards C_star C_h (s + (e + v)) z = some ((A ++ D).take (e + v)) := by
      simpa only [hs] using htake
    rw [hlist] at htake'
    simpa only [Nat.add_assoc] using htake'

/-- Every shorter boundary of a present corrected prefix is obtained from the
same original optional-slot word.  Since `prefixInputs` uses `mapM id`, no
missing physical slot is filtered out. -/
theorem prefixInputs_same_calendar_every_prefix
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (e : ℕ) (A D : List (RecordedQueueRun.RoundInput p.K))
    (hA : A.length = e)
    (hfull : prefixInputs rate rewards C_star C_h
      (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h +
        (e + D.length)) z = some (A ++ D)) :
    ∀ v, v ≤ D.length →
      prefixInputs rate rewards C_star C_h
        (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h +
          (e + v)) z = some (A ++ D.take v) := by
  intro v hv
  let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  have hlaunchFull := prefixInputs_launch rate rewards C_star C_h (s + (e + D.length)) z
    (A ++ D) (by simpa only [s, Nat.add_assoc] using hfull)
  have hlaunchPrefix : ReferenceSourcePrefixHistoryFiltration.actualLaunchBy
      rate rewards C_star C_h (s + (e + v)) z := by
    rcases hlaunchFull with ⟨hcross, hstart⟩
    refine ⟨hcross, ?_⟩
    omega
  have htake := prefixInputs_take rate rewards C_star C_h z
    (s + (e + D.length)) (e + v) (A ++ D)
    (by simpa only [s, Nat.add_assoc] using hfull) hlaunchPrefix (by omega)
  have hlist : (A ++ D).take (e + v) = A ++ D.take v := by
    rw [List.take_append, List.take_of_length_le (by omega), hA]
    simp only [Nat.add_sub_cancel_left]
  simpa only [s, Nat.add_assoc, hlist] using htake

/-- Taking a physical segment prefix preserves the source-slot identity with
the corresponding numerical cell prefix, for the same pre-ledger and arm. -/
theorem segment_prefix_physical_queue_words
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (seg : ReferenceCollectionSegmentExtraction.Segment rate)
    (D : List (RecordedQueueRun.RoundInput p.K))
    (a : Fin p.K)
    (hwords : seg.records.map
        (ReferenceCollectionRawBufferHistory.physicalQueueRecord seg.context.preLedger a) =
      D.map (fun d => (d.enabled,
        RecordedQueueRun.quantizedArrival
          (ReferenceFirstLaunchNumericalCell.queueParameters rate) d a)))
    (v : ℕ) :
    (seg.records.take v).map
        (ReferenceCollectionRawBufferHistory.physicalQueueRecord seg.context.preLedger a) =
      (D.take v).map (fun d => (d.enabled,
        RecordedQueueRun.quantizedArrival
          (ReferenceFirstLaunchNumericalCell.queueParameters rate) d a)) := by
  simpa only [List.map_take] using congrArg (List.take v) hwords

private theorem replay_backlog_independent_of_score
    (capacity score₁ score₂ backlog : ℕ) (records : List (Bool × ℕ)) :
    (QueueReplay.replay capacity (score₁, backlog) records).2 =
      (QueueReplay.replay capacity (score₂, backlog) records).2 := by
  induction records generalizing score₁ score₂ backlog with
  | nil => rfl
  | cons record records ih =>
      change (QueueReplay.replay capacity
          (QueueReplay.transition capacity (score₁, backlog) record) records).2 =
        (QueueReplay.replay capacity
          (QueueReplay.transition capacity (score₂, backlog) record) records).2
      have h₁ := CollectionKnownQueueContinuation.queueReplay_transition_add_score
        capacity score₁ backlog record
      have h₂ := CollectionKnownQueueContinuation.queueReplay_transition_add_score
        capacity score₂ backlog record
      rw [h₁, h₂]
      exact ih (score₁ + (QueueReplay.transition capacity (0, backlog) record).1)
        (score₂ + (QueueReplay.transition capacity (0, backlog) record).1)
        (QueueReplay.transition capacity (0, backlog) record).2

/-- An extracted source segment uses the source's own launch state and full
physical run, including the empty checked prefix after a failed first round. -/
private theorem actual_segment_run
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (e : ℕ) (seg : Segment rate)
    (hseg : segmentAt (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h) e = some seg) :
    let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
    ∃ (initial : ReferenceActivePhysicalStep.State p rate)
      (span : s + (p.T - s) ≤ p.T) (active : allActiveAtStart initial s),
      initial.coordinator = .first ∧
      ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h =
        (run initial z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)
          rewards s (p.T - s) span active).records := by
  intro s
  have hlaunchNe : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate z rewards C_star C_h ≠ none := by
    intro hnone
    have hnil : ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h = [] := by
      simp only [ReferenceCompletePhysicalHistory.completeSuffixRecords, hnone,
        dite_true]
    rw [hnil] at hseg
    simp only [segmentAt, List.drop_nil, ReferenceCollectionSegmentExtraction.segment] at hseg
    contradiction
  have hsome : (ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate z rewards C_star C_h).isSome = true := by
    cases hl : ReferenceCorrectedInitializationLaunch.correctedLaunch
        rate z rewards C_star C_h with
    | none => exact False.elim (hlaunchNe hl)
    | some initial => rfl
  have hc := (ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
    rate z rewards C_star C_h).mp hsome
  obtain ⟨initial, hlaunch, hfirst, _⟩ :=
    ReferenceCorrectedInitializationLaunch.correctedLaunch_coordinator_provenance
      rate z rewards C_star C_h hc
  have hs := ReferenceCompletePhysicalHistory.physicalStart_le_T rate z rewards C_star C_h
  exact ⟨initial, by dsimp only [s]; omega,
    ReferenceCompletePhysicalHistory.activeMode_of_launch_eq_some
      rate z rewards C_star C_h initial hlaunch, hfirst,
    ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
      rate z rewards C_star C_h initial hlaunch⟩

/-- Every actual source-segment prefix is a checked execution from that
segment's own initializer. No successful UP or terminal-pending test is an input. -/
theorem actual_segment_prefix_execution
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (e : ℕ) (seg : Segment rate)
    (hseg : segmentAt (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h) e = some seg)
    (v : ℕ) (hv : v ≤ seg.records.length) :
    ∃ (I : Initializer p) (accepted : List Bool),
      seg.context.initializer = some I ∧
      I.checkedStart rate = .success seg.context.preLedger ∧
      CollectionCheckedExecution.startAndRunChecked p rate.eta.val rate.eta.property
        (ReferenceUpReception.sourceCap_forLedger rate) rate.n rate.n_scale
        I.assignment I.sigma I.cutoff I.freezeAt I.base I.outside (seg.inputs.take v) =
        .success ⟨seg.context.preLedger, accepted,
          endpointLedger seg.context.preLedger (seg.records.take v)⟩ := by
  obtain ⟨initial, span, active, hfirst, hrun⟩ :=
    actual_segment_run rate rewards C_star C_h z e seg hseg
  have hsegRun := hseg
  rw [hrun] at hsegRun
  obtain ⟨I, hI, hstart, _⟩ :=
    ReferenceCollectionRawBufferHistory.run_collection_raw_buffer_execution
      initial z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)
      rewards _ _ span active hfirst e seg hsegRun
  obtain ⟨accepted, hfold⟩ :=
    ReferenceCollectionPrefixLedgerHistory.run_segment_prefix_checked
      initial z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)
      rewards _ _ span active e seg hsegRun v hv
  refine ⟨I, accepted, hI, hstart, ?_⟩
  change CoordinatorCollectionLedger.startCollectionChecked _ _ _ _ _ _
    _ _ _ _ _ _ = .success seg.context.preLedger at hstart
  simp only [CollectionCheckedExecution.startAndRunChecked, hstart, hfold]

private theorem inputs_getElem_of_completed
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (hgood : ∀ r ∈ records, (extractRound r).isSome = true)
    (j : ℕ) (hj : j < records.length) (done : CompletedRound rate)
    (hdone : extractRound records[j] = some done) :
    (inputs records)[j]? = some done.input := by
  induction records generalizing j with
  | nil => simp only [List.length_nil] at hj; omega
  | cons r rs ih =>
    cases hr : extractRound r with
    | none => have h := hgood r List.mem_cons_self; simp only [hr] at h; contradiction
    | some head =>
      cases j with
      | zero =>
        have heq : head = done := Option.some.inj (hr.symm.trans hdone)
        subst head
        simp only [inputs, completed, List.filterMap_cons, hr, List.map_cons,
          List.getElem?_cons_zero]
      | succ j =>
        have hj' : j < rs.length := by simp only [List.length_cons] at hj; omega
        have he := ih (fun q hq => hgood q (List.mem_cons_of_mem r hq)) j hj' hdone
        simpa only [inputs, completed, List.filterMap_cons, hr, List.map_cons,
          List.getElem?_cons_succ] using he

private theorem choice_executedTail
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (x : ReferenceActivePhysicalStep.RoundInput p rate) (c : Choice rate)
    (hc : choice x = some c) :
    ReferenceCollectionPhaseHistory.executedTail x = some
      ⟨c.payload, c.preLedger, c.started, c.weights⟩ := by
  unfold choice at hc
  unfold ReferenceCollectionPhaseHistory.executedTail
  split at hc
  · contradiction
  next hn =>
    rw [ite_eq_right hn]
    cases hd : (prepare x).coordinator with
    | first outcome => cases outcome <;> simp [hd, choiceOfCut] at hc
    | live r owned base outcome =>
      cases outcome <;> simp only [hd, choiceOfCut, reduceCtorEq] at hc
      next => cases Option.some.inj hc; rfl
    | collection payload ledger clock cutoff outcome =>
      cases outcome <;> simp only [hd, choiceOfCut, reduceCtorEq] at hc
      next => cases Option.some.inj hc; rfl
    | invalidCollectionCutoff => simp [hd, choiceOfCut] at hc
    | dagger => simp [hd, choiceOfCut] at hc

private theorem decodePrefixQueue_zero_of_success
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (l result : ReferenceActivePhysicalStep.Ledger rate)
    (i : Fin (p.m - 1)) (M : ReferenceCollectionPhaseHistory.UpRecord p rate)
    (h : decodeUp l i (some M) = .success result) :
    ReferenceFirstCorrectedNativeUpComputedPrefixObservation.decodePrefixQueue?
      rate l i (some M) 0 = some (l.assignment.arm i, M.val.q) := by
  classical
  have hinput : validLedgerCheck l = true ∧ l.phase = .started ∧
      1 ≤ l.cutoff ∧ l.cutoff ≤ l.cursor ∧ l.cursor ≤ p.T := by
    by_contra hn
    simp only [decodeUp, dite_eq_right hn] at h
    contradiction
  have haccept : acceptUpCheck l i M = true := by
    by_contra hn
    simp only [decodeUp, dite_eq_left hinput, Bool.not_eq_true] at h hn
    rw [hn] at h
    simp only [Bool.false_eq_true, ite_false] at h
    split at h <;> contradiction
  have hunknown : l.currentRegisters (l.assignment.arm i) = none ∧
      l.cutoffRegisters (l.assignment.arm i) = none := by
    by_contra hn
    simp only [decodeUp, dite_eq_left hinput, haccept, dite_eq_right hn] at h
    contradiction
  obtain ⟨bound, last, hlast, past, current, hpast, hcurrent, _, _⟩ :=
    CollectionCheckedExecution.decodeUp_success_candidate l result i M h
  have hlastEq : last = ⟨l.cursor - 1, by have ht := hinput.2.2.2.2; omega⟩ := by
    apply Fin.ext
    dsimp only [sourceRound] at hlast
    change last.val = l.cursor - 1
    omega
  rw [hlastEq] at hcurrent
  have hdomain : replayOutputDomainsCheck (p := p) (4 * rate.n) M.val.q
      (past ++ [current]) = true := by
    by_contra hn
    simp only [decodeUp, dite_eq_left hinput, haccept, dite_eq_left hunknown,
      hpast, hcurrent, Bool.not_eq_true] at h hn
    rw [hn] at h
    contradiction
  have hguards : (decide ((past ++ [current]).length ≤ p.T) &&
      (past ++ [current]).all (fun r => decide (r.2 ≤ ConstructorDimensions.D p))) = true := by
    simp only [replayOutputDomainsCheck, Bool.and_eq_true] at hdomain
    simp only [Bool.and_eq_true]
    exact hdomain.1
  exact ReferenceFirstCorrectedNativeUpComputedPrefixObservation.decodePrefixQueue?_zero_of_reached
    rate l i M hinput haccept hunknown past current hpast hcurrent hguards

/-- An actual accepting receiver exposes its actual cutoff queue in the
zero-prefix native diagnostic. This reverses no parser or word filter. -/
private theorem accepted_record_zero_observer
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (c : Choice rate) (hc : choice record.input = some c)
    (i : Fin (p.m - 1)) (M : ReferenceCollectionPhaseHistory.UpRecord p rate)
    (hacc : ReferenceCollectionPhaseHistory.AcceptedUp record.input i M) :
    ReferenceFirstCorrectedNativeUpComputedPrefixObservation.recordPrefixQueue? rate record 0 =
      some (c.preLedger.assignment.arm i, M.val.q) := by
  classical
  obtain ⟨tail, recording, started, decoded, bank, htail, hrecorder,
    hstart, hreceive, hparse, hsender⟩ := hacc
  have htailEq : tail = ⟨c.payload, c.preLedger, c.started, c.weights⟩ :=
    Option.some.inj (htail.symm.trans (choice_executedTail record.input c hc))
  subst tail
  have hdecode := receiveUp_decode_result record.input started
  rw [hreceive] at hdecode
  change decodeUp started (upSenderIndex record.input)
    (ReferenceCollectionPhaseHistory.filteredParsed record.input started) = .success decoded at hdecode
  rw [hparse, ← hsender] at hdecode
  have hzero := decodePrefixQueue_zero_of_success started decoded i M hdecode
  have hassign : started.assignment = c.preLedger.assignment := by
    rw [CollectionCheckedExecution.startRound_success_candidate c.preLedger started
      (record.input.time.val + 1) (collectionEnabled c.preLedger record.input.time)
      (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) hstart]
    rfl
  have hcheck := receiveUp_input_check record.input started (by rw [hreceive]; intro h; contradiction)
  have hobs : record.output.coordinator = collectionPostChoice (prepare record.input)
      c.payload c.preLedger c.started c.weights := by
    rw [record.output_eq]
    exact choice_tail record.input c hc
  unfold ReferenceFirstCorrectedNativeUpComputedPrefixObservation.recordPrefixQueue?
  rw [hobs]
  unfold collectionPostChoice
  dsimp only at hrecorder hstart
  rw [hrecorder]
  dsimp only
  rw [hstart, ReferenceActiveAffinePositiveTest.collectionFinish_up]
  unfold receiveUp
  dsimp only
  rw [ite_eq_left hcheck]
  dsimp only [Option.bind_some]
  change ReferenceFirstCorrectedNativeUpComputedPrefixObservation.decodePrefixQueue?
    rate started (upSenderIndex record.input)
    (ReferenceCollectionPhaseHistory.filteredParsed record.input started) 0 = _
  rw [hparse, ← hsender, hzero, hassign]

/-- A known assigned arm on an actual retained prefix has a real accepting
physical record strictly before that prefix. The accepting input and message
are extracted from the checked prefix, then identified with the very same
record's recorder/start/filtered receiver calls. -/
theorem actual_segment_known_assigned_prefix_accepted
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (e : ℕ) (seg : Segment rate)
    (hseg : segmentAt (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h) e = some seg)
    (v : ℕ) (hv : v ≤ seg.records.length) (i : Fin (p.m - 1))
    (current : CurrentRegister)
    (hknown : (endpointLedger seg.context.preLedger (seg.records.take v)).currentRegisters
      (seg.context.preLedger.assignment.arm i) = some current) :
    ∃ (j : ℕ) (hj : j < seg.records.length)
      (M : ReferenceCollectionPhaseHistory.UpRecord p rate),
      j < v ∧ ReferenceCollectionPhaseHistory.AcceptedUp seg.records[j].input i M ∧
      ReferenceFirstCorrectedNativeUpComputedPrefixObservation.recordPrefixQueue?
        rate seg.records[j] 0 = some (seg.context.preLedger.assignment.arm i, M.val.q) ∧
      current.queue = (QueueReplay.replay (4 * rate.n) (0, M.val.q)
        (CollectionKnownQueueContinuation.inputQueueRecords seg.context.preLedger
          (seg.context.preLedger.assignment.arm i) (seg.inputs.take v))).2 ∧
      (∀ cutoff, (endpointLedger seg.context.preLedger (seg.records.take v)).cutoffRegisters
        (seg.context.preLedger.assignment.arm i) = some cutoff → cutoff.queue = M.val.q) := by
  classical
  obtain ⟨I, accepted, hI, hstartI, hchecked⟩ :=
    actual_segment_prefix_execution rate rewards C_star C_h z e seg hseg v hv
  let execution : CollectionCheckedExecution.Execution p rate.eta.val rate.eta.property
      (ReferenceUpReception.sourceCap_forLedger rate) rate.n rate.n_scale :=
    ⟨seg.context.preLedger, accepted, endpointLedger seg.context.preLedger (seg.records.take v)⟩
  obtain ⟨pre, input, suffix, prefixAccepted, before, started, decoded, finished,
    suffixAccepted, M, hsplit, hselected, hparsed, hprefix, _hunknown, hs, hd,
    _hf, _hsuffix, _hunique, hcur, _hinc, hcut, _hcursor, _hcursorEnd,
    _hchron, _hraw, _henables, _hassign, _hcutoff, _hfreeze⟩ :=
    CollectionFullInputReplay.assigned_follower_full_input_queue_replay
      I.assignment I.sigma I.cutoff I.freezeAt I.base I.outside
      (seg.inputs.take v) execution i hchecked ⟨current, hknown⟩
  have hcount := segment_input_count _ seg (segmentAt_branch _ e seg hseg).1
  have hjv : pre.length < v := by
    have hh := congrArg List.length hsplit
    simp only [List.length_take, List.length_append, List.length_cons, hcount,
      Nat.min_eq_left hv] at hh
    omega
  have hj : pre.length < seg.records.length := Nat.lt_of_lt_of_le hjv hv
  have hgood := segment_all_completed _ seg (segmentAt_branch _ e seg hseg).1
  obtain ⟨done, hdone⟩ : ∃ done, extractRound seg.records[pre.length] = some done := by
    cases hh : extractRound seg.records[pre.length] with
    | none => have hg := hgood _ (List.getElem_mem hj); simp only [hh] at hg; contradiction
    | some done => exact ⟨done, rfl⟩
  have hinputAt : seg.inputs[pre.length]? = some input := by
    have hh := congrArg (fun xs => xs[pre.length]?) hsplit
    rw [List.getElem?_take, ite_eq_left hjv, List.getElem?_append_right (by rfl),
      Nat.sub_self, List.getElem?_cons_zero] at hh
    exact hh
  have hdoneInput : done.input = input := Option.some.inj
    ((inputs_getElem_of_completed seg.records hgood pre.length hj done hdone).symm.trans hinputAt)
  have hpre : seg.inputs.take pre.length = pre := by
    have hh := congrArg (List.take pre.length) hsplit
    rw [List.take_take, Nat.min_eq_left (by omega), List.take_left] at hh
    exact hh
  obtain ⟨initial, span, active, _hfirst, hrun⟩ :=
    actual_segment_run rate rewards C_star C_h z e seg hseg
  have hsegRun := hseg
  rw [hrun] at hsegRun
  have hbeforeActual := ReferenceCollectionPrefixLedgerHistory.retained_completed_preledger
    initial z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)
    rewards _ _ span active e seg hsegRun pre.length hj done hdone
  obtain ⟨acceptedPre, hcheckedPre⟩ :=
    ReferenceCollectionPrefixLedgerHistory.run_segment_prefix_checked
      initial z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)
      rewards _ _ span active e seg hsegRun pre.length (Nat.le_of_lt hj)
  rw [hpre] at hcheckedPre
  have hbefore : before = done.context.preLedger := by
    have hh := congrArg Prod.snd (Option.some.inj (hprefix.symm.trans hcheckedPre))
    exact hh.trans hbeforeActual.symm
  obtain ⟨recording, startedA, decodedA, bankA, _hrecording, hrecorder,
    hstartA, hinputA, hreceiveA, hcheckA⟩ :=
    actual_collection_round_inputs seg.records[pre.length] done hdone
  have hs' : startRound done.context.preLedger
      (sourceRound done.input.round) done.input.enabled done.input.raw = .success started := by
    rw [hdoneInput, ← hbefore]
    exact hs
  rw [hinputA] at hs'
  have hstarted : startedA = started := Checked.success.inj (hstartA.symm.trans hs')
  subst startedA
  have hparsedA : effectiveParse seg.records[pre.length].input started = some M := by
    rw [← hdoneInput, hinputA] at hparsed
    exact hparsed
  have hsender : i = upSenderIndex seg.records[pre.length].input := by
    rw [← hdoneInput, hinputA] at hselected
    exact hselected.symm
  have hdecodeA : decodeUp started (upSenderIndex seg.records[pre.length].input)
      (effectiveParse seg.records[pre.length].input started) = .success decoded := by
    rw [← hsender, hparsedA]
    simpa only [hselected, hparsed] using hd
  have hreceive := receiveUp_filtered seg.records[pre.length].input started hcheckA
  rw [hdecodeA] at hreceive
  change (receiveUp (prepare seg.records[pre.length].input) started).result =
    .success (decoded, _) at hreceive
  have hchoice := (actual_collection_round_checked _ done hdone).1
  have hacc : ReferenceCollectionPhaseHistory.AcceptedUp seg.records[pre.length].input i M :=
    ⟨⟨done.context.payload, done.context.preLedger, done.context.started,
      done.context.weights⟩, recording, started, decoded, _,
    choice_executedTail _ done.context hchoice, hrecorder, hstartA,
    hreceive, hparsedA, hsender⟩
  have hzero := accepted_record_zero_observer seg.records[pre.length] done.context hchoice i M hacc
  have hcontext := CollectionBufferProvenance.checkedRounds_success_preserves_context
    execution.initial before pre prefixAccepted hprefix
  have hassignBefore : before.assignment = seg.context.preLedger.assignment :=
    congrArg (fun context => context.1) hcontext
  rw [← hbefore, hassignBefore] at hzero
  refine ⟨pre.length, hj, M, hjv, hacc, hzero, ?_, ?_⟩
  · exact congrArg CurrentRegister.queue (Option.some.inj (hknown.symm.trans hcur))
  · intro cutoff hcutoff
    exact congrArg CutoffRegister.queue (Option.some.inj (hcutoff.symm.trans hcut))

/-- The initially known queues are seeded at the actual cutoff boundary,
before its first collection update. Assigned unknown registers remain absent. -/
theorem firstCell_initial_known_queue_seed
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hz : z ∈ correctedCell rate rewards C_star C_h u t)
    (seg : Segment rate)
    (hseg : segmentAt (sourceRecords rate rewards C_star C_h z)
      (birthIndex rate rewards C_star C_h z + 1 + (liveTail rate rewards C_star C_h z).length) = some seg)
    (A : List (RecordedQueueRun.RoundInput p.K))
    (hA : prefixInputs rate rewards C_star C_h
      (sourceStart rate rewards C_star C_h z + birthIndex rate rewards C_star C_h z + 1 +
        (liveTail rate rewards C_star C_h z).length) z = some A) :
    ∀ a, (∀ current, seg.context.preLedger.currentRegisters a = some current →
      current.queue = (UnstoppedRecordedQueueComparison.unstoppedReplay
        (ReferenceFirstLaunchNumericalCell.queueParameters rate) A A.length a).2) ∧
      (∀ cutoff, seg.context.preLedger.cutoffRegisters a = some cutoff →
      cutoff.queue = (UnstoppedRecordedQueueComparison.unstoppedReplay
        (ReferenceFirstLaunchNumericalCell.queueParameters rate) A A.length a).2) ∧
      seg.context.preLedger.increment a = 0 := by
  classical
  let R := sourceRecords rate rewards C_star C_h z
  let s := sourceStart rate rewards C_star C_h z
  let b := birthIndex rate rewards C_star C_h z
  let e := b + 1 + (liveTail rate rewards C_star C_h z).length
  have he : e < R.length := by
    by_contra hn
    have hnil : R.drop e = [] := List.drop_eq_nil_iff.mpr (by omega)
    have hb := (segmentAt_branch R e seg hseg).1
    rw [hnil] at hb
    contradiction
  obtain ⟨L, c, birth, _hL, _hc, _hprefixBirth, _hLb, _hbsub, hdateBirth,
    _henabled, hb, _har, _ht, _hrows, _hJ, _hrewards, _hcurrent, _hnext, hcont⟩ :=
    ReferenceFirstCollectionCorrectedOutsideCutoffNumericalJoin.firstCell_outside_cutoff_numerical_join
      rate rewards C_star C_h u t z hz
  obtain ⟨birthR, rout, qout, beta, hbR, _hdateR, _htR, _hrowsR, _hJR,
    _hrewardsR, _hbornR, _hsigmaR, _hlaterR, hliveR, _hcontR⟩ :=
    ReferenceFirstCorrectedReplacementCollectionReadout.firstCell_collection_readout_cover
      rate rewards C_star C_h u t z hz
  have hbirthEq : birthR = birth := Option.some.inj (hbR.symm.trans hb)
  subst birthR
  obtain ⟨_hsigma, hcont⟩ := hcont rout qout beta hliveR
  have hlen := ReferenceCompletePhysicalHistory.completeSuffixRecords_length rate z rewards C_star C_h
  change R.length = p.T - s at hlen
  change s + b = t.val at hdateBirth
  have htT : t.val + 1 < p.T := by dsimp only [e] at he; omega
  obtain ⟨_next, _hk, _hstate, _hlater, _hnext, _hnextState, _hBlen, _heR,
    _heT, _hWtimes, _hprefixes, hprefixA, _hAlen, hdateA,
    rE, qE, _hpE, _hlastE, _hstateE, _hvaluesE, hboundary⟩ := hcont htT
  have hW := liveTail_eq_continuingPrefix rate rewards C_star C_h z
  simp only [← hW] at hprefixA hdateA hboundary
  change s + e = _ at hdateA
  have hAeq : ((L ++ [c]) ++
      ReferenceCompleteLaterLiveComplementPrefixReplay.prefixCells
        rewards C_star C_h z ⟨b + 1, _hk⟩ rout qout beta _hstate _hlater) = A := by
    rw [← hdateA] at hprefixA
    apply Option.some.inj
    exact hprefixA.symm.trans (by simpa only [s, e, b, Nat.add_assoc] using hA)
  rcases hboundary with hterminal | ⟨_he, chosen, _hchosen, _hprepared, hbranch⟩
  · change e = R.length at hterminal
    omega
  cases chosen <;> try contradiction
  next dispatched hstart ledger hinit hledger hvalid hclock hpending hnone selected =>
    obtain ⟨_htau, _htau', _huc, _hscan, segF, I, hsegF, _hentry,
      _hpay, hpre, _hI, _hIdef, _hIchecked, _hIarm, _hIsigma, _hIcut,
      _hfreeze, _hbase, _hne, _hpartition, _hexit, _hwhole, _hcalendar,
      _hcount, _hpositive, hknown0, hassigned0, _hrest⟩ := hbranch
    have hsegEq : segF = seg := Option.some.inj (hsegF.symm.trans hseg)
    subst segF
    rw [← hpre] at hknown0 hassigned0
    rw [hAeq] at hknown0
    have hinc : ∀ a, seg.context.preLedger.increment a = 0 := by
      rw [hpre]
      unfold Initializer.checkedStart startCollectionChecked at _hIchecked
      repeat (first | split at _hIchecked | dsimp only at _hIchecked)
      all_goals first | contradiction |
        (injection _hIchecked with heq; rw [← heq]; intro a; rfl)
    intro a
    by_cases ha : a ∈ rout.payload.slowSet.1
    · have hm : a ∈ Finset.univ.image rout.payload.assignment.assigned := by
        rw [rout.payload.assignment_image]
        exact ha
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hm
      have hn := hassigned0 i
      rw [hi] at hn
      refine ⟨?_, ?_, hinc a⟩
      · intro current hc
        rw [hn.2] at hc
        contradiction
      · intro cutoff hc
        rw [hn.1] at hc
        contradiction
    · let j : CanonicalFastSampling.FastArm rout.payload.slowSet :=
        ⟨a, Finset.mem_sdiff.mpr ⟨Finset.mem_univ a, ha⟩⟩
      obtain ⟨_, hcutoff, hcurrent, _⟩ := hknown0 j
      refine ⟨?_, ?_, hinc a⟩
      · intro current hc
        exact congrArg CurrentRegister.queue (Option.some.inj (hc.symm.trans hcurrent))
      · intro cutoff hc
        exact congrArg CutoffRegister.queue (Option.some.inj (hc.symm.trans hcutoff))

private theorem firstCell_zero_observer_seed
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hz : z ∈ correctedCell rate rewards C_star C_h u t)
    (seg : Segment rate)
    (hseg : segmentAt (sourceRecords rate rewards C_star C_h z)
      (birthIndex rate rewards C_star C_h z + 1 + (liveTail rate rewards C_star C_h z).length) = some seg)
    (hentry : (sourceRecords rate rewards C_star C_h z)[birthIndex rate rewards C_star C_h z + 1 + (liveTail rate rewards C_star C_h z).length]? =
        some seg.entry)
    (hcut : ReferenceCollectionPhaseHistory.cutoffChosen seg.entry.input = true)
    (j : ℕ) (hj : j < seg.records.length) (a : Fin p.K) (q : ℕ)
    (hzero : ReferenceFirstCorrectedNativeUpComputedPrefixObservation.recordPrefixQueue?
      rate seg.records[j] 0 = some (a, q))
    (A : List (RecordedQueueRun.RoundInput p.K))
    (hA : prefixInputs rate rewards C_star C_h
      (sourceStart rate rewards C_star C_h z +
        (birthIndex rate rewards C_star C_h z + 1 + (liveTail rate rewards C_star C_h z).length)) z =
        some A) :
    q = (UnstoppedRecordedQueueComparison.unstoppedReplay
      (ReferenceFirstLaunchNumericalCell.queueParameters rate) A A.length a).2 := by
  let R := sourceRecords rate rewards C_star C_h z
  let e := birthIndex rate rewards C_star C_h z + 1 + (liveTail rate rewards C_star C_h z).length
  have hrecord : R[e + j]? = some seg.records[j] := by
    have hp := segmentAt_partition R e seg hseg
    rw [← List.getElem?_drop, ← hp, List.getElem?_append_left hj,
      List.getElem?_eq_getElem hj]
  dsimp only [R, e] at hrecord
  have hqueue : ReferenceFirstCorrectedNativeUpComputedPrefixObservation.firstPrefixQueueAt
      rate rewards C_star C_h z j 0 = some (a, q) := by
    simp only [ReferenceFirstCorrectedNativeUpComputedPrefixObservation.firstPrefixQueueAt,
      hentry, hcut, hseg, ite_true, ite_eq_left (Nat.le_of_lt hj), hrecord, Option.bind_some, hzero]
  obtain ⟨_entry, _record, _seg, _d, _M, _past, _current, AN, DN, PN,
    _hentry, _hentryEq, _hcut, _hseg, _hjpos, _hjlt, _hn, _hk,
    _hrecord, _hd, _hsender, _hparsed, _hacc, _harm, _hdecoded, _hpast,
    _hword, _hq, _hAlen, _hDlen, hPN, _hPlen, hprefixAN, _hprefixG,
    _hprefixP, _htimeLeft, _htimeRight, _hGT, hfinal⟩ :=
    ReferenceFirstCorrectedNativeUpReplayCalendarJoin.firstCell_nativeUp_replay_calendar_join
      rate rewards C_star C_h u t z hz j 0 a q hqueue
  have hAN : AN = A := Option.some.inj (hprefixAN.symm.trans hA)
  simp only [List.take_zero, List.append_nil] at hPN
  simpa only [hPN, hAN] using hfinal

variable {eta : ℝ} {heta : 0 < eta}
  {hcap : CoordinatorCollectionLedger.sourceLearningCap p eta} {n : ℕ}
  {hn : (n : ℝ) = eta * (ConstructorDimensions.D p : ℝ)}

private theorem startCollectionChecked_success_valid
    (assignment : Assignment p) (sigma cutoff freezeAt : ℕ)
    (baseScore : Fin (p.m - 1) → ℕ)
    (outside : Fin p.K → Option CutoffRegister)
    (initial : Ledger p eta heta hcap n hn)
    (h : startCollectionChecked p eta heta hcap n hn assignment sigma cutoff
      freezeAt baseScore outside = .success initial) :
    validLedgerCheck initial = true := by
  unfold startCollectionChecked at h
  repeat (first | split at h | dsimp only at h)
  all_goals
    first
    | contradiction
    | (injection h with heq; cases heq; assumption)

private theorem finishRound_success_valid
    (l result : Ledger p eta heta hcap n hn)
    (h : finishRound l = .success result) : validLedgerCheck result = true := by
  unfold finishRound at h
  repeat (first | split at h | dsimp only at h)
  all_goals
    first
    | contradiction
    | (injection h with heq; cases heq; assumption)

private theorem checkedRounds_success_valid
    (l final : Ledger p eta heta hcap n hn)
    (inputs : List (RoundInput (p := p) (eta := eta)))
    (accepted : List Bool)
    (hvalid : validLedgerCheck l = true)
    (hfold : checkedRounds l inputs = some (accepted, final)) :
    validLedgerCheck final = true := by
  induction inputs generalizing l accepted final with
  | nil =>
      simp only [checkedRounds] at hfold
      rcases hfold with ⟨rfl, rfl⟩
      exact hvalid
  | cons input rest ih =>
      cases hstart : startRound l (sourceRound input.round) input.enabled input.raw with
      | invalid => simp [checkedRounds, hstart] at hfold
      | rejected bad => simp [checkedRounds, hstart] at hfold
      | success started =>
          cases hdecode : decodeUp started input.selectedFollower input.parsed with
          | invalid => simp [checkedRounds, hstart, hdecode] at hfold
          | rejected decoded =>
              cases hfinish : finishRound decoded with
              | invalid => simp [checkedRounds, hstart, hdecode, hfinish] at hfold
              | rejected bad => simp [checkedRounds, hstart, hdecode, hfinish] at hfold
              | success finished =>
                  cases htail : checkedRounds finished rest with
                  | none => simp [checkedRounds, hstart, hdecode, hfinish, htail] at hfold
                  | some pair =>
                      have hfold' : false :: pair.1 = accepted ∧ pair.2 = final := by
                        simpa [checkedRounds, hstart, hdecode, hfinish, htail]
                          using hfold
                      rcases hfold' with ⟨rfl, rfl⟩
                      exact ih finished pair.2 pair.1
                        (finishRound_success_valid decoded finished hfinish) htail
          | success decoded =>
              cases hfinish : finishRound decoded with
              | invalid => simp [checkedRounds, hstart, hdecode, hfinish] at hfold
              | rejected bad => simp [checkedRounds, hstart, hdecode, hfinish] at hfold
              | success finished =>
                  cases htail : checkedRounds finished rest with
                  | none => simp [checkedRounds, hstart, hdecode, hfinish, htail] at hfold
                  | some pair =>
                      have hfold' : true :: pair.1 = accepted ∧ pair.2 = final := by
                        simpa [checkedRounds, hstart, hdecode, hfinish, htail]
                          using hfold
                      rcases hfold' with ⟨rfl, rfl⟩
                      exact ih finished pair.2 pair.1
                        (finishRound_success_valid decoded finished hfinish) htail

private theorem valid_register_options
    (l : CoordinatorCollectionLedger.Ledger p eta heta hcap n hn)
    (hvalid : validLedgerCheck l = true) (a : Fin p.K) :
    (l.currentRegisters a = none ↔ l.cutoffRegisters a = none) ∧
    (l.currentRegisters a = none → ∃ i, l.assignment.arm i = a) := by
  have hc : allFin p.K (fun b =>
      (l.currentRegisters b).isNone == armPendingCheck l b) = true := by
    have hh := hvalid
    simp only [validLedgerCheck, Bool.and_eq_true] at hh
    tauto
  have hk : allFin p.K (fun b =>
      (l.cutoffRegisters b).isNone == armPendingCheck l b) = true := by
    have hh := hvalid
    simp only [validLedgerCheck, Bool.and_eq_true] at hh
    tauto
  unfold allFin at hc hk
  have hcA := List.all_eq_true.mp hc _ (List.mem_ofFn.mpr ⟨a, rfl⟩)
  have hkA := List.all_eq_true.mp hk _ (List.mem_ofFn.mpr ⟨a, rfl⟩)
  have hcurr : (l.currentRegisters a).isNone = armPendingCheck l a := by
    simpa only [id_eq, beq_iff_eq] using hcA
  have hcut : (l.cutoffRegisters a).isNone = armPendingCheck l a := by
    simpa only [id_eq, beq_iff_eq] using hkA
  constructor
  · rw [← Option.isNone_iff_eq_none, ← Option.isNone_iff_eq_none, hcurr, hcut]
  · intro hnone
    have hpending : armPendingCheck l a = true := by rw [← hcurr, hnone]; rfl
    have hp : armPending l a := by
      unfold armPendingCheck anyFin at hpending
      rw [List.any_eq_true] at hpending
      simpa [armPending] using hpending
    obtain ⟨i, _hi, harm⟩ := hp
    exact ⟨i, harm⟩

/-- Queue values of an initially known current register on a successful checked
prefix equal the literal calendar replay whenever that checked prefix's local
record list is the corresponding numerical calendar word. -/
theorem checked_prefix_known_current_queue_replay
    (l : CoordinatorCollectionLedger.Ledger p eta heta hcap n hn)
    (a : Fin p.K)
    (current : CoordinatorCollectionLedger.CurrentRegister)
    (inputs : List (CollectionCheckedExecution.RoundInput (p := p) (eta := eta)))
    (A H : List (Bool × ℕ))
    (hknown : l.currentRegisters a = some current)
    (hincrement : l.increment a = 0)
    (hseed : current.queue = (QueueReplay.replay (4 * n) (0, 0) A).2)
    (hrecords : ∀ v, v ≤ inputs.length →
      CollectionKnownQueueContinuation.inputQueueRecords l a (inputs.take v) = H.take v)
    (v : ℕ) (hv : v ≤ inputs.length)
    (prefixAccepted : List Bool)
    (prefixFinal : CoordinatorCollectionLedger.Ledger p eta heta hcap n hn)
    (hfold : CollectionCheckedExecution.checkedRounds l (inputs.take v) =
      some (prefixAccepted, prefixFinal))
    (register : CoordinatorCollectionLedger.CurrentRegister)
    (hregister : prefixFinal.currentRegisters a = some register) :
    register.queue =
      (QueueReplay.replay (4 * n) (0, 0) (A ++ H.take v)).2 := by
  have hcontinuation :=
    CollectionKnownQueueContinuation.checkedRounds_known_queue_continuation
      l prefixFinal a current (inputs.take v) prefixAccepted hknown hfold
  have hcurrent := hcontinuation.1
  dsimp only [CollectionKnownQueueContinuation.inputQueueRecords] at hcurrent
  have hregEq : register =
      ⟨(QueueReplay.replay (4 * n) (l.increment a, current.queue)
          (CollectionKnownQueueContinuation.inputQueueRecords l a (inputs.take v))).2,
        CollectionKnownQueueContinuation.replayLastService (4 * n)
          (l.increment a, current.queue) current.lastService
          (CollectionKnownQueueContinuation.inputQueueRecords l a (inputs.take v))⟩ := by
    apply Option.some.inj
    exact hregister.symm.trans hcurrent
  have hrecordsV := hrecords v hv
  rw [hrecordsV] at hregEq
  have hqueue := congrArg CoordinatorCollectionLedger.CurrentRegister.queue hregEq
  change register.queue =
    (QueueReplay.replay (4 * n) (l.increment a, current.queue) (H.take v)).2 at hqueue
  rw [hqueue, hincrement, hseed]
  have happ := QueueReplay.replay_append (4 * n) (0, 0) A (H.take v)
  rw [happ]
  exact replay_backlog_independent_of_score (4 * n) 0
    (QueueReplay.replay (4 * n) (0, 0) A).1
    (QueueReplay.replay (4 * n) (0, 0) A).2 (H.take v)

/-- An initially known cutoff register is preserved on every successful
checked prefix; unknown cutoff registers are outside this implication. -/
theorem checked_prefix_known_cutoff_register_preserved
    (l prefixFinal : CoordinatorCollectionLedger.Ledger p eta heta hcap n hn)
    (a : Fin p.K) (current : CoordinatorCollectionLedger.CurrentRegister)
    (inputs : List (CollectionCheckedExecution.RoundInput (p := p) (eta := eta)))
    (accepted : List Bool) (v : ℕ)
    (hcurrent : l.currentRegisters a = some current)
    (hfold : CollectionCheckedExecution.checkedRounds l (inputs.take v) =
      some (accepted, prefixFinal)) :
    prefixFinal.cutoffRegisters a = l.cutoffRegisters a := by
  obtain ⟨_, _, _, _, _, _, hpreserved⟩ :=
    CollectionKnownQueueContinuation.checkedRounds_known_queue_continuation
      l prefixFinal a current (inputs.take v) accepted hcurrent hfold
  exact hpreserved

/-- The queue field of an initially known cutoff register keeps its original
calendar replay value on each successful checked prefix. -/
theorem checked_prefix_known_cutoff_queue_replay
    (l : CoordinatorCollectionLedger.Ledger p eta heta hcap n hn)
    (a : Fin p.K) (current : CoordinatorCollectionLedger.CurrentRegister)
    (cutoff : CoordinatorCollectionLedger.CutoffRegister)
    (inputs : List (CollectionCheckedExecution.RoundInput (p := p) (eta := eta)))
    (accepted : List Bool) (A : List (Bool × ℕ)) (v : ℕ)
    (hcurrent : l.currentRegisters a = some current)
    (hcutoff : l.cutoffRegisters a = some cutoff)
    (hseed : cutoff.queue = (QueueReplay.replay (4 * n) (0, 0) A).2)
    (prefixFinal : CoordinatorCollectionLedger.Ledger p eta heta hcap n hn)
    (hfold : CollectionCheckedExecution.checkedRounds l (inputs.take v) =
      some (accepted, prefixFinal))
    (register : CoordinatorCollectionLedger.CutoffRegister)
    (hregister : prefixFinal.cutoffRegisters a = some register) :
    register.queue = (QueueReplay.replay (4 * n) (0, 0) A).2 := by
  have hpreserved := checked_prefix_known_cutoff_register_preserved
    l prefixFinal a current inputs accepted v hcurrent hfold
  have hfinal : prefixFinal.cutoffRegisters a = some cutoff := by
    rw [hpreserved]
    exact hcutoff
  have heq : register = cutoff := Option.some.inj (hregister.symm.trans hfinal)
  rw [heq]
  exact hseed

/-- On the first corrected collection, every actually known current or
cutoff queue at every retained prefix equals replay on one original calendar.
The same `A,D` witness all prefixes and all arms. No terminal success, pending
emptiness, supplied UP, or queue-truth premise is used. -/
theorem firstCell_collection_known_queue_every_prefix_replay
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hz : z ∈ correctedCell rate rewards C_star C_h u t) :
    let R := sourceRecords rate rewards C_star C_h z
    let s := sourceStart rate rewards C_star C_h z
    let e := birthIndex rate rewards C_star C_h z + 1 + (liveTail rate rewards C_star C_h z).length
    let Q := ReferenceFirstLaunchNumericalCell.queueParameters rate
    ∀ (seg : Segment rate), segmentAt R e = some seg →
      ∃ (A D : List (RecordedQueueRun.RoundInput p.K)),
        A.length = e ∧ D.length = seg.records.length ∧
        prefixInputs rate rewards C_star C_h (s + e) z = some A ∧
        (∀ j : Fin seg.records.length, ∃ hD : j.val < D.length,
          ReferenceFirstCollectionCurrentRetainedGate.cell0 rate seg.records[j.val] = some (D[j.val]'hD)) ∧
        (∀ a v, (seg.records.take v).map
          (ReferenceCollectionRawBufferHistory.physicalQueueRecord seg.context.preLedger a) =
          (D.take v).map (fun d => (d.enabled, RecordedQueueRun.quantizedArrival Q d a))) ∧
        (∀ v, v ≤ D.length →
          let Gv := A ++ D.take v
          let lv := endpointLedger seg.context.preLedger (seg.records.take v)
          prefixInputs rate rewards C_star C_h (s + e + v) z = some Gv ∧
          (∀ a current, lv.currentRegisters a = some current →
            current.queue = (UnstoppedRecordedQueueComparison.unstoppedReplay Q Gv Gv.length a).2) ∧
          (∀ a cutoff, lv.cutoffRegisters a = some cutoff →
            cutoff.queue = (UnstoppedRecordedQueueComparison.unstoppedReplay Q A A.length a).2)) := by
  classical
  intro R s e Q seg hseg
  have he : e < R.length := by
    by_contra hn
    have hnil : R.drop e = [] := List.drop_eq_nil_iff.mpr (by omega)
    have hb := (segmentAt_branch R e seg hseg).1
    rw [hnil] at hb
    contradiction
  obtain ⟨L, B, c, birth, payload, segW, D, _hL, _hprefixBirth, _hLb,
    _hdateBirth, _hb, _hborn, _hsigma, _hlater, hsegW, hentry, _hpay, hcut,
    _hcutDate, hAlen, _heR, hprefixA, hDlen, hDcells, hDwords, hIwords,
    _hGT, _hprefixG, hGwords, hprefixes⟩ :=
    firstCell_actual_segment_prefix_words rate rewards C_star C_h u t z hz he
  have hsegEq : segW = seg := Option.some.inj (hsegW.symm.trans hseg)
  subst segW
  let A := (L ++ [c]) ++ B
  change A.length = e at hAlen
  change prefixInputs rate rewards C_star C_h (s + e) z = some A at hprefixA
  have hentrySource : R[e]? = some seg.entry := by
    rw [hentry]
    exact List.getElem?_eq_getElem he
  have hseed := firstCell_initial_known_queue_seed rate rewards C_star C_h u t z hz seg hseg A
    (by simpa only [s, e, Nat.add_assoc] using hprefixA)
  refine ⟨A, D, hAlen, hDlen, hprefixA, hDcells, hDwords, ?_⟩
  intro v hv
  dsimp only
  let lv := endpointLedger seg.context.preLedger (seg.records.take v)
  have hvR : v ≤ seg.records.length := by omega
  obtain ⟨I, accepted, _hI, hstartI, hchecked⟩ :=
    actual_segment_prefix_execution rate rewards C_star C_h z e seg hseg v hvR
  obtain ⟨acceptedV, hstartV, hfold⟩ :=
    CollectionBufferProvenance.startAndRunChecked_success_components
      I.assignment I.sigma I.cutoff I.freezeAt I.base I.outside (seg.inputs.take v)
      ⟨seg.context.preLedger, accepted, lv⟩ hchecked
  have hvalidI := startCollectionChecked_success_valid I.assignment I.sigma I.cutoff
    I.freezeAt I.base I.outside seg.context.preLedger hstartV
  have hvalidV := checkedRounds_success_valid seg.context.preLedger lv
    (seg.inputs.take v) acceptedV hvalidI hfold
  have htakeA : (A ++ D).take e = A := by rw [← hAlen, List.take_left]
  have htakeG : (A ++ D).take (e + v) = A ++ D.take v := by
    rw [List.take_append, List.take_of_length_le (by omega), hAlen, Nat.add_sub_cancel_left]
  have hvalues (a : Fin p.K) :
      (∀ current, lv.currentRegisters a = some current →
        current.queue = (UnstoppedRecordedQueueComparison.unstoppedReplay Q
          (A ++ D.take v) (A ++ D.take v).length a).2) ∧
      (∀ cutoff, lv.cutoffRegisters a = some cutoff →
        cutoff.queue = (UnstoppedRecordedQueueComparison.unstoppedReplay Q A A.length a).2) := by
    let raw := fun xs : List (RecordedQueueRun.RoundInput p.K) => xs.map
      (fun d => (d.enabled, RecordedQueueRun.quantizedArrival Q d a))
    have hrawA : A.map (fun d => UnstoppedRecordedQueueComparison.unstoppedRecord Q d a) = raw A := by
      have hh := hGwords a e
      change ((A ++ D).take e).map
        (fun d => UnstoppedRecordedQueueComparison.unstoppedRecord Q d a) = raw ((A ++ D).take e) at hh
      rw [htakeA] at hh
      exact hh
    have hrawG : (A ++ D.take v).map
        (fun d => UnstoppedRecordedQueueComparison.unstoppedRecord Q d a) = raw (A ++ D.take v) := by
      have hh := hGwords a (e + v)
      change ((A ++ D).take (e + v)).map
        (fun d => UnstoppedRecordedQueueComparison.unstoppedRecord Q d a) = raw ((A ++ D).take (e + v)) at hh
      rw [htakeG] at hh
      exact hh
    have hseedRaw : (UnstoppedRecordedQueueComparison.unstoppedReplay Q A A.length a).2 =
        (QueueReplay.replay (4 * rate.n) (0, 0) (raw A)).2 := by
      unfold UnstoppedRecordedQueueComparison.unstoppedReplay
      rw [List.take_length, hrawA]
      rfl
    have hjoin (q : ℕ)
        (hq : q = (UnstoppedRecordedQueueComparison.unstoppedReplay Q A A.length a).2) :
        (QueueReplay.replay (4 * rate.n) (0, q) (raw (D.take v))).2 =
        (UnstoppedRecordedQueueComparison.unstoppedReplay Q
          (A ++ D.take v) (A ++ D.take v).length a).2 := by
      rw [hq, hseedRaw, UnstoppedRecordedQueueComparison.unstoppedReplay,
        List.take_length, hrawG]
      change _ = (QueueReplay.replay (4 * rate.n) (0, 0) (raw (A ++ D.take v))).2
      rw [show raw (A ++ D.take v) = raw A ++ raw (D.take v) from List.map_append,
        QueueReplay.replay_append]
      exact replay_backlog_independent_of_score (4 * rate.n) 0
        (QueueReplay.replay (4 * rate.n) (0, 0) (raw A)).1
        (QueueReplay.replay (4 * rate.n) (0, 0) (raw A)).2 (raw (D.take v))
    cases hi : seg.context.preLedger.currentRegisters a with
    | some initialCurrent =>
      obtain ⟨hcurrent, _hinc, _hassign, _hsigma, _hcutoffDate, _hfreeze, hcutoff⟩ :=
        CollectionKnownQueueContinuation.checkedRounds_known_queue_continuation
          seg.context.preLedger lv a initialCurrent (seg.inputs.take v) acceptedV hi hfold
      constructor
      · intro current hc
        have hq := congrArg CurrentRegister.queue (Option.some.inj (hc.symm.trans hcurrent))
        change current.queue = (QueueReplay.replay (4 * rate.n)
          (seg.context.preLedger.increment a, initialCurrent.queue)
          (CollectionKnownQueueContinuation.inputQueueRecords seg.context.preLedger a
            (seg.inputs.take v))).2 at hq
        rw [(hseed a).2.2, hIwords a v] at hq
        exact hq.trans (hjoin initialCurrent.queue ((hseed a).1 initialCurrent hi))
      · intro cutoff hc
        exact (hseed a).2.1 cutoff (hcutoff.symm.trans hc)
    | none =>
      obtain ⟨i, harm⟩ := (valid_register_options seg.context.preLedger hvalidI a).2 hi
      have assigned (current : CurrentRegister) (hc : lv.currentRegisters a = some current) :
          current.queue = (UnstoppedRecordedQueueComparison.unstoppedReplay Q
            (A ++ D.take v) (A ++ D.take v).length a).2 ∧
          (∀ cutoff, lv.cutoffRegisters a = some cutoff → cutoff.queue =
            (UnstoppedRecordedQueueComparison.unstoppedReplay Q A A.length a).2) := by
        obtain ⟨j, hj, M, _hjv, _hacc, hzero, hcurrent, hcutoff⟩ :=
          actual_segment_known_assigned_prefix_accepted rate rewards C_star C_h z e seg hseg
            v hvR i current (by rw [harm]; exact hc)
        rw [harm] at hzero hcurrent hcutoff
        have hM := firstCell_zero_observer_seed rate rewards C_star C_h u t z hz seg hseg
          hentrySource hcut j hj a M.val.q hzero A hprefixA
        rw [hIwords a v] at hcurrent
        exact ⟨hcurrent.trans (hjoin M.val.q hM), fun cutoff hk => (hcutoff cutoff hk).trans hM⟩
      constructor
      · intro current hc
        exact (assigned current hc).1
      · intro cutoff hk
        cases hc : lv.currentRegisters a with
        | none =>
          have hn := (valid_register_options lv hvalidV a).1.mp hc
          rw [hn] at hk
          contradiction
        | some current => exact (assigned current hc).2 cutoff hk
  refine ⟨hprefixes v hv, ?_, ?_⟩
  · intro a current hc
    exact (hvalues a).1 current hc
  · intro a cutoff hc
    exact (hvalues a).2 cutoff hc

end Bandits.Support.ReferenceFirstCorrectedCollectionKnownQueuePrefixReplay

end
