/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionCurrentRetainedMoments

import Mathlib.Tactic

/-!
# Physical reconstruction at the original first collection invocation

Sources: `04_slow_fast_learner.tex:140-188`, `06_interruptions.tex:355-426`,
and `appendix_a_local_protocol.tex:28-64` in `sources/zip4/manuscript/`.

The actual incoming ledger and its canonical next dispatch are produced from
the original first-call event. Finite record lookup and the first empty pending
boundary identify their numerical stream with the gate's complete dated prefix.
The numerical next-start producer is used for its FINISH register equations;
the actual dispatch's own literal operation ledger and register certificates
then identify its reconstruction. No equality of dispatch witnesses is needed.

Physical scores and queues agree with UNSTOPPED replay on the entire first-call
event. Agreement with the stopped numerical run is asserted only on the
strict-past retained test. These internal results do not establish a coupling,
an anchor band, a sampling outcome, or a manuscript theorem.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ReferenceFirstCollectionCurrentReplayReconstruction

open ReferenceCollectionSegmentExtraction
open ReferenceFirstCollectionStreamEmptyDispatch
open ActualInitializationPhysicalStep (GridRewardTable)
open ReferenceFirstLaunchNumericalCell (queueParameters)
open ReferenceCalendarCollectionCallControlLaw (firstCell)
open ReferenceFirstCollectionCurrentRetainedGate (pastCells? H G)
open UnstoppedRecordedQueueComparison (unstoppedReplay)

variable {p : ConstructorDimensions.Parameters}

section Alignment

variable {rate : ReferenceActivePhysicalStep.RateInput p}
    {source : BootstrapPrivateRoundStreams.SourceInput p} {rewards : GridRewardTable p}
    {C_star C_h : ℝ} {count : ℕ}
    {hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true}
    {hspan : ReferenceFirstCollectionReadyStream.startTime (rate := rate)
      source rewards C_star C_h + count ≤ p.T}
    {hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
        source rewards C_star C_h hcross count hspan).records).length < count}

private theorem same_stream_output
    (f g : ReferenceFirstCollectionReadyStream.ActualInitializedStreamOutput
      source rewards C_star C_h count hcross hspan hshort)
    (i : Fin f.ell) (j : Fin g.ell) (hij : i.val = j.val) :
    f.payload = g.payload ∧ f.ledgers i = g.ledgers j ∧ f.saved = g.saved := by
  obtain ⟨r, hr, _, hc, _⟩ := f.output_properties i
  obtain ⟨r', hr', _, hc', _⟩ := g.output_properties j
  have hw : f.window = g.window := f.windowIsActual.trans g.windowIsActual.symm
  rw [hw, hij, hr'] at hr
  have he : r = r' := Option.some.inj hr.symm
  rw [he] at hc
  exact ReferenceActivePhysicalStep.CoordinatorConfiguration.collection.inj (hc.symm.trans hc')

/-- First empty pending is unique on this actual finite window, including the
alternative where another produced stream exhausts the window. -/
private theorem first_empty_alignment
    (f g : ActualInitializedStreamDispatch
      source rewards C_star C_h count hcross hspan hshort)
    (hf : f.ledger.pending = ∅) :
    g.stream.ell = f.stream.ell ∧ g.record = f.record ∧
      g.stream.payload = f.stream.payload ∧ g.ledger = f.ledger ∧
      g.stream.saved = f.stream.saved := by
  have hw : f.stream.window = g.stream.window :=
    f.stream.windowIsActual.trans g.stream.windowIsActual.symm
  have hlength : g.stream.ell = f.stream.ell := by
    apply Nat.le_antisymm
    · by_contra hnot
      have hlt : f.stream.ell < g.stream.ell := by omega
      let j : Fin g.stream.ell := ⟨f.last.val, by have h := f.lastIsLast; omega⟩
      have heq := (same_stream_output f.stream g.stream f.last j rfl).2.1
      have hn := g.allEarlierNonempty j (by
        have h := f.lastIsLast
        change f.last.val + 1 < g.stream.ell
        omega)
      rw [← heq, ← f.ledgerIsLast, hf] at hn
      exact Finset.not_nonempty_empty hn
    · by_contra hnot
      have hlt : g.stream.ell < f.stream.ell := by omega
      cases g.outcome with
      | exhausted _ hex _ _ _ =>
          have hfwindow := f.stream.withinWindow
          rw [hw, ← hex] at hfwindow
          omega
      | empty e =>
          let i : Fin f.stream.ell := ⟨g.last.val, by have h := g.lastIsLast; omega⟩
          have heq := (same_stream_output f.stream g.stream i g.last rfl).2.1
          have hn := f.allEarlierNonempty i (by
            have h := g.lastIsLast
            change g.last.val + 1 < f.stream.ell
            omega)
          rw [heq, ← g.ledgerIsLast, e.pendingEmpty] at hn
          exact Finset.not_nonempty_empty hn
  have hlast : g.last.val = f.last.val := by
    have hg := g.lastIsLast
    have hf := f.lastIsLast
    omega
  have hrecord : g.record = f.record := by
    have hr := g.recordAt
    rw [← hw, hlast, f.recordAt] at hr
    exact Option.some.inj hr.symm
  obtain ⟨hp, hl, hs⟩ := same_stream_output g.stream f.stream g.last f.last hlast
  exact ⟨hlength, hrecord, hp, g.ledgerIsLast.trans (hl.trans f.ledgerIsLast.symm), hs⟩

end Alignment

variable (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : GridRewardTable p) (C_star C_h : ℝ)

private theorem collection_readout_zero (s : ℕ)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (cell : RecordedQueueRun.RoundInput p.K)
    (hread : ReferenceLaterCollectionArrivalReadout.laterCollectionReadout s record = some cell) :
    ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 record = some cell := by
  have hp : (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout s record).isSome = true := by
    rw [hread]
    rfl
  obtain ⟨hf, hb⟩ :=
    (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout_domain s record).mp hp
  cases hcoord : record.output.preparation.coordinator with
  | collection payload ledger clock cutoff outcome =>
      cases outcome with
      | continuing core snapshot boundary scores =>
          simpa only [ReferenceLaterCollectionArrivalReadout.laterCollectionReadout,
            dite_eq_left hf, hcoord] using hread
      | _ => simp only [hcoord] at hb
  | live registers owned base outcome =>
      cases outcome with
      | cutoffChosen dispatched hstart ledger hinit hcand hdomain hclock hpending hnone selected =>
          have hg : s < registers.payload.sigma.val := by simpa only [hcoord] using hb
          have hg0 : 0 < registers.payload.sigma.val := by omega
          simpa only [ReferenceLaterCollectionArrivalReadout.laterCollectionReadout,
            dite_eq_left hf, hcoord, hg, hg0, ite_true] using hread
      | _ => simp only [hcoord] at hb
  | first outcome => cases outcome <;> simp only [hcoord] at hb
  | invalidCollectionCutoff => simp only [hcoord] at hb
  | dagger => simp only [hcoord] at hb

/-- The cutoff head is a genuine numerical readout too; it is never discarded
when aligning the two lists. -/
private theorem cutoff_readout_zero (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true)
    (hs : ReferenceFirstCollectionReadyStream.startTime
      (rate := rate) z rewards C_star C_h +
        (p.T - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h) ≤ p.T)
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate) z rewards C_star C_h
        hc (p.T - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h) hs).records).length <
          p.T - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
    (out : ReferenceFirstCollectionReadyStream.ActualInitializedStreamOutput
      (rate := rate) z rewards C_star C_h
      (p.T - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h) hc hs hshort)
    (head : Choice rate)
    (valid : CoordinatorRecorderComplementBridge.LocalInputsValid
      (ReferenceActivePhysicalStep.collectionRecordingInput out.cutoff.cut.output.preparation
        head.payload head.started head.weights))
    (hhead : choice out.cutoff.cut.input = some head) :
    ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 out.cutoff.cut =
      some (ReferenceFirstCollectionCheckedSourcePrefix.sourceCell
        rate out.cutoff.cut head rewards valid) := by
  obtain ⟨_, _, d, _, _, _, D, _, _, _, _, hDlen, _, hcells⟩ :=
    ReferenceCompleteFirstPhaseObservationRecovery.actualFirstCollectionRawObservationIdentity
      rate rewards C_star C_h z hc hshort
  let zero : Fin d.stream.ell := ⟨0, by have h := d.stream.positiveLength; omega⟩
  obtain ⟨call, validCall, hcall, _, _, hcell, _, _, _, _, _, _, _, _, hread, _⟩ :=
    hcells zero
  have hd := (d.stream.alignment
    ⟨0, lt_of_lt_of_le zero.isLt d.stream.withinWindow⟩).1
  have ho := (out.alignment ⟨0, out.windowNonempty⟩).1
  simp only [Nat.add_zero] at hd ho
  rw [out.cutoffIsHead] at ho
  have he : d.stream.window[0]'(by have h := d.stream.windowNonempty; omega) =
      out.cutoff.cut := Option.some.inj (hd.symm.trans ho)
  dsimp only [zero] at hcall hcell hread
  rw [he] at hcall hcell hread
  have hchoice : call = head := Option.some.inj (hcall.symm.trans hhead)
  subst call
  rw [hcell] at hread
  exact hread

/-- Disabled records preserve registers regardless of their unused numerical
arrival. Enabled zero arrivals retain their service step. -/
private theorem replay_arrivals (cells : List (RecordedQueueRun.RoundInput p.K))
    (a : Fin p.K) (initial : ℕ × ℕ) :
    QueueReplay.replay (4 * rate.n) initial
      (ReferenceFirstCollectionAllArmNumericalStream.arrivals rate a cells) =
    QueueReplay.replay (4 * rate.n) initial
      (cells.map fun c => UnstoppedRecordedQueueComparison.unstoppedRecord
        (queueParameters rate) c a) := by
  induction cells generalizing initial with
  | nil => rfl
  | cons c cells ih =>
      change QueueReplay.replay (4 * rate.n)
          (QueueReplay.transition (4 * rate.n) initial
            (c.enabled, RecordedQueueRun.quantizedArrival (queueParameters rate) c a))
          (ReferenceFirstCollectionAllArmNumericalStream.arrivals rate a cells) =
        QueueReplay.replay (4 * rate.n)
          (QueueReplay.transition (4 * rate.n) initial
            (UnstoppedRecordedQueueComparison.unstoppedRecord (queueParameters rate) c a))
          (cells.map fun c => UnstoppedRecordedQueueComparison.unstoppedRecord
            (queueParameters rate) c a)
      rw [ih]
      congr 1
      cases he : c.enabled <;>
        simp only [UnstoppedRecordedQueueComparison.unstoppedRecord, he,
          Bool.false_eq_true, ite_false, ite_true, QueueReplay.transition]

private theorem unstopped_eq_arrivals (cells : List (RecordedQueueRun.RoundInput p.K))
    (n : ℕ) (a : Fin p.K) :
    unstoppedReplay (queueParameters rate) cells n a =
      QueueReplay.replay (4 * rate.n) (0, 0)
        (ReferenceFirstCollectionAllArmNumericalStream.arrivals rate a (cells.take n)) :=
  (replay_arrivals rate (cells.take n) a (0, 0)).symm

private theorem stopped_eq_unstopped_on_H (t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (L : List (RecordedQueueRun.RoundInput p.K))
    (hL : pastCells? rate rewards C_star C_h t z = some L)
    (hH : z ∈ H rate rewards C_star C_h t) :
    ∀ a, (RecordedQueueRun.run (queueParameters rate) L).registers a =
      unstoppedReplay (queueParameters rate) L L.length a := by
  obtain ⟨v, hv, hfalse⟩ := hH
  have hv' : ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
      (RecordedQueueRun.run (queueParameters rate) L) = v := by
    apply Option.some.inj
    simpa only [ReferenceFirstCollectionCurrentRetainedGate.prefixReadout?, hL,
      Option.map_some] using hv
  have hflag : (RecordedQueueRun.run (queueParameters rate) L).overflow = false := by
    rw [← hv'] at hfalse
    exact hfalse
  have hcmp := UnstoppedRecordedQueueComparison.prefix_state_comparison
    (queueParameters rate) L L.length (Nat.le_refl _)
  simp only [List.take_length] at hcmp
  have hbefore : L.length <
      UnstoppedRecordedQueueComparison.firstOverflowPrefix (queueParameters rate) L := by
    by_contra hn
    have htrue := hcmp.2.mpr (Nat.le_of_not_gt hn)
    rw [hflag] at htrue
    cases htrue
  simpa only [Nat.min_eq_left (Nat.le_of_lt hbefore)] using hcmp.1

/-- At the original first collection invocation, the physical reconstruction
is the unstopped replay of the gate's SAME original numerical prefix. The
stopped comparison is a separate conclusion conditional on `H`. -/
theorem firstCell_reconstruction (u t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hz : z ∈ firstCell rate rewards C_star C_h u t) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
    ∃ (L : List (RecordedQueueRun.RoundInput p.K)) (n : ℕ)
      (r : ReferenceFirstCollectionSamplerCall.RoundRecord p rate)
      (theta : ReferenceFirstCollectionSamplerCall.Theta p)
      (old : ReferenceActivePhysicalStep.Payload rate)
      (ledger : ReferenceActivePhysicalStep.Ledger rate)
      (saved : Option (Fin p.T × Bool))
      (previous : ReferenceFirstCollectionSamplerCall.RoundRecord p rate),
      pastCells? rate rewards C_star C_h t z = some L ∧
      L.length = t.val - s ∧ s ≤ u.val ∧ u.val < t.val ∧ s + n = t.val ∧
      R[n]? = some r ∧ r.input.time = t ∧
      ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some r ∧
      ReferenceFirstCollectionSamplerCall.collectionCallAt r = some (u, theta) ∧
      ReferenceCalendarLaterSamplerPredictability.calendarParameters
        rate rewards C_star C_h t z = some theta ∧
      ReferenceLaterSamplerParameterMeasurability.parameters? r.input = some theta ∧
      r.input.rows = z.1.2 ∧
      r.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p z ∧
      r.input.rewards = rewards ∧
      (∀ j < n, ∀ q, R[j]? = some q →
        ReferenceLaterSamplerParameterMeasurability.parameters? q.input = none) ∧
      R[n - 1]? = some previous ∧ r.input.state = previous.output.next ∧
      r.input.state.coordinator = .collection old ledger saved ∧
      ledger.cutoff = u.val + 1 ∧ ledger.cursor = t.val + 1 ∧ ledger.pending = ∅ ∧
      ∃ k : ActualNextDispatch r.input old ledger saved,
        k.operationLedger = CoordinatorRoundDispatch.collectionOperationLedger
          (ReferenceActivePhysicalStep.collectionInput r.input old ledger
            (ReferenceActivePhysicalStep.collectionClock old ledger saved k.cutoffTime)
            k.cutoffTime) k.core.payload_n_eq ∧
        k.cutoffTime = u ∧ k.instruction.time = t ∧
        k.operationLedger.cutoffRegisters = ledger.cutoffRegisters ∧
        k.operationLedger.currentRegisters = ledger.currentRegisters ∧
        k.operationLedger.increment = ledger.increment ∧
        AssignmentScoreReconstruction.reconstructLaterStart k.operationLedger k.instruction =
          .success k.operationLedger k.instruction k.reconstructed ∧
        (∀ a, ledger.cutoffRegisters a = some (k.reconstructed.registers.cutoff a) ∧
          ledger.currentRegisters a = some (k.reconstructed.registers.current a)) ∧
        let replay := unstoppedReplay (queueParameters rate) L
        (∀ a : Fin p.K,
          ledger.cutoffRegisters a = some
            ⟨(replay (u.val - s) a).1, (replay (u.val - s) a).2,
              (replay (u.val - s) a).1 - (replay (u.val - s - 1) a).1⟩ ∧
          ledger.currentRegisters a = some
            ⟨(replay L.length a).2,
              (replay L.length a).1 - (replay (L.length - 1) a).1⟩ ∧
          k.reconstructed.registers.cutoff a =
            ⟨(replay (u.val - s) a).1, (replay (u.val - s) a).2,
              (replay (u.val - s) a).1 - (replay (u.val - s - 1) a).1⟩ ∧
          k.reconstructed.registers.current a =
            ⟨(replay L.length a).2,
              (replay L.length a).1 - (replay (L.length - 1) a).1⟩ ∧
          AssignmentScoreReconstruction.sourceScore k.reconstructed a = (replay L.length a).1 ∧
          AssignmentScoreReconstruction.initialQueue k.reconstructed a = (replay L.length a).2 ∧
          AssignmentScoreReconstruction.currentWeight k.reconstructed a =
            (1 + 1 / (ConstructorDimensions.D p : ℝ)) ^ (replay L.length a).1) ∧
        (z ∈ H rate rewards C_star C_h t → ∀ a : Fin p.K,
          AssignmentScoreReconstruction.sourceScore k.reconstructed a =
            ((RecordedQueueRun.run (queueParameters rate) L).registers a).1 ∧
          AssignmentScoreReconstruction.initialQueue k.reconstructed a =
            ((RecordedQueueRun.run (queueParameters rate) L).registers a).2 ∧
          AssignmentScoreReconstruction.currentWeight k.reconstructed a =
            RecordedQueueRun.scoreWeight (queueParameters rate)
              (RecordedQueueRun.run (queueParameters rate) L) a) := by
  classical
  dsimp only
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  let count := p.T - s
  let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
  obtain ⟨n, r, theta, hr, ht, hactual, hcall, hrows, hselected, hrewards,
    hearlier, htime, hc, hs, hrecords, hk, f, e, _hf, hu, hn,
    hprevious, hstate, hcoord, hcutoff, hcursor, hempty, _hknown, _hservice,
    _hincrement, k, hliteral, hkcut, hktime⟩ :=
    ReferenceFirstCollectionCallStoredBounds.firstCell_stored_bounds
      rate rewards C_star C_h u t z hz
  obtain ⟨_, _, _, _, _, hparameters⟩ :=
    (ReferenceFirstCollectionSamplerCall.collectionCallAt_spec r u theta).mp hcall
  have hcalendar : ReferenceCalendarLaterSamplerPredictability.calendarParameters
      rate rewards C_star C_h t z = some theta := by
    simp only [ReferenceCalendarLaterSamplerPredictability.calendarParameters,
      hactual, Option.bind_some]
    exact hparameters
  obtain ⟨_hcGate, _hsGate, _hshortGate, b, _headGate, _validGate, B, L,
    hsCut, hcutNext, _huGate, _htimeGate, hbempty, _hpreviousGate, _hheadGate,
    hBlen, _hBzero, hBread, hLsplit, hL, hLlen, _hcoverage⟩ :=
    ReferenceFirstCollectionCurrentRetainedGate.firstCell_prefix_coverage
      rate rewards C_star C_h u t z hz
  obtain ⟨g, head, _initializer, valid, D, hhead, _hpay, _hinit, _hchecked,
    hDlen, hDzero, hcells, _hprefix, _hrecordsNum, hendpoint, _hpre,
    _hboundary⟩ :=
    ReferenceFirstCollectionNumericalStartReconstruction.actual_first_collection_numerical_next_start_reconstruction
      rate z rewards C_star C_h count hc hs _
  obtain ⟨hglen, _hgrecord, _hgpay, hgledger, _hgsaved⟩ :=
    first_empty_alignment f g hempty
  obtain ⟨hblen, _hbrecord, _hbpay, _hbledger, _hbsaved⟩ :=
    first_empty_alignment f b hempty
  have hgempty : g.ledger.pending = ∅ := by rw [hgledger]; exact hempty
  have hnum := hendpoint hgempty
  rw [hgledger] at hnum
  have hheadRead := cutoff_readout_zero rate rewards C_star C_h z hc hs _
    g.stream head valid hhead
  have hDread (i : Fin g.stream.ell) :
      ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0
        (g.stream.window[i.val]'(lt_of_lt_of_le i.isLt g.stream.withinWindow)) =
          some (D[i.val]'(by omega)) := by
    by_cases hi : i.val = 0
    · simpa only [hi, g.stream.cutoffIsHead, hDzero] using hheadRead
    · obtain ⟨_call, _validCall, _hchoice, _hp, _hcontext, _hcell, _hrows,
        _hselected, _hrewards, _hdate, _henabled, _hreward, _hrate,
        _hphysical, hread⟩ := hcells i
      exact collection_readout_zero rate _ _ _ (hread (by omega))
  have hwindow : g.stream.window = b.stream.window :=
    g.stream.windowIsActual.trans b.stream.windowIsActual.symm
  have hDB : D = B := by
    apply List.ext_getElem (by omega)
    intro i hi hi'
    let gi : Fin g.stream.ell := ⟨i, by omega⟩
    let bi : Fin b.stream.ell := ⟨i, by omega⟩
    have hd := hDread gi
    have hb := hBread bi
    rw [List.getElem?_eq_getElem hi'] at hb
    have hrecord :
        g.stream.window[gi.val]'(lt_of_lt_of_le gi.isLt g.stream.withinWindow) =
          b.stream.window[bi.val]'(lt_of_lt_of_le bi.isLt b.stream.withinWindow) := by
      apply Option.some.inj
      exact (List.getElem?_eq_getElem _).symm.trans
        ((congrArg (fun xs => xs[i]?) hwindow).trans (List.getElem?_eq_getElem _))
    rw [hrecord] at hd
    exact Option.some.inj (hd.symm.trans hb)
  let Cells := ReferenceFirstWindowNumericalStream.actualLiveSourceCells
    rate z rewards C_star C_h hc count hs
  have hsplit : L = Cells ++ D := by
    simpa only [← hDB] using hLsplit
  have hCellsLen : Cells.length = w := by
    have hlen := ReferenceFirstWindowNumericalStream.actualLiveSourceCells_length
      rate z rewards C_star C_h hc count hs
    unfold ReferenceFirstWindowNumericalStream.actualFirstLiveWindow at hlen
    have hepoch := ReferenceCompleteFirstPhaseObservationRecovery.completeSuffixRecords_eq_actualFirstLiveRun
      rate rewards C_star C_h z hc
    rw [← hepoch] at hlen
    exact hlen
  have hwindowLen : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
        z rewards C_star C_h hc count hs).records).length = w := by
    exact congrArg (fun records =>
      (ReferenceFirstLiveConfirmationHistory.firstLiveWindow records).length) hrecords.symm
  have hcutIndex : u.val - s = Cells.length := by
    change u.val = s + w at hu
    omega
  have htakeCut : L.take (u.val - s) = Cells := by
    rw [hsplit, hcutIndex, List.take_append_of_le_length (Nat.le_refl _), List.take_length]
  have htakePre : L.take (u.val - s - 1) = Cells.take (w - 1) := by
    rw [hsplit, List.take_append_of_le_length (by omega), hcutIndex, hCellsLen]
  have hDpos : 0 < D.length := by
    rw [hDlen]
    exact g.stream.positiveLength
  have htakeLast : L.take (L.length - 1) = Cells ++ D.take (D.length - 1) := by
    have hlen : L.length = Cells.length + D.length := by rw [hsplit, List.length_append]
    have hi : L.length - 1 = Cells.length + (D.length - 1) := by omega
    rw [hi, hsplit, List.take_append, List.take_of_length_le (by omega), Nat.add_sub_cancel_left]
  have hV (a : Fin p.K) : QueueReplay.replay (4 * rate.n) (0, 0)
      (ReferenceFirstCollectionAllArmNumericalStream.arrivals rate a Cells) =
        unstoppedReplay (queueParameters rate) L (u.val - s) a := by
    rw [unstopped_eq_arrivals, htakeCut]
  have hVpre (a : Fin p.K) : QueueReplay.replay (4 * rate.n) (0, 0)
      (ReferenceFirstCollectionAllArmNumericalStream.arrivals rate a (Cells.take (w - 1))) =
        unstoppedReplay (queueParameters rate) L (u.val - s - 1) a := by
    rw [unstopped_eq_arrivals, htakePre]
  have hWhole (a : Fin p.K) : QueueReplay.replay (4 * rate.n) (0, 0)
      (ReferenceFirstCollectionAllArmNumericalStream.arrivals rate a (Cells ++ D)) =
        unstoppedReplay (queueParameters rate) L L.length a := by
    rw [unstopped_eq_arrivals, List.take_length, hsplit]
  have hLast (a : Fin p.K) : QueueReplay.replay (4 * rate.n) (0, 0)
      (ReferenceFirstCollectionAllArmNumericalStream.arrivals rate a
        (Cells ++ D.take (D.length - 1))) =
          unstoppedReplay (queueParameters rate) L (L.length - 1) a := by
    rw [unstopped_eq_arrivals, htakeLast]
  let replay := unstoppedReplay (queueParameters rate) L
  have hcutNum (a : Fin p.K) : f.ledger.cutoffRegisters a = some
      ⟨(replay (u.val - s) a).1, (replay (u.val - s) a).2,
        (replay (u.val - s) a).1 - (replay (u.val - s - 1) a).1⟩ := by
    have ha := (hnum a).1
    dsimp only at ha
    rw [hwindowLen] at ha
    change f.ledger.cutoffRegisters a = some
      ⟨(QueueReplay.replay (4 * rate.n) (0, 0)
          (ReferenceFirstCollectionAllArmNumericalStream.arrivals rate a Cells)).1,
        (QueueReplay.replay (4 * rate.n) (0, 0)
          (ReferenceFirstCollectionAllArmNumericalStream.arrivals rate a Cells)).2,
        (QueueReplay.replay (4 * rate.n) (0, 0)
          (ReferenceFirstCollectionAllArmNumericalStream.arrivals rate a Cells)).1 -
        (QueueReplay.replay (4 * rate.n) (0, 0)
          (ReferenceFirstCollectionAllArmNumericalStream.arrivals rate a (Cells.take (w - 1)))).1⟩ at ha
    rw [hV a, hVpre a] at ha
    exact ha
  have hcurNum (a : Fin p.K) : f.ledger.currentRegisters a = some
      ⟨(replay L.length a).2, (replay L.length a).1 - (replay (L.length - 1) a).1⟩ := by
    have ha := (hnum a).2.1
    change f.ledger.currentRegisters a = some
      ⟨(QueueReplay.replay (4 * rate.n) (0, 0)
          (ReferenceFirstCollectionAllArmNumericalStream.arrivals rate a (Cells ++ D))).2,
        (QueueReplay.replay (4 * rate.n) (0, 0)
          (ReferenceFirstCollectionAllArmNumericalStream.arrivals rate a (Cells ++ D.take g.stream.ell))).1 -
        (QueueReplay.replay (4 * rate.n) (0, 0)
          (ReferenceFirstCollectionAllArmNumericalStream.arrivals rate a
            (Cells ++ D.take (g.stream.ell - 1)))).1⟩ at ha
    rw [← hDlen, List.take_length, hWhole a, hLast a] at ha
    exact ha
  have hsum (a : Fin p.K) : (replay (u.val - s) a).1 + f.ledger.increment a =
      (replay L.length a).1 := by
    have ha := (hnum a).2.2.2
    change (QueueReplay.replay (4 * rate.n) (0, 0)
        (ReferenceFirstCollectionAllArmNumericalStream.arrivals rate a Cells)).1 +
      f.ledger.increment a =
        (QueueReplay.replay (4 * rate.n) (0, 0)
          (ReferenceFirstCollectionAllArmNumericalStream.arrivals rate a (Cells ++ D))).1 at ha
    rw [hV a, hWhole a] at ha
    exact ha
  have hopCut : k.operationLedger.cutoffRegisters = f.ledger.cutoffRegisters := by
    rw [hliteral]
    rfl
  have hopCur : k.operationLedger.currentRegisters = f.ledger.currentRegisters := by
    rw [hliteral]
    rfl
  have hopInc : k.operationLedger.increment = f.ledger.increment := by
    rw [hliteral]
    rfl
  have hcutStored (a : Fin p.K) : f.ledger.cutoffRegisters a =
      some (k.reconstructed.registers.cutoff a) := by
    rw [← hopCut]
    exact k.reconstructed.registers.cutoff_eq a
  have hcurStored (a : Fin p.K) : f.ledger.currentRegisters a =
      some (k.reconstructed.registers.current a) := by
    rw [← hopCur]
    exact k.reconstructed.registers.current_eq a
  have hcutValue (a : Fin p.K) : k.reconstructed.registers.cutoff a =
      ⟨(replay (u.val - s) a).1, (replay (u.val - s) a).2,
        (replay (u.val - s) a).1 - (replay (u.val - s - 1) a).1⟩ :=
    Option.some.inj ((hcutStored a).symm.trans (hcutNum a))
  have hcurValue (a : Fin p.K) : k.reconstructed.registers.current a =
      ⟨(replay L.length a).2, (replay L.length a).1 - (replay (L.length - 1) a).1⟩ :=
    Option.some.inj ((hcurStored a).symm.trans (hcurNum a))
  have hscore (a : Fin p.K) : AssignmentScoreReconstruction.sourceScore k.reconstructed a =
      (replay L.length a).1 := by
    change (k.reconstructed.registers.cutoff a).score + k.operationLedger.increment a = _
    rw [hcutValue a, hopInc]
    exact hsum a
  have hqueue (a : Fin p.K) : AssignmentScoreReconstruction.initialQueue k.reconstructed a =
      (replay L.length a).2 := by
    change (k.reconstructed.registers.current a).queue = _
    rw [hcurValue a]
  have hweight (a : Fin p.K) : AssignmentScoreReconstruction.currentWeight k.reconstructed a =
      (1 + 1 / (ConstructorDimensions.D p : ℝ)) ^ (replay L.length a).1 := by
    change (1 + 1 / (ConstructorDimensions.D p : ℝ)) ^
      AssignmentScoreReconstruction.sourceScore k.reconstructed a = _
    rw [hscore a]
  refine ⟨L, n, r, theta, f.stream.payload, f.ledger, f.stream.saved, f.record,
    hL, hLlen, hsCut, hcutNext, htime, hr, ht, hactual, hcall, hcalendar,
    hparameters, hrows, hselected, hrewards, hearlier, hprevious, hstate,
    hcoord, hcutoff, hcursor, hempty, k, hliteral, hkcut, hktime,
    hopCut, hopCur, hopInc, k.reconstructionSuccess,
    fun a => ⟨hcutStored a, hcurStored a⟩, ?_, ?_⟩
  · intro a
    exact ⟨hcutNum a, hcurNum a, hcutValue a, hcurValue a, hscore a, hqueue a, hweight a⟩
  · intro hH a
    have hstopped := stopped_eq_unstopped_on_H rate rewards C_star C_h t z L hL hH a
    refine ⟨(hscore a).trans (congrArg Prod.fst hstopped).symm,
      (hqueue a).trans (congrArg Prod.snd hstopped).symm, ?_⟩
    change (1 + 1 / (ConstructorDimensions.D p : ℝ)) ^
        AssignmentScoreReconstruction.sourceScore k.reconstructed a =
      (1 + 1 / (ConstructorDimensions.D p : ℝ)) ^
        ((RecordedQueueRun.run (queueParameters rate) L).registers a).1
    rw [hscore a, hstopped]

/-- On the original first-call event intersected with the strict-past retained
test, the SAME actual reconstruction is also the stopped run's register pair
and score weight. This supplies no assertion on the complementary event. -/
theorem G_reconstruction (u t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hz : z ∈ G rate rewards C_star C_h u t) :
    ∃ (L : List (RecordedQueueRun.RoundInput p.K)) (n : ℕ)
      (r : ReferenceFirstCollectionSamplerCall.RoundRecord p rate)
      (theta : ReferenceFirstCollectionSamplerCall.Theta p)
      (old : ReferenceActivePhysicalStep.Payload rate)
      (ledger : ReferenceActivePhysicalStep.Ledger rate)
      (saved : Option (Fin p.T × Bool)),
      pastCells? rate rewards C_star C_h t z = some L ∧
      L.length = t.val - ReferenceCompletePhysicalHistory.physicalStart
        rate z rewards C_star C_h ∧
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[n]? = some r ∧ r.input.time = t ∧
      ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some r ∧
      ReferenceFirstCollectionSamplerCall.collectionCallAt r = some (u, theta) ∧
      ReferenceCalendarLaterSamplerPredictability.calendarParameters
        rate rewards C_star C_h t z = some theta ∧
      r.input.state.coordinator = .collection old ledger saved ∧ ledger.pending = ∅ ∧
      ∃ k : ActualNextDispatch r.input old ledger saved,
        k.operationLedger = CoordinatorRoundDispatch.collectionOperationLedger
          (ReferenceActivePhysicalStep.collectionInput r.input old ledger
            (ReferenceActivePhysicalStep.collectionClock old ledger saved k.cutoffTime)
            k.cutoffTime) k.core.payload_n_eq ∧
        k.cutoffTime = u ∧ k.instruction.time = t ∧
        (∀ a : Fin p.K,
          AssignmentScoreReconstruction.sourceScore k.reconstructed a =
            (unstoppedReplay (queueParameters rate) L L.length a).1 ∧
          AssignmentScoreReconstruction.initialQueue k.reconstructed a =
            (unstoppedReplay (queueParameters rate) L L.length a).2 ∧
          AssignmentScoreReconstruction.currentWeight k.reconstructed a =
            (1 + 1 / (ConstructorDimensions.D p : ℝ)) ^
              (unstoppedReplay (queueParameters rate) L L.length a).1) ∧
        (∀ a : Fin p.K,
          (AssignmentScoreReconstruction.sourceScore k.reconstructed a,
            AssignmentScoreReconstruction.initialQueue k.reconstructed a) =
              (RecordedQueueRun.run (queueParameters rate) L).registers a ∧
          AssignmentScoreReconstruction.currentWeight k.reconstructed a =
            RecordedQueueRun.scoreWeight (queueParameters rate)
              (RecordedQueueRun.run (queueParameters rate) L) a) := by
  obtain ⟨L, n, r, theta, old, ledger, saved, _previous, hL, hlen,
    _hs, _hut, _hdate, hr, ht, hactual, hcall, hcalendar, _hparameters,
    _hrows, _hselected, _hrewards, _hearlier, _hprevious, _hstate,
    hcoord, _hcutoff, _hcursor, hempty, k, hliteral, hkcut, hktime,
    _hopCut, _hopCur, _hopInc, _hrec, _hstored, hnum, hstopped⟩ :=
    firstCell_reconstruction rate rewards C_star C_h u t z hz.1
  refine ⟨L, n, r, theta, old, ledger, saved, hL, hlen, hr, ht, hactual,
    hcall, hcalendar, hcoord, hempty, k, hliteral, hkcut, hktime, ?_, ?_⟩
  · intro a
    exact (hnum a).2.2.2.2
  · intro a
    obtain ⟨hs, hq, hw⟩ := hstopped hz.2 a
    exact ⟨Prod.ext hs hq, hw⟩

end Bandits.Support.ReferenceFirstCollectionCurrentReplayReconstruction
