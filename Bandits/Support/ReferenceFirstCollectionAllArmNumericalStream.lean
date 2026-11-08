/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionRecoveredNumericalEndpoint
public import Bandits.Support.ReferenceFirstCollectionKnownSourceSplice
public import Bandits.Support.ReferenceFirstCollectionStreamEmptyDispatch

import Lean.Elab.Tactic.Omega

/-!
# Original numerical cells along the actual first collection stream

Mathematical evidence: `sources/zip4/manuscript/06_interruptions.tex:9-100,246-299`,
`sources/zip4/manuscript/04_slow_fast_learner.tex:157-174`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-79`.

The physical records, source rows, private arrays, selected row, reward table,
payload and FINISH ledgers are those of the initialized stream. Numerical cells
are read from actual recorder calls, with no value for an absent readout.
This is internal mathematics, not manuscript or regret closure.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ReferenceCollectionSegmentExtraction

namespace Bandits.Support.ReferenceFirstCollectionAllArmNumericalStream

variable {p : ConstructorDimensions.Parameters}

/-- Project the original numerical cells to the existing per-arm queue replay. -/
def arrivals (rate : ReferenceActivePhysicalStep.RateInput p) (a : Fin p.K)
    (cells : List (RecordedQueueRun.RoundInput p.K)) : List (Bool × ℕ) :=
  cells.map fun c => (c.enabled,
    RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a)

private theorem cell_ext {K : ℕ} (a b : RecordedQueueRun.RoundInput K)
    (he : a.enabled = b.enabled) (ha : a.recordedArm = b.recordedArm)
    (hr : a.reward = b.reward) (hx : a.rate = b.rate) : a = b := by
  cases a
  cases b
  cases he
  cases ha
  cases hr
  cases hx
  rfl

private theorem source_cell_congr (rate : ReferenceActivePhysicalStep.RateInput p)
    (left right : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (lc rc : Choice rate) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (lv : CoordinatorRecorderComplementBridge.LocalInputsValid
      (ReferenceActivePhysicalStep.collectionRecordingInput left.output.preparation
        lc.payload lc.started lc.weights))
    (rv : CoordinatorRecorderComplementBridge.LocalInputsValid
      (ReferenceActivePhysicalStep.collectionRecordingInput right.output.preparation
        rc.payload rc.started rc.weights)) (he : left = right) (hc : lc = rc) :
    ReferenceFirstCollectionCheckedSourcePrefix.sourceCell rate left lc rewards lv =
      ReferenceFirstCollectionCheckedSourcePrefix.sourceCell rate right rc rewards rv := by
  cases he
  cases hc
  rfl

/-- First-cell equality and the actual optional readouts force equality of
every common prefix. In particular, armwise witnesses cannot choose different
numerical cells for the same physical record. -/
theorem source_prefix_eq
    (rate : ReferenceActivePhysicalStep.RateInput p) (start : ℕ)
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (left right : List (RecordedQueueRun.RoundInput p.K)) (h : ℕ)
    (hl : h ≤ left.length) (hr : h ≤ right.length) (hb : h ≤ records.length)
    (hzero : ∀ hp : 0 < h, left[0]'(by omega) = right[0]'(by omega))
    (hleft : ∀ k : Fin h, 0 < k.val →
      ReferenceLaterCollectionArrivalReadout.laterCollectionReadout start
        (records[k.val]'(by have hk := k.isLt; omega)) = some (left[k.val]'(by have hk := k.isLt; omega)))
    (hright : ∀ k : Fin h, 0 < k.val →
      ReferenceLaterCollectionArrivalReadout.laterCollectionReadout start
        (records[k.val]'(by have hk := k.isLt; omega)) = some (right[k.val]'(by have hk := k.isLt; omega))) :
    left.take h = right.take h := by
  apply List.ext_getElem
  · simp only [List.length_take, Nat.min_eq_left hl, Nat.min_eq_left hr]
  · intro k hk hk'
    have hkh : k < h := lt_of_lt_of_le hk (List.length_take_le _ _)
    simp only [List.getElem_take]
    by_cases hz : k = 0
    · subst k
      exact hzero (by omega)
    · exact Option.some.inj ((hleft ⟨k, hkh⟩ (Nat.pos_of_ne_zero hz)).symm.trans
        (hright ⟨k, hkh⟩ (Nat.pos_of_ne_zero hz)))

private theorem physical_record_context
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (left right : ReferenceActivePhysicalStep.Ledger rate)
    (hc : CollectionBufferProvenance.collectionContext left =
      CollectionBufferProvenance.collectionContext right)
    (a : Fin p.K)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) :
    ReferenceCollectionRawBufferHistory.physicalQueueRecord left a record =
      ReferenceCollectionRawBufferHistory.physicalQueueRecord right a record := by
  simp only [CollectionBufferProvenance.collectionContext, Prod.mk.injEq] at hc
  simp only [ReferenceCollectionRawBufferHistory.physicalQueueRecord,
    ReferenceActivePhysicalStep.collectionEnabled, hc.2.1, hc.2.2.1, hc.2.2.2.1]

private theorem registers_pending
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (l : ReferenceActivePhysicalStep.Ledger rate)
    (hv : CoordinatorCollectionLedger.validLedgerCheck l = true) (a : Fin p.K) :
    (l.currentRegisters a = none ↔ CoordinatorCollectionLedger.armPending l a) ∧
    (l.cutoffRegisters a = none ↔ CoordinatorCollectionLedger.armPending l a) := by
  classical
  have hchecks := hv
  simp only [CoordinatorCollectionLedger.validLedgerCheck, Bool.and_eq_true] at hchecks
  have hcur : CoordinatorCollectionLedger.allFin p.K (fun b =>
      (l.currentRegisters b).isNone == CoordinatorCollectionLedger.armPendingCheck l b) = true := by
    tauto
  have hcut : CoordinatorCollectionLedger.allFin p.K (fun b =>
      (l.cutoffRegisters b).isNone == CoordinatorCollectionLedger.armPendingCheck l b) = true := by
    tauto
  have entry {test : Fin p.K → Bool}
      (ht : CoordinatorCollectionLedger.allFin p.K test = true) : test a = true := by
    exact List.all_eq_true.mp ht _ (List.mem_ofFn.mpr ⟨a, rfl⟩)
  have hp : CoordinatorCollectionLedger.armPendingCheck l a = true ↔
      CoordinatorCollectionLedger.armPending l a := by
    simp [CoordinatorCollectionLedger.armPendingCheck, CoordinatorCollectionLedger.anyFin,
      List.any_eq_true, CoordinatorCollectionLedger.armPending]
  have hc := entry hcur
  have hd := entry hcut
  cases he : CoordinatorCollectionLedger.armPendingCheck l a <;>
    cases hq : l.currentRegisters a <;> cases hz : l.cutoffRegisters a <;>
    simp_all

private theorem replay_add_score (capacity score backlog : ℕ) (records : List (Bool × ℕ)) :
    QueueReplay.replay capacity (score, backlog) records =
      (score + (QueueReplay.replay capacity (0, backlog) records).1,
        (QueueReplay.replay capacity (0, backlog) records).2) := by
  induction records generalizing score backlog with
  | nil => rfl
  | cons record rest ih =>
      change QueueReplay.replay capacity (QueueReplay.transition capacity (score, backlog) record) rest =
        (score + (QueueReplay.replay capacity
          (QueueReplay.transition capacity (0, backlog) record) rest).1,
          (QueueReplay.replay capacity (QueueReplay.transition capacity (0, backlog) record) rest).2)
      rw [CollectionKnownQueueContinuation.queueReplay_transition_add_score]
      rw [ih (score + (QueueReplay.transition capacity (0, backlog) record).1)
        (QueueReplay.transition capacity (0, backlog) record).2]
      rw [ih (QueueReplay.transition capacity (0, backlog) record).1
        (QueueReplay.transition capacity (0, backlog) record).2]
      simp only [Nat.add_assoc]

/-- A checked FINISH continues an already stored queue along the next actual
source record. Its conditional inputs are the previous stored queue/increment,
the checked round and the literal record identity, all supplied by the stream
induction below. -/
private theorem known_source_step
    (rate : ReferenceActivePhysicalStep.RateInput p) (a : Fin p.K)
    (live D : List (RecordedQueueRun.RoundInput p.K)) (n : ℕ) (hn : n < D.length)
    (l f : ReferenceActivePhysicalStep.Ledger rate)
    (input : CollectionCheckedExecution.RoundInput (p := p) (eta := rate.eta.val))
    (accepted : Bool) (q : CoordinatorCollectionLedger.CurrentRegister)
    (hknown : l.currentRegisters a = some q)
    (hchecked : CollectionCheckedExecution.checkedRounds l [input] = some ([accepted], f))
    (hrecord : CoordinatorCollectionLedger.localQueueRecord l input.round input.enabled input.raw a =
      ((D[n]).enabled, RecordedQueueRun.quantizedArrival
        (ReferenceFirstLaunchNumericalCell.queueParameters rate) D[n] a)) :
    let V := QueueReplay.replay (4 * rate.n) (0, 0) (arrivals rate a live)
    let R := fun h => QueueReplay.replay (4 * rate.n) (0, 0)
      (arrivals rate a (live ++ D.take h))
    let I := fun h => QueueReplay.replay (4 * rate.n) (0, V.2) (arrivals rate a (D.take h))
    q.queue = (R n).2 → l.increment a = (I n).1 →
    f.cutoffRegisters a = l.cutoffRegisters a ∧
    f.currentRegisters a = some ⟨(R (n + 1)).2, (R (n + 1)).1 - (R n).1⟩ ∧
    f.increment a = (I (n + 1)).1 ∧ V.1 + f.increment a = (R (n + 1)).1 := by
  intro V R I hqueue hinc
  let row := ((D[n]).enabled, RecordedQueueRun.quantizedArrival
    (ReferenceFirstLaunchNumericalCell.queueParameters rate) D[n] a)
  have hsplit (h : ℕ) : R h = (V.1 + (I h).1, (I h).2) := by
    change QueueReplay.replay (4 * rate.n) (0, 0)
      (arrivals rate a (live ++ D.take h)) = _
    simp only [arrivals, List.map_append]
    rw [QueueReplay.replay_append]
    exact replay_add_score (4 * rate.n) V.1 V.2 _
  have hI : I (n + 1) = QueueReplay.transition (4 * rate.n) (I n) row := by
    simp only [I, arrivals, List.take_succ_eq_append_getElem hn,
      List.map_append, List.map_cons, List.map_nil]
    rw [QueueReplay.replay_append]
    rfl
  have hbefore : (l.increment a, q.queue) = I n := by
    apply Prod.ext
    · exact hinc
    · rw [hqueue, hsplit]
  have hk := CollectionKnownQueueContinuation.checkedRounds_known_queue_continuation
    l f a q [input] [accepted] hknown hchecked
  have hrecords : CollectionKnownQueueContinuation.inputQueueRecords l a [input] = [row] := by
    simp only [CollectionKnownQueueContinuation.inputQueueRecords, List.map_cons, List.map_nil,
      hrecord, row]
  dsimp only at hk
  rw [hrecords, hbefore] at hk
  have hc := hk.1
  have hi := hk.2.1
  have hcut := hk.2.2.2.2.2.2
  have hcur : f.currentRegisters a = some ⟨(I (n + 1)).2, (I (n + 1)).1 - (I n).1⟩ := by
    simpa [CollectionKnownQueueContinuation.replayLastService, QueueReplay.replay, hI] using hc
  have hinc' : f.increment a = (I (n + 1)).1 := by
    simpa [QueueReplay.replay, hI] using hi
  refine ⟨hcut, ?_, hinc', ?_⟩
  · simpa only [hsplit, Nat.add_sub_add_left] using hcur
  · rw [hinc', hsplit]

section Actual

variable (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput
        source rewards C_star C_h rate)).crossing.isSome = true)
    (count : ℕ)
    (hspan : ReferenceFirstCollectionReadyStream.startTime (rate := rate)
      source rewards C_star C_h + count ≤ p.T)
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
        source rewards C_star C_h hcross count hspan).records).length < count)

local notation "s" => ReferenceFirstCollectionReadyStream.startTime (rate := rate)
  source rewards C_star C_h
local notation "E" => ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
  source rewards C_star C_h hcross count hspan
local notation "L" => ReferenceFirstLiveConfirmationHistory.firstLiveWindow
  (ReferenceActivePhysicalHorizon.Run.records
    (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
      source rewards C_star C_h hcross count hspan))
local notation "B" => ReferenceFirstCollectionReadyStream.actualWindow (rate := rate)
  source rewards C_star C_h hcross count hspan
local notation "Cells" => ReferenceFirstWindowNumericalStream.actualLiveSourceCells
  rate source rewards C_star C_h hcross count hspan

include hshort

/-- A selected physical record has its literal original recorder cell. All
conditions here are local choice selectors; none is a numerical premise. -/
private theorem actual_source_cell
    (j : Fin (B).length) (call : Choice rate)
    (hc : choice B[j.val].input = some call) :
    ∃ valid : CoordinatorRecorderComplementBridge.LocalInputsValid
      (ReferenceActivePhysicalStep.collectionRecordingInput B[j.val].output.preparation
        call.payload call.started call.weights),
      let cell := ReferenceFirstCollectionCheckedSourcePrefix.sourceCell
        rate B[j.val] call rewards valid
      B[j.val].input.rows = source.1.2 ∧
      B[j.val].input.selected = ActualInitializationPhysicalStep.selectedRowIndex p source ∧
      B[j.val].input.rewards = rewards ∧ B[j.val].input.time.val = s + (L).length + j.val ∧
      (∀ a, ReferenceCollectionRawBufferHistory.physicalQueueRecord call.preLedger a B[j.val] =
        (cell.enabled, RecordedQueueRun.quantizedArrival
          (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell a)) ∧
      (0 < j.val → ReferenceLaterCollectionArrivalReadout.laterCollectionReadout s B[j.val] =
        some cell) := by
  classical
  obtain ⟨cut, suffix, payload, headCell, _hcut, _hrecords, _hrows, _hselected,
    _hrewards, _htime, _hlive, _hwindow, _hboundary,
    hrows, hselected, hrewards, htime, _hnone, hcall⟩ :=
    ReferenceFirstCollectionCanonicalArrivalSource.actual_first_collection_canonical_arrival_source
      rate source rewards C_star C_h hcross count hspan hshort j
  obtain ⟨_hpayload, _hinitHead, _hinitTail, valid, cell, he, hclock, ha, hr, hx, _hrate,
    hout, hreadout⟩ := hcall call hc
  have hcell : cell = ReferenceFirstCollectionCheckedSourcePrefix.sourceCell
      rate B[j.val] call rewards valid := cell_ext _ _ he ha hr hx
  obtain ⟨out, _hrun, _hdiag, _hgate, _hraw, _harrival, hphysical,
    _hformula, _habsent, _hzero⟩ := hout
  refine ⟨valid, hrows, hselected, hrewards, htime, hcell ▸ hphysical, ?_⟩
  intro hj
  rcases hreadout with ⟨hz, _⟩ | ⟨_, hread⟩
  · omega
  · exact hcell ▸ hread

variable (out : ReferenceFirstCollectionReadyStream.ActualInitializedStreamOutput
  (p := p) (rate := rate) source rewards C_star C_h count hcross hspan hshort)

private theorem stream_cutoff_choice :
    ∃ (head : Choice rate) (initializer : Initializer p),
      choice out.cutoff.cut.input = some head ∧ head.payload = out.payload ∧
      head.initializer = some initializer ∧
      initializer.checkedStart rate = .success head.preLedger := by
  classical
  have hBpos : 0 < (B).length := by rw [← out.windowIsActual]; exact out.windowNonempty
  obtain ⟨cut, suffix, payload, headCell, hcut, _hrecords, _hrows, _hselected,
    _hrewards, _htime, hlive, _hwindow, _hboundary,
    _hrowsAt, _hselectedAt, _hrewardsAt, _htimeAt, hnone, hcall⟩ :=
    ReferenceFirstCollectionCanonicalArrivalSource.actual_first_collection_canonical_arrival_source
      rate source rewards C_star C_h hcross count hspan hshort ⟨0, hBpos⟩
  have hbound : (L).length < (E).records.length := List.getElem?_eq_some_iff.mp out.cutoff.cutIndex |>.choose
  have hcutIndex : (E).records[(L).length]? = some cut :=
    (List.getElem?_eq_getElem hbound).trans (congrArg some hcut.symm)
  have hcutEq : cut = out.cutoff.cut :=
    Option.some.inj (hcutIndex.symm.trans out.cutoff.cutIndex)
  have hzero : (B)[0]'hBpos = out.cutoff.cut :=
    (List.getElem_of_eq out.windowIsActual.symm hBpos).trans out.cutoffIsHead
  have hsome : (choice (B)[0].input).isSome = true := by
    cases hc : choice (B)[0].input with
    | none => exact False.elim (Nat.not_lt_zero _ (hnone hc))
    | some head => rfl
  obtain ⟨head, hhead⟩ := Option.isSome_iff_exists.mp hsome
  obtain ⟨hpay, hinit, _htail, _hcell⟩ := hcall head hhead
  obtain ⟨initializer, hi⟩ := Option.isSome_iff_exists.mp (hinit rfl)
  obtain ⟨r, q, base, hstate, hP⟩ := hlive
  obtain ⟨execution⟩ := out.cutoffExecution
  have hcfg : ReferenceActivePhysicalStep.CoordinatorConfiguration.live r q base =
      .live execution.live execution.owned execution.base := by
    rw [hcutEq] at hstate
    exact hstate.symm.trans execution.actualLive
  have hreg := (ReferenceActivePhysicalStep.CoordinatorConfiguration.live.inj hcfg).1
  have hpayOut : head.payload = out.payload := by
    calc
      head.payload = payload := hpay
      _ = r.payload := hP
      _ = execution.live.payload := congrArg (fun z => z.payload) hreg
      _ = out.cutoff.payload := execution.payloadIsLive.symm
      _ = out.payload := out.payloadMatchesCutoff.symm
  have hheadCut : choice out.cutoff.cut.input = some head := by simpa only [hzero] using hhead
  exact ⟨head, initializer, hheadCut, hpayOut, hi,
    choice_initializer out.cutoff.cut.input head initializer hheadCut hi⟩

private theorem stream_choice_at
    (head : Choice rate) (hhead : choice out.cutoff.cut.input = some head)
    (hpay : head.payload = out.payload) (n : Fin out.ell) :
    ∃ call : Choice rate,
      choice (out.window[n.val]'(lt_of_lt_of_le n.isLt out.withinWindow)).input = some call ∧
      call.payload = out.payload ∧ (n.val = 0 → call = head) := by
  by_cases hz : n.val = 0
  · refine ⟨head, ?_, hpay, fun _ => rfl⟩
    simpa only [hz, out.cutoffIsHead] using hhead
  · obtain ⟨j, record, incoming, cell, _hj, hr, _hf, _hi⟩ :=
      out.cell_at n (Nat.pos_of_ne_zero hz)
    have hrecord : out.window[n.val]'(lt_of_lt_of_le n.isLt out.withinWindow) = record :=
      Option.some.inj ((List.getElem?_eq_getElem _).symm.trans hr)
    exact ⟨cell.choice, hrecord ▸ cell.actualChoice, cell.choicePayload,
      fun h => False.elim (hz h)⟩

/-- One common original-source cell list through exactly the actual stream.
The cutoff and every later cell have their actual recorder proof. Physical
queue identities hold simultaneously for all arms at every selected record. -/
theorem stream_source_prefix :
    ∃ (head : Choice rate) (initializer : Initializer p)
      (valid : CoordinatorRecorderComplementBridge.LocalInputsValid
        (ReferenceActivePhysicalStep.collectionRecordingInput out.cutoff.cut.output.preparation
          head.payload head.started head.weights))
      (D : List (RecordedQueueRun.RoundInput p.K)),
      choice out.cutoff.cut.input = some head ∧ head.payload = out.payload ∧
      head.initializer = some initializer ∧
      initializer.checkedStart rate = .success head.preLedger ∧
      ∃ hDlen : D.length = out.ell,
      D[0]'(by rw [hDlen]; exact lt_of_lt_of_le Nat.zero_lt_one out.positiveLength) =
        ReferenceFirstCollectionCheckedSourcePrefix.sourceCell rate out.cutoff.cut head rewards valid ∧
      (∀ n : Fin out.ell,
        let record := out.window[n.val]'(lt_of_lt_of_le n.isLt out.withinWindow)
        let cell := D[n.val]'(by rw [hDlen]; exact n.isLt)
        ∃ (call : Choice rate)
          (validCall : CoordinatorRecorderComplementBridge.LocalInputsValid
            (ReferenceActivePhysicalStep.collectionRecordingInput record.output.preparation
              call.payload call.started call.weights)),
          choice record.input = some call ∧ call.payload = out.payload ∧
          cell = ReferenceFirstCollectionCheckedSourcePrefix.sourceCell rate record call rewards validCall ∧
          record.input.rows = source.1.2 ∧
          record.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p source ∧
          record.input.rewards = rewards ∧ record.input.time.val = s + (L).length + n.val ∧
          cell.enabled = ReferenceActivePhysicalStep.collectionEnabled call.preLedger record.input.time ∧
          cell.reward = (fun a => ((rewards record.input.time a).val : ℝ) /
            (ConstructorDimensions.D p : ℝ)) ∧ cell.rate = out.payload.rate ∧
          (∀ a : Fin p.K,
            ReferenceCollectionRawBufferHistory.physicalQueueRecord call.preLedger a record =
              (cell.enabled, RecordedQueueRun.quantizedArrival
                (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell a)) ∧
          (0 < n.val → ReferenceLaterCollectionArrivalReadout.laterCollectionReadout s record = some cell)) := by
  classical
  obtain ⟨head, initializer, hhead, hpay, hinit, hchecked⟩ :=
    stream_cutoff_choice rate source rewards C_star C_h hcross count hspan hshort out
  have hchoices := stream_choice_at rate source rewards C_star C_h hcross count hspan hshort
    out head hhead hpay
  let calls (n : Fin out.ell) := Classical.choose (hchoices n)
  have hcalls (n : Fin out.ell) := Classical.choose_spec (hchoices n)
  have hcells (n : Fin out.ell) := actual_source_cell
    rate source rewards C_star C_h hcross count hspan hshort
    ⟨n.val, by rw [← out.windowIsActual]; exact lt_of_lt_of_le n.isLt out.withinWindow⟩ (calls n)
    (by simpa only [← out.windowIsActual] using (hcalls n).1)
  let validAt (n : Fin out.ell) := Classical.choose (hcells n)
  have recordEq (n : Fin out.ell) :
      (B)[n.val]'(by rw [← out.windowIsActual]; exact lt_of_lt_of_le n.isLt out.withinWindow) =
        out.window[n.val]'(lt_of_lt_of_le n.isLt out.withinWindow) :=
    List.getElem_of_eq out.windowIsActual.symm _
  let D := List.ofFn fun n : Fin out.ell =>
    ReferenceFirstCollectionCheckedSourcePrefix.sourceCell rate
      (out.window[n.val]'(lt_of_lt_of_le n.isLt out.withinWindow)) (calls n) rewards
      (recordEq n ▸ validAt n)
  have hDlen : D.length = out.ell := List.length_ofFn
  let zero : Fin out.ell := ⟨0, by have h := out.positiveLength; omega⟩
  have hcallZero : calls zero = head := (hcalls zero).2.2 rfl
  have valid : CoordinatorRecorderComplementBridge.LocalInputsValid
      (ReferenceActivePhysicalStep.collectionRecordingInput out.cutoff.cut.output.preparation
        head.payload head.started head.weights) := by
    have hv : CoordinatorRecorderComplementBridge.LocalInputsValid
        (ReferenceActivePhysicalStep.collectionRecordingInput (out.window[0]'out.windowNonempty).output.preparation
          (calls zero).payload (calls zero).started (calls zero).weights) := by
      exact recordEq zero ▸ validAt zero
    rw [out.cutoffIsHead, hcallZero] at hv
    exact hv
  refine ⟨head, initializer, valid, D, hhead, hpay, hinit, hchecked, hDlen, ?_, ?_⟩
  · simp only [D, List.getElem_ofFn]
    change ReferenceFirstCollectionCheckedSourcePrefix.sourceCell rate
      (out.window[0]'out.windowNonempty) (calls zero) rewards _ = _
    exact source_cell_congr rate _ _ _ _ rewards _ valid out.cutoffIsHead hcallZero
  · intro n
    dsimp only
    have hn := Classical.choose_spec (hcells n)
    simp only [← out.windowIsActual] at hn
    obtain ⟨hrows, hselected, hrewards, htime, hphysical, hread⟩ := hn
    refine ⟨calls n, recordEq n ▸ validAt n,
      (hcalls n).1, (hcalls n).2.1, ?_, hrows, hselected, hrewards, htime, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [D, List.getElem_ofFn]
    · simp only [D, List.getElem_ofFn, ReferenceFirstCollectionCheckedSourcePrefix.sourceCell]
    · simp only [D, List.getElem_ofFn, ReferenceFirstCollectionCheckedSourcePrefix.sourceCell]
    · simp only [D, List.getElem_ofFn, ReferenceFirstCollectionCheckedSourcePrefix.sourceCell]
      change (calls n).payload.rate = out.payload.rate
      rw [(hcalls n).2.1]
    · simpa only [D, List.getElem_ofFn] using hphysical
    · simpa only [D, List.getElem_ofFn] using hread

/-- The cutoff FINISH already contains the numerical source replay on each
fast arm. The retained previous service is supplied by the actual live prefix,
not by an arbitrary cutoff register. -/
private theorem cutoff_fast_numerical
    (head : Choice rate)
    (valid : CoordinatorRecorderComplementBridge.LocalInputsValid
      (ReferenceActivePhysicalStep.collectionRecordingInput out.cutoff.cut.output.preparation
        head.payload head.started head.weights))
    (hhead : choice out.cutoff.cut.input = some head)
    (a : CanonicalFastSampling.FastArm out.payload.slowSet) :
    let cu := ReferenceFirstCollectionCheckedSourcePrefix.sourceCell rate out.cutoff.cut head rewards valid
    let V := QueueReplay.replay (4 * rate.n) (0, 0) (arrivals rate a.val Cells)
    let Vpre := QueueReplay.replay (4 * rate.n) (0, 0)
      (arrivals rate a.val ((Cells).take ((L).length - 1)))
    let R := QueueReplay.replay (4 * rate.n) (0, 0) (arrivals rate a.val (Cells ++ [cu]))
    out.cutoff.ledger.cutoffRegisters a.val = some ⟨V.1, V.2, V.1 - Vpre.1⟩ ∧
    out.cutoff.ledger.currentRegisters a.val = some ⟨R.2, R.1 - V.1⟩ ∧
    out.cutoff.ledger.increment a.val =
      (QueueReplay.replay (4 * rate.n) (0, V.2) (arrivals rate a.val [cu])).1 ∧
    V.1 + out.cutoff.ledger.increment a.val = R.1 := by
  classical
  intro cu V Vpre R
  obtain ⟨cut, suffix, r, q, base, dispatched, hstart,
    ledger, hinit, hledger, hdomain, hclock, hpending, hnoAssignment,
    selected, recording, hcut, _hrecords, _hphysical, htime, _hrows,
    _hselected, _hrewards, _hsigma, _hn, _hbase, hstate, hprep,
    _hu, _huBound, _huGrid, _hcutoff, hwpos, _hpayloads, htail⟩ :=
    ReferenceFirstCutoffKnownNumericalState.actual_first_cutoff_known_numerical_state
      rate source rewards C_star C_h hcross count hspan hshort
  dsimp only at htail
  obtain ⟨_he, _ha, _hr, _hx, _henabled, _hrec, _hdiag, _habsent,
    _hraw, _hzero, _hslot, _harrival, _hqueue, _hdisabled, _hboundary,
    _hlen, _hslow, started, _hstart, _hcandidate, hfast, _hunknown, _hbuffer, hreceiver⟩ := htail
  obtain ⟨input, diagnostic, _hinput, _hinputLedger, _hinputDomain, _hinputCheck,
    _hrawParsed, _hfiltered, _hparsed, _hreceive, _hdiagSome, _hdiagInput,
    _hdiagRaw, _hdiagParsed, _hdiagExpected, _hdiagDecoder, _hdiagAccepted,
    _hdiagMatches, _hdiagWrong, _hbankOther, _hbankEq, _hbatchCompleted,
    _hbatchPending, finished, _hfinish, _hfinishCandidate, hfinishedCut,
    hfinishedKnown, _hfinishedUnknown, _hconfiguration, hnext, _hnextBank,
    _hcoordinatorBank, _hfailure, _hrecordingFinal, _hupFinal⟩ := hreceiver
  have hbound : (L).length < (E).records.length :=
    (List.getElem?_eq_some_iff.mp out.cutoff.cutIndex).1
  have hcutEq : cut = out.cutoff.cut := by
    have hget : (E).records[(L).length]? = some cut :=
      (List.getElem?_eq_getElem hbound).trans (congrArg some hcut.symm)
    exact Option.some.inj (hget.symm.trans out.cutoff.cutIndex)
  have hmem : cut ∈ (E).records := hcut ▸ List.getElem_mem hbound
  clear hcut
  subst cut
  have hcfg := hnext.symm.trans out.cutoff.outputCoordinator
  have hpayCut : r.payload = out.cutoff.payload :=
    (ReferenceActivePhysicalStep.CoordinatorConfiguration.collection.inj hcfg).1
  have hfinished : finished = out.cutoff.ledger :=
    (ReferenceActivePhysicalStep.CoordinatorConfiguration.collection.inj hcfg).2.1
  have hpayR : r.payload = out.payload := hpayCut.trans out.payloadMatchesCutoff.symm
  let headK : Choice rate :=
    ⟨r.payload, ReferenceActivePhysicalStep.sharedLedger ledger, dispatched.startResult,
      (ReferenceActivePhysicalStep.liveRegistersAt r out.cutoff.cut.input.time).complementWeights,
      some (cutoffInitializer (ReferenceActivePhysicalStep.liveRegistersAt r out.cutoff.cut.input.time)
        (ReferenceActivePhysicalStep.liveOwnedAt r q out.cutoff.cut.input.time)
        base out.cutoff.cut.input.time)⟩
  have hprepared : out.cutoff.cut.output.preparation =
      ReferenceActivePhysicalStep.prepare out.cutoff.cut.input := by rw [out.cutoff.cut.output_eq]; rfl
  have hprepCut := hprepared ▸ hprep
  have hheadK : choice out.cutoff.cut.input = some headK := by
    unfold choice
    have hs : (ReferenceActivePhysicalStep.prepare out.cutoff.cut.input).coordinator.selection ≠ none := by
      rw [hprepCut]
      simp [ReferenceActivePhysicalStep.DispatchCut.selection, ReferenceActivePhysicalStep.selectionAt]
    rw [ite_eq_right hs, hprepCut]
    rfl
  have hheadEq : head = headK := Option.some.inj (hhead.symm.trans hheadK)

  -- The incoming physical state is the original live-prefix endpoint.
  obtain ⟨k, _hk, htime', hstate'⟩ := ReferenceSelectedPayloadChronology.actualRunRecord_has_prefix
    (ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hcross)
    source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s count hspan
    (ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
      rate source rewards C_star C_h hcross).activeAtStart out.cutoff.cut hmem
  have htimeOut := out.cutoff.cutTime
  have hk : k = (L).length := by omega
  subst k
  have hprefix := ReferenceFirstLiveComplementQueueReplay.actual_first_live_complement_prefix_replay
    rate source rewards C_star C_h hcross count hspan (L).length le_rfl
  obtain ⟨rp, qp, bp, hpstate, _hpspan, _hpsigma, _hpn, _hpbase, _hbirth, hpqueues⟩ :=
    hprefix.2.2 hwpos
  have hlive : ReferenceActivePhysicalStep.CoordinatorConfiguration.live rp qp bp = .live r q base :=
    hpstate.symm.trans ((congrArg ReferenceActivePhysicalStep.State.coordinator hstate').symm.trans hstate)
  cases hlive
  let ar : CanonicalFastSampling.FastArm r.payload.slowSet :=
    ⟨a.val, by simpa only [hpayR] using a.property⟩
  have hsameArm : ar.val = a.val := rfl
  have hcellLen : (Cells).length = (L).length :=
    ReferenceFirstWindowNumericalStream.actualLiveSourceCells_length
      rate source rewards C_star C_h hcross count hspan
  have htake : (Cells).take (L).length = Cells := by simp [hcellLen]
  have hprevious := (hpqueues ar).2.2.2.1
  dsimp only at hprevious
  rw [htake] at hprevious
  have hprevious' : q.previousService ar = V.1 - Vpre.1 := by
    simpa only [V, Vpre, arrivals, hsameArm] using hprevious
  have hfields := hfast ar
  have hfinishedFields := hfinishedKnown ar
  have hcutoff : out.cutoff.ledger.cutoffRegisters a.val =
      some ⟨V.1, V.2, V.1 - Vpre.1⟩ := by
    rw [← hfinished, hfinishedCut]
    simpa only [V, arrivals, hsameArm, hprevious'] using hfields.2.1
  have hcu : cu = ReferenceFirstCollectionCheckedSourcePrefix.sourceCell
      rate out.cutoff.cut headK rewards (hheadEq ▸ valid) :=
    source_cell_congr rate _ _ _ _ rewards valid _ rfl hheadEq
  let row := (cu.enabled, RecordedQueueRun.quantizedArrival
    (ReferenceFirstLaunchNumericalCell.queueParameters rate) cu a.val)
  have hR : R = QueueReplay.transition (4 * rate.n) V row := by
    simp only [R, V, arrivals, List.map_append, List.map_cons, List.map_nil]
    rw [QueueReplay.replay_append]
    rfl
  have hcurrent : out.cutoff.ledger.currentRegisters a.val = some ⟨R.2, R.1 - V.1⟩ := by
    rw [← hfinished]
    simpa only [hR, V, arrivals, row, hcu, headK,
      ReferenceFirstCollectionCheckedSourcePrefix.sourceCell, hsameArm] using hfinishedFields.2.1
  have hoff := CollectionKnownQueueContinuation.queueReplay_transition_add_score
    (4 * rate.n) V.1 V.2 row
  have hinc : out.cutoff.ledger.increment a.val = R.1 - V.1 := by
    rw [← hfinished]
    simpa only [hR, V, arrivals, row, hcu, headK,
      ReferenceFirstCollectionCheckedSourcePrefix.sourceCell, hsameArm] using hfinishedFields.1
  refine ⟨hcutoff, hcurrent, ?_, ?_⟩
  · rw [hinc, hR, hoff]
    simp only [arrivals, List.map_cons, List.map_nil, QueueReplay.replay,
      Nat.add_sub_cancel_left, row, List.foldl_cons, List.foldl_nil]
  · rw [hinc, hR, hoff]
    simp only [Nat.add_sub_cancel_left]

/-- Consume the recovered-endpoint producer at the current actual acceptance.
Its existential readout is identified with the common stream prefix before
any armwise numerical equation is used. -/
private theorem accepted_numerical
    (head : Choice rate)
    (valid : CoordinatorRecorderComplementBridge.LocalInputsValid
      (ReferenceActivePhysicalStep.collectionRecordingInput out.cutoff.cut.output.preparation
        head.payload head.started head.weights))
    (hhead : choice out.cutoff.cut.input = some head)
    (D : List (RecordedQueueRun.RoundInput p.K)) (hDlen : D.length = out.ell)
    (hDzero : D[0]'(by rw [hDlen]; have h := out.positiveLength; omega) =
      ReferenceFirstCollectionCheckedSourcePrefix.sourceCell rate out.cutoff.cut head rewards valid)
    (hread : ∀ k : Fin out.ell, 0 < k.val →
      ReferenceLaterCollectionArrivalReadout.laterCollectionReadout s
        (out.window[k.val]'(lt_of_lt_of_le k.isLt out.withinWindow)) =
        some (D[k.val]'(by rw [hDlen]; exact k.isLt)))
    (n : Fin out.ell)
    (incoming : ReferenceActivePhysicalStep.Ledger rate)
    (hready : ReferenceContinuingCollectionStartDomains.continuingCollectionReadyDomain
      (out.window[n.val]'(lt_of_lt_of_le n.isLt out.withinWindow)).input out.payload incoming out.saved)
    (M : ReferenceCollectionPhaseHistory.UpRecord p rate)
    (hparse : effectiveParse (out.window[n.val]'(lt_of_lt_of_le n.isLt out.withinWindow)).input
      (CoordinatorCollectionLedger.startRoundCandidate incoming
        (out.window[n.val]'(lt_of_lt_of_le n.isLt out.withinWindow)).input.time
        (ReferenceActivePhysicalStep.collectionEnabled incoming
          (out.window[n.val]'(lt_of_lt_of_le n.isLt out.withinWindow)).input.time)
        (ReferenceCollectionRawBufferHistory.rawDiagnostic
          (out.window[n.val]'(lt_of_lt_of_le n.isLt out.withinWindow)))) = some M)
    (haccept : CoordinatorCollectionLedger.acceptUpCheck
      (CoordinatorCollectionLedger.startRoundCandidate incoming
        (out.window[n.val]'(lt_of_lt_of_le n.isLt out.withinWindow)).input.time
        (ReferenceActivePhysicalStep.collectionEnabled incoming
          (out.window[n.val]'(lt_of_lt_of_le n.isLt out.withinWindow)).input.time)
        (ReferenceCollectionRawBufferHistory.rawDiagnostic
          (out.window[n.val]'(lt_of_lt_of_le n.isLt out.withinWindow))))
      (ReferenceActivePhysicalStep.upSenderIndex
        (out.window[n.val]'(lt_of_lt_of_le n.isLt out.withinWindow)).input) M = true) :
    let a := incoming.assignment.arm (ReferenceActivePhysicalStep.upSenderIndex
      (out.window[n.val]'(lt_of_lt_of_le n.isLt out.withinWindow)).input)
    let l := out.ledgers n
    let V := QueueReplay.replay (4 * rate.n) (0, 0) (arrivals rate a Cells)
    let Vpre := QueueReplay.replay (4 * rate.n) (0, 0)
      (arrivals rate a ((Cells).take ((L).length - 1)))
    let R := fun h => QueueReplay.replay (4 * rate.n) (0, 0)
      (arrivals rate a (Cells ++ D.take h))
    l.cutoffRegisters a = some ⟨V.1, V.2, V.1 - Vpre.1⟩ ∧
    l.currentRegisters a = some ⟨(R (n.val + 1)).2, (R (n.val + 1)).1 - (R n.val).1⟩ ∧
    l.increment a = (QueueReplay.replay (4 * rate.n) (0, V.2)
      (arrivals rate a (D.take (n.val + 1)))).1 ∧
    V.1 + l.increment a = (R (n.val + 1)).1 := by
  classical
  intro a l V Vpre R
  let nb : Fin ((ReferenceCollectionPhaseHistory.collectionWindow
      (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
        rate source rewards C_star C_h hcross count hspan).records
      (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
          rate source rewards C_star C_h hcross count hspan).records).length).length) :=
    ⟨n.val, by change n.val < (B).length
               rw [← out.windowIsActual]
               exact lt_of_lt_of_le n.isLt out.withinWindow⟩
  have recordEq (k : ℕ) (hk : k < out.window.length) :
      (B)[k]'(by simpa only [out.windowIsActual] using hk) = out.window[k] :=
    List.getElem_of_eq out.windowIsActual.symm _
  have hr : (B)[nb.val] = out.window[n.val]'(lt_of_lt_of_le n.isLt out.withinWindow) :=
    recordEq n.val _
  have hR := ReferenceFirstCollectionRecoveredNumericalEndpoint.actual_first_collection_recovered_numerical_endpoint
    rate source rewards C_star C_h count hcross hspan hshort nb out.payload incoming out.saved
    (hr ▸ hready) M (hr ▸ hparse) (hr ▸ haccept)
  dsimp only at hR
  obtain ⟨call, f, completed, cut, headR, initializer, seg, _hn, _hchoice,
    _hpay, _hledger, _hinit, hnext, _hcursor, _hpending, _hextract, _hcontext,
    _hfinal, _haccepted, _hparsed, _hselected, hcut, hheadR, _hinitR,
    _hcheckedInit, _hbase, _hsegment, _hentry, _hsegcontext, retained,
    _htake, _hcurrent, _hcheckedPrefix, _hendpoint, validR, presentR,
    hDRlen, hDRzero, hDRread, _hsource, _hphysical,
    hcutoffR, hcurrentR, hincrementR, hsumR, _hgamma⟩ := hR
  let DR := ReferenceFirstCollectionCheckedSourcePrefix.readoutPrefix rate s B nb
    (ReferenceFirstCollectionCheckedSourcePrefix.sourceCell rate cut headR rewards validR) presentR
  change DR.length = n.val + 1 at hDRlen
  have hcutEq : cut = out.cutoff.cut := hcut.trans
    ((recordEq 0 out.windowNonempty).trans out.cutoffIsHead)
  have hheadEq : headR = head :=
    Option.some.inj ((hcutEq ▸ hheadR).symm.trans hhead)
  have hzero : DR[0]'(by omega) = D[0]'(by rw [hDlen]; have h := out.positiveLength; omega) :=
    hDRzero.trans ((source_cell_congr rate _ _ _ _ rewards validR valid hcutEq hheadEq).trans hDzero.symm)
  have hpref : DR = D.take (n.val + 1) := by
    have he := source_prefix_eq rate s out.window DR D (n.val + 1)
      (by omega) (by rw [hDlen]; exact n.isLt) (by have h := out.withinWindow; omega)
      (fun _ => hzero) (fun k hk => by
        have h := hDRread k hk
        have hkB : k.val < out.window.length := by
          have hn := n.isLt
          have hk := k.isLt
          have hw := out.withinWindow
          omega
        change ReferenceLaterCollectionArrivalReadout.laterCollectionReadout s
          ((B)[k.val]'(by simpa only [out.windowIsActual] using hkB)) =
            some (DR[k.val]'(by have hk := k.isLt; omega)) at h
        rw [recordEq k.val hkB] at h
        exact h)
      (fun k hk => hread ⟨k.val, by have hn := n.isLt; have hk := k.isLt; omega⟩ hk)
    simpa only [List.take_of_length_le (by omega : DR.length ≤ n.val + 1)] using he
  obtain ⟨record, hrecord, _hfail, hnextOut, _hrest⟩ := out.output_properties n
  have hrecordEq : (B)[nb.val] = record := hr.trans (List.getElem?_eq_some_iff.mp hrecord).2
  have hf : f = out.ledgers n :=
    (ReferenceActivePhysicalStep.CoordinatorConfiguration.collection.inj
      ((hrecordEq ▸ hnext).symm.trans hnextOut)).2.1
  have hcellLen : (Cells).length = (L).length :=
    ReferenceFirstWindowNumericalStream.actualLiveSourceCells_length
      rate source rewards C_star C_h hcross count hspan
  have htake : (Cells).take (L).length = Cells := by simp [hcellLen]
  have ht : ∀ h, h ≤ n.val + 1 → DR.take h = D.take h := by
    intro h hh
    rw [hpref, List.take_take, Nat.min_eq_left hh]
  dsimp only [ReferenceFirstCollectionReadyStream.actualWindow,
    ReferenceFirstCollectionReadyStream.actualEpoch] at hr
  have ha : incoming.assignment.arm (ReferenceActivePhysicalStep.upSenderIndex (B)[nb.val].input) = a :=
    congrArg (fun record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) =>
      incoming.assignment.arm (ReferenceActivePhysicalStep.upSenderIndex record.input)) hr
  dsimp only [ReferenceFirstCollectionReadyStream.actualWindow,
    ReferenceFirstCollectionReadyStream.actualEpoch] at ha
  have hcut : f.cutoffRegisters a = some
      ⟨(QueueReplay.replay (4 * rate.n) (0, 0)
          (arrivals rate a ((Cells).take (L).length))).1,
        (QueueReplay.replay (4 * rate.n) (0, 0)
          (arrivals rate a ((Cells).take (L).length))).2,
        (QueueReplay.replay (4 * rate.n) (0, 0)
          (arrivals rate a ((Cells).take (L).length))).1 -
        (QueueReplay.replay (4 * rate.n) (0, 0)
          (arrivals rate a ((Cells).take ((L).length - 1)))).1⟩ := ha ▸ hcutoffR
  have hcur : f.currentRegisters a = some
      ⟨(QueueReplay.replay (4 * rate.n) (0, 0) (arrivals rate a (Cells ++ DR.take (n.val + 1)))).2,
        (QueueReplay.replay (4 * rate.n) (0, 0) (arrivals rate a (Cells ++ DR.take (n.val + 1)))).1 -
        (QueueReplay.replay (4 * rate.n) (0, 0) (arrivals rate a (Cells ++ DR.take n.val))).1⟩ := ha ▸ hcurrentR
  have hinc : f.increment a = (QueueReplay.replay (4 * rate.n)
      (0, (QueueReplay.replay (4 * rate.n) (0, 0)
        (arrivals rate a ((Cells).take (L).length))).2) (arrivals rate a DR)).1 := ha ▸ hincrementR
  have hsum : (QueueReplay.replay (4 * rate.n) (0, 0)
      (arrivals rate a ((Cells).take (L).length))).1 + f.increment a =
        (QueueReplay.replay (4 * rate.n) (0, 0)
          (arrivals rate a (Cells ++ DR.take (n.val + 1)))).1 := ha ▸ hsumR
  rw [hf] at hcut hcur hinc hsum
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [V, Vpre, htake] using hcut
  · simpa only [ht (n.val + 1) le_rfl, ht n.val (Nat.le_add_right _ _)] using hcur
  · simpa only [V, htake, hpref] using hinc
  · simpa only [V, R, htake, ht (n.val + 1) le_rfl] using hsum

private theorem fast_incoming_numerical
    (head : Choice rate)
    (valid : CoordinatorRecorderComplementBridge.LocalInputsValid
      (ReferenceActivePhysicalStep.collectionRecordingInput out.cutoff.cut.output.preparation
        head.payload head.started head.weights))
    (hhead : choice out.cutoff.cut.input = some head)
    (D : List (RecordedQueueRun.RoundInput p.K)) (hDlen : D.length = out.ell)
    (hDzero : D[0]'(by rw [hDlen]; have h := out.positiveLength; omega) =
      ReferenceFirstCollectionCheckedSourcePrefix.sourceCell rate out.cutoff.cut head rewards valid)
    (hread : ∀ k : Fin out.ell, 0 < k.val →
      ReferenceLaterCollectionArrivalReadout.laterCollectionReadout s
        (out.window[k.val]'(lt_of_lt_of_le k.isLt out.withinWindow)) =
        some (D[k.val]'(by rw [hDlen]; exact k.isLt)))
    (n : Fin out.ell) (hn : 0 < n.val) (call : Choice rate)
    (hc : choice (out.window[n.val]'(lt_of_lt_of_le n.isLt out.withinWindow)).input = some call)
    (a : CanonicalFastSampling.FastArm call.payload.slowSet) :
    let R := fun h => QueueReplay.replay (4 * rate.n) (0, 0)
      (arrivals rate a.val (Cells ++ D.take h))
    call.preLedger.currentRegisters a.val =
      some ⟨(R n.val).2, (R n.val).1 - (R (n.val - 1)).1⟩ := by
  classical
  intro R
  let nb : Fin ((ReferenceCollectionPhaseHistory.collectionWindow
      (ReferenceFirstWindowNumericalStream.actualFirstLiveRun
        rate source rewards C_star C_h hcross count hspan).records
      (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
        rate source rewards C_star C_h hcross count hspan).length).length) :=
    ⟨n.val, by change n.val < (B).length
               rw [← out.windowIsActual]
               exact lt_of_lt_of_le n.isLt out.withinWindow⟩
  have recordEq (k : ℕ) (hk : k < out.window.length) :
      (B)[k]'(by simpa only [out.windowIsActual] using hk) = out.window[k] :=
    List.getElem_of_eq out.windowIsActual.symm _
  have hc' : choice (B)[nb.val].input = some call := (recordEq n.val _) ▸ hc
  have hK := ReferenceFirstCollectionKnownSourceSplice.actual_first_collection_known_source_splice
    rate source rewards C_star C_h hcross count hspan hshort nb hn call hc' a
  dsimp only at hK
  obtain ⟨cut, suffix, r, q, base, headK, f0, proposal, hindex, _hrecords, _hwindow,
    _hstate, _hpay, _hinit, hheadK, _hcompleted, _hnext, validK, presentK,
    hDKlen, hDKzero, hDKread, _hcallPay, _hcallInit, _hcontext, _hchain, _hfold,
    _hHlen, _hIlen, _hTailLen, _hAt, _hRecords,
    oldLast, _hcut0, _hcut, hcurrent, _hinc, _hsum, _htail⟩ := hK
  let DK := ReferenceFirstCollectionCheckedSourcePrefix.readoutPrefix rate s B nb
    (ReferenceFirstCollectionCheckedSourcePrefix.sourceCell rate cut headK rewards validK) presentK
  change DK.length = n.val + 1 at hDKlen
  have hcutEq : cut = out.cutoff.cut := Option.some.inj (hindex.symm.trans out.cutoff.cutIndex)
  have hheadEq : headK = head := Option.some.inj ((hcutEq ▸ hheadK).symm.trans hhead)
  have hzero : DK[0]'(by omega) = D[0]'(by rw [hDlen]; have h := out.positiveLength; omega) :=
    hDKzero.trans ((source_cell_congr rate _ _ _ _ rewards validK valid hcutEq hheadEq).trans hDzero.symm)
  have hpref : DK = D.take (n.val + 1) := by
    have he := source_prefix_eq rate s out.window DK D (n.val + 1)
      (by omega) (by rw [hDlen]; exact n.isLt) (by have h := out.withinWindow; omega)
      (fun _ => hzero) (fun k hk => by
        let j : Fin nb.val := ⟨k.val - 1, by have hk' := k.isLt; change _ < n.val; omega⟩
        have hj : j.val + 1 = k.val := by dsimp only [j]; omega
        have h := hDKread j
        have hjB : j.val + 1 < (B).length :=
          Nat.lt_of_le_of_lt (Nat.succ_le_of_lt j.isLt) nb.isLt
        have hjD : j.val + 1 < DK.length := by
          rw [hDKlen]
          exact Nat.succ_lt_succ j.isLt
        change ReferenceLaterCollectionArrivalReadout.laterCollectionReadout s
          ((B)[j.val + 1]'hjB) = some (DK[j.val + 1]'hjD) at h
        have hkB : k.val < out.window.length := by
          have hk' := k.isLt
          have hn' := n.isLt
          have hw := out.withinWindow
          omega
        simpa only [hj, recordEq k.val hkB] using h)
      (fun k hk => hread ⟨k.val, by have hn := n.isLt; have hk := k.isLt; omega⟩ hk)
    simpa only [List.take_of_length_le (by omega : DK.length ≤ n.val + 1)] using he
  have ht (h : ℕ) (hh : h ≤ n.val + 1) : DK.take h = D.take h := by
    rw [hpref, List.take_take, Nat.min_eq_left hh]
  change call.preLedger.currentRegisters a.val = some
    ⟨(QueueReplay.replay (4 * rate.n) (0, 0) (arrivals rate a.val (Cells ++ DK.take n.val))).2,
      (QueueReplay.replay (4 * rate.n) (0, 0) (arrivals rate a.val (Cells ++ DK.take n.val))).1 -
      (QueueReplay.replay (4 * rate.n) (0, 0) (arrivals rate a.val (Cells ++ DK.take (n.val - 1)))).1⟩ at hcurrent
  simpa only [ht n.val (by omega), ht (n.val - 1) (by omega)] using hcurrent

private theorem stream_numerical
    (head : Choice rate)
    (valid : CoordinatorRecorderComplementBridge.LocalInputsValid
      (ReferenceActivePhysicalStep.collectionRecordingInput out.cutoff.cut.output.preparation
        head.payload head.started head.weights))
    (hhead : choice out.cutoff.cut.input = some head)
    (D : List (RecordedQueueRun.RoundInput p.K)) (hDlen : D.length = out.ell)
    (hDzero : D[0]'(by rw [hDlen]; have h := out.positiveLength; omega) =
      ReferenceFirstCollectionCheckedSourcePrefix.sourceCell rate out.cutoff.cut head rewards valid)
    (hread : ∀ k : Fin out.ell, 0 < k.val →
      ReferenceLaterCollectionArrivalReadout.laterCollectionReadout s
        (out.window[k.val]'(lt_of_lt_of_le k.isLt out.withinWindow)) =
        some (D[k.val]'(by rw [hDlen]; exact k.isLt)))
    (hrows : ∀ (k : Fin out.ell) (call : Choice rate),
      choice (out.window[k.val]'(lt_of_lt_of_le k.isLt out.withinWindow)).input = some call →
      ∀ a : Fin p.K,
      ReferenceCollectionRawBufferHistory.physicalQueueRecord call.preLedger a
        (out.window[k.val]'(lt_of_lt_of_le k.isLt out.withinWindow)) =
          ((D[k.val]'(by rw [hDlen]; exact k.isLt)).enabled,
            RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate)
              (D[k.val]'(by rw [hDlen]; exact k.isLt)) a)) :
    let V := fun a => QueueReplay.replay (4 * rate.n) (0, 0) (arrivals rate a Cells)
    let Vpre := fun a => QueueReplay.replay (4 * rate.n) (0, 0)
      (arrivals rate a ((Cells).take ((L).length - 1)))
    let R := fun a h => QueueReplay.replay (4 * rate.n) (0, 0)
      (arrivals rate a (Cells ++ D.take h))
    let I := fun a h => QueueReplay.replay (4 * rate.n) (0, (V a).2)
      (arrivals rate a (D.take h))
    ∀ (n : Fin out.ell) (a : Fin p.K),
      ¬ CoordinatorCollectionLedger.armPending (out.ledgers n) a →
      (out.ledgers n).cutoffRegisters a = some ⟨(V a).1, (V a).2, (V a).1 - (Vpre a).1⟩ ∧
      (out.ledgers n).currentRegisters a =
        some ⟨(R a (n.val + 1)).2, (R a (n.val + 1)).1 - (R a n.val).1⟩ ∧
      (out.ledgers n).increment a = (I a (n.val + 1)).1 ∧
      (V a).1 + (out.ledgers n).increment a = (R a (n.val + 1)).1 := by
  classical
  intro V Vpre R I
  have hrec : ∀ (k : ℕ) (hk : k < out.ell) (a : Fin p.K),
      ¬ CoordinatorCollectionLedger.armPending (out.ledgers ⟨k, hk⟩) a →
      (out.ledgers ⟨k, hk⟩).cutoffRegisters a = some ⟨(V a).1, (V a).2, (V a).1 - (Vpre a).1⟩ ∧
      (out.ledgers ⟨k, hk⟩).currentRegisters a = some ⟨(R a (k + 1)).2, (R a (k + 1)).1 - (R a k).1⟩ ∧
      (out.ledgers ⟨k, hk⟩).increment a = (I a (k + 1)).1 ∧
      (V a).1 + (out.ledgers ⟨k, hk⟩).increment a = (R a (k + 1)).1 := by
    intro k
    induction k with
    | zero =>
        intro hk a hnot
        have hledger : out.ledgers ⟨0, hk⟩ = out.cutoff.ledger := by
          rw [out.ledgers_are_outputs]
          rfl
        have hnotCut : ¬ CoordinatorCollectionLedger.armPending out.cutoff.ledger a := hledger ▸ hnot
        have houtside : a ∉ out.payload.slowSet.val := by
          intro ha
          rw [← CanonicalAssignmentVector.followerArm_image p.two_le_m out.payload.slowSet] at ha
          obtain ⟨i, _hi, hai⟩ := Finset.mem_image.mp ha
          apply hnotCut
          refine ⟨i, by rw [out.cutoffPendingUniv]; exact Finset.mem_univ _, ?_⟩
          rw [out.cutoffContext.2.2.2.1, ← out.payloadMatchesCutoff]
          exact hai
        let fast : CanonicalFastSampling.FastArm out.payload.slowSet :=
          ⟨a, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, houtside⟩⟩
        have hb := cutoff_fast_numerical rate source rewards C_star C_h hcross count hspan hshort
          out head valid hhead fast
        have hDpos : 0 < D.length := by rw [hDlen]; exact hk
        have hone : D.take 1 =
            [ReferenceFirstCollectionCheckedSourcePrefix.sourceCell rate out.cutoff.cut head rewards valid] := by
          rw [show 1 = 0 + 1 from rfl, List.take_succ_eq_append_getElem hDpos,
            List.take_zero, List.nil_append, hDzero]
        simpa only [hledger, V, Vpre, R, I, hone, List.take_zero, List.append_nil, fast] using hb
    | succ k ih =>
        intro hk a hnot
        let n : Fin out.ell := ⟨k + 1, hk⟩
        obtain ⟨j, record, incoming, cell, _hj, hr, hf, hprevious⟩ :=
          out.cell_at n (Nat.succ_pos _)
        have hrecord : out.window[n.val]'(lt_of_lt_of_le n.isLt out.withinWindow) = record :=
          (List.getElem?_eq_some_iff.mp hr).2
        clear hr
        subst record
        have hprev : incoming = out.ledgers ⟨k, by omega⟩ := by
          simpa only [n, Fin.val_mk, Nat.add_sub_cancel] using hprevious
        by_cases hp : CoordinatorCollectionLedger.armPending incoming a
        · cases hbranch : cell.branch with
          | rejected hreject result =>
              have hs : cell.serviceLedger = result.finished := by
                have h := cell.serviceLedgerIsBranch
                rw [hbranch] at h
                exact h
              apply False.elim
              apply hnot
              rcases hp with ⟨i, hi, hai⟩
              refine ⟨i, ?_, ?_⟩
              · change i ∈ (out.ledgers n).pending
                rw [← hf, hs, result.finished_pending]
                exact hi
              · change (out.ledgers n).assignment.arm i = a
                rw [← hf, hs, result.finished_assignment]
                exact hai
          | @accepted M hparse haccept result =>
              have hs : cell.serviceLedger = result.finished := by
                have h := cell.serviceLedgerIsBranch
                rw [hbranch] at h
                exact h
              have harm : incoming.assignment.arm (ReferenceActivePhysicalStep.upSenderIndex
                  (out.window[n.val]'(lt_of_lt_of_le n.isLt out.withinWindow)).input) = a := by
                rcases hp with ⟨i, hi, hai⟩
                by_cases he : i = ReferenceActivePhysicalStep.upSenderIndex
                    (out.window[n.val]'(lt_of_lt_of_le n.isLt out.withinWindow)).input
                · exact he ▸ hai
                · apply False.elim
                  apply hnot
                  refine ⟨i, ?_, ?_⟩
                  · rw [← hf, hs, result.finishedPending]
                    exact Finset.mem_erase.mpr ⟨he, hi⟩
                  · change (out.ledgers n).assignment.arm i = a
                    rw [← hf, hs, result.finishedContext.2.2.2.1]
                    exact hai
              have hcand : cell.started = CoordinatorCollectionLedger.startRoundCandidate incoming
                  (out.window[n.val]'(lt_of_lt_of_le n.isLt out.withinWindow)).input.time
                  (ReferenceActivePhysicalStep.collectionEnabled incoming
                    (out.window[n.val]'(lt_of_lt_of_le n.isLt out.withinWindow)).input.time)
                  (ReferenceCollectionRawBufferHistory.rawDiagnostic
                    (out.window[n.val]'(lt_of_lt_of_le n.isLt out.withinWindow))) := by
                simpa only [cell.choiceLedger] using cell.startedIsCandidate
              have hn := accepted_numerical rate source rewards C_star C_h hcross count hspan hshort
                out head valid hhead D hDlen hDzero hread n incoming cell.readyInput M
                (by rw [← hcand]; exact hparse) (by rw [← hcand]; exact haccept)
              simpa only [harm] using hn
        · have hold := ih (by omega) a (hprev ▸ hp)
          rw [← hprev] at hold
          obtain ⟨hcut, hcur, hinc, _hsum⟩ := hold
          have hcur' : incoming.currentRegisters a =
              some ⟨(R a (k + 1)).2, (R a (k + 1)).1 - (R a k).1⟩ := by
            by_cases ha : a ∈ out.payload.slowSet.val
            · exact hcur
            · let fast : CanonicalFastSampling.FastArm cell.choice.payload.slowSet :=
                ⟨a, by rw [cell.choicePayload]; exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ha⟩⟩
              have hfast := fast_incoming_numerical rate source rewards C_star C_h hcross count hspan hshort
                out head valid hhead D hDlen hDzero hread n (Nat.succ_pos _) cell.choice cell.actualChoice fast
              simpa only [cell.choiceLedger, n, Fin.val_mk, Nat.add_sub_cancel, fast] using hfast
          obtain ⟨completed, he⟩ := actual_collection_round_complete
            (out.window[n.val]'(lt_of_lt_of_le n.isLt out.withinWindow)) cell.choice
            out.payload cell.serviceLedger out.saved cell.actualChoice cell.serviceNextCoordinator
          obtain ⟨hc, hround, hchecked, payload', saved', hnext⟩ :=
            actual_collection_round_checked _ completed he
          have hcontext : completed.context = cell.choice :=
            Option.some.inj (hc.symm.trans cell.actualChoice)
          have hfinal : completed.final = cell.serviceLedger :=
            (ReferenceActivePhysicalStep.CoordinatorConfiguration.collection.inj
              (hnext.symm.trans cell.serviceNextCoordinator)).2.1
          have hchecked' : CollectionCheckedExecution.checkedRounds incoming [completed.input] =
              some ([completed.accepted], out.ledgers n) := by
            simpa only [hcontext, cell.choiceLedger, hfinal, hf] using hchecked
          have hraw := ReferenceCollectionRawBufferHistory.actual_completed_input_raw_and_enabled _ completed he
          have hlocal : CoordinatorCollectionLedger.localQueueRecord incoming completed.input.round
              completed.input.enabled completed.input.raw a =
              ReferenceCollectionRawBufferHistory.physicalQueueRecord cell.choice.preLedger a
                (out.window[n.val]'(lt_of_lt_of_le n.isLt out.withinWindow)) := by
            rw [hraw.1, hraw.2, hround, hcontext, cell.choiceLedger]
            obtain ⟨_, _, hSigma, _, _, _, _, _, _, _, _, hCursor, hCutCursor, _⟩ := cell.readyInput
            have hSigPos : 0 < incoming.sigma := hSigma
            have hcutBefore : incoming.cutoff ≤ (out.window[n.val]'(lt_of_lt_of_le n.isLt out.withinWindow)).input.time.val + 1 := by omega
            by_cases hbefore : (out.window[n.val]'(lt_of_lt_of_le n.isLt out.withinWindow)).input.time.val + 1 < incoming.freezeAt
            · simp [CoordinatorCollectionLedger.localQueueRecord,
                ReferenceCollectionRawBufferHistory.physicalQueueRecord,
                ReferenceActivePhysicalStep.collectionEnabled,
                CoordinatorCollectionLedger.sourceRound, hbefore, hSigPos, hcutBefore]
            · simp [CoordinatorCollectionLedger.localQueueRecord,
                ReferenceCollectionRawBufferHistory.physicalQueueRecord,
                CoordinatorCollectionLedger.sourceRound, hbefore]
          have hstep := known_source_step rate a Cells D (k + 1) (by rw [hDlen]; exact hk)
            incoming (out.ledgers n) completed.input completed.accepted
            ⟨(R a (k + 1)).2, (R a (k + 1)).1 - (R a k).1⟩ hcur' hchecked'
            (hlocal.trans (hrows n cell.choice cell.actualChoice a)) rfl hinc
          exact ⟨hstep.1.trans hcut, hstep.2⟩
  intro n a hn
  exact hrec n.val n.isLt a hn

private theorem stream_context (head : Choice rate)
    (hhead : choice out.cutoff.cut.input = some head) :
    (∀ n : Fin out.ell,
      CollectionBufferProvenance.collectionContext (out.ledgers n) =
        CollectionBufferProvenance.collectionContext head.preLedger) ∧
    (∀ (n : Fin out.ell) (call : Choice rate),
      choice (out.window[n.val]'(lt_of_lt_of_le n.isLt out.withinWindow)).input = some call →
      CollectionBufferProvenance.collectionContext call.preLedger =
        CollectionBufferProvenance.collectionContext head.preLedger) := by
  obtain ⟨completed, he⟩ := actual_collection_round_complete out.cutoff.cut head
    out.cutoff.payload out.cutoff.ledger out.cutoff.saved hhead out.cutoff.outputCoordinator
  obtain ⟨hc, _hround, hchecked, payload, saved, hnext⟩ :=
    actual_collection_round_checked _ completed he
  have hcontext : completed.context = head := Option.some.inj (hc.symm.trans hhead)
  have hfinal : completed.final = out.cutoff.ledger :=
    (ReferenceActivePhysicalStep.CoordinatorConfiguration.collection.inj
      (hnext.symm.trans out.cutoff.outputCoordinator)).2.1
  have hcutctx : CollectionBufferProvenance.collectionContext out.cutoff.ledger =
      CollectionBufferProvenance.collectionContext head.preLedger := by
    have h := CollectionBufferProvenance.checkedRounds_success_preserves_context
      completed.context.preLedger completed.final [completed.input] [completed.accepted] hchecked
    simpa only [hcontext, hfinal] using h
  have hout (n : Fin out.ell) : CollectionBufferProvenance.collectionContext (out.ledgers n) =
      CollectionBufferProvenance.collectionContext head.preLedger := by
    have h := out.context n
    have hc : CollectionBufferProvenance.collectionContext (out.ledgers n) =
        CollectionBufferProvenance.collectionContext out.cutoff.ledger := by
      simp only [CollectionBufferProvenance.collectionContext,
        h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2]
    exact hc.trans hcutctx
  refine ⟨hout, ?_⟩
  intro n call hc
  by_cases hz : n.val = 0
  · have hcall : call = head := by
      have hc' : choice out.cutoff.cut.input = some call := by
        simpa only [hz, out.cutoffIsHead] using hc
      exact Option.some.inj (hc'.symm.trans hhead)
    rw [hcall]
  · obtain ⟨j, record, incoming, cell, _hj, hr, _hf, hi⟩ := out.cell_at n (Nat.pos_of_ne_zero hz)
    have hrecord : out.window[n.val]'(lt_of_lt_of_le n.isLt out.withinWindow) = record :=
      (List.getElem?_eq_some_iff.mp hr).2
    have hcall : call = cell.choice := Option.some.inj ((hrecord ▸ hc).symm.trans cell.actualChoice)
    rw [hcall, cell.choiceLedger, hi]
    exact hout _

/-- Produce S's actual dispatch and one common chronological numerical source
prefix. Every known FINISH register is its original source replay; unknown
arms remain exactly the pending arms. The final all-arm equations follow only
at the actual empty-pending boundary. Exhaustion and dispatch alternatives are
retained in `d.outcome` without any new installation or budget assertion. -/
theorem actual_initialized_first_collection_all_arm_numerical_stream :
    ∃ d : ReferenceFirstCollectionStreamEmptyDispatch.ActualInitializedStreamDispatch
      (p := p) (rate := rate) source rewards C_star C_h count hcross hspan hshort,
    let out := d.stream
    ∃ (head : Choice rate) (initializer : Initializer p)
      (valid : CoordinatorRecorderComplementBridge.LocalInputsValid
        (ReferenceActivePhysicalStep.collectionRecordingInput out.cutoff.cut.output.preparation
          head.payload head.started head.weights))
      (D : List (RecordedQueueRun.RoundInput p.K)),
      choice out.cutoff.cut.input = some head ∧ head.payload = out.payload ∧
      head.initializer = some initializer ∧
      initializer.checkedStart rate = .success head.preLedger ∧
      ∃ hDlen : D.length = out.ell,
      D[0]'(by rw [hDlen]; have h := out.positiveLength; omega) =
        ReferenceFirstCollectionCheckedSourcePrefix.sourceCell rate out.cutoff.cut head rewards valid ∧
      let V := fun a => QueueReplay.replay (4 * rate.n) (0, 0) (arrivals rate a Cells)
      let Vpre := fun a => QueueReplay.replay (4 * rate.n) (0, 0)
        (arrivals rate a ((Cells).take ((L).length - 1)))
      let R := fun a h => QueueReplay.replay (4 * rate.n) (0, 0)
        (arrivals rate a (Cells ++ D.take h))
      let I := fun a h => QueueReplay.replay (4 * rate.n) (0, (V a).2) (arrivals rate a (D.take h))
      (∀ n : Fin out.ell,
        let record := out.window[n.val]'(lt_of_lt_of_le n.isLt out.withinWindow)
        let cell := D[n.val]'(by rw [hDlen]; exact n.isLt)
        ∃ (call : Choice rate)
          (validCall : CoordinatorRecorderComplementBridge.LocalInputsValid
            (ReferenceActivePhysicalStep.collectionRecordingInput record.output.preparation
              call.payload call.started call.weights)),
          choice record.input = some call ∧ call.payload = out.payload ∧
          CollectionBufferProvenance.collectionContext call.preLedger =
            CollectionBufferProvenance.collectionContext head.preLedger ∧
          cell = ReferenceFirstCollectionCheckedSourcePrefix.sourceCell rate record call rewards validCall ∧
          record.input.rows = source.1.2 ∧
          record.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p source ∧
          record.input.rewards = rewards ∧ record.input.time.val = s + (L).length + n.val ∧
          cell.enabled = ReferenceActivePhysicalStep.collectionEnabled call.preLedger record.input.time ∧
          cell.reward = (fun a => ((rewards record.input.time a).val : ℝ) /
            (ConstructorDimensions.D p : ℝ)) ∧ cell.rate = out.payload.rate ∧
          (∀ a : Fin p.K,
            ReferenceCollectionRawBufferHistory.physicalQueueRecord head.preLedger a record =
              (cell.enabled, RecordedQueueRun.quantizedArrival
                (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell a)) ∧
          (0 < n.val → ReferenceLaterCollectionArrivalReadout.laterCollectionReadout s record = some cell)) ∧
      (∀ h, h ≤ out.ell → ∀ a : Fin p.K,
        (out.window.take h).map (ReferenceCollectionRawBufferHistory.physicalQueueRecord head.preLedger a) =
          arrivals rate a (D.take h)) ∧
      (∀ n : Fin out.ell,
        let l := out.ledgers n
        let record := out.window[n.val]'(lt_of_lt_of_le n.isLt out.withinWindow)
        record.output.coordinator.failure = none ∧
        record.output.next.coordinator = .collection out.payload l out.saved ∧
        l.cursor = s + (L).length + 1 + n.val + 1 ∧
        CollectionBufferProvenance.collectionContext l =
          CollectionBufferProvenance.collectionContext head.preLedger ∧
        ∀ a : Fin p.K, l.gammaLoc a = 0 ∧
          (l.currentRegisters a = none ↔ CoordinatorCollectionLedger.armPending l a) ∧
          (l.cutoffRegisters a = none ↔ CoordinatorCollectionLedger.armPending l a) ∧
          (¬ CoordinatorCollectionLedger.armPending l a →
            l.cutoffRegisters a = some ⟨(V a).1, (V a).2, (V a).1 - (Vpre a).1⟩ ∧
            l.currentRegisters a = some ⟨(R a (n.val + 1)).2,
              (R a (n.val + 1)).1 - (R a n.val).1⟩ ∧
            l.increment a = (I a (n.val + 1)).1 ∧
            (V a).1 + l.increment a = (R a (n.val + 1)).1)) ∧
      (d.ledger.pending = ∅ → ∀ a : Fin p.K,
        d.ledger.cutoffRegisters a = some ⟨(V a).1, (V a).2, (V a).1 - (Vpre a).1⟩ ∧
        d.ledger.currentRegisters a = some ⟨(R a out.ell).2,
          (R a out.ell).1 - (R a (out.ell - 1)).1⟩ ∧
        d.ledger.increment a = (QueueReplay.replay (4 * rate.n) (0, (V a).2)
          (arrivals rate a D)).1 ∧
        (V a).1 + d.ledger.increment a = (R a out.ell).1) := by
  classical
  obtain ⟨d⟩ := ReferenceFirstCollectionStreamEmptyDispatch.actual_initialized_first_collection_stream_empty_dispatch
    rate source rewards C_star C_h count hcross hspan hshort
  let out := d.stream
  obtain ⟨head, initializer, valid, D, hhead, hpay, hinit, hchecked, hDlen, hzero, hcells⟩ :=
    stream_source_prefix rate source rewards C_star C_h hcross count hspan hshort out
  have hcontexts := stream_context rate source rewards C_star C_h hcross count hspan hshort out head hhead
  have hread (n : Fin out.ell) (hn : 0 < n.val) :
      ReferenceLaterCollectionArrivalReadout.laterCollectionReadout s
        (out.window[n.val]'(lt_of_lt_of_le n.isLt out.withinWindow)) =
          some (D[n.val]'(by rw [hDlen]; exact n.isLt)) := by
    obtain ⟨call, validCall, _hc, _hp, _he, _hr, _hj, _hreward, _ht,
      _henabled, _hcellReward, _hx, _hphysical, hread⟩ := hcells n
    exact hread hn
  have hrows (n : Fin out.ell) (call : Choice rate)
      (hc : choice (out.window[n.val]'(lt_of_lt_of_le n.isLt out.withinWindow)).input = some call)
      (a : Fin p.K) :
      ReferenceCollectionRawBufferHistory.physicalQueueRecord call.preLedger a
        (out.window[n.val]'(lt_of_lt_of_le n.isLt out.withinWindow)) =
          ((D[n.val]'(by rw [hDlen]; exact n.isLt)).enabled,
            RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate)
              (D[n.val]'(by rw [hDlen]; exact n.isLt)) a) := by
    obtain ⟨other, validOther, ho, _hp, _he, _hr, _hj, _hreward, _ht,
      _henabled, _hcellReward, _hx, hphysical, _hread⟩ := hcells n
    have heq : other = call := Option.some.inj (ho.symm.trans hc)
    simpa only [heq] using hphysical a
  have hnum := stream_numerical rate source rewards C_star C_h hcross count hspan hshort
    out head valid hhead D hDlen hzero hread hrows
  refine ⟨d, head, initializer, valid, D, hhead, hpay, hinit, hchecked, hDlen, hzero, ?_⟩
  dsimp only
  have hphysical (n : Fin out.ell) (a : Fin p.K) :
      ReferenceCollectionRawBufferHistory.physicalQueueRecord head.preLedger a
        (out.window[n.val]'(lt_of_lt_of_le n.isLt out.withinWindow)) =
          ((D[n.val]'(by rw [hDlen]; exact n.isLt)).enabled,
            RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate)
              (D[n.val]'(by rw [hDlen]; exact n.isLt)) a) := by
    obtain ⟨call, validCall, hc, _hp, _he, _hr, _hj, _hreward, _ht,
      _henabled, _hcellReward, _hx, hphysical, _hread⟩ := hcells n
    rw [← physical_record_context rate call.preLedger head.preLedger (hcontexts.2 n call hc) a]
    exact hphysical a
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n
    obtain ⟨call, validCall, hc, hp, he, hr, hj, hreward, ht,
      henabled, hcellReward, hx, _hphysical, hread⟩ := hcells n
    exact ⟨call, validCall, hc, hp, hcontexts.2 n call hc, he, hr, hj, hreward, ht,
      henabled, hcellReward, hx, hphysical n, hread⟩
  · intro h hh a
    change h ≤ out.ell at hh
    change (out.window.take h).map
      (ReferenceCollectionRawBufferHistory.physicalQueueRecord head.preLedger a) = arrivals rate a (D.take h)
    apply List.ext_getElem
    · simp only [arrivals, List.length_map, List.length_take,
        Nat.min_eq_left (hh.trans out.withinWindow),
        Nat.min_eq_left (by omega : h ≤ D.length)]
    · intro k hk _hk'
      have hkh : k < h := by
        have hlen : (out.window.take h).length = h := List.length_take_of_le (hh.trans out.withinWindow)
        simpa only [List.length_map, hlen] using hk
      simpa only [arrivals, List.getElem_map, List.getElem_take] using
        hphysical ⟨k, lt_of_lt_of_le hkh hh⟩ a
  · intro n
    obtain ⟨record, hr, hfail, hnext, hvalid, _hphase, hcursor, hgamma, _hcut, _hinc⟩ := out.output_properties n
    have heq : out.window[n.val]'(lt_of_lt_of_le n.isLt out.withinWindow) = record :=
      (List.getElem?_eq_some_iff.mp hr).2
    have htime := (out.alignment ⟨n.val, lt_of_lt_of_le n.isLt out.withinWindow⟩).2
    rw [heq] at htime
    change record.input.time.val + 1 = s + (L).length + 1 + n.val at htime
    refine ⟨heq ▸ hfail, heq ▸ hnext, ?_, hcontexts.1 n, ?_⟩
    · change (out.ledgers n).cursor = s + (L).length + 1 + n.val + 1
      omega
    · intro a
      exact ⟨hgamma a, (registers_pending rate _ hvalid a).1,
        (registers_pending rate _ hvalid a).2, hnum n a⟩
  · intro hempty a
    have hknown : ¬ CoordinatorCollectionLedger.armPending (out.ledgers d.last) a := by
      rintro ⟨i, hi, _⟩
      rw [← d.ledgerIsLast, hempty] at hi
      exact Finset.notMem_empty i hi
    have hn := hnum d.last a hknown
    have hlast' : d.last.val + 1 = out.ell := d.lastIsLast
    have hlast : d.last.val = out.ell - 1 := by omega
    have hledgerEq : out.ledgers d.last = d.ledger := d.ledgerIsLast.symm
    rw [hledgerEq] at hn
    rw [hlast', hlast] at hn
    refine ⟨hn.1, hn.2.1, ?_, hn.2.2.2⟩
    simpa only [List.take_of_length_le hDlen.le] using hn.2.2.1

end Actual

end Bandits.Support.ReferenceFirstCollectionAllArmNumericalStream

end
