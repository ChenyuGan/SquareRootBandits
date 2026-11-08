/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveStoppedHandoverSectionService
public import Bandits.Support.ReferenceFirstLiveStoppedReleaseSignedCost

/-!
# Initial handover and release chronology

The calendars below use the original complete physical execution. Missing
confirmations and pending release tasks remain distinct. Analytical stopping
only filters dates; it does not interrupt the physical execution.

Sources: ZIP4 `05_binary_transport.tex:244-345` and
`06_interruptions.tex:431-490`.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalStepMeasurability
open Bandits.Support.ReferenceAssignmentPayloadChronology
open Bandits.Support.ReferenceRetainedReleasePhaseObservation
open scoped Classical

namespace Bandits.Support.ReferenceFirstLiveInitialTransferChronology

variable {p : ConstructorDimensions.Parameters} {rate : ReferenceActivePhysicalStep.RateInput p}

private theorem frame_no_cutoff (x : RoundInput p rate)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r) (base : Fin (p.m - 1) → ℕ)
    (hc : x.state.coordinator = .live r q base)
    (hu : r.priorClock.u = none)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (hs : CoordinatorPhaseClock.startRound p rate.eta.val x.time r.priorClock
      r.clockPending = .ok started)
    (hf : CoordinatorLiveChoiceRecorderStep.unchangedLiveClockFrame
      (liveRegistersAt r x.time) started) :
    ReferenceCollectionPhaseHistory.cutoffChosen x = false := by
  have hd : (prepare x).coordinator = .live r q base
      (CoordinatorRoundDispatch.dispatchLive (liveInput x r q base)) := by
    simp only [prepare, dispatch, hc, CoordinatorRoundDispatch.dispatch]
    rfl
  unfold ReferenceCollectionPhaseHistory.cutoffChosen
  rw [hd]
  cases ho : CoordinatorRoundDispatch.dispatchLive (liveInput x r q base) with
  | cutoffChosen dispatched hstart ledger hinit hledger hvalid hclock hpending hnone selected =>
      have heq : dispatched.startResult = started := Except.ok.inj (hstart.symm.trans hs)
      have huframe : started.clock.u = r.priorClock.u := congrArg
        CoordinatorPhaseClock.ClockRegisters.u hf.1
      have hucut : dispatched.startResult.clock.u = some x.time := congrArg
        CoordinatorPhaseClock.ClockRegisters.u hclock
      rw [heq, huframe, hu] at hucut
      cases hucut
  | _ => rfl

private theorem gate_no_cutoff (x : RoundInput p rate) (b : ℕ)
    (hg : localReleaseGate rate b x.time (encodeState x.state) = true) :
    ReferenceCollectionPhaseHistory.cutoffChosen x = false := by
  obtain ⟨r, q, base, hc, _, _, _, hu⟩ := ReferenceLocalReleaseGateChronology.gate_live b x.time x.state hg
  have hgate := hg
  simp only [localReleaseGate, encodeState, encodeCoordinator, hc,
    Bool.and_eq_true, decide_eq_true_eq] at hgate
  have hlast := hgate.2
  cases hs : localReleaseStartResult rate x.time (encodeLive r q base) with
  | error failure => simp only [hs, Bool.false_eq_true] at hlast
  | ok started =>
      have hf : CoordinatorLiveChoiceRecorderStep.unchangedLiveClockFrame
          (liveRegistersAt r x.time) started := by
        have hf' : CoordinatorLiveChoiceRecorderStep.unchangedLiveClockFrame
            (decodeLiveRegisters r.payload (encodeLive r q base)) started := by
          simpa only [hs, decide_eq_true_eq] using hlast
        simpa only [CoordinatorLiveChoiceRecorderStep.unchangedLiveClockFrame,
          decodeLiveRegisters, encodeLive, liveRegistersAt,
          CoordinatorLiveChoiceRecorderStep.Registers.clockPending] using hf'
      exact frame_no_cutoff x r q base hc hu started hs hf

private theorem gate_of_frame (x : RoundInput p rate) (b : ℕ)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r) (base : Fin (p.m - 1) → ℕ)
    (hc : x.state.coordinator = .live r q base) (hb : r.payload.sigma.val = b)
    (he : r.pendingAtChoice = ∅) (hsigma : r.priorClock.sigma = some r.payload.sigma)
    (hu : r.priorClock.u = none) (started : CoordinatorPhaseClock.StartRoundResult p)
    (hs : CoordinatorPhaseClock.startRound p rate.eta.val x.time r.priorClock
      r.clockPending = .ok started)
    (hf : CoordinatorLiveChoiceRecorderStep.unchangedLiveClockFrame
      (liveRegistersAt r x.time) started) :
    localReleaseGate rate b x.time (encodeState x.state) = true := by
  have hs' : localReleaseStartResult rate x.time (encodeLive r q base) = .ok started := hs
  have hf' : CoordinatorLiveChoiceRecorderStep.unchangedLiveClockFrame
      (decodeLiveRegisters r.payload (encodeLive r q base)) started := by
    simpa only [CoordinatorLiveChoiceRecorderStep.unchangedLiveClockFrame,
      decodeLiveRegisters, encodeLive, liveRegistersAt,
      CoordinatorLiveChoiceRecorderStep.Registers.clockPending] using hf
  simp only [localReleaseGate, encodeState, encodeCoordinator, hc]
  change (decide (r.payload.sigma.val = b) && decide (r.pendingAtChoice = ∅) &&
    decide (r.priorClock.sigma = some r.payload.sigma) && decide (r.priorClock.u = none) &&
    (match localReleaseStartResult rate x.time (encodeLive r q base) with
      | .error _ => false
      | .ok result => decide (CoordinatorLiveChoiceRecorderStep.unchangedLiveClockFrame
          (decodeLiveRegisters r.payload (encodeLive r q base)) result))) = true
  rw [hs']
  simp only [hb, he, hsigma, hu, hf', decide_true, Bool.and_self]

section Run

variable (initial : State p rate) (rows : CompletePublicTable.CompleteRows p)
  (J : Fin (M p)) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (s : ℕ) (hactive : ReferenceActivePhysicalHorizon.allActiveAtStart initial s)
  (hfirst : initial.coordinator = .first)

include hfirst in
/-- Backward propagation stays on the same physical prefixes. The incoming
old payload and its empty-cutoff clock cannot cross a chosen cutoff. -/
private theorem old_live_prefix_no_cutoff (n : ℕ) (hspan : s + n ≤ p.T)
    (next : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters next) (base : Fin (p.m - 1) → ℕ)
    (hc : (ReferenceActivePhysicalHorizon.run initial rows J rewards s n hspan
      hactive).finalState.coordinator = .live next owned base)
    (hb : next.payload.sigma.val = s) (hu : next.priorClock.u = none) :
    ∀ (i : ℕ) (hi : i < n), ReferenceCollectionPhaseHistory.cutoffChosen
      (actualRunRecordAt initial rows J rewards s i (by omega) hactive).input = false := by
  induction n generalizing next owned base with
  | zero => intro i hi; omega
  | succ n ih =>
      let record := actualRunRecordAt initial rows J rewards s n hspan hactive
      have hout : (step record.input).next.coordinator = .live next owned base := by
        rw [run_successor_finalState_eq_actualRunRecordAt] at hc
        exact hc
      by_cases hn : n = 0
      · subst n
        intro i hi
        have hi0 : i = 0 := by omega
        subst i
        have hstate : (actualRunRecordAt initial rows J rewards s 0 (by omega)
            hactive).input.state.coordinator = .first := by
          simpa only [actualRunRecordAt, ReferenceActivePhysicalHorizon.roundInputAt,
            ReferenceActivePhysicalHorizon.run_zero_final] using hfirst
        simp only [ReferenceCollectionPhaseHistory.cutoffChosen, prepare, dispatch,
          hstate, CoordinatorRoundDispatch.dispatch]
        cases CoordinatorRoundDispatch.dispatchFirst
          (firstInput (actualRunRecordAt initial rows J rewards s 0 (by omega) hactive).input)
          <;> rfl
      · obtain ⟨r, q, oldBase, hr, hrb, started, hs, hf, _, _, _, hcutoff⟩ :=
          ReferenceLocalReleaseGateChronology.step_old_live_predecessor record.input s next owned base hout hb (by
            change s < s + n
            omega)
        have hru : r.priorClock.u = none := hcutoff.symm.trans hu
        have hprefix : (ReferenceActivePhysicalHorizon.run initial rows J rewards s n
            (by omega) hactive).finalState.coordinator = .live r q oldBase := hr
        have hprevious := ih (by omega) r q oldBase hprefix hrb hru
        intro i hi
        by_cases hin : i < n
        · exact hprevious i hin
        · have hieq : i = n := by omega
          subst i
          exact frame_no_cutoff record.input r q oldBase hr hru started hs hf

end Run

private theorem indexed_mem_takeWhile {α : Type*} (pred : α → Bool)
    (xs : List α) (j : Fin xs.length)
    (h : ∀ i : Fin xs.length, i.val ≤ j.val → pred xs[i.val] = true) :
    xs[j.val] ∈ xs.takeWhile pred := by
  induction xs with
  | nil => exact Fin.elim0 j
  | cons a xs ih =>
      have hhead : pred a = true := h ⟨0, by simp⟩ (Nat.zero_le _)
      simp only [List.takeWhile_cons, hhead, ↓reduceIte]
      cases j using Fin.cases with
      | zero => exact List.mem_cons_self
      | succ j =>
          apply List.mem_cons_of_mem
          exact ih j (fun i hi => h i.succ (Nat.succ_le_succ hi))

section Context

variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)

local notation "Source" => BootstrapPrivateRoundStreams.SourceInput p
local notation "W" => ReferenceFirstLiveSourceStoppedHandoverEndpoint.window rate rewards C_star C_h
local notation "s" => ReferenceFirstLiveSourceStoppedReleaseEndpoint.physicalStart rate rewards C_star C_h

private theorem window_crossing (z : Source) (hne : 0 < (W z).length) :
    (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true := by
  cases hl : ReferenceCorrectedInitializationLaunch.correctedLaunch rate z rewards C_star C_h with
  | none =>
      rw [ReferenceFirstLiveSourceStoppedHandoverEndpoint.window_eq_nil_of_no_launch
        rate rewards C_star C_h z hl] at hne
      simp at hne
  | some active =>
      apply (ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
        rate z rewards C_star C_h).mp
      simp only [hl, Option.isSome_some]

private theorem window_clock (z : Source) (k : Fin (W z).length) :
    ReferenceCoordinatorClockDomains.clockAt z.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p z)
      ((W z).get k).input.time.val ((W z).get k).input.state := by
  have hcross := window_crossing rate rewards C_star C_h z (by have := k.isLt; omega)
  let initial := ReferenceLocalReleaseGateChronology.sourceSeed rate z rewards C_star C_h hcross
  have hseed := ReferenceLocalReleaseGateChronology.canonical_seed_release_inputs
    rate z rewards C_star C_h hcross
  have hspan : s z + (p.T - s z) ≤ p.T := by
    have hs : s z ≤ p.T :=
      ReferenceCompletePhysicalHistory.physicalStart_le_T rate z rewards C_star C_h
    omega
  let run := ReferenceActivePhysicalHorizon.run initial z.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards (s z) (p.T - s z)
    hspan hseed.2.1
  have hcomplete : run.records =
      ReferenceFirstLiveSourceStoppedHandoverEndpoint.completeRecords rate rewards C_star C_h z :=
    (ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch rate z rewards C_star C_h
      initial (ReferenceLocalReleaseGateChronology.sourceSeed_launch
        rate z rewards C_star C_h hcross)).symm
  have hprefix : W z <+: run.records := by
    rw [hcomplete]
    exact List.takeWhile_prefix _
  have hmem : (W z).get k ∈ run.records :=
    hprefix.subset (List.get_mem _ _)
  have hfirst : initial.coordinator = .first := hseed.1
  have hclock := ReferenceRunClockPreservation.run_clockAt initial z.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards (s z) (p.T - s z)
    hspan hseed.2.1 (by
      simp only [ReferenceCoordinatorClockDomains.clockAt, hfirst])
  exact (hclock.2.2.2 ((W z).get k) hmem).1

private theorem gate_record_mem_window (z : Source)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true)
    (record : ReferenceFirstLiveSourceStoppedHandoverEndpoint.Record (rate := rate))
    (hrecord : record ∈ ReferenceFirstLiveSourceStoppedHandoverEndpoint.completeRecords
      rate rewards C_star C_h z)
    (hg : localReleaseGate rate (s z) record.input.time
      (encodeState record.input.state) = true) : record ∈ W z := by
  let initial := ReferenceLocalReleaseGateChronology.sourceSeed rate z rewards C_star C_h hcross
  have hseed := ReferenceLocalReleaseGateChronology.canonical_seed_release_inputs
    rate z rewards C_star C_h hcross
  have hs : s z ≤ p.T :=
    ReferenceCompletePhysicalHistory.physicalStart_le_T rate z rewards C_star C_h
  let count := p.T - s z
  have hspan : s z + count ≤ p.T := by dsimp only [count]; omega
  let run := ReferenceActivePhysicalHorizon.run initial z.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards (s z) count hspan hseed.2.1
  have hcomplete : run.records =
      ReferenceFirstLiveSourceStoppedHandoverEndpoint.completeRecords rate rewards C_star C_h z :=
    (ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch rate z rewards C_star C_h
      initial (ReferenceLocalReleaseGateChronology.sourceSeed_launch
        rate z rewards C_star C_h hcross)).symm
  have hmem : record ∈ run.records := hcomplete.symm ▸ hrecord
  obtain ⟨j, hj, heq⟩ := List.mem_iff_getElem.mp hmem
  have hcount : run.records.length = count :=
    ReferenceActivePhysicalHorizon.run_record_count _ _ _ _ _ _ _ _
  have hjcount : j < count := by omega
  have hget := ReferenceLocalReleaseGateChronology.run_record_at initial z.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards (s z) hseed.2.1
    count hspan ⟨j, hjcount⟩
  have hactual : actualRunRecordAt initial z.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards (s z) j
      (by omega) hseed.2.1 = record := hget.symm.trans heq
  obtain ⟨payload, birth, hstored, _, hstamp, _, _, _, _, _⟩ :=
    ReferenceLocalReleaseGateChronology.source_gate_birth_and_payload_chronology
      rate z rewards C_star C_h hcross (s z) count rfl hspan (s z)
      record hmem record hmem hg hg
  obtain ⟨r, q, base, hc, _, _, _, hu⟩ :=
    ReferenceLocalReleaseGateChronology.gate_live (s z) _ _ hg
  have hpayload : r.payload = payload := by
    rw [hc] at hstored
    exact Option.some.inj hstored
  have hb : r.payload.sigma.val = s z :=
    (congrArg (fun payload => payload.sigma.val) hpayload).trans hstamp
  have hprior : (ReferenceActivePhysicalHorizon.run initial z.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards (s z) j
      (by omega) hseed.2.1).finalState.coordinator = .live r q base := by
    change (actualRunRecordAt initial z.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards (s z) j
      (by omega) hseed.2.1).input.state.coordinator = _
    rw [hactual]
    exact hc
  have hprevious := old_live_prefix_no_cutoff initial z.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards (s z) hseed.2.1 hseed.1
    j (by omega) r q base hprior hb hu
  have hcurrent := gate_no_cutoff record.input (s z) hg
  have hw : record ∈ run.records.takeWhile
      (fun r => !ReferenceCollectionPhaseHistory.cutoffChosen r.input) := by
    rw [← heq]
    apply indexed_mem_takeWhile _ run.records ⟨j, hj⟩
    intro i hi
    change i.val ≤ j at hi
    have hgeti := ReferenceLocalReleaseGateChronology.run_record_at initial z.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards (s z) hseed.2.1
      count hspan ⟨i.val, by rw [← hcount]; exact i.isLt⟩
    by_cases hij : i.val < j
    · rw [hgeti, hprevious i.val hij]
      rfl
    · have hieq : i.val = j := by omega
      have hir : run.records[i.val] = record := by simpa only [hieq] using heq
      rw [hir, hcurrent]
      rfl
  change record ∈ (ReferenceFirstLiveSourceStoppedHandoverEndpoint.completeRecords
    rate rewards C_star C_h z).takeWhile _
  rw [← hcomplete]
  exact hw

private theorem window_gate_iff_missing_empty (z : Source) (k : Fin (W z).length) :
    localReleaseGate rate (s z) ((W z).get k).input.time
      (encodeState ((W z).get k).input.state) = true ↔
      ReferenceFirstLiveSourceStoppedHandoverEndpoint.missing rate ((W z).get k) = ∅ := by
  have hcross := window_crossing rate rewards C_star C_h z (by have := k.isLt; omega)
  have hprov := ReferenceFirstLiveSourceStoppedHandoverEndpoint.source_window_provenance
    rate rewards C_star C_h z hcross
  dsimp only at hprov
  rcases hprov with hzero | ⟨hW, installed, firstSelected, _, hinstall, _, _, _, hrows⟩
  · have := k.isLt
    omega
  · have hstamp : installed.registers.payload.sigma.val = s z := by
      rw [hinstall]
      change ((W z).get ⟨0, hW⟩).input.time.val = s z
      exact (ReferenceFirstLiveSourceStoppedHandoverEndpoint.source_window_record_calendar
        rate rewards C_star C_h z ⟨0, hW⟩).1.trans (Nat.add_zero _)
    obtain ⟨selected, hselected, hpayload, hphase, next, owned, base,
      hnext, hpnext, _⟩ := hrows k
    have hm : ReferenceFirstLiveSourceStoppedHandoverEndpoint.missing rate ((W z).get k) =
        selected.view.pendingAtChoice := by
      unfold ReferenceFirstLiveSourceStoppedHandoverEndpoint.missing
        ReferenceFirstLiveSourceStoppedHandoverEndpoint.actualSelection
      rw [hselected]
      rfl
    have hclock := window_clock rate rewards C_star C_h z k
    cases hc : ((W z).get k).input.state.coordinator with
    | first =>
        rw [hc] at hphase
        rw [hm, hphase]
        have hne : (Finset.univ : Finset (Fin (p.m - 1))) ≠ ∅ := by
          apply Finset.Nonempty.ne_empty
          exact ⟨⟨0, by have := p.two_le_m; omega⟩, Finset.mem_univ _⟩
        simp only [localReleaseGate, encodeState, encodeCoordinator, hc, Bool.false_eq_true]
        exact ⟨False.elim, fun h => hne h⟩
    | collection payload ledger proposal => rw [hc] at hphase; exact hphase.elim
    | dagger => rw [hc] at hphase; exact hphase.elim
    | live incoming incomingOwned incomingBase =>
        rw [hc] at hphase
        simp only [ReferenceCoordinatorClockDomains.clockAt, hc] at hclock
        have hb : incoming.payload.sigma.val = s z :=
          (congrArg (fun payload => payload.sigma.val) hphase.1.symm).trans
            ((congrArg (fun payload => payload.sigma.val) hpayload).trans hstamp)
        have hnextstamp : next.payload.sigma.val = s z :=
          (congrArg (fun payload => payload.sigma.val) hpnext).trans
            ((congrArg (fun payload => payload.sigma.val) hpayload).trans hstamp)
        have hout : (step ((W z).get k).input).next.coordinator = .live next owned base := by
          rw [← ((W z).get k).output_eq]
          exact hnext
        obtain ⟨r, q, oldBase, hr, hrb, started, hs, hf, hsigma, _⟩ :=
          ReferenceLocalReleaseGateChronology.step_old_live_predecessor ((W z).get k).input
            (s z) next owned base hout hnextstamp (by rw [← hb]; exact hclock.2.2.2.2.2.1)
        rw [hc] at hr
        cases hr
        constructor
        · intro hg
          obtain ⟨r, q, oldBase, hr, _, he, _⟩ :=
            ReferenceLocalReleaseGateChronology.gate_live (s z) _ _ hg
          rw [hc] at hr
          cases hr
          exact hm.trans (hphase.2.trans he)
        · intro hempty
          have he : incoming.pendingAtChoice = ∅ := hphase.2.symm.trans (hm.symm.trans hempty)
          exact gate_of_frame ((W z).get k).input (s z) incoming incomingOwned incomingBase
            hc hb he hsigma hclock.2.2.2.1 started hs hf

/-- Every raw gate, including gates with no release tasks left, is exactly an
empty-confirmation record in the actual first-live window. -/
theorem raw_release_calendar (z : Source) :
    ReferenceFirstLiveSourceStoppedReleaseEndpoint.actualGateSupport rate rewards C_star C_h z =
      ((W z).toFinset.filter (fun r =>
        ReferenceFirstLiveSourceStoppedHandoverEndpoint.missing rate r = ∅)).image
          (fun r => r.input.time.val + 1) := by
  cases hl : ReferenceCorrectedInitializationLaunch.correctedLaunch rate z rewards C_star C_h with
  | none =>
      have hno := ReferenceCompletePhysicalHistory.no_launch_complete_history
        rate z rewards C_star C_h hl
      have hw := ReferenceFirstLiveSourceStoppedHandoverEndpoint.window_eq_nil_of_no_launch
        rate rewards C_star C_h z hl
      simp only [ReferenceFirstLiveSourceStoppedReleaseEndpoint.actualGateSupport,
        ReferenceFirstLiveSourceStoppedReleaseEndpoint.completeRecords, hno.2.1,
        ReferenceLocalReleaseGateChronology.gateSupport, List.filter_nil, List.map_nil,
        List.toFinset_nil, hw, Finset.filter_empty, Finset.image_empty]
  | some active =>
      have hcross := (ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
        rate z rewards C_star C_h).mp (by simp only [hl, Option.isSome_some])
      ext v
      constructor
      · intro hv
        obtain ⟨record, hrecord, hg, hdate⟩ :=
          (ReferenceLocalReleaseGateChronology.mem_gateSupport (s z) v _).mp hv
        have hw := gate_record_mem_window rate rewards C_star C_h z hcross record hrecord hg
        obtain ⟨j, hj, heq⟩ := List.mem_iff_getElem.mp hw
        have he : ReferenceFirstLiveSourceStoppedHandoverEndpoint.missing rate record = ∅ := by
          have he := (window_gate_iff_missing_empty rate rewards C_star C_h z ⟨j, hj⟩).mp
            (by simpa only [List.get_eq_getElem, heq] using hg)
          simpa only [List.get_eq_getElem, heq] using he
        exact Finset.mem_image.mpr ⟨record,
          Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hw, he⟩, hdate⟩
      · intro hv
        obtain ⟨record, hrecord, hdate⟩ := Finset.mem_image.mp hv
        obtain ⟨hrecord, he⟩ := Finset.mem_filter.mp hrecord
        obtain ⟨j, hj, heq⟩ := List.mem_iff_getElem.mp (List.mem_toFinset.mp hrecord)
        have hg : localReleaseGate rate (s z) record.input.time
            (encodeState record.input.state) = true := by
          have hg := (window_gate_iff_missing_empty rate rewards C_star C_h z ⟨j, hj⟩).mpr
            (by simpa only [List.get_eq_getElem, heq] using he)
          simpa only [List.get_eq_getElem, heq] using hg
        apply (ReferenceLocalReleaseGateChronology.mem_gateSupport (s z) v _).mpr
        have hprefix : W z <+:
            ReferenceFirstLiveSourceStoppedHandoverEndpoint.completeRecords rate rewards C_star C_h z :=
          List.takeWhile_prefix _
        exact ⟨record, hprefix.subset (List.mem_toFinset.mp hrecord), hg, hdate⟩

local notation "missing" => ReferenceFirstLiveSourceStoppedHandoverEndpoint.missing rate
local notation "SH" => ReferenceFirstLiveSourceStoppedHandoverEndpoint.supportDates rate rewards C_star C_h
local notation "SR" => ReferenceFirstLiveSourceStoppedReleaseEndpoint.actualFirstReleaseSupport rate rewards C_star C_h
local notation "excluded" => ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstExcluded rate rewards C_star C_h
local notation "sigR" => ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstReleaseSigma rate rewards C_star C_h
local notation "thH" => ReferenceFirstLiveSourceStoppedHandoverEndpoint.theta rate rewards C_star C_h

/-- All actual initial-transfer dates before the first excluded source date. -/
def stoppedInitialDates (z : Source) : Finset ℕ :=
  (((W z).map (fun r => r.input.time.val + 1)).toFinset).filter (fun v => v < excluded z)

private theorem release_mem_iff (z : Source) (v : ℕ) :
    v ∈ SR z ↔ ∃ k : Fin (W z).length,
      (W z)[k.val].input.time.val + 1 = v ∧ missing (W z)[k.val] = ∅ ∧ v < excluded z := by
  rw [ReferenceFirstLiveSourceStoppedReleaseEndpoint.actualFirstReleaseSupport,
    raw_release_calendar rate rewards C_star C_h z]
  constructor
  · intro hv
    obtain ⟨hv, hstop⟩ := Finset.mem_filter.mp hv
    obtain ⟨record, hrecord, hdate⟩ := Finset.mem_image.mp hv
    obtain ⟨hrecord, hempty⟩ := Finset.mem_filter.mp hrecord
    obtain ⟨j, hj, heq⟩ := List.mem_iff_getElem.mp (List.mem_toFinset.mp hrecord)
    exact ⟨⟨j, hj⟩, by simpa only [heq] using hdate,
      by simpa only [heq] using hempty, hstop⟩
  · rintro ⟨k, hdate, hempty, hstop⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨(W z)[k.val],
      Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr (List.getElem_mem k.isLt), hempty⟩,
      hdate⟩, hstop⟩

private theorem initial_mem_iff (z : Source) (v : ℕ) :
    v ∈ stoppedInitialDates rate rewards C_star C_h z ↔
      ∃ k : Fin (W z).length, (W z)[k.val].input.time.val + 1 = v ∧ v < excluded z := by
  constructor
  · intro hv
    obtain ⟨hv, hstop⟩ := Finset.mem_filter.mp hv
    obtain ⟨record, hrecord, hdate⟩ := List.mem_map.mp (List.mem_toFinset.mp hv)
    obtain ⟨j, hj, heq⟩ := List.mem_iff_getElem.mp hrecord
    exact ⟨⟨j, hj⟩, by simpa only [heq] using hdate, hstop⟩
  · rintro ⟨k, hdate, hstop⟩
    exact Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr
      (List.mem_map.mpr ⟨(W z)[k.val], List.getElem_mem k.isLt, hdate⟩), hstop⟩

private theorem launch_date (z : Source) :
    ReferenceInitializationRun.launchRound
      (ReferenceCompletePhysicalHistory.generatedInput rate z rewards C_star C_h) = s z + 1 := by
  cases hl : ReferenceCorrectedInitializationLaunch.correctedLaunch rate z rewards C_star C_h with
  | none =>
      have hL := ReferenceCompletePhysicalHistory.no_launch_sentinel_round
        rate z rewards C_star C_h hl
      have hs : s z = p.T :=
        ReferenceCompletePhysicalHistory.correctedLaunch_none_start_eq_T
          rate z rewards C_star C_h hl
      rw [hL, hs]
  | some active =>
      have hcross := (ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
        rate z rewards C_star C_h).mp (by simp only [hl, Option.isSome_some])
      change (if (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome
        then s z + 1 else p.T + 1) = s z + 1
      rw [hcross]
      rfl

private theorem initial_dates_interval (z : Source) :
    stoppedInitialDates rate rewards C_star C_h z =
      Finset.Ico (ReferenceInitializationRun.launchRound
        (ReferenceCompletePhysicalHistory.generatedInput rate z rewards C_star C_h))
        (min (s z + (W z).length + 1) (excluded z)) := by
  rw [launch_date rate rewards C_star C_h z]
  ext v
  rw [initial_mem_iff, Finset.mem_Ico, lt_min_iff]
  constructor
  · rintro ⟨k, hdate, hstop⟩
    have htime := (ReferenceFirstLiveSourceStoppedHandoverEndpoint.source_window_record_calendar
      rate rewards C_star C_h z k).1
    have hk := k.isLt
    exact ⟨by omega, by omega, hstop⟩
  · rintro ⟨hstart, hend, hstop⟩
    have hk : v - (s z + 1) < (W z).length := by omega
    let k : Fin (W z).length := ⟨v - (s z + 1), hk⟩
    have htime := (ReferenceFirstLiveSourceStoppedHandoverEndpoint.source_window_record_calendar
      rate rewards C_star C_h z k).1
    refine ⟨k, ?_, hstop⟩
    dsimp only [k, Fin.val_mk] at htime ⊢
    omega

private theorem hand_before_release (z : Source) (h : ℕ) (hh : h ∈ SH z)
    (r : ℕ) (hr : r ∈ SR z) : h < r := by
  obtain ⟨i, hidate, himissing, _⟩ :=
    (ReferenceFirstLiveSourceStoppedHandoverEndpoint.supportDates_mem_iff
      rate rewards C_star C_h z h).mp hh
  obtain ⟨j, hjdate, hjmissing, _⟩ := (release_mem_iff rate rewards C_star C_h z r).mp hr
  have htimei := (ReferenceFirstLiveSourceStoppedHandoverEndpoint.source_window_record_calendar
    rate rewards C_star C_h z i).1
  have htimej := (ReferenceFirstLiveSourceStoppedHandoverEndpoint.source_window_record_calendar
    rate rewards C_star C_h z j).1
  by_contra hnot
  have hji : j.val ≤ i.val := by omega
  have hempty := ReferenceFirstLiveSourceStoppedHandoverEndpoint.source_window_missing_empty_persistent
    rate rewards C_star C_h z j i hji hjmissing
  exact himissing.ne_empty hempty

/-- The stopped handover and release supports partition the same consecutive
initial calendar. Every handover date strictly precedes every release date. -/
theorem stopped_initial_calendar (z : Source) :
    Disjoint (SH z) (SR z) ∧
      SH z ∪ SR z = stoppedInitialDates rate rewards C_star C_h z ∧
      stoppedInitialDates rate rewards C_star C_h z =
        Finset.Ico (ReferenceInitializationRun.launchRound
          (ReferenceCompletePhysicalHistory.generatedInput rate z rewards C_star C_h))
          (min (s z + (W z).length + 1) (excluded z)) ∧
      ∀ h ∈ SH z, ∀ r ∈ SR z, h < r := by
  refine ⟨?_, ?_, initial_dates_interval rate rewards C_star C_h z,
    hand_before_release rate rewards C_star C_h z⟩
  · apply Finset.disjoint_left.mpr
    intro v hh hr
    exact (Nat.lt_irrefl v) (hand_before_release rate rewards C_star C_h z v hh v hr)
  · ext v
    rw [Finset.mem_union, initial_mem_iff]
    constructor
    · rintro (hh | hr)
      · obtain ⟨k, hdate, _, hstop⟩ :=
          (ReferenceFirstLiveSourceStoppedHandoverEndpoint.supportDates_mem_iff
            rate rewards C_star C_h z v).mp hh
        exact ⟨k, hdate, hstop⟩
      · obtain ⟨k, hdate, _, hstop⟩ := (release_mem_iff rate rewards C_star C_h z v).mp hr
        exact ⟨k, hdate, hstop⟩
    · rintro ⟨k, hdate, hstop⟩
      by_cases hempty : missing (W z)[k.val] = ∅
      · exact Or.inr ((release_mem_iff rate rewards C_star C_h z v).mpr
          ⟨k, hdate, hempty, hstop⟩)
      · exact Or.inl ((ReferenceFirstLiveSourceStoppedHandoverEndpoint.supportDates_mem_iff
          rate rewards C_star C_h z v).mpr ⟨k, hdate, Finset.nonempty_iff_ne_empty.mpr hempty, hstop⟩)

private theorem first_release_predecessor (z : Source) (hne : (SR z).Nonempty) :
    ∃ (k : Fin (W z).length) (hk : k.val + 1 < (W z).length),
      (W z)[k.val].input.time.val + 1 ∈ SH z ∧
      (W z)[k.val].input.time.val + 1 + 1 = sigR z ∧
      missing ((W z)[k.val + 1]'hk) = ∅ := by
  have hinterval := ReferenceFirstLiveSourceStoppedReleaseEndpoint.actual_first_release_interval
    rate rewards C_star C_h z
  obtain ⟨v, hv⟩ := hne
  have hvI := Finset.mem_Ico.mp (hinterval.1 ▸ hv)
  have hsigma : sigR z ∈ SR z := by
    rw [hinterval.1]
    exact Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩
  obtain ⟨j, hjdate, hjempty, hjstop⟩ := (release_mem_iff rate rewards C_star C_h z _).mp hsigma
  have hW : 0 < (W z).length := by have := j.isLt; omega
  have hjpos : 0 < j.val := by
    by_contra hn
    have hjzero : j.val = 0 := by omega
    have hm0 := ReferenceFirstLiveSourceStoppedHandoverEndpoint.source_window_initial_missing
      rate rewards C_star C_h z hW
    have hmu : missing (W z)[j.val] = Finset.univ := by
      simpa only [List.get_eq_getElem, hjzero] using hm0
    have hnonempty : (Finset.univ : Finset (Fin (p.m - 1))).Nonempty :=
      ⟨⟨0, by have := p.two_le_m; omega⟩, Finset.mem_univ _⟩
    exact hnonempty.ne_empty (hmu.symm.trans hjempty)
  let k : Fin (W z).length := ⟨j.val - 1, by have := j.isLt; omega⟩
  have hkj : k.val + 1 = j.val := by dsimp only [k, Fin.val_mk]; omega
  have hk : k.val + 1 < (W z).length := by rw [hkj]; exact j.isLt
  have htimej := (ReferenceFirstLiveSourceStoppedHandoverEndpoint.source_window_record_calendar
    rate rewards C_star C_h z j).1
  have htimek := (ReferenceFirstLiveSourceStoppedHandoverEndpoint.source_window_record_calendar
    rate rewards C_star C_h z k).1
  have hkdate : (W z)[k.val].input.time.val + 1 + 1 = sigR z := by omega
  have hkstop : (W z)[k.val].input.time.val + 1 < excluded z := by omega
  have hkmissing : (missing (W z)[k.val]).Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro hempty
    have hr := (release_mem_iff rate rewards C_star C_h z
      ((W z)[k.val].input.time.val + 1)).mpr ⟨k, rfl, hempty, hkstop⟩
    have hlo := (Finset.mem_Ico.mp (hinterval.1 ▸ hr)).1
    omega
  refine ⟨k, hk, ?_, hkdate, ?_⟩
  · exact (ReferenceFirstLiveSourceStoppedHandoverEndpoint.supportDates_mem_iff
      rate rewards C_star C_h z _).mpr ⟨k, rfl, hkmissing, hkstop⟩
  · simpa only [hkj] using hjempty

private theorem nonempty_release_boundary (z : Source) (hne : (SR z).Nonempty) :
    (SH z).Nonempty ∧ thH z = sigR z := by
  obtain ⟨k, hk, hd, hdate, hempty⟩ := first_release_predecessor rate rewards C_star C_h z hne
  have hend := ReferenceFirstLiveSourceStoppedHandoverEndpoint.last_confirmation_endpoint
    rate rewards C_star C_h z k.val hk hd hempty
  exact ⟨⟨_, hd⟩, hend.1.trans (by omega)⟩

/-- The handover endpoint precedes release. Equality is asserted only when
an actual stopped release round exists. -/
theorem initial_phase_boundary (z : Source) :
    thH z ≤ sigR z ∧ (SH z = ∅ → SR z = ∅) ∧
      ((SR z).Nonempty → (SH z).Nonempty ∧ thH z = sigR z) := by
  have hnonempty := nonempty_release_boundary rate rewards C_star C_h z
  refine ⟨?_, ?_, hnonempty⟩
  · by_cases hR : (SR z).Nonempty
    · exact (hnonempty hR).2.le
    · have hRempty := Finset.not_nonempty_iff_eq_empty.mp hR
      have hend := ReferenceFirstLiveSourceStoppedReleaseEndpoint.empty_first_release_endpoints
        rate rewards C_star C_h z hRempty
      rw [hend.1]
      exact (ReferenceFirstLiveSourceStoppedHandoverEndpoint.sigma_theta_bounds
        rate rewards C_star C_h z).2.2
  · intro hH
    apply Finset.not_nonempty_iff_eq_empty.mp
    intro hR
    have hh := (hnonempty hR).1
    rw [hH] at hh
    exact Finset.not_nonempty_empty hh

/-- The first release date is immediately after an actual positive DOWN
confirmation of the sole remaining follower on the original selected row. -/
theorem last_confirmation_before_release (z : Source) (hne : (SR z).Nonempty) :
    ∃ k : Fin (W z).length, k.val + 1 < (W z).length ∧
      ((W z).get k).input.time.val + 1 ∈ SH z ∧
      ((W z).get k).input.time.val + 1 + 1 = sigR z ∧
      ∃ selected : ReferenceActivePhysicalStep.Selection ((W z).get k).input,
        ReferenceFirstLiveSourceStoppedHandoverEndpoint.actualSelection rate ((W z).get k) =
          some selected ∧
        ReferenceFirstLiveMissingSetProvenance.actualDownConfirmationEvent ((W z).get k) selected ∧
        missing ((W z).get k) =
          {PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
            (((W z).get k).input.row.2 ((W z).get k).input.time).1} := by
  obtain ⟨k, hk, hd, hdate, hempty⟩ := first_release_predecessor rate rewards C_star C_h z hne
  obtain ⟨selected, next, owned, base, hselected, hnext, hupdate⟩ :=
    ReferenceFirstLiveSourceStoppedHandoverEndpoint.source_window_last_confirmation_update
      rate rewards C_star C_h z k hd
  have hcross := window_crossing rate rewards C_star C_h z (by have := k.isLt; omega)
  have hprov := ReferenceFirstLiveSourceStoppedHandoverEndpoint.source_window_provenance
    rate rewards C_star C_h z hcross
  dsimp only at hprov
  rcases hprov with hzero | ⟨_, _, _, _, _, _, _, _, hrows⟩
  · have := k.isLt
    omega
  · obtain ⟨successorSelected, hs, _, hphase, _⟩ := hrows ⟨k.val + 1, hk⟩
    have hlink := ReferenceFirstLiveSourceStoppedHandoverEndpoint.source_window_successor
      rate rewards C_star C_h z k.val hk
    have hstate : ((W z).get ⟨k.val + 1, hk⟩).input.state.coordinator =
        .live next owned base :=
      (congrArg (fun st => st.coordinator) hlink).trans hnext
    rw [hstate] at hphase
    have hmissing : missing ((W z).get ⟨k.val + 1, hk⟩) =
        successorSelected.view.pendingAtChoice := by
      unfold ReferenceFirstLiveSourceStoppedHandoverEndpoint.missing
        ReferenceFirstLiveSourceStoppedHandoverEndpoint.actualSelection
      rw [hs]
      rfl
    have hnextempty : next.pendingAtChoice = ∅ :=
      hphase.2.symm.trans (hmissing.symm.trans hempty)
    have hconfirmation := hupdate.mp hnextempty
    exact ⟨k, hk, hd, hdate, selected, hselected, hconfirmation.1, hconfirmation.2⟩

end Context

end Bandits.Support.ReferenceFirstLiveInitialTransferChronology

end
