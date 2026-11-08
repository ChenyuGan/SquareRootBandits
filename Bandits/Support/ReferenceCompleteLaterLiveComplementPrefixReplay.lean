/-
Copyright (c) 2026 The Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCompleteLaterLiveCalendarService

import Mathlib.Data.List.TakeWhile
import Mathlib.Data.List.OfFn
import Lean.Elab.Tactic.Omega

/-!
# Continuing later-LIVE complement prefix of the complete physical execution

Sources: `04_slow_fast_learner.tex:140-188,219-243`,
`05_binary_transport.tex:354-399`, `06_interruptions.tex:9-100,192-233,246-299`,
and `appendix_a_local_protocol.tex:28-84`, under `sources/zip4/manuscript/`.

The prefix is selected solely by the actual preparation's continuing dispatch.
The seed is the queried incoming complement score and queue, without an
initialization claim. This internal result is intended for the complete-source
later-LIVE calendar splice and renewed-window physical overflow coverage.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.CanonicalFastSampling

namespace Bandits.Support.ReferenceCompleteLaterLiveComplementPrefixReplay

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

/-- Only the actual prepared continuing-LIVE constructor passes this test. -/
def continuingTest (r : RoundRecord (p := p) (rate := rate)) : Bool :=
  match r.output.preparation.coordinator with
  | .live _ _ _ chosen =>
      match chosen with
      | .continuingChosen .. => true
      | _ => false
  | _ => false

/-- Maximal contiguous continuing prefix starting at the queried record. -/
def continuingPrefix (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (b : ℕ) : List (RoundRecord (p := p) (rate := rate)) :=
  ((ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate source rewards C_star C_h).drop b).takeWhile continuingTest

/-- Normalize the dependent one-round service witnesses to the actual incoming
registers. In particular the queue transition uses those registers, rather than
an independently supplied numerical seed. -/
theorem continuing_step
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
    (base : Fin (p.m - 1) → ℕ)
    (hstate : ((ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[k.val]).input.state.coordinator =
        .live registers owned base)
    (hlater : ReferenceCompletePhysicalHistory.physicalStart
      rate source rewards C_star C_h < registers.payload.sigma.val)
    (hcontinue : continuingTest ((ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[k.val]) = true) :
    let r := (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[k.val]
    let s := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
    ∃ (c : RecordedQueueRun.RoundInput p.K)
      (serviced : CoordinatorLiveServiceFinish.ServicedRegisters
        (liveRegistersAt registers r.input.time) (liveOwnedAt registers owned r.input.time))
      (finished : CoordinatorPhaseClock.FinishRoundResult p),
      ReferenceLaterLiveNumericalReadout.laterLiveReadout s r = some c ∧
      c.enabled = true ∧
      c.reward = (fun arm => ((rewards r.input.time arm).val : ℝ) / (D p : ℝ)) ∧
      c.rate = registers.payload.rate ∧
      (∃ (v : Selection r.input)
        (ho : ReferenceLaterLiveNumericalReadout.preparedOrdinary r),
        r.output.preparation.coordinator.selection = some v ∧
        v.view.payload = registers.payload ∧
        c = ReferenceFirstWindowNumericalStream.sourceCell r v.view.payload
          v.view.pendingAtChoice (ReferenceLaterLiveNumericalReadout.preparedStates r ho)
          v.view.complementWeights v.view.cutoff
          (ReferenceLaterLiveNumericalReadout.selection_choiceValid v)) ∧
      r.output.coordinator.recording = some serviced.recording ∧
      r.output.coordinator.failure = none ∧
      (∀ j, serviced.arrival j = RecordedQueueRun.quantizedArrival
          (ReferenceFirstLaunchNumericalCell.queueParameters rate) c j.val ∧
        QueueReplay.transition (4 * rate.n)
          (registers.complementScores j, owned.queue j)
          (c.enabled, RecordedQueueRun.quantizedArrival
            (ReferenceFirstLaunchNumericalCell.queueParameters rate) c j.val) =
          (serviced.score j, serviced.queue j) ∧
        serviced.previousService j = serviced.service j ∧
        serviced.previousService j = serviced.score j - registers.complementScores j) ∧
      r.output.next.coordinator =
        .live { payload := registers.payload
                priorClock := finished.clock
                pendingAtChoice := finished.pending
                time := r.input.time
                gridBoundary := finished.clock.g
                complementScores := serviced.score }
          { queue := serviced.queue, previousService := serviced.previousService } base := by
  classical
  dsimp only
  let r := (ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate source rewards C_star C_h)[k.val]
  have h := ReferenceCompleteLaterLiveCalendarService.complete_later_live_calendar_service
    (rate := rate) rewards C_star C_h source k registers owned base hstate
  dsimp only at h
  obtain ⟨hprep, hbranch⟩ := h
  have hactual : r.output.preparation = prepare r.input := by
    rw [r.output_eq]
    rfl
  have htest := hcontinue
  change continuingTest r = true at htest
  have hprepared : r.output.preparation.coordinator =
      .live registers owned base
        (CoordinatorRoundDispatch.dispatchLive (liveInput r.input registers owned base)) := by
    rw [hactual]
    exact hprep
  simp only [continuingTest, hprepared] at htest
  cases hc : CoordinatorRoundDispatch.dispatchLive (liveInput r.input registers owned base) with
  | continuingChosen dispatched hstart continuation selection =>
      rw [hc] at hbranch
      obtain ⟨v, hs, hp, _hcut, _hstarted, _harm, _hlive, hsout,
        a, q, followerBase, started, ha, hq, hb, _hstartedEq,
        valid, o, serviced, pending, finished, hpost⟩ := hbranch hlater
      obtain ⟨_hrun, hrecord, _hgate, _hraw, _hdiag, _hcall, _hbridge,
        _hqueue, _hprevious, hrecording, _harrival, _hservice, _hresidual,
        _hscore, _hlast, _hconfirm, _hpending, _hfinish, _hpostChoice,
        _hout, _hnext, _hup, c, ho, hread, henabled, hcell, _hfollowers,
        _hrows, _hselected, _hrewards, hreward, hrate, _hpayload, _hfloor,
        htransition, hfailure, hnext⟩ := hpost
      have ha' : a = liveRegistersAt registers r.input.time := eq_of_heq ha
      subst a
      have hq' : q = liveOwnedAt registers owned r.input.time := eq_of_heq hq
      subst q
      subst followerBase
      refine ⟨c, serviced, finished, hread, henabled, hreward, hrate,
        ⟨v, ho, hsout, hp, hcell⟩, ?_, hfailure, htransition, hnext⟩
      rw [hrecording]
      exact hrecord
  | cutoffChosen => rw [hc] at htest; cases htest
  | clockFailure => rw [hc] at hbranch; exact False.elim hbranch
  | initializerFailure => rw [hc] at hbranch; exact False.elim hbranch
  | localFailure => rw [hc] at hbranch; exact False.elim hbranch

/-- Adjacency is obtained from the actual `Connected` chain. -/
private theorem connected_adjacent
    {initial final : ReferenceActivePhysicalStep.State p rate} {records : List (RoundRecord (p := p) (rate := rate))}
    (h : Connected initial records final) (i : ℕ) (hi : i + 1 < records.length) :
    (records[i + 1]).input.state = (records[i]).output.next := by
  induction records generalizing initial i with
  | nil => simp at hi
  | cons r rest ih =>
      obtain ⟨_, htail⟩ := h
      cases i with
      | zero =>
          cases rest with
          | nil => simp at hi
          | cons r' rest => exact htail.1
      | succ i =>
          simpa only [List.getElem_cons_succ] using
            ih htail i (by simpa using hi)

/-- A nonempty suffix forces a genuine corrected launch; no launch or survival
assumption is passed to the consumer. -/
theorem complete_adjacent
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (i : ℕ)
    (hi : i + 1 < (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length) :
    ((ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[i + 1]).input.state =
    ((ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[i]).output.next := by
  have hn : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h ≠ none := by
    intro hnone
    simp [ReferenceCompletePhysicalHistory.completeSuffixRecords, hnone] at hi
  have hlaunch := ReferenceCompletePhysicalHistory.correctedLaunch_eq_some_payload
    rate source rewards C_star C_h hn
  exact connected_adjacent
    (ReferenceCompletePhysicalHistory.completeSuffix_connected_on_launch
      rate source rewards C_star C_h _ hlaunch) i hi

private theorem takeWhile_length_le {α : Type*} (xs : List α) (test : α → Bool) :
    (xs.takeWhile test).length ≤ xs.length :=
  (List.takeWhile_prefix test).length_le

private theorem takeWhile_drop_index {α : Type*} (xs : List α) (test : α → Bool)
    (b i : ℕ) (hi : i < ((xs.drop b).takeWhile test).length) :
    ((xs.drop b).takeWhile test)[i] =
      xs[b + i]'(by
        have := takeWhile_length_le (xs.drop b) test
        simp only [List.length_drop] at this
        omega) := by
  rw [(List.takeWhile_prefix test).getElem hi, List.getElem_drop]

private theorem takeWhile_eq_take_length {α : Type*} (xs : List α) (test : α → Bool) :
    xs.takeWhile test = xs.take (xs.takeWhile test).length := by
  obtain ⟨tail, heq⟩ := List.takeWhile_prefix (l := xs) test
  have ht := congrArg (fun ys : List α => ys.take (xs.takeWhile test).length) heq
  rw [List.take_left] at ht
  exact ht

private theorem replay_take_succ {α : Type*} (capacity : ℕ) (seed : ℕ × ℕ)
    (cells : List α) (f : α → Bool × ℕ) (i : ℕ) (hi : i < cells.length) :
    QueueReplay.replay capacity seed ((cells.take (i + 1)).map f) =
      QueueReplay.transition capacity
        (QueueReplay.replay capacity seed ((cells.take i).map f)) (f cells[i]) := by
  rw [List.take_succ_eq_append_getElem hi, List.map_append, List.map_singleton,
    QueueReplay.replay_append]
  rfl

private theorem takeWhile_next_false {α : Type*} (xs : List α) (test : α → Bool)
    (h : (xs.takeWhile test).length < xs.length) :
    test xs[(xs.takeWhile test).length] = false := by
  induction xs with
  | nil => simp at h
  | cons x xs ih =>
      cases hx : test x with
      | false => simp only [List.takeWhile_cons, hx, Bool.false_eq_true, ite_false,
          List.length_nil, List.getElem_cons_zero]
      | true =>
          simp only [List.takeWhile_cons, hx, ite_true, List.length_cons] at h ⊢
          exact ih (by omega)

section CompleteSource

variable (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
variable (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)

local notation "R" => ReferenceCompletePhysicalHistory.completeSuffixRecords
  rate source rewards C_star C_h
local notation "s" => ReferenceCompletePhysicalHistory.physicalStart
  rate source rewards C_star C_h

variable (b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
  rate source rewards C_star C_h).length)

local notation "W" => continuingPrefix rate rewards C_star C_h source b.val

/-- The prefix uses the literal contiguous indices of the original run. -/
theorem prefix_index (i : ℕ) (_hi : i < (W).length) :
    W[i] = R[b.val + i]'(by
      have hlen := takeWhile_length_le ((R).drop b.val) continuingTest
      have hilt : i < (((R).drop b.val).takeWhile continuingTest).length := _hi
      simp only [List.length_drop] at hlen
      omega) :=
  takeWhile_drop_index R continuingTest b.val i _hi

/-- The end index remains within the original suffix. -/
theorem prefix_length_le : b.val + (W).length ≤ (R).length := by
  have hlen := takeWhile_length_le ((R).drop b.val) continuingTest
  change (W).length ≤ ((R).drop b.val).length at hlen
  simp only [List.length_drop] at hlen
  have hb := b.isLt
  omega

/-- Every retained physical record passed the actual constructor test. -/
theorem prefix_test (i : ℕ) (_hi : i < (W).length) :
    continuingTest W[i] = true :=
  List.mem_takeWhile_imp (List.getElem_mem _hi)

/-- Exact time-tagged slice of the existing partial calendar, including every
zero-arrival round and retaining the option cell until its domain is proved. -/
theorem prefix_calendar :
    (W).map (fun r => (r.input.time,
      ReferenceLaterLiveNumericalReadout.laterLiveReadout s r)) =
      ((ReferenceLaterLiveNumericalReadout.laterLivePartialCalendar
        rate rewards C_star C_h source).drop b.val).take (W).length := by
  rw [ReferenceLaterLiveNumericalReadout.laterLivePartialCalendar,
    ← List.map_drop, ← List.map_take]
  congr 1
  exact takeWhile_eq_take_length ((R).drop b.val) continuingTest

variable (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
variable (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
variable (base : Fin (p.m - 1) → ℕ)
variable (hstate : ((ReferenceCompletePhysicalHistory.completeSuffixRecords
  rate source rewards C_star C_h)[b.val]'b.isLt).input.state.coordinator =
    .live registers owned base)
variable (hlater : ReferenceCompletePhysicalHistory.physicalStart
  rate source rewards C_star C_h < registers.payload.sigma.val)

include hstate hlater

/-- At every prefix endpoint, retain the actual output constructor, including
at the horizon. When a successor exists it is the very same input state. -/
theorem prefix_live (v : ℕ) (hv : v ≤ (W).length) :
    ∃ (rv : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
      (qv : CoordinatorLiveServiceFinish.OwnedRegisters rv),
      rv.payload = registers.payload ∧
      (∀ hpos : 0 < v,
        (W[v - 1]'(by omega)).output.next.coordinator = .live rv qv base) ∧
      (∀ hnext : b.val + v < (R).length,
        (R[b.val + v]).input.state.coordinator = .live rv qv base) := by
  induction v with
  | zero =>
      refine ⟨registers, owned, rfl, ?_, ?_⟩
      · intro hpos
        omega
      · intro hnext
        simpa only [Nat.add_zero] using hstate
  | succ v ih =>
      have hvlt : v < (W).length := by omega
      have hbound : b.val + v < (R).length := by
        have hlen := prefix_length_le rewards C_star C_h source b
        omega
      obtain ⟨rv, qv, hp, _hout, hin⟩ := ih (by omega)
      have ht := prefix_test rewards C_star C_h source b v hvlt
      rw [prefix_index rewards C_star C_h source b v hvlt] at ht
      obtain ⟨c, serviced, finished, _hread, _henabled, _hreward, _hrate,
        _hcanonical, _hrecording, _hfailure, _htransition, hstep⟩ :=
        continuing_step rewards C_star C_h source ⟨b.val + v, hbound⟩
          rv qv base (hin hbound) (by simpa only [hp] using hlater) ht
      let next : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta :=
        { payload := rv.payload
          priorClock := finished.clock
          pendingAtChoice := finished.pending
          time := (R[b.val + v]).input.time
          gridBoundary := finished.clock.g
          complementScores := serviced.score }
      let queues : CoordinatorLiveServiceFinish.OwnedRegisters next :=
        { queue := serviced.queue, previousService := serviced.previousService }
      have hnext : (R[b.val + v]).output.next.coordinator = .live next queues base := hstep
      refine ⟨next, queues, hp, ?_, ?_⟩
      · intro hpos
        change (W[v]'hvlt).output.next.coordinator = .live next queues base
        rw [prefix_index rewards C_star C_h source b v hvlt]
        exact hnext
      · intro hsuccessor
        have hadj := complete_adjacent rewards C_star C_h source (b.val + v)
          (by omega)
        have hc := congrArg (fun st => st.coordinator) hadj
        simpa only [Nat.add_assoc] using hc.trans hnext

/-- All retained cells exist, derived from actual incoming LIVE states and
actual continuing preparation. No domain premise is supplied. -/
theorem prefix_readout_domain (i : Fin (W).length) :
    (ReferenceLaterLiveNumericalReadout.laterLiveReadout s W[i.val]).isSome := by
  have hbound : b.val + i.val < (R).length := by
    have := prefix_length_le rewards C_star C_h source b
    omega
  obtain ⟨rv, qv, hp, _hout, hin⟩ :=
    prefix_live rewards C_star C_h source b registers owned base hstate hlater
      i.val (Nat.le_of_lt i.isLt)
  have ht := prefix_test rewards C_star C_h source b i.val i.isLt
  rw [prefix_index rewards C_star C_h source b i.val i.isLt] at ht ⊢
  obtain ⟨c, serviced, finished, hread, _⟩ :=
    continuing_step rewards C_star C_h source ⟨b.val + i.val, hbound⟩
      rv qv base (hin hbound) (by simpa only [hp] using hlater) ht
  rw [hread]
  rfl

/-- Proof extraction from each actual `some` cell, without defaults, filtering,
or a second execution. The index subtype retains every physical round. -/
def prefixCells : List (RecordedQueueRun.RoundInput p.K) :=
  List.ofFn fun i : Fin (W).length =>
    (ReferenceLaterLiveNumericalReadout.laterLiveReadout s W[i.val]).get
      (prefix_readout_domain rewards C_star C_h source b registers owned base hstate hlater i)

local notation "A" => prefixCells rewards C_star C_h source b registers owned base hstate hlater

/-- Cell extraction preserves the entire contiguous calendar length. -/
theorem prefixCells_length : (A).length = (W).length := by
  simp only [prefixCells, List.length_ofFn]

/-- Each extracted cell is the unique value of the existing readout. -/
theorem prefixCells_readout (i : Fin (W).length) :
    ReferenceLaterLiveNumericalReadout.laterLiveReadout s W[i.val] =
      some ((A)[i.val]'(by rw [prefixCells_length]; exact i.isLt)) := by
  simp only [prefixCells, List.getElem_ofFn]
  exact (Option.some_get _).symm

/-- Literal map equality, retaining enabled zero arrivals and zero rewards. -/
theorem prefixCells_map :
    (W).map (ReferenceLaterLiveNumericalReadout.laterLiveReadout s) = (A).map some := by
  apply List.ext_getElem
  · simp only [List.length_map, prefixCells_length]
  · intro i hi hj
    have hi' : i < (W).length := by simpa only [List.length_map] using hi
    simp only [List.getElem_map]
    exact prefixCells_readout rewards C_star C_h source b registers owned base hstate hlater
      ⟨i, hi'⟩

/-- No arbitrary matching numerical trajectory is selected. -/
theorem prefixCells_unique (cells : List (RecordedQueueRun.RoundInput p.K))
    (h : (W).map (ReferenceLaterLiveNumericalReadout.laterLiveReadout s) = cells.map some) :
    cells = A := by
  apply List.map_injective_iff.mpr (fun _ _ h => Option.some.inj h)
  exact h.symm.trans (prefixCells_map rewards C_star C_h source b
    registers owned base hstate hlater)

/-- Each actual retained service uses the unique extracted cell and the
canonical whole rewards and rates. The serviced registers are linked to the
same actual next coordinator, with the original payload and follower bases. -/
theorem prefix_step (i : Fin (W).length) :
    let r := R[b.val + i.val]'(by
      have := prefix_length_le rewards C_star C_h source b
      omega)
    let c := (A)[i.val]'(by rw [prefixCells_length]; exact i.isLt)
    ∃ (rv : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
      (qv : CoordinatorLiveServiceFinish.OwnedRegisters rv),
      rv.payload = registers.payload ∧
      r.input.state.coordinator = .live rv qv base ∧
      ∃ (serviced : CoordinatorLiveServiceFinish.ServicedRegisters
          (liveRegistersAt rv r.input.time) (liveOwnedAt rv qv r.input.time))
        (finished : CoordinatorPhaseClock.FinishRoundResult p),
        ReferenceLaterLiveNumericalReadout.laterLiveReadout s r = some c ∧
        c.enabled = true ∧
        c.reward = (fun arm => ((rewards r.input.time arm).val : ℝ) / (D p : ℝ)) ∧
        c.rate = registers.payload.rate ∧
        (∃ (selected : Selection r.input)
          (ho : ReferenceLaterLiveNumericalReadout.preparedOrdinary r),
          r.output.preparation.coordinator.selection = some selected ∧
          selected.view.payload = registers.payload ∧
          c = ReferenceFirstWindowNumericalStream.sourceCell r selected.view.payload
            selected.view.pendingAtChoice
            (ReferenceLaterLiveNumericalReadout.preparedStates r ho)
            selected.view.complementWeights selected.view.cutoff
            (ReferenceLaterLiveNumericalReadout.selection_choiceValid selected)) ∧
        r.output.coordinator.recording = some serviced.recording ∧
        r.output.coordinator.failure = none ∧
        (∀ j, serviced.arrival j = RecordedQueueRun.quantizedArrival
            (ReferenceFirstLaunchNumericalCell.queueParameters rate) c j.val ∧
          QueueReplay.transition (4 * rate.n) (rv.complementScores j, qv.queue j)
            (c.enabled, RecordedQueueRun.quantizedArrival
              (ReferenceFirstLaunchNumericalCell.queueParameters rate) c j.val) =
            (serviced.score j, serviced.queue j) ∧
          serviced.previousService j = serviced.service j ∧
          serviced.previousService j = serviced.score j - rv.complementScores j) ∧
        r.output.next.coordinator =
          .live { payload := rv.payload
                  priorClock := finished.clock
                  pendingAtChoice := finished.pending
                  time := r.input.time
                  gridBoundary := finished.clock.g
                  complementScores := serviced.score }
            { queue := serviced.queue, previousService := serviced.previousService } base := by
  dsimp only
  have hi : b.val + i.val < (R).length := by
    have := prefix_length_le rewards C_star C_h source b
    omega
  obtain ⟨rv, qv, hp, _hout, hin⟩ := prefix_live rewards C_star C_h source b
    registers owned base hstate hlater i.val (Nat.le_of_lt i.isLt)
  have ht := prefix_test rewards C_star C_h source b i.val i.isLt
  have hindex := prefix_index rewards C_star C_h source b i.val i.isLt
  rw [hindex] at ht
  obtain ⟨c, serviced, finished, hread, henabled, hreward, hrate,
    hcanonical, hrecord, hfailure, htrans, hnext⟩ :=
    continuing_step rewards C_star C_h source ⟨b.val + i.val, hi⟩
      rv qv base (hin hi) (by simpa only [hp] using hlater) ht
  have hreadA := prefixCells_readout rewards C_star C_h source b
    registers owned base hstate hlater i
  rw [hindex] at hreadA
  have hcell : c = (A)[i.val]'(by rw [prefixCells_length]; exact i.isLt) :=
    Option.some.inj (hread.symm.trans hreadA)
  subst c
  refine ⟨rv, qv, hp, hin hi, serviced, finished, hread, henabled,
    hreward, ?_, ?_, hrecord, hfailure, htrans, hnext⟩
  · simpa only [hp] using hrate
  · obtain ⟨selected, ho, hs, hpayload, hsource⟩ := hcanonical
    exact ⟨selected, ho, hs, hpayload.trans hp, hsource⟩

/-- Replay of each original complement arm from its actual, possibly nonzero,
queried seed. The same returned coordinator is the actual last output and,
when present, the next input. Empty prefixes preserve working prior service. -/
theorem prefix_replay (v : ℕ) (hv : v ≤ (W).length) :
    let V := fun (j : FastArm registers.payload.slowSet) (w : ℕ) =>
      QueueReplay.replay (4 * rate.n)
        (registers.complementScores j, owned.queue j)
        (((A).take w).map fun c =>
          (c.enabled, RecordedQueueRun.quantizedArrival
            (ReferenceFirstLaunchNumericalCell.queueParameters rate) c j.val))
    ∃ (rv : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
      (qv : CoordinatorLiveServiceFinish.OwnedRegisters rv)
      (hp : rv.payload = registers.payload),
      (∀ hpos : 0 < v,
        (W[v - 1]'(by omega)).output.next.coordinator = .live rv qv base) ∧
      (∀ hnext : b.val + v < (R).length,
        (R[b.val + v]).input.state.coordinator = .live rv qv base) ∧
      ∀ j : FastArm registers.payload.slowSet,
        let jv : FastArm rv.payload.slowSet := ⟨j.val, by simpa only [hp] using j.property⟩
        (rv.complementScores jv, qv.queue jv) = V j v ∧
        qv.previousService jv =
          if v = 0 then owned.previousService j else (V j v).1 - (V j (v - 1)).1 := by
  dsimp only
  induction v with
  | zero =>
      refine ⟨registers, owned, rfl, ?_, ?_, ?_⟩
      · intro hpos
        omega
      · intro hnext
        simpa only [Nat.add_zero] using hstate
      · intro j
        simp [QueueReplay.replay]
  | succ v ih =>
      have hvlt : v < (W).length := by omega
      have hbound : b.val + v < (R).length := by
        have := prefix_length_le rewards C_star C_h source b
        omega
      have hav : v < (A).length := by
        rw [prefixCells_length]
        exact hvlt
      obtain ⟨rv, qv, hp, _hout, hin, hvalues⟩ := ih (by omega)
      have ht := prefix_test rewards C_star C_h source b v hvlt
      have hindex := prefix_index rewards C_star C_h source b v hvlt
      rw [hindex] at ht
      obtain ⟨c, serviced, finished, hread, _henabled, _hreward, _hrate,
        _hcanonical, _hrecording, _hfailure, htransition, hstep⟩ :=
        continuing_step rewards C_star C_h source ⟨b.val + v, hbound⟩
          rv qv base (hin hbound) (by simpa only [hp] using hlater) ht
      have hreadA := prefixCells_readout rewards C_star C_h source b
        registers owned base hstate hlater ⟨v, hvlt⟩
      rw [hindex] at hreadA
      have hcell : c = (A)[v]'hav := Option.some.inj (hread.symm.trans hreadA)
      subst c
      let next : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta :=
        { payload := rv.payload
          priorClock := finished.clock
          pendingAtChoice := finished.pending
          time := (R[b.val + v]).input.time
          gridBoundary := finished.clock.g
          complementScores := serviced.score }
      let queues : CoordinatorLiveServiceFinish.OwnedRegisters next :=
        { queue := serviced.queue, previousService := serviced.previousService }
      have hnext : (R[b.val + v]).output.next.coordinator = .live next queues base := hstep
      refine ⟨next, queues, hp, ?_, ?_, ?_⟩
      · intro hpos
        change (W[v]'hvlt).output.next.coordinator = .live next queues base
        rw [hindex]
        exact hnext
      · intro hsuccessor
        have hadj := complete_adjacent rewards C_star C_h source (b.val + v) (by omega)
        have hc := congrArg (fun st => st.coordinator) hadj
        simpa only [Nat.add_assoc] using hc.trans hnext
      · intro j
        let jv : FastArm rv.payload.slowSet :=
          ⟨j.val, by simpa only [hp] using j.property⟩
        have hpair := (hvalues j).1
        have htrans := (htransition jv).2.1
        have hnew : (serviced.score jv, serviced.queue jv) =
            QueueReplay.replay (4 * rate.n)
              (registers.complementScores j, owned.queue j)
              (((A).take (v + 1)).map fun c =>
                (c.enabled, RecordedQueueRun.quantizedArrival
                  (ReferenceFirstLaunchNumericalCell.queueParameters rate) c j.val)) := by
          rw [replay_take_succ _ _ _ _ v hav, ← hpair]
          exact htrans.symm
        refine ⟨hnew, ?_⟩
        simp only [Nat.add_one_ne_zero, ite_false, Nat.add_one_sub_one]
        change serviced.previousService jv = _
        rw [(htransition jv).2.2.2, ← hnew, ← hpair]

/-- The first excluded record is an actual cutoff choice, unless the prefix
reaches the physical horizon. Failures are ruled out by the admitted complete
service producer; no survival or desired trajectory is assumed. -/
theorem prefix_maximal :
    b.val + (W).length = (R).length ∨
    ∃ (hnext : b.val + (W).length < (R).length)
      (rv : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
      (qv : CoordinatorLiveServiceFinish.OwnedRegisters rv),
      rv.payload = registers.payload ∧
      (R[b.val + (W).length]'hnext).input.state.coordinator = .live rv qv base ∧
      (∃ chosen : CoordinatorRoundDispatch.LiveOutcome
          (liveInput (rate := rate) (R[b.val + (W).length]'hnext).input rv qv base),
        (R[b.val + (W).length]'hnext).output.preparation.coordinator = .live rv qv base chosen ∧
        (match chosen with | .cutoffChosen .. => True | _ => False)) := by
  have hlen := prefix_length_le rewards C_star C_h source b
  by_cases heq : b.val + (W).length = (R).length
  · exact Or.inl heq
  · have hnext : b.val + (W).length < (R).length := by omega
    obtain ⟨rv, qv, hp, _hout, hin⟩ := prefix_live rewards C_star C_h source b
      registers owned base hstate hlater (W).length le_rfl
    refine Or.inr ⟨hnext, rv, qv, hp, hin hnext, ?_⟩
    let r := R[b.val + (W).length]'hnext
    have hfalse : continuingTest r = false := by
      have hd : (((R).drop b.val).takeWhile continuingTest).length <
          ((R).drop b.val).length := by
        change (W).length < ((R).drop b.val).length
        simp only [List.length_drop]
        omega
      have hf := takeWhile_next_false ((R).drop b.val) continuingTest hd
      simpa only [r, continuingPrefix, List.getElem_drop] using hf
    have h := ReferenceCompleteLaterLiveCalendarService.complete_later_live_calendar_service
      (rate := rate) rewards C_star C_h source ⟨b.val + (W).length, hnext⟩
      rv qv base (hin hnext)
    dsimp only at h
    obtain ⟨hprep, hbranch⟩ := h
    have hactual : r.output.preparation = prepare r.input := by
      rw [r.output_eq]
      rfl
    have hprepared : r.output.preparation.coordinator = .live rv qv base
        (CoordinatorRoundDispatch.dispatchLive (liveInput r.input rv qv base)) := by
      rw [hactual]
      exact hprep
    refine ⟨CoordinatorRoundDispatch.dispatchLive (liveInput r.input rv qv base),
      hprepared, ?_⟩
    simp only [continuingTest, hprepared] at hfalse
    cases hc : CoordinatorRoundDispatch.dispatchLive (liveInput r.input rv qv base) with
    | continuingChosen => rw [hc] at hfalse; cases hfalse
    | cutoffChosen => trivial
    | clockFailure => rw [hc] at hbranch; exact False.elim hbranch
    | initializerFailure => rw [hc] at hbranch; exact False.elim hbranch
    | localFailure => rw [hc] at hbranch; exact False.elim hbranch

omit hstate hlater in
/-- Times are the literal consecutive physical source indices. -/
theorem prefix_times :
    (W).map (fun r => r.input.time.val) = List.range' (s + b.val) (W).length := by
  have htimes := ReferenceCompletePhysicalHistory.completeSuffixRecords_time_values
    rate source rewards C_star C_h
  have hlen := prefix_length_le rewards C_star C_h source b
  apply List.ext_getElem
  · simp only [List.length_map, List.length_range']
  · intro i hi hj
    have hi' : i < (W).length := by simpa only [List.length_map] using hi
    have hk : b.val + i < (R).length := by omega
    have hcal : b.val + i < (ReferenceActivePhysicalHorizon.calendar
        s (p.T - s)).length := by
      rw [← htimes, List.length_map]
      exact hk
    have hget : ((R).map (fun r => r.input.time.val))[b.val + i]'(by
        simpa only [List.length_map] using hk) =
        (ReferenceActivePhysicalHorizon.calendar s (p.T - s))[b.val + i]'hcal := by
      simp only [htimes]
    simp only [List.getElem_map] at hget
    simp only [ReferenceActivePhysicalHorizon.calendar, List.getElem_range'] at hget
    simp only [List.getElem_map, List.getElem_range']
    rw [prefix_index rewards C_star C_h source b i hi']
    exact hget.trans (by omega)

/-- Complete internal producer for one maintained later-LIVE complement
interval of the actual complete source. This packages the unique numerical
cells, exact calendar slice, actual per-record service, all seeded replay
endpoints and the first excluded cutoff. It makes no global initial-queue,
recording-law, logical-stop, or regret assertion. -/
theorem complete_later_live_complement_prefix_replay :
    (A).length = (W).length ∧
    (W).map (ReferenceLaterLiveNumericalReadout.laterLiveReadout s) = (A).map some ∧
    (∀ cells : List (RecordedQueueRun.RoundInput p.K),
      (W).map (ReferenceLaterLiveNumericalReadout.laterLiveReadout s) = cells.map some →
        cells = A) ∧
    (W).map (fun r => (r.input.time,
      ReferenceLaterLiveNumericalReadout.laterLiveReadout s r)) =
        ((ReferenceLaterLiveNumericalReadout.laterLivePartialCalendar
          rate rewards C_star C_h source).drop b.val).take (W).length ∧
    (W).map (fun r => r.input.time.val) = List.range' (s + b.val) (W).length ∧
    (∀ i : Fin (W).length,
      let r := R[b.val + i.val]'(by
        have := prefix_length_le rewards C_star C_h source b
        omega)
      let c := (A)[i.val]'(by rw [prefixCells_length]; exact i.isLt)
      ∃ (rv : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
        (qv : CoordinatorLiveServiceFinish.OwnedRegisters rv),
        rv.payload = registers.payload ∧
        r.input.state.coordinator = .live rv qv base ∧
        ∃ (serviced : CoordinatorLiveServiceFinish.ServicedRegisters
            (liveRegistersAt rv r.input.time) (liveOwnedAt rv qv r.input.time))
          (finished : CoordinatorPhaseClock.FinishRoundResult p),
          ReferenceLaterLiveNumericalReadout.laterLiveReadout s r = some c ∧
          c.enabled = true ∧
          c.reward = (fun arm => ((rewards r.input.time arm).val : ℝ) / (D p : ℝ)) ∧
          c.rate = registers.payload.rate ∧
          (∃ (selected : Selection r.input)
            (ho : ReferenceLaterLiveNumericalReadout.preparedOrdinary r),
            r.output.preparation.coordinator.selection = some selected ∧
            selected.view.payload = registers.payload ∧
            c = ReferenceFirstWindowNumericalStream.sourceCell r selected.view.payload
              selected.view.pendingAtChoice
              (ReferenceLaterLiveNumericalReadout.preparedStates r ho)
              selected.view.complementWeights selected.view.cutoff
              (ReferenceLaterLiveNumericalReadout.selection_choiceValid selected)) ∧
          r.output.coordinator.recording = some serviced.recording ∧
          r.output.coordinator.failure = none ∧
          (∀ j, serviced.arrival j = RecordedQueueRun.quantizedArrival
              (ReferenceFirstLaunchNumericalCell.queueParameters rate) c j.val ∧
            QueueReplay.transition (4 * rate.n) (rv.complementScores j, qv.queue j)
              (c.enabled, RecordedQueueRun.quantizedArrival
                (ReferenceFirstLaunchNumericalCell.queueParameters rate) c j.val) =
              (serviced.score j, serviced.queue j) ∧
            serviced.previousService j = serviced.service j ∧
            serviced.previousService j = serviced.score j - rv.complementScores j) ∧
          r.output.next.coordinator =
            .live { payload := rv.payload
                    priorClock := finished.clock
                    pendingAtChoice := finished.pending
                    time := r.input.time
                    gridBoundary := finished.clock.g
                    complementScores := serviced.score }
              { queue := serviced.queue, previousService := serviced.previousService } base) ∧
    (∀ (v : ℕ) (hv : v ≤ (W).length),
      let V := fun (j : FastArm registers.payload.slowSet) (w : ℕ) =>
        QueueReplay.replay (4 * rate.n)
          (registers.complementScores j, owned.queue j)
          (((A).take w).map fun c =>
            (c.enabled, RecordedQueueRun.quantizedArrival
              (ReferenceFirstLaunchNumericalCell.queueParameters rate) c j.val))
      ∃ (rv : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
        (qv : CoordinatorLiveServiceFinish.OwnedRegisters rv)
        (hp : rv.payload = registers.payload),
        (∀ hpos : 0 < v,
          (W[v - 1]'(by omega)).output.next.coordinator = .live rv qv base) ∧
        (∀ hnext : b.val + v < (R).length,
          (R[b.val + v]).input.state.coordinator = .live rv qv base) ∧
        ∀ j : FastArm registers.payload.slowSet,
          let jv : FastArm rv.payload.slowSet := ⟨j.val, by simpa only [hp] using j.property⟩
          (rv.complementScores jv, qv.queue jv) = V j v ∧
          qv.previousService jv =
            if v = 0 then owned.previousService j else (V j v).1 - (V j (v - 1)).1) ∧
    (b.val + (W).length = (R).length ∨
    ∃ (hnext : b.val + (W).length < (R).length)
      (rv : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
      (qv : CoordinatorLiveServiceFinish.OwnedRegisters rv),
      rv.payload = registers.payload ∧
      (R[b.val + (W).length]'hnext).input.state.coordinator = .live rv qv base ∧
      (∃ chosen : CoordinatorRoundDispatch.LiveOutcome
          (liveInput (rate := rate) (R[b.val + (W).length]'hnext).input rv qv base),
        (R[b.val + (W).length]'hnext).output.preparation.coordinator = .live rv qv base chosen ∧
        (match chosen with | .cutoffChosen .. => True | _ => False))) := by
  refine ⟨prefixCells_length rewards C_star C_h source b registers owned base hstate hlater,
    prefixCells_map rewards C_star C_h source b registers owned base hstate hlater,
    ?_, prefix_calendar rewards C_star C_h source b,
    prefix_times rewards C_star C_h source b, ?_, ?_,
    prefix_maximal rewards C_star C_h source b registers owned base hstate hlater⟩
  · intro cells h
    exact prefixCells_unique rewards C_star C_h source b registers owned base hstate hlater cells h
  · intro i
    exact prefix_step rewards C_star C_h source b registers owned base hstate hlater i
  · intro v hv
    exact prefix_replay rewards C_star C_h source b registers owned base hstate hlater v hv

end CompleteSource

end Bandits.Support.ReferenceCompleteLaterLiveComplementPrefixReplay

end
