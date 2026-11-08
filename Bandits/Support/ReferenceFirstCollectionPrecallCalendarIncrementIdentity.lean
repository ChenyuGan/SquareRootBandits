/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionOldCalendarExponentialStep

/-!
# The original pre-call calendar exponential increment

The original first LIVE prefix and the subsequent OLD cells use the same
stopped numerical run. The first cutoff cell belongs to OLD exactly once.
The analysis cut is the first actual invocation, including a failed checked
sampler, and permits the terminal boundary `T` without inventing a next round.

Sources: `04_slow_fast_learner.tex:140-188,245-290`,
`05_binary_transport.tex:352-431`, and `06_interruptions.tex:35-100,355-426`
under `sources/zip4/manuscript/`. These are deterministic internal identities.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open scoped Classical

namespace Bandits.Support.ReferenceFirstCollectionPrecallCalendarIncrementIdentity

open BootstrapPrivateRoundStreams (SourceInput)
open ActualInitializationPhysicalStep (GridRewardTable)
open ReferenceFirstCollectionPrecallCalendarSupport
open ReferenceSourcePrefixHistoryFiltration (actualRecord actualLaunchBy)
open ReferenceFirstCollectionCurrentRetainedGate (cell0)
open ReferenceFirstLiveCalendarPrefixReadout (firstWindowBacklogAt)

variable {p : Parameters}
  (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : GridRewardTable p) (C_star C_h : ℝ)

local notation "S" => SourceInput p
local notation "q" => ReferenceFirstLaunchNumericalCell.queueParameters rate
local notation "beta" => CanonicalRecordingRates.beta p rate.eta.val
local notation "R" z:max => ReferenceCompletePhysicalHistory.completeSuffixRecords
  rate z rewards C_star C_h
local notation "s" z:max => ReferenceCompletePhysicalHistory.physicalStart
  rate z rewards C_star C_h
local notation "W" z:max => ReferenceFirstLiveConfirmationHistory.firstLiveWindow (R z)
local notation "V" z:max => ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells
  rate rewards C_star C_h z

private theorem liveCells_length (z : S) : (V z).length = (W z).length :=
  ReferenceFirstLiveSourcePhasePartition.wholeFirstLiveCells_length
    rate rewards C_star C_h z

private theorem record_time (z : S) (k : ℕ)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : (R z)[k]? = some r) : r.input.time.val = s z + k :=
  ReferenceFirstCollectionRenewalRecordingFeedback.complete_record_time
    rate z rewards C_star C_h k r hr

/-- Even an unsuccessful first invocation occurs after the original LIVE
window. With no invocation, its boundary is the physical horizon. -/
theorem firstLive_end_le_firstCallBoundary (z : S) :
    s z + (V z).length ≤ firstCallBoundary rate rewards C_star C_h z := by
  rw [liveCells_length rate rewards C_star C_h z]
  cases hf : ReferenceFirstCollectionSamplerCall.firstCollectionCall
      rate rewards C_star C_h z with
  | none =>
      have hw := (List.takeWhile_prefix (l := R z)
        (fun r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) =>
          !ReferenceCollectionPhaseHistory.cutoffChosen r.input)).length_le
      change (W z).length ≤ (R z).length at hw
      rw [ReferenceCompletePhysicalHistory.completeSuffixRecords_length] at hw
      have hs := ReferenceCompletePhysicalHistory.physicalStart_le_T
        rate z rewards C_star C_h
      simp only [firstCallBoundary, hf]
      omega
  | some call =>
      obtain ⟨u, t, theta⟩ := call
      obtain ⟨k, r, hr, ht, hcall, _⟩ :=
        (ReferenceFirstCollectionSamplerCall.firstCollectionCall_spec
          (rate := rate) rewards C_star C_h z u t theta).mp hf
      obtain ⟨old, ledger, saved, hcoord, _⟩ :=
        (ReferenceFirstCollectionSamplerCall.collectionCallAt_spec r u theta).mp hcall
      have hw := ReferenceFirstCollectionCurrentNumericalCell.collection_after_firstLive
        rate rewards C_star C_h z k r hr old ledger saved hcoord
      have hd := record_time rate rewards C_star C_h z k r hr
      rw [ht] at hd
      simp only [firstCallBoundary, hf]
      omega

private theorem takeWhile_lookup {A : Type*} (test : A → Bool)
    (xs : List A) (k : ℕ) (hk : k < (xs.takeWhile test).length) :
    xs[k]? = (xs.takeWhile test)[k]? := by
  induction xs generalizing k with
  | nil => simp only [List.takeWhile_nil, List.length_nil, Nat.not_lt_zero] at hk
  | cons x xs ih =>
      cases ht : test x with
      | false => simp only [List.takeWhile_cons, ht, Bool.false_eq_true,
          ↓reduceIte, List.length_nil, Nat.not_lt_zero] at hk
      | true =>
          cases k with
          | zero => simp only [List.takeWhile_cons, ht, ↓reduceIte,
              List.getElem?_cons_zero]
          | succ k =>
              have hk' : k < (xs.takeWhile test).length := by
                simpa only [List.takeWhile_cons, ht, ↓reduceIte,
                  List.length_cons, Nat.succ_lt_succ_iff] using hk
              simpa only [List.takeWhile_cons, ht, ↓reduceIte,
                List.getElem?_cons_succ] using ih k hk'

/-- At every index inside the original LIVE window, the full original cell
is read from that same dated physical record. -/
private theorem firstLive_cell (z : S)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true)
    (k : ℕ) (hk : k < (V z).length) :
    ∃ r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate),
      (R z)[k]? = some r ∧
      ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 r = some (V z)[k] ∧
      ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 r = none := by
  let count := p.T - s z
  let hs := ReferenceCompleteFirstPhaseObservationRecovery.firstPhaseSpan
    rate rewards C_star C_h z
  let window := ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
    rate z rewards C_star C_h hc count hs
  have hW : window = W z := by
    unfold window ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
    rw [← ReferenceCompleteFirstPhaseObservationRecovery.completeSuffixRecords_eq_actualFirstLiveRun
      rate rewards C_star C_h z hc]
  have hV : V z = ReferenceFirstWindowNumericalStream.actualLiveSourceCells
      rate z rewards C_star C_h hc count hs := by
    unfold ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells
    split
    · rfl
    · rename_i hnot
      exact (hnot hc).elim
  have hkw : k < (W z).length := by
    rw [← liveCells_length rate rewards C_star C_h z]
    exact hk
  let j : Fin window.length := ⟨k, by rw [hW]; exact hkw⟩
  obtain ⟨_, _, hcells⟩ :=
    ReferenceCompleteFirstPhaseObservationRecovery.actualFirstLiveRawObservationIdentity
      rate rewards C_star C_h z hc
  obtain ⟨_, _, _, _, _, _, hread, hnone, _⟩ := hcells j
  let r := window[j.val]
  have hr : (R z)[k]? = some r := by
    rw [takeWhile_lookup
      (fun r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) =>
        !ReferenceCollectionPhaseHistory.cutoffChosen r.input) (R z) k hkw]
    change (W z)[k]? = some r
    rw [← hW]
    exact List.getElem?_eq_getElem j.isLt
  refine ⟨r, hr, ?_, hnone⟩
  simpa only [hV] using hread

private theorem mapM_some {A : Type*} (xs : List A) :
    (xs.map some).mapM id = some xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [List.mapM_cons, ih]

/-- Before the LIVE endpoint the actual optional prefix is literally a take
of the whole first LIVE list, including the empty prefix at launch. -/
theorem precallCells_eq_firstLive_take (n : ℕ) (z : S)
    (hz : actualLaunchBy rate rewards C_star C_h n z)
    (hlive : n ≤ s z + (V z).length) :
    precallCells? rate rewards C_star C_h n z = some ((V z).take (n - s z)) := by
  have hbound := firstLive_end_le_firstCallBoundary rate rewards C_star C_h z
  have hcut : cutBoundary rate rewards C_star C_h n z = n :=
    Nat.min_eq_left (hlive.trans hbound)
  have hlen : n - s z ≤ (V z).length := by omega
  have hslots : precallSlots rate rewards C_star C_h n z =
      ((V z).take (n - s z)).map some := by
    apply List.ext_getElem
    · simp only [precallSlots, hcut, List.length_map, List.length_range,
        List.length_take, Nat.min_eq_left hlen]
    · intro k hk hk'
      have hkn : k < n - s z := by
        simpa only [precallSlots, hcut, List.length_map, List.length_range] using hk
      obtain ⟨r, hr, hread, _⟩ := firstLive_cell rate rewards C_star C_h z hz.1 k
        (lt_of_lt_of_le hkn hlen)
      simp only [precallSlots, hcut, List.getElem_map, List.getElem_range,
        hr, Option.bind_some, cell0, hread, Option.some_or, List.getElem_take]
  unfold precallCells?
  rw [hcut, ite_eq_left hz, hslots, mapM_some]

/-- The scalar first LIVE and pre-call readouts coincide on the same prefix.
The launch premise here is produced inside the unconditional increment proof. -/
theorem precallBacklog_eq_firstWindowBacklogAt (n : ℕ) (a : Fin p.K) (z : S)
    (hz : actualLaunchBy rate rewards C_star C_h n z)
    (hlive : n ≤ s z + (V z).length) :
    precallBacklog rate rewards C_star C_h n a z =
      firstWindowBacklogAt rate rewards C_star C_h a n z := by
  rw [precallBacklog, precallCells_eq_firstLive_take
    rate rewards C_star C_h n z hz hlive]
  rfl

private theorem index_lt_takeWhile {A : Type*} (test : A → Bool)
    (xs : List A) (k : ℕ) (hk : k < xs.length)
    (hall : ∀ j ≤ k, ∀ x, xs[j]? = some x → test x = true) :
    k < (xs.takeWhile test).length := by
  induction xs generalizing k with
  | nil => simp only [List.length_nil, Nat.not_lt_zero] at hk
  | cons x xs ih =>
      have hx : test x = true := hall 0 (Nat.zero_le _) x rfl
      cases k with
      | zero => simp only [List.takeWhile_cons, hx, ↓reduceIte,
          List.length_cons, Nat.zero_lt_succ]
      | succ k =>
          have hk' : k < xs.length := Nat.lt_of_succ_lt_succ hk
          have hh : ∀ j ≤ k, ∀ y, xs[j]? = some y → test y = true := by
            intro j hj y hy
            exact hall (j + 1) (by omega) y
              (by simpa only [List.getElem?_cons_succ] using hy)
          simpa only [List.takeWhile_cons, hx, ↓reduceIte, List.length_cons,
            Nat.succ_lt_succ_iff] using ih k hk' hh

private theorem index_lt_collectionWindow (z : S) (k w : ℕ)
    (hw : w < (R z).length) (hwk : w ≤ k) (hk : k < (R z).length)
    (hbefore : s z + k < firstCallBoundary rate rewards C_star C_h z) :
    k - w < (ReferenceCollectionPhaseHistory.collectionWindow (R z) w).length := by
  have hhead : ((R z).drop w |>.take 1).length = 1 := by
    simp only [List.length_take, List.length_drop]
    omega
  unfold ReferenceCollectionPhaseHistory.collectionWindow
  rw [List.length_append, hhead]
  by_cases heq : k = w
  · omega
  · have htail : k - w - 1 < ((R z).drop (w + 1)).length := by
      simp only [List.length_drop]
      omega
    have htake := index_lt_takeWhile
      (fun r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) =>
        !ReferenceCollectionPhaseHistory.laterChosen r.input)
      ((R z).drop (w + 1)) (k - w - 1) htail (by
        intro j hj r hr
        have hr' : (R z)[w + 1 + j]? = some r := by
          simpa only [List.getElem?_drop] using hr
        have hd := record_time rate rewards C_star C_h z _ r hr'
        have hnone := parameters_none_before_cut rate rewards C_star C_h z _ r hr'
          (by omega)
        cases hb : ReferenceCollectionPhaseHistory.laterChosen r.input with
        | false => rfl
        | true =>
            have hp := ReferenceFirstCollectionRenewalRecordingFeedback.laterChosen_parameters_present
              r.input hb
            change (ReferenceLaterSamplerParameterMeasurability.parameters? r.input).isSome = true at hp
            simp only [hnone, Option.isSome_none, Bool.false_eq_true] at hp)
    have hi : k - w = k - w - 1 + 1 := by omega
    rw [hi]
    simpa only [Nat.succ_eq_add_one, Nat.add_comm] using Nat.succ_lt_succ htake

/-- Once the first LIVE list has ended, every actual pre-call date is still
in the original initialized collection stream. Its last physical update is
retained even if no next invocation exists. -/
private theorem old_readout_of_after_firstLive (t : Fin p.T) (z : S)
    (hz : actualLaunchBy rate rewards C_star C_h t.val z)
    (hbefore : t.val < firstCallBoundary rate rewards C_star C_h z)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : actualRecord rate rewards C_star C_h t z = some r)
    (hend : s z + (V z).length ≤ t.val) :
    ∃ c : RecordedQueueRun.RoundInput p.K,
      ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 r = some c ∧
      ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 r = none := by
  let count := p.T - s z
  let hs := ReferenceCompleteFirstPhaseObservationRecovery.firstPhaseReadySpan
    rate rewards C_star C_h z
  let w := (W z).length
  let k := t.val - s z
  have hwk : w ≤ k := by
    rw [liveCells_length rate rewards C_star C_h z] at hend
    dsimp only [w, k]
    omega
  have hk : k < (R z).length := by
    rw [ReferenceCompletePhysicalHistory.completeSuffixRecords_length]
    have hs0 := hz.2
    have ht0 := t.isLt
    dsimp only [k]
    omega
  have hbefore' : s z + k < firstCallBoundary rate rewards C_star C_h z := by
    have hs0 := hz.2
    dsimp only [k]
    omega
  have hR : (R z)[k]? = some r := by
    simpa only [actualRecord, ite_eq_left hz.2] using hr
  have hepoch := ReferenceCompleteFirstPhaseObservationRecovery.completeSuffixRecords_eq_actualFirstEpoch
    rate rewards C_star C_h z hz.1
  have hcount : (R z).length = count :=
    ReferenceCompletePhysicalHistory.completeSuffixRecords_length rate z rewards C_star C_h
  have hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate) z rewards C_star C_h
        hz.1 count hs).records).length < count := by
    rw [← hepoch]
    change w < count
    omega
  obtain ⟨_, _, d, head, initializer, valid, D, hhead, hpay, hinit, hchecked,
      hDlen, hzero, hcells⟩ :=
    ReferenceCompleteFirstPhaseObservationRecovery.actualFirstCollectionRawObservationIdentity
      rate rewards C_star C_h z hz.1 hshort
  have hwin : k - w < d.stream.window.length := by
    rw [d.stream.windowIsActual]
    change k - w < (ReferenceCollectionPhaseHistory.collectionWindow
      (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate) z rewards C_star C_h
        hz.1 count hs).records _).length
    rw [← hepoch]
    exact index_lt_collectionWindow rate rewards C_star C_h z k w
      (by omega) hwk hk hbefore'
  have hell : k - w < d.stream.ell := by
    by_contra hn
    have hshorter : d.stream.ell < d.stream.window.length := by omega
    have halign := (d.stream.alignment
      ⟨d.last.val, lt_of_lt_of_le d.last.isLt d.stream.withinWindow⟩).2
    have hrecord : d.stream.window[d.last.val]'(by
        exact lt_of_lt_of_le d.last.isLt d.stream.withinWindow) = d.record :=
      (List.getElem?_eq_some_iff.mp d.recordAt).2
    rw [hrecord, ← hepoch] at halign
    have hlast : d.record.input.time.val + 1 = s z + w + d.stream.ell := by
      have he := d.lastIsLast
      change d.record.input.time.val + 1 = s z + w + 1 + d.last.val at halign
      omega
    cases d.outcome with
    | exhausted _ hend _ _ _ => omega
    | empty e =>
        cases e.nextBoundary with
        | terminal ht _ =>
            have hsT := d.record.input.time.isLt
            have hsbound := firstCallBoundary_le_T rate rewards C_star C_h z
            omega
        | next hb _ x _ _ htime _ _ _ _ hrun dispatch =>
            have hnext : w + d.stream.ell < (R z).length := by
              rw [hcount]
              dsimp only [count]
              omega
            let rNext := (R z)[w + d.stream.ell]'hnext
            have hlook : (R z)[w + d.stream.ell]? = some rNext :=
              List.getElem?_eq_getElem hnext
            have hx : x = rNext.input := hrun rNext (by
              rw [← hepoch]
              exact hlook)
            have hp : (ReferenceLaterSamplerParameterMeasurability.parameters?
                rNext.input).isSome = true := by
              rw [← hx]
              exact actualNextDispatch_parameters_present rate x _ _ _ dispatch
                (fun a c hc => (e.cutoffLastService a c hc).1)
            have hfirst := firstCallBoundary_le_of_parameters rate rewards C_star C_h
              z _ rNext hlook hp
            have hdate := record_time rate rewards C_star C_h z _ rNext hlook
            omega
  let j : Fin d.stream.ell := ⟨k - w, hell⟩
  obtain ⟨call, validCall, _, _, _, _, _, _, _, _, _, _, _, _, hread, hnone, _⟩ :=
    hcells j
  let r0 := d.stream.window[j.val]'(lt_of_lt_of_le j.isLt d.stream.withinWindow)
  have hlookup := (d.stream.alignment
    ⟨j.val, lt_of_lt_of_le j.isLt d.stream.withinWindow⟩).1
  rw [← hepoch] at hlookup
  have hindex : w + j.val = k := by dsimp only [j]; omega
  change (R z)[w + j.val]? = some r0 at hlookup
  rw [hindex] at hlookup
  have heq : r0 = r := Option.some.inj (hlookup.symm.trans hR)
  exact ⟨_, by simpa only [← heq] using hread, by simpa only [← heq] using hnone⟩

/-- Past the endpoint the literal first LIVE readout stays fixed, independently
of all subsequent physical or stopped numerical behavior. -/
theorem firstWindowBacklogAt_preserve (m n : ℕ) (a : Fin p.K) (z : S)
    (hm : s z + (V z).length ≤ m) (hn : s z + (V z).length ≤ n) :
    firstWindowBacklogAt rate rewards C_star C_h a m z =
      firstWindowBacklogAt rate rewards C_star C_h a n z := by
  have hm' : (V z).length ≤ m - s z := by omega
  have hn' : (V z).length ≤ n - s z := by omega
  simp only [firstWindowBacklogAt, List.take_of_length_le hm',
    List.take_of_length_le hn']

private theorem firstWindowBacklogAt_zero_before_start (n : ℕ) (a : Fin p.K) (z : S)
    (hn : n ≤ s z) : firstWindowBacklogAt rate rewards C_star C_h a n z = 0 := by
  simp [firstWindowBacklogAt, Nat.sub_eq_zero_of_le hn, RecordedQueueRun.run,
    RecordedQueueRun.execute, RecordedQueueRun.initialState, StoppedQueueBound.normalizedBacklog]

private theorem firstWindowBacklogAt_zero_no_launch (n : ℕ) (a : Fin p.K) (z : S)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome ≠ true) :
    firstWindowBacklogAt rate rewards C_star C_h a n z = 0 := by
  have hV : V z = [] := by
    unfold ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells
    split
    · rename_i h
      exact (hc h).elim
    · rfl
  simp [firstWindowBacklogAt, hV, RecordedQueueRun.run, RecordedQueueRun.execute,
    RecordedQueueRun.initialState, StoppedQueueBound.normalizedBacklog]

/-- On the produced OLD event, both localized exponentials are evaluated on
the very same original prefix and its actual stopped numerical successor. -/
theorem oldCalendarExponentialIncrement (t : Fin p.T) (a : Fin p.K) (z : S)
    (hz : z ∈ ReferenceFirstCollectionOldCalendarExponentialStep.E
      rate rewards C_star C_h t) :
    Real.exp (beta * precallBacklog rate rewards C_star C_h (t.val + 1) a z) -
        Real.exp (beta * precallBacklog rate rewards C_star C_h t.val a z) =
      ReferenceFirstCollectionOldCalendarExponentialStep.Xplus
          rate rewards C_star C_h t a z -
        ReferenceFirstCollectionOldCalendarExponentialStep.Xminus
          rate rewards C_star C_h t a z := by
  obtain ⟨L, c, hL, _, hnext, hstep⟩ :=
    ReferenceFirstCollectionOldCalendarExponentialStep.actual_old_calendar_append
      rate rewards C_star C_h t z hz
  have hbefore : precallBacklog rate rewards C_star C_h t.val a z =
      StoppedQueueBound.normalizedBacklog q (RecordedQueueRun.run q L) a := by
    rw [precallBacklog, hL]
  have hafter : precallBacklog rate rewards C_star C_h (t.val + 1) a z =
      StoppedQueueBound.normalizedBacklog q
        (RecordedQueueRun.step q (RecordedQueueRun.run q L) c) a := by
    simp only [precallBacklog, hnext, hstep]
  simp only [ReferenceFirstCollectionOldCalendarExponentialStep.Xplus,
    ReferenceFirstCollectionOldCalendarExponentialStep.Xminus,
    Set.indicator_of_mem hz, hbefore, hafter]

private theorem old_difference_zero (t : Fin p.T) (a : Fin p.K) (z : S)
    (hz : z ∉ ReferenceFirstCollectionOldCalendarExponentialStep.E
      rate rewards C_star C_h t) :
    ReferenceFirstCollectionOldCalendarExponentialStep.Xplus
        rate rewards C_star C_h t a z -
      ReferenceFirstCollectionOldCalendarExponentialStep.Xminus
        rate rewards C_star C_h t a z = 0 := by
  simp only [ReferenceFirstCollectionOldCalendarExponentialStep.Xplus,
    ReferenceFirstCollectionOldCalendarExponentialStep.Xminus,
    Set.indicator_of_notMem hz, sub_self]

private theorem not_mem_old_of_cell_none (t : Fin p.T) (z : S)
    (hnone : ReferenceFirstCollectionOldRecorderFoundation.oldCell?
      rate rewards C_star C_h t z = none) :
    z ∉ ReferenceFirstCollectionOldCalendarExponentialStep.E rate rewards C_star C_h t := by
  intro hz
  have h := (ReferenceFirstCollectionOldCalendarExponentialStep.mem_E_iff_beforeBoundary_and_oldCell
    rate rewards C_star C_h t z).mp hz |>.2
  simp only [hnone, Option.isSome_none, Bool.false_eq_true] at h

/-- The complete deterministic pre-call increment identity on every original
source, date, and arm. No launch, invocation, phase, success, survival, or
endpoint condition is assumed. Both queue readouts retain their existing
first-overflow-update semantics. -/
theorem precallCalendarIncrementIdentity (a : Fin p.K) (t : Fin p.T) (z : S) :
    Real.exp (beta * precallBacklog rate rewards C_star C_h (t.val + 1) a z) -
        Real.exp (beta * precallBacklog rate rewards C_star C_h t.val a z) =
      (Real.exp (beta * firstWindowBacklogAt rate rewards C_star C_h a (t.val + 1) z) -
        Real.exp (beta * firstWindowBacklogAt rate rewards C_star C_h a t.val z)) +
      (ReferenceFirstCollectionOldCalendarExponentialStep.Xplus
          rate rewards C_star C_h t a z -
        ReferenceFirstCollectionOldCalendarExponentialStep.Xminus
          rate rewards C_star C_h t a z) := by
  by_cases hafter : firstCallBoundary rate rewards C_star C_h z ≤ t.val
  · have hprefix := precallCells_preserve rate rewards C_star C_h
      (t.val + 1) t.val z (hafter.trans (Nat.le_succ _)) hafter
    have hbacklog : precallBacklog rate rewards C_star C_h (t.val + 1) a z =
        precallBacklog rate rewards C_star C_h t.val a z := by
      simp only [precallBacklog, hprefix]
    have hend := firstLive_end_le_firstCallBoundary rate rewards C_star C_h z
    have hfirst := firstWindowBacklogAt_preserve rate rewards C_star C_h
      (t.val + 1) t.val a z (by omega) (by omega)
    have hnot : z ∉ ReferenceFirstCollectionOldCalendarExponentialStep.E
        rate rewards C_star C_h t := by
      intro hz
      have hb := (ReferenceFirstCollectionOldCalendarExponentialStep.mem_E_iff_beforeBoundary_and_oldCell
        rate rewards C_star C_h t z).mp hz |>.1
      omega
    rw [hbacklog, hfirst, old_difference_zero rate rewards C_star C_h t a z hnot]
    simp only [sub_self, zero_add]
  · have hbefore : t.val < firstCallBoundary rate rewards C_star C_h z := by omega
    by_cases hz : actualLaunchBy rate rewards C_star C_h t.val z
    · obtain ⟨L, r, c, _, hr, _, _, hread, _, _⟩ :=
        precallPrefix_append rate rewards C_star C_h t z hz hbefore
      rcases hread with ⟨hlive, holdNone⟩ | ⟨hold, _⟩
      · have hlt : t.val < s z + (V z).length := by
          by_contra h
          obtain ⟨c0, _, hnone⟩ := old_readout_of_after_firstLive
            rate rewards C_star C_h t z hz hbefore r hr (by omega)
          rw [hnone] at hlive
          cases hlive
        have hzNext : actualLaunchBy rate rewards C_star C_h (t.val + 1) z :=
          ⟨hz.1, hz.2.trans (Nat.le_succ _)⟩
        have hcurrent := precallBacklog_eq_firstWindowBacklogAt
          rate rewards C_star C_h t.val a z hz (Nat.le_of_lt hlt)
        have hnext := precallBacklog_eq_firstWindowBacklogAt
          rate rewards C_star C_h (t.val + 1) a z hzNext (by omega)
        have hnone : ReferenceFirstCollectionOldRecorderFoundation.oldCell?
            rate rewards C_star C_h t z = none := by
          simp only [ReferenceFirstCollectionOldRecorderFoundation.oldCell?,
            hr, Option.bind_some, holdNone]
        have hnot := not_mem_old_of_cell_none rate rewards C_star C_h t z hnone
        rw [hnext, hcurrent, old_difference_zero rate rewards C_star C_h t a z hnot]
        exact (add_zero _).symm
      · have hE : z ∈ ReferenceFirstCollectionOldCalendarExponentialStep.E
            rate rewards C_star C_h t := by
          apply (ReferenceFirstCollectionOldCalendarExponentialStep.mem_E_iff_beforeBoundary_and_oldCell
            rate rewards C_star C_h t z).mpr
          refine ⟨hbefore, ?_⟩
          simp only [ReferenceFirstCollectionOldRecorderFoundation.oldCell?,
            hr, Option.bind_some, hold, Option.isSome_some]
        have hend := old_readout_after_firstLiveWindow
          rate rewards C_star C_h t z hz r hr (by rw [hold]; rfl)
        rw [← liveCells_length rate rewards C_star C_h z] at hend
        have hfirst := firstWindowBacklogAt_preserve rate rewards C_star C_h
          (t.val + 1) t.val a z (by omega) hend
        rw [hfirst, sub_self, zero_add]
        exact oldCalendarExponentialIncrement rate rewards C_star C_h t a z hE
    · have hcut : cutBoundary rate rewards C_star C_h t.val z = t.val :=
        Nat.min_eq_left (Nat.le_of_lt hbefore)
      have hnone : precallCells? rate rewards C_star C_h t.val z = none :=
        precallCells_no_launch rate rewards C_star C_h t.val z (by rw [hcut]; exact hz)
      have hnext : precallCells? rate rewards C_star C_h (t.val + 1) z = none ∨
          precallCells? rate rewards C_star C_h (t.val + 1) z = some [] := by
        rcases precallPrefix_step_or_preserve rate rewards C_star C_h t z with
          hpreserve | habsent | happend
        · exact (Nat.not_le_of_gt hbefore hpreserve.1).elim
        · exact habsent.2.2.2
        · obtain ⟨_, L, c, hL, _, _⟩ := happend
          rw [hnone] at hL
          cases hL
      have hzero : precallBacklog rate rewards C_star C_h t.val a z = 0 := by
        rw [precallBacklog, hnone]
      have hzeroNext : precallBacklog rate rewards C_star C_h (t.val + 1) a z = 0 := by
        rcases hnext with hn | hn
        · rw [precallBacklog, hn]
        · simp [precallBacklog, hn, RecordedQueueRun.run, RecordedQueueRun.execute,
            RecordedQueueRun.initialState, StoppedQueueBound.normalizedBacklog]
      have hfirstZero : firstWindowBacklogAt rate rewards C_star C_h a t.val z = 0 ∧
          firstWindowBacklogAt rate rewards C_star C_h a (t.val + 1) z = 0 := by
        by_cases hc : (ReferenceInitializationRun.output
            (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true
        · have hs : t.val + 1 ≤ s z := by
            by_contra h
            exact hz ⟨hc, by omega⟩
          exact ⟨firstWindowBacklogAt_zero_before_start
              rate rewards C_star C_h t.val a z (by omega),
            firstWindowBacklogAt_zero_before_start rate rewards C_star C_h (t.val + 1) a z hs⟩
        · exact ⟨firstWindowBacklogAt_zero_no_launch rate rewards C_star C_h t.val a z hc,
            firstWindowBacklogAt_zero_no_launch rate rewards C_star C_h (t.val + 1) a z hc⟩
      have hrecord := ReferenceSourcePrefixHistoryFiltration.actualRecord_eq_none_of_not_launchBy
        rate rewards C_star C_h t z hz
      have hOldNone : ReferenceFirstCollectionOldRecorderFoundation.oldCell?
          rate rewards C_star C_h t z = none := by
        simp only [ReferenceFirstCollectionOldRecorderFoundation.oldCell?, hrecord, Option.bind_none]
      have hnot := not_mem_old_of_cell_none rate rewards C_star C_h t z hOldNone
      rw [hzeroNext, hzero, hfirstZero.1, hfirstZero.2,
        old_difference_zero rate rewards C_star C_h t a z hnot]
      simp only [sub_self, zero_add]

end Bandits.Support.ReferenceFirstCollectionPrecallCalendarIncrementIdentity
