/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionPrecallCalendarIncrementIdentity
public import Bandits.Support.ReferenceFirstCollectionCurrentConditionalWeightedDrift

import Mathlib.Tactic

/-!
# Original old-prefix stream origin and rate credit

The old pre-call readout is tied to the original initialized collection stream
at its actual physical record.  The prefix score envelope is then run from the
literal zero state on that same recorded prefix.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open scoped Classical

namespace Bandits.Support.ReferenceFirstCollectionOldPrefixOriginRateCredit

open BootstrapPrivateRoundStreams (SourceInput)
open ActualInitializationPhysicalStep (GridRewardTable)
open ReferenceSourcePrefixHistoryFiltration (actualLaunchBy actualRecord)
open ReferenceFirstCollectionPrecallCalendarSupport
  (firstCallBoundary precallCells? precallBacklog cutBoundary)
open ReferenceFirstCollectionCurrentRetainedGate (cell0)
open ReferenceCompletePhysicalHistory (completeSuffixRecords physicalStart)
open ReferenceFirstCollectionOldCalendarExponentialStep (E G)
open ReferenceFirstCollectionOldRecorderFoundation (oldCell? incomingPayload?)
open ReferenceFirstLiveOverflowReadout (wholeFirstLiveCells)
open ReferenceFirstLiveConfirmationHistory (firstLiveWindow)

variable {p : Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : GridRewardTable p) (C_star C_h : ℝ)

local notation "S" => SourceInput p
local notation "R" z:max => completeSuffixRecords rate z rewards C_star C_h
local notation "s" z:max => physicalStart rate z rewards C_star C_h
local notation "W" z:max => firstLiveWindow (R z)
local notation "V" z:max => wholeFirstLiveCells rate rewards C_star C_h z
local notation "q" => ReferenceFirstLaunchNumericalCell.queueParameters rate

private theorem liveCells_length (z : S) : (V z).length = (W z).length :=
  ReferenceFirstLiveSourcePhasePartition.wholeFirstLiveCells_length
    rate rewards C_star C_h z

private theorem record_time (z : S) (k : ℕ)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : (R z)[k]? = some r) : r.input.time.val = s z + k :=
  ReferenceFirstCollectionRenewalRecordingFeedback.complete_record_time
    rate z rewards C_star C_h k r hr

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
        have hnone := ReferenceFirstCollectionPrecallCalendarSupport.parameters_none_before_cut
          rate rewards C_star C_h z _ r hr' (by omega)
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

/-- An actual OLD readout after the first LIVE list is the old collection
cell of the very same physical record.  The returned context retains its
initialized head witness or the continuing cell's ready input on the same
stream position. -/
theorem actual_old_cell_after_firstLive_before_boundary
    (t : Fin p.T) (z : S)
    (hz : actualLaunchBy rate rewards C_star C_h t.val z)
    (hbefore : t.val < firstCallBoundary rate rewards C_star C_h z)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : actualRecord rate rewards C_star C_h t z = some r)
    (hend : s z + (V z).length ≤ t.val) :
    ∃ c : RecordedQueueRun.RoundInput p.K,
      ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 r = some c ∧
      ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 r = none ∧
      ∃ d : ReferenceFirstCollectionStreamEmptyDispatch.ActualInitializedStreamDispatch
          (p := p) (rate := rate) z rewards C_star C_h
            (p.T - s z) hz.1
            (ReferenceCompleteFirstPhaseObservationRecovery.firstPhaseReadySpan
              rate rewards C_star C_h z)
            (by
              have hepoch :=
                ReferenceCompleteFirstPhaseObservationRecovery.completeSuffixRecords_eq_actualFirstEpoch
                  rate rewards C_star C_h z hz.1
              rw [← hepoch]
              change (W z).length < p.T - s z
              have hst : s z + (W z).length < p.T := by
                rw [← liveCells_length rate rewards C_star C_h z]
                exact lt_of_le_of_lt hend t.isLt
              omega),
        ∃ head : ReferenceCollectionSegmentExtraction.Choice rate,
        ∃ initializer : ReferenceCollectionSegmentExtraction.Initializer p,
        ∃ valid : CoordinatorRecorderComplementBridge.LocalInputsValid
          (ReferenceActivePhysicalStep.collectionRecordingInput
            d.stream.cutoff.cut.output.preparation head.payload head.started head.weights),
        ∃ D : List (RecordedQueueRun.RoundInput p.K),
        ∃ hDlen : D.length = d.stream.ell,
          ReferenceCollectionSegmentExtraction.choice d.stream.cutoff.cut.input = some head ∧
          head.payload = d.stream.payload ∧
          head.initializer = some initializer ∧
          initializer.checkedStart rate = .success head.preLedger ∧
          ∃ n : Fin d.stream.ell,
            n.val = t.val - s z - (W z).length ∧
            ∃ call : ReferenceCollectionSegmentExtraction.Choice rate,
            ∃ validCall : CoordinatorRecorderComplementBridge.LocalInputsValid
              (ReferenceActivePhysicalStep.collectionRecordingInput
                (d.stream.window[n.val]'(by
                  exact lt_of_lt_of_le n.isLt d.stream.withinWindow)).output.preparation
                  call.payload call.started call.weights),
              ReferenceCollectionSegmentExtraction.choice
                (d.stream.window[n.val]'(by
                  exact lt_of_lt_of_le n.isLt d.stream.withinWindow)).input =
                  some call ∧
              d.stream.window[n.val]'(lt_of_lt_of_le n.isLt d.stream.withinWindow) = r ∧
              call.payload = d.stream.payload ∧
              CollectionBufferProvenance.collectionContext call.preLedger =
                CollectionBufferProvenance.collectionContext head.preLedger ∧
              D[n.val]'(by rw [hDlen]; exact n.isLt) = c ∧
              c.enabled = ReferenceActivePhysicalStep.collectionEnabled
                call.preLedger r.input.time ∧
              ((n.val = 0 ∧
                  d.stream.cutoff.ledger.sigma =
                    ReferenceFirstCollectionReadyStream.startTime
                      (rate := rate) z rewards C_star C_h + 1) ∨
                ∃ cell : ReferenceFirstCollectionReadyStream.ContinuingStreamCell
                  z rewards
                    (ReferenceFirstCollectionReadyStream.actualEpoch
                      (rate := rate) z rewards C_star C_h hz.1
                      (p.T - s z)
                      (ReferenceCompleteFirstPhaseObservationRecovery.firstPhaseReadySpan
                        rate rewards C_star C_h z)).records
                    ((ReferenceFirstLiveConfirmationHistory.firstLiveWindow
                      (ReferenceFirstCollectionReadyStream.actualEpoch
                        (rate := rate) z rewards C_star C_h hz.1
                        (p.T - s z)
                        (ReferenceCompleteFirstPhaseObservationRecovery.firstPhaseReadySpan
                          rate rewards C_star C_h z)).records).length + n.val)
                    (p.T - s z)
                    (ReferenceFirstCollectionReadyStream.startTime
                      (rate := rate) z rewards C_star C_h)
                    r
                    d.stream.payload
                    (d.stream.ledgers ⟨n.val - 1,
                      Nat.lt_of_le_of_lt (Nat.sub_le _ _) n.isLt⟩) d.stream.saved,
                  0 < n.val ∧ cell.choice = call ∧
                  cell.serviceLedger = d.stream.ledgers n) := by
  let count := p.T - s z
  let hs := ReferenceCompleteFirstPhaseObservationRecovery.firstPhaseReadySpan
    rate rewards C_star C_h z
  let epoch := ReferenceFirstCollectionReadyStream.actualEpoch
    (rate := rate) z rewards C_star C_h hz.1 count hs
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
      epoch.records).length < count := by
    rw [← hepoch]
    change w < count
    have hst : s z + (W z).length < p.T := by
      rw [← liveCells_length rate rewards C_star C_h z]
      exact lt_of_le_of_lt hend t.isLt
    omega
  obtain ⟨_, _, d, head, initializer, valid, D, hhead, hpay, hinit, hchecked,
      hDlen, hzero, hcells⟩ :=
    ReferenceCompleteFirstPhaseObservationRecovery.actualFirstCollectionRawObservationIdentity
      rate rewards C_star C_h z hz.1 hshort
  have hwin : k - w < d.stream.window.length := by
    rw [d.stream.windowIsActual]
    change k - w < (ReferenceCollectionPhaseHistory.collectionWindow
      epoch.records _).length
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
    | exhausted _ hend' _ _ _ => omega
    | empty e =>
        cases e.nextBoundary with
        | terminal ht _ =>
            have hsT := d.record.input.time.isLt
            have hsbound :=
              ReferenceFirstCollectionPrecallCalendarSupport.firstCallBoundary_le_T
                rate rewards C_star C_h z
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
              exact ReferenceFirstCollectionPrecallCalendarSupport.actualNextDispatch_parameters_present
                rate x _ _ _ dispatch
                (fun a c hc => (e.cutoffLastService a c hc).1)
            have hfirst :=
              ReferenceFirstCollectionPrecallCalendarSupport.firstCallBoundary_le_of_parameters
                rate rewards C_star C_h z _ rNext hlook hp
            have hdate := record_time rate rewards C_star C_h z _ rNext hlook
            omega
  let n : Fin d.stream.ell := ⟨k - w, hell⟩
  rcases hcells n with ⟨call, validCall, hcall, hpayload, hctx, _hcellEq,
    _hrows, _hselected, _hrewards, _htime, henabled, _hreward, _hrate,
    _hqueue, hread0, hnone0, _hindex, _⟩
  let c := D[n.val]'(by rw [hDlen]; exact n.isLt)
  let r0 := d.stream.window[n.val]'(lt_of_lt_of_le n.isLt d.stream.withinWindow)
  have hlookup := (d.stream.alignment
    ⟨n.val, lt_of_lt_of_le n.isLt d.stream.withinWindow⟩).1
  rw [← hepoch] at hlookup
  have hindex : w + n.val = k := by dsimp only [n]; omega
  change (R z)[w + n.val]? = some r0 at hlookup
  rw [hindex] at hlookup
  have hr0 : r0 = r := Option.some.inj (hlookup.symm.trans hR)
  have hread' : ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 r = some c := by
    simpa only [← hr0, c] using hread0
  have hreadAt : ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 r =
      some c := by
    simpa only [← hr0, c] using hread0
  have hnone' : ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 r = none := by
    simpa only [← hr0] using hnone0
  have hcontext :
      d.stream.window[n.val]'(lt_of_lt_of_le n.isLt d.stream.withinWindow) = r := by
    exact hr0
  have hheadCell : D[n.val]'(by rw [hDlen]; exact n.isLt) = c :=
    Option.some.inj (hreadAt.symm.trans hread')
  by_cases hn0 : n.val = 0
  · refine ⟨c, hread', hnone', d, head, initializer, valid, D, hDlen, hhead,
      hpay, hinit, hchecked, n, ?_, call, validCall,
      hcall, ?_, ?_, ?_, hheadCell, ?_, ?_⟩
    · dsimp only [n, k, w]
    · exact hcontext
    · exact hpayload
    · simpa only [hcontext] using hctx
    · simpa only [hcontext] using henabled
    · exact Or.inl ⟨hn0, d.stream.cutoffContext.1⟩
  · have hpos : 0 < n.val := Nat.pos_of_ne_zero hn0
    obtain ⟨j, r', incoming, cell, hj, hr', hledger, hincoming⟩ :=
      d.stream.cell_at n hpos
    subst j
    have hr'eq : r' = r := by
      have hsame : d.stream.window[n.val]? = some r := by
        rw [List.getElem?_eq_getElem (lt_of_lt_of_le n.isLt d.stream.withinWindow)]
        exact congrArg some hcontext
      exact Option.some.inj (hr'.symm.trans hsame)
    subst r'
    subst incoming
    have hcallR := hcall
    rw [hcontext] at hcallR
    have hchoiceCell : cell.choice = call :=
      Option.some.inj (cell.actualChoice.symm.trans hcallR)
    refine ⟨c, hread', hnone', d, head, initializer, valid, D, hDlen, hhead,
      hpay, hinit, hchecked, n, ?_, call, validCall,
      hcall, ?_, ?_, ?_, hheadCell, ?_, ?_⟩
    · dsimp only [n, k, w]
    · exact hcontext
    · exact hpayload
    · simpa only [hcontext] using hctx
    · simpa only [hcontext] using henabled
    · exact Or.inr ⟨cell, hpos, hchoiceCell, hledger⟩

private theorem elapsed_le_episodeHorizon (sigma : Fin p.T) (t : Fin p.T)
    (hbefore : t.val + 1 < FollowerCutoffScan.gridBoundary p rate.eta.val sigma) :
    t.val - sigma.val ≤ ReplayWeightStability.episodeHorizon rate.eta.val := by
  let H := ReplayWeightStability.episodeHorizon rate.eta.val
  have hdiv : (sigma.val + 1) % H + H * ((sigma.val + 1) / H) = sigma.val + 1 :=
    Nat.mod_add_div _ _
  have hraw : H * ((sigma.val + 1) / H + 1) ≤ sigma.val + 1 + H := by
    rw [Nat.mul_succ]
    omega
  have hmin : FollowerCutoffScan.gridBoundary p rate.eta.val sigma ≤
      H * ((sigma.val + 1) / H + 1) := Nat.min_le_right _ _
  change t.val - sigma.val ≤ H
  omega

private theorem zero_run_score_envelope
    (L : List (RecordedQueueRun.RoundInput p.K))
    (hlen : L.length ≤ ReplayWeightStability.episodeHorizon rate.eta.val)
    (a : Fin p.K) :
    1 ≤ RecordedQueueRun.scoreWeight q (RecordedQueueRun.run q L) a ∧
      RecordedQueueRun.scoreWeight q (RecordedQueueRun.run q L) a < 2 := by
  have h := RecordedEpisodeStability.execute_source_weight_envelope
    q (RecordedQueueRun.initialState p.K) L a hlen
  have hzero : RecordedQueueRun.scoreWeight q
      (RecordedQueueRun.initialState p.K) a = 1 := by
    simp only [RecordedQueueRun.scoreWeight, RecordedQueueRun.initialState,
      ScoreWeights.scoreWeight, pow_zero]
  change 1 ≤ RecordedQueueRun.scoreWeight q
      (RecordedQueueRun.execute q L (RecordedQueueRun.initialState p.K)) a ∧ _
    at h
  rw [hzero, mul_one] at h
  simpa only [RecordedQueueRun.run, RecordedQueueRun.execute] using
    And.intro h.1 h.2.1

private theorem ready_input_anchor_one
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (saved : Option (Fin p.T × Bool))
    (hReady : ReferenceContinuingCollectionStartDomains.continuingCollectionReadyDomain
      x payload ledger saved) :
    ∀ a : Fin p.K, payload.anchor a = 1 := by
  rcases hReady with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hanchor, _⟩
  exact hanchor

private theorem boundary_input_anchor_one
    (state : ReferenceActivePhysicalStep.State p rate)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (saved : Option (Fin p.T × Bool))
    (hReady : ReferenceContinuingCollectionRejectedFinishDomains.continuingCollectionReadyBoundaryDomain
      state payload ledger saved) :
    ∀ a : Fin p.K, payload.anchor a = 1 := by
  rcases hReady with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hanchor, _⟩
  exact hanchor

/-- On the original retained OLD event, the precall list appends the exact
same old cell; the incoming payload and enabled bit come from that same actual
record. This preserves the source-facing data needed by the later origin and
score-credit step. -/
theorem old_prefix_actual_append_and_payload (t : Fin p.T) (z : S)
    (hz : z ∈ G rate rewards C_star C_h t) :
    ∃ (L : List (RecordedQueueRun.RoundInput p.K))
      (c : RecordedQueueRun.RoundInput p.K)
      (payload : ReferenceActivePhysicalStep.Payload rate)
      (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)),
      precallCells? rate rewards C_star C_h t.val z = some L ∧
      ReferenceFirstCollectionOldRecorderFoundation.oldCell?
        rate rewards C_star C_h t z = some c ∧
      ReferenceFirstCollectionOldRecorderFoundation.incomingPayload?
        rate rewards C_star C_h t z = some payload ∧
      c.rate = payload.rate ∧
      precallCells? rate rewards C_star C_h (t.val + 1) z = some (L ++ [c]) ∧
      RecordedQueueRun.run q (L ++ [c]) =
        RecordedQueueRun.step q (RecordedQueueRun.run q L) c ∧
      L.length = t.val - s z ∧
      actualRecord rate rewards C_star C_h t z = some r ∧
      r.input.time = t ∧ c.enabled = true := by
  classical
  obtain ⟨⟨hzE, _hzH⟩, hEnabled⟩ := hz
  obtain ⟨L, c, hL, hc, hnext, hrun⟩ :=
    ReferenceFirstCollectionOldCalendarExponentialStep.actual_old_calendar_append
      rate rewards C_star C_h t z hzE
  have hOldSelector : z ∈ ReferenceFirstCollectionOldRecorderFoundation.oldSelector
      rate rewards C_star C_h t := by
    simpa only [E] using hzE
  obtain ⟨payload, c', hp, hc', hrate, _hmarker⟩ :=
    ReferenceFirstCollectionOldRecorderFoundation.oldCell_recordingMap
      rate rewards C_star C_h t z hOldSelector
  have hcell : c' = c := Option.some.inj (hc'.symm.trans hc)
  subst c'
  have hrecordBind :
      (actualRecord rate rewards C_star C_h t z).bind
        (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0) = some c := by
    simpa only [ReferenceFirstCollectionOldRecorderFoundation.oldCell?] using hc
  obtain ⟨r, hr, hread⟩ := Option.bind_eq_some_iff.mp hrecordBind
  have hbefore : t.val < firstCallBoundary rate rewards C_star C_h z :=
    (ReferenceFirstCollectionOldCalendarExponentialStep.mem_E_iff_beforeBoundary_and_oldCell
      rate rewards C_star C_h t z).mp hzE |>.1
  have hcut : ReferenceFirstCollectionPrecallCalendarSupport.cutBoundary
      rate rewards C_star C_h t.val z = t.val := by
    unfold ReferenceFirstCollectionPrecallCalendarSupport.cutBoundary
    exact Nat.min_eq_left (Nat.le_of_lt hbefore)
  obtain ⟨L', hL', hlen', _hslots, _hcoverage⟩ :=
    ReferenceFirstCollectionPrecallCalendarSupport.precallPrefix_present
      rate rewards C_star C_h t.val (Nat.le_of_lt t.isLt) z
      (by
        have hlaunch : actualLaunchBy rate rewards C_star C_h t.val z := by
          by_contra hnot
          rw [ReferenceSourcePrefixHistoryFiltration.actualRecord_eq_none_of_not_launchBy
            rate rewards C_star C_h t z hnot] at hr
          cases hr
        simpa only [hcut] using hlaunch)
  have hLsame : L' = L := Option.some.inj (hL'.symm.trans hL)
  subst L'
  have hlen : L.length = t.val - s z := by
    rw [hlen', hcut]
  have htime : r.input.time = t :=
    (ReferenceCalendarLaterSamplerOutputSections.actualRecord_fields
      rate rewards C_star C_h t z r hr).2.2.1
  have hcEnabled := ReferenceFirstCollectionOldRecorderFoundation.oldCell_enabled_eq_incoming
    rate rewards C_star C_h t z c hc
  have hcEnabledTrue : c.enabled = true := by
    change ReferenceFirstCollectionOldRecorderFoundation.incomingEnabled?
      rate rewards C_star C_h t z = some true at hEnabled
    rw [hcEnabled] at hEnabled
    exact Option.some.inj hEnabled
  exact ⟨L, c, payload, r, hL, hc, hp, hrate, hnext, hrun,
    hlen, hr, htime, hcEnabledTrue⟩

/-- The original incoming OLD payload is the payload of the same first
initialized stream. Its start and all-arm unit anchor are derived from the
head initialization or the exact continuing ready cell. -/
theorem old_prefix_source_origin (t : Fin p.T) (z : S)
    (hz : z ∈ G rate rewards C_star C_h t) :
    ∃ (L : List (RecordedQueueRun.RoundInput p.K))
      (c : RecordedQueueRun.RoundInput p.K)
      (payload : ReferenceActivePhysicalStep.Payload rate)
      (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)),
      precallCells? rate rewards C_star C_h t.val z = some L ∧
      ReferenceFirstCollectionOldRecorderFoundation.oldCell?
        rate rewards C_star C_h t z = some c ∧
      ReferenceFirstCollectionOldRecorderFoundation.incomingPayload?
        rate rewards C_star C_h t z = some payload ∧
      c.rate = payload.rate ∧
      precallCells? rate rewards C_star C_h (t.val + 1) z = some (L ++ [c]) ∧
      L.length = t.val - s z ∧
      ReferenceSourcePrefixHistoryFiltration.actualRecord
        rate rewards C_star C_h t z = some r ∧
      r.input.time = t ∧ c.enabled = true ∧
      payload.sigma.val = s z ∧ (∀ a : Fin p.K, payload.anchor a = 1) ∧
      t.val + 1 < FollowerCutoffScan.gridBoundary p rate.eta.val payload.sigma := by
  classical
  obtain ⟨L, c, payload, r, hL, hc, hp, hrate, hnext, _hrun,
    hlen, hr, htime, hcEnabled⟩ :=
    old_prefix_actual_append_and_payload rate rewards C_star C_h t z hz
  obtain ⟨⟨hzE, _hzH⟩, _hEnabled⟩ := hz
  have hlaunch : actualLaunchBy rate rewards C_star C_h t.val z := by
    by_contra hnot
    rw [ReferenceSourcePrefixHistoryFiltration.actualRecord_eq_none_of_not_launchBy
      rate rewards C_star C_h t z hnot] at hr
    cases hr
  have hbefore : t.val < firstCallBoundary rate rewards C_star C_h z :=
    (ReferenceFirstCollectionOldCalendarExponentialStep.mem_E_iff_beforeBoundary_and_oldCell
      rate rewards C_star C_h t z).mp hzE |>.1
  have hreadBind :
      (actualRecord rate rewards C_star C_h t z).bind
        (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0) = some c := by
    simpa only [ReferenceFirstCollectionOldRecorderFoundation.oldCell?] using hc
  obtain ⟨r', hr', hread⟩ := Option.bind_eq_some_iff.mp hreadBind
  have hrEq : r' = r := Option.some.inj (hr'.symm.trans hr)
  subst r'
  have hend := ReferenceFirstCollectionPrecallCalendarSupport.old_readout_after_firstLiveWindow
    rate rewards C_star C_h t z hlaunch r hr (by rw [hread]; rfl)
  have hend' : s z + (V z).length ≤ t.val := by
    rw [liveCells_length rate rewards C_star C_h z]
    exact hend
  obtain ⟨c0, hread0, _hnone, d, head, _initializer, _valid, _D, _hDlen,
    hhead, _hpay, _hinit, _hchecked, n, _hn, call, _validCall, hcall,
    hrecordEq, hcallPayload, hctx, _hcellD, _henabled, hstreamContext⟩ :=
    actual_old_cell_after_firstLive_before_boundary
      rate rewards C_star C_h t z hlaunch hbefore r hr hend'
  have hc0 : c0 = c := Option.some.inj (hread0.symm.trans hread)
  have hcellEnabled : c.enabled = ReferenceActivePhysicalStep.collectionEnabled
      call.preLedger r.input.time := by
    rw [← hc0]
    exact _henabled
  subst c0
  have hstored :
      ReferenceAssignmentPayloadPersistence.storedPayload r.input.state.coordinator =
        some payload := by
    simpa only [ReferenceFirstCollectionOldRecorderFoundation.incomingPayload?, hr,
      Option.bind_some] using hp
  have hpEq : payload = d.stream.payload := by
    by_cases hn0 : n.val = 0
    · have hzero : n = (⟨0, d.stream.positiveLength⟩ : Fin d.stream.ell) :=
        Fin.ext hn0
      have hwindowEq :
          d.stream.window[n.val]'(lt_of_lt_of_le n.isLt d.stream.withinWindow) =
            d.stream.window[0]'(Nat.zero_lt_of_lt d.stream.windowNonempty) := by
        subst n
        rfl
      have hcutRecord : r = d.stream.cutoff.cut := by
        calc
          r = d.stream.window[n.val]'(lt_of_lt_of_le n.isLt d.stream.withinWindow) :=
            hrecordEq.symm
          _ = d.stream.window[0]'(Nat.zero_lt_of_lt d.stream.windowNonempty) := hwindowEq
          _ = d.stream.cutoff.cut := d.stream.cutoffIsHead
      let execution := Classical.choice d.stream.cutoffExecution
      have hstate : r.input.state.coordinator = .live execution.live execution.owned execution.base := by
        have h := congrArg (fun record : ReferenceActivePhysicalHorizon.RoundRecord
            (p := p) (rate := rate) => record.input.state.coordinator) hcutRecord
        rw [execution.actualLive] at h
        exact h
      rw [hstate, ReferenceAssignmentPayloadPersistence.storedPayload_live] at hstored
      have hsourcePayload : payload = execution.live.payload := (Option.some.inj hstored).symm
      calc
        payload = execution.live.payload := hsourcePayload
        _ = d.stream.cutoff.payload := execution.payloadIsLive.symm
        _ = d.stream.payload := d.stream.payloadMatchesCutoff.symm
    · rcases hstreamContext with ⟨_, _⟩ | ⟨cell, _hpos, hchoiceCell, _hledger⟩
      · omega
      · have hstateWindow :
            r.input.state.coordinator =
                .collection d.stream.payload
                  (d.stream.ledgers ⟨n.val - 1,
                    Nat.lt_of_le_of_lt (Nat.sub_le _ _) n.isLt⟩) d.stream.saved :=
          cell.readyInput.1
        have hstate : r.input.state.coordinator =
            .collection d.stream.payload
              (d.stream.ledgers ⟨n.val - 1,
                Nat.lt_of_le_of_lt (Nat.sub_le _ _) n.isLt⟩) d.stream.saved :=
          hstateWindow
        rw [hstate, ReferenceAssignmentPayloadPersistence.storedPayload_collection] at hstored
        exact (Option.some.inj hstored).symm
  have hanchor : ∀ a : Fin p.K, payload.anchor a = 1 := by
    have hstreamAnchor : ∀ a : Fin p.K, d.stream.payload.anchor a = 1 := by
      by_cases hn0 : n.val = 0
      · by_cases hterminal : d.stream.cutoff.cut.input.time.val + 1 = p.T
        · have hcutAnchor := boundary_input_anchor_one rate d.stream.cutoff.cut.output.next
            d.stream.cutoff.payload d.stream.cutoff.ledger d.stream.cutoff.saved
            (d.stream.cutoffTerminalReady hterminal)
          simpa only [d.stream.payloadMatchesCutoff, d.stream.savedMatchesCutoff] using hcutAnchor
        · have hbeforeT : d.stream.cutoff.cut.input.time.val + 1 < p.T := by omega
          obtain ⟨next, _hstate, _, _, _, _, hReady, _⟩ :=
            d.stream.cutoffNextReady hbeforeT
          have hcutAnchor := ready_input_anchor_one rate next d.stream.cutoff.payload
            d.stream.cutoff.ledger d.stream.cutoff.saved hReady
          simpa only [d.stream.payloadMatchesCutoff, d.stream.savedMatchesCutoff] using hcutAnchor
      · rcases hstreamContext with ⟨_, _⟩ | ⟨cell, _hpos, _hchoiceCell, _hledger⟩
        · omega
        · exact ready_input_anchor_one rate r.input d.stream.payload
            (d.stream.ledgers ⟨n.val - 1,
              Nat.lt_of_le_of_lt (Nat.sub_le _ _) n.isLt⟩)
            d.stream.saved cell.readyInput
    intro a
    rw [hpEq]
    exact hstreamAnchor a
  have hsigma : payload.sigma.val = s z := by
    rw [hpEq, d.stream.payloadMatchesCutoff]
    simpa only [ReferenceFirstCollectionReadyStream.startTime,
      ReferenceCompletePhysicalHistory.physicalStart,
      ReferenceCompletePhysicalHistory.generatedBoundary,
      ReferenceCompletePhysicalHistory.generatedInput] using d.stream.cutoffContext.2.1
  obtain ⟨completed, hcomplete⟩ :=
    ReferenceCollectionSegmentExtraction.actual_collection_round_complete
      d.stream.cutoff.cut head d.stream.cutoff.payload d.stream.cutoff.ledger
      d.stream.cutoff.saved hhead d.stream.cutoff.outputCoordinator
  obtain ⟨hcompletedChoice, _hcompletedTime, hcompletedChecked,
    completedPayload, completedSaved, hcompletedNext⟩ :=
    ReferenceCollectionSegmentExtraction.actual_collection_round_checked
      d.stream.cutoff.cut completed hcomplete
  have hcompletedHead : completed.context = head :=
    Option.some.inj (hcompletedChoice.symm.trans hhead)
  have hcompletedFinal : completed.final = d.stream.cutoff.ledger := by
    have hsame := hcompletedNext.symm.trans d.stream.cutoff.outputCoordinator
    exact (ReferenceActivePhysicalStep.CoordinatorConfiguration.collection.inj hsame).2.1
  rw [hcompletedHead, hcompletedFinal] at hcompletedChecked
  have hheadContext := CollectionBufferProvenance.checkedRounds_success_preserves_context
    head.preLedger d.stream.cutoff.ledger [completed.input] [completed.accepted]
    hcompletedChecked
  have hfreeze : call.preLedger.freezeAt =
      FollowerCutoffScan.gridBoundary p rate.eta.val payload.sigma := by
    have hsame := hctx.trans hheadContext.symm
    have hfields := congrArg (fun context => context.2.2.2.1) hsame
    change call.preLedger.freezeAt = d.stream.cutoff.ledger.freezeAt at hfields
    rw [hfields, d.stream.cutoffContext.2.2.1, hpEq,
      d.stream.payloadMatchesCutoff]
  have hbeforeGrid : t.val + 1 <
      FollowerCutoffScan.gridBoundary p rate.eta.val payload.sigma := by
    have hEnabled : ReferenceActivePhysicalStep.collectionEnabled
        call.preLedger r.input.time = true := hcellEnabled.symm.trans hcEnabled
    have hdate := (of_decide_eq_true hEnabled).2.2
    rw [htime, hfreeze] at hdate
    exact hdate
  exact ⟨L, c, payload, r, hL, hc, hp, hrate, hnext, hlen, hr, htime,
    hcEnabled, hsigma, hanchor, hbeforeGrid⟩

/-- The original enabled OLD cell uses the first stream's unit anchor and
canonical rates. Its same precall prefix lies within the clipped episode,
so executing that prefix from zero gives the score band and inverse-rate
credit. No physical score identity or probabilistic premise is used. -/
theorem old_prefix_score_and_rate_credit (t : Fin p.T) (z : S)
    (hz : z ∈ G rate rewards C_star C_h t) :
    ∃ (L : List (RecordedQueueRun.RoundInput p.K))
      (c : RecordedQueueRun.RoundInput p.K)
      (payload : ReferenceActivePhysicalStep.Payload rate)
      (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)),
      precallCells? rate rewards C_star C_h t.val z = some L ∧
      oldCell? rate rewards C_star C_h t z = some c ∧
      incomingPayload? rate rewards C_star C_h t z = some payload ∧
      c.rate = payload.rate ∧
      precallCells? rate rewards C_star C_h (t.val + 1) z = some (L ++ [c]) ∧
      L.length = t.val - s z ∧
      payload.sigma.val = s z ∧ (∀ a : Fin p.K, payload.anchor a = 1) ∧
      L.length ≤ ReplayWeightStability.episodeHorizon rate.eta.val ∧
      (∀ a : Fin p.K,
        1 ≤ RecordedQueueRun.scoreWeight q (RecordedQueueRun.run q L) a ∧
        RecordedQueueRun.scoreWeight q (RecordedQueueRun.run q L) a < 2) ∧
      (∑ a : Fin p.K, ProductSetLaw.theta p.m
        (RecordedQueueRun.scoreWeight q (RecordedQueueRun.run q L)) a / c.rate a) ≤
          CanonicalRecordingRates.R p ∧
      actualRecord rate rewards C_star C_h t z = some r ∧
      r.input.time = t ∧ c.enabled = true ∧
      t.val + 1 < FollowerCutoffScan.gridBoundary p rate.eta.val payload.sigma := by
  obtain ⟨L, c, payload, r, hL, hc, hp, hrate, hnext, hlen, hr, htime,
    henabled, hsigma, hanchor, hbefore⟩ :=
    old_prefix_source_origin rate rewards C_star C_h t z hz
  have hspan : L.length ≤ ReplayWeightStability.episodeHorizon rate.eta.val := by
    rw [hlen, ← hsigma]
    exact elapsed_le_episodeHorizon rate payload.sigma t hbefore
  have hband := zero_run_score_envelope rate L hspan
  have hcredit : (∑ a : Fin p.K, ProductSetLaw.theta p.m
      (RecordedQueueRun.scoreWeight q (RecordedQueueRun.run q L)) a / c.rate a) ≤
        CanonicalRecordingRates.R p := by
    have hxi : c.rate = CanonicalRecordingRates.xi p rate.eta.val payload.anchor := by
      funext a
      rw [hrate, payload.rate_eq_canonical]
    rw [hxi]
    apply CanonicalRecordingRates.sum_theta_div_xi_le_R p rate.eta.property
      payload.anchor (RecordedQueueRun.scoreWeight q (RecordedQueueRun.run q L))
      payload.anchor_pos
    intro a
    rw [hanchor a, mul_one]
    exact ⟨(hband a).1, (hband a).2.le⟩
  exact ⟨L, c, payload, r, hL, hc, hp, hrate, hnext, hlen, hsigma,
    hanchor, hspan, hband, hcredit, hr, htime, henabled, hbefore⟩

end Bandits.Support.ReferenceFirstCollectionOldPrefixOriginRateCredit
