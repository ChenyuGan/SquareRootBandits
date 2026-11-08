/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionCorrectedNumericalOverflowSum

import Mathlib.Tactic

/-!
# Actual corrected first-call current numerical output

The local join uses the original complete suffix and initialized numerical
prefix. It includes the current service and FINISH operations, preserving their
failure alternatives. No continuing-tail or stopped physical coupling is claimed.

Sources: ZIP4 `04_slow_fast_learner.tex:157-187,256-290`,
`06_interruptions.tex:355-361,391-408,425-426`, and
`appendix_a_local_protocol.tex:28-64`.
-/

@[expose] public section

noncomputable section

open Bandits.Support ConstructorDimensions
open ReferenceFirstCollectionReadyStream
open ReferenceFirstCollectionStreamEmptyDispatch
open ReferenceCollectionSegmentExtraction
open ReferenceFirstLaunchNumericalCell (queueParameters)

namespace Bandits.Support.ReferenceFirstCollectionCorrectedCurrentNumericalOutput

variable {p : ConstructorDimensions.Parameters} {rate : ReferenceActivePhysicalStep.RateInput p}

/-- Disabled raw values may differ; their register transitions agree. -/
private theorem replay_arrivals (a : Fin p.K)
    (L : List (RecordedQueueRun.RoundInput p.K)) (initial : ℕ × ℕ) :
    QueueReplay.replay (4 * rate.n) initial
        (ReferenceFirstCollectionAllArmNumericalStream.arrivals rate a L) =
      QueueReplay.replay (4 * rate.n) initial
        (L.map fun c => UnstoppedRecordedQueueComparison.unstoppedRecord
          (queueParameters rate) c a) := by
  induction L generalizing initial with
  | nil => rfl
  | cons c L ih =>
      simp only [ReferenceFirstCollectionAllArmNumericalStream.arrivals,
        List.map_cons, QueueReplay.replay, List.foldl_cons]
      have he : QueueReplay.transition (4 * rate.n) initial
          (c.enabled, RecordedQueueRun.quantizedArrival (queueParameters rate) c a) =
        QueueReplay.transition (4 * rate.n) initial
          (UnstoppedRecordedQueueComparison.unstoppedRecord (queueParameters rate) c a) := by
        cases hc : c.enabled <;>
          simp only [UnstoppedRecordedQueueComparison.unstoppedRecord, hc,
            Bool.false_eq_true, ite_false, ite_true, QueueReplay.transition]
      rw [he]
      exact ih _

private theorem replay_arrivals_eq_unstopped (a : Fin p.K)
    (L : List (RecordedQueueRun.RoundInput p.K)) :
    QueueReplay.replay (4 * rate.n) (0, 0)
        (ReferenceFirstCollectionAllArmNumericalStream.arrivals rate a L) =
      UnstoppedRecordedQueueComparison.unstoppedReplay
        (queueParameters rate) L L.length a := by
  simpa only [UnstoppedRecordedQueueComparison.unstoppedReplay,
    List.take_length, queueParameters] using replay_arrivals (rate := rate) a L (0, 0)

private theorem collection_readout_baseline (s : ℕ)
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

private theorem source_cell_congr
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

section Endpoint

variable (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (count : ℕ)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hs : startTime (rate := rate) source rewards C_star C_h + count ≤ p.T)
    (hk : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (actualEpoch (rate := rate) source rewards C_star C_h hc count hs).records).length < count)

private theorem stream_output_ledger_eq
    (d f : ActualInitializedStreamDispatch
      (rate := rate) source rewards C_star C_h count hc hs hk)
    (i : Fin d.stream.ell) (j : Fin f.stream.ell) (hij : i.val = j.val) :
    d.stream.payload = f.stream.payload ∧
      d.stream.ledgers i = f.stream.ledgers j ∧ d.stream.saved = f.stream.saved := by
  have hw : d.stream.window = f.stream.window :=
    d.stream.windowIsActual.trans f.stream.windowIsActual.symm
  obtain ⟨r, hr, _, hd, _⟩ := d.stream.output_properties i
  obtain ⟨q, hq, _, hf, _⟩ := f.stream.output_properties j
  have he : r = q := by
    rw [hw, hij, hq] at hr
    exact Option.some.inj hr.symm
  have hh := hd.symm.trans (he ▸ hf)
  exact ReferenceActivePhysicalStep.CoordinatorConfiguration.collection.inj hh

/-- Compare actual output records before identifying either existential ledger. -/
private theorem stream_endpoint_eq
    (d f : ActualInitializedStreamDispatch
      (rate := rate) source rewards C_star C_h count hc hs hk)
    (hfull : f.stream.ell = f.stream.window.length)
    :
    d.stream.ell = f.stream.ell ∧ d.record = f.record ∧
      d.stream.payload = f.stream.payload ∧ d.ledger = f.ledger ∧
      d.stream.saved = f.stream.saved := by
  have hw : d.stream.window = f.stream.window :=
    d.stream.windowIsActual.trans f.stream.windowIsActual.symm
  have hle : d.stream.ell ≤ f.stream.ell := by
    rw [hfull, ← hw]
    exact d.stream.withinWindow
  have hlen : d.stream.ell = f.stream.ell := by
    by_contra hne
    have hlt : d.stream.ell < f.stream.ell := by omega
    cases hd : d.outcome with
    | exhausted hp hex hservice hinc boundary =>
        rw [hw, ← hfull] at hex
        omega
    | empty e =>
        let j : Fin f.stream.ell := ⟨d.last.val, by
          have h := d.last.isLt
          omega⟩
        have hj : j.val + 1 < f.stream.ell := by
          have h := d.lastIsLast
          change d.last.val + 1 < f.stream.ell
          omega
        have hledger := (stream_output_ledger_eq source rewards C_star C_h count hc hs hk
          d f d.last j rfl).2.1
        have hp := f.allEarlierNonempty j hj
        rw [← hledger, ← d.ledgerIsLast, e.pendingEmpty] at hp
        exact Finset.not_nonempty_empty hp
  have hlast : d.last.val = f.last.val := by
    have hd := d.lastIsLast
    have hf := f.lastIsLast
    omega
  have hrecord : d.record = f.record := by
    have h := d.recordAt
    rw [hw, hlast, f.recordAt] at h
    exact Option.some.inj h.symm
  have hledger := stream_output_ledger_eq source rewards C_star C_h count hc hs hk
    d f d.last f.last hlast
  rw [← d.ledgerIsLast, ← f.ledgerIsLast] at hledger
  exact ⟨hlen, hrecord, hledger⟩

private theorem stream_source_lists_eq
    (d f : ActualInitializedStreamDispatch
      (rate := rate) source rewards C_star C_h count hc hs hk)
    (hlen : d.stream.ell = f.stream.ell)
    (head head0 : Choice rate)
    (valid : CoordinatorRecorderComplementBridge.LocalInputsValid
      (ReferenceActivePhysicalStep.collectionRecordingInput d.stream.cutoff.cut.output.preparation
        head.payload head.started head.weights))
    (valid0 : CoordinatorRecorderComplementBridge.LocalInputsValid
      (ReferenceActivePhysicalStep.collectionRecordingInput f.stream.cutoff.cut.output.preparation
        head0.payload head0.started head0.weights))
    (D D0 : List (RecordedQueueRun.RoundInput p.K))
    (hhead : choice d.stream.cutoff.cut.input = some head)
    (hhead0 : choice f.stream.cutoff.cut.input = some head0)
    (hDlen : D.length = d.stream.ell) (hD0len : D0.length = f.stream.ell)
    (hzero : D[0]'(by have h := d.stream.positiveLength; omega) =
      ReferenceFirstCollectionCheckedSourcePrefix.sourceCell
        rate d.stream.cutoff.cut head rewards valid)
    (hzero0 : D0[0]? = some (ReferenceFirstCollectionCheckedSourcePrefix.sourceCell
      rate f.stream.cutoff.cut head0 rewards valid0))
    (hread : ∀ k : Fin d.stream.ell, 0 < k.val →
      ReferenceLaterCollectionArrivalReadout.laterCollectionReadout
        (startTime (rate := rate) source rewards C_star C_h)
        (d.stream.window[k.val]'(lt_of_lt_of_le k.isLt d.stream.withinWindow)) =
          some (D[k.val]'(by omega)))
    (hread0 : ∀ k : Fin f.stream.ell,
      ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0
        (f.stream.window[k.val]'(lt_of_lt_of_le k.isLt f.stream.withinWindow)) = D0[k.val]?) :
    D = D0 := by
  have hw : d.stream.window = f.stream.window :=
    d.stream.windowIsActual.trans f.stream.windowIsActual.symm
  have hcut : d.stream.cutoff.cut = f.stream.cutoff.cut := by
    calc
      d.stream.cutoff.cut = d.stream.window[0]'(by have h := d.stream.windowNonempty; omega) :=
        d.stream.cutoffIsHead.symm
      _ = f.stream.window[0]'(by have h := f.stream.windowNonempty; omega) := by simp only [hw]
      _ = f.stream.cutoff.cut := f.stream.cutoffIsHead
  have hh : head = head0 := by
    rw [hcut, hhead0] at hhead
    exact Option.some.inj hhead.symm
  have hsource := source_cell_congr d.stream.cutoff.cut f.stream.cutoff.cut
    head head0 rewards valid valid0 hcut hh
  have hz0 : D[0]'(by have h := d.stream.positiveLength; omega) =
      D0[0]'(by have h := f.stream.positiveLength; omega) := by
    rw [List.getElem?_eq_getElem (by have h := f.stream.positiveLength; omega)] at hzero0
    exact hzero.trans (hsource.trans (Option.some.inj hzero0).symm)
  have he := ReferenceFirstCollectionAllArmNumericalStream.source_prefix_eq
    rate 0 f.stream.window D D0 f.stream.ell
    (by omega) (by omega) f.stream.withinWindow
    (fun _ => hz0)
    (fun k hp => by
      have h := collection_readout_baseline _ _ _
        (hread ⟨k.val, by omega⟩ hp)
      simpa only [hw] using h)
    (fun k _ => by
      have h := hread0 k
      rw [List.getElem?_eq_getElem (by omega)] at h
      exact h)
  rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)] at he
  exact he

end Endpoint

private theorem dispatch_carried_ledger
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate) (saved : Option (Fin p.T × Bool))
    (hstate : x.state.coordinator = .collection payload ledger saved) :
    match ReferenceActivePhysicalStep.dispatch x with
    | .collection _ l _ _ _ => l = ledger
    | _ => True := by
  unfold ReferenceActivePhysicalStep.dispatch
  simp only [hstate]
  by_cases hcutoff : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
  · simp only [dite_eq_left hcutoff, CoordinatorRoundDispatch.dispatch]
    rfl
  · simp only [dite_eq_right hcutoff]


private theorem firstCell_seed
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hz : z ∈ ReferenceFirstCollectionCorrectedSliceNumericalPrefix.correctedCell
      rate rewards C_star C_h u t) :
    let R := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords rate rewards C_star C_h z
    let s := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart rate rewards C_star C_h z
    let b := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.birthIndex rate rewards C_star C_h z
    ∃ (L : List (RecordedQueueRun.RoundInput p.K)) (c : RecordedQueueRun.RoundInput p.K)
      (birth : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)),
      ReferenceFirstCollectionCurrentRetainedGate.pastCells? rate rewards C_star C_h t z = some L ∧
      ReferenceFirstCollectionCurrentNumericalCell.currentCell rate rewards C_star C_h t z = some c ∧
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
        rate rewards C_star C_h (t.val + 1) z = some (L ++ [c]) ∧
      L.length = b ∧ b = t.val - s ∧ s + b = t.val ∧ c.enabled = true ∧
      R[b]? = some birth ∧
      ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some birth ∧
      birth.input.time = t ∧ birth.input.rows = z.1.2 ∧
      birth.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p z ∧
      birth.input.rewards = rewards ∧
      (match birth.output.preparation.coordinator with
      | .collection _ _ _ _
          (.laterChosen _ _ started _ instruction _ output _ clockData installed _) =>
        instruction.time = t ∧ instruction.kind = .corrected ∧
        installed = CoordinatorAssignmentRegisterInstall.installLater output clockData ∧
        installed.registers.payload = output.payload ∧ installed.registers.payload.sigma = t ∧
        installed.assignmentVector = output.assignmentVector ∧
        output.assignmentVector = LaterAssignmentStartOperation.ownAssignmentVector birth.input.row t ∧
        installed.reconstruction = output.reconstruction ∧
        (∀ a : Fin p.K,
          AssignmentScoreReconstruction.sourceScore output.reconstruction a =
            (UnstoppedRecordedQueueComparison.unstoppedReplay (queueParameters rate) L L.length a).1 ∧
          AssignmentScoreReconstruction.initialQueue output.reconstruction a =
            (UnstoppedRecordedQueueComparison.unstoppedReplay (queueParameters rate) L L.length a).2 ∧
          (output.reconstruction.registers.current a).lastService =
            (UnstoppedRecordedQueueComparison.unstoppedReplay (queueParameters rate) L L.length a).1 -
            (UnstoppedRecordedQueueComparison.unstoppedReplay (queueParameters rate)
              (L.take (L.length - 1)) (L.take (L.length - 1)).length a).1 ∧
          installed.registers.payload.queues a =
            (UnstoppedRecordedQueueComparison.unstoppedReplay (queueParameters rate) L L.length a).2) ∧
        (∀ i : Fin (p.m - 1),
          let a := installed.registers.payload.assignment.assigned i
          installed.retainedBaseScore i =
            (UnstoppedRecordedQueueComparison.unstoppedReplay (queueParameters rate) L L.length a).1 ∧
          (installed.registers.payload.downRecord i).val.q =
            (UnstoppedRecordedQueueComparison.unstoppedReplay (queueParameters rate) L L.length a).2) ∧
        (∀ j : CanonicalFastSampling.FastArm installed.registers.payload.slowSet,
          (installed.registers.complementScores j, installed.ownedRegisters.queue j) =
            UnstoppedRecordedQueueComparison.unstoppedReplay (queueParameters rate) L L.length j.val ∧
          installed.ownedRegisters.previousService j =
            (UnstoppedRecordedQueueComparison.unstoppedReplay (queueParameters rate) L L.length j.val).1 -
            (UnstoppedRecordedQueueComparison.unstoppedReplay (queueParameters rate)
              (L.take (L.length - 1)) (L.take (L.length - 1)).length j.val).1) ∧
        c.rate = installed.registers.payload.rate ∧
        c.reward = (fun a => ((rewards t a).val : ℝ) / (D p : ℝ)) ∧
        birth.output.coordinator = ReferenceActivePhysicalStep.livePostChoice
          birth.output.preparation installed.registers installed.ownedRegisters
          installed.retainedBaseScore started ∧
        birth.output.next.coordinator = birth.output.coordinator.configuration
      | _ => False) := by
  classical
  dsimp only
  obtain ⟨n, birth, theta, hb, ht, har, hcall, hrows, hselected, hrewards,
    hearlier, htime, hc, hs, hrecords, hk, f, e, hf, hu, hn,
    hlast, hnext, hcoord, hcut, hcursor, hpending, hknown, hservice, hinc, k, hcanonical, hkcut, hktime⟩ :=
    ReferenceFirstCollectionCallStoredBounds.firstCell_stored_bounds rate rewards C_star C_h u t z hz.1
  obtain ⟨birth0, hb0, har0, ht0, hchosen⟩ :=
    ReferenceFirstCollectionCorrectedNextPhysicalReadout.firstCell_firstReplacement_record
      rate rewards C_star C_h u t z hz.1
  have hbirth : birth0 = birth := Option.some.inj (har0.symm.trans har)
  subst birth0
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let s := startTime (rate := rate) z rewards C_star C_h
  let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
  let b := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.birthIndex rate rewards C_star C_h z
  have hbtime := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.firstCell_birth_time
    rate rewards C_star C_h u t z hz
  change s + b = t.val at hbtime
  change s + n = t.val at htime
  have hnb : n = b := by omega
  -- The stored first call is exactly the end of this complete collection window.
  have hfull : f.stream.ell = f.stream.window.length := by
    have hw := f.stream.windowIsActual
    change f.stream.window = ReferenceCollectionPhaseHistory.collectionWindow
      (actualEpoch (rate := rate) z rewards C_star C_h hc (p.T - s) hs).records
      (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (actualEpoch (rate := rate) z rewards C_star C_h hc (p.T - s) hs).records).length at hw
    change R = (actualEpoch (rate := rate) z rewards C_star C_h hc (p.T - s) hs).records at hrecords
    rw [← hrecords] at hw
    rw [hw]
    change f.stream.ell = (ReferenceCollectionPhaseHistory.collectionWindow R w).length
    change n = w + f.stream.ell at hn
    change n = w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length at hnb
    omega
  obtain ⟨hc0, hs0, hk0, g, head0, valid0, D0, L,
    hsu, hut, hu0, hgt, hgp, hglast, hhead0, hD0len, hD0zero, hD0read,
    hLjoin, hL, hLlen, hcoverage⟩ :=
    ReferenceFirstCollectionCurrentRetainedGate.firstCell_prefix_coverage
      rate rewards C_star C_h u t z hz.1
  have hfg : f.stream.ell = g.stream.ell := by
    change u.val = s + w at hu
    change s + w + g.stream.ell = t.val at hgt
    change n = w + f.stream.ell at hn
    omega
  have hfullg : g.stream.ell = g.stream.window.length := by
    have hw : f.stream.window = g.stream.window :=
      f.stream.windowIsActual.trans g.stream.windowIsActual.symm
    rw [← hw, ← hfg]
    exact hfull
  obtain ⟨_, _, hfgpay, hfgledger, _⟩ :=
    stream_endpoint_eq z rewards C_star C_h _ hc hs _ f g hfullg
  rw [hfgpay, hfgledger] at hcoord
  -- The numerical producer may choose a different witness. Align its actual outputs.
  obtain ⟨d, head, initializer, valid, DD, hhead, hpay, hinit, hchecked,
    hDlen, hDzero, hCells, hPrefix, hRecords, hEndpoint, hVpre, hBoundary⟩ :=
    ReferenceFirstCollectionNumericalStartReconstruction.actual_first_collection_numerical_next_start_reconstruction
      rate z rewards C_star C_h _ hc hs _
  obtain ⟨hdglen, hdgrecord, hdgpay, hdgledger, hdgsaved⟩ :=
    stream_endpoint_eq z rewards C_star C_h _ hc hs _ d g hfullg
  -- The common head choice and the same original optional readouts fix every cell.
  have hDD : DD = D0 := by
    apply stream_source_lists_eq z rewards C_star C_h _ hc hs _ d g hdglen
      head head0 valid valid0 DD D0 hhead hhead0 hDlen hD0len hDzero hD0zero
    · intro j hj
      obtain ⟨call, validCall, _, _, _, _, _, _, _, _, _, _, _, _, hread⟩ := hCells j
      exact hread hj
    · exact hD0read
  have hnum := hEndpoint (by rw [hdgledger]; exact hgp)
  rw [hdgledger, hDD] at hnum
  obtain ⟨L0, c, hL0, hcCell, hprefix, hL0len⟩ :=
    ReferenceFirstCollectionCorrectedSliceNumericalPrefix.firstCell_initial_inputs
      rate rewards C_star C_h u t z hz
  have hLL : L0 = L := Option.some.inj (hL0.symm.trans hL)
  subst L0
  have hLb : L.length = b := by change L.length = t.val - s at hLlen; omega
  have hprep : birth.output.preparation = ReferenceActivePhysicalStep.prepare birth.input := by
    rw [birth.output_eq]
    rfl
  unfold ReferenceCollectionPhaseHistory.laterChosen at hchosen
  rw [← hprep] at hchosen
  obtain ⟨nr, rr, tr, hrr, hrt, harr, hrcall, hrrows, hrselected, hrrewards, hreal⟩ :=
    ReferenceFirstCollectionCurrentNumericalCell.firstCell_realization
      rate rewards C_star C_h u t z hz.1
  have hrrEq : rr = birth := Option.some.inj (harr.symm.trans har)
  subst rr
  have hledger := dispatch_carried_ledger birth.input g.stream.payload g.ledger f.stream.saved hcoord
  rw [← birth.output.preparation.coordinator_eq] at hledger
  have hprovenance := ReferenceLaterInstallationProvenance.dispatch_laterChosen_provenance birth.input
  rw [← birth.output.preparation.coordinator_eq] at hprovenance
  cases hd : birth.output.preparation.coordinator <;>
    simp only [hd, Bool.false_eq_true] at hchosen
  rename_i old ledger clock cutoff outcome
  cases outcome <;> simp only at hchosen <;> try contradiction
  rename_i core consistent started hstart instruction hi output hlocal clockData installed selection
  simp only [hd] at hledger hprovenance hreal
  obtain ⟨hinstall, hpayActual, hsigma, hdown⟩ := hprovenance
  obtain ⟨_, _, cell, hcell, hread, hselection, hview, hpayCell, hpendingCell,
    hsigCell, hstates, hfollowers, henabled, hrate, hreward, hmarker, hquantized,
    hfollowerArrival, hrecording, hlogging, howners, hallowners⟩ := hreal
  have hceq : cell.input = c := Option.some.inj (hcell.symm.trans hcCell)
  have hinstTime : instruction.time = t :=
    (ReferenceActivePhysicalStep.later_instruction_time birth.input old ledger clock cutoff
      core started instruction hstart hi).trans ht
  have hkind := (AssignmentScoreReconstruction.reconstructLaterStart_success_equations
    _ _ output.reconstruction output.reconstruction_eq).1.2.2.2.2.1
  change instruction.kind = AssignmentScoreReconstruction.expectedLaterStartKind
    ledger.freezeAt instruction.time at hkind
  obtain ⟨freeze, hfreeze, hbefore⟩ := hz.2
  have hfreezeActual := ReferenceFirstCollectionRenewalAuxiliaryLaw.oldFreezeAt?_eq_of_record
    rate rewards C_star C_h t z birth (List.mem_of_getElem? hb) ht
    g.stream.payload g.ledger f.stream.saved hcoord
  have hfreezeEq : freeze = g.ledger.freezeAt := Option.some.inj (hfreeze.symm.trans hfreezeActual)
  have hcorrected : instruction.kind = .corrected := by
    rw [hledger, hinstTime] at hkind
    simpa only [AssignmentScoreReconstruction.expectedLaterStartKind,
      hfreezeEq ▸ hbefore, ite_true] using hkind
  let V := ReferenceFirstWindowNumericalStream.actualLiveSourceCells
    rate z rewards C_star C_h hc (p.T - s) hs
  have hVL : V ++ D0 = L := hLjoin.symm
  have hlastTake : V ++ D0.take (d.stream.ell - 1) = L.take (L.length - 1) := by
    have hlenV := ReferenceFirstWindowNumericalStream.actualLiveSourceCells_length
      rate z rewards C_star C_h hc (p.T - s) hs
    rw [← hVL, List.length_append, hD0len, ← hdglen]
    have hpos := d.stream.positiveLength
    rw [show V.length + d.stream.ell - 1 = V.length + (d.stream.ell - 1) by omega]
    simp only [List.take_append, List.take_of_length_le (by omega : V.length ≤ V.length + (d.stream.ell - 1)),
      Nat.add_sub_cancel_left]
  dsimp only [V, s] at hVL hlastTake
  -- Consume the actual successful reconstruction equations on the carried ledger.
  have hall (a : Fin p.K) :
      AssignmentScoreReconstruction.sourceScore output.reconstruction a = (UnstoppedRecordedQueueComparison.unstoppedReplay (queueParameters rate) L L.length a).1 ∧
      AssignmentScoreReconstruction.initialQueue output.reconstruction a = (UnstoppedRecordedQueueComparison.unstoppedReplay (queueParameters rate) L L.length a).2 ∧
      (output.reconstruction.registers.current a).lastService =
        (UnstoppedRecordedQueueComparison.unstoppedReplay (queueParameters rate) L L.length a).1 - (UnstoppedRecordedQueueComparison.unstoppedReplay (queueParameters rate) (L.take (L.length - 1)) (L.take (L.length - 1)).length a).1 := by
    have hcutoff := output.reconstruction.registers.cutoff_eq a
    have hcurrent := output.reconstruction.registers.current_eq a
    change ledger.cutoffRegisters a = some (output.reconstruction.registers.cutoff a) at hcutoff
    change ledger.currentRegisters a = some (output.reconstruction.registers.current a) at hcurrent
    have hcutoff0 : g.ledger.cutoffRegisters a = some (output.reconstruction.registers.cutoff a) :=
      (congrArg (fun l : ReferenceActivePhysicalStep.Ledger rate => l.cutoffRegisters a) hledger).symm.trans hcutoff
    have hcurrent0 : g.ledger.currentRegisters a = some (output.reconstruction.registers.current a) :=
      (congrArg (fun l : ReferenceActivePhysicalStep.Ledger rate => l.currentRegisters a) hledger).symm.trans hcurrent
    have hcv := Option.some.inj (hcutoff0.symm.trans (hnum a).1)
    have hqv := Option.some.inj (hcurrent0.symm.trans (hnum a).2.1)
    have hsval : AssignmentScoreReconstruction.sourceScore output.reconstruction a =
        (QueueReplay.replay (4 * rate.n) (0, 0)
          (ReferenceFirstCollectionAllArmNumericalStream.arrivals rate a L)).1 := by
      change (output.reconstruction.registers.cutoff a).score + ledger.increment a = _
      rw [hcv, hledger]
      simpa only [hVL] using (hnum a).2.2.2
    have hqval : AssignmentScoreReconstruction.initialQueue output.reconstruction a =
        (QueueReplay.replay (4 * rate.n) (0, 0)
          (ReferenceFirstCollectionAllArmNumericalStream.arrivals rate a L)).2 := by
      change (output.reconstruction.registers.current a).queue = _
      rw [hqv]
      simp only [hVL]
    have hdval := congrArg CoordinatorCollectionLedger.CurrentRegister.lastService hqv
    dsimp only at hdval
    rw [List.take_of_length_le (by omega : D0.length ≤ d.stream.ell),
      hVL, hlastTake] at hdval
    rw [replay_arrivals_eq_unstopped] at hsval hqval
    simp only [replay_arrivals_eq_unstopped] at hdval
    exact ⟨hsval, hqval, hdval⟩
  have hcoordOutput : birth.output.coordinator = ReferenceActivePhysicalStep.livePostChoice
      birth.output.preparation installed.registers installed.ownedRegisters
      installed.retainedBaseScore started := by
    have hframes := ReferenceCoordinatorRecorderCallCorrespondence.actual_call_frames birth
    simp only [hd] at hframes
    have hsel : birth.output.preparation.coordinator.selection ≠ none := by
      simp only [hd, ReferenceActivePhysicalStep.DispatchCut.selection,
        ReferenceActivePhysicalStep.selectionAt, dite_eq_left hframes.1,
        ne_eq, reduceCtorEq, not_false_eq_true]
    have he : birth.output.coordinator = birth.output.preparation.observeCoordinator := by
      rw [birth.output_eq]
      rfl
    rw [he]
    unfold ReferenceActivePhysicalStep.PreparedRound.observeCoordinator
    rw [dite_eq_right hsel, hd]
  refine ⟨L, c, birth, hL, hcCell, hprefix, hLb, by omega, hbtime,
    hceq ▸ henabled, ?_, har, ht, hrows, hselected, hrewards, ?_⟩
  · change R[b]? = some birth
    rw [← hnb]
    exact hb
  · simp only [hd]
    refine ⟨hinstTime, hcorrected, hinstall, hpayActual,
      by apply Fin.ext; simpa only [ht] using hsigma,
      ?_, ?_, ?_, ?_, ?_, ?_, hceq ▸ hrate, hceq ▸ hreward,
      hcoordOutput, ?_⟩
    · rw [hinstall]
      rfl
    · exact output.assignmentVector_eq_row_projection.trans
        (congrArg (LaterAssignmentStartOperation.ownAssignmentVector birth.input.row) hinstTime)
    · rw [hinstall]
      rfl
    · intro a
      exact ⟨(hall a).1, (hall a).2.1, (hall a).2.2,
        (by rw [hpayActual, output.payload_queues]; exact (hall a).2.1)⟩
    · intro i
      constructor
      · rw [hinstall]
        exact (CoordinatorAssignmentRegisterInstall.later_retained_base_score_eq_source
          output clockData i).trans (hall _).1
      · exact (hdown i).trans (hall _).2.1
    · intro j
      subst installed
      exact ⟨Prod.ext ((CoordinatorAssignmentRegisterInstall.later_complement_score_eq_source_score
        output clockData j).trans (hall _).1)
        ((CoordinatorAssignmentRegisterInstall.later_owned_queue_eq_initial_queue
          output clockData j).trans (hall _).2.1),
        (CoordinatorAssignmentRegisterInstall.later_owned_previous_service_eq_current_register
          output clockData j).trans (hall _).2.2⟩
    · rw [birth.output_eq]
      rfl

private theorem servicePass_recording
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (recording : CoordinatorRecordingOperation.Output p)
    (serviced : CoordinatorLiveServiceFinish.ServicedRegisters r q)
    (h : CoordinatorLiveServiceFinish.servicePass r q recording = .ok serviced) :
    serviced.recording = recording := by
  classical
  unfold CoordinatorLiveServiceFinish.servicePass at h
  by_cases hq : q.queueDomainValid
  · rw [dite_eq_left hq] at h
    by_cases hp : q.previousServiceDomainValid
    · rw [dite_eq_left hp] at h
      let arrival := fun j => CoordinatorLiveServiceFinish.complementArrival r.payload recording j
      by_cases ha : ∀ j, arrival j ≤ D p
      · rw [dite_eq_left ha] at h
        let service := fun j => CappedService.service (4 * r.payload.n) (q.queue j) (arrival j)
        by_cases hg : ∀ j, service j ≤ D p
        · rw [dite_eq_left hg] at h
          let score := fun j => r.complementScores j + service j
          by_cases hz : ∀ j, score j ≤ p.T * D p
          · rw [dite_eq_left hz] at h
            let backlog := fun j => CappedService.residual (4 * r.payload.n) (q.queue j) (arrival j)
            by_cases hb : ∀ j, backlog j ≤ p.T * D p
            · rw [dite_eq_left hb] at h
              cases h
              rfl
            · rw [dite_eq_right hb] at h
              cases h
          · rw [dite_eq_right hz] at h
            cases h
        · rw [dite_eq_right hg] at h
          cases h
      · rw [dite_eq_right ha] at h
        cases h
    · rw [dite_eq_right hp] at h
      cases h
  · rw [dite_eq_right hq] at h
    cases h

private theorem unstopped_append_enabled
    (L : List (RecordedQueueRun.RoundInput p.K)) (c : RecordedQueueRun.RoundInput p.K)
    (henabled : c.enabled = true) (a : Fin p.K) :
    UnstoppedRecordedQueueComparison.unstoppedReplay (queueParameters rate)
      (L ++ [c]) (L ++ [c]).length a =
    QueueReplay.transition (4 * rate.n)
      (UnstoppedRecordedQueueComparison.unstoppedReplay (queueParameters rate) L L.length a)
      (true, RecordedQueueRun.quantizedArrival (queueParameters rate) c a) := by
  simp only [UnstoppedRecordedQueueComparison.unstoppedReplay, List.take_length,
    List.map_append, List.map_cons, List.map_nil]
  rw [QueueReplay.replay_append]
  simp only [QueueReplay.replay, List.foldl_cons, List.foldl_nil,
    UnstoppedRecordedQueueComparison.unstoppedRecord, henabled, ite_true]
  rfl

private theorem serviced_current_replay
    (birth : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (selected : ReferenceActivePhysicalStep.Selection birth.input)
    (hpayload : selected.view.payload = r.payload)
    (L : List (RecordedQueueRun.RoundInput p.K)) (c : RecordedQueueRun.RoundInput p.K)
    (henabled : c.enabled = true)
    (hseed : ∀ j : CanonicalFastSampling.FastArm r.payload.slowSet,
      (r.complementScores j, q.queue j) =
        UnstoppedRecordedQueueComparison.unstoppedReplay (queueParameters rate) L L.length j.val)
    (hraw : ∀ a : Fin p.K, a ∉ r.payload.slowSet.val →
      ReferenceCoordinatorRecorderCallTrace.coordinatorRaw
        (ReferenceActiveHorizonMeasurability.roundRecordCode birth) a =
        some (RecordedQueueRun.quantizedArrival (queueParameters rate) c a))
    (recording : CoordinatorRecordingOperation.Output p)
    (serviced : CoordinatorLiveServiceFinish.ServicedRegisters r q)
    (hstored : birth.output.coordinator.recording = some recording)
    (hservice : CoordinatorLiveServiceFinish.servicePass r q recording = .ok serviced) :
    ∀ j : CanonicalFastSampling.FastArm r.payload.slowSet,
      (serviced.score j, serviced.queue j) =
        UnstoppedRecordedQueueComparison.unstoppedReplay (queueParameters rate)
          (L ++ [c]) (L ++ [c]).length j.val ∧
      serviced.previousService j =
        (UnstoppedRecordedQueueComparison.unstoppedReplay (queueParameters rate)
          (L ++ [c]) (L ++ [c]).length j.val).1 -
        (UnstoppedRecordedQueueComparison.unstoppedReplay (queueParameters rate) L L.length j.val).1 := by
  intro j
  -- This successful service uses precisely the retained actual recorder output.
  have hsr := servicePass_recording r q recording serviced hservice
  have hrecord := ReferenceCoordinatorRecorderCallTrace.recording_eq_actualDiagnostics birth
  change ReferenceCoordinatorRecorderCallTrace.recording
    (ReferenceActiveHorizonMeasurability.roundRecordCode birth) = birth.output.coordinator.recording at hrecord
  rw [hstored] at hrecord
  let ja : CanonicalFastSampling.FastArm selected.view.payload.slowSet :=
    ⟨j.val, by rw [hpayload]; exact j.property⟩
  have htrace := ReferenceCoordinatorRecorderCallTrace.coordinatorRaw_eq_complementArrival
    (ReferenceActiveHorizonMeasurability.roundRecordCode birth)
    (ReferenceLiveDispatchOutputMeasurability.encodeSelection selected) ja
  rw [hrecord, Option.map_some] at htrace
  have harr := Option.some.inj (htrace.symm.trans
    (hraw j.val (Finset.mem_sdiff.mp j.property).2))
  change CoordinatorLiveServiceFinish.complementArrival r.payload recording j =
    RecordedQueueRun.quantizedArrival (queueParameters rate) c j.val at harr
  have ha : serviced.arrival j = RecordedQueueRun.quantizedArrival (queueParameters rate) c j.val := by
    rw [serviced.arrival_eq, hsr]
    exact harr
  have htransition := CoordinatorLiveServiceFinish.serviced_queueReplay_transition r q serviced j
  rw [ReferenceActivePhysicalStep.payload_n_eq, hseed j, ha] at htransition
  have hpair : (serviced.score j, serviced.queue j) =
      UnstoppedRecordedQueueComparison.unstoppedReplay (queueParameters rate)
        (L ++ [c]) (L ++ [c]).length j.val :=
    htransition.symm.trans (unstopped_append_enabled L c henabled j.val).symm
  refine ⟨hpair, ?_⟩
  calc
    serviced.previousService j = serviced.score j - r.complementScores j := by
      rw [serviced.previousService_eq, serviced.score_eq, Nat.add_sub_cancel_left]
    _ = _ := congrArg₂ Nat.sub (congrArg Prod.fst hpair) (congrArg Prod.fst (hseed j))

private theorem actual_current_tail
    (birth : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r) (base : Fin (p.m - 1) → ℕ)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (selected : ReferenceActivePhysicalStep.Selection birth.input)
    (hpayload : selected.view.payload = r.payload)
    (recording0 : CoordinatorRecordingOperation.Output p)
    (hrecording0 : birth.output.coordinator.recording = some recording0)
    (L : List (RecordedQueueRun.RoundInput p.K)) (c : RecordedQueueRun.RoundInput p.K)
    (henabled : c.enabled = true)
    (hseed : ∀ j : CanonicalFastSampling.FastArm r.payload.slowSet,
      (r.complementScores j, q.queue j) =
        UnstoppedRecordedQueueComparison.unstoppedReplay (queueParameters rate) L L.length j.val)
    (hraw : ∀ a : Fin p.K, a ∉ r.payload.slowSet.val →
      ReferenceCoordinatorRecorderCallTrace.coordinatorRaw
        (ReferenceActiveHorizonMeasurability.roundRecordCode birth) a =
        some (RecordedQueueRun.quantizedArrival (queueParameters rate) c a))
    (hco : birth.output.coordinator = ReferenceActivePhysicalStep.livePostChoice
      birth.output.preparation r q base started)
    (hnext : birth.output.next.coordinator = birth.output.coordinator.configuration) :
    match birth.output.next.coordinator with
    | .live rout qout baseout =>
      rout.payload = r.payload ∧ baseout = base ∧
      ∃ (recording : CoordinatorRecordingOperation.Output p)
        (serviced : CoordinatorLiveServiceFinish.ServicedRegisters r q)
        (pending : Finset (Fin (p.m - 1))) (finished : CoordinatorPhaseClock.FinishRoundResult p),
        CoordinatorRecorderComplementBridge.run
          (ReferenceActivePhysicalStep.liveRecordingInput birth.output.preparation r started) =
            some recording ∧
        CoordinatorLiveServiceFinish.servicePass r q recording = .ok serviced ∧
        CoordinatorLocalArmChoice.confirmationUpdate r.payload started.pending
          (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
          birth.input.time birth.input.row birth.output.preparation.coordinatorObservation = some pending ∧
        CoordinatorPhaseClock.finishRound p rate.eta.val birth.input.time started.clock pending birth.input.row =
          .ok finished ∧
        birth.output.coordinator =
          ⟨.live {
              payload := r.payload
              priorClock := finished.clock
              pendingAtChoice := finished.pending
              time := birth.input.time
              gridBoundary := finished.clock.g
              complementScores := serviced.score }
            { queue := serviced.queue, previousService := serviced.previousService } base,
            birth.input.state.upDecoderBank, none, some recording, none⟩ ∧
        ∀ j : CanonicalFastSampling.FastArm rout.payload.slowSet,
          (rout.complementScores j, qout.queue j) =
            UnstoppedRecordedQueueComparison.unstoppedReplay (queueParameters rate)
              (L ++ [c]) (L ++ [c]).length j.val ∧
          qout.previousService j =
            (UnstoppedRecordedQueueComparison.unstoppedReplay (queueParameters rate)
              (L ++ [c]) (L ++ [c]).length j.val).1 -
            (UnstoppedRecordedQueueComparison.unstoppedReplay (queueParameters rate) L L.length j.val).1
    | .dagger =>
      (CoordinatorRecorderComplementBridge.run
          (ReferenceActivePhysicalStep.liveRecordingInput birth.output.preparation r started) = none ∧
        birth.output.coordinator = ReferenceActivePhysicalStep.coordinatorFailure
          birth.input.state.upDecoderBank (.live .recorderRejected) none none) ∨
      (∃ recording reason,
        CoordinatorRecorderComplementBridge.run
          (ReferenceActivePhysicalStep.liveRecordingInput birth.output.preparation r started) = some recording ∧
        CoordinatorLiveServiceFinish.servicePass r q recording = .error reason ∧
        birth.output.coordinator = ReferenceActivePhysicalStep.coordinatorFailure
          birth.input.state.upDecoderBank (.live reason) (some recording) none) ∨
      (∃ recording serviced,
        CoordinatorRecorderComplementBridge.run
          (ReferenceActivePhysicalStep.liveRecordingInput birth.output.preparation r started) = some recording ∧
        CoordinatorLiveServiceFinish.servicePass r q recording = .ok serviced ∧
        CoordinatorLocalArmChoice.confirmationUpdate r.payload started.pending
          (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
          birth.input.time birth.input.row birth.output.preparation.coordinatorObservation = none ∧
        birth.output.coordinator = ReferenceActivePhysicalStep.coordinatorFailure
          birth.input.state.upDecoderBank (.live .confirmationRejected) (some recording) none) ∨
      (∃ recording serviced pending reason,
        CoordinatorRecorderComplementBridge.run
          (ReferenceActivePhysicalStep.liveRecordingInput birth.output.preparation r started) = some recording ∧
        CoordinatorLiveServiceFinish.servicePass r q recording = .ok serviced ∧
        CoordinatorLocalArmChoice.confirmationUpdate r.payload started.pending
          (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
          birth.input.time birth.input.row birth.output.preparation.coordinatorObservation = some pending ∧
        CoordinatorPhaseClock.finishRound p rate.eta.val birth.input.time started.clock pending birth.input.row =
          .error reason ∧
        birth.output.coordinator = ReferenceActivePhysicalStep.coordinatorFailure
          birth.input.state.upDecoderBank
            (.live (CoordinatorLiveServiceFinish.finishFailureCode reason)) (some recording) none)
    | _ => False := by
  classical
  cases hr : CoordinatorRecorderComplementBridge.run
      (ReferenceActivePhysicalStep.liveRecordingInput birth.output.preparation r started) with
  | none =>
      have hout : birth.output.coordinator = ReferenceActivePhysicalStep.coordinatorFailure
          birth.input.state.upDecoderBank (.live .recorderRejected) none none := by
        rw [hco]
        simp only [ReferenceActivePhysicalStep.livePostChoice, hr]
      rw [hnext.trans (congrArg ReferenceActivePhysicalStep.CoordinatorObservation.configuration hout)]
      exact Or.inl ⟨rfl, hout⟩
  | some recording =>
    cases hs : CoordinatorLiveServiceFinish.servicePass r q recording with
    | error reason =>
        have hout : birth.output.coordinator = ReferenceActivePhysicalStep.coordinatorFailure
            birth.input.state.upDecoderBank (.live reason) (some recording) none := by
          rw [hco]
          simp only [ReferenceActivePhysicalStep.livePostChoice, hr, hs]
        rw [hnext.trans (congrArg ReferenceActivePhysicalStep.CoordinatorObservation.configuration hout)]
        exact Or.inr (Or.inl ⟨recording, reason, rfl, hs, hout⟩)
    | ok serviced =>
      cases hc : CoordinatorLocalArmChoice.confirmationUpdate r.payload started.pending
          (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
          birth.input.time birth.input.row birth.output.preparation.coordinatorObservation with
      | none =>
          have hout : birth.output.coordinator = ReferenceActivePhysicalStep.coordinatorFailure
              birth.input.state.upDecoderBank (.live .confirmationRejected) (some recording) none := by
            rw [hco]
            simp only [ReferenceActivePhysicalStep.livePostChoice, hr, hs, hc]
          rw [hnext.trans (congrArg ReferenceActivePhysicalStep.CoordinatorObservation.configuration hout)]
          exact Or.inr (Or.inr (Or.inl ⟨recording, serviced, rfl, hs, rfl, hout⟩))
      | some pending =>
        cases hf : CoordinatorPhaseClock.finishRound p rate.eta.val birth.input.time
            started.clock pending birth.input.row with
        | error reason =>
            have hout : birth.output.coordinator = ReferenceActivePhysicalStep.coordinatorFailure
                birth.input.state.upDecoderBank
                  (.live (CoordinatorLiveServiceFinish.finishFailureCode reason)) (some recording) none := by
              rw [hco]
              simp only [ReferenceActivePhysicalStep.livePostChoice, hr, hs, hc, hf]
            rw [hnext.trans (congrArg ReferenceActivePhysicalStep.CoordinatorObservation.configuration hout)]
            exact Or.inr (Or.inr (Or.inr ⟨recording, serviced, pending, reason, rfl, hs, rfl, hf, hout⟩))
        | ok finished =>
            have hout := hco.trans (ReferenceActivePhysicalStep.livePostChoice_success
              birth.output.preparation r q base started recording serviced pending finished hr hs hc hf)
            rw [hnext.trans (congrArg ReferenceActivePhysicalStep.CoordinatorObservation.configuration hout)]
            refine ⟨rfl, rfl, recording, serviced, pending, finished, rfl, hs, rfl, hf, hout, ?_⟩
            have hstored := congrArg ReferenceActivePhysicalStep.CoordinatorObservation.recording hout
            have hsame : recording0 = recording :=
              Option.some.inj (hrecording0.symm.trans hstored)
            exact serviced_current_replay birth r q selected hpayload L c henabled hseed hraw
              recording serviced (hrecording0.trans (congrArg some hsame)) hs

/-- The actual corrected first call installs the initialized strict-past replay,
executes its current service and FINISH, and retains every literal failure branch.
The adjacent record is returned only when it exists before the horizon. -/
theorem firstCell_current_output
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hz : z ∈ ReferenceFirstCollectionCorrectedSliceNumericalPrefix.correctedCell
      rate rewards C_star C_h u t) :
    let R := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords rate rewards C_star C_h z
    let s := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart rate rewards C_star C_h z
    let b := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.birthIndex rate rewards C_star C_h z
    ∃ (L : List (RecordedQueueRun.RoundInput p.K)) (c : RecordedQueueRun.RoundInput p.K)
      (birth : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)),
      ReferenceFirstCollectionCurrentRetainedGate.pastCells? rate rewards C_star C_h t z = some L ∧
      ReferenceFirstCollectionCurrentNumericalCell.currentCell rate rewards C_star C_h t z = some c ∧
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
        rate rewards C_star C_h (t.val + 1) z = some (L ++ [c]) ∧
      L.length = b ∧ b = t.val - s ∧ s + b = t.val ∧ c.enabled = true ∧
      R[b]? = some birth ∧
      ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some birth ∧
      birth.input.time = t ∧ birth.input.rows = z.1.2 ∧
      birth.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p z ∧
      birth.input.rewards = rewards ∧
      (match birth.output.preparation.coordinator with
      | .collection _ _ _ _
          (.laterChosen _ _ started _ instruction _ output _ clockData installed _) =>
        instruction.time = t ∧ instruction.kind = .corrected ∧
        installed = CoordinatorAssignmentRegisterInstall.installLater output clockData ∧
        installed.registers.payload = output.payload ∧ installed.registers.payload.sigma = t ∧
        installed.assignmentVector = output.assignmentVector ∧
        output.assignmentVector = LaterAssignmentStartOperation.ownAssignmentVector birth.input.row t ∧
        installed.reconstruction = output.reconstruction ∧
        (∀ a : Fin p.K,
          AssignmentScoreReconstruction.sourceScore output.reconstruction a =
            (UnstoppedRecordedQueueComparison.unstoppedReplay (queueParameters rate) L L.length a).1 ∧
          AssignmentScoreReconstruction.initialQueue output.reconstruction a =
            (UnstoppedRecordedQueueComparison.unstoppedReplay (queueParameters rate) L L.length a).2 ∧
          (output.reconstruction.registers.current a).lastService =
            (UnstoppedRecordedQueueComparison.unstoppedReplay (queueParameters rate) L L.length a).1 -
            (UnstoppedRecordedQueueComparison.unstoppedReplay (queueParameters rate)
              (L.take (L.length - 1)) (L.take (L.length - 1)).length a).1 ∧
          installed.registers.payload.queues a =
            (UnstoppedRecordedQueueComparison.unstoppedReplay (queueParameters rate) L L.length a).2) ∧
        (∀ i : Fin (p.m - 1),
          let a := installed.registers.payload.assignment.assigned i
          installed.retainedBaseScore i =
            (UnstoppedRecordedQueueComparison.unstoppedReplay (queueParameters rate) L L.length a).1 ∧
          (installed.registers.payload.downRecord i).val.q =
            (UnstoppedRecordedQueueComparison.unstoppedReplay (queueParameters rate) L L.length a).2) ∧
        (∀ j : CanonicalFastSampling.FastArm installed.registers.payload.slowSet,
          (installed.registers.complementScores j, installed.ownedRegisters.queue j) =
            UnstoppedRecordedQueueComparison.unstoppedReplay (queueParameters rate) L L.length j.val ∧
          installed.ownedRegisters.previousService j =
            (UnstoppedRecordedQueueComparison.unstoppedReplay (queueParameters rate) L L.length j.val).1 -
            (UnstoppedRecordedQueueComparison.unstoppedReplay (queueParameters rate)
              (L.take (L.length - 1)) (L.take (L.length - 1)).length j.val).1) ∧
        c.rate = installed.registers.payload.rate ∧
        c.reward = (fun a => ((rewards t a).val : ℝ) / (D p : ℝ)) ∧
        birth.output.coordinator = ReferenceActivePhysicalStep.livePostChoice
          birth.output.preparation installed.registers installed.ownedRegisters
          installed.retainedBaseScore started ∧
        birth.output.next.coordinator = birth.output.coordinator.configuration ∧
        (match birth.output.next.coordinator with
        | .live rout qout baseout =>
          rout.payload = installed.registers.payload ∧ baseout = installed.retainedBaseScore ∧
          ∃ (recording : CoordinatorRecordingOperation.Output p)
            (serviced : CoordinatorLiveServiceFinish.ServicedRegisters installed.registers installed.ownedRegisters)
            (pending : Finset (Fin (p.m - 1))) (finished : CoordinatorPhaseClock.FinishRoundResult p),
            CoordinatorRecorderComplementBridge.run
              (ReferenceActivePhysicalStep.liveRecordingInput birth.output.preparation installed.registers started) =
                some recording ∧
            CoordinatorLiveServiceFinish.servicePass installed.registers installed.ownedRegisters recording = .ok serviced ∧
            CoordinatorLocalArmChoice.confirmationUpdate installed.registers.payload started.pending
              (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
              birth.input.time birth.input.row birth.output.preparation.coordinatorObservation = some pending ∧
            CoordinatorPhaseClock.finishRound p rate.eta.val birth.input.time started.clock pending birth.input.row =
              .ok finished ∧
            birth.output.coordinator =
              ⟨.live {
                  payload := installed.registers.payload
                  priorClock := finished.clock
                  pendingAtChoice := finished.pending
                  time := birth.input.time
                  gridBoundary := finished.clock.g
                  complementScores := serviced.score }
                { queue := serviced.queue, previousService := serviced.previousService } installed.retainedBaseScore,
                birth.input.state.upDecoderBank, none, some recording, none⟩ ∧
            ∀ j : CanonicalFastSampling.FastArm rout.payload.slowSet,
              (rout.complementScores j, qout.queue j) =
                UnstoppedRecordedQueueComparison.unstoppedReplay (queueParameters rate)
                  (L ++ [c]) (L ++ [c]).length j.val ∧
              qout.previousService j =
                (UnstoppedRecordedQueueComparison.unstoppedReplay (queueParameters rate)
                  (L ++ [c]) (L ++ [c]).length j.val).1 -
                (UnstoppedRecordedQueueComparison.unstoppedReplay (queueParameters rate) L L.length j.val).1
        | .dagger =>
          (CoordinatorRecorderComplementBridge.run
              (ReferenceActivePhysicalStep.liveRecordingInput birth.output.preparation installed.registers started) = none ∧
            birth.output.coordinator = ReferenceActivePhysicalStep.coordinatorFailure
              birth.input.state.upDecoderBank (.live .recorderRejected) none none) ∨
          (∃ recording reason,
            CoordinatorRecorderComplementBridge.run
              (ReferenceActivePhysicalStep.liveRecordingInput birth.output.preparation installed.registers started) = some recording ∧
            CoordinatorLiveServiceFinish.servicePass installed.registers installed.ownedRegisters recording = .error reason ∧
            birth.output.coordinator = ReferenceActivePhysicalStep.coordinatorFailure
              birth.input.state.upDecoderBank (.live reason) (some recording) none) ∨
          (∃ recording serviced,
            CoordinatorRecorderComplementBridge.run
              (ReferenceActivePhysicalStep.liveRecordingInput birth.output.preparation installed.registers started) = some recording ∧
            CoordinatorLiveServiceFinish.servicePass installed.registers installed.ownedRegisters recording = .ok serviced ∧
            CoordinatorLocalArmChoice.confirmationUpdate installed.registers.payload started.pending
              (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
              birth.input.time birth.input.row birth.output.preparation.coordinatorObservation = none ∧
            birth.output.coordinator = ReferenceActivePhysicalStep.coordinatorFailure
              birth.input.state.upDecoderBank (.live .confirmationRejected) (some recording) none) ∨
          (∃ recording serviced pending reason,
            CoordinatorRecorderComplementBridge.run
              (ReferenceActivePhysicalStep.liveRecordingInput birth.output.preparation installed.registers started) = some recording ∧
            CoordinatorLiveServiceFinish.servicePass installed.registers installed.ownedRegisters recording = .ok serviced ∧
            CoordinatorLocalArmChoice.confirmationUpdate installed.registers.payload started.pending
              (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
              birth.input.time birth.input.row birth.output.preparation.coordinatorObservation = some pending ∧
            CoordinatorPhaseClock.finishRound p rate.eta.val birth.input.time started.clock pending birth.input.row =
              .error reason ∧
            birth.output.coordinator = ReferenceActivePhysicalStep.coordinatorFailure
              birth.input.state.upDecoderBank
                (.live (CoordinatorLiveServiceFinish.finishFailureCode reason)) (some recording) none)
        | _ => False)
      | _ => False) ∧
      (∀ hq : t.val + 1 < p.T,
        ∃ next : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate),
          R[b + 1]? = some next ∧
          ReferenceSourcePrefixHistoryFiltration.actualRecord
            rate rewards C_star C_h ⟨t.val + 1, hq⟩ z = some next ∧
          next.input.time = ⟨t.val + 1, hq⟩ ∧ next.input.state = birth.output.next ∧
          next.input.rows = z.1.2 ∧
          next.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p z ∧
          next.input.rewards = rewards) := by
  classical
  dsimp only
  obtain ⟨L, c, birth, hL, hc, hprefix, hLb, hbsub, htime, henabled,
    hb, har, ht, hrows, hselected, hrewards, hseed⟩ :=
    firstCell_seed rate rewards C_star C_h u t z hz
  refine ⟨L, c, birth, hL, hc, hprefix, hLb, hbsub, htime, henabled,
    hb, har, ht, hrows, hselected, hrewards, ?_, ?_⟩
  · obtain ⟨n0, birth0, theta, hb0, ht0, har0, hcall, hrows0, hselected0, hrewards0, hreal⟩ :=
      ReferenceFirstCollectionCurrentNumericalCell.firstCell_realization
        rate rewards C_star C_h u t z hz.1
    have heq : birth0 = birth := Option.some.inj (har0.symm.trans har)
    subst birth0
    cases hd : birth.output.preparation.coordinator <;> simp only [hd] at hseed
    rename_i old ledger clock cutoff outcome
    cases outcome <;> simp only at hseed
    rename_i core consistent started hstart instruction hi output hlocal clockData installed selection
    simp only [hd] at hreal ⊢
    obtain ⟨hinstTime, hkind, hinstall, hpay, hsigma, hvector, hvectorRow,
      hreconstruction, hall, hfollowers, hcomplement, hrate, hreward, hco, hnext⟩ := hseed
    obtain ⟨_, _, cell, hcell, hread, hselection, hview, hpayCell, hpendingCell,
      hsigCell, hstates, hfollowersCell, henabledCell, hrateCell, hrewardCell,
      hmarker, hquantized, hfollowerArrival, hrecording, hlogging, howners, hallowners⟩ := hreal
    have hceq : cell.input = c := Option.some.inj (hcell.symm.trans hc)
    obtain ⟨out, hout, hraw⟩ := hrecording
    have hrawActual (a : Fin p.K) (ha : a ∉ installed.registers.payload.slowSet.val) :
        ReferenceCoordinatorRecorderCallTrace.coordinatorRaw
          (ReferenceActiveHorizonMeasurability.roundRecordCode birth) a =
          some (RecordedQueueRun.quantizedArrival (queueParameters rate) c a) := by
      simpa only [hceq] using hraw a (by simpa only [hview] using ha)
    exact ⟨hinstTime, hkind, hinstall, hpay, hsigma, hvector, hvectorRow,
      hreconstruction, hall, hfollowers, hcomplement, hrate, hreward, hco, hnext,
      actual_current_tail birth installed.registers installed.ownedRegisters
        installed.retainedBaseScore started cell.selected hview out hout L c henabled
        (fun j => (hcomplement j).1) hrawActual hco hnext⟩
  · intro hq
    obtain ⟨birth0, next, hb0, hn, har0, han, ht0, htn, hstate, hrowsn, hselectedn, hrewardsn, hchosen⟩ :=
      ReferenceFirstCollectionCorrectedNextPhysicalReadout.firstCell_successor_records
        rate rewards C_star C_h u t hq z hz.1
    have heq : birth0 = birth := Option.some.inj (har0.symm.trans har)
    subst birth0
    exact ⟨next, hn, han, htn, hstate, hrowsn, hselectedn, hrewardsn⟩

end Bandits.Support.ReferenceFirstCollectionCorrectedCurrentNumericalOutput
