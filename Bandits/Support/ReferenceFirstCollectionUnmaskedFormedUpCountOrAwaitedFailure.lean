/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bandits Lean regret formalization contributors.
-/
module

public import Bandits.Support.ReferenceFirstCollectionUnmaskedFormedUpOrigin

/-!
# Actual unmasked formed-UP test count or an earlier awaited failure

Sources: `05_binary_transport.tex:27-55`, `06_interruptions.tex:476-481`,
and `appendix_a_local_protocol.tex:100-109,139-157` in the pinned manuscript.
The literal unmasked test set is counted on the original calendar. The
alternative is an actual fixed-awaited UP failure on the same source.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions
open scoped Classical

namespace Bandits.Support.ReferenceFirstCollectionUnmaskedFormedUpCountOrAwaitedFailure

variable {p : ConstructorDimensions.Parameters}

private theorem inclusive_card_le_strict_add_one
    (tests : Finset (Fin p.T)) (latest : Fin p.T) :
    (tests.filter (fun t => t.val ≤ latest.val)).card ≤
      (tests.filter (fun t => t.val < latest.val)).card + 1 := by
  have hsubset : tests.filter (fun t => t.val ≤ latest.val) ⊆
      insert latest (tests.filter (fun t => t.val < latest.val)) := by
    intro t ht
    obtain ⟨hmem, hle⟩ := Finset.mem_filter.mp ht
    by_cases heq : t = latest
    · exact Finset.mem_insert.mpr (Or.inl heq)
    · apply Finset.mem_insert.mpr
      right
      exact Finset.mem_filter.mpr ⟨hmem, lt_of_le_of_ne hle
        (fun h => heq (Fin.ext h))⟩
  exact (Finset.card_le_card hsubset).trans (Finset.card_insert_le _ _)

section Pending

variable {rate : ReferenceActivePhysicalStep.RateInput p}
variable {source : BootstrapPrivateRoundStreams.SourceInput p}
variable {rewards : ActualInitializationPhysicalStep.GridRewardTable p}
variable {C_star C_h : ℝ} {count : ℕ} {hcross hspan hshort}
variable (out : ReferenceFirstCollectionReadyStream.ActualInitializedStreamOutput
  (rate := rate) source rewards C_star C_h count hcross hspan hshort)

/-- Every step uses its actual FINISH erasure, so a label cannot reenter the
pending ledger of this dispatch. -/
private theorem pending_antitone (a b : Fin out.ell) (hab : a.val ≤ b.val) :
    (out.ledgers b).pending ⊆ (out.ledgers a).pending := by
  have hrec : ∀ j (hj : j < out.ell), a.val ≤ j →
      (out.ledgers ⟨j, hj⟩).pending ⊆ (out.ledgers a).pending := by
    intro j
    induction j with
    | zero =>
        intro hj ha
        have heq : (⟨0, hj⟩ : Fin out.ell) = a := by
          apply Fin.ext
          change 0 = a.val
          omega
        rw [heq]
    | succ j ih =>
        intro hj ha
        by_cases heq : a.val = j + 1
        · have heq' : (⟨j + 1, hj⟩ : Fin out.ell) = a := Fin.ext heq.symm
          rw [heq']
        · obtain ⟨_, r, incoming, cell, _, _, houtput, hprevious⟩ :=
            out.cell_at ⟨j + 1, hj⟩ (show 0 < j + 1 by omega)
          have hstep : (out.ledgers ⟨j + 1, hj⟩).pending ⊆
              (out.ledgers ⟨j, by omega⟩).pending := by
            rw [← houtput, ReferenceFirstCollectionReadyStream.cell_pending_recurrence cell,
              hprevious]
            cases ReferenceCollectionPhaseHistory.acceptedLabel r.input with
            | none => exact Finset.Subset.refl _
            | some i => exact Finset.erase_subset i _
          exact hstep.trans (ih (by omega) (by omega))
  exact hrec b.val b.isLt hab

/-- Successful reception at an actual positive stream coordinate removes its
label from every later incoming pending set in the same dispatch. -/
private theorem accepted_not_pending_later
    (q n : Fin out.ell) (hqpos : 0 < q.val) (hqn : q.val < n.val)
    (i : Fin (p.m - 1))
    (U : ReferenceCollectionPhaseHistory.UpRecord p rate)
    (haccepted : ReferenceCollectionPhaseHistory.AcceptedUp
      (out.window[q.val]'(q.isLt.trans_le out.withinWindow)).input i U) :
    i ∉ (out.ledgers ⟨n.val - 1, by omega⟩).pending := by
  obtain ⟨tail, recording, started, decoded, bank, htail, hrecording,
    hstarted, hreceive, _hparse, hsender⟩ := haccepted
  have hlabel : ReferenceCollectionPhaseHistory.acceptedLabel
      (out.window[q.val]'(q.isLt.trans_le out.withinWindow)).input = some i := by
    simp only [ReferenceCollectionPhaseHistory.acceptedLabel, htail, Option.bind_some,
      ReferenceCollectionPhaseHistory.Tail.reception, hrecording, hstarted, hreceive,
      ← hsender]
  obtain ⟨_, r, incoming, cell, _, hr, houtput, _hprevious⟩ := out.cell_at q hqpos
  have hrEq : r = out.window[q.val]'(q.isLt.trans_le out.withinWindow) :=
    (List.getElem?_eq_some_iff.mp hr).2.symm
  have hnot : i ∉ (out.ledgers q).pending := by
    rw [← houtput, ReferenceFirstCollectionReadyStream.cell_pending_recurrence cell,
      hrEq, hlabel]
    exact Finset.notMem_erase i incoming.pending
  intro hi
  exact hnot (pending_antitone out q ⟨n.val - 1, by omega⟩
    (show q.val ≤ n.val - 1 by omega) hi)

/-- Transport the actual acceptance along the dispatch's window identity
before applying the same-dispatch erasure result. -/
private theorem accepted_window_not_pending_later
    (B : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (hwindow : out.window = B) (q : Fin B.length) (n : Fin out.ell)
    (hqpos : 0 < q.val) (hqn : q.val < n.val) (i : Fin (p.m - 1))
    (U : ReferenceCollectionPhaseHistory.UpRecord p rate)
    (haccepted : ReferenceCollectionPhaseHistory.AcceptedUp B[q.val].input i U) :
    i ∉ (out.ledgers ⟨n.val - 1, by omega⟩).pending := by
  have hq : q.val < out.ell := hqn.trans n.isLt
  let qR : Fin out.ell := ⟨q.val, hq⟩
  have hget : out.window[q.val]'(hq.trans_le out.withinWindow) = B[q.val] :=
    List.getElem_of_eq hwindow (hq.trans_le out.withinWindow)
  have hacceptedR : ReferenceCollectionPhaseHistory.AcceptedUp
      (out.window[qR.val]'(qR.isLt.trans_le out.withinWindow)).input i U := by
    rw [hget]
    exact haccepted
  exact accepted_not_pending_later out qR n hqpos hqn i U hacceptedR

end Pending

/-- Two actual dispatches read the same incoming pending observation and
the same continuing coordinator constructor at a positive query. -/
private theorem dispatch_pending_and_payload
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (count : ℕ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hspan : ReferenceFirstCollectionReadyStream.startTime
      (rate := rate) source rewards C_star C_h + count ≤ p.T)
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
        source rewards C_star C_h hcross count hspan).records).length < count)
    (dI dR : ReferenceFirstCollectionStreamEmptyDispatch.ActualInitializedStreamDispatch
      (rate := rate) source rewards C_star C_h count hcross hspan hshort)
    (nI : Fin dI.stream.ell) (hnpos : 0 < nI.val) (i : Fin (p.m - 1))
    (hiI : i ∈ (dI.stream.ledgers ⟨nI.val - 1, by omega⟩).pending) :
    ∃ hnR : nI.val < dR.stream.ell,
      i ∈ (dR.stream.ledgers ⟨nI.val - 1, by omega⟩).pending ∧
      dR.stream.payload = dI.stream.payload := by
  let outI := dI.stream
  let outR := dR.stream
  let E := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
    rate source rewards C_star C_h hcross count hspan
  let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records).length
  let B := ReferenceCollectionPhaseHistory.collectionWindow E.records w
  have hwindowI : outI.window = B := outI.windowIsActual
  have hwindowR : outR.window = B := outR.windowIsActual
  have hBI : outI.ell ≤ B.length := by
    calc
      outI.ell ≤ outI.window.length := outI.withinWindow
      _ = B.length := congrArg List.length hwindowI
  let nB : Fin B.length := ⟨nI.val, nI.isLt.trans_le hBI⟩
  have hQI := ReferenceFirstCollectionPendingObservation.Q_window
    (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
    source count hcross hspan hshort dI nB
  have hQR := ReferenceFirstCollectionPendingObservation.Q_window
    (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
    source count hcross hspan hshort dR nB
  have hQmember : i ∈ ReferenceFirstCollectionPendingObservation.Q rate rewards C_star C_h
      (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
      B[nI.val].input.time source := by
    rw [hQI, ite_eq_right (show nB.val ≠ 0 by exact Nat.ne_of_gt hnpos),
      dite_eq_left nI.isLt]
    exact hiI
  have hnR : nI.val < outR.ell := by
    by_contra hnot
    rw [hQR, ite_eq_right (show nB.val ≠ 0 by exact Nat.ne_of_gt hnpos),
      dite_eq_right hnot] at hQmember
    exact Finset.notMem_empty i hQmember
  let nR : Fin outR.ell := ⟨nI.val, hnR⟩
  have hiR : i ∈ (outR.ledgers ⟨nI.val - 1, by omega⟩).pending := by
    rw [hQR, ite_eq_right (show nB.val ≠ 0 by exact Nat.ne_of_gt hnpos),
      dite_eq_left hnR] at hQmember
    exact hQmember
  obtain ⟨_, rI, incomingI, cellI, _, hrI, _, _⟩ := outI.cell_at nI hnpos
  obtain ⟨_, rR, incomingR, cellR, _, hrR, _, _⟩ := outR.cell_at nR hnpos
  have hrIEq : rI = B[nI.val] := by
    rw [hwindowI] at hrI
    exact (List.getElem?_eq_some_iff.mp hrI).2.symm
  have hrREq : rR = B[nI.val] := by
    rw [hwindowR] at hrR
    exact (List.getElem?_eq_some_iff.mp hrR).2.symm
  have hpayload : outR.payload = outI.payload := by
    have hcI := cellI.readyInput.1
    have hcR := cellR.readyInput.1
    rw [hrIEq] at hcI
    rw [hrREq] at hcR
    exact (ReferenceActivePhysicalStep.CoordinatorConfiguration.collection.inj
      (hcR.symm.trans hcI)).1
  exact ⟨hnR, hiR, hpayload⟩

/-- Supply the same actual bank and retained positive prefix to the public
awaited-failure producer. -/
private theorem initialized_second_batch_awaited_failure
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (count : ℕ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hspan : ReferenceFirstCollectionReadyStream.startTime
      (rate := rate) source rewards C_star C_h + count ≤ p.T)
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
        source rewards C_star C_h hcross count hspan).records).length < count)
    (dR : ReferenceFirstCollectionStreamEmptyDispatch.ActualInitializedStreamDispatch
      (rate := rate) source rewards C_star C_h count hcross hspan hshort) :
    let outR := dR.stream
    let E := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
      rate source rewards C_star C_h hcross count hspan
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records).length
    let B := ReferenceCollectionPhaseHistory.collectionWindow E.records w
    let hB : outR.ell ≤ B.length := by
      calc
        outR.ell ≤ outR.window.length := outR.withinWindow
        _ = B.length := congrArg List.length outR.windowIsActual
    ∀ (nR : Fin outR.ell) (hnpos : 0 < nR.val) (i : Fin (p.m - 1)),
      i ∈ (outR.ledgers ⟨nR.val - 1, by omega⟩).pending →
    ∀ (state : ReferencePrelaunchFollower.State p rate.eta)
      (memory : ActiveFollowerLifecycle.LocalMemory p),
      (B[nR.val]'(nR.isLt.trans_le hB)).input.state.followers i = .ordinary state memory →
      state.lastDown = some (outR.payload.downRecord i) →
    ∀ (U : OrdinaryMessageCodec.UpRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
      (j : Fin E.records.length),
      U.val = ActiveFollowerQueueOperation.upOfferFields state →
      j.val < w + nR.val →
      ReferenceAcceptedUpFollowerHistory.RetainedDown E.records[j.val] i
        (outR.payload.downRecord i) →
    let f := if j.val < w then 0 else j.val - w + 1
    ∀ (b : ℕ) (q : Fin B.length) (_hqpos : 0 < q.val) (hfq : f ≤ q.val)
      (_hqn : q.val ≤ nR.val) (_hqb : q.val + 1 = b),
    let chB := (B[f]'(hfq.trans_lt q.isLt)).input.state.upDecoderBank i
    let Qb := AffineBatchDecoder.quota p
    let S := (B.drop f).take (b - f)
    let tr := ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace S i
    let P := AffineBatchDecoder.positives p tr (S.map (fun r => r.input.time))
    let W := P.drop (Qb - chB.pending.length)
    chB.pending.length < Qb →
    (ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries S i).length =
      Qb - chB.pending.length + Qb →
    ∀ (last : AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p))
      (diagnostic : ReferenceActivePhysicalStep.UpDiagnostic p rate),
      B[q.val].output.coordinator.up = some diagnostic →
      last ∈ W → B[q.val].input.time = last.time →
      (diagnostic.input.upDecoderBank i).pending ++ [last] = W →
      (∀ e ∈ W, AffineBatchDecoder.equation e.sample
        (ReferenceFirstCollectionFormedUpOfferReceiver.encodedUpOfferWord U)) →
      (∃ left right : AffineChannelLaw.Word (AffineBatchDecoder.width p),
        left ≠ right ∧ AffineBatchDecoder.satisfies (AffineBatchDecoder.samples W) left ∧
          AffineBatchDecoder.satisfies (AffineBatchDecoder.samples W) right) →
      ReferenceCollectionUpFailureReadoutV2.fixedAwaitedUpFailureAt
        rate rewards C_star C_h source B[q.val].input.time := by
  intro outR E w B hB nR hnpos i hiR state memory hstate
    hdownR U j hU hjBefore hretainedR f b q hqpos hfq hqn hqb
    chB Qb S tr P W hchB hcount last diagnostic hdiagnostic hlast hlastTime hpending
    hequations hsolvers
  have hchron : S.Pairwise (fun a b => a.input.time.val < b.input.time.val) :=
    (ReferenceFirstCollectionFormedUpAwaitedFailure.actual_window_chronological
      rate source rewards C_star C_h count hcross hspan hshort).drop.take
  have htrace : P = ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries S i :=
    ReferenceCoordinatorUpIntervalWindow.actual_trace_positives_eq_retained S i hchron
  have hPlength : P.length = Qb - chB.pending.length + Qb := by
    rw [htrace]
    exact hcount
  have hfailure :=
    ReferenceFirstCollectionFormedUpAwaitedFailure.actual_formed_up_receiver_awaited_failure
      rate source rewards C_star C_h count hcross hspan hshort dR
      nR hnpos i hiR state memory hstate hdownR U hU j hjBefore hretainedR
      b q hqpos hfq hqn hqb
  extract_lets -descend -merge chA QA SA trA PA WA at hfailure
  have hchA : chA = chB := rfl
  have hPA : PA = P := rfl
  have hWA : WA = W := by
    change PA.drop (QA - chA.pending.length) = W
    rw [hPA, hchA]
  have hchAShort : chA.pending.length < QA := by
    rw [hchA]
    exact hchB
  have hPACount : PA.length = QA - chA.pending.length + QA := by
    rw [hPA, hchA]
    exact hPlength
  have hfailure := hfailure hchAShort hPACount last diagnostic hdiagnostic
    (hWA.symm ▸ hlast) hlastTime (hpending.trans hWA.symm)
    (by rw [hWA]; exact hequations) (by rw [hWA]; exact hsolvers)
  extract_lets -descend +merge +useContext at hfailure
  obtain ⟨a, _ha, _hlookup, _hcompletion, _hat, _hsigma, _hmultiple,
    _hentries, _hcalendar, hfailure⟩ := hfailure
  exact hfailure

/-- Align the independent receiver dispatch with the injected actual offer,
then retain its subthreshold alternative or its same first exact receiver. -/
private theorem aligned_prefix_receiver
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (latest : Fin p.T)
    (count : ℕ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hspan : ReferenceFirstCollectionReadyStream.startTime
      (rate := rate) source rewards C_star C_h + count ≤ p.T)
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
        source rewards C_star C_h hcross count hspan).records).length < count)
    (dI : ReferenceFirstCollectionStreamEmptyDispatch.ActualInitializedStreamDispatch
      (rate := rate) source rewards C_star C_h count hcross hspan hshort) :
    let outI := dI.stream
    let E := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
      rate source rewards C_star C_h hcross count hspan
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records).length
    let B := ReferenceCollectionPhaseHistory.collectionWindow E.records w
    ∀ (hBI : outI.ell ≤ B.length) (nI : Fin outI.ell), 0 < nI.val →
      (B[nI.val]'(nI.isLt.trans_le hBI)).input.time = latest →
      i ∈ (outI.ledgers ⟨nI.val - 1, by omega⟩).pending →
    ∀ (state : ReferencePrelaunchFollower.State p rate.eta)
      (memory : ActiveFollowerLifecycle.LocalMemory p),
      (B[nI.val]'(nI.isLt.trans_le hBI)).input.state.followers i = .ordinary state memory →
      state.lastDown = some (outI.payload.downRecord i) →
    ∀ (U : OrdinaryMessageCodec.UpRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
      (j : Fin E.records.length),
      U.val = ActiveFollowerQueueOperation.upOfferFields state →
      j.val < w + nI.val →
      ReferenceAcceptedUpFollowerHistory.RetainedDown E.records[j.val] i
        (outI.payload.downRecord i) →
      (∀ j' : Fin E.records.length, j'.val < w + nI.val →
        ReferenceAcceptedUpFollowerHistory.RetainedDown E.records[j'.val] i
          (outI.payload.downRecord i) → j' = j) →
    let f := if j.val < w then 0 else j.val - w + 1
    ∃ dR : ReferenceFirstCollectionStreamEmptyDispatch.ActualInitializedStreamDispatch
        (rate := rate) source rewards C_star C_h count hcross hspan hshort,
    let outR := dR.stream
    ∃ _hlenR : w + outR.ell ≤ count,
    ∃ hBR : outR.ell ≤ B.length,
    ∃ nR : Fin outR.ell,
      nR.val = nI.val ∧
      i ∈ (outR.ledgers ⟨nR.val - 1, by omega⟩).pending ∧
      (B[nR.val]'(nR.isLt.trans_le hBR)).input.state.followers i = .ordinary state memory ∧
      state.lastDown = some (outR.payload.downRecord i) ∧
      ReferenceAcceptedUpFollowerHistory.RetainedDown E.records[j.val] i
        (outR.payload.downRecord i) ∧
    ∃ hfR : f < B.length,
    ∃ _hfnR : f ≤ nR.val,
    let ch := (B[f]'hfR).input.state.upDecoderBank i
    let Q := AffineBatchDecoder.quota p
    let H := Q - ch.pending.length + Q
    ch.pending.length < Q ∧ Q < H ∧ H ≤ 2 * Q ∧
      ((ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries
        ((B.drop f).take (nI.val - f)) i).length < H ∨
      ∃ (b : ℕ) (_hfb : f ≤ b) (_hbn : b ≤ nR.val + 1),
      let chB := ch
      let S := (B.drop f).take (b - f)
      let tr := ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace S i
      let P := AffineBatchDecoder.positives p tr (S.map (fun r => r.input.time))
      let W := P.drop (Q - chB.pending.length)
      ∃ (q : Fin B.length) (last : AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p))
        (diagnostic : ReferenceActivePhysicalStep.UpDiagnostic p rate),
        q.val < nI.val ∧ 0 < q.val ∧ f ≤ q.val ∧ q.val ≤ nR.val ∧ q.val + 1 = b ∧
        (ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries S i).length =
          Q - chB.pending.length + Q ∧
        chB.pending.length < Q ∧ B[q.val].output.coordinator.up = some diagnostic ∧
        last ∈ W ∧ B[q.val].input.time = last.time ∧
        (diagnostic.input.upDecoderBank i).pending ++ [last] = W ∧
        (∀ e ∈ W, AffineBatchDecoder.equation e.sample
          (ReferenceFirstCollectionFormedUpOfferReceiver.encodedUpOfferWord U)) ∧
        (ReferenceCollectionPhaseHistory.AcceptedUp B[q.val].input i U ∨
          ∃ left right : AffineChannelLaw.Word (AffineBatchDecoder.width p),
            left ≠ right ∧ AffineBatchDecoder.satisfies (AffineBatchDecoder.samples W) left ∧
              AffineBatchDecoder.satisfies (AffineBatchDecoder.samples W) right)) := by
  intro outI E w B hBI nI hnpos hnTime hiI state memory hstate hdownI
    U j hU hjBefore hretainedI huniqueI f
  obtain ⟨dR, hR⟩ :=
    ReferenceFirstCollectionFormedUpFirstThresholdReceiver.actual_initialized_first_collection_formed_up_count_or_receiver
      rate source rewards C_star C_h count hcross hspan hshort
  extract_lets -descend -merge outR ER wR sR BR at hR
  obtain ⟨hlenR, hBR, hR⟩ := hR
  extract_lets -descend -merge initialR activeR JR XR at hR
  obtain ⟨hwindowR, hqueriesR⟩ := hR
  obtain ⟨hnR, hiR, hpayload⟩ := dispatch_pending_and_payload
    rate source rewards C_star C_h count hcross hspan hshort dI dR nI hnpos i hiI
  let nR : Fin outR.ell := ⟨nI.val, hnR⟩
  obtain ⟨stateR, memoryR, hstateR, _hstatusR, _hvalidR, hformedR⟩ :=
    hqueriesR nR hnpos i hiR
  clear hqueriesR
  have hconfig : stateR = state ∧ memoryR = memory :=
    DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj (hstateR.symm.trans hstate)
  rcases hconfig with ⟨hstateEq, hmemoryEq⟩
  subst stateR
  subst memoryR
  have hdownR : state.lastDown = some (outR.payload.downRecord i) := by
    rw [hpayload]
    exact hdownI
  obtain ⟨UR, jR, hUR, _hUsigmaR, _hUpositiveR, hjRBefore, hretainedR,
    huniqueR, hformationR⟩ := hformedR hdownR
  clear hformedR
  have hUEq : UR = U := Subtype.ext (hUR.trans hU.symm)
  subst UR
  have hjEq : jR = j := by
    apply huniqueI jR hjRBefore
    rw [← hpayload]
    exact hretainedR
  subst jR
  extract_lets -descend -merge fR at hformationR
  obtain ⟨hfR, hfnR, _hftimeR, _hfzeroR, _hfoneR, hprefixR⟩ := hformationR
  have hprefix := hprefixR nI.val hfnR (show nI.val ≤ nI.val + 1 by omega)
  clear hprefixR
  extract_lets -descend -merge upPrefix Pa ch Q H at hprefix
  refine ⟨dR, hlenR, hBR, nR, rfl, hiR, hstateR, hdownR, hretainedR,
    hfR, hfnR, ?_⟩
  intro chA QA HA
  have hendpoint := (ReferenceFirstCollectionReadyStep.actual_collection_window_prefix_endpoints
    rate source rewards C_star C_h count hcross hspan hshort ⟨f, hfR⟩).1
  have hchEq : ch = chA :=
    (congrArg (fun st => st.upDecoderBank i) hendpoint).symm
  have hHEq : H = HA := by
    change Q - ch.pending.length + Q = QA - chA.pending.length + QA
    rw [hchEq]
  obtain ⟨hch, hQH, hHbound, hsmall | hhit⟩ := hprefix
  · exact ⟨hchEq ▸ hch, hHEq ▸ hQH, hHEq ▸ hHbound, Or.inl (hHEq ▸ hsmall)⟩
  · refine ⟨hchEq ▸ hch, hHEq ▸ hQH, hHEq ▸ hHbound, Or.inr ?_⟩
    obtain ⟨b, hfb, hbn, hhit⟩ := hhit
    extract_lets -descend -merge S times tr P chB Qb first W uword at hhit
    obtain ⟨q, hqn, last, diagnostic, tail, recording, L,
      hfbStrict, hba, hqb, hqpos, hfq, hqn', hcount, hcountq,
      hminimal, hsingle, hreceiver⟩ := hhit
    have hqLatest : q.val < nI.val := by omega
    extract_lets -descend -merge r at hreceiver
    obtain ⟨_hqpos, _hfq, _hqb, _hqn, hrecord, htime, hrows, hselected,
      hrewards, hfirstLength, hWlength, hchB, hPbound, hWpair, hdisjoint,
      hlast, hdecision, hlastTime, hdiagnostic, hselectedFollower,
      hchannel, hupPositive, hownPositive, htail, hrecording, hround,
      hsite, hactualInput, hinputCheck, hreception, hnotInvalid, hiL,
      hacceptCheck, hexpectedOffer, hexpected, hdiagnosticTime, hsample,
      hownObservation, hdiagnosticBank, hpending, htransition, hdecoderAfter,
      hraw, hqBank, hbBank, hcompleted, hequations, hcrop, hcoordLive,
      hfollowerLive, halternative⟩ := hreceiver
    refine ⟨b, hfb, hbn, ?_⟩
    intro chBA SA trA PA WA
    have hchBEq : chB = chA := (show chB = ch from rfl).trans hchEq
    have hPA : PA = P := rfl
    have hWEq : W = WA := by
      change P.drop (Qb - chB.pending.length) = PA.drop (QA - chBA.pending.length)
      rw [hPA, hchBEq]
    have hcountA : (ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries SA i).length =
        QA - chBA.pending.length + QA := hcount.trans hHEq
    have hchAShort : chA.pending.length < QA := hchEq ▸ hch
    refine ⟨q, last, diagnostic, hqLatest, hqpos, hfq, hqn, hqb,
      hcountA, hchAShort, hdiagnostic, hWEq ▸ hlast, hlastTime,
      hpending.trans hWEq, ?_, ?_⟩
    · intro e he
      exact (hequations e (hWEq.symm ▸ he)).2.2
    · rcases halternative with haccepted | hambiguous
      · obtain ⟨_hraw, _hparse, decoded, bank, hreceive, haccepted⟩ := haccepted
        exact Or.inl haccepted
      · exact Or.inr (hWEq ▸ hambiguous.2)

/-- Count the actual earlier unmasked dates through their retained positive
entries in the one receiver slice. Distinct dates remain distinct because each
chosen entry carries its actual time. -/
private theorem actual_earlier_count_le_slice_length
    (earlier : Finset (Fin p.T))
    (entries : List (AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p)))
    (hentries : ∀ v ∈ earlier,
      ∃ e, e.time = v ∧ e ∈ entries) :
    earlier.card ≤ entries.length := by
  classical
  let times := entries.map (fun e => e.time) |>.toFinset
  have hsubset : earlier ⊆ times := by
    intro v hv
    obtain ⟨e, htime, hmem⟩ := hentries v hv
    simp only [times, List.mem_toFinset, List.mem_map]
    exact ⟨e, hmem, htime⟩
  have htime_injective : Set.InjOn (fun v : Fin p.T => v) earlier := by
    intro a _ b _ hab
    exact hab
  have htimes_map : Set.MapsTo (fun v : Fin p.T => v) earlier times := by
    intro v hv
    exact hsubset hv
  have hcard := Finset.card_le_card_of_injOn
    (fun v : Fin p.T => v) htimes_map htime_injective
  calc
    earlier.card ≤ times.card := hcard
    _ ≤ entries.length := by
      calc
        _ ≤ (entries.map (fun e => e.time)).length :=
          (entries.map (fun e => e.time)).toFinset_card_le
        _ = entries.length := by simp

/-- Count the actual unmasked strict prefix, restoring its current test, or
use the same exact receiver to produce an earlier original-source obstruction. -/
private theorem initialized_prefix_count_or_awaited_failure
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (latest : Fin p.T)
    (count : ℕ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hspan : ReferenceFirstCollectionReadyStream.startTime
      (rate := rate) source rewards C_star C_h + count ≤ p.T)
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
        source rewards C_star C_h hcross count hspan).records).length < count)
    (dI : ReferenceFirstCollectionStreamEmptyDispatch.ActualInitializedStreamDispatch
      (rate := rate) source rewards C_star C_h count hcross hspan hshort) :
    let outI := dI.stream
    let E := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
      rate source rewards C_star C_h hcross count hspan
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records).length
    let B := ReferenceCollectionPhaseHistory.collectionWindow E.records w
    ∀ (hBI : outI.ell ≤ B.length) (nI : Fin outI.ell), 0 < nI.val →
      (B[nI.val]'(nI.isLt.trans_le hBI)).input.time = latest →
      i ∈ (outI.ledgers ⟨nI.val - 1, by omega⟩).pending →
    ∀ (state : ReferencePrelaunchFollower.State p rate.eta)
      (memory : ActiveFollowerLifecycle.LocalMemory p),
      (B[nI.val]'(nI.isLt.trans_le hBI)).input.state.followers i = .ordinary state memory →
      state.lastDown = some (outI.payload.downRecord i) →
    ∀ (U : OrdinaryMessageCodec.UpRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))
      (j : Fin E.records.length),
      U.val = ActiveFollowerQueueOperation.upOfferFields state →
      j.val < w + nI.val →
      ReferenceAcceptedUpFollowerHistory.RetainedDown E.records[j.val] i
        (outI.payload.downRecord i) →
      (∀ j' : Fin E.records.length, j'.val < w + nI.val →
        ReferenceAcceptedUpFollowerHistory.RetainedDown E.records[j'.val] i
          (outI.payload.downRecord i) → j' = j) →
    let f := if j.val < w then 0 else j.val - w + 1
    let Pn := ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries
      ((B.drop f).take (nI.val - f)) i
    ((ReferenceFirstCollectionUnmaskedFormedUpOrigin.unmaskedFormedUpTests
      rate rewards C_star C_h i source).filter (fun t => t.val < latest.val)).card ≤ Pn.length →
    ((ReferenceFirstCollectionUnmaskedFormedUpOrigin.unmaskedFormedUpTests
      rate rewards C_star C_h i source).filter (fun t => t.val ≤ latest.val)).card ≤
        2 * AffineBatchDecoder.quota p ∨
      ∃ a : Fin p.T, a.val < latest.val ∧
        ReferenceCollectionUpFailureReadoutV2.fixedAwaitedUpFailureAt
          rate rewards C_star C_h source a := by
  intro outI E w B hBI nI hnpos hnTime hiI state memory hstate hdownI
    U j hU hjBefore hretainedI huniqueI f Pn hcardI
  have hinc := inclusive_card_le_strict_add_one
    (ReferenceFirstCollectionUnmaskedFormedUpOrigin.unmaskedFormedUpTests
      rate rewards C_star C_h i source) latest
  have haligned := aligned_prefix_receiver
    rate rewards C_star C_h source i latest count hcross hspan hshort dI
    hBI nI hnpos hnTime hiI state memory hstate hdownI U j hU hjBefore hretainedI huniqueI
  extract_lets -descend -merge fA at haligned
  obtain ⟨dR, hdata⟩ := haligned
  extract_lets -descend -merge outR at hdata
  obtain ⟨hlenR, hBR, nR, hnEq, hiR, hstateR, hdownR, hretainedR,
    hfR, hfnR, hdata⟩ := hdata
  extract_lets -descend -merge ch Q H at hdata
  obtain ⟨_hch, _hQH, hHbound, hsmall | hhit⟩ := hdata
  · left
    change Pn.length < H at hsmall
    have hprefix :
        ((ReferenceFirstCollectionUnmaskedFormedUpOrigin.unmaskedFormedUpTests
          rate rewards C_star C_h i source).filter (fun t => t.val < latest.val)).card + 1 ≤
          Pn.length + 1 := Nat.add_le_add_right hcardI 1
    have hplus : Pn.length + 1 ≤ H := by omega
    calc
      ((ReferenceFirstCollectionUnmaskedFormedUpOrigin.unmaskedFormedUpTests
        rate rewards C_star C_h i source).filter (fun t => t.val ≤ latest.val)).card ≤
          ((ReferenceFirstCollectionUnmaskedFormedUpOrigin.unmaskedFormedUpTests
            rate rewards C_star C_h i source).filter (fun t => t.val < latest.val)).card + 1 :=
        hinc
      _ ≤ Pn.length + 1 := hprefix
      _ ≤ H := hplus
      _ ≤ 2 * AffineBatchDecoder.quota p := hHbound
  · obtain ⟨b, hfb, hbn, hhit⟩ := hhit
    extract_lets -descend -merge chB S tr P W at hhit
    obtain ⟨q, last, diagnostic, hqLatest, hqpos, hfq, hqn, hqb, hcount,
      hchB, hdiagnostic, hlast, hlastTime, hpending, hequations, halternative⟩ := hhit
    rcases halternative with haccepted | hsolvers
    · have hwindowR : outR.window = B := outR.windowIsActual
      have hqN : q.val < nR.val := by omega
      exact False.elim ((accepted_window_not_pending_later outR B hwindowR q nR
        hqpos hqN i U haccepted) hiR)
    · have hnRpos : 0 < nR.val := by omega
      have hjRBefore : j.val < w + nR.val := by omega
      have hfailure := initialized_second_batch_awaited_failure
        rate source rewards C_star C_h count hcross hspan hshort dR
        nR hnRpos i hiR state memory hstateR hdownR U j hU hjRBefore
        hretainedR b q hqpos hfq hqn hqb
        hchB hcount last diagnostic hdiagnostic hlast hlastTime hpending hequations hsolvers
      right
      refine ⟨B[q.val].input.time, ?_, hfailure⟩
      have hchron : B.Pairwise (fun a b => a.input.time.val < b.input.time.val) :=
        ReferenceFirstCollectionFormedUpAwaitedFailure.actual_window_chronological
          rate source rewards C_star C_h count hcross hspan hshort
      have hbefore := (List.pairwise_iff_getElem.mp hchron)
        q.val nI.val q.isLt (nI.isLt.trans_le hBI) hqLatest
      rw [hnTime] at hbefore
      exact hbefore

/-- For any latest literal unmasked FORMED test, the inclusive original-calendar
count is at most twice the decoder quota, or the same source has an awaited UP
failure strictly before that latest test. No UP-failure exclusion is assumed. -/
theorem actual_first_collection_unmasked_formed_up_count_or_awaited_failure
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (latest : Fin p.T)
    (hlatest : latest ∈ ReferenceFirstCollectionUnmaskedFormedUpOrigin.unmaskedFormedUpTests
      rate rewards C_star C_h i source) :
    ((ReferenceFirstCollectionUnmaskedFormedUpOrigin.unmaskedFormedUpTests
      rate rewards C_star C_h i source).filter (fun t => t.val ≤ latest.val)).card ≤
        2 * AffineBatchDecoder.quota p ∨
      ∃ a : Fin p.T, a.val < latest.val ∧
        ReferenceCollectionUpFailureReadoutV2.fixedAwaitedUpFailureAt
          rate rewards C_star C_h source a := by
  have hinc := inclusive_card_le_strict_add_one
    (ReferenceFirstCollectionUnmaskedFormedUpOrigin.unmaskedFormedUpTests
      rate rewards C_star C_h i source) latest
  have hO := ReferenceFirstCollectionUnmaskedFormedUpOrigin.actual_unmasked_formed_up_origin_interval
    rate rewards C_star C_h source i latest hlatest
  extract_lets -descend -merge s count at hO
  obtain ⟨hcross, hspan, hshort, dI, hO⟩ := hO
  extract_lets -descend -merge outI E w B J at hO
  obtain ⟨hBI, hwindowI, nI, hnTime, hfields, hzero, hpositive⟩ := hO
  by_cases hnzero : nI.val = 0
  · left
    rw [hzero hnzero, Finset.card_empty] at hinc
    have hQpos := AffineBatchDecoder.quota_pos p
    omega
  have hnpos : 0 < nI.val := by omega
  obtain ⟨hiI, state, memory, U, j, hstate, hstatus, hvalid, hdownI,
    hU, hUsigma, hjBefore, hretainedI, huniqueI, hformationI⟩ := hpositive hnpos
  clear hzero hfields hstatus hvalid hUsigma
  extract_lets -descend -merge f at hformationI
  obtain ⟨_hfI, _hfnI, _hftimeI, _hfzeroI, _hfoneI, _hawaitI, hentriesI⟩ := hformationI
  let tests := ReferenceFirstCollectionUnmaskedFormedUpOrigin.unmaskedFormedUpTests
    (p := p) rate rewards C_star C_h i source
  let earlier := tests.filter (fun t => t.val < latest.val)
  let Pn := ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries
    ((B.drop f).take (nI.val - f)) i
  have hcardI : earlier.card ≤ Pn.length := by
    apply actual_earlier_count_le_slice_length earlier Pn
    intro v hv
    obtain ⟨k, e, _hfk, _hkn, _htime, _hsingleton, htime, _hsample, hentry⟩ := hentriesI v hv
    exact ⟨e, htime, hentry⟩
  have hcount := initialized_prefix_count_or_awaited_failure
    rate rewards C_star C_h source i latest count hcross hspan hshort dI
    hBI nI hnpos hnTime hiI state memory hstate hdownI U j hU hjBefore hretainedI
    huniqueI hcardI
  simpa only [tests, earlier] using hcount

end Bandits.Support.ReferenceFirstCollectionUnmaskedFormedUpCountOrAwaitedFailure

end
