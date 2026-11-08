/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bandits Lean regret formalization contributors.
-/
module

public import Bandits.Support.ReferenceFirstCollectionFormedUpLocalReceiverCut

/-!
# Actual source-dispatch assembly for the formed-UP detecting cut

The same initialized dispatch supplies the pure completed batch and every
local receiver premise. Formation, pending membership, and the exact positive
count remain local conditions; this internal producer asserts no quota.

Sources: `sources/zip4/manuscript/06_interruptions.tex:476-481`,
`05_binary_transport.tex:20-55,70-124`, and
`appendix_a_local_protocol.tex:139-157`.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions
open ReferenceActivePhysicalHorizon

namespace Bandits.Support.ReferenceFirstCollectionFormedUpSourceDetectingCut

variable {p : ConstructorDimensions.Parameters}

/-- Reorder only the local let bindings of the accepted receiver result to
match the source root. All five local premises remain explicit. -/
private theorem actual_formed_query_deciding_receiver_at_source
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (count : ℕ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hspan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed + count ≤ p.T)
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
        rate source rewards C_star C_h hcross count hspan).records).length < count)
    (d : ReferenceFirstCollectionStreamEmptyDispatch.ActualInitializedStreamDispatch
      source rewards C_star C_h count hcross hspan hshort) :
    let out := d.stream
    let E := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
      rate source rewards C_star C_h hcross count hspan
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records).length
    let s := ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
    ∀ (B whole : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
      (J : Fin (M p)),
    B = ReferenceCollectionPhaseHistory.collectionWindow E.records w →
    whole = E.records →
    J = ActualInitializationPhysicalStep.selectedRowIndex p source →
    ∀ (hlen : w + out.ell ≤ count) (hBlength : out.ell ≤ B.length),
    let initial := ReferenceFirstCollectionEpochAlignment.actualLaunchState
      rate source rewards C_star C_h hcross
    let active := (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
      rate source rewards C_star C_h hcross).1
    ∀ (X : (t : ℕ) → w + t ≤ count → ReferenceActivePhysicalStep.State p rate),
    X = (fun t hwt =>
      (ReferenceActivePhysicalHorizon.run initial source.1.2 J rewards s (w + t)
        (Nat.le_trans (Nat.add_le_add_left hwt s) hspan) active).finalState) →
    ∀ (i : Fin (p.m - 1)) (f n : ℕ) (hfn : f ≤ n) (hn : n < out.ell)
      (U : OrdinaryMessageCodec.UpRecord (ReferencePrelaunchFollower.codecParams p rate.eta)),
    (∀ (b : ℕ) (_hfb : f ≤ b) (_hbn : b ≤ n + 1),
      let S := (B.drop f).take (b - f)
      let times := S.map (fun r => r.input.time)
      let tr := ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace S i
      let P := AffineBatchDecoder.positives p tr times
      let ch := (X f (by omega)).upDecoderBank i
      let Q := AffineBatchDecoder.quota p
      let window := P.drop (Q - ch.pending.length)
      P.length = Q - ch.pending.length + Q →
      (∀ e, e ∈ ch.pending → e ∉ window) ∧ P.length ≤ 2 * Q ∧
      ∀ e, e ∈ window → s + w + f ≤ e.time.val ∧ e.time.val < s + w + b ∧
        AffineBatchDecoder.equation e.sample
          (ReferenceFirstCollectionFormedUpOfferReceiver.encodedUpOfferWord U)) →
    (∀ k : Fin out.ell,
      (B[k.val]'(Nat.lt_of_lt_of_le k.isLt hBlength)).input.state = X k.val (by omega) ∧
      (B[k.val]'(Nat.lt_of_lt_of_le k.isLt hBlength)).output.next =
        X (k.val + 1) (by omega)) →
    (∀ (b : ℕ) (_hfb : f ≤ b) (hbn : b ≤ n + 1),
      let S := (B.drop f).take (b - f)
      let times := S.map (fun record => record.input.time)
      let tr := ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace S i
      let P := ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries S i
      (X b (by omega)).upDecoderBank =
        ReferenceCoordinatorUpDecoderReplay.replay (X f (by omega)).upDecoderBank
          (ReferenceCoordinatorUpDecoderReplay.retainedUpDiagnostics S) ∧
      AffineBatchDecoder.run p tr times ((X f (by omega)).upDecoderBank i) =
        (X b (by omega)).upDecoderBank i ∧
      AffineBatchDecoder.collected ((X b (by omega)).upDecoderBank i) =
        AffineBatchDecoder.collected ((X f (by omega)).upDecoderBank i) ++ P ∧
      AffineBatchDecoder.positives p tr times = P ∧
      times.Pairwise (fun a b => a.val < b.val) ∧
      ((X f (by omega)).upDecoderBank i).pending.length < AffineBatchDecoder.quota p ∧
      ∀ e, e ∈ ((X f (by omega)).upDecoderBank i).pending →
        e ∈ ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries
          (whole.take (w + f)) i ∧
        e.time.val < s + w + f ∧
        ∀ t, t ∈ times → e.time.val < t.val) →
    (∀ (t : ℕ) (ht : t ≤ out.ell),
      ReferenceUpDecoderBankInvariant.upBankInvariant (X t (by omega)) ∧
      (X t (by omega)).coordinator ≠ .dagger) →
    (∀ (q : Fin B.length) (_hqpos : 0 < q.val) (_hfq : f ≤ q.val) (_hqn : q.val ≤ n),
      let r := ReferenceFirstCollectionFormedReplyStateInterval.actualCollectionRecord B q
      PublicDiscreteDraws.slotDraw (r.input.row.2 r.input.time).1 = PublicDiscreteDraws.upSlot →
      PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
        (r.input.row.2 r.input.time).1 = i →
      ∃ (choice : ReferencePrelaunchFollower.State p rate.eta)
        (memory : ActiveFollowerLifecycle.LocalMemory p)
        (incoming : ReferenceActivePhysicalStep.Ledger rate)
        (tail : ReferenceCollectionPhaseHistory.Tail r.input)
        (recording : CoordinatorRecordingOperation.Output p)
        (L : ReferenceActivePhysicalStep.Ledger rate)
        (diagnostic : ReferenceActivePhysicalStep.UpDiagnostic p rate),
        (ReferenceFirstCollectionFormedReplyStateInterval.actualCollectionChoice B i q).configuration =
          .ordinary choice memory ∧ ActiveFollowerLifecycle.localStateDomainValid choice ∧
        choice.status = .unoccupied ∧
        r.input.state.coordinator = .collection out.payload incoming out.saved ∧
        r.input.rows = source.1.2 ∧ r.input.selected = J ∧ r.input.rewards = rewards ∧
        ReferenceActivePhysicalStep.upExpected (ReferenceActivePhysicalStep.prepare r.input) =
          some (ReferenceFirstCollectionFormedUpOfferReceiver.encodedUpOfferWord U) ∧
        ReferenceCollectionPhaseHistory.executedTail r.input = some tail ∧
        CoordinatorRecorderComplementBridge.run
          (ReferenceActivePhysicalStep.collectionRecordingInput (ReferenceActivePhysicalStep.prepare r.input)
            tail.payload tail.started tail.weights) = some recording ∧
        CoordinatorCollectionLedger.startRound tail.ledger (r.input.time.val + 1)
          (ReferenceActivePhysicalStep.collectionEnabled tail.ledger r.input.time)
          (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) = .success L ∧
        ReferenceCoordinatorUpPhysicalCall.siteLedger? (x := r.input) = some L ∧
        CoordinatorUpReception.receptionInputCheck
          (ReferenceCoordinatorUpPhysicalCall.actualUpInput r.input L) = true ∧
        r.output.coordinator.up = some diagnostic ∧
        diagnostic.input = ReferenceCoordinatorUpPhysicalCall.actualUpInput r.input L ∧
        tail.reception = some (L,
          ReferenceActivePhysicalStep.receiveUp (ReferenceActivePhysicalStep.prepare r.input) L) ∧
        (ReferenceActivePhysicalStep.receiveUp
          (ReferenceActivePhysicalStep.prepare r.input) L).result ≠ .invalid ∧
        i ∈ L.pending ∧ CoordinatorCollectionLedger.acceptUpCheck L i U = true) →
    ∀ (b : ℕ) (hfb : f ≤ b) (hbn : b ≤ n + 1),
      let S := (B.drop f).take (b - f)
      let times := S.map (fun record => record.input.time)
      let tr := ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace S i
      let P := AffineBatchDecoder.positives p tr times
      let ch := (X f ((Nat.add_le_add_left
        (hfb.trans (hbn.trans (Nat.succ_le_of_lt hn))) w).trans hlen)).upDecoderBank i
      let Q := AffineBatchDecoder.quota p
      let first := ch.pending ++ P.take (Q - ch.pending.length)
      let window := P.drop (Q - ch.pending.length)
      let uword := ReferenceFirstCollectionFormedUpOfferReceiver.encodedUpOfferWord U
      P.length = Q - ch.pending.length + Q →
      ∃ (q : Fin B.length) (_hqn : q.val ≤ n)
        (last : AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p))
        (diagnostic : ReferenceActivePhysicalStep.UpDiagnostic p rate)
        (tail : ReferenceCollectionPhaseHistory.Tail B[q.val].input)
        (recording : CoordinatorRecordingOperation.Output p)
        (L : ReferenceActivePhysicalStep.Ledger rate),
        let r := B[q.val]
        0 < q.val ∧ f ≤ q.val ∧ q.val < b ∧ q.val ≤ n ∧
        whole[w + q.val]? = some r ∧
        r.input.time.val = s + w + q.val ∧
        r.input.rows = source.1.2 ∧ r.input.selected = J ∧
        r.input.rewards = rewards ∧
        first.length = Q ∧ window.length = Q ∧ ch.pending.length < Q ∧
        P.length ≤ 2 * Q ∧
        window.Pairwise (fun a b => a.time.val < b.time.val) ∧
        (∀ e, e ∈ ch.pending → e ∉ window) ∧
        last ∈ window ∧ AffineBatchDecoder.decisionTime window = some last.time ∧
        r.input.time = last.time ∧
        r.output.coordinator.up = some diagnostic ∧
        diagnostic.input.selectedFollower = i ∧
        ReferenceSelectedAffinePairLaw.selectedChannel p
          ((source.1.2 J).2 r.input.time).1 = some (1, i) ∧
        ReferenceActiveAffinePositiveTest.upPositive r.input = true ∧
        0 < CoordinatorUpReception.roundedObservationValue p
          diagnostic.input.ownObservation ∧
        ReferenceCollectionPhaseHistory.executedTail r.input = some tail ∧
        CoordinatorRecorderComplementBridge.run
          (ReferenceActivePhysicalStep.collectionRecordingInput
            (ReferenceActivePhysicalStep.prepare r.input)
            tail.payload tail.started tail.weights) = some recording ∧
        CoordinatorCollectionLedger.startRound tail.ledger (r.input.time.val + 1)
          (ReferenceActivePhysicalStep.collectionEnabled tail.ledger r.input.time)
          (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) =
            .success L ∧
        ReferenceCoordinatorUpPhysicalCall.siteLedger? (x := r.input) = some L ∧
        diagnostic.input = ReferenceCoordinatorUpPhysicalCall.actualUpInput r.input L ∧
        CoordinatorUpReception.receptionInputCheck diagnostic.input = true ∧
        tail.reception = some (L,
          ReferenceActivePhysicalStep.receiveUp (ReferenceActivePhysicalStep.prepare r.input) L) ∧
        (ReferenceActivePhysicalStep.receiveUp
          (ReferenceActivePhysicalStep.prepare r.input) L).result ≠ .invalid ∧
        i ∈ L.pending ∧ CoordinatorCollectionLedger.acceptUpCheck L i U = true ∧
        ReferenceActivePhysicalStep.upExpected
          (ReferenceActivePhysicalStep.prepare r.input) = some uword ∧
        diagnostic.expected = some uword ∧
        diagnostic.input.time = r.input.time ∧
        diagnostic.input.affineSample = ((source.1.2 J).2 r.input.time).2 (1, i) ∧
        diagnostic.input.ownObservation =
          (ReferenceActivePhysicalStep.prepare r.input).feedback.feedback
            (ActiveRoundActions.coordinator p.two_le_m) ∧
        diagnostic.input.upDecoderBank = r.input.state.upDecoderBank ∧
        (diagnostic.input.upDecoderBank i).pending ++ [last] = window ∧
        CoordinatorUpReception.decoderTransition diagnostic.input =
          ({ pending := [], completed := ch.completed ++ [first, window] },
            AffineBatchDecoder.batchOutput window) ∧
        diagnostic.decoderAfter =
          { pending := [], completed := ch.completed ++ [first, window] } ∧
        diagnostic.raw = AffineBatchDecoder.batchOutput window ∧
        (X (q.val + 1) ((Nat.add_le_add_left
          ((Nat.succ_le_succ _hqn).trans (Nat.succ_le_of_lt hn)) w).trans hlen)).upDecoderBank i = diagnostic.decoderAfter ∧
        (X b ((Nat.add_le_add_left
          (hbn.trans (Nat.succ_le_of_lt hn)) w).trans hlen)).upDecoderBank i = diagnostic.decoderAfter ∧
        window ∈ diagnostic.decoderAfter.completed ∧
        (∀ e, e ∈ window → s + w + f ≤ e.time.val ∧
          e.time.val < s + w + b ∧ AffineBatchDecoder.equation e.sample uword) ∧
        AffineBatchDecoder.positives p
          (ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace
            ((B.drop f).take (q.val + 1 - f)) i)
          (((B.drop f).take (q.val + 1 - f)).map (fun r => r.input.time)) = P ∧
        r.output.next.coordinator ≠ .dagger ∧
        r.output.next.followers i ≠ .dagger ∧
        ((diagnostic.raw = some uword ∧
          ReferenceCollectionPhaseHistory.filteredParsed r.input L = some U ∧
          ∃ (decoded : ReferenceActivePhysicalStep.Ledger rate)
            (bank : CoordinatorUpReception.UpDecoderBank p),
            (ReferenceActivePhysicalStep.receiveUp
              (ReferenceActivePhysicalStep.prepare r.input) L).result =
                .success (decoded, bank) ∧
            ReferenceCollectionPhaseHistory.AcceptedUp r.input i U) ∨
          (diagnostic.raw = none ∧
            ∃ left right : AffineChannelLaw.Word (AffineBatchDecoder.width p),
              left ≠ right ∧
              AffineBatchDecoder.satisfies (AffineBatchDecoder.samples window) left ∧
              AffineBatchDecoder.satisfies (AffineBatchDecoder.samples window) right)) := by
  intro out E w s B whole J hB hwhole hJ hlen hBlength initial active X hX i f n hfn hn U
    hpure hEndpoints hsaved hstates hreceiver
  subst B
  subst whole
  subst J
  subst X
  have hfinish :=
    ReferenceFirstCollectionFormedUpLocalReceiverCut.actual_formed_query_deciding_receiver
      rate source rewards C_star C_h count hcross hspan hshort d hlen hBlength
      i f n hfn hn U hpure hEndpoints hsaved hstates hreceiver
  intro b hfb hbn S times tr P ch Q first window uword hcount
  exact hfinish b hfb hbn hcount

/-- The single initialized source dispatch supplies all local receiver
premises, retaining the same formed reply and retained DOWN index. -/
private theorem actual_initialized_formed_up_local_premises
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (count : ℕ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hspan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed + count ≤ p.T)
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
        rate source rewards C_star C_h hcross count hspan).records).length < count) :
    ∃ d : ReferenceFirstCollectionStreamEmptyDispatch.ActualInitializedStreamDispatch
        source rewards C_star C_h count hcross hspan hshort,
      let out := d.stream
      let E := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
        rate source rewards C_star C_h hcross count hspan
      let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records).length
      let s := ReferenceInitializationRun.elapsed p
        (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
      let B := ReferenceCollectionPhaseHistory.collectionWindow E.records w
      ∃ hlen : w + out.ell ≤ count,
        ∃ hBlength : out.ell ≤ B.length,
        let initial := ReferenceFirstCollectionEpochAlignment.actualLaunchState
          rate source rewards C_star C_h hcross
        let active := (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
          rate source rewards C_star C_h hcross).1
        let J := ActualInitializationPhysicalStep.selectedRowIndex p source
        ∃ X : (t : ℕ) → w + t ≤ count → ReferenceActivePhysicalStep.State p rate,
          X = (fun t hwt =>
            (ReferenceActivePhysicalHorizon.run initial source.1.2 J rewards s (w + t)
              (Nat.le_trans (Nat.add_le_add_left hwt s) hspan) active).finalState) ∧
        out.window = B ∧
        (∀ k : Fin out.ell,
          (B[k.val]'(Nat.lt_of_lt_of_le k.isLt hBlength)).input.state = X k.val (by omega) ∧
          (B[k.val]'(Nat.lt_of_lt_of_le k.isLt hBlength)).output.next =
            X (k.val + 1) (by omega)) ∧
        (∀ (t : ℕ) (ht : t ≤ out.ell),
          ReferenceUpDecoderBankInvariant.upBankInvariant (X t (by omega)) ∧
          (X t (by omega)).coordinator ≠ .dagger) ∧
        ∀ (n : Fin out.ell) (_hn : 0 < n.val) (i : Fin (p.m - 1)),
          i ∈ (out.ledgers ⟨n.val - 1, Nat.lt_of_le_of_lt (Nat.sub_le n.val 1) n.isLt⟩).pending →
          ∃ (state : ReferencePrelaunchFollower.State p rate.eta)
            (memory : ActiveFollowerLifecycle.LocalMemory p),
            (B[n.val]'(Nat.lt_of_lt_of_le n.isLt hBlength)).input.state.followers i = .ordinary state memory ∧
            state.status = .unoccupied ∧ ActiveFollowerLifecycle.localStateDomainValid state ∧
            (state.lastDown = some (out.payload.downRecord i) →
              ∃ (U : OrdinaryMessageCodec.UpRecord
                  (ReferencePrelaunchFollower.codecParams p rate.eta))
                (j : Fin E.records.length),
                U.val = ActiveFollowerQueueOperation.upOfferFields state ∧
                U.val.sigma = s + 1 ∧ 1 ≤ U.val.sigma ∧ j.val < w + n.val ∧
                ReferenceAcceptedUpFollowerHistory.RetainedDown E.records[j.val] i
                  (out.payload.downRecord i) ∧
                (∀ j' : Fin E.records.length, j'.val < w + n.val →
                  ReferenceAcceptedUpFollowerHistory.RetainedDown E.records[j'.val] i
                    (out.payload.downRecord i) → j' = j) ∧
                let f := if j.val < w then 0 else j.val - w + 1
                ∃ hf : f < B.length,
                  f ≤ n.val ∧
                  B[f].input.time.val + 1 = max (s + w + 1) (s + j.val + 2) ∧
                  (j.val < w → f = 0) ∧ (j.val = w → f = 1) ∧
                  (∀ (b : ℕ) (_hfb : f ≤ b) (_hbn : b ≤ n.val + 1),
                    let S := (B.drop f).take (b - f)
                    let times := S.map (fun r => r.input.time)
                    let tr := ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace S i
                    let P := AffineBatchDecoder.positives p tr times
                    let ch := (X f (by omega)).upDecoderBank i
                    let Q := AffineBatchDecoder.quota p
                    let window := P.drop (Q - ch.pending.length)
                    P.length = Q - ch.pending.length + Q →
                    (∀ e, e ∈ ch.pending → e ∉ window) ∧ P.length ≤ 2 * Q ∧
                    ∀ e, e ∈ window → s + w + f ≤ e.time.val ∧ e.time.val < s + w + b ∧
                      AffineBatchDecoder.equation e.sample
                        (ReferenceFirstCollectionFormedUpOfferReceiver.encodedUpOfferWord U)) ∧
                  (∀ (b : ℕ) (_hfb : f ≤ b) (hbn : b ≤ n.val + 1),
                    let S := (B.drop f).take (b - f)
                    let times := S.map (fun record => record.input.time)
                    let tr := ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace S i
                    let P := ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries S i
                    (X b (by omega)).upDecoderBank =
                      ReferenceCoordinatorUpDecoderReplay.replay (X f (by omega)).upDecoderBank
                        (ReferenceCoordinatorUpDecoderReplay.retainedUpDiagnostics S) ∧
                    AffineBatchDecoder.run p tr times ((X f (by omega)).upDecoderBank i) =
                      (X b (by omega)).upDecoderBank i ∧
                    AffineBatchDecoder.collected ((X b (by omega)).upDecoderBank i) =
                      AffineBatchDecoder.collected ((X f (by omega)).upDecoderBank i) ++ P ∧
                    AffineBatchDecoder.positives p tr times = P ∧
                    times.Pairwise (fun a b => a.val < b.val) ∧
                    ((X f (by omega)).upDecoderBank i).pending.length < AffineBatchDecoder.quota p ∧
                    ∀ e, e ∈ ((X f (by omega)).upDecoderBank i).pending →
                      e ∈ ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries
                        (E.records.take (w + f)) i ∧
                      e.time.val < s + w + f ∧
                      ∀ t, t ∈ times → e.time.val < t.val) ∧
                  (∀ (q : Fin B.length) (_hqpos : 0 < q.val) (_hfq : f ≤ q.val) (_hqn : q.val ≤ n.val),
                    let r := ReferenceFirstCollectionFormedReplyStateInterval.actualCollectionRecord B q
                    PublicDiscreteDraws.slotDraw (r.input.row.2 r.input.time).1 = PublicDiscreteDraws.upSlot →
                    PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
                      (r.input.row.2 r.input.time).1 = i →
                    ∃ (choice : ReferencePrelaunchFollower.State p rate.eta)
                      (memory : ActiveFollowerLifecycle.LocalMemory p)
                      (incoming : ReferenceActivePhysicalStep.Ledger rate)
                      (tail : ReferenceCollectionPhaseHistory.Tail r.input)
                      (recording : CoordinatorRecordingOperation.Output p)
                      (L : ReferenceActivePhysicalStep.Ledger rate)
                      (diagnostic : ReferenceActivePhysicalStep.UpDiagnostic p rate),
                      (ReferenceFirstCollectionFormedReplyStateInterval.actualCollectionChoice B i q).configuration =
                        .ordinary choice memory ∧ ActiveFollowerLifecycle.localStateDomainValid choice ∧
                      choice.status = .unoccupied ∧
                      r.input.state.coordinator = .collection out.payload incoming out.saved ∧
                      r.input.rows = source.1.2 ∧ r.input.selected = J ∧ r.input.rewards = rewards ∧
                      ReferenceActivePhysicalStep.upExpected (ReferenceActivePhysicalStep.prepare r.input) =
                        some (ReferenceFirstCollectionFormedUpOfferReceiver.encodedUpOfferWord U) ∧
                      ReferenceCollectionPhaseHistory.executedTail r.input = some tail ∧
                      CoordinatorRecorderComplementBridge.run
                        (ReferenceActivePhysicalStep.collectionRecordingInput (ReferenceActivePhysicalStep.prepare r.input)
                          tail.payload tail.started tail.weights) = some recording ∧
                      CoordinatorCollectionLedger.startRound tail.ledger (r.input.time.val + 1)
                        (ReferenceActivePhysicalStep.collectionEnabled tail.ledger r.input.time)
                        (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) = .success L ∧
                      ReferenceCoordinatorUpPhysicalCall.siteLedger? (x := r.input) = some L ∧
                      CoordinatorUpReception.receptionInputCheck
                        (ReferenceCoordinatorUpPhysicalCall.actualUpInput r.input L) = true ∧
                      r.output.coordinator.up = some diagnostic ∧
                      diagnostic.input = ReferenceCoordinatorUpPhysicalCall.actualUpInput r.input L ∧
                      tail.reception = some (L,
                        ReferenceActivePhysicalStep.receiveUp (ReferenceActivePhysicalStep.prepare r.input) L) ∧
                      (ReferenceActivePhysicalStep.receiveUp
                        (ReferenceActivePhysicalStep.prepare r.input) L).result ≠ .invalid ∧
                      i ∈ L.pending ∧ CoordinatorCollectionLedger.acceptUpCheck L i U = true)) := by
  classical
  obtain ⟨d, registers, owned, base, cutRecord, _, _,
    _, _, _, _, _, hresult⟩ :=
    ReferenceFirstCollectionFormedUpSecondPureBatch.actual_initialized_first_collection_formed_up_second_pure_batch
      rate source rewards C_star C_h count hcross hspan hshort
  refine ⟨d, ?_⟩
  intro out E w s B
  have hWindow : out.window = B := out.windowIsActual
  have hBlength : out.ell ≤ B.length := hWindow ▸ out.withinWindow
  rcases hresult with ⟨⟨hlen, hEndpoint, hStateFacts, _, _⟩, hqueries⟩
  have hlen : w + out.ell ≤ count := hlen
  refine ⟨hlen, hBlength, ?_⟩
  intro initial active J
  let X (t : ℕ) (hwt : w + t ≤ count) : ReferenceActivePhysicalStep.State p rate :=
    (ReferenceActivePhysicalHorizon.run initial source.1.2 J rewards s (w + t)
      (Nat.le_trans (Nat.add_le_add_left hwt s) hspan) active).finalState
  refine ⟨X, rfl, hWindow, hEndpoint, hStateFacts, ?_⟩
  intro n hn i hi
  have hnEll : n.val < out.ell := n.isLt
  obtain ⟨rN, incoming, cell, state, memory, hrN, _, _, _,
    _, _, _, _, _, hstate, hstatus,
    hvalid, _, _, _, _, _, _, _, hformed⟩ :=
      hqueries n hn i hi
  clear hqueries
  have hrNB : B[n.val]'(Nat.lt_of_lt_of_le hnEll hBlength) = rN := by
    rw [hWindow] at hrN
    exact (List.getElem?_eq_some_iff.mp hrN).2
  refine ⟨state, memory, by rw [hrNB]; exact hstate, hstatus, hvalid, ?_⟩
  intro hlastDown
  obtain ⟨U, hUfields, hUsigma, hUpositive, _, _, _,
    j, hjIndex, acceptedRecord, hjbefore, _, hretained, _,
    _, _, _, _, hunique, hinterval⟩ := hformed hlastDown
  clear hformed
  let retainedIndex : Fin E.records.length := ⟨j, hjIndex⟩
  let f := if j < w then 0 else j - w + 1
  obtain ⟨hf, hfn, hftime, hfzero, hfone, _,
    hsourceBanks, hgeometry, hchoices⟩ := hinterval
  refine ⟨U, retainedIndex, hUfields, hUsigma, hUpositive, hjbefore, hretained, ?_,
    hf, hfn, hftime, hfzero, hfone, ?_⟩
  · intro j' hj' hretained'
    apply Fin.ext
    exact hunique j'.val j'.isLt E.records[j'.val] hj'
      (List.getElem?_eq_getElem j'.isLt) hretained'
  · refine ⟨(by
        intro b hfb hbn S times tr P ch Q window hcount
        clear hchoices hEndpoint hsourceBanks hStateFacts
        obtain ⟨firstA, windowA, _lastA, _indexA, _recordA, _diagnosticA,
          _, _, hwindowA, _, _, _,
          hdisjoint, hbound2, _, _, _, _,
          _, _, _, _, hwindowEquations⟩ :=
            hgeometry b hfb hbn hcount
        have hwindowEq : windowA = window := hwindowA
        rw [hwindowEq] at hdisjoint hwindowEquations
        exact ⟨hdisjoint, hbound2, hwindowEquations⟩), hsourceBanks, ?_⟩
    intro q hqpos hfq hqn r hslot hdraw
    obtain ⟨choice, choiceMemory, hchoice, hchoiceValid, hchoiceStatus, _, _,
      _, _, _, _, _,
      _, _, before, beforeMemory, _,
      _, _, _, _, hselectedUp, _,
      hcontinuing⟩ := hchoices q hfq hqn
    clear hchoices
    have hexpected : ReferenceActivePhysicalStep.upExpected
        (ReferenceActivePhysicalStep.prepare r.input) =
          some (ReferenceFirstCollectionFormedUpOfferReceiver.encodedUpOfferWord U) :=
      (hselectedUp hslot hdraw).2.2.2
    clear hselectedUp
    obtain ⟨jK, recordK, incomingK, cellK, _, _, _, _,
      hrecordKAt, hcollection, _, hrowsK, hselectedK, hrewardsK,
      _, _, tail, recording, L, diagnosticK,
      htail, _, _, hrecording, hstartL, _,
      hsite, hcheck, hdiagK, hinputK, htailReception, hnoninvalid,
      _, _, _, hiL, haccept, _⟩ := hcontinuing hqpos
    clear hcontinuing
    have hrecordKEq : r = recordK := hrecordKAt
    rw [hrecordKEq] at hexpected ⊢
    exact ⟨choice, choiceMemory, incomingK, tail, recording, L, diagnosticK,
      hchoice, hchoiceValid, hchoiceStatus, hcollection, hrowsK, hselectedK,
      hrewardsK, hexpected, htail, hrecording, hstartL, hsite, hcheck,
      hdiagK, hinputK, htailReception, hnoninvalid, hiL, haccept⟩

/-- Assemble the source query witnesses over literal data parameters.
This proof only threads already produced facts through the receiver theorem. -/
private theorem assemble_formed_queries
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (s w count ell : ℕ)
    (B whole : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (saved : Option (Fin p.T × Bool))
    (ledgers : Fin ell → ReferenceActivePhysicalStep.Ledger rate)
    (hlen : w + ell ≤ count) (hBlength : ell ≤ B.length)
    (X : (t : ℕ) → w + t ≤ count → ReferenceActivePhysicalStep.State p rate)
    (hEndpoints : ∀ k : Fin ell,
      (B[k.val]'(Nat.lt_of_lt_of_le k.isLt hBlength)).input.state = X k.val (by omega) ∧
      (B[k.val]'(Nat.lt_of_lt_of_le k.isLt hBlength)).output.next =
        X (k.val + 1) (by omega))
    (hstates : ∀ (t : ℕ) (ht : t ≤ ell),
      ReferenceUpDecoderBankInvariant.upBankInvariant (X t (by omega)) ∧
      (X t (by omega)).coordinator ≠ .dagger)
    (hqueries : ∀ (n : Fin ell) (_hn : 0 < n.val) (i : Fin (p.m - 1)),
      i ∈ (ledgers ⟨n.val - 1, Nat.lt_of_le_of_lt (Nat.sub_le n.val 1) n.isLt⟩).pending →
      ∃ (state : ReferencePrelaunchFollower.State p rate.eta)
        (memory : ActiveFollowerLifecycle.LocalMemory p),
        (B[n.val]'(Nat.lt_of_lt_of_le n.isLt hBlength)).input.state.followers i = .ordinary state memory ∧
        state.status = .unoccupied ∧ ActiveFollowerLifecycle.localStateDomainValid state ∧
        (state.lastDown = some (payload.downRecord i) →
          ∃ (U : OrdinaryMessageCodec.UpRecord
              (ReferencePrelaunchFollower.codecParams p rate.eta))
            (j : Fin whole.length),
            U.val = ActiveFollowerQueueOperation.upOfferFields state ∧
            U.val.sigma = s + 1 ∧ 1 ≤ U.val.sigma ∧ j.val < w + n.val ∧
            ReferenceAcceptedUpFollowerHistory.RetainedDown whole[j.val] i
              (payload.downRecord i) ∧
            (∀ j' : Fin whole.length, j'.val < w + n.val →
              ReferenceAcceptedUpFollowerHistory.RetainedDown whole[j'.val] i
                (payload.downRecord i) → j' = j) ∧
            let f := if j.val < w then 0 else j.val - w + 1
            ∃ hf : f < B.length,
              f ≤ n.val ∧
              B[f].input.time.val + 1 = max (s + w + 1) (s + j.val + 2) ∧
              (j.val < w → f = 0) ∧ (j.val = w → f = 1) ∧
              (∀ (b : ℕ) (_hfb : f ≤ b) (_hbn : b ≤ n.val + 1),
                let S := (B.drop f).take (b - f)
                let times := S.map (fun r => r.input.time)
                let tr := ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace S i
                let P := AffineBatchDecoder.positives p tr times
                let ch := (X f (by omega)).upDecoderBank i
                let Q := AffineBatchDecoder.quota p
                let window := P.drop (Q - ch.pending.length)
                P.length = Q - ch.pending.length + Q →
                (∀ e, e ∈ ch.pending → e ∉ window) ∧ P.length ≤ 2 * Q ∧
                ∀ e, e ∈ window → s + w + f ≤ e.time.val ∧ e.time.val < s + w + b ∧
                  AffineBatchDecoder.equation e.sample
                    (ReferenceFirstCollectionFormedUpOfferReceiver.encodedUpOfferWord U)) ∧
              (∀ (b : ℕ) (_hfb : f ≤ b) (hbn : b ≤ n.val + 1),
                let S := (B.drop f).take (b - f)
                let times := S.map (fun record => record.input.time)
                let tr := ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace S i
                let P := ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries S i
                (X b (by omega)).upDecoderBank =
                  ReferenceCoordinatorUpDecoderReplay.replay (X f (by omega)).upDecoderBank
                    (ReferenceCoordinatorUpDecoderReplay.retainedUpDiagnostics S) ∧
                AffineBatchDecoder.run p tr times ((X f (by omega)).upDecoderBank i) =
                  (X b (by omega)).upDecoderBank i ∧
                AffineBatchDecoder.collected ((X b (by omega)).upDecoderBank i) =
                  AffineBatchDecoder.collected ((X f (by omega)).upDecoderBank i) ++ P ∧
                AffineBatchDecoder.positives p tr times = P ∧
                times.Pairwise (fun a b => a.val < b.val) ∧
                ((X f (by omega)).upDecoderBank i).pending.length < AffineBatchDecoder.quota p ∧
                ∀ e, e ∈ ((X f (by omega)).upDecoderBank i).pending →
                  e ∈ ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries
                    (whole.take (w + f)) i ∧
                  e.time.val < s + w + f ∧
                  ∀ t, t ∈ times → e.time.val < t.val) ∧
              (∀ (q : Fin B.length) (_hqpos : 0 < q.val) (_hfq : f ≤ q.val) (_hqn : q.val ≤ n.val),
                let r := ReferenceFirstCollectionFormedReplyStateInterval.actualCollectionRecord B q
                PublicDiscreteDraws.slotDraw (r.input.row.2 r.input.time).1 = PublicDiscreteDraws.upSlot →
                PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
                  (r.input.row.2 r.input.time).1 = i →
                ∃ (choice : ReferencePrelaunchFollower.State p rate.eta)
                  (memory : ActiveFollowerLifecycle.LocalMemory p)
                  (incoming : ReferenceActivePhysicalStep.Ledger rate)
                  (tail : ReferenceCollectionPhaseHistory.Tail r.input)
                  (recording : CoordinatorRecordingOperation.Output p)
                  (L : ReferenceActivePhysicalStep.Ledger rate)
                  (diagnostic : ReferenceActivePhysicalStep.UpDiagnostic p rate),
                  (ReferenceFirstCollectionFormedReplyStateInterval.actualCollectionChoice B i q).configuration =
                    .ordinary choice memory ∧ ActiveFollowerLifecycle.localStateDomainValid choice ∧
                  choice.status = .unoccupied ∧
                  r.input.state.coordinator = .collection payload incoming saved ∧
                  r.input.rows = rows ∧ r.input.selected = J ∧ r.input.rewards = rewards ∧
                  ReferenceActivePhysicalStep.upExpected (ReferenceActivePhysicalStep.prepare r.input) =
                    some (ReferenceFirstCollectionFormedUpOfferReceiver.encodedUpOfferWord U) ∧
                  ReferenceCollectionPhaseHistory.executedTail r.input = some tail ∧
                  CoordinatorRecorderComplementBridge.run
                    (ReferenceActivePhysicalStep.collectionRecordingInput (ReferenceActivePhysicalStep.prepare r.input)
                      tail.payload tail.started tail.weights) = some recording ∧
                  CoordinatorCollectionLedger.startRound tail.ledger (r.input.time.val + 1)
                    (ReferenceActivePhysicalStep.collectionEnabled tail.ledger r.input.time)
                    (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) = .success L ∧
                  ReferenceCoordinatorUpPhysicalCall.siteLedger? (x := r.input) = some L ∧
                  CoordinatorUpReception.receptionInputCheck
                    (ReferenceCoordinatorUpPhysicalCall.actualUpInput r.input L) = true ∧
                  r.output.coordinator.up = some diagnostic ∧
                  diagnostic.input = ReferenceCoordinatorUpPhysicalCall.actualUpInput r.input L ∧
                  tail.reception = some (L,
                    ReferenceActivePhysicalStep.receiveUp (ReferenceActivePhysicalStep.prepare r.input) L) ∧
                  (ReferenceActivePhysicalStep.receiveUp
                    (ReferenceActivePhysicalStep.prepare r.input) L).result ≠ .invalid ∧
                  i ∈ L.pending ∧ CoordinatorCollectionLedger.acceptUpCheck L i U = true)))
    (hfinish : ∀ (i : Fin (p.m - 1)) (f n : ℕ) (hfn : f ≤ n) (hn : n < ell)
      (U : OrdinaryMessageCodec.UpRecord (ReferencePrelaunchFollower.codecParams p rate.eta)),
    (∀ (b : ℕ) (_hfb : f ≤ b) (_hbn : b ≤ n + 1),
      let S := (B.drop f).take (b - f)
      let times := S.map (fun r => r.input.time)
      let tr := ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace S i
      let P := AffineBatchDecoder.positives p tr times
      let ch := (X f (by omega)).upDecoderBank i
      let Q := AffineBatchDecoder.quota p
      let window := P.drop (Q - ch.pending.length)
      P.length = Q - ch.pending.length + Q →
      (∀ e, e ∈ ch.pending → e ∉ window) ∧ P.length ≤ 2 * Q ∧
      ∀ e, e ∈ window → s + w + f ≤ e.time.val ∧ e.time.val < s + w + b ∧
        AffineBatchDecoder.equation e.sample
          (ReferenceFirstCollectionFormedUpOfferReceiver.encodedUpOfferWord U)) →
    (∀ k : Fin ell,
      (B[k.val]'(Nat.lt_of_lt_of_le k.isLt hBlength)).input.state = X k.val (by omega) ∧
      (B[k.val]'(Nat.lt_of_lt_of_le k.isLt hBlength)).output.next =
        X (k.val + 1) (by omega)) →
    (∀ (b : ℕ) (_hfb : f ≤ b) (hbn : b ≤ n + 1),
      let S := (B.drop f).take (b - f)
      let times := S.map (fun record => record.input.time)
      let tr := ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace S i
      let P := ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries S i
      (X b (by omega)).upDecoderBank =
        ReferenceCoordinatorUpDecoderReplay.replay (X f (by omega)).upDecoderBank
          (ReferenceCoordinatorUpDecoderReplay.retainedUpDiagnostics S) ∧
      AffineBatchDecoder.run p tr times ((X f (by omega)).upDecoderBank i) =
        (X b (by omega)).upDecoderBank i ∧
      AffineBatchDecoder.collected ((X b (by omega)).upDecoderBank i) =
        AffineBatchDecoder.collected ((X f (by omega)).upDecoderBank i) ++ P ∧
      AffineBatchDecoder.positives p tr times = P ∧
      times.Pairwise (fun a b => a.val < b.val) ∧
      ((X f (by omega)).upDecoderBank i).pending.length < AffineBatchDecoder.quota p ∧
      ∀ e, e ∈ ((X f (by omega)).upDecoderBank i).pending →
        e ∈ ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries
          (whole.take (w + f)) i ∧
        e.time.val < s + w + f ∧
        ∀ t, t ∈ times → e.time.val < t.val) →
    (∀ (t : ℕ) (ht : t ≤ ell),
      ReferenceUpDecoderBankInvariant.upBankInvariant (X t (by omega)) ∧
      (X t (by omega)).coordinator ≠ .dagger) →
    (∀ (q : Fin B.length) (_hqpos : 0 < q.val) (_hfq : f ≤ q.val) (_hqn : q.val ≤ n),
      let r := ReferenceFirstCollectionFormedReplyStateInterval.actualCollectionRecord B q
      PublicDiscreteDraws.slotDraw (r.input.row.2 r.input.time).1 = PublicDiscreteDraws.upSlot →
      PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
        (r.input.row.2 r.input.time).1 = i →
      ∃ (choice : ReferencePrelaunchFollower.State p rate.eta)
        (memory : ActiveFollowerLifecycle.LocalMemory p)
        (incoming : ReferenceActivePhysicalStep.Ledger rate)
        (tail : ReferenceCollectionPhaseHistory.Tail r.input)
        (recording : CoordinatorRecordingOperation.Output p)
        (L : ReferenceActivePhysicalStep.Ledger rate)
        (diagnostic : ReferenceActivePhysicalStep.UpDiagnostic p rate),
        (ReferenceFirstCollectionFormedReplyStateInterval.actualCollectionChoice B i q).configuration =
          .ordinary choice memory ∧ ActiveFollowerLifecycle.localStateDomainValid choice ∧
        choice.status = .unoccupied ∧
        r.input.state.coordinator = .collection payload incoming saved ∧
        r.input.rows = rows ∧ r.input.selected = J ∧ r.input.rewards = rewards ∧
        ReferenceActivePhysicalStep.upExpected (ReferenceActivePhysicalStep.prepare r.input) =
          some (ReferenceFirstCollectionFormedUpOfferReceiver.encodedUpOfferWord U) ∧
        ReferenceCollectionPhaseHistory.executedTail r.input = some tail ∧
        CoordinatorRecorderComplementBridge.run
          (ReferenceActivePhysicalStep.collectionRecordingInput (ReferenceActivePhysicalStep.prepare r.input)
            tail.payload tail.started tail.weights) = some recording ∧
        CoordinatorCollectionLedger.startRound tail.ledger (r.input.time.val + 1)
          (ReferenceActivePhysicalStep.collectionEnabled tail.ledger r.input.time)
          (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) = .success L ∧
        ReferenceCoordinatorUpPhysicalCall.siteLedger? (x := r.input) = some L ∧
        CoordinatorUpReception.receptionInputCheck
          (ReferenceCoordinatorUpPhysicalCall.actualUpInput r.input L) = true ∧
        r.output.coordinator.up = some diagnostic ∧
        diagnostic.input = ReferenceCoordinatorUpPhysicalCall.actualUpInput r.input L ∧
        tail.reception = some (L,
          ReferenceActivePhysicalStep.receiveUp (ReferenceActivePhysicalStep.prepare r.input) L) ∧
        (ReferenceActivePhysicalStep.receiveUp
          (ReferenceActivePhysicalStep.prepare r.input) L).result ≠ .invalid ∧
        i ∈ L.pending ∧ CoordinatorCollectionLedger.acceptUpCheck L i U = true) →
    ∀ (b : ℕ) (hfb : f ≤ b) (hbn : b ≤ n + 1),
      let S := (B.drop f).take (b - f)
      let times := S.map (fun record => record.input.time)
      let tr := ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace S i
      let P := AffineBatchDecoder.positives p tr times
      let ch := (X f ((Nat.add_le_add_left
        (hfb.trans (hbn.trans (Nat.succ_le_of_lt hn))) w).trans hlen)).upDecoderBank i
      let Q := AffineBatchDecoder.quota p
      let first := ch.pending ++ P.take (Q - ch.pending.length)
      let window := P.drop (Q - ch.pending.length)
      let uword := ReferenceFirstCollectionFormedUpOfferReceiver.encodedUpOfferWord U
      P.length = Q - ch.pending.length + Q →
      ∃ (q : Fin B.length) (_hqn : q.val ≤ n)
        (last : AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p))
        (diagnostic : ReferenceActivePhysicalStep.UpDiagnostic p rate)
        (tail : ReferenceCollectionPhaseHistory.Tail B[q.val].input)
        (recording : CoordinatorRecordingOperation.Output p)
        (L : ReferenceActivePhysicalStep.Ledger rate),
        let r := B[q.val]
        0 < q.val ∧ f ≤ q.val ∧ q.val < b ∧ q.val ≤ n ∧
        whole[w + q.val]? = some r ∧
        r.input.time.val = s + w + q.val ∧
        r.input.rows = rows ∧ r.input.selected = J ∧
        r.input.rewards = rewards ∧
        first.length = Q ∧ window.length = Q ∧ ch.pending.length < Q ∧
        P.length ≤ 2 * Q ∧
        window.Pairwise (fun a b => a.time.val < b.time.val) ∧
        (∀ e, e ∈ ch.pending → e ∉ window) ∧
        last ∈ window ∧ AffineBatchDecoder.decisionTime window = some last.time ∧
        r.input.time = last.time ∧
        r.output.coordinator.up = some diagnostic ∧
        diagnostic.input.selectedFollower = i ∧
        ReferenceSelectedAffinePairLaw.selectedChannel p
          ((rows J).2 r.input.time).1 = some (1, i) ∧
        ReferenceActiveAffinePositiveTest.upPositive r.input = true ∧
        0 < CoordinatorUpReception.roundedObservationValue p
          diagnostic.input.ownObservation ∧
        ReferenceCollectionPhaseHistory.executedTail r.input = some tail ∧
        CoordinatorRecorderComplementBridge.run
          (ReferenceActivePhysicalStep.collectionRecordingInput
            (ReferenceActivePhysicalStep.prepare r.input)
            tail.payload tail.started tail.weights) = some recording ∧
        CoordinatorCollectionLedger.startRound tail.ledger (r.input.time.val + 1)
          (ReferenceActivePhysicalStep.collectionEnabled tail.ledger r.input.time)
          (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) =
            .success L ∧
        ReferenceCoordinatorUpPhysicalCall.siteLedger? (x := r.input) = some L ∧
        diagnostic.input = ReferenceCoordinatorUpPhysicalCall.actualUpInput r.input L ∧
        CoordinatorUpReception.receptionInputCheck diagnostic.input = true ∧
        tail.reception = some (L,
          ReferenceActivePhysicalStep.receiveUp (ReferenceActivePhysicalStep.prepare r.input) L) ∧
        (ReferenceActivePhysicalStep.receiveUp
          (ReferenceActivePhysicalStep.prepare r.input) L).result ≠ .invalid ∧
        i ∈ L.pending ∧ CoordinatorCollectionLedger.acceptUpCheck L i U = true ∧
        ReferenceActivePhysicalStep.upExpected
          (ReferenceActivePhysicalStep.prepare r.input) = some uword ∧
        diagnostic.expected = some uword ∧
        diagnostic.input.time = r.input.time ∧
        diagnostic.input.affineSample = ((rows J).2 r.input.time).2 (1, i) ∧
        diagnostic.input.ownObservation =
          (ReferenceActivePhysicalStep.prepare r.input).feedback.feedback
            (ActiveRoundActions.coordinator p.two_le_m) ∧
        diagnostic.input.upDecoderBank = r.input.state.upDecoderBank ∧
        (diagnostic.input.upDecoderBank i).pending ++ [last] = window ∧
        CoordinatorUpReception.decoderTransition diagnostic.input =
          ({ pending := [], completed := ch.completed ++ [first, window] },
            AffineBatchDecoder.batchOutput window) ∧
        diagnostic.decoderAfter =
          { pending := [], completed := ch.completed ++ [first, window] } ∧
        diagnostic.raw = AffineBatchDecoder.batchOutput window ∧
        (X (q.val + 1) ((Nat.add_le_add_left
          ((Nat.succ_le_succ _hqn).trans (Nat.succ_le_of_lt hn)) w).trans hlen)).upDecoderBank i = diagnostic.decoderAfter ∧
        (X b ((Nat.add_le_add_left
          (hbn.trans (Nat.succ_le_of_lt hn)) w).trans hlen)).upDecoderBank i = diagnostic.decoderAfter ∧
        window ∈ diagnostic.decoderAfter.completed ∧
        (∀ e, e ∈ window → s + w + f ≤ e.time.val ∧
          e.time.val < s + w + b ∧ AffineBatchDecoder.equation e.sample uword) ∧
        AffineBatchDecoder.positives p
          (ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace
            ((B.drop f).take (q.val + 1 - f)) i)
          (((B.drop f).take (q.val + 1 - f)).map (fun r => r.input.time)) = P ∧
        r.output.next.coordinator ≠ .dagger ∧
        r.output.next.followers i ≠ .dagger ∧
        ((diagnostic.raw = some uword ∧
          ReferenceCollectionPhaseHistory.filteredParsed r.input L = some U ∧
          ∃ (decoded : ReferenceActivePhysicalStep.Ledger rate)
            (bank : CoordinatorUpReception.UpDecoderBank p),
            (ReferenceActivePhysicalStep.receiveUp
              (ReferenceActivePhysicalStep.prepare r.input) L).result =
                .success (decoded, bank) ∧
            ReferenceCollectionPhaseHistory.AcceptedUp r.input i U) ∨
          (diagnostic.raw = none ∧
            ∃ left right : AffineChannelLaw.Word (AffineBatchDecoder.width p),
              left ≠ right ∧
              AffineBatchDecoder.satisfies (AffineBatchDecoder.samples window) left ∧
              AffineBatchDecoder.satisfies (AffineBatchDecoder.samples window) right))) :
    ∀ (n : Fin ell) (hn : 0 < n.val) (i : Fin (p.m - 1)),
      i ∈ (ledgers ⟨n.val - 1, Nat.lt_of_le_of_lt (Nat.sub_le n.val 1) n.isLt⟩).pending →
      ∃ (state : ReferencePrelaunchFollower.State p rate.eta)
        (memory : ActiveFollowerLifecycle.LocalMemory p),
        (B[n.val]'(Nat.lt_of_lt_of_le n.isLt hBlength)).input.state.followers i = .ordinary state memory ∧
        state.status = .unoccupied ∧ ActiveFollowerLifecycle.localStateDomainValid state ∧
        (state.lastDown = some (payload.downRecord i) →
          ∃ (U : OrdinaryMessageCodec.UpRecord
              (ReferencePrelaunchFollower.codecParams p rate.eta))
            (j : Fin whole.length),
            U.val = ActiveFollowerQueueOperation.upOfferFields state ∧
            U.val.sigma = s + 1 ∧ 1 ≤ U.val.sigma ∧ j.val < w + n.val ∧
            ReferenceAcceptedUpFollowerHistory.RetainedDown whole[j.val] i
              (payload.downRecord i) ∧
            (∀ j' : Fin whole.length, j'.val < w + n.val →
              ReferenceAcceptedUpFollowerHistory.RetainedDown whole[j'.val] i
                (payload.downRecord i) → j' = j) ∧
            let f := if j.val < w then 0 else j.val - w + 1
            ∃ hf : f < B.length,
              f ≤ n.val ∧
              B[f].input.time.val + 1 = max (s + w + 1) (s + j.val + 2) ∧
              (j.val < w → f = 0) ∧ (j.val = w → f = 1) ∧
              ∀ (b : ℕ) (hfb : f ≤ b) (hbn : b ≤ n.val + 1),
                let S := (B.drop f).take (b - f)
                let times := S.map (fun record => record.input.time)
                let tr := ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace S i
                let P := AffineBatchDecoder.positives p tr times
                let ch := (X f ((Nat.add_le_add_left
                  (hfb.trans (hbn.trans (Nat.succ_le_of_lt n.isLt))) w).trans hlen)).upDecoderBank i
                let Q := AffineBatchDecoder.quota p
                let first := ch.pending ++ P.take (Q - ch.pending.length)
                let window := P.drop (Q - ch.pending.length)
                let uword := ReferenceFirstCollectionFormedUpOfferReceiver.encodedUpOfferWord U
                P.length = Q - ch.pending.length + Q →
                ∃ (q : Fin B.length) (_hqn : q.val ≤ n.val)
                  (last : AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p))
                  (diagnostic : ReferenceActivePhysicalStep.UpDiagnostic p rate)
                  (tail : ReferenceCollectionPhaseHistory.Tail B[q.val].input)
                  (recording : CoordinatorRecordingOperation.Output p)
                  (L : ReferenceActivePhysicalStep.Ledger rate),
                  let r := B[q.val]
                  0 < q.val ∧ f ≤ q.val ∧ q.val < b ∧ q.val ≤ n.val ∧
                  whole[w + q.val]? = some r ∧
                  r.input.time.val = s + w + q.val ∧
                  r.input.rows = rows ∧ r.input.selected = J ∧
                  r.input.rewards = rewards ∧
                  first.length = Q ∧ window.length = Q ∧ ch.pending.length < Q ∧
                  P.length ≤ 2 * Q ∧
                  window.Pairwise (fun a b => a.time.val < b.time.val) ∧
                  (∀ e, e ∈ ch.pending → e ∉ window) ∧
                  last ∈ window ∧ AffineBatchDecoder.decisionTime window = some last.time ∧
                  r.input.time = last.time ∧
                  r.output.coordinator.up = some diagnostic ∧
                  diagnostic.input.selectedFollower = i ∧
                  ReferenceSelectedAffinePairLaw.selectedChannel p
                    ((rows J).2 r.input.time).1 = some (1, i) ∧
                  ReferenceActiveAffinePositiveTest.upPositive r.input = true ∧
                  0 < CoordinatorUpReception.roundedObservationValue p
                    diagnostic.input.ownObservation ∧
                  ReferenceCollectionPhaseHistory.executedTail r.input = some tail ∧
                  CoordinatorRecorderComplementBridge.run
                    (ReferenceActivePhysicalStep.collectionRecordingInput
                      (ReferenceActivePhysicalStep.prepare r.input)
                      tail.payload tail.started tail.weights) = some recording ∧
                  CoordinatorCollectionLedger.startRound tail.ledger (r.input.time.val + 1)
                    (ReferenceActivePhysicalStep.collectionEnabled tail.ledger r.input.time)
                    (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) =
                      .success L ∧
                  ReferenceCoordinatorUpPhysicalCall.siteLedger? (x := r.input) = some L ∧
                  diagnostic.input = ReferenceCoordinatorUpPhysicalCall.actualUpInput r.input L ∧
                  CoordinatorUpReception.receptionInputCheck diagnostic.input = true ∧
                  tail.reception = some (L,
                    ReferenceActivePhysicalStep.receiveUp (ReferenceActivePhysicalStep.prepare r.input) L) ∧
                  (ReferenceActivePhysicalStep.receiveUp
                    (ReferenceActivePhysicalStep.prepare r.input) L).result ≠ .invalid ∧
                  i ∈ L.pending ∧ CoordinatorCollectionLedger.acceptUpCheck L i U = true ∧
                  ReferenceActivePhysicalStep.upExpected
                    (ReferenceActivePhysicalStep.prepare r.input) = some uword ∧
                  diagnostic.expected = some uword ∧
                  diagnostic.input.time = r.input.time ∧
                  diagnostic.input.affineSample = ((rows J).2 r.input.time).2 (1, i) ∧
                  diagnostic.input.ownObservation =
                    (ReferenceActivePhysicalStep.prepare r.input).feedback.feedback
                      (ActiveRoundActions.coordinator p.two_le_m) ∧
                  diagnostic.input.upDecoderBank = r.input.state.upDecoderBank ∧
                  (diagnostic.input.upDecoderBank i).pending ++ [last] = window ∧
                  CoordinatorUpReception.decoderTransition diagnostic.input =
                    ({ pending := [], completed := ch.completed ++ [first, window] },
                      AffineBatchDecoder.batchOutput window) ∧
                  diagnostic.decoderAfter =
                    { pending := [], completed := ch.completed ++ [first, window] } ∧
                  diagnostic.raw = AffineBatchDecoder.batchOutput window ∧
                  (X (q.val + 1) ((Nat.add_le_add_left
                    ((Nat.succ_le_succ _hqn).trans (Nat.succ_le_of_lt n.isLt)) w).trans hlen)).upDecoderBank i = diagnostic.decoderAfter ∧
                  (X b ((Nat.add_le_add_left
                    (hbn.trans (Nat.succ_le_of_lt n.isLt)) w).trans hlen)).upDecoderBank i = diagnostic.decoderAfter ∧
                  window ∈ diagnostic.decoderAfter.completed ∧
                  (∀ e, e ∈ window → s + w + f ≤ e.time.val ∧
                    e.time.val < s + w + b ∧ AffineBatchDecoder.equation e.sample uword) ∧
                  AffineBatchDecoder.positives p
                    (ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace
                      ((B.drop f).take (q.val + 1 - f)) i)
                    (((B.drop f).take (q.val + 1 - f)).map (fun r => r.input.time)) = P ∧
                  r.output.next.coordinator ≠ .dagger ∧
                  r.output.next.followers i ≠ .dagger ∧
                  ((diagnostic.raw = some uword ∧
                    ReferenceCollectionPhaseHistory.filteredParsed r.input L = some U ∧
                    ∃ (decoded : ReferenceActivePhysicalStep.Ledger rate)
                      (bank : CoordinatorUpReception.UpDecoderBank p),
                      (ReferenceActivePhysicalStep.receiveUp
                        (ReferenceActivePhysicalStep.prepare r.input) L).result =
                          .success (decoded, bank) ∧
                      ReferenceCollectionPhaseHistory.AcceptedUp r.input i U) ∨
                    (diagnostic.raw = none ∧
                      ∃ left right : AffineChannelLaw.Word (AffineBatchDecoder.width p),
                        left ≠ right ∧
                        AffineBatchDecoder.satisfies (AffineBatchDecoder.samples window) left ∧
                        AffineBatchDecoder.satisfies (AffineBatchDecoder.samples window) right))) := by
  intro n hn i hi
  obtain ⟨state, memory, hstate, hstatus, hvalid, hformed⟩ := hqueries n hn i hi
  refine ⟨state, memory, hstate, hstatus, hvalid, ?_⟩
  intro hlastDown
  obtain ⟨U, j, hfields, hsigma, hpositive, hjbefore, hretained, hunique,
    hf, hfn, hftime, hfzero, hfone, hpure, hsaved, hreceiver⟩ := hformed hlastDown
  let f := if j.val < w then 0 else j.val - w + 1
  refine ⟨U, j, hfields, hsigma, hpositive, hjbefore, hretained, hunique,
    hf, hfn, hftime, hfzero, hfone, ?_⟩
  have hcut := hfinish i f n.val hfn n.isLt U hpure hEndpoints hsaved hstates hreceiver
  intro b hfb hbn S times tr P ch Q first window uword hcount
  exact hcut b hfb hbn hcount

/-- Refine one actual initialized collection dispatch at every formed-reply
query and every exact local two-batch count. The local formation and count
conditions remain visible; no service attainment or stopped quota is claimed.
The same completed window either causes actual acceptance or has two solvers. -/
public theorem actual_initialized_first_collection_formed_up_detecting_cut
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (count : ℕ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hspan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed + count ≤ p.T)
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
        rate source rewards C_star C_h hcross count hspan).records).length < count) :
    ∃ d : ReferenceFirstCollectionStreamEmptyDispatch.ActualInitializedStreamDispatch
        source rewards C_star C_h count hcross hspan hshort,
      let out := d.stream
      let E := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
        rate source rewards C_star C_h hcross count hspan
      let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records).length
      let s := ReferenceInitializationRun.elapsed p
        (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
      let B := ReferenceCollectionPhaseHistory.collectionWindow E.records w
      ∃ hlen : w + out.ell ≤ count,
        ∃ hBlength : out.ell ≤ B.length,
        let initial := ReferenceFirstCollectionEpochAlignment.actualLaunchState
          rate source rewards C_star C_h hcross
        let active := (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
          rate source rewards C_star C_h hcross).1
        let J := ActualInitializationPhysicalStep.selectedRowIndex p source
        let X (t : ℕ) (hwt : w + t ≤ count) :=
          (ReferenceActivePhysicalHorizon.run initial source.1.2 J rewards s (w + t)
            (Nat.le_trans (Nat.add_le_add_left hwt s) hspan) active).finalState
        out.window = B ∧
        ∀ (n : Fin out.ell) (hn : 0 < n.val) (i : Fin (p.m - 1)),
          i ∈ (out.ledgers ⟨n.val - 1, Nat.lt_of_le_of_lt (Nat.sub_le n.val 1) n.isLt⟩).pending →
          ∃ (state : ReferencePrelaunchFollower.State p rate.eta)
            (memory : ActiveFollowerLifecycle.LocalMemory p),
            (B[n.val]'(Nat.lt_of_lt_of_le n.isLt hBlength)).input.state.followers i = .ordinary state memory ∧
            state.status = .unoccupied ∧ ActiveFollowerLifecycle.localStateDomainValid state ∧
            (state.lastDown = some (out.payload.downRecord i) →
              ∃ (U : OrdinaryMessageCodec.UpRecord
                  (ReferencePrelaunchFollower.codecParams p rate.eta))
                (j : Fin E.records.length),
                U.val = ActiveFollowerQueueOperation.upOfferFields state ∧
                U.val.sigma = s + 1 ∧ 1 ≤ U.val.sigma ∧ j.val < w + n.val ∧
                ReferenceAcceptedUpFollowerHistory.RetainedDown E.records[j.val] i
                  (out.payload.downRecord i) ∧
                (∀ j' : Fin E.records.length, j'.val < w + n.val →
                  ReferenceAcceptedUpFollowerHistory.RetainedDown E.records[j'.val] i
                    (out.payload.downRecord i) → j' = j) ∧
                let f := if j.val < w then 0 else j.val - w + 1
                ∃ hf : f < B.length,
                  f ≤ n.val ∧
                  B[f].input.time.val + 1 = max (s + w + 1) (s + j.val + 2) ∧
                  (j.val < w → f = 0) ∧ (j.val = w → f = 1) ∧
                  ∀ (b : ℕ) (hfb : f ≤ b) (hbn : b ≤ n.val + 1),
                    let S := (B.drop f).take (b - f)
                    let times := S.map (fun record => record.input.time)
                    let tr := ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace S i
                    let P := AffineBatchDecoder.positives p tr times
                    let ch := (X f ((Nat.add_le_add_left
                      (hfb.trans (hbn.trans (Nat.succ_le_of_lt n.isLt))) w).trans hlen)).upDecoderBank i
                    let Q := AffineBatchDecoder.quota p
                    let first := ch.pending ++ P.take (Q - ch.pending.length)
                    let window := P.drop (Q - ch.pending.length)
                    let uword := ReferenceFirstCollectionFormedUpOfferReceiver.encodedUpOfferWord U
                    P.length = Q - ch.pending.length + Q →
                    ∃ (q : Fin B.length) (_hqn : q.val ≤ n.val)
                      (last : AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p))
                      (diagnostic : ReferenceActivePhysicalStep.UpDiagnostic p rate)
                      (tail : ReferenceCollectionPhaseHistory.Tail B[q.val].input)
                      (recording : CoordinatorRecordingOperation.Output p)
                      (L : ReferenceActivePhysicalStep.Ledger rate),
                      let r := B[q.val]
                      0 < q.val ∧ f ≤ q.val ∧ q.val < b ∧ q.val ≤ n.val ∧
                      E.records[w + q.val]? = some r ∧
                      r.input.time.val = s + w + q.val ∧
                      r.input.rows = source.1.2 ∧ r.input.selected = J ∧
                      r.input.rewards = rewards ∧
                      first.length = Q ∧ window.length = Q ∧ ch.pending.length < Q ∧
                      P.length ≤ 2 * Q ∧
                      window.Pairwise (fun a b => a.time.val < b.time.val) ∧
                      (∀ e, e ∈ ch.pending → e ∉ window) ∧
                      last ∈ window ∧ AffineBatchDecoder.decisionTime window = some last.time ∧
                      r.input.time = last.time ∧
                      r.output.coordinator.up = some diagnostic ∧
                      diagnostic.input.selectedFollower = i ∧
                      ReferenceSelectedAffinePairLaw.selectedChannel p
                        ((source.1.2 J).2 r.input.time).1 = some (1, i) ∧
                      ReferenceActiveAffinePositiveTest.upPositive r.input = true ∧
                      0 < CoordinatorUpReception.roundedObservationValue p
                        diagnostic.input.ownObservation ∧
                      ReferenceCollectionPhaseHistory.executedTail r.input = some tail ∧
                      CoordinatorRecorderComplementBridge.run
                        (ReferenceActivePhysicalStep.collectionRecordingInput
                          (ReferenceActivePhysicalStep.prepare r.input)
                          tail.payload tail.started tail.weights) = some recording ∧
                      CoordinatorCollectionLedger.startRound tail.ledger (r.input.time.val + 1)
                        (ReferenceActivePhysicalStep.collectionEnabled tail.ledger r.input.time)
                        (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) =
                          .success L ∧
                      ReferenceCoordinatorUpPhysicalCall.siteLedger? (x := r.input) = some L ∧
                      diagnostic.input = ReferenceCoordinatorUpPhysicalCall.actualUpInput r.input L ∧
                      CoordinatorUpReception.receptionInputCheck diagnostic.input = true ∧
                      tail.reception = some (L,
                        ReferenceActivePhysicalStep.receiveUp (ReferenceActivePhysicalStep.prepare r.input) L) ∧
                      (ReferenceActivePhysicalStep.receiveUp
                        (ReferenceActivePhysicalStep.prepare r.input) L).result ≠ .invalid ∧
                      i ∈ L.pending ∧ CoordinatorCollectionLedger.acceptUpCheck L i U = true ∧
                      ReferenceActivePhysicalStep.upExpected
                        (ReferenceActivePhysicalStep.prepare r.input) = some uword ∧
                      diagnostic.expected = some uword ∧
                      diagnostic.input.time = r.input.time ∧
                      diagnostic.input.affineSample = ((source.1.2 J).2 r.input.time).2 (1, i) ∧
                      diagnostic.input.ownObservation =
                        (ReferenceActivePhysicalStep.prepare r.input).feedback.feedback
                          (ActiveRoundActions.coordinator p.two_le_m) ∧
                      diagnostic.input.upDecoderBank = r.input.state.upDecoderBank ∧
                      (diagnostic.input.upDecoderBank i).pending ++ [last] = window ∧
                      CoordinatorUpReception.decoderTransition diagnostic.input =
                        ({ pending := [], completed := ch.completed ++ [first, window] },
                          AffineBatchDecoder.batchOutput window) ∧
                      diagnostic.decoderAfter =
                        { pending := [], completed := ch.completed ++ [first, window] } ∧
                      diagnostic.raw = AffineBatchDecoder.batchOutput window ∧
                      (X (q.val + 1) ((Nat.add_le_add_left
                        ((Nat.succ_le_succ _hqn).trans (Nat.succ_le_of_lt n.isLt)) w).trans hlen)).upDecoderBank i = diagnostic.decoderAfter ∧
                      (X b ((Nat.add_le_add_left
                        (hbn.trans (Nat.succ_le_of_lt n.isLt)) w).trans hlen)).upDecoderBank i = diagnostic.decoderAfter ∧
                      window ∈ diagnostic.decoderAfter.completed ∧
                      (∀ e, e ∈ window → s + w + f ≤ e.time.val ∧
                        e.time.val < s + w + b ∧ AffineBatchDecoder.equation e.sample uword) ∧
                      AffineBatchDecoder.positives p
                        (ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace
                          ((B.drop f).take (q.val + 1 - f)) i)
                        (((B.drop f).take (q.val + 1 - f)).map (fun r => r.input.time)) = P ∧
                      r.output.next.coordinator ≠ .dagger ∧
                      r.output.next.followers i ≠ .dagger ∧
                      ((diagnostic.raw = some uword ∧
                        ReferenceCollectionPhaseHistory.filteredParsed r.input L = some U ∧
                        ∃ (decoded : ReferenceActivePhysicalStep.Ledger rate)
                          (bank : CoordinatorUpReception.UpDecoderBank p),
                          (ReferenceActivePhysicalStep.receiveUp
                            (ReferenceActivePhysicalStep.prepare r.input) L).result =
                              .success (decoded, bank) ∧
                          ReferenceCollectionPhaseHistory.AcceptedUp r.input i U) ∨
                        (diagnostic.raw = none ∧
                          ∃ left right : AffineChannelLaw.Word (AffineBatchDecoder.width p),
                            left ≠ right ∧
                            AffineBatchDecoder.satisfies (AffineBatchDecoder.samples window) left ∧
                            AffineBatchDecoder.satisfies (AffineBatchDecoder.samples window) right))) := by
  obtain ⟨d, hsource⟩ := actual_initialized_formed_up_local_premises
    rate source rewards C_star C_h count hcross hspan hshort
  refine ⟨d, ?_⟩
  intro out E w s B
  obtain ⟨hlen, hBlength, hlocal⟩ := hsource
  refine ⟨hlen, hBlength, ?_⟩
  intro initial active J X
  obtain ⟨Y, hY, hWindow, hEndpoints, hstates, hqueries⟩ := hlocal
  have hYX : Y = X := hY
  refine ⟨hWindow, ?_⟩
  have hassembled := assemble_formed_queries rate source.1.2 J rewards s w count out.ell
    B E.records out.payload out.saved out.ledgers hlen hBlength Y
    hEndpoints hstates hqueries
    (by
      intro i f n hfn hn U hpure hEndpoints' hsaved hstates' hreceiver
        b hfb hbn S times tr P ch Q first window uword hcount
      exact actual_formed_query_deciding_receiver_at_source
        rate source rewards C_star C_h count hcross hspan hshort d B E.records J rfl rfl rfl hlen hBlength
        Y hYX i f n hfn hn U hpure hEndpoints' hsaved hstates' hreceiver
        b hfb hbn hcount)
  rw [hYX] at hassembled
  exact hassembled

end Bandits.Support.ReferenceFirstCollectionFormedUpSourceDetectingCut

end
