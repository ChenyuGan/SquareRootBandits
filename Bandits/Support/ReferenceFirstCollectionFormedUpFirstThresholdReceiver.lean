/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bandits Lean regret formalization contributors.
-/
module

public import Bandits.Support.ReferenceFirstCollectionUpPrefixThreshold

/-!
# First exact UP threshold with its actual receiver

Compose the actual formed-reply receiver cut with the first exact retained
UP-positive prefix. At each prefix this gives either a subthreshold count or
the receiver at the exact first hit.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support

namespace Bandits.Support.ReferenceFirstCollectionFormedUpFirstThresholdReceiver

variable {p : ConstructorDimensions.Parameters}

private theorem actual_collection_window_chronological
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (count : ℕ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hspan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed + count ≤ p.T) :
    let E := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
      rate source rewards C_star C_h hcross count hspan
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records).length
    let B := ReferenceCollectionPhaseHistory.collectionWindow E.records w
    B.Pairwise (fun earlier later => earlier.input.time.val < later.input.time.val) := by
  classical
  let initial := ReferenceFirstCollectionEpochAlignment.actualLaunchState
    rate source rewards C_star C_h hcross
  let active := (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
    rate source rewards C_star C_h hcross).1
  let s := ReferenceInitializationRun.elapsed p
    (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
  let E := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
    rate source rewards C_star C_h hcross count hspan
  let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records).length
  let B := ReferenceCollectionPhaseHistory.collectionWindow E.records w
  have htimes : E.records.map (fun record => record.input.time.val) =
      ReferenceActivePhysicalHorizon.calendar s count := by
    simpa [E, ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun,
      initial, active, s] using
      ReferenceActivePhysicalHorizon.run_time_values initial source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s count hspan active
  have hcalendar : (ReferenceActivePhysicalHorizon.calendar s count).Pairwise
      (fun earlier later => earlier < later) := by
    simpa [ReferenceActivePhysicalHorizon.calendar] using
      (List.pairwise_lt_range' (s := s) (n := count) (step := 1)
        (by decide : 0 < 1))
  have htimePair : (E.records.map (fun record => record.input.time.val)).Pairwise
      (fun earlier later => earlier < later) := by
    rw [htimes]
    exact hcalendar
  have hrecords : E.records.Pairwise
      (fun earlier later => earlier.input.time.val < later.input.time.val) := by
    simpa only [Function.comp_def] using List.pairwise_map.mp htimePair
  have htail : List.Sublist ((E.records.drop (w + 1)).takeWhile
      (fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input))
        (E.records.drop (w + 1)) :=
    List.takeWhile_sublist _
  have hsplit : (E.records.drop w).take 1 ++ E.records.drop (w + 1) =
      E.records.drop w := by
    have hdrop : E.records.drop (w + 1) = (E.records.drop w).drop 1 := by
      simp [List.drop_drop]
    rw [hdrop]
    exact List.take_append_drop 1 (E.records.drop w)
  have hwindowSublist : List.Sublist B E.records := by
    change List.Sublist ((E.records.drop w).take 1 ++
      (E.records.drop (w + 1)).takeWhile
        (fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input))
      E.records
    have hparts : List.Sublist
        ((E.records.drop w).take 1 ++
          (E.records.drop (w + 1)).takeWhile
            (fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input))
        ((E.records.drop w).take 1 ++ E.records.drop (w + 1)) :=
      List.Sublist.append (List.Sublist.refl _) htail
    rw [hsplit] at hparts
    exact hparts.trans (List.drop_sublist w E.records)
  exact hrecords.sublist hwindowSublist

private theorem actual_initialized_up_pending_short
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (count : ℕ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hspan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed + count ≤ p.T)
    (t : ℕ) (ht : t ≤ count) (i : Fin (p.m - 1)) :
    let initial := ReferenceFirstCollectionEpochAlignment.actualLaunchState
      rate source rewards C_star C_h hcross
    let active := (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
      rate source rewards C_star C_h hcross).1
    let s := ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
    let J := ActualInitializationPhysicalStep.selectedRowIndex p source
    ((ReferenceActivePhysicalHorizon.run initial source.1.2 J rewards s t
      ((Nat.add_le_add_left ht s).trans hspan) active).finalState.upDecoderBank i).pending.length <
        AffineBatchDecoder.quota p := by
  intro initial active s J
  have hIbank : ReferenceUpDecoderBankInvariant.upBankInvariant initial := by
    obtain ⟨launch, hlaunch, hcoord, hbank, _, _, _⟩ :=
      ReferenceCorrectedInitializationLaunch.correctedLaunch_coordinator_provenance
        rate source rewards C_star C_h hcross
    have hlaunchEq : launch = initial := by
      exact (Option.get_of_eq_some
        ((ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
          rate source rewards C_star C_h).2 hcross) hlaunch).symm
    rw [← hlaunchEq]
    simp only [ReferenceUpDecoderBankInvariant.upBankInvariant,
      ReferenceUpDecoderBankInvariant.coordinatorBankInvariant, hcoord, hbank]
    exact ⟨CoordinatorUpReception.initialUpDecoderBank_wellFormed p, fun _ => rfl⟩
  exact ((ReferenceUpDecoderBankInvariant.run_upBankInvariant
    initial source.1.2 J rewards s t ((Nat.add_le_add_left ht s).trans hspan)
    active hIbank).1 i).1

private theorem two_batch_threshold_bounds {Q k : ℕ} (hk : k < Q) :
    Q < Q - k + Q ∧ Q - k + Q ≤ 2 * Q := by
  omega

/-- A receiver's crop identity places its deciding record at the least
retained-positive prefix that reaches the exact threshold. -/
private theorem receiver_at_first_exact_prefix
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (B : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (i : Fin (p.m - 1))
    (hchronological : B.Pairwise
      (fun earlier later => earlier.input.time.val < later.input.time.val))
    (f b H : ℕ) (q : Fin B.length) (hfq : f ≤ q.val) (hqb : q.val < b)
    (hexact : (ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries
      ((B.drop f).take (b - f)) i).length = H)
    (hminimal : ∀ c : ℕ, f ≤ c → c < b →
      (ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries
        ((B.drop f).take (c - f)) i).length < H)
    (hcrop : AffineBatchDecoder.positives p
        (ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace
          ((B.drop f).take (q.val + 1 - f)) i)
        (((B.drop f).take (q.val + 1 - f)).map (fun record => record.input.time)) =
      AffineBatchDecoder.positives p
        (ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace
          ((B.drop f).take (b - f)) i)
        (((B.drop f).take (b - f)).map (fun record => record.input.time))) :
    q.val + 1 = b := by
  have hbChrono := hchronological.sublist
    ((List.take_sublist (b - f) (B.drop f)).trans (List.drop_sublist f B))
  have hqChrono := hchronological.sublist
    ((List.take_sublist (q.val + 1 - f) (B.drop f)).trans (List.drop_sublist f B))
  have htraceB := ReferenceCoordinatorUpIntervalWindow.actual_trace_positives_eq_retained
    ((B.drop f).take (b - f)) i hbChrono
  have htraceQ := ReferenceCoordinatorUpIntervalWindow.actual_trace_positives_eq_retained
    ((B.drop f).take (q.val + 1 - f)) i hqChrono
  have hentries : ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries
      ((B.drop f).take (q.val + 1 - f)) i =
    ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries
      ((B.drop f).take (b - f)) i := htraceQ.symm.trans (hcrop.trans htraceB)
  have hqCount : (ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries
      ((B.drop f).take (q.val + 1 - f)) i).length = H :=
    (congrArg List.length hentries).trans hexact
  by_contra hnot
  have hlt : q.val + 1 < b := by omega
  have hearlier := hminimal (q.val + 1) (hfq.trans (Nat.le_succ _)) hlt
  rw [hqCount] at hearlier
  exact (Nat.lt_irrefl H) hearlier

/-- For the same actual initialized dispatch and formed-UP receiver, every
finite prefix either remains below the decoder's two-batch threshold or has
the exact first threshold record and that very record's actual receiver data.
The only inputs are the original source parameters and the three conditions
used by the existing initialized dispatch. -/
public theorem actual_initialized_first_collection_formed_up_count_or_receiver
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
            (B[n.val]'(Nat.lt_of_lt_of_le n.isLt hBlength)).input.state.followers i =
              .ordinary state memory ∧
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
                  ∃ hfn : f ≤ n.val,
                    B[f].input.time.val + 1 = max (s + w + 1) (s + j.val + 2) ∧
                    (j.val < w → f = 0) ∧ (j.val = w → f = 1) ∧
                    ∀ (a : ℕ) (hfa : f ≤ a) (haa : a ≤ n.val + 1),
                    let upPrefix := fun c : ℕ =>
                      ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries
                        ((B.drop f).take (c - f)) i
                    let Pa := upPrefix a
                    let ch := (X f
                      (Nat.le_trans
                        (Nat.add_le_add_left
                          (Nat.le_trans hfn (Nat.le_of_lt n.isLt)) w)
                        hlen)).upDecoderBank i
                    let Q := AffineBatchDecoder.quota p
                    let H := Q - ch.pending.length + Q
                    ch.pending.length < Q ∧
                    Q < H ∧
                    H ≤ 2 * Q ∧
                    (Pa.length < H ∨
                      ∃ (b : ℕ) (hfb : f ≤ b) (hbn : b ≤ n.val + 1),
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
                        ∃ (q : Fin B.length) (_hqn : q.val ≤ n.val)
                          (last : AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p))
                          (diagnostic : ReferenceActivePhysicalStep.UpDiagnostic p rate)
                          (tail : ReferenceCollectionPhaseHistory.Tail B[q.val].input)
                          (recording : CoordinatorRecordingOperation.Output p)
                          (L : ReferenceActivePhysicalStep.Ledger rate),
                        f < b ∧ b ≤ a ∧ q.val + 1 = b ∧
                        0 < q.val ∧ f ≤ q.val ∧ q.val ≤ n.val ∧
                        (upPrefix b).length = H ∧
                        (upPrefix q.val).length + 1 = H ∧
                        (∀ c : ℕ, f ≤ c → c < b → (upPrefix c).length < H) ∧
                        (∃ q0 : Fin B.length,
                          q = q0 ∧
                          ∃ e : AffineBatchDecoder.Entry p.T
                              (AffineBatchDecoder.width p),
                            ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries
                              B[q0.val] i = [e] ∧
                            upPrefix b = upPrefix q0.val ++ [e]) ∧
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
                              AffineBatchDecoder.satisfies (AffineBatchDecoder.samples window) right)))) := by
  classical
  obtain ⟨d, hsource⟩ :=
    ReferenceFirstCollectionFormedUpSourceDetectingCut.actual_initialized_first_collection_formed_up_detecting_cut
      rate source rewards C_star C_h count hcross hspan hshort
  refine ⟨d, ?_⟩
  intro out E w s B
  extract_lets -descend +merge +useContext at hsource
  obtain ⟨hlen, hBlength, hlocal⟩ := hsource
  refine ⟨hlen, hBlength, ?_⟩
  intro initial active J X
  extract_lets -descend +merge +useContext at hlocal
  obtain ⟨hwindow, hqueries⟩ := hlocal
  have hBchrono : B.Pairwise
      (fun earlier later => earlier.input.time.val < later.input.time.val) := by
    simpa only [E, w, B] using
      actual_collection_window_chronological
        rate source rewards C_star C_h count hcross hspan
  refine ⟨hwindow, ?_⟩
  intro n hn i hi
  obtain ⟨state, memory, hstate, hstatus, hvalid, hformed⟩ :=
    hqueries n hn i hi
  refine ⟨state, memory, hstate, hstatus, hvalid, ?_⟩
  intro hlastDown
  obtain ⟨U, j, hfields, hsigma, hpositive, hjbefore, hretained, hunique,
    hformation⟩ := hformed hlastDown
  refine ⟨U, j, hfields, hsigma, hpositive, hjbefore, hretained, hunique, ?_⟩
  intro f
  extract_lets -descend +merge +useContext at hformation
  obtain ⟨hf, hfn, hftime, hfzero, hfone, hreceiver⟩ := hformation
  refine ⟨hf, hfn, hftime, hfzero, hfone, ?_⟩
  intro a hfa haa upPrefix Pa ch Q H
  have hfEll : f ≤ out.ell := Nat.le_trans hfn (Nat.le_of_lt n.isLt)
  have hPoint : w + f ≤ count :=
    Nat.le_trans (Nat.add_le_add_left hfEll w) hlen
  have hpending : ch.pending.length < Q :=
    actual_initialized_up_pending_short rate source rewards C_star C_h count
      hcross hspan (w + f) hPoint i
  obtain ⟨hQltH, hHle⟩ : Q < H ∧ H ≤ 2 * Q := two_batch_threshold_bounds hpending
  by_cases hsmall : Pa.length < H
  · exact ⟨hpending, hQltH, hHle, Or.inl hsmall⟩
  · have hthreshold : H ≤ Pa.length := Nat.le_of_not_gt hsmall
    have haEll : a ≤ out.ell :=
      Nat.le_trans haa (Nat.succ_le_of_lt n.isLt)
    have haB : a ≤ B.length := Nat.le_trans haEll hBlength
    have hwacount : w + a ≤ count :=
      Nat.le_trans (Nat.add_le_add_left haEll w) hlen
    have hPrefix :=
      ReferenceFirstCollectionUpPrefixThreshold.actual_first_collection_up_first_threshold
        rate source rewards C_star C_h count hcross hspan
    extract_lets -descend +merge +useContext at hPrefix
    have hPrefix := hPrefix i f a hfa haB hwacount
    extract_lets -descend -merge prefixSpan prefixBank prefixH prefixEntries at hPrefix
    have hbankEq : prefixBank = ch := rfl
    have hHEq : prefixH = H := by
      change Q - prefixBank.pending.length + Q = Q - ch.pending.length + Q
      rw [hbankEq]
    have hPEq : prefixEntries = upPrefix := rfl
    rw [hHEq, hPEq] at hPrefix
    have hPrefix := hPrefix hthreshold
    obtain ⟨b, hfb, hba, q0, hqsucc, hPb, hPq, hminimal,
      e, he, happend⟩ := hPrefix
    have hSegChrono :
        ((B.drop f).take (b - f)).Pairwise
          (fun earlier later => earlier.input.time.val < later.input.time.val) :=
      hBchrono.sublist
        ((List.take_sublist _ _).trans (List.drop_sublist _ _))
    have htraceB :=
      ReferenceCoordinatorUpIntervalWindow.actual_trace_positives_eq_retained
        ((B.drop f).take (b - f)) i hSegChrono
    have hcountForReceiver :
        (AffineBatchDecoder.positives p
          (ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace
            ((B.drop f).take (b - f)) i)
          (((B.drop f).take (b - f)).map (fun record => record.input.time))).length =
            Q - ch.pending.length + Q := by
      rw [htraceB]
      exact hPb
    have hbUpper : b ≤ n.val + 1 := Nat.le_trans hba haa
    have hSreceiver := hreceiver b (Nat.le_of_lt hfb) hbUpper
    extract_lets -descend -merge S times tr P chB Qb first window uword at hSreceiver
    have hSreceiver := hSreceiver hcountForReceiver
    rcases hSreceiver with
      ⟨qS, hqSBound, lastS, diagnosticS, tailS, recordingS, LS, hR⟩
    have hRKeep := hR
    rcases hR with
      ⟨hqPosInspect, hfqInspect, hqBeforeInspect, hqBoundInspect,
        hRrecordHit, hRtime, hRrows, hRselected, hRrewards,
        hRfirstLength, hRwindowLength, hRpendingShort, hRpositiveBound,
        hRwindowChronological, hRoldPendingDisjoint, hRlastInWindow,
        hRdecisionTime, hRrecordTime, hRdiagnostic, hRselectedFollower,
        hRselectedChannel, hRupPositive, hRownPositive, hRexecutedTail,
        hRrecording, hRround, hRsiteLedger, hRactualInput, hRinputCheck,
        hRreception, hRnotInvalid, hRledgerPending, hRacceptCheck,
        hRexpectedOffer, hRexpected, hRdiagnosticTime, hRaffineSample,
        hRownObservation, hRdiagnosticBank, hRdecoderPending,
        hRtransition, hRdecoderAfter, hRraw, hRqBank, hRbBank,
        hRcompletedWindow, hRwindowEquations, hCropInspect, hRcoordinatorLive,
        hRfollowerLive, hRfinalAlternative⟩
    have hqStep : qS.val + 1 = b :=
      receiver_at_first_exact_prefix B i hBchrono f b H qS hfqInspect hqBeforeInspect
        hPb hminimal hCropInspect
    have hqEq : qS = q0 :=
      Fin.ext (Nat.add_right_cancel (hqStep.trans hqsucc.symm))
    have hqValues : qS.val = q0.val := congrArg Fin.val hqEq
    have hPqAtS : (upPrefix qS.val).length + 1 = H := by
      rw [hqValues]
      exact hPq
    refine ⟨hpending, hQltH, hHle, Or.inr ?_⟩
    refine ⟨b, Nat.le_of_lt hfb, hbUpper, ?_⟩
    extract_lets -descend +merge +useContext
    refine ⟨qS, hqSBound, lastS, diagnosticS, tailS, recordingS, LS,
      hfb, hba, hqStep, hqPosInspect, hfqInspect, hqBoundInspect,
      hPb, hPqAtS, hminimal, ⟨q0, hqEq, ⟨e, he, happend⟩⟩, ?_⟩
    exact hRKeep

end Bandits.Support.ReferenceFirstCollectionFormedUpFirstThresholdReceiver

end
