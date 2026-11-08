/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionFormedUpOfferReceiver

import Lean.Elab.Tactic.Omega

/-!
# Actual formed-UP bank replay and chronology

Sources: `sources/zip4/manuscript/06_interruptions.tex:476-481`,
`sources/zip4/manuscript/05_binary_transport.tex:27-55`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:100-157`.

The result retains the actual first-collection dispatch and its formed reply,
then records the full physical UP-bank replay and chronological provenance.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions
open ReferenceActivePhysicalHorizon
open ReferencePrelaunchFollower
open ReferenceFirstCollectionFormedUpOfferReceiver

namespace Bandits.Support.ReferenceFirstCollectionFormedUpBankReplay

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

private theorem run_prefix_records
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start total : ℕ) (hspan : start + total ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (n : ℕ) (hn : n ≤ total) :
    (ReferenceActivePhysicalHorizon.run initial rows selected rewards start n
      (by omega) hmode).records =
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start total
        hspan hmode).records.take n := by
  obtain ⟨suffix, hprefix⟩ := ReferenceCollectionPhaseHistory.run_records_prefix
    initial rows selected rewards start n (total - n) (by omega) hmode
  have hadd : n + (total - n) = total := Nat.add_sub_of_le hn
  simp only [hadd] at hprefix
  rw [hprefix, List.take_append_of_le_length (by
    rw [ReferenceActivePhysicalHorizon.run_record_count])]
  symm
  apply List.take_of_length_le
  rw [ReferenceActivePhysicalHorizon.run_record_count]

private theorem run_records_getElem?_actualRunRecordAt
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start total : ℕ) (hspan : start + total ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (index : ℕ) (hindex : index < total) :
    (ReferenceActivePhysicalHorizon.run initial rows selected rewards start total
      hspan hmode).records[index]? = some
      (ReferenceAssignmentPayloadChronology.actualRunRecordAt initial rows selected rewards
        start index (by omega) hmode) := by
  induction total generalizing index with
  | zero => omega
  | succ total ih =>
      have hspan' : start + (total + 1) ≤ p.T := by omega
      have hprefixSpan : start + total ≤ p.T := by omega
      have hprefixLength := ReferenceActivePhysicalHorizon.run_record_count initial rows selected
        rewards start total hprefixSpan hmode
      rw [ReferenceAssignmentPayloadChronology.run_successor_actualRunRecordAt
        initial rows selected rewards start total hspan' hmode]
      by_cases hlt : index < total
      · rw [List.getElem?_append_left (by simpa [hprefixLength] using hlt)]
        exact ih hprefixSpan index hlt
      · have hlast : index = total := by omega
        subst index
        simp [hprefixLength]

private theorem collectionWindow_isPrefix_drop
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (w : ℕ) :
    ReferenceCollectionPhaseHistory.collectionWindow records w <+: records.drop w := by
  unfold ReferenceCollectionPhaseHistory.collectionWindow
  have htail :
      (records.drop (w + 1)).takeWhile
        (fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input) <+:
        records.drop (w + 1) := List.takeWhile_prefix _
  obtain ⟨suffix, htail⟩ := htail
  have hhead : (records.drop w).take 1 ++ records.drop (w + 1) = records.drop w := by
    simp
  refine ⟨suffix, ?_⟩
  calc
    (records.drop w).take 1 ++
        (records.drop (w + 1)).takeWhile
          (fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input) ++ suffix =
      (records.drop w).take 1 ++
        ((records.drop (w + 1)).takeWhile
          (fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input) ++ suffix) := by
            simp [List.append_assoc]
    _ = (records.drop w).take 1 ++ records.drop (w + 1) := by rw [htail]
    _ = records.drop w := hhead

public theorem actual_initialized_first_collection_formed_up_bank_replay
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
      ∃ (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
        (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
        (base : Fin (p.m - 1) → ℕ)
        (cutRecord : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)),
        E.records[w]? = some cutRecord ∧
        cutRecord.input.state.coordinator = .live registers owned base ∧
        registers.payload = out.payload ∧
        out.cutoff.ledger.pending = Finset.univ ∧
        ∃ hBpos : 0 < B.length,
          B[0]'hBpos = cutRecord ∧
        out.cutoff.cut = cutRecord ∧
        let hWindow : out.window = B := by
          simpa [out, E, w, B, ReferenceFirstCollectionReadyStream.actualWindow,
            ReferenceFirstCollectionReadyStream.actualEpoch,
            ReferenceFirstCollectionReadyStream.startTime] using out.windowIsActual
        let hBlength : out.ell ≤ B.length := by simpa [hWindow] using out.withinWindow
        let hlen : w + out.ell ≤ count := by
          have hw : w < count := hshort
          have hElen : E.records.length = count := by
            simpa [E, ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun] using
              ReferenceActivePhysicalHorizon.run_record_count
                (ReferenceFirstCollectionEpochAlignment.actualLaunchState rate source rewards C_star C_h hcross)
                source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
                rewards s count hspan
                (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
                  rate source rewards C_star C_h hcross).1
          have hdrop : (E.records.drop (w + 1)).length + 1 =
              (E.records.drop w).length := by
            rw [List.length_drop, List.length_drop]
            omega
          have htakeWhile :
              ((E.records.drop (w + 1)).takeWhile
                (fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input)).length ≤
                (E.records.drop (w + 1)).length := by
            exact (List.takeWhile_prefix _).length_le
          have hhead : ((E.records.drop w).take 1).length ≤ 1 := by simp
          have hwindowBound : B.length ≤ (E.records.drop w).length := by
            unfold B ReferenceCollectionPhaseHistory.collectionWindow
            rw [List.length_append]
            calc
              ((E.records.drop w).take 1).length +
                  ((E.records.drop (w + 1)).takeWhile
                    (fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input)).length ≤
                  1 + (E.records.drop (w + 1)).length := Nat.add_le_add hhead htakeWhile
              _ = (E.records.drop w).length := by
                simpa [Nat.add_comm] using hdrop
          have hBcount : B.length ≤ count - w := by
            rw [List.length_drop, hElen] at hwindowBound
            exact hwindowBound
          omega
        let initial := ReferenceFirstCollectionEpochAlignment.actualLaunchState
          rate source rewards C_star C_h hcross
        let hmode := (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
          rate source rewards C_star C_h hcross).1
        let selected := ActualInitializationPhysicalStep.selectedRowIndex p source
        let X (t : ℕ) (hwt : w + t ≤ count) :=
          (ReferenceActivePhysicalHorizon.run initial source.1.2 selected rewards s (w + t)
            (by omega) hmode).finalState
        (w + out.ell ≤ count ∧
         (∀ (k : Fin out.ell),
          (B[k.val]'(by omega)).input.state = X k.val (by omega) ∧
          (B[k.val]'(by omega)).output.next = X (k.val + 1) (by omega)) ∧
        (∀ (t : ℕ) (ht : t ≤ out.ell),
          ReferenceUpDecoderBankInvariant.upBankInvariant (X t (by omega)) ∧
          (X t (by omega)).coordinator ≠ .dagger) ∧
        (∀ i : Fin (p.m - 1), ((X 0 (by omega)).upDecoderBank i).pending = []) ∧
        (∀ (i : Fin (p.m - 1)) (a b : ℕ) (hab : a ≤ b) (hb : b ≤ out.ell),
          let S := (B.drop a).take (b - a)
          let times := S.map (fun record => record.input.time)
          let tr := ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace S i
          let P := ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries S i
          (X b (by omega)).upDecoderBank =
            ReferenceCoordinatorUpDecoderReplay.replay (X a (by omega)).upDecoderBank
              (ReferenceCoordinatorUpDecoderReplay.retainedUpDiagnostics S) ∧
          AffineBatchDecoder.run p tr times ((X a (by omega)).upDecoderBank i) =
            (X b (by omega)).upDecoderBank i ∧
          AffineBatchDecoder.collected ((X b (by omega)).upDecoderBank i) =
            AffineBatchDecoder.collected ((X a (by omega)).upDecoderBank i) ++ P ∧
          AffineBatchDecoder.positives p tr times = P ∧
          times.Pairwise (fun x y => x.val < y.val) ∧
          ((X a (by omega)).upDecoderBank i).pending.length < AffineBatchDecoder.quota p ∧
          ∀ e, e ∈ ((X a (by omega)).upDecoderBank i).pending →
            e ∈ ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries
                (E.records.take (w + a)) i ∧
            e.time.val < s + w + a ∧
            ∀ t, t ∈ times → e.time.val < t.val)) ∧
        (∀ (n : Fin out.ell), 0 < n.val →
          ∀ i : Fin (p.m - 1),
            i ∈ (out.ledgers ⟨n.val - 1, by omega⟩).pending →
              ∃ (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
                (incoming : ReferenceActivePhysicalStep.Ledger rate)
                (cell : ReferenceFirstCollectionReadyStream.ContinuingStreamCell
                  source rewards E.records (w + n.val) count s
                  r out.payload incoming out.saved)
                (state : ReferencePrelaunchFollower.State p rate.eta)
                (memory : ActiveFollowerLifecycle.LocalMemory p),
                out.window[n.val]? = some r ∧
                r.input.time.val + 1 = s + w + 1 + n.val ∧
                r.input.rows = source.1.2 ∧
                r.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p source ∧
                r.input.rewards = rewards ∧
                incoming = out.ledgers ⟨n.val - 1, by omega⟩ ∧
                i ∈ incoming.pending ∧
                ReferenceContinuingCollectionStartDomains.continuingCollectionReadyDomain
                  r.input out.payload incoming out.saved ∧
                cell.serviceLedger = out.ledgers n ∧
                r.input.state.followers i = .ordinary state memory ∧
                state.status = .unoccupied ∧
                ActiveFollowerLifecycle.localStateDomainValid state ∧
                state.S ≤ p.T * D p ∧ state.delta ≤ D p ∧ state.backlog ≤ p.T * D p ∧
                state.S + state.backlog ≤ w * D p ∧
                state.downBatch.pending.length < AffineBatchDecoder.quota p ∧
                (∀ batch ∈ state.downBatch.completed,
                  batch.length = AffineBatchDecoder.quota p) ∧
                ((state.lastDown = none ∧ state.S = 0 ∧ state.delta = 0 ∧ state.backlog = 0) ∨
                  state.lastDown = some (out.payload.downRecord i)) ∧
                (state.lastDown = some (out.payload.downRecord i) →
                  ∃ (U : OrdinaryMessageCodec.UpRecord
                      (ReferencePrelaunchFollower.codecParams p rate.eta)),
                    U.val = ActiveFollowerQueueOperation.upOfferFields state ∧
                    U.val.sigma = s + 1 ∧
                    1 ≤ U.val.sigma ∧
                    (ReferenceActivePhysicalStep.upSenderIndex r.input = i →
                      PublicDiscreteDraws.slotDraw
                          (r.input.row.2 r.input.time).1 = PublicDiscreteDraws.upSlot →
                        ((ReferenceActivePhysicalStep.prepare r.input).followers.followers i).configuration =
                            .ordinary state memory ∧
                        ActiveFollowerQueueOperation.checkedUpOffer rate.eta i r.input.row
                          (r.input.state.activations i) r.input.time state = .offer U ∧
                        ReferenceFollowerFixedReply.actualUpExpected r =
                          some ((OrdinaryMessageCodec.wordEquivFlat
                            (CoordinatorCollectionLedger.codecParams p rate.eta.val))
                            (OrdinaryMessageCodec.encodeUp
                              (CoordinatorCollectionLedger.codecParams p rate.eta.val) U))) ∧
                    (out.payload.downRecord i).val.sigma = s + 1 ∧
                    ReferencePrelaunchFollower.acceptedStart state = s + 1 ∧
                    ∃ (j : ℕ) (hjIndex : j < E.records.length)
                      (acceptedRecord : ReferenceActivePhysicalHorizon.RoundRecord
                        (p := p) (rate := rate)),
                      j < w + n.val ∧ E.records[j]? = some acceptedRecord ∧
                      ReferenceAcceptedUpFollowerHistory.RetainedDown
                        (E.records[j]'(hjIndex)) i
                        (out.payload.downRecord i) ∧
                      (∃ (logged : ReferencePrelaunchFollower.State p rate.eta)
                        (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
                        (after : ReferencePrelaunchFollower.State p rate.eta)
                        (raw : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p)))
                        (scan : FollowerCutoffScan.ScanResult p.T)
                        (registers' : ℕ × ℕ) (lastService : ℕ),
                        (acceptedRecord.output.followers i).downInput = some logged ∧
                        (acceptedRecord.output.followers i).down = some cut ∧
                        cut.outcome = ActiveFollowerDownAcceptance.LocalDownResult.accepted
                          logged after raw (out.payload.downRecord i) scan registers' lastService) ∧
                      acceptedRecord.input.time.val + 1 = s + j + 1 ∧
                      acceptedRecord.input.rows = source.1.2 ∧
                      acceptedRecord.input.selected =
                        ActualInitializationPhysicalStep.selectedRowIndex p source ∧
                      acceptedRecord.input.rewards = rewards ∧
                      (∀ (j' : ℕ) (hjPrimeIndex : j' < E.records.length)
                        (other : ReferenceActivePhysicalHorizon.RoundRecord
                          (p := p) (rate := rate)),
                        j' < w + n.val → E.records[j']? = some other →
                          ReferenceAcceptedUpFollowerHistory.RetainedDown
                            (E.records[j']'(hjPrimeIndex)) i
                            (out.payload.downRecord i) → j' = j) ∧
                      let f := if j < w then 0 else j - w + 1
                      ∃ hf : f < B.length,
                        f ≤ n.val ∧
                        B[f].input.time.val + 1 = max (s + w + 1) (s + j + 2) ∧
                        (j < w → f = 0) ∧
                        (j = w → f = 1) ∧
                        (∀ (k : Fin B.length) (_hkpos : 0 < k.val)
                          (hkn : k.val ≤ n.val),
                          (out.ledgers ⟨n.val - 1, by omega⟩).pending ⊆
                            (out.ledgers ⟨k.val - 1, by omega⟩).pending) ∧
                        (∀ (b : ℕ) (hfb : f ≤ b) (hbn : b ≤ n.val + 1),
                          let S := (B.drop f).take (b - f)
                          let times := S.map (fun record => record.input.time)
                          let tr := ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace S i
                          let P := ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries S i
                          (X b (by omega)).upDecoderBank =
                            ReferenceCoordinatorUpDecoderReplay.replay
                              (X f (by omega)).upDecoderBank
                              (ReferenceCoordinatorUpDecoderReplay.retainedUpDiagnostics S) ∧
                          AffineBatchDecoder.run p tr times
                              ((X f (by omega)).upDecoderBank i) =
                            (X b (by omega)).upDecoderBank i ∧
                          AffineBatchDecoder.collected ((X b (by omega)).upDecoderBank i) =
                            AffineBatchDecoder.collected ((X f (by omega)).upDecoderBank i) ++ P ∧
                          AffineBatchDecoder.positives p tr times = P ∧
                          times.Pairwise (fun x y => x.val < y.val) ∧
                          ((X f (by omega)).upDecoderBank i).pending.length <
                            AffineBatchDecoder.quota p ∧
                          ∀ e, e ∈ ((X f (by omega)).upDecoderBank i).pending →
                            e ∈ ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries
                                (E.records.take (w + f)) i ∧
                            e.time.val < s + w + f ∧
                            ∀ t, t ∈ times → e.time.val < t.val) ∧
                        ∀ (k : Fin B.length) (hfk : f ≤ k.val)
                          (hkn : k.val ≤ n.val),
                          ∃ (choice : ReferencePrelaunchFollower.State p rate.eta)
                            (choiceMemory : ActiveFollowerLifecycle.LocalMemory p),
                            (ReferenceFirstCollectionFormedReplyStateInterval.actualCollectionChoice
                              B i k).configuration = .ordinary choice choiceMemory ∧
                            ActiveFollowerLifecycle.localStateDomainValid choice ∧
                            choice.status = .unoccupied ∧
                            ReferenceFollowerReplyChronology.reply choice =
                              ReferenceFollowerReplyChronology.reply state ∧
                            choice.lastDown = some (out.payload.downRecord i) ∧
                            choice.S = state.S ∧ choice.delta = state.delta ∧
                            choice.backlog = state.backlog ∧
                            (ReferenceFirstCollectionFormedReplyStateInterval.actualCollectionChoice
                              B i k).row =
                              (ReferenceFirstCollectionFormedReplyStateInterval.actualCollectionRecord
                                B k).input.row ∧
                            (ReferenceFirstCollectionFormedReplyStateInterval.actualCollectionChoice
                              B i k).follower = i ∧
                            (ReferenceFirstCollectionFormedReplyStateInterval.actualCollectionChoice
                              B i k).activation =
                              (ReferenceFirstCollectionFormedReplyStateInterval.actualCollectionRecord
                                B k).input.state.activations i ∧
                            (ReferenceFirstCollectionFormedReplyStateInterval.actualCollectionChoice
                              B i k).time =
                              (ReferenceFirstCollectionFormedReplyStateInterval.actualCollectionRecord
                                B k).input.time ∧
                            ∃ (before : ReferencePrelaunchFollower.State p rate.eta)
                              (beforeMemory : ActiveFollowerLifecycle.LocalMemory p),
                              (ReferenceFirstCollectionFormedReplyStateInterval.actualCollectionRecord
                                B k).input.state.followers i =
                                  .ordinary before beforeMemory ∧
                              ActiveFollowerLifecycle.localStateDomainValid before ∧
                              ActiveFollowerLifecycle.startRound rate.eta
                                (ReferenceFirstCollectionFormedReplyStateInterval.actualCollectionRecord
                                  B k).input.time before beforeMemory =
                                  .ok (choice, choiceMemory) ∧
                              ReferenceFollowerReplyChronology.reply choice =
                                ReferenceFollowerReplyChronology.reply before ∧
                              ((k.val = 0 →
                                i ∈ out.cutoff.ledger.pending ∧
                                out.cutoff.ledger.pending = Finset.univ ∧
                                (ReferenceFirstCollectionFormedReplyStateInterval.actualCollectionRecord
                                  B k).input.state.coordinator = .live registers owned base ∧
                                E.records[w]? = some cutRecord) ∧
                               (0 < k.val →
                                i ∈ (out.ledgers ⟨k.val - 1, by omega⟩).pending ∧
                                incoming = out.ledgers ⟨n.val - 1, by omega⟩ ∧
                                i ∈ incoming.pending)) ∧
                              ((hslot : PublicDiscreteDraws.slotDraw
                                  (((ReferenceFirstCollectionFormedReplyStateInterval.actualCollectionRecord
                                    B k).input.row).2
                                      (ReferenceFirstCollectionFormedReplyStateInterval.actualCollectionRecord
                                        B k).input.time).1 = PublicDiscreteDraws.upSlot) →
                                (hselected : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m
                                  p.m_lt_K
                                  (((ReferenceFirstCollectionFormedReplyStateInterval.actualCollectionRecord
                                    B k).input.row).2
                                      (ReferenceFirstCollectionFormedReplyStateInterval.actualCollectionRecord
                                        B k).input.time).1 = i) →
                                  ActiveFollowerQueueOperation.checkedUpOffer rate.eta i
                                    (ReferenceFirstCollectionFormedReplyStateInterval.actualCollectionRecord
                                      B k).input.row
                                    ((ReferenceFirstCollectionFormedReplyStateInterval.actualCollectionRecord
                                      B k).input.state.activations i)
                                    (ReferenceFirstCollectionFormedReplyStateInterval.actualCollectionRecord
                                      B k).input.time choice = .offer U ∧
                                  ReferenceUpReception.currentOfferWord rate
                                    (ReferenceFirstCollectionFormedReplyStateInterval.actualCollectionRecord
                                      B k).input.row i
                                    (ReferenceFirstCollectionFormedReplyStateInterval.actualCollectionRecord
                                      B k).input.time
                                    (ReferenceFirstCollectionFormedReplyStateInterval.actualCollectionChoice
                                      B i k)
                                    (ReferenceFollowerFixedReply.actualChoice_alignment
                                      (ReferenceFirstCollectionFormedReplyStateInterval.actualCollectionRecord
                                        B k) i).1
                                    (ReferenceFollowerFixedReply.actualChoice_alignment
                                      (ReferenceFirstCollectionFormedReplyStateInterval.actualCollectionRecord
                                        B k) i).2.1
                                    (ReferenceFollowerFixedReply.actualChoice_alignment
                                      (ReferenceFirstCollectionFormedReplyStateInterval.actualCollectionRecord
                                        B k) i).2.2 = some (encodedUpOfferWord U) ∧
                                  ReferenceFollowerFixedReply.actualUpExpected
                                    (ReferenceFirstCollectionFormedReplyStateInterval.actualCollectionRecord
                                      B k) = some (encodedUpOfferWord U) ∧
                                  ReferenceActivePhysicalStep.upExpected
                                    (ReferenceActivePhysicalStep.prepare
                                      (ReferenceFirstCollectionFormedReplyStateInterval.actualCollectionRecord
                                        B k).input) = some (encodedUpOfferWord U)) ∧
                              (k.val = 0 →
                                ∃ (cutBefore : ReferencePrelaunchFollower.State p rate.eta)
                                  (cutMemory : ActiveFollowerLifecycle.LocalMemory p),
                                  cutRecord.input.state.followers i =
                                    .ordinary cutBefore cutMemory ∧
                                  (ReferenceFollowerFixedReply.actualChoice cutRecord i).configuration =
                                    .ordinary { cutBefore with status := .unoccupied } cutMemory ∧
                                  ActiveFollowerLifecycle.localStateDomainValid
                                    { cutBefore with status := .unoccupied } ∧
                                  ActiveFollowerLifecycle.startRound rate.eta cutRecord.input.time
                                    cutBefore cutMemory =
                                      .ok ({ cutBefore with status := .unoccupied }, cutMemory) ∧
                                  Nonempty (ReferenceFirstCollectionReadyStream.CutoffExecution
                                    out.cutoff.cut out.cutoff.payload out.cutoff.ledger) ∧
                                  ∃ execution : ReferenceFirstCollectionReadyStream.CutoffExecution
                                      cutRecord out.cutoff.payload out.cutoff.ledger,
                                    execution.initial.pending = Finset.univ ∧
                                    execution.started.pending = Finset.univ) ∧
                              (0 < k.val →
                                ∃ (jK : ℕ)
                                  (recordK : ReferenceActivePhysicalHorizon.RoundRecord
                                    (p := p) (rate := rate))
                                  (incomingK : ReferenceActivePhysicalStep.Ledger rate)
                                  (cellK : ReferenceFirstCollectionReadyStream.ContinuingStreamCell
                                    source rewards E.records jK count s recordK
                                    out.payload incomingK out.saved),
                                  jK = w + k.val ∧
                                  out.window[k.val]? = some recordK ∧
                                  cellK.serviceLedger = out.ledgers ⟨k.val, by omega⟩ ∧
                                  incomingK = out.ledgers ⟨k.val - 1, by omega⟩ ∧
                                  (ReferenceFirstCollectionFormedReplyStateInterval.actualCollectionRecord
                                    B k) = recordK ∧
                                  recordK.input.state.coordinator =
                                    .collection out.payload incomingK out.saved ∧
                                  recordK.input.time.val + 1 = s + w + 1 + k.val ∧
                                  recordK.input.rows = source.1.2 ∧
                                  recordK.input.selected =
                                    ActualInitializationPhysicalStep.selectedRowIndex p source ∧
                                  recordK.input.rewards = rewards ∧
                                  choice = before ∧ choiceMemory = beforeMemory ∧
                                  ∃ (tail : ReferenceCollectionPhaseHistory.Tail recordK.input)
                                    (recording : CoordinatorRecordingOperation.Output p)
                                    (L : ReferenceActivePhysicalStep.Ledger rate)
                                    (diagnostic : ReferenceActivePhysicalStep.UpDiagnostic p rate),
                                    ReferenceCollectionPhaseHistory.executedTail recordK.input =
                                      some tail ∧
                                    tail.payload = out.payload ∧ tail.ledger = incomingK ∧
                                    CoordinatorRecorderComplementBridge.run
                                      (ReferenceActivePhysicalStep.collectionRecordingInput
                                        (ReferenceActivePhysicalStep.prepare recordK.input)
                                        tail.payload tail.started tail.weights) = some recording ∧
                                    CoordinatorCollectionLedger.startRound tail.ledger
                                      (recordK.input.time.val + 1)
                                      (ReferenceActivePhysicalStep.collectionEnabled tail.ledger
                                        recordK.input.time)
                                      (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder
                                        recording) = .success L ∧
                                    L = cellK.started ∧
                                    ReferenceCoordinatorUpPhysicalCall.siteLedger?
                                      (x := recordK.input) = some L ∧
                                    CoordinatorUpReception.receptionInputCheck
                                      (ReferenceCoordinatorUpPhysicalCall.actualUpInput
                                        recordK.input L) = true ∧
                                    recordK.output.coordinator.up = some diagnostic ∧
                                    diagnostic.input = ReferenceCoordinatorUpPhysicalCall.actualUpInput
                                      recordK.input L ∧
                                    tail.reception = some (L,
                                      ReferenceActivePhysicalStep.receiveUp
                                        (ReferenceActivePhysicalStep.prepare recordK.input) L) ∧
                                    (ReferenceActivePhysicalStep.receiveUp
                                      (ReferenceActivePhysicalStep.prepare recordK.input) L).result ≠
                                        .invalid ∧
                                    diagnostic.input.time = recordK.input.time ∧
                                    diagnostic.input.affineSample =
                                      ((recordK.input.rows recordK.input.selected).2
                                        recordK.input.time).2
                                        (1, CoordinatorUpMeasurability.selectedChannelFollower
                                          ((recordK.input.rows recordK.input.selected).2
                                            recordK.input.time)) ∧
                                    diagnostic.input.ownObservation =
                                      (ReferenceActivePhysicalStep.prepare recordK.input).feedback.feedback
                                        (ActiveRoundActions.coordinator p.two_le_m) ∧
                                    i ∈ L.pending ∧
                                    CoordinatorCollectionLedger.acceptUpCheck L i U = true ∧
                                    ((hslot : PublicDiscreteDraws.slotDraw
                                        (recordK.input.row.2 recordK.input.time).1 =
                                          PublicDiscreteDraws.upSlot) →
                                      (hselected : PublicDiscreteDraws.selectedFollowerDraw
                                        p.two_le_m p.m_lt_K
                                        (recordK.input.row.2 recordK.input.time).1 = i) →
                                        (∀ M : ReferenceCollectionPhaseHistory.UpRecord p rate,
                                          ReferenceCollectionPhaseHistory.filteredParsed
                                            recordK.input L = some M → M = U) ∧
                                        (∀ M : ReferenceCollectionPhaseHistory.UpRecord p rate,
                                          ReferenceCollectionPhaseHistory.AcceptedUp
                                            recordK.input i M → M = U))))) := by

  classical
  obtain ⟨d, registers, owned, base, cutRecord, hcutIndex, hcutState,
    hpayload, hpending, hBpos, hBzero, hcutoff, hboundaries⟩ :=
    ReferenceFirstCollectionFormedUpOfferReceiver.actual_initialized_first_collection_formed_up_offer_receiver
      rate source rewards C_star C_h count hcross hspan hshort
  let out := d.stream
  let E := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
    rate source rewards C_star C_h hcross count hspan
  let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records).length
  let s := ReferenceInitializationRun.elapsed p
    (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
  let B := ReferenceCollectionPhaseHistory.collectionWindow E.records w
  have hWindow : out.window = B := by
    simpa [out, E, w, B, ReferenceFirstCollectionReadyStream.actualWindow,
      ReferenceFirstCollectionReadyStream.actualEpoch,
      ReferenceFirstCollectionReadyStream.startTime] using out.windowIsActual
  have hBlength : out.ell ≤ B.length := by
    simpa [hWindow] using out.withinWindow
  have hElen : E.records.length = count := by
    simpa [E, ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun] using
      ReferenceActivePhysicalHorizon.run_record_count
        (ReferenceFirstCollectionEpochAlignment.actualLaunchState rate source rewards C_star C_h hcross)
        source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s count
        hspan (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
          rate source rewards C_star C_h hcross).1
  have hlen : w + out.ell ≤ count := by
    have hw : w < count := hshort
    have hwE : w < E.records.length := by rw [hElen]; exact hw
    have hdrop : (E.records.drop w).length = 1 + (E.records.drop (w + 1)).length := by
      rw [List.length_drop, List.length_drop]
      omega
    have htakeWhile :
        ((E.records.drop (w + 1)).takeWhile
          (fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input)).length ≤
          (E.records.drop (w + 1)).length :=
      (List.takeWhile_prefix _).length_le
    have hhead : ((E.records.drop w).take 1).length ≤ 1 := by simp
    have hwindowBound : B.length ≤ (E.records.drop w).length := by
      unfold B ReferenceCollectionPhaseHistory.collectionWindow
      rw [List.length_append]
      calc
        ((E.records.drop w).take 1).length +
            ((E.records.drop (w + 1)).takeWhile
              (fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input)).length ≤
            1 + (E.records.drop (w + 1)).length := Nat.add_le_add hhead htakeWhile
        _ = (E.records.drop w).length := hdrop.symm
    have hBcount : B.length ≤ count - w := by
      rw [List.length_drop, hElen] at hwindowBound
      exact hwindowBound
    omega
  let initial := ReferenceFirstCollectionEpochAlignment.actualLaunchState
    rate source rewards C_star C_h hcross
  let hmode := (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
    rate source rewards C_star C_h hcross).1
  let selected := ActualInitializationPhysicalStep.selectedRowIndex p source
  let X (t : ℕ) (_hwt : w + t ≤ count) :=
    (ReferenceActivePhysicalHorizon.run initial source.1.2 selected rewards s (w + t)
      (by omega) hmode).finalState
  have hseedData := ReferenceFirstLaunchNumericalCell.actual_launch_seed
    rate source rewards C_star C_h hcross
  rcases hseedData with ⟨_, _, _, hfirst, hbank, _, _, _⟩
  have hfirst : initial.coordinator = .first := by
    simpa [initial, ReferenceFirstCollectionEpochAlignment.actualLaunchState,
      ReferenceFirstLaunchNumericalCell.launchState] using hfirst
  have hbank : initial.upDecoderBank = CoordinatorUpReception.initialUpDecoderBank p := by
    simpa [initial, ReferenceFirstCollectionEpochAlignment.actualLaunchState,
      ReferenceFirstLaunchNumericalCell.launchState] using hbank
  have hinitial : ReferenceUpDecoderBankInvariant.upBankInvariant initial := by
    change ReferenceUpDecoderBankInvariant.coordinatorBankInvariant
      initial.coordinator initial.upDecoderBank
    rw [hfirst, hbank]
    exact ⟨CoordinatorUpReception.initialUpDecoderBank_wellFormed p, fun _ => rfl⟩
  have hseed (i : Fin (p.m - 1)) :
      AffineBatchDecoder.collected (initial.upDecoderBank i) = [] := by
    simp [hbank, CoordinatorUpReception.initialUpDecoderBank,
      AffineBatchDecoder.initial, AffineBatchDecoder.collected]
  have hcutRecordMem : cutRecord ∈ E.records := by
    have hget := List.getElem?_eq_some_iff.mp hcutIndex
    rw [← hget.2]
    exact List.getElem_mem _
  have hreadyShort := ReferenceFirstCollectionReadyStream.generatedFirstCutoffRun_short
    source rewards C_star C_h hcross count hspan hshort
  have hreadyInit :=
    ReferenceFirstCollectionReadyInitialization.actual_first_collection_ready_initialization
      rate source rewards C_star C_h hcross s rfl count hspan hreadyShort
  dsimp only at hreadyInit
  rcases hreadyInit with ⟨_hsT, cutReady, suffixReady, _hsplitReady, hindexReady,
    _htimeReady, _hstateReady, _hrowsReady, _hselectedReady, _hrewardsReady,
    rReady, qReady, baseReady, hreadyLive, _hsigmaReady, dispatchedReady,
    hstartReady, ledgerReady, hinitReady, hledgerReady, hdomainReady,
    _hclockReady, _hpendingReady, _hnoAssignmentReady, _selectedReady,
    hbranchReady, _huReady, _huTReady, _hugReady, _hsigmaLedgerReady,
    _hcutoffLedgerReady, _recordingReady, _hactualInputReady, _htraceReady,
    _hrecordingDiagnosticReady, _hrecordingRunReady, _ledgerStartedReady,
    _hstartSuccessReady, _hstartCandidateReady, _inputReady, _decodedReady,
    _bankReady, _diagnosticReady, finishedReady, _hinputReady,
    _hinputDomainReady, _hinputCheckReady, _htransitionReady, _hquotaReady,
    _hdecodedReady, _hreceiveReady, _hbankReady, _hbankUpdateReady, _hbankFrameReady,
    _hrawParsedReady, _hreceiveDiagnosticReady, _hdiagnosticInputReady,
    _hdiagnosticExpectedReady, _hdiagnosticAfterReady, _hdiagnosticRawReady,
    _hdiagnosticParsedReady, _hdiagnosticAcceptedReady, _hdiagnosticWrongReady,
    _hfinishReady, _hreadyTail⟩
  have hgeneratedRun :
      (ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun rate source rewards
        C_star C_h hcross s rfl count hspan).records = E.records := by
    simpa [E, ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun,
      ReferenceFirstCollectionReadyStream.actualEpoch,
      ReferenceFirstCollectionReadyStream.startTime] using
      ReferenceFirstCollectionReadyStream.generatedFirstCutoffRun_records_eq
        source rewards C_star C_h hcross count hspan
  have hgeneratedWindowLength :
      (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun rate source rewards
          C_star C_h hcross s rfl count hspan).records).length = w := by
    simpa [w, E, ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun,
      ReferenceFirstCollectionReadyStream.actualEpoch] using
      congrArg (fun rs : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) =>
        (ReferenceFirstLiveConfirmationHistory.firstLiveWindow rs).length) hgeneratedRun
  have hwE : w < E.records.length := by rw [hElen]; exact hshort
  have hreadyCut : cutReady = E.records[w]'hwE := by
    simpa only [hgeneratedRun, hgeneratedWindowLength] using hindexReady
  have hsameCut : cutReady = cutRecord := by
    have hget := List.getElem?_eq_getElem (l := E.records) (i := w) hwE
    exact hreadyCut.trans (Option.some.inj (hget.symm.trans hcutIndex))
  have hcutChosenReady : ReferenceUpDecoderBankInvariant.isActualCutoffChosen
      cutReady.output.preparation.coordinator := by
    refine ⟨rReady, qReady, baseReady,
      .cutoffChosen dispatchedReady hstartReady ledgerReady hinitReady hledgerReady
        hdomainReady _hclockReady _hpendingReady _hnoAssignmentReady _selectedReady,
      hreadyLive, hbranchReady, trivial⟩
  have hcutChosen : ReferenceUpDecoderBankInvariant.isActualCutoffChosen
      cutRecord.output.preparation.coordinator := by
    cases hsameCut
    exact hcutChosenReady
  have hcutActualRecord := run_records_getElem?_actualRunRecordAt initial source.1.2
    selected rewards s count hspan hmode w hshort
  have hcutSpan : s + (w + 1) ≤ p.T := by omega
  have hcutActualEq : cutRecord =
      ReferenceAssignmentPayloadChronology.actualRunRecordAt initial source.1.2 selected
        rewards s w hcutSpan hmode :=
    Option.some.inj (hcutIndex.symm.trans hcutActualRecord)
  have hcutInputState : cutRecord.input.state = X 0 (by omega) := by
    rw [hcutActualEq]
    rfl
  have hcutPending := ReferenceUpDecoderBankInvariant.run_cutoff_up_pending_empty
    initial source.1.2 selected rewards s count hspan hmode hinitial cutRecord
    hcutRecordMem hcutChosen
  have hEndpoint : ∀ (k : Fin out.ell),
      (B[k.val]'(by omega)).input.state = X k.val (by omega) ∧
      (B[k.val]'(by omega)).output.next = X (k.val + 1) (by omega) := by
    intro k
    have hkB : k.val < B.length := lt_of_lt_of_le k.isLt hBlength
    let kWindow : Fin out.window.length := ⟨k.val, by rw [hWindow]; exact hkB⟩
    have hlookup : E.records[w + k.val]? = some (B[k.val]'hkB) := by
      simpa [out, E, w, hWindow,
        ReferenceFirstCollectionReadyStream.actualEpoch,
        ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun] using
          (out.alignment kWindow).1
    have hactual := run_records_getElem?_actualRunRecordAt initial source.1.2 selected
      rewards s count hspan hmode (w + k.val) (by omega)
    have hrecord : B[k.val]'hkB =
        ReferenceAssignmentPayloadChronology.actualRunRecordAt initial source.1.2 selected
          rewards s (w + k.val) (by omega) hmode :=
      Option.some.inj (hlookup.symm.trans hactual)
    constructor
    · rw [hrecord]
      rfl
    · rw [hrecord]
      have hnext := ReferenceAssignmentPayloadChronology.run_successor_finalState_eq_actualRunRecordAt
        initial source.1.2 selected rewards s (w + k.val) (by omega) hmode
      simpa [X, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hnext.symm
  have hordinary : ∀ (t : ℕ) (ht : t ≤ out.ell),
      (X t (by omega)).coordinator ≠ .dagger := by
    intro t ht
    by_cases hzero : t = 0
    · subst t
      have hcoord : (X 0 (by omega)).coordinator = .live registers owned base := by
        rw [← hcutInputState, hcutState]
      intro hdagger
      rw [hcoord] at hdagger
      cases hdagger
    · have hpositive : 0 < t := Nat.pos_of_ne_zero hzero
      have hprev : t - 1 < out.ell := by omega
      have hprevFin : (⟨t - 1, hprev⟩ : Fin out.ell).val + 1 = t := by
        exact Nat.sub_add_cancel (show 1 ≤ t by omega)
      have hstate := (hEndpoint ⟨t - 1, hprev⟩).2
      by_cases hfirstCell : t = 1
      · subst t
        have hzeroEndpoint := (hEndpoint ⟨0, by omega⟩).2
        rw [hBzero] at hzeroEndpoint
        have hnextCoord := congrArg (fun state => state.coordinator) hzeroEndpoint
        have hcutoffCoord := out.cutoff.outputCoordinator
        rw [hcutoff] at hcutoffCoord
        have hcoord : (X 1 (by omega)).coordinator =
            .collection out.cutoff.payload out.cutoff.ledger out.cutoff.saved :=
          hnextCoord.symm.trans hcutoffCoord
        intro hdagger
        rw [hcoord] at hdagger
        cases hdagger
      · have hprevPositive : 0 < t - 1 := by omega
        obtain ⟨_j, record, incoming, cell, _hj, hcellIndex, _hservice, _hincoming⟩ :=
          out.cell_at ⟨t - 1, hprev⟩ hprevPositive
        have hrecordWindow : out.window[t - 1]? = some record := hcellIndex
        have hwindowRecord : out.window[t - 1]? = some (B[t - 1]'(by omega)) := by
          rw [hWindow]
          exact List.getElem?_eq_some_iff.mpr ⟨by omega, rfl⟩
        have hrecordEq : record = B[t - 1]'(by omega) :=
          Option.some.inj (hrecordWindow.symm.trans hwindowRecord)
        have hnextOrd := cell.serviceNextCoordinator
        have hnextEq := congrArg (fun r : ReferenceActivePhysicalHorizon.RoundRecord
            (p := p) (rate := rate) => r.output.next.coordinator) hrecordEq
        have hstateCoord : (B[t - 1]'(by omega)).output.next.coordinator =
            (X t (by omega)).coordinator := by
          simpa [Nat.sub_add_cancel (by omega : 1 ≤ t)] using
            congrArg (fun state : ReferenceActivePhysicalHorizon.State p rate => state.coordinator) hstate
        have hcoord : (X t (by omega)).coordinator =
            .collection out.payload cell.serviceLedger out.saved := by
          calc
            (X t (by omega)).coordinator =
                (B[t - 1]'(by omega)).output.next.coordinator := hstateCoord.symm
            _ = record.output.next.coordinator := hnextEq.symm
            _ = .collection out.payload cell.serviceLedger out.saved := hnextOrd
        intro hdagger
        rw [hcoord] at hdagger
        cases hdagger
  have hrunInvariant : ∀ (t : ℕ) (ht : t ≤ out.ell),
      ReferenceUpDecoderBankInvariant.upBankInvariant (X t (by omega)) := by
    intro t ht
    have hprefix := ReferenceUpDecoderBankInvariant.run_prefix_upBankInvariant
      initial source.1.2 selected rewards s count hspan hmode hinitial (w + t) (by omega)
    simpa [X] using hprefix
  have hzeroPending : ∀ i : Fin (p.m - 1), ((X 0 (by omega)).upDecoderBank i).pending = [] := by
    intro i
    have h := hcutPending i
    simpa [hcutInputState] using h
  have hAllBanks : ∀ (i : Fin (p.m - 1)) (a b : ℕ)
      (hab : a ≤ b) (hb : b ≤ out.ell),
      let S := (B.drop a).take (b - a)
      let times := S.map (fun record => record.input.time)
      let tr := ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace S i
      let P := ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries S i
      (X b (by omega)).upDecoderBank =
          ReferenceCoordinatorUpDecoderReplay.replay (X a (by omega)).upDecoderBank
            (ReferenceCoordinatorUpDecoderReplay.retainedUpDiagnostics S) ∧
      AffineBatchDecoder.run p tr times ((X a (by omega)).upDecoderBank i) =
        (X b (by omega)).upDecoderBank i ∧
      AffineBatchDecoder.collected ((X b (by omega)).upDecoderBank i) =
        AffineBatchDecoder.collected ((X a (by omega)).upDecoderBank i) ++ P ∧
      AffineBatchDecoder.positives p tr times = P ∧
      times.Pairwise (fun x y => x.val < y.val) ∧
      ((X a (by omega)).upDecoderBank i).pending.length < AffineBatchDecoder.quota p ∧
      ∀ e, e ∈ ((X a (by omega)).upDecoderBank i).pending →
        e ∈ ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries
            (E.records.take (w + a)) i ∧
        e.time.val < s + w + a ∧
        ∀ t, t ∈ times → e.time.val < t.val := by
    intro i a b hab hb
    let A := w + a
    let C := w + b
    let preRun := ReferenceActivePhysicalHorizon.run initial source.1.2 selected rewards s A
      (by omega) hmode
    let full := ReferenceActivePhysicalHorizon.run initial source.1.2 selected rewards s C
      (by omega) hmode
    let S := (B.drop a).take (b - a)
    let times := S.map (fun record => record.input.time)
    let tr := ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace S i
    let P := ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries S i
    have hhab : A ≤ C := by dsimp [A, C]; omega
    have hspanC : s + C ≤ p.T := by dsimp [C]; omega
    have hspanA : s + A ≤ p.T := by dsimp [A]; omega
    have hrunCount : C ≤ count := by dsimp [C]; omega
    have hpreRecords : preRun.records = E.records.take A := by
      simpa [preRun, E, A, ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun] using
        run_prefix_records initial source.1.2 selected rewards s count hspan hmode A
          (by omega)
    have hfullRecords : full.records = E.records.take C := by
      simpa [full, E, C, ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun] using
        run_prefix_records initial source.1.2 selected rewards s count hspan hmode C
          hrunCount
    have hSlen : S.length = b - a := by
      have htakeBound : b - a ≤ B.length - a := by omega
      simp [S, List.length_take, List.length_drop, Nat.min_eq_left htakeBound]
    have hfullLen : full.records.length = C := by
      simpa [full] using ReferenceActivePhysicalHorizon.run_record_count initial source.1.2
        selected rewards s C (by omega) hmode
    have hintervalLen : (full.records.drop A).length = b - a := by
      rw [List.length_drop, hfullLen]
      dsimp [A, C]
      omega
    have hSinterval : S = full.records.drop A := by
      apply List.ext_getElem
      · rw [hSlen, hintervalLen]
      · intro j hjS hjI
        have hj : j < b - a := by
          have hjS' := hjS
          simp [S, List.length_take, List.length_drop] at hjS'
          exact hjS'.1
        have hjB : a + j < B.length := by omega
        have hSget : S[j]'hjS = B[a + j]'hjB := by
          simp [S, List.getElem_take, List.getElem_drop]
        have hBprefix := collectionWindow_isPrefix_drop E.records w
        have hBindex : w + (a + j) < E.records.length := by
          rw [hElen]
          omega
        have hBget : B[a + j]'hjB = E.records[w + (a + j)]'hBindex := by
          simpa [B, w, List.getElem_drop, Nat.add_assoc] using
            hBprefix.getElem hjB
        have hfullIndex : w + a + j < E.records.length := by
          rw [hElen]
          omega
        have hdropRecords : full.records.drop A = (E.records.take C).drop A :=
          congrArg (fun records : List (ReferenceActivePhysicalHorizon.RoundRecord
            (p := p) (rate := rate)) => records.drop A) hfullRecords
        have hrightBound : j < ((E.records.take C).drop A).length := by
          rw [← hdropRecords]
          exact hjI
        have hfullget : (full.records.drop A)[j]'hjI = E.records[w + a + j]'hfullIndex := by
          have hleft := List.getElem?_eq_getElem (l := full.records.drop A) (i := j) hjI
          have hoptEq := congrArg (fun records : List (ReferenceActivePhysicalHorizon.RoundRecord
            (p := p) (rate := rate)) => records[j]?) hdropRecords
          have hrightVal : ((E.records.take C).drop A)[j]'hrightBound =
              E.records[w + a + j]'hfullIndex := by
            simp [List.getElem_drop, List.getElem_take, A, C,
              Nat.add_left_comm, Nat.add_comm]
          have hright := List.getElem?_eq_getElem
            (l := (E.records.take C).drop A) (i := j) hrightBound
          exact Option.some.inj (hleft.symm.trans (hoptEq.trans
            (hright.trans (congrArg some hrightVal))))
        calc
          S[j]'hjS = B[a + j]'hjB := hSget
          _ = E.records[w + a + j]'hfullIndex := by
            simpa [Nat.add_assoc] using hBget
          _ = (full.records.drop A)[j]'hjI := hfullget.symm
    let hordinaryFull : full.finalState.coordinator ≠ .dagger := by
      exact hordinary b hb
    have hintervalBank := ReferenceCoordinatorUpIntervalWindow.run_interval_upDecoderBank_replay
      initial source.1.2 selected rewards s A C hhab hspanC hmode hinitial hordinaryFull i
    have hintervalBank' :
        full.finalState.upDecoderBank =
          ReferenceCoordinatorUpDecoderReplay.replay preRun.finalState.upDecoderBank
            (ReferenceCoordinatorUpDecoderReplay.retainedUpDiagnostics (full.records.drop A)) ∧
        AffineBatchDecoder.collected (full.finalState.upDecoderBank i) =
          AffineBatchDecoder.collected (preRun.finalState.upDecoderBank i) ++
            ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries (full.records.drop A) i := by
      simpa [preRun, full] using hintervalBank
    have hintervalBank'' := hintervalBank'
    rw [← hSinterval] at hintervalBank''
    have hfold := ReferenceCoordinatorUpIntervalWindow.run_interval_focal_decoder_fold
      initial source.1.2 selected rewards s A C hhab hspanC hmode hinitial hordinaryFull i
    have hfold' :
        AffineBatchDecoder.run p
          (ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace (full.records.drop A) i)
          ((full.records.drop A).map (fun record => record.input.time))
          (preRun.finalState.upDecoderBank i) = full.finalState.upDecoderBank i := by
      simpa [preRun, full] using hfold
    rw [← hSinterval] at hfold'
    have hroundChron := ReferenceCoordinatorUpIntervalWindow.run_interval_rounds_chronological
      initial source.1.2 selected rewards s A C hhab hspanC hmode hinitial hordinaryFull
    have hroundChron' :
        ((full.records.drop A).map (fun record => record.input.time)).Pairwise
          (fun x y => x.val < y.val) := by
      simpa [ReferenceCoordinatorUpIntervalWindow.intervalRounds,
        ReferenceCoordinatorUpIntervalWindow.intervalRecords, full] using hroundChron
    have htimesEq : times = (full.records.drop A).map
        (fun record => record.input.time) := by
      change S.map (fun record => record.input.time) = _
      rw [hSinterval]
    have htimes : times.Pairwise (fun x y => x.val < y.val) := by
      rw [htimesEq]
      exact hroundChron'
    have hrecordsChron : S.Pairwise
        (fun earlier later => earlier.input.time.val < later.input.time.val) := by
      have hmap := List.pairwise_map.mp htimes
      simpa [times, Function.comp_def] using hmap
    have hpositives := ReferenceCoordinatorUpIntervalWindow.actual_trace_positives_eq_retained
      S i hrecordsChron
    have hcut := ReferenceCoordinatorUpIntervalWindow.run_interval_cut
      initial source.1.2 selected rewards s A C hhab hspanC hmode hinitial hordinaryFull
    have hpreOrdinary : preRun.finalState.coordinator ≠ .dagger := hcut.2.2.2.2.1
    have hcollected := ReferenceCoordinatorUpDecoderReplay.run_collected_upPositiveEntries
      initial source.1.2 selected rewards s A hspanA hmode hinitial hpreOrdinary i
    have hchronology := ReferenceCoordinatorUpDecoderReplay.run_upPositiveEntries_chronology
      initial source.1.2 selected rewards s A hspanA hmode hinitial hpreOrdinary i
    have hentryCollected (e : AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p))
        (he : e ∈ (preRun.finalState.upDecoderBank i).pending) :
        e ∈ AffineBatchDecoder.collected (preRun.finalState.upDecoderBank i) := by
      change e ∈ (preRun.finalState.upDecoderBank i).completed.flatten ++
        (preRun.finalState.upDecoderBank i).pending
      exact List.mem_append_right _ he
    have horig (e : AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p))
        (he : e ∈ (preRun.finalState.upDecoderBank i).pending) :
        e ∈ ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries
          (E.records.take A) i := by
      have hcol := hentryCollected e he
      rw [hcollected, hseed] at hcol
      simp only [List.nil_append] at hcol
      rw [hpreRecords] at hcol
      exact hcol
    have horigTime (e : AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p))
        (he : e ∈ (preRun.finalState.upDecoderBank i).pending) :
        e.time.val < s + A := by
      have he' : e ∈ ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries
          preRun.records i := by
        simpa [hpreRecords] using horig e he
      exact (hchronology.2 e he').2
    have hseedInterval := ReferenceCoordinatorUpIntervalWindow.run_interval_pending_older_of_empty_seed
      initial source.1.2 selected rewards s A C hhab hspanC hmode hinitial hordinaryFull i (hseed i)
    have holder (e : AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p))
        (he : e ∈ (preRun.finalState.upDecoderBank i).pending)
        (t : Fin p.T) (ht : t ∈ times) : e.time.val < t.val := by
      have ht' : t ∈ ReferenceCoordinatorUpIntervalWindow.intervalRounds
          initial source.1.2 selected rewards s A C (by omega) hmode := by
        dsimp [times] at ht
        rw [hSinterval] at ht
        simpa [ReferenceCoordinatorUpIntervalWindow.intervalRounds,
          ReferenceCoordinatorUpIntervalWindow.intervalRecords, full] using ht
      exact hseedInterval e he t ht'
    have hwellA : CoordinatorUpReception.decoderBankWellFormed p
        (preRun.finalState.upDecoderBank) := by
      have ha : a ≤ out.ell := by omega
      have hInv := hrunInvariant a ha
      have hInv' : ReferenceUpDecoderBankInvariant.upBankInvariant preRun.finalState := by
        simpa [X, preRun, A] using hInv
      change ReferenceUpDecoderBankInvariant.coordinatorBankInvariant
        preRun.finalState.coordinator preRun.finalState.upDecoderBank at hInv'
      exact hInv'.1
    refine ⟨?_, ?_, ?_, ?_, htimes, (hwellA i).1, ?_⟩
    · change full.finalState.upDecoderBank =
        ReferenceCoordinatorUpDecoderReplay.replay preRun.finalState.upDecoderBank
          (ReferenceCoordinatorUpDecoderReplay.retainedUpDiagnostics S)
      exact hintervalBank''.1
    · change AffineBatchDecoder.run p tr times (preRun.finalState.upDecoderBank i) =
        full.finalState.upDecoderBank i
      exact hfold'
    · change AffineBatchDecoder.collected (full.finalState.upDecoderBank i) =
        AffineBatchDecoder.collected (preRun.finalState.upDecoderBank i) ++
          ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries S i
      exact hintervalBank''.2
    · change AffineBatchDecoder.positives p tr times =
        ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries S i
      exact hpositives
    · intro e he
      exact ⟨horig e he, by simpa [A, Nat.add_assoc] using horigTime e he, holder e he⟩
  refine ⟨d, registers, owned, base, cutRecord, hcutIndex, hcutState,
    hpayload, hpending, hBpos, hBzero, hcutoff, ?_, ?_⟩
  · change (w + out.ell ≤ count) ∧ _
    exact ⟨hlen, ⟨hEndpoint,
      ⟨(by
          intro t ht
          exact ⟨hrunInvariant t ht, hordinary t ht⟩),
        ⟨hzeroPending, hAllBanks⟩⟩⟩⟩
  · intro n hn i hi
    obtain ⟨r, incoming, cell, state, memory, hr, htime, hrows, hselected,
      hrewards, hincoming, hiPending, hready, hservice, hstate, hstatus,
      hvalid, hS, hdelta, hbacklog, hsum, hquota, hcompleted, hlast, hformed⟩ :=
        hboundaries n hn i hi
    refine ⟨r, incoming, cell, state, memory, hr, htime, hrows, hselected,
      hrewards, hincoming, hiPending, hready, hservice, hstate, hstatus,
      hvalid, hS, hdelta, hbacklog, hsum, hquota, hcompleted, hlast, ?_⟩
    intro hlastDown
    obtain ⟨U, hUfields, hUsigma, hUpositive, hUoffer, hDownsigma, haccepted,
      j, hjIndex, acceptedRecord, hjbefore, hjrecord, hretained, hacceptedCut,
      hatime, harows, haselected, harewards, hunique, hinterval⟩ := hformed hlastDown
    let f := if j < w then 0 else j - w + 1
    obtain ⟨hf, hfn, hftime, hfzero, hfone, hpendingMono, hchoices⟩ := hinterval
    refine ⟨U, hUfields, hUsigma, hUpositive, hUoffer, hDownsigma, haccepted,
      j, hjIndex, acceptedRecord, hjbefore, hjrecord, hretained, hacceptedCut,
      hatime, harows, haselected, harewards, hunique, hf, hfn, hftime,
      hfzero, hfone, hpendingMono, ?_, hchoices⟩
    intro b hfb hbn
    have hb : b ≤ out.ell := Nat.le_trans hbn n.isLt
    exact hAllBanks i f b hfb hb

end Bandits.Support.ReferenceFirstCollectionFormedUpBankReplay

end
