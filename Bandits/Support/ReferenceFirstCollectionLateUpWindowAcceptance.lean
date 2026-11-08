/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionLateUpSecondWindow

/-!
# Actual late first-collection saved-window acceptance

Sources: `sources/zip4/manuscript/05_binary_transport.tex:20-53`,
`sources/zip4/manuscript/06_interruptions.tex:164-177,277-295,327-348`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:92-109,151-157`.

The original source and whole reward grid determine all runs and records.
The local ordinary-coordinator and exact positive-count conditions are explicit;
uniqueness concerns the entire actual second window. These internal results
compose deterministic acceptance and do not assert service attainment or a
probabilistic decoder event. The next consumer is the late first-collection
2Q delivery bound, followed by original-source UP truth.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon

namespace Bandits.Support.ReferenceFirstCollectionLateUpWindowAcceptance

local instance propDecidable (q : Prop) : Decidable q := Classical.propDecidable q

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

private theorem run_prefix_records
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start total : ℕ) (hspan : start + total ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (n : ℕ) (hn : n ≤ total) :
    (ReferenceActivePhysicalHorizon.run initial rows selected rewards start total hspan active).records.take n =
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start n
        (by omega) active).records := by
  revert hspan hn
  induction total with
  | zero =>
      intro hspan hn
      have hn0 : n = 0 := by omega
      subst n
      rw [List.take_zero, ReferenceActivePhysicalHorizon.run_zero_records]
  | succ total ih =>
      intro hspan hn
      by_cases heq : n = total + 1
      · subst n
        apply List.take_of_length_le
        rw [ReferenceActivePhysicalHorizon.run_record_count]
      · have hn' : n ≤ total := by omega
        rw [ReferenceAssignmentPayloadChronology.run_successor_actualRunRecordAt,
          List.take_append_of_le_length (by
            rw [ReferenceActivePhysicalHorizon.run_record_count]
            exact hn')]
        exact ih (by omega) hn'

private theorem interval_eq_window_take
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start total : ℕ) (hspan : start + total ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (b n : ℕ) (hbound : b + n ≤ total)
    (hn : n ≤ (((ReferenceActivePhysicalHorizon.run initial rows selected rewards
      start total hspan active).records.drop b).takeWhile
        (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)).length) :
    (ReferenceActivePhysicalHorizon.run initial rows selected rewards start (b + n)
      (by omega) active).records.drop b =
      (((ReferenceActivePhysicalHorizon.run initial rows selected rewards start total
        hspan active).records.drop b).takeWhile
          (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)).take n := by
  let records := (ReferenceActivePhysicalHorizon.run initial rows selected rewards
    start total hspan active).records
  let window := (records.drop b).takeWhile
    (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
  change n ≤ window.length at hn
  have hwindow : window.take n = (records.drop b).take n := by
    have hp : window.take n <+: (records.drop b).take n :=
      (List.takeWhile_prefix _).take n
    rw [List.prefix_iff_eq_take.mp hp]
    simp only [List.length_take, Nat.min_eq_left hn, List.take_take, Nat.min_self]
  rw [← run_prefix_records initial rows selected rewards start total hspan active
    (b + n) hbound, List.drop_take]
  simpa only [Nat.add_sub_cancel_left] using hwindow.symm

/-- Every actual positive entry retains its original UP call, selected label,
physical positive test, and full-table affine sample. -/
private theorem positive_entry_record
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (i : Fin (p.m - 1))
    (hchronological : records.Pairwise
      (fun earlier later => earlier.input.time.val < later.input.time.val))
    (entry : AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p))
    (hentry : entry ∈ AffineBatchDecoder.positives p
      (ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace records i)
      (records.map (fun r => r.input.time))) :
    ∃ (q : Fin records.length) (d : ReferenceActivePhysicalStep.UpDiagnostic p rate),
      let r := records[q.val]
      r.input.time = entry.time ∧ r.output.coordinator.up = some d ∧
      d.input.selectedFollower = i ∧
      AffineBatchDecoder.eligible (CoordinatorUpReception.roundInput d.input) ∧
      PublicDiscreteDraws.slotDraw (r.input.row.2 r.input.time).1 = PublicDiscreteDraws.upSlot ∧
      PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
        (r.input.row.2 r.input.time).1 = i ∧
      ReferenceActiveAffinePositiveTest.upPositive r.input = true ∧
      entry.sample = (r.input.row.2 r.input.time).2 (1, i) := by
  classical
  let trace := ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace records i
  obtain ⟨htime, heligible, hsample⟩ :=
    (AffineBatchDecoder.mem_positives_iff p trace _ entry).mp hentry
  obtain ⟨r, hr, htime⟩ := List.mem_map.mp htime
  obtain ⟨q, hq, hget⟩ := List.mem_iff_getElem.mp hr
  have htrace := ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace_at_record
    records i hchronological r hr
  have hfocal : AffineBatchDecoder.eligible
      (ReferenceCoordinatorUpIntervalWindow.recordFocalInput r i) := by
    rw [← htrace, htime]
    exact heligible
  obtain ⟨d, hd, hi⟩ : ∃ d, r.output.coordinator.up = some d ∧
      d.input.selectedFollower = i := by
    cases hcall : r.output.coordinator.up with
    | none =>
        simp [ReferenceCoordinatorUpIntervalWindow.recordFocalInput, hcall,
          ReferenceCoordinatorUpIntervalWindow.administrativeNoCallInput,
          AffineBatchDecoder.eligible] at hfocal
    | some d =>
        by_cases hi : d.input.selectedFollower = i
        · exact ⟨d, rfl, hi⟩
        · simp [ReferenceCoordinatorUpIntervalWindow.recordFocalInput, hcall, hi,
            ReferenceCoordinatorUpDecoderReplay.retainedUpRoundInput,
            AffineBatchDecoder.eligible] at hfocal
  have htraceInput : trace r.input.time = CoordinatorUpReception.roundInput d.input := by
    change trace r.input.time = _ at htrace
    rw [htrace]
    simp only [ReferenceCoordinatorUpIntervalWindow.recordFocalInput, hd, hi,
      ReferenceCoordinatorUpDecoderReplay.retainedUpRoundInput, ite_true]
  have hround : AffineBatchDecoder.eligible (CoordinatorUpReception.roundInput d.input) := by
    rw [← htraceInput, htime]
    exact heligible
  obtain ⟨ledger, _hsite, _hledger, _hbank, _htime, _hobs, hindex,
      hactualSample, hslot, _henabled, hselectedFlag, hroundSample, _hreward,
      _hfeedback⟩ :=
    ReferenceCoordinatorUpPhysicalCall.record_retained_up_input_fields r d hd
  have hgate : ledger.cutoff ≤ r.input.time.val + 1 ∧
      d.input.slot = PublicDiscreteDraws.upSlot ∧
      d.input.selectedFollower ∈ ledger.pending := by
    have hs := hround.1
    rw [hselectedFlag] at hs
    exact of_decide_eq_true hs
  have hslotDraw : PublicDiscreteDraws.slotDraw (r.input.row.2 r.input.time).1 =
      PublicDiscreteDraws.upSlot := hslot.symm.trans hgate.2.1
  have hdraw : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
      (r.input.row.2 r.input.time).1 = i := by
    rw [← CoordinatorUpMeasurability.selectedFollowerIndex_eq_draw]
    exact hindex.symm.trans hi
  have hchannel : CoordinatorUpMeasurability.selectedChannelFollower
      ((r.input.rows r.input.selected).2 r.input.time) = i := by
    apply Fin.ext
    rw [CoordinatorUpMeasurability.selectedChannelFollower_val,
      ← CoordinatorUpMeasurability.selectedFollowerIndex_eq_draw]
    simpa only [ContinuousLearningRows.d] using congrArg Fin.val (hindex.symm.trans hi)
  have hsampleEq : entry.sample = (r.input.row.2 r.input.time).2 (1, i) := by
    rw [hsample, ← htime, htraceInput, hroundSample, hactualSample, hchannel]
    rfl
  have hpositive : ReferenceActiveAffinePositiveTest.upPositive r.input = true := by
    rw [ReferenceActiveAffinePositiveTest.record_upPositive]
    simpa only [ReferenceActiveAffinePositiveTest.upDiagnosticPositive, hd,
      decide_eq_true_eq] using hround
  refine ⟨⟨q, hq⟩, d, ?_⟩
  dsimp only
  rw [hget]
  exact ⟨htime, hd, hi, hround, hslotDraw, hdraw, hpositive, hsampleEq⟩

/-- Pointwise actual sender equalities imply equations only for the actual
positive calls. In the main theorem the pointwise inputs are produced by A. -/
private theorem positive_entries_word_truth
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (i : Fin (p.m - 1))
    (U : OrdinaryMessageCodec.UpRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (hchronological : records.Pairwise
      (fun earlier later => earlier.input.time.val < later.input.time.val))
    (hsender : ∀ (q : Fin records.length),
      let r := records[q.val]
      PublicDiscreteDraws.slotDraw (r.input.row.2 r.input.time).1 = PublicDiscreteDraws.upSlot →
      PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
        (r.input.row.2 r.input.time).1 = i →
      ReferenceActiveAffinePositiveTest.upSent r.input =
        some (ActiveFollowerArmChoice.offeredUpWord rate.eta U) ∧
      ReferenceActivePhysicalStep.upExpected (ReferenceActivePhysicalStep.prepare r.input) =
        some (ActiveFollowerArmChoice.offeredUpWord rate.eta U)) :
    ∀ entry, entry ∈ AffineBatchDecoder.positives p
        (ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace records i)
        (records.map (fun r => r.input.time)) →
      ∃ (original : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
        (d : ReferenceActivePhysicalStep.UpDiagnostic p rate),
        original ∈ records ∧ original.input.time = entry.time ∧
        AffineBatchDecoder.equation entry.sample
          (ActiveFollowerArmChoice.offeredUpWord rate.eta U) ∧
        ReferenceActivePhysicalStep.upExpected (ReferenceActivePhysicalStep.prepare original.input) =
          some (ActiveFollowerArmChoice.offeredUpWord rate.eta U) ∧
        original.output.coordinator.up = some d ∧ d.input.selectedFollower = i ∧
        AffineBatchDecoder.eligible (CoordinatorUpReception.roundInput d.input) ∧
        PublicDiscreteDraws.slotDraw (original.input.row.2 original.input.time).1 =
          PublicDiscreteDraws.upSlot ∧
        PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
          (original.input.row.2 original.input.time).1 = i := by
  intro entry hentry
  obtain ⟨q, d, htime, hup, hselected, heligible, hslot, hdraw,
      hpositive, hsample⟩ := positive_entry_record records i hchronological entry hentry
  have hoff := hsender q hslot hdraw
  have hsenderIndex : ReferenceActivePhysicalStep.upSenderIndex (records[q.val]).input = i := by
    rw [ReferenceActiveAffinePositiveTest.upSenderIndex_eq_draw, hdraw]
  have hhash := ReferenceUpPhysicalHashRule.upPositive_hash_one (records[q.val]).input
    (ActiveFollowerArmChoice.offeredUpWord rate.eta U) hoff.1 hpositive
  rw [hsenderIndex] at hhash
  have hequation : AffineBatchDecoder.equation entry.sample
      (ActiveFollowerArmChoice.offeredUpWord rate.eta U) := by
    rw [hsample]
    exact (AffineBatchDecoder.equation_iff_affineHash _ _).2 hhash
  exact ⟨records[q.val], d, List.getElem_mem q.isLt, htime, hequation, hoff.2,
    hup, hselected, heligible, hslot, hdraw⟩

/-- The original late retained DOWN produces a single reply before all prefix
queries. On its ordinary endpoint branch, the actual saved second batch
solves that reply; local uniqueness yields successful checked reception. -/
theorem actual_first_collection_late_up_window_acceptance
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
    let x0 := ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate
    let b0 := ReferenceInitializationRun.output x0
    let s := ReferenceInitializationRun.elapsed p b0.completed
    let I := ReferenceFirstCollectionEpochAlignment.actualLaunchState
      rate source rewards C_star C_h hcross
    let active := (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
      rate source rewards C_star C_h hcross).1
    let E := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
      rate source rewards C_star C_h hcross count hspan
    let W := ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records
    let w := W.length
    let B := ReferenceCollectionPhaseHistory.collectionWindow E.records w
    let u := s + w + 1
    ∃ (cutoffRecord : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
      (suffix : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
      (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
      (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
      (base : Fin (p.m - 1) → ℕ)
      (P0 : ReferenceActivePhysicalStep.Payload rate)
      (birth : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)),
      E.records = W ++ cutoffRecord :: suffix ∧
      (∃ hindex : w < E.records.length,
        cutoffRecord = E.records[w]'hindex) ∧
      cutoffRecord.input.time.val = s + w ∧
      cutoffRecord.input.state.coordinator = .live registers owned base ∧
      ReferenceCollectionPhaseHistory.cutoffChosen cutoffRecord.input = true ∧
      P0 = registers.payload ∧ P0.sigma.val = s ∧
      (∀ arm, P0.queues arm = 0) ∧
      FollowerCutoffScan.firstCutoff p rate.eta.val P0.sigma
        (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
          (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source))) = u ∧
      birth ∈ E.records ∧
      ReferenceAssignmentPayloadPersistence.InstallationBirth birth P0 ∧
      birth.input.time.val = s ∧
      (∀ k : Fin B.length,
        E.records[w + k.val]? = some B[k.val] ∧
          B[k.val].input.time.val + 1 = u + k.val) ∧
      ∀ (k : Fin B.length) (i : Fin (p.m - 1))
        (M : ReferenceAcceptedUpFollowerHistory.DownRecord (p := p) (rate := rate)),
        let j := w + k.val
        let r := B[k.val]
        ReferenceAcceptedUpFollowerHistory.RetainedDown r i M →
        r.output.next.followers i = .dagger ∨
        r.output.next.coordinator = .dagger ∨
        ∃ (out : ReferencePrelaunchFollower.State p rate.eta)
          (memory : ActiveFollowerLifecycle.LocalMemory p)
          (l0 : ReferenceActivePhysicalStep.Ledger rate)
          (saved : Option (Fin p.T × Bool)),
          r.output.next.followers i = .ordinary out memory ∧
          r.output.next.coordinator = .collection P0 l0 saved ∧
          out.status = .unoccupied ∧
          let V := fun h => QueueReplay.replay (4 * rate.n) (0, 0)
            (ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords E.records i j M h)
          ReferenceFollowerReplyChronology.reply out =
            (some M, (V w).1, (V w).1 - (V (w - 1)).1, (V w).2) ∧
          M = P0.downRecord i ∧ M.val.sigma = s + 1 ∧
          (∃ (logged : ReferencePrelaunchFollower.State p rate.eta)
            (cutD : ReferenceDownReception.ReferenceDownCutOutput p rate)
            (after : ReferencePrelaunchFollower.State p rate.eta)
            (raw : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p)))
            (scan : FollowerCutoffScan.ScanResult p.T)
            (replayedRegisters : ℕ × ℕ) (lastService : ℕ),
            cutD.outcome = .accepted logged after raw M scan replayedRegisters lastService ∧
            j < count ∧ ∃ (n0 : ℕ),
              n0 = scan.endpoint - M.val.sigma ∧ n0 = w ∧
              ActiveFollowerDownAcceptance.checkedRecovery p rate M logged scan.endpoint =
                .ok ⟨replayedRegisters, lastService⟩) ∧
          out.lastDown = some M ∧
          ReferencePrelaunchFollower.acceptedStart out = s + 1 ∧
          let b := j + 1
          let Wlate := (E.records.drop b).takeWhile
            (fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input)
          ∃ (hb : b ≤ count) (hbspan : s + b ≤ p.T)
            (hlate : Wlate.length ≤ count - b),
            let C := fun (h : ℕ) (hh : h ≤ Wlate.length) =>
              ReferenceActivePhysicalHorizon.run I source.1.2
                (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s (b + h)
                (by
                  have hbound : b + h ≤ count := by omega
                  have hstart : s + count ≤ p.T := by
                    dsimp only [s, b0, x0]
                    exact hspan
                  omega) active
            (ReferenceActivePhysicalHorizon.run I source.1.2
              (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s b
              hbspan active).finalState = r.output.next ∧
            Wlate = B.drop (k.val + 1) ∧
            (∀ h (hh : h < Wlate.length),
              E.records[b + h]? = some (Wlate[h]'hh) ∧
                (Wlate[h]'hh).input.time.val = u + k.val + h) ∧
            (∀ h (hh : h ≤ Wlate.length),
              ((C h hh).finalState.coordinator = .dagger ∨
                ∃ moving movingSaved,
                  (C h hh).finalState.coordinator = .collection P0 moving movingSaved) ∧
              ((C h hh).finalState.followers i = .dagger ∨
                ∃ state stateMemory,
                  (C h hh).finalState.followers i = .ordinary state stateMemory ∧
                  state.status = .unoccupied ∧
                  ReferenceFollowerReplyChronology.reply state =
                    (some M, (V w).1, (V w).1 - (V (w - 1)).1, (V w).2))) ∧
            (∀ h (_hh : h < Wlate.length) (hrecord : b + h < E.records.length),
              ∀ start,
                ¬ ReferenceFollowerReplyChronology.appliedDown
                  (E.records.get ⟨b + h, hrecord⟩) i start) ∧
            (∀ h (_hh : h ≤ Wlate.length) (hrecord : b + h < E.records.length),
              (h = Wlate.length →
                ReferenceCollectionPhaseHistory.laterChosen
                  ((E.records.get ⟨b + h, hrecord⟩).input) = true) ∧
              ((ReferenceFollowerFixedReply.actualChoice
                  (E.records.get ⟨b + h, hrecord⟩) i).configuration = .dagger ∨
                ∃ state stateMemory,
                  (ReferenceFollowerFixedReply.actualChoice
                    (E.records.get ⟨b + h, hrecord⟩) i).configuration =
                      .ordinary state stateMemory ∧
                  state.status = .unoccupied ∧
                  ReferenceFollowerReplyChronology.reply state =
                    (some M, (V w).1, (V w).1 - (V (w - 1)).1, (V w).2))) ∧
            ∃ (U : OrdinaryMessageCodec.UpRecord
              (ReferencePrelaunchFollower.codecParams p rate.eta)),
              U.val = ActiveFollowerQueueOperation.upOfferFields out ∧
              U.val = OrdinaryMessageCodec.UpFields.mk (s + 1)
                (V w).1 ((V w).1 - (V (w - 1)).1) (V w).2 ∧
              0 < U.val.sigma ∧
              l0.sigma = s + 1 ∧ i ∈ l0.pending ∧
              (∀ h (hh : h ≤ Wlate.length),
                (C h hh).finalState.coordinator = .dagger ∨
                ∃ moving proposal,
                  (C h hh).finalState.coordinator = .collection P0 moving proposal ∧
                  moving.sigma = s + 1 ∧
                  moving.pending = l0.pending \
                    (ReferenceCollectionPhaseHistory.acceptedLabels (Wlate.take h)).toFinset ∧
                  (i ∈ moving.pending ↔ i ∉
                    (ReferenceCollectionPhaseHistory.acceptedLabels (Wlate.take h)).toFinset)) ∧
              ∀ n (_hn : n ≤ Wlate.length),
                ∃ hspan_n : s + (b + n) ≤ p.T,
                let Cn := ReferenceActivePhysicalHorizon.run I source.1.2
                  (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s (b + n)
                  hspan_n active
                (Cn.finalState.coordinator = .dagger ∨
                  ∃ moving movingSaved,
                    Cn.finalState.coordinator = .collection P0 moving movingSaved) ∧
                (Cn.finalState.followers i = .dagger ∨
                  ∃ endpoint endpointMemory,
                    Cn.finalState.followers i = .ordinary endpoint endpointMemory ∧
                    endpoint.status = .unoccupied ∧
                    ReferenceFollowerReplyChronology.reply endpoint =
                      ReferenceFollowerReplyChronology.reply out ∧
                    (Cn.finalState.coordinator ≠ .dagger →
                      let preRun := ReferenceActivePhysicalHorizon.run I source.1.2
                        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s b
                        ((Nat.add_le_add_left (Nat.le_add_right b n) s).trans hspan_n) active
                      let full := Cn
                      let interval := full.records.drop b
                      let trace := ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace interval i
                      let rounds := ReferenceCoordinatorUpIntervalWindow.intervalRounds I source.1.2
                        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s b (b + n)
                        hspan_n active
                      let positive := AffineBatchDecoder.positives p trace rounds
                      let channel := preRun.finalState.upDecoderBank i
                      let window := positive.drop (AffineBatchDecoder.quota p - channel.pending.length)
                      positive.length = AffineBatchDecoder.quota p - channel.pending.length +
                        AffineBatchDecoder.quota p →
                      ∃ (first : List (AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p)))
                        (last : AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p))
                        (index : Fin rounds.length)
                        (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
                        (diagnostic : ReferenceActivePhysicalStep.UpDiagnostic p rate),
                        let before := AffineBatchDecoder.run p trace (rounds.take index.val) channel
                        first = channel.pending ++ positive.take
                            (AffineBatchDecoder.quota p - channel.pending.length) ∧
                        first.length = AffineBatchDecoder.quota p ∧
                        window.length = AffineBatchDecoder.quota p ∧
                        window.Pairwise (fun (earlier later :
                            AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p)) =>
                              earlier.time.val < later.time.val) ∧
                        last ∈ window ∧
                        AffineBatchDecoder.decisionTime window = some last.time ∧
                        rounds.get index = last.time ∧
                        record ∈ interval ∧
                        record.input.time = last.time ∧
                        record.output.coordinator.up = some diagnostic ∧
                        diagnostic.input.selectedFollower = i ∧
                        diagnostic.input.time = record.input.time ∧
                        last = AffineBatchDecoder.entry p trace last.time ∧
                        last.sample = ((record.input.rows record.input.selected).2 record.input.time).2
                          (1, CoordinatorUpMeasurability.selectedChannelFollower
                            ((record.input.rows record.input.selected).2 record.input.time)) ∧
                        (∃ ledger,
                          ReferenceCoordinatorUpPhysicalCall.siteLedger? (x := record.input) = some ledger ∧
                          CoordinatorUpReception.receptionInputCheck
                            (ReferenceCoordinatorUpPhysicalCall.actualUpInput record.input ledger) = true ∧
                          diagnostic.input = ReferenceCoordinatorUpPhysicalCall.actualUpInput record.input ledger ∧
                          diagnostic.decoderAfter = (CoordinatorUpReception.decoderTransition
                            (ReferenceCoordinatorUpPhysicalCall.actualUpInput record.input ledger)).1 ∧
                          diagnostic.input.time = record.input.time ∧
                          diagnostic.input.selectedFollower =
                            CoordinatorUpMeasurability.selectedFollowerIndex
                              ((record.input.rows record.input.selected).2 record.input.time) ∧
                          diagnostic.input.affineSample =
                            ((record.input.rows record.input.selected).2 record.input.time).2
                              (1, CoordinatorUpMeasurability.selectedChannelFollower
                                ((record.input.rows record.input.selected).2 record.input.time)) ∧
                          diagnostic.input.ownObservation =
                            (ReferenceActivePhysicalStep.prepare record.input).feedback.feedback
                              (ActiveRoundActions.coordinator p.two_le_m) ∧
                          (ReferenceActivePhysicalStep.prepare record.input).feedback.feedback
                              (ActiveRoundActions.coordinator p.two_le_m) =
                            (if FiniteBanditModel.collisionFreeFor
                                (ReferenceActivePhysicalStep.prepare record.input).arms.actions
                                  (ActiveRoundActions.coordinator p.two_le_m) then
                              record.input.rewards record.input.time
                                ((ReferenceActivePhysicalStep.prepare record.input).arms.actions
                                  (ActiveRoundActions.coordinator p.two_le_m))
                            else 0) ∧
                          (ReferenceCoordinatorUpDecoderReplay.retainedUpRoundInput diagnostic).receiverEnabled = true ∧
                          (ReferenceCoordinatorUpDecoderReplay.retainedUpRoundInput diagnostic).sample =
                            diagnostic.input.affineSample ∧
                          (ReferenceCoordinatorUpDecoderReplay.retainedUpRoundInput diagnostic).roundedReward =
                            CoordinatorUpReception.roundedObservationValue p diagnostic.input.ownObservation ∧
                          (AffineBatchDecoder.eligible
                            (ReferenceCoordinatorUpDecoderReplay.retainedUpRoundInput diagnostic) ↔
                            CoordinatorUpReception.receptionGate diagnostic.input ∧
                              0 < CoordinatorUpReception.roundedObservationValue p diagnostic.input.ownObservation) ∧
                          record.output.ownEntries (ActiveRoundActions.coordinator p.two_le_m) =
                            (record.output.preparation.arms.actions
                              (ActiveRoundActions.coordinator p.two_le_m),
                             ActualInitializationPhysicalStep.observationOfGrid p
                              (record.output.preparation.feedback.feedback
                                (ActiveRoundActions.coordinator p.two_le_m)))) ∧
                        ReferenceActivePhysicalHorizon.Connected preRun.finalState
                          (interval.take index.val) record.input.state ∧
                        record.input.state.upDecoderBank =
                          ReferenceCoordinatorUpDecoderReplay.replay preRun.finalState.upDecoderBank
                            (ReferenceCoordinatorUpDecoderReplay.retainedUpDiagnostics
                              (interval.take index.val)) ∧
                        diagnostic.input.upDecoderBank = record.input.state.upDecoderBank ∧
                        before = diagnostic.input.upDecoderBank i ∧
                        before.pending ++ [AffineBatchDecoder.entry p trace last.time] = window ∧
                        (CoordinatorUpReception.decoderTransition diagnostic.input).1.pending = [] ∧
                        (CoordinatorUpReception.decoderTransition diagnostic.input).1.completed =
                          channel.completed ++ [first, window] ∧
                        diagnostic.decoderAfter = (CoordinatorUpReception.decoderTransition diagnostic.input).1 ∧
                        diagnostic.raw = (CoordinatorUpReception.decoderTransition diagnostic.input).2 ∧
                        diagnostic.raw = AffineBatchDecoder.batchOutput window ∧
                        CoordinatorUpReception.decoderTransition diagnostic.input =
                          (⟨[], channel.completed ++ [first, window]⟩,
                            AffineBatchDecoder.batchOutput window) ∧
                        AffineBatchDecoder.run p trace rounds channel =
                          ⟨[], channel.completed ++ [first, window]⟩ ∧
                        AffineBatchDecoder.run p trace rounds channel = full.finalState.upDecoderBank i ∧
                      (∀ entry, entry ∈ window →
                        AffineBatchDecoder.equation entry.sample
                          (ActiveFollowerArmChoice.offeredUpWord rate.eta U)) ∧
                      AffineBatchDecoder.satisfies (AffineBatchDecoder.samples window)
                        (ActiveFollowerArmChoice.offeredUpWord rate.eta U) ∧
                      ((∃! word, AffineBatchDecoder.satisfies
                          (AffineBatchDecoder.samples window) word) →
                        diagnostic.raw = some (ActiveFollowerArmChoice.offeredUpWord rate.eta U) ∧
                        diagnostic.expected = some (ActiveFollowerArmChoice.offeredUpWord rate.eta U) ∧
                        ∃ (tail : ReferenceCollectionPhaseHistory.Tail record.input)
                          (pre : ReferenceActivePhysicalStep.Ledger rate)
                          (preSaved : Option (Fin p.T × Bool))
                          (Lsite : ReferenceActivePhysicalStep.Ledger rate),
                          record.input.state.coordinator = .collection P0 pre preSaved ∧
                          pre.pending = l0.pending \
                            (ReferenceCollectionPhaseHistory.acceptedLabels
                              (Wlate.take index.val)).toFinset ∧
                          ReferenceCollectionPhaseHistory.executedTail record.input = some tail ∧
                          ReferenceCoordinatorUpPhysicalCall.siteLedger? (x := record.input) = some Lsite ∧
                          diagnostic.input = ReferenceCoordinatorUpPhysicalCall.actualUpInput
                            record.input Lsite ∧
                          i ∈ pre.pending ∧ i ∈ Lsite.pending ∧
                          CoordinatorCollectionLedger.acceptUpCheck Lsite i U = true ∧
                          ReferenceCollectionPhaseHistory.filteredParsed record.input Lsite = some U ∧
                          diagnostic.parsed = some U ∧ diagnostic.locallyAccepted = true ∧
                          diagnostic.rawMatches = true ∧ diagnostic.wrongUniqueAccepted = false ∧
                          ∃ (decoded : ReferenceActivePhysicalStep.Ledger rate)
                            (bank : CoordinatorUpReception.UpDecoderBank p),
                            (ReferenceActivePhysicalStep.receiveUp
                              (ReferenceActivePhysicalStep.prepare record.input) Lsite).result =
                                .success (decoded, bank) ∧
                            ReferenceCollectionPhaseHistory.AcceptedUp record.input i U))) := by
  classical
  intro x0 b0 s I active E W w B u
  obtain ⟨cutoffRecord, suffix, registers, owned, base, P0, birth,
      hsplit, hindex, htime, hstate, hcutoff, hP0, hP0sigma, hqueues,
      hfirstCutoff, hbirth, hbirthInstall, hbirthTime, hwindow, hqueries⟩ :=
    ReferenceFirstCollectionLateUpSender.actual_first_collection_late_up_sender
      rate source rewards C_star C_h count hcross hspan hshort
  obtain ⟨cutoffB, _suffixB, registersB, _ownedB, _baseB, P0B, _birthB,
      _hsplitB, hindexB, _htimeB, hstateB, _hcutoffB, hP0B, _hP0sigmaB,
      _hqueuesB, _hfirstCutoffB, _hbirthB, _hbirthInstallB, _hbirthTimeB,
      _hwindowB, hqueriesB⟩ :=
    ReferenceFirstCollectionLateUpReceiverEligibility.actual_first_collection_late_up_receiver_eligibility
      rate source rewards C_star C_h count hcross hspan hshort
  have hcutoffEq : cutoffB = cutoffRecord := by
    obtain ⟨ha, heqa⟩ := hindex
    obtain ⟨hb, heqb⟩ := hindexB
    exact heqb.trans heqa.symm
  rw [hcutoffEq] at hstateB
  have hregistersEq : registersB = registers :=
    (ReferenceActivePhysicalStep.CoordinatorConfiguration.live.inj
      (hstateB.symm.trans hstate)).1
  have hpayloadEq : P0B = P0 := by
    rw [hP0B, hregistersEq, ← hP0]
  refine ⟨cutoffRecord, suffix, registers, owned, base, P0, birth,
    hsplit, hindex, htime, hstate, hcutoff, hP0, hP0sigma, hqueues,
    hfirstCutoff, hbirth, hbirthInstall, hbirthTime, hwindow, ?_⟩
  intro k i M j r hretained
  rcases hqueries k i M hretained with hdagger | hdagger | hordinary
  · exact Or.inl hdagger
  · exact Or.inr (Or.inl hdagger)
  · rcases hordinary with ⟨out, memory, l0, saved, hfollower, hcoordinator,
        hstatus, hreply, hM, hMsigma, hrecover, hlastDown, hstart,
        hb, hbspan, hlate, hprefix, hWlate, hlookup, hprefixFacts,
        hnoDown, hboundary, U, hUfields, hUnumeric, hUpositive, hsenderQueries⟩
    let V := fun h => QueueReplay.replay (4 * rate.n) (0, 0)
      (ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords E.records i j M h)
    let b := j + 1
    let Wlate := (E.records.drop b).takeWhile
      (fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input)
    have hqueryB := hqueriesB k i M hretained
    rw [hpayloadEq] at hqueryB
    obtain ⟨_loggedB, _cutDB, _afterB, _rawB, _scanB, _replayedB, _lastServiceB,
        _hinputB, _hdownB, _hacceptedB, _hMB, _hMsigmaB, _hMqB, _hdownStartB,
        _hscanB, _hafterStatusB, _hafterLastB, _hrecoveryB,
        _hreplayedB, _hlastServiceB, _hafterSB, _hafterDeltaB, _hafterBacklogB,
        _hafterReplyB, hnextB⟩ := hqueryB
    rcases hnextB with ⟨hdagger, _⟩ | ⟨outB, memoryB, hfollowerB, _hstatusB,
        _hreplyB, _hlastDownB, _hSB, _hDeltaB, _hBacklogB, _hstartB, hcoordB⟩
    · rw [hfollower] at hdagger
      cases hdagger
    have houtEq := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
      (hfollowerB.symm.trans hfollower)
    have _houtBEq : outB = out := houtEq.1
    have _hmemoryBEq : memoryB = memory := houtEq.2
    rcases hcoordB with hdagger | ⟨l0B, savedB, hcoordB, hsigma0, hipending0,
        _hbB, _hbspanB, _hprefixB, _hWlateB, _hlookupB, hmovement, hreceiver⟩
    · rw [hcoordinator] at hdagger
      cases hdagger
    have hledgerEq := ReferenceActivePhysicalStep.CoordinatorConfiguration.collection.inj
      (hcoordB.symm.trans hcoordinator)
    have hl0BEq : l0B = l0 := hledgerEq.2.1
    have _hsavedBEq : savedB = saved := hledgerEq.2.2
    rw [hl0BEq] at hsigma0 hipending0 hmovement hreceiver
    refine Or.inr (Or.inr ⟨out, memory, l0, saved, hfollower, hcoordinator,
      hstatus, hreply, hM, hMsigma, hrecover, hlastDown, hstart, hb, hbspan,
      hlate, hprefix, hWlate, hlookup, hprefixFacts, hnoDown, hboundary,
      U, hUfields, hUnumeric, hUpositive, hsigma0, hipending0, hmovement, ?_⟩)
    intro n hn
    have hbLocal : b ≤ count := hb
    have hlateLocal : Wlate.length ≤ count - b := hlate
    have hbound : b + n ≤ count := by
      have hrest : n ≤ count - b := Nat.le_trans hn hlateLocal
      simpa only [Nat.add_comm] using Nat.add_le_of_le_sub hbLocal hrest
    have hstartSpan : s + count ≤ p.T := hspan
    have hspan_n : s + (b + n) ≤ p.T :=
      (Nat.add_le_add_left hbound s).trans hstartSpan
    let Cn := ReferenceActivePhysicalHorizon.run I source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s (b + n)
      hspan_n active
    have hsenderN := hsenderQueries n hn
    refine ⟨hspan_n, hsenderN.1, ?_⟩
    rcases hsenderN.2 with hdagger |
      ⟨endpoint, endpointMemory, hendpoint, hendpointStatus, hendpointReply, hchoices⟩
    · exact Or.inl hdagger
    refine Or.inr ⟨endpoint, endpointMemory, hendpoint, hendpointStatus, hendpointReply, ?_⟩
    intro hOrd preRun full interval trace rounds positive channel window hCount
    obtain ⟨spanS, hcutS⟩ :=
      ReferenceFirstCollectionLateUpSecondWindow.actual_first_collection_late_up_second_window
        rate source rewards C_star C_h count hcross hspan hshort k i M hretained n hn
    have hcut := hcutS hOrd hCount
    obtain ⟨first, last, index, record, diagnostic, hcutFacts⟩ := hcut
    rcases hcutFacts with ⟨hfirst, hfirstLen, hwindowLen, hwindowPairwise, hlast,
      hdecision, hindexRound, hrecordMem, hrecordTime, hdiagnostic, hselected,
      hdiagnosticTime, hlastEntry, hsample, hledgerFacts, hconnectedCut, hbankReplay,
      hdiagnosticBank, hbefore, hbeforePending, htransitionPending, htransitionCompleted,
      hdecoderAfter, hrawTransition, hrawBatch, htransitionPair, hrunReplay, hfinalBank⟩
    have hlaunch := ReferenceFirstCollectionLateUpSecondWindow.actual_launch_up_bank_seed
      rate source rewards C_star C_h count hcross hspan
    have hinitial : ReferenceUpDecoderBankInvariant.upBankInvariant I := hlaunch.1
    have hintervalEq : interval = Wlate.take n :=
      interval_eq_window_take I source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s count hspan
        active b n hbound hn
    have hintervalLen : interval.length = n := by
      rw [hintervalEq, List.length_take, Nat.min_eq_left hn]
    have hroundsChronological :=
      ReferenceCoordinatorUpIntervalWindow.run_interval_rounds_chronological
        I source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
        rewards s b (b + n) (Nat.le_add_right b n) hspan_n active hinitial hOrd
    have hchronological : interval.Pairwise
        (fun earlier later => earlier.input.time.val < later.input.time.val) := by
      have hroundValues := List.pairwise_map.mpr hroundsChronological
      have htimeValues : (interval.map (fun current => current.input.time.val)).Pairwise LT.lt := by
        simpa only [ReferenceCoordinatorUpIntervalWindow.intervalRounds,
          ReferenceCoordinatorUpIntervalWindow.intervalRecords, List.map_map,
          Function.comp_def] using hroundValues
      exact List.pairwise_map.mp htimeValues
    have hentryDetails : ∀ entry, entry ∈ window →
        ∃ (original : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
          (d : ReferenceActivePhysicalStep.UpDiagnostic p rate),
          original ∈ interval ∧ original.input.time = entry.time ∧
          AffineBatchDecoder.equation entry.sample
            (ActiveFollowerArmChoice.offeredUpWord rate.eta U) ∧
          ReferenceActivePhysicalStep.upExpected (ReferenceActivePhysicalStep.prepare original.input) =
            some (ActiveFollowerArmChoice.offeredUpWord rate.eta U) ∧
          original.output.coordinator.up = some d ∧ d.input.selectedFollower = i ∧
          AffineBatchDecoder.eligible (CoordinatorUpReception.roundInput d.input) ∧
          PublicDiscreteDraws.slotDraw (original.input.row.2 original.input.time).1 =
            PublicDiscreteDraws.upSlot ∧
          PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
            (original.input.row.2 original.input.time).1 = i := by
      intro entry hentry
      apply positive_entries_word_truth interval i U hchronological ?_ entry
        (List.mem_of_mem_drop hentry)
      intro q
      dsimp only
      intro hslotQ hdrawQ
      have hqn : q.val < n := by rw [← hintervalLen]; exact q.isLt
      have hqLate : q.val < Wlate.length := Nat.lt_of_lt_of_le hqn hn
      have hsourceEq : interval[q.val] = Wlate[q.val]'hqLate := by
        have heq := List.getElem_of_eq hintervalEq q.isLt
        exact heq.trans (by simp only [List.getElem_take])
      obtain ⟨_choice, _choiceMemory, _hchoice, _hchoiceStatus, _hchoiceReply, hsender⟩ :=
        hchoices q.val hqn
      have hoff := hsender (by rw [← hsourceEq]; exact hslotQ)
        (by rw [← hsourceEq]; exact hdrawQ)
      have hsent := hoff.2.2.1
      have hexpected := hoff.2.2.2.1
      rw [← hsourceEq] at hsent hexpected
      exact ⟨hsent, hexpected⟩
    have hequations : ∀ entry, entry ∈ window →
        AffineBatchDecoder.equation entry.sample
          (ActiveFollowerArmChoice.offeredUpWord rate.eta U) := by
      intro entry hentry
      obtain ⟨original, d, _hm, _ht, heq, _rest⟩ := hentryDetails entry hentry
      exact heq
    have hsolves : AffineBatchDecoder.satisfies (AffineBatchDecoder.samples window)
        (ActiveFollowerArmChoice.offeredUpWord rate.eta U) :=
      (AffineBatchDecoder.satisfies_samples_iff window _).2 hequations
    refine ⟨first, last, index, record, diagnostic, hfirst, hfirstLen, hwindowLen,
      hwindowPairwise, hlast, hdecision, hindexRound, hrecordMem, hrecordTime,
      hdiagnostic, hselected, hdiagnosticTime, hlastEntry, hsample, hledgerFacts,
      hconnectedCut, hbankReplay, hdiagnosticBank, hbefore, hbeforePending,
      htransitionPending, htransitionCompleted, hdecoderAfter, hrawTransition,
      hrawBatch, htransitionPair, hrunReplay, hfinalBank, hequations, hsolves, ?_⟩
    intro hunique
    obtain ⟨word, _hword, hwordUnique⟩ := hunique
    have hbatchWord : AffineBatchDecoder.batchOutput window =
        some (ActiveFollowerArmChoice.offeredUpWord rate.eta U) := by
      apply (AffineBatchDecoder.batchOutput_eq_some_iff window _).2
      refine ⟨hequations, ?_⟩
      intro candidate hcandidate
      have hc := (AffineBatchDecoder.satisfies_samples_iff window candidate).2 hcandidate
      exact (hwordUnique candidate hc).trans (hwordUnique _ hsolves).symm
    have hrawWord := hrawBatch.trans hbatchWord
    obtain ⟨original, d, horiginalMem, horiginalTime, _heq, hsentExpected,
        horiginalUp, horiginalSelected, heligible, hslot, hdraw⟩ := hentryDetails last hlast
    have horiginalEq : original = record :=
      ReferenceAssignmentPayloadChronology.run_records_time_injective I source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s (b + n)
        hspan_n active (List.mem_of_mem_drop horiginalMem)
        (List.mem_of_mem_drop hrecordMem) (by rw [horiginalTime, hrecordTime])
    subst original
    have hdEq : d = diagnostic := Option.some.inj (horiginalUp.symm.trans hdiagnostic)
    subst d
    have hintervalCut := ReferenceCoordinatorUpIntervalWindow.run_interval_cut I source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s b (b + n)
      (Nat.le_add_right b n) hspan_n active hinitial hOrd
    have hrecordOrd : record.output.next.coordinator ≠ .dagger :=
      hintervalCut.2.2.2.2.2.2 record (List.mem_of_mem_drop hrecordMem)
    have hindexInterval : index.val < interval.length := by
      simpa only [ReferenceCoordinatorUpIntervalWindow.intervalRounds,
        ReferenceCoordinatorUpIntervalWindow.intervalRecords, List.length_map] using index.isLt
    have hindexN : index.val < n := lt_of_lt_of_eq hindexInterval hintervalLen
    have hindexLate : index.val < Wlate.length := Nat.lt_of_lt_of_le hindexN hn
    have hindexTime : (interval[index.val]'hindexInterval).input.time = last.time := by
      have hroundAt : (interval.map (fun r => r.input.time))[index.val]'(by
          simpa only [List.length_map] using hindexInterval) = last.time := by
        exact hindexRound
      simpa only [List.getElem_map] using hroundAt
    have hrecordAt : interval[index.val]'hindexInterval = record :=
      ReferenceAssignmentPayloadChronology.run_records_time_injective I source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s (b + n)
        hspan_n active (List.mem_of_mem_drop (List.getElem_mem hindexInterval))
        (List.mem_of_mem_drop hrecordMem) (by rw [hindexTime, hrecordTime])
    have hlateRecord : Wlate[index.val]'hindexLate = record := by
      have heq := List.getElem_of_eq hintervalEq hindexInterval
      simp only [List.getElem_take] at heq
      exact heq.symm.trans hrecordAt
    obtain ⟨hindexOriginal, hreceiverAt⟩ := hreceiver index.val hindexLate
    have hrecordOriginal : E.records[b + index.val]'hindexOriginal = record :=
      (List.getElem?_eq_some_iff.mp (hlookup index.val hindexLate).1).2.trans hlateRecord
    dsimp only at hreceiverAt
    rw [hrecordOriginal] at hreceiverAt
    obtain ⟨tail, _recording, pre, preSaved, Lsite, dB, _received, _receivedBank,
        _finished, _clockFinished, hinputCollection, hpending, _hsigma,
        htail, _htailLedger, _hrecording, _hstartRound, hsite, _hsiteCheck,
        hupB, hinputB, _htailReception, _hnotInvalid, hsitePending, _hsiteSigma,
        _hsiteCursor, _hsiteCutoff, _hbank, _htime, _hsample, _hobservation,
        _hdecoder, _hraw, hexpected, _hparsed, _hlocal, _hrawMatches,
        _hresult, _hfinish, _hclock, _hzero, hlocalQueries⟩ := hreceiverAt hrecordOrd
    have hdB : dB = diagnostic := Option.some.inj (hupB.symm.trans hdiagnostic)
    subst dB
    have hexpectedWord := hexpected.trans hsentExpected
    have hgate : CoordinatorUpReception.receptionGate diagnostic.input :=
      (CoordinatorUpReception.roundInput_selected_iff_gate diagnostic.input).mp heligible.1
    have hnotAccepted : i ∉ (ReferenceCollectionPhaseHistory.acceptedLabels
        (Wlate.take index.val)).toFinset := by
      intro haccepted
      exact ((hlocalQueries hslot hdraw).2 haccepted).2.1 hgate
    have hlocalFacts := (hlocalQueries hslot hdraw).1 hnotAccepted
    have hUsigma : U.val.sigma = s + 1 := congrArg OrdinaryMessageCodec.UpFields.sigma hUnumeric
    have haccept : CoordinatorCollectionLedger.acceptUpCheck Lsite i U = true :=
      hlocalFacts.2.2.2.2 U hUsigma
    have hipre : i ∈ pre.pending := by
      rw [hpending]
      exact Finset.mem_sdiff.mpr ⟨hipending0, hnotAccepted⟩
    have hisite : i ∈ Lsite.pending := by rw [hsitePending]; exact hipre
    obtain ⟨_recordingR, siteR, dR, _hrecordingR, _hstartR, hsiteR, _hcheckR,
        hupR, _hinputR, _htailR, _hnotInvalidR, _hresultsR, _hdecoderR, _hrawR,
        _hparsedR, _hlocalR, _hexpectedR, _hmatchesR, _hbankR, _htimeR,
        _hsampleR, _hobservationR, _hwrongR, hmatching⟩ :=
      ReferenceCollectionUpReceiverLocal.actual_collection_up_receiver_matching_word
        record P0 pre preSaved tail hinputCollection htail hrecordOrd
    have hsiteEq : siteR = Lsite := Option.some.inj (hsiteR.symm.trans hsite)
    subst siteR
    have hdiagEq : dR = diagnostic := Option.some.inj (hupR.symm.trans hdiagnostic)
    subst dR
    have hsenderIndex : ReferenceActivePhysicalStep.upSenderIndex record.input = i := by
      rw [ReferenceActiveAffinePositiveTest.upSenderIndex_eq_draw, hdraw]
    have hmatchingWord := hmatching U hrawWord hexpectedWord (by rw [hsenderIndex]; exact haccept)
    rw [hsenderIndex] at hmatchingWord
    exact ⟨hrawWord, hexpectedWord, tail, pre, preSaved, Lsite,
      hinputCollection, hpending, htail, hsite, hinputB, hipre, hisite, haccept,
      hmatchingWord⟩

end Bandits.Support.ReferenceFirstCollectionLateUpWindowAcceptance

end
