/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionFormedUpBankReplay

import Lean.Elab.Tactic.Omega

/-!
# Actual formed-UP second pure batch at a local inclusive count

Sources: sources/zip4/manuscript/06_interruptions.tex:476-481,
sources/zip4/manuscript/05_binary_transport.tex:27-55, and
sources/zip4/manuscript/appendix_a_local_protocol.tex:100-157.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions
open ReferenceActivePhysicalHorizon
open ReferencePrelaunchFollower
open ReferenceFirstCollectionFormedUpOfferReceiver

namespace Bandits.Support.ReferenceFirstCollectionFormedUpSecondPureBatch

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


private theorem mem_of_mem_drop_list {α : Type} (xs : List α) (n : ℕ)
    {x : α} (h : x ∈ xs.drop n) : x ∈ xs := by
  induction n generalizing xs with
  | zero => simpa using h
  | succ n ih =>
      cases xs with
      | nil => simp at h
      | cons a xs => exact List.mem_cons_of_mem a (ih xs (by simpa using h))

private theorem positive_entry_details
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (i : Fin (p.m - 1))
    (hchronological : records.Pairwise
      (fun earlier later => earlier.input.time.val < later.input.time.val))
    (entry : AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p))
    (hentry : entry ∈
      ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries records i) :
    ∃ (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
      (diagnostic : ReferenceActivePhysicalStep.UpDiagnostic p rate),
      record ∈ records ∧ record.input.time = entry.time ∧
      record.output.coordinator.up = some diagnostic ∧
      diagnostic.input.selectedFollower = i ∧
      AffineBatchDecoder.eligible (CoordinatorUpReception.roundInput diagnostic.input) ∧
      PublicDiscreteDraws.slotDraw (record.input.row.2 record.input.time).1 =
        PublicDiscreteDraws.upSlot ∧
      PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
        (record.input.row.2 record.input.time).1 = i ∧
      entry.sample = ((record.input.rows record.input.selected).2 record.input.time).2 (1, i) ∧
      ReferenceActiveAffinePositiveTest.upPositive record.input = true := by
  classical
  let trace := ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace records i
  have htracePos :=
    ReferenceCoordinatorUpIntervalWindow.actual_trace_positives_eq_retained
      records i hchronological
  have hentryPos : entry ∈ AffineBatchDecoder.positives p trace
      (records.map fun r => r.input.time) := by
    change entry ∈ AffineBatchDecoder.positives p
      (ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace records i)
      (records.map fun r => r.input.time)
    rw [htracePos]
    exact hentry
  obtain ⟨htime, heligible, hsample⟩ :=
    (AffineBatchDecoder.mem_positives_iff p trace (records.map fun r => r.input.time) entry).mp
      hentryPos
  obtain ⟨record, hrecord, htime⟩ := List.mem_map.mp htime
  have htrace := ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace_at_record
    records i hchronological record hrecord
  have hfocal : AffineBatchDecoder.eligible
      (ReferenceCoordinatorUpIntervalWindow.recordFocalInput record i) := by
    rw [← htrace, htime]
    exact heligible
  obtain ⟨diagnostic, hdiagnostic, hselected⟩ :
      ∃ diagnostic, record.output.coordinator.up = some diagnostic ∧
        diagnostic.input.selectedFollower = i := by
    cases hcall : record.output.coordinator.up with
    | none =>
        simp [ReferenceCoordinatorUpIntervalWindow.recordFocalInput, hcall,
          ReferenceCoordinatorUpIntervalWindow.administrativeNoCallInput,
          AffineBatchDecoder.eligible] at hfocal
    | some diagnostic =>
        by_cases hi : diagnostic.input.selectedFollower = i
        · exact ⟨diagnostic, rfl, hi⟩
        · simp [ReferenceCoordinatorUpIntervalWindow.recordFocalInput, hcall, hi,
            ReferenceCoordinatorUpDecoderReplay.retainedUpRoundInput,
            AffineBatchDecoder.eligible] at hfocal
  have htraceInput : trace record.input.time =
      CoordinatorUpReception.roundInput diagnostic.input := by
    change ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace records i record.input.time = _
    rw [htrace]
    simp only [ReferenceCoordinatorUpIntervalWindow.recordFocalInput, hdiagnostic,
      hselected, ReferenceCoordinatorUpDecoderReplay.retainedUpRoundInput, ite_true]
  have hround : AffineBatchDecoder.eligible
      (CoordinatorUpReception.roundInput diagnostic.input) := by
    rw [← htraceInput, htime]
    exact heligible
  obtain ⟨ledger, _hsite, _hcheck, hinput, _hafter, _hdiagTime,
      hselectedIndex, hactualSample, _hobs, _hfeedback, _henabled,
      hretainedSample, _hrounded, _heligibleCall, _hownEntries⟩ :=
    ReferenceCoordinatorUpIntervalWindow.record_retained_up_actual_call
      record diagnostic hdiagnostic
  have hgate :=
    (CoordinatorUpReception.roundInput_selected_iff_gate diagnostic.input).mp hround.1
  have hslotInput : diagnostic.input.slot =
      PublicDiscreteDraws.slotDraw (record.input.row.2 record.input.time).1 := by
    rw [hinput]
    rfl
  have hslotDraw : PublicDiscreteDraws.slotDraw
      (record.input.row.2 record.input.time).1 = PublicDiscreteDraws.upSlot :=
    hslotInput.symm.trans hgate.2.1
  have hdraw : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
      (record.input.row.2 record.input.time).1 = i := by
    rw [← CoordinatorUpMeasurability.selectedFollowerIndex_eq_draw]
    exact hselectedIndex.symm.trans hselected
  have hchannel : CoordinatorUpMeasurability.selectedChannelFollower
      ((record.input.rows record.input.selected).2 record.input.time) = i := by
    apply Fin.ext
    rw [CoordinatorUpMeasurability.selectedChannelFollower_val,
      ← CoordinatorUpMeasurability.selectedFollowerIndex_eq_draw]
    simpa only [ContinuousLearningRows.d] using congrArg Fin.val
      (hselectedIndex.symm.trans hselected)
  have hsampleEq : entry.sample =
      (record.input.row.2 record.input.time).2 (1, i) := by
    rw [hsample, ← htime, htraceInput]
    simp [CoordinatorUpReception.roundInput, ReferenceActivePhysicalStep.RoundInput.row,
      hactualSample, hchannel]
    rfl
  have hpositive : ReferenceActiveAffinePositiveTest.upPositive record.input = true := by
    rw [ReferenceActiveAffinePositiveTest.record_upPositive, hdiagnostic]
    simpa only [ReferenceActiveAffinePositiveTest.upDiagnosticPositive] using
      (decide_eq_true hround)
  exact ⟨record, diagnostic, hrecord, htime, hdiagnostic, hselected,
    hround, hslotDraw, hdraw, hsampleEq, hpositive⟩

private theorem prefix_slice_eq {α : Type} (xs ys : List α)
    (w f b : ℕ) (hprefix : xs <+: ys.drop w)
    (hfb : f ≤ b) (hb : b ≤ xs.length) :
    (xs.drop f).take (b - f) = (ys.take (w + b)).drop (w + f) := by
  have htake : xs.take b = (ys.drop w).take b := by
    obtain ⟨suffix, hsuffix⟩ := hprefix
    rw [← hsuffix, List.take_append_of_le_length hb]
  calc
    (xs.drop f).take (b - f) = (xs.take b).drop f := by
      rw [List.take_drop, Nat.add_sub_of_le hfb]
    _ = ((ys.drop w).take b).drop f := congrArg (fun zs => zs.drop f) htake
    _ = (ys.take (w + b)).drop (w + f) := by
      rw [List.take_drop, List.drop_drop]

private theorem slice_member_index {α : Type} (xs : List α)
    (f b : ℕ) (record : α)
    (hrecord : record ∈ (xs.drop f).take (b - f)) :
    ∃ k : Fin xs.length, f ≤ k.val ∧ k.val < b ∧ xs[k.val] = record := by
  obtain ⟨q, hq, hrecord⟩ := List.mem_iff_getElem.mp hrecord
  have hqbound : q < b - f ∧ q < xs.length - f := by
    simpa only [List.length_take, List.length_drop, lt_min_iff] using hq
  have hk : f + q < xs.length := by omega
  refine ⟨⟨f + q, hk⟩, Nat.le_add_right f q, by change f + q < b; omega, ?_⟩
  simpa only [List.getElem_take, List.getElem_drop] using hrecord

private theorem positive_equation
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1))
    (entry : AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p))
    (word : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (hsample : entry.sample =
      ((record.input.rows record.input.selected).2 record.input.time).2 (1, i))
    (hdraw : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
      (record.input.row.2 record.input.time).1 = i)
    (hexpected : ReferenceActivePhysicalStep.upExpected
      (ReferenceActivePhysicalStep.prepare record.input) = some word)
    (hpositive : ReferenceActiveAffinePositiveTest.upPositive record.input = true) :
    AffineBatchDecoder.equation entry.sample word := by
  have hsent : ReferenceActiveAffinePositiveTest.upSent record.input = some word := hexpected
  have hhash := ReferenceUpPhysicalHashRule.upPositive_hash_one
    record.input word hsent hpositive
  have hsender : ReferenceActivePhysicalStep.upSenderIndex record.input = i := hdraw
  rw [hsender] at hhash
  rw [hsample]
  exact (AffineBatchDecoder.equation_iff_affineHash
    ((record.input.row.2 record.input.time).2 (1, i)) word).mpr hhash


private theorem saved_second_batch
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start a b : ℕ) (hab : a ≤ b) (hspan : start + b ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hinitial : ReferenceUpDecoderBankInvariant.upBankInvariant initial)
    (hordinary : (ReferenceActivePhysicalHorizon.run initial rows selected rewards
      start b hspan hmode).finalState.coordinator ≠ .dagger)
    (i : Fin (p.m - 1))
    (hseed : AffineBatchDecoder.collected (initial.upDecoderBank i) = [])
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (hrecords : records = ReferenceCoordinatorUpIntervalWindow.intervalRecords
      initial rows selected rewards start a b hspan hmode)
    (channel final : AffineBatchDecoder.State p.T (AffineBatchDecoder.width p))
    (hchannel : channel = (ReferenceActivePhysicalHorizon.run initial rows selected rewards
      start a (by omega) hmode).finalState.upDecoderBank i)
    (hfinal : final = (ReferenceActivePhysicalHorizon.run initial rows selected rewards
      start b hspan hmode).finalState.upDecoderBank i) :
    let times := records.map (fun record => record.input.time)
    let trace := ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace records i
    let positive := AffineBatchDecoder.positives p trace times
    positive.length = AffineBatchDecoder.quota p - channel.pending.length +
      AffineBatchDecoder.quota p →
    ∃ (first window : List (AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p)))
      (last : AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p))
      (index : Fin times.length)
      (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
      (diagnostic : ReferenceActivePhysicalStep.UpDiagnostic p rate),
      first = channel.pending ++ positive.take
        (AffineBatchDecoder.quota p - channel.pending.length) ∧
      first.length = AffineBatchDecoder.quota p ∧
      window = positive.drop (AffineBatchDecoder.quota p - channel.pending.length) ∧
      window.length = AffineBatchDecoder.quota p ∧
      final =
        { pending := [], completed := channel.completed ++ [first, window] } ∧
      window.Pairwise (fun earlier later => earlier.time.val < later.time.val) ∧
      (∀ e, e ∈ channel.pending → e ∉ window) ∧
      positive.length ≤ 2 * AffineBatchDecoder.quota p ∧
      last ∈ window ∧
      AffineBatchDecoder.decisionTime window = some last.time ∧
      times.get index = last.time ∧
      record ∈ records ∧ record.input.time = last.time ∧
      record.output.coordinator.up = some diagnostic ∧
      diagnostic.input.selectedFollower = i ∧
      diagnostic.raw = AffineBatchDecoder.batchOutput window ∧
      ∀ e, e ∈ window → start + a ≤ e.time.val ∧ e.time.val < start + b := by
  subst records channel final
  intro times trace positive hcount
  have hgeometry := ReferenceCoordinatorUpIntervalWindow.run_interval_two_batch_window
    initial rows selected rewards start a b hab hspan hmode hinitial hordinary i hseed hcount
  obtain ⟨_first, _last, _index, _hrun, _hfinal, _hfirst, _hfirstLen,
    _hwindowLen, _hchron, hdisjoint, hbound, hbounds, _hlast, _hdecision,
    _hindex, _heligible, _hsample, _hmax, _hraw⟩ := hgeometry
  have hcut := ReferenceCoordinatorUpWindowCompletedCut.run_interval_saved_completed_cut
    initial rows selected rewards start a b hab hspan hmode hinitial hordinary i hseed hcount
  obtain ⟨first, last, index, record, diagnostic, hfields⟩ := hcut
  rcases hfields with ⟨hfirst, hfirstLen, hwindowLen, hchron, hlast,
    hdecision, hindex, hrecord, htime, hdiagnostic, hselected, _hdiagTime,
    _hlastEntry, _hlastSample, _hphysical, _hconnected, _hrecordBank,
    _hdiagBank, _hbefore, _happend, _hpending, _hcompleted, _hafter,
    _hraw, hraw, _htransition, hrun, hfinal⟩
  refine ⟨first, _, last, index, record, diagnostic, hfirst, hfirstLen, rfl,
    hwindowLen, hfinal.symm.trans hrun, hchron, hdisjoint, hbound, hlast,
    hdecision, hindex, hrecord, htime, hdiagnostic, hselected, hraw, hbounds⟩


public theorem actual_initialized_first_collection_formed_up_second_pure_batch
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
                          (∀ (b : ℕ) (hfb : f ≤ b) (hbn : b ≤ n.val + 1),
                            let S := (B.drop f).take (b - f)
                            let times := S.map (fun record => record.input.time)
                            let tr := ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace S i
                            let P := AffineBatchDecoder.positives p tr times
                            let ch := (X f (by omega)).upDecoderBank i
                            let Q := AffineBatchDecoder.quota p
                            P.length = Q - ch.pending.length + Q →
                            ∃ (first : List (AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p)))
                              (window : List (AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p)))
                              (last : AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p))
                              (index : Fin times.length)
                              (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
                              (diagnostic : ReferenceActivePhysicalStep.UpDiagnostic p rate),
                              first = ch.pending ++ P.take (Q - ch.pending.length) ∧
                              first.length = Q ∧
                              window = P.drop (Q - ch.pending.length) ∧
                              window.length = Q ∧
                              (X b (by omega)).upDecoderBank i =
                                { pending := [], completed := ch.completed ++ [first, window] } ∧
                              window.Pairwise (fun x y => x.time.val < y.time.val) ∧
                              (∀ e, e ∈ ch.pending → e ∉ window) ∧
                              P.length ≤ 2 * Q ∧
                              last ∈ window ∧
                              AffineBatchDecoder.decisionTime window = some last.time ∧
                              times.get index = last.time ∧
                              record ∈ S ∧
                              record.input.time = last.time ∧
                              record.output.coordinator.up = some diagnostic ∧
                              diagnostic.input.selectedFollower = i ∧
                              diagnostic.raw = AffineBatchDecoder.batchOutput window ∧
                              (∀ e, e ∈ window →
                                s + w + f ≤ e.time.val ∧ e.time.val < s + w + b ∧
                                AffineBatchDecoder.equation e.sample
                                  (ReferenceFirstCollectionFormedUpOfferReceiver.encodedUpOfferWord U))) ∧
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
    hpayload, hpending, hBpos, hBzero, hcutoff, hresult⟩ :=
    ReferenceFirstCollectionFormedUpBankReplay.actual_initialized_first_collection_formed_up_bank_replay
      rate source rewards C_star C_h count hcross hspan hshort
  let out := d.stream
  let E := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
    rate source rewards C_star C_h hcross count hspan
  let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records).length
  let s := ReferenceInitializationRun.elapsed p
    (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
  let B := ReferenceCollectionPhaseHistory.collectionWindow E.records w
  let initial := ReferenceFirstCollectionEpochAlignment.actualLaunchState
    rate source rewards C_star C_h hcross
  let hmode := (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
    rate source rewards C_star C_h hcross).1
  let selected := ActualInitializationPhysicalStep.selectedRowIndex p source
  let X (t : ℕ) (_hwt : w + t ≤ count) :=
    (ReferenceActivePhysicalHorizon.run initial source.1.2 selected rewards s (w + t)
      (by omega) hmode).finalState
  have hWindow : out.window = B := by
    simpa [out, E, w, B, ReferenceFirstCollectionReadyStream.actualWindow,
      ReferenceFirstCollectionReadyStream.actualEpoch,
      ReferenceFirstCollectionReadyStream.startTime] using out.windowIsActual
  have hBlength : out.ell ≤ B.length := by
    simpa [hWindow] using out.withinWindow
  rcases hresult with ⟨hprefix, hboundaries⟩
  rcases hprefix with ⟨hlen, hEndpoint, hStateFacts, hzeroPending, hAllBanks⟩
  refine ⟨d, registers, owned, base, cutRecord, hcutIndex, hcutState,
    hpayload, hpending, hBpos, hBzero, hcutoff, ?_, ?_⟩
  · exact ⟨hlen, hEndpoint, hStateFacts, hzeroPending, hAllBanks⟩
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
    obtain ⟨hf, hfn, hftime, hfzero, hfone, hpendingMono,
      _hsourceBanks, hchoices⟩ := hinterval
    refine ⟨U, hUfields, hUsigma, hUpositive, hUoffer, hDownsigma, haccepted,
      j, hjIndex, acceptedRecord, hjbefore, hjrecord, hretained, hacceptedCut,
      hatime, harows, haselected, harewards, hunique, hf, hfn, hftime,
      hfzero, hfone, hpendingMono, ?_⟩
    constructor
    · intro b hfb hbn
      have hb : b ≤ out.ell := Nat.le_trans hbn n.isLt
      exact hAllBanks i f b hfb hb
    · constructor
      · intro b hfb hbn S times tr P ch Q hQuery
        let Aoff := w + f
        let Coff := w + b
        have hbEll : b ≤ out.ell := Nat.le_trans hbn (Nat.succ_le_of_lt n.isLt)
        have hbB : b ≤ B.length := Nat.le_trans hbEll hBlength
        have hhab : Aoff ≤ Coff := Nat.add_le_add_left hfb w
        have hwC : w + b ≤ count :=
          Nat.le_trans (Nat.add_le_add_left hbEll w) hlen
        have hrunCount : Coff ≤ count := hwC
        have hspanC : s + Coff ≤ p.T :=
          Nat.le_trans (Nat.add_le_add_left hwC s) hspan
        let full := ReferenceActivePhysicalHorizon.run initial source.1.2 selected rewards s Coff
          hspanC hmode
        let interval := full.records.drop Aoff
        have hordinary : full.finalState.coordinator ≠ .dagger :=
          (hStateFacts b hbEll).2
        have hBprefix := collectionWindow_isPrefix_drop E.records w
        have hfullRecords : full.records = E.records.take Coff := by
          simpa [full, E, Coff, ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun] using
            run_prefix_records initial source.1.2 selected rewards s count hspan hmode Coff hrunCount
        have hSinterval : S = interval := by
          have hslice := prefix_slice_eq B E.records w f b hBprefix hfb hbB
          change S = full.records.drop Aoff
          rw [hfullRecords]
          exact hslice
        have hseedData := ReferenceFirstLaunchNumericalCell.actual_launch_seed
          rate source rewards C_star C_h hcross
        rcases hseedData with ⟨_, _, _, hfirstSeed, hbankSeed, _, _, _⟩
        have hinitialFirst : initial.coordinator = .first := by
          simpa [initial, ReferenceFirstCollectionEpochAlignment.actualLaunchState,
            ReferenceFirstLaunchNumericalCell.launchState] using hfirstSeed
        have hinitialBank : initial.upDecoderBank = CoordinatorUpReception.initialUpDecoderBank p := by
          simpa [initial, ReferenceFirstCollectionEpochAlignment.actualLaunchState,
            ReferenceFirstLaunchNumericalCell.launchState] using hbankSeed
        have hinitial : ReferenceUpDecoderBankInvariant.upBankInvariant initial := by
          change ReferenceUpDecoderBankInvariant.coordinatorBankInvariant
            initial.coordinator initial.upDecoderBank
          rw [hinitialFirst, hinitialBank]
          exact ⟨CoordinatorUpReception.initialUpDecoderBank_wellFormed p, fun _ => rfl⟩
        have hseed (follower : Fin (p.m - 1)) :
            AffineBatchDecoder.collected (initial.upDecoderBank follower) = [] := by
          simp [hinitialBank, CoordinatorUpReception.initialUpDecoderBank,
            AffineBatchDecoder.initial, AffineBatchDecoder.collected]
        have hpositiveRetained := hAllBanks i f b hfb hbEll
        rcases hpositiveRetained with ⟨_hbankReplay, _hdecodeRun, _hcollected,
          hPretained, htimesChron, _hpendingSmall, _hpendingOld⟩
        have hrecordsChron : S.Pairwise
            (fun earlier later => earlier.input.time.val < later.input.time.val) :=
          (List.pairwise_map
            (f := fun record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) =>
              record.input.time)
            (R := fun x y : Fin p.T => x.val < y.val)).mp htimesChron
        have hPtrace : P = ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries S i :=
          hPretained
        obtain ⟨first, window, last, index, record, diagnostic, hfirstEq,
          hfirstLen, hwindowEq, hwindowLength, hbank, hwindowPair,
          hwindowDisjoint, hbound2, hlastMem, hdecision, hindex,
          hrecordInS, hrecordTime, hdiagnostic, hselected, hraw,
          hwindowBounds⟩ :=
          saved_second_batch initial source.1.2 selected rewards s Aoff Coff
            hhab hspanC hmode hinitial hordinary i (hseed i) S hSinterval
            ch ((X b hwC).upDecoderBank i) rfl rfl hQuery
        have hrecordDetails : ∀ e, e ∈ window →
            s + w + f ≤ e.time.val ∧ e.time.val < s + w + b ∧
            AffineBatchDecoder.equation e.sample
              (ReferenceFirstCollectionFormedUpOfferReceiver.encodedUpOfferWord U) := by
          intro e he
          have heP : e ∈ P := by
            rw [hwindowEq] at he
            exact mem_of_mem_drop_list P (Q - ch.pending.length) he
          have heRetained : e ∈ ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries S i := by
            rw [← hPtrace]
            exact heP
          obtain ⟨recordE, diagnosticE, hrecordMem, htimeE, hdiagE, hselE,
            _heEligible, hslotE, hdrawE, hsampleE, hpositiveE⟩ :=
            positive_entry_details S i hrecordsChron e heRetained
          obtain ⟨k, hfk, hkb, hrecordB⟩ :=
            slice_member_index B f b recordE hrecordMem
          have hkn : k.val ≤ n.val := Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hkb hbn)
          have hrecordK :
              ReferenceFirstCollectionFormedReplyStateInterval.actualCollectionRecord B k = recordE :=
            hrecordB
          obtain ⟨choice, choiceMemory, _hcfg, _hdom, _hstatus, _hreply, _hdown,
            _hS, _hdelta, _hbacklog, _hrow, _hfollower, _hactivation, _htime,
            before, beforeMemory, _hbeforeState, _hbeforeDomain, _hstart,
            _hreplyStart, _hledgers, hselectedUp, _hcutChoice⟩ := hchoices k hfk hkn
          have hslotK : PublicDiscreteDraws.slotDraw
              ((ReferenceFirstCollectionFormedReplyStateInterval.actualCollectionRecord B k).input.row.2
                (ReferenceFirstCollectionFormedReplyStateInterval.actualCollectionRecord B k).input.time).1 =
              PublicDiscreteDraws.upSlot := by
            rw [hrecordK]
            exact hslotE
          have hdrawK : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
              ((ReferenceFirstCollectionFormedReplyStateInterval.actualCollectionRecord B k).input.row.2
                (ReferenceFirstCollectionFormedReplyStateInterval.actualCollectionRecord B k).input.time).1 = i := by
            rw [hrecordK]
            exact hdrawE
          have hsenderExpected : ReferenceActivePhysicalStep.upExpected
              (ReferenceActivePhysicalStep.prepare recordE.input) = some (encodedUpOfferWord U) := by
            have h := (hselectedUp hslotK hdrawK).2.2.2
            rw [hrecordK] at h
            exact h
          have hequation := positive_equation recordE i e (encodedUpOfferWord U)
            hsampleE hdrawE hsenderExpected hpositiveE
          have hbounds := hwindowBounds e he
          exact ⟨by simpa only [Aoff, Nat.add_assoc] using hbounds.1,
            by simpa only [Coff, Nat.add_assoc] using hbounds.2, hequation⟩
        refine ⟨first, window, last, index, record, diagnostic,
          hfirstEq, hfirstLen, hwindowEq, hwindowLength, hbank, hwindowPair,
          hwindowDisjoint, hbound2, hlastMem, hdecision, hindex, hrecordInS,
          hrecordTime, hdiagnostic, hselected, hraw, hrecordDetails⟩
      · exact hchoices
