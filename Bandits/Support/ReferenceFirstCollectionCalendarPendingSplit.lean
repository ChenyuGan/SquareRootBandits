/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionAwaitedCutoffHistory

import Lean.Elab.Tactic.Omega

/-!
# Raw first-collection calendar pending/failure split

The theorem below classifies the unchanged raw first-collection window on the
original source input. Empty pending at the actual next boundary is retained
as a real failed checked-sampler call followed by coordinator dagger. It does
not assert that dagger or empty-pending suffixes have zero service charge.

Sources: `sources/zip4/manuscript/06_interruptions.tex:9-14,40-100,425-431,459-487`,
`sources/zip4/manuscript/05_binary_transport.tex:180-240`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:8-84`.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions
open BootstrapPrivateRoundStreams
open ReferenceActivePhysicalStep
open ReferenceActivePhysicalHorizon
open scoped Classical

namespace Bandits.Support.ReferenceFirstCollectionCalendarPendingSplit

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

abbrev Record (rate : ReferenceActivePhysicalStep.RateInput p) :=
  ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)

private theorem takeWhile_member_false {α : Type*} (pred : α → Bool)
    (xs : List α) (x : α) (h : x ∈ xs.takeWhile pred) : pred x = true := by
  induction xs with
  | nil => simp at h
  | cons a tail ih =>
      by_cases hp : pred a = true
      · simp [List.takeWhile, hp] at h
        rcases h with rfl | h
        · exact hp
        · exact ih h
      · simp [List.takeWhile, hp] at h

private theorem collectionWindow_laterChosen_false_of_pos
    (records : List (Record (p := p) (rate := rate))) (w index : ℕ)
    (hpos : 0 < index)
    (hindex : index < (ReferenceCollectionPhaseHistory.collectionWindow records w).length) :
    ReferenceCollectionPhaseHistory.laterChosen
      ((ReferenceCollectionPhaseHistory.collectionWindow records w)[index]'hindex).input = false := by
  classical
  let head := (records.drop w).take 1
  let tail := (records.drop (w + 1)).takeWhile
    (fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input)
  let window := head ++ tail
  have hwindow : ReferenceCollectionPhaseHistory.collectionWindow records w = window := by
    rfl
  have hnonempty : records.drop w ≠ [] := by
    intro hnil
    have : records.drop (w + 1) = [] := by
      apply List.drop_eq_nil_of_le
      have hlen := congrArg List.length hnil
      simp at hlen
      omega
    have hzero : ReferenceCollectionPhaseHistory.collectionWindow records w = [] := by
      simp [ReferenceCollectionPhaseHistory.collectionWindow, hnil, this]
    simp [hzero] at hindex
  have hhead : head.length = 1 := by
    rcases hdrop : records.drop w with _ | ⟨a, rest⟩
    · exact (hnonempty hdrop).elim
    · simp [head, hdrop]
  have hright : head.length ≤ index := by omega
  have hget : window[index]? = some (window[index]'(by
      simpa [hwindow] using hindex)) := by
    exact List.getElem?_eq_getElem (by simpa [hwindow] using hindex)
  have htailGet : tail[index - head.length]? = some (window[index]'(by
      simpa [hwindow] using hindex)) := by
    dsimp only [window] at hget
    rw [List.getElem?_append_right hright] at hget
    exact hget
  obtain ⟨htailIndex, htailValue⟩ := List.getElem?_eq_some_iff.mp htailGet
  have hmem : window[index]'(by simpa [hwindow] using hindex) ∈ tail := by
    rw [← htailValue]
    exact List.getElem_mem htailIndex
  have hpred := takeWhile_member_false _ _ _ hmem
  have hnot : !ReferenceCollectionPhaseHistory.laterChosen
      (window[index]'(by simpa [hwindow] using hindex)).input = true := hpred
  simpa [window, ReferenceCollectionPhaseHistory.collectionWindow] using hnot

private theorem failed_checked_sampler_falls_to_dagger
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (saved : Option (Fin p.T × Bool))
    (dispatch : ReferenceFirstCollectionStreamEmptyDispatch.ActualNextDispatch
      x payload ledger saved)
    (cutoffLastService : ∀ a c, ledger.cutoffRegisters a = some c →
      c.lastService ≤ c.score ∧ c.lastService ≤ 4 * rate.n)
    (hnotLater : ReferenceCollectionPhaseHistory.laterChosen x = false) :
    (ReferenceLaterSamplerParameterMeasurability.parameters? x).isSome = true ∧
      (ReferenceActivePhysicalStep.step x).next.coordinator = .dagger := by
  classical
  rcases dispatch.classification with
    ⟨cutoff, hcutoff, core, started, hstart, instruction, hassignment, consistent,
      hinstructionTime, hkind, hprepared, hpreviousOutputDomain, hcases⟩
  rcases hcases with hbad | ⟨out, hreconstructionSuccess, hsampleCases⟩
  · rcases hbad with ⟨a, c, hc, hscore, _hrec, _hkind, _hdispatch⟩
    have hbound := cutoffLastService a c hc
    omega
  · rcases hsampleCases with hprefixFailure | hlaterChosen
    · rcases hprefixFailure with
        ⟨hcutoffReached, hcurrentPositive, law, arm, reason, hcorrected,
          hselectLaw, previous, hprevious, hpreviousPositive, hanchor, hmass,
          hlaterStart, hsample, state, hready, hfailedStep, hrawPositive,
          hreasonBounds, hprefixDispatch⟩
      have hselected :
          (LaterAssignmentStartMeasurability.selectedSamplerParameters? payload
            ⟨CoordinatorRoundDispatch.collectionOperationLedger
                (ReferenceActivePhysicalStep.collectionInput x payload ledger
                  (ReferenceActivePhysicalStep.collectionClock payload ledger saved cutoff)
                  cutoff) core.payload_n_eq,
              (instruction, consistent)⟩).isSome = true := by
        rw [LaterAssignmentJointCodeMeasurability.selectedSamplerParameters?_eq_match]
        have hpair : (⟨AssignmentScoreReconstruction.reconstructLaterStart
            (CoordinatorRoundDispatch.collectionOperationLedger
              (ReferenceActivePhysicalStep.collectionInput x payload ledger
                (ReferenceActivePhysicalStep.collectionClock payload ledger saved cutoff)
                cutoff) core.payload_n_eq) instruction, rfl⟩ :
              LaterAssignmentStartOperation.ReconstructionCall payload
                (CoordinatorRoundDispatch.collectionOperationLedger
                  (ReferenceActivePhysicalStep.collectionInput x payload ledger
                    (ReferenceActivePhysicalStep.collectionClock payload ledger saved cutoff)
                    cutoff) core.payload_n_eq) instruction) =
            ⟨.success
                (CoordinatorRoundDispatch.collectionOperationLedger
                  (ReferenceActivePhysicalStep.collectionInput x payload ledger
                    (ReferenceActivePhysicalStep.collectionClock payload ledger saved cutoff)
                    cutoff) core.payload_n_eq)
                instruction out,
              hreconstructionSuccess⟩ := by
          apply LaterAssignmentStartOperation.ReconstructionCall.ext
          exact hreconstructionSuccess
        unfold LaterAssignmentStartOperation.decideReconstruction
        rw [hpair]
        rfl
      have hpreparedPrefix :
          (ReferenceActivePhysicalStep.prepare x).coordinator =
            .collection payload ledger
              (ReferenceActivePhysicalStep.collectionClock payload ledger saved cutoff)
              cutoff
              (.laterPrefixFailure core consistent started hstart instruction hassignment
                (some arm) reason hlaterStart) := by
        simpa [hprefixDispatch] using hprepared
      have hdispatchPrefix : ReferenceActivePhysicalStep.dispatch x =
          .collection payload ledger
            (ReferenceActivePhysicalStep.collectionClock payload ledger saved cutoff)
            cutoff
            (.laterPrefixFailure core consistent started hstart instruction hassignment
              (some arm) reason hlaterStart) := by
        simpa only [ReferenceActivePhysicalStep.prepare] using hpreparedPrefix
      have hparameters :
          (ReferenceLaterSamplerParameterMeasurability.parameters? x).isSome = true := by
        change (ReferenceLaterAssignmentFibreStep.parameters? x).isSome = true
        rw [ReferenceLaterAssignmentFibreStep.parameters?_eq_physicalDispatch]
        rw [hdispatchPrefix]
        simpa [ReferenceLaterAssignmentFibreStep.dispatchParameters?,
          ReferenceLaterAssignmentFibreStep.outcomeParameters?, hselected]
      have hselectionNone :
          (ReferenceActivePhysicalStep.DispatchCut.collection payload ledger
            (ReferenceActivePhysicalStep.collectionClock payload ledger saved cutoff)
            cutoff
            (.laterPrefixFailure core consistent started hstart instruction hassignment
              (some arm) reason hlaterStart)).selection = none := by
        simp [ReferenceActivePhysicalStep.DispatchCut.selection]
      have hobserved := ReferenceActivePhysicalStep.observeCoordinator_collection_equation
        (ReferenceActivePhysicalStep.prepare x) payload ledger
        (ReferenceActivePhysicalStep.collectionClock payload ledger saved cutoff) cutoff
        (.laterPrefixFailure core consistent started hstart instruction hassignment
          (some arm) reason hlaterStart) hpreparedPrefix
      have hstep : (ReferenceActivePhysicalStep.step x).next.coordinator = .dagger := by
        have hfields := ReferenceActivePhysicalStep.step_next_fields x
        rw [hfields.1, hobserved, hselectionNone]
        simp [ReferenceActivePhysicalStep.coordinatorFailure]
      exact ⟨hparameters, hstep⟩
    · rcases hlaterChosen with
        ⟨output, hlocal, clockData, installation, selection, hinstruction,
          hchoice, hreconstructed, hlaterCall, hlaterOutcome, _hlaw, _hvector,
          _hsampled, _hslowSet, _hassignedSet, _hstrictMono, _hauxiliary,
          _hqueues, _hbase, _hretainedBase, _hcorrectedData, _hrenewalData,
          _hdown⟩
      have hlater : ReferenceCollectionPhaseHistory.laterChosen x = true := by
        simp [ReferenceCollectionPhaseHistory.laterChosen, hprepared, hlaterOutcome]
      simp [hnotLater] at hlater

private theorem Connected.coordinator_dagger_after_get
    {initial final : ReferenceActivePhysicalStep.State p rate}
    {records : List (Record (p := p) (rate := rate))}
    (hchain : ReferenceActivePhysicalHorizon.Connected initial records final)
    (i : ℕ) (hi : i < records.length)
    (hdagger : (records[i]'hi).output.next.coordinator = .dagger) :
    ∀ j (_hij : i < j) (hj : j < records.length),
      (records[j]'hj).input.state.coordinator = .dagger := by
  induction i generalizing initial records final with
  | zero =>
      cases records with
      | nil => simp at hi
      | cons first rest =>
          have hdaggerFirst : first.output.next.coordinator = .dagger := by
            simpa using hdagger
          have hrest := hchain.2.coordinator_dagger hdaggerFirst
          intro j hj hjr
          cases j with
          | zero => omega
          | succ j =>
              have hj' : j < rest.length := by simpa using hjr
              simpa using hrest.2 _ (List.getElem_mem hj')
  | succ i ih =>
      cases records with
      | nil => simp at hi
      | cons first rest =>
          have htail : i < rest.length := by simp at hi; omega
          have hdaggerTail : (rest[i]'htail).output.next.coordinator = .dagger := by
            simpa using hdagger
          have hrest := ih hchain.2 htail hdaggerTail
          intro j hij hjr
          cases j with
          | zero => omega
          | succ j =>
              have hij' : i < j := by omega
              have hjr' : j < rest.length := by simpa using hjr
              simpa using hrest j hij' hjr'

/-- Original-source classification of every raw first-collection calendar
record. Its only inputs are the whole source telescope; the stream, crossing,
cutoff, and empty-boundary witnesses are recovered in the proof. -/
public theorem original_raw_calendar_pending_split
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let b := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
    let B := ReferenceCollectionPhaseHistory.collectionWindow R w
    let A := fun t => ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t z
    let param := ReferenceLaterSamplerParameterMeasurability.parameters? (rate := rate)
    ∀ k : Fin B.length, let r := B[k.val];
      (ReferenceFirstCollectionPendingObservation.Q rate rewards C_star C_h b
        r.input.time z).Nonempty ∨
      (((∃ (P : ReferenceActivePhysicalStep.Payload rate)
          (l : ReferenceActivePhysicalStep.Ledger rate)
          (saved : Option (Fin p.T × Bool)),
          r.input.state.coordinator = .collection P l saved ∧ l.pending = ∅) ∧
        (param r.input).isSome = true ∧
        r.output.next.coordinator = .dagger ∧
        ∀ (v : Fin p.T) (r' : Record (p := p) (rate := rate)),
          r.input.time.val < v.val → A v = some r' →
            r'.input.state.coordinator = .dagger) ∨
      r.input.state.coordinator = .dagger) := by
  classical
  dsimp only
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let b := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
  let B := ReferenceCollectionPhaseHistory.collectionWindow R w
  let A := fun t => ReferenceSourcePrefixHistoryFiltration.actualRecord
    rate rewards C_star C_h t z
  let param := ReferenceLaterSamplerParameterMeasurability.parameters? (rate := rate)
  change ∀ k : Fin B.length, let r := B[k.val];
    (ReferenceFirstCollectionPendingObservation.Q rate rewards C_star C_h b
      r.input.time z).Nonempty ∨
    (((∃ (P : ReferenceActivePhysicalStep.Payload rate)
        (l : ReferenceActivePhysicalStep.Ledger rate)
        (saved : Option (Fin p.T × Bool)),
        r.input.state.coordinator = .collection P l saved ∧ l.pending = ∅) ∧
      (param r.input).isSome = true ∧
      r.output.next.coordinator = .dagger ∧
      ∀ (v : Fin p.T) (r' : Record (p := p) (rate := rate)),
        r.input.time.val < v.val → A v = some r' →
          r'.input.state.coordinator = .dagger) ∨
    r.input.state.coordinator = .dagger)
  by_cases hBzero : B.length = 0
  · intro k
    exact Fin.elim0 (Fin.cast hBzero k)
  · have hBpos : 0 < B.length := by omega
    have hR : R ≠ [] := by
      intro hnil
      have hzero : B.length = 0 := by
        simp [B, ReferenceCollectionPhaseHistory.collectionWindow, hnil]
      omega
    have hw : w < R.length := by
      by_contra hnot
      have hdrop : R.drop w = [] := List.drop_eq_nil_of_le (Nat.le_of_not_gt hnot)
      have hlen := congrArg List.length hdrop
      simp only [List.length_drop, List.length_nil] at hlen
      have hdrop' : R.drop (w + 1) = [] :=
        List.drop_eq_nil_of_le (by omega)
      have hzero : B.length = 0 := by
        simp [B, ReferenceCollectionPhaseHistory.collectionWindow, hdrop, hdrop']
      omega
    let launch := ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate z rewards C_star C_h
    have hlaunchNone : launch ≠ none := by
      intro hnone
      have hno := ReferenceCompletePhysicalHistory.no_launch_complete_history
        rate z rewards C_star C_h hnone
      exact hR (by simpa [R] using hno.2.1)
    obtain ⟨active, hlaunchActive⟩ : ∃ active, launch = some active := by
      cases h : launch with
      | none => exact False.elim (hlaunchNone h)
      | some active => exact ⟨active, rfl⟩
    have hcross : (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true := by
      exact (ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
        rate z rewards C_star C_h).mp (by simp [launch, hlaunchActive])
    have hsome := (ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
      rate z rewards C_star C_h).2 hcross
    let initial := ReferenceFirstCollectionEpochAlignment.actualLaunchState
      rate z rewards C_star C_h hcross
    have hinitialEq : initial = active := by
      exact Option.get_of_eq_some hsome (by simpa [launch] using hlaunchActive)
    have hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
        rate z rewards C_star C_h = some initial := by
      simpa [launch] using hlaunchActive.trans (congrArg some hinitialEq.symm)
    have hstart : ReferenceFirstCollectionReadyStream.startTime
        (rate := rate) z rewards C_star C_h = b := rfl
    have hphysicalStart :
        ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h =
          ReferenceInitializationRun.elapsed p
            (ReferenceInitializationRun.output
              (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed := by
      simpa [b, ReferenceFirstCollectionReadyStream.startTime] using hstart.symm
    let count := p.T - b
    have hspan : ReferenceFirstCollectionReadyStream.startTime
        (rate := rate) z rewards C_star C_h + count ≤ p.T := by
      have hb : b ≤ p.T := by
        simpa [b] using ReferenceCompletePhysicalHistory.physicalStart_le_T
          rate z rewards C_star C_h
      rw [hstart]
      simp only [count]
      omega
    let E := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
      rate z rewards C_star C_h hcross count hspan
    have hRE : R = E.records := by
      change ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h =
        (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
          rate z rewards C_star C_h hcross count hspan).records
      rw [ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
        rate z rewards C_star C_h initial hlaunch]
      rfl
    have hRlen : R.length = count := by
      rw [hRE]
      exact ReferenceActivePhysicalHorizon.run_record_count _ _ _ _ _ _ _ _
    have hElen : E.records.length = count := by
      rw [← hRE]
      exact hRlen
    have hwRun : w = (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
          rate z rewards C_star C_h hcross count hspan).records).length := by
      dsimp [w]
      rw [hRE]
    have hshortRun :
        (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
          (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
            rate z rewards C_star C_h hcross count hspan).records).length < count := by
      rw [← hwRun]
      exact Nat.lt_of_lt_of_eq hw hRlen
    have hwEpoch : w =
        (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
          (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
            z rewards C_star C_h hcross count hspan).records).length := by
      simpa only [ReferenceFirstCollectionReadyStream.actualEpoch] using hwRun
    have hshortEpoch :
        (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
          (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
            z rewards C_star C_h hcross count hspan).records).length < count := by
      simpa only [ReferenceFirstCollectionReadyStream.actualEpoch] using hshortRun
    obtain ⟨stream⟩ := ReferenceFirstCollectionStreamEmptyDispatch.actual_initialized_first_collection_stream_empty_dispatch
        rate z rewards C_star C_h count hcross hspan hshortEpoch
    let out := stream.stream
    have hwindow : out.window = B := by
      simpa [out, E, w, B, hRE,
        ReferenceFirstCollectionReadyStream.actualWindow,
        ReferenceFirstCollectionReadyStream.actualEpoch] using out.windowIsActual
    have hconnected0 := ReferenceCompletePhysicalHistory.completeSuffix_connected_on_launch
      rate z rewards C_star C_h initial hlaunch
    have hmode := ReferenceCompletePhysicalHistory.activeMode_of_launch_eq_some
      rate z rewards C_star C_h initial hlaunch
    let final := (ReferenceActivePhysicalHorizon.run initial z.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards b count hspan hmode).finalState
    have hconnectedR : ReferenceActivePhysicalHorizon.Connected initial R final := by
      change ReferenceActivePhysicalHorizon.Connected initial
        (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h) final
      simpa [final, b, count, ReferenceFirstCollectionReadyStream.startTime] using hconnected0
    have hconnected : ReferenceActivePhysicalHorizon.Connected initial E.records final := by
      rw [← hRE]
      exact hconnectedR
    have hsuffix := ReferenceFirstCollectionEmptyStreamSuffix.actual_first_collection_empty_stream_suffix
        rate z rewards C_star C_h count hcross hspan hshortRun stream
    dsimp only at hsuffix
    obtain ⟨_hb, hBbound, _hprefixFinal, _hprefixCoordinator, _hrecordsSplit,
      _hfinal, _hdrop, hemptyTail, htail⟩ := hsuffix
    have hQwindow := ReferenceFirstCollectionPendingObservation.Q_window
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
      z count hcross hspan hshortEpoch stream
    let actualB := ReferenceCollectionPhaseHistory.collectionWindow E.records
      (ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records).length
    have hBactual : B = actualB := by
      simp [B, actualB, w, hRE]
    have hBlen : B.length = actualB.length := congrArg List.length hBactual
    have hBboundLocal : w + B.length ≤ count := by
      simpa [actualB, B, w, hRE] using hBbound
    have hQwindow' (k : Fin B.length) :
        ReferenceFirstCollectionPendingObservation.Q rate rewards C_star C_h b
          B[k.val].input.time z =
          if k.val = 0 then Finset.univ else
            if hk : k.val < out.ell then
              (out.ledgers ⟨k.val - 1, by omega⟩).pending else ∅ := by
      have hk' : k.val < actualB.length := by
        rw [← hBactual]
        exact k.isLt
      let k' : Fin actualB.length := ⟨k.val, hk'⟩
      have hq := hQwindow k'
      simpa [b, actualB, B, w, hRE, k'] using hq
    by_cases hellEnd : out.ell = B.length
    · intro k
      dsimp only
      let r := B[k.val]
      have hklt : k.val < out.ell := by omega
      have hQ := hQwindow' k
      by_cases hk0 : k.val = 0
      · left
        rw [hQ]
        simp [hk0]
        have htwo : 2 ≤ p.m := p.two_le_m
        exact Finset.univ_nonempty_iff.mpr ⟨⟨0, by omega⟩⟩
      · have hkpos : 0 < k.val := Nat.pos_of_ne_zero hk0
        have hsub : k.val - 1 + 1 = k.val := by omega
        have hpendingIndex : k.val - 1 < out.ell := by
          exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) hklt
        have hpending := out.pending_before_last
          ⟨k.val - 1, hpendingIndex⟩ (by rw [hsub]; exact hklt)
        left
        rw [hQ]
        simpa [hk0, hklt] using hpending
    · have hEllB : out.ell < B.length := by
        have hwithin : out.ell ≤ B.length := by
          rw [← hwindow]
          exact out.withinWindow
        omega
      have hEllActual : out.ell < actualB.length := by
        rw [← hBactual]
        exact hEllB
      have hlastEmpty : stream.ledger.pending = ∅ := hemptyTail hEllActual
      have hlastWindowIndex : stream.last.val < out.window.length :=
        Nat.lt_of_lt_of_le stream.last.isLt out.withinWindow
      have hlastWindowRecord : out.window[stream.last.val] = stream.record :=
        Option.some.inj ((List.getElem?_eq_getElem hlastWindowIndex).symm.trans stream.recordAt)
      cases houtcome : stream.outcome with
      | exhausted hnonempty _ _ _ _ =>
          have hpending : stream.ledger.pending.Nonempty := by
            simpa [houtcome] using hnonempty
          exfalso
          exact (Finset.not_nonempty_iff_eq_empty.mpr hlastEmpty) hpending
      | empty data =>
          cases hboundary : data.nextBoundary with
          | terminal htime _hcursor =>
              have hlastAligned := out.alignment ⟨stream.last.val, hlastWindowIndex⟩
              have hlastTime : stream.record.input.time.val + 1 =
                  ReferenceFirstCollectionReadyStream.startTime (rate := rate)
                    z rewards C_star C_h + w + out.ell := by
                calc
                  stream.record.input.time.val + 1 =
                      out.window[stream.last.val].input.time.val + 1 := by
                    rw [hlastWindowRecord]
                  _ = ReferenceFirstCollectionReadyStream.startTime (rate := rate)
                      z rewards C_star C_h + w + 1 + stream.last.val := by
                    have ht := hlastAligned.2
                    rw [← hwEpoch] at ht
                    exact ht
                  _ = ReferenceFirstCollectionReadyStream.startTime (rate := rate)
                      z rewards C_star C_h + w + out.ell := by
                    have hlast : stream.last.val + 1 = out.ell := by
                      change stream.last.val + 1 = stream.stream.ell
                      exact stream.lastIsLast
                    omega
              have hstrict : ReferenceFirstCollectionReadyStream.startTime
                    (rate := rate) z rewards C_star C_h + w + out.ell < p.T := by
                have hprefix : w + out.ell < count := by
                  have hlt := Nat.add_lt_add_left hEllB w
                  exact Nat.lt_of_lt_of_le hlt hBboundLocal
                calc
                  _ < ReferenceFirstCollectionReadyStream.startTime (rate := rate)
                      z rewards C_star C_h + count := by omega
                  _ ≤ p.T := hspan
              rw [hlastTime] at htime
              omega
          | next _before _currentStart x _input _stateIsPrior _timeIsNext _rows
              _selected _rewards equalsWindow _equalsRun dispatchData =>
              let rEll : Record (p := p) (rate := rate) := B[out.ell]
              have hgetWindow : out.window[out.ell]? = some rEll := by
                rw [hwindow]
                exact List.getElem?_eq_getElem hEllB
              have hx : x = rEll.input := equalsWindow rEll hgetWindow
              have hnotLater : ReferenceCollectionPhaseHistory.laterChosen rEll.input = false := by
                have h := collectionWindow_laterChosen_false_of_pos R w out.ell
                  (by have hp := out.positiveLength; omega) hEllB
                simpa [B, rEll] using h
              have hfailed := failed_checked_sampler_falls_to_dagger
                x out.payload stream.ledger out.saved dispatchData data.cutoffLastService
                (by simpa [hx] using hnotLater)
              have hstateCoord : rEll.input.state.coordinator =
                  .collection out.payload stream.ledger out.saved := by
                simpa [hx, stream.ledgerIsLast] using dispatchData.actualState
              have hnextDagger : rEll.output.next.coordinator = .dagger := by
                rw [rEll.output_eq, ← hx]
                exact hfailed.2
              have hparam : (param rEll.input).isSome = true := by
                change (ReferenceLaterSamplerParameterMeasurability.parameters?
                  rEll.input).isSome = true
                rw [← hx]
                exact hfailed.1
              have hEllOut : out.ell < out.window.length := by
                rw [hwindow]
                exact hEllB
              have hrecordGlobal : E.records[w + out.ell]? = some rEll := by
                have ha := out.alignment ⟨out.ell, hEllOut⟩
                simpa [E, w, B, hRE, hwindow, rEll,
                  ReferenceFirstCollectionReadyStream.actualEpoch] using ha.1
              have hglobalIndex : w + out.ell < E.records.length :=
                (List.getElem?_eq_some_iff.mp hrecordGlobal).1
              have hglobalRecord : E.records[w + out.ell]'hglobalIndex = rEll :=
                Option.some.inj ((List.getElem?_eq_getElem hglobalIndex).symm.trans hrecordGlobal)
              have hglobalDagger :
                  (E.records[w + out.ell]'hglobalIndex).output.next.coordinator = .dagger := by
                rw [hglobalRecord]
                exact hnextDagger
              have hdaggerAfter :=
                _root_.Bandits.Support.ReferenceFirstCollectionCalendarPendingSplit.Connected.coordinator_dagger_after_get
                  hconnected (w + out.ell) hglobalIndex hglobalDagger
              intro k
              dsimp only
              let r : Record (p := p) (rate := rate) := B[k.val]
              by_cases hk0 : k.val = 0
              · left
                rw [hQwindow' k]
                simp [hk0]
                have htwo : 2 ≤ p.m := p.two_le_m
                exact Finset.univ_nonempty_iff.mpr ⟨⟨0, by omega⟩⟩
              · have hkpos : 0 < k.val := Nat.pos_of_ne_zero hk0
                by_cases hkle : k.val < out.ell
                · have hsub : k.val - 1 + 1 = k.val := by omega
                  have hpendingIndex : k.val - 1 < out.ell := by
                    exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) hkle
                  have hpending := out.pending_before_last
                    ⟨k.val - 1, hpendingIndex⟩ (by rw [hsub]; exact hkle)
                  left
                  rw [hQwindow' k]
                  simpa [hk0, hkle] using hpending
                · have hellk : out.ell ≤ k.val := by omega
                  by_cases hkeq : out.ell = k.val
                  · have hrecordEqLocal : B[k.val] = rEll := by
                      have hfin : (⟨out.ell, hEllB⟩ : Fin B.length) = k :=
                        Fin.ext hkeq
                      simpa [rEll] using
                        (congrArg (fun i : Fin B.length => B[i.val]) hfin).symm
                    right
                    left
                    refine ⟨⟨out.payload, stream.ledger, out.saved, ?_, ?_⟩,
                      ?_, ?_, ?_⟩
                    · rw [hrecordEqLocal]
                      exact hstateCoord
                    · exact dispatchData.emptyPending
                    · rw [hrecordEqLocal]
                      exact hparam
                    · rw [hrecordEqLocal]
                      exact hnextDagger
                    · intro v r' htimeFuture hactual
                      rw [hrecordEqLocal] at htimeFuture
                      have htimeEll : rEll.input.time.val =
                          ReferenceFirstCollectionReadyStream.startTime (rate := rate)
                            z rewards C_star C_h + w + out.ell := by
                        have ht := htail ⟨out.ell, hEllActual⟩ (Nat.le_refl _)
                        dsimp only at ht
                        rcases ht with ⟨_, _, _, htime, _, _, _, _, _, _⟩
                        have hgetActual : B[out.ell]? = some actualB[out.ell] := by
                          rw [hBactual]
                          exact List.getElem?_eq_getElem hEllActual
                        have hrecordActual : rEll = actualB[out.ell]'hEllActual := by
                          apply Option.some.inj
                          exact (List.getElem?_eq_getElem hEllB).symm.trans hgetActual
                        rw [hrecordActual]
                        simpa [actualB, E, w, hRE,
                          ReferenceFirstCollectionReadyStream.startTime] using htime
                      let j := v.val - b
                      have hj : j < count := by
                        simp [j, count, b]
                        omega
                      have hstartLE : b ≤ v.val := by rw [← hstart]; omega
                      have hactualLaunch := ReferenceSourcePrefixHistoryFiltration.actualRecord_on_launch
                        rate rewards C_star C_h v z initial hlaunch
                          hstartLE
                      let canonical := ReferenceAssignmentPayloadChronology.actualRunRecordAt
                        initial z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)
                        rewards b j (by omega) hmode
                      have hcanonical : r' = canonical := by
                        apply Option.some.inj
                        exact (hactualLaunch.symm.trans hactual).symm
                      have hrunGet : E.records[j]? = some r' := by
                        have hget := ReferenceLocalReleaseGateChronology.run_record_at
                          initial z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)
                          rewards b hmode count hspan ⟨j, hj⟩
                        have hjE : j < E.records.length := by rw [hElen]; exact hj
                        have hget' : E.records[j]? = some canonical := by
                          rw [List.getElem?_eq_getElem hjE]
                          simpa [canonical, E, initial, b,
                            ReferenceFirstCollectionReadyStream.startTime,
                            ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun,
                            hphysicalStart] using
                            hget
                        simpa [hcanonical] using hget'
                      have hcanonTime : canonical.input.time.val = b + j := by
                        simp [canonical, ReferenceAssignmentPayloadChronology.actualRunRecordAt,
                          ReferenceActivePhysicalHorizon.roundInputAt]
                      have hjTime : b + j = v.val := by
                        dsimp [j]
                        omega
                      have hfutureIndex : w + out.ell < j := by
                        rw [hstart] at htimeEll
                        omega
                      have hrecordIndex : j < E.records.length :=
                        (List.getElem?_eq_some_iff.mp hrunGet).1
                      have hdagger := hdaggerAfter j hfutureIndex hrecordIndex
                      have hrecordEq : E.records[j]'hrecordIndex = r' :=
                        Option.some.inj ((List.getElem?_eq_getElem hrecordIndex).symm.trans hrunGet)
                      rw [hrecordEq] at hdagger
                      exact hdagger
                  · right
                    right
                    have hglobal : w + out.ell < w + k.val := by omega
                    have hrecordWindow :
                        E.records[w + k.val]? = some r := by
                      have hindex : k.val < out.window.length := by
                        rw [hwindow]
                        exact k.isLt
                      have ha := out.alignment ⟨k.val, hindex⟩
                      simpa [E, w, B, hRE, hwindow, r,
                        ReferenceFirstCollectionReadyStream.actualEpoch] using ha.1
                    have hrecordIndex : w + k.val < E.records.length :=
                      (List.getElem?_eq_some_iff.mp hrecordWindow).1
                    have hrecordEq : E.records[w + k.val]'hrecordIndex = r :=
                      Option.some.inj ((List.getElem?_eq_getElem hrecordIndex).symm.trans hrecordWindow)
                    have hdagger := hdaggerAfter (w + k.val) hglobal hrecordIndex
                    rw [hrecordEq] at hdagger
                    exact hdagger

end Bandits.Support.ReferenceFirstCollectionCalendarPendingSplit
