/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionCurrentNumericalCell
public import Bandits.Support.ReferenceFirstAdmissionNextDispatch

import Lean.Elab.Tactic.Omega

/-!
# Stored bounds at the original first collection invocation

Sources: `sources/zip4/manuscript/06_interruptions.tex:363-426`,
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-79`, and
`sources/zip4/manuscript/04_slow_fast_learner.tex:140-188`.

The first prechoice invocation in the complete original physical suffix is
immediately after the initialized stream's first empty-pending FINISH. Its
stored-register bounds and canonical reconstruction are produced without a
successful assignment sample. No calendar queue truth or probability law is
asserted here.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions
open ReferenceFirstCollectionReadyStream
open ReferenceFirstCollectionStreamEmptyDispatch

namespace Bandits.Support.ReferenceFirstCollectionCallStoredBounds

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

private theorem connected_adjacent
    {initial final : ReferenceActivePhysicalStep.State p rate}
    {records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))}
    (hc : ReferenceActivePhysicalHorizon.Connected initial records final)
    (n : ℕ) (r q : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : records[n]? = some r) (hq : records[n + 1]? = some q) :
    q.input.state = r.output.next := by
  induction records generalizing initial n with
  | nil => simp only [List.getElem?_nil, reduceCtorEq] at hr
  | cons head rest ih =>
      cases n with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hr
          subst head
          cases rest with
          | nil => simp at hq
          | cons next tail =>
              simp only [Nat.zero_add, List.getElem?_cons_succ, List.getElem?_cons_zero,
                Option.some.injEq] at hq
              subst next
              exact hc.2.1
      | succ n =>
          exact ih hc.2 n (by simpa only [List.getElem?_cons_succ] using hr)
            (by simpa only [Nat.succ_add, List.getElem?_cons_succ] using hq)

private theorem parameters_none_of_pending
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate) (saved : Option (Fin p.T × Bool))
    (hcoord : x.state.coordinator = .collection payload ledger saved)
    (hp : ledger.pending.Nonempty) :
    ReferenceLaterAssignmentFibreStep.parameters? x = none := by
  unfold ReferenceLaterAssignmentFibreStep.parameters?
  simp only [hcoord]
  split
  · unfold ReferenceLaterAssignmentFibreStep.collectionParameters?
    split
    · rfl
    · split
      · simp only [ReferenceActivePhysicalStep.collectionInput, hp, ite_true]
      · rfl
  · rfl

private theorem selected_parameters_present
    {eta : ReferencePrelaunchFollower.LearningRate}
    (old : AssignmentStartPayload.Input p eta)
    (ledger : LaterAssignmentStartOperation.LocalLedger old)
    (instruction : CoordinatorPhaseClock.AssignmentStartInstruction p)
    (consistent : LaterAssignmentStartOperation.LocalConsistency old ledger)
    (out : AssignmentScoreReconstruction.ReconstructedStart ledger instruction)
    (hrec : AssignmentScoreReconstruction.reconstructLaterStart ledger instruction =
      .success ledger instruction out) :
    (LaterAssignmentStartMeasurability.selectedSamplerParameters? old
      ⟨ledger, instruction, consistent⟩).isSome = true := by
  rw [LaterAssignmentJointCodeMeasurability.selectedSamplerParameters?_eq_match]
  have hpair : (⟨AssignmentScoreReconstruction.reconstructLaterStart ledger instruction, rfl⟩ :
      LaterAssignmentStartOperation.ReconstructionCall old ledger instruction) =
      ⟨.success ledger instruction out, hrec⟩ := by
    apply LaterAssignmentStartOperation.ReconstructionCall.ext
    exact hrec
  unfold LaterAssignmentStartOperation.decideReconstruction
  rw [hpair]
  rfl

private theorem parameters_present_of_reconstruction
    (x : CoordinatorRoundDispatch.CollectionInput p)
    (core : CoordinatorRoundDispatch.CollectionCoreValid x)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (hstart : CoordinatorPhaseClock.startRound p x.etaReal x.time x.clock x.ledger.pending = .ok started)
    (instruction : CoordinatorPhaseClock.AssignmentStartInstruction p)
    (hi : started.assignmentStart = some instruction)
    (hp : x.ledger.pending = ∅)
    (out : AssignmentScoreReconstruction.ReconstructedStart
      (CoordinatorRoundDispatch.collectionOperationLedger x core.payload_n_eq) instruction)
    (hrec : AssignmentScoreReconstruction.reconstructLaterStart
      (CoordinatorRoundDispatch.collectionOperationLedger x core.payload_n_eq) instruction =
        .success _ instruction out) :
    (ReferenceLaterAssignmentFibreStep.collectionParameters? x).isSome = true := by
  unfold ReferenceLaterAssignmentFibreStep.collectionParameters?
  simp only [hstart]
  rw [dite_eq_left core]
  simp only [hp, Finset.not_nonempty_empty, ite_false, hi]
  exact selected_parameters_present x.payload _ instruction _ out hrec

private theorem laterChosen_parameters_present
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (h : ReferenceCollectionPhaseHistory.laterChosen x = true) :
    (ReferenceLaterAssignmentFibreStep.parameters? x).isSome = true := by
  have hp := ReferenceLaterAssignmentFibreStep.parameters?_eq_physicalDispatch x
  change ReferenceLaterAssignmentFibreStep.parameters? x =
    ReferenceLaterAssignmentFibreStep.dispatchParameters? (ReferenceActivePhysicalStep.prepare x).coordinator at hp
  cases he : (ReferenceActivePhysicalStep.prepare x).coordinator with
  | collection payload ledger clock cutoff outcome =>
      cases outcome <;> simp only [ReferenceCollectionPhaseHistory.laterChosen, he,
        Bool.false_eq_true] at h
      rename_i core consistent started hstart instruction hi output hlocal clockData installed selection
      rw [he] at hp
      rw [hp]
      simp only [ReferenceLaterAssignmentFibreStep.dispatchParameters?,
        ReferenceLaterAssignmentFibreStep.outcomeParameters?]
      exact selected_parameters_present _ _ instruction consistent
        output.reconstruction output.reconstruction_eq
  | first outcome => simp only [ReferenceCollectionPhaseHistory.laterChosen, he, Bool.false_eq_true] at h
  | live r q base outcome => simp only [ReferenceCollectionPhaseHistory.laterChosen, he, Bool.false_eq_true] at h
  | invalidCollectionCutoff => simp only [ReferenceCollectionPhaseHistory.laterChosen, he, Bool.false_eq_true] at h
  | dagger => simp only [ReferenceCollectionPhaseHistory.laterChosen, he, Bool.false_eq_true] at h

private theorem takeWhile_stop {A : Type*} (f : A → Bool) (xs : List A)
    (h : (xs.takeWhile f).length < xs.length) :
    ∃ r, xs[(xs.takeWhile f).length]? = some r ∧ f r = false := by
  induction xs with
  | nil => simp at h
  | cons head rest ih =>
      cases hf : f head with
      | false => exact ⟨head, by simp [List.takeWhile, hf], hf⟩
      | true =>
          simp only [List.takeWhile_cons, hf, ↓reduceIte, List.length_cons, Nat.add_lt_add_iff_right] at h
          obtain ⟨r, hr, hfr⟩ := ih h
          exact ⟨r, by simpa only [List.takeWhile_cons, hf, ↓reduceIte,
            List.length_cons, List.getElem?_cons_succ] using hr, hfr⟩

private theorem ready_parameters_none
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate) (saved : Option (Fin p.T × Bool))
    (h : ReferenceContinuingCollectionStartDomains.continuingCollectionReadyDomain x payload ledger saved) :
    ReferenceLaterAssignmentFibreStep.parameters? x = none := by
  obtain ⟨hcoord, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hp, _⟩ := h
  exact parameters_none_of_pending x payload ledger saved hcoord hp

private theorem stream_record_at
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (count : ℕ) (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hs : startTime (rate := rate) source rewards C_star C_h + count ≤ p.T)
    (hk : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (actualEpoch (rate := rate) source rewards C_star C_h hc count hs).records).length < count)
    (out : ActualInitializedStreamOutput source rewards C_star C_h count hc hs hk)
    (i : Fin out.ell) (r : ReferenceFirstCollectionReadyStream.Record p rate) (hr : out.window[i.val]? = some r) :
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (actualEpoch (rate := rate) source rewards C_star C_h hc count hs).records).length
    (actualEpoch (rate := rate) source rewards C_star C_h hc count hs).records[w + i.val]? = some r ∧
      r.input.time.val = startTime (rate := rate) source rewards C_star C_h + w + i.val := by
  have hi : i.val < out.window.length := lt_of_lt_of_le i.isLt out.withinWindow
  have heq : out.window[i.val] = r :=
    Option.some.inj ((List.getElem?_eq_getElem hi).symm.trans hr)
  have h := out.alignment ⟨i.val, hi⟩
  rw [heq] at h
  dsimp only at h
  exact ⟨h.1, by omega⟩

private theorem window_stop
    (records : List (ReferenceFirstCollectionReadyStream.Record p rate)) (w : ℕ) (hw : w < records.length)
    (hstop : w + (ReferenceCollectionPhaseHistory.collectionWindow records w).length < records.length) :
    ∃ r, records[w + (ReferenceCollectionPhaseHistory.collectionWindow records w).length]? = some r ∧
      ReferenceCollectionPhaseHistory.laterChosen r.input = true := by
  let f := fun r : ReferenceFirstCollectionReadyStream.Record p rate => !ReferenceCollectionPhaseHistory.laterChosen r.input
  let tail := records.drop (w + 1)
  have hhead : ((records.drop w).take 1).length = 1 := by
    simp only [List.length_take, List.length_drop]
    omega
  have hlen : (ReferenceCollectionPhaseHistory.collectionWindow records w).length =
      1 + (tail.takeWhile f).length := by
    simp only [ReferenceCollectionPhaseHistory.collectionWindow, List.length_append, hhead]
    rfl
  have htail : (tail.takeWhile f).length < tail.length := by
    have ht : tail.length = records.length - (w + 1) := List.length_drop
    omega
  obtain ⟨r, hr, hfr⟩ := takeWhile_stop f tail htail
  refine ⟨r, ?_, ?_⟩
  · have hi : w + (ReferenceCollectionPhaseHistory.collectionWindow records w).length =
        w + 1 + (tail.takeWhile f).length := by omega
    rw [hi]
    simpa only [tail, List.getElem?_drop, Nat.add_comm] using hr
  · cases hb : ReferenceCollectionPhaseHistory.laterChosen r.input with
    | false => simp only [f, hb, Bool.not_false, Bool.true_eq_false] at hfr
    | true => rfl

private theorem canonical_next_dispatch
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (l : ReferenceActivePhysicalStep.Ledger rate) (saved : Option (Fin p.T × Bool))
    (k : ActualNextDispatch x payload l saved)
    (hbound : ∀ a c, l.cutoffRegisters a = some c → c.lastService ≤ c.score) :
    ∃ k' : ActualNextDispatch x payload l saved,
      (ReferenceLaterAssignmentFibreStep.parameters? x).isSome = true ∧
      k'.operationLedger = CoordinatorRoundDispatch.collectionOperationLedger
        (ReferenceActivePhysicalStep.collectionInput x payload l
          (ReferenceActivePhysicalStep.collectionClock payload l saved k'.cutoffTime) k'.cutoffTime)
        k'.core.payload_n_eq := by
  classical
  obtain ⟨cutoff, hcut, core, started, hstart, instruction, hi, consistent,
    ht, hkind, hprep, hiff, hcases⟩ := k.classification
  rcases hcases with hbad | ⟨out, hrec, _⟩
  · obtain ⟨a, c, hc, hlt, _⟩ := hbad
    exact ((Nat.not_lt_of_ge (hbound a c hc)) hlt).elim
  · let k' : ActualNextDispatch x payload l saved := {
      actualState := k.actualState
      validLedger := k.validLedger
      readyPhase := k.readyPhase
      sigma := k.sigma
      order := k.order
      cutoffBeforeCursor := k.cutoffBeforeCursor
      cursor := k.cursor
      freeze := k.freeze
      assignment := k.assignment
      emptyPending := k.emptyPending
      unitAnchor := k.unitAnchor
      currentMassBounds := k.currentMassBounds
      currentServiceSpan := k.currentServiceSpan
      nextBankCheck := k.nextBankCheck
      classification := k.classification
      cutoffTime := cutoff
      cutoffTimeEq := hcut
      core := core
      started := started
      startCheck := hstart
      instruction := instruction
      assignmentStart := hi
      operationLedger := _
      consistent := consistent
      instructionTime := ht
      expectedKind := hkind
      preparedCoordinator := hprep
      correctedFailureIff := hiff
      correctedFailureAbsent := by intro he; rw [he] at hrec; cases hrec
      reconstructed := out
      reconstructionSuccess := hrec }
    refine ⟨k', ?_, rfl⟩
    have hcutValid : 1 ≤ l.cutoff ∧ l.cutoff ≤ p.T := by
      have ht := cutoff.isLt
      omega
    have hindex : (⟨l.cutoff - 1, by omega⟩ : Fin p.T) = cutoff := by
      apply Fin.ext
      dsimp
      omega
    simp only [ReferenceLaterAssignmentFibreStep.parameters?, k.actualState,
      dite_eq_left hcutValid, hindex]
    exact parameters_present_of_reconstruction _ core started hstart instruction hi
      k.emptyPending out hrec

/-- The original first prechoice call is the actual next input after the first
empty-pending FINISH on the complete suffix. The same stored ledger has all
cutoff registers, the cutoff last-service bounds and the exact increment
span bound. Reconstruction succeeds before any checked-sampler outcome is
selected. The operation ledger is the literal canonical collection ledger. -/
theorem firstCell_stored_bounds
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hz : z ∈ ReferenceCalendarCollectionCallControlLaw.firstCell
      rate rewards C_star C_h u t) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let s := startTime (rate := rate) z rewards C_star C_h
    let count := p.T - s
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
    ∃ (n : ℕ) (r : ReferenceFirstCollectionSamplerCall.RoundRecord p rate)
      (theta : ReferenceFirstCollectionSamplerCall.Theta p),
      R[n]? = some r ∧ r.input.time = t ∧
      ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some r ∧
      ReferenceFirstCollectionSamplerCall.collectionCallAt r = some (u, theta) ∧
      r.input.rows = z.1.2 ∧
      r.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p z ∧
      r.input.rewards = rewards ∧
      (∀ j < n, ∀ q, R[j]? = some q →
        ReferenceLaterSamplerParameterMeasurability.parameters? q.input = none) ∧
      s + n = t.val ∧
      ∃ hc : (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true,
      ∃ hs : s + count ≤ p.T,
      ∃ hrecords : R = (actualEpoch (rate := rate) z rewards C_star C_h hc count hs).records,
      ∃ hk : w < count,
      let hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
          (actualEpoch (rate := rate) z rewards C_star C_h hc count hs).records).length < count := by
        rw [← hrecords]
        exact hk
      ∃ f : ActualInitializedStreamDispatch z rewards C_star C_h count hc hs hshort,
      ∃ e : EmptyPendingBoundary z rewards C_star C_h count hc hs hshort
          f.stream f.last f.ledger f.record,
        f.outcome = .empty e ∧
        u.val = s + w ∧ n = w + f.stream.ell ∧
        R[n - 1]? = some f.record ∧
        r.input.state = f.record.output.next ∧
        r.input.state.coordinator = .collection f.stream.payload f.ledger f.stream.saved ∧
        f.ledger.cutoff = u.val + 1 ∧ f.ledger.cursor = t.val + 1 ∧
        f.ledger.pending = ∅ ∧
        (∀ arm, (∃ q, f.ledger.currentRegisters arm = some q) ∧
          ∃ c, f.ledger.cutoffRegisters arm = some c) ∧
        (∀ arm c, f.ledger.cutoffRegisters arm = some c →
          c.lastService ≤ c.score ∧ c.lastService ≤ 4 * rate.n) ∧
        (∀ arm, f.ledger.increment arm ≤
          4 * rate.n * (min f.ledger.cursor f.ledger.freezeAt - f.ledger.cutoff)) ∧
        ∃ k : ActualNextDispatch r.input f.stream.payload f.ledger f.stream.saved,
          k.operationLedger = CoordinatorRoundDispatch.collectionOperationLedger
            (ReferenceActivePhysicalStep.collectionInput r.input f.stream.payload f.ledger
              (ReferenceActivePhysicalStep.collectionClock f.stream.payload f.ledger
                f.stream.saved k.cutoffTime) k.cutoffTime) k.core.payload_n_eq ∧
          k.cutoffTime = u ∧ k.instruction.time = t := by
  classical
  obtain ⟨n, r, theta, hr, ht, har, hcall, hrows, hselected, hrewards, hearlier⟩ :=
    ReferenceFirstCollectionCurrentNumericalCell.firstCell_record
      rate rewards C_star C_h u t z hz
  obtain ⟨old, ledger, saved, hcoord, hcut, hparameters⟩ :=
    (ReferenceFirstCollectionSamplerCall.collectionCallAt_spec r u theta).mp hcall
  have hpresent : (ReferenceLaterAssignmentFibreStep.parameters? r.input).isSome = true := by
    change ReferenceLaterAssignmentFibreStep.parameters? r.input = some theta at hparameters
    rw [hparameters]
    rfl
  have hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true := by
    cases hl : ReferenceCorrectedInitializationLaunch.correctedLaunch rate z rewards C_star C_h with
    | none =>
        simp only [ReferenceCompletePhysicalHistory.completeSuffixRecords, hl, dite_true,
          List.getElem?_nil, reduceCtorEq] at hr
    | some initial =>
        exact (ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
          rate z rewards C_star C_h).mp (by rw [hl]; rfl)
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let s := startTime (rate := rate) z rewards C_star C_h
  let count := p.T - s
  have hsle : s ≤ p.T := ReferenceCompletePhysicalHistory.physicalStart_le_T
    rate z rewards C_star C_h
  have hs : s + count ≤ p.T := by omega
  let initial := ReferenceFirstCollectionEpochAlignment.actualLaunchState rate z rewards C_star C_h hc
  let epoch := actualEpoch (rate := rate) z rewards C_star C_h hc count hs
  have hrecords : R = epoch.records :=
    ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
      rate z rewards C_star C_h initial (Option.some_get _).symm
  let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow epoch.records).length
  have hwR : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length = w := by
    rw [hrecords]
  have hn : n < count := by
    have h := (List.getElem?_eq_some_iff.mp hr).1
    rw [ReferenceCompletePhysicalHistory.completeSuffixRecords_length] at h
    exact h
  have hntime := ReferenceFirstCollectionRenewalRecordingFeedback.complete_record_time
    rate z rewards C_star C_h n r hr
  change r.input.time.val = s + n at hntime
  have hnt : s + n = t.val := by rw [ht] at hntime; exact hntime.symm
  have hrEpoch : epoch.records[n]? = some r := hrecords ▸ hr
  have hw : w < n := by
    have h := ReferenceFirstCollectionCurrentNumericalCell.collection_after_firstLive
      rate rewards C_star C_h z n r hr old ledger saved hcoord
    rw [show (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length = w from hwR] at h
    exact h
  have hk : w < count := lt_trans hw hn
  obtain ⟨f⟩ := actual_initialized_first_collection_stream_empty_dispatch
    rate z rewards C_star C_h count hc hs hk
  have hlength : epoch.records.length = count :=
    ReferenceActivePhysicalHorizon.run_record_count _ _ _ _ _ _ _ _
  have hwindow : f.stream.window = ReferenceCollectionPhaseHistory.collectionWindow epoch.records w :=
    f.stream.windowIsActual
  have hprefix : w + f.stream.ell ≤ n := by
    by_contra hnot
    have hi : n - w < f.stream.ell := by omega
    obtain ⟨j, q, incoming, cell, _hj, hrecord, _, _⟩ :=
      f.stream.cell_at ⟨n - w, hi⟩ (by change 0 < n - w; omega)
    have hrun := (stream_record_at z rewards C_star C_h count hc hs hk
      f.stream ⟨n - w, hi⟩ q hrecord).1
    have hin : w + (n - w) = n := by omega
    change epoch.records[w + (n - w)]? = some q at hrun
    rw [hin, hrEpoch] at hrun
    have heq : r = q := Option.some.inj hrun
    have hnone := ready_parameters_none q.input f.stream.payload incoming f.stream.saved cell.readyInput
    rw [← heq] at hnone
    rw [hnone] at hpresent
    cases hpresent
  have hend : n ≤ w + f.stream.window.length := by
    by_contra hnot
    have hstop : w + (ReferenceCollectionPhaseHistory.collectionWindow epoch.records w).length <
        epoch.records.length := by rw [← hwindow, hlength]; omega
    obtain ⟨q, hget, hchosen⟩ := window_stop epoch.records w (by omega) hstop
    have hgetR : R[w + f.stream.window.length]? = some q := by
      rw [hrecords, hwindow]
      exact hget
    have hnone := hearlier (w + f.stream.window.length) (by omega) q hgetR
    have hsome := laterChosen_parameters_present q.input hchosen
    change ReferenceLaterAssignmentFibreStep.parameters? q.input = none at hnone
    rw [hnone] at hsome
    cases hsome
  have hrecord := stream_record_at z rewards C_star C_h count hc hs hk
    f.stream f.last f.record f.recordAt
  change epoch.records[w + f.last.val]? = some f.record ∧
    f.record.input.time.val = s + w + f.last.val at hrecord
  have hfinalTime : f.record.input.time.val + 1 = s + w + f.stream.ell := by
    have hl := f.lastIsLast
    omega
  cases houtcome : f.outcome with
  | exhausted hp hex hcutoff hinc boundary =>
      exfalso
      have hm : w + f.stream.ell = n := by omega
      have hadj := connected_adjacent epoch.connected (w + f.last.val) f.record r
        hrecord.1 (by
          have he : w + f.last.val + 1 = n := by have hl := f.lastIsLast; omega
          rw [he]
          exact hrEpoch)
      have hcnext : r.input.state.coordinator =
          .collection f.stream.payload f.ledger f.stream.saved := by
        rw [hadj]
        exact f.actualNextCoordinator
      have hnone := parameters_none_of_pending r.input f.stream.payload f.ledger
        f.stream.saved hcnext hp
      rw [hnone] at hpresent
      cases hpresent
  | empty e =>
      cases hb : e.nextBoundary with
      | terminal hT hcursor =>
          exfalso
          have htlt := t.isLt
          omega
      | next hbefore hafter x hinput hstate htime hrowsNext hselectedNext hrewardsNext hwindowNext hrunNext k0 =>
          obtain ⟨k, hsome, hliteral⟩ := canonical_next_dispatch x f.stream.payload f.ledger f.stream.saved
            k0 (fun arm c hc => (f.cutoffLastService arm c hc).1)
          have hm : w + f.stream.ell = n := by
            by_contra hne
            have hlt : w + f.stream.ell < n := by omega
            have hretained : w + f.stream.ell < epoch.records.length := by omega
            let q := epoch.records[w + f.stream.ell]'hretained
            have hget : epoch.records[w + f.stream.ell]? = some q :=
              List.getElem?_eq_getElem hretained
            have hx := hrunNext _ hget
            have hgetR : R[w + f.stream.ell]? = some q := by
              rw [hrecords]
              exact hget
            have hnone := hearlier (w + f.stream.ell) hlt _ hgetR
            rw [← hx] at hnone
            change ReferenceLaterAssignmentFibreStep.parameters? x = none at hnone
            rw [hnone] at hsome
            cases hsome
          have hx : x = r.input := hrunNext r (by rw [hm]; exact hrEpoch)
          have hstateAt : r.input.state = f.record.output.next := by
            rw [← hx]
            exact hstate
          obtain ⟨kAt, hliteralAt⟩ :
              ∃ kAt : ActualNextDispatch r.input f.stream.payload f.ledger f.stream.saved,
                kAt.operationLedger = CoordinatorRoundDispatch.collectionOperationLedger
                  (ReferenceActivePhysicalStep.collectionInput r.input f.stream.payload f.ledger
                    (ReferenceActivePhysicalStep.collectionClock f.stream.payload f.ledger
                      f.stream.saved kAt.cutoffTime) kAt.cutoffTime) kAt.core.payload_n_eq := by
            rw [← hx]
            exact ⟨k, hliteral⟩
          have hcoordEq := kAt.actualState.symm.trans hcoord
          obtain ⟨hpayload, hledger, hsaved⟩ :=
            ReferenceActivePhysicalStep.CoordinatorConfiguration.collection.inj hcoordEq
          have hcutoff : f.ledger.cutoff = u.val + 1 := by rw [hledger]; exact hcut
          have hcontext := (f.stream.context f.last).2.1
          have hstartCut : f.ledger.cutoff = s + w + 1 := by
            rw [f.ledgerIsLast, hcontext]
            exact f.stream.cutoff.ledgerCutoff
          have hu : u.val = s + w := by omega
          have hprevious : R[n - 1]? = some f.record := by
            rw [hrecords]
            have he : n - 1 = w + f.last.val := by have hl := f.lastIsLast; omega
            rw [he]
            exact hrecord.1
          have hcutTime : kAt.cutoffTime = u := by
            apply Fin.ext
            have he := kAt.cutoffTimeEq
            omega
          refine ⟨n, r, theta, hr, ht, har, hcall, hrows, hselected, hrewards,
            hearlier, hnt, hc, hs, hrecords, ?_, ?_⟩
          · rw [hwR]
            exact hk
          · dsimp only
            refine ⟨f, e, houtcome, ?_, ?_, hprevious, hstateAt, kAt.actualState,
              hcutoff, ?_, e.pendingEmpty, e.allKnownRegisters,
              e.cutoffLastService, e.incrementGrowth, kAt, hliteralAt, hcutTime, ?_⟩
            · rw [hwR]
              exact hu
            · exact hm.symm.trans (congrArg (fun j => j + f.stream.ell) hwR.symm)
            · rw [kAt.cursor, ht]
            · exact kAt.instructionTime.trans ht

end Bandits.Support.ReferenceFirstCollectionCallStoredBounds
