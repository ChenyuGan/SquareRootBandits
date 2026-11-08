/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionRenewalInstallationCoupling
public import Bandits.Support.ReferenceFirstCollectionStreamEmptyDispatch

import Lean.Elab.Tactic.Omega

/-!
# The first actual renewal call and the first empty collection boundary

Sources: `sources/zip4/manuscript/06_interruptions.tex:40-69,399-423`,
`sources/zip4/manuscript/04_slow_fast_learner.tex:157-215`,
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-79`, and
`sources/zip4/manuscript/07_public_setup.tex:121-164`.

The call is the prechoice parameter projection of the original physical run.
The numerical conclusion concerns its stored registers. It does not identify
these registers with physical calendar scores or assert manuscript closure.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions
open ReferenceFirstCollectionRenewalAuxiliaryLaw
open ReferenceFirstCollectionReadyStream
open ReferenceFirstCollectionStreamEmptyDispatch

namespace Bandits.Support.ReferenceFirstCollectionRenewalCallFirstEmptyBoundary

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

private theorem record_time
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (s count : ℕ) (hs : s + count ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial s)
    (n : ℕ) (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : (ReferenceActivePhysicalHorizon.run initial rows J rewards s count hs active).records[n]? =
      some r) : r.input.time.val = s + n := by
  obtain ⟨hn, _⟩ := List.getElem?_eq_some_iff.mp hr
  have hcount := ReferenceActivePhysicalHorizon.run_record_count initial rows J rewards s count hs active
  have hn' : n < count := by omega
  have h := congrArg (fun xs : List ℕ => xs[n]?)
    (ReferenceActivePhysicalHorizon.run_time_values initial rows J rewards s count hs active)
  rw [List.getElem?_map, hr] at h
  simpa only [ReferenceActivePhysicalHorizon.calendar, List.getElem?_range' hn',
    ↓reduceIte, Nat.one_mul, Option.map_some, Option.some.injEq] using h

private theorem connected_prefix_input
    {initial middle final : ReferenceActivePhysicalStep.State p rate}
    (pref : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (rest : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (hfull : ReferenceActivePhysicalHorizon.Connected initial (pref ++ r :: rest) final)
    (hpref : ReferenceActivePhysicalHorizon.Connected initial pref middle) :
    r.input.state = middle := by
  induction pref generalizing initial with
  | nil => exact hfull.1.trans hpref.symm
  | cons head tail ih => exact ih hfull.2 hpref.2

private theorem run_input_state
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (s count : ℕ) (hs : s + count ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial s)
    (n : ℕ) (hn : n < count)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : (ReferenceActivePhysicalHorizon.run initial rows J rewards s count hs active).records[n]? =
      some r) :
    r.input.state =
      (ReferenceActivePhysicalHorizon.run initial rows J rewards s n (by omega) active).finalState := by
  obtain ⟨suffix, he⟩ := ReferenceCollectionPhaseHistory.run_records_prefix
    initial rows J rewards s n (count - n) (by omega) active
  have he' : (ReferenceActivePhysicalHorizon.run initial rows J rewards s count hs active).records =
      (ReferenceActivePhysicalHorizon.run initial rows J rewards s n (by omega) active).records ++ suffix := by
    simpa only [Nat.add_sub_of_le (Nat.le_of_lt hn)] using he
  have hlength := ReferenceActivePhysicalHorizon.run_record_count initial rows J rewards s n
    (by omega) active
  have hhead : suffix[0]? = some r := by
    rw [he', List.getElem?_append_right (by omega), hlength, Nat.sub_self] at hr
    exact hr
  cases suffix with
  | nil => simp only [List.getElem?_nil, reduceCtorEq] at hhead
  | cons head rest =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hhead
      subst head
      have hc := (ReferenceActivePhysicalHorizon.run initial rows J rewards s count hs active).connected
      rw [he'] at hc
      exact connected_prefix_input _ r rest hc
        (ReferenceActivePhysicalHorizon.run initial rows J rewards s n (by omega) active).connected

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

private theorem actual_first_call_index
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T)
    (z : ReferenceFirstCollectionRenewalInstallationCoupling.Source rate rewards C_star C_h u t)
    (d : ActualRenewalCall rate rewards C_star C_h u t z) :
    let s := startTime (rate := rate) z.val rewards C_star C_h
    let count := p.T - s
    ∃ hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z.val rewards C_star C_h rate)).crossing.isSome = true,
    ∃ hs : s + count ≤ p.T,
    let epoch := actualEpoch (rate := rate) z.val rewards C_star C_h hc count hs
    ∃ n : ℕ, n < count ∧ epoch.records[n]? = some d.record ∧ s + n = t.val ∧
      (∀ j < n, ∀ r, epoch.records[j]? = some r →
        ReferenceLaterAssignmentFibreStep.parameters? r.input = none) ∧
      (ReferenceLaterAssignmentFibreStep.parameters? d.record.input).isSome = true ∧
      (ReferenceFirstLiveConfirmationHistory.firstLiveWindow epoch.records).length < n := by
  classical
  dsimp only
  have hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z.val rewards C_star C_h rate)).crossing.isSome = true := by
    cases hl : ReferenceCorrectedInitializationLaunch.correctedLaunch rate z.val rewards C_star C_h with
    | none =>
        have hm := d.record_mem
        simp only [ReferenceCompletePhysicalHistory.completeSuffixRecords, hl, dite_true,
          List.not_mem_nil] at hm
    | some state =>
        exact (ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
          rate z.val rewards C_star C_h).mp (by rw [hl]; rfl)
  let s := startTime (rate := rate) z.val rewards C_star C_h
  let count := p.T - s
  have hsle : s ≤ p.T := ReferenceCompletePhysicalHistory.physicalStart_le_T
    rate z.val rewards C_star C_h
  have hs : s + count ≤ p.T := by omega
  let initial := ReferenceFirstCollectionEpochAlignment.actualLaunchState rate z.val rewards C_star C_h hc
  have hactive := ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
    rate z.val rewards C_star C_h hc
  let epoch := actualEpoch (rate := rate) z.val rewards C_star C_h hc count hs
  have hrecords : ReferenceCompletePhysicalHistory.completeSuffixRecords rate z.val rewards C_star C_h =
      epoch.records := by
    exact ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
      rate z.val rewards C_star C_h initial (Option.some_get _).symm
  obtain ⟨n, r, hr, ht, hcall, hearlier⟩ :=
    (ReferenceFirstCollectionSamplerCall.firstCollectionCall_spec rewards C_star C_h z.val u t
      (renewalCallParameter rate rewards C_star C_h u t z)).mp
      (firstCollectionCall_eq rate rewards C_star C_h u t z)
  rw [hrecords] at hr
  have hn : n < count := by
    have h := (List.getElem?_eq_some_iff.mp hr).1
    have hlen : epoch.records.length = count := ReferenceActivePhysicalHorizon.run_record_count
      initial z.val.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z.val) rewards s count hs hactive.1
    omega
  have htime := record_time initial z.val.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p z.val) rewards s count hs hactive.1 n r hr
  obtain ⟨j, hd⟩ := List.mem_iff_getElem?.mp d.record_mem
  rw [hrecords] at hd
  have hdtime := record_time initial z.val.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p z.val) rewards s count hs hactive.1 j d.record hd
  have hnt : s + n = t.val := by rw [ht] at htime; exact htime.symm
  have hj : j = n := by rw [d.time_eq] at hdtime; omega
  subst j
  have heq : r = d.record := Option.some.inj (hr.symm.trans hd)
  subst r
  have hstate := run_input_state initial z.val.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p z.val) rewards s count hs hactive.1 n hn d.record hr
  have hw : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow epoch.records).length < n := by
    by_contra hnot
    have hmass := ReferenceFirstComplementMassBudget.run_first_complement_mass
      initial z.val.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z.val) rewards s count hs
      hactive.1 hactive.2 n (Nat.le_of_lt hn) (Nat.le_of_not_gt hnot)
    have hcoord := (congrArg ReferenceActivePhysicalStep.State.coordinator hstate).symm.trans d.coordinator_eq
    change (match (ReferenceActivePhysicalHorizon.run initial z.val.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p z.val) rewards s n (by omega) hactive.1).finalState.coordinator with
      | .first => n = 0
      | .collection _ _ _ => False
      | .dagger => True
      | .live r q base => _) at hmass
    rw [hcoord] at hmass
    exact hmass
  refine ⟨hc, hs, n, hn, hr, hnt, ?_, ?_, hw⟩
  · intro j hj r hrj
    exact hearlier j hj r (hrecords ▸ hrj)
  · obtain ⟨old, ledger, saved, _, _, hp⟩ :=
      (ReferenceFirstCollectionSamplerCall.collectionCallAt_spec d.record u
        (renewalCallParameter rate rewards C_star C_h u t z)).mp hcall
    change ReferenceLaterAssignmentFibreStep.parameters? d.record.input = some _ at hp
    rw [hp]
    rfl

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

private theorem next_dispatch_eq_call
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T)
    (z : ReferenceFirstCollectionRenewalInstallationCoupling.Source rate rewards C_star C_h u t)
    (d : ActualRenewalCall rate rewards C_star C_h u t z)
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (l : ReferenceActivePhysicalStep.Ledger rate) (saved : Option (Fin p.T × Bool))
    (k : ActualNextDispatch x payload l saved)
    (hliteral : k.operationLedger = CoordinatorRoundDispatch.collectionOperationLedger
      (ReferenceActivePhysicalStep.collectionInput x payload l
        (ReferenceActivePhysicalStep.collectionClock payload l saved k.cutoffTime) k.cutoffTime)
      k.core.payload_n_eq)
    (hx : x = d.record.input) :
    payload = d.old ∧ l = d.ledger ∧ saved = d.saved ∧
      k.started = d.started ∧ k.instruction = d.instruction ∧ HEq k.reconstructed d.out := by
  rcases k with ⟨hstate, hvalid, hready, hsigma, horder, hcutcursor, hcursor,
    hfreeze, hassign, hempty, hunit, hmass, hspan, hbank, hclass,
    cutoff, hcut, core, started, hstart, instruction, hi, ledger, consistent,
    ht, hkind, hprep, hiff, hfailure, out, hrec⟩
  change ledger = CoordinatorRoundDispatch.collectionOperationLedger
    (ReferenceActivePhysicalStep.collectionInput x payload l
      (ReferenceActivePhysicalStep.collectionClock payload l saved cutoff) cutoff) core.payload_n_eq at hliteral
  change payload = d.old ∧ l = d.ledger ∧ saved = d.saved ∧
    started = d.started ∧ instruction = d.instruction ∧ HEq out d.out
  subst ledger
  subst x
  have hcoord := hstate.symm.trans d.coordinator_eq
  obtain ⟨hp, hl, hs⟩ := ReferenceActivePhysicalStep.CoordinatorConfiguration.collection.inj hcoord
  subst payload
  subst l
  subst saved
  have hc : cutoff = u := by
    apply Fin.ext
    rw [d.cutoff_eq] at hcut
    omega
  subst cutoff
  have hstarted : started = d.started := Except.ok.inj (hstart.symm.trans d.clock_eq)
  subst started
  have hinstruction : instruction = d.instruction := Option.some.inj (hi.symm.trans d.instruction_eq)
  subst instruction
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
  have heq := hrec.symm.trans d.reconstruction_eq
  injection heq with _ _ hout
  exact heq_of_eq hout

/-- The existing first prechoice renewal call is the input immediately after
the initialized stream's first empty FINISH. All witnesses are derived from
the original run; no successful sampler or no-failure trace is an input. -/
theorem actual_renewal_call_first_empty_boundary
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T)
    (z : ReferenceFirstCollectionRenewalInstallationCoupling.Source rate rewards C_star C_h u t)
    (d : ActualRenewalCall rate rewards C_star C_h u t z) :
    let s := startTime (rate := rate) z.val rewards C_star C_h
    let count := p.T - s
    ∃ hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z.val rewards C_star C_h rate)).crossing.isSome = true,
    ∃ hs : s + count ≤ p.T,
    let epoch := actualEpoch (rate := rate) z.val rewards C_star C_h hc count hs
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow epoch.records).length
    ∃ hk : w < count,
    ∃ f : ActualInitializedStreamDispatch z.val rewards C_star C_h count hc hs hk,
    ∃ e : EmptyPendingBoundary z.val rewards C_star C_h count hc hs hk
        f.stream f.last f.ledger f.record,
      f.outcome = .empty e ∧
      (∃ (before : f.record.input.time.val + 1 < p.T)
         (after : s ≤ f.record.input.time.val)
         (x : ReferenceActivePhysicalStep.RoundInput p rate),
       ∃ hinput : x = ReferenceActivePhysicalHorizon.roundInputAt
          (ReferenceFirstCollectionEpochAlignment.actualLaunchState rate z.val rewards C_star C_h hc)
          z.val.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z.val) rewards s
          (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
            rate z.val rewards C_star C_h hc).1
          e.prefixRun ⟨f.record.input.time.val + 1, by exact ⟨by omega, before⟩⟩,
       ∃ hstate : x.state = f.record.output.next,
       ∃ htime : x.time.val = f.record.input.time.val + 1,
       ∃ hrows : x.rows = z.val.1.2,
       ∃ hselected : x.selected = ActualInitializationPhysicalStep.selectedRowIndex p z.val,
       ∃ hrewards : x.rewards = rewards,
       ∃ hwindow : ∀ rNext, f.stream.window[f.stream.ell]? = some rNext → x = rNext.input,
       ∃ hrun : ∀ rNext, epoch.records[w + f.stream.ell]? = some rNext → x = rNext.input,
       ∃ k : ActualNextDispatch x f.stream.payload f.ledger f.stream.saved,
         e.nextBoundary = .next before after x hinput hstate htime hrows hselected
           hrewards hwindow hrun k ∧
         x = d.record.input ∧ k.started = d.started ∧
           k.instruction = d.instruction ∧ HEq k.reconstructed d.out) ∧
      f.stream.payload = d.old ∧ f.ledger = d.ledger ∧ f.stream.saved = d.saved ∧
      s + w + f.stream.ell = t.val := by
  classical
  obtain ⟨hc, hs, n, hn, hr, hnt, hearlier, hpresent, hw⟩ :=
    actual_first_call_index rate rewards C_star C_h u t z d
  let s := startTime (rate := rate) z.val rewards C_star C_h
  let count := p.T - s
  let epoch := actualEpoch (rate := rate) z.val rewards C_star C_h hc count hs
  let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow epoch.records).length
  change n < count at hn
  change epoch.records[n]? = some d.record at hr
  change s + n = t.val at hnt
  change w < n at hw
  have hk : w < count := lt_trans hw hn
  obtain ⟨f⟩ := actual_initialized_first_collection_stream_empty_dispatch
    rate z.val rewards C_star C_h count hc hs hk
  have hlength : epoch.records.length = count := ReferenceActivePhysicalHorizon.run_record_count
    _ _ _ _ _ _ _ _
  have hwindow : f.stream.window = ReferenceCollectionPhaseHistory.collectionWindow epoch.records w :=
    f.stream.windowIsActual
  have hprefix : w + f.stream.ell ≤ n := by
    by_contra hnot
    have hi : n - w < f.stream.ell := by omega
    obtain ⟨j, r, incoming, cell, hj, hrecord, _, _⟩ :=
      f.stream.cell_at ⟨n - w, hi⟩ (by change 0 < n - w; omega)
    have hrun := (stream_record_at z.val rewards C_star C_h count hc hs hk
      f.stream ⟨n - w, hi⟩ r hrecord).1
    have hin : w + (n - w) = n := by omega
    change epoch.records[w + (n - w)]? = some r at hrun
    rw [hin, hr] at hrun
    have heq : d.record = r := Option.some.inj hrun
    have hnone := ready_parameters_none r.input f.stream.payload incoming f.stream.saved cell.readyInput
    rw [← heq] at hnone
    rw [hnone] at hpresent
    cases hpresent
  have hend : n ≤ w + f.stream.window.length := by
    by_contra hnot
    have hstop : w + (ReferenceCollectionPhaseHistory.collectionWindow epoch.records w).length <
        epoch.records.length := by rw [← hwindow, hlength]; omega
    obtain ⟨r, hget, hchosen⟩ := window_stop epoch.records w (by omega) hstop
    have hnone := hearlier (w + f.stream.window.length) (by omega) r (hwindow ▸ hget)
    have hsome := laterChosen_parameters_present r.input hchosen
    rw [hnone] at hsome
    cases hsome
  have hrecord := stream_record_at z.val rewards C_star C_h count hc hs hk
    f.stream f.last f.record f.recordAt
  change epoch.records[w + f.last.val]? = some f.record ∧
    f.record.input.time.val = s + w + f.last.val at hrecord
  have hfinalTime : f.record.input.time.val + 1 = s + w + f.stream.ell := by
    have ht := hrecord.2
    have hl := f.lastIsLast
    omega
  have hnotExhausted : ∀ hp hex hcut hinc boundary,
      f.outcome ≠ .exhausted hp hex hcut hinc boundary := by
    intro hp hex hcut hinc boundary _
    have hm : w + f.stream.ell = n := by omega
    have hadj := connected_adjacent epoch.connected (w + f.last.val) f.record d.record
      hrecord.1 (by
        have he : w + f.last.val + 1 = n := by have hl := f.lastIsLast; omega
        rw [he]
        exact hr)
    have hcnext : d.record.input.state.coordinator =
        .collection f.stream.payload f.ledger f.stream.saved := by
      rw [hadj]
      exact f.actualNextCoordinator
    have hnone := parameters_none_of_pending d.record.input f.stream.payload f.ledger
      f.stream.saved hcnext hp
    rw [hnone] at hpresent
    cases hpresent
  cases houtcome : f.outcome with
  | exhausted hp hex hcut hinc boundary =>
      exact (hnotExhausted hp hex hcut hinc boundary houtcome).elim
  | empty e =>
      cases hb : e.nextBoundary with
      | terminal hT hcursor =>
          exfalso
          have ht := t.isLt
          omega
      | next hbefore hafter x hinput hstate htime hrows hselected hrewards hwindowNext hrunNext k0 =>
          obtain ⟨k, hsome, hliteral⟩ := canonical_next_dispatch x f.stream.payload f.ledger f.stream.saved
            k0 (fun a c hc => (f.cutoffLastService a c hc).1)
          have hm : w + f.stream.ell = n := by
            by_contra hne
            have hlt : w + f.stream.ell < n := by omega
            have hmcount : w + f.stream.ell < count := lt_trans hlt hn
            have hget := List.getElem?_eq_getElem (show w + f.stream.ell < epoch.records.length by omega)
            have hx := hrunNext _ hget
            have hnone := hearlier (w + f.stream.ell) hlt _ hget
            rw [← hx] at hnone
            rw [hnone] at hsome
            cases hsome
          have hx : x = d.record.input := hrunNext d.record (by rw [hm]; exact hr)
          obtain ⟨hpayload, hledger, hsaved, hstarted, hinstruction, hout⟩ :=
            next_dispatch_eq_call rate rewards C_star C_h u t z d x f.stream.payload f.ledger
              f.stream.saved k hliteral hx
          let e' : EmptyPendingBoundary z.val rewards C_star C_h count hc hs hk
              f.stream f.last f.ledger f.record :=
            { e with
              nextBoundary :=
                .next hbefore hafter x hinput hstate htime hrows hselected
                  hrewards hwindowNext hrunNext k }
          let f' : ActualInitializedStreamDispatch z.val rewards C_star C_h count hc hs hk :=
            { f with outcome := .empty e' }
          refine ⟨hc, hs, hk, f', e', rfl, ?_⟩
          refine ⟨?_, hpayload, hledger, hsaved, ?_⟩
          · exact ⟨hbefore, hafter, x, hinput, hstate, htime, hrows, hselected,
              hrewards, hwindowNext, hrunNext, k, rfl, hx, hstarted, hinstruction, hout⟩
          · change s + w + f.stream.ell = t.val
            omega

/-- The same actual first renewal call has the joint stored score/queue
budget. The proof consumes the initialized stream's current mass bound; it
does not assume or assert physical all-arm replay truth. -/
theorem actual_renewal_call_joint_budget
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T)
    (z : ReferenceFirstCollectionRenewalInstallationCoupling.Source rate rewards C_star C_h u t)
    (d : ActualRenewalCall rate rewards C_star C_h u t z) :
    let s := startTime (rate := rate) z.val rewards C_star C_h
    ∀ a : Fin p.K,
      AssignmentScoreReconstruction.sourceScore d.out a +
        AssignmentScoreReconstruction.initialQueue d.out a ≤ (t.val - s) * D p := by
  classical
  dsimp only
  obtain ⟨hc, hs, hk, f, e, _, hnext, hpayload, hledger, hsaved, _⟩ :=
    actual_renewal_call_first_empty_boundary rate rewards C_star C_h u t z d
  have hsigma : f.ledger.sigma = startTime (rate := rate) z.val rewards C_star C_h + 1 := by
    rw [f.ledgerIsLast]
    exact (f.stream.context f.last).1.trans f.stream.cutoffContext.1
  obtain ⟨hbefore, hafter, x, hinput, hstate, htime, hrows, hselected,
    hrewards, hwindow, hrun, k, _, hx, _, _, _⟩ := hnext
  have hcursor : f.ledger.cursor = t.val + 1 := by
    have ht : x.time = t := (congrArg ReferenceActivePhysicalStep.RoundInput.time hx).trans d.time_eq
    exact k.cursor.trans (congrArg (fun q : Fin p.T => q.val + 1) ht)
  have hmass := k.currentMassBounds
  rw [hledger] at hsigma hcursor hmass
  intro a
  have hcut : d.ledger.cutoffRegisters a = some (d.out.registers.cutoff a) :=
    d.out.registers.cutoff_eq a
  have hcurrent : d.ledger.currentRegisters a = some (d.out.registers.current a) :=
    d.out.registers.current_eq a
  have hbound := hmass a (d.out.registers.cutoff a) (d.out.registers.current a) hcut hcurrent
  rw [hsigma, hcursor, Nat.add_sub_add_right] at hbound
  exact hbound

end Bandits.Support.ReferenceFirstCollectionRenewalCallFirstEmptyBoundary

end
