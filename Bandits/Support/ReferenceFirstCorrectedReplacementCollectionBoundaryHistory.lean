/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionCorrectedOutsideCutoffNumericalJoin

import Lean.Elab.Tactic.Omega

/-!
# Actual corrected collection boundary and physical UP history

Source evidence: ZIP4 `appendix_a_local_protocol.tex:28-64` and
`06_interruptions.tex:40-100,246-299`. These are deterministic identities on
one original initialized physical run. Numerical installation and manuscript
closure are separate obligations.
-/

@[expose] public section
noncomputable section

namespace Bandits.Support.ReferenceFirstCorrectedReplacementCollectionBoundaryHistory

open ConstructorDimensions ReferenceActivePhysicalStep ReferenceActivePhysicalHorizon
open ReferenceCollectionSegmentExtraction

variable {p : ConstructorDimensions.Parameters} {rate : ReferenceActivePhysicalStep.RateInput p}

/-- A retained physical collection round keeps its complete choice payload. -/
private theorem completed_payload
    (record : RoundRecord (p := p) (rate := rate)) (done : CompletedRound rate)
    (h : extractRound record = some done) :
    ∃ saved, record.output.next.coordinator = .collection done.context.payload done.final saved := by
  obtain ⟨hc, _, _, P, saved, hn⟩ := actual_collection_round_checked record done h
  have ht : record.output.coordinator = collectionPostChoice (prepare record.input)
      done.context.payload done.context.preLedger done.context.started done.context.weights := by
    rw [record.output_eq]
    exact choice_tail record.input done.context hc
  have hf := ReferenceAssignmentPayloadPersistence.collectionPostChoice_payload_frame
    (prepare record.input) done.context.payload done.context.preLedger
      done.context.started done.context.weights
  have hs : record.output.coordinator.configuration = .collection P done.final saved := by
    rw [record.output_eq] at hn ⊢
    exact hn
  rw [← ht, hs] at hf
  simp only [ReferenceAssignmentPayloadPersistence.storedPayload_collection,
    reduceCtorEq, false_or] at hf
  have hp := Option.some.inj hf
  exact ⟨saved, hp ▸ hn⟩

/-- On an incoming collection, the choice's payload is the carried payload.
The equality is obtained from the actual dispatch constructor. -/
private theorem choice_collection_payload
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (P : Payload rate) (l : Ledger rate) (saved : Option (Fin p.T × Bool))
    (c : Choice rate) (hstate : x.state.coordinator = .collection P l saved)
    (hc : choice x = some c) : c.payload = P := by
  classical
  unfold choice at hc
  split at hc
  · contradiction
  next =>
    change choiceOfCut (ReferenceActivePhysicalStep.dispatch x) = some c at hc
    simp only [ReferenceActivePhysicalStep.dispatch, hstate] at hc
    split at hc
    next hcut =>
      let u : Fin p.T := ⟨l.cutoff - 1, by omega⟩
      let clock := collectionClock P l saved u
      change choiceOfCut (.collection P l clock u
        (CoordinatorRoundDispatch.dispatchCollection (collectionInput x P l clock u))) = some c at hc
      cases ho : CoordinatorRoundDispatch.dispatchCollection (collectionInput x P l clock u) <;>
        simp only [choiceOfCut, ho] at hc
      all_goals first | contradiction | (cases Option.some.inj hc; rfl)
    · simp only [choiceOfCut, reduceCtorEq] at hc

private theorem connected_endpoint
    {initial final : ReferenceActivePhysicalStep.State p rate}
    {records : List (RoundRecord (p := p) (rate := rate))}
    (h : Connected initial records final) : endpointState initial records = final := by
  induction records generalizing initial with
  | nil => exact h.symm
  | cons record rest ih => exact ih h.2

private theorem connected_prefix
    {initial final : ReferenceActivePhysicalStep.State p rate}
    (left right : List (RoundRecord (p := p) (rate := rate)))
    (h : Connected initial (left ++ right) final) :
    Connected initial left (endpointState initial left) := by
  induction left generalizing initial with
  | nil => rfl
  | cons record rest ih => exact ⟨h.1, ih h.2⟩

private theorem completed_collection_endpoint
    (records : List (RoundRecord (p := p) (rate := rate)))
    {initial final : ReferenceActivePhysicalStep.State p rate}
    (P : Payload rate) (l : Ledger rate) (saved : Option (Fin p.T × Bool))
    (hchain : Connected initial records final)
    (hstate : initial.coordinator = .collection P l saved)
    (hgood : ∀ r ∈ records, (extractRound r).isSome = true) :
    (∀ r ∈ records, ∀ c, choice r.input = some c → c.payload = P) ∧
      ∃ proposal, (endpointState initial records).coordinator =
        .collection P (endpointLedger l records) proposal := by
  induction records generalizing initial l saved with
  | nil => exact ⟨fun r hr => False.elim (List.not_mem_nil hr), saved, hstate⟩
  | cons record rest ih =>
    have hg := hgood record List.mem_cons_self
    cases he : extractRound record with
    | none => simp only [he, Option.isSome_none, Bool.false_eq_true] at hg
    | some done =>
      have hc := (actual_collection_round_checked record done he).1
      have hp := choice_collection_payload record.input P l saved done.context
        (hchain.1 ▸ hstate) hc
      obtain ⟨proposal, hn⟩ := completed_payload record done he
      rw [hp] at hn
      obtain ⟨hrest, proposal', hend⟩ := ih done.final proposal hchain.2 hn
        (fun r hr => hgood r (List.mem_cons_of_mem _ hr))
      refine ⟨?_, proposal', ?_⟩
      · intro r hr c hchoice
        rcases List.mem_cons.mp hr with rfl | hr
        · have hh := Option.some.inj (hc.symm.trans hchoice)
          exact hh ▸ hp
        · exact hrest r hr c hchoice
      · simpa only [endpointState, endpointLedger, completed, List.foldl_cons,
          List.filterMap_cons, he] using hend

/-- The entire retained segment has one original payload, including its last
successful physical output and every continuing choice. -/
private theorem segment_payload_endpoint
    (records : List (RoundRecord (p := p) (rate := rate)))
    (initial final : ReferenceActivePhysicalStep.State p rate) (e : ℕ)
    (seg : Segment rate) (hchain : Connected initial records final)
    (hseg : segmentAt records e = some seg) (hne : seg.records ≠ []) :
    (∀ r ∈ seg.records, ∀ c, choice r.input = some c → c.payload = seg.context.payload) ∧
      ∃ saved, (endpointState seg.entry.input.state seg.records).coordinator =
        .collection seg.context.payload seg.final saved := by
  have hb := (segmentAt_branch records e seg hseg).1
  have hg := segment_all_completed _ seg hb
  have hd := connected_drop records initial final e hchain
  cases hdrop : records.drop e with
  | nil => simp only [hdrop, ReferenceCollectionSegmentExtraction.segment, reduceCtorEq] at hb
  | cons entry rest =>
    have hentry : seg.entry = entry ∧ choice entry.input = some seg.context ∧
        ∃ tail, seg.records = entry :: tail := by
      simp only [hdrop, ReferenceCollectionSegmentExtraction.segment] at hb
      cases hc : choice entry.input with
      | none => simp only [hc, Option.map_none, reduceCtorEq] at hb
      | some c =>
        simp only [hc, Option.map_some] at hb
        split at hb
        · cases Option.some.inj hb
          exact ⟨rfl, rfl, _, rfl⟩
        · cases Option.some.inj hb
          exact False.elim (hne rfl)
    obtain ⟨hentry, hc, tail, hrecords⟩ := hentry
    have hpart := segmentAt_partition records e seg hseg
    rw [hdrop, hrecords] at hpart
    have hrest : tail ++ seg.remaining = rest := List.cons.inj hpart |>.2
    rw [hdrop] at hd
    have hprefix := connected_prefix tail seg.remaining (hrest.symm ▸ hd.2)
    have hhead := hg entry (by rw [hrecords]; exact List.mem_cons_self)
    cases he : extractRound entry with
    | none => simp only [he, Option.isSome_none, Bool.false_eq_true] at hhead
    | some done =>
      have hcontext := Option.some.inj
        ((actual_collection_round_checked entry done he).1.symm.trans hc)
      obtain ⟨saved, hn⟩ := completed_payload entry done he
      have hp : done.context.payload = seg.context.payload := congrArg Choice.payload hcontext
      rw [hp] at hn
      obtain ⟨htail, proposal, hend⟩ := completed_collection_endpoint tail seg.context.payload
        done.final saved hprefix hn (fun r hr => hg r (by rw [hrecords]; exact List.mem_cons_of_mem _ hr))
      refine ⟨?_, proposal, ?_⟩
      · intro r hr c hchoice
        rw [hrecords] at hr
        rcases List.mem_cons.mp hr with rfl | hr
        · exact congrArg Choice.payload (Option.some.inj (hchoice.symm.trans hc))
        · exact htail r hr c hchoice
      · simpa only [hrecords, endpointState, Segment.final, endpointLedger, completed,
          List.filterMap_cons, he, List.foldl_cons] using hend

/-- The original corrected cell supplies the initialized first-phase horizon;
no launch, activation, or history premise is added to the root. -/
private theorem firstCell_initialized_run
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hz : z ∈ ReferenceFirstCollectionCorrectedSliceNumericalPrefix.correctedCell
      rate rewards C_star C_h u t) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
    ∃ (initial : ReferenceActivePhysicalStep.State p rate) (span : s + (p.T - s) ≤ p.T)
      (active : allActiveAtStart initial s),
      ReferenceCorrectedInitializationLaunch.correctedLaunch rate z rewards C_star C_h = some initial ∧
      initial.coordinator = .first ∧
      R = (run initial z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)
        rewards s (p.T - s) span active).records := by
  obtain ⟨hc, _⟩ := ReferenceFirstCollectionCurrentRetainedGate.firstCell_prefix_coverage
    rate rewards C_star C_h u t z hz.1
  obtain ⟨initial, hlaunch, hfirst, _⟩ :=
    ReferenceCorrectedInitializationLaunch.correctedLaunch_coordinator_provenance
      rate z rewards C_star C_h hc
  have hs := ReferenceCompletePhysicalHistory.physicalStart_le_T rate z rewards C_star C_h
  refine ⟨initial, by omega,
    ReferenceCompletePhysicalHistory.activeMode_of_launch_eq_some
      rate z rewards C_star C_h initial hlaunch, hlaunch, hfirst, ?_⟩
  exact ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
    rate z rewards C_star C_h initial hlaunch

private theorem prefix_run_records
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (s total : ℕ) (span : s + total ≤ p.T) (active : allActiveAtStart initial s)
    (v : ℕ) (hv : v ≤ total) :
    (run initial rows J rewards s total span active).records.take v =
      (run initial rows J rewards s v (by omega) active).records := by
  obtain ⟨suffix, h⟩ := ReferenceCollectionPhaseHistory.run_records_prefix
    initial rows J rewards s v (total - v) (by omega) active
  have he : v + (total - v) = total := Nat.add_sub_of_le hv
  simp only [he] at h
  rw [h, List.take_append_of_le_length (by rw [run_record_count])]
  exact List.take_of_length_le (by rw [run_record_count])

private theorem segment_records_take
    (R : List (RoundRecord (p := p) (rate := rate))) (e : ℕ) (seg : Segment rate)
    (h : segmentAt R e = some seg) :
    (R.drop e).take seg.records.length = seg.records ∧
      e + seg.records.length ≤ R.length := by
  have hp := segmentAt_partition R e seg h
  have hn := congrArg List.length hp
  simp only [List.length_append, List.length_drop] at hn
  have he : e ≤ R.length := by
    by_contra hbad
    have hn' : R.drop e = [] := List.drop_eq_nil_iff.mpr (by omega)
    have hb := (segmentAt_branch R e seg h).1
    simp only [hn', ReferenceCollectionSegmentExtraction.segment, reduceCtorEq] at hb
  exact ⟨by rw [← hp]; simp only [List.take_append_length], by omega⟩

/-- A nonempty actual collection ends at the original physical state. At a
strict interior boundary the next input carries exactly this payload and final
ledger; at the horizon no new `Fin T` input is manufactured. -/
private theorem initialized_segment_boundary
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (initial : ReferenceActivePhysicalStep.State p rate)
    (hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate z rewards C_star C_h = some initial)
    (e : ℕ) (seg : Segment rate)
    (hseg : segmentAt (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h) e = some seg) (hne : seg.records ≠ []) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
    let v := e + seg.records.length
    v ≤ R.length ∧
    (∀ r ∈ seg.records, ∀ c, choice r.input = some c → c.payload = seg.context.payload) ∧
    ∃ saved, (endpointState seg.entry.input.state seg.records).coordinator =
      .collection seg.context.payload seg.final saved ∧
    (v = R.length ∨ ∃ hv : v < R.length,
      R[v].input.state = endpointState seg.entry.input.state seg.records ∧
      R[v].input.state.coordinator = .collection seg.context.payload seg.final saved ∧
      R[v].input.time.val = s + v ∧
      R.drop v = seg.remaining) := by
  intro R s v
  have hchain := ReferenceCompletePhysicalHistory.completeSuffix_connected_on_launch
    rate z rewards C_star C_h initial hlaunch
  obtain ⟨_, hle⟩ := segment_records_take R e seg hseg
  obtain ⟨hp, saved, hend⟩ := segment_payload_endpoint R initial _ e seg hchain hseg hne
  refine ⟨hle, hp, saved, hend, ?_⟩
  by_cases hv : v = R.length
  · exact Or.inl hv
  · have hv : v < R.length := by omega
    have heq : R[v].input.state = endpointState seg.entry.input.state seg.records := by
      have hd := connected_drop R initial _ e hchain
      have hp := segmentAt_partition R e seg hseg
      rw [← hp] at hd
      have he : seg.records.length < (seg.records ++ seg.remaining).length := by
        have hh := congrArg List.length hp
        simp only [List.length_append, List.length_drop] at hh ⊢
        dsimp only [v] at hv
        omega
      have ht := ReferenceFollowerReplyChronology.connected_take_to_input hd seg.records.length he
      rw [List.take_append_length] at ht
      have hstate := connected_endpoint ht
      have hfold : endpointState (endpointState initial (R.take e)) seg.records =
          endpointState seg.entry.input.state seg.records := by
        cases hh : seg.records with
        | nil => exact False.elim (hne hh)
        | cons r rs => rfl
      rw [hfold] at hstate
      simpa only [hp, List.getElem_drop, v, Nat.add_comm] using hstate.symm
    refine Or.inr ⟨hv, heq, heq ▸ hend, ?_, ?_⟩
    · have ht := ReferenceCompletePhysicalHistory.completeSuffixRecords_time_values
        rate z rewards C_star C_h
      change R.map (fun r => r.input.time.val) = List.range' s (p.T - s) at ht
      have hh := congrArg (fun xs => xs[v]?) ht
      have hv' : v < p.T - s := by
        have hn := ReferenceCompletePhysicalHistory.completeSuffixRecords_length rate z rewards C_star C_h
        change R.length = p.T - s at hn
        omega
      rw [List.getElem?_map, List.getElem?_eq_getElem hv, Option.map_some,
        List.getElem?_eq_getElem (by simpa only [List.length_range'] using hv')] at hh
      exact Option.some.inj hh |>.trans (List.getElem_range'_1 v _)
    · have hp := segmentAt_partition R e seg hseg
      have hd := congrArg (List.drop seg.records.length) hp
      simpa only [List.drop_left', List.drop_drop, v, Nat.add_comm] using hd.symm

private theorem continuing_not_cutoff (r : RoundRecord (p := p) (rate := rate))
    (h : continuing r = true) : ReferenceCollectionPhaseHistory.cutoffChosen r.input = false := by
  classical
  unfold continuing at h
  cases he : extractRound r with
  | none => simp only [he, Bool.false_eq_true] at h
  | some done =>
    simp only [he] at h
    have hc := (actual_collection_round_checked r done he).1
    unfold choice at hc
    split at hc
    · contradiction
    next =>
      cases hd : (prepare r.input).coordinator with
      | live live owned base outcome =>
        cases outcome <;> simp only [hd, choiceOfCut] at hc
        all_goals
          first
          | contradiction
          | have hi := congrArg Choice.initializer (Option.some.inj hc)
            rw [← hi] at h
            exact Bool.noConfusion h
      | collection P l clock cutoff outcome =>
        simp only [ReferenceCollectionPhaseHistory.cutoffChosen, hd]
      | first outcome => simp only [ReferenceCollectionPhaseHistory.cutoffChosen, hd]
      | invalidCollectionCutoff => simp only [ReferenceCollectionPhaseHistory.cutoffChosen, hd]
      | dagger => simp only [ReferenceCollectionPhaseHistory.cutoffChosen, hd]

private theorem segment_shape
    (R : List (RoundRecord (p := p) (rate := rate))) (e : ℕ) (seg : Segment rate)
    (hseg : segmentAt R e = some seg) (hne : seg.records ≠ []) :
    ∃ tail, seg.records = seg.entry :: tail ∧
      ∀ r ∈ tail, ReferenceCollectionPhaseHistory.cutoffChosen r.input = false := by
  have hb := (segmentAt_branch R e seg hseg).1
  cases hd : R.drop e with
  | nil => simp only [hd, ReferenceCollectionSegmentExtraction.segment, reduceCtorEq] at hb
  | cons entry rest =>
    simp only [hd, ReferenceCollectionSegmentExtraction.segment] at hb
    cases hc : choice entry.input with
    | none => simp only [hc, Option.map_none, reduceCtorEq] at hb
    | some c =>
      simp only [hc, Option.map_some] at hb
      split at hb
      · cases Option.some.inj hb
        refine ⟨_, rfl, ?_⟩
        intro r hr
        exact continuing_not_cutoff r ((List.all_eq_true.mp List.all_takeWhile) r hr)
      · cases Option.some.inj hb
        exact False.elim (hne rfl)

private theorem last_marked_prefix_length {α : Type*} (test : α → Bool)
    (before before' : List α) (head head' : α) (tail tail' : List α)
    (h : before ++ head :: tail = before' ++ head' :: tail')
    (hh : test head = true) (hh' : test head' = true)
    (ht : ∀ r ∈ tail, test r = false) (ht' : ∀ r ∈ tail', test r = false) :
    before.length = before'.length := by
  induction before generalizing before' with
  | nil =>
    cases before' with
    | nil => rfl
    | cons r rs =>
      have he := (List.cons.inj h).2
      have hm : head' ∈ tail := by rw [he]; exact List.mem_append_right _ List.mem_cons_self
      have hf := ht head' hm
      rw [hh'] at hf
      contradiction
  | cons r rs ih =>
    cases before' with
    | nil =>
      have he := (List.cons.inj h).2
      have hm : head ∈ tail' := by rw [← he]; exact List.mem_append_right _ List.mem_cons_self
      have hf := ht' head hm
      rw [hh] at hf
      contradiction
    | cons r' rs' =>
      exact congrArg Nat.succ (ih rs' (List.cons.inj h).2)

/-- Empty pending at this actual segment's endpoint gives real physical UP
witnesses inside this very segment. The last-cutoff history is identified by
its literal list decomposition, including at a terminal horizon. -/
private theorem segment_literal_history
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (initial : ReferenceActivePhysicalStep.State p rate)
    (span : ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h +
      (p.T - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h) ≤ p.T)
    (active : allActiveAtStart initial (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h))
    (hfirst : initial.coordinator = .first)
    (hrun : ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h =
      (run initial z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards
        (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
        (p.T - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h) span active).records)
    (e : ℕ) (seg : Segment rate)
    (hseg : segmentAt (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h) e = some seg)
    (hne : seg.records ≠ [])
    (hcut : ReferenceCollectionPhaseHistory.cutoffChosen seg.entry.input = true) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    ∃ during, seg.records = seg.entry :: during ∧
      R.take (e + seg.records.length) = R.take e ++ seg.records ∧
      ReferenceCollectionPhaseHistory.laterChosen seg.entry.input = false ∧
      (∀ r ∈ during, ReferenceCollectionPhaseHistory.cutoffChosen r.input = false ∧
        ReferenceCollectionPhaseHistory.laterChosen r.input = false) ∧
      seg.final.pending = Finset.univ \ (ReferenceCollectionPhaseHistory.acceptedLabels seg.records).toFinset ∧
      (ReferenceCollectionPhaseHistory.acceptedLabels seg.records).Nodup ∧
      (seg.final.pending = ∅ → ∀ i : Fin (p.m - 1), ∃ (k : Fin R.length) (U : ReferenceCollectionPhaseHistory.UpRecord p rate),
      e ≤ k.val ∧ k.val < e + seg.records.length ∧
      R[k.val] ∈ seg.records ∧ ReferenceCollectionPhaseHistory.AcceptedUp R[k.val].input i U ∧
      U.val.sigma = seg.final.sigma) := by
  intro R
  let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  let v := e + seg.records.length
  have hlen : R.length = p.T - s := ReferenceCompletePhysicalHistory.completeSuffixRecords_length
    rate z rewards C_star C_h
  have hchain := run_connected initial z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)
    rewards s (p.T - s) span active
  rw [← hrun] at hchain
  obtain ⟨_, hle⟩ := segment_records_take R e seg hseg
  have he : e ≤ R.length := by omega
  have hprefix : R.take v = R.take e ++ seg.records := by
    have hp := segmentAt_partition R e seg hseg
    have hfull : R = (R.take e ++ seg.records) ++ seg.remaining := by
      rw [List.append_assoc, hp, List.take_append_drop]
    have hcount : (R.take e ++ seg.records).length = v := by
      simp only [List.length_append, List.length_take, Nat.min_eq_left he, v]
    conv_lhs => rw [hfull, ← hcount, List.take_append_length]
  have hv : v ≤ p.T - s := by omega
  have hpref := prefix_run_records initial z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)
    rewards s (p.T - s) span active v hv
  rw [← hrun] at hpref
  have hendpoint := connected_endpoint (run_connected initial z.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s v (by omega) active)
  rw [← hpref, hprefix] at hendpoint
  have hfold : endpointState initial (R.take e ++ seg.records) =
      endpointState seg.entry.input.state seg.records := by
    simp only [endpointState, List.foldl_append]
    cases hh : seg.records with
    | nil => exact False.elim (hne hh)
    | cons r rs => rfl
  rw [hfold] at hendpoint
  obtain ⟨_, saved, hend⟩ := segment_payload_endpoint R initial _ e seg hchain hseg hne
  have hcoord : (run initial z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)
      rewards s v (by omega) active).finalState.coordinator =
      .collection seg.context.payload seg.final saved := by rw [← hendpoint]; exact hend
  obtain ⟨before, cutoff, during, hdecomp, hcutoff, hlater, hduring, hpending, hnodup, hw⟩ :=
    ReferenceCollectionPhaseHistory.run_history initial z.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s v (by omega) active
      hfirst seg.context.payload seg.final saved hcoord
  rw [← hpref, hprefix] at hdecomp
  obtain ⟨tail, htail, hnocut⟩ := segment_shape R e seg hseg hne
  have hbefore : e = before.length := by
    have heq := last_marked_prefix_length
      (fun r : RoundRecord (p := p) (rate := rate) => ReferenceCollectionPhaseHistory.cutoffChosen r.input)
      (R.take e) before seg.entry cutoff tail during (by rw [← htail]; exact hdecomp)
      hcut hcutoff hnocut (fun r hr => (hduring r hr).1)
    simpa only [List.length_take, Nat.min_eq_left he] using heq
  have hwindow : seg.records = cutoff :: during := by
    have hleft : (R.take e).length = e := by simp only [List.length_take, Nat.min_eq_left he]
    calc
      seg.records = (R.take e ++ seg.records).drop (R.take e).length :=
        List.drop_append_length.symm
      _ = (before ++ cutoff :: during).drop before.length := by rw [hdecomp, hleft, hbefore]
      _ = cutoff :: during := List.drop_append_length
  have hentry : cutoff = seg.entry := (List.cons.inj (htail.symm.trans hwindow)).1.symm
  subst cutoff
  refine ⟨during, hwindow, hprefix, hlater, hduring, ?_, ?_, ?_⟩
  · rw [hwindow]
    exact hpending
  · rw [hwindow]
    exact hnodup
  intro hempty i
  have himem : i ∈ ReferenceCollectionPhaseHistory.acceptedLabels (seg.entry :: during) := by
    apply List.mem_toFinset.mp
    by_contra hn
    have hi : i ∈ seg.final.pending := by
      rw [hpending]
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hn⟩
    rw [hempty] at hi
    exact Finset.notMem_empty i hi
  obtain ⟨r, hr, ha⟩ := List.mem_filterMap.mp himem
  obtain ⟨U, hU, hsigma⟩ := hw r hr i ha
  have hrseg : r ∈ seg.records := hwindow ▸ hr
  obtain ⟨j, hj, hget⟩ := List.mem_iff_getElem.mp hrseg
  have hk : e + j < R.length := by omega
  have hrecord : R[e + j] = r := by
    have hp := segmentAt_partition R e seg hseg
    have hh : (seg.records ++ seg.remaining)[j]? = (R.drop e)[j]? := congrArg (fun xs => xs[j]?) hp
    simpa only [List.getElem?_append_left hj, List.getElem?_eq_getElem hj, hget,
      List.getElem?_drop, List.getElem?_eq_getElem hk, Option.some.injEq] using hh.symm
  exact ⟨⟨e + j, hk⟩, U, by dsimp only; omega, by dsimp only; omega, hrecord ▸ hrseg, hrecord ▸ hU, hsigma⟩


/-- Checked chronology fixes the cursor even when there is no next physical
input. It uses the actual source calendar and successful collection fold. -/
private theorem initialized_segment_cursor
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (initial : ReferenceActivePhysicalStep.State p rate)
    (span : ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h +
      (p.T - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h) ≤ p.T)
    (active : allActiveAtStart initial
      (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h))
    (hfirst : initial.coordinator = .first)
    (hrun : ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h =
      (run initial z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards
        (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
        (p.T - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
        span active).records)
    (e : ℕ) (seg : Segment rate)
    (hseg : segmentAt (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h) e = some seg) (hne : seg.records ≠ []) :
    seg.final.cursor = ReferenceCompletePhysicalHistory.physicalStart
      rate z rewards C_star C_h + (e + seg.records.length) + 1 := by
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  have hb := (segmentAt_branch R e seg hseg).1
  have hcount := segment_input_count (R.drop e) seg hb
  have hcal := segment_input_calendar (R.drop e) seg hb
  have hle := (segment_records_take R e seg hseg).2
  have htimes := ReferenceCompletePhysicalHistory.completeSuffixRecords_time_values
    rate z rewards C_star C_h
  change R.map (fun r => r.input.time.val) = List.range' s (p.T - s) at htimes
  have hlen : R.length = p.T - s :=
    ReferenceCompletePhysicalHistory.completeSuffixRecords_length rate z rewards C_star C_h
  rw [List.map_drop, htimes, List.drop_range', Nat.mul_one,
    List.take_range'_of_length_ge (by omega)] at hcal
  have hseg' := hseg
  rw [hrun] at hseg'
  have hchron := run_collection_input_chronology initial z.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s (p.T - s)
    span active e seg hseg'
  have hcursor := (run_collection_final_cursor initial z.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s (p.T - s)
    span active hfirst e seg hseg').1
  have hstart : seg.context.preLedger.cursor = s + e + 1 := by
    cases hi : seg.inputs with
    | nil =>
      rw [hi, List.length_nil] at hcount
      exact False.elim (hne (List.length_eq_zero_iff.mp hcount.symm))
    | cons input rest =>
      rw [hi] at hchron hcal hcount
      have hc : CoordinatorCollectionLedger.sourceRound input.round =
          seg.context.preLedger.cursor := hchron.1
      have hn : seg.records.length = rest.length + 1 := by
        simpa only [List.length_cons] using hcount.symm
      rw [List.map_cons, hn, List.range'_succ] at hcal
      have ht : input.round.val = s + e := (List.cons.inj hcal).1
      simpa only [CoordinatorCollectionLedger.sourceRound, ht] using hc.symm
  rw [hcursor, hcount, hstart]
  omega

/-- One deterministic boundary/history outcome on the original corrected-cell
run. The last-cutoff decomposition is this literal extracted interval. Empty
pending supplies actual physical UP witnesses; a later choice derives that
emptiness from its incoming collection constructor. Horizon and stopped
interior boundaries retain their original suffix without a new time input. -/
theorem firstCell_collection_boundary_history
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hz : z ∈ ReferenceFirstCollectionCorrectedSliceNumericalPrefix.correctedCell
      rate rewards C_star C_h u t)
    (e : ℕ) (seg : Segment rate)
    (hseg : segmentAt (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h) e = some seg) (hne : seg.records ≠ [])
    (hcut : ReferenceCollectionPhaseHistory.cutoffChosen seg.entry.input = true) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
    let v := e + seg.records.length
    v ≤ R.length ∧
    (∀ r ∈ R, r.input.rows = z.1.2 ∧
      r.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p z ∧
      r.input.rewards = rewards) ∧
    (∀ r ∈ seg.records, ∀ c, choice r.input = some c → c.payload = seg.context.payload) ∧
    ∃ saved, (endpointState seg.entry.input.state seg.records).coordinator =
        .collection seg.context.payload seg.final saved ∧
      seg.final.cursor = s + v + 1 ∧
    ∃ during, seg.records = seg.entry :: during ∧
      R.take v = R.take e ++ seg.records ∧
      ReferenceCollectionPhaseHistory.laterChosen seg.entry.input = false ∧
      (∀ r ∈ during, ReferenceCollectionPhaseHistory.cutoffChosen r.input = false ∧
        ReferenceCollectionPhaseHistory.laterChosen r.input = false) ∧
      seg.final.pending = Finset.univ \ (ReferenceCollectionPhaseHistory.acceptedLabels seg.records).toFinset ∧
      (ReferenceCollectionPhaseHistory.acceptedLabels seg.records).Nodup ∧
      (seg.final.pending = ∅ → ∀ i : Fin (p.m - 1),
        ∃ (k : Fin R.length) (U : ReferenceCollectionPhaseHistory.UpRecord p rate),
          e ≤ k.val ∧ k.val < v ∧ R[k.val] ∈ seg.records ∧
          ReferenceCollectionPhaseHistory.AcceptedUp R[k.val].input i U ∧
          U.val.sigma = seg.final.sigma) ∧
      (v = R.length ∨ ∃ hv : v < R.length,
        R[v].input.state = endpointState seg.entry.input.state seg.records ∧
        R[v].input.state.coordinator = .collection seg.context.payload seg.final saved ∧
        R[v].input.time.val = s + v ∧ R.drop v = seg.remaining ∧
        (ReferenceCollectionPhaseHistory.laterChosen R[v].input = false ∨
          ReferenceCollectionPhaseHistory.laterChosen R[v].input = true ∧
          seg.final.pending = ∅ ∧ ∀ i : Fin (p.m - 1),
            ∃ (k : Fin R.length) (U : ReferenceCollectionPhaseHistory.UpRecord p rate),
              e ≤ k.val ∧ k.val < v ∧ R[k.val] ∈ seg.records ∧
              ReferenceCollectionPhaseHistory.AcceptedUp R[k.val].input i U ∧
              U.val.sigma = seg.final.sigma)) := by
  intro R s v
  obtain ⟨initial, span, active, hlaunch, hfirst, hrun⟩ :=
    firstCell_initialized_run rate rewards C_star C_h u t z hz
  obtain ⟨hle, hpayload, saved, hend, hboundary⟩ :=
    initialized_segment_boundary rewards C_star C_h z initial hlaunch e seg hseg hne
  have hcursor := initialized_segment_cursor rewards C_star C_h z initial span active
    hfirst hrun e seg hseg hne
  obtain ⟨during, hrecords, hprefix, hnotlater, hduring, hpending, hnodup, hw⟩ :=
    segment_literal_history rewards C_star C_h z initial span active hfirst hrun
      e seg hseg hne hcut
  refine ⟨hle, ?_, hpayload, saved, hend, hcursor, during, hrecords, hprefix,
    hnotlater, hduring, hpending, hnodup, hw, ?_⟩
  · intro r hr
    change r ∈ ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h at hr
    rw [hrun] at hr
    exact run_record_inputs initial z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)
      rewards s (p.T - s) span active r hr
  · rcases hboundary with hhorizon | ⟨hv, hstate, hcoord, htime, hdrop⟩
    · exact Or.inl hhorizon
    · refine Or.inr ⟨hv, hstate, hcoord, htime, hdrop, ?_⟩
      by_cases hlater : ReferenceCollectionPhaseHistory.laterChosen R[v].input = true
      · obtain ⟨P, l, proposal, hactual, hempty⟩ :=
          ReferenceCollectionPhaseHistory.laterChosen_pending_empty R[v].input hlater
        have hledger : seg.final = l :=
          (CoordinatorConfiguration.collection.inj (hcoord.symm.trans hactual)).2.1
        have hpempty : seg.final.pending = ∅ := by rw [hledger]; exact hempty
        exact Or.inr ⟨hlater, hpempty, hw hpempty⟩
      · exact Or.inl (Bool.eq_false_iff.mpr hlater)

end Bandits.Support.ReferenceFirstCorrectedReplacementCollectionBoundaryHistory
