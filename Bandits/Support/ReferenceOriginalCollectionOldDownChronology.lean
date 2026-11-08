/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceOriginalKthCollectionSourceSections
public import Bandits.Support.ReferenceFirstReplacementCollectionStoppedCompositeQuota

import Lean.Elab.Tactic.Omega

/-!
# Original LIVE cutoff OLD DOWN chronology

Sources: `sources/zip4/manuscript/06_interruptions.tex:459-481`,
`sources/zip4/manuscript/05_binary_transport.tex:180-240`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:109-163`.

This file starts from an indexed record of the original complete suffix.  The
cutoff branch and its payload are read from that record's actual preparation.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open Bandits.Support.ConstructorDimensions
open scoped Classical

namespace Bandits.Support.ReferenceOriginalCollectionOldDownChronology

abbrev Parameters := ReferenceOriginalKthCollectionSourceSections.Parameters
abbrev RateInput := ReferenceOriginalKthCollectionSourceSections.RateInput
abbrev SourceInput (p : Parameters) :=
  ReferenceOriginalKthCollectionSourceSections.SourceInput p
abbrev GridRewardTable (p : Parameters) :=
  ReferenceOriginalKthCollectionSourceSections.GridRewardTable p
abbrev Record {p : Parameters} (rate : RateInput p) :=
  ReferenceCompletePhysicalHistory.RoundRecord (p := p) (rate := rate)
abbrev DownRecord {p : Parameters} (rate : RateInput p) :=
  OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta)

variable {p : Parameters}
variable (rate : RateInput p) (rewards : GridRewardTable p)
  (C_star C_h : ℝ)

private theorem complete_suffix_get_time (z : SourceInput p) (e : ℕ)
    (he : e < (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length) :
    ((ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[e]'he).input.time.val =
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + e := by
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  have htimes := ReferenceCompletePhysicalHistory.completeSuffixRecords_time_values
    rate z rewards C_star C_h
  have hget := congrArg (fun xs : List ℕ => xs[e]?) htimes
  have he' : e < p.T - s := by
    rw [← ReferenceCompletePhysicalHistory.completeSuffixRecords_length
      rate z rewards C_star C_h]
    exact he
  have hrange := List.getElem?_range' (s := s) (step := 1) he'
  simpa [R, s, ReferenceActivePhysicalHorizon.calendar,
    List.getElem?_map, List.getElem?_eq_getElem he, hrange] using hget

/-- The actual full-calendar lookup returns the same record stored at suffix
index `e`; this derives the date from the complete suffix chronology. -/
theorem actualRecord_at_completeSuffix_get (z : SourceInput p) (e : ℕ)
    (he : e < (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length) :
    ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[e]'he).input.time z =
      some ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[e]'he) := by
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  let r := R[e]'he
  have htime := complete_suffix_get_time rate rewards C_star C_h z e he
  have hsle : s ≤ r.input.time.val := by
    rw [htime]
    omega
  have hindex : r.input.time.val - s = e := by
    rw [htime]
    omega
  change (if s ≤ r.input.time.val then R[r.input.time.val - s]? else none) = some r
  rw [ite_eq_left hsle, hindex, List.getElem?_eq_getElem he]

/-- Read the OLD word from the actual LIVE `cutoffChosen` branch at a suffix
index. `none` records the literal absent or noncutoff branch. -/
def actualCutOldWord (z : SourceInput p) (e : ℕ) (i : Fin (p.m - 1)) :
    Option (DownRecord rate) := by
  classical
  exact ((ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate z rewards C_star C_h)[e]?).bind fun r =>
      match r.output.preparation.coordinator with
      | .live registers _ _ (.cutoffChosen ..) => some (registers.payload.downRecord i)
      | _ => none

/-- An actual complete-suffix cutoff record has the source choice and exact
payload/pending/cutoff read by the incoming coordinator code. Every
noncutoff/absent case remains the literal absent branch. -/
theorem actual_live_cutoff_choice_at (z : SourceInput p) (e : ℕ)
    (he : e < (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length) (i : Fin (p.m - 1)) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    match R[e]? with
    | none => True
    | some r =>
      match r.output.preparation.coordinator with
      | .live registers _ _ (.cutoffChosen _ _ _ _ _ _ _ _ _ _) =>
        ∃ c : ReferenceCollectionSegmentExtraction.Choice rate,
          ReferenceCollectionSegmentExtraction.choice r.input = some c ∧
          c.payload = registers.payload ∧
          actualCutOldWord rate rewards C_star C_h z e i =
            some (c.payload.downRecord i) ∧
          ∃ data : ReferenceOriginalKthCollectionSourceSections.KthCPrechoiceData rate,
            ReferenceOriginalKthCollectionSourceSections.kthCPrechoiceData
              rate rewards C_star C_h r.input.time z = some data ∧
            data.1 = c.payload ∧ data.2.1 = c.preLedger.pending ∧
            data.2.2.1 = c.preLedger.cutoff
      | _ => True := by
  dsimp only
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  cases hget : R[e]? with
  | none => trivial
  | some r =>
    simp only
    cases hbranch : r.output.preparation.coordinator with
    | first outcome => simp only
    | collection payload ledger clock cutoff outcome => simp only
    | invalidCollectionCutoff => simp only
    | dagger => simp only
    | live registers owned base outcome =>
      cases outcome with
      | continuingChosen dispatched hstart continuation selected => simp only
      | clockFailure failure hfailure => simp only
      | initializerFailure dispatched hstart checked hfailure => simp only
      | localFailure dispatched hstart failure => simp only
      | cutoffChosen dispatched hstart ledger hinitialization hledger hdomains
          hclock hpending hassignment selected =>
        simp only
        have hrecord : ReferenceSourcePrefixHistoryFiltration.actualRecord
            rate rewards C_star C_h r.input.time z = some r := by
          have hr : R[e]'he = r := by
            apply Option.some.inj
            exact (List.getElem?_eq_getElem he).symm.trans hget
          rw [← hr]
          simpa [R] using actualRecord_at_completeSuffix_get
            rate rewards C_star C_h z e he
        have hstate : r.input.state.coordinator = .live registers owned base := by
          have hprep : r.output.preparation = ReferenceActivePhysicalStep.prepare r.input := by
            rw [r.output_eq]
            rfl
          have hbranch' := hbranch
          rw [hprep] at hbranch'
          cases hcoord : r.input.state.coordinator with
          | first =>
              simp [ReferenceActivePhysicalStep.prepare,
                ReferenceActivePhysicalStep.dispatch, hcoord] at hbranch'
              cases hbranch'
          | live registers' owned' base' =>
              simp only [ReferenceActivePhysicalStep.prepare,
                ReferenceActivePhysicalStep.dispatch, hcoord] at hbranch'
              injection hbranch' with hregisters howned hbase
              subst registers'
              subst base'
              have hownedEq : owned' = owned := eq_of_heq howned
              subst owned'
              rfl
          | collection payload ledger saved =>
              simp only [ReferenceActivePhysicalStep.prepare,
                ReferenceActivePhysicalStep.dispatch, hcoord] at hbranch'
              split at hbranch'
              · split at hbranch'; cases hbranch'
              · cases hbranch'
          | dagger =>
              simp [ReferenceActivePhysicalStep.prepare,
                ReferenceActivePhysicalStep.dispatch, hcoord] at hbranch'
        let c : ReferenceCollectionSegmentExtraction.Choice rate :=
          ⟨registers.payload, ReferenceActivePhysicalStep.sharedLedger ledger,
            dispatched.startResult,
            (ReferenceActivePhysicalStep.liveRegistersAt registers r.input.time).complementWeights,
            some (ReferenceCollectionSegmentExtraction.cutoffInitializer
              (ReferenceActivePhysicalStep.liveRegistersAt registers r.input.time)
              (ReferenceActivePhysicalStep.liveOwnedAt registers owned r.input.time)
              base r.input.time)⟩
        have hchoice : ReferenceCollectionSegmentExtraction.choice r.input = some c := by
          have hprep : r.output.preparation = ReferenceActivePhysicalStep.prepare r.input := by
            rw [r.output_eq]
            rfl
          have hbranch' := hbranch
          rw [hprep] at hbranch'
          have hselection : (ReferenceActivePhysicalStep.prepare r.input).coordinator.selection ≠ none := by
            rw [hbranch']
            simp [ReferenceActivePhysicalStep.DispatchCut.selection,
              ReferenceActivePhysicalStep.selectionAt]
          unfold ReferenceCollectionSegmentExtraction.choice
          rw [ite_eq_right hselection]
          rw [hbranch']
          rfl
        have hcutoff :=
          ReferenceOriginalKthCollectionSourceSections.kthCPrechoiceData_actualLiveCollectionChoice
            rate rewards C_star C_h r.input.time z r hrecord registers owned base hstate c hchoice
        rcases hcutoff with ⟨data, hdata, hpayload, hpending', hcutoff', _hinitializer⟩
        refine ⟨c, hchoice, rfl, ?_, ?_⟩
        · simp [actualCutOldWord, R, hget, hbranch, c]
        · exact ⟨data, hdata, hpayload, hpending', hcutoff'⟩

private theorem complete_run_realization (z : SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length) :
    let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
    ∃ (initial : ReferenceActivePhysicalStep.State p rate)
      (span : s + (p.T - s) ≤ p.T)
      (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial s),
      ReferenceCorrectedInitializationLaunch.correctedLaunch
        rate z rewards C_star C_h = some initial ∧
      initial.coordinator = .first ∧
      ReferenceFollowerDecoderChronology.downBatchSeed initial s ∧
      ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h =
        (ReferenceActivePhysicalHorizon.run initial z.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s
          (p.T - s) span active).records := by
  dsimp only
  cases hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate z rewards C_star C_h with
  | none =>
      have hk := k.isLt
      simp only [ReferenceCompletePhysicalHistory.completeSuffixRecords, hlaunch] at hk
      simp at hk
  | some initial =>
      have hc := (ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
        rate z rewards C_star C_h).mp (by rw [hlaunch]; rfl)
      obtain ⟨coordinatorInitial, hcoordinator, hfirst, _⟩ :=
        ReferenceCorrectedInitializationLaunch.correctedLaunch_coordinator_provenance
          rate z rewards C_star C_h hc
      have heq : coordinatorInitial = initial :=
        Option.some.inj (hcoordinator.symm.trans hlaunch)
      subst coordinatorInitial
      obtain ⟨decoderInitial, hdecoder, hseed⟩ :=
        ReferenceCorrectedInitializationLaunch.correctedLaunch_downBatchSeed
          rate z rewards C_star C_h hc
      have heq : decoderInitial = initial :=
        Option.some.inj (hdecoder.symm.trans hlaunch)
      subst decoderInitial
      let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
      have span : s + (p.T - s) ≤ p.T := by
        have hs := ReferenceCompletePhysicalHistory.physicalStart_le_T
          rate z rewards C_star C_h
        dsimp only [s]
        omega
      have active := ReferenceCompletePhysicalHistory.activeMode_of_launch_eq_some
        rate z rewards C_star C_h initial hlaunch
      refine ⟨initial, span, active, rfl, hfirst, ?_, ?_⟩
      · exact hseed
      · exact ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
          rate z rewards C_star C_h initial hlaunch

private theorem run_get_eq_actualRunRecordAt
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (s count : ℕ) (span : s + count ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial s)
    (k : ℕ) (hk : k < count) :
    (ReferenceActivePhysicalHorizon.run initial rows J rewards s count span active).records[k]'
      (by rw [ReferenceActivePhysicalHorizon.run_record_count]; exact hk) =
      ReferenceAssignmentPayloadChronology.actualRunRecordAt initial rows J rewards s k
        (by omega) active := by
  have hsplit : k + 1 + (count - (k + 1)) = count := by omega
  obtain ⟨tail, hprefix⟩ := ReferenceCollectionPhaseHistory.run_records_prefix
    initial rows J rewards s (k + 1) (count - (k + 1)) (by omega) active
  have hprefix' :
      (ReferenceActivePhysicalHorizon.run initial rows J rewards s count span active).records =
        (ReferenceActivePhysicalHorizon.run initial rows J rewards s (k + 1)
          (by omega) active).records ++ tail := by
    simpa only [hsplit] using hprefix
  have hkprefix : k < (ReferenceActivePhysicalHorizon.run initial rows J rewards s
      (k + 1) (by omega) active).records.length := by
    rw [ReferenceActivePhysicalHorizon.run_record_count]
    omega
  have hsuccessor := ReferenceAssignmentPayloadChronology.run_successor_actualRunRecordAt
    initial rows J rewards s k (by omega) active
  calc
    _ = ((ReferenceActivePhysicalHorizon.run initial rows J rewards s (k + 1)
        (by omega) active).records ++ tail)[k]'(by
          rw [List.length_append, ReferenceActivePhysicalHorizon.run_record_count]
          omega) := getElem_congr_coll hprefix'
    _ = (ReferenceActivePhysicalHorizon.run initial rows J rewards s (k + 1)
        (by omega) active).records[k]'hkprefix := List.getElem_append_left hkprefix
    _ = ((ReferenceActivePhysicalHorizon.run initial rows J rewards s k
        (by omega) active).records ++
        [ReferenceAssignmentPayloadChronology.actualRunRecordAt initial rows J rewards
          s k (by omega) active])[k]'(by
            rw [List.length_append, ReferenceActivePhysicalHorizon.run_record_count]
            simp only [List.length_singleton]
            omega) := getElem_congr_coll hsuccessor
    _ = _ := by simp only [List.getElem_append,
        ReferenceActivePhysicalHorizon.run_record_count, Nat.lt_irrefl, ↓reduceDIte,
        Nat.sub_self, List.getElem_cons_zero]

private theorem retainedDown_selected_word
    (r : Record rate) (i : Fin (p.m - 1)) (M : DownRecord rate)
    (hretained : ReferenceAcceptedUpFollowerHistory.RetainedDown r i M) :
    ∃ selected : ReferenceActivePhysicalStep.Selection r.input,
      r.output.preparation.coordinator.selection = some selected ∧
      M = selected.view.payload.downRecord i := by
  obtain ⟨logged, cut, after, raw, scan, registers, lastService,
    hlogged, hcut, haccepted⟩ := hretained
  have hactual := ReferenceDownCompletedAmbiguityMeasurability.record_downCut_eq_actual
    r i logged cut hlogged hcut
  have haccepted' := haccepted
  rw [hactual] at haccepted'
  obtain ⟨view, hview⟩ := ReferenceFollowerSparseEmissionRecovery.acceptedReferenceCut_someView
    r.output.preparation.coordinator.downView i r.input.row r.input.time
    (ReferenceFollowerDownDecoderReplay.preparedOwnObservation r i) logged logged after
    raw M scan registers lastService haccepted'
  rw [hview] at haccepted'
  have hword := (ReferenceActiveDataOwnership.referenceDown_accepted_fields view i
    r.input.row r.input.time (ReferenceFollowerDownDecoderReplay.preparedOwnObservation r i)
    logged logged after raw M scan registers lastService haccepted').1
  have hselection : r.output.preparation.coordinator.selection.map
      ReferenceActivePhysicalStep.Selection.view = some view := hview
  cases hs : r.output.preparation.coordinator.selection with
  | none => simp only [hs, Option.map_none] at hselection; cases hselection
  | some selected =>
      have heq : selected.view = view := by
        simpa only [hs, Option.map_some, Option.some.injEq] using hselection
      exact ⟨selected, rfl, by rw [heq]; exact hword⟩

/-- At an actual record whose input retains a payload, an
ordinary follower either already holds its entire DOWN word or has a strictly
older accepted start. Older accepted words are retained in the second case. -/
theorem actual_stored_choice_current_or_older (z : SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (P : ReferenceActivePhysicalStep.Payload rate)
    (hstored : ReferenceAssignmentPayloadPersistence.storedPayload
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[k.val].input.state.coordinator = some P)
    (i : Fin (p.m - 1))
    (choice : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hchoice : (ReferenceFollowerFixedReply.actualChoice
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[k.val] i).configuration = .ordinary choice memory) :
    choice.lastDown = some (P.downRecord i) ∨
      ReferencePrelaunchFollower.acceptedStart choice < (P.downRecord i).val.sigma := by
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  let J := ActualInitializationPhysicalStep.selectedRowIndex p z
  obtain ⟨initial, span, active, _hlaunch, hfirst, _hseed, hrecords⟩ :=
    complete_run_realization rate rewards C_star C_h z k
  have hlength : R.length = p.T - s := by
    exact ReferenceCompletePhysicalHistory.completeSuffixRecords_length rate z rewards C_star C_h
  have hk : k.val < p.T - s := by rw [← hlength]; exact k.isLt
  have hrecord (a : Fin R.length) : R[a.val] =
      ReferenceAssignmentPayloadChronology.actualRunRecordAt initial z.1.2 J rewards s a.val
        (by have ha := a.isLt; omega) active := by
    rw [List.getElem_of_eq hrecords]
    exact run_get_eq_actualRunRecordAt rate rewards initial z.1.2 J s (p.T - s)
      span active a.val (by have ha := a.isLt; omega)
  have hinput : R[k.val].input.state =
      (ReferenceActivePhysicalHorizon.run initial z.1.2 J rewards s k.val
        (by omega) active).finalState := by
    rw [hrecord k]
    rfl
  have hstored' : ReferenceAssignmentPayloadPersistence.storedPayload
      (ReferenceActivePhysicalHorizon.run initial z.1.2 J rewards s k.val
        (by omega) active).finalState.coordinator = some P := by
    rw [← hinput]
    exact hstored
  have hMsigma : (P.downRecord i).val.sigma = P.sigma.val + 1 :=
    congrArg OrdinaryMessageCodec.DownFields.sigma (P.downRecord_fields i)
  cases hdown : choice.lastDown with
  | none =>
      right
      simp only [ReferencePrelaunchFollower.acceptedStart, hdown]
      omega
  | some M =>
      obtain ⟨_b, j, _oldPayload, _beta, _hbj, hjk, _hbirth, _hbase, hretained,
        _hword, _hmass, _hdelta⟩ :=
        ReferenceCompleteOrdinaryFollowerMass.complete_ordinary_follower_choice_mass
          rewards C_star C_h z k i choice memory hchoice M hdown
      have hretained' : ReferenceAcceptedUpFollowerHistory.RetainedDown
          (ReferenceAssignmentPayloadChronology.actualRunRecordAt initial z.1.2 J rewards
            s j.val (by have hj := j.isLt; omega) active) i M := by
        rw [← hrecord j]
        exact hretained
      obtain ⟨selected, hselected, hM⟩ := retainedDown_selected_word rate _ i M hretained'
      have hprepared : (ReferenceActivePhysicalStep.prepare
          (ReferenceAssignmentPayloadChronology.actualRunRecordAt initial z.1.2 J rewards
            s j.val (by have hj := j.isLt; omega) active).input).coordinator.selection =
          some selected := hselected
      have hle := ReferenceGeneratedUpSitePayloadOrder.actual_prefix_selected_start_le
        initial z.1.2 J rewards s k.val (by omega) active hfirst P hstored'
        j.val hjk (by have hj := j.isLt; omega) selected hprepared
      have hMstart : M.val.sigma = selected.view.payload.sigma.val + 1 := by
        rw [hM]
        exact congrArg OrdinaryMessageCodec.DownFields.sigma
          (selected.view.payload.downRecord_fields i)
      by_cases heq : selected.view.payload.sigma.val = P.sigma.val
      · left
        have hmem : ReferenceAssignmentPayloadChronology.actualRunRecordAt initial z.1.2 J
            rewards s j.val (by have hj := j.isLt; omega) active ∈
            (ReferenceActivePhysicalHorizon.run initial z.1.2 J rewards s
              (p.T - s) span active).records := by
          rw [← hrecord j, ← hrecords]
          exact List.getElem_mem j.isLt
        have hwords :=
          ReferenceSelectedPayloadChronology.run_actualSelectedPayload_downRecord_eq_of_prefix_storedPayload_equal_sigma
            initial z.1.2 J rewards s (p.T - s) span active hfirst _ selected hmem
            hselected k.val (by omega) P hstored' heq i
        exact congrArg some (hM.trans hwords)
      · right
        simp only [ReferencePrelaunchFollower.acceptedStart, hdown]
        omega

private theorem selected_down_diagnostics
    (r : Record rate) (i : Fin (p.m - 1))
    (choice : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hchoice : (ReferenceFollowerFixedReply.actualChoice r i).configuration =
      .ordinary choice memory)
    (hbuffer : ActiveFollowerLifecycle.localBufferValid choice)
    (hstatus : choice.status = .unoccupied)
    (hselected : ActiveFollowerDownAcceptance.downSelected p i r.input.row r.input.time) :
    (r.output.followers i).downInput = some choice ∧
      (r.output.followers i).down = some (ReferenceDownReception.referenceDownCut p
        r.output.preparation.coordinator.downView i r.input.row r.input.time
        (ReferenceFollowerDownDecoderReplay.preparedOwnObservation r i) rate choice) := by
  let own := ((r.output.preparation.followers.followers i).arm,
    ReferenceFollowerDownDecoderReplay.preparedOwnObservation r i)
  have hnot : ¬ SparseCalendarReplay.loggingTestsPass
      (ReferencePrelaunchFollower.loggingRound i r.input.row
        (r.input.state.activations i) r.input.time own) := by
    intro hpass
    have hdata := (ActiveFollowerLogging.loggingTestsPass_iff_source_mask i r.input.row
      (r.input.state.activations i) r.input.time own).mp hpass |>.2.1
    rw [hselected.1] at hdata
    cases hdata
  have hnil := ActiveFollowerLogging.logAt_eq_nil_of_not_tests i r.input.row
    (r.input.state.activations i) r.input.time own hnot
  have hlogging : ActiveFollowerLogging.checkedLogging i r.input.row
      (r.input.state.activations i) r.input.time own choice = .ok choice := by
    apply (ActiveFollowerLogging.checkedLogging_success_iff _ _ _ _ _ _ _).mpr
    refine ⟨hbuffer, ?_, hbuffer⟩
    unfold ActiveFollowerLogging.loggingUpdate
    split <;> simp only [hnil, List.append_nil]
  have halign := r.output.preparation.follower_alignment i
  have hlogging' : ActiveFollowerLogging.checkedLogging
      (r.output.preparation.followers.followers i).follower
      (r.output.preparation.followers.followers i).row
      (r.output.preparation.followers.followers i).activation
      (r.output.preparation.followers.followers i).time own choice = .ok choice := by
    rw [halign.1, halign.2.1, halign.2.2.1, halign.2.2.2]
    exact hlogging
  have hd := ReferenceActivePhysicalStep.recordFollower_logged
    r.output.preparation.coordinator.downView
    (r.output.preparation.followers.followers i).follower
    (r.output.preparation.followers.followers i).row
    (r.output.preparation.followers.followers i).activation
    (r.output.preparation.followers.followers i).time
    (r.output.preparation.followers.followers i).active
    (r.output.preparation.followers.followers i).arm
    (ReferenceFollowerDownDecoderReplay.preparedOwnObservation r i)
    choice choice hstatus hlogging'
  have hf := ReferenceFollowerSparseEmissionRecovery.finishFollower_diagnostics
    r.output.preparation.coordinator.downView
    (r.output.preparation.followers.followers i)
    (ReferenceFollowerDownDecoderReplay.preparedOwnObservation r i)
    choice memory hchoice
  rw [ReferenceFollowerBufferProvenance.roundRecord_follower_eq_finishFollower i r]
  constructor
  · exact hf.1.trans hd.1
  · have h := hf.2.trans hd.2
    rw [halign.1, halign.2.1, halign.2.2.1] at h
    exact h

/-- Every selected OLD receiver call at an actual stored-payload selection is
awaited in the original physical detector dictionary. No positivity premise
is used, so selected zero feedback is retained. -/
theorem actual_stored_old_down_awaited (z : SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (P : ReferenceActivePhysicalStep.Payload rate)
    (hstored : ReferenceAssignmentPayloadPersistence.storedPayload
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[k.val].input.state.coordinator = some P)
    (selected : ReferenceActivePhysicalStep.Selection
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[k.val].input)
    (hselected : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[k.val].output.preparation.coordinator.selection = some selected)
    (hpayload : selected.view.payload = P)
    (i : Fin (p.m - 1)) (hpending : i ∈ selected.view.pendingAtChoice)
    (hold : ReferenceFirstReplacementCollectionOldDownCallDates.actualOldAt
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[k.val] i (P.downRecord i))
    (hdown : ActiveFollowerDownAcceptance.downSelected p i
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[k.val].input.row
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[k.val].input.time) :
    ReferenceCompleteAwaitedBatchSourceCoverage.originalDownAwaitedCallAt rate
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[k.val] i
      (CoordinatorLocalArmChoice.storedDownFlatWord P i) := by
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let r := R[k.val]
  obtain ⟨choice, memory, hchoice, hstatus, hnotCurrent⟩ := hold
  obtain ⟨before, beforeMemory, actualChoice, _hinput, _hbeforeDomain, _hstart,
    hactual, hdomain, hoperation⟩ :=
    ReferenceCompleteSuffixFollowerPreservation.complete_suffix_follower_choice
      (rate := rate) rewards C_star C_h z k i
  have heq : actualChoice = choice :=
    (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
      (hactual.symm.trans hchoice)).1
  subst actualChoice
  have horder := actual_stored_choice_current_or_older
    rate rewards C_star C_h z k P hstored i choice memory hchoice
  have hstrict : ReferencePrelaunchFollower.acceptedStart choice < (P.downRecord i).val.sigma :=
    horder.resolve_left hnotCurrent
  have htime : (P.downRecord i).val.sigma ≤ r.input.time.val + 1 := by
    obtain ⟨initial, span, active, _hlaunch, hfirst, _hseed, hrecords⟩ :=
      complete_run_realization rate rewards C_star C_h z k
    have hmem : r ∈ (ReferenceActivePhysicalHorizon.run initial z.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards
        (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
        (p.T - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
        span active).records := by
      rw [← hrecords]
      exact List.getElem_mem k.isLt
    obtain ⟨_birth, _hbirthMem, _hbirth, _hbirthTime, hbefore⟩ :=
      ReferenceSelectedPayloadChronology.actualRun_selectedPayload_has_birth
        initial z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards
        _ _ span active hfirst r selected hmem hselected
    rw [hpayload] at hbefore
    have hsigma : (P.downRecord i).val.sigma = P.sigma.val + 1 :=
      congrArg OrdinaryMessageCodec.DownFields.sigma (P.downRecord_fields i)
    rw [hsigma]
    exact Nat.add_le_add_right hbefore 1
  have hsender := ReferenceFirstReplacementCollectionOldDownSenderReadiness.selected_sender
    r P i selected hselected hpayload hdown hpending
  obtain ⟨hinput, hdiag⟩ := selected_down_diagnostics rate r i choice memory hchoice
    hdomain.2.1 hstatus hdown
  refine ⟨choice, _, P.downRecord i, hinput, hdiag, hdown, hstatus,
    hoperation.1, hoperation.2.1, hoperation.2.2, hsender.2.1, ?_, hstrict, htime⟩
  exact ReferenceFirstReplacementCollectionOldDownSenderReadiness.parse_stored_word P i

/-- Source initialization of the OLD receiver at an arbitrary actual LIVE
cutoff. The birth, cutoff, ordinary START, inherited bank, and zero-inclusive
awaited call are all derived from the original source. Noncutoff and absent
records retain their literal branch. -/
theorem actual_live_cutoff_old_down_initialization
    (z : SourceInput p) (e : ℕ) (i : Fin (p.m - 1)) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    match R[e]? with
    | none => True
    | some cut =>
      match cut.output.preparation.coordinator with
      | .live registers _ _ (.cutoffChosen _ _ _ _ _ _ _ _ _ _) =>
        let P := registers.payload
        let M := P.downRecord i
        ∃ (c : ReferenceCollectionSegmentExtraction.Choice rate) (b : Fin R.length),
          ReferenceCollectionSegmentExtraction.choice cut.input = some c ∧
          c.payload = P ∧
          ReferenceAssignmentPayloadPersistence.storedPayload cut.input.state.coordinator = some P ∧
          c.preLedger.pending = Finset.univ ∧
          c.preLedger.cutoff = cut.input.time.val + 1 ∧
          b.val < e ∧ ReferenceAssignmentPayloadPersistence.InstallationBirth R[b.val] P ∧
          R[b.val].input.time = P.sigma ∧
          FollowerCutoffScan.firstCutoff p rate.eta.val P.sigma
            (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
              (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z))) =
                cut.input.time.val + 1 ∧
          ∃ (before choice : ReferencePrelaunchFollower.State p rate.eta)
            (memory : ActiveFollowerLifecycle.LocalMemory p),
            cut.input.state.followers i = .ordinary before memory ∧
            ActiveFollowerLifecycle.startRound rate.eta cut.input.time before memory =
              .ok (choice, memory) ∧
            (ReferenceFollowerFixedReply.actualChoice cut i).configuration =
              .ordinary choice memory ∧
            choice.status = .unoccupied ∧ choice.downBatch = before.downBatch ∧
            choice.downBatch.pending.length < AffineBatchDecoder.quota p ∧
            (choice.lastDown = some M ∨
              ReferencePrelaunchFollower.acceptedStart choice < M.val.sigma) ∧
            (ActiveFollowerDownAcceptance.downSelected p i cut.input.row cut.input.time →
              choice.lastDown ≠ some M →
              ReferenceCompleteAwaitedBatchSourceCoverage.originalDownAwaitedCallAt rate cut i
                (CoordinatorLocalArmChoice.storedDownFlatWord P i))
      | _ => True := by
  dsimp only
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  cases hget : R[e]? with
  | none => trivial
  | some cut =>
      simp only
      cases hbranch : cut.output.preparation.coordinator with
      | first outcome => trivial
      | collection payload ledger clock cutoff outcome => trivial
      | invalidCollectionCutoff => trivial
      | dagger => trivial
      | live registers owned base outcome =>
        cases outcome with
        | continuingChosen dispatched hstart continuation selected => trivial
        | clockFailure failure hfailure => trivial
        | initializerFailure dispatched hstart checked hfailure => trivial
        | localFailure dispatched hstart failure => trivial
        | cutoffChosen dispatched hstart ledger hinitialization hledger hdomains
            hclock hpending hassignment selected =>
          dsimp only
          obtain ⟨he, hcut⟩ := List.getElem?_eq_some_iff.mp hget
          subst cut
          let cut := R[e]'he
          let k : Fin R.length := ⟨e, he⟩
          have hkcut : (ReferenceCompletePhysicalHistory.completeSuffixRecords
              rate z rewards C_star C_h)[k.val] = cut := rfl
          have hprep : cut.output.preparation = ReferenceActivePhysicalStep.prepare cut.input := by
            rw [cut.output_eq]
            rfl
          let physical : ReferenceActivePhysicalStep.Selection cut.input := {
            view := {
              payload := registers.payload
              pendingAtChoice := dispatched.startResult.pending
              cutoff := CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
                dispatched.startResult.clock.u
              complementWeights :=
                (ReferenceActivePhysicalStep.liveRegistersAt registers cut.input.time).complementWeights }
            started := dispatched.startResult
            pending_eq := rfl
            cutoff_eq := rfl
            arm := selected.arm
            choice_eq := selected.armChoice_eq }
          have hphysical : cut.output.preparation.coordinator.selection = some physical := by
            rw [hbranch]
            simp only [ReferenceActivePhysicalStep.DispatchCut.selection,
              ReferenceActivePhysicalStep.selectionAt]
            rfl
          have hstored : ReferenceAssignmentPayloadPersistence.storedPayload
              cut.input.state.coordinator = some registers.payload := by
            rcases ReferenceSelectedPayloadChronology.actualSelectedPayload_local_stored_or_birth
                cut physical hphysical with hstored | hborn
            · exact hstored
            · unfold ReferenceAssignmentPayloadPersistence.InstallationBirth at hborn
              rw [hbranch] at hborn
              exact hborn.elim
          let c : ReferenceCollectionSegmentExtraction.Choice rate :=
            ⟨registers.payload, ReferenceActivePhysicalStep.sharedLedger ledger,
              dispatched.startResult,
              (ReferenceActivePhysicalStep.liveRegistersAt registers cut.input.time).complementWeights,
              some (ReferenceCollectionSegmentExtraction.cutoffInitializer
                (ReferenceActivePhysicalStep.liveRegistersAt registers cut.input.time)
                (ReferenceActivePhysicalStep.liveOwnedAt registers owned cut.input.time)
                base cut.input.time)⟩
          have hc : ReferenceCollectionSegmentExtraction.choice cut.input = some c := by
            unfold ReferenceCollectionSegmentExtraction.choice
            rw [← hprep, ite_eq_right (by rw [hphysical]; exact Option.some_ne_none physical)]
            rw [hbranch]
            rfl
          have hcSource : ReferenceCollectionSegmentExtraction.choice R[k.val].input = some c := by
            rw [hkcut]
            exact hc
          obtain ⟨b, hbe, hborn, _hassignment, _hsigma, hfirstCutoff, _hbase⟩ :=
            ReferenceAssignmentRetainedBirthProvenance.complete_collection_choice_birth_provenance
              rate rewards C_star C_h z k c hcSource
          have hcutoff : c.preLedger.cutoff = cut.input.time.val + 1 := by
            change ledger.cutoff = _
            rw [hledger]
            rfl
          have hfirstCutoff' : FollowerCutoffScan.firstCutoff p rate.eta.val registers.payload.sigma
              (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
                (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z))) =
                  cut.input.time.val + 1 := hfirstCutoff.symm.trans hcutoff
          have hbornTime : R[b.val].input.time = registers.payload.sigma := by
            apply Fin.ext
            exact (ReferenceAssignmentPayloadChronology.installationBirth_time_eq
              R[b.val] registers.payload hborn).symm
          obtain ⟨before, memory, choice, hinput, _hbeforeDomain, hstarted,
            hchoice, _hchoiceDomain, hoperation⟩ :=
            ReferenceCompleteSuffixFollowerPreservation.complete_suffix_follower_choice
              (rate := rate) rewards C_star C_h z k i
          have hstoredSource : ReferenceAssignmentPayloadPersistence.storedPayload
              R[k.val].input.state.coordinator = some registers.payload := by
            rw [hkcut]
            exact hstored
          have horder := actual_stored_choice_current_or_older rate rewards C_star C_h
            z k registers.payload hstoredSource i choice memory hchoice
          have hframe := ActiveFollowerLifecycle.startRound_frame rate.eta
            R[k.val].input.time before choice memory memory hstarted
          have hunoccupied : choice.status = .unoccupied := by
            by_cases hcurrent : choice.lastDown = some (registers.payload.downRecord i)
            · have hbeforeDown : before.lastDown = some (registers.payload.downRecord i) :=
                hframe.1.symm.trans hcurrent
              have hphase := ReferenceCompleteFollowerCutoffPhase.complete_ordinary_follower_phase
                rate rewards C_star C_h z k i before memory hinput
                (registers.payload.downRecord i) hbeforeDown
              have htoken := ReferenceCompleteFollowerCutoffPhase.complete_ordinary_follower_token
                rate rewards C_star C_h z k i before memory hinput
              have hstatus := ReferenceAssignmentFollowerMassSteps.start_round_cutoff_status
                R[k.val].input.time R[k.val].input.row before choice memory memory
                (registers.payload.downRecord i) hbeforeDown hphase htoken hstarted
              apply hstatus.mpr
              have hcoordinate : ActiveFollowerDownAcceptance.downStart p rate
                  (registers.payload.downRecord i) = registers.payload.sigma := by
                apply Fin.ext
                change registers.payload.sigma.val + 1 - 1 = registers.payload.sigma.val
                omega
              rw [hcoordinate]
              obtain ⟨initial, span, active, _hlaunch, _hfirst, _hseed, hrecords⟩ :=
                complete_run_realization rate rewards C_star C_h z k
              have hmem : R[k.val] ∈ (ReferenceActivePhysicalHorizon.run initial z.1.2
                  (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards _ _ span active).records := by
                rw [← hrecords]
                exact List.getElem_mem k.isLt
              obtain ⟨hrows, hselected, _hrewards⟩ :=
                ReferenceActivePhysicalHorizon.run_record_inputs initial z.1.2
                  (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards _ _ span active _ hmem
              have hrow : R[k.val].input.row =
                  z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) :=
                congrArg₂ (fun rows selected => rows selected) hrows hselected
              rw [hrow, hfirstCutoff', hkcut]
            · obtain ⟨states, memories, hchoices, hoccupied, _hfields⟩ :=
                ReferenceCompletePayloadChoiceChronology.complete_selected_payload_choice_fields
                  rewards C_star C_h z k
                  physical
                  hphysical
              have hstateEq : states i = choice :=
                (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
                  ((hchoices i).symm.trans hchoice)).1
              by_contra hnot
              apply hcurrent
              simpa only [hstateEq] using hoccupied i (by simpa only [hstateEq] using hnot)
          refine ⟨c, b, hc, rfl, hstored, ?_, hcutoff, hbe, hborn, hbornTime, hfirstCutoff',
            before, choice, memory, ?_, ?_, ?_, hunoccupied, hframe.2.2.2.2.1,
            hoperation.2.1.1, horder, ?_⟩
          · change ledger.pending = Finset.univ
            rw [hledger]
            rfl
          · simpa only [hkcut] using hinput
          · simpa only [hkcut] using hstarted
          · simpa only [hkcut] using hchoice
          · intro hdown hnotCurrent
            have hold : ReferenceFirstReplacementCollectionOldDownCallDates.actualOldAt
                R[k.val] i (registers.payload.downRecord i) :=
              ⟨choice, memory, hchoice, hunoccupied, hnotCurrent⟩
            have hawaited := actual_stored_old_down_awaited rate rewards C_star C_h
              z k registers.payload hstoredSource
              physical
              hphysical rfl i
              (by
                change i ∈ dispatched.startResult.pending
                rw [hpending]
                exact Finset.mem_univ i)
              hold (by simpa only [hkcut] using hdown)
            simpa only [hkcut] using hawaited

private theorem connected_endpoint_eq
    {initial final : ReferenceActivePhysicalStep.State p rate}
    {records : List (Record rate)}
    (hconnected : ReferenceActivePhysicalHorizon.Connected initial records final) :
    ReferenceCollectionSegmentExtraction.endpointState initial records = final := by
  induction records generalizing initial with
  | nil => exact hconnected.symm
  | cons r records ih =>
      exact ih hconnected.2

private theorem raw_cut_down_bank_replay (z : SourceInput p) (e j : ℕ)
    (he : e < (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length) (i : Fin (p.m - 1)) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let cut := R[e]'he
    let K := cut :: (R.drop (e + 1)).takeWhile
      (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
    let Z := ReferenceCollectionSegmentExtraction.endpointState cut.input.state (K.take j)
    let calls := ReferenceFollowerDownDecoderReplay.actualDownCalls i (K.take j)
    let positives := ReferenceFollowerDownDecoderReplay.actualDownPositives i (K.take j)
    ∃ (base state : ReferencePrelaunchFollower.State p rate.eta)
      (baseMemory memory : ActiveFollowerLifecycle.LocalMemory p),
      cut.input.state.followers i = .ordinary base baseMemory ∧
      Z.followers i = .ordinary state memory ∧
      state.downBatch = ReferenceFollowerDownDecoderReplay.foldDownCalls calls base.downBatch ∧
      AffineBatchDecoder.collected state.downBatch =
        AffineBatchDecoder.collected base.downBatch ++ positives ∧
      base.downBatch.pending.length < AffineBatchDecoder.quota p ∧
      (∀ entry ∈ base.downBatch.pending, entry.time.val < cut.input.time.val) ∧
      calls.Pairwise (fun first second => first.1.val < second.1.val) ∧
      (calls.map Prod.fst).map Fin.val =
        ReferenceActivePhysicalHorizon.calendar cut.input.time.val (K.take j).length ∧
      positives.Pairwise (fun first second => first.time.val < second.time.val) ∧
      (∀ entry ∈ positives, cut.input.time.val ≤ entry.time.val ∧
        entry.time.val < cut.input.time.val + (K.take j).length) ∧
      (positives.length = AffineBatchDecoder.quota p - base.downBatch.pending.length +
          AffineBatchDecoder.quota p →
        let secondBank := positives.drop
          (AffineBatchDecoder.quota p - base.downBatch.pending.length)
        ∃ (record : Record rate) (logged : ReferencePrelaunchFollower.State p rate.eta)
          (diag : ReferenceDownReception.ReferenceDownCutOutput p rate),
          record ∈ K.take j ∧
          (record.output.followers i).downInput = some logged ∧
          (record.output.followers i).down = some diag ∧
          diag.rawComparison.isSome = true ∧
          ReferenceFirstLiveDownCompletionReadout.completedDownBatch record i = some secondBank ∧
          diag.raw = AffineBatchDecoder.batchOutput secondBank) := by
  dsimp only
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  let J := ActualInitializationPhysicalStep.selectedRowIndex p z
  let k : Fin R.length := ⟨e, he⟩
  let cut := R[e]'he
  let K := cut :: (R.drop (e + 1)).takeWhile
    (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
  let d := min j K.length
  change e < R.length at he
  have hd : d ≤ K.length := Nat.min_le_right _ _
  have hpref : K <+: R.drop e := by
    rw [List.drop_eq_getElem_cons he]
    exact List.cons_prefix_cons.mpr ⟨rfl, List.takeWhile_prefix _⟩
  have hlen : e + K.length ≤ R.length := by
    have h := hpref.length_le
    simp only [List.length_drop] at h
    omega
  have htake : K.take j = (R.drop e).take d := by
    rw [List.take_eq_take_min]
    change K.take d = _
    rw [List.prefix_iff_eq_take.mp hpref, List.take_take, Nat.min_eq_left hd]
  obtain ⟨initial, span, active, _hlaunch, _hfirst, hseed, hrecords⟩ :=
    complete_run_realization rate rewards C_star C_h z k
  change R = (ReferenceActivePhysicalHorizon.run initial z.1.2 J rewards s
    (p.T - s) span active).records at hrecords
  have hlength : R.length = p.T - s :=
    ReferenceCompletePhysicalHistory.completeSuffixRecords_length rate z rewards C_star C_h
  have hprefix (n : ℕ) (hn : n ≤ R.length) :
      (ReferenceActivePhysicalHorizon.run initial z.1.2 J rewards s n
        (by omega) active).records = R.take n := by
    obtain ⟨tail, hsplit⟩ := ReferenceCollectionPhaseHistory.run_records_prefix
      initial z.1.2 J rewards s n (p.T - s - n) (by omega) active
    have hsum : n + (p.T - s - n) = p.T - s := by omega
    have hfull : R = (ReferenceActivePhysicalHorizon.run initial z.1.2 J rewards s n
        (by omega) active).records ++ tail := by
      rw [hrecords]
      simpa only [hsum] using hsplit
    rw [hfull, List.take_append_of_le_length (by
      rw [ReferenceActivePhysicalHorizon.run_record_count])]
    rw [List.take_of_length_le (by rw [ReferenceActivePhysicalHorizon.run_record_count])]
  have hrecord (a : Fin R.length) : R[a.val] =
      ReferenceAssignmentPayloadChronology.actualRunRecordAt initial z.1.2 J rewards s a.val
        (by have ha := a.isLt; omega) active := by
    rw [List.getElem_of_eq hrecords]
    exact run_get_eq_actualRunRecordAt rate rewards initial z.1.2 J s (p.T - s)
      span active a.val (by have ha := a.isLt; omega)
  have hcutInput : cut.input.state =
      (ReferenceActivePhysicalHorizon.run initial z.1.2 J rewards s e
        (by omega) active).finalState := by
    change R[k.val].input.state = _
    rw [hrecord k]
    rfl
  have hcutTime : cut.input.time.val = s + e :=
    complete_suffix_get_time rate rewards C_star C_h z e he
  have hend : ReferenceCollectionSegmentExtraction.endpointState cut.input.state (K.take j) =
      (ReferenceActivePhysicalHorizon.run initial z.1.2 J rewards s (e + d)
        (by omega) active).finalState := by
    have hbefore := connected_endpoint_eq rate
      (ReferenceActivePhysicalHorizon.run_connected initial z.1.2 J rewards s e
        (by omega) active)
    have hafter := connected_endpoint_eq rate
      (ReferenceActivePhysicalHorizon.run_connected initial z.1.2 J rewards s (e + d)
        (by omega) active)
    rw [hprefix e (by omega)] at hbefore
    rw [hprefix (e + d) (by omega), List.take_add] at hafter
    unfold ReferenceCollectionSegmentExtraction.endpointState at hbefore hafter ⊢
    rw [List.foldl_append, hbefore, ← hcutInput, ← htake] at hafter
    exact hafter
  have hordinary (n : ℕ) (hn : n ≤ R.length) :
      ∃ state memory, (ReferenceActivePhysicalHorizon.run initial z.1.2 J rewards s n
        (by omega) active).finalState.followers i = .ordinary state memory := by
    cases n with
    | zero =>
        obtain ⟨state, memory, hconfig, _⟩ := hseed i
        exact ⟨state, memory, by rw [ReferenceActivePhysicalHorizon.run_zero_final]; exact hconfig⟩
    | succ n =>
        let a : Fin R.length := ⟨n, by omega⟩
        obtain ⟨_before, _beforeMemory, _choice, state, memory, _hinput, _hchoice,
          _hchoiceDomain, _hstateDomain, _houtput, _hfailure, hnext⟩ :=
          ReferenceCompleteSuffixFollowerPreservation.complete_suffix_follower_output
            (rate := rate) rewards C_star C_h z a i
        refine ⟨state, memory, ?_⟩
        rw [ReferenceAssignmentPayloadChronology.run_successor_finalState_eq_actualRunRecordAt,
          ← hrecord a]
        exact hnext
  obtain ⟨state, memory, hstate⟩ := hordinary (e + d) (by omega)
  obtain ⟨base, baseMemory, hbase, hinterval⟩ :=
    ReferenceFollowerDownIntervalWindow.run_interval_downBatch_replay p rate initial z.1.2 J
      rewards s e (e + d) (by omega) (by omega) active hseed i state memory hstate
  dsimp only at hinterval
  have hI : (ReferenceActivePhysicalHorizon.run initial z.1.2 J rewards s (e + d)
      (by omega) active).records.drop e = K.take j := by
    rw [hprefix (e + d) (by omega), List.drop_take, Nat.add_sub_cancel_left]
    exact htake.symm
  rw [hI] at hinterval
  obtain ⟨_hprefix, hcallsPair, hcalendar, hbank, hcollected, hquota, hstamps,
    hpositivesPair, hpositiveTimes⟩ := hinterval
  obtain ⟨secondBase, _secondMemory, hsecondBase, hsecond⟩ :=
    ReferenceFirstReplacementCollectionOldDownCountOrAmbiguity.run_interval_actual_second_completion
      initial z.1.2 J rewards s e (e + d) (by omega) (by omega) active hseed i
      state memory hstate
  have hbaseEq : secondBase = base :=
    (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
      (hsecondBase.symm.trans hbase)).1
  subst secondBase
  dsimp only at hsecond
  rw [hI] at hsecond
  refine ⟨base, state, baseMemory, memory, ?_, ?_, hbank, hcollected,
    hquota, ?_, hcallsPair, ?_, hpositivesPair, ?_, ?_⟩
  · rw [hcutInput]
    exact hbase
  · rw [hend]
    exact hstate
  · change ∀ entry ∈ base.downBatch.pending, entry.time.val < cut.input.time.val
    rw [hcutTime]
    exact hstamps
  · change ((ReferenceFollowerDownDecoderReplay.actualDownCalls i (K.take j)).map
      Prod.fst).map Fin.val =
        ReferenceActivePhysicalHorizon.calendar cut.input.time.val (K.take j).length
    rw [hcutTime, List.length_take]
    simpa only [Nat.add_sub_cancel_left] using hcalendar
  · intro entry hentry
    have h := hpositiveTimes entry hentry
    rw [hcutTime]
    simpa only [List.length_take, Nat.add_assoc] using h
  · intro hcount
    obtain ⟨_entry, record, logged, diag, _hentry, _hmax, _htime, hmem,
      hinput, hdiag, hcomparison, hcompleted, hraw, _hreset⟩ := hsecond hcount
    exact ⟨record, logged, diag, hmem, hinput, hdiag, hcomparison, hcompleted, hraw⟩

/-- Whole inherited-bank replay on every prefix of the literal actual-cut
list. The list keeps raw exit and detecting records, and the physical source
continues beyond analytic decoder failure. -/
theorem actual_live_cutoff_old_down_bank_replay
    (z : SourceInput p) (e j : ℕ) (i : Fin (p.m - 1)) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    match R[e]? with
    | none => True
    | some cut =>
      match cut.output.preparation.coordinator with
      | .live _ _ _ (.cutoffChosen _ _ _ _ _ _ _ _ _ _) =>
        let K := cut :: (R.drop (e + 1)).takeWhile
          (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
        let Z := ReferenceCollectionSegmentExtraction.endpointState cut.input.state (K.take j)
        let calls := ReferenceFollowerDownDecoderReplay.actualDownCalls i (K.take j)
        let positives := ReferenceFollowerDownDecoderReplay.actualDownPositives i (K.take j)
        ∃ (base state : ReferencePrelaunchFollower.State p rate.eta)
          (baseMemory memory : ActiveFollowerLifecycle.LocalMemory p),
          cut.input.state.followers i = .ordinary base baseMemory ∧
          Z.followers i = .ordinary state memory ∧
          state.downBatch = ReferenceFollowerDownDecoderReplay.foldDownCalls calls base.downBatch ∧
          AffineBatchDecoder.collected state.downBatch =
            AffineBatchDecoder.collected base.downBatch ++ positives ∧
          base.downBatch.pending.length < AffineBatchDecoder.quota p ∧
          (∀ entry ∈ base.downBatch.pending, entry.time.val < cut.input.time.val) ∧
          calls.Pairwise (fun first second => first.1.val < second.1.val) ∧
          (calls.map Prod.fst).map Fin.val =
            ReferenceActivePhysicalHorizon.calendar cut.input.time.val (K.take j).length ∧
          positives.Pairwise (fun first second => first.time.val < second.time.val) ∧
          (∀ entry ∈ positives, cut.input.time.val ≤ entry.time.val ∧
            entry.time.val < cut.input.time.val + (K.take j).length) ∧
          (positives.length = AffineBatchDecoder.quota p - base.downBatch.pending.length +
              AffineBatchDecoder.quota p →
            let secondBank := positives.drop
              (AffineBatchDecoder.quota p - base.downBatch.pending.length)
            ∃ (record : Record rate) (logged : ReferencePrelaunchFollower.State p rate.eta)
              (diag : ReferenceDownReception.ReferenceDownCutOutput p rate),
              record ∈ K.take j ∧
              (record.output.followers i).downInput = some logged ∧
              (record.output.followers i).down = some diag ∧
              diag.rawComparison.isSome = true ∧
              ReferenceFirstLiveDownCompletionReadout.completedDownBatch record i = some secondBank ∧
              diag.raw = AffineBatchDecoder.batchOutput secondBank)
      | _ => True := by
  dsimp only
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  cases hget : R[e]? with
  | none => trivial
  | some cut =>
      simp only
      obtain ⟨he, hcut⟩ := List.getElem?_eq_some_iff.mp hget
      have hreplay := raw_cut_down_bank_replay rate rewards C_star C_h z e j he i
      dsimp only at hreplay
      rw [show (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[e] = cut from hcut] at hreplay
      cases hbranch : cut.output.preparation.coordinator with
      | first outcome => trivial
      | collection payload ledger clock cutoff outcome => trivial
      | invalidCollectionCutoff => trivial
      | dagger => trivial
      | live registers owned base outcome =>
          cases outcome with
          | continuingChosen dispatched hstart continuation selected => trivial
          | clockFailure failure hfailure => trivial
          | initializerFailure dispatched hstart checked hfailure => trivial
          | localFailure dispatched hstart failure => trivial
          | cutoffChosen dispatched hstart ledger hinitialization hledger hdomains
              hclock hpending hassignment selected => exact hreplay

private theorem collection_choice_next_payload
    (r : Record rate) (c : ReferenceCollectionSegmentExtraction.Choice rate)
    (hc : ReferenceCollectionSegmentExtraction.choice r.input = some c) :
    r.output.next.coordinator = .dagger ∨
      ∃ ledger saved, r.output.next.coordinator = .collection c.payload ledger saved := by
  have htail := ReferenceCollectionSegmentExtraction.choice_tail r.input c hc
  have hout : r.output.next.coordinator =
      (ReferenceActivePhysicalStep.collectionPostChoice (ReferenceActivePhysicalStep.prepare r.input)
        c.payload c.preLedger c.started c.weights).configuration := by
    rw [r.output_eq]
    exact congrArg ReferenceActivePhysicalStep.CoordinatorObservation.configuration htail
  have hphase := ReferenceCollectionPhaseHistory.collectionPostChoice_no_installation
    (ReferenceActivePhysicalStep.prepare r.input) c.payload c.preLedger c.started c.weights
  have hframe := ReferenceAssignmentPayloadPersistence.collectionPostChoice_payload_frame
    (ReferenceActivePhysicalStep.prepare r.input) c.payload c.preLedger c.started c.weights
  rw [← hout] at hphase hframe
  rcases hphase with hdagger | ⟨P, ledger, saved, hcollection⟩
  · exact Or.inl hdagger
  · have hpayload : P = c.payload := by
      rw [hcollection] at hframe
      rcases hframe with hnone | hsome
      · cases hnone
      · exact Option.some.inj hsome
    exact Or.inr ⟨ledger, saved, by rw [← hpayload]; exact hcollection⟩

private theorem no_selection_next_dagger (r : Record rate)
    (hnone : r.output.preparation.coordinator.selection = none) :
    r.output.next.coordinator = .dagger := by
  have hnone' : (ReferenceActivePhysicalStep.prepare r.input).coordinator.selection = none := by
    simpa only [r.output_eq, ReferenceActivePhysicalStep.step] using hnone
  rw [r.output_eq]
  change (ReferenceActivePhysicalStep.prepare r.input).observeCoordinator.configuration = .dagger
  unfold ReferenceActivePhysicalStep.PreparedRound.observeCoordinator
  rw [dite_eq_left hnone']
  cases (ReferenceActivePhysicalStep.prepare r.input).coordinator <;> rfl

private theorem collection_input_next_payload
    (r : Record rate) (P : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate) (saved : Option (Fin p.T × Bool))
    (hstate : r.input.state.coordinator = .collection P ledger saved)
    (hn : ReferenceCollectionPhaseHistory.laterChosen r.input = false) :
    r.output.next.coordinator = .dagger ∨
      ∃ nextLedger nextSaved, r.output.next.coordinator = .collection P nextLedger nextSaved := by
  classical
  by_cases hnone : r.output.preparation.coordinator.selection = none
  · exact Or.inl (no_selection_next_dagger rate r hnone)
  have hprep : r.output.preparation = ReferenceActivePhysicalStep.prepare r.input := by
    rw [r.output_eq]
    rfl
  by_cases hv : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
  · let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
    let clock := ReferenceActivePhysicalStep.collectionClock P ledger saved cutoff
    let x := ReferenceActivePhysicalStep.collectionInput r.input P ledger clock cutoff
    have hdispatch : r.output.preparation.coordinator =
        .collection P ledger clock cutoff (CoordinatorRoundDispatch.dispatchCollection x) := by
      rw [hprep]
      simp only [ReferenceActivePhysicalStep.prepare, ReferenceActivePhysicalStep.dispatch,
        hstate, dite_eq_left hv, CoordinatorRoundDispatch.dispatch]
      rfl
    cases ho : CoordinatorRoundDispatch.dispatchCollection x with
    | continuing core snapshot boundary scores =>
        let c : ReferenceCollectionSegmentExtraction.Choice rate :=
          ⟨P, ledger, snapshot.clockStarted,
            CoordinatorCollectionInteractive.PreObservationInputs.weights x
              snapshot.inputsValid.ledger_valid snapshot.inputsValid.assignment_eq, none⟩
        have hc : ReferenceCollectionSegmentExtraction.choice r.input = some c := by
          unfold ReferenceCollectionSegmentExtraction.choice
          rw [← hprep, ite_eq_right hnone, hdispatch, ho]
          rfl
        exact collection_choice_next_payload rate r c hc
    | laterChosen core consistent started hs instruction hi output he data installed selected =>
        unfold ReferenceCollectionPhaseHistory.laterChosen at hn
        rw [← hprep, hdispatch, ho] at hn
        cases hn
    | _ =>
        exfalso
        apply hnone
        simp only [hdispatch, ho, ReferenceActivePhysicalStep.DispatchCut.selection]
  · apply (hnone ?_).elim
    rw [hprep]
    simp only [ReferenceActivePhysicalStep.prepare, ReferenceActivePhysicalStep.dispatch,
      hstate, dite_eq_right hv, ReferenceActivePhysicalStep.DispatchCut.selection]

private theorem connected_collection_payload
    {initial final : ReferenceActivePhysicalStep.State p rate}
    {records : List (Record rate)}
    (P : ReferenceActivePhysicalStep.Payload rate)
    (hchain : ReferenceActivePhysicalHorizon.Connected initial records final)
    (hphase : initial.coordinator = .dagger ∨
      ∃ ledger saved, initial.coordinator = .collection P ledger saved)
    (hno : ∀ r ∈ records, ReferenceCollectionPhaseHistory.laterChosen r.input = false) :
    ∀ r ∈ records, r.input.state.coordinator = .dagger ∨
      ∃ ledger saved, r.input.state.coordinator = .collection P ledger saved := by
  induction records generalizing initial with
  | nil => intro r hr; cases hr
  | cons r rest ih =>
      have hinput : r.input.state.coordinator = .dagger ∨
          ∃ ledger saved, r.input.state.coordinator = .collection P ledger saved := by
        rw [hchain.1]
        exact hphase
      have hnext : r.output.next.coordinator = .dagger ∨
          ∃ ledger saved, r.output.next.coordinator = .collection P ledger saved := by
        rcases hinput with hd | ⟨ledger, saved, hc⟩
        · left
          rw [r.output_eq]
          exact (ReferenceActivePhysicalStep.step_coordinator_dagger r.input hd).1
        · exact collection_input_next_payload rate r P ledger saved hc (hno r List.mem_cons_self)
      intro current hcurrent
      rcases List.mem_cons.mp hcurrent with hhead | hrest
      · simpa only [hhead] using hinput
      · exact ih hchain.2 hnext (fun r hr => hno r (List.mem_cons_of_mem _ hr)) current hrest

/-- Before an actual OLD choice, every earlier accepted UP for this follower
has a strictly older start. This uses the actual accepted sender choice and
the original connected history; no pending-history premise is supplied. -/
theorem actual_stored_old_prior_up_start_lt (z : SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (P : ReferenceActivePhysicalStep.Payload rate)
    (hstored : ReferenceAssignmentPayloadPersistence.storedPayload
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[k.val].input.state.coordinator = some P)
    (i : Fin (p.m - 1))
    (hold : ReferenceFirstReplacementCollectionOldDownCallDates.actualOldAt
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[k.val] i (P.downRecord i)) :
    ∀ a : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length, a.val < k.val →
      ∀ U : ReferenceCollectionPhaseHistory.UpRecord p rate,
        ReferenceCollectionPhaseHistory.AcceptedUp
          (ReferenceCompletePhysicalHistory.completeSuffixRecords
            rate z rewards C_star C_h)[a.val].input i U →
        U.val.sigma < (P.downRecord i).val.sigma := by
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  obtain ⟨right, rightMemory, hright, _hunoccupied, hnotCurrent⟩ := hold
  have horder := actual_stored_choice_current_or_older rate rewards C_star C_h
    z k P hstored i right rightMemory hright
  have hstrict := horder.resolve_left hnotCurrent
  obtain ⟨initial, span, active, _hlaunch, _hfirst, _hseed, hrecords⟩ :=
    complete_run_realization rate rewards C_star C_h z k
  have hchain := ReferenceActivePhysicalHorizon.run_connected initial z.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards _ _ span active
  rw [← hrecords] at hchain
  intro a hak U haccepted
  obtain ⟨sender, left, leftMemory, hsender, hindex, hleft, _hleftStatus,
    _hoffer, hsigma, _hrest⟩ := ReferenceAcceptedUpFollowerHistory.acceptedUp_current_choice haccepted
  have hprep : R[a.val].output.preparation = ReferenceActivePhysicalStep.prepare R[a.val].input := by
    rw [(R[a.val]).output_eq]
    rfl
  have hleft' : (ReferenceFollowerFixedReply.actualChoice R[a.val] i).configuration =
      .ordinary left leftMemory := by
    change (R[a.val].output.preparation.followers.followers i).configuration = _
    rw [hprep, hindex, ← hsender]
    exact hleft
  have hmono := (ReferenceFollowerReplyChronology.connected_choice_chronology hchain i
    a.val k.val a.isLt k.isLt (Nat.le_of_lt hak) left right leftMemory rightMemory
    hleft' hright).1
  calc
    U.val.sigma = ReferencePrelaunchFollower.acceptedStart left := hsigma
    _ ≤ ReferencePrelaunchFollower.acceptedStart right := hmono
    _ < (P.downRecord i).val.sigma := hstrict

/-- Every selected record in the raw local cutoff list keeps the original
payload. On its actual pending/OLD domain every selected DOWN call, including
zero feedback, is awaited by the canonical original-source dictionary. -/
theorem actual_live_cutoff_old_down_fixed_awaited_prefix
    (z : SourceInput p) (e : ℕ) (i : Fin (p.m - 1)) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    match R[e]? with
    | none => True
    | some cut =>
      match cut.output.preparation.coordinator with
      | .live registers _ _ (.cutoffChosen _ _ _ _ _ _ _ _ _ _) =>
        let P := registers.payload
        let M := P.downRecord i
        let K := cut :: (R.drop (e + 1)).takeWhile
          (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
        ∀ a : Fin K.length, ∃ k : Fin R.length,
          k.val = e + a.val ∧ R[k.val] = K.get a ∧
          ∀ selected : ReferenceActivePhysicalStep.Selection R[k.val].input,
            R[k.val].output.preparation.coordinator.selection = some selected →
            selected.view.payload = P ∧
            ReferenceAssignmentPayloadPersistence.storedPayload
              R[k.val].input.state.coordinator = some P ∧
            ((∃ (choice : ReferencePrelaunchFollower.State p rate.eta)
                (memory : ActiveFollowerLifecycle.LocalMemory p),
                (ReferenceFollowerFixedReply.actualChoice cut i).configuration =
                  .ordinary choice memory ∧ choice.lastDown = some M) →
              ¬ ReferenceFirstReplacementCollectionOldDownCallDates.actualOldAt R[k.val] i M) ∧
            (ReferenceFirstReplacementCollectionOldDownCallDates.actualOldAt R[k.val] i M →
              ∀ b : Fin R.length, b.val < k.val →
                ∀ U : ReferenceCollectionPhaseHistory.UpRecord p rate,
                  ReferenceCollectionPhaseHistory.AcceptedUp R[b.val].input i U →
                    U.val.sigma < M.val.sigma) ∧
            (i ∈ selected.view.pendingAtChoice →
              ReferenceFirstReplacementCollectionOldDownCallDates.actualOldAt R[k.val] i M →
              ActiveFollowerDownAcceptance.downSelected p i R[k.val].input.row R[k.val].input.time →
              ReferenceCompleteAwaitedBatchSourceCoverage.originalDownAwaitedCallAt rate
                R[k.val] i (CoordinatorLocalArmChoice.storedDownFlatWord P i) ∧
              ReferenceCompleteAwaitedBatchSourceCoverage.sourceDownAwaitedAt
                rate rewards C_star C_h z i
                (CoordinatorLocalArmChoice.storedDownFlatWord P i) R[k.val].input.time)
      | _ => True := by
  dsimp only
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  cases hget : R[e]? with
  | none => trivial
  | some cut =>
      simp only
      obtain ⟨he, hcut⟩ := List.getElem?_eq_some_iff.mp hget
      subst cut
      let cut := R[e]'he
      have hcut : R[e]'he = cut := rfl
      cases hbranch : cut.output.preparation.coordinator with
      | first outcome => trivial
      | collection payload ledger clock cutoff outcome => trivial
      | invalidCollectionCutoff => trivial
      | dagger => trivial
      | live registers owned base outcome =>
        cases outcome with
        | continuingChosen dispatched hstart continuation selected => trivial
        | clockFailure failure hfailure => trivial
        | initializerFailure dispatched hstart checked hfailure => trivial
        | localFailure dispatched hstart failure => trivial
        | cutoffChosen dispatched hstart ledger hinitialization hledger hdomains
            hclock hpending hassignment selected =>
          dsimp only
          have hinit := actual_live_cutoff_old_down_initialization
            rate rewards C_star C_h z e i
          dsimp only at hinit
          rw [show (ReferenceCompletePhysicalHistory.completeSuffixRecords
            rate z rewards C_star C_h)[e]? = some cut from hget] at hinit
          dsimp only at hinit
          rw [hbranch] at hinit
          dsimp only at hinit
          obtain ⟨c, _b, hc, hcP, hstored, _rest⟩ := hinit
          let W := (R.drop (e + 1)).takeWhile
            (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
          let K := cut :: W
          have hpref : K <+: R.drop e := by
            rw [List.drop_eq_getElem_cons he, hcut]
            exact List.cons_prefix_cons.mpr ⟨rfl, List.takeWhile_prefix _⟩
          have hlen : e + K.length ≤ R.length := by
            have h := hpref.length_le
            have he' : e < R.length := he
            simp only [List.length_drop] at h
            omega
          let entry : Fin R.length := ⟨e, he⟩
          obtain ⟨span, active, hrun⟩ :=
            ReferenceCompleteFollowerRetainedDownRecovery.complete_input_suffix_reindex
              (rate := rate) rewards C_star C_h z entry K.length hlen
          have hrun' : (ReferenceActivePhysicalHorizon.run cut.input.state z.1.2
              (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards
              cut.input.time.val K.length span active).records = K := by
            exact hrun.trans (List.prefix_iff_eq_take.mp hpref).symm
          have hchain := ReferenceActivePhysicalHorizon.run_connected cut.input.state z.1.2
            (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards
            cut.input.time.val K.length span active
          rw [hrun'] at hchain
          have hnext := collection_choice_next_payload rate cut c hc
          rw [hcP] at hnext
          have hno : ∀ r ∈ W, ReferenceCollectionPhaseHistory.laterChosen r.input = false := by
            intro r hr
            have h := List.mem_takeWhile_imp hr
            cases hn : ReferenceCollectionPhaseHistory.laterChosen r.input with
            | false => rfl
            | true => rw [hn] at h; cases h
          have htail := connected_collection_payload rate registers.payload hchain.2 hnext hno
          change ∀ a : Fin K.length, _
          intro a
          have hak : e + a.val < R.length := by
            have ha : a.val < K.length := a.isLt
            omega
          let k : Fin R.length := ⟨e + a.val, hak⟩
          have hrecord : R[k.val] = K.get a := by
            have h := hpref.getElem a.isLt
            simpa only [List.getElem_drop, List.get_eq_getElem] using h.symm
          refine ⟨k, rfl, hrecord, ?_⟩
          intro physical hphysical
          have hfields : physical.view.payload = registers.payload ∧
              ReferenceAssignmentPayloadPersistence.storedPayload
                R[k.val].input.state.coordinator = some registers.payload := by
            by_cases ha0 : a.val = 0
            · have hhead : R[k.val] = cut := by
                rw [hrecord]
                change K[a.val] = cut
                simp only [ha0, K, List.getElem_cons_zero]
              have hstored' : ReferenceAssignmentPayloadPersistence.storedPayload
                  R[k.val].input.state.coordinator = some registers.payload := by
                rw [hhead]
                exact hstored
              have hlocal :=
                ReferenceSelectedPayloadChronology.actualSelectedPayload_local_stored_or_birth
                  R[k.val] physical hphysical
              rcases hlocal with hsame | hborn
              · exact ⟨(Option.some.inj (hstored'.symm.trans hsame)).symm, hstored'⟩
              · have hnoBirth : ∀ Q : ReferenceActivePhysicalStep.Payload rate,
                    ¬ ReferenceAssignmentPayloadPersistence.InstallationBirth R[k.val] Q := by
                  rw [hhead]
                  intro Q
                  unfold ReferenceAssignmentPayloadPersistence.InstallationBirth
                  rw [hbranch]
                  exact id
                exact (hnoBirth physical.view.payload hborn).elim
            · have haW : a.val - 1 < W.length := by
                have ha := a.isLt
                change a.val < W.length + 1 at ha
                omega
              have htailRecord : K.get a = W[a.val - 1]'haW := by
                have ha : a.val = (a.val - 1) + 1 := by omega
                have haIndex : a = (⟨(a.val - 1) + 1, by
                    change (a.val - 1) + 1 < W.length + 1
                    omega⟩ : Fin K.length) := Fin.ext ha
                calc
                  K.get a = K.get ⟨(a.val - 1) + 1, by
                    change (a.val - 1) + 1 < W.length + 1
                    omega⟩ := congrArg (fun b => K.get b) haIndex
                  _ = _ := rfl
              have hmem : R[k.val] ∈ W := by
                rw [hrecord, htailRecord]
                exact List.getElem_mem haW
              rcases htail R[k.val] hmem with hd | ⟨l, saved, hc⟩
              · have hs := hphysical
                rw [(R[k.val]).output_eq] at hs
                simp only [ReferenceActivePhysicalStep.step, ReferenceActivePhysicalStep.prepare,
                  ReferenceActivePhysicalStep.dispatch, hd, CoordinatorRoundDispatch.dispatch,
                  ReferenceActivePhysicalStep.DispatchCut.selection] at hs
                cases hs
              · have hp :=
                  ReferenceFirstReplacementCollectionOldDownSenderReadiness.collection_selection_pending
                    R[k.val] registers.payload l saved hc (hno _ hmem) physical hphysical
                exact ⟨hp.1, by rw [hc]; rfl⟩
          refine ⟨hfields.1, hfields.2, ?_, ?_, ?_⟩
          · rintro ⟨left, leftMemory, hleft, hcurrent⟩
            rintro ⟨right, rightMemory, hright, _hunoccupied, hnotCurrent⟩
            have horder := actual_stored_choice_current_or_older rate rewards C_star C_h
              z k registers.payload hfields.2 i right rightMemory hright
            have hstrict := horder.resolve_left hnotCurrent
            have hleft' : (ReferenceFollowerFixedReply.actualChoice K[0] i).configuration =
                .ordinary left leftMemory := hleft
            have hright' : (ReferenceFollowerFixedReply.actualChoice K[a.val] i).configuration =
                .ordinary right rightMemory := by
              change (ReferenceFollowerFixedReply.actualChoice (K.get a) i).configuration = _
              rw [← hrecord]
              exact hright
            have hmono := (ReferenceFollowerReplyChronology.connected_choice_chronology hchain
              i 0 a.val (by simp only [K, List.length_cons]; omega) a.isLt (Nat.zero_le _)
              left right leftMemory rightMemory hleft' hright').1
            have hstart : ReferencePrelaunchFollower.acceptedStart left =
                (registers.payload.downRecord i).val.sigma := by
              simp only [ReferencePrelaunchFollower.acceptedStart, hcurrent]
            omega
          · exact actual_stored_old_prior_up_start_lt rate rewards C_star C_h
              z k registers.payload hfields.2 i
          · intro hi hold hdown
            have hawaited := actual_stored_old_down_awaited rate rewards C_star C_h
              z k registers.payload hfields.2 physical hphysical hfields.1 i hi hold hdown
            refine ⟨hawaited, ?_⟩
            unfold ReferenceCompleteAwaitedBatchSourceCoverage.sourceDownAwaitedAt
            rw [actualRecord_at_completeSuffix_get rate rewards C_star C_h z k.val k.isLt]
            exact hawaited

end Bandits.Support.ReferenceOriginalCollectionOldDownChronology
