/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedLiveConfirmationAcceptedDown
public import Bandits.Support.ReferenceGeneratedSelectedSuccessorStaleCut

import Lean.Elab.Tactic.Omega

/-!
# Selected LIVE stale DOWN exclusion

Sources: `sources/zip4/manuscript/appendix_a_local_protocol.tex:92-109`,
`sources/zip4/manuscript/05_binary_transport.tex:60-124`, and
`sources/zip4/manuscript/06_interruptions.tex:270-295,327-348`.

The first result excludes a wrong accepted DOWN cut whose raw word is the
currently selected LIVE payload word. The second excludes a strictly earlier
selected LIVE test word from that same cut. Both keep the original generated
run, launch source, rows, rewards, and private coordinates. These are local
internal results, not a source-event or regret closure.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions
open ReferenceActivePhysicalStep
open ReferenceActivePhysicalHorizon
open ReferenceFollowerReplyChronology
open ReferencePrelaunchFollower
open ReferenceGeneratedDownBatchCalendar
open ReferenceGeneratedInheritedDownWrongCompletionWitness

namespace Bandits.Support.ReferenceGeneratedLiveStaleDownExclusion

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

private theorem wrong_cut_raw_parse_and_receiver_gate
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1))
    (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
    (word : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (hcut : (record.output.followers i).down = some cut)
    (hwrong : ReferenceDownReception.wrongUniqueAccepted cut)
    (hraw : cut.raw = some word) :
    ∃ logged,
      cut = ReferenceDownReception.referenceDownCut p
        record.output.preparation.coordinator.downView i record.input.row record.input.time
        (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i) rate logged ∧
      ActiveFollowerDownAcceptance.downSelected p i record.input.row record.input.time ∧
      logged.status = .unoccupied ∧
      ActiveFollowerDownAcceptance.registerInputDomain p rate logged ∧
      ActiveFollowerDownAcceptance.decoderInputDomain p logged.downBatch ∧
      ActiveFollowerDownAcceptance.bufferInputDomain p logged.buffer ∧
      cut.ordinaryParse = ReferenceDownReception.ordinaryParse p rate (some word) := by
  obtain ⟨_choice, _memory, logged, _hconfiguration, _hunoccupied, _hlogging,
      hlogged, _hcutFromChoice⟩ :=
    ReferenceFollowerSparseEmissionRecovery.actualDownDiagnostic_choice
      record i cut hcut
  have hcutActual := ReferenceDownCompletedAmbiguityMeasurability.record_downCut_eq_actual
    record i logged cut hlogged hcut
  have hfalse := hwrong.1
  rw [hcutActual] at hfalse
  have hraw' := hraw
  rw [hcutActual] at hraw'
  let view := record.output.preparation.coordinator.downView
  let row := record.input.row
  let time := record.input.time
  let observation := ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i
  have hselected : ActiveFollowerDownAcceptance.downSelected p i row time := by
    by_contra hnot
    simp [ReferenceDownReception.referenceDownCut, row, time, hnot] at hfalse
  have hstatus : logged.status = .unoccupied := by
    by_contra hnot
    simp [ReferenceDownReception.referenceDownCut, row, time,
      hselected, hnot] at hfalse
  have hregisters : ActiveFollowerDownAcceptance.registerInputDomain p rate logged := by
    by_contra hnot
    simp [ReferenceDownReception.referenceDownCut, row, time,
      hselected, hstatus, hnot] at hfalse
  have hbatch : ActiveFollowerDownAcceptance.decoderInputDomain p logged.downBatch := by
    by_contra hnot
    simp [ReferenceDownReception.referenceDownCut, row, time,
      hselected, hstatus, hregisters, hnot] at hfalse
  have hbuffer : ActiveFollowerDownAcceptance.bufferInputDomain p logged.buffer := by
    by_contra hnot
    simp [ReferenceDownReception.referenceDownCut, row, time,
      hselected, hstatus, hregisters, hbatch, hnot] at hfalse
  have hpreserved := ReferenceDownReception.referenceDownCut_raw_mismatch_preserves
    view i row time observation rate logged hselected hstatus hregisters hbatch hbuffer
    (by simpa only [ReferenceDownReception.rawMismatch] using hfalse)
  rcases hpreserved with ⟨_, hrawDecode, _, hparse, _, _⟩
  have hdecoded :
      (ActiveFollowerDownAcceptance.currentDecodeStep p i row time observation rate logged).2 =
        some word := hrawDecode.symm.trans hraw'
  have hparseWord :
      (ReferenceDownReception.referenceDownCut p view i row time observation rate logged).ordinaryParse =
        ReferenceDownReception.ordinaryParse p rate (some word) := by
    calc
      _ = ReferenceDownReception.ordinaryParse p rate
          (ActiveFollowerDownAcceptance.currentDecodeStep p i row time observation rate logged).2 :=
        hparse
      _ = ReferenceDownReception.ordinaryParse p rate (some word) :=
        congrArg (ReferenceDownReception.ordinaryParse p rate) hdecoded
  refine ⟨logged, hcutActual, hselected, hstatus, hregisters, hbatch, hbuffer, ?_⟩
  rw [hcutActual]
  exact hparseWord

private theorem accepted_down_start_le_later_actual_choice
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (x : ReferenceGeneratedDownBatchCalendar.LaunchSource rate rewards C_star C_h s hs)
    (a n : Fin (p.T - s)) (han : a.val < n.val)
    (i : Fin (p.m - 1))
    (M : OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (haccepted : ReferenceFirstLiveConfirmationHistory.AcceptedDown
      (ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt
        rate rewards C_star C_h s hs x a) i M)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hchoice : (ReferenceFollowerFixedReply.actualChoice
      (ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt
        rate rewards C_star C_h s hs x n) i).configuration = .ordinary state memory) :
    M.val.sigma ≤ ReferencePrelaunchFollower.acceptedStart state := by
  let R := ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt
    rate rewards C_star C_h s hs x
  let seed := ReferenceGeneratedDownBatchCalendar.generatedSourceSeed
    rate rewards C_star C_h s hs x
  let full := ReferenceActivePhysicalHorizon.run seed x.1.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p x.1) rewards s (p.T - s)
    (by omega) (ReferenceGeneratedDownBatchCalendar.generatedSourceSeed_spec
      rate rewards C_star C_h s hs x).2.1
  have hfullEq : full = ReferenceGeneratedDownBatchCalendar.generatedSourceRun
      rate rewards C_star C_h s hs x := by
    rfl
  have hrecordsEq : full.records =
      (ReferenceGeneratedDownBatchCalendar.generatedSourceRun
        rate rewards C_star C_h s hs x).records :=
    congrArg (fun run => run.records) hfullEq
  have hcount : full.records.length = p.T - s := by
    exact ReferenceActivePhysicalHorizon.run_record_count _ _ _ _ _ _ _ _
  have hgetAOption : full.records[a.val]? = some (R a) := by
    calc
      full.records[a.val]? =
          (ReferenceGeneratedDownBatchCalendar.generatedSourceRun
            rate rewards C_star C_h s hs x).records[a.val]? :=
        congrArg (fun records => records[a.val]?) hrecordsEq
      _ = some (R a) :=
        ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt_getElem?
          rate rewards C_star C_h s hs x a
  have hgetNOption : full.records[n.val]? = some (R n) := by
    calc
      full.records[n.val]? =
          (ReferenceGeneratedDownBatchCalendar.generatedSourceRun
            rate rewards C_star C_h s hs x).records[n.val]? :=
        congrArg (fun records => records[n.val]?) hrecordsEq
      _ = some (R n) :=
        ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt_getElem?
          rate rewards C_star C_h s hs x n
  have haBound : a.val < full.records.length := by
    rw [hcount]
    exact a.isLt
  have hnBound : n.val < full.records.length := by
    rw [hcount]
    exact n.isLt
  have hgetA : full.records[a.val] = R a := by
    rw [List.getElem?_eq_getElem haBound] at hgetAOption
    exact Option.some.inj hgetAOption
  have hgetN : full.records[n.val] = R n := by
    rw [List.getElem?_eq_getElem hnBound] at hgetNOption
    exact Option.some.inj hgetNOption
  have hchoiceFull : (ReferenceFollowerFixedReply.actualChoice full.records[n.val] i).configuration =
      .ordinary state memory := by
    rw [hgetN]
    exact hchoice
  obtain ⟨before, beforeMemory, hbefore, hreply, _⟩ :=
    ReferenceFollowerReplyChronology.record_input_to_choice full.records[n.val] i
      state memory hchoiceFull
  have hstart := ReferenceFollowerReplyChronology.acceptedStart_eq_of_reply_eq hreply
  have hprefix := ReferenceFollowerReplyChronology.connected_take_to_input
    full.connected n.val hnBound
  have haPrefix : a.val < (full.records.take n.val).length := by
    simp only [List.length_take]
    exact Nat.lt_min.mpr ⟨han, haBound⟩
  obtain ⟨next, nextMemory, houtput, hbound⟩ :=
    ReferenceFollowerReplyChronology.connected_output_chronology hprefix i before
      beforeMemory hbefore a.val haPrefix
  rw [List.getElem_take (xs := full.records) (j := n.val) (i := a.val)
    (h := haPrefix)] at houtput
  rw [hgetA] at houtput
  rcases haccepted with
    ⟨logged, cut, after, raw, scan, registers, lastService, hinput, hdown, houtcome⟩
  have happlied : ReferenceFollowerReplyChronology.appliedDown (R a) i M.val.sigma := by
    exact ⟨logged, cut, after, raw, M, scan, registers, lastService,
      hinput, hdown, houtcome, rfl⟩
  obtain ⟨_choice, _choiceMemory, _hchoice, _hstrict, hin⟩ :=
    ReferenceFollowerReplyChronology.record_appliedDown_strict (R a) i M.val.sigma
      happlied next nextMemory houtput
  calc
    M.val.sigma = ReferencePrelaunchFollower.acceptedStart next := hin.symm
    _ ≤ ReferencePrelaunchFollower.acceptedStart before := hbound
    _ = ReferencePrelaunchFollower.acceptedStart state := hstart.symm

/-- A wrong uniquely accepted current LIVE cut cannot carry the current
selected payload's stored DOWN word. The ordinary parser and unoccupied
CHOICE are derived from the actual retained cut; no successful current
recovery or FINISH is required. -/
theorem generated_live_current_payload_raw_down_excluded
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (x : ReferenceGeneratedDownBatchCalendar.LaunchSource rate rewards C_star C_h s hs)
    (n : Fin (p.T - s)) (i : Fin (p.m - 1)) :
    let R := ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt
      rate rewards C_star C_h s hs x
    match (R n).output.preparation.coordinator with
    | .live _ _ _ (.continuingChosen _ _ _ _) =>
        ∀ v : ReferenceActivePhysicalStep.Selection (R n).input,
          (R n).output.preparation.coordinator.selection = some v →
        ∀ cut : ReferenceDownReception.ReferenceDownCutOutput p rate,
          ((R n).output.followers i).down = some cut →
          ReferenceDownReception.wrongUniqueAccepted cut →
          cut.raw ≠ some (CoordinatorLocalArmChoice.storedDownFlatWord v.view.payload i)
    | _ => True := by
  classical
  dsimp only
  let R := ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt
    rate rewards C_star C_h s hs x
  cases hcoordinator : (R n).output.preparation.coordinator with
  | first _ => trivial
  | live endpoint endpointOwned endpointBase outcome =>
      cases outcome with
      | continuingChosen _ _ _ _ =>
          intro v hv cut hcut hwrong hraw
          obtain ⟨logged, hcutActual, hdownSelected, hstatus, hregisters, hbatch,
              hbuffer, hparseRaw⟩ :=
            wrong_cut_raw_parse_and_receiver_gate (R n) i cut
              (CoordinatorLocalArmChoice.storedDownFlatWord v.view.payload i)
              hcut hwrong hraw
          have hparseStored :
              ReferenceDownReception.ordinaryParse p rate
                (some (CoordinatorLocalArmChoice.storedDownFlatWord v.view.payload i)) =
              some (v.view.payload.downRecord i) := by
            unfold ReferenceDownReception.ordinaryParse CoordinatorLocalArmChoice.storedDownFlatWord
            change OrdinaryMessageCodec.parseDown
              (ReferencePrelaunchFollower.codecParams p rate.eta)
              (some ((OrdinaryMessageCodec.wordEquivFlat _).symm
                ((OrdinaryMessageCodec.wordEquivFlat _) (v.view.payload.downWord i)))) = _
            exact (congrArg (fun word => OrdinaryMessageCodec.parseDown
              (ReferencePrelaunchFollower.codecParams p rate.eta) (some word))
              ((OrdinaryMessageCodec.wordEquivFlat _).symm_apply_apply
              (v.view.payload.downWord i))).trans (v.view.payload.parseDown_downWord i)
          have hparse : cut.ordinaryParse = some (v.view.payload.downRecord i) :=
            hparseRaw.trans hparseStored
          obtain ⟨state, memory, hchoice, _hunoccupied, hstrict⟩ :=
            ReferenceFirstLiveRawDownExclusion.retained_raw_down_parse_acceptance_actual_choice
              (R n) i cut (v.view.payload.downRecord i) hcut hparse hwrong.2.2
          by_cases hpending : i ∈ v.view.pendingAtChoice
          · have hview : (R n).output.preparation.coordinator.downView = some v.view := by
              change Option.map Selection.view
                ((R n).output.preparation.coordinator.selection) = some v.view
              rw [hcoordinator, hv]
              rfl
            have hbranch : ReferenceDownReception.selectedDownSenderBranch v.view i
                (R n).input.row (R n).input.time :=
              ⟨hdownSelected.1, hdownSelected.2, hpending⟩
            have hexpected := v.expected_down_word i hbranch
            have hfalse := hwrong.1
            rw [hcutActual] at hfalse
            have hcompared :
                (ReferenceDownReception.referenceDownCut p
                  (R n).output.preparation.coordinator.downView i (R n).input.row
                  (R n).input.time (ReferenceFollowerDownDecoderReplay.preparedOwnObservation
                    (R n) i) rate logged).rawComparison ≠ none := by
              rw [hfalse]
              decide
            have hrawDecode :=
              ReferenceDownReception.referenceDownCut_raw_eq_currentDecodeStep_of_compared
                (R n).output.preparation.coordinator.downView i (R n).input.row
                (R n).input.time
                (ReferenceFollowerDownDecoderReplay.preparedOwnObservation (R n) i)
                rate logged hcompared
            have hraw' := hraw
            rw [hcutActual] at hraw'
            have hexpectedCurrent :
                ReferenceDownReception.expectedDownFlatWord
                  (R n).output.preparation.coordinator.downView i (R n).input.row
                  (R n).input.time =
                some (CoordinatorLocalArmChoice.storedDownFlatWord v.view.payload i) := by
              rw [hview]
              exact hexpected
            have hdecodeWord := hrawDecode.symm.trans hraw'
            have hdecodedExpected :
                (ActiveFollowerDownAcceptance.currentDecodeStep p i (R n).input.row
                  (R n).input.time
                  (ReferenceFollowerDownDecoderReplay.preparedOwnObservation (R n) i)
                  rate logged).2 =
                ReferenceDownReception.expectedDownFlatWord
                  (R n).output.preparation.coordinator.downView i (R n).input.row
                  (R n).input.time :=
              hdecodeWord.trans hexpectedCurrent.symm
            simp [ReferenceDownReception.referenceDownCut, hdownSelected, hstatus,
              hregisters, hbatch, hbuffer, hdecodedExpected] at hfalse
          · have hprior :=
              ReferenceGeneratedLiveConfirmationAcceptedDown.generated_live_missing_pending_prior_accepted_down
                rate rewards C_star C_h s hs x n i
            dsimp only at hprior
            rw [hcoordinator] at hprior
            obtain ⟨a, han, haccepted, _k, _hak, _hkn, _w, _hw, _hpayload,
                _hdraw, _stateK, _memoryK, _hchoiceK, _hevent⟩ :=
              hprior v hv state memory hchoice hpending
            have hbound := accepted_down_start_le_later_actual_choice
              rewards C_star C_h s hs x a n han i (v.view.payload.downRecord i)
              haccepted state memory hchoice
            omega
      | cutoffChosen _ _ _ _ _ _ _ _ _ _ => trivial
      | clockFailure _ _ => trivial
      | initializerFailure _ _ _ _ => trivial
      | localFailure _ _ _ => trivial
  | collection _ _ _ _ _ => trivial
  | invalidCollectionCutoff => trivial
  | dagger => trivial

/-- An earlier actually selected LIVE DOWN test word cannot equal the raw
word of a current wrong uniquely accepted cut. Equality would force whole
payload equality by the selected-successor result, then make the current raw
word exactly the word excluded above. -/
theorem generated_live_earlier_selected_test_raw_excluded
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (x : ReferenceGeneratedDownBatchCalendar.LaunchSource rate rewards C_star C_h s hs)
    (n : Fin (p.T - s)) (i : Fin (p.m - 1)) :
    let R := ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt
      rate rewards C_star C_h s hs x
    match (R n).output.preparation.coordinator with
    | .live _ _ _ (.continuingChosen _ _ _ _) =>
        ∀ v : ReferenceActivePhysicalStep.Selection (R n).input,
          (R n).output.preparation.coordinator.selection = some v →
        ∀ cut : ReferenceDownReception.ReferenceDownCutOutput p rate,
          ((R n).output.followers i).down = some cut →
          ReferenceDownReception.wrongUniqueAccepted cut →
        ∀ k : Fin (p.T - s), k.val < n.val →
          ∀ old : ReferenceActivePhysicalStep.Selection (R k).input,
            (R k).output.preparation.coordinator.selection = some old →
          ∀ oldCut : ReferenceDownReception.ReferenceDownCutOutput p rate,
            ((R k).output.followers i).down = some oldCut →
            oldCut.expectedWord ≠ cut.raw
    | _ => True := by
  classical
  dsimp only
  let R := ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt
    rate rewards C_star C_h s hs x
  cases hcoordinator : (R n).output.preparation.coordinator with
  | first _ => trivial
  | live endpoint endpointOwned endpointBase outcome =>
      cases outcome with
      | continuingChosen _ _ _ _ =>
          intro v hv cut hcut hwrong k hkn old hold oldCut holdCut hsent
          cases hraw : cut.raw with
          | none => exact False.elim (hwrong.2.1 hraw)
          | some word =>
              have hexpected : oldCut.expectedWord = some word := by
                calc
                  oldCut.expectedWord = cut.raw := hsent
                  _ = some word := hraw
              obtain ⟨oldSelected, holdSelected, _hbranch, hword, _hparse, _hencode⟩ :=
                ReferenceGeneratedInheritedDownCandidateOrigin.actual_expectedDownWord_origin
                  (R k) i oldCut word holdCut hexpected
              have hselectedEq : oldSelected = old :=
                Option.some.inj (holdSelected.symm.trans hold)
              subst oldSelected
              have hnow : (R n).output.preparation.coordinator.selection = some v := by
                rw [hcoordinator]
                exact hv
              have hpayload :=
                ReferenceGeneratedSelectedSuccessorStaleCut.generated_earlier_sent_wrong_cut_same_selected_payload
                  rewards C_star C_h s hs x i n cut hcut hwrong k hkn old v hold hnow oldCut
                  holdCut hsent
              have hwordCurrent : word =
                  CoordinatorLocalArmChoice.storedDownFlatWord v.view.payload i :=
                hword.trans (congrArg (fun payload =>
                  CoordinatorLocalArmChoice.storedDownFlatWord payload i) hpayload)
              have hrawCurrent :
                  cut.raw = some (CoordinatorLocalArmChoice.storedDownFlatWord v.view.payload i) :=
                (hsent.symm.trans hexpected).trans
                  (congrArg (fun w : AffineChannelLaw.Word (AffineBatchDecoder.width p) => some w)
                    hwordCurrent)
              have hcurrent := generated_live_current_payload_raw_down_excluded
                rate rewards C_star C_h s hs x n i
              dsimp only at hcurrent
              rw [hcoordinator] at hcurrent
              exact (hcurrent v hv cut hcut hwrong) hrawCurrent
      | cutoffChosen _ _ _ _ _ _ _ _ _ _ => trivial
      | clockFailure _ _ => trivial
      | initializerFailure _ _ _ _ => trivial
      | localFailure _ _ _ => trivial
  | collection _ _ _ _ _ => trivial
  | invalidCollectionCutoff => trivial
  | dagger => trivial

end Bandits.Support.ReferenceGeneratedLiveStaleDownExclusion

end
