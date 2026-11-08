/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstReplacementCollectionStoppedPureUpQuota

import Lean.Elab.Tactic.Omega

/-!
# Original-source first-replacement DOWN receiver readiness

This module follows the physical first-replacement cutoff and each actual
ordinary continuation record. It retains the receiver's real choice, checked
logging, decoder input and diagnostic, then replays the original DOWN bank from
the corrected launch along the same physical calendar.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions
open ReferenceActivePhysicalStep
open ReferenceActivePhysicalHorizon
open ReferencePrelaunchFollower
open ActiveFollowerLifecycle
open ActiveFollowerDownAcceptance
open ReferenceFollowerDecoderChronology
open ReferenceFollowerDownDecoderReplay
open ReferenceFollowerDownIntervalWindow

namespace Bandits.Support.ReferenceFirstReplacementCollectionOldDownReceiverReadiness

variable {p : ConstructorDimensions.Parameters} {rate : ReferenceActivePhysicalStep.RateInput p}

/-- A selected DOWN call uses the actual prepared choice and own observation.
Logging contributes no DATA record on this slot, regardless of feedback. -/
private theorem selected_down_receiver_input
    (r : ReferenceCompletePhysicalHistory.RoundRecord p rate)
    (i : Fin (p.m - 1))
    (state logged : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hChoice : (ReferenceFollowerFixedReply.actualChoice r i).configuration =
      .ordinary state memory)
    (hLogging : ActiveFollowerLogging.checkedLogging i r.input.row
      (r.input.state.activations i) r.input.time
      ((r.output.preparation.followers.followers i).arm,
        r.output.preparation.feedback.observations
          (PublicDiscreteDraws.followerPlayer p.two_le_m i)) state = .ok logged)
    (hStatus : state.status = .unoccupied)
    (hSelected : ActiveFollowerDownAcceptance.downSelected p i r.input.row r.input.time) :
    logged = state ∧
      let input := ActiveFollowerDownAcceptance.currentRoundInput p i r.input.row r.input.time
        (r.output.preparation.feedback.observations
          (PublicDiscreteDraws.followerPlayer p.two_le_m i)) rate logged
      ReferenceFollowerDownDecoderReplay.actualDownCall i r = some (r.input.time, input) ∧
      input.selected = true ∧ input.receiverEnabled = true ∧
      input.sample = (r.input.row.2 r.input.time).2 (0, i) ∧
      input.roundedReward =
        (r.output.preparation.feedback.observations
          (PublicDiscreteDraws.followerPlayer p.two_le_m i)).val.val := by
  classical
  let own := ((r.output.preparation.followers.followers i).arm,
    r.output.preparation.feedback.observations
      (PublicDiscreteDraws.followerPlayer p.two_le_m i))
  have hNoLog : ¬ SparseCalendarReplay.loggingTestsPass
      (ReferencePrelaunchFollower.loggingRound i r.input.row
        (r.input.state.activations i) r.input.time own) := by
    intro hPass
    have hData := (ActiveFollowerLogging.loggingTestsPass_iff_source_mask
      i r.input.row (r.input.state.activations i) r.input.time own).mp hPass |>.2.1
    rw [hSelected.1] at hData
    cases hData
  have hNil := ActiveFollowerLogging.logAt_eq_nil_of_not_tests i r.input.row
    (r.input.state.activations i) r.input.time own hNoLog
  have hLogged : logged = state := by
    have hUpdate := ((ActiveFollowerLogging.checkedLogging_success_iff i r.input.row
      (r.input.state.activations i) r.input.time own state logged).mp hLogging).2.1
    rw [hUpdate]
    unfold ActiveFollowerLogging.loggingUpdate
    split <;> simp only [hNil, List.append_nil]
  have hCall := ReferenceFollowerDownDecoderReplay.actualDownCall_ordinary
    r i state memory hChoice
  rcases r.output.preparation.follower_alignment i with ⟨hRow, _, hTime, _⟩
  refine ⟨hLogged, ?_⟩
  rw [hLogged]
  refine ⟨?_, decide_eq_true_eq.mpr hSelected, ?_, rfl, rfl⟩
  · simpa only [ReferenceFollowerDownDecoderReplay.preparedChoiceTime,
      ReferenceFollowerDownDecoderReplay.preparedChoiceRow,
      ReferenceFollowerDownDecoderReplay.preparedOwnObservation, hRow, hTime] using hCall
  · simp only [ActiveFollowerDownAcceptance.currentRoundInput, hStatus, decide_true]

/-- The original first-replacement DOWN receiver calls, including zero-feedback
selected calls, and the whole decoder bank replay at every actual endpoint. -/
private theorem first_replacement_old_down_receiver_components
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
    let _s := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
    let _J := ActualInitializationPhysicalStep.selectedRowIndex p source
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
    let v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
    let tail := ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v
    let c := v + 1 + tail.length
    match R[v]? with
    | none => True
    | some birth =>
      match birth.output.preparation.coordinator with
      | .collection _ _ _ _ (.laterChosen _ _ _ _ _ _ _ _ _ installed _) =>
        let payload := installed.registers.payload
        match R[c]? with
        | none => True
        | some cut =>
          match cut.output.preparation.coordinator with
          | .live _ _ _ (.cutoffChosen _ _ _ _ _ _ _ _ _ _) =>
            let _u := cut.input.time.val + 1
            let W := (R.drop (c + 1)).takeWhile
              (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
            let K := cut :: W
            let _Z := fun j => ReferenceCollectionSegmentExtraction.endpointState
              cut.input.state (K.take j)
            let M := fun i => payload.downRecord i
            (∀ i : Fin (p.m - 1),
              ∃ state memory logged post diag,
                (ReferenceFollowerFixedReply.actualChoice cut i).configuration =
                  .ordinary state memory ∧
                state.status = .unoccupied ∧
                ActiveFollowerLifecycle.localStateDomainValid state ∧
                (ReferencePrelaunchFollower.acceptedStart state < (M i).val.sigma ∨
                  state.lastDown = some (M i)) ∧
                ActiveFollowerLogging.checkedLogging i cut.input.row
                  (cut.input.state.activations i) cut.input.time
                  ((cut.output.preparation.followers.followers i).arm,
                    cut.output.preparation.feedback.observations
                      (PublicDiscreteDraws.followerPlayer p.two_le_m i)) state = .ok logged ∧
                logged.buffer = state.buffer ++ ReferencePrelaunchFollower.logAt i cut.input.row
                  (cut.input.state.activations i) cut.input.time
                  ((cut.output.preparation.followers.followers i).arm,
                    cut.output.preparation.feedback.observations
                      (PublicDiscreteDraws.followerPlayer p.two_le_m i)) ∧
                logged.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound) ∧
                logged.downBatch = state.downBatch ∧
                logged.initializationFailure = state.initializationFailure ∧
                (cut.output.followers i).downInput = some logged ∧
                (cut.output.followers i).down = some diag ∧
                diag = ReferenceDownReception.referenceDownCut p
                  cut.output.preparation.coordinator.downView i cut.input.row cut.input.time
                  (cut.output.preparation.feedback.observations
                    (PublicDiscreteDraws.followerPlayer p.two_le_m i)) rate logged ∧
                cut.output.followers i = ⟨.ordinary post memory, none, some logged, some diag⟩ ∧
                post.initializationFailure = state.initializationFailure ∧
                post.status = .unoccupied ∧
                ActiveFollowerLifecycle.localStateDomainValid post ∧
                (ActiveFollowerDownAcceptance.downSelected p i cut.input.row cut.input.time →
                  logged = state ∧
                  let input := ActiveFollowerDownAcceptance.currentRoundInput p i cut.input.row
                    cut.input.time
                    (cut.output.preparation.feedback.observations
                      (PublicDiscreteDraws.followerPlayer p.two_le_m i)) rate logged
                  ReferenceFollowerDownDecoderReplay.actualDownCall i cut =
                    some (cut.input.time, input) ∧
                  input.selected = true ∧ input.receiverEnabled = true ∧
                  input.sample = (cut.input.row.2 cut.input.time).2 (0, i) ∧
                  input.roundedReward =
                    (cut.output.preparation.feedback.observations
                      (PublicDiscreteDraws.followerPlayer p.two_le_m i)).val.val)) ∧
            (∀ (a : Fin W.length) (i : Fin (p.m - 1)),
              ∃ state memory logged post diag,
                let r := W.get a
                (ReferenceFollowerFixedReply.actualChoice r i).configuration =
                  .ordinary state memory ∧
                state.status = .unoccupied ∧
                ActiveFollowerLifecycle.localStateDomainValid state ∧
                (ReferencePrelaunchFollower.acceptedStart state < (M i).val.sigma ∨
                  state.lastDown = some (M i)) ∧
                ActiveFollowerLogging.checkedLogging i r.input.row
                  (r.input.state.activations i) r.input.time
                  ((r.output.preparation.followers.followers i).arm,
                    r.output.preparation.feedback.observations
                      (PublicDiscreteDraws.followerPlayer p.two_le_m i)) state = .ok logged ∧
                logged.buffer = state.buffer ++ ReferencePrelaunchFollower.logAt i r.input.row
                  (r.input.state.activations i) r.input.time
                  ((r.output.preparation.followers.followers i).arm,
                    r.output.preparation.feedback.observations
                      (PublicDiscreteDraws.followerPlayer p.two_le_m i)) ∧
                logged.buffer.Pairwise (fun x y => x.calendarRound < y.calendarRound) ∧
                logged.downBatch = state.downBatch ∧
                logged.initializationFailure = state.initializationFailure ∧
                (r.output.followers i).downInput = some logged ∧
                (r.output.followers i).down = some diag ∧
                diag = ReferenceDownReception.referenceDownCut p
                  r.output.preparation.coordinator.downView i r.input.row r.input.time
                  (r.output.preparation.feedback.observations
                    (PublicDiscreteDraws.followerPlayer p.two_le_m i)) rate logged ∧
                r.output.followers i = ⟨.ordinary post memory, none, some logged, some diag⟩ ∧
                post.initializationFailure = state.initializationFailure ∧
                post.status = .unoccupied ∧
                ActiveFollowerLifecycle.localStateDomainValid post ∧
                (ActiveFollowerDownAcceptance.downSelected p i r.input.row r.input.time →
                  logged = state ∧
                  let input := ActiveFollowerDownAcceptance.currentRoundInput p i r.input.row
                    r.input.time
                    (r.output.preparation.feedback.observations
                      (PublicDiscreteDraws.followerPlayer p.two_le_m i)) rate logged
                  ReferenceFollowerDownDecoderReplay.actualDownCall i r =
                    some (r.input.time, input) ∧
                  input.selected = true ∧ input.receiverEnabled = true ∧
                  input.sample = (r.input.row.2 r.input.time).2 (0, i) ∧
                  input.roundedReward =
                    (r.output.preparation.feedback.observations
                      (PublicDiscreteDraws.followerPlayer p.two_le_m i)).val.val))
          | _ => True
      | _ => True := by
  classical
  have hRoot :=
    ReferenceFirstReplacementCollectionPureUpAcceptanceRoot.complete_first_replacement_collection_pure_up_acceptance
      rate source rewards C_star C_h
  have hPrefix :=
    ReferenceFirstReplacementCollectionPrefix.complete_first_replacement_collection_follower_prefix
      rate source rewards C_star C_h
  have hCutoff :=
    ReferenceFirstReplacementCutoffDownRecovery.complete_first_replacement_cutoff_down_recovery_and_finish
      rate source rewards C_star C_h
  simp only [] at hRoot hPrefix hCutoff ⊢
  set R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
  set s := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
  set J := ActualInitializationPhysicalStep.selectedRowIndex p source
  set w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
  set v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
  set tail := ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v
  set c := v + 1 + tail.length
  cases hb : R[v]? with
  | none => trivial
  | some birth =>
    simp only [hb] at hRoot hPrefix hCutoff ⊢
    cases hbirth : birth.output.preparation.coordinator with
    | first _ => trivial
    | live _ _ _ _ => trivial
    | dagger => trivial
    | invalidCollectionCutoff => trivial
    | collection _ _ _ _ outcome =>
      simp only [hbirth] at hRoot hPrefix hCutoff ⊢
      cases outcome <;> try trivial
      rename_i core consistent birthStarted hstart instruction hinstruction output hconsistent
        clockData installed selectedBirth
      dsimp only [ReferenceActivePhysicalStep.collectionInput] at hRoot hPrefix hCutoff ⊢
      let payload : ReferenceActivePhysicalStep.Payload rate := installed.registers.payload
      cases hc : R[c]? with
      | none => trivial
      | some cut =>
        simp only [hc] at hRoot hPrefix hCutoff ⊢
        cases hcut : cut.output.preparation.coordinator with
        | first _ => trivial
        | collection _ _ _ _ _ => trivial
        | dagger => trivial
        | invalidCollectionCutoff => trivial
        | live registers owned base outcome =>
          simp only [hcut] at hRoot hPrefix hCutoff ⊢
          cases outcome <;> try trivial
          rename_i dispatched hs ledger hi hledger hdata hclock hpending hnone selectedCut
          dsimp only at hRoot hPrefix hCutoff ⊢
          let u := cut.input.time.val + 1
          let W := (R.drop (c + 1)).takeWhile
            (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
          let K := cut :: W
          let Z := fun j => ReferenceCollectionSegmentExtraction.endpointState
            cut.input.state (K.take j)
          let M := fun i => payload.downRecord i
          rcases hRoot with ⟨_, _, hRoot⟩
          rcases hRoot with ⟨hcalendar, hZspec, hrootFollowers, hrootBoundary⟩
          rcases hZspec with ⟨hZ0, hZE, hZrecords⟩
          rcases hPrefix with
            ⟨hCollectionWindow, hE0, hSourceEndpoints, huLower, huUpper,
                hFirstCutoff, hPrefixFollowers⟩
          rcases hCutoff with
            ⟨_, _, _, _, _, _, _, _, _, _, _, _, hSelected⟩
          rcases hSelected with ⟨selected, hSelection, hPayload, hPending, hCutoffView,
            hCutoffFollowers⟩
          refine ⟨?_, ?_⟩
          · intro i
            obtain ⟨old, memory, hInput, hOldDomain, _, hOldNone, hOldUnoccupied,
              hOldOccupied, hInterrupt, hStart, hPrepared, hChoiceDomain, hChoiceBound,
              hChoiceBuffer, hChoiceBufferStamp, hOffer, hDownSigma, hDownQueue,
              logged, post, hLog, hLogBuffer, hLogDomain, hLogLast, hLogS, hLogDelta,
              hLogBacklog, hLogFailure, hLogStatus, hLogPairwise, hLogStamp,
              hSelectedLog, hConsume, hPostStatus, hPostDomain, hPostBound, hPostDelta,
              hPostFailure, hCases, hRecordResult, hDownInput, hDown, hRelease, hFinish,
              hReleaseFinish, hFollowerOutput⟩ := hCutoffFollowers i
            let state : ReferencePrelaunchFollower.State p rate.eta :=
              { old with status := .unoccupied }
            have hChoice : (ReferenceFollowerFixedReply.actualChoice cut i).configuration =
                .ordinary state memory := by
              simpa only [ReferenceFollowerFixedReply.actualChoice] using hPrepared
            have hStatus : state.status = .unoccupied := by simp [state]
            have hDomain : ActiveFollowerLifecycle.localStateDomainValid state := hChoiceDomain
            have hClass : ReferencePrelaunchFollower.acceptedStart state < (M i).val.sigma ∨
                state.lastDown = some (M i) := by
              by_cases hOldUnoccupied' : old.status = .unoccupied
              · left
                simpa [state, ReferencePrelaunchFollower.acceptedStart] using
                  hOldUnoccupied hOldUnoccupied'
              · right
                rcases hOldOccupied hOldUnoccupied' with ⟨hLast, _⟩
                simpa [state] using hLast
            have hFrame := ActiveFollowerLogging.checkedLogging_success_frame
              i cut.input.row (cut.input.state.activations i) cut.input.time
              ((cut.output.preparation.followers.followers i).arm,
                cut.output.preparation.feedback.observations
                  (PublicDiscreteDraws.followerPlayer p.two_le_m i)) state logged hLog
            rcases hFrame with ⟨_, _, _, _, _, hBatch, hInitFailure⟩
            refine ⟨state, memory, logged, post,
              ReferenceDownReception.referenceDownCut p
                cut.output.preparation.coordinator.downView i cut.input.row cut.input.time
                (cut.output.preparation.feedback.observations
                  (PublicDiscreteDraws.followerPlayer p.two_le_m i)) rate logged, ?_⟩
            constructor
            · exact hChoice
            constructor
            · exact hStatus
            constructor
            · exact hDomain
            constructor
            · exact hClass
            constructor
            · exact hLog
            constructor
            · exact hLogBuffer
            constructor
            · exact hLogPairwise
            constructor
            · exact hBatch
            constructor
            · exact hInitFailure
            constructor
            · simp only [hFollowerOutput]
            constructor
            · simpa only [hcut] using
                congrArg (fun observation => observation.down) hFollowerOutput
            constructor
            · simp only [hcut]
            constructor
            · simp only [hFollowerOutput, hcut]
            constructor
            · simpa [state] using hPostFailure
            constructor
            · exact hPostStatus
            constructor
            · exact hPostDomain
            · intro hDownSelected
              exact selected_down_receiver_input cut i state logged memory
                hChoice hLog hStatus hDownSelected
          · intro a i
            obtain ⟨_, _, hOrigin⟩ := hPrefixFollowers i
            rcases hOrigin with
              ⟨old, initial, memory, hInput, hInitialChoice, hCutFailure, hEInitial,
                hInitialStatus, hInitialDomain, hInitialBound, hInitialDelta, hInitialNone,
                hInitialClass, hInitialFailure, hInitialPairwise, hInitialStamp,
                hStateEndpoints, hRoundRecords, hFinalEndpoint⟩
            obtain ⟨hRecordGet, state, logged, post, hStateInput, hStateStatus,
              hStateDomain, _, _, hStateFailure, _, hStateClass, hStatePairwise,
              hStateStamps, hStartRound, hPrepared, _, hLog, hLogBuffer, hLogLast,
              hLogS, hLogDelta, hLogBacklog, hLogStatus, hLogBatch, hLogFailure,
              hLogDomain, hLogOperation, hLogPairwise, hLogBufferStamp, hRecordResult,
              hDownInputRecord, hDownRecord, hRelease, hFinish, hReleaseFinish,
              hOutput, hConsume, hPostStatus, hPostDomain, _, _, hPostFailure, _, hPostPairwise,
              _, hExpected, hSelectedRaw, hCases, hEndpointPost⟩ :=
                hRoundRecords a.val a.isLt
            let r := W.get a
            have hChoice : (ReferenceFollowerFixedReply.actualChoice r i).configuration =
                .ordinary state memory := by
              simpa only [r, ReferenceFollowerFixedReply.actualChoice] using hPrepared
            have hFrame := ActiveFollowerLogging.checkedLogging_success_frame
              i r.input.row (r.input.state.activations i) r.input.time
              ((r.output.preparation.followers.followers i).arm,
                r.output.preparation.feedback.observations
                  (PublicDiscreteDraws.followerPlayer p.two_le_m i)) state logged hLog
            rcases hFrame with ⟨_, _, _, _, _, hBatch, hInitFailure⟩
            refine ⟨state, memory, logged, post,
              ReferenceDownReception.referenceDownCut p
                r.output.preparation.coordinator.downView i r.input.row r.input.time
                (r.output.preparation.feedback.observations
                  (PublicDiscreteDraws.followerPlayer p.two_le_m i)) rate logged, ?_⟩
            constructor
            · simpa only [hRecordGet, hStateInput] using hChoice
            constructor
            · exact hStateStatus
            constructor
            · exact hStateDomain
            constructor
            · exact hStateClass
            constructor
            · exact hLog
            constructor
            · exact hLogBuffer
            constructor
            · exact hLogPairwise
            constructor
            · exact hBatch
            constructor
            · exact hInitFailure
            constructor
            · simpa only [r] using
                congrArg (fun observation => observation.downInput) hOutput
            constructor
            · simpa only [r] using
                congrArg (fun observation => observation.down) hOutput
            constructor
            · rfl
            constructor
            · simpa only [r] using hOutput
            constructor
            · exact hPostFailure
            constructor
            · exact hPostStatus
            constructor
            · exact hPostDomain
            · intro hDownSelected
              exact selected_down_receiver_input r i state logged memory
                hChoice hLog hStateStatus hDownSelected


private theorem first_replacement_old_down_receiver_source_replay
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
    let s := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
    let J := ActualInitializationPhysicalStep.selectedRowIndex p source
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
    let v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
    let tail := ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v
    let c := v + 1 + tail.length
    match R[v]? with
    | none => True
    | some birth =>
      match birth.output.preparation.coordinator with
      | .collection _ _ _ _ (.laterChosen _ _ _ _ _ _ _ _ _ installed _) =>
        let payload := installed.registers.payload
        match R[c]? with
        | none => True
        | some cut =>
          match cut.output.preparation.coordinator with
          | .live _ _ _ (.cutoffChosen _ _ _ _ _ _ _ _ _ _) =>
            let _u := cut.input.time.val + 1
            let W := (R.drop (c + 1)).takeWhile
              (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
            let K := cut :: W
            let Z := fun j => ReferenceCollectionSegmentExtraction.endpointState
              cut.input.state (K.take j)
            let _M := fun i => payload.downRecord i
            ∃ initial : ReferenceActivePhysicalStep.State p rate,
              ∃ active : ReferenceActivePhysicalHorizon.allActiveAtStart initial s,
                ReferenceCorrectedInitializationLaunch.correctedLaunch
                  rate source rewards C_star C_h = some initial ∧
                ReferenceFollowerDecoderChronology.downBatchSeed initial s ∧
                ∀ i : Fin (p.m - 1), ∀ j : ℕ, j ≤ K.length →
                  let calls := ReferenceFollowerDownDecoderReplay.actualDownCalls i (K.take j)
                  let positives := ReferenceFollowerDownDecoderReplay.actualDownPositives i (K.take j)
                  ∃ span : s + (c + j) ≤ p.T,
                    ∃ state memory base baseMemory,
                    (Z j).followers i = .ordinary state memory ∧
                    (ReferenceActivePhysicalHorizon.run initial source.1.2 J rewards s
                      (c + j) span active).records.drop c = K.take j ∧
                    (ReferenceActivePhysicalHorizon.run initial source.1.2 J rewards s
                      (c + j) span active).finalState = Z j ∧
                    ReferenceFollowerDecoderChronology.downBatchEndpoint state (s + c + j) ∧
                    (ReferenceActivePhysicalHorizon.run initial source.1.2 J rewards s
                      c (by omega) active).finalState.followers i = .ordinary base baseMemory ∧
                    ReferenceFollowerDecoderChronology.downBatchEndpoint base (s + c) ∧
                    (∃ choice choiceMemory,
                      (ReferenceFollowerFixedReply.actualChoice cut i).configuration =
                        .ordinary choice choiceMemory ∧
                      choice.downBatch = base.downBatch) ∧
                    state.downBatch = ReferenceFollowerDownDecoderReplay.foldDownCalls calls
                      base.downBatch ∧
                    AffineBatchDecoder.collected state.downBatch =
                      AffineBatchDecoder.collected base.downBatch ++
                        positives ∧
                    base.downBatch.pending.length < AffineBatchDecoder.quota p ∧
                    (∀ entry ∈ base.downBatch.pending, entry.time.val < s + c) ∧
                    calls.Pairwise
                      (fun first second => first.1.val < second.1.val) ∧
                    (calls.map Prod.fst).map
                      Fin.val = ReferenceActivePhysicalHorizon.calendar (s + c) j ∧
                    positives.Pairwise
                      (fun earlier later => earlier.time.val < later.time.val) ∧
                    (∀ entry ∈ positives,
                      s + c ≤ entry.time.val ∧ entry.time.val < s + c + j)
          | _ => True
      | _ => True := by
  classical
  have hRoot :=
    ReferenceFirstReplacementCollectionPureUpAcceptanceRoot.complete_first_replacement_collection_pure_up_acceptance
      rate source rewards C_star C_h
  have hPrefix :=
    ReferenceFirstReplacementCollectionPrefix.complete_first_replacement_collection_follower_prefix
      rate source rewards C_star C_h
  have hCutoff :=
    ReferenceFirstReplacementCutoffDownRecovery.complete_first_replacement_cutoff_down_recovery_and_finish
      rate source rewards C_star C_h
  simp only [] at hRoot hPrefix hCutoff ⊢
  set R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
  set s := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
  set J := ActualInitializationPhysicalStep.selectedRowIndex p source
  set w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
  set v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
  set tail := ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v
  set c := v + 1 + tail.length
  cases hb : R[v]? with
  | none => trivial
  | some birth =>
    simp only [hb] at hRoot hPrefix hCutoff ⊢
    cases hbirth : birth.output.preparation.coordinator with
    | first _ => trivial
    | live _ _ _ _ => trivial
    | dagger => trivial
    | invalidCollectionCutoff => trivial
    | collection _ _ _ _ outcome =>
      simp only [hbirth] at hRoot hPrefix hCutoff ⊢
      cases outcome <;> try trivial
      rename_i core consistent birthStarted hstart instruction hinstruction output hconsistent
        clockData installed selectedBirth
      dsimp only [ReferenceActivePhysicalStep.collectionInput] at hRoot hPrefix hCutoff ⊢
      let payload : ReferenceActivePhysicalStep.Payload rate := installed.registers.payload
      cases hc : R[c]? with
      | none => trivial
      | some cut =>
        simp only [hc] at hRoot hPrefix hCutoff ⊢
        cases hcut : cut.output.preparation.coordinator with
        | first _ => trivial
        | collection _ _ _ _ _ => trivial
        | dagger => trivial
        | invalidCollectionCutoff => trivial
        | live registers owned base outcome =>
          simp only [hcut] at hRoot hPrefix hCutoff ⊢
          cases outcome <;> try trivial
          rename_i dispatched hs ledger hi hledger hdata hclock hpending hnone selectedCut
          dsimp only at hRoot hPrefix hCutoff ⊢
          let u := cut.input.time.val + 1
          let W := (R.drop (c + 1)).takeWhile
            (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
          let K := cut :: W
          let Z := fun j => ReferenceCollectionSegmentExtraction.endpointState
            cut.input.state (K.take j)
          let M := fun i => payload.downRecord i
          rcases hRoot with ⟨_, _, hRoot⟩
          rcases hRoot with ⟨hcalendar, hZspec, hrootFollowers, hrootBoundary⟩
          rcases hZspec with ⟨hZ0, hZE, hZrecords⟩
          rcases hPrefix with
            ⟨hCollectionWindow, hE0, hSourceEndpoints, huLower, huUpper,
                hFirstCutoff, hPrefixFollowers⟩
          rcases hCutoff with
            ⟨_, _, _, _, _, _, _, _, _, _, _, _, hSelected⟩
          rcases hSelected with ⟨selected, hSelection, hPayload, hPending, hCutoffView,
            hCutoffFollowers⟩
          obtain ⟨hci, hce⟩ := List.getElem?_eq_some_iff.mp hc
          have hKprefix : K <+: R.drop c := by
            rw [List.drop_eq_getElem_cons hci, hce]
            refine ⟨(R.drop (c + 1)).dropWhile
              (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input), ?_⟩
            simp only [K, W, List.cons_append, List.takeWhile_append_dropWhile]
          obtain ⟨crossing, _, _⟩ := ReferenceLaterLiveNumericalReadout.source_record_prefix
            rate rewards C_star C_h source ⟨c, hci⟩
          obtain ⟨initial, active, hLaunch, _, _, _, _, _hFull, hRuns⟩ :=
            ReferenceFirstReplacementCollectionPureUpWindowCut.source_interval_runs
              rate source rewards C_star C_h c cut hc K hKprefix
          have hElapsed : ReferenceInitializationRun.elapsed p
              (ReferenceInitializationRun.output
                (ActualReferenceInitializationBlock.referenceInput
                  source rewards C_star C_h rate)).completed = s := by
            simp [ReferenceCompletePhysicalHistory.physicalStart,
              ReferenceCompletePhysicalHistory.generatedBoundary,
              ReferenceCompletePhysicalHistory.generatedInput, s]
          obtain ⟨launchAgain, hLaunchAgain, hDownSeed⟩ :=
            ReferenceCorrectedInitializationLaunch.correctedLaunch_downBatchSeed
              rate source rewards C_star C_h (by exact crossing)
          have hLaunchEq : launchAgain = initial :=
            Option.some.inj (hLaunchAgain.symm.trans hLaunch)
          subst launchAgain
          have hDownSeedAtS : ReferenceFollowerDecoderChronology.downBatchSeed initial s := by
            simpa [hElapsed] using hDownSeed
          refine ⟨initial, active, hLaunch, hDownSeedAtS, ?_⟩
          ·
              intro i j hj
              obtain ⟨spanB, hRecordsB, hFinalB⟩ := hRuns j hj
              obtain ⟨spanA, hRecordsA, hFinalA⟩ := hRuns 0 (by omega)
              obtain ⟨_, _, hOrigin⟩ := hPrefixFollowers i
              rcases hOrigin with
                ⟨old, initialState, memory, hInput, hInitialChoice, hCutFailure, hEInitial,
                  hInitialStatus, hInitialDomain, hInitialBound, hInitialDelta, hInitialNone,
                  hInitialClass, hInitialFailure, hInitialPairwise, hInitialStamp,
                  hStateEndpoints, hRoundRecords, hFinalEndpoint⟩
              have hZordinary : ∃ state memory, (Z j).followers i = .ordinary state memory := by
                by_cases hj0 : j = 0
                · subst j
                  exact ⟨old, memory,
                    (congrArg (fun st : ReferenceActivePhysicalStep.State p rate => st.followers i)
                      hZ0).trans hInput⟩
                · have hjPos : 0 < j := Nat.pos_of_ne_zero hj0
                  let q := j - 1
                  have hqBound : q ≤ W.length := by
                    change j ≤ (cut :: W).length at hj
                    simp only [List.length_cons] at hj
                    dsimp [q]
                    omega
                  obtain ⟨state, hStateAtEndpoint, _⟩ := hStateEndpoints q hqBound
                  have hIndex : q + 1 = j := by dsimp [q]; omega
                  have hZEq : Z j = ReferenceCollectionSegmentExtraction.endpointState
                      cut.output.next (W.take q) := by
                    calc
                      Z j = Z (q + 1) := congrArg Z hIndex.symm
                      _ = ReferenceCollectionSegmentExtraction.endpointState
                          cut.output.next (W.take q) := hZE q hqBound
                  rw [hZEq]
                  exact ⟨state, memory, hStateAtEndpoint⟩
              rcases hZordinary with ⟨state, memoryB, hZState⟩
              have hOrdinaryB :
                  (ReferenceActivePhysicalHorizon.run initial source.1.2 J rewards s
                    (c + j) spanB active).finalState.followers i = .ordinary state memoryB := by
                rw [hFinalB]
                exact hZState
              have hOrdinaryA :
                  (ReferenceActivePhysicalHorizon.run initial source.1.2 J rewards s
                    c spanA active).finalState.followers i = .ordinary old memory := by
                have hFinalA' :
                    (ReferenceActivePhysicalHorizon.run initial source.1.2 J rewards s
                      c spanA active).finalState = Z 0 := by
                  simpa only [Nat.add_zero] using hFinalA
                calc
                  _ = (Z 0).followers i := congrArg
                    (fun st : ReferenceActivePhysicalStep.State p rate => st.followers i) hFinalA'
                  _ = .ordinary old memory :=
                    (congrArg (fun st : ReferenceActivePhysicalStep.State p rate => st.followers i)
                      hZ0).trans hInput
              have hReplaySpecB := ReferenceFollowerDecoderChronology.run_downBatch_spec
                initial source.1.2 J rewards s (c + j) spanB active hDownSeedAtS i state memoryB
                hOrdinaryB
              have hReplaySpecA := ReferenceFollowerDecoderChronology.run_downBatch_spec
                initial source.1.2 J rewards s c spanA active hDownSeedAtS i old memory
                hOrdinaryA
              obtain ⟨baseReplay, baseMemoryReplay, hOrdinaryAReplay, hReplayFacts⟩ :=
                ReferenceFollowerDownIntervalWindow.run_interval_downBatch_replay
                  p rate initial source.1.2 J rewards s c (c + j) (by omega) spanB active
                  hDownSeedAtS i state memoryB hOrdinaryB
              have hBaseConfiguration :
                  DeclaredFollowerLocalRound.LocalConfiguration.ordinary baseReplay baseMemoryReplay =
                    DeclaredFollowerLocalRound.LocalConfiguration.ordinary old memory := by
                calc
                  _ = (ReferenceActivePhysicalHorizon.run initial source.1.2 J rewards s
                    c spanA active).finalState.followers i := hOrdinaryAReplay.symm
                  _ = .ordinary old memory := hOrdinaryA
              have hBaseState : baseReplay = old :=
                (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
                  hBaseConfiguration).1
              have hBaseMemory : baseMemoryReplay = memory :=
                (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
                  hBaseConfiguration).2
              subst baseReplay
              subst baseMemoryReplay
              rcases hReplayFacts with
                ⟨hRunPrefix, hCallPairwise, hCallCalendar, hBank, hCollected,
                  hPending, hPendingStamp, hPositivePairwise, hPositiveStamp⟩
              rw [hRecordsB] at hBank hCollected hCallPairwise hCallCalendar hPositivePairwise hPositiveStamp
              obtain ⟨cutOld, cutMemory, hCutInput, hCutDomain, hCutBound, hCutNone,
                hCutUnoccupied, hCutOccupied, hCutInterrupt, hCutStart, hPrepared,
                hCutChoiceDomain, hCutChoiceBound, hCutChoiceBuffer, hCutChoiceStamp,
                hCutOffer, hCutSigma, hCutQueue, loggedCut, postCut, hLogCut,
                hLogCutBuffer, hLogCutDomain, hLogCutLast, hLogCutS, hLogCutDelta,
                hLogCutBacklog, hLogCutFailure, hLogCutStatus, hLogCutPairwise,
                hLogCutStamp, hLogCutSelected, hConsumeCut, hPostCutStatus,
                hPostCutDomain, hPostCutBound, hPostCutDelta, hPostCutFailure,
                hCasesCut, hRecordCut, hDownInputCut, hDownCut, hReleaseCut,
                hFinishCut, hReleaseFinishCut, hOutputCut⟩ := hCutoffFollowers i
              have hOldConfigurations :
                  DeclaredFollowerLocalRound.LocalConfiguration.ordinary cutOld cutMemory =
                    DeclaredFollowerLocalRound.LocalConfiguration.ordinary old memory := by
                calc
                  _ = cut.input.state.followers i := hCutInput.symm
                  _ = .ordinary old memory := hInput
              have hCutOldState : cutOld = old :=
                (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
                  hOldConfigurations).1
              have hCutMemory : cutMemory = memory :=
                (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
                  hOldConfigurations).2
              subst cutOld
              subst cutMemory
              let choice : ReferencePrelaunchFollower.State p rate.eta :=
                { old with status := .unoccupied }
              have hChoiceConfiguration :
                  (ReferenceFollowerFixedReply.actualChoice cut i).configuration =
                    .ordinary choice memory := by
                simpa only [ReferenceFollowerFixedReply.actualChoice] using hPrepared
              have hCutInterruption :=
                ReferenceFollowerDecoderChronology.run_interruption_downBatch_frame
                  cut i old choice memory memory hInput hPrepared hReplaySpecA.2
              have hEndpointB :
                  ReferenceFollowerDecoderChronology.downBatchEndpoint state (s + c + j) := by
                simpa only [Nat.add_assoc] using hReplaySpecB.1
              have hCallCalendar' :
                  ((ReferenceFollowerDownDecoderReplay.actualDownCalls i (K.take j)).map Prod.fst).map
                      Fin.val = ReferenceActivePhysicalHorizon.calendar (s + c) j := by
                simpa only [Nat.add_sub_cancel_left] using hCallCalendar
              have hPositiveStamp' :
                  ∀ entry ∈ ReferenceFollowerDownDecoderReplay.actualDownPositives i (K.take j),
                    s + c ≤ entry.time.val ∧ entry.time.val < s + c + j := by
                simpa only [Nat.add_assoc] using hPositiveStamp
              refine ⟨spanB, state, memoryB, old, memory, hZState, hRecordsB, hFinalB,
                hEndpointB, hOrdinaryA, hReplaySpecA.1, ?_, hBank, hCollected,
                hPending, hPendingStamp, hCallPairwise, hCallCalendar',
                hPositivePairwise, hPositiveStamp'⟩
              · exact ⟨choice, memory, hChoiceConfiguration, hCutInterruption.1⟩

theorem complete_first_replacement_collection_old_down_receiver_readiness
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
    let s := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
    let J := ActualInitializationPhysicalStep.selectedRowIndex p source
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
    let v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
    let tail := ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v
    let c := v + 1 + tail.length
    match R[v]? with
    | none => True
    | some birth =>
      match birth.output.preparation.coordinator with
      | .collection _ _ _ _ (.laterChosen _ _ _ _ _ _ _ _ _ installed _) =>
        let payload := installed.registers.payload
        match R[c]? with
        | none => True
        | some cut =>
          match cut.output.preparation.coordinator with
          | .live _ _ _ (.cutoffChosen _ _ _ _ _ _ _ _ _ _) =>
            let _u := cut.input.time.val + 1
            let W := (R.drop (c + 1)).takeWhile
              (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
            let K := cut :: W
            let Z := fun j => ReferenceCollectionSegmentExtraction.endpointState
              cut.input.state (K.take j)
            let M := fun i => payload.downRecord i
            (∀ i : Fin (p.m - 1),
              ∃ state memory logged post diag,
                (ReferenceFollowerFixedReply.actualChoice cut i).configuration =
                  .ordinary state memory ∧
                state.status = .unoccupied ∧
                ActiveFollowerLifecycle.localStateDomainValid state ∧
                (ReferencePrelaunchFollower.acceptedStart state < (M i).val.sigma ∨
                  state.lastDown = some (M i)) ∧
                ActiveFollowerLogging.checkedLogging i cut.input.row
                  (cut.input.state.activations i) cut.input.time
                  ((cut.output.preparation.followers.followers i).arm,
                    cut.output.preparation.feedback.observations
                      (PublicDiscreteDraws.followerPlayer p.two_le_m i)) state = .ok logged ∧
                logged.buffer = state.buffer ++ ReferencePrelaunchFollower.logAt i cut.input.row
                  (cut.input.state.activations i) cut.input.time
                  ((cut.output.preparation.followers.followers i).arm,
                    cut.output.preparation.feedback.observations
                      (PublicDiscreteDraws.followerPlayer p.two_le_m i)) ∧
                logged.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound) ∧
                logged.downBatch = state.downBatch ∧
                logged.initializationFailure = state.initializationFailure ∧
                (cut.output.followers i).downInput = some logged ∧
                (cut.output.followers i).down = some diag ∧
                diag = ReferenceDownReception.referenceDownCut p
                  cut.output.preparation.coordinator.downView i cut.input.row cut.input.time
                  (cut.output.preparation.feedback.observations
                    (PublicDiscreteDraws.followerPlayer p.two_le_m i)) rate logged ∧
                cut.output.followers i = ⟨.ordinary post memory, none, some logged, some diag⟩ ∧
                post.initializationFailure = state.initializationFailure ∧
                post.status = .unoccupied ∧
                ActiveFollowerLifecycle.localStateDomainValid post ∧
                (ActiveFollowerDownAcceptance.downSelected p i cut.input.row cut.input.time →
                  logged = state ∧
                  let input := ActiveFollowerDownAcceptance.currentRoundInput p i cut.input.row
                    cut.input.time
                    (cut.output.preparation.feedback.observations
                      (PublicDiscreteDraws.followerPlayer p.two_le_m i)) rate logged
                  ReferenceFollowerDownDecoderReplay.actualDownCall i cut =
                    some (cut.input.time, input) ∧
                  input.selected = true ∧ input.receiverEnabled = true ∧
                  input.sample = (cut.input.row.2 cut.input.time).2 (0, i) ∧
                  input.roundedReward =
                    (cut.output.preparation.feedback.observations
                      (PublicDiscreteDraws.followerPlayer p.two_le_m i)).val.val)) ∧
            (∀ (a : Fin W.length) (i : Fin (p.m - 1)),
              ∃ state memory logged post diag,
                let r := W.get a
                (ReferenceFollowerFixedReply.actualChoice r i).configuration =
                  .ordinary state memory ∧
                state.status = .unoccupied ∧
                ActiveFollowerLifecycle.localStateDomainValid state ∧
                (ReferencePrelaunchFollower.acceptedStart state < (M i).val.sigma ∨
                  state.lastDown = some (M i)) ∧
                ActiveFollowerLogging.checkedLogging i r.input.row
                  (r.input.state.activations i) r.input.time
                  ((r.output.preparation.followers.followers i).arm,
                    r.output.preparation.feedback.observations
                      (PublicDiscreteDraws.followerPlayer p.two_le_m i)) state = .ok logged ∧
                logged.buffer = state.buffer ++ ReferencePrelaunchFollower.logAt i r.input.row
                  (r.input.state.activations i) r.input.time
                  ((r.output.preparation.followers.followers i).arm,
                    r.output.preparation.feedback.observations
                      (PublicDiscreteDraws.followerPlayer p.two_le_m i)) ∧
                logged.buffer.Pairwise (fun x y => x.calendarRound < y.calendarRound) ∧
                logged.downBatch = state.downBatch ∧
                logged.initializationFailure = state.initializationFailure ∧
                (r.output.followers i).downInput = some logged ∧
                (r.output.followers i).down = some diag ∧
                diag = ReferenceDownReception.referenceDownCut p
                  r.output.preparation.coordinator.downView i r.input.row r.input.time
                  (r.output.preparation.feedback.observations
                    (PublicDiscreteDraws.followerPlayer p.two_le_m i)) rate logged ∧
                r.output.followers i = ⟨.ordinary post memory, none, some logged, some diag⟩ ∧
                post.initializationFailure = state.initializationFailure ∧
                post.status = .unoccupied ∧
                ActiveFollowerLifecycle.localStateDomainValid post ∧
                (ActiveFollowerDownAcceptance.downSelected p i r.input.row r.input.time →
                  logged = state ∧
                  let input := ActiveFollowerDownAcceptance.currentRoundInput p i r.input.row
                    r.input.time
                    (r.output.preparation.feedback.observations
                      (PublicDiscreteDraws.followerPlayer p.two_le_m i)) rate logged
                  ReferenceFollowerDownDecoderReplay.actualDownCall i r =
                    some (r.input.time, input) ∧
                  input.selected = true ∧ input.receiverEnabled = true ∧
                  input.sample = (r.input.row.2 r.input.time).2 (0, i) ∧
                  input.roundedReward =
                    (r.output.preparation.feedback.observations
                      (PublicDiscreteDraws.followerPlayer p.two_le_m i)).val.val)) ∧
            ∃ initial : ReferenceActivePhysicalStep.State p rate,
              ∃ active : ReferenceActivePhysicalHorizon.allActiveAtStart initial s,
                ReferenceCorrectedInitializationLaunch.correctedLaunch
                  rate source rewards C_star C_h = some initial ∧
                ReferenceFollowerDecoderChronology.downBatchSeed initial s ∧
                ∀ i : Fin (p.m - 1), ∀ j : ℕ, j ≤ K.length →
                  let calls := ReferenceFollowerDownDecoderReplay.actualDownCalls i (K.take j)
                  let positives := ReferenceFollowerDownDecoderReplay.actualDownPositives i (K.take j)
                  ∃ span : s + (c + j) ≤ p.T,
                    ∃ state memory base baseMemory,
                    (Z j).followers i = .ordinary state memory ∧
                    (ReferenceActivePhysicalHorizon.run initial source.1.2 J rewards s
                      (c + j) span active).records.drop c = K.take j ∧
                    (ReferenceActivePhysicalHorizon.run initial source.1.2 J rewards s
                      (c + j) span active).finalState = Z j ∧
                    ReferenceFollowerDecoderChronology.downBatchEndpoint state (s + c + j) ∧
                    (ReferenceActivePhysicalHorizon.run initial source.1.2 J rewards s
                      c (by omega) active).finalState.followers i = .ordinary base baseMemory ∧
                    ReferenceFollowerDecoderChronology.downBatchEndpoint base (s + c) ∧
                    (∃ choice choiceMemory,
                      (ReferenceFollowerFixedReply.actualChoice cut i).configuration =
                        .ordinary choice choiceMemory ∧
                      choice.downBatch = base.downBatch) ∧
                    state.downBatch = ReferenceFollowerDownDecoderReplay.foldDownCalls calls
                      base.downBatch ∧
                    AffineBatchDecoder.collected state.downBatch =
                      AffineBatchDecoder.collected base.downBatch ++
                        positives ∧
                    base.downBatch.pending.length < AffineBatchDecoder.quota p ∧
                    (∀ entry ∈ base.downBatch.pending, entry.time.val < s + c) ∧
                    calls.Pairwise
                      (fun first second => first.1.val < second.1.val) ∧
                    (calls.map Prod.fst).map
                      Fin.val = ReferenceActivePhysicalHorizon.calendar (s + c) j ∧
                    positives.Pairwise
                      (fun earlier later => earlier.time.val < later.time.val) ∧
                    (∀ entry ∈ positives,
                      s + c ≤ entry.time.val ∧ entry.time.val < s + c + j)
          | _ => True
      | _ => True := by
  classical
  have hReceiver := first_replacement_old_down_receiver_components
    rate source rewards C_star C_h
  have hReplay := first_replacement_old_down_receiver_source_replay
    rate source rewards C_star C_h
  simp only [] at hReceiver hReplay ⊢
  set R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
  set s := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
  set J := ActualInitializationPhysicalStep.selectedRowIndex p source
  set w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
  set v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
  set tail := ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v
  set c := v + 1 + tail.length
  cases hb : R[v]? with
  | none => trivial
  | some birth =>
    have hbSource := hb
    dsimp only [R, w, v] at hbSource
    simp only [hbSource] at hReplay
    simp only [hb] at hReceiver ⊢
    cases hbirth : birth.output.preparation.coordinator with
    | first _ => trivial
    | live _ _ _ _ => trivial
    | dagger => trivial
    | invalidCollectionCutoff => trivial
    | collection _ _ _ _ outcome =>
      simp only [hbirth] at hReceiver hReplay ⊢
      cases outcome <;> try trivial
      rename_i core consistent birthStarted hstart instruction hinstruction output hconsistent
        clockData installed selectedBirth
      dsimp only [ReferenceActivePhysicalStep.collectionInput] at hReceiver hReplay ⊢
      let payload : ReferenceActivePhysicalStep.Payload rate := installed.registers.payload
      cases hc : R[c]? with
      | none => trivial
      | some cut =>
        have hcSource := hc
        dsimp only [R, w, v, tail, c] at hcSource
        simp only [hcSource] at hReplay
        simp only [hc] at hReceiver ⊢
        cases hcut : cut.output.preparation.coordinator with
        | first _ => trivial
        | collection _ _ _ _ _ => trivial
        | dagger => trivial
        | invalidCollectionCutoff => trivial
        | live registers owned base outcome =>
          simp only [hcut] at hReceiver hReplay ⊢
          cases outcome <;> try trivial
          rename_i dispatched hs ledger hi hledger hdata hclock hpending hnone selectedCut
          dsimp only at hReceiver hReplay ⊢
          let u := cut.input.time.val + 1
          let W := (R.drop (c + 1)).takeWhile
            (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
          let K := cut :: W
          let Z := fun j => ReferenceCollectionSegmentExtraction.endpointState
            cut.input.state (K.take j)
          let M := fun i => payload.downRecord i
          rcases hReceiver with ⟨hCutoffReceivers, hLaterReceivers⟩
          exact ⟨hCutoffReceivers, hLaterReceivers, hReplay⟩

end Bandits.Support.ReferenceFirstReplacementCollectionOldDownReceiverReadiness

end
