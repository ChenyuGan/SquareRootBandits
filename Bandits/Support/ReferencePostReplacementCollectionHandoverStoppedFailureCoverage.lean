/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferencePostReplacementCollectionHandoverDecoderCorrespondence
public import Bandits.Support.ReferencePostReplacementCollectionHandoverSourcePrefix

/-!
# Actual later-handover local service and source-date failure coverage

The birth seed retains the actual follower bank and accepted-start register.
Every selected awaiting DOWN call, including zero feedback, has original-source
awaited provenance. Both failure phases of a local awaiting service update are
covered on that same source date, with every entry of the actual completed bank
and every selected calendar date retained. A current-word acceptance produces
the checked physical installation and cannot confirm in that same round.

These one-step results use the actual physical awaiting projection. Identifying
it with `run` or `snapshotBefore` over all strict predecessors, including the
actual cutoff/overflow markers and launch-based queue domain, remains open.
No postfailure state correspondence or manuscript closure is asserted.

Sources: ZIP4 `05_binary_transport.tex:244-289`,
`06_interruptions.tex:246-299,431-490`, and
`appendix_a_local_protocol.tex:28-79`.
-/

@[expose] public section

noncomputable section

open Bandits.Support ConstructorDimensions BootstrapPrivateRoundStreams
open HandoverStoppedDecoderReplay

namespace Bandits.Support.ReferencePostReplacementCollectionHandoverStoppedFailureCoverage

variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
variable (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
variable (C_star C_h : ℝ)
variable (z : BootstrapPrivateRoundStreams.SourceInput p)

open ReferencePostReplacementCollectionHandoverDecoderCorrespondence
open ReferenceFirstLiveDownCompletionReadout
open ActiveFollowerDownAcceptance ReferenceDownReception
open scoped Classical

private theorem actual_handover_record_index
    (b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (j : Fin (actualHandoverRecords rate rewards C_star C_h z b).length) :
    ∃ hk : b.val + j.val <
        (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).length,
      (actualHandoverRecords rate rewards C_star C_h z b)[j.val] =
        (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h)[b.val + j.val]'hk := by
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let V := R[b.val] :: ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
    rate rewards C_star C_h z (b.val + 1)
  have hV : V.IsPrefix (R.drop b.val) := by
    rw [List.drop_eq_getElem_cons b.isLt]
    exact List.cons_prefix_cons.mpr ⟨rfl, List.takeWhile_prefix _⟩
  have hH : (actualHandoverRecords rate rewards C_star C_h z b).IsPrefix
      (R.drop b.val) := (List.takeWhile_prefix _).trans hV
  have hlen := hH.length_le
  simp only [List.length_drop] at hlen
  have hk : b.val + j.val < R.length := by have := j.isLt; omega
  refine ⟨hk, ?_⟩
  rw [hH.getElem j.isLt]
  simp only [List.getElem_drop]
  rfl

private theorem actual_unoccupied_diagnostics
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (i : Fin (p.m - 1)) (choice : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hc : ((ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[k.val].output.preparation.followers.followers i).configuration =
        .ordinary choice memory)
    (hu : choice.status = .unoccupied) :
    let r := (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[k.val]
    ∃ (logged : ReferencePrelaunchFollower.State p rate.eta)
      (cut : ReferenceDownCutOutput p rate),
      (r.output.followers i).downInput = some logged ∧
      (r.output.followers i).down = some cut ∧
      logged.lastDown = choice.lastDown ∧ logged.downBatch = choice.downBatch ∧
      logged.status = .unoccupied ∧
      (downSelected p i r.input.row r.input.time →
        registerInputDomain p rate logged ∧ decoderInputDomain p logged.downBatch ∧
        bufferInputDomain p logged.buffer ∧ cut.rawComparison.isSome = true) := by
  dsimp only
  let r := (ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate z rewards C_star C_h)[k.val]
  let f := r.output.preparation.followers.followers i
  let own := ReferenceFollowerDownDecoderReplay.preparedOwnObservation r i
  obtain ⟨_, _, _, next, nextMemory, _, _, _, _, hnext, _, _⟩ :=
    ReferenceCompleteSuffixFollowerPreservation.complete_suffix_follower_output
      rewards C_star C_h z k i
  have hfinish := ReferenceFollowerBufferProvenance.roundRecord_follower_eq_finishFollower i r
  change r.output.followers i = ReferenceActivePhysicalStep.finishFollower
    r.output.preparation.coordinator.downView f own at hfinish
  have hn : (ReferenceActivePhysicalStep.finishFollower
      r.output.preparation.coordinator.downView f own).configuration =
        .ordinary next nextMemory := by
    rw [← hfinish]
    exact hnext
  obtain ⟨choice', memory', post, hc', hrecord, _, hdiagInput, hdiagDown⟩ :=
    ReferenceFollowerReplyChronology.finishFollower_ordinary_inversion _ _ _ next nextMemory hn
  obtain ⟨he, hm⟩ := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
    (hc'.symm.trans hc)
  subst choice'
  subst memory'
  cases hlogging : ActiveFollowerLogging.checkedLogging f.follower f.row f.activation
      f.time (f.arm, own) choice with
  | error failure =>
      simp only [ReferenceActivePhysicalStep.recordFollower, dite_eq_left hu, hlogging] at hrecord
      cases hrecord
  | ok logged =>
      let cut := referenceDownCut p r.output.preparation.coordinator.downView
        f.follower f.row f.time own rate logged
      simp only [ReferenceActivePhysicalStep.recordFollower, dite_eq_left hu, hlogging] at hrecord
      change DeclaredFollowerLocalRound.consumeDownResult rate cut.outcome = .ok post at hrecord
      have hlog := ReferenceActivePhysicalStep.recordFollower_logged
        r.output.preparation.coordinator.downView f.follower f.row f.activation f.time
        f.active f.arm own choice logged hu hlogging
      have hi : (r.output.followers i).downInput = some logged := by
        rw [hfinish]
        exact hdiagInput.trans hlog.1
      have hd : (r.output.followers i).down = some cut := by
        rw [hfinish]
        exact hdiagDown.trans hlog.2
      have hframe := ActiveFollowerLogging.checkedLogging_success_frame
        f.follower f.row f.activation f.time (f.arm, own) choice logged hlogging
      have hstatus : logged.status = .unoccupied := hframe.2.2.2.2.1.trans hu
      refine ⟨logged, cut, hi, hd, hframe.1, hframe.2.2.2.2.2.1, hstatus, ?_⟩
      intro hdown
      change downSelected p i r.input.row r.input.time at hdown
      have hcut : cut = referenceDownCut p r.output.preparation.coordinator.downView
          i r.input.row r.input.time own rate logged := by
        dsimp only [cut, f]
        rw [(r.output.preparation.follower_alignment i).1,
          (r.output.preparation.follower_alignment i).2.1,
          (r.output.preparation.follower_alignment i).2.2.1]
      rw [hcut] at hrecord ⊢
      simp only [referenceDownCut, hdown, hstatus, dite_true] at hrecord ⊢
      by_cases hr : registerInputDomain p rate logged
      · rw [dite_eq_left hr] at hrecord ⊢
        by_cases hb : decoderInputDomain p logged.downBatch
        · rw [dite_eq_left hb] at hrecord ⊢
          by_cases hbuf : bufferInputDomain p logged.buffer
          · rw [dite_eq_left hbuf] at hrecord ⊢
            exact ⟨hr, hb, hbuf, by split <;> rfl⟩
          · rw [dite_eq_right hbuf] at hrecord
            cases hrecord
        · rw [dite_eq_right hb] at hrecord
          cases hrecord
      · rw [dite_eq_right hr] at hrecord
        cases hrecord

private theorem actualHandoverRecord_sourceDate
    (b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (j : Fin (ReferencePostReplacementCollectionHandoverDecoderCorrespondence.actualHandoverRecords
      rate rewards C_star C_h z b).length) :
    ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
        (ReferencePostReplacementCollectionHandoverDecoderCorrespondence.actualHandoverRecords
          rate rewards C_star C_h z b)[j.val].input.time z =
      some (ReferencePostReplacementCollectionHandoverDecoderCorrespondence.actualHandoverRecords
        rate rewards C_star C_h z b)[j.val] := by
  let H := ReferencePostReplacementCollectionHandoverDecoderCorrespondence.actualHandoverRecords
    rate rewards C_star C_h z b
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let V := R[b.val] :: ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
    rate rewards C_star C_h z (b.val + 1)
  have hV : V.IsPrefix (R.drop b.val) := by
    rw [List.drop_eq_getElem_cons b.isLt]
    exact List.cons_prefix_cons.mpr ⟨rfl, List.takeWhile_prefix _⟩
  have hH : H.IsPrefix (R.drop b.val) := by
    change (V.takeWhile ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice).IsPrefix
      (R.drop b.val)
    exact (List.takeWhile_prefix _).trans hV
  have hjH : j.val < H.length := by
    simpa only [H] using j.isLt
  have hk : b.val + j.val < R.length := by
    have hlen := hH.length_le
    change H.length ≤ (R.drop b.val).length at hlen
    simp only [List.length_drop] at hlen
    change j.val < H.length at hjH
    omega
  have hrecord : H[j.val] = R[b.val + j.val]'hk := by
    rw [hH.getElem hjH]
    simp only [List.getElem_drop]
  have htime := ReferenceAssignmentFollowerMassSteps.complete_record_time
    rate rewards C_star C_h z ⟨b.val + j.val, hk⟩
  have hdate : H[j.val].input.time = (R[b.val + j.val]'hk).input.time := by
    rw [hrecord]
  rw [hdate]
  unfold ReferenceSourcePrefixHistoryFiltration.actualRecord
  have hstart : ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h ≤
      (R[b.val + j.val]'hk).input.time.val := by
    rw [htime]
    omega
  rw [ite_eq_left hstart]
  have hindex : (R[b.val + j.val]'hk).input.time.val -
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h =
        b.val + j.val := by
    rw [htime]
    simp only [Nat.add_sub_cancel_left]
  rw [hindex, List.getElem?_eq_getElem hk]
  change some (R[b.val + j.val]'hk) = some (H[j.val])
  exact congrArg some hrecord.symm

/-- The accepted later-installation decoder API supplies the actual birth
state and the complete inherited bank at every handover date. We initialize
the stopped local phase from that same bank and accepted-start register. -/
public theorem actual_later_handover_stoppedReplay_seed
    (b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (hb : ReferenceCollectionPhaseHistory.laterChosen
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[b.val].input = true)
    (i : Fin (p.m - 1)) :
    ∃ (payload : ReferenceActivePhysicalStep.Payload rate)
      (before : ReferencePrelaunchFollower.State p rate.eta)
      (beforeMemory : ActiveFollowerLifecycle.LocalMemory p),
      ReferenceAssignmentPayloadPersistence.InstallationBirth
        (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[b.val] payload ∧
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[b.val].input.state.followers i =
        .ordinary before beforeMemory ∧
      before.status = .unoccupied ∧
      ReferencePrelaunchFollower.acceptedStart before <
        (payload.downRecord i).val.sigma ∧
      ReferenceFollowerDecoderChronology.downBatchWellFormed before.downBatch ∧
      (∀ entry ∈ before.downBatch.pending,
        entry.time.val <
          (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[b.val].input.time.val) ∧
      ReferenceFollowerDecoderChronology.downCollectedChronological before.downBatch ∧
      (∀ entry ∈ AffineBatchDecoder.collected before.downBatch,
        entry.time.val <
          (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[b.val].input.time.val) ∧
      (HandoverStoppedDecoderReplay.initial p before.downBatch
        (ReferencePrelaunchFollower.acceptedStart before)).phase = .awaitingDown ∧
      ∀ j : Fin (ReferencePostReplacementCollectionHandoverDecoderCorrespondence.actualHandoverRecords
        rate rewards C_star C_h z b).length,
        ∃ (inputState : ReferencePrelaunchFollower.State p rate.eta)
          (inputMemory : ActiveFollowerLifecycle.LocalMemory p),
          (ReferencePostReplacementCollectionHandoverDecoderCorrespondence.actualHandoverRecords
            rate rewards C_star C_h z b)[j.val].input.state.followers i =
              .ordinary inputState inputMemory ∧
          inputState.downBatch = ReferenceFollowerDownDecoderReplay.replayDownCalls i
            ((ReferencePostReplacementCollectionHandoverDecoderCorrespondence.actualHandoverRecords
              rate rewards C_star C_h z b).take j.val) before.downBatch := by
  obtain ⟨payload, before, beforeMemory, hbirth, hbefore, hunoccupied, hstrict, hdates⟩ :=
    ReferencePostReplacementCollectionHandoverDecoderCorrespondence.actual_later_handover_decoder_correspondence
      rewards C_star C_h z b hb i
  have hseedBank := ReferencePostReplacementCollectionHandoverReplay.actual_later_installation_birth_bank_replay
    rate rewards C_star C_h z b
  rw [ite_eq_left hb] at hseedBank
  obtain ⟨_, _, _, _, hseedStates⟩ := hseedBank
  obtain ⟨seedBefore, seedMemory, _choice, _choiceMemory, _initialFollower, _initialMemory,
      hseedBefore, _hseedBeforeStatus, _hchoice, _hchoiceStatus, _hreply, _hbuffer,
      _hfailure, _hmemory, _hinitial, _hwellSeed, _hchronSeed, _hstampSeed,
      _hbankReplay, hwell, hpendingStamps, hchron, hcollectedStamps⟩ := hseedStates i
  have hsame := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
    (hseedBefore.symm.trans hbefore)
  rw [hsame.1] at hwell hpendingStamps hchron hcollectedStamps
  refine ⟨payload, before, beforeMemory, hbirth, hbefore, hunoccupied, hstrict,
    hwell, hpendingStamps, hchron, hcollectedStamps, rfl, ?_⟩
  intro j
  obtain ⟨_, _, _, inputState, inputMemory, _, _, _, hin, hbank, _, _, _, _, _, _⟩ := hdates j
  exact ⟨inputState, inputMemory, hin, hbank⟩

/-- A wrong-unique DOWN result on an actual later-handover record is the
literal original-source false event at that record's calendar date. -/
public theorem actual_later_handover_wrongUniqueAccepted_mem_S_false
    (b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (j : Fin (ReferencePostReplacementCollectionHandoverDecoderCorrespondence.actualHandoverRecords
      rate rewards C_star C_h z b).length)
    (i : Fin (p.m - 1))
    (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
    (hcut : ((ReferencePostReplacementCollectionHandoverDecoderCorrespondence.actualHandoverRecords
      rate rewards C_star C_h z b)[j.val].output.followers i).down = some cut)
    (hwrong : ReferenceDownReception.wrongUniqueAccepted cut) :
    ReferenceLiteralSourceDecoderCoverage.S_false rate rewards C_star C_h z
      (ReferencePostReplacementCollectionHandoverDecoderCorrespondence.actualHandoverRecords
        rate rewards C_star C_h z b)[j.val].input.time := by
  let H := ReferencePostReplacementCollectionHandoverDecoderCorrespondence.actualHandoverRecords
    rate rewards C_star C_h z b
  have hsource := actualHandoverRecord_sourceDate rate rewards C_star C_h z b j
  change ReferenceLiteralSourceDecoderCoverage.S_false rate rewards C_star C_h z H[j.val].input.time
  change
    (∃ k, ReferenceSourceRawDecoderDecision.prelaunch_down_wrong
        rate rewards C_star C_h z H[j.val].input.time k) ∨
      (∃ k, ReferenceSourceRawDecoderDecision.source_down_wrong
        rate rewards C_star C_h z H[j.val].input.time k) ∨
      (∃ k, ReferenceSourceRawDecoderDecision.source_up_wrong
        rate rewards C_star C_h z H[j.val].input.time k)
  exact Or.inr (Or.inl ⟨i,
    (ReferenceSourceRawDecoderDecision.source_down_wrong_iff
      rate rewards C_star C_h z H[j.val].input.time i).2
      ⟨H[j.val], cut, hsource, hcut, hwrong⟩⟩)

/-- Preserve the actual current decode call, inherited bank and raw output
alongside the same-date literal false cover for a wrong-unique DOWN result. -/
public theorem actual_later_handover_wrongUniqueAccepted_sourceAndOutput
    (b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (hb : ReferenceCollectionPhaseHistory.laterChosen
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[b.val].input = true)
    (j : Fin (ReferencePostReplacementCollectionHandoverDecoderCorrespondence.actualHandoverRecords
      rate rewards C_star C_h z b).length)
    (i : Fin (p.m - 1))
    (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
    (hcut : ((ReferencePostReplacementCollectionHandoverDecoderCorrespondence.actualHandoverRecords
      rate rewards C_star C_h z b)[j.val].output.followers i).down = some cut)
    (hwrong : ReferenceDownReception.wrongUniqueAccepted cut) :
    ReferenceLiteralSourceDecoderCoverage.S_false rate rewards C_star C_h z
        (ReferencePostReplacementCollectionHandoverDecoderCorrespondence.actualHandoverRecords
          rate rewards C_star C_h z b)[j.val].input.time ∧
      ∃ (payload : ReferenceActivePhysicalStep.Payload rate)
        (before : ReferencePrelaunchFollower.State p rate.eta)
        (beforeMemory : ActiveFollowerLifecycle.LocalMemory p),
        ReferenceAssignmentPayloadPersistence.InstallationBirth
          (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[b.val]
          payload ∧
        (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[b.val].input.state.followers i =
          .ordinary before beforeMemory ∧
        before.status = .unoccupied ∧
        ReferencePrelaunchFollower.acceptedStart before < (payload.downRecord i).val.sigma ∧
        let live := ReferencePostReplacementCollectionHandoverDecoderCorrespondence.actualLaterHandoverLive
          rate rewards C_star C_h z payload
          (ReferencePostReplacementCollectionHandoverDecoderCorrespondence.actualHandoverRecords
            rate rewards C_star C_h z b)
        let trace := HandoverStoppedDecoderReplay.observationTrace p payload.assignment
          (HandoverStoppedDecoderReplay.fromLive p payload.assignment live
            (fun _ => false) (fun _ => false)) i
        ∃ (selected : ReferenceActivePhysicalStep.Selection
            (ReferencePostReplacementCollectionHandoverDecoderCorrespondence.actualHandoverRecords
              rate rewards C_star C_h z b)[j.val].input)
          (states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
          (memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p)
          (inputState : ReferencePrelaunchFollower.State p rate.eta)
          (inputMemory : ActiveFollowerLifecycle.LocalMemory p),
          (ReferencePostReplacementCollectionHandoverDecoderCorrespondence.actualHandoverRecords
            rate rewards C_star C_h z b)[j.val].output.preparation.coordinator.selection = some selected ∧
          selected.view.payload = payload ∧
          (∀ k, ((ReferencePostReplacementCollectionHandoverDecoderCorrespondence.actualHandoverRecords
            rate rewards C_star C_h z b)[j.val].output.preparation.followers.followers k).configuration =
              .ordinary (states k) (memories k)) ∧
          (ReferencePostReplacementCollectionHandoverDecoderCorrespondence.actualHandoverRecords
            rate rewards C_star C_h z b)[j.val].input.state.followers i =
              .ordinary inputState inputMemory ∧
          inputState.downBatch = ReferenceFollowerDownDecoderReplay.replayDownCalls i
            ((ReferencePostReplacementCollectionHandoverDecoderCorrespondence.actualHandoverRecords
              rate rewards C_star C_h z b).take j.val) before.downBatch ∧
          (states i).downBatch = inputState.downBatch ∧
          ActiveObservationBridge.liveSnapshotBefore p payload.assignment live
            (ReferencePostReplacementCollectionHandoverDecoderCorrespondence.actualHandoverRecords
              rate rewards C_star C_h z b)[j.val].input.time =
                ⟨selected.view.pendingAtChoice, fun k => (states k).status⟩ ∧
          ∃ logged : ReferencePrelaunchFollower.State p rate.eta,
            ((ReferencePostReplacementCollectionHandoverDecoderCorrespondence.actualHandoverRecords
              rate rewards C_star C_h z b)[j.val].output.followers i).downInput = some logged ∧
            logged.downBatch = ReferenceFollowerDownDecoderReplay.replayDownCalls i
              ((ReferencePostReplacementCollectionHandoverDecoderCorrespondence.actualHandoverRecords
                rate rewards C_star C_h z b).take j.val) before.downBatch ∧
            AffineBatchDecoder.decodeStep p trace
              (ReferenceFollowerDownDecoderReplay.replayDownCalls i
                ((ReferencePostReplacementCollectionHandoverDecoderCorrespondence.actualHandoverRecords
                  rate rewards C_star C_h z b).take j.val) before.downBatch)
              (ReferencePostReplacementCollectionHandoverDecoderCorrespondence.actualHandoverRecords
                rate rewards C_star C_h z b)[j.val].input.time =
              ActiveFollowerDownAcceptance.currentDecodeStep p i
                (ReferencePostReplacementCollectionHandoverDecoderCorrespondence.actualHandoverRecords
                  rate rewards C_star C_h z b)[j.val].input.row
                (ReferencePostReplacementCollectionHandoverDecoderCorrespondence.actualHandoverRecords
                  rate rewards C_star C_h z b)[j.val].input.time
                ((ReferencePostReplacementCollectionHandoverDecoderCorrespondence.actualHandoverRecords
                  rate rewards C_star C_h z b)[j.val].output.preparation.feedback.observations
                  (PublicDiscreteDraws.followerPlayer p.two_le_m i)) rate logged ∧
            cut.raw = (AffineBatchDecoder.decodeStep p trace
              (ReferenceFollowerDownDecoderReplay.replayDownCalls i
                ((ReferencePostReplacementCollectionHandoverDecoderCorrespondence.actualHandoverRecords
                  rate rewards C_star C_h z b).take j.val) before.downBatch)
              (ReferencePostReplacementCollectionHandoverDecoderCorrespondence.actualHandoverRecords
                rate rewards C_star C_h z b)[j.val].input.time).2 := by
  refine ⟨actual_later_handover_wrongUniqueAccepted_mem_S_false
    rate rewards C_star C_h z b j i cut hcut hwrong, ?_⟩
  obtain ⟨payload, before, beforeMemory, hbirth, hbefore, hunoccupied, hstrict, hdates⟩ :=
    ReferencePostReplacementCollectionHandoverDecoderCorrespondence.actual_later_handover_decoder_correspondence
      rewards C_star C_h z b hb i
  refine ⟨payload, before, beforeMemory, hbirth, hbefore, hunoccupied, hstrict, ?_⟩
  dsimp only
  obtain ⟨selected, states, memories, inputState, inputMemory,
      hselection, hpayload, hconfig, hin, hbank, hchoiceBank, hsnapshot,
      hoccupied, hnotselected, hinput, hcutCases⟩ := hdates j
  have hcompared : cut.rawComparison ≠ none := by
    rw [hwrong.1]
    decide
  obtain hnone | ⟨logged, hloggedInput, hloggedBank, hdecode, hraw⟩ := hcutCases cut hcut
  · exact (hcompared hnone).elim
  · exact ⟨selected, states, memories, inputState, inputMemory,
      hselection, hpayload, hconfig, hin, hbank, hchoiceBank, hsnapshot,
      logged, hloggedInput, hloggedBank, hdecode, hraw⟩

section AwaitedCalls

local notation "R" => ReferenceCompletePhysicalHistory.completeSuffixRecords
  rate z rewards C_star C_h
local notation "β" => CanonicalRecordingRates.beta p rate.eta.val

variable (b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
  rate z rewards C_star C_h).length)
local notation "H" => actualHandoverRecords rate rewards C_star C_h z b

private theorem actual_handover_record_time (j : Fin (H).length) :
    H[j.val].input.time.val = R[b.val].input.time.val + j.val := by
  obtain ⟨hk, heq⟩ := actual_handover_record_index rate rewards C_star C_h z b j
  have ht := completeSuffixRecord_time rate rewards C_star C_h z ⟨b.val + j.val, hk⟩
  have hb := completeSuffixRecord_time rate rewards C_star C_h z b
  calc
    _ = ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h +
        (b.val + j.val) := by rw [heq]; exact ht
    _ = R[b.val].input.time.val + j.val := by rw [hb]; omega

private theorem false_decision_iff_wrong_unique
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1)) (payload : ReferenceActivePhysicalStep.Payload rate)
    (logged : ReferencePrelaunchFollower.State p rate.eta)
    (cut : ReferenceDownCutOutput p rate)
    (hi : (r.output.followers i).downInput = some logged)
    (hd : (r.output.followers i).down = some cut)
    (hc : cut.rawComparison.isSome = true)
    (he : cut.expectedWord = some (currentWord p β (payload.downRecord i))) :
    falseDecision p β (payload.downRecord i)
        (ReferencePrelaunchFollower.acceptedStart logged) r.input.time cut.raw ↔
      wrongUniqueAccepted cut := by
  have hf := retained_call_fields r i logged cut hi hd hc
  have ha : cut.ordinaryAcceptance = ordinaryLocalAcceptanceTest p rate
      r.input.time logged (ordinaryParse p rate cut.raw) := hf.2.2.2.2.2.2.2.2.1
  have hcmp := hf.2.2.2.2.2.2.2.2.2
  constructor
  · rintro ⟨other, hparse, hne, haccept⟩
    have hrawNe : cut.raw ≠ some (currentWord p β (payload.downRecord i)) := by
      intro hraw
      rw [hraw] at hparse
      have hcurrent := parseOutput_currentWord p β (payload.downRecord i)
      exact hne (Option.some.inj (hparse.symm.trans hcurrent))
    refine ⟨?_, ?_, ?_⟩
    · rw [hcmp, he, decide_eq_false hrawNe]
    · intro hn
      rw [hn, parseOutput_none] at hparse
      cases hparse
    · rw [ha]
      change ordinaryLocalAcceptanceTest p rate r.input.time logged
        (parseOutput p β cut.raw)
      rw [hparse]
      exact haccept
  · rintro ⟨hcomp, _, haccept⟩
    rw [ha] at haccept
    change ordinaryLocalAcceptanceTest p rate r.input.time logged
      (parseOutput p β cut.raw) at haccept
    cases hparse : parseOutput p β cut.raw with
    | none => rw [hparse] at haccept; cases haccept
    | some other =>
        have hne : other ≠ payload.downRecord i := by
          intro heq
          subst other
          have hraw := (ReferenceFirstLiveHandoverPhaseReplay.parseOutput_eq_some_iff
            β (payload.downRecord i) cut.raw).mp hparse
          have htrue : cut.rawComparison = some true :=
            hcmp.trans (congrArg some (decide_eq_true (hraw.trans he.symm)))
          cases htrue.symm.trans hcomp
        rw [hparse] at haccept
        exact ⟨other, hparse, hne, haccept⟩

/-- Every actual selected DOWN date at an awaiting later-handover receiver
is an ordinary physically awaited call. This includes zero feedback and uses
the retained old accepted start and the full inherited bank. The false-word
dictionary is evaluated before reference filtering, on this same date. -/
public theorem actual_later_handover_awaiting_calls
    (hb : ReferenceCollectionPhaseHistory.laterChosen R[b.val].input = true)
    (i : Fin (p.m - 1)) :
    ∃ (payload : ReferenceActivePhysicalStep.Payload rate)
      (before : ReferencePrelaunchFollower.State p rate.eta)
      (beforeMemory : ActiveFollowerLifecycle.LocalMemory p),
      ReferenceAssignmentPayloadPersistence.InstallationBirth R[b.val] payload ∧
      R[b.val].input.state.followers i = .ordinary before beforeMemory ∧
      before.status = .unoccupied ∧
      ReferencePrelaunchFollower.acceptedStart before < (payload.downRecord i).val.sigma ∧
      ∀ j : Fin (H).length,
        ∃ (selected : ReferenceActivePhysicalStep.Selection H[j.val].input)
          (choice : ReferencePrelaunchFollower.State p rate.eta)
          (memory : ActiveFollowerLifecycle.LocalMemory p),
          H[j.val].output.preparation.coordinator.selection = some selected ∧
          selected.view.payload = payload ∧
          (H[j.val].output.preparation.followers.followers i).configuration =
            .ordinary choice memory ∧
          (choice.status = .unoccupied →
            ReferencePrelaunchFollower.acceptedStart choice =
              ReferencePrelaunchFollower.acceptedStart before ∧
            ∀ _hdown : downSelected p i H[j.val].input.row H[j.val].input.time,
              ∃ (logged : ReferencePrelaunchFollower.State p rate.eta)
                (cut : ReferenceDownCutOutput p rate),
                (H[j.val].output.followers i).downInput = some logged ∧
                (H[j.val].output.followers i).down = some cut ∧
                logged.downBatch = choice.downBatch ∧
                ReferencePrelaunchFollower.acceptedStart logged =
                  ReferencePrelaunchFollower.acceptedStart before ∧
                cut.rawComparison.isSome = true ∧
                ReferenceLiteralSourceDecoderCoverage.physicalAwaitedDownAt H[j.val] i
                  (currentWord p β (payload.downRecord i)) ∧
                cut.ordinaryParse = parseOutput p β cut.raw ∧
                (falseDecision p β (payload.downRecord i)
                    (ReferencePrelaunchFollower.acceptedStart before) H[j.val].input.time cut.raw ↔
                  wrongUniqueAccepted cut)) := by
  have hstages := ReferencePostReplacementCollectionHandoverReplay.actual_later_installation_handover_choice_stages
    rate rewards C_star C_h z b
  rw [ite_eq_left hb] at hstages
  obtain ⟨payload, hbirth, hfollowers⟩ := hstages
  obtain ⟨before, beforeMemory, hbefore, huBefore, hstrict, hdates⟩ := hfollowers i
  change ∀ j : Fin (H).length, _ at hdates
  refine ⟨payload, before, beforeMemory, hbirth, hbefore, huBefore, hstrict, ?_⟩
  intro j
  obtain ⟨selected, choice, memory, hs, hp, hc, hstage⟩ := hdates j
  change H[j.val].output.preparation.coordinator.selection = some selected at hs
  change (H[j.val].output.preparation.followers.followers i).configuration =
    .ordinary choice memory at hc
  refine ⟨selected, choice, memory, hs, hp, hc, ?_⟩
  intro hu
  have hawait : i ∈ selected.view.pendingAtChoice ∧
      ReferencePrelaunchFollower.acceptedStart choice =
        ReferencePrelaunchFollower.acceptedStart before := by
    rcases hstage with h | h | h
    · exact ⟨h.1, h.2.2.2⟩
    · rw [hu] at h; cases h.2.1
    · rw [hu] at h; cases h.2.1
  refine ⟨hawait.2, ?_⟩
  intro hdown
  obtain ⟨hk, hj⟩ := actual_handover_record_index rate rewards C_star C_h z b j
  have hcR : ((R[b.val + j.val]'hk).output.preparation.followers.followers i).configuration =
      .ordinary choice memory := hj ▸ hc
  obtain ⟨logged, cut, hi, hd, hlast, hbank, hstatus, hdomains⟩ :=
    actual_unoccupied_diagnostics rate rewards C_star C_h z ⟨b.val + j.val, hk⟩
      i choice memory hcR hu
  rw [← hj] at hi hd hdomains
  obtain ⟨hreg, hdec, hbuf, hcomp⟩ := hdomains hdown
  have hstart : ReferencePrelaunchFollower.acceptedStart logged =
      ReferencePrelaunchFollower.acceptedStart before := by
    unfold ReferencePrelaunchFollower.acceptedStart
    rw [hlast]
    exact hawait.2
  have hview : H[j.val].output.preparation.coordinator.downView = some selected.view := by
    change H[j.val].output.preparation.coordinator.selection.map
      ReferenceActivePhysicalStep.Selection.view = some selected.view
    exact congrArg (Option.map ReferenceActivePhysicalStep.Selection.view) hs
  have hexpected : cut.expectedWord = some (currentWord p β (payload.downRecord i)) := by
    have he := selected.expected_down_word i ⟨hdown.1, hdown.2, hawait.1⟩
    change expectedDownFlatWord (some selected.view) i H[j.val].input.row
      H[j.val].input.time = some (CoordinatorLocalArmChoice.storedDownFlatWord
        selected.view.payload i) at he
    have he' : some (CoordinatorLocalArmChoice.storedDownFlatWord selected.view.payload i) =
        some (currentWord p β (payload.downRecord i)) := by rw [hp]; rfl
    exact (retained_call_fields H[j.val] i logged cut hi hd hcomp).2.2.2.2.2.2.1.trans
      ((congrArg (fun v => expectedDownFlatWord v i H[j.val].input.row H[j.val].input.time)
        hview).trans (he.trans he'))
  have hsent := ReferenceSourceRawDecoderDecision.retained_down_sent
    H[j.val] i logged cut hi hd hcomp
  have htime := actual_handover_record_time rate rewards C_star C_h z b j
  have hbirthTime := ReferenceAssignmentPayloadChronology.installationBirth_time_eq
    R[b.val] payload hbirth
  have hsigma : (payload.downRecord i).val.sigma = payload.sigma.val + 1 := rfl
  have hparse : ordinaryParse p rate (some (currentWord p β (payload.downRecord i))) =
      some (payload.downRecord i) := parseOutput_currentWord p β _
  refine ⟨logged, cut, hi, hd, hbank, hstart, hcomp, ?_, ?_, ?_⟩
  · exact ⟨logged, cut, payload.downRecord i, hi, hd, hdown, hstatus,
      hreg, hdec, hbuf, hsent.symm.trans hexpected, hparse, hstart ▸ hstrict, by omega⟩
  · exact (retained_call_fields H[j.val] i logged cut hi hd hcomp).2.2.2.2.2.2.2.1
  · rw [← hstart]
    exact false_decision_iff_wrong_unique rate H[j.val] i payload logged cut hi hd hcomp hexpected

private theorem live_unoccupied_predecessor
    (a : ActiveRoundActions.Assignment p.m p.K)
    (live : Fin p.T → ActiveRoundActions.LiveRoundData a (AffineBatchDecoder.width p))
    (i : Fin (p.m - 1)) (u v : Fin p.T) (huv : u.val ≤ v.val)
    (hv : (ActiveObservationBridge.liveSnapshotBefore p a live v).status i = .unoccupied) :
    (ActiveObservationBridge.liveSnapshotBefore p a live u).status i = .unoccupied := by
  have one (s : ActiveRoundActions.Snapshot a)
      (d : ActiveRoundActions.LiveRoundData a (AffineBatchDecoder.width p))
      (h : (ActiveRoundActions.finishLiveRound p.two_le_m s d.input d.rewards d.acceptCurrent).status i =
        .unoccupied) : s.status i = .unoccupied := by
    change (if s.status i = .pending ∧
      ActiveRoundActions.releaseObservation p.two_le_m s d.input d.rewards i then .released
      else ActiveRoundActions.statusAfterAcceptance s d.input d.acceptCurrent i) = .unoccupied at h
    split at h
    · cases h
    · unfold ActiveRoundActions.statusAfterAcceptance at h
      split at h
      · cases h
      · exact h
  have fold (ds : List (ActiveRoundActions.LiveRoundData a (AffineBatchDecoder.width p))) :
      ∀ s : ActiveRoundActions.Snapshot a,
      (ds.foldl (fun s d => ActiveRoundActions.finishLiveRound p.two_le_m
        s d.input d.rewards d.acceptCurrent) s).status i = .unoccupied →
      s.status i = .unoccupied := by
    induction ds with
    | nil => intro s h; exact h
    | cons d ds ih => intro s h; exact one s d (ih _ h)
  obtain ⟨tail, he⟩ := List.take_prefix_take_left
    (l := List.ofFn live) huv
  change ((List.ofFn live).take v.val |>.foldl
    (fun s d => ActiveRoundActions.finishLiveRound p.two_le_m
      s d.input d.rewards d.acceptCurrent) (ActiveRoundActions.initialSnapshot a)).status i =
      .unoccupied at hv
  rw [← he, List.foldl_append] at hv
  exact fold tail _ hv

private theorem actual_choice_snapshot
    (hb : ReferenceCollectionPhaseHistory.laterChosen R[b.val].input = true)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (hbirth : ReferenceAssignmentPayloadPersistence.InstallationBirth R[b.val] payload)
    (j : Fin (H).length) (i : Fin (p.m - 1))
    (choice : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hc : (H[j.val].output.preparation.followers.followers i).configuration =
      .ordinary choice memory) :
    (ActiveObservationBridge.liveSnapshotBefore p payload.assignment
      (actualLaterHandoverLive rate rewards C_star C_h z payload H)
      H[j.val].input.time).status i = choice.status := by
  obtain ⟨P, hP, dates⟩ := actual_later_handover_snapshot rewards C_star C_h z b hb
  have he := ReferenceAssignmentPayloadChronology.installationBirth_payload_unique
    R[b.val] P payload hP hbirth
  subst P
  obtain ⟨selected, states, memories, _, _, hconfig, hsnap, _⟩ := dates j
  have hchoice := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
    ((hconfig i).symm.trans hc)
  rw [hsnap]
  exact congrArg ReferencePrelaunchFollower.State.status hchoice.1

private theorem actual_trace_input
    (hb : ReferenceCollectionPhaseHistory.laterChosen R[b.val].input = true)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (hbirth : ReferenceAssignmentPayloadPersistence.InstallationBirth R[b.val] payload)
    (j : Fin (H).length) (i : Fin (p.m - 1))
    (choice : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hc : (H[j.val].output.preparation.followers.followers i).configuration =
      .ordinary choice memory)
    (hu : choice.status = .unoccupied)
    (hd : downSelected p i H[j.val].input.row H[j.val].input.time) :
    observationTrace p payload.assignment
      (fromLive p payload.assignment
        (actualLaterHandoverLive rate rewards C_star C_h z payload H)
        (fun _ => false) (fun _ => false)) i H[j.val].input.time =
      currentRoundInput p i H[j.val].input.row H[j.val].input.time
        (ReferenceFollowerDownDecoderReplay.preparedOwnObservation H[j.val] i) rate choice := by
  obtain ⟨P, _, _, hP, _, _, _, dates⟩ :=
    actual_later_handover_decoder_correspondence rewards C_star C_h z b hb i
  have he := ReferenceAssignmentPayloadChronology.installationBirth_payload_unique
    R[b.val] P payload hP hbirth
  subst P
  obtain ⟨_, states, memories, _, _, _, _, hconfig, _, _, _, _, _, _, hinput, _⟩ := dates j
  have hchoice := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
    ((hconfig i).symm.trans hc)
  have hin := (hinput hd (hchoice.1 ▸ hu)).1
  exact hin.trans (congrArg (fun state => currentRoundInput p i H[j.val].input.row
    H[j.val].input.time (ReferenceFollowerDownDecoderReplay.preparedOwnObservation H[j.val] i)
      rate state) hchoice.1)

private theorem actual_handover_record_at_date
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (hbirth : ReferenceAssignmentPayloadPersistence.InstallationBirth R[b.val] payload)
    (j : Fin (H).length) (v : Fin p.T)
    (hs : payload.sigma.val ≤ v.val) (ht : v.val ≤ H[j.val].input.time.val) :
    ∃ k : Fin (H).length, k.val ≤ j.val ∧ H[k.val].input.time = v := by
  have hbirthTime := ReferenceAssignmentPayloadChronology.installationBirth_time_eq
    R[b.val] payload hbirth
  have hj := actual_handover_record_time rate rewards C_star C_h z b j
  have hk : v.val - payload.sigma.val < (H).length := by have := j.isLt; omega
  let k : Fin (H).length := ⟨v.val - payload.sigma.val, hk⟩
  have hktime := actual_handover_record_time rate rewards C_star C_h z b k
  refine ⟨k, by dsimp only [k]; omega, Fin.ext ?_⟩
  calc
    _ = R[b.val].input.time.val + k.val := hktime
    _ = v.val := by dsimp only [k]; omega

private theorem actual_awaited_call
    (hb : ReferenceCollectionPhaseHistory.laterChosen R[b.val].input = true)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (hbirth : ReferenceAssignmentPayloadPersistence.InstallationBirth R[b.val] payload)
    (j : Fin (H).length) (i : Fin (p.m - 1))
    (choice : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hc : (H[j.val].output.preparation.followers.followers i).configuration =
      .ordinary choice memory)
    (hu : choice.status = .unoccupied)
    (hd : downSelected p i H[j.val].input.row H[j.val].input.time) :
    ReferenceLiteralSourceDecoderCoverage.physicalAwaitedDownAt H[j.val] i
      (currentWord p β (payload.downRecord i)) := by
  obtain ⟨P, _, _, hP, _, _, _, dates⟩ :=
    actual_later_handover_awaiting_calls rate rewards C_star C_h z b hb i
  have he := ReferenceAssignmentPayloadChronology.installationBirth_payload_unique
    R[b.val] P payload hP hbirth
  subst P
  obtain ⟨_, other, otherMemory, _, _, hc', hawait⟩ := dates j
  have hchoice := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj (hc'.symm.trans hc)
  obtain ⟨_, _, _, _, _, _, _, hphysical, _⟩ := (hawait (hchoice.1 ▸ hu)).2 hd
  exact hphysical

private theorem selectedChannel_down
    (slice : ContinuousLearningRows.Slice p) (i : Fin (p.m - 1))
    (h : ReferenceSelectedAffinePairLaw.selectedChannel p slice = some (0, i)) :
    PublicDiscreteDraws.slotDraw slice = PublicDiscreteDraws.downSlot ∧
      PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K slice = i := by
  by_cases hd : PublicDiscreteDraws.slotDraw slice = PublicDiscreteDraws.downSlot
  · rw [ReferenceSelectedAffinePairLaw.selectedChannel_of_down p slice hd] at h
    exact ⟨hd, congrArg Prod.snd (Option.some.inj h)⟩
  · by_cases hu : PublicDiscreteDraws.slotDraw slice = PublicDiscreteDraws.upSlot
    · rw [ReferenceSelectedAffinePairLaw.selectedChannel_of_up p slice hu] at h
      have he := congrArg Prod.fst (Option.some.inj h)
      have hn : (1 : Fin 2) ≠ 0 := by decide
      exact (hn he).elim
    · simp only [ReferenceSelectedAffinePairLaw.selectedChannel,
        ReferenceSelectedAffinePairLaw.channelFromDraws, hd, hu, ite_false] at h
      cases h

private theorem actual_awaited_interval
    (hb : ReferenceCollectionPhaseHistory.laterChosen R[b.val].input = true)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (hbirth : ReferenceAssignmentPayloadPersistence.InstallationBirth R[b.val] payload)
    (j : Fin (H).length) (i : Fin (p.m - 1))
    (choice : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hc : (H[j.val].output.preparation.followers.followers i).configuration =
      .ordinary choice memory)
    (hu : choice.status = .unoccupied) :
    ∀ v : Fin p.T, payload.sigma.val ≤ v.val → v.val ≤ H[j.val].input.time.val →
      ReferenceSelectedAffinePairLaw.selectedChannel p
        ((z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)).2 v).1 = some (0, i) →
      ∃ rv : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate),
        ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h v z = some rv ∧
        rv.input.rows = z.1.2 ∧
        rv.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p z ∧
        rv.input.time = v ∧ rv.input.rewards = rewards ∧
        ReferenceLiteralSourceDecoderCoverage.physicalAwaitedDownAt rv i
          (currentWord p β (payload.downRecord i)) := by
  intro v hs ht hsel
  obtain ⟨k, _, htime⟩ := actual_handover_record_at_date rate rewards C_star C_h z b
    payload hbirth j v hs ht
  have hsource := actualHandoverRecord_sourceDate rate rewards C_star C_h z b k
  rw [htime] at hsource
  have hfields := ReferenceLiteralSourceDecoderCoverage.actualRecord_original_fields
    rate rewards C_star C_h z v H[k.val] hsource
  obtain ⟨P, hP, dates⟩ := actual_later_handover_snapshot rewards C_star C_h z b hb
  have he := ReferenceAssignmentPayloadChronology.installationBirth_payload_unique
    R[b.val] P payload hP hbirth
  subst P
  obtain ⟨_, states, memories, _, _, hconfig, _, _⟩ := dates k
  have hcurrent := (actual_choice_snapshot rate rewards C_star C_h z b hb payload
    hbirth j i choice memory hc).trans hu
  have hpast := live_unoccupied_predecessor payload.assignment
    (actualLaterHandoverLive rate rewards C_star C_h z payload H) i v H[j.val].input.time ht hcurrent
  have hprevious := actual_choice_snapshot rate rewards C_star C_h z b hb payload
    hbirth k i (states i) (memories i) (hconfig i)
  rw [htime] at hprevious
  have hstatus : (states i).status = .unoccupied := hprevious.symm.trans hpast
  have hrow : H[k.val].input.row = z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) := by
    change H[k.val].input.rows H[k.val].input.selected = _
    rw [hfields.1, hfields.2.1]
  have hdown : downSelected p i H[k.val].input.row H[k.val].input.time := by
    rw [hrow, htime]
    exact selectedChannel_down _ i hsel
  exact ⟨H[k.val], hsource, hfields.1, hfields.2.1, hfields.2.2.1, hfields.2.2.2,
    actual_awaited_call rate rewards C_star C_h z b hb payload hbirth k i
      (states i) (memories i) (hconfig i) hstatus hdown⟩

private theorem actual_completed_batch_dates
    (hb : ReferenceCollectionPhaseHistory.laterChosen R[b.val].input = true)
    (j : Fin (H).length) (i : Fin (p.m - 1)) (B : List (DecoderEntry p))
    (hB : completedDownBatch H[j.val] i = some B) :
    ∀ e ∈ B, e.time.val ≤ H[j.val].input.time.val := by
  obtain ⟨_, logged, cut, hi, hd, _, hbank, _, _⟩ := completedDownBatch_spec H[j.val] i B hB
  obtain ⟨P, _, _, _, _, _, _, dates⟩ :=
    actual_later_handover_decoder_correspondence rewards C_star C_h z b hb i
  obtain ⟨_, states, memories, inputState, inputMemory, _, _, hconfigs, hin, _,
    hchoiceBank, _, _, _, _, _⟩ := dates j
  obtain ⟨choice, memory, hc, _, _, _, hloggedBank⟩ := retained_input_origin H[j.val] i logged hi
  have he := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
    ((hconfigs i).symm.trans hc)
  have hlogged : logged.downBatch = inputState.downBatch :=
    hloggedBank.trans ((congrArg ReferencePrelaunchFollower.State.downBatch he.1).symm.trans hchoiceBank)
  obtain ⟨hk, hj⟩ := actual_handover_record_index rate rewards C_star C_h z b j
  have hinR : (R[b.val + j.val]'hk).input.state.followers i = .ordinary inputState inputMemory := hj ▸ hin
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hstamps, _⟩ :=
    ReferencePostReplacementCollectionHandoverReplay.actual_complete_suffix_input_down_bank_replay
      rate rewards C_star C_h z ⟨b.val + j.val, hk⟩ i inputState inputMemory hinR
  intro e heB
  rw [hbank, appendedDownBatch, List.mem_append] at heB
  rcases heB with hold | hnew
  · rw [hlogged] at hold
    have ht := hstamps e hold
    rw [← hj] at ht
    exact ht.le
  · unfold AffineBatchDecoder.positiveAt at hnew
    split at hnew
    · have heq := List.mem_singleton.mp hnew
      have ht := congrArg AffineBatchDecoder.Entry.time heq
      exact le_of_eq (congrArg Fin.val ht)
    · cases hnew

private theorem positive_singleton_of_call
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1)) (call : ReferenceFollowerDownDecoderReplay.Call p)
    (hcall : ReferenceFollowerDownDecoderReplay.actualDownCall i r = some call)
    (e : DecoderEntry p)
    (he : e ∈ AffineBatchDecoder.positiveAt p (currentInputExtension p call.2) call.1) :
    e ∈ ReferenceFollowerDownDecoderReplay.actualDownPositives i [r] := by
  simp only [ReferenceFollowerDownDecoderReplay.actualDownPositives,
    ReferenceFollowerDownDecoderReplay.actualDownCalls, List.filterMap_cons, hcall,
    List.filterMap_nil, ReferenceFollowerDownDecoderReplay.positiveCallEntries,
    List.flatMap_cons, List.flatMap_nil, List.append_nil]
  exact he

private theorem positive_of_logged_input
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1)) (logged : ReferencePrelaunchFollower.State p rate.eta)
    (hi : (r.output.followers i).downInput = some logged)
    (tr : AffineBatchDecoder.Trace p) (e : DecoderEntry p)
    (ht : r.input.time = e.time)
    (hin : tr e.time = currentRoundInput p i r.input.row e.time
      (ReferenceFollowerDownDecoderReplay.preparedOwnObservation r i) rate logged)
    (hel : AffineBatchDecoder.eligible (tr e.time))
    (hsample : e.sample = (tr e.time).sample) :
    e ∈ ReferenceFollowerDownDecoderReplay.actualDownPositives i [r] := by
  let call : ReferenceFollowerDownDecoderReplay.Call p :=
    (e.time, currentRoundInput p i r.input.row e.time
      (ReferenceFollowerDownDecoderReplay.preparedOwnObservation r i) rate logged)
  have hcall : ReferenceFollowerDownDecoderReplay.actualDownCall i r = some call := by
    obtain ⟨code, hcode, hdecode⟩ := retained_call_reconstructs r i logged hi
    rw [← ReferenceDownCompletedAmbiguityMeasurability.downCallObservation_reconstructs i r,
      hcode, Option.map_some, hdecode, ht]
  have helCall : AffineBatchDecoder.eligible call.2 :=
    Eq.mp (congrArg AffineBatchDecoder.eligible hin) hel
  have heSample : e.sample = call.2.sample :=
    hsample.trans (congrArg AffineBatchDecoder.RoundInput.sample hin)
  apply positive_singleton_of_call rate r i call hcall e
  simp only [AffineBatchDecoder.positiveAt, currentInputExtension, helCall, ite_true,
    List.mem_singleton, AffineBatchDecoder.entry]
  cases e with
  | mk time sample => exact congrArg (AffineBatchDecoder.Entry.mk time) heSample

private theorem compared_call_raw
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1)) (logged : ReferencePrelaunchFollower.State p rate.eta)
    (cut : ReferenceDownCutOutput p rate)
    (hi : (r.output.followers i).downInput = some logged)
    (hd : (r.output.followers i).down = some cut)
    (hc : cut.rawComparison.isSome = true)
    (tr : AffineBatchDecoder.Trace p) (bank : DecoderState p)
    (hb : logged.downBatch = bank)
    (hin : tr r.input.time = currentRoundInput p i r.input.row r.input.time
      (ReferenceFollowerDownDecoderReplay.preparedOwnObservation r i) rate logged) :
    cut.raw = (AffineBatchDecoder.decodeStep p tr bank r.input.time).2 := by
  have hf := retained_call_fields r i logged cut hi hd hc
  have hdecode := decodeStep_depends_on_current_input p tr
    (currentInputExtension p (currentRoundInput p i r.input.row r.input.time
      (ReferenceFollowerDownDecoderReplay.preparedOwnObservation r i) rate logged))
    logged.downBatch r.input.time hin
  have hraw := hf.2.2.2.2.2.1
  change cut.raw = (AffineBatchDecoder.decodeStep p
    (currentInputExtension p (currentRoundInput p i r.input.row r.input.time
      (ReferenceFollowerDownDecoderReplay.preparedOwnObservation r i) rate logged))
    logged.downBatch r.input.time).2 at hraw
  rw [hb] at hraw
  rw [hb] at hdecode
  exact hraw.trans (congrArg Prod.snd hdecode).symm

private theorem actual_ambiguity_cover
    (hb : ReferenceCollectionPhaseHistory.laterChosen R[b.val].input = true)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (hbirth : ReferenceAssignmentPayloadPersistence.InstallationBirth R[b.val] payload)
    (j : Fin (H).length) (i : Fin (p.m - 1))
    (choice : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hc : (H[j.val].output.preparation.followers.followers i).configuration =
      .ordinary choice memory)
    (hu : choice.status = .unoccupied)
    (B : List (DecoderEntry p)) (hB : completedDownBatch H[j.val] i = some B)
    (hwhole : wholeCurrentBatch p β payload.assignment
      (fromLive p payload.assignment
        (actualLaterHandoverLive rate rewards C_star C_h z payload H)
        (fun _ => false) (fun _ => false)) i payload.sigma (payload.downRecord i) B)
    (hmulti : multipleSolutions p B) :
    ReferenceLiteralSourceDecoderCoverage.S_amb rate rewards C_star C_h z H[j.val].input.time := by
  let live := actualLaterHandoverLive rate rewards C_star C_h z payload H
  let data := fromLive p payload.assignment live (fun _ => false) (fun _ => false)
  let tr := observationTrace p payload.assignment data i
  have hbirthTime := ReferenceAssignmentPayloadChronology.installationBirth_time_eq
    R[b.val] payload hbirth
  have htime := actual_handover_record_time rate rewards C_star C_h z b j
  have hs : payload.sigma.val ≤ H[j.val].input.time.val := by omega
  change ReferenceLiteralSourceDecoderCoverage.literalDownAmbiguityAt
    rate rewards C_star C_h z H[j.val].input.time ∨ _
  left
  refine ⟨H[j.val], i, currentWord p β (payload.downRecord i), B, payload.sigma,
    actualHandoverRecord_sourceDate rate rewards C_star C_h z b j,
    ReferenceLiteralSourceDecoderCoverage.physicalDownCompletedAt_of_completedDownBatch
      H[j.val] i B hB, hs, hmulti, ?_, ?_⟩
  · intro e he
    obtain ⟨hfix, hel, hsample, hword⟩ := hwhole e he
    have hle := actual_completed_batch_dates rate rewards C_star C_h z b hb j i B hB e he
    obtain ⟨k, _, hktime⟩ := actual_handover_record_at_date rate rewards C_star C_h z b
      payload hbirth j e.time hfix hle
    have hsource := actualHandoverRecord_sourceDate rate rewards C_star C_h z b k
    rw [hktime] at hsource
    have hfields := ReferenceLiteralSourceDecoderCoverage.actualRecord_original_fields
      rate rewards C_star C_h z e.time H[k.val] hsource
    have hkt := actual_handover_record_time rate rewards C_star C_h z b k
    have hcalendar := actualLaterHandoverLive_of_actual_record rate rewards C_star C_h z
      payload H e.time (by rw [← hktime]; constructor <;> omega) H[k.val] hsource
    have hinput : (data e.time).input = handoverRoundInput payload H[k.val].input.row e.time :=
      congrArg ActiveRoundActions.LiveRoundData.input hcalendar
    obtain ⟨hdown, hdraw, _, _, _⟩ := (eligible_iff p payload.assignment data i e.time).mp hel
    rw [hinput] at hdown hdraw
    have hrow : H[k.val].input.row = z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) := by
      change H[k.val].input.rows H[k.val].input.selected = _
      rw [hfields.1, hfields.2.1]
    have hsel : ReferenceSelectedAffinePairLaw.selectedChannel p
        ((z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)).2 e.time).1 = some (0, i) := by
      rw [← hrow, ReferenceSelectedAffinePairLaw.selectedChannel_of_down p _ hdown]
      exact congrArg some (congrArg (fun k => (0, k)) hdraw)
    obtain ⟨rv, hrv, _, _, _, _, hawait⟩ :=
      actual_awaited_interval rate rewards C_star C_h z b hb payload hbirth j i choice memory hc hu
        e.time hfix hle hsel
    have hrvEq : rv = H[k.val] := Option.some.inj (hrv.symm.trans hsource)
    have hphysical : ReferenceLiteralSourceDecoderCoverage.physicalAwaitedDownAt H[k.val] i
        (currentWord p β (payload.downRecord i)) := hrvEq ▸ hawait
    have hphysical' := hphysical
    obtain ⟨logged, cut, _, hi, hd, hselected, hstatus, _, _, _, _, _, _, _⟩ := hphysical'
    obtain ⟨previous, previousMemory, hprevious, hpu, _, hls, _⟩ :=
      retained_input_origin H[k.val] i logged hi
    have hin := actual_trace_input rate rewards C_star C_h z b hb payload hbirth k i
      previous previousMemory hprevious hpu hselected
    have hinLog : tr e.time = currentRoundInput p i H[k.val].input.row e.time
        (ReferenceFollowerDownDecoderReplay.preparedOwnObservation H[k.val] i) rate logged := by
      rw [hktime] at hin
      exact hin.trans (by simp only [currentRoundInput, hls])
    have hpositive := positive_of_logged_input rate H[k.val] i logged hi tr e hktime hinLog hel hsample
    have hequation := live_positive_equation p payload.assignment live
      (fun _ => false) (fun _ => false) i e.time hel
    change AffineBatchDecoder.equation (data e.time).input.down.sample
      (data e.time).input.down.word at hequation
    rw [← hsample, hword] at hequation
    refine ⟨hfix, hle, hequation, H[k.val], hsource, hfields.1, hfields.2.1,
      hfields.2.2.1, hfields.2.2.2, ?_, hpositive, ?_⟩
    · have hcoordinates := ReferenceLiteralSourceDecoderCoverage.downPositiveEntry_original_coordinates
        H[k.val] i e hpositive
      rw [hrow, hktime] at hcoordinates
      exact hcoordinates.2
    · exact hphysical
  · exact actual_awaited_interval rate rewards C_star C_h z b hb payload hbirth j i choice memory hc hu

private theorem completed_of_positive_call
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1)) (logged : ReferencePrelaunchFollower.State p rate.eta)
    (cut : ReferenceDownCutOutput p rate)
    (hi : (r.output.followers i).downInput = some logged)
    (hd : (r.output.followers i).down = some cut)
    (hc : cut.rawComparison.isSome = true)
    (tr : AffineBatchDecoder.Trace p) (bank : DecoderState p)
    (hb : logged.downBatch = bank)
    (hin : tr r.input.time = currentRoundInput p i r.input.row r.input.time
      (ReferenceFollowerDownDecoderReplay.preparedOwnObservation r i) rate logged)
    (hel : AffineBatchDecoder.eligible (tr r.input.time))
    (hshort : ¬ bank.pending.length + 1 < AffineBatchDecoder.quota p) :
    completedDownBatch r i = some (bank.pending ++ [AffineBatchDecoder.entry p tr r.input.time]) := by
  have happ : appendedDownBatch r i logged =
      bank.pending ++ [AffineBatchDecoder.entry p tr r.input.time] := by
    unfold appendedDownBatch
    rw [hb]
    simp only [AffineBatchDecoder.positiveAt, currentInputExtension,
      ← hin, hel, ite_true, AffineBatchDecoder.entry]
  apply (completedDownBatch_eq_some_iff r i _).mpr
  refine ⟨logged, cut, hi, hd, hc, ?_, happ⟩
  rw [happ, List.length_append, List.length_singleton]
  omega

private theorem actual_call_raw_and_completion
    (hb : ReferenceCollectionPhaseHistory.laterChosen R[b.val].input = true)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (hbirth : ReferenceAssignmentPayloadPersistence.InstallationBirth R[b.val] payload)
    (j : Fin (H).length) (i : Fin (p.m - 1))
    (choice : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hc : (H[j.val].output.preparation.followers.followers i).configuration =
      .ordinary choice memory)
    (hu : choice.status = .unoccupied)
    (hdown : downSelected p i H[j.val].input.row H[j.val].input.time)
    (logged : ReferencePrelaunchFollower.State p rate.eta) (cut : ReferenceDownCutOutput p rate)
    (hi : (H[j.val].output.followers i).downInput = some logged)
    (hd : (H[j.val].output.followers i).down = some cut)
    (hcomp : cut.rawComparison.isSome = true) (hbank : logged.downBatch = choice.downBatch) :
    let tr := observationTrace p payload.assignment
      (fromLive p payload.assignment (actualLaterHandoverLive rate rewards C_star C_h z payload H)
        (fun _ => false) (fun _ => false)) i
    cut.raw = (AffineBatchDecoder.decodeStep p tr choice.downBatch H[j.val].input.time).2 ∧
      (AffineBatchDecoder.eligible (tr H[j.val].input.time) →
        ¬ choice.downBatch.pending.length + 1 < AffineBatchDecoder.quota p →
        completedDownBatch H[j.val] i = some (choice.downBatch.pending ++
          [AffineBatchDecoder.entry p tr H[j.val].input.time])) := by
  dsimp only
  let data := fromLive p payload.assignment
    (actualLaterHandoverLive rate rewards C_star C_h z payload H) (fun _ => false) (fun _ => false)
  let tr := observationTrace p payload.assignment data i
  have hin := actual_trace_input rate rewards C_star C_h z b hb payload hbirth j i choice memory hc hu hdown
  have hf := retained_call_fields H[j.val] i logged cut hi hd hcomp
  have hinLog : tr H[j.val].input.time = currentRoundInput p i H[j.val].input.row
      H[j.val].input.time (ReferenceFollowerDownDecoderReplay.preparedOwnObservation H[j.val] i)
        rate logged := hin.trans (by simp only [currentRoundInput, hu, hf.2.1])
  refine ⟨compared_call_raw rate H[j.val] i logged cut hi hd hcomp tr choice.downBatch hbank hinLog, ?_⟩
  intro hel hshort
  exact completed_of_positive_call rate H[j.val] i logged cut hi hd hcomp tr choice.downBatch hbank hinLog hel hshort

private theorem awaiting_service_failure_cases
    (beta : ℝ) (a : ActiveRoundActions.Assignment p.m p.K)
    (data : Fin p.T → RoundData p a) (i : Fin (p.m - 1)) (fixing : Fin p.T)
    (M : Down p beta) (bank : DecoderState p) (old : ℕ) (t : Fin p.T)
    (h : (serviceStep p beta a data i fixing M (initial p bank old) t).phase = .failedFalse ∨
      (serviceStep p beta a data i fixing M (initial p bank old) t).phase = .failedAmbiguous) :
    let tr := observationTrace p a data i
    let updated : LocalState p := ⟨(AffineBatchDecoder.decodeStep p tr bank t).1, old, .awaitingDown⟩
    AffineBatchDecoder.eligible (tr t) ∧
      ¬ bank.pending.length + 1 < AffineBatchDecoder.quota p ∧
      ((afterDecision p beta a data i fixing M updated t
        (bank.pending ++ [AffineBatchDecoder.entry p tr t])
        (AffineBatchDecoder.decodeStep p tr bank t).2).phase = .failedFalse ∨
      (afterDecision p beta a data i fixing M updated t
        (bank.pending ++ [AffineBatchDecoder.entry p tr t])
        (AffineBatchDecoder.decodeStep p tr bank t).2).phase = .failedAmbiguous) := by
  dsimp only
  by_cases hel : AffineBatchDecoder.eligible (observationTrace p a data i t)
  · simp only [serviceStep, initial, hel, ite_true] at h
    by_cases hs : bank.pending.length + 1 < AffineBatchDecoder.quota p
    · simp only [receiverStep, hs, ite_true] at h
      rcases h with h | h <;> cases h
    · refine ⟨hel, hs, ?_⟩
      simpa only [receiverStep, hs, ite_false] using h
  · simp only [serviceStep, initial, hel, ite_false] at h
    rcases h with h | h <;> cases h

private theorem actual_after_decision_failure_cover
    (hb : ReferenceCollectionPhaseHistory.laterChosen R[b.val].input = true)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (hbirth : ReferenceAssignmentPayloadPersistence.InstallationBirth R[b.val] payload)
    (j : Fin (H).length) (i : Fin (p.m - 1))
    (choice : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hc : (H[j.val].output.preparation.followers.followers i).configuration =
      .ordinary choice memory) (hu : choice.status = .unoccupied)
    (cut : ReferenceDownCutOutput p rate) (hd : (H[j.val].output.followers i).down = some cut)
    (old : ℕ) (B : List (DecoderEntry p)) (hB : completedDownBatch H[j.val] i = some B)
    (s : LocalState p) (hs : s.phase = .awaitingDown) (hstart : s.acceptedStart = old)
    (raw : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p))) (hraw : cut.raw = raw)
    (hfalse : falseDecision p β (payload.downRecord i) old H[j.val].input.time cut.raw ↔
      wrongUniqueAccepted cut)
    (hfailure :
      let data := fromLive p payload.assignment
        (actualLaterHandoverLive rate rewards C_star C_h z payload H) (fun _ => false) (fun _ => false)
      (afterDecision p β payload.assignment data i payload.sigma (payload.downRecord i)
        s H[j.val].input.time B raw).phase = .failedFalse ∨
      (afterDecision p β payload.assignment data i payload.sigma (payload.downRecord i)
        s H[j.val].input.time B raw).phase = .failedAmbiguous) :
    ReferenceLiteralSourceDecoderCoverage.S_false rate rewards C_star C_h z H[j.val].input.time ∨
      ReferenceLiteralSourceDecoderCoverage.S_amb rate rewards C_star C_h z H[j.val].input.time := by
  let data := fromLive p payload.assignment
    (actualLaterHandoverLive rate rewards C_star C_h z payload H) (fun _ => false) (fun _ => false)
  rcases hfailure with hf | ha
  · have hcause := afterDecision_false_cause p β payload.assignment data i payload.sigma
      (payload.downRecord i) s H[j.val].input.time B raw hs hf
    rw [hstart, ← hraw] at hcause
    exact Or.inl (actual_later_handover_wrongUniqueAccepted_mem_S_false
      rate rewards C_star C_h z b j i cut hd (hfalse.mp hcause))
  · have hcause := afterDecision_ambiguity_cause p β payload.assignment data i payload.sigma
      (payload.downRecord i) s H[j.val].input.time B raw hs ha
    exact Or.inr (actual_ambiguity_cover rate rewards C_star C_h z b hb payload hbirth j i
      choice memory hc hu B hB hcause.2.1 hcause.2.2.2)

/-- A genuine local awaiting service failure, evaluated on the actual
incoming bank/register and the complete accepted physical input, is covered
on the same source date. This is a one-step result; identifying the incoming
state with a replay of all strict predecessors is a separate assertion. -/
public theorem actual_later_handover_awaiting_service_failure_coverage
    (hb : ReferenceCollectionPhaseHistory.laterChosen R[b.val].input = true)
    (i : Fin (p.m - 1)) :
    ∃ (payload : ReferenceActivePhysicalStep.Payload rate)
      (before : ReferencePrelaunchFollower.State p rate.eta)
      (beforeMemory : ActiveFollowerLifecycle.LocalMemory p),
      ReferenceAssignmentPayloadPersistence.InstallationBirth R[b.val] payload ∧
      R[b.val].input.state.followers i = .ordinary before beforeMemory ∧
      before.status = .unoccupied ∧
      ReferencePrelaunchFollower.acceptedStart before < (payload.downRecord i).val.sigma ∧
      ∀ j : Fin (H).length,
        ∃ (choice : ReferencePrelaunchFollower.State p rate.eta)
          (memory : ActiveFollowerLifecycle.LocalMemory p),
          (H[j.val].output.preparation.followers.followers i).configuration =
            .ordinary choice memory ∧
          (choice.status = .unoccupied →
            let live := actualLaterHandoverLive rate rewards C_star C_h z payload H
            let data := fromLive p payload.assignment live (fun _ => false) (fun _ => false)
            let incoming := initial p choice.downBatch
              (ReferencePrelaunchFollower.acceptedStart before)
            let outgoing := serviceStep p β payload.assignment data i payload.sigma
              (payload.downRecord i) incoming H[j.val].input.time
            outgoing.phase = .failedFalse ∨ outgoing.phase = .failedAmbiguous →
              ReferenceLiteralSourceDecoderCoverage.S_false rate rewards C_star C_h z H[j.val].input.time ∨
              ReferenceLiteralSourceDecoderCoverage.S_amb rate rewards C_star C_h z H[j.val].input.time) := by
  obtain ⟨payload, before, beforeMemory, hbirth, hbefore, huBefore, hstrict, dates⟩ :=
    actual_later_handover_awaiting_calls rate rewards C_star C_h z b hb i
  refine ⟨payload, before, beforeMemory, hbirth, hbefore, huBefore, hstrict, ?_⟩
  intro j
  obtain ⟨_, choice, memory, _, _, hc, hawait⟩ := dates j
  refine ⟨choice, memory, hc, ?_⟩
  intro hu
  dsimp only
  let live := actualLaterHandoverLive rate rewards C_star C_h z payload H
  let data := fromLive p payload.assignment live (fun _ => false) (fun _ => false)
  let tr := observationTrace p payload.assignment data i
  let s := initial p choice.downBatch (ReferencePrelaunchFollower.acceptedStart before)
  intro hfailed
  change (serviceStep p β payload.assignment data i payload.sigma
    (payload.downRecord i) s H[j.val].input.time).phase = .failedFalse ∨
    (serviceStep p β payload.assignment data i payload.sigma
    (payload.downRecord i) s H[j.val].input.time).phase = .failedAmbiguous at hfailed
  obtain ⟨hel, hshort, hdecision⟩ := awaiting_service_failure_cases β payload.assignment data i
    payload.sigma (payload.downRecord i) choice.downBatch
    (ReferencePrelaunchFollower.acceptedStart before) H[j.val].input.time hfailed
  have hbirthTime := ReferenceAssignmentPayloadChronology.installationBirth_time_eq
    R[b.val] payload hbirth
  have ht := actual_handover_record_time rate rewards C_star C_h z b j
  have hcalendar := actualLaterHandoverLive_of_actual_record rate rewards C_star C_h z payload H
    H[j.val].input.time (by constructor <;> have := j.isLt <;> omega) H[j.val]
    (actualHandoverRecord_sourceDate rate rewards C_star C_h z b j)
  obtain ⟨hslot, hdraw, _, _, _⟩ := (eligible_iff p payload.assignment data i H[j.val].input.time).mp hel
  have hinp : (data H[j.val].input.time).input =
      handoverRoundInput payload H[j.val].input.row H[j.val].input.time :=
    congrArg ActiveRoundActions.LiveRoundData.input hcalendar
  rw [hinp] at hslot hdraw
  have hdown : downSelected p i H[j.val].input.row H[j.val].input.time := ⟨hslot, hdraw⟩
  obtain ⟨logged, cut, hi, hd, hbank, _, hcomp, _, _, hfalse⟩ := (hawait hu).2 hdown
  obtain ⟨hraw, hcompletion⟩ := actual_call_raw_and_completion rate rewards C_star C_h z b hb
    payload hbirth j i choice memory hc hu hdown logged cut hi hd hcomp hbank
  let B := choice.downBatch.pending ++ [AffineBatchDecoder.entry p tr H[j.val].input.time]
  let updated : LocalState p := ⟨(AffineBatchDecoder.decodeStep p tr
    choice.downBatch H[j.val].input.time).1,
    ReferencePrelaunchFollower.acceptedStart before, .awaitingDown⟩
  have hB : completedDownBatch H[j.val] i = some B := hcompletion hel hshort
  change (afterDecision p β payload.assignment data i payload.sigma (payload.downRecord i)
    updated H[j.val].input.time B
    (AffineBatchDecoder.decodeStep p tr choice.downBatch H[j.val].input.time).2).phase = .failedFalse ∨
    (afterDecision p β payload.assignment data i payload.sigma (payload.downRecord i)
    updated H[j.val].input.time B
    (AffineBatchDecoder.decodeStep p tr choice.downBatch H[j.val].input.time).2).phase = .failedAmbiguous at hdecision
  exact actual_after_decision_failure_cover rate rewards C_star C_h z b hb payload hbirth j i
    choice memory hc hu cut hd (ReferencePrelaunchFollower.acceptedStart before) B hB
    updated rfl rfl _ hraw hfalse hdecision

/-- Literal strict-past safety excludes both local failure phases at every
earlier actual awaiting service. The current diagnostic gates are consumed
only in their accepted forward direction. This does not identify the local
incoming projection with the full stopped replay. -/
public theorem actual_later_handover_strict_predecessor_failure_exclusion
    (hb : ReferenceCollectionPhaseHistory.laterChosen R[b.val].input = true)
    (i : Fin (p.m - 1)) :
    ∃ (payload : ReferenceActivePhysicalStep.Payload rate)
      (before : ReferencePrelaunchFollower.State p rate.eta)
      (beforeMemory : ActiveFollowerLifecycle.LocalMemory p),
      ReferenceAssignmentPayloadPersistence.InstallationBirth R[b.val] payload ∧
      R[b.val].input.state.followers i = .ordinary before beforeMemory ∧
      before.status = .unoccupied ∧
      ReferencePrelaunchFollower.acceptedStart before < (payload.downRecord i).val.sigma ∧
      ∀ j : Fin (H).length,
        ReferencePostReplacementCollectionHandoverSourcePrefix.literalStoppedHTaskSupport
          rate rewards C_star C_h H[j.val].input.time i z →
        z ∈ ReferencePostReplacementCollectionHandoverSourcePrefix.diagnosticHTaskSupport
            rate rewards C_star C_h H[j.val].input.time i ∧
          ∀ k : Fin (H).length, k.val < j.val →
            ∃ (choice : ReferencePrelaunchFollower.State p rate.eta)
              (memory : ActiveFollowerLifecycle.LocalMemory p),
              (H[k.val].output.preparation.followers.followers i).configuration =
                .ordinary choice memory ∧
              (choice.status = .unoccupied →
                let data := fromLive p payload.assignment
                  (actualLaterHandoverLive rate rewards C_star C_h z payload H)
                  (fun _ => false) (fun _ => false)
                let incoming := initial p choice.downBatch
                  (ReferencePrelaunchFollower.acceptedStart before)
                let outgoing := serviceStep p β payload.assignment data i payload.sigma
                  (payload.downRecord i) incoming H[k.val].input.time
                outgoing.phase ≠ .failedFalse ∧ outgoing.phase ≠ .failedAmbiguous) := by
  obtain ⟨payload, before, beforeMemory, hbirth, hbefore, hu, hstrict, dates⟩ :=
    actual_later_handover_awaiting_service_failure_coverage rate rewards C_star C_h z b hb i
  refine ⟨payload, before, beforeMemory, hbirth, hbefore, hu, hstrict, ?_⟩
  intro j hsupport
  refine ⟨ReferencePostReplacementCollectionHandoverSourcePrefix.literalStoppedHTaskSupport_mem_diagnostic
    rate rewards C_star C_h H[j.val].input.time i z hsupport, ?_⟩
  intro k hkj
  obtain ⟨choice, memory, hc, hcover⟩ := dates k
  refine ⟨choice, memory, hc, ?_⟩
  intro hchoice
  have hj := actual_handover_record_time rate rewards C_star C_h z b j
  have hk := actual_handover_record_time rate rewards C_star C_h z b k
  have hlt : H[k.val].input.time.val < H[j.val].input.time.val := by omega
  have hsafe := hsupport.2.1 H[k.val].input.time hlt
  change ¬ (ReferenceLiteralSourceDecoderCoverage.S_false
    rate rewards C_star C_h z H[k.val].input.time ∨
    ReferenceLiteralSourceDecoderCoverage.S_amb rate rewards C_star C_h z H[k.val].input.time) at hsafe
  exact ⟨fun h => hsafe (hcover hchoice (Or.inl h)),
    fun h => hsafe (hcover hchoice (Or.inr h))⟩

private theorem awaiting_service_accepted_cause
    (beta : ℝ) (a : ActiveRoundActions.Assignment p.m p.K)
    (data : Fin p.T → RoundData p a) (i : Fin (p.m - 1)) (fixing : Fin p.T)
    (M : Down p beta) (bank : DecoderState p) (old : ℕ) (t : Fin p.T)
    (h : (serviceStep p beta a data i fixing M (initial p bank old) t).phase =
      .acceptedUnconfirmed) :
    AffineBatchDecoder.eligible (observationTrace p a data i t) ∧
      (AffineBatchDecoder.decodeStep p (observationTrace p a data i) bank t).2 =
        some (currentWord p beta M) ∧
      OrdinaryMessageCodec.acceptDown (AffineBatchDecoder.codecParams p beta)
        old (WaitedWordWindow.sourceRound t) M := by
  by_cases hel : AffineBatchDecoder.eligible (observationTrace p a data i t)
  · simp only [serviceStep, initial, hel, ite_true] at h
    by_cases hs : bank.pending.length + 1 < AffineBatchDecoder.quota p
    · simp only [receiverStep, hs, ite_true] at h
      cases h
    · simp only [receiverStep, hs, ite_false] at h
      cases hp : parseOutput p beta
          (AffineBatchDecoder.decodeStep p (observationTrace p a data i) bank t).2 with
      | none =>
          simp only [afterDecision, hp] at h
          split at h <;> cases h
      | some other =>
          simp only [afterDecision, hp] at h
          split at h
          · rename_i ha
            split at h
            · rename_i he
              subst other
              exact ⟨hel, (ReferenceFirstLiveHandoverPhaseReplay.parseOutput_eq_some_iff beta M _).mp hp, ha⟩
            · cases h
          · cases h
  · simp only [serviceStep, initial, hel, ite_false] at h
    cases h

private theorem current_decode_raw_of_input
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1)) (choice : ReferencePrelaunchFollower.State p rate.eta)
    (tr : AffineBatchDecoder.Trace p)
    (hin : tr r.input.time = currentRoundInput p i r.input.row r.input.time
      (ReferenceFollowerDownDecoderReplay.preparedOwnObservation r i) rate choice)
    (raw : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p)))
    (hraw : (AffineBatchDecoder.decodeStep p tr choice.downBatch r.input.time).2 = raw) :
    (currentDecodeStep p i r.input.row r.input.time
      (ReferenceFollowerDownDecoderReplay.preparedOwnObservation r i) rate choice).2 = raw := by
  have he := decodeStep_depends_on_current_input p tr
    (currentInputExtension p (currentRoundInput p i r.input.row r.input.time
      (ReferenceFollowerDownDecoderReplay.preparedOwnObservation r i) rate choice))
    choice.downBatch r.input.time hin
  exact (congrArg Prod.snd he).symm.trans hraw

private theorem actual_choice_missing
    (hb : ReferenceCollectionPhaseHistory.laterChosen R[b.val].input = true)
    (j : Fin (H).length) (i : Fin (p.m - 1))
    (selected : ReferenceActivePhysicalStep.Selection H[j.val].input)
    (hs : H[j.val].output.preparation.coordinator.selection = some selected)
    (choice : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hc : (H[j.val].output.preparation.followers.followers i).configuration = .ordinary choice memory)
    (hu : choice.status = .unoccupied) : i ∈ selected.view.pendingAtChoice := by
  obtain ⟨_, _, dates⟩ := actual_later_handover_snapshot rewards C_star C_h z b hb
  obtain ⟨s, states, memories, hs', _, hconfigs, _, _, _, hmissing⟩ := dates j
  have he := Option.some.inj (hs'.symm.trans hs)
  have hc' := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj ((hconfigs i).symm.trans hc)
  exact he ▸ hmissing i (hc'.1 ▸ hu)

private theorem current_down_branch
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (selected : ReferenceActivePhysicalStep.Selection r.input)
    (hs : r.output.preparation.coordinator.selection = some selected)
    (payload : ReferenceActivePhysicalStep.Payload rate) (hp : selected.view.payload = payload)
    (i : Fin (p.m - 1)) (choice : ReferencePrelaunchFollower.State p rate.eta)
    (hdown : downSelected p i r.input.row r.input.time) (hmissing : i ∈ selected.view.pendingAtChoice)
    (hraw : (currentDecodeStep p i r.input.row r.input.time
      (ReferenceFollowerDownDecoderReplay.preparedOwnObservation r i) rate choice).2 =
      some (currentWord p β (payload.downRecord i)))
    (ha : OrdinaryMessageCodec.acceptDown (ReferencePrelaunchFollower.codecParams p rate.eta)
      (ReferencePrelaunchFollower.acceptedStart choice) (r.input.time.val + 1) (payload.downRecord i)) :
    downSelected p i r.input.row r.input.time ∧
      (currentDecodeStep p i r.input.row r.input.time
        (ReferenceFollowerDownDecoderReplay.preparedOwnObservation r i) rate choice).2 =
        expectedDownFlatWord r.output.preparation.coordinator.downView i r.input.row r.input.time ∧
      ordinaryLocalAcceptanceTest p rate r.input.time choice
        (ordinaryParse p rate (currentDecodeStep p i r.input.row r.input.time
          (ReferenceFollowerDownDecoderReplay.preparedOwnObservation r i) rate choice).2) := by
  have hv : r.output.preparation.coordinator.downView = some selected.view :=
    congrArg (Option.map ReferenceActivePhysicalStep.Selection.view) hs
  have he := selected.expected_down_word i ⟨hdown.1, hdown.2, hmissing⟩
  refine ⟨hdown, ?_, ?_⟩
  · rw [hraw, hv, he, hp]
    rfl
  · rw [hraw]
    change ordinaryLocalAcceptanceTest p rate r.input.time choice
      (parseOutput p β (some (currentWord p β (payload.downRecord i))))
    rw [parseOutput_currentWord p β (payload.downRecord i)]
    exact ha

private theorem complete_current_down_output
    (k : Fin (R).length) (i : Fin (p.m - 1))
    (choice : ReferencePrelaunchFollower.State p rate.eta) (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hc : ((R[k.val]).output.preparation.followers.followers i).configuration = .ordinary choice memory)
    (hu : choice.status = .unoccupied)
    (hbranch : downSelected p i R[k.val].input.row R[k.val].input.time ∧
      (currentDecodeStep p i R[k.val].input.row R[k.val].input.time
        (ReferenceFollowerDownDecoderReplay.preparedOwnObservation R[k.val] i) rate choice).2 =
        expectedDownFlatWord R[k.val].output.preparation.coordinator.downView i R[k.val].input.row R[k.val].input.time ∧
      ordinaryLocalAcceptanceTest p rate R[k.val].input.time choice
        (ordinaryParse p rate (currentDecodeStep p i R[k.val].input.row R[k.val].input.time
          (ReferenceFollowerDownDecoderReplay.preparedOwnObservation R[k.val] i) rate choice).2)) :
    ∃ selected : ReferenceActivePhysicalStep.Selection R[k.val].input,
      R[k.val].output.preparation.coordinator.selection = some selected ∧
      ∃ next nextMemory, R[k.val].output.next.followers i = .ordinary next nextMemory ∧
        next.lastDown = some (selected.view.payload.downRecord i) := by
  obtain ⟨selected, hs, _, _, _, _, _, _, _, _, _, _, _, _, htail⟩ :=
    ReferenceCompleteAcceptedCurrentDownForward.complete_ordinary_unoccupied_accepted_current_down_forward
      (rate := rate) rewards C_star C_h z k i choice memory hc hu hbranch
  rcases htail with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hnext⟩
  exact ⟨selected, hs, _, _, hnext, rfl⟩

/-- A current acceptance by the local awaiting service is an actual checked
physical installation of that same record. Confirmation still uses the
incoming unoccupied snapshot, so it cannot occur on this acceptance date. -/
public theorem actual_later_handover_current_acceptance_output
    (hb : ReferenceCollectionPhaseHistory.laterChosen R[b.val].input = true)
    (i : Fin (p.m - 1)) :
    ∃ (payload : ReferenceActivePhysicalStep.Payload rate)
      (before : ReferencePrelaunchFollower.State p rate.eta)
      (beforeMemory : ActiveFollowerLifecycle.LocalMemory p),
      ReferenceAssignmentPayloadPersistence.InstallationBirth R[b.val] payload ∧
      R[b.val].input.state.followers i = .ordinary before beforeMemory ∧
      before.status = .unoccupied ∧
      ReferencePrelaunchFollower.acceptedStart before < (payload.downRecord i).val.sigma ∧
      ∀ j : Fin (H).length,
        ∃ (choice : ReferencePrelaunchFollower.State p rate.eta)
          (memory : ActiveFollowerLifecycle.LocalMemory p),
          (H[j.val].output.preparation.followers.followers i).configuration =
            .ordinary choice memory ∧
          (choice.status = .unoccupied →
            let data := fromLive p payload.assignment
              (actualLaterHandoverLive rate rewards C_star C_h z payload H)
              (fun _ => false) (fun _ => false)
            let incoming := initial p choice.downBatch
              (ReferencePrelaunchFollower.acceptedStart before)
            (serviceStep p β payload.assignment data i payload.sigma (payload.downRecord i)
              incoming H[j.val].input.time).phase = .acceptedUnconfirmed →
            ¬ physicalConfirmation p payload.assignment data i H[j.val].input.time ∧
              ∃ (next : ReferencePrelaunchFollower.State p rate.eta)
                (nextMemory : ActiveFollowerLifecycle.LocalMemory p),
                H[j.val].output.next.followers i = .ordinary next nextMemory ∧
                next.lastDown = some (payload.downRecord i)) := by
  obtain ⟨payload, before, beforeMemory, hbirth, hbefore, huBefore, hstrict, dates⟩ :=
    actual_later_handover_awaiting_calls rate rewards C_star C_h z b hb i
  refine ⟨payload, before, beforeMemory, hbirth, hbefore, huBefore, hstrict, ?_⟩
  intro j
  obtain ⟨selected, choice, memory, hselection, hpayload, hc, hawait⟩ := dates j
  refine ⟨choice, memory, hc, ?_⟩
  intro hu
  dsimp only
  let live := actualLaterHandoverLive rate rewards C_star C_h z payload H
  let data := fromLive p payload.assignment live (fun _ => false) (fun _ => false)
  let tr := observationTrace p payload.assignment data i
  intro haccepted
  obtain ⟨hel, hraw, ha⟩ := awaiting_service_accepted_cause β payload.assignment data i payload.sigma
    (payload.downRecord i) choice.downBatch (ReferencePrelaunchFollower.acceptedStart before)
    H[j.val].input.time haccepted
  have hsnapshot := actual_choice_snapshot rate rewards C_star C_h z b hb payload hbirth j i choice memory hc
  refine ⟨?_, ?_⟩
  · intro hconfirm
    have hstatus : (data H[j.val].input.time).snapshot.status i = .unoccupied := hsnapshot.trans hu
    have ho := ActiveRoundActions.confirmation_implies_occupied p.two_le_m
      (data H[j.val].input.time).snapshot (data H[j.val].input.time).input
      (data H[j.val].input.time).rewards i hconfirm
    rcases ho with ho | ho <;> rw [hstatus] at ho <;> cases ho
  · obtain ⟨hslot, hdraw, _, _, _⟩ := (eligible_iff p payload.assignment data i H[j.val].input.time).mp hel
    have hbirthTime := ReferenceAssignmentPayloadChronology.installationBirth_time_eq R[b.val] payload hbirth
    have ht := actual_handover_record_time rate rewards C_star C_h z b j
    have hcalendar := actualLaterHandoverLive_of_actual_record rate rewards C_star C_h z payload H
      H[j.val].input.time (by constructor <;> have := j.isLt <;> omega) H[j.val]
      (actualHandoverRecord_sourceDate rate rewards C_star C_h z b j)
    have hinp : (data H[j.val].input.time).input =
        handoverRoundInput payload H[j.val].input.row H[j.val].input.time :=
      congrArg ActiveRoundActions.LiveRoundData.input hcalendar
    rw [hinp] at hslot hdraw
    have hdown : downSelected p i H[j.val].input.row H[j.val].input.time := ⟨hslot, hdraw⟩
    have hin := actual_trace_input rate rewards C_star C_h z b hb payload hbirth j i choice memory hc hu hdown
    have hrawPhysical : (currentDecodeStep p i H[j.val].input.row H[j.val].input.time
        (ReferenceFollowerDownDecoderReplay.preparedOwnObservation H[j.val] i) rate choice).2 =
        some (currentWord p β (payload.downRecord i)) :=
      current_decode_raw_of_input rate H[j.val] i choice tr hin _ hraw
    have hmissing := actual_choice_missing rate rewards C_star C_h z b hb j i selected hselection choice memory hc hu
    obtain ⟨hk, hj⟩ := actual_handover_record_index rate rewards C_star C_h z b j
    have haChoice : OrdinaryMessageCodec.acceptDown (ReferencePrelaunchFollower.codecParams p rate.eta)
        (ReferencePrelaunchFollower.acceptedStart choice) (H[j.val].input.time.val + 1)
        (payload.downRecord i) := by
      rw [(hawait hu).1]
      exact ha
    have hbranch := current_down_branch rate H[j.val] selected hselection payload hpayload i choice hdown
      hmissing hrawPhysical haChoice
    have hfwd := complete_current_down_output rate rewards C_star C_h z ⟨b.val + j.val, hk⟩
    rw [← hj] at hfwd
    obtain ⟨selected', hs', next, nextMemory, hnext, hlast⟩ := hfwd i choice memory hc hu hbranch
    have he := Option.some.inj (hs'.symm.trans hselection)
    have hp : selected'.view.payload = payload := (congrArg (fun s => s.view.payload) he).trans hpayload
    refine ⟨next, nextMemory, hnext, ?_⟩
    exact hlast.trans (congrArg (fun P => some (P.downRecord i)) hp)

end AwaitedCalls

end Bandits.Support.ReferencePostReplacementCollectionHandoverStoppedFailureCoverage

end
