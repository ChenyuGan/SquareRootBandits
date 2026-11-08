/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstReplacementCollectionStoppedPureUpQuota
public import Bandits.Support.ReferenceCompleteSuffixFollowerPreservation

import Mathlib.Data.List.TakeWhile
import Lean.Elab.Tactic.Omega

/-!
# Actual OLD DOWN sender at the first replacement collection

Sources: `sources/zip4/manuscript/06_interruptions.tex:246-349,477-481`,
`sources/zip4/manuscript/05_binary_transport.tex:20-55,180-239`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:92-157`.

Sender assertions use the literal prefix before the first retained physical
failure. A raw current word is a separate antecedent for reception, never an
input to sender production. These are internal source-construction results.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions

namespace Bandits.Support.ReferenceFirstReplacementCollectionOldDownSenderReadiness

variable {p : Parameters} {rate : ReferenceActivePhysicalStep.RateInput p}

theorem parse_stored_word (payload : ReferenceActivePhysicalStep.Payload rate)
    (i : Fin (p.m - 1)) :
    ReferenceDownReception.ordinaryParse p rate
      (some (CoordinatorLocalArmChoice.storedDownFlatWord payload i)) =
      some (payload.downRecord i) := by
  unfold ReferenceDownReception.ordinaryParse CoordinatorLocalArmChoice.storedDownFlatWord
  change OrdinaryMessageCodec.parseDown (ReferencePrelaunchFollower.codecParams p rate.eta)
    (some ((OrdinaryMessageCodec.wordEquivFlat _).symm
      ((OrdinaryMessageCodec.wordEquivFlat _) (payload.downWord i)))) = _
  exact (congrArg (fun word => OrdinaryMessageCodec.parseDown
    (ReferencePrelaunchFollower.codecParams p rate.eta) (some word))
      ((OrdinaryMessageCodec.wordEquivFlat _).symm_apply_apply
        (payload.downWord i))).trans (payload.parseDown_downWord i)

/-- An actual ordinary OLD choice cannot follow an acceptance of this DOWN. -/
theorem no_earlier_retained_down
    {initial final : ReferenceActivePhysicalStep.State p rate}
    {records : List (ReferenceCompletePhysicalHistory.RoundRecord p rate)}
    (chain : ReferenceActivePhysicalHorizon.Connected initial records final)
    (a : Fin records.length) (i : Fin (p.m - 1))
    (M : OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (choice : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hc : (ReferenceFollowerFixedReply.actualChoice (records.get a) i).configuration =
      .ordinary choice memory)
    (hold : ReferencePrelaunchFollower.acceptedStart choice < M.val.sigma) :
    ∀ b : Fin records.length, b.val < a.val →
      ¬ ReferenceAcceptedUpFollowerHistory.RetainedDown (records.get b) i M := by
  intro b hba hretained
  obtain ⟨before, beforeMemory, hbefore, hreply, _⟩ :=
    ReferenceFollowerReplyChronology.record_input_to_choice (records.get a) i choice memory hc
  have hstart := ReferenceFollowerReplyChronology.acceptedStart_eq_of_reply_eq hreply
  have hprefix := ReferenceFollowerReplyChronology.connected_take_to_input chain a.val a.isLt
  have hb : b.val < (records.take a.val).length := by
    simp only [List.length_take]
    exact lt_min hba b.isLt
  obtain ⟨after, afterMemory, hafter, hbound⟩ :=
    ReferenceFollowerReplyChronology.connected_output_chronology hprefix i
      before beforeMemory hbefore b.val hb
  rw [List.getElem_take] at hafter
  obtain ⟨_, _, _, _, hafterStart⟩ :=
    ReferenceFollowerReplyChronology.record_appliedDown_strict (records.get b) i M.val.sigma
      (ReferenceAcceptedUpFollowerHistory.retainedDown_appliedDown hretained)
      after afterMemory hafter
  omega

/-- Absence of physical failure propagates ordinary coordinator input locally.
The first detecting record is excluded by the inclusive prefix hypothesis. -/
theorem prefix_coordinator_ne_dagger
    (records : List (ReferenceCompletePhysicalHistory.RoundRecord p rate))
    (Z : ℕ → ReferenceActivePhysicalStep.State p rate)
    (hlinks : ∀ a : Fin records.length,
      (records.get a).input.state = Z a.val ∧
      (records.get a).output.next = Z (a.val + 1))
    (hzero : (Z 0).coordinator ≠ .dagger)
    (a : Fin records.length)
    (hfailure : ∀ r ∈ records.take (a.val + 1),
      ¬ ReferenceFirstReplacementCollectionStoppedPureUpQuota.physicalFailureAt r) :
    ∀ j : ℕ, j ≤ a.val + 1 → (Z j).coordinator ≠ .dagger := by
  intro j hj
  induction j with
  | zero => exact hzero
  | succ j ih =>
      have hjr : j < records.length := by omega
      let q : Fin records.length := ⟨j, hjr⟩
      have hbefore : (records.get q).input.state.coordinator ≠ .dagger := by
        rw [(hlinks q).1]
        exact ih (by omega)
      intro hdagger
      have hafter : (records.get q).output.next.coordinator = .dagger := by
        rw [(hlinks q).2]
        exact hdagger
      obtain ⟨reason, hreason⟩ :=
        ReferenceFirstReplacementCollectionPureUpWindowCut.first_dagger_record_failure
          (records.get q) hbefore hafter
      have hmem : records.get q ∈ records.take (a.val + 1) := by
        apply List.mem_take_iff_getElem.mpr
        exact ⟨j, lt_min (by omega) hjr, rfl⟩
      exact hfailure _ hmem (Or.inl ⟨reason, hreason⟩)

/-- The actual executed-offer split and CHOICE chronology exclude earlier UP
acceptances. The caller must supply a connected local interval and its actual
choices; the source theorem below constructs both. -/
theorem old_choice_not_mem_accepted_labels
    {initial final : ReferenceActivePhysicalStep.State p rate}
    {records : List (ReferenceCompletePhysicalHistory.RoundRecord p rate)}
    (chain : ReferenceActivePhysicalHorizon.Connected initial records final)
    (a : Fin records.length) (i : Fin (p.m - 1))
    (M : OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (choice : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hc : (ReferenceFollowerFixedReply.actualChoice (records.get a) i).configuration =
      .ordinary choice memory)
    (hold : ReferencePrelaunchFollower.acceptedStart choice < M.val.sigma)
    (hchoices : ∀ b : Fin records.length, ∃ state mem,
      (ReferenceFollowerFixedReply.actualChoice (records.get b) i).configuration =
        .ordinary state mem)
    (hphysical : ∀ b : Fin records.length,
      ReferenceActivePhysicalStep.upSenderIndex (records.get b).input = i →
      ∀ (t : ReferenceCollectionPhaseHistory.Tail (records.get b).input)
        (started : ReferenceActivePhysicalStep.Ledger rate),
      ReferenceCollectionPhaseHistory.executedTail (records.get b).input = some t →
      t.reception = some (started, ReferenceActivePhysicalStep.receiveUp
        (ReferenceActivePhysicalStep.prepare (records.get b).input) started) →
      PublicDiscreteDraws.slotDraw ((records.get b).input.row.2 (records.get b).input.time).1 =
        PublicDiscreteDraws.upSlot →
      ∃ offered offerMem offer,
        ((records.get b).output.preparation.followers.followers
          (ReferenceActivePhysicalStep.upSenderIndex (records.get b).input)).configuration =
            .ordinary offered offerMem ∧
        ActiveFollowerQueueOperation.checkedUpOffer rate.eta
          (ReferenceActivePhysicalStep.upSenderIndex (records.get b).input)
          (records.get b).input.row
          ((records.get b).input.state.activations
            (ReferenceActivePhysicalStep.upSenderIndex (records.get b).input))
          (records.get b).input.time offered = .offer offer ∧
        (CoordinatorCollectionLedger.acceptUpCheck started
          (ReferenceActivePhysicalStep.upSenderIndex (records.get b).input) offer = false ∨
          offered.lastDown = some M)) :
    i ∉ (ReferenceCollectionPhaseHistory.acceptedLabels (records.take a.val)).toFinset := by
  intro hmem
  rw [List.mem_toFinset, ReferenceCollectionPhaseHistory.acceptedLabels,
    List.mem_filterMap] at hmem
  obtain ⟨r, hr, hlabel⟩ := hmem
  obtain ⟨b, hb, heq⟩ := List.mem_take_iff_getElem.mp hr
  have hba : b < a.val := (lt_min_iff.mp hb).1
  have hbr : b < records.length := (lt_min_iff.mp hb).2
  let q : Fin records.length := ⟨b, hbr⟩
  obtain ⟨state, mem, hs⟩ := hchoices q
  have hchrono := (ReferenceFollowerReplyChronology.connected_choice_chronology chain i
    b a.val hbr a.isLt (by omega) state choice mem memory hs hc).1
  obtain ⟨U, hU⟩ := ReferenceCollectionPhaseHistory.acceptedLabel_witness hlabel
  have hU' : ReferenceCollectionPhaseHistory.AcceptedUp (records.get q).input i U := by
    simpa only [q, List.get_eq_getElem, heq] using hU
  have hUcopy := hU'
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hindex⟩ := hUcopy
  exact ReferenceFirstReplacementCollectionUpOfferCut.accepted_up_excludes_strictly_older_choice
    (records.get q) i M state mem hs (lt_of_le_of_lt hchrono hold) U hU'
      (hphysical q hindex.symm)

/-- An ordinary input with no retained coordinator failure has an actual
successful dispatch selection. -/
theorem selection_exists_of_no_failure
    (r : ReferenceCompletePhysicalHistory.RoundRecord p rate)
    (hbefore : r.input.state.coordinator ≠ .dagger)
    (hfailure : ¬ ReferenceFirstReplacementCollectionStoppedPureUpQuota.physicalFailureAt r) :
    ∃ selected : ReferenceActivePhysicalStep.Selection r.input,
      r.output.preparation.coordinator.selection = some selected := by
  classical
  have hp : r.output.preparation = ReferenceActivePhysicalStep.prepare r.input := by
    rw [r.output_eq]
    rfl
  have hd : (ReferenceActivePhysicalStep.prepare r.input).coordinator ≠ .dagger := by
    intro hdagger
    change ReferenceActivePhysicalStep.dispatch r.input = .dagger at hdagger
    unfold ReferenceActivePhysicalStep.dispatch at hdagger
    cases hc : r.input.state.coordinator with
    | first =>
        simp only [hc, CoordinatorRoundDispatch.dispatch] at hdagger
        cases CoordinatorRoundDispatch.dispatchFirst
          (ReferenceActivePhysicalStep.firstInput r.input) <;> contradiction
    | live registers owned base =>
        simp only [hc, CoordinatorRoundDispatch.dispatch] at hdagger
        cases CoordinatorRoundDispatch.dispatchLive
          (ReferenceActivePhysicalStep.liveInput r.input registers owned base) <;> contradiction
    | collection payload ledger saved =>
        simp only [hc] at hdagger
        split at hdagger
        · rename_i hcutoff
          simp only [CoordinatorRoundDispatch.dispatch] at hdagger
          cases CoordinatorRoundDispatch.dispatchCollection
            (ReferenceActivePhysicalStep.collectionInput r.input payload ledger
              (ReferenceActivePhysicalStep.collectionClock payload ledger saved
                ⟨ledger.cutoff - 1, by omega⟩) ⟨ledger.cutoff - 1, by omega⟩) <;> contradiction
        · contradiction
    | dagger => exact hbefore hc
  cases hs : (ReferenceActivePhysicalStep.prepare r.input).coordinator.selection with
  | some selected => exact ⟨selected, by rw [hp]; exact hs⟩
  | none =>
      have hf : r.output.coordinator.failure = some .dispatchRejected := by
        rw [r.output_eq]
        change (ReferenceActivePhysicalStep.prepare r.input).observeCoordinator.failure = _
        unfold ReferenceActivePhysicalStep.PreparedRound.observeCoordinator
        rw [dite_eq_left hs]
        cases hc : (ReferenceActivePhysicalStep.prepare r.input).coordinator <;>
          simp only [ReferenceActivePhysicalStep.coordinatorFailure]
        exact (hd hc).elim
      exact (hfailure (Or.inl ⟨_, hf⟩)).elim

/-- A continuing collection selection reads pending at CHOICE, before the
recorder and UP receiver. -/
theorem collection_selection_pending
    (r : ReferenceCompletePhysicalHistory.RoundRecord p rate)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (saved : Option (Fin p.T × Bool))
    (hc : r.input.state.coordinator = .collection payload ledger saved)
    (hn : ReferenceCollectionPhaseHistory.laterChosen r.input = false)
    (selected : ReferenceActivePhysicalStep.Selection r.input)
    (hs : r.output.preparation.coordinator.selection = some selected) :
    selected.view.payload = payload ∧ selected.view.pendingAtChoice = ledger.pending := by
  classical
  have hp : r.output.preparation.coordinator = ReferenceActivePhysicalStep.dispatch r.input := by
    rw [r.output_eq]
    rfl
  rw [hp] at hs
  by_cases hv : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
  · let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
    let clock := ReferenceActivePhysicalStep.collectionClock payload ledger saved cutoff
    let x := ReferenceActivePhysicalStep.collectionInput r.input payload ledger clock cutoff
    have hd : ReferenceActivePhysicalStep.dispatch r.input =
        .collection payload ledger clock cutoff (CoordinatorRoundDispatch.dispatchCollection x) := by
      simp only [ReferenceActivePhysicalStep.dispatch, hc, dite_eq_left hv,
        CoordinatorRoundDispatch.dispatch]
      rfl
    rw [hd] at hs
    cases ho : CoordinatorRoundDispatch.dispatchCollection x with
    | continuing core prepared boundary scores =>
        rw [ho] at hs
        have he := Option.some.inj hs
        have hpayload := congrArg
          (fun s : ReferenceActivePhysicalStep.Selection r.input => s.view.payload) he.symm
        have hstarted := congrArg
          (fun s : ReferenceActivePhysicalStep.Selection r.input => s.started) he.symm
        refine ⟨hpayload, selected.pending_eq.trans ?_⟩
        exact (congrArg (fun started => started.pending) hstarted).trans
          prepared.clockStarted_frame.2.1
    | laterChosen core consistent started startEq instruction instructionEq output
        localEq clockData installed chosen =>
        have htrue : ReferenceCollectionPhaseHistory.laterChosen r.input = true := by
          simp only [ReferenceCollectionPhaseHistory.laterChosen,
            ReferenceActivePhysicalStep.prepare, hd, ho]
        exact Bool.noConfusion (hn.symm.trans htrue)
    | _ => simp [ho, ReferenceActivePhysicalStep.DispatchCut.selection] at hs
  · simp [ReferenceActivePhysicalStep.dispatch, hc, dite_eq_right hv,
      ReferenceActivePhysicalStep.DispatchCut.selection] at hs

/-- Local sender consequences of the actual retained selection and its
CHOICE pending membership. Source assembly produces these inputs below. -/
theorem selected_sender
    (r : ReferenceCompletePhysicalHistory.RoundRecord p rate)
    (payload : ReferenceActivePhysicalStep.Payload rate) (i : Fin (p.m - 1))
    (selected : ReferenceActivePhysicalStep.Selection r.input)
    (hselected : r.output.preparation.coordinator.selection = some selected)
    (hpayload : selected.view.payload = payload)
    (hdown : ActiveFollowerDownAcceptance.downSelected p i r.input.row r.input.time)
    (hpending : i ∈ selected.view.pendingAtChoice) :
    ReferenceDownReception.selectedDownSenderBranch selected.view i r.input.row r.input.time ∧
    ReferenceActiveAffinePositiveTest.downSent r.input =
      some (CoordinatorLocalArmChoice.storedDownFlatWord payload i) ∧
    ReferenceDownReception.expectedDownFlatWord
      r.output.preparation.coordinator.downView i r.input.row r.input.time =
        some (CoordinatorLocalArmChoice.storedDownFlatWord payload i) ∧
    r.output.preparation.arms.actions (ActiveRoundActions.coordinator p.two_le_m) =
      ActiveRoundActions.sendArm
        (CoordinatorLocalArmChoice.currentDownHash payload (r.input.row.2 r.input.time) i)
        ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K (r.input.row.2 r.input.time).1).val
          (ActiveRoundActions.coordinator p.two_le_m))
        ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K (r.input.row.2 r.input.time).1).val
          (PublicDiscreteDraws.followerPlayer p.two_le_m i)) ∧
    (ReferenceActiveAffinePositiveTest.downPositive r.input = true →
      AffineChannelLaw.affineHash (ReferenceDownPhysicalHashRule.originalDownSample r.input)
        (CoordinatorLocalArmChoice.storedDownFlatWord payload i) = 1) := by
  have hbranch : ReferenceDownReception.selectedDownSenderBranch selected.view i r.input.row r.input.time :=
    ⟨hdown.1, hdown.2, hpending⟩
  have hview : r.output.preparation.coordinator.downView = some selected.view := by
    simp only [ReferenceActivePhysicalStep.DispatchCut.downView, hselected, Option.map_some]
  have hexpected : ReferenceDownReception.expectedDownFlatWord
      r.output.preparation.coordinator.downView i r.input.row r.input.time =
        some (CoordinatorLocalArmChoice.storedDownFlatWord payload i) := by
    rw [hview]
    exact (selected.expected_down_word i hbranch).trans (by rw [hpayload])
  have hp : r.output.preparation = ReferenceActivePhysicalStep.prepare r.input := by
    rw [r.output_eq]
    rfl
  have hsent : ReferenceActiveAffinePositiveTest.downSent r.input =
      some (CoordinatorLocalArmChoice.storedDownFlatWord payload i) := by
    unfold ReferenceActiveAffinePositiveTest.downSent
    rw [ReferenceActiveAffinePositiveTest.upSenderIndex_eq_draw, hdown.2]
    change ReferenceDownReception.expectedDownFlatWord
      (ReferenceActivePhysicalStep.prepare r.input).coordinator.downView i r.input.row r.input.time = _
    rw [← hp]
    exact hexpected
  have haction := ReferenceActivePhysicalStep.action_eq_down_sendArm
    r.output.preparation selected hselected i hbranch
  rw [hpayload] at haction
  exact ⟨hbranch, hsent, hexpected, haction,
    fun hpositive => ReferenceDownPhysicalHashRule.downPositive_sent_hash_one
      r.input _ hsent hpositive⟩

/-- The current raw call remains available even on a detecting failure. -/
theorem selected_down_raw
    (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p) (t : Fin p.T)
    (own : ReferencePrelaunchFollower.Observation p)
    (choice : ReferencePrelaunchFollower.State p rate.eta)
    (hs : ActiveFollowerDownAcceptance.downSelected p i row t)
    (hu : choice.status = .unoccupied)
    (hop : ActiveFollowerDownAcceptance.operationInputDomain p rate choice) :
    (ReferenceDownReception.referenceDownCut p view i row t own rate choice).raw =
      (ActiveFollowerDownAcceptance.currentDecodeStep p i row t own rate choice).2 := by
  classical
  simp only [ReferenceDownReception.referenceDownCut, dite_eq_left hs,
    dite_eq_left hu, dite_eq_left hop.1, dite_eq_left hop.2.1, dite_eq_left hop.2.2]
  split <;> rfl

/-- Reception is conditional on the actual current decoder word. The source
forward theorem supplies checked recovery and the literal retained slots. -/
theorem current_word_reception
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (r : ReferenceCompletePhysicalHistory.RoundRecord p rate)
    (hr : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[k.val] = r)
    (i : Fin (p.m - 1))
    (choice : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (payload : ReferenceActivePhysicalStep.Payload rate) (u : ℕ) :
    let own := r.output.preparation.feedback.observations
      (PublicDiscreteDraws.followerPlayer p.two_le_m i)
    let decoded := ActiveFollowerDownAcceptance.currentDecodeStep
      p i r.input.row r.input.time own rate choice
    let diag := ReferenceDownReception.referenceDownCut p
      r.output.preparation.coordinator.downView i r.input.row r.input.time own rate choice
    let M := payload.downRecord i
    ∀ selected : ReferenceActivePhysicalStep.Selection r.input,
    r.output.preparation.coordinator.selection = some selected →
    selected.view.payload = payload →
    (ReferenceFollowerFixedReply.actualChoice r i).configuration = .ordinary choice memory →
    choice.status = .unoccupied →
    ActiveFollowerDownAcceptance.downSelected p i r.input.row r.input.time →
    ReferenceDownReception.expectedDownFlatWord r.output.preparation.coordinator.downView
      i r.input.row r.input.time = some (CoordinatorLocalArmChoice.storedDownFlatWord payload i) →
    OrdinaryMessageCodec.acceptDown (ReferencePrelaunchFollower.codecParams p rate.eta)
      (ReferencePrelaunchFollower.acceptedStart choice) (r.input.time.val + 1) M →
    FollowerCutoffScan.firstCutoff p rate.eta.val payload.sigma
      (FollowerCutoffScan.completeRowProposalBit p rate.eta.val r.input.row) = u →
    u ≤ r.input.time.val + 1 →
    decoded.2 = some (CoordinatorLocalArmChoice.storedDownFlatWord payload i) →
    ∃ (accepted : OrdinaryMessageCodec.acceptDown
        (ReferencePrelaunchFollower.codecParams p rate.eta)
        (ReferencePrelaunchFollower.acceptedStart choice) (r.input.time.val + 1) M)
      (recovered : ActiveFollowerDownAcceptance.ReplayRegisters)
      (post : ReferencePrelaunchFollower.State p rate.eta),
      let scan := ActiveFollowerDownAcceptance.acceptedCutoffScan p rate M r.input.time
        (ActiveFollowerDownAcceptance.acceptedDownStartLE p rate M r.input.time choice accepted)
        r.input.row
      scan.endpoint = u ∧
      ActiveFollowerDownAcceptance.checkedRecovery p rate M choice u = .ok recovered ∧
      recovered.registers = QueueReplay.replay (4 * rate.n) (0, M.val.q)
        (ActiveFollowerDownAcceptance.recoveryQueueRecords p rate M choice u) ∧
      (∀ j : ℕ, ∃ middle,
        ActiveFollowerDownAcceptance.checkedReplay (D p) (p.T * D p) (4 * rate.n) 0
          ⟨(0, M.val.q), 0⟩
          ((ActiveFollowerDownAcceptance.recoveryQueueRecords p rate M choice u).take j) =
            .ok middle ∧
        middle.registers = QueueReplay.replay (4 * rate.n) (0, M.val.q)
          ((ActiveFollowerDownAcceptance.recoveryQueueRecords p rate M choice u).take j)) ∧
      post.lastDown = some M ∧ post.status = .unoccupied ∧ post.buffer = [] ∧
      post.downBatch = decoded.1 ∧
      diag.raw = decoded.2 ∧
      diag.outcome = .accepted choice post decoded.2 M scan
        recovered.registers recovered.lastService ∧
      r.output.followers i = ⟨.ordinary post memory, none, some choice, some diag⟩ ∧
      r.output.next.followers i = .ordinary post memory ∧
      ReferenceAcceptedUpFollowerHistory.RetainedDown r i M := by
  subst r
  let r := (ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate source rewards C_star C_h)[k.val]
  intro own decoded diag M selectedActual hselectedActual hpayload hc hu hs he ha hfirst hub hraw
  subst payload
  have htest : ReferenceDownReception.ordinaryLocalAcceptanceTest p rate r.input.time choice
      (ReferenceDownReception.ordinaryParse p rate decoded.2) := by
    have hp : ReferenceDownReception.ordinaryParse p rate decoded.2 = some M :=
      (congrArg (ReferenceDownReception.ordinaryParse p rate) hraw).trans
        (parse_stored_word (rate := rate) selectedActual.view.payload i)
    exact (congrArg (ReferenceDownReception.ordinaryLocalAcceptanceTest
      p rate r.input.time choice) hp).mpr ha
  have hforward :=
    ReferenceCompleteAcceptedCurrentDownForward.complete_ordinary_unoccupied_accepted_current_down_forward
      (rate := rate) rewards C_star C_h source k i choice memory hc hu
      ⟨hs, hraw.trans he.symm, htest⟩
  simp (config := { zeta := true }) only [] at hforward
  obtain ⟨selected, hselected, hview, hbranch, hraw', hparsed, accepted,
    b, beta, hbk, hbirth, hbase, hcredit, recovered, hfinal⟩ := hforward
  have hsame : selected = selectedActual :=
    Option.some.inj (hselected.symm.trans hselectedActual)
  subst selected
  have hdownStart : ActiveFollowerDownAcceptance.downStart p rate M = selectedActual.view.payload.sigma := by
    apply Fin.ext
    have hval := ActiveFollowerDownAcceptance.downStart_val_add_one p rate M
    have hfields := congrArg OrdinaryMessageCodec.DownFields.sigma
      (selectedActual.view.payload.downRecord_fields i)
    change (ActiveFollowerDownAcceptance.downStart p rate M).val = selectedActual.view.payload.sigma.val
    have hfields' : M.val.sigma = selectedActual.view.payload.sigma.val + 1 := hfields
    omega
  have hscan := ReferenceFirstReplacementCollectionFollowerPrefix.acceptedScan_endpoint_of_firstCutoff
    M selectedActual.view.payload.sigma r.input.time r.input.row u hdownStart
    (ActiveFollowerDownAcceptance.acceptedDownStartLE p rate M r.input.time choice accepted)
    hfirst (by
      change u ≤ r.input.time.val + 1 at hub
      exact Nat.le_trans hub (Nat.le_succ _))
  clear hfirst
  subst u
  have hne : (ActiveFollowerDownAcceptance.acceptedCutoffScan p rate M r.input.time
      (ActiveFollowerDownAcceptance.acceptedDownStartLE p rate M r.input.time choice accepted)
      r.input.row).endpoint ≠ r.input.time.val + 2 := by
    change _ ≤ r.input.time.val + 1 at hub
    exact ne_of_lt (lt_of_le_of_lt hub (Nat.lt_succ_self _))
  rcases hfinal with ⟨_, _, _, hchecked, hregisters, _, _, _, _, _, _, _, _, _, hprefix,
    _, _, _, _, _, hdiagRaw, _, _, _, _, houtcome, _, _, _, _, _, _, _, _, houtput, hnext⟩
  let scan := ActiveFollowerDownAcceptance.acceptedCutoffScan p rate M r.input.time
    (ActiveFollowerDownAcceptance.acceptedDownStartLE p rate M r.input.time choice accepted)
    r.input.row
  let post : ReferencePrelaunchFollower.State p rate.eta := { choice with
    lastDown := some M
    S := recovered.registers.1
    delta := recovered.lastService
    backlog := recovered.registers.2
    downBatch := decoded.1
    buffer := []
    status := if scan.endpoint = r.input.time.val + 2 then .pending else .unoccupied }
  let nextMemory : ActiveFollowerLifecycle.LocalMemory p := if scan.endpoint = r.input.time.val + 2 then
    { lastProposalRead := some {
      timestamp := r.input.time
      bit := FollowerCutoffScan.completeRowProposalBit p rate.eta.val r.input.row r.input.time } }
    else memory
  have hmemory : nextMemory = memory := ite_eq_right hne
  have houtput' : r.output.followers i =
      ⟨.ordinary post memory, none, some choice, some diag⟩ :=
    houtput.trans (congrArg (fun mem =>
      (⟨.ordinary post mem, none, some choice, some diag⟩ :
        ReferenceActivePhysicalStep.FollowerObservation p rate)) hmemory)
  have hnext' : r.output.next.followers i = .ordinary post memory :=
    hnext.trans (congrArg (fun mem => DeclaredFollowerLocalRound.LocalConfiguration.ordinary post mem)
      hmemory)
  refine ⟨accepted, recovered, post, rfl, hchecked, hregisters, ?_, rfl,
    ite_eq_right hne, rfl, rfl, hdiagRaw, houtcome, houtput', hnext', ?_⟩
  · intro j
    obtain ⟨middle, hm, _, hr, _⟩ := hprefix j
    exact ⟨middle, hm, hr⟩
  · refine ⟨choice, diag, post, decoded.2, scan, recovered.registers,
      recovered.lastService, ?_, ?_, houtcome⟩
    · exact congrArg (fun out : ReferenceActivePhysicalStep.FollowerObservation p rate => out.downInput) houtput'
    · exact congrArg (fun out : ReferenceActivePhysicalStep.FollowerObservation p rate => out.down) houtput'

/-- Connect the actual endpoint readouts without changing the physical run. -/
theorem connected_of_endpoint_links
    (records : List (ReferenceCompletePhysicalHistory.RoundRecord p rate))
    (Z : ℕ → ReferenceActivePhysicalStep.State p rate)
    (hlinks : ∀ a : Fin records.length,
      (records.get a).input.state = Z a.val ∧
      (records.get a).output.next = Z (a.val + 1)) :
    ReferenceActivePhysicalHorizon.Connected (Z 0) records (Z records.length) := by
  have htake : ∀ j : ℕ, j ≤ records.length →
      ReferenceActivePhysicalHorizon.Connected (Z 0) (records.take j) (Z j) := by
    intro j hj
    induction j with
    | zero => rfl
    | succ j ih =>
        have hlt : j < records.length := by omega
        have h := hlinks ⟨j, hlt⟩
        rw [← h.2, List.take_succ_eq_append_getElem hlt]
        exact ReferenceActivePhysicalHorizon.Connected.append_one _ _ (ih (by omega)) h.1
  simpa only [List.take_length] using htake records.length le_rfl

/-- Exact source fields at a finite physical index. -/
theorem complete_record_fields
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length) :
    let r := (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).get k
    r.input.time.val = ReferenceCompletePhysicalHistory.physicalStart
      rate source rewards C_star C_h + k.val ∧
    r.input.rows = source.1.2 ∧
    r.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p source ∧
    r.input.rewards = rewards := by
  obtain ⟨_, _, hr⟩ := ReferenceLaterLiveNumericalReadout.source_record_prefix
    rate rewards C_star C_h source k
  rw [hr]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- A retained selected receiver call has exactly its own physical positive
feedback test, including zero observations and detecting failures. -/
theorem selected_positive_eq_feedback
    (r : ReferenceCompletePhysicalHistory.RoundRecord p rate) (i : Fin (p.m - 1))
    (choice : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (post : ReferencePrelaunchFollower.State p rate.eta)
    (hs : ActiveFollowerDownAcceptance.downSelected p i r.input.row r.input.time)
    (hu : choice.status = .unoccupied)
    (hop : ActiveFollowerDownAcceptance.operationInputDomain p rate choice)
    (hout : r.output.followers i = ⟨.ordinary post memory, none, some choice,
      some (ReferenceDownReception.referenceDownCut p r.output.preparation.coordinator.downView
        i r.input.row r.input.time (r.output.preparation.feedback.observations
          (PublicDiscreteDraws.followerPlayer p.two_le_m i)) rate choice)⟩) :
    ReferenceActiveAffinePositiveTest.downPositive r.input =
      decide (0 < (r.output.preparation.feedback.observations
        (PublicDiscreteDraws.followerPlayer p.two_le_m i)).val.val) := by
  classical
  rw [ReferenceActiveAffinePositiveTest.record_downPositive,
    ReferenceActiveAffinePositiveTest.upSenderIndex_eq_draw, hs.2, hout]
  simp only [ReferenceActiveAffinePositiveTest.downDiagnosticCall,
    ReferenceActiveAffinePositiveTest.referenceDownCut_has_call,
    ReferenceActiveAffinePositiveTest.downReceiverGate,
    hs, hu, hop.1, hop.2.1, hop.2.2, and_self, decide_true, Bool.true_and]

/-- Source-produced OLD-choice chronology, original raw calls, and strict
past exclusion. No survival or sender premise is supplied to this theorem. -/
theorem complete_first_replacement_collection_old_down_choice
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
            let W := (R.drop (c + 1)).takeWhile
              (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
            let K := cut :: W
            let E := fun j => ReferenceCollectionSegmentExtraction.endpointState
              cut.output.next (W.take j)
            let Z := fun j => ReferenceCollectionSegmentExtraction.endpointState
              cut.input.state (K.take j)
            let M := fun i => payload.downRecord i
            let u := cut.input.time.val + 1
            Z 0 = cut.input.state ∧
            (∀ j : ℕ, j ≤ W.length → Z (j + 1) = E j) ∧
            (∀ a : Fin K.length, (K.get a).input.state = Z a.val ∧
              (K.get a).output.next = Z (a.val + 1)) ∧
            (∀ a : Fin K.length, R[c + a.val]? = some (K.get a)) ∧
            ∀ (a : Fin K.length) (i : Fin (p.m - 1))
              (choice : ReferencePrelaunchFollower.State p rate.eta)
              (memory : ActiveFollowerLifecycle.LocalMemory p),
              let r := K.get a
              (ReferenceFollowerFixedReply.actualChoice r i).configuration =
                .ordinary choice memory →
              choice.status = .unoccupied → choice.lastDown ≠ some (M i) →
              r.input.time.val = s + (c + a.val) ∧
              r.input.rows = source.1.2 ∧ r.input.selected = J ∧ r.input.rewards = rewards ∧
              r.input.time.val + 1 = u + a.val ∧
              ReferencePrelaunchFollower.acceptedStart choice < (M i).val.sigma ∧
              (M i).val.sigma ≤ r.input.time.val + 1 ∧
              ActiveFollowerLifecycle.localStateDomainValid choice ∧
              ActiveFollowerDownAcceptance.operationInputDomain p rate choice ∧
              ReferenceDownReception.ordinaryParse p rate
                (some (CoordinatorLocalArmChoice.storedDownFlatWord payload i)) = some (M i) ∧
              ReferenceDownReception.ordinaryLocalAcceptanceTest p rate r.input.time choice
                (ReferenceDownReception.ordinaryParse p rate
                  (some (CoordinatorLocalArmChoice.storedDownFlatWord payload i))) ∧
              i ∉ (ReferenceCollectionPhaseHistory.acceptedLabels (K.take a.val)).toFinset ∧
              (∀ b : Fin K.length, b.val < a.val →
                ¬ ReferenceAcceptedUpFollowerHistory.RetainedDown (K.get b) i (M i)) ∧
              (ActiveFollowerDownAcceptance.downSelected p i r.input.row r.input.time →
                let own := r.output.preparation.feedback.observations
                  (PublicDiscreteDraws.followerPlayer p.two_le_m i)
                let decoded := ActiveFollowerDownAcceptance.currentDecodeStep
                  p i r.input.row r.input.time own rate choice
                let diag := ReferenceDownReception.referenceDownCut p
                  r.output.preparation.coordinator.downView i r.input.row r.input.time own rate choice
                (∃ post,
                  r.output.followers i = ⟨.ordinary post memory, none, some choice, some diag⟩) ∧
                diag.raw = decoded.2 ∧
                ReferenceActiveAffinePositiveTest.downPositive r.input = decide (0 < own.val.val))
          | _ => True
      | _ => True := by
  classical
  have hF := ReferenceFirstReplacementCollectionPrefix.complete_first_replacement_collection_follower_prefix
    rate source rewards C_star C_h
  have hK := ReferenceFirstReplacementCutoffDownRecovery.complete_first_replacement_cutoff_down_recovery_and_finish
    rate source rewards C_star C_h
  have hO := ReferenceFirstReplacementCollectionUpOfferCut.complete_first_replacement_collection_up_offer_cut
    rate source rewards C_star C_h
  have hU := ReferenceFirstReplacementCollectionUpReceiverProvenance.complete_first_replacement_collection_up_receiver_provenance
    rate source rewards C_star C_h
  simp (config := { zeta := true }) only [] at hF hK hO hU ⊢
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
    simp only [hb] at hF hK hO hU ⊢
    cases hbirth : birth.output.preparation.coordinator with
    | first _ => trivial
    | live _ _ _ _ => trivial
    | dagger => trivial
    | invalidCollectionCutoff => trivial
    | collection _ _ _ _ outcome =>
      simp only [hbirth] at hF hK hO hU ⊢
      cases outcome <;> try trivial
      rename_i core consistent started hstart instruction hinstruction output hconsistent
        clockData installed selectedBirth
      dsimp only [ReferenceActivePhysicalStep.collectionInput] at hF hK hO hU ⊢
      let payload : ReferenceActivePhysicalStep.Payload rate := installed.registers.payload
      rcases hO with ⟨_, _, hO⟩
      rcases hU with ⟨_, _, hU⟩
      cases hcutGet : R[c]? with
      | none => trivial
      | some cut =>
        simp only [tail, c, hcutGet] at hF hK hO hU ⊢
        rcases hK with ⟨_, hK⟩
        cases hcut : cut.output.preparation.coordinator with
        | first _ => trivial
        | collection _ _ _ _ _ => trivial
        | dagger => trivial
        | invalidCollectionCutoff => trivial
        | live registers owned base outcome =>
          simp only [hcut] at hF hK hO hU ⊢
          cases outcome <;> try trivial
          rename_i dispatched hs ledger hi hledger hdata hclock hpending hnone chosenCut
          dsimp only at hF hK hO hU ⊢
          let W := (R.drop (c + 1)).takeWhile
            (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
          let K := cut :: W
          let E := fun j => ReferenceCollectionSegmentExtraction.endpointState
            cut.output.next (W.take j)
          let Z := fun j => ReferenceCollectionSegmentExtraction.endpointState
            cut.input.state (K.take j)
          let M := fun i => payload.downRecord i
          let u := cut.input.time.val + 1
          rcases hF with ⟨_, _, _, hu3, huT, hfirst, hfollowers⟩
          rcases hK with ⟨_, _, _, hcutRows, hcutSelected, _, _, _, _, _, _,
            selectedCut, hselectionCut, hpayloadCut, hpendingCut, _, hcutFollowers⟩
          rcases hO with ⟨hcalendar, ⟨hZzero, hZsucc, hZrecord⟩, _, _⟩
          rcases hU with ⟨hledgers, hreceptions, _⟩
          change Z 0 = cut.input.state at hZzero
          change ∀ j : ℕ, j ≤ W.length → Z (j + 1) = E j at hZsucc
          change ∀ a : Fin K.length, (K.get a).input.state = Z a.val ∧
            (K.get a).output.next = Z (a.val + 1) at hZrecord
          change ∀ a : Fin K.length, (K.get a).input.time.val + 1 = u + a.val at hcalendar
          have hselectionCut' : cut.output.preparation.coordinator.selection = some selectedCut := by
            rw [hcut]
            exact hselectionCut
          have hchain := connected_of_endpoint_links K Z hZrecord
          obtain ⟨hcBound, hcElem⟩ := List.getElem?_eq_some_iff.mp hcutGet
          have hWprefix : W <+: R.drop (c + 1) := List.takeWhile_prefix _
          have hget : ∀ a : Fin K.length, R[c + a.val]? = some (K.get a) := by
            intro ⟨a, ha⟩
            cases a with
            | zero =>
              change R[c + 0]? = some cut
              exact hcutGet
            | succ j =>
              have hj : j < W.length := by
                change j + 1 < W.length + 1 at ha
                omega
              have hbound := hWprefix.length_le
              simp only [List.length_drop] at hbound
              have hindex : c + 1 + j < R.length := by omega
              have he := hWprefix.getElem hj
              rw [List.getElem_drop] at he
              change R[c + (j + 1)]? = some (W.get ⟨j, hj⟩)
              apply List.getElem?_eq_some_iff.mpr
              refine ⟨by omega, ?_⟩
              simpa only [K, List.get_eq_getElem, List.getElem_cons_succ,
                Nat.add_assoc, Nat.add_comm 1 j] using he.symm
          have hchoices : ∀ (a : Fin K.length) (i : Fin (p.m - 1)), ∃ state mem,
              (ReferenceFollowerFixedReply.actualChoice (K.get a) i).configuration =
                .ordinary state mem := by
            intro a i
            obtain ⟨hk, he⟩ := List.getElem?_eq_some_iff.mp (hget a)
            obtain ⟨_, mem, state, _, _, _, hc, _, _⟩ :=
              ReferenceCompleteSuffixFollowerPreservation.complete_suffix_follower_choice
                (rate := rate) rewards C_star C_h source ⟨c + a.val, hk⟩ i
            change (ReferenceFollowerFixedReply.actualChoice R[c + a.val] i).configuration =
              .ordinary state mem at hc
            rw [he] at hc
            exact ⟨state, mem, hc⟩
          refine ⟨hZzero, hZsucc, hZrecord, hget, ?_⟩
          intro a i choice memory hc hu hOld
          let r := K.get a
          obtain ⟨hrBound, hrElem⟩ := List.getElem?_eq_some_iff.mp (hget a)
          let k : Fin R.length := ⟨c + a.val, hrBound⟩
          have hsource := complete_record_fields rate source rewards C_star C_h k
          rw [show R.get k = r from hrElem] at hsource
          obtain ⟨_, memF, choiceF, _, _, _, hcF, hchoiceDomain, hoperation⟩ :=
            ReferenceCompleteSuffixFollowerPreservation.complete_suffix_follower_choice
              (rate := rate) rewards C_star C_h source k i
          rw [hrElem] at hcF
          obtain ⟨hchoiceSame, hmemorySame⟩ := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
            (hc.symm.trans hcF)
          subst choice
          subst memory
          have hlocal : ReferencePrelaunchFollower.acceptedStart choiceF < (M i).val.sigma ∧
              (M i).val.sigma ≤ r.input.time.val + 1 ∧
              ∀ hdown : ActiveFollowerDownAcceptance.downSelected p i r.input.row r.input.time,
                ∃ post, r.output.followers i = ⟨.ordinary post memF, none, some choiceF,
                  some (ReferenceDownReception.referenceDownCut p
                    r.output.preparation.coordinator.downView i r.input.row r.input.time
                    (r.output.preparation.feedback.observations
                      (PublicDiscreteDraws.followerPlayer p.two_le_m i)) rate choiceF)⟩ := by
            rcases a with ⟨a, ha⟩
            cases a with
            | zero =>
              change (ReferenceFollowerFixedReply.actualChoice cut i).configuration = _ at hc
              rcases hcutFollowers i with ⟨old, mem, hinput, _, _, _, holder, hoccupied,
                _, _, hchoice, _, _, _, _, _, hstartBound, _, logged, post,
                hlogging, _, _, _, _, _, _, _, _, _, _, hlogChoice, htail⟩
              have hactual : (ReferenceFollowerFixedReply.actualChoice cut i).configuration =
                  .ordinary { old with status := .unoccupied } mem := hchoice
              obtain ⟨rfl, rfl⟩ := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
                (hc.symm.trans hactual)
              have holdStatus : old.status = .unoccupied := by
                by_contra hn
                exact hOld (hoccupied hn).1
              refine ⟨holder holdStatus, Nat.le_trans hstartBound (Nat.le_succ _), ?_⟩
              intro hdown
              have hsame := hlogChoice hdown
              subst logged
              rcases htail with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, houtput⟩
              refine ⟨post, ?_⟩
              simpa only [r, K, List.get_eq_getElem, List.getElem_cons_zero, hcut] using houtput
            | succ j =>
              have hj : j < W.length := by
                change j + 1 < W.length + 1 at ha
                omega
              rcases hfollowers i with ⟨hstartBound, _, old, initial, mem,
                _, _, _, _, _, _, _, _, _, _, _, _, _, _, hsteps, _⟩
              rcases hsteps j hj with ⟨_, state, logged, post, _, _, _, _, _, _, _, hclass,
                _, _, _, hchoice, _, hlogging, _, hlast, _, _, _, _, _, _, _, _, _, _, _, _, _,
                _, _, _, houtput, hrest⟩
              have hactual : (ReferenceFollowerFixedReply.actualChoice r i).configuration =
                  .ordinary state mem := hchoice
              obtain ⟨hchoiceSame, hmemorySame⟩ := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
                (hc.symm.trans hactual)
              subst choiceF
              subst memF
              have holder : ReferencePrelaunchFollower.acceptedStart state < (M i).val.sigma :=
                hclass.resolve_right hOld
              refine ⟨holder, ?_, ?_⟩
              · have ht := hcalendar ⟨j + 1, ha⟩
                change (M i).val.sigma ≤ u - 1 at hstartBound
                change r.input.time.val + 1 = u + (j + 1) at ht
                omega
              · intro hdown
                have hvalid := (ActiveFollowerLogging.checkedLogging_success_iff
                  i r.input.row (r.input.state.activations i) r.input.time
                  ((ReferenceFollowerFixedReply.actualChoice r i).arm,
                    r.output.preparation.feedback.observations
                      (PublicDiscreteDraws.followerPlayer p.two_le_m i)) state logged).mp hlogging
                have hnoop := ReferenceActiveAffinePositiveTest.checkedLogging_eq_of_down
                  (rate := rate) i r.input.row (r.input.state.activations i) r.input.time
                  ((ReferenceFollowerFixedReply.actualChoice r i).arm,
                    r.output.preparation.feedback.observations
                      (PublicDiscreteDraws.followerPlayer p.two_le_m i)) state hdown.1
                rw [ite_eq_left hvalid.1] at hnoop
                have hsame : logged = state := Except.ok.inj (hlogging.symm.trans hnoop)
                subst logged
                exact ⟨post, houtput⟩
          obtain ⟨holder, hstartBound, hrawSlots⟩ := hlocal
          have hphysical : ∀ b : Fin K.length,
              ReferenceActivePhysicalStep.upSenderIndex (K.get b).input = i →
              ∀ (t : ReferenceCollectionPhaseHistory.Tail (K.get b).input)
                (started : ReferenceActivePhysicalStep.Ledger rate),
              ReferenceCollectionPhaseHistory.executedTail (K.get b).input = some t →
              t.reception = some (started, ReferenceActivePhysicalStep.receiveUp
                (ReferenceActivePhysicalStep.prepare (K.get b).input) started) →
              PublicDiscreteDraws.slotDraw ((K.get b).input.row.2 (K.get b).input.time).1 =
                PublicDiscreteDraws.upSlot →
              ∃ offered offerMem offer,
                ((K.get b).output.preparation.followers.followers
                  (ReferenceActivePhysicalStep.upSenderIndex (K.get b).input)).configuration =
                    .ordinary offered offerMem ∧
                ActiveFollowerQueueOperation.checkedUpOffer rate.eta
                  (ReferenceActivePhysicalStep.upSenderIndex (K.get b).input)
                  (K.get b).input.row ((K.get b).input.state.activations
                    (ReferenceActivePhysicalStep.upSenderIndex (K.get b).input))
                  (K.get b).input.time offered = .offer offer ∧
                (CoordinatorCollectionLedger.acceptUpCheck started
                  (ReferenceActivePhysicalStep.upSenderIndex (K.get b).input) offer = false ∨
                  offered.lastDown = some (M i)) := by
            intro b hindex t started ht hr hslot
            have hrec := hreceptions b
            dsimp only [K, W, c, tail] at ht
            rw [ht] at hrec
            dsimp only at hrec
            rw [hr] at hrec
            obtain ⟨state, mem, offer, hcOffer, hchecked, _, _, horigin⟩ := hrec.2.2.2.2.2.1 hslot
            refine ⟨state, mem, offer, hcOffer, hchecked, ?_⟩
            rcases horigin with hreject | hcurrent
            · exact Or.inl hreject.2.2
            · have hcurrent' : state.lastDown = some
                  (M (ReferenceActivePhysicalStep.upSenderIndex (K.get b).input)) := hcurrent.1
              exact Or.inr (hcurrent'.trans (congrArg (fun j => some (M j)) hindex))
          have hnot := old_choice_not_mem_accepted_labels hchain a i (M i)
            choiceF memF hc holder (fun b => hchoices b i) hphysical
          have hnoEarlier := no_earlier_retained_down hchain a i (M i) choiceF memF hc holder
          have haTest : OrdinaryMessageCodec.acceptDown (ReferencePrelaunchFollower.codecParams p rate.eta)
              (ReferencePrelaunchFollower.acceptedStart choiceF) (r.input.time.val + 1) (M i) :=
            ⟨holder, hstartBound⟩
          have hparse := parse_stored_word (rate := rate) payload i
          have htest : ReferenceDownReception.ordinaryLocalAcceptanceTest p rate r.input.time choiceF
              (ReferenceDownReception.ordinaryParse p rate
                (some (CoordinatorLocalArmChoice.storedDownFlatWord payload i))) :=
            (congrArg (ReferenceDownReception.ordinaryLocalAcceptanceTest
              p rate r.input.time choiceF) hparse).mpr haTest
          refine ⟨hsource.1, hsource.2.1, hsource.2.2.1, hsource.2.2.2,
            hcalendar a, holder, hstartBound,
            hchoiceDomain, hoperation, hparse, htest, hnot, hnoEarlier, ?_⟩
          intro hdown
          let own := r.output.preparation.feedback.observations
            (PublicDiscreteDraws.followerPlayer p.two_le_m i)
          let decoded := ActiveFollowerDownAcceptance.currentDecodeStep
            p i r.input.row r.input.time own rate choiceF
          let diag := ReferenceDownReception.referenceDownCut p
            r.output.preparation.coordinator.downView i r.input.row r.input.time own rate choiceF
          obtain ⟨post, houtput⟩ := hrawSlots hdown
          exact ⟨⟨post, houtput⟩,
            selected_down_raw _ i r.input.row r.input.time own choiceF hdown hu hoperation,
            selected_positive_eq_feedback r i choiceF memF post hdown hu hoperation houtput⟩

/-- Actual OLD DOWN sender and hypothetical current-word acceptance on the
real first-replacement collection prefix, before physical failure. -/
theorem complete_first_replacement_collection_old_down_sender_readiness
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
            let W := (R.drop (c + 1)).takeWhile
              (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
            let K := cut :: W
            let E := fun j => ReferenceCollectionSegmentExtraction.endpointState
              cut.output.next (W.take j)
            let Z := fun j => ReferenceCollectionSegmentExtraction.endpointState
              cut.input.state (K.take j)
            let M := fun i => payload.downRecord i
            let u := cut.input.time.val + 1
            Z 0 = cut.input.state ∧
            (∀ j : ℕ, j ≤ W.length → Z (j + 1) = E j) ∧
            ∀ (a : Fin K.length) (i : Fin (p.m - 1))
              (choice : ReferencePrelaunchFollower.State p rate.eta)
              (memory : ActiveFollowerLifecycle.LocalMemory p),
              let r := K.get a
              (ReferenceFollowerFixedReply.actualChoice r i).configuration =
                .ordinary choice memory →
              choice.status = .unoccupied → choice.lastDown ≠ some (M i) →
              r.input.time.val = s + (c + a.val) ∧
              r.input.rows = source.1.2 ∧ r.input.selected = J ∧ r.input.rewards = rewards ∧
              ReferencePrelaunchFollower.acceptedStart choice < (M i).val.sigma ∧
              (M i).val.sigma ≤ r.input.time.val + 1 ∧
              ActiveFollowerLifecycle.localStateDomainValid choice ∧
              ActiveFollowerDownAcceptance.operationInputDomain p rate choice ∧
              ReferenceDownReception.ordinaryParse p rate
                (some (CoordinatorLocalArmChoice.storedDownFlatWord payload i)) = some (M i) ∧
              ReferenceDownReception.ordinaryLocalAcceptanceTest p rate r.input.time choice
                (ReferenceDownReception.ordinaryParse p rate
                  (some (CoordinatorLocalArmChoice.storedDownFlatWord payload i))) ∧
              i ∉ (ReferenceCollectionPhaseHistory.acceptedLabels (K.take a.val)).toFinset ∧
              (∀ b : Fin K.length, b.val < a.val →
                ¬ ReferenceAcceptedUpFollowerHistory.RetainedDown (K.get b) i (M i)) ∧
              (ActiveFollowerDownAcceptance.downSelected p i r.input.row r.input.time →
                let own := r.output.preparation.feedback.observations
                  (PublicDiscreteDraws.followerPlayer p.two_le_m i)
                let decoded := ActiveFollowerDownAcceptance.currentDecodeStep
                  p i r.input.row r.input.time own rate choice
                let diag := ReferenceDownReception.referenceDownCut p
                  r.output.preparation.coordinator.downView i r.input.row r.input.time own rate choice
                (∃ post,
                  r.output.followers i = ⟨.ordinary post memory, none, some choice, some diag⟩) ∧
                diag.raw = decoded.2 ∧
                ((∀ record ∈ K.take (a.val + 1),
                    ¬ ReferenceFirstReplacementCollectionStoppedPureUpQuota.physicalFailureAt record) →
                  ∃ selected : ReferenceActivePhysicalStep.Selection r.input,
                    r.output.preparation.coordinator.selection = some selected ∧
                    selected.view.payload = payload ∧ i ∈ selected.view.pendingAtChoice ∧
                    ReferenceDownReception.selectedDownSenderBranch selected.view i r.input.row r.input.time ∧
                    ReferenceActiveAffinePositiveTest.downSent r.input =
                      some (CoordinatorLocalArmChoice.storedDownFlatWord payload i) ∧
                    ReferenceDownReception.expectedDownFlatWord
                      r.output.preparation.coordinator.downView i r.input.row r.input.time =
                        some (CoordinatorLocalArmChoice.storedDownFlatWord payload i) ∧
                    r.output.preparation.arms.actions (ActiveRoundActions.coordinator p.two_le_m) =
                      ActiveRoundActions.sendArm
                        (CoordinatorLocalArmChoice.currentDownHash payload (r.input.row.2 r.input.time) i)
                        ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K (r.input.row.2 r.input.time).1).val
                          (ActiveRoundActions.coordinator p.two_le_m))
                        ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K (r.input.row.2 r.input.time).1).val
                          (PublicDiscreteDraws.followerPlayer p.two_le_m i)) ∧
                    (0 < own.val.val →
                      AffineChannelLaw.affineHash (ReferenceDownPhysicalHashRule.originalDownSample r.input)
                        (CoordinatorLocalArmChoice.storedDownFlatWord payload i) = 1) ∧
                    (decoded.2 = some (CoordinatorLocalArmChoice.storedDownFlatWord payload i) →
                      ∃ (accepted : OrdinaryMessageCodec.acceptDown
                          (ReferencePrelaunchFollower.codecParams p rate.eta)
                          (ReferencePrelaunchFollower.acceptedStart choice) (r.input.time.val + 1) (M i))
                        (recovered : ActiveFollowerDownAcceptance.ReplayRegisters)
                        (post : ReferencePrelaunchFollower.State p rate.eta),
                        let scan := ActiveFollowerDownAcceptance.acceptedCutoffScan p rate (M i)
                          r.input.time (ActiveFollowerDownAcceptance.acceptedDownStartLE
                            p rate (M i) r.input.time choice accepted) r.input.row
                        scan.endpoint = u ∧
                        ActiveFollowerDownAcceptance.checkedRecovery p rate (M i) choice u = .ok recovered ∧
                        recovered.registers = QueueReplay.replay (4 * rate.n) (0, (M i).val.q)
                          (ActiveFollowerDownAcceptance.recoveryQueueRecords p rate (M i) choice u) ∧
                        (∀ j : ℕ, ∃ middle,
                          ActiveFollowerDownAcceptance.checkedReplay (D p) (p.T * D p) (4 * rate.n) 0
                            ⟨(0, (M i).val.q), 0⟩
                            ((ActiveFollowerDownAcceptance.recoveryQueueRecords p rate (M i) choice u).take j) =
                              .ok middle ∧
                          middle.registers = QueueReplay.replay (4 * rate.n) (0, (M i).val.q)
                            ((ActiveFollowerDownAcceptance.recoveryQueueRecords p rate (M i) choice u).take j)) ∧
                        post.lastDown = some (M i) ∧ post.status = .unoccupied ∧ post.buffer = [] ∧
                        post.downBatch = decoded.1 ∧ diag.raw = decoded.2 ∧
                        diag.outcome = .accepted choice post decoded.2 (M i) scan
                          recovered.registers recovered.lastService ∧
                        r.output.followers i = ⟨.ordinary post memory, none, some choice, some diag⟩ ∧
                        r.output.next.followers i = .ordinary post memory ∧
                        ReferenceAcceptedUpFollowerHistory.RetainedDown r i (M i) ∧
                        ∃ b : ℕ, b = a.val + 1 ∧ b ≤ K.length ∧
                          (Z b).followers i = .ordinary post memory)))
          | _ => True
      | _ => True := by
  classical
  have hA := complete_first_replacement_collection_old_down_choice
    rate source rewards C_star C_h
  have hK := ReferenceFirstReplacementCutoffDownRecovery.complete_first_replacement_cutoff_down_recovery_and_finish
    rate source rewards C_star C_h
  have hU := ReferenceFirstReplacementCollectionUpReceiverProvenance.complete_first_replacement_collection_up_receiver_provenance
    rate source rewards C_star C_h
  simp (config := { zeta := true }) only [] at hA hK hU ⊢
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
    simp only [hb] at hA hK hU ⊢
    cases hbirth : birth.output.preparation.coordinator with
    | first _ => trivial
    | live _ _ _ _ => trivial
    | dagger => trivial
    | invalidCollectionCutoff => trivial
    | collection _ _ _ _ outcome =>
      simp only [hbirth] at hA hK hU ⊢
      cases outcome <;> try trivial
      rename_i core consistent started hstart instruction hinstruction output hconsistent
        clockData installed selectedBirth
      dsimp only [ReferenceActivePhysicalStep.collectionInput] at hA hK hU ⊢
      let payload : ReferenceActivePhysicalStep.Payload rate := installed.registers.payload
      rcases hU with ⟨_, _, hU⟩
      cases hcutGet : R[c]? with
      | none => trivial
      | some cut =>
        simp only [tail, c, hcutGet] at hA hK hU ⊢
        rcases hK with ⟨_, hK⟩
        cases hcut : cut.output.preparation.coordinator with
        | first _ => trivial
        | collection _ _ _ _ _ => trivial
        | dagger => trivial
        | invalidCollectionCutoff => trivial
        | live registers owned base outcome =>
          simp only [hcut] at hA hK hU ⊢
          cases outcome <;> try trivial
          rename_i dispatched hs ledger hi hledger hdata hclock hpending hnone chosenCut
          dsimp only at hA hK hU ⊢
          let W := (R.drop (c + 1)).takeWhile
            (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
          let K := cut :: W
          let E := fun j => ReferenceCollectionSegmentExtraction.endpointState
            cut.output.next (W.take j)
          let Z := fun j => ReferenceCollectionSegmentExtraction.endpointState
            cut.input.state (K.take j)
          let M := fun i => payload.downRecord i
          let u := cut.input.time.val + 1
          rcases hA with ⟨hZzero, hZsucc, hZrecord, hget, hchoices⟩
          rcases hK with ⟨_, _, _, hcutRows, hcutSelected, _, _, _, hfirst, _, _,
            selectedCut, hselectionCut, hpayloadCut, hpendingCut, _, _⟩
          rcases hU with ⟨hledgers, _, _⟩
          change Z 0 = cut.input.state at hZzero
          change ∀ j : ℕ, j ≤ W.length → Z (j + 1) = E j at hZsucc
          change ∀ a : Fin K.length, (K.get a).input.state = Z a.val ∧
            (K.get a).output.next = Z (a.val + 1) at hZrecord
          change ∀ a : Fin K.length, R[c + a.val]? = some (K.get a) at hget
          have hselectionCut' : cut.output.preparation.coordinator.selection = some selectedCut := by
            rw [hcut]
            exact hselectionCut
          refine ⟨hZzero, hZsucc, ?_⟩
          intro a i choice memory hc hu hOld
          let r := K.get a
          obtain ⟨hrBound, hrElem⟩ := List.getElem?_eq_some_iff.mp (hget a)
          let k : Fin R.length := ⟨c + a.val, hrBound⟩
          rcases hchoices a i choice memory hc hu hOld with
            ⟨htime, hrows, hselectedRow, hrewards, hcalendar, holder, hstartBound,
              hchoiceDomain, hoperation, hparse, htest, hnot, hnoEarlier, hrawSlots⟩
          have hsource : r.input.time.val = s + (c + a.val) ∧
              r.input.rows = source.1.2 ∧ r.input.selected = J ∧ r.input.rewards = rewards :=
            ⟨htime, hrows, hselectedRow, hrewards⟩
          have haTest : OrdinaryMessageCodec.acceptDown (ReferencePrelaunchFollower.codecParams p rate.eta)
              (ReferencePrelaunchFollower.acceptedStart choice) (r.input.time.val + 1) (M i) :=
            ⟨holder, hstartBound⟩
          refine ⟨htime, hrows, hselectedRow, hrewards, holder, hstartBound,
            hchoiceDomain, hoperation, hparse, htest, hnot, hnoEarlier, ?_⟩
          intro hdown
          let own := r.output.preparation.feedback.observations
            (PublicDiscreteDraws.followerPlayer p.two_le_m i)
          let decoded := ActiveFollowerDownAcceptance.currentDecodeStep
            p i r.input.row r.input.time own rate choice
          let diag := ReferenceDownReception.referenceDownCut p
            r.output.preparation.coordinator.downView i r.input.row r.input.time own rate choice
          obtain ⟨hrawSlots, hdiagRaw, hpositiveEq⟩ := hrawSlots hdown
          refine ⟨hrawSlots, hdiagRaw, ?_⟩
          intro hfailure
          have hzero : (Z 0).coordinator ≠ .dagger := by
            rw [hZzero]
            intro hd
            have hp : cut.output.preparation.coordinator = ReferenceActivePhysicalStep.dispatch cut.input := by
              rw [cut.output_eq]
              rfl
            simp only [ReferenceActivePhysicalStep.dispatch, hd] at hp
            rw [hcut] at hp
            contradiction
          have hsurvive := prefix_coordinator_ne_dagger K Z hZrecord hzero a hfailure
          have hbefore : r.input.state.coordinator ≠ .dagger := by
            rw [(hZrecord a).1]
            exact hsurvive a.val (by omega)
          have hmem : r ∈ K.take (a.val + 1) :=
            List.mem_take_iff_getElem.mpr ⟨a.val, lt_min (by omega) a.isLt, rfl⟩
          obtain ⟨selected, hselected⟩ := selection_exists_of_no_failure r hbefore (hfailure r hmem)
          have hpending : selected.view.payload = payload ∧ i ∈ selected.view.pendingAtChoice := by
            rcases a with ⟨a, ha⟩
            cases a with
            | zero =>
              have heq : selected = selectedCut := Option.some.inj (hselected.symm.trans hselectionCut')
              subst selected
              exact ⟨hpayloadCut, by rw [hpendingCut]; exact Finset.mem_univ i⟩
            | succ j =>
              have hj : j < W.length := by
                change j + 1 < W.length + 1 at ha
                omega
              have hz : (E j).coordinator ≠ .dagger := by
                rw [← hZsucc j (Nat.le_of_lt hj)]
                exact hsurvive (j + 1) (Nat.le_succ _)
              rcases hledgers j (Nat.le_of_lt hj) with hd | ⟨ledger', saved, hcoord, _, _, hpend⟩
              · exact (hz hd).elim
              have hinput : r.input.state.coordinator = .collection payload ledger' saved := by
                rw [(hZrecord ⟨j + 1, ha⟩).1, hZsucc j (Nat.le_of_lt hj)]
                exact hcoord
              have hn : ReferenceCollectionPhaseHistory.laterChosen r.input = false := by
                have hmemW : r ∈ W := List.get_mem W ⟨j, hj⟩
                have hpred := List.mem_takeWhile_imp hmemW
                cases ht : ReferenceCollectionPhaseHistory.laterChosen r.input <;> simp [ht] at hpred ⊢
              have hsel := collection_selection_pending r payload ledger' saved hinput hn selected hselected
              refine ⟨hsel.1, ?_⟩
              rw [hsel.2, hpend]
              apply Finset.mem_sdiff.mpr
              refine ⟨Finset.mem_univ i, ?_⟩
              simpa only [K, List.take_succ_cons] using hnot
          obtain ⟨hbranch, hsent, hexpected, haction, hhash⟩ :=
            selected_sender r payload i selected hselected hpending.1 hdown hpending.2
          refine ⟨selected, hselected, hpending.1, hpending.2, hbranch, hsent, hexpected, haction,
            (fun hpositive => hhash (hpositiveEq.trans (decide_eq_true hpositive))), ?_⟩
          intro hraw
          have hrow : r.input.row = cut.input.row := by
            change r.input.rows r.input.selected = cut.input.rows cut.input.selected
            rw [hsource.2.1, hsource.2.2.1, hcutRows, hcutSelected]
          have hfirstR : FollowerCutoffScan.firstCutoff p rate.eta.val payload.sigma
              (FollowerCutoffScan.completeRowProposalBit p rate.eta.val r.input.row) = u := by
            rw [hrow]
            exact hfirst
          have hub : u ≤ r.input.time.val + 1 := by
            change r.input.time.val + 1 = u + a.val at hcalendar
            omega
          have hreceive := current_word_reception source rewards C_star C_h k r hrElem i choice memory
            payload u selected hselected hpending.1 hc hu hdown hexpected haTest hfirstR hub hraw
          obtain ⟨accepted, recovered, post, hscan, hchecked, hregs, hprefix, hlast, hstatus,
            hbuffer, hbatch, hdiagRaw, houtcome, houtput, hnext, hretained⟩ := hreceive
          refine ⟨accepted, recovered, post, hscan, hchecked, hregs, hprefix, hlast, hstatus,
            hbuffer, hbatch, hdiagRaw, houtcome, houtput, hnext, hretained,
            a.val + 1, rfl, Nat.succ_le_of_lt a.isLt, ?_⟩
          change (Z (a.val + 1)).followers i = .ordinary post memory
          rw [← (hZrecord a).2]
          exact hnext

end Bandits.Support.ReferenceFirstReplacementCollectionOldDownSenderReadiness

end
