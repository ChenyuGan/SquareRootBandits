/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionLateDownReplyHistory
public import Bandits.Support.ReferenceCollectionUpReceiverLocal

/-!
# Actual first-collection late-UP sender

Sources: `sources/zip4/manuscript/05_binary_transport.tex:36-53,70-124`,
`sources/zip4/manuscript/06_interruptions.tex:246-295,327-348`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:92-109,151-157`.

The actual late retained-DOWN producer supplies the original collection
boundary and the follower's fixed terminal reply. This module constructs its
admissible UP record once, then identifies the actual sender word on earlier
selected UP preparations whenever the computed endpoint remains ordinary.
The statement retains the actual dagger and terminal alternatives and makes
no delivery or acceptance claim.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferencePrelaunchFollower
open Bandits.Support.ReferenceFollowerReplyChronology
open Bandits.Support.ReferenceFollowerFixedReply

namespace Bandits.Support.ReferenceFirstCollectionLateUpSender

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

private theorem connected_endpoint_unique
    {initial final₁ final₂ : ReferenceActivePhysicalStep.State p rate}
    {records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))}
    (h₁ : ReferenceActivePhysicalHorizon.Connected initial records final₁)
    (h₂ : ReferenceActivePhysicalHorizon.Connected initial records final₂) :
    final₁ = final₂ := by
  induction records generalizing initial final₁ final₂ with
  | nil =>
      change final₁ = initial at h₁
      change final₂ = initial at h₂
      exact h₁.trans h₂.symm
  | cons record rest ih =>
      simp only [ReferenceActivePhysicalHorizon.Connected] at h₁ h₂
      exact ih h₁.2 h₂.2

private def runRecordAt (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start index : ℕ) (hspan : start + (index + 1) ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start) :
    ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) :=
  let prefixRun := ReferenceActivePhysicalHorizon.run initial rows selected rewards start index
    (by omega) active
  let input := ReferenceActivePhysicalHorizon.roundInputAt initial rows selected rewards start
    active prefixRun ⟨start + index, by omega, by omega⟩
  ⟨input, ReferenceActivePhysicalStep.step input, rfl⟩

private theorem run_successor_equations (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start index : ℕ) (hspan : start + (index + 1) ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start) :
    (ReferenceActivePhysicalHorizon.run initial rows selected rewards start (index + 1)
      hspan active).finalState =
        (runRecordAt initial rows selected rewards start index hspan active).output.next ∧
    (ReferenceActivePhysicalHorizon.run initial rows selected rewards start (index + 1)
      hspan active).records =
        (ReferenceActivePhysicalHorizon.run initial rows selected rewards start index
          (by omega) active).records ++
          [runRecordAt initial rows selected rewards start index hspan active] := by
  rw [ReferenceActivePhysicalHorizon.run_successor_step]
  have heq := ReferenceActivePhysicalHorizon.foldRound_equations initial rows selected rewards start
    active (ReferenceActivePhysicalHorizon.run initial rows selected rewards start index
      (by omega) active) ⟨start + index, by omega, by omega⟩
  simpa [runRecordAt, ReferenceActivePhysicalHorizon.roundInputAt] using heq

private theorem run_prefix_records (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start total : ℕ) (hspan : start + total ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (n : ℕ) (hn : n ≤ total) :
    (ReferenceActivePhysicalHorizon.run initial rows selected rewards start total hspan active).records.take n =
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start n
        (by omega) active).records := by
  revert hspan hn
  induction total with
  | zero =>
      intro hspan hn
      have hn0 : n = 0 := by omega
      subst n
      rw [List.take_zero, ReferenceActivePhysicalHorizon.run_zero_records]
  | succ total ih =>
      intro hspan hn
      by_cases heq : n = total + 1
      · subst n
        apply List.take_of_length_le
        rw [ReferenceActivePhysicalHorizon.run_record_count]
      · have hn' : n ≤ total := by omega
        rw [(run_successor_equations initial rows selected rewards start total hspan active).2,
          List.take_append_of_le_length (by
            rw [ReferenceActivePhysicalHorizon.run_record_count]
            exact hn')]
        exact ih (by omega) hn'

private theorem run_prefix_endpoints (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start total : ℕ) (hspan : start + total ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (n : ℕ) (hn : n < total) :
    (ReferenceActivePhysicalHorizon.run initial rows selected rewards start n
      (by omega) active).finalState =
      ((ReferenceActivePhysicalHorizon.run initial rows selected rewards start total hspan active).records[n]'(by
        rw [ReferenceActivePhysicalHorizon.run_record_count]
        exact hn)).input.state ∧
    (ReferenceActivePhysicalHorizon.run initial rows selected rewards start (n + 1)
      (by omega) active).finalState =
      ((ReferenceActivePhysicalHorizon.run initial rows selected rewards start total hspan active).records[n]'(by
        rw [ReferenceActivePhysicalHorizon.run_record_count]
        exact hn)).output.next := by
  let full := ReferenceActivePhysicalHorizon.run initial rows selected rewards start total hspan active
  let prefixRun := ReferenceActivePhysicalHorizon.run initial rows selected rewards start n
    (by omega) active
  let nextPrefix := ReferenceActivePhysicalHorizon.run initial rows selected rewards start (n + 1)
    (by omega) active
  have hconnected := ReferenceActivePhysicalHorizon.run_connected initial rows selected rewards
    start total hspan active
  have hnFull : n < full.records.length := by
    dsimp [full]
    rw [ReferenceActivePhysicalHorizon.run_record_count]
    exact hn
  have htake := ReferenceFollowerReplyChronology.connected_take_to_input hconnected n hnFull
  have hprefix := run_prefix_records initial rows selected rewards start total hspan active n
    (by omega)
  have hinput := connected_endpoint_unique prefixRun.connected (by
    rw [← hprefix]
    exact htake)
  have hchainPrefix := ReferenceFollowerReplyChronology.connected_take_to_input
    hconnected n hnFull
  have htakeSucc : full.records.take (n + 1) = full.records.take n ++ [full.records[n]] := by
    rw [List.take_add_one]
    simp [hnFull]
  have hchainNext : ReferenceActivePhysicalHorizon.Connected initial
      (full.records.take (n + 1)) (full.records[n].output.next) := by
    rw [htakeSucc]
    exact ReferenceActivePhysicalHorizon.Connected.append_one
      (full.records.take n) full.records[n] hchainPrefix rfl
  have hrecordsNext := run_prefix_records initial rows selected rewards start total hspan active
    (n + 1) (by omega)
  have hnext := connected_endpoint_unique nextPrefix.connected (by
    rw [← hrecordsNext]
    exact hchainNext)
  exact ⟨hinput, hnext⟩

private theorem actual_ordinary_state_domain
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1)) (out : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hnext : record.output.next.followers i = .ordinary out memory) :
    ActiveFollowerLifecycle.localStateDomainValid out := by
  rcases record with ⟨input, output, houtput⟩
  cases houtput
  change (ReferenceActivePhysicalStep.finishFollower
      (ReferenceActivePhysicalStep.prepare input).coordinator.downView
      ((ReferenceActivePhysicalStep.prepare input).followers.followers i)
      ((ReferenceActivePhysicalStep.prepare input).feedback.observations
        (PublicDiscreteDraws.followerPlayer p.two_le_m i))).configuration =
      .ordinary out memory at hnext
  let prepared := ReferenceActivePhysicalStep.prepare input
  let choice := prepared.followers.followers i
  let observation := prepared.feedback.observations
    (PublicDiscreteDraws.followerPlayer p.two_le_m i)
  obtain ⟨choiceState, choiceMemory, post, hchoice, hrecord, hfinish, _, _⟩ :=
    ReferenceFollowerReplyChronology.finishFollower_ordinary_inversion
      prepared.coordinator.downView choice observation out memory hnext
  cases hrelease : ActiveFollowerLifecycle.releaseAfterService rate.eta choice.follower
      choice.time (ActiveFollowerLifecycle.publicRowOfCompleteRow choice.row choice.time)
      observation choiceState post with
  | error reason =>
      simp [DeclaredFollowerLocalRound.releaseAndFinish, hrelease] at hfinish
  | ok afterRelease =>
      cases hround : ActiveFollowerLifecycle.finishRound rate.eta choice.time choice.row
          afterRelease choiceMemory with
      | error reason =>
          simp [DeclaredFollowerLocalRound.releaseAndFinish, hrelease, hround] at hfinish
      | ok pair =>
          have hpair : pair = (out, memory) := by
            simpa [DeclaredFollowerLocalRound.releaseAndFinish, hrelease, hround] using hfinish
          have hdomain : ActiveFollowerLifecycle.localStateDomainValid afterRelease := by
            by_contra hbad
            rw [ActiveFollowerLifecycle.finishRound_invalid_domain rate.eta choice.time
              choice.row afterRelease choiceMemory hbad] at hround
            cases hround
          have hframe := ActiveFollowerLifecycle.finishRound_frame rate.eta choice.time
            choice.row afterRelease pair.1 choiceMemory pair.2 hround
          have hpairState : pair.1 = out := congrArg Prod.fst hpair
          have hout : out = afterRelease := hpairState.symm.trans hframe
          rw [← hout] at hdomain
          exact hdomain

private theorem actual_query_sender_word
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1)) (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (out : ReferencePrelaunchFollower.State p rate.eta)
    (hconfiguration : (ReferenceFollowerFixedReply.actualChoice record i).configuration =
      .ordinary state memory)
    (hunoccupied : state.status = .unoccupied)
    (hreply : ReferenceFollowerReplyChronology.reply state =
      ReferenceFollowerReplyChronology.reply out)
    (U : OrdinaryMessageCodec.UpRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))
    (hUfields : U.val = ActiveFollowerQueueOperation.upOfferFields out)
    (hslot : PublicDiscreteDraws.slotDraw (record.input.row.2 record.input.time).1 =
      PublicDiscreteDraws.upSlot)
    (hselected : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
      (record.input.row.2 record.input.time).1 = i) :
    ActiveFollowerQueueOperation.checkedUpOffer rate.eta i record.input.row
      (record.input.state.activations i) record.input.time state = .offer U ∧
    ActiveFollowerQueueOperation.checkedUpOffer rate.eta
      (ReferenceFollowerFixedReply.actualChoice record i).follower
      (ReferenceFollowerFixedReply.actualChoice record i).row
      (ReferenceFollowerFixedReply.actualChoice record i).activation
      (ReferenceFollowerFixedReply.actualChoice record i).time state = .offer U ∧
    ReferenceActiveAffinePositiveTest.upSent record.input =
      some (ActiveFollowerArmChoice.offeredUpWord rate.eta U) ∧
    ReferenceActivePhysicalStep.upExpected (ReferenceActivePhysicalStep.prepare record.input) =
      some (ActiveFollowerArmChoice.offeredUpWord rate.eta U) ∧
    (ReferenceActiveAffinePositiveTest.upPositive record.input = true →
      AffineChannelLaw.affineHash ((record.input.row.2 record.input.time).2 (1, i))
        (ActiveFollowerArmChoice.offeredUpWord rate.eta U) = 1) := by
  have hprep : ReferenceFollowerFixedReply.actualChoice record i =
      DeclaredFollowerLocalRound.prepare rate i record.input.row
        (record.input.state.activations i) record.input.time (record.input.active i)
        (record.input.state.followers i) :=
    record.output.preparation.followers.followers_eq i
  have haligned := record.output.preparation.follower_alignment i
  have hspec := ReferenceUpPhysicalHashRule.prepare_arm_spec i record.input.row
    (record.input.state.activations i) record.input.time (record.input.active i)
    (record.input.state.followers i)
  simp only [← hprep, hconfiguration] at hspec
  have hnotFailure : ActiveFollowerQueueOperation.checkedUpOffer rate.eta i
      record.input.row (record.input.state.activations i) record.input.time state ≠ .failure := by
    intro hfailure
    simp only [hfailure] at hspec
  have hselectedUp : ActiveFollowerQueueOperation.selectedUpRound i record.input.row
      (record.input.state.activations i) record.input.time ∧ state.status = .unoccupied := by
    exact ⟨⟨record.input.active i, hslot, hselected⟩, hunoccupied⟩
  have hdomain : ActiveFollowerQueueOperation.stateInputDomain state := by
    by_contra hbad
    apply hnotFailure
    simp [ActiveFollowerQueueOperation.checkedUpOffer, hbad]
  have hadmissible : OrdinaryMessageCodec.upAdmissible
      (ReferencePrelaunchFollower.codecParams p rate.eta)
      (ActiveFollowerQueueOperation.upOfferFields state) := by
    by_contra hbad
    apply hnotFailure
    simp [ActiveFollowerQueueOperation.checkedUpOffer, hdomain, hselectedUp, hbad]
  let offered : OrdinaryMessageCodec.UpRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta) :=
    ⟨ActiveFollowerQueueOperation.upOfferFields state, hadmissible⟩
  have hoff : ActiveFollowerQueueOperation.checkedUpOffer rate.eta i record.input.row
      (record.input.state.activations i) record.input.time state = .offer offered := by
    simp [ActiveFollowerQueueOperation.checkedUpOffer, hdomain, hselectedUp, hadmissible, offered]
  have hoffFields := ActiveFollowerQueueOperation.checkedUpOffer_fields rate.eta i
    record.input.row (record.input.state.activations i) record.input.time state offered hoff
  have hreplyParts : state.lastDown = out.lastDown ∧ state.S = out.S ∧
      state.delta = out.delta ∧ state.backlog = out.backlog := by
    simpa only [ReferenceFollowerReplyChronology.reply, Prod.mk.injEq] using hreply
  have hstartEq := ReferenceFollowerReplyChronology.acceptedStart_eq_of_reply_eq hreply
  have hfields : ActiveFollowerQueueOperation.upOfferFields state =
      ActiveFollowerQueueOperation.upOfferFields out := by
    apply OrdinaryMessageCodec.UpFields.ext
    · exact hstartEq
    · exact hreplyParts.2.1
    · exact hreplyParts.2.2.1
    · exact hreplyParts.2.2.2
  have hval : offered.val = U.val := by
    calc
      offered.val = ActiveFollowerQueueOperation.upOfferFields state := hoffFields
      _ = ActiveFollowerQueueOperation.upOfferFields out := hfields
      _ = U.val := hUfields.symm
  have hoffU : offered = U := Subtype.ext hval
  have hcheckedOriginal : ActiveFollowerQueueOperation.checkedUpOffer rate.eta i
      record.input.row (record.input.state.activations i) record.input.time state = .offer U := by
    rw [hoffU] at hoff
    exact hoff
  have hcheckedPrepared : ActiveFollowerQueueOperation.checkedUpOffer rate.eta
      (ReferenceFollowerFixedReply.actualChoice record i).follower
      (ReferenceFollowerFixedReply.actualChoice record i).row
      (ReferenceFollowerFixedReply.actualChoice record i).activation
      (ReferenceFollowerFixedReply.actualChoice record i).time state = .offer U := by
    have hargs : ActiveFollowerQueueOperation.checkedUpOffer rate.eta
        (ReferenceFollowerFixedReply.actualChoice record i).follower
        (ReferenceFollowerFixedReply.actualChoice record i).row
        (ReferenceFollowerFixedReply.actualChoice record i).activation
        (ReferenceFollowerFixedReply.actualChoice record i).time state =
          ActiveFollowerQueueOperation.checkedUpOffer rate.eta i record.input.row
            (record.input.state.activations i) record.input.time state := by
      dsimp only [ReferenceFollowerFixedReply.actualChoice]
      rw [haligned.2.1, haligned.1, haligned.2.2.2, haligned.2.2.1]
    rw [hargs]
    exact hcheckedOriginal
  have hselectedIndex : ReferenceActivePhysicalStep.upSenderIndex record.input = i := by
    rw [ReferenceActiveAffinePositiveTest.upSenderIndex_eq_draw, hselected]
  have hExpectedFlat := ReferenceFollowerFixedReply.actualUpExpected_eq_encoded_offer
    record i hselectedIndex state memory hconfiguration U hcheckedPrepared
  have hprepOutput : record.output.preparation =
      ReferenceActivePhysicalStep.prepare record.input := by
    rw [record.output_eq]
    rfl
  have hcodec : CoordinatorCollectionLedger.codecParams p rate.eta.val =
      ReferencePrelaunchFollower.codecParams p rate.eta := by
    rfl
  cases hcodec
  rw [ReferenceFollowerFixedReply.actualUpExpected, hprepOutput] at hExpectedFlat
  have hexpected : ReferenceActivePhysicalStep.upExpected
      (ReferenceActivePhysicalStep.prepare record.input) =
        some (ActiveFollowerArmChoice.offeredUpWord rate.eta U) := by
    exact hExpectedFlat
  have hsent : ReferenceActiveAffinePositiveTest.upSent record.input =
      some (ActiveFollowerArmChoice.offeredUpWord rate.eta U) := by
    simpa only [ReferenceActiveAffinePositiveTest.upSent] using hexpected
  refine ⟨hcheckedOriginal, hcheckedPrepared, hsent, hexpected, ?_⟩
  intro hpositive
  have hhash := ReferenceUpPhysicalHashRule.upPositive_hash_one record.input
    (ActiveFollowerArmChoice.offeredUpWord rate.eta U) hsent hpositive
  rw [hselectedIndex] at hhash
  exact hhash

/-- The actual late retained-DOWN sender record and every earlier selected
UP sender word on the computed ordinary endpoint branch. The sole outer
premises are the original construction branch and finite active prefix
hypotheses; all records, states, rows, replies, and selected-round facts are
produced from the original run.
-/
theorem actual_first_collection_late_up_sender
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
    let x0 := ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate
    let b0 := ReferenceInitializationRun.output x0
    let s := ReferenceInitializationRun.elapsed p b0.completed
    let I := ReferenceFirstCollectionEpochAlignment.actualLaunchState
      rate source rewards C_star C_h hcross
    let active := (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
      rate source rewards C_star C_h hcross).1
    let E := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
      rate source rewards C_star C_h hcross count hspan
    let W := ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records
    let w := W.length
    let B := ReferenceCollectionPhaseHistory.collectionWindow E.records w
    let u := s + w + 1
    ∃ (cutoffRecord : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
      (suffix : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
      (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
      (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
      (base : Fin (p.m - 1) → ℕ)
      (P0 : ReferenceActivePhysicalStep.Payload rate)
      (birth : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)),
      E.records = W ++ cutoffRecord :: suffix ∧
      (∃ hindex : w < E.records.length,
        cutoffRecord = E.records[w]'hindex) ∧
      cutoffRecord.input.time.val = s + w ∧
      cutoffRecord.input.state.coordinator = .live registers owned base ∧
      ReferenceCollectionPhaseHistory.cutoffChosen cutoffRecord.input = true ∧
      P0 = registers.payload ∧ P0.sigma.val = s ∧
      (∀ arm, P0.queues arm = 0) ∧
      FollowerCutoffScan.firstCutoff p rate.eta.val P0.sigma
        (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
          (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source))) = u ∧
      birth ∈ E.records ∧
      ReferenceAssignmentPayloadPersistence.InstallationBirth birth P0 ∧
      birth.input.time.val = s ∧
      (∀ k : Fin B.length,
        E.records[w + k.val]? = some B[k.val] ∧
          B[k.val].input.time.val + 1 = u + k.val) ∧
      ∀ (k : Fin B.length) (i : Fin (p.m - 1))
        (M : ReferenceAcceptedUpFollowerHistory.DownRecord (p := p) (rate := rate)),
        let j := w + k.val
        let r := B[k.val]
        ReferenceAcceptedUpFollowerHistory.RetainedDown r i M →
        r.output.next.followers i = .dagger ∨
        r.output.next.coordinator = .dagger ∨
        ∃ (out : ReferencePrelaunchFollower.State p rate.eta)
          (memory : ActiveFollowerLifecycle.LocalMemory p)
          (ledger : ReferenceActivePhysicalStep.Ledger rate)
          (saved : Option (Fin p.T × Bool)),
          r.output.next.followers i = .ordinary out memory ∧
          r.output.next.coordinator = .collection P0 ledger saved ∧
          out.status = .unoccupied ∧
          let V := fun h => QueueReplay.replay (4 * rate.n) (0, 0)
            (ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords E.records i j M h)
          ReferenceFollowerReplyChronology.reply out =
            (some M, (V w).1, (V w).1 - (V (w - 1)).1, (V w).2) ∧
          M = P0.downRecord i ∧ M.val.sigma = s + 1 ∧
          (∃ (logged : ReferencePrelaunchFollower.State p rate.eta)
            (cutD : ReferenceDownReception.ReferenceDownCutOutput p rate)
            (after : ReferencePrelaunchFollower.State p rate.eta)
            (raw : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p)))
            (scan : FollowerCutoffScan.ScanResult p.T)
            (replayedRegisters : ℕ × ℕ) (lastService : ℕ),
            cutD.outcome = .accepted logged after raw M scan replayedRegisters lastService ∧
            j < count ∧ ∃ (n0 : ℕ),
              n0 = scan.endpoint - M.val.sigma ∧ n0 = w ∧
              ActiveFollowerDownAcceptance.checkedRecovery p rate M logged scan.endpoint =
                .ok ⟨replayedRegisters, lastService⟩) ∧
          out.lastDown = some M ∧
          ReferencePrelaunchFollower.acceptedStart out = s + 1 ∧
          let b := j + 1
          let Wlate := (E.records.drop b).takeWhile
            (fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input)
          ∃ (hb : b ≤ count) (hbspan : s + b ≤ p.T)
            (hlate : Wlate.length ≤ count - b),
            let C := fun (h : ℕ) (hh : h ≤ Wlate.length) =>
              ReferenceActivePhysicalHorizon.run I source.1.2
                (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s (b + h)
                (by
                  have hbound : b + h ≤ count := by omega
                  have hstart : s + count ≤ p.T := by
                    dsimp only [s, b0, x0]
                    exact hspan
                  omega) active
            (ReferenceActivePhysicalHorizon.run I source.1.2
              (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s b
              hbspan active).finalState = r.output.next ∧
            Wlate = B.drop (k.val + 1) ∧
            (∀ h (hh : h < Wlate.length),
              E.records[b + h]? = some (Wlate[h]'hh) ∧
                (Wlate[h]'hh).input.time.val = u + k.val + h) ∧
            (∀ h (hh : h ≤ Wlate.length),
              ((C h hh).finalState.coordinator = .dagger ∨
                ∃ moving movingSaved,
                  (C h hh).finalState.coordinator = .collection P0 moving movingSaved) ∧
              ((C h hh).finalState.followers i = .dagger ∨
                ∃ state stateMemory,
                  (C h hh).finalState.followers i = .ordinary state stateMemory ∧
                  state.status = .unoccupied ∧
                  ReferenceFollowerReplyChronology.reply state =
                    (some M, (V w).1, (V w).1 - (V (w - 1)).1, (V w).2))) ∧
            (∀ h (_hh : h < Wlate.length) (hrecord : b + h < E.records.length),
              ∀ start,
                ¬ ReferenceFollowerReplyChronology.appliedDown
                  (E.records.get ⟨b + h, hrecord⟩) i start) ∧
            (∀ h (_hh : h ≤ Wlate.length) (hrecord : b + h < E.records.length),
              (h = Wlate.length →
                ReferenceCollectionPhaseHistory.laterChosen
                  ((E.records.get ⟨b + h, hrecord⟩).input) = true) ∧
              ((ReferenceFollowerFixedReply.actualChoice
                  (E.records.get ⟨b + h, hrecord⟩) i).configuration = .dagger ∨
                ∃ state stateMemory,
                  (ReferenceFollowerFixedReply.actualChoice
                    (E.records.get ⟨b + h, hrecord⟩) i).configuration =
                      .ordinary state stateMemory ∧
                  state.status = .unoccupied ∧
                  ReferenceFollowerReplyChronology.reply state =
                    (some M, (V w).1, (V w).1 - (V (w - 1)).1, (V w).2))) ∧
            ∃ (U : OrdinaryMessageCodec.UpRecord
              (ReferencePrelaunchFollower.codecParams p rate.eta)),
              U.val = ActiveFollowerQueueOperation.upOfferFields out ∧
              U.val = OrdinaryMessageCodec.UpFields.mk (s + 1)
                (V w).1 ((V w).1 - (V (w - 1)).1) (V w).2 ∧
              0 < U.val.sigma ∧
              ∀ n (hn : n ≤ Wlate.length),
                let Cn := C n hn
                ((Cn.finalState.coordinator = .dagger ∨
                  ∃ moving movingSaved,
                    Cn.finalState.coordinator = .collection P0 moving movingSaved) ∧
                 (Cn.finalState.followers i = .dagger ∨
                  ∃ endpoint endpointMemory,
                    Cn.finalState.followers i = .ordinary endpoint endpointMemory ∧
                    endpoint.status = .unoccupied ∧
                    ReferenceFollowerReplyChronology.reply endpoint =
                      ReferenceFollowerReplyChronology.reply out ∧
                    ∀ h (hh : h < n),
                      ∃ choice choiceMemory,
                        let rh := Wlate[h]'(by omega)
                        (ReferenceFollowerFixedReply.actualChoice rh i).configuration =
                          .ordinary choice choiceMemory ∧
                        choice.status = .unoccupied ∧
                        ReferenceFollowerReplyChronology.reply choice =
                          ReferenceFollowerReplyChronology.reply out ∧
                        ∀ (_hslot : PublicDiscreteDraws.slotDraw
                            (rh.input.row.2 rh.input.time).1 = PublicDiscreteDraws.upSlot)
                          (_hselected : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m
                            p.m_lt_K (rh.input.row.2 rh.input.time).1 = i),
                          ActiveFollowerQueueOperation.checkedUpOffer rate.eta i rh.input.row
                            (rh.input.state.activations i) rh.input.time choice = .offer U ∧
                          ActiveFollowerQueueOperation.checkedUpOffer rate.eta
                            (ReferenceFollowerFixedReply.actualChoice rh i).follower
                            (ReferenceFollowerFixedReply.actualChoice rh i).row
                            (ReferenceFollowerFixedReply.actualChoice rh i).activation
                            (ReferenceFollowerFixedReply.actualChoice rh i).time choice = .offer U ∧
                          ReferenceActiveAffinePositiveTest.upSent rh.input =
                            some (ActiveFollowerArmChoice.offeredUpWord rate.eta U) ∧
                          ReferenceActivePhysicalStep.upExpected
                            (ReferenceActivePhysicalStep.prepare rh.input) =
                              some (ActiveFollowerArmChoice.offeredUpWord rate.eta U) ∧
                          (ReferenceActiveAffinePositiveTest.upPositive rh.input = true →
                            AffineChannelLaw.affineHash
                              ((rh.input.row.2 rh.input.time).2 (1, i))
                              (ActiveFollowerArmChoice.offeredUpWord rate.eta U) = 1))) := by
  classical
  intro x0 b0 s I active E W w B u
  obtain ⟨cutoffRecord, suffix, registers, owned, base, P0, birth,
      hsplit, hindex, htime, hstate, hcutoffChosen, hP0, hP0sigma,
      hP0queues, hfirstCutoff, hbirth, hbirthInstall, hbirthTime,
      hwindow, hqueries⟩ :=
    ReferenceFirstCollectionLateDownReplyHistory.actual_first_collection_late_down_reply_history
      rate source rewards C_star C_h count hcross hspan hshort
  refine ⟨cutoffRecord, suffix, registers, owned, base, P0, birth,
    hsplit, hindex, htime, hstate, hcutoffChosen, hP0, hP0sigma,
    hP0queues, hfirstCutoff, hbirth, hbirthInstall, hbirthTime, hwindow, ?_⟩
  intro k i M j r hretained
  have hquery := hqueries k i M hretained
  rcases hquery with ⟨logged, cutD, after, raw, scan, replayedRegisters, lastService,
      _hinput, _hdown, haccepted, hM, hMsigma, _hMq, _hdownStart, _hscan, _hafterStatus,
      _hafterLastDown, ⟨hjcount, n0, hn0, hn0eq, hchecked⟩,
      ⟨_hregisters, _hlastService, _hafterS, _hafterDelta, _hafterBacklog,
        _hreplyAfter, hnextState⟩⟩
  let V := fun h => QueueReplay.replay (4 * rate.n) (0, 0)
    (ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords E.records i j M h)
  rcases hnextState with ⟨hnextDagger, _hnextCoordinator⟩ |
      ⟨out, memory, hnextOrdinary, houtStatus, houtReply, houtLastDown,
        houtS, houtDelta, houtBacklog, houtStart, hnextCoordinator⟩
  · exact Or.inl hnextDagger
  · have hlastOut : out.lastDown = some M := by
      have h := congrArg Prod.fst houtReply
      simpa only [ReferenceFollowerReplyChronology.reply] using h
    have hreplyOut : ReferenceFollowerReplyChronology.reply out =
        (some M, (V w).1, (V w).1 - (V (w - 1)).1, (V w).2) := by
      simpa only [V] using houtReply
    have hstartOut : ReferencePrelaunchFollower.acceptedStart out = s + 1 := by
      simpa only [hP0sigma, s, b0, x0] using houtStart
    rcases hnextCoordinator with hcoordDagger |
        ⟨ledger, saved, hcoordCollection, hsuffix⟩
    · exact Or.inr (Or.inl hcoordDagger)
    · let b := j + 1
      let Wlate := (E.records.drop b).takeWhile
        (fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input)
      rcases hsuffix with ⟨hb, hbspan, hcoordPrefix, hseedPrefix, hWlate,
          htimeLookup, hprefixFacts, hnoAppliedFacts, hboundaryFacts,
          _hofferFacts, _hpairOffers⟩
      have hwindowK := hwindow k
      have hjlt : j < E.records.length := by
        have h := (List.getElem?_eq_some_iff.mp hwindowK.1).1
        simpa only [j] using h
      have hgetQuery : E.records[j]? = some r := by
        simpa only [j, r] using hwindowK.1
      have hRunEq :
          E = ReferenceActivePhysicalHorizon.run I source.1.2
            (ActualInitializationPhysicalStep.selectedRowIndex p source)
            rewards s count hspan active := by
        dsimp only [E, I, s, b0, x0, active,
          ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun]
      have hstartSpan : s + count ≤ p.T := by
        dsimp only [s, b0, x0]
        exact hspan
      have hjSpan : s + (j + 1) ≤ p.T := by
        calc
          s + (j + 1) ≤ s + count :=
            Nat.add_le_add_left (Nat.succ_le_of_lt hjcount) s
          _ ≤ p.T := hstartSpan
      have hRunGet :
          (ReferenceActivePhysicalHorizon.run I source.1.2
            (ActualInitializationPhysicalStep.selectedRowIndex p source)
            rewards s count hspan active).records[j]? = some r := by
        rw [← hRunEq]
        exact hgetQuery
      have hRunLt :
          j < (ReferenceActivePhysicalHorizon.run I source.1.2
            (ActualInitializationPhysicalStep.selectedRowIndex p source)
            rewards s count hspan active).records.length := by
        rw [← hRunEq]
        exact hjlt
      have hRunRecord :
          (ReferenceActivePhysicalHorizon.run I source.1.2
            (ActualInitializationPhysicalStep.selectedRowIndex p source)
            rewards s count hspan active).records[j]'hRunLt = r := by
        rw [List.getElem?_eq_getElem hRunLt] at hRunGet
        exact Option.some.inj hRunGet
      have hsuccessor := run_prefix_endpoints I source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s count
        hstartSpan active j hjcount
      have hprefixOutput :
          (ReferenceActivePhysicalHorizon.run I source.1.2
            (ActualInitializationPhysicalStep.selectedRowIndex p source)
            rewards s (j + 1) hjSpan active).finalState = r.output.next := by
        calc
          (ReferenceActivePhysicalHorizon.run I source.1.2
            (ActualInitializationPhysicalStep.selectedRowIndex p source)
            rewards s (j + 1) hjSpan active).finalState =
              ((ReferenceActivePhysicalHorizon.run I source.1.2
                (ActualInitializationPhysicalStep.selectedRowIndex p source)
                rewards s count hspan active).records[j]'hRunLt).output.next :=
            hsuccessor.2
          _ = r.output.next := by rw [hRunRecord]
      have hbPrefix :
          (ReferenceActivePhysicalHorizon.run I source.1.2
            (ActualInitializationPhysicalStep.selectedRowIndex p source)
            rewards s b hbspan active).finalState = r.output.next := by
        change (ReferenceActivePhysicalHorizon.run I source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source)
          rewards s (j + 1) hjSpan active).finalState = _
        exact hprefixOutput
      have hcountE : E.records.length = count := by
        rw [hRunEq]
        exact ReferenceActivePhysicalHorizon.run_record_count I source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source)
          rewards s count hspan active
      have hlate : Wlate.length ≤ count - b := by
        calc
          Wlate.length ≤ (E.records.drop b).length :=
            (List.takeWhile_prefix _).length_le
          _ = count - b := by rw [List.length_drop, hcountE]
      have hlocalDomain := actual_ordinary_state_domain r i out memory hnextOrdinary
      have hregisterBounds : out.S ≤ p.T * D p ∧ out.delta ≤ D p ∧
          out.backlog ≤ p.T * D p := by
        simpa only [ActiveFollowerLifecycle.localStateDomainValid,
          ActiveFollowerLifecycle.serviceRegistersValid] using hlocalDomain.1
      have hMsigmaBounds : 1 ≤ M.val.sigma ∧ M.val.sigma ≤ p.T :=
        ⟨M.property.1, M.property.2.1⟩
      have hadmissible : OrdinaryMessageCodec.upAdmissible
          (ReferencePrelaunchFollower.codecParams p rate.eta)
          (OrdinaryMessageCodec.UpFields.mk (s + 1) (V w).1
            ((V w).1 - (V (w - 1)).1) (V w).2) := by
        apply Or.inr
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · rw [← hMsigma]
          exact hMsigmaBounds.1
        · rw [← hMsigma]
          exact hMsigmaBounds.2
        · rw [← houtS]
          exact hregisterBounds.1
        · rw [← houtDelta]
          exact hregisterBounds.2.1
        · rw [← houtBacklog]
          exact hregisterBounds.2.2
      let U : OrdinaryMessageCodec.UpRecord
          (ReferencePrelaunchFollower.codecParams p rate.eta) :=
        ⟨OrdinaryMessageCodec.UpFields.mk (s + 1) (V w).1
          ((V w).1 - (V (w - 1)).1) (V w).2, hadmissible⟩
      have hUfields : U.val = ActiveFollowerQueueOperation.upOfferFields out := by
        apply OrdinaryMessageCodec.UpFields.ext
        · change s + 1 = ReferencePrelaunchFollower.acceptedStart out
          exact hstartOut.symm
        · simpa [U, ActiveFollowerQueueOperation.upOfferFields, V] using houtS.symm
        · simpa [U, ActiveFollowerQueueOperation.upOfferFields, V] using houtDelta.symm
        · simpa [U, ActiveFollowerQueueOperation.upOfferFields, V] using houtBacklog.symm
      have hUpositive : 0 < U.val.sigma := by
        simp [U]
      have hRecovery :
          ∃ (logged : ReferencePrelaunchFollower.State p rate.eta)
            (cutD : ReferenceDownReception.ReferenceDownCutOutput p rate)
            (after : ReferencePrelaunchFollower.State p rate.eta)
            (raw : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p)))
            (scan : FollowerCutoffScan.ScanResult p.T)
            (replayedRegisters : ℕ × ℕ) (lastService : ℕ),
            cutD.outcome = .accepted logged after raw M scan replayedRegisters lastService ∧
            j < count ∧ ∃ (n0 : ℕ),
              n0 = scan.endpoint - M.val.sigma ∧ n0 = w ∧
              ActiveFollowerDownAcceptance.checkedRecovery p rate M logged scan.endpoint =
                .ok ⟨replayedRegisters, lastService⟩ := by
        exact ⟨logged, cutD, after, raw, scan, replayedRegisters, lastService,
          haccepted, ⟨hjcount, ⟨n0, hn0, hn0eq, hchecked⟩⟩⟩
      refine Or.inr (Or.inr ⟨out, memory, ledger, saved,
        hnextOrdinary, hcoordCollection, houtStatus, hreplyOut, hM, hMsigma,
        hRecovery, hlastOut, hstartOut, hb, hbspan, hlate, hbPrefix, hWlate, htimeLookup,
        hprefixFacts, hnoAppliedFacts, hboundaryFacts, U, hUfields, ?_, ?_, ?_⟩)
      · rfl
      · exact hUpositive
      · intro n hn
        have hbn : b + n ≤ count := by
          have hrest : n ≤ count - b := Nat.le_trans hn hlate
          omega
        let C := fun (h : ℕ) (hh : h ≤ Wlate.length) =>
          ReferenceActivePhysicalHorizon.run I source.1.2
            (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s (b + h)
            (by
              have hrest : h ≤ count - b := Nat.le_trans hh hlate
              have hbound : b + h ≤ count := by omega
              exact Nat.le_trans (Nat.add_le_add_left hbound s) hstartSpan)
            active
        have hprefixN := hprefixFacts n hn
        refine ⟨hprefixN.1, ?_⟩
        rcases hprefixN.2 with hendpointDagger |
            ⟨endpoint, endpointMemory, hendpoint, hendpointStatus, hendpointReply⟩
        · exact Or.inl hendpointDagger
        · refine Or.inr ⟨endpoint, endpointMemory, hendpoint, hendpointStatus,
            hendpointReply.trans hreplyOut.symm, ?_⟩
          intro h hh
          have hlateIndex : h < Wlate.length := Nat.lt_of_lt_of_le hh hn
          let rh := Wlate[h]'hlateIndex
          have hlookup := (htimeLookup h hlateIndex).1
          have hrecord : b + h < E.records.length :=
            (List.getElem?_eq_some_iff.mp hlookup).1
          have hrecordE : E.records.get ⟨b + h, hrecord⟩ = rh := by
            have hget := List.getElem?_eq_getElem hrecord
            rw [hget] at hlookup
            exact Option.some.inj hlookup
          have hqCn : b + h < (C n hn).records.length := by
            rw [ReferenceActivePhysicalHorizon.run_record_count]
            omega
          have hprefixRecords : (C n hn).records = E.records.take (b + n) := by
            change (ReferenceActivePhysicalHorizon.run I source.1.2
              (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s (b + n)
              (by
                have hbound : b + n ≤ count := hbn
                exact Nat.le_trans (Nat.add_le_add_left hbound s) hstartSpan)
              active).records = _
            calc
              (ReferenceActivePhysicalHorizon.run I source.1.2
                (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s (b + n)
                (by
                  have hbound : b + n ≤ count := hbn
                  exact Nat.le_trans (Nat.add_le_add_left hbound s) hstartSpan)
                active).records =
                  (ReferenceActivePhysicalHorizon.run I source.1.2
                    (ActualInitializationPhysicalStep.selectedRowIndex p source)
                    rewards s count hspan active).records.take (b + n) := by
                symm
                exact run_prefix_records I source.1.2
                  (ActualInitializationPhysicalStep.selectedRowIndex p source)
                  rewards s count hspan active (b + n) hbn
              _ = E.records.take (b + n) := by rw [← hRunEq]
          have hoptPrefix :
              (C n hn).records[b + h]? = E.records[b + h]? := by
            have h := congrArg (fun records : List
                (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) =>
                  records[b + h]?) hprefixRecords
            rw [List.getElem?_take_of_lt (by omega)] at h
            exact h
          have hqE : b + h < E.records.length := hrecord
          have hrecordPrefix :
              (C n hn).records.get ⟨b + h, hqCn⟩ = E.records.get ⟨b + h, hqE⟩ := by
            have h := hoptPrefix
            rw [List.getElem?_eq_getElem hqCn, List.getElem?_eq_getElem hqE] at h
            exact Option.some.inj h
          obtain ⟨next, nextMemory, hnextOutput, _hstartMono⟩ :=
            ReferenceFollowerReplyChronology.connected_output_chronology
              (C n hn).connected i endpoint endpointMemory hendpoint (b + h) hqCn
          have hnextRh : rh.output.next.followers i = .ordinary next nextMemory := by
            have hEq := hrecordPrefix.trans hrecordE
            rw [← hEq]
            exact hnextOutput
          obtain ⟨choice, choiceMemory, hchoice, _hchoiceMono,
              _hchoiceFrame, _hchoiceDown⟩ :=
            ReferenceFollowerReplyChronology.record_choice_chronology
              rh i next nextMemory hnextRh
          have hboundary := (hboundaryFacts h (Nat.le_of_lt hlateIndex) hrecord).2
          rw [hrecordE] at hboundary
          rcases hboundary with hchoiceDagger |
              ⟨boundary, boundaryMemory, hboundaryChoice, hboundaryStatus,
                hboundaryReply⟩
          · rw [hchoice] at hchoiceDagger
            cases hchoiceDagger
          · have heq := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
              (hchoice.symm.trans hboundaryChoice)
            rcases heq with ⟨rfl, rfl⟩
            have hreplyChoice : ReferenceFollowerReplyChronology.reply choice =
                ReferenceFollowerReplyChronology.reply out :=
              hboundaryReply.trans hreplyOut.symm
            refine ⟨choice, choiceMemory, hchoice, hboundaryStatus, hreplyChoice, ?_⟩
            intro hslot hselected
            have hreplyChoiceEndpoint : ReferenceFollowerReplyChronology.reply choice =
                ReferenceFollowerReplyChronology.reply endpoint :=
              hboundaryReply.trans hendpointReply.symm
            have hendpointReplyOut : ReferenceFollowerReplyChronology.reply endpoint =
                ReferenceFollowerReplyChronology.reply out :=
              hendpointReply.trans hreplyOut.symm
            have hendpointParts : endpoint.lastDown = out.lastDown ∧
                endpoint.S = out.S ∧ endpoint.delta = out.delta ∧
                endpoint.backlog = out.backlog := by
              simpa only [ReferenceFollowerReplyChronology.reply, Prod.mk.injEq]
                using hendpointReplyOut
            have hfieldsOutEndpoint :
                ActiveFollowerQueueOperation.upOfferFields out =
                  ActiveFollowerQueueOperation.upOfferFields endpoint := by
              apply OrdinaryMessageCodec.UpFields.ext
              · exact ReferenceFollowerReplyChronology.acceptedStart_eq_of_reply_eq
                  hendpointReplyOut.symm
              · exact hendpointParts.2.1.symm
              · exact hendpointParts.2.2.1.symm
              · exact hendpointParts.2.2.2.symm
            have hUfieldsEndpoint := hUfields.trans hfieldsOutEndpoint
            exact actual_query_sender_word rh i choice choiceMemory endpoint hchoice
              hboundaryStatus hreplyChoiceEndpoint U hUfieldsEndpoint hslot hselected

end Bandits.Support.ReferenceFirstCollectionLateUpSender

end
