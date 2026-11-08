/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionLateDownReplySeed

/-!
# Actual first-collection late-DOWN fixed-reply history

Sources: sources/zip4/manuscript/05_binary_transport.tex:45-53,70-88,100-124,
sources/zip4/manuscript/06_interruptions.tex:192-209,246-295,327-348, and
sources/zip4/manuscript/appendix_a_local_protocol.tex:139-157.

The one actual cutoff and payload are produced before the late retained-DOWN
queries. On the actual ordinary-follower and collection-coordinator branch,
the existing collection-history results carry that reply through the remaining
original run, including zero-observation prepared UP queries. Dagger and
checked-offer failure paths remain explicit. This is an internal history and
word result, not a source-facing awaited-trace or regret theorem.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferencePrelaunchFollower
open Bandits.Support.ReferenceFollowerFixedReply
open Bandits.Support.ReferenceFollowerReplyChronology
open Bandits.Support.DeclaredFollowerLocalRound

namespace Bandits.Support.ReferenceFirstCollectionLateDownReplyHistory

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

private theorem takeWhile_length_le (α : Type) (pred : α → Bool) (xs : List α) :
    (xs.takeWhile pred).length ≤ xs.length := by
  induction xs with
  | nil => simp
  | cons head tail ih =>
      by_cases hp : pred head
      · simp [List.takeWhile, hp, ih]
      · simp [List.takeWhile, hp]

private theorem takeWhile_drop (α : Type) (pred : α → Bool)
    (xs : List α) (n : ℕ) (hn : n ≤ (xs.takeWhile pred).length) :
    (xs.drop n).takeWhile pred = (xs.takeWhile pred).drop n := by
  induction xs generalizing n with
  | nil => simp
  | cons head tail ih =>
      by_cases hp : pred head
      · cases n with
        | zero => simp [List.takeWhile, hp]
        | succ n =>
            have hn' : n ≤ (tail.takeWhile pred).length := by
              simpa [List.takeWhile, hp] using hn
            simpa [List.takeWhile, hp] using ih n hn'
      · have hn0 : n = 0 := by
          have : n ≤ 0 := by simpa [List.takeWhile, hp] using hn
          omega
        subst n
        simp [List.takeWhile, hp]

private theorem tail_drop (α : Type) (xs : List α) (n : ℕ) :
    (xs.drop n).tail = xs.drop (n + 1) := by
  induction n generalizing xs with
  | zero => cases xs <;> rfl
  | succ n ih =>
      cases xs with
      | nil => simp [List.drop]
      | cons head rest =>
          simpa [List.drop] using ih rest

/-- The actual late retained-DOWN query is joined to its original returned
reply and to the actual suffix of the same first collection. The suffix keeps
every physical record, partial decoder bank, sparse buffer, and actual memory.
Successful local UP offers, when they occur, all flatten the same four-field
reply; no positive-observation or receiver-acceptance premise is used. -/
theorem actual_first_collection_late_down_reply_history
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
    let hactive := (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
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
        ∃ (logged : ReferencePrelaunchFollower.State p rate.eta)
          (cutD : ReferenceDownReception.ReferenceDownCutOutput p rate)
          (after : ReferencePrelaunchFollower.State p rate.eta)
          (raw : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p)))
          (scan : FollowerCutoffScan.ScanResult p.T)
          (replayedRegisters : ℕ × ℕ) (lastService : ℕ),
          (r.output.followers i).downInput = some logged ∧
          (r.output.followers i).down = some cutD ∧
          cutD.outcome = .accepted logged after raw M scan replayedRegisters lastService ∧
          M = P0.downRecord i ∧ M.val.sigma = s + 1 ∧ M.val.q = 0 ∧
          ActiveFollowerDownAcceptance.downStart p rate M = P0.sigma ∧
          scan.endpoint = u ∧ after.status = .unoccupied ∧
          after.lastDown = some M ∧
          (∃ (hindex : j < count) (n0 : ℕ),
            n0 = scan.endpoint - M.val.sigma ∧ n0 = w ∧
            ActiveFollowerDownAcceptance.checkedRecovery p rate M logged scan.endpoint =
              .ok ⟨replayedRegisters, lastService⟩) ∧
          (let V := fun h => QueueReplay.replay (4 * rate.n) (0, 0)
            (ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords E.records i j M h)
           replayedRegisters = V w ∧
           lastService = (V w).1 - (V (w - 1)).1 ∧
           after.S = (V w).1 ∧ after.delta = (V w).1 - (V (w - 1)).1 ∧
           after.backlog = (V w).2 ∧
           ReferenceFollowerReplyChronology.reply after =
             (some M, (V w).1, (V w).1 - (V (w - 1)).1, (V w).2) ∧
           ((r.output.next.followers i = .dagger ∧
               (r.output.next.coordinator = .dagger ∨
                 ∃ actualLedger actualSaved,
                   r.output.next.coordinator = .collection P0 actualLedger actualSaved)) ∨
             (∃ out memory,
               r.output.next.followers i = .ordinary out memory ∧
               out.status = .unoccupied ∧
               ReferenceFollowerReplyChronology.reply out =
                 (some M, (V w).1, (V w).1 - (V (w - 1)).1, (V w).2) ∧
               out.lastDown = some M ∧ out.S = (V w).1 ∧
               out.delta = (V w).1 - (V (w - 1)).1 ∧ out.backlog = (V w).2 ∧
               ReferencePrelaunchFollower.acceptedStart out = s + 1 ∧
               ((r.output.next.coordinator = .dagger) ∨
                 ∃ actualLedger actualSaved,
                   r.output.next.coordinator = .collection P0 actualLedger actualSaved ∧
                   let b := j + 1
                   let Wlate := (E.records.drop b).takeWhile
                     (fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input)
                   let C := fun (h : ℕ) (hh : h ≤ Wlate.length) =>
                     ReferenceActivePhysicalHorizon.run I source.1.2
                       (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s
                       (b + h) (by
                         have hcount : E.records.length = count := by
                           change (ReferenceActivePhysicalHorizon.run I source.1.2
                             (ActualInitializationPhysicalStep.selectedRowIndex p source)
                             rewards s count hspan hactive).records.length = count
                           exact ReferenceActivePhysicalHorizon.run_record_count I source.1.2
                             (ActualInitializationPhysicalStep.selectedRowIndex p source)
                             rewards s count hspan hactive
                         have hdrop : (E.records.drop b).length = count - b := by
                           rw [List.length_drop, hcount]
                         have htake : Wlate.length ≤ (E.records.drop b).length := by
                           change ((E.records.drop b).takeWhile
                             (fun record =>
                               !ReferenceCollectionPhaseHistory.laterChosen record.input)).length ≤
                               (E.records.drop b).length
                           exact takeWhile_length_le _ _
                             (E.records.drop b)
                         have hlength : Wlate.length ≤ count - b := by
                           calc
                             Wlate.length ≤ (E.records.drop b).length := htake
                             _ = count - b := hdrop
                         have hstartSpan : s + count ≤ p.T := by
                           dsimp only [s, b0, x0]
                           exact hspan
                         have hw : w < count := by
                           simpa only [w, W, E] using hshort
                         have hcountE : E.records.length = count := by
                           dsimp only [E, I, s, hactive,
                             ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun]
                           exact ReferenceActivePhysicalHorizon.run_record_count I source.1.2
                             (ActualInitializationPhysicalStep.selectedRowIndex p source)
                             rewards s count hspan hactive
                         have hBbound : B.length ≤ count - w := by
                           have hfirstLen : ((E.records.drop w).take 1).length ≤ 1 := by
                             simp
                           have hsecondPrefix :
                               ((E.records.drop (w + 1)).takeWhile
                                 (fun record =>
                                   !ReferenceCollectionPhaseHistory.laterChosen record.input)).length ≤
                                 (E.records.drop (w + 1)).length :=
                             takeWhile_length_le _ _ _
                           have hsecondLen :
                               ((E.records.drop (w + 1)).takeWhile
                                 (fun record =>
                                   !ReferenceCollectionPhaseHistory.laterChosen record.input)).length ≤
                                 count - (w + 1) := by
                             calc
                               _ ≤ (E.records.drop (w + 1)).length := hsecondPrefix
                               _ = E.records.length - (w + 1) := by rw [List.length_drop]
                               _ = count - (w + 1) := by rw [hcountE]
                           dsimp only [B, ReferenceCollectionPhaseHistory.collectionWindow]
                           rw [List.length_append]
                           calc
                             ((E.records.drop w).take 1).length +
                                 ((E.records.drop (w + 1)).takeWhile
                                   (fun record =>
                                     !ReferenceCollectionPhaseHistory.laterChosen record.input)).length
                                 ≤ 1 + (count - (w + 1)) := Nat.add_le_add hfirstLen hsecondLen
                             _ ≤ count - w := by omega
                         have hbCount : b ≤ count := by
                           dsimp only [b, j, w]
                           omega
                         have hdropCount : (E.records.drop b).length = count - b := by
                           rw [List.length_drop, hcountE]
                         have hlateCount : Wlate.length ≤ count - b := by
                           calc
                             Wlate.length ≤ (E.records.drop b).length := htake
                             _ = count - b := hdropCount
                         have hindexCount : b + h ≤ count := by
                           have hbefore : h ≤ Wlate.length := hh
                           omega
                         have hphysicalSpan : s + (b + h) ≤ p.T := by
                           calc
                             s + (b + h) ≤ s + count := Nat.add_le_add_left hindexCount s
                             _ ≤ p.T := hstartSpan
                         exact hphysicalSpan) hactive
                   ∃ (hb : b ≤ count) (hbspan : s + b ≤ p.T),
                   (ReferenceActivePhysicalHorizon.run I source.1.2
                     (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s b
                     hbspan hactive).finalState.coordinator =
                       .collection P0 actualLedger actualSaved ∧
                   (ReferenceActivePhysicalHorizon.run I source.1.2
                     (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s b
                     hbspan hactive).finalState.followers i = .ordinary out memory ∧
                   Wlate = B.drop (k.val + 1) ∧
                   (∀ h (hh : h < Wlate.length),
                     E.records[b + h]? = some (Wlate[h]'hh) ∧
                       (Wlate[h]'hh).input.time.val = u + k.val + h) ∧
                   (∀ h (hh : h ≤ Wlate.length),
                     ((C h hh).finalState.coordinator = .dagger ∨
                       ∃ movingLedger movingSaved,
                         (C h hh).finalState.coordinator =
                           .collection P0 movingLedger movingSaved) ∧
                     ((C h hh).finalState.followers i = .dagger ∨
                       ∃ state memory,
                         (C h hh).finalState.followers i = .ordinary state memory ∧
                         state.status = .unoccupied ∧
                         ReferenceFollowerReplyChronology.reply state =
                           (some M, (V w).1, (V w).1 - (V (w - 1)).1, (V w).2))) ∧
                       (∀ h (hh : h < Wlate.length)
                       (hrecord : b + h < E.records.length),
                     ∀ start,
                       ¬ ReferenceFollowerReplyChronology.appliedDown
                             (E.records.get ⟨b + h, hrecord⟩) i start) ∧
                   (∀ h (hh : h ≤ Wlate.length)
                       (hrecord : b + h < E.records.length),
                     (h = Wlate.length →
                       ReferenceCollectionPhaseHistory.laterChosen
                         ((E.records.get ⟨b + h, hrecord⟩).input) = true) ∧
                     ((ReferenceFollowerFixedReply.actualChoice
                             (E.records.get ⟨b + h, hrecord⟩) i).configuration = .dagger ∨
                       ∃ state memory,
                         (ReferenceFollowerFixedReply.actualChoice
                             (E.records.get ⟨b + h, hrecord⟩) i).configuration =
                             .ordinary state memory ∧
                         state.status = .unoccupied ∧
                         ReferenceFollowerReplyChronology.reply state =
                           (some M, (V w).1, (V w).1 - (V (w - 1)).1, (V w).2))) ∧
                       (∀ h (hh : h < Wlate.length)
                       (hrecord : b + h < E.records.length),
                         let record := E.records.get ⟨b + h, hrecord⟩
                     let prepared := ReferenceFollowerFixedReply.actualChoice record i
                     (prepared.configuration = .dagger →
                       ReferenceUpReception.currentOfferWord rate record.input.row i
                         record.input.time prepared
                         (ReferenceFollowerFixedReply.actualChoice_alignment record i).1
                         (ReferenceFollowerFixedReply.actualChoice_alignment record i).2.1
                         (ReferenceFollowerFixedReply.actualChoice_alignment record i).2.2 = none) ∧
                     ∀ state memory,
                       prepared.configuration = .ordinary state memory →
                         ((∀ offered :
                         OrdinaryMessageCodec.UpRecord
                           (ReferencePrelaunchFollower.codecParams p rate.eta),
                         ActiveFollowerQueueOperation.checkedUpOffer rate.eta
                           prepared.follower prepared.row prepared.activation prepared.time state =
                             .offer offered →
                         offered.val.sigma = s + 1 ∧
                         offered.val.S = (V w).1 ∧
                         offered.val.delta = (V w).1 - (V (w - 1)).1 ∧
                         offered.val.q = (V w).2 ∧
                         ReferenceUpReception.currentOfferWord rate record.input.row i
                           record.input.time prepared
                           (ReferenceFollowerFixedReply.actualChoice_alignment record i).1
                           (ReferenceFollowerFixedReply.actualChoice_alignment record i).2.1
                           (ReferenceFollowerFixedReply.actualChoice_alignment record i).2.2 =
                             some ((OrdinaryMessageCodec.wordEquivFlat
                               (CoordinatorCollectionLedger.codecParams p rate.eta.val))
                               (OrdinaryMessageCodec.encodeUp
                                 (CoordinatorCollectionLedger.codecParams p rate.eta.val)
                                 offered))) ∧
                       ((ActiveFollowerQueueOperation.checkedUpOffer rate.eta
                          prepared.follower prepared.row prepared.activation prepared.time state =
                            .failure ∨
                        ActiveFollowerQueueOperation.checkedUpOffer rate.eta
                          prepared.follower prepared.row prepared.activation prepared.time state =
                            .noOffer) →
                         ReferenceUpReception.currentOfferWord rate record.input.row i
                           record.input.time prepared
                           (ReferenceFollowerFixedReply.actualChoice_alignment record i).1
                           (ReferenceFollowerFixedReply.actualChoice_alignment record i).2.1
                           (ReferenceFollowerFixedReply.actualChoice_alignment record i).2.2 =
                             none))) ∧
                   (∀ h₁ h₂ (hh₁ : h₁ < Wlate.length) (hh₂ : h₂ < Wlate.length)
                       (hrecord₁ : b + h₁ < E.records.length)
                       (hrecord₂ : b + h₂ < E.records.length),
                     let record₁ := E.records.get ⟨b + h₁, hrecord₁⟩
                     let record₂ := E.records.get ⟨b + h₂, hrecord₂⟩
                     ∀ state₁ memory₁ state₂ memory₂
                       (offered₁ offered₂ :
                         OrdinaryMessageCodec.UpRecord
                           (ReferencePrelaunchFollower.codecParams p rate.eta)),
                       (ReferenceFollowerFixedReply.actualChoice record₁ i).configuration =
                         .ordinary state₁ memory₁ →
                       (ReferenceFollowerFixedReply.actualChoice record₂ i).configuration =
                         .ordinary state₂ memory₂ →
                       ActiveFollowerQueueOperation.checkedUpOffer rate.eta
                         (ReferenceFollowerFixedReply.actualChoice record₁ i).follower
                         (ReferenceFollowerFixedReply.actualChoice record₁ i).row
                         (ReferenceFollowerFixedReply.actualChoice record₁ i).activation
                         (ReferenceFollowerFixedReply.actualChoice record₁ i).time state₁ =
                           .offer offered₁ →
                       ActiveFollowerQueueOperation.checkedUpOffer rate.eta
                         (ReferenceFollowerFixedReply.actualChoice record₂ i).follower
                         (ReferenceFollowerFixedReply.actualChoice record₂ i).row
                         (ReferenceFollowerFixedReply.actualChoice record₂ i).activation
                         (ReferenceFollowerFixedReply.actualChoice record₂ i).time state₂ =
                           .offer offered₂ →
                       (OrdinaryMessageCodec.wordEquivFlat
                         (CoordinatorCollectionLedger.codecParams p rate.eta.val))
                         (OrdinaryMessageCodec.encodeUp
                           (CoordinatorCollectionLedger.codecParams p rate.eta.val) offered₁) =
                       (OrdinaryMessageCodec.wordEquivFlat
                         (CoordinatorCollectionLedger.codecParams p rate.eta.val))
                         (OrdinaryMessageCodec.encodeUp
                           (CoordinatorCollectionLedger.codecParams p rate.eta.val) offered₂)))))) := by
  classical
  intro x0 b0 s I hactive E W w B u
  have hseed :=
    ReferenceFirstCollectionLateDownReplySeed.actual_first_collection_late_down_reply_seed
      rate source rewards C_star C_h count hcross hspan hshort
  obtain ⟨cutoffRecord, suffix, registers, owned, base, P0, birth,
      hsplit, hindex, htime, hstate, hcutoffChosen, hP0, hP0sigma,
      hP0queues, hfirstCutoff, hbirth, hbirthInstall, hbirthTime,
      hwindow, hqueries⟩ := hseed
  refine ⟨cutoffRecord, suffix, registers, owned, base, P0, birth,
    hsplit, hindex, htime, hstate, hcutoffChosen, hP0, hP0sigma,
    hP0queues, hfirstCutoff, hbirth, hbirthInstall, hbirthTime, hwindow, ?_⟩
  intro k i M j r hretained
  have hquery := hqueries k i M hretained
  rcases hquery with ⟨logged, cutD, after, raw, scan, replayedRegisters, lastService,
      hinput, hdown, haccepted, hM, hMsigma, hMq, hdownStart, hscan, hafterStatus,
      hafterLastDown, ⟨hjcount, n0, hn0, hn0eq, hchecked, _hprefix⟩,
      ⟨hregisters, hlastService, hafterS, hafterBacklog, hafterDelta⟩,
      hnextFollower, hnextCoordinator⟩
  let V := fun h => QueueReplay.replay (4 * rate.n) (0, 0)
    (ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords E.records i j M h)
  have hreplyAfter :
      ReferenceFollowerReplyChronology.reply after =
        (some M, (V w).1, (V w).1 - (V (w - 1)).1, (V w).2) := by
    change (after.lastDown, after.S, after.delta, after.backlog) = _
    rw [hafterLastDown, hafterS, hafterDelta, hafterBacklog]
  let tailWindow := suffix.takeWhile
    (fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input)
  have hBshape : B = cutoffRecord :: tailWindow := by
    dsimp only [B, ReferenceCollectionPhaseHistory.collectionWindow, tailWindow]
    rw [hsplit]
    rw [List.drop_append_length, List.drop_add_one_eq_tail_drop,
      List.drop_append_length]
    simp only [List.tail_cons, List.take_succ_cons, List.take_zero,
      List.singleton_append]
  have hBlen : B.length = tailWindow.length + 1 := by
    rw [hBshape]
    simp
  have hwindowK := hwindow k
  have hjlt : j < E.records.length := by
    have h := (List.getElem?_eq_some_iff.mp hwindowK.1).1
    simpa only [j] using h
  have hgetQuery : E.records[j]? = some r := by
    simpa only [j, r] using hwindowK.1
  have hRunEq :
      E = ReferenceActivePhysicalHorizon.run I source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source)
        rewards s count hspan hactive := by
    dsimp only [E, I, s, b0, x0, hactive,
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
        rewards s count hspan hactive).records[j]? = some r := by
    rw [← hRunEq]
    exact hgetQuery
  have hRunLt :
      j < (ReferenceActivePhysicalHorizon.run I source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source)
        rewards s count hspan hactive).records.length := by
    rw [← hRunEq]
    exact hjlt
  have hRunRecord :
      (ReferenceActivePhysicalHorizon.run I source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source)
        rewards s count hspan hactive).records[j]'hRunLt = r := by
    rw [List.getElem?_eq_getElem hRunLt] at hRunGet
    exact Option.some.inj hRunGet
  have hsuccessor := run_prefix_endpoints I source.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s count
    hstartSpan hactive j hjcount
  have hprefixOutput :
      (ReferenceActivePhysicalHorizon.run I source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source)
        rewards s (j + 1) hjSpan hactive).finalState = r.output.next := by
    calc
      (ReferenceActivePhysicalHorizon.run I source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source)
        rewards s (j + 1) hjSpan hactive).finalState =
          ((ReferenceActivePhysicalHorizon.run I source.1.2
            (ActualInitializationPhysicalStep.selectedRowIndex p source)
            rewards s count hspan hactive).records[j]'hRunLt).output.next :=
        hsuccessor.2
      _ = r.output.next := by rw [hRunRecord]
  rcases hnextFollower with hnextDagger | ⟨out, memory, hnextOrdinary,
      houtStatus, houtReply, houtS, houtBacklog, houtDelta, houtStart⟩
  · rcases hnextCoordinator with hcoordDagger | ⟨actualLedger, actualSaved, hcoordCollection⟩
    · refine ⟨logged, cutD, after, raw, scan, replayedRegisters, lastService,
        hinput, hdown, haccepted, hM, hMsigma, hMq, hdownStart, hscan,
        hafterStatus, hafterLastDown, ⟨hjcount, n0, hn0, hn0eq, hchecked⟩,
        ?_⟩
      exact ⟨hregisters, hlastService, hafterS, hafterDelta, hafterBacklog,
        hreplyAfter, Or.inl ⟨hnextDagger, Or.inl hcoordDagger⟩⟩
    · refine ⟨logged, cutD, after, raw, scan, replayedRegisters, lastService,
        hinput, hdown, haccepted, hM, hMsigma, hMq, hdownStart, hscan,
        hafterStatus, hafterLastDown, ⟨hjcount, n0, hn0, hn0eq, hchecked⟩,
        ?_⟩
      exact ⟨hregisters, hlastService, hafterS, hafterDelta, hafterBacklog,
        hreplyAfter,
        Or.inl ⟨hnextDagger, Or.inr ⟨actualLedger, actualSaved, hcoordCollection⟩⟩⟩
  · have hlastOut : out.lastDown = some M := by
      have h := congrArg Prod.fst houtReply
      simpa [ReferenceFollowerReplyChronology.reply, hafterLastDown] using h
    have hfixedOut :
        ReferenceFollowerReplyChronology.reply out =
          (some M, (V w).1, (V w).1 - (V (w - 1)).1, (V w).2) :=
      houtReply.trans hreplyAfter
    have hstartOut : ReferencePrelaunchFollower.acceptedStart out = s + 1 := by
      simpa only [hP0sigma] using houtStart
    rcases hnextCoordinator with hcoordDagger |
        ⟨actualLedger, actualSaved, hcoordCollection⟩
    · refine ⟨logged, cutD, after, raw, scan, replayedRegisters, lastService,
        hinput, hdown, haccepted, hM, hMsigma, hMq, hdownStart, hscan,
        hafterStatus, hafterLastDown, ⟨hjcount, n0, hn0, hn0eq, hchecked⟩,
        ?_⟩
      exact ⟨hregisters, hlastService, hafterS, hafterDelta, hafterBacklog,
        hreplyAfter,
        Or.inr ⟨out, memory, hnextOrdinary, houtStatus, hfixedOut, hlastOut,
          houtS, houtDelta, houtBacklog, hstartOut, Or.inl hcoordDagger⟩⟩
    · let b := j + 1
      let Wlate := (E.records.drop b).takeWhile
        (fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input)
      have hb : b ≤ count := by
        change j + 1 ≤ count
        exact Nat.succ_le_of_lt hjcount
      have hbspan : s + b ≤ p.T := by
        change s + (j + 1) ≤ p.T
        exact hjSpan
      have hseedPrefix :
          (ReferenceActivePhysicalHorizon.run I source.1.2
            (ActualInitializationPhysicalStep.selectedRowIndex p source)
            rewards s b hbspan hactive).finalState.followers i =
              .ordinary out memory := by
        change (ReferenceActivePhysicalHorizon.run I source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source)
          rewards s (j + 1) hjSpan hactive).finalState.followers i = _
        rw [hprefixOutput]
        exact hnextOrdinary
      have hcoordPrefix :
          (ReferenceActivePhysicalHorizon.run I source.1.2
            (ActualInitializationPhysicalStep.selectedRowIndex p source)
            rewards s b hbspan hactive).finalState.coordinator =
              .collection P0 actualLedger actualSaved := by
        change (ReferenceActivePhysicalHorizon.run I source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source)
          rewards s (j + 1) hjSpan hactive).finalState.coordinator = _
        rw [hprefixOutput]
        exact hcoordCollection
      have hstartOutP0 :
          ReferencePrelaunchFollower.acceptedStart out = P0.sigma.val + 1 := by
        simpa only [hP0sigma] using hstartOut
      have hprefix :=
        ReferenceCollectionUnoccupiedHistory.run_collection_unoccupied_prefix
          p rate I source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
          rewards s count hspan hactive b hb P0 actualLedger actualSaved hcoordPrefix
          i out memory hseedPrefix houtStatus hstartOutP0
      have hnoApplied :=
        ReferenceCollectionUnoccupiedHistory.run_collection_no_appliedDown
          p rate I source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
          rewards s count hspan hactive b hb P0 actualLedger actualSaved hcoordPrefix
          i out memory hseedPrefix houtStatus hstartOutP0
      have hboundary :=
        ReferenceCollectionUnoccupiedHistory.run_collection_boundary_choice_unoccupied
          p rate I source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
          rewards s count hspan hactive b hb P0 actualLedger actualSaved hcoordPrefix
          i out memory hseedPrefix houtStatus hstartOutP0
      have hRunCount :
          (ReferenceActivePhysicalHorizon.run I source.1.2
            (ActualInitializationPhysicalStep.selectedRowIndex p source)
            rewards s count hspan hactive).records.length = count :=
        ReferenceActivePhysicalHorizon.run_record_count I source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source)
          rewards s count hspan hactive
      have hcountE : E.records.length = count := by
        rw [hRunEq]
        exact hRunCount
      let full := ReferenceActivePhysicalHorizon.run I source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source)
        rewards s count hspan hactive
      have hRecordsEq : full.records = E.records := by
        change (ReferenceActivePhysicalHorizon.run I source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source)
          rewards s count hspan hactive).records = E.records
        rw [← hRunEq]
      have htakeLength : Wlate.length ≤ (E.records.drop b).length := by
        exact takeWhile_length_le _ _ _
      have hlateLength : Wlate.length ≤ count - b := by
        calc
          Wlate.length ≤ (E.records.drop b).length := htakeLength
          _ = count - b := by rw [List.length_drop, hcountE]
      have hprefixSpan : ∀ h, h ≤ Wlate.length → s + (b + h) ≤ p.T := by
        intro h hh
        have hleSub : h ≤ count - b := le_trans hh hlateLength
        have hcountPrefix : b + h ≤ count := by
          have hcountPrefix' : h + b ≤ count := (Nat.le_sub_iff_add_le hb).mp hleSub
          omega
        calc
          s + (b + h) ≤ s + count := Nat.add_le_add_left hcountPrefix s
          _ ≤ p.T := hstartSpan
      have hbIndex : b = W.length + (k.val + 1) := by
        dsimp [b, j, w]
        omega
      have hWlate : Wlate = B.drop (k.val + 1) := by
        have hkTail : k.val ≤ tailWindow.length := by
          have hk := k.isLt
          have hkLength : k.val < tailWindow.length + 1 := by
            calc
              k.val < B.length := hk
              _ = tailWindow.length + 1 := hBlen
          omega
        calc
          Wlate = (suffix.drop k.val).takeWhile
              (fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input) := by
            dsimp only [Wlate]
            rw [hsplit, hbIndex, ← List.drop_drop, List.drop_append_length,
              List.drop_add_one_eq_tail_drop]
            have htail :
                (List.drop k.val (cutoffRecord :: suffix)).tail = suffix.drop k.val := by
              cases k.val with
              | zero => rfl
              | succ n =>
                  change (suffix.drop n).tail = suffix.drop (n + 1)
                  exact tail_drop _ _ _
            rw [htail]
          _ = tailWindow.drop k.val := by
            exact takeWhile_drop _ _ _ k.val hkTail
          _ = B.drop (k.val + 1) := by
            have hdrop :
                B.drop (k.val + 1) = (cutoffRecord :: tailWindow).drop (k.val + 1) :=
              congrArg (fun records : List _ => records.drop (k.val + 1)) hBshape
            rw [hdrop]
            cases k.val with
            | zero => rfl
            | succ n => simp [List.drop]
      have htimeLookup :
          ∀ h (hh : h < Wlate.length),
            E.records[b + h]? = some (Wlate[h]'hh) ∧
              (Wlate[h]'hh).input.time.val = u + k.val + h := by
        intro h hh
        have hrem : h < (B.drop (k.val + 1)).length := by
          simpa only [hWlate] using hh
        have hq : k.val + 1 + h < B.length := by
          rw [List.length_drop] at hrem
          omega
        let q : Fin B.length := ⟨k.val + 1 + h, hq⟩
        have hgetDrop : (B.drop (k.val + 1))[h] = B[q.val] := by
          simp [q, List.getElem_drop]
        have hgetOption : Wlate[h]? = some B[q.val] := by
          rw [hWlate, List.getElem?_eq_getElem hrem, hgetDrop]
        have hget : Wlate[h]'hh = B[q.val] := by
          have hsome : some (Wlate[h]'hh) = some B[q.val] := by
            rw [← List.getElem?_eq_getElem hh]
            exact hgetOption
          exact Option.some.inj hsome
        have hbq : b + h = w + q.val := by
          dsimp [b, j, q, w]
          omega
        constructor
        · rw [hbq, hget]
          exact (hwindow q).1
        · rw [hget]
          have hqval : q.val = k.val + 1 + h := rfl
          have htime : B[q.val].input.time.val + 1 = u + (k.val + 1 + h) := by
            simpa [q] using (hwindow q).2
          change B[q.val].input.time.val = u + k.val + h
          omega
      have hprefixFacts :
          ∀ h (hh : h ≤ Wlate.length),
            ((ReferenceActivePhysicalHorizon.run I source.1.2
              (ActualInitializationPhysicalStep.selectedRowIndex p source)
              rewards s (b + h) (hprefixSpan h hh) hactive).finalState.coordinator = .dagger ∨
              ∃ movingLedger movingSaved,
                (ReferenceActivePhysicalHorizon.run I source.1.2
                  (ActualInitializationPhysicalStep.selectedRowIndex p source)
                  rewards s (b + h) (hprefixSpan h hh) hactive).finalState.coordinator =
                    .collection P0 movingLedger movingSaved) ∧
            ((ReferenceActivePhysicalHorizon.run I source.1.2
              (ActualInitializationPhysicalStep.selectedRowIndex p source)
              rewards s (b + h) (hprefixSpan h hh) hactive).finalState.followers i = .dagger ∨
              ∃ state memory,
                (ReferenceActivePhysicalHorizon.run I source.1.2
                  (ActualInitializationPhysicalStep.selectedRowIndex p source)
                  rewards s (b + h) (hprefixSpan h hh) hactive).finalState.followers i =
                    .ordinary state memory ∧
                state.status = .unoccupied ∧
                ReferenceFollowerReplyChronology.reply state =
                  (some M, (V w).1, (V w).1 - (V (w - 1)).1, (V w).2)) := by
        intro h hh
        have hstate := hprefix h hh
        rcases hstate with ⟨hcoord, hfollow⟩
        rcases hfollow with hdagger | ⟨state, memory, hconfiguration, hstatus, hreply⟩
        · exact And.intro hcoord (Or.inl hdagger)
        · exact And.intro hcoord (Or.inr ⟨state, memory, hconfiguration, hstatus,
            hreply.trans hfixedOut⟩)
      have hnoAppliedFacts :
          ∀ h (hh : h < Wlate.length)
            (hrecord : b + h < E.records.length),
            ∀ start,
              ¬ ReferenceFollowerReplyChronology.appliedDown
                (E.records.get ⟨b + h, hrecord⟩) i start := by
        intro h hh hrecord start
        have hfullRecord : b + h < full.records.length := by
          rw [hRecordsEq]
          exact hrecord
        have hrecordOption : full.records[b + h]? = E.records[b + h]? :=
          congrArg (fun records : List _ => records[b + h]?) hRecordsEq
        have hfullGet := List.getElem?_eq_getElem hfullRecord
        have hsourceGet := List.getElem?_eq_getElem hrecord
        rw [hfullGet, hsourceGet] at hrecordOption
        have hrecordEq :
            full.records.get ⟨b + h, hfullRecord⟩ = E.records.get ⟨b + h, hrecord⟩ := by
          change full.records[b + h]'hfullRecord = E.records[b + h]'hrecord
          exact Option.some.inj hrecordOption
        have h := hnoApplied h hh hfullRecord start
        rw [hrecordEq] at h
        exact h
      have hboundaryFacts :
          ∀ h (hh : h ≤ Wlate.length)
            (hrecord : b + h < E.records.length),
            (h = Wlate.length →
              ReferenceCollectionPhaseHistory.laterChosen
                ((E.records.get ⟨b + h, hrecord⟩).input) = true) ∧
            ((ReferenceFollowerFixedReply.actualChoice
              (E.records.get ⟨b + h, hrecord⟩) i).configuration = .dagger ∨
              ∃ state memory,
                (ReferenceFollowerFixedReply.actualChoice
                  (E.records.get ⟨b + h, hrecord⟩) i).configuration =
                    .ordinary state memory ∧
                state.status = .unoccupied ∧
                ReferenceFollowerReplyChronology.reply state =
                  (some M, (V w).1, (V w).1 - (V (w - 1)).1, (V w).2)) := by
        intro h hh hrecord
        have hfullRecord : b + h < full.records.length := by
          rw [hRecordsEq]
          exact hrecord
        have hrecordOption : full.records[b + h]? = E.records[b + h]? :=
          congrArg (fun records : List _ => records[b + h]?) hRecordsEq
        have hfullGet := List.getElem?_eq_getElem hfullRecord
        have hsourceGet := List.getElem?_eq_getElem hrecord
        rw [hfullGet, hsourceGet] at hrecordOption
        have hrecordEq :
            full.records.get ⟨b + h, hfullRecord⟩ = E.records.get ⟨b + h, hrecord⟩ := by
          change full.records[b + h]'hfullRecord = E.records[b + h]'hrecord
          exact Option.some.inj hrecordOption
        have hFullWlate :
            (full.records.drop b).takeWhile
                (fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input) =
              Wlate := by
          change (full.records.drop b).takeWhile
              (fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input) =
            (E.records.drop b).takeWhile
              (fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input)
          rw [hRecordsEq]
        have h := hboundary h hh hfullRecord
        rcases h with ⟨hend, hchoice⟩
        rw [hFullWlate] at hend
        rw [hrecordEq] at hchoice
        rcases hchoice with hdagger | ⟨state, memory, hconfiguration, hstatus, hreply⟩
        · exact And.intro hend (Or.inl hdagger)
        · exact And.intro hend
            (Or.inr ⟨state, memory, hconfiguration, hstatus, hreply.trans hfixedOut⟩)
      have hofferFacts :
          ∀ h (hh : h < Wlate.length)
            (hrecord : b + h < E.records.length),
            let record := E.records.get ⟨b + h, hrecord⟩
            let prepared := ReferenceFollowerFixedReply.actualChoice record i
            (prepared.configuration = .dagger →
              ReferenceUpReception.currentOfferWord rate record.input.row i record.input.time
                prepared
                (ReferenceFollowerFixedReply.actualChoice_alignment record i).1
                (ReferenceFollowerFixedReply.actualChoice_alignment record i).2.1
                (ReferenceFollowerFixedReply.actualChoice_alignment record i).2.2 = none) ∧
            ∀ state memory,
              prepared.configuration = .ordinary state memory →
              ((∀ offered :
                OrdinaryMessageCodec.UpRecord
                  (ReferencePrelaunchFollower.codecParams p rate.eta),
                ActiveFollowerQueueOperation.checkedUpOffer rate.eta
                  prepared.follower prepared.row prepared.activation prepared.time state =
                    .offer offered →
                offered.val.sigma = s + 1 ∧
                offered.val.S = (V w).1 ∧
                offered.val.delta = (V w).1 - (V (w - 1)).1 ∧
                offered.val.q = (V w).2 ∧
                ReferenceUpReception.currentOfferWord rate record.input.row i record.input.time
                  prepared
                  (ReferenceFollowerFixedReply.actualChoice_alignment record i).1
                  (ReferenceFollowerFixedReply.actualChoice_alignment record i).2.1
                  (ReferenceFollowerFixedReply.actualChoice_alignment record i).2.2 =
                    some ((OrdinaryMessageCodec.wordEquivFlat
                      (CoordinatorCollectionLedger.codecParams p rate.eta.val))
                      (OrdinaryMessageCodec.encodeUp
                        (CoordinatorCollectionLedger.codecParams p rate.eta.val) offered))) ∧
              ((ActiveFollowerQueueOperation.checkedUpOffer rate.eta
                prepared.follower prepared.row prepared.activation prepared.time state =
                  .failure ∨
               ActiveFollowerQueueOperation.checkedUpOffer rate.eta
                prepared.follower prepared.row prepared.activation prepared.time state =
                  .noOffer) →
                ReferenceUpReception.currentOfferWord rate record.input.row i record.input.time
                  prepared
                  (ReferenceFollowerFixedReply.actualChoice_alignment record i).1
                  (ReferenceFollowerFixedReply.actualChoice_alignment record i).2.1
                  (ReferenceFollowerFixedReply.actualChoice_alignment record i).2.2 =
                    none)) := by
        intro h hh hrecord
        let record := E.records.get ⟨b + h, hrecord⟩
        let prepared := ReferenceFollowerFixedReply.actualChoice record i
        have hchoice := (hboundaryFacts h (Nat.le_of_lt hh) hrecord).2
        constructor
        · intro hdagger
          exact ReferenceUpReception.currentOfferWord_eq_none_of_dagger
            rate record.input.row i record.input.time prepared
            (ReferenceFollowerFixedReply.actualChoice_alignment record i).1
            (ReferenceFollowerFixedReply.actualChoice_alignment record i).2.1
            (ReferenceFollowerFixedReply.actualChoice_alignment record i).2.2 hdagger
        · intro state memory hconfiguration
          have hreplyChoice :
              ReferenceFollowerReplyChronology.reply state =
                (some M, (V w).1, (V w).1 - (V (w - 1)).1, (V w).2) := by
            rcases hchoice with hdagger | ⟨choice, choiceMemory, hchoice, _, hreply⟩
            · rw [hconfiguration] at hdagger
              cases hdagger
            · have heq := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
                (hconfiguration.symm.trans hchoice)
              simpa only [ReferenceFollowerReplyChronology.reply, heq.1] using hreply
          constructor
          · intro offered hoff
            have hfields :=
              ReferenceUpReception.checkedPreparedOffer_field_equations
                rate record.input.row i record.input.time prepared
                (ReferenceFollowerFixedReply.actualChoice_alignment record i).1
                (ReferenceFollowerFixedReply.actualChoice_alignment record i).2.1
                (ReferenceFollowerFixedReply.actualChoice_alignment record i).2.2
                state memory hconfiguration offered hoff
            have hstart : ReferencePrelaunchFollower.acceptedStart state = s + 1 := by
              have hsameReply :
                  ReferenceFollowerReplyChronology.reply state =
                    ReferenceFollowerReplyChronology.reply out :=
                hreplyChoice.trans hfixedOut.symm
              have heq := ReferenceFollowerReplyChronology.acceptedStart_eq_of_reply_eq
                hsameReply
              simpa only [hstartOut] using heq
            have hS : state.S = (V w).1 :=
              congrArg (fun reply => reply.2.1) hreplyChoice
            have hdelta : state.delta = (V w).1 - (V (w - 1)).1 :=
              congrArg (fun reply => reply.2.2.1) hreplyChoice
            have hbacklog : state.backlog = (V w).2 :=
              congrArg (fun reply => reply.2.2.2) hreplyChoice
            have hword :=
              ReferenceUpReception.currentOfferWord_eq_encoded_offer
                rate record.input.row i record.input.time prepared
                (ReferenceFollowerFixedReply.actualChoice_alignment record i).1
                (ReferenceFollowerFixedReply.actualChoice_alignment record i).2.1
                (ReferenceFollowerFixedReply.actualChoice_alignment record i).2.2
                state memory hconfiguration offered hoff
            exact ⟨hfields.1.trans hstart, hfields.2.1.trans hS,
              hfields.2.2.1.trans hdelta, hfields.2.2.2.trans hbacklog, hword⟩
          · intro hnonoffer
            exact ReferenceUpReception.currentOfferWord_eq_none_of_checked_nonoffer
              rate record.input.row i record.input.time prepared
              (ReferenceFollowerFixedReply.actualChoice_alignment record i).1
              (ReferenceFollowerFixedReply.actualChoice_alignment record i).2.1
              (ReferenceFollowerFixedReply.actualChoice_alignment record i).2.2
              state memory hconfiguration hnonoffer
      have hpairOffers :
          ∀ h₁ h₂ (hh₁ : h₁ < Wlate.length) (hh₂ : h₂ < Wlate.length)
            (hrecord₁ : b + h₁ < E.records.length)
            (hrecord₂ : b + h₂ < E.records.length),
            let record₁ := E.records.get ⟨b + h₁, hrecord₁⟩
            let record₂ := E.records.get ⟨b + h₂, hrecord₂⟩
            ∀ state₁ memory₁ state₂ memory₂
              (offered₁ offered₂ :
                OrdinaryMessageCodec.UpRecord
                  (ReferencePrelaunchFollower.codecParams p rate.eta)),
              (ReferenceFollowerFixedReply.actualChoice record₁ i).configuration =
                .ordinary state₁ memory₁ →
              (ReferenceFollowerFixedReply.actualChoice record₂ i).configuration =
                .ordinary state₂ memory₂ →
              ActiveFollowerQueueOperation.checkedUpOffer rate.eta
                (ReferenceFollowerFixedReply.actualChoice record₁ i).follower
                (ReferenceFollowerFixedReply.actualChoice record₁ i).row
                (ReferenceFollowerFixedReply.actualChoice record₁ i).activation
                (ReferenceFollowerFixedReply.actualChoice record₁ i).time state₁ =
                  .offer offered₁ →
              ActiveFollowerQueueOperation.checkedUpOffer rate.eta
                (ReferenceFollowerFixedReply.actualChoice record₂ i).follower
                (ReferenceFollowerFixedReply.actualChoice record₂ i).row
                (ReferenceFollowerFixedReply.actualChoice record₂ i).activation
                (ReferenceFollowerFixedReply.actualChoice record₂ i).time state₂ =
                  .offer offered₂ →
              (OrdinaryMessageCodec.wordEquivFlat
                (CoordinatorCollectionLedger.codecParams p rate.eta.val))
                (OrdinaryMessageCodec.encodeUp
                  (CoordinatorCollectionLedger.codecParams p rate.eta.val) offered₁) =
              (OrdinaryMessageCodec.wordEquivFlat
                (CoordinatorCollectionLedger.codecParams p rate.eta.val))
                (OrdinaryMessageCodec.encodeUp
                  (CoordinatorCollectionLedger.codecParams p rate.eta.val) offered₂) := by
        intro h₁ h₂ hh₁ hh₂ hrecord₁ hrecord₂ record₁ record₂
        intro state₁ memory₁ state₂ memory₂ offered₁ offered₂ hconfiguration₁
          hconfiguration₂ hoff₁ hoff₂
        have hfixed₁ := (hofferFacts h₁ hh₁ hrecord₁).2 state₁ memory₁
          hconfiguration₁ |>.1 offered₁ hoff₁
        have hfixed₂ := (hofferFacts h₂ hh₂ hrecord₂).2 state₂ memory₂
          hconfiguration₂ |>.1 offered₂ hoff₂
        have hactual₁ :=
          ReferenceUpReception.checkedPreparedOffer_field_equations
            rate record₁.input.row i record₁.input.time
            (ReferenceFollowerFixedReply.actualChoice record₁ i)
            (ReferenceFollowerFixedReply.actualChoice_alignment record₁ i).1
            (ReferenceFollowerFixedReply.actualChoice_alignment record₁ i).2.1
            (ReferenceFollowerFixedReply.actualChoice_alignment record₁ i).2.2
            state₁ memory₁ hconfiguration₁ offered₁ hoff₁
        have hactual₂ :=
          ReferenceUpReception.checkedPreparedOffer_field_equations
            rate record₂.input.row i record₂.input.time
            (ReferenceFollowerFixedReply.actualChoice record₂ i)
            (ReferenceFollowerFixedReply.actualChoice_alignment record₂ i).1
            (ReferenceFollowerFixedReply.actualChoice_alignment record₂ i).2.1
            (ReferenceFollowerFixedReply.actualChoice_alignment record₂ i).2.2
            state₂ memory₂ hconfiguration₂ offered₂ hoff₂
        have hstart₁ : ReferencePrelaunchFollower.acceptedStart state₁ = s + 1 :=
          hactual₁.1.symm.trans hfixed₁.1
        have hstart₂ : ReferencePrelaunchFollower.acceptedStart state₂ = s + 1 :=
          hactual₂.1.symm.trans hfixed₂.1
        have hS₁ : state₁.S = (V w).1 := hactual₁.2.1.symm.trans hfixed₁.2.1
        have hS₂ : state₂.S = (V w).1 := hactual₂.2.1.symm.trans hfixed₂.2.1
        have hdelta₁ : state₁.delta = (V w).1 - (V (w - 1)).1 :=
          hactual₁.2.2.1.symm.trans hfixed₁.2.2.1
        have hdelta₂ : state₂.delta = (V w).1 - (V (w - 1)).1 :=
          hactual₂.2.2.1.symm.trans hfixed₂.2.2.1
        have hbacklog₁ : state₁.backlog = (V w).2 :=
          hactual₁.2.2.2.symm.trans hfixed₁.2.2.2.1
        have hbacklog₂ : state₂.backlog = (V w).2 :=
          hactual₂.2.2.2.symm.trans hfixed₂.2.2.2.1
        have hregisters :
            ReferencePrelaunchFollower.acceptedStart state₁ =
                ReferencePrelaunchFollower.acceptedStart state₂ ∧
              state₁.S = state₂.S ∧ state₁.delta = state₂.delta ∧
                state₁.backlog = state₂.backlog := by
          exact ⟨hstart₁.trans hstart₂.symm, hS₁.trans hS₂.symm,
            hdelta₁.trans hdelta₂.symm, hbacklog₁.trans hbacklog₂.symm⟩
        have hword := ReferenceFollowerFixedReply.currentOfferWord_eq_of_same_reply_registers
          record₁ record₂ i state₁ state₂ memory₁ memory₂
          hconfiguration₁ hconfiguration₂ hregisters offered₁ offered₂ hoff₁ hoff₂
        have hword₁ := hfixed₁.2.2.2.2
        have hword₂ := hfixed₂.2.2.2.2
        rw [hword₁, hword₂] at hword
        exact Option.some.inj hword
      refine ⟨logged, cutD, after, raw, scan, replayedRegisters, lastService,
        hinput, hdown, haccepted, hM, hMsigma, hMq, hdownStart, hscan,
        hafterStatus, hafterLastDown, ⟨hjcount, n0, hn0, hn0eq, hchecked⟩,
        ?_⟩
      refine ⟨hregisters, hlastService, hafterS, hafterDelta, hafterBacklog,
        hreplyAfter,
        Or.inr ⟨out, memory, hnextOrdinary, houtStatus, hfixedOut, hlastOut,
          houtS, houtDelta, houtBacklog, hstartOut,
          Or.inr ⟨actualLedger, actualSaved, hcoordCollection, ?_⟩⟩⟩
      exact ⟨hb, hbspan, hcoordPrefix, hseedPrefix, hWlate, htimeLookup,
        hprefixFacts, hnoAppliedFacts, hboundaryFacts,
        (by simpa only [b, Wlate] using hofferFacts),
        (by simpa only [b, Wlate] using hpairOffers)⟩

end Bandits.Support.ReferenceFirstCollectionLateDownReplyHistory

end
