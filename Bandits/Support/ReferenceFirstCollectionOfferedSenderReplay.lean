/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionDownPayloadOrigin
public import Bandits.Support.ReferenceFirstOfferedUpNumericalReplay

/-!
# First-collection offered UP sender replay

Sources: sources/zip4/manuscript/06_interruptions.tex:9-100,192-233,246-297,301-344,
sources/zip4/manuscript/appendix_a_local_protocol.tex:28-64, and
sources/zip4/manuscript/04_slow_fast_learner.tex:157-174.

For an actual choice-time UP offer in the raw first-collection window, this
producer joins the actual first-cutoff payload and birth to the literal sender
replay. A retained DOWN may be accepted before or after the cutoff. The
conclusion remains conditional on the actual ordinary choice and checked
offer; receiver acceptance, finish success, and manuscript queue identities
are not asserted.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferencePrelaunchFollower
open Bandits.Support.ReferenceFollowerFixedReply

namespace Bandits.Support.ReferenceFirstCollectionOfferedSenderReplay

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

private theorem run_record_time_of_lookup
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (span : start + count ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (n : ℕ)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hget : (ReferenceActivePhysicalHorizon.run initial rows J rewards start count
      span active).records[n]? = some record) :
    record.input.time.val = start + n := by
  have hmap :
      ((ReferenceActivePhysicalHorizon.run initial rows J rewards start count
        span active).records.map fun r => r.input.time.val)[n]? =
        some record.input.time.val := by
    simp only [List.getElem?_map, hget, Option.map_some]
  rw [ReferenceActivePhysicalHorizon.run_time_values] at hmap
  have hn : n < count := by
    have hlen := (List.getElem?_eq_some_iff.mp hget).1
    rw [ReferenceActivePhysicalHorizon.run_record_count initial rows J rewards
      start count span active] at hlen
    exact hlen
  have hcalendar :
      (ReferenceActivePhysicalHorizon.calendar start count)[n]? =
        some (start + n) := by
    have hbound : n < (ReferenceActivePhysicalHorizon.calendar start count).length := by
      simpa [ReferenceActivePhysicalHorizon.calendar] using hn
    rw [List.getElem?_eq_getElem hbound]
    simp [ReferenceActivePhysicalHorizon.calendar]
  rw [hcalendar] at hmap
  exact (Option.some.inj hmap).symm

/-- The actual pre-receiver UP offer in the first collection window has the
same cutoff payload and initial birth as the first interruption. Its returned
UP fields follow the literal reply projection through the cutoff, including
the final service at u - 1. The conclusion makes no claim about current
receiver acceptance or source Delta/Gamma truth. -/
theorem run_first_collection_offered_sender_replay
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (count : ℕ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true)
    (hspan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed + count ≤ p.T)
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
        rate z rewards C_star C_h hcross count hspan).records).length < count) :
    let x0 := ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate
    let b0 := ReferenceInitializationRun.output x0
    let s := ReferenceInitializationRun.elapsed p b0.completed
    let I := ReferenceFirstCollectionEpochAlignment.actualLaunchState
      rate z rewards C_star C_h hcross
    let Erun := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
      rate z rewards C_star C_h hcross count hspan
    let W := ReferenceFirstLiveConfirmationHistory.firstLiveWindow Erun.records
    let w := W.length
    let B := ReferenceCollectionPhaseHistory.collectionWindow Erun.records w
    let u := s + w + 1
    ∃ (cutoffRecord : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
      (suffix : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
      (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
      (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
      (base : Fin (p.m - 1) → ℕ)
      (P0 : ReferenceActivePhysicalStep.Payload rate)
      (birth : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)),
      Erun.records = W ++ cutoffRecord :: suffix ∧
      (∃ hindex : w < Erun.records.length,
        cutoffRecord = Erun.records[w]'hindex) ∧
      cutoffRecord.input.time.val = s + w ∧
      cutoffRecord.input.state.coordinator = .live registers owned base ∧
      ReferenceCollectionPhaseHistory.cutoffChosen cutoffRecord.input = true ∧
      P0 = registers.payload ∧
      P0.sigma.val = s ∧
      (∀ arm, P0.queues arm = 0) ∧
      FollowerCutoffScan.firstCutoff p rate.eta.val P0.sigma
        (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
          (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z))) = u ∧
      birth ∈ Erun.records ∧
      ReferenceAssignmentPayloadPersistence.InstallationBirth birth P0 ∧
      birth.input.time.val = s ∧
      (∃ installed birthSelection,
        birth.output.preparation.coordinator = .first (.chosen installed birthSelection) ∧
          installed.registers.payload = P0) ∧
      (∀ k : Fin B.length,
        Erun.records[w + k.val]? = some B[k.val] ∧
          B[k.val].input.time.val + 1 = u + k.val) ∧
      ∀ (k : Fin B.length) (i : Fin (p.m - 1))
        (choice : ReferencePrelaunchFollower.State p rate.eta)
        (mu : ActiveFollowerLifecycle.LocalMemory p)
        (M : OrdinaryMessageCodec.UpRecord (ReferencePrelaunchFollower.codecParams p rate.eta)),
        let prepared := actualChoice B[k.val] i
        prepared.configuration = .ordinary choice mu →
        ActiveFollowerQueueOperation.checkedUpOffer rate.eta prepared.follower prepared.row
          prepared.activation prepared.time choice = .offer M →
        ReferenceUpReception.currentOfferWord rate B[k.val].input.row i B[k.val].input.time prepared
          (actualChoice_alignment B[k.val] i).1 (actualChoice_alignment B[k.val] i).2.1
          (actualChoice_alignment B[k.val] i).2.2 =
          some ((OrdinaryMessageCodec.wordEquivFlat
            (CoordinatorCollectionLedger.codecParams p rate.eta.val))
            (OrdinaryMessageCodec.encodeUp
              (CoordinatorCollectionLedger.codecParams p rate.eta.val) M)) ∧
        M.val = ActiveFollowerQueueOperation.upOfferFields choice ∧
        choice.status = .unoccupied ∧
        ((choice.lastDown = none ∧ M.val = OrdinaryMessageCodec.upPlaceholder) ∨
          ∃ (j : Fin Erun.records.length)
            (message : ReferenceFirstAcceptedUpNumericSnapshot.DownRecord
              (p := p) (rate := rate)),
            j.val < w + k.val ∧
            ReferenceAcceptedUpFollowerHistory.RetainedDown Erun.records[j.val] i message ∧
            message = P0.downRecord i ∧
            choice.lastDown = some message ∧
            message.val.sigma = s + 1 ∧
            message.val.q = 0 ∧
            (let Frec :=
              ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords
                Erun.records i j.val message w
             let V := fun h => QueueReplay.replay (4 * rate.n) (0, 0)
               (ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords
                 Erun.records i j.val message h)
             M.val.sigma = s + 1 ∧
             M.val.S = (V w).1 ∧
             M.val.q = (V w).2 ∧
             M.val.delta = (V w).1 - (V (w - 1)).1 ∧
             Frec.length = w ∧
             (∀ r ∈ Frec, r.2 ≤ D p) ∧
             (∀ h ≤ w, (V h).1 + (V h).2 ≤ h * D p) ∧
             (V w).1 - (V (w - 1)).1 ≤ 4 * rate.n ∧
             4 * rate.n ≤ D p)) := by
  classical
  intro x0 b0 s I Erun W w B u
  let initial := ReferenceFirstLaunchNumericalCell.launchState
    rate z rewards C_star C_h hcross
  let rows := z.1.2
  let J := ActualInitializationPhysicalStep.selectedRowIndex p z
  let active := ReferenceFirstLaunchNumericalCell.launchState_allActiveAtStart
    rate z rewards C_star C_h hcross
  let E0 := ReferenceActivePhysicalHorizon.run initial rows J rewards s count hspan active
  have hI : I = initial := by
    dsimp only [I, initial, ReferenceFirstCollectionEpochAlignment.actualLaunchState,
      ReferenceFirstLaunchNumericalCell.launchState]
  have hE : Erun = E0 := by
    change ReferenceActivePhysicalHorizon.run I rows J rewards s count hspan
        (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
          rate z rewards C_star C_h hcross).1 = E0
    cases hI
    rfl
  have hshort0 : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow E0.records).length < count := by
    change (ReferenceFirstLiveConfirmationHistory.firstLiveWindow Erun.records).length < count at hshort
    simpa only [hE] using hshort
  have hseedSource := ReferenceFirstLaunchNumericalCell.actual_launch_seed
    rate z rewards C_star C_h hcross
  obtain ⟨_, _, _, hfirst, _, _, _, hseeds⟩ := hseedSource
  have hdiag := ReferenceFirstOfferedUpNumericalReplay.run_first_collection_offered_sender_diagnostics
    rate z rewards C_star C_h hcross count hspan hshort0
  obtain ⟨diagCut, diagSuffix, _diagRegisters, _diagOwned, _diagBase,
      hdiagSplit, hdiagTime, _hdiagState, _hdiagSigma, _hdiagBase,
      _hdiagBirth, _hdiagCutoff, hqueries⟩ := hdiag
  have hdiagSplitE : Erun.records = W ++ diagCut :: diagSuffix :=
    hE.symm ▸ hdiagSplit
  have horigin := ReferenceFirstCollectionDownPayloadOrigin.actual_first_collection_down_payload_origin
    rate z rewards C_star C_h count hcross hspan hshort
  rcases horigin.origin with
    ⟨cutoffRecord, P0, birth, registers, owned, base,
      hcutIndex, hcutUnique, hcutState, hcutoffTag, hP0, hP0sigma,
      hP0queues, hfirstCutoff, hbirthMember, hbirthInstall, hbirthTime,
      hbirthFirst, hwindowLookup, _hselectedPayload, _hretainedWindow, hprior⟩
  have hsameCut : diagCut = cutoffRecord :=
    hcutUnique diagCut diagSuffix hdiagSplitE
  have hsplit : Erun.records = W ++ cutoffRecord :: diagSuffix := by
    rw [hsameCut] at hdiagSplitE
    exact hdiagSplitE
  have hcutTime : cutoffRecord.input.time.val = s + w := by
    rw [← hsameCut]
    exact hdiagTime
  have hwindowLookup0 :
      ∀ k : Fin B.length,
        E0.records[w + k.val]? = some B[k.val] ∧
          B[k.val].input.time.val + 1 = u + k.val := by
    intro k
    exact hE ▸ hwindowLookup k
  have hprior0 :
      ∀ (k : Fin B.length) (j : ℕ), j < w + k.val →
        ∀ (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)),
          E0.records[j]? = some record →
            ∀ (i : Fin (p.m - 1))
              (message : ReferenceAcceptedUpFollowerHistory.DownRecord
                (p := p) (rate := rate)),
              ReferenceAcceptedUpFollowerHistory.RetainedDown record i message →
                message = P0.downRecord i ∧
                  message.val.sigma = s + 1 ∧ message.val.q = 0 := by
    intro k j hj record hget i message hretained
    have hgetE : Erun.records[j]? = some record := hE.symm ▸ hget
    exact hprior k j hj record hgetE i message hretained
  refine ⟨cutoffRecord, diagSuffix, registers, owned, base, P0, birth, ?_⟩
  constructor
  · exact hsplit
  constructor
  · exact hcutIndex
  constructor
  · exact hcutTime
  constructor
  · exact hcutState
  constructor
  · exact hcutoffTag
  constructor
  · exact hP0
  constructor
  · exact hP0sigma
  constructor
  · exact hP0queues
  constructor
  · exact hfirstCutoff
  constructor
  · exact hbirthMember
  constructor
  · exact hbirthInstall
  constructor
  · exact hbirthTime
  constructor
  · exact hbirthFirst
  constructor
  · exact hwindowLookup
  intro k i choice mu M prepared hchoice hoff
  have hquery := hqueries k i choice mu M hchoice hoff
  rcases hquery with ⟨hword, hfields, hstatus, hbranch⟩
  have hwindow := hwindowLookup0 k
  have hindex : w + k.val < E0.records.length :=
    (List.getElem?_eq_some_iff.mp hwindow.1).1
  have hcurrent : B[k.val] = E0.records[w + k.val]'hindex := by
    have hlook := hwindow.1
    rw [List.getElem?_eq_getElem hindex] at hlook
    exact (Option.some.inj hlook).symm
  refine ⟨hword, hfields, hstatus, ?_⟩
  rcases hbranch with ⟨hnone, hplaceholder⟩ |
    ⟨a, j, message, hBa, hja, hretained, hlastDown⟩
  · exact Or.inl ⟨hnone, hplaceholder⟩
  · have htimeA := run_record_time_of_lookup initial rows J rewards s count hspan active
      a.val E0.records[a.val] (List.getElem?_eq_getElem a.isLt)
    have htimeEq :
        E0.records[a.val].input.time.val = B[k.val].input.time.val :=
      (congrArg (fun record => record.input.time.val) hBa).symm
    have htimeBidx :
        B[k.val].input.time.val = s + a.val :=
      htimeEq.symm.trans htimeA
    have ha : a.val = w + k.val := by
      dsimp only [u] at hwindow
      omega
    have hpriorFields := hprior0 k j.val (by omega)
      E0.records[j.val] (List.getElem?_eq_getElem j.isLt) i message hretained
    rcases hpriorFields with ⟨hmessage, hmessageSigma, hmessageQueue⟩
    let seed := ReferenceInitializationRun.ordinary x0 b0
      (ActualReferenceInitializationBlock.refFollower i)
    let memory := ActiveFollowerLifecycle.initialMemory p
    have hseedFacts := hseeds i
    change initial.followers i = .ordinary seed memory ∧
      seed.lastDown = none ∧ ReferencePrelaunchFollower.acceptedStart seed = 0 ∧
      seed.S = 0 ∧ seed.delta = 0 ∧ seed.backlog = 0 ∧
      seed.status = .unoccupied ∧
      ActiveFollowerLifecycle.localStateDomainValid seed ∧
      ActiveFollowerLifecycle.localBufferValid seed ∧
      seed.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound) ∧
      ∀ saved ∈ seed.buffer, saved.calendarRound ≤ s at hseedFacts
    rcases hseedFacts with
      ⟨hseed, hnoneSeed, _hstartSeed, _hSSeed, _hdeltaSeed, _hbacklogSeed,
        hunoccupiedSeed, _hdomainSeed, hvalidSeed, hpairSeed, htimeSeed⟩
    let currentIndex : Fin E0.records.length := ⟨w + k.val, hindex⟩
    have hlastChoice :
        (actualChoice E0.records[currentIndex.val] i).configuration =
          .ordinary choice mu := by
      dsimp only [currentIndex]
      rw [← hcurrent]
      exact hchoice
    have hjk : j.val < currentIndex.val := by
      dsimp only [currentIndex]
      omega
    have hReplay :=
      ReferenceFirstOfferedUpNumericalReplay.choice_replay_of_retained_first_down
        initial rows J rewards s count hspan active hfirst i seed memory hseed
        hnoneSeed hunoccupiedSeed hvalidSeed hpairSeed htimeSeed j currentIndex hjk
        message hretained hmessageSigma choice mu hlastChoice hlastDown hstatus
    let bits := FollowerCutoffScan.completeRowProposalBit p rate.eta.val (rows J)
    let cutoff := FollowerCutoffScan.firstCutoff p rate.eta.val
      (ActiveFollowerDownAcceptance.downStart p rate message) bits
    let m := cutoff - (s + 1)
    let V := fun h => QueueReplay.replay (4 * rate.n) (0, 0)
      (ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords E0.records i j.val message h)
    change s + 1 < cutoff ∧ 0 < m ∧ m ≤ currentIndex.val ∧
      max m (j.val + 1) ≤ currentIndex.val ∧
      choice.S = (V m).1 ∧ choice.backlog = (V m).2 ∧
      choice.delta = (V m).1 - (V (m - 1)).1 at hReplay
    have hdownStart :
        ActiveFollowerDownAcceptance.downStart p rate message = P0.sigma := by
      have hstartVal :
          (ActiveFollowerDownAcceptance.downStart p rate message).val = s := by
        have hstart := ActiveFollowerDownAcceptance.downStart_val_add_one p rate message
        rw [hmessageSigma] at hstart
        omega
      apply Fin.ext
      rw [hP0sigma]
      exact hstartVal
    have hcutoffEq : cutoff = u := by
      dsimp only [cutoff, bits, rows, J]
      rw [hdownStart]
      exact hfirstCutoff
    have hm : m = w := by
      dsimp only [m]
      rw [hcutoffEq]
      dsimp only [u]
      omega
    rcases hReplay with ⟨_hcutoffPositive, _hmPositive, _hmle, _hdle,
      hchoiceS, hchoiceQ, hchoiceDelta⟩
    have hchoiceS' : choice.S = (V w).1 := by simpa only [hm] using hchoiceS
    have hchoiceQ' : choice.backlog = (V w).2 := by simpa only [hm] using hchoiceQ
    have hchoiceDelta' :
        choice.delta = (V w).1 - (V (w - 1)).1 := by
      simpa only [hm] using hchoiceDelta
    have hlength : E0.records.length = count :=
      ReferenceActivePhysicalHorizon.run_record_count
        initial rows J rewards s count hspan active
    have hwlen : w ≤ E0.records.length := by
      rw [hlength]
      omega
    have hbounds :=
      ReferenceFirstOfferedUpNumericalReplay.first_reply_queue_records_bounds
        E0.records i j.val w message hwlen
    rcases hbounds with ⟨hlenRecords, harrival, hmass, hservice, hcapacity⟩
    have hfields' :
        M.val = ⟨ReferencePrelaunchFollower.acceptedStart choice,
          choice.S, choice.delta, choice.backlog⟩ := by
      simpa only [ActiveFollowerQueueOperation.upOfferFields] using hfields
    have hMsigma :
        M.val.sigma = ReferencePrelaunchFollower.acceptedStart choice :=
      congrArg (fun fields : OrdinaryMessageCodec.UpFields => fields.sigma) hfields'
    have hMS : M.val.S = choice.S :=
      congrArg (fun fields : OrdinaryMessageCodec.UpFields => fields.S) hfields'
    have hMdelta : M.val.delta = choice.delta :=
      congrArg (fun fields : OrdinaryMessageCodec.UpFields => fields.delta) hfields'
    have hMq : M.val.q = choice.backlog :=
      congrArg (fun fields : OrdinaryMessageCodec.UpFields => fields.q) hfields'
    have hMsigma' := hMsigma
    simp only [ReferencePrelaunchFollower.acceptedStart, hlastDown] at hMsigma'
    have hright0 :
        ∃ (j : Fin E0.records.length)
          (message : ReferenceFirstAcceptedUpNumericSnapshot.DownRecord
            (p := p) (rate := rate)),
          j.val < w + k.val ∧
          ReferenceAcceptedUpFollowerHistory.RetainedDown E0.records[j.val] i message ∧
          message = P0.downRecord i ∧
          choice.lastDown = some message ∧
          message.val.sigma = s + 1 ∧
          message.val.q = 0 ∧
          (let Frec :=
            ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords
              E0.records i j.val message w
           let V := fun h => QueueReplay.replay (4 * rate.n) (0, 0)
             (ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords
               E0.records i j.val message h)
           M.val.sigma = s + 1 ∧
           M.val.S = (V w).1 ∧
           M.val.q = (V w).2 ∧
           M.val.delta = (V w).1 - (V (w - 1)).1 ∧
           Frec.length = w ∧
           (∀ r ∈ Frec, r.2 ≤ D p) ∧
           (∀ h ≤ w, (V h).1 + (V h).2 ≤ h * D p) ∧
           (V w).1 - (V (w - 1)).1 ≤ 4 * rate.n ∧
           4 * rate.n ≤ D p) := by
      refine ⟨j, message, ?_, hretained, hmessage, hlastDown,
        hmessageSigma, hmessageQueue, ?_⟩
      · dsimp only [currentIndex] at hjk
        omega
      · change M.val.sigma = s + 1 ∧ M.val.S = (V w).1 ∧
          M.val.q = (V w).2 ∧
          M.val.delta = (V w).1 - (V (w - 1)).1 ∧
          (ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords
            E0.records i j.val message w).length = w ∧
          (∀ r ∈ ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords
            E0.records i j.val message w, r.2 ≤ D p) ∧
          (∀ h ≤ w, (V h).1 + (V h).2 ≤ h * D p) ∧
          (V w).1 - (V (w - 1)).1 ≤ 4 * rate.n ∧
          4 * rate.n ≤ D p
        exact ⟨hMsigma'.trans hmessageSigma, hMS.trans hchoiceS',
          hMq.trans hchoiceQ', hMdelta.trans hchoiceDelta',
          hlenRecords, harrival, hmass, hservice, hcapacity⟩
    have hrecordEq : E0.records = Erun.records :=
      congrArg (fun execution => execution.records) hE.symm
    have hrightRight :
        ∃ (j : Fin Erun.records.length)
          (message : ReferenceFirstAcceptedUpNumericSnapshot.DownRecord
            (p := p) (rate := rate)),
          j.val < w + k.val ∧
          ReferenceAcceptedUpFollowerHistory.RetainedDown Erun.records[j.val] i message ∧
          message = P0.downRecord i ∧
          choice.lastDown = some message ∧
          message.val.sigma = s + 1 ∧
          message.val.q = 0 ∧
          (let Frec :=
            ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords
              Erun.records i j.val message w
           let V := fun h => QueueReplay.replay (4 * rate.n) (0, 0)
             (ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords
               Erun.records i j.val message h)
           M.val.sigma = s + 1 ∧
           M.val.S = (V w).1 ∧
           M.val.q = (V w).2 ∧
           M.val.delta = (V w).1 - (V (w - 1)).1 ∧
           Frec.length = w ∧
           (∀ r ∈ Frec, r.2 ≤ D p) ∧
           (∀ h ≤ w, (V h).1 + (V h).2 ≤ h * D p) ∧
           (V w).1 - (V (w - 1)).1 ≤ 4 * rate.n ∧
           4 * rate.n ≤ D p) := by
      rcases hright0 with
        ⟨j0, message, hj0, hretained0, hmessage, hlastDown,
          hmessageSigma, hmessageQueue, hnumeric0⟩
      have hlengthEq : E0.records.length = Erun.records.length :=
        congrArg List.length hrecordEq
      have hjlt : j0.val < Erun.records.length := by
        rw [← hlengthEq]
        exact j0.isLt
      let j : Fin Erun.records.length := ⟨j0.val, hjlt⟩
      have hrecordAt0 : E0.records[j0.val] = Erun.records[j0.val] := by
        have hlookup := congrArg
          (fun records : List (ReferenceActivePhysicalHorizon.RoundRecord
            (p := p) (rate := rate)) => records[j0.val]?) hrecordEq
        rw [List.getElem?_eq_getElem j0.isLt] at hlookup
        rw [List.getElem?_eq_getElem hjlt] at hlookup
        exact Option.some.inj hlookup
      have hretained' : ReferenceAcceptedUpFollowerHistory.RetainedDown
          Erun.records[j.val] i message := by
        change ReferenceAcceptedUpFollowerHistory.RetainedDown
          Erun.records[j0.val] i message
        rw [← hrecordAt0]
        exact hretained0
      have hnumeric' :
          (let Frec :=
            ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords
              Erun.records i j.val message w
           let V := fun h => QueueReplay.replay (4 * rate.n) (0, 0)
             (ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords
               Erun.records i j.val message h)
           M.val.sigma = s + 1 ∧
           M.val.S = (V w).1 ∧
           M.val.q = (V w).2 ∧
           M.val.delta = (V w).1 - (V (w - 1)).1 ∧
           Frec.length = w ∧
           (∀ r ∈ Frec, r.2 ≤ D p) ∧
           (∀ h ≤ w, (V h).1 + (V h).2 ≤ h * D p) ∧
           (V w).1 - (V (w - 1)).1 ≤ 4 * rate.n ∧
           4 * rate.n ≤ D p) := by
        simpa only [j, hrecordEq] using hnumeric0
      exact ⟨j, message, by simpa only [j] using hj0,
        hretained', hmessage, hlastDown, hmessageSigma, hmessageQueue,
        hnumeric'⟩
    have hright :
        (choice.lastDown = none ∧ M.val = OrdinaryMessageCodec.upPlaceholder) ∨
          ∃ (j : Fin Erun.records.length)
            (message : ReferenceFirstAcceptedUpNumericSnapshot.DownRecord
              (p := p) (rate := rate)),
            j.val < w + k.val ∧
            ReferenceAcceptedUpFollowerHistory.RetainedDown Erun.records[j.val] i message ∧
            message = P0.downRecord i ∧
            choice.lastDown = some message ∧
            message.val.sigma = s + 1 ∧
            message.val.q = 0 ∧
            (let Frec :=
              ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords
                Erun.records i j.val message w
             let V := fun h => QueueReplay.replay (4 * rate.n) (0, 0)
               (ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords
                 Erun.records i j.val message h)
             M.val.sigma = s + 1 ∧
             M.val.S = (V w).1 ∧
             M.val.q = (V w).2 ∧
             M.val.delta = (V w).1 - (V (w - 1)).1 ∧
             Frec.length = w ∧
             (∀ r ∈ Frec, r.2 ≤ D p) ∧
             (∀ h ≤ w, (V h).1 + (V h).2 ≤ h * D p) ∧
             (V w).1 - (V (w - 1)).1 ≤ 4 * rate.n ∧
             4 * rate.n ≤ D p) := by
      exact Or.inr hrightRight
    exact hright

end Bandits.Support.ReferenceFirstCollectionOfferedSenderReplay

end
