/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bandits Lean regret formalization contributors.
-/
module

public import Bandits.Support.ReferenceFirstCutoffRecordedService

/-!
# Actual first-collection follower PREPARE

This module proves the local PREPARE operation on the actual records strictly
after the first cutoff in the original physical run.  The cutoff and its
collection service are obtained from the admitted recorded-service producer;
the local operation remains conditional on the explicit single-state
induction fields used by the later follower proof.

Source: `sources/zip4/manuscript/05_binary_transport.tex:70-124`,
`sources/zip4/manuscript/06_interruptions.tex:246-256,294`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:34-44,54-60`.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceFirstLiveConfirmationHistory
open Bandits.Support.ReferenceCollectionPhaseHistory
open Bandits.Support.ReferenceAssignmentPayloadChronology
open Bandits.Support.ReferenceAssignmentPayloadPersistence
open Bandits.Support.ReferencePrelaunchFollower
open Bandits.Support.ActiveFollowerLifecycle
open Bandits.Support.ActiveFollowerQueueOperation
open Bandits.Support.ActiveFollowerArmChoice
open Bandits.Support.DeclaredFollowerLocalRound
open Bandits.Support.OrdinaryMessageCodec
open Bandits.Support.FollowerCutoffScan
open Bandits.Support.OrderedTupleSampler
open Bandits.Support.PublicDiscreteDraws
open Bandits.Support.ActiveRoundActions

namespace Bandits.Support.ReferenceFirstCollectionFollowerPreparation

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput

variable {p : Parameters} {rate : RateInput p}

private theorem firstCollectionWindow_length_bound
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hshort : (firstLiveWindow
      (ReferenceActivePhysicalHorizon.run initial rows J rewards start count hspan active).records).length
        < count) :
    let execution := ReferenceActivePhysicalHorizon.run initial rows J rewards
      start count hspan active
    let d := (firstLiveWindow execution.records).length
    d + 1 + ((execution.records.drop (d + 1)).takeWhile
      (fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input)).length ≤ count := by
  let execution := ReferenceActivePhysicalHorizon.run initial rows J rewards
    start count hspan active
  let d := (firstLiveWindow execution.records).length
  have hcount : execution.records.length = count := by
    simpa [execution] using ReferenceActivePhysicalHorizon.run_record_count
      initial rows J rewards start count hspan active
  have hd : d < count := by
    simpa [execution, d] using hshort
  have hdrop : d + 1 ≤ execution.records.length := by omega
  have hprefix : ((execution.records.drop (d + 1)).takeWhile
      (fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input)) <+:
      execution.records.drop (d + 1) := List.takeWhile_prefix _
  have hlength := hprefix.length_le
  have htail : ((execution.records.drop (d + 1)).takeWhile
      (fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input)).length ≤
      count - (d + 1) := by
    simpa [List.length_drop, hcount] using hlength
  have hbound : d + 1 + ((execution.records.drop (d + 1)).takeWhile
      (fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input)).length ≤ count := by
    omega
  simpa [execution, d] using hbound

/-- Indexed records of the accepted physical fold are exactly the public
actual-record constructor at that original calendar coordinate. -/
private theorem run_records_getElem?_actualRunRecordAt
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (index : ℕ) (hindex : index < count) :
    (ReferenceActivePhysicalHorizon.run initial rows J rewards start count hspan active).records[index]? =
      some (ReferenceAssignmentPayloadChronology.actualRunRecordAt initial rows J rewards
        start index (by omega) active) := by
  induction count generalizing index with
  | zero => omega
  | succ count ih =>
      have hspan' : start + (count + 1) ≤ p.T := by omega
      have hprefixSpan : start + count ≤ p.T := by omega
      have hprefixLength :
          (ReferenceActivePhysicalHorizon.run initial rows J rewards start count
            hprefixSpan active).records.length = count :=
        ReferenceActivePhysicalHorizon.run_record_count initial rows J rewards start count
          hprefixSpan active
      rw [ReferenceAssignmentPayloadChronology.run_successor_actualRunRecordAt
        initial rows J rewards start count hspan' active]
      by_cases hlt : index < count
      · rw [List.getElem?_append_left (by simpa [hprefixLength] using hlt)]
        exact ih hprefixSpan index hlt
      · have hlast : index = count := by omega
        subst index
        simp [List.getElem?_append_right, hprefixLength]

private theorem firstChosen_payload_down_queue_zero
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (installed : CoordinatorAssignmentRegisterInstall.FirstInstallation
      (CoordinatorRoundDispatch.firstLaunchInput (ReferenceActivePhysicalStep.firstInput record.input)))
    (selection : CoordinatorRoundDispatch.ArmSelection installed.registers.payload
      installed.startRoundResult installed.registers.time installed.registers.complementWeights record.input.row)
    (hprep : record.output.preparation.coordinator = .first (.chosen installed selection))
    (i : Fin (p.m - 1)) :
    (installed.registers.payload.downRecord i).val.q = 0 := by
  have hdispatch : ReferenceActivePhysicalStep.dispatch record.input =
      .first (.chosen installed selection) :=
    record.output.preparation.coordinator_eq.symm.trans hprep
  have hfirst : record.input.state.coordinator = .first := by
    cases hc : record.input.state.coordinator with
    | first => rfl
    | live r q base =>
        simp only [ReferenceActivePhysicalStep.dispatch, hc,
          CoordinatorRoundDispatch.dispatch] at hdispatch
        cases hdispatch
    | collection payload ledger proposal =>
        simp only [ReferenceActivePhysicalStep.dispatch, hc] at hdispatch
        split at hdispatch <;> cases hdispatch
    | dagger =>
        simp only [ReferenceActivePhysicalStep.dispatch, hc] at hdispatch
        cases hdispatch
  have hchosen : CoordinatorRoundDispatch.dispatchFirst
      (ReferenceActivePhysicalStep.firstInput record.input) = .chosen installed selection := by
    rw [ReferenceActivePhysicalStep.dispatch_first record.input hfirst] at hdispatch
    exact ReferenceActivePhysicalStep.DispatchCut.first.inj hdispatch
  exact ReferenceAssignmentPayloadPersistence.firstChosen_down_queue_zero
    record.input installed selection hchosen i

private theorem local_prepare_of_actual_record
    (payload : AssignmentStartPayload.Input p rate.eta)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (current : ReferenceActivePhysicalHorizon.State p rate)
    (hrecordState : record.input.state = current)
    (d : ℕ)
    (hpayloadStartPositive : 1 ≤ payload.sigma.val + 1)
    (hpayloadStartBound : payload.sigma.val + 1 ≤ p.T)
    (i : Fin (p.m - 1))
    (s : ReferencePrelaunchFollower.State p rate.eta)
    (mu : ActiveFollowerLifecycle.LocalMemory p)
    (hordinary : current.followers i = .ordinary s mu)
    (hunoccupied : s.status = .unoccupied)
    (hS : s.S ≤ p.T * D p)
    (hdelta : s.delta ≤ D p)
    (hbacklog : s.backlog ≤ p.T * D p)
    (_hSbacklog : s.S + s.backlog ≤ d * D p)
    (hcalendar : ∀ z ∈ s.buffer, 1 ≤ z.calendarRound ∧ z.calendarRound ≤ p.T)
    (hkeys : (s.buffer.map fun z => (z.calendarRound, z.pilot)).Nodup)
    (hquantized : ∀ z ∈ s.buffer, ∃ q : ℕ, q ≤ D p ∧
      z.observation.val = (q : ℝ) / (D p : ℝ))
    (_hpairwise : List.Pairwise
      (fun (a b : SparseCalendarReplay.SparseCalendarRecord p.K) =>
        a.calendarRound < b.calendarRound) s.buffer)
    (_hchronological : ∀ z ∈ s.buffer,
      z.calendarRound < record.input.time.val + 1)
    (hpending : s.downBatch.pending.length < AffineBatchDecoder.quota p)
    (hcompleted : ∀ batch ∈ s.downBatch.completed,
      batch.length = AffineBatchDecoder.quota p)
    (hdown : (s.lastDown = none ∧ s.S = 0 ∧ s.delta = 0 ∧ s.backlog = 0) ∨
      s.lastDown = some (payload.downRecord i)) :
    ActiveFollowerLifecycle.startRound rate.eta record.input.time s mu = .ok (s, mu) ∧
    (record.output.preparation.followers.followers i).configuration = .ordinary s mu ∧
    (∀ hselected : ActiveFollowerQueueOperation.selectedUpRound i record.input.row
        (record.input.state.activations i) record.input.time,
      ∃ offered : OrdinaryMessageCodec.UpRecord
          (ReferencePrelaunchFollower.codecParams p rate.eta),
        ActiveFollowerQueueOperation.checkedUpOffer rate.eta i record.input.row
          (record.input.state.activations i) record.input.time s = .offer offered ∧
        offered.val = ActiveFollowerQueueOperation.upOfferFields s ∧
        OrdinaryMessageCodec.upAdmissible
          (ReferencePrelaunchFollower.codecParams p rate.eta) offered.val ∧
        record.output.preparation.arms.actions
          (PublicDiscreteDraws.followerPlayer p.two_le_m i) =
          ActiveRoundActions.sendArm
            (ActiveFollowerArmChoice.offeredUpBit rate.eta
              (record.input.row.2 record.input.time) i offered)
            ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K
              (record.input.row.2 record.input.time).1).val
                (PublicDiscreteDraws.followerPlayer p.two_le_m i))
            ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K
              (record.input.row.2 record.input.time).1).val
                (ActiveRoundActions.coordinator p.two_le_m))) ∧
    (¬ ActiveFollowerQueueOperation.selectedUpRound i record.input.row
        (record.input.state.activations i) record.input.time →
      ActiveFollowerQueueOperation.checkedUpOffer rate.eta i record.input.row
        (record.input.state.activations i) record.input.time s = .noOffer) ∧
    (PublicDiscreteDraws.slotDraw (record.input.row.2 record.input.time).1 =
        PublicDiscreteDraws.dataSlot →
      record.output.preparation.arms.actions
        (PublicDiscreteDraws.followerPlayer p.two_le_m i) =
        PublicDiscreteDraws.pilotDraw (K_pos p)
          (PublicDiscreteDraws.followerPlayer p.two_le_m i)
          (record.input.row.2 record.input.time).1) ∧
    (PublicDiscreteDraws.slotDraw (record.input.row.2 record.input.time).1 ≠
        PublicDiscreteDraws.dataSlot →
      ¬ (PublicDiscreteDraws.slotDraw (record.input.row.2 record.input.time).1 =
          PublicDiscreteDraws.upSlot ∧
        PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
          (record.input.row.2 record.input.time).1 = i) →
      record.output.preparation.arms.actions
        (PublicDiscreteDraws.followerPlayer p.two_le_m i) =
        (OrderedTupleSampler.sample p.two_le_m p.m_lt_K
          (record.input.row.2 record.input.time).1).val
          (PublicDiscreteDraws.followerPlayer p.two_le_m i)) := by
  have hrecordStateFollower : record.input.state.followers i = .ordinary s mu := by
    rw [hrecordState]
    exact hordinary
  have hlocalBuffer : ActiveFollowerLifecycle.localBufferValid s :=
    ⟨hcalendar, ⟨hkeys, hquantized⟩⟩
  have hdecoder : ActiveFollowerLifecycle.downDecoderStateValid s :=
    ⟨hpending, hcompleted⟩
  have hlocalDomain : ActiveFollowerLifecycle.localStateDomainValid s :=
    ⟨⟨hS, hdelta, hbacklog⟩, hlocalBuffer, hdecoder⟩
  have hstart := ActiveFollowerLifecycle.startRound_unoccupied rate.eta
    record.input.time s mu hlocalDomain hunoccupied
  have hstateInput : ActiveFollowerQueueOperation.stateInputDomain s := by
    refine ⟨hS, hdelta, hbacklog, hcalendar, ?_⟩
    change (s.buffer.map fun z => (z.calendarRound, z.pilot)).Nodup
    exact hkeys
  have hfieldsAdmissible :
      OrdinaryMessageCodec.upAdmissible
        (ReferencePrelaunchFollower.codecParams p rate.eta)
        (ActiveFollowerQueueOperation.upOfferFields s) := by
    rcases hdown with ⟨hnone, hSzero, hdeltaZero, hbacklogZero⟩ | hsome
    · simp [OrdinaryMessageCodec.upAdmissible, OrdinaryMessageCodec.upPlaceholder,
        ActiveFollowerQueueOperation.upOfferFields,
        ReferencePrelaunchFollower.acceptedStart, hnone, hSzero, hdeltaZero,
        hbacklogZero]
    · right
      have haccepted : ReferencePrelaunchFollower.acceptedStart s =
          payload.sigma.val + 1 := by
        have hrecordSigma : (payload.downRecord i).val.sigma = payload.sigma.val + 1 := rfl
        simp [ReferencePrelaunchFollower.acceptedStart, hsome, hrecordSigma]
      rw [ActiveFollowerQueueOperation.upOfferFields, haccepted]
      exact ⟨hpayloadStartPositive, hpayloadStartBound, hS, hdelta, hbacklog⟩
  let offered : OrdinaryMessageCodec.UpRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta) :=
    ⟨ActiveFollowerQueueOperation.upOfferFields s, hfieldsAdmissible⟩
  have hoffSelected : ∀ hselected : ActiveFollowerQueueOperation.selectedUpRound i
      record.input.row (record.input.state.activations i) record.input.time,
      ActiveFollowerQueueOperation.checkedUpOffer rate.eta i record.input.row
        (record.input.state.activations i) record.input.time s = .offer offered := by
    intro hselected
    unfold ActiveFollowerQueueOperation.checkedUpOffer
    rw [dif_pos hstateInput]
    rw [dif_pos ⟨hselected, hunoccupied⟩]
    rw [dif_pos hfieldsAdmissible]
  have hoffNotSelected : ∀ hnot : ¬ ActiveFollowerQueueOperation.selectedUpRound
      i record.input.row (record.input.state.activations i) record.input.time,
      ActiveFollowerQueueOperation.checkedUpOffer rate.eta i record.input.row
        (record.input.state.activations i) record.input.time s = .noOffer := by
    intro hnot
    apply ActiveFollowerQueueOperation.checkedUpOffer_noOffer rate.eta i
      record.input.row (record.input.state.activations i) record.input.time s hstateInput
    intro hselected
    exact hnot hselected.1
  have hprepareConfig :
      (DeclaredFollowerLocalRound.prepare rate i record.input.row
        (record.input.state.activations i) record.input.time
        (record.input.active i) (.ordinary s mu)).configuration = .ordinary s mu := by
    by_cases hdata : PublicDiscreteDraws.slotDraw (record.input.row.2 record.input.time).1 =
        PublicDiscreteDraws.dataSlot
    · have hnotSelected : ¬ ActiveFollowerQueueOperation.selectedUpRound i record.input.row
          (record.input.state.activations i) record.input.time := by
        rintro ⟨_, hslot, _⟩
        have hne : PublicDiscreteDraws.dataSlot ≠ PublicDiscreteDraws.upSlot := by
          simp [PublicDiscreteDraws.dataSlot, PublicDiscreteDraws.upSlot]
        exact hne (hdata.symm.trans hslot)
      have hoff := hoffNotSelected hnotSelected
      have hchoice := ActiveFollowerArmChoice.followerArmChoiceCore_unoccupied_data s
        (record.input.row.2 record.input.time) i none hunoccupied hdata
      have hchoice' : ActiveFollowerArmChoice.followerArmChoice s record.input.row
          record.input.time i none = some (PublicDiscreteDraws.pilotDraw (K_pos p)
            (PublicDiscreteDraws.followerPlayer p.two_le_m i)
            (record.input.row.2 record.input.time).1) := by
        rw [ActiveFollowerArmChoice.followerArmChoice_eq_core]
        exact hchoice
      simp [DeclaredFollowerLocalRound.prepare, hstart, hoff, hchoice']
    · by_cases hup : PublicDiscreteDraws.slotDraw (record.input.row.2 record.input.time).1 =
          PublicDiscreteDraws.upSlot ∧
          PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
            (record.input.row.2 record.input.time).1 = i
      · have hselected : ActiveFollowerQueueOperation.selectedUpRound i record.input.row
            (record.input.state.activations i) record.input.time := by
          exact ⟨record.input.active i, hup.1, hup.2⟩
        have hoff := hoffSelected hselected
        have hvalid : ActiveFollowerArmChoice.upStateDomain s ∧
            ActiveFollowerArmChoice.offeredUpMatchesState s offered := by
          constructor
          · exact ⟨hS, hdelta, hbacklog⟩
          · simp [ActiveFollowerArmChoice.offeredUpMatchesState, offered,
              ActiveFollowerQueueOperation.upOfferFields]
        have hchoiceCore := ActiveFollowerArmChoice.followerArmChoiceCore_unoccupied_selected_up
          s (record.input.row.2 record.input.time) i offered hunoccupied hup.1 hup.2 hvalid
        have hchoice : ActiveFollowerArmChoice.followerArmChoice s record.input.row
            record.input.time i (some offered) = some
              (ActiveRoundActions.sendArm
                (ActiveFollowerArmChoice.offeredUpBit rate.eta
                  (record.input.row.2 record.input.time) i offered)
                ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K
                  (record.input.row.2 record.input.time).1).val
                    (PublicDiscreteDraws.followerPlayer p.two_le_m i))
                ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K
                  (record.input.row.2 record.input.time).1).val
                    (ActiveRoundActions.coordinator p.two_le_m))) := by
          rw [ActiveFollowerArmChoice.followerArmChoice_eq_core]
          exact hchoiceCore
        simp [DeclaredFollowerLocalRound.prepare, hstart, hoff, hchoice]
      · have hnotSelected : ¬ ActiveFollowerQueueOperation.selectedUpRound i
            record.input.row (record.input.state.activations i) record.input.time := by
          intro h
          exact hup ⟨h.2.1, h.2.2⟩
        have hoff := hoffNotSelected hnotSelected
        have hchoiceCore := ActiveFollowerArmChoice.followerArmChoiceCore_unoccupied_other
          s (record.input.row.2 record.input.time) i none hunoccupied
          (by simpa [hdata]) hup
        have hchoice : ActiveFollowerArmChoice.followerArmChoice s record.input.row
            record.input.time i none = some
              ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K
                (record.input.row.2 record.input.time).1).val
                  (PublicDiscreteDraws.followerPlayer p.two_le_m i)) := by
          rw [ActiveFollowerArmChoice.followerArmChoice_eq_core]
          exact hchoiceCore
        simp [DeclaredFollowerLocalRound.prepare, hstart, hoff, hchoice]
  have hpreparedEq : record.output.preparation =
      ReferenceActivePhysicalStep.prepare record.input := by
    rw [record.output_eq]
    rfl
  have hfollowersEq : record.output.preparation.followers.followers i =
      DeclaredFollowerLocalRound.prepare rate i record.input.row
        (record.input.state.activations i) record.input.time
        (record.input.active i) (record.input.state.followers i) := by
    calc
      _ = (ReferenceActivePhysicalStep.prepare record.input).followers.followers i := by
        rw [hpreparedEq]
      _ = ReferenceActiveFeedbackCut.prepareFollowers
          (ReferenceActivePhysicalStep.followerInput record.input) i :=
        (ReferenceActivePhysicalStep.prepare record.input).followers.followers_eq i
      _ = DeclaredFollowerLocalRound.prepare rate i record.input.row
          (record.input.state.activations i) record.input.time
          (record.input.active i) (record.input.state.followers i) := by
        rfl
  have hactualConfig :
      (record.output.preparation.followers.followers i).configuration = .ordinary s mu := by
    rw [hfollowersEq, hrecordStateFollower]
    exact hprepareConfig
  have haction : record.output.preparation.arms.actions
      (PublicDiscreteDraws.followerPlayer p.two_le_m i) =
        (DeclaredFollowerLocalRound.prepare rate i record.input.row
          (record.input.state.activations i) record.input.time
          (record.input.active i) (record.input.state.followers i)).arm :=
    record.output.preparation.action_follower i
  have hselectedOffer : ∀ hselected : ActiveFollowerQueueOperation.selectedUpRound i
      record.input.row (record.input.state.activations i) record.input.time,
      ∃ actual : OrdinaryMessageCodec.UpRecord
          (ReferencePrelaunchFollower.codecParams p rate.eta),
        ActiveFollowerQueueOperation.checkedUpOffer rate.eta i record.input.row
          (record.input.state.activations i) record.input.time s = .offer actual ∧
        actual.val = ActiveFollowerQueueOperation.upOfferFields s ∧
        OrdinaryMessageCodec.upAdmissible
          (ReferencePrelaunchFollower.codecParams p rate.eta) actual.val ∧
        record.output.preparation.arms.actions
          (PublicDiscreteDraws.followerPlayer p.two_le_m i) =
          ActiveRoundActions.sendArm
            (ActiveFollowerArmChoice.offeredUpBit rate.eta
              (record.input.row.2 record.input.time) i actual)
            ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K
              (record.input.row.2 record.input.time).1).val
                (PublicDiscreteDraws.followerPlayer p.two_le_m i))
            ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K
              (record.input.row.2 record.input.time).1).val
                (ActiveRoundActions.coordinator p.two_le_m)) := by
    intro hselected
    refine ⟨offered, hoffSelected hselected, ?_, ?_, ?_⟩
    · rfl
    · exact hfieldsAdmissible
    · have hvalid : ActiveFollowerArmChoice.upStateDomain s ∧
          ActiveFollowerArmChoice.offeredUpMatchesState s offered := by
        constructor
        · exact ⟨hS, hdelta, hbacklog⟩
        · simp [ActiveFollowerArmChoice.offeredUpMatchesState, offered,
            ActiveFollowerQueueOperation.upOfferFields]
      have hoff := hoffSelected hselected
      rcases hselected with ⟨_, hslot, hselectedIndex⟩
      have hchoiceCore := ActiveFollowerArmChoice.followerArmChoiceCore_unoccupied_selected_up
        s (record.input.row.2 record.input.time) i offered hunoccupied hslot hselectedIndex hvalid
      rw [haction, hrecordStateFollower]
      simp [DeclaredFollowerLocalRound.prepare, hstart, hoff,
        ActiveFollowerArmChoice.followerArmChoice_eq_core, hchoiceCore]
  have hnoOffer : ¬ ActiveFollowerQueueOperation.selectedUpRound i record.input.row
      (record.input.state.activations i) record.input.time →
      ActiveFollowerQueueOperation.checkedUpOffer rate.eta i record.input.row
        (record.input.state.activations i) record.input.time s = .noOffer :=
    hoffNotSelected
  have hdataArm : PublicDiscreteDraws.slotDraw
      (record.input.row.2 record.input.time).1 = PublicDiscreteDraws.dataSlot →
      record.output.preparation.arms.actions
        (PublicDiscreteDraws.followerPlayer p.two_le_m i) =
        PublicDiscreteDraws.pilotDraw (K_pos p)
          (PublicDiscreteDraws.followerPlayer p.two_le_m i)
          (record.input.row.2 record.input.time).1 := by
    intro hdata
    have hnotSelected : ¬ ActiveFollowerQueueOperation.selectedUpRound i record.input.row
        (record.input.state.activations i) record.input.time := by
      rintro ⟨_, hslot, _⟩
      have hne : PublicDiscreteDraws.dataSlot ≠ PublicDiscreteDraws.upSlot := by
        simp [PublicDiscreteDraws.dataSlot, PublicDiscreteDraws.upSlot]
      exact hne (hdata.symm.trans hslot)
    have hoff := hoffNotSelected hnotSelected
    have hchoice := ActiveFollowerArmChoice.followerArmChoiceCore_unoccupied_data s
      (record.input.row.2 record.input.time) i none hunoccupied hdata
    have hchoice' : ActiveFollowerArmChoice.followerArmChoice s record.input.row
        record.input.time i none = some (PublicDiscreteDraws.pilotDraw (K_pos p)
          (PublicDiscreteDraws.followerPlayer p.two_le_m i)
          (record.input.row.2 record.input.time).1) := by
      rw [ActiveFollowerArmChoice.followerArmChoice_eq_core]
      exact hchoice
    rw [haction, hrecordStateFollower]
    simpa [DeclaredFollowerLocalRound.prepare, hstart, hoff, hchoice']
  have hotherArm : PublicDiscreteDraws.slotDraw
      (record.input.row.2 record.input.time).1 ≠ PublicDiscreteDraws.dataSlot →
      ¬ (PublicDiscreteDraws.slotDraw (record.input.row.2 record.input.time).1 =
          PublicDiscreteDraws.upSlot ∧
        PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
          (record.input.row.2 record.input.time).1 = i) →
      record.output.preparation.arms.actions
        (PublicDiscreteDraws.followerPlayer p.two_le_m i) =
        (OrderedTupleSampler.sample p.two_le_m p.m_lt_K
          (record.input.row.2 record.input.time).1).val
          (PublicDiscreteDraws.followerPlayer p.two_le_m i) := by
    intro hnotdata hnotselected
    have hnotUp : ¬ ActiveFollowerQueueOperation.selectedUpRound i record.input.row
        (record.input.state.activations i) record.input.time := by
      intro h
      exact hnotselected ⟨h.2.1, h.2.2⟩
    have hoff := hoffNotSelected hnotUp
    have hchoice := ActiveFollowerArmChoice.followerArmChoiceCore_unoccupied_other s
      (record.input.row.2 record.input.time) i none hunoccupied hnotdata hnotselected
    have hchoice' : ActiveFollowerArmChoice.followerArmChoice s record.input.row
        record.input.time i none = some
          ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K
            (record.input.row.2 record.input.time).1).val
              (PublicDiscreteDraws.followerPlayer p.two_le_m i)) := by
      rw [ActiveFollowerArmChoice.followerArmChoice_eq_core]
      exact hchoice
    rw [haction, hrecordStateFollower]
    simpa [DeclaredFollowerLocalRound.prepare, hstart, hoff, hchoice']
  exact ⟨hstart, hactualConfig, hselectedOffer, hnoOffer, hdataArm, hotherArm⟩

/-- The actual first-cutoff PREPARE producer for one original run and one
whole private row index. The cutoff, its dispatcher witnesses, first DOWN
queue values, and recorded stage-(1) service are outputs of the actual
producers. Each later result is conditional on the explicitly displayed
single-current-state follower fields; no history-wide survival premise is
introduced. The `hrecord` guard permits the final live-window boundary record
when it exists, while never creating a record when the original run ends. -/
theorem run_first_collection_follower_preparation_step
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hfirst : initial.coordinator = .first)
    (hshort : (firstLiveWindow
      (ReferenceActivePhysicalHorizon.run initial rows J rewards start count hspan active).records).length
        < count) :
    let execution := ReferenceActivePhysicalHorizon.run initial rows J rewards
      start count hspan active
    let window := firstLiveWindow execution.records
    let d := window.length
    let b := d + 1
    let W := (execution.records.drop b).takeWhile
      (fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input)
    ∃ cut suffix,
      execution.records = window ++ cut :: suffix ∧
      cut = execution.records[d]'(by
        simpa [execution, ReferenceActivePhysicalHorizon.run_record_count] using hshort) ∧
      cut.input.time.val = start + d ∧
      ∃ (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
        (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
        (base : Fin (p.m - 1) → ℕ),
        cut.input.state = (ReferenceActivePhysicalHorizon.run initial rows J rewards start d
          (by
            have hd : d < count := by simpa [execution, window, d] using hshort
            exact le_trans (Nat.add_le_add_left (Nat.le_of_lt hd) start) hspan) active).finalState ∧
        (ReferenceActivePhysicalHorizon.run initial rows J rewards start d
          (by
            have hd : d < count := by simpa [execution, window, d] using hshort
            exact le_trans (Nat.add_le_add_left (Nat.le_of_lt hd) start) hspan) active).finalState.coordinator =
          .live r q base ∧
        let callInput := ReferenceActivePhysicalStep.liveInput cut.input r q base
        ∃ (dispatched : CoordinatorStartRoundCutoffDispatch.Output
            callInput.registers callInput.ownedRegisters base)
          (hstart : CoordinatorPhaseClock.startRound p rate.eta.val
            callInput.registers.time callInput.registers.priorClock
            callInput.registers.clockPending = .ok dispatched.startResult)
          (ledger : CoordinatorStartRoundCutoffDispatch.NewLedger callInput.registers)
          (hinit : dispatched.collectionInitialization = .success (some ledger))
          (hledger : ledger = CoordinatorStartRoundCutoffDispatch.collectionStartLedger
            callInput.registers callInput.ownedRegisters base callInput.registers.time)
          (hdomain : CoordinatorStartRoundCutoffDispatch.initializationDomainValid
            callInput.registers callInput.ownedRegisters base callInput.registers.time)
          (hclock : dispatched.startResult.clock =
            { callInput.registers.priorClock with u := some callInput.registers.time })
          (hpending : dispatched.startResult.pending = Finset.univ)
          (hnoAssignment : dispatched.startResult.assignmentStart = none)
          (selected : CoordinatorRoundDispatch.ArmSelection callInput.registers.payload
            dispatched.startResult callInput.registers.time
            callInput.registers.complementWeights cut.input.row),
          cut.output.preparation.coordinator = .live r q base
            (.cutoffChosen dispatched hstart ledger hinit hledger hdomain hclock hpending
              hnoAssignment selected) ∧
          r.payload.sigma.val = start ∧
          let u := cut.input.time.val + 1
          FollowerCutoffScan.firstCutoff p rate.eta.val r.payload.sigma
            (FollowerCutoffScan.completeRowProposalBit p rate.eta.val (rows J)) = u ∧
          u ≤ p.T ∧
          (∀ i : Fin (p.m - 1), (r.payload.downRecord i).val.q = 0) ∧
          ∀ (j : ℕ) (hj : j ≤ W.length)
            (hrecord : b + j < execution.records.length)
            (i : Fin (p.m - 1))
            (s : ReferencePrelaunchFollower.State p rate.eta)
            (mu : ActiveFollowerLifecycle.LocalMemory p),
            (ReferenceActivePhysicalHorizon.run initial rows J rewards (start) (b + j)
              (by
                have hwindow : b + W.length ≤ count := by
                  simpa [execution, window, W, d, b] using
                    firstCollectionWindow_length_bound initial rows J rewards
                      start count hspan active hshort
                have : j ≤ W.length := hj
                omega) active).finalState.followers i = .ordinary s mu →
            s.status = .unoccupied →
            s.S ≤ p.T * D p →
            s.delta ≤ D p →
            s.backlog ≤ p.T * D p →
            s.S + s.backlog ≤ d * D p →
            (∀ z ∈ s.buffer, 1 ≤ z.calendarRound ∧ z.calendarRound ≤ p.T) →
            (s.buffer.map fun z => (z.calendarRound, z.pilot)).Nodup →
            (∀ z ∈ s.buffer, ∃ q : ℕ, q ≤ D p ∧
              z.observation.val = (q : ℝ) / (D p : ℝ)) →
            List.Pairwise
              (fun (a b : SparseCalendarReplay.SparseCalendarRecord p.K) =>
                a.calendarRound < b.calendarRound) s.buffer →
            (∀ z ∈ s.buffer, z.calendarRound < start + b + j + 1) →
            s.downBatch.pending.length < AffineBatchDecoder.quota p →
            (∀ batch ∈ s.downBatch.completed,
              batch.length = AffineBatchDecoder.quota p) →
            ((s.lastDown = none ∧ s.S = 0 ∧ s.delta = 0 ∧ s.backlog = 0) ∨
              s.lastDown = some (r.payload.downRecord i)) →
            let record := execution.records[b + j]'hrecord
            ActiveFollowerLifecycle.startRound rate.eta record.input.time s mu =
              .ok (s, mu) ∧
            (record.output.preparation.followers.followers i).configuration = .ordinary s mu ∧
            (∀ hselected : ActiveFollowerQueueOperation.selectedUpRound i record.input.row
                (record.input.state.activations i) record.input.time,
              ∃ offered : OrdinaryMessageCodec.UpRecord
                  (ReferencePrelaunchFollower.codecParams p rate.eta),
                ActiveFollowerQueueOperation.checkedUpOffer rate.eta i record.input.row
                  (record.input.state.activations i) record.input.time s = .offer offered ∧
                offered.val = ActiveFollowerQueueOperation.upOfferFields s ∧
                OrdinaryMessageCodec.upAdmissible
                  (ReferencePrelaunchFollower.codecParams p rate.eta) offered.val ∧
                record.output.preparation.arms.actions
                  (PublicDiscreteDraws.followerPlayer p.two_le_m i) =
                  ActiveRoundActions.sendArm
                    (ActiveFollowerArmChoice.offeredUpBit rate.eta
                      (record.input.row.2 record.input.time) i offered)
                    ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K
                      (record.input.row.2 record.input.time).1).val
                        (PublicDiscreteDraws.followerPlayer p.two_le_m i))
                    ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K
                      (record.input.row.2 record.input.time).1).val
                        (ActiveRoundActions.coordinator p.two_le_m))) ∧
            (¬ ActiveFollowerQueueOperation.selectedUpRound i record.input.row
                (record.input.state.activations i) record.input.time →
              ActiveFollowerQueueOperation.checkedUpOffer rate.eta i record.input.row
                (record.input.state.activations i) record.input.time s = .noOffer) ∧
            (PublicDiscreteDraws.slotDraw (record.input.row.2 record.input.time).1 =
                PublicDiscreteDraws.dataSlot →
              record.output.preparation.arms.actions
                (PublicDiscreteDraws.followerPlayer p.two_le_m i) =
                PublicDiscreteDraws.pilotDraw (K_pos p)
                  (PublicDiscreteDraws.followerPlayer p.two_le_m i)
                  (record.input.row.2 record.input.time).1) ∧
            (PublicDiscreteDraws.slotDraw (record.input.row.2 record.input.time).1 ≠
                PublicDiscreteDraws.dataSlot →
              ¬ (PublicDiscreteDraws.slotDraw (record.input.row.2 record.input.time).1 =
                  PublicDiscreteDraws.upSlot ∧
                PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
                  (record.input.row.2 record.input.time).1 = i) →
              record.output.preparation.arms.actions
                (PublicDiscreteDraws.followerPlayer p.two_le_m i) =
                (OrderedTupleSampler.sample p.two_le_m p.m_lt_K
                  (record.input.row.2 record.input.time).1).val
                  (PublicDiscreteDraws.followerPlayer p.two_le_m i)) := by
  classical
  let execution := ReferenceActivePhysicalHorizon.run initial rows J rewards
    start count hspan active
  let window := firstLiveWindow execution.records
  let d := window.length
  let b := d + 1
  let W := (execution.records.drop b).takeWhile
    (fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input)
  have hservice := ReferenceFirstCutoffRecordedService.run_first_cutoff_recorded_service
    initial rows J rewards start count hspan active hfirst (by simpa [execution] using hshort)
  have hcutoff := ReferenceFirstCutoffOutsideInitialization.run_first_cutoff_outside_initializer
    initial rows J rewards start count hspan active hfirst (by simpa [execution] using hshort)
  dsimp only [execution, window, d] at hservice
  rcases hservice with ⟨serviceCut, serviceSuffix, hserviceParts⟩
  rcases hcutoff with ⟨cut, suffix, hcutParts⟩
  have hparts := hcutParts.1
  have hindex := hcutParts.2.1
  have htime := hcutParts.2.2.1
  have hactualRecord := hcutParts.2.2.2.1
  have hstateWitness := hcutParts.2.2.2.2
  rcases hstateWitness with ⟨r, q, base, hstate, hprefixLive, hcall⟩
  dsimp only at hcall
  rcases hcall with ⟨dispatched, hstart, ledger, hinit, hledger, hdomain,
    hclock, hpending, hnoAssignment, selected, hbranchRest⟩
  rcases hbranchRest with ⟨hbranch, hpositive, hsigma, hbaseZero,
    hbirth, _hproposalHistory, _hdiagnosticReplay, hcutoffFacts⟩
  rcases hbirth with ⟨birth, hbirthMem, hbirth, hbirthTime, installed,
    birthSelection, hbirthBranch, hbirthPayload⟩
  rcases hcutoffFacts with ⟨_huEq, _hsigmaBeforeU, _huBound, _huGrid,
    _hgridBound, _hledgerSigma, _hledgerCutoff, _hledgerFreeze,
    hfirstCutoff, _⟩
  have hsameCut : serviceCut = cut := by
    have hserviceIndex := hserviceParts.2.1
    calc
      serviceCut = execution.records[d]'(by
        simpa [execution, ReferenceActivePhysicalHorizon.run_record_count] using hshort) := by
          simpa [execution, window, d] using hserviceIndex
      _ = cut := by
        have hcutIndex : cut = execution.records[d]'(by
            simpa [execution, ReferenceActivePhysicalHorizon.run_record_count] using hshort) := by
          simpa [execution, window, d] using hindex
        exact hcutIndex.symm
  cases hsameCut
  let cut := serviceCut
  rcases hserviceParts.2.2.2 with ⟨serviceR, serviceQ, serviceBase,
    hserviceState, hservicePrefix, hserviceCall⟩
  rcases hserviceCall with ⟨serviceDispatch, serviceStart, serviceLedger,
    serviceInit, serviceLedgerEq, serviceDomain, serviceClock, servicePending,
    serviceNoAssignment, serviceSelected, hserviceBranch, _⟩
  have hservicePayloadEq : serviceR.payload = r.payload := by
    have hbranchEq : DispatchCut.live serviceR serviceQ serviceBase
        (.cutoffChosen serviceDispatch serviceStart serviceLedger serviceInit serviceLedgerEq
          serviceDomain serviceClock servicePending serviceNoAssignment serviceSelected) =
        DispatchCut.live r q base
          (.cutoffChosen dispatched hstart ledger hinit hledger hdomain hclock hpending
            hnoAssignment selected) := by
      exact hserviceBranch.symm.trans hbranch
    injection hbranchEq with hr
    exact congrArg CoordinatorLiveChoiceRecorderStep.Registers.payload hr
  have hcutoffEndpoint :
      FollowerCutoffScan.firstCutoff p rate.eta.val r.payload.sigma
        (FollowerCutoffScan.completeRowProposalBit p rate.eta.val (rows J)) =
          cut.input.time.val + 1 := by
    change FollowerCutoffScan.firstCutoff p rate.eta.val r.payload.sigma
      (FollowerCutoffScan.completeRowProposalBit p rate.eta.val (rows J)) =
        serviceCut.input.time.val + 1
    exact hfirstCutoff
  have hqzero : ∀ i : Fin (p.m - 1), (r.payload.downRecord i).val.q = 0 := by
    intro i
    have hzero := firstChosen_payload_down_queue_zero birth installed
      birthSelection hbirthBranch i
    have hpayloadBirth : installed.registers.payload = r.payload := hbirthPayload
    rw [hpayloadBirth] at hzero
    exact hzero
  refine ⟨cut, suffix, ?_, ?_, ?_, ?_⟩
  · simpa [execution, window, d] using hparts
  · simpa [execution, window, d] using hindex
  · simpa [execution, window, d] using htime
  · refine ⟨r, q, base, ?_, ?_, ?_⟩
    · simpa [execution, window, d] using hstate
    · simpa [execution, window, d] using hprefixLive
    · dsimp only
      refine ⟨dispatched, hstart, ledger, hinit, hledger, hdomain, hclock,
        hpending, hnoAssignment, selected, ?_⟩
      refine ⟨hbranch, hsigma, ?_, ?_, hqzero, ?_⟩
      · exact hcutoffEndpoint
      · have hd : d < count := by simpa [execution, window, d] using hshort
        have hu : start + d + 1 ≤ p.T := by omega
        simpa [htime] using hu
      · intro j hj hrecord i s mu hordinary hunoccupied hS hdelta hbacklog hSbacklog
        intro hcalendar hkeys hquantized hpairwise hchronological hpending hcompleted hdown
        have hwindowBound := firstCollectionWindow_length_bound
          initial rows J rewards start count hspan active (by simpa [execution] using hshort)
        have hwindowBound' : b + W.length ≤ count := by
          simpa [execution, window, W, d, b] using hwindowBound
        have hprefixSpan : start + (b + j) ≤ p.T := by
          have hprefixCount : b + j ≤ count :=
            Nat.le_trans (Nat.add_le_add_left hj b) hwindowBound'
          exact le_trans (Nat.add_le_add_left hprefixCount start) hspan
        let prefixRun := ReferenceActivePhysicalHorizon.run initial rows J rewards
          start (b + j) hprefixSpan active
        let record := execution.records[b + j]'hrecord
        have hcount : execution.records.length = count := by
          simpa [execution] using ReferenceActivePhysicalHorizon.run_record_count
            initial rows J rewards start count hspan active
        have hrecord' : b + j < execution.records.length := by
          simpa [execution, window, d, b] using hrecord
        have hindexCount : b + j < count := by simpa [hcount] using hrecord'
        have hrecordLookup := run_records_getElem?_actualRunRecordAt initial rows J rewards
          start count hspan active (b + j) hindexCount
        have hrecordEq : record = ReferenceAssignmentPayloadChronology.actualRunRecordAt
            initial rows J rewards start (b + j) (by omega) active := by
          rw [List.getElem?_eq_getElem hrecord] at hrecordLookup
          exact Option.some.inj hrecordLookup
        have hrecordState : record.input.state = prefixRun.finalState := by
          rw [hrecordEq]
          rfl
        have htimeRecord : record.input.time.val = start + b + j := by
          rw [hrecordEq]
          dsimp [ReferenceAssignmentPayloadChronology.actualRunRecordAt,
            ReferenceActivePhysicalHorizon.roundInputAt]
          omega
        have hchronologicalRecord : ∀ z ∈ s.buffer,
            z.calendarRound < record.input.time.val + 1 := by
          intro z hz
          rw [htimeRecord]
          exact hchronological z hz
        have hpayloadStart : serviceR.payload.sigma.val = start := by
          rw [hservicePayloadEq]
          exact hsigma
        have hpayloadPos : 1 ≤ serviceR.payload.sigma.val + 1 := by omega
        have hpayloadBound : serviceR.payload.sigma.val + 1 ≤ p.T := by
          have hd : d < count := by simpa [execution, window, d] using hshort
          have hu : serviceR.payload.sigma.val + 1 < cut.input.time.val + 1 := by
            rw [hservicePayloadEq, hsigma, htime]
            omega
          have huT : cut.input.time.val + 1 ≤ p.T := by
            have hu : start + d + 1 ≤ p.T := by omega
            simpa [htime] using hu
          omega
        have hdownService :
            (s.lastDown = none ∧ s.S = 0 ∧ s.delta = 0 ∧ s.backlog = 0) ∨
              s.lastDown = some (serviceR.payload.downRecord i) := by
          rcases hdown with hnone | hsome
          · exact Or.inl hnone
          · right
            have hDownEq : r.payload.downRecord i = serviceR.payload.downRecord i :=
              congrArg (fun x : AssignmentStartPayload.Input p rate.eta => x.downRecord i)
                hservicePayloadEq.symm
            rw [hDownEq] at hsome
            exact hsome
        have hstep := local_prepare_of_actual_record serviceR.payload record
          prefixRun.finalState hrecordState d hpayloadPos hpayloadBound i s mu hordinary
          hunoccupied hS hdelta hbacklog hSbacklog hcalendar hkeys hquantized hpairwise
          hchronologicalRecord hpending hcompleted hdownService
        simpa [prefixRun, record, execution] using hstep

end Bandits.Support.ReferenceFirstCollectionFollowerPreparation

end
