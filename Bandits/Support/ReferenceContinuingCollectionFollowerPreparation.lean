/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bandits Lean regret formalization contributors.
-/
module

public import Bandits.Support.ReferenceCollectionCutoffSourceHistory
public import Bandits.Support.ReferenceOccupiedFollowerCutoffHistory

import Lean.Elab.Tactic.Omega

/-!
# Continuing collection follower PREPARE cases

This module joins the actual continuing-collection clock and occupied-follower
cutoff bounds to the local PREPARE operation on the existing physical run.
It retains incoming and outgoing dagger cases, checked UP offers, and the
actual choice equations.  The readout result remains optional when a follower
is dagger.

Sources: `sources/zip4/manuscript/05_binary_transport.tex:70-124,354-431`,
`sources/zip4/manuscript/06_interruptions.tex:9-70,192-233,246-295`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-64`.

These are internal constructor cases. They establish no ordinary-availability
induction, numerical arrival coverage, score or queue truth, overflow result,
section closure, or regret theorem.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions
open ReferenceActivePhysicalStep
open ReferenceActivePhysicalHorizon
open ReferenceCompletePhysicalHistory
open ReferencePrelaunchFollower
open ActiveFollowerLifecycle
open ActiveFollowerQueueOperation
open ActiveFollowerArmChoice
open DeclaredFollowerLocalRound
open OrdinaryMessageCodec
open ReferenceFollowerDecoderChronology
open ReferenceFollowerReplyChronology
open ReferenceOccupiedFieldHistory
open ReferenceCollectionCutoffSourceHistory
open ReferenceOccupiedFollowerCutoffHistory
open ReferenceLaterCollectionArrivalReadout
open FollowerCutoffScan
open OrderedTupleSampler
open PublicDiscreteDraws
open ActiveRoundActions

namespace Bandits.Support.ReferenceContinuingCollectionFollowerPreparation

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

private theorem run_records_getElem?_actualRunRecordAt
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (index : ℕ) (hindex : index < count) :
    (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count
      hspan active).records[index]? =
      some (ReferenceAssignmentPayloadChronology.actualRunRecordAt initial rows
        selected rewards start index (by omega) active) := by
  induction count generalizing index with
  | zero => omega
  | succ count ih =>
      have hspan' : start + (count + 1) ≤ p.T := by omega
      have hprefixSpan : start + count ≤ p.T := by omega
      have hprefixLength :
          (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count
            hprefixSpan active).records.length = count :=
        ReferenceActivePhysicalHorizon.run_record_count initial rows selected rewards
          start count hprefixSpan active
      rw [ReferenceAssignmentPayloadChronology.run_successor_actualRunRecordAt
        initial rows selected rewards start count hspan' active]
      by_cases hlt : index < count
      · rw [List.getElem?_append_left (by simpa [hprefixLength] using hlt)]
        exact ih hprefixSpan index hlt
      · have hlast : index = count := by omega
        subst index
        simp [List.getElem?_append_right, hprefixLength]

private theorem releaseAndFinish_ordinary_success_domain
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (t : Fin p.T) (observation : ReferencePrelaunchFollower.Observation p)
    (choice : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (post next : ReferencePrelaunchFollower.State p rate.eta)
    (nextMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hfinish : DeclaredFollowerLocalRound.releaseAndFinish rate i row t observation
      choice memory post = .ok (next, nextMemory)) :
    ActiveFollowerLifecycle.localStateDomainValid next ∧
      (next.status = .unoccupied → nextMemory = memory) := by
  have hfinishOriginal := hfinish
  unfold DeclaredFollowerLocalRound.releaseAndFinish at hfinish
  cases hrelease : ActiveFollowerLifecycle.releaseAfterService rate.eta i t
      (ActiveFollowerLifecycle.publicRowOfCompleteRow row t) observation choice post with
  | error reason => simp [hrelease] at hfinish
  | ok released =>
      cases hroundCall : ActiveFollowerLifecycle.finishRound rate.eta t row released memory with
      | error reason => simp [hrelease, hroundCall] at hfinish
      | ok pair =>
          have hpair : pair = (next, nextMemory) := by
            simpa [hrelease, hroundCall] using hfinish
          have hround : ActiveFollowerLifecycle.finishRound rate.eta t row released memory =
              .ok (next, nextMemory) := by
            rw [hroundCall, hpair]
          have hvalid : ActiveFollowerLifecycle.localStateDomainValid released := by
            by_contra hbad
            rw [ActiveFollowerLifecycle.finishRound_invalid_domain rate.eta t row released
              memory hbad] at hround
            cases hround
          have hframe := ActiveFollowerLifecycle.finishRound_frame rate.eta t row released
            next memory nextMemory hround
          refine ⟨?_, ?_⟩
          · rw [hframe]
            exact hvalid
          · intro hunoccupied
            have hreleased : released.status = .unoccupied := by
              rw [← hframe]
              exact hunoccupied
            have hcanonical := DeclaredFollowerLocalRound.releaseAndFinish_unoccupied_memory
              rate i row t observation choice memory post released hrelease hvalid hreleased
            have hpairs := Except.ok.inj (hcanonical.symm.trans hfinishOriginal)
            exact (congrArg Prod.snd hpairs).symm

private theorem actualCollection_prepare_selection_payload
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (clock : CoordinatorPhaseClock.ClockRegisters p) (cutoff : Fin p.T)
    (core : CoordinatorRoundDispatch.CollectionCoreValid
      (ReferenceActivePhysicalStep.collectionInput record.input payload ledger clock cutoff))
    (snapshot : CoordinatorCollectionInteractive.PreparedSnapshot
      (ReferenceActivePhysicalStep.collectionInput record.input payload ledger clock cutoff))
    (boundary : snapshot.clockStarted.clock.g ≤ p.T + 1)
    (scores : CoordinatorRoundDispatch.collectionCurrentScoresCheck
      (ReferenceActivePhysicalStep.collectionInput record.input payload ledger clock cutoff) = true)
    (hcoord : record.output.preparation.coordinator =
      .collection payload ledger clock cutoff (.continuing core snapshot boundary scores)) :
    ∃ selected : ReferenceActivePhysicalStep.Selection record.input,
      record.output.preparation.coordinator.selection = some selected ∧
        selected.view.payload = payload := by
  have hselection : ∃ selected : ReferenceActivePhysicalStep.Selection record.input,
      (ReferenceActivePhysicalStep.prepare record.input).coordinator.selection = some selected := by
    have hprep : record.output.preparation = ReferenceActivePhysicalStep.prepare record.input := by
      rw [record.output_eq]
      rfl
    have hpreparedCoord : (ReferenceActivePhysicalStep.prepare record.input).coordinator =
        .collection payload ledger clock cutoff (.continuing core snapshot boundary scores) := by
      have hc := congrArg (fun prepared : ReferenceActivePhysicalStep.PreparedRound record.input =>
        prepared.coordinator) hprep.symm
      exact hc.trans hcoord
    rw [hpreparedCoord]
    simp [ReferenceActivePhysicalStep.DispatchCut.selection]
  rcases hselection with ⟨selected, hselected⟩
  have hprep : record.output.preparation = ReferenceActivePhysicalStep.prepare record.input := by
    rw [record.output_eq]
    rfl
  have hpreparedCoord : (ReferenceActivePhysicalStep.prepare record.input).coordinator =
      .collection payload ledger clock cutoff (.continuing core snapshot boundary scores) := by
    have hc := congrArg (fun prepared : ReferenceActivePhysicalStep.PreparedRound record.input =>
      prepared.coordinator) hprep.symm
    exact hc.trans hcoord
  have hselected' : record.output.preparation.coordinator.selection = some selected := by
    have hc := congrArg (fun prepared : ReferenceActivePhysicalStep.PreparedRound record.input =>
      prepared.coordinator.selection) hprep
    exact hc.trans hselected
  have hselectedPayload : selected.view.payload = payload := by
    have h := hselected
    rw [hpreparedCoord] at h
    simp only [ReferenceActivePhysicalStep.DispatchCut.selection] at h
    have heq := Option.some.inj h
    exact congrArg (fun value : ReferenceActivePhysicalStep.Selection record.input =>
      value.view.payload) heq.symm
  exact ⟨selected, hselected', hselectedPayload⟩

private theorem actual_prepare_unoccupied_follower_cases
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (activation : ReferencePrelaunchFollower.Activation p) (t : Fin p.T)
    (active : activation.val ≤ t.val + 1)
    (old : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hstatus : old.status = .unoccupied)
    (hstart : ActiveFollowerLifecycle.startRound rate.eta t old memory = .ok (old, memory))
    (hstateInput : ActiveFollowerQueueOperation.stateInputDomain old)
    (hadmissible : OrdinaryMessageCodec.upAdmissible
      (ReferencePrelaunchFollower.codecParams p rate.eta)
      (ActiveFollowerQueueOperation.upOfferFields old))
    (prepared : DeclaredFollowerLocalRound.PreparedRound p rate)
    (hprepared : prepared = DeclaredFollowerLocalRound.prepare rate i row activation t active
      (.ordinary old memory)) :
    prepared.configuration = .ordinary old memory ∧
    (∀ hselected : ActiveFollowerQueueOperation.selectedUpRound i row activation t,
      ∃ offered : OrdinaryMessageCodec.UpRecord
          (ReferencePrelaunchFollower.codecParams p rate.eta),
        ActiveFollowerQueueOperation.checkedUpOffer rate.eta i row activation t old =
          .offer offered ∧ offered.val = ActiveFollowerQueueOperation.upOfferFields old ∧
        ActiveFollowerArmChoice.followerArmChoice old row t i (some offered) =
          some prepared.arm ∧
        prepared.arm = ActiveRoundActions.sendArm
          (ActiveFollowerArmChoice.offeredUpBit rate.eta (row.2 t) i offered)
          ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K (row.2 t).1).val
            (PublicDiscreteDraws.followerPlayer p.two_le_m i))
          ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K (row.2 t).1).val
            (ActiveRoundActions.coordinator p.two_le_m))) ∧
    (¬ ActiveFollowerQueueOperation.selectedUpRound i row activation t →
      ActiveFollowerQueueOperation.checkedUpOffer rate.eta i row activation t old = .noOffer ∧
      ActiveFollowerArmChoice.followerArmChoice old row t i none = some prepared.arm) ∧
    (PublicDiscreteDraws.slotDraw (row.2 t).1 = PublicDiscreteDraws.dataSlot →
      prepared.arm = PublicDiscreteDraws.pilotDraw (K_pos p)
        (PublicDiscreteDraws.followerPlayer p.two_le_m i) (row.2 t).1) ∧
    (PublicDiscreteDraws.slotDraw (row.2 t).1 ≠ PublicDiscreteDraws.dataSlot →
      ¬ ActiveFollowerQueueOperation.selectedUpRound i row activation t →
      prepared.arm = (OrderedTupleSampler.sample p.two_le_m p.m_lt_K (row.2 t).1).val
        (PublicDiscreteDraws.followerPlayer p.two_le_m i)) := by
  let offered : OrdinaryMessageCodec.UpRecord (ReferencePrelaunchFollower.codecParams p rate.eta) :=
    ⟨ActiveFollowerQueueOperation.upOfferFields old, hadmissible⟩
  have hnotSelected : ¬ ActiveFollowerQueueOperation.selectedUpRound i row activation t →
      ActiveFollowerQueueOperation.checkedUpOffer rate.eta i row activation t old = .noOffer := by
    intro hnot
    apply ActiveFollowerQueueOperation.checkedUpOffer_noOffer rate.eta i row activation t old
      hstateInput
    intro hselected
    exact hnot hselected.1
  have hselectedOffer : ∀ hselected : ActiveFollowerQueueOperation.selectedUpRound i row activation t,
      ActiveFollowerQueueOperation.checkedUpOffer rate.eta i row activation t old = .offer offered := by
    intro hselected
    unfold ActiveFollowerQueueOperation.checkedUpOffer
    rw [dif_pos hstateInput, dif_pos ⟨hselected, hstatus⟩, dif_pos hadmissible]
  have hconfig : prepared.configuration = .ordinary old memory := by
    by_cases hdata : PublicDiscreteDraws.slotDraw (row.2 t).1 = PublicDiscreteDraws.dataSlot
    · have hnot : ¬ ActiveFollowerQueueOperation.selectedUpRound i row activation t := by
        intro hselected
        exact (by decide : PublicDiscreteDraws.dataSlot ≠ PublicDiscreteDraws.upSlot)
          (hdata.symm.trans hselected.2.1)
      have hoff := hnotSelected hnot
      have hchoiceCore := ActiveFollowerArmChoice.followerArmChoiceCore_unoccupied_data old
        (row.2 t) i none hstatus hdata
      have hchoice : ActiveFollowerArmChoice.followerArmChoice old row t i none =
          some (PublicDiscreteDraws.pilotDraw (K_pos p)
            (PublicDiscreteDraws.followerPlayer p.two_le_m i) (row.2 t).1) := by
        rw [ActiveFollowerArmChoice.followerArmChoice_eq_core]
        exact hchoiceCore
      have hpreparedArm := (DeclaredFollowerLocalRound.prepare_no_offer_arm_equation
          rate i row activation t active old old memory memory hstart hoff).2 _ hchoice
      have heq := congrArg DeclaredFollowerLocalRound.PreparedRound.configuration hprepared
      exact heq.trans hpreparedArm.2
    · by_cases hup : PublicDiscreteDraws.slotDraw (row.2 t).1 = PublicDiscreteDraws.upSlot ∧
          PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K (row.2 t).1 = i
      · have hselected : ActiveFollowerQueueOperation.selectedUpRound i row activation t :=
          ⟨active, hup.1, hup.2⟩
        have hoff := hselectedOffer hselected
        have hvalid : ActiveFollowerArmChoice.upStateDomain old ∧
            ActiveFollowerArmChoice.offeredUpMatchesState old offered := by
          constructor
          · exact ⟨hstateInput.1, hstateInput.2.1, hstateInput.2.2.1⟩
          · simp [ActiveFollowerArmChoice.offeredUpMatchesState, offered,
              ActiveFollowerQueueOperation.upOfferFields]
        have hchoiceCore := ActiveFollowerArmChoice.followerArmChoiceCore_unoccupied_selected_up
          old (row.2 t) i offered hstatus hup.1 hup.2 hvalid
        have hchoice : ActiveFollowerArmChoice.followerArmChoice old row t i (some offered) =
            some (ActiveRoundActions.sendArm
              (ActiveFollowerArmChoice.offeredUpBit rate.eta (row.2 t) i offered)
              ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K (row.2 t).1).val
                (PublicDiscreteDraws.followerPlayer p.two_le_m i))
              ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K (row.2 t).1).val
                (ActiveRoundActions.coordinator p.two_le_m))) := by
          rw [ActiveFollowerArmChoice.followerArmChoice_eq_core]
          exact hchoiceCore
        have hpreparedArm := (DeclaredFollowerLocalRound.prepare_offer_arm_equation
            rate i row activation t active old old memory memory hstart offered hoff).2 _ hchoice
        have heq := congrArg DeclaredFollowerLocalRound.PreparedRound.configuration hprepared
        exact heq.trans hpreparedArm.2
      · have hnot : ¬ ActiveFollowerQueueOperation.selectedUpRound i row activation t := by
          intro hselected
          exact hup ⟨hselected.2.1, hselected.2.2⟩
        have hoff := hnotSelected hnot
        have hchoiceCore := ActiveFollowerArmChoice.followerArmChoiceCore_unoccupied_other old
          (row.2 t) i none hstatus (by simpa [hdata]) hup
        have hchoice : ActiveFollowerArmChoice.followerArmChoice old row t i none =
            some ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K (row.2 t).1).val
              (PublicDiscreteDraws.followerPlayer p.two_le_m i)) := by
          rw [ActiveFollowerArmChoice.followerArmChoice_eq_core]
          exact hchoiceCore
        have hpreparedArm := (DeclaredFollowerLocalRound.prepare_no_offer_arm_equation
            rate i row activation t active old old memory memory hstart hoff).2 _ hchoice
        have heq := congrArg DeclaredFollowerLocalRound.PreparedRound.configuration hprepared
        exact heq.trans hpreparedArm.2
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact hconfig
  · intro hselected
    let offered' : OrdinaryMessageCodec.UpRecord
        (ReferencePrelaunchFollower.codecParams p rate.eta) := offered
    have hoff := hselectedOffer hselected
    have hvalid : ActiveFollowerArmChoice.upStateDomain old ∧
        ActiveFollowerArmChoice.offeredUpMatchesState old offered' := by
      constructor
      · exact ⟨hstateInput.1, hstateInput.2.1, hstateInput.2.2.1⟩
      · simp [ActiveFollowerArmChoice.offeredUpMatchesState, offered', offered,
          ActiveFollowerQueueOperation.upOfferFields]
    have hchoiceCore := ActiveFollowerArmChoice.followerArmChoiceCore_unoccupied_selected_up
      old (row.2 t) i offered' hstatus hselected.2.1 hselected.2.2 hvalid
    have hchoice := ActiveFollowerArmChoice.followerArmChoice_eq_core old row t i (some offered')
      |>.trans hchoiceCore
    have hpreparedArm := (DeclaredFollowerLocalRound.prepare_offer_arm_equation
        rate i row activation t active old old memory memory hstart offered' hoff).2 _ hchoice
    refine ⟨offered', hoff, rfl, ?_, ?_⟩
    · rw [hprepared]
      rw [hpreparedArm.1]
      exact hchoice
    · rw [hprepared]
      exact hpreparedArm.1
  · intro hnot
    have hoff := hnotSelected hnot
    have hchoice : ActiveFollowerArmChoice.followerArmChoice old row t i none =
        some prepared.arm := by
      by_cases hdata : PublicDiscreteDraws.slotDraw (row.2 t).1 = PublicDiscreteDraws.dataSlot
      · have hcore := ActiveFollowerArmChoice.followerArmChoiceCore_unoccupied_data old
          (row.2 t) i none hstatus hdata
        have hpreparedArm := (DeclaredFollowerLocalRound.prepare_no_offer_arm_equation
            rate i row activation t active old old memory memory hstart hoff).2 _ hcore
        rw [hprepared]
        rw [hpreparedArm.1]
        rw [ActiveFollowerArmChoice.followerArmChoice_eq_core]
        exact hcore
      · have hup : ¬ (PublicDiscreteDraws.slotDraw (row.2 t).1 = PublicDiscreteDraws.upSlot ∧
            PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K (row.2 t).1 = i) := by
          intro h
          exact hnot ⟨active, h.1, h.2⟩
        have hcore := ActiveFollowerArmChoice.followerArmChoiceCore_unoccupied_other old
          (row.2 t) i none hstatus hdata hup
        have hpreparedArm := (DeclaredFollowerLocalRound.prepare_no_offer_arm_equation
            rate i row activation t active old old memory memory hstart hoff).2 _ hcore
        rw [hprepared]
        rw [hpreparedArm.1]
        rw [ActiveFollowerArmChoice.followerArmChoice_eq_core]
        exact hcore
    exact ⟨hoff, hchoice⟩
  · intro hdata
    have hnot : ¬ ActiveFollowerQueueOperation.selectedUpRound i row activation t := by
      intro hselected
      exact (by decide : PublicDiscreteDraws.dataSlot ≠ PublicDiscreteDraws.upSlot)
        (hdata.symm.trans hselected.2.1)
    have hoff := hnotSelected hnot
    have hcore := ActiveFollowerArmChoice.followerArmChoiceCore_unoccupied_data old
      (row.2 t) i none hstatus hdata
    have hchoice := ActiveFollowerArmChoice.followerArmChoice_eq_core old row t i none
      |>.trans hcore
    have hpreparedArm := (DeclaredFollowerLocalRound.prepare_no_offer_arm_equation
        rate i row activation t active old old memory memory hstart hoff).2 _ hchoice
    rw [hprepared]
    exact hpreparedArm.1

  · intro hnotdata hnotselected
    have hup : ¬ (PublicDiscreteDraws.slotDraw (row.2 t).1 = PublicDiscreteDraws.upSlot ∧
        PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K (row.2 t).1 = i) := by
      intro h
      exact hnotselected ⟨active, h.1, h.2⟩
    have hcore := ActiveFollowerArmChoice.followerArmChoiceCore_unoccupied_other old
      (row.2 t) i none hstatus hnotdata hup
    have hchoice := ActiveFollowerArmChoice.followerArmChoice_eq_core old row t i none
      |>.trans hcore
    have hoff := hnotSelected hnotselected
    have hpreparedArm := (DeclaredFollowerLocalRound.prepare_no_offer_arm_equation
        rate i row activation t active old old memory memory hstart hoff).2 _ hchoice
    rw [hprepared]
    exact hpreparedArm.1

/-- The actual complete source suffix supplies both the continuing collection
timing barrier and the local PREPARE cases for each incoming follower.  An
ordinary input has its full local and decoder domains, while dagger and all
noncontinuing coordinator branches remain explicit. -/
theorem complete_continuing_collection_follower_preparation_cases
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (i : Fin (p.m - 1)) :
    let records := ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h
    let r := records.get k
    let x := r.input
    let prep := r.output.preparation
    let t := x.time
    let f := prep.followers.followers i
    let out := r.output.next.followers i
    let tuple := OrderedTupleSampler.sample p.two_le_m p.m_lt_K (x.row.2 t).1
    match prep.coordinator with
    | .collection payload ledger clock cutoff (.continuing core snapshot boundary scores) =>
        match x.state.followers i with
        | .dagger => f.configuration = .dagger ∧ out = .dagger
        | .ordinary old memory =>
            old.status = .unoccupied ∧
            ActiveFollowerLifecycle.localStateDomainValid old ∧
            ReferenceFollowerDecoderChronology.downBatchEndpoint old t.val ∧
            ActiveFollowerLifecycle.startRound rate.eta t old memory = .ok (old, memory) ∧
            f.configuration = .ordinary old memory ∧
            ActiveFollowerQueueOperation.stateInputDomain old ∧
            OrdinaryMessageCodec.upAdmissible
              (ReferencePrelaunchFollower.codecParams p rate.eta)
              (ActiveFollowerQueueOperation.upOfferFields old) ∧
            (ActiveFollowerQueueOperation.selectedUpRound i x.row
                (x.state.activations i) t →
              ∃ offered : OrdinaryMessageCodec.UpRecord
                  (ReferencePrelaunchFollower.codecParams p rate.eta),
                ActiveFollowerQueueOperation.checkedUpOffer rate.eta i x.row
                  (x.state.activations i) t old = .offer offered ∧
                offered.val = ActiveFollowerQueueOperation.upOfferFields old ∧
                ActiveFollowerArmChoice.followerArmChoice old x.row t i (some offered) =
                  some f.arm ∧
                f.arm = ActiveRoundActions.sendArm
                  (ActiveFollowerArmChoice.offeredUpBit rate.eta (x.row.2 t) i offered)
                  (tuple.val (PublicDiscreteDraws.followerPlayer p.two_le_m i))
                  (tuple.val (ActiveRoundActions.coordinator p.two_le_m))) ∧
            (¬ ActiveFollowerQueueOperation.selectedUpRound i x.row
                (x.state.activations i) t →
              ActiveFollowerQueueOperation.checkedUpOffer rate.eta i x.row
                (x.state.activations i) t old = .noOffer ∧
              ActiveFollowerArmChoice.followerArmChoice old x.row t i none = some f.arm) ∧
            (PublicDiscreteDraws.slotDraw (x.row.2 t).1 = PublicDiscreteDraws.dataSlot →
              f.arm = PublicDiscreteDraws.pilotDraw (K_pos p)
                (PublicDiscreteDraws.followerPlayer p.two_le_m i) (x.row.2 t).1) ∧
            (PublicDiscreteDraws.slotDraw (x.row.2 t).1 ≠ PublicDiscreteDraws.dataSlot →
              ¬ ActiveFollowerQueueOperation.selectedUpRound i x.row
                (x.state.activations i) t →
              f.arm = tuple.val (PublicDiscreteDraws.followerPlayer p.two_le_m i)) ∧
            (match out with
            | .dagger => True
            | .ordinary next nextMemory =>
                next.status = .unoccupied ∧
                ActiveFollowerLifecycle.localStateDomainValid next ∧
                ReferenceFollowerDecoderChronology.downBatchEndpoint next (t.val + 1) ∧
                nextMemory = memory)
    | _ => True := by
  classical
  let records := ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate source rewards C_star C_h
  let record := records.get k
  change match record.output.preparation.coordinator with
    | .collection payload ledger clock cutoff (.continuing core snapshot boundary scores) =>
        match record.input.state.followers i with
        | .dagger =>
            (record.output.preparation.followers.followers i).configuration = .dagger ∧
            record.output.next.followers i = .dagger
        | .ordinary old memory =>
            old.status = .unoccupied ∧
            ActiveFollowerLifecycle.localStateDomainValid old ∧
            ReferenceFollowerDecoderChronology.downBatchEndpoint old record.input.time.val ∧
            ActiveFollowerLifecycle.startRound rate.eta record.input.time old memory =
              .ok (old, memory) ∧
            (record.output.preparation.followers.followers i).configuration =
              .ordinary old memory ∧
            ActiveFollowerQueueOperation.stateInputDomain old ∧
            OrdinaryMessageCodec.upAdmissible
              (ReferencePrelaunchFollower.codecParams p rate.eta)
              (ActiveFollowerQueueOperation.upOfferFields old) ∧
            (ActiveFollowerQueueOperation.selectedUpRound i record.input.row
                (record.input.state.activations i) record.input.time →
              ∃ offered : OrdinaryMessageCodec.UpRecord
                  (ReferencePrelaunchFollower.codecParams p rate.eta),
                ActiveFollowerQueueOperation.checkedUpOffer rate.eta i record.input.row
                  (record.input.state.activations i) record.input.time old = .offer offered ∧
                offered.val = ActiveFollowerQueueOperation.upOfferFields old ∧
                ActiveFollowerArmChoice.followerArmChoice old record.input.row
                  record.input.time i (some offered) =
                  some (record.output.preparation.followers.followers i).arm ∧
                (record.output.preparation.followers.followers i).arm =
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
                (record.input.state.activations i) record.input.time old = .noOffer ∧
              ActiveFollowerArmChoice.followerArmChoice old record.input.row
                record.input.time i none =
                some (record.output.preparation.followers.followers i).arm) ∧
            (PublicDiscreteDraws.slotDraw (record.input.row.2 record.input.time).1 =
                PublicDiscreteDraws.dataSlot →
              (record.output.preparation.followers.followers i).arm =
                PublicDiscreteDraws.pilotDraw (K_pos p)
                  (PublicDiscreteDraws.followerPlayer p.two_le_m i)
                  (record.input.row.2 record.input.time).1) ∧
            (PublicDiscreteDraws.slotDraw (record.input.row.2 record.input.time).1 ≠
                PublicDiscreteDraws.dataSlot →
              ¬ ActiveFollowerQueueOperation.selectedUpRound i record.input.row
                (record.input.state.activations i) record.input.time →
              (record.output.preparation.followers.followers i).arm =
                (OrderedTupleSampler.sample p.two_le_m p.m_lt_K
                  (record.input.row.2 record.input.time).1).val
                  (PublicDiscreteDraws.followerPlayer p.two_le_m i)) ∧
            (match record.output.next.followers i with
            | .dagger => True
            | .ordinary next nextMemory =>
                next.status = .unoccupied ∧
                ActiveFollowerLifecycle.localStateDomainValid next ∧
                ReferenceFollowerDecoderChronology.downBatchEndpoint next
                  (record.input.time.val + 1) ∧
                nextMemory = memory)
    | _ => True
  cases hcoord : record.output.preparation.coordinator with
  | first outcome => trivial
  | live registers owned base outcome =>
      cases outcome <;> trivial
  | invalidCollectionCutoff => trivial
  | dagger => trivial
  | collection payload ledger clock cutoff outcome =>
      cases outcome with
      | clockFailure failure hfailure => trivial
      | localFailure started hstart hinvalid reason => trivial
      | coreFailure core started hstart reason => trivial
      | continuing core snapshot boundary scores =>
          change match record.input.state.followers i with
          | .dagger =>
              (record.output.preparation.followers.followers i).configuration = .dagger ∧
              record.output.next.followers i = .dagger
          | .ordinary old memory =>
              old.status = .unoccupied ∧
              ActiveFollowerLifecycle.localStateDomainValid old ∧
              ReferenceFollowerDecoderChronology.downBatchEndpoint old
                record.input.time.val ∧
              ActiveFollowerLifecycle.startRound rate.eta record.input.time old memory =
                .ok (old, memory) ∧
              (record.output.preparation.followers.followers i).configuration =
                .ordinary old memory ∧
              ActiveFollowerQueueOperation.stateInputDomain old ∧
              OrdinaryMessageCodec.upAdmissible
                (ReferencePrelaunchFollower.codecParams p rate.eta)
                (ActiveFollowerQueueOperation.upOfferFields old) ∧
              (ActiveFollowerQueueOperation.selectedUpRound i record.input.row
                  (record.input.state.activations i) record.input.time →
                ∃ offered : OrdinaryMessageCodec.UpRecord
                    (ReferencePrelaunchFollower.codecParams p rate.eta),
                  ActiveFollowerQueueOperation.checkedUpOffer rate.eta i record.input.row
                    (record.input.state.activations i) record.input.time old = .offer offered ∧
                  offered.val = ActiveFollowerQueueOperation.upOfferFields old ∧
                  ActiveFollowerArmChoice.followerArmChoice old record.input.row
                    record.input.time i (some offered) =
                    some (record.output.preparation.followers.followers i).arm ∧
                  (record.output.preparation.followers.followers i).arm =
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
                  (record.input.state.activations i) record.input.time old = .noOffer ∧
                ActiveFollowerArmChoice.followerArmChoice old record.input.row
                  record.input.time i none =
                  some (record.output.preparation.followers.followers i).arm) ∧
              (PublicDiscreteDraws.slotDraw (record.input.row.2 record.input.time).1 =
                  PublicDiscreteDraws.dataSlot →
                (record.output.preparation.followers.followers i).arm =
                  PublicDiscreteDraws.pilotDraw (K_pos p)
                    (PublicDiscreteDraws.followerPlayer p.two_le_m i)
                    (record.input.row.2 record.input.time).1) ∧
              (PublicDiscreteDraws.slotDraw (record.input.row.2 record.input.time).1 ≠
                  PublicDiscreteDraws.dataSlot →
                ¬ ActiveFollowerQueueOperation.selectedUpRound i record.input.row
                  (record.input.state.activations i) record.input.time →
                (record.output.preparation.followers.followers i).arm =
                  (OrderedTupleSampler.sample p.two_le_m p.m_lt_K
                    (record.input.row.2 record.input.time).1).val
                    (PublicDiscreteDraws.followerPlayer p.two_le_m i)) ∧
              (match record.output.next.followers i with
              | .dagger => True
              | .ordinary next nextMemory =>
                  next.status = .unoccupied ∧
                  ActiveFollowerLifecycle.localStateDomainValid next ∧
                  ReferenceFollowerDecoderChronology.downBatchEndpoint next
                    (record.input.time.val + 1) ∧
                  nextMemory = memory)
          cases hinput : record.input.state.followers i with
          | dagger =>
              constructor
              · rw [record.output_eq]
                change ((ReferenceActivePhysicalStep.prepare record.input).followers.followers i).configuration = _
                rw [(ReferenceActivePhysicalStep.prepare record.input).followers.followers_eq i,
                  ReferenceActiveFeedbackCut.prepareFollowers_apply]
                change (DeclaredFollowerLocalRound.prepare rate i record.input.row
                  (record.input.state.activations i) record.input.time
                  (record.input.active i) (record.input.state.followers i)).configuration =
                    LocalConfiguration.dagger
                rw [hinput]
                exact (DeclaredFollowerLocalRound.prepare_dagger rate i record.input.row
                  (record.input.state.activations i) record.input.time
                  (record.input.active i)).2
              · rw [record.output_eq]
                exact ReferenceActivePhysicalStep.step_follower_dagger record.input i hinput
          | ordinary old memory =>
              -- The actual run and launch seed are recovered from the source;
              -- no arbitrary state or history is used at this root.
              let start := ReferenceCompletePhysicalHistory.physicalStart
                rate source rewards C_star C_h
              let count := p.T - start
              rcases ReferenceLaterCollectionArrivalReadout.source_launch_split
                  rate rewards C_star C_h source with hnone | ⟨initial, hlaunch, hrecords, hseedData⟩
              · have hlength := congrArg List.length hnone.2.1
                exact False.elim (Nat.not_lt_zero k.val (k.isLt.trans_eq hlength))
              · rcases hseedData with ⟨hc, hactive, seed, hfirst, hunoccupied, hbuffer⟩
                subst initial
                have hspan : start + count ≤ p.T := by
                  have hs := ReferenceCompletePhysicalHistory.physicalStart_le_T
                    rate source rewards C_star C_h
                  dsimp [start, count]
                  omega
                have hmode := ReferenceCompletePhysicalHistory.activeMode_of_launch_eq_some
                  rate source rewards C_star C_h
                  (ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hc)
                  hlaunch
                let initial := ReferenceFirstLaunchNumericalCell.launchState
                  rate source rewards C_star C_h hc
                let run := ReferenceActivePhysicalHorizon.run initial source.1.2
                  (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
                  start count hspan hmode
                have hrunRecords : run.records = records := by
                  simpa [run, initial, start, count] using hrecords.symm
                have hkRecords : k.val < records.length := by
                  simpa [records] using k.isLt
                have hkRun : k.val < run.records.length := by
                  rw [hrunRecords]
                  exact hkRecords
                have hkCount : k.val < count := by
                  have hlen := ReferenceActivePhysicalHorizon.run_record_count initial
                    source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
                    rewards start count hspan hmode
                  rw [hlen] at hkRun
                  exact hkRun
                have hspanK : start + (k.val + 1) ≤ p.T := by omega
                have hspanPrefix : start + k.val ≤ p.T := by omega
                have hrecordGet := run_records_getElem?_actualRunRecordAt initial
                  source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
                  rewards start count hspan hmode k.val hkCount
                let current := ReferenceAssignmentPayloadChronology.actualRunRecordAt
                  initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
                  rewards start k.val hspanK hmode
                have hrecordEq : record = current := by
                  have hrecordAt? : records[k.val]? = some current := by
                    exact (congrArg (fun rs => rs[k.val]?) hrunRecords.symm).trans hrecordGet
                  have hget := List.getElem?_eq_some_iff.mp hrecordAt?
                  change records[k.val]'k.isLt = current
                  exact hget.2
                have hrecordMem : record ∈ run.records := by
                  rw [hrunRecords]
                  exact List.get_mem records k
                have hprepEq : record.output.preparation =
                    ReferenceActivePhysicalStep.prepare record.input := by
                  rw [record.output_eq]
                  rfl
                have hselection := actualCollection_prepare_selection_payload record payload
                  ledger clock cutoff core snapshot boundary scores hcoord
                rcases hselection with ⟨selected, hselected, hselectedPayload⟩
                have hseedFirst : initial.coordinator = .first := by
                  exact hfirst
                have hseedOrdinary : ∀ j st μ,
                    initial.followers j = .ordinary st μ → st.status = .unoccupied := by
                  intro j st μ hj
                  have hstate := (LocalConfiguration.ordinary.inj
                    (hj.symm.trans (seed.configuration j))).1
                  subst st
                  exact seed.unoccupied j
                have hfields := ReferenceOccupiedFieldHistory.run_prefix_occupied_field_history
                  initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
                  rewards start count hspan seed.activeAtStart hseedFirst hseedOrdinary
                  count le_rfl
                have hactualFields := hfields.2 record hrecordMem selected hselected
                have hinputOccupied := hactualFields.1 i
                have houtputOccupied := hactualFields.2.2 i
                have hcutoffUpper :=
                  Bandits.Support.ReferenceCollectionCutoffSourceHistory.complete_continuing_collection_cutoff_source_bound
                  rate source rewards C_star C_h k
                dsimp only at hcutoffUpper
                rw [hcoord] at hcutoffUpper
                change FollowerCutoffScan.firstCutoff p rate.eta.val payload.sigma
                    (FollowerCutoffScan.completeRowProposalBit p rate.eta.val record.input.row) ≤
                      ledger.cutoff ∧ ledger.cutoff ≤ record.input.time.val at hcutoffUpper
                have hoccupiedBounds :=
                  Bandits.Support.ReferenceOccupiedFollowerCutoffHistory.complete_occupied_follower_cutoff_source_bounds
                  rate source rewards C_star C_h k i
                dsimp only at hoccupiedBounds
                change (match record.input.state.followers i with
                    | .dagger => True
                    | .ordinary state _ => state.status ≠ .unoccupied →
                        ∃ M, state.lastDown = some M ∧
                          record.input.time.val + 1 ≤ FollowerCutoffScan.firstCutoff p
                            rate.eta.val
                            (ActiveFollowerDownAcceptance.downStart p rate M)
                            (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
                              record.input.row)) ∧
                  (match record.output.next.followers i with
                    | .dagger => True
                    | .ordinary state _ => state.status ≠ .unoccupied →
                        ∃ M, state.lastDown = some M ∧
                          record.input.time.val + 2 ≤ FollowerCutoffScan.firstCutoff p
                            rate.eta.val
                            (ActiveFollowerDownAcceptance.downStart p rate M)
                            (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
                              record.input.row)) at hoccupiedBounds
                have hrowTime : record.input.time.val = start + k.val := by
                  have htime := congrArg (fun rec => rec.input.time.val) hrecordEq
                  simp [current, ReferenceAssignmentPayloadChronology.actualRunRecordAt,
                    ReferenceActivePhysicalHorizon.roundInputAt] at htime
                  exact htime
                have hstatusOld : old.status = .unoccupied := by
                  by_contra hnot
                  have hinputBound : old.status ≠ .unoccupied →
                      ∃ M, old.lastDown = some M ∧
                        record.input.time.val + 1 ≤ FollowerCutoffScan.firstCutoff p
                          rate.eta.val (ActiveFollowerDownAcceptance.downStart p rate M)
                          (FollowerCutoffScan.completeRowProposalBit p rate.eta.val record.input.row) := by
                    simpa [hinput] using hoccupiedBounds.1
                  have hbound := hinputBound hnot
                  rcases hbound with ⟨M, hM, htimeBound⟩
                  rw [hinput] at hinputOccupied
                  change old.status ≠ .unoccupied → old.lastDown =
                    some (selected.view.payload.downRecord i) at hinputOccupied
                  have hfield := hinputOccupied hnot
                  rw [hselectedPayload] at hfield
                  have hMrecord : M = payload.downRecord i :=
                    Option.some.inj (hM.symm.trans hfield)
                  have hdownStart : ActiveFollowerDownAcceptance.downStart p rate M =
                      payload.sigma := by
                    apply Fin.ext
                    have hsigmaPayload := congrArg OrdinaryMessageCodec.DownFields.sigma
                      (payload.downRecord_fields i)
                    have hsigmaM : M.val.sigma = payload.sigma.val + 1 := by
                      rw [hMrecord]
                      exact hsigmaPayload
                    have hstart := ActiveFollowerDownAcceptance.downStart_val_add_one p rate M
                    change (ActiveFollowerDownAcceptance.downStart p rate M).val =
                      payload.sigma.val at ⊢
                    omega
                  rw [hdownStart] at htimeBound
                  omega
                have hinputRun : (ReferenceActivePhysicalHorizon.run initial
                    source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
                    rewards start k.val hspanPrefix hmode).finalState.followers i =
                      .ordinary old memory := by
                  have hcurrentInput := (congrArg
                    (fun rec => rec.input.state.followers i) hrecordEq).symm.trans hinput
                  simpa [current, ReferenceAssignmentPayloadChronology.actualRunRecordAt,
                    ReferenceActivePhysicalHorizon.roundInputAt] using hcurrentInput
                have hpreviousPos : 0 < k.val := by
                  by_contra hzero
                  have hkzero : k.val = 0 := by omega
                  have hcurrState : current.input.state = initial := by
                    change (ReferenceActivePhysicalHorizon.run initial source.1.2
                      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
                      start k.val hspanPrefix hmode).finalState = initial
                    simpa only [hkzero] using
                      ReferenceActivePhysicalHorizon.run_zero_final initial source.1.2
                        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
                        start (by omega) hmode
                  have hrecordState : record.input.state = initial := by
                    exact (congrArg (fun rec => rec.input.state) hrecordEq).trans hcurrState
                  have hrecordCoord : record.input.state.coordinator = .first := by
                    rw [hrecordState]
                    exact hfirst
                  have hrecordPrepared :
                      (ReferenceActivePhysicalStep.prepare record.input).coordinator =
                        .collection payload ledger clock cutoff
                          (.continuing core snapshot boundary scores) := by
                    exact (congrArg
                      (fun prep : ReferenceActivePhysicalStep.PreparedRound record.input =>
                        prep.coordinator) hprepEq).symm.trans hcoord
                  have hdispatch := ReferenceActivePhysicalStep.dispatch_first record.input
                    hrecordCoord
                  simp only [(ReferenceActivePhysicalStep.prepare record.input).coordinator_eq,
                    hdispatch] at hrecordPrepared
                  have himpossible := hrecordPrepared
                  cases himpossible
                have hpreviousSpan : start + (k.val - 1 + 1) ≤ p.T := by omega
                let previous := ReferenceAssignmentPayloadChronology.actualRunRecordAt
                  initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
                  rewards start (k.val - 1) hpreviousSpan hmode
                have hpreviousFinal : previous.output.next =
                    (ReferenceActivePhysicalHorizon.run initial source.1.2
                      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start
                      k.val hspanPrefix hmode).finalState := by
                  have hsuccessor := Bandits.Support.ReferenceAssignmentPayloadChronology.run_successor_finalState_eq_actualRunRecordAt
                    initial source.1.2
                    (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start
                    (k.val - 1) (by omega) hmode
                  simpa only [Nat.sub_add_cancel (by omega : 1 ≤ k.val)] using hsuccessor.symm
                have hpreviousOrdinary : previous.output.next.followers i = .ordinary old memory := by
                  rw [hpreviousFinal]
                  exact hinputRun
                have hpreviousPrepEq : previous.output.preparation =
                    ReferenceActivePhysicalStep.prepare previous.input := by
                  rw [previous.output_eq]
                  rfl
                have hpreviousPrepared :
                    previous.output.preparation.followers.followers i =
                      DeclaredFollowerLocalRound.prepare rate i previous.input.row
                        (previous.input.state.activations i) previous.input.time
                        (previous.input.active i) (previous.input.state.followers i) := by
                  rw [hpreviousPrepEq]
                  change (ReferenceActiveFeedbackCut.prepare
                    (ReferenceActivePhysicalStep.followerInput previous.input)).followers i = _
                  rfl
                rcases ReferenceFollowerReplyChronology.finishFollower_ordinary_inversion
                    previous.output.preparation.coordinator.downView
                    (previous.output.preparation.followers.followers i)
                    (previous.output.ownEntries
                      (PublicDiscreteDraws.followerPlayer p.two_le_m i)).2 old memory
                    hpreviousOrdinary with
                  ⟨choice, choiceMemory, post, hchoice, hlogged, hrelease, _, _⟩
                have hlocalOld := releaseAndFinish_ordinary_success_domain
                  (previous.output.preparation.followers.followers i).follower
                  (previous.output.preparation.followers.followers i).row
                  (previous.output.preparation.followers.followers i).time
                  (previous.output.ownEntries
                    (PublicDiscreteDraws.followerPlayer p.two_le_m i)).2
                  choice choiceMemory post old memory hrelease
                have hstartRound : ActiveFollowerLifecycle.startRound rate.eta
                    record.input.time old memory = .ok (old, memory) :=
                  ActiveFollowerLifecycle.startRound_unoccupied rate.eta record.input.time old
                    memory hlocalOld.1 hstatusOld
                have hstateInput : ActiveFollowerQueueOperation.stateInputDomain old := by
                  have hregisters := hlocalOld.1.1
                  change old.S ≤ p.T * D p ∧ old.delta ≤ D p ∧ old.backlog ≤ p.T * D p
                    at hregisters
                  have hbuffer := hlocalOld.1.2.1
                  have hbufferTimestamps := ActiveFollowerLifecycle.localBufferValid_timestamp hbuffer
                  have hbufferNodup := ActiveFollowerLifecycle.localBufferValid_keys_nodup hbuffer
                  unfold ActiveFollowerQueueOperation.stateInputDomain
                  exact ⟨hregisters.1, hregisters.2.1, hregisters.2.2,
                    hbufferTimestamps, hbufferNodup⟩
                have hreplyChronology := ReferenceFollowerReplyChronology.run_input_final_chronology
                  initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
                  rewards start k.val hspanPrefix hmode i (seed.followers i) old
                  (seed.memory i) memory (seed.configuration i) hinputRun
                have hupAdmissible : OrdinaryMessageCodec.upAdmissible
                    (ReferencePrelaunchFollower.codecParams p rate.eta)
                    (ActiveFollowerQueueOperation.upOfferFields old) := by
                  cases hlast : old.lastDown with
                  | none =>
                      have hacceptedOld : ReferencePrelaunchFollower.acceptedStart old = 0 := by
                        simp [ReferencePrelaunchFollower.acceptedStart, hlast]
                      have hreply := hreplyChronology.2.1 (seed.unoccupied i)
                        ((seed.acceptedStart_zero i).trans hacceptedOld.symm)
                      simp only [ReferenceFollowerReplyChronology.reply,
                        Prod.mk.injEq] at hreply
                      rcases hreply with ⟨_, hfields⟩
                      rcases hfields with ⟨_, hfields⟩
                      rcases hfields with ⟨hS, hfields⟩
                      rcases hfields with ⟨hdelta, hbacklog⟩
                      have hSzero : old.S = 0 := hS.trans (seed.S_zero i)
                      have hdeltaZero : old.delta = 0 := hdelta.trans (seed.delta_zero i)
                      have hbacklogZero : old.backlog = 0 := hbacklog.trans
                        (seed.backlog_zero i)
                      simp [ActiveFollowerQueueOperation.upOfferFields,
                        ReferencePrelaunchFollower.acceptedStart, hlast, hSzero,
                        hdeltaZero, hbacklogZero, OrdinaryMessageCodec.upAdmissible,
                        OrdinaryMessageCodec.upPlaceholder]
                  | some M =>
                      have hM := M.property
                      unfold OrdinaryMessageCodec.upAdmissible
                        ActiveFollowerQueueOperation.upOfferFields
                      simp only [ReferencePrelaunchFollower.acceptedStart, hlast]
                      have hregisters := hlocalOld.1.1
                      change old.S ≤ p.T * D p ∧ old.delta ≤ D p ∧ old.backlog ≤ p.T * D p
                        at hregisters
                      exact Or.inr ⟨hM.1, hM.2.1, hregisters.1,
                        hregisters.2.1, hregisters.2.2⟩
                have hprepared : record.output.preparation.followers.followers i =
                    DeclaredFollowerLocalRound.prepare rate i record.input.row
                      (record.input.state.activations i) record.input.time
                      (record.input.active i) (record.input.state.followers i) := by
                  rw [hprepEq]
                  change (ReferenceActiveFeedbackCut.prepare
                    (ReferenceActivePhysicalStep.followerInput record.input)).followers i = _
                  rfl
                have hpreparedOld : record.output.preparation.followers.followers i =
                    DeclaredFollowerLocalRound.prepare rate i record.input.row
                      (record.input.state.activations i) record.input.time
                      (record.input.active i) (.ordinary old memory) := by
                  simpa [hinput] using hprepared
                have hlocalPrepare := actual_prepare_unoccupied_follower_cases
                  i record.input.row (record.input.state.activations i) record.input.time
                  (record.input.active i) old memory hstatusOld hstartRound hstateInput
                  hupAdmissible (record.output.preparation.followers.followers i) hpreparedOld
                have hdownSeed :=
                  Bandits.Support.ReferenceCorrectedInitializationLaunch.correctedLaunch_downBatchSeed
                    rate source rewards C_star C_h hc
                rcases hdownSeed with ⟨downInitial, hdownLaunch, hdownSeed⟩
                have hdownInitial : downInitial = initial :=
                  Option.some.inj (hdownLaunch.symm.trans hlaunch)
                subst downInitial
                have hdownSeed' : ReferenceFollowerDecoderChronology.downBatchSeed initial start := by
                  change ReferenceFollowerDecoderChronology.downBatchSeed initial
                    (ReferenceInitializationRun.elapsed p
                      (ReferenceInitializationRun.output
                        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed)
                  exact hdownSeed
                have hdownOld := ReferenceFollowerDecoderChronology.run_downBatch_spec
                  initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
                  rewards start k.val hspanPrefix hmode hdownSeed' i old memory hinputRun
                have hdownOld' : ReferenceFollowerDecoderChronology.downBatchEndpoint old
                    record.input.time.val := by
                  rw [hrowTime]
                  exact hdownOld.1
                -- Keep the actual arm equations and all output constructors.
                cases hout : record.output.next.followers i with
                | dagger =>
                    rcases hlocalPrepare with ⟨hconfig, hselected, hnoOffer,
                      hdataArm, hotherArm⟩
                    refine ⟨hstatusOld, hlocalOld.1, hdownOld', hstartRound,
                      hconfig, hstateInput, hupAdmissible, hselected, hnoOffer,
                      hdataArm, hotherArm, trivial⟩
                | ordinary next nextMemory =>
                    have hnextStatus : next.status = .unoccupied := by
                      by_contra hnot
                      have houtputBound : next.status ≠ .unoccupied →
                          ∃ M, next.lastDown = some M ∧
                            record.input.time.val + 2 ≤ FollowerCutoffScan.firstCutoff p
                              rate.eta.val (ActiveFollowerDownAcceptance.downStart p rate M)
                              (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
                                record.input.row) := by
                        simpa [hout] using hoccupiedBounds.2
                      have hbound := houtputBound hnot
                      rcases hbound with ⟨M, hM, htimeBound⟩
                      rw [hout] at houtputOccupied
                      change next.status ≠ .unoccupied → next.lastDown =
                        some (selected.view.payload.downRecord i) at houtputOccupied
                      have hfield := houtputOccupied hnot
                      rw [hselectedPayload] at hfield
                      have hMrecord : M = payload.downRecord i :=
                        Option.some.inj (hM.symm.trans hfield)
                      have hdownStart : ActiveFollowerDownAcceptance.downStart p rate M =
                          payload.sigma := by
                        apply Fin.ext
                        have hsigmaPayload := congrArg OrdinaryMessageCodec.DownFields.sigma
                          (payload.downRecord_fields i)
                        have hsigmaM : M.val.sigma = payload.sigma.val + 1 := by
                          rw [hMrecord]
                          exact hsigmaPayload
                        have hstart := ActiveFollowerDownAcceptance.downStart_val_add_one p rate M
                        change (ActiveFollowerDownAcceptance.downStart p rate M).val =
                          payload.sigma.val at ⊢
                        omega
                      rw [hdownStart] at htimeBound
                      omega
                    have houtRun :
                        (ReferenceActivePhysicalHorizon.run initial source.1.2
                          (ActualInitializationPhysicalStep.selectedRowIndex p source)
                          rewards start (k.val + 1) (by omega) hmode).finalState.followers i =
                          .ordinary next nextMemory := by
                      have hcurrentOut := (congrArg
                        (fun rec => rec.output.next.followers i) hrecordEq).symm.trans hout
                      have hsuccessor :=
                        Bandits.Support.ReferenceAssignmentPayloadChronology.run_successor_finalState_eq_actualRunRecordAt
                          initial source.1.2
                          (ActualInitializationPhysicalStep.selectedRowIndex p source)
                          rewards start k.val (by omega) hmode
                      rw [hsuccessor]
                      simpa [current, ReferenceAssignmentPayloadChronology.actualRunRecordAt] using
                        hcurrentOut
                    have hdownNext := ReferenceFollowerDecoderChronology.run_downBatch_spec
                      initial source.1.2
                      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
                      start (k.val + 1) (by omega) hmode hdownSeed' i next nextMemory houtRun
                    have hdownNext' : ReferenceFollowerDecoderChronology.downBatchEndpoint next
                        (record.input.time.val + 1) := by
                      have heq : start + (k.val + 1) = record.input.time.val + 1 := by
                        omega
                      rw [← heq]
                      exact hdownNext.1
                    have hfinish :
                        (ReferenceActivePhysicalStep.finishFollower
                          record.output.preparation.coordinator.downView
                          (record.output.preparation.followers.followers i)
                          (record.output.ownEntries
                            (PublicDiscreteDraws.followerPlayer p.two_le_m i)).2).configuration =
                          .ordinary next nextMemory := by
                      rw [record.output_eq] at hout
                      change (ReferenceActivePhysicalStep.finishFollower
                        (ReferenceActivePhysicalStep.prepare record.input).coordinator.downView
                        ((ReferenceActivePhysicalStep.prepare record.input).followers.followers i)
                        ((ReferenceActivePhysicalStep.step record.input).ownEntries
                          (PublicDiscreteDraws.followerPlayer p.two_le_m i)).2).configuration =
                        .ordinary next nextMemory at hout
                      rw [record.output_eq]
                      change (ReferenceActivePhysicalStep.finishFollower
                        (ReferenceActivePhysicalStep.prepare record.input).coordinator.downView
                        ((ReferenceActivePhysicalStep.prepare record.input).followers.followers i)
                        ((ReferenceActivePhysicalStep.step record.input).ownEntries
                          (PublicDiscreteDraws.followerPlayer p.two_le_m i)).2).configuration = _
                      simpa [hprepEq] using hout
                    rcases hlocalPrepare with ⟨hconfig, hselected, hnoOffer,
                      hdataArm, hotherArm⟩
                    rcases ReferenceFollowerReplyChronology.finishFollower_ordinary_inversion
                        record.output.preparation.coordinator.downView
                        (record.output.preparation.followers.followers i)
                        (record.output.ownEntries
                          (PublicDiscreteDraws.followerPlayer p.two_le_m i)).2
                        next nextMemory hfinish with
                      ⟨choice, choiceMemory, post, hchoice, _, hreleaseNext, _, _⟩
                    have hnextLocal := releaseAndFinish_ordinary_success_domain
                      (record.output.preparation.followers.followers i).follower
                      (record.output.preparation.followers.followers i).row
                      (record.output.preparation.followers.followers i).time
                      (record.output.ownEntries
                        (PublicDiscreteDraws.followerPlayer p.two_le_m i)).2
                      choice choiceMemory post next nextMemory hreleaseNext
                    have hpreparedAgreement :
                        LocalConfiguration.ordinary old memory =
                          LocalConfiguration.ordinary choice choiceMemory :=
                      hconfig.symm.trans hchoice
                    rcases LocalConfiguration.ordinary.inj hpreparedAgreement with
                      ⟨_, hmemory⟩
                    have hmem : nextMemory = memory := (hnextLocal.2 hnextStatus).trans hmemory.symm
                    refine ⟨hstatusOld, hlocalOld.1, hdownOld', hstartRound,
                      hconfig, hstateInput, hupAdmissible, hselected, hnoOffer,
                      hdataArm, hotherArm, ?_⟩
                    exact ⟨hnextStatus, hnextLocal.1, hdownNext', hmem⟩
      | laterReconstructionFailure core consistent started hstart instruction hinstruction reason =>
          trivial
      | laterPrefixFailure core consistent started hstart instruction hinstruction arm reason hlater =>
          trivial
      | laterOrientationFailure core consistent started hstart instruction hinstruction set hlater =>
          trivial
      | laterChoiceFailure core consistent started hstart instruction hinstruction output hconsistency
          clockData installation reason => trivial
      | laterChosen core consistent started hstart instruction hinstruction output hconsistency
          clockData installation selection => trivial

/-- On an actual continuing collection, either an incoming follower is
dagger or every actual PREPARE configuration lies in the existing optional
readout's ordinary/unoccupied domain. The option remains unfilled in its
NONE branches. -/
theorem complete_continuing_collection_readout_domain_cases
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length) :
    let records := ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h
    let start := ReferenceCompletePhysicalHistory.physicalStart
      rate source rewards C_star C_h
    let r := records.get k
    let x := r.input
    let prep := r.output.preparation
    match prep.coordinator with
    | .collection payload ledger clock cutoff (.continuing core snapshot boundary scores) =>
        (∃ i : Fin (p.m - 1), x.state.followers i = .dagger) ∨
          (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout start r).isSome = true
    | _ => True := by
  classical
  let records := ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate source rewards C_star C_h
  let start := ReferenceCompletePhysicalHistory.physicalStart
    rate source rewards C_star C_h
  let record := records.get k
  change match record.output.preparation.coordinator with
    | .collection payload ledger clock cutoff (.continuing core snapshot boundary scores) =>
        (∃ i : Fin (p.m - 1), record.input.state.followers i = .dagger) ∨
          (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout start record).isSome = true
    | _ => True
  cases hcoord : record.output.preparation.coordinator with
  | first outcome => trivial
  | live registers owned base outcome => cases outcome <;> trivial
  | invalidCollectionCutoff => trivial
  | dagger => trivial
  | collection payload ledger clock cutoff outcome =>
      cases outcome with
      | clockFailure failure hfailure => trivial
      | localFailure started hstart hinvalid reason => trivial
      | coreFailure core started hstart reason => trivial
      | continuing core snapshot boundary scores =>
          by_cases hany : ∃ i : Fin (p.m - 1),
              record.input.state.followers i = .dagger
          · exact Or.inl hany
          · apply Or.inr
            have hpreparedReady :
                ReferenceLaterCollectionArrivalReadout.preparedFollowersUnoccupied record := by
              intro j
              cases hstate : record.input.state.followers j with
              | dagger => exact False.elim (hany ⟨j, hstate⟩)
              | ordinary old memory =>
                  have hcases := complete_continuing_collection_follower_preparation_cases
                    rate source rewards C_star C_h k j
                  dsimp only at hcases
                  rw [hcoord, hstate] at hcases
                  rcases hcases with ⟨hstatus, hlocal, hbatch, hstart, hconfig,
                    hinputDomain, hup, hselected, hnoOffer, hdata, hother, hout⟩
                  change match (record.output.preparation.followers.followers j).configuration with
                    | .ordinary state _ => state.status = .unoccupied
                    | .dagger => False
                  rw [hconfig]
                  exact hstatus
            exact (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout_domain
              start record).mpr ⟨hpreparedReady, by simp [hcoord]⟩
      | laterReconstructionFailure core consistent started hstart instruction hinstruction reason =>
          trivial
      | laterPrefixFailure core consistent started hstart instruction hinstruction arm reason hlater =>
          trivial
      | laterOrientationFailure core consistent started hstart instruction hinstruction set hlater =>
          trivial
      | laterChoiceFailure core consistent started hstart instruction hinstruction output hconsistency
          clockData installation reason => trivial
      | laterChosen core consistent started hstart instruction hinstruction output hconsistency
          clockData installation selection => trivial
end Bandits.Support.ReferenceContinuingCollectionFollowerPreparation

end
