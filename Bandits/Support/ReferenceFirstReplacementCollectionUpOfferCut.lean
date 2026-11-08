/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstReplacementCollectionUpReceiverProvenance
public import Bandits.Support.ReferenceCoordinatorUpPhysicalCall
public import Bandits.Support.ReferenceUpPhysicalHashRule

/-!
# First replacement collection: actual fixed UP offers

Sources: `sources/zip4/manuscript/06_interruptions.tex:108-177,246-299`,
`sources/zip4/manuscript/appendix_a_local_protocol.tex:100-108,141-157`, and
`sources/zip4/manuscript/05_binary_transport.tex:354-431`.

This module produces the actual current-DOWN origin and fixed UP offer cut
from the source-generated first replacement history. It retains saved eligible
diagnostics without asserting purity of an inherited completed UP window.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions

namespace Bandits.Support.ReferenceFirstReplacementCollectionUpOfferCut

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

/-- From an actual ordinary, unoccupied current-DOWN choice, construct the
literal admissible UP record and identify the expected word of that physical
round. Domain validity supplies all numerical bounds; the DOWN record supplies
the positive current start. -/
theorem actual_current_choice_up_offer
    (r : ReferenceCompletePhysicalHistory.RoundRecord p rate)
    (i : Fin (p.m - 1))
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (M : OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))
    (hindex : ReferenceActivePhysicalStep.upSenderIndex r.input = i)
    (hconfiguration : (r.output.preparation.followers.followers i).configuration =
      .ordinary state memory)
    (hstatus : state.status = ActiveRoundActions.FollowerStatus.unoccupied)
    (hdomain : ActiveFollowerLifecycle.localStateDomainValid state)
    (hcurrent : state.lastDown = some M)
    (hslot : PublicDiscreteDraws.slotDraw (r.input.row.2 r.input.time).1 =
      PublicDiscreteDraws.upSlot) :
    ∃ U : OrdinaryMessageCodec.UpRecord
        (ReferencePrelaunchFollower.codecParams p rate.eta),
      ActiveFollowerQueueOperation.checkedUpOffer rate.eta i r.input.row
        (r.input.state.activations i) r.input.time state = .offer U ∧
      U.val = ActiveFollowerQueueOperation.upOfferFields state ∧
      U.val.sigma = M.val.sigma ∧ 0 < U.val.sigma ∧
      ReferenceActivePhysicalStep.upExpected
        (ReferenceActivePhysicalStep.prepare r.input) =
          some (ActiveFollowerArmChoice.offeredUpWord rate.eta U) := by
  classical
  have hstateInput : ActiveFollowerQueueOperation.stateInputDomain state := by
    rcases hdomain with ⟨⟨hS, hdelta, hbacklog⟩, hbuffer, _⟩
    exact ⟨hS, hdelta, hbacklog,
      ActiveFollowerLifecycle.localBufferValid_timestamp hbuffer,
      ActiveFollowerLifecycle.localBufferValid_keys_nodup hbuffer⟩
  have hselected : ActiveFollowerQueueOperation.selectedUpRound i r.input.row
      (r.input.state.activations i) r.input.time := by
    have hselected' : ActiveFollowerQueueOperation.selectedUpRound
        (ReferenceActivePhysicalStep.upSenderIndex r.input) r.input.row
        (r.input.state.activations (ReferenceActivePhysicalStep.upSenderIndex r.input))
        r.input.time := by
      exact ⟨r.input.active (ReferenceActivePhysicalStep.upSenderIndex r.input), hslot,
        (CoordinatorUpMeasurability.selectedFollowerIndex_eq_draw _).symm⟩
    simpa only [hindex] using hselected'
  have hadmissible : OrdinaryMessageCodec.upAdmissible
      (ReferencePrelaunchFollower.codecParams p rate.eta)
      (ActiveFollowerQueueOperation.upOfferFields state) := by
    rcases M.property with ⟨hσ, hσT, _, _, _, _, _, _, _, _, _⟩
    rcases hdomain with ⟨⟨hS, hdelta, hbacklog⟩, _, _⟩
    right
    simpa [OrdinaryMessageCodec.upAdmissible,
      ActiveFollowerQueueOperation.upOfferFields,
      ReferencePrelaunchFollower.acceptedStart, hcurrent,
      ReferencePrelaunchFollower.codecParams] using
      (show 1 ≤ M.val.sigma ∧ M.val.sigma ≤ p.T ∧
        state.S ≤ p.T * D p ∧ state.delta ≤ D p ∧
        state.backlog ≤ p.T * D p from
        ⟨hσ, hσT, by simpa using hS, by simpa using hdelta,
          by simpa using hbacklog⟩)
  let U : OrdinaryMessageCodec.UpRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta) :=
    ⟨ActiveFollowerQueueOperation.upOfferFields state, hadmissible⟩
  have hoff : ActiveFollowerQueueOperation.checkedUpOffer rate.eta i r.input.row
      (r.input.state.activations i) r.input.time state = .offer U := by
    unfold ActiveFollowerQueueOperation.checkedUpOffer
    rw [dite_eq_left hstateInput, dite_eq_left ⟨hselected, hstatus⟩,
      dite_eq_left hadmissible]
  have hfields : U.val = ActiveFollowerQueueOperation.upOfferFields state := rfl
  have hsigma : U.val.sigma = M.val.sigma := by
    rw [hfields]
    simp [ActiveFollowerQueueOperation.upOfferFields,
      ReferencePrelaunchFollower.acceptedStart, hcurrent]
  have hpositive : 0 < U.val.sigma := by
    rw [hsigma]
    exact lt_of_lt_of_le Nat.zero_lt_one M.property.1
  have halign := r.output.preparation.follower_alignment i
  have hoff' : ActiveFollowerQueueOperation.checkedUpOffer rate.eta
      (ReferenceFollowerFixedReply.actualChoice r i).follower
      (ReferenceFollowerFixedReply.actualChoice r i).row
      (ReferenceFollowerFixedReply.actualChoice r i).activation
      (ReferenceFollowerFixedReply.actualChoice r i).time state = .offer U := by
    change ActiveFollowerQueueOperation.checkedUpOffer rate.eta
      (r.output.preparation.followers.followers i).follower
      (r.output.preparation.followers.followers i).row
      (r.output.preparation.followers.followers i).activation
      (r.output.preparation.followers.followers i).time state = .offer U
    rw [halign.1, halign.2.1, halign.2.2.1, halign.2.2.2]
    exact hoff
  have hword := ReferenceFollowerFixedReply.actualUpExpected_eq_encoded_offer
    r i hindex state memory hconfiguration U hoff'
  refine ⟨U, hoff, hfields, hsigma, hpositive, ?_⟩
  unfold ReferenceFollowerFixedReply.actualUpExpected at hword
  rw [r.output_eq] at hword
  exact hword

/-- A current DOWN and an ordinary local-domain state determine an admissible
UP record even before selecting a physical UP round. -/
theorem current_down_offer_record
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (M : OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))
    (hdomain : ActiveFollowerLifecycle.localStateDomainValid state)
    (hcurrent : state.lastDown = some M) :
    ∃ U : OrdinaryMessageCodec.UpRecord
        (ReferencePrelaunchFollower.codecParams p rate.eta),
      U.val = ActiveFollowerQueueOperation.upOfferFields state ∧
      U.val.sigma = M.val.sigma ∧ 0 < U.val.sigma := by
  have hadmissible : OrdinaryMessageCodec.upAdmissible
      (ReferencePrelaunchFollower.codecParams p rate.eta)
      (ActiveFollowerQueueOperation.upOfferFields state) := by
    rcases M.property with ⟨hσ, hσT, _, _, _, _, _, _, _, _, _⟩
    rcases hdomain with ⟨⟨hS, hdelta, hbacklog⟩, _, _⟩
    right
    simpa [OrdinaryMessageCodec.upAdmissible,
      ActiveFollowerQueueOperation.upOfferFields,
      ReferencePrelaunchFollower.acceptedStart, hcurrent,
      ReferencePrelaunchFollower.codecParams] using
      (show 1 ≤ M.val.sigma ∧ M.val.sigma ≤ p.T ∧
        state.S ≤ p.T * D p ∧ state.delta ≤ D p ∧
        state.backlog ≤ p.T * D p from
        ⟨hσ, hσT, by simpa using hS, by simpa using hdelta,
          by simpa using hbacklog⟩)
  let U : OrdinaryMessageCodec.UpRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta) :=
    ⟨ActiveFollowerQueueOperation.upOfferFields state, hadmissible⟩
  refine ⟨U, rfl, ?_, ?_⟩
  · simp [U, ActiveFollowerQueueOperation.upOfferFields,
      ReferencePrelaunchFollower.acceptedStart, hcurrent]
  · rw [show U.val.sigma = M.val.sigma by
      simp [U, ActiveFollowerQueueOperation.upOfferFields,
        ReferencePrelaunchFollower.acceptedStart, hcurrent]]
    exact lt_of_lt_of_le Nat.zero_lt_one M.property.1

/-- A later actual current choice with the same retained DOWN and numerical
reply registers uses the single UP record determined by its anchor. The
follower's other memory, buffer, and batch remain the actual choice values. -/
theorem actual_current_choice_uses_anchor_offer
    (r : ReferenceCompletePhysicalHistory.RoundRecord p rate)
    (i : Fin (p.m - 1))
    (state anchor : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (M : OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))
    (hindex : ReferenceActivePhysicalStep.upSenderIndex r.input = i)
    (hconfiguration : (r.output.preparation.followers.followers i).configuration =
      .ordinary state memory)
    (hstatus : state.status = ActiveRoundActions.FollowerStatus.unoccupied)
    (hdomain : ActiveFollowerLifecycle.localStateDomainValid state)
    (hcurrent : state.lastDown = some M)
    (hreply : ReferenceFollowerReplyChronology.reply state =
      ReferenceFollowerReplyChronology.reply anchor)
    (hslot : PublicDiscreteDraws.slotDraw (r.input.row.2 r.input.time).1 =
      PublicDiscreteDraws.upSlot) :
    ∃ U : OrdinaryMessageCodec.UpRecord
        (ReferencePrelaunchFollower.codecParams p rate.eta),
      ActiveFollowerQueueOperation.checkedUpOffer rate.eta i r.input.row
        (r.input.state.activations i) r.input.time state = .offer U ∧
      U.val = ActiveFollowerQueueOperation.upOfferFields anchor ∧
      U.val.sigma = M.val.sigma ∧ 0 < U.val.sigma ∧
      ReferenceActivePhysicalStep.upExpected
        (ReferenceActivePhysicalStep.prepare r.input) =
          some (ActiveFollowerArmChoice.offeredUpWord rate.eta U) := by
  have hreply := hreply
  change (state.lastDown, state.S, state.delta, state.backlog) =
    (anchor.lastDown, anchor.S, anchor.delta, anchor.backlog) at hreply
  rcases Prod.mk.inj hreply with ⟨hlast, hreply⟩
  rcases Prod.mk.inj hreply with ⟨hS, hreply⟩
  rcases Prod.mk.inj hreply with ⟨hdelta, hbacklog⟩
  have hfields : ActiveFollowerQueueOperation.upOfferFields state =
      ActiveFollowerQueueOperation.upOfferFields anchor := by
    apply OrdinaryMessageCodec.UpFields.ext
    · simp [ActiveFollowerQueueOperation.upOfferFields,
        ReferencePrelaunchFollower.acceptedStart, hlast]
    · simpa [ActiveFollowerQueueOperation.upOfferFields] using hS
    · simpa [ActiveFollowerQueueOperation.upOfferFields] using hdelta
    · simpa [ActiveFollowerQueueOperation.upOfferFields] using hbacklog
  obtain ⟨U, hcheck, hval, hsigma, hpositive, hword⟩ :=
    actual_current_choice_up_offer r i state memory M hindex hconfiguration
      hstatus hdomain hcurrent hslot
  refine ⟨U, hcheck, hval.trans hfields, hsigma, hpositive, hword⟩

/-- Every eligible retained diagnostic on an actual physical record uses the
same affine word as its checked current offer. The diagnostic equations remain
available even when later receiver, finish, detection, or overflow logic fails. -/
theorem retained_eligible_diagnostic_uses_offer
    (r : ReferenceCompletePhysicalHistory.RoundRecord p rate)
    (i : Fin (p.m - 1))
    (d : ReferenceActivePhysicalStep.UpDiagnostic p rate)
    (U : OrdinaryMessageCodec.UpRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))
    (hdiagnostic : r.output.coordinator.up = some d)
    (hselected : d.input.selectedFollower = i)
    (heligible : AffineBatchDecoder.eligible
      (CoordinatorUpReception.roundInput d.input))
    (hword : ReferenceActivePhysicalStep.upExpected
      (ReferenceActivePhysicalStep.prepare r.input) =
        some (ActiveFollowerArmChoice.offeredUpWord rate.eta U)) :
    d.input.time = r.input.time ∧
    d.input.selectedFollower = i ∧
    d.input.slot = PublicDiscreteDraws.slotDraw (r.input.row.2 r.input.time).1 ∧
    d.input.affineSample = (r.input.row.2 r.input.time).2 (1, i) ∧
    AffineChannelLaw.affineHash d.input.affineSample
      (ActiveFollowerArmChoice.offeredUpWord rate.eta U) = 1 := by
  have hpositive : ReferenceActiveAffinePositiveTest.upPositive r.input = true := by
    rw [ReferenceActiveAffinePositiveTest.record_upPositive]
    simp [ReferenceActiveAffinePositiveTest.upDiagnosticPositive,
      hdiagnostic, heligible]
  have hsent : ReferenceActiveAffinePositiveTest.upSent r.input =
      some (ActiveFollowerArmChoice.offeredUpWord rate.eta U) := hword
  have hhash := ReferenceUpPhysicalHashRule.upPositive_hash_one r.input
    (ActiveFollowerArmChoice.offeredUpWord rate.eta U) hsent hpositive
  obtain ⟨_, _, _, _, htime, _, hindex, hsample, hslot, _, _, _, _, _⟩ :=
    ReferenceCoordinatorUpPhysicalCall.record_retained_up_input_fields
      r d hdiagnostic
  have hselectedIndex :
      CoordinatorUpMeasurability.selectedFollowerIndex
        ((r.input.rows r.input.selected).2 r.input.time) = i := by
    exact hindex.symm.trans hselected
  have hchannel : CoordinatorUpMeasurability.selectedChannelFollower
      ((r.input.rows r.input.selected).2 r.input.time) =
        Fin.cast (show ContinuousLearningRows.d p = p.m - 1 by rfl) i := by
    apply Fin.ext
    have hv := congrArg Fin.val hselectedIndex
    simpa [CoordinatorUpMeasurability.selectedChannelFollower,
      CoordinatorUpMeasurability.selectedFollowerIndex,
      ContinuousLearningRows.d] using hv
  have hsample' : d.input.affineSample = (r.input.row.2 r.input.time).2
      (1, Fin.cast (show ContinuousLearningRows.d p = p.m - 1 by rfl) i) := by
    rw [hsample, hchannel]
    rfl
  have hindex' : ReferenceActivePhysicalStep.upSenderIndex r.input = i :=
    hselectedIndex
  have hhash' : AffineChannelLaw.affineHash
      ((r.input.row.2 r.input.time).2 (1, i))
      (ActiveFollowerArmChoice.offeredUpWord rate.eta U) = 1 := by
    simpa [hindex'] using hhash
  exact ⟨htime, hselected, hslot, hsample', by
    rw [hsample']
    exact hhash'⟩

/-- A retained-positive entry needs the offered word only at its own eligible
actual diagnostic. This preserves the source record and saved call while
allowing later reception or finish failures. -/
theorem retained_positive_entry_has_conditional_offer_equation
    (records : List (ReferenceCompletePhysicalHistory.RoundRecord p rate))
    (i : Fin (p.m - 1))
    (U : OrdinaryMessageCodec.UpRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))
    (hword : ∀ r, r ∈ records → ∀ d : ReferenceActivePhysicalStep.UpDiagnostic p rate,
      r.output.coordinator.up = some d → d.input.selectedFollower = i →
      AffineBatchDecoder.eligible (CoordinatorUpReception.roundInput d.input) →
      ReferenceActivePhysicalStep.upExpected
        (ReferenceActivePhysicalStep.prepare r.input) =
          some (ActiveFollowerArmChoice.offeredUpWord rate.eta U))
    (entry : AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p))
    (hentry : entry ∈
      ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries records i) :
    ∃ r ∈ records, ∃ d : ReferenceActivePhysicalStep.UpDiagnostic p rate,
      r.output.coordinator.up = some d ∧ d.input.selectedFollower = i ∧
      AffineBatchDecoder.eligible (CoordinatorUpReception.roundInput d.input) ∧
      entry.time = r.input.time ∧
      d.input.slot = PublicDiscreteDraws.slotDraw (r.input.row.2 r.input.time).1 ∧
      entry.sample = d.input.affineSample ∧
      d.input.affineSample = (r.input.row.2 r.input.time).2 (1, i) ∧
      AffineChannelLaw.affineHash entry.sample
        (ActiveFollowerArmChoice.offeredUpWord rate.eta U) = 1 := by
  classical
  change entry ∈ records.flatMap (fun r =>
    ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries r i) at hentry
  obtain ⟨r, hr, hentry⟩ := List.mem_flatMap.mp hentry
  cases hd : r.output.coordinator.up with
  | none =>
      simp [ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries, hd] at hentry
  | some d =>
      by_cases hchannel :
          ReferenceCoordinatorUpDecoderReplay.retainedUpFollower d = i
      · have hselected : d.input.selectedFollower = i := by
          simpa [ReferenceCoordinatorUpDecoderReplay.retainedUpFollower] using hchannel
        have hpositiveEntry : entry ∈
            AffineBatchDecoder.positiveAt p
              (ReferenceCoordinatorUpDecoderReplay.constantInputTrace d.input)
              (ReferenceCoordinatorUpDecoderReplay.retainedUpTime d) := by
          simpa [ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries,
            ReferenceCoordinatorUpDecoderReplay.retainedUpFollower, hd, hselected] using hentry
        by_cases heligible : AffineBatchDecoder.eligible
            ((ReferenceCoordinatorUpDecoderReplay.constantInputTrace d.input)
              (ReferenceCoordinatorUpDecoderReplay.retainedUpTime d))
        · have hentryEq : entry = AffineBatchDecoder.entry p
              (ReferenceCoordinatorUpDecoderReplay.constantInputTrace d.input)
              (ReferenceCoordinatorUpDecoderReplay.retainedUpTime d) := by
            simpa [AffineBatchDecoder.positiveAt, heligible] using hpositiveEntry
          subst entry
          have heligible' : AffineBatchDecoder.eligible
              (CoordinatorUpReception.roundInput d.input) := by
            simpa [ReferenceCoordinatorUpDecoderReplay.constantInputTrace,
              ReferenceCoordinatorUpDecoderReplay.retainedUpRoundInput] using heligible
          have hdiag := retained_eligible_diagnostic_uses_offer r i d U hd hselected
            heligible' (hword r hr d hd hselected heligible')
          have hsample : (AffineBatchDecoder.entry p
              (ReferenceCoordinatorUpDecoderReplay.constantInputTrace d.input)
              (ReferenceCoordinatorUpDecoderReplay.retainedUpTime d)).sample =
                d.input.affineSample := by
            simp [AffineBatchDecoder.entry,
              ReferenceCoordinatorUpDecoderReplay.constantInputTrace,
              ReferenceCoordinatorUpDecoderReplay.retainedUpTime,
              CoordinatorUpReception.roundInput]
          refine ⟨r, hr, d, hd, hselected, heligible', ?_, hdiag.2.2.1,
            hsample, hdiag.2.2.2.1, ?_⟩
          · calc
              (AffineBatchDecoder.entry p
                (ReferenceCoordinatorUpDecoderReplay.constantInputTrace d.input)
                (ReferenceCoordinatorUpDecoderReplay.retainedUpTime d)).time = d.input.time := rfl
              _ = r.input.time := hdiag.1
          · rw [hsample]
            exact hdiag.2.2.2.2
        · simp [AffineBatchDecoder.positiveAt, heligible] at hpositiveEntry
      · have hchannel' : ¬ d.input.selectedFollower = i := by
          simpa [ReferenceCoordinatorUpDecoderReplay.retainedUpFollower] using hchannel
        simp [ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries,
          ReferenceCoordinatorUpDecoderReplay.retainedUpFollower, hd, hchannel'] at hentry

/-- Find the least actual retained DOWN acceptance for one literal message in
an actual finite record list. The result keeps the original RetainedDown
witness and records minimality among list indices. -/
theorem least_actual_retained_down_event
    (records : List (ReferenceCompletePhysicalHistory.RoundRecord p rate))
    (i : Fin (p.m - 1))
    (M : OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))
    (hevent : ∃ q : Fin records.length,
      ReferenceAcceptedUpFollowerHistory.RetainedDown (records.get q) i M) :
    ∃ q : Fin records.length,
      ReferenceAcceptedUpFollowerHistory.RetainedDown (records.get q) i M ∧
      ∀ j : Fin records.length, j.val < q.val →
        ¬ ReferenceAcceptedUpFollowerHistory.RetainedDown (records.get j) i M := by
  classical
  let event : ℕ → Prop := fun n =>
    ∃ hn : n < records.length,
      ReferenceAcceptedUpFollowerHistory.RetainedDown
        (records.get ⟨n, hn⟩) i M
  have heventNat : ∃ n, event n := by
    obtain ⟨q, hq⟩ := hevent
    exact ⟨q.val, q.isLt, hq⟩
  let q := Nat.find heventNat
  have hq : event q := Nat.find_spec heventNat
  obtain ⟨hqLt, hqRetained⟩ := hq
  refine ⟨⟨q, hqLt⟩, hqRetained, ?_⟩
  intro j hj hretained
  have hnot : ¬ event j.val := Nat.find_min heventNat hj
  exact hnot ⟨j.isLt, hretained⟩

/-- Two actual retained acceptances of the same complete DOWN record cannot
occur at different indices of a connected prefix with an ordinary endpoint. -/
theorem connected_retained_down_index_unique
    {initial final : ReferenceActivePhysicalStep.State p rate}
    {records : List (ReferenceActivePhysicalHorizon.RoundRecord (rate := rate))}
    (hchain : ReferenceActivePhysicalHorizon.Connected initial records final)
    (i : Fin (p.m - 1))
    (last : ReferencePrelaunchFollower.State p rate.eta)
    (lastMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hfinal : final.followers i = .ordinary last lastMemory)
    (a b : ℕ)
    (ha : a < records.length)
    (hb : b < records.length)
    (M : OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))
    (hleft : ReferenceAcceptedUpFollowerHistory.RetainedDown records[a] i M)
    (hright : ReferenceAcceptedUpFollowerHistory.RetainedDown records[b] i M) :
    a = b := by
  have retainedDownStartsStrict
      (a b : ℕ) (ha : a < records.length) (hb : b < records.length)
      (hab : a < b)
      (left right : OrdinaryMessageCodec.DownRecord
        (ReferencePrelaunchFollower.codecParams p rate.eta))
      (hleft : ReferenceAcceptedUpFollowerHistory.RetainedDown records[a] i left)
      (hright : ReferenceAcceptedUpFollowerHistory.RetainedDown records[b] i right) :
      left.val.sigma < right.val.sigma := by
    obtain ⟨next, nextMemory, hnext, _⟩ :=
      ReferenceFollowerReplyChronology.connected_output_chronology
        hchain i last lastMemory hfinal b hb
    obtain ⟨choice, choiceMemory, hchoice, hstrict, _⟩ :=
      ReferenceFollowerReplyChronology.record_appliedDown_strict records[b] i
        right.val.sigma
        (ReferenceAcceptedUpFollowerHistory.retainedDown_appliedDown hright)
        next nextMemory hnext
    obtain ⟨before, beforeMemory, hbefore, hreply, _⟩ :=
      ReferenceFollowerReplyChronology.record_input_to_choice records[b] i
        choice choiceMemory hchoice
    have hstart := ReferenceFollowerReplyChronology.acceptedStart_eq_of_reply_eq hreply
    have hprefix := ReferenceFollowerReplyChronology.connected_take_to_input
      hchain b hb
    have haTake : a < (records.take b).length := by
      simp only [List.length_take]
      exact lt_min hab ha
    obtain ⟨after, afterMemory, hafter, hbound⟩ :=
      ReferenceFollowerReplyChronology.connected_output_chronology
        hprefix i before beforeMemory hbefore a haTake
    rw [List.getElem_take] at hafter
    obtain ⟨_, _, _, _, hafterStart⟩ :=
      ReferenceFollowerReplyChronology.record_appliedDown_strict records[a] i
        left.val.sigma
        (ReferenceAcceptedUpFollowerHistory.retainedDown_appliedDown hleft)
        after afterMemory hafter
    omega
  rcases lt_trichotomy a b with hab | hab | hab
  · have hstrict := retainedDownStartsStrict a b ha hb hab M M hleft hright
    omega
  · exact hab
  · have hstrict := retainedDownStartsStrict b a hb ha hab M M hright hleft
    omega

/-- A retained DOWN event in an actual connected interval has one unique
record index. The least-event selector keeps that actual acceptance witness. -/
theorem unique_actual_retained_down_event
    {initial final : ReferenceActivePhysicalStep.State p rate}
    {records : List (ReferenceActivePhysicalHorizon.RoundRecord (rate := rate))}
    (hchain : ReferenceActivePhysicalHorizon.Connected initial records final)
    (i : Fin (p.m - 1))
    (last : ReferencePrelaunchFollower.State p rate.eta)
    (lastMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hfinal : final.followers i = .ordinary last lastMemory)
    (M : OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))
    (hevent : ∃ q : Fin records.length,
      ReferenceAcceptedUpFollowerHistory.RetainedDown (records.get q) i M) :
    ∃! q : Fin records.length,
      ReferenceAcceptedUpFollowerHistory.RetainedDown (records.get q) i M := by
  obtain ⟨q, hq, _⟩ := least_actual_retained_down_event records i M hevent
  refine ⟨q, hq, ?_⟩
  intro q' hq'
  apply Fin.ext
  symm
  exact connected_retained_down_index_unique hchain i last lastMemory hfinal
    q.val q'.val q.isLt q'.isLt M hq hq'

/-- The cutoff's actual CHOICE remains an inherited current-DOWN case exactly
when its pre-interruption state was occupied. The imported cutoff witness then
gives the unique actual retained origin in the earlier physical prefix. -/
theorem inherited_current_cut_choice_has_unique_prefix_origin
    {initial final : ReferenceActivePhysicalStep.State p rate}
    {prefixRecords : List (ReferenceActivePhysicalHorizon.RoundRecord (rate := rate))}
    (hchain : ReferenceActivePhysicalHorizon.Connected initial prefixRecords final)
    (i : Fin (p.m - 1))
    (M : OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))
    (old : ReferencePrelaunchFollower.State p rate.eta)
    (oldMemory : ActiveFollowerLifecycle.LocalMemory p)
    (choice : ReferencePrelaunchFollower.State p rate.eta)
    (hcutInput : final.followers i = .ordinary old oldMemory)
    (hchoiceCurrent : choice.lastDown = some M)
    (hchoiceStart : ReferencePrelaunchFollower.acceptedStart choice = M.val.sigma ↔
      old.status ≠ ActiveRoundActions.FollowerStatus.unoccupied)
    (hinPrefix : old.status ≠ ActiveRoundActions.FollowerStatus.unoccupied →
      ∃ x : Fin prefixRecords.length,
        ReferenceAcceptedUpFollowerHistory.RetainedDown (prefixRecords.get x) i M) :
    ∃! x : Fin prefixRecords.length,
      ReferenceAcceptedUpFollowerHistory.RetainedDown (prefixRecords.get x) i M := by
  have hstart : ReferencePrelaunchFollower.acceptedStart choice = M.val.sigma := by
    simp [ReferencePrelaunchFollower.acceptedStart, hchoiceCurrent]
  have holdBusy := hchoiceStart.mp hstart
  exact unique_actual_retained_down_event hchain i old oldMemory hcutInput M
    (hinPrefix holdBusy)

private theorem record_current_down_origin
    (record : ReferenceActivePhysicalHorizon.RoundRecord (rate := rate))
    (i : Fin (p.m - 1))
    (next : ReferencePrelaunchFollower.State p rate.eta)
    (nextMemory : ActiveFollowerLifecycle.LocalMemory p)
    (target : OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))
    (hout : record.output.next.followers i = .ordinary next nextMemory)
    (hlast : next.lastDown = some target) :
    (∃ before : ReferencePrelaunchFollower.State p rate.eta,
      ∃ beforeMemory : ActiveFollowerLifecycle.LocalMemory p,
        record.input.state.followers i = .ordinary before beforeMemory ∧
        before.lastDown = some target) ∨
      ReferenceAcceptedUpFollowerHistory.RetainedDown record i target := by
  rcases record with ⟨input, output, output_eq⟩
  cases output_eq
  let prepared := ReferenceActivePhysicalStep.prepare input
  let sender := prepared.followers.followers i
  let view := prepared.coordinator.downView
  let observation := prepared.feedback.observations
    (PublicDiscreteDraws.followerPlayer p.two_le_m i)
  have houtFinish :
      (ReferenceActivePhysicalStep.finishFollower view sender observation).configuration =
        .ordinary next nextMemory := by
    simpa only [ReferenceActivePhysicalStep.step,
      ReferenceActivePhysicalStep.PreparedRound.observeFollower] using hout
  obtain ⟨choice, choiceMemory, post, hchoice, hrecord, hfinish,
      hfinishDownInput, hfinishDown⟩ :=
    ReferenceFollowerReplyChronology.finishFollower_ordinary_inversion
      view sender observation next nextMemory houtFinish
  obtain ⟨before, beforeMemory, hinput, hreply, _⟩ :=
    ReferenceFollowerReplyChronology.record_input_to_choice
      ⟨input, ReferenceActivePhysicalStep.step input, rfl⟩ i choice choiceMemory hchoice
  have hfinishFrame := ReferenceFollowerReplyChronology.releaseAndFinish_frame
    sender.follower sender.row sender.time observation choice post next choiceMemory
    nextMemory hfinish
  have hnextPost : next.lastDown = post.lastDown := by
    have h := congrArg Prod.fst hfinishFrame.1
    change next.lastDown = post.lastDown at h
    exact h
  have hrecordResult := ReferenceFollowerReplyChronology.recordFollower_ordinary_inversion
    view sender.follower sender.row sender.activation sender.time sender.active sender.arm
      observation choice post hrecord
  rcases hrecordResult with ⟨hpostChoice, _⟩ |
    ⟨logged, cut, raw, message, scan, registers, lastService,
      hrecordInput, hrecordDown, hcut, houtcome, _, hpostMessage⟩
  · left
    refine ⟨before, beforeMemory, hinput, ?_⟩
    have hchoiceBefore : choice.lastDown = before.lastDown := by
      have h := congrArg Prod.fst hreply
      change choice.lastDown = before.lastDown at h
      exact h
    calc
      before.lastDown = choice.lastDown := hchoiceBefore.symm
      _ = post.lastDown := hpostChoice.symm
      _ = next.lastDown := hnextPost.symm
      _ = some target := hlast
  · right
    have hmessage : message = target := by
      have hnext : next.lastDown = some message := hnextPost.trans hpostMessage
      exact Option.some.inj (hnext.symm.trans hlast)
    subst message
    refine ⟨logged, cut, post, raw, scan, registers, lastService, ?_, ?_, houtcome⟩
    · change ((ReferenceActivePhysicalStep.step input).followers i).downInput = some logged
      have halignment := prepared.follower_alignment i
      simpa only [ReferenceActivePhysicalStep.step,
        ReferenceActivePhysicalStep.PreparedRound.observeFollower,
        sender, prepared, halignment.1, halignment.2.1] using
        hfinishDownInput.trans hrecordInput
    · change ((ReferenceActivePhysicalStep.step input).followers i).down = some cut
      have halignment := prepared.follower_alignment i
      simpa only [ReferenceActivePhysicalStep.step,
        ReferenceActivePhysicalStep.PreparedRound.observeFollower,
        sender, prepared, halignment.1, halignment.2.1] using
        hfinishDown.trans hrecordDown

/-- An actual current DOWN at an ordinary connected endpoint either was
already present at the interval input or has its exact retained acceptance
inside that physical interval. -/
theorem connected_endpoint_current_down_has_actual_origin
    {initial final : ReferenceActivePhysicalStep.State p rate}
    {records : List (ReferenceActivePhysicalHorizon.RoundRecord (rate := rate))}
    (hchain : ReferenceActivePhysicalHorizon.Connected initial records final)
    (i : Fin (p.m - 1))
    (first : ReferencePrelaunchFollower.State p rate.eta)
    (firstMemory : ActiveFollowerLifecycle.LocalMemory p)
    (last : ReferencePrelaunchFollower.State p rate.eta)
    (lastMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hfirst : initial.followers i = .ordinary first firstMemory)
    (hfinal : final.followers i = .ordinary last lastMemory)
    (M : OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))
    (hcurrent : last.lastDown = some M) :
    first.lastDown = some M ∨
      ∃ record ∈ records,
        ReferenceAcceptedUpFollowerHistory.RetainedDown record i M := by
  induction records generalizing initial first firstMemory final last lastMemory with
  | nil =>
      change final = initial at hchain
      subst final
      have hstates :=
        DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj (hfirst.symm.trans hfinal)
      rcases hstates with ⟨rfl, rfl⟩
      exact Or.inl hcurrent
  | cons record rest ih =>
      rcases hchain with ⟨hpre, hrest⟩
      obtain ⟨middle, middleMemory, hmiddle, _, _, _⟩ :=
        ReferenceFollowerReplyChronology.connected_ordinary_chronology
          hrest i last lastMemory hfinal
      have hrecordInput : record.input.state.followers i = .ordinary first firstMemory := by
        rw [hpre]
        exact hfirst
      rcases ih hrest middle middleMemory last lastMemory hmiddle hfinal hcurrent with
        hmiddleCurrent | ⟨laterRecord, hlaterRecord, hlaterCurrent⟩
      · rcases record_current_down_origin record i middle middleMemory M hmiddle
          hmiddleCurrent with
          ⟨before, beforeMemory, hbefore, hbeforeCurrent⟩ | hcurrentRecord
        · have hstates :=
            DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
              (hbefore.symm.trans hrecordInput)
          rcases hstates with ⟨rfl, rfl⟩
          exact Or.inl hbeforeCurrent
        · exact Or.inr ⟨record, List.mem_cons_self, hcurrentRecord⟩
      · exact Or.inr ⟨laterRecord, List.mem_cons_of_mem _ hlaterRecord,
          hlaterCurrent⟩

/-- Align prefixes of the actual replacement collection list with the endpoint
states used by the segment extractor. The only history inputs are adjacency
equations for these same physical records. -/
theorem actual_collection_endpoint_alignment
    (cut : ReferenceCompletePhysicalHistory.RoundRecord p rate)
    (W : List (ReferenceCompletePhysicalHistory.RoundRecord p rate))
    (hadjacent : ∀ j : Fin W.length,
      (W.get j).input.state =
        ReferenceCollectionSegmentExtraction.endpointState cut.output.next (W.take j.val) ∧
      ReferenceCollectionSegmentExtraction.endpointState cut.output.next
          (W.take (j.val + 1)) = (W.get j).output.next) :
    let K := cut :: W
    let E := fun j => ReferenceCollectionSegmentExtraction.endpointState
      cut.output.next (W.take j)
    let Z := fun j => ReferenceCollectionSegmentExtraction.endpointState
      cut.input.state (K.take j)
    Z 0 = cut.input.state ∧
    (∀ j : ℕ, j ≤ W.length → Z (j + 1) = E j) ∧
    (∀ j : Fin W.length,
      (W.get j).input.state = Z (j.val + 1) ∧
      Z (j.val + 2) = (W.get j).output.next) := by
  dsimp only
  let K := cut :: W
  let E := fun j => ReferenceCollectionSegmentExtraction.endpointState
    cut.output.next (W.take j)
  let Z := fun j => ReferenceCollectionSegmentExtraction.endpointState
    cut.input.state (K.take j)
  have hZzero : Z 0 = cut.input.state := by
    simp [Z, K, ReferenceCollectionSegmentExtraction.endpointState]
  have hZsucc : ∀ j : ℕ, Z (j + 1) = E j := by
    intro j
    simp [Z, K, E, ReferenceCollectionSegmentExtraction.endpointState,
      List.take_succ_cons]
  refine ⟨hZzero, ?_, ?_⟩
  · intro j _
    exact hZsucc j
  · intro j
    have hstate := hadjacent j
    refine ⟨?_, ?_⟩
    · exact hstate.1.trans (hZsucc j).symm
    · calc
        Z (j.val + 2) = E (j.val + 1) := by
          simpa [Nat.add_assoc] using hZsucc (j.val + 1)
        _ = (W.get j).output.next := hstate.2

/-- CHOICE-to-endpoint chronology keeps the actual intermediate output. -/
theorem connected_choice_endpoint_chronology
    {initial final : ReferenceActivePhysicalStep.State p rate}
    {records : List (ReferenceActivePhysicalHorizon.RoundRecord (rate := rate))}
    (chain : ReferenceActivePhysicalHorizon.Connected initial records final)
    (i : Fin (p.m - 1)) (j : Fin records.length)
    (choice last : ReferencePrelaunchFollower.State p rate.eta)
    (memory lastMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hc : (ReferenceFollowerFixedReply.actualChoice (records.get j) i).configuration =
      .ordinary choice memory)
    (hf : final.followers i = .ordinary last lastMemory) :
    ReferencePrelaunchFollower.acceptedStart choice ≤
        ReferencePrelaunchFollower.acceptedStart last ∧
    (choice.status = .unoccupied → ReferencePrelaunchFollower.acceptedStart choice =
        ReferencePrelaunchFollower.acceptedStart last →
      last.status = .unoccupied ∧ ReferenceFollowerReplyChronology.reply last =
        ReferenceFollowerReplyChronology.reply choice) := by
  have tail := ReferenceFollowerReplyChronology.connected_drop_from_output chain j.val j.isLt
  obtain ⟨next, nextMemory, hn, hnl, hkeep, _⟩ :=
    ReferenceFollowerReplyChronology.connected_ordinary_chronology tail i last lastMemory hf
  obtain ⟨choice', memory', hc', hcn, hframe, _⟩ :=
    ReferenceFollowerReplyChronology.record_choice_chronology (records.get j) i next nextMemory hn
  obtain ⟨rfl, rfl⟩ := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
    (hc.symm.trans hc')
  refine ⟨hcn.trans hnl, ?_⟩
  intro hu heq
  obtain ⟨hnu, hnr⟩ := hframe hu (by omega)
  obtain ⟨hlu, hlr⟩ := hkeep hnu (by omega)
  exact ⟨hlu, hlr.trans hnr⟩

/-- Assemble physical offers and every saved positive equation from actual
CHOICE replies. These local inputs are discharged by the source-root proof. -/
theorem fixed_offer_on_actual_reply_suffix
    (records : List (ReferenceCompletePhysicalHistory.RoundRecord p rate))
    (i : Fin (p.m - 1)) (b : ℕ)
    (anchor : ReferencePrelaunchFollower.State p rate.eta)
    (M : OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (hdomain : ActiveFollowerLifecycle.localStateDomainValid anchor)
    (hcurrent : anchor.lastDown = some M)
    (hchoices : ∀ j : Fin records.length, b ≤ j.val →
      ∃ state memory,
        (ReferenceFollowerFixedReply.actualChoice (records.get j) i).configuration =
          .ordinary state memory ∧ state.status = .unoccupied ∧
        ActiveFollowerLifecycle.localStateDomainValid state ∧ state.lastDown = some M ∧
        ReferenceFollowerReplyChronology.reply state = ReferenceFollowerReplyChronology.reply anchor) :
    ∃ U : OrdinaryMessageCodec.UpRecord (ReferencePrelaunchFollower.codecParams p rate.eta),
      U.val = ActiveFollowerQueueOperation.upOfferFields anchor ∧
      U.val.sigma = M.val.sigma ∧ 0 < U.val.sigma ∧
      (∀ j : Fin records.length, b ≤ j.val → ∃ state memory,
        (ReferenceFollowerFixedReply.actualChoice (records.get j) i).configuration =
          .ordinary state memory ∧ state.status = .unoccupied ∧
        state.lastDown = some M ∧
        ReferenceFollowerReplyChronology.reply state = ReferenceFollowerReplyChronology.reply anchor ∧
        (ReferenceActivePhysicalStep.upSenderIndex (records.get j).input = i →
          PublicDiscreteDraws.slotDraw ((records.get j).input.row.2
            (records.get j).input.time).1 = PublicDiscreteDraws.upSlot →
          ActiveFollowerQueueOperation.checkedUpOffer rate.eta i (records.get j).input.row
            ((records.get j).input.state.activations i) (records.get j).input.time state = .offer U ∧
          ReferenceActivePhysicalStep.upExpected (ReferenceActivePhysicalStep.prepare
            (records.get j).input) = some (ActiveFollowerArmChoice.offeredUpWord rate.eta U)) ∧
        (∀ d : ReferenceActivePhysicalStep.UpDiagnostic p rate,
          (records.get j).output.coordinator.up = some d → d.input.selectedFollower = i →
          AffineBatchDecoder.eligible (CoordinatorUpReception.roundInput d.input) →
          d.input.time = (records.get j).input.time ∧ d.input.selectedFollower = i ∧
          d.input.slot = PublicDiscreteDraws.slotDraw
            ((records.get j).input.row.2 (records.get j).input.time).1 ∧
          d.input.affineSample = ((records.get j).input.row.2 (records.get j).input.time).2 (1, i) ∧
          AffineChannelLaw.affineHash d.input.affineSample
            (ActiveFollowerArmChoice.offeredUpWord rate.eta U) = 1)) ∧
      (∀ entry ∈ ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries (records.drop b) i,
        ∃ r ∈ records.drop b, ∃ d : ReferenceActivePhysicalStep.UpDiagnostic p rate,
          r.output.coordinator.up = some d ∧ d.input.selectedFollower = i ∧
          AffineBatchDecoder.eligible (CoordinatorUpReception.roundInput d.input) ∧
          entry.time = r.input.time ∧
          d.input.slot = PublicDiscreteDraws.slotDraw (r.input.row.2 r.input.time).1 ∧
          entry.sample = d.input.affineSample ∧
          d.input.affineSample = (r.input.row.2 r.input.time).2 (1, i) ∧
          AffineChannelLaw.affineHash entry.sample
            (ActiveFollowerArmChoice.offeredUpWord rate.eta U) = 1) := by
  obtain ⟨U, hfields, hsigma, hpositive⟩ := current_down_offer_record anchor M hdomain hcurrent
  have hoffers : ∀ j : Fin records.length, b ≤ j.val → ∃ state memory,
      (ReferenceFollowerFixedReply.actualChoice (records.get j) i).configuration =
        .ordinary state memory ∧ state.status = .unoccupied ∧ state.lastDown = some M ∧
      ReferenceFollowerReplyChronology.reply state = ReferenceFollowerReplyChronology.reply anchor ∧
      (ReferenceActivePhysicalStep.upSenderIndex (records.get j).input = i →
        PublicDiscreteDraws.slotDraw ((records.get j).input.row.2
          (records.get j).input.time).1 = PublicDiscreteDraws.upSlot →
        ActiveFollowerQueueOperation.checkedUpOffer rate.eta i (records.get j).input.row
          ((records.get j).input.state.activations i) (records.get j).input.time state = .offer U ∧
        ReferenceActivePhysicalStep.upExpected (ReferenceActivePhysicalStep.prepare
          (records.get j).input) = some (ActiveFollowerArmChoice.offeredUpWord rate.eta U)) := by
    intro j hj
    obtain ⟨state, memory, hc, hu, hd, hm, hr⟩ := hchoices j hj
    refine ⟨state, memory, hc, hu, hm, hr, ?_⟩
    intro hi hs
    obtain ⟨U', hcheck, hfields', _, _, hword⟩ := actual_current_choice_uses_anchor_offer
      (records.get j) i state anchor memory M hi hc hu hd hm hr hs
    have he : U' = U := Subtype.ext (hfields'.trans hfields.symm)
    exact he ▸ ⟨hcheck, hword⟩
  have wordAt : ∀ j : Fin records.length, b ≤ j.val →
      ∀ d : ReferenceActivePhysicalStep.UpDiagnostic p rate,
      (records.get j).output.coordinator.up = some d → d.input.selectedFollower = i →
      AffineBatchDecoder.eligible (CoordinatorUpReception.roundInput d.input) →
      ReferenceActivePhysicalStep.upExpected (ReferenceActivePhysicalStep.prepare
        (records.get j).input) = some (ActiveFollowerArmChoice.offeredUpWord rate.eta U) := by
    intro j hj d hd hi he
    obtain ⟨_, _, _, _, _, _, hindex, _, hslot, _, _, _, _, _⟩ :=
      ReferenceCoordinatorUpPhysicalCall.record_retained_up_input_fields (records.get j) d hd
    have hgate := (CoordinatorUpReception.roundInput_selected_iff_gate d.input).mp he.1
    obtain ⟨state, memory, hc, hu, hm, hr, ho⟩ := hoffers j hj
    exact (ho (hindex.symm.trans hi) (hslot.symm.trans hgate.2.1)).2
  refine ⟨U, hfields, hsigma, hpositive, ?_, ?_⟩
  · intro j hj
    obtain ⟨state, memory, hc, hu, hm, hr, ho⟩ := hoffers j hj
    refine ⟨state, memory, hc, hu, hm, hr, ho, ?_⟩
    intro d hd hi he
    exact retained_eligible_diagnostic_uses_offer (records.get j) i d U hd hi he
      (wordAt j hj d hd hi he)
  · apply retained_positive_entry_has_conditional_offer_equation (records.drop b) i U
    intro r hr d hd hi he
    obtain ⟨n, hn, hget⟩ := List.getElem_of_mem hr
    have hnb : b + n < records.length := by
      have := hn
      simp only [List.length_drop] at this
      omega
    have hget' : records.get ⟨b + n, hnb⟩ = r := by
      simpa only [List.get_eq_getElem, List.getElem_drop] using hget
    rw [← hget'] at hd ⊢
    exact wordAt ⟨b + n, hnb⟩ (by dsimp only; omega) d hd hi he


/-- A successful actual filtered reception checks the very parsed UP record. -/
theorem received_success_checks_actual_parsed_up
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (started decoded : ReferenceActivePhysicalStep.Ledger rate)
    (bank : CoordinatorUpReception.UpDecoderBank p)
    (U : ReferenceCollectionPhaseHistory.UpRecord p rate)
    (hreceived : (ReferenceActivePhysicalStep.receiveUp
      (ReferenceActivePhysicalStep.prepare x) started).result = .success (decoded, bank))
    (hparsed : ReferenceCollectionPhaseHistory.filteredParsed x started = some U) :
    CoordinatorCollectionLedger.acceptUpCheck started
      (ReferenceActivePhysicalStep.upSenderIndex x) U = true := by
  have hr : CoordinatorUpReception.packDecodeResult
      (CoordinatorCollectionLedger.decodeUp started (ReferenceActivePhysicalStep.upSenderIndex x)
        (ReferenceCollectionPhaseHistory.filteredParsed x started))
      (CoordinatorUpReception.decoderBankAfter (ReferenceUpReception.receptionInputAtRow rate x.row
        (ReferenceActivePhysicalStep.upInputs (ReferenceActivePhysicalStep.prepare x) started) x.time)) =
      .success (decoded, bank) := by
    change (if CoordinatorUpReception.receptionInputCheck _ = true then _ else _) = _ at hreceived
    split at hreceived
    · exact hreceived
    · contradiction
  rw [hparsed] at hr
  by_contra hncheck
  have hfcheck : CoordinatorCollectionLedger.acceptUpCheck started
      (ReferenceActivePhysicalStep.upSenderIndex x) U = false := Bool.eq_false_iff.mpr hncheck
  unfold CoordinatorCollectionLedger.decodeUp at hr
  split at hr <;> try contradiction
  simp only [hfcheck, Bool.false_eq_true, ite_false] at hr
  split at hr <;> contradiction


/-- An actual accepted UP cannot come from an older CHOICE when the executed
receiver's offer split is old-and-rejected or the current complete DOWN. -/
theorem accepted_up_excludes_strictly_older_choice
    (r : ReferenceCompletePhysicalHistory.RoundRecord p rate) (i : Fin (p.m - 1))
    (M : OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hchoice : (ReferenceFollowerFixedReply.actualChoice r i).configuration = .ordinary state memory)
    (holder : ReferencePrelaunchFollower.acceptedStart state < M.val.sigma)
    (U : ReferenceCollectionPhaseHistory.UpRecord p rate)
    (haccepted : ReferenceCollectionPhaseHistory.AcceptedUp r.input i U)
    (hphysical : ∀ (t : ReferenceCollectionPhaseHistory.Tail r.input)
        (started : ReferenceActivePhysicalStep.Ledger rate),
      ReferenceCollectionPhaseHistory.executedTail r.input = some t →
      t.reception = some (started, ReferenceActivePhysicalStep.receiveUp
        (ReferenceActivePhysicalStep.prepare r.input) started) →
      PublicDiscreteDraws.slotDraw (r.input.row.2 r.input.time).1 = PublicDiscreteDraws.upSlot →
      ∃ offered offerMem offer,
        (r.output.preparation.followers.followers
          (ReferenceActivePhysicalStep.upSenderIndex r.input)).configuration = .ordinary offered offerMem ∧
        ActiveFollowerQueueOperation.checkedUpOffer rate.eta
          (ReferenceActivePhysicalStep.upSenderIndex r.input) r.input.row
          (r.input.state.activations (ReferenceActivePhysicalStep.upSenderIndex r.input))
          r.input.time offered = .offer offer ∧
        (CoordinatorCollectionLedger.acceptUpCheck started
          (ReferenceActivePhysicalStep.upSenderIndex r.input) offer = false ∨
          offered.lastDown = some M)) : False := by
  obtain ⟨sender, current, currentMem, hs, hi, hc, _, hcheckA, _, _, _, _, _, _, _, hslot⟩ :=
    ReferenceAcceptedUpFollowerHistory.acceptedUp_current_choice haccepted
  rcases haccepted with ⟨t, recording, started, decoded, bank, ht, hrecording,
    hstarted, hreceived, hparsed, _⟩
  have htrec : t.reception = some (started,
      ReferenceActivePhysicalStep.receiveUp (ReferenceActivePhysicalStep.prepare r.input) started) := by
    simp only [ReferenceCollectionPhaseHistory.Tail.reception, hrecording, hstarted]
  obtain ⟨offered, offerMem, offer, hcOffer, hcheck, horigin⟩ := hphysical t started ht htrec hslot
  have hcActual : (ReferenceFollowerFixedReply.actualChoice r i).configuration =
      .ordinary current currentMem := by
    rw [hs, ← hi] at hc
    unfold ReferenceFollowerFixedReply.actualChoice
    rw [r.output_eq]
    exact hc
  obtain ⟨rfl, rfl⟩ := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
    (hchoice.symm.trans hcActual)
  have hcheckA' : ActiveFollowerQueueOperation.checkedUpOffer rate.eta i r.input.row
      (r.input.state.activations i) r.input.time state = .offer U := by
    rw [hs, ← hi] at hcheckA
    have hal := (ReferenceActivePhysicalStep.prepare r.input).follower_alignment i
    simpa only [hal.1, hal.2.1, hal.2.2.1, hal.2.2.2] using hcheckA
  rw [← hi] at hcOffer hcheck horigin
  obtain ⟨rfl, rfl⟩ := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
    (hchoice.symm.trans hcOffer)
  have hsame : offer = U := ActiveFollowerQueueOperation.UpOfferResult.offer.inj
    (hcheck.symm.trans hcheckA')
  rcases horigin with hold | hcur
  · have htrue := received_success_checks_actual_parsed_up r.input started decoded bank U hreceived hparsed
    rw [← hi] at htrue
    rw [hsame] at hold
    exact Bool.noConfusion (hold.symm.trans htrue)
  · have hstart : ReferencePrelaunchFollower.acceptedStart state = M.val.sigma := by
      simp only [ReferencePrelaunchFollower.acceptedStart, hcur]
    exact (ne_of_lt holder) hstart

/-- The actual first replacement cut: inherited current DOWN, its least new
acceptance, or absence through the endpoint. Present cases carry one fixed UP
offer and all eligible saved equations, including equations on failing rounds. -/
theorem complete_first_replacement_collection_up_offer_cut
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
    let s := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
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
        let X := (R.drop v).take (1 + tail.length)
        let C := X.filterMap (ReferenceLaterLiveNumericalReadout.laterLiveReadout s)
        let L := X.length
        C.length = L ∧ X = birth :: tail ∧
        match R[c]? with
        | none => True
        | some cut =>
          match cut.output.preparation.coordinator with
          | .live _ _ _ (.cutoffChosen _ _ _ _ _ _ _ _ _ _) =>
            let u := cut.input.time.val + 1
            let W := (R.drop (c + 1)).takeWhile
              (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
            let K := cut :: W
            let E := fun j => ReferenceCollectionSegmentExtraction.endpointState
              cut.output.next (W.take j)
            let Z := fun j => ReferenceCollectionSegmentExtraction.endpointState
              cut.input.state (K.take j)
            let M := fun i => payload.downRecord i
            (∀ q : Fin K.length, (K.get q).input.time.val + 1 = u + q.val) ∧
            (Z 0 = cut.input.state ∧
              (∀ j : ℕ, j ≤ W.length → Z (j + 1) = E j) ∧
              (∀ q : Fin K.length, (K.get q).input.state = Z q.val ∧
                (K.get q).output.next = Z (q.val + 1))) ∧
            (∀ i : Fin (p.m - 1),
              (∃ (b : ℕ) (anchor : ReferencePrelaunchFollower.State p rate.eta)
                  (memory : ActiveFollowerLifecycle.LocalMemory p),
                ((b = 0 ∧
                  (cut.output.preparation.followers.followers i).configuration =
                    .ordinary anchor memory ∧
                  ∃! x : Fin X.length,
                    ReferenceAcceptedUpFollowerHistory.RetainedDown (X.get x) i (M i)) ∨
                 (∃ q : Fin K.length, b = q.val + 1 ∧
                  ReferenceAcceptedUpFollowerHistory.RetainedDown (K.get q) i (M i) ∧
                  (∀ j : Fin K.length, j.val < q.val →
                    ¬ ReferenceAcceptedUpFollowerHistory.RetainedDown (K.get j) i (M i)) ∧
                  (K.get q).output.next.followers i = .ordinary anchor memory ∧
                  (Z (q.val + 1)).followers i = .ordinary anchor memory ∧
                  ∀ state mem, (cut.output.preparation.followers.followers i).configuration =
                    .ordinary state mem → state.lastDown ≠ some (M i))) ∧
                b ≤ K.length ∧ anchor.status = .unoccupied ∧
                ActiveFollowerLifecycle.localStateDomainValid anchor ∧
                anchor.lastDown = some (M i) ∧
                (∃ last lastMemory, (E W.length).followers i = .ordinary last lastMemory ∧
                  last.status = .unoccupied ∧ last.lastDown = some (M i) ∧
                  ReferenceFollowerReplyChronology.reply last =
                    ReferenceFollowerReplyChronology.reply anchor) ∧
                ∃ U : OrdinaryMessageCodec.UpRecord (ReferencePrelaunchFollower.codecParams p rate.eta),
                U.val = ActiveFollowerQueueOperation.upOfferFields anchor ∧
                U.val.sigma = (M i).val.sigma ∧ 0 < U.val.sigma ∧
                (∀ j : Fin K.length, b ≤ j.val → ∃ state memory,
                  (ReferenceFollowerFixedReply.actualChoice (K.get j) i).configuration =
                    .ordinary state memory ∧ state.status = .unoccupied ∧
                  state.lastDown = some (M i) ∧
                  ReferenceFollowerReplyChronology.reply state = ReferenceFollowerReplyChronology.reply anchor ∧
                  (ReferenceActivePhysicalStep.upSenderIndex (K.get j).input = i →
                    PublicDiscreteDraws.slotDraw ((K.get j).input.row.2
                      (K.get j).input.time).1 = PublicDiscreteDraws.upSlot →
                    ActiveFollowerQueueOperation.checkedUpOffer rate.eta i (K.get j).input.row
                      ((K.get j).input.state.activations i) (K.get j).input.time state = .offer U ∧
                    ReferenceActivePhysicalStep.upExpected (ReferenceActivePhysicalStep.prepare
                      (K.get j).input) = some (ActiveFollowerArmChoice.offeredUpWord rate.eta U)) ∧
                  (∀ d : ReferenceActivePhysicalStep.UpDiagnostic p rate,
                    (K.get j).output.coordinator.up = some d → d.input.selectedFollower = i →
                    AffineBatchDecoder.eligible (CoordinatorUpReception.roundInput d.input) →
                    d.input.time = (K.get j).input.time ∧ d.input.selectedFollower = i ∧
                    d.input.slot = PublicDiscreteDraws.slotDraw
                      ((K.get j).input.row.2 (K.get j).input.time).1 ∧
                    d.input.affineSample = ((K.get j).input.row.2 (K.get j).input.time).2 (1, i) ∧
                    AffineChannelLaw.affineHash d.input.affineSample
                      (ActiveFollowerArmChoice.offeredUpWord rate.eta U) = 1)) ∧
                (∀ entry ∈ ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries (K.drop b) i,
                  ∃ r ∈ K.drop b, ∃ d : ReferenceActivePhysicalStep.UpDiagnostic p rate,
                    r.output.coordinator.up = some d ∧ d.input.selectedFollower = i ∧
                    AffineBatchDecoder.eligible (CoordinatorUpReception.roundInput d.input) ∧
                    entry.time = r.input.time ∧
                    d.input.slot = PublicDiscreteDraws.slotDraw (r.input.row.2 r.input.time).1 ∧
                    entry.sample = d.input.affineSample ∧
                    d.input.affineSample = (r.input.row.2 r.input.time).2 (1, i) ∧
                    AffineChannelLaw.affineHash entry.sample
                      (ActiveFollowerArmChoice.offeredUpWord rate.eta U) = 1)) ∨
              ((∀ j : Fin K.length, ∃ state memory,
                  (ReferenceFollowerFixedReply.actualChoice (K.get j) i).configuration =
                    .ordinary state memory ∧ state.status = .unoccupied ∧
                  state.lastDown ≠ some (M i) ∧
                  ReferencePrelaunchFollower.acceptedStart state < (M i).val.sigma ∧
                  ((state.lastDown = none ∧ state.S = 0 ∧ state.delta = 0 ∧ state.backlog = 0) ∨
                    ∃ old, state.lastDown = some old ∧ 0 < old.val.sigma ∧
                      old.val.sigma < (M i).val.sigma)) ∧
               (∃ last memory, (E W.length).followers i = .ordinary last memory ∧
                  last.status = .unoccupied ∧ last.lastDown ≠ some (M i) ∧
                  ReferencePrelaunchFollower.acceptedStart last < (M i).val.sigma ∧
                  ((last.lastDown = none ∧ last.S = 0 ∧ last.delta = 0 ∧ last.backlog = 0) ∨
                    ∃ old, last.lastDown = some old ∧ 0 < old.val.sigma ∧
                      old.val.sigma < (M i).val.sigma)) ∧
               (∀ q : Fin K.length,
                 ¬ ReferenceAcceptedUpFollowerHistory.RetainedDown (K.get q) i (M i)) ∧
               (∀ q : Fin K.length, ∀ old,
                 ReferenceAcceptedUpFollowerHistory.RetainedDown (K.get q) i old →
                 old.val.sigma < (M i).val.sigma) ∧
               R[c + 1 + W.length]? = none)) ∧
            match R[c + 1 + W.length]? with
            | none => c + 1 + W.length = R.length ∧
                ReferenceCompletePhysicalHistory.completeTerminalState
                  rate source rewards C_star C_h = some (E W.length)
            | some next => next.input.state = E W.length ∧
                ReferenceCollectionPhaseHistory.laterChosen next.input = true ∧
                ∃ ledger saved,
                  (E W.length).coordinator = .collection payload ledger saved ∧
                  next.input.state.coordinator = .collection payload ledger saved ∧
                  ledger.pending = ∅ ∧
                  ∀ i : Fin (p.m - 1), ∃ r ∈ K,
                    ∃ U, ReferenceCollectionPhaseHistory.AcceptedUp r.input i U
          | _ => True
      | _ => True := by
  classical
  have hR := ReferenceFirstReplacementCollectionUpReceiverProvenance.complete_first_replacement_collection_up_receiver_provenance
    rate source rewards C_star C_h
  have hF := ReferenceFirstReplacementCollectionPrefix.complete_first_replacement_collection_follower_prefix
    rate source rewards C_star C_h
  have hB := ReferenceFirstReplacementCutoffPreparedBoundary.complete_first_replacement_cutoff_follower_boundary
    rate source rewards C_star C_h
  have hK := ReferenceFirstReplacementCutoffCurrentNumericalOutputs.complete_first_replacement_cutoff_current_numerical_outputs
    rate source rewards C_star C_h
  dsimp only at hR hF hB hK ⊢
  set R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
  set s := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
  set w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
  set v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
  set tail := ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v
  set c := v + 1 + tail.length
  cases hb : R[v]? with
  | none => trivial
  | some birth =>
    simp only [hb] at hR hF hB hK ⊢
    cases hbirth : birth.output.preparation.coordinator with
    | first _ => trivial
    | live _ _ _ _ => trivial
    | dagger => trivial
    | invalidCollectionCutoff => trivial
    | collection _ _ _ _ outcome =>
      simp only [hbirth] at hR hF hB hK ⊢
      cases outcome <;> try trivial
      rename_i core consistent started hstart instruction hinstruction output hconsistent
        clockData installed selectedBirth
      dsimp only [ReferenceActivePhysicalStep.collectionInput] at hR hF hB hK ⊢
      let payload : ReferenceActivePhysicalStep.Payload rate := installed.registers.payload
      let X := (R.drop v).take (1 + tail.length)
      rcases hR with ⟨hCL, hX, hR⟩
      refine ⟨hCL, hX, ?_⟩
      cases hc : R[c]? with
      | none => trivial
      | some cut =>
        simp only [tail, c, hc] at hR hF hB hK ⊢
        rcases hB with ⟨_, hB⟩
        rcases hK with ⟨_, _, _, _, hK⟩
        cases hcut : cut.output.preparation.coordinator with
        | first _ => trivial
        | collection _ _ _ _ _ => trivial
        | dagger => trivial
        | invalidCollectionCutoff => trivial
        | live registers owned base outcome =>
          simp only [hcut] at hR hF hB hK ⊢
          cases outcome <;> try trivial
          rename_i dispatched hs ledger hi hledger hdata hclock hpending hnone selectedCut
          dsimp only at hR hF hB hK ⊢
          let W := (R.drop (c + 1)).takeWhile
            (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
          let K := cut :: W
          let E := fun j => ReferenceCollectionSegmentExtraction.endpointState
            cut.output.next (W.take j)
          let Z := fun j => ReferenceCollectionSegmentExtraction.endpointState
            cut.input.state (K.take j)
          let M := fun i => payload.downRecord i
          rcases hF with ⟨_, _, hgeometry, _, _, _, hfollowers⟩
          rcases hB with ⟨_, _, _, _, _, _, _, _, _, _, _,
            selectedB, _, _, _, _, hboundary⟩
          rcases hK with ⟨_, _, _, _, _, _, _, _, _, _, _,
            selectedK, _, _, _, _, hcutFollowers⟩
          rcases hR with ⟨_, hreceptions, hnext⟩
          have hlinks : ∀ j : Fin W.length,
              (W.get j).input.state = E j.val ∧ E (j.val + 1) = (W.get j).output.next ∧
              (W.get j).input.time.val = cut.input.time.val + 1 + j.val := by
            intro j
            rcases hfollowers ⟨0, by have := p.two_le_m; omega⟩ with
              ⟨_, _, old, initial, memory, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hsteps, _⟩
            rcases hsteps j.val j.isLt with ⟨hget, state, logged, post, _⟩
            have hgeo := hgeometry j.val (Nat.le_of_lt j.isLt)
            rw [hget] at hgeo
            exact ⟨hgeo.1, (hgeo.2.2.2.2.2.1 j.isLt).2, hgeo.2.1⟩
          have hadjacent : ∀ j : Fin W.length,
              (W.get j).input.state = E j.val ∧ E (j.val + 1) = (W.get j).output.next :=
            fun j => ⟨(hlinks j).1, (hlinks j).2.1⟩
          have hcalendar : ∀ q : Fin K.length,
              (K.get q).input.time.val + 1 = cut.input.time.val + 1 + q.val := by
            intro ⟨q, hq⟩
            cases q with
            | zero => rfl
            | succ j =>
              have hj : j < W.length := Nat.lt_of_succ_lt_succ hq
              change (W.get ⟨j, hj⟩).input.time.val + 1 = cut.input.time.val + 1 + (j + 1)
              exact (congrArg (· + 1) (hlinks ⟨j, hj⟩).2.2).trans (Nat.add_assoc _ _ _)
          have halign := actual_collection_endpoint_alignment cut W hadjacent
          have hZrecord : ∀ q : Fin K.length, (K.get q).input.state = Z q.val ∧
              (K.get q).output.next = Z (q.val + 1) := by
            intro ⟨q, hq⟩
            cases q with
            | zero => exact ⟨halign.1.symm, (halign.2.1 0 (Nat.zero_le _)).trans rfl |>.symm⟩
            | succ j =>
              have hj : j < W.length := by have : j + 1 < W.length + 1 := hq; omega
              have ha := halign.2.2 ⟨j, hj⟩
              exact ⟨ha.1, ha.2.symm⟩
          have hconnectedW : ∀ j : ℕ, j ≤ W.length →
              ReferenceActivePhysicalHorizon.Connected cut.output.next (W.take j) (E j) := by
            intro j hj
            induction j with
            | zero => rfl
            | succ j ih =>
              have hlt : j < W.length := by omega
              have ha := hadjacent ⟨j, hlt⟩
              rw [ha.2, List.take_succ_eq_append_getElem hlt]
              exact ReferenceActivePhysicalHorizon.Connected.append_one _ _ (ih (by omega)) ha.1
          have hchain : ReferenceActivePhysicalHorizon.Connected cut.input.state K (E W.length) := by
            exact ⟨rfl, by simpa only [List.take_length] using hconnectedW W.length le_rfl⟩
          obtain ⟨hci, hce⟩ := List.getElem?_eq_some_iff.mp hc
          obtain ⟨hbi, hbe⟩ := List.getElem?_eq_some_iff.mp hb
          obtain ⟨hcLaunch, _, _⟩ := ReferenceLaterLiveNumericalReadout.source_record_prefix
            rate rewards C_star C_h source ⟨c, hci⟩
          have hfull := ReferenceCompletePhysicalHistory.completeSuffix_connected_on_launch
            rate source rewards C_star C_h
            (ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hcLaunch)
            (ReferenceFirstLaunchNumericalCell.correctedLaunch_eq_some_launchState
              rate source rewards C_star C_h hcLaunch)
          have hprefix := ReferenceFollowerReplyChronology.connected_take_to_input hfull c hci
          rw [hce] at hprefix
          have hvc : v < (R.take c).length := by
            simp only [List.length_take]; dsimp only [c]; omega
          have hXchain := ReferenceFollowerReplyChronology.connected_drop_from_input hprefix v hvc
          have hXeq : (R.take c).drop v = X := by
            dsimp only [X, c]
            rw [List.take_drop]
            congr 2
            omega
          rw [hXeq] at hXchain
          refine ⟨hcalendar, ⟨halign.1, halign.2.1, hZrecord⟩, ?_, hnext⟩
          intro i
          rcases hfollowers i with
            ⟨_, _, oldF, initial, memoryF, hinputF, _, _, _, _, _, _, _, _, _, _, _, _, hend, hsteps, _⟩
          rcases hboundary i with
            ⟨old, memory, hinput, _, _, hzeroOld, hold, _, _, _, hchoice,
              hchoiceDomain, _⟩
          rcases hcutFollowers i with
            ⟨oldK, memoryK, hinputK, hchoiceK, _, logged, post, hlogging, hlogLast,
              hlogS, hlogDelta, hlogBacklog, hlogFailure, hlogStatus, hconsume,
              hpostStatus, hpostFailure, hrecord, hdownInput, hdown, hfinish,
              hcutOutput, _, hchoiceStart, hinPrefix, _⟩
          obtain ⟨rfl, rfl⟩ := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
            (hinput.symm.trans hinputK)
          let choice : ReferencePrelaunchFollower.State p rate.eta := { old with status := .unoccupied }
          have hchoice' : (ReferenceFollowerFixedReply.actualChoice cut i).configuration =
              .ordinary choice memory := hchoice
          have hchoiceOrigin : ReferencePrelaunchFollower.acceptedStart choice < (M i).val.sigma ∨
              choice.lastDown = some (M i) := by
            by_cases hu : old.status = .unoccupied
            · exact Or.inl (hold hu)
            · exact Or.inr (hinPrefix hu).1
          have hchoices : ∀ j : Fin K.length, ∃ state mem,
              (ReferenceFollowerFixedReply.actualChoice (K.get j) i).configuration = .ordinary state mem ∧
              state.status = .unoccupied ∧ ActiveFollowerLifecycle.localStateDomainValid state ∧
              (state.lastDown = none → state.S = 0 ∧ state.delta = 0 ∧ state.backlog = 0) ∧
              (ReferencePrelaunchFollower.acceptedStart state < (M i).val.sigma ∨
                state.lastDown = some (M i)) := by
            intro ⟨j, hj⟩
            cases j with
            | zero => exact ⟨choice, memory, hchoice', rfl, hchoiceDomain, hzeroOld, hchoiceOrigin⟩
            | succ j =>
              have hjW : j < W.length := by have : j + 1 < W.length + 1 := hj; omega
              rcases hsteps j hjW with ⟨_, state, logged, post, hin, hu, hd, _, _, _, hz,
                ho, _, _, _, hp, _⟩
              exact ⟨state, memoryF, hp, hu, hd, hz, ho⟩
          obtain ⟨last, hlast, hlastStatus, hlastDomain, _, _, _, hlastZero, hlastOrigin, _⟩ :=
            hend W.length (Nat.le_refl _)
          change (E W.length).followers i = .ordinary last memoryF at hlast
          change ReferencePrelaunchFollower.acceptedStart last < (M i).val.sigma ∨
            last.lastDown = some (M i) at hlastOrigin
          have hlastBound (j : Fin K.length) (state : ReferencePrelaunchFollower.State p rate.eta)
              (mem : ActiveFollowerLifecycle.LocalMemory p)
              (hj : (ReferenceFollowerFixedReply.actualChoice (K.get j) i).configuration =
                .ordinary state mem) :=
            connected_choice_endpoint_chronology hchain i j state last mem memoryF hj hlast
          have hnewBound (q : Fin K.length)
              (hq : ReferenceAcceptedUpFollowerHistory.RetainedDown (K.get q) i (M i)) :
              (M i).val.sigma ≤ ReferencePrelaunchFollower.acceptedStart last := by
            obtain ⟨next, mem, hn, hb⟩ := ReferenceFollowerReplyChronology.connected_output_chronology
              hchain i last memoryF hlast q.val q.isLt
            obtain ⟨_, _, _, _, hs⟩ := ReferenceFollowerReplyChronology.record_appliedDown_strict
              (K.get q) i (M i).val.sigma
              (ReferenceAcceptedUpFollowerHistory.retainedDown_appliedDown hq) next mem hn
            omega
          have hreplySuffix (b : ℕ) (anchor : ReferencePrelaunchFollower.State p rate.eta)
              (hfinalCurrent : last.lastDown = some (M i))
              (hfinalReply : ReferenceFollowerReplyChronology.reply last =
                ReferenceFollowerReplyChronology.reply anchor)
              (hlower : ∀ j : Fin K.length, b ≤ j.val →
                ∀ state mem, (ReferenceFollowerFixedReply.actualChoice (K.get j) i).configuration =
                  .ordinary state mem → (M i).val.sigma ≤ ReferencePrelaunchFollower.acceptedStart state) :
              ∀ j : Fin K.length, b ≤ j.val → ∃ state mem,
                (ReferenceFollowerFixedReply.actualChoice (K.get j) i).configuration = .ordinary state mem ∧
                state.status = .unoccupied ∧ ActiveFollowerLifecycle.localStateDomainValid state ∧
                state.lastDown = some (M i) ∧
                ReferenceFollowerReplyChronology.reply state = ReferenceFollowerReplyChronology.reply anchor := by
            intro j hj
            obtain ⟨state, mem, hcj, hu, hd, _, ho⟩ := hchoices j
            have hb := hlower j hj state mem hcj
            have hcjCurrent : state.lastDown = some (M i) := ho.resolve_left (not_lt_of_ge hb)
            have hs : ReferencePrelaunchFollower.acceptedStart state =
                ReferencePrelaunchFollower.acceptedStart last := by
              simp only [ReferencePrelaunchFollower.acceptedStart, hcjCurrent, hfinalCurrent]
            have hr := (hlastBound j state mem hcj).2 hu hs
            exact ⟨state, mem, hcj, hu, hd, hcjCurrent, hr.2.symm.trans hfinalReply⟩
          by_cases hcurrent : choice.lastDown = some (M i)
          · left
            have hstart : ReferencePrelaunchFollower.acceptedStart choice = (M i).val.sigma := by
              simp only [ReferencePrelaunchFollower.acceptedStart, hcurrent]
            have hchron := hlastBound ⟨0, by simp [K]⟩ choice memory hchoice'
            have hfinalCurrent := hlastOrigin.resolve_left (not_lt_of_ge (hstart ▸ hchron.1))
            have hfinalStart : ReferencePrelaunchFollower.acceptedStart last = (M i).val.sigma := by
              simp only [ReferencePrelaunchFollower.acceptedStart, hfinalCurrent]
            have hfinalReply := (hchron.2 rfl (hstart.trans hfinalStart.symm)).2
            have horigin := inherited_current_cut_choice_has_unique_prefix_origin hXchain i (M i)
              old memory choice hinput hcurrent hchoiceStart (fun hu => (hinPrefix hu).2.2.2.2.2.2.2.2.2.2.2.2)
            refine ⟨0, choice, memory, Or.inl ⟨rfl, hchoice, horigin⟩, Nat.zero_le _,
              rfl, hchoiceDomain, hcurrent, ⟨last, memoryF, hlast, hlastStatus, hfinalCurrent, hfinalReply⟩, ?_⟩
            apply fixed_offer_on_actual_reply_suffix K i 0 choice (M i) hchoiceDomain hcurrent
            apply hreplySuffix 0 choice hfinalCurrent hfinalReply
            intro j _ state mem hj
            have hm := (ReferenceFollowerReplyChronology.connected_choice_chronology hchain i 0 j.val
              (by simp [K]) j.isLt (Nat.zero_le _) choice state memory mem hchoice' hj).1
            omega
          · by_cases hevent : ∃ q : Fin K.length,
                ReferenceAcceptedUpFollowerHistory.RetainedDown (K.get q) i (M i)
            · left
              obtain ⟨q, hq, hminimal⟩ := least_actual_retained_down_event K i (M i) hevent
              have hqa := hZrecord q
              have hqW : q.val ≤ W.length := by
                have h := q.isLt
                change q.val < W.length + 1 at h
                omega
              have hqE : (K.get q).output.next = E q.val :=
                hqa.2.trans (halign.2.1 q.val hqW)
              obtain ⟨anchor, haE, hu, hd, _, _, _, hz, ho, _⟩ := hend q.val hqW
              change (E q.val).followers i = .ordinary anchor memoryF at haE
              change ReferencePrelaunchFollower.acceptedStart anchor < (M i).val.sigma ∨
                anchor.lastDown = some (M i) at ho
              have ha : (K.get q).output.next.followers i = .ordinary anchor memoryF := by
                rw [hqE]
                exact haE
              obtain ⟨_, _, _, _, hs⟩ := ReferenceFollowerReplyChronology.record_appliedDown_strict
                (K.get q) i (M i).val.sigma
                (ReferenceAcceptedUpFollowerHistory.retainedDown_appliedDown hq) anchor memoryF ha
              have hacurrent := ho.resolve_left (by rw [hs]; exact lt_irrefl _)
              have hfinalCurrent := hlastOrigin.resolve_left (not_lt_of_ge (hnewBound q hq))
              have htail := ReferenceFollowerReplyChronology.connected_drop_from_output hchain q.val q.isLt
              obtain ⟨first, firstMem, hf, _, hfreeze, _⟩ :=
                ReferenceFollowerReplyChronology.connected_ordinary_chronology htail i last memoryF hlast
              obtain ⟨rfl, rfl⟩ := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj (ha.symm.trans hf)
              have hfinalReply := (hfreeze hu (by
                simp only [ReferencePrelaunchFollower.acceptedStart, hacurrent, hfinalCurrent])).2
              refine ⟨q.val + 1, anchor, memoryF, Or.inr ⟨q, rfl, hq, hminimal, ha,
                by change (Z (q.val + 1)).followers i = _; rw [← hqa.2]; exact ha,
                ?_⟩, Nat.succ_le_of_lt q.isLt, hu, hd, hacurrent,
                ⟨last, memoryF, hlast, hlastStatus, hfinalCurrent, hfinalReply⟩, ?_⟩
              · intro state mem hcj
                have he := (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
                  (hchoice.symm.trans hcj)).1
                exact he ▸ hcurrent
              · apply fixed_offer_on_actual_reply_suffix K i (q.val + 1) anchor (M i) hd hacurrent
                apply hreplySuffix (q.val + 1) anchor hfinalCurrent hfinalReply
                intro j hj state mem hcj
                obtain ⟨before, beforeMem, hin, hr, _⟩ :=
                  ReferenceFollowerReplyChronology.record_input_to_choice (K.get j) i state mem hcj
                have hprefix := ReferenceFollowerReplyChronology.connected_take_to_input hchain j.val j.isLt
                obtain ⟨next, nextMem, hn, hb⟩ := ReferenceFollowerReplyChronology.connected_output_chronology
                  hprefix i before beforeMem hin q.val (by simp only [List.length_take]; omega)
                rw [List.getElem_take] at hn
                obtain ⟨_, _, _, _, hsig⟩ := ReferenceFollowerReplyChronology.record_appliedDown_strict
                  (K.get q) i (M i).val.sigma
                  (ReferenceAcceptedUpFollowerHistory.retainedDown_appliedDown hq) next nextMem hn
                have hsr := ReferenceFollowerReplyChronology.acceptedStart_eq_of_reply_eq hr
                omega
            · right
              have hno : ∀ q : Fin K.length,
                  ¬ ReferenceAcceptedUpFollowerHistory.RetainedDown (K.get q) i (M i) := by
                intro q hq; exact hevent ⟨q, hq⟩
              have hnotInput : old.lastDown ≠ some (M i) := hcurrent
              have hnotLast : last.lastDown ≠ some (M i) := by
                intro hl
                rcases connected_endpoint_current_down_has_actual_origin hchain i old memory last memoryF
                    hinput hlast (M i) hl with hin | ⟨r, hr, he⟩
                · exact hnotInput hin
                · obtain ⟨j, hj, hget⟩ := List.getElem_of_mem hr
                  apply hno ⟨j, hj⟩
                  simpa only [List.get_eq_getElem, hget] using he
              have hlastOlder := hlastOrigin.resolve_right hnotLast
              have splitOld (state : ReferencePrelaunchFollower.State p rate.eta)
                  (hz : state.lastDown = none → state.S = 0 ∧ state.delta = 0 ∧ state.backlog = 0)
                  (ho : ReferencePrelaunchFollower.acceptedStart state < (M i).val.sigma) :
                  (state.lastDown = none ∧ state.S = 0 ∧ state.delta = 0 ∧ state.backlog = 0) ∨
                  ∃ old, state.lastDown = some old ∧ 0 < old.val.sigma ∧ old.val.sigma < (M i).val.sigma := by
                cases hd : state.lastDown with
                | none => exact Or.inl ⟨rfl, hz hd⟩
                | some old => exact Or.inr ⟨old, rfl, by have := old.property.1; omega,
                    by simpa only [ReferencePrelaunchFollower.acceptedStart, hd] using ho⟩
              have hchoicesOlder : ∀ j : Fin K.length, ∃ state mem,
                  (ReferenceFollowerFixedReply.actualChoice (K.get j) i).configuration = .ordinary state mem ∧
                  state.status = .unoccupied ∧ state.lastDown ≠ some (M i) ∧
                  ReferencePrelaunchFollower.acceptedStart state < (M i).val.sigma ∧
                  ((state.lastDown = none ∧ state.S = 0 ∧ state.delta = 0 ∧ state.backlog = 0) ∨
                    ∃ old, state.lastDown = some old ∧ 0 < old.val.sigma ∧ old.val.sigma < (M i).val.sigma) := by
                intro j
                obtain ⟨state, mem, hcj, hu, _, hz, _⟩ := hchoices j
                have hb := (hlastBound j state mem hcj).1
                have ho : ReferencePrelaunchFollower.acceptedStart state < (M i).val.sigma := by omega
                have hn : state.lastDown ≠ some (M i) := by
                  intro hc; have hs : ReferencePrelaunchFollower.acceptedStart state = (M i).val.sigma := by
                    simp only [ReferencePrelaunchFollower.acceptedStart, hc]
                  omega
                exact ⟨state, mem, hcj, hu, hn, ho, splitOld state hz ho⟩
              refine ⟨hchoicesOlder, ⟨last, memoryF, hlast, hlastStatus, hnotLast, hlastOlder,
                splitOld last hlastZero hlastOlder⟩, hno, ?_, ?_⟩
              · intro q old hq
                obtain ⟨next, mem, hn, hb⟩ := ReferenceFollowerReplyChronology.connected_output_chronology
                  hchain i last memoryF hlast q.val q.isLt
                obtain ⟨_, _, _, _, hs⟩ := ReferenceFollowerReplyChronology.record_appliedDown_strict
                  (K.get q) i old.val.sigma
                  (ReferenceAcceptedUpFollowerHistory.retainedDown_appliedDown hq) next mem hn
                exact hs ▸ hb.trans_lt hlastOlder
              · cases hn : R[c + 1 + W.length]? with
                | none => rfl
                | some next =>
                  exfalso
                  rw [hn] at hnext
                  obtain ⟨_, _, led, saved, _, _, _, hall⟩ := hnext
                  obtain ⟨r, hr, U, haccepted⟩ := hall i
                  obtain ⟨j, hj, hjr⟩ := List.getElem_of_mem hr
                  have hget : K.get ⟨j, hj⟩ = r := hjr
                  have hacceptedAt : ReferenceCollectionPhaseHistory.AcceptedUp
                      (K.get ⟨j, hj⟩).input i U := by
                    rw [hget]
                    exact haccepted
                  have hsender : i = ReferenceActivePhysicalStep.upSenderIndex (K.get ⟨j, hj⟩).input := by
                    obtain ⟨_, _, _, _, _, _, _, _, _, _, hi⟩ := hacceptedAt
                    exact hi
                  obtain ⟨state, mem, hcj, _, _, ho, _⟩ := hchoicesOlder ⟨j, hj⟩
                  apply accepted_up_excludes_strictly_older_choice (K.get ⟨j, hj⟩) i (M i)
                    state mem hcj ho U hacceptedAt
                  intro t started ht htrec hslot
                  dsimp only [K, W, c, tail] at ht htrec hslot hsender ⊢
                  have hrec := hreceptions ⟨j, hj⟩
                  rw [ht] at hrec
                  dsimp only at hrec
                  rw [htrec] at hrec
                  dsimp only at hrec
                  obtain ⟨offered, offerMem, offer, hcOffer, hcheck, _, _, horigin⟩ :=
                    hrec.2.2.2.2.2.1 hslot
                  refine ⟨offered, offerMem, offer, hcOffer, hcheck, ?_⟩
                  rcases horigin with hold | hcur
                  · exact Or.inl hold.2.2
                  · right
                    rw [hsender]
                    exact hcur.1

end Bandits.Support.ReferenceFirstReplacementCollectionUpOfferCut

end
