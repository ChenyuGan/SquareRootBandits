/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionFormationOrigin

import Lean.Elab.Tactic.Omega

/-!
# Actual first-collection formed-reply state interval

Sources: `sources/zip4/manuscript/06_interruptions.tex:246-296,327-348,459-490`,
`sources/zip4/manuscript/05_binary_transport.tex:20-53,70-124`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-79,92-108`.

This producer extends the exact initialized formation-origin result. Its
formed branch retains the same dispatch, cutoff registers, accepted-DOWN
diagnostic, and clipped formation coordinate. Every interval point is an
actual CHOICE configuration with its actual incoming PREPARE state and
pending membership. No offer, receiver, bank, service-law, or regret claim is
made here.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions
open ReferencePrelaunchFollower
open ReferenceFollowerReplyChronology
open ReferenceActivePhysicalHorizon
open DeclaredFollowerLocalRound
open ReferenceAcceptedUpFollowerHistory

namespace Bandits.Support.ReferenceFirstCollectionFormedReplyStateInterval

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

/-- Internal ledger nesting uses the actual cell's pending recurrence. It permits
acceptance after the current CHOICE and compares the resulting FINISH ledgers. -/
private theorem initialized_stream_pending_predecessor
    {source : BootstrapPrivateRoundStreams.SourceInput p}
    {rewards : ActualInitializationPhysicalStep.GridRewardTable p}
    {C_star C_h : ℝ} {count : ℕ} {hcross hspan hshort}
    (out : ReferenceFirstCollectionReadyStream.ActualInitializedStreamOutput
      (rate := rate) source rewards C_star C_h count hcross hspan hshort)
    (q : ℕ) (hq : 1 < q) (hqell : q < out.ell) :
    (out.ledgers ⟨q - 1, by omega⟩).pending ⊆
      (out.ledgers ⟨q - 2, by omega⟩).pending := by
  let n : Fin out.ell := ⟨q - 1, by omega⟩
  have hnpos : 0 < n.val := by dsimp [n]; omega
  obtain ⟨j, r, incoming, cell, _hj, _hr, hservice, hincoming⟩ :=
    out.cell_at n hnpos
  intro i hi
  have hmember : i ∈ cell.serviceLedger.pending := by
    simpa only [hservice] using hi
  rw [ReferenceFirstCollectionReadyStream.cell_pending_recurrence cell] at hmember
  have hsubset :
      ReferenceCollectionPhaseHistory.eraseEvent incoming.pending
        (ReferenceCollectionPhaseHistory.acceptedLabel r.input) ⊆ incoming.pending := by
    cases he : ReferenceCollectionPhaseHistory.acceptedLabel r.input with
    | none => simp [ReferenceCollectionPhaseHistory.eraseEvent]
    | some label => exact Finset.erase_subset label incoming.pending
  have hmember' := hsubset hmember
  simpa [hincoming, n, Nat.sub_sub] using hmember'

private theorem initialized_stream_pending_suffix_subset
    {source : BootstrapPrivateRoundStreams.SourceInput p}
    {rewards : ActualInitializationPhysicalStep.GridRewardTable p}
    {C_star C_h : ℝ} {count : ℕ} {hcross hspan hshort}
    (out : ReferenceFirstCollectionReadyStream.ActualInitializedStreamOutput
      (rate := rate) source rewards C_star C_h count hcross hspan hshort)
    (first last : ℕ) (hfirst : 1 ≤ first) (hle : first ≤ last)
    (hlast : last < out.ell) :
    (out.ledgers ⟨last - 1, by omega⟩).pending ⊆
      (out.ledgers ⟨first - 1, by omega⟩).pending := by
  induction last generalizing first with
  | zero => omega
  | succ q ih =>
      by_cases hsame : first = q + 1
      · subst first
        exact Finset.Subset.rfl
      · have hfirstq : first ≤ q := by omega
        have hprev := initialized_stream_pending_predecessor out (q + 1)
          (by omega) (by omega)
        have hrest := ih first hfirst hfirstq (by omega)
        have hprev' :
            (out.ledgers ⟨q, by omega⟩).pending ⊆
              (out.ledgers ⟨q - 1, by omega⟩).pending := by
          simpa [Nat.succ_eq_add_one] using hprev
        have hrest' :
            (out.ledgers ⟨q - 1, by omega⟩).pending ⊆
              (out.ledgers ⟨first - 1, by omega⟩).pending := by
          simpa [Nat.succ_eq_add_one] using hrest
        exact Finset.Subset.trans hprev' hrest'

/-- An actual retained acceptance bounds the accepted start at a later ordinary
input. Connected chronology produces the intervening ordinary configurations;
the caller supplies only the indicated endpoint and retained diagnostic. -/
private theorem retained_down_start_le_of_later_input
    {initial final : ReferenceActivePhysicalStep.State p rate}
    {records : List (RoundRecord (p := p) (rate := rate))}
    (chain : Connected initial records final)
    (i : Fin (p.m - 1)) (j k : ℕ)
    (hj : j < records.length) (hk : k < records.length) (hjk : j < k)
    (message : ReferenceAcceptedUpFollowerHistory.DownRecord (p := p) (rate := rate))
    (hretained : ReferenceAcceptedUpFollowerHistory.RetainedDown records[j] i message)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hinput : records[k].input.state.followers i = .ordinary state memory) :
    message.val.sigma ≤ ReferencePrelaunchFollower.acceptedStart state := by
  have hprefix := connected_take_to_input chain k hk
  have hjPrefix : j < (records.take k).length := by
    simp only [List.length_take]
    exact lt_min hjk hj
  obtain ⟨post, postMemory, hpost, _hpostBound⟩ :=
    connected_output_chronology hprefix i state memory hinput j hjPrefix
  have hpostRecord : (records.take k)[j] = records[j] := by
    simp only [List.getElem_take]
  rw [hpostRecord] at hpost
  have happlied := ReferenceAcceptedUpFollowerHistory.retainedDown_appliedDown hretained
  obtain ⟨_choice, _choiceMemory, _hchoice, _hstrict, hpostStart⟩ :=
    record_appliedDown_strict records[j] i message.val.sigma happlied post postMemory hpost
  have htail := connected_drop_from_output chain j hj
  let tail := records.drop (j + 1)
  let offset := k - (j + 1)
  have hoffset : offset < tail.length := by
    simp only [tail, List.length_drop]
    omega
  have hsegment := connected_take_to_input htail offset hoffset
  have hrecord : tail[offset] = records[k] := by
    simp only [tail, offset, List.getElem_drop]
    congr 1; omega
  rw [hrecord] at hsegment
  obtain ⟨first, firstMemory, hfirst, hbound, _hfreeze, _hwitness⟩ :=
    connected_ordinary_chronology hsegment i state memory hinput
  have hfirstEq : first = post := by
    have hlocal :
        records[j].output.next.followers i = .ordinary first firstMemory := hfirst
    have hlocal' : records[j].output.next.followers i = .ordinary post postMemory := hpost
    exact (LocalConfiguration.ordinary.inj (hlocal.symm.trans hlocal')).1
  have hbound' :
      ReferencePrelaunchFollower.acceptedStart post ≤
        ReferencePrelaunchFollower.acceptedStart state := by
    simpa only [hfirstEq] using hbound
  rw [← hpostStart]
  exact hbound'

private theorem unoccupied_prepare_configuration
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (activation : ReferencePrelaunchFollower.Activation p) (time : Fin p.T)
    (active : activation.val ≤ time.val + 1)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hdomain : ActiveFollowerLifecycle.localStateDomainValid state)
    (hunoccupied : state.status = .unoccupied)
    (hpositive : 1 ≤ ReferencePrelaunchFollower.acceptedStart state) :
    (DeclaredFollowerLocalRound.prepare rate i row activation time active
      (.ordinary state memory)).configuration = .ordinary state memory := by
  have hstart := ActiveFollowerLifecycle.startRound_unoccupied rate.eta time state memory
    hdomain hunoccupied
  have hstateInput := ActualReferenceInitializationBlock.up_domain_of_local_domain state hdomain
  have hstartBound : ReferencePrelaunchFollower.acceptedStart state ≤ p.T := by
    cases hlast : state.lastDown with
    | none => simp [ReferencePrelaunchFollower.acceptedStart, hlast] at hpositive
    | some down =>
        have hbound : down.val.sigma ≤ p.T := by
          simpa only [ReferencePrelaunchFollower.codecParams] using down.property.2.1
        simpa [ReferencePrelaunchFollower.acceptedStart, hlast] using hbound
  have hadmissible : OrdinaryMessageCodec.upAdmissible
      (ReferencePrelaunchFollower.codecParams p rate.eta)
      (ActiveFollowerQueueOperation.upOfferFields state) := by
    unfold OrdinaryMessageCodec.upAdmissible ActiveFollowerQueueOperation.upOfferFields
    exact Or.inr ⟨hpositive, hstartBound, hdomain.1.1, hdomain.1.2.1,
      hdomain.1.2.2⟩
  let offered : OrdinaryMessageCodec.UpRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta) :=
    ⟨ActiveFollowerQueueOperation.upOfferFields state, hadmissible⟩
  have hoffSelected : ∀ hselected : ActiveFollowerQueueOperation.selectedUpRound i row
      activation time,
      ActiveFollowerQueueOperation.checkedUpOffer rate.eta i row activation time state =
        .offer offered := by
    intro hselected
    unfold ActiveFollowerQueueOperation.checkedUpOffer
    rw [dite_eq_left hstateInput, dite_eq_left ⟨hselected, hunoccupied⟩,
      dite_eq_left hadmissible]
  have hoffNotSelected : ∀ hnot : ¬ ActiveFollowerQueueOperation.selectedUpRound i row
      activation time,
      ActiveFollowerQueueOperation.checkedUpOffer rate.eta i row activation time state =
        .noOffer := by
    intro hnot
    apply ActiveFollowerQueueOperation.checkedUpOffer_noOffer rate.eta i row activation time
      state hstateInput
    intro hselected
    exact hnot hselected.1
  by_cases hdata : PublicDiscreteDraws.slotDraw (row.2 time).1 = PublicDiscreteDraws.dataSlot
  · have hnotSelected : ¬ ActiveFollowerQueueOperation.selectedUpRound i row activation time := by
      rintro ⟨_, hslot, _⟩
      have hne : PublicDiscreteDraws.dataSlot ≠ PublicDiscreteDraws.upSlot := by decide
      exact hne (hdata.symm.trans hslot)
    have hoff := hoffNotSelected hnotSelected
    have hcore := ActiveFollowerArmChoice.followerArmChoiceCore_unoccupied_data state
      (row.2 time) i none hunoccupied hdata
    have hchoice : ActiveFollowerArmChoice.followerArmChoice state row time i none =
        some (PublicDiscreteDraws.pilotDraw (ConstructorDimensions.K_pos p)
          (PublicDiscreteDraws.followerPlayer p.two_le_m i) (row.2 time).1) := by
      rw [ActiveFollowerArmChoice.followerArmChoice_eq_core]
      exact hcore
    simp [DeclaredFollowerLocalRound.prepare, hstart, hoff, hchoice]
  · by_cases hup : PublicDiscreteDraws.slotDraw (row.2 time).1 = PublicDiscreteDraws.upSlot ∧
        PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K (row.2 time).1 = i
    · have hselected : ActiveFollowerQueueOperation.selectedUpRound i row activation time :=
        ⟨active, hup.1, hup.2⟩
      have hoff := hoffSelected hselected
      have hfields := ActiveFollowerQueueOperation.checkedUpOffer_fields rate.eta i row
        activation time state offered hoff
      have hvalid : ActiveFollowerArmChoice.upStateDomain state ∧
          ActiveFollowerArmChoice.offeredUpMatchesState state offered := by
        constructor
        · exact hdomain.1
        · simp [ActiveFollowerArmChoice.offeredUpMatchesState, offered,
            ActiveFollowerQueueOperation.upOfferFields]
      have hcore := ActiveFollowerArmChoice.followerArmChoiceCore_unoccupied_selected_up
        state (row.2 time) i offered hunoccupied hup.1 hup.2 hvalid
      have hchoice : ActiveFollowerArmChoice.followerArmChoice state row time i (some offered) =
          some (ActiveRoundActions.sendArm
            (ActiveFollowerArmChoice.offeredUpBit rate.eta (row.2 time) i offered)
            ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K (row.2 time).1).val
              (PublicDiscreteDraws.followerPlayer p.two_le_m i))
            ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K (row.2 time).1).val
              (ActiveRoundActions.coordinator p.two_le_m))) := by
        rw [ActiveFollowerArmChoice.followerArmChoice_eq_core]
        exact hcore
      simp [DeclaredFollowerLocalRound.prepare, hstart, hoff, hchoice]
    · have hnotSelected : ¬ ActiveFollowerQueueOperation.selectedUpRound i row activation time := by
        intro hselected
        exact hup ⟨hselected.2.1, hselected.2.2⟩
      have hoff := hoffNotSelected hnotSelected
      have hnotPair : ¬ (PublicDiscreteDraws.slotDraw (row.2 time).1 =
          PublicDiscreteDraws.upSlot ∧
          PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
            (row.2 time).1 = i) := fun hp => hup hp
      have hcore := ActiveFollowerArmChoice.followerArmChoiceCore_unoccupied_other
        state (row.2 time) i none hunoccupied (by simp [hdata]) hnotPair
      have hchoice : ActiveFollowerArmChoice.followerArmChoice state row time i none =
          some ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K (row.2 time).1).val
            (PublicDiscreteDraws.followerPlayer p.two_le_m i)) := by
        rw [ActiveFollowerArmChoice.followerArmChoice_eq_core]
        exact hcore
      simp [DeclaredFollowerLocalRound.prepare, hstart, hoff, hchoice]

private theorem actual_unoccupied_prepare_configuration
    (record : RoundRecord (p := p) (rate := rate)) (i : Fin (p.m - 1))
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hinput : record.input.state.followers i = .ordinary state memory)
    (hdomain : ActiveFollowerLifecycle.localStateDomainValid state)
    (hunoccupied : state.status = .unoccupied)
    (hpositive : 1 ≤ ReferencePrelaunchFollower.acceptedStart state) :
    (ReferenceFollowerFixedReply.actualChoice record i).configuration =
      .ordinary state memory := by
  have hdeclared := unoccupied_prepare_configuration i record.input.row
    (record.input.state.activations i) record.input.time (record.input.active i)
    state memory hdomain hunoccupied hpositive
  have hprep : record.output.preparation.followers.followers i =
      DeclaredFollowerLocalRound.prepare rate i record.input.row
        (record.input.state.activations i) record.input.time
        (record.input.active i) (record.input.state.followers i) := by
    rw [record.output_eq]
    exact (ReferenceActivePhysicalStep.prepare record.input).followers.followers_eq i
  change (record.output.preparation.followers.followers i).configuration = _
  rw [hprep, hinput]
  exact hdeclared

end Bandits.Support.ReferenceFirstCollectionFormedReplyStateInterval

@[expose] public section

namespace Bandits.Support.ReferenceFirstCollectionFormedReplyStateInterval

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

/-- Literal record at a coordinate of the complete actual collection window. -/
public def actualCollectionRecord
    (B : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (k : Fin B.length) : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) :=
  B[k.val]

/-- Literal prepared CHOICE of the indicated follower in that same record. -/
public def actualCollectionChoice
    (B : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (i : Fin (p.m - 1)) (k : Fin B.length) :
    DeclaredFollowerLocalRound.PreparedRound p rate :=
  ReferenceFollowerFixedReply.actualChoice (actualCollectionRecord B k) i

private theorem actualCollectionChoice_eq_actualChoice
    {B : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))}
    (i : Fin (p.m - 1)) (k : Fin B.length)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hrecord : B[k.val]'k.isLt = record) :
    actualCollectionChoice B i k = ReferenceFollowerFixedReply.actualChoice record i := by
  unfold actualCollectionChoice actualCollectionRecord
  rw [hrecord]

private theorem actualCollectionChoice_alignment
    {B : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))}
    (i : Fin (p.m - 1)) (k : Fin B.length) :
    (actualCollectionChoice B i k).row = (actualCollectionRecord B k).input.row ∧
    (actualCollectionChoice B i k).follower = i ∧
    (actualCollectionChoice B i k).activation =
      (actualCollectionRecord B k).input.state.activations i ∧
    (actualCollectionChoice B i k).time = (actualCollectionRecord B k).input.time := by
  have h := ReferenceActivePhysicalStep.PreparedRound.follower_alignment
    (actualCollectionRecord B k).output.preparation i
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [actualCollectionChoice, ReferenceFollowerFixedReply.actualChoice] using h.1
  · simpa [actualCollectionChoice, ReferenceFollowerFixedReply.actualChoice] using h.2.1
  · simpa [actualCollectionChoice, ReferenceFollowerFixedReply.actualChoice] using h.2.2.2
  · simpa [actualCollectionChoice, ReferenceFollowerFixedReply.actualChoice] using h.2.2.1

private theorem connected_actual_reply_constancy
    {initial final : ReferenceActivePhysicalStep.State p rate}
    {records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))}
    (chain : ReferenceActivePhysicalHorizon.Connected initial records final)
    (i : Fin (p.m - 1)) (a b : Fin records.length) (hab : a.val ≤ b.val)
    (left right : ReferencePrelaunchFollower.State p rate.eta)
    (leftMemory rightMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hl : (ReferenceFollowerFixedReply.actualChoice records[a.val] i).configuration =
      .ordinary left leftMemory)
    (hr : (ReferenceFollowerFixedReply.actualChoice records[b.val] i).configuration =
      .ordinary right rightMemory)
    (hunoccupied : left.status = .unoccupied)
    (hstart : ReferencePrelaunchFollower.acceptedStart left =
      ReferencePrelaunchFollower.acceptedStart right) :
    right.status = .unoccupied ∧ right.lastDown = left.lastDown ∧
      right.S = left.S ∧ right.delta = left.delta ∧ right.backlog = left.backlog := by
  obtain ⟨hstatus, hreply⟩ :=
    ReferenceFollowerReplyChronology.connected_choice_chronology chain i a.val b.val
      a.isLt b.isLt hab left right leftMemory rightMemory hl hr |>.2.1 hunoccupied hstart
  exact ⟨hstatus, (Prod.mk.inj hreply).1, (Prod.mk.inj (Prod.mk.inj hreply).2).1,
    (Prod.mk.inj (Prod.mk.inj (Prod.mk.inj hreply).2).2).1,
    (Prod.mk.inj (Prod.mk.inj (Prod.mk.inj hreply).2).2).2⟩

/-- Extend the admitted formation origin on its same dispatch and unique
acceptance index. Every choice from the clipped formation coordinate through
the current pending boundary has the same ordinary unoccupied reply. The
incoming state and PREPARE reply equality are produced at each coordinate;
pending is read before CHOICE, using the actual START reset at coordinate zero.

The root telescope is unchanged from the formation-origin producer. Its
existing current-boundary offer fact is retained; no interval offer, receiver,
decoder-bank, numerical-identity, or manuscript-closure claim is added. -/
public theorem actual_initialized_first_collection_formed_reply_state_interval
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
    ∃ d : ReferenceFirstCollectionStreamEmptyDispatch.ActualInitializedStreamDispatch
        source rewards C_star C_h count hcross hspan hshort,
      let out := d.stream
      let E := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
        rate source rewards C_star C_h hcross count hspan
      let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records).length
      let s := ReferenceInitializationRun.elapsed p
        (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
      let B := ReferenceCollectionPhaseHistory.collectionWindow E.records w
      ∃ (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
        (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
        (base : Fin (p.m - 1) → ℕ)
        (cutRecord : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)),
        E.records[w]? = some cutRecord ∧
        cutRecord.input.state.coordinator = .live registers owned base ∧
        registers.payload = out.payload ∧
        out.cutoff.ledger.pending = Finset.univ ∧
        (∀ (n : Fin out.ell), 0 < n.val →
          ∀ i : Fin (p.m - 1),
            i ∈ (out.ledgers ⟨n.val - 1, by omega⟩).pending →
              ∃ (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
                (incoming : ReferenceActivePhysicalStep.Ledger rate)
                (cell : ReferenceFirstCollectionReadyStream.ContinuingStreamCell
                  source rewards E.records (w + n.val) count
                  (ReferenceInitializationRun.elapsed p
                    (ReferenceInitializationRun.output
                      (ActualReferenceInitializationBlock.referenceInput
                        source rewards C_star C_h rate)).completed)
                  r out.payload incoming out.saved)
                (state : ReferencePrelaunchFollower.State p rate.eta)
                (memory : ActiveFollowerLifecycle.LocalMemory p),
                out.window[n.val]? = some r ∧
                r.input.time.val + 1 =
                  ReferenceInitializationRun.elapsed p
                    (ReferenceInitializationRun.output
                      (ActualReferenceInitializationBlock.referenceInput
                        source rewards C_star C_h rate)).completed +
                    w + 1 + n.val ∧
                r.input.rows = source.1.2 ∧
                r.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p source ∧
                r.input.rewards = rewards ∧
                incoming = out.ledgers ⟨n.val - 1, by omega⟩ ∧
                i ∈ incoming.pending ∧
                ReferenceContinuingCollectionStartDomains.continuingCollectionReadyDomain
                  r.input out.payload incoming out.saved ∧
                cell.serviceLedger = out.ledgers n ∧
                r.input.state.followers i = .ordinary state memory ∧
                state.status = .unoccupied ∧
                ActiveFollowerLifecycle.localStateDomainValid state ∧
                state.S ≤ p.T * D p ∧ state.delta ≤ D p ∧ state.backlog ≤ p.T * D p ∧
                state.S + state.backlog ≤ w * D p ∧
                state.downBatch.pending.length < AffineBatchDecoder.quota p ∧
                (∀ batch ∈ state.downBatch.completed,
                  batch.length = AffineBatchDecoder.quota p) ∧
                ((state.lastDown = none ∧ state.S = 0 ∧ state.delta = 0 ∧ state.backlog = 0) ∨
                  state.lastDown = some (out.payload.downRecord i)) ∧
                (state.lastDown = some (out.payload.downRecord i) →
                  ∃ U : OrdinaryMessageCodec.UpRecord
                      (ReferencePrelaunchFollower.codecParams p rate.eta),
                    U.val = ActiveFollowerQueueOperation.upOfferFields state ∧
                    1 ≤ U.val.sigma ∧
                    (ReferenceActivePhysicalStep.upSenderIndex r.input = i →
                      PublicDiscreteDraws.slotDraw
                          (r.input.row.2 r.input.time).1 = PublicDiscreteDraws.upSlot →
                        ((ReferenceActivePhysicalStep.prepare r.input).followers.followers i).configuration =
                            .ordinary state memory ∧
                        ActiveFollowerQueueOperation.checkedUpOffer rate.eta i r.input.row
                          (r.input.state.activations i) r.input.time state = .offer U ∧
                        ReferenceFollowerFixedReply.actualUpExpected r =
                          some ((OrdinaryMessageCodec.wordEquivFlat
                            (CoordinatorCollectionLedger.codecParams p rate.eta.val))
                            (OrdinaryMessageCodec.encodeUp
                              (CoordinatorCollectionLedger.codecParams p rate.eta.val) U)))) ∧
                (state.lastDown = some (out.payload.downRecord i) →
                  (out.payload.downRecord i).val.sigma = s + 1 ∧
                  acceptedStart state = s + 1 ∧
                  ∃ (j : ℕ) (acceptedRecord : RoundRecord (p := p) (rate := rate)),
                    j < w + n.val ∧ E.records[j]? = some acceptedRecord ∧
                    RetainedDown acceptedRecord i (out.payload.downRecord i) ∧
                    (∃ (logged : ReferencePrelaunchFollower.State p rate.eta)
                      (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
                      (after : ReferencePrelaunchFollower.State p rate.eta)
                      (raw : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p)))
                      (scan : FollowerCutoffScan.ScanResult p.T)
                      (registers : ℕ × ℕ) (lastService : ℕ),
                      (acceptedRecord.output.followers i).downInput = some logged ∧
                      (acceptedRecord.output.followers i).down = some cut ∧
                      cut.outcome = ActiveFollowerDownAcceptance.LocalDownResult.accepted
                        logged after raw (out.payload.downRecord i) scan registers lastService) ∧
                    acceptedRecord.input.time.val + 1 = s + j + 1 ∧
                    acceptedRecord.input.rows = source.1.2 ∧
                    acceptedRecord.input.selected =
                      ActualInitializationPhysicalStep.selectedRowIndex p source ∧
                    acceptedRecord.input.rewards = rewards ∧
                    (∀ (j' : ℕ) (other : RoundRecord (p := p) (rate := rate)),
                      j' < w + n.val → E.records[j']? = some other →
                        RetainedDown other i (out.payload.downRecord i) → j' = j) ∧
                    let f := if j < w then 0 else j - w + 1
                    ∃ hf : f < B.length,
                      f ≤ n.val ∧
                      B[f].input.time.val + 1 = max (s + w + 1) (s + j + 2) ∧
                      (j < w → f = 0) ∧ (j = w → f = 1) ∧
                      ((∀ (k : Fin B.length) (_hkpos : 0 < k.val)
                          (hkn : k.val ≤ n.val),
                        (out.ledgers ⟨n.val - 1, by omega⟩).pending ⊆
                          (out.ledgers ⟨k.val - 1,
                            Nat.lt_of_le_of_lt (Nat.sub_le _ _)
                              (Nat.lt_of_le_of_lt hkn n.isLt)⟩).pending) ∧
                      ∀ (k : Fin B.length) (hfk : f ≤ k.val)
                        (hkn : k.val ≤ n.val),
                        ∃ (choice : ReferencePrelaunchFollower.State p rate.eta)
                          (choiceMemory : ActiveFollowerLifecycle.LocalMemory p),
                          (actualCollectionChoice B i k).configuration =
                            .ordinary choice choiceMemory ∧
                          choice.status = .unoccupied ∧
                          ReferenceFollowerReplyChronology.reply choice =
                            ReferenceFollowerReplyChronology.reply state ∧
                          choice.lastDown = some (out.payload.downRecord i) ∧
                          choice.S = state.S ∧ choice.delta = state.delta ∧
                          choice.backlog = state.backlog ∧
                          (actualCollectionChoice B i k).row =
                            (actualCollectionRecord B k).input.row ∧
                          (actualCollectionChoice B i k).follower = i ∧
                          (actualCollectionChoice B i k).activation =
                            (actualCollectionRecord B k).input.state.activations i ∧
                          (actualCollectionChoice B i k).time =
                            (actualCollectionRecord B k).input.time ∧
                          ∃ (before : ReferencePrelaunchFollower.State p rate.eta)
                            (beforeMemory : ActiveFollowerLifecycle.LocalMemory p),
                            (actualCollectionRecord B k).input.state.followers i =
                              .ordinary before beforeMemory ∧
                            ReferenceFollowerReplyChronology.reply choice =
                              ReferenceFollowerReplyChronology.reply before ∧
                            ((k.val = 0 →
                              i ∈ out.cutoff.ledger.pending ∧
                              out.cutoff.ledger.pending = Finset.univ ∧
                              (actualCollectionRecord B k).input.state.coordinator =
                                .live registers owned base ∧
                              E.records[w]? = some cutRecord) ∧
                             (0 < k.val →
                              i ∈ (out.ledgers ⟨k.val - 1,
                                Nat.lt_of_le_of_lt (Nat.sub_le _ _)
                                  (Nat.lt_of_le_of_lt hkn n.isLt)⟩).pending ∧
                              incoming = out.ledgers ⟨n.val - 1,
                                Nat.lt_of_le_of_lt (Nat.sub_le _ _) n.isLt⟩ ∧
                              i ∈ incoming.pending))))) := by
  classical
  obtain ⟨d, registers, owned, base, cutRecord, hcutIndex, hcutState,
    hpayload, hpending, hboundaries⟩ :=
    ReferenceFirstCollectionFormationOrigin.actual_initialized_first_collection_formation_origin
      rate source rewards C_star C_h count hcross hspan hshort
  refine ⟨d, registers, owned, base, cutRecord, hcutIndex, hcutState,
    hpayload, hpending, ?_⟩
  let out := d.stream
  let E := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
    rate source rewards C_star C_h hcross count hspan
  let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records).length
  let s := ReferenceInitializationRun.elapsed p
    (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
  let B := ReferenceCollectionPhaseHistory.collectionWindow E.records w
  let initial := ReferenceFirstCollectionEpochAlignment.actualLaunchState
    rate source rewards C_star C_h hcross
  let active := (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
    rate source rewards C_star C_h hcross).1
  let rows := source.1.2
  let selected := ActualInitializationPhysicalStep.selectedRowIndex p source
  let seed (a : Fin (p.m - 1)) :=
    ReferenceInitializationRun.ordinary
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate))
      (ActualReferenceInitializationBlock.refFollower a)
  let seedMemory (_a : Fin (p.m - 1)) := ActiveFollowerLifecycle.initialMemory p
  have hRun : E = ReferenceActivePhysicalHorizon.run initial rows selected rewards s count
      hspan active := by
    rfl
  have hWindow : out.window = B := by
    simpa [out, E, w, B, ReferenceFirstCollectionReadyStream.actualWindow,
      ReferenceFirstCollectionReadyStream.actualEpoch,
      ReferenceFirstCollectionReadyStream.startTime] using out.windowIsActual
  have hshortRun :
      (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (ReferenceActivePhysicalHorizon.run initial rows selected rewards s count
          hspan active).records).length < count := by
    simpa [E, initial, active,
      ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun] using hshort
  have hseedAll := ReferenceFirstLaunchNumericalCell.actual_launch_seed
    rate source rewards C_star C_h hcross
  rcases hseedAll with ⟨_, hactive, _, hfirst, _, _, _, hseedFields⟩
  have hseedProperties (a : Fin (p.m - 1)) :
      initial.followers a = .ordinary (seed a) (seedMemory a) ∧
      (seed a).lastDown = none ∧ ReferencePrelaunchFollower.acceptedStart (seed a) = 0 ∧
      (seed a).S = 0 ∧ (seed a).delta = 0 ∧
      (seed a).backlog = 0 ∧ (seed a).status = .unoccupied ∧
      ActiveFollowerLifecycle.localStateDomainValid (seed a) ∧
      ActiveFollowerLifecycle.localBufferValid (seed a) ∧
      (seed a).buffer.Pairwise (fun x y => x.calendarRound < y.calendarRound) ∧
      ∀ saved, saved ∈ (seed a).buffer → saved.calendarRound ≤ s := by
    simpa [initial, seed, seedMemory,
      ReferenceFirstCollectionEpochAlignment.actualLaunchState,
      ReferenceFirstLaunchNumericalCell.launchState] using hseedFields a
  have hseedOrd : ∀ a, initial.followers a = .ordinary (seed a) (seedMemory a) :=
    fun a => (hseedProperties a).1
  have hseedNone : ∀ a, (seed a).lastDown = none := fun a => (hseedProperties a).2.1
  have hseedStart : ∀ a, ReferencePrelaunchFollower.acceptedStart (seed a) = 0 :=
    fun a => (hseedProperties a).2.2.1
  have hseedS : ∀ a, (seed a).S = 0 := fun a => (hseedProperties a).2.2.2.1
  have hseedDelta : ∀ a, (seed a).delta = 0 := fun a => (hseedProperties a).2.2.2.2.1
  have hseedBacklog : ∀ a, (seed a).backlog = 0 := fun a => (hseedProperties a).2.2.2.2.2.1
  have hseedUnoccupied : ∀ a, (seed a).status = .unoccupied :=
    fun a => (hseedProperties a).2.2.2.2.2.2.1
  have hseedDomain : ∀ a, ActiveFollowerLifecycle.localStateDomainValid (seed a) :=
    fun a => (hseedProperties a).2.2.2.2.2.2.2.1
  have hseedBuffer : ∀ a, ActiveFollowerLifecycle.localBufferValid (seed a) :=
    fun a => (hseedProperties a).2.2.2.2.2.2.2.2.1
  have hseedPair : ∀ a, (seed a).buffer.Pairwise
      (fun x y => x.calendarRound < y.calendarRound) :=
    fun a => (hseedProperties a).2.2.2.2.2.2.2.2.2.1
  have hseedTime : ∀ a saved, saved ∈ (seed a).buffer → saved.calendarRound ≤ s :=
    fun a => (hseedProperties a).2.2.2.2.2.2.2.2.2.2
  have hseedBatch : ∀ a, ActiveFollowerLifecycle.downDecoderStateValid (seed a) := by
    intro a
    exact (hseedDomain a).2.2
  have hcutPrep :=
    ReferenceFirstCutoffFollowerPreparation.run_first_cutoff_follower_preparation
      initial rows selected rewards s count hspan hactive hfirst seed seedMemory
      hseedOrd hseedS hseedDelta hseedBacklog hseedNone hseedUnoccupied hseedBuffer
      hseedPair hseedTime hseedBatch hshortRun
  rcases hcutPrep with ⟨cut, suffix, hsplit, hcutInRun, hcutTime, hcutStateRun,
    _hcutRows, _hcutSelected, _hcutRewards, hcutFollowers, _hcutFeedback,
    _hcutEntries⟩
  have hw : w < E.records.length :=
    (List.getElem?_eq_some_iff.mp hcutIndex).1
  have hcutAt : cut = E.records[w]'hw := by
    have hActiveProof : active = hactive := Subsingleton.elim _ _
    cases hActiveProof
    simpa [hRun, w] using hcutInRun
  have hcutLookup : E.records[w]? = some cut := by
    rw [List.getElem?_eq_getElem hw]
    exact congrArg some hcutAt.symm
  have hcutEq : cut = cutRecord := Option.some.inj (hcutLookup.symm.trans hcutIndex)
  have hWindowPos : 0 < out.window.length := out.windowNonempty
  have hBPos : 0 < B.length := by rw [← hWindow]; exact hWindowPos
  let zero : Fin out.window.length := ⟨0, hWindowPos⟩
  have hentryZero : out.window[0]? = some B[0] := by
    rw [hWindow]
    exact List.getElem?_eq_some_iff.mpr ⟨by omega, rfl⟩
  have halignZero := out.alignment zero
  simp only [zero] at halignZero
  have helemZero : out.window[0] = B[0] :=
    (List.getElem?_eq_some_iff.mp hentryZero).2
  have hrootB0 : E.records[w]? = some B[0] := by
    simpa [out, E, w, zero, Nat.add_zero, helemZero,
      ReferenceFirstCollectionReadyStream.actualEpoch,
      ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun] using halignZero.1
  have hcutB0 : B[0] = cutRecord := Option.some.inj (hrootB0.symm.trans hcutIndex)

  intro n hn i hi
  rcases hboundaries n hn i hi with
    ⟨r, incoming, cell, state, memory, hr, htime, hrows, hselected,
      hrewards, hincoming, hiIncoming, hready, hservice, hstate, hstatus,
      hdomain, hS, hdelta, hbacklog, hmass, hbank, hcompleted, hlast,
      hup, horigin⟩
  refine ⟨r, incoming, cell, state, memory, hr, htime, hrows, hselected,
    hrewards, hincoming, hiIncoming, hready, hservice, hstate, hstatus,
    hdomain, hS, hdelta, hbacklog, hmass, hbank, hcompleted, hlast, hup, ?_⟩
  intro hformed
  rcases horigin hformed with
    ⟨hmessageSigma, hstart, j, acceptedRecord, hj, hlookup, hretained,
      hdiagnostics, hacceptedTime, hacceptedRows, hacceptedSelected,
      hacceptedRewards, hunique, hf, hfn, hdate, hjBefore, hjAtCutoff⟩
  refine ⟨hmessageSigma, hstart, j, acceptedRecord, hj, hlookup, hretained,
    hdiagnostics, hacceptedTime, hacceptedRows, hacceptedSelected,
    hacceptedRewards, hunique, hf, hfn, hdate, hjBefore, hjAtCutoff, ?_⟩
  let message := out.payload.downRecord i
  have hlastSome : state.lastDown = some message := by
    rcases hlast with hzeroState | hsomeState
    · rcases hzeroState with ⟨hlastNone, _hSZero, _hdeltaZero, _hbacklogZero⟩
      simp [ReferencePrelaunchFollower.acceptedStart, hlastNone] at hstart
    · exact hsomeState
  have hjIndex : j < E.records.length := (List.getElem?_eq_some_iff.mp hlookup).1
  have hacceptedRecord : E.records[j] = acceptedRecord :=
    (List.getElem?_eq_some_iff.mp hlookup).2
  have hretainedIndex :
      ReferenceAcceptedUpFollowerHistory.RetainedDown E.records[j] i message := by
    rw [hacceptedRecord]
    exact hretained
  have hterminalStart : ReferencePrelaunchFollower.acceptedStart state = message.val.sigma := by
    calc
      ReferencePrelaunchFollower.acceptedStart state = s + 1 := hstart
      _ = (out.payload.downRecord i).val.sigma := hmessageSigma.symm
      _ = message.val.sigma := rfl
  have hwindowBounds : n.val < B.length := by
    calc
      n.val < out.ell := n.isLt
      _ ≤ out.window.length := out.withinWindow
      _ = B.length := congrArg List.length hWindow
  let nWindow : Fin B.length := ⟨n.val, hwindowBounds⟩
  have hentryN : out.window[n.val]? = some B[n.val] := by
    rw [hWindow]
    exact List.getElem?_eq_some_iff.mpr ⟨hwindowBounds, rfl⟩
  have hrecordN : B[n.val] = r := Option.some.inj (hentryN.symm.trans hr)
  let outIndexN : Fin out.window.length := ⟨n.val, by
    calc
      n.val < out.ell := n.isLt
      _ ≤ out.window.length := out.withinWindow⟩
  have halignN := out.alignment outIndexN
  have hrecordLookupN : E.records[w + n.val]? = some r := by
    have hlookupBase : E.records[w + n.val]? =
        some (out.window[outIndexN.val]'outIndexN.isLt) := by
      simpa only [outIndexN, out, E, w,
        ReferenceFirstCollectionReadyStream.actualEpoch,
        ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun] using halignN.1
    have hnwindow : n.val < out.window.length :=
      lt_of_lt_of_le n.isLt out.withinWindow
    have hwindowValueN : out.window[n.val]'hnwindow = B[n.val]'hwindowBounds :=
      (List.getElem?_eq_some_iff.mp hentryN).2
    simp only [outIndexN] at hlookupBase
    rw [hwindowValueN] at hlookupBase
    rw [hrecordN] at hlookupBase
    exact hlookupBase
  have hindexNlt : w + n.val < E.records.length :=
    (List.getElem?_eq_some_iff.mp hrecordLookupN).1
  have hrecordEqN : E.records[w + n.val] = r :=
    (List.getElem?_eq_some_iff.mp hrecordLookupN).2
  have hinputN : E.records[w + n.val].input.state.followers i =
      .ordinary state memory := by
    rw [hrecordEqN]
    exact hstate
  have hjBeforeN : j < w + n.val := by
    by_cases hjw : j < w
    · omega
    · omega
  have hlowerN := retained_down_start_le_of_later_input E.connected i j (w + n.val)
    hjIndex hindexNlt hjBeforeN message hretainedIndex state memory hinputN
  have hpositiveN : 1 ≤ ReferencePrelaunchFollower.acceptedStart state := by
    rw [hterminalStart, hmessageSigma]
    omega
  have hchoiceN := actual_unoccupied_prepare_configuration r i state memory
    hstate hdomain hstatus hpositiveN
  have hchoiceNWindow :
      (actualCollectionChoice B i nWindow).configuration =
        .ordinary state memory := by
    have hrecordNWindow : B[nWindow.val]'nWindow.isLt = r := by
      simpa [nWindow] using hrecordN
    have hchoiceEq := actualCollectionChoice_eq_actualChoice i nWindow r hrecordNWindow
    exact (congrArg (fun choice => choice.configuration) hchoiceEq).trans hchoiceN
  have hlookupWindow (k : Fin B.length) :
      E.records[w + k.val]? = some B[k.val] := by
    let outIndex : Fin out.window.length := ⟨k.val, by rw [hWindow]; exact k.isLt⟩
    have halign := out.alignment outIndex
    have hlookupBase : E.records[w + k.val]? =
        some (out.window[outIndex.val]'outIndex.isLt) := by
      simpa only [outIndex, out, E, w,
        ReferenceFirstCollectionReadyStream.actualEpoch,
        ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun] using halign.1
    have hbound : k.val < out.window.length := by
      calc
        k.val < B.length := k.isLt
        _ = out.window.length := (congrArg List.length hWindow).symm
    have hentry : out.window[k.val]? = some B[k.val] := by
      rw [hWindow]
      exact List.getElem?_eq_some_iff.mpr ⟨k.isLt, rfl⟩
    have hwindowValue : out.window[k.val]'hbound = B[k.val]'k.isLt :=
      (List.getElem?_eq_some_iff.mp hentry).2
    simp only [outIndex] at hlookupBase
    rw [hwindowValue] at hlookupBase
    exact hlookupBase
  have hlookupActualWindow (k : Fin B.length) :
      ∃ hkWindow : k.val < out.window.length,
        E.records[w + k.val]? = some (out.window[k.val]'hkWindow) := by
    have hkWindow : k.val < out.window.length := by
      calc
        k.val < B.length := k.isLt
        _ = out.window.length := (congrArg List.length hWindow).symm
    let outIndex : Fin out.window.length := ⟨k.val, hkWindow⟩
    have halign := out.alignment outIndex
    refine ⟨hkWindow, ?_⟩
    simpa only [outIndex, out, E, w,
      ReferenceFirstCollectionReadyStream.actualEpoch,
      ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun] using halign.1

  have finishAt (k : Fin B.length)
      (hfk : (if j < w then 0 else j - w + 1) ≤ k.val)
      (hkn : k.val ≤ n.val)
      (choice : ReferencePrelaunchFollower.State p rate.eta)
      (choiceMemory : ActiveFollowerLifecycle.LocalMemory p)
      (before : ReferencePrelaunchFollower.State p rate.eta)
      (beforeMemory : ActiveFollowerLifecycle.LocalMemory p)
      (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
      (hrecord : B[k.val]'k.isLt = record)
      (hconfig : (actualCollectionChoice B i k).configuration =
        .ordinary choice choiceMemory)
      (hstatusChoice : choice.status = .unoccupied)
      (hbefore : record.input.state.followers i = .ordinary before beforeMemory)
      (hreplyBefore : ReferenceFollowerReplyChronology.reply choice =
        ReferenceFollowerReplyChronology.reply before)
      (hcutPending : k.val = 0 →
        i ∈ out.cutoff.ledger.pending ∧ out.cutoff.ledger.pending = Finset.univ ∧
        record.input.state.coordinator = .live registers owned base ∧
        E.records[w]? = some cutRecord)
      (hpositivePending : ∀ (hkpos : 0 < k.val),
        i ∈ (out.ledgers ⟨k.val - 1,
          Nat.lt_of_le_of_lt (Nat.sub_le _ _) (Nat.lt_of_le_of_lt hkn n.isLt)⟩).pending ∧
        incoming = out.ledgers ⟨n.val - 1,
          Nat.lt_of_le_of_lt (Nat.sub_le _ _) n.isLt⟩ ∧ i ∈ incoming.pending)
      (hlowerChoice : message.val.sigma ≤
        ReferencePrelaunchFollower.acceptedStart choice) :
      ReferenceFollowerReplyChronology.reply choice =
        ReferenceFollowerReplyChronology.reply state ∧
      choice.lastDown = some message ∧ choice.S = state.S ∧
      choice.delta = state.delta ∧ choice.backlog = state.backlog ∧
      (actualCollectionChoice B i k).row = (actualCollectionRecord B k).input.row ∧
      (actualCollectionChoice B i k).follower = i ∧
      (actualCollectionChoice B i k).activation =
        (actualCollectionRecord B k).input.state.activations i ∧
      (actualCollectionChoice B i k).time = (actualCollectionRecord B k).input.time ∧
      ((k.val = 0 →
          i ∈ out.cutoff.ledger.pending ∧ out.cutoff.ledger.pending = Finset.univ ∧
          record.input.state.coordinator = .live registers owned base ∧
          E.records[w]? = some cutRecord) ∧
       (0 < k.val →
          i ∈ (out.ledgers ⟨k.val - 1,
            Nat.lt_of_le_of_lt (Nat.sub_le _ _) (Nat.lt_of_le_of_lt hkn n.isLt)⟩).pending ∧
          incoming = out.ledgers ⟨n.val - 1,
            Nat.lt_of_le_of_lt (Nat.sub_le _ _) n.isLt⟩ ∧ i ∈ incoming.pending)) := by
    have hindexKlt : w + k.val < E.records.length :=
      (List.getElem?_eq_some_iff.mp (hlookupWindow k)).1
    let indexK : Fin E.records.length := ⟨w + k.val, hindexKlt⟩
    have hrecordEqK : E.records[indexK.val]'hindexKlt = B[k.val]'k.isLt :=
      (List.getElem?_eq_some_iff.mp (hlookupWindow k)).2
    have hchoiceKE : (ReferenceFollowerFixedReply.actualChoice
        E.records[indexK.val] i).configuration = .ordinary choice choiceMemory := by
      have hchoiceEq := actualCollectionChoice_eq_actualChoice i k
        E.records[indexK.val] hrecordEqK.symm
      exact (congrArg (fun c => c.configuration) hchoiceEq).symm.trans hconfig
    have hrecordEqN : E.records[w + n.val]'hindexNlt = B[n.val]'nWindow.isLt :=
      (List.getElem?_eq_some_iff.mp (hlookupWindow nWindow)).2
    have hchoiceNE : (ReferenceFollowerFixedReply.actualChoice
        E.records[w + n.val] i).configuration = .ordinary state memory := by
      have hchoiceEq := actualCollectionChoice_eq_actualChoice i nWindow
        E.records[w + n.val] hrecordEqN.symm
      exact (congrArg (fun c => c.configuration) hchoiceEq).symm.trans hchoiceNWindow
    let indexN : Fin E.records.length := ⟨w + n.val, hindexNlt⟩
    have hchron := ReferenceFollowerReplyChronology.connected_choice_chronology
      E.connected i indexK.val indexN.val indexK.isLt indexN.isLt
      (by dsimp [indexK, indexN]; omega) choice state choiceMemory memory
      hchoiceKE hchoiceNE
    have hmono := hchron.1
    -- Chronology supplies the upper bound; the retained acceptance supplies
    -- the lower bound. Neither bound alone establishes reply constancy.
    have hstartEqual :
        ReferencePrelaunchFollower.acceptedStart choice =
          ReferencePrelaunchFollower.acceptedStart state := by
      apply Nat.le_antisymm hmono
      calc
        ReferencePrelaunchFollower.acceptedStart state = message.val.sigma := hterminalStart
        _ ≤ ReferencePrelaunchFollower.acceptedStart choice := hlowerChoice
    have hconst := connected_actual_reply_constancy E.connected i indexK indexN
      (by dsimp [indexK, indexN]; omega) choice state choiceMemory memory
      hchoiceKE hchoiceNE hstatusChoice hstartEqual
    rcases hconst with ⟨_hstatusRight, hlastDown, hSReply, hdeltaReply, hbacklogReply⟩
    have hreply : ReferenceFollowerReplyChronology.reply choice =
        ReferenceFollowerReplyChronology.reply state := by
      simp only [ReferenceFollowerReplyChronology.reply, Prod.mk.injEq]
      exact ⟨hlastDown.symm, hSReply.symm, hdeltaReply.symm, hbacklogReply.symm⟩
    rcases actualCollectionChoice_alignment i k with
      ⟨hrowChoice, hfollowerChoice, hactivationChoice, htimeChoice⟩
    exact ⟨hreply, hlastDown.symm.trans hlastSome, hSReply.symm, hdeltaReply.symm,
      hbacklogReply.symm, hrowChoice, hfollowerChoice, hactivationChoice, htimeChoice,
      ⟨hcutPending, hpositivePending⟩⟩

  have hAt (k : Fin B.length) (hfk : (if j < w then 0 else j - w + 1) ≤ k.val)
      (hkn : k.val ≤ n.val) :
      ∃ choice choiceMemory,
        (actualCollectionChoice B i k).configuration = .ordinary choice choiceMemory ∧
        choice.status = .unoccupied ∧
        ReferenceFollowerReplyChronology.reply choice =
          ReferenceFollowerReplyChronology.reply state ∧
        choice.lastDown = some message ∧ choice.S = state.S ∧
        choice.delta = state.delta ∧ choice.backlog = state.backlog ∧
        (actualCollectionChoice B i k).row = (actualCollectionRecord B k).input.row ∧
        (actualCollectionChoice B i k).follower = i ∧
        (actualCollectionChoice B i k).activation =
          (actualCollectionRecord B k).input.state.activations i ∧
        (actualCollectionChoice B i k).time = (actualCollectionRecord B k).input.time ∧
        ∃ (before : ReferencePrelaunchFollower.State p rate.eta)
          (beforeMemory : ActiveFollowerLifecycle.LocalMemory p),
          (actualCollectionRecord B k).input.state.followers i =
            .ordinary before beforeMemory ∧
          ReferenceFollowerReplyChronology.reply choice =
            ReferenceFollowerReplyChronology.reply before ∧
          ((k.val = 0 →
            i ∈ out.cutoff.ledger.pending ∧ out.cutoff.ledger.pending = Finset.univ ∧
            (actualCollectionRecord B k).input.state.coordinator =
              .live registers owned base ∧
            E.records[w]? = some cutRecord) ∧
           (0 < k.val →
            i ∈ (out.ledgers ⟨k.val - 1,
              Nat.lt_of_le_of_lt (Nat.sub_le _ _) (Nat.lt_of_le_of_lt hkn n.isLt)⟩).pending ∧
            incoming = out.ledgers ⟨n.val - 1,
              Nat.lt_of_le_of_lt (Nat.sub_le _ _) n.isLt⟩ ∧ i ∈ incoming.pending)) := by
    by_cases hk0 : k.val = 0
    · have hk : k = ⟨0, by omega⟩ := Fin.ext hk0
      subst k
      have hzeroB : B[0] = cut := hcutB0.trans hcutEq.symm
      obtain ⟨before, beforeMemory, hbefore, hstatusFacts, hchoiceExtra,
        hstartRound, hprepareCut, hlocalDomain, _hmass, _hSBound, _hDeltaBound,
        _hBacklogBound, _hBufferPair, _hBufferTime, hfields, _hOffer, _hNotOffer,
        _hPilot, _hNoSelected⟩ := hcutFollowers i
      have hjw : j < w := by
        by_contra hnot
        simp only [ite_eq_right hnot] at hfk
        exact (Nat.not_le_of_gt (Nat.succ_pos (j - w))) hfk
      have hinputCut : cut.input.state.followers i =
          .ordinary before beforeMemory := by
        calc
          cut.input.state.followers i = _ := congrArg
            (fun z : ReferenceActivePhysicalStep.State p rate => z.followers i)
            hcutStateRun
          _ = .ordinary before beforeMemory := hbefore
      have hinputAtW : E.records[w].input.state.followers i =
          .ordinary before beforeMemory := by
        have hrecordEq : E.records[w] = cutRecord := by
          have hlookup := hcutIndex
          rw [List.getElem?_eq_getElem hw] at hlookup
          exact Option.some.inj hlookup
        rw [hrecordEq, ← hcutEq]
        exact hinputCut
      have hlowerCut := retained_down_start_le_of_later_input E.connected i j w
        hjIndex hw hjw message hretainedIndex before beforeMemory hinputAtW
      let cutChoice : ReferencePrelaunchFollower.State p rate.eta :=
        { before with status := .unoccupied }
      have hconfigCut :
          (ReferenceFollowerFixedReply.actualChoice cut i).configuration =
            .ordinary cutChoice beforeMemory := by
        simpa [cutChoice, ReferenceFollowerFixedReply.actualChoice] using hprepareCut
      have hreplyCut : ReferenceFollowerReplyChronology.reply cutChoice =
          ReferenceFollowerReplyChronology.reply before := by
        simp [cutChoice, ReferenceFollowerReplyChronology.reply]
      have hcutCoordinator : cut.input.state.coordinator = .live registers owned base := by
        rw [hcutEq]
        exact hcutState
      let k0 : Fin B.length := ⟨0, hBPos⟩
      have hrecordCutB : B[k0.val]'k0.isLt = cut := by
        simpa [k0] using hzeroB
      have hconfigCutB :
          (actualCollectionChoice B i k0).configuration =
            .ordinary cutChoice beforeMemory := by
        have hchoiceEq := actualCollectionChoice_eq_actualChoice i k0 cut hrecordCutB
        exact (congrArg (fun c => c.configuration) hchoiceEq).trans hconfigCut
      have hcutPending : k0.val = 0 →
          i ∈ out.cutoff.ledger.pending ∧ out.cutoff.ledger.pending = Finset.univ ∧
          cut.input.state.coordinator = .live registers owned base ∧
          E.records[w]? = some cutRecord := by
        intro _
        exact ⟨by rw [hpending]; exact Finset.mem_univ i, hpending,
          hcutCoordinator, hcutIndex⟩
      have hpositivePending : ∀ (hkpos : 0 < k0.val),
          i ∈ (out.ledgers ⟨k0.val - 1,
            Nat.lt_of_le_of_lt (Nat.sub_le _ _) (Nat.lt_of_le_of_lt hkn n.isLt)⟩).pending ∧
          incoming = out.ledgers ⟨n.val - 1,
            Nat.lt_of_le_of_lt (Nat.sub_le _ _) n.isLt⟩ ∧ i ∈ incoming.pending := by
        intro hkpos
        omega
      have hlowerChoice : message.val.sigma ≤
          ReferencePrelaunchFollower.acceptedStart cutChoice := by
        have hstartReply :=
          ReferenceFollowerReplyChronology.acceptedStart_eq_of_reply_eq hreplyCut
        exact hlowerCut.trans_eq hstartReply.symm
      refine ⟨cutChoice, beforeMemory, hconfigCutB, ?_, ?_⟩
      · simp [cutChoice]
      · rcases finishAt k0 hfk hkn cutChoice beforeMemory before beforeMemory
          cut hrecordCutB hconfigCutB (by simp [cutChoice]) hinputCut hreplyCut hcutPending
          hpositivePending hlowerChoice with
          ⟨hreply, hlastDown, hS, hdelta, hbacklog, hrow, hfollower, hactivation,
            htime, hpending⟩
        have hinputB : (actualCollectionRecord B k0).input.state.followers i =
            .ordinary before beforeMemory := by
          change B[0].input.state.followers i = .ordinary before beforeMemory
          rw [hzeroB]
          exact hinputCut
        have hcutPendingB : k0.val = 0 → i ∈ out.cutoff.ledger.pending ∧
            out.cutoff.ledger.pending = Finset.univ ∧
            (actualCollectionRecord B k0).input.state.coordinator =
              .live registers owned base ∧
            E.records[w]? = some cutRecord := by
          change k0.val = 0 → i ∈ out.cutoff.ledger.pending ∧
            out.cutoff.ledger.pending = Finset.univ ∧
            B[0].input.state.coordinator = .live registers owned base ∧
            E.records[w]? = some cutRecord
          intro _
          rcases hpending.1 rfl with ⟨hiCut, hpCut, hcoordCut, hindexCut⟩
          exact ⟨hiCut, hpCut, by rw [hzeroB]; exact hcoordCut, hindexCut⟩
        exact ⟨hreply, hlastDown, hS, hdelta, hbacklog, hrow, hfollower, hactivation,
          htime, before, beforeMemory, hinputB, hreplyCut,
          ⟨hcutPendingB, fun hpos => by omega⟩⟩
    · have hkpos : 0 < k.val := by omega
      have hkLe : 1 ≤ k.val := Nat.succ_le_iff.mpr hkpos
      have hklt : k.val < out.ell := lt_of_le_of_lt hkn n.isLt
      let q : Fin out.ell := ⟨k.val, hklt⟩
      have hsubset := initialized_stream_pending_suffix_subset out k.val n.val
        hkLe hkn n.isLt
      have hiK : i ∈ (out.ledgers ⟨k.val - 1,
          Nat.lt_of_le_of_lt (Nat.sub_le _ _) hklt⟩).pending := hsubset hi
      rcases hboundaries q hkpos i hiK with
        ⟨rK, incomingK, cellK, stateK, memoryK, hrK, _htimeK, _hrowsK,
          _hselectedK, _hrewardsK, hincomingK, hiIncomingK, _hreadyK, _hserviceK,
          hstateK, hstatusK, hdomainK, _hSK, _hdeltaK, _hbacklogK, _hmassK,
          _hbankK, _hcompletedK, _hlastK, _hupK, _horiginK⟩
      have hrecordKLookup := hlookupWindow k
      have hrecordKlt : w + k.val < E.records.length :=
        (List.getElem?_eq_some_iff.mp hrecordKLookup).1
      have hjk : j < w + k.val := by
        by_cases hjw : j < w
        · omega
        · simp only [ite_eq_right hjw] at hfk
          omega
      have hrecordK : E.records[w + k.val]'hrecordKlt = B[k.val]'k.isLt :=
        (List.getElem?_eq_some_iff.mp hrecordKLookup).2
      rcases hlookupActualWindow k with ⟨hkWindow, hlookupActualK⟩
      have hwindowEqB : out.window[k.val]'hkWindow = B[k.val]'k.isLt :=
        Option.some.inj (hlookupActualK.symm.trans (hlookupWindow k))
      have hwindowEqK : out.window[k.val]'hkWindow = rK :=
        (List.getElem?_eq_some_iff.mp hrK).2
      have hrecordKState : B[k.val]'k.isLt = rK := hwindowEqB.symm.trans hwindowEqK
      have hstateKB : (actualCollectionRecord B k).input.state.followers i =
          .ordinary stateK memoryK := by
        change (B[k.val]'k.isLt).input.state.followers i = .ordinary stateK memoryK
        rw [hrecordKState]
        exact hstateK
      have hinputK : (E.records[w + k.val]'hrecordKlt).input.state.followers i =
          .ordinary stateK memoryK := by
        rw [hrecordK]
        exact hstateKB
      have hlowerK := retained_down_start_le_of_later_input E.connected i j
        (w + k.val) hjIndex hrecordKlt hjk message hretainedIndex
        stateK memoryK hinputK
      have hpositiveK : 1 ≤ ReferencePrelaunchFollower.acceptedStart stateK := by
        omega
      have hconfigKR := actual_unoccupied_prepare_configuration rK i stateK memoryK
        hstateK hdomainK hstatusK hpositiveK
      have hconfigK :
          (actualCollectionChoice B i k).configuration = .ordinary stateK memoryK := by
        have hchoiceEq := actualCollectionChoice_eq_actualChoice i k rK hrecordKState
        exact (congrArg (fun choice => choice.configuration) hchoiceEq).trans hconfigKR
      have hcutPending : k.val = 0 →
          i ∈ out.cutoff.ledger.pending ∧ out.cutoff.ledger.pending = Finset.univ ∧
          rK.input.state.coordinator = .live registers owned base ∧
          E.records[w]? = some cutRecord := by
        intro hkzero
        omega
      have hpositivePending : ∀ (hkpos : 0 < k.val),
          i ∈ (out.ledgers ⟨k.val - 1,
            Nat.lt_of_le_of_lt (Nat.sub_le _ _) (Nat.lt_of_le_of_lt hkn n.isLt)⟩).pending ∧
          incoming = out.ledgers ⟨n.val - 1,
            Nat.lt_of_le_of_lt (Nat.sub_le _ _) n.isLt⟩ ∧ i ∈ incoming.pending := by
        intro _hkpos
        exact ⟨hiK, hincoming, hiIncoming⟩
      have hlowerChoice : message.val.sigma ≤
          ReferencePrelaunchFollower.acceptedStart stateK := hlowerK
      refine ⟨stateK, memoryK, hconfigK, hstatusK, ?_⟩
      · rcases finishAt k hfk hkn stateK memoryK stateK memoryK rK hrecordKState
          hconfigK hstatusK hstateK rfl hcutPending hpositivePending hlowerChoice with
          ⟨hreply, hlastDown, hS, hdelta, hbacklog, hrow, hfollower, hactivation,
            htime, hpending⟩
        have hcutPendingB : k.val = 0 → i ∈ out.cutoff.ledger.pending ∧
            out.cutoff.ledger.pending = Finset.univ ∧
            (actualCollectionRecord B k).input.state.coordinator =
              .live registers owned base ∧
            E.records[w]? = some cutRecord := by
          intro hkzero
          omega
        have hpositivePendingB : 0 < k.val →
            i ∈ (out.ledgers ⟨k.val - 1,
              Nat.lt_of_le_of_lt (Nat.sub_le _ _) (Nat.lt_of_le_of_lt hkn n.isLt)⟩).pending ∧
            incoming = out.ledgers ⟨n.val - 1,
              Nat.lt_of_le_of_lt (Nat.sub_le _ _) n.isLt⟩ ∧ i ∈ incoming.pending := by
          intro hkpos
          simpa using hpending.2 hkpos
        exact ⟨hreply, hlastDown, hS, hdelta, hbacklog, hrow, hfollower, hactivation,
          htime, stateK, memoryK, hstateKB, rfl, ⟨hcutPendingB, hpositivePendingB⟩⟩

  have hpendingInterval : ∀ (k : Fin B.length) (hkpos : 0 < k.val)
      (hkn : k.val ≤ n.val),
      (out.ledgers ⟨n.val - 1,
        lt_of_le_of_lt (Nat.sub_le _ _) n.isLt⟩).pending ⊆
        (out.ledgers ⟨k.val - 1,
          lt_of_le_of_lt (Nat.sub_le _ _) (lt_of_le_of_lt hkn n.isLt)⟩).pending := by
    intro k hk hkn
    simpa using initialized_stream_pending_suffix_subset out k.val n.val
      (Nat.succ_le_iff.mpr hk) hkn n.isLt

  refine ⟨?_, ?_⟩
  · exact fun k hk hkn => hpendingInterval k hk hkn
  · intro k hfk hkn
    exact hAt k hfk hkn

end Bandits.Support.ReferenceFirstCollectionFormedReplyStateInterval

end
