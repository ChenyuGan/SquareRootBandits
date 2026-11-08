/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveHandoverPhaseReplay

/-!
# Actual first-handover physical service and quota

Sources: ZIP4 `05_binary_transport.tex:244-281`,
`06_interruptions.tex:246-299,431-440`, and
`appendix_a_local_protocol.tex:100-108,141-157`.

The count below is read from the original physical source records. The replay
is used only to identify that count with the stopped receiver's incoming
service sum; its state is not an additional source premise.
-/

@[expose] public section

noncomputable section

open Bandits.Support ConstructorDimensions
open ReferenceFirstLiveHandoverSnapshotPrefix
open ReferenceFirstLiveSourceStoppedHandoverEndpoint
open ReferenceFirstLiveHandoverPhaseReplay
open HandoverStoppedDecoderReplay HandoverStoppedServiceQuota
open ReferenceFollowerDownDecoderReplay ReferenceDownReception
open ActiveFollowerDownAcceptance
open scoped Classical

namespace Bandits.Support.ReferenceFirstLiveHandoverPhysicalQuota

variable {p : ConstructorDimensions.Parameters}

def actionFollowerIndex (i : Fin (p.m - 1)) : ActiveRoundActions.Follower p.m :=
  ⟨i.val, by simp [PublicDiscreteDraws.followerCount]⟩

private theorem actionFollowerIndex_eq (i : Fin (p.m - 1)) :
    actionFollowerIndex i = (i : ActiveRoundActions.Follower p.m) := by
  apply Fin.ext
  rfl

private theorem actionFollowerIndex_apply_eq {α : Type*}
    (f : Fin (p.m - 1) → α) (i : Fin (p.m - 1)) :
    f (actionFollowerIndex i) = f i := by
  congr 1

abbrev Record (rate : ReferenceActivePhysicalStep.RateInput p) :=
  ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)

/-- A positive observation by an unaccepted, selected follower on a DOWN
round, read from the actual prepared physical output. -/
def beforeDownService (rate : ReferenceActivePhysicalStep.RateInput p)
    (i : ActiveRoundActions.Follower p.m) (r : Record rate) : Prop :=
  ∃ incoming memory,
    r.input.state.followers i = .ordinary incoming memory ∧
    incoming.lastDown = none ∧
    ActiveFollowerDownAcceptance.downSelected p i r.input.row r.input.time ∧
    0 < (ReferenceFollowerDownDecoderReplay.preparedOwnObservation r i).val.val

/-- A positive coordinator observation on hash zero after the intended DOWN
word has been accepted. -/
def afterDownService (rate : ReferenceActivePhysicalStep.RateInput p)
    (i : ActiveRoundActions.Follower p.m) (r : Record rate) : Prop :=
  ∃ selected : ReferenceActivePhysicalStep.Selection r.input,
    ReferenceFirstLiveSourceStoppedHandoverEndpoint.actualSelection rate r =
      some selected ∧
    (∃ incoming memory,
      r.input.state.followers i = .ordinary incoming memory ∧
      incoming.lastDown = some (selected.view.payload.downRecord i)) ∧
    ActiveFollowerDownAcceptance.downSelected p i r.input.row r.input.time ∧
    CoordinatorLocalArmChoice.currentDownHash selected.view.payload
      (r.input.row.2 r.input.time) i = 0 ∧
    0 < CoordinatorLocalArmChoice.ownGridObservationValue
      r.output.preparation.coordinatorObservation

/-- The literal physical service indicator, masked by the original stopped
handover support. An absent source record contributes zero. -/
def physicalServiceTerm (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (i : ActiveRoundActions.Follower p.m) (t : Fin p.T) : ℕ :=
  match ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t z with
  | none => 0
  | some r =>
      if i ∈ ReferenceFirstLiveSourceStoppedHandoverEndpoint.pendingNat
          rate rewards C_star C_h t.val z ∧
          (beforeDownService rate i r ∨ afterDownService rate i r) then 1 else 0

/-- Uncapped physical service count on the original calendar prefix. -/
def stoppedServiceSum (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (n : ℕ) : ℕ :=
  ∑ t : Fin p.T, if t.val < n then
    physicalServiceTerm rate rewards C_star C_h z (actionFollowerIndex i) t else 0

/-- The actual first overflow update, on its original one-based endpoint. -/
def actualOverflowAfter (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (t : Fin p.T) : Bool :=
  decide (ReferenceFirstLiveOverflowReadout.wholeFirstLiveOverflowRound
    rate rewards C_star C_h z = some (t.val + 1))

/-- On an eligible auxiliary round, the DOWN word is the fixed word of the
same payload and selected follower. -/
private theorem auxiliary_word_of_eligible
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (n : ℕ) (payload : ReferenceActivePhysicalStep.Payload rate)
    (hp : ReferenceFirstLiveSourceStoppedHandoverEndpoint.payload0
      rate rewards C_star C_h z = some payload)
    (i : Fin (p.m - 1)) (t : Fin p.T)
    (heligible : AffineBatchDecoder.eligible
      (HandoverStoppedDecoderReplay.observationTrace p payload.assignment
        (HandoverStoppedDecoderReplay.fromLive p payload.assignment
          (ReferenceFirstLiveHandoverSnapshotPrefix.auxiliaryLive
            rate rewards C_star C_h z n payload hp)
          (fun _ => false) (actualOverflowAfter rate rewards C_star C_h z))
        (actionFollowerIndex i) t)) :
    (ReferenceFirstLiveHandoverSnapshotPrefix.auxiliaryLive
      rate rewards C_star C_h z n payload hp t).input.down.word =
      HandoverStoppedDecoderReplay.currentWord p
        (CanonicalRecordingRates.beta p rate.eta.val)
        (payload.downRecord (actionFollowerIndex i)) := by
  have hselected := (HandoverStoppedDecoderReplay.eligible_iff p payload.assignment
    (HandoverStoppedDecoderReplay.fromLive p payload.assignment
      (ReferenceFirstLiveHandoverSnapshotPrefix.auxiliaryLive
        rate rewards C_star C_h z n payload hp)
      (fun _ => false) (actualOverflowAfter rate rewards C_star C_h z))
    (actionFollowerIndex i) t).mp heligible
  have hsel : (ReferenceFirstLiveHandoverSnapshotPrefix.auxiliaryLive
      rate rewards C_star C_h z n payload hp t).input.selected = actionFollowerIndex i :=
    hselected.2.1
  have hselInput : (ReferenceFirstLiveHandoverSnapshotPrefix.auxiliaryInput
      payload z t).selected = actionFollowerIndex i := by
    simpa only [ReferenceFirstLiveHandoverSnapshotPrefix.auxiliaryLive_input] using hsel
  rw [ReferenceFirstLiveHandoverSnapshotPrefix.auxiliaryLive_input,
    ReferenceFirstLiveHandoverSnapshotPrefix.auxiliaryInput_decoder_word]
  simp only [hselInput]

/-- The fixed word premise used by the stopped quota applies at every eligible
date in this auxiliary continuation. -/
private theorem auxiliary_hfixed
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (n : ℕ) (payload : ReferenceActivePhysicalStep.Payload rate)
    (hp : ReferenceFirstLiveSourceStoppedHandoverEndpoint.payload0
      rate rewards C_star C_h z = some payload)
    (i : Fin (p.m - 1)) (fixing : Fin p.T)
    (M : HandoverStoppedDecoderReplay.Down p
      (CanonicalRecordingRates.beta p rate.eta.val))
    (hM : M = payload.downRecord (actionFollowerIndex i)) :
    ∀ t, fixing.val ≤ t.val →
      AffineBatchDecoder.eligible
        (HandoverStoppedDecoderReplay.observationTrace p payload.assignment
          (HandoverStoppedDecoderReplay.fromLive p payload.assignment
            (ReferenceFirstLiveHandoverSnapshotPrefix.auxiliaryLive
              rate rewards C_star C_h z n payload hp)
            (fun _ => false) (actualOverflowAfter rate rewards C_star C_h z))
          (actionFollowerIndex i) t) →
      (ReferenceFirstLiveHandoverSnapshotPrefix.auxiliaryLive
        rate rewards C_star C_h z n payload hp t).input.down.word =
        HandoverStoppedDecoderReplay.currentWord p
          (CanonicalRecordingRates.beta p rate.eta.val) M := by
  intro t _ heligible
  rw [hM]
  exact auxiliary_word_of_eligible rate rewards C_star C_h z n payload hp i t heligible

private theorem actual_supported_payload_start
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)
      ).crossing.isSome = true)
    (d : ℕ)
    (hd : d ∈ ReferenceFirstLiveSourceStoppedHandoverEndpoint.supportDates
      rate rewards C_star C_h z) :
    ∃ payload : ReferenceActivePhysicalStep.Payload rate,
      ReferenceFirstLiveSourceStoppedHandoverEndpoint.payload0
        rate rewards C_star C_h z = some payload ∧
      payload.sigma.val = ReferenceFirstLiveHandoverSnapshotPrefix.start
        rate rewards C_star C_h z ∧
      ∀ i : ActiveRoundActions.Follower p.m, (payload.downRecord i).val.sigma =
        ReferenceFirstLiveHandoverSnapshotPrefix.start rate rewards C_star C_h z + 1 := by
  obtain ⟨k, _, _, selected, hselection, hpayload, _⟩ :=
    ReferenceFirstLiveSourceStoppedHandoverEndpoint.supportDates_member_provenance
      rate rewards C_star C_h z d hd
  change ((ReferenceFirstLiveSourceStoppedHandoverEndpoint.window
      rate rewards C_star C_h z).get k).output.preparation.coordinator.selection =
    some selected at hselection
  let s := ReferenceFirstLiveHandoverSnapshotPrefix.start rate rewards C_star C_h z
  let initial := ReferenceFirstLaunchNumericalCell.launchState rate z rewards C_star C_h hc
  let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
    rate z rewards C_star C_h hc
  let count := p.T - s
  have hs : s ≤ p.T := ReferenceCompletePhysicalHistory.physicalStart_le_T rate z rewards C_star C_h
  have hspan : s + count ≤ p.T := by dsimp [count]; omega
  have hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial s := seed.activeAtStart
  let R := ReferenceFirstWindowNumericalStream.actualFirstLiveRun
    rate z rewards C_star C_h hc count hspan
  let W := ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
    rate z rewards C_star C_h hc count hspan
  have hcomplete : R.records = ReferenceFirstLiveSourceStoppedHandoverEndpoint.completeRecords
      rate rewards C_star C_h z := by
    exact (ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch rate z rewards
      C_star C_h initial
      (ReferenceFirstLaunchNumericalCell.actual_launch_seed rate z rewards C_star C_h hc).1).symm
  have hwindow : W = ReferenceFirstLiveSourceStoppedHandoverEndpoint.window
      rate rewards C_star C_h z := by
    change ReferenceFirstLiveConfirmationHistory.firstLiveWindow R.records =
      ReferenceFirstLiveConfirmationHistory.firstLiveWindow _
    rw [hcomplete]
  have hgeometry :
      ∀ (j : Fin (ReferenceFirstLiveSourceStoppedHandoverEndpoint.window
          rate rewards C_star C_h z).length)
        (chosen : ReferenceActivePhysicalStep.Selection
          ((ReferenceFirstLiveSourceStoppedHandoverEndpoint.window
            rate rewards C_star C_h z).get j).input),
        ((ReferenceFirstLiveSourceStoppedHandoverEndpoint.window
          rate rewards C_star C_h z).get j).output.preparation.coordinator.selection =
          some chosen → chosen.view.payload.sigma.val = s := by
    rw [← hwindow]
    intro j chosen hchosen
    exact (ReferenceFirstLiveDownNumericalRecovery.first_live_geometry
      initial z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s count hspan
      hmode seed.coordinatorFirst j chosen hchosen).1
  refine ⟨selected.view.payload, hpayload, ?_, ?_⟩
  · have hgeometry := hgeometry k selected hselection
    simpa [s] using hgeometry
  · intro i
    have hsigma : selected.view.payload.sigma.val = s :=
      hgeometry k selected hselection
    have hfields := congrArg OrdinaryMessageCodec.DownFields.sigma
      (selected.view.payload.downRecord_fields i)
    change (selected.view.payload.downRecord i).val.sigma =
      selected.view.payload.sigma.val + 1 at hfields
    rw [hfields, hsigma]

private theorem actual_auxiliary_quota_inputs
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)
      ).crossing.isSome = true)
    (n : ℕ) (hnonempty : (ReferenceFirstLiveHandoverSnapshotPrefix.prefixDates
      rate rewards C_star C_h z n).Nonempty)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (hp : ReferenceFirstLiveSourceStoppedHandoverEndpoint.payload0
      rate rewards C_star C_h z = some payload) (i : Fin (p.m - 1)) :
    let live := ReferenceFirstLiveHandoverSnapshotPrefix.auxiliaryLive
      rate rewards C_star C_h z n payload hp
    let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
      rate z rewards C_star C_h hc
    let fixing : Fin p.T := payload.sigma
    let M : HandoverStoppedDecoderReplay.Down p
      (CanonicalRecordingRates.beta p rate.eta.val) :=
        payload.downRecord (actionFollowerIndex i)
    let d0 := (seed.followers i).downBatch
    WaitedWordWindow.sourceRound fixing = M.val.sigma ∧
    0 < M.val.sigma ∧
    d0.pending.length < AffineBatchDecoder.quota p ∧
    (∀ e, e ∈ d0.pending → e.time.val < fixing.val) ∧
    (∀ t, fixing.val ≤ t.val →
      AffineBatchDecoder.eligible
        (ActiveObservationBridge.downObservationTrace p payload.assignment live
          (actionFollowerIndex i) t) →
      (live t).input.down.word = HandoverStoppedDecoderReplay.currentWord
        p (CanonicalRecordingRates.beta p rate.eta.val) M) := by
  let s := ReferenceFirstLiveHandoverSnapshotPrefix.start rate rewards C_star C_h z
  let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
    rate z rewards C_star C_h hc
  let fixing : Fin p.T := payload.sigma
  let M : HandoverStoppedDecoderReplay.Down p
      (CanonicalRecordingRates.beta p rate.eta.val) :=
    payload.downRecord (actionFollowerIndex i)
  let live := ReferenceFirstLiveHandoverSnapshotPrefix.auxiliaryLive
    rate rewards C_star C_h z n payload hp
  have hS : (ReferenceFirstLiveHandoverSnapshotPrefix.prefixDates
      rate rewards C_star C_h z n).Nonempty := hnonempty
  have hsigmaPayload : payload.sigma.val = s := by
    obtain ⟨t, ht⟩ := hS
    have hmem := Finset.mem_filter.mp ht
    have hd : t.val + 1 ∈ ReferenceFirstLiveSourceStoppedHandoverEndpoint.supportDates
        rate rewards C_star C_h z := hmem.2.2.2
    obtain ⟨payload', hpayload', hsigma', _⟩ :=
      actual_supported_payload_start
        rate rewards C_star C_h z hc (t.val + 1) hd
    have hpayloadEq : payload' = payload := Option.some.inj (hpayload'.symm.trans hp)
    subst payload'
    exact hsigma'
  have hfields := congrArg OrdinaryMessageCodec.DownFields.sigma
    (payload.downRecord_fields (actionFollowerIndex i))
  have hrecordStamp : M.val.sigma = s + 1 := by
    change (payload.downRecord (actionFollowerIndex i)).val.sigma =
      payload.sigma.val + 1 at hfields
    rw [hsigmaPayload] at hfields
    exact hfields
  have hsource : WaitedWordWindow.sourceRound fixing = M.val.sigma := by
    change payload.sigma.val + 1 = M.val.sigma
    rw [hsigmaPayload]
    exact hrecordStamp.symm
  have hholder : 0 < M.val.sigma := by rw [hrecordStamp]; omega
  obtain ⟨state, memory, hstate, _hlast, _hstatus, hwell, _hchron, hstamps⟩ :=
    ReferenceFirstLiveDownCompletionReadout.actual_corrected_decoder_seed
      rate z rewards C_star C_h hc i
  have hstateEq : state = seed.followers i := by
    exact (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
      (hstate.symm.trans (seed.configuration i))).1
  let d0 := (seed.followers i).downBatch
  have hd0 : d0 = state.downBatch :=
    congrArg (fun st : ReferencePrelaunchFollower.State p rate.eta => st.downBatch)
      hstateEq.symm
  have hquota : d0.pending.length < AffineBatchDecoder.quota p := by
    rw [hd0]
    exact hwell.1
  have hfixingStart : fixing.val = ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed := by
    change payload.sigma.val = ReferenceFirstLiveHandoverSnapshotPrefix.start
      rate rewards C_star C_h z
    rw [hsigmaPayload]
  have hpending : ∀ e, e ∈ d0.pending → e.time.val < fixing.val := by
    intro e he
    have he' : e ∈ state.downBatch.pending := by rw [hd0] at he; exact he
    have hcollected : e ∈ AffineBatchDecoder.collected state.downBatch := by
      rw [AffineBatchDecoder.collected]
      exact List.mem_append_right _ he'
    have hstamp := hstamps e hcollected
    rw [hfixingStart]
    exact hstamp
  have hfixedAux := auxiliary_hfixed
    rate rewards C_star C_h z n payload hp i fixing M rfl
  have cutoffBefore : Fin p.T → Bool := fun _ => false
  have overflowAfter := actualOverflowAfter rate rewards C_star C_h z
  have hfixed : ∀ t, fixing.val ≤ t.val →
      AffineBatchDecoder.eligible
        (ActiveObservationBridge.downObservationTrace p payload.assignment live
          (actionFollowerIndex i) t) →
      (live t).input.down.word = HandoverStoppedDecoderReplay.currentWord
        p (CanonicalRecordingRates.beta p rate.eta.val) M := by
    intro t ht heligible
    have heligible' : AffineBatchDecoder.eligible
        (HandoverStoppedDecoderReplay.observationTrace p payload.assignment
          (HandoverStoppedDecoderReplay.fromLive p payload.assignment live
            cutoffBefore overflowAfter) (actionFollowerIndex i) t) := by
      have htrace := congrFun (HandoverStoppedDecoderReplay.observationTrace_fromLive
        p payload.assignment live cutoffBefore overflowAfter (actionFollowerIndex i)) t
      rw [htrace]
      exact heligible
    exact hfixedAux t ht heligible'
  exact ⟨hsource, hholder, hquota, hpending, hfixed⟩

private theorem physical_prefix_term_eq_auxiliary
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (n : ℕ) (hnonempty : (ReferenceFirstLiveHandoverSnapshotPrefix.prefixDates
      rate rewards C_star C_h z n).Nonempty)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)
      ).crossing.isSome = true)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (hp : ReferenceFirstLiveSourceStoppedHandoverEndpoint.payload0
      rate rewards C_star C_h z = some payload)
    (i : ActiveRoundActions.Follower p.m) (t : Fin p.T)
    (ht : t ∈ ReferenceFirstLiveHandoverSnapshotPrefix.prefixDates
      rate rewards C_star C_h z n) :
    let live := ReferenceFirstLiveHandoverSnapshotPrefix.auxiliaryLive
      rate rewards C_star C_h z n payload hp
    let data := HandoverStoppedDecoderReplay.fromLive p payload.assignment live
      (fun _ => false) (fun u => decide
        (ReferenceFirstLiveOverflowReadout.wholeFirstLiveOverflowRound rate rewards C_star C_h z =
          some (u.val + 1)))
    let q := HandoverStoppedDecoderReplay.snapshotBefore p
      (CanonicalRecordingRates.beta p rate.eta.val) payload.assignment data
      i payload.sigma
      (payload.downRecord i) (HandoverStoppedDecoderReplay.initial p
        ((ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
          rate z rewards C_star C_h hc).followers i).downBatch 0) t.val
    physicalServiceTerm rate rewards C_star C_h z i t =
      HandoverStoppedDecoderReplay.J p payload.assignment data payload.sigma q t *
      HandoverStoppedDecoderReplay.X p payload.assignment data i q t := by
  classical
  let live := ReferenceFirstLiveHandoverSnapshotPrefix.auxiliaryLive
    rate rewards C_star C_h z n payload hp
  let data := HandoverStoppedDecoderReplay.fromLive p payload.assignment live
    (fun _ => false) (fun u => decide
      (ReferenceFirstLiveOverflowReadout.wholeFirstLiveOverflowRound rate rewards C_star C_h z =
        some (u.val + 1)))
  let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
    rate z rewards C_star C_h hc
  let initial := HandoverStoppedDecoderReplay.initial p
    (seed.followers i).downBatch 0
  let q := HandoverStoppedDecoderReplay.snapshotBefore p
    (CanonicalRecordingRates.beta p rate.eta.val) payload.assignment data
    i payload.sigma
    (payload.downRecord i) initial t.val
  have hcorr := ReferenceFirstLiveHandoverPhaseReplay.actual_prefix_correspondence
    rate rewards C_star C_h z n
  have hsupport : (ReferenceFirstLiveSourceStoppedHandoverEndpoint.supportDates
      rate rewards C_star C_h z).Nonempty := by
    obtain ⟨u, hu⟩ := hnonempty
    exact ⟨u.val + 1, (Finset.mem_filter.mp hu).2.2.2⟩
  rcases hcorr with hempty | ⟨payload', hp', hc', hsigma, hstamps, hforall⟩
  · exact False.elim ((Finset.nonempty_iff_ne_empty.mp hnonempty) hempty)
  have hpayload : payload' = payload := Option.some.inj (hp'.symm.trans hp)
  subst payload'
  have hhp : hp' = hp := Subsingleton.elim _ _
  rw [hhp] at hforall
  obtain ⟨r, states, memories, hrecord, htime, hmissing, hstateData⟩ := hforall t ht
  obtain ⟨hinput, _hprepared, _hstatus, _hphase, _hlocal, _hJ, hJX⟩ := hstateData i
  have hselectionData := ReferenceFirstLiveSourceStoppedHandoverEndpoint.supportDates_member_provenance
    rate rewards C_star C_h z (t.val + 1) ((Finset.mem_filter.mp ht).2.2.2)
  obtain ⟨k, hdate, _hrecordAtDate, selected, hselection, hpayloadAtDate, _⟩ := hselectionData
  let sourceRecord := (ReferenceFirstLiveSourceStoppedHandoverEndpoint.window
    rate rewards C_star C_h z).get k
  have hsourceTime : sourceRecord.input.time = t := by
    apply Fin.ext
    change sourceRecord.input.time.val + 1 = t.val + 1 at hdate
    exact Nat.add_right_cancel hdate
  have hsourceLookup := (ReferenceFirstLiveSourceStoppedHandoverEndpoint.source_window_record_calendar
    rate rewards C_star C_h z k).2
  change ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
      sourceRecord.input.time z = some sourceRecord at hsourceLookup
  rw [hsourceTime] at hsourceLookup
  have hrecordEq : r = sourceRecord := Option.some.inj (hrecord.symm.trans hsourceLookup)
  subst r
  let r := sourceRecord
  have hselectedPayload : selected.view.payload = payload :=
    Option.some.inj (hpayloadAtDate.symm.trans hp)
  have hbefore : beforeDownService rate i r ↔
      (states i).lastDown = none ∧
        ActiveFollowerDownAcceptance.downSelected p i r.input.row r.input.time ∧
        0 < (ReferenceFollowerDownDecoderReplay.preparedOwnObservation r i).val.val := by
    constructor
    · rintro ⟨incoming, memory, hin, hnone, hdown, hpositive⟩
      have heq : incoming = states i := by
        have h := hin.symm.trans (hinput)
        cases h
        rfl
      subst incoming
      exact ⟨hnone, hdown, hpositive⟩
    · rintro ⟨hnone, hdown, hpositive⟩
      exact ⟨states i, memories i, hinput, hnone, hdown, hpositive⟩
  have hafter : afterDownService rate i r ↔
      (states i).lastDown = some (payload.downRecord i) ∧
        ActiveFollowerDownAcceptance.downSelected p i r.input.row r.input.time ∧
        CoordinatorLocalArmChoice.currentDownHash payload (r.input.row.2 r.input.time)
          i = 0 ∧
        0 < CoordinatorLocalArmChoice.ownGridObservationValue
          r.output.preparation.coordinatorObservation := by
    constructor
    · rintro ⟨actual, hactual, hordinary, hdown, hhash, hpositive⟩
      have hactual' : actual = selected := Option.some.inj (hactual.symm.trans hselection)
      subst actual
      obtain ⟨incoming, memory, hin, hlast⟩ := hordinary
      have heq : incoming = states i := by
        have h := hin.symm.trans hinput
        cases h
        rfl
      subst incoming
      rw [hselectedPayload] at hlast hhash
      exact ⟨hlast, hdown, hhash, hpositive⟩
    · rintro ⟨hlast, hdown, hhash, hpositive⟩
      refine ⟨selected, ?_, ?_, hdown, ?_, hpositive⟩
      · exact hselection
      · exact ⟨states i, memories i, hinput, by rw [hselectedPayload]; exact hlast⟩
      · have hhash' := hhash
        rw [← hselectedPayload] at hhash'
        exact hhash'
  have hpredicate :
      (i ∈ ReferenceFirstLiveSourceStoppedHandoverEndpoint.pendingNat
          rate rewards C_star C_h t.val z ∧
        (beforeDownService rate i r ∨ afterDownService rate i r)) ↔
      (i ∈ ReferenceFirstLiveSourceStoppedHandoverEndpoint.pendingNat
          rate rewards C_star C_h t.val z ∧
        ActiveFollowerDownAcceptance.downSelected p i r.input.row r.input.time ∧
        (((states i).lastDown = none ∧
            0 < (ReferenceFollowerDownDecoderReplay.preparedOwnObservation r i).val.val) ∨
          ((states i).lastDown = some (payload.downRecord i) ∧
            CoordinatorLocalArmChoice.currentDownHash payload
              (r.input.row.2 r.input.time) i = 0 ∧
            0 < CoordinatorLocalArmChoice.ownGridObservationValue
              r.output.preparation.coordinatorObservation))) := by
    constructor
    · rintro ⟨hi, hb | ha⟩
      · exact ⟨hi, (hbefore.mp hb).2.1, Or.inl ⟨(hbefore.mp hb).1, (hbefore.mp hb).2.2⟩⟩
      · obtain ⟨hlast, hdown, hhash, hpositive⟩ := hafter.mp ha
        exact ⟨hi, hdown, Or.inr ⟨hlast, hhash, hpositive⟩⟩
    · rintro ⟨hi, hdown, hb | ha⟩
      · exact ⟨hi, Or.inl (hbefore.mpr ⟨hb.1, hdown, hb.2⟩)⟩
      · exact ⟨hi, Or.inr (hafter.mpr ⟨ha.1, hdown, ha.2.1, ha.2.2⟩)⟩
  have hhc : hc' = hc := Subsingleton.elim _ _
  have hJX' := hJX
  rw [hhc] at hJX'
  have hservice :
      HandoverStoppedDecoderReplay.J p payload.assignment data payload.sigma q t *
        HandoverStoppedDecoderReplay.X p payload.assignment data i q t =
      (if i ∈ ReferenceFirstLiveSourceStoppedHandoverEndpoint.pendingNat
          rate rewards C_star C_h t.val z ∧
        ActiveFollowerDownAcceptance.downSelected p i r.input.row r.input.time ∧
        (((states i).lastDown = none ∧
            0 < (ReferenceFollowerDownDecoderReplay.preparedOwnObservation r i).val.val) ∨
          ((states i).lastDown = some (payload.downRecord i) ∧
            CoordinatorLocalArmChoice.currentDownHash payload
              (r.input.row.2 r.input.time) i = 0 ∧
            0 < CoordinatorLocalArmChoice.ownGridObservationValue
              r.output.preparation.coordinatorObservation)) then 1 else 0) := by
    simpa only [live, data, q, initial, seed, r, htime] using hJX'
  have hindicator :
      (if i ∈ ReferenceFirstLiveSourceStoppedHandoverEndpoint.pendingNat
          rate rewards C_star C_h t.val z ∧
        (beforeDownService rate i r ∨ afterDownService rate i r) then 1 else 0) =
      (if i ∈ ReferenceFirstLiveSourceStoppedHandoverEndpoint.pendingNat
          rate rewards C_star C_h t.val z ∧
        ActiveFollowerDownAcceptance.downSelected p i r.input.row r.input.time ∧
        (((states i).lastDown = none ∧
            0 < (ReferenceFollowerDownDecoderReplay.preparedOwnObservation r i).val.val) ∨
          ((states i).lastDown = some (payload.downRecord i) ∧
            CoordinatorLocalArmChoice.currentDownHash payload
              (r.input.row.2 r.input.time) i = 0 ∧
            0 < CoordinatorLocalArmChoice.ownGridObservationValue
              r.output.preparation.coordinatorObservation)) then 1 else 0) :=
    by
      by_cases h : i ∈ ReferenceFirstLiveSourceStoppedHandoverEndpoint.pendingNat
        rate rewards C_star C_h t.val z ∧
        (beforeDownService rate i r ∨ afterDownService rate i r)
      · have h' := hpredicate.mp h
        simp only [ite_eq_left h, ite_eq_left h']
      · have h' : ¬ (i ∈ ReferenceFirstLiveSourceStoppedHandoverEndpoint.pendingNat
          rate rewards C_star C_h t.val z ∧
          ActiveFollowerDownAcceptance.downSelected p i r.input.row r.input.time ∧
          (((states i).lastDown = none ∧
              0 < (ReferenceFollowerDownDecoderReplay.preparedOwnObservation r i).val.val) ∨
            ((states i).lastDown = some (payload.downRecord i) ∧
              CoordinatorLocalArmChoice.currentDownHash payload
                (r.input.row.2 r.input.time) i = 0 ∧
              0 < CoordinatorLocalArmChoice.ownGridObservationValue
                r.output.preparation.coordinatorObservation))) := by
          intro h'
          exact h (hpredicate.mpr h')
        simp only [ite_eq_right h, ite_eq_right h']
  have hphysical : physicalServiceTerm rate rewards C_star C_h z i t =
      (if i ∈ ReferenceFirstLiveSourceStoppedHandoverEndpoint.pendingNat
          rate rewards C_star C_h t.val z ∧
        (beforeDownService rate i r ∨ afterDownService rate i r) then 1 else 0) := by
    simp only [physicalServiceTerm, hrecord, r]
  calc
    physicalServiceTerm rate rewards C_star C_h z i t =
        (if i ∈ ReferenceFirstLiveSourceStoppedHandoverEndpoint.pendingNat
            rate rewards C_star C_h t.val z ∧
          (beforeDownService rate i r ∨ afterDownService rate i r) then 1 else 0) := hphysical
    _ = (if i ∈ ReferenceFirstLiveSourceStoppedHandoverEndpoint.pendingNat
            rate rewards C_star C_h t.val z ∧
          ActiveFollowerDownAcceptance.downSelected p i r.input.row r.input.time ∧
          (((states i).lastDown = none ∧
              0 < (ReferenceFollowerDownDecoderReplay.preparedOwnObservation r i).val.val) ∨
            ((states i).lastDown = some (payload.downRecord i) ∧
              CoordinatorLocalArmChoice.currentDownHash payload
                (r.input.row.2 r.input.time) i = 0 ∧
              0 < CoordinatorLocalArmChoice.ownGridObservationValue
                r.output.preparation.coordinatorObservation)) then 1 else 0) := hindicator
    _ = HandoverStoppedDecoderReplay.J p payload.assignment data payload.sigma q t *
        HandoverStoppedDecoderReplay.X p payload.assignment data i q t := hservice.symm

private theorem physical_prefix_eq_N_before
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (n : ℕ) (hnonempty : (ReferenceFirstLiveHandoverSnapshotPrefix.prefixDates
      rate rewards C_star C_h z n).Nonempty)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)
      ).crossing.isSome = true)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (hp : ReferenceFirstLiveSourceStoppedHandoverEndpoint.payload0
      rate rewards C_star C_h z = some payload)
    (i : Fin (p.m - 1)) (k : ℕ) (hk : k ≤ n)
    (_hstop : k ≤ ReferenceFirstLiveHandoverSnapshotPrefix.stop
      rate rewards C_star C_h z n) :
    stoppedServiceSum rate rewards C_star C_h z i k =
      HandoverStoppedDecoderReplay.N_before p
        (CanonicalRecordingRates.beta p rate.eta.val) payload.assignment
        (HandoverStoppedDecoderReplay.fromLive p payload.assignment
          (ReferenceFirstLiveHandoverSnapshotPrefix.auxiliaryLive
            rate rewards C_star C_h z n payload hp)
        (fun _ => false) (actualOverflowAfter rate rewards C_star C_h z))
        (actionFollowerIndex i) payload.sigma
        (payload.downRecord (actionFollowerIndex i))
        (HandoverStoppedDecoderReplay.initial p
          ((ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
            rate z rewards C_star C_h hc).followers i).downBatch 0) k := by
  classical
  let live := ReferenceFirstLiveHandoverSnapshotPrefix.auxiliaryLive
    rate rewards C_star C_h z n payload hp
  let data := HandoverStoppedDecoderReplay.fromLive p payload.assignment live
    (fun _ => false) (fun u => decide
      (ReferenceFirstLiveOverflowReadout.wholeFirstLiveOverflowRound rate rewards C_star C_h z =
        some (u.val + 1)))
  let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
    rate z rewards C_star C_h hc
  let initial := HandoverStoppedDecoderReplay.initial p (seed.followers i).downBatch 0
  let fixing : Fin p.T := payload.sigma
  let M : HandoverStoppedDecoderReplay.Down p
      (CanonicalRecordingRates.beta p rate.eta.val) :=
        payload.downRecord (actionFollowerIndex i)
  have hsupport : (ReferenceFirstLiveSourceStoppedHandoverEndpoint.supportDates
      rate rewards C_star C_h z).Nonempty := by
    obtain ⟨u, hu⟩ := hnonempty
    exact ⟨u.val + 1, (Finset.mem_filter.mp hu).2.2.2⟩
  have hfixStart : ReferenceFirstLiveHandoverSnapshotPrefix.start
      rate rewards C_star C_h z =
      ReferenceFirstLiveSourceStoppedReleaseEndpoint.physicalStart
        rate rewards C_star C_h z := rfl
  have hsigma := ReferenceFirstLiveSourceStoppedHandoverEndpoint.sigma_eq_physicalStart_succ
    rate rewards C_star C_h z hsupport
  rw [← hfixStart] at hsigma
  have hsum : ∀ t : Fin p.T, t.val < k →
      physicalServiceTerm rate rewards C_star C_h z (actionFollowerIndex i) t =
        HandoverStoppedDecoderReplay.J p payload.assignment data fixing
          (HandoverStoppedDecoderReplay.snapshotBefore p
            (CanonicalRecordingRates.beta p rate.eta.val) payload.assignment data
            (actionFollowerIndex i) fixing M
            initial t.val) t *
        HandoverStoppedDecoderReplay.X p payload.assignment data (actionFollowerIndex i)
          (HandoverStoppedDecoderReplay.snapshotBefore p
            (CanonicalRecordingRates.beta p rate.eta.val) payload.assignment data
            (actionFollowerIndex i) fixing M
            initial t.val) t := by
    intro t htk
    have htn : t.val < n := lt_of_lt_of_le htk hk
    by_cases hd : t.val + 1 ∈ ReferenceFirstLiveSourceStoppedHandoverEndpoint.supportDates
        rate rewards C_star C_h z
    · have hinterval := ReferenceFirstLiveSourceStoppedHandoverEndpoint.supportDates_subset_interval
        rate rewards C_star C_h z hd
      have hlow : ReferenceFirstLiveHandoverSnapshotPrefix.start
          rate rewards C_star C_h z ≤ t.val := by
        have h := (Finset.mem_Ico.mp hinterval).1
        rw [hsigma] at h
        omega
      have hhigh : t.val < ReferenceFirstLiveSourceStoppedHandoverEndpoint.theta
          rate rewards C_star C_h z - 1 := by
        have h := (Finset.mem_Ico.mp hinterval).2
        omega
      have hprefix : t ∈ ReferenceFirstLiveHandoverSnapshotPrefix.prefixDates
          rate rewards C_star C_h z n := by
        simp only [ReferenceFirstLiveHandoverSnapshotPrefix.prefixDates,
          Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨hlow, ?_, hd⟩
        simp only [ReferenceFirstLiveHandoverSnapshotPrefix.stop, lt_min_iff]
        exact ⟨htn, hhigh⟩
      have hterm := physical_prefix_term_eq_auxiliary rate rewards C_star C_h z n
        hnonempty hc payload hp (actionFollowerIndex i) t hprefix
      have hseedIndex := actionFollowerIndex_apply_eq
        (ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
          rate z rewards C_star C_h hc).followers i
      rw [hseedIndex] at hterm
      simpa only [live, data, seed, initial, fixing, M] using hterm
    · have hpending : ReferenceFirstLiveSourceStoppedHandoverEndpoint.pendingNat
          rate rewards C_star C_h t.val z = ∅ := by
        by_contra hne
        have hne' := (ReferenceFirstLiveSourceStoppedHandoverEndpoint.pendingNat_nonempty_iff
          rate rewards C_star C_h z t.val).mp (Finset.nonempty_iff_ne_empty.mpr hne)
        exact hd hne'
      have hzero := ReferenceFirstLiveHandoverPhaseReplay.off_support_X_zero
        rate rewards C_star C_h z n payload hp hsupport (actionFollowerIndex i)
        (HandoverStoppedDecoderReplay.snapshotBefore p
          (CanonicalRecordingRates.beta p rate.eta.val) payload.assignment data
            (actionFollowerIndex i) fixing M
          initial t.val) t hd
      have hzero' : HandoverStoppedDecoderReplay.X p payload.assignment data
          (actionFollowerIndex i)
          (HandoverStoppedDecoderReplay.snapshotBefore p
            (CanonicalRecordingRates.beta p rate.eta.val) payload.assignment data
            (actionFollowerIndex i) fixing M
            initial t.val) t = 0 := by
        change HandoverStoppedDecoderReplay.X p payload.assignment
          (HandoverStoppedDecoderReplay.fromLive p payload.assignment live (fun _ => false)
            (fun u => decide (ReferenceFirstLiveOverflowReadout.wholeFirstLiveOverflowRound
              rate rewards C_star C_h z = some (u.val + 1)))) (actionFollowerIndex i)
          (HandoverStoppedDecoderReplay.snapshotBefore p
            (CanonicalRecordingRates.beta p rate.eta.val) payload.assignment
            (HandoverStoppedDecoderReplay.fromLive p payload.assignment live (fun _ => false)
              (actualOverflowAfter rate rewards C_star C_h z))
            (actionFollowerIndex i) fixing M initial t.val) t = 0
        exact hzero
      cases hactual : ReferenceSourcePrefixHistoryFiltration.actualRecord
          rate rewards C_star C_h t z with
      | none => simp only [physicalServiceTerm, hactual, hzero', Nat.mul_zero]
      | some r =>
          have hnot : ¬ actionFollowerIndex i ∈
              (∅ : Finset (Fin (p.m - 1))) := by
            exact Finset.notMem_empty _
          simp [physicalServiceTerm, hactual, hpending, hnot, hzero']
  unfold stoppedServiceSum
  unfold HandoverStoppedDecoderReplay.N_before
  apply Finset.sum_congr rfl
  intro t _
  by_cases htk : t.val < k
  · simp only [ite_eq_left htk]
    exact hsum t htk
  · simp only [ite_eq_right htk]

private theorem actual_auxiliary_N_before_le_twoQ_add_one
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)
      ).crossing.isSome = true)
    (n : ℕ)
    (hnonempty : (ReferenceFirstLiveHandoverSnapshotPrefix.prefixDates
      rate rewards C_star C_h z n).Nonempty)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (hp : ReferenceFirstLiveSourceStoppedHandoverEndpoint.payload0
      rate rewards C_star C_h z = some payload)
    (i : Fin (p.m - 1)) (k : ℕ) :
    HandoverStoppedDecoderReplay.N_before p
        (CanonicalRecordingRates.beta p rate.eta.val) payload.assignment
        (HandoverStoppedDecoderReplay.fromLive p payload.assignment
          (ReferenceFirstLiveHandoverSnapshotPrefix.auxiliaryLive
            rate rewards C_star C_h z n payload hp)
          (fun _ => false) (actualOverflowAfter rate rewards C_star C_h z))
        (actionFollowerIndex i) payload.sigma
        (payload.downRecord (actionFollowerIndex i))
        (HandoverStoppedDecoderReplay.initial p
          ((ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
            rate z rewards C_star C_h hc).followers i).downBatch 0) k ≤
      2 * AffineBatchDecoder.quota p + 1 := by
  let live := ReferenceFirstLiveHandoverSnapshotPrefix.auxiliaryLive
    rate rewards C_star C_h z n payload hp
  let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
    rate z rewards C_star C_h hc
  let fixing : Fin p.T := payload.sigma
  let M : HandoverStoppedDecoderReplay.Down p
      (CanonicalRecordingRates.beta p rate.eta.val) := payload.downRecord (actionFollowerIndex i)
  let d0 := (seed.followers i).downBatch
  let cutoffBefore : Fin p.T → Bool := fun _ => false
  let overflowAfter := actualOverflowAfter rate rewards C_star C_h z
  rcases actual_auxiliary_quota_inputs rate rewards C_star C_h z hc n hnonempty
      payload hp i with ⟨hsource, hholder, hquota, hpending, hfixed⟩
  exact HandoverStoppedServiceQuota.N_before_le_twoQ_add_one
    p (CanonicalRecordingRates.beta p rate.eta.val) payload.assignment live cutoffBefore
    overflowAfter (actionFollowerIndex i) fixing M 0 d0 hsource hholder hquota hpending
    hfixed k

private theorem stoppedServiceSum_eq_zero_of_empty_prefix
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (n : ℕ)
    (hempty : ReferenceFirstLiveHandoverSnapshotPrefix.prefixDates
      rate rewards C_star C_h z n = ∅) :
    stoppedServiceSum rate rewards C_star C_h z i n = 0 := by
  unfold stoppedServiceSum
  apply Finset.sum_eq_zero
  intro t ht
  by_cases htn : t.val < n
  · cases hrecord : ReferenceSourcePrefixHistoryFiltration.actualRecord
        rate rewards C_star C_h t z with
    | none => simp [htn, physicalServiceTerm, hrecord]
    | some r =>
        have hpending : ReferenceFirstLiveSourceStoppedHandoverEndpoint.pendingNat
            rate rewards C_star C_h t.val z = ∅ := by
          by_contra hne
          have hnonempty : (ReferenceFirstLiveSourceStoppedHandoverEndpoint.pendingNat
              rate rewards C_star C_h t.val z).Nonempty :=
            Finset.nonempty_iff_ne_empty.mpr hne
          have hdate := (ReferenceFirstLiveSourceStoppedHandoverEndpoint.pendingNat_nonempty_iff
            rate rewards C_star C_h z t.val).mp hnonempty
          have hneSupport : (ReferenceFirstLiveSourceStoppedHandoverEndpoint.supportDates
              rate rewards C_star C_h z).Nonempty := ⟨t.val + 1, hdate⟩
          have hsig := ReferenceFirstLiveSourceStoppedHandoverEndpoint.sigma_eq_physicalStart_succ
            rate rewards C_star C_h z hneSupport
          have hstart : ReferenceFirstLiveSourceStoppedReleaseEndpoint.physicalStart
              rate rewards C_star C_h z =
              ReferenceFirstLiveHandoverSnapshotPrefix.start rate rewards C_star C_h z := rfl
          rw [hstart] at hsig
          have hinterval := ReferenceFirstLiveSourceStoppedHandoverEndpoint.supportDates_subset_interval
            rate rewards C_star C_h z hdate
          have hlow := (Finset.mem_Ico.mp hinterval).1
          have hhigh := (Finset.mem_Ico.mp hinterval).2
          have hs : ReferenceFirstLiveHandoverSnapshotPrefix.start
              rate rewards C_star C_h z ≤ t.val := by omega
          have hstop : t.val < ReferenceFirstLiveHandoverSnapshotPrefix.stop
              rate rewards C_star C_h z n := by
            simp only [ReferenceFirstLiveHandoverSnapshotPrefix.stop, lt_min_iff]
            omega
          have hmember : t ∈ ReferenceFirstLiveHandoverSnapshotPrefix.prefixDates
              rate rewards C_star C_h z n := by
            simp only [ReferenceFirstLiveHandoverSnapshotPrefix.prefixDates,
              Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨hs, hstop, hdate⟩
          simp [hempty] at hmember
        have hnot : ¬ actionFollowerIndex i ∈
            (∅ : Finset (Fin (p.m - 1))) := by
          exact Finset.notMem_empty _
        simp [htn, physicalServiceTerm, hrecord, hpending, hnot]
  · simp [htn]

/-- The actual physical count through the first-handover stopped endpoint is
bounded by two initialized receiver batches and one genuine confirmation. -/
theorem actualStoppedServiceSum_le_twoQ_add_one
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (n : ℕ) :
    stoppedServiceSum rate rewards C_star C_h z i
        (min n (ReferenceFirstLiveSourceStoppedHandoverEndpoint.theta
          rate rewards C_star C_h z - 1)) ≤
      2 * AffineBatchDecoder.quota p + 1 := by
  classical
  let m := min n (ReferenceFirstLiveSourceStoppedHandoverEndpoint.theta
    rate rewards C_star C_h z - 1)
  by_cases hempty : ReferenceFirstLiveHandoverSnapshotPrefix.prefixDates
      rate rewards C_star C_h z n = ∅
  · have hzero := stoppedServiceSum_eq_zero_of_empty_prefix
      rate rewards C_star C_h z i n hempty
    have hmono : stoppedServiceSum rate rewards C_star C_h z i m ≤
        stoppedServiceSum rate rewards C_star C_h z i n := by
      unfold stoppedServiceSum
      apply Finset.sum_le_sum
      intro t _
      by_cases htm : t.val < m
      · have htn : t.val < n := lt_of_lt_of_le htm (Nat.min_le_left _ _)
        simp only [ite_eq_left htm, ite_eq_left htn]
        exact le_rfl
      · simp only [ite_eq_right htm]
        exact Nat.zero_le _
    rw [hzero] at hmono
    have hsumzero : stoppedServiceSum rate rewards C_star C_h z i m = 0 := by omega
    rw [hsumzero]
    exact Nat.zero_le _
  · have hnonempty : (ReferenceFirstLiveHandoverSnapshotPrefix.prefixDates
        rate rewards C_star C_h z n).Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hempty
    obtain ⟨payload, hp, hc, _hsigma, _hstamps, _hforall⟩ :=
      (ReferenceFirstLiveHandoverPhaseReplay.actual_prefix_correspondence
        rate rewards C_star C_h z n).resolve_left hempty
    have hk : m ≤ n := by dsimp [m]; exact Nat.min_le_left _ _
    have hstop : m ≤ ReferenceFirstLiveHandoverSnapshotPrefix.stop
        rate rewards C_star C_h z n := by
      simp [ReferenceFirstLiveHandoverSnapshotPrefix.stop, m]
    have hphysical := physical_prefix_eq_N_before rate rewards C_star C_h z n
      hnonempty hc payload hp i m hk hstop
    have hquota := actual_auxiliary_N_before_le_twoQ_add_one rate rewards C_star C_h z
      hc n hnonempty payload hp i m
    rw [hphysical]
    simpa [m] using hquota

/-- Immediately before each actual supported date on which the selected
follower is still pending, the accumulated physical service is strictly below
two initial batches plus one confirmation. The auxiliary calendar is queried
through this date, so its `J` witness and `N_before` share one prefix. -/
theorem actualStoppedServiceSum_lt_twoQ_add_one_before_pending
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (t : Fin p.T)
    (htSupport : t.val + 1 ∈
      ReferenceFirstLiveSourceStoppedHandoverEndpoint.supportDates rate rewards C_star C_h z)
    (hiPending : i ∈ ReferenceFirstLiveSourceStoppedHandoverEndpoint.pendingNat
      rate rewards C_star C_h t.val z) :
    stoppedServiceSum rate rewards C_star C_h z i t.val <
      2 * AffineBatchDecoder.quota p + 1 := by
  classical
  let query := t.val + 1
  have hsourceSupport : (ReferenceFirstLiveSourceStoppedHandoverEndpoint.supportDates
      rate rewards C_star C_h z).Nonempty := ⟨t.val + 1, htSupport⟩
  have hsigma := ReferenceFirstLiveSourceStoppedHandoverEndpoint.sigma_eq_physicalStart_succ
    rate rewards C_star C_h z hsourceSupport
  have hstart : ReferenceFirstLiveSourceStoppedReleaseEndpoint.physicalStart
      rate rewards C_star C_h z = ReferenceFirstLiveHandoverSnapshotPrefix.start
        rate rewards C_star C_h z := rfl
  rw [hstart] at hsigma
  have hinterval := ReferenceFirstLiveSourceStoppedHandoverEndpoint.supportDates_subset_interval
    rate rewards C_star C_h z htSupport
  have hlow : ReferenceFirstLiveHandoverSnapshotPrefix.start rate rewards C_star C_h z ≤
      t.val := by
    have h := (Finset.mem_Ico.mp hinterval).1
    omega
  have hhigh : t.val < ReferenceFirstLiveSourceStoppedHandoverEndpoint.theta
      rate rewards C_star C_h z - 1 := by
    have h := (Finset.mem_Ico.mp hinterval).2
    omega
  have hstop : t.val < ReferenceFirstLiveHandoverSnapshotPrefix.stop
      rate rewards C_star C_h z query := by
    simp only [ReferenceFirstLiveHandoverSnapshotPrefix.stop, lt_min_iff, query]
    exact ⟨by omega, hhigh⟩
  have hmember : t ∈ ReferenceFirstLiveHandoverSnapshotPrefix.prefixDates
      rate rewards C_star C_h z query := by
    simp only [ReferenceFirstLiveHandoverSnapshotPrefix.prefixDates,
      Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hlow, hstop, htSupport⟩
  have hnonempty : (ReferenceFirstLiveHandoverSnapshotPrefix.prefixDates
      rate rewards C_star C_h z query).Nonempty := ⟨t, hmember⟩
  rcases ReferenceFirstLiveHandoverPhaseReplay.actual_prefix_correspondence
      rate rewards C_star C_h z query with hempty | hexists
  · exact False.elim ((Finset.nonempty_iff_ne_empty.mp hnonempty) hempty)
  ·
      obtain ⟨payload, hp, hc, _hsigma, _hstamps, hforall⟩ := hexists
      obtain ⟨r, states, memories, hrecord, htime, hmissing, hstateData⟩ := hforall t hmember
      have hiPendingActual : actionFollowerIndex i ∈
          ReferenceFirstLiveSourceStoppedHandoverEndpoint.pendingNat
            rate rewards C_star C_h t.val z := by
        rw [actionFollowerIndex_eq]
        exact hiPending
      obtain ⟨_hinput, _hprepared, _hstatus, _hphase, _hlocal, hJ, _hJX⟩ :=
        hstateData (actionFollowerIndex i)
      let live := ReferenceFirstLiveHandoverSnapshotPrefix.auxiliaryLive
        rate rewards C_star C_h z query payload hp
      let cutoffBefore : Fin p.T → Bool := fun _ => false
      let overflowAfter : Fin p.T → Bool := fun u => decide
        (ReferenceFirstLiveOverflowReadout.wholeFirstLiveOverflowRound rate rewards C_star C_h z =
          some (u.val + 1))
      let fixing : Fin p.T := payload.sigma
      let M : HandoverStoppedDecoderReplay.Down p
          (CanonicalRecordingRates.beta p rate.eta.val) := payload.downRecord (actionFollowerIndex i)
      let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
        rate z rewards C_star C_h hc
      let d0 := (seed.followers i).downBatch
      have hseedBatch :
          ((ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
            rate z rewards C_star C_h hc).followers (actionFollowerIndex i)).downBatch =
          ((ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
            rate z rewards C_star C_h hc).followers i).downBatch := by
        rw [actionFollowerIndex_apply_eq
          (ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
            rate z rewards C_star C_h hc).followers i]
      rcases actual_auxiliary_quota_inputs rate rewards C_star C_h z hc query hnonempty
          payload hp i with ⟨hsource, hholder, hquota, hpending, hfixed⟩
      have hJaux : HandoverStoppedDecoderReplay.J p payload.assignment
          (HandoverStoppedDecoderReplay.fromLive p payload.assignment live cutoffBefore overflowAfter)
          fixing (HandoverStoppedDecoderReplay.snapshotBefore p
            (CanonicalRecordingRates.beta p rate.eta.val) payload.assignment
            (HandoverStoppedDecoderReplay.fromLive p payload.assignment live cutoffBefore overflowAfter)
            (actionFollowerIndex i) fixing M
            (HandoverStoppedDecoderReplay.initial p d0 0) t.val) t = 1 := by
        rw [hseedBatch] at hJ
        simpa [live, cutoffBefore, overflowAfter, fixing, M, seed, d0,
          hiPendingActual] using hJ
      have hstrict := HandoverStoppedServiceQuota.N_before_lt_twoQ_add_one_of_J
        p (CanonicalRecordingRates.beta p rate.eta.val) payload.assignment live cutoffBefore
        overflowAfter (actionFollowerIndex i) fixing M 0 d0 hsource hholder hquota hpending
        hfixed t hJaux
      have hphysical := physical_prefix_eq_N_before rate rewards C_star C_h z query
        hnonempty hc payload hp i t.val (by dsimp [query]; omega)
        (by dsimp [query]; exact Nat.le_of_lt hstop)
      rw [hphysical]
      exact hstrict

end Bandits.Support.ReferenceFirstLiveHandoverPhysicalQuota

end
