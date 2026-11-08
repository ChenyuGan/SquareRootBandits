/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCorrectedCurrentCutoffReplyRetention

import Mathlib.Tactic

/-!
# Current follower queues at the first corrected collection

This module develops the source-level queue producer for actual first-collection
follower registers. The proved choice lemma below uses the original installed
payload and the single full birth-plus-LIVE attributed-arrival word.

Sources: `appendix_a_local_protocol.tex:28-64`,
`06_interruptions.tex:40-100,192-233,246-299`, and
`04_slow_fast_learner.tex:157-174` under `sources/zip4/manuscript/`.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions

namespace Bandits.Support.ReferenceFirstCorrectedCurrentFollowerCollectionQueue

variable {p : ConstructorDimensions.Parameters}

local instance (Q : Prop) : Decidable Q := Classical.propDecidable Q

/-- An actual unoccupied CHOICE with a fixed accepted DOWN carries its reply
back through PREPARE and through the physical release/finish transition,
provided the queried INPUT or OUTPUT retains that same DOWN. -/
theorem actual_record_input_output_queue_of_choice
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1))
    (M : OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (queue : ℕ) (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hchoice : (ReferenceFollowerFixedReply.actualChoice r i).configuration =
      .ordinary state memory)
    (hunoccupied : state.status = .unoccupied)
    (hlast : state.lastDown = some M)
    (hqueue : state.backlog = queue) :
    (∀ (input : ReferencePrelaunchFollower.State p rate.eta)
        (inputMemory : ActiveFollowerLifecycle.LocalMemory p),
      r.input.state.followers i = .ordinary input inputMemory →
      input.backlog = queue) ∧
    (∀ (output : ReferencePrelaunchFollower.State p rate.eta)
        (outputMemory : ActiveFollowerLifecycle.LocalMemory p),
      (r.output.followers i).configuration = .ordinary output outputMemory →
      output.lastDown = some M → output.backlog = queue) := by
  constructor
  · intro input inputMemory hinput
    obtain ⟨before, beforeMemory, hbefore, hreply, _⟩ :=
      ReferenceFollowerReplyChronology.record_input_to_choice r i state memory hchoice
    have hstate : input = before :=
      (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
        (hinput.symm.trans hbefore)).1
    subst input
    have hbacklog : state.backlog = before.backlog :=
      congrArg (fun q => q.2.2.2) hreply
    exact hbacklog.symm.trans hqueue
  · intro output outputMemory houtput houtputLast
    have hnextConfig : r.output.next.followers i = .ordinary output outputMemory := by
      have hprojection : r.output.next.followers i = (r.output.followers i).configuration := by
        rw [r.output_eq]
        rfl
      rw [hprojection]
      exact houtput
    obtain ⟨choice, choiceMemory, hchoice', _hmono, hframe, _hchanged⟩ :=
      ReferenceFollowerReplyChronology.record_choice_chronology r i output outputMemory hnextConfig
    have hstate : choice = state :=
      (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
        (hchoice'.symm.trans hchoice)).1
    subst choice
    have hstart : ReferencePrelaunchFollower.acceptedStart state =
        ReferencePrelaunchFollower.acceptedStart output := by
      simp only [ReferencePrelaunchFollower.acceptedStart, hlast, houtputLast]
    have hreply := (hframe hunoccupied hstart).2
    have hbacklog : output.backlog = state.backlog :=
      congrArg (fun q => q.2.2.2) hreply
    exact hbacklog.trans hqueue

/-- The actual first cutoff has already reset every ordinary current-DOWN
CHOICE, including an excluded boundary record. This uses the complete-row
phase and proposal token, rather than a status assumption on the query. -/
theorem actual_current_choice_unoccupied
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (P : ReferenceActivePhysicalStep.Payload rate) (e : ℕ)
    (hcutoff : FollowerCutoffScan.firstCutoff p rate.eta.val P.sigma
      (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
        (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z))) =
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + e + 1)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length) (hek : e ≤ k.val)
    (i : Fin (p.m - 1)) (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hc : (ReferenceFollowerFixedReply.actualChoice
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val]
        i).configuration = .ordinary state memory)
    (hacceptedStart : ReferencePrelaunchFollower.acceptedStart state = P.sigma.val + 1) :
    state.status = .unoccupied := by
  obtain ⟨M, hd⟩ : ∃ M, state.lastDown = some M := by
    cases hd : state.lastDown with
    | none => simp only [ReferencePrelaunchFollower.acceptedStart, hd] at hacceptedStart
              omega
    | some M => exact ⟨M, rfl⟩
  have hMstart : M.val.sigma = P.sigma.val + 1 := by
    simpa only [ReferencePrelaunchFollower.acceptedStart, hd] using hacceptedStart
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  have hp : ReferenceFollowerFixedReply.actualChoice R[k.val] i =
      DeclaredFollowerLocalRound.prepare rate i R[k.val].input.row
        (R[k.val].input.state.activations i) R[k.val].input.time
        (R[k.val].input.active i) (R[k.val].input.state.followers i) :=
    R[k.val].output.preparation.followers.followers_eq i
  have hc' : (DeclaredFollowerLocalRound.prepare rate i R[k.val].input.row
      (R[k.val].input.state.activations i) R[k.val].input.time
      (R[k.val].input.active i) (R[k.val].input.state.followers i)).configuration =
        .ordinary state memory := by
    rw [← hp]
    exact hc
  obtain ⟨before, beforeMemory, hin, hstart, hreply, _⟩ :=
    ReferenceFollowerReplyChronology.prepare_ordinary_inversion i R[k.val].input.row
      (R[k.val].input.state.activations i) R[k.val].input.time
      (R[k.val].input.active i) (R[k.val].input.state.followers i) state memory hc'
  have hdBefore : before.lastDown = some M :=
    (congrArg Prod.fst hreply).symm.trans hd
  have hphase := ReferenceCompleteFollowerCutoffPhase.complete_ordinary_follower_phase
    rate rewards C_star C_h z k i before beforeMemory hin M hdBefore
  have htoken := ReferenceCompleteFollowerCutoffPhase.complete_ordinary_follower_token
    rate rewards C_star C_h z k i before beforeMemory hin
  have hstatus := ReferenceAssignmentFollowerMassSteps.start_round_cutoff_status
    R[k.val].input.time R[k.val].input.row before state beforeMemory memory
    M hdBefore hphase htoken hstart
  apply hstatus.mpr
  have hcoordinate : ActiveFollowerDownAcceptance.downStart p rate M =
      P.sigma := by
    apply Fin.ext
    have h := ActiveFollowerDownAcceptance.downStart_val_add_one p rate M
    rw [hMstart] at h
    omega
  obtain ⟨_, _, hr⟩ := ReferenceLaterLiveNumericalReadout.source_record_prefix
    rate rewards C_star C_h z k
  have hrow : R[k.val].input.row =
      z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) := by
    change (R.get k).input.row = _
    rw [hr]
    rfl
  have htime := ReferenceAssignmentFollowerMassSteps.complete_record_time
    rate rewards C_star C_h z k
  rw [hcoordinate, hrow, hcutoff, htime]
  omega

/-- At every actual ordinary first-collection CHOICE whose current DOWN is
the retained installation DOWN, the backlog is
the endpoint of the same full birth-plus-LIVE replay. The payload and word are
selected once from the accepted source theorem, not reconstructed from an
endpoint fold. -/
theorem actual_first_corrected_current_collection_choice_queue
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hz : z ∈ ReferenceFirstCollectionCorrectedSliceNumericalPrefix.correctedCell
      rate rewards C_star C_h u t) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let b := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.birthIndex
      rate rewards C_star C_h z
    let W := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.liveTail
      rate rewards C_star C_h z
    let V := (R.drop b).take (1 + W.length)
    let e := b + (1 + W.length)
    ∃ (birth : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
      (P : ReferenceActivePhysicalStep.Payload rate)
      (words : Fin (p.m - 1) → List (Bool × ℕ)),
      R[b]? = some birth ∧
      ReferenceAssignmentPayloadPersistence.InstallationBirth birth P ∧
      P.sigma = t ∧
      (∀ i, (P.downRecord i).val.q = P.queues (P.assignment.assigned i)) ∧
      (∀ i, V.mapM
        (ReferenceFirstCorrectedAssignedArrivalPrefix.attributedArrival? P i) =
          some (words i)) ∧
      (e = R.length ∨
        ∃ (he : e < R.length)
          (seg : ReferenceCollectionSegmentExtraction.Segment rate),
          ReferenceCollectionSegmentExtraction.segmentAt R e = some seg ∧
          seg.entry = R[e] ∧
          seg.context.payload = P ∧
          ∀ (k : Fin R.length), R[k.val] ∈ seg.records →
            ∀ (i : Fin (p.m - 1)) (state : ReferencePrelaunchFollower.State p rate.eta)
              (memory : ActiveFollowerLifecycle.LocalMemory p),
              (ReferenceFollowerFixedReply.actualChoice R[k.val] i).configuration =
                .ordinary state memory →
              state.lastDown = some (P.downRecord i) →
              state.backlog = (QueueReplay.replay (4 * rate.n)
                (0, (P.downRecord i).val.q) (words i)).2) := by
  classical
  intro R b W V e
  obtain ⟨L, c, birth, P, base, _hL, _hc, _hprefix, _hlen, hb, hborn,
      hSigma, hqueues, hbase, hshape, _hbound, _hterminal, _hstorage,
      _hcarry, hwords, hcollection⟩ :=
    ReferenceFirstCorrectedCurrentCutoffReplyRetention.actual_first_corrected_current_cutoff_reply_retention
      rate rewards C_star C_h u t z hz
  have hseed : ∀ i, (P.downRecord i).val.q = P.queues (P.assignment.assigned i) := by
    intro i
    exact (hbase i).2.trans (hqueues (P.assignment.assigned i)).symm
  have hVlength : V.length = 1 + W.length := by
    change ((R.drop b).take (1 + W.length)).length = _
    rw [List.length_take, List.length_drop, Nat.min_eq_left]
    change b + (1 + W.length) ≤ R.length at _hbound
    omega
  have hVbound : V.length ≤ 1 + W.length := by
    rw [hVlength]
  let words : Fin (p.m - 1) → List (Bool × ℕ) := fun i =>
    Classical.choose (hwords i V.length hVbound)
  have hword : ∀ i, V.mapM
      (ReferenceFirstCorrectedAssignedArrivalPrefix.attributedArrival? P i) =
        some (words i) := by
    intro i
    have hspec := (Classical.choose_spec (hwords i V.length hVbound)).1
    have hspec' : (V.take V.length).mapM
        (ReferenceFirstCorrectedAssignedArrivalPrefix.attributedArrival? P i) =
          some (words i) := by
      simpa only [words] using hspec
    simpa only [List.take_length] using hspec'
  refine ⟨birth, P, words, hb, hborn, hSigma, hseed, hword, ?_⟩
  rcases hcollection with hend | ⟨he, seg, hseg, hentry, hpayload, _hpartition,
      hcutoff, _hselected, _hlate, hrecords, _hremaining⟩
  · exact Or.inl hend
  · refine Or.inr ⟨he, seg, hseg, hentry, hpayload, ?_⟩
    intro k hmem i state memory hconfiguration hlast
    have hdrop : R[k.val] ∈ R.drop e := by
      rw [← _hpartition]
      exact List.mem_append_left _ hmem
    obtain ⟨j, hj, hget⟩ := List.mem_iff_getElem.mp hdrop
    have hjR : e + j < R.length := by
      rw [List.length_drop] at hj
      omega
    have heqR : R[e + j] = R[k.val] := by
      simpa only [List.getElem_drop] using hget
    have htime1 := ReferenceAssignmentFollowerMassSteps.complete_record_time
      rate rewards C_star C_h z ⟨e + j, hjR⟩
    have htime2 := ReferenceAssignmentFollowerMassSteps.complete_record_time
      rate rewards C_star C_h z k
    change R[e + j].input.time.val = _ at htime1
    rw [heqR, htime2] at htime1
    change _ = _ + (e + j) at htime1
    have hek : e ≤ k.val := by omega
    have hstart : ReferencePrelaunchFollower.acceptedStart state = P.sigma.val + 1 := by
      rw [ReferencePrelaunchFollower.acceptedStart, hlast]
      exact congrArg OrdinaryMessageCodec.DownFields.sigma (P.downRecord_fields i)
    have hunoccupied := actual_current_choice_unoccupied rate rewards C_star C_h z
      P e hcutoff k hek i state memory hconfiguration hstart
    rcases hrecords R[k.val] hmem with ⟨_, _, hcurrent, _⟩
    obtain ⟨_, _, _, _, word, hword', _hS, _hdelta, hbacklog, _hretention⟩ :=
      hcurrent k hmem i state memory hconfiguration hunoccupied hstart
    have hsameWord : word = words i :=
      Option.some.inj (hword'.symm.trans (hword i))
    rw [hsameWord] at hbacklog
    exact hbacklog

/-- The actual cutoff entry INPUT and reset CHOICE carry the same full-V
backlog even when the entry is excluded from the completed segment. The INPUT
with the current DOWN is occupied and PREPARE resets only its status. -/
theorem actual_first_corrected_current_collection_entry_queue
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hz : z ∈ ReferenceFirstCollectionCorrectedSliceNumericalPrefix.correctedCell
      rate rewards C_star C_h u t) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let b := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.birthIndex
      rate rewards C_star C_h z
    let W := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.liveTail
      rate rewards C_star C_h z
    let V := (R.drop b).take (1 + W.length)
    let e := b + (1 + W.length)
    ∃ (birth : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
      (P : ReferenceActivePhysicalStep.Payload rate)
      (words : Fin (p.m - 1) → List (Bool × ℕ)),
      R[b]? = some birth ∧
      ReferenceAssignmentPayloadPersistence.InstallationBirth birth P ∧
      P.sigma = t ∧
      (∀ i, V.mapM
        (ReferenceFirstCorrectedAssignedArrivalPrefix.attributedArrival? P i) =
          some (words i)) ∧
      (e = R.length ∨
        ∃ (he : e < R.length)
          (seg : ReferenceCollectionSegmentExtraction.Segment rate),
          ReferenceCollectionSegmentExtraction.segmentAt R e = some seg ∧
          seg.entry = R[e] ∧ seg.context.payload = P ∧
          (∀ i (state : ReferencePrelaunchFollower.State p rate.eta)
              (memory : ActiveFollowerLifecycle.LocalMemory p),
            seg.entry.input.state.followers i = .ordinary state memory →
            state.lastDown = some (P.downRecord i) →
            state.backlog = (QueueReplay.replay (4 * rate.n)
              (0, (P.downRecord i).val.q) (words i)).2) ∧
          (∀ i (state : ReferencePrelaunchFollower.State p rate.eta)
              (memory : ActiveFollowerLifecycle.LocalMemory p),
            (ReferenceFollowerFixedReply.actualChoice seg.entry i).configuration =
              .ordinary state memory →
            state.lastDown = some (P.downRecord i) →
            state.backlog = (QueueReplay.replay (4 * rate.n)
              (0, (P.downRecord i).val.q) (words i)).2)) := by
  classical
  intro R b W V e
  obtain ⟨L, c, birth, P, base, _hL, _hc, _hprefix, _hlen, hb, hborn,
      hSigma, _hqueues, _hbase, _hshape, _hbound, _hterminal, _hstorage,
      hcarry, _hwords, hcollection⟩ :=
    ReferenceFirstCorrectedCurrentCutoffReplyRetention.actual_first_corrected_current_cutoff_reply_retention
      rate rewards C_star C_h u t z hz
  obtain ⟨birthQ, PQ, words, hbQ, hbornQ, _hSigmaQ, _hseedQ, hwords, _⟩ :=
    actual_first_corrected_current_collection_choice_queue rate rewards C_star C_h u t z hz
  have hbirthEq : birthQ = birth := Option.some.inj (hbQ.symm.trans hb)
  subst birthQ
  have hPEq : PQ = P := ReferenceAssignmentPayloadChronology.installationBirth_payload_unique
    birth PQ P hbornQ hborn
  subst PQ
  refine ⟨birth, P, words, hb, hborn, hSigma, hwords, ?_⟩
  rcases hcollection with hend | ⟨he, seg, hseg, hentry, hpayload, _hpartition,
      hcutoff, _hselected, _hlate, _hrecords, _hremaining⟩
  · exact Or.inl hend
  · refine Or.inr ⟨he, seg, hseg, hentry, hpayload, ?_⟩
    have hget : R[e]? = some seg.entry := by
      rw [hentry]
      exact List.getElem?_eq_getElem he
    have hinputQueue : ∀ i (state : ReferencePrelaunchFollower.State p rate.eta)
        (memory : ActiveFollowerLifecycle.LocalMemory p),
        seg.entry.input.state.followers i = .ordinary state memory →
        state.lastDown = some (P.downRecord i) →
        state.backlog = (QueueReplay.replay (4 * rate.n)
          (0, (P.downRecord i).val.q) (words i)).2 := by
      intro i state memory hin hd
      obtain ⟨endpoint, endpointMemory, _hlast, _hout, _hnext, hinput,
        _htime, _hstart, _hchoice, hnumeric⟩ := hcarry seg.entry hget i
      have hstate := (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
        (hin.symm.trans hinput)).1
      subst state
      have hphase := ReferenceCompleteFollowerCutoffPhase.complete_ordinary_follower_phase
        rate rewards C_star C_h z ⟨e, he⟩ i endpoint endpointMemory
        (by rw [← hentry]; exact hinput) (P.downRecord i) hd
      have hcoordinate : ActiveFollowerDownAcceptance.downStart p rate (P.downRecord i) =
          P.sigma := by
        apply Fin.ext
        have h := ActiveFollowerDownAcceptance.downStart_val_add_one p rate (P.downRecord i)
        rw [P.downRecord_fields i] at h
        change _ + 1 = P.sigma.val + 1 at h
        omega
      obtain ⟨_, _, hr⟩ := ReferenceLaterLiveNumericalReadout.source_record_prefix
        rate rewards C_star C_h z ⟨e, he⟩
      have hrow : R[e].input.row =
          z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) := by
        change (R.get ⟨e, he⟩).input.row = _
        rw [hr]
        rfl
      have hdate := ReferenceAssignmentFollowerMassSteps.complete_record_time
        rate rewards C_star C_h z ⟨e, he⟩
      have hoccupied : endpoint.status ≠ .unoccupied := by
        intro hu
        have hle := hphase.mp hu
        change FollowerCutoffScan.firstCutoff p rate.eta.val
          (ActiveFollowerDownAcceptance.downStart p rate (P.downRecord i))
          (FollowerCutoffScan.completeRowProposalBit p rate.eta.val R[e].input.row) ≤
          R[e].input.time.val at hle
        rw [hcoordinate, hrow, hcutoff, hdate] at hle
        change _ + e + 1 ≤ _ + e at hle
        omega
      obtain ⟨word, hmap, _hd, hpair, _hdelta⟩ := hnumeric hoccupied
      have hwordEq : word = words i := Option.some.inj (hmap.symm.trans (hwords i))
      have hqueue := congrArg Prod.snd hpair
      rw [hwordEq] at hqueue
      exact hqueue
    refine ⟨hinputQueue, ?_⟩
    intro i state memory hc hd
    obtain ⟨before, beforeMemory, hin, hreply, _⟩ :=
      ReferenceFollowerReplyChronology.record_input_to_choice seg.entry i state memory hc
    have hdBefore : before.lastDown = some (P.downRecord i) :=
      (congrArg Prod.fst hreply).symm.trans hd
    exact (congrArg (fun q => q.2.2.2) hreply).trans
      (hinputQueue i before beforeMemory hin hdBefore)

private theorem retained_down_selected_payload
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1))
    (prior : ReferenceAcceptedUpFollowerHistory.DownRecord (p := p) (rate := rate))
    (hretained : ReferenceAcceptedUpFollowerHistory.RetainedDown record i prior) :
    ∃ selected : ReferenceActivePhysicalStep.Selection record.input,
      record.output.preparation.coordinator.selection = some selected ∧
      prior = selected.view.payload.downRecord i := by
  obtain ⟨logged, cut, after, raw, scan, registers, lastService,
    hinput, hdown, haccepted⟩ := hretained
  obtain ⟨choice, memory, actualLogged, hconfiguration, hunoccupied, hlogging,
    hactualInput, hcut⟩ :=
    ReferenceFollowerSparseEmissionRecovery.actualDownDiagnostic_choice record i cut hdown
  have hactualIndex := (record.output.preparation.follower_alignment i).2.1
  have hloggedEq : actualLogged = logged := Option.some.inj (hactualInput.symm.trans hinput)
  subst actualLogged
  rw [hcut] at haccepted
  obtain ⟨view, hview⟩ := ReferenceFollowerSparseEmissionRecovery.acceptedReferenceCut_someView
    record.output.preparation.coordinator.downView
    (record.output.preparation.followers.followers i).follower
    (record.output.preparation.followers.followers i).row
    (record.output.preparation.followers.followers i).time
    (record.output.preparation.feedback.observations
      (PublicDiscreteDraws.followerPlayer p.two_le_m i)) logged logged after raw prior scan registers
    lastService haccepted
  rw [hview] at haccepted
  have hfields := ReferenceActiveDataOwnership.referenceDown_accepted_fields view
    (record.output.preparation.followers.followers i).follower
    (record.output.preparation.followers.followers i).row
    (record.output.preparation.followers.followers i).time
    (record.output.preparation.feedback.observations
      (PublicDiscreteDraws.followerPlayer p.two_le_m i)) logged logged after raw prior scan registers
    lastService haccepted
  have hmap : record.output.preparation.coordinator.selection.map ReferenceActivePhysicalStep.Selection.view = some view := hview
  obtain ⟨selected, hselection, hselectedView⟩ := Option.map_eq_some_iff.mp hmap
  refine ⟨selected, hselection, ?_⟩
  have hmessage : prior = view.payload.downRecord i := by
    simpa only [hactualIndex] using hfields.1
  simpa only [hselectedView] using hmessage

/-- An actual retained current DOWN identifies the whole original selected
payload by its real installation, rather than by replay endpoint equality. -/
private theorem current_retained_down_selection
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (b : ℕ)
    (birth : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (P : ReferenceActivePhysicalStep.Payload rate)
    (hb : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[b]? = some birth)
    (hborn : ReferenceAssignmentPayloadPersistence.InstallationBirth birth P)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (i : Fin (p.m - 1))
    (hretained : ReferenceAcceptedUpFollowerHistory.RetainedDown
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[k.val] i (P.downRecord i)) :
    ∃ selected : ReferenceActivePhysicalStep.Selection
        (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h)[k.val].input,
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[k.val].output.preparation.coordinator.selection = some selected ∧
      selected.view.payload = P := by
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  obtain ⟨selected, hs, hmessage⟩ := retained_down_selected_payload R[k.val] i
    (P.downRecord i) hretained
  obtain ⟨crossing, _, _⟩ := ReferenceLaterLiveNumericalReadout.source_record_prefix
    rate rewards C_star C_h z k
  let initial := ReferenceFirstLaunchNumericalCell.launchState rate z rewards C_star C_h crossing
  let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
    rate z rewards C_star C_h crossing
  let start := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  have hspan : start + (p.T - start) ≤ p.T := by
    have h := ReferenceCompletePhysicalHistory.physicalStart_le_T rate z rewards C_star C_h
    dsimp only [start]
    omega
  have hrun := ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
    rate z rewards C_star C_h initial
    (ReferenceFirstLaunchNumericalCell.correctedLaunch_eq_some_launchState
      rate z rewards C_star C_h crossing)
  have hmem : R[k.val] ∈ (ReferenceActivePhysicalHorizon.run initial z.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards start (p.T - start)
      hspan seed.activeAtStart).records := by
    rw [← hrun]
    exact List.getElem_mem k.isLt
  obtain ⟨selectedBirth, hselectedMem, hselectedBirth, _htime, _hbefore⟩ :=
    ReferenceSelectedPayloadChronology.actualRun_selectedPayload_has_birth initial z.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards start (p.T - start)
      hspan seed.activeAtStart seed.coordinatorFirst R[k.val] selected hmem hs
  rw [← hrun] at hselectedMem
  obtain ⟨j, hj, hget⟩ := List.mem_iff_getElem.mp hselectedMem
  have hbirthTime := ReferenceAssignmentPayloadChronology.installationBirth_time_eq
    birth P hborn
  have hselectedTime := ReferenceAssignmentPayloadChronology.installationBirth_time_eq
    selectedBirth selected.view.payload hselectedBirth
  have hPstart : P.sigma.val = selected.view.payload.sigma.val := by
    have h := congrArg (fun M : OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta) => M.val.sigma) hmessage
    rw [P.downRecord_fields i, selected.view.payload.downRecord_fields i] at h
    change P.sigma.val + 1 = selected.view.payload.sigma.val + 1 at h
    omega
  have hbGet := (List.getElem?_eq_some_iff.mp hb).2
  have hbLt := (List.getElem?_eq_some_iff.mp hb).1
  have hbTime := ReferenceAssignmentFollowerMassSteps.complete_record_time
    rate rewards C_star C_h z ⟨b, hbLt⟩
  have hjTime := ReferenceAssignmentFollowerMassSteps.complete_record_time
    rate rewards C_star C_h z ⟨j, hj⟩
  have hget' : R[j] = selectedBirth := hget
  change R[b].input.time.val = start + b at hbTime
  change R[j].input.time.val = start + j at hjTime
  rw [hbGet] at hbTime
  rw [hget'] at hjTime
  have hindex : j = b := by omega
  have hbirthEq : selectedBirth = birth := by
    calc
      selectedBirth = R[j] := hget'.symm
      _ = R[b] := by simp only [hindex]
      _ = birth := hbGet
  have hselectedBirthAt : ReferenceAssignmentPayloadPersistence.InstallationBirth
      birth selected.view.payload := by
    simpa only [hbirthEq] using hselectedBirth
  exact ⟨selected, hs,
    ReferenceAssignmentPayloadChronology.installationBirth_payload_unique
      birth selected.view.payload P hselectedBirthAt hborn⟩

/-- A late accepted current DOWN itself fixes the actual follower OUTPUT at
its full birth-plus-LIVE replay endpoint, including when acceptance occurs on
the final physical record. -/
theorem actual_first_corrected_current_collection_late_down_output_queue
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hz : z ∈ ReferenceFirstCollectionCorrectedSliceNumericalPrefix.correctedCell
      rate rewards C_star C_h u t) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let b := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.birthIndex
      rate rewards C_star C_h z
    let W := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.liveTail
      rate rewards C_star C_h z
    let V := (R.drop b).take (1 + W.length)
    let e := b + (1 + W.length)
    ∃ (birth : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
      (P : ReferenceActivePhysicalStep.Payload rate)
      (words : Fin (p.m - 1) → List (Bool × ℕ)),
      R[b]? = some birth ∧
      ReferenceAssignmentPayloadPersistence.InstallationBirth birth P ∧
      P.sigma = t ∧
      (∀ i, V.mapM
        (ReferenceFirstCorrectedAssignedArrivalPrefix.attributedArrival? P i) =
          some (words i)) ∧
      (e = R.length ∨
        ∃ (he : e < R.length)
          (seg : ReferenceCollectionSegmentExtraction.Segment rate),
          ReferenceCollectionSegmentExtraction.segmentAt R e = some seg ∧
          seg.entry = R[e] ∧ seg.context.payload = P ∧
          ∀ (k : Fin R.length), e ≤ k.val →
            ∀ (selected : ReferenceActivePhysicalStep.Selection R[k.val].input),
              R[k.val].output.preparation.coordinator.selection = some selected →
              selected.view.payload = P →
              ∀ (i : Fin (p.m - 1))
                (logged after : ReferencePrelaunchFollower.State p rate.eta)
                (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
                (raw : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p)))
                (scan : FollowerCutoffScan.ScanResult p.T)
                (registers : ℕ × ℕ) (lastService : ℕ),
                (R[k.val].output.followers i).downInput = some logged →
                (R[k.val].output.followers i).down = some cut →
                cut.outcome = .accepted logged after raw (P.downRecord i)
                  scan registers lastService →
                ∃ nextMemory : ActiveFollowerLifecycle.LocalMemory p,
                  after.lastDown = some (P.downRecord i) ∧
                  after.backlog = (QueueReplay.replay (4 * rate.n)
                    (0, (P.downRecord i).val.q) (words i)).2 ∧
                  (R[k.val].output.followers i).configuration =
                    .ordinary after nextMemory) := by
  classical
  intro R b W V e
  obtain ⟨_L, _c, birth, P, _base, _hL, _hc, _hprefix, _hlen, hb, hborn,
      hSigma, _hqueues, _hbase, hshape, hbound, _hterminal, _hstorage,
      _hcarry, hwords, hcollection⟩ :=
    ReferenceFirstCorrectedCurrentCutoffReplyRetention.actual_first_corrected_current_cutoff_reply_retention
      rate rewards C_star C_h u t z hz
  have hVlength : V.length = 1 + W.length := by
    change ((R.drop b).take (1 + W.length)).length = _
    rw [List.length_take, List.length_drop, Nat.min_eq_left]
    change b + (1 + W.length) ≤ R.length at hbound
    omega
  have hVbound : V.length ≤ 1 + W.length := by rw [hVlength]
  let words : Fin (p.m - 1) → List (Bool × ℕ) := fun i =>
    Classical.choose (hwords i V.length hVbound)
  have hword : ∀ i, V.mapM
      (ReferenceFirstCorrectedAssignedArrivalPrefix.attributedArrival? P i) =
        some (words i) := by
    intro i
    have hspec := (Classical.choose_spec (hwords i V.length hVbound)).1
    have hspec' : (V.take V.length).mapM
        (ReferenceFirstCorrectedAssignedArrivalPrefix.attributedArrival? P i) =
          some (words i) := by
      simpa only [words] using hspec
    simpa only [List.take_length] using hspec'
  refine ⟨birth, P, words, hb, hborn, hSigma, hword, ?_⟩
  rcases hcollection with hend | ⟨he, seg, hseg, hentry, hpayload, _hpartition,
      _hcutoff, _hselected, hlate, _hrecords, _hremaining⟩
  · exact Or.inl hend
  · refine Or.inr ⟨he, seg, hseg, hentry, hpayload, ?_⟩
    intro k hek selected hselected hpayloadK i logged after cut raw scan registers lastService
      hlogged hdown houtcome
    obtain ⟨word, nextMemory, hword', _hstatus, hlast, _hS, _hdelta, hbacklog, hnext⟩ :=
      hlate k hek selected hselected hpayloadK i logged after cut raw scan registers lastService
        hlogged hdown houtcome
    have hsameWord : word = words i :=
      Option.some.inj (hword'.symm.trans (hword i))
    have hnextOut : (R[k.val].output.followers i).configuration =
        .ordinary after nextMemory := by
      have hprojection : R[k.val].output.next.followers i =
          (R[k.val].output.followers i).configuration := by
        rw [R[k.val].output_eq]
        rfl
      rw [← hprojection]
      exact hnext
    refine ⟨nextMemory, hlast, ?_, hnextOut⟩
    rw [hsameWord] at hbacklog
    exact hbacklog

/-- Every literal ordinary current-DOWN register at this actual first
collection has the same full birth-plus-LIVE queue. The optional first
excluded record is retained at INPUT and CHOICE; its OUTPUT is queried only
when no later assignment is chosen there. Birth, payload, segment and source
are the original actual selectors. Each follower has one attributed word. -/
theorem actual_first_corrected_current_follower_collection_queues
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hz : z ∈ ReferenceFirstCollectionCorrectedSliceNumericalPrefix.correctedCell
      rate rewards C_star C_h u t)
    (birth : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (P : ReferenceActivePhysicalStep.Payload rate)
    (hb : (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.birthIndex rate rewards C_star C_h z]? =
        some birth)
    (hborn : ReferenceAssignmentPayloadPersistence.InstallationBirth birth P)
    (_hSigma : P.sigma = t) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let b := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.birthIndex rate rewards C_star C_h z
    let W := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.liveTail rate rewards C_star C_h z
    let V := (R.drop b).take (1 + W.length)
    let e := b + (1 + W.length)
    ∀ seg : ReferenceCollectionSegmentExtraction.Segment rate,
      ReferenceCollectionSegmentExtraction.segmentAt R e = some seg →
      seg.context.payload = P ∧
      ∀ i : Fin (p.m - 1), ∃ word : List (Bool × ℕ),
        V.mapM (ReferenceFirstCorrectedAssignedArrivalPrefix.attributedArrival? P i) = some word ∧
        (∀ (state : ReferencePrelaunchFollower.State p rate.eta)
            (memory : ActiveFollowerLifecycle.LocalMemory p),
          seg.entry.input.state.followers i = .ordinary state memory →
          state.lastDown = some (P.downRecord i) →
          state.backlog = (QueueReplay.replay (4 * rate.n) (0, (P.downRecord i).val.q) word).2) ∧
        (∀ (state : ReferencePrelaunchFollower.State p rate.eta)
            (memory : ActiveFollowerLifecycle.LocalMemory p),
          (ReferenceFollowerFixedReply.actualChoice seg.entry i).configuration = .ordinary state memory →
          state.lastDown = some (P.downRecord i) →
          state.backlog = (QueueReplay.replay (4 * rate.n) (0, (P.downRecord i).val.q) word).2) ∧
        (∀ r ∈ seg.records,
          (∀ (state : ReferencePrelaunchFollower.State p rate.eta)
              (memory : ActiveFollowerLifecycle.LocalMemory p),
            r.input.state.followers i = .ordinary state memory →
            state.lastDown = some (P.downRecord i) →
            state.backlog = (QueueReplay.replay (4 * rate.n) (0, (P.downRecord i).val.q) word).2) ∧
          (∀ (state : ReferencePrelaunchFollower.State p rate.eta)
              (memory : ActiveFollowerLifecycle.LocalMemory p),
            (ReferenceFollowerFixedReply.actualChoice r i).configuration = .ordinary state memory →
            state.lastDown = some (P.downRecord i) →
            state.backlog = (QueueReplay.replay (4 * rate.n) (0, (P.downRecord i).val.q) word).2) ∧
          (∀ (state : ReferencePrelaunchFollower.State p rate.eta)
              (memory : ActiveFollowerLifecycle.LocalMemory p),
            (r.output.followers i).configuration = .ordinary state memory →
            state.lastDown = some (P.downRecord i) →
            state.backlog = (QueueReplay.replay (4 * rate.n) (0, (P.downRecord i).val.q) word).2)) ∧
        (∀ r, seg.remaining.head? = some r →
          (∀ (state : ReferencePrelaunchFollower.State p rate.eta)
              (memory : ActiveFollowerLifecycle.LocalMemory p),
            r.input.state.followers i = .ordinary state memory →
            state.lastDown = some (P.downRecord i) →
            state.backlog = (QueueReplay.replay (4 * rate.n) (0, (P.downRecord i).val.q) word).2) ∧
          (∀ (state : ReferencePrelaunchFollower.State p rate.eta)
              (memory : ActiveFollowerLifecycle.LocalMemory p),
            (ReferenceFollowerFixedReply.actualChoice r i).configuration = .ordinary state memory →
            state.lastDown = some (P.downRecord i) →
            state.backlog = (QueueReplay.replay (4 * rate.n) (0, (P.downRecord i).val.q) word).2) ∧
          (ReferenceCollectionPhaseHistory.laterChosen r.input = false →
            ∀ (state : ReferencePrelaunchFollower.State p rate.eta)
              (memory : ActiveFollowerLifecycle.LocalMemory p),
            (r.output.followers i).configuration = .ordinary state memory →
            state.lastDown = some (P.downRecord i) →
            state.backlog = (QueueReplay.replay (4 * rate.n) (0, (P.downRecord i).val.q) word).2)) := by
  classical
  intro R b W V e seg hseg
  obtain ⟨_L, _c, birthR, PR, _base, _hL, _hc, _hprefix, _hlen, hbR, hbornR,
      _hSigmaR, _hqueues, _hbase, _hshape, _hbound, _hterminal, _hstorage,
      _hcarry, _hwords, hcollection⟩ :=
    ReferenceFirstCorrectedCurrentCutoffReplyRetention.actual_first_corrected_current_cutoff_reply_retention
      rate rewards C_star C_h u t z hz
  have hbirthEq : birthR = birth := Option.some.inj (hbR.symm.trans hb)
  subst birthR
  have hPEq : PR = P := ReferenceAssignmentPayloadChronology.installationBirth_payload_unique
    birth PR P hbornR hborn
  subst PR
  rcases hcollection with hend | ⟨he, segR, hsegR, hentry, hpayload, hpartition,
      hcutoff, _hselected, hlate, hrecords, _hremaining⟩
  · change e = R.length at hend
    have hnone : ReferenceCollectionSegmentExtraction.segmentAt R e = none := by
      rw [hend]
      simp only [ReferenceCollectionSegmentExtraction.segmentAt, List.drop_length,
        ReferenceCollectionSegmentExtraction.segment, Option.bind_none]
    rw [hnone] at hseg
    cases hseg
  · have hsegEq : segR = seg := Option.some.inj (hsegR.symm.trans hseg)
    subst segR
    obtain ⟨birthE, PE, words, hbE, hbornE, _hSigmaE, hword, hentryBranch⟩ :=
      actual_first_corrected_current_collection_entry_queue rate rewards C_star C_h u t z hz
    have hbirthEEq : birthE = birth := Option.some.inj (hbE.symm.trans hb)
    subst birthE
    have hPEEq : PE = P := ReferenceAssignmentPayloadChronology.installationBirth_payload_unique
      birth PE P hbornE hborn
    subst PE
    have hentryQueues :
        (∀ i (state : ReferencePrelaunchFollower.State p rate.eta)
            (memory : ActiveFollowerLifecycle.LocalMemory p),
          seg.entry.input.state.followers i = .ordinary state memory →
          state.lastDown = some (P.downRecord i) →
          state.backlog = (QueueReplay.replay (4 * rate.n)
            (0, (P.downRecord i).val.q) (words i)).2) ∧
        (∀ i (state : ReferencePrelaunchFollower.State p rate.eta)
            (memory : ActiveFollowerLifecycle.LocalMemory p),
          (ReferenceFollowerFixedReply.actualChoice seg.entry i).configuration = .ordinary state memory →
          state.lastDown = some (P.downRecord i) →
          state.backlog = (QueueReplay.replay (4 * rate.n)
            (0, (P.downRecord i).val.q) (words i)).2) := by
      rcases hentryBranch with hend | ⟨_heE, segE, hsegE, _hentryE, _hpayloadE, hinputE, hchoiceE⟩
      · omega
      · have hsegEEq : segE = seg := Option.some.inj (hsegE.symm.trans hseg)
        subst segE
        exact ⟨hinputE, hchoiceE⟩
    have hindex : ∀ r ∈ R.drop e, ∃ k : Fin R.length, e ≤ k.val ∧ R[k.val] = r := by
      intro r hmem
      obtain ⟨j, hj, hget⟩ := List.mem_iff_getElem.mp hmem
      have hjR : e + j < R.length := by
        rw [List.length_drop] at hj
        omega
      refine ⟨⟨e + j, hjR⟩, Nat.le_add_right e j, ?_⟩
      simpa only [List.getElem_drop] using hget
    refine ⟨hpayload, ?_⟩
    intro i
    let queue := (QueueReplay.replay (4 * rate.n) (0, (P.downRecord i).val.q) (words i)).2
    have hchoiceQueue : ∀ (k : Fin R.length), R[k.val] ∈ seg.records →
        ∀ (state : ReferencePrelaunchFollower.State p rate.eta)
          (memory : ActiveFollowerLifecycle.LocalMemory p),
        (ReferenceFollowerFixedReply.actualChoice R[k.val] i).configuration = .ordinary state memory →
        state.lastDown = some (P.downRecord i) → state.backlog = queue := by
      intro k hmem state memory hc hd
      have hmemDrop : R[k.val] ∈ R.drop e := by
        rw [← hpartition]
        exact List.mem_append_left _ hmem
      obtain ⟨j, hej, hsame⟩ := hindex R[k.val] hmemDrop
      have ht1 := ReferenceAssignmentFollowerMassSteps.complete_record_time
        rate rewards C_star C_h z j
      have ht2 := ReferenceAssignmentFollowerMassSteps.complete_record_time
        rate rewards C_star C_h z k
      change R[j.val].input.time.val = _ at ht1
      rw [hsame, ht2] at ht1
      have hek : e ≤ k.val := by omega
      have hstart : ReferencePrelaunchFollower.acceptedStart state = P.sigma.val + 1 := by
        rw [ReferencePrelaunchFollower.acceptedStart, hd]
        exact congrArg OrdinaryMessageCodec.DownFields.sigma (P.downRecord_fields i)
      have hu := actual_current_choice_unoccupied rate rewards C_star C_h z
        P e hcutoff k hek i state memory hc hstart
      obtain ⟨_, _, hcurrent, _⟩ := hrecords R[k.val] hmem
      obtain ⟨_a, _hba, _hak, _hretained, word, hmap, _hS, _hdelta, hqueue, _hrest⟩ :=
        hcurrent k hmem i state memory hc hu hstart
      have hw : word = words i := Option.some.inj (hmap.symm.trans (hword i))
      rw [hw] at hqueue
      exact hqueue
    have hinputQueue : ∀ (k : Fin R.length),
        (∀ (state : ReferencePrelaunchFollower.State p rate.eta)
            (memory : ActiveFollowerLifecycle.LocalMemory p),
          (ReferenceFollowerFixedReply.actualChoice R[k.val] i).configuration = .ordinary state memory →
          state.lastDown = some (P.downRecord i) → state.backlog = queue) →
        ∀ (state : ReferencePrelaunchFollower.State p rate.eta)
          (memory : ActiveFollowerLifecycle.LocalMemory p),
        R[k.val].input.state.followers i = .ordinary state memory →
        state.lastDown = some (P.downRecord i) → state.backlog = queue := by
      intro k hchoices state memory hin hd
      obtain ⟨choice, _hvalid, hstart, hc, _hchoiceValid, _hop⟩ :=
        ReferenceCompleteFollowerPreparation.complete_ordinary_input_prepare
          rewards C_star C_h z k i state memory hin
      have hf := ActiveFollowerLifecycle.startRound_frame rate.eta R[k.val].input.time
        state choice memory memory hstart
      have hdChoice : choice.lastDown = some (P.downRecord i) := hf.1.trans hd
      exact hf.2.2.2.1.symm.trans (hchoices choice memory hc hdChoice)
    have houtputQueue : ∀ (k : Fin R.length), e ≤ k.val →
        (∀ (state : ReferencePrelaunchFollower.State p rate.eta)
            (memory : ActiveFollowerLifecycle.LocalMemory p),
          (ReferenceFollowerFixedReply.actualChoice R[k.val] i).configuration = .ordinary state memory →
          state.lastDown = some (P.downRecord i) → state.backlog = queue) →
        ∀ (state : ReferencePrelaunchFollower.State p rate.eta)
          (memory : ActiveFollowerLifecycle.LocalMemory p),
        (R[k.val].output.followers i).configuration = .ordinary state memory →
        state.lastDown = some (P.downRecord i) → state.backlog = queue := by
      intro k hek hchoices state memory hout hd
      have hnext : R[k.val].output.next.followers i = .ordinary state memory := by
        have hp : R[k.val].output.next.followers i = (R[k.val].output.followers i).configuration := by
          rw [R[k.val].output_eq]
          rfl
        exact hp.trans hout
      obtain ⟨choice, choiceMemory, hc, _hmono, hframe, hchanged⟩ :=
        ReferenceFollowerReplyChronology.record_choice_chronology R[k.val] i state memory hnext
      have hstart : ReferencePrelaunchFollower.acceptedStart state = P.sigma.val + 1 := by
        rw [ReferencePrelaunchFollower.acceptedStart, hd]
        exact congrArg OrdinaryMessageCodec.DownFields.sigma (P.downRecord_fields i)
      by_cases hs : ReferencePrelaunchFollower.acceptedStart choice =
          ReferencePrelaunchFollower.acceptedStart state
      · have hu := actual_current_choice_unoccupied rate rewards C_star C_h z
          P e hcutoff k hek i choice choiceMemory hc (hs.trans hstart)
        have hr := (hframe hu hs).2
        have hdChoice : choice.lastDown = some (P.downRecord i) :=
          (congrArg Prod.fst hr).symm.trans hd
        exact (congrArg (fun q => q.2.2.2) hr).trans (hchoices choice choiceMemory hc hdChoice)
      · obtain ⟨logged, cut, after, raw, M, scan, registers, lastService,
            hlogged, hdown, haccepted, _hsigma⟩ := hchanged hs
        obtain ⟨hafterDown, _hS, _hdelta, _hq, afterMemory, hafter⟩ :=
          ReferenceCompleteFollowerRetainedDownRecovery.complete_accepted_down_output
            rewards C_star C_h z k i logged after cut raw M scan registers lastService
            hlogged hdown haccepted
        have hafterEq : after = state :=
          (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj (hafter.symm.trans hnext)).1
        subst after
        have hM : M = P.downRecord i := Option.some.inj (hafterDown.symm.trans hd)
        subst M
        have hretained : ReferenceAcceptedUpFollowerHistory.RetainedDown R[k.val] i
            (P.downRecord i) :=
          ⟨logged, cut, state, raw, scan, registers, lastService, hlogged, hdown, haccepted⟩
        obtain ⟨selected, hselected, hcurrent⟩ := current_retained_down_selection
          rate rewards C_star C_h z b birth P hb hborn k i hretained
        obtain ⟨word, _nextMemory, hmap, _hu, _hd, _hS, _hdelta, hqueue, _hout⟩ :=
          hlate k hek selected hselected hcurrent i logged state cut raw scan registers lastService
            hlogged hdown haccepted
        have hw : word = words i := Option.some.inj (hmap.symm.trans (hword i))
        rw [hw] at hqueue
        exact hqueue
    have hrecordQueues : ∀ r ∈ seg.records,
        (∀ (state : ReferencePrelaunchFollower.State p rate.eta)
            (memory : ActiveFollowerLifecycle.LocalMemory p),
          r.input.state.followers i = .ordinary state memory →
          state.lastDown = some (P.downRecord i) → state.backlog = queue) ∧
        (∀ (state : ReferencePrelaunchFollower.State p rate.eta)
            (memory : ActiveFollowerLifecycle.LocalMemory p),
          (ReferenceFollowerFixedReply.actualChoice r i).configuration = .ordinary state memory →
          state.lastDown = some (P.downRecord i) → state.backlog = queue) ∧
        (∀ (state : ReferencePrelaunchFollower.State p rate.eta)
            (memory : ActiveFollowerLifecycle.LocalMemory p),
          (r.output.followers i).configuration = .ordinary state memory →
          state.lastDown = some (P.downRecord i) → state.backlog = queue) := by
      intro r hmem
      have hmemDrop : r ∈ R.drop e := by
        rw [← hpartition]
        exact List.mem_append_left _ hmem
      obtain ⟨k, hek, hk⟩ := hindex r hmemDrop
      have hmemK : R[k.val] ∈ seg.records := by rw [hk]; exact hmem
      rw [← hk]
      exact ⟨hinputQueue k (hchoiceQueue k hmemK), hchoiceQueue k hmemK,
        houtputQueue k hek (hchoiceQueue k hmemK)⟩
    refine ⟨words i, hword i, hentryQueues.1 i, hentryQueues.2 i, hrecordQueues, ?_⟩
    intro r hhead
    have hgetBoundary : R[e + seg.records.length]? = some r := by
      have happ : (seg.records ++ seg.remaining)[seg.records.length]? = some r := by
        rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, ← List.head?_eq_getElem?]
        exact hhead
      rw [hpartition, List.getElem?_drop] at happ
      exact happ
    have hkLt := (List.getElem?_eq_some_iff.mp hgetBoundary).1
    let k : Fin R.length := ⟨e + seg.records.length, hkLt⟩
    have hk : R[k.val] = r := (List.getElem?_eq_some_iff.mp hgetBoundary).2
    have hboundaryInput : ∀ (state : ReferencePrelaunchFollower.State p rate.eta)
        (memory : ActiveFollowerLifecycle.LocalMemory p),
        r.input.state.followers i = .ordinary state memory →
        state.lastDown = some (P.downRecord i) → state.backlog = queue := by
      intro state memory hin hd
      by_cases hempty : seg.records.length = 0
      · have heq : r = seg.entry := by
          have hke : k.val = e := by dsimp only [k]; omega
          have hkr : R[e] = r := by simpa only [hke] using hk
          exact hkr.symm.trans hentry.symm
        rw [heq] at hin
        exact hentryQueues.1 i state memory hin hd
      · have hjLt : e + seg.records.length - 1 < R.length := by omega
        have hjSlice : seg.records.length - 1 < (R.drop e).length := by
          rw [List.length_drop]
          omega
        have hjMem : R[e + seg.records.length - 1] ∈ seg.records := by
          have hlen : seg.records.length - 1 < seg.records.length := by omega
          have hget : (R.drop e)[seg.records.length - 1] =
              seg.records[seg.records.length - 1] := by
            simpa only [hpartition] using
              (List.getElem_append_left (bs := seg.remaining)
                (h' := by rw [List.length_append]; omega) hlen)
          have hindexEq : e + (seg.records.length - 1) = e + seg.records.length - 1 := by omega
          have hget' : R[e + seg.records.length - 1] =
              seg.records[seg.records.length - 1] := by
            simpa only [List.getElem_drop, hindexEq] using hget
          rw [hget']
          exact List.getElem_mem hlen
        have hsucc : e + seg.records.length - 1 + 1 < R.length := by omega
        have hadj := ReferenceCompleteLaterLiveComplementPrefixReplay.complete_adjacent
          (rate := rate) rewards C_star C_h z (e + seg.records.length - 1) hsucc
        have hsuccEq : e + seg.records.length - 1 + 1 = k.val := by dsimp only [k]; omega
        change R[e + seg.records.length - 1 + 1].input.state =
          R[e + seg.records.length - 1].output.next at hadj
        have hadj' : r.input.state = R[e + seg.records.length - 1].output.next := by
          simpa only [hsuccEq, hk] using hadj
        have hpreviousOutput :
            (R[e + seg.records.length - 1].output.followers i).configuration =
              .ordinary state memory := by
          have hp : R[e + seg.records.length - 1].output.next.followers i =
              (R[e + seg.records.length - 1].output.followers i).configuration := by
            rw [R[e + seg.records.length - 1].output_eq]
            rfl
          rw [← hp]
          exact (congrArg (fun s => s.followers i) hadj').symm.trans hin
        exact (hrecordQueues R[e + seg.records.length - 1] hjMem).2.2
          state memory hpreviousOutput hd
    have hboundaryChoice : ∀ (state : ReferencePrelaunchFollower.State p rate.eta)
        (memory : ActiveFollowerLifecycle.LocalMemory p),
        (ReferenceFollowerFixedReply.actualChoice r i).configuration = .ordinary state memory →
        state.lastDown = some (P.downRecord i) → state.backlog = queue := by
      intro state memory hc hd
      obtain ⟨before, beforeMemory, hin, hr, _⟩ :=
        ReferenceFollowerReplyChronology.record_input_to_choice r i state memory hc
      have hdBefore : before.lastDown = some (P.downRecord i) :=
        (congrArg Prod.fst hr).symm.trans hd
      exact (congrArg (fun q => q.2.2.2) hr).trans
        (hboundaryInput before beforeMemory hin hdBefore)
    refine ⟨hboundaryInput, hboundaryChoice, ?_⟩
    intro _hnoLater
    have hchoiceK : ∀ (state : ReferencePrelaunchFollower.State p rate.eta)
        (memory : ActiveFollowerLifecycle.LocalMemory p),
        (ReferenceFollowerFixedReply.actualChoice R[k.val] i).configuration = .ordinary state memory →
        state.lastDown = some (P.downRecord i) → state.backlog = queue := by
      rw [hk]
      exact hboundaryChoice
    have hout := houtputQueue k (by dsimp only [k]; omega) hchoiceK
    rw [hk] at hout
    exact hout

end Bandits.Support.ReferenceFirstCorrectedCurrentFollowerCollectionQueue

end
