/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCorrectedAssignedNativeFollowerPrefix

import Mathlib.Tactic

/-!
# Source composition for first corrected current-cutoff replies

This consumer joins actual corrected LIVE storage and first-cutoff carry to
the same installed payload's first physical collection. Current unoccupied
choices include no-offer rounds. Late accepted DOWN outputs are retained even
at the horizon. All records remain those of the original source run.

Sources: `appendix_a_local_protocol.tex:28-64`,
`06_interruptions.tex:192-233,246-299`, and
`05_binary_transport.tex:70-124` under `sources/zip4/manuscript/`.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions

namespace Bandits.Support.ReferenceFirstCorrectedCurrentCutoffReplyRetention

variable {p : ConstructorDimensions.Parameters}

local instance (Q : Prop) : Decidable Q := Classical.propDecidable Q

private theorem current_choice_down_origin
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (b : ℕ)
    (birth : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (hb : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[b]? = some birth)
    (hborn : ReferenceAssignmentPayloadPersistence.InstallationBirth birth payload)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (i : Fin (p.m - 1))
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hconfiguration : (ReferenceFollowerFixedReply.actualChoice
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h)[k.val]
      i).configuration = .ordinary state memory)
    (hacceptedStart : ReferencePrelaunchFollower.acceptedStart state = payload.sigma.val + 1) :
    ∃ a : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h).length,
      b ≤ a.val ∧ a.val < k.val ∧
      ReferenceAcceptedUpFollowerHistory.RetainedDown
        (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h)[a.val] i (payload.downRecord i) := by
  classical
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
  obtain ⟨M, hlastDown⟩ : ∃ M : OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta), state.lastDown = some M := by
    cases hlast : state.lastDown with
    | none => simp [ReferencePrelaunchFollower.acceptedStart, hlast] at hacceptedStart
    | some M => exact ⟨M, rfl⟩
  obtain ⟨b', a, P', beta, hba, hak, hborn', _hbase, hretained, hmessage,
      _hmass, _hdelta⟩ :=
    ReferenceCompleteOrdinaryFollowerMass.complete_ordinary_follower_choice_mass
      rewards C_star C_h source k i state memory hconfiguration M hlastDown
  have hMstart : M.val.sigma = payload.sigma.val + 1 := by
    simpa only [ReferencePrelaunchFollower.acceptedStart, hlastDown] using hacceptedStart
  have hPstart : P'.sigma.val = payload.sigma.val := by
    have hplus : P'.sigma.val + 1 = M.val.sigma := by
      calc
        P'.sigma.val + 1 = (P'.downRecord i).val.sigma := by
          rw [P'.downRecord_fields i]
        _ = M.val.sigma := by rw [← hmessage]
    omega
  have hbLt : b < R.length := (List.getElem?_eq_some_iff.mp hb).1
  have hbGet : R[b] = birth := (List.getElem?_eq_some_iff.mp hb).2
  let bFin : Fin R.length := ⟨b, hbLt⟩
  have hbornAt : ReferenceAssignmentPayloadPersistence.InstallationBirth R[b] payload := by
    rw [hbGet]
    exact hborn
  have htimeP' : P'.sigma.val =
      ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h + b'.val := by
    calc
      P'.sigma.val = R[b'.val].input.time.val :=
        ReferenceAssignmentPayloadChronology.installationBirth_time_eq
          R[b'.val] P' hborn'
      _ = ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h + b'.val :=
        ReferenceAssignmentFollowerMassSteps.complete_record_time rate rewards C_star C_h source b'
  have htimePayload : payload.sigma.val =
      ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h + b := by
    calc
      payload.sigma.val = R[b].input.time.val :=
        ReferenceAssignmentPayloadChronology.installationBirth_time_eq R[b] payload hbornAt
      _ = ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h + b := by
        simpa only [bFin] using
          (ReferenceAssignmentFollowerMassSteps.complete_record_time rate rewards C_star C_h source bFin)
  have hindex : b'.val = b := by omega
  have hbornCurrent : ReferenceAssignmentPayloadPersistence.InstallationBirth R[b] P' := by
    simpa only [hindex] using hborn'
  have hpayload : P' = payload :=
    ReferenceAssignmentPayloadChronology.installationBirth_payload_unique
      R[b] P' payload hbornCurrent hbornAt
  have hmessageCurrent : M = payload.downRecord i :=
    hmessage.trans (congrArg (fun x : ReferenceActivePhysicalStep.Payload rate => x.downRecord i)
      hpayload)
  have hretainedCurrent : ReferenceAcceptedUpFollowerHistory.RetainedDown
      R[a.val] i (payload.downRecord i) := by
    simpa only [hmessageCurrent] using hretained
  exact ⟨a, by omega, hak, hretainedCurrent⟩

private theorem complete_record_row
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length) :
    (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[k.val].input.row =
      z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) := by
  obtain ⟨_, _, hr⟩ := ReferenceLaterLiveNumericalReadout.source_record_prefix
    rate rewards C_star C_h z k
  change ((ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate z rewards C_star C_h).get k).input.row = _
  rw [hr]
  rfl

private theorem complete_mem_drop_index
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (e : ℕ)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).length)
    (hmem : (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val] ∈
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).drop e) :
    e ≤ k.val := by
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  obtain ⟨j, hj, hget⟩ := List.mem_iff_getElem.mp hmem
  have hjR : e + j < R.length := by
    change j < (R.drop e).length at hj
    rw [List.length_drop] at hj
    omega
  have heqR : R[e + j] = R[k.val] := by
    change (R.drop e)[j] = R[k.val] at hget
    simpa only [List.getElem_drop] using hget
  have ht1 := ReferenceAssignmentFollowerMassSteps.complete_record_time
    rate rewards C_star C_h z ⟨e + j, hjR⟩
  have ht2 := ReferenceAssignmentFollowerMassSteps.complete_record_time
    rate rewards C_star C_h z k
  change R[e + j].input.time.val =
    ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + (e + j) at ht1
  change R[k.val].input.time.val = _ at ht2
  rw [heqR] at ht1
  omega

private theorem cutoff_input_occupied_of_current_origin
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (P : ReferenceActivePhysicalStep.Payload rate)
    (i : Fin (p.m - 1)) (e : ℕ)
    (a k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).length)
    (he : e < (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).length)
    (haEarly : a.val < e) (hek : e ≤ k.val)
    (after state endpoint : ReferencePrelaunchFollower.State p rate.eta)
    (afterMemory memory endpointMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hafter : (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[a.val].output.next.followers i = .ordinary after afterMemory)
    (hafterStart : ReferencePrelaunchFollower.acceptedStart after = P.sigma.val + 1)
    (hconfiguration : (ReferenceFollowerFixedReply.actualChoice
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val] i).configuration = .ordinary state memory)
    (hstart : ReferencePrelaunchFollower.acceptedStart state = P.sigma.val + 1)
    (hinput : (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[e].input.state.followers i = .ordinary endpoint endpointMemory)
    (hterminalChoice : (ReferenceFollowerFixedReply.actualChoice
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[e] i).configuration = .ordinary {endpoint with status := .unoccupied} endpointMemory)
    (hcutoff : FollowerCutoffScan.firstCutoff p rate.eta.val P.sigma
      (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
        (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z))) =
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + e + 1) :
    endpoint.status ≠ .unoccupied := by
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let terminal : ReferencePrelaunchFollower.State p rate.eta := {endpoint with status := .unoccupied}
  obtain ⟨crossing, _, _⟩ := ReferenceLaterLiveNumericalReadout.source_record_prefix
    rate rewards C_star C_h z k
  have hchain := ReferenceCompletePhysicalHistory.completeSuffix_connected_on_launch
    rate z rewards C_star C_h
    (ReferenceFirstLaunchNumericalCell.launchState rate z rewards C_star C_h crossing)
    (ReferenceFirstLaunchNumericalCell.correctedLaunch_eq_some_launchState
      rate z rewards C_star C_h crossing)
  have hprefix := ReferenceFollowerReplyChronology.connected_take_to_input hchain e he
  obtain ⟨out, outMemory, hout, hlo⟩ :=
    ReferenceFollowerReplyChronology.connected_output_chronology hprefix i
      endpoint endpointMemory hinput a.val (by simp only [List.length_take]; omega)
  have haTake : a.val < (R.take e).length := by
    rw [List.length_take]
    exact lt_min haEarly a.isLt
  have hout' : R[a.val].output.next.followers i = .ordinary out outMemory := by
    change ((R.take e)[a.val]'haTake).output.next.followers i = _ at hout
    rw [List.getElem_take] at hout
    exact hout
  have heqAfter : out = after :=
    (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj (hout'.symm.trans hafter)).1
  subst out
  have hhi := (ReferenceFollowerReplyChronology.connected_choice_chronology hchain i
    e k.val he k.isLt hek terminal state endpointMemory memory
    hterminalChoice hconfiguration).1
  have hendpointStart : ReferencePrelaunchFollower.acceptedStart endpoint = P.sigma.val + 1 := by
    change ReferencePrelaunchFollower.acceptedStart endpoint ≤
      ReferencePrelaunchFollower.acceptedStart state at hhi
    omega
  obtain ⟨M, hM⟩ : ∃ M, endpoint.lastDown = some M := by
    cases hlastDown : endpoint.lastDown with
    | none => simp [ReferencePrelaunchFollower.acceptedStart, hlastDown] at hendpointStart
    | some M => exact ⟨M, rfl⟩
  have hcoordinate : ActiveFollowerDownAcceptance.downStart p rate M = P.sigma := by
    apply Fin.ext
    have hs : M.val.sigma = P.sigma.val + 1 := by
      simpa only [ReferencePrelaunchFollower.acceptedStart, hM] using hendpointStart
    have hcoord := ActiveFollowerLifecycle.accepted_start_coordinate_one_based M
    change (ActiveFollowerDownAcceptance.downStart p rate M).val + 1 = M.val.sigma at hcoord
    omega
  have hphase := ReferenceCompleteFollowerCutoffPhase.complete_ordinary_follower_phase
    rate rewards C_star C_h z ⟨e, he⟩ i endpoint endpointMemory hinput M hM
  intro hu
  have hle := hphase.mp hu
  change FollowerCutoffScan.firstCutoff p rate.eta.val
    (ActiveFollowerDownAcceptance.downStart p rate M)
    (FollowerCutoffScan.completeRowProposalBit p rate.eta.val R[e].input.row) ≤
    R[e].input.time.val at hle
  rw [hcoordinate, complete_record_row rate rewards C_star C_h z ⟨e, he⟩,
    hcutoff] at hle
  have hdate := ReferenceAssignmentFollowerMassSteps.complete_record_time
    rate rewards C_star C_h z ⟨e, he⟩
  change R[e].input.time.val =
    ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + e at hdate
  omega

private theorem choice_interval_retention
    {rate : ReferenceActivePhysicalStep.RateInput p}
    {initial final : ReferenceActivePhysicalStep.State p rate}
    {R : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))}
    (chain : ReferenceActivePhysicalHorizon.Connected initial R final)
    (i : Fin (p.m - 1)) (a b : Fin R.length)
    (left right : ReferencePrelaunchFollower.State p rate.eta)
    (leftMemory rightMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hl : (ReferenceFollowerFixedReply.actualChoice R[a.val] i).configuration = .ordinary left leftMemory)
    (hr : (ReferenceFollowerFixedReply.actualChoice R[b.val] i).configuration = .ordinary right rightMemory)
    (hu : left.status = .unoccupied)
    (heq : ReferencePrelaunchFollower.acceptedStart left = ReferencePrelaunchFollower.acceptedStart right) :
    (∀ n : Fin R.length, a.val ≤ n.val → n.val < b.val → ∀ sigma,
      ¬ ReferenceFollowerReplyChronology.appliedDown R[n.val] i sigma) ∧
    (∀ n : Fin R.length, a.val ≤ n.val → n.val ≤ b.val →
      ∃ state memory, (ReferenceFollowerFixedReply.actualChoice R[n.val] i).configuration = .ordinary state memory ∧
        state.status = .unoccupied ∧ ReferenceFollowerReplyChronology.reply state = ReferenceFollowerReplyChronology.reply left) := by
  obtain ⟨before, memory, hb, hreply, _⟩ :=
    ReferenceFollowerReplyChronology.record_input_to_choice R[b.val] i right rightMemory hr
  have hstart := ReferenceFollowerReplyChronology.acceptedStart_eq_of_reply_eq hreply
  have hprefixChain := ReferenceFollowerReplyChronology.connected_take_to_input chain b.val b.isLt
  constructor
  · intro n han hnb sigma happ
    have hn : n.val < (R.take b.val).length := by
      rw [List.length_take]
      exact lt_min hnb n.isLt
    obtain ⟨next, nextMemory, hout, hbound⟩ :=
      ReferenceFollowerReplyChronology.connected_output_chronology hprefixChain i before memory hb n.val hn
    rw [List.getElem_take] at hout
    obtain ⟨choice, choiceMemory, hc, hlt, hnext⟩ :=
      ReferenceFollowerReplyChronology.record_appliedDown_strict R[n.val] i sigma happ next nextMemory hout
    have hm := (ReferenceFollowerReplyChronology.connected_choice_chronology chain i a.val n.val
      a.isLt n.isLt han left choice leftMemory choiceMemory hl hc).1
    omega

  · intro n han hnb
    by_cases hn : n.val = b.val
    · have hsame : n = b := Fin.ext hn
      subst n
      obtain ⟨hunoccupied, hreply⟩ :=
        (ReferenceFollowerReplyChronology.connected_choice_chronology chain i a.val b.val a.isLt b.isLt han
          left right leftMemory rightMemory hl hr).2.1 hu heq
      exact ⟨right, rightMemory, hr, hunoccupied, hreply⟩
    · have hlt : n.val < b.val := by omega
      have hnTake : n.val < (R.take b.val).length := by rw [List.length_take]; exact lt_min hlt n.isLt
      obtain ⟨next, nextMemory, hout, _hbound⟩ :=
        ReferenceFollowerReplyChronology.connected_output_chronology hprefixChain i before memory hb n.val hnTake
      rw [List.getElem_take] at hout
      obtain ⟨choice, choiceMemory, hc, _hm, _hkeep, _hchange⟩ :=
        ReferenceFollowerReplyChronology.record_choice_chronology R[n.val] i next nextMemory hout
      have hleft := ReferenceFollowerReplyChronology.connected_choice_chronology chain i a.val n.val
        a.isLt n.isLt han left choice leftMemory choiceMemory hl hc
      have hright := (ReferenceFollowerReplyChronology.connected_choice_chronology chain i n.val b.val
        n.isLt b.isLt hnb choice right choiceMemory rightMemory hc hr).1
      obtain ⟨hunoccupied, hreply⟩ := hleft.2.1 hu (by omega)
      exact ⟨choice, choiceMemory, hc, hunoccupied, hreply⟩

private theorem current_choice_endpoint_fields
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
    (hborn : ReferenceAssignmentPayloadPersistence.InstallationBirth birth P) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let b := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.birthIndex rate rewards C_star C_h z
    let W := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.liveTail rate rewards C_star C_h z
    let V := (R.drop b).take (1 + W.length)
    let e := b + (1 + W.length)
    ∀ (_he : e < R.length),
    FollowerCutoffScan.firstCutoff p rate.eta.val P.sigma
      (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
        (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z))) =
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + e + 1 →
    ∀ (k : Fin R.length), e ≤ k.val →
        ∀ (selected : ReferenceActivePhysicalStep.Selection R[k.val].input),
        R[k.val].output.preparation.coordinator.selection = some selected →
        selected.view.payload = P →
        ∀ i (state : ReferencePrelaunchFollower.State p rate.eta)
          (memory : ActiveFollowerLifecycle.LocalMemory p),
        (ReferenceFollowerFixedReply.actualChoice R[k.val] i).configuration = .ordinary state memory →
        ReferencePrelaunchFollower.acceptedStart state = P.sigma.val + 1 →
        ∃ word, V.mapM (ReferenceFirstCorrectedAssignedArrivalPrefix.attributedArrival? P i) =
          some word ∧
          state.S = (QueueReplay.replay (4 * rate.n) (0, (P.downRecord i).val.q) word).1 ∧
          state.delta =
            (QueueReplay.replay (4 * rate.n) (0, (P.downRecord i).val.q) word).1 -
            (QueueReplay.replay (4 * rate.n) (0, (P.downRecord i).val.q)
              (word.take (V.length - 1))).1 ∧
          state.backlog = (QueueReplay.replay (4 * rate.n) (0, (P.downRecord i).val.q) word).2 ∧
          (∃ n : Fin R.length, e ≤ n.val ∧ n.val ≤ k.val ∧
            (n.val = e ∨ ∃ a0 : Fin R.length, e ≤ a0.val ∧ a0.val < k.val ∧
              ReferenceAcceptedUpFollowerHistory.RetainedDown R[a0.val] i (P.downRecord i) ∧ n.val = a0.val + 1) ∧
            ∃ terminal terminalMemory,
              (ReferenceFollowerFixedReply.actualChoice R[n.val] i).configuration = .ordinary terminal terminalMemory ∧
              terminal.status = .unoccupied ∧ terminal.lastDown = some (P.downRecord i) ∧
              ReferenceFollowerReplyChronology.reply state = ReferenceFollowerReplyChronology.reply terminal ∧
              (∀ j : Fin R.length, n.val ≤ j.val → j.val < k.val → ∀ sigma,
                ¬ ReferenceFollowerReplyChronology.appliedDown R[j.val] i sigma) ∧
              (∀ j : Fin R.length, n.val ≤ j.val → j.val ≤ k.val →
                ∃ s m, (ReferenceFollowerFixedReply.actualChoice R[j.val] i).configuration = .ordinary s m ∧
                  s.status = .unoccupied ∧
                  ReferenceFollowerReplyChronology.reply s = ReferenceFollowerReplyChronology.reply terminal)) := by
  intro R b W V e he hcutoff
  have htail :
      ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
          rate rewards C_star C_h z
          (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.birthIndex rate rewards C_star C_h z + 1) =
        ReferenceFirstCollectionCorrectedSliceNumericalPrefix.liveTail rate rewards C_star C_h z := by
    dsimp only [ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix,
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.liveTail,
      ReferenceFirstReplacementLiveFollowerPrefix.continuingTail,
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords]
    have htest : ReferenceCompleteLaterLiveComplementPrefixReplay.continuingTest
          (p := p) (rate := rate) =
        ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen := by
      funext r
      unfold ReferenceCompleteLaterLiveComplementPrefixReplay.continuingTest
        ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen
      cases r.output.preparation.coordinator with
      | live rv qv base chosen => cases chosen <;> rfl
      | first _ | collection _ _ _ _ _ | invalidCollectionCutoff | dagger => rfl
    rw [htest]
  obtain ⟨_L, _c, birthD, PD, _hL, _hc, _hinputs, _hlen, hbD, hbornD,
      _hSigma, _hqueues, _hdownQueues, _hV, hboundD, _hwords, _hcollection,
      hdiagnosticsD⟩ :=
    ReferenceFirstCorrectedNativeDownCalendarReplay.firstCell_native_down_calendar_replay
      rate rewards C_star C_h u t z hz
  have hbirthEq : birthD = birth := Option.some.inj (hbD.symm.trans hb)
  subst birthD
  have hPEq : PD = P :=
    ReferenceAssignmentPayloadChronology.installationBirth_payload_unique birth PD P hbornD hborn
  subst PD
  simp only [htail] at hboundD hdiagnosticsD
  obtain ⟨birthC, PC, hbC, hbornC, _hVC, hcarry⟩ :=
    ReferenceFirstCorrectedAssignedNativeFollowerPrefix.actual_first_corrected_first_cutoff_carry
      rate rewards C_star C_h u t z hz
  have hbirthCEq : birthC = birth := Option.some.inj (hbC.symm.trans hb)
  subst birthC
  have hPCEq : PC = P :=
    ReferenceAssignmentPayloadChronology.installationBirth_payload_unique birth PC P hbornC hborn
  subst PC
  have hcarry' := hcarry
  simp only [Nat.add_assoc] at hcarry'
  have hVlen : V.length = 1 + W.length := by
    change ((R.drop b).take (1 + W.length)).length = _
    rw [List.length_take, List.length_drop, Nat.min_eq_left]
    change b + (1 + W.length) ≤ R.length at hboundD
    omega
  have hbLt : b < R.length := (List.getElem?_eq_some_iff.mp hb).1
  have hbGet : R[b] = birth := (List.getElem?_eq_some_iff.mp hb).2
  have hbornAt : ReferenceAssignmentPayloadPersistence.InstallationBirth R[b] P := by
    rw [hbGet]
    exact hborn
  obtain ⟨crossing, _, _⟩ := ReferenceLaterLiveNumericalReadout.source_record_prefix
    rate rewards C_star C_h z ⟨b, hbLt⟩
  have hchain := ReferenceCompletePhysicalHistory.completeSuffix_connected_on_launch
    rate z rewards C_star C_h
    (ReferenceFirstLaunchNumericalCell.launchState rate z rewards C_star C_h crossing)
    (ReferenceFirstLaunchNumericalCell.correctedLaunch_eq_some_launchState
      rate z rewards C_star C_h crossing)
  intro k hek selected hselectedK hpK i state memory hconfiguration hstart
  obtain ⟨a, hba, hak, hretained⟩ := current_choice_down_origin
    rate rewards C_star C_h z b birth P hb hborn k i state memory hconfiguration hstart
  rcases hretained with ⟨logged, cut, after, raw, scan, registers, lastService,
    hlogged, hdown, houtcome⟩
  obtain ⟨hafterDown, _hafterS, _hafterDelta, _hafterQ, afterMemory, hafter⟩ :=
    ReferenceCompleteFollowerRetainedDownRecovery.complete_accepted_down_output
      rewards C_star C_h z a i logged after cut raw (P.downRecord i)
      scan registers lastService hlogged hdown houtcome
  have hafterStart : ReferencePrelaunchFollower.acceptedStart after = P.sigma.val + 1 := by
    rw [ReferencePrelaunchFollower.acceptedStart, hafterDown]
    exact congrArg OrdinaryMessageCodec.DownFields.sigma (P.downRecord_fields i)
  have hframe : ∀ (n : ℕ) (hn : n < R.length) (hnk : n ≤ k.val)
      (terminal : ReferencePrelaunchFollower.State p rate.eta)
      (terminalMemory : ActiveFollowerLifecycle.LocalMemory p),
      (ReferenceFollowerFixedReply.actualChoice R[n] i).configuration =
        .ordinary terminal terminalMemory →
      terminal.status = .unoccupied →
      terminal.lastDown = some (P.downRecord i) →
      ReferenceFollowerReplyChronology.reply state =
        ReferenceFollowerReplyChronology.reply terminal := by
    intro n hn hnk terminal terminalMemory ht hu hd
    have htStart : ReferencePrelaunchFollower.acceptedStart terminal = P.sigma.val + 1 := by
      rw [ReferencePrelaunchFollower.acceptedStart, hd]
      exact congrArg OrdinaryMessageCodec.DownFields.sigma (P.downRecord_fields i)
    exact (ReferenceFollowerReplyChronology.connected_choice_chronology hchain i
      n k.val hn k.isLt hnk terminal state terminalMemory memory ht hconfiguration).2.1
        hu (htStart.trans hstart.symm) |>.2
  by_cases haEarly : a.val < e
  · obtain ⟨endpoint, endpointMemory, hlast, _houtput, _hnext, hinput,
      _htime, _hstartRound, hchoice, hnumeric⟩ :=
      hcarry' R[e] (List.getElem?_eq_getElem he) i
    let terminal : ReferencePrelaunchFollower.State p rate.eta :=
      {endpoint with status := .unoccupied}
    have hterminalChoice : (ReferenceFollowerFixedReply.actualChoice R[e] i).configuration =
        .ordinary terminal endpointMemory := hchoice
    have hoccupied := cutoff_input_occupied_of_current_origin rate rewards C_star C_h z P i e
      a k he haEarly hek after state endpoint afterMemory memory endpointMemory
      hafter hafterStart hconfiguration hstart hinput hterminalChoice hcutoff
    obtain ⟨word, hword, hlastDown, hpair, hdelta⟩ := hnumeric hoccupied
    have hr := hframe e he hek terminal endpointMemory hterminalChoice rfl hlastDown
    have hreplyFields : state.S = endpoint.S ∧ state.delta = endpoint.delta ∧
        state.backlog = endpoint.backlog := by
      exact ⟨congrArg (fun r => r.2.1) hr,
        congrArg (fun r => r.2.2.1) hr, congrArg (fun r => r.2.2.2) hr⟩
    refine ⟨word, hword, ?_, ?_, ?_, ?_⟩
    · exact hreplyFields.1.trans (congrArg Prod.fst hpair)
    · exact hreplyFields.2.1.trans hdelta
    · exact hreplyFields.2.2.trans (congrArg Prod.snd hpair)
    · exact ⟨⟨e, he⟩, le_rfl, hek, Or.inl rfl, terminal, endpointMemory, hterminalChoice, rfl, hlastDown, hr,
        choice_interval_retention hchain i ⟨e, he⟩ k terminal state endpointMemory memory
          hterminalChoice hconfiguration rfl (ReferenceFollowerReplyChronology.acceptedStart_eq_of_reply_eq hr.symm)⟩
  · obtain ⟨selectedA, hselectedA, hpA⟩ :=
      ReferenceFirstCorrectedNativeDownCalendarReplay.complete_birth_current_selected_interval
        rewards C_star C_h z ⟨b, hbLt⟩ k P hbornAt (hba.trans hak.le)
        selected hselectedK hpK a hba hak
    have hdiag := (hdiagnosticsD a hba i).2.2 selectedA hselectedA
    rw [ite_eq_left hpA] at hdiag
    obtain ⟨_, _, word, hword, _hM, _hscan, _hvpos, _hvN, hlate, _hseed,
      _hno, _hrecovery, _hchecked, hreplay, _hprefix, _hservice, hdelta,
      _hdownAfter, _hSAfter, _hdeltaAfter, _hqAfter, _hmem⟩ :=
      hdiag logged logged after cut raw (P.downRecord i) scan registers lastService
        hlogged hdown houtcome
    obtain ⟨hscanU, hv⟩ := hlate (by change e ≤ a.val; omega)
    change scan.endpoint - (P.sigma.val + 1) = 1 + W.length at hv
    change (V.take (scan.endpoint - (P.sigma.val + 1))).mapM
      (ReferenceFirstCorrectedAssignedArrivalPrefix.attributedArrival? P i) = some word at hword
    have hwhole : V.mapM (ReferenceFirstCorrectedAssignedArrivalPrefix.attributedArrival? P i) =
        some word := by
      rw [hv, ← hVlen, List.take_length] at hword
      exact hword
    have hrow := complete_record_row rate rewards C_star C_h z a
    have hdate := ReferenceAssignmentFollowerMassSteps.complete_record_time
      rate rewards C_star C_h z a
    have htail : FollowerCutoffScan.firstCutoff p rate.eta.val P.sigma
        (FollowerCutoffScan.completeRowProposalBit p rate.eta.val R[a.val].input.row) ≤
        R[a.val].input.time.val + 2 := by
      rw [hrow, hcutoff, hdate]
      omega
    have hscan' : scan.endpoint = min
        (FollowerCutoffScan.firstCutoff p rate.eta.val P.sigma
          (FollowerCutoffScan.completeRowProposalBit p rate.eta.val R[a.val].input.row))
        (R[a.val].input.time.val + 2) := by
      rw [Nat.min_eq_left htail, hrow]
      exact hscanU
    obtain ⟨terminal, terminalMemory, ht, hu, hd, hpair, hdel⟩ :=
      ReferenceCompleteFollowerContinuationKernel.accepted_down_next_cutoff_choice
        rewards C_star C_h z a i P logged after cut raw scan registers lastService
        hlogged hdown houtcome ((Nat.succ_le_iff.mpr hak).trans_lt k.isLt) hscan' htail
    have hr := hframe (a.val + 1) ((Nat.succ_le_iff.mpr hak).trans_lt k.isLt)
      (Nat.succ_le_iff.mpr hak)
      terminal terminalMemory ht hu hd
    have hreplyFields : state.S = terminal.S ∧ state.delta = terminal.delta ∧
        state.backlog = terminal.backlog := by
      exact ⟨congrArg (fun r => r.2.1) hr,
        congrArg (fun r => r.2.2.1) hr, congrArg (fun r => r.2.2.2) hr⟩
    refine ⟨word, hwhole, ?_, ?_, ?_, ?_⟩
    · exact hreplyFields.1.trans ((congrArg Prod.fst hpair).trans (congrArg Prod.fst hreplay))
    · rw [hreplyFields.2.1, hdel, hdelta, hv, ← hVlen]
    · exact hreplyFields.2.2.trans ((congrArg Prod.snd hpair).trans (congrArg Prod.snd hreplay))
    · exact ⟨⟨a.val + 1, (Nat.succ_le_iff.mpr hak).trans_lt k.isLt⟩,
        by dsimp only; omega, Nat.succ_le_iff.mpr hak,
        Or.inr ⟨a, by omega, hak,
          ⟨logged, cut, after, raw, scan, registers, lastService, hlogged, hdown, houtcome⟩, rfl⟩,
        terminal, terminalMemory, ht, hu, hd, hr,
        choice_interval_retention hchain i ⟨a.val + 1, (Nat.succ_le_iff.mpr hak).trans_lt k.isLt⟩ k
          terminal state terminalMemory memory ht hconfiguration hu
          (ReferenceFollowerReplyChronology.acceptedStart_eq_of_reply_eq hr.symm)⟩

private theorem current_choice_tail
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).length)
    (P : ReferenceActivePhysicalStep.Payload rate)
    (selected : ReferenceActivePhysicalStep.Selection
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val].input)
    (hselected : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[k.val].output.preparation.coordinator.selection = some selected)
    (hpayload : selected.view.payload = P)
    (i : Fin (p.m - 1)) (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hchoice : (ReferenceFollowerFixedReply.actualChoice
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val] i).configuration =
      .ordinary state memory)
    (hu : state.status = .unoccupied)
    (hs : ReferencePrelaunchFollower.acceptedStart state = P.sigma.val + 1) :
    let r := (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val]
    (∀ sigma, ¬ ReferenceFollowerReplyChronology.appliedDown r i sigma) ∧
    ∃ next nextMemory, r.output.next.followers i = .ordinary next nextMemory ∧
      next.status = .unoccupied ∧
      ReferenceFollowerReplyChronology.reply next = ReferenceFollowerReplyChronology.reply state := by
  intro r
  change r.output.preparation.coordinator.selection = some selected at hselected
  obtain ⟨_before, _memory, _choice, next, nextMemory, _hin, _hc, _hdom, _hndom,
    _houtput, _hfailure, hnext⟩ :=
    ReferenceCompleteSuffixFollowerPreservation.complete_suffix_follower_output
      (rate := rate) rewards C_star C_h z k i
  have hno : ∀ sigma, ¬ ReferenceFollowerReplyChronology.appliedDown r i sigma := by
    intro sigma happ
    obtain ⟨choice, choiceMemory, hc, hstrict, _hnextStart⟩ :=
      ReferenceFollowerReplyChronology.record_appliedDown_strict r i sigma happ next nextMemory hnext
    have heq : choice = state :=
      (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj (hc.symm.trans hchoice)).1
    subst choice
    rcases happ with ⟨logged, cut, after, raw, M, scan, registers, lastService,
      hlogged, hdown, houtcome, hMsigma⟩
    obtain ⟨_choice, _mem, actualLogged, _hchoice, _hu, _hlog, hinput, hcut⟩ :=
      ReferenceFollowerSparseEmissionRecovery.actualDownDiagnostic_choice r i cut hdown
    have hlogEq : actualLogged = logged := Option.some.inj (hinput.symm.trans hlogged)
    subst actualLogged
    have haccepted := houtcome
    rw [hcut] at haccepted
    have hview : r.output.preparation.coordinator.downView = some selected.view := by
      simp only [ReferenceActivePhysicalStep.DispatchCut.downView, hselected, Option.map_some]
    rw [hview] at haccepted
    have hM := (ReferenceActiveDataOwnership.referenceDown_accepted_fields selected.view
      _ _ _ _ logged logged after raw M scan registers lastService haccepted).1
    have halign := r.output.preparation.follower_alignment i
    rw [halign.2.1, hpayload] at hM
    have hstartM : M.val.sigma = P.sigma.val + 1 := by
      rw [hM]
      exact congrArg OrdinaryMessageCodec.DownFields.sigma (P.downRecord_fields i)
    omega
  obtain ⟨choice, choiceMemory, hc, _hm, hkeep, hchange⟩ :=
    ReferenceFollowerReplyChronology.record_choice_chronology r i next nextMemory hnext
  have heq : choice = state :=
    (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj (hc.symm.trans hchoice)).1
  subst choice
  have hsame : ReferencePrelaunchFollower.acceptedStart state =
      ReferencePrelaunchFollower.acceptedStart next := by
    by_contra hne
    exact hno _ (hchange hne)
  exact ⟨hno, next, nextMemory, hnext, hkeep hu hsame⟩

private theorem complete_collection_reply_window
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (j : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).length)
    (P : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate) (saved : Option (Fin p.T × Bool))
    (hcoord : (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[j.val].input.state.coordinator =
      .collection P ledger saved)
    (i : Fin (p.m - 1)) (seed : ReferencePrelaunchFollower.State p rate.eta)
    (seedMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hseed : (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[j.val].input.state.followers i =
      .ordinary seed seedMemory)
    (hu : seed.status = .unoccupied)
    (hs : ReferencePrelaunchFollower.acceptedStart seed = P.sigma.val + 1) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let F := (R.drop j.val).takeWhile fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input
    (∀ n, n < F.length → ∀ (hn : j.val + n < R.length) sigma,
      ¬ ReferenceFollowerReplyChronology.appliedDown R[j.val + n] i sigma) ∧
    (∀ n, n ≤ F.length → ∀ (hn : j.val + n < R.length),
      (n = F.length → ReferenceCollectionPhaseHistory.laterChosen R[j.val + n].input = true) ∧
      ((ReferenceFollowerFixedReply.actualChoice R[j.val + n] i).configuration = .dagger ∨
        ∃ state memory,
          (ReferenceFollowerFixedReply.actualChoice R[j.val + n] i).configuration = .ordinary state memory ∧
          state.status = .unoccupied ∧
          ReferenceFollowerReplyChronology.reply state = ReferenceFollowerReplyChronology.reply seed)) := by
  intro R F
  have hj : j.val < R.length := j.isLt
  obtain ⟨span, mode, hrecords⟩ :=
    ReferenceCompleteFollowerRetainedDownRecovery.complete_input_suffix_reindex
      (rate := rate) rewards C_star C_h z j (R.length - j.val)
      (by change j.val + (R.length - j.val) ≤ R.length; omega)
  let initial := R[j.val].input.state
  let rows := z.1.2
  let J := ActualInitializationPhysicalStep.selectedRowIndex p z
  let start := R[j.val].input.time.val
  let count := R.length - j.val
  let X := ReferenceActivePhysicalHorizon.run initial rows J rewards start count span mode
  change X.records = (R.drop j.val).take count at hrecords
  have hlength : (R.drop j.val).length = count := List.length_drop
  rw [← hlength, List.take_length] at hrecords
  have hcoord0 : (ReferenceActivePhysicalHorizon.run initial rows J rewards start 0
      (by omega) mode).finalState.coordinator = .collection P ledger saved := by
    rw [ReferenceActivePhysicalHorizon.run_zero_final]
    exact hcoord
  have hseed0 : (ReferenceActivePhysicalHorizon.run initial rows J rewards start 0
      (by omega) mode).finalState.followers i = .ordinary seed seedMemory := by
    rw [ReferenceActivePhysicalHorizon.run_zero_final]
    exact hseed
  obtain ⟨_hprefix, hno, hchoices⟩ :=
    ReferenceCutoffUpReplyInterval.collectionWindowProducers_of_boundary
      initial rows J rewards start count span mode 0 (Nat.zero_le _) P ledger saved
      hcoord0 i seed seedMemory hseed0 hu hs
  have hrecords' : (ReferenceActivePhysicalHorizon.run initial rows J rewards start count span mode).records =
      R.drop j.val := hrecords
  have hF : (X.records.drop 0).takeWhile
      (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input) = F := by
    rw [List.drop_zero, hrecords]
  constructor
  · intro n hn hrec sigma
    have hnX : 0 + n < X.records.length := by
      rw [Nat.zero_add, hrecords, List.length_drop]
      omega
    have hnF : n < ((X.records.drop 0).takeWhile
        (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)).length := hF ▸ hn
    have h := hno n hnF hnX sigma
    simpa only [Nat.zero_add, List.get_eq_getElem, hrecords', List.getElem_drop] using h
  · intro n hn hrec
    have hnX : 0 + n < X.records.length := by
      rw [Nat.zero_add, hrecords, List.length_drop]
      omega
    have hnF : n ≤ ((X.records.drop 0).takeWhile
        (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)).length := hF ▸ hn
    have h := hchoices n hnF hnX
    simpa only [Nat.zero_add, List.get_eq_getElem, hrecords', List.drop_zero,
      List.getElem_drop] using h

private theorem completed_current_collection_output
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (P : ReferenceActivePhysicalStep.Payload rate)
    (selected : ReferenceActivePhysicalStep.Selection r.input)
    (hselected : r.output.preparation.coordinator.selection = some selected)
    (hp : selected.view.payload = P)
    (hcomplete : (ReferenceCollectionSegmentExtraction.extractRound r).isSome = true) :
    ∃ ledger saved, r.output.next.coordinator = .collection P ledger saved := by
  obtain ⟨done, hdone⟩ := Option.isSome_iff_exists.mp hcomplete
  obtain ⟨_hc, _ht, _hchecked, payload, saved, hnext⟩ :=
    ReferenceCollectionSegmentExtraction.actual_collection_round_checked r done hdone
  have hstored : ReferenceAssignmentPayloadPersistence.storedPayload
      (ReferenceActivePhysicalStep.step r.input).next.coordinator = some payload := by
    rw [← r.output_eq, hnext]
    rfl
  have hselectedPayload := ReferenceGeneratedUpSitePayloadOrder.actual_step_stored_payload_eq_selected
    r.input payload hstored
  have hr : ReferenceAssignmentPayloadChronology.actualStepRecord r.input = r := by
    cases r with
    | mk input output ho => cases ho; rfl
  rw [hr] at hselectedPayload
  simp only [ReferenceAssignmentPayloadPersistence.selectedPayload, hselected,
    Option.map_some, Option.some.injEq] at hselectedPayload
  have hpay : payload = P := hselectedPayload.symm.trans hp
  rw [hpay] at hnext
  exact ⟨done.final, saved, hnext⟩

private theorem collection_tail_up_eq_receive
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (P : ReferenceActivePhysicalStep.Payload rate) (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (weights : CanonicalFastSampling.FastArm P.slowSet → ℝ)
    (actual : ReferenceActivePhysicalStep.Ledger rate)
    (hsite : ReferenceCoordinatorUpPhysicalCall.tailLedger?
      (ReferenceActivePhysicalStep.prepare x) P ledger started weights = some actual) :
    (ReferenceActivePhysicalStep.collectionPostChoice (ReferenceActivePhysicalStep.prepare x)
      P ledger started weights).up =
      (ReferenceActivePhysicalStep.receiveUp (ReferenceActivePhysicalStep.prepare x) actual).diagnostic := by
  unfold ReferenceCoordinatorUpPhysicalCall.tailLedger? at hsite
  cases hr : CoordinatorRecorderComplementBridge.run
      (ReferenceActivePhysicalStep.collectionRecordingInput
        (ReferenceActivePhysicalStep.prepare x) P started weights) with
  | none => simp only [hr, reduceCtorEq] at hsite
  | some recording =>
    simp only [hr] at hsite
    cases hs : CoordinatorCollectionLedger.startRound ledger (x.time.val + 1)
        (ReferenceActivePhysicalStep.collectionEnabled ledger x.time)
        (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) with
    | invalid => simp only [hs, reduceCtorEq] at hsite
    | rejected _ => simp only [hs, reduceCtorEq] at hsite
    | success found =>
      simp only [hs, Option.some.injEq] at hsite
      subst found
      simp only [ReferenceActivePhysicalStep.collectionPostChoice, hr, hs]
      exact ReferenceActiveAffinePositiveTest.collectionFinish_up x P started recording _

private theorem record_up_eq_receive
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (hsite : ReferenceCoordinatorUpPhysicalCall.siteLedger? (x := r.input) = some ledger) :
    r.output.coordinator.up =
      (ReferenceActivePhysicalStep.receiveUp (ReferenceActivePhysicalStep.prepare r.input) ledger).diagnostic := by
  have hout : r.output.coordinator = (ReferenceActivePhysicalStep.prepare r.input).observeCoordinator := by
    rw [r.output_eq]
    rfl
  rw [hout]
  unfold ReferenceCoordinatorUpPhysicalCall.siteLedger? at hsite
  dsimp only at hsite
  split at hsite
  · cases hsite
  next hsel =>
    unfold ReferenceActivePhysicalStep.PreparedRound.observeCoordinator
    rw [dite_eq_right hsel]
    cases hc : (ReferenceActivePhysicalStep.prepare r.input).coordinator with
    | first outcome => cases outcome <;> simp only [hc, reduceCtorEq] at hsite
    | invalidCollectionCutoff => simp only [hc, reduceCtorEq] at hsite
    | dagger => simp only [hc, reduceCtorEq] at hsite
    | live registers owned base outcome =>
      cases outcome <;> simp only [hc, reduceCtorEq] at hsite
      next dispatched hs actual hi he hd hclock hp hn selected =>
        dsimp only
        exact collection_tail_up_eq_receive r.input _ _ _ _ ledger hsite
    | collection payload old clock cutoff outcome =>
      cases outcome <;> simp only [hc, reduceCtorEq] at hsite
      next core snapshot boundary scores =>
        dsimp only
        exact collection_tail_up_eq_receive r.input _ _ _ _ ledger hsite

private theorem retained_wrong_unique_iff
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (d : ReferenceActivePhysicalStep.UpDiagnostic p rate)
    (hd : r.output.coordinator.up = some d) :
    d.wrongUniqueAccepted = true ↔
      ∃ word parsed, d.raw = some word ∧
        CoordinatorUpReception.parseDecoderOutput (p := p) (eta := rate.eta.val)
          (some word) = some parsed ∧
        CoordinatorCollectionLedger.acceptUpCheck d.input.ledger d.input.selectedFollower parsed = true ∧
        some word ≠ d.expected := by
  obtain ⟨ledger, hsite, hcheck, _hinput, _hafter⟩ :=
    ReferenceCoordinatorUpPhysicalCall.record_retained_up_input r d hd
  have hdiag := (record_up_eq_receive r ledger hsite).symm.trans hd
  unfold ReferenceActivePhysicalStep.receiveUp at hdiag
  dsimp only at hdiag
  have hc : CoordinatorUpReception.receptionInputCheck
      (ReferenceUpReception.receptionInputAtRow rate r.input.row
        (ReferenceActivePhysicalStep.upInputs (ReferenceActivePhysicalStep.prepare r.input) ledger)
          r.input.time) = true := hcheck
  simp only [hc, ite_true, Option.some.injEq] at hdiag
  rw [← hdiag]
  exact ReferenceUpReception.wrongUniqueAndLocalAcceptanceAtRow_eq_true_iff rate r.input.row
    (ReferenceActivePhysicalStep.upInputs (ReferenceActivePhysicalStep.prepare r.input) ledger)
    r.input.time _ _ _ _ rfl

private theorem raw_current_offer
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (d : ReferenceActivePhysicalStep.UpDiagnostic p rate)
    (offered : OrdinaryMessageCodec.UpRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (hraw : d.raw = (CoordinatorUpReception.decoderTransition d.input).2)
    (hparsed : d.parsed = ReferenceUpReception.rawParsedOutput rate d.input)
    (hexpected : d.expected = some ((OrdinaryMessageCodec.wordEquivFlat
      (CoordinatorCollectionLedger.codecParams p rate.eta.val))
      (OrdinaryMessageCodec.encodeUp (CoordinatorCollectionLedger.codecParams p rate.eta.val) offered)))
    (hequal : d.raw = d.expected) :
    d.parsed = some offered ∧
      CoordinatorUpReception.parseDecoderOutput
        (ReferenceUpReception.filterRawByExpected d.raw d.expected) = some offered := by
  have hword := hequal.trans hexpected
  have hparse : CoordinatorUpReception.parseDecoderOutput d.raw = some offered := by
    rw [hword]
    change OrdinaryMessageCodec.parseUp (CoordinatorCollectionLedger.codecParams p rate.eta.val)
      (some ((OrdinaryMessageCodec.wordEquivFlat
        (CoordinatorCollectionLedger.codecParams p rate.eta.val)).symm
        ((OrdinaryMessageCodec.wordEquivFlat (CoordinatorCollectionLedger.codecParams p rate.eta.val))
          (OrdinaryMessageCodec.encodeUp (CoordinatorCollectionLedger.codecParams p rate.eta.val) offered)))) = _
    rw [Equiv.symm_apply_apply]
    exact OrdinaryMessageCodec.parseUp_encode _ offered
  constructor
  · rw [hparsed]
    change CoordinatorUpReception.parseDecoderOutput (CoordinatorUpReception.decoderTransition d.input).2 = _
    rw [← hraw]
    exact hparse
  · rw [ReferenceUpReception.filterRawByExpected_eq_raw_of_eq d.raw d.expected hequal]
    exact hparse

private theorem current_choice_future
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
    (hborn : ReferenceAssignmentPayloadPersistence.InstallationBirth birth P) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let b := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.birthIndex rate rewards C_star C_h z
    let W := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.liveTail rate rewards C_star C_h z
    let V := (R.drop b).take (1 + W.length)
    let e := b + (1 + W.length)
    ∀ (_he : e < R.length),
    FollowerCutoffScan.firstCutoff p rate.eta.val P.sigma
      (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
        (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z))) =
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + e + 1 →
    ∀ k : Fin R.length, e ≤ k.val →
              ∀ (selected : ReferenceActivePhysicalStep.Selection R[k.val].input),
              R[k.val].output.preparation.coordinator.selection = some selected →
              selected.view.payload = P →
              (ReferenceCollectionSegmentExtraction.extractRound R[k.val]).isSome = true →
              ∀ i (state : ReferencePrelaunchFollower.State p rate.eta)
                (memory : ActiveFollowerLifecycle.LocalMemory p),
              (ReferenceFollowerFixedReply.actualChoice R[k.val] i).configuration = .ordinary state memory →
              state.status = .unoccupied →
              ReferencePrelaunchFollower.acceptedStart state = P.sigma.val + 1 →
              ∃ a : Fin R.length,
                b ≤ a.val ∧ a.val < k.val ∧
                ReferenceAcceptedUpFollowerHistory.RetainedDown
                  R[a.val] i (P.downRecord i) ∧
                ∃ word, V.mapM (ReferenceFirstCorrectedAssignedArrivalPrefix.attributedArrival? P i) =
                  some word ∧
                  state.S = (QueueReplay.replay (4 * rate.n) (0, (P.downRecord i).val.q) word).1 ∧
                  state.delta =
                    (QueueReplay.replay (4 * rate.n) (0, (P.downRecord i).val.q) word).1 -
                    (QueueReplay.replay (4 * rate.n) (0, (P.downRecord i).val.q)
                      (word.take (V.length - 1))).1 ∧
                  state.backlog = (QueueReplay.replay (4 * rate.n) (0, (P.downRecord i).val.q) word).2 ∧
                (∃ n : Fin R.length, e ≤ n.val ∧ n.val ≤ k.val ∧
            (n.val = e ∨ ∃ a0 : Fin R.length, e ≤ a0.val ∧ a0.val < k.val ∧
              ReferenceAcceptedUpFollowerHistory.RetainedDown R[a0.val] i (P.downRecord i) ∧ n.val = a0.val + 1) ∧
            ∃ terminal terminalMemory,
              (ReferenceFollowerFixedReply.actualChoice R[n.val] i).configuration = .ordinary terminal terminalMemory ∧
              terminal.status = .unoccupied ∧ terminal.lastDown = some (P.downRecord i) ∧
              ReferenceFollowerReplyChronology.reply state = ReferenceFollowerReplyChronology.reply terminal ∧
              (∀ j : Fin R.length, n.val ≤ j.val → j.val < k.val → ∀ sigma,
                ¬ ReferenceFollowerReplyChronology.appliedDown R[j.val] i sigma) ∧
              (∀ j : Fin R.length, n.val ≤ j.val → j.val ≤ k.val →
                ∃ s m, (ReferenceFollowerFixedReply.actualChoice R[j.val] i).configuration = .ordinary s m ∧
                  s.status = .unoccupied ∧
                  ReferenceFollowerReplyChronology.reply s = ReferenceFollowerReplyChronology.reply terminal)) ∧
                (∀ sigma, ¬ ReferenceFollowerReplyChronology.appliedDown R[k.val] i sigma) ∧
                ∃ next nextMemory,
                  R[k.val].output.next.followers i = .ordinary next nextMemory ∧
                  next.status = .unoccupied ∧
                  ReferenceFollowerReplyChronology.reply next = ReferenceFollowerReplyChronology.reply state ∧
                  ∀ (hsucc : k.val + 1 < R.length),
                    let F := (R.drop (k.val + 1)).takeWhile
                      fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input
                    (∀ n, n < F.length → ∀ (hn : k.val + 1 + n < R.length) sigma,
                      ¬ ReferenceFollowerReplyChronology.appliedDown R[k.val + 1 + n] i sigma) ∧
                    (∀ n, n ≤ F.length → ∀ (hn : k.val + 1 + n < R.length),
                      (n = F.length →
                        ReferenceCollectionPhaseHistory.laterChosen R[k.val + 1 + n].input = true) ∧
                      ((ReferenceFollowerFixedReply.actualChoice R[k.val + 1 + n] i).configuration = .dagger ∨
                        ∃ s m,
                          (ReferenceFollowerFixedReply.actualChoice R[k.val + 1 + n] i).configuration = .ordinary s m ∧
                          s.status = .unoccupied ∧
                          ReferenceFollowerReplyChronology.reply s = ReferenceFollowerReplyChronology.reply next)) := by
  intro R b W V e he hcutoff
  have hcurrentFields := current_choice_endpoint_fields rate rewards C_star C_h u t z hz
    birth P hb hborn he hcutoff
  intro k hek selected hs hp hcomplete i state memory hconfiguration hu hstart
  obtain ⟨a, hba, hak, hretained⟩ := current_choice_down_origin
    rate rewards C_star C_h z b birth P hb hborn k i state memory hconfiguration hstart
  obtain ⟨word, hwordV, hS, hdelta, hq, hterminalSeed⟩ :=
    hcurrentFields k hek selected hs hp i state memory hconfiguration hstart
  obtain ⟨hno, next, nextMemory, hnext, hnextUnoccupied, hreply⟩ :=
    current_choice_tail rate rewards C_star C_h z k P selected hs hp
      i state memory hconfiguration hu hstart
  refine ⟨a, hba, hak, hretained, word, hwordV, hS, hdelta, hq, hterminalSeed,
    hno, next, nextMemory, hnext, hnextUnoccupied, hreply, ?_⟩
  intro hsucc
  obtain ⟨ledger, saved, hcoord⟩ := completed_current_collection_output R[k.val] P
    selected hs hp hcomplete
  have hadj := ReferenceCompleteLaterLiveComplementPrefixReplay.complete_adjacent
    (rate := rate) rewards C_star C_h z k.val hsucc
  have hcoordIn : R[k.val + 1].input.state.coordinator = .collection P ledger saved := by
    rw [hadj]
    exact hcoord
  have hseedIn : R[k.val + 1].input.state.followers i = .ordinary next nextMemory := by
    rw [hadj]
    exact hnext
  have hnextStart : ReferencePrelaunchFollower.acceptedStart next = P.sigma.val + 1 :=
    (ReferenceFollowerReplyChronology.acceptedStart_eq_of_reply_eq hreply).trans hstart
  exact complete_collection_reply_window rate rewards C_star C_h z ⟨k.val + 1, hsucc⟩
    P ledger saved hcoordIn i next nextMemory hseedIn hnextUnoccupied hnextStart

/-- Actual current replies have the native cutoff registers. Their derived
terminal CHOICE and all intervening choices retain the whole reply without an
applied DOWN. The actual successor suffix retains it through the first later
CHOICE, excluding that CHOICE's tail. Late DOWN outputs need no successor.
This internal source consumer makes no UP acceptance or delivery assumption. -/
theorem actual_first_corrected_current_cutoff_reply_retention
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
    ∃ (L : List (RecordedQueueRun.RoundInput p.K))
      (c : RecordedQueueRun.RoundInput p.K)
      (birth : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
      (P : ReferenceActivePhysicalStep.Payload rate)
      (base : Fin (p.m - 1) → ℕ),
      ReferenceFirstCollectionCurrentRetainedGate.pastCells? rate rewards C_star C_h t z = some L ∧
      ReferenceFirstCollectionCurrentNumericalCell.currentCell rate rewards C_star C_h t z = some c ∧
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs rate rewards C_star C_h
        (t.val + 1) z = some (L ++ [c]) ∧
      L.length = b ∧ R[b]? = some birth ∧
      ReferenceAssignmentPayloadPersistence.InstallationBirth birth P ∧ P.sigma = t ∧
      (∀ a, P.queues a = (UnstoppedRecordedQueueComparison.unstoppedReplay
        (ReferenceFirstLaunchNumericalCell.queueParameters rate) L L.length a).2) ∧
      (∀ i, base i = (UnstoppedRecordedQueueComparison.unstoppedReplay
          (ReferenceFirstLaunchNumericalCell.queueParameters rate) L L.length
          (P.assignment.assigned i)).1 ∧
        (P.downRecord i).val.q = (UnstoppedRecordedQueueComparison.unstoppedReplay
          (ReferenceFirstLaunchNumericalCell.queueParameters rate) L L.length
          (P.assignment.assigned i)).2) ∧
      V = birth :: W ∧ b + (1 + W.length) ≤ R.length ∧
      (t.val + 1 = p.T → b + 1 = R.length ∧ W = [] ∧ V.length = 1) ∧
      (∀ (i : Fin (p.m - 1)) (j : ℕ) (hj : j < V.length),
        let r := V[j]
        ∃ input memory choice next nextMemory,
          R[b + j]? = some r ∧
          r.input.state.followers i = .ordinary input memory ∧
          ActiveFollowerLifecycle.startRound rate.eta r.input.time input memory = .ok (choice, memory) ∧
          (r.output.preparation.followers.followers i).configuration = .ordinary choice memory ∧
          (r.output.followers i).configuration = .ordinary next nextMemory ∧
          (r.output.followers i).failure = none ∧
          r.output.next.followers i = .ordinary next nextMemory ∧
          (j = 0 → input.status = .unoccupied) ∧
          (1 ≤ j → input.status ≠ .unoccupied → ∃ word,
            (V.take j).mapM (ReferenceFirstCorrectedAssignedArrivalPrefix.attributedArrival? P i) =
              some word ∧
            input.lastDown = some (P.downRecord i) ∧
            (input.S, input.backlog) =
              QueueReplay.replay (4 * rate.n) (0, (P.downRecord i).val.q) word) ∧
          (next.status ≠ .unoccupied → ∃ word,
            (V.take (j + 1)).mapM
                (ReferenceFirstCorrectedAssignedArrivalPrefix.attributedArrival? P i) =
              some word ∧
            next.lastDown = some (P.downRecord i) ∧
            (next.S, next.backlog) =
              QueueReplay.replay (4 * rate.n) (0, (P.downRecord i).val.q) word ∧
            next.delta =
              (QueueReplay.replay (4 * rate.n) (0, (P.downRecord i).val.q) word).1 -
                (QueueReplay.replay (4 * rate.n) (0, (P.downRecord i).val.q)
                  (word.take j)).1) ∧
          (∀ hnext : j + 1 < V.length,
            (V[j + 1]).input.state.followers i = .ordinary next nextMemory ∧
            (V[j + 1]).input.time.val = r.input.time.val + 1)) ∧
      (∀ (cutoff : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)),
        R[e]? = some cutoff → ∀ i : Fin (p.m - 1),
        ∃ (endpoint : ReferencePrelaunchFollower.State p rate.eta)
          (memory : ActiveFollowerLifecycle.LocalMemory p)
          (hlast : V.length - 1 < V.length),
          ((V[V.length - 1]).output.followers i).configuration = .ordinary endpoint memory ∧
          (V[V.length - 1]).output.next.followers i = .ordinary endpoint memory ∧
          cutoff.input.state.followers i = .ordinary endpoint memory ∧
          cutoff.input.time.val = (V[V.length - 1]).input.time.val + 1 ∧
          ActiveFollowerLifecycle.startRound rate.eta cutoff.input.time endpoint memory =
            .ok ({endpoint with status := .unoccupied}, memory) ∧
          (cutoff.output.preparation.followers.followers i).configuration =
            .ordinary {endpoint with status := .unoccupied} memory ∧
          (endpoint.status ≠ .unoccupied → ∃ word,
            V.mapM (ReferenceFirstCorrectedAssignedArrivalPrefix.attributedArrival? P i) =
              some word ∧
            endpoint.lastDown = some (P.downRecord i) ∧
            (endpoint.S, endpoint.backlog) =
              QueueReplay.replay (4 * rate.n) (0, (P.downRecord i).val.q) word ∧
            endpoint.delta =
              (QueueReplay.replay (4 * rate.n) (0, (P.downRecord i).val.q) word).1 -
                (QueueReplay.replay (4 * rate.n) (0, (P.downRecord i).val.q)
                  (word.take (V.length - 1))).1)) ∧
      (∀ i : Fin (p.m - 1), ∀ v, v ≤ 1 + W.length → ∃! word,
        (V.take v).mapM
          (ReferenceFirstCorrectedAssignedArrivalPrefix.attributedArrival? P i) = some word) ∧
      (e = R.length ∨
        ∃ (he : e < R.length) (seg : ReferenceCollectionSegmentExtraction.Segment rate),
          ReferenceCollectionSegmentExtraction.segmentAt R e = some seg ∧
          seg.entry = R[e] ∧ seg.context.payload = P ∧
          seg.records ++ seg.remaining = R.drop e ∧
          FollowerCutoffScan.firstCutoff p rate.eta.val P.sigma
            (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
              (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z))) =
            ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + e + 1 ∧
          (∀ r ∈ seg.records, ∃ selected : ReferenceActivePhysicalStep.Selection r.input,
            r.output.preparation.coordinator.selection = some selected ∧
            selected.view.payload = P) ∧
          (∀ (k : Fin R.length), e ≤ k.val →
            ∀ (selected : ReferenceActivePhysicalStep.Selection R[k.val].input),
            R[k.val].output.preparation.coordinator.selection = some selected → selected.view.payload = P →
            ∀ i (logged after : ReferencePrelaunchFollower.State p rate.eta)
              (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
              (raw : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p)))
              (scan : FollowerCutoffScan.ScanResult p.T) (registers : ℕ × ℕ) (lastService : ℕ),
            (R[k.val].output.followers i).downInput = some logged →
            (R[k.val].output.followers i).down = some cut →
            cut.outcome = .accepted logged after raw (P.downRecord i) scan registers lastService →
            ∃ word nextMemory,
              V.mapM (ReferenceFirstCorrectedAssignedArrivalPrefix.attributedArrival? P i) = some word ∧
              after.status = .unoccupied ∧ after.lastDown = some (P.downRecord i) ∧
              after.S = (QueueReplay.replay (4 * rate.n) (0, (P.downRecord i).val.q) word).1 ∧
              after.delta = (QueueReplay.replay (4 * rate.n) (0, (P.downRecord i).val.q) word).1 -
                (QueueReplay.replay (4 * rate.n) (0, (P.downRecord i).val.q) (word.take (V.length - 1))).1 ∧
              after.backlog = (QueueReplay.replay (4 * rate.n) (0, (P.downRecord i).val.q) word).2 ∧
              R[k.val].output.next.followers i = .ordinary after nextMemory) ∧
          (∀ r ∈ seg.records, (ReferenceCollectionSegmentExtraction.extractRound r).isSome = true ∧
            (∀ i (state : ReferencePrelaunchFollower.State p rate.eta)
                (memory : ActiveFollowerLifecycle.LocalMemory p)
                (offered : OrdinaryMessageCodec.UpRecord
                  (ReferencePrelaunchFollower.codecParams p rate.eta)),
              (ReferenceFollowerFixedReply.actualChoice r i).configuration =
                  .ordinary state memory →
              ReferenceActivePhysicalStep.upSenderIndex r.input = i →
              ActiveFollowerQueueOperation.checkedUpOffer rate.eta
                (ReferenceFollowerFixedReply.actualChoice r i).follower
                (ReferenceFollowerFixedReply.actualChoice r i).row
                (ReferenceFollowerFixedReply.actualChoice r i).activation
                (ReferenceFollowerFixedReply.actualChoice r i).time state = .offer offered →
              ReferenceFollowerFixedReply.actualUpExpected r =
                some ((OrdinaryMessageCodec.wordEquivFlat
                  (CoordinatorCollectionLedger.codecParams p rate.eta.val))
                    (OrdinaryMessageCodec.encodeUp
                      (CoordinatorCollectionLedger.codecParams p rate.eta.val) offered)) ∧
              offered.val.sigma = ReferencePrelaunchFollower.acceptedStart state ∧
              offered.val.S = state.S ∧ offered.val.delta = state.delta ∧
              offered.val.q = state.backlog) ∧
            (∀ k : Fin R.length, R[k.val] ∈ seg.records →
              ∀ i (state : ReferencePrelaunchFollower.State p rate.eta)
                (memory : ActiveFollowerLifecycle.LocalMemory p),
              (ReferenceFollowerFixedReply.actualChoice R[k.val] i).configuration = .ordinary state memory →
              state.status = .unoccupied →
              ReferencePrelaunchFollower.acceptedStart state = P.sigma.val + 1 →
              ∃ a : Fin R.length,
                b ≤ a.val ∧ a.val < k.val ∧
                ReferenceAcceptedUpFollowerHistory.RetainedDown
                  R[a.val] i (P.downRecord i) ∧
                ∃ word, V.mapM (ReferenceFirstCorrectedAssignedArrivalPrefix.attributedArrival? P i) =
                  some word ∧
                  state.S = (QueueReplay.replay (4 * rate.n) (0, (P.downRecord i).val.q) word).1 ∧
                  state.delta =
                    (QueueReplay.replay (4 * rate.n) (0, (P.downRecord i).val.q) word).1 -
                    (QueueReplay.replay (4 * rate.n) (0, (P.downRecord i).val.q)
                      (word.take (V.length - 1))).1 ∧
                  state.backlog = (QueueReplay.replay (4 * rate.n) (0, (P.downRecord i).val.q) word).2 ∧
                (∃ n : Fin R.length, e ≤ n.val ∧ n.val ≤ k.val ∧
            (n.val = e ∨ ∃ a0 : Fin R.length, e ≤ a0.val ∧ a0.val < k.val ∧
              ReferenceAcceptedUpFollowerHistory.RetainedDown R[a0.val] i (P.downRecord i) ∧ n.val = a0.val + 1) ∧
            ∃ terminal terminalMemory,
              (ReferenceFollowerFixedReply.actualChoice R[n.val] i).configuration = .ordinary terminal terminalMemory ∧
              terminal.status = .unoccupied ∧ terminal.lastDown = some (P.downRecord i) ∧
              ReferenceFollowerReplyChronology.reply state = ReferenceFollowerReplyChronology.reply terminal ∧
              (∀ j : Fin R.length, n.val ≤ j.val → j.val < k.val → ∀ sigma,
                ¬ ReferenceFollowerReplyChronology.appliedDown R[j.val] i sigma) ∧
              (∀ j : Fin R.length, n.val ≤ j.val → j.val ≤ k.val →
                ∃ s m, (ReferenceFollowerFixedReply.actualChoice R[j.val] i).configuration = .ordinary s m ∧
                  s.status = .unoccupied ∧
                  ReferenceFollowerReplyChronology.reply s = ReferenceFollowerReplyChronology.reply terminal)) ∧
                (∀ sigma, ¬ ReferenceFollowerReplyChronology.appliedDown R[k.val] i sigma) ∧
                ∃ next nextMemory,
                  R[k.val].output.next.followers i = .ordinary next nextMemory ∧
                  next.status = .unoccupied ∧
                  ReferenceFollowerReplyChronology.reply next = ReferenceFollowerReplyChronology.reply state ∧
                  ∀ (hsucc : k.val + 1 < R.length),
                    let F := (R.drop (k.val + 1)).takeWhile
                      fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input
                    (∀ n, n < F.length → ∀ (hn : k.val + 1 + n < R.length) sigma,
                      ¬ ReferenceFollowerReplyChronology.appliedDown R[k.val + 1 + n] i sigma) ∧
                    (∀ n, n ≤ F.length → ∀ (hn : k.val + 1 + n < R.length),
                      (n = F.length →
                        ReferenceCollectionPhaseHistory.laterChosen R[k.val + 1 + n].input = true) ∧
                      ((ReferenceFollowerFixedReply.actualChoice R[k.val + 1 + n] i).configuration = .dagger ∨
                        ∃ s m,
                          (ReferenceFollowerFixedReply.actualChoice R[k.val + 1 + n] i).configuration = .ordinary s m ∧
                          s.status = .unoccupied ∧
                          ReferenceFollowerReplyChronology.reply s = ReferenceFollowerReplyChronology.reply next))) ∧
            (∀ d : ReferenceActivePhysicalStep.UpDiagnostic p rate,
              r.output.coordinator.up = some d →
              d.decoderAfter = (CoordinatorUpReception.decoderTransition d.input).1 ∧
              d.raw = (CoordinatorUpReception.decoderTransition d.input).2 ∧
              d.parsed = ReferenceUpReception.rawParsedOutput rate d.input ∧
              d.locallyAccepted = ReferenceUpReception.rawParsedLocalAcceptance rate d.input ∧
              d.rawMatches = decide ((CoordinatorUpReception.decoderTransition d.input).2 =
                ReferenceActivePhysicalStep.upExpected
                  (ReferenceActivePhysicalStep.prepare r.input)) ∧
              d.expected = ReferenceFollowerFixedReply.actualUpExpected r ∧
              (d.wrongUniqueAccepted = true ↔ ∃ word parsed,
                d.raw = some word ∧
                CoordinatorUpReception.parseDecoderOutput (p := p) (eta := rate.eta.val)
                  (some word) = some parsed ∧
                CoordinatorCollectionLedger.acceptUpCheck d.input.ledger d.input.selectedFollower parsed = true ∧
                some word ≠ d.expected) ∧
              (∀ i (state : ReferencePrelaunchFollower.State p rate.eta)
                  (memory : ActiveFollowerLifecycle.LocalMemory p)
                  (offered : OrdinaryMessageCodec.UpRecord
                    (ReferencePrelaunchFollower.codecParams p rate.eta)),
                (ReferenceFollowerFixedReply.actualChoice r i).configuration = .ordinary state memory →
                ReferenceActivePhysicalStep.upSenderIndex r.input = i →
                ActiveFollowerQueueOperation.checkedUpOffer rate.eta
                  (ReferenceFollowerFixedReply.actualChoice r i).follower
                  (ReferenceFollowerFixedReply.actualChoice r i).row
                  (ReferenceFollowerFixedReply.actualChoice r i).activation
                  (ReferenceFollowerFixedReply.actualChoice r i).time state = .offer offered →
                let encoded := (OrdinaryMessageCodec.wordEquivFlat
                  (CoordinatorCollectionLedger.codecParams p rate.eta.val))
                    (OrdinaryMessageCodec.encodeUp
                      (CoordinatorCollectionLedger.codecParams p rate.eta.val) offered)
                d.expected = some encoded ∧
                (d.raw = some encoded → d.parsed = some offered ∧ d.rawMatches = true ∧
                  CoordinatorUpReception.parseDecoderOutput
                    (ReferenceUpReception.filterRawByExpected d.raw d.expected) = some offered)) ∧
              ∃ ledger, ReferenceCoordinatorUpPhysicalCall.siteLedger? (x := r.input) = some ledger ∧
                d.input.ledger = ledger ∧
                d.input.upDecoderBank = r.input.state.upDecoderBank ∧
                d.input.time = r.input.time ∧
                d.input.ownObservation =
                  (ReferenceActivePhysicalStep.prepare r.input).feedback.feedback
                    (ActiveRoundActions.coordinator p.two_le_m) ∧
                d.input.selectedFollower =
                  CoordinatorUpMeasurability.selectedFollowerIndex
                    ((r.input.rows r.input.selected).2 r.input.time) ∧
                d.input.affineSample =
                  ((r.input.rows r.input.selected).2 r.input.time).2
                    (1, CoordinatorUpMeasurability.selectedChannelFollower
                      ((r.input.rows r.input.selected).2 r.input.time)) ∧
                d.input.slot = PublicDiscreteDraws.slotDraw
                  ((r.input.rows r.input.selected).2 r.input.time).1 ∧
                (CoordinatorUpReception.roundInput d.input).receiverEnabled = true ∧
                (CoordinatorUpReception.roundInput d.input).selected = decide
                  (ledger.cutoff ≤ r.input.time.val + 1 ∧
                    d.input.slot = PublicDiscreteDraws.upSlot ∧
                    d.input.selectedFollower ∈ ledger.pending) ∧
                (CoordinatorUpReception.roundInput d.input).sample = d.input.affineSample ∧
                (CoordinatorUpReception.roundInput d.input).roundedReward =
                  CoordinatorUpReception.roundedObservationValue p
                    ((ReferenceActivePhysicalStep.prepare r.input).feedback.feedback
                      (ActiveRoundActions.coordinator p.two_le_m)) ∧
                (ReferenceActivePhysicalStep.prepare r.input).feedback.feedback
                    (ActiveRoundActions.coordinator p.two_le_m) =
                  if FiniteBanditModel.collisionFreeFor
                      (ReferenceActivePhysicalStep.prepare r.input).arms.actions
                        (ActiveRoundActions.coordinator p.two_le_m) then
                    r.input.rewards r.input.time
                      ((ReferenceActivePhysicalStep.prepare r.input).arms.actions
                        (ActiveRoundActions.coordinator p.two_le_m))
                  else 0)) ∧
          (∀ r, seg.remaining.head? = some r →
            ReferenceAssignmentPayloadPersistence.storedPayload r.input.state.coordinator = some P →
            ∀ d : ReferenceActivePhysicalStep.UpDiagnostic p rate,
              r.output.coordinator.up = some d →
              d.decoderAfter = (CoordinatorUpReception.decoderTransition d.input).1 ∧
              d.raw = (CoordinatorUpReception.decoderTransition d.input).2 ∧
              d.parsed = ReferenceUpReception.rawParsedOutput rate d.input ∧
              d.locallyAccepted = ReferenceUpReception.rawParsedLocalAcceptance rate d.input ∧
              d.rawMatches = decide ((CoordinatorUpReception.decoderTransition d.input).2 =
                ReferenceActivePhysicalStep.upExpected
                  (ReferenceActivePhysicalStep.prepare r.input)) ∧
              d.expected = ReferenceFollowerFixedReply.actualUpExpected r ∧
              (d.wrongUniqueAccepted = true ↔ ∃ word parsed,
                d.raw = some word ∧
                CoordinatorUpReception.parseDecoderOutput (p := p) (eta := rate.eta.val)
                  (some word) = some parsed ∧
                CoordinatorCollectionLedger.acceptUpCheck d.input.ledger d.input.selectedFollower parsed = true ∧
                some word ≠ d.expected) ∧
              (∀ (k : Fin R.length), R[k.val] = r →
                ∀ (selected : ReferenceActivePhysicalStep.Selection R[k.val].input),
                R[k.val].output.preparation.coordinator.selection = some selected →
                selected.view.payload = P →
                ∀ i (state : ReferencePrelaunchFollower.State p rate.eta)
                  (memory : ActiveFollowerLifecycle.LocalMemory p)
                  (offered : OrdinaryMessageCodec.UpRecord (ReferencePrelaunchFollower.codecParams p rate.eta)),
                (ReferenceFollowerFixedReply.actualChoice R[k.val] i).configuration = .ordinary state memory →
                ReferenceActivePhysicalStep.upSenderIndex R[k.val].input = i →
                ActiveFollowerQueueOperation.checkedUpOffer rate.eta
                  (ReferenceFollowerFixedReply.actualChoice R[k.val] i).follower
                  (ReferenceFollowerFixedReply.actualChoice R[k.val] i).row
                  (ReferenceFollowerFixedReply.actualChoice R[k.val] i).activation
                  (ReferenceFollowerFixedReply.actualChoice R[k.val] i).time state = .offer offered →
                offered.val.sigma = P.sigma.val + 1 →
                ∃ word, V.mapM (ReferenceFirstCorrectedAssignedArrivalPrefix.attributedArrival? P i) = some word ∧
                  offered.val.S = (QueueReplay.replay (4 * rate.n) (0, (P.downRecord i).val.q) word).1 ∧
                  offered.val.delta =
                    (QueueReplay.replay (4 * rate.n) (0, (P.downRecord i).val.q) word).1 -
                    (QueueReplay.replay (4 * rate.n) (0, (P.downRecord i).val.q) (word.take (V.length - 1))).1 ∧
                  offered.val.q = (QueueReplay.replay (4 * rate.n) (0, (P.downRecord i).val.q) word).2 ∧
                  d.expected = some ((OrdinaryMessageCodec.wordEquivFlat
                    (CoordinatorCollectionLedger.codecParams p rate.eta.val))
                    (OrdinaryMessageCodec.encodeUp (CoordinatorCollectionLedger.codecParams p rate.eta.val) offered)) ∧
                  (d.raw = d.expected → d.parsed = some offered ∧
                    CoordinatorUpReception.parseDecoderOutput
                      (ReferenceUpReception.filterRawByExpected d.raw d.expected) = some offered)) ∧
              ∃ ledger, ReferenceCoordinatorUpPhysicalCall.siteLedger? (x := r.input) = some ledger ∧
                d.input.ledger = ledger ∧
                d.input.upDecoderBank = r.input.state.upDecoderBank ∧
                d.input.time = r.input.time ∧
                d.input.ownObservation =
                  (ReferenceActivePhysicalStep.prepare r.input).feedback.feedback
                    (ActiveRoundActions.coordinator p.two_le_m) ∧
                d.input.selectedFollower =
                  CoordinatorUpMeasurability.selectedFollowerIndex
                    ((r.input.rows r.input.selected).2 r.input.time) ∧
                d.input.affineSample =
                  ((r.input.rows r.input.selected).2 r.input.time).2
                    (1, CoordinatorUpMeasurability.selectedChannelFollower
                      ((r.input.rows r.input.selected).2 r.input.time)) ∧
                d.input.slot = PublicDiscreteDraws.slotDraw
                  ((r.input.rows r.input.selected).2 r.input.time).1 ∧
                (CoordinatorUpReception.roundInput d.input).receiverEnabled = true ∧
                (CoordinatorUpReception.roundInput d.input).selected = decide
                  (ledger.cutoff ≤ r.input.time.val + 1 ∧
                    d.input.slot = PublicDiscreteDraws.upSlot ∧
                    d.input.selectedFollower ∈ ledger.pending) ∧
                (CoordinatorUpReception.roundInput d.input).sample = d.input.affineSample ∧
                (CoordinatorUpReception.roundInput d.input).roundedReward =
                  CoordinatorUpReception.roundedObservationValue p
                    ((ReferenceActivePhysicalStep.prepare r.input).feedback.feedback
                      (ActiveRoundActions.coordinator p.two_le_m)) ∧
                (ReferenceActivePhysicalStep.prepare r.input).feedback.feedback
                    (ActiveRoundActions.coordinator p.two_le_m) =
                  if FiniteBanditModel.collisionFreeFor
                      (ReferenceActivePhysicalStep.prepare r.input).arms.actions
                        (ActiveRoundActions.coordinator p.two_le_m) then
                    r.input.rewards r.input.time
                      ((ReferenceActivePhysicalStep.prepare r.input).arms.actions
                        (ActiveRoundActions.coordinator p.two_le_m))
                  else 0)) := by
  classical
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let b := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.birthIndex
    rate rewards C_star C_h z
  let W := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.liveTail
    rate rewards C_star C_h z
  let V := (R.drop b).take (1 + W.length)
  let e := b + (1 + W.length)
  obtain ⟨L, c, birth, P, base, hL, hc, hprefix, hlen, hb, hborn, hSigma,
      hqueues, hbase, hshape, hbound, hterminal, hstorage⟩ :=
    ReferenceFirstCorrectedAssignedNativeFollowerPrefix.actual_first_corrected_native_follower_storage
      rate rewards C_star C_h u t z hz
  have htail :
      ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
          rate rewards C_star C_h z
          (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.birthIndex rate rewards C_star C_h z + 1) =
        ReferenceFirstCollectionCorrectedSliceNumericalPrefix.liveTail rate rewards C_star C_h z := by
    dsimp only [ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix,
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.liveTail,
      ReferenceFirstReplacementLiveFollowerPrefix.continuingTail,
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords]
    have htest : ReferenceCompleteLaterLiveComplementPrefixReplay.continuingTest
          (p := p) (rate := rate) =
        ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen := by
      funext r
      unfold ReferenceCompleteLaterLiveComplementPrefixReplay.continuingTest
        ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen
      cases r.output.preparation.coordinator with
      | live rv qv base chosen => cases chosen <;> rfl
      | first _ | collection _ _ _ _ _ | invalidCollectionCutoff | dagger => rfl
    rw [htest]
  obtain ⟨LD, cD, birthD, PD, hLD, hcD, _hinputsD, _hlenD, hbD, hbornD,
      _hSigmaD, _hqueuesD, _hdownQueuesD, hVD, hboundD, hwordsD, hcollectionD,
      hdiagnosticsD⟩ :=
    ReferenceFirstCorrectedNativeDownCalendarReplay.firstCell_native_down_calendar_replay
      rate rewards C_star C_h u t z hz
  have hLEq : LD = L := Option.some.inj (hLD.symm.trans hL)
  have hcEq : cD = c := Option.some.inj (hcD.symm.trans hc)
  have hbirthEq : birthD = birth := Option.some.inj (hbD.symm.trans hb)
  subst LD cD birthD
  have hPEq : PD = P :=
    ReferenceAssignmentPayloadChronology.installationBirth_payload_unique birth PD P hbornD hborn
  subst PD
  simp only [htail] at hVD hcollectionD hwordsD hdiagnosticsD
  obtain ⟨birthC, PC, hbC, hbornC, _hVC, hcarry⟩ :=
    ReferenceFirstCorrectedAssignedNativeFollowerPrefix.actual_first_corrected_first_cutoff_carry
      rate rewards C_star C_h u t z hz
  have hbirthCEq : birthC = birth := Option.some.inj (hbC.symm.trans hb)
  subst birthC
  have hPCEq : PC = P :=
    ReferenceAssignmentPayloadChronology.installationBirth_payload_unique birth PC P hbornC hborn
  subst PC
  have hcarry' := hcarry
  simp only [Nat.add_assoc] at hcarry'
  refine ⟨L, c, birth, P, base, hL, hc, hprefix, hlen, hb, hborn, hSigma,
    hqueues, hbase, hshape, hbound, hterminal, hstorage, hcarry', hwordsD, ?_⟩
  rcases hcollectionD with hend | ⟨he, seg, hseg, hentry, hpayload, hpartition, hcutoff, hselected⟩
  · exact Or.inl hend
  · have hsegment_eq :=
      (ReferenceCollectionSegmentExtraction.segmentAt_branch R e seg hseg).1
    have hallcomplete :=
      ReferenceCollectionSegmentExtraction.segment_all_completed (R.drop e) seg hsegment_eq
    have hcurrentFields := current_choice_endpoint_fields rate rewards C_star C_h u t z hz
      birth P hb hborn he hcutoff
    have hVlen : V.length = 1 + W.length := by
      change ((R.drop b).take (1 + W.length)).length = _
      rw [List.length_take, List.length_drop, Nat.min_eq_left]
      change b + (1 + W.length) ≤ R.length at hbound
      omega
    refine Or.inr ⟨he, seg, hseg, hentry, hpayload, hpartition, hcutoff, hselected, ?_, ?_, ?_⟩
    · intro k hek selected hs hp i logged after cut raw scan registers lastService hlogged hdown houtcome
      have hbk : b ≤ k.val := (Nat.le_add_right b (1 + W.length)).trans hek
      have hdiag := (hdiagnosticsD k hbk i).2.2 selected hs
      rw [ite_eq_left hp] at hdiag
      obtain ⟨_, _, word, hword, _hM, _hscan, _hvpos, _hvN, hlate, _hseed, _hno,
        _hrecovery, _hchecked, hreplay, _hprefix, _hservice, hdelta,
        hlastDown, hS, hdel, hq, nextMemory, hnext⟩ :=
        hdiag logged logged after cut raw (P.downRecord i) scan registers lastService hlogged hdown houtcome
      obtain ⟨hscanU, hv⟩ := hlate hek
      change scan.endpoint - (P.sigma.val + 1) = 1 + W.length at hv
      change (V.take (scan.endpoint - (P.sigma.val + 1))).mapM
        (ReferenceFirstCorrectedAssignedArrivalPrefix.attributedArrival? P i) = some word at hword
      rw [hv, ← hVlen, List.take_length] at hword
      have hstatus := (ReferenceCompleteFollowerContinuationKernel.accepted_down_successor_token
        (rate := rate) rewards C_star C_h z k i logged after cut raw (P.downRecord i)
        scan registers lastService hlogged hdown houtcome).1
      have hdate := ReferenceAssignmentFollowerMassSteps.complete_record_time rate rewards C_star C_h z k
      have hunoccupied : after.status = .unoccupied := by
        rw [hstatus, hscanU, hcutoff, hdate, ite_eq_right]
        omega
      refine ⟨word, nextMemory, hword, hunoccupied, hlastDown,
        hS.trans (congrArg Prod.fst hreplay), ?_, hq.trans (congrArg Prod.snd hreplay), hnext⟩
      have hindex : scan.endpoint - (P.sigma.val + 1) - 1 = V.length - 1 :=
        congrArg (fun v : ℕ => v - 1) (hv.trans hVlen.symm)
      simpa only [hindex] using hdel.trans hdelta

    · intro r hr
      have hcomplete := hallcomplete r hr
      refine ⟨hcomplete, ?_, ?_, ?_⟩
      · intro i state memory offered hconfiguration hselectedSender hoff
        have hword := ReferenceFollowerFixedReply.actualUpExpected_eq_encoded_offer
          r i hselectedSender state memory hconfiguration offered hoff
        have halign := ReferenceFollowerFixedReply.actualChoice_alignment r i
        have hfields := ReferenceUpReception.checkedPreparedOffer_field_equations
          rate r.input.row i r.input.time (ReferenceFollowerFixedReply.actualChoice r i)
          halign.1 halign.2.1 halign.2.2 state memory hconfiguration offered hoff
        exact ⟨hword, hfields.1, hfields.2.1, hfields.2.2.1, hfields.2.2.2⟩
      · intro k hk i state memory hconfiguration hu hstart
        have hmemDrop : R[k.val] ∈ R.drop e := by
          rw [← hpartition]
          exact List.mem_append_left _ hk
        have hek := complete_mem_drop_index rate rewards C_star C_h z e k hmemDrop
        obtain ⟨selected, hs, hp⟩ := hselected R[k.val] hk
        exact current_choice_future rate rewards C_star C_h u t z hz birth P hb hborn he hcutoff
          k hek selected hs hp (hallcomplete R[k.val] hk)
          i state memory hconfiguration hu hstart
      · intro d hd
        obtain ⟨_, _, _, _, hafter, hraw, hparsed, hlocal, hmatch, hexpected, _, _, _, _⟩ :=
          ReferenceGeneratedUpBatchCalendar.record_up_executed_fields r d hd
        have hprep : r.output.preparation = ReferenceActivePhysicalStep.prepare r.input := by
          rw [r.output_eq]
          rfl
        have hexpectedActual : d.expected = ReferenceFollowerFixedReply.actualUpExpected r := by
          simpa [ReferenceGeneratedAffineHashHalf.directionSent,
            ReferenceActiveAffinePositiveTest.upSent,
            ReferenceFollowerFixedReply.actualUpExpected, hprep] using hexpected
        have hpreparedExpected : ReferenceFollowerFixedReply.actualUpExpected r =
            ReferenceActivePhysicalStep.upExpected (ReferenceActivePhysicalStep.prepare r.input) := by
          simp [ReferenceFollowerFixedReply.actualUpExpected, hprep]
        have hrawMatchesExpected : d.rawMatches = decide (d.raw = d.expected) := by
          rw [hraw, hexpectedActual, hpreparedExpected]
          exact hmatch
        refine ⟨hafter, hraw, hparsed, hlocal, hmatch, hexpectedActual,
          retained_wrong_unique_iff r d hd, ?_, ?_⟩
        · intro i state memory offered hconfiguration hselectedSender hoff
          have hword := ReferenceFollowerFixedReply.actualUpExpected_eq_encoded_offer
            r i hselectedSender state memory hconfiguration offered hoff
          refine ⟨?_, ?_⟩
          · exact hexpectedActual.trans hword
          · intro hrawCurrent
            have hrawEqExpected : d.raw = d.expected :=
              hrawCurrent.trans (hexpectedActual.trans hword).symm
            obtain ⟨hparsedOffer, heffectiveParse⟩ := raw_current_offer rate d offered
              hraw hparsed (hexpectedActual.trans hword) hrawEqExpected
            have hmatchCurrent : d.rawMatches = true := by
              rw [hrawMatchesExpected]
              have hrawEqExpected : d.raw = d.expected :=
                hrawCurrent.trans (hexpectedActual.trans hword).symm
              rw [hrawEqExpected]
              exact (decide_eq_true_iff).2 rfl
            exact ⟨hparsedOffer, hmatchCurrent, heffectiveParse⟩
        · exact ReferenceCoordinatorUpPhysicalCall.record_retained_up_input_fields r d hd
    · intro r hhead _hstored d hd
      obtain ⟨_, _, _, _, hafter, hraw, hparsed, hlocal, hmatch, hexpected, _, _, _, _⟩ :=
        ReferenceGeneratedUpBatchCalendar.record_up_executed_fields r d hd
      have hprep : r.output.preparation = ReferenceActivePhysicalStep.prepare r.input := by
        rw [r.output_eq]
        rfl
      have hexpectedActual : d.expected = ReferenceFollowerFixedReply.actualUpExpected r := by
        simpa [ReferenceGeneratedAffineHashHalf.directionSent,
          ReferenceActiveAffinePositiveTest.upSent,
          ReferenceFollowerFixedReply.actualUpExpected, hprep] using hexpected
      refine ⟨hafter, hraw, hparsed, hlocal, hmatch, hexpectedActual,
        retained_wrong_unique_iff r d hd, ?_,
        ReferenceCoordinatorUpPhysicalCall.record_retained_up_input_fields r d hd⟩
      intro k hkr selected hs hp i state memory offered hc hsender hoff hcurrent
      have hmem : R[k.val] ∈ R.drop e := by
        rw [← hpartition, hkr]
        exact List.mem_append_right _ (List.mem_of_head? hhead)
      have hek := complete_mem_drop_index rate rewards C_star C_h z e k hmem
      have halign := ReferenceFollowerFixedReply.actualChoice_alignment R[k.val] i
      have hfields := ReferenceUpReception.checkedPreparedOffer_field_equations rate
        R[k.val].input.row i R[k.val].input.time (ReferenceFollowerFixedReply.actualChoice R[k.val] i)
        halign.1 halign.2.1 halign.2.2 state memory hc offered hoff
      obtain ⟨word, hw, hS, hdelta, hq, _hterminalSeed⟩ :=
        hcurrentFields k hek selected hs hp i state memory hc (hfields.1.symm.trans hcurrent)
      have hword := ReferenceFollowerFixedReply.actualUpExpected_eq_encoded_offer
        R[k.val] i hsender state memory hc offered hoff
      have hwordR : ReferenceFollowerFixedReply.actualUpExpected r =
          ReferenceFollowerFixedReply.actualUpExpected R[k.val] :=
        (congrArg ReferenceFollowerFixedReply.actualUpExpected hkr).symm
      have hexpectedWord := hexpectedActual.trans (hwordR.trans hword)
      refine ⟨word, hw, hfields.2.1.trans hS, hfields.2.2.1.trans hdelta,
        hfields.2.2.2.trans hq, hexpectedWord, ?_⟩
      intro hequal
      exact raw_current_offer rate d offered hraw hparsed hexpectedWord hequal



end Bandits.Support.ReferenceFirstCorrectedCurrentCutoffReplyRetention

end
