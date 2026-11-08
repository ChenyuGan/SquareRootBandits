/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstDownZeroRecovery
public import Bandits.Support.ReferenceFirstUpCutoffChronology

/-!
# Actual first accepted-UP sender-local numerical replay

Sources: `sources/zip4/manuscript/06_interruptions.tex:192-233,246-295,301-344`,
`sources/zip4/manuscript/appendix_a_local_protocol.tex:54-60`, and
`sources/zip4/manuscript/04_slow_fast_learner.tex:157-174`.

The queue stream is literally `firstReplyQueueRecords` of the computed physical
run. Recovery initializes it once at the retained DOWN; occupied calendar
rounds advance it, including zero arrivals. The actual interruption choice
retains its last calendar service. These are internal local numerical facts,
without identification with the source queue or a manuscript closure claim.
-/

@[expose] public section

noncomputable section

open Bandits.Support ConstructorDimensions ReferencePrelaunchFollower
open DeclaredFollowerLocalRound ReferenceFollowerFixedReply

namespace Bandits.Support.ReferenceFirstAcceptedUpOnlineReplay

variable {p : ConstructorDimensions.Parameters} {rate : ReferenceActivePhysicalStep.RateInput p}

private theorem actual_finish
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) (i : Fin (p.m - 1))
    (next : ReferencePrelaunchFollower.State p rate.eta) (nextMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hout : record.output.next.followers i = .ordinary next nextMemory) :
    ∃ choice memory post,
      (actualChoice record i).configuration = .ordinary choice memory ∧
      (ReferenceActivePhysicalStep.recordFollower record.output.preparation.coordinator.downView
        (actualChoice record i).follower (actualChoice record i).row
        (actualChoice record i).activation (actualChoice record i).time
        (actualChoice record i).active (actualChoice record i).arm
        (record.output.preparation.feedback.observations
          (PublicDiscreteDraws.followerPlayer p.two_le_m i)) choice).result = .ok post ∧
      DeclaredFollowerLocalRound.releaseAndFinish rate (actualChoice record i).follower (actualChoice record i).row
        (actualChoice record i).time
        (record.output.preparation.feedback.observations
          (PublicDiscreteDraws.followerPlayer p.two_le_m i)) choice memory post =
        .ok (next, nextMemory) ∧
      (record.output.followers i).downInput =
        (ReferenceActivePhysicalStep.recordFollower record.output.preparation.coordinator.downView
          (actualChoice record i).follower (actualChoice record i).row
          (actualChoice record i).activation (actualChoice record i).time
          (actualChoice record i).active (actualChoice record i).arm
          (record.output.preparation.feedback.observations
            (PublicDiscreteDraws.followerPlayer p.two_le_m i)) choice).downInput ∧
      (record.output.followers i).down =
        (ReferenceActivePhysicalStep.recordFollower record.output.preparation.coordinator.downView
          (actualChoice record i).follower (actualChoice record i).row
          (actualChoice record i).activation (actualChoice record i).time
          (actualChoice record i).active (actualChoice record i).arm
          (record.output.preparation.feedback.observations
            (PublicDiscreteDraws.followerPlayer p.two_le_m i)) choice).down := by
  have he := ReferenceFollowerBufferProvenance.roundRecord_follower_eq_finishFollower i record
  have hc : (ReferenceActivePhysicalStep.finishFollower record.output.preparation.coordinator.downView
      (actualChoice record i) (record.output.preparation.feedback.observations
        (PublicDiscreteDraws.followerPlayer p.two_le_m i))).configuration =
      .ordinary next nextMemory := by
    change (ReferenceActivePhysicalStep.finishFollower _
      (record.output.preparation.followers.followers i) _).configuration = _
    rw [← he]
    have hn : record.output.next.followers i =
        (record.output.followers i).configuration := by
      rw [record.output_eq]
      rfl
    exact hn ▸ hout
  obtain ⟨choice, memory, post, hp, hr, hf, hi, hd⟩ :=
    ReferenceFollowerReplyChronology.finishFollower_ordinary_inversion _ _ _ next nextMemory hc
  exact ⟨choice, memory, post, hp, hr, hf, he ▸ hi, he ▸ hd⟩

private theorem actual_start
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1))
    (before choice : ReferencePrelaunchFollower.State p rate.eta)
    (memory choiceMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hi : record.input.state.followers i = .ordinary before memory)
    (hc : (actualChoice record i).configuration = .ordinary choice choiceMemory) :
    ActiveFollowerLifecycle.startRound rate.eta record.input.time before memory =
      .ok (choice, choiceMemory) := by
  have hp : actualChoice record i = DeclaredFollowerLocalRound.prepare rate i
      record.input.row (record.input.state.activations i) record.input.time
      (record.input.active i) (record.input.state.followers i) :=
    record.output.preparation.followers.followers_eq i
  have hc' := hc
  rw [hp] at hc'
  obtain ⟨before', memory', hi', hs, _, _⟩ :=
    ReferenceFollowerReplyChronology.prepare_ordinary_inversion _ _ _ _ _ _ choice choiceMemory hc'
  obtain ⟨he, hm⟩ := LocalConfiguration.ordinary.inj (hi'.symm.trans hi)
  subst before'
  subst memory'
  exact hs

private theorem connected_next
    {initial final : ReferenceActivePhysicalStep.State p rate}
    {records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))}
    (chain : ReferenceActivePhysicalHorizon.Connected initial records final)
    (n : ℕ) (hn : n + 1 < records.length) :
    records[n + 1].input.state = records[n].output.next := by
  have hs := ReferenceFollowerReplyChronology.connected_drop_from_output chain n (by omega)
  have ht := ReferenceFollowerReplyChronology.connected_take_to_input hs 0 (by
    simp only [List.length_drop]; omega)
  simpa only [List.take_zero, ReferenceActivePhysicalHorizon.Connected,
    List.getElem_drop, Nat.add_zero] using ht

private theorem next_choice_reply
    {initial final : ReferenceActivePhysicalStep.State p rate}
    {records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))}
    (chain : ReferenceActivePhysicalHorizon.Connected initial records final)
    (i : Fin (p.m - 1)) (n : ℕ) (hn : n + 1 < records.length)
    (out choice : ReferencePrelaunchFollower.State p rate.eta)
    (outMemory choiceMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hout : records[n].output.next.followers i = .ordinary out outMemory)
    (hc : (actualChoice records[n + 1] i).configuration = .ordinary choice choiceMemory) :
    ReferenceFollowerReplyChronology.reply choice = ReferenceFollowerReplyChronology.reply out := by
  have hi : records[n + 1].input.state.followers i = .ordinary out outMemory := by
    rw [connected_next chain n hn]
    exact hout
  have hs := actual_start records[n + 1] i out choice outMemory choiceMemory hi hc
  have hf := ActiveFollowerLifecycle.startRound_frame rate.eta records[n + 1].input.time
    out choice outMemory choiceMemory hs
  simp only [ReferenceFollowerReplyChronology.reply, hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1]

/-- A real retained acceptance followed by an ordinary output has no second
service at acceptance. Release and finish preserve the accepted triple. -/
private theorem retained_output_reply
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1))
    (message : ReferenceFirstAcceptedUpNumericSnapshot.DownRecord (p := p) (rate := rate))
    (logged after next : ReferencePrelaunchFollower.State p rate.eta)
    (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
    (nextMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hinput : (record.output.followers i).downInput = some logged)
    (hdown : (record.output.followers i).down = some cut)
    (ha : ∃ raw scan registers lastService,
      cut.outcome = .accepted logged after raw message scan registers lastService)
    (hout : record.output.next.followers i = .ordinary next nextMemory) :
    ReferenceFollowerReplyChronology.reply next = ReferenceFollowerReplyChronology.reply after := by
  obtain ⟨raw, scan, registers, lastService, ha⟩ := ha
  obtain ⟨saved, savedMemory, logged', hc, hu, hl, hinput', hcut⟩ :=
    ReferenceFollowerSparseEmissionRecovery.actualDownDiagnostic_choice record i cut hdown
  have heq : logged' = logged := Option.some.inj (hinput'.symm.trans hinput)
  subst logged'
  obtain ⟨choice, memory, post, hc', hr, hf, _, _⟩ := actual_finish record i next nextMemory hout
  obtain ⟨he, hm⟩ := LocalConfiguration.ordinary.inj (hc'.symm.trans hc)
  subst choice
  subst memory
  dsimp only [actualChoice] at hr hf
  have hpost : post = after := by
    simp only [ReferenceActivePhysicalStep.recordFollower, dite_eq_left hu, hl] at hr
    rw [← hcut, ha] at hr
    exact (Except.ok.inj hr).symm
  subst post
  exact (ReferenceFollowerReplyChronology.releaseAndFinish_frame _ _ _ _
    saved after next savedMemory nextMemory hf).1

/-- The literal next calendar cell of the admitted projection. Its index is
past acceptance, so the cell contains the actual own-row recorder arrival. -/
private theorem first_reply_records_succ
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (i : Fin (p.m - 1)) (j n : ℕ)
    (message : ReferenceFirstAcceptedUpNumericSnapshot.DownRecord (p := p) (rate := rate))
    (hn : n < records.length) (hjn : j < n) :
    ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords records i j message (n + 1) =
      ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords records i j message n ++
        [(true, ActiveFollowerQueueOperation.rawArrival rate.eta i records[n].input.row
          records[n].input.time message
          (records[n].output.ownEntries (PublicDiscreteDraws.followerPlayer p.two_le_m i)).2)] := by
  classical
  unfold ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords
  rw [List.take_succ_eq_append_getElem hn, List.zipIdx_append, List.map_append]
  simp only [List.length_take, Nat.min_eq_left (Nat.le_of_lt hn), Nat.zero_add,
    List.zipIdx_cons, List.zipIdx_nil, List.map_cons, List.map_nil,
    ite_eq_right (by omega : ¬ n ≤ j)]

/-- Invert the actual occupied service and its successful release/finish.
The arrival is the SAME row, time, message and own observation used by the
literal projection; successful output is derived from the ordinary output. -/
private theorem occupied_output_equations
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1))
    (message : ReferenceFirstAcceptedUpNumericSnapshot.DownRecord (p := p) (rate := rate))
    (choice next : ReferencePrelaunchFollower.State p rate.eta)
    (memory nextMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hc : (actualChoice record i).configuration = .ordinary choice memory)
    (ho : choice.status ≠ .unoccupied) (hd : choice.lastDown = some message)
    (hout : record.output.next.followers i = .ordinary next nextMemory) :
    (next.S, next.backlog) = QueueReplay.transition (4 * rate.n) (choice.S, choice.backlog)
      (true, ActiveFollowerQueueOperation.rawArrival rate.eta i record.input.row record.input.time
        message (record.output.ownEntries (PublicDiscreteDraws.followerPlayer p.two_le_m i)).2) ∧
      next.delta = next.S - choice.S := by
  classical
  obtain ⟨saved, savedMemory, post, hc', hr, hf, _, _⟩ := actual_finish record i next nextMemory hout
  obtain ⟨he, hm⟩ := LocalConfiguration.ordinary.inj (hc'.symm.trans hc)
  subst saved
  subst savedMemory
  simp only [ReferenceActivePhysicalStep.recordFollower, recordOrServiceThenDown,
    dite_eq_right ho] at hr
  cases hs : ActiveFollowerQueueOperation.checkedService rate.eta rate.sourceCap rate.n rate.n_scale
      (actualChoice record i).follower (actualChoice record i).row
      (actualChoice record i).activation (actualChoice record i).time
      (record.output.preparation.feedback.observations
        (PublicDiscreteDraws.followerPlayer p.two_le_m i)) choice with
  | failure => rw [hs] at hr; cases hr
  | success result =>
    rw [hs] at hr
    have hpost : post = ActiveFollowerQueueOperation.serviceUpdate rate.n choice result.arrival := by
      rw [← Except.ok.inj hr, result.queueUpdate]
      cases hstatus : choice.status with
      | unoccupied => exact (ho hstatus).elim
      | pending => simp only [ActiveFollowerQueueOperation.serviceOutput, hstatus,
          ActiveRoundActions.FollowerStatus.occupied, true_or, ite_true]
      | released => simp only [ActiveFollowerQueueOperation.serviceOutput, hstatus,
          ActiveRoundActions.FollowerStatus.occupied, or_true, ite_true]
    have hraw : result.arrival = ActiveFollowerQueueOperation.rawArrival rate.eta
        (actualChoice record i).follower (actualChoice record i).row (actualChoice record i).time
        message (record.output.preparation.feedback.observations
          (PublicDiscreteDraws.followerPlayer p.two_le_m i)) := by
      have ha := result.action
      cases hstatus : choice.status with
      | unoccupied => exact (ho hstatus).elim
      | pending | released =>
        simp only [ActiveFollowerQueueOperation.serviceAction, hstatus] at ha
        obtain ⟨_, M, hM, _, harrival, _⟩ := ha
        have hM' : M = message := Option.some.inj (hM.symm.trans hd)
        subst M
        exact harrival
    have hown : (record.output.ownEntries (PublicDiscreteDraws.followerPlayer p.two_le_m i)).2 =
        record.output.preparation.feedback.observations (PublicDiscreteDraws.followerPlayer p.two_le_m i) := by
      have he : record.output.ownEntries = record.output.preparation.feedback.ownEntries := by
        rw [record.output_eq]
        rfl
      rw [he, record.output.preparation.feedback.ownEntries_eq]
    have halign := actualChoice_alignment record i
    have hrawActual : result.arrival = ActiveFollowerQueueOperation.rawArrival rate.eta
        i record.input.row record.input.time message
        (record.output.ownEntries (PublicDiscreteDraws.followerPlayer p.two_le_m i)).2 := by
      calc
        result.arrival = _ := hraw
        _ = _ := by rw [halign.1, halign.2.1, halign.2.2, ← hown]
    have hframe := (ReferenceFollowerReplyChronology.releaseAndFinish_frame _ _ _ _
      choice post next memory nextMemory hf).1
    have hS : next.S = post.S := congrArg (fun r => r.2.1) hframe
    have hdelta : next.delta = post.delta := congrArg (fun r => r.2.2.1) hframe
    have hq : next.backlog = post.backlog := congrArg (fun r => r.2.2.2) hframe
    rw [hpost] at hS hdelta hq
    have hp := ActiveFollowerQueueOperation.serviceUpdate_eq_queueTransition rate.n choice result.arrival
    have heq := ActiveFollowerQueueOperation.serviceUpdate_register_equations rate.n choice result.arrival
    refine ⟨?_, ?_⟩
    · rw [hS, hq, hp, hrawActual]
      rfl
    · rw [hS, hdelta, heq.1, heq.2.1]
      omega

/-- First-sigma accepted-UP replay in the original computed run. The same
retained DOWN initializes recovery and every later actual online update.
The index `b` is a genuine post-acceptance choice even for late acceptance. -/
theorem run_first_accepted_up_online_replay
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (span : start + count ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hfirst : initial.coordinator = .first) (i : Fin (p.m - 1))
    (seed : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hseed : initial.followers i = .ordinary seed memory) (hnone : seed.lastDown = none)
    (hunoccupied : seed.status = .unoccupied)
    (hvalid : ActiveFollowerLifecycle.localBufferValid seed)
    (hpair : seed.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound))
    (htime : ∀ saved ∈ seed.buffer, saved.calendarRound ≤ start)
    (k : Fin (ReferenceActivePhysicalHorizon.run initial rows J rewards start count span active).records.length)
    (U : ReferenceCollectionPhaseHistory.UpRecord p rate)
    (haccepted : ReferenceCollectionPhaseHistory.AcceptedUp
      (ReferenceActivePhysicalHorizon.run initial rows J rewards start count span active).records[k.val].input i U)
    (hsigma : U.val.sigma = start + 1) :
    let E := ReferenceActivePhysicalHorizon.run initial rows J rewards start count span active
    ∃ j : Fin E.records.length, j.val < k.val ∧
      ∃ message : ReferenceFirstAcceptedUpNumericSnapshot.DownRecord (p := p) (rate := rate),
        ReferenceAcceptedUpFollowerHistory.RetainedDown E.records[j.val] i message ∧
        message.val.sigma = start + 1 ∧
        let bits := FollowerCutoffScan.completeRowProposalBit p rate.eta.val (rows J)
        let u := FollowerCutoffScan.firstCutoff p rate.eta.val
          (ActiveFollowerDownAcceptance.downStart p rate message) bits
        let m := u - (start + 1)
        let b := max m (j.val + 1)
        let V := fun h => QueueReplay.replay (4 * rate.n) (0, 0)
          (ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords E.records i j.val message h)
        start + 1 < u ∧ u ≤ start + k.val + 1 ∧ 0 < m ∧ m ≤ k.val ∧ b ≤ k.val ∧
        U.val.S = (V m).1 ∧ U.val.q = (V m).2 ∧
        U.val.delta = (V m).1 - (V (m - 1)).1 ∧
        ∃ hb : b < E.records.length, ∃ s mu,
          (actualChoice E.records[b] i).configuration = .ordinary s mu ∧
          s.status = .unoccupied ∧ s.lastDown = some message ∧
          s.S = (V m).1 ∧ s.backlog = (V m).2 ∧
          s.delta = (V m).1 - (V (m - 1)).1 := by
  classical
  let E := ReferenceActivePhysicalHorizon.run initial rows J rewards start count span active
  obtain ⟨j, hjk, message, hretained, hmessage, hu, huk, hmpos, hmk, hbk,
      hchoices, houtputs, _hno, hb, boundary, boundaryMemory, hbc, hbu, hbd,
      hUS, hUq, hUd⟩ :=
    ReferenceFirstUpCutoffChronology.run_first_accepted_up_cutoff_chronology
      initial rows J rewards start count span active hfirst i seed memory hseed hnone
      k U haccepted hsigma
  let bits := FollowerCutoffScan.completeRowProposalBit p rate.eta.val (rows J)
  let u := FollowerCutoffScan.firstCutoff p rate.eta.val
    (ActiveFollowerDownAcceptance.downStart p rate message) bits
  let m := u - (start + 1)
  let b := max m (j.val + 1)
  let V := fun h => QueueReplay.replay (4 * rate.n) (0, 0)
    (ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords E.records i j.val message h)
  change start + 1 < u at hu
  change u ≤ start + k.val + 1 at huk
  change 0 < m at hmpos
  change m ≤ k.val at hmk
  change b ≤ k.val at hbk
  change b < E.records.length at hb
  change (actualChoice E.records[b] i).configuration = .ordinary boundary boundaryMemory at hbc
  obtain ⟨logged, cut, after, raw, scan, registers, lastService, hinput, hdown, ha,
      view, selected, _hview, _hselected, _hviewEq, _hmessageView,
      birth, installed, firstChoice, _hbirth, _hborn, _hbirthTime, _hbirthFirst,
      _hhead, _hdispatch, _hpayload, _hfirstPayload, _hmessageInstalled,
      _hqzero, _hseedNone, _hseedStatus, n0, hn0, hend, _hn0pos, _hn0le,
      _hnoprior, _hrecovery, _hchecked, hregisters, hlastService, _hprefix, hafter⟩ :=
    ReferenceFirstDownZeroRecovery.actual_first_down_zero_seeded_recovery
      initial rows J rewards start count span active hfirst i seed memory hseed hnone
      hunoccupied hvalid hpair htime j message hretained hmessage
  change scan.endpoint = min u (start + j.val + 2) at hend
  have hn0eq : n0 = min m (j.val + 1) := by
    dsimp only [m]
    rw [hn0, hend, hmessage]
    omega
  change registers = V n0 at hregisters
  change lastService = (V n0).1 - (V (n0 - 1)).1 at hlastService
  have hafterPair : (after.S, after.backlog) = V n0 := by
    rw [hafter]
    exact hregisters
  have hafterDelta : after.delta = (V n0).1 - (V (n0 - 1)).1 := by
    rw [hafter]
    exact hlastService
  obtain ⟨out0, outMemory0, _choice0, _choiceMemory0, hout0, _hd0, _hstart0,
      _hstatus0, _hc0, _hread0, _hkeep0, _next0, _hnext0⟩ :=
    houtputs j le_rfl hjk
  have hreply0 := retained_output_reply E.records[j.val] i message logged after
    out0 cut outMemory0 hinput hdown ⟨raw, scan, registers, lastService, ha⟩ hout0
  have hinitPair : (out0.S, out0.backlog) = V n0 := by
    have hS : out0.S = after.S := congrArg (fun r => r.2.1) hreply0
    have hq : out0.backlog = after.backlog := congrArg (fun r => r.2.2.2) hreply0
    rw [hS, hq]
    exact hafterPair
  have hinitDelta : out0.delta = (V n0).1 - (V (n0 - 1)).1 :=
    (congrArg (fun r => r.2.2.1) hreply0).trans hafterDelta
  -- The minimum covers both a live acceptance and recovery already at cutoff.
  -- Only the base choice is needed when j ≥ m; later induction steps have n ≤ m.
  have hnumeric : ∀ (n : ℕ) (hn : n < E.records.length), j.val < n → n ≤ b →
      ∀ (s : ReferencePrelaunchFollower.State p rate.eta)
        (mu : ActiveFollowerLifecycle.LocalMemory p),
        (actualChoice E.records[n] i).configuration = .ordinary s mu →
        (s.S, s.backlog) = V (min m n) ∧
          s.delta = (V (min m n)).1 - (V (min m n - 1)).1 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn hjn hnb s mu hc
      by_cases hbase : n = j.val + 1
      · subst n
        have hreply := next_choice_reply E.connected i j.val hn
          out0 s outMemory0 mu hout0 hc
        have hS : s.S = out0.S := congrArg (fun r => r.2.1) hreply
        have hq : s.backlog = out0.backlog := congrArg (fun r => r.2.2.2) hreply
        have hd : s.delta = out0.delta := congrArg (fun r => r.2.2.1) hreply
        rw [← hn0eq, hS, hq, hd]
        exact ⟨hinitPair, hinitDelta⟩
      · let prev := n - 1
        have hprev : prev < E.records.length := by dsimp only [prev]; omega
        have hjprev : j.val < prev := by dsimp only [prev]; omega
        have hprevn : prev < n := by dsimp only [prev]; omega
        have hnprev : prev + 1 = n := by dsimp only [prev]; omega
        have hnm : n ≤ m := by dsimp only [b] at hnb; omega
        have hprevm : prev < m := by omega
        let index : Fin E.records.length := ⟨prev, hprev⟩
        obtain ⟨choice, choiceMemory, hcc, hcd, _hcs, hcstatus⟩ :=
          hchoices index hjprev (by change prev ≤ k.val; omega)
        have hoccupied : choice.status ≠ .unoccupied := by
          intro he
          have hh := hcstatus.mp he
          change m ≤ prev at hh
          omega
        obtain ⟨hchoicePair, _hchoiceDelta⟩ :=
          ih prev hprevn hprev hjprev (by omega) choice choiceMemory hcc
        rw [Nat.min_eq_right (Nat.le_of_lt hprevm)] at hchoicePair
        obtain ⟨out, outMemory, _choice, _choiceMemory, hout, _hd, _hs,
            _hstatus, _hc, _hread, _hkeep, _next, _hnext⟩ :=
          houtputs index (by change j.val ≤ prev; omega) (by change prev < k.val; omega)
        have hservice := occupied_output_equations E.records[prev] i message
          choice out choiceMemory outMemory hcc hoccupied hcd hout
        have hstep : V (prev + 1) = QueueReplay.transition (4 * rate.n) (V prev)
            (true, ActiveFollowerQueueOperation.rawArrival rate.eta i E.records[prev].input.row
              E.records[prev].input.time message
              (E.records[prev].output.ownEntries (PublicDiscreteDraws.followerPlayer p.two_le_m i)).2) := by
          dsimp only [V]
          rw [first_reply_records_succ E.records i j.val prev message hprev hjprev,
            QueueReplay.replay_append]
          rfl
        have houtPair : (out.S, out.backlog) = V (prev + 1) := by
          rw [hservice.1, hchoicePair, hstep]
        have houtDelta : out.delta = (V (prev + 1)).1 - (V prev).1 := by
          rw [hservice.2, ← hchoicePair, ← houtPair]
        -- PREPARE at cutoff runs before service and frames all reply registers.
        have hreply : ReferenceFollowerReplyChronology.reply s =
            ReferenceFollowerReplyChronology.reply out := by
          have hc' : (actualChoice E.records[prev + 1] i).configuration = .ordinary s mu := by
            simpa only [hnprev] using hc
          exact next_choice_reply E.connected i prev (by omega) out s outMemory mu hout hc'
        have hS : s.S = out.S := congrArg (fun r => r.2.1) hreply
        have hq : s.backlog = out.backlog := congrArg (fun r => r.2.2.2) hreply
        have hd : s.delta = out.delta := congrArg (fun r => r.2.2.1) hreply
        rw [Nat.min_eq_right hnm, hS, hq, hd, ← hnprev]
        have hpred : prev + 1 - 1 = prev := by omega
        rw [hpred]
        exact ⟨houtPair, houtDelta⟩
  have hjb : j.val < b := by dsimp only [b]; omega
  obtain ⟨hboundaryPair, hboundaryDelta⟩ := hnumeric b hb hjb le_rfl boundary boundaryMemory hbc
  rw [Nat.min_eq_left (Nat.le_max_left m (j.val + 1))] at hboundaryPair hboundaryDelta
  have hboundaryS := congrArg Prod.fst hboundaryPair
  have hboundaryq := congrArg Prod.snd hboundaryPair
  refine ⟨j, hjk, message, hretained, hmessage, hu, huk, hmpos, hmk, hbk,
    hUS.trans hboundaryS, hUq.trans hboundaryq, hUd.trans hboundaryDelta,
    hb, boundary, boundaryMemory, hbc, hbu, hbd, hboundaryS, hboundaryq, hboundaryDelta⟩

section ActualLaunch

/-- The same numerical replay at the original conditional launched boundary.
All source, reward, private-array, initialization-relation and handoff inputs
are retained. The launch premises themselves are not established here. -/
theorem ofActualLaunchedBoundary_first_accepted_up_online_replay
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (launchRate : RateInput p) (C_star C_h : ℝ)
    (b : ReferenceInitializationRun.Boundary p)
    (h : b.completed < BootstrapDimensions.n_boot p)
    (actual : ActualInitializationRun.BlockCarry p launchRate
      (ReferenceInitializationRun.nextBlock b h))
    (past : List (ActualInitializationRun.PhysicalRoundRecord p launchRate source rewards))
    (hr : ActualReferenceInitializationBlock.BlockStartRelated source rewards
      C_star C_h launchRate (ReferenceInitializationRun.nextBlock b h) actual b past)
    (hdown : ∀ i, ¬ InitializationFailureProvenance.generatedBlockDown
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h launchRate) b h i)
    (hclean : ∀ (i : Fin (p.m - 1))
      (hi : ActualReferenceInitializationBlock.refFollower i ∈
        (ReferenceInitializationRun.physical
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h launchRate)
          b h).uninformed),
      BootstrapAllCandidateController.cleanPrefix
        (ReferenceInitializationRun.physical
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h launchRate)
          b h)
        source.1.2 ⟨ActualReferenceInitializationBlock.refFollower i, hi⟩
        (ActualInitializationPhysicalStep.selectedRowIndex p source) p.T)
    (hforce : ∀ i, ReferenceInitializationRun.forced
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h launchRate)
      b h i = false)
    (launch : BootstrapCoordinatorLocalRound.LaunchedBlock p)
    (learnerSeed : ActualInitializationRun.CoordinatorLearnerZeroSeed p)
    (hlaunched : (ActualInitializationRun.combinedBoundaryHandoff p launchRate
      (ReferenceInitializationRun.nextBlock b h) source rewards actual.C_star actual.C_h
      (ActualInitializationRun.foldBlock p launchRate (ReferenceInitializationRun.nextBlock b h)
        source rewards actual)).disposition = .launched launch learnerSeed)
    (count : ℕ)
    (span : (BootstrapObservedFollower.blockStop p (ReferenceInitializationRun.nextBlock b h)) + count ≤ p.T)
    (i : Fin (p.m - 1))
    (k : Fin (ReferenceActivePhysicalHorizon.run
      (ActualInitializationLaunchState.ofActualLaunchedBoundary source rewards launchRate
        C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed hlaunched)
      source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
      (BootstrapObservedFollower.blockStop p (ReferenceInitializationRun.nextBlock b h)) count span
      (fun player =>
        ActualInitializationLaunchState.ofActualLaunchedBoundary_activation_le_blockStop
          source rewards launchRate C_star C_h b h actual past hr hdown hclean hforce
          launch learnerSeed hlaunched player)).records.length)
    (U : ReferenceCollectionPhaseHistory.UpRecord p launchRate)
    (haccepted : ReferenceCollectionPhaseHistory.AcceptedUp
      (ReferenceActivePhysicalHorizon.run
      (ActualInitializationLaunchState.ofActualLaunchedBoundary source rewards launchRate
        C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed hlaunched)
      source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
      (BootstrapObservedFollower.blockStop p (ReferenceInitializationRun.nextBlock b h)) count span
      (fun player =>
        ActualInitializationLaunchState.ofActualLaunchedBoundary_activation_le_blockStop
          source rewards launchRate C_star C_h b h actual past hr hdown hclean hforce
          launch learnerSeed hlaunched player)).records[k.val].input i U)
    (hsigma : U.val.sigma = (BootstrapObservedFollower.blockStop p (ReferenceInitializationRun.nextBlock b h)) + 1) :
    let initial := (ActualInitializationLaunchState.ofActualLaunchedBoundary source rewards launchRate
        C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed hlaunched)
    let start := (BootstrapObservedFollower.blockStop p (ReferenceInitializationRun.nextBlock b h))
    let active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start :=
      (fun player =>
        ActualInitializationLaunchState.ofActualLaunchedBoundary_activation_le_blockStop
          source rewards launchRate C_star C_h b h actual past hr hdown hclean hforce
          launch learnerSeed hlaunched player)
    let E := ReferenceActivePhysicalHorizon.run initial source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start count span active
    ∃ j : Fin E.records.length, j.val < k.val ∧
      ∃ message : ReferenceFirstAcceptedUpNumericSnapshot.DownRecord (p := p) (rate := launchRate),
        ReferenceAcceptedUpFollowerHistory.RetainedDown (E.records[j.val]'(j.isLt)) i message ∧
        message.val.sigma = start + 1 ∧
        let bits := FollowerCutoffScan.completeRowProposalBit p launchRate.eta.val
          (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source))
        let u := FollowerCutoffScan.firstCutoff p launchRate.eta.val
          (ActiveFollowerDownAcceptance.downStart p launchRate message) bits
        let m := u - (start + 1)
        let replyIndex := max m (j.val + 1)
        let V := fun n => QueueReplay.replay (4 * launchRate.n) (0, 0)
          (ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords E.records i j.val message n)
        start + 1 < u ∧ u ≤ start + k.val + 1 ∧ 0 < m ∧ m ≤ k.val ∧ replyIndex ≤ k.val ∧
        U.val.S = (V m).1 ∧ U.val.q = (V m).2 ∧
        U.val.delta = (V m).1 - (V (m - 1)).1 ∧
        ∃ hb : replyIndex < E.records.length, ∃ s mu,
          (actualChoice (E.records[replyIndex]'(hb)) i).configuration = .ordinary s mu ∧
          s.status = .unoccupied ∧ s.lastDown = some message ∧
          s.S = (V m).1 ∧ s.backlog = (V m).2 ∧
          s.delta = (V m).1 - (V (m - 1)).1 := by
  dsimp only
  obtain ⟨hfirst, hactive, seed, memory, hseed, _hS, _hdelta, _hq, hnone,
      hstatus, hvalid, hpair, htime⟩ :=
    ReferenceFirstAcceptedUpNumericSnapshot.actual_launched_follower_local_invariants
      source rewards launchRate C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed hlaunched i
  exact run_first_accepted_up_online_replay
    (ActualInitializationLaunchState.ofActualLaunchedBoundary source rewards launchRate
      C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed hlaunched)
    source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
    (BootstrapObservedFollower.blockStop p (ReferenceInitializationRun.nextBlock b h)) count span
    hactive hfirst i seed memory hseed hnone hstatus hvalid hpair htime k U haccepted hsigma

end ActualLaunch

end Bandits.Support.ReferenceFirstAcceptedUpOnlineReplay

end
