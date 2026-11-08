/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionOfferedSenderReplay

/-!
# Actual retained DOWN reply at the first cutoff

Sources: `sources/zip4/manuscript/05_binary_transport.tex:70-88,105-124`,
`sources/zip4/manuscript/06_interruptions.tex:9-70,192-209,246-284,327-348`,
and `sources/zip4/manuscript/appendix_a_local_protocol.tex:151-157`.

This producer follows one actual first-collection run from its source launch
through the first cutoff. A retained DOWN from any earlier record, including
the immediately preceding record, determines the incoming interrupted reply.
The result preserves the actual payload, state, memory, output alternatives,
and original source row.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferencePrelaunchFollower
open Bandits.Support.ReferenceFollowerFixedReply
open Bandits.Support.DeclaredFollowerLocalRound

namespace Bandits.Support.ReferenceFirstCutoffRetainedDownReplySeed

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

abbrev Record := ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)
abbrev DownRecord := ReferenceAcceptedUpFollowerHistory.DownRecord (p := p) (rate := rate)

private theorem record_lastDown_origin
    (record : Record (p := p) (rate := rate)) (i : Fin (p.m - 1))
    (next : ReferencePrelaunchFollower.State p rate.eta)
    (nextMemory : ActiveFollowerLifecycle.LocalMemory p)
    (target : DownRecord (p := p) (rate := rate))
    (hout : record.output.next.followers i = .ordinary next nextMemory)
    (hlast : next.lastDown = some target) :
    (∃ before beforeMemory,
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
    sender.follower sender.row sender.time observation choice post next choiceMemory nextMemory hfinish
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

private theorem connected_lastDown_origin
    {initial final : ReferenceActivePhysicalStep.State p rate}
    {records : List (Record (p := p) (rate := rate))}
    (chain : ReferenceActivePhysicalHorizon.Connected initial records final)
    (i : Fin (p.m - 1))
    (first : ReferencePrelaunchFollower.State p rate.eta)
    (firstMemory : ActiveFollowerLifecycle.LocalMemory p)
    (last : ReferencePrelaunchFollower.State p rate.eta)
    (lastMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hfirst : initial.followers i = .ordinary first firstMemory)
    (hlast : final.followers i = .ordinary last lastMemory)
    (target : DownRecord (p := p) (rate := rate))
    (hdown : last.lastDown = some target) :
    first.lastDown = some target ∨
      ∃ record ∈ records,
        ReferenceAcceptedUpFollowerHistory.RetainedDown record i target := by
  induction records generalizing initial first firstMemory final last lastMemory with
  | nil =>
      change final = initial at chain
      subst final
      have hstates := LocalConfiguration.ordinary.inj (hfirst.symm.trans hlast)
      rcases hstates with ⟨rfl, rfl⟩
      exact Or.inl hdown
  | cons record rest ih =>
      rcases chain with ⟨hpre, hrest⟩
      obtain ⟨middle, middleMemory, hmiddle, _, _, _⟩ :=
        ReferenceFollowerReplyChronology.connected_ordinary_chronology
          hrest i last lastMemory hlast
      have hrecordInput : record.input.state.followers i = .ordinary first firstMemory := by
        rw [hpre]
        exact hfirst
      rcases ih hrest middle middleMemory last lastMemory hmiddle hlast hdown with
        hmiddleDown | ⟨laterRecord, hlaterRecord, hlaterDown⟩
      · rcases record_lastDown_origin record i middle middleMemory target hmiddle hmiddleDown with
          ⟨before, beforeMemory, hbefore, hbeforeDown⟩ | hcurrentDown
        · have hstates := LocalConfiguration.ordinary.inj (hbefore.symm.trans hrecordInput)
          rcases hstates with ⟨rfl, rfl⟩
          exact Or.inl hbeforeDown
        · exact Or.inr ⟨record, List.mem_cons_self, hcurrentDown⟩
      · exact Or.inr ⟨laterRecord, List.mem_cons_of_mem _ hlaterRecord, hlaterDown⟩

private theorem priorDown_payload_of_index
    {records W : List (Record (p := p) (rate := rate))}
    {s w : ℕ} {B : List (ReferenceCollectionPhaseHistory.Record (p := p) (rate := rate))}
    {cut : Record (p := p) (rate := rate)} {suffix : List (Record (p := p) (rate := rate))}
    {P0 : ReferenceActivePhysicalStep.Payload rate}
    (_hsplit : records = W ++ cut :: suffix) (hindex : w < records.length)
    (hw : w = W.length) (hB : 0 < B.length)
    (hprior : ∀ (k : Fin B.length) (j : ℕ), j < w + k.val →
      ∀ (record : Record (p := p) (rate := rate)), records[j]? = some record →
      ∀ (i : Fin (p.m - 1)) (M : DownRecord (p := p) (rate := rate)),
        ReferenceAcceptedUpFollowerHistory.RetainedDown record i M →
          M = P0.downRecord i ∧ M.val.sigma = s + 1 ∧ M.val.q = 0)
    (j : ℕ) (hj : j < w)
    (i : Fin (p.m - 1)) (M : DownRecord (p := p) (rate := rate))
    (hretained : ReferenceAcceptedUpFollowerHistory.RetainedDown records[j] i M) :
    M = P0.downRecord i ∧ M.val.sigma = s + 1 ∧ M.val.q = 0 := by
  let k : Fin B.length := ⟨0, hB⟩
  have hget : records[j]? = some records[j] := List.getElem?_eq_getElem (by omega)
  exact hprior k j (by simp only [k]; omega) records[j] hget i M hretained

private theorem priorDown_payload_of_mem
    {records W : List (Record (p := p) (rate := rate))}
    {s w : ℕ} {B : List (ReferenceCollectionPhaseHistory.Record (p := p) (rate := rate))}
    {cut : Record (p := p) (rate := rate)} {suffix : List (Record (p := p) (rate := rate))}
    {P0 : ReferenceActivePhysicalStep.Payload rate}
    (hsplit : records = W ++ cut :: suffix) (hindex : w < records.length)
    (hw : w = W.length) (hB : 0 < B.length)
    (hprior : ∀ (k : Fin B.length) (j : ℕ), j < w + k.val →
      ∀ (record : Record (p := p) (rate := rate)), records[j]? = some record →
      ∀ (i : Fin (p.m - 1)) (M : DownRecord (p := p) (rate := rate)),
        ReferenceAcceptedUpFollowerHistory.RetainedDown record i M →
          M = P0.downRecord i ∧ M.val.sigma = s + 1 ∧ M.val.q = 0)
    {record : Record (p := p) (rate := rate)} (hmem : record ∈ W)
    (i : Fin (p.m - 1)) (M : DownRecord (p := p) (rate := rate))
    (hretained : ReferenceAcceptedUpFollowerHistory.RetainedDown record i M) :
    M = P0.downRecord i ∧ M.val.sigma = s + 1 ∧ M.val.q = 0 := by
  obtain ⟨j, hj, hrecord⟩ :=
    (List.exists_mem_iff_getElem (l := W) (p := fun x => x = record)).mp
      ⟨record, hmem, rfl⟩
  have hrecordAt : records[j]? = some record := by
    rw [hsplit]
    rw [List.getElem?_append_left (by omega : j < W.length)]
    rw [List.getElem?_eq_getElem hj, hrecord]
  have hrecordEq : records[j] = record := by
    rw [List.getElem?_eq_getElem (by omega)] at hrecordAt
    exact Option.some.inj hrecordAt
  exact priorDown_payload_of_index hsplit hindex hw hB hprior j (by omega) i M
    (hrecordEq.symm ▸ hretained)

private theorem startRound_interrupted_at_firstCutoff
    (t : Fin p.T) (before : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (M : DownRecord (p := p) (rate := rate))
    (sigma : Fin p.T) (bits : Fin p.T → Bool) (s w u : ℕ)
    (token : ActiveFollowerLifecycle.ProposalRead p)
    (hstatus : before.status ≠ .unoccupied)
    (hvalid : ActiveFollowerLifecycle.localStateDomainValid before)
    (hrecord : before.lastDown = some M)
    (hM : M.val.sigma = s + 1) (hsigma : sigma.val = s)
    (htime : t.val = s + w) (hw : 0 < w) (hu : u = s + w + 1)
    (hfirst : FollowerCutoffScan.firstCutoff p rate.eta.val sigma bits = u)
    (hread : memory.lastProposalRead = some token)
    (htokenTime : token.timestamp.val + 1 = t.val)
    (htokenBit : token.bit = bits token.timestamp) :
    ActiveFollowerLifecycle.startRound rate.eta t before memory =
      .ok ({before with status := .unoccupied}, memory) := by
  have hcoordinate : ActiveFollowerLifecycle.acceptedStartCoordinate M = sigma := by
    apply Fin.ext
    have hMcoord := ActiveFollowerLifecycle.accepted_start_coordinate_one_based M
    omega
  have hbounds := FollowerCutoffScan.firstCutoff_bounds p rate.eta.val
    rate.eta.property rate.sourceCap sigma bits
  have hgrid : u ≤ FollowerCutoffScan.gridBoundary p rate.eta.val sigma := by
    rw [← hfirst]
    exact hbounds.2
  have hcarrier : u ∈ FollowerCutoffScan.firstCutoffCarrier p rate.eta.val sigma bits := by
    rw [← hfirst]
    exact Finset.min'_mem _ _
  change u ∈ insert (FollowerCutoffScan.gridBoundary p rate.eta.val sigma)
    (FollowerCutoffScan.trueProposalEndpoints bits
      (FollowerCutoffScan.proposalCoordinates p sigma)) at hcarrier
  have hinterrupt :
      FollowerCutoffScan.gridBoundary p rate.eta.val sigma = t.val + 1 ∨ token.bit = true := by
    rcases Finset.mem_insert.mp hcarrier with hgridEq | hproposal
    · left
      rw [← hgridEq]
      omega
    · unfold FollowerCutoffScan.trueProposalEndpoints at hproposal
      rcases Finset.mem_image.mp hproposal with ⟨stamp, hstamp, hendpoint⟩
      have hstampBit : bits stamp = true := (Finset.mem_filter.mp hstamp).2
      have hstampValue : stamp.val + 2 = token.timestamp.val + 2 := by
        simp only [FollowerCutoffScan.proposalEndpoint] at hendpoint
        have htokenEndpoint : token.timestamp.val + 2 = u := by omega
        omega
      have hstampToken : stamp = token.timestamp := Fin.ext (by omega)
      right
      calc
        token.bit = bits token.timestamp := htokenBit
        _ = bits stamp := congrArg bits hstampToken.symm
        _ = true := hstampBit
  have hstarted : M.val.sigma ≤ t.val := by omega
  have hnotmissed : t.val + 1 ≤
      FollowerCutoffScan.gridBoundary p rate.eta.val
        (ActiveFollowerLifecycle.acceptedStartCoordinate M) := by
    rw [hcoordinate]
    omega
  have hstamp : ActiveFollowerLifecycle.isPriorProposalRead t token := by
    change token.timestamp.val + 1 = t.val
    exact htokenTime
  rw [ActiveFollowerLifecycle.startRound_occupied_branch rate.eta t before memory
    hstatus hvalid M hrecord hstarted hnotmissed token hread hstamp]
  rcases hinterrupt with hgridCut | hbit
  · simp [hcoordinate, hgridCut]
  · simp [hcoordinate, hbit]

private theorem finishFollower_down_frame
    (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (prepared : DeclaredFollowerLocalRound.PreparedRound p rate)
    (observation : ReferencePrelaunchFollower.Observation p)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hconfiguration : prepared.configuration = .ordinary state memory) :
    (ReferenceActivePhysicalStep.finishFollower view prepared observation).down =
      (ReferenceActivePhysicalStep.recordFollower view prepared.follower prepared.row
        prepared.activation prepared.time prepared.active prepared.arm observation state).down := by
  cases hrecord : ReferenceActivePhysicalStep.recordFollower view prepared.follower prepared.row
      prepared.activation prepared.time prepared.active prepared.arm observation state with
  | mk result downInput down =>
      cases result with
      | error failure =>
          simp [ReferenceActivePhysicalStep.finishFollower, hconfiguration, hrecord]
      | ok post =>
          cases hfinish : DeclaredFollowerLocalRound.releaseAndFinish rate prepared.follower
              prepared.row prepared.time observation state memory post with
          | error failure =>
              simp [ReferenceActivePhysicalStep.finishFollower, hconfiguration, hrecord, hfinish]
          | ok pair =>
              simp [ReferenceActivePhysicalStep.finishFollower, hconfiguration, hrecord, hfinish]

private theorem finishFollower_diagnostic_frame
    (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (prepared : DeclaredFollowerLocalRound.PreparedRound p rate)
    (observation : ReferencePrelaunchFollower.Observation p)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hconfiguration : prepared.configuration = .ordinary state memory) :
    (ReferenceActivePhysicalStep.finishFollower view prepared observation).downInput =
      (ReferenceActivePhysicalStep.recordFollower view prepared.follower prepared.row
        prepared.activation prepared.time prepared.active prepared.arm observation state).downInput ∧
    (ReferenceActivePhysicalStep.finishFollower view prepared observation).down =
      (ReferenceActivePhysicalStep.recordFollower view prepared.follower prepared.row
        prepared.activation prepared.time prepared.active prepared.arm observation state).down := by
  cases hrecord : ReferenceActivePhysicalStep.recordFollower view prepared.follower prepared.row
      prepared.activation prepared.time prepared.active prepared.arm observation state with
  | mk result downInput down =>
      cases result with
      | error failure =>
          simp [ReferenceActivePhysicalStep.finishFollower, hconfiguration, hrecord]
      | ok post =>
          cases hfinish : DeclaredFollowerLocalRound.releaseAndFinish rate prepared.follower
              prepared.row prepared.time observation state memory post with
          | error failure =>
              simp [ReferenceActivePhysicalStep.finishFollower, hconfiguration, hrecord, hfinish]
          | ok pair =>
              simp [ReferenceActivePhysicalStep.finishFollower, hconfiguration, hrecord, hfinish]

private theorem interrupted_choice_no_appliedDown
    (record : Record (p := p) (rate := rate)) (i : Fin (p.m - 1))
    (before : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (message : DownRecord (p := p) (rate := rate))
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (hchoice : (actualChoice record i).configuration =
      .ordinary {before with status := .unoccupied} memory)
    (hselected : ∃ selected : ReferenceActivePhysicalStep.Selection record.input,
      record.output.preparation.coordinator.selection = some selected ∧
        selected.view.payload = payload)
    (hlast : before.lastDown = some message)
    (hmessage : message = payload.downRecord i) :
    ∀ sigma, ¬ ReferenceFollowerReplyChronology.appliedDown record i sigma := by
  intro sigma happ
  rcases happ with ⟨logged, cut, after, raw, accepted, scan, registers, lastService,
    hinput, hdown, houtcome, hsigma⟩
  let prepared := ReferenceActivePhysicalStep.prepare record.input
  let localPrep := prepared.followers.followers i
  let observation := prepared.feedback.observations
    (PublicDiscreteDraws.followerPlayer p.two_le_m i)
  have hprepared : prepared = record.output.preparation := by
    dsimp only [prepared]
    rw [record.output_eq]
    rfl
  have hlocal : localPrep.configuration = .ordinary {before with status := .unoccupied} memory := by
    calc
      localPrep.configuration = (record.output.preparation.followers.followers i).configuration := by
        change (prepared.followers.followers i).configuration = _
        exact congrArg (fun prep : ReferenceActivePhysicalStep.PreparedRound record.input =>
          (prep.followers.followers i).configuration) hprepared
      _ = .ordinary {before with status := .unoccupied} memory := by
        simpa only [actualChoice] using hchoice
  obtain ⟨selected, hselection, hpayload⟩ := hselected
  have hview : prepared.coordinator.downView = some selected.view := by
    rw [hprepared]
    change record.output.preparation.coordinator.selection.map
      ReferenceActivePhysicalStep.Selection.view = some selected.view
    rw [hselection]
    rfl
  have hfinishDown :
      (ReferenceActivePhysicalStep.finishFollower prepared.coordinator.downView localPrep observation).down =
        some cut := by
    have h := hdown
    rw [record.output_eq] at h
    change (ReferenceActivePhysicalStep.finishFollower prepared.coordinator.downView
      localPrep observation).down = some cut at h
    exact h
  have hrecordDown :
      (ReferenceActivePhysicalStep.recordFollower (some selected.view) localPrep.follower localPrep.row
        localPrep.activation localPrep.time localPrep.active localPrep.arm observation
        {before with status := .unoccupied}).down = some cut := by
    have hframe := finishFollower_down_frame prepared.coordinator.downView localPrep observation
      {before with status := .unoccupied} memory hlocal
    calc
      (ReferenceActivePhysicalStep.recordFollower (some selected.view) localPrep.follower localPrep.row
        localPrep.activation localPrep.time localPrep.active localPrep.arm observation
        {before with status := .unoccupied}).down =
          (ReferenceActivePhysicalStep.finishFollower (some selected.view) localPrep observation).down := by
        simpa only [hview] using hframe.symm
      _ = some cut := by simpa only [hview] using hfinishDown
  have hinputFrame := finishFollower_diagnostic_frame prepared.coordinator.downView localPrep observation
    {before with status := .unoccupied} memory hlocal
  have hloggedInput :
      (ReferenceActivePhysicalStep.recordFollower (some selected.view) localPrep.follower localPrep.row
        localPrep.activation localPrep.time localPrep.active localPrep.arm observation
        {before with status := .unoccupied}).downInput = some logged := by
    have h := hinput
    rw [record.output_eq] at h
    change (ReferenceActivePhysicalStep.finishFollower prepared.coordinator.downView
      localPrep observation).downInput = some logged at h
    calc
      (ReferenceActivePhysicalStep.recordFollower (some selected.view) localPrep.follower localPrep.row
        localPrep.activation localPrep.time localPrep.active localPrep.arm observation
        {before with status := .unoccupied}).downInput =
          (ReferenceActivePhysicalStep.finishFollower (some selected.view) localPrep observation).downInput := by
        simpa only [hview] using hinputFrame.1.symm
      _ = some logged := by simpa only [hview] using h
  have hlog : ActiveFollowerLogging.checkedLogging localPrep.follower localPrep.row localPrep.activation
      localPrep.time (localPrep.arm, observation) {before with status := .unoccupied} = .ok logged := by
    cases hlogging : ActiveFollowerLogging.checkedLogging localPrep.follower localPrep.row localPrep.activation
        localPrep.time (localPrep.arm, observation) {before with status := .unoccupied} with
    | error failure =>
        simp [ReferenceActivePhysicalStep.recordFollower, hlogging] at hloggedInput
    | ok logged' =>
        have heq : logged' = logged := by
          simp [ReferenceActivePhysicalStep.recordFollower, hlogging] at hloggedInput
          exact hloggedInput
        simp only [heq]
  have hcutEq : cut = ReferenceDownReception.referenceDownCut p (some selected.view) i
      record.input.row record.input.time observation rate logged := by
    have h := hrecordDown
    simp [ReferenceActivePhysicalStep.recordFollower, hlog] at h
    have hcutLocal := h.symm
    have halignment := prepared.follower_alignment i
    simpa only [localPrep, halignment.1, halignment.2.1, halignment.2.2.1] using hcutLocal
  have haccepted :
      (ReferenceDownReception.referenceDownCut p (some selected.view) i record.input.row
        record.input.time observation rate logged).outcome =
        .accepted logged after raw accepted scan registers lastService := by
    rw [hcutEq] at houtcome
    exact houtcome
  have hstrict := ReferenceFollowerReplyChronology.referenceDownCut_accepted
    (some selected.view) i record.input.row record.input.time observation logged after
    raw accepted scan registers lastService haccepted
  have hactualMessage := ReferenceActiveDataOwnership.referenceDown_accepted_fields
    selected.view i record.input.row record.input.time observation logged logged after
    raw accepted scan registers lastService haccepted
  have hloggedFrame := ActiveFollowerLogging.checkedLogging_success_frame localPrep.follower
    localPrep.row localPrep.activation localPrep.time (localPrep.arm, observation)
    {before with status := .unoccupied} logged hlog
  have hloggedStart : ReferencePrelaunchFollower.acceptedStart logged =
      ReferencePrelaunchFollower.acceptedStart {before with status := .unoccupied} := by
    simp only [ReferencePrelaunchFollower.acceptedStart, hloggedFrame.1]
  have hchoiceStart : ReferencePrelaunchFollower.acceptedStart
      {before with status := .unoccupied} = message.val.sigma := by
    simp only [ReferencePrelaunchFollower.acceptedStart, hlast]
  have hsame : accepted.val.sigma = message.val.sigma := by
    rw [hactualMessage.1, hpayload]
    exact congrArg (fun M : DownRecord (p := p) (rate := rate) => M.val.sigma) hmessage.symm
  have hstartAccepted : ReferencePrelaunchFollower.acceptedStart logged = accepted.val.sigma :=
    hloggedStart.trans (hchoiceStart.trans hsame.symm)
  rw [hstartAccepted] at hstrict
  simp only [OrdinaryMessageCodec.acceptDown] at hstrict
  exact (Nat.lt_irrefl _) hstrict.1.1

private theorem dagger_choice_no_appliedDown
    (record : Record (p := p) (rate := rate)) (i : Fin (p.m - 1))
    (hchoice : (actualChoice record i).configuration = .dagger) :
    ∀ sigma, ¬ ReferenceFollowerReplyChronology.appliedDown record i sigma := by
  intro sigma happ
  rcases happ with ⟨logged, cut, after, raw, message, scan, registers, lastService,
    hinput, hdown, houtcome, hsigma⟩
  have hprepareDagger :
      ((ReferenceActivePhysicalStep.prepare record.input).followers.followers i).configuration = .dagger := by
    simpa only [ReferenceFollowerFixedReply.actualChoice, record.output_eq,
      ReferenceActivePhysicalStep.step] using hchoice
  have hdownNone := ReferenceActivePhysicalStep.finishFollower_dagger
    (ReferenceActivePhysicalStep.prepare record.input).coordinator.downView
    ((ReferenceActivePhysicalStep.prepare record.input).followers.followers i)
    ((ReferenceActivePhysicalStep.prepare record.input).feedback.observations
      (PublicDiscreteDraws.followerPlayer p.two_le_m i)) hprepareDagger
  have hactualDown : (record.output.followers i).down = none := by
    rw [record.output_eq]
    simpa only [ReferenceActivePhysicalStep.step,
      ReferenceActivePhysicalStep.PreparedRound.observeFollower] using hdownNone.2
  rw [hactualDown] at hdown
  cases hdown

/- The hypotheses here are the actual prefix-safety and payload-origin facts.
The public producer below supplies each one from the same original run. -/
private theorem retained_down_incoming
    (initial : ReferenceActivePhysicalStep.State p rate)
    (W : List (Record (p := p) (rate := rate)))
    (cut : Record (p := p) (rate := rate))
    (chain : ReferenceActivePhysicalHorizon.Connected initial W cut.input.state)
    (s : ℕ) (bits : Fin p.T → Bool)
    (payload : ReferenceActivePhysicalStep.Payload rate) (i : Fin (p.m - 1))
    (seed before : ReferencePrelaunchFollower.State p rate.eta)
    (seedMemory memory : ActiveFollowerLifecycle.LocalMemory p)
    (hseed : initial.followers i = .ordinary seed seedMemory)
    (hnone : seed.lastDown = none)
    (hbefore : cut.input.state.followers i = .ordinary before memory)
    (hzero : before.status = .unoccupied → before.lastDown = none)
    (hoccupied : before.status ≠ .unoccupied → 0 < W.length ∧ ∃ M token,
      before.lastDown = some M ∧ M.val.sigma = s + 1 ∧
      memory.lastProposalRead = some token ∧ token.timestamp.val + 1 = s + W.length ∧
      token.bit = bits token.timestamp)
    (horigin : ∀ record ∈ W, ∀ M : DownRecord (p := p) (rate := rate),
      ReferenceAcceptedUpFollowerHistory.RetainedDown record i M →
        M = payload.downRecord i ∧ M.val.sigma = s + 1 ∧ M.val.q = 0)
    (j : Fin W.length) (message : DownRecord (p := p) (rate := rate))
    (hretained : ReferenceAcceptedUpFollowerHistory.RetainedDown W[j.val] i message) :
    before.lastDown = some message ∧ message = payload.downRecord i ∧
    before.status ≠ .unoccupied ∧
    ReferencePrelaunchFollower.acceptedStart before = s + 1 ∧
    ∃ token : ActiveFollowerLifecycle.ProposalRead p,
      memory.lastProposalRead = some token ∧
      token.timestamp.val + 1 = s + W.length ∧ token.bit = bits token.timestamp := by
  have hmessage := horigin W[j.val] (List.getElem_mem j.isLt) message hretained
  obtain ⟨after, afterMemory, hafter, hafterBound⟩ :=
    ReferenceFollowerReplyChronology.connected_output_chronology chain i
      before memory hbefore j.val j.isLt
  have happly := ReferenceAcceptedUpFollowerHistory.retainedDown_appliedDown hretained
  obtain ⟨choice, choiceMemory, hchoice, hstrict, hafterStart⟩ :=
    ReferenceFollowerReplyChronology.record_appliedDown_strict W[j.val] i
      message.val.sigma happly after afterMemory hafter
  have hstartBound : s + 1 ≤ ReferencePrelaunchFollower.acceptedStart before := by
    by_cases hadjacent : j.val + 1 = W.length
    · -- At the endpoint, the previous output IS the incoming cutoff state.
      have htail := ReferenceFollowerReplyChronology.connected_drop_from_output
        chain j.val j.isLt
      rw [List.drop_eq_nil_of_le (show W.length ≤ j.val + 1 by omega)] at htail
      change cut.input.state = W[j.val].output.next at htail
      have hbeforeAtOutput : W[j.val].output.next.followers i = .ordinary before memory := by
        rw [← htail]
        exact hbefore
      have hstates := LocalConfiguration.ordinary.inj (hafter.symm.trans hbeforeAtOutput)
      rw [← hstates.1, hafterStart, hmessage.2.1]
    · -- A nonempty intervening suffix preserves the accepted-start lower bound.
      rw [hafterStart, hmessage.2.1] at hafterBound
      exact hafterBound
  have hstatus : before.status ≠ .unoccupied := by
    intro hu
    have hstartZero : ReferencePrelaunchFollower.acceptedStart before = 0 := by
      simp only [ReferencePrelaunchFollower.acceptedStart, hzero hu]
    omega
  obtain ⟨_, last, token, hlast, _, hread, htime, hbit⟩ := hoccupied hstatus
  have hlastOrigin : last = payload.downRecord i := by
    rcases connected_lastDown_origin chain i seed seedMemory before memory
        hseed hbefore last hlast with hseedLast | ⟨record, hmem, hretainedLast⟩
    · rw [hnone] at hseedLast
      cases hseedLast
    · exact (horigin record hmem last hretainedLast).1
  have hbeforeLast : before.lastDown = some message := by
    rw [hlast, hlastOrigin.trans hmessage.1.symm]
  have hstart : ReferencePrelaunchFollower.acceptedStart before = s + 1 := by
    simp only [ReferencePrelaunchFollower.acceptedStart, hbeforeLast, hmessage.2.1]
  exact ⟨hbeforeLast, hmessage.1, hstatus, hstart, token, hread, htime, hbit⟩

/- This local physical-step lemma assumes only the displayed incoming state,
interruption equation and actual selection. It retains preparation failures. -/
private theorem interrupted_record_reply
    (cut : Record (p := p) (rate := rate)) (i : Fin (p.m - 1))
    (before : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (message : DownRecord (p := p) (rate := rate))
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (hincoming : cut.input.state.followers i = .ordinary before memory)
    (hlast : before.lastDown = some message)
    (hmessage : message = payload.downRecord i)
    (hselected : ∃ selected : ReferenceActivePhysicalStep.Selection cut.input,
      cut.output.preparation.coordinator.selection = some selected ∧
        selected.view.payload = payload)
    (hstartRound : ActiveFollowerLifecycle.startRound rate.eta cut.input.time before memory =
      .ok ({before with status := .unoccupied}, memory)) :
    ((actualChoice cut i).configuration = .dagger ∨
      (actualChoice cut i).configuration =
        .ordinary {before with status := .unoccupied} memory) ∧
    (cut.output.next.followers i = .dagger ∨ ∃ out outMemory,
      cut.output.next.followers i = .ordinary out outMemory ∧
      out.status = .unoccupied ∧
      ReferenceFollowerReplyChronology.reply out = ReferenceFollowerReplyChronology.reply before ∧
      out.lastDown = some message ∧
      ReferencePrelaunchFollower.acceptedStart out = payload.sigma.val + 1) ∧
    (∀ sigma, ¬ ReferenceFollowerReplyChronology.appliedDown cut i sigma) := by
  have hchoiceBranch : (actualChoice cut i).configuration = .dagger ∨
      (actualChoice cut i).configuration =
        .ordinary {before with status := .unoccupied} memory := by
    cases hchoice : (actualChoice cut i).configuration with
    | dagger => exact Or.inl rfl
    | ordinary choice choiceMemory =>
        have hprepared : actualChoice cut i = DeclaredFollowerLocalRound.prepare rate i
            cut.input.row (cut.input.state.activations i) cut.input.time
            (cut.input.active i) (cut.input.state.followers i) :=
          cut.output.preparation.followers.followers_eq i
        have hordinary := hchoice
        rw [hprepared] at hordinary
        obtain ⟨incoming, incomingMemory, hinput, hstart, _, _⟩ :=
          ReferenceFollowerReplyChronology.prepare_ordinary_inversion i cut.input.row
            (cut.input.state.activations i) cut.input.time (cut.input.active i)
            (cut.input.state.followers i) choice choiceMemory hordinary
        obtain ⟨rfl, rfl⟩ := LocalConfiguration.ordinary.inj (hinput.symm.trans hincoming)
        have hsame := Prod.mk.inj (Except.ok.inj (hstart.symm.trans hstartRound))
        right
        rw [← hsame.1, ← hsame.2]
  have hnoApplied : ∀ sigma, ¬ ReferenceFollowerReplyChronology.appliedDown cut i sigma := by
    rcases hchoiceBranch with hdagger | hordinary
    · exact dagger_choice_no_appliedDown cut i hdagger
    · exact interrupted_choice_no_appliedDown cut i before memory message payload
        hordinary hselected hlast hmessage
  refine ⟨hchoiceBranch, ?_, hnoApplied⟩
  cases hnext : cut.output.next.followers i with
  | dagger => exact Or.inl rfl
  | ordinary out outMemory =>
      obtain ⟨choice, choiceMemory, hactual, _, hfreeze, hchange⟩ :=
        ReferenceFollowerReplyChronology.record_choice_chronology cut i out outMemory hnext
      rcases hchoiceBranch with hdagger | hordinary
      · have hfalse := hactual.symm.trans hdagger
        cases hfalse
      · have hsame := LocalConfiguration.ordinary.inj (hactual.symm.trans hordinary)
        have hstartOut : ReferencePrelaunchFollower.acceptedStart choice =
            ReferencePrelaunchFollower.acceptedStart out := by
          by_contra hne
          exact hnoApplied _ (hchange hne)
        obtain ⟨houtStatus, houtReply⟩ := hfreeze (by rw [hsame.1]) hstartOut
        have hreplyBefore : ReferenceFollowerReplyChronology.reply choice =
            ReferenceFollowerReplyChronology.reply before := by
          rw [hsame.1]
          rfl
        have hlastOut : out.lastDown = some message := by
          have h := congrArg Prod.fst (houtReply.trans hreplyBefore)
          change out.lastDown = before.lastDown at h
          exact h.trans hlast
        refine Or.inr ⟨out, outMemory, rfl, houtStatus,
          houtReply.trans hreplyBefore, hlastOut, ?_⟩
        rw [ReferencePrelaunchFollower.acceptedStart, hlastOut, hmessage]
        rfl

private theorem collectionPostChoice_configuration
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ) :
    (ReferenceActivePhysicalStep.collectionPostChoice prepared payload ledger started weights).configuration =
        .dagger ∨
      ∃ nextLedger saved,
        (ReferenceActivePhysicalStep.collectionPostChoice prepared payload ledger started weights).configuration =
          .collection payload nextLedger saved := by
  classical
  unfold ReferenceActivePhysicalStep.collectionPostChoice
  cases hrecording : CoordinatorRecorderComplementBridge.run
      (ReferenceActivePhysicalStep.collectionRecordingInput prepared payload started weights) with
  | none => simp [ReferenceActivePhysicalStep.coordinatorFailure]
  | some recording =>
      dsimp only [hrecording]
      let enabled := ReferenceActivePhysicalStep.collectionEnabled ledger x.time
      let raw := CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording
      cases hstart : CoordinatorCollectionLedger.startRound ledger (x.time.val + 1) enabled raw with
      | invalid => simp [ReferenceActivePhysicalStep.coordinatorFailure]
      | rejected rejected => simp [ReferenceActivePhysicalStep.coordinatorFailure]
      | success startedLedger =>
          dsimp only [hstart]
          cases hcut : (ReferenceActivePhysicalStep.receiveUp prepared startedLedger).result with
          | invalid =>
              simp [ReferenceActivePhysicalStep.collectionFinish, hcut,
                ReferenceActivePhysicalStep.coordinatorFailure]
          | rejected rejected =>
              rcases rejected with ⟨nextLedger, bank⟩
              cases hfinish : CoordinatorCollectionLedger.finishRound nextLedger with
              | invalid => simp [ReferenceActivePhysicalStep.collectionFinish, hcut, hfinish,
                  ReferenceActivePhysicalStep.coordinatorFailure]
              | rejected rejectedLedger =>
                  simp [ReferenceActivePhysicalStep.collectionFinish, hcut, hfinish,
                    ReferenceActivePhysicalStep.coordinatorFailure]
              | success ledgerFinished =>
                  cases hclock : CoordinatorPhaseClock.finishRound p rate.eta.val x.time
                      started.clock ledgerFinished.pending x.row with
                  | error reason =>
                      simp [ReferenceActivePhysicalStep.collectionFinish, hcut, hfinish, hclock,
                        ReferenceActivePhysicalStep.coordinatorFailure]
                  | ok clockFinished =>
                      refine Or.inr ⟨ledgerFinished, clockFinished.clock.lastProposal, ?_⟩
                      simp [ReferenceActivePhysicalStep.collectionFinish, hcut, hfinish, hclock]
          | success pair =>
              rcases pair with ⟨nextLedger, bank⟩
              cases hfinish : CoordinatorCollectionLedger.finishRound nextLedger with
              | invalid => simp [ReferenceActivePhysicalStep.collectionFinish, hcut, hfinish,
                  ReferenceActivePhysicalStep.coordinatorFailure]
              | rejected rejectedLedger =>
                  simp [ReferenceActivePhysicalStep.collectionFinish, hcut, hfinish,
                    ReferenceActivePhysicalStep.coordinatorFailure]
              | success ledgerFinished =>
                  cases hclock : CoordinatorPhaseClock.finishRound p rate.eta.val x.time
                      started.clock ledgerFinished.pending x.row with
                  | error reason =>
                      simp [ReferenceActivePhysicalStep.collectionFinish, hcut, hfinish, hclock,
                        ReferenceActivePhysicalStep.coordinatorFailure]
                  | ok clockFinished =>
                      refine Or.inr ⟨ledgerFinished, clockFinished.clock.lastProposal, ?_⟩
                      simp [ReferenceActivePhysicalStep.collectionFinish, hcut, hfinish, hclock]

/- All local hypotheses are produced before the public query is introduced:
actual prefix safety, original-row cutoff geometry, payload origin and the
actual selection. No successful preparation or output is assumed. -/
private theorem first_cutoff_retained_queries
    (initial : ReferenceActivePhysicalStep.State p rate)
    (records W : List (Record (p := p) (rate := rate)))
    (cut : Record (p := p) (rate := rate))
    (suffix : List (Record (p := p) (rate := rate)))
    (hsplit : records = W ++ cut :: suffix)
    (chain : ReferenceActivePhysicalHorizon.Connected initial W cut.input.state)
    (s : ℕ) (bits : Fin p.T → Bool)
    (P0 : ReferenceActivePhysicalStep.Payload rate)
    (hsigma : P0.sigma.val = s)
    (htime : cut.input.time.val = s + W.length)
    (hcutoff : FollowerCutoffScan.firstCutoff p rate.eta.val P0.sigma bits = s + W.length + 1)
    (seed : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
    (seedMemory : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p)
    (hseed : ∀ i, initial.followers i = .ordinary (seed i) (seedMemory i))
    (hnone : ∀ i, (seed i).lastDown = none)
    (hfollowers : ∀ i, ∃ before memory,
      cut.input.state.followers i = .ordinary before memory ∧
      ActiveFollowerLifecycle.localStateDomainValid before ∧
      (before.status = .unoccupied → before.lastDown = none) ∧
      (before.status ≠ .unoccupied → 0 < W.length ∧ ∃ M token,
        before.lastDown = some M ∧ M.val.sigma = s + 1 ∧
        memory.lastProposalRead = some token ∧ token.timestamp.val + 1 = s + W.length ∧
        token.bit = bits token.timestamp))
    (horigin : ∀ record ∈ W, ∀ i, ∀ M : DownRecord (p := p) (rate := rate),
      ReferenceAcceptedUpFollowerHistory.RetainedDown record i M →
        M = P0.downRecord i ∧ M.val.sigma = s + 1 ∧ M.val.q = 0)
    (hselected : ∃ selected : ReferenceActivePhysicalStep.Selection cut.input,
      cut.output.preparation.coordinator.selection = some selected ∧ selected.view.payload = P0) :
    ∀ (i : Fin (p.m - 1)) (j : Fin records.length)
      (M : DownRecord (p := p) (rate := rate)),
      j.val < W.length → ReferenceAcceptedUpFollowerHistory.RetainedDown records[j.val] i M →
      ∃ (before : ReferencePrelaunchFollower.State p rate.eta)
        (memory : ActiveFollowerLifecycle.LocalMemory p)
        (token : ActiveFollowerLifecycle.ProposalRead p),
        cut.input.state.followers i = .ordinary before memory ∧
        before.lastDown = some M ∧ M = P0.downRecord i ∧
        before.status ≠ .unoccupied ∧
        ReferencePrelaunchFollower.acceptedStart before = s + 1 ∧
        ActiveFollowerLifecycle.localStateDomainValid before ∧
        memory.lastProposalRead = some token ∧
        token.timestamp.val + 1 = cut.input.time.val ∧
        token.bit = bits token.timestamp ∧
        ActiveFollowerLifecycle.startRound rate.eta cut.input.time before memory =
          .ok ({before with status := .unoccupied}, memory) ∧
        ((actualChoice cut i).configuration = .dagger ∨
          (actualChoice cut i).configuration =
            .ordinary {before with status := .unoccupied} memory) ∧
        (cut.output.next.followers i = .dagger ∨
          ∃ out outMemory,
            cut.output.next.followers i = .ordinary out outMemory ∧
            out.status = .unoccupied ∧
            ReferenceFollowerReplyChronology.reply out =
              ReferenceFollowerReplyChronology.reply before ∧
            out.lastDown = some M ∧
            ReferencePrelaunchFollower.acceptedStart out = P0.sigma.val + 1) ∧
        (∀ sigma, ¬ ReferenceFollowerReplyChronology.appliedDown cut i sigma) := by
  intro i j message hj hretained
  have hlookup : records[j.val]? = some W[j.val] := by
    have h := congrArg (fun xs : List (Record (p := p) (rate := rate)) => xs[j.val]?) hsplit
    rw [List.getElem?_append_left hj, List.getElem?_eq_getElem hj] at h
    exact h
  have hrecordAt : records[j.val] = W[j.val] := by
    rw [List.getElem?_eq_getElem j.isLt] at hlookup
    exact Option.some.inj hlookup
  have hretainedW : ReferenceAcceptedUpFollowerHistory.RetainedDown W[j.val] i message :=
    hrecordAt ▸ hretained
  obtain ⟨before, memory, hbefore, hvalid, hzero, hoccupied⟩ := hfollowers i
  obtain ⟨hlast, hmessage, hstatus, hstart, token, hread, htokenTime, htokenBit⟩ :=
    retained_down_incoming initial W cut chain s bits P0 i (seed i) before
      (seedMemory i) memory (hseed i) (hnone i) hbefore hzero hoccupied
      (fun record hmem M hM => horigin record hmem i M hM) ⟨j.val, hj⟩ message hretainedW
  have hmessageSigma : message.val.sigma = s + 1 := by
    simpa only [ReferencePrelaunchFollower.acceptedStart, hlast] using hstart
  have hstartRound := startRound_interrupted_at_firstCutoff cut.input.time before memory
    message P0.sigma bits s W.length (s + W.length + 1) token hstatus hvalid hlast
    hmessageSigma hsigma htime (by omega) rfl hcutoff hread (by omega) htokenBit
  obtain ⟨hchoice, houtput, hnoApplied⟩ := interrupted_record_reply
    cut i before memory message P0 hbefore hlast hmessage hselected hstartRound
  exact ⟨before, memory, token, hbefore, hlast, hmessage, hstatus, hstart, hvalid,
    hread, by omega, htokenBit, hstartRound, hchoice, houtput, hnoApplied⟩

/- Every conditional input is a literal launch fact, supplied below by
`actual_launch_seed`; decoder validity is obtained from its domain fact. -/
private theorem first_live_boundary_safety
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hfirst : initial.coordinator = .first)
    (seed : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
    (memory : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p)
    (hseeds : ∀ i, initial.followers i = .ordinary (seed i) (memory i) ∧
      (seed i).lastDown = none ∧ ReferencePrelaunchFollower.acceptedStart (seed i) = 0 ∧
      (seed i).S = 0 ∧ (seed i).delta = 0 ∧ (seed i).backlog = 0 ∧
      (seed i).status = .unoccupied ∧
      ActiveFollowerLifecycle.localStateDomainValid (seed i) ∧
      ActiveFollowerLifecycle.localBufferValid (seed i) ∧
      (seed i).buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound) ∧
      ∀ saved ∈ (seed i).buffer, saved.calendarRound ≤ start) :
    let E := ReferenceActivePhysicalHorizon.run initial rows J rewards start count hspan active
    let W := ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records
    ∃ hprefix : start + W.length ≤ p.T, ∀ i, ∃ before mem,
      (ReferenceActivePhysicalHorizon.run initial rows J rewards start W.length hprefix active).finalState.followers i =
        .ordinary before mem ∧
      ActiveFollowerLifecycle.localStateDomainValid before ∧
      (before.status = .unoccupied → before.lastDown = none) ∧
      (before.status ≠ .unoccupied → 0 < W.length ∧ ∃ M token,
        before.lastDown = some M ∧ M.val.sigma = start + 1 ∧
        mem.lastProposalRead = some token ∧ token.timestamp.val + 1 = start + W.length ∧
        token.bit = FollowerCutoffScan.completeRowProposalBit p rate.eta.val (rows J) token.timestamp) := by
  intro E W
  have hseedState : ∀ i, initial.followers i = .ordinary (seed i) (memory i) := by
    intro i
    exact (hseeds i).1
  have hseedS : ∀ i, (seed i).S = 0 := by
    intro i
    rcases hseeds i with ⟨_, _, _, hS, _, _, _, _, _, _, _⟩
    exact hS
  have hseedDelta : ∀ i, (seed i).delta = 0 := by
    intro i
    rcases hseeds i with ⟨_, _, _, _, hdelta, _, _, _, _, _, _⟩
    exact hdelta
  have hseedBacklog : ∀ i, (seed i).backlog = 0 := by
    intro i
    rcases hseeds i with ⟨_, _, _, _, _, hbacklog, _, _, _, _, _⟩
    exact hbacklog
  have hseedNone : ∀ i, (seed i).lastDown = none := by
    intro i
    rcases hseeds i with ⟨_, hnone, _, _, _, _, _, _, _, _, _⟩
    exact hnone
  have hseedUnoccupied : ∀ i, (seed i).status = .unoccupied := by
    intro i
    rcases hseeds i with ⟨_, _, _, _, _, _, hu, _, _, _, _⟩
    exact hu
  have hseedDomain : ∀ i, ActiveFollowerLifecycle.localStateDomainValid (seed i) := by
    intro i
    rcases hseeds i with ⟨_, _, _, _, _, _, _, hvalid, _, _, _⟩
    exact hvalid
  have hseedBuffer : ∀ i, ActiveFollowerLifecycle.localBufferValid (seed i) := by
    intro i
    rcases hseeds i with ⟨_, _, _, _, _, _, _, _, hbuffer, _, _⟩
    exact hbuffer
  have hseedPair : ∀ i, (seed i).buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound) := by
    intro i
    rcases hseeds i with ⟨_, _, _, _, _, _, _, _, _, hpair, _⟩
    exact hpair
  have hseedTime : ∀ i saved, saved ∈ (seed i).buffer → saved.calendarRound ≤ start := by
    intro i saved hs
    rcases hseeds i with ⟨_, _, _, _, _, _, _, _, _, _, htime⟩
    exact htime saved hs
  have hseedDecoder : ∀ i, ActiveFollowerLifecycle.downDecoderStateValid (seed i) := by
    intro i
    exact (hseedDomain i).2.2
  have hsafety := ReferenceFirstLiveFollowerSafety.run_first_live_follower_safety
    initial rows J rewards start count hspan active hfirst seed memory
    hseedState hseedS hseedDelta hseedBacklog hseedNone hseedUnoccupied
    hseedBuffer hseedPair hseedTime hseedDecoder
  obtain ⟨hprefix, hfollowers⟩ := hsafety.1 W.length le_rfl
  refine ⟨hprefix, ?_⟩
  intro i
  obtain ⟨before, mem, hbefore, hvalid, _, _, _, hzero, hoccupied⟩ := hfollowers i
  exact ⟨before, mem, hbefore, hvalid, fun hu => (hzero hu).1, hoccupied⟩

/-- The first cutoff's actual incoming state is the single retained DOWN reply
from any earlier accepted record. The query hypotheses occur only in the
conclusion, and `j + 1 = w` is included as the immediately preceding record.
The output keeps both actual dagger alternatives and the real collection
finish data. -/
theorem actual_first_cutoff_retained_down_reply_seed
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
    let Erun := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
      rate source rewards C_star C_h hcross count hspan
    let W := ReferenceFirstLiveConfirmationHistory.firstLiveWindow Erun.records
    let w := W.length
    let B := ReferenceCollectionPhaseHistory.collectionWindow Erun.records w
    let u := s + w + 1
    ∃ (cut : Record (p := p) (rate := rate))
      (suffix : List (Record (p := p) (rate := rate)))
      (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
      (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
      (base : Fin (p.m - 1) → ℕ)
      (P0 : ReferenceActivePhysicalStep.Payload rate)
      (birth : Record (p := p) (rate := rate)),
      Erun.records = W ++ cut :: suffix ∧
      ReferenceActivePhysicalHorizon.Connected I W cut.input.state ∧
      (∃ hindex : w < Erun.records.length, cut = Erun.records[w]'hindex) ∧
      cut.input.time.val = s + w ∧
      cut.input.state.coordinator = .live registers owned base ∧
      ReferenceCollectionPhaseHistory.cutoffChosen cut.input = true ∧
      P0 = registers.payload ∧ P0.sigma.val = s ∧
      (∀ arm, P0.queues arm = 0) ∧
      FollowerCutoffScan.firstCutoff p rate.eta.val P0.sigma
        (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
          (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source))) = u ∧
      birth ∈ Erun.records ∧
      ReferenceAssignmentPayloadPersistence.InstallationBirth birth P0 ∧
      birth.input.time.val = s ∧
      (∃ installed birthSelection,
        birth.output.preparation.coordinator = .first (.chosen installed birthSelection) ∧
          installed.registers.payload = P0) ∧
      (∀ k : Fin B.length,
        Erun.records[w + k.val]? = some B[k.val] ∧
          B[k.val].input.time.val + 1 = u + k.val) ∧
      (let callInput := ReferenceActivePhysicalStep.liveInput cut.input registers owned base
       ∃ (dispatched : CoordinatorStartRoundCutoffDispatch.Output
          callInput.registers callInput.ownedRegisters base),
        ∃ (hstart : CoordinatorPhaseClock.startRound p rate.eta.val callInput.registers.time
          callInput.registers.priorClock callInput.registers.clockPending = .ok dispatched.startResult),
        ∃ (ledger : CoordinatorStartRoundCutoffDispatch.NewLedger callInput.registers),
        ∃ (hinit : dispatched.collectionInitialization = .success (some ledger)),
        ∃ (hledger : ledger = CoordinatorStartRoundCutoffDispatch.collectionStartLedger
          callInput.registers callInput.ownedRegisters base callInput.registers.time),
        ∃ (hdomain : CoordinatorStartRoundCutoffDispatch.initializationDomainValid
          callInput.registers callInput.ownedRegisters base callInput.registers.time),
        ∃ (hclock : dispatched.startResult.clock =
          { callInput.registers.priorClock with u := some callInput.registers.time }),
        ∃ (hpending : dispatched.startResult.pending = Finset.univ),
        ∃ (hnoAssignment : dispatched.startResult.assignmentStart = none),
        ∃ (selected : CoordinatorRoundDispatch.ArmSelection
          callInput.registers.payload dispatched.startResult callInput.registers.time
            callInput.registers.complementWeights callInput.row),
        cut.output.preparation.coordinator = .live registers owned base
          (.cutoffChosen dispatched hstart ledger hinit hledger hdomain hclock hpending
            hnoAssignment selected) ∧
        cut.output.coordinator =
          ReferenceActivePhysicalStep.collectionPostChoice cut.output.preparation registers.payload
            (ReferenceActivePhysicalStep.sharedLedger ledger) dispatched.startResult
            callInput.registers.complementWeights) ∧
      (cut.output.next.coordinator = .dagger ∨
        ∃ nextLedger saved, cut.output.next.coordinator = .collection P0 nextLedger saved) ∧
      (∀ (i : Fin (p.m - 1)) (j : Fin Erun.records.length)
        (M : DownRecord (p := p) (rate := rate)),
        j.val < w → ReferenceAcceptedUpFollowerHistory.RetainedDown Erun.records[j.val] i M →
        ∃ (before : ReferencePrelaunchFollower.State p rate.eta)
          (memory : ActiveFollowerLifecycle.LocalMemory p)
          (token : ActiveFollowerLifecycle.ProposalRead p),
          cut.input.state.followers i = .ordinary before memory ∧
          before.lastDown = some M ∧ M = P0.downRecord i ∧
          before.status ≠ .unoccupied ∧
          ReferencePrelaunchFollower.acceptedStart before = s + 1 ∧
          ActiveFollowerLifecycle.localStateDomainValid before ∧
          memory.lastProposalRead = some token ∧
          token.timestamp.val + 1 = cut.input.time.val ∧
          token.bit = FollowerCutoffScan.completeRowProposalBit p rate.eta.val
            (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)) token.timestamp ∧
          ActiveFollowerLifecycle.startRound rate.eta cut.input.time before memory =
            .ok ({before with status := .unoccupied}, memory) ∧
          ((actualChoice cut i).configuration = .dagger ∨
            (actualChoice cut i).configuration =
              .ordinary {before with status := .unoccupied} memory) ∧
          (cut.output.next.followers i = .dagger ∨
            ∃ out outMemory,
              cut.output.next.followers i = .ordinary out outMemory ∧
              out.status = .unoccupied ∧
              ReferenceFollowerReplyChronology.reply out =
                ReferenceFollowerReplyChronology.reply before ∧
              out.lastDown = some M ∧
              ReferencePrelaunchFollower.acceptedStart out = P0.sigma.val + 1) ∧
          (∀ sigma, ¬ ReferenceFollowerReplyChronology.appliedDown cut i sigma)) := by
  classical
  intro x0 b0 s I Erun W w B u
  let rows := source.1.2
  let J := ActualInitializationPhysicalStep.selectedRowIndex p source
  let initial := ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hcross
  have hroot := ReferenceFirstCollectionOfferedSenderReplay.run_first_collection_offered_sender_replay
    rate source rewards C_star C_h count hcross hspan hshort
  have hroot' := hroot
  dsimp only [x0, b0, s, I, Erun, W, w, B, u] at hroot'
  rcases hroot' with ⟨cutRoot, suffixRoot, registersRoot, ownedRoot, baseRoot,
    payloadRoot, birthRoot,
    hsplitRoot, hindexRoot, htimeRoot, hstateRoot, hcutoffRoot, hpayloadRoot,
    hsigmaRoot, hqueuesRoot, hfirstCutoffRoot, hbirthMemRoot, hbirthInstallRoot,
    hbirthTimeRoot, hbirthFirstRoot, hwindowRoot, _hqueriesRoot⟩
  have horigin := ReferenceFirstCollectionDownPayloadOrigin.actual_first_collection_down_payload_origin
    rate source rewards C_star C_h count hcross hspan hshort
  let hclaim := horigin
  dsimp only [s, I, Erun, W, w, B, u] at hclaim
  rcases hclaim.origin with ⟨cutOrigin, payloadOrigin, birthOrigin,
    registersOrigin, ownedOrigin, baseOrigin, hindexOrigin, huniqueOrigin,
    hstateOrigin, hcutoffOrigin, hpayloadOrigin, hsigmaOrigin, hqueuesOrigin,
    hfirstCutoffOrigin, hbirthMemOrigin, hbirthInstallOrigin, hbirthTimeOrigin,
    hbirthFirstOrigin, hwindowLookupOrigin, hselectedPayloadOrigin,
    hretainedWindowOrigin, hpriorOrigin⟩
  have hrootOrigin : cutRoot = cutOrigin := huniqueOrigin cutRoot suffixRoot hsplitRoot
  have hOutside := ReferenceFirstCutoffOutsideInitialization.run_first_cutoff_outside_initializer
    I rows J rewards s count hspan
    (by simpa [I, initial] using
      (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
        rate source rewards C_star C_h hcross).1)
    (by simpa [I] using
      (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
        rate source rewards C_star C_h hcross).2)
    hshort
  rcases hOutside with ⟨cutOutside, suffixOutside, hsplitOutside, hindexOutside,
    htimeOutside, _hactualOutside, registersOutside, ownedOutside, baseOutside,
    hcutStateOutside, hprefixLiveOutside, dispatchedOutside, hstartOutside,
    ledgerOutside, hinitOutside, hledgerOutside, hdomainOutside, hclockOutside,
    hpendingOutside, hnoAssignmentOutside, selectedOutside, hcutBranchOutside,
    htailOutside⟩
  rcases htailOutside with ⟨_hkOutside, _hpayloadSigmaOutside, _hbaseZeroOutside,
    _hbirthOutside, _hproposalFalseOutside, _hqueuesOutside, _hgeometryOutside⟩
  have hsplitOutside' : Erun.records = W ++ cutOutside :: suffixOutside := by
    simpa only [Erun, W, I,
      ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun] using hsplitOutside
  have hOutsideOrigin : cutOutside = cutOrigin :=
    huniqueOrigin cutOutside suffixOutside hsplitOutside'
  cases hrootOrigin
  cases hOutsideOrigin
  rcases hindexRoot with ⟨hindex, hcutGet⟩
  have hliveRootOrigin := hstateRoot.symm.trans hstateOrigin
  injection hliveRootOrigin with hregistersRoot hownedRoot hbaseRoot
  subst registersRoot
  cases hownedRoot
  subst baseRoot
  have hstateOutside : cutRoot.input.state.coordinator =
      .live registersOutside ownedOutside baseOutside := by
    rw [hcutStateOutside]
    exact hprefixLiveOutside
  have hliveOutsideOrigin := hstateOutside.symm.trans hstateOrigin
  injection hliveOutsideOrigin with hregistersOutside hownedOutside hbaseOutside
  subst registersOutside
  cases hownedOutside
  subst baseOutside
  have hrootPayloadOrigin : payloadRoot = payloadOrigin := by
    rw [hpayloadRoot, hpayloadOrigin]
  have hbirthInstall : ReferenceAssignmentPayloadPersistence.InstallationBirth birthRoot payloadOrigin := by
    rw [← hrootPayloadOrigin]
    exact hbirthInstallRoot
  have hlaunchSeed := ReferenceFirstLaunchNumericalCell.actual_launch_seed
    rate source rewards C_star C_h hcross
  rcases hlaunchSeed with ⟨_, hmodeLaunch, _, hfirstLaunch, _, _, _, hseeds⟩
  have hmodeI : ReferenceActivePhysicalHorizon.allActiveAtStart I s := by
    simpa only [I, initial, ReferenceFirstCollectionEpochAlignment.actualLaunchState,
      ReferenceFirstLaunchNumericalCell.launchState] using hmodeLaunch
  have hfirstI : I.coordinator = .first := by
    simpa only [I, initial, ReferenceFirstCollectionEpochAlignment.actualLaunchState,
      ReferenceFirstLaunchNumericalCell.launchState] using hfirstLaunch
  let seed := fun i : Fin (p.m - 1) => ReferenceInitializationRun.ordinary x0 b0
    (ActualReferenceInitializationBlock.refFollower i)
  let memory := fun _ : Fin (p.m - 1) => ActiveFollowerLifecycle.initialMemory p
  have hlaunchFacts (i : Fin (p.m - 1)) :
      I.followers i = .ordinary (seed i) (memory i) ∧
      (seed i).lastDown = none ∧ ReferencePrelaunchFollower.acceptedStart (seed i) = 0 ∧
      (seed i).S = 0 ∧ (seed i).delta = 0 ∧ (seed i).backlog = 0 ∧
      (seed i).status = .unoccupied ∧
      ActiveFollowerLifecycle.localStateDomainValid (seed i) ∧
      ActiveFollowerLifecycle.localBufferValid (seed i) ∧
      (seed i).buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound) ∧
      ∀ saved ∈ (seed i).buffer, saved.calendarRound ≤ s := by
    have h := hseeds i
    simpa only [I, seed, memory, ReferenceFirstCollectionEpochAlignment.actualLaunchState,
      ReferenceFirstLaunchNumericalCell.launchState, x0, b0, s] using h
  have hseedState : ∀ i, I.followers i = .ordinary (seed i) (memory i) := by
    intro i
    exact (hlaunchFacts i).1
  have hseedNone : ∀ i, (seed i).lastDown = none := by
    intro i
    exact (hlaunchFacts i).2.1
  obtain ⟨hspanW, hfollowersW⟩ := first_live_boundary_safety
    I rows J rewards s count hspan hmodeI hfirstI seed memory hlaunchFacts
  have hconnectedW0 :=
    ReferenceFollowerReplyChronology.connected_take_to_input Erun.connected w hindex
  have htakeW : Erun.records.take w = W := by
    rw [hsplitRoot]
    change (W ++ cutRoot :: suffixRoot).take W.length = W
    rw [List.take_append_of_le_length (show W.length ≤ W.length from le_rfl)]
    simp
  have hconnectedW : ReferenceActivePhysicalHorizon.Connected I W cutRoot.input.state := by
    rw [← htakeW, hcutGet]
    exact hconnectedW0
  have hBpositive : 0 < B.length := by
    have hrecordsLength : Erun.records.length = count := by
      exact ReferenceActivePhysicalHorizon.run_record_count I rows J rewards s count hspan hmodeI
    have hdrop : 0 < (Erun.records.drop w).length := by
      rw [List.length_drop, hrecordsLength]
      exact Nat.sub_pos_of_lt (hrecordsLength ▸ hindex)
    have htake : 0 < ((Erun.records.drop w).take 1).length := by
      simp only [List.length_take]
      omega
    dsimp only [B, ReferenceCollectionPhaseHistory.collectionWindow]
    simp only [List.length_append]
    omega
  let callInput := ReferenceActivePhysicalStep.liveInput cutRoot.input
    registersOrigin ownedOrigin baseOrigin
  let outcome := CoordinatorRoundDispatch.LiveOutcome.cutoffChosen dispatchedOutside
    hstartOutside ledgerOutside hinitOutside hledgerOutside hdomainOutside hclockOutside
    hpendingOutside hnoAssignmentOutside selectedOutside
  have hselectedSome : ∃ selected : ReferenceActivePhysicalStep.Selection cutRoot.input,
      cutRoot.output.preparation.coordinator.selection = some selected := by
    rw [hcutBranchOutside]
    simp [ReferenceActivePhysicalStep.DispatchCut.selection,
      ReferenceActivePhysicalStep.selectionAt]
  obtain ⟨selectedAtCut, hselectedAtCut⟩ := hselectedSome
  have hcutSelectionNotNone :
      (ReferenceActivePhysicalStep.DispatchCut.live registersOrigin ownedOrigin
        baseOrigin outcome).selection ≠ none := by
    rw [← hcutBranchOutside, hselectedAtCut]
    exact Option.some_ne_none _
  have hcutObservation := ReferenceActivePhysicalStep.observeCoordinator_live_equation
    cutRoot.output.preparation registersOrigin ownedOrigin baseOrigin outcome hcutBranchOutside
  have hcutOutputEq : cutRoot.output.coordinator =
      ReferenceActivePhysicalStep.collectionPostChoice cutRoot.output.preparation
        registersOrigin.payload (ReferenceActivePhysicalStep.sharedLedger ledgerOutside)
        dispatchedOutside.startResult callInput.registers.complementWeights := by
    have hactualObservation : cutRoot.output.coordinator =
        cutRoot.output.preparation.observeCoordinator := by
      rw [cutRoot.output_eq]
      rfl
    calc
      cutRoot.output.coordinator = cutRoot.output.preparation.observeCoordinator := hactualObservation
      _ = ReferenceActivePhysicalStep.collectionPostChoice cutRoot.output.preparation
          registersOrigin.payload (ReferenceActivePhysicalStep.sharedLedger ledgerOutside)
          dispatchedOutside.startResult callInput.registers.complementWeights := by
        have h := hcutObservation
        rw [ite_eq_right hcutSelectionNotNone] at h
        simpa [callInput, ReferenceActivePhysicalStep.liveInput,
          ReferenceActivePhysicalStep.liveRegistersAt] using h
  have hsplitRootSource :
      (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
        rate source rewards C_star C_h hcross count hspan).records =
        W ++ cutRoot :: suffixRoot := by
    simpa only [Erun] using hsplitRoot
  have hindexSource : w <
      (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
        rate source rewards C_star C_h hcross count hspan).records.length := by
    simpa only [Erun] using hindex
  have hP0Sigma : registersOrigin.payload.sigma.val = s := by
    rw [← hpayloadOrigin]
    exact hsigmaOrigin
  have hP0Queues : ∀ arm, registersOrigin.payload.queues arm = 0 := by
    intro arm
    rw [← hpayloadOrigin]
    exact hqueuesOrigin arm
  have hP0Cutoff :
      FollowerCutoffScan.firstCutoff p rate.eta.val registersOrigin.payload.sigma
        (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
          (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source))) = u := by
    rw [← hpayloadOrigin]
    exact hfirstCutoffOrigin
  have hP0Install : ReferenceAssignmentPayloadPersistence.InstallationBirth
      birthRoot registersOrigin.payload := by
    rw [← hpayloadOrigin]
    exact hbirthInstall
  have hP0BirthFirst : ∃ installed birthSelection,
      birthRoot.output.preparation.coordinator = .first (.chosen installed birthSelection) ∧
        installed.registers.payload = registersOrigin.payload := by
    rcases hbirthFirstRoot with ⟨installed, birthSelection, hbirthChoice, hpayload⟩
    exact ⟨installed, birthSelection, hbirthChoice,
      hpayload.trans (hrootPayloadOrigin.trans hpayloadOrigin)⟩
  refine ⟨cutRoot, suffixRoot, registersOrigin, ownedOrigin, baseOrigin,
    registersOrigin.payload, birthRoot, hsplitRoot, hconnectedW, ⟨hindex, hcutGet⟩, htimeRoot,
    hstateRoot, hcutoffRoot, rfl, hP0Sigma, hP0Queues,
    hP0Cutoff, hbirthMemRoot, hP0Install, hbirthTimeRoot, hP0BirthFirst,
    hwindowRoot, ?_, ?_, ?_⟩
  · let callInput := ReferenceActivePhysicalStep.liveInput cutRoot.input
      registersOrigin ownedOrigin baseOrigin
    refine ⟨dispatchedOutside, hstartOutside, ledgerOutside, hinitOutside,
      hledgerOutside, hdomainOutside, hclockOutside, hpendingOutside,
      hnoAssignmentOutside, selectedOutside, hcutBranchOutside, hcutOutputEq⟩
  · let callInput := ReferenceActivePhysicalStep.liveInput cutRoot.input
      registersOrigin ownedOrigin baseOrigin
    have hpost := collectionPostChoice_configuration cutRoot.output.preparation
      registersOrigin.payload (ReferenceActivePhysicalStep.sharedLedger ledgerOutside)
      dispatchedOutside.startResult callInput.registers.complementWeights
    have hnext : cutRoot.output.next.coordinator =
          (ReferenceActivePhysicalStep.collectionPostChoice cutRoot.output.preparation
            registersOrigin.payload (ReferenceActivePhysicalStep.sharedLedger ledgerOutside)
            dispatchedOutside.startResult callInput.registers.complementWeights).configuration := by
      calc
        cutRoot.output.next.coordinator = cutRoot.output.coordinator.configuration := by
          rw [cutRoot.output_eq]
          rfl
        _ = (ReferenceActivePhysicalStep.collectionPostChoice cutRoot.output.preparation
            registersOrigin.payload (ReferenceActivePhysicalStep.sharedLedger ledgerOutside)
            dispatchedOutside.startResult callInput.registers.complementWeights).configuration :=
          congrArg ReferenceActivePhysicalStep.CoordinatorObservation.configuration hcutOutputEq
    rcases hpost with hdagger | ⟨nextLedger, saved, hcollection⟩
    · exact Or.inl (hnext.trans hdagger)
    · exact Or.inr ⟨nextLedger, saved, hnext.trans hcollection⟩
  · have hfollowersAtCut : ∀ i, ∃ before mem,
        cutRoot.input.state.followers i = .ordinary before mem ∧
        ActiveFollowerLifecycle.localStateDomainValid before ∧
        (before.status = .unoccupied → before.lastDown = none) ∧
        (before.status ≠ .unoccupied → 0 < W.length ∧ ∃ M token,
          before.lastDown = some M ∧ M.val.sigma = s + 1 ∧
          mem.lastProposalRead = some token ∧ token.timestamp.val + 1 = s + W.length ∧
          token.bit = FollowerCutoffScan.completeRowProposalBit p rate.eta.val (rows J) token.timestamp) := by
      intro i
      rw [hcutStateOutside]
      exact hfollowersW i
    have horiginW : ∀ record ∈ W, ∀ i, ∀ M : DownRecord (p := p) (rate := rate),
        ReferenceAcceptedUpFollowerHistory.RetainedDown record i M →
          M = registersOrigin.payload.downRecord i ∧ M.val.sigma = s + 1 ∧ M.val.q = 0 := by
      intro record hmem i M hretainedM
      have h := priorDown_payload_of_mem hsplitRootSource hindexSource rfl hBpositive
        hpriorOrigin hmem i M hretainedM
      refine ⟨?_, h.2⟩
      rw [h.1, hpayloadOrigin]
    have hselectedCut : ∃ selected : ReferenceActivePhysicalStep.Selection cutRoot.input,
        cutRoot.output.preparation.coordinator.selection = some selected ∧
          selected.view.payload = registersOrigin.payload := by
      have hcutLookup : Erun.records[w]? = some cutRoot := by
        rw [List.getElem?_eq_getElem hindex]
        exact congrArg some hcutGet.symm
      have hcutLookupSource :
          (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
            rate source rewards C_star C_h hcross count hspan).records[w]? = some cutRoot := by
        simpa only [Erun] using hcutLookup
      have hselectedPayload := hselectedPayloadOrigin ⟨0, hBpositive⟩ cutRoot
        (by simpa using hcutLookupSource) selectedAtCut hselectedAtCut
      exact ⟨selectedAtCut, hselectedAtCut, hselectedPayload.trans hpayloadOrigin⟩
    exact first_cutoff_retained_queries I Erun.records W cutRoot suffixRoot hsplitRoot
      hconnectedW s (FollowerCutoffScan.completeRowProposalBit p rate.eta.val (rows J))
      registersOrigin.payload hP0Sigma htimeRoot hP0Cutoff seed memory hseedState hseedNone
      hfollowersAtCut horiginW hselectedCut

end Bandits.Support.ReferenceFirstCutoffRetainedDownReplySeed
