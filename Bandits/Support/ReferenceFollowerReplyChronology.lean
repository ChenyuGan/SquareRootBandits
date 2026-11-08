/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFollowerFixedReply

/-!
# Follower reply register chronology

Sources: `sources/zip4/manuscript/05_binary_transport.tex:70-72,108-110`,
`sources/zip4/manuscript/06_interruptions.tex:168-177,248-295,327-348`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:100-108`.

These are internal statements about the literal active physical transition.
They do not identify the registers with global service or queue quantities,
and do not prove coordinator barriers, stale-batch safety, or manuscript closure.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions
open ReferenceFollowerFixedReply
open ReferencePrelaunchFollower
open DeclaredFollowerLocalRound

namespace Bandits.Support.ReferenceFollowerReplyChronology

section Chronology

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

/-- The whole retained DOWN record and the three numerical reply fields.
The decoder batch, sparse buffer, and proposal memory are deliberately not
part of this projection and are never replaced by a fresh seed. -/
def reply (s : ReferencePrelaunchFollower.State p rate.eta) :=
  (s.lastDown, s.S, s.delta, s.backlog)

theorem acceptedStart_eq_of_reply_eq
    {s s' : ReferencePrelaunchFollower.State p rate.eta}
    (h : reply s = reply s') : acceptedStart s = acceptedStart s' := by
  have hd := congrArg Prod.fst h
  change s.lastDown = s'.lastDown at hd
  simp only [acceptedStart, hd]

/-- Inverting the actual filtered decoder, including suppression of a raw
mismatch, yields either framed reply fields and status, or its actual
accepted outcome with the strict source acceptance predicate. -/
theorem referenceDownCut_ordinary_inversion
    (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (t : Fin p.T) (observation : Observation p)
    (before after : ReferencePrelaunchFollower.State p rate.eta)
    (h : consumeDownResult rate
      (ReferenceDownReception.referenceDownCut p view i row t observation rate before).outcome =
        .ok after) :
    (reply after = reply before ∧ after.status = before.status) ∨
      ∃ raw M scan registers lastService,
        (ReferenceDownReception.referenceDownCut p view i row t observation rate before).outcome =
          .accepted before after raw M scan registers lastService ∧
        OrdinaryMessageCodec.acceptDown (codecParams p rate.eta)
          (acceptedStart before) (t.val + 1) M ∧ after.lastDown = some M := by
  classical
  unfold ReferenceDownReception.referenceDownCut at h
  split at h <;> rename_i hselected
  · split at h <;> rename_i hstatus
    · split at h <;> rename_i hregisters
      · split at h <;> rename_i hbatch
        · split at h <;> rename_i hbuffer
          · dsimp only at h
            split at h <;> rename_i hmatches
            · dsimp only at h
              split at h
              next hparsed =>
                simp only [consumeDownResult, Except.ok.injEq] at h
                subst after
                exact Or.inl ⟨rfl, rfl⟩
              next M hparsed =>
                split at h <;> rename_i haccepted
                · split at h
                  next failure hchecked => cases h
                  next recovered hchecked =>
                    simp only [consumeDownResult, Except.ok.injEq] at h
                    subst after
                    refine Or.inr ⟨(ActiveFollowerDownAcceptance.currentDecodeStep
                      p i row t observation rate before).2, M,
                      ActiveFollowerDownAcceptance.acceptedCutoffScan p rate M t
                        (ActiveFollowerDownAcceptance.acceptedDownStartLE p rate M t before haccepted) row,
                      recovered.registers, recovered.lastService, ?_, haccepted, rfl⟩
                    simp only [ReferenceDownReception.referenceDownCut, dite_eq_left hselected,
                      dite_eq_left hstatus, dite_eq_left hregisters, dite_eq_left hbatch, dite_eq_left hbuffer,
                      dite_eq_left hmatches, hparsed, dite_eq_left haccepted, hchecked]
                · simp only [consumeDownResult, Except.ok.injEq] at h
                  subst after
                  exact Or.inl ⟨rfl, rfl⟩
            · simp only [consumeDownResult, Except.ok.injEq] at h
              subst after
              exact Or.inl ⟨rfl, rfl⟩
          · cases h
        · cases h
      · cases h
    · simp only [consumeDownResult, Except.ok.injEq] at h
      subst after
      exact Or.inl ⟨rfl, rfl⟩
  · simp only [consumeDownResult, Except.ok.injEq] at h
    subst after
    exact Or.inl ⟨rfl, rfl⟩

/-- Ordinary retained output produces both successful local calls; they are
conclusions of inversion, not additional successful-history inputs. -/
theorem finishFollower_ordinary_inversion
    (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (prepared : PreparedRound p rate) (observation : Observation p)
    (next : ReferencePrelaunchFollower.State p rate.eta)
    (nextMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hout : (ReferenceActivePhysicalStep.finishFollower view prepared observation).configuration =
      .ordinary next nextMemory) :
    ∃ choice memory post,
      prepared.configuration = .ordinary choice memory ∧
      (ReferenceActivePhysicalStep.recordFollower view prepared.follower prepared.row
        prepared.activation prepared.time prepared.active prepared.arm observation choice).result =
          .ok post ∧
      releaseAndFinish rate prepared.follower prepared.row prepared.time observation
        choice memory post = .ok (next, nextMemory) ∧
      (ReferenceActivePhysicalStep.finishFollower view prepared observation).downInput =
        (ReferenceActivePhysicalStep.recordFollower view prepared.follower prepared.row
          prepared.activation prepared.time prepared.active prepared.arm observation choice).downInput ∧
      (ReferenceActivePhysicalStep.finishFollower view prepared observation).down =
        (ReferenceActivePhysicalStep.recordFollower view prepared.follower prepared.row
          prepared.activation prepared.time prepared.active prepared.arm observation choice).down := by
  cases hc : prepared.configuration with
  | dagger => simp only [ReferenceActivePhysicalStep.finishFollower, hc] at hout; cases hout
  | ordinary choice memory =>
    cases hr : (ReferenceActivePhysicalStep.recordFollower view prepared.follower prepared.row
        prepared.activation prepared.time prepared.active prepared.arm observation choice).result with
    | error reason => simp only [ReferenceActivePhysicalStep.finishFollower, hc, hr] at hout; cases hout
    | ok post =>
      cases hf : releaseAndFinish rate prepared.follower prepared.row prepared.time
          observation choice memory post with
      | error reason =>
        simp only [ReferenceActivePhysicalStep.finishFollower, hc, hr, hf] at hout
        cases hout
      | ok pair =>
        rcases pair with ⟨out, outMemory⟩
        simp only [ReferenceActivePhysicalStep.finishFollower, hc, hr, hf,
          LocalConfiguration.ordinary.injEq] at hout
        rcases hout with ⟨rfl, rfl⟩
        exact ⟨choice, memory, post, rfl, hr, hf,
          by simp only [ReferenceActivePhysicalStep.finishFollower, hc, hr, hf],
          by simp only [ReferenceActivePhysicalStep.finishFollower, hc, hr, hf]⟩

/-- Release changes only status; finishing changes only proposal memory.
An unoccupied choice cannot be released by the saved-choice test. -/
theorem releaseAndFinish_frame
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (t : Fin p.T) (observation : Observation p)
    (choice post next : ReferencePrelaunchFollower.State p rate.eta)
    (memory nextMemory : ActiveFollowerLifecycle.LocalMemory p)
    (h : releaseAndFinish rate i row t observation choice memory post =
      .ok (next, nextMemory)) :
    reply next = reply post ∧
      (choice.status = .unoccupied → next.status = post.status) := by
  classical
  unfold releaseAndFinish at h
  cases hr : ActiveFollowerLifecycle.releaseAfterService rate.eta i t
      (ActiveFollowerLifecycle.publicRowOfCompleteRow row t) observation choice post with
  | error reason => simp only [hr] at h; cases h
  | ok released =>
    have hf : ActiveFollowerLifecycle.finishRound rate.eta t row released memory =
        .ok (next, nextMemory) := by
      cases he : ActiveFollowerLifecycle.finishRound rate.eta t row released memory with
      | error reason => simp only [hr, he] at h; cases h
      | ok pair =>
        have hp : pair = (next, nextMemory) := by simpa only [hr, he, Except.ok.injEq] using h
        exact congrArg Except.ok hp
    have heq := ActiveFollowerLifecycle.finishRound_frame rate.eta t row released next
      memory nextMemory hf
    subst next
    constructor
    · unfold ActiveFollowerLifecycle.releaseAfterService at hr
      split at hr
      · split at hr
        · split at hr
          · cases hr
          · split at hr
            · split at hr
              · dsimp only at hr
                split at hr <;> rename_i htest
                all_goals
                  split at hr
                  · simpa only [reply] using congrArg reply (Except.ok.inj hr).symm
                  · cases hr
              · cases hr
            · cases hr
        · cases hr
      · exact congrArg reply (Except.ok.inj hr).symm
    · intro hu
      rw [ActiveFollowerLifecycle.releaseAfterService_unoccupied rate.eta i t
        (ActiveFollowerLifecycle.publicRowOfCompleteRow row t) observation choice post hu] at hr
      exact congrArg ReferencePrelaunchFollower.State.status (Except.ok.inj hr).symm

/-- Successful PREPARE exposes its actual input and start-round frame. -/
theorem prepare_ordinary_inversion
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (activation : Activation p) (t : Fin p.T) (active : activation.val ≤ t.val + 1)
    (input : LocalConfiguration p rate)
    (choice : ReferencePrelaunchFollower.State p rate.eta)
    (choiceMemory : ActiveFollowerLifecycle.LocalMemory p)
    (h : (DeclaredFollowerLocalRound.prepare rate i row activation t active input).configuration =
      .ordinary choice choiceMemory) :
    ∃ before memory, input = .ordinary before memory ∧
      ActiveFollowerLifecycle.startRound rate.eta t before memory = .ok (choice, choiceMemory) ∧
      reply choice = reply before ∧
      (before.status = .unoccupied → choice.status = .unoccupied) := by
  classical
  cases input with
  | dagger => simp only [DeclaredFollowerLocalRound.prepare] at h; cases h
  | ordinary before memory =>
    have hs : ActiveFollowerLifecycle.startRound rate.eta t before memory =
        .ok (choice, choiceMemory) := by
      cases he : ActiveFollowerLifecycle.startRound rate.eta t before memory with
      | error reason => simp only [DeclaredFollowerLocalRound.prepare, he] at h; cases h
      | ok pair =>
        rcases pair with ⟨out, outMemory⟩
        cases ho : ActiveFollowerQueueOperation.checkedUpOffer rate.eta i row activation t out with
        | failure => simp only [DeclaredFollowerLocalRound.prepare, he, ho] at h; cases h
        | noOffer =>
          cases ha : ActiveFollowerArmChoice.followerArmChoice out row t i none <;>
            simp only [DeclaredFollowerLocalRound.prepare, he, ho, ha,
              LocalConfiguration.ordinary.injEq] at h
          · cases h
          · rcases h with ⟨rfl, rfl⟩; rfl
        | offer offered =>
          cases ha : ActiveFollowerArmChoice.followerArmChoice out row t i (some offered) <;>
            simp only [DeclaredFollowerLocalRound.prepare, he, ho, ha,
              LocalConfiguration.ordinary.injEq] at h
          · cases h
          · rcases h with ⟨rfl, rfl⟩; rfl
    have hframe := ActiveFollowerLifecycle.startRound_frame rate.eta t before choice
      memory choiceMemory hs
    refine ⟨before, memory, rfl, hs, ?_, ?_⟩
    · simp only [reply, hframe.1, hframe.2.1, hframe.2.2.1, hframe.2.2.2.1]
    · intro hu
      unfold ActiveFollowerLifecycle.startRound at hs
      cases hd : ActiveFollowerLifecycle.interruptionDecision rate.eta t before memory with
      | error reason => simp [hd] at hs
      | ok interrupted =>
        simp [hd] at hs
        rw [← hs.1]
        cases interrupted <;> simp only [Bool.false_eq_true, ite_false, ite_true, hu]

/-- A successful first observation stage either keeps the DOWN register
(and all reply fields if unoccupied), or retains an actually applied accepted
filtered DOWN. No matching-raw assumption is supplied. -/
theorem recordFollower_ordinary_inversion
    (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (activation : Activation p) (t : Fin p.T) (active : activation.val ≤ t.val + 1)
    (arm : Fin p.K) (observation : Observation p)
    (choice post : ReferencePrelaunchFollower.State p rate.eta)
    (h : (ReferenceActivePhysicalStep.recordFollower view i row activation t active arm
      observation choice).result = .ok post) :
    (post.lastDown = choice.lastDown ∧
      (choice.status = .unoccupied → reply post = reply choice ∧ post.status = .unoccupied)) ∨
    ∃ logged cut raw M scan registers lastService,
      (ReferenceActivePhysicalStep.recordFollower view i row activation t active arm
        observation choice).downInput = some logged ∧
      (ReferenceActivePhysicalStep.recordFollower view i row activation t active arm
        observation choice).down = some cut ∧
      cut = ReferenceDownReception.referenceDownCut p view i row t observation rate logged ∧
      cut.outcome = .accepted logged post raw M scan registers lastService ∧
      acceptedStart choice < M.val.sigma ∧ post.lastDown = some M := by
  classical
  by_cases hu : choice.status = .unoccupied
  · cases hl : ActiveFollowerLogging.checkedLogging i row activation t (arm, observation) choice with
    | error reason => simp only [ReferenceActivePhysicalStep.recordFollower, dite_eq_left hu, hl] at h; cases h
    | ok logged =>
      have hc : consumeDownResult rate
          (ReferenceDownReception.referenceDownCut p view i row t observation rate logged).outcome =
            .ok post := by
        simpa only [ReferenceActivePhysicalStep.recordFollower, dite_eq_left hu, hl] using h
      have hf := ActiveFollowerLogging.checkedLogging_success_frame i row activation t
        (arm, observation) choice logged hl
      have hreply : reply logged = reply choice := by
        simp only [reply, hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1]
      rcases referenceDownCut_ordinary_inversion view i row t observation logged post hc with
        hframe | ⟨raw, M, scan, registers, lastService, hcut, ha, hlast⟩
      · have hr := hframe.1.trans hreply
        exact Or.inl ⟨congrArg Prod.fst hr, fun _ =>
          ⟨hr, hframe.2.trans (hf.2.2.2.2.1.trans hu)⟩⟩
      · refine Or.inr ⟨logged, _, raw, M, scan, registers, lastService, ?_, ?_, rfl,
          hcut, ?_, hlast⟩
        · simp only [ReferenceActivePhysicalStep.recordFollower, dite_eq_left hu, hl]
        · simp only [ReferenceActivePhysicalStep.recordFollower, dite_eq_left hu, hl]
        · rw [← acceptedStart_eq_of_reply_eq hreply]
          exact ha.1
  · have hc : recordOrServiceThenDown rate i row activation t active arm observation choice =
        .ok post := by
      simpa only [ReferenceActivePhysicalStep.recordFollower, dite_eq_right hu] using h
    rw [recordOrServiceThenDown, dite_eq_right hu] at hc
    cases hs : ActiveFollowerQueueOperation.checkedService rate.eta rate.sourceCap rate.n
        rate.n_scale i row activation t observation choice with
    | failure => simp only [hs] at hc; cases hc
    | success result =>
      simp only [hs, Except.ok.injEq] at hc
      subst post
      refine Or.inl ⟨?_, fun hstatus => (hu hstatus).elim⟩
      rw [result.queueUpdate]
      unfold ActiveFollowerQueueOperation.serviceOutput
      split <;> rfl

/-- An applied DOWN is an accepted outcome in this actual round's retained
filtered diagnostic, not a parsed candidate or a successful raw comparison. -/
def appliedDown (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1)) (sigma : ℕ) : Prop :=
  ∃ logged cut after raw M scan registers lastService,
    (record.output.followers i).downInput = some logged ∧
    (record.output.followers i).down = some cut ∧
    cut.outcome = ActiveFollowerDownAcceptance.LocalDownResult.accepted
      logged after raw M scan registers lastService ∧ M.val.sigma = sigma

/-- Ordinary output of one actual record yields the actual ordinary CHOICE
state, monotonicity, the unoccupied frame, and a retained acceptance witness
for every strict change. All first-stage and finish successes are derived. -/
theorem record_choice_chronology
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1)) (next : ReferencePrelaunchFollower.State p rate.eta)
    (nextMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hout : record.output.next.followers i = .ordinary next nextMemory) :
    ∃ choice memory,
      (actualChoice record i).configuration = .ordinary choice memory ∧
      acceptedStart choice ≤ acceptedStart next ∧
      (choice.status = .unoccupied → acceptedStart choice = acceptedStart next →
        next.status = .unoccupied ∧ reply next = reply choice) ∧
      (acceptedStart choice ≠ acceptedStart next → appliedDown record i (acceptedStart next)) := by
  rcases record with ⟨input, output, ho⟩
  cases ho
  change (ReferenceActivePhysicalStep.finishFollower _ _ _).configuration = _ at hout
  obtain ⟨choice, memory, post, hc, hr, hf, hdi, hd⟩ :=
    finishFollower_ordinary_inversion _ _ _ next nextMemory hout
  have hframe := releaseAndFinish_frame _ _ _ _ choice post next memory nextMemory hf
  have hstart := acceptedStart_eq_of_reply_eq hframe.1
  refine ⟨choice, memory, hc, ?_, ?_, ?_⟩
  all_goals
    have hinv := recordFollower_ordinary_inversion _ _ _ _ _ _ _ _ choice post hr
  · rcases hinv with ⟨hlast, _⟩ | ⟨logged, cut, raw, M, scan, registers, lastService,
        _, _, _, _, hlt, hlast⟩
    · have he : acceptedStart post = acceptedStart choice := by simp only [acceptedStart, hlast]
      exact Nat.le_of_eq (he.symm.trans hstart.symm)
    · have hp : acceptedStart post = M.val.sigma := by simp only [acceptedStart, hlast]
      exact (Nat.le_of_lt hlt).trans_eq (hp.symm.trans hstart.symm)
  · intro hu heq
    rcases hinv with ⟨_, hkeep⟩ | ⟨logged, cut, raw, M, scan, registers, lastService,
        _, _, _, _, hlt, hlast⟩
    · obtain ⟨hreply, hstatus⟩ := hkeep hu
      exact ⟨(hframe.2 hu).trans hstatus, hframe.1.trans hreply⟩
    · have he : acceptedStart next = M.val.sigma := by
        rw [hstart, acceptedStart, hlast]
      omega
  · intro hne
    rcases hinv with ⟨hlast, _⟩ | ⟨logged, cut, raw, M, scan, registers, lastService,
        hlogged, hcut, _, houtcome, _, hlast⟩
    · have he : acceptedStart post = acceptedStart choice := by simp only [acceptedStart, hlast]
      exact (hne (he.symm.trans hstart.symm)).elim
    · refine ⟨logged, cut, post, raw, M, scan, registers, lastService, ?_, ?_, houtcome, ?_⟩
      · exact hdi.trans hlogged
      · exact hd.trans hcut
      · rw [hstart, acceptedStart, hlast]

/-- The frame from physical input to CHOICE is derived from PREPARE itself.
An ordinary CHOICE excludes an earlier preparation failure or dagger. -/
theorem record_input_to_choice
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1)) (choice : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hc : (actualChoice record i).configuration = .ordinary choice memory) :
    ∃ before beforeMemory, record.input.state.followers i = .ordinary before beforeMemory ∧
      reply choice = reply before ∧
      (before.status = .unoccupied → choice.status = .unoccupied) := by
  have hp : actualChoice record i = DeclaredFollowerLocalRound.prepare rate i
      record.input.row (record.input.state.activations i) record.input.time
      (record.input.active i) (record.input.state.followers i) := by
    exact record.output.preparation.followers.followers_eq i
  rw [hp] at hc
  obtain ⟨before, beforeMemory, hi, _, hr, hu⟩ := prepare_ordinary_inversion
    i record.input.row (record.input.state.activations i) record.input.time
    (record.input.active i) (record.input.state.followers i) choice memory hc
  exact ⟨before, beforeMemory, hi, hr, hu⟩

/-- Complete actual input-to-output chronology, including the conditional
unoccupied frame. This covers enabled occupied service, even at zero arrival;
it never invokes service for an unoccupied CHOICE state. -/
theorem record_ordinary_chronology
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1)) (next : ReferencePrelaunchFollower.State p rate.eta)
    (nextMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hout : record.output.next.followers i = .ordinary next nextMemory) :
    ∃ before memory, record.input.state.followers i = .ordinary before memory ∧
      acceptedStart before ≤ acceptedStart next ∧
      (before.status = .unoccupied → acceptedStart before = acceptedStart next →
        next.status = .unoccupied ∧ reply next = reply before) ∧
      (acceptedStart before ≠ acceptedStart next → appliedDown record i (acceptedStart next)) := by
  obtain ⟨choice, choiceMemory, hc, hm, hf, ha⟩ := record_choice_chronology record i next nextMemory hout
  obtain ⟨before, memory, hi, hr, hu⟩ := record_input_to_choice record i choice choiceMemory hc
  have hs := acceptedStart_eq_of_reply_eq hr
  refine ⟨before, memory, hi, ?_, ?_, ?_⟩
  · exact hs ▸ hm
  · intro hstatus heq
    obtain ⟨hstatus', hreply⟩ := hf (hu hstatus) (hs.trans heq)
    exact ⟨hstatus', hreply.trans hr⟩
  · intro hne
    exact ha (fun heq => hne (hs.symm.trans heq))

/-- An accepted filtered diagnostic itself supplies the strict acceptance
test and installed record, independently of the ordinary-result inversion. -/
theorem referenceDownCut_accepted
    (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (t : Fin p.T) (observation : Observation p)
    (before after : ReferencePrelaunchFollower.State p rate.eta)
    (raw : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p)))
    (M : OrdinaryMessageCodec.DownRecord (codecParams p rate.eta))
    (scan : FollowerCutoffScan.ScanResult p.T) (registers : ℕ × ℕ) (lastService : ℕ)
    (h : (ReferenceDownReception.referenceDownCut p view i row t observation rate before).outcome =
      .accepted before after raw M scan registers lastService) :
    OrdinaryMessageCodec.acceptDown (codecParams p rate.eta)
      (acceptedStart before) (t.val + 1) M ∧ after.lastDown = some M := by
  classical
  unfold ReferenceDownReception.referenceDownCut at h
  split at h
  · split at h
    · split at h
      · split at h
        · split at h
          · dsimp only at h
            split at h
            · dsimp only at h
              split at h
              · cases h
              · split at h
                next ha =>
                  split at h
                  · cases h
                  · cases h
                    exact ⟨ha, rfl⟩
                · cases h
            · cases h
          · cases h
        · cases h
      · cases h
    · cases h
  · cases h

/-- Conversely, every retained applied acceptance strictly increases the
start from this actual ordinary CHOICE to its actual ordinary successor. -/
theorem record_appliedDown_strict
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1)) (sigma : ℕ) (ha : appliedDown record i sigma)
    (next : ReferencePrelaunchFollower.State p rate.eta)
    (nextMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hout : record.output.next.followers i = .ordinary next nextMemory) :
    ∃ choice memory, (actualChoice record i).configuration = .ordinary choice memory ∧
      acceptedStart choice < sigma ∧ acceptedStart next = sigma := by
  classical
  rcases record with ⟨input, output, ho⟩
  cases ho
  change (ReferenceActivePhysicalStep.finishFollower _ _ _).configuration = _ at hout
  obtain ⟨choice, memory, post, hc, hr, hf, hdi, hd⟩ :=
    finishFollower_ordinary_inversion _ _ _ next nextMemory hout
  obtain ⟨logged, cut, after, raw, M, scan, registers, lastService, hi, hcut, ho, hsigma⟩ := ha
  have hri := hdi.symm.trans hi
  have hrd := hd.symm.trans hcut
  let prepared := (ReferenceActivePhysicalStep.prepare input).followers.followers i
  let observation := (ReferenceActivePhysicalStep.prepare input).feedback.observations
    (PublicDiscreteDraws.followerPlayer p.two_le_m i)
  by_cases hu : choice.status = .unoccupied
  · cases hl : ActiveFollowerLogging.checkedLogging prepared.follower prepared.row
        prepared.activation prepared.time (prepared.arm, observation) choice with
    | error reason =>
      dsimp only [prepared, observation] at hl
      simp only [ReferenceActivePhysicalStep.recordFollower, dite_eq_left hu, hl] at hri
      cases hri
    | ok logged' =>
      dsimp only [prepared, observation] at hl
      simp only [ReferenceActivePhysicalStep.recordFollower, dite_eq_left hu, hl] at hri hrd hr
      have hlog : logged' = logged := Option.some.inj hri
      subst logged'
      have hce := Option.some.inj hrd
      subst cut
      have haccepted := referenceDownCut_accepted _ _ _ _ _ logged after raw M scan registers lastService ho
      rw [ho] at hr
      have hp : after = post := Except.ok.inj hr
      subst after
      have hframe := releaseAndFinish_frame _ _ _ _ choice post next memory nextMemory hf
      have hlogging := ActiveFollowerLogging.checkedLogging_success_frame _ _ _ _ _ choice logged hl
      have hstart : acceptedStart logged = acceptedStart choice := by
        simp only [acceptedStart, hlogging.1]
      refine ⟨choice, memory, hc, ?_, ?_⟩
      · rw [← hsigma, ← hstart]
        exact haccepted.1.1
      · rw [← hsigma, acceptedStart_eq_of_reply_eq hframe.1]
        simp only [acceptedStart, haccepted.2]
  · simp only [ReferenceActivePhysicalStep.recordFollower, dite_eq_right hu] at hri
    cases hri

open ReferenceActivePhysicalHorizon

/-- Backward inversion along the actual connected chain: an ordinary later
endpoint excludes all earlier dagger paths. The change witness is an actual
retained filtered acceptance inside this same interval. -/
theorem connected_ordinary_chronology
    {initial final : ReferenceActivePhysicalStep.State p rate}
    {records : List (RoundRecord (p := p) (rate := rate))}
    (chain : Connected initial records final) (i : Fin (p.m - 1))
    (last : ReferencePrelaunchFollower.State p rate.eta)
    (lastMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hout : final.followers i = .ordinary last lastMemory) :
    ∃ first memory, initial.followers i = .ordinary first memory ∧
      acceptedStart first ≤ acceptedStart last ∧
      (first.status = .unoccupied → acceptedStart first = acceptedStart last →
        last.status = .unoccupied ∧ reply last = reply first) ∧
      (acceptedStart first ≠ acceptedStart last →
        ∃ record ∈ records, ∃ sigma, appliedDown record i sigma ∧
          acceptedStart first < sigma ∧ sigma ≤ acceptedStart last) := by
  induction records generalizing initial final with
  | nil =>
    change final = initial at chain
    subst final
    exact ⟨last, lastMemory, hout, le_rfl, fun hu _ => ⟨hu, rfl⟩,
      fun hne => (hne rfl).elim⟩
  | cons record rest ih =>
    obtain ⟨hpre, hrest⟩ := chain
    obtain ⟨mid, midMemory, hmid, hml, hfreeze, hwitness⟩ := ih hrest hout
    obtain ⟨first, memory, hfirst, hfm, hkeep, haccept⟩ :=
      record_ordinary_chronology record i mid midMemory hmid
    refine ⟨first, memory, hpre ▸ hfirst, hfm.trans hml, ?_, ?_⟩
    · intro hu heq
      have hem : acceptedStart first = acceptedStart mid := by omega
      have hel : acceptedStart mid = acceptedStart last := by omega
      obtain ⟨hmu, hmr⟩ := hkeep hu hem
      obtain ⟨hlu, hlr⟩ := hfreeze hmu hel
      exact ⟨hlu, hlr.trans hmr⟩
    · intro hne
      by_cases hem : acceptedStart first = acceptedStart mid
      · obtain ⟨r, hr, sigma, ha, hlo, hhi⟩ := hwitness (fun he => hne (hem.trans he))
        exact ⟨r, List.mem_cons_of_mem _ hr, sigma, ha, hem ▸ hlo, hhi⟩
      · exact ⟨record, List.mem_cons_self, acceptedStart mid, haccept hem,
          by omega, hml⟩

/-- The actual prefix before an indexed record ends at that record's input.
This is a structural consequence of `Connected`, with no supplied trace law. -/
theorem connected_take_to_input
    {initial final : ReferenceActivePhysicalStep.State p rate}
    {records : List (RoundRecord (p := p) (rate := rate))}
    (chain : Connected initial records final) (n : ℕ) (hn : n < records.length) :
    Connected initial (records.take n) records[n].input.state := by
  induction records generalizing initial n with
  | nil => simp only [List.length_nil] at hn; omega
  | cons record rest ih =>
    obtain ⟨hpre, hrest⟩ := chain
    cases n with
    | zero => exact hpre
    | succ n =>
      exact ⟨hpre, ih hrest n (by simp only [List.length_cons] at hn; omega)⟩

/-- The actual suffix begins at the retained input of its first record. -/
theorem connected_drop_from_input
    {initial final : ReferenceActivePhysicalStep.State p rate}
    {records : List (RoundRecord (p := p) (rate := rate))}
    (chain : Connected initial records final) (n : ℕ) (hn : n < records.length) :
    Connected records[n].input.state (records.drop n) final := by
  induction records generalizing initial n with
  | nil => simp only [List.length_nil] at hn; omega
  | cons record rest ih =>
    obtain ⟨_, hrest⟩ := chain
    cases n with
    | zero => exact ⟨rfl, hrest⟩
    | succ n => exact ih hrest n (by simp only [List.length_cons] at hn; omega)

/-- The suffix after an actual record begins at its literal successor. -/
theorem connected_drop_from_output
    {initial final : ReferenceActivePhysicalStep.State p rate}
    {records : List (RoundRecord (p := p) (rate := rate))}
    (chain : Connected initial records final) (n : ℕ) (hn : n < records.length) :
    Connected records[n].output.next (records.drop (n + 1)) final := by
  have hs := connected_drop_from_input chain n hn
  rw [List.drop_eq_getElem_cons hn] at hs
  exact hs.2

/-- An ordinary final endpoint produces an ordinary output at every earlier
actual record, with its start bounded by the final start. -/
theorem connected_output_chronology
    {initial final : ReferenceActivePhysicalStep.State p rate}
    {records : List (RoundRecord (p := p) (rate := rate))}
    (chain : Connected initial records final) (i : Fin (p.m - 1))
    (last : ReferencePrelaunchFollower.State p rate.eta)
    (lastMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hf : final.followers i = .ordinary last lastMemory)
    (n : ℕ) (hn : n < records.length) :
    ∃ next memory, records[n].output.next.followers i = .ordinary next memory ∧
      acceptedStart next ≤ acceptedStart last := by
  induction records generalizing initial n with
  | nil => simp only [List.length_nil] at hn; omega
  | cons record rest ih =>
    obtain ⟨_, hrest⟩ := chain
    cases n with
    | zero =>
      obtain ⟨s, memory, hs, hm, _, _⟩ := connected_ordinary_chronology hrest i last lastMemory hf
      exact ⟨s, memory, hs, hm⟩
    | succ n => exact ih hrest n (by simp only [List.length_cons] at hn; omega)

/-- Chronology between actual CHOICE configurations in an indexed connected
chain. Equality of starts is the only interval selector for the frame. -/
theorem connected_choice_chronology
    {initial final : ReferenceActivePhysicalStep.State p rate}
    {records : List (RoundRecord (p := p) (rate := rate))}
    (chain : Connected initial records final) (i : Fin (p.m - 1))
    (a b : ℕ) (ha : a < records.length) (hb : b < records.length) (hab : a ≤ b)
    (left right : ReferencePrelaunchFollower.State p rate.eta)
    (leftMemory rightMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hl : (actualChoice records[a] i).configuration = .ordinary left leftMemory)
    (hr : (actualChoice records[b] i).configuration = .ordinary right rightMemory) :
    acceptedStart left ≤ acceptedStart right ∧
      (left.status = .unoccupied → acceptedStart left = acceptedStart right →
        right.status = .unoccupied ∧ reply right = reply left) ∧
      (acceptedStart left ≠ acceptedStart right →
        ∃ n : Fin records.length, a ≤ n.val ∧ n.val < b ∧ ∃ sigma,
          appliedDown records[n.val] i sigma ∧ acceptedStart left < sigma ∧
            sigma ≤ acceptedStart right) := by
  induction records generalizing initial a b with
  | nil => simp only [List.length_nil] at ha; omega
  | cons record rest ih =>
    obtain ⟨hpre, hrest⟩ := chain
    cases a with
    | succ a =>
      cases b with
      | zero => omega
      | succ b =>
        obtain ⟨hm, hf, hw⟩ := ih hrest a b (by simp only [List.length_cons] at ha; omega)
          (by simp only [List.length_cons] at hb; omega) (by omega) hl hr
        refine ⟨hm, hf, ?_⟩
        intro hne
        obtain ⟨n, hlo, hhi, sigma, hw, hs, ht⟩ := hw hne
        exact ⟨⟨n.val + 1, by simp only [List.length_cons]; omega⟩, by dsimp only; omega, by dsimp only; omega, sigma, hw, hs, ht⟩
    | zero =>
      cases b with
      | zero =>
        have he : left = right := (LocalConfiguration.ordinary.inj (hl.symm.trans hr)).1
        subst right
        exact ⟨le_rfl, fun hu _ => ⟨hu, rfl⟩, fun hne => (hne rfl).elim⟩
      | succ b =>
        have hblt : b < rest.length := by simp only [List.length_cons] at hb; omega
        obtain ⟨before, beforeMemory, hbefore, hreply, hstatus⟩ :=
          record_input_to_choice rest[b] i right rightMemory hr
        have hbeforeStart := acceptedStart_eq_of_reply_eq hreply
        have hprefix := connected_take_to_input hrest b (by simp only [List.length_cons] at hb; omega)
        obtain ⟨mid, midMemory, hmid, hmb, hfreeze, hwitness⟩ :=
          connected_ordinary_chronology hprefix i before beforeMemory hbefore
        obtain ⟨choice, choiceMemory, hc, hlm, hkeep, haccept⟩ :=
          record_choice_chronology record i mid midMemory hmid
        have he : choice = left := (LocalConfiguration.ordinary.inj (hc.symm.trans hl)).1
        subst choice
        have hm : acceptedStart left ≤ acceptedStart right := by omega
        refine ⟨hm, ?_, ?_⟩
        · intro hu heq
          have hem : acceptedStart left = acceptedStart mid := by omega
          have heb : acceptedStart mid = acceptedStart before := by omega
          obtain ⟨hmu, hmr⟩ := hkeep hu hem
          obtain ⟨hbu, hbr⟩ := hfreeze hmu heb
          exact ⟨hstatus hbu, hreply.trans (hbr.trans hmr)⟩
        · intro hne
          by_cases hem : acceptedStart left = acceptedStart mid
          · obtain ⟨r, hrmem, sigma, hw, hs, ht⟩ := hwitness (by omega)
            obtain ⟨n, hn, helem⟩ := List.getElem_of_mem hrmem
            have hnrest : n < rest.length := by
              have hnlen : n < (rest.take b).length := hn
              simp only [List.length_take] at hnlen
              omega
            have hnb : n < b := by simp only [List.length_take] at hn; omega
            have hrn : rest[n] = r := by simpa only [List.getElem_take] using helem
            refine ⟨⟨n + 1, by simp only [List.length_cons]; omega⟩, by dsimp only; omega, by dsimp only; omega, sigma, ?_, ?_, ?_⟩
            · simpa only [List.getElem_cons_succ, hrn] using hw
            · omega
            · omega
          · exact ⟨⟨0, by simp only [List.length_cons]; omega⟩, le_rfl, by dsimp only; omega, acceptedStart mid, haccept hem, by omega, by omega⟩

section Run

variable (initial : ReferenceActivePhysicalStep.State p rate)
variable (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
variable (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
variable (start count : ℕ) (hspan : start + count ≤ p.T)
variable (hmode : allActiveAtStart initial start)

/-- Ordered actual ordinary CHOICE endpoints have nondecreasing starts.
Every change has an intervening actual filtered acceptance, at an index in
the half-open interval between the selected endpoints. -/
theorem run_acceptedStart_mono
    (i : Fin (p.m - 1))
    (a b : Fin (run initial rows selected rewards start count hspan hmode).records.length)
    (hab : a.val ≤ b.val)
    (left right : ReferencePrelaunchFollower.State p rate.eta)
    (leftMemory rightMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hl : (actualChoice (run initial rows selected rewards start count hspan hmode).records[a.val] i).configuration =
      .ordinary left leftMemory)
    (hr : (actualChoice (run initial rows selected rewards start count hspan hmode).records[b.val] i).configuration =
      .ordinary right rightMemory) :
    acceptedStart left ≤ acceptedStart right ∧
      (acceptedStart left ≠ acceptedStart right →
        ∃ n : Fin (run initial rows selected rewards start count hspan hmode).records.length,
          a.val ≤ n.val ∧ n.val < b.val ∧ ∃ sigma,
            appliedDown (run initial rows selected rewards start count hspan hmode).records[n.val] i sigma ∧
              acceptedStart left < sigma ∧ sigma ≤ acceptedStart right) := by
  have h := connected_choice_chronology (run_connected initial rows selected rewards start count hspan hmode)
    i a.val b.val a.isLt b.isLt hab left right leftMemory rightMemory hl hr
  exact ⟨h.1, h.2.2⟩

/-- An actual unoccupied CHOICE remains unoccupied with the whole last DOWN
record and all three reply registers fixed up to an ordinary CHOICE with the
same accepted start. No no-service or fixed-word history is an input. -/
theorem run_unoccupied_reply_const
    (i : Fin (p.m - 1))
    (a b : Fin (run initial rows selected rewards start count hspan hmode).records.length)
    (hab : a.val ≤ b.val)
    (left right : ReferencePrelaunchFollower.State p rate.eta)
    (leftMemory rightMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hl : (actualChoice (run initial rows selected rewards start count hspan hmode).records[a.val] i).configuration =
      .ordinary left leftMemory)
    (hr : (actualChoice (run initial rows selected rewards start count hspan hmode).records[b.val] i).configuration =
      .ordinary right rightMemory)
    (hu : left.status = .unoccupied) (heq : acceptedStart left = acceptedStart right) :
    right.status = .unoccupied ∧ right.lastDown = left.lastDown ∧
      right.S = left.S ∧ right.delta = left.delta ∧ right.backlog = left.backlog := by
  obtain ⟨hstatus, hreply⟩ :=
    (connected_choice_chronology (run_connected initial rows selected rewards start count hspan hmode)
      i a.val b.val a.isLt b.isLt hab left right leftMemory rightMemory hl hr).2.1 hu heq
  exact ⟨hstatus, (Prod.mk.inj hreply).1, (Prod.mk.inj (Prod.mk.inj hreply).2).1,
    (Prod.mk.inj (Prod.mk.inj (Prod.mk.inj hreply).2).2).1,
    (Prod.mk.inj (Prod.mk.inj (Prod.mk.inj hreply).2).2).2⟩

/-- Equal ordinary endpoint starts exclude every actually applied DOWN
between those choices, even without assuming the earlier state unoccupied. -/
theorem run_no_appliedDown_of_equal_starts
    (i : Fin (p.m - 1))
    (a b : Fin (run initial rows selected rewards start count hspan hmode).records.length)
    (left right : ReferencePrelaunchFollower.State p rate.eta)
    (leftMemory rightMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hl : (actualChoice (run initial rows selected rewards start count hspan hmode).records[a.val] i).configuration =
      .ordinary left leftMemory)
    (hr : (actualChoice (run initial rows selected rewards start count hspan hmode).records[b.val] i).configuration =
      .ordinary right rightMemory)
    (heq : acceptedStart left = acceptedStart right)
    (n : Fin (run initial rows selected rewards start count hspan hmode).records.length)
    (han : a.val ≤ n.val) (hnb : n.val < b.val) (sigma : ℕ) :
    ¬ appliedDown (run initial rows selected rewards start count hspan hmode).records[n.val] i sigma := by
  intro ha
  let execution := run initial rows selected rewards start count hspan hmode
  obtain ⟨before, beforeMemory, hb, hreply, _⟩ := record_input_to_choice _ i right rightMemory hr
  have hstart := acceptedStart_eq_of_reply_eq hreply
  have chain := connected_take_to_input execution.connected b.val b.isLt
  have hn : n.val < (execution.records.take b.val).length := by
    simp only [List.length_take]
    exact lt_min hnb n.isLt
  obtain ⟨next, memory, hout, hbound⟩ := connected_output_chronology
    chain i before beforeMemory hb n.val hn
  have helem := List.getElem_take (xs := execution.records) (j := b.val) (i := n.val) (h := hn)
  rw [helem] at hout
  obtain ⟨choice, choiceMemory, hc, hlt, hnext⟩ :=
    record_appliedDown_strict _ i sigma ha next memory hout
  have hm := (connected_choice_chronology execution.connected i a.val n.val a.isLt n.isLt han
    left choice leftMemory choiceMemory hl hc).1
  omega

/-- Chronological equality of actual offered records and current words, only
at the two successfully checked selected offers. -/
theorem run_up_word_const
    (i : Fin (p.m - 1))
    (a b : Fin (run initial rows selected rewards start count hspan hmode).records.length)
    (hab : a.val ≤ b.val)
    (left right : ReferencePrelaunchFollower.State p rate.eta)
    (leftMemory rightMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hl : (actualChoice (run initial rows selected rewards start count hspan hmode).records[a.val] i).configuration =
      .ordinary left leftMemory)
    (hr : (actualChoice (run initial rows selected rewards start count hspan hmode).records[b.val] i).configuration =
      .ordinary right rightMemory)
    (hu : left.status = .unoccupied) (heq : acceptedStart left = acceptedStart right)
    (leftOffer rightOffer : OrdinaryMessageCodec.UpRecord (codecParams p rate.eta))
    (hlo : ActiveFollowerQueueOperation.checkedUpOffer rate.eta
      (actualChoice (run initial rows selected rewards start count hspan hmode).records[a.val] i).follower
      (actualChoice (run initial rows selected rewards start count hspan hmode).records[a.val] i).row
      (actualChoice (run initial rows selected rewards start count hspan hmode).records[a.val] i).activation
      (actualChoice (run initial rows selected rewards start count hspan hmode).records[a.val] i).time left = .offer leftOffer)
    (hro : ActiveFollowerQueueOperation.checkedUpOffer rate.eta
      (actualChoice (run initial rows selected rewards start count hspan hmode).records[b.val] i).follower
      (actualChoice (run initial rows selected rewards start count hspan hmode).records[b.val] i).row
      (actualChoice (run initial rows selected rewards start count hspan hmode).records[b.val] i).activation
      (actualChoice (run initial rows selected rewards start count hspan hmode).records[b.val] i).time right = .offer rightOffer)
    (hls : ReferenceActivePhysicalStep.upSenderIndex
      (run initial rows selected rewards start count hspan hmode).records[a.val].input = i)
    (hrs : ReferenceActivePhysicalStep.upSenderIndex
      (run initial rows selected rewards start count hspan hmode).records[b.val].input = i) :
    leftOffer = rightOffer ∧
      actualUpExpected (run initial rows selected rewards start count hspan hmode).records[a.val] =
        actualUpExpected (run initial rows selected rewards start count hspan hmode).records[b.val] ∧
      (let l := (run initial rows selected rewards start count hspan hmode).records[a.val]
       let r := (run initial rows selected rewards start count hspan hmode).records[b.val]
       ReferenceUpReception.currentOfferWord rate l.input.row i l.input.time (actualChoice l i)
           (actualChoice_alignment l i).1 (actualChoice_alignment l i).2.1 (actualChoice_alignment l i).2.2 =
         ReferenceUpReception.currentOfferWord rate r.input.row i r.input.time (actualChoice r i)
           (actualChoice_alignment r i).1 (actualChoice_alignment r i).2.1 (actualChoice_alignment r i).2.2) := by
  have hf := run_unoccupied_reply_const initial rows selected rewards start count hspan hmode
    i a b hab left right leftMemory rightMemory hl hr hu heq
  have hregisters : acceptedStart left = acceptedStart right ∧
      left.S = right.S ∧ left.delta = right.delta ∧ left.backlog = right.backlog :=
    ⟨heq, hf.2.2.1.symm, hf.2.2.2.1.symm, hf.2.2.2.2.symm⟩
  have hwords := actualUpExpected_eq_of_same_reply_registers _ _ i hls hrs left right
    leftMemory rightMemory hl hr hregisters leftOffer rightOffer hlo hro
  exact ⟨hwords.1, hwords.2, currentOfferWord_eq_of_same_reply_registers _ _ i left right
    leftMemory rightMemory hl hr hregisters leftOffer rightOffer hlo hro⟩

/-- Input-to-final-prefix form, including the empty and terminal intervals.
An ordinary final state itself supplies every earlier ordinary branch. -/
theorem run_input_final_chronology
    (i : Fin (p.m - 1))
    (first last : ReferencePrelaunchFollower.State p rate.eta)
    (firstMemory lastMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hi : initial.followers i = .ordinary first firstMemory)
    (hf : (run initial rows selected rewards start count hspan hmode).finalState.followers i =
      .ordinary last lastMemory) :
    acceptedStart first ≤ acceptedStart last ∧
      (first.status = .unoccupied → acceptedStart first = acceptedStart last →
        last.status = .unoccupied ∧ reply last = reply first) ∧
      (acceptedStart first ≠ acceptedStart last →
        ∃ record ∈ (run initial rows selected rewards start count hspan hmode).records,
          ∃ sigma, appliedDown record i sigma ∧
            acceptedStart first < sigma ∧ sigma ≤ acceptedStart last) := by
  obtain ⟨s, memory, hs, hm, hkeep, hw⟩ := connected_ordinary_chronology
    (run_connected initial rows selected rewards start count hspan hmode) i last lastMemory hf
  have he : s = first := (LocalConfiguration.ordinary.inj (hs.symm.trans hi)).1
  subst s
  exact ⟨hm, hkeep, hw⟩

/-- The same input-to-CHOICE frame, using the actual prefix before that
choice and its separate PREPARE frame. -/
theorem run_initial_to_choice
    (i : Fin (p.m - 1))
    (a : Fin (run initial rows selected rewards start count hspan hmode).records.length)
    (first last : ReferencePrelaunchFollower.State p rate.eta)
    (firstMemory lastMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hi : initial.followers i = .ordinary first firstMemory)
    (hl : (actualChoice (run initial rows selected rewards start count hspan hmode).records[a.val] i).configuration =
      .ordinary last lastMemory) :
    acceptedStart first ≤ acceptedStart last ∧
      (first.status = .unoccupied → acceptedStart first = acceptedStart last →
        last.status = .unoccupied ∧ reply last = reply first) ∧
      (acceptedStart first ≠ acceptedStart last →
        ∃ record ∈ (run initial rows selected rewards start count hspan hmode).records,
          ∃ sigma, appliedDown record i sigma ∧
            acceptedStart first < sigma ∧ sigma ≤ acceptedStart last) := by
  obtain ⟨before, memory, hb, hr, hu⟩ := record_input_to_choice _ i last lastMemory hl
  have hstart := acceptedStart_eq_of_reply_eq hr
  have chain := connected_take_to_input (run_connected initial rows selected rewards start count hspan hmode)
    a.val a.isLt
  obtain ⟨s, smemory, hs, hm, hkeep, hw⟩ := connected_ordinary_chronology chain i before memory hb
  have he : s = first := (LocalConfiguration.ordinary.inj (hs.symm.trans hi)).1
  subst s
  refine ⟨by omega, ?_, ?_⟩
  · intro hstatus heq
    obtain ⟨hbu, hbr⟩ := hkeep hstatus (by omega)
    exact ⟨hu hbu, hr.trans hbr⟩
  · intro hne
    obtain ⟨record, hrecord, sigma, ha, hlo, hhi⟩ := hw (by omega)
    exact ⟨record, List.mem_of_mem_take hrecord, sigma, ha, hlo, by omega⟩

/-- Ordered ordinary input endpoints of the same computed run. The frame
from input to CHOICE is not silently identified with the input state. -/
theorem run_input_chronology
    (i : Fin (p.m - 1))
    (a b : Fin (run initial rows selected rewards start count hspan hmode).records.length)
    (hab : a.val ≤ b.val)
    (left right : ReferencePrelaunchFollower.State p rate.eta)
    (leftMemory rightMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hl : (run initial rows selected rewards start count hspan hmode).records[a.val].input.state.followers i =
      .ordinary left leftMemory)
    (hr : (run initial rows selected rewards start count hspan hmode).records[b.val].input.state.followers i =
      .ordinary right rightMemory) :
    acceptedStart left ≤ acceptedStart right ∧
      (left.status = .unoccupied → acceptedStart left = acceptedStart right →
        right.status = .unoccupied ∧ reply right = reply left) ∧
      (acceptedStart left ≠ acceptedStart right →
        ∃ record ∈ (run initial rows selected rewards start count hspan hmode).records,
          ∃ sigma, appliedDown record i sigma ∧
            acceptedStart left < sigma ∧ sigma ≤ acceptedStart right) := by
  let execution := run initial rows selected rewards start count hspan hmode
  have chain := connected_drop_from_input execution.connected a.val a.isLt
  have hn : b.val - a.val < (execution.records.drop a.val).length := by
    have hblt : b.val < execution.records.length := b.isLt
    simp only [List.length_drop]
    omega
  have segment := connected_take_to_input chain (b.val - a.val) hn
  have helem : (execution.records.drop a.val)[b.val - a.val] = execution.records[b.val] := by
    simp only [List.getElem_drop, Nat.add_sub_of_le hab]
  rw [helem] at segment
  obtain ⟨s, memory, hs, hm, hkeep, hw⟩ := connected_ordinary_chronology segment i right rightMemory hr
  have he : s = left := (LocalConfiguration.ordinary.inj (hs.symm.trans hl)).1
  subst s
  refine ⟨hm, hkeep, ?_⟩
  intro hne
  obtain ⟨record, hrecord, sigma, ha, hlo, hhi⟩ := hw hne
  exact ⟨record, List.mem_of_mem_drop (List.mem_of_mem_take hrecord), sigma, ha, hlo, hhi⟩

/-- An ordinary CHOICE and the computed final-prefix endpoint. Earlier
dagger paths are excluded by inversion of the actual ordinary final state. -/
theorem run_choice_final_chronology
    (i : Fin (p.m - 1))
    (a : Fin (run initial rows selected rewards start count hspan hmode).records.length)
    (left right : ReferencePrelaunchFollower.State p rate.eta)
    (leftMemory rightMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hl : (actualChoice (run initial rows selected rewards start count hspan hmode).records[a.val] i).configuration =
      .ordinary left leftMemory)
    (hr : (run initial rows selected rewards start count hspan hmode).finalState.followers i =
      .ordinary right rightMemory) :
    acceptedStart left ≤ acceptedStart right ∧
      (left.status = .unoccupied → acceptedStart left = acceptedStart right →
        right.status = .unoccupied ∧ reply right = reply left) ∧
      (acceptedStart left ≠ acceptedStart right →
        ∃ record ∈ (run initial rows selected rewards start count hspan hmode).records,
          ∃ sigma, appliedDown record i sigma ∧
            acceptedStart left < sigma ∧ sigma ≤ acceptedStart right) := by
  let execution := run initial rows selected rewards start count hspan hmode
  have chain := connected_drop_from_output execution.connected a.val a.isLt
  obtain ⟨mid, memory, hm, hmr, hkeep, hw⟩ := connected_ordinary_chronology chain i right rightMemory hr
  obtain ⟨choice, choiceMemory, hc, hcm, hfreeze, ha⟩ :=
    record_choice_chronology execution.records[a.val] i mid memory hm
  have he : choice = left := (LocalConfiguration.ordinary.inj (hc.symm.trans hl)).1
  subst choice
  refine ⟨hcm.trans hmr, ?_, ?_⟩
  · intro hu heq
    have hem : acceptedStart left = acceptedStart mid := by omega
    have her : acceptedStart mid = acceptedStart right := by omega
    obtain ⟨hmu, hml⟩ := hfreeze hu hem
    obtain ⟨hru, hrl⟩ := hkeep hmu her
    exact ⟨hru, hrl.trans hml⟩
  · intro hne
    by_cases hem : acceptedStart left = acceptedStart mid
    · obtain ⟨record, hrecord, sigma, ha, hlo, hhi⟩ := hw (by omega)
      exact ⟨record, List.mem_of_mem_drop hrecord, sigma, ha, by omega, hhi⟩
    · exact ⟨execution.records[a.val], List.getElem_mem a.isLt, acceptedStart mid,
        ha hem, by omega, hmr⟩

/-- Ordered computed prefix boundaries, including the terminal boundary.
The last added record is the literal successor step, so any change is
witnessed in the computed longer prefix itself. -/
theorem run_prefix_final_chronology
    (a : ℕ) (ha : a ≤ count) (i : Fin (p.m - 1))
    (left right : ReferencePrelaunchFollower.State p rate.eta)
    (leftMemory rightMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hl : (run initial rows selected rewards start a (by omega) hmode).finalState.followers i =
      .ordinary left leftMemory)
    (hr : (run initial rows selected rewards start count hspan hmode).finalState.followers i =
      .ordinary right rightMemory) :
    acceptedStart left ≤ acceptedStart right ∧
      (left.status = .unoccupied → acceptedStart left = acceptedStart right →
        right.status = .unoccupied ∧ reply right = reply left) ∧
      (acceptedStart left ≠ acceptedStart right →
        ∃ record ∈ (run initial rows selected rewards start count hspan hmode).records,
          ∃ sigma, appliedDown record i sigma ∧
            acceptedStart left < sigma ∧ sigma ≤ acceptedStart right) := by
  induction count generalizing a right rightMemory with
  | zero =>
    have he : a = 0 := by omega
    subst a
    have hs : left = right := (LocalConfiguration.ordinary.inj (hl.symm.trans hr)).1
    subst right
    exact ⟨le_rfl, fun hu _ => ⟨hu, rfl⟩, fun hne => (hne rfl).elim⟩
  | succ n ih =>
    by_cases he : a = n + 1
    · subst a
      have hs : left = right := (LocalConfiguration.ordinary.inj (hl.symm.trans hr)).1
      subst right
      exact ⟨le_rfl, fun hu _ => ⟨hu, rfl⟩, fun hne => (hne rfl).elim⟩
    · have han : a ≤ n := by omega
      let acc := run initial rows selected rewards start n (by omega) hmode
      let entry : CalendarEntry p start := ⟨start + n, by omega, by omega⟩
      let input := roundInputAt initial rows selected rewards start hmode acc entry
      let record : RoundRecord (p := p) (rate := rate) :=
        ⟨input, ReferenceActivePhysicalStep.step input, rfl⟩
      have hfinal : (run initial rows selected rewards start (n + 1) hspan hmode).finalState =
          record.output.next := by
        rw [run_successor_step]
        rfl
      have hrecords : (run initial rows selected rewards start (n + 1) hspan hmode).records =
          acc.records ++ [record] := by
        rw [run_successor_step]
        rfl
      rw [hfinal] at hr
      obtain ⟨mid, memory, hm, hmr, hkeep, hw⟩ := record_ordinary_chronology record i right rightMemory hr
      have hacc : acc.finalState.followers i = .ordinary mid memory := hm
      obtain ⟨hlm, hfreeze, hwitness⟩ := ih (by omega) a han mid memory hl hacc
      refine ⟨hlm.trans hmr, ?_, ?_⟩
      · intro hu heq
        have hem : acceptedStart left = acceptedStart mid := by omega
        have her : acceptedStart mid = acceptedStart right := by omega
        obtain ⟨hmu, hml⟩ := hfreeze hu hem
        obtain ⟨hru, hrl⟩ := hkeep hmu her
        exact ⟨hru, hrl.trans hml⟩
      · intro hne
        by_cases hem : acceptedStart left = acceptedStart mid
        · refine ⟨record, ?_, acceptedStart right, hw (by omega), by omega, le_rfl⟩
          rw [hrecords]
          exact List.mem_append_right _ List.mem_cons_self
        · obtain ⟨r, hrmem, sigma, ha, hlo, hhi⟩ := hwitness hem
          refine ⟨r, ?_, sigma, ha, hlo, hhi.trans hmr⟩
          rw [hrecords]
          exact List.mem_append_left _ hrmem

end Run

end Chronology

section ActualLaunchSeed

open ReferenceActivePhysicalHorizon

variable {p : ConstructorDimensions.Parameters}
variable
  (source : Bandits.Support.BootstrapPrivateRoundStreams.SourceInput p)
  (rewards : Bandits.Support.ActualInitializationPhysicalStep.GridRewardTable p)
  (rate : ActualInitializationLaunchState.RateInput p) (C_star C_h : ℝ)
  (b : ReferenceInitializationRun.Boundary p)
  (h : b.completed < Bandits.Support.BootstrapDimensions.n_boot p)
  (actual : ActualInitializationRun.BlockCarry p rate
    (ReferenceInitializationRun.nextBlock b h))
  (past : List (ActualInitializationRun.PhysicalRoundRecord p rate source rewards))
  (hr : ActualReferenceInitializationBlock.BlockStartRelated source rewards
    C_star C_h rate (ReferenceInitializationRun.nextBlock b h) actual b past)
  (hdown : ∀ i, ¬ InitializationFailureProvenance.generatedBlockDown
    (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
    b h i)
  (hclean : ∀ (i : Fin (p.m - 1))
    (hi : ActualReferenceInitializationBlock.refFollower i ∈
      (ReferenceInitializationRun.physical
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
        b h).uninformed),
    Bandits.Support.BootstrapAllCandidateController.cleanPrefix
      (ReferenceInitializationRun.physical
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
        b h)
      source.1.2 ⟨ActualReferenceInitializationBlock.refFollower i, hi⟩
      (Bandits.Support.ActualInitializationPhysicalStep.selectedRowIndex p source) p.T)
  (hforce : ∀ i, ReferenceInitializationRun.forced
    (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
    b h i = false)
  (launch : BootstrapCoordinatorLocalRound.LaunchedBlock p)
  (learnerSeed : ActualInitializationRun.CoordinatorLearnerZeroSeed p)
  (hlaunched : (ActualInitializationRun.combinedBoundaryHandoff p rate
    (ReferenceInitializationRun.nextBlock b h) source rewards actual.C_star actual.C_h
    (ActualInitializationRun.foldBlock p rate (ReferenceInitializationRun.nextBlock b h)
      source rewards actual)).disposition = .launched launch learnerSeed)

include source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch
  learnerSeed hlaunched

/-- The existing actual launch/replay seed supplies the placeholder on
every actual ordinary CHOICE before a first acceptance (observable start
zero). All launch-constructor inputs are retained verbatim. The full public
rows, original private source, selected J, and whole rewards are the same as
the launch inputs. An empty terminal suffix needs no physical action.
-/
theorem ofActualLaunchedBoundary_placeholder_before_acceptance
    (hstop : BootstrapObservedFollower.blockStop p
      (ReferenceInitializationRun.nextBlock b h) < p.T)
    (count : ℕ)
    (hspan : BootstrapObservedFollower.blockStop p
      (ReferenceInitializationRun.nextBlock b h) + count ≤ p.T)
    (i : Fin (p.m - 1)) :
    let initial := ActualInitializationLaunchState.ofActualLaunchedBoundary source rewards rate
      C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed hlaunched
    let origin := BootstrapObservedFollower.blockStop p (ReferenceInitializationRun.nextBlock b h)
    let active := ofActualLaunchedBoundary_allActiveAtBlockStop source rewards rate
      C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed hlaunched hstop
    let execution := run initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
      rewards origin count hspan active
    ∀ (a : Fin execution.records.length)
      (state : ReferencePrelaunchFollower.State p rate.eta)
      (memory : ActiveFollowerLifecycle.LocalMemory p),
      (actualChoice execution.records[a.val] i).configuration = .ordinary state memory →
      acceptedStart state = 0 →
      ∀ offered : OrdinaryMessageCodec.UpRecord (codecParams p rate.eta),
        ActiveFollowerQueueOperation.checkedUpOffer rate.eta
          (actualChoice execution.records[a.val] i).follower
          (actualChoice execution.records[a.val] i).row
          (actualChoice execution.records[a.val] i).activation
          (actualChoice execution.records[a.val] i).time state = .offer offered →
        offered.val = OrdinaryMessageCodec.upPlaceholder := by
  intro initial origin active execution a state memory hc hstart offered hoff
  obtain ⟨seed, seedMemory, hseed, _, _, hs, hS, hd, hb, hu, _⟩ :=
    ofActualLaunchedBoundary_replaySeed source rewards rate C_star C_h b h actual past
      hr hdown hclean hforce launch learnerSeed hlaunched i
  obtain ⟨_, hreply⟩ :=
    (run_initial_to_choice initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
      rewards origin count hspan active i a seed state seedMemory memory hseed hc).2.1 hu
        (hs.trans hstart.symm)
  have hstateS : state.S = seed.S := congrArg (fun v => v.2.1) hreply
  have hstateDelta : state.delta = seed.delta := congrArg (fun v => v.2.2.1) hreply
  have hstateBacklog : state.backlog = seed.backlog := congrArg (fun v => v.2.2.2) hreply
  exact checked_offer_is_placeholder_of_zero_registers _ _ _ _ state hstart
    (hstateS.trans hS) (hstateDelta.trans hd) (hstateBacklog.trans hb) offered hoff

end ActualLaunchSeed

end Bandits.Support.ReferenceFollowerReplyChronology
