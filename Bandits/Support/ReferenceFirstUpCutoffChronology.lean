/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstAcceptedUpNumericSnapshot

/-!
# Actual first accepted-UP cutoff chronology

Sources: `sources/zip4/manuscript/06_interruptions.tex:197-209,246-295,301-344`,
`sources/zip4/manuscript/appendix_a_local_protocol.tex:54-60`, and
`sources/zip4/manuscript/04_slow_fast_learner.tex:157-165`.

The statements concern the original computed physical run, its retained DOWN,
local status, and actual proposal-read memory. They assert no numerical
recovery identity, source queue truth, delivery, or manuscript closure.
-/

@[expose] public section

noncomputable section

open Bandits.Support ConstructorDimensions ReferencePrelaunchFollower
open DeclaredFollowerLocalRound ReferenceFollowerFixedReply

namespace Bandits.Support.ReferenceFirstUpCutoffChronology


variable {p : ConstructorDimensions.Parameters} {rate : ReferenceActivePhysicalStep.RateInput p}

private theorem release_success
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (t : Fin p.T) (observation : Observation p)
    (choice post next : ReferencePrelaunchFollower.State p rate.eta)
    (memory nextMemory : ActiveFollowerLifecycle.LocalMemory p)
    (h : DeclaredFollowerLocalRound.releaseAndFinish rate i row t observation choice memory post =
      .ok (next, nextMemory)) :
    ∃ released,
      ActiveFollowerLifecycle.releaseAfterService rate.eta i t (ActiveFollowerLifecycle.publicRowOfCompleteRow row t)
        observation choice post = .ok released ∧
      ActiveFollowerLifecycle.finishRound rate.eta t row released memory = .ok (next, nextMemory) ∧
      next = released := by
  unfold DeclaredFollowerLocalRound.releaseAndFinish at h
  cases hr : ActiveFollowerLifecycle.releaseAfterService rate.eta i t (ActiveFollowerLifecycle.publicRowOfCompleteRow row t)
      observation choice post with
  | error reason => simp only [hr] at h; cases h
  | ok released =>
    cases hf : ActiveFollowerLifecycle.finishRound rate.eta t row released memory with
    | error reason => simp only [hr, hf] at h; cases h
    | ok pair =>
      have hp : pair = (next, nextMemory) := by
        simpa only [hr, hf, Except.ok.injEq] using h
      have hf' := hf.trans (congrArg Except.ok hp)
      exact ⟨released, rfl, hf', ActiveFollowerLifecycle.finishRound_frame rate.eta t row released next
        memory nextMemory hf'⟩

private theorem release_status
    (i : Fin (p.m - 1)) (t : Fin p.T)
    (row : ActiveFollowerLifecycle.FollowerPublicRow p.m p.K) (observation : Observation p)
    (choice post released : ReferencePrelaunchFollower.State p rate.eta)
    (h : ActiveFollowerLifecycle.releaseAfterService rate.eta i t row observation choice post = .ok released)
    (hs : post.status = choice.status) :
    (released.status = .unoccupied ↔ choice.status = .unoccupied) := by
  classical
  unfold ActiveFollowerLifecycle.releaseAfterService at h
  split at h
  next hpending =>
    split at h
    · split at h
      · cases h
      · split at h
        · split at h
          · dsimp only at h
            split at h
            · split at h
              · have he := Except.ok.inj h
                rw [← he]
                simp only [hpending, reduceCtorEq]
              · cases h
            · split at h
              · have he := Except.ok.inj h
                rw [← he, hs]
              · cases h
          · cases h
        · cases h
    · cases h
  next hpending =>
    have he := Except.ok.inj h
    rw [← he, hs]

private theorem finish_memory
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (t : Fin p.T) (observation : Observation p)
    (choice post next : ReferencePrelaunchFollower.State p rate.eta)
    (memory nextMemory : ActiveFollowerLifecycle.LocalMemory p)
    (h : DeclaredFollowerLocalRound.releaseAndFinish rate i row t observation choice memory post =
      .ok (next, nextMemory)) :
    (next.status = .unoccupied → nextMemory = memory) ∧
    (next.status ≠ .unoccupied → nextMemory.lastProposalRead =
      some ⟨t, FollowerCutoffScan.completeRowProposalBit p rate.eta.val row t⟩) := by
  classical
  obtain ⟨released, hr, hf, he⟩ := release_success i row t observation
    choice post next memory nextMemory h
  subst released
  have hvalid : ActiveFollowerLifecycle.localStateDomainValid next := by
    by_contra hn
    rw [ActiveFollowerLifecycle.finishRound_invalid_domain rate.eta t row next memory hn] at hf
    cases hf
  constructor
  · intro hu
    have hm := DeclaredFollowerLocalRound.releaseAndFinish_unoccupied_memory rate i row t observation
      choice memory post next hr hvalid hu
    exact (Prod.mk.inj (Except.ok.inj (h.symm.trans hm))).2
  · intro ho
    cases hd : next.lastDown with
    | none =>
      rw [ActiveFollowerLifecycle.finishRound_missing_record rate.eta t row next memory ho hvalid hd] at hf
      cases hf
    | some message =>
      have ht : message.val.sigma ≤ t.val + 1 := by
        by_contra hn
        rw [ActiveFollowerLifecycle.finishRound_incompatible_start rate.eta t row next memory ho hvalid
          message hd (by omega)] at hf
        cases hf
      have hm := DeclaredFollowerLocalRound.releaseAndFinish_occupied_token rate i row t observation
        choice memory post next hr hvalid ho message hd ht
      exact congrArg ActiveFollowerLifecycle.LocalMemory.lastProposalRead
        (Prod.mk.inj (Except.ok.inj (h.symm.trans hm))).2

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

private theorem record_without_down
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) (i : Fin (p.m - 1))
    (next : ReferencePrelaunchFollower.State p rate.eta) (nextMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hout : record.output.next.followers i = .ordinary next nextMemory)
    (hno : ∀ sigma, ¬ ReferenceFollowerReplyChronology.appliedDown record i sigma) :
    ∃ choice memory,
      (actualChoice record i).configuration = .ordinary choice memory ∧
      next.lastDown = choice.lastDown ∧
      (next.status = .unoccupied ↔ choice.status = .unoccupied) ∧
      (next.status = .unoccupied → nextMemory = memory) ∧
      (next.status ≠ .unoccupied → nextMemory.lastProposalRead =
        some ⟨record.input.time,
          FollowerCutoffScan.completeRowProposalBit p rate.eta.val record.input.row record.input.time⟩) := by
  classical
  obtain ⟨choice, memory, post, hc, hr, hf, hi, hd⟩ := actual_finish record i next nextMemory hout
  have halign := actualChoice_alignment record i
  have hpost : post.lastDown = choice.lastDown ∧ post.status = choice.status := by
    by_cases hu : choice.status = .unoccupied
    · rcases ReferenceFollowerReplyChronology.recordFollower_ordinary_inversion _ _ _ _ _ _ _ _ choice post hr with
        ⟨hlast, hkeep⟩ | ⟨logged, cut, raw, message, scan, registers, lastService,
          hinput, hdown, _, ha, _, _⟩
      · exact ⟨hlast, (hkeep hu).2.trans hu.symm⟩
      · exact (hno message.val.sigma ⟨logged, cut, post, raw, message, scan,
          registers, lastService, hi.trans hinput, hd.trans hdown, ha, rfl⟩).elim
    · simp only [ReferenceActivePhysicalStep.recordFollower, DeclaredFollowerLocalRound.recordOrServiceThenDown,
        dite_eq_right hu] at hr
      cases hs : ActiveFollowerQueueOperation.checkedService rate.eta rate.sourceCap rate.n rate.n_scale
          (actualChoice record i).follower (actualChoice record i).row
          (actualChoice record i).activation (actualChoice record i).time
          (record.output.preparation.feedback.observations
            (PublicDiscreteDraws.followerPlayer p.two_le_m i)) choice with
      | failure => rw [hs] at hr; cases hr
      | success result =>
        rw [hs] at hr
        have hp := Except.ok.inj hr
        rw [← hp, result.queueUpdate]
        have hframe := ActiveFollowerQueueOperation.serviceOutput_preserves_other_registers rate.n choice result.arrival
        exact ⟨hframe.1, hframe.2.2.2.1⟩
  obtain ⟨released, hrelease, _hfinish, he⟩ := release_success _ _ _ _ choice post
    next memory nextMemory hf
  have hstatus := release_status _ _ _ _ choice post released hrelease hpost.2
  have hframe := ReferenceFollowerReplyChronology.releaseAndFinish_frame _ _ _ _ choice post next memory nextMemory hf
  have hmem := finish_memory _ _ _ _ choice post next memory nextMemory hf
  refine ⟨choice, memory, hc, (congrArg Prod.fst hframe.1).trans hpost.1,
    he ▸ hstatus, hmem.1, ?_⟩
  simpa only [halign.1, halign.2.2] using hmem.2

private theorem accepted_scan_endpoint
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (t : Fin p.T) (observation : Observation p)
    (before after : ReferencePrelaunchFollower.State p rate.eta)
    (raw : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p)))
    (message : ReferenceFirstAcceptedUpNumericSnapshot.DownRecord (p := p) (rate := rate))
    (scan : FollowerCutoffScan.ScanResult p.T) (registers : ℕ × ℕ) (lastService : ℕ)
    (h : ActiveFollowerDownAcceptance.downTransition p i row t observation rate before =
      .accepted before after raw message scan registers lastService) :
    scan.endpoint = min (FollowerCutoffScan.firstCutoff p rate.eta.val (ActiveFollowerDownAcceptance.downStart p rate message)
      (FollowerCutoffScan.completeRowProposalBit p rate.eta.val row)) (t.val + 2) := by
  classical
  unfold ActiveFollowerDownAcceptance.downTransition at h
  split at h
  · split at h
    · split at h
      · split at h
        · split at h
          · dsimp only at h
            split at h
            · cases h
            · split at h
              · split at h
                · cases h
                · cases h
                  exact FollowerCutoffScan.followerCutoffScan_endpoint_eq_min_firstCutoff _ _ _ _
                    (ActiveFollowerDownAcceptance.acceptedDownStartLE p rate message t before ‹_›) _
              · cases h
          · cases h
        · cases h
      · cases h
    · cases h
  · cases h

private theorem accepted_output
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1))
    (message : ReferenceFirstAcceptedUpNumericSnapshot.DownRecord (p := p) (rate := rate))
    (hretained : ReferenceAcceptedUpFollowerHistory.RetainedDown record i message)
    (next : ReferencePrelaunchFollower.State p rate.eta)
    (nextMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hout : record.output.next.followers i = .ordinary next nextMemory) :
    next.lastDown = some message ∧
    (next.status = .unoccupied ↔
      FollowerCutoffScan.firstCutoff p rate.eta.val
        (ActiveFollowerDownAcceptance.downStart p rate message)
        (FollowerCutoffScan.completeRowProposalBit p rate.eta.val record.input.row) ≤
        record.input.time.val + 1) ∧
    ∃ choice memory,
      (actualChoice record i).configuration = .ordinary choice memory ∧
      choice.status = .unoccupied ∧
      (next.status = .unoccupied → nextMemory = memory) ∧
      (next.status ≠ .unoccupied → nextMemory.lastProposalRead =
        some ⟨record.input.time, FollowerCutoffScan.completeRowProposalBit
          p rate.eta.val record.input.row record.input.time⟩) := by
  classical
  obtain ⟨logged, cut, after, raw, scan, registers, lastService, hinput, hdown, ha⟩ := hretained
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
  have htransition := ReferenceFollowerSparseEmissionRecovery.actualAcceptedCut_downTransition
    record i logged cut after raw message scan registers lastService hinput hdown ha
  have hfields := ActiveFollowerDownAcceptance.downTransition_accepted_checked p
    _ _ _ _ rate logged after raw message scan registers lastService htransition
  have hend := accepted_scan_endpoint _ _ _ _ logged after raw message scan
    registers lastService htransition
  have hframe := ReferenceFollowerReplyChronology.releaseAndFinish_frame _ _ _ _
    saved after next savedMemory nextMemory hf
  have hstatus := hframe.2 hu
  have hlast : next.lastDown = some message := by
    have he := congrArg Prod.fst hframe.1
    change next.lastDown = after.lastDown at he
    rw [he, hfields.2.2.2.2.2.2]
  have halign := actualChoice_alignment record i
  dsimp only [actualChoice] at halign
  have hmemory := finish_memory _ _ _ _ saved after next savedMemory nextMemory hf
  refine ⟨hlast, ?_, saved, savedMemory, hc, hu, hmemory.1, ?_⟩
  · rw [hstatus, hfields.2.2.2.2.2.2]
    simp only
    simp only [hend, halign.1, halign.2.2]
    simp only [ite_eq_right_iff, reduceCtorEq, imp_false, min_eq_right_iff]
    omega
  · simpa only [halign.1, halign.2.2] using hmemory.2

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

private theorem first_cutoff_test
    (sigma t prior : Fin p.T) (bits : Fin p.T → Bool)
    (hstart : sigma.val < t.val) (hprior : prior.val + 1 = t.val)
    (hle : t.val + 1 ≤ FollowerCutoffScan.firstCutoff p rate.eta.val sigma bits) :
    (FollowerCutoffScan.gridBoundary p rate.eta.val sigma = t.val + 1 ∨
      bits prior = true) ↔
      FollowerCutoffScan.firstCutoff p rate.eta.val sigma bits = t.val + 1 := by
  classical
  let carrier := FollowerCutoffScan.firstCutoffCarrier p rate.eta.val sigma bits
  have hmin : FollowerCutoffScan.firstCutoff p rate.eta.val sigma bits =
      carrier.min' (FollowerCutoffScan.firstCutoffCarrier_nonempty _ _ _ _) := rfl
  constructor
  · intro h
    have hmem : t.val + 1 ∈ carrier := by
      rcases h with hg | hb
      · exact hg ▸ Finset.mem_insert_self _ _
      · apply Finset.mem_insert_of_mem
        apply Finset.mem_image.mpr
        refine ⟨prior, Finset.mem_filter.mpr ⟨?_, hb⟩, ?_⟩
        · simp only [FollowerCutoffScan.proposalCoordinates, Finset.mem_filter,
            Finset.mem_univ, true_and]
          omega
        · simp only [FollowerCutoffScan.proposalEndpoint]
          omega
    have hm := Finset.min'_le carrier (t.val + 1) hmem
    omega
  · intro he
    have hm : FollowerCutoffScan.firstCutoff p rate.eta.val sigma bits ∈ carrier :=
      Finset.min'_mem _ _
    rw [he] at hm
    rcases Finset.mem_insert.mp hm with hg | hb
    · exact Or.inl hg.symm
    · obtain ⟨v, hv, ht⟩ := Finset.mem_image.mp hb
      have hvbit := (Finset.mem_filter.mp hv).2
      have heq : v = prior := by
        apply Fin.ext
        simp only [FollowerCutoffScan.proposalEndpoint] at ht
        omega
      exact Or.inr (heq ▸ hvbit)

private theorem start_status
    (message : ReferenceFirstAcceptedUpNumericSnapshot.DownRecord (p := p) (rate := rate))
    (t prior : Fin p.T) (bits : Fin p.T → Bool)
    (hprior : prior.val + 1 = t.val) (hstarted : message.val.sigma ≤ t.val)
    (before choice : ReferencePrelaunchFollower.State p rate.eta)
    (memory choiceMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hs : ActiveFollowerLifecycle.startRound rate.eta t before memory = .ok (choice, choiceMemory))
    (hlast : before.lastDown = some message)
    (hstatus : before.status = .unoccupied ↔
      FollowerCutoffScan.firstCutoff p rate.eta.val
        (ActiveFollowerDownAcceptance.downStart p rate message) bits ≤ prior.val + 1)
    (hread : before.status ≠ .unoccupied →
      memory.lastProposalRead = some ⟨prior, bits prior⟩) :
    choice.lastDown = some message ∧ choiceMemory = memory ∧
    (choice.status = .unoccupied ↔
      FollowerCutoffScan.firstCutoff p rate.eta.val
        (ActiveFollowerDownAcceptance.downStart p rate message) bits ≤ t.val + 1) := by
  classical
  have hframe := ActiveFollowerLifecycle.startRound_frame rate.eta t before choice
    memory choiceMemory hs
  refine ⟨hframe.1.trans hlast, hframe.2.2.2.2.2.2.2, ?_⟩
  have hvalid : ActiveFollowerLifecycle.localStateDomainValid before := by
    by_contra hn
    simp only [ActiveFollowerLifecycle.startRound,
      ActiveFollowerLifecycle.interruptionDecision_invalid_domain rate.eta t before memory hn]
      at hs
    cases hs
  by_cases hu : before.status = .unoccupied
  · have he := ActiveFollowerLifecycle.startRound_unoccupied rate.eta t before memory hvalid hu
    have hp := Prod.mk.inj (Except.ok.inj (hs.symm.trans he))
    rw [hp.1, hu]
    have ht := hstatus.mp hu
    simp only [true_iff]
    omega
  · have hbound := FollowerCutoffScan.firstCutoff_bounds p rate.eta.val
      rate.eta.property rate.sourceCap (ActiveFollowerDownAcceptance.downStart p rate message) bits
    have hc := ActiveFollowerDownAcceptance.downStart_val_add_one p rate message
    have hle : t.val + 1 ≤ FollowerCutoffScan.firstCutoff p rate.eta.val
        (ActiveFollowerDownAcceptance.downStart p rate message) bits := by
      have hn := mt hstatus.mpr hu
      omega
    have hg : t.val + 1 ≤ FollowerCutoffScan.gridBoundary p rate.eta.val
        (ActiveFollowerLifecycle.acceptedStartCoordinate message) :=
      hle.trans hbound.2
    have hb := ActiveFollowerLifecycle.startRound_occupied_branch rate.eta t before memory
      hu hvalid message hlast hstarted hg ⟨prior, bits prior⟩ (hread hu) hprior
    have hp := Prod.mk.inj (Except.ok.inj (hs.symm.trans hb))
    have ht := first_cutoff_test (ActiveFollowerDownAcceptance.downStart p rate message)
      t prior bits (by omega) hprior hle
    have he : ((decide (FollowerCutoffScan.gridBoundary p rate.eta.val
        (ActiveFollowerDownAcceptance.downStart p rate message) = t.val + 1)) ||
        bits prior) = true ↔ FollowerCutoffScan.firstCutoff p rate.eta.val
        (ActiveFollowerDownAcceptance.downStart p rate message) bits = t.val + 1 := by
      simpa only [Bool.or_eq_true, decide_eq_true_eq] using ht
    rw [hp.1]
    change (if _ then _ else _) = _ ↔ _
    split
    · rename_i h
      have hu' := he.mp h
      simp only [true_iff]
      omega
    · rename_i h
      have hn : FollowerCutoffScan.firstCutoff p rate.eta.val
          (ActiveFollowerDownAcceptance.downStart p rate message) bits ≠ t.val + 1 := by
        intro heq
        exact h (he.mpr heq)
      simp only [hu, false_iff]
      omega

section Run

variable (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (span : start + count ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)

private theorem run_time
    (n : Fin (ReferenceActivePhysicalHorizon.run initial rows J rewards start count span active).records.length) :
    (ReferenceActivePhysicalHorizon.run initial rows J rewards start count span active).records[n.val].input.time.val =
      start + n.val := by
  have ht := ReferenceActivePhysicalHorizon.run_time_values initial rows J rewards start count span active
  have hn : n.val < (ReferenceActivePhysicalHorizon.calendar start count).length := by
    rw [← ht, List.length_map]
    exact n.isLt
  have hi := congrArg (fun xs : List ℕ => xs[n.val]?) ht
  rw [List.getElem?_eq_getElem (by simpa only [List.length_map] using n.isLt),
    List.getElem?_eq_getElem hn] at hi
  have hc : (ReferenceActivePhysicalHorizon.calendar start count)[n.val] = start + n.val := by
    simp only [ReferenceActivePhysicalHorizon.calendar, List.getElem_range', Nat.one_mul]
  exact Option.some.inj (by simpa only [List.getElem_map, hc] using hi)

private theorem run_row
    (n : Fin (ReferenceActivePhysicalHorizon.run initial rows J rewards start count span active).records.length) :
    (ReferenceActivePhysicalHorizon.run initial rows J rewards start count span active).records[n.val].input.row = rows J := by
  have hi := ReferenceActivePhysicalHorizon.run_record_inputs initial rows J rewards start count span active
    _ (List.getElem_mem n.isLt)
  simp only [ReferenceActivePhysicalStep.RoundInput.row, hi.1, hi.2.1]

private theorem run_ordinary_prefix
    (i : Fin (p.m - 1))
    (k : Fin (ReferenceActivePhysicalHorizon.run initial rows J rewards start count span active).records.length)
    (last : ReferencePrelaunchFollower.State p rate.eta)
    (lastMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hlastChoice : (actualChoice
      (ReferenceActivePhysicalHorizon.run initial rows J rewards start count span active).records[k.val] i).configuration =
        .ordinary last lastMemory) :
    let E := ReferenceActivePhysicalHorizon.run initial rows J rewards start count span active
    (∀ n : Fin E.records.length, n.val < k.val →
      ∃ s mu, E.records[n.val].output.next.followers i = .ordinary s mu) ∧
    (∀ n : Fin E.records.length, n.val ≤ k.val →
      ∃ s mu, (actualChoice E.records[n.val] i).configuration = .ordinary s mu) := by
  let E := ReferenceActivePhysicalHorizon.run initial rows J rewards start count span active
  obtain ⟨lastInput, lastInputMemory, hlastInput, hlastReply, _⟩ :=
    ReferenceFollowerReplyChronology.record_input_to_choice E.records[k.val] i last lastMemory hlastChoice
  have hprefix := ReferenceFollowerReplyChronology.connected_take_to_input E.connected k.val k.isLt
  have houtputs (n : Fin E.records.length) (hn : n.val < k.val) :
      ∃ s mu, E.records[n.val].output.next.followers i = .ordinary s mu := by
    have hnt : n.val < (E.records.take k.val).length := by
      simp only [List.length_take]
      exact lt_min hn n.isLt
    obtain ⟨s, mu, ho, _⟩ := ReferenceFollowerReplyChronology.connected_output_chronology
      hprefix i lastInput lastInputMemory hlastInput n.val hnt
    have he := List.getElem_take (xs := E.records) (j := k.val) (i := n.val) (h := hnt)
    rw [he] at ho
    exact ⟨s, mu, ho⟩
  have hchoices (n : Fin E.records.length) (hn : n.val ≤ k.val) :
      ∃ s mu, (actualChoice E.records[n.val] i).configuration = .ordinary s mu := by
    by_cases he : n.val = k.val
    · have heq : n = k := Fin.ext he
      subst n
      exact ⟨last, lastMemory, hlastChoice⟩
    · obtain ⟨s, mu, ho⟩ := houtputs n (by omega)
      obtain ⟨c, cm, hc, _, _, _⟩ :=
        ReferenceFollowerReplyChronology.record_choice_chronology E.records[n.val] i s mu ho
      exact ⟨c, cm, hc⟩
  exact ⟨houtputs, hchoices⟩

private theorem run_retained_start_eq
    (hfirst : initial.coordinator = .first) (i : Fin (p.m - 1))
    (j : Fin (ReferenceActivePhysicalHorizon.run initial rows J rewards start count span active).records.length)
    (message : ReferenceFirstAcceptedUpNumericSnapshot.DownRecord (p := p) (rate := rate))
    (hretained : ReferenceAcceptedUpFollowerHistory.RetainedDown
      (ReferenceActivePhysicalHorizon.run initial rows J rewards start count span active).records[j.val] i message)
    (hmessage : message.val.sigma = start + 1) :
    (ActiveFollowerDownAcceptance.downStart p rate message).val = start := by
  let E := ReferenceActivePhysicalHorizon.run initial rows J rewards start count span active
  -- The selected-view lower bound consumes original installation births.
  have hinterval := ReferenceFirstAcceptedUpNumericSnapshot.run_selectedViewInterval
    initial rows J rewards start count span active hfirst
  obtain ⟨logged, cut, after, raw, scan, registers, lastService, hinput, hdown, ha⟩ := hretained
  obtain ⟨c, cm, logged', _hc, _hu, _hl, hi, hcut⟩ :=
    ReferenceFollowerSparseEmissionRecovery.actualDownDiagnostic_choice E.records[j.val] i cut hdown
  have hlog : logged' = logged := Option.some.inj (hi.symm.trans hinput)
  subst logged'
  rw [hcut] at ha
  obtain ⟨view, hv⟩ := ReferenceFollowerSparseEmissionRecovery.acceptedReferenceCut_someView
    _ _ _ _ _ logged logged after raw message scan registers lastService ha
  have ha' := ha
  rw [hv] at ha'
  have hfields := ReferenceActiveDataOwnership.referenceDown_accepted_fields view _ _ _ _
    logged logged after raw message scan registers lastService ha'
  have halign := actualChoice_alignment E.records[j.val] i
  dsimp only [actualChoice] at halign
  rw [halign.2.1] at hfields
  have hlower := hinterval E.records[j.val] (List.getElem_mem j.isLt) view hv
  have hone := ActiveFollowerDownAcceptance.downStart_val_add_one p rate message
  have hs : message.val.sigma = view.payload.sigma.val + 1 := by
    rw [hfields.1]
    rfl
  omega

private theorem run_next_status
    (i : Fin (p.m - 1))
    (k : Fin (ReferenceActivePhysicalHorizon.run initial rows J rewards start count span active).records.length)
    (message : ReferenceFirstAcceptedUpNumericSnapshot.DownRecord (p := p) (rate := rate))
    (hmessage : message.val.sigma = start + 1)
    (last : ReferencePrelaunchFollower.State p rate.eta)
    (lastMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hlastChoice : (actualChoice
      (ReferenceActivePhysicalHorizon.run initial rows J rewards start count span active).records[k.val] i).configuration =
        .ordinary last lastMemory) :
    let E := ReferenceActivePhysicalHorizon.run initial rows J rewards start count span active
    let bits := FollowerCutoffScan.completeRowProposalBit p rate.eta.val (rows J)
    let u := FollowerCutoffScan.firstCutoff p rate.eta.val
      (ActiveFollowerDownAcceptance.downStart p rate message) bits
    ∀ (n : Fin E.records.length) (hnk : n.val < k.val)
      (s : ReferencePrelaunchFollower.State p rate.eta) (mu : ActiveFollowerLifecycle.LocalMemory p)
      (_ho : E.records[n.val].output.next.followers i = .ordinary s mu)
      (_hd : s.lastDown = some message)
      (_hst : s.status = .unoccupied ↔ u ≤ start + n.val + 1)
      (_hr : s.status ≠ .unoccupied → mu.lastProposalRead =
        some ⟨E.records[n.val].input.time, bits E.records[n.val].input.time⟩),
      ∃ c cm, (actualChoice (E.records[n.val + 1]'(by
        have hk : k.val < E.records.length := k.isLt
        omega)) i).configuration = .ordinary c cm ∧
        c.lastDown = some message ∧ cm = mu ∧
        (c.status = .unoccupied ↔ u ≤ start + (n.val + 1) + 1) := by
  dsimp only
  let E := ReferenceActivePhysicalHorizon.run initial rows J rewards start count span active
  let bits := FollowerCutoffScan.completeRowProposalBit p rate.eta.val (rows J)
  let u := FollowerCutoffScan.firstCutoff p rate.eta.val
    (ActiveFollowerDownAcceptance.downStart p rate message) bits
  have hk : k.val < E.records.length := k.isLt
  obtain ⟨_, hchoices⟩ := run_ordinary_prefix initial rows J rewards start count span active
    i k last lastMemory hlastChoice
  have htime (n : Fin E.records.length) : E.records[n.val].input.time.val = start + n.val :=
    run_time initial rows J rewards start count span active n
  intro n hnk s mu ho hd hst hr
  let next : Fin E.records.length := ⟨n.val + 1, by omega⟩
  obtain ⟨c, cm, hc⟩ := hchoices next (by dsimp only [next]; omega)
  have hi : E.records[next.val].input.state.followers i = .ordinary s mu := by
    have he := connected_next E.connected n.val (by omega)
    exact congrArg (fun s => s.followers i) he |>.trans ho
  have hs := actual_start E.records[next.val] i s c mu cm hi hc
  have hst' : s.status = .unoccupied ↔ u ≤ E.records[n.val].input.time.val + 1 := by
    simpa only [htime n] using hst
  have hresult := start_status message E.records[next.val].input.time E.records[n.val].input.time
    bits (by rw [htime n, htime next]; dsimp only [next]; omega)
    (by rw [hmessage, htime next]; dsimp only [next]; omega)
    s c mu cm hs hd hst' hr
  refine ⟨c, cm, hc, hresult.1, hresult.2.1, ?_⟩
  simpa only [htime next, next] using hresult.2.2

private theorem run_same_down_interval
    (i : Fin (p.m - 1))
    (j k : Fin (ReferenceActivePhysicalHorizon.run initial rows J rewards start count span active).records.length)
    (hjk : j.val < k.val)
    (message : ReferenceFirstAcceptedUpNumericSnapshot.DownRecord (p := p) (rate := rate))
    (hretained : ReferenceAcceptedUpFollowerHistory.RetainedDown
      (ReferenceActivePhysicalHorizon.run initial rows J rewards start count span active).records[j.val] i message)
    (hmessage : message.val.sigma = start + 1)
    (last : ReferencePrelaunchFollower.State p rate.eta)
    (lastMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hlastChoice : (actualChoice
      (ReferenceActivePhysicalHorizon.run initial rows J rewards start count span active).records[k.val] i).configuration =
        .ordinary last lastMemory)
    (hlastDown : last.lastDown = some message) :
    let E := ReferenceActivePhysicalHorizon.run initial rows J rewards start count span active
    (∀ (n : Fin E.records.length), j.val < n.val → n.val ≤ k.val →
      ∀ (s : ReferencePrelaunchFollower.State p rate.eta) (mu : ActiveFollowerLifecycle.LocalMemory p),
        (actualChoice E.records[n.val] i).configuration = .ordinary s mu → acceptedStart s = start + 1) ∧
    (∀ (n : Fin E.records.length), j.val < n.val → n.val < k.val →
      ∀ sigma, ¬ ReferenceFollowerReplyChronology.appliedDown E.records[n.val] i sigma) := by
  let E := ReferenceActivePhysicalHorizon.run initial rows J rewards start count span active
  have hk : k.val < E.records.length := k.isLt
  obtain ⟨houtputs, hchoices⟩ := run_ordinary_prefix initial rows J rewards start count span active
    i k last lastMemory hlastChoice
  change (∀ n : Fin E.records.length, n.val < k.val →
    ∃ s mu, E.records[n.val].output.next.followers i = .ordinary s mu) at houtputs
  change (∀ n : Fin E.records.length, n.val ≤ k.val →
    ∃ s mu, (actualChoice E.records[n.val] i).configuration = .ordinary s mu) at hchoices
  obtain ⟨firstOut, firstMemory, hfirstOut⟩ := houtputs j hjk
  have hfirstDown := (accepted_output E.records[j.val] i message hretained
    firstOut firstMemory hfirstOut).1
  have hlastStart : acceptedStart last = start + 1 := by
    simp only [acceptedStart, hlastDown, hmessage]
  let a : Fin E.records.length := ⟨j.val + 1, by omega⟩
  obtain ⟨aState, aMemory, haChoice⟩ := hchoices a (by dsimp only [a]; omega)
  have haInput : E.records[a.val].input.state.followers i = .ordinary firstOut firstMemory := by
    have hc := connected_next E.connected j.val (by omega)
    exact congrArg (fun s => s.followers i) hc |>.trans hfirstOut
  have haStart := actual_start E.records[a.val] i firstOut aState firstMemory aMemory haInput haChoice
  have haFrame := ActiveFollowerLifecycle.startRound_frame rate.eta _ _ _ _ _ haStart
  have haDown : aState.lastDown = some message := haFrame.1.trans hfirstDown
  have haSigma : acceptedStart aState = start + 1 := by
    simp only [acceptedStart, haDown, hmessage]
  have hstarts (n : Fin E.records.length) (hjn : j.val < n.val) (hnk : n.val ≤ k.val)
      (s : ReferencePrelaunchFollower.State p rate.eta) (mu : ActiveFollowerLifecycle.LocalMemory p)
      (hc : (actualChoice E.records[n.val] i).configuration = .ordinary s mu) :
      acceptedStart s = start + 1 := by
    have hlo := (ReferenceFollowerReplyChronology.run_acceptedStart_mono initial rows J rewards
      start count span active i a n (by dsimp only [a]; omega)
      aState s aMemory mu haChoice hc).1
    have hhi := (ReferenceFollowerReplyChronology.run_acceptedStart_mono initial rows J rewards
      start count span active i n k hnk s last mu lastMemory hc hlastChoice).1
    omega
  have hno (n : Fin E.records.length) (hjn : j.val < n.val) (hnk : n.val < k.val)
      (sigma : ℕ) : ¬ ReferenceFollowerReplyChronology.appliedDown E.records[n.val] i sigma :=
    ReferenceFollowerReplyChronology.run_no_appliedDown_of_equal_starts initial rows J rewards
      start count span active i a k aState last aMemory lastMemory haChoice hlastChoice
      (haSigma.trans hlastStart.symm) n (by dsimp only [a]; omega) hnk sigma
  exact ⟨hstarts, hno⟩

private theorem run_status_outputs
    (i : Fin (p.m - 1))
    (j k : Fin (ReferenceActivePhysicalHorizon.run initial rows J rewards start count span active).records.length)
    (hjk : j.val < k.val)
    (message : ReferenceFirstAcceptedUpNumericSnapshot.DownRecord (p := p) (rate := rate))
    (hretained : ReferenceAcceptedUpFollowerHistory.RetainedDown
      (ReferenceActivePhysicalHorizon.run initial rows J rewards start count span active).records[j.val] i message)
    (hmessage : message.val.sigma = start + 1)
    (last : ReferencePrelaunchFollower.State p rate.eta)
    (lastMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hlastChoice : (actualChoice
      (ReferenceActivePhysicalHorizon.run initial rows J rewards start count span active).records[k.val] i).configuration =
        .ordinary last lastMemory)
    (hlastDown : last.lastDown = some message) :
    let E := ReferenceActivePhysicalHorizon.run initial rows J rewards start count span active
    let bits := FollowerCutoffScan.completeRowProposalBit p rate.eta.val (rows J)
    let u := FollowerCutoffScan.firstCutoff p rate.eta.val
      (ActiveFollowerDownAcceptance.downStart p rate message) bits
    ∀ (n : ℕ) (_hjn : j.val ≤ n) (hnk : n < k.val),
      ∃ s mu c cm,
        (E.records[n]'(lt_trans hnk k.isLt)).output.next.followers i = .ordinary s mu ∧
        s.lastDown = some message ∧ (s.status = .unoccupied ↔ u ≤ start + n + 1) ∧
        (actualChoice (E.records[n]'(lt_trans hnk k.isLt)) i).configuration = .ordinary c cm ∧
        (s.status = .unoccupied → mu = cm) ∧
        (s.status ≠ .unoccupied → mu.lastProposalRead =
          some ⟨(E.records[n]'(lt_trans hnk k.isLt)).input.time,
            bits (E.records[n]'(lt_trans hnk k.isLt)).input.time⟩) := by
  let E := ReferenceActivePhysicalHorizon.run initial rows J rewards start count span active
  let bits := FollowerCutoffScan.completeRowProposalBit p rate.eta.val (rows J)
  let u := FollowerCutoffScan.firstCutoff p rate.eta.val
    (ActiveFollowerDownAcceptance.downStart p rate message) bits
  have hk : k.val < E.records.length := k.isLt
  obtain ⟨houtputs, _⟩ := run_ordinary_prefix initial rows J rewards start count span active
    i k last lastMemory hlastChoice
  change (∀ n : Fin E.records.length, n.val < k.val →
    ∃ s mu, E.records[n.val].output.next.followers i = .ordinary s mu) at houtputs
  obtain ⟨firstOut, firstMemory, hfirstOut⟩ := houtputs j hjk
  obtain ⟨hfirstDown, hfirstStatus, firstChoice, firstChoiceMemory, hfirstChoice,
      hfirstUnoccupied, hfirstKeep, hfirstRead⟩ :=
    accepted_output E.records[j.val] i message hretained firstOut firstMemory hfirstOut
  have htime (n : Fin E.records.length) : E.records[n.val].input.time.val = start + n.val :=
    run_time initial rows J rewards start count span active n
  have hrow (n : Fin E.records.length) : E.records[n.val].input.row = rows J :=
    run_row initial rows J rewards start count span active n
  have hfirstStatus' : firstOut.status = .unoccupied ↔ u ≤ start + j.val + 1 := by
    simpa only [hrow j, htime j, u, bits] using hfirstStatus
  have hfirstRead' : firstOut.status ≠ .unoccupied → firstMemory.lastProposalRead =
      some ⟨E.records[j.val].input.time, bits E.records[j.val].input.time⟩ := by
    simpa only [hrow j, bits] using hfirstRead
  have hno := (run_same_down_interval initial rows J rewards start count span active
    i j k hjk message hretained hmessage last lastMemory hlastChoice hlastDown).2
  have hstep (n : Fin E.records.length) (hnk : n.val < k.val)
      (s : ReferencePrelaunchFollower.State p rate.eta) (mu : ActiveFollowerLifecycle.LocalMemory p)
      (ho : E.records[n.val].output.next.followers i = .ordinary s mu)
      (hd : s.lastDown = some message)
      (hst : s.status = .unoccupied ↔ u ≤ start + n.val + 1)
      (hr : s.status ≠ .unoccupied → mu.lastProposalRead =
        some ⟨E.records[n.val].input.time, bits E.records[n.val].input.time⟩) :
      ∃ c cm, (actualChoice (E.records[n.val + 1]'(by omega)) i).configuration = .ordinary c cm ∧
        c.lastDown = some message ∧ cm = mu ∧
        (c.status = .unoccupied ↔ u ≤ start + (n.val + 1) + 1) :=
    run_next_status initial rows J rewards start count span active
      i k message hmessage last lastMemory hlastChoice n hnk s mu ho hd hst hr
  have hall (n : ℕ) (hjn : j.val ≤ n) (hnk : n < k.val) :
      ∃ s mu c cm,
        E.records[n].output.next.followers i = .ordinary s mu ∧
        s.lastDown = some message ∧ (s.status = .unoccupied ↔ u ≤ start + n + 1) ∧
        (actualChoice E.records[n] i).configuration = .ordinary c cm ∧
        (s.status = .unoccupied → mu = cm) ∧
        (s.status ≠ .unoccupied → mu.lastProposalRead =
          some ⟨E.records[n].input.time, bits E.records[n].input.time⟩) := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      by_cases he : n = j.val
      · subst n
        exact ⟨firstOut, firstMemory, firstChoice, firstChoiceMemory, hfirstOut,
          hfirstDown, hfirstStatus', hfirstChoice, hfirstKeep, hfirstRead'⟩
      · have hnpos : 0 < n := by omega
        obtain ⟨s, mu, _c, _cm, ho, hd, hst, _hc, _hkeep, hr⟩ :=
          ih (n - 1) (by omega) (by omega) (by omega)
        let prev : Fin E.records.length := ⟨n - 1, by omega⟩
        obtain ⟨c, cm, hc, hcd, hcm, hcst⟩ := hstep prev (by dsimp only [prev]; omega) s mu ho hd hst hr
        have hnprev : prev.val + 1 = n := by dsimp only [prev]; omega
        have hcN : (actualChoice E.records[n] i).configuration = .ordinary c cm := by
          simpa only [hnprev] using hc
        have hcstN : c.status = .unoccupied ↔ u ≤ start + n + 1 := by
          simpa only [hnprev] using hcst
        let current : Fin E.records.length := ⟨n, by omega⟩
        obtain ⟨out, outMemory, hout⟩ := houtputs current hnk
        obtain ⟨c', cm', hc', houtDown, houtStatus, hkeep, hread⟩ :=
          record_without_down E.records[n] i out outMemory hout
            (hno current (by dsimp only [current]; omega) hnk)
        obtain ⟨hec, hem⟩ := LocalConfiguration.ordinary.inj (hc'.symm.trans hcN)
        subst c'
        subst cm'
        refine ⟨out, outMemory, c, cm, hout, houtDown.trans hcd,
          houtStatus.trans hcstN, hcN, hkeep, ?_⟩
        have hrowN : E.records[n].input.row = rows J := hrow current
        simpa only [hrowN, bits] using hread
  exact hall

end Run

/-- Actual first-sigma accepted-UP chronology. The focal ordinary seed,
first coordinator, all-active boundary, accepted UP and its first sigma are
explicit internal restrictions. No successful follower tail at `k`, numerical
initialization, buffer validity, or status history is a calling premise. -/
theorem run_first_accepted_up_cutoff_chronology
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (span : start + count ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hfirst : initial.coordinator = .first) (i : Fin (p.m - 1))
    (seed : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hseed : initial.followers i = .ordinary seed memory) (hnone : seed.lastDown = none)
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
        start + 1 < u ∧ u ≤ start + k.val + 1 ∧ 0 < m ∧ m ≤ k.val ∧ b ≤ k.val ∧
        (∀ n : Fin E.records.length, j.val < n.val → n.val ≤ k.val →
          ∃ s mu, (actualChoice E.records[n.val] i).configuration = .ordinary s mu ∧
            s.lastDown = some message ∧ acceptedStart s = start + 1 ∧
            (s.status = .unoccupied ↔ m ≤ n.val)) ∧
        (∀ (n : Fin E.records.length) (_hjn : j.val ≤ n.val) (hnk : n.val < k.val),
          ∃ sOut muOut choice choiceMemory,
            E.records[n.val].output.next.followers i = .ordinary sOut muOut ∧
            sOut.lastDown = some message ∧ acceptedStart sOut = start + 1 ∧
            (sOut.status = .unoccupied ↔ m ≤ n.val) ∧
            (actualChoice E.records[n.val] i).configuration = .ordinary choice choiceMemory ∧
            (sOut.status ≠ .unoccupied → muOut.lastProposalRead =
              some ⟨E.records[n.val].input.time, bits E.records[n.val].input.time⟩) ∧
            (sOut.status = .unoccupied → muOut = choiceMemory) ∧
            ∃ nextChoice,
              (actualChoice (E.records[n.val + 1]'(lt_of_le_of_lt (Nat.succ_le_of_lt hnk) k.isLt)) i).configuration =
                .ordinary nextChoice muOut) ∧
        (∀ n : Fin E.records.length, j.val < n.val → n.val < k.val →
          ∀ sigma, ¬ ReferenceFollowerReplyChronology.appliedDown E.records[n.val] i sigma) ∧
        ∃ hb : b < E.records.length, ∃ s mu,
          (actualChoice E.records[b] i).configuration = .ordinary s mu ∧
          s.status = .unoccupied ∧ s.lastDown = some message ∧
          U.val.S = s.S ∧ U.val.q = s.backlog ∧ U.val.delta = s.delta := by
  classical
  let E := ReferenceActivePhysicalHorizon.run initial rows J rewards start count span active
  obtain ⟨j, hjk, message, hretained, hmessage, sender, last, lastMemory,
      hsender, hlastChoice, hlastStatus, hlastDown, hS, hdelta, hq⟩ :=
    ReferenceFirstAcceptedUpNumericSnapshot.acceptedUp_first_assignment_prior_down
      initial rows J rewards start count span active i seed memory hseed hnone k U haccepted hsigma
  have hk : k.val < E.records.length := k.isLt
  have hj : j.val < E.records.length := j.isLt
  change ReferenceAcceptedUpFollowerHistory.RetainedDown E.records[j.val] i message at hretained
  subst sender
  change (actualChoice E.records[k.val] i).configuration = .ordinary last lastMemory at hlastChoice
  have hlastStart : acceptedStart last = start + 1 := by
    simp only [acceptedStart, hlastDown, hmessage]
  let bits := FollowerCutoffScan.completeRowProposalBit p rate.eta.val (rows J)
  let u := FollowerCutoffScan.firstCutoff p rate.eta.val
    (ActiveFollowerDownAcceptance.downStart p rate message) bits
  have hcoord := run_retained_start_eq initial rows J rewards start count span active
    hfirst i j message hretained hmessage
  have hubounds := FollowerCutoffScan.firstCutoff_bounds p rate.eta.val rate.eta.property
    rate.sourceCap (ActiveFollowerDownAcceptance.downStart p rate message) bits
  have hu : start + 1 < u := by dsimp only [u]; omega
  obtain ⟨hstarts, hno⟩ := run_same_down_interval initial rows J rewards start count span active
    i j k hjk message hretained hmessage last lastMemory hlastChoice hlastDown
  change (∀ (n : Fin E.records.length), j.val < n.val → n.val ≤ k.val →
    ∀ (s : ReferencePrelaunchFollower.State p rate.eta) (mu : ActiveFollowerLifecycle.LocalMemory p),
      (actualChoice E.records[n.val] i).configuration = .ordinary s mu → acceptedStart s = start + 1) at hstarts
  change (∀ (n : Fin E.records.length), j.val < n.val → n.val < k.val →
    ∀ sigma, ¬ ReferenceFollowerReplyChronology.appliedDown E.records[n.val] i sigma) at hno
  have hstep (n : Fin E.records.length) (hnk : n.val < k.val)
      (s : ReferencePrelaunchFollower.State p rate.eta) (mu : ActiveFollowerLifecycle.LocalMemory p)
      (ho : E.records[n.val].output.next.followers i = .ordinary s mu)
      (hd : s.lastDown = some message)
      (hst : s.status = .unoccupied ↔ u ≤ start + n.val + 1)
      (hr : s.status ≠ .unoccupied → mu.lastProposalRead =
        some ⟨E.records[n.val].input.time, bits E.records[n.val].input.time⟩) :
      ∃ c cm, (actualChoice (E.records[n.val + 1]'(by omega)) i).configuration = .ordinary c cm ∧
        c.lastDown = some message ∧ cm = mu ∧
        (c.status = .unoccupied ↔ u ≤ start + (n.val + 1) + 1) :=
    run_next_status initial rows J rewards start count span active
      i k message hmessage last lastMemory hlastChoice n hnk s mu ho hd hst hr
  have hall := run_status_outputs initial rows J rewards start count span active
    i j k hjk message hretained hmessage last lastMemory hlastChoice hlastDown
  have htrace (n : Fin E.records.length) (hjn : j.val < n.val) (hnk : n.val ≤ k.val) :
      ∃ s mu, (actualChoice E.records[n.val] i).configuration = .ordinary s mu ∧
        s.lastDown = some message ∧ acceptedStart s = start + 1 ∧
        (s.status = .unoccupied ↔ u - (start + 1) ≤ n.val) := by
    let prev : Fin E.records.length := ⟨n.val - 1, by omega⟩
    obtain ⟨s, mu, _c, _cm, ho, hd, hst, _hc, _hkeep, hr⟩ :=
      hall prev.val (by dsimp only [prev]; omega) (by dsimp only [prev]; omega)
    obtain ⟨c, cm, hc, hcd, _, hcst⟩ := hstep prev (by dsimp only [prev]; omega) s mu ho hd hst hr
    have hnprev : prev.val + 1 = n.val := by dsimp only [prev]; omega
    have hcN : (actualChoice E.records[n.val] i).configuration = .ordinary c cm := by
      simpa only [hnprev] using hc
    have hcstN : c.status = .unoccupied ↔ u ≤ start + n.val + 1 := by
      simpa only [hnprev] using hcst
    refine ⟨c, cm, hcN, hcd, hstarts n hjn hnk c cm hcN, ?_⟩
    exact hcstN.trans (by omega)
  obtain ⟨ks, km, hkc, _hkd, _hks, hkst⟩ := htrace k hjk le_rfl
  have hke : ks = last := (LocalConfiguration.ordinary.inj (hkc.symm.trans hlastChoice)).1
  have hmk : u - (start + 1) ≤ k.val := hkst.mp (hke ▸ hlastStatus)
  have hub : u ≤ start + k.val + 1 := by omega
  let b := max (u - (start + 1)) (j.val + 1)
  have hbk : b ≤ k.val := max_le hmk (by omega)
  let boundary : Fin E.records.length := ⟨b, by omega⟩
  obtain ⟨bs, bm, hbc, hbd, hbs, hbst⟩ := htrace boundary
    (by dsimp only [boundary, b]; omega) hbk
  have hbu : bs.status = .unoccupied := hbst.mpr (Nat.le_max_left _ _)
  have hconst := ReferenceFollowerReplyChronology.run_unoccupied_reply_const initial rows J rewards
    start count span active i boundary k hbk bs last bm lastMemory hbc hlastChoice hbu
      (hbs.trans hlastStart.symm)
  have hmpos : 0 < u - (start + 1) := by omega
  refine ⟨j, hjk, message, hretained, hmessage, hu, hub, hmpos, hmk, hbk, htrace, ?_, hno,
    boundary.isLt, bs, bm, hbc, hbu, hbd, hS.trans hconst.2.2.1,
    hq.trans hconst.2.2.2.2, hdelta.trans hconst.2.2.2.1⟩
  intro n hjn hnk
  obtain ⟨out, outMemory, c, cm, hout, hd, hst, hc, hkeep, hr⟩ := hall n.val hjn hnk
  obtain ⟨next, nextMemory, hnext, _hnextDown, hmemory, _hnextStatus⟩ := hstep n hnk out outMemory hout hd hst hr
  have hindex : u ≤ start + n.val + 1 ↔ u - (start + 1) ≤ n.val := by omega
  refine ⟨out, outMemory, c, cm, hout, hd, ?_, hst.trans hindex, hc, hr, hkeep, next, ?_⟩
  · simp only [acceptedStart, hd, hmessage]
  · rw [← hmemory]
    exact hnext

section ActualLaunch

/-- The same chronology at the original conditional launched boundary.
All source, reward, private-array, initialization-relation and handoff inputs
are retained. The launch premises themselves are not established here. -/
theorem ofActualLaunchedBoundary_first_accepted_up_cutoff_chronology
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
        start + 1 < u ∧ u ≤ start + k.val + 1 ∧ 0 < m ∧ m ≤ k.val ∧ replyIndex ≤ k.val ∧
        (∀ n : Fin E.records.length, j.val < n.val → n.val ≤ k.val →
          ∃ s mu, (actualChoice (E.records[n.val]'(n.isLt)) i).configuration = .ordinary s mu ∧
            s.lastDown = some message ∧ acceptedStart s = start + 1 ∧
            (s.status = .unoccupied ↔ m ≤ n.val)) ∧
        (∀ (n : Fin E.records.length) (_hjn : j.val ≤ n.val) (hnk : n.val < k.val),
          ∃ sOut muOut choice choiceMemory,
            (E.records[n.val]'(n.isLt)).output.next.followers i = .ordinary sOut muOut ∧
            sOut.lastDown = some message ∧ acceptedStart sOut = start + 1 ∧
            (sOut.status = .unoccupied ↔ m ≤ n.val) ∧
            (actualChoice (E.records[n.val]'(n.isLt)) i).configuration = .ordinary choice choiceMemory ∧
            (sOut.status ≠ .unoccupied → muOut.lastProposalRead =
              some ⟨(E.records[n.val]'(n.isLt)).input.time, bits (E.records[n.val]'(n.isLt)).input.time⟩) ∧
            (sOut.status = .unoccupied → muOut = choiceMemory) ∧
            ∃ nextChoice,
              (actualChoice (E.records[n.val + 1]'(lt_of_le_of_lt (Nat.succ_le_of_lt hnk) k.isLt)) i).configuration =
                .ordinary nextChoice muOut) ∧
        (∀ n : Fin E.records.length, j.val < n.val → n.val < k.val →
          ∀ sigma, ¬ ReferenceFollowerReplyChronology.appliedDown (E.records[n.val]'(n.isLt)) i sigma) ∧
        ∃ hb : replyIndex < E.records.length, ∃ s mu,
          (actualChoice (E.records[replyIndex]'(hb)) i).configuration = .ordinary s mu ∧
          s.status = .unoccupied ∧ s.lastDown = some message ∧
          U.val.S = s.S ∧ U.val.q = s.backlog ∧ U.val.delta = s.delta := by
  dsimp only
  obtain ⟨hfirst, _hactive, seed, memory, hseed, _hS, _hdelta, _hq, hnone,
      _hstatus, _hvalid, _hpair, _htime⟩ :=
    ReferenceFirstAcceptedUpNumericSnapshot.actual_launched_follower_local_invariants
      source rewards launchRate C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed hlaunched i
  exact run_first_accepted_up_cutoff_chronology
    (ActualInitializationLaunchState.ofActualLaunchedBoundary source rewards launchRate
      C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed hlaunched)
    source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
    (BootstrapObservedFollower.blockStop p (ReferenceInitializationRun.nextBlock b h)) count span
    (ReferenceFirstAcceptedUpNumericSnapshot.actual_launched_follower_local_invariants
      source rewards launchRate C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed hlaunched i).2.1
    hfirst i seed memory hseed hnone k U haccepted hsigma

end ActualLaunch

end Bandits.Support.ReferenceFirstUpCutoffChronology

end
