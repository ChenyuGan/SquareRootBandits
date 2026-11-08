/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionNumericalReplay
public import Bandits.Support.ReferenceFirstLaunchNumericalCell
public import Bandits.Support.ReferenceFirstLiveFollowerSafety
public import Bandits.Support.ReferenceFirstCutoffRecordedService

/-!
# Choice-time offered UP sender replay

Sources: `sources/zip4/manuscript/06_interruptions.tex:192-233,246-297,301-344`,
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-64`, and
`sources/zip4/manuscript/04_slow_fast_learner.tex:157-174`.

All replay records below are the existing literal first-reply projection of
an actual physical run. The operation leaves are reproved locally from the
public lifecycle and checked-operation interfaces; private upstream proofs
are evidence only. Current receiver and finish success are never premises.

The generated result stops at strict prior-DOWN diagnostics. Its identification
with the same first-cutoff payload after a late DOWN acceptance remains open;
the complete requested generated sender replay theorem is not exported.
-/

@[expose] public section

noncomputable section

open Bandits.Support ConstructorDimensions ReferencePrelaunchFollower
open DeclaredFollowerLocalRound ReferenceFollowerFixedReply

namespace Bandits.Support.ReferenceFirstOfferedUpNumericalReplay

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

/-- Conditional local operation result. The retained DOWN and its first
sigma are explicit inputs here; this lemma alone is not a generated-root
producer. Ordinary current CHOICE supplies every past ordinary focal output. -/
theorem choice_replay_of_retained_first_down
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
    (hlastDown : last.lastDown = some message) (hlastStatus : last.status = .unoccupied) :
    let E := ReferenceActivePhysicalHorizon.run initial rows J rewards start count span active
    let bits := FollowerCutoffScan.completeRowProposalBit p rate.eta.val (rows J)
    let u := FollowerCutoffScan.firstCutoff p rate.eta.val
      (ActiveFollowerDownAcceptance.downStart p rate message) bits
    let m := u - (start + 1)
    let d := max m (j.val + 1)
    let V := fun h => QueueReplay.replay (4 * rate.n) (0, 0)
      (ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords E.records i j.val message h)
    start + 1 < u ∧ 0 < m ∧ m ≤ k.val ∧ d ≤ k.val ∧
      last.S = (V m).1 ∧ last.backlog = (V m).2 ∧
      last.delta = (V m).1 - (V (m - 1)).1 := by
  let E := ReferenceActivePhysicalHorizon.run initial rows J rewards start count span active
  let bits := FollowerCutoffScan.completeRowProposalBit p rate.eta.val (rows J)
  let u := FollowerCutoffScan.firstCutoff p rate.eta.val
    (ActiveFollowerDownAcceptance.downStart p rate message) bits
  let m := u - (start + 1)
  let b := max m (j.val + 1)
  let V := fun h => QueueReplay.replay (4 * rate.n) (0, 0)
    (ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords E.records i j.val message h)
  have hk : k.val < E.records.length := k.isLt
  have hstart := ActiveFollowerDownAcceptance.downStart_val_add_one p rate message
  have hubounds := FollowerCutoffScan.firstCutoff_bounds p rate.eta.val rate.eta.property
    rate.sourceCap (ActiveFollowerDownAcceptance.downStart p rate message) bits
  have hu : start + 1 < u := by dsimp only [u]; omega
  have hmpos : 0 < m := Nat.sub_pos_of_lt hu
  have hordinary := run_ordinary_prefix initial rows J rewards start count span active
    i k last lastMemory hlastChoice
  have hall := run_status_outputs initial rows J rewards start count span active
    i j k hjk message hretained hmessage last lastMemory hlastChoice hlastDown
  have htrace (n : Fin E.records.length) (hjn : j.val < n.val) (hnk : n.val ≤ k.val) :
      ∃ s mu, (actualChoice E.records[n.val] i).configuration = .ordinary s mu ∧
        s.lastDown = some message ∧ (s.status = .unoccupied ↔ m ≤ n.val) := by
    let prev : Fin E.records.length := ⟨n.val - 1, by omega⟩
    obtain ⟨s, mu, _c, _cm, ho, hd, hst, _hc, _hkeep, hr⟩ :=
      hall prev.val (by dsimp only [prev]; omega) (by dsimp only [prev]; omega)
    obtain ⟨c, cm, hc, hcd, _, hcst⟩ := run_next_status initial rows J rewards start count span active
      i k message hmessage last lastMemory hlastChoice prev (by dsimp only [prev]; omega) s mu ho hd hst hr
    have hnprev : prev.val + 1 = n.val := by dsimp only [prev]; omega
    change c.status = .unoccupied ↔ u ≤ start + (prev.val + 1) + 1 at hcst
    refine ⟨c, cm, ?_, hcd, ?_⟩
    · simpa only [hnprev] using hc
    · rw [hnprev] at hcst
      exact hcst.trans (by dsimp only [m]; omega)
  obtain ⟨ks, km, hkc, _hkd, hkst⟩ := htrace k hjk le_rfl
  have hke : ks = last := (LocalConfiguration.ordinary.inj (hkc.symm.trans hlastChoice)).1
  have hmk : m ≤ k.val := hkst.mp (hke ▸ hlastStatus)
  have hbk : b ≤ k.val := max_le hmk (by omega)
  let boundaryIndex : Fin E.records.length := ⟨b, by omega⟩
  obtain ⟨boundary, boundaryMemory, hbc, hbd, hbst⟩ := htrace boundaryIndex
    (by dsimp only [boundaryIndex, b]; omega) hbk
  have hbu : boundary.status = .unoccupied := hbst.mpr (Nat.le_max_left _ _)
  have hconst := ReferenceFollowerReplyChronology.run_unoccupied_reply_const initial rows J rewards
    start count span active i boundaryIndex k hbk boundary last boundaryMemory lastMemory hbc hlastChoice hbu
      (by simp only [acceptedStart, hbd, hlastDown])
  have hb : b < E.records.length := boundaryIndex.isLt
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
  obtain ⟨out0, outMemory0, hout0⟩ := hordinary.1 j hjk
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
        obtain ⟨choice, choiceMemory, hcc, hcd, hcstatus⟩ :=
          htrace index hjprev (by change prev ≤ k.val; omega)
        have hoccupied : choice.status ≠ .unoccupied := by
          intro he
          have hh := hcstatus.mp he
          change m ≤ prev at hh
          omega
        obtain ⟨hchoicePair, _hchoiceDelta⟩ :=
          ih prev hprevn hprev hjprev (by omega) choice choiceMemory hcc
        rw [Nat.min_eq_right (Nat.le_of_lt hprevm)] at hchoicePair
        obtain ⟨out, outMemory, hout⟩ :=
          hordinary.1 index (by change prev < k.val; omega)
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
  exact ⟨hu, hmpos, hmk, hbk,
    hconst.2.2.1.trans (congrArg Prod.fst hboundaryPair),
    hconst.2.2.2.2.trans (congrArg Prod.snd hboundaryPair),
    hconst.2.2.2.1.trans hboundaryDelta⟩

private theorem logAt_contribution_le
    (message : ReferenceFirstAcceptedUpNumericSnapshot.DownRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (activation : Activation p) (time : Fin p.T) (own : Fin p.K × Observation p) :
    SparseCalendarReplay.sparseBufferContribution (p.m - 1) (D p : ℝ) rate.eta.val
      message.val.h (PrelaunchBufferRecovery.downArm rate.eta message) (time.val + 1)
      (ReferencePrelaunchFollower.logAt i row activation time own) ≤ D p := by
  classical
  unfold ReferencePrelaunchFollower.logAt
  split
  · simp only [SparseCalendarReplay.sparseBufferContribution, List.foldr_cons,
      List.foldr_nil, Nat.add_zero]
    split
    · unfold SparseCalendarReplay.savedContribution
      split
      · have hf := ActiveFollowerQueueOperation.sourceArrivalFloor_le_D rate.eta message own.2
        rw [ActiveFollowerQueueOperation.sourceArrivalFloor_eq_savedFloor] at hf
        exact hf
      · exact Nat.zero_le _
    · exact Nat.zero_le _
  · exact Nat.zero_le _

/-- A physical sparse emission has at most one saved arrival; the bound uses
its actual quantized own observation and the DOWN record's admissible rate. -/
theorem emission_contribution_le_D
    (message : ReferenceFirstAcceptedUpNumericSnapshot.DownRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1))
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) :
    ReferenceFollowerSparseEmissionRecovery.emissionContribution message i record ≤ D p := by
  classical
  unfold ReferenceFollowerSparseEmissionRecovery.emissionContribution
    ReferenceFollowerBufferProvenance.logEmission
  dsimp only
  cases (record.output.preparation.followers.followers i).configuration with
  | dagger => exact Nat.zero_le _
  | ordinary state memory =>
    dsimp only
    split
    · exact logAt_contribution_le message i _ _ _ _
    · exact Nat.zero_le _

private theorem replay_mass_le (capacity bound : ℕ) (initial : ℕ × ℕ)
    (records : List (Bool × ℕ)) (harrival : ∀ r ∈ records, r.2 ≤ bound) :
    (QueueReplay.replay capacity initial records).1 +
      (QueueReplay.replay capacity initial records).2 ≤
        initial.1 + initial.2 + records.length * bound := by
  induction records generalizing initial with
  | nil => simp only [QueueReplay.replay, List.foldl_nil, List.length_nil,
      Nat.zero_mul, Nat.add_zero, le_refl]
  | cons r rest ih =>
    have ha := harrival r List.mem_cons_self
    have htail := ih (QueueReplay.transition capacity initial r)
      (fun v hv => harrival v (List.mem_cons_of_mem _ hv))
    have hstep : (QueueReplay.transition capacity initial r).1 +
        (QueueReplay.transition capacity initial r).2 ≤ initial.1 + initial.2 + bound := by
      cases r with
      | mk enabled arrival =>
        cases enabled <;> simp only [QueueReplay.transition, Bool.false_eq_true,
          ite_false, ite_true]
        · omega
        · have hmin := Nat.min_le_right capacity (initial.2 + arrival)
          omega
    change (QueueReplay.replay capacity (QueueReplay.transition capacity initial r) rest).1 +
      (QueueReplay.replay capacity (QueueReplay.transition capacity initial r) rest).2 ≤ _
    calc
      _ ≤ (QueueReplay.transition capacity initial r).1 +
          (QueueReplay.transition capacity initial r).2 + rest.length * bound := htail
      _ ≤ initial.1 + initial.2 + bound + rest.length * bound := Nat.add_le_add_right hstep _
      _ = initial.1 + initial.2 + (r :: rest).length * bound := by
        simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
        omega

/-- Length, every arrival, every prefix's joint mass, and the final service
bound for the literal first-reply stream. No source Delta identity is used. -/
theorem first_reply_queue_records_bounds
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (i : Fin (p.m - 1)) (j m : ℕ)
    (message : ReferenceFirstAcceptedUpNumericSnapshot.DownRecord (p := p) (rate := rate))
    (hm : m ≤ records.length) :
    let Frec := ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords records i j message m
    let V := fun h => QueueReplay.replay (4 * rate.n) (0, 0)
      (ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords records i j message h)
    Frec.length = m ∧ (∀ r ∈ Frec, r.2 ≤ D p) ∧
      (∀ h ≤ m, (V h).1 + (V h).2 ≤ h * D p) ∧
      (V m).1 - (V (m - 1)).1 ≤ 4 * rate.n ∧ 4 * rate.n ≤ D p := by
  classical
  have hlength (h : ℕ) (hh : h ≤ records.length) :
      (ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords records i j message h).length = h := by
    simp only [ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords,
      List.length_map, List.length_zipIdx, List.length_take, Nat.min_eq_left hh]
  have harrival (h : ℕ) : ∀ r ∈
      ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords records i j message h, r.2 ≤ D p := by
    intro r hr
    obtain ⟨⟨record, n⟩, _hrecord, rfl⟩ := List.mem_map.mp hr
    dsimp only
    split
    · exact emission_contribution_le_D message i record
    · exact ActiveFollowerQueueOperation.rawArrival_le_D rate.eta i _ _ message _
  refine ⟨hlength m hm, harrival m, ?_, ?_, ?_⟩
  · intro h hh
    have hb := replay_mass_le (4 * rate.n) (D p) (0, 0) _ (harrival h)
    simpa only [Nat.zero_add, hlength h (hh.trans hm)] using hb
  · cases m with
    | zero => simp only [Nat.zero_sub, Nat.sub_self, Nat.zero_le]
    | succ n =>
      have hn : n < records.length := by omega
      have he : ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords records i j message (n + 1) =
          ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords records i j message n ++
            [(true, if n ≤ j then ReferenceFollowerSparseEmissionRecovery.emissionContribution message i records[n]
              else ActiveFollowerQueueOperation.rawArrival rate.eta i records[n].input.row records[n].input.time
                message (records[n].output.ownEntries (PublicDiscreteDraws.followerPlayer p.two_le_m i)).2)] := by
        unfold ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords
        rw [List.take_succ_eq_append_getElem hn, List.zipIdx_append, List.map_append]
        simp only [List.length_take, Nat.min_eq_left (Nat.le_of_lt hn), Nat.zero_add,
          List.zipIdx_cons, List.zipIdx_nil, List.map_cons, List.map_nil]
      dsimp only
      rw [Nat.add_sub_cancel, he, QueueReplay.replay_append]
      simp only [QueueReplay.replay, List.foldl_cons, List.foldl_nil, QueueReplay.transition, ite_true]
      exact (Nat.add_sub_cancel_left _ _).le.trans (Nat.min_le_left _ _)
  · exact ActiveFollowerQueueOperation.serviceCapacity_le_D rate.eta rate.sourceCap rate.n rate.n_scale

/-- A retained DOWN in the actual first live window has the first one-based
sigma and zero queue seed, obtained from its selected original payload. The
membership restriction is explicit and is not extended to late acceptances. -/
theorem first_live_retained_down_fields
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (span : start + count ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hfirst : initial.coordinator = .first) :
    let E := ReferenceActivePhysicalHorizon.run initial rows J rewards start count span active
    let W := ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records
    ∀ (j : Fin W.length) (i : Fin (p.m - 1))
      (message : ReferenceFirstAcceptedUpNumericSnapshot.DownRecord (p := p) (rate := rate)),
      ReferenceAcceptedUpFollowerHistory.RetainedDown W[j.val] i message →
        message.val.sigma = start + 1 ∧ message.val.q = 0 := by
  intro E W j i message hretained
  obtain ⟨logged, cut, after, raw, scan, registers, lastService, hinput, hdown, ha⟩ := hretained
  obtain ⟨_c, _cm, logged', _hc, _hu, _hl, hi, hcut⟩ :=
    ReferenceFollowerSparseEmissionRecovery.actualDownDiagnostic_choice W[j.val] i cut hdown
  have he : logged' = logged := Option.some.inj (hi.symm.trans hinput)
  subst logged'
  rw [hcut] at ha
  obtain ⟨view, hv⟩ := ReferenceFollowerSparseEmissionRecovery.acceptedReferenceCut_someView
    _ _ _ _ _ logged logged after raw message scan registers lastService ha
  rw [hv] at ha
  have hfields := ReferenceActiveDataOwnership.referenceDown_accepted_fields view _ _ _ _
    logged logged after raw message scan registers lastService ha
  have halign := actualChoice_alignment W[j.val] i
  dsimp only [actualChoice] at halign
  rw [halign.2.1] at hfields
  obtain ⟨selected, hs, hsv⟩ := Option.map_eq_some_iff.mp hv
  have hmessage : message = selected.view.payload.downRecord i := by
    simpa only [hsv] using hfields.1
  obtain ⟨_birth, _hbirth, _htime, _hborn, hsigma, hzero⟩ :=
    ReferenceFirstDownRecoveryBudget.run_first_selected_payload
      initial rows J rewards start count span active hfirst j selected hs
  constructor
  · rw [hmessage]
    change selected.view.payload.sigma.val + 1 = start + 1
    rw [hsigma]
  · rw [hmessage]
    exact (selected.view.payload.downRecord_initialQueue i).trans (hzero _)

/-- Generated-source diagnostics before the current receiver. This produces
the genuine first-cutoff payload and the strict prior DOWN or actual zero
placeholder. It does not yet identify a post-cutoff retained DOWN with that
payload; consequently it is not the requested complete sender replay root. -/
theorem run_first_collection_offered_sender_diagnostics
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true) :
    let x0 := ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate
    let b0 := ReferenceInitializationRun.output x0
    let s := ReferenceInitializationRun.elapsed p b0.completed
    ∀ (count : ℕ) (hspan : s + count ≤ p.T),
    let initial := ReferenceFirstLaunchNumericalCell.launchState rate z rewards C_star C_h hc
    let rows := z.1.2
    let J := ActualInitializationPhysicalStep.selectedRowIndex p z
    let active := ReferenceFirstLaunchNumericalCell.launchState_allActiveAtStart rate z rewards C_star C_h hc
    let E := ReferenceActivePhysicalHorizon.run initial rows J rewards s count hspan active
    let W := ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records
    let w := W.length
    let B := ReferenceCollectionPhaseHistory.collectionWindow E.records w
    w < count → ∃ cut suffix, ∃
      (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
      (q : CoordinatorLiveServiceFinish.OwnedRegisters r) (base : Fin (p.m - 1) → ℕ),
      E.records = W ++ cut :: suffix ∧ cut.input.time.val = s + w ∧
      cut.input.state.coordinator = .live r q base ∧
      r.payload.sigma.val = s ∧ (∀ i, base i = 0) ∧
      (∃ birth, birth ∈ E.records ∧
        ReferenceAssignmentPayloadPersistence.InstallationBirth birth r.payload ∧
        birth.input.time.val = s ∧ ∃ installed birthSelection,
          birth.output.preparation.coordinator = .first (.chosen installed birthSelection) ∧
          installed.registers.payload = r.payload) ∧
      FollowerCutoffScan.firstCutoff p rate.eta.val r.payload.sigma
        (FollowerCutoffScan.completeRowProposalBit p rate.eta.val (rows J)) = s + w + 1 ∧
      ∀ (k : Fin B.length) (i : Fin (p.m - 1))
        (choice : ReferencePrelaunchFollower.State p rate.eta)
        (mu : ActiveFollowerLifecycle.LocalMemory p)
        (M : OrdinaryMessageCodec.UpRecord (ReferencePrelaunchFollower.codecParams p rate.eta)),
        let prepared := actualChoice B[k.val] i
        prepared.configuration = .ordinary choice mu →
        ActiveFollowerQueueOperation.checkedUpOffer rate.eta prepared.follower prepared.row
          prepared.activation prepared.time choice = .offer M →
        ReferenceUpReception.currentOfferWord rate B[k.val].input.row i B[k.val].input.time prepared
          (actualChoice_alignment B[k.val] i).1 (actualChoice_alignment B[k.val] i).2.1
          (actualChoice_alignment B[k.val] i).2.2 =
          some ((OrdinaryMessageCodec.wordEquivFlat (CoordinatorCollectionLedger.codecParams p rate.eta.val))
            (OrdinaryMessageCodec.encodeUp (CoordinatorCollectionLedger.codecParams p rate.eta.val) M)) ∧
        M.val = ActiveFollowerQueueOperation.upOfferFields choice ∧ choice.status = .unoccupied ∧
        ((choice.lastDown = none ∧ M.val = OrdinaryMessageCodec.upPlaceholder) ∨
          ∃ (a j : Fin E.records.length)
            (message : ReferenceFirstAcceptedUpNumericSnapshot.DownRecord (p := p) (rate := rate)),
            B[k.val] = E.records[a.val] ∧ j.val < a.val ∧
            ReferenceAcceptedUpFollowerHistory.RetainedDown E.records[j.val] i message ∧
            choice.lastDown = some message) := by
  intro x0 b0 s count hspan initial rows J active E W w B hshort
  obtain ⟨_, _hactive, _, hfirst, _, _, _, hseeds⟩ :=
    ReferenceFirstLaunchNumericalCell.actual_launch_seed rate z rewards C_star C_h hc
  obtain ⟨cut, suffix, hsplit, _hindex, hcutTime, _hactual, r, q, base,
      hinput, hprefix, hcall⟩ :=
    ReferenceFirstCutoffOutsideInitialization.run_first_cutoff_outside_initializer
      initial rows J rewards s count hspan active hfirst hshort
  dsimp only at hcall
  obtain ⟨dispatched, _hstart, ledger, _hinit, _hledger, _hdomain, _hclock,
      _hpending, _hnoAssignment, selected, _hbranch, _hwpos, hsigma, hbase,
      hbirth, _hbits, _hdiagnostic, _hu, _hpositive, _hT, _hgrid, _hgridT,
      _hledgerSigma, _hledgerCut, _hfreeze, hfirstCutoff, _hrest⟩ := hcall
  have hcutState : cut.input.state.coordinator = .live r q base := by rw [hinput]; exact hprefix
  have hbirthFull : ∃ birth, birth ∈ E.records ∧
      ReferenceAssignmentPayloadPersistence.InstallationBirth birth r.payload ∧ birth.input.time.val = s ∧
        ∃ installed birthSelection,
          birth.output.preparation.coordinator = .first (.chosen installed birthSelection) ∧
          installed.registers.payload = r.payload := by
    obtain ⟨birth, hb, hborn, ht, hinstalled⟩ := hbirth
    have hpre : (ReferenceActivePhysicalHorizon.run initial rows J rewards s w (by omega) active).records.IsPrefix
        E.records := by
      obtain ⟨tail, he⟩ := ReferenceCollectionPhaseHistory.run_records_prefix
        initial rows J rewards s w (count - w) (by omega) active
      exact ⟨tail, by simpa only [Nat.add_sub_of_le (Nat.le_of_lt hshort)] using he.symm⟩
    exact ⟨birth, hpre.sublist.subset hb, hborn, ht, hinstalled⟩
  refine ⟨cut, suffix, r, q, base, hsplit, hcutTime, hcutState, hsigma, hbase, hbirthFull,
    ?_, ?_⟩
  · simpa only [hcutTime] using hfirstCutoff
  intro k i choice mu M prepared hcq hoff
  have hmem : B[k.val] ∈ E.records := by
    have hb := List.getElem_mem k.isLt
    change B[k.val] ∈ (E.records.drop w).take 1 ++
      (E.records.drop (w + 1)).takeWhile (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input) at hb
    rcases List.mem_append.mp hb with h | h
    · exact List.mem_of_mem_drop (List.mem_of_mem_take h)
    · exact List.mem_of_mem_drop ((List.takeWhile_prefix _).sublist.subset h)
  obtain ⟨a, ha, he⟩ := List.mem_iff_getElem.mp hmem
  let index : Fin E.records.length := ⟨a, ha⟩
  have hcq' : (actualChoice E.records[a] i).configuration = .ordinary choice mu := by rw [he]; exact hcq
  have hword := ReferenceUpReception.currentOfferWord_eq_encoded_offer rate B[k.val].input.row i
    B[k.val].input.time prepared (actualChoice_alignment B[k.val] i).1
    (actualChoice_alignment B[k.val] i).2.1 (actualChoice_alignment B[k.val] i).2.2 choice mu hcq M hoff
  have hfields := ActiveFollowerQueueOperation.checkedUpOffer_fields rate.eta _ _ _ _ choice M hoff
  have hstatus : choice.status = .unoccupied := by
    have h := hoff
    unfold ActiveFollowerQueueOperation.checkedUpOffer at h
    split at h
    · split at h
      · rename_i hselected
        exact hselected.2
      · cases h
    · cases h
  refine ⟨hword, hfields, hstatus, ?_⟩
  cases hd : choice.lastDown with
  | none =>
    obtain ⟨hseed, _hnone, hstart, hS, hdelta, hbacklog, hu, _⟩ := hseeds i
    have hzero : acceptedStart choice = 0 := by simp only [acceptedStart, hd]
    obtain ⟨_, hr⟩ := (ReferenceFollowerReplyChronology.run_initial_to_choice initial rows J rewards
      s count hspan active i index _ choice _ mu hseed hcq').2.1 hu (hstart.trans hzero.symm)
    exact Or.inl ⟨rfl, checked_offer_is_placeholder_of_zero_registers _ _ _ _ choice hzero
      ((congrArg (fun v => v.2.1) hr).trans hS)
      ((congrArg (fun v => v.2.2.1) hr).trans hdelta)
      ((congrArg (fun v => v.2.2.2) hr).trans hbacklog) M hoff⟩
  | some message =>
    have hseedAll : ReferenceFirstLiveConfirmationHistory.InitialFollowers initial := by
      intro j state memory hs
      obtain ⟨hj, hn, _, _, _, _, hu, _⟩ := hseeds j
      rw [hj] at hs
      cases hs
      exact ⟨hu, hn⟩
    obtain ⟨j, hj, hretained⟩ := ReferenceFirstLiveConfirmationHistory.run_choice_prior_down
      initial rows J rewards s count hspan active hseedAll index i choice mu hcq' message hd
    exact Or.inr ⟨index, ⟨j, hj.trans ha⟩, message, he.symm, hj, hretained, rfl⟩

end Bandits.Support.ReferenceFirstOfferedUpNumericalReplay

end
