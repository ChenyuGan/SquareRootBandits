/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceAssignmentFollowerMassSteps

import Lean.Elab.Tactic.Omega

/-!
# Complete actual follower cutoff phase

The actual complete suffix carries each follower's cutoff status and the
previous-row proposal token for its retained DOWN record. This fold proves
that local invariant from the corrected launch and actual ordinary endpoints;
it does not use numerical credit or coordinator birth provenance.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ReferenceCompleteFollowerCutoffPhase

open ConstructorDimensions
open ReferenceActivePhysicalStep
open ReferenceActivePhysicalHorizon

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

private theorem release_finish_occupied
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (t : Fin p.T) (observation : ReferencePrelaunchFollower.Observation p)
    (before post next : ReferencePrelaunchFollower.State p rate.eta)
    (memory nextMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hpost : post.status ≠ .unoccupied)
    (h : DeclaredFollowerLocalRound.releaseAndFinish rate i row t observation
      before memory post = .ok (next, nextMemory)) :
    next.status ≠ .unoccupied := by
  unfold DeclaredFollowerLocalRound.releaseAndFinish at h
  cases hr : ActiveFollowerLifecycle.releaseAfterService rate.eta i t
      (ActiveFollowerLifecycle.publicRowOfCompleteRow row t) observation before post with
  | error reason => rw [hr] at h; cases h
  | ok released =>
    simp only [hr] at h
    cases hf : ActiveFollowerLifecycle.finishRound rate.eta t row released memory with
    | error reason => rw [hf] at h; cases h
    | ok result =>
      have heq : result = (next, nextMemory) :=
        Except.ok.inj (by simpa only [hf] using h)
      rw [heq] at hf
      have hframe := ActiveFollowerLifecycle.finishRound_frame rate.eta t row released
        next memory nextMemory hf
      rw [hframe]
      unfold ActiveFollowerLifecycle.releaseAfterService at hr
      split at hr
      · split at hr
        · split at hr
          · cases hr
          · split at hr
            · split at hr
              · split at hr
                · dsimp only at hr
                  split at hr
                  · cases hr; intro hbad; cases hbad
                  · cases hr
                · dsimp only at hr
                  split at hr
                  · cases hr; exact hpost
                  · cases hr
              · cases hr
            · cases hr
        · cases hr
      · cases hr; exact hpost

private theorem occupied_record_status
    (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (activation : ReferencePrelaunchFollower.Activation p) (t : Fin p.T)
    (active : activation.val ≤ t.val + 1) (arm : Fin p.K)
    (observation : ReferencePrelaunchFollower.Observation p)
    (choice post : ReferencePrelaunchFollower.State p rate.eta)
    (hoccupied : choice.status ≠ .unoccupied)
    (hrecord : (ReferenceActivePhysicalStep.recordFollower
      view i row activation t active arm
      observation choice).result = .ok post) :
    post.status = choice.status := by
  have hlogged := hrecord
  rw [ReferenceActivePhysicalStep.recordFollower_result] at hlogged
  unfold ReferenceDownReception.loggingThenReferenceDown at hlogged
  simp only [dite_eq_right hoccupied] at hlogged
  unfold DeclaredFollowerLocalRound.recordOrServiceThenDown at hlogged
  simp only [dite_eq_right hoccupied] at hlogged
  cases hservice : ActiveFollowerQueueOperation.checkedService rate.eta rate.sourceCap
      rate.n rate.n_scale i row activation t observation choice with
  | failure => simp only [hservice] at hlogged; cases hlogged
  | success result =>
    simp only [hservice] at hlogged
    have hstate : result.output = post := Except.ok.inj hlogged
    subst post
    rw [result.queueUpdate]
    exact (ActiveFollowerQueueOperation.serviceOutput_preserves_other_registers
      rate.n choice result.arrival).2.2.2.1

private theorem record_output_phase_token
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1)) (next : ReferencePrelaunchFollower.State p rate.eta)
    (nextMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hnext : record.output.next.followers i = .ordinary next nextMemory)
    (M : OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))
    (hnextDown : next.lastDown = some M)
    (hinvariant : ∀ (before : ReferencePrelaunchFollower.State p rate.eta)
      (memory : ActiveFollowerLifecycle.LocalMemory p)
      (M₀ : OrdinaryMessageCodec.DownRecord
        (ReferencePrelaunchFollower.codecParams p rate.eta)),
      record.input.state.followers i = .ordinary before memory →
      before.lastDown = some M₀ →
      (before.status = .unoccupied ↔
        FollowerCutoffScan.firstCutoff p rate.eta.val
          (ActiveFollowerDownAcceptance.downStart p rate M₀)
          (FollowerCutoffScan.completeRowProposalBit p rate.eta.val record.input.row) ≤
            record.input.time.val) ∧
      (before.status ≠ .unoccupied → ∃ stamp : Fin p.T,
        stamp.val + 1 = record.input.time.val ∧
        memory.lastProposalRead = some ⟨stamp,
          FollowerCutoffScan.completeRowProposalBit p rate.eta.val record.input.row stamp⟩)) :
    (next.status = .unoccupied ↔
      FollowerCutoffScan.firstCutoff p rate.eta.val
        (ActiveFollowerDownAcceptance.downStart p rate M)
        (FollowerCutoffScan.completeRowProposalBit p rate.eta.val record.input.row) ≤
          record.input.time.val + 1) ∧
    (next.status ≠ .unoccupied →
      nextMemory.lastProposalRead = some ⟨record.input.time,
        FollowerCutoffScan.completeRowProposalBit p rate.eta.val
          record.input.row record.input.time⟩) := by
  have htoken := ReferenceAssignmentFollowerMassSteps.record_output_proposal_token
    record i next nextMemory hnext
  have hroundFollower := ReferenceFollowerBufferProvenance.roundRecord_follower_eq_finishFollower
    i record
  rcases record with ⟨input, output, houtput⟩
  cases houtput
  change (ReferenceActivePhysicalStep.finishFollower _ _ _).configuration =
    .ordinary next nextMemory at hnext
  let prepared := (ReferenceActivePhysicalStep.prepare input).followers.followers i
  let view := (ReferenceActivePhysicalStep.prepare input).coordinator.downView
  let observation := (ReferenceActivePhysicalStep.prepare input).feedback.observations
    (PublicDiscreteDraws.followerPlayer p.two_le_m i)
  obtain ⟨choice, choiceMemory, post, hchoice, hrecord, hrelease,
      _hdownInput, hfinishDown⟩ :=
    ReferenceFollowerReplyChronology.finishFollower_ordinary_inversion
      view prepared observation next nextMemory hnext
  have hprepareEq : prepared = DeclaredFollowerLocalRound.prepare rate i input.row
      (input.state.activations i) input.time (input.active i) (input.state.followers i) := by
    exact (ReferenceActivePhysicalStep.prepare input).followers.followers_eq i
  rw [hprepareEq] at hchoice
  obtain ⟨before, memory, hinput, hstart, _hpreparedReply, _hprepareUnoccupied⟩ :=
    ReferenceFollowerReplyChronology.prepare_ordinary_inversion
      i input.row (input.state.activations i) input.time (input.active i)
      (input.state.followers i) choice choiceMemory hchoice
  have halignment := (ReferenceActivePhysicalStep.prepare input).follower_alignment i
  have hreleaseFrame := ReferenceFollowerReplyChronology.releaseAndFinish_frame
    prepared.follower prepared.row prepared.time observation choice post next
    choiceMemory nextMemory hrelease
  obtain hpostLast | ⟨logged, cut, raw, accepted, scan, registers, lastService,
      hdownInput, hdown, hcut, haccepted, _hstrict, hacceptedLast⟩ :=
    ReferenceFollowerReplyChronology.recordFollower_ordinary_inversion
      view prepared.follower prepared.row prepared.activation prepared.time prepared.active
      prepared.arm observation choice post hrecord
  · have hnextLast : next.lastDown = choice.lastDown := by
      have hreplyLast := congrArg Prod.fst hreleaseFrame.1
      exact hreplyLast.trans hpostLast.1
    have hbeforeLast : before.lastDown = some M := by
      have heq : choice.lastDown = some M := hnextLast.symm.trans hnextDown
      exact (congrArg Prod.fst _hpreparedReply).symm.trans heq
    obtain ⟨hphase, htokenInput⟩ := hinvariant before memory M hinput hbeforeLast
    have hphasePrepared := hphase
    rw [← halignment.1, ← halignment.2.2.1] at hphasePrepared
    have htokenPrepared := htokenInput
    rw [← halignment.1, ← halignment.2.2.1] at htokenPrepared
    have hstartPrepared := hstart
    rw [← halignment.2.2.1] at hstartPrepared
    have hpreparePhase := ReferenceAssignmentFollowerMassSteps.start_round_cutoff_status
      prepared.time prepared.row before choice memory choiceMemory M hbeforeLast hphasePrepared
      htokenPrepared hstartPrepared
    have hpreparePhaseRecord := hpreparePhase
    rw [halignment.1, halignment.2.2.1] at hpreparePhaseRecord
    have hstatusEquiv : next.status = .unoccupied ↔ choice.status = .unoccupied := by
      by_cases hchoiceUnoccupied : choice.status = .unoccupied
      · obtain ⟨_hreply, hpostUnoccupied⟩ := hpostLast.2 hchoiceUnoccupied
        have hnextUnoccupied : next.status = .unoccupied := by
          rw [(hreleaseFrame.2 hchoiceUnoccupied), hpostUnoccupied]
        exact iff_of_true hnextUnoccupied hchoiceUnoccupied
      · have hpostStatus := occupied_record_status view prepared.follower prepared.row
          prepared.activation prepared.time prepared.active prepared.arm observation
          choice post hchoiceUnoccupied hrecord
        have hpostOccupied : post.status ≠ .unoccupied := by
          rw [hpostStatus]
          exact hchoiceUnoccupied
        have hnextOccupied := release_finish_occupied prepared.follower prepared.row
          prepared.time observation choice post next choiceMemory nextMemory hpostOccupied hrelease
        constructor
        · intro hnextUnoccupied
          exact (hnextOccupied hnextUnoccupied).elim
        · intro hchoiceUnoccupied'
          exact (hchoiceUnoccupied hchoiceUnoccupied').elim
    refine ⟨hstatusEquiv.trans hpreparePhaseRecord, ?_⟩
    intro hoccupied
    exact htoken hoccupied
  · have hnextLast : next.lastDown = post.lastDown := congrArg Prod.fst hreleaseFrame.1
    have hacceptedEq : accepted = M := Option.some.inj (hacceptedLast.symm.trans
      (hnextLast.symm.trans hnextDown))
    subst accepted
    have hdownPhysical : ((ReferenceActivePhysicalStep.step input).followers i).down =
        some cut := by
      rw [hroundFollower]
      exact hfinishDown.trans hdown
    obtain ⟨choice', choiceMemory', _logged', hchoice', hchoiceUnoccupied,
        _hlogging, _hdownInput', _hcut'⟩ :=
      ReferenceFollowerSparseEmissionRecovery.actualDownDiagnostic_choice
        ⟨input, ReferenceActivePhysicalStep.step input, rfl⟩ i cut hdownPhysical
    have heqChoice := (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
      (hchoice'.symm.trans hchoice)).1
    have hchoiceUnoccupied' : choice.status = .unoccupied := heqChoice ▸ hchoiceUnoccupied
    have hnoMismatch := ReferenceFollowerSparseEmissionRecovery.acceptedReferenceCut_not_rawMismatch
      view prepared.follower prepared.row prepared.time observation logged post raw M scan
      registers lastService (by rw [hcut] at haccepted; exact haccepted)
    have htransitionEq := ReferenceDownReception.referenceDownCut_outcome_eq_downTransition_of_no_raw_mismatch
      view prepared.follower prepared.row prepared.time observation rate logged hnoMismatch
    have htransition : ActiveFollowerDownAcceptance.downTransition p prepared.follower
        prepared.row prepared.time observation rate logged =
        .accepted logged post raw M scan registers lastService := by
      calc
        _ = (ReferenceDownReception.referenceDownCut p view prepared.follower prepared.row
            prepared.time observation rate logged).outcome := htransitionEq.symm
        _ = cut.outcome := by rw [← hcut]
        _ = .accepted logged post raw M scan registers lastService := haccepted
    have hscan := ReferenceAssignmentFollowerMassSteps.accepted_down_scan_endpoint
      prepared.follower prepared.row prepared.time observation logged post raw M scan registers
      lastService htransition
    obtain ⟨_hparsed, _hchecked, _hinterval, _hnextTime, _hhorizon, _hraw, hafter⟩ :=
      ActiveFollowerDownAcceptance.downTransition_accepted_checked p prepared.follower
        prepared.row prepared.time observation rate logged post raw M scan registers lastService
        htransition
    have hacceptedPhase : post.status = .unoccupied ↔
        FollowerCutoffScan.firstCutoff p rate.eta.val
          (ActiveFollowerDownAcceptance.downStart p rate M)
          (FollowerCutoffScan.completeRowProposalBit p rate.eta.val prepared.row) ≤
            prepared.time.val + 1 := by
      rw [hafter]
      dsimp only
      rw [hscan]
      let cutoff := FollowerCutoffScan.firstCutoff p rate.eta.val
          (ActiveFollowerDownAcceptance.downStart p rate M)
          (FollowerCutoffScan.completeRowProposalBit p rate.eta.val prepared.row)
      change (if Nat.min cutoff (prepared.time.val + 2) = prepared.time.val + 2 then
        ActiveRoundActions.FollowerStatus.pending else
        ActiveRoundActions.FollowerStatus.unoccupied) = .unoccupied ↔
          cutoff ≤ prepared.time.val + 1
      by_cases hcutoff : cutoff ≤ prepared.time.val + 1
      · have hmin : Nat.min cutoff (prepared.time.val + 2) = cutoff :=
          Nat.min_eq_left (by omega)
        rw [hmin]
        have hne : cutoff ≠ prepared.time.val + 2 := by omega
        simp [hcutoff, hne]
      · have hmin : Nat.min cutoff (prepared.time.val + 2) = prepared.time.val + 2 :=
          Nat.min_eq_right (by omega)
        rw [hmin]
        simp [hcutoff]
    have hnextStatus := hreleaseFrame.2 hchoiceUnoccupied'
    have hacceptedPhaseRecord := hacceptedPhase
    rw [halignment.1, halignment.2.2.1] at hacceptedPhaseRecord
    refine ⟨?_, ?_⟩
    · rw [hnextStatus]
      exact hacceptedPhaseRecord
    · intro hoccupied
      exact htoken hoccupied

private theorem connected_phase_token_fold
    {initial final : ReferenceActivePhysicalStep.State p rate}
    {records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))}
    (hconnected : ReferenceActivePhysicalHorizon.Connected initial records final)
    (row : CompletePublicTable.CompleteRow p) (start : ℕ)
    (hdata : ∀ n (hn : n < records.length),
      records[n].input.time.val = start + n ∧ records[n].input.row = row)
    (hinitial : ∀ (i : Fin (p.m - 1)) (F : ReferencePrelaunchFollower.State p rate.eta)
      (memory : ActiveFollowerLifecycle.LocalMemory p)
      (M : OrdinaryMessageCodec.DownRecord
        (ReferencePrelaunchFollower.codecParams p rate.eta)),
      initial.followers i = .ordinary F memory → F.lastDown = some M →
      (F.status = .unoccupied ↔
        FollowerCutoffScan.firstCutoff p rate.eta.val
          (ActiveFollowerDownAcceptance.downStart p rate M)
          (FollowerCutoffScan.completeRowProposalBit p rate.eta.val row) ≤ start) ∧
      (F.status ≠ .unoccupied → ∃ stamp : Fin p.T,
        stamp.val + 1 = start ∧ memory.lastProposalRead = some ⟨stamp,
          FollowerCutoffScan.completeRowProposalBit p rate.eta.val row stamp⟩)) :
    ∀ (i : Fin (p.m - 1)) (F : ReferencePrelaunchFollower.State p rate.eta)
      (memory : ActiveFollowerLifecycle.LocalMemory p)
      (M : OrdinaryMessageCodec.DownRecord
        (ReferencePrelaunchFollower.codecParams p rate.eta)),
      final.followers i = .ordinary F memory → F.lastDown = some M →
      (F.status = .unoccupied ↔
        FollowerCutoffScan.firstCutoff p rate.eta.val
          (ActiveFollowerDownAcceptance.downStart p rate M)
          (FollowerCutoffScan.completeRowProposalBit p rate.eta.val row) ≤
            start + records.length) ∧
      (F.status ≠ .unoccupied → ∃ stamp : Fin p.T,
        stamp.val + 1 = start + records.length ∧ memory.lastProposalRead = some ⟨stamp,
          FollowerCutoffScan.completeRowProposalBit p rate.eta.val row stamp⟩) := by
  induction records generalizing initial final start with
  | nil =>
      intro i F memory M hfinal hdown
      have hstate : final = initial := hconnected
      subst final
      exact hinitial i F memory M hfinal hdown
  | cons record rest ih =>
      intro i F memory M hfinal hdown
      rcases hconnected with ⟨hpre, htail⟩
      have hfirstData : record.input.time.val = start ∧ record.input.row = row := by
        have hhead := hdata 0 (by simp)
        change record.input.time.val = start + 0 ∧ record.input.row = row at hhead
        simpa only [Nat.add_zero] using hhead
      have hinputInvariant : ∀ (j : Fin (p.m - 1))
          (before : ReferencePrelaunchFollower.State p rate.eta)
          (memoryBefore : ActiveFollowerLifecycle.LocalMemory p)
          (M₀ : OrdinaryMessageCodec.DownRecord
            (ReferencePrelaunchFollower.codecParams p rate.eta)),
          record.input.state.followers j = .ordinary before memoryBefore →
          before.lastDown = some M₀ →
          (before.status = .unoccupied ↔
            FollowerCutoffScan.firstCutoff p rate.eta.val
              (ActiveFollowerDownAcceptance.downStart p rate M₀)
              (FollowerCutoffScan.completeRowProposalBit p rate.eta.val record.input.row) ≤
                record.input.time.val) ∧
          (before.status ≠ .unoccupied → ∃ stamp : Fin p.T,
            stamp.val + 1 = record.input.time.val ∧ memoryBefore.lastProposalRead = some ⟨stamp,
              FollowerCutoffScan.completeRowProposalBit p rate.eta.val record.input.row stamp⟩) := by
        intro j before memoryBefore M₀ hbefore hbeforeDown
        have hinitialConfig : initial.followers j = .ordinary before memoryBefore := by
          rw [← hpre]
          exact hbefore
        obtain ⟨hphase, htoken⟩ := hinitial j before memoryBefore M₀
          hinitialConfig hbeforeDown
        constructor
        · rw [← hfirstData.2, ← hfirstData.1] at hphase
          exact hphase
        · intro hoccupied
          obtain ⟨stamp, hstamp, hread⟩ := htoken hoccupied
          refine ⟨stamp, ?_, ?_⟩
          · rw [← hfirstData.1] at hstamp
            exact hstamp
          · rw [← hfirstData.2] at hread
            exact hread
      have houtputInvariant : ∀ (j : Fin (p.m - 1))
          (F' : ReferencePrelaunchFollower.State p rate.eta)
          (memory' : ActiveFollowerLifecycle.LocalMemory p)
          (M' : OrdinaryMessageCodec.DownRecord
            (ReferencePrelaunchFollower.codecParams p rate.eta)),
          record.output.next.followers j = .ordinary F' memory' →
          F'.lastDown = some M' →
          (F'.status = .unoccupied ↔
            FollowerCutoffScan.firstCutoff p rate.eta.val
              (ActiveFollowerDownAcceptance.downStart p rate M')
              (FollowerCutoffScan.completeRowProposalBit p rate.eta.val row) ≤ start + 1) ∧
          (F'.status ≠ .unoccupied → ∃ stamp : Fin p.T,
            stamp.val + 1 = start + 1 ∧ memory'.lastProposalRead = some ⟨stamp,
              FollowerCutoffScan.completeRowProposalBit p rate.eta.val row stamp⟩) := by
        intro j F' memory' M' hconfiguration hdown'
        have hout := record_output_phase_token record j F' memory' hconfiguration M'
          hdown' (by
            intro before memoryBefore M₀ hbefore hbeforeDown
            exact hinputInvariant j before memoryBefore M₀ hbefore hbeforeDown)
        refine ⟨?_, ?_⟩
        · have hphase := hout.1
          rw [hfirstData.2, hfirstData.1] at hphase
          exact hphase
        · intro hoccupied
          have htokenCurrent := ReferenceAssignmentFollowerMassSteps.record_output_proposal_token
            record j F' memory' hconfiguration hoccupied
          refine ⟨record.input.time, ?_, ?_⟩
          · rw [hfirstData.1]
          · rw [← hfirstData.2]
            exact htokenCurrent
      have htailData : ∀ n (hn : n < rest.length),
          rest[n].input.time.val = (start + 1) + n ∧ rest[n].input.row = row := by
        intro n hn
        have h := hdata (n + 1) (by simp at hn ⊢; omega)
        have h' : rest[n].input.time.val = start + (n + 1) ∧ rest[n].input.row = row := by
          simpa only [List.getElem_cons_succ] using h
        exact ⟨by omega, h'.2⟩
      have htailInitial : ∀ (j : Fin (p.m - 1))
          (F' : ReferencePrelaunchFollower.State p rate.eta)
          (memory' : ActiveFollowerLifecycle.LocalMemory p)
          (M' : OrdinaryMessageCodec.DownRecord
            (ReferencePrelaunchFollower.codecParams p rate.eta)),
          record.output.next.followers j = .ordinary F' memory' →
          F'.lastDown = some M' →
          (F'.status = .unoccupied ↔
            FollowerCutoffScan.firstCutoff p rate.eta.val
              (ActiveFollowerDownAcceptance.downStart p rate M')
              (FollowerCutoffScan.completeRowProposalBit p rate.eta.val row) ≤ start + 1) ∧
          (F'.status ≠ .unoccupied → ∃ stamp : Fin p.T,
            stamp.val + 1 = start + 1 ∧ memory'.lastProposalRead = some ⟨stamp,
              FollowerCutoffScan.completeRowProposalBit p rate.eta.val row stamp⟩) := by
        exact houtputInvariant
      have hfinal' := ih htail (start + 1) htailData htailInitial
      have hlen : start + 1 + rest.length = start + (record :: rest).length := by simp; omega
      simpa only [hlen] using hfinal' i F memory M hfinal hdown

private theorem complete_ordinary_follower_phase_token
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (i : Fin (p.m - 1)) (F : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hordinary : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[k.val].input.state.followers i = .ordinary F memory)
    (M : OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))
    (hdown : F.lastDown = some M) :
    (F.status = .unoccupied ↔
      FollowerCutoffScan.firstCutoff p rate.eta.val
        (ActiveFollowerDownAcceptance.downStart p rate M)
        (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
          (ReferenceCompletePhysicalHistory.completeSuffixRecords
            rate source rewards C_star C_h)[k.val].input.row) ≤
          (ReferenceCompletePhysicalHistory.completeSuffixRecords
            rate source rewards C_star C_h)[k.val].input.time.val) ∧
    (F.status ≠ .unoccupied → ∃ stamp : Fin p.T,
      stamp.val + 1 =
        (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h)[k.val].input.time.val ∧
      memory.lastProposalRead = some ⟨stamp,
        FollowerCutoffScan.completeRowProposalBit p rate.eta.val
          (ReferenceCompletePhysicalHistory.completeSuffixRecords
            rate source rewards C_star C_h)[k.val].input.row stamp⟩) := by
  cases hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h with
  | none =>
      have hempty : ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h = [] := by
        simp only [ReferenceCompletePhysicalHistory.completeSuffixRecords, hlaunch,
          ↓reduceDIte]
      have hk := k.isLt
      simp only [hempty, List.length_nil] at hk
      omega
  | some active =>
      have hc := (ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
        rate source rewards C_star C_h).mp (by rw [hlaunch]; rfl)
      let initial := ReferenceFirstLaunchNumericalCell.launchState
        rate source rewards C_star C_h hc
      let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
        rate source rewards C_star C_h hc
      let start := ReferenceCompletePhysicalHistory.physicalStart
        rate source rewards C_star C_h
      have hspan : start + (p.T - start) ≤ p.T := by
        have hs := ReferenceCompletePhysicalHistory.physicalStart_le_T
          rate source rewards C_star C_h
        dsimp only [start]
        omega
      have hrecords := ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
        rate source rewards C_star C_h initial
        (ReferenceFirstLaunchNumericalCell.correctedLaunch_eq_some_launchState
          rate source rewards C_star C_h hc)
      let execution := ReferenceActivePhysicalHorizon.run initial source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start
        (p.T - start) hspan seed.activeAtStart
      have hrun : ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h = execution.records := hrecords
      have hk : k.val < execution.records.length := by rw [← hrun]; exact k.isLt
      have hinput : execution.records[k.val].input.state.followers i = .ordinary F memory := by
        simpa only [hrun] using hordinary
      have hseed : ∀ (j : Fin (p.m - 1))
          (G : ReferencePrelaunchFollower.State p rate.eta)
          (mu : ActiveFollowerLifecycle.LocalMemory p),
          initial.followers j = .ordinary G mu → G.lastDown = none := by
        intro j G mu hconfiguration
        obtain ⟨_hfirst, _hactive, hfollowers⟩ :=
          ReferenceAssignmentFollowerMassSteps.actual_launch_mass_seed
            rate rewards C_star C_h source hc
        exact (hfollowers j G mu hconfiguration).1
      have hprefix := ReferenceFollowerReplyChronology.connected_take_to_input
        execution.connected k.val hk
      have hdataAll : ∀ n (hn : n < execution.records.length),
          execution.records[n].input.time.val = start + n ∧
            execution.records[n].input.row = source.1.2
              (ActualInitializationPhysicalStep.selectedRowIndex p source) := by
        intro n hn
        have hnR : n < (ReferenceCompletePhysicalHistory.completeSuffixRecords
            rate source rewards C_star C_h).length := by rw [hrun]; exact hn
        have htimeR := ReferenceAssignmentFollowerMassSteps.complete_record_time
          rate rewards C_star C_h source ⟨n, hnR⟩
        have htime : execution.records[n].input.time.val = start + n := by
          simpa only [hrun, start] using htimeR
        have hmem : execution.records[n] ∈ execution.records := List.get_mem _ _
        obtain ⟨hrows, hselected, _hrewards⟩ :=
          ReferenceActivePhysicalHorizon.run_record_inputs initial source.1.2
            (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start
            (p.T - start) hspan seed.activeAtStart (execution.records[n]) hmem
        have hrow : execution.records[n].input.row = source.1.2
            (ActualInitializationPhysicalStep.selectedRowIndex p source) := by
          change execution.records[n].input.rows execution.records[n].input.selected = _
          rw [hrows, hselected]
        exact ⟨htime, hrow⟩
      have hdataPrefix : ∀ n (hn : n < (execution.records.take k.val).length),
          (execution.records.take k.val)[n].input.time.val = start + n ∧
            (execution.records.take k.val)[n].input.row = source.1.2
              (ActualInitializationPhysicalStep.selectedRowIndex p source) := by
        intro n hn
        have hn' : n < execution.records.length := by
          have htake : (execution.records.take k.val).length =
              min k.val execution.records.length := List.length_take
          rw [htake] at hn
          omega
        have h := hdataAll n hn'
        simpa using h
      have hseedInvariant : ∀ (j : Fin (p.m - 1))
          (G : ReferencePrelaunchFollower.State p rate.eta)
          (mu : ActiveFollowerLifecycle.LocalMemory p)
          (N : OrdinaryMessageCodec.DownRecord
            (ReferencePrelaunchFollower.codecParams p rate.eta)),
          initial.followers j = .ordinary G mu → G.lastDown = some N →
          (G.status = .unoccupied ↔
            FollowerCutoffScan.firstCutoff p rate.eta.val
              (ActiveFollowerDownAcceptance.downStart p rate N)
              (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
                (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source))) ≤ start) ∧
          (G.status ≠ .unoccupied → ∃ stamp : Fin p.T,
            stamp.val + 1 = start ∧ mu.lastProposalRead = some ⟨stamp,
              FollowerCutoffScan.completeRowProposalBit p rate.eta.val
                (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)) stamp⟩) := by
        intro j G mu N hconfiguration hdown'
        have hnone := hseed j G mu hconfiguration
        rw [hnone] at hdown'
        cases hdown'
      have hfold := connected_phase_token_fold hprefix
        (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source))
        start hdataPrefix hseedInvariant
      have hfinal := hfold i F memory M hinput hdown
      have hprefixLength : (execution.records.take k.val).length = k.val := by
        rw [List.length_take]
        omega
      have htimeR := ReferenceAssignmentFollowerMassSteps.complete_record_time
        rate rewards C_star C_h source k
      have htime : execution.records[k.val].input.time.val = start + k.val := by
        simpa only [hrun, start] using htimeR
      have hrow : execution.records[k.val].input.row =
          source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) :=
        (hdataAll k.val hk).2
      have hresult := by simpa only [hprefixLength] using hfinal
      have hresult' := hresult
      simpa only [hrun, htime, hrow] using hresult'

/-- The actual ordinary input's unoccupied status is exactly its retained
DOWN's first complete-row cutoff by the current calendar time. -/
theorem complete_ordinary_follower_phase
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (i : Fin (p.m - 1)) (F : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hordinary : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[k.val].input.state.followers i = .ordinary F memory)
    (M : OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))
    (hdown : F.lastDown = some M) :
    F.status = .unoccupied ↔
      FollowerCutoffScan.firstCutoff p rate.eta.val
        (ActiveFollowerDownAcceptance.downStart p rate M)
        (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
          (ReferenceCompletePhysicalHistory.completeSuffixRecords
            rate source rewards C_star C_h)[k.val].input.row) ≤
        (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h)[k.val].input.time.val := by
  exact (complete_ordinary_follower_phase_token rate rewards C_star C_h source k i F memory
    hordinary M hdown).1

/-- Every occupied actual ordinary input has the proposal token read from the
same complete source row in the immediately preceding physical round. -/
theorem complete_ordinary_follower_token
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (i : Fin (p.m - 1)) (F : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hordinary : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[k.val].input.state.followers i = .ordinary F memory)
    (hoccupied : F.status ≠ .unoccupied) :
    ∃ stamp : Fin p.T,
      stamp.val + 1 =
        (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h)[k.val].input.time.val ∧
      memory.lastProposalRead = some ⟨stamp,
        FollowerCutoffScan.completeRowProposalBit p rate.eta.val
          (ReferenceCompletePhysicalHistory.completeSuffixRecords
            rate source rewards C_star C_h)[k.val].input.row stamp⟩ := by
  cases hlast : F.lastDown with
  | none =>
      have hzero := ReferenceAssignmentFollowerMassSteps.complete_no_down_input
        rate rewards C_star C_h source k i F memory hordinary hlast
      exact (hoccupied hzero.2.2.2).elim
  | some M =>
      exact (complete_ordinary_follower_phase_token rate rewards C_star C_h source k i F memory
        hordinary M hlast).2 hoccupied

end Bandits.Support.ReferenceCompleteFollowerCutoffPhase

end
