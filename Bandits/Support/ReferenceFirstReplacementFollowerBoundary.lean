/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstReplacementLiveFollowerPrefix

/-!
# Actual follower boundaries in the first replacement's continuing prefix

Sources: `sources/zip4/manuscript/05_binary_transport.tex:354-431`,
`06_interruptions.tex:9-70,193-233,246-295`,
`04_slow_fast_learner.tex:157-188`, and
`appendix_a_local_protocol.tex:28-79`.

The induction uses the computed finite slice of the original physical records.
It retains full follower states, decoder buffers, proposal memories, the whole
installed payload, original private arrays and reward table. The initial queue
credit is the actual NEW DOWN credit and may be nonzero. These are internal
physical-prefix results; they assert neither coordinator survival at the cutoff
nor sparse-stream queue/score identity nor manuscript closure.
-/

@[expose] public section
noncomputable section

namespace Bandits.Support.ReferenceFirstReplacementFollowerBoundary

open ConstructorDimensions ReferenceActivePhysicalStep ReferenceActivePhysicalHorizon
open ReferencePrelaunchFollower ActiveFollowerLifecycle ActiveFollowerDownAcceptance
open ReferenceDownReception PublicDiscreteDraws
open ReferenceFirstReplacementLiveFollowerPrefix ReferenceFirstReplacementNextFollowerStep

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

/-- The visible local induction invariant. Its witnesses are constructed from
birth and preserved by the actual local operation, never supplied to a root. -/
private def boundaryInput
    (r : RoundRecord (p := p) (rate := rate)) (payload : Payload rate)
    (i : Fin (p.m - 1)) (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : LocalMemory p) : Prop :=
  r.input.state.followers i = .ordinary state memory ∧
  localStateDomainValid state ∧ state.S + state.backlog ≤ r.input.time.val * D p ∧
  (state.lastDown = none → state.S = 0 ∧ state.delta = 0 ∧ state.backlog = 0) ∧
  (state.status = .unoccupied → acceptedStart state < (payload.downRecord i).val.sigma) ∧
  (state.status ≠ .unoccupied → state.lastDown = some (payload.downRecord i) ∧
    ∃ token, memory.lastProposalRead = some token ∧ token.timestamp.val + 1 = r.input.time.val ∧
      token.bit = FollowerCutoffScan.completeRowProposalBit p rate.eta.val r.input.row token.timestamp)

private theorem complete_adjacent
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (k : ℕ) (hk : k + 1 < (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
    (R.get ⟨k + 1, hk⟩).input.state =
      (R.get ⟨k, (Nat.lt_succ_self k).trans hk⟩).output.next ∧
    (R.get ⟨k + 1, hk⟩).input.time.val =
      (R.get ⟨k, (Nat.lt_succ_self k).trans hk⟩).input.time.val + 1 := by
  dsimp only
  obtain ⟨_, _, hr0⟩ := ReferenceLaterLiveNumericalReadout.source_record_prefix
    rate rewards C_star C_h source ⟨k, by omega⟩
  obtain ⟨_, _, hr1⟩ := ReferenceLaterLiveNumericalReadout.source_record_prefix
    rate rewards C_star C_h source ⟨k + 1, hk⟩
  rw [hr0, hr1]
  exact ⟨ReferenceAssignmentPayloadChronology.run_successor_finalState_eq_actualRunRecordAt
    _ source.1.2 _ rewards _ k _ _, rfl⟩

private theorem tail_adjacent
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (v n : ℕ)
    (hn : n + 1 < (continuingTail (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h) v).length) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
    let previous := (continuingTail R v).get ⟨n, show n < (continuingTail
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h) v).length by omega⟩
    let current := (continuingTail R v).get ⟨n + 1, hn⟩
    current.input.state = previous.output.next ∧
      current.input.time.val = previous.input.time.val + 1 := by
  dsimp only
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
  change n + 1 < (continuingTail R v).length at hn
  have hg0 := continuingTail_get R v ⟨n, by omega⟩
  have hg1 := continuingTail_get R v ⟨n + 1, hn⟩
  have hget0 : R.get ⟨v + 1 + n, (List.getElem?_eq_some_iff.mp hg0).1⟩ =
      (continuingTail R v).get ⟨n, by omega⟩ := (List.getElem?_eq_some_iff.mp hg0).2
  have hk1 : v + 1 + (n + 1) < R.length := (List.getElem?_eq_some_iff.mp hg1).1
  have hget1 : R.get ⟨v + 1 + n + 1, by
      have := (List.getElem?_eq_some_iff.mp hg1).1; omega⟩ =
      (continuingTail R v).get ⟨n + 1, hn⟩ := by
    have he : (⟨v + 1 + n + 1, by omega⟩ : Fin R.length) =
        ⟨v + 1 + (n + 1), (List.getElem?_eq_some_iff.mp hg1).1⟩ :=
      Fin.ext (Nat.add_assoc _ _ _)
    rw [he]
    exact (List.getElem?_eq_some_iff.mp hg1).2
  have hadj := complete_adjacent rate source rewards C_star C_h (v + 1 + n) (by
    have := (List.getElem?_eq_some_iff.mp hg1).1; omega)
  dsimp only at hadj
  rw [hget0, hget1] at hadj
  exact hadj

private theorem tail_chronology
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (v : ℕ) (k : Fin (continuingTail (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h) v).length)
    (i : Fin (p.m - 1)) (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : LocalMemory p)
    (hi : ((continuingTail (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h) v).get k).input.state.followers i = .ordinary state memory) :
    state.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound) ∧
    ∀ saved ∈ state.buffer, saved.calendarRound <
      ((continuingTail (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h) v).get k).input.time.val + 1 := by
  have hg := continuingTail_get
    (ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h) v k
  have he : (ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h).get
      ⟨v + 1 + k.val, (List.getElem?_eq_some_iff.mp hg).1⟩ =
      (continuingTail (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h) v).get k := (List.getElem?_eq_some_iff.mp hg).2
  have h := complete_input_buffer_chronological rate source rewards C_star C_h
    ⟨v + 1 + k.val, (List.getElem?_eq_some_iff.mp hg).1⟩ i state memory (by rw [he]; exact hi)
  rw [he] at h
  exact h.2

private theorem complete_first_replacement_boundary_inputs
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
    let v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
    match R[v]? with
    | none => True
    | some birth => match birth.output.preparation.coordinator with
      | .collection _ _ _ _ (.laterChosen _ _ _ _ _ _ _ _ _ installed _) =>
        ∀ k : Fin (continuingTail R v).length, ∀ i : Fin (p.m - 1),
          ∃ state memory, boundaryInput ((continuingTail R v).get k) installed.registers.payload i state memory
      | _ => True := by
  classical
  have hgeometry := complete_first_replacement_continuing_geometry rate source rewards C_star C_h
  have hbirth := ReferenceFirstReplacementDownRecovery.complete_first_replacement_down_recovery_and_finish
    rate source rewards C_star C_h
  have hseed := ReferenceFirstReplacementFollowerLoggingSeed.complete_first_replacement_follower_logging_seed
    rate source rewards C_star C_h
  have hD := ReferenceFirstReplacementNextDownReplay.complete_first_replacement_next_unoccupied_recovery
    rate source rewards C_star C_h
  have hA := complete_first_replacement_next_preparation_and_occupied_step rate source rewards C_star C_h
  dsimp only at hgeometry hbirth hseed hD hA ⊢
  set R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
  set w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
  set v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
  cases hb : R[v]? with
  | none => trivial
  | some birth =>
    simp only [hb] at hgeometry hbirth hseed hD hA ⊢
    cases hc : birth.output.preparation.coordinator with
    | first _ => trivial
    | live _ _ _ _ => trivial
    | dagger => trivial
    | invalidCollectionCutoff => trivial
    | collection oldPayload ledger clock cutoff outcome =>
      rw [hc] at hgeometry hbirth hseed hD hA
      cases outcome <;> try trivial
      rename_i core consistent started hs instruction hi output hcons clockData installed arm
      dsimp only at hgeometry hbirth hseed hD hA ⊢
      have hcredit (i : Fin (p.m - 1)) : (installed.registers.payload.downRecord i).val.q ≤
          ((installed.registers.payload.downRecord i).val.sigma - 1) * D p := by
        obtain ⟨_, _, _, _, _, _, _, _, _, hstamp, hq, _⟩ := hbirth.2 i
        rw [hstamp, Nat.add_sub_cancel]
        exact hq
      suffices hall : ∀ n (hn : n < (continuingTail R v).length), ∀ i : Fin (p.m - 1),
          ∃ state memory, boundaryInput ((continuingTail R v).get ⟨n, hn⟩)
            installed.registers.payload i state memory by
        intro k i
        exact hall k.val k.isLt i
      intro n
      induction n with
      | zero =>
        intro hn i
        let r := (continuingTail R v).get ⟨0, hn⟩
        have hg := continuingTail_get R v ⟨0, hn⟩
        simp only [Nat.add_zero] at hg
        have hg' : R[v + 1]? = some r := hg
        rw [hg'] at hD hA
        dsimp only at hD hA
        have hcont : isContinuingChosen r = true := continuingTail_mem R v r (List.get_mem ..)
        cases hcut : r.output.preparation.coordinator <;>
          simp only [isContinuingChosen, hcut] at hcont
        all_goals try cases hcont
        rename_i registers owned base result
        cases result <;> simp only at hcont <;> try cases hcont
        rw [hcut] at hD
        obtain ⟨_, htime, _, _, _, _, _, _, _, _, _, _, _, _, _, hfollowers⟩ := hD
        obtain ⟨state, memory, hinput, hprep, hdomain, hmass, hdecision, hunocc⟩ := hfollowers i
        obtain ⟨astate, amemory, haprep, _hadomain, _hamass, habusy, before,
          _hbeforeDomain, _hbeforeOut, hainput, hastart, hacases⟩ := hA.2 i
        have he := hinput.symm.trans hainput
        simp only [DeclaredFollowerLocalRound.LocalConfiguration.ordinary.injEq] at he
        have heBefore := he.1
        have heMemory := he.2
        subst before
        subst amemory
        have hstartNoop : startRound rate.eta r.input.time state memory = .ok (state, memory) := by
          rw [startRound, hdecision]
          rfl
        have heState := (Prod.mk.inj (Except.ok.inj (hastart.symm.trans hstartNoop))).1
        subst astate
        refine ⟨state, memory, hinput, hdomain, hmass, ?_, ?_, ?_⟩
        · intro hnone
          by_cases hu : state.status = .unoccupied
          · obtain ⟨old, birthMemory, birthLogged, logged, hOldInput, _, _, _, _, hBirthLog,
              _, hBirthLast, hretained, hlog, hrest⟩ := hunocc hu
            obtain ⟨seedOld, seedMemory, seedLogged, hSeedInput, _, _, _, _, _, _, _, _, _, _, _, hold, _⟩ :=
              hseed.2.2.2.2.2.2.2 i
            have he := hOldInput.symm.trans hSeedInput
            simp only [DeclaredFollowerLocalRound.LocalConfiguration.ordinary.injEq] at he
            obtain ⟨rfl, _⟩ := he
            have hframe := ActiveFollowerLogging.checkedLogging_success_frame i birth.input.row
              (birth.input.state.activations i) birth.input.time _ old birthLogged hBirthLog
            have hlast : state.lastDown = old.lastDown := by
              rcases hretained with he | he <;> rw [he] <;> exact hBirthLast
            have hS : state.S = old.S := by
              rcases hretained with he | he <;> rw [he] <;> exact hframe.2.1
            have hd : state.delta = old.delta := by
              rcases hretained with he | he <;> rw [he] <;> exact hframe.2.2.1
            have hq : state.backlog = old.backlog := by
              rcases hretained with he | he <;> rw [he] <;> exact hframe.2.2.2.1
            rcases hold with hz | hp
            · exact ⟨hS.trans hz.2.1, hd.trans hz.2.2.1, hq.trans hz.2.2.2⟩
            · rw [hlast, hp] at hnone; cases hnone
          · rw [(habusy hu).1] at hnone; cases hnone
        · intro hu
          obtain ⟨old, bm, bl, logged, _, _, _, _, _, _, _, _, _, hlog,
            _, _, _, _, _, _, _, _, hstrict, _⟩ := hunocc hu
          have hf := ActiveFollowerLogging.checkedLogging_success_frame i r.input.row
            (r.input.state.activations i) r.input.time _ state logged hlog
          unfold acceptedStart
          rw [← hf.1]
          exact hstrict
        · intro hu
          refine ⟨(habusy hu).1, ?_⟩
          rcases hacases with ha | ⟨_, _, hread⟩
          · exact (hu ha).elim
          · refine ⟨⟨birth.input.time, FollowerCutoffScan.completeRowProposalBit
              p rate.eta.val birth.input.row birth.input.time⟩, hread, htime.symm, ?_⟩
            have hrow : r.input.row = birth.input.row := by
              obtain ⟨_, _, hrows, hJ, _⟩ := hgeometry.2 ⟨0, hn⟩
              change r.input.rows r.input.selected = birth.input.rows birth.input.selected
              rw [hrows, hJ, hseed.2.2.2.1, hseed.2.2.2.2.1]
            rw [hrow]
      | succ n ih =>
        intro hn i
        have hn0 : n < (continuingTail R v).length := by omega
        let previous := (continuingTail R v).get ⟨n, hn0⟩
        let current := (continuingTail R v).get ⟨n + 1, hn⟩
        obtain ⟨state, memory, hinput, hdomain, hmass, hzero, hstrict, hbusy⟩ := ih hn0 i
        obtain ⟨_, htime0, hrows0, hJ0, _, selected, hsel, hpay, _, hgrid, hbits⟩ :=
          hgeometry.2 ⟨n, hn0⟩
        obtain ⟨hp, ht⟩ := tail_chronology rate source rewards C_star C_h v ⟨n, hn0⟩ i state memory hinput
        have hstart : (installed.registers.payload.downRecord i).val.sigma ≤ previous.input.time.val := by
          change installed.registers.payload.sigma.val + 1 ≤ previous.input.time.val
          have hbTime := hgeometry.1
          dsimp only [previous] at *
          omega
        obtain ⟨next, nextMemory, _hdecision, _hprep, hout, _hfailure, _hflag,
          hdNext, hmNext, hzNext, hsNext, hbNext⟩ := local_follower_step_of_boundary
            previous installed.registers.payload selected hsel hpay i state memory hinput
            hdomain hmass hzero hstrict hbusy hp ht hstart (hcredit i) hgrid hbits
        have hadj := tail_adjacent rate source rewards C_star C_h v n hn
        change current.input.state = previous.output.next ∧
          current.input.time.val = previous.input.time.val + 1 at hadj
        have hrow : current.input.row = previous.input.row := by
          obtain ⟨_, _, hrows1, hJ1, _⟩ := hgeometry.2 ⟨n + 1, hn⟩
          change current.input.rows current.input.selected = previous.input.rows previous.input.selected
          rw [hrows0, hJ0, hrows1, hJ1]
        refine ⟨next, nextMemory, ?_, hdNext, ?_, hzNext, hsNext, ?_⟩
        · rw [hadj.1]
          have hf : previous.output.next.followers i = (previous.output.followers i).configuration := by
            rw [previous.output_eq]; rfl
          exact hf.trans hout
        · rw [hadj.2]; exact hmNext
        · intro hu
          obtain ⟨hdown, token, hread, hstamp, hbit⟩ := hbNext hu
          exact ⟨hdown, token, hread, hstamp.trans hadj.2.symm, by rw [hrow]; exact hbit⟩

/-- A successful release can only retain occupied status or release it; FINISH
retains the complete resulting state. All inputs to this local fact are shown. -/
private theorem release_finish_occupied
    (record : RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1)) (before post next : ReferencePrelaunchFollower.State p rate.eta)
    (memory nextMemory : LocalMemory p)
    (hpost : post.status ≠ .unoccupied)
    (h : DeclaredFollowerLocalRound.releaseAndFinish rate i record.input.row record.input.time
      (record.output.preparation.feedback.observations (followerPlayer p.two_le_m i))
      before memory post = .ok (next, nextMemory)) : next.status ≠ .unoccupied := by
  unfold DeclaredFollowerLocalRound.releaseAndFinish at h
  cases hr : releaseAfterService rate.eta i record.input.time (publicRowOfCompleteRow
      record.input.row record.input.time) _ before post with
  | error reason => rw [hr] at h; cases h
  | ok released =>
    simp only [hr] at h
    cases hf : finishRound rate.eta record.input.time record.input.row released memory with
    | error reason => rw [hf] at h; cases h
    | ok result =>
      have heq : result = (next, nextMemory) := Except.ok.inj (by simpa only [hf] using h)
      rw [heq] at hf
      have he := finishRound_frame rate.eta record.input.time record.input.row released next memory nextMemory hf
      rw [he]
      unfold releaseAfterService at hr
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

private theorem occupied_output_of_actual_finish
    (record : RoundRecord (p := p) (rate := rate)) (i : Fin (p.m - 1))
    (state next : ReferencePrelaunchFollower.State p rate.eta) (memory nextMemory : LocalMemory p)
    (hprepared : (record.output.preparation.followers.followers i).configuration = .ordinary state memory)
    (hdomain : localStateDomainValid state) (hmass : state.S + state.backlog ≤ record.input.time.val * D p)
    (M : OrdinaryMessageCodec.DownRecord (codecParams p rate.eta))
    (hdown : state.lastDown = some M) (hstart : M.val.sigma ≤ record.input.time.val)
    (hout : (record.output.followers i).configuration = .ordinary next nextMemory)
    (hbusy : state.status ≠ .unoccupied) : next.status ≠ .unoccupied := by
  obtain ⟨serviced, finished, _hservice, _hrecord, htail, hfinished, _⟩ :=
    occupied_actual_follower_finish record i state memory hprepared hbusy hdomain M hdown hstart hmass
  have hpost : serviced.output.status ≠ .unoccupied := by
    rw [serviced.queueUpdate]
    unfold ActiveFollowerQueueOperation.serviceOutput
    split <;> exact hbusy
  have hn := release_finish_occupied record i state serviced.output finished memory _ hpost htail
  have hconfiguration : (record.output.followers i).configuration = .ordinary finished
      ⟨some ⟨record.input.time, FollowerCutoffScan.completeRowProposalBit
        p rate.eta.val record.input.row record.input.time⟩⟩ := by rw [hfinished]
  have he := hconfiguration.symm.trans hout
  simp only [DeclaredFollowerLocalRound.LocalConfiguration.ordinary.injEq] at he
  rw [← he.1]
  exact hn

/-- Unconditional safety on the computed first-replacement continuing prefix.
Every local-step input is produced from the original birth and source run.
The selectors remain inside the result, including absent/other branches. -/
theorem complete_first_replacement_follower_boundary
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
    let v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
    match R[v]? with
    | none => True
    | some birth => match birth.output.preparation.coordinator with
      | .collection _ _ _ _ (.laterChosen _ _ _ _ _ _ _ _ _ installed _) =>
        ∀ k : Fin (continuingTail R v).length,
          let r := (continuingTail R v).get k
          R[v + 1 + k.val]? = some r ∧
          r.input.rows = source.1.2 ∧
          r.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p source ∧
          r.input.rewards = rewards ∧
          ∃ selected : Selection r.input,
            r.output.preparation.coordinator.selection = some selected ∧
            selected.view.payload = installed.registers.payload ∧
            CoordinatorLocalArmChoice.assignmentIsLive selected.view.payload selected.view.cutoff r.input.time ∧
            r.input.time.val + 2 ≤ FollowerCutoffScan.gridBoundary p rate.eta.val installed.registers.payload.sigma ∧
            (∀ j : Fin p.T, installed.registers.payload.sigma.val ≤ j.val → j.val < r.input.time.val →
              FollowerCutoffScan.completeRowProposalBit p rate.eta.val r.input.row j = false) ∧
            ∀ i : Fin (p.m - 1), ∃ state memory next nextMemory,
              r.input.state.followers i = .ordinary state memory ∧
              localStateDomainValid state ∧ state.S + state.backlog ≤ r.input.time.val * D p ∧
              (state.lastDown = none → state.S = 0 ∧ state.delta = 0 ∧ state.backlog = 0) ∧
              (state.status = .unoccupied → acceptedStart state < (installed.registers.payload.downRecord i).val.sigma) ∧
              (state.status ≠ .unoccupied → state.lastDown = some (installed.registers.payload.downRecord i) ∧
                ∃ token, memory.lastProposalRead = some token ∧ token.timestamp.val + 1 = r.input.time.val ∧
                  token.bit = FollowerCutoffScan.completeRowProposalBit p rate.eta.val r.input.row token.timestamp) ∧
              state.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound) ∧
              (∀ saved ∈ state.buffer, saved.calendarRound < r.input.time.val + 1) ∧
              (installed.registers.payload.downRecord i).val.sigma = installed.registers.payload.sigma.val + 1 ∧
              (installed.registers.payload.downRecord i).val.sigma ≤ r.input.time.val ∧
              (installed.registers.payload.downRecord i).val.q ≤
                ((installed.registers.payload.downRecord i).val.sigma - 1) * D p ∧
              interruptionDecision rate.eta r.input.time state memory = .ok false ∧
              (r.output.preparation.followers.followers i).configuration = .ordinary state memory ∧
              (r.output.followers i).configuration = .ordinary next nextMemory ∧
              (r.output.followers i).failure = none ∧
              next.initializationFailure = state.initializationFailure ∧
              localStateDomainValid next ∧ next.S + next.backlog ≤ (r.input.time.val + 1) * D p ∧
              next.delta ≤ D p ∧
              (next.lastDown = none → next.S = 0 ∧ next.delta = 0 ∧ next.backlog = 0) ∧
              (next.status = .unoccupied → acceptedStart next < (installed.registers.payload.downRecord i).val.sigma) ∧
              (next.status ≠ .unoccupied → next.lastDown = some (installed.registers.payload.downRecord i) ∧
                ∃ token, nextMemory.lastProposalRead = some token ∧ token.timestamp.val + 1 = r.input.time.val + 1 ∧
                  token.bit = FollowerCutoffScan.completeRowProposalBit p rate.eta.val r.input.row token.timestamp) ∧
              (state.status ≠ .unoccupied → next.status ≠ .unoccupied)
      | _ => True := by
  classical
  have hinputs := complete_first_replacement_boundary_inputs rate source rewards C_star C_h
  have hgeometry := complete_first_replacement_continuing_geometry rate source rewards C_star C_h
  have hbirth := ReferenceFirstReplacementDownRecovery.complete_first_replacement_down_recovery_and_finish
    rate source rewards C_star C_h
  dsimp only at hinputs hgeometry hbirth ⊢
  set R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
  set w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
  set v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
  cases hb : R[v]? with
  | none => trivial
  | some birth =>
    simp only [hb] at hinputs hgeometry hbirth ⊢
    cases hc : birth.output.preparation.coordinator with
    | first _ => trivial
    | live _ _ _ _ => trivial
    | dagger => trivial
    | invalidCollectionCutoff => trivial
    | collection old ledger clock cutoff outcome =>
      rw [hc] at hinputs hgeometry hbirth
      cases outcome <;> try trivial
      rename_i core consistent started hs instruction hi output hcons clockData installed arm
      dsimp only at hinputs hgeometry hbirth ⊢
      intro k
      let r := (continuingTail R v).get k
      obtain ⟨hindex, htime, hrows, hJ, hrewards, selected, hsel, hpay, hlive, hgrid, hbits⟩ := hgeometry.2 k
      refine ⟨hindex, hrows, hJ, hrewards, selected, hsel, hpay, hlive, hgrid, hbits, ?_⟩
      intro i
      obtain ⟨state, memory, hinput, hdomain, hmass, hzero, hstrict, hbusy⟩ := hinputs k i
      obtain ⟨hpair, hbefore⟩ := tail_chronology rate source rewards C_star C_h v k i state memory hinput
      have hstart : (installed.registers.payload.downRecord i).val.sigma ≤ r.input.time.val := by
        change installed.registers.payload.sigma.val + 1 ≤ r.input.time.val
        have hbTime := hgeometry.1
        change r.input.time.val = birth.input.time.val + 1 + k.val at htime
        omega
      have hcredit : (installed.registers.payload.downRecord i).val.q ≤
          ((installed.registers.payload.downRecord i).val.sigma - 1) * D p := by
        obtain ⟨_, _, _, _, _, _, _, _, _, hstamp, hq, _⟩ := hbirth.2 i
        rw [hstamp, Nat.add_sub_cancel]
        exact hq
      obtain ⟨next, nextMemory, hdecision, hprep, hout, hfailure, hflag, hdNext,
        hmNext, hzNext, hsNext, hbNext⟩ := local_follower_step_of_boundary r installed.registers.payload
          selected hsel hpay i state memory hinput hdomain hmass hzero hstrict hbusy
          hpair hbefore hstart hcredit hgrid hbits
      refine ⟨state, memory, next, nextMemory, hinput, hdomain, hmass, hzero, hstrict, hbusy,
        hpair, hbefore, rfl, hstart, hcredit, hdecision, hprep, hout, hfailure, hflag, hdNext,
        hmNext, hdNext.1.2.1, hzNext, hsNext, hbNext, ?_⟩
      intro hu
      exact occupied_output_of_actual_finish r i state next memory nextMemory hprep hdomain hmass
        (installed.registers.payload.downRecord i) (hbusy hu).1 hstart hout hu

/-- Every retained record has its canonical later-live readout and full actual
source cell. This is an existence consequence of all-follower PREPARE safety;
it does not construct a numerical stream or assert its replay/score identity. -/
theorem complete_first_replacement_continuing_live_readout
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
    let s := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
    let v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
    match R[v]? with
    | none => True
    | some birth => match birth.output.preparation.coordinator with
      | .collection _ _ _ _ (.laterChosen _ _ _ _ _ _ _ _ _ installed _) =>
        ∀ k : Fin (continuingTail R v).length,
          let r := (continuingTail R v).get k
          R[v + 1 + k.val]? = some r ∧
          ∃ cell : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell r,
            cell.selected.view.payload = installed.registers.payload ∧
            ReferenceLaterLiveNumericalReadout.laterLiveReadout s r = some cell.input ∧
            cell.input.enabled = true ∧
            r.input.rows = source.1.2 ∧
            r.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p source ∧
            r.input.rewards = rewards
      | _ => True := by
  classical
  have hboundary := complete_first_replacement_follower_boundary rate source rewards C_star C_h
  have hgeometry := complete_first_replacement_continuing_geometry rate source rewards C_star C_h
  have hbirth := ReferenceFirstReplacementDownRecovery.complete_first_replacement_down_recovery_and_finish
    rate source rewards C_star C_h
  dsimp only at hboundary hgeometry hbirth ⊢
  set R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
  set s := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
  set w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
  set v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
  cases hb : R[v]? with
  | none => trivial
  | some birth =>
    simp only [hb] at hboundary hgeometry hbirth ⊢
    cases hc : birth.output.preparation.coordinator with
    | first _ => trivial
    | live _ _ _ _ => trivial
    | dagger => trivial
    | invalidCollectionCutoff => trivial
    | collection old ledger clock cutoff outcome =>
      rw [hc] at hboundary hgeometry hbirth
      cases outcome <;> try trivial
      rename_i core consistent started hs instruction hi output hcons clockData installed arm
      dsimp only at hboundary hgeometry hbirth ⊢
      intro k
      let r := (continuingTail R v).get k
      obtain ⟨hindex, hrows, hJ, hrewards, selected, hsel, hpay, hlive, _hgrid, _hbits, hfollowers⟩ := hboundary k
      have ho : ReferenceLaterLiveNumericalReadout.preparedOrdinary r := by
        intro i
        obtain ⟨state, memory, next, nextMemory, _, _, _, _, _, _, _, _, _, _, _, _, hprep, _⟩ := hfollowers i
        rw [hprep]
        rfl
      have hstarted : s < selected.view.payload.sigma.val := by
        rw [hpay, hgeometry.1]
        exact hbirth.1
      have hsome := (ReferenceLaterLiveNumericalReadout.laterLiveReadout_domain s r).mpr
        ⟨selected, hsel, hstarted, hlive, ho⟩
      cases hread : ReferenceLaterLiveNumericalReadout.laterLiveReadout s r with
      | none => rw [hread] at hsome; cases hsome
      | some c =>
        have hget : R.get ⟨v + 1 + k.val, (List.getElem?_eq_some_iff.mp hindex).1⟩ = r :=
          (List.getElem?_eq_some_iff.mp hindex).2
        have hreadAt : ReferenceLaterLiveNumericalReadout.laterLiveReadout s
            (R.get ⟨v + 1 + k.val, (List.getElem?_eq_some_iff.mp hindex).1⟩) = some c := by
          rw [hget]; exact hread
        have hphysical := ReferenceLaterLiveNumericalReadout.laterLiveReadout_physical
          rate rewards C_star C_h source ⟨v + 1 + k.val, (List.getElem?_eq_some_iff.mp hindex).1⟩ c hreadAt
        rw [hget] at hphysical
        obtain ⟨cell, hcell, henabled, _⟩ := hphysical
        have hselected : cell.selected = selected :=
          Option.some.inj (cell.selection_actual.symm.trans hsel)
        refine ⟨hindex, cell, ?_, ?_, ?_, hrows, hJ, hrewards⟩
        · rw [hselected]; exact hpay
        · rw [hcell]
        · rw [hcell]; exact henabled

end Bandits.Support.ReferenceFirstReplacementFollowerBoundary
end
