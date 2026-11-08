/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstReplacementCollectionOneRecord

import Lean.Elab.Tactic.Omega
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.List.TakeWhile

/-!
# The actual first replacement collection follower prefix

Sources: `sources/zip4/manuscript/06_interruptions.tex:193-233,246-295`,
`sources/zip4/manuscript/05_binary_transport.tex:354-431`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-79`.

The result follows the original complete-suffix indices from the replacement
cutoff through the first later assignment choice. It reuses the cutoff seed,
the old-payload dispatcher origin, and the checked local one-record receiver.
It does not assert global queue, score, or physical UP truth.
-/

@[expose] public section
noncomputable section

namespace Bandits.Support.ReferenceFirstReplacementCollectionPrefix

open ConstructorDimensions ReferenceActivePhysicalStep ReferenceActivePhysicalHorizon

variable {p : ConstructorDimensions.Parameters}

/-- The actual follower prefix after the first replacement cutoff. The outer
selectors are the same literal birth/cutoff branches as the one-record root.
Each follower keeps the single memory produced by the cutoff seed throughout
the whole prefix. -/
theorem complete_first_replacement_collection_follower_prefix
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
    let v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
    let tail := ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v
    let c := v + 1 + tail.length
    match R[v]? with
    | none => True
    | some birth =>
      match birth.output.preparation.coordinator with
      | .collection _ _ _ _ (.laterChosen _ _ _ _ _ _ _ _ _ installed _) =>
        let payload := installed.registers.payload
        match R[c]? with
        | none => True
        | some cut =>
          match cut.output.preparation.coordinator with
          | .live _ _ _ (.cutoffChosen _ _ _ _ _ _ _ _ _ _) =>
            let u := cut.input.time.val + 1
            let W := (R.drop (c + 1)).takeWhile
              (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
            let E := fun j => ReferenceCollectionSegmentExtraction.endpointState
              cut.output.next (W.take j)
            ReferenceCollectionPhaseHistory.collectionWindow R c = cut :: W ∧
            E 0 = cut.output.next ∧
            (∀ j : ℕ, j ≤ W.length →
              match R[c + 1 + j]? with
              | some r => r.input.state = E j ∧
                  r.input.time.val = u + j ∧
                  r.input.rows = source.1.2 ∧
                  r.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p source ∧
                  r.input.rewards = rewards ∧
                  (j < W.length → W[j]? = some r ∧ E (j + 1) = r.output.next) ∧
                  (j = W.length → ReferenceCollectionPhaseHistory.laterChosen r.input = true)
              | none => j = W.length ∧ c + 1 + j = R.length ∧
                  ReferenceCompletePhysicalHistory.completeTerminalState
                    rate source rewards C_star C_h = some (E j)) ∧
            3 ≤ u ∧ u ≤ p.T ∧
            FollowerCutoffScan.firstCutoff p rate.eta.val payload.sigma
              (FollowerCutoffScan.completeRowProposalBit p rate.eta.val cut.input.row) = u ∧
            (∀ i : Fin (p.m - 1),
              (payload.downRecord i).val.sigma ≤ u - 1 ∧
              (payload.downRecord i).val.q ≤ ((payload.downRecord i).val.sigma - 1) * D p ∧
              ∃ old initial : ReferencePrelaunchFollower.State p rate.eta,
                ∃ memory : ActiveFollowerLifecycle.LocalMemory p,
                  cut.input.state.followers i = .ordinary old memory ∧
                  (cut.output.followers i).configuration = .ordinary initial memory ∧
                  (cut.output.followers i).failure = none ∧
                  (E 0).followers i = .ordinary initial memory ∧
                  initial.status = .unoccupied ∧
                  ActiveFollowerLifecycle.localStateDomainValid initial ∧
                  initial.S + initial.backlog ≤ (u - 1) * D p ∧
                  initial.delta ≤ D p ∧
                  (initial.lastDown = none →
                    initial.S = 0 ∧ initial.delta = 0 ∧ initial.backlog = 0) ∧
                  (ReferencePrelaunchFollower.acceptedStart initial <
                      (payload.downRecord i).val.sigma ∨
                    initial.lastDown = some (payload.downRecord i)) ∧
                  initial.initializationFailure = old.initializationFailure ∧
                  initial.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound) ∧
                  (∀ z ∈ initial.buffer, z.calendarRound < u + 1) ∧
                  (∀ j : ℕ, j ≤ W.length →
                    ∃ state : ReferencePrelaunchFollower.State p rate.eta,
                      (E j).followers i = .ordinary state memory ∧
                      state.status = .unoccupied ∧
                      ActiveFollowerLifecycle.localStateDomainValid state ∧
                      state.S + state.backlog ≤ (u - 1) * D p ∧
                      state.delta ≤ D p ∧
                      state.initializationFailure = old.initializationFailure ∧
                      (state.lastDown = none →
                        state.S = 0 ∧ state.delta = 0 ∧ state.backlog = 0) ∧
                      (ReferencePrelaunchFollower.acceptedStart state <
                          (payload.downRecord i).val.sigma ∨
                        state.lastDown = some (payload.downRecord i)) ∧
                      state.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound) ∧
                      (∀ z ∈ state.buffer, z.calendarRound < u + j + 1)) ∧
                  (∀ j : ℕ, (hj : j < W.length) →
                    let r := W.get ⟨j, hj⟩
                    R[c + 1 + j]? = some r ∧
                    ∃ state logged post,
                      r.input.state.followers i = .ordinary state memory ∧
                      state.status = .unoccupied ∧
                      ActiveFollowerLifecycle.localStateDomainValid state ∧
                      state.S + state.backlog ≤ (u - 1) * D p ∧
                      state.delta ≤ D p ∧
                      state.initializationFailure = old.initializationFailure ∧
                      (state.lastDown = none →
                        state.S = 0 ∧ state.delta = 0 ∧ state.backlog = 0) ∧
                      (ReferencePrelaunchFollower.acceptedStart state <
                          (payload.downRecord i).val.sigma ∨
                        state.lastDown = some (payload.downRecord i)) ∧
                      state.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound) ∧
                      (∀ z ∈ state.buffer, z.calendarRound < u + j + 1) ∧
                      let prepared := r.output.preparation.followers.followers i
                      let own := r.output.preparation.feedback.observations
                        (PublicDiscreteDraws.followerPlayer p.two_le_m i)
                      let view := r.output.preparation.coordinator.downView
                      let decoded := ActiveFollowerDownAcceptance.currentDecodeStep
                        p i r.input.row r.input.time own rate logged
                      let diag := ReferenceDownReception.referenceDownCut
                        p view i r.input.row r.input.time own rate logged
                      let advanced := { logged with downBatch := decoded.1 }
                      let M := payload.downRecord i
                      let word := CoordinatorLocalArmChoice.storedDownFlatWord payload i
                      ActiveFollowerLifecycle.startRound rate.eta r.input.time state memory =
                        .ok (state, memory) ∧
                      prepared.configuration = .ordinary state memory ∧
                      OrdinaryMessageCodec.upAdmissible
                        (ReferencePrelaunchFollower.codecParams p rate.eta)
                        (ActiveFollowerQueueOperation.upOfferFields state) ∧
                      ActiveFollowerLogging.checkedLogging i r.input.row
                        (r.input.state.activations i) r.input.time (prepared.arm, own) state =
                        .ok logged ∧
                      logged.buffer = state.buffer ++ ReferencePrelaunchFollower.logAt i r.input.row
                        (r.input.state.activations i) r.input.time (prepared.arm, own) ∧
                      logged.lastDown = state.lastDown ∧ logged.S = state.S ∧
                      logged.delta = state.delta ∧ logged.backlog = state.backlog ∧
                      logged.status = state.status ∧ logged.downBatch = state.downBatch ∧
                      logged.initializationFailure = state.initializationFailure ∧
                      ActiveFollowerLifecycle.localStateDomainValid logged ∧
                      ActiveFollowerDownAcceptance.operationInputDomain p rate logged ∧
                      logged.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound) ∧
                      (∀ z ∈ logged.buffer, z.calendarRound < r.input.time.val + 2) ∧
                      (ReferenceActivePhysicalStep.recordFollower view i r.input.row
                        (r.input.state.activations i) r.input.time (r.input.active i)
                        prepared.arm own state).result = .ok post ∧
                      (ReferenceActivePhysicalStep.recordFollower view i r.input.row
                        (r.input.state.activations i) r.input.time (r.input.active i)
                        prepared.arm own state).downInput = some logged ∧
                      (ReferenceActivePhysicalStep.recordFollower view i r.input.row
                        (r.input.state.activations i) r.input.time (r.input.active i)
                        prepared.arm own state).down = some diag ∧
                      ActiveFollowerLifecycle.releaseAfterService rate.eta i r.input.time
                        (ActiveFollowerLifecycle.publicRowOfCompleteRow r.input.row r.input.time)
                        own state post = .ok post ∧
                      ActiveFollowerLifecycle.finishRound rate.eta r.input.time r.input.row post
                        memory = .ok (post, memory) ∧
                      DeclaredFollowerLocalRound.releaseAndFinish rate i r.input.row r.input.time
                        own state memory post = .ok (post, memory) ∧
                      r.output.followers i =
                        ⟨.ordinary post memory, none, some logged, some diag⟩ ∧
                      DeclaredFollowerLocalRound.consumeDownResult rate diag.outcome = .ok post ∧
                      post.status = .unoccupied ∧
                      ActiveFollowerLifecycle.localStateDomainValid post ∧
                      post.S + post.backlog ≤ (u - 1) * D p ∧ post.delta ≤ D p ∧
                      post.initializationFailure = state.initializationFailure ∧
                      (post.lastDown = none →
                        post.S = 0 ∧ post.delta = 0 ∧ post.backlog = 0) ∧
                      (ReferencePrelaunchFollower.acceptedStart post < M.val.sigma ∨
                        post.lastDown = some M) ∧
                      post.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound) ∧
                      (∀ z ∈ post.buffer, z.calendarRound < r.input.time.val + 2) ∧
                      diag.expectedWord = ReferenceDownReception.expectedDownFlatWord
                        view i r.input.row r.input.time ∧
                      (ActiveFollowerDownAcceptance.downSelected p i r.input.row r.input.time →
                        diag.raw = decoded.2 ∧
                        diag.ordinaryParse = ReferenceDownReception.ordinaryParse p rate decoded.2 ∧
                        (diag.ordinaryAcceptance ↔
                          ReferenceDownReception.ordinaryLocalAcceptanceTest p rate
                            r.input.time logged
                            (ReferenceDownReception.ordinaryParse p rate decoded.2))) ∧
                      ((post = logged ∨ post = advanced) →
                        post.lastDown = state.lastDown ∧ post.S = state.S ∧
                        post.delta = state.delta ∧ post.backlog = state.backlog) ∧
                      ((¬ ActiveFollowerDownAcceptance.downSelected p i r.input.row r.input.time ∧
                          diag.outcome = .skipped logged .notSelectedDown ∧ post = logged ∧
                          diag.raw = none ∧ diag.filteredRaw = none ∧ diag.ordinaryParse = none ∧
                          diag.rawComparison = none ∧ ¬ diag.ordinaryAcceptance) ∨
                        (ActiveFollowerDownAcceptance.downSelected p i r.input.row r.input.time ∧
                          diag.outcome = .decodeOrParseRejected logged advanced decoded.2 ∧
                          post = advanced ∧
                          ((decoded.2 ≠ diag.expectedWord ∧ diag.filteredRaw = none ∧
                              diag.rawComparison = some false) ∨
                            (decoded.2 = none ∧ diag.expectedWord = none ∧
                              diag.filteredRaw = decoded.2 ∧ diag.rawComparison = some true))) ∨
                        (ActiveFollowerDownAcceptance.downSelected p i r.input.row r.input.time ∧
                          decoded.2 = some word ∧ diag.expectedWord = some word ∧
                          diag.filteredRaw = decoded.2 ∧ diag.rawComparison = some true ∧
                          diag.ordinaryParse = some M ∧ ¬ diag.ordinaryAcceptance ∧
                          diag.outcome = .parsedButUnaccepted logged advanced decoded.2 M ∧
                          post = advanced ∧ state.lastDown = some M) ∨
                        (ActiveFollowerDownAcceptance.downSelected p i r.input.row r.input.time ∧
                          decoded.2 = some word ∧ diag.expectedWord = some word ∧
                          diag.filteredRaw = decoded.2 ∧ diag.rawComparison = some true ∧
                          diag.ordinaryParse = some M ∧ diag.ordinaryAcceptance ∧
                          ∃ accepted : OrdinaryMessageCodec.acceptDown
                            (ReferencePrelaunchFollower.codecParams p rate.eta)
                            (ReferencePrelaunchFollower.acceptedStart logged)
                            (r.input.time.val + 1) M,
                            let scan := ActiveFollowerDownAcceptance.acceptedCutoffScan p rate M
                              r.input.time
                              (ActiveFollowerDownAcceptance.acceptedDownStartLE p rate M
                                r.input.time logged accepted) r.input.row
                            ∃ recovered : ActiveFollowerDownAcceptance.ReplayRegisters,
                              scan.endpoint = u ∧
                              ActiveFollowerDownAcceptance.checkedRecovery p rate M logged u =
                                .ok recovered ∧
                              diag.outcome = .accepted logged post decoded.2 M scan
                                recovered.registers recovered.lastService ∧
                              post = { advanced with
                                lastDown := some M
                                S := recovered.registers.1
                                delta := recovered.lastService
                                backlog := recovered.registers.2
                                status := .unoccupied
                                buffer := [] } ∧
                              (∀ q ∈ ActiveFollowerDownAcceptance.recoveryQueueRecords p rate M
                                  logged u, q.1 = true) ∧
                              recovered.registers = QueueReplay.replay (4 * rate.n)
                                (0, M.val.q)
                                (ActiveFollowerDownAcceptance.recoveryQueueRecords p rate M
                                  logged u) ∧
                              recovered.registers.1 + recovered.registers.2 ≤ (u - 1) * D p ∧
                              recovered.lastService ≤ D p ∧
                              ActiveFollowerDownAcceptance.replay_register_domain (D p)
                                (p.T * D p) recovered ∧
                              ∀ b : ℕ, ∃ mid,
                                ActiveFollowerDownAcceptance.checkedReplay (D p) (p.T * D p)
                                  (4 * rate.n) 0 ⟨(0, M.val.q), 0⟩
                                  ((ActiveFollowerDownAcceptance.recoveryQueueRecords p rate M
                                    logged u).take b) = .ok mid ∧
                                ActiveFollowerDownAcceptance.replay_register_domain (D p)
                                  (p.T * D p) mid ∧
                                mid.registers = QueueReplay.replay (4 * rate.n)
                                  (0, M.val.q)
                                  ((ActiveFollowerDownAcceptance.recoveryQueueRecords p rate M
                                    logged u).take b))) ∧
                    (E (j + 1)).followers i = .ordinary post memory) ∧
                  match R[c + 1 + W.length]? with
                  | none =>
                      c + 1 + W.length = R.length ∧
                      ReferenceCompletePhysicalHistory.completeTerminalState
                        rate source rewards C_star C_h = some (E W.length)
                  | some r =>
                      R[c + 1 + W.length]? = some r ∧
                      r.input.state = E W.length ∧
                      r.input.time.val = u + W.length ∧
                      r.input.rows = source.1.2 ∧
                      r.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p source ∧
                      r.input.rewards = rewards ∧
                      ReferenceCollectionPhaseHistory.laterChosen r.input = true ∧
                      ∃ state : ReferencePrelaunchFollower.State p rate.eta,
                        (E W.length).followers i = .ordinary state memory ∧
                        let prepared := r.output.preparation.followers.followers i
                        ActiveFollowerLifecycle.startRound rate.eta r.input.time state memory =
                          .ok (state, memory) ∧
                        prepared.configuration = .ordinary state memory ∧
                        OrdinaryMessageCodec.upAdmissible
                          (ReferencePrelaunchFollower.codecParams p rate.eta)
                          (ActiveFollowerQueueOperation.upOfferFields state))
            | _ => True
      | _ => True := by
  classical
  have hS := ReferenceFirstReplacementCollectionSeedEndpoint.complete_first_replacement_collection_seed_endpoint
    rate source rewards C_star C_h
  have hA := ReferenceFirstReplacementCollectionDispatchOrigin.complete_first_replacement_collection_dispatch_origin
    rate source rewards C_star C_h
  dsimp only at hS hA ⊢
  set R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
  set w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
  set v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
  cases hbirthGet : R[v]? with
  | none => trivial
  | some birth =>
      simp only [hbirthGet] at hS hA ⊢
      cases hbirthCoord : birth.output.preparation.coordinator with
      | first _ => trivial
      | live _ _ _ _ => trivial
      | dagger => trivial
      | invalidCollectionCutoff => trivial
      | collection _ _ _ _ outcome =>
          rw [hbirthCoord] at hS hA
          cases outcome <;> try trivial
          rename_i core consistent started hstart instruction hinstruction output hconsistent
            clockData installed birthArm
          dsimp only at hS hA ⊢
          let payload : ReferenceActivePhysicalStep.Payload rate := installed.registers.payload
          set tail := ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v
          set c := v + 1 + tail.length
          cases hcutGet : R[c]? with
          | none => trivial
          | some cut =>
              simp only [tail, c, hcutGet] at hS hA ⊢
              cases hcutCoord : cut.output.preparation.coordinator with
              | first _ => trivial
              | collection _ _ _ _ _ => trivial
              | dagger => trivial
              | invalidCollectionCutoff => trivial
              | live _ _ _ outcome =>
                  rw [hcutCoord] at hS hA
                  cases outcome <;> try trivial
                  dsimp only at hS hA ⊢
                  let u := cut.input.time.val + 1
                  let W := (R.drop (c + 1)).takeWhile
                    (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
                  let E := fun j => ReferenceCollectionSegmentExtraction.endpointState
                    cut.output.next (W.take j)
                  rcases hS with ⟨hwindow, hEzero, _, hu, huT, hfirst, hseed, hgeometry⟩
                  have hendpoints := hgeometry
                  obtain ⟨hcutIndex, hcutEq⟩ := List.getElem?_eq_some_iff.mp hcutGet
                  have hcutRecord : R.get ⟨c, hcutIndex⟩ = cut := hcutEq
                  let hcutFin : Fin R.length := ⟨c, hcutIndex⟩
                  obtain ⟨_, _, hcutSource⟩ := ReferenceLaterLiveNumericalReadout.source_record_prefix
                    rate rewards C_star C_h source hcutFin
                  have hcutRow : cut.input.row =
                      source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) := by
                    rw [← hcutRecord, hcutSource]
                    rfl
                  refine ⟨hwindow, hEzero, hendpoints, hu, huT, hfirst, ?_⟩
                  intro i
                  rcases hseed i with
                    ⟨hsigma, hcredit, old, initial, memory, hcutInput, hcutConfiguration,
                      hcutFailure, hinitialEndpoint, hstatus0, hdomain0, hmass0, hdelta0,
                      hzero0, horigin0, hinitialFailure, hpair0, hdates0⟩
                  have hinitialEndpoint' : (E 0).followers i = .ordinary initial memory := by
                    simpa only [E, W, payload, u, c, tail] using hinitialEndpoint
                  refine ⟨hsigma, hcredit, old, initial, memory, hcutInput,
                    hcutConfiguration, hcutFailure, hinitialEndpoint', hstatus0, hdomain0,
                    hmass0, hdelta0, hzero0, horigin0, hinitialFailure, hpair0, hdates0, ?_⟩
                  have hInvariant : ∀ j : ℕ, j ≤ W.length →
                      ∃ state : ReferencePrelaunchFollower.State p rate.eta,
                        (E j).followers i = .ordinary state memory ∧
                        state.status = .unoccupied ∧
                        ActiveFollowerLifecycle.localStateDomainValid state ∧
                        state.S + state.backlog ≤ (u - 1) * D p ∧
                        state.delta ≤ D p ∧
                        state.initializationFailure = old.initializationFailure ∧
                        (state.lastDown = none →
                          state.S = 0 ∧ state.delta = 0 ∧ state.backlog = 0) ∧
                        (ReferencePrelaunchFollower.acceptedStart state <
                            (payload.downRecord i).val.sigma ∨
                          state.lastDown = some (payload.downRecord i)) ∧
                        state.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound) ∧
                        (∀ z ∈ state.buffer, z.calendarRound < u + j + 1) := by
                    intro j
                    induction j with
                    | zero =>
                        intro hj
                        have hEinitial : (E 0).followers i = .ordinary initial memory :=
                          hinitialEndpoint
                        refine ⟨initial, hEinitial, hstatus0, hdomain0, hmass0, hdelta0,
                          hinitialFailure, hzero0, horigin0, hpair0, ?_⟩
                        intro z hz
                        have hz0 : z.calendarRound < cut.input.time.val + 1 + 1 := by
                          simpa only [u] using hdates0 z hz
                        change z.calendarRound < (cut.input.time.val + 1) + 0 + 1
                        omega
                    | succ j ih =>
                        intro hj
                        have hjlt : j < W.length := by omega
                        obtain ⟨state, hcurrent, hstatus, hdomain, hmass, hdelta, hfailure,
                          hzero, horigin, hpair, hdates⟩ := ih (by omega)
                        let r := W.get ⟨j, hjlt⟩
                        have hRGet :=
                          ReferenceFirstReplacementCollectionFollowerPrefix.collectionWindow_get
                            R c j hjlt
                        have hindex := (List.getElem?_eq_some_iff.mp hRGet).1
                        let k : Fin R.length := ⟨c + 1 + j, hindex⟩
                        have hr : R.get k = r := (List.getElem?_eq_some_iff.mp hRGet).2
                        have hgeo := hendpoints j (Nat.le_of_lt hjlt)
                        rw [hRGet] at hgeo
                        rcases hgeo with ⟨hrecordState, htime, hrows, hselected,
                          hrewards, hadvance, _⟩
                        have hinput : (R.get k).input.state.followers i =
                            .ordinary state memory := by
                          rw [hr, hrecordState]
                          exact hcurrent
                        have hcoord := (hA.2 ⟨j, hjlt⟩).1
                        have hc : (R.get k).input.state.coordinator = .dagger ∨
                            ∃ ledger saved,
                              (R.get k).input.state.coordinator = .collection payload ledger saved := by
                          rw [hr]
                          exact hcoord
                        have hmem : r ∈ W := List.get_mem W ⟨j, hjlt⟩
                        have hpred := List.mem_takeWhile_imp hmem
                        have hn : ReferenceCollectionPhaseHistory.laterChosen r.input = false := by
                          cases hb : ReferenceCollectionPhaseHistory.laterChosen r.input <;>
                            simp [hb] at hpred ⊢
                        have hrow : r.input.row = cut.input.row := by
                          calc
                            r.input.row = r.input.rows r.input.selected := rfl
                            _ = source.1.2
                                (ActualInitializationPhysicalStep.selectedRowIndex p source) := by
                                  rw [hrows, hselected]
                            _ = cut.input.row := hcutRow.symm
                        have hfirstR : FollowerCutoffScan.firstCutoff p rate.eta.val
                            payload.sigma
                            (FollowerCutoffScan.completeRowProposalBit p rate.eta.val r.input.row) = u := by
                          rw [hrow]
                          exact hfirst
                        have hfirstK : FollowerCutoffScan.firstCutoff p rate.eta.val
                            payload.sigma
                            (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
                              (R.get k).input.row) = u := by
                          rw [hr]
                          exact hfirstR
                        have hend : u ≤ (R.get k).input.time.val + 1 := by
                          rw [hr]
                          change cut.input.time.val + 1 ≤ r.input.time.val + 1
                          rw [htime]
                          omega
                        have hrun :=
                          ReferenceFirstReplacementCollectionOneRecord.actual_collection_follower_step
                            rate source rewards C_star C_h k payload u i state memory hinput
                            hstatus hdomain hmass hzero horigin hc (by rw [hr]; exact hn)
                            hu hend hfirstK hcredit
                        rw [hr] at hrun
                        rcases hrun with ⟨logged, post, hstart, hprepared, hup, hlogging,
                          hbuffer, hlast, hS, hdeltaPost, hbacklog, hlogStatus, hbatch,
                          hinit, hlogDomain, hoperation, hpairLog, hdatesLog, hrecord,
                          hdownInput, hdown, hrelease, hfinish, hreleaseFinish, houtput,
                          hconsume, hpost, hexpected, hselectedWord, hpreserve, hbranches⟩
                        have hnext : (E (j + 1)).followers i = .ordinary post memory := by
                          have hnext' : r.output.next.followers i = .ordinary post memory := by
                            calc
                              r.output.next.followers i = (r.output.followers i).configuration := by
                                rw [r.output_eq]
                                rfl
                              _ = .ordinary post memory := by rw [houtput]
                          rcases hadvance hjlt with ⟨_, hendpoint⟩
                          have hendpoint' : E (j + 1) = r.output.next := by
                            simpa only [E, W] using hendpoint
                          rw [hendpoint']
                          exact hnext'
                        rcases hpost with ⟨hpostStatus, hpostDomain, hpostMass, hpostDelta,
                          hpostFailure, hpostZero, hpostOrigin, hpostPair, hpostDates⟩
                        refine ⟨post, hnext, hpostStatus, hpostDomain, hpostMass,
                          hpostDelta, ?_, hpostZero, hpostOrigin, hpostPair, ?_⟩
                        · exact hpostFailure.trans hfailure
                        · intro z hz
                          have hzPost := hpostDates z hz
                          rw [htime] at hzPost
                          change z.calendarRound < (cut.input.time.val + 1) + (j + 1) + 1
                          omega
                  refine ⟨hInvariant, ?_, ?_⟩
                  intro j hj
                  let r := W.get ⟨j, hj⟩
                  have hRGet :=
                    ReferenceFirstReplacementCollectionFollowerPrefix.collectionWindow_get
                      R c j hj
                  have hindex := (List.getElem?_eq_some_iff.mp hRGet).1
                  let k : Fin R.length := ⟨c + 1 + j, hindex⟩
                  have hr : R.get k = r := (List.getElem?_eq_some_iff.mp hRGet).2
                  have hgeo := hendpoints j (Nat.le_of_lt hj)
                  rw [hRGet] at hgeo
                  rcases hgeo with ⟨hrecordState, htime, hrows, hselected,
                    hrewards, hadvance, _⟩
                  rcases hInvariant j (Nat.le_of_lt hj) with
                    ⟨state, hcurrent, hstatus, hdomain, hmass, hdelta, hfailure,
                      hzero, horigin, hpair, hdates⟩
                  have hinput : (R.get k).input.state.followers i =
                      .ordinary state memory := by
                    rw [hr, hrecordState]
                    exact hcurrent
                  have hcoord := (hA.2 ⟨j, hj⟩).1
                  have hc : (R.get k).input.state.coordinator = .dagger ∨
                      ∃ ledger saved,
                        (R.get k).input.state.coordinator = .collection payload ledger saved := by
                    rw [hr]
                    exact hcoord
                  have hmem : r ∈ W := List.get_mem W ⟨j, hj⟩
                  have hpred := List.mem_takeWhile_imp hmem
                  have hn : ReferenceCollectionPhaseHistory.laterChosen r.input = false := by
                    cases hb : ReferenceCollectionPhaseHistory.laterChosen r.input <;>
                      simp [hb] at hpred ⊢
                  have hrow : r.input.row = cut.input.row := by
                    calc
                      r.input.row = r.input.rows r.input.selected := rfl
                      _ = source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) := by
                        rw [hrows, hselected]
                      _ = cut.input.row := hcutRow.symm
                  have hfirstR : FollowerCutoffScan.firstCutoff p rate.eta.val
                      payload.sigma
                      (FollowerCutoffScan.completeRowProposalBit p rate.eta.val r.input.row) = u := by
                    rw [hrow]
                    exact hfirst
                  have hfirstK : FollowerCutoffScan.firstCutoff p rate.eta.val
                      payload.sigma
                      (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
                        (R.get k).input.row) = u := by
                    rw [hr]
                    exact hfirstR
                  have hend : u ≤ (R.get k).input.time.val + 1 := by
                    rw [hr]
                    change cut.input.time.val + 1 ≤ r.input.time.val + 1
                    rw [htime]
                    omega
                  have hrun :=
                    ReferenceFirstReplacementCollectionOneRecord.actual_collection_follower_step
                      rate source rewards C_star C_h k payload u i state memory hinput
                      hstatus hdomain hmass hzero horigin hc (by rw [hr]; exact hn)
                      hu hend hfirstK hcredit
                  rw [hr] at hrun
                  rcases hrun with ⟨logged, post, hstart, hprepared, hup, hlogging,
                    hbuffer, hlast, hS, hdeltaPost, hbacklog, hlogStatus, hbatch,
                    hinit, hlogDomain, hoperation, hpairLog, hdatesLog, hrecord,
                    hdownInput, hdown, hrelease, hfinish, hreleaseFinish, houtput,
                    hconsume, hpost, hexpected, hselectedWord, hpreserve, hbranches⟩
                  have hnext : (E (j + 1)).followers i = .ordinary post memory := by
                    have hnext' : r.output.next.followers i = .ordinary post memory := by
                      calc
                        r.output.next.followers i = (r.output.followers i).configuration := by
                          rw [r.output_eq]
                          rfl
                        _ = .ordinary post memory := by rw [houtput]
                    rcases hadvance hj with ⟨_, hendpoint⟩
                    have hendpoint' : E (j + 1) = r.output.next := by
                      simpa only [E, W] using hendpoint
                    rw [hendpoint']
                    exact hnext'
                  have hinput' : r.input.state.followers i = .ordinary state memory := by
                    rw [← hr]
                    exact hinput
                  rcases hpost with ⟨hpostStatus, hpostDomain, hpostMass, hpostDelta,
                    hpostFailure, hpostZero, hpostOrigin, hpostPair, hpostDates⟩
                  refine ⟨hRGet, ⟨state, ?_⟩⟩
                  refine ⟨logged, ?_⟩
                  refine ⟨post, ?_⟩
                  refine ⟨hinput', hstatus, hdomain, hmass, hdelta, hfailure,
                    hzero, horigin, hpair, hdates, ?_⟩
                  exact ⟨hstart, hprepared, hup, hlogging, hbuffer, hlast, hS,
                    hdeltaPost, hbacklog, hlogStatus, hbatch, hinit, hlogDomain,
                    hoperation, hpairLog, hdatesLog, hrecord, hdownInput, hdown,
                    hrelease, hfinish, hreleaseFinish, houtput, hconsume, hpostStatus,
                    hpostDomain, hpostMass, hpostDelta, hpostFailure, hpostZero,
                    hpostOrigin, hpostPair, hpostDates,
                    hexpected, hselectedWord, hpreserve, hbranches, hnext⟩
                  cases hEndGet : R[c + 1 + W.length]? with
                  | none =>
                      have hEnd := hendpoints W.length (Nat.le_refl _)
                      rw [hEndGet] at hEnd
                      rcases hEnd with ⟨_, hlength, hterminal⟩
                      exact ⟨hlength, hterminal⟩
                  | some lastRecord =>
                      have hEnd := hendpoints W.length (Nat.le_refl _)
                      rw [hEndGet] at hEnd
                      rcases hEnd with ⟨hstateEnd, htimeEnd, hrowsEnd, hselectedEnd,
                        hrewardsEnd, _, hlater⟩
                      have hlaterEnd := hlater rfl
                      obtain ⟨hlastIndex, hlastEq⟩ := List.getElem?_eq_some_iff.mp hEndGet
                      have hrEnd : R.get ⟨c + 1 + W.length, hlastIndex⟩ = lastRecord := hlastEq
                      let kEnd : Fin R.length := ⟨c + 1 + W.length, hlastIndex⟩
                      rcases hInvariant W.length (Nat.le_refl _) with
                        ⟨state, hcurrent, hstatus, hdomain, hmass, hdelta, hfailure,
                          hzero, horigin, hpair, hdates⟩
                      have hinputEnd : (R.get kEnd).input.state.followers i =
                          .ordinary state memory := by
                        rw [hrEnd, hstateEnd]
                        exact hcurrent
                      have hprepare :=
                        ReferenceFirstReplacementCollectionOneRecord.actual_collection_follower_prepare
                          rate source rewards C_star C_h kEnd i state memory hinputEnd
                          hdomain hstatus hzero
                      rw [hrEnd] at hprepare
                      refine ⟨rfl, hstateEnd, htimeEnd, hrowsEnd, hselectedEnd,
                        hrewardsEnd, hlaterEnd, state, hcurrent, hprepare.1,
                        hprepare.2.1, hprepare.2.2⟩

end Bandits.Support.ReferenceFirstReplacementCollectionPrefix

end
