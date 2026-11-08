/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstReplacementCollectionDispatchOrigin
public import Bandits.Support.ReferenceFirstReplacementCollectionSeedEndpoint

import Lean.Elab.Tactic.Omega
import Mathlib.Data.List.TakeWhile

/-!
# The actual first record after the first replacement cutoff

Sources: `sources/zip4/manuscript/06_interruptions.tex:193-233,246-295`,
`sources/zip4/manuscript/05_binary_transport.tex:354-431`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-64`.

The conditional step exposes its local induction inputs. The complete root
constructs them from the actual cutoff seed and old-payload dispatch origin.
Recovery uses every calendar round before the original cutoff, including zero
arrivals. These are internal execution results, not physical score identities
or closure of a manuscript theorem. The subsequent collection-prefix induction
belongs to `ReferenceFirstReplacementCollectionPrefix`.
-/

@[expose] public section
noncomputable section

namespace Bandits.Support.ReferenceFirstReplacementCollectionOneRecord

open ConstructorDimensions ReferenceActivePhysicalStep ReferenceActivePhysicalHorizon

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

private theorem operation_input_of_local_domain
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (h : ActiveFollowerLifecycle.localStateDomainValid state) :
    ActiveFollowerDownAcceptance.operationInputDomain p rate state := by
  refine ⟨h.1, h.2.2, ?_⟩
  refine ⟨?_, h.2.1.2.1⟩
  intro saved hsaved
  obtain ⟨q, hq, heq⟩ := h.2.1.2.2 saved hsaved
  exact ⟨(h.2.1.1 saved hsaved).1, (h.2.1.1 saved hsaved).2,
    ⟨⟨q, by omega⟩, heq⟩⟩

private theorem logging_chronology
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (activation : ReferencePrelaunchFollower.Activation p) (t : Fin p.T)
    (own : Fin p.K × ReferencePrelaunchFollower.Observation p)
    (choice logged : ReferencePrelaunchFollower.State p rate.eta)
    (hbuffer : logged.buffer = choice.buffer ++ ReferencePrelaunchFollower.logAt i row activation t own)
    (hpair : choice.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound))
    (hbefore : ∀ saved ∈ choice.buffer, saved.calendarRound < t.val + 1) :
    logged.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound) ∧
      ∀ saved ∈ logged.buffer, saved.calendarRound < t.val + 2 := by
  rw [hbuffer]
  constructor
  · apply List.pairwise_append.mpr
    refine ⟨hpair, ?_, ?_⟩
    · unfold ReferencePrelaunchFollower.logAt
      split <;> simp only [List.pairwise_singleton, List.Pairwise.nil]
    · intro a ha b hb
      rw [(ActiveFollowerLogging.logAt_member_fields i row activation t own b hb).1]
      exact hbefore a ha
  · intro saved hsaved
    rcases List.mem_append.mp hsaved with hsaved | hsaved
    · exact Nat.lt_trans (hbefore saved hsaved) (by omega)
    · have ht := (ActiveFollowerLogging.logAt_member_fields i row activation t own saved hsaved).1
      omega

private theorem parse_stored_word (payload : ReferenceActivePhysicalStep.Payload rate)
    (i : Fin (p.m - 1)) :
    ReferenceDownReception.ordinaryParse p rate
      (some (CoordinatorLocalArmChoice.storedDownFlatWord payload i)) =
      some (payload.downRecord i) := by
  unfold ReferenceDownReception.ordinaryParse CoordinatorLocalArmChoice.storedDownFlatWord
  change OrdinaryMessageCodec.parseDown (ReferencePrelaunchFollower.codecParams p rate.eta)
    (some ((OrdinaryMessageCodec.wordEquivFlat _).symm
      ((OrdinaryMessageCodec.wordEquivFlat _) (payload.downWord i)))) = _
  exact (congrArg (fun word => OrdinaryMessageCodec.parseDown
    (ReferencePrelaunchFollower.codecParams p rate.eta) (some word))
      ((OrdinaryMessageCodec.wordEquivFlat _).symm_apply_apply
        (payload.downWord i))).trans (payload.parseDown_downWord i)


/-- PREPARE on an actual ordinary, unoccupied follower. No coordinator-phase,
selection, view, offered word, or interruption premise is an input. The only
zero-register requirement applies when the accepted DOWN record is absent. -/
theorem actual_collection_follower_prepare
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (i : Fin (p.m - 1)) (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hinput : ((ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).get k).input.state.followers i = .ordinary state memory)
    (hdomain : ActiveFollowerLifecycle.localStateDomainValid state)
    (hstatus : state.status = .unoccupied)
    (hzero : state.lastDown = none → state.S = 0 ∧ state.delta = 0 ∧ state.backlog = 0) :
    let r := (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).get k
    ActiveFollowerLifecycle.startRound rate.eta r.input.time state memory = .ok (state, memory) ∧
    (r.output.preparation.followers.followers i).configuration = .ordinary state memory ∧
    OrdinaryMessageCodec.upAdmissible (ReferencePrelaunchFollower.codecParams p rate.eta)
      (ActiveFollowerQueueOperation.upOfferFields state) := by
  classical
  let r := (ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate source rewards C_star C_h).get k
  have hstart := ActiveFollowerLifecycle.startRound_unoccupied rate.eta
    r.input.time state memory hdomain hstatus
  have hqueue : ActiveFollowerQueueOperation.stateInputDomain state :=
    ⟨hdomain.1.1, hdomain.1.2.1, hdomain.1.2.2, hdomain.2.1.1, hdomain.2.1.2.1⟩
  have hup : OrdinaryMessageCodec.upAdmissible
      (ReferencePrelaunchFollower.codecParams p rate.eta)
      (ActiveFollowerQueueOperation.upOfferFields state) := by
    cases hlast : state.lastDown with
    | none =>
        obtain ⟨hS, hd, hb⟩ := hzero hlast
        simp [OrdinaryMessageCodec.upAdmissible, ActiveFollowerQueueOperation.upOfferFields,
          ReferencePrelaunchFollower.acceptedStart, hlast, hS, hd, hb,
          OrdinaryMessageCodec.upPlaceholder]
    | some M =>
        simp only [OrdinaryMessageCodec.upAdmissible, ActiveFollowerQueueOperation.upOfferFields,
          ReferencePrelaunchFollower.acceptedStart, hlast]
        exact Or.inr ⟨M.property.1, M.property.2.1,
          hdomain.1.1, hdomain.1.2.1, hdomain.1.2.2⟩
  have hlocal : (DeclaredFollowerLocalRound.prepare rate i r.input.row
      (r.input.state.activations i) r.input.time (r.input.active i)
      (.ordinary state memory)).configuration = .ordinary state memory := by
    by_cases hs : ActiveFollowerQueueOperation.selectedUpRound i r.input.row
        (r.input.state.activations i) r.input.time
    · let offered : OrdinaryMessageCodec.UpRecord
          (ReferencePrelaunchFollower.codecParams p rate.eta) :=
        ⟨ActiveFollowerQueueOperation.upOfferFields state, hup⟩
      have hoff : ActiveFollowerQueueOperation.checkedUpOffer rate.eta i r.input.row
          (r.input.state.activations i) r.input.time state = .offer offered := by
        simp [ActiveFollowerQueueOperation.checkedUpOffer, hqueue, hs, hstatus, hup, offered]
      have hchoice := ActiveFollowerArmChoice.followerArmChoiceCore_unoccupied_selected_up
        state (r.input.row.2 r.input.time) i offered hstatus hs.2.1 hs.2.2
        ⟨⟨hdomain.1.1, hdomain.1.2.1, hdomain.1.2.2⟩, ⟨rfl, rfl, rfl, rfl⟩⟩
      simp only [DeclaredFollowerLocalRound.prepare, hstart, hoff,
        ActiveFollowerArmChoice.followerArmChoice, hchoice]
    · have hoff := ActiveFollowerQueueOperation.checkedUpOffer_noOffer rate.eta i r.input.row
        (r.input.state.activations i) r.input.time state hqueue (fun h => hs h.1)
      have hnot : ¬ (PublicDiscreteDraws.slotDraw (r.input.row.2 r.input.time).1 =
          PublicDiscreteDraws.upSlot ∧ PublicDiscreteDraws.selectedFollowerDraw
            p.two_le_m p.m_lt_K (r.input.row.2 r.input.time).1 = i) := by
        intro h
        exact hs ⟨r.input.active i, h.1, h.2⟩
      by_cases hd : PublicDiscreteDraws.slotDraw (r.input.row.2 r.input.time).1 =
          PublicDiscreteDraws.dataSlot
      · have hchoice := ActiveFollowerArmChoice.followerArmChoiceCore_unoccupied_data
          state (r.input.row.2 r.input.time) i none hstatus hd
        simp only [DeclaredFollowerLocalRound.prepare, hstart, hoff,
          ActiveFollowerArmChoice.followerArmChoice, hchoice]
      · have hchoice := ActiveFollowerArmChoice.followerArmChoiceCore_unoccupied_other
          state (r.input.row.2 r.input.time) i none hstatus hd hnot
        simp only [DeclaredFollowerLocalRound.prepare, hstart, hoff,
          ActiveFollowerArmChoice.followerArmChoice, hchoice]
  have hprep : r.output.preparation = ReferenceActivePhysicalStep.prepare r.input := by
    rw [r.output_eq]
    rfl
  have hfollowers : r.output.preparation.followers.followers i =
      DeclaredFollowerLocalRound.prepare rate i r.input.row (r.input.state.activations i)
        r.input.time (r.input.active i) (r.input.state.followers i) := by
    rw [hprep]
    exact (ReferenceActivePhysicalStep.prepare r.input).followers.followers_eq i
  refine ⟨hstart, ?_, hup⟩
  rw [hfollowers, hinput]
  exact hlocal

private theorem receiver_at_source_cutoff
    (payload : ReferenceActivePhysicalStep.Payload rate) (u : ℕ) (i : Fin (p.m - 1))
    (row : CompletePublicTable.CompleteRow p) (time : Fin p.T)
    (own : ReferencePrelaunchFollower.Observation p)
    (logged : ReferencePrelaunchFollower.State p rate.eta)
    (hstatus : logged.status = .unoccupied)
    (hdomain : ActiveFollowerLifecycle.localStateDomainValid logged)
    (hmass : logged.S + logged.backlog ≤ (u - 1) * D p)
    (hzero : logged.lastDown = none → logged.S = 0 ∧ logged.delta = 0 ∧ logged.backlog = 0)
    (horigin : ReferencePrelaunchFollower.acceptedStart logged < (payload.downRecord i).val.sigma ∨
      logged.lastDown = some (payload.downRecord i))
    (hpair : logged.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound))
    (hdates : ∀ z ∈ logged.buffer, z.calendarRound < time.val + 2)
    (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (hexpected : ReferenceDownReception.expectedDownFlatWord view i row time = none ∨
      ReferenceDownReception.expectedDownFlatWord view i row time =
        some (CoordinatorLocalArmChoice.storedDownFlatWord payload i))
    (hu : 3 ≤ u) (hend : u ≤ time.val + 1)
    (hfirst : FollowerCutoffScan.firstCutoff p rate.eta.val payload.sigma
      (FollowerCutoffScan.completeRowProposalBit p rate.eta.val row) = u)
    (hcredit : (payload.downRecord i).val.q ≤ ((payload.downRecord i).val.sigma - 1) * D p) :
    let decoded := ActiveFollowerDownAcceptance.currentDecodeStep p i row time own rate logged
    let diag := ReferenceDownReception.referenceDownCut p view i row time own rate logged
    let advanced := { logged with downBatch := decoded.1 }
    let M := payload.downRecord i
    let word := CoordinatorLocalArmChoice.storedDownFlatWord payload i
    ∃ post,
      DeclaredFollowerLocalRound.consumeDownResult rate diag.outcome = .ok post ∧
      (post.status = .unoccupied ∧ ActiveFollowerLifecycle.localStateDomainValid post ∧
        post.S + post.backlog ≤ (u - 1) * D p ∧ post.delta ≤ D p ∧
        post.initializationFailure = logged.initializationFailure ∧
        (post.lastDown = none → post.S = 0 ∧ post.delta = 0 ∧ post.backlog = 0) ∧
        (ReferencePrelaunchFollower.acceptedStart post < M.val.sigma ∨ post.lastDown = some M) ∧
        post.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound) ∧
        (∀ z ∈ post.buffer, z.calendarRound < time.val + 2)) ∧
      diag.expectedWord = ReferenceDownReception.expectedDownFlatWord view i row time ∧
      (ActiveFollowerDownAcceptance.downSelected p i row time →
        diag.raw = decoded.2 ∧
        diag.ordinaryParse = ReferenceDownReception.ordinaryParse p rate decoded.2 ∧
        (diag.ordinaryAcceptance ↔ ReferenceDownReception.ordinaryLocalAcceptanceTest
          p rate time logged (ReferenceDownReception.ordinaryParse p rate decoded.2))) ∧
      ((post = logged ∨ post = advanced) → post.lastDown = logged.lastDown ∧
        post.S = logged.S ∧ post.delta = logged.delta ∧ post.backlog = logged.backlog) ∧
      ((¬ ActiveFollowerDownAcceptance.downSelected p i row time ∧
          diag.outcome = .skipped logged .notSelectedDown ∧ post = logged ∧
          diag.raw = none ∧ diag.filteredRaw = none ∧ diag.ordinaryParse = none ∧
          diag.rawComparison = none ∧ ¬ diag.ordinaryAcceptance) ∨
        (ActiveFollowerDownAcceptance.downSelected p i row time ∧
          diag.outcome = .decodeOrParseRejected logged advanced decoded.2 ∧ post = advanced ∧
          ((decoded.2 ≠ diag.expectedWord ∧ diag.filteredRaw = none ∧
              diag.rawComparison = some false) ∨
            (decoded.2 = none ∧ diag.expectedWord = none ∧ diag.filteredRaw = decoded.2 ∧
              diag.rawComparison = some true))) ∨
        (ActiveFollowerDownAcceptance.downSelected p i row time ∧
          decoded.2 = some word ∧ diag.expectedWord = some word ∧
          diag.filteredRaw = decoded.2 ∧ diag.rawComparison = some true ∧
          diag.ordinaryParse = some M ∧ ¬ diag.ordinaryAcceptance ∧
          diag.outcome = .parsedButUnaccepted logged advanced decoded.2 M ∧ post = advanced ∧
          logged.lastDown = some M) ∨
        (ActiveFollowerDownAcceptance.downSelected p i row time ∧
          decoded.2 = some word ∧ diag.expectedWord = some word ∧
          diag.filteredRaw = decoded.2 ∧ diag.rawComparison = some true ∧
          diag.ordinaryParse = some M ∧ diag.ordinaryAcceptance ∧
          ∃ accepted : OrdinaryMessageCodec.acceptDown
              (ReferencePrelaunchFollower.codecParams p rate.eta)
              (ReferencePrelaunchFollower.acceptedStart logged) (time.val + 1) M,
            let scan := ActiveFollowerDownAcceptance.acceptedCutoffScan p rate M time
              (ActiveFollowerDownAcceptance.acceptedDownStartLE p rate M time logged accepted) row
            ∃ recovered : ActiveFollowerDownAcceptance.ReplayRegisters,
              scan.endpoint = u ∧
              ActiveFollowerDownAcceptance.checkedRecovery p rate M logged u = .ok recovered ∧
              diag.outcome = .accepted logged post decoded.2 M scan
                recovered.registers recovered.lastService ∧
              post = { advanced with
                lastDown := some M
                S := recovered.registers.1
                delta := recovered.lastService
                backlog := recovered.registers.2
                status := .unoccupied
                buffer := [] } ∧
              (∀ q ∈ ActiveFollowerDownAcceptance.recoveryQueueRecords p rate M logged u,
                q.1 = true) ∧
              recovered.registers = QueueReplay.replay (4 * rate.n) (0, M.val.q)
                (ActiveFollowerDownAcceptance.recoveryQueueRecords p rate M logged u) ∧
              recovered.registers.1 + recovered.registers.2 ≤ (u - 1) * D p ∧
              recovered.lastService ≤ D p ∧
              ActiveFollowerDownAcceptance.replay_register_domain (D p) (p.T * D p) recovered ∧
              ∀ b : ℕ, ∃ mid,
                ActiveFollowerDownAcceptance.checkedReplay (D p) (p.T * D p) (4 * rate.n) 0
                  ⟨(0, M.val.q), 0⟩
                  ((ActiveFollowerDownAcceptance.recoveryQueueRecords p rate M logged u).take b) =
                    .ok mid ∧
                ActiveFollowerDownAcceptance.replay_register_domain (D p) (p.T * D p) mid ∧
                mid.registers = QueueReplay.replay (4 * rate.n) (0, M.val.q)
                  ((ActiveFollowerDownAcceptance.recoveryQueueRecords p rate M logged u).take b))) := by
  classical
  intro decoded diag advanced M word
  have hop := operation_input_of_local_domain logged hdomain
  have hstep := AffineBatchDecoder.step_spec p
    (ActiveFollowerDownAcceptance.currentInputExtension p
      (ActiveFollowerDownAcceptance.currentRoundInput p i row time own rate logged))
    logged.downBatch time hop.2.1.1 hop.2.1.2
  have hbatch : ActiveFollowerDownAcceptance.decoderInputDomain p
      (ActiveFollowerDownAcceptance.currentDecodeStep p i row time own rate logged).1 :=
    ⟨hstep.1, hstep.2.1⟩
  have hadvanced : ActiveFollowerLifecycle.localStateDomainValid advanced :=
    ⟨hdomain.1, hdomain.2.1, hbatch⟩
  have hstable (post : ReferencePrelaunchFollower.State p rate.eta)
      (heq : post = logged ∨ post = advanced) :
      post.status = .unoccupied ∧ ActiveFollowerLifecycle.localStateDomainValid post ∧
      post.S + post.backlog ≤ (u - 1) * D p ∧ post.delta ≤ D p ∧
      post.initializationFailure = logged.initializationFailure ∧
      (post.lastDown = none → post.S = 0 ∧ post.delta = 0 ∧ post.backlog = 0) ∧
      (ReferencePrelaunchFollower.acceptedStart post < M.val.sigma ∨ post.lastDown = some M) ∧
      post.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound) ∧
      (∀ z ∈ post.buffer, z.calendarRound < time.val + 2) := by
    rcases heq with rfl | rfl
    · exact ⟨hstatus, hdomain, hmass, hdomain.1.2.1, rfl, hzero, horigin, hpair, hdates⟩
    · exact ⟨hstatus, hadvanced, hmass, hdomain.1.2.1, rfl, hzero, horigin, hpair, hdates⟩
  have hpreserve (post : ReferencePrelaunchFollower.State p rate.eta)
      (heq : post = logged ∨ post = advanced) :
      post.lastDown = logged.lastDown ∧ post.S = logged.S ∧
        post.delta = logged.delta ∧ post.backlog = logged.backlog := by
    rcases heq with rfl | rfl <;> exact ⟨rfl, rfl, rfl, rfl⟩
  by_cases hs : ActiveFollowerDownAcceptance.downSelected p i row time
  · have hcommon : diag.expectedWord = ReferenceDownReception.expectedDownFlatWord view i row time ∧
        (ActiveFollowerDownAcceptance.downSelected p i row time →
          diag.raw = (ActiveFollowerDownAcceptance.currentDecodeStep p i row time own rate logged).2 ∧
          diag.ordinaryParse = ReferenceDownReception.ordinaryParse p rate
              (ActiveFollowerDownAcceptance.currentDecodeStep p i row time own rate logged).2 ∧
          (diag.ordinaryAcceptance ↔ ReferenceDownReception.ordinaryLocalAcceptanceTest
            p rate time logged (ReferenceDownReception.ordinaryParse p rate
                (ActiveFollowerDownAcceptance.currentDecodeStep p i row time own rate logged).2))) := by
      by_cases hm :
          (ActiveFollowerDownAcceptance.currentDecodeStep p i row time own rate logged).2 =
          ReferenceDownReception.expectedDownFlatWord view i row time
      · simp only [diag, ReferenceDownReception.referenceDownCut, dite_eq_left hs,
          dite_eq_left hstatus, dite_eq_left hop.1, dite_eq_left hop.2.1,
          dite_eq_left hop.2.2, dite_eq_left hm]
        exact ⟨trivial, fun _ => ⟨trivial, trivial, trivial⟩⟩
      · simp only [diag, ReferenceDownReception.referenceDownCut, dite_eq_left hs,
          dite_eq_left hstatus, dite_eq_left hop.1, dite_eq_left hop.2.1,
          dite_eq_left hop.2.2, dite_eq_right hm]
        exact ⟨trivial, fun _ => ⟨trivial, trivial, trivial⟩⟩
    by_cases hm :
        (ActiveFollowerDownAcceptance.currentDecodeStep p i row time own rate logged).2 =
        ReferenceDownReception.expectedDownFlatWord view i row time
    · rcases hexpected with hn | hw
      · have hraw : (ActiveFollowerDownAcceptance.currentDecodeStep p i row time own rate logged).2 = none := hm.trans hn
        have hout : diag.outcome = .decodeOrParseRejected logged advanced
            (ActiveFollowerDownAcceptance.currentDecodeStep p i row time own rate logged).2 := by
          simp only [diag, ReferenceDownReception.referenceDownCut, dite_eq_left hs,
            dite_eq_left hstatus, dite_eq_left hop.1, dite_eq_left hop.2.1,
            dite_eq_left hop.2.2, dite_eq_left hm]
          simp only [hraw, ReferenceDownReception.ordinaryParse,
            OrdinaryMessageCodec.parseDown]
          rfl
        refine ⟨advanced, ?_, hstable advanced (Or.inr rfl), hcommon.1, hcommon.2,
          hpreserve advanced, Or.inr (Or.inl ⟨hs, hout, rfl, Or.inr ?_⟩)⟩
        · rw [hout]
          rfl
        · refine ⟨hraw, hcommon.1.trans hn, ?_, ?_⟩ <;>
            simp only [diag, decoded, ReferenceDownReception.referenceDownCut, dite_eq_left hs,
              dite_eq_left hstatus, dite_eq_left hop.1, dite_eq_left hop.2.1,
              dite_eq_left hop.2.2, dite_eq_left hm]
      · have hraw : (ActiveFollowerDownAcceptance.currentDecodeStep p i row time own rate logged).2 = some word := hm.trans hw
        have hparse : ReferenceDownReception.ordinaryParse p rate
            (ActiveFollowerDownAcceptance.currentDecodeStep p i row time own rate logged).2 = some M := by
          rw [hraw]
          exact parse_stored_word payload i
        have hfields : diag.filteredRaw = (ActiveFollowerDownAcceptance.currentDecodeStep p i row time own rate logged).2 ∧
            diag.rawComparison = some true ∧
            diag.ordinaryParse = some M := by
          simp only [diag, ReferenceDownReception.referenceDownCut, dite_eq_left hs,
            dite_eq_left hstatus, dite_eq_left hop.1, dite_eq_left hop.2.1,
            dite_eq_left hop.2.2, dite_eq_left hm, hparse]
          exact ⟨trivial, trivial, trivial⟩
        by_cases ha : OrdinaryMessageCodec.acceptDown
            (ReferencePrelaunchFollower.codecParams p rate.eta)
            (ReferencePrelaunchFollower.acceptedStart logged) (time.val + 1) M
        · have hdownStart : ActiveFollowerDownAcceptance.downStart p rate M = payload.sigma := by
            apply Fin.ext
            have ht := ActiveFollowerDownAcceptance.downStart_val_add_one p rate M
            have hM : M.val.sigma = payload.sigma.val + 1 := by
              exact congrArg OrdinaryMessageCodec.DownFields.sigma (payload.downRecord_fields i)
            omega
          let scan := ActiveFollowerDownAcceptance.acceptedCutoffScan p rate M time
            (ActiveFollowerDownAcceptance.acceptedDownStartLE p rate M time logged ha) row
          have hscan : scan.endpoint = u :=
            ReferenceFirstReplacementCollectionFollowerPrefix.acceptedScan_endpoint_of_firstCutoff
              M payload.sigma time row u hdownStart
              (ActiveFollowerDownAcceptance.acceptedDownStartLE p rate M time logged ha)
              hfirst (by omega)
          obtain ⟨recovered, hchecked, hmassFinal, hlast, hregs, hexact, hprefix⟩ :=
            ReferenceFirstReplacementCollectionFollowerPrefix.checkedRecovery_at_sourceFirstCutoff
              M logged payload.sigma row u hdownStart hfirst hdomain.2.1 hcredit hu
              (by have := time.isLt; omega)
          let post := { advanced with
            lastDown := some M
            S := recovered.registers.1
            delta := recovered.lastService
            backlog := recovered.registers.2
            status := ActiveRoundActions.FollowerStatus.unoccupied
            buffer := [] }
          have hpost : ActiveFollowerLifecycle.localStateDomainValid post := by
            refine ⟨hregs, ?_, hbatch⟩
            simp [ActiveFollowerLifecycle.localBufferValid, post]
          have hout : diag.outcome = .accepted logged post
              (ActiveFollowerDownAcceptance.currentDecodeStep p i row time own rate logged).2 M scan
              recovered.registers recovered.lastService := by
            have hne : u ≠ time.val + 2 := by omega
            simp only [diag, decoded, ReferenceDownReception.referenceDownCut, dite_eq_left hs,
              dite_eq_left hstatus, dite_eq_left hop.1, dite_eq_left hop.2.1,
              dite_eq_left hop.2.2, dite_eq_left hm, hparse, dite_eq_left ha,
              scan, hscan, hchecked, ite_eq_right hne, post, advanced]
          have haccept : diag.ordinaryAcceptance :=
            (hcommon.2 hs).2.2.mpr (by
              simpa only [hparse, ReferenceDownReception.ordinaryLocalAcceptanceTest] using ha)
          refine ⟨post, ?_, ?_, hcommon.1, hcommon.2, hpreserve post,
            Or.inr (Or.inr (Or.inr ⟨hs, hraw, hcommon.1.trans hw,
              hfields.1, hfields.2.1, hfields.2.2, haccept, ha, recovered, hscan, hchecked,
              hout, rfl, ?_, hexact, hmassFinal, hlast, hregs, hprefix⟩))⟩
          · rw [hout]
            rfl
          · refine ⟨rfl, hpost, hmassFinal, hlast, rfl, ?_, Or.inr rfl,
              List.Pairwise.nil, ?_⟩
            · intro hn
              cases hn
            · intro z hz
              exact False.elim (List.not_mem_nil hz)
          · exact ActiveFollowerDownAcceptance.recoveryQueueRecords_all_enabled p rate M logged u
        · have hout : diag.outcome = .parsedButUnaccepted logged advanced
            (ActiveFollowerDownAcceptance.currentDecodeStep p i row time own rate logged).2 M := by
            simp only [diag, decoded, ReferenceDownReception.referenceDownCut, dite_eq_left hs,
              dite_eq_left hstatus, dite_eq_left hop.1, dite_eq_left hop.2.1,
              dite_eq_left hop.2.2, dite_eq_left hm, hparse, dite_eq_right ha, advanced, decoded]
          have hlast : logged.lastDown = some M := by
            rcases horigin with hold | hcurrent
            · have hstart := ReferenceFirstReplacementCollectionFollowerPrefix.downRecord_start_before_firstCutoff
                M payload.sigma row u (by
                  apply Fin.ext
                  have ht := ActiveFollowerDownAcceptance.downStart_val_add_one p rate M
                  have hM : M.val.sigma = payload.sigma.val + 1 := by
                    exact congrArg OrdinaryMessageCodec.DownFields.sigma (payload.downRecord_fields i)
                  omega) hfirst
              exact False.elim (ha ⟨hold, by omega⟩)
            · exact hcurrent
          have hnaccept : ¬ diag.ordinaryAcceptance := by
            intro h
            have ha' := (hcommon.2 hs).2.2.mp h
            exact ha (by simpa only [hparse, ReferenceDownReception.ordinaryLocalAcceptanceTest] using ha')
          refine ⟨advanced, ?_, hstable advanced (Or.inr rfl), hcommon.1, hcommon.2,
            hpreserve advanced, Or.inr (Or.inr (Or.inl ⟨hs, hraw, hcommon.1.trans hw,
              hfields.1, hfields.2.1, hfields.2.2, hnaccept, hout, rfl, hlast⟩))⟩
          rw [hout]
          rfl
    · have hout : diag.outcome = .decodeOrParseRejected logged advanced
        (ActiveFollowerDownAcceptance.currentDecodeStep p i row time own rate logged).2 := by
        simp only [diag, decoded, ReferenceDownReception.referenceDownCut, dite_eq_left hs,
          dite_eq_left hstatus, dite_eq_left hop.1, dite_eq_left hop.2.1,
          dite_eq_left hop.2.2, dite_eq_right hm, advanced, decoded]
      refine ⟨advanced, ?_, hstable advanced (Or.inr rfl), hcommon.1, hcommon.2,
        hpreserve advanced, Or.inr (Or.inl ⟨hs, hout, rfl, Or.inl ?_⟩)⟩
      · rw [hout]
        rfl
      · refine ⟨?_, ?_, ?_⟩
        · rw [hcommon.1]
          exact hm
        · simp only [diag, ReferenceDownReception.referenceDownCut, dite_eq_left hs,
            dite_eq_left hstatus, dite_eq_left hop.1, dite_eq_left hop.2.1,
            dite_eq_left hop.2.2, dite_eq_right hm]
        · simp only [diag, ReferenceDownReception.referenceDownCut, dite_eq_left hs,
            dite_eq_left hstatus, dite_eq_left hop.1, dite_eq_left hop.2.1,
            dite_eq_left hop.2.2, dite_eq_right hm]
  · have hout : diag.outcome = .skipped logged .notSelectedDown := by
      simp only [diag, ReferenceDownReception.referenceDownCut, dite_eq_right hs]
    refine ⟨logged, ?_, hstable logged (Or.inl rfl), ?_, ?_, hpreserve logged,
      Or.inl ⟨hs, hout, rfl, ?_⟩⟩
    · rw [hout]
      rfl
    · simp only [diag, ReferenceDownReception.referenceDownCut, dite_eq_right hs]
    · intro h
      exact False.elim (hs h)
    · simp only [diag, ReferenceDownReception.referenceDownCut, dite_eq_right hs, not_false_eq_true,
        and_self]

/-- One actual collection record, conditional only on the displayed local
induction inputs. Chronology and choice-view origin are produced at this same
complete-suffix index; no receiver or recovery success is supplied. -/
theorem actual_collection_follower_step
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (payload : ReferenceActivePhysicalStep.Payload rate) (u : ℕ) (i : Fin (p.m - 1))
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hinput : ((ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).get k).input.state.followers i = .ordinary state memory)
    (hstatus : state.status = .unoccupied)
    (hdomain : ActiveFollowerLifecycle.localStateDomainValid state)
    (hmass : state.S + state.backlog ≤ (u - 1) * D p)
    (hzero : state.lastDown = none → state.S = 0 ∧ state.delta = 0 ∧ state.backlog = 0)
    (horigin : ReferencePrelaunchFollower.acceptedStart state < (payload.downRecord i).val.sigma ∨
      state.lastDown = some (payload.downRecord i))
    (hc : ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h).get k).input.state.coordinator = .dagger ∨
      ∃ ledger saved, ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h).get k).input.state.coordinator =
          .collection payload ledger saved)
    (hn : ReferenceCollectionPhaseHistory.laterChosen ((ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).get k).input = false)
    (hu : 3 ≤ u)
    (hend : u ≤ ((ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).get k).input.time.val + 1)
    (hfirst : FollowerCutoffScan.firstCutoff p rate.eta.val payload.sigma
      (FollowerCutoffScan.completeRowProposalBit p rate.eta.val ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h).get k).input.row) = u)
    (hcredit : (payload.downRecord i).val.q ≤ ((payload.downRecord i).val.sigma - 1) * D p) :
    let r := (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).get k
    let prepared := r.output.preparation.followers.followers i
    let own := r.output.preparation.feedback.observations
      (PublicDiscreteDraws.followerPlayer p.two_le_m i)
    let view := r.output.preparation.coordinator.downView
    ∃ logged post,
      let decoded := ActiveFollowerDownAcceptance.currentDecodeStep
        p i r.input.row r.input.time own rate logged
      let diag := ReferenceDownReception.referenceDownCut
        p view i r.input.row r.input.time own rate logged
      let advanced := { logged with downBatch := decoded.1 }
      let M := payload.downRecord i
      let word := CoordinatorLocalArmChoice.storedDownFlatWord payload i
      ActiveFollowerLifecycle.startRound rate.eta r.input.time state memory = .ok (state, memory) ∧
      prepared.configuration = .ordinary state memory ∧
      OrdinaryMessageCodec.upAdmissible (ReferencePrelaunchFollower.codecParams p rate.eta)
        (ActiveFollowerQueueOperation.upOfferFields state) ∧
      ActiveFollowerLogging.checkedLogging i r.input.row (r.input.state.activations i)
        r.input.time (prepared.arm, own) state = .ok logged ∧
      logged.buffer = state.buffer ++ ReferencePrelaunchFollower.logAt i r.input.row
        (r.input.state.activations i) r.input.time (prepared.arm, own) ∧
      logged.lastDown = state.lastDown ∧ logged.S = state.S ∧ logged.delta = state.delta ∧
      logged.backlog = state.backlog ∧ logged.status = state.status ∧
      logged.downBatch = state.downBatch ∧ logged.initializationFailure = state.initializationFailure ∧
      ActiveFollowerLifecycle.localStateDomainValid logged ∧
      ActiveFollowerDownAcceptance.operationInputDomain p rate logged ∧
      logged.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound) ∧
      (∀ z ∈ logged.buffer, z.calendarRound < r.input.time.val + 2) ∧
      (ReferenceActivePhysicalStep.recordFollower view i r.input.row (r.input.state.activations i)
        r.input.time (r.input.active i) prepared.arm own state).result = .ok post ∧
      (ReferenceActivePhysicalStep.recordFollower view i r.input.row (r.input.state.activations i)
        r.input.time (r.input.active i) prepared.arm own state).downInput = some logged ∧
      (ReferenceActivePhysicalStep.recordFollower view i r.input.row (r.input.state.activations i)
        r.input.time (r.input.active i) prepared.arm own state).down = some diag ∧
      ActiveFollowerLifecycle.releaseAfterService rate.eta i r.input.time
        (ActiveFollowerLifecycle.publicRowOfCompleteRow r.input.row r.input.time)
        own state post = .ok post ∧
      ActiveFollowerLifecycle.finishRound rate.eta r.input.time r.input.row post memory =
        .ok (post, memory) ∧
      DeclaredFollowerLocalRound.releaseAndFinish rate i r.input.row r.input.time own state memory post =
        .ok (post, memory) ∧
      r.output.followers i = ⟨.ordinary post memory, none, some logged, some diag⟩ ∧
      DeclaredFollowerLocalRound.consumeDownResult rate diag.outcome = .ok post ∧
      (post.status = .unoccupied ∧ ActiveFollowerLifecycle.localStateDomainValid post ∧
        post.S + post.backlog ≤ (u - 1) * D p ∧ post.delta ≤ D p ∧
        post.initializationFailure = state.initializationFailure ∧
        (post.lastDown = none → post.S = 0 ∧ post.delta = 0 ∧ post.backlog = 0) ∧
        (ReferencePrelaunchFollower.acceptedStart post < M.val.sigma ∨ post.lastDown = some M) ∧
        post.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound) ∧
        (∀ z ∈ post.buffer, z.calendarRound < r.input.time.val + 2)) ∧
      diag.expectedWord = ReferenceDownReception.expectedDownFlatWord view i r.input.row r.input.time ∧
      (ActiveFollowerDownAcceptance.downSelected p i r.input.row r.input.time →
        diag.raw = decoded.2 ∧
        diag.ordinaryParse = ReferenceDownReception.ordinaryParse p rate decoded.2 ∧
        (diag.ordinaryAcceptance ↔ ReferenceDownReception.ordinaryLocalAcceptanceTest
          p rate r.input.time logged (ReferenceDownReception.ordinaryParse p rate decoded.2))) ∧
      ((post = logged ∨ post = advanced) → post.lastDown = state.lastDown ∧
        post.S = state.S ∧ post.delta = state.delta ∧ post.backlog = state.backlog) ∧
      ((¬ ActiveFollowerDownAcceptance.downSelected p i r.input.row r.input.time ∧
          diag.outcome = .skipped logged .notSelectedDown ∧ post = logged ∧
          diag.raw = none ∧ diag.filteredRaw = none ∧ diag.ordinaryParse = none ∧
          diag.rawComparison = none ∧ ¬ diag.ordinaryAcceptance) ∨
        (ActiveFollowerDownAcceptance.downSelected p i r.input.row r.input.time ∧
          diag.outcome = .decodeOrParseRejected logged advanced decoded.2 ∧ post = advanced ∧
          ((decoded.2 ≠ diag.expectedWord ∧ diag.filteredRaw = none ∧
              diag.rawComparison = some false) ∨
            (decoded.2 = none ∧ diag.expectedWord = none ∧ diag.filteredRaw = decoded.2 ∧
              diag.rawComparison = some true))) ∨
        (ActiveFollowerDownAcceptance.downSelected p i r.input.row r.input.time ∧
          decoded.2 = some word ∧ diag.expectedWord = some word ∧
          diag.filteredRaw = decoded.2 ∧ diag.rawComparison = some true ∧
          diag.ordinaryParse = some M ∧ ¬ diag.ordinaryAcceptance ∧
          diag.outcome = .parsedButUnaccepted logged advanced decoded.2 M ∧ post = advanced ∧
          state.lastDown = some M) ∨
        (ActiveFollowerDownAcceptance.downSelected p i r.input.row r.input.time ∧
          decoded.2 = some word ∧ diag.expectedWord = some word ∧
          diag.filteredRaw = decoded.2 ∧ diag.rawComparison = some true ∧
          diag.ordinaryParse = some M ∧ diag.ordinaryAcceptance ∧
          ∃ accepted : OrdinaryMessageCodec.acceptDown
              (ReferencePrelaunchFollower.codecParams p rate.eta)
              (ReferencePrelaunchFollower.acceptedStart logged) (r.input.time.val + 1) M,
            let scan := ActiveFollowerDownAcceptance.acceptedCutoffScan p rate M r.input.time
              (ActiveFollowerDownAcceptance.acceptedDownStartLE p rate M r.input.time logged accepted) r.input.row
            ∃ recovered : ActiveFollowerDownAcceptance.ReplayRegisters,
              scan.endpoint = u ∧
              ActiveFollowerDownAcceptance.checkedRecovery p rate M logged u = .ok recovered ∧
              diag.outcome = .accepted logged post decoded.2 M scan
                recovered.registers recovered.lastService ∧
              post = { advanced with
                lastDown := some M
                S := recovered.registers.1
                delta := recovered.lastService
                backlog := recovered.registers.2
                status := .unoccupied
                buffer := [] } ∧
              (∀ q ∈ ActiveFollowerDownAcceptance.recoveryQueueRecords p rate M logged u,
                q.1 = true) ∧
              recovered.registers = QueueReplay.replay (4 * rate.n) (0, M.val.q)
                (ActiveFollowerDownAcceptance.recoveryQueueRecords p rate M logged u) ∧
              recovered.registers.1 + recovered.registers.2 ≤ (u - 1) * D p ∧
              recovered.lastService ≤ D p ∧
              ActiveFollowerDownAcceptance.replay_register_domain (D p) (p.T * D p) recovered ∧
              ∀ b : ℕ, ∃ mid,
                ActiveFollowerDownAcceptance.checkedReplay (D p) (p.T * D p) (4 * rate.n) 0
                  ⟨(0, M.val.q), 0⟩
                  ((ActiveFollowerDownAcceptance.recoveryQueueRecords p rate M logged u).take b) =
                    .ok mid ∧
                ActiveFollowerDownAcceptance.replay_register_domain (D p) (p.T * D p) mid ∧
                mid.registers = QueueReplay.replay (4 * rate.n) (0, M.val.q)
                  ((ActiveFollowerDownAcceptance.recoveryQueueRecords p rate M logged u).take b))) := by
  classical
  intro r prepared own view
  obtain ⟨hstart, hprepared, hup⟩ := actual_collection_follower_prepare rate source rewards
    C_star C_h k i state memory hinput hdomain hstatus hzero
  have hchron := ReferenceFirstReplacementLiveFollowerPrefix.complete_input_buffer_chronological
    rate source rewards C_star C_h k i state memory hinput
  obtain ⟨logged, hlogging, hbuffer, hlogStatus, hlogFlag, hvalid⟩ :=
    ActiveFollowerLogging.checkedLogging_success_of_chronological i r.input.row
      (r.input.state.activations i) r.input.time (prepared.arm, own) state
      hdomain.2.1 hchron.2.2 hstatus
  have hframe := ActiveFollowerLogging.checkedLogging_success_frame i r.input.row
    (r.input.state.activations i) r.input.time (prepared.arm, own) state logged hlogging
  have hlu : logged.status = .unoccupied := hlogStatus.trans hstatus
  have hlogDomain : ActiveFollowerLifecycle.localStateDomainValid logged := by
    refine ⟨?_, hvalid, ?_⟩
    · simpa only [ActiveFollowerLifecycle.serviceRegistersValid,
        hframe.2.1, hframe.2.2.1, hframe.2.2.2.1] using hdomain.1
    · simpa only [ActiveFollowerLifecycle.downDecoderStateValid, hframe.2.2.2.2.2.1]
        using hdomain.2.2
  have hlogMass : logged.S + logged.backlog ≤ (u - 1) * D p := by
    simpa only [hframe.2.1, hframe.2.2.2.1] using hmass
  have hlogZero : logged.lastDown = none →
      logged.S = 0 ∧ logged.delta = 0 ∧ logged.backlog = 0 := by
    simpa only [hframe.1, hframe.2.1, hframe.2.2.1, hframe.2.2.2.1] using hzero
  have hlogOrigin : ReferencePrelaunchFollower.acceptedStart logged < (payload.downRecord i).val.sigma ∨
      logged.lastDown = some (payload.downRecord i) := by
    simpa only [ReferencePrelaunchFollower.acceptedStart, hframe.1] using horigin
  have hlogChron := logging_chronology i r.input.row (r.input.state.activations i)
    r.input.time (prepared.arm, own) state logged hbuffer hchron.2.1 hchron.2.2
  have hdispatch := ReferenceFirstReplacementCollectionDispatchOrigin.actual_collection_dispatch_step
    (rate := rate) r payload hc hn
  obtain ⟨post, hconsume, hpostFacts, hexpected, hselected, hpreserve, hbranches⟩ :=
    receiver_at_source_cutoff payload u i r.input.row r.input.time own logged hlu hlogDomain
      hlogMass hlogZero hlogOrigin hlogChron.1 hlogChron.2 view (hdispatch.2.2.2 i)
      hu hend hfirst hcredit
  have hrelease := ActiveFollowerLifecycle.releaseAfterService_unoccupied rate.eta i
    r.input.time (ActiveFollowerLifecycle.publicRowOfCompleteRow r.input.row r.input.time)
    own state post hstatus
  have hfinish := ActiveFollowerLifecycle.finishRound_unoccupied rate.eta r.input.time
    r.input.row post memory hpostFacts.2.1 hpostFacts.1
  have htail := DeclaredFollowerLocalRound.releaseAndFinish_unoccupied_memory rate i
    r.input.row r.input.time own state memory post post hrelease hpostFacts.2.1 hpostFacts.1
  have hrecord : (ReferenceActivePhysicalStep.recordFollower view i r.input.row
      (r.input.state.activations i) r.input.time (r.input.active i) prepared.arm own state).result =
        .ok post := by
    simp only [ReferenceActivePhysicalStep.recordFollower, dite_eq_left hstatus, hlogging, hconsume]
  have hdiagnostic := ReferenceActivePhysicalStep.recordFollower_logged view i r.input.row
    (r.input.state.activations i) r.input.time (r.input.active i) prepared.arm own state logged
    hstatus hlogging
  have halign := r.output.preparation.follower_alignment i
  have hrecordP : (ReferenceActivePhysicalStep.recordFollower view prepared.follower prepared.row
      prepared.activation prepared.time prepared.active prepared.arm own state).result = .ok post := by
    simpa only [prepared, halign.1, halign.2.1, halign.2.2.1, halign.2.2.2] using hrecord
  have htailP : DeclaredFollowerLocalRound.releaseAndFinish rate prepared.follower prepared.row
      prepared.time own state memory post = .ok (post, memory) := by
    simpa only [prepared, halign.1, halign.2.1, halign.2.2.1] using htail
  have houtput : r.output.followers i = ⟨.ordinary post memory, none, some logged,
      some (ReferenceDownReception.referenceDownCut p view i r.input.row r.input.time own rate logged)⟩ := by
    have hout : r.output.followers i = r.output.preparation.observeFollower i := by
      rw [r.output_eq]
      rfl
    rw [hout]
    change ReferenceActivePhysicalStep.finishFollower view prepared own = _
    change prepared.configuration = .ordinary state memory at hprepared
    unfold ReferenceActivePhysicalStep.finishFollower
    simp only [hprepared, hrecordP, htailP]
    congr 1
    · simpa only [prepared, halign.1, halign.2.1, halign.2.2.1, halign.2.2.2] using hdiagnostic.1
    · simpa only [prepared, halign.1, halign.2.1, halign.2.2.1, halign.2.2.2] using hdiagnostic.2
  refine ⟨logged, post, hstart, hprepared, hup, hlogging, hbuffer, hframe.1, hframe.2.1,
    hframe.2.2.1, hframe.2.2.2.1, hframe.2.2.2.2.1, hframe.2.2.2.2.2.1,
    hframe.2.2.2.2.2.2, hlogDomain, operation_input_of_local_domain logged hlogDomain,
    hlogChron.1, hlogChron.2, hrecord, hdiagnostic.1, hdiagnostic.2, hrelease, hfinish,
    htail, houtput, hconsume, ?_⟩
  have hrest := And.intro hpostFacts (And.intro hexpected
    (And.intro hselected (And.intro hpreserve hbranches)))
  simpa only [hframe.1, hframe.2.1, hframe.2.2.1, hframe.2.2.2.1, hframe.2.2.2.2.2.2] using hrest

/-- The actual first collection follower record after the first replacement
cutoff. All local induction inputs are produced by the integrated seed at
endpoint zero and dispatch origin on this actual window member. The empty
window and every nonselected dispatcher constructor remain explicit. -/
theorem complete_first_replacement_collection_first_record
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
            match W[0]? with
            | none => True
            | some r => ∀ i : Fin (p.m - 1), ∃ state memory,
              r.input.state.followers i = .ordinary state memory ∧
              let prepared := r.output.preparation.followers.followers i
              let own := r.output.preparation.feedback.observations
                (PublicDiscreteDraws.followerPlayer p.two_le_m i)
              let view := r.output.preparation.coordinator.downView
              ∃ logged post,
                let decoded := ActiveFollowerDownAcceptance.currentDecodeStep
                  p i r.input.row r.input.time own rate logged
                let diag := ReferenceDownReception.referenceDownCut
                  p view i r.input.row r.input.time own rate logged
                let advanced := { logged with downBatch := decoded.1 }
                let M := payload.downRecord i
                let word := CoordinatorLocalArmChoice.storedDownFlatWord payload i
                ActiveFollowerLifecycle.startRound rate.eta r.input.time state memory = .ok (state, memory) ∧
                prepared.configuration = .ordinary state memory ∧
                OrdinaryMessageCodec.upAdmissible (ReferencePrelaunchFollower.codecParams p rate.eta)
                  (ActiveFollowerQueueOperation.upOfferFields state) ∧
                ActiveFollowerLogging.checkedLogging i r.input.row (r.input.state.activations i)
                  r.input.time (prepared.arm, own) state = .ok logged ∧
                logged.buffer = state.buffer ++ ReferencePrelaunchFollower.logAt i r.input.row
                  (r.input.state.activations i) r.input.time (prepared.arm, own) ∧
                logged.lastDown = state.lastDown ∧ logged.S = state.S ∧ logged.delta = state.delta ∧
                logged.backlog = state.backlog ∧ logged.status = state.status ∧
                logged.downBatch = state.downBatch ∧ logged.initializationFailure = state.initializationFailure ∧
                ActiveFollowerLifecycle.localStateDomainValid logged ∧
                ActiveFollowerDownAcceptance.operationInputDomain p rate logged ∧
                logged.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound) ∧
                (∀ z ∈ logged.buffer, z.calendarRound < r.input.time.val + 2) ∧
                (ReferenceActivePhysicalStep.recordFollower view i r.input.row (r.input.state.activations i)
                  r.input.time (r.input.active i) prepared.arm own state).result = .ok post ∧
                (ReferenceActivePhysicalStep.recordFollower view i r.input.row (r.input.state.activations i)
                  r.input.time (r.input.active i) prepared.arm own state).downInput = some logged ∧
                (ReferenceActivePhysicalStep.recordFollower view i r.input.row (r.input.state.activations i)
                  r.input.time (r.input.active i) prepared.arm own state).down = some diag ∧
                ActiveFollowerLifecycle.releaseAfterService rate.eta i r.input.time
                  (ActiveFollowerLifecycle.publicRowOfCompleteRow r.input.row r.input.time)
                  own state post = .ok post ∧
                ActiveFollowerLifecycle.finishRound rate.eta r.input.time r.input.row post memory =
                  .ok (post, memory) ∧
                DeclaredFollowerLocalRound.releaseAndFinish rate i r.input.row r.input.time own state memory post =
                  .ok (post, memory) ∧
                r.output.followers i = ⟨.ordinary post memory, none, some logged, some diag⟩ ∧
                DeclaredFollowerLocalRound.consumeDownResult rate diag.outcome = .ok post ∧
                (post.status = .unoccupied ∧ ActiveFollowerLifecycle.localStateDomainValid post ∧
                  post.S + post.backlog ≤ (u - 1) * D p ∧ post.delta ≤ D p ∧
                  post.initializationFailure = state.initializationFailure ∧
                  (post.lastDown = none → post.S = 0 ∧ post.delta = 0 ∧ post.backlog = 0) ∧
                  (ReferencePrelaunchFollower.acceptedStart post < M.val.sigma ∨ post.lastDown = some M) ∧
                  post.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound) ∧
                  (∀ z ∈ post.buffer, z.calendarRound < r.input.time.val + 2)) ∧
                diag.expectedWord = ReferenceDownReception.expectedDownFlatWord view i r.input.row r.input.time ∧
                (ActiveFollowerDownAcceptance.downSelected p i r.input.row r.input.time →
                  diag.raw = decoded.2 ∧
                  diag.ordinaryParse = ReferenceDownReception.ordinaryParse p rate decoded.2 ∧
                  (diag.ordinaryAcceptance ↔ ReferenceDownReception.ordinaryLocalAcceptanceTest
                    p rate r.input.time logged (ReferenceDownReception.ordinaryParse p rate decoded.2))) ∧
                ((post = logged ∨ post = advanced) → post.lastDown = state.lastDown ∧
                  post.S = state.S ∧ post.delta = state.delta ∧ post.backlog = state.backlog) ∧
                ((¬ ActiveFollowerDownAcceptance.downSelected p i r.input.row r.input.time ∧
                    diag.outcome = .skipped logged .notSelectedDown ∧ post = logged ∧
                    diag.raw = none ∧ diag.filteredRaw = none ∧ diag.ordinaryParse = none ∧
                    diag.rawComparison = none ∧ ¬ diag.ordinaryAcceptance) ∨
                  (ActiveFollowerDownAcceptance.downSelected p i r.input.row r.input.time ∧
                    diag.outcome = .decodeOrParseRejected logged advanced decoded.2 ∧ post = advanced ∧
                    ((decoded.2 ≠ diag.expectedWord ∧ diag.filteredRaw = none ∧
                        diag.rawComparison = some false) ∨
                      (decoded.2 = none ∧ diag.expectedWord = none ∧ diag.filteredRaw = decoded.2 ∧
                        diag.rawComparison = some true))) ∨
                  (ActiveFollowerDownAcceptance.downSelected p i r.input.row r.input.time ∧
                    decoded.2 = some word ∧ diag.expectedWord = some word ∧
                    diag.filteredRaw = decoded.2 ∧ diag.rawComparison = some true ∧
                    diag.ordinaryParse = some M ∧ ¬ diag.ordinaryAcceptance ∧
                    diag.outcome = .parsedButUnaccepted logged advanced decoded.2 M ∧ post = advanced ∧
                    state.lastDown = some M) ∨
                  (ActiveFollowerDownAcceptance.downSelected p i r.input.row r.input.time ∧
                    decoded.2 = some word ∧ diag.expectedWord = some word ∧
                    diag.filteredRaw = decoded.2 ∧ diag.rawComparison = some true ∧
                    diag.ordinaryParse = some M ∧ diag.ordinaryAcceptance ∧
                    ∃ accepted : OrdinaryMessageCodec.acceptDown
                        (ReferencePrelaunchFollower.codecParams p rate.eta)
                        (ReferencePrelaunchFollower.acceptedStart logged) (r.input.time.val + 1) M,
                      let scan := ActiveFollowerDownAcceptance.acceptedCutoffScan p rate M r.input.time
                        (ActiveFollowerDownAcceptance.acceptedDownStartLE p rate M r.input.time logged accepted) r.input.row
                      ∃ recovered : ActiveFollowerDownAcceptance.ReplayRegisters,
                        scan.endpoint = u ∧
                        ActiveFollowerDownAcceptance.checkedRecovery p rate M logged u = .ok recovered ∧
                        diag.outcome = .accepted logged post decoded.2 M scan
                          recovered.registers recovered.lastService ∧
                        post = { advanced with
                          lastDown := some M
                          S := recovered.registers.1
                          delta := recovered.lastService
                          backlog := recovered.registers.2
                          status := .unoccupied
                          buffer := [] } ∧
                        (∀ q ∈ ActiveFollowerDownAcceptance.recoveryQueueRecords p rate M logged u,
                          q.1 = true) ∧
                        recovered.registers = QueueReplay.replay (4 * rate.n) (0, M.val.q)
                          (ActiveFollowerDownAcceptance.recoveryQueueRecords p rate M logged u) ∧
                        recovered.registers.1 + recovered.registers.2 ≤ (u - 1) * D p ∧
                        recovered.lastService ≤ D p ∧
                        ActiveFollowerDownAcceptance.replay_register_domain (D p) (p.T * D p) recovered ∧
                        ∀ b : ℕ, ∃ mid,
                          ActiveFollowerDownAcceptance.checkedReplay (D p) (p.T * D p) (4 * rate.n) 0
                            ⟨(0, M.val.q), 0⟩
                            ((ActiveFollowerDownAcceptance.recoveryQueueRecords p rate M logged u).take b) =
                              .ok mid ∧
                          ActiveFollowerDownAcceptance.replay_register_domain (D p) (p.T * D p) mid ∧
                          mid.registers = QueueReplay.replay (4 * rate.n) (0, M.val.q)
                            ((ActiveFollowerDownAcceptance.recoveryQueueRecords p rate M logged u).take b)))
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
          set payload := installed.registers.payload
          set c := v + 1 + (ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v).length
          cases hcutGet : R[c]? with
          | none => trivial
          | some cut =>
              simp only [hcutGet] at hS hA ⊢
              cases hcutCoord : cut.output.preparation.coordinator with
              | first _ => trivial
              | collection _ _ _ _ _ => trivial
              | dagger => trivial
              | invalidCollectionCutoff => trivial
              | live _ _ _ outcome =>
                  rw [hcutCoord] at hS hA
                  cases outcome <;> try trivial
                  dsimp only at hS hA ⊢
                  set u := cut.input.time.val + 1
                  set W := (R.drop (c + 1)).takeWhile
                    (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
                  rcases hS with ⟨_, _, _, hu, _, hfirst, hseed, hgeometry⟩
                  cases hWGet : W[0]? with
                  | none => trivial
                  | some r =>
                      obtain ⟨hj, hWval⟩ := List.getElem?_eq_some_iff.mp hWGet
                      have hWrecord : W.get ⟨0, hj⟩ = r := hWval
                      have hRGet : R[c + 1 + 0]? = some r := by
                        have hget := ReferenceFirstReplacementCollectionFollowerPrefix.collectionWindow_get
                          R c 0 hj
                        rw [hWrecord] at hget
                        exact hget
                      obtain ⟨hk, hRval⟩ := List.getElem?_eq_some_iff.mp hRGet
                      let k : Fin R.length := ⟨c + 1 + 0, hk⟩
                      have hr : R.get k = r := hRval
                      have hgeo := hgeometry 0 (Nat.zero_le W.length)
                      rw [hRGet] at hgeo
                      rcases hgeo with ⟨hstate, htime, hrows, hselectedRow, _, _, _⟩
                      have hAfirst := hA.2 ⟨0, hj⟩
                      rw [hWrecord] at hAfirst
                      have hn : ReferenceCollectionPhaseHistory.laterChosen r.input = false := by
                        have hmem : r ∈ W := hWrecord ▸ List.get_mem W ⟨0, hj⟩
                        have hpred := List.mem_takeWhile_imp hmem
                        cases hb : ReferenceCollectionPhaseHistory.laterChosen r.input <;>
                          simp [hb] at hpred ⊢
                      obtain ⟨hc, hcutval⟩ := List.getElem?_eq_some_iff.mp hcutGet
                      have hcutRecord : R.get ⟨c, hc⟩ = cut := hcutval
                      obtain ⟨_, _, hcutSource⟩ := ReferenceLaterLiveNumericalReadout.source_record_prefix
                        rate rewards C_star C_h source ⟨c, hc⟩
                      have hcutRow : cut.input.row = source.1.2
                          (ActualInitializationPhysicalStep.selectedRowIndex p source) := by
                        rw [← hcutRecord, hcutSource]
                        rfl
                      have hrow : r.input.row = cut.input.row := by
                        rw [hcutRow]
                        change r.input.rows r.input.selected = _
                        rw [hrows, hselectedRow]
                      have hfirstR : FollowerCutoffScan.firstCutoff p rate.eta.val payload.sigma
                          (FollowerCutoffScan.completeRowProposalBit p rate.eta.val r.input.row) = u := by
                        rw [hrow]
                        exact hfirst
                      intro i
                      rcases hseed i with ⟨_, hcredit, old, state, memory, _, _, _, hendpoint,
                        hstatus, hdomain, hmass, _, hzero, horigin, _, _, _⟩
                      have hinput : r.input.state.followers i = .ordinary state memory := by
                        rw [hstate]
                        exact hendpoint
                      have hprep := actual_collection_follower_prepare rate source rewards C_star C_h
                        k i state memory (by rw [hr]; exact hinput) hdomain hstatus hzero
                      have hstep := actual_collection_follower_step rate source rewards C_star C_h
                        k payload u i state memory (by rw [hr]; exact hinput) hstatus hdomain
                        hmass hzero horigin (by rw [hr]; exact hAfirst.1)
                        (by rw [hr]; exact hn) hu (by rw [hr]; omega)
                        (by rw [hr]; exact hfirstR) hcredit
                      rw [hr] at hprep hstep
                      obtain ⟨logged, post, hstep⟩ := hstep
                      refine ⟨state, memory, hinput, logged, post,
                        hprep.1, hprep.2.1, hprep.2.2, ?_⟩
                      exact hstep.2.2.2

end Bandits.Support.ReferenceFirstReplacementCollectionOneRecord

end
