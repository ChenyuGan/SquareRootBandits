/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstReplacementFollowerLoggingSeed
import Lean.Elab.Tactic.Omega

/-!
# First replacement DOWN recovery and the follower's round tail

Sources: `sources/zip4/manuscript/06_interruptions.tex:9-70,193-233,246-295`,
`sources/zip4/manuscript/05_binary_transport.tex:70-124,354-431`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-64`.

These are internal local results. Recovery at the new assignment's birth
has one enabled calendar update. DOWN cannot append a DATA observation, and
the retained buffer precedes the new start, so that update has zero arrival.
Its initial queue is the actual new DOWN queue and need not be zero.
-/

@[expose] public section
noncomputable section

namespace Bandits.Support.ReferenceFirstReplacementDownRecovery

open ConstructorDimensions ReferencePrelaunchFollower ActiveFollowerLifecycle
open ActiveFollowerDownAcceptance ReferenceDownReception

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

/-- The common carried domain supplies all three actual DOWN input checks.
Quantization is inherited from the saved observations, including zeros. -/
private theorem operation_input_of_local_domain
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (h : localStateDomainValid state) : operationInputDomain p rate state := by
  refine ⟨h.1, h.2.2, ?_⟩
  refine ⟨?_, h.2.1.2.1⟩
  intro saved hsaved
  obtain ⟨q, hq, heq⟩ := h.2.1.2.2 saved hsaved
  exact ⟨(h.2.1.1 saved hsaved).1, (h.2.1.1 saved hsaved).2,
    ⟨⟨q, by omega⟩, heq⟩⟩

/-- DOWN does not log. This is an equality of the full state, retaining the
complete old buffer and decoder, without a condition on the observation. -/
private theorem logged_eq_old_on_down
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (activation : Activation p) (t : Fin p.T) (own : Fin p.K × Observation p)
    (old logged : ReferencePrelaunchFollower.State p rate.eta)
    (hlogging : ActiveFollowerLogging.checkedLogging i row activation t own old = .ok logged)
    (hdown : PublicDiscreteDraws.slotDraw (row.2 t).1 = PublicDiscreteDraws.downSlot) :
    logged = old := by
  classical
  have htests : ¬ SparseCalendarReplay.loggingTestsPass
      (loggingRound i row activation t own) := by
    intro h
    have hdata := (ActiveFollowerLogging.loggingTestsPass_iff_source_mask
      i row activation t own).mp h |>.2.1
    rw [hdown] at hdata
    cases hdata
  have hnil := ActiveFollowerLogging.logAt_eq_nil_of_not_tests
    i row activation t own htests
  have heq := (ActiveFollowerLogging.checkedLogging_success_iff
    i row activation t own old logged).mp hlogging |>.2.1
  rw [heq]
  unfold ActiveFollowerLogging.loggingUpdate
  split <;> simp only [hnil, List.append_nil]

/-- A buffer strictly before this calendar stamp contributes zero there.
The saved real thinning scalars and zero observations are left untouched. -/
private theorem buffer_arrival_zero_of_before
    (M : OrdinaryMessageCodec.DownRecord (codecParams p rate.eta))
    (state : ReferencePrelaunchFollower.State p rate.eta) (r : ℕ)
    (hbefore : ∀ saved ∈ state.buffer, saved.calendarRound < r) :
    bufferArrivalAt p rate M state r = 0 := by
  unfold bufferArrivalAt
  generalize state.buffer = buffer at hbefore ⊢
  revert hbefore
  induction buffer with
  | nil => intro _; rfl
  | cons saved rest ih =>
      intro hbefore
      have hne : ¬ (saved.calendarRound = r ∧
          saved.pilot = PrelaunchBufferRecovery.downArm rate.eta M) := by
        have hlt := hbefore saved List.mem_cons_self
        omega
      change (if saved.calendarRound = r ∧
          saved.pilot = PrelaunchBufferRecovery.downArm rate.eta M then
            SparseCalendarReplay.savedContribution p.K (p.m - 1) (D p : ℝ)
              rate.eta.val M.val.h saved.observation saved.thinScalar else 0) + _ = 0
      rw [ite_eq_right hne, zero_add]
      exact ih (fun item hi => hbefore item (List.mem_cons_of_mem _ hi))

/-- At birth the literal accepted scan has no past proposal coordinates.
The endpoint bounds include the clipped final physical round. -/
theorem accepted_scan_at_birth
    (M : OrdinaryMessageCodec.DownRecord (codecParams p rate.eta))
    (t : Fin p.T) (row : CompletePublicTable.CompleteRow p)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (hsigma : M.val.sigma = t.val + 1)
    (ha : OrdinaryMessageCodec.acceptDown (codecParams p rate.eta)
      (acceptedStart state) (t.val + 1) M) :
    acceptedCutoffScan p rate M t (acceptedDownStartLE p rate M t state ha) row =
      ⟨t.val + 2, []⟩ := by
  have hstart := downStart_val_add_one p rate M
  have hbounds := acceptedCutoff_interval_bounds p rate M t row state ha
  have hend : (acceptedCutoffScan p rate M t
      (acceptedDownStartLE p rate M t state ha) row).endpoint = t.val + 2 := by omega
  have hnil : (acceptedCutoffScan p rate M t
      (acceptedDownStartLE p rate M t state ha) row).inspected = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro j hj
    have hb := FollowerCutoffScan.followerCutoffScan_inspected_source_bounds
      p rate.eta.val (downStart p rate M) t (acceptedDownStartLE p rate M t state ha)
      (FollowerCutoffScan.completeRowProposalBit p rate.eta.val row) j hj
    omega
  cases hscan : acceptedCutoffScan p rate M t
      (acceptedDownStartLE p rate M t state ha) row with
  | mk endpoint inspected =>
      simp only [hscan] at hend hnil
      cases hend
      cases hnil
      rfl

/-- Exactly one ENABLED update services the nonzero-capable parsed queue.
Both the empty prefix and the updated registers pass the actual checks. -/
theorem checked_recovery_one_zero_arrival
    (M : OrdinaryMessageCodec.DownRecord (codecParams p rate.eta))
    (state : ReferencePrelaunchFollower.State p rate.eta) (t : Fin p.T)
    (hsigma : M.val.sigma = t.val + 1)
    (hcredit : M.val.q ≤ t.val * D p)
    (hzero : bufferArrivalAt p rate M state (t.val + 1) = 0) :
    recoveryRounds p rate M (t.val + 2) = [t.val + 1] ∧
    recoveryQueueRecords p rate M state (t.val + 2) = [(true, 0)] ∧
    checkedRecovery p rate M state (t.val + 2) =
      .ok ⟨(min (4 * rate.n) M.val.q, M.val.q - min (4 * rate.n) M.val.q),
        min (4 * rate.n) M.val.q⟩ ∧
    min (4 * rate.n) M.val.q + (M.val.q - min (4 * rate.n) M.val.q) = M.val.q ∧
    replay_register_domain (D p) (p.T * D p) ⟨(0, M.val.q), 0⟩ ∧
    replay_register_domain (D p) (p.T * D p)
      ⟨(min (4 * rate.n) M.val.q, M.val.q - min (4 * rate.n) M.val.q),
        min (4 * rate.n) M.val.q⟩ := by
  have hrounds : recoveryRounds p rate M (t.val + 2) = [t.val + 1] := by
    simp [recoveryRounds, SparseCalendarReplay.sparseCalendarRounds, hsigma]
  have hrecords : recoveryQueueRecords p rate M state (t.val + 2) = [(true, 0)] := by
    simp only [recoveryQueueRecords, recoveryArrivals, hrounds, List.map_cons,
      List.map_nil, hzero]
  have hq : M.val.q ≤ p.T * D p :=
    hcredit.trans (Nat.mul_le_mul_right (D p) (Nat.le_of_lt t.isLt))
  have hservice : min (4 * rate.n) M.val.q ≤ D p :=
    (Nat.min_le_left _ _).trans (four_n_le_D p rate)
  have hmin := Nat.min_le_right (4 * rate.n) M.val.q
  have hmass : min (4 * rate.n) M.val.q +
      (M.val.q - min (4 * rate.n) M.val.q) = M.val.q := Nat.add_sub_of_le hmin
  have hi : replay_register_domain (D p) (p.T * D p) ⟨(0, M.val.q), 0⟩ :=
    ⟨Nat.zero_le _, Nat.zero_le _, hq⟩
  have hf : replay_register_domain (D p) (p.T * D p)
      ⟨(min (4 * rate.n) M.val.q, M.val.q - min (4 * rate.n) M.val.q),
        min (4 * rate.n) M.val.q⟩ :=
    ⟨hmin.trans hq, hservice, (Nat.sub_le _ _).trans hq⟩
  refine ⟨hrounds, hrecords, ?_, hmass, hi, hf⟩
  rw [checkedRecovery_eq_checkedReplay, hrecords]
  have hu : checkedReplayUpdate (D p) (p.T * D p) (4 * rate.n)
      ⟨(0, M.val.q), 0⟩ (true, 0) =
      .ok ⟨(min (4 * rate.n) M.val.q, M.val.q - min (4 * rate.n) M.val.q),
        min (4 * rate.n) M.val.q⟩ := by
    simp only [checkedReplayUpdate, replayService, QueueReplay.transition,
      Nat.add_zero, Nat.zero_add, ite_true]
    rw [ite_eq_left (Nat.zero_le _), ite_eq_left hservice,
      ite_eq_left hf.1, ite_eq_left hf.2.2]
  simp only [checkedReplay, ite_eq_left hi, hu, ite_eq_left hf]

/-- The expected flat word parses to the NEW payload's actual DOWN record. -/
private theorem parse_stored_down
    (payload : ReferenceActivePhysicalStep.Payload rate) (i : Fin (p.m - 1)) :
    ordinaryParse p rate (some (CoordinatorLocalArmChoice.storedDownFlatWord payload i)) =
      some (payload.downRecord i) := by
  unfold ordinaryParse CoordinatorLocalArmChoice.storedDownFlatWord
  change OrdinaryMessageCodec.parseDown (codecParams p rate.eta)
    (some ((OrdinaryMessageCodec.wordEquivFlat _).symm
      ((OrdinaryMessageCodec.wordEquivFlat _) (payload.downWord i)))) = _
  rw [(OrdinaryMessageCodec.wordEquivFlat _).symm_apply_apply]
  exact payload.parseDown_downWord i

/-- Exhaust the actual pre-effect receiver cut at the new start. The local
conditional inputs below are produced from the source root, never assumed
there. Neither delivery, a unique solution, matching, nor acceptance is an
input: the returned raw word is split internally. -/
private theorem down_cut_at_birth
    (view : Option (ChoiceTimeView p rate.eta))
    (payload : ReferenceActivePhysicalStep.Payload rate) (i : Fin (p.m - 1))
    (row : CompletePublicTable.CompleteRow p) (t : Fin p.T) (own : Observation p)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (hdomain : localStateDomainValid state) (hstatus : state.status = .unoccupied)
    (hsigma : (payload.downRecord i).val.sigma = t.val + 1)
    (hstrict : acceptedStart state < (payload.downRecord i).val.sigma)
    (hcredit : (payload.downRecord i).val.q ≤ t.val * D p)
    (hexpected : downSelected p i row t → expectedDownFlatWord view i row t =
      some (CoordinatorLocalArmChoice.storedDownFlatWord payload i))
    (hzero : downSelected p i row t →
      bufferArrivalAt p rate (payload.downRecord i) state (t.val + 1) = 0) :
    let M := payload.downRecord i
    let decoded := currentDecodeStep p i row t own rate state
    let cut := referenceDownCut p view i row t own rate state
    let service := min (4 * rate.n) M.val.q
    let afterDecode := { state with downBatch := decoded.1 }
    let accepted := { afterDecode with
      lastDown := some M
      S := service
      delta := service
      backlog := M.val.q - service
      status := .pending
      buffer := [] }
    (¬ downSelected p i row t ∧ cut.outcome = .skipped state .notSelectedDown) ∨
    (downSelected p i row t ∧ cut.raw = decoded.2 ∧ cut.filteredRaw = none ∧
      cut.outcome = .decodeOrParseRejected state afterDecode decoded.2 ∧
      cut.rawComparison = some false) ∨
    (downSelected p i row t ∧ decoded.2 =
        some (CoordinatorLocalArmChoice.storedDownFlatWord payload i) ∧
      cut.raw = decoded.2 ∧ cut.filteredRaw = decoded.2 ∧
      cut.rawComparison = some true ∧ cut.ordinaryParse = some M ∧
      cut.ordinaryAcceptance ∧
      cut.outcome = .accepted state accepted decoded.2 M ⟨t.val + 2, []⟩
        (service, M.val.q - service) service ∧
      bufferArrivalAt p rate M state (t.val + 1) = 0 ∧
      recoveryQueueRecords p rate M state (t.val + 2) = [(true, 0)] ∧
      checkedRecovery p rate M state (t.val + 2) =
        .ok ⟨(service, M.val.q - service), service⟩) := by
  classical
  dsimp only
  obtain ⟨hregisters, hbatch, hbuffer⟩ := operation_input_of_local_domain state hdomain
  by_cases hselected : downSelected p i row t
  · have he := hexpected hselected
    have ha : OrdinaryMessageCodec.acceptDown (codecParams p rate.eta)
        (acceptedStart state) (t.val + 1) (payload.downRecord i) :=
      ⟨hstrict, Nat.le_of_eq hsigma⟩
    have hscan := accepted_scan_at_birth (payload.downRecord i) t row state hsigma ha
    have hrecovery := checked_recovery_one_zero_arrival (payload.downRecord i) state t
      hsigma hcredit (hzero hselected)
    by_cases hmatches : (currentDecodeStep p i row t own rate state).2 =
        expectedDownFlatWord view i row t
    · have hraw := hmatches.trans he
      have hp := parse_stored_down payload i
      have hparse : ordinaryParse p rate (currentDecodeStep p i row t own rate state).2 =
          some (payload.downRecord i) := by rw [hraw]; exact hp
      right; right
      refine ⟨hselected, hraw, ?_⟩
      simp only [referenceDownCut, dite_eq_left hselected, dite_eq_left hstatus,
        dite_eq_left hregisters, dite_eq_left hbatch, dite_eq_left hbuffer,
        dite_eq_left hmatches, hparse, hscan, hrecovery.2.2.1,
        ite_true, ordinaryLocalAcceptanceTest, ha, hzero hselected,
        hrecovery.2.1, dite_true, and_true]
    · right; left
      refine ⟨hselected, ?_⟩
      simp only [referenceDownCut, dite_eq_left hselected, dite_eq_left hstatus,
        dite_eq_left hregisters, dite_eq_left hbatch, dite_eq_left hbuffer,
        dite_eq_right hmatches, and_self]
  · left
    exact ⟨hselected, by simp only [referenceDownCut, dite_eq_right hselected]⟩

/-- Compose a computed successful receiver outcome with the actual follower
tail. All conditional inputs are explicit; the source root supplies them
separately for every receiver alternative. Release uses OLD choice status. -/
private theorem finish_actual
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1))
    (old logged next : ReferencePrelaunchFollower.State p rate.eta) (memory : LocalMemory p)
    (hconfiguration : (record.output.preparation.followers.followers i).configuration =
      .ordinary old memory)
    (hstatus : old.status = .unoccupied)
    (hlogging : ActiveFollowerLogging.checkedLogging i record.input.row
      (record.input.state.activations i) record.input.time
      ((record.output.preparation.followers.followers i).arm,
        record.output.preparation.feedback.observations
          (PublicDiscreteDraws.followerPlayer p.two_le_m i)) old = .ok logged)
    (hconsume : DeclaredFollowerLocalRound.consumeDownResult rate
      (referenceDownCut p record.output.preparation.coordinator.downView i record.input.row
        record.input.time (record.output.preparation.feedback.observations
          (PublicDiscreteDraws.followerPlayer p.two_le_m i)) rate logged).outcome = .ok next)
    (hdomain : localStateDomainValid next)
    (hmass : next.S + next.backlog ≤ (record.input.time.val + 1) * D p)
    (hmarker : next.initializationFailure = old.initializationFailure)
    (hcompatible : next.status ≠ .unoccupied → ∃ M,
      next.lastDown = some M ∧ M.val.sigma ≤ record.input.time.val + 1) :
    let x := record.input
    let own := record.output.preparation.feedback.observations
      (PublicDiscreteDraws.followerPlayer p.two_le_m i)
    let cut := referenceDownCut p record.output.preparation.coordinator.downView
      i x.row x.time own rate logged
    let nextMemory : LocalMemory p := if next.status = .unoccupied then memory else
      ⟨some ⟨x.time, FollowerCutoffScan.completeRowProposalBit p rate.eta.val x.row x.time⟩⟩
    DeclaredFollowerLocalRound.consumeDownResult rate cut.outcome = .ok next ∧
    releaseAfterService rate.eta i x.time (publicRowOfCompleteRow x.row x.time)
      own old next = .ok next ∧
    finishRound rate.eta x.time x.row next memory = .ok (next, nextMemory) ∧
    DeclaredFollowerLocalRound.releaseAndFinish rate i x.row x.time own old memory next =
      .ok (next, nextMemory) ∧
    record.output.followers i = ⟨.ordinary next nextMemory, none, some logged, some cut⟩ ∧
    localStateDomainValid next ∧
    next.S + next.backlog ≤ (x.time.val + 1) * D p ∧ next.delta ≤ D p ∧
    next.initializationFailure = old.initializationFailure := by
  classical
  dsimp only
  let nextMemory : LocalMemory p := if next.status = .unoccupied then memory else
    ⟨some ⟨record.input.time, FollowerCutoffScan.completeRowProposalBit
      p rate.eta.val record.input.row record.input.time⟩⟩
  have hrelease := releaseAfterService_unoccupied rate.eta i record.input.time
    (publicRowOfCompleteRow record.input.row record.input.time)
    (record.output.preparation.feedback.observations
      (PublicDiscreteDraws.followerPlayer p.two_le_m i)) old next hstatus
  have hfinish : finishRound rate.eta record.input.time record.input.row next memory =
      .ok (next, nextMemory) := by
    by_cases hu : next.status = .unoccupied
    · simpa only [nextMemory, ite_eq_left hu] using
        finishRound_unoccupied rate.eta record.input.time record.input.row next memory hdomain hu
    · obtain ⟨M, hM, ht⟩ := hcompatible hu
      simpa only [nextMemory, ite_eq_right hu] using finishRound_occupied_read
        rate.eta record.input.time record.input.row next memory hu hdomain M hM ht
  have htail : DeclaredFollowerLocalRound.releaseAndFinish rate i record.input.row
      record.input.time (record.output.preparation.feedback.observations
        (PublicDiscreteDraws.followerPlayer p.two_le_m i)) old memory next =
      .ok (next, nextMemory) := by
    simp only [DeclaredFollowerLocalRound.releaseAndFinish, hrelease, hfinish]
  refine ⟨hconsume, hrelease, hfinish, htail, ?_, hdomain, hmass, hdomain.1.2.1, hmarker⟩
  have halign := record.output.preparation.follower_alignment i
  have hrecord : (ReferenceActivePhysicalStep.recordFollower
      record.output.preparation.coordinator.downView i record.input.row
      (record.input.state.activations i) record.input.time (record.input.active i)
      (record.output.preparation.followers.followers i).arm
      (record.output.preparation.feedback.observations
        (PublicDiscreteDraws.followerPlayer p.two_le_m i)) old).result = .ok next := by
    simp only [ReferenceActivePhysicalStep.recordFollower, dite_eq_left hstatus,
      hlogging, hconsume]
  have hdiagnostic := ReferenceActivePhysicalStep.recordFollower_logged
    record.output.preparation.coordinator.downView i record.input.row
    (record.input.state.activations i) record.input.time (record.input.active i)
    (record.output.preparation.followers.followers i).arm
    (record.output.preparation.feedback.observations
      (PublicDiscreteDraws.followerPlayer p.two_le_m i)) old logged hstatus hlogging
  have hresultP : (ReferenceActivePhysicalStep.recordFollower
      record.output.preparation.coordinator.downView
      (record.output.preparation.followers.followers i).follower
      (record.output.preparation.followers.followers i).row
      (record.output.preparation.followers.followers i).activation
      (record.output.preparation.followers.followers i).time
      (record.output.preparation.followers.followers i).active
      (record.output.preparation.followers.followers i).arm
      (record.output.preparation.feedback.observations
        (PublicDiscreteDraws.followerPlayer p.two_le_m i)) old).result = .ok next := by
    simpa only [halign.1, halign.2.1, halign.2.2.1, halign.2.2.2] using hrecord
  have htailP : DeclaredFollowerLocalRound.releaseAndFinish rate
      (record.output.preparation.followers.followers i).follower
      (record.output.preparation.followers.followers i).row
      (record.output.preparation.followers.followers i).time
      (record.output.preparation.feedback.observations
        (PublicDiscreteDraws.followerPlayer p.two_le_m i)) old memory next =
      .ok (next, nextMemory) := by
    simpa only [halign.1, halign.2.1, halign.2.2.1] using htail
  have hout : record.output.followers i = record.output.preparation.observeFollower i := by
    rw [record.output_eq]
    rfl
  rw [hout]
  unfold ReferenceActivePhysicalStep.PreparedRound.observeFollower
    ReferenceActivePhysicalStep.finishFollower
  simp only [hconfiguration, hresultP, htailP]
  congr 1
  · simpa only [halign.1, halign.2.1, halign.2.2.1, halign.2.2.2] using hdiagnostic.1
  · simpa only [halign.1, halign.2.1, halign.2.2.1, halign.2.2.2] using hdiagnostic.2

/-- On the original complete source, every follower finishes the first
replacement ROUND ordinarily, if that replacement is reached. All absent,
failed, terminal, and other dispatcher branches retain the conclusion `True`.

The local result records the pre-effect cut and exhausts its real alternatives.
An accepted current word recovers one enabled zero-arrival update from its
actual, possibly nonzero, immutable queue. An unaccepted word retains the
whole logged buffer and old reply, with only the actual decoder advancement.
No replacement existence, later survival, queue authenticity, probability
law, or manuscript theorem is asserted. -/
theorem complete_first_replacement_down_recovery_and_finish
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
    let s := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
    let Cwin := ReferenceCollectionPhaseHistory.collectionWindow R w
    let v := w + Cwin.length
    match R[v]? with
    | none => True
    | some record => match record.output.preparation.coordinator with
      | .collection _oldPayload _ledger _ _
          (.laterChosen _ _ _ _ _ _ _output _ _clockData installed _) =>
          let x := record.input
          s < x.time.val ∧ ∀ i : Fin (p.m - 1),
            let prepared := record.output.preparation.followers.followers i
            let own := record.output.preparation.feedback.observations
              (PublicDiscreteDraws.followerPlayer p.two_le_m i)
            let M := installed.registers.payload.downRecord i
            let service := min (4 * rate.n) M.val.q
            ∃ old memory logged,
              x.state.followers i = .ordinary old memory ∧
              old.status = .unoccupied ∧ prepared.configuration = .ordinary old memory ∧
              ActiveFollowerLogging.checkedLogging i x.row (x.state.activations i)
                x.time (prepared.arm, own) old = .ok logged ∧
              operationInputDomain p rate logged ∧
              acceptedStart logged < M.val.sigma ∧ M.val.sigma = x.time.val + 1 ∧
              M.val.q ≤ x.time.val * D p ∧
              (downSelected p i x.row x.time → logged = old ∧
                bufferArrivalAt p rate M logged (x.time.val + 1) = 0 ∧
                expectedDownFlatWord record.output.preparation.coordinator.downView i x.row x.time =
                  some (CoordinatorLocalArmChoice.storedDownFlatWord installed.registers.payload i)) ∧
              let decoded := currentDecodeStep p i x.row x.time own rate logged
              let cut := referenceDownCut p record.output.preparation.coordinator.downView
                i x.row x.time own rate logged
              let afterDecode := { logged with downBatch := decoded.1 }
              let accepted := { afterDecode with
                lastDown := some M
                S := service
                delta := service
                backlog := M.val.q - service
                status := .pending
                buffer := [] }
              ∃ next,
                (let nextMemory : LocalMemory p := if next.status = .unoccupied then memory else
                  ⟨some ⟨x.time, FollowerCutoffScan.completeRowProposalBit
                    p rate.eta.val x.row x.time⟩⟩
                 DeclaredFollowerLocalRound.consumeDownResult rate cut.outcome = .ok next ∧
                 releaseAfterService rate.eta i x.time (publicRowOfCompleteRow x.row x.time)
                   own old next = .ok next ∧
                 finishRound rate.eta x.time x.row next memory = .ok (next, nextMemory) ∧
                 DeclaredFollowerLocalRound.releaseAndFinish rate i x.row x.time own old memory next =
                   .ok (next, nextMemory) ∧
                 record.output.followers i =
                   ⟨.ordinary next nextMemory, none, some logged, some cut⟩ ∧
                 localStateDomainValid next ∧
                 next.S + next.backlog ≤ (x.time.val + 1) * D p ∧ next.delta ≤ D p ∧
                 next.initializationFailure = old.initializationFailure) ∧
                ((¬ downSelected p i x.row x.time ∧
                    cut.outcome = .skipped logged .notSelectedDown ∧ next = logged) ∨
                 (downSelected p i x.row x.time ∧ cut.raw = decoded.2 ∧
                    cut.filteredRaw = none ∧
                    cut.outcome = .decodeOrParseRejected logged afterDecode decoded.2 ∧
                    cut.rawComparison = some false ∧ next = afterDecode) ∨
                 (downSelected p i x.row x.time ∧ decoded.2 =
                    some (CoordinatorLocalArmChoice.storedDownFlatWord installed.registers.payload i) ∧
                    cut.raw = decoded.2 ∧ cut.filteredRaw = decoded.2 ∧
                    cut.rawComparison = some true ∧ cut.ordinaryParse = some M ∧
                    cut.ordinaryAcceptance ∧
                    cut.outcome = .accepted logged accepted decoded.2 M ⟨x.time.val + 2, []⟩
                      (service, M.val.q - service) service ∧
                    bufferArrivalAt p rate M logged (x.time.val + 1) = 0 ∧
                    recoveryQueueRecords p rate M logged (x.time.val + 2) = [(true, 0)] ∧
                    checkedRecovery p rate M logged (x.time.val + 2) =
                      .ok ⟨(service, M.val.q - service), service⟩ ∧
                    service + (M.val.q - service) = M.val.q ∧ next = accepted))
      | _ => True := by
  classical
  have seed := ReferenceFirstReplacementFollowerLoggingSeed.complete_first_replacement_follower_logging_seed
    rate source rewards C_star C_h
  have execution :=
    ReferenceFirstReplacementCollectionExecution.complete_first_replacement_collection_execution
      rate source rewards C_star C_h
  dsimp only at seed execution ⊢
  set R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
  set s := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
  set w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
  set Cwin := ReferenceCollectionPhaseHistory.collectionWindow R w
  set v := w + Cwin.length
  cases hget : R[v]? with
  | none => trivial
  | some record =>
    simp only [hget] at seed execution
    dsimp only
    cases hcut : record.output.preparation.coordinator with
    | first outcome => trivial
    | live registers owned base outcome => trivial
    | invalidCollectionCutoff => trivial
    | dagger => trivial
    | collection oldPayload ledger clock cutoff outcome =>
      rw [hcut] at seed execution
      cases outcome <;> dsimp only at seed execution ⊢
      rename_i core consistent started hs instruction hi output hl clockData installed selected
      obtain ⟨hwR, _, _, _⟩ := execution
      obtain ⟨_hinstalled, holdSigma, htime, _hrows, _hselected, _hrewards, _hnewTime,
        hfollowers⟩ := seed
      -- Collection includes its actual cutoff. Thus even an immediate next
      -- assignment is strictly after the OLD assignment's start.
      have hCpos : 0 < Cwin.length := by
        have hdrop := List.drop_eq_getElem_cons hwR
        dsimp only [Cwin, ReferenceCollectionPhaseHistory.collectionWindow]
        rw [hdrop]
        simp only [List.take_succ_cons, List.take_zero, List.length_append,
          List.length_cons, List.length_nil]
        omega
      have hvpos : 0 < v := by dsimp only [v]; omega
      have heffect := CoordinatorPhaseClock.startRound_assignment_effect
        p rate.eta.val record.input.time clock ledger.pending started instruction
        core.clock_parameter_valid core.clock_registers_valid core.clock_start_time_valid hs hi
      have ht : instruction.time = record.input.time := heffect.1
      have hpending : started.pending = Finset.univ := heffect.2.2.2.2.2.2.1
      -- The view is produced by the original successful dispatcher choice.
      -- Its payload is the NEW installation, not the OLD follower reply.
      have hview : ∃ actual : ReferenceActivePhysicalStep.Selection record.input,
          record.output.preparation.coordinator.downView = some actual.view ∧
          actual.view.payload = installed.registers.payload ∧
          actual.view.pendingAtChoice = Finset.univ := by
        let actual : ReferenceActivePhysicalStep.Selection record.input := {
          view := {
            payload := installed.registers.payload
            pendingAtChoice := started.pending
            cutoff := CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u
            complementWeights := installed.registers.complementWeights }
          started := started
          pending_eq := rfl
          cutoff_eq := rfl
          arm := selected.arm
          choice_eq := by
            simpa only [ht, ReferenceActivePhysicalStep.collectionInput]
              using selected.armChoice_eq }
        refine ⟨actual, ?_, rfl, hpending⟩
        simp only [hcut, ReferenceActivePhysicalStep.DispatchCut.downView,
          ReferenceActivePhysicalStep.DispatchCut.selection,
          ReferenceActivePhysicalStep.selectionAt, dite_eq_left ht, Option.map_some]
        rfl
      obtain ⟨actual, hview, hpayload, hfull⟩ := hview
      simp only [← hcut]
      refine ⟨by omega, ?_⟩
      intro i
      obtain ⟨old, memory, logged, hstate, hstatus, hdomainOld, _hbufferOld, _hdecoderOld,
        _hendpointOld, hmassOld, _hcalendarOld, _hkeysOld, _hquantOld, _hpairOld,
        hbefore, halt, _hstart, _hprepared, hconfiguration, _hrow, _hfollower, _htime,
        _hactivation, _harm, hlogging, _hlogBuffer, _hlogBufferValid, hdomain,
        hlogStatus, hlogLast, _hlogS, _hlogDelta, _hlogBacklog, _hlogBatch, hlogMarker,
        _hlogEndpoint, _hcalendar, _hkeys, _hquant, _hpair, _hlogBefore,
        hmass, _hrecordInput, _hactualInput, _hlogTests, _hnoLogTests, _htests,
        hsigma, hcredit, _hretainedCredit⟩ := hfollowers i
      have hstrict : acceptedStart logged <
          (installed.registers.payload.downRecord i).val.sigma := by
        unfold acceptedStart
        rw [hlogLast]
        rcases halt with ⟨hnone, _, _, _⟩ | hsome
        · rw [hnone]
          dsimp only
          omega
        · rw [hsome]
          change (oldPayload.downRecord i).val.sigma < _
          change oldPayload.sigma.val + 1 < _
          omega
      have hlogEq : downSelected p i record.input.row record.input.time → logged = old := by
        intro hselected
        exact logged_eq_old_on_down i record.input.row (record.input.state.activations i)
          record.input.time _ old logged hlogging hselected.1
      have hzero : downSelected p i record.input.row record.input.time →
          bufferArrivalAt p rate (installed.registers.payload.downRecord i) logged
            (record.input.time.val + 1) = 0 := by
        intro hselected
        rw [hlogEq hselected]
        exact buffer_arrival_zero_of_before _ old _ hbefore
      have hexpected : downSelected p i record.input.row record.input.time →
          expectedDownFlatWord record.output.preparation.coordinator.downView i
            record.input.row record.input.time =
              some (CoordinatorLocalArmChoice.storedDownFlatWord installed.registers.payload i) := by
        intro hselected
        rw [hview, ← hpayload]
        apply actual.expected_down_word i
        exact ⟨hselected.1, hselected.2, hfull ▸ Finset.mem_univ i⟩
      refine ⟨old, memory, logged, hstate, hstatus, hconfiguration, hlogging,
        operation_input_of_local_domain logged hdomain, hstrict, hsigma, hcredit,
        (fun h => ⟨hlogEq h, hzero h, hexpected h⟩), ?_⟩
      let own := record.output.preparation.feedback.observations
        (PublicDiscreteDraws.followerPlayer p.two_le_m i)
      have hcases := down_cut_at_birth record.output.preparation.coordinator.downView
        installed.registers.payload i record.input.row record.input.time own logged
        hdomain hlogStatus hsigma hstrict hcredit hexpected hzero
      dsimp only at hcases
      have hmassBound : logged.S + logged.backlog ≤ (record.input.time.val + 1) * D p := by
        apply hmass.trans
        apply Nat.mul_le_mul_right
        dsimp only [v] at htime
        omega
      rcases hcases with ⟨hnotsel, houtcome⟩ | ⟨hsel, hraw, hfiltered, houtcome, hcomparison⟩ |
        ⟨hsel, hraw, hcutraw, hfiltered, hcompared, hparsed, haccepted,
          houtcome, hzeroNow, hrecords, hrecovered⟩
      · refine ⟨logged, ?_, Or.inl ⟨hnotsel, houtcome, rfl⟩⟩
        apply finish_actual record i old logged logged memory hconfiguration hstatus hlogging
          (by rw [houtcome]; rfl) hdomain hmassBound hlogMarker
        intro hoccupied
        exact False.elim (hoccupied hlogStatus)
      · let afterDecode := { logged with downBatch :=
          (currentDecodeStep p i record.input.row record.input.time
            (record.output.preparation.feedback.observations
              (PublicDiscreteDraws.followerPlayer p.two_le_m i)) rate logged).1 }
        have hbatch := (ReferenceFollowerDecoderChronology.currentDecodeStep_batch_spec
          i record.input.row record.input.time own logged hdomain.2.2).1
        have hnextDomain : localStateDomainValid afterDecode :=
          ⟨hdomain.1, hdomain.2.1, hbatch⟩
        refine ⟨afterDecode, ?_, Or.inr (Or.inl
          ⟨hsel, hraw, hfiltered, houtcome, hcomparison, rfl⟩)⟩
        apply finish_actual record i old logged afterDecode memory hconfiguration hstatus hlogging
          (by rw [houtcome]; rfl) hnextDomain hmassBound hlogMarker
        intro hoccupied
        exact False.elim (hoccupied hlogStatus)
      · let M := installed.registers.payload.downRecord i
        let service := min (4 * rate.n) M.val.q
        let next := { logged with
          lastDown := some M
          S := service
          delta := service
          backlog := M.val.q - service
          status := .pending
          downBatch := (currentDecodeStep p i record.input.row record.input.time
            (record.output.preparation.feedback.observations
              (PublicDiscreteDraws.followerPlayer p.two_le_m i)) rate logged).1
          buffer := [] }
        have hmin : service ≤ M.val.q := Nat.min_le_right _ _
        have hconserve : service + (M.val.q - service) = M.val.q := Nat.add_sub_of_le hmin
        have hq : M.val.q ≤ p.T * D p := hcredit.trans
          (Nat.mul_le_mul_right (D p) (Nat.le_of_lt record.input.time.isLt))
        have hservice : service ≤ D p := (Nat.min_le_left _ _).trans (four_n_le_D p rate)
        have hbatch := (ReferenceFollowerDecoderChronology.currentDecodeStep_batch_spec
          i record.input.row record.input.time own logged hdomain.2.2).1
        have hnextDomain : localStateDomainValid next := by
          refine ⟨⟨hmin.trans hq, hservice, (Nat.sub_le _ _).trans hq⟩, ?_, hbatch⟩
          refine ⟨?_, List.nodup_nil, ?_⟩
          · intro saved hsaved
            cases hsaved
          · intro saved hsaved
            cases hsaved
        have hnextMass : next.S + next.backlog ≤ (record.input.time.val + 1) * D p := by
          change service + (M.val.q - service) ≤ _
          rw [hconserve]
          exact hcredit.trans (Nat.mul_le_mul_right (D p) (by omega))
        refine ⟨next, ?_, Or.inr (Or.inr ⟨hsel, hraw, hcutraw, hfiltered, hcompared,
          hparsed, haccepted, houtcome, hzeroNow, hrecords, hrecovered, hconserve, rfl⟩)⟩
        apply finish_actual record i old logged next memory hconfiguration hstatus hlogging
          (by rw [houtcome]; rfl) hnextDomain hnextMass hlogMarker
        intro _
        exact ⟨M, rfl, Nat.le_of_eq hsigma⟩

end Bandits.Support.ReferenceFirstReplacementDownRecovery
end
