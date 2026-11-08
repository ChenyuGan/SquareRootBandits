/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstReplacementNextFollowerStep

/-!
# First replacement: the next unoccupied follower's sparse replay

Sources: `sources/zip4/manuscript/06_interruptions.tex:9-100,193-233,246-295`,
`05_binary_transport.tex:354-431`, and `appendix_a_local_protocol.tex:28-79`.
Recovery retains the chronological old buffer and starts from the actual
installed queue, which may be nonzero. These are internal physical-prefix
results; no coordinator survival or manuscript closure is asserted.
-/

@[expose] public section
noncomputable section

namespace Bandits.Support.ReferenceFirstReplacementNextDownReplay

open ConstructorDimensions ReferenceActivePhysicalStep ReferenceActivePhysicalHorizon
open ReferencePrelaunchFollower ActiveFollowerLifecycle ActiveFollowerDownAcceptance
open ReferenceDownReception SparseCalendarReplay PublicDiscreteDraws
open ReferenceFirstReplacementNextFollowerStep

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

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

private theorem sparseBufferContribution_zero_of_no_key
    (d : ℕ) (D : ℝ) (eta : ℝ) (h : ℕ) (arm : Fin p.K) (r : ℕ)
    (buffer : List (SparseCalendarRecord p.K))
    (hno : ∀ saved ∈ buffer, ¬ (saved.calendarRound = r ∧ saved.pilot = arm)) :
    sparseBufferContribution d D eta h arm r buffer = 0 := by
  classical
  induction buffer with
  | nil => rfl
  | cons saved rest ih =>
      have hhead : ¬ (saved.calendarRound = r ∧ saved.pilot = arm) :=
        hno saved List.mem_cons_self
      have htail : ∀ item ∈ rest,
          ¬ (item.calendarRound = r ∧ item.pilot = arm) := by
        intro item hi
        exact hno item (List.mem_cons_of_mem _ hi)
      change (if saved.calendarRound = r ∧ saved.pilot = arm then
          savedContribution p.K d D eta h saved.observation saved.thinScalar else 0) +
        sparseBufferContribution d D eta h arm r rest = 0
      rw [ite_eq_right hhead, zero_add]
      exact ih htail

private theorem sparseBufferContribution_le_of_unique_key
    (d D : ℕ) (eta : ℝ) (h : ℕ) (arm : Fin p.K) (r : ℕ)
    (buffer : List (SparseCalendarRecord p.K))
    (hkeys : (buffer.map fun saved => (saved.calendarRound, saved.pilot)).Nodup)
    (hcontribution : ∀ saved ∈ buffer,
      saved.calendarRound = r → saved.pilot = arm →
        savedContribution p.K d (D : ℝ) eta h saved.observation saved.thinScalar ≤ D) :
    sparseBufferContribution d (D : ℝ) eta h arm r buffer ≤ D := by
  classical
  induction buffer with
  | nil => simp [sparseBufferContribution]
  | cons saved rest ih =>
      simp only [List.map_cons, List.nodup_cons] at hkeys
      have htail : ∀ item ∈ rest,
          item.calendarRound = r → item.pilot = arm →
            savedContribution p.K d (D : ℝ) eta h item.observation item.thinScalar ≤ D := by
        intro item hitem hround hpilot
        exact hcontribution item (List.mem_cons_of_mem _ hitem) hround hpilot
      by_cases hkey : saved.calendarRound = r ∧ saved.pilot = arm
      · have hnotTail : ∀ item ∈ rest,
            ¬ (item.calendarRound = r ∧ item.pilot = arm) := by
          intro item hitem hitemKey
          apply hkeys.1
          apply List.mem_map.mpr
          exact ⟨item, hitem,
            Prod.ext (hitemKey.1.trans hkey.1.symm) (hitemKey.2.trans hkey.2.symm)⟩
        have hone := sparseBufferContribution_zero_of_no_key d (D : ℝ) eta h arm r rest hnotTail
        change (if saved.calendarRound = r ∧ saved.pilot = arm then
            savedContribution p.K d (D : ℝ) eta h saved.observation saved.thinScalar else 0) +
          sparseBufferContribution d (D : ℝ) eta h arm r rest ≤ D
        rw [ite_eq_left hkey, hone]
        exact hcontribution saved List.mem_cons_self hkey.1 hkey.2
      · change (if saved.calendarRound = r ∧ saved.pilot = arm then
            savedContribution p.K d (D : ℝ) eta h saved.observation saved.thinScalar else 0) +
          sparseBufferContribution d (D : ℝ) eta h arm r rest ≤ D
        rw [ite_eq_right hkey, zero_add]
        exact ih hkeys.2 htail

private theorem bufferArrival_le_D
    (M : OrdinaryMessageCodec.DownRecord (codecParams p rate.eta))
    (logged : ReferencePrelaunchFollower.State p rate.eta)
    (hvalid : ActiveFollowerLifecycle.localBufferValid logged)
    (r : ℕ) :
    ActiveFollowerDownAcceptance.bufferArrivalAt p rate M logged r ≤ D p := by
  change SparseCalendarReplay.sparseBufferContribution (p.m - 1) (D p : ℝ)
    rate.eta.val M.val.h (PrelaunchBufferRecovery.downArm rate.eta M) r logged.buffer ≤ D p
  apply sparseBufferContribution_le_of_unique_key
    (d := p.m - 1) (D := D p) (eta := rate.eta.val) (h := M.val.h)
    (arm := PrelaunchBufferRecovery.downArm rate.eta M) (r := r)
    (buffer := logged.buffer)
    (ActiveFollowerLifecycle.localBufferValid_keys_nodup hvalid)
  intro saved hsaved hround harm
  by_cases hthin : saved.thinScalar.1 ≤
      (4 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ) * (((2 : ℝ) ^ M.val.h)⁻¹)) /
        SparseCalendarReplay.sparseMaskProbability p.K (p.m - 1)
  · rw [SparseCalendarReplay.savedContribution_eq_floor_of_le
      p.K (p.m - 1) (D p : ℝ) rate.eta.val M.val.h saved.observation
      saved.thinScalar hthin]
    obtain ⟨own, hown⟩ := ActiveFollowerLifecycle.localBufferValid_observation_typed
      hvalid saved hsaved
    have hfloor := ActiveFollowerQueueOperation.sourceArrivalFloor_le_D rate.eta M own
    have hsame := ActiveFollowerQueueOperation.sourceArrivalFloor_eq_savedFloor rate.eta M own
    rw [hown] at hsame
    rw [hsame] at hfloor
    exact hfloor
  · simp [SparseCalendarReplay.savedContribution, hthin]

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



/-- Two enabled updates from the original queue. The arrival cap comes from
unique timestamp/arm keys and the actual grid-valued observations. The empty
prefix is checked before either service operation. -/
private theorem checked_recovery_two_rounds
    (M : OrdinaryMessageCodec.DownRecord (codecParams p rate.eta))
    (state : ReferencePrelaunchFollower.State p rate.eta) (t : Fin p.T)
    (hsigma : M.val.sigma = t.val)
    (hcredit : M.val.q ≤ (t.val - 1) * D p)
    (hvalid : localBufferValid state)
    (hzero : bufferArrivalAt p rate M state (t.val + 1) = 0) :
    let a := bufferArrivalAt p rate M state t.val
    let g0 := min (4 * rate.n) (M.val.q + a)
    let b0 := M.val.q + a - g0
    let g1 := min (4 * rate.n) b0
    recoveryRounds p rate M (t.val + 2) = [t.val, t.val + 1] ∧
    recoveryQueueRecords p rate M state (t.val + 2) = [(true, a), (true, 0)] ∧
    checkedRecovery p rate M state (t.val + 2) =
      .ok ⟨(g0 + g1, b0 - g1), g1⟩ ∧
    g0 + g1 + (b0 - g1) = M.val.q + a ∧
    M.val.q + a ≤ t.val * D p ∧
    replay_register_domain (D p) (p.T * D p) ⟨(0, M.val.q), 0⟩ ∧
    replay_register_domain (D p) (p.T * D p) ⟨(g0, b0), g0⟩ ∧
    replay_register_domain (D p) (p.T * D p) ⟨(g0 + g1, b0 - g1), g1⟩ := by
  dsimp only
  let a := bufferArrivalAt p rate M state t.val
  let g0 := min (4 * rate.n) (M.val.q + a)
  let b0 := M.val.q + a - g0
  let g1 := min (4 * rate.n) b0
  have hpos : 1 ≤ t.val := by
    have h := PrelaunchBufferRecovery.down_sigma_pos rate.eta M
    omega
  have ha : a ≤ D p := bufferArrival_le_D M state hvalid t.val
  have hmul : (t.val - 1) * D p + D p = t.val * D p := by
    calc
      (t.val - 1) * D p + D p = (t.val - 1 + 1) * D p := by
        rw [Nat.add_mul, one_mul]
      _ = t.val * D p := by rw [Nat.sub_add_cancel hpos]
  have hcredit' : M.val.q + a ≤ t.val * D p := by omega
  have hbound : M.val.q + a ≤ p.T * D p :=
    hcredit'.trans (Nat.mul_le_mul_right (D p) (Nat.le_of_lt t.isLt))
  have hg0 : g0 ≤ M.val.q + a := Nat.min_le_right _ _
  have hg1 : g1 ≤ b0 := Nat.min_le_right _ _
  have hserv0 : g0 ≤ D p := (Nat.min_le_left _ _).trans (four_n_le_D p rate)
  have hserv1 : g1 ≤ D p := (Nat.min_le_left _ _).trans (four_n_le_D p rate)
  have hmass0 : g0 + b0 = M.val.q + a := Nat.add_sub_of_le hg0
  have hmass1 : g0 + g1 + (b0 - g1) = M.val.q + a := by omega
  have hi : replay_register_domain (D p) (p.T * D p) ⟨(0, M.val.q), 0⟩ :=
    ⟨Nat.zero_le _, Nat.zero_le _, (Nat.le_add_right _ _).trans hbound⟩
  have hm : replay_register_domain (D p) (p.T * D p) ⟨(g0, b0), g0⟩ :=
    ⟨hg0.trans hbound, hserv0, (Nat.sub_le _ _).trans hbound⟩
  have hf : replay_register_domain (D p) (p.T * D p)
      ⟨(g0 + g1, b0 - g1), g1⟩ :=
    ⟨by change g0 + g1 ≤ p.T * D p; omega, hserv1,
      by change b0 - g1 ≤ p.T * D p; omega⟩
  have hr : recoveryRounds p rate M (t.val + 2) = [t.val, t.val + 1] := by
    simp [recoveryRounds, sparseCalendarRounds, hsigma, List.range_succ]
  have hrecords : recoveryQueueRecords p rate M state (t.val + 2) =
      [(true, a), (true, 0)] := by
    simp only [recoveryQueueRecords, recoveryArrivals, hr, List.map_cons,
      List.map_nil, hzero]
    rfl
  have hu0 : checkedReplayUpdate (D p) (p.T * D p) (4 * rate.n)
      ⟨(0, M.val.q), 0⟩ (true, a) = .ok ⟨(g0, b0), g0⟩ := by
    simp only [checkedReplayUpdate, replayService, QueueReplay.transition,
      ite_true, Nat.zero_add]
    rw [ite_eq_left ha, ite_eq_left hserv0, ite_eq_left hm.1, ite_eq_left hm.2.2]
  have hu1 : checkedReplayUpdate (D p) (p.T * D p) (4 * rate.n)
      ⟨(g0, b0), g0⟩ (true, 0) = .ok ⟨(g0 + g1, b0 - g1), g1⟩ := by
    simp only [checkedReplayUpdate, replayService, QueueReplay.transition,
      ite_true, Nat.add_zero]
    rw [ite_eq_left (Nat.zero_le _), ite_eq_left hserv1,
      ite_eq_left hf.1, ite_eq_left hf.2.2]
  refine ⟨hr, hrecords, ?_, hmass1, hcredit', hi, hm, hf⟩
  rw [checkedRecovery_eq_checkedReplay, hrecords]
  simp only [checkedReplay, ite_eq_left hi, hu0, ite_eq_left hm, hu1, ite_eq_left hf]
  rfl

/-- The actual scan at the next calendar round visits just the birth proposal
coordinate. Both grid and proposal facts are local inputs here; the root
obtains them from the original coordinator clock and actual continuation. -/
private theorem accepted_scan_next
    (M : OrdinaryMessageCodec.DownRecord (codecParams p rate.eta))
    (t : Fin p.T) (row : CompletePublicTable.CompleteRow p)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (hsigma : M.val.sigma = t.val)
    (hgrid : t.val + 2 ≤ FollowerCutoffScan.gridBoundary p rate.eta.val (downStart p rate M))
    (hbit : FollowerCutoffScan.completeRowProposalBit p rate.eta.val row
      (downStart p rate M) = false)
    (ha : OrdinaryMessageCodec.acceptDown (codecParams p rate.eta)
      (acceptedStart state) (t.val + 1) M) :
    acceptedCutoffScan p rate M t (acceptedDownStartLE p rate M t state ha) row =
      ⟨t.val + 2, [downStart p rate M]⟩ := by
  classical
  have hstart := downStart_val_add_one p rate M
  have hcoords : FollowerCutoffScan.pastProposalCoordinates p (downStart p rate M) t =
      {downStart p rate M} := by
    ext j
    simp only [FollowerCutoffScan.pastProposalCoordinates,
      FollowerCutoffScan.proposalCoordinates, Finset.mem_filter,
      Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro h
      apply Fin.ext
      omega
    · intro h
      subst j
      omega
  simp only [acceptedCutoffScan, FollowerCutoffScan.completeRowCutoffScan,
    FollowerCutoffScan.followerCutoffScan, hcoords, Finset.sort_singleton,
    Nat.min_eq_left hgrid, FollowerCutoffScan.chronologicalScanLoop,
    ite_eq_left (show (downStart p rate M).val + 1 <
      FollowerCutoffScan.gridBoundary p rate.eta.val (downStart p rate M) by omega),
    hbit, Bool.false_eq_true, ite_false]

private theorem dispatch_live_origin (x : RoundInput p rate) :
    match dispatch x with
    | .live r q base _ => x.state.coordinator = .live r q base
    | _ => True := by
  unfold dispatch
  cases hs : x.state.coordinator with
  | first => trivial
  | live r q base =>
    simp only [CoordinatorRoundDispatch.dispatch]
    cases CoordinatorRoundDispatch.dispatchLive (liveInput x r q base)
      <;> rfl
  | collection payload ledger saved =>
    by_cases hc : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
    · simp only [dite_eq_left hc, CoordinatorRoundDispatch.dispatch]
      cases CoordinatorRoundDispatch.dispatchCollection
        (collectionInput x payload ledger (collectionClock payload ledger saved
          ⟨ledger.cutoff - 1, by omega⟩) ⟨ledger.cutoff - 1, by omega⟩) <;> trivial
    · simp only [dite_eq_right hc]
  | dagger => trivial

private theorem clock_detectCutoff_of_interruption
    (clock : CoordinatorPhaseClock.ClockRegisters p) (time sigma stamp : Fin p.T) (bit : Bool)
    (hsigma : clock.sigma = some sigma) (hu : clock.u = none)
    (htoken : clock.lastProposal = some (stamp, bit))
    (hstamp : stamp.val + 1 = time.val)
    (hinterrupted : time.val + 1 = clock.g ∨ bit = true) :
    CoordinatorPhaseClock.detectCutoff clock time =
      .ok (.cutoff sigma hsigma) := by
  rcases clock with ⟨s, u, g, token⟩
  dsimp only at hsigma hu htoken hinterrupted
  subst s
  subst u
  subst token
  rcases hinterrupted with hgrid | hbit
  · simp [CoordinatorPhaseClock.detectCutoff, FollowerCutoffScan.calendarRound, hgrid]
  · simp [CoordinatorPhaseClock.detectCutoff, CoordinatorPhaseClock.savedPriorProposal,
      hstamp, hbit]
    intro _
    rfl


/-- An actual continuing dispatcher with the produced clock cannot have read
a true prior proposal or reached the grid. This supplies the one-coordinate
scan rather than assuming a successful recovery trace. -/
private theorem continuing_scan_facts
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hclock : ReferenceCoordinatorClockDomains.clockAt record.input.rows
      record.input.selected record.input.time.val record.input.state) :
    match record.output.preparation.coordinator with
    | .live r _ _ (.continuingChosen ..) =>
      r.payload.sigma.val + 1 = record.input.time.val →
        record.input.time.val + 2 ≤ FollowerCutoffScan.gridBoundary p rate.eta.val r.payload.sigma ∧
        FollowerCutoffScan.completeRowProposalBit p rate.eta.val record.input.row r.payload.sigma = false
    | _ => True := by
  classical
  cases hcut : record.output.preparation.coordinator with
  | first _ => trivial
  | collection _ _ _ _ _ => trivial
  | dagger => trivial
  | invalidCollectionCutoff => trivial
  | live r q base outcome =>
    cases outcome <;> try trivial
    rename_i dispatched hstart continuation arm
    intro hs
    have horigin := dispatch_live_origin record.input
    have hdispatch : dispatch record.input = record.output.preparation.coordinator := by
      rw [record.output_eq]; rfl
    rw [hdispatch, hcut] at horigin
    simp only [ReferenceCoordinatorClockDomains.clockAt, horigin] at hclock
    obtain ⟨hstamp, hvalid, hsigma, hu, hg, hstarted, hbefore, htoken⟩ := hclock
    have hrow : record.input.rows record.input.selected = record.input.row := rfl
    rw [hrow] at htoken
    have htime : CoordinatorPhaseClock.startRoundTimeValid p record.input.time r.priorClock := by
      simp only [CoordinatorPhaseClock.startRoundTimeValid, hsigma, hu,
        FollowerCutoffScan.calendarRound]
      exact ⟨hstarted, by omega⟩
    have hframes := ReferenceCoordinatorRecorderCallCorrespondence.actual_call_frames record
    rw [hcut] at hframes
    have hno : ¬ (record.input.time.val + 1 = r.priorClock.g ∨
        FollowerCutoffScan.completeRowProposalBit p rate.eta.val record.input.row r.time = true) := by
      intro h
      have hd := clock_detectCutoff_of_interruption r.priorClock record.input.time r.payload.sigma
        r.time (FollowerCutoffScan.completeRowProposalBit p rate.eta.val record.input.row r.time)
        hsigma hu htoken hstamp h
      obtain ⟨cut, he, hc, _⟩ := CoordinatorPhaseClock.startRound_cutoff_effect
        p rate.eta.val record.input.time r.payload.sigma r.priorClock
        (liveRegistersAt r record.input.time).clockPending
        (ReferenceCoordinatorClockDomains.proposalParameterValid_of_rate rate)
        hvalid htime hsigma hd
      have heq : cut = dispatched.startResult := Except.ok.inj (he.symm.trans hstart)
      have hlt := hframes.1.2
      rw [← heq, hc] at hlt
      change record.input.time.val + 1 < record.input.time.val + 1 at hlt
      omega
    have hgrid : r.priorClock.g = FollowerCutoffScan.gridBoundary p rate.eta.val r.payload.sigma := by
      simpa only [CoordinatorPhaseClock.boundaryFromSigma, hsigma] using hvalid.1
    have hsame : r.time = r.payload.sigma := Fin.ext (by omega)
    constructor
    · rw [← hgrid]
      have hn := fun h => hno (Or.inl h)
      omega
    · have hn := fun h => hno (Or.inr h)
      rw [hsame] at hn
      cases hb : FollowerCutoffScan.completeRowProposalBit p rate.eta.val
          record.input.row r.payload.sigma with
      | false => rfl
      | true => exact (hn hb).elim


/-- Exhaust the literal receiver. Expected absence and mismatch are separate
rejections; a matching present current word is parsed and all recovery guards
are constructed before installation. None of these outcomes is supplied. -/
private theorem down_cut_next
    (view : Option (ChoiceTimeView p rate.eta)) (payload : Payload rate)
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (t : Fin p.T) (own : Observation p)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (hdomain : localStateDomainValid state) (hstatus : state.status = .unoccupied)
    (hsigma : (payload.downRecord i).val.sigma = t.val)
    (hstrict : acceptedStart state < (payload.downRecord i).val.sigma)
    (hcredit : (payload.downRecord i).val.q ≤ (t.val - 1) * D p)
    (hmass : state.S + state.backlog ≤ t.val * D p)
    (hexpected : expectedDownFlatWord view i row t = none ∨
      expectedDownFlatWord view i row t = some (CoordinatorLocalArmChoice.storedDownFlatWord payload i))
    (hgrid : t.val + 2 ≤ FollowerCutoffScan.gridBoundary p rate.eta.val
      (downStart p rate (payload.downRecord i)))
    (hbit : FollowerCutoffScan.completeRowProposalBit p rate.eta.val row
      (downStart p rate (payload.downRecord i)) = false)
    (hzero : downSelected p i row t → bufferArrivalAt p rate (payload.downRecord i) state (t.val + 1) = 0) :
    let M := payload.downRecord i
    let decoded := currentDecodeStep p i row t own rate state
    let cut := referenceDownCut p view i row t own rate state
    let afterDecode := { state with downBatch := decoded.1 }
    let a := bufferArrivalAt p rate M state t.val
    let g0 := min (4 * rate.n) (M.val.q + a)
    let b0 := M.val.q + a - g0
    let g1 := min (4 * rate.n) b0
    let accepted := { afterDecode with
      lastDown := some M
      S := g0 + g1
      delta := g1
      backlog := b0 - g1
      status := .pending
      buffer := [] }
    ∃ next,
      DeclaredFollowerLocalRound.consumeDownResult rate cut.outcome = .ok next ∧
      localStateDomainValid next ∧ next.S + next.backlog ≤ (t.val + 1) * D p ∧
      next.initializationFailure = state.initializationFailure ∧
      (next.status ≠ .unoccupied → next.lastDown = some M) ∧
      ((¬ downSelected p i row t ∧ cut.outcome = .skipped state .notSelectedDown ∧ next = state) ∨
       (downSelected p i row t ∧ cut.raw = decoded.2 ∧ cut.filteredRaw = none ∧
        cut.outcome = .decodeOrParseRejected state afterDecode decoded.2 ∧
        cut.ordinaryParse = ordinaryParse p rate decoded.2 ∧
        (cut.ordinaryAcceptance ↔ ordinaryLocalAcceptanceTest p rate t state (ordinaryParse p rate decoded.2)) ∧
        (cut.rawComparison = some false ∨
          cut.rawComparison = some true ∧ decoded.2 = none) ∧ next = afterDecode) ∨
       (downSelected p i row t ∧ decoded.2 = some (CoordinatorLocalArmChoice.storedDownFlatWord payload i) ∧
        cut.raw = decoded.2 ∧ cut.filteredRaw = decoded.2 ∧ cut.rawComparison = some true ∧
        cut.ordinaryParse = some M ∧ cut.ordinaryAcceptance ∧
        cut.outcome = .accepted state accepted decoded.2 M
          ⟨t.val + 2, [downStart p rate M]⟩ (g0 + g1, b0 - g1) g1 ∧
        recoveryRounds p rate M (t.val + 2) = [t.val, t.val + 1] ∧
        recoveryQueueRecords p rate M state (t.val + 2) = [(true, a), (true, 0)] ∧
        checkedRecovery p rate M state (t.val + 2) = .ok ⟨(g0 + g1, b0 - g1), g1⟩ ∧
        g0 + g1 + (b0 - g1) = M.val.q + a ∧
        M.val.q + a ≤ t.val * D p ∧
        (∀ k, ∃ middle, checkedReplay (D p) (p.T * D p) (4 * rate.n) 0
          ⟨(0, M.val.q), 0⟩ ((recoveryQueueRecords p rate M state (t.val + 2)).take k) = .ok middle ∧
          replay_register_domain (D p) (p.T * D p) middle ∧
          middle.registers = QueueReplay.replay (4 * rate.n) (0, M.val.q)
            ((recoveryQueueRecords p rate M state (t.val + 2)).take k)) ∧ next = accepted)) := by
  classical
  dsimp only
  let M := payload.downRecord i
  let decoded := currentDecodeStep p i row t own rate state
  let afterDecode := { state with downBatch := decoded.1 }
  have hop := operation_input_of_local_domain state hdomain
  have hbatch := (ReferenceFollowerDecoderChronology.currentDecodeStep_batch_spec
    i row t own state hdomain.2.2).1
  have hd : localStateDomainValid afterDecode := ⟨hdomain.1, hdomain.2.1, hbatch⟩
  have hmass' : state.S + state.backlog ≤ (t.val + 1) * D p :=
    hmass.trans (Nat.mul_le_mul_right (D p) (by omega))
  by_cases hselected : downSelected p i row t
  · by_cases hmatches : decoded.2 = expectedDownFlatWord view i row t
    · dsimp only [decoded] at hmatches
      rcases hexpected with he | he
      · have hraw : (currentDecodeStep p i row t own rate state).2 = none := hmatches.trans he
        have ho : (referenceDownCut p view i row t own rate state).outcome =
            .decodeOrParseRejected state afterDecode decoded.2 := by
          simp [referenceDownCut, hselected, hstatus, hop.1, hop.2.1, hop.2.2,
            hmatches, he, ordinaryParse, OrdinaryMessageCodec.parseDown, decoded, afterDecode]
          rfl
        refine ⟨afterDecode, ?_, hd, hmass', rfl, ?_, Or.inr (Or.inl ?_)⟩
        · rw [ho]; rfl
        · intro hb
          exact (hb hstatus).elim
        · refine ⟨hselected, ?_⟩
          simp [referenceDownCut, hselected, hstatus, hop.1, hop.2.1, hop.2.2,
            hmatches, he, ordinaryParse, OrdinaryMessageCodec.parseDown, decoded, afterDecode]
          rfl
      · have hraw : (currentDecodeStep p i row t own rate state).2 = some (CoordinatorLocalArmChoice.storedDownFlatWord payload i) :=
          hmatches.trans he
        have hp : ordinaryParse p rate (currentDecodeStep p i row t own rate state).2 = some M := by
          rw [hraw]
          unfold ordinaryParse CoordinatorLocalArmChoice.storedDownFlatWord
          change OrdinaryMessageCodec.parseDown (codecParams p rate.eta)
            (some ((OrdinaryMessageCodec.wordEquivFlat _).symm
              ((OrdinaryMessageCodec.wordEquivFlat _) (payload.downWord i)))) = _
          rw [(OrdinaryMessageCodec.wordEquivFlat _).symm_apply_apply]
          exact payload.parseDown_downWord i
        have ha : OrdinaryMessageCodec.acceptDown (codecParams p rate.eta)
            (acceptedStart state) (t.val + 1) M :=
          ⟨hstrict, (Nat.le_of_eq hsigma).trans (Nat.le_add_right _ _)⟩
        have hscan := accepted_scan_next M t row state hsigma hgrid hbit ha
        have hr := checked_recovery_two_rounds M state t hsigma hcredit hdomain.2.1 (hzero hselected)
        dsimp only at hr
        let a := bufferArrivalAt p rate M state t.val
        let g0 := min (4 * rate.n) (M.val.q + a)
        let b0 := M.val.q + a - g0
        let g1 := min (4 * rate.n) b0
        let accepted := { afterDecode with
          lastDown := some M
          S := g0 + g1
          delta := g1
          backlog := b0 - g1
          status := .pending
          buffer := [] }
        have hdAccepted : localStateDomainValid accepted := by
          refine ⟨hr.2.2.2.2.2.2.2, ?_, hbatch⟩
          refine ⟨?_, List.nodup_nil, ?_⟩ <;> intro saved hsaved <;> cases hsaved
        have ho : (referenceDownCut p view i row t own rate state).outcome =
            .accepted state accepted decoded.2 M ⟨t.val + 2, [downStart p rate M]⟩
              (g0 + g1, b0 - g1) g1 := by
          simp only [referenceDownCut, dite_eq_left hselected, dite_eq_left hstatus,
            dite_eq_left hop.1, dite_eq_left hop.2.1, dite_eq_left hop.2.2,
            dite_eq_left hmatches, hp, dite_eq_left ha, hscan, hr.2.2.1,
            ite_true]
          rfl
        refine ⟨accepted, ?_, hdAccepted, ?_, rfl, (fun _ => rfl), Or.inr (Or.inr ?_)⟩
        · rw [ho]; rfl
        · change g0 + g1 + (b0 - g1) ≤ (t.val + 1) * D p
          rw [hr.2.2.2.1]
          exact hr.2.2.2.2.1.trans (Nat.mul_le_mul_right (D p) (by omega))
        · refine ⟨hselected, hraw, ?_⟩
          have hprefix : ∀ k, ∃ middle, checkedReplay (D p) (p.T * D p) (4 * rate.n) 0
              ⟨(0, M.val.q), 0⟩ ((recoveryQueueRecords p rate M state (t.val + 2)).take k) = .ok middle ∧
              replay_register_domain (D p) (p.T * D p) middle ∧
              middle.registers = QueueReplay.replay (4 * rate.n) (0, M.val.q)
                ((recoveryQueueRecords p rate M state (t.val + 2)).take k) :=
            fun k => checkedRecovery_success_prefix p rate M state (t.val + 2) _ hr.2.2.1 k
          simp only [referenceDownCut, dite_eq_left hselected, dite_eq_left hstatus,
            dite_eq_left hop.1, dite_eq_left hop.2.1, dite_eq_left hop.2.2,
            dite_eq_left hmatches, hp, ordinaryLocalAcceptanceTest, ha, hscan, hr.2.2.1,
            ite_true, dite_true, true_and]
          exact ⟨rfl, rfl, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hprefix, rfl⟩
    · dsimp only [decoded] at hmatches
      have ho : (referenceDownCut p view i row t own rate state).outcome =
          .decodeOrParseRejected state afterDecode decoded.2 := by
        simp only [referenceDownCut, dite_eq_left hselected, dite_eq_left hstatus,
          dite_eq_left hop.1, dite_eq_left hop.2.1, dite_eq_left hop.2.2,
          dite_eq_right hmatches]
        rfl
      refine ⟨afterDecode, ?_, hd, hmass', rfl, ?_, Or.inr (Or.inl ?_)⟩
      · rw [ho]; rfl
      · intro hb
        exact (hb hstatus).elim
      · refine ⟨hselected, ?_⟩
        simp only [referenceDownCut, dite_eq_left hselected, dite_eq_left hstatus,
          dite_eq_left hop.1, dite_eq_left hop.2.1, dite_eq_left hop.2.2,
          dite_eq_right hmatches, true_and]
        exact ⟨Or.inl trivial, rfl⟩
  · have ho : (referenceDownCut p view i row t own rate state).outcome =
        .skipped state .notSelectedDown := by
      simp only [referenceDownCut, dite_eq_right hselected]
    refine ⟨state, ?_, hdomain, hmass', rfl, ?_, Or.inl ⟨hselected, ho, rfl⟩⟩
    · rw [ho]; rfl
    · intro hb
      exact (hb hstatus).elim

/-- The actual first replacement's next continuing live round, on its
unoccupied follower branch. All data come from the original complete suffix.
The next consumer is finite later-replacement follower-prefix preservation,
composed with the imported occupied-step producer. No branch occurrence,
coordinator tail survival, full interval, or later episode splice is asserted. -/
theorem complete_first_replacement_next_unoccupied_recovery
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
    let s := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
    let v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
    match R[v]? with
    | none => True
    | some r0 => match r0.output.preparation.coordinator with
      | .collection oldPayload _ _ _ (.laterChosen _ _ _ _ _ _ _ _ _ installed _) =>
        match R[v + 1]? with
        | none => True
        | some r1 => match r1.output.preparation.coordinator with
          | .live _ _ _ (.continuingChosen ..) =>
            r1.input.state = r0.output.next ∧ r1.input.time.val = r0.input.time.val + 1 ∧
            r1.input.time.val + 2 = r0.input.time.val + 3 ∧
            ∃ selected : Selection r1.input,
              r1.output.preparation.coordinator.selection = some selected ∧
              selected.view.payload = installed.registers.payload ∧
              s < selected.view.payload.sigma.val ∧
              CoordinatorLocalArmChoice.assignmentIsLive selected.view.payload selected.view.cutoff r1.input.time ∧
            ∃ cell0 : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell r0,
              cell0.selected.view.payload = installed.registers.payload ∧
              ReferenceLaterLiveNumericalReadout.laterLiveReadout s r0 = some cell0.input ∧
              cell0.input.enabled = true ∧
            ∃ cell1 : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell r1,
              cell1.selected.view.payload = installed.registers.payload ∧
              ReferenceLaterLiveNumericalReadout.laterLiveReadout s r1 = some cell1.input ∧
            ∀ i : Fin (p.m - 1), ∃ state memory,
              r1.input.state.followers i = .ordinary state memory ∧
              (r1.output.preparation.followers.followers i).configuration = .ordinary state memory ∧
              localStateDomainValid state ∧ state.S + state.backlog ≤ r1.input.time.val * D p ∧
              interruptionDecision rate.eta r1.input.time state memory = .ok false ∧
              (state.status = .unoccupied →
                ∃ old birthMemory birthLogged logged,
                  r0.input.state.followers i = .ordinary old birthMemory ∧
                  (r0.output.preparation.followers.followers i).configuration = .ordinary old birthMemory ∧
                  old.status = .unoccupied ∧
                  ((old.lastDown = none ∧ old.S = 0 ∧ old.delta = 0 ∧ old.backlog = 0) ∨
                    old.lastDown = some (oldPayload.downRecord i)) ∧
                  (∀ saved ∈ old.buffer, saved.calendarRound < r0.input.time.val + 1) ∧
                  ActiveFollowerLogging.checkedLogging i r0.input.row (r0.input.state.activations i)
                    r0.input.time ((r0.output.preparation.followers.followers i).arm,
                      r0.output.preparation.feedback.observations (followerPlayer p.two_le_m i)) old = .ok birthLogged ∧
                  birthLogged.buffer = old.buffer ++ ReferenceFollowerBufferProvenance.logEmission i r0 ∧
                  birthLogged.lastDown = old.lastDown ∧
                  (state = birthLogged ∨ state = { birthLogged with downBatch :=
                    (currentDecodeStep p i r0.input.row r0.input.time
                      (r0.output.preparation.feedback.observations (followerPlayer p.two_le_m i)) rate birthLogged).1 }) ∧
                  ActiveFollowerLogging.checkedLogging i r1.input.row (r1.input.state.activations i)
                    r1.input.time ((r1.output.preparation.followers.followers i).arm,
                      r1.output.preparation.feedback.observations (followerPlayer p.two_le_m i)) state = .ok logged ∧
                  logged.buffer = state.buffer ++ logAt i r1.input.row (r1.input.state.activations i)
                    r1.input.time ((r1.output.preparation.followers.followers i).arm,
                      r1.output.preparation.feedback.observations (followerPlayer p.two_le_m i)) ∧
                  localStateDomainValid logged ∧
                  state.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound) ∧
                  (∀ saved ∈ state.buffer, saved.calendarRound < r1.input.time.val + 1) ∧
                  logged.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound) ∧
                  (∀ saved ∈ logged.buffer, saved.calendarRound ≤ r1.input.time.val + 1) ∧
                let M := installed.registers.payload.downRecord i
                let own := r1.output.preparation.feedback.observations (followerPlayer p.two_le_m i)
                let decoded := currentDecodeStep p i r1.input.row r1.input.time own rate logged
                let cut := referenceDownCut p r1.output.preparation.coordinator.downView
                  i r1.input.row r1.input.time own rate logged
                let afterDecode := { logged with downBatch := decoded.1 }
                let a := ReferenceFollowerSparseEmissionRecovery.emissionContribution M i r0
                let g0 := min (4 * rate.n) (M.val.q + a)
                let b0 := M.val.q + a - g0
                let g1 := min (4 * rate.n) b0
                let accepted := { afterDecode with
                  lastDown := some M
                  S := g0 + g1
                  delta := g1
                  backlog := b0 - g1
                  status := .pending
                  buffer := [] }
                M.val.sigma = r1.input.time.val ∧ M.val.q ≤ r0.input.time.val * D p ∧
                acceptedStart logged < M.val.sigma ∧
                bufferArrivalAt p rate M logged r1.input.time.val = a ∧
                a = RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate)
                  cell0.input (installed.registers.payload.assignment.assigned i) ∧ a ≤ D p ∧
                (¬ SparseCalendarReplay.loggingTestsPass (loggingRound i r0.input.row
                  (r0.input.state.activations i) r0.input.time (r0.output.ownEntries (followerPlayer p.two_le_m i))) → a = 0) ∧
                (downSelected p i r1.input.row r1.input.time → logged = state ∧
                  bufferArrivalAt p rate M logged (r1.input.time.val + 1) = 0) ∧
                ∃ next,
                  (let nextMemory : LocalMemory p := if next.status = .unoccupied then memory else
                    ⟨some ⟨r1.input.time, FollowerCutoffScan.completeRowProposalBit
                      p rate.eta.val r1.input.row r1.input.time⟩⟩
                   DeclaredFollowerLocalRound.consumeDownResult rate cut.outcome = .ok next ∧
                   releaseAfterService rate.eta i r1.input.time (publicRowOfCompleteRow r1.input.row r1.input.time)
                     own state next = .ok next ∧
                   finishRound rate.eta r1.input.time r1.input.row next memory = .ok (next, nextMemory) ∧
                   DeclaredFollowerLocalRound.releaseAndFinish rate i r1.input.row r1.input.time own state memory next =
                     .ok (next, nextMemory) ∧
                   r1.output.followers i = ⟨.ordinary next nextMemory, none, some logged, some cut⟩ ∧
                   localStateDomainValid next ∧ next.S + next.backlog ≤ (r1.input.time.val + 1) * D p ∧
                   next.delta ≤ D p ∧ next.initializationFailure = state.initializationFailure) ∧
                  ((¬ downSelected p i r1.input.row r1.input.time ∧
                      cut.outcome = .skipped logged .notSelectedDown ∧ next = logged) ∨
                   (downSelected p i r1.input.row r1.input.time ∧ cut.raw = decoded.2 ∧ cut.filteredRaw = none ∧
                    cut.outcome = .decodeOrParseRejected logged afterDecode decoded.2 ∧
                    cut.ordinaryParse = ordinaryParse p rate decoded.2 ∧
                    (cut.ordinaryAcceptance ↔ ordinaryLocalAcceptanceTest p rate r1.input.time logged (ordinaryParse p rate decoded.2)) ∧
                    (cut.rawComparison = some false ∨ cut.rawComparison = some true ∧ decoded.2 = none) ∧ next = afterDecode) ∨
                   (downSelected p i r1.input.row r1.input.time ∧ decoded.2 =
                      some (CoordinatorLocalArmChoice.storedDownFlatWord installed.registers.payload i) ∧
                    cut.raw = decoded.2 ∧ cut.filteredRaw = decoded.2 ∧ cut.rawComparison = some true ∧
                    cut.ordinaryParse = some M ∧ cut.ordinaryAcceptance ∧
                    cut.outcome = .accepted logged accepted decoded.2 M
                      ⟨r1.input.time.val + 2, [downStart p rate M]⟩ (g0 + g1, b0 - g1) g1 ∧
                    recoveryRounds p rate M (r1.input.time.val + 2) = [r1.input.time.val, r1.input.time.val + 1] ∧
                    recoveryQueueRecords p rate M logged (r1.input.time.val + 2) = [(true, a), (true, 0)] ∧
                    checkedRecovery p rate M logged (r1.input.time.val + 2) = .ok ⟨(g0 + g1, b0 - g1), g1⟩ ∧
                    g0 + g1 + (b0 - g1) = M.val.q + a ∧ M.val.q + a ≤ r1.input.time.val * D p ∧
                    (∀ k, ∃ middle, checkedReplay (D p) (p.T * D p) (4 * rate.n) 0 ⟨(0, M.val.q), 0⟩
                      ((recoveryQueueRecords p rate M logged (r1.input.time.val + 2)).take k) = .ok middle ∧
                      replay_register_domain (D p) (p.T * D p) middle ∧
                      middle.registers = QueueReplay.replay (4 * rate.n) (0, M.val.q)
                        ((recoveryQueueRecords p rate M logged (r1.input.time.val + 2)).take k)) ∧ next = accepted)))
          | _ => True
      | _ => True := by
  classical
  have hprep := complete_first_replacement_next_preparation_and_occupied_step rate source rewards C_star C_h
  have hcont := complete_first_replacement_next_continuing_readout rate source rewards C_star C_h
  have hbirth := complete_first_replacement_birth_live_readout rate source rewards C_star C_h
  have hadj := complete_first_replacement_actual_successor rate source rewards C_star C_h
  have hroot := ReferenceFirstReplacementDownRecovery.complete_first_replacement_down_recovery_and_finish
    rate source rewards C_star C_h
  have hseed := ReferenceFirstReplacementFollowerLoggingSeed.complete_first_replacement_follower_logging_seed
    rate source rewards C_star C_h
  dsimp only at hprep hcont hbirth hadj hroot hseed ⊢
  set R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
  set s := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
  set w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
  set v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
  cases hg0 : R[v]? with
  | none => trivial
  | some r0 =>
    simp only [hg0] at hprep hcont hbirth hadj hroot hseed ⊢
    cases hcut0 : r0.output.preparation.coordinator with
    | first _ => trivial
    | live _ _ _ _ => trivial
    | dagger => trivial
    | invalidCollectionCutoff => trivial
    | collection oldPayload ledger clock cutoff outcome =>
      rw [hcut0] at hprep hcont hbirth hroot hseed
      cases outcome <;> try trivial
      rename_i core consistent started hs instruction hi output hcons clockData installed arm
      cases hg1 : R[v + 1]? with
      | none => trivial
      | some r1 =>
        simp only [hg1] at hprep hcont hadj ⊢
        obtain ⟨_hc, _h0, _h1, _hrun0, _hrun1, hstate, htime⟩ := hadj
        obtain ⟨_hstart, hfollowers⟩ := hprep
        obtain ⟨_hfirst, hbirthFollowers⟩ := hroot
        obtain ⟨_hinstall, _holdSigma, _htime, _hrows, _hJ, _hrewards, hnewTime, hseedFollowers⟩ := hseed
        obtain ⟨k0, _hk0, hr0, selected0, hsel0, hpay0, _hsigma0, _hlive0,
          c0, hread0, _hnum0, hreadAt0, _hcell0⟩ := hbirth
        have hphysical := ReferenceLaterLiveNumericalReadout.laterLiveReadout_physical
          rate rewards C_star C_h source k0 c0 hreadAt0
        rw [hr0] at hphysical
        obtain ⟨cell0, hcell0, hen0, _htrace0, _henabled0, _hrows0, _hselected0, _hrewards0,
          _hmarker0, hfields0, _howners0, _hoccupied0, _hunoccupied0, _hlogging0, _hcoord0, hu0⟩ := hphysical
        have hsel0' : r0.output.preparation.coordinator.selection = some selected0 := by
          rw [hcut0]; exact hsel0
        have hpayCell0 : cell0.selected.view.payload = installed.registers.payload := by
          have he : cell0.selected = selected0 := Option.some.inj (cell0.selection_actual.symm.trans hsel0')
          rw [he]; exact hpay0
        have hreadCell0 : ReferenceLaterLiveNumericalReadout.laterLiveReadout s r0 = some cell0.input := by
          rw [hcell0]; exact hread0
        rw [hcut0] at hu0
        dsimp only at hu0
        cases hcut1 : r1.output.preparation.coordinator with
        | first _ => trivial
        | collection _ _ _ _ _ => trivial
        | dagger => trivial
        | invalidCollectionCutoff => trivial
        | live r q base outcome =>
          rw [hcut1] at hcont
          cases outcome <;> try trivial
          rename_i dispatched hstart continuation arm1
          obtain ⟨selected1, hsel1, hpay1, hsigma1, hlive1, hno,
            cell1, hread1, hpayCell1, _hoccupied1, _howners1⟩ := hcont
          let k1 : Fin R.length := ⟨v + 1, (List.getElem?_eq_some_iff.mp hg1).1⟩
          have hr1 : R.get k1 = r1 := (List.getElem?_eq_some_iff.mp hg1).2
          have hclock := complete_suffix_record_clock rate source rewards C_star C_h k1
          rw [hr1] at hclock
          have hscanFacts := continuing_scan_facts r1 hclock
          rw [hcut1] at hscanFacts
          have hselectedPayload : selected1.view.payload = r.payload := by
            have h := hsel1
            simp only [DispatchCut.selection, selectionAt, dite_true] at h
            exact (congrArg (fun z => z.view.payload) (Option.some.inj h)).symm
          have hpay : r.payload = installed.registers.payload := hselectedPayload.symm.trans hpay1
          have hnewStart : r.payload.sigma.val + 1 = r1.input.time.val := by
            rw [hpay, hnewTime, htime]
          obtain ⟨hgrid, hbit⟩ := hscanFacts hnewStart
          rw [hpay] at hgrid hbit
          refine ⟨hstate, htime, (by omega), selected1, ?_, hpay1, hsigma1, hlive1,
            cell0, hpayCell0, hreadCell0, ?_, cell1, hpayCell1, hread1, ?_⟩
          · exact hsel1
          · rw [hcell0]; exact hen0
          · intro i
            obtain ⟨state, memory, hconfig, hdomain, hmass, _hbusy, before,
              _hbeforeDomain, houtput, hinput, hstartLocal, _hbeforeCases⟩ := hfollowers i
            obtain ⟨before', state', memory', hinput', hconfig', hdecision, hsame'⟩ := hno i
            have he := hinput.symm.trans hinput'
            simp only [DeclaredFollowerLocalRound.LocalConfiguration.ordinary.injEq] at he
            obtain ⟨heBefore, heMemory⟩ := he
            subst before'
            subst memory'
            have he := hconfig.symm.trans hconfig'
            simp only [DeclaredFollowerLocalRound.LocalConfiguration.ordinary.injEq] at he
            obtain ⟨heState, _⟩ := he
            subst state'
            subst before
            refine ⟨state, memory, hinput', hconfig', hdomain, hmass, hdecision, ?_⟩
            intro hunoccupied
            obtain ⟨old, birthMemory, birthLogged, hinput0, hstatus0, hconfig0, hloggingBirth,
              _hop0, _hstrict0, hsigma0, hcredit0, _hzero0, birthNext, htail0, hcases0⟩ := hbirthFollowers i
            obtain ⟨seedOld, seedMemory, seedLogged, hseedInput, _hseedStatus, _hseedDomain,
              _hseedBuffer, _hseedDecoder, _hseedEndpoint, _hseedMass, _hseedTimes, _hseedKeys,
              _hseedQuantized, hpairOld, hbefore0, hold, _hseedRest⟩ := hseedFollowers i
            have he := hinput0.symm.trans hseedInput
            simp only [DeclaredFollowerLocalRound.LocalConfiguration.ordinary.injEq] at he
            obtain ⟨heOld, heBirthMemory⟩ := he
            subst seedOld
            subst seedMemory
            obtain ⟨_hconsume0, _hrelease0, _hfinish0, _htail0, houtput0,
              _hdomain0, _hmass0, _hdelta0, _hflag0⟩ := htail0
            have hout0 : (r0.output.followers i).configuration = .ordinary birthNext
                (if birthNext.status = .unoccupied then birthMemory else
                  ⟨some ⟨r0.input.time, FollowerCutoffScan.completeRowProposalBit
                    p rate.eta.val r0.input.row r0.input.time⟩⟩) := by
              rw [houtput0]
            have he := houtput.symm.trans hout0
            simp only [DeclaredFollowerLocalRound.LocalConfiguration.ordinary.injEq] at he
            obtain ⟨heState, _heMemory⟩ := he
            have hbirthNextStatus : birthNext.status = .unoccupied := heState ▸ hunoccupied
            have hretained : state = birthLogged ∨ state = { birthLogged with downBatch :=
                (currentDecodeStep p i r0.input.row r0.input.time
                  (r0.output.preparation.feedback.observations (followerPlayer p.two_le_m i)) rate birthLogged).1 } := by
              rcases hcases0 with hc | hc | hc
              · exact Or.inl (heState.trans hc.2.2)
              · exact Or.inr (heState.trans hc.2.2.2.2.2)
              · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, heAccepted⟩ := hc
                rw [heAccepted] at hbirthNextStatus
                cases hbirthNextStatus
            have hbirthBuffer : birthLogged.buffer = old.buffer ++ ReferenceFollowerBufferProvenance.logEmission i r0 := by
              have h := ActiveFollowerLogging.checkedLogging_success_buffer i r0.input.row
                (r0.input.state.activations i) r0.input.time _ old birthLogged hloggingBirth
              rw [ite_eq_left ⟨r0.input.active i, hstatus0⟩] at h
              have hem : ReferenceFollowerBufferProvenance.logEmission i r0 =
                  logAt i r0.input.row (r0.input.state.activations i) r0.input.time
                    ((r0.output.preparation.followers.followers i).arm,
                      r0.output.preparation.feedback.observations (followerPlayer p.two_le_m i)) := by
                simp only [ReferenceFollowerBufferProvenance.logEmission, hconfig0, hstatus0, dite_true]
                rw [ReferenceFollowerBufferProvenance.round_ownEntry_eq_prepared]
              rw [hem]; exact h
            have hframe0 := ActiveFollowerLogging.checkedLogging_success_frame i r0.input.row
              (r0.input.state.activations i) r0.input.time _ old birthLogged hloggingBirth
            have hstateBuffer : state.buffer = birthLogged.buffer := by
              rcases hretained with h | h <;> rw [h]
            have hstatePair : state.buffer.Pairwise
                (fun a b => a.calendarRound < b.calendarRound) := by
              rw [hstateBuffer, hbirthBuffer, List.pairwise_append]
              refine ⟨hpairOld, ReferenceFollowerBufferProvenance.logEmission_pairwise i r0, ?_⟩
              intro a ha b hb
              have := hbefore0 a ha
              have := ReferenceFollowerBufferProvenance.logEmission_source_timestamp i r0 b hb
              omega
            have hstateLast : state.lastDown = old.lastDown := by
              rcases hretained with h | h <;> rw [h] <;> exact hframe0.1
            have hbefore1 : ∀ saved ∈ state.buffer, saved.calendarRound < r1.input.time.val + 1 := by
              rw [hstateBuffer, hbirthBuffer]
              intro saved hsaved
              rcases List.mem_append.mp hsaved with h | h
              · have := hbefore0 saved h; omega
              · have := ReferenceFollowerBufferProvenance.logEmission_source_timestamp i r0 saved h
                omega
            let own1 := ((r1.output.preparation.followers.followers i).arm,
              r1.output.preparation.feedback.observations (followerPlayer p.two_le_m i))
            obtain ⟨logged, hlogging, hlogBuffer, hlogStatus, hlogFlag, hlogValid⟩ :=
              ActiveFollowerLogging.checkedLogging_success_of_chronological i r1.input.row
                (r1.input.state.activations i) r1.input.time own1 state hdomain.2.1 hbefore1 hunoccupied
            have hlogPair : logged.buffer.Pairwise
                (fun a b => a.calendarRound < b.calendarRound) := by
              rw [hlogBuffer, List.pairwise_append]
              refine ⟨hstatePair, ?_, ?_⟩
              · unfold logAt
                split <;> simp only [List.pairwise_singleton, List.Pairwise.nil]
              · intro a ha b hb
                have := hbefore1 a ha
                have := (ActiveFollowerLogging.logAt_member_fields i r1.input.row
                  (r1.input.state.activations i) r1.input.time own1 b hb).1
                omega
            have hlogTime : ∀ saved ∈ logged.buffer,
                saved.calendarRound ≤ r1.input.time.val + 1 := by
              rw [hlogBuffer]
              intro saved hsaved
              rcases List.mem_append.mp hsaved with h | h
              · exact Nat.le_of_lt (hbefore1 saved h)
              · exact Nat.le_of_eq (ActiveFollowerLogging.logAt_member_fields i r1.input.row
                  (r1.input.state.activations i) r1.input.time own1 saved h).1
            have hframe1 := ActiveFollowerLogging.checkedLogging_success_frame i r1.input.row
              (r1.input.state.activations i) r1.input.time own1 state logged hlogging
            have hlogDomain : localStateDomainValid logged := by
              refine ⟨?_, hlogValid, ?_⟩
              · exact ⟨hframe1.2.1 ▸ hdomain.1.1, hframe1.2.2.1 ▸ hdomain.1.2.1,
                  hframe1.2.2.2.1 ▸ hdomain.1.2.2⟩
              · unfold downDecoderStateValid
                rw [hframe1.2.2.2.2.2.1]; exact hdomain.2.2
            let M := installed.registers.payload.downRecord i
            let a := ReferenceFollowerSparseEmissionRecovery.emissionContribution M i r0
            have hsigma : M.val.sigma = r1.input.time.val := hsigma0.trans htime.symm
            have hstrict : acceptedStart logged < M.val.sigma := by
              rw [acceptedStart, hframe1.1, hstateLast]
              rcases hold with hn | ho
              · rw [hn.1]; dsimp only; have := PrelaunchBufferRecovery.down_sigma_pos rate.eta M; omega
              · rw [ho]
                change (oldPayload.downRecord i).val.sigma < M.val.sigma
                change oldPayload.sigma.val + 1 < M.val.sigma
                rw [_holdSigma, hsigma, htime]
                omega
            have hcoord : downStart p rate M = installed.registers.payload.sigma := by
              apply Fin.ext
              have h := downStart_val_add_one p rate M
              change (installed.registers.payload.downRecord i).val.sigma = _ at hsigma0
              have hd := installed.registers.payload.downRecord_fields i
              omega
            have hzeroOld (r : ℕ) (hr : r0.input.time.val + 1 ≤ r) :
                sparseBufferContribution (p.m - 1) (D p : ℝ) rate.eta.val M.val.h
                  (PrelaunchBufferRecovery.downArm rate.eta M) r old.buffer = 0 := by
              apply ReferenceFollowerSparseEmissionRecovery.sparseBufferContribution_zero_of_no_matching_round
              intro saved hsaved
              have := hbefore0 saved hsaved
              omega
            have hdelta : bufferArrivalAt p rate M logged r1.input.time.val = a := by
              unfold bufferArrivalAt
              rw [hlogBuffer, hstateBuffer, hbirthBuffer, sparseBufferContribution_append,
                sparseBufferContribution_append, hzeroOld _ (by omega), zero_add]
              have hz : sparseBufferContribution (p.m - 1) (D p : ℝ) rate.eta.val M.val.h
                  (PrelaunchBufferRecovery.downArm rate.eta M) r1.input.time.val
                  (logAt i r1.input.row (r1.input.state.activations i) r1.input.time own1) = 0 := by
                apply ReferenceFollowerSparseEmissionRecovery.sparseBufferContribution_zero_of_no_matching_round
                intro saved hsaved
                have := (ActiveFollowerLogging.logAt_member_fields i r1.input.row
                  (r1.input.state.activations i) r1.input.time own1 saved hsaved).1
                omega
              rw [hz, Nat.add_zero]
              dsimp only [a, ReferenceFollowerSparseEmissionRecovery.emissionContribution]
              rw [htime]
            have harrival : a = RecordedQueueRun.quantizedArrival
                (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell0.input
                (installed.registers.payload.assignment.assigned i) := by
              have h := ReferenceFirstLiveUnoccupiedEmission.emissionContribution_eq_quantizedArrival
                r0 cell0 hfields0 i (hu0 i)
              rw [hpayCell0] at h
              exact h
            have ha : a ≤ D p := by rw [← hdelta]; exact bufferArrival_le_D M logged hlogValid _
            have hnotLog : ¬ loggingTestsPass (loggingRound i r0.input.row (r0.input.state.activations i)
                r0.input.time (r0.output.ownEntries (followerPlayer p.two_le_m i))) → a = 0 := by
              intro hn
              have he : ReferenceFollowerBufferProvenance.logEmission i r0 = [] := by
                simp only [ReferenceFollowerBufferProvenance.logEmission, cell0.ordinary i, hu0 i, dite_true]
                exact ActiveFollowerLogging.logAt_eq_nil_of_not_tests _ _ _ _ _ hn
              simp only [a, ReferenceFollowerSparseEmissionRecovery.emissionContribution, he,
                sparseBufferContribution, List.foldr_nil]
            have hdown : downSelected p i r1.input.row r1.input.time → logged = state ∧
                bufferArrivalAt p rate M logged (r1.input.time.val + 1) = 0 := by
              intro hd
              have he := logged_eq_old_on_down i r1.input.row (r1.input.state.activations i)
                r1.input.time own1 state logged hlogging hd.1
              refine ⟨he, ?_⟩
              rw [he]
              apply ReferenceFollowerSparseEmissionRecovery.sparseBufferContribution_zero_of_no_matching_round
              intro saved hsaved
              have := hbefore1 saved hsaved
              omega
            have hview : r1.output.preparation.coordinator.downView = some selected1.view := by
              simp only [DispatchCut.downView, hcut1, hsel1, Option.map_some]
            have hexpected : expectedDownFlatWord r1.output.preparation.coordinator.downView
                i r1.input.row r1.input.time = none ∨
                expectedDownFlatWord r1.output.preparation.coordinator.downView i r1.input.row r1.input.time =
                  some (CoordinatorLocalArmChoice.storedDownFlatWord installed.registers.payload i) := by
              rw [hview]
              by_cases hbranch : CoordinatorLocalArmChoice.coordinatorArmChoice
                  selected1.view.payload selected1.view.pendingAtChoice selected1.view.cutoff
                  r1.input.time selected1.view.complementWeights r1.input.row ≠ none ∧
                  selectedDownSenderBranch selected1.view i r1.input.row r1.input.time
              · right
                change (if _ then _ else _) = _
                rw [ite_eq_left hbranch, hpay1]
                rfl
              · left
                change (if _ then _ else _) = _
                exact ite_eq_right hbranch
            have hcredit : M.val.q ≤ (r1.input.time.val - 1) * D p := by
              rw [htime, Nat.add_sub_cancel]; exact hcredit0
            have hmassLog : logged.S + logged.backlog ≤ r1.input.time.val * D p := by
              rw [hframe1.2.1, hframe1.2.2.2.1]; exact hmass
            have hg : r1.input.time.val + 2 ≤ FollowerCutoffScan.gridBoundary p rate.eta.val (downStart p rate M) := by
              rw [hcoord]; exact hgrid
            have hb : FollowerCutoffScan.completeRowProposalBit p rate.eta.val r1.input.row (downStart p rate M) = false := by
              rw [hcoord]; exact hbit
            obtain ⟨next, hconsume, hdNext, hmNext, hflagNext, hcompat, hcases⟩ := down_cut_next (p := p) (rate := rate)
              r1.output.preparation.coordinator.downView installed.registers.payload i r1.input.row
              r1.input.time own1.2 logged hlogDomain (hlogStatus.trans hunoccupied) hsigma hstrict
              hcredit hmassLog hexpected hg hb (fun hd => (hdown hd).2)
            refine ⟨old, birthMemory, birthLogged, logged, hinput0, hconfig0, hstatus0,
              hold, hbefore0, hloggingBirth, hbirthBuffer, hframe0.1, hretained,
              hlogging, hlogBuffer, hlogDomain, hstatePair, hbefore1, hlogPair, hlogTime, hsigma, hcredit0, hstrict, hdelta,
              harrival, ha, hnotLog, hdown, next, ?_, ?_⟩
            · have hfinish := finish_actual r1 i state logged next memory hconfig' hunoccupied hlogging
                hconsume hdNext hmNext (hflagNext.trans hlogFlag)
                (fun hbusy => ⟨M, hcompat hbusy, (Nat.le_of_eq hsigma).trans (Nat.le_add_right _ _)⟩)
              simpa only [hcut1] using hfinish
            · dsimp only at hcases
              have hdeltaExact : bufferArrivalAt p rate (installed.registers.payload.downRecord i)
                  logged r1.input.time.val = ReferenceFollowerSparseEmissionRecovery.emissionContribution
                    (installed.registers.payload.downRecord i) i r0 := hdelta
              simp only [hcut1] at hcases
              exact hdeltaExact ▸ hcases

end Bandits.Support.ReferenceFirstReplacementNextDownReplay
end
