/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstReplacementNextDownReplay

import Mathlib.Data.List.TakeWhile

/-!
# The finite continuing prefix after the first replacement

Sources: `sources/zip4/manuscript/05_binary_transport.tex:354-431`,
`06_interruptions.tex:9-70,193-233,246-295`,
`04_slow_fast_learner.tex:157-188`, and
`appendix_a_local_protocol.tex:28-79`.

The window below is a slice of the original complete physical records. The
payload's `sigma.val` is a zero-based coordinate; its DOWN record stores the
one-based calendar start `sigma.val + 1`. Recovery retains the transmitted
queue and services every calendar round, including zero-arrival rounds.
These are internal prefix results, not manuscript closure. The unconditional
follower-boundary induction and full chronological source-emission identity
are not proved by this module's conditional one-record helpers.
-/

@[expose] public section
noncomputable section

namespace Bandits.Support.ReferenceFirstReplacementLiveFollowerPrefix

open ConstructorDimensions ReferenceActivePhysicalStep ReferenceActivePhysicalHorizon
open ReferencePrelaunchFollower ActiveFollowerLifecycle ActiveFollowerDownAcceptance
open ReferenceDownReception SparseCalendarReplay PublicDiscreteDraws
open ReferenceFirstReplacementNextFollowerStep

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

/-- Recognize exactly the actual continuing chosen live dispatcher constructor. -/
def isContinuingChosen
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) : Bool :=
  match r.output.preparation.coordinator with
  | .live _ _ _ (.continuingChosen ..) => true
  | _ => false

/-- The finite original-record slice after the birth at index `v`. It may be
empty and stops before its first noncontinuing record. -/
def continuingTail
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (v : ℕ) :=
  (records.drop (v + 1)).takeWhile isContinuingChosen

/-- Every retained record satisfies the literal constructor test. -/
theorem continuingTail_mem
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (v : ℕ) (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : r ∈ continuingTail records v) : isContinuingChosen r = true :=
  List.mem_takeWhile_imp hr

/-- Indexed members are the original records at their original indices. -/
theorem continuingTail_get
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (v : ℕ) (k : Fin (continuingTail records v).length) :
    records[v + 1 + k.val]? = some ((continuingTail records v).get k) := by
  have hp : continuingTail records v <+: records.drop (v + 1) := List.takeWhile_prefix _
  have hk : k.val < records.length - (v + 1) := by
    simpa only [List.length_drop] using Nat.lt_of_lt_of_le k.isLt hp.length_le
  have hindex : v + 1 + k.val < records.length := by omega
  apply List.getElem?_eq_some_iff.mpr
  refine ⟨hindex, ?_⟩
  simpa only [List.get_eq_getElem, List.getElem_drop, Nat.add_comm, Nat.add_left_comm,
    Nat.add_assoc] using (hp.getElem k.isLt).symm

private theorem complete_record_fields
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length) :
    let r := (ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h).get k
    r.input.time.val = ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h + k.val ∧
    r.input.rows = source.1.2 ∧
    r.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p source ∧
    r.input.rewards = rewards := by
  obtain ⟨hc, hspan, hr⟩ := ReferenceLaterLiveNumericalReadout.source_record_prefix
    rate rewards C_star C_h source k
  rw [hr]
  exact ⟨rfl, rfl, rfl, rfl⟩

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
  obtain ⟨hc0, hs0, hr0⟩ := ReferenceLaterLiveNumericalReadout.source_record_prefix
    rate rewards C_star C_h source ⟨k, by omega⟩
  obtain ⟨hc1, hs1, hr1⟩ := ReferenceLaterLiveNumericalReadout.source_record_prefix
    rate rewards C_star C_h source ⟨k + 1, hk⟩
  rw [hr0, hr1]
  constructor
  · exact ReferenceAssignmentPayloadChronology.run_successor_finalState_eq_actualRunRecordAt
      _ source.1.2 _ rewards _ k _ _
  · rfl

private theorem operation_input_of_local_domain
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (h : localStateDomainValid state) : operationInputDomain p rate state := by
  refine ⟨h.1, h.2.2, ?_⟩
  refine ⟨?_, h.2.1.2.1⟩
  intro saved hsaved
  obtain ⟨q, hq, heq⟩ := h.2.1.2.2 saved hsaved
  exact ⟨(h.2.1.1 saved hsaved).1, (h.2.1.1 saved hsaved).2,
    ⟨⟨q, by omega⟩, heq⟩⟩

private theorem sparse_contribution_zero_of_no_key
    (d : ℕ) (D eta : ℝ) (h : ℕ) (arm : Fin p.K) (r : ℕ)
    (buffer : List (SparseCalendarRecord p.K))
    (hno : ∀ saved ∈ buffer, ¬ (saved.calendarRound = r ∧ saved.pilot = arm)) :
    sparseBufferContribution d D eta h arm r buffer = 0 := by
  classical
  induction buffer with
  | nil => rfl
  | cons saved rest ih =>
      have hhead := hno saved List.mem_cons_self
      have htail : ∀ item ∈ rest, ¬ (item.calendarRound = r ∧ item.pilot = arm) :=
        fun item hi => hno item (List.mem_cons_of_mem _ hi)
      change (if saved.calendarRound = r ∧ saved.pilot = arm then
          savedContribution p.K d D eta h saved.observation saved.thinScalar else 0) +
        sparseBufferContribution d D eta h arm r rest = 0
      rw [ite_eq_right hhead, zero_add]
      exact ih htail

private theorem sparse_contribution_le_of_unique_key
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
      · have hzero : sparseBufferContribution d (D : ℝ) eta h arm r rest = 0 := by
          apply sparse_contribution_zero_of_no_key
          intro item hitem hitemKey
          apply hkeys.1
          exact List.mem_map.mpr ⟨item, hitem,
            Prod.ext (hitemKey.1.trans hkey.1.symm) (hitemKey.2.trans hkey.2.symm)⟩
        change (if saved.calendarRound = r ∧ saved.pilot = arm then
            savedContribution p.K d (D : ℝ) eta h saved.observation saved.thinScalar else 0) +
          sparseBufferContribution d (D : ℝ) eta h arm r rest ≤ D
        rw [ite_eq_left hkey, hzero, Nat.add_zero]
        exact hcontribution saved List.mem_cons_self hkey.1 hkey.2
      · change (if saved.calendarRound = r ∧ saved.pilot = arm then
            savedContribution p.K d (D : ℝ) eta h saved.observation saved.thinScalar else 0) +
          sparseBufferContribution d (D : ℝ) eta h arm r rest ≤ D
        rw [ite_eq_right hkey, zero_add]
        exact ih hkeys.2 htail

private theorem buffer_arrival_le_D
    (M : OrdinaryMessageCodec.DownRecord (codecParams p rate.eta))
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (hvalid : localBufferValid state) (r : ℕ) :
    bufferArrivalAt p rate M state r ≤ D p := by
  change sparseBufferContribution (p.m - 1) (D p : ℝ) rate.eta.val M.val.h
    (PrelaunchBufferRecovery.downArm rate.eta M) r state.buffer ≤ D p
  apply sparse_contribution_le_of_unique_key _ _ _ _ _ _ state.buffer
    (localBufferValid_keys_nodup hvalid)
  intro saved hsaved _ _
  by_cases hthin : saved.thinScalar.1 ≤
      (4 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ) * (((2 : ℝ) ^ M.val.h)⁻¹)) /
        sparseMaskProbability p.K (p.m - 1)
  · rw [savedContribution_eq_floor_of_le p.K (p.m - 1) (D p : ℝ)
      rate.eta.val M.val.h saved.observation saved.thinScalar hthin]
    obtain ⟨own, hown⟩ := localBufferValid_observation_typed hvalid saved hsaved
    have hfloor := ActiveFollowerQueueOperation.sourceArrivalFloor_le_D rate.eta M own
    have hsame := ActiveFollowerQueueOperation.sourceArrivalFloor_eq_savedFloor rate.eta M own
    rw [hown] at hsame
    rw [hsame] at hfloor
    exact hfloor
  · simp [savedContribution, hthin]

private theorem checked_calendar_of_mass
    (D T capacity offset elapsed : ℕ) (current : ReplayRegisters)
    (arrivalAt : ℕ → ℕ) (rounds : List ℕ)
    (hlast : current.lastService ≤ D)
    (hmass : current.registers.1 + current.registers.2 ≤ elapsed * D)
    (hcapacity : capacity ≤ D)
    (harrival : ∀ r ∈ rounds, arrivalAt r ≤ D)
    (hspan : elapsed + rounds.length ≤ T) :
    ∃ final, checkedCalendarReplay D (T * D) capacity offset current arrivalAt rounds = .ok final ∧
      final.registers.1 + final.registers.2 ≤ (elapsed + rounds.length) * D ∧
      final.lastService ≤ D := by
  induction rounds generalizing current offset elapsed with
  | nil =>
      have hbound := hmass.trans (Nat.mul_le_mul_right D (show elapsed ≤ T by simpa using hspan))
      have hd : replay_register_domain D (T * D) current := ⟨by omega, hlast, by omega⟩
      exact ⟨current, by simp only [checkedCalendarReplay, ite_eq_left hd],
        by simpa only [List.length_nil, Nat.add_zero] using hmass, hlast⟩
  | cons r rest ih =>
      have ha := harrival r List.mem_cons_self
      have htail : ∀ u ∈ rest, arrivalAt u ≤ D := fun u hu =>
        harrival u (List.mem_cons_of_mem _ hu)
      let service := min capacity (current.registers.2 + arrivalAt r)
      let next : ReplayRegisters :=
        ⟨QueueReplay.transition capacity current.registers (true, arrivalAt r), service⟩
      have hservice : service ≤ D := (Nat.min_le_left _ _).trans hcapacity
      have hmin : service ≤ current.registers.2 + arrivalAt r := Nat.min_le_right _ _
      have hconserve : next.registers.1 + next.registers.2 =
          current.registers.1 + current.registers.2 + arrivalAt r := by
        change current.registers.1 + service +
          (current.registers.2 + arrivalAt r - service) = _
        omega
      have hmassNext : next.registers.1 + next.registers.2 ≤ (elapsed + 1) * D := by
        rw [hconserve, Nat.add_mul, one_mul]
        omega
      have hspanNext : elapsed + 1 + rest.length ≤ T := by
        simp only [List.length_cons] at hspan
        omega
      have hbound := hmassNext.trans (Nat.mul_le_mul_right D (by omega : elapsed + 1 ≤ T))
      have hdNext : replay_register_domain D (T * D) next := ⟨by omega, hservice, by omega⟩
      have hboundOld := hmass.trans (Nat.mul_le_mul_right D (by omega : elapsed ≤ T))
      have hd : replay_register_domain D (T * D) current := ⟨by omega, hlast, by omega⟩
      have hu : checkedReplayUpdate D (T * D) capacity current (true, arrivalAt r) = .ok next := by
        unfold checkedReplayUpdate
        rw [ite_eq_left ha]
        change (if service ≤ D then _ else _) = _
        rw [ite_eq_left hservice]
        rw [ite_eq_left hdNext.1, ite_eq_left hdNext.2.2]
        rfl
      obtain ⟨final, hf, hm, hl⟩ := ih (offset + 1) (elapsed + 1) next
        hservice hmassNext htail hspanNext
      refine ⟨final, ?_, ?_, hl⟩
      · simpa only [checkedCalendarReplay, ite_eq_left hd, hu] using hf
      · simpa only [List.length_cons, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hm

/-- Arbitrary-length checked recovery from the original, possibly nonzero
DOWN queue. The conditional inputs are local buffer validity, source-time
credit and an actual calendar endpoint; no successful replay is assumed. -/
theorem checked_recovery_of_calendar_credit
    (M : OrdinaryMessageCodec.DownRecord (codecParams p rate.eta))
    (state : ReferencePrelaunchFollower.State p rate.eta) (t : Fin p.T)
    (hvalid : localBufferValid state)
    (hstart : M.val.sigma ≤ t.val + 1)
    (hcredit : M.val.q ≤ (M.val.sigma - 1) * D p) :
    ∃ final, checkedRecovery p rate M state (t.val + 2) = .ok final ∧
      final.registers.1 + final.registers.2 ≤ (t.val + 1) * D p ∧
      final.lastService ≤ D p ∧
      replay_register_domain (D p) (p.T * D p) final ∧
      final.registers = QueueReplay.replay (4 * rate.n) (0, M.val.q)
        (recoveryQueueRecords p rate M state (t.val + 2)) ∧
      (∀ k, ∃ middle,
        checkedReplay (D p) (p.T * D p) (4 * rate.n) 0 ⟨(0, M.val.q), 0⟩
          ((recoveryQueueRecords p rate M state (t.val + 2)).take k) = .ok middle ∧
        replay_register_domain (D p) (p.T * D p) middle ∧
        middle.registers = QueueReplay.replay (4 * rate.n) (0, M.val.q)
          ((recoveryQueueRecords p rate M state (t.val + 2)).take k)) := by
  have hpos := PrelaunchBufferRecovery.down_sigma_pos rate.eta M
  have hlength : (M.val.sigma - 1) + (recoveryRounds p rate M (t.val + 2)).length =
      t.val + 1 := by rw [recoveryRounds_length]; omega
  obtain ⟨final, hc, hm, hl⟩ := checked_calendar_of_mass (D p) p.T (4 * rate.n)
    0 (M.val.sigma - 1) ⟨(0, M.val.q), 0⟩ (bufferArrivalAt p rate M state)
    (recoveryRounds p rate M (t.val + 2)) (Nat.zero_le _)
    (by simpa only [Nat.zero_add] using hcredit) (four_n_le_D p rate)
    (fun r _ => buffer_arrival_le_D M state hvalid r) (by rw [hlength]; omega)
  change checkedRecovery p rate M state (t.val + 2) = .ok final at hc
  have hs := checkedRecovery_success p rate M state (t.val + 2) final hc
  refine ⟨final, hc, ?_, hl, hs.1, hs.2.1, ?_⟩
  · rw [hlength] at hm
    exact hm
  · exact fun k => checkedRecovery_success_prefix p rate M state (t.val + 2) final hc k

private theorem scan_live_endpoint
    (row : CompletePublicTable.CompleteRow p) (t : Fin p.T)
    (M : OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (hstart : (downStart p rate M).val ≤ t.val)
    (hgrid : t.val + 2 ≤ FollowerCutoffScan.gridBoundary p rate.eta.val (downStart p rate M))
    (hbits : ∀ j : Fin p.T, (downStart p rate M).val ≤ j.val → j.val < t.val →
      FollowerCutoffScan.completeRowProposalBit p rate.eta.val row j = false) :
    (acceptedCutoffScan p rate M t hstart row).endpoint = t.val + 2 := by
  classical
  rw [acceptedCutoffScan, FollowerCutoffScan.completeRowCutoffScan,
    FollowerCutoffScan.followerCutoffScan_endpoint_eq_knownCutoff]
  have hempty : FollowerCutoffScan.trueProposalEndpoints (FollowerCutoffScan.completeRowProposalBit p rate.eta.val row)
      (FollowerCutoffScan.pastProposalCoordinates p (downStart p rate M) t) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨j, hj, _⟩ := Finset.mem_image.mp hx
    simp only [Finset.mem_filter, FollowerCutoffScan.pastProposalCoordinates, FollowerCutoffScan.proposalCoordinates,
      Finset.mem_univ, true_and] at hj
    have hf := hbits j hj.1.1.1 hj.1.2
    rw [hf] at hj
    cases hj.2
  unfold FollowerCutoffScan.knownCutoff FollowerCutoffScan.knownCutoffCarrier
  simp only [hempty]
  apply le_antisymm
  · exact Finset.min'_le _ _ (Finset.mem_insert_self _ _)
  · apply Finset.le_min'
    intro x hx
    simp only [Finset.mem_insert, Finset.notMem_empty, or_false] at hx
    rcases hx with rfl | rfl
    · exact le_rfl
    · exact hgrid

private theorem down_cut_live
    (view : Option (ChoiceTimeView p rate.eta)) (payload : Payload rate)
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (t : Fin p.T) (own : Observation p)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (hdomain : localStateDomainValid state) (hstatus : state.status = .unoccupied)
    (hstart : (payload.downRecord i).val.sigma ≤ t.val + 1)
    (hstrict : acceptedStart state < (payload.downRecord i).val.sigma)
    (hcredit : (payload.downRecord i).val.q ≤ ((payload.downRecord i).val.sigma - 1) * D p)
    (hmass : state.S + state.backlog ≤ t.val * D p)
    (hexpected : expectedDownFlatWord view i row t = none ∨
      expectedDownFlatWord view i row t = some (CoordinatorLocalArmChoice.storedDownFlatWord payload i))
    (hgrid : t.val + 2 ≤ FollowerCutoffScan.gridBoundary p rate.eta.val
      (downStart p rate (payload.downRecord i)))
    (hbits : ∀ j : Fin p.T, (downStart p rate (payload.downRecord i)).val ≤ j.val →
      j.val < t.val → FollowerCutoffScan.completeRowProposalBit p rate.eta.val row j = false) :
    let M := payload.downRecord i
    let decoded := currentDecodeStep p i row t own rate state
    let cut := referenceDownCut p view i row t own rate state
    let afterDecode := { state with downBatch := decoded.1 }
    ∃ next,
      DeclaredFollowerLocalRound.consumeDownResult rate cut.outcome = .ok next ∧
      localStateDomainValid next ∧ next.S + next.backlog ≤ (t.val + 1) * D p ∧
      next.initializationFailure = state.initializationFailure ∧
      ((¬ downSelected p i row t ∧ cut.outcome = .skipped state .notSelectedDown ∧ next = state) ∨
       (downSelected p i row t ∧ cut.raw = decoded.2 ∧ cut.filteredRaw = none ∧
        cut.outcome = .decodeOrParseRejected state afterDecode decoded.2 ∧
        cut.ordinaryParse = ordinaryParse p rate decoded.2 ∧
        (cut.ordinaryAcceptance ↔ ordinaryLocalAcceptanceTest p rate t state (ordinaryParse p rate decoded.2)) ∧
        (cut.rawComparison = some false ∨ cut.rawComparison = some true ∧ decoded.2 = none) ∧
        next = afterDecode) ∨
       (∃ (ha : OrdinaryMessageCodec.acceptDown (codecParams p rate.eta)
            (acceptedStart state) (t.val + 1) M) (final : ReplayRegisters),
        let scan := acceptedCutoffScan p rate M t (acceptedDownStartLE p rate M t state ha) row
        downSelected p i row t ∧
        decoded.2 = some (CoordinatorLocalArmChoice.storedDownFlatWord payload i) ∧
        cut.raw = decoded.2 ∧ cut.filteredRaw = decoded.2 ∧ cut.rawComparison = some true ∧
        cut.ordinaryParse = some M ∧ cut.ordinaryAcceptance ∧
        scan.endpoint = t.val + 2 ∧
        checkedRecovery p rate M state scan.endpoint = .ok final ∧
        final.registers.1 + final.registers.2 ≤ (t.val + 1) * D p ∧
        replay_register_domain (D p) (p.T * D p) final ∧
        final.registers = QueueReplay.replay (4 * rate.n) (0, M.val.q)
          (recoveryQueueRecords p rate M state scan.endpoint) ∧
        (∀ k, ∃ middle, checkedReplay (D p) (p.T * D p) (4 * rate.n) 0 ⟨(0, M.val.q), 0⟩
          ((recoveryQueueRecords p rate M state scan.endpoint).take k) = .ok middle ∧
          replay_register_domain (D p) (p.T * D p) middle ∧
          middle.registers = QueueReplay.replay (4 * rate.n) (0, M.val.q)
            ((recoveryQueueRecords p rate M state scan.endpoint).take k)) ∧
        next = { afterDecode with
          lastDown := some M
          S := final.registers.1
          delta := final.lastService
          backlog := final.registers.2
          status := .pending
          buffer := [] } ∧
        cut.outcome = .accepted state next decoded.2 M scan final.registers final.lastService)) := by
  classical
  dsimp only
  let M := payload.downRecord i
  let decoded := currentDecodeStep p i row t own rate state
  let afterDecode := { state with downBatch := decoded.1 }
  have hop := operation_input_of_local_domain state hdomain
  have hbatch := (ReferenceFollowerDecoderChronology.currentDecodeStep_batch_spec
    i row t own state hdomain.2.2).1
  have hd : localStateDomainValid afterDecode := ⟨hdomain.1, hdomain.2.1, hbatch⟩
  have hm : state.S + state.backlog ≤ (t.val + 1) * D p :=
    hmass.trans (Nat.mul_le_mul_right (D p) (by omega))
  by_cases hselected : downSelected p i row t
  · by_cases hmatches : decoded.2 = expectedDownFlatWord view i row t
    · dsimp only [decoded] at hmatches
      rcases hexpected with he | he
      · have ho : (referenceDownCut p view i row t own rate state).outcome =
            .decodeOrParseRejected state afterDecode decoded.2 := by
          simp [referenceDownCut, hselected, hstatus, hop.1, hop.2.1, hop.2.2,
            hmatches, he, ordinaryParse, OrdinaryMessageCodec.parseDown, decoded, afterDecode]
          rfl
        refine ⟨afterDecode, ?_, hd, hm, rfl, Or.inr (Or.inl ?_)⟩
        · rw [ho]; rfl
        · refine ⟨hselected, ?_⟩
          simp [referenceDownCut, hselected, hstatus, hop.1, hop.2.1, hop.2.2,
            hmatches, he, ordinaryParse, OrdinaryMessageCodec.parseDown, decoded, afterDecode]
          rfl
      · have hraw : (currentDecodeStep p i row t own rate state).2 =
            some (CoordinatorLocalArmChoice.storedDownFlatWord payload i) := hmatches.trans he
        have hp : ordinaryParse p rate (currentDecodeStep p i row t own rate state).2 = some M := by
          rw [hraw]
          unfold ordinaryParse CoordinatorLocalArmChoice.storedDownFlatWord
          change OrdinaryMessageCodec.parseDown (codecParams p rate.eta)
            (some ((OrdinaryMessageCodec.wordEquivFlat _).symm
              ((OrdinaryMessageCodec.wordEquivFlat _) (payload.downWord i)))) = _
          rw [(OrdinaryMessageCodec.wordEquivFlat _).symm_apply_apply]
          exact payload.parseDown_downWord i
        have ha : OrdinaryMessageCodec.acceptDown (codecParams p rate.eta)
            (acceptedStart state) (t.val + 1) M := ⟨hstrict, hstart⟩
        let scan := acceptedCutoffScan p rate M t (acceptedDownStartLE p rate M t state ha) row
        have hend : scan.endpoint = t.val + 2 := scan_live_endpoint row t M _ hgrid hbits
        obtain ⟨final, hc, hmFinal, hl, hdFinal, hqueue, hprefix⟩ :=
          checked_recovery_of_calendar_credit M state t hdomain.2.1 hstart hcredit
        have hcScan : checkedRecovery p rate M state scan.endpoint = .ok final := by rw [hend]; exact hc
        dsimp only [scan] at hcScan hend
        let next := { afterDecode with
          lastDown := some M
          S := final.registers.1
          delta := final.lastService
          backlog := final.registers.2
          status := .pending
          buffer := [] }
        have hdNext : localStateDomainValid next := by
          refine ⟨hdFinal, ?_, hbatch⟩
          refine ⟨?_, List.nodup_nil, ?_⟩ <;> intro saved hsaved <;> cases hsaved
        have ho : (referenceDownCut p view i row t own rate state).outcome =
            .accepted state next decoded.2 M scan final.registers final.lastService := by
          simp only [referenceDownCut, dite_eq_left hselected, dite_eq_left hstatus,
            dite_eq_left hop.1, dite_eq_left hop.2.1, dite_eq_left hop.2.2,
            dite_eq_left hmatches, hp, dite_eq_left ha, hend, hc, ite_true]
          rfl
        refine ⟨next, ?_, hdNext, hmFinal, rfl, Or.inr (Or.inr ⟨ha, final, ?_⟩)⟩
        · rw [ho]; rfl
        · refine ⟨hselected, hraw, ?_, ?_, ?_, ?_, ?_, hend, hcScan, hmFinal, hdFinal,
            ?_, ?_, rfl, ho⟩
          · simp only [referenceDownCut, dite_eq_left hselected, dite_eq_left hstatus,
              dite_eq_left hop.1, dite_eq_left hop.2.1, dite_eq_left hop.2.2,
              dite_eq_left hmatches]
          · simp only [referenceDownCut, dite_eq_left hselected, dite_eq_left hstatus,
              dite_eq_left hop.1, dite_eq_left hop.2.1, dite_eq_left hop.2.2,
              dite_eq_left hmatches]
          · simp only [referenceDownCut, dite_eq_left hselected, dite_eq_left hstatus,
              dite_eq_left hop.1, dite_eq_left hop.2.1, dite_eq_left hop.2.2,
              dite_eq_left hmatches]
          · simp only [referenceDownCut, dite_eq_left hselected, dite_eq_left hstatus,
              dite_eq_left hop.1, dite_eq_left hop.2.1, dite_eq_left hop.2.2,
              dite_eq_left hmatches, hp]
            rfl
          · simp only [referenceDownCut, dite_eq_left hselected, dite_eq_left hstatus,
              dite_eq_left hop.1, dite_eq_left hop.2.1, dite_eq_left hop.2.2,
              dite_eq_left hmatches, hp, ordinaryLocalAcceptanceTest, ha]
          · rw [hend]; exact hqueue
          · rw [hend]; exact hprefix
    · dsimp only [decoded] at hmatches
      have ho : (referenceDownCut p view i row t own rate state).outcome =
          .decodeOrParseRejected state afterDecode decoded.2 := by
        simp only [referenceDownCut, dite_eq_left hselected, dite_eq_left hstatus,
          dite_eq_left hop.1, dite_eq_left hop.2.1, dite_eq_left hop.2.2,
          dite_eq_right hmatches]
        rfl
      refine ⟨afterDecode, ?_, hd, hm, rfl, Or.inr (Or.inl ?_)⟩
      · rw [ho]; rfl
      · refine ⟨hselected, ?_⟩
        simp only [referenceDownCut, dite_eq_left hselected, dite_eq_left hstatus,
          dite_eq_left hop.1, dite_eq_left hop.2.1, dite_eq_left hop.2.2,
          dite_eq_right hmatches, true_and]
        exact ⟨Or.inl trivial, rfl⟩
  · have ho : (referenceDownCut p view i row t own rate state).outcome =
        .skipped state .notSelectedDown := by
      simp only [referenceDownCut, dite_eq_right hselected]
    refine ⟨state, ?_, hdomain, hm, rfl, Or.inl ⟨hselected, ho, rfl⟩⟩
    rw [ho]; rfl

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


private theorem continuing_clock_facts
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hclock : ReferenceCoordinatorClockDomains.clockAt record.input.rows
      record.input.selected record.input.time.val record.input.state) :
    match record.output.preparation.coordinator with
    | .live r _ _ (.continuingChosen ..) =>
      record.input.time.val + 2 ≤ FollowerCutoffScan.gridBoundary p rate.eta.val r.payload.sigma ∧
        FollowerCutoffScan.completeRowProposalBit p rate.eta.val record.input.row r.time = false ∧
        r.time.val + 1 = record.input.time.val
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
    constructor
    · rw [← hgrid]
      have hn := fun h => hno (Or.inl h)
      omega
    · have hn := fun h => hno (Or.inr h)
      cases hb : FollowerCutoffScan.completeRowProposalBit p rate.eta.val
          record.input.row r.time with
      | false => exact ⟨rfl, hstamp⟩
      | true => exact (hn hb).elim


private theorem continuing_not_birth
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (h : isContinuingChosen r = true) (payload : Payload rate) :
    ¬ ReferenceAssignmentPayloadPersistence.InstallationBirth r payload := by
  cases hc : r.output.preparation.coordinator <;>
    simp only [isContinuingChosen, hc] at h
  all_goals try cases h
  rename_i registers owned base outcome
  cases outcome <;> simp_all only [Bool.false_eq_true, not_false_eq_true,
    ReferenceAssignmentPayloadPersistence.InstallationBirth]

private theorem continuing_payload_frame
    (previous current : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hstate : current.input.state = previous.output.next)
    (hprevious : isContinuingChosen previous = true)
    (hcurrent : isContinuingChosen current = true)
    (left : Selection previous.input) (right : Selection current.input)
    (hleft : previous.output.preparation.coordinator.selection = some left)
    (hright : current.output.preparation.coordinator.selection = some right) :
    right.view.payload = left.view.payload := by
  have hstoredLeft := ReferenceSelectedPayloadChronology.actualSelectedPayload_local_stored_or_birth
    previous left hleft
  have hstoredRight := ReferenceSelectedPayloadChronology.actualSelectedPayload_local_stored_or_birth
    current right hright
  rcases hstoredLeft with hstoredLeft | hb
  swap
  · exact (continuing_not_birth previous hprevious _ hb).elim
  rcases hstoredRight with hstoredRight | hb
  swap
  · exact (continuing_not_birth current hcurrent _ hb).elim
  have he : ReferenceAssignmentPayloadChronology.actualStepRecord previous.input = previous := by
    cases previous with
    | mk input output hout => cases hout; rfl
  have hclass := ReferenceAssignmentPayloadChronology.actualStep_payload_classification previous.input
  rw [← previous.output_eq, he] at hclass
  rw [hstate] at hstoredRight
  rcases hclass with hn | ⟨old, hin, hout⟩ | ⟨fresh, hb, _⟩
  · rw [hn] at hstoredRight; cases hstoredRight
  · exact Option.some.inj (hstoredRight.symm.trans hout) |>.trans
      (Option.some.inj (hin.symm.trans hstoredLeft))
  · exact (continuing_not_birth previous hprevious _ hb).elim

private theorem continuing_selection_clock
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hclock : ReferenceCoordinatorClockDomains.clockAt record.input.rows
      record.input.selected record.input.time.val record.input.state)
    (hcontinuing : isContinuingChosen record = true) :
    ∃ selected : Selection record.input,
      record.output.preparation.coordinator.selection = some selected ∧
      selected.view.payload.sigma.val < record.input.time.val ∧
      CoordinatorLocalArmChoice.assignmentIsLive selected.view.payload selected.view.cutoff record.input.time ∧
      record.input.time.val + 2 ≤ FollowerCutoffScan.gridBoundary p rate.eta.val selected.view.payload.sigma ∧
      ∃ stamp : Fin p.T, stamp.val + 1 = record.input.time.val ∧
        FollowerCutoffScan.completeRowProposalBit p rate.eta.val record.input.row stamp = false := by
  have hf := continuing_clock_facts record hclock
  cases hc : record.output.preparation.coordinator <;>
    simp only [isContinuingChosen, hc] at hcontinuing
  all_goals try cases hcontinuing
  rename_i r q base outcome
  cases outcome <;> simp only at hcontinuing <;> try cases hcontinuing
  rename_i dispatched hstart continuation arm
  rw [hc] at hf
  let selected := ReferenceCoordinatorRecorderCallCorrespondence.selectionOfArm
    record.input r.payload dispatched.startResult record.input.time
    (liveRegistersAt r record.input.time).complementWeights arm rfl
  have hs : record.output.preparation.coordinator.selection = some selected := by
    rw [hc]
    exact ReferenceCoordinatorRecorderCallCorrespondence.selectionAt_eq _ _ _ _ _ _ rfl
  have hframes := ReferenceCoordinatorRecorderCallCorrespondence.actual_call_frames record
  rw [hc] at hframes
  have horigin := dispatch_live_origin record.input
  have hd : dispatch record.input = record.output.preparation.coordinator := by rw [record.output_eq]; rfl
  rw [hd, hc] at horigin
  simp only [ReferenceCoordinatorClockDomains.clockAt, horigin] at hclock
  refine ⟨selected, ?_, hclock.2.2.2.2.2.1, hframes.1, hf.1, r.time, hf.2.2, hf.2.1⟩
  simpa only [hc] using hs

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



private theorem prepare_ordinary_after_actual_start
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (activation : ReferencePrelaunchFollower.Activation p) (time : Fin p.T)
    (active : activation.val ≤ time.val + 1)
    (before : ReferencePrelaunchFollower.State p rate.eta)
    (beforeMemory : ActiveFollowerLifecycle.LocalMemory p)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hstart : ActiveFollowerLifecycle.startRound rate.eta time before beforeMemory =
      .ok (state, memory))
    (hdomain : ActiveFollowerQueueOperation.stateInputDomain state)
    (hzero : state.status = .unoccupied → state.lastDown = none →
      state.S = 0 ∧ state.delta = 0 ∧ state.backlog = 0)
    (hrecord : state.status ≠ .unoccupied → ∃ M, state.lastDown = some M) :
    (DeclaredFollowerLocalRound.prepare rate i row activation time active
      (.ordinary before beforeMemory)).configuration = .ordinary state memory := by
  classical
  have hupAdmissible : OrdinaryMessageCodec.upAdmissible
      (ReferencePrelaunchFollower.codecParams p rate.eta)
      (ActiveFollowerQueueOperation.upOfferFields state) := by
    cases hlast : state.lastDown with
    | some M =>
      simp only [OrdinaryMessageCodec.upAdmissible, ActiveFollowerQueueOperation.upOfferFields,
        ReferencePrelaunchFollower.acceptedStart, hlast]
      exact Or.inr ⟨M.property.1, M.property.2.1, hdomain.1, hdomain.2.1, hdomain.2.2.1⟩
    | none =>
      have hu : state.status = .unoccupied := by
        by_contra h
        obtain ⟨M, hM⟩ := hrecord h
        rw [hlast] at hM
        cases hM
      obtain ⟨hS, hd, hb⟩ := hzero hu hlast
      simp [OrdinaryMessageCodec.upAdmissible, ActiveFollowerQueueOperation.upOfferFields,
        ReferencePrelaunchFollower.acceptedStart, hlast, hS, hd, hb,
        OrdinaryMessageCodec.upPlaceholder]
  have hqueueDomain : ActiveFollowerArmChoice.upStateDomain state :=
    ⟨hdomain.1, hdomain.2.1, hdomain.2.2.1⟩
  by_cases hu : state.status = .unoccupied
  · by_cases hselected : ActiveFollowerQueueOperation.selectedUpRound i row activation time
    · have hslot : PublicDiscreteDraws.slotDraw (row.2 time).1 = PublicDiscreteDraws.upSlot :=
        hselected.2.1
      have hi : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
          (row.2 time).1 = i := hselected.2.2
      let offered : OrdinaryMessageCodec.UpRecord
          (ReferencePrelaunchFollower.codecParams p rate.eta) :=
        ⟨ActiveFollowerQueueOperation.upOfferFields state, hupAdmissible⟩
      have hoff : ActiveFollowerQueueOperation.checkedUpOffer rate.eta i row activation time state =
          .offer offered := by
        simp [ActiveFollowerQueueOperation.checkedUpOffer, hdomain, hselected, hu,
          hupAdmissible, offered]
      have hmatch : ActiveFollowerArmChoice.offeredUpMatchesState state offered :=
        ⟨rfl, rfl, rfl, rfl⟩
      have hchoice := ActiveFollowerArmChoice.followerArmChoiceCore_unoccupied_selected_up
        state (row.2 time) i offered hu hslot hi ⟨hqueueDomain, hmatch⟩
      simp only [DeclaredFollowerLocalRound.prepare, hstart, hoff,
        ActiveFollowerArmChoice.followerArmChoice, hchoice]
    · have hnot : ¬ (ActiveFollowerQueueOperation.selectedUpRound i row activation time ∧
          state.status = .unoccupied) := fun h => hselected h.1
      have hoff := ActiveFollowerQueueOperation.checkedUpOffer_noOffer rate.eta i row
        activation time state hdomain hnot
      have hnotUp : ¬ (PublicDiscreteDraws.slotDraw (row.2 time).1 =
          PublicDiscreteDraws.upSlot ∧
          PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
            (row.2 time).1 = i) := by
        intro h
        exact hselected ⟨active, h.1, h.2⟩
      by_cases hdata : PublicDiscreteDraws.slotDraw (row.2 time).1 =
          PublicDiscreteDraws.dataSlot
      · have hchoice := ActiveFollowerArmChoice.followerArmChoiceCore_unoccupied_data
          state (row.2 time) i none hu hdata
        simp only [DeclaredFollowerLocalRound.prepare, hstart, hoff,
          ActiveFollowerArmChoice.followerArmChoice, hchoice]
      · have hchoice := ActiveFollowerArmChoice.followerArmChoiceCore_unoccupied_other
          state (row.2 time) i none hu hdata hnotUp
        simp only [DeclaredFollowerLocalRound.prepare, hstart, hoff,
          ActiveFollowerArmChoice.followerArmChoice, hchoice]
  · have hnot : ¬ (ActiveFollowerQueueOperation.selectedUpRound i row activation time ∧
        state.status = .unoccupied) := fun h => hu h.2
    have hoff := ActiveFollowerQueueOperation.checkedUpOffer_noOffer rate.eta i row
      activation time state hdomain hnot
    have hchoice : ∃ arm, ActiveFollowerArmChoice.followerArmChoiceCore state
        (row.2 time) i none = some arm := by
      obtain ⟨M, hM⟩ := hrecord hu
      simp only [ActiveFollowerArmChoice.followerArmChoiceCore, ite_eq_right hu, hM]
      split
      · exact ⟨_, rfl⟩
      · split
        · exact ⟨_, rfl⟩
        · split <;> exact ⟨_, rfl⟩
    obtain ⟨arm, hchoice⟩ := hchoice
    have hchoice' : ActiveFollowerArmChoice.followerArmChoice state row time i none =
        some arm := by
      simpa [ActiveFollowerArmChoice.followerArmChoice] using hchoice
    simp only [DeclaredFollowerLocalRound.prepare, hstart, hoff]
    rw [hchoice']

/-- Every member of the computed continuing slice uses the whole installed
payload and original row. Its prior proposal coordinates are false and its
current scan endpoint is before the clipped grid. Empty tails remain empty;
the theorem asserts no survival or occurrence of a continuing record. -/
theorem complete_first_replacement_continuing_geometry
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
        installed.registers.payload.sigma.val = birth.input.time.val ∧
        ∀ k : Fin (continuingTail R v).length,
          let r := (continuingTail R v).get k
          R[v + 1 + k.val]? = some r ∧
          r.input.time.val = birth.input.time.val + 1 + k.val ∧
          r.input.rows = source.1.2 ∧
          r.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p source ∧
          r.input.rewards = rewards ∧
          ∃ selected : Selection r.input,
            r.output.preparation.coordinator.selection = some selected ∧
            selected.view.payload = installed.registers.payload ∧
            CoordinatorLocalArmChoice.assignmentIsLive selected.view.payload selected.view.cutoff r.input.time ∧
            r.input.time.val + 2 ≤ FollowerCutoffScan.gridBoundary p rate.eta.val installed.registers.payload.sigma ∧
            (∀ j : Fin p.T, installed.registers.payload.sigma.val ≤ j.val → j.val < r.input.time.val →
              FollowerCutoffScan.completeRowProposalBit p rate.eta.val r.input.row j = false)
      | _ => True := by
  classical
  have hfirst := complete_first_replacement_next_continuing_readout rate source rewards C_star C_h
  dsimp only at hfirst ⊢
  set R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
  set w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
  set v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
  cases hb : R[v]? with
  | none => trivial
  | some birth =>
    simp only [hb] at hfirst ⊢
    cases hc : birth.output.preparation.coordinator with
    | first _ => trivial
    | live _ _ _ _ => trivial
    | dagger => trivial
    | invalidCollectionCutoff => trivial
    | collection old ledger clock cutoff outcome =>
      rw [hc] at hfirst
      cases outcome <;> try trivial
      rename_i core consistent started hs instruction hi output hcons clockData installed arm
      dsimp only at hfirst
      have hbirth := ReferenceLaterInstallationProvenance.record_laterChosen_birth birth
      rw [hc] at hbirth
      simp only [ReferenceAssignmentPayloadPersistence.InstallationBirth, hc] at hbirth
      have htime : installed.registers.payload.sigma.val = birth.input.time.val := hbirth.2
      refine ⟨htime, ?_⟩
      have hfieldBirth := complete_record_fields rate source rewards C_star C_h
        ⟨v, (List.getElem?_eq_some_iff.mp hb).1⟩
      have hgetBirth : R.get ⟨v, (List.getElem?_eq_some_iff.mp hb).1⟩ = birth :=
        (List.getElem?_eq_some_iff.mp hb).2
      rw [hgetBirth] at hfieldBirth
      dsimp only at hfieldBirth
      suffices hall : ∀ n (hn : n < (continuingTail R v).length),
          let r := (continuingTail R v).get ⟨n, hn⟩
          ∃ selected : Selection r.input,
            r.output.preparation.coordinator.selection = some selected ∧
            selected.view.payload = installed.registers.payload ∧
            CoordinatorLocalArmChoice.assignmentIsLive selected.view.payload selected.view.cutoff r.input.time ∧
            r.input.time.val + 2 ≤ FollowerCutoffScan.gridBoundary p rate.eta.val installed.registers.payload.sigma ∧
            (∀ j : Fin p.T, installed.registers.payload.sigma.val ≤ j.val → j.val < r.input.time.val →
              FollowerCutoffScan.completeRowProposalBit p rate.eta.val r.input.row j = false) by
        intro k
        have hg := continuingTail_get R v k
        have hget : R.get ⟨v + 1 + k.val, (List.getElem?_eq_some_iff.mp hg).1⟩ =
            (continuingTail R v).get k := (List.getElem?_eq_some_iff.mp hg).2
        have hf := complete_record_fields rate source rewards C_star C_h
          ⟨v + 1 + k.val, (List.getElem?_eq_some_iff.mp hg).1⟩
        rw [hget] at hf
        dsimp only at hf
        exact ⟨hg, by omega, hf.2.1, hf.2.2.1, hf.2.2.2, hall k.val k.isLt⟩
      intro n
      induction n with
      | zero =>
        intro hn
        let r := (continuingTail R v).get ⟨0, hn⟩
        have hg := continuingTail_get R v ⟨0, hn⟩
        simp only [Nat.add_zero] at hg
        have hget : R.get ⟨v + 1, (List.getElem?_eq_some_iff.mp hg).1⟩ = r :=
          (List.getElem?_eq_some_iff.mp hg).2
        have hclock := complete_suffix_record_clock rate source rewards C_star C_h
          ⟨v + 1, (List.getElem?_eq_some_iff.mp hg).1⟩
        rw [hget] at hclock
        have hcont : isContinuingChosen r = true := continuingTail_mem R v r (List.get_mem ..)
        obtain ⟨selected, hsel, hstarted, hlive, hgrid, stamp, hstamp, hbit⟩ :=
          continuing_selection_clock r hclock hcont
        have hp : selected.view.payload = installed.registers.payload := by
          have hhead := hfirst
          rw [hg] at hhead
          dsimp only at hhead
          cases hcut : r.output.preparation.coordinator <;>
            simp only [isContinuingChosen, hcut] at hcont
          all_goals try cases hcont
          rename_i registers owned base result
          cases result <;> simp only at hcont <;> try cases hcont
          rw [hcut] at hhead
          obtain ⟨other, ho, hp, _⟩ := hhead
          have he : selected = other := Option.some.inj (hsel.symm.trans (by simpa only [hcut] using ho))
          rw [he]; exact hp
        have hf := complete_record_fields rate source rewards C_star C_h
          ⟨v + 1, (List.getElem?_eq_some_iff.mp hg).1⟩
        rw [hget] at hf
        dsimp only at hf
        refine ⟨selected, hsel, hp, hlive, by simpa only [hp] using hgrid, ?_⟩
        intro j hj ht
        have he : j = stamp := Fin.ext (by dsimp only [r] at *; omega)
        rw [he]; exact hbit
      | succ n ih =>
        intro hn
        have hn0 : n < (continuingTail R v).length := by omega
        let previous := (continuingTail R v).get ⟨n, hn0⟩
        let current := (continuingTail R v).get ⟨n + 1, hn⟩
        obtain ⟨left, hleft, hpayLeft, hliveLeft, hgridLeft, hbitsLeft⟩ := ih hn0
        have hg0 := continuingTail_get R v ⟨n, hn0⟩
        have hg1 := continuingTail_get R v ⟨n + 1, hn⟩
        have hget0 : R.get ⟨v + 1 + n, (List.getElem?_eq_some_iff.mp hg0).1⟩ = previous :=
          (List.getElem?_eq_some_iff.mp hg0).2
        have hget1 : R.get ⟨v + 1 + (n + 1), (List.getElem?_eq_some_iff.mp hg1).1⟩ = current :=
          (List.getElem?_eq_some_iff.mp hg1).2
        have hk1 := (List.getElem?_eq_some_iff.mp hg1).1
        change v + 1 + (n + 1) < R.length at hk1
        have hclock := complete_suffix_record_clock rate source rewards C_star C_h
          ⟨v + 1 + (n + 1), hk1⟩
        rw [hget1] at hclock
        have hc1 : isContinuingChosen current = true := continuingTail_mem R v current (List.get_mem ..)
        obtain ⟨right, hright, hstarted, hlive, hgrid, stamp, hstamp, hbit⟩ :=
          continuing_selection_clock current hclock hc1
        have hadj := complete_adjacent rate source rewards C_star C_h (v + 1 + n) (by omega)
        dsimp only at hadj
        have hget1' : R.get ⟨v + 1 + n + 1, by omega⟩ = current := by
          have he : (⟨v + 1 + n + 1, by omega⟩ : Fin R.length) =
              ⟨v + 1 + (n + 1), hk1⟩ := Fin.ext (Nat.add_assoc _ _ _)
          rw [he]; exact hget1
        rw [hget0, hget1'] at hadj
        change current.input.state = previous.output.next ∧
          current.input.time.val = previous.input.time.val + 1 at hadj
        have hpay : right.view.payload = installed.registers.payload :=
          (continuing_payload_frame previous current hadj.1
            (continuingTail_mem R v previous (List.get_mem ..)) hc1 left right hleft hright).trans hpayLeft
        have hf0 := complete_record_fields rate source rewards C_star C_h
          ⟨v + 1 + n, (List.getElem?_eq_some_iff.mp hg0).1⟩
        have hf1 := complete_record_fields rate source rewards C_star C_h
          ⟨v + 1 + (n + 1), hk1⟩
        rw [hget0] at hf0
        rw [hget1] at hf1
        have hrow : current.input.row = previous.input.row := by
          change current.input.rows current.input.selected = previous.input.rows previous.input.selected
          rw [hf0.2.1, hf1.2.1, hf0.2.2.1, hf1.2.2.1]
        refine ⟨right, hright, hpay, hlive, by simpa only [hpay] using hgrid, ?_⟩
        intro j hj ht
        change j.val < current.input.time.val at ht
        by_cases hprior : j.val < previous.input.time.val
        · rw [hrow]; exact hbitsLeft j hj hprior
        · have he : j = stamp := Fin.ext (by omega)
          rw [he]; exact hbit

/-- Conditional one-record unoccupied preservation. Every logical input is
displayed: actual PREPARE, local domain/mass/chronology, strict accepted start,
installed queue credit and the uninterrupted interval. The receiver and its
checked recovery are evaluated inside the proof, never supplied as laws. -/
theorem unoccupied_actual_follower_finish
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (payload : Payload rate) (selected : Selection record.input)
    (hselection : record.output.preparation.coordinator.selection = some selected)
    (hpayload : selected.view.payload = payload)
    (i : Fin (p.m - 1)) (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : LocalMemory p)
    (hprepared : (record.output.preparation.followers.followers i).configuration = .ordinary state memory)
    (hstatus : state.status = .unoccupied) (hdomain : localStateDomainValid state)
    (hmass : state.S + state.backlog ≤ record.input.time.val * D p)
    (hpair : state.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound))
    (htime : ∀ saved ∈ state.buffer, saved.calendarRound < record.input.time.val + 1)
    (hstart : (payload.downRecord i).val.sigma ≤ record.input.time.val + 1)
    (hstrict : acceptedStart state < (payload.downRecord i).val.sigma)
    (hcredit : (payload.downRecord i).val.q ≤ ((payload.downRecord i).val.sigma - 1) * D p)
    (hgrid : record.input.time.val + 2 ≤ FollowerCutoffScan.gridBoundary p rate.eta.val payload.sigma)
    (hbits : ∀ j : Fin p.T, payload.sigma.val ≤ j.val → j.val < record.input.time.val →
      FollowerCutoffScan.completeRowProposalBit p rate.eta.val record.input.row j = false) :
    let own := record.output.preparation.feedback.observations (followerPlayer p.two_le_m i)
    ∃ logged next,
      ActiveFollowerLogging.checkedLogging i record.input.row (record.input.state.activations i)
        record.input.time ((record.output.preparation.followers.followers i).arm, own) state = .ok logged ∧
      logged.buffer = state.buffer ++ ReferenceFollowerBufferProvenance.logEmission i record ∧
      logged.lastDown = state.lastDown ∧
      localStateDomainValid logged ∧
      logged.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound) ∧
      (∀ saved ∈ logged.buffer, saved.calendarRound ≤ record.input.time.val + 1) ∧
      acceptedStart logged < (payload.downRecord i).val.sigma ∧
      (let cut := referenceDownCut p record.output.preparation.coordinator.downView
          i record.input.row record.input.time own rate logged
       let nextMemory : LocalMemory p := if next.status = .unoccupied then memory else
          ⟨some ⟨record.input.time, FollowerCutoffScan.completeRowProposalBit
            p rate.eta.val record.input.row record.input.time⟩⟩
       DeclaredFollowerLocalRound.consumeDownResult rate cut.outcome = .ok next ∧
       DeclaredFollowerLocalRound.releaseAndFinish rate i record.input.row record.input.time
         own state memory next = .ok (next, nextMemory) ∧
       record.output.followers i = ⟨.ordinary next nextMemory, none, some logged, some cut⟩ ∧
       localStateDomainValid next ∧ next.S + next.backlog ≤ (record.input.time.val + 1) * D p ∧
       next.delta ≤ D p ∧ next.initializationFailure = state.initializationFailure ∧
       ((next.status = .unoccupied ∧ next.lastDown = state.lastDown ∧
          next.S = state.S ∧ next.delta = state.delta ∧ next.backlog = state.backlog ∧
          next.buffer = logged.buffer) ∨
        (next.status = .pending ∧ next.lastDown = some (payload.downRecord i) ∧ next.buffer = []))) := by
  classical
  dsimp only
  let own := ((record.output.preparation.followers.followers i).arm,
    record.output.preparation.feedback.observations (followerPlayer p.two_le_m i))
  obtain ⟨logged, hlogging, hbuffer, hlogStatus, hlogFlag, hlogValid⟩ :=
    ActiveFollowerLogging.checkedLogging_success_of_chronological i record.input.row
      (record.input.state.activations i) record.input.time own state hdomain.2.1 htime hstatus
  have hframe := ActiveFollowerLogging.checkedLogging_success_frame i record.input.row
    (record.input.state.activations i) record.input.time own state logged hlogging
  have hlogDomain : localStateDomainValid logged := by
    refine ⟨⟨hframe.2.1 ▸ hdomain.1.1, hframe.2.2.1 ▸ hdomain.1.2.1,
      hframe.2.2.2.1 ▸ hdomain.1.2.2⟩, hlogValid, ?_⟩
    unfold downDecoderStateValid
    rw [hframe.2.2.2.2.2.1]; exact hdomain.2.2
  have hem : ReferenceFollowerBufferProvenance.logEmission i record =
      logAt i record.input.row (record.input.state.activations i) record.input.time own := by
    simp only [ReferenceFollowerBufferProvenance.logEmission, hprepared, hstatus, dite_true]
    rw [ReferenceFollowerBufferProvenance.round_ownEntry_eq_prepared]
  have hp : logged.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound) := by
    rw [hbuffer, ← hem, List.pairwise_append]
    refine ⟨hpair, ReferenceFollowerBufferProvenance.logEmission_pairwise i record, ?_⟩
    intro a ha b hb
    have := htime a ha
    have := ReferenceFollowerBufferProvenance.logEmission_source_timestamp i record b hb
    omega
  have ht : ∀ saved ∈ logged.buffer, saved.calendarRound ≤ record.input.time.val + 1 := by
    rw [hbuffer, ← hem]
    intro saved hsaved
    rcases List.mem_append.mp hsaved with h | h
    · exact Nat.le_of_lt (htime saved h)
    · exact Nat.le_of_eq (ReferenceFollowerBufferProvenance.logEmission_source_timestamp i record saved h)
  have hstrictLog : acceptedStart logged < (payload.downRecord i).val.sigma := by
    simpa only [acceptedStart, hframe.1] using hstrict
  have hcoord : downStart p rate (payload.downRecord i) = payload.sigma := by
    apply Fin.ext
    change payload.sigma.val + 1 - 1 = payload.sigma.val
    exact Nat.add_sub_cancel _ _
  have hv : record.output.preparation.coordinator.downView = some selected.view := by
    simp only [DispatchCut.downView, hselection, Option.map_some]
  have hexpected : expectedDownFlatWord record.output.preparation.coordinator.downView i
      record.input.row record.input.time = none ∨
      expectedDownFlatWord record.output.preparation.coordinator.downView i record.input.row record.input.time =
        some (CoordinatorLocalArmChoice.storedDownFlatWord payload i) := by
    rw [hv]
    by_cases hbranch : CoordinatorLocalArmChoice.coordinatorArmChoice selected.view.payload
        selected.view.pendingAtChoice selected.view.cutoff record.input.time
        selected.view.complementWeights record.input.row ≠ none ∧
        selectedDownSenderBranch selected.view i record.input.row record.input.time
    · right
      change (if _ then _ else _) = _
      rw [ite_eq_left hbranch, hpayload]
      rfl
    · left
      change (if _ then _ else _) = _
      exact ite_eq_right hbranch
  obtain ⟨next, hconsume, hdNext, hmNext, hflagNext, hcases⟩ := down_cut_live
    record.output.preparation.coordinator.downView payload i record.input.row record.input.time own.2
    logged hlogDomain (hlogStatus.trans hstatus) hstart hstrictLog hcredit
    (by rw [hframe.2.1, hframe.2.2.2.1]; exact hmass) hexpected
    (by rw [hcoord]; exact hgrid) (by rw [hcoord]; exact hbits)
  have hshape : (next.status = .unoccupied ∧ next.lastDown = state.lastDown ∧
      next.S = state.S ∧ next.delta = state.delta ∧ next.backlog = state.backlog ∧
      next.buffer = logged.buffer) ∨
      (next.status = .pending ∧ next.lastDown = some (payload.downRecord i) ∧ next.buffer = []) := by
    rcases hcases with hskip | hrejected | haccepted
    · rw [hskip.2.2]
      exact Or.inl ⟨hlogStatus.trans hstatus, hframe.1, hframe.2.1, hframe.2.2.1, hframe.2.2.2.1, rfl⟩
    · rw [hrejected.2.2.2.2.2.2.2]
      exact Or.inl ⟨hlogStatus.trans hstatus, hframe.1, hframe.2.1, hframe.2.2.1, hframe.2.2.2.1, rfl⟩
    · obtain ⟨ha, final, hc⟩ := haccepted
      dsimp only at hc
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, he, _⟩ := hc
      rw [he]
      exact Or.inr ⟨rfl, rfl, rfl⟩
  have hcompatible : next.status ≠ .unoccupied → ∃ M,
      next.lastDown = some M ∧ M.val.sigma ≤ record.input.time.val + 1 := by
    intro hbusy
    rcases hshape with hu | hb
    · exact (hbusy hu.1).elim
    · exact ⟨payload.downRecord i, hb.2.1, hstart⟩
  have hf := finish_actual record i state logged next memory hprepared hstatus hlogging
    hconsume hdNext hmNext (hflagNext.trans hlogFlag) hcompatible
  dsimp only at hf
  exact ⟨logged, next, hlogging, by rw [hem]; exact hbuffer, hframe.1, hlogDomain, hp, ht, hstrictLog,
    hf.1, hf.2.2.2.1, hf.2.2.2.2.1, hf.2.2.2.2.2.1, hf.2.2.2.2.2.2.1,
    hf.2.2.2.2.2.2.2.1, hf.2.2.2.2.2.2.2.2, hshape⟩

/-- Any ordinary incoming follower in the actual complete suffix has its
original valid chronological buffer, with timestamps strictly in the past. -/
theorem complete_input_buffer_chronological
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h).length)
    (i : Fin (p.m - 1)) (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : LocalMemory p)
    (hinput : ((ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).get k).input.state.followers i = .ordinary state memory) :
    localBufferValid state ∧
    state.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound) ∧
    ∀ saved ∈ state.buffer, saved.calendarRound <
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h).get k).input.time.val + 1 := by
  obtain ⟨hc, hspan, hr⟩ := ReferenceLaterLiveNumericalReadout.source_record_prefix
    rate rewards C_star C_h source k
  rw [hr] at hinput ⊢
  let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed rate source rewards C_star C_h hc
  dsimp only [ReferenceCompletePhysicalHistory.physicalStart,
    ReferenceCompletePhysicalHistory.generatedBoundary, ReferenceCompletePhysicalHistory.generatedInput] at hspan
  exact ReferenceFollowerBufferProvenance.run_buffer_chronological i _ source.1.2 _ rewards _
    k.val (by omega) seed.activeAtStart (seed.followers i) (seed.memory i)
    (seed.configuration i) (seed.bufferValid i) (seed.chronologicalBuffer i) (seed.bufferStamps i)
    state memory hinput

private theorem release_finish_occupied
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
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

/-- Conditional preservation at one actual continuing record. The local input
domains, mass, old-start/occupied-token alternatives, chronology, installed
queue credit and public interval facts are all explicit. Neither source-run
ordinariness nor these boundary fields are established by this helper. -/
theorem local_follower_step_of_boundary
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (payload : Payload rate) (selected : Selection record.input)
    (hselection : record.output.preparation.coordinator.selection = some selected)
    (hpayload : selected.view.payload = payload)
    (i : Fin (p.m - 1)) (state : ReferencePrelaunchFollower.State p rate.eta) (memory : LocalMemory p)
    (hinput : record.input.state.followers i = .ordinary state memory)
    (hdomain : localStateDomainValid state)
    (hmass : state.S + state.backlog ≤ record.input.time.val * D p)
    (hzero : state.lastDown = none → state.S = 0 ∧ state.delta = 0 ∧ state.backlog = 0)
    (hstrict : state.status = .unoccupied → acceptedStart state < (payload.downRecord i).val.sigma)
    (hbusy : state.status ≠ .unoccupied → state.lastDown = some (payload.downRecord i) ∧
      ∃ token, memory.lastProposalRead = some token ∧ token.timestamp.val + 1 = record.input.time.val ∧
        token.bit = FollowerCutoffScan.completeRowProposalBit p rate.eta.val record.input.row token.timestamp)
    (hpair : state.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound))
    (htime : ∀ saved ∈ state.buffer, saved.calendarRound < record.input.time.val + 1)
    (hstart : (payload.downRecord i).val.sigma ≤ record.input.time.val)
    (hcredit : (payload.downRecord i).val.q ≤ ((payload.downRecord i).val.sigma - 1) * D p)
    (hgrid : record.input.time.val + 2 ≤ FollowerCutoffScan.gridBoundary p rate.eta.val payload.sigma)
    (hbits : ∀ j : Fin p.T, payload.sigma.val ≤ j.val → j.val < record.input.time.val →
      FollowerCutoffScan.completeRowProposalBit p rate.eta.val record.input.row j = false) :
    ∃ next nextMemory,
      interruptionDecision rate.eta record.input.time state memory = .ok false ∧
      (record.output.preparation.followers.followers i).configuration = .ordinary state memory ∧
      (record.output.followers i).configuration = .ordinary next nextMemory ∧
      (record.output.followers i).failure = none ∧
      next.initializationFailure = state.initializationFailure ∧
      localStateDomainValid next ∧ next.S + next.backlog ≤ (record.input.time.val + 1) * D p ∧
      (next.lastDown = none → next.S = 0 ∧ next.delta = 0 ∧ next.backlog = 0) ∧
      (next.status = .unoccupied → acceptedStart next < (payload.downRecord i).val.sigma) ∧
      (next.status ≠ .unoccupied → next.lastDown = some (payload.downRecord i) ∧
        ∃ token, nextMemory.lastProposalRead = some token ∧
          token.timestamp.val + 1 = record.input.time.val + 1 ∧
          token.bit = FollowerCutoffScan.completeRowProposalBit p rate.eta.val record.input.row token.timestamp) := by
  classical
  have hcoord : acceptedStartCoordinate (payload.downRecord i) = payload.sigma := by
    apply Fin.ext
    change payload.sigma.val + 1 - 1 = payload.sigma.val
    exact Nat.add_sub_cancel _ _
  have hdecision : interruptionDecision rate.eta record.input.time state memory = .ok false := by
    by_cases hu : state.status = .unoccupied
    · exact interruptionDecision_unoccupied rate.eta record.input.time state memory hdomain hu
    · obtain ⟨hdown, token, hread, hstamp, hbit⟩ := hbusy hu
      have hfalse : token.bit = false := by
        rw [hbit]
        have hstart' : payload.sigma.val + 1 ≤ record.input.time.val := hstart
        apply hbits token.timestamp <;> omega
      have hbound : record.input.time.val + 1 ≤ FollowerCutoffScan.gridBoundary p rate.eta.val payload.sigma := by omega
      have hne : FollowerCutoffScan.gridBoundary p rate.eta.val payload.sigma ≠ record.input.time.val + 1 := by omega
      simp only [interruptionDecision, dite_eq_left hdomain, dite_eq_right hu, hdown, dite_eq_left hstart]
      rw [hcoord, dite_eq_left hbound, hread]
      simp only [hstamp, decide_eq_false hne, hfalse, Bool.false_or, dite_true]
  have hstartRound : startRound rate.eta record.input.time state memory = .ok (state, memory) := by
    rw [startRound, hdecision]
    rfl
  have hprepared : (record.output.preparation.followers.followers i).configuration = .ordinary state memory := by
    rw [record.output.preparation.followers.followers_eq i]
    change (DeclaredFollowerLocalRound.prepare rate i record.input.row (record.input.state.activations i)
      record.input.time (record.input.active i) (record.input.state.followers i)).configuration = _
    rw [hinput]
    exact prepare_ordinary_after_actual_start i record.input.row (record.input.state.activations i)
      record.input.time (record.input.active i) state memory state memory hstartRound
      ⟨hdomain.1.1, hdomain.1.2.1, hdomain.1.2.2, hdomain.2.1.1, hdomain.2.1.2.1⟩
      (fun _ hn => hzero hn) (fun hu => ⟨payload.downRecord i, (hbusy hu).1⟩)
  by_cases hu : state.status = .unoccupied
  · obtain ⟨logged, next, hlogging, hbuffer, hlast, hdLog, hpLog, htLog, hsLog, hf⟩ :=
      unoccupied_actual_follower_finish record payload selected hselection hpayload i state memory
        hprepared hu hdomain hmass hpair htime (by omega) (hstrict hu) hcredit hgrid hbits
    dsimp only at hf
    obtain ⟨hconsume, htail, hout, hdNext, hmNext, hdelta, hflag, hshape⟩ := hf
    let nextMemory : LocalMemory p := if next.status = .unoccupied then memory else
      ⟨some ⟨record.input.time, FollowerCutoffScan.completeRowProposalBit p rate.eta.val record.input.row record.input.time⟩⟩
    refine ⟨next, nextMemory, hdecision, hprepared, ?_, ?_, hflag, hdNext, hmNext, ?_, ?_, ?_⟩
    · rw [hout]
    · rw [hout]
    · intro hn
      rcases hshape with hret | hacc
      · have hz := hzero (hret.2.1.symm.trans hn)
        exact ⟨hret.2.2.1.trans hz.1, hret.2.2.2.1.trans hz.2.1, hret.2.2.2.2.1.trans hz.2.2⟩
      · rw [hacc.2.1] at hn; cases hn
    · intro hn
      rcases hshape with hret | hacc
      · simpa only [acceptedStart, hret.2.1] using hstrict hu
      · rw [hacc.1] at hn; cases hn
    · intro hn
      rcases hshape with hret | hacc
      · exact (hn hret.1).elim
      · exact ⟨hacc.2.1, ⟨record.input.time, FollowerCutoffScan.completeRowProposalBit
            p rate.eta.val record.input.row record.input.time⟩,
          by simp only [nextMemory, ite_eq_right hn], rfl, rfl⟩
  · obtain ⟨serviced, next, hservice, hrecord, htail, hout, hdNext, hmNext, hdelta,
      hdown, hbatch, hbuffer, hflag⟩ := occupied_actual_follower_finish record i state memory
      hprepared hu hdomain (payload.downRecord i) (hbusy hu).1 hstart hmass
    have hpost : serviced.output.status ≠ .unoccupied := by
      rw [serviced.queueUpdate]
      unfold ActiveFollowerQueueOperation.serviceOutput
      split <;> exact hu
    let nextMemory : LocalMemory p := ⟨some ⟨record.input.time,
      FollowerCutoffScan.completeRowProposalBit p rate.eta.val record.input.row record.input.time⟩⟩
    have hn := release_finish_occupied record i state serviced.output next memory nextMemory hpost htail
    refine ⟨next, nextMemory, hdecision, hprepared, ?_, ?_, hflag, hdNext, hmNext, ?_, ?_, ?_⟩
    · rw [hout]
    · rw [hout]
    · intro hnone; rw [hdown, (hbusy hu).1] at hnone; cases hnone
    · exact fun h => (hn h).elim
    · intro _
      exact ⟨hdown.trans (hbusy hu).1, ⟨record.input.time,
        FollowerCutoffScan.completeRowProposalBit p rate.eta.val record.input.row record.input.time⟩,
        rfl, rfl, rfl⟩

/-- On every retained original record, an actual DOWN diagnostic has an
actual successfully logged input. Its arbitrary-length replay from the NEW
installed queue passes all arithmetic guards. This proves guard budgets from
the original source, not acceptance, ordinary PREPARE, or follower survival.
Absent diagnostics remain an explicit alternative. -/
theorem complete_first_replacement_logged_recovery_budgets
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
          ∀ i : Fin (p.m - 1),
          let M := installed.registers.payload.downRecord i
          match (r.output.followers i).down with
          | none => True
          | some cut =>
            ∃ state memory logged,
              (r.output.preparation.followers.followers i).configuration = .ordinary state memory ∧
              state.status = .unoccupied ∧
              ActiveFollowerLogging.checkedLogging i r.input.row (r.input.state.activations i)
                r.input.time ((r.output.preparation.followers.followers i).arm,
                  r.output.preparation.feedback.observations (followerPlayer p.two_le_m i)) state = .ok logged ∧
              (r.output.followers i).downInput = some logged ∧
              cut = referenceDownCut p r.output.preparation.coordinator.downView i r.input.row
                r.input.time (r.output.preparation.feedback.observations (followerPlayer p.two_le_m i)) rate logged ∧
              localBufferValid logged ∧
              M.val.sigma = installed.registers.payload.sigma.val + 1 ∧
              M.val.q ≤ (M.val.sigma - 1) * D p ∧
              ∃ final, checkedRecovery p rate M logged (r.input.time.val + 2) = .ok final ∧
                final.registers.1 + final.registers.2 ≤ (r.input.time.val + 1) * D p ∧
                replay_register_domain (D p) (p.T * D p) final ∧
                final.registers = QueueReplay.replay (4 * rate.n) (0, M.val.q)
                  (recoveryQueueRecords p rate M logged (r.input.time.val + 2)) ∧
                (∀ j, ∃ middle,
                  checkedReplay (D p) (p.T * D p) (4 * rate.n) 0 ⟨(0, M.val.q), 0⟩
                    ((recoveryQueueRecords p rate M logged (r.input.time.val + 2)).take j) = .ok middle ∧
                  replay_register_domain (D p) (p.T * D p) middle ∧
                  middle.registers = QueueReplay.replay (4 * rate.n) (0, M.val.q)
                    ((recoveryQueueRecords p rate M logged (r.input.time.val + 2)).take j))
      | _ => True := by
  classical
  have hgeometry := complete_first_replacement_continuing_geometry rate source rewards C_star C_h
  have hbirth := ReferenceFirstReplacementDownRecovery.complete_first_replacement_down_recovery_and_finish
    rate source rewards C_star C_h
  dsimp only at hgeometry hbirth ⊢
  set R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
  set w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
  set v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
  cases hb : R[v]? with
  | none => trivial
  | some birth =>
    simp only [hb] at hgeometry hbirth ⊢
    cases hc : birth.output.preparation.coordinator with
    | first _ => trivial
    | live _ _ _ _ => trivial
    | dagger => trivial
    | invalidCollectionCutoff => trivial
    | collection old ledger clock cutoff outcome =>
      rw [hc] at hgeometry hbirth
      cases outcome <;> try trivial
      rename_i core consistent started hs instruction hi output hcons clockData installed arm
      dsimp only at hgeometry hbirth ⊢
      intro k i
      let r := (continuingTail R v).get k
      cases hdown : (r.output.followers i).down with
      | none => trivial
      | some cut =>
        obtain ⟨state, memory, logged, hprepared, hstatus, hlogging, hinput, hcut⟩ :=
          ReferenceFollowerSparseEmissionRecovery.actualDownDiagnostic_choice r i cut hdown
        have halign := r.output.preparation.follower_alignment i
        simp only [halign.1, halign.2.1, halign.2.2.1, halign.2.2.2] at hlogging hcut
        have hvalid := (ActiveFollowerLogging.checkedLogging_success_iff i r.input.row
          (r.input.state.activations i) r.input.time _ state logged).mp hlogging |>.2.2
        obtain ⟨_, _, _, _, _, _, _, _, _, hsigma, hcredit, _⟩ := hbirth.2 i
        have hM : (installed.registers.payload.downRecord i).val.sigma =
            installed.registers.payload.sigma.val + 1 := rfl
        have hg := hgeometry.2 k
        have hstart : (installed.registers.payload.downRecord i).val.sigma ≤ r.input.time.val + 1 := by
          rw [hsigma]
          have ht := hg.2.1
          change r.input.time.val = birth.input.time.val + 1 + k.val at ht
          omega
        have hcredit' : (installed.registers.payload.downRecord i).val.q ≤
            ((installed.registers.payload.downRecord i).val.sigma - 1) * D p := by
          rw [hsigma, Nat.add_sub_cancel]
          exact hcredit
        obtain ⟨final, hchecked, hmass, hlast, hdomain, hqueue, hprefix⟩ :=
          checked_recovery_of_calendar_credit (installed.registers.payload.downRecord i)
            logged r.input.time hvalid hstart hcredit'
        exact ⟨state, memory, logged, hprepared, hstatus, hlogging, hinput, hcut, hvalid,
          hM, hcredit', final, hchecked, hmass, hdomain, hqueue, hprefix⟩

end Bandits.Support.ReferenceFirstReplacementLiveFollowerPrefix
end
