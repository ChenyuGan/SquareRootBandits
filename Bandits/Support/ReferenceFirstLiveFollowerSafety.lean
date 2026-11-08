/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveCoordinatorSafety
public import Bandits.Support.ReferenceFirstDownZeroRecovery
public import Bandits.Support.ReferenceFirstComplementReplay

import Lean.Elab.Tactic.Omega
import Mathlib.Data.List.TakeWhile

/-!
# Actual first-live follower safety

Sources: `sources/zip4/manuscript/appendix_a_local_protocol.tex:28-64`,
`04_slow_fast_learner.tex:157-174`, `05_binary_transport.tex:366-391,426-431`,
and `06_interruptions.tex:9-14,192-209,246-297`.

This is internal safety of the first all-active window from an explicit
unoccupied boundary. Whole public rows, the selected private index, and the
whole reward table remain inputs. Numerical service and recovery checks use
the actual feedback and diagnostics. No source queue, score, arrival,
probability, or manuscript closure is asserted.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ReferenceFirstLiveFollowerSafety

open ConstructorDimensions
open ActiveFollowerLifecycle
open ActiveFollowerDownAcceptance
open ReferenceDownReception

variable {p : Parameters} {rate : ReferenceActivePhysicalStep.RateInput p}

/-- The service input checks follow from the carried local domains. -/
private theorem queue_input_domain (s : ReferencePrelaunchFollower.State p rate.eta)
    (h : localStateDomainValid s) : ActiveFollowerQueueOperation.stateInputDomain s :=
  ⟨h.1.1, h.1.2.1, h.1.2.2, h.2.1.1, h.2.1.2.1⟩

/-- Retype the same quantized buffer entries for the DOWN input check. -/
private theorem down_buffer_domain (s : ReferencePrelaunchFollower.State p rate.eta)
    (h : localBufferValid s) : bufferInputDomain p s.buffer := by
  refine ⟨?_, h.2.1⟩
  intro saved hsaved
  obtain ⟨q, hq, heq⟩ := h.2.2 saved hsaved
  exact ⟨(h.1 saved hsaved).1, (h.1 saved hsaved).2,
    ⟨q, by omega⟩, heq⟩

/-- Conditional local PREPARE lemma. The induction supplies the domain,
unoccupied zero fields, occupied record and the actual unchanged StartRound.
The offer and arm-choice equations are proved here, including the placeholder. -/
private theorem prepare_after_unchanged_start
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (alpha : ReferencePrelaunchFollower.Activation p) (t : Fin p.T)
    (active : alpha.val ≤ t.val + 1)
    (s : ReferencePrelaunchFollower.State p rate.eta) (memory : LocalMemory p)
    (hvalid : localStateDomainValid s)
    (hzero : s.status = .unoccupied →
      s.lastDown = none ∧ s.S = 0 ∧ s.delta = 0 ∧ s.backlog = 0)
    (hrecord : s.status ≠ .unoccupied → ∃ M, s.lastDown = some M)
    (hstart : startRound rate.eta t s memory = .ok (s, memory)) :
    (DeclaredFollowerLocalRound.prepare rate i row alpha t active (.ordinary s memory)).configuration =
      .ordinary s memory := by
  classical
  have hdomain := queue_input_domain s hvalid
  by_cases hu : s.status = .unoccupied
  · obtain ⟨hnone, hS, hd, hb⟩ := hzero hu
    have hfields : ActiveFollowerQueueOperation.upOfferFields s = OrdinaryMessageCodec.upPlaceholder := by
      simp [ActiveFollowerQueueOperation.upOfferFields, ReferencePrelaunchFollower.acceptedStart,
        hnone, hS, hd, hb, OrdinaryMessageCodec.upPlaceholder]
    have hadm : OrdinaryMessageCodec.upAdmissible
        (ReferencePrelaunchFollower.codecParams p rate.eta) (ActiveFollowerQueueOperation.upOfferFields s) :=
      Or.inl hfields
    by_cases hselected : ActiveFollowerQueueOperation.selectedUpRound i row alpha t
    · let offered : OrdinaryMessageCodec.UpRecord
          (ReferencePrelaunchFollower.codecParams p rate.eta) := ⟨ActiveFollowerQueueOperation.upOfferFields s, hadm⟩
      have hoff : ActiveFollowerQueueOperation.checkedUpOffer rate.eta i row alpha t s = .offer offered := by
        simp [ActiveFollowerQueueOperation.checkedUpOffer, hdomain, hselected, hu, hadm, offered]
      have hmatch : ActiveFollowerArmChoice.upStateDomain s ∧ ActiveFollowerArmChoice.offeredUpMatchesState s offered :=
        ⟨hvalid.1, rfl, rfl, rfl, rfl⟩
      obtain ⟨_, hslot, hsender⟩ := hselected
      have hchoice := ActiveFollowerArmChoice.followerArmChoiceCore_unoccupied_selected_up s (row.2 t) i
        offered hu hslot hsender hmatch
      simp only [DeclaredFollowerLocalRound.prepare, hstart, hoff, ActiveFollowerArmChoice.followerArmChoice, hchoice]
    · have hoff : ActiveFollowerQueueOperation.checkedUpOffer rate.eta i row alpha t s = .noOffer :=
        ActiveFollowerQueueOperation.checkedUpOffer_noOffer rate.eta i row alpha t s hdomain
          (fun h => hselected h.1)
      have hnot : ¬ (PublicDiscreteDraws.slotDraw (row.2 t).1 =
          PublicDiscreteDraws.upSlot ∧
          PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K (row.2 t).1 = i) :=
        fun h => hselected ⟨active, h⟩
      have hchoice : ∃ arm, ActiveFollowerArmChoice.followerArmChoice s row t i none = some arm := by
        simp only [ActiveFollowerArmChoice.followerArmChoice,
          ActiveFollowerArmChoice.followerArmChoiceCore, ite_eq_left hu, ite_eq_right hnot]
        split <;> exact ⟨_, rfl⟩
      obtain ⟨arm, hc⟩ := hchoice
      simp only [DeclaredFollowerLocalRound.prepare, hstart, hoff, hc]
  · obtain ⟨M, hM⟩ := hrecord hu
    have hoff := ActiveFollowerQueueOperation.checkedUpOffer_noOffer rate.eta i row alpha t s hdomain
      (fun h => hu h.2)
    have hchoice : ∃ arm, ActiveFollowerArmChoice.followerArmChoice s row t i none = some arm := by
      simp only [ActiveFollowerArmChoice.followerArmChoice,
        ActiveFollowerArmChoice.followerArmChoiceCore, ite_eq_right hu, hM]
      split
      · exact ⟨_, rfl⟩
      · split
        · exact ⟨_, rfl⟩
        · split <;> exact ⟨_, rfl⟩
    obtain ⟨arm, hc⟩ := hchoice
    simp only [DeclaredFollowerLocalRound.prepare, hstart, hoff, hc]

/-- Conditional occupied service lemma. Its inputs are local domains, the
preceding mass bound, active time and the stored record. The actual feedback
arrival and conservation prove the output check; no output-domain input occurs. -/
private theorem occupied_service
    (steps : ℕ) (hsteps : steps + 1 ≤ p.T)
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (alpha : ReferencePrelaunchFollower.Activation p) (t : Fin p.T)
    (active : alpha.val ≤ t.val + 1)
    (observation : ReferencePrelaunchFollower.Observation p)
    (s : ReferencePrelaunchFollower.State p rate.eta)
    (hvalid : localStateDomainValid s) (hmass : s.S + s.backlog ≤ steps * D p)
    (hu : s.status ≠ .unoccupied)
    (M : OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (hM : s.lastDown = some M) :
    ∃ serviced,
      ActiveFollowerQueueOperation.checkedService rate.eta rate.sourceCap rate.n rate.n_scale i row alpha t
        observation s = .success serviced ∧
      serviced.output = ActiveFollowerQueueOperation.serviceUpdate rate.n s
        (ActiveFollowerQueueOperation.rawArrival rate.eta i row t M observation) ∧
      localStateDomainValid serviced.output ∧
      serviced.output.S + serviced.output.backlog ≤ (steps + 1) * D p := by
  classical
  let arrival := ActiveFollowerQueueOperation.rawArrival rate.eta i row t M observation
  let service := ActiveFollowerQueueOperation.localService rate.n s.backlog arrival
  have ha : arrival ≤ D p := ActiveFollowerQueueOperation.rawArrival_le_D rate.eta i row t M observation
  have hd : service ≤ D p := ActiveFollowerQueueOperation.localService_le_D rate.eta rate.sourceCap
    rate.n rate.n_scale s.backlog arrival
  have hconservation : (ActiveFollowerQueueOperation.serviceUpdate rate.n s arrival).S +
      (ActiveFollowerQueueOperation.serviceUpdate rate.n s arrival).backlog = s.S + s.backlog + arrival := by
    have hc := CappedService.residual_add_service (ActiveFollowerQueueOperation.serviceCapacity rate.n) s.backlog arrival
    change s.S + service + CappedService.residual (ActiveFollowerQueueOperation.serviceCapacity rate.n)
      s.backlog arrival = _
    change CappedService.residual (ActiveFollowerQueueOperation.serviceCapacity rate.n) s.backlog arrival + service =
      s.backlog + arrival at hc
    omega
  have hmassNext : (ActiveFollowerQueueOperation.serviceUpdate rate.n s arrival).S +
      (ActiveFollowerQueueOperation.serviceUpdate rate.n s arrival).backlog ≤ (steps + 1) * D p := by
    rw [hconservation, Nat.add_mul, one_mul]
    omega
  have htotal : (ActiveFollowerQueueOperation.serviceUpdate rate.n s arrival).S +
      (ActiveFollowerQueueOperation.serviceUpdate rate.n s arrival).backlog ≤ p.T * D p :=
    hmassNext.trans (Nat.mul_le_mul_right _ hsteps)
  have hout : ActiveFollowerQueueOperation.outputDomain rate.n s arrival service :=
    ⟨ha, hd, by change (ActiveFollowerQueueOperation.serviceUpdate rate.n s arrival).S ≤ _; omega,
      by change (ActiveFollowerQueueOperation.serviceUpdate rate.n s arrival).backlog ≤ _; omega⟩
  have hdomain := queue_input_domain s hvalid
  have hthin := ActiveFollowerQueueOperation.thinningProbability_domain rate.eta M
  have hexists : ∃ serviced,
      ActiveFollowerQueueOperation.checkedService rate.eta rate.sourceCap rate.n rate.n_scale i row alpha t
        observation s = .success serviced := by
    unfold ActiveFollowerQueueOperation.checkedService
    rw [dite_eq_left hdomain]
    split
    · rename_i hs
      exact False.elim (hu hs)
    · rw [dite_eq_left active]
      split
      · rename_i hn
        rw [hM] at hn
        cases hn
      · rename_i M' hM'
        have he := Option.some.inj (hM'.symm.trans hM)
        subst M'
        rw [dite_eq_left hthin, dite_eq_left hout]
        exact ⟨_, rfl⟩
    · rw [dite_eq_left active]
      split
      · rename_i hn
        rw [hM] at hn
        cases hn
      · rename_i M' hM'
        have he := Option.some.inj (hM'.symm.trans hM)
        subst M'
        rw [dite_eq_left hthin, dite_eq_left hout]
        exact ⟨_, rfl⟩
  obtain ⟨serviced, hservice⟩ := hexists
  have heq : serviced.output = ActiveFollowerQueueOperation.serviceUpdate rate.n s arrival := by
    have haction := serviced.action
    have harrival : serviced.arrival = arrival := by
      cases hs : s.status with
      | unoccupied => exact False.elim (hu hs)
      | pending =>
        simp only [ActiveFollowerQueueOperation.serviceAction, hs] at haction
        obtain ⟨_, M', hM', _, har, _⟩ := haction
        have := Option.some.inj (hM'.symm.trans hM)
        subst M'
        exact har
      | released =>
        simp only [ActiveFollowerQueueOperation.serviceAction, hs] at haction
        obtain ⟨_, M', hM', _, har, _⟩ := haction
        have := Option.some.inj (hM'.symm.trans hM)
        subst M'
        exact har
    rw [serviced.queueUpdate, harrival]
    have hoccupied : s.status.occupied := by
      cases hs : s.status <;> simp_all [ActiveRoundActions.FollowerStatus.occupied]
    simp only [ActiveFollowerQueueOperation.serviceOutput, ite_eq_left hoccupied]
  refine ⟨serviced, hservice, heq, ?_, heq ▸ hmassNext⟩
  rw [heq]
  exact ⟨⟨by omega,
    hd, by omega⟩,
    hvalid.2.1, hvalid.2.2⟩

/-- A scan with the produced grid bound and false strictly prior bits includes
the current round. Its current proposal is unrestricted and acts next round. -/
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

/-- Actual pre-effect diagnostics survive every later failure branch. -/
private theorem finish_diagnostics
    (view : Option (ChoiceTimeView p rate.eta)) (prepared : DeclaredFollowerLocalRound.PreparedRound p rate)
    (observation : ReferencePrelaunchFollower.Observation p)
    (s : ReferencePrelaunchFollower.State p rate.eta) (memory : LocalMemory p)
    (hc : prepared.configuration = .ordinary s memory) :
    let recorded := ReferenceActivePhysicalStep.recordFollower view prepared.follower prepared.row prepared.activation
      prepared.time prepared.active prepared.arm observation s
    (ReferenceActivePhysicalStep.finishFollower view prepared observation).downInput = recorded.downInput ∧
      (ReferenceActivePhysicalStep.finishFollower view prepared observation).down = recorded.down := by
  simp only [ReferenceActivePhysicalStep.finishFollower, hc]
  cases hr : (ReferenceActivePhysicalStep.recordFollower view prepared.follower prepared.row prepared.activation
    prepared.time prepared.active prepared.arm observation s).result with
  | error e => exact ⟨rfl, rfl⟩
  | ok after =>
    simp only
    cases hf : DeclaredFollowerLocalRound.releaseAndFinish rate prepared.follower prepared.row prepared.time
      observation s memory after with
    | error e => exact ⟨rfl, rfl⟩
    | ok pair => cases pair; exact ⟨rfl, rfl⟩

/-- List-prefix equations identify the whole actual successor record and
produce its physical span, without a successful-history assumption. -/
private theorem window_record_actual
    (initial : ReferenceActivePhysicalHorizon.State p rate) (rows : CompletePublicTable.CompleteRows p)
    (J : Fin (M p)) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (k : ℕ) (hk : k < (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceActivePhysicalHorizon.run initial rows J rewards start count hspan active).records).length) :
    ∃ hstep : start + (k + 1) ≤ p.T,
      (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (ReferenceActivePhysicalHorizon.run initial rows J rewards start count hspan active).records)[k] =
        ReferenceAssignmentPayloadChronology.actualRunRecordAt initial rows J rewards start k hstep active := by
  let E := ReferenceActivePhysicalHorizon.run initial rows J rewards start count hspan active
  let W := ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records
  change k < W.length at hk
  have hprefix : W.IsPrefix E.records := List.takeWhile_prefix _
  have hcount := ReferenceActivePhysicalHorizon.run_record_count initial rows J rewards start count hspan active
  have hkcount : k < count := by
    have := hprefix.length_le
    change E.records.length = count at hcount
    omega
  have hstep : start + (k + 1) ≤ p.T := by omega
  refine ⟨hstep, ?_⟩
  have hnextPrefix : (ReferenceActivePhysicalHorizon.run initial rows J rewards start (k + 1) hstep active).records.IsPrefix
      E.records := by
    obtain ⟨suffix, heq⟩ := ReferenceCollectionPhaseHistory.run_records_prefix initial rows J
      rewards start (k + 1) (count - (k + 1)) (by omega) active
    exact ⟨suffix, by simpa only [Nat.add_sub_of_le (by omega : k + 1 ≤ count)] using heq.symm⟩
  have hlength := ReferenceActivePhysicalHorizon.run_record_count initial rows J rewards start k (by omega) active
  have hkNext : k <
      (ReferenceActivePhysicalHorizon.run initial rows J rewards start (k + 1) hstep active).records.length := by
    rw [ReferenceActivePhysicalHorizon.run_record_count]
    omega
  have helem : (ReferenceActivePhysicalHorizon.run initial rows J rewards start (k + 1) hstep active).records[k] =
      ReferenceAssignmentPayloadChronology.actualRunRecordAt initial rows J rewards start k hstep active := by
    simp only [ReferenceAssignmentPayloadChronology.run_successor_actualRunRecordAt, List.getElem_append_right (by omega :
      (ReferenceActivePhysicalHorizon.run initial rows J rewards start k (by omega) active).records.length ≤ k),
      hlength, Nat.sub_self, List.getElem_singleton]
  exact (hprefix.getElem hk).trans ((hnextPrefix.getElem hkNext).symm.trans helem)

/-- Conditional tail lemma. The induction supplies pre/post domains, mass,
unoccupied zero fields, compatible stored starts and preserved occupancy.
Both literal release tests and the final token write are checked here. -/
private theorem release_finish_success
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p) (t : Fin p.T)
    (observation : ReferencePrelaunchFollower.Observation p)
    (pre post : ReferencePrelaunchFollower.State p rate.eta) (memory : LocalMemory p)
    (start steps : ℕ)
    (hpre : localStateDomainValid pre) (hpost : localStateDomainValid post)
    (hmass : post.S + post.backlog ≤ steps * D p)
    (hzero : post.status = .unoccupied →
      post.lastDown = none ∧ post.S = 0 ∧ post.delta = 0 ∧ post.backlog = 0)
    (hpreRecord : pre.status ≠ .unoccupied → ∃ M,
      pre.lastDown = some M ∧ M.val.sigma ≤ t.val)
    (hpostRecord : post.status ≠ .unoccupied → ∃ M,
      post.lastDown = some M ∧ M.val.sigma = start + 1 ∧ M.val.sigma ≤ t.val + 1)
    (hoccupied : pre.status ≠ .unoccupied → post.status ≠ .unoccupied) :
    ∃ next nextMemory,
      DeclaredFollowerLocalRound.releaseAndFinish rate i row t observation pre memory post = .ok (next, nextMemory) ∧
      localStateDomainValid next ∧ next.S + next.backlog ≤ steps * D p ∧
      (next.status = .unoccupied →
        next.lastDown = none ∧ next.S = 0 ∧ next.delta = 0 ∧ next.backlog = 0) ∧
      (next.status ≠ .unoccupied → ∃ M,
        next.lastDown = some M ∧ M.val.sigma = start + 1 ∧
        nextMemory.lastProposalRead = some ⟨t, FollowerCutoffScan.completeRowProposalBit p rate.eta.val row t⟩) := by
  classical
  have hrelease : ∃ released,
      releaseAfterService rate.eta i t (publicRowOfCompleteRow row t) observation pre post =
        .ok released ∧
      localStateDomainValid released ∧ released.S + released.backlog ≤ steps * D p ∧
      (released.status = .unoccupied →
        released.lastDown = none ∧ released.S = 0 ∧ released.delta = 0 ∧ released.backlog = 0) ∧
      (released.status ≠ .unoccupied → ∃ M,
        released.lastDown = some M ∧ M.val.sigma = start + 1 ∧ M.val.sigma ≤ t.val + 1) := by
    by_cases hp : pre.status = .pending
    · have hne : pre.status ≠ .unoccupied := by simp only [hp]; decide
      obtain ⟨M, hM, htime⟩ := hpreRecord hne
      obtain ⟨M', hM', hsigma', htime'⟩ := hpostRecord (hoccupied hne)
      rw [releaseAfterService_pending_branch rate.eta i t (publicRowOfCompleteRow row t)
        observation pre post hp hpre M hM htime hpost
        (Or.inr ⟨M', hM', htime'⟩)]
      by_cases hc : releaseCondition rate.eta i (publicRowOfCompleteRow row t) observation M
      · rw [ite_eq_left hc]
        refine ⟨_, rfl, hpost, hmass, ?_, ?_⟩
        · intro hu
          cases hu
        · intro _
          exact ⟨M', hM', hsigma', htime'⟩
      · rw [ite_eq_right hc]
        exact ⟨post, rfl, hpost, hmass, hzero, hpostRecord⟩
    · rw [releaseAfterService_not_pending rate.eta i t (publicRowOfCompleteRow row t)
        observation pre post hp]
      exact ⟨post, rfl, hpost, hmass, hzero, hpostRecord⟩
  obtain ⟨released, hr, hv, hm, hz, hrecord⟩ := hrelease
  by_cases hu : released.status = .unoccupied
  · have hf := finishRound_unoccupied rate.eta t row released memory hv hu
    refine ⟨released, memory, ?_, hv, hm, hz, ?_⟩
    · simp only [DeclaredFollowerLocalRound.releaseAndFinish, hr, hf]
    · exact fun h => False.elim (h hu)
  · obtain ⟨M, hM, hsigma, htime⟩ := hrecord hu
    have hf := finishRound_occupied_read rate.eta t row released memory hu hv M hM htime
    refine ⟨released, ⟨some ⟨t, FollowerCutoffScan.completeRowProposalBit p rate.eta.val row t⟩⟩,
      ?_, hv, hm, hz, ?_⟩
    · simp only [DeclaredFollowerLocalRound.releaseAndFinish, hr, hf]
    · intro _
      exact ⟨M, hM, hsigma, rfl⟩

/-- Coordinator safety, first-complement replay and clock preservation produce
the common current payload, live grid and prior bits. Equal-time actual birth
records identify the whole selected payload, rather than only its start field. -/
private theorem first_window_geometry
    (initial : ReferenceActivePhysicalHorizon.State p rate) (rows : CompletePublicTable.CompleteRows p)
    (J : Fin (M p)) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start) (hfirst : initial.coordinator = .first) :
    let E := ReferenceActivePhysicalHorizon.run initial rows J rewards start count hspan active
    let W := ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records
    ∀ k : Fin W.length, ∃ payload : ReferenceActivePhysicalStep.Payload rate,
      payload.sigma.val = start ∧
      W[k.val].input.time.val + 2 ≤ FollowerCutoffScan.gridBoundary p rate.eta.val payload.sigma ∧
      (∀ j : Fin p.T, start ≤ j.val → j.val < W[k.val].input.time.val →
        FollowerCutoffScan.completeRowProposalBit p rate.eta.val (rows J) j = false) ∧
      (∀ selected : ReferenceActivePhysicalStep.Selection W[k.val].input,
        W[k.val].output.preparation.coordinator.selection = some selected →
        selected.view.payload = payload) := by
  intro E W k
  have hw : W.length ≤ count := by
    calc
      W.length ≤ E.records.length := (List.takeWhile_prefix _).length_le
      _ = count := ReferenceActivePhysicalHorizon.run_record_count initial rows J rewards start count hspan active
  obtain ⟨hstep, hactual⟩ := window_record_actual initial rows J rewards start count hspan active
    k.val k.isLt
  have htime : W[k.val].input.time.val = start + k.val := by rw [hactual]; rfl
  have hN := ReferenceFirstLiveCoordinatorSafety.run_first_live_coordinator_safety
    initial rows J rewards start count hspan active hfirst
  have hkWindow : k.val + 1 ≤ (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceActivePhysicalHorizon.run initial rows J rewards start count hspan active).records).length :=
    Nat.succ_le_of_lt k.isLt
  have hkCount : k.val + 1 ≤ count := (Nat.succ_le_of_lt k.isLt).trans hw
  obtain ⟨r, q, base, hr⟩ := (hN.2.1 (k.val + 1) hkWindow).2 (by omega)
  obtain ⟨_, hsigma, _, ⟨birth, hbirth, hborn, hbirthTime, _⟩, hbits, _⟩ :=
    ReferenceFirstComplementReplay.run_first_complement_replay initial rows J rewards start count hspan active hfirst
      (k.val + 1) hkCount hkWindow r q base hr
  have hseed : ReferenceCoordinatorClockDomains.clockAt rows J start initial := by
    simp only [ReferenceCoordinatorClockDomains.clockAt, hfirst]
  have hc := (ReferenceRunClockPreservation.run_clockAt initial rows J rewards start
    (k.val + 1) hstep active hseed).1
  simp only [ReferenceCoordinatorClockDomains.clockAt, hr] at hc
  obtain ⟨_, hclock, hclockSigma, _, hgrid, _, hbeforeGrid, _⟩ := hc
  have hg : r.gridBoundary = FollowerCutoffScan.gridBoundary p rate.eta.val r.payload.sigma := by
    rw [hgrid, hclock.1, hclockSigma]
    rfl
  have hbirthFull : birth ∈ E.records := by
    obtain ⟨suffix, heq⟩ := ReferenceCollectionPhaseHistory.run_records_prefix initial rows J
      rewards start (k.val + 1) (count - (k.val + 1)) (by omega) active
    have heq' : E.records =
        (ReferenceActivePhysicalHorizon.run initial rows J rewards start (k.val + 1) hstep active).records ++ suffix := by
      simpa only [Nat.add_sub_of_le (by omega : k.val + 1 ≤ count)] using heq
    rw [heq']
    exact List.mem_append_left _ hbirth
  refine ⟨r.payload, hsigma, ?_, ?_, ?_⟩
  · rw [htime]
    rw [hg] at hbeforeGrid
    omega
  · intro j hj ht
    apply hbits j hj
    rw [htime] at ht
    omega
  · intro selected hs
    obtain ⟨other, hother, hotherTime, hotherBorn, _, _⟩ :=
      ReferenceFirstDownRecoveryBudget.run_first_selected_payload initial rows J rewards start count hspan active hfirst k
        selected hs
    have heq : other = birth := ReferenceAssignmentPayloadChronology.run_records_time_injective initial rows J rewards start
      count hspan active hother hbirthFull (hotherTime.trans hbirthTime.symm)
    subst other
    exact ReferenceAssignmentPayloadChronology.installationBirth_payload_unique birth _ _ hotherBorn hborn

/-- Conditional unoccupied observation lemma on an actual window record.
CHOICE ordinariness, local domains, zero fields and chronology come from the
prefix induction. The real diagnostic call supplies every input to the
pre-effect recovery budget, even before retention or tail success is known. -/
private theorem unoccupied_record_success
    (initial : ReferenceActivePhysicalHorizon.State p rate) (rows : CompletePublicTable.CompleteRows p)
    (J : Fin (M p)) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start) (hfirst : initial.coordinator = .first) :
    let E := ReferenceActivePhysicalHorizon.run initial rows J rewards start count hspan active
    let W := ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records
    ∀ (k : Fin W.length) (i : Fin (p.m - 1))
      (choice : ReferencePrelaunchFollower.State p rate.eta) (memory : LocalMemory p),
      (W[k.val].output.preparation.followers.followers i).configuration = .ordinary choice memory →
      localStateDomainValid choice → choice.status = .unoccupied →
      choice.lastDown = none → choice.S = 0 → choice.delta = 0 → choice.backlog = 0 →
      (∀ saved ∈ choice.buffer, saved.calendarRound < W[k.val].input.time.val + 1) →
      ∃ post,
        (ReferenceActivePhysicalStep.recordFollower W[k.val].output.preparation.coordinator.downView i
          W[k.val].input.row (W[k.val].input.state.activations i) W[k.val].input.time
          (W[k.val].input.active i) (W[k.val].output.preparation.followers.followers i).arm
          (W[k.val].output.preparation.feedback.observations
            (PublicDiscreteDraws.followerPlayer p.two_le_m i)) choice).result = .ok post ∧
        localStateDomainValid post ∧ post.S + post.backlog ≤ (k.val + 1) * D p ∧
        (post.status = .unoccupied →
          post.lastDown = none ∧ post.S = 0 ∧ post.delta = 0 ∧ post.backlog = 0) ∧
        (post.status ≠ .unoccupied → ∃ M,
          post.lastDown = some M ∧ M.val.sigma = start + 1 ∧ M.val.sigma ≤ W[k.val].input.time.val + 1) := by
  classical
  intro E W k i choice memory hchoice hvalid hu hn hS hd hb hbefore
  let record := W[k.val]
  let prepared := record.output.preparation.followers.followers i
  let observation := record.output.preparation.feedback.observations
    (PublicDiscreteDraws.followerPlayer p.two_le_m i)
  let view := record.output.preparation.coordinator.downView
  obtain ⟨logged, hlog, _, _, _, hloggedBuffer⟩ :=
    ActiveFollowerLogging.checkedLogging_success_of_chronological i record.input.row
      (record.input.state.activations i) record.input.time (prepared.arm, observation)
      choice hvalid.2.1 hbefore hu
  have hframe := ActiveFollowerLogging.checkedLogging_success_frame i record.input.row
    (record.input.state.activations i) record.input.time (prepared.arm, observation) choice logged hlog
  have hlu : logged.status = .unoccupied := hframe.2.2.2.2.1.trans hu
  have hln : logged.lastDown = none := hframe.1.trans hn
  have hlS : logged.S = 0 := hframe.2.1.trans hS
  have hld : logged.delta = 0 := hframe.2.2.1.trans hd
  have hlb : logged.backlog = 0 := hframe.2.2.2.1.trans hb
  have hlbatch : downDecoderStateValid logged := by
    rw [downDecoderStateValid, hframe.2.2.2.2.2.1]
    exact hvalid.2.2
  have hlvalid : localStateDomainValid logged :=
    ⟨⟨by omega, by omega, by omega⟩, hloggedBuffer, hlbatch⟩
  let cut := referenceDownCut p view i record.input.row record.input.time observation rate logged
  have hrecorded :
      (ReferenceActivePhysicalStep.recordFollower view i record.input.row (record.input.state.activations i)
        record.input.time (record.input.active i) prepared.arm observation choice).result =
        DeclaredFollowerLocalRound.consumeDownResult rate cut.outcome := by
    simp only [ReferenceActivePhysicalStep.recordFollower, dite_eq_left hu, hlog, cut]
  have halign := record.output.preparation.follower_alignment i
  have hobs : record.output.followers i = ReferenceActivePhysicalStep.finishFollower view prepared observation := by
    dsimp only [view, prepared, observation]
    rw [record.output_eq]
    rfl
  have hdiag := finish_diagnostics view prepared observation choice memory hchoice
  have hcall := ReferenceActivePhysicalStep.recordFollower_logged view i record.input.row
    (record.input.state.activations i) record.input.time (record.input.active i)
    prepared.arm observation choice logged hu hlog
  have hinput : (record.output.followers i).downInput = some logged := by
    rw [hobs, hdiag.1]
    simpa only [prepared, halign.1, halign.2.1, halign.2.2.1, halign.2.2.2] using hcall.1
  have hcut : (record.output.followers i).down = some cut := by
    rw [hobs, hdiag.2]
    simpa only [prepared, halign.1, halign.2.1, halign.2.2.1, halign.2.2.2] using hcall.2
  have hregs : registerInputDomain p rate logged := hlvalid.1
  have hbatch : decoderInputDomain p logged.downBatch := hlbatch
  have hbuffer := down_buffer_domain logged hloggedBuffer
  have hstepSpec := AffineBatchDecoder.step_spec p
    (currentInputExtension p (currentRoundInput p i record.input.row record.input.time observation rate logged))
    logged.downBatch record.input.time hlbatch.1 hlbatch.2
  have hstepBatch : decoderInputDomain p
      (currentDecodeStep p i record.input.row record.input.time observation rate logged).1 :=
    ⟨hstepSpec.1, hstepSpec.2.1⟩
  let advanced := { logged with downBatch :=
    (currentDecodeStep p i record.input.row record.input.time observation rate logged).1 }
  have hadvanced : localStateDomainValid advanced :=
    ⟨hlvalid.1, hloggedBuffer, hstepBatch⟩
  have hsimple : ∀ post : ReferencePrelaunchFollower.State p rate.eta,
      post.lastDown = none → post.S = 0 → post.delta = 0 → post.backlog = 0 →
      post.status = .unoccupied → localStateDomainValid post →
      DeclaredFollowerLocalRound.consumeDownResult rate cut.outcome = .ok post →
      ∃ post,
        (ReferenceActivePhysicalStep.recordFollower view i record.input.row (record.input.state.activations i)
          record.input.time (record.input.active i) prepared.arm observation choice).result = .ok post ∧
        localStateDomainValid post ∧ post.S + post.backlog ≤ (k.val + 1) * D p ∧
        (post.status = .unoccupied →
          post.lastDown = none ∧ post.S = 0 ∧ post.delta = 0 ∧ post.backlog = 0) ∧
        (post.status ≠ .unoccupied → ∃ M,
          post.lastDown = some M ∧ M.val.sigma = start + 1 ∧ M.val.sigma ≤ record.input.time.val + 1) := by
    intro post hn hS hd hb hu hv he
    exact ⟨post, hrecorded.trans he, hv, by omega,
      fun _ => ⟨hn, hS, hd, hb⟩, fun h => False.elim (h hu)⟩
  by_cases hselected : downSelected p i record.input.row record.input.time
  · by_cases hmatches : (currentDecodeStep p i record.input.row record.input.time
        observation rate logged).2 = expectedDownFlatWord view i record.input.row record.input.time
    · cases hp : ordinaryParse p rate
        (currentDecodeStep p i record.input.row record.input.time observation rate logged).2 with
      | none =>
        apply hsimple advanced hln hlS hld hlb hlu hadvanced
        simp only [cut, referenceDownCut, dite_eq_left hselected, dite_eq_left hlu,
          dite_eq_left hregs, dite_eq_left hbatch, dite_eq_left hbuffer, dite_eq_left hmatches,
          hp, DeclaredFollowerLocalRound.consumeDownResult, advanced]
      | some M =>
        by_cases ha : OrdinaryMessageCodec.acceptDown
            (ReferencePrelaunchFollower.codecParams p rate.eta)
            (ReferencePrelaunchFollower.acceptedStart logged) (record.input.time.val + 1) M
        · have hc : cut.rawComparison = some true := by
            simp only [cut, referenceDownCut, dite_eq_left hselected, dite_eq_left hlu,
              dite_eq_left hregs, dite_eq_left hbatch, dite_eq_left hbuffer, dite_eq_left hmatches]
          have hparse : cut.ordinaryParse = some M := by
            simp only [cut, referenceDownCut, dite_eq_left hselected, dite_eq_left hlu,
              dite_eq_left hregs, dite_eq_left hbatch, dite_eq_left hbuffer, dite_eq_left hmatches, hp]
          have haccept : cut.ordinaryAcceptance := by
            simp only [cut, referenceDownCut, dite_eq_left hselected, dite_eq_left hlu,
              dite_eq_left hregs, dite_eq_left hbatch, dite_eq_left hbuffer, dite_eq_left hmatches,
              hp, ordinaryLocalAcceptanceTest]
            exact ha
          obtain ⟨selected, birth, hstart, hs, _, _, _, hM, hsigma, _, hMsigma, _, _,
              htime, _, _, _, _, hlength, final, hchecked, hmass, hlast, _⟩ :=
            ReferenceFirstDownRecoveryBudget.run_first_down_recovery_budget
              initial rows J rewards start count hspan active hfirst
              k i logged cut M hinput hcut hc hparse haccept
          obtain ⟨payload, hpsigma, hpgrid, hpbits, hpselected⟩ :=
            first_window_geometry initial rows J rewards start count hspan active hfirst k
          have hwhole := hpselected selected hs
          have hcurrent : M = payload.downRecord i :=
            hM.trans (congrArg (fun P : ReferenceActivePhysicalStep.Payload rate => P.downRecord i) hwhole)
          have hdownStart : downStart p rate M = payload.sigma := by
            apply Fin.ext
            have hlabel := downStart_val_add_one p rate M
            have hlabelCurrent := congrArg (fun N => N.val.sigma) hcurrent
            change M.val.sigma = payload.sigma.val + 1 at hlabelCurrent
            omega
          have hell : (acceptedCutoffScan p rate M record.input.time hstart record.input.row).endpoint =
              record.input.time.val + 2 := by
            apply scan_live_endpoint record.input.row record.input.time M hstart
            · rw [hdownStart]
              exact hpgrid
            · intro j hj hjt
              have hrow : record.input.row = rows J := by
                obtain ⟨hstep, he⟩ := window_record_actual initial rows J rewards start count hspan
                  active k.val k.isLt
                exact congrArg (fun r => r.input.row) he
              rw [hrow]
              apply hpbits j
              · rw [hdownStart, hpsigma] at hj
                exact hj
              · exact hjt
          let after := { advanced with
            lastDown := some M
            S := final.registers.1
            delta := final.lastService
            backlog := final.registers.2
            status := ActiveRoundActions.FollowerStatus.pending
            buffer := [] }
          have hout := (checkedRecovery_success p rate M logged _ final hchecked).1
          have hafterBuffer : localBufferValid after := by
            simp [localBufferValid, after]
          have hafterValid : localStateDomainValid after :=
            ⟨hout, hafterBuffer, hstepBatch⟩
          have hcheckedNow : checkedRecovery p rate M logged (record.input.time.val + 2) = .ok final := by
            rw [← hell]
            exact hchecked
          have hconsume : DeclaredFollowerLocalRound.consumeDownResult rate cut.outcome = .ok after := by
            simp only [cut, referenceDownCut, dite_eq_left hselected, dite_eq_left hlu,
              dite_eq_left hregs, dite_eq_left hbatch, dite_eq_left hbuffer, dite_eq_left hmatches,
              hp, dite_eq_left ha, hell, hcheckedNow, ↓reduceIte, DeclaredFollowerLocalRound.consumeDownResult,
              after, advanced]
          refine ⟨after, hrecorded.trans hconsume, hafterValid, ?_, ?_, ?_⟩
          · exact hmass.trans (Nat.mul_le_mul_right _ hlength)
          · intro hu
            cases hu
          · intro _
            exact ⟨M, rfl, hMsigma, ha.2⟩
        · apply hsimple advanced hln hlS hld hlb hlu hadvanced
          simp only [cut, referenceDownCut, dite_eq_left hselected, dite_eq_left hlu,
            dite_eq_left hregs, dite_eq_left hbatch, dite_eq_left hbuffer, dite_eq_left hmatches,
            hp, dite_eq_right ha, DeclaredFollowerLocalRound.consumeDownResult, advanced]
    · apply hsimple advanced hln hlS hld hlb hlu hadvanced
      simp only [cut, referenceDownCut, dite_eq_left hselected, dite_eq_left hlu,
        dite_eq_left hregs, dite_eq_left hbatch, dite_eq_left hbuffer, dite_eq_right hmatches,
        DeclaredFollowerLocalRound.consumeDownResult, advanced]
  · apply hsimple logged hln hlS hld hlb hlu hlvalid
    simp only [cut, referenceDownCut, dite_eq_right hselected, DeclaredFollowerLocalRound.consumeDownResult]

/-- The simultaneous endpoint/record induction, for one actual follower.
Its only follower premises describe the explicit initial boundary. -/
private theorem prefix_follower_safety
    (initial : ReferenceActivePhysicalHorizon.State p rate) (rows : CompletePublicTable.CompleteRows p)
    (J : Fin (M p)) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start) (hfirst : initial.coordinator = .first)
    (i : Fin (p.m - 1)) (seed : ReferencePrelaunchFollower.State p rate.eta)
    (memory : LocalMemory p) (hseed : initial.followers i = .ordinary seed memory)
    (hS : seed.S = 0) (hd : seed.delta = 0) (hb : seed.backlog = 0)
    (hn : seed.lastDown = none) (hu : seed.status = .unoccupied)
    (hvalid : localBufferValid seed)
    (hpair : seed.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound))
    (htime : ∀ saved ∈ seed.buffer, saved.calendarRound ≤ start)
    (hbatch : downDecoderStateValid seed) :
    let E := ReferenceActivePhysicalHorizon.run initial rows J rewards start count hspan active
    let W := ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records
    ∀ (k : ℕ) (_hk : k ≤ W.length) (hspanK : start + k ≤ p.T),
      (∃ s mem,
        (ReferenceActivePhysicalHorizon.run initial rows J rewards start k hspanK active).finalState.followers i =
          .ordinary s mem ∧
        localStateDomainValid s ∧ s.S + s.backlog ≤ k * D p ∧
        (s.status = .unoccupied → s.lastDown = none ∧ s.S = 0 ∧ s.delta = 0 ∧ s.backlog = 0) ∧
        (s.status ≠ .unoccupied → 0 < k ∧ ∃ M token,
          s.lastDown = some M ∧ M.val.sigma = start + 1 ∧
          mem.lastProposalRead = some token ∧ token.timestamp.val + 1 = start + k ∧
          token.bit = FollowerCutoffScan.completeRowProposalBit p rate.eta.val (rows J) token.timestamp)) ∧
      (∀ j : Fin W.length, j.val < k → ∃ choice choiceMemory next nextMemory,
        (W[j.val].output.preparation.followers.followers i).configuration = .ordinary choice choiceMemory ∧
        (W[j.val].output.followers i).configuration = .ordinary next nextMemory ∧
        (W[j.val].output.followers i).failure = none) := by
  classical
  intro E W k
  induction k with
  | zero =>
    intro _hk hspanK
    refine ⟨⟨seed, memory, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [ReferenceActivePhysicalHorizon.run_zero_final]
      exact hseed
    · exact ⟨⟨by omega, by omega, by omega⟩, hvalid, hbatch⟩
    · simp only [hS, hb, Nat.zero_add, Nat.zero_mul, le_refl]
    · exact fun _ => ⟨hn, hS, hd, hb⟩
    · exact fun h => False.elim (h hu)
    · intro j hj
      omega
  | succ k ih =>
    intro hk hspanK
    have hkprev : k ≤ W.length := by omega
    have hklt : k < W.length := by omega
    obtain ⟨hstep, hactual⟩ := window_record_actual initial rows J rewards start count hspan
      active k hklt
    let record := W[k]
    let prior := ReferenceActivePhysicalHorizon.run initial rows J rewards start k (by omega) active
    have hstate : record.input.state = prior.finalState := by
      change W[k].input.state = _
      rw [hactual]
      rfl
    have ht : record.input.time.val = start + k := by
      change W[k].input.time.val = _
      rw [hactual]
      rfl
    have hrow : record.input.row = rows J := congrArg (fun r => r.input.row) hactual
    have hend : (ReferenceActivePhysicalHorizon.run initial rows J rewards start (k + 1) hspanK active).finalState =
        record.output.next := by
      rw [ReferenceAssignmentPayloadChronology.run_successor_finalState_eq_actualRunRecordAt]
      exact congrArg (fun r => r.output.next) hactual.symm
    obtain ⟨⟨s, mem, hs, hv, hm, hz, ho⟩, hrecords⟩ := ih hkprev (by omega)
    have hsInput : record.input.state.followers i = .ordinary s mem := by
      rw [hstate]
      exact hs
    obtain ⟨payload, hpsigma, hpgrid, hpbits, _⟩ :=
      first_window_geometry initial rows J rewards start count hspan active hfirst ⟨k, hklt⟩
    have hstart : startRound rate.eta record.input.time s mem = .ok (s, mem) := by
      by_cases hu : s.status = .unoccupied
      · exact startRound_unoccupied rate.eta record.input.time s mem hv hu
      · obtain ⟨hkpos, M, token, hM, hMsigma, hread, hstamp, hbit⟩ := ho hu
        have hcoord : acceptedStartCoordinate M = payload.sigma := by
          apply Fin.ext
          have hh := accepted_start_coordinate_one_based M
          omega
        have htimeM : M.val.sigma ≤ record.input.time.val := by omega
        have hgrid : record.input.time.val + 2 ≤
            FollowerCutoffScan.gridBoundary p rate.eta.val (acceptedStartCoordinate M) := by
          rw [hcoord]
          exact hpgrid
        have hbitFalse : token.bit = false := by
          rw [hbit]
          apply hpbits token.timestamp
          · omega
          · change token.timestamp.val < record.input.time.val
            omega
        have hgridNe : FollowerCutoffScan.gridBoundary p rate.eta.val (acceptedStartCoordinate M) ≠
            record.input.time.val + 1 := by omega
        have hbranch := startRound_occupied_branch rate.eta record.input.time s mem hu hv M hM
          htimeM (by omega) token hread (by change token.timestamp.val + 1 = _; omega)
        simpa only [hgridNe, decide_false, hbitFalse, Bool.false_or, Bool.false_eq_true,
          ite_false] using hbranch
    have hchoice : (record.output.preparation.followers.followers i).configuration = .ordinary s mem := by
      rw [record.output.preparation.followers.followers_eq i]
      change (DeclaredFollowerLocalRound.prepare rate i record.input.row (record.input.state.activations i)
        record.input.time (record.input.active i) (record.input.state.followers i)).configuration = _
      rw [hsInput]
      apply prepare_after_unchanged_start i record.input.row (record.input.state.activations i)
        record.input.time (record.input.active i) s mem hv hz
      · intro h
        obtain ⟨_, M, _, hM, _⟩ := ho h
        exact ⟨M, hM⟩
      · exact hstart
    have hchron := ReferenceFollowerBufferProvenance.run_buffer_chronological i initial rows J
      rewards start k (by omega) active seed memory hseed hvalid hpair htime s mem hs
    let prepared := record.output.preparation.followers.followers i
    let observation := record.output.preparation.feedback.observations
      (PublicDiscreteDraws.followerPlayer p.two_le_m i)
    let view := record.output.preparation.coordinator.downView
    have hpost : ∃ post,
        (ReferenceActivePhysicalStep.recordFollower view i record.input.row
          (record.input.state.activations i) record.input.time (record.input.active i)
          prepared.arm observation s).result = .ok post ∧
        localStateDomainValid post ∧ post.S + post.backlog ≤ (k + 1) * D p ∧
        (post.status = .unoccupied →
          post.lastDown = none ∧ post.S = 0 ∧ post.delta = 0 ∧ post.backlog = 0) ∧
        (post.status ≠ .unoccupied → ∃ M,
          post.lastDown = some M ∧ M.val.sigma = start + 1 ∧ M.val.sigma ≤ record.input.time.val + 1) ∧
        (s.status ≠ .unoccupied → post.status ≠ .unoccupied) := by
      by_cases hu : s.status = .unoccupied
      · obtain ⟨hn, hS, hd, hb⟩ := hz hu
        obtain ⟨post, hr, hvpost, hmpost, hzpost, hopost⟩ :=
          unoccupied_record_success initial rows J rewards start count hspan active hfirst
            ⟨k, hklt⟩ i s mem hchoice hv hu hn hS hd hb
            (by
              intro saved hsaved
              change saved.calendarRound < record.input.time.val + 1
              have := hchron.2.2 saved hsaved
              omega)
        exact ⟨post, hr, hvpost, hmpost, hzpost, hopost, fun h => False.elim (h hu)⟩
      · obtain ⟨_, M, _, hM, hMsigma, _⟩ := ho hu
        obtain ⟨serviced, hservice, heq, hvpost, hmpost⟩ := occupied_service k (by omega)
          i record.input.row (record.input.state.activations i) record.input.time (record.input.active i)
          observation s hv hm hu M hM
        refine ⟨serviced.output, ?_, hvpost, hmpost, ?_, ?_, ?_⟩
        · simp only [ReferenceActivePhysicalStep.recordFollower, dite_eq_right hu,
            DeclaredFollowerLocalRound.recordOrServiceThenDown, hservice]
        · intro h
          rw [heq] at h
          exact False.elim (hu h)
        · intro _
          exact ⟨M, by rw [heq]; exact hM, hMsigma, by omega⟩
        · intro _ h
          rw [heq] at h
          exact hu h
    obtain ⟨post, hrecord, hvpost, hmpost, hzpost, hopost, hoc⟩ := hpost
    have hpreRecord : s.status ≠ .unoccupied → ∃ M,
        s.lastDown = some M ∧ M.val.sigma ≤ record.input.time.val := by
      intro h
      obtain ⟨hkpos, M, _, hM, hMsigma, _⟩ := ho h
      exact ⟨M, hM, by omega⟩
    obtain ⟨next, nextMem, hfinish, hvnext, hmnext, hznext, honext⟩ := release_finish_success
      i record.input.row record.input.time observation s post mem start (k + 1)
      hv hvpost hmpost hzpost hpreRecord hopost hoc
    have halign := record.output.preparation.follower_alignment i
    have hrecordPrepared : (ReferenceActivePhysicalStep.recordFollower view prepared.follower prepared.row
        prepared.activation prepared.time prepared.active prepared.arm observation s).result = .ok post := by
      simpa only [prepared, halign.1, halign.2.1, halign.2.2.1, halign.2.2.2] using hrecord
    have hfinishPrepared : DeclaredFollowerLocalRound.releaseAndFinish rate prepared.follower prepared.row prepared.time
        observation s mem post = .ok (next, nextMem) := by
      simpa only [prepared, halign.1, halign.2.1, halign.2.2.1] using hfinish
    have hsuccess := ReferenceActivePhysicalStep.finishFollower_success view prepared observation s post next mem nextMem
      hchoice hrecordPrepared hfinishPrepared
    have hobs : record.output.followers i = ReferenceActivePhysicalStep.finishFollower view prepared observation := by
      dsimp only [view, prepared, observation]
      rw [record.output_eq]
      rfl
    have hnextConfig : (record.output.followers i).configuration = .ordinary next nextMem := by
      rw [hobs]
      exact hsuccess.1
    have hfailure : (record.output.followers i).failure = none := by
      rw [hobs]
      exact hsuccess.2
    refine ⟨⟨next, nextMem, ?_, hvnext, hmnext, hznext, ?_⟩, ?_⟩
    · rw [hend]
      have hfields : record.output.next.followers i = (record.output.followers i).configuration := by
        rw [record.output_eq]
        rfl
      exact hfields.trans hnextConfig
    · intro h
      obtain ⟨M, hM, hMsigma, hread⟩ := honext h
      refine ⟨by omega, M, ⟨record.input.time,
        FollowerCutoffScan.completeRowProposalBit p rate.eta.val record.input.row record.input.time⟩,
        hM, hMsigma, hread, ?_, ?_⟩
      · simp only [ht]
        omega
      · simp only [hrow]
    · intro j hj
      by_cases hlt : j.val < k
      · exact hrecords j hlt
      · have he : j.val = k := by omega
        have hr : W[j.val] = record := by simp only [he, record]
        refine ⟨s, mem, next, nextMem, ?_, ?_, ?_⟩
        · rw [hr]
          exact hchoice
        · rw [hr]
          exact hnextConfig
        · rw [hr]
          exact hfailure


/-- Every endpoint and every actual CHOICE/OBSERVE in the first live window is
ordinary. The explicit initial boundary is the only follower-domain input.
The prefix span is produced from the real record count, including prefix zero
and an empty window. Occupied CHOICE fields name the actual selected payload.
This is internal first-window safety, not source queue or arrival truth. -/
theorem run_first_live_follower_safety
    (initial : ReferenceActivePhysicalHorizon.State p rate) (rows : CompletePublicTable.CompleteRows p)
    (J : Fin (M p)) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start) (hfirst : initial.coordinator = .first)
    (seed : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
    (memory : Fin (p.m - 1) → LocalMemory p)
    (hseed : ∀ i, initial.followers i = .ordinary (seed i) (memory i))
    (hS : ∀ i, (seed i).S = 0) (hdelta : ∀ i, (seed i).delta = 0)
    (hbacklog : ∀ i, (seed i).backlog = 0) (hnone : ∀ i, (seed i).lastDown = none)
    (hunoccupied : ∀ i, (seed i).status = .unoccupied)
    (hvalid : ∀ i, localBufferValid (seed i))
    (hpair : ∀ i, (seed i).buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound))
    (htime : ∀ i saved, saved ∈ (seed i).buffer → saved.calendarRound ≤ start)
    (hbatch : ∀ i, downDecoderStateValid (seed i)) :
    let E := ReferenceActivePhysicalHorizon.run initial rows J rewards start count hspan active
    let W := ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records
    (∀ k : ℕ, k ≤ W.length → ∃ hprefix : start + k ≤ p.T,
      ∀ i : Fin (p.m - 1), ∃ s mem,
        (ReferenceActivePhysicalHorizon.run initial rows J rewards start k hprefix active).finalState.followers i =
          .ordinary s mem ∧
        localStateDomainValid s ∧ s.S + s.backlog ≤ k * D p ∧
        s.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound) ∧
        (∀ saved ∈ s.buffer, saved.calendarRound < start + k + 1) ∧
        (s.status = .unoccupied →
          s.lastDown = none ∧ s.S = 0 ∧ s.delta = 0 ∧ s.backlog = 0) ∧
        (s.status ≠ .unoccupied → 0 < k ∧ ∃ M token,
          s.lastDown = some M ∧ M.val.sigma = start + 1 ∧
          mem.lastProposalRead = some token ∧ token.timestamp.val + 1 = start + k ∧
          token.bit = FollowerCutoffScan.completeRowProposalBit p rate.eta.val (rows J) token.timestamp)) ∧
    (∀ (k : Fin W.length) (i : Fin (p.m - 1)), ∃ choice choiceMemory next nextMemory,
      (W[k.val].output.preparation.followers.followers i).configuration = .ordinary choice choiceMemory ∧
      (W[k.val].output.followers i).configuration = .ordinary next nextMemory ∧
      (W[k.val].output.followers i).failure = none ∧
      ∀ selected : ReferenceActivePhysicalStep.Selection W[k.val].input,
        W[k.val].output.preparation.coordinator.selection = some selected →
        choice.status ≠ .unoccupied →
        choice.lastDown = some (selected.view.payload.downRecord i)) := by
  intro E W
  have hw : W.length ≤ count := by
    calc
      W.length ≤ E.records.length := (List.takeWhile_prefix _).length_le
      _ = count := ReferenceActivePhysicalHorizon.run_record_count initial rows J rewards start count hspan active
  have hsafe := fun i => prefix_follower_safety initial rows J rewards start count hspan active hfirst
    i (seed i) (memory i) (hseed i) (hS i) (hdelta i) (hbacklog i) (hnone i) (hunoccupied i)
    (hvalid i) (hpair i) (htime i) (hbatch i)
  constructor
  · intro k hk
    have hprefix : start + k ≤ p.T := (Nat.add_le_add_left (hk.trans hw) start).trans hspan
    refine ⟨hprefix, ?_⟩
    intro i
    obtain ⟨s, mem, hs, hv, hm, hz, ho⟩ := (hsafe i k hk hprefix).1
    have hchron := ReferenceFollowerBufferProvenance.run_buffer_chronological i initial rows J rewards
      start k hprefix active (seed i) (memory i) (hseed i) (hvalid i) (hpair i) (htime i) s mem hs
    exact ⟨s, mem, hs, hv, hm, hchron.2.1, hchron.2.2, hz, ho⟩
  · intro k i
    have hk : k.val + 1 ≤ W.length := Nat.succ_le_of_lt k.isLt
    have hprefix : start + (k.val + 1) ≤ p.T :=
      (Nat.add_le_add_left (hk.trans hw) start).trans hspan
    obtain ⟨choice, choiceMemory, next, nextMemory, hc, hn, hf⟩ :=
      (hsafe i (k.val + 1) hk hprefix).2 k (Nat.lt_succ_self _)
    refine ⟨choice, choiceMemory, next, nextMemory, hc, hn, hf, ?_⟩
    intro selected hs hoccupied
    have hinit : ReferenceFirstLiveConfirmationHistory.InitialFollowers initial := by
      intro j s mem hs
      rw [hseed j] at hs
      cases hs
      exact ⟨hunoccupied j, hnone j⟩
    have hcarried := ReferenceFirstLiveConfirmationHistory.run_firstLive_carried
      initial rows J rewards start count hspan active hfirst hinit k
    let record := W[k.val]
    have hnocut : ReferenceCollectionPhaseHistory.cutoffChosen record.input = false := by
      have hm : record ∈ W := List.getElem_mem k.isLt
      have h := List.mem_takeWhile_imp hm
      simpa only [Bool.not_eq_true'] using h
    have hselection : (ReferenceActivePhysicalStep.prepare record.input).coordinator.selection = some selected := by
      change record.output.preparation.coordinator.selection = some selected at hs
      simpa only [record.output_eq, ReferenceActivePhysicalStep.step] using hs
    have hchoice : ((ReferenceActivePhysicalStep.prepare record.input).followers.followers i).configuration =
        .ordinary choice choiceMemory := by
      change (record.output.preparation.followers.followers i).configuration =
        .ordinary choice choiceMemory at hc
      simpa only [record.output_eq, ReferenceActivePhysicalStep.step] using hc
    exact (ReferenceFirstLiveConfirmationHistory.selected_choice record.input hcarried hnocut selected hselection
      i choice choiceMemory hchoice).1 hoccupied

/-- The admitted replay characterization supplies the actual launch decoder
domain. Forced and unactivated branches use the literal initial batch. -/
private theorem initialization_ordinary_decoder
    (x : ReferenceInitializationRun.Input p) (b : ReferenceInitializationRun.Boundary p)
    (i : ActiveRoundActions.Follower p.m) :
    downDecoderStateValid (ReferenceInitializationRun.ordinary x b i) := by
  classical
  have hi : downDecoderStateValid (ReferencePrelaunchFollower.initial p x.eta) :=
    ⟨AffineBatchDecoder.quota_pos p, by simp [ReferencePrelaunchFollower.initial,
      AffineBatchDecoder.initial]⟩
  unfold ReferenceInitializationRun.ordinary
  split
  · exact hi
  · split
    · exact hi
    · rename_i activation _
      have h := ReferencePrelaunchFollower.replay_batch_spec x.eta
        (BootstrapPhysicalInput.sourceFollowerIndex p i) x.row activation
        (b.history (PublicDiscreteDraws.followerPlayer p.two_le_m i))
        (ReferenceInitializationRun.elapsed_le_T p b.completed)
      exact ⟨h.1, h.2.1⟩

section ActualLaunch

variable
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (rate : ReferenceActivePhysicalStep.RateInput p) (C_star C_h : ℝ)
    (b : ReferenceInitializationRun.Boundary p)
    (h : b.completed < BootstrapDimensions.n_boot p)
    (actual : ActualInitializationRun.BlockCarry p rate
      (ReferenceInitializationRun.nextBlock b h))
    (past : List (ActualInitializationRun.PhysicalRoundRecord p rate source rewards))
    (hr : ActualReferenceInitializationBlock.BlockStartRelated source rewards
      C_star C_h rate (ReferenceInitializationRun.nextBlock b h) actual b past)
    (hdown : ∀ i, ¬ InitializationFailureProvenance.generatedBlockDown
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate) b h i)
    (hclean : ∀ (i : Fin (p.m - 1))
      (hi : ActualReferenceInitializationBlock.refFollower i ∈
        (ReferenceInitializationRun.physical
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
          b h).uninformed),
      BootstrapAllCandidateController.cleanPrefix
        (ReferenceInitializationRun.physical
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
          b h)
        source.1.2 ⟨ActualReferenceInitializationBlock.refFollower i, hi⟩
        (ActualInitializationPhysicalStep.selectedRowIndex p source) p.T)
    (hforce : ∀ i, ReferenceInitializationRun.forced
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
      b h i = false)
    (launch : BootstrapCoordinatorLocalRound.LaunchedBlock p)
    (learnerSeed : ActualInitializationRun.CoordinatorLearnerZeroSeed p)
    (hlaunched : (ActualInitializationRun.combinedBoundaryHandoff p rate
      (ReferenceInitializationRun.nextBlock b h) source rewards actual.C_star actual.C_h
      (ActualInitializationRun.foldBlock p rate (ReferenceInitializationRun.nextBlock b h)
        source rewards actual)).disposition = .launched launch learnerSeed)

/-- Consume the actual launched boundary with its full original initialization
relation, clean-prefix, generated-DOWN exclusion, no-force and handoff telescope.
The original source rows, selected private J, block endpoint and inherited
buffers are retained. No source-totality claim follows from this adapter. -/
theorem actual_launched_first_live_follower_safety (count : ℕ)
    (hspan : BootstrapObservedFollower.blockStop p (ReferenceInitializationRun.nextBlock b h) +
      count ≤ p.T) :
    let initial := ActualInitializationLaunchState.ofActualLaunchedBoundary source rewards rate
      C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed hlaunched
    let start := BootstrapObservedFollower.blockStop p (ReferenceInitializationRun.nextBlock b h)
    let active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start := fun i =>
      ActualInitializationLaunchState.ofActualLaunchedBoundary_activation_le_blockStop
        source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed hlaunched i
    let E := ReferenceActivePhysicalHorizon.run initial source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start count hspan active
    let W := ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records
    (∀ k : ℕ, k ≤ W.length → ∃ hprefix : start + k ≤ p.T,
      ∀ i : Fin (p.m - 1), ∃ s mem,
        (ReferenceActivePhysicalHorizon.run initial source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start k hprefix active).finalState.followers i =
          .ordinary s mem ∧
        localStateDomainValid s ∧ s.S + s.backlog ≤ k * D p ∧
        s.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound) ∧
        (∀ saved ∈ s.buffer, saved.calendarRound < start + k + 1) ∧
        (s.status = .unoccupied →
          s.lastDown = none ∧ s.S = 0 ∧ s.delta = 0 ∧ s.backlog = 0) ∧
        (s.status ≠ .unoccupied → 0 < k ∧ ∃ M token,
          s.lastDown = some M ∧ M.val.sigma = start + 1 ∧
          mem.lastProposalRead = some token ∧ token.timestamp.val + 1 = start + k ∧
          token.bit = FollowerCutoffScan.completeRowProposalBit p rate.eta.val
            (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)) token.timestamp)) ∧
    (∀ (k : Fin W.length) (i : Fin (p.m - 1)), ∃ choice choiceMemory next nextMemory,
      (W[k.val].output.preparation.followers.followers i).configuration = .ordinary choice choiceMemory ∧
      (W[k.val].output.followers i).configuration = .ordinary next nextMemory ∧
      (W[k.val].output.followers i).failure = none ∧
      ∀ selected : ReferenceActivePhysicalStep.Selection W[k.val].input,
        W[k.val].output.preparation.coordinator.selection = some selected →
        choice.status ≠ .unoccupied →
        choice.lastDown = some (selected.view.payload.downRecord i)) := by
  classical
  intro initial start active E W
  have hfirst : initial.coordinator = .first :=
    ActualInitializationLaunchState.ofActualLaunchedBoundary_coordinator source rewards rate C_star C_h
      b h actual past hr hdown hclean hforce launch learnerSeed hlaunched
  have hseeds : ∀ i : Fin (p.m - 1), ∃ seed memory,
      initial.followers i = .ordinary seed memory ∧
      seed.S = 0 ∧ seed.delta = 0 ∧ seed.backlog = 0 ∧ seed.lastDown = none ∧
      seed.status = .unoccupied ∧ localBufferValid seed ∧
      seed.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound) ∧
      (∀ saved ∈ seed.buffer, saved.calendarRound ≤ start) ∧ downDecoderStateValid seed := by
    intro i
    obtain ⟨seed, memory, hseed, hS, hd, hb, hu, hn, hv, hp, ht⟩ :=
      ReferenceFirstFollowerMassBudget.actual_launched_follower_seed source rewards rate C_star C_h
        b h actual past hr hdown hclean hforce launch learnerSeed hlaunched i
    obtain ⟨state, mem, hconfig, hstate, _⟩ :=
      ActualInitializationLaunchState.ofActualLaunchedBoundary_follower_replay source rewards rate
        C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed hlaunched i
    have hsame : seed = state :=
      (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj (hseed.symm.trans hconfig)).1
    have hdecoder : downDecoderStateValid seed := by
      rw [hsame, hstate]
      exact initialization_ordinary_decoder _ _ _
    exact ⟨seed, memory, hseed, hS, hd, hb, hn, hu, hv, hp, ht, hdecoder⟩
  choose seed memory hseed hS hdelta hbacklog hnone hunoccupied hvalid hpair htime hbatch using hseeds
  exact run_first_live_follower_safety initial source.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start count hspan active hfirst
    seed memory hseed hS hdelta hbacklog hnone hunoccupied hvalid hpair htime hbatch

end ActualLaunch

end Bandits.Support.ReferenceFirstLiveFollowerSafety

end
