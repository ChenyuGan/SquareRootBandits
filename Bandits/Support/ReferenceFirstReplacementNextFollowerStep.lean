/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstReplacementDownRecovery
public import Bandits.Support.ReferenceLaterLiveNumericalReadout

/-!
# The first replacement's next follower preparation and occupied service

Sources: `sources/zip4/manuscript/06_interruptions.tex:9-70,193-233,246-295`,
`sources/zip4/manuscript/05_binary_transport.tex:354-431`,
`sources/zip4/manuscript/04_slow_fast_learner.tex:157-188`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-79`.

These internal producers retain the original complete physical execution,
whole reward table, and unrestricted shared constants. They connect only the
first replacement record to its actual calendar successor; absence of that
successor remains a genuine terminal case. They do not assert that the
continuing coordinator branch or any observation tail occurs. The next consumers
are first-successor unoccupied DOWN replay from the original nonzero-capable
queue, and later replacement live-prefix induction; neither is implemented here.
-/

@[expose] public section
noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceAssignmentPayloadChronology
open Bandits.Support.ActiveRoundActions
open Bandits.Support.PublicDiscreteDraws

namespace Bandits.Support.ReferenceFirstReplacementNextFollowerStep

open ReferenceActivePhysicalStep ReferenceLaterLiveNumericalReadout ActiveFollowerLifecycle

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

/-- Project the literal queue input domain from the complete local-state
domain used by the actual start operation. -/
private theorem queueInputDomain_of_localStateDomainValid
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (h : ActiveFollowerLifecycle.localStateDomainValid state) :
    ActiveFollowerQueueOperation.stateInputDomain state :=
  ⟨h.1.1, h.1.2.1, h.1.2.2, h.2.1.1, h.2.1.2.1⟩

/-- Consecutive indexed records in the canonical physical run share the
literal state transition and consecutive original calendar coordinates. -/
private theorem actualRunRecordAt_successor_input
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start index : ℕ)
    (hspan : start + (index + 2) ≤ p.T)
    (hmode : allActiveAtStart initial start) :
    let previous := actualRunRecordAt initial rows J rewards start index (by omega) hmode
    let next := actualRunRecordAt initial rows J rewards start (index + 1) hspan hmode
    next.input.state = previous.output.next ∧
      next.input.time.val = previous.input.time.val + 1 := by
  dsimp only
  have hspanPrevious : start + (index + 1) ≤ p.T := by omega
  have hstate := run_successor_finalState_eq_actualRunRecordAt initial rows J rewards
    start index hspanPrevious hmode
  constructor
  · change (ReferenceActivePhysicalHorizon.run initial rows J rewards start
      (index + 1) (by omega) hmode).finalState =
        (actualRunRecordAt initial rows J rewards start index hspanPrevious hmode).output.next
    exact hstate
  · change start + (index + 1) = (start + index) + 1
    omega

/-- The first replacement has only the successor supplied by the complete
physical suffix. If it exists, both records are the adjacent original-run
records from the same launch and prefix; no terminal successor is filled in. -/
theorem complete_first_replacement_actual_successor
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
    let Cwin := ReferenceCollectionPhaseHistory.collectionWindow R w
    let v := w + Cwin.length
    match R[v]? with
    | none => True
    | some r0 => match R[v + 1]? with
      | none => True
      | some r1 =>
        ∃ (hc : (ReferenceInitializationRun.output
            (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
          (h0 : ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h +
            (v + 1) ≤ p.T)
          (h1 : ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h +
            (v + 2) ≤ p.T),
          r0 = ReferenceAssignmentPayloadChronology.actualRunRecordAt
            (ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hc)
            source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
            (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
            v h0 (ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
              rate source rewards C_star C_h hc).activeAtStart ∧
          r1 = ReferenceAssignmentPayloadChronology.actualRunRecordAt
            (ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hc)
            source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
            (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
            (v + 1) h1 (ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
              rate source rewards C_star C_h hc).activeAtStart ∧
          r1.input.state = r0.output.next ∧
          r1.input.time.val = r0.input.time.val + 1 := by
  classical
  intro R w Cwin v
  cases hget0 : R[v]? with
  | none => trivial
  | some r0 =>
    cases hget1 : R[v + 1]? with
    | none => trivial
    | some r1 =>
      have hindex0 := List.getElem?_eq_some_iff.mp hget0
      have hindex1 := List.getElem?_eq_some_iff.mp hget1
      obtain ⟨hv0, hindexValue0⟩ := hindex0
      obtain ⟨hv1, hindexValue1⟩ := hindex1
      let k0 : Fin R.length := ⟨v, hv0⟩
      let k1 : Fin R.length := ⟨v + 1, hv1⟩
      have hvalue0 : R.get k0 = r0 := by
        simp only [k0, List.get_eq_getElem]
        exact hindexValue0
      have hvalue1 : R.get k1 = r1 := by
        simp only [k1, List.get_eq_getElem]
        exact hindexValue1
      obtain ⟨hc0, hspan0, hp0⟩ := ReferenceLaterLiveNumericalReadout.source_record_prefix
        rate rewards C_star C_h source k0
      obtain ⟨hc1, hspan1, hp1⟩ := ReferenceLaterLiveNumericalReadout.source_record_prefix
        rate rewards C_star C_h source k1
      have hprefixSame : hc0 = hc1 := Subsingleton.elim _ _
      rw [← hprefixSame] at hp1
      have hadj := actualRunRecordAt_successor_input
        (ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hc0)
        source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
        (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
        v hspan1 (ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
          rate source rewards C_star C_h hc0).activeAtStart
      have hstate' : r1.input.state = r0.output.next := by
        rw [← hvalue1, ← hvalue0, hp1, hp0]
        exact hadj.1
      have htime' : r1.input.time.val = r0.input.time.val + 1 := by
        rw [← hvalue1, ← hvalue0, hp1, hp0]
        exact hadj.2
      refine ⟨hc0, ?_, ?_, ?_, ?_, hstate', htime'⟩
      · dsimp [k0] at hspan0
        exact hspan0
      · dsimp [k1] at hspan1
        exact hspan1
      · rw [← hvalue0]
        exact hp0
      · rw [← hvalue1]
        exact hp1

/-- Enabled occupied service succeeds from the actual local domains and
calendar mass credit. The raw arrival is computed from the current complete
row; the cap and conservation come from the literal capped service. -/
private theorem checkedService_success_from_credit
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (activation : ReferencePrelaunchFollower.Activation p) (time : Fin p.T)
    (observation : ReferencePrelaunchFollower.Observation p)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (hoccupied : state.status ≠ ActiveRoundActions.FollowerStatus.unoccupied)
    (hdomain : ActiveFollowerQueueOperation.stateInputDomain state)
    (M : OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (hdown : state.lastDown = some M)
    (hactive : activation.val ≤ time.val + 1)
    (hcredit : state.S + state.backlog ≤ time.val * D p) :
    ∃ serviced : ActiveFollowerQueueOperation.ServiceSuccess p rate.eta rate.n i row
        activation time observation state,
      ActiveFollowerQueueOperation.checkedService rate.eta rate.sourceCap rate.n
        rate.n_scale i row activation time observation state = .success serviced := by
  classical
  let arrival := ActiveFollowerQueueOperation.rawArrival rate.eta i row time M observation
  let service := ActiveFollowerQueueOperation.localService rate.n state.backlog arrival
  have harrival : arrival ≤ D p := by
    exact ActiveFollowerQueueOperation.rawArrival_le_D rate.eta i row time M observation
  have hserviceCapacity := ActiveFollowerDownAcceptance.four_n_le_D p rate
  have hservice : service ≤ D p := by
    dsimp [service, ActiveFollowerQueueOperation.localService,
      ActiveFollowerQueueOperation.serviceCapacity]
    exact (CappedService.service_le_capacity (4 * rate.n) state.backlog arrival).trans
      hserviceCapacity
  have hserviceTotal : service ≤ state.backlog + arrival := by
    dsimp [service, ActiveFollowerQueueOperation.localService,
      ActiveFollowerQueueOperation.serviceCapacity]
    exact CappedService.service_le_total (4 * rate.n) state.backlog arrival
  have htimeBound : time.val + 1 ≤ p.T := by omega
  have hscore : state.S + service ≤ p.T * D p := by
    calc
      state.S + service ≤ state.S + (state.backlog + arrival) := Nat.add_le_add_left hserviceTotal _
      _ ≤ time.val * D p + D p := by omega
      _ = (time.val + 1) * D p := by rw [Nat.add_mul]; simp
      _ ≤ p.T * D p := Nat.mul_le_mul_right (D p) htimeBound
  have hbacklog : CappedService.residual (4 * rate.n) state.backlog arrival ≤ p.T * D p := by
    calc
      CappedService.residual (4 * rate.n) state.backlog arrival ≤ state.backlog + arrival :=
        Nat.sub_le _ _
      _ ≤ time.val * D p + D p := by omega
      _ = (time.val + 1) * D p := by rw [Nat.add_mul]; simp
      _ ≤ p.T * D p := Nat.mul_le_mul_right (D p) htimeBound
  have houtput : ActiveFollowerQueueOperation.outputDomain rate.n state arrival service :=
    ⟨harrival, hservice, hscore, hbacklog⟩
  have hcap : ActiveFollowerQueueOperation.sourceRateCapped p rate.eta := rate.sourceCap
  have hthin : ActiveFollowerQueueOperation.thinningProbabilityDomain rate.eta M :=
    ActiveFollowerQueueOperation.thinningProbability_domain rate.eta M
  have houtput' : ActiveFollowerQueueOperation.outputDomain rate.n state
      (ActiveFollowerQueueOperation.rawArrival rate.eta i row time M observation)
      (ActiveFollowerQueueOperation.localService rate.n state.backlog
        (ActiveFollowerQueueOperation.rawArrival rate.eta i row time M observation)) := by
    simpa [arrival, service] using houtput
  have hexists : ∃ serviced,
      ActiveFollowerQueueOperation.checkedService rate.eta rate.sourceCap rate.n rate.n_scale
        i row activation time observation state = .success serviced := by
    unfold ActiveFollowerQueueOperation.checkedService
    rw [dite_eq_left hdomain]
    split
    · rename_i hstatus
      exact False.elim (hoccupied hstatus)
    · rw [dite_eq_left hactive]
      split
      · rename_i hmissing
        rw [hdown] at hmissing
        cases hmissing
      · rename_i M' hM'
        have heq := Option.some.inj (hM'.symm.trans hdown)
        subst M'
        rw [dite_eq_left hthin, dite_eq_left houtput']
        exact ⟨_, rfl⟩
    · rw [dite_eq_left hactive]
      split
      · rename_i hmissing
        rw [hdown] at hmissing
        cases hmissing
      · rename_i M' hM'
        have heq := Option.some.inj (hM'.symm.trans hdown)
        subst M'
        rw [dite_eq_left hthin, dite_eq_left houtput']
        exact ⟨_, rfl⟩
  obtain ⟨serviced, hserviced⟩ := hexists
  exact ⟨serviced, hserviced⟩

/-- The literal PREPARE constructor produces an ordinary configuration from
an actual successful start, local domains, the source unoccupied placeholder
or positive accepted start, and an existing accepted DOWN on occupied states.
Callers must produce these branch facts from their physical predecessor. -/
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

/-- A newly accepted DOWN starts at this calendar coordinate. Its genuine
proposal token is the immediately preceding row's read, so the literal start
operation succeeds and exposes precisely its grid/proposal interruption bit. -/
private theorem fresh_pending_startRound_success
    (time : Fin p.T) (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (M : OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (token : ActiveFollowerLifecycle.ProposalRead p)
    (hstatus : state.status = ActiveRoundActions.FollowerStatus.pending)
    (hdomain : ActiveFollowerLifecycle.localStateDomainValid state)
    (hdown : state.lastDown = some M)
    (hsigma : M.val.sigma = time.val)
    (hread : memory.lastProposalRead = some token)
    (hstamp : token.timestamp.val + 1 = time.val) :
    ∃ started,
      ActiveFollowerLifecycle.startRound rate.eta time state memory = .ok (started, memory) ∧
      (started.status = if (FollowerCutoffScan.gridBoundary p rate.eta.val
            (ActiveFollowerLifecycle.acceptedStartCoordinate M) = time.val + 1 || token.bit)
        then .unoccupied else .pending) ∧
      started.lastDown = state.lastDown ∧ started.S = state.S ∧
      started.delta = state.delta ∧ started.backlog = state.backlog ∧
      started.buffer = state.buffer ∧ started.downBatch = state.downBatch ∧
      started.initializationFailure = state.initializationFailure := by
  have hcoordinate : (ActiveFollowerLifecycle.acceptedStartCoordinate M).val + 1 = time.val := by
    have hpositive := M.property.1
    change M.val.sigma - 1 + 1 = time.val
    rw [hsigma]
    omega
  have hgrid := FollowerCutoffScan.gridBoundary_bounds p rate.eta.val
    rate.eta.property rate.sourceCap (ActiveFollowerLifecycle.acceptedStartCoordinate M)
  have hnotmissed : time.val + 1 ≤ FollowerCutoffScan.gridBoundary p rate.eta.val
      (ActiveFollowerLifecycle.acceptedStartCoordinate M) := by omega
  have hprior : ActiveFollowerLifecycle.isPriorProposalRead time token := by
    change token.timestamp.val + 1 = time.val
    exact hstamp
  let started : ReferencePrelaunchFollower.State p rate.eta :=
    { state with status := if (FollowerCutoffScan.gridBoundary p rate.eta.val
        (ActiveFollowerLifecycle.acceptedStartCoordinate M) = time.val + 1 || token.bit)
      then .unoccupied else .pending }
  have hstatusNe : state.status ≠ ActiveRoundActions.FollowerStatus.unoccupied := by
    rw [hstatus]
    decide
  have hstart := ActiveFollowerLifecycle.startRound_occupied_branch rate.eta time state memory
    hstatusNe hdomain M hdown (by omega) hnotmissed token hread hprior
  have hstart' : ActiveFollowerLifecycle.startRound rate.eta time state memory =
      .ok (started, memory) := by
    simpa [started, hstatus] using hstart
  rcases ActiveFollowerLifecycle.startRound_frame rate.eta time state started memory memory hstart' with
    ⟨hlast, hS, hdelta, hbacklog, hbatch, hbuffer, hfailure, _⟩
  exact ⟨started, hstart', rfl, hlast, hS, hdelta,
    hbacklog, hbuffer, hbatch, hfailure⟩

/-- The ordinary occupied service output is the actual capped update. It
retains the accepted record, all sparse and decoder state, and the original
initialization-failure flag. -/
private theorem checkedService_success_frame
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (activation : ReferencePrelaunchFollower.Activation p) (time : Fin p.T)
    (observation : ReferencePrelaunchFollower.Observation p)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (serviced : ActiveFollowerQueueOperation.ServiceSuccess p rate.eta rate.n i row
      activation time observation state)
    (hoccupied : state.status ≠ ActiveRoundActions.FollowerStatus.unoccupied)
    (M : OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (hdown : state.lastDown = some M) :
    serviced.output = ActiveFollowerQueueOperation.serviceUpdate rate.n state serviced.arrival ∧
      serviced.output.status = state.status ∧ serviced.output.lastDown = state.lastDown ∧
      serviced.output.S = state.S + serviced.service ∧
      serviced.output.delta = serviced.service ∧
      serviced.output.backlog = CappedService.residual
        (ActiveFollowerQueueOperation.serviceCapacity rate.n) state.backlog serviced.arrival ∧
      serviced.output.buffer = state.buffer ∧ serviced.output.downBatch = state.downBatch ∧
      serviced.output.initializationFailure = state.initializationFailure ∧
      serviced.arrival = ActiveFollowerQueueOperation.rawArrival rate.eta i row time M observation ∧
      serviced.service = ActiveFollowerQueueOperation.localService rate.n state.backlog serviced.arrival := by
  have hserviceAction := serviced.action
  have harrival : serviced.arrival =
      ActiveFollowerQueueOperation.rawArrival rate.eta i row time M observation := by
    cases hstatus : state.status with
    | unoccupied => exact (hoccupied hstatus).elim
    | pending =>
        simp only [ActiveFollowerQueueOperation.serviceAction, hstatus] at hserviceAction
        obtain ⟨_, M', hM', _, harrival, _⟩ := hserviceAction
        have heq := Option.some.inj (hM'.symm.trans hdown)
        subst M'
        exact harrival
    | released =>
        simp only [ActiveFollowerQueueOperation.serviceAction, hstatus] at hserviceAction
        obtain ⟨_, M', hM', _, harrival, _⟩ := hserviceAction
        have heq := Option.some.inj (hM'.symm.trans hdown)
        subst M'
        exact harrival
  have hservice : serviced.service =
      ActiveFollowerQueueOperation.localService rate.n state.backlog serviced.arrival := by
    cases hstatus : state.status with
    | unoccupied => exact (hoccupied hstatus).elim
    | pending =>
        simp only [ActiveFollowerQueueOperation.serviceAction, hstatus] at hserviceAction
        obtain ⟨_, _, _, _, _, hservice⟩ := hserviceAction
        exact hservice
    | released =>
        simp only [ActiveFollowerQueueOperation.serviceAction, hstatus] at hserviceAction
        obtain ⟨_, _, _, _, _, hservice⟩ := hserviceAction
        exact hservice
  have hstateOccupied : state.status.occupied := by
    cases hstatus : state.status <;> simp_all [ActiveRoundActions.FollowerStatus.occupied]
  rw [serviced.queueUpdate, hservice]
  simp [ActiveFollowerQueueOperation.serviceOutput, hstateOccupied,
    ActiveFollowerQueueOperation.serviceUpdate, ActiveFollowerQueueOperation.localService,
    harrival]

/-- A reached occupied follower's literal service, release, and finish
composition succeeds. Its output is the physical observation record; every
queue, buffer, decoder, and initialization field is retained, and EndRound
stores this row's actual proposal bit. -/
theorem occupied_actual_follower_finish
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1)) (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hprepared : (record.output.preparation.followers.followers i).configuration =
      .ordinary state memory)
    (hoccupied : state.status ≠ ActiveRoundActions.FollowerStatus.unoccupied)
    (hdomain : ActiveFollowerLifecycle.localStateDomainValid state)
    (M : OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (hdown : state.lastDown = some M)
    (htime : M.val.sigma ≤ record.input.time.val)
    (hcredit : state.S + state.backlog ≤ record.input.time.val * D p) :
    ∃ serviced next,
      ActiveFollowerQueueOperation.checkedService rate.eta rate.sourceCap rate.n
        rate.n_scale i record.input.row (record.input.state.activations i) record.input.time
        (record.output.preparation.feedback.observations
          (PublicDiscreteDraws.followerPlayer p.two_le_m i)) state = .success serviced ∧
      (ReferenceActivePhysicalStep.recordFollower record.output.preparation.coordinator.downView
        i record.input.row (record.input.state.activations i) record.input.time
        (record.input.active i) (record.output.preparation.followers.followers i).arm
        (record.output.preparation.feedback.observations
          (PublicDiscreteDraws.followerPlayer p.two_le_m i)) state).result = .ok serviced.output ∧
      DeclaredFollowerLocalRound.releaseAndFinish rate i record.input.row record.input.time
        (record.output.preparation.feedback.observations
          (PublicDiscreteDraws.followerPlayer p.two_le_m i)) state memory serviced.output =
        .ok (next, ⟨some ⟨record.input.time,
          FollowerCutoffScan.completeRowProposalBit p rate.eta.val record.input.row
            record.input.time⟩⟩) ∧
      record.output.followers i = ⟨.ordinary next
        ⟨some ⟨record.input.time,
          FollowerCutoffScan.completeRowProposalBit p rate.eta.val record.input.row
            record.input.time⟩⟩, none, none, none⟩ ∧
      ActiveFollowerLifecycle.localStateDomainValid next ∧
      next.S + next.backlog ≤ (record.input.time.val + 1) * D p ∧
      next.delta ≤ D p ∧ next.lastDown = state.lastDown ∧
      next.downBatch = state.downBatch ∧ next.buffer = state.buffer ∧
      next.initializationFailure = state.initializationFailure := by
  classical
  let prepared := record.output.preparation.followers.followers i
  let observation := record.output.preparation.feedback.observations
    (PublicDiscreteDraws.followerPlayer p.two_le_m i)
  let view := record.output.preparation.coordinator.downView
  let follower : ActiveRoundActions.Follower p.m := i
  have hstateDomain := hdomain
  have hqueueDomain := queueInputDomain_of_localStateDomainValid state hdomain
  rcases hdomain with ⟨hregisters, hbuffer, hbatch⟩
  obtain ⟨serviced, hchecked⟩ := checkedService_success_from_credit i record.input.row
    (record.input.state.activations i) record.input.time observation state hoccupied
    hqueueDomain M hdown (record.input.active i) hcredit
  rcases checkedService_success_frame i record.input.row
      (record.input.state.activations i) record.input.time observation state serviced
      hoccupied M hdown with
    ⟨hupdate, hpostStatus, hpostDown, hpostS, hpostDelta, hpostBacklog,
      hpostBuffer, hpostBatch, hpostFailure, harrival, hservice⟩
  let post := serviced.output
  have hpostDomain : ActiveFollowerLifecycle.localStateDomainValid post := by
    change ActiveFollowerLifecycle.serviceRegistersValid p post ∧
      ActiveFollowerLifecycle.localBufferValid post ∧
        ActiveFollowerLifecycle.downDecoderStateValid post
    unfold ActiveFollowerLifecycle.serviceRegistersValid
    refine ⟨⟨serviced.score_le_TD, ?_, serviced.backlog_le_TD⟩, ?_, ?_⟩
    · rw [hpostDelta]
      exact serviced.service_le_D
    · unfold ActiveFollowerLifecycle.localBufferValid at hbuffer ⊢
      rw [hpostBuffer]
      exact hbuffer
    · unfold ActiveFollowerLifecycle.downDecoderStateValid at hbatch ⊢
      rw [hpostBatch]
      exact hbatch
  have hpostMass : post.S + post.backlog ≤ (record.input.time.val + 1) * D p := by
    have hconserve :
        CappedService.residual (ActiveFollowerQueueOperation.serviceCapacity rate.n)
            state.backlog serviced.arrival + serviced.service =
          state.backlog + serviced.arrival := by
      calc
        CappedService.residual (ActiveFollowerQueueOperation.serviceCapacity rate.n)
              state.backlog serviced.arrival + serviced.service =
            CappedService.residual (4 * rate.n) state.backlog serviced.arrival +
              CappedService.service (4 * rate.n) state.backlog serviced.arrival := by
                simp [ActiveFollowerQueueOperation.serviceCapacity,
                  ActiveFollowerQueueOperation.localService, hservice]
        _ = state.backlog + serviced.arrival :=
          CappedService.residual_add_service (4 * rate.n) state.backlog serviced.arrival
    rw [hpostS, hpostBacklog]
    calc
      state.S + serviced.service +
          CappedService.residual (ActiveFollowerQueueOperation.serviceCapacity rate.n)
            state.backlog serviced.arrival ≤ state.S + (state.backlog + serviced.arrival) := by
              omega
      _ ≤ record.input.time.val * D p + D p := by
        have harrivalBound := serviced.arrival_le_D
        omega
      _ = (record.input.time.val + 1) * D p := by
        rw [Nat.add_mul]
        simp
  have hpostRecord :
      (¬ ActiveFollowerLifecycle.releaseCondition rate.eta follower
          (ActiveFollowerLifecycle.publicRowOfCompleteRow record.input.row record.input.time)
          (record.output.preparation.feedback.observations
            (PublicDiscreteDraws.followerPlayer p.two_le_m i)) M ∧
        post.status = .unoccupied) ∨
      ∃ M', post.lastDown = some M' ∧ M'.val.sigma ≤ record.input.time.val + 1 := by
    have hpostDownM : post.lastDown = some M := by
      calc
        post.lastDown = state.lastDown := by simpa [post] using hpostDown
        _ = some M := hdown
    exact Or.inr ⟨M, hpostDownM, by omega⟩
  have hrecordStage :
      (ReferenceActivePhysicalStep.recordFollower view i record.input.row
        (record.input.state.activations i) record.input.time (record.input.active i)
        prepared.arm observation state).result = .ok post := by
    simp only [ReferenceActivePhysicalStep.recordFollower, dite_eq_right hoccupied]
    rw [DeclaredFollowerLocalRound.recordOrServiceThenDown_occupied rate i record.input.row
      (record.input.state.activations i) record.input.time (record.input.active i)
      prepared.arm observation state hoccupied, hchecked]
  have hpostStatus' : post.status = state.status := by simpa [post] using hpostStatus
  have hpostDownM : post.lastDown = some M := by
    calc
      post.lastDown = state.lastDown := by simpa [post] using hpostDown
      _ = some M := hdown
  have hpostDeltaBound : post.delta ≤ D p := by
    change serviced.output.delta ≤ D p
    rw [hpostDelta]
    exact serviced.service_le_D
  let nextMemory : ActiveFollowerLifecycle.LocalMemory p :=
    ⟨some ⟨record.input.time,
      FollowerCutoffScan.completeRowProposalBit p rate.eta.val record.input.row
        record.input.time⟩⟩
  have hfinish : ∃ next,
      DeclaredFollowerLocalRound.releaseAndFinish rate i record.input.row record.input.time
        observation state memory post = .ok (next, nextMemory) ∧
      ActiveFollowerLifecycle.localStateDomainValid next ∧
      next.S + next.backlog ≤ (record.input.time.val + 1) * D p ∧
      next.delta ≤ D p ∧ next.lastDown = state.lastDown ∧
      next.downBatch = state.downBatch ∧ next.buffer = state.buffer ∧
      next.initializationFailure = state.initializationFailure := by
    let test := state.status = .pending ∧ ActiveFollowerLifecycle.releaseCondition
      rate.eta follower (ActiveFollowerLifecycle.publicRowOfCompleteRow record.input.row
        record.input.time) observation M
    let next := if test then {post with status := .released} else post
    have hrelease : ActiveFollowerLifecycle.releaseAfterService rate.eta i record.input.time
        (ActiveFollowerLifecycle.publicRowOfCompleteRow record.input.row record.input.time)
        observation state post = .ok next := by
      by_cases hpending : state.status = .pending
      · rw [ActiveFollowerLifecycle.releaseAfterService_pending_branch rate.eta i
          record.input.time _ observation state post hpending hstateDomain M hdown htime
          hpostDomain hpostRecord]
        simp only [next, test, hpending, true_and, follower]
      · rw [ActiveFollowerLifecycle.releaseAfterService_not_pending rate.eta i
          record.input.time _ observation state post hpending]
        simp only [next, test, hpending, false_and, ite_false]
    have hnextDomain : ActiveFollowerLifecycle.localStateDomainValid next := by
      dsimp only [next]
      split_ifs <;> simpa only [ActiveFollowerLifecycle.localStateDomainValid,
        ActiveFollowerLifecycle.serviceRegistersValid, ActiveFollowerLifecycle.localBufferValid,
        ActiveFollowerLifecycle.downDecoderStateValid] using hpostDomain
    have hnextOccupied : next.status ≠ .unoccupied := by
      by_cases htest : test
      · simp only [next, ite_eq_left htest]; decide
      · simpa only [next, ite_eq_right htest, hpostStatus'] using hoccupied
    have hnextDown : next.lastDown = some M := by
      dsimp only [next]
      split_ifs <;> exact hpostDownM
    have hround := ActiveFollowerLifecycle.finishRound_occupied_read rate.eta record.input.time
      record.input.row next memory hnextOccupied hnextDomain M hnextDown (by omega)
    refine ⟨next, ?_, hnextDomain, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [DeclaredFollowerLocalRound.releaseAndFinish, hrelease, hround]
      rfl
    all_goals
      dsimp only [next]
      split_ifs <;> assumption
  obtain ⟨next, htail, hnextDomain, hnextMass, hnextDelta, hnextDown,
    hnextBatch, hnextBuffer, hnextFailure⟩ := hfinish
  have halign := record.output.preparation.follower_alignment i
  have hrecordPrepared :
      (ReferenceActivePhysicalStep.recordFollower view prepared.follower prepared.row
        prepared.activation prepared.time prepared.active prepared.arm observation state).result =
        .ok post := by
    simpa [prepared, view, observation, halign.1, halign.2.1, halign.2.2.1,
      halign.2.2.2] using hrecordStage
  have hrecordPreparedStage :
      DeclaredFollowerLocalRound.recordOrServiceThenDown rate prepared.follower
        prepared.row prepared.activation prepared.time prepared.active prepared.arm
        observation state = .ok post := by
    simpa [ReferenceActivePhysicalStep.recordFollower, prepared, view, observation,
      halign.1, halign.2.1, halign.2.2.1, halign.2.2.2, hoccupied] using hrecordPrepared
  have htailPrepared :
      DeclaredFollowerLocalRound.releaseAndFinish rate prepared.follower prepared.row
        prepared.time observation state memory post = .ok (next, nextMemory) := by
    simpa [prepared, halign.1, halign.2.1, halign.2.2.1] using htail
  have hactual : record.output.followers i =
      ReferenceActivePhysicalStep.finishFollower view prepared observation := by
    dsimp [view, prepared, observation]
    rw [record.output_eq]
    rfl
  have houtput : record.output.followers i =
      ⟨.ordinary next nextMemory, none, none, none⟩ := by
    rw [hactual]
    simp [ReferenceActivePhysicalStep.finishFollower, prepared, observation,
      hprepared, hrecordPreparedStage, htailPrepared,
      ReferenceActivePhysicalStep.recordFollower, hoccupied]
  refine ⟨serviced, next, hchecked, hrecordStage, htail, ?_, hnextDomain,
    hnextMass, hnextDelta, hnextDown, hnextBatch, hnextBuffer, hnextFailure⟩
  exact houtput

/-- After the actual first-replacement record, every present next suffix record
prepares from the state produced by the preceding physical step. The optional
successor and every local start/offer/arm result are produced from the two
admitted public roots and the literal constructors. -/
theorem complete_first_replacement_next_preparation_and_occupied_step
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
    let s := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
    let Cwin := ReferenceCollectionPhaseHistory.collectionWindow R w
    let v := w + Cwin.length
    match R[v]? with
    | none => True
    | some record => match record.output.preparation.coordinator with
      | .collection _oldPayload _ledger _ _ (.laterChosen _ _ _ _ _ _ _ _ _ installed _) =>
        match R[v + 1]? with
        | none => True
        | some nextRecord =>
          s < record.input.time.val ∧
          ∀ i : Fin (p.m - 1),
            ∃ state memory,
              (nextRecord.output.preparation.followers.followers i).configuration =
                .ordinary state memory ∧
              ActiveFollowerLifecycle.localStateDomainValid state ∧
              state.S + state.backlog ≤ nextRecord.input.time.val * D p ∧
              (state.status ≠ .unoccupied →
                state.lastDown = some (installed.registers.payload.downRecord i) ∧
                (installed.registers.payload.downRecord i).val.sigma = nextRecord.input.time.val ∧
                ∃ serviced next,
                  ActiveFollowerQueueOperation.checkedService rate.eta rate.sourceCap rate.n
                    rate.n_scale i nextRecord.input.row (nextRecord.input.state.activations i)
                    nextRecord.input.time (nextRecord.output.preparation.feedback.observations
                      (followerPlayer p.two_le_m i)) state = .success serviced ∧
                  nextRecord.output.followers i = ⟨.ordinary next
                    ⟨some ⟨nextRecord.input.time, FollowerCutoffScan.completeRowProposalBit
                      p rate.eta.val nextRecord.input.row nextRecord.input.time⟩⟩, none, none, none⟩ ∧
                  ActiveFollowerLifecycle.localStateDomainValid next ∧
                  next.S + next.backlog ≤ (nextRecord.input.time.val + 1) * D p ∧
                  next.delta ≤ D p ∧ next.lastDown = state.lastDown ∧
                  next.downBatch = state.downBatch ∧ next.buffer = state.buffer ∧
                  next.initializationFailure = state.initializationFailure) ∧
              ∃ before,
                ActiveFollowerLifecycle.localStateDomainValid before ∧
                (record.output.followers i).configuration = .ordinary before memory ∧
                nextRecord.input.state.followers i = .ordinary before memory ∧
                ActiveFollowerLifecycle.startRound rate.eta nextRecord.input.time before memory =
                  .ok (state, memory) ∧
                (before.status = .unoccupied ∨
                  before.status = .pending ∧
                  before.lastDown = some (installed.registers.payload.downRecord i) ∧
                  memory.lastProposalRead = some ⟨record.input.time,
                    FollowerCutoffScan.completeRowProposalBit p rate.eta.val
                      record.input.row record.input.time⟩)
      | _ => True := by
  classical
  have hroot := ReferenceFirstReplacementDownRecovery.complete_first_replacement_down_recovery_and_finish
    rate source rewards C_star C_h
  have hseed := ReferenceFirstReplacementFollowerLoggingSeed.complete_first_replacement_follower_logging_seed
    rate source rewards C_star C_h
  dsimp only at hroot hseed ⊢
  set R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
  set s := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
  set w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
  set Cwin := ReferenceCollectionPhaseHistory.collectionWindow R w
  set v := w + Cwin.length
  cases hget : R[v]? with
  | none => trivial
  | some record =>
    simp only [hget] at hroot hseed ⊢
    cases hcut : record.output.preparation.coordinator with
    | first outcome => trivial
    | live registers owned base outcome => trivial
    | invalidCollectionCutoff => trivial
    | dagger => trivial
    | collection oldPayload ledger clock cutoff outcome =>
      rw [hcut] at hroot hseed
      cases outcome with
      | clockFailure _ _ => trivial
      | localFailure _ _ _ _ => trivial
      | coreFailure _ _ _ _ => trivial
      | continuing _ _ _ _ => trivial
      | laterReconstructionFailure _ _ _ _ _ _ _ _ => trivial
      | laterPrefixFailure _ _ _ _ _ _ _ _ _ => trivial
      | laterOrientationFailure _ _ _ _ _ _ _ => trivial
      | laterChoiceFailure _ _ _ _ _ _ _ _ _ => trivial
      | laterChosen core consistent started hs instruction hinstruction output hcons
          clockData installed arm =>
        obtain ⟨hstart, hfollowers⟩ := hroot
        rcases hseed with ⟨_, _, _, _, _, _, _, hseedFollowers⟩
        cases hnextGet : R[v + 1]? with
        | none => trivial
        | some nextRecord =>
          have hsuccessor := complete_first_replacement_actual_successor
            rate source rewards C_star C_h
          simp only [R, w, Cwin, v, hget, hnextGet] at hsuccessor
          rcases hsuccessor with
            ⟨_hc, _hspan0, _hspan1, _hrecord0, _hrecord1, hstate, hcalendar⟩
          refine ⟨hstart, ?_⟩
          intro i
          obtain ⟨old, oldMemory, logged, hstateOld, hstatusOld,
            hconfigurationOld, hrest⟩ := hfollowers i
          obtain ⟨oldSeed, memorySeed, loggedSeed, hstateSeed, hstatusSeed,
            _hdomainSeed, _hbufferSeed, _hdecoderSeed, _hendpointSeed, _hmassSeed,
            _htimestampsSeed, _hkeysSeed, _hquantizedSeed, _hpairwiseSeed,
            _hbeforeSeed, hzeroSeed, _hseedTail⟩ := hseedFollowers i
          have hsameState := hstateOld.symm.trans hstateSeed
          simp only [DeclaredFollowerLocalRound.LocalConfiguration.ordinary.injEq] at hsameState
          rcases hsameState with ⟨rfl, rfl⟩
          rcases hrest with
            ⟨hlogging, _hoperationDomain, _hacceptedBefore, hnewSigma, _hnewQ,
              _hdownAlternatives, hnextExists⟩
          rcases hnextExists with ⟨next, hnextUpdate, hnextAlternatives⟩
          rcases hnextUpdate with
            ⟨_hconsume, _hrelease, _hfinish, _hreleaseFinish, houtputFollower,
              hnextDomain, hnextMass, _hnextDelta, _hnextFailure⟩
          let nextMemory : ActiveFollowerLifecycle.LocalMemory p :=
            if next.status = .unoccupied then oldMemory else
              ⟨some ⟨record.input.time,
                FollowerCutoffScan.completeRowProposalBit p rate.eta.val
                  record.input.row record.input.time⟩⟩
          have houtputConfig : (record.output.followers i).configuration =
              .ordinary next nextMemory := by
            have h := congrArg ReferenceActivePhysicalStep.FollowerObservation.configuration
              houtputFollower
            simpa only [nextMemory] using h
          have hloggingFrame := ActiveFollowerLogging.checkedLogging_success_frame
            i record.input.row (record.input.state.activations i) record.input.time
            ((record.output.preparation.followers.followers i).arm,
              record.output.preparation.feedback.observations
                (PublicDiscreteDraws.followerPlayer p.two_le_m i)) old logged hlogging
          have hzeroOld : old.lastDown = none →
              old.S = 0 ∧ old.delta = 0 ∧ old.backlog = 0 := by
            intro hnone
            rcases hzeroSeed with hzero | hprior
            · exact ⟨hzero.2.1, hzero.2.2.1, hzero.2.2.2⟩
            · rw [hprior] at hnone
              cases hnone
          have hstateAfter : record.output.next.followers i = .ordinary next nextMemory := by
            have hstep := (ReferenceActivePhysicalStep.step_next_fields record.input).2.2.2 i
            have hnextConfig : record.output.next.followers i =
                (record.output.preparation.observeFollower i).configuration := by
              rw [record.output_eq]
              rfl
            have hobserve : record.output.preparation.observeFollower i =
                record.output.followers i := by
              rw [record.output_eq]
              rfl
            rw [hobserve] at hnextConfig
            exact hnextConfig.trans houtputConfig
          have hinputAfter : nextRecord.input.state.followers i = .ordinary next nextMemory := by
            rw [hstate]
            exact hstateAfter
          have hbranch :
              (next.status = .unoccupied ∧
                (next.lastDown = none → next.S = 0 ∧ next.delta = 0 ∧ next.backlog = 0)) ∨
              (next.status = .pending ∧
                next.lastDown = some (installed.registers.payload.downRecord i) ∧
                (installed.registers.payload.downRecord i).val.sigma = record.input.time.val + 1) := by
            rcases hnextAlternatives with hskip | hreject | haccepted
            · rcases hskip with ⟨_, _, hnextEq⟩
              subst next
              have hlogLast := hloggingFrame.1
              have hlogS := hloggingFrame.2.1
              have hlogDelta := hloggingFrame.2.2.1
              have hlogBacklog := hloggingFrame.2.2.2.1
              have hlogStatus := hloggingFrame.2.2.2.2.1
              have hzero : logged.lastDown = none →
                  logged.S = 0 ∧ logged.delta = 0 ∧ logged.backlog = 0 := by
                intro hnone
                have holdNone : old.lastDown = none := by rw [← hlogLast]; exact hnone
                have hz := hzeroOld holdNone
                rw [hlogS, hlogDelta, hlogBacklog]
                exact hz
              exact Or.inl ⟨hlogStatus.trans hstatusOld, hzero⟩
            · rcases hreject with ⟨_, _, _, _, _, hnextEq⟩
              have hlogLast := hloggingFrame.1
              have hlogS := hloggingFrame.2.1
              have hlogDelta := hloggingFrame.2.2.1
              have hlogBacklog := hloggingFrame.2.2.2.1
              have hlogStatus := hloggingFrame.2.2.2.2.1
              have hzero : next.lastDown = none →
                  next.S = 0 ∧ next.delta = 0 ∧ next.backlog = 0 := by
                intro hnone
                have hnone' : logged.lastDown = none := by
                  simpa [hnextEq] using hnone
                have holdNone : old.lastDown = none := by rw [← hlogLast]; exact hnone'
                have hz := hzeroOld holdNone
                constructor
                · have hnextS : next.S = logged.S := by simp [hnextEq]
                  rw [hnextS, hlogS]
                  exact hz.1
                · constructor
                  · have hnextDelta : next.delta = logged.delta := by simp [hnextEq]
                    rw [hnextDelta, hlogDelta]
                    exact hz.2.1
                  · have hnextBacklog : next.backlog = logged.backlog := by simp [hnextEq]
                    rw [hnextBacklog, hlogBacklog]
                    exact hz.2.2
              have hstatusNext : next.status = .unoccupied := by
                rw [hnextEq]
                simp [hlogStatus, hstatusOld]
              exact Or.inl ⟨hstatusNext, hzero⟩
            · rcases haccepted with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hnextEq⟩
              refine Or.inr ⟨?_, ?_, ?_⟩
              · rw [hnextEq]
              · rw [hnextEq]
                rfl
              · rw [installed.registers.payload.downRecord_fields i]
                exact hnewSigma
          rcases hbranch with ⟨hnextUnoccupied, hnextZero⟩ |
              ⟨hnextPending, hnextDown, hMsigma⟩
          · have hstartLocal := ActiveFollowerLifecycle.startRound_unoccupied
              rate.eta nextRecord.input.time next nextMemory hnextDomain hnextUnoccupied
            let startedState := next
            have hstartedDomain : ActiveFollowerLifecycle.localStateDomainValid startedState := by
              simpa [startedState] using hnextDomain
            have hstartedQueueDomain := queueInputDomain_of_localStateDomainValid
              startedState hstartedDomain
            have hprep := prepare_ordinary_after_actual_start i nextRecord.input.row
              (nextRecord.input.state.activations i) nextRecord.input.time
              (nextRecord.input.active i) next nextMemory startedState nextMemory
              (by simpa [startedState] using hstartLocal) hstartedQueueDomain
              (by intro _; exact hnextZero)
              (by intro h; exact False.elim (h hnextUnoccupied))
            have hactualPrep :
                (nextRecord.output.preparation.followers.followers i).configuration =
                  .ordinary startedState nextMemory := by
              have hpreparedEq := congrArg (fun o : ReferenceActivePhysicalStep.RoundOutput
                  nextRecord.input => o.preparation) nextRecord.output_eq
              rw [hpreparedEq]
              change (DeclaredFollowerLocalRound.prepare rate i nextRecord.input.row
                (nextRecord.input.state.activations i) nextRecord.input.time
                (nextRecord.input.active i) (nextRecord.input.state.followers i)).configuration = _
              rw [hinputAfter]
              exact hprep
            refine ⟨startedState, nextMemory, hactualPrep, hstartedDomain, ?_, ?_, next, hnextDomain,
              houtputConfig, hinputAfter, hstartLocal, Or.inl hnextUnoccupied⟩
            · rw [hcalendar]
              simpa only [startedState] using hnextMass
            · intro hbusy
              exact (hbusy hnextUnoccupied).elim
          · let M := installed.registers.payload.downRecord i
            have htime : M.val.sigma = nextRecord.input.time.val := by
              rw [hcalendar]
              exact hMsigma
            let htoken : ActiveFollowerLifecycle.ProposalRead p :=
              ⟨record.input.time,
                FollowerCutoffScan.completeRowProposalBit p rate.eta.val
                  record.input.row record.input.time⟩
            have hread : nextMemory.lastProposalRead = some htoken := by
              simp [nextMemory, hnextPending, htoken]
            have htokenTime : htoken.timestamp.val + 1 = nextRecord.input.time.val := by
              dsimp [htoken]
              exact hcalendar.symm
            obtain ⟨startedState, hstartLocal, hstartedStatus, hlast, hS, hdelta,
              hbacklog, hbuffer, hbatch, hfailure⟩ :=
              fresh_pending_startRound_success nextRecord.input.time next nextMemory M htoken hnextPending
                hnextDomain hnextDown htime hread htokenTime
            have hframe := ActiveFollowerLifecycle.startRound_frame rate.eta
              nextRecord.input.time next startedState nextMemory nextMemory hstartLocal
            have hstartedDomain : ActiveFollowerLifecycle.localStateDomainValid startedState := by
              rcases hnextDomain with ⟨hregs, hbuf, hdecoder⟩
              refine ⟨?_, ?_, ?_⟩
              · exact ⟨by rw [hS]; exact hregs.1,
                  by rw [hdelta]; exact hregs.2.1,
                  by rw [hbacklog]; exact hregs.2.2⟩
              · unfold ActiveFollowerLifecycle.localBufferValid at hbuf ⊢
                rw [hbuffer]
                exact hbuf
              · unfold ActiveFollowerLifecycle.downDecoderStateValid at hdecoder ⊢
                rw [hbatch]
                exact hdecoder
            have hstartedQueueDomain := queueInputDomain_of_localStateDomainValid
              startedState hstartedDomain
            have hzeroStarted : startedState.status = .unoccupied →
                startedState.lastDown = none →
                startedState.S = 0 ∧ startedState.delta = 0 ∧ startedState.backlog = 0 := by
              intro _ hnone
              rw [hlast] at hnone
              rw [hnextDown] at hnone
              cases hnone
            have hrecordStarted : startedState.status ≠ .unoccupied →
                ∃ M', startedState.lastDown = some M' := by
              intro _
              exact ⟨M, hlast.trans hnextDown⟩
            have hprep := prepare_ordinary_after_actual_start i nextRecord.input.row
              (nextRecord.input.state.activations i) nextRecord.input.time
              (nextRecord.input.active i) next nextMemory startedState nextMemory
              hstartLocal hstartedQueueDomain hzeroStarted hrecordStarted
            have hactualPrep :
                (nextRecord.output.preparation.followers.followers i).configuration =
                  .ordinary startedState nextMemory := by
              have hpreparedEq := congrArg (fun o : ReferenceActivePhysicalStep.RoundOutput
                  nextRecord.input => o.preparation) nextRecord.output_eq
              rw [hpreparedEq]
              change (DeclaredFollowerLocalRound.prepare rate i nextRecord.input.row
                (nextRecord.input.state.activations i) nextRecord.input.time
                (nextRecord.input.active i) (nextRecord.input.state.followers i)).configuration = _
              rw [hinputAfter]
              exact hprep
            refine ⟨startedState, nextMemory, hactualPrep, hstartedDomain, ?_, ?_, next, hnextDomain,
              houtputConfig, hinputAfter, hstartLocal, Or.inr ⟨hnextPending, hnextDown, hread⟩⟩
            · calc
                startedState.S + startedState.backlog = next.S + next.backlog := by
                  rw [hS, hbacklog]
                _ ≤ (record.input.time.val + 1) * D p := hnextMass
                _ = nextRecord.input.time.val * D p := by rw [← hcalendar]
            · intro hbusy
              have hdownStarted := hlast.trans hnextDown
              obtain ⟨serviced, finished, hchecked, _hrecord, _hfinish, hout, hvalid,
                hmass, hdeltaBound, hdownFinished, hbatchFinished, hbufferFinished,
                hfailureFinished⟩ := occupied_actual_follower_finish nextRecord i
                  startedState nextMemory hactualPrep hbusy hstartedDomain M
                  hdownStarted (by omega) (by
                    rw [hS, hbacklog, hcalendar]
                    exact hnextMass)
              exact ⟨hdownStarted, htime, serviced, finished, hchecked, hout, hvalid,
                hmass, hdeltaBound, hdownFinished, hbatchFinished, hbufferFinished,
                hfailureFinished⟩

/-- At the actual first replacement birth, the successful later-choice
constructor itself supplies the coordinator selection and the complete
ordinary PREPARE family. Consequently the admitted live numerical readout is
`some`, and its numerical and physical feedback identities refer to this
same original record and selected payload. -/
theorem complete_first_replacement_birth_live_readout
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h
    let s := ReferenceCompletePhysicalHistory.physicalStart
      rate source rewards C_star C_h
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
    let Cwin := ReferenceCollectionPhaseHistory.collectionWindow R w
    let v := w + Cwin.length
    match R[v]? with
    | none => True
    | some record =>
      match record.output.preparation.coordinator with
      | .collection _ _ _ _ (.laterChosen _ _ _ _ _ _ _ _ _ installed _) =>
        ∃ k : Fin R.length, k.val = v ∧
        ∃ _hrecord : R.get k = record,
        ∃ selected : ReferenceActivePhysicalStep.Selection record.input,
          record.output.preparation.coordinator.selection = some selected ∧
          selected.view.payload = installed.registers.payload ∧
          s < selected.view.payload.sigma.val ∧
          CoordinatorLocalArmChoice.assignmentIsLive selected.view.payload
            selected.view.cutoff record.input.time ∧
          ∃ c : RecordedQueueRun.RoundInput p.K,
            ∃ _hread : ReferenceLaterLiveNumericalReadout.laterLiveReadout s record = some c,
              (c.enabled = true ∧
                ∃ selected' : ReferenceActivePhysicalStep.Selection record.input,
                  record.output.preparation.coordinator.selection = some selected' ∧
                  c.reward = (fun a =>
                    ((record.input.rewards record.input.time a).val : ℝ) / (D p : ℝ)) ∧
                  c.rate = selected'.view.payload.rate ∧
                  ∀ a, RecordedQueueRun.quantizedArrival
                      (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a =
                    if c.recordedArm = some a then
                      Nat.floor ((D p : ℝ) * rate.eta.val *
                        (((record.input.rewards record.input.time a).val : ℝ) / (D p : ℝ)) /
                          selected'.view.payload.rate a)
                    else 0) ∧
              ∃ _hreadAtIndex : ReferenceLaterLiveNumericalReadout.laterLiveReadout
                  s (R.get k) = some c,
                ∃ cell : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell (R.get k),
                  cell.input = c ∧
                  (∀ a, c.recordedArm = some a →
                    ∃ owner : Fin p.m,
                      SnapshotRecordingKernel.owns p
                        (.live cell.selected.view.payload.assignment
                          (ReferenceActiveDataOwnership.choiceSnapshot cell.selected cell.states))
                        owner a ∧
                      (∀ other, SnapshotRecordingKernel.owns p
                        (.live cell.selected.view.payload.assignment
                          (ReferenceActiveDataOwnership.choiceSnapshot cell.selected cell.states))
                        other a → other = owner) ∧
                      (R.get k).output.preparation.arms.actions owner = a ∧
                      (R.get k).gridFeedback owner = rewards (R.get k).input.time a ∧
                      ((R.get k).output.ownEntries owner).2.val.val =
                        ((rewards (R.get k).input.time a).val : ℝ) / (D p : ℝ)) ∧
                  ∀ i : Fin (p.m - 1), (cell.states i).status ≠ ActiveRoundActions.FollowerStatus.unoccupied →
                    (c.recordedArm = some (cell.selected.view.payload.assignment.assigned i) ↔
                      ActiveFollowerQueueOperation.recorderGate rate.eta i
                        (R.get k).input.row (R.get k).input.time
                        (cell.selected.view.payload.downRecord i)) ∧
                    ActiveFollowerQueueOperation.rawArrival rate.eta i
                      (R.get k).input.row (R.get k).input.time
                      (cell.selected.view.payload.downRecord i)
                      ((R.get k).output.ownEntries
                        (PublicDiscreteDraws.followerPlayer p.two_le_m i)).2 =
                    RecordedQueueRun.quantizedArrival
                      (ReferenceFirstLaunchNumericalCell.queueParameters rate) c
                      (cell.selected.view.payload.assignment.assigned i)
      | _ => True := by
  classical
  have hroot :=
    ReferenceFirstReplacementDownRecovery.complete_first_replacement_down_recovery_and_finish
      rate source rewards C_star C_h
  dsimp only at hroot ⊢
  set R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
  set s := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
  set w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
  set Cwin := ReferenceCollectionPhaseHistory.collectionWindow R w
  set v := w + Cwin.length
  cases hget : R[v]? with
  | none => trivial
  | some record =>
    simp only [hget] at hroot ⊢
    cases hcut : record.output.preparation.coordinator with
    | first outcome => trivial
    | live registers owned base outcome => trivial
    | invalidCollectionCutoff => trivial
    | dagger => trivial
    | collection oldPayload ledger clock cutoff outcome =>
      rw [hcut] at hroot
      cases outcome with
      | clockFailure _ _ => trivial
      | localFailure _ _ _ _ => trivial
      | coreFailure _ _ _ _ => trivial
      | continuing _ _ _ _ => trivial
      | laterReconstructionFailure _ _ _ _ _ _ _ _ => trivial
      | laterPrefixFailure _ _ _ _ _ _ _ _ _ => trivial
      | laterOrientationFailure _ _ _ _ _ _ _ => trivial
      | laterChoiceFailure _ _ _ _ _ _ _ _ _ => trivial
      | laterChosen core consistent started hs instruction hinstruction output hcons
          clockData installed arm =>
        obtain ⟨hstart, hfollowers⟩ := hroot
        have hframes :=
          ReferenceCoordinatorRecorderCallCorrespondence.actual_call_frames record
        rw [hcut] at hframes
        rcases hframes with ⟨htime, _hlive, _hgrid⟩
        have hlive := _hlive
        let selected := ReferenceCoordinatorRecorderCallCorrespondence.selectionOfArm
          record.input installed.registers.payload started instruction.time
          installed.registers.complementWeights arm htime
        have hselection : record.output.preparation.coordinator.selection = some selected := by
          rw [hcut]
          change ReferenceActivePhysicalStep.selectionAt record.input
            installed.registers.payload started instruction.time
            installed.registers.complementWeights arm = some selected
          rw [ReferenceCoordinatorRecorderCallCorrespondence.selectionAt_eq
            record.input installed.registers.payload started instruction.time
            installed.registers.complementWeights arm htime]
        have hprepared : ReferenceLaterLiveNumericalReadout.preparedOrdinary record := by
          intro i
          rcases hfollowers i with
            ⟨old, memory, logged, _hstate, _hstatus, hconfiguration, _hrest⟩
          simp [ReferenceLaterLiveNumericalReadout.ordinaryData, hconfiguration]
        have hpayloadSigma : installed.registers.payload.sigma.val = record.input.time.val := by
          let i : Fin (p.m - 1) := ⟨0, by have hm := p.two_le_m; omega⟩
          rcases hfollowers i with
            ⟨old, memory, logged, _hstate, _hstatus, _hconfiguration,
              _hlogging, _hdomain, _hacceptedStart, hdownSigma, _hrest⟩
          have hfields : (installed.registers.payload.downRecord i).val.sigma =
              installed.registers.payload.sigma.val + 1 := by
            rw [installed.registers.payload.downRecord_fields i]
          rw [hfields] at hdownSigma
          exact Nat.add_right_cancel hdownSigma
        have hsigma : s < selected.view.payload.sigma.val := by
          change s < installed.registers.payload.sigma.val
          rw [hpayloadSigma]
          exact hstart
        have hselectedLive :
            CoordinatorLocalArmChoice.assignmentIsLive selected.view.payload
              selected.view.cutoff record.input.time := by
          exact hlive
        have hc : ReferenceLaterLiveNumericalReadout.laterLiveReadout s record =
            some (ReferenceFirstWindowNumericalStream.sourceCell record
              selected.view.payload selected.view.pendingAtChoice
              (ReferenceLaterLiveNumericalReadout.preparedStates record hprepared)
              selected.view.complementWeights selected.view.cutoff
              (ReferenceLaterLiveNumericalReadout.selection_choiceValid selected)) := by
          simp [ReferenceLaterLiveNumericalReadout.laterLiveReadout, hselection,
            hsigma, hselectedLive, hprepared]
        have hv : v < R.length := (List.getElem?_eq_some_iff.mp hget).1
        let k : Fin R.length := ⟨v, hv⟩
        have hgetValue : R[v] = record := (List.getElem?_eq_some_iff.mp hget).2
        have hrecord : R.get k = record := by
          simp only [k, List.get_eq_getElem]
          exact hgetValue
        have hck : ReferenceLaterLiveNumericalReadout.laterLiveReadout s (R.get k) =
            some (ReferenceFirstWindowNumericalStream.sourceCell record
              selected.view.payload selected.view.pendingAtChoice
              (ReferenceLaterLiveNumericalReadout.preparedStates record hprepared)
              selected.view.complementWeights selected.view.cutoff
              (ReferenceLaterLiveNumericalReadout.selection_choiceValid selected)) := by
          rw [hrecord]
          exact hc
        have hselectionCut :
            (ReferenceActivePhysicalStep.DispatchCut.collection oldPayload ledger clock cutoff
              (CoordinatorRoundDispatch.CollectionOutcome.laterChosen core consistent started hs
                instruction hinstruction output hcons clockData installed arm)).selection =
              some selected := by
          rw [← hcut]
          exact hselection
        have hphysical :=
          ReferenceLaterLiveNumericalReadout.laterLiveReadout_physical
            rate rewards C_star C_h source k _ hck
        refine ⟨k, rfl, hrecord, selected, hselectionCut, rfl, hsigma, hselectedLive, ?_⟩
        rcases hphysical with
          ⟨cell, hcell, _henabled, _hlive, _henabledTrace, _hrows,
            _hselectedRow, _hrewards, _hmarker, _hdown, howner, harrivals, _hrest⟩
        have hnum := ReferenceLaterLiveNumericalReadout.laterLiveReadout_numerical
          s record _ hc
        rcases hnum with ⟨henabled, selected', hselection', hreward, hrate, hquantized⟩
        refine ⟨_, hc, ⟨henabled, selected', ?_, hreward, hrate, hquantized⟩,
          ⟨hck, ⟨cell, hcell, howner, harrivals⟩⟩⟩
        rw [← hcut]
        exact hselection'

/-- The original launch and its actual prefix produce the clock invariant at
any present complete-suffix record. No clock law is an input. -/
theorem complete_suffix_record_clock
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length) :
    let r := (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).get k
    ReferenceCoordinatorClockDomains.clockAt r.input.rows r.input.selected
      r.input.time.val r.input.state := by
  obtain ⟨hc, span, hr⟩ := source_record_prefix rate rewards C_star C_h source k
  rw [hr]
  let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
    rate source rewards C_star C_h hc
  have hseed : ReferenceCoordinatorClockDomains.clockAt source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source)
      (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
      (ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hc) := by
    simp only [ReferenceCoordinatorClockDomains.clockAt, seed.coordinatorFirst]
  exact (ReferenceRunClockPreservation.run_clockAt _ source.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
    (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
    k.val (by omega) seed.activeAtStart hseed).1

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

/-- On the actual continuing successor branch, the selected payload is the
birth payload and every follower's local interruption decision is false.
The real numerical source cell supplies occupied arrivals and physical feedback.
The branch is inspected locally; its occurrence and its observation tail are
not asserted. This is the selection/domain interface for delayed sparse replay. -/
theorem complete_first_replacement_next_continuing_readout
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
      | .collection _ _ _ _ (.laterChosen _ _ _ _ _ _ _ _ _ installed _) =>
        match R[v + 1]? with
        | none => True
        | some r1 => match r1.output.preparation.coordinator with
          | .live _ _ _ (.continuingChosen ..) =>
            ∃ selected : Selection r1.input,
              r1.output.preparation.coordinator.selection = some selected ∧
              selected.view.payload = installed.registers.payload ∧
              s < selected.view.payload.sigma.val ∧
              CoordinatorLocalArmChoice.assignmentIsLive selected.view.payload
                selected.view.cutoff r1.input.time ∧
              (∀ i, ∃ before state memory,
                r1.input.state.followers i = .ordinary before memory ∧
                (r1.output.preparation.followers.followers i).configuration = .ordinary state memory ∧
                interruptionDecision rate.eta r1.input.time before memory = .ok false ∧
                state = before) ∧
              ∃ cell : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell r1,
                laterLiveReadout s r1 = some cell.input ∧
                cell.selected.view.payload = installed.registers.payload ∧
                (∀ i, (cell.states i).status ≠ .unoccupied →
                  ActiveFollowerQueueOperation.rawArrival rate.eta i r1.input.row r1.input.time
                    (cell.selected.view.payload.downRecord i)
                    (r1.output.ownEntries (followerPlayer p.two_le_m i)).2 =
                  RecordedQueueRun.quantizedArrival
                    (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell.input
                    (cell.selected.view.payload.assignment.assigned i)) ∧
                (∀ a, cell.input.recordedArm = some a → ∃ owner : Fin p.m,
                  r1.output.preparation.arms.actions owner = a ∧
                  r1.gridFeedback owner = rewards r1.input.time a ∧
                  (r1.output.ownEntries owner).2.val.val =
                    ((rewards r1.input.time a).val : ℝ) / (D p : ℝ))
          | _ => True
      | _ => True := by
  classical
  have hprep := complete_first_replacement_next_preparation_and_occupied_step rate source rewards C_star C_h
  have hbirth := complete_first_replacement_birth_live_readout rate source rewards C_star C_h
  have hadj := complete_first_replacement_actual_successor rate source rewards C_star C_h
  dsimp only at hprep hbirth hadj ⊢
  set R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
  set s := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
  set w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
  set v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
  cases hg0 : R[v]? with
  | none => trivial
  | some r0 =>
    simp only [hg0] at hprep hbirth hadj ⊢
    cases hcut0 : r0.output.preparation.coordinator with
    | first _ => trivial
    | live _ _ _ _ => trivial
    | dagger => trivial
    | invalidCollectionCutoff => trivial
    | collection payload ledger clock cutoff outcome =>
      rw [hcut0] at hprep hbirth
      cases outcome <;> try trivial
      rename_i core consistent started hs instruction hi output hcons clockData installed arm
      cases hg1 : R[v + 1]? with
      | none => trivial
      | some r1 =>
        simp only [hg1] at hprep hadj ⊢
        rcases hadj with ⟨_hc, _h0, _h1, hrun0, hrun1, hstate, htime⟩
        rcases hprep with ⟨_hstart, hfollowers⟩
        rcases hbirth with ⟨_k0, _hk0, _hindex0, selected0, hsel0, hpayload0, hsigma0, _hlive0, _⟩
        have hsel0' : r0.output.preparation.coordinator.selection = some selected0 := by
          rw [hcut0]; exact hsel0
        cases hcut1 : r1.output.preparation.coordinator with
        | first _ => trivial
        | collection _ _ _ _ _ => trivial
        | dagger => trivial
        | invalidCollectionCutoff => trivial
        | live r q base outcome =>
          cases outcome <;> try trivial
          rename_i dispatched hstart continuation arm1
          have horigin := dispatch_live_origin r1.input
          have hdispatch : dispatch r1.input = r1.output.preparation.coordinator := by
            rw [r1.output_eq]; rfl
          rw [hdispatch, hcut1] at horigin
          have hstored : ReferenceAssignmentPayloadPersistence.storedPayload
              r0.output.next.coordinator = some r.payload := by
            rw [← hstate, horigin]; rfl
          have htail := ReferenceAssignmentPayloadPersistence.livePostChoice_payload_frame
            r0.output.preparation installed.registers installed.ownedRegisters
            installed.retainedBaseScore started
          have hnext : r0.output.next.coordinator =
              (livePostChoice r0.output.preparation installed.registers installed.ownedRegisters
                installed.retainedBaseScore started).configuration := by
            have hnext' : r0.output.next.coordinator =
                r0.output.preparation.observeCoordinator.configuration := by
              rw [r0.output_eq]; rfl
            rw [hnext']
            unfold PreparedRound.observeCoordinator
            rw [dite_eq_right (by rw [hsel0']; exact Option.some_ne_none _), hcut0]
          rw [← hnext] at htail
          have hpayload : r.payload = installed.registers.payload := by
            rcases htail with hn | he
            · rw [hstored] at hn; cases hn
            · exact Option.some.inj (hstored.symm.trans he)
          let selected := ReferenceCoordinatorRecorderCallCorrespondence.selectionOfArm
            r1.input r.payload dispatched.startResult r1.input.time
            (liveRegistersAt r r1.input.time).complementWeights arm1 rfl
          have hsel1 : r1.output.preparation.coordinator.selection = some selected := by
            rw [hcut1]
            exact ReferenceCoordinatorRecorderCallCorrespondence.selectionAt_eq _ _ _ _ _ _ rfl
          have hframes := ReferenceCoordinatorRecorderCallCorrespondence.actual_call_frames r1
          rw [hcut1] at hframes
          have hlive : CoordinatorLocalArmChoice.assignmentIsLive selected.view.payload
              selected.view.cutoff r1.input.time := hframes.1
          have hsigma : s < selected.view.payload.sigma.val := by
            change s < r.payload.sigma.val
            rw [hpayload, ← hpayload0]; exact hsigma0
          let k1 : Fin R.length := ⟨v + 1, (List.getElem?_eq_some_iff.mp hg1).1⟩
          have hr1 : R.get k1 = r1 := (List.getElem?_eq_some_iff.mp hg1).2
          have hclock := complete_suffix_record_clock rate source rewards C_star C_h k1
          rw [hr1] at hclock
          simp only [ReferenceCoordinatorClockDomains.clockAt, horigin] at hclock
          rcases hclock with ⟨hstamp, hvalid, hsigmaClock, hu, hg, hstarted, hbefore, htoken⟩
          have htimeValid : CoordinatorPhaseClock.startRoundTimeValid p r1.input.time r.priorClock := by
            simp only [CoordinatorPhaseClock.startRoundTimeValid, hsigmaClock, hu,
              FollowerCutoffScan.calendarRound]
            exact ⟨hstarted, by omega⟩
          have hnoCutoff : ¬ (r1.input.time.val + 1 = r.priorClock.g ∨
              FollowerCutoffScan.completeRowProposalBit p rate.eta.val r1.input.row r.time = true) := by
            intro hcutoff
            have hdetect := clock_detectCutoff_of_interruption r.priorClock r1.input.time
              r.payload.sigma r.time
              (FollowerCutoffScan.completeRowProposalBit p rate.eta.val r1.input.row r.time)
              hsigmaClock hu htoken hstamp hcutoff
            obtain ⟨cut, hrun, hcutClock, _⟩ := CoordinatorPhaseClock.startRound_cutoff_effect
              p rate.eta.val r1.input.time r.payload.sigma r.priorClock
              (liveRegistersAt r r1.input.time).clockPending
              (ReferenceCoordinatorClockDomains.proposalParameterValid_of_rate rate)
              hvalid htimeValid hsigmaClock hdetect
            have heq : cut = dispatched.startResult := Except.ok.inj (hrun.symm.trans hstart)
            have hlt := hframes.1.2
            rw [← heq, hcutClock] at hlt
            change r1.input.time.val + 1 < r1.input.time.val + 1 at hlt
            omega
          have hbit : FollowerCutoffScan.completeRowProposalBit p rate.eta.val
              r0.input.row r0.input.time = false := by
            have hrt : r.time = r0.input.time := Fin.ext (by omega)
            have hrows : r1.input.row = r0.input.row := by
              rw [hrun1, hrun0]; rfl
            have hb := fun h => hnoCutoff (Or.inr h)
            rw [hrt, hrows] at hb
            cases h : FollowerCutoffScan.completeRowProposalBit p rate.eta.val
                r0.input.row r0.input.time with
            | false => rfl
            | true => exact (hb h).elim
          have hgridEq : r.priorClock.g = FollowerCutoffScan.gridBoundary p rate.eta.val
              installed.registers.payload.sigma := by
            have h := hvalid.1
            simpa only [CoordinatorPhaseClock.boundaryFromSigma, hsigmaClock, hpayload] using h
          have ho : preparedOrdinary r1 := by
            intro i
            obtain ⟨state, memory, hconfig, _⟩ := hfollowers i
            simp only [hconfig, ordinaryData, Option.isSome_some]
          obtain ⟨c, hc⟩ : ∃ c, laterLiveReadout s r1 = some c := by
            have hd : laterLiveDomain s r1 := ⟨selected, hsel1, hsigma, hlive, ho⟩
            have h := (laterLiveReadout_domain s r1).2 hd
            cases hh : laterLiveReadout s r1 with
            | none => simp only [hh, Option.isSome_none, Bool.false_eq_true] at h
            | some c => exact ⟨c, rfl⟩
          have hck : laterLiveReadout s (R.get k1) = some c := by rw [hr1]; exact hc
          have hphysical := laterLiveReadout_physical rate rewards C_star C_h source k1 c hck
          rw [hr1] at hphysical
          obtain ⟨cell, hcell, _henabled, _hlive, _hen, _hrows, _hselected, _hrewards,
            _hmarker, _hdown, howner, harrival, _⟩ := hphysical
          have hcellSelected : cell.selected = selected :=
            Option.some.inj (cell.selection_actual.symm.trans hsel1)
          refine ⟨selected, ?_, hpayload, hsigma, hlive, ?_, cell, ?_, ?_, ?_, ?_⟩
          · rw [← hcut1]; exact hsel1
          · intro i
            change ActiveRoundActions.Follower p.m at i
            obtain ⟨state, memory, hconfig, _hdomain, _hmass, _hbusy, before,
              hbeforeDomain, _houtput, hinput, hstartLocal, hbranch⟩ := hfollowers i
            have hdecision : interruptionDecision rate.eta r1.input.time before memory = .ok false := by
              rcases hbranch with huBefore | ⟨hpending, hdown, hread⟩
              · simp only [interruptionDecision, dite_eq_left hbeforeDomain, dite_eq_left huBefore]
              · let M : OrdinaryMessageCodec.DownRecord
                    (ReferencePrelaunchFollower.codecParams p rate.eta) :=
                  installed.registers.payload.downRecord i
                have hdown' : before.lastDown = some M := hdown
                have hcoord : acceptedStartCoordinate M = installed.registers.payload.sigma := by
                  apply Fin.ext
                  change (installed.registers.payload.downRecord i).val.sigma - 1 =
                    installed.registers.payload.sigma.val
                  rw [installed.registers.payload.downRecord_fields i]
                  exact Nat.add_sub_cancel _ _
                have hnotGrid : ¬ (FollowerCutoffScan.gridBoundary p rate.eta.val
                    installed.registers.payload.sigma = r1.input.time.val + 1) := by
                  rw [← hgridEq]; exact fun he => hnoCutoff (Or.inl he.symm)
                have hdownTime : M.val.sigma ≤ r1.input.time.val := by
                  change (installed.registers.payload.downRecord i).val.sigma ≤ r1.input.time.val
                  rw [installed.registers.payload.downRecord_fields i, ← hpayload]
                  change r.payload.sigma.val + 1 ≤ r1.input.time.val
                  omega
                have hoccupied : before.status ≠ .unoccupied := by rw [hpending]; decide
                have hbound : r1.input.time.val + 1 ≤ FollowerCutoffScan.gridBoundary
                    p rate.eta.val installed.registers.payload.sigma := by
                  rw [← hgridEq, ← hg]; omega
                simp only [interruptionDecision, dite_eq_left hbeforeDomain,
                  dite_eq_right hoccupied, hdown', dite_eq_left hdownTime]
                rw [hcoord, dite_eq_left hbound, hread]
                simp only [htime.symm, ↓reduceDIte, hbit, decide_eq_false hnotGrid,
                  Bool.false_or]
            have hsame : state = before := by
              rw [startRound, hdecision] at hstartLocal
              have heq := congrArg Prod.fst (Except.ok.inj hstartLocal)
              simpa only [Prod.fst, Bool.false_eq_true, ite_false] using heq.symm
            exact ⟨before, state, memory, hinput, hconfig, hdecision, hsame⟩
          · rw [hcell]; exact hc
          · rw [hcellSelected]; exact hpayload
          · intro i hbusy; rw [hcell]; exact (harrival i hbusy).2
          · intro a ha
            obtain ⟨owner, _howns, _hunique, harm, hfeedback, hown⟩ := howner a (by rw [← hcell]; exact ha)
            exact ⟨owner, harm, hfeedback, hown⟩

end Bandits.Support.ReferenceFirstReplacementNextFollowerStep
end
