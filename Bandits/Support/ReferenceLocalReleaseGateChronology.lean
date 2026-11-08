/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceReleaseStrictPastFactor
public import Bandits.Support.ReferencePhysicalReleaseQuota

/-!
# Chronology of local release gates on the physical execution

Sources: `sources/zip4/manuscript/05_binary_transport.tex:74-88,293-348`,
`sources/zip4/manuscript/06_interruptions.tex:246-297,435-492`,
`sources/zip4/manuscript/07_public_setup.tex:121-164`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-79`.

The support below reads actual incoming records, including gates with no
pending follower. It is an internal local readout. It does not define the
manuscript's stopped support, its filtration, or any conditional service law.
The original physical execution, its exit record, and its later suffix are
retained throughout.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ReferenceLocalReleaseGateChronology

open ConstructorDimensions ReferenceActivePhysicalStep
open ReferenceActivePhysicalStepMeasurability
open ReferenceAssignmentPayloadPersistence ReferenceAssignmentPayloadChronology
open ReferenceRetainedReleasePhaseObservation
open scoped Classical

variable {p : ConstructorDimensions.Parameters} {rate : ReferenceActivePhysicalStep.RateInput p}

abbrev Record := ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)

/-- The finite set of one-based physical rounds whose actual incoming state
passes the local gate. No pending-set nonemptiness test is made. -/
def gateSupport (b : ℕ) (records : List (Record (p := p) (rate := rate))) : Finset ℕ :=
  ((records.filter fun r => localReleaseGate rate b r.input.time
    (encodeState r.input.state)).map fun r => r.input.time.val + 1).toFinset

theorem mem_gateSupport (b v : ℕ) (records : List (Record (p := p) (rate := rate))) :
    v ∈ gateSupport b records ↔ ∃ r ∈ records,
      localReleaseGate rate b r.input.time (encodeState r.input.state) = true ∧
      r.input.time.val + 1 = v := by
  simp only [gateSupport, List.mem_toFinset, List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨r, ⟨hr, hg⟩, hv⟩
    exact ⟨r, hr, hg, hv⟩
  · rintro ⟨r, hr, hg, hv⟩
    exact ⟨r, ⟨hr, hg⟩, hv⟩

theorem gateSupport_bounds (b v : ℕ) (records : List (Record (p := p) (rate := rate)))
    (hv : v ∈ gateSupport b records) : 1 ≤ v ∧ v ≤ p.T := by
  obtain ⟨r, _, _, rfl⟩ := (mem_gateSupport b v records).mp hv
  have ht := r.input.time.isLt
  omega

/-- Literal minimum gate, with the horizon sentinel on empty support. -/
def gateAlpha (b : ℕ) (records : List (Record (p := p) (rate := rate))) : ℕ :=
  if h : (gateSupport b records).Nonempty then (gateSupport b records).min' h else p.T + 1

/-- One past the literal last gate, with the same empty sentinel. -/
def gateBeta (b : ℕ) (records : List (Record (p := p) (rate := rate))) : ℕ :=
  if h : (gateSupport b records).Nonempty then (gateSupport b records).max' h + 1 else p.T + 1

theorem gate_endpoints_bounds (b : ℕ) (records : List (Record (p := p) (rate := rate))) :
    1 ≤ gateAlpha b records ∧ gateAlpha b records ≤ gateBeta b records ∧
      gateBeta b records ≤ p.T + 1 := by
  by_cases h : (gateSupport b records).Nonempty
  · have hlo := gateSupport_bounds b _ records (Finset.min'_mem _ h)
    have hhi := gateSupport_bounds b _ records (Finset.max'_mem _ h)
    have horder := Finset.min'_le_max' (gateSupport b records) h
    simp only [gateAlpha, gateBeta, dite_eq_left h]
    omega
  · simp only [gateAlpha, gateBeta, dite_eq_right h]
    omega

theorem gate_endpoints_empty (b : ℕ) (records : List (Record (p := p) (rate := rate)))
    (h : gateSupport b records = ∅) :
    gateAlpha b records = p.T + 1 ∧ gateBeta b records = p.T + 1 := by
  simp only [gateAlpha, gateBeta, h, Finset.not_nonempty_empty, dite_false, and_self]

/-- A true gate extracts its own incoming live registers and their whole
payload; it does not replace an older payload by a current one. -/
theorem gate_live (b : ℕ) (time : Fin p.T) (state : State p rate)
    (hg : localReleaseGate rate b time (encodeState state) = true) :
    ∃ r q base, state.coordinator = .live r q base ∧
      r.payload.sigma.val = b ∧ r.pendingAtChoice = ∅ ∧
      r.priorClock.sigma = some r.payload.sigma ∧ r.priorClock.u = none := by
  cases hc : state.coordinator with
  | first => simp [localReleaseGate, encodeState, encodeCoordinator, hc] at hg
  | collection payload ledger proposal =>
      simp [localReleaseGate, encodeState, encodeCoordinator, hc] at hg
  | dagger => simp [localReleaseGate, encodeState, encodeCoordinator, hc] at hg
  | live r q base =>
      refine ⟨r, q, base, rfl, ?_⟩
      simp only [localReleaseGate, encodeState, encodeCoordinator, hc,
        encodeLive, Bool.and_eq_true, decide_eq_true_eq] at hg
      exact ⟨hg.1.1.1.1, hg.1.1.1.2, hg.1.1.2, hg.1.2⟩

/-- The actual corrected-launch option, with the original whole source and
unrestricted initialization constants. -/
def sourceSeed (rate : ReferenceActivePhysicalStep.RateInput p)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true) :
    State p rate :=
  (ReferenceCorrectedInitializationLaunch.correctedLaunch rate z rewards C_star C_h).get
    ((ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
      rate z rewards C_star C_h).mpr hcross)

theorem sourceSeed_launch (rate : ReferenceActivePhysicalStep.RateInput p)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true) :
    ReferenceCorrectedInitializationLaunch.correctedLaunch rate z rewards C_star C_h =
      some (sourceSeed rate z rewards C_star C_h hcross) :=
  (Option.some_get _).symm

/-- Initialization inputs are produced from the same corrected launch,
including rejection and forcing branches. No follower invariant is supplied. -/
theorem canonical_seed_release_inputs (rate : ReferenceActivePhysicalStep.RateInput p)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true) :
    let seed := sourceSeed rate z rewards C_star C_h hcross
    let s := ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed
    seed.coordinator = .first ∧ ReferenceActivePhysicalHorizon.allActiveAtStart seed s ∧
      ReferenceFirstLiveConfirmationHistory.InitialFollowers seed := by
  intro seed s
  have hseed := sourceSeed_launch rate z rewards C_star C_h hcross
  obtain ⟨active, ⟨hlaunch, hfirst, _, _, _⟩, _⟩ :=
    ReferenceCorrectedInitializationLaunch.correctedLaunch_crossing_characterization
      rate z rewards C_star C_h hcross
  have heq : active = seed := Option.some.inj (hlaunch.symm.trans hseed)
  subst active
  obtain ⟨active, hlaunch, hactive⟩ :=
    ReferenceCorrectedInitializationLaunch.correctedLaunch_all_active_at_start
      rate z rewards C_star C_h hcross
  have heq : active = seed := Option.some.inj (hlaunch.symm.trans hseed)
  subst active
  obtain ⟨active, hlaunch, hfields⟩ :=
    ReferenceCorrectedInitializationLaunch.correctedLaunch_follower_source_fields
      rate z rewards C_star C_h hcross
  have heq : active = seed := Option.some.inj (hlaunch.symm.trans hseed)
  subst active
  refine ⟨hfirst, hactive, ?_⟩
  intro i before memory hbefore
  have hf := hfields i
  rw [hbefore] at hf
  have heq := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj hf.1
  cases heq.1
  exact ⟨hf.2.2.2.2.2.2.1, hf.2.1⟩

private theorem finish_clock_frame (time : Fin p.T)
    (clock : CoordinatorPhaseClock.ClockRegisters p)
    (pending : Finset (Fin (p.m - 1))) (row : CompletePublicTable.CompleteRow p)
    (finished : CoordinatorPhaseClock.FinishRoundResult p)
    (hf : CoordinatorPhaseClock.finishRound p rate.eta.val time clock pending row = .ok finished) :
    finished.clock.sigma = clock.sigma ∧ finished.clock.u = clock.u := by
  simp only [CoordinatorPhaseClock.finishRound] at hf
  repeat' split at hf
  all_goals cases hf
  all_goals exact ⟨rfl, rfl⟩

private theorem live_tail_frame (x : RoundInput p rate) (prepared : PreparedRound x)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r) (base : Fin (p.m - 1) → ℕ)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (next : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters next) (nextBase : Fin (p.m - 1) → ℕ)
    (hout : (livePostChoice prepared r q base started).configuration = .live next owned nextBase) :
    next.payload = r.payload ∧ next.pendingAtChoice ⊆ started.pending ∧
      next.priorClock.sigma = started.clock.sigma ∧ next.priorClock.u = started.clock.u := by
  have hframe := ReferenceFirstLiveConfirmationHistory.livePostChoice_frame x prepared r q base started
  have hsub : next.pendingAtChoice ⊆ started.pending := by
    rcases hframe with hdagger | ⟨actual, actualOwned, heq, _, hsub⟩
    · rw [hout] at hdagger
      cases hdagger
    · rw [hout] at heq
      cases heq
      exact hsub
  unfold livePostChoice at hout
  split at hout
  · cases hout
  · split at hout
    · cases hout
    · split at hout
      · cases hout
      · split at hout
        · cases hout
        · rename_i finished hfinish
          have hclock := finish_clock_frame x.time _ _ x.row finished hfinish
          cases hout
          exact ⟨rfl, hsub, hclock⟩

private theorem collection_finish_not_live (x : RoundInput p rate) (payload : Payload rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (recording : CoordinatorRecordingOperation.Output p) (cut : UpCut p rate)
    (next : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters next) (base : Fin (p.m - 1) → ℕ) :
    (collectionFinish (x := x) payload started recording cut).configuration ≠ .live next owned base := by
  unfold collectionFinish
  split
  · simp only [coordinatorFailure, ne_eq, reduceCtorEq, not_false_eq_true]
  all_goals dsimp only
  all_goals repeat' split
  all_goals simp only [coordinatorFailure, ne_eq, reduceCtorEq, not_false_eq_true]

private theorem collection_tail_not_live (x : RoundInput p rate) (prepared : PreparedRound x)
    (payload : Payload rate) (ledger : Ledger rate) (started : CoordinatorPhaseClock.StartRoundResult p)
    (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ)
    (next : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters next) (base : Fin (p.m - 1) → ℕ) :
    (collectionPostChoice prepared payload ledger started weights).configuration ≠ .live next owned base := by
  unfold collectionPostChoice
  split
  · simp only [coordinatorFailure, ne_eq, reduceCtorEq, not_false_eq_true]
  · dsimp only
    split
    · simp only [coordinatorFailure, ne_eq, reduceCtorEq, not_false_eq_true]
    · simp only [coordinatorFailure, ne_eq, reduceCtorEq, not_false_eq_true]
    · exact collection_finish_not_live x payload started _ _ next owned base

private theorem continuing_frame
    (input : CoordinatorRoundDispatch.LiveInput p)
    (dispatched : CoordinatorStartRoundCutoffDispatch.Output
      input.registers input.ownedRegisters input.followerBaseScore)
    (hstart : CoordinatorPhaseClock.startRound p input.eta.val input.registers.time
      input.registers.priorClock input.registers.clockPending = .ok dispatched.startResult)
    (continuation : CoordinatorLiveChoiceRecorderStep.Continuation input.registers input.row)
    (selection : CoordinatorRoundDispatch.ArmSelection input.registers.payload
      dispatched.startResult input.registers.time input.registers.complementWeights input.row)
    (heq : CoordinatorRoundDispatch.dispatchLive input =
      .continuingChosen dispatched hstart continuation selection) :
    CoordinatorLiveChoiceRecorderStep.unchangedLiveClockFrame input.registers dispatched.startResult := by
  unfold CoordinatorRoundDispatch.dispatchLive at heq
  dsimp only at heq
  split at heq
  · cases heq
  · split at heq
    · cases heq
    · cases heq
    · rename_i actual _ _
      by_cases hframe : CoordinatorLiveChoiceRecorderStep.unchangedLiveClockFrame
          input.registers actual.startResult
      · rw [dite_eq_left hframe] at heq
        repeat' split at heq
        all_goals first
          | (cases heq; exact hframe)
          | cases heq
          | (rename_i hchoice hboundary henvelope hselected
             exact ((CoordinatorLiveChoiceRecorderStep.coordinatorArmChoice_ne_none
               input.registers.payload actual.startResult.pending
               (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p actual.startResult.clock.u)
               input.registers.time input.registers.complementWeights input.row hchoice) hselected).elim)
      · rw [dite_eq_right hframe] at heq
        cases heq
    · rename_i actual _ _ _
      repeat' split at heq
      all_goals first
        | cases heq
        | (rename_i hchoice hboundary henvelope hselected
           exact ((CoordinatorLiveChoiceRecorderStep.coordinatorArmChoice_ne_none
             input.registers.payload actual.startResult.pending
             (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p actual.startResult.clock.u)
             input.registers.time input.registers.complementWeights input.row hchoice) hselected).elim)

/-- Inversion for a live successor with an older birth stamp. A later
installation is excluded by its actual timestamp, not by a no-cutoff premise.
The returned clock call and frame come from the actual continuing dispatch. -/
theorem step_old_live_predecessor (x : RoundInput p rate) (b : ℕ)
    (next : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters next) (nextBase : Fin (p.m - 1) → ℕ)
    (hout : (step x).next.coordinator = .live next owned nextBase)
    (hb : next.payload.sigma.val = b) (hold : b < x.time.val) :
    ∃ r q base, x.state.coordinator = .live r q base ∧ r.payload.sigma.val = b ∧
      ∃ started, CoordinatorPhaseClock.startRound p rate.eta.val x.time r.priorClock
          r.clockPending = .ok started ∧
        CoordinatorLiveChoiceRecorderStep.unchangedLiveClockFrame (liveRegistersAt r x.time) started ∧
        r.priorClock.sigma = some r.payload.sigma ∧
        next.pendingAtChoice ⊆ r.pendingAtChoice ∧
        next.priorClock.sigma = r.priorClock.sigma ∧ next.priorClock.u = r.priorClock.u := by
  have hstored : storedPayload (step x).next.coordinator = some next.payload := by
    rw [hout]
    rfl
  have hnotBirth : ∀ fresh, InstallationBirth (actualStepRecord x) fresh →
      storedPayload (step x).next.coordinator ≠ some fresh := by
    intro fresh hf hs
    have heq := Option.some.inj (hstored.symm.trans hs)
    have ht := installationBirth_time_eq (actualStepRecord x) fresh hf
    rw [← heq, hb] at ht
    exact (Nat.ne_of_lt hold) ht
  cases hc : x.state.coordinator with
  | first =>
      rcases actualStep_payload_classification x with hn | ⟨old, ho, _⟩ | ⟨fresh, hf, hs⟩
      · rw [hstored] at hn; cases hn
      · simp only [hc, storedPayload] at ho; cases ho
      · exact (hnotBirth fresh hf hs).elim
  | dagger =>
      have hd := observeCoordinator_dagger (prepare x) (dispatch_dagger x hc)
      rw [(step_next_fields x).1, hd] at hout
      cases hout
  | collection payload ledger proposal =>
      by_cases hvalid : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
      · let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
        let clock := collectionClock payload ledger proposal cutoff
        let source := collectionInput x payload ledger clock cutoff
        cases hdispatch : CoordinatorRoundDispatch.dispatch (.collection source) with
        | collection outcome =>
          have hd : (prepare x).coordinator = .collection payload ledger clock cutoff outcome := by
            change dispatch x = _
            simp [dispatch, hc, hvalid, cutoff, clock, source, hdispatch]
            rfl
          have he := observeCoordinator_collection_equation (prepare x) _ _ _ _ _ hd
          cases outcome with
          | continuing core prepared boundary checked =>
              rw [(step_next_fields x).1, he] at hout
              split at hout
              · cases hout
              · exact (collection_tail_not_live x (prepare x) _ _ _ _ next owned nextBase hout).elim
          | laterChosen core consistent started hstart instruction hi output consistency clockData installed selection =>
              have hp := ReferenceLaterInstallationProvenance.dispatch_laterChosen_provenance x
              change dispatch x = _ at hd
              rw [hd] at hp
              rw [(step_next_fields x).1, he] at hout
              split at hout
              · cases hout
              · have ht := live_tail_frame x (prepare x) installed.registers installed.ownedRegisters
                    installed.retainedBaseScore started next owned nextBase hout
                have htime : next.payload.sigma.val = x.time.val :=
                  (congrArg (fun M => M.sigma.val) ht.1).trans hp.2.2.1
                omega
          | _ =>
              rw [(step_next_fields x).1, he] at hout
              simp only [DispatchCut.selection, ite_true, coordinatorFailure] at hout
              cases hout
      · have hd : (prepare x).coordinator = .invalidCollectionCutoff :=
          (dispatch_collection_invalid_cutoff x payload ledger proposal hc hvalid).1
        rw [(step_next_fields x).1] at hout
        simp only [PreparedRound.observeCoordinator, hd, DispatchCut.selection,
          coordinatorFailure] at hout
        cases hout
  | live r q base =>
      have hd : (prepare x).coordinator = .live r q base
          (CoordinatorRoundDispatch.dispatchLive (liveInput x r q base)) := by
        simp only [prepare, dispatch, hc, CoordinatorRoundDispatch.dispatch]
        rfl
      have he := observeCoordinator_live_equation (prepare x) r q base _ hd
      cases ho : CoordinatorRoundDispatch.dispatchLive (liveInput x r q base) with
      | continuingChosen dispatched hstart continuation selection =>
          have hf := continuing_frame (liveInput x r q base) dispatched hstart continuation selection ho
          rw [(step_next_fields x).1, he, ho] at hout
          split at hout
          · cases hout
          · have ht := live_tail_frame x (prepare x) (liveRegistersAt r x.time)
                (liveOwnedAt r q x.time) base dispatched.startResult next owned nextBase hout
            refine ⟨r, q, base, rfl, ht.1.symm ▸ hb, dispatched.startResult, ?_, hf,
              continuation.payloadClockStart, ?_, ?_, ?_⟩
            · exact hstart
            · exact ht.2.1.trans (by rw [hf.2.1]; exact Finset.Subset.refl _)
            · exact ht.2.2.1.trans (congrArg CoordinatorPhaseClock.ClockRegisters.sigma hf.1)
            · exact ht.2.2.2.trans (congrArg CoordinatorPhaseClock.ClockRegisters.u hf.1)
      | cutoffChosen =>
          rw [(step_next_fields x).1, he, ho] at hout
          split at hout
          · cases hout
          · exact (collection_tail_not_live x (prepare x) _ _ _ _ next owned nextBase hout).elim
      | _ =>
          rw [(step_next_fields x).1, he, ho] at hout
          simp only [DispatchCut.selection, ite_true, coordinatorFailure] at hout
          cases hout

private theorem gate_of_frame (time : Fin p.T) (state : State p rate) (b : ℕ)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r) (base : Fin (p.m - 1) → ℕ)
    (hc : state.coordinator = .live r q base) (hb : r.payload.sigma.val = b)
    (he : r.pendingAtChoice = ∅) (hs : r.priorClock.sigma = some r.payload.sigma)
    (hu : r.priorClock.u = none) (started : CoordinatorPhaseClock.StartRoundResult p)
    (hstart : CoordinatorPhaseClock.startRound p rate.eta.val time r.priorClock r.clockPending = .ok started)
    (hf : CoordinatorLiveChoiceRecorderStep.unchangedLiveClockFrame (liveRegistersAt r time) started) :
    localReleaseGate rate b time (encodeState state) = true := by
  have hstart' : localReleaseStartResult rate time (encodeLive r q base) = .ok started := hstart
  have hf' : CoordinatorLiveChoiceRecorderStep.unchangedLiveClockFrame
      (decodeLiveRegisters r.payload (encodeLive r q base)) started := by
    simpa only [CoordinatorLiveChoiceRecorderStep.unchangedLiveClockFrame,
      decodeLiveRegisters, encodeLive, liveRegistersAt,
      CoordinatorLiveChoiceRecorderStep.Registers.clockPending] using hf
  simp only [localReleaseGate, encodeState, encodeCoordinator, hc]
  change (decide (r.payload.sigma.val = b) && decide (r.pendingAtChoice = ∅) &&
    decide (r.priorClock.sigma = some r.payload.sigma) && decide (r.priorClock.u = none) &&
    (match localReleaseStartResult rate time (encodeLive r q base) with
      | .error _ => false
      | .ok result => decide (CoordinatorLiveChoiceRecorderStep.unchangedLiveClockFrame
          (decodeLiveRegisters r.payload (encodeLive r q base)) result))) = true
  rw [hstart']
  simp only [hb, he, hs, hu, hf', decide_true, Bool.and_self]

section Run

variable (initial : State p rate) (rows : CompletePublicTable.CompleteRows p)
  (J : Fin (M p)) (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (s : ℕ)
  (hactive : ReferenceActivePhysicalHorizon.allActiveAtStart initial s)

private theorem records_eq_ofFn (count : ℕ) (hspan : s + count ≤ p.T) :
    (ReferenceActivePhysicalHorizon.run initial rows J rewards s count hspan hactive).records =
      List.ofFn (fun j : Fin count => actualRunRecordAt initial rows J rewards s j.val
        (by have _hj := j.isLt; omega) hactive) := by
  induction count with
  | zero => simp only [ReferenceActivePhysicalHorizon.run_zero_records, List.ofFn_zero]
  | succ count ih =>
      rw [run_successor_actualRunRecordAt, List.ofFn_succ', List.concat_eq_append, ih (by omega)]
      rfl

theorem run_record_at (count : ℕ) (hspan : s + count ≤ p.T) (j : Fin count) :
    (ReferenceActivePhysicalHorizon.run initial rows J rewards s count hspan hactive).records[j.val]'(by rw [ReferenceActivePhysicalHorizon.run_record_count]; exact j.isLt) =
      actualRunRecordAt initial rows J rewards s j.val (by have _hj := j.isLt; omega) hactive := by
  simp only [records_eq_ofFn, List.getElem_ofFn]

private theorem prefix_record_mem (count : ℕ) (hspan : s + count ≤ p.T)
    (n : ℕ) (hn : n ≤ count) (r : Record (p := p) (rate := rate))
    (hr : r ∈ (ReferenceActivePhysicalHorizon.run initial rows J rewards s n (by omega) hactive).records) :
    r ∈ (ReferenceActivePhysicalHorizon.run initial rows J rewards s count hspan hactive).records := by
  rw [records_eq_ofFn] at hr ⊢
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hr
  exact List.mem_ofFn.mpr ⟨⟨j.val, by have _hj := j.isLt; omega⟩, rfl⟩

/-- Every incoming gate has an actual earlier installation on this SAME
execution. The installing record need not have a successful post-choice tail. -/
theorem run_gate_birth (count : ℕ) (hspan : s + count ≤ p.T)
    (hfirst : initial.coordinator = .first) (j : Fin count) (b : ℕ)
    (hg : localReleaseGate rate b
      (actualRunRecordAt initial rows J rewards s j.val (by have _hj := j.isLt; omega) hactive).input.time
      (encodeState (actualRunRecordAt initial rows J rewards s j.val
        (by have _hj := j.isLt; omega) hactive).input.state) = true) :
    ∃ payload birth,
      storedPayload (actualRunRecordAt initial rows J rewards s j.val
        (by have _hj := j.isLt; omega) hactive).input.state.coordinator = some payload ∧
      payload.sigma.val = b ∧
      birth ∈ (ReferenceActivePhysicalHorizon.run initial rows J rewards s count hspan hactive).records ∧
      InstallationBirth birth payload ∧ birth.input.time.val = b ∧ s ≤ b ∧ b < s + j.val := by
  obtain ⟨r, q, base, hc, hb, _, _, _⟩ := gate_live b _ _ hg
  have hstored : storedPayload
      (ReferenceActivePhysicalHorizon.run initial rows J rewards s j.val (by have _hj := j.isLt; omega)
        hactive).finalState.coordinator = some r.payload := by
    change storedPayload (actualRunRecordAt initial rows J rewards s j.val
      (by have _hj := j.isLt; omega) hactive).input.state.coordinator = some r.payload
    rw [hc]
    rfl
  obtain ⟨birth, hm, hbirth, ht, hlo, hhi⟩ := run_prefix_storedPayload_has_birth
    initial rows J rewards s count hspan hactive hfirst j.val (Nat.le_of_lt j.isLt) r.payload hstored
  refine ⟨r.payload, birth, hstored, hb,
    prefix_record_mem initial rows J rewards s hactive count hspan j.val
      (Nat.le_of_lt j.isLt) birth hm, hbirth, ht.trans hb, ?_, ?_⟩
  · omega
  · omega

private theorem live_bridge (left right b : ℕ) (hspan : s + (right + 1) ≤ p.T)
    (hle : left ≤ right) (hold : b < s + left)
    (hg : localReleaseGate rate b ⟨s + left, by omega⟩
      (encodeState (ReferenceActivePhysicalHorizon.run initial rows J rewards s left
        (by omega) hactive).finalState) = true)
    (next : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters next) (base : Fin (p.m - 1) → ℕ)
    (hc : (ReferenceActivePhysicalHorizon.run initial rows J rewards s right
      (by omega) hactive).finalState.coordinator = .live next owned base)
    (hb : next.payload.sigma.val = b) :
    next.pendingAtChoice = ∅ ∧ next.priorClock.u = none ∧
      ∀ (j : ℕ) (_hj : left ≤ j) (_hk : j < right), localReleaseGate rate b ⟨s + j, by omega⟩
        (encodeState (ReferenceActivePhysicalHorizon.run initial rows J rewards s j
          (by omega) hactive).finalState) = true := by
  induction right generalizing next owned base with
  | zero =>
      have hleft : left = 0 := by omega
      subst left
      obtain ⟨r, q, oldBase, hr, _, he, _, hu⟩ := gate_live b _ _ hg
      rw [hc] at hr
      cases hr
      exact ⟨he, hu, fun j _ hj => by omega⟩
  | succ right ih =>
      by_cases heq : left = right + 1
      · subst left
        obtain ⟨r, q, oldBase, hr, _, he, _, hu⟩ := gate_live b _ _ hg
        rw [hc] at hr
        cases hr
        exact ⟨he, hu, fun j hj hk => by omega⟩
      · have hleft : left ≤ right := by omega
        let record := actualRunRecordAt initial rows J rewards s right (by omega) hactive
        have hout : (step record.input).next.coordinator = .live next owned base := by
          rw [run_successor_finalState_eq_actualRunRecordAt] at hc
          exact hc
        obtain ⟨r, q, oldBase, hr, hrb, started, hs, hf, hclock, hsub, _, hu⟩ :=
          step_old_live_predecessor record.input b next owned base hout hb (by
            change b < s + right
            omega)
        have hprefix : (ReferenceActivePhysicalHorizon.run initial rows J rewards s right
            (by omega) hactive).finalState.coordinator = .live r q oldBase := hr
        obtain ⟨he, hnone, hgates⟩ := ih (by omega) hleft hg r q oldBase hprefix hrb
        refine ⟨Finset.eq_empty_iff_forall_notMem.mpr (fun i hi => by
          have hm := hsub hi
          rw [he] at hm
          exact Finset.notMem_empty i hm), hu.trans hnone, ?_⟩
        intro j hj hk
        by_cases hjr : j < right
        · exact hgates j hj hjr
        · have hjr : j = right := by omega
          subst j
          exact gate_of_frame _ _ b r q oldBase hprefix hrb he hclock hnone started hs hf

/-- Gates with one birth stamp are order-convex on the actual run, across all
assignments and every exceptional dispatch/tail branch. -/
theorem run_gate_convex (count : ℕ) (hspan : s + count ≤ p.T)
    (hfirst : initial.coordinator = .first) (i j k : Fin count)
    (hij : i.val ≤ j.val) (hjk : j.val ≤ k.val) (b : ℕ)
    (hi : localReleaseGate rate b
      (actualRunRecordAt initial rows J rewards s i.val (by have _hi := i.isLt; omega) hactive).input.time
      (encodeState (actualRunRecordAt initial rows J rewards s i.val
        (by have _hi := i.isLt; omega) hactive).input.state) = true)
    (hk : localReleaseGate rate b
      (actualRunRecordAt initial rows J rewards s k.val (by have _hk := k.isLt; omega) hactive).input.time
      (encodeState (actualRunRecordAt initial rows J rewards s k.val
        (by have _hk := k.isLt; omega) hactive).input.state) = true) :
    localReleaseGate rate b
      (actualRunRecordAt initial rows J rewards s j.val (by have _hj := j.isLt; omega) hactive).input.time
      (encodeState (actualRunRecordAt initial rows J rewards s j.val
        (by have _hj := j.isLt; omega) hactive).input.state) = true := by
  by_cases hjk' : j.val = k.val
  · have heq : j = k := Fin.ext hjk'
    subst j
    exact hk
  · obtain ⟨_, _, _, _, _, _, _, _, hold⟩ := run_gate_birth
      initial rows J rewards s hactive count hspan hfirst i b hi
    obtain ⟨r, q, base, hc, hb, _, _, _⟩ := gate_live b _ _ hk
    have hbridge := live_bridge initial rows J rewards s hactive i.val k.val b
      (by have _hk := k.isLt; omega) (le_trans hij hjk) hold hi r q base hc hb
    exact hbridge.2.2 j.val hij (by omega)

theorem mem_run_gateSupport (count : ℕ) (hspan : s + count ≤ p.T) (b v : ℕ) :
    v ∈ gateSupport b
      (ReferenceActivePhysicalHorizon.run initial rows J rewards s count hspan hactive).records ↔
      ∃ j : Fin count, localReleaseGate rate b
        (actualRunRecordAt initial rows J rewards s j.val (by have _hj := j.isLt; omega) hactive).input.time
        (encodeState (actualRunRecordAt initial rows J rewards s j.val
          (by have _hj := j.isLt; omega) hactive).input.state) = true ∧ s + j.val + 1 = v := by
  rw [mem_gateSupport, records_eq_ofFn]
  constructor
  · rintro ⟨r, hr, hg, hv⟩
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hr
    exact ⟨j, hg, hv⟩
  · rintro ⟨j, hg, hv⟩
    exact ⟨_, List.mem_ofFn.mpr ⟨j, rfl⟩, hg, hv⟩

/-- Equality with the interval between the literal minimum and one-past-last
gates. This proves contiguity; neither endpoint was defined by a first-false
search or by an assumed phase interval. -/
theorem local_gate_support_eq_Ico (count : ℕ) (hspan : s + count ≤ p.T)
    (hfirst : initial.coordinator = .first) (b : ℕ) :
    let records := (ReferenceActivePhysicalHorizon.run initial rows J rewards s count hspan hactive).records
    gateSupport b records = Finset.Ico (gateAlpha b records) (gateBeta b records) := by
  intro records
  by_cases hne : (gateSupport b records).Nonempty
  · have hmin := Finset.min'_mem (gateSupport b records) hne
    have hmax := Finset.max'_mem (gateSupport b records) hne
    obtain ⟨i, hi, hiv⟩ := (mem_run_gateSupport initial rows J rewards s hactive count hspan b _).mp hmin
    obtain ⟨k, hk, hkv⟩ := (mem_run_gateSupport initial rows J rewards s hactive count hspan b _).mp hmax
    ext v
    simp only [gateAlpha, gateBeta, dite_eq_left hne, Finset.mem_Ico]
    constructor
    · intro hv
      exact ⟨Finset.min'_le _ _ hv, Nat.lt_succ_of_le (Finset.le_max' _ _ hv)⟩
    · rintro ⟨hlo, hhi⟩
      have hj : v - (s + 1) < count := by have _hk := k.isLt; omega
      let j : Fin count := ⟨v - (s + 1), hj⟩
      have hij : i.val ≤ j.val := by dsimp only [j]; omega
      have hjk : j.val ≤ k.val := by dsimp only [j]; omega
      have hgate := run_gate_convex initial rows J rewards s hactive count hspan hfirst i j k hij hjk b hi hk
      apply (mem_run_gateSupport initial rows J rewards s hactive count hspan b v).mpr
      exact ⟨j, hgate, by dsimp only [j]; omega⟩
  · have hempty := Finset.not_nonempty_iff_eq_empty.mp hne
    rw [hempty, (gate_endpoints_empty b records hempty).1,
      (gate_endpoints_empty b records hempty).2, Finset.Ico_self]

/-- Whole payload identity compares two independently extracted stored
endpoints on this run. Timestamp equality is used only after extraction. -/
theorem run_gates_payload_eq (count : ℕ) (hspan : s + count ≤ p.T)
    (hfirst : initial.coordinator = .first) (i j : Fin count) (b : ℕ)
    (hi : localReleaseGate rate b
      (actualRunRecordAt initial rows J rewards s i.val (by have _hi := i.isLt; omega) hactive).input.time
      (encodeState (actualRunRecordAt initial rows J rewards s i.val
        (by have _hi := i.isLt; omega) hactive).input.state) = true)
    (hj : localReleaseGate rate b
      (actualRunRecordAt initial rows J rewards s j.val (by have _hj := j.isLt; omega) hactive).input.time
      (encodeState (actualRunRecordAt initial rows J rewards s j.val
        (by have _hj := j.isLt; omega) hactive).input.state) = true) :
    ∃ left right,
      storedPayload (actualRunRecordAt initial rows J rewards s i.val
        (by have _hi := i.isLt; omega) hactive).input.state.coordinator = some left ∧
      storedPayload (actualRunRecordAt initial rows J rewards s j.val
        (by have _hj := j.isLt; omega) hactive).input.state.coordinator = some right ∧
      left.sigma.val = b ∧ right.sigma.val = b ∧ left = right := by
  obtain ⟨left, _, hl, hlb, _, _, _, _, _⟩ := run_gate_birth
    initial rows J rewards s hactive count hspan hfirst i b hi
  obtain ⟨right, _, hr, hrb, _, _, _, _, _⟩ := run_gate_birth
    initial rows J rewards s hactive count hspan hfirst j b hj
  refine ⟨left, right, hl, hr, hlb, hrb, ?_⟩
  exact run_prefix_storedPayload_eq_of_equal_sigma initial rows J rewards s count hspan hactive hfirst
    i.val j.val (Nat.le_of_lt i.isLt) (Nat.le_of_lt j.isLt) left right hl hr (hlb.trans hrb.symm)

/-- If the last gate precedes the observed-window endpoint, the next actual
record has a false gate. The record and every later suffix remain in the run. -/
theorem gateBeta_first_false (count : ℕ) (hspan : s + count ≤ p.T)
    (b : ℕ)
    (hne : (gateSupport b
      (ReferenceActivePhysicalHorizon.run initial rows J rewards s count hspan hactive).records).Nonempty) :
    let records := (ReferenceActivePhysicalHorizon.run initial rows J rewards s count hspan hactive).records
    gateBeta b records ≤ s + count + 1 ∧
      ∀ (j : Fin count), s + j.val + 1 = gateBeta b records →
        localReleaseGate rate b
          (actualRunRecordAt initial rows J rewards s j.val (by have _hj := j.isLt; omega) hactive).input.time
          (encodeState (actualRunRecordAt initial rows J rewards s j.val
            (by have _hj := j.isLt; omega) hactive).input.state) = false := by
  intro records
  have hbeta : gateBeta b records = (gateSupport b records).max' hne + 1 := by
    unfold gateBeta
    exact dite_eq_left hne
  have hmax := Finset.max'_mem (gateSupport b records) hne
  obtain ⟨k, _, htime⟩ := (mem_run_gateSupport initial rows J rewards s hactive count hspan b _).mp hmax
  constructor
  · rw [hbeta]
    have _hk := k.isLt
    omega
  · intro j hj
    apply Bool.eq_false_iff.mpr
    intro hg
    have hmem := (mem_run_gateSupport initial rows J rewards s hactive count hspan b _).mpr ⟨j, hg, hj⟩
    have hle : gateBeta b records ≤ (gateSupport b records).max' hne := Finset.le_max' _ _ hmem
    rw [hbeta] at hle
    omega

theorem run_gate_record_birth (count : ℕ) (hspan : s + count ≤ p.T)
    (hfirst : initial.coordinator = .first) (r : Record (p := p) (rate := rate))
    (hr : r ∈ (ReferenceActivePhysicalHorizon.run initial rows J rewards s count hspan hactive).records)
    (b : ℕ) (hg : localReleaseGate rate b r.input.time (encodeState r.input.state) = true) :
    ∃ payload birth, storedPayload r.input.state.coordinator = some payload ∧ payload.sigma.val = b ∧
      birth ∈ (ReferenceActivePhysicalHorizon.run initial rows J rewards s count hspan hactive).records ∧
      InstallationBirth birth payload ∧ birth.input.time.val = b ∧ s ≤ b ∧ b < r.input.time.val := by
  rw [records_eq_ofFn] at hr
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hr
  exact run_gate_birth initial rows J rewards s hactive count hspan hfirst j b hg

theorem run_gate_records_payload_eq (count : ℕ) (hspan : s + count ≤ p.T)
    (hfirst : initial.coordinator = .first) (r₁ r₂ : Record (p := p) (rate := rate))
    (h₁ : r₁ ∈ (ReferenceActivePhysicalHorizon.run initial rows J rewards s count hspan hactive).records)
    (h₂ : r₂ ∈ (ReferenceActivePhysicalHorizon.run initial rows J rewards s count hspan hactive).records)
    (b : ℕ) (hg₁ : localReleaseGate rate b r₁.input.time (encodeState r₁.input.state) = true)
    (hg₂ : localReleaseGate rate b r₂.input.time (encodeState r₂.input.state) = true) :
    ∃ payload birth, storedPayload r₁.input.state.coordinator = some payload ∧
      storedPayload r₂.input.state.coordinator = some payload ∧ payload.sigma.val = b ∧
      birth ∈ (ReferenceActivePhysicalHorizon.run initial rows J rewards s count hspan hactive).records ∧
      InstallationBirth birth payload ∧ birth.input.time.val = b ∧
      b < r₁.input.time.val ∧ b < r₂.input.time.val := by
  rw [records_eq_ofFn] at h₁ h₂
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp h₁
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp h₂
  obtain ⟨left, birth, hl, hlb, hm, hb, htime, _, hbefore₁⟩ :=
    run_gate_birth initial rows J rewards s hactive count hspan hfirst i b hg₁
  obtain ⟨right, _, hr, hrb, _, _, _, _, hbefore₂⟩ :=
    run_gate_birth initial rows J rewards s hactive count hspan hfirst j b hg₂
  have heq := run_prefix_storedPayload_eq_of_equal_sigma initial rows J rewards s count hspan hactive hfirst
    i.val j.val (Nat.le_of_lt i.isLt) (Nat.le_of_lt j.isLt) left right hl hr (hlb.trans hrb.symm)
  exact ⟨left, birth, hl, heq ▸ hr, hlb, hm, hb, htime, hbefore₁, hbefore₂⟩

end Run

/-- The existing physical run from the corrected launch option on the whole
original source. The original rows and original selected private J are used. -/
def sourceRun (rate : ReferenceActivePhysicalStep.RateInput p)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true)
    (s count : ℕ)
    (helapsed : ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed = s)
    (hspan : s + count ≤ p.T) :=
  ReferenceActivePhysicalHorizon.run (sourceSeed rate z rewards C_star C_h hcross)
    z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s count hspan
    (by simpa only [helapsed] using (canonical_seed_release_inputs rate z rewards C_star C_h hcross).2.1)

/-- Original-source all-assignment interval producer. Crossing and elapsed
are the computed launch branch; no state, trace, successful tail, queue law,
or phase interval is supplied. -/
theorem source_local_gate_interval (rate : ReferenceActivePhysicalStep.RateInput p)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true)
    (s count : ℕ)
    (helapsed : ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed = s)
    (hspan : s + count ≤ p.T) (b : ℕ) :
    let E := sourceRun rate z rewards C_star C_h hcross s count helapsed hspan
    gateSupport b E.records = Finset.Ico (gateAlpha b E.records) (gateBeta b E.records) ∧
      1 ≤ gateAlpha b E.records ∧ gateAlpha b E.records ≤ gateBeta b E.records ∧
      gateBeta b E.records ≤ p.T + 1 := by
  intro E
  refine ⟨?_, gate_endpoints_bounds b E.records⟩
  exact local_gate_support_eq_Ico _ _ _ _ _ _ count hspan
    (canonical_seed_release_inputs rate z rewards C_star C_h hcross).1 b

/-- No action is invented at a terminal launch or on any zero-count request. -/
theorem sourceRun_zero_records (rate : ReferenceActivePhysicalStep.RateInput p)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true)
    (s : ℕ)
    (helapsed : ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed = s)
    (hspan : s + 0 ≤ p.T) :
    (sourceRun rate z rewards C_star C_h hcross s 0 helapsed hspan).records = [] :=
  ReferenceActivePhysicalHorizon.run_zero_records _ _ _ _ _ _ _

theorem sourceRun_terminal_records (rate : ReferenceActivePhysicalStep.RateInput p)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true)
    (count : ℕ)
    (helapsed : ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed = p.T)
    (hspan : p.T + count ≤ p.T) :
    (sourceRun rate z rewards C_star C_h hcross p.T count helapsed hspan).records = [] := by
  have hcount : count = 0 := by omega
  subst count
  exact sourceRun_zero_records rate z rewards C_star C_h hcross p.T helapsed hspan

private theorem run_records_eq_of_seed_eq (left right : State p rate)
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (s count : ℕ) (hspan : s + count ≤ p.T)
    (hl : ReferenceActivePhysicalHorizon.allActiveAtStart left s)
    (hr : ReferenceActivePhysicalHorizon.allActiveAtStart right s) (heq : left = right) :
    (ReferenceActivePhysicalHorizon.run left rows J rewards s count hspan hl).records =
      (ReferenceActivePhysicalHorizon.run right rows J rewards s count hspan hr).records := by
  subst right
  rfl

/-- The all-assignment payload/birth producer on the original-source run.
The only record inputs select actual members and true local gates. -/
theorem source_gate_birth_and_payload_chronology (rate : ReferenceActivePhysicalStep.RateInput p)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true)
    (s count : ℕ)
    (helapsed : ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed = s)
    (hspan : s + count ≤ p.T) (b : ℕ) :
    let E := sourceRun rate z rewards C_star C_h hcross s count helapsed hspan
    ∀ r₁ ∈ E.records, ∀ r₂ ∈ E.records,
      localReleaseGate rate b r₁.input.time (encodeState r₁.input.state) = true →
      localReleaseGate rate b r₂.input.time (encodeState r₂.input.state) = true →
      ∃ payload birth, storedPayload r₁.input.state.coordinator = some payload ∧
        storedPayload r₂.input.state.coordinator = some payload ∧ payload.sigma.val = b ∧
        birth ∈ E.records ∧ InstallationBirth birth payload ∧ birth.input.time.val = b ∧
        b < r₁.input.time.val ∧ b < r₂.input.time.val := by
  intro E r₁ h₁ r₂ h₂ hg₁ hg₂
  exact run_gate_records_payload_eq _ _ _ _ _ _ count hspan
    (canonical_seed_release_inputs rate z rewards C_star C_h hcross).1 r₁ r₂ h₁ h₂ b hg₁ hg₂

section Launch

variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
  (hs : s ≤ t.val) (control0 : ContinuousLearningRows.TimeControl p)

local notation "X" => LaunchStart rate rewards C_star C_h q t s hs control0

theorem launch_parts (x : X) :
    x.val ∈ ReferenceFixedTimeSourceControlCoupling.fixedControlRemainderStratum p q t ∧
      x.val ∈ ReferenceInitializationControlRemainder.launchStartRemainderEvent
        rate rewards C_star C_h q t s control0 := x.property

theorem launch_event (x : X) (u : ContinuousLearningRows.TimeControl p) :
    x.val ∈ ReferenceInitializationControlRemainder.launchStartRemainderEvent
      rate rewards C_star C_h q t s u :=
  (ReferenceInitializationControlRemainder.launchStartRemainderEvent_control_independent
    rate rewards C_star C_h q t s x.val (launch_parts rate rewards C_star C_h q t s hs control0 x).1
    control0 u).mp (launch_parts rate rewards C_star C_h q t s hs control0 x).2

/-- Direct alias of the existing generated seed on this launch stratum. -/
def launchSeed (x : X) (u : ContinuousLearningRows.TimeControl p) : State p rate :=
  ReferenceGeneratedActivePrefixFactor.generatedActiveSeed rate rewards C_star C_h q t u x.val
    (launch_parts rate rewards C_star C_h q t s hs control0 x).1 s hs
    (launch_event rate rewards C_star C_h q t s hs control0 x u)

theorem launchSeed_release_inputs (x : X) (u : ContinuousLearningRows.TimeControl p) :
    (launchSeed rate rewards C_star C_h q t s hs control0 x u).coordinator = .first ∧
      ReferenceActivePhysicalHorizon.allActiveAtStart
        (launchSeed rate rewards C_star C_h q t s hs control0 x u) s ∧
      ReferenceFirstLiveConfirmationHistory.InitialFollowers
        (launchSeed rate rewards C_star C_h q t s hs control0 x u) := by
  have hrem := (launch_parts rate rewards C_star C_h q t s hs control0 x).1
  have hevent := launch_event rate rewards C_star C_h q t s hs control0 x u
  have hf := ReferenceGeneratedActivePrefixFactor.launchStart_source_facts
    rate rewards C_star C_h q t u x.val hrem s hs hevent
  have hi := canonical_seed_release_inputs rate
    (ReferenceGeneratedActivePrefixFactor.splitSource q t u x.val) rewards C_star C_h hf.1
  simpa only [launchSeed, sourceSeed, ReferenceGeneratedActivePrefixFactor.generatedActiveSeed, hf.2] using hi

/-- Includes the physical record at the current incoming coordinate. Every
replacement uses its own whole source rows and original private coordinates. -/
def launchRun (x : X) (u : ContinuousLearningRows.TimeControl p) :=
  let z := ReferenceGeneratedActivePrefixFactor.splitSource q t u x.val
  ReferenceActivePhysicalHorizon.run (launchSeed rate rewards C_star C_h q t s hs control0 x u)
    z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s (t.val - s + 1)
    (by have _ht := t.isLt; omega)
    (launchSeed_release_inputs rate rewards C_star C_h q t s hs control0 x u).2.1

theorem launchRun_gate_interval (x : X) (u : ContinuousLearningRows.TimeControl p) (b : ℕ) :
    let E := launchRun rate rewards C_star C_h q t s hs control0 x u
    gateSupport b E.records = Finset.Ico (gateAlpha b E.records) (gateBeta b E.records) := by
  exact local_gate_support_eq_Ico _ _ _ _ _ _ _ _
    (launchSeed_release_inputs rate rewards C_star C_h q t s hs control0 x u).1 b

theorem launchRun_gate_birth_and_payload_chronology
    (x : X) (u : ContinuousLearningRows.TimeControl p) (b : ℕ) :
    let E := launchRun rate rewards C_star C_h q t s hs control0 x u
    ∀ r₁ ∈ E.records, ∀ r₂ ∈ E.records,
      localReleaseGate rate b r₁.input.time (encodeState r₁.input.state) = true →
      localReleaseGate rate b r₂.input.time (encodeState r₂.input.state) = true →
      ∃ payload birth, storedPayload r₁.input.state.coordinator = some payload ∧
        storedPayload r₂.input.state.coordinator = some payload ∧ payload.sigma.val = b ∧
        birth ∈ E.records ∧ InstallationBirth birth payload ∧ birth.input.time.val = b ∧
        b < r₁.input.time.val ∧ b < r₂.input.time.val := by
  intro E r₁ h₁ r₂ h₂ hg₁ hg₂
  exact run_gate_records_payload_eq _ _ _ _ _ _ _ _
    (launchSeed_release_inputs rate rewards C_star C_h q t s hs control0 x u).1 r₁ r₂ h₁ h₂ b hg₁ hg₂

private theorem generatedPhaseBefore_record (x : X) (u : ContinuousLearningRows.TimeControl p)
    (j : Fin (t.val - s + 1)) :
    generatedPhaseBefore rate rewards C_star C_h q t s hs control0 x u j =
      encodeState (actualRunRecordAt
        (launchSeed rate rewards C_star C_h q t s hs control0 x u)
        (ReferenceGeneratedActivePrefixFactor.splitSource q t u x.val).1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p
          (ReferenceGeneratedActivePrefixFactor.splitSource q t u x.val)) rewards s j.val
        (by have _hj := j.isLt; have _ht := t.isLt; omega)
        (launchSeed_release_inputs rate rewards C_star C_h q t s hs control0 x u).2.1).input.state := by
  rfl

/-- R's whole gate/pending entry is the entry of the actual inclusive run.
Only incoming states are compared across replacement controls. -/
theorem releaseEntries_run_record (x : X) (u : ContinuousLearningRows.TimeControl p)
    (b : ℕ) (j : Fin (t.val - s + 1)) :
    ReferenceReleaseStrictPastFactor.releaseEntries rate rewards C_star C_h q t s hs control0 b x j =
      localReleaseEntry rate b
        ((launchRun rate rewards C_star C_h q t s hs control0 x u).records[j.val]'(by
          simp only [launchRun, ReferenceActivePhysicalHorizon.run_record_count]; exact j.isLt)).input.time
        (encodeState ((launchRun rate rewards C_star C_h q t s hs control0 x u).records[j.val]'(by
          simp only [launchRun, ReferenceActivePhysicalHorizon.run_record_count]; exact j.isLt)).input.state) := by
  unfold ReferenceReleaseStrictPastFactor.releaseEntries
  rw [← ReferenceReleaseStrictPastFactor.phaseFactor_eq rate rewards C_star C_h q t s hs control0 x control0,
    ReferenceReleaseStrictPastFactor.phaseFactor_eq rate rewards C_star C_h q t s hs control0 x u,
    generatedPhaseBefore_record]
  simp only [launchRun, run_record_at]
  rfl

theorem mem_launchRun_gateSupport (x : X) (u : ContinuousLearningRows.TimeControl p) (b v : ℕ) :
    v ∈ gateSupport b (launchRun rate rewards C_star C_h q t s hs control0 x u).records ↔
      ∃ j : Fin (t.val - s + 1),
        (ReferenceReleaseStrictPastFactor.releaseEntries rate rewards C_star C_h q t s hs control0 b x j).1 = true ∧
        s + j.val + 1 = v := by
  rw [mem_gateSupport]
  simp only [launchRun, records_eq_ofFn, List.mem_ofFn]
  constructor
  · rintro ⟨r, ⟨j, rfl⟩, hg, hv⟩
    refine ⟨j, ?_, hv⟩
    have heq := congrArg Prod.fst
      (releaseEntries_run_record rate rewards C_star C_h q t s hs control0 x u b j)
    simp only [launchRun, run_record_at, localReleaseEntry] at heq
    exact heq.trans hg
  · rintro ⟨j, hg, hv⟩
    refine ⟨_, ⟨j, rfl⟩, ?_, hv⟩
    have heq := congrArg Prod.fst
      (releaseEntries_run_record rate rewards C_star C_h q t s hs control0 x u b j)
    simp only [launchRun, run_record_at, localReleaseEntry] at heq
    exact heq.symm.trans hg

/-- Pointwise form of the actual interval. Together with `gateBeta_first_false`,
this identifies the first false gate after entry, or the observed-window end. -/
theorem releaseEntries_gate_iff_Ico (x : X) (u : ContinuousLearningRows.TimeControl p)
    (b : ℕ) (j : Fin (t.val - s + 1)) :
    let E := launchRun rate rewards C_star C_h q t s hs control0 x u
    (ReferenceReleaseStrictPastFactor.releaseEntries rate rewards C_star C_h q t s hs control0 b x j).1 = true ↔
      gateAlpha b E.records ≤ s + j.val + 1 ∧ s + j.val + 1 < gateBeta b E.records := by
  intro E
  have hinterval := launchRun_gate_interval rate rewards C_star C_h q t s hs control0 x u b
  constructor
  · intro hg
    have hm := (mem_launchRun_gateSupport rate rewards C_star C_h q t s hs control0 x u b _).mpr ⟨j, hg, rfl⟩
    rw [hinterval, Finset.mem_Ico] at hm
    exact hm
  · intro hj
    have hm : s + j.val + 1 ∈ gateSupport b E.records := by
      rw [hinterval, Finset.mem_Ico]
      exact hj
    obtain ⟨k, hk, htime⟩ :=
      (mem_launchRun_gateSupport rate rewards C_star C_h q t s hs control0 x u b _).mp hm
    have heq : k = j := Fin.ext (by omega)
    subst k
    exact hk

/-- Exact agreement with O's first-gate search, including its `T+1` empty
sentinel when the observed window ends strictly before the horizon. -/
theorem gateAlpha_eq_firstLocalReleaseGateRound (x : X) (u : ContinuousLearningRows.TimeControl p) (b : ℕ) :
    gateAlpha b (launchRun rate rewards C_star C_h q t s hs control0 x u).records =
      firstLocalReleaseGateRound rate rewards C_star C_h q t s hs control0 x b := by
  let records := (launchRun rate rewards C_star C_h q t s hs control0 x u).records
  let first := firstLocalReleaseGateRound rate rewards C_star C_h q t s hs control0 x b
  have hfirstBound : first ≤ p.T + 1 :=
    firstLocalReleaseGateRound_le_horizon rate rewards C_star C_h q t s hs control0 x b
  have hsublevel (n : ℕ) (hn : n < p.T + 1) :
      first ≤ n ↔ ∃ v ∈ gateSupport b records, v ≤ n := by
    rw [firstLocalReleaseGateRound_le_iff rate rewards C_star C_h q t s hs control0 x b n hn]
    constructor
    · rintro ⟨j, hg, hj⟩
      refine ⟨s + j.val + 1, ?_, hj⟩
      apply (mem_launchRun_gateSupport rate rewards C_star C_h q t s hs control0 x u b _).mpr
      exact ⟨j, hg, rfl⟩
    · rintro ⟨v, hv, hn⟩
      obtain ⟨j, hg, rfl⟩ :=
        (mem_launchRun_gateSupport rate rewards C_star C_h q t s hs control0 x u b v).mp hv
      exact ⟨j, hg, hn⟩
  by_cases hne : (gateSupport b records).Nonempty
  · have hmem := Finset.min'_mem (gateSupport b records) hne
    have hbounds := gateSupport_bounds b _ records hmem
    have hα : gateAlpha b records = (gateSupport b records).min' hne := by
      unfold gateAlpha
      exact dite_eq_left hne
    have hfirst : first ≤ (gateSupport b records).min' hne :=
      (hsublevel _ (by omega)).mpr ⟨_, hmem, le_rfl⟩
    have hfirstLt : first < p.T + 1 := by omega
    obtain ⟨v, hv, hvfirst⟩ := (hsublevel first hfirstLt).mp le_rfl
    have hmin := Finset.min'_le _ _ hv
    change gateAlpha b records = first
    rw [hα]
    omega
  · have hfirst : first = p.T + 1 := by
      by_contra hneFirst
      have hlt : first < p.T + 1 := by omega
      obtain ⟨v, hv, _⟩ := (hsublevel first hlt).mp le_rfl
      exact hne ⟨v, hv⟩
    change gateAlpha b records = first
    rw [hfirst]
    unfold gateAlpha
    exact dite_eq_right hne

end Launch

/-- Original-source specialization uses the actual split control of `z`.
This equality compares executions of the SAME source, not records or feedback
under two distinct replacement controls. -/
theorem launchRun_original_source (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (q : Fin (M p)) (t : Fin p.T) (s : ℕ) (hs : s ≤ t.val)
    (control0 : ContinuousLearningRows.TimeControl p) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hselected : ActualInitializationPhysicalStep.selectedRowIndex p z = q)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true)
    (helapsed : ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed = s) :
    let split := ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t z
    let x := ReferenceRetainedBoundaryMeasurability.retainedLaunchStartInputOfSource
      rate rewards C_star C_h q t s hs control0 z hselected hcross helapsed
    (launchRun rate rewards C_star C_h q t s hs control0 x split.1).records =
      (sourceRun rate z rewards C_star C_h hcross s (t.val - s + 1) helapsed
        (by have _ht := t.isLt; omega)).records := by
  intro split x
  have hsource : ReferenceGeneratedActivePrefixFactor.splitSource q t split.1 x.val = z := by
    change (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t).symm
      ((ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t z).1,
        (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t z).2) = z
    exact (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t).symm_apply_apply z
  have hl := (ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec
    rate rewards C_star C_h q t split.1 x.val
      (launch_parts rate rewards C_star C_h q t s hs control0 x).1 s hs
      (launch_event rate rewards C_star C_h q t s hs control0 x split.1)).1
  have hl' : ReferenceCorrectedInitializationLaunch.correctedLaunch rate z rewards C_star C_h =
      some (launchSeed rate rewards C_star C_h q t s hs control0 x split.1) := by
    change ReferenceCorrectedInitializationLaunch.correctedLaunch rate
      (ReferenceGeneratedActivePrefixFactor.splitSource q t split.1 x.val) rewards C_star C_h =
      some (launchSeed rate rewards C_star C_h q t s hs control0 x split.1) at hl
    rw [hsource] at hl
    exact hl
  have hseed := Option.some.inj
    (hl'.symm.trans (sourceSeed_launch rate z rewards C_star C_h hcross))
  simp only [launchRun, hsource, sourceRun]
  exact run_records_eq_of_seed_eq _ _ _ _ _ _ _ _ _ _ hseed

/-- Every R entry specializes to the actual original-source physical record,
including the current incoming coordinate and any failing tail after it. -/
theorem releaseEntries_original_source_record (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (q : Fin (M p)) (t : Fin p.T) (s : ℕ) (hs : s ≤ t.val)
    (control0 : ContinuousLearningRows.TimeControl p) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hselected : ActualInitializationPhysicalStep.selectedRowIndex p z = q)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true)
    (helapsed : ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed = s)
    (b : ℕ) :
    let x := ReferenceRetainedBoundaryMeasurability.retainedLaunchStartInputOfSource
      rate rewards C_star C_h q t s hs control0 z hselected hcross helapsed
    let E := sourceRun rate z rewards C_star C_h hcross s (t.val - s + 1) helapsed
      (by have _ht := t.isLt; omega)
    ∀ j : Fin (t.val - s + 1),
      ReferenceReleaseStrictPastFactor.releaseEntries rate rewards C_star C_h q t s hs control0 b x j =
        localReleaseEntry rate b (E.records[j.val]'(by
          simp only [E, sourceRun, ReferenceActivePhysicalHorizon.run_record_count]; exact j.isLt)).input.time
          (encodeState (E.records[j.val]'(by
            simp only [E, sourceRun, ReferenceActivePhysicalHorizon.run_record_count]; exact j.isLt)).input.state) := by
  intro x E j
  have hr := releaseEntries_run_record rate rewards C_star C_h q t s hs control0 x
    (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t z).1 b j
  have heq := launchRun_original_source rate rewards C_star C_h q t s hs control0 z
    hselected hcross helapsed
  change (launchRun rate rewards C_star C_h q t s hs control0 x
    (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t z).1).records = E.records at heq
  simpa only [heq] using hr

/-- Intersect the actual local interval with an arbitrary source-round
endpoint. Both endpoints are reset to `T+1` on empty intersection. No stopping
time or source first-error interpretation of `v` is asserted. -/
theorem source_gate_interval_restrict (rate : ReferenceActivePhysicalStep.RateInput p)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true)
    (s count : ℕ)
    (helapsed : ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed = s)
    (hspan : s + count ≤ p.T) (b v : ℕ) (hv : 1 ≤ v ∧ v ≤ p.T + 1) :
    let E := sourceRun rate z rewards C_star C_h hcross s count helapsed hspan
    let α := gateAlpha b E.records
    let β := min (gateBeta b E.records) v
    let left := if α < β then α else p.T + 1
    let right := if α < β then β else p.T + 1
    (gateSupport b E.records).filter (· < v) = Finset.Ico left right ∧
      1 ≤ left ∧ left ≤ right ∧ right ≤ p.T + 1 := by
  intro E α β left right
  have hinterval := (source_local_gate_interval rate z rewards C_star C_h hcross s count helapsed hspan b).1
  have hbounds := gate_endpoints_bounds b E.records
  have hfilter : (gateSupport b E.records).filter (· < v) = Finset.Ico α β := by
    rw [hinterval, Finset.Ico_filter_lt]
  by_cases h : α < β
  · have hleft : left = α := ite_eq_left h
    have hright : right = β := ite_eq_left h
    rw [hleft, hright]
    refine ⟨hfilter, hbounds.1, Nat.le_of_lt h, ?_⟩
    exact (min_le_right _ _).trans hv.2
  · have hleft : left = p.T + 1 := ite_eq_right h
    have hright : right = p.T + 1 := ite_eq_right h
    rw [hleft, hright]
    have hempty : Finset.Ico α β = ∅ := Finset.Ico_eq_empty_of_le (Nat.le_of_not_gt h)
    refine ⟨?_, by omega, le_rfl, le_rfl⟩
    rw [hfilter, hempty, Finset.Ico_self]

end Bandits.Support.ReferenceLocalReleaseGateChronology

end
