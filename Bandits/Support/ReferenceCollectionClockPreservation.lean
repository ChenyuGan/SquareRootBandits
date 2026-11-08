/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCoordinatorClockDomains

/-!
# Collection clock frames in the actual reference step

Sources: `sources/zip4/manuscript/06_interruptions.tex:9-14,40-70,246-247,277-294`
and `sources/zip4/manuscript/appendix_a_local_protocol.tex:8-14,30-44,81-84`.

The cutoff branch initializes the source sigma, cutoff and clipped freeze boundary.
Recording, queue service (including enabled zero arrivals and disabled rounds),
filtered UP reception, and finishing preserve these three coordinates. Ordinary
rejection retains its actual ledger and decoder bank; checked failures enter dagger.
The invariant here is exactly `ReferenceCoordinatorClockDomains.clockAt`.

These are conditional internal transition results, for the two indicated actual
dispatcher outcomes only. No global step/run induction, accepted-message truth,
score/queue correspondence, no-error result, sampler law, or regret closure is claimed.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions

namespace Bandits.Support.ReferenceCollectionClockPreservation

variable {p : ConstructorDimensions.Parameters} {rate : ReferenceActivePhysicalStep.RateInput p}

/-- The checked stage-(1) candidate changes neither sigma, cutoff nor freeze,
for either service bit and every recorder output, including no raw arrival. -/
theorem ledger_startRound_frame (ledger out : ReferenceActivePhysicalStep.Ledger rate) (time : Fin p.T)
    (enabled : Bool) (raw : Option (Fin p.K × ℕ))
    (h : CoordinatorCollectionLedger.startRound ledger (time.val + 1) enabled raw = .success out) :
    out.sigma = ledger.sigma ∧ out.cutoff = ledger.cutoff ∧
      out.freezeAt = ledger.freezeAt := by
  have hc := CoordinatorCollectionUpRoundStep.InputsValid.startRound_success_candidate
    ledger (time.val + 1) (by omega) (Nat.succ_le_of_lt time.isLt) enabled raw out h
  rw [hc]
  exact ⟨rfl, rfl, rfl⟩

/-- The actual checked finish changes the accumulator, cursor and phase;
the three collection clock coordinates remain unchanged. -/
theorem ledger_finishRound_frame (ledger out : ReferenceActivePhysicalStep.Ledger rate)
    (h : CoordinatorCollectionLedger.finishRound ledger = .success out) :
    out.sigma = ledger.sigma ∧ out.cutoff = ledger.cutoff ∧
      out.freezeAt = ledger.freezeAt := by
  rw [CoordinatorCollectionUpRoundStep.InputsValid.finishRound_success_candidate ledger out h]
  exact ⟨rfl, rfl, rfl⟩

/-- Every non-invalid ledger decode preserves the collection frame. In
particular an ordinary parser/acceptance rejection is not treated as dagger. -/
theorem ledger_decodeUp_frame (ledger : ReferenceActivePhysicalStep.Ledger rate) (i : Fin (p.m - 1))
    (parsed : Option (OrdinaryMessageCodec.UpRecord (CoordinatorCollectionLedger.codecParams p rate.eta.val)))
    (out : ReferenceActivePhysicalStep.Ledger rate)
    (h : CoordinatorCollectionLedger.decodeUp ledger i parsed = .success out ∨
      CoordinatorCollectionLedger.decodeUp ledger i parsed = .rejected out) :
    out.sigma = ledger.sigma ∧ out.cutoff = ledger.cutoff ∧
      out.freezeAt = ledger.freezeAt := by
  classical
  by_cases hd : CoordinatorCollectionLedger.validLedgerCheck ledger = true ∧ ledger.phase = .started ∧
      1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ ledger.cursor ∧ ledger.cursor ≤ p.T
  · rcases h with hs | hr
    · obtain ⟨M, past, current, _, hout, _, _⟩ :=
        CoordinatorCollectionUpRoundStep.InputsValid.decodeUp_success_candidate
          ledger i parsed out hd hs
      rw [hout]
      exact ⟨rfl, rfl, rfl⟩
    · unfold CoordinatorCollectionLedger.decodeUp at hr
      rw [dite_eq_left hd] at hr
      cases parsed with
      | none =>
          dsimp only at hr
          split_ifs at hr with hv
          injection hr with hout
          rw [← hout]
          exact ⟨rfl, rfl, rfl⟩
      | some M =>
          dsimp only at hr
          by_cases ha : CoordinatorCollectionLedger.acceptUpCheck ledger i M = true
          · rw [ite_eq_left ha] at hr
            split at hr
            · split at hr
              · rename_i past last hpast hlast
                cases last with
                | nil => cases hr
                | cons record tail =>
                    cases tail with
                    | nil => dsimp only at hr; split_ifs at hr
                    | cons record' tail' => cases hr
              · cases hr
            · cases hr
          · rw [ite_eq_right ha] at hr
            split_ifs at hr with hv
            injection hr with hout
            rw [← hout]
            exact ⟨rfl, rfl, rfl⟩
  · simp only [CoordinatorCollectionLedger.decodeUp, dite_eq_right hd] at h
    cases h <;> contradiction

private theorem packDecodeResult_frame
    (ledger : ReferenceActivePhysicalStep.Ledger rate) (i : Fin (p.m - 1))
    (parsed : Option (OrdinaryMessageCodec.UpRecord (CoordinatorCollectionLedger.codecParams p rate.eta.val)))
    (bank : CoordinatorUpReception.UpDecoderBank p)
    (out : ReferenceActivePhysicalStep.Ledger rate × CoordinatorUpReception.UpDecoderBank p)
    (h : CoordinatorUpReception.packDecodeResult (CoordinatorCollectionLedger.decodeUp ledger i parsed) bank =
        .success out ∨
      CoordinatorUpReception.packDecodeResult (CoordinatorCollectionLedger.decodeUp ledger i parsed) bank =
        .rejected out) :
    out.1.sigma = ledger.sigma ∧ out.1.cutoff = ledger.cutoff ∧
      out.1.freezeAt = ledger.freezeAt := by
  cases hd : CoordinatorCollectionLedger.decodeUp ledger i parsed with
  | invalid => simp only [hd, CoordinatorUpReception.packDecodeResult] at h; cases h <;> contradiction
  | success decoded =>
      simp only [hd, CoordinatorUpReception.packDecodeResult] at h
      have ho : out = (decoded, bank) := by
        rcases h with h | h
        · exact (CoordinatorCollectionLedger.Checked.success.inj h).symm
        · cases h
      rw [ho]
      exact ledger_decodeUp_frame ledger i parsed decoded (Or.inl hd)
  | rejected decoded =>
      simp only [hd, CoordinatorUpReception.packDecodeResult] at h
      have ho : out = (decoded, bank) := by
        rcases h with h | h
        · cases h
        · exact (CoordinatorCollectionLedger.Checked.rejected.inj h).symm
      rw [ho]
      exact ledger_decodeUp_frame ledger i parsed decoded (Or.inr hd)

/-- Frame preservation for the actual reference-filtered receiver. Its parsed
input is the literal filtered raw output, so this includes wrong-unique
suppression without any correctness premise about accepted replies. -/
theorem receiveUp_frame {x : ReferenceActivePhysicalStep.RoundInput p rate} (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (out : ReferenceActivePhysicalStep.Ledger rate × CoordinatorUpReception.UpDecoderBank p)
    (h : (ReferenceActivePhysicalStep.receiveUp prepared ledger).result = .success out ∨
      (ReferenceActivePhysicalStep.receiveUp prepared ledger).result = .rejected out) :
    out.1.sigma = ledger.sigma ∧ out.1.cutoff = ledger.cutoff ∧
      out.1.freezeAt = ledger.freezeAt := by
  classical
  unfold ReferenceActivePhysicalStep.receiveUp at h
  dsimp only at h
  unfold ReferenceUpReception.receiveUpFilteredAtRow at h
  dsimp only at h
  split at h
  · exact packDecodeResult_frame _ _ _ _ out h
  · cases h <;> contradiction

/-- The three clock-related core fields follow from the literal invariant.
No remaining `CollectionCoreValid` field is assumed or concluded. The finite
cutoff index is exactly the ledger cutoff minus one. -/
theorem collection_clock_fields {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (payload : ReferenceActivePhysicalStep.Payload rate) (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (saved : Option (Fin p.T × Bool))
    (hstate : x.state.coordinator = .collection payload ledger saved)
    (hclock : ReferenceCoordinatorClockDomains.clockAt x.rows x.selected x.time.val x.state)
    (cutoff : Fin p.T) (hcutoff : cutoff.val = ledger.cutoff - 1) :
    let input := ReferenceActivePhysicalStep.collectionInput x payload ledger
      (ReferenceActivePhysicalStep.collectionClock payload ledger saved cutoff) cutoff
    CoordinatorPhaseClock.proposalParameterValid p input.etaReal ∧
      CoordinatorPhaseClock.clockRegistersValid p input.etaReal input.clock ∧
      CoordinatorPhaseClock.startRoundTimeValid p input.time input.clock := by
  have hinv := hclock
  simp only [ReferenceCoordinatorClockDomains.clockAt, hstate] at hinv
  rcases hinv with ⟨_, horder, hpos, _, htime, hfreeze, hcutFreeze, hfreezeBound⟩
  refine ⟨ReferenceCoordinatorClockDomains.proposalParameterValid_of_rate rate, ?_, ?_⟩
  · change ledger.freezeAt = FollowerCutoffScan.gridBoundary p rate.eta.val payload.sigma ∧
      payload.sigma.val + 1 < ledger.freezeAt ∧ ledger.freezeAt ≤ p.T + 1 ∧
      payload.sigma.val < cutoff.val ∧ cutoff.val + 1 ≤ ledger.freezeAt
    exact ⟨hfreeze, by omega, hfreezeBound, by omega, by omega⟩
  · change payload.sigma.val < x.time.val ∧ cutoff.val ≤ x.time.val
    omega

/-- The exact existing collection start-call safety result, paired with the
three clock fields needed by the future actual collection core consumer. -/
theorem collection_clock_call {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (payload : ReferenceActivePhysicalStep.Payload rate) (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (saved : Option (Fin p.T × Bool))
    (hstate : x.state.coordinator = .collection payload ledger saved)
    (hclock : ReferenceCoordinatorClockDomains.clockAt x.rows x.selected x.time.val x.state)
    (cutoff : Fin p.T) (hcutoff : cutoff.val = ledger.cutoff - 1) :
    ∃ started, CoordinatorPhaseClock.startRound p rate.eta.val x.time
      (ReferenceActivePhysicalStep.collectionClock payload ledger saved cutoff) ledger.pending = .ok started := by
  exact ReferenceCoordinatorClockDomains.collection_startRound_success x.rows x.selected x.time.val x.state
    payload ledger saved hstate hclock x.time cutoff rfl hcutoff

private theorem collection_clockAt_of_frame
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (k : ℕ) (state : ReferenceActivePhysicalStep.State p rate) (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger out : ReferenceActivePhysicalStep.Ledger rate) (saved saved' : Option (Fin p.T × Bool))
    (hclock : ReferenceCoordinatorClockDomains.clockAt rows selected k
      { state with coordinator := .collection payload ledger saved })
    (hframe : out.sigma = ledger.sigma ∧ out.cutoff = ledger.cutoff ∧
      out.freezeAt = ledger.freezeAt) :
    ReferenceCoordinatorClockDomains.clockAt rows selected k { state with coordinator := .collection payload out saved' } := by
  simpa only [ReferenceCoordinatorClockDomains.clockAt, hframe.1, hframe.2.1, hframe.2.2] using hclock

private theorem collectionFinish_clockAt {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (payload : ReferenceActivePhysicalStep.Payload rate) (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (saved : Option (Fin p.T × Bool)) (started : CoordinatorPhaseClock.StartRoundResult p)
    (recording : CoordinatorRecordingOperation.Output p) (cut : ReferenceActivePhysicalStep.UpCut p rate)
    (hclock : ReferenceCoordinatorClockDomains.clockAt x.rows x.selected (x.time.val + 1)
      { x.state with coordinator := .collection payload ledger saved })
    (hframe : ∀ out, cut.result = .success out ∨ cut.result = .rejected out →
      out.1.sigma = ledger.sigma ∧ out.1.cutoff = ledger.cutoff ∧
        out.1.freezeAt = ledger.freezeAt) :
    ReferenceCoordinatorClockDomains.clockAt x.rows x.selected (x.time.val + 1)
      { x.state with coordinator := (ReferenceActivePhysicalStep.collectionFinish (x := x)
        payload started recording cut).configuration } := by
  classical
  have hfinish : ∀ decoded bank,
      (cut.result = .success (decoded, bank) ∨ cut.result = .rejected (decoded, bank)) →
      ReferenceCoordinatorClockDomains.clockAt x.rows x.selected (x.time.val + 1)
        { x.state with coordinator := (ReferenceActivePhysicalStep.collectionFinish (x := x)
          payload started recording cut).configuration } := by
    intro decoded bank hdecoded
    have hf := hframe (decoded, bank) hdecoded
    cases he : CoordinatorCollectionLedger.finishRound decoded with
    | invalid =>
        rcases hdecoded with h | h <;>
          simp only [ReferenceActivePhysicalStep.collectionFinish, h, he, ReferenceActivePhysicalStep.coordinatorFailure, ReferenceCoordinatorClockDomains.clockAt]
    | rejected rejected =>
        rcases hdecoded with h | h <;>
          simp only [ReferenceActivePhysicalStep.collectionFinish, h, he, ReferenceActivePhysicalStep.coordinatorFailure, ReferenceCoordinatorClockDomains.clockAt]
    | success finished =>
        have hff := ledger_finishRound_frame decoded finished he
        cases hc : CoordinatorPhaseClock.finishRound p rate.eta.val x.time started.clock finished.pending x.row with
        | error reason =>
            rcases hdecoded with h | h <;>
              simp only [ReferenceActivePhysicalStep.collectionFinish, h, he, hc, ReferenceActivePhysicalStep.coordinatorFailure, ReferenceCoordinatorClockDomains.clockAt]
        | ok clockFinished =>
            rw [ReferenceActivePhysicalStep.collectionFinish_success payload started recording cut decoded finished bank
              clockFinished hdecoded he hc]
            exact collection_clockAt_of_frame x.rows x.selected (x.time.val + 1)
              x.state payload ledger finished saved clockFinished.clock.lastProposal hclock
              ⟨hff.1.trans hf.1, hff.2.1.trans hf.2.1, hff.2.2.trans hf.2.2⟩
  cases hr : cut.result with
  | invalid => simp only [ReferenceActivePhysicalStep.collectionFinish, hr, ReferenceActivePhysicalStep.coordinatorFailure, ReferenceCoordinatorClockDomains.clockAt]
  | rejected pair => exact hfinish pair.1 pair.2 (Or.inr hr)
  | success pair => exact hfinish pair.1 pair.2 (Or.inl hr)

/-- The actual entire collection tail preserves the incoming clock frame.
This helper takes only `clockAt` at this calendar boundary, and evaluates all
recorder, service, receiver and finish failures rather than assuming success. -/
theorem collectionPostChoice_clockAt {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (prepared : ReferenceActivePhysicalStep.PreparedRound x) (payload : ReferenceActivePhysicalStep.Payload rate) (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (saved : Option (Fin p.T × Bool)) (started : CoordinatorPhaseClock.StartRoundResult p)
    (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ)
    (hclock : ReferenceCoordinatorClockDomains.clockAt x.rows x.selected (x.time.val + 1)
      { x.state with coordinator := .collection payload ledger saved }) :
    ReferenceCoordinatorClockDomains.clockAt x.rows x.selected (x.time.val + 1)
      { x.state with coordinator :=
        (ReferenceActivePhysicalStep.collectionPostChoice prepared payload ledger started weights).configuration } := by
  classical
  cases hr : CoordinatorRecorderComplementBridge.run
      (ReferenceActivePhysicalStep.collectionRecordingInput prepared payload started weights) with
  | none => simp only [ReferenceActivePhysicalStep.collectionPostChoice, hr, ReferenceActivePhysicalStep.coordinatorFailure, ReferenceCoordinatorClockDomains.clockAt]
  | some recording =>
      cases hs : CoordinatorCollectionLedger.startRound ledger (x.time.val + 1) (ReferenceActivePhysicalStep.collectionEnabled ledger x.time)
          (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) with
      | invalid => simp only [ReferenceActivePhysicalStep.collectionPostChoice, hr, hs, ReferenceActivePhysicalStep.coordinatorFailure, ReferenceCoordinatorClockDomains.clockAt]
      | rejected rejected =>
          simp only [ReferenceActivePhysicalStep.collectionPostChoice, hr, hs, ReferenceActivePhysicalStep.coordinatorFailure, ReferenceCoordinatorClockDomains.clockAt]
      | success ledgerStarted =>
          rw [ReferenceActivePhysicalStep.collectionPostChoice_after_start prepared payload ledger started weights
            recording ledgerStarted hr hs]
          have hf := ledger_startRound_frame ledger ledgerStarted x.time
            (ReferenceActivePhysicalStep.collectionEnabled ledger x.time)
            (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) hs
          apply collectionFinish_clockAt payload ledger saved started recording
            (ReferenceActivePhysicalStep.receiveUp prepared ledgerStarted) hclock
          intro out hout
          have hu := receiveUp_frame prepared ledgerStarted out hout
          exact ⟨hu.1.trans hf.1, hu.2.1.trans hf.2.1, hu.2.2.trans hf.2.2⟩

/-- The actual `cutoffChosen` outcome initializes the collection frame and
preserves it through the entire same-round tail. The branch's initializer
fields are obtained by eliminating `outcome`, tied to the real preparation by
`hcut`; no good-ledger or local-success law is supplied. The source cutoff is
`x.time.val + 1`, and the original clipped boundary is retained. Other outcome
constructors carry no claim in this disjoint residual. -/
theorem step_clockAt_live_cutoff
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ)
    (outcome : CoordinatorRoundDispatch.LiveOutcome
      (ReferenceActivePhysicalStep.liveInput x r q base))
    (hstate : x.state.coordinator = .live r q base)
    (hclock : ReferenceCoordinatorClockDomains.clockAt x.rows x.selected x.time.val x.state)
    (hcut : (ReferenceActivePhysicalStep.prepare x).coordinator = .live r q base outcome) :
    match outcome with
    | .cutoffChosen _ _ _ _ _ _ _ _ _ _ =>
        ReferenceCoordinatorClockDomains.clockAt x.rows x.selected (x.time.val + 1)
          (ReferenceActivePhysicalStep.step x).next
    | _ => True := by
  classical
  cases outcome
  case cutoffChosen dispatched hstart ledger hinitialization hcandidate hdomains
      hcutoffClock hcutoffPending hnoAssignment selection =>
    have hinv := hclock
    simp only [ReferenceCoordinatorClockDomains.clockAt, hstate] at hinv
    rcases hinv with ⟨_, hvalid, hsigma, _, hgrid, hsigmaTime, hbeforeGrid, _⟩
    have hboundary : r.priorClock.g =
        FollowerCutoffScan.gridBoundary p rate.eta.val r.payload.sigma := by
      simpa only [CoordinatorPhaseClock.boundaryFromSigma, hsigma] using hvalid.1
    have hgridDomain := CoordinatorPhaseClock.clockRegistersValid_gridDomain
      p rate.eta.val r.priorClock hvalid
    have hgridBound : r.priorClock.g ≤ p.T + 1 := by
      have hd : r.payload.sigma.val + 1 < r.priorClock.g ∧ r.priorClock.g ≤ p.T + 1 := by
        simpa only [CoordinatorPhaseClock.clockGridDomain, hsigma] using hgridDomain
      exact hd.2
    have hshared := ReferenceActivePhysicalStep.sharedLedger_fields (rate := rate) ledger
    have hinitial := CoordinatorStartRoundCutoffDispatch.collectionStartLedger_fields
      (ReferenceActivePhysicalStep.liveRegistersAt r x.time)
      (ReferenceActivePhysicalStep.liveOwnedAt r q x.time) base
      (ReferenceActivePhysicalStep.liveRegistersAt r x.time).time
    have hledgerSigma : (ReferenceActivePhysicalStep.sharedLedger (rate := rate) ledger).sigma =
        r.payload.sigma.val + 1 := by
      rw [hshared.2.1, hcandidate]
      exact hinitial.2.1
    have hledgerCutoff : (ReferenceActivePhysicalStep.sharedLedger (rate := rate) ledger).cutoff =
        x.time.val + 1 := by
      rw [hshared.2.2.1, hcandidate]
      exact hinitial.2.2.1
    have hledgerFreeze : (ReferenceActivePhysicalStep.sharedLedger (rate := rate) ledger).freezeAt =
        r.gridBoundary := by
      rw [hshared.2.2.2.1, hcandidate]
      exact hinitial.2.2.2.1
    have hinitialClock : ReferenceCoordinatorClockDomains.clockAt x.rows x.selected
        (x.time.val + 1) { x.state with coordinator :=
          (.collection r.payload (ReferenceActivePhysicalStep.sharedLedger (rate := rate) ledger) none) } := by
      simp only [ReferenceCoordinatorClockDomains.clockAt, hledgerSigma, hledgerCutoff,
        hledgerFreeze]
      refine ⟨True.intro, by omega, by omega, Nat.succ_le_of_lt x.time.isLt, le_rfl,
        hgrid.trans hboundary, by omega, ?_⟩
      simpa only [hgrid] using hgridBound
    have htail := collectionPostChoice_clockAt (ReferenceActivePhysicalStep.prepare x)
      r.payload (ReferenceActivePhysicalStep.sharedLedger (rate := rate) ledger) none dispatched.startResult
      (ReferenceActivePhysicalStep.liveRegistersAt r x.time).complementWeights hinitialClock
    have hobserve := ReferenceActivePhysicalStep.observeCoordinator_live_equation
      (ReferenceActivePhysicalStep.prepare x) r q base
      (.cutoffChosen dispatched hstart ledger hinitialization hcandidate hdomains
        hcutoffClock hcutoffPending hnoAssignment selection) hcut
    have hobs : (ReferenceActivePhysicalStep.prepare x).observeCoordinator =
        ReferenceActivePhysicalStep.collectionPostChoice (ReferenceActivePhysicalStep.prepare x)
          r.payload (ReferenceActivePhysicalStep.sharedLedger (rate := rate) ledger) dispatched.startResult
          (ReferenceActivePhysicalStep.liveRegistersAt r x.time).complementWeights := by
      simpa only [ReferenceActivePhysicalStep.DispatchCut.selection,
        ReferenceActivePhysicalStep.selectionAt, reduceCtorEq, dite_true, ite_false,
        ReferenceActivePhysicalStep.sharedLedger, ReferenceActivePhysicalStep.liveRegistersAt]
        using hobserve
    simpa only [ReferenceActivePhysicalStep.step, hobs, ReferenceCoordinatorClockDomains.clockAt]
      using htail
  all_goals trivial

/-- An actual continuing collection preserves its original sigma, cutoff and
freeze through recording, reception and finishing, even at/past the freeze
boundary. Saved proposal memory is unrestricted. This is one actual step
branch, not a run invariant or a local no-error claim. All checked core fields
are obtained from the actual retained outcome, rather than supplied separately.
Other outcome constructors carry no claim in this disjoint residual. -/
theorem step_clockAt_collection_continuing
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (saved : Option (Fin p.T × Bool))
    (clock : CoordinatorPhaseClock.ClockRegisters p) (cutoff : Fin p.T)
    (outcome : CoordinatorRoundDispatch.CollectionOutcome
      (ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff))
    (hstate : x.state.coordinator = .collection payload ledger saved)
    (hclock : ReferenceCoordinatorClockDomains.clockAt x.rows x.selected x.time.val x.state)
    (hcut : (ReferenceActivePhysicalStep.prepare x).coordinator =
      .collection payload ledger clock cutoff outcome) :
    match outcome with
    | .continuing _ _ _ _ =>
        ReferenceCoordinatorClockDomains.clockAt x.rows x.selected (x.time.val + 1)
          (ReferenceActivePhysicalStep.step x).next
    | _ => True := by
  classical
  cases outcome
  case continuing core snapshot hboundary hscores =>
    have hinv := hclock
    simp only [ReferenceCoordinatorClockDomains.clockAt, hstate] at hinv
    have hnext : ReferenceCoordinatorClockDomains.clockAt x.rows x.selected (x.time.val + 1)
        { x.state with coordinator := .collection payload ledger saved } := by
      change ledger.sigma = payload.sigma.val + 1 ∧
        payload.sigma.val + 1 < ledger.cutoff ∧ 1 ≤ ledger.cutoff ∧
        ledger.cutoff ≤ p.T ∧ ledger.cutoff ≤ x.time.val + 1 ∧
        ledger.freezeAt = FollowerCutoffScan.gridBoundary p rate.eta.val payload.sigma ∧
        ledger.cutoff ≤ ledger.freezeAt ∧ ledger.freezeAt ≤ p.T + 1
      exact ⟨hinv.1, hinv.2.1, hinv.2.2.1, hinv.2.2.2.1,
        Nat.le_trans hinv.2.2.2.2.1 (Nat.le_succ _), hinv.2.2.2.2.2⟩
    have htail := collectionPostChoice_clockAt (ReferenceActivePhysicalStep.prepare x)
      payload ledger saved snapshot.clockStarted
      (CoordinatorCollectionInteractive.PreObservationInputs.weights
        (ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff)
        snapshot.inputsValid.ledger_valid snapshot.inputsValid.assignment_eq) hnext
    have hobserve := ReferenceActivePhysicalStep.observeCoordinator_collection_equation
      (ReferenceActivePhysicalStep.prepare x) payload ledger clock cutoff
      (.continuing core snapshot hboundary hscores) hcut
    by_cases hselection : (ReferenceActivePhysicalStep.DispatchCut.collection
        payload ledger clock cutoff (.continuing core snapshot hboundary hscores)).selection = none
    · rw [ite_eq_left hselection] at hobserve
      simp only [ReferenceActivePhysicalStep.step, hobserve,
        ReferenceActivePhysicalStep.coordinatorFailure, ReferenceCoordinatorClockDomains.clockAt]
    · rw [ite_eq_right hselection] at hobserve
      simpa only [ReferenceActivePhysicalStep.step, hobserve,
        ReferenceCoordinatorClockDomains.clockAt] using htail
  all_goals trivial

end Bandits.Support.ReferenceCollectionClockPreservation

end
