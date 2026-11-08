/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedLiveConfirmationAcceptedDown
public import Bandits.Support.ReferenceFirstReplacementInstalledCredit

/-!
# Retained assignment installation provenance

Sources: `sources/zip4/manuscript/appendix_a_local_protocol.tex:28-64` and
`sources/zip4/manuscript/06_interruptions.tex:255-282,303-348,355-390`.

The coordinator retains the base vector of its actual installation and the
assignment's first cutoff. These are chronological field identities; they
assert no numerical score or queue identity and no manuscript closure.
-/

@[expose] public section
noncomputable section

namespace Bandits.Support.ReferenceAssignmentRetainedBirthProvenance

open ConstructorDimensions ReferenceActivePhysicalStep ReferenceActivePhysicalHorizon
open ReferenceAssignmentPayloadPersistence ReferenceAssignmentPayloadChronology

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

/-- At the next physical decision the finite minimum can be attained only
by the clipped grid or the immediately preceding admissible proposal. -/
private theorem firstCutoff_test
    (sigma t prior : Fin p.T) (bits : Fin p.T → Bool)
    (hstart : sigma.val < t.val) (hprior : prior.val + 1 = t.val)
    (hle : t.val + 1 ≤ FollowerCutoffScan.firstCutoff p rate.eta.val sigma bits) :
    (FollowerCutoffScan.gridBoundary p rate.eta.val sigma = t.val + 1 ∨
      bits prior = true) ↔
      FollowerCutoffScan.firstCutoff p rate.eta.val sigma bits = t.val + 1 := by
  classical
  let carrier := FollowerCutoffScan.firstCutoffCarrier p rate.eta.val sigma bits
  constructor
  · intro h
    have hmem : t.val + 1 ∈ carrier := by
      rcases h with hg | hb
      · exact hg ▸ Finset.mem_insert_self _ _
      · apply Finset.mem_insert_of_mem
        apply Finset.mem_image.mpr
        refine ⟨prior, Finset.mem_filter.mpr ⟨?_, hb⟩, ?_⟩
        · simp only [FollowerCutoffScan.proposalCoordinates, Finset.mem_filter,
            Finset.mem_univ, true_and]
          omega
        · simp only [FollowerCutoffScan.proposalEndpoint]
          omega
    have hm := Finset.min'_le carrier (t.val + 1) hmem
    exact Nat.le_antisymm hm hle
  · intro he
    have hm : FollowerCutoffScan.firstCutoff p rate.eta.val sigma bits ∈ carrier :=
      Finset.min'_mem _ _
    rw [he] at hm
    rcases Finset.mem_insert.mp hm with hg | hb
    · exact Or.inl hg.symm
    · obtain ⟨v, hv, ht⟩ := Finset.mem_image.mp hb
      have hvbit := (Finset.mem_filter.mp hv).2
      have heq : v = prior := by
        apply Fin.ext
        simp only [FollowerCutoffScan.proposalEndpoint] at ht
        omega
      exact Or.inr (heq ▸ hvbit)

/-- The successful source clock distinguishes the first cutoff from a live
continuation, using the saved predecessor bit rather than a terminal token. -/
private theorem startRound_firstCutoff
    (sigma t prior : Fin p.T) (bits : Fin p.T → Bool)
    (clock : CoordinatorPhaseClock.ClockRegisters p)
    (pending : Finset (Fin (p.m - 1)))
    (out : CoordinatorPhaseClock.StartRoundResult p)
    (hsigma : clock.sigma = some sigma) (hu : clock.u = none)
    (hg : clock.g = FollowerCutoffScan.gridBoundary p rate.eta.val sigma)
    (hproposal : clock.lastProposal = some (prior, bits prior))
    (hprior : prior.val + 1 = t.val) (hstart : sigma.val < t.val)
    (hclock : CoordinatorPhaseClock.clockRegistersValid p rate.eta.val clock)
    (htime : CoordinatorPhaseClock.startRoundTimeValid p t clock)
    (hlive : t.val < FollowerCutoffScan.firstCutoff p rate.eta.val sigma bits)
    (hout : CoordinatorPhaseClock.startRound p rate.eta.val t clock pending = .ok out) :
    (out.clock.u = none →
      t.val + 1 < FollowerCutoffScan.firstCutoff p rate.eta.val sigma bits) ∧
    (out.clock.u = some t →
      FollowerCutoffScan.firstCutoff p rate.eta.val sigma bits = t.val + 1) := by
  classical
  have hparam := ReferenceCoordinatorClockDomains.proposalParameterValid_of_rate rate
  have hread := CoordinatorPhaseClock.savedPriorProposal_correct clock t prior
    (bits prior) hproposal hprior
  have htest := firstCutoff_test (rate := rate) sigma t prior bits hstart hprior
    (by omega)
  by_cases hgrid : FollowerCutoffScan.calendarRound t = clock.g
  · have hdecision : CoordinatorPhaseClock.detectCutoff clock t =
        .ok (.cutoff sigma hsigma) := by
      rcases clock with ⟨s, v, g, token⟩
      change s = some sigma at hsigma
      change v = none at hu
      subst s
      subst v
      simp only [CoordinatorPhaseClock.detectCutoff, hgrid, ite_true]
    obtain ⟨result, hresult, hframe, _, _, _⟩ :=
      CoordinatorPhaseClock.startRound_cutoff_effect p rate.eta.val t sigma clock
        pending hparam hclock htime hsigma hdecision
    have heq := Except.ok.inj (hout.symm.trans hresult)
    have hcut : out.clock.u = some t := by rw [heq, hframe]
    have hmin := htest.mp (Or.inl (by
      simpa only [FollowerCutoffScan.calendarRound, hg] using hgrid.symm))
    constructor
    · intro hn
      rw [hn] at hcut
      cases hcut
    · exact fun _ => hmin
  · by_cases hbit : bits prior = true
    · have hdecision : CoordinatorPhaseClock.detectCutoff clock t =
          .ok (.cutoff sigma hsigma) := by
        rcases clock with ⟨s, v, g, token⟩
        change s = some sigma at hsigma
        change v = none at hu
        subst s
        subst v
        simp [CoordinatorPhaseClock.detectCutoff, hgrid, hread, hbit]
        rfl
      obtain ⟨result, hresult, hframe, _, _, _⟩ :=
        CoordinatorPhaseClock.startRound_cutoff_effect p rate.eta.val t sigma clock
          pending hparam hclock htime hsigma hdecision
      have heq := Except.ok.inj (hout.symm.trans hresult)
      have hcut : out.clock.u = some t := by rw [heq, hframe]
      constructor
      · intro hn
        rw [hn] at hcut
        cases hcut
      · exact fun _ => htest.mp (Or.inr hbit)
    · have hfalse : bits prior = false := Bool.eq_false_iff.mpr hbit
      have hdecision : CoordinatorPhaseClock.detectCutoff clock t = .ok .noCutoff := by
        rcases clock with ⟨s, v, g, token⟩
        change s = some sigma at hsigma
        change v = none at hu
        subst s
        subst v
        simp [CoordinatorPhaseClock.detectCutoff, hgrid, hread, hfalse]
        rfl
      have hnoStart := CoordinatorPhaseClock.sourceStartTest_false_without_cutoff
        sigma t pending
      simp only [CoordinatorPhaseClock.startRound, hparam, hclock, htime,
        dite_true, ite_true, hdecision, hsigma, hu, hnoStart, dite_false] at hout
      have hnone : out.clock.u = none := by
        cases hout
        exact hu
      have hne : FollowerCutoffScan.firstCutoff p rate.eta.val sigma bits ≠ t.val + 1 := by
        intro he
        rcases htest.mpr he with hg' | hb
        · exact hgrid (by simpa only [FollowerCutoffScan.calendarRound, hg] using hg'.symm)
        · exact hbit hb
      constructor
      · intro _
        omega
      · intro hc
        rw [hnone] at hc
        cases hc

/-- Stage (1) copies the installed assignment and base, including disabled
service and enabled zero arrivals. -/
private theorem startRound_base_frame (ledger out : Ledger rate) (time : Fin p.T)
    (enabled : Bool) (raw : Option (Fin p.K × ℕ))
    (h : CoordinatorCollectionLedger.startRound ledger (time.val + 1) enabled raw =
      .success out) :
    out.assignment = ledger.assignment ∧ out.baseScore = ledger.baseScore ∧
      out.sigma = ledger.sigma ∧ out.cutoff = ledger.cutoff := by
  rw [CoordinatorCollectionUpRoundStep.InputsValid.startRound_success_candidate
    ledger (time.val + 1) (by omega) (Nat.succ_le_of_lt time.isLt) enabled raw out h]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- An accepted reply changes recovered registers and pending membership;
ordinary rejection changes only the phase. Both retain the installed base. -/
private theorem decodeUp_base_frame (ledger : Ledger rate) (i : Fin (p.m - 1))
    (parsed : Option (OrdinaryMessageCodec.UpRecord
      (CoordinatorCollectionLedger.codecParams p rate.eta.val)))
    (out : Ledger rate)
    (h : CoordinatorCollectionLedger.decodeUp ledger i parsed = .success out ∨
      CoordinatorCollectionLedger.decodeUp ledger i parsed = .rejected out) :
    out.assignment = ledger.assignment ∧ out.baseScore = ledger.baseScore ∧
      out.sigma = ledger.sigma ∧ out.cutoff = ledger.cutoff := by
  classical
  by_cases hd : CoordinatorCollectionLedger.validLedgerCheck ledger = true ∧
      ledger.phase = .started ∧ 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ ledger.cursor ∧
      ledger.cursor ≤ p.T
  · rcases h with hs | hr
    · obtain ⟨M, past, current, _, hout, _, _⟩ :=
        CoordinatorCollectionUpRoundStep.InputsValid.decodeUp_success_candidate
          ledger i parsed out hd hs
      rw [hout]
      exact ⟨rfl, rfl, rfl, rfl⟩
    · unfold CoordinatorCollectionLedger.decodeUp at hr
      rw [dite_eq_left hd] at hr
      cases parsed with
      | none =>
          dsimp only at hr
          split_ifs at hr with hv
          injection hr with hout
          rw [← hout]
          exact ⟨rfl, rfl, rfl, rfl⟩
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
            exact ⟨rfl, rfl, rfl, rfl⟩
  · simp only [CoordinatorCollectionLedger.decodeUp, dite_eq_right hd] at h
    cases h <;> contradiction

private theorem packDecode_base_frame (ledger : Ledger rate) (i : Fin (p.m - 1))
    (parsed : Option (OrdinaryMessageCodec.UpRecord
      (CoordinatorCollectionLedger.codecParams p rate.eta.val)))
    (bank : CoordinatorUpReception.UpDecoderBank p)
    (out : Ledger rate × CoordinatorUpReception.UpDecoderBank p)
    (h : CoordinatorUpReception.packDecodeResult
        (CoordinatorCollectionLedger.decodeUp ledger i parsed) bank = .success out ∨
      CoordinatorUpReception.packDecodeResult
        (CoordinatorCollectionLedger.decodeUp ledger i parsed) bank = .rejected out) :
    out.1.assignment = ledger.assignment ∧ out.1.baseScore = ledger.baseScore ∧
      out.1.sigma = ledger.sigma ∧ out.1.cutoff = ledger.cutoff := by
  cases hd : CoordinatorCollectionLedger.decodeUp ledger i parsed with
  | invalid =>
      simp only [hd, CoordinatorUpReception.packDecodeResult] at h
      cases h <;> contradiction
  | success decoded =>
      simp only [hd, CoordinatorUpReception.packDecodeResult] at h
      have ho : out = (decoded, bank) := by
        rcases h with h | h
        · exact (CoordinatorCollectionLedger.Checked.success.inj h).symm
        · cases h
      rw [ho]
      exact decodeUp_base_frame ledger i parsed decoded (Or.inl hd)
  | rejected decoded =>
      simp only [hd, CoordinatorUpReception.packDecodeResult] at h
      have ho : out = (decoded, bank) := by
        rcases h with h | h
        · cases h
        · exact (CoordinatorCollectionLedger.Checked.rejected.inj h).symm
      rw [ho]
      exact decodeUp_base_frame ledger i parsed decoded (Or.inr hd)

private theorem receiveUp_base_frame {x : RoundInput p rate} (prepared : PreparedRound x)
    (ledger : Ledger rate) (out : Ledger rate × CoordinatorUpReception.UpDecoderBank p)
    (h : (receiveUp prepared ledger).result = .success out ∨
      (receiveUp prepared ledger).result = .rejected out) :
    out.1.assignment = ledger.assignment ∧ out.1.baseScore = ledger.baseScore ∧
      out.1.sigma = ledger.sigma ∧ out.1.cutoff = ledger.cutoff := by
  classical
  unfold receiveUp at h
  dsimp only at h
  unfold ReferenceUpReception.receiveUpFilteredAtRow at h
  dsimp only at h
  split at h
  · exact packDecode_base_frame _ _ _ _ out h
  · cases h <;> contradiction

private theorem collectionFinish_base_frame {x : RoundInput p rate}
    (payload : Payload rate) (started : CoordinatorPhaseClock.StartRoundResult p)
    (recording : CoordinatorRecordingOperation.Output p) (cut : UpCut p rate)
    (ledger : Ledger rate)
    (hcut : ∀ out, cut.result = .success out ∨ cut.result = .rejected out →
      out.1.assignment = ledger.assignment ∧ out.1.baseScore = ledger.baseScore ∧
        out.1.sigma = ledger.sigma ∧ out.1.cutoff = ledger.cutoff) :
    (collectionFinish (x := x) payload started recording cut).configuration = .dagger ∨
      ∃ next saved,
        (collectionFinish (x := x) payload started recording cut).configuration =
          .collection payload next saved ∧
        next.assignment = ledger.assignment ∧ next.baseScore = ledger.baseScore ∧
          next.sigma = ledger.sigma ∧ next.cutoff = ledger.cutoff := by
  unfold collectionFinish
  cases hr : cut.result with
  | invalid => exact Or.inl rfl
  | success pair | rejected pair =>
      have hframe := hcut pair (by simp only [hr]; tauto)
      rcases pair with ⟨decoded, bank⟩
      dsimp only at hframe ⊢
      cases hf : CoordinatorCollectionLedger.finishRound decoded with
      | invalid => exact Or.inl rfl
      | rejected _ => exact Or.inl rfl
      | success finished =>
          dsimp only
          have hc := CoordinatorCollectionUpRoundStep.InputsValid.finishRound_success_candidate
            decoded finished hf
          cases CoordinatorPhaseClock.finishRound p rate.eta.val x.time started.clock
              finished.pending x.row with
          | error _ => exact Or.inl rfl
          | ok result =>
              refine Or.inr ⟨finished, result.clock.lastProposal, rfl, ?_⟩
              simpa only [hc, CoordinatorCollectionLedger.finishRoundCandidate] using hframe

/-- The complete collection tail retains the literal base, assignment, start
and cutoff or enters the actual absorbing state. No successful-tail premise. -/
private theorem collectionPostChoice_base_frame {x : RoundInput p rate}
    (prepared : PreparedRound x) (payload : Payload rate) (ledger : Ledger rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ) :
    (collectionPostChoice prepared payload ledger started weights).configuration = .dagger ∨
      ∃ next saved,
        (collectionPostChoice prepared payload ledger started weights).configuration =
          .collection payload next saved ∧
        next.assignment = ledger.assignment ∧ next.baseScore = ledger.baseScore ∧
          next.sigma = ledger.sigma ∧ next.cutoff = ledger.cutoff := by
  classical
  unfold collectionPostChoice
  cases CoordinatorRecorderComplementBridge.run
      (collectionRecordingInput prepared payload started weights) with
  | none => exact Or.inl rfl
  | some recording =>
      dsimp only
      cases hs : CoordinatorCollectionLedger.startRound ledger (x.time.val + 1)
          (collectionEnabled ledger x.time)
          (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) with
      | invalid => exact Or.inl rfl
      | rejected _ => exact Or.inl rfl
      | success startedLedger =>
          apply collectionFinish_base_frame payload started recording
            (receiveUp prepared startedLedger) ledger
          intro out hout
          have hreceive := receiveUp_base_frame prepared startedLedger out hout
          have hstart := startRound_base_frame ledger startedLedger x.time _ _ hs
          exact ⟨hreceive.1.trans hstart.1, hreceive.2.1.trans hstart.2.1,
            hreceive.2.2.1.trans hstart.2.2.1, hreceive.2.2.2.trans hstart.2.2.2⟩

private theorem finishRound_cutoff_frame
    (clock : CoordinatorPhaseClock.ClockRegisters p) (t : Fin p.T)
    (pending : Finset (Fin (p.m - 1))) (row : CompletePublicTable.CompleteRow p)
    (out : CoordinatorPhaseClock.FinishRoundResult p)
    (h : CoordinatorPhaseClock.finishRound p rate.eta.val t clock pending row = .ok out) :
    out.clock.u = clock.u := by
  simp only [CoordinatorPhaseClock.finishRound] at h
  repeat' split at h
  all_goals
    cases h
    all_goals simp_all

private theorem livePostChoice_base_frame {x : RoundInput p rate}
    (prepared : PreparedRound x)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ) (started : CoordinatorPhaseClock.StartRoundResult p) :
    (livePostChoice prepared r q base started).configuration = .dagger ∨
      ∃ next owned,
        (livePostChoice prepared r q base started).configuration = .live next owned base ∧
        next.payload = r.payload ∧ next.priorClock.u = started.clock.u := by
  unfold livePostChoice
  split
  · exact Or.inl rfl
  · split
    · exact Or.inl rfl
    · split
      · exact Or.inl rfl
      · rename_i recording hrecord serviced hservice pending hpending
        split
        · exact Or.inl rfl
        · rename_i finished hfinish
          exact Or.inr ⟨_, _, rfl, rfl,
            finishRound_cutoff_frame started.clock x.time pending x.row finished hfinish⟩

private theorem no_selection_dagger (x : RoundInput p rate)
    (hnone : (prepare x).coordinator.selection = none) :
    (step x).next.coordinator = .dagger := by
  rw [(step_next_fields x).1]
  unfold PreparedRound.observeCoordinator
  rw [dite_eq_left hnone]
  cases hcut : (prepare x).coordinator <;> rfl

/-- One actual round preserves the original birth and base. The list is a
prefixLength of the same run at its later use; this lemma assumes no numerical mass. -/
private theorem step_retained_birth (x : RoundInput p rate)
    (history : List (RoundRecord (p := p) (rate := rate)))
    (hclock : ReferenceCoordinatorClockDomains.clockAt
      x.rows x.selected x.time.val x.state)
    (hin : match x.state.coordinator with
      | .live r _ beta =>
          (∃ b ∈ history, InstallationBirth b r.payload ∧
            (match b.output.preparation.coordinator with
            | .first (.chosen installed _) => beta = installed.followerBaseScore
            | .collection _ _ _ _ (.laterChosen _ _ _ _ _ _ _ _ _ installed _) =>
                beta = installed.retainedBaseScore
            | _ => False)) ∧
          x.time.val < FollowerCutoffScan.firstCutoff p rate.eta.val r.payload.sigma
            (FollowerCutoffScan.completeRowProposalBit p rate.eta.val x.row)
      | .collection P l _ =>
          (∃ b ∈ history, InstallationBirth b P ∧
            (match b.output.preparation.coordinator with
            | .first (.chosen installed _) => l.baseScore = installed.followerBaseScore
            | .collection _ _ _ _ (.laterChosen _ _ _ _ _ _ _ _ _ installed _) =>
                l.baseScore = installed.retainedBaseScore
            | _ => False)) ∧
          l.assignment.arm = P.assignment.assigned ∧ l.sigma = P.sigma.val + 1 ∧
          l.cutoff = FollowerCutoffScan.firstCutoff p rate.eta.val P.sigma
            (FollowerCutoffScan.completeRowProposalBit p rate.eta.val x.row)
      | .first => True
      | .dagger => True) :
    match (step x).next.coordinator with
    | .live r _ beta =>
        (∃ b ∈ history ++ [actualStepRecord x], InstallationBirth b r.payload ∧
          (match b.output.preparation.coordinator with
          | .first (.chosen installed _) => beta = installed.followerBaseScore
          | .collection _ _ _ _ (.laterChosen _ _ _ _ _ _ _ _ _ installed _) =>
              beta = installed.retainedBaseScore
          | _ => False)) ∧
        x.time.val + 1 < FollowerCutoffScan.firstCutoff p rate.eta.val r.payload.sigma
          (FollowerCutoffScan.completeRowProposalBit p rate.eta.val x.row)
    | .collection P l _ =>
        (∃ b ∈ history ++ [actualStepRecord x], InstallationBirth b P ∧
          (match b.output.preparation.coordinator with
          | .first (.chosen installed _) => l.baseScore = installed.followerBaseScore
          | .collection _ _ _ _ (.laterChosen _ _ _ _ _ _ _ _ _ installed _) =>
              l.baseScore = installed.retainedBaseScore
          | _ => False)) ∧
        l.assignment.arm = P.assignment.assigned ∧ l.sigma = P.sigma.val + 1 ∧
        l.cutoff = FollowerCutoffScan.firstCutoff p rate.eta.val P.sigma
          (FollowerCutoffScan.completeRowProposalBit p rate.eta.val x.row)
    | .first => True
    | .dagger => True := by
  classical
  by_cases hnone : (prepare x).coordinator.selection = none
  · rw [no_selection_dagger x hnone]
    trivial
  have hnextClock := ReferenceRunClockPreservation.step_clockAt x hclock
  cases hstate : x.state.coordinator with
  | first =>
      have hcut_of (outcome : CoordinatorRoundDispatch.FirstOutcome (firstInput x))
          (hd : CoordinatorRoundDispatch.dispatchFirst (firstInput x) = outcome) :
          (prepare x).coordinator = .first outcome := by
        change dispatch x = _
        rw [dispatch_first x hstate, hd]
      cases hd : CoordinatorRoundDispatch.dispatchFirst (firstInput x)
      case chosen installed selected =>
        have hcut : (prepare x).coordinator = .first (.chosen installed selected) := by
          change dispatch x = _
          rw [dispatch_first x hstate, hd]
        have htail : (step x).next.coordinator =
            (livePostChoice (prepare x) installed.registers installed.ownedRegisters
              installed.followerBaseScore installed.startRoundResult).configuration := by
          rw [(step_next_fields x).1]
          unfold PreparedRound.observeCoordinator
          rw [dite_eq_right hnone, hcut]
        rcases livePostChoice_base_frame (prepare x) installed.registers
            installed.ownedRegisters installed.followerBaseScore installed.startRoundResult with
          hdagger | ⟨next, owned, hnext, hpayload, _⟩
        · rw [htail, hdagger]
          trivial
        · rw [htail, hnext]
          have hbtime := firstChosen_payload_time x installed selected hd
          have hb : InstallationBirth (actualStepRecord x) installed.registers.payload := by
            unfold InstallationBirth
            have hrecordCut : (actualStepRecord x).output.preparation.coordinator =
                .first (.chosen installed selected) := hcut
            rw [hrecordCut]
            exact ⟨rfl, hbtime⟩
          constructor
          · refine ⟨actualStepRecord x, List.mem_append_right _ (List.mem_singleton_self _),
              ?_, ?_⟩
            · simpa only [hpayload] using hb
            · have hrecordCut : (actualStepRecord x).output.preparation.coordinator =
                  .first (.chosen installed selected) := hcut
              rw [hrecordCut]
          · rw [hpayload, ← hbtime]
            exact (FollowerCutoffScan.firstCutoff_bounds p rate.eta.val
              rate.eta.property rate.sourceCap _ _).1
      all_goals
        have hcut := hcut_of _ hd
        exact (hnone (by rw [hcut]; rfl)).elim
  | live r q base =>
      have hclock' := hclock
      simp only [ReferenceCoordinatorClockDomains.clockAt, hstate] at hclock'
      rcases hclock' with ⟨hst, hvalid, hsigma, hu, hg, hstarted, hgrid, htoken⟩
      have htime : CoordinatorPhaseClock.startRoundTimeValid p x.time r.priorClock := by
        simp only [CoordinatorPhaseClock.startRoundTimeValid, hsigma, hu,
          FollowerCutoffScan.calendarRound]
        omega
      have hgridEq : r.priorClock.g =
          FollowerCutoffScan.gridBoundary p rate.eta.val r.payload.sigma := by
        simpa only [CoordinatorPhaseClock.boundaryFromSigma, hsigma] using hvalid.1
      simp only [hstate] at hin
      rcases hin with ⟨⟨birth, hmem, hbirth, hbase⟩, hmin⟩
      have hcut_of (outcome : CoordinatorRoundDispatch.LiveOutcome (liveInput x r q base))
          (hd : CoordinatorRoundDispatch.dispatchLive (liveInput x r q base) = outcome) :
          (prepare x).coordinator = .live r q base outcome := by
        simp [prepare, dispatch, hstate, CoordinatorRoundDispatch.dispatch, hd]
        rfl
      cases hd : CoordinatorRoundDispatch.dispatchLive (liveInput x r q base)
      case continuingChosen dispatched hstart continuation selected =>
        have hcut : (prepare x).coordinator =
            .live r q base (.continuingChosen dispatched hstart continuation selected) := by
          simp [prepare, dispatch, hstate, CoordinatorRoundDispatch.dispatch, hd]
          rfl
        have htail : (step x).next.coordinator =
            (livePostChoice (prepare x) (liveRegistersAt r x.time) (liveOwnedAt r q x.time)
              base dispatched.startResult).configuration := by
          rw [(step_next_fields x).1]
          unfold PreparedRound.observeCoordinator
          rw [dite_eq_right hnone, hcut]
        rcases livePostChoice_base_frame (prepare x) (liveRegistersAt r x.time)
            (liveOwnedAt r q x.time) base dispatched.startResult with
          hdagger | ⟨next, owned, hnext, hpayload, hcutoff⟩
        · rw [htail, hdagger]
          trivial
        · have huNext : next.priorClock.u = none := by
            simp only [ReferenceCoordinatorClockDomains.clockAt, htail, hnext] at hnextClock
            exact hnextClock.2.2.2.1
          have hminimum := startRound_firstCutoff r.payload.sigma x.time r.time
            (FollowerCutoffScan.completeRowProposalBit p rate.eta.val x.row)
            r.priorClock (liveRegistersAt r x.time).clockPending dispatched.startResult
            hsigma hu hgridEq htoken hst hstarted hvalid htime hmin hstart
          rw [htail, hnext]
          constructor
          · refine ⟨birth, List.mem_append_left _ hmem, ?_, hbase⟩
            simpa only [hpayload, liveRegistersAt] using hbirth
          · simpa only [hpayload, liveRegistersAt] using
              hminimum.1 (hcutoff.symm.trans huNext)
      case cutoffChosen dispatched hstart ledger hinit hcandidate hdomains hclockCut
          hpending hnoStart selected =>
        have hcut : (prepare x).coordinator = .live r q base
            (.cutoffChosen dispatched hstart ledger hinit hcandidate hdomains hclockCut
              hpending hnoStart selected) := by
          simp [prepare, dispatch, hstate, CoordinatorRoundDispatch.dispatch, hd]
          rfl
        have hminimum := startRound_firstCutoff r.payload.sigma x.time r.time
          (FollowerCutoffScan.completeRowProposalBit p rate.eta.val x.row)
          r.priorClock (liveRegistersAt r x.time).clockPending dispatched.startResult
          hsigma hu hgridEq htoken hst hstarted hvalid htime hmin hstart
        have hcutoff : FollowerCutoffScan.firstCutoff p rate.eta.val r.payload.sigma
            (FollowerCutoffScan.completeRowProposalBit p rate.eta.val x.row) =
              x.time.val + 1 := hminimum.2 (by rw [hclockCut]; rfl)
        have hfields := CoordinatorStartRoundCutoffDispatch.collectionStartLedger_fields
          (liveRegistersAt r x.time) (liveOwnedAt r q x.time) base x.time
        have htail : (step x).next.coordinator =
            (collectionPostChoice (prepare x) r.payload (sharedLedger ledger)
              dispatched.startResult (liveRegistersAt r x.time).complementWeights).configuration := by
          rw [(step_next_fields x).1]
          unfold PreparedRound.observeCoordinator
          rw [dite_eq_right hnone, hcut]
        rcases collectionPostChoice_base_frame (prepare x) r.payload (sharedLedger ledger)
            dispatched.startResult (liveRegistersAt r x.time).complementWeights with
          hdagger | ⟨next, saved, hnext, ha, hb, hs, hc⟩
        · rw [htail, hdagger]
          trivial
        · rw [htail, hnext]
          have hbaseNext : next.baseScore = base := by
            rw [hb, (sharedLedger_fields ledger).2.2.2.2.1, hcandidate]
            exact hfields.2.2.2.2.1
          refine ⟨⟨birth, List.mem_append_left _ hmem, hbirth, ?_⟩, ?_, ?_, ?_⟩
          · simpa only [hbaseNext] using hbase
          · rw [ha, (sharedLedger_fields ledger).1, hcandidate]
            exact hfields.1
          · rw [hs, (sharedLedger_fields ledger).2.1, hcandidate]
            exact hfields.2.1
          · rw [hc, (sharedLedger_fields ledger).2.2.1, hcandidate]
            exact hfields.2.2.1.trans hcutoff.symm
      all_goals
        have hcut := hcut_of _ hd
        exact (hnone (by rw [hcut]; rfl)).elim
  | collection P ledger saved =>
      simp only [hstate] at hin
      by_cases hvalid : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
      · let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
        let clock := collectionClock P ledger saved cutoff
        let source := collectionInput x P ledger clock cutoff
        have hcut_of (outcome : CoordinatorRoundDispatch.CollectionOutcome source)
            (hd : CoordinatorRoundDispatch.dispatchCollection source = outcome) :
            (prepare x).coordinator = .collection P ledger clock cutoff outcome := by
          simp [prepare, dispatch, hstate, hvalid, cutoff, clock, source,
            CoordinatorRoundDispatch.dispatch, hd]
          rfl
        cases hd : CoordinatorRoundDispatch.dispatchCollection source
        case continuing core snapshot boundary hscores =>
          have hcut := hcut_of _ hd
          have htail : (step x).next.coordinator =
              (collectionPostChoice (prepare x) P ledger snapshot.clockStarted
                (CoordinatorCollectionInteractive.PreObservationInputs.weights source
                  snapshot.inputsValid.ledger_valid snapshot.inputsValid.assignment_eq)).configuration := by
            rw [(step_next_fields x).1]
            unfold PreparedRound.observeCoordinator
            rw [dite_eq_right hnone, hcut]
          rcases collectionPostChoice_base_frame (prepare x) P ledger snapshot.clockStarted
              (CoordinatorCollectionInteractive.PreObservationInputs.weights source
                snapshot.inputsValid.ledger_valid snapshot.inputsValid.assignment_eq) with
            hdagger | ⟨next, saved', hnext, ha, hb, hs, hc⟩
          · rw [htail, hdagger]
            trivial
          · rw [htail, hnext]
            obtain ⟨⟨birth, hmem, hbirth, hbase⟩, hassign, hsigma, hcutoff⟩ := hin
            refine ⟨⟨birth, List.mem_append_left _ hmem, hbirth, ?_⟩, ?_, ?_, ?_⟩
            · simpa only [hb] using hbase
            · exact (congrArg CoordinatorCollectionLedger.Assignment.arm ha).trans hassign
            · exact hs.trans hsigma
            · exact hc.trans hcutoff
        case laterChosen core consistent started hstart instruction hinstruction output
            hlocal clockData installed selected =>
          have hcut := hcut_of _ hd
          have hprov := ReferenceLaterInstallationProvenance.dispatch_laterChosen_provenance x
          change dispatch x = _ at hcut
          rw [hcut] at hprov
          have hbtime := hprov.2.2.1
          have htail : (step x).next.coordinator =
              (livePostChoice (prepare x) installed.registers installed.ownedRegisters
                installed.retainedBaseScore started).configuration := by
            rw [(step_next_fields x).1]
            unfold PreparedRound.observeCoordinator
            rw [dite_eq_right hnone, show (prepare x).coordinator = _ from hcut]
          rcases livePostChoice_base_frame (prepare x) installed.registers
              installed.ownedRegisters installed.retainedBaseScore started with
            hdagger | ⟨next, owned, hnext, hpayload, _⟩
          · rw [htail, hdagger]
            trivial
          · rw [htail, hnext]
            have hb := ReferenceLaterInstallationProvenance.record_laterChosen_birth
              (actualStepRecord x)
            have hrecordCut : (actualStepRecord x).output.preparation.coordinator =
                .collection P ledger clock cutoff
                  (.laterChosen core consistent started hstart instruction hinstruction output
                    hlocal clockData installed selected) := hcut
            rw [hrecordCut] at hb
            constructor
            · refine ⟨actualStepRecord x, List.mem_append_right _ (List.mem_singleton_self _),
                ?_, ?_⟩
              · simpa only [hpayload] using hb
              · rw [hrecordCut]
            · rw [hpayload, ← hbtime]
              exact (FollowerCutoffScan.firstCutoff_bounds p rate.eta.val
                rate.eta.property rate.sourceCap _ _).1
        all_goals
          have hcut := hcut_of _ hd
          exact (hnone (by rw [hcut]; simp [DispatchCut.selection])).elim
      · exact (hnone (by simp [prepare, dispatch, hstate, hvalid, DispatchCut.selection])).elim
  | dagger =>
      rw [(step_coordinator_dagger x hstate).1]
      trivial

private theorem run_retained_birth
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : allActiveAtStart initial start) (hfirst : initial.coordinator = .first) :
    let total := run initial rows selected rewards start count hspan hmode
    match total.finalState.coordinator with
    | .live r _ beta =>
        (∃ b ∈ total.records, InstallationBirth b r.payload ∧
          (match b.output.preparation.coordinator with
          | .first (.chosen installed _) => beta = installed.followerBaseScore
          | .collection _ _ _ _ (.laterChosen _ _ _ _ _ _ _ _ _ installed _) =>
              beta = installed.retainedBaseScore
          | _ => False)) ∧
        start + count < FollowerCutoffScan.firstCutoff p rate.eta.val r.payload.sigma
          (FollowerCutoffScan.completeRowProposalBit p rate.eta.val (rows selected))
    | .collection P l _ =>
        (∃ b ∈ total.records, InstallationBirth b P ∧
          (match b.output.preparation.coordinator with
          | .first (.chosen installed _) => l.baseScore = installed.followerBaseScore
          | .collection _ _ _ _ (.laterChosen _ _ _ _ _ _ _ _ _ installed _) =>
              l.baseScore = installed.retainedBaseScore
          | _ => False)) ∧
        l.assignment.arm = P.assignment.assigned ∧ l.sigma = P.sigma.val + 1 ∧
        l.cutoff = FollowerCutoffScan.firstCutoff p rate.eta.val P.sigma
          (FollowerCutoffScan.completeRowProposalBit p rate.eta.val (rows selected))
    | .first => True
    | .dagger => True := by
  dsimp only
  induction count with
  | zero =>
      rw [run_zero_final, hfirst]
      trivial
  | succ count ih =>
      let prior := run initial rows selected rewards start count (by omega) hmode
      let record := actualRunRecordAt initial rows selected rewards start count hspan hmode
      have hseed : ReferenceCoordinatorClockDomains.clockAt rows selected start initial := by
        simp only [ReferenceCoordinatorClockDomains.clockAt, hfirst]
      have hclock := (ReferenceRunClockPreservation.run_clockAt initial rows selected rewards
        start count (by omega) hmode hseed).1
      have hinputClock : ReferenceCoordinatorClockDomains.clockAt
          record.input.rows record.input.selected record.input.time.val record.input.state := by
        exact hclock
      have hinput := ih (by omega)
      have hstep := step_retained_birth record.input prior.records hinputClock hinput
      rw [run_successor_finalState_eq_actualRunRecordAt,
        run_successor_actualRunRecordAt]
      convert hstep using 1 <;> rfl

private theorem run_prefix_mem
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : allActiveAtStart initial start) (prefixLength : ℕ) (hp : prefixLength ≤ count)
    (b : RoundRecord (p := p) (rate := rate))
    (hb : b ∈ (run initial rows selected rewards start prefixLength (by omega) hmode).records) :
    b ∈ (run initial rows selected rewards start count hspan hmode).records := by
  induction count with
  | zero =>
      have he : prefixLength = 0 := by omega
      subst prefixLength
      exact hb
  | succ count ih =>
      by_cases he : prefixLength = count + 1
      · subst prefixLength
        exact hb
      · rw [run_successor_actualRunRecordAt]
        exact List.mem_append_left _ (ih (by omega) (by omega) hb)

private theorem run_record_time
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : allActiveAtStart initial start)
    (k : Fin (run initial rows selected rewards start count hspan hmode).records.length) :
    (run initial rows selected rewards start count hspan hmode).records[k.val].input.time.val =
      start + k.val := by
  have ht := run_time_values initial rows selected rewards start count hspan hmode
  have hindex : k.val < count := by
    simpa only [run_record_count] using k.isLt
  have hget := congrArg (fun times : List ℕ => times[k.val]?) ht
  have hcalendar : (calendar start count)[k.val]? = some (start + k.val) := by
    rw [List.getElem?_eq_getElem (by simpa only [calendar, List.length_range'] using hindex)]
    exact congrArg some (List.getElem_range'_1 _ _)
  rw [hcalendar] at hget
  simp only [List.getElem?_map, List.getElem?_eq_getElem k.isLt, Option.map_some] at hget
  exact Option.some.inj hget

private theorem run_input_retained_birth
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : allActiveAtStart initial start) (hfirst : initial.coordinator = .first)
    (k : Fin (run initial rows selected rewards start count hspan hmode).records.length) :
    let R := (run initial rows selected rewards start count hspan hmode).records
    match R[k.val].input.state.coordinator with
    | .live r _ beta =>
        (∃ b : Fin R.length, b.val < k.val ∧ InstallationBirth R[b.val] r.payload ∧
          (match R[b.val].output.preparation.coordinator with
          | .first (.chosen installed _) => beta = installed.followerBaseScore
          | .collection _ _ _ _ (.laterChosen _ _ _ _ _ _ _ _ _ installed _) =>
              beta = installed.retainedBaseScore
          | _ => False)) ∧
        R[k.val].input.time.val < FollowerCutoffScan.firstCutoff p rate.eta.val r.payload.sigma
          (FollowerCutoffScan.completeRowProposalBit p rate.eta.val (rows selected))
    | .collection P l _ =>
        (∃ b : Fin R.length, b.val < k.val ∧ InstallationBirth R[b.val] P ∧
          (match R[b.val].output.preparation.coordinator with
          | .first (.chosen installed _) => l.baseScore = installed.followerBaseScore
          | .collection _ _ _ _ (.laterChosen _ _ _ _ _ _ _ _ _ installed _) =>
              l.baseScore = installed.retainedBaseScore
          | _ => False)) ∧
        l.assignment.arm = P.assignment.assigned ∧ l.sigma = P.sigma.val + 1 ∧
        l.cutoff = FollowerCutoffScan.firstCutoff p rate.eta.val P.sigma
          (FollowerCutoffScan.completeRowProposalBit p rate.eta.val (rows selected))
    | .first => True
    | .dagger => True := by
  dsimp only
  let R := (run initial rows selected rewards start count hspan hmode).records
  have hkMem : R[k.val] ∈ R := List.getElem_mem k.isLt
  obtain ⟨prefixLength, hp, ht, hs⟩ := ReferenceSelectedPayloadChronology.actualRunRecord_has_prefix
    initial rows selected rewards start count hspan hmode R[k.val] hkMem
  have hretained := run_retained_birth initial rows selected rewards start prefixLength
    (by omega) hmode hfirst
  dsimp only at hretained
  rw [← hs] at hretained
  have hbirthIndex (birth : RoundRecord (p := p) (rate := rate))
      (hmem : birth ∈ (run initial rows selected rewards start prefixLength (by omega) hmode).records) :
      ∃ b : Fin R.length, b.val < k.val ∧ R[b.val] = birth := by
    have hfull := run_prefix_mem initial rows selected rewards start count hspan hmode
      prefixLength (by omega) birth hmem
    obtain ⟨n, hn, he⟩ := List.mem_iff_getElem.mp hfull
    let b : Fin R.length := ⟨n, hn⟩
    have htimeMem : birth.input.time.val ∈ calendar start prefixLength := by
      rw [← run_time_values initial rows selected rewards start prefixLength (by omega) hmode]
      exact List.mem_map.mpr ⟨birth, hmem, rfl⟩
    have hbefore : birth.input.time.val < start + prefixLength := by
      obtain ⟨offset, hoffset, heq⟩ := List.mem_range'.mp htimeMem
      omega
    have hbt := run_record_time initial rows selected rewards start count hspan hmode b
    have hkt := run_record_time initial rows selected rewards start count hspan hmode k
    change R[b.val].input.time.val = start + b.val at hbt
    change R[k.val].input.time.val = start + k.val at hkt
    rw [he] at hbt
    exact ⟨b, by omega, he⟩
  cases hc : R[k.val].input.state.coordinator with
  | first => trivial
  | dagger => trivial
  | live r q base =>
      rw [hc] at hretained
      obtain ⟨⟨birth, hmem, hbirth, hbase⟩, hcutoff⟩ := hretained
      obtain ⟨b, hbk, he⟩ := hbirthIndex birth hmem
      subst birth
      refine ⟨⟨b, hbk, hbirth, ?_⟩, ?_⟩
      · cases hbc : R[b.val].output.preparation.coordinator with
        | first outcome =>
            cases outcome <;> simp only [hbc] at hbase ⊢
            all_goals exact hbase
        | collection P l clock cutoff outcome =>
            cases outcome <;> simp only [hbc] at hbase ⊢
            all_goals exact hbase
        | live r q beta outcome => simp only [hbc] at hbase
        | invalidCollectionCutoff => simp only [hbc] at hbase
        | dagger => simp only [hbc] at hbase
      · change R[k.val].input.time.val < _
        rw [ht]
        exact hcutoff
  | collection P ledger saved =>
      rw [hc] at hretained
      obtain ⟨⟨birth, hmem, hbirth, hbase⟩, ha, hsigma, hcutoff⟩ := hretained
      obtain ⟨b, hbk, he⟩ := hbirthIndex birth hmem
      subst birth
      refine ⟨⟨b, hbk, hbirth, ?_⟩, ha, hsigma, hcutoff⟩
      cases hbc : R[b.val].output.preparation.coordinator with
      | first outcome =>
          cases outcome <;> simp only [hbc] at hbase ⊢
          all_goals exact hbase
      | collection P l clock cutoff outcome =>
          cases outcome <;> simp only [hbc] at hbase ⊢
          all_goals exact hbase
      | live r q beta outcome => simp only [hbc] at hbase
      | invalidCollectionCutoff => simp only [hbc] at hbase
      | dagger => simp only [hbc] at hbase

/-- Every retained coordinator assignment carries the base of its actual
earlier installation, and its cutoff is the first source cutoff of that same
payload on the original selected complete row. -/
theorem complete_coordinator_retained_birth
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length) :
    let R : List (RoundRecord (p := p) (rate := rate)) :=
      ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
    let J : Fin (M p) := ActualInitializationPhysicalStep.selectedRowIndex p source
    let bits : Fin p.T → Bool :=
      FollowerCutoffScan.completeRowProposalBit p rate.eta.val (source.1.2 J)
    match (R[k.val]'k.isLt).input.state.coordinator with
    | .live r _ beta =>
        (∃ b : Fin R.length, b.val < k.val ∧ InstallationBirth (R[b.val]'b.isLt) r.payload ∧
          (match (R[b.val]'b.isLt).output.preparation.coordinator with
          | .first (.chosen installed _) => beta = installed.followerBaseScore
          | .collection _ _ _ _ (.laterChosen _ _ _ _ _ _ _ _ _ installed _) =>
              beta = installed.retainedBaseScore
          | _ => False)) ∧
        (R[k.val]'k.isLt).input.time.val < FollowerCutoffScan.firstCutoff p rate.eta.val r.payload.sigma bits
    | .collection P l _ =>
        (∃ b : Fin R.length, b.val < k.val ∧ InstallationBirth (R[b.val]'b.isLt) P ∧
          (match (R[b.val]'b.isLt).output.preparation.coordinator with
          | .first (.chosen installed _) => l.baseScore = installed.followerBaseScore
          | .collection _ _ _ _ (.laterChosen _ _ _ _ _ _ _ _ _ installed _) =>
              l.baseScore = installed.retainedBaseScore
          | _ => False)) ∧
        l.assignment.arm = P.assignment.assigned ∧ l.sigma = P.sigma.val + 1 ∧
        l.cutoff = FollowerCutoffScan.firstCutoff p rate.eta.val P.sigma bits
    | .first => True
    | .dagger => True := by
  classical
  cases hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h with
  | none =>
      have hlength := k.isLt
      simp only [ReferenceCompletePhysicalHistory.completeSuffixRecords, hlaunch,
        dite_true, List.length_nil] at hlength
      omega
  | some active =>
      have hc := (ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
        rate source rewards C_star C_h).1 (by rw [hlaunch]; rfl)
      let initial := ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hc
      have hcanonical := ReferenceFirstLaunchNumericalCell.correctedLaunch_eq_some_launchState
        rate source rewards C_star C_h hc
      let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
        rate source rewards C_star C_h hc
      have hrecords := ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
        rate source rewards C_star C_h initial hcanonical
      dsimp only
      generalize hR : ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h = R at k ⊢
      rw [hR] at hrecords
      subst R
      have hresult := run_input_retained_birth initial source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards _ _ _ _
        seed.coordinatorFirst k
      dsimp only at hresult
      split at hresult
      next r q beta hcoord =>
        simp only [hcoord]
        obtain ⟨⟨b, hbk, hbirth, hbase⟩, hcutoff⟩ := hresult
        refine ⟨⟨b, hbk, hbirth, ?_⟩, hcutoff⟩
        split at hbase <;> simp_all only
        all_goals rfl
      next P l saved hcoord =>
        simp only [hcoord]
        obtain ⟨⟨b, hbk, hbirth, hbase⟩, ha, hsigma, hcutoff⟩ := hresult
        refine ⟨⟨b, hbk, hbirth, ?_⟩, ha, hsigma, hcutoff⟩
        split at hbase <;> simp_all only
        all_goals rfl
      all_goals simp_all only

private theorem complete_input_clock
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length) :
    let x := ((ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[k.val]'k.isLt).input
    ReferenceCoordinatorClockDomains.clockAt x.rows x.selected x.time.val x.state ∧
      x.rows = source.1.2 ∧
      x.selected = ActualInitializationPhysicalStep.selectedRowIndex p source := by
  classical
  cases hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h with
  | none =>
      have hlength := k.isLt
      simp only [ReferenceCompletePhysicalHistory.completeSuffixRecords, hlaunch,
        dite_true, List.length_nil] at hlength
      omega
  | some active =>
      have hc := (ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
        rate source rewards C_star C_h).1 (by rw [hlaunch]; rfl)
      let initial := ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hc
      have hcanonical := ReferenceFirstLaunchNumericalCell.correctedLaunch_eq_some_launchState
        rate source rewards C_star C_h hc
      let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
        rate source rewards C_star C_h hc
      have hrecords := ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
        rate source rewards C_star C_h initial hcanonical
      dsimp only
      generalize hR : ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h = R at k ⊢
      rw [hR] at hrecords
      subst R
      have hseed : ReferenceCoordinatorClockDomains.clockAt source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source)
          (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
          initial := by
        have hfirst : initial.coordinator = .first := seed.coordinatorFirst
        simp only [ReferenceCoordinatorClockDomains.clockAt, hfirst]
      have hclock := ReferenceRunClockPreservation.run_clockAt initial source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
        (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
        (p.T - ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
        (by have hs := ReferenceCompletePhysicalHistory.physicalStart_le_T
              rate source rewards C_star C_h; omega)
        (ReferenceCompletePhysicalHistory.activeMode_of_launch_eq_some
          rate source rewards C_star C_h initial hcanonical) hseed
      have hrecord := hclock.2.2.2 _ (List.getElem_mem k.isLt)
      refine ⟨?_, hrecord.2.2.1, hrecord.2.2.2.1⟩
      rw [hrecord.2.2.1, hrecord.2.2.2.1]
      exact hrecord.1

/-- Both the first cutoff choice and a continuing collection choice inherit
the very same earlier installation and literal base, before any UP or follower
observation tail is required to complete. -/
theorem complete_collection_choice_birth_provenance
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (c : ReferenceCollectionSegmentExtraction.Choice rate)
    (hchoice : ReferenceCollectionSegmentExtraction.choice
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val].input = some c) :
    let R : List (RoundRecord (p := p) (rate := rate)) :=
      ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
    let J : Fin (M p) := ActualInitializationPhysicalStep.selectedRowIndex p source
    let bits : Fin p.T → Bool :=
      FollowerCutoffScan.completeRowProposalBit p rate.eta.val (source.1.2 J)
    ∃ b : Fin R.length, b.val < k.val ∧ InstallationBirth (R[b.val]'b.isLt) c.payload ∧
      c.preLedger.assignment.arm = c.payload.assignment.assigned ∧
      c.preLedger.sigma = c.payload.sigma.val + 1 ∧
      c.preLedger.cutoff = FollowerCutoffScan.firstCutoff p rate.eta.val c.payload.sigma bits ∧
      (match (R[b.val]'b.isLt).output.preparation.coordinator with
      | .first (.chosen installed _) => c.preLedger.baseScore = installed.followerBaseScore
      | .collection _ _ _ _ (.laterChosen _ _ _ _ _ _ _ _ _ installed _) =>
          c.preLedger.baseScore = installed.retainedBaseScore
      | _ => False) := by
  classical
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
  let x := R[k.val].input
  have hretained := complete_coordinator_retained_birth rate rewards C_star C_h source k
  have hdata := complete_input_clock rate rewards C_star C_h source k
  dsimp only at hretained hdata ⊢
  change ReferenceCollectionSegmentExtraction.choice x = some c at hchoice
  obtain ⟨hclock, hrows, hselected⟩ := hdata
  have hrow : x.row = source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) := by
    exact congrArg₂ (fun rows selected => rows selected) hrows hselected
  unfold ReferenceCollectionSegmentExtraction.choice at hchoice
  split at hchoice
  · contradiction
  next hnone =>
    cases hstate : x.state.coordinator with
    | first =>
        have hcut_of (outcome : CoordinatorRoundDispatch.FirstOutcome (firstInput x))
            (hd : CoordinatorRoundDispatch.dispatchFirst (firstInput x) = outcome) :
            (prepare x).coordinator = .first outcome := by
          change dispatch x = _
          rw [dispatch_first x hstate, hd]
        cases hd : CoordinatorRoundDispatch.dispatchFirst (firstInput x)
        all_goals
          have hcut := hcut_of _ hd
          simp only [hcut, ReferenceCollectionSegmentExtraction.choiceOfCut] at hchoice
          contradiction
    | live r q base =>
        have hcut_of (outcome : CoordinatorRoundDispatch.LiveOutcome (liveInput x r q base))
            (hd : CoordinatorRoundDispatch.dispatchLive (liveInput x r q base) = outcome) :
            (prepare x).coordinator = .live r q base outcome := by
          simp [prepare, dispatch, hstate, CoordinatorRoundDispatch.dispatch, hd]
          rfl
        cases hd : CoordinatorRoundDispatch.dispatchLive (liveInput x r q base)
        case cutoffChosen dispatched hstart ledger hinit hcandidate hdomains hclockCut
            hpending hnoStart selected =>
          have hcut := hcut_of _ hd
          simp only [hcut, ReferenceCollectionSegmentExtraction.choiceOfCut] at hchoice
          cases Option.some.inj hchoice
          rw [hstate] at hretained
          obtain ⟨⟨b, hbk, hbirth, hbase⟩, hlive⟩ := hretained
          change ReferenceCoordinatorClockDomains.clockAt x.rows x.selected x.time.val x.state at hclock
          simp only [ReferenceCoordinatorClockDomains.clockAt, hstate] at hclock
          rcases hclock with ⟨hst, hvalid, hsigma, hu, hg, hstarted, hgrid, htoken⟩
          have htime : CoordinatorPhaseClock.startRoundTimeValid p x.time r.priorClock := by
            simp only [CoordinatorPhaseClock.startRoundTimeValid, hsigma, hu,
              FollowerCutoffScan.calendarRound]
            omega
          have hgridEq : r.priorClock.g =
              FollowerCutoffScan.gridBoundary p rate.eta.val r.payload.sigma := by
            simpa only [CoordinatorPhaseClock.boundaryFromSigma, hsigma] using hvalid.1
          have hminimum := startRound_firstCutoff r.payload.sigma x.time r.time
            (FollowerCutoffScan.completeRowProposalBit p rate.eta.val x.row)
            r.priorClock (liveRegistersAt r x.time).clockPending dispatched.startResult
            hsigma hu hgridEq htoken hst hstarted hvalid htime (by simpa only [hrow] using hlive)
            hstart
          have hcutoff := hminimum.2 (by rw [hclockCut]; rfl)
          rw [hrow] at hcutoff
          have hfields := CoordinatorStartRoundCutoffDispatch.collectionStartLedger_fields
            (liveRegistersAt r x.time) (liveOwnedAt r q x.time) base x.time
          refine ⟨b, hbk, hbirth, ?_, ?_, ?_, ?_⟩
          · rw [(sharedLedger_fields ledger).1, hcandidate]
            exact hfields.1
          · rw [(sharedLedger_fields ledger).2.1, hcandidate]
            exact hfields.2.1
          · rw [(sharedLedger_fields ledger).2.2.1, hcandidate]
            exact hfields.2.2.1.trans hcutoff.symm
          · have hb : (sharedLedger ledger).baseScore = base := by
              rw [(sharedLedger_fields ledger).2.2.2.2.1, hcandidate]
              exact hfields.2.2.2.2.1
            simpa only [hb] using hbase
        all_goals
          have hcut := hcut_of _ hd
          simp only [hcut, ReferenceCollectionSegmentExtraction.choiceOfCut] at hchoice
          contradiction
    | collection P ledger saved =>
        by_cases hvalid : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
        · let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
          let clock := collectionClock P ledger saved cutoff
          let sourceInput := collectionInput x P ledger clock cutoff
          have hcut_of (outcome : CoordinatorRoundDispatch.CollectionOutcome sourceInput)
              (hd : CoordinatorRoundDispatch.dispatchCollection sourceInput = outcome) :
              (prepare x).coordinator = .collection P ledger clock cutoff outcome := by
            simp [prepare, dispatch, hstate, hvalid, cutoff, clock, sourceInput,
              CoordinatorRoundDispatch.dispatch, hd]
            rfl
          cases hd : CoordinatorRoundDispatch.dispatchCollection sourceInput
          case continuing core snapshot boundary hscores =>
            have hcut := hcut_of _ hd
            simp only [hcut, ReferenceCollectionSegmentExtraction.choiceOfCut] at hchoice
            cases Option.some.inj hchoice
            rw [hstate] at hretained
            obtain ⟨⟨b, hbk, hbirth, hbase⟩, ha, hsigma, hcutoff⟩ := hretained
            exact ⟨b, hbk, hbirth, ha, hsigma, hcutoff, hbase⟩
          all_goals
            have hcut := hcut_of _ hd
            simp only [hcut, ReferenceCollectionSegmentExtraction.choiceOfCut] at hchoice
            contradiction
        · have hcut : (prepare x).coordinator = .invalidCollectionCutoff :=
            (dispatch_collection_invalid_cutoff x P ledger saved hstate hvalid).1
          simp only [hcut, ReferenceCollectionSegmentExtraction.choiceOfCut] at hchoice
          contradiction
    | dagger =>
        have hcut : (prepare x).coordinator = .dagger := dispatch_dagger x hstate
        simp only [hcut, ReferenceCollectionSegmentExtraction.choiceOfCut] at hchoice
        contradiction

end Bandits.Support.ReferenceAssignmentRetainedBirthProvenance
