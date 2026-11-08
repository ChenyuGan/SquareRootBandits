/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCompleteCoordinatorMass

import Lean.Elab.Tactic.Omega

/-!
# Actual live complement score growth from an installation

The score origin is the actual installation retained by the physical source
run. First installations start at zero; later installations use the score
reconstruction from their actual accepted start operation.

Sources: `sources/zip4/manuscript/04_slow_fast_learner.tex:157-188,245-290`,
`sources/zip4/manuscript/06_interruptions.tex:9-100,246-349,355-390`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:8-64`.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ReferenceCompleteLiveComplementScoreSpan

open ConstructorDimensions
open ReferenceActivePhysicalStep
open ReferenceActivePhysicalHorizon
open ReferenceCompletePhysicalHistory
open ReferenceAssignmentPayloadPersistence
open ReferenceAssignmentPayloadChronology
open CoordinatorLiveServiceFinish
open CoordinatorAssignmentRegisterInstall
open CoordinatorRoundDispatch

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

/-- Exact whole-vector score semantics for either actual installation branch.
The first constructor reads the source's zero vector; a later constructor
reads the source score reconstruction on every arm and identifies its owned
complement entries with the installed registers. Other dispatcher branches
are outside the carrier of an installation. -/
def installationScoreVector
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (payload : Payload rate) (z : Fin p.K → ℕ) : Prop :=
  match record.output.preparation.coordinator with
  | .first (.chosen installed _) =>
      payload = installed.registers.payload ∧ z = (fun _ => 0) ∧
        ∀ j : CanonicalFastSampling.FastArm installed.registers.payload.slowSet,
          installed.registers.complementScores j = z j.1
  | .collection _ _ _ _ (.laterChosen _ _ _ _ _ _ output _ _clockData installed _) =>
      payload = installed.registers.payload ∧
        z = (fun a => AssignmentScoreReconstruction.sourceScore output.reconstruction a) ∧
        ∀ j : CanonicalFastSampling.FastArm installed.registers.payload.slowSet,
          installed.registers.complementScores j = z j.1
  | _ => False

private def liveScoreSpanAt
    (priorRecords : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (endpoint : ℕ) (configuration : ReferenceActivePhysicalStep.CoordinatorConfiguration p rate) : Prop :=
  match configuration with
  | .live registers _ _ =>
      ∃ birth, birth ∈ priorRecords ∧ InstallationBirth birth registers.payload ∧
        ∃ z : Fin p.K → ℕ,
          installationScoreVector birth registers.payload z ∧
          birth.input.time.val + 1 = registers.payload.sigma.val + 1 ∧
          registers.payload.sigma.val ≤ endpoint ∧
          ∀ j : CanonicalFastSampling.FastArm registers.payload.slowSet,
            z j.1 ≤ registers.complementScores j ∧
              registers.complementScores j ≤
                z j.1 + (4 * rate.n) *
                  (endpoint + 1 - (registers.payload.sigma.val + 1))
  | _ => True

private theorem payload_n_eq_rate_n (payload : Payload rate) : payload.n = rate.n := by
  apply Nat.cast_injective (R := ℝ)
  rw [payload.n_eq_eta_mul_D, rate.n_scale]

/-- Every successful actual live post-choice tail adds only its literal capped
service to each complement score. The resulting live configuration is the
only condition; recorder, service, confirmation, and clock success are
recovered from that literal operation. -/
theorem livePostChoice_score_bounds
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (next : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (nextQueues : CoordinatorLiveServiceFinish.OwnedRegisters next)
    (nextBase : Fin (p.m - 1) → ℕ)
    (hnext : (ReferenceActivePhysicalStep.livePostChoice prepared r q base started).configuration =
      .live next nextQueues nextBase) :
    ∃ hp : next.payload = r.payload,
      ∃ serviced : CoordinatorLiveServiceFinish.ServicedRegisters r q,
        (∀ j : CanonicalFastSampling.FastArm r.payload.slowSet,
          r.complementScores j ≤ serviced.score j ∧
            serviced.score j ≤ r.complementScores j + 4 * rate.n) ∧
        ∀ j : CanonicalFastSampling.FastArm r.payload.slowSet,
          next.complementScores (hp.symm ▸ j) = serviced.score j := by
  unfold ReferenceActivePhysicalStep.livePostChoice at hnext
  cases hrecord : CoordinatorRecorderComplementBridge.run
      (ReferenceActivePhysicalStep.liveRecordingInput prepared r started) with
  | none => simp [hrecord, ReferenceActivePhysicalStep.coordinatorFailure] at hnext
  | some recording =>
      cases hservice : CoordinatorLiveServiceFinish.servicePass r q recording with
      | error reason =>
          simp [hrecord, hservice, ReferenceActivePhysicalStep.coordinatorFailure] at hnext
      | ok serviced =>
          cases hconfirmation : CoordinatorLocalArmChoice.confirmationUpdate r.payload
              started.pending
              (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
              x.time x.row prepared.coordinatorObservation with
          | none =>
              simp [hrecord, hservice, hconfirmation,
                ReferenceActivePhysicalStep.coordinatorFailure] at hnext
          | some pending =>
              cases hfinish : CoordinatorPhaseClock.finishRound p rate.eta.val x.time
                  started.clock pending x.row with
              | error reason =>
                  simp [hrecord, hservice, hconfirmation, hfinish,
                    ReferenceActivePhysicalStep.coordinatorFailure] at hnext
              | ok finished =>
                  simp only [hrecord, hservice, hconfirmation, hfinish] at hnext
                  have hregs : next =
                      { payload := r.payload
                        priorClock := finished.clock
                        pendingAtChoice := finished.pending
                        time := x.time
                        gridBoundary := finished.clock.g
                        complementScores := serviced.score } := by
                    cases hnext
                    rfl
                  cases hregs
                  refine ⟨rfl, serviced, ?_, ?_⟩
                  intro j
                  rw [serviced.score_eq j]
                  have hserviceCap : serviced.service j ≤ 4 * rate.n := by
                    have hcap := CappedService.service_le_capacity
                      (4 * r.payload.n) (q.queue j) (serviced.arrival j)
                    have heq : serviced.service j =
                        CappedService.service (4 * r.payload.n) (q.queue j)
                          (serviced.arrival j) := serviced.service_eq j
                    have hcap' : serviced.service j ≤ 4 * r.payload.n := by
                      rw [heq]
                      exact hcap
                    simpa only [payload_n_eq_rate_n r.payload] using hcap'
                  · exact ⟨by omega, by omega⟩
                  · intro j
                    rfl

/-- One successful live post-choice service extends the actual installation's
whole-vector source witness by that round's capped service. This is the local
step used by the source-prefix induction; callers must produce both the
installation witness and its score equations from the actual constructor. -/
theorem installed_live_post_choice_score_span
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (next : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (nextQueues : CoordinatorLiveServiceFinish.OwnedRegisters next)
    (nextBase : Fin (p.m - 1) → ℕ)
    (z : Fin p.K → ℕ)
    (hsource : InstallationBirth record r.payload ∧
      installationScoreVector record r.payload z ∧
      r.payload.sigma.val = record.input.time.val)
    (hseed : ∀ j : CanonicalFastSampling.FastArm r.payload.slowSet,
      r.complementScores j = z j.1)
    (hpost : (ReferenceActivePhysicalStep.livePostChoice record.output.preparation
      r q base started).configuration = .live next nextQueues nextBase) :
    ∃ hp : next.payload = r.payload,
      InstallationBirth record r.payload ∧
      installationScoreVector record r.payload z ∧
      r.payload.sigma.val = record.input.time.val ∧
      ∀ j : CanonicalFastSampling.FastArm r.payload.slowSet,
        z j.1 ≤ next.complementScores (hp.symm ▸ j) ∧
          next.complementScores (hp.symm ▸ j) ≤ z j.1 + 4 * rate.n := by
  obtain ⟨hp, serviced, hservice, hscores⟩ :=
    livePostChoice_score_bounds record.input record.output.preparation r q base started
      next nextQueues nextBase hpost
  refine ⟨hp, hsource.1, hsource.2.1, hsource.2.2, ?_⟩
  intro j
  constructor
  · calc
      z j.1 = r.complementScores j := (hseed j).symm
      _ ≤ serviced.score j := (hservice j).1
      _ = next.complementScores (hp.symm ▸ j) := (hscores j).symm
  · calc
      next.complementScores (hp.symm ▸ j) = serviced.score j := hscores j
      _ ≤ r.complementScores j + 4 * rate.n := (hservice j).2
      _ = z j.1 + 4 * rate.n := by rw [hseed j]

private theorem collectionPostChoice_not_live
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (payload : Payload rate) (ledger : Ledger rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ)
    (h : (ReferenceActivePhysicalStep.collectionPostChoice prepared payload ledger
      started weights).configuration = .live r q base) : False := by
  unfold ReferenceActivePhysicalStep.collectionPostChoice at h
  cases hrecord : CoordinatorRecorderComplementBridge.run
      (ReferenceActivePhysicalStep.collectionRecordingInput prepared payload started weights) with
  | none => simp [hrecord, ReferenceActivePhysicalStep.coordinatorFailure] at h
  | some recording =>
      cases hstart : CoordinatorCollectionLedger.startRound ledger (x.time.val + 1)
          (ReferenceActivePhysicalStep.collectionEnabled ledger x.time)
          (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) with
      | invalid => simp [hrecord, hstart, ReferenceActivePhysicalStep.coordinatorFailure] at h
      | rejected bad => simp [hrecord, hstart, ReferenceActivePhysicalStep.coordinatorFailure] at h
      | success startedLedger =>
          unfold ReferenceActivePhysicalStep.collectionFinish at h
          cases hreceive : (ReferenceActivePhysicalStep.receiveUp prepared startedLedger).result with
          | invalid => simp [hrecord, hstart, hreceive,
              ReferenceActivePhysicalStep.coordinatorFailure] at h
          | success pair | rejected pair =>
              rcases pair with ⟨decoded, bank⟩
              cases hfinish : CoordinatorCollectionLedger.finishRound decoded with
              | invalid => simp [hrecord, hstart, hreceive, hfinish,
                  ReferenceActivePhysicalStep.coordinatorFailure] at h
              | rejected bad => simp [hrecord, hstart, hreceive, hfinish,
                  ReferenceActivePhysicalStep.coordinatorFailure] at h
              | success finished =>
                  cases hclock : CoordinatorPhaseClock.finishRound p rate.eta.val x.time
                      started.clock finished.pending x.row with
                  | error reason =>
                      simp [hrecord, hstart, hreceive, hfinish, hclock,
                        ReferenceActivePhysicalStep.coordinatorFailure] at h
                  | ok clockFinished =>
                      simp [hrecord, hstart, hreceive, hfinish, hclock] at h

/-- The actual chosen first-installation branch is a birth at the current
physical round and installs its literal zero complement-score vector. -/
theorem first_installation_source
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (installed : CoordinatorAssignmentRegisterInstall.FirstInstallation
      (CoordinatorRoundDispatch.firstLaunchInput
        (ReferenceActivePhysicalStep.firstInput record.input)))
    (selected : CoordinatorRoundDispatch.ArmSelection installed.registers.payload
      installed.startRoundResult installed.registers.time
      installed.registers.complementWeights record.input.row)
    (hbranch : record.output.preparation.coordinator = .first (.chosen installed selected)) :
    InstallationBirth record installed.registers.payload ∧
      installationScoreVector record installed.registers.payload (fun _ => 0) ∧
      installed.registers.payload.sigma.val = record.input.time.val := by
  have hactual : record.output.preparation.coordinator =
      ReferenceActivePhysicalStep.dispatch record.input := by
    rw [record.output_eq]
    rfl
  have hdispatch : ReferenceActivePhysicalStep.dispatch record.input =
      .first (.chosen installed selected) := hactual.symm.trans hbranch
  have hstate : record.input.state.coordinator = .first := by
    cases hs : record.input.state.coordinator with
    | first => rfl
    | live r q base =>
        simp only [ReferenceActivePhysicalStep.dispatch, hs] at hdispatch
        cases hround : CoordinatorRoundDispatch.dispatch
            (.live (ReferenceActivePhysicalStep.liveInput record.input r q base));
          simp [hround] at hdispatch
        all_goals cases hdispatch
    | collection payload ledger saved =>
        by_cases hc : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
        · let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
          let clock := ReferenceActivePhysicalStep.collectionClock payload ledger saved cutoff
          cases hround : CoordinatorRoundDispatch.dispatch
              (.collection (ReferenceActivePhysicalStep.collectionInput
                record.input payload ledger clock cutoff));
            simp [ReferenceActivePhysicalStep.dispatch, hs, hc, cutoff, clock, hround] at hdispatch
          all_goals cases hdispatch
        · simp [ReferenceActivePhysicalStep.dispatch, hs, hc] at hdispatch
    | dagger => simp [ReferenceActivePhysicalStep.dispatch, hs] at hdispatch
  have hcut := ReferenceActivePhysicalStep.dispatch_first record.input hstate
  rw [hcut] at hdispatch
  have hchosen : CoordinatorRoundDispatch.dispatchFirst
      (ReferenceActivePhysicalStep.firstInput record.input) = .chosen installed selected := by
    injection hdispatch with hchosen
  have hseed := ReferenceActivePhysicalStep.dispatchFirst_zero_seed
    record.input installed selected hchosen
  have htime := ReferenceAssignmentPayloadPersistence.firstChosen_payload_time
    record.input installed selected hchosen
  refine ⟨?_, ?_, htime⟩
  · unfold ReferenceAssignmentPayloadPersistence.InstallationBirth
    rw [hbranch]
    exact ⟨rfl, htime⟩
  · simp only [installationScoreVector, hbranch]
    constructor
    · rfl
    constructor
    · trivial
    · exact hseed.1

/-- After the actual first installation's successful live post-choice tail,
the installed zero vector has grown by at most this round's capped service. -/
theorem first_live_post_choice_score_le
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (installed : CoordinatorAssignmentRegisterInstall.FirstInstallation
      (CoordinatorRoundDispatch.firstLaunchInput
        (ReferenceActivePhysicalStep.firstInput record.input)))
    (selected : CoordinatorRoundDispatch.ArmSelection installed.registers.payload
      installed.startRoundResult installed.registers.time
      installed.registers.complementWeights record.input.row)
    (next : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (nextQueues : CoordinatorLiveServiceFinish.OwnedRegisters next)
    (nextBase : Fin (p.m - 1) → ℕ)
    (hbranch : record.output.preparation.coordinator = .first (.chosen installed selected))
    (hpost : (ReferenceActivePhysicalStep.livePostChoice record.output.preparation
      installed.registers installed.ownedRegisters installed.followerBaseScore
      installed.startRoundResult).configuration = .live next nextQueues nextBase) :
    ∃ hp : next.payload = installed.registers.payload,
      ∀ j : CanonicalFastSampling.FastArm installed.registers.payload.slowSet,
        0 ≤ next.complementScores (hp.symm ▸ j) ∧
          next.complementScores (hp.symm ▸ j) ≤ 4 * rate.n := by
  obtain ⟨hp, serviced, hservice, hscores⟩ :=
    livePostChoice_score_bounds record.input record.output.preparation installed.registers
      installed.ownedRegisters installed.followerBaseScore installed.startRoundResult
      next nextQueues nextBase hpost
  have hsource := first_installation_source record installed selected hbranch
  have hzero : ∀ j : CanonicalFastSampling.FastArm installed.registers.payload.slowSet,
      installed.registers.complementScores j = 0 := by
    intro j
    have hv := hsource.2.1
    simp only [installationScoreVector, hbranch] at hv
    exact hv.2.2 j
  refine ⟨hp, ?_⟩
  intro j
  constructor
  · exact Nat.zero_le _
  · calc
      next.complementScores (hp.symm ▸ j) = serviced.score j := hscores j
      _ ≤ installed.registers.complementScores j + 4 * rate.n := (hservice j).2
      _ = 4 * rate.n := by rw [hzero j]; simp

/-- A real chosen later-installation branch is a birth at this round and its
whole installed complement vector is the source-score reconstruction attached
to that accepted start. -/
theorem later_installation_source
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (payload : Payload rate) (ledger : Ledger rate)
    (clock : CoordinatorPhaseClock.ClockRegisters p) (cutoff : Fin p.T)
    (core : CoordinatorRoundDispatch.CollectionCoreValid
      (ReferenceActivePhysicalStep.collectionInput record.input payload ledger clock cutoff))
    (consistent : LaterAssignmentStartOperation.LocalConsistency
      (ReferenceActivePhysicalStep.collectionInput record.input payload ledger clock cutoff).payload
      (CoordinatorRoundDispatch.collectionOperationLedger
        (ReferenceActivePhysicalStep.collectionInput record.input payload ledger clock cutoff)
        core.payload_n_eq))
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (hstart : CoordinatorPhaseClock.startRound p
      (ReferenceActivePhysicalStep.collectionInput record.input payload ledger clock cutoff).etaReal
      (ReferenceActivePhysicalStep.collectionInput record.input payload ledger clock cutoff).time
      (ReferenceActivePhysicalStep.collectionInput record.input payload ledger clock cutoff).clock
      (ReferenceActivePhysicalStep.collectionInput record.input payload ledger clock cutoff).ledger.pending =
        .ok started)
    (instruction : CoordinatorPhaseClock.AssignmentStartInstruction p)
    (hinstruction : started.assignmentStart = some instruction)
    (output : LaterAssignmentStartOperation.SuccessfulStart
      (ReferenceActivePhysicalStep.collectionInput record.input payload ledger clock cutoff).payload
      (CoordinatorRoundDispatch.collectionOperationLedger
        (ReferenceActivePhysicalStep.collectionInput record.input payload ledger clock cutoff)
        core.payload_n_eq)
      instruction
      (ReferenceActivePhysicalStep.collectionInput record.input payload ledger clock cutoff).row)
    (hlocal : output.localConsistency = consistent)
    (clockData : CoordinatorAssignmentRegisterInstall.LaterStartRoundEvidence output)
    (installed : CoordinatorAssignmentRegisterInstall.LaterInstallation output clockData)
    (selected : CoordinatorRoundDispatch.ArmSelection installed.registers.payload started
      instruction.time installed.registers.complementWeights
      (ReferenceActivePhysicalStep.collectionInput record.input payload ledger clock cutoff).row)
    (hbranch : record.output.preparation.coordinator =
      .collection payload ledger clock cutoff
        (.laterChosen core consistent started hstart instruction hinstruction output hlocal
          clockData installed selected)) :
    InstallationBirth record installed.registers.payload ∧
      installationScoreVector record installed.registers.payload
        (fun a => AssignmentScoreReconstruction.sourceScore output.reconstruction a) ∧
      installed.registers.payload.sigma.val = record.input.time.val := by
  have hactual : record.output.preparation.coordinator =
      ReferenceActivePhysicalStep.dispatch record.input := by
    rw [record.output_eq]
    rfl
  have hprovenance := ReferenceLaterInstallationProvenance.dispatch_laterChosen_provenance
    record.input
  rw [← hactual, hbranch] at hprovenance
  rcases hprovenance with ⟨hinstalled, _, htime, _⟩
  have hbirth := ReferenceLaterInstallationProvenance.record_laterChosen_birth record
  rw [hbranch] at hbirth
  cases hinstalled
  refine ⟨hbirth, ?_, htime⟩
  simp only [installationScoreVector, hbranch]
  constructor
  · rfl
  constructor
  · trivial
  · intro j
    exact CoordinatorAssignmentRegisterInstall.later_complement_score_eq_source_score
      output clockData j

private theorem arm_transport
    (P Q : Payload rate) (h : P = Q)
    (j : CanonicalFastSampling.FastArm P.slowSet) :
    (h.symm ▸ (h ▸ j)) = j ∧ (h ▸ j).1 = j.1 := by
  cases h
  exact ⟨rfl, rfl⟩

private theorem live_tail_span
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (history : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (hin : liveScoreSpanAt history record.input.time.val (.live r q base)) :
    liveScoreSpanAt history (record.input.time.val + 1)
      (livePostChoice record.output.preparation r q base started).configuration := by
  cases hout : (livePostChoice record.output.preparation r q base started).configuration with
  | first => trivial
  | collection payload ledger saved => trivial
  | dagger => trivial
  | live next nextQueues nextBase =>
      obtain ⟨birth, hmem, hbirth, z, hz, htime, hchron, hscore⟩ := hin
      obtain ⟨hp, serviced, hservice, hnext⟩ :=
        livePostChoice_score_bounds record.input record.output.preparation r q base started
          next nextQueues nextBase hout
      refine ⟨birth, hmem, ?_, z, ?_, ?_, ?_, ?_⟩
      · simpa only [hp] using hbirth
      · simpa only [hp] using hz
      · simpa only [hp] using htime
      · rw [hp]
        omega
      · intro j
        let oldj : CanonicalFastSampling.FastArm r.payload.slowSet := hp ▸ j
        obtain ⟨hback, harm⟩ := arm_transport next.payload r.payload hp j
        have hread : next.complementScores j = serviced.score oldj := by
          have heq := hnext oldj
          change next.complementScores (hp.symm ▸ (hp ▸ j)) = serviced.score oldj at heq
          rw [hback] at heq
          exact heq
        have hprior := hscore oldj
        have hcap := hservice oldj
        rw [harm] at hprior
        rw [hread]
        constructor
        · exact hprior.1.trans hcap.1
        · have hdiff : record.input.time.val + 1 + 1 - (r.payload.sigma.val + 1) =
              (record.input.time.val + 1 - (r.payload.sigma.val + 1)) + 1 := by omega
          have hsigma : next.payload.sigma.val = r.payload.sigma.val :=
            congrArg (fun P : Payload rate => P.sigma.val) hp
          rw [hsigma, hdiff, Nat.mul_add, Nat.mul_one]
          omega

private theorem span_history_mono
    (left right : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (endpoint : ℕ) (configuration : CoordinatorConfiguration p rate)
    (hmem : ∀ birth, birth ∈ left → birth ∈ right)
    (hspan : liveScoreSpanAt left endpoint configuration) :
    liveScoreSpanAt right endpoint configuration := by
  cases configuration with
  | first => trivial
  | collection payload ledger saved => trivial
  | dagger => trivial
  | live r q base =>
      obtain ⟨birth, hb, hrest⟩ := hspan
      exact ⟨birth, hmem birth hb, hrest⟩

private theorem birth_seed_span
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (history : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ) (z : Fin p.K → ℕ)
    (hsource : InstallationBirth record r.payload ∧
      installationScoreVector record r.payload z ∧ r.payload.sigma.val = record.input.time.val)
    (hscore : ∀ j, r.complementScores j = z j.1) :
    liveScoreSpanAt (history ++ [record]) record.input.time.val (.live r q base) := by
  refine ⟨record, by simp, hsource.1, z, hsource.2.1, ?_, ?_, ?_⟩
  · omega
  · omega
  · intro j
    rw [hscore j, hsource.2.2]
    simp

private theorem collection_tail_span
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (history : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (payload : Payload rate) (ledger : Ledger rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ) :
    liveScoreSpanAt history (record.input.time.val + 1)
      (collectionPostChoice record.output.preparation payload ledger started weights).configuration := by
  cases h : (collectionPostChoice record.output.preparation payload ledger started weights).configuration with
  | first => trivial
  | collection payload ledger saved => trivial
  | dagger => trivial
  | live r q base =>
      exact False.elim (collectionPostChoice_not_live record.input record.output.preparation
        payload ledger started weights r q base h)

private theorem round_score_span
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (history : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (hin : liveScoreSpanAt history record.input.time.val record.input.state.coordinator) :
    liveScoreSpanAt (history ++ [record]) (record.input.time.val + 1)
      record.output.next.coordinator := by
  classical
  have hprep : record.output.preparation = prepare record.input := by
    rw [record.output_eq]
    rfl
  have hout : record.output.next.coordinator =
      record.output.preparation.observeCoordinator.configuration := by
    rw [record.output_eq]
    rfl
  rw [hout]
  by_cases hselected : record.output.preparation.coordinator.selection = none
  · simp only [PreparedRound.observeCoordinator, dite_eq_left hselected]
    cases record.output.preparation.coordinator <;> trivial
  · simp only [PreparedRound.observeCoordinator, dite_eq_right hselected]
    have hactual : record.output.preparation.coordinator = dispatch record.input := by
      rw [hprep]
      rfl
    cases hconfiguration : record.input.state.coordinator with
    | first =>
        have hcut : record.output.preparation.coordinator =
            .first (CoordinatorRoundDispatch.dispatchFirst (firstInput record.input)) := by
          rw [hactual]
          simp only [ReferenceActivePhysicalStep.dispatch, hconfiguration, CoordinatorRoundDispatch.dispatch]
          rfl
        rw [hcut]
        cases ho : CoordinatorRoundDispatch.dispatchFirst (firstInput record.input)
        all_goals try trivial
        case chosen installed selected =>
          have hbranch := hcut.trans (congrArg DispatchCut.first ho)
          have hs := first_installation_source record installed selected hbranch
          have hseed : ∀ j, installed.registers.complementScores j = (fun _ => 0) j.1 := by
            have hv := hs.2.1
            simp only [installationScoreVector, hbranch] at hv
            exact hv.2.2
          exact live_tail_span record (history ++ [record]) installed.registers
            installed.ownedRegisters installed.followerBaseScore installed.startRoundResult
            (birth_seed_span record history installed.registers installed.ownedRegisters
              installed.followerBaseScore (fun _ => 0) hs hseed)
    | live r q base =>
        have hcut : record.output.preparation.coordinator = .live r q base
            (CoordinatorRoundDispatch.dispatchLive (liveInput record.input r q base)) := by
          rw [hactual]
          simp only [ReferenceActivePhysicalStep.dispatch, hconfiguration, CoordinatorRoundDispatch.dispatch]
          rfl
        rw [hcut]
        cases ho : CoordinatorRoundDispatch.dispatchLive (liveInput record.input r q base)
        all_goals try trivial
        case continuingChosen dispatched hstart hno selected =>
          have hs : liveScoreSpanAt history record.input.time.val (.live r q base) := by
            simpa only [hconfiguration] using hin
          have hat : liveScoreSpanAt history record.input.time.val
              (.live (liveRegistersAt r record.input.time)
                (liveOwnedAt r q record.input.time) base) := hs
          exact live_tail_span record (history ++ [record])
            (liveRegistersAt r record.input.time) (liveOwnedAt r q record.input.time)
            base dispatched.startResult
            (span_history_mono history (history ++ [record]) _ _
              (by intro birth hb; exact List.mem_append_left _ hb) hat)
        case cutoffChosen dispatched hstart ledger hinit hcandidate hdomains hclock hpending hno selected =>
          exact collection_tail_span record (history ++ [record]) r.payload
            (sharedLedger ledger) dispatched.startResult (liveRegistersAt r record.input.time).complementWeights
    | collection old ledger saved =>
        by_cases hcutoff : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
        · let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
          let clock := collectionClock old ledger saved cutoff
          have hcut : record.output.preparation.coordinator = .collection old ledger clock cutoff
              (CoordinatorRoundDispatch.dispatchCollection
                (collectionInput record.input old ledger clock cutoff)) := by
            rw [hactual]
            simp only [ReferenceActivePhysicalStep.dispatch, hconfiguration, dite_eq_left hcutoff, CoordinatorRoundDispatch.dispatch]
            rfl
          rw [hcut]
          cases ho : CoordinatorRoundDispatch.dispatchCollection
              (collectionInput record.input old ledger clock cutoff)
          all_goals try trivial
          case continuing core snapshot hcontinue selected =>
            exact collection_tail_span record (history ++ [record]) old ledger snapshot.clockStarted
              (CoordinatorCollectionInteractive.PreObservationInputs.weights
                (collectionInput record.input old ledger clock cutoff)
                snapshot.inputsValid.ledger_valid snapshot.inputsValid.assignment_eq)
          case laterChosen core consistent started hstart instruction hinstruction output hlocal
              clockData installed selected =>
            have hbranch : record.output.preparation.coordinator =
                .collection old ledger clock cutoff (.laterChosen core consistent started hstart
                  instruction hinstruction output hlocal clockData installed selected) := by
              rw [hcut, ho]
            have hs := later_installation_source record old ledger clock cutoff core consistent
              started hstart instruction hinstruction output hlocal clockData installed selected hbranch
            let z : Fin p.K → ℕ := fun a => AssignmentScoreReconstruction.sourceScore output.reconstruction a
            have hseed : ∀ j, installed.registers.complementScores j = z j.1 := by
              have hv := hs.2.1
              simp only [installationScoreVector, hbranch] at hv
              exact hv.2.2
            exact live_tail_span record (history ++ [record]) installed.registers
              installed.ownedRegisters installed.retainedBaseScore started
              (birth_seed_span record history installed.registers installed.ownedRegisters
                installed.retainedBaseScore z hs hseed)
        · have hcut : record.output.preparation.coordinator = .invalidCollectionCutoff := by
            rw [hactual]
            simp only [ReferenceActivePhysicalStep.dispatch, hconfiguration, dite_eq_right hcutoff]
          rw [hcut]
          trivial
    | dagger =>
        have hcut : record.output.preparation.coordinator = .dagger := by
          rw [hactual]
          simp only [ReferenceActivePhysicalStep.dispatch, hconfiguration]
        rw [hcut]
        trivial

private theorem connected_first_input
    {initial final : ReferenceActivePhysicalHorizon.State p rate}
    {records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))}
    (hconnected : ReferenceActivePhysicalHorizon.Connected initial records final)
    (h : 0 < records.length) : records[0].input.state = initial := by
  cases records with
  | nil => simp only [List.length_nil] at h; omega
  | cons record rest => exact hconnected.1

private theorem connected_succ_input
    {initial final : ReferenceActivePhysicalHorizon.State p rate}
    {records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))}
    (hconnected : ReferenceActivePhysicalHorizon.Connected initial records final)
    (n : ℕ) (h : n + 1 < records.length) :
    records[n + 1].input.state = records[n].output.next := by
  induction records generalizing initial n with
  | nil => simp only [List.length_nil] at h; omega
  | cons record rest ih =>
      cases n with
      | zero =>
          cases rest with
          | nil => simp only [List.length_cons, List.length_nil] at h; omega
          | cons next tail => exact hconnected.2.1
      | succ n =>
          exact ih hconnected.2 n (by simp only [List.length_cons] at h; omega)

private theorem complete_input_output_span
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p) :
    let R := completeSuffixRecords rate source rewards C_star C_h
    ∀ k : Fin R.length,
      liveScoreSpanAt (R.take k.val) R[k.val].input.time.val R[k.val].input.state.coordinator ∧
      liveScoreSpanAt (R.take (k.val + 1)) (R[k.val].input.time.val + 1)
        R[k.val].output.next.coordinator := by
  classical
  dsimp only
  let R := completeSuffixRecords rate source rewards C_star C_h
  intro k
  cases hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h with
  | none =>
      have hlength := k.isLt
      simp only [completeSuffixRecords, hlaunch, dite_true, List.length_nil] at hlength
      omega
  | some active =>
      have hc :=
        (ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
          rate source rewards C_star C_h).mp (by rw [hlaunch]; rfl)
      let initial := ReferenceFirstLaunchNumericalCell.launchState
        rate source rewards C_star C_h hc
      let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
        rate source rewards C_star C_h hc
      have hcanonical :=
        ReferenceFirstLaunchNumericalCell.correctedLaunch_eq_some_launchState
          rate source rewards C_star C_h hc
      have hconnected := completeSuffix_connected_on_launch
        rate source rewards C_star C_h initial hcanonical
      have hfold : ∀ n (hn : n < R.length),
          liveScoreSpanAt (R.take n) R[n].input.time.val R[n].input.state.coordinator ∧
          liveScoreSpanAt (R.take (n + 1)) (R[n].input.time.val + 1)
            R[n].output.next.coordinator := by
        intro n
        induction n with
        | zero =>
            intro hn
            have hstate := connected_first_input hconnected hn
            have hin : liveScoreSpanAt (R.take 0) R[0].input.time.val R[0].input.state.coordinator := by
              rw [hstate, seed.coordinatorFirst]
              trivial
            refine ⟨hin, ?_⟩
            rw [List.take_succ_eq_append_getElem hn]
            exact round_score_span R[0] (R.take 0) hin
        | succ n ih =>
            intro hn
            have hnprev : n < R.length := by omega
            have htime : R[n + 1].input.time.val = R[n].input.time.val + 1 := by
              have hprev := ReferenceAssignmentFollowerMassSteps.complete_record_time
                rate rewards C_star C_h source ⟨n, hnprev⟩
              have hnext := ReferenceAssignmentFollowerMassSteps.complete_record_time
                rate rewards C_star C_h source ⟨n + 1, hn⟩
              change R[n].input.time.val = _ + n at hprev
              change R[n + 1].input.time.val = _ + (n + 1) at hnext
              omega
            have hstate := connected_succ_input hconnected n hn
            have hin : liveScoreSpanAt (R.take (n + 1)) R[n + 1].input.time.val
                R[n + 1].input.state.coordinator := by
              rw [hstate, htime]
              exact (ih hnprev).2
            refine ⟨hin, ?_⟩
            rw [List.take_succ_eq_append_getElem hn]
            exact round_score_span R[n + 1] (R.take (n + 1)) hin
      exact hfold k.val k.isLt

/-- Before any actual incoming LIVE round, its same earlier installation in
that source prefix supplies the whole installed score vector. Every actual
complement entry has grown from that vector by at most `4*n` per elapsed
round. The input endpoint is before the current service, including on a round
whose later dispatcher fails or initiates collection. -/
theorem complete_live_complement_score_span
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (completeSuffixRecords rate source rewards C_star C_h).length)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ)
    (hlive : (completeSuffixRecords rate source rewards C_star C_h)[k.val].input.state.coordinator =
      .live r q base) :
    let R := completeSuffixRecords rate source rewards C_star C_h
    ∃ birth, birth ∈ R.take k.val ∧ InstallationBirth birth r.payload ∧
      ∃ z : Fin p.K → ℕ,
        installationScoreVector birth r.payload z ∧
        birth.input.time.val + 1 = r.payload.sigma.val + 1 ∧
        r.payload.sigma.val ≤ R[k.val].input.time.val ∧
        ∀ j : CanonicalFastSampling.FastArm r.payload.slowSet,
          z j.1 ≤ r.complementScores j ∧
          r.complementScores j ≤ z j.1 + (4 * rate.n) *
            (R[k.val].input.time.val + 1 - (r.payload.sigma.val + 1)) := by
  have h := (complete_input_output_span rate rewards C_star C_h source k).1
  rw [hlive] at h
  exact h

/-- The same installation-relative estimate at an actual LIVE output, including
the terminal physical round. This requires only the observed output equation;
no success premise is imposed on later records. A birth in this round is
included, and the endpoint counts this round's single service update. -/
theorem complete_live_output_complement_score_span
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (completeSuffixRecords rate source rewards C_star C_h).length)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ)
    (hlive : (completeSuffixRecords rate source rewards C_star C_h)[k.val].output.next.coordinator =
      .live r q base) :
    let R := completeSuffixRecords rate source rewards C_star C_h
    ∃ birth, birth ∈ R.take (k.val + 1) ∧ InstallationBirth birth r.payload ∧
      ∃ z : Fin p.K → ℕ,
        installationScoreVector birth r.payload z ∧
        birth.input.time.val + 1 = r.payload.sigma.val + 1 ∧
        r.payload.sigma.val ≤ R[k.val].input.time.val + 1 ∧
        ∀ j : CanonicalFastSampling.FastArm r.payload.slowSet,
          z j.1 ≤ r.complementScores j ∧
          r.complementScores j ≤ z j.1 + (4 * rate.n) *
            (R[k.val].input.time.val + 1 + 1 - (r.payload.sigma.val + 1)) := by
  have h := (complete_input_output_span rate rewards C_star C_h source k).2
  rw [hlive] at h
  exact h

/-- At an actual cutoff choice, the literal initialized outside registers
retain the same installation-relative bound as the incoming LIVE scores.
Neither reception nor the cutoff round's post-choice operations are assumed
to succeed. -/
theorem complete_cutoff_complement_score_span
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (completeSuffixRecords rate source rewards C_star C_h).length)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ)
    (hlive : (completeSuffixRecords rate source rewards C_star C_h)[k.val].input.state.coordinator =
      .live r q base)
    (c : ReferenceCollectionSegmentExtraction.Choice rate)
    (hchoice : ReferenceCollectionSegmentExtraction.choice
      (completeSuffixRecords rate source rewards C_star C_h)[k.val].input = some c) :
    let R := completeSuffixRecords rate source rewards C_star C_h
    ∃ birth, birth ∈ R.take k.val ∧ InstallationBirth birth r.payload ∧
      ∃ z : Fin p.K → ℕ,
        installationScoreVector birth r.payload z ∧
        birth.input.time.val + 1 = r.payload.sigma.val + 1 ∧
        c.preLedger.sigma = r.payload.sigma.val + 1 ∧
        c.preLedger.cutoff = R[k.val].input.time.val + 1 ∧
        ∀ j : CanonicalFastSampling.FastArm r.payload.slowSet,
          ∃ cut : CoordinatorCollectionLedger.CutoffRegister,
            c.preLedger.cutoffRegisters j.1 = some cut ∧
            cut.score = r.complementScores j ∧
            z j.1 ≤ cut.score ∧
            cut.score ≤ z j.1 + (4 * rate.n) *
              (c.preLedger.cutoff - (r.payload.sigma.val + 1)) := by
  classical
  let R := completeSuffixRecords rate source rewards C_star C_h
  let x := R[k.val].input
  have hcut : (prepare x).coordinator = .live r q base
      (CoordinatorRoundDispatch.dispatchLive (liveInput x r q base)) := by
    change x.state.coordinator = .live r q base at hlive
    change ReferenceActivePhysicalStep.dispatch x = _
    simp only [ReferenceActivePhysicalStep.dispatch, hlive, CoordinatorRoundDispatch.dispatch]
    rfl
  have hc := hchoice
  change ReferenceCollectionSegmentExtraction.choice x = some c at hc
  unfold ReferenceCollectionSegmentExtraction.choice at hc
  split at hc
  · cases hc
  · rw [hcut] at hc
    cases ho : CoordinatorRoundDispatch.dispatchLive (liveInput x r q base)
    all_goals simp only [ho, ReferenceCollectionSegmentExtraction.choiceOfCut] at hc
    all_goals try cases hc
    case isFalse.cutoffChosen.refl dispatched hstart ledger hinit hcandidate hdomains hclock hpending hno selected =>
      obtain ⟨birth, hb, hbirth, z, hz, htime, _hchron, hscore⟩ :=
        complete_live_complement_score_span rate rewards C_star C_h source k r q base hlive
      refine ⟨birth, hb, hbirth, z, hz, htime, ?_, ?_, ?_⟩
      · change (sharedLedger ledger).sigma = _
        rw [hcandidate]
        rfl
      · change (sharedLedger ledger).cutoff = _
        rw [hcandidate]
        rfl
      · intro j
        let cut : CoordinatorCollectionLedger.CutoffRegister :=
          ⟨r.complementScores j, q.queue j, q.previousService j⟩
        refine ⟨cut, ?_, rfl, (hscore j).1, ?_⟩
        · change (sharedLedger ledger).cutoffRegisters j.1 = some cut
          rw [hcandidate]
          change CoordinatorStartRoundCutoffDispatch.outsideRegisters
            (liveRegistersAt r x.time) (liveOwnedAt r q x.time) j.1 = some cut
          unfold CoordinatorStartRoundCutoffDispatch.outsideRegisters
          have hj : j.1 ∈ CanonicalFastSampling.fastArmFinset
              (liveRegistersAt r x.time).payload.slowSet := j.property
          rw [dite_eq_left hj]
          rfl
        · change r.complementScores j ≤ z j.1 + (4 * rate.n) *
            ((sharedLedger ledger).cutoff - (r.payload.sigma.val + 1))
          rw [hcandidate]
          exact (hscore j).2

end Bandits.Support.ReferenceCompleteLiveComplementScoreSpan

end
