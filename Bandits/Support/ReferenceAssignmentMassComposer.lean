/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceAcceptedUpAssignmentBirthJoin
public import Bandits.Support.ReferenceCompleteFollowerCutoffPhase
public import Bandits.Support.ReferenceAssignmentCollectionMassSteps

import Lean.Elab.Tactic.Omega

/-!
# Numerical composition on the original complete physical suffix

Sources: `sources/zip4/manuscript/appendix_a_local_protocol.tex:28-64`
and `sources/zip4/manuscript/06_interruptions.tex:255-282,303-348,355-390`.
The installation base is the existing literal `installedBaseScore` projection.
Historical births remain available even when a subsequent operation fails.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ReferenceAssignmentMassComposer

open ConstructorDimensions ReferenceActivePhysicalStep
open ReferenceActivePhysicalHorizon (RoundRecord)
open ReferenceAssignmentCollectionMassSteps

variable {p : ConstructorDimensions.Parameters} {rate : RateInput p}

/-- PREPARE supplies one base witness for all numerical birth assertions,
including the DOWN credit used by acceptance in this very round. The incoming
ledger credit is a local induction premise, before observation and FINISH. -/
private theorem record_birth_mass_of_ready_credit
    (record : RoundRecord (p := p) (rate := rate))
    (hready : ∀ (old : Payload rate) (l : Ledger rate)
      (saved : Option (Fin p.T × Bool)),
      record.input.state.coordinator = .collection old l saved →
      ∀ (a : Fin p.K) (c : CoordinatorCollectionLedger.CutoffRegister)
        (q : CoordinatorCollectionLedger.CurrentRegister),
        l.cutoffRegisters a = some c → l.currentRegisters a = some q →
        c.score + l.increment a + q.queue ≤ record.input.time.val * D p)
    (P : Payload rate)
    (hbirth : ReferenceAssignmentPayloadPersistence.InstallationBirth record P) :
    ∃ beta : Fin (p.m - 1) → ℕ,
      installedBaseScore record = some beta ∧
      (∀ a : Fin p.K, P.queues a ≤ P.sigma.val * D p) ∧
      (∀ i : Fin (p.m - 1), beta i + P.queues (P.assignment.assigned i) ≤
        P.sigma.val * D p) ∧
      (∀ i : Fin (p.m - 1), beta i + (P.downRecord i).val.q ≤
        ((P.downRecord i).val.sigma - 1) * D p) := by
  obtain ⟨beta, hbase, hqueues, hassigned⟩ :=
    ReferenceAssignmentCollectionMassSteps.record_birth_mass_of_ready_credit
      record hready P hbirth
  refine ⟨beta, hbase, hqueues, hassigned, ?_⟩
  intro i
  rw [P.downRecord_initialQueue i, P.downRecord_fields i]
  simpa only [Nat.add_sub_cancel] using hassigned i

/-- Equal start coordinates identify both actual birth records before their
literal installation bases are compared. -/
private theorem complete_birth_base_unique
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (b c : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (P Q : Payload rate)
    (hbirthP : ReferenceAssignmentPayloadPersistence.InstallationBirth
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[b.val] P)
    (hbirthQ : ReferenceAssignmentPayloadPersistence.InstallationBirth
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[c.val] Q)
    (hsigma : P.sigma.val = Q.sigma.val) :
    b = c ∧ P = Q ∧ ∀ beta gamma : Fin (p.m - 1) → ℕ,
      installedBaseScore (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[b.val] = some beta →
      installedBaseScore (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[c.val] = some gamma → beta = gamma := by
  have hbTime := ReferenceAssignmentPayloadChronology.installationBirth_time_eq _ P hbirthP
  have hcTime := ReferenceAssignmentPayloadChronology.installationBirth_time_eq _ Q hbirthQ
  rw [ReferenceAssignmentFollowerMassSteps.complete_record_time
    rate rewards C_star C_h source b] at hbTime
  rw [ReferenceAssignmentFollowerMassSteps.complete_record_time
    rate rewards C_star C_h source c] at hcTime
  have hindices : b = c := by
    apply Fin.ext
    omega
  subst c
  refine ⟨rfl, ReferenceAssignmentPayloadChronology.installationBirth_payload_unique
    _ P Q hbirthP hbirthQ, ?_⟩
  intro beta gamma hbeta hgamma
  exact Option.some.inj (hbeta.symm.trans hgamma)

/-- An accepted UP spends the sender's own historical birth credit at the
OLD cutoff. The input follower witness and the coordinator witness are built
independently, then equal sigma identifies their literal base vectors.
This is the local reply step of the simultaneous prefix induction. -/
private theorem complete_accepted_up_mass_of_prefix_credit
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (c : ReferenceCollectionSegmentExtraction.Choice rate)
    (hchoice : ReferenceCollectionSegmentExtraction.choice
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val].input = some c)
    (i : Fin (p.m - 1)) (U : ReferenceCollectionPhaseHistory.UpRecord p rate)
    (hfollowers : ∀ (F : ReferencePrelaunchFollower.State p rate.eta)
      (memory : ActiveFollowerLifecycle.LocalMemory p),
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val].input.state.followers i = .ordinary F memory →
      ∀ M, F.lastDown = some M →
      ∃ (b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h).length) (P : Payload rate)
        (beta : Fin (p.m - 1) → ℕ),
        b.val < k.val ∧ ReferenceAssignmentPayloadPersistence.InstallationBirth
          (ReferenceCompletePhysicalHistory.completeSuffixRecords
            rate source rewards C_star C_h)[b.val] P ∧
        installedBaseScore (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h)[b.val] = some beta ∧ M = P.downRecord i ∧
        beta i + F.S + F.backlog ≤
          min (ReferenceCompletePhysicalHistory.completeSuffixRecords
            rate source rewards C_star C_h)[k.val].input.time.val
            (FollowerCutoffScan.firstCutoff p rate.eta.val P.sigma
              (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
                (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source))) - 1) * D p ∧
        F.delta ≤ D p)
    (haccepted : ReferenceCollectionPhaseHistory.AcceptedUp
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val].input i U) :
    c.preLedger.baseScore i + U.val.S + U.val.q ≤ (c.preLedger.cutoff - 1) * D p ∧
      U.val.delta ≤ D p := by
  obtain ⟨bc, j, F, memory, _hbcj, _hjk, hbirthc, _hretained,
    hinput, hlast, _hreplySigma, _hledgerSigma, hS, hdelta, hq, hcutoff, hbase⟩ :=
    ReferenceAcceptedUpAssignmentBirthJoin.complete_accepted_up_birth_join
      rate rewards C_star C_h source k c hchoice i U haccepted
  obtain ⟨bf, P, beta, _hbfk, hbirthf, hbetaf, hmessage, hmass, hcap⟩ :=
    hfollowers F memory hinput _ hlast
  have hsigma : P.sigma.val = c.payload.sigma.val := by
    have heq := congrArg (fun M : OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta) => M.val.sigma) hmessage
    rw [P.downRecord_fields i, c.payload.downRecord_fields i] at heq
    change c.payload.sigma.val + 1 = P.sigma.val + 1 at heq
    omega
  obtain ⟨_hbirthIndex, hP, hbaseUnique⟩ := complete_birth_base_unique
    rate rewards C_star C_h source bf bc P c.payload hbirthf hbirthc hsigma
  have hbetac : installedBaseScore (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[bc.val] = some c.preLedger.baseScore := by
    unfold installedBaseScore
    split at hbase <;> simp_all only
  have hbeta := hbaseUnique beta c.preLedger.baseScore hbetaf hbetac
  subst P
  rw [hbeta, ← hcutoff] at hmass
  rw [hS, hq, hdelta]
  exact ⟨hmass.trans (Nat.mul_le_mul_right (D p) (min_le_right _ _)), hcap⟩

private theorem choice_executedTail
    (x : RoundInput p rate) (c : ReferenceCollectionSegmentExtraction.Choice rate)
    (hchoice : ReferenceCollectionSegmentExtraction.choice x = some c) :
    ReferenceCollectionPhaseHistory.executedTail x =
      some ⟨c.payload, c.preLedger, c.started, c.weights⟩ := by
  unfold ReferenceCollectionSegmentExtraction.choice at hchoice
  split at hchoice
  · contradiction
  next hn =>
    unfold ReferenceCollectionPhaseHistory.executedTail
    dsimp only
    split
    · contradiction
    next _ =>
      cases hc : (prepare x).coordinator with
      | first outcome =>
          cases outcome <;>
            simp only [hc, ReferenceCollectionSegmentExtraction.choiceOfCut] at hchoice
          all_goals contradiction
      | live r q base outcome =>
          cases outcome <;>
            simp only [hc, ReferenceCollectionSegmentExtraction.choiceOfCut] at hchoice
          all_goals first | contradiction | (cases Option.some.inj hchoice; rfl)
      | collection payload ledger clock cutoff outcome =>
          cases outcome <;>
            simp only [hc, ReferenceCollectionSegmentExtraction.choiceOfCut] at hchoice
          all_goals first | contradiction | (cases Option.some.inj hchoice; rfl)
      | invalidCollectionCutoff =>
          simp only [hc, ReferenceCollectionSegmentExtraction.choiceOfCut] at hchoice
          contradiction
      | dagger =>
          simp only [hc, ReferenceCollectionSegmentExtraction.choiceOfCut] at hchoice
          contradiction

/-- A successful local decode of the actual filtered input produces the
physical acceptance event consumed by the historical birth join. -/
private theorem local_decode_accepted_up
    (x : RoundInput p rate) (c : ReferenceCollectionSegmentExtraction.Choice rate)
    (hchoice : ReferenceCollectionSegmentExtraction.choice x = some c)
    (recording : CoordinatorRecordingOperation.Output p)
    (started decoded : Ledger rate)
    (hrecord : CoordinatorRecorderComplementBridge.run
      (collectionRecordingInput (prepare x) c.payload c.started c.weights) = some recording)
    (hstart : CoordinatorCollectionLedger.startRound c.preLedger (x.time.val + 1)
      (collectionEnabled c.preLedger x.time)
      (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) = .success started)
    (hreception : (receiveUp (prepare x) started).result ≠ .invalid)
    (U : ReferenceCollectionPhaseHistory.UpRecord p rate)
    (hparsed : ReferenceCollectionSegmentExtraction.effectiveParse x started = some U)
    (hdecode : CoordinatorCollectionLedger.decodeUp started (upSenderIndex x) (some U) =
      .success decoded) :
    ReferenceCollectionPhaseHistory.AcceptedUp x (upSenderIndex x) U := by
  refine ⟨⟨c.payload, c.preLedger, c.started, c.weights⟩, recording, started, decoded,
    CoordinatorUpReception.decoderBankAfter
      (ReferenceUpReception.receptionInputAtRow rate x.row
        (upInputs (prepare x) started) x.time),
    choice_executedTail x c hchoice, hrecord, hstart, ?_, hparsed, rfl⟩
  rw [ReferenceCollectionSegmentExtraction.receiveUp_filtered x started
    (ReferenceCollectionSegmentExtraction.receiveUp_input_check x started hreception),
    hparsed, hdecode]
  rfl

private theorem live_tail_mass
    (x : RoundInput p rate)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ) (started : CoordinatorPhaseClock.StartRoundResult p)
    (hcredit : ∀ j : CanonicalFastSampling.FastArm r.payload.slowSet,
      r.complementScores j + owned.queue j ≤ x.time.val * D p) :
    match (livePostChoice (prepare x) r owned base started).configuration with
    | .live next queues _ =>
        (∀ j : CanonicalFastSampling.FastArm next.payload.slowSet,
          next.complementScores j + queues.queue j ≤ (x.time.val + 1) * D p) ∧
        queues.previousServiceDomainValid
    | .dagger => True
    | _ => False := by
  unfold livePostChoice
  cases hrecord : CoordinatorRecorderComplementBridge.run
      (liveRecordingInput (prepare x) r started) with
  | none => trivial
  | some recording =>
      dsimp only
      cases hservice : CoordinatorLiveServiceFinish.servicePass r owned recording with
      | error reason => trivial
      | ok serviced =>
          dsimp only
          cases hconfirmation : CoordinatorLocalArmChoice.confirmationUpdate r.payload started.pending
              (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
              x.time x.row (prepare x).coordinatorObservation with
          | none => trivial
          | some pending =>
              dsimp only
              cases hfinish : CoordinatorPhaseClock.finishRound p rate.eta.val x.time
                  started.clock pending x.row with
              | error reason => trivial
              | ok finished =>
                  dsimp only
                  exact ⟨live_service_mass r owned serviced x.time.val hcredit,
                    serviced.previousServiceDomain⟩

private theorem checked_round_cutoff
    (l started decoded finished : Ledger rate)
    (input : CollectionCheckedExecution.RoundInput (p := p) (eta := rate.eta.val))
    (hstart : CoordinatorCollectionLedger.startRound l
      (CoordinatorCollectionLedger.sourceRound input.round) input.enabled input.raw = .success started)
    (hdecode : CoordinatorCollectionLedger.decodeUp started input.selectedFollower input.parsed =
      .success decoded ∨ CoordinatorCollectionLedger.decodeUp started input.selectedFollower
        input.parsed = .rejected decoded)
    (hfinish : CoordinatorCollectionLedger.finishRound decoded = .success finished) :
    finished.cutoff = l.cutoff := by
  have hs := CollectionCheckedExecution.startRound_success_candidate l started
    (CoordinatorCollectionLedger.sourceRound input.round) input.enabled input.raw hstart
  have hf := CollectionCheckedExecution.finishRound_success_candidate decoded finished hfinish
  have hd : decoded.cutoff = started.cutoff := by
    rcases hdecode with hsuccess | hrejected
    · cases hp : input.parsed with
      | none =>
          simp only [hp, CoordinatorCollectionLedger.decodeUp] at hsuccess
          split at hsuccess
          · split at hsuccess <;> contradiction
          · contradiction
      | some U =>
          rw [hp] at hsuccess
          obtain ⟨_hbound, _last, _hsource, _past, _current, _hpast, _hcurrent,
            _hunknown, hcandidate⟩ := CollectionCheckedExecution.decodeUp_success_candidate
              started decoded input.selectedFollower U hsuccess
          rw [hcandidate]
          rfl
    · rw [CollectionKnownQueueContinuation.decodeUp_rejected_candidate
        started decoded input.selectedFollower input.parsed hrejected]
  rw [hf]
  change decoded.cutoff = l.cutoff
  rw [hd, hs]
  rfl

/-- Numerical preservation for an actually executed collection tail. Local
successful calls are recovered from the surviving endpoint. The reply premise
is about physical accepted events, so the filtered local parse must produce
that event before the numerical leaf can consume it. -/
private theorem collection_tail_mass
    (x : RoundInput p rate) (c : ReferenceCollectionSegmentExtraction.Choice rate)
    (hchoice : ReferenceCollectionSegmentExtraction.choice x = some c)
    (hcredit : ∀ (a : Fin p.K) (cutoff : CoordinatorCollectionLedger.CutoffRegister)
      (current : CoordinatorCollectionLedger.CurrentRegister),
      c.preLedger.cutoffRegisters a = some cutoff →
      c.preLedger.currentRegisters a = some current →
      cutoff.score + c.preLedger.increment a + current.queue ≤ x.time.val * D p ∧
        cutoff.score + cutoff.queue ≤ (c.preLedger.cutoff - 1) * D p ∧
        cutoff.lastService ≤ D p)
    (hreply : ∀ (i : Fin (p.m - 1)) (U : ReferenceCollectionPhaseHistory.UpRecord p rate),
      ReferenceCollectionPhaseHistory.AcceptedUp x i U →
      c.preLedger.baseScore i + U.val.S + U.val.q ≤ (c.preLedger.cutoff - 1) * D p ∧
        U.val.delta ≤ D p) :
    match (collectionPostChoice (prepare x) c.payload c.preLedger c.started c.weights).configuration with
    | .collection _ final _ =>
        ∀ (a : Fin p.K) (cutoff : CoordinatorCollectionLedger.CutoffRegister)
          (current : CoordinatorCollectionLedger.CurrentRegister),
          final.cutoffRegisters a = some cutoff → final.currentRegisters a = some current →
          cutoff.score + final.increment a + current.queue ≤ (x.time.val + 1) * D p ∧
            cutoff.score + cutoff.queue ≤ (final.cutoff - 1) * D p ∧
            cutoff.lastService ≤ D p ∧ current.lastService ≤ D p
    | .dagger => True
    | _ => False := by
  unfold collectionPostChoice
  cases hrecord : CoordinatorRecorderComplementBridge.run
      (collectionRecordingInput (prepare x) c.payload c.started c.weights) with
  | none => trivial
  | some recording =>
      dsimp only
      cases hstart : CoordinatorCollectionLedger.startRound c.preLedger (x.time.val + 1)
          (collectionEnabled c.preLedger x.time)
          (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) with
      | invalid => trivial
      | rejected bad => trivial
      | success started =>
          dsimp only
          unfold collectionFinish
          have hdecode := ReferenceCollectionSegmentExtraction.receiveUp_decode_result x started
          cases hreceive : (receiveUp (prepare x) started).result with
          | invalid => trivial
          | success pair | rejected pair =>
              rcases pair with ⟨decoded, bank⟩
              simp only [hreceive] at hdecode ⊢
              cases hfinish : CoordinatorCollectionLedger.finishRound decoded with
              | invalid => trivial
              | rejected bad => trivial
              | success finished =>
                  dsimp only
                  cases hclock : CoordinatorPhaseClock.finishRound p rate.eta.val x.time
                      c.started.clock finished.pending x.row with
                  | error reason => trivial
                  | ok clockFinished =>
                      dsimp only
                      let input := ReferenceCollectionSegmentExtraction.inputOf
                        x c.preLedger recording started
                      have hd : CoordinatorCollectionLedger.decodeUp started input.selectedFollower
                          input.parsed = .success decoded ∨
                          CoordinatorCollectionLedger.decodeUp started input.selectedFollower
                            input.parsed = .rejected decoded := by
                        first | exact Or.inl hdecode | exact Or.inr hdecode
                      have hcutoff := checked_round_cutoff c.preLedger started decoded finished
                        input hstart hd hfinish
                      rw [hcutoff]
                      apply collection_round_mass c.preLedger started decoded finished input
                        hcredit ?_ hstart hd hfinish
                      intro U hparsed hsuccess
                      apply hreply (upSenderIndex x) U
                      exact local_decode_accepted_up x c hchoice recording started decoded
                        hrecord hstart (by rw [hreceive]; intro h; cases h) U hparsed hsuccess

private theorem retainedDown_selectedPayload
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1))
    (prior : ReferenceAcceptedUpFollowerHistory.DownRecord (p := p) (rate := rate))
    (hretained : ReferenceAcceptedUpFollowerHistory.RetainedDown record i prior) :
    ∃ selected : Selection record.input,
      record.output.preparation.coordinator.selection = some selected ∧
      prior = selected.view.payload.downRecord i := by
  obtain ⟨logged, cut, after, raw, scan, registers, lastService,
    hinput, hdown, haccepted⟩ := hretained
  obtain ⟨choice, memory, actualLogged, hconfiguration, hunoccupied, hlogging,
    hactualInput, hcut⟩ :=
    ReferenceFollowerSparseEmissionRecovery.actualDownDiagnostic_choice record i cut hdown
  have hactualIndex := (record.output.preparation.follower_alignment i).2.1
  have hloggedEq : actualLogged = logged := Option.some.inj (hactualInput.symm.trans hinput)
  subst actualLogged
  rw [hcut] at haccepted
  obtain ⟨view, hview⟩ := ReferenceFollowerSparseEmissionRecovery.acceptedReferenceCut_someView
    record.output.preparation.coordinator.downView
    (record.output.preparation.followers.followers i).follower
    (record.output.preparation.followers.followers i).row
    (record.output.preparation.followers.followers i).time
    (record.output.preparation.feedback.observations
      (PublicDiscreteDraws.followerPlayer p.two_le_m i)) logged logged after raw prior scan registers
    lastService haccepted
  rw [hview] at haccepted
  have hfields := ReferenceActiveDataOwnership.referenceDown_accepted_fields view
    (record.output.preparation.followers.followers i).follower
    (record.output.preparation.followers.followers i).row
    (record.output.preparation.followers.followers i).time
    (record.output.preparation.feedback.observations
      (PublicDiscreteDraws.followerPlayer p.two_le_m i)) logged logged after raw prior scan registers
    lastService haccepted
  have hmap : record.output.preparation.coordinator.selection.map Selection.view = some view := hview
  obtain ⟨selected, hselection, hselectedView⟩ := Option.map_eq_some_iff.mp hmap
  refine ⟨selected, hselection, ?_⟩
  have hmessage : prior = view.payload.downRecord i := by
    simpa only [hactualIndex] using hfields.1
  simpa only [hselectedView] using hmessage

/-- The original suffix's actual selected payload has an actual birth at or
before its selection, including a selection on the PREPARE birth round. -/
private theorem complete_selected_payload_birth
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (selected : Selection (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[k.val].input)
    (hselected : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[k.val].output.preparation.coordinator.selection = some selected) :
    ∃ b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length,
      b.val ≤ k.val ∧ ReferenceAssignmentPayloadPersistence.InstallationBirth
        (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h)[b.val] selected.view.payload := by
  cases hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h with
  | none =>
      have hlength := k.isLt
      simp only [ReferenceCompletePhysicalHistory.completeSuffixRecords, hlaunch,
        dite_true, List.length_nil] at hlength
      omega
  | some active =>
      have hc := (ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
        rate source rewards C_star C_h).mp (by rw [hlaunch]; rfl)
      let initial := ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hc
      let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
        rate source rewards C_star C_h hc
      have hrecords := ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
        rate source rewards C_star C_h initial
        (ReferenceFirstLaunchNumericalCell.correctedLaunch_eq_some_launchState
          rate source rewards C_star C_h hc)
      let start := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
      have span : start + (p.T - start) ≤ p.T := by
        have hs := ReferenceCompletePhysicalHistory.physicalStart_le_T
          rate source rewards C_star C_h
        dsimp only [start]
        omega
      let execution := ReferenceActivePhysicalHorizon.run initial source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start (p.T - start)
        span seed.activeAtStart
      have hrun : ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h = execution.records := hrecords
      have hmem : (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h)[k.val] ∈ execution.records := by
        rw [← hrun]
        exact List.getElem_mem k.isLt
      obtain ⟨birth, hbirthMem, hbirth, htime, hbefore⟩ :=
        ReferenceSelectedPayloadChronology.actualRun_selectedPayload_has_birth
          initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
          rewards start (p.T - start) span seed.activeAtStart seed.coordinatorFirst
          _ selected hmem hselected
      rw [← hrun] at hbirthMem
      obtain ⟨b, hb, hrecord⟩ := List.mem_iff_getElem.mp hbirthMem
      subst birth
      refine ⟨⟨b, hb⟩, ?_, hbirth⟩
      have hbtime := ReferenceAssignmentFollowerMassSteps.complete_record_time
        rate rewards C_star C_h source ⟨b, hb⟩
      have hktime := ReferenceAssignmentFollowerMassSteps.complete_record_time
        rate rewards C_star C_h source k
      change (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[b].input.time.val = start + b at hbtime
      change (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val].input.time.val = start + k.val at hktime
      change b ≤ k.val
      exact Nat.le_of_add_le_add_left
        (hbtime.symm.trans_le (htime.trans_le (hbefore.trans_eq hktime)))

/-- A retained accepted DOWN is from the selected payload's real birth;
there is no presumption that it is the current coordinator assignment. -/
private theorem complete_retained_down_birth
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (i : Fin (p.m - 1))
    (M : OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (hretained : ReferenceAcceptedUpFollowerHistory.RetainedDown
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val] i M) :
    ∃ (b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length) (P : Payload rate),
      b.val ≤ k.val ∧ ReferenceAssignmentPayloadPersistence.InstallationBirth
        (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h)[b.val] P ∧ M = P.downRecord i := by
  obtain ⟨selected, hselected, hmessage⟩ := retainedDown_selectedPayload _ i M hretained
  obtain ⟨b, hbk, hbirth⟩ := complete_selected_payload_birth
    rate rewards C_star C_h source k selected hselected
  exact ⟨b, selected.view.payload, hbk, hbirth, hmessage⟩

private theorem coordinator_round_mass
    (x : RoundInput p rate)
    (hlive : ∀ (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
      (q : CoordinatorLiveServiceFinish.OwnedRegisters r) (base : Fin (p.m - 1) → ℕ),
      x.state.coordinator = .live r q base →
      (∀ j : CanonicalFastSampling.FastArm r.payload.slowSet,
        r.complementScores j + q.queue j ≤ x.time.val * D p) ∧ q.previousServiceDomainValid)
    (hcollection : ∀ (P : Payload rate) (l : Ledger rate) (saved : Option (Fin p.T × Bool)),
      x.state.coordinator = .collection P l saved →
      ∀ (a : Fin p.K) (c : CoordinatorCollectionLedger.CutoffRegister)
        (q : CoordinatorCollectionLedger.CurrentRegister),
        l.cutoffRegisters a = some c → l.currentRegisters a = some q →
        c.score + l.increment a + q.queue ≤ x.time.val * D p ∧
          c.score + c.queue ≤ (l.cutoff - 1) * D p ∧
          c.lastService ≤ D p ∧ q.lastService ≤ D p)
    (hreply : ∀ (c : ReferenceCollectionSegmentExtraction.Choice rate),
      ReferenceCollectionSegmentExtraction.choice x = some c →
      ∀ (i : Fin (p.m - 1)) (U : ReferenceCollectionPhaseHistory.UpRecord p rate),
        ReferenceCollectionPhaseHistory.AcceptedUp x i U →
        c.preLedger.baseScore i + U.val.S + U.val.q ≤ (c.preLedger.cutoff - 1) * D p ∧
          U.val.delta ≤ D p) :
    match (prepare x).observeCoordinator.configuration with
    | .live r q _ =>
        (∀ j : CanonicalFastSampling.FastArm r.payload.slowSet,
          r.complementScores j + q.queue j ≤ (x.time.val + 1) * D p) ∧ q.previousServiceDomainValid
    | .collection _ l _ =>
        ∀ (a : Fin p.K) (c : CoordinatorCollectionLedger.CutoffRegister)
          (q : CoordinatorCollectionLedger.CurrentRegister),
          l.cutoffRegisters a = some c → l.currentRegisters a = some q →
          c.score + l.increment a + q.queue ≤ (x.time.val + 1) * D p ∧
            c.score + c.queue ≤ (l.cutoff - 1) * D p ∧
            c.lastService ≤ D p ∧ q.lastService ≤ D p
    | .dagger => True
    | .first => False := by
  classical
  by_cases hselected : (prepare x).coordinator.selection = none
  · simp only [PreparedRound.observeCoordinator, dite_eq_left hselected]
    cases (prepare x).coordinator <;> trivial
  · simp only [PreparedRound.observeCoordinator, dite_eq_right hselected]
    have hactual : (prepare x).coordinator = dispatch x := rfl
    cases hconfiguration : x.state.coordinator with
    | first =>
        have hcut : (prepare x).coordinator =
            .first (CoordinatorRoundDispatch.dispatchFirst (firstInput x)) := by
          rw [hactual]
          simp only [dispatch, hconfiguration, CoordinatorRoundDispatch.dispatch]
          rfl
        rw [hcut]
        cases ho : CoordinatorRoundDispatch.dispatchFirst (firstInput x) with
        | choiceDomainFailure installed => trivial
        | recorderBoundaryFailure installed => trivial
        | choiceRejected installed => trivial
        | chosen installed selected =>
            obtain ⟨hscores, hqueues, _hprevious, _hbase⟩ := dispatchFirst_zero_seed x installed selected ho
            have ht := live_tail_mass x installed.registers installed.ownedRegisters
              installed.followerBaseScore installed.startRoundResult (by
                intro j
                rw [hscores j, hqueues j, Nat.zero_add]
                exact Nat.zero_le _)
            split at ht <;> simp_all only [implies_true, and_true]
    | live r q base =>
        have hcut : (prepare x).coordinator = .live r q base
            (CoordinatorRoundDispatch.dispatchLive (liveInput x r q base)) := by
          rw [hactual]
          simp only [dispatch, hconfiguration, CoordinatorRoundDispatch.dispatch]
          rfl
        obtain ⟨hmass, hprevious⟩ := hlive r q base hconfiguration
        rw [hcut]
        cases ho : CoordinatorRoundDispatch.dispatchLive (liveInput x r q base)
        all_goals try trivial
        case continuingChosen dispatched hstart hno selected =>
          have ht := live_tail_mass x (liveRegistersAt r x.time) (liveOwnedAt r q x.time)
            base dispatched.startResult hmass
          split at ht <;> simp_all only [implies_true, and_true]
        case cutoffChosen dispatched hstart ledger hinit hcandidate hdomains hclock
            hpending hno selected =>
          let c : ReferenceCollectionSegmentExtraction.Choice rate :=
            ⟨r.payload, sharedLedger ledger, dispatched.startResult,
              (liveRegistersAt r x.time).complementWeights,
              some (ReferenceCollectionSegmentExtraction.cutoffInitializer
                (liveRegistersAt r x.time) (liveOwnedAt r q x.time) base x.time)⟩
          have hchoice : ReferenceCollectionSegmentExtraction.choice x = some c := by
            unfold ReferenceCollectionSegmentExtraction.choice
            rw [ite_eq_right hselected, hcut, ho]
            rfl
          have hcredit := collection_start_mass (liveRegistersAt r x.time)
            (liveOwnedAt r q x.time) base x.time hmass hprevious
          have hledger : c.preLedger = sharedLedger
              (CoordinatorStartRoundCutoffDispatch.collectionStartLedger
                (liveRegistersAt r x.time) (liveOwnedAt r q x.time) base x.time) := by
            dsimp only [c]
            rw [hcandidate]
            rfl
          have ht := collection_tail_mass x c hchoice (by
            intro a cutoff current hc hq
            rw [hledger] at hc hq ⊢
            obtain ⟨hcurrent, hfrozen, hlast, _hprevious⟩ := hcredit a cutoff current hc hq
            exact ⟨hcurrent, hfrozen, hlast⟩) (hreply c hchoice)
          split at ht <;> simp_all only [c, implies_true, true_and]
          intro a cut current hc hq
          exact (ht a cut current hc hq).2
    | collection old ledger saved =>
        by_cases hcutoff : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
        · let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
          let clock := collectionClock old ledger saved cutoff
          have hcut : (prepare x).coordinator = .collection old ledger clock cutoff
              (CoordinatorRoundDispatch.dispatchCollection (collectionInput x old ledger clock cutoff)) := by
            rw [hactual]
            simp only [dispatch, hconfiguration, dite_eq_left hcutoff, CoordinatorRoundDispatch.dispatch]
            rfl
          rw [hcut]
          cases ho : CoordinatorRoundDispatch.dispatchCollection
              (collectionInput x old ledger clock cutoff)
          all_goals try trivial
          case continuing core snapshot hcontinue selected =>
            let c : ReferenceCollectionSegmentExtraction.Choice rate :=
              ⟨old, ledger, snapshot.clockStarted,
                CoordinatorCollectionInteractive.PreObservationInputs.weights
                  (collectionInput x old ledger clock cutoff)
                  snapshot.inputsValid.ledger_valid snapshot.inputsValid.assignment_eq, none⟩
            have hchoice : ReferenceCollectionSegmentExtraction.choice x = some c := by
              unfold ReferenceCollectionSegmentExtraction.choice
              rw [ite_eq_right hselected, hcut, ho]
              rfl
            have ht := collection_tail_mass x c hchoice (by
              intro a cut current hc hq
              obtain ⟨hmass, hfrozen, hlast, _hprevious⟩ :=
                hcollection old ledger saved hconfiguration a cut current hc hq
              exact ⟨hmass, hfrozen, hlast⟩) (hreply c hchoice)
            split at ht <;> simp_all only [c, implies_true, true_and]
            intro a cut current hc hq
            exact (ht a cut current hc hq).2
          case laterChosen core consistent started hstart instruction hinstruction output hlocal
              clockData installed selected =>
            have hprovenance := ReferenceLaterInstallationProvenance.dispatch_laterChosen_provenance x
            rw [← hactual, hcut, ho] at hprovenance
            obtain ⟨hinstalled, _hpayload, _hsigma, _hdown⟩ := hprovenance
            have fields := CoordinatorRoundDispatch.collectionOperationLedger_fields
              (collectionInput x old ledger clock cutoff) core.payload_n_eq
            obtain ⟨_hassignment, _hstartSigma, _hcut, _hfreeze, _hbase, _hpending,
              hcutoffRegisters, hcurrentRegisters, hincrement, _hother⟩ := fields
            have htime := later_instruction_time x old ledger clock cutoff core
              started instruction hstart hinstruction
            have hoperation : ∀ (a : Fin p.K) (c : CoordinatorCollectionLedger.CutoffRegister)
                (q : CoordinatorCollectionLedger.CurrentRegister),
                (CoordinatorRoundDispatch.collectionOperationLedger
                  (collectionInput x old ledger clock cutoff) core.payload_n_eq).cutoffRegisters a =
                    some c →
                (CoordinatorRoundDispatch.collectionOperationLedger
                  (collectionInput x old ledger clock cutoff) core.payload_n_eq).currentRegisters a =
                    some q →
                c.score + (CoordinatorRoundDispatch.collectionOperationLedger
                  (collectionInput x old ledger clock cutoff) core.payload_n_eq).increment a +
                    q.queue ≤ instruction.time.val * D p := by
              intro a c q hc hq
              rw [hcutoffRegisters] at hc
              rw [hcurrentRegisters] at hq
              rw [hincrement, htime]
              exact (hcollection old ledger saved hconfiguration a c q hc hq).1
            obtain ⟨_hqueues, hmass, _hfollowers, _hdownCredit⟩ :=
              later_installation_mass output clockData hoperation
            subst installed
            have hsigma : (CoordinatorAssignmentRegisterInstall.installLater
                output clockData).registers.payload.sigma.val = x.time.val := by
              change output.payload.sigma.val = x.time.val
              rw [output.payload_start, htime]
            have ht := live_tail_mass x
              (CoordinatorAssignmentRegisterInstall.installLater output clockData).registers
              (CoordinatorAssignmentRegisterInstall.installLater output clockData).ownedRegisters
              (CoordinatorAssignmentRegisterInstall.installLater output clockData).retainedBaseScore
              started (by
                intro j
                exact (hmass j).trans_eq (congrArg (fun n : ℕ => n * D p) hsigma))
            split at ht <;> simp_all only [implies_true, and_true]
        · have hcut : (prepare x).coordinator = .invalidCollectionCutoff := by
            rw [hactual]
            simp only [dispatch, hconfiguration, dite_eq_right hcutoff]
          rw [hcut]
          trivial
    | dagger =>
        have hcut : (prepare x).coordinator = .dagger := by
          rw [hactual]
          simp only [dispatch, hconfiguration]
        rw [hcut]
        trivial

private theorem complete_record_row
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length) :
    (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[k.val].input.row =
      source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) := by
  cases hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h with
  | none =>
      have hlength := k.isLt
      simp only [ReferenceCompletePhysicalHistory.completeSuffixRecords, hlaunch,
        dite_true, List.length_nil] at hlength
      omega
  | some active =>
      have hrecords := ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
        rate source rewards C_star C_h active hlaunch
      let start := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
      have span : start + (p.T - start) ≤ p.T := by
        have hs := ReferenceCompletePhysicalHistory.physicalStart_le_T
          rate source rewards C_star C_h
        dsimp only [start]
        omega
      let execution := ReferenceActivePhysicalHorizon.run active source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start (p.T - start)
        span (ReferenceCompletePhysicalHistory.activeMode_of_launch_eq_some
          rate source rewards C_star C_h active hlaunch)
      have hrun : ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h = execution.records := hrecords
      have hmem : (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h)[k.val] ∈ execution.records := by
        rw [← hrun]
        exact List.getElem_mem k.isLt
      have hdata := ReferenceActivePhysicalHorizon.run_record_inputs active source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
        start (p.T - start) span _ _ hmem
      exact congrArg₂ (fun rows selected => rows selected) hdata.1 hdata.2.1

private theorem payload_down_start (P : Payload rate) (i : Fin (p.m - 1)) :
    ActiveFollowerDownAcceptance.downStart p rate (P.downRecord i) = P.sigma := by
  apply Fin.ext
  change P.sigma.val + 1 - 1 = P.sigma.val
  exact Nat.add_sub_cancel _ _

private theorem no_new_down_mass
    (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (activation : ReferencePrelaunchFollower.Activation p) (t : Fin p.T)
    (active : activation.val ≤ t.val + 1) (arm : Fin p.K)
    (observation : ReferencePrelaunchFollower.Observation p)
    (choice post : ReferencePrelaunchFollower.State p rate.eta)
    (hrecord : (recordFollower view i row activation t active arm observation choice).result = .ok post)
    (hkeep : choice.status = .unoccupied → ReferenceFollowerReplyChronology.reply post =
      ReferenceFollowerReplyChronology.reply choice)
    (u beta : ℕ)
    (hcredit : beta + choice.S + choice.backlog ≤ min t.val (u - 1) * D p)
    (hdelta : choice.delta ≤ D p)
    (hcutoff : choice.status = .unoccupied ↔ u ≤ t.val + 1) :
    beta + post.S + post.backlog ≤ min (t.val + 1) (u - 1) * D p ∧ post.delta ≤ D p := by
  by_cases hunoccupied : choice.status = .unoccupied
  · have hframe := hkeep hunoccupied
    have hS := congrArg (fun r => r.2.1) hframe
    have hq := congrArg (fun r => r.2.2.2) hframe
    have hd := congrArg (fun r => r.2.2.1) hframe
    change post.S = choice.S at hS
    change post.backlog = choice.backlog at hq
    change post.delta = choice.delta at hd
    rw [hS, hq, hd]
    exact ⟨hcredit.trans (Nat.mul_le_mul_right (D p)
      (min_le_min (Nat.le_succ _) le_rfl)), hdelta⟩
  · simp only [recordFollower, dite_eq_right hunoccupied] at hrecord
    rw [DeclaredFollowerLocalRound.recordOrServiceThenDown, dite_eq_right hunoccupied] at hrecord
    cases hs : ActiveFollowerQueueOperation.checkedService rate.eta rate.sourceCap rate.n
        rate.n_scale i row activation t observation choice with
    | failure => simp only [hs] at hrecord; cases hrecord
    | success result =>
        simp only [hs, Except.ok.injEq] at hrecord
        subst post
        exact ReferenceAssignmentFollowerMassSteps.service_mass_of_choice_cutoff
          i row activation t observation choice result u beta hcredit hcutoff

private theorem follower_round_mass
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
    let bits := FollowerCutoffScan.completeRowProposalBit p rate.eta.val
      (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source))
    ∀ (k : Fin R.length),
    (∀ (b : Fin R.length), b.val ≤ k.val → ∀ P : Payload rate,
      ReferenceAssignmentPayloadPersistence.InstallationBirth R[b.val] P →
      ∃ beta : Fin (p.m - 1) → ℕ, installedBaseScore R[b.val] = some beta ∧
        ∀ i, beta i + (P.downRecord i).val.q ≤ ((P.downRecord i).val.sigma - 1) * D p) →
    (∀ (i : Fin (p.m - 1)) (F : ReferencePrelaunchFollower.State p rate.eta)
      (memory : ActiveFollowerLifecycle.LocalMemory p) M,
      R[k.val].input.state.followers i = .ordinary F memory → F.lastDown = some M →
      ∃ (b j : Fin R.length) (P : Payload rate) (beta : Fin (p.m - 1) → ℕ),
        b.val ≤ j.val ∧ j.val < k.val ∧
        ReferenceAssignmentPayloadPersistence.InstallationBirth R[b.val] P ∧
        installedBaseScore R[b.val] = some beta ∧
        ReferenceAcceptedUpFollowerHistory.RetainedDown R[j.val] i M ∧ M = P.downRecord i ∧
        beta i + F.S + F.backlog ≤ min R[k.val].input.time.val
          (FollowerCutoffScan.firstCutoff p rate.eta.val P.sigma bits - 1) * D p ∧ F.delta ≤ D p) →
    ∀ (i : Fin (p.m - 1)) (next : ReferencePrelaunchFollower.State p rate.eta)
      (nextMemory : ActiveFollowerLifecycle.LocalMemory p) M,
      R[k.val].output.next.followers i = .ordinary next nextMemory → next.lastDown = some M →
      ∃ (b j : Fin R.length) (P : Payload rate) (beta : Fin (p.m - 1) → ℕ),
        b.val ≤ j.val ∧ j.val ≤ k.val ∧
        ReferenceAssignmentPayloadPersistence.InstallationBirth R[b.val] P ∧
        installedBaseScore R[b.val] = some beta ∧
        ReferenceAcceptedUpFollowerHistory.RetainedDown R[j.val] i M ∧ M = P.downRecord i ∧
        beta i + next.S + next.backlog ≤ min (R[k.val].input.time.val + 1)
          (FollowerCutoffScan.firstCutoff p rate.eta.val P.sigma bits - 1) * D p ∧
        next.delta ≤ D p := by
  dsimp only
  intro k hbirths hfollowers i next nextMemory M hnext hnextDown
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
  let record := R[k.val]
  let input := record.input
  let prepared := (prepare input).followers.followers i
  let view := (prepare input).coordinator.downView
  let observation := (prepare input).feedback.observations
    (PublicDiscreteDraws.followerPlayer p.two_le_m i)
  have hnext' : (finishFollower view prepared observation).configuration =
      .ordinary next nextMemory := by
    rw [record.output_eq] at hnext
    exact hnext
  obtain ⟨choice, choiceMemory, post, hchoice, hrecord, hrelease,
    hfinishInput, hfinishDown⟩ :=
    ReferenceFollowerReplyChronology.finishFollower_ordinary_inversion
      view prepared observation next nextMemory hnext'
  have hprepareEq : prepared = DeclaredFollowerLocalRound.prepare rate i input.row
      (input.state.activations i) input.time (input.active i) (input.state.followers i) :=
    (prepare input).followers.followers_eq i
  rw [hprepareEq] at hchoice
  obtain ⟨before, memory, hinput, hstart, hprepareFrame, _hprepareUnoccupied⟩ :=
    ReferenceFollowerReplyChronology.prepare_ordinary_inversion i input.row
      (input.state.activations i) input.time (input.active i) (input.state.followers i)
      choice choiceMemory hchoice
  have halignment := (prepare input).follower_alignment i
  have hrecord' : (recordFollower view i input.row (input.state.activations i)
      input.time (input.active i) prepared.arm observation choice).result = .ok post := by
    simpa only [prepared, halignment.1, halignment.2.1, halignment.2.2.1, halignment.2.2.2] using hrecord
  have hrelease' : DeclaredFollowerLocalRound.releaseAndFinish rate i input.row input.time
      observation choice choiceMemory post = .ok (next, nextMemory) := by
    simpa only [prepared, halignment.1, halignment.2.1, halignment.2.2.1] using hrelease
  have hfinishInput' : (finishFollower view prepared observation).downInput =
      (recordFollower view i input.row (input.state.activations i) input.time
        (input.active i) prepared.arm observation choice).downInput := by
    simpa only [prepared, halignment.1, halignment.2.1, halignment.2.2.1, halignment.2.2.2] using hfinishInput
  have hfinishDown' : (finishFollower view prepared observation).down =
      (recordFollower view i input.row (input.state.activations i) input.time
        (input.active i) prepared.arm observation choice).down := by
    simpa only [prepared, halignment.1, halignment.2.1, halignment.2.2.1, halignment.2.2.2] using hfinishDown
  have hframe := ReferenceFollowerReplyChronology.releaseAndFinish_frame
    i input.row input.time observation choice post next choiceMemory nextMemory hrelease'
  have hnextLast : next.lastDown = post.lastDown := congrArg Prod.fst hframe.1
  have hnextS : next.S = post.S := congrArg (fun r => r.2.1) hframe.1
  have hnextDelta : next.delta = post.delta := congrArg (fun r => r.2.2.1) hframe.1
  have hnextQueue : next.backlog = post.backlog := congrArg (fun r => r.2.2.2) hframe.1
  have hrow := complete_record_row rate rewards C_star C_h source k
  obtain hpostLast | ⟨logged, cut, raw, accepted, scan, registers, lastService,
      hdownInput, hdown, _hcut, haccepted, _hstrict, hacceptedLast⟩ :=
    ReferenceFollowerReplyChronology.recordFollower_ordinary_inversion
      view i input.row (input.state.activations i) input.time (input.active i)
      prepared.arm observation choice post hrecord'
  · have hbeforeLast : before.lastDown = some M :=
      (congrArg Prod.fst hprepareFrame).symm.trans
        (hpostLast.1.symm.trans (hnextLast.symm.trans hnextDown))
    obtain ⟨b, j, P, beta, hbj, hjk, hbirth, hbase, hretained, hmessage, hmass, hdelta⟩ :=
      hfollowers i before memory M hinput hbeforeLast
    have hphase := ReferenceCompleteFollowerCutoffPhase.complete_ordinary_follower_phase
      rate rewards C_star C_h source k i before memory hinput M hbeforeLast
    have htoken := ReferenceCompleteFollowerCutoffPhase.complete_ordinary_follower_token
      rate rewards C_star C_h source k i before memory hinput
    have hchoicePhase := ReferenceAssignmentFollowerMassSteps.start_round_cutoff_status
      input.time input.row before choice memory choiceMemory M hbeforeLast hphase htoken hstart
    have hchoiceS : choice.S = before.S := congrArg (fun r => r.2.1) hprepareFrame
    have hchoiceDelta : choice.delta = before.delta := congrArg (fun r => r.2.2.1) hprepareFrame
    have hchoiceQueue : choice.backlog = before.backlog := congrArg (fun r => r.2.2.2) hprepareFrame
    have hstartP : ActiveFollowerDownAcceptance.downStart p rate M = P.sigma := by
      rw [hmessage]
      exact payload_down_start P i
    rw [hstartP] at hchoicePhase
    have hpost := no_new_down_mass view i input.row (input.state.activations i) input.time
      (input.active i) prepared.arm observation choice post hrecord'
      (fun hu => (hpostLast.2 hu).1)
      (FollowerCutoffScan.firstCutoff p rate.eta.val P.sigma
        (FollowerCutoffScan.completeRowProposalBit p rate.eta.val input.row)) (beta i)
      (by rw [hchoiceS, hchoiceQueue, hrow]; exact hmass)
      (by rw [hchoiceDelta]; exact hdelta) hchoicePhase
    refine ⟨b, j, P, beta, hbj, hjk.le, hbirth, hbase, hretained, hmessage, ?_, ?_⟩
    · rw [hnextS, hnextQueue, ← hrow]
      exact hpost.1
    · rw [hnextDelta]
      exact hpost.2
  · have hacceptedEq : accepted = M :=
      Option.some.inj (hacceptedLast.symm.trans (hnextLast.symm.trans hnextDown))
    subst accepted
    have hdiagnosticInput : (record.output.followers i).downInput = some logged := by
      rw [record.output_eq]
      exact hfinishInput'.trans hdownInput
    have hdiagnosticDown : (record.output.followers i).down = some cut := by
      rw [record.output_eq]
      exact hfinishDown'.trans hdown
    have hretained : ReferenceAcceptedUpFollowerHistory.RetainedDown record i M :=
      ⟨logged, cut, post, raw, scan, registers, lastService,
        hdiagnosticInput, hdiagnosticDown, haccepted⟩
    obtain ⟨b, P, hbk, hbirth, hmessage⟩ :=
      complete_retained_down_birth rate rewards C_star C_h source k i M hretained
    obtain ⟨beta, hbase, hcredit⟩ := hbirths b hbk P hbirth
    have hdownCredit : beta i + M.val.q ≤ (M.val.sigma - 1) * D p := by
      rw [hmessage]
      exact hcredit i
    obtain ⟨_hlast, hmass, hdelta, _hphase⟩ :=
      ReferenceAssignmentFollowerMassSteps.record_accepted_down_mass record i logged cut post raw
        M scan registers lastService (beta i) hdownCredit hdiagnosticInput hdiagnosticDown haccepted
    have hstartP : ActiveFollowerDownAcceptance.downStart p rate M = P.sigma := by
      rw [hmessage]
      exact payload_down_start P i
    rw [hstartP] at hmass
    refine ⟨b, k, P, beta, hbk, le_rfl, hbirth, hbase, hretained, hmessage, ?_, ?_⟩
    · rw [hnextS, hnextQueue, ← hrow]
      exact hmass
    · rw [hnextDelta]
      exact hdelta

private theorem connected_first_input
    {initial final : State p rate} {records : List (RoundRecord (p := p) (rate := rate))}
    (hconnected : ReferenceActivePhysicalHorizon.Connected initial records final)
    (h : 0 < records.length) : records[0].input.state = initial := by
  cases records with
  | nil => simp only [List.length_nil] at h; omega
  | cons record rest => exact hconnected.1

private theorem connected_succ_input
    {initial final : State p rate} {records : List (RoundRecord (p := p) (rate := rate))}
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

private theorem complete_prefix_mass
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
    let bits := FollowerCutoffScan.completeRowProposalBit p rate.eta.val
      (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source))
    ∀ (k : Fin R.length),
    (∀ (b : Fin R.length), b.val < k.val → ∀ P : Payload rate,
      ReferenceAssignmentPayloadPersistence.InstallationBirth R[b.val] P →
      ∃ beta : Fin (p.m - 1) → ℕ, installedBaseScore R[b.val] = some beta ∧
        (∀ a : Fin p.K, P.queues a ≤ P.sigma.val * D p) ∧
        (∀ i : Fin (p.m - 1), beta i + P.queues (P.assignment.assigned i) ≤ P.sigma.val * D p) ∧
        (∀ i : Fin (p.m - 1), beta i + (P.downRecord i).val.q ≤
          ((P.downRecord i).val.sigma - 1) * D p)) ∧
    (match R[k.val].input.state.coordinator with
    | .live r q _ =>
        (∀ j : CanonicalFastSampling.FastArm r.payload.slowSet,
          r.complementScores j + q.queue j ≤ R[k.val].input.time.val * D p) ∧
        q.previousServiceDomainValid
    | .collection _ l _ =>
        ∀ (a : Fin p.K) (c : CoordinatorCollectionLedger.CutoffRegister)
          (q : CoordinatorCollectionLedger.CurrentRegister),
          l.cutoffRegisters a = some c → l.currentRegisters a = some q →
          c.score + l.increment a + q.queue ≤ R[k.val].input.time.val * D p ∧
            c.score + c.queue ≤ (l.cutoff - 1) * D p ∧
            c.lastService ≤ D p ∧ q.lastService ≤ D p
    | .first => True
    | .dagger => True) ∧
    (∀ (i : Fin (p.m - 1)) (F : ReferencePrelaunchFollower.State p rate.eta)
      (memory : ActiveFollowerLifecycle.LocalMemory p) M,
      R[k.val].input.state.followers i = .ordinary F memory → F.lastDown = some M →
      ∃ (b j : Fin R.length) (P : Payload rate) (beta : Fin (p.m - 1) → ℕ),
        b.val ≤ j.val ∧ j.val < k.val ∧
        ReferenceAssignmentPayloadPersistence.InstallationBirth R[b.val] P ∧
        installedBaseScore R[b.val] = some beta ∧
        ReferenceAcceptedUpFollowerHistory.RetainedDown R[j.val] i M ∧ M = P.downRecord i ∧
        beta i + F.S + F.backlog ≤ min R[k.val].input.time.val
          (FollowerCutoffScan.firstCutoff p rate.eta.val P.sigma bits - 1) * D p ∧ F.delta ≤ D p) := by
  dsimp only
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
  let bits := FollowerCutoffScan.completeRowProposalBit p rate.eta.val
    (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source))
  intro k
  cases hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h with
  | none =>
      have hlength := k.isLt
      simp only [ReferenceCompletePhysicalHistory.completeSuffixRecords, hlaunch,
        dite_true, List.length_nil] at hlength
      omega
  | some active =>
      have hc := (ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
        rate source rewards C_star C_h).mp (by rw [hlaunch]; rfl)
      let initial := ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hc
      let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
        rate source rewards C_star C_h hc
      have hcanonical := ReferenceFirstLaunchNumericalCell.correctedLaunch_eq_some_launchState
        rate source rewards C_star C_h hc
      have hconnected := ReferenceCompletePhysicalHistory.completeSuffix_connected_on_launch
        rate source rewards C_star C_h initial hcanonical
      have hfold : ∀ n (hn : n < R.length),
          (∀ (b : Fin R.length), b.val < n → ∀ P : Payload rate,
            ReferenceAssignmentPayloadPersistence.InstallationBirth R[b.val] P →
            ∃ beta : Fin (p.m - 1) → ℕ, installedBaseScore R[b.val] = some beta ∧
              (∀ a : Fin p.K, P.queues a ≤ P.sigma.val * D p) ∧
              (∀ i : Fin (p.m - 1), beta i + P.queues (P.assignment.assigned i) ≤ P.sigma.val * D p) ∧
              (∀ i : Fin (p.m - 1), beta i + (P.downRecord i).val.q ≤
                ((P.downRecord i).val.sigma - 1) * D p)) ∧
          (match R[n].input.state.coordinator with
          | .live r q _ =>
              (∀ j : CanonicalFastSampling.FastArm r.payload.slowSet,
                r.complementScores j + q.queue j ≤ R[n].input.time.val * D p) ∧
              q.previousServiceDomainValid
          | .collection _ l _ =>
              ∀ (a : Fin p.K) (c : CoordinatorCollectionLedger.CutoffRegister)
                (q : CoordinatorCollectionLedger.CurrentRegister),
                l.cutoffRegisters a = some c → l.currentRegisters a = some q →
                c.score + l.increment a + q.queue ≤ R[n].input.time.val * D p ∧
                  c.score + c.queue ≤ (l.cutoff - 1) * D p ∧
                  c.lastService ≤ D p ∧ q.lastService ≤ D p
          | .first => True
          | .dagger => True) ∧
          (∀ (i : Fin (p.m - 1)) (F : ReferencePrelaunchFollower.State p rate.eta)
            (memory : ActiveFollowerLifecycle.LocalMemory p) M,
            R[n].input.state.followers i = .ordinary F memory → F.lastDown = some M →
            ∃ (b j : Fin R.length) (P : Payload rate) (beta : Fin (p.m - 1) → ℕ),
              b.val ≤ j.val ∧ j.val < n ∧
              ReferenceAssignmentPayloadPersistence.InstallationBirth R[b.val] P ∧
              installedBaseScore R[b.val] = some beta ∧
              ReferenceAcceptedUpFollowerHistory.RetainedDown R[j.val] i M ∧ M = P.downRecord i ∧
              beta i + F.S + F.backlog ≤ min R[n].input.time.val
                (FollowerCutoffScan.firstCutoff p rate.eta.val P.sigma bits - 1) * D p ∧ F.delta ≤ D p) := by
        intro n
        induction n with
        | zero =>
            intro hn
            have hstate := connected_first_input hconnected hn
            refine ⟨?_, ?_, ?_⟩
            · intro b hb
              omega
            · rw [hstate, seed.coordinatorFirst]
              trivial
            · intro i F memory M hconfiguration hdown
              rw [hstate] at hconfiguration
              have hF := (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
                ((seed.configuration i).symm.trans hconfiguration)).1
              subst F
              rw [seed.lastDown_none i] at hdown
              cases hdown
        | succ n ih =>
            intro hn
            have hnprev : n < R.length := by omega
            let prior : Fin R.length := ⟨n, hnprev⟩
            obtain ⟨hbirths, hcoord, hfollowers⟩ := ih hnprev
            have hlive : ∀ (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
                (q : CoordinatorLiveServiceFinish.OwnedRegisters r) (base : Fin (p.m - 1) → ℕ),
                R[n].input.state.coordinator = .live r q base →
                (∀ j : CanonicalFastSampling.FastArm r.payload.slowSet,
                  r.complementScores j + q.queue j ≤ R[n].input.time.val * D p) ∧
                q.previousServiceDomainValid := by
              intro r q base hconfiguration
              have h := hcoord
              rw [hconfiguration] at h
              exact h
            have hcollection : ∀ (P : Payload rate) (l : Ledger rate)
                (saved : Option (Fin p.T × Bool)),
                R[n].input.state.coordinator = .collection P l saved →
                ∀ (a : Fin p.K) (c : CoordinatorCollectionLedger.CutoffRegister)
                  (q : CoordinatorCollectionLedger.CurrentRegister),
                  l.cutoffRegisters a = some c → l.currentRegisters a = some q →
                  c.score + l.increment a + q.queue ≤ R[n].input.time.val * D p ∧
                    c.score + c.queue ≤ (l.cutoff - 1) * D p ∧
                    c.lastService ≤ D p ∧ q.lastService ≤ D p := by
              intro P l saved hconfiguration
              have h := hcoord
              rw [hconfiguration] at h
              exact h
            have hcurrentBirth := record_birth_mass_of_ready_credit R[n] (by
              intro P l saved hconfiguration a c q hc hq
              exact (hcollection P l saved hconfiguration a c q hc hq).1)
            have haugmented : ∀ (b : Fin R.length), b.val ≤ n → ∀ P : Payload rate,
                ReferenceAssignmentPayloadPersistence.InstallationBirth R[b.val] P →
                ∃ beta : Fin (p.m - 1) → ℕ, installedBaseScore R[b.val] = some beta ∧
                  (∀ a : Fin p.K, P.queues a ≤ P.sigma.val * D p) ∧
                  (∀ i : Fin (p.m - 1), beta i + P.queues (P.assignment.assigned i) ≤ P.sigma.val * D p) ∧
                  (∀ i : Fin (p.m - 1), beta i + (P.downRecord i).val.q ≤
                    ((P.downRecord i).val.sigma - 1) * D p) := by
              intro b hb P hbirth
              by_cases hstrict : b.val < n
              · exact hbirths b hstrict P hbirth
              · have heq : b.val = n := by omega
                subst heq
                exact hcurrentBirth P hbirth
            have hreply : ∀ (c : ReferenceCollectionSegmentExtraction.Choice rate),
                ReferenceCollectionSegmentExtraction.choice R[n].input = some c →
                ∀ (i : Fin (p.m - 1)) (U : ReferenceCollectionPhaseHistory.UpRecord p rate),
                  ReferenceCollectionPhaseHistory.AcceptedUp R[n].input i U →
                  c.preLedger.baseScore i + U.val.S + U.val.q ≤ (c.preLedger.cutoff - 1) * D p ∧
                    U.val.delta ≤ D p := by
              intro c hchoice i U haccepted
              apply complete_accepted_up_mass_of_prefix_credit
                rate rewards C_star C_h source prior c hchoice i U ?_ haccepted
              intro F memory hconfiguration M hdown
              obtain ⟨b, j, P, beta, hbj, hjn, hbirth, hbase, _hretained, hmessage, hmass, hdelta⟩ :=
                hfollowers i F memory M hconfiguration hdown
              exact ⟨b, P, beta, hbj.trans_lt hjn, hbirth, hbase, hmessage, hmass, hdelta⟩
            have hcoordNext := coordinator_round_mass R[n].input hlive hcollection hreply
            have houtput : R[n].output.next.coordinator = (prepare R[n].input).observeCoordinator.configuration := by
              rw [R[n].output_eq]
              rfl
            rw [← houtput] at hcoordNext
            have hstate := connected_succ_input hconnected n hn
            have htime : R[n + 1].input.time.val = R[n].input.time.val + 1 := by
              have hprev := ReferenceAssignmentFollowerMassSteps.complete_record_time
                rate rewards C_star C_h source prior
              have hnextTime := ReferenceAssignmentFollowerMassSteps.complete_record_time
                rate rewards C_star C_h source ⟨n + 1, hn⟩
              change R[n].input.time.val = _ + n at hprev
              change R[n + 1].input.time.val = _ + (n + 1) at hnextTime
              omega
            refine ⟨?_, ?_, ?_⟩
            · intro b hb P hbirth
              exact haugmented b (by omega) P hbirth
            · rw [hstate, htime]
              cases hconfiguration : R[n].output.next.coordinator <;>
                simp only [hconfiguration] at hcoordNext ⊢
              all_goals exact hcoordNext
            · intro i F memory M hconfiguration hdown
              have hout : R[n].output.next.followers i = .ordinary F memory := by
                rw [← hstate]
                exact hconfiguration
              obtain ⟨b, j, P, beta, hbj, hjn, hbirth, hbase, hretained, hmessage, hmass, hdelta⟩ :=
                follower_round_mass rate rewards C_star C_h source prior (by
                  intro b hb P hbirth
                  obtain ⟨beta, hbase, _hqueues, _hassigned, hcredit⟩ := haugmented b hb P hbirth
                  exact ⟨beta, hbase, hcredit⟩) hfollowers i F memory M hout hdown
              change j.val ≤ n at hjn
              refine ⟨b, j, P, beta, hbj, by omega, hbirth, hbase, hretained, hmessage, ?_, hdelta⟩
              rw [htime]
              exact hmass
      exact hfold k.val k.isLt

/-- Every installation on the complete original suffix has one literal base
witness satisfying all-arm queue credit and the coupled assigned/DOWN credit.
No successful-run, reply-credit or birth-history family is a theorem input. -/
theorem complete_assignment_birth_mass
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (P : Payload rate)
    (hbirth : ReferenceAssignmentPayloadPersistence.InstallationBirth
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val] P) :
    ∃ beta : Fin (p.m - 1) → ℕ,
      installedBaseScore (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val] = some beta ∧
      (∀ a : Fin p.K, P.queues a ≤ P.sigma.val * D p) ∧
      (∀ i : Fin (p.m - 1), beta i + P.queues (P.assignment.assigned i) ≤ P.sigma.val * D p) ∧
      (∀ i : Fin (p.m - 1), beta i + (P.downRecord i).val.q ≤
        ((P.downRecord i).val.sigma - 1) * D p) := by
  obtain ⟨_hhistory, hcoordinator, _hfollowers⟩ :=
    complete_prefix_mass rate rewards C_star C_h source k
  apply record_birth_mass_of_ready_credit _ ?_ P hbirth
  intro old l saved hconfiguration a c q hc hq
  rw [hconfiguration] at hcoordinator
  exact (hcoordinator a c q hc hq).1

/-- The all-arm queue projection uses the witness from the same joint birth
theorem and has exactly its common telescope. -/
theorem complete_assignment_birth_queue_bound
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (P : Payload rate)
    (hbirth : ReferenceAssignmentPayloadPersistence.InstallationBirth
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val] P) :
    ∀ a : Fin p.K, P.queues a ≤ P.sigma.val * D p := by
  obtain ⟨_beta, _hbase, hqueues, _hassigned, _hdown⟩ :=
    complete_assignment_birth_mass rate rewards C_star C_h source k P hbirth
  exact hqueues

end Bandits.Support.ReferenceAssignmentMassComposer

end
