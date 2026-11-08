/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCompleteEpisodeAnchorOrigin
public import Bandits.Support.ReferenceCompleteCollectionAssignedScoreSpan

/-!
# Installation scores within their actual episode

Sources: `sources/zip4/manuscript/04_slow_fast_learner.tex:96-188,219-243`
and `sources/zip4/manuscript/06_interruptions.tex:9-100,246-299,355-390`.

The comparison uses the whole literal installation score readout. The two
calendar intervals are installation to cutoff and cutoff to the next start;
the latter is clipped at the old grid boundary. No physical/logical score
identification, sampler feasibility, or regret assertion is made here.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ReferenceCompleteInstallationEpisodeScoreSpan

open ConstructorDimensions
open ReferenceActivePhysicalStep
open ReferenceActivePhysicalHorizon
open ReferenceAssignmentPayloadPersistence
open ReferenceCompletePhysicalHistory
open ReferenceCompleteLiveComplementScoreSpan
open ReferenceCompleteEpisodeAnchorOrigin
open CoordinatorCollectionLedger
open CoordinatorRoundDispatch
open CoordinatorAssignmentRegisterInstall

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

/-- Retained source registers at the cutoff: complement entries are already
known and retain the same installation vector throughout collection. -/
private def cutoffFrame
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (P : Payload rate) (l : Ledger rate) : Prop :=
  ∃ birth, birth ∈ records ∧ InstallationBirth birth P ∧
    ∃ z : Fin p.K → ℕ, installationScoreVector birth P z ∧
      ∀ j : CanonicalFastSampling.FastArm P.slowSet,
        ∃ cut : CutoffRegister, ∃ current : CurrentRegister,
          l.cutoffRegisters j.1 = some cut ∧
          l.currentRegisters j.1 = some current ∧
          z j.1 ≤ cut.score ∧
          cut.score ≤ z j.1 + (4 * rate.n) * (l.cutoff - (P.sigma.val + 1))

private theorem checked_round_cutoff_frame
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (P : Payload rate) (l started decoded finished : Ledger rate)
    (input : CollectionCheckedExecution.RoundInput (p := p) (eta := rate.eta.val))
    (hframe : cutoffFrame records P l)
    (hstart : startRound l (sourceRound input.round) input.enabled input.raw = .success started)
    (hdecode : decodeUp started input.selectedFollower input.parsed = .success decoded ∨
      decodeUp started input.selectedFollower input.parsed = .rejected decoded)
    (hfinish : finishRound decoded = .success finished) :
    cutoffFrame records P finished := by
  obtain ⟨birth, hmem, hbirth, z, hz, hcuts⟩ := hframe
  refine ⟨birth, hmem, hbirth, z, hz, ?_⟩
  intro j
  obtain ⟨cut, current, hcut, hcurrent, hlo, hhi⟩ := hcuts j
  obtain ⟨hnext, _hinc, _ha, _hs, hcutoff, _hf, hcutFrame⟩ :=
    CollectionKnownQueueContinuation.checkedRound_known_transition
      l started decoded finished input j.1 current hcurrent hstart hdecode hfinish
  refine ⟨cut, _, hcutFrame.trans hcut, hnext, hlo, ?_⟩
  rw [hcutoff]
  exact hhi

private theorem collection_tail_cutoff_frame
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (x : RoundInput p rate) (c : ReferenceCollectionSegmentExtraction.Choice rate)
    (hframe : cutoffFrame records c.payload c.preLedger) :
    match (collectionPostChoice (prepare x)
      c.payload c.preLedger c.started c.weights).configuration with
    | .collection P final _ => cutoffFrame records P final
    | _ => True := by
  unfold collectionPostChoice
  cases hrecord : CoordinatorRecorderComplementBridge.run
      (collectionRecordingInput (prepare x) c.payload c.started c.weights) with
  | none => trivial
  | some recording =>
      dsimp only
      cases hstart : startRound c.preLedger (x.time.val + 1)
          (collectionEnabled c.preLedger x.time)
          (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) with
      | invalid => trivial
      | rejected bad => trivial
      | success started =>
          dsimp only
          unfold collectionFinish
          have hdecodeResult := ReferenceCollectionSegmentExtraction.receiveUp_decode_result x started
          cases hreceive : (receiveUp (prepare x) started).result with
          | invalid => trivial
          | success pair | rejected pair =>
              rcases pair with ⟨decoded, bank⟩
              simp only [hreceive] at hdecodeResult ⊢
              cases hfinish : finishRound decoded with
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
                      have hdecode :
                          decodeUp started input.selectedFollower input.parsed = .success decoded ∨
                          decodeUp started input.selectedFollower input.parsed = .rejected decoded := by
                        first | exact Or.inl hdecodeResult | exact Or.inr hdecodeResult
                      exact checked_round_cutoff_frame records c.payload
                        c.preLedger started decoded finished input hframe hstart hdecode hfinish

private theorem live_tail_no_collection
    (x : RoundInput p rate) (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r) (base : Fin (p.m - 1) → ℕ)
    (started : CoordinatorPhaseClock.StartRoundResult p) :
    match (livePostChoice (prepare x) r q base started).configuration with
    | .collection _ _ _ => False
    | _ => True := by
  unfold livePostChoice
  cases hr : CoordinatorRecorderComplementBridge.run (liveRecordingInput (prepare x) r started) with
  | none => trivial
  | some recording =>
      dsimp only
      cases hs : CoordinatorLiveServiceFinish.servicePass r q recording with
      | error reason => trivial
      | ok serviced =>
          dsimp only
          cases hc : CoordinatorLocalArmChoice.confirmationUpdate r.payload started.pending
              (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
              x.time x.row (prepare x).coordinatorObservation with
          | none => trivial
          | some pending =>
              dsimp only
              cases hf : CoordinatorPhaseClock.finishRound p rate.eta.val x.time
                  started.clock pending x.row with
              | error reason => trivial
              | ok finished => trivial

private theorem cutoff_choice_frame
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (completeSuffixRecords rate source rewards C_star C_h).length)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r) (base : Fin (p.m - 1) → ℕ)
    (hlive : (completeSuffixRecords rate source rewards C_star C_h)[k.val].input.state.coordinator =
      .live r q base)
    (c : ReferenceCollectionSegmentExtraction.Choice rate)
    (hchoice : ReferenceCollectionSegmentExtraction.choice
      (completeSuffixRecords rate source rewards C_star C_h)[k.val].input = some c) :
    cutoffFrame (completeSuffixRecords rate source rewards C_star C_h) c.payload c.preLedger := by
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
      obtain ⟨birth, hb, hbirth, z, hz, _htime, _hsigma, _hcutoff, hscore⟩ :=
        complete_cutoff_complement_score_span rate rewards C_star C_h source k r q base hlive
          _ hchoice
      refine ⟨birth, List.mem_of_mem_take hb, hbirth, z, hz, ?_⟩
      intro j
      obtain ⟨cut, hcutRegister, _heq, hlo, hhi⟩ := hscore j
      refine ⟨cut, ⟨cut.queue, cut.lastService⟩, hcutRegister, ?_, hlo, hhi⟩
      change (sharedLedger ledger).currentRegisters j.1 = _
      rw [hcandidate]
      change Option.map (fun c : CutoffRegister =>
        (⟨c.queue, c.lastService⟩ : CurrentRegister))
        (CoordinatorStartRoundCutoffDispatch.outsideRegisters
          (liveRegistersAt r x.time) (liveOwnedAt r q x.time) j.1) = _
      have hcutRegister' : CoordinatorStartRoundCutoffDispatch.outsideRegisters
          (liveRegistersAt r x.time) (liveOwnedAt r q x.time) j.1 = some cut := by
        rw [hcandidate] at hcutRegister
        exact hcutRegister
      rw [hcutRegister']
      rfl

private theorem coordinator_round_cutoff_frame
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (completeSuffixRecords rate source rewards C_star C_h).length)
    (hcollection : ∀ P l saved,
      (completeSuffixRecords rate source rewards C_star C_h)[k.val].input.state.coordinator =
        .collection P l saved →
      cutoffFrame (completeSuffixRecords rate source rewards C_star C_h) P l) :
    match (prepare (completeSuffixRecords rate source rewards C_star C_h)[k.val].input).observeCoordinator.configuration with
    | .collection P final _ =>
        cutoffFrame (completeSuffixRecords rate source rewards C_star C_h) P final
    | _ => True := by
  classical
  let R := completeSuffixRecords rate source rewards C_star C_h
  let x := R[k.val].input
  change match (prepare x).observeCoordinator.configuration with
    | .collection P final _ => cutoffFrame R P final
    | _ => True
  by_cases hselected : (prepare x).coordinator.selection = none
  · simp only [PreparedRound.observeCoordinator, dite_eq_left hselected]
    cases (prepare x).coordinator <;> trivial
  · simp only [PreparedRound.observeCoordinator, dite_eq_right hselected]
    have hactual : (prepare x).coordinator = ReferenceActivePhysicalStep.dispatch x := rfl
    cases hconfiguration : x.state.coordinator with
    | first =>
        have hcut : (prepare x).coordinator =
            .first (CoordinatorRoundDispatch.dispatchFirst (firstInput x)) := by
          rw [hactual]
          simp only [ReferenceActivePhysicalStep.dispatch, hconfiguration, CoordinatorRoundDispatch.dispatch]
          rfl
        rw [hcut]
        cases ho : CoordinatorRoundDispatch.dispatchFirst (firstInput x)
        all_goals try trivial
        case chosen installed selected =>
          have ht := live_tail_no_collection x installed.registers installed.ownedRegisters
            installed.followerBaseScore installed.startRoundResult
          split at ht <;> simp_all only
    | live r q base =>
        have hcut : (prepare x).coordinator = .live r q base
            (CoordinatorRoundDispatch.dispatchLive (liveInput x r q base)) := by
          rw [hactual]
          simp only [ReferenceActivePhysicalStep.dispatch, hconfiguration, CoordinatorRoundDispatch.dispatch]
          rfl
        rw [hcut]
        cases ho : CoordinatorRoundDispatch.dispatchLive (liveInput x r q base)
        all_goals try trivial
        case continuingChosen dispatched hstart hno selected =>
          have ht := live_tail_no_collection x (liveRegistersAt r x.time)
            (liveOwnedAt r q x.time) base dispatched.startResult
          split at ht <;> simp_all only
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
          have hframe := cutoff_choice_frame rewards C_star C_h source k r q base
            hconfiguration c hchoice
          exact collection_tail_cutoff_frame R x c hframe
    | collection old ledger saved =>
        by_cases hcutoff : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
        · let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
          let clock := collectionClock old ledger saved cutoff
          have hcut : (prepare x).coordinator = .collection old ledger clock cutoff
              (CoordinatorRoundDispatch.dispatchCollection
                (collectionInput x old ledger clock cutoff)) := by
            rw [hactual]
            simp only [ReferenceActivePhysicalStep.dispatch, hconfiguration, dite_eq_left hcutoff,
              CoordinatorRoundDispatch.dispatch]
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
            exact collection_tail_cutoff_frame R x c
              (hcollection old ledger saved hconfiguration)
          case laterChosen core consistent started hstart instruction hinstruction output
              hlocal clockData installed selected =>
            have ht := live_tail_no_collection x installed.registers installed.ownedRegisters
              installed.retainedBaseScore started
            split at ht <;> simp_all only
        · have hcut : (prepare x).coordinator = .invalidCollectionCutoff := by
            rw [hactual]
            simp only [ReferenceActivePhysicalStep.dispatch, hconfiguration, dite_eq_right hcutoff]
          rw [hcut]
          trivial
    | dagger =>
        have hcut : (prepare x).coordinator = .dagger := by
          rw [hactual]
          simp only [ReferenceActivePhysicalStep.dispatch, hconfiguration]
        rw [hcut]
        trivial

private theorem connected_first_input
    {initial final : ReferenceActivePhysicalHorizon.State p rate}
    {records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))}
    (hconnected : ReferenceActivePhysicalHorizon.Connected initial records final)
    (hfirst : 0 < records.length) :
    records[0].input.state = initial := by
  cases records with
  | nil => simp only [List.length_nil] at hfirst; omega
  | cons record rest => exact hconnected.1

private theorem connected_succ_input
    {initial final : ReferenceActivePhysicalHorizon.State p rate}
    {records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))}
    (hconnected : ReferenceActivePhysicalHorizon.Connected initial records final)
    (n : ℕ) (hn : n + 1 < records.length) :
    records[n + 1].input.state = records[n].output.next := by
  induction records generalizing initial n with
  | nil => simp only [List.length_nil] at hn; omega
  | cons record rest ih =>
      cases n with
      | zero =>
          cases rest with
          | nil => simp only [List.length_cons, List.length_nil] at hn; omega
          | cons next tail => exact hconnected.2.1
      | succ n => exact ih hconnected.2 n (by simp only [List.length_cons] at hn; omega)

private theorem complete_collection_cutoff_frame
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (completeSuffixRecords rate source rewards C_star C_h).length) :
    let R := completeSuffixRecords rate source rewards C_star C_h
    ∀ P l saved, R[k.val].input.state.coordinator = .collection P l saved →
      cutoffFrame R P l := by
  classical
  dsimp only
  let R := completeSuffixRecords rate source rewards C_star C_h
  cases hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h with
  | none =>
      have hlength := k.isLt
      simp only [completeSuffixRecords, hlaunch, dite_true, List.length_nil] at hlength
      omega
  | some active =>
      have hc := (ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
        rate source rewards C_star C_h).mp (by rw [hlaunch]; rfl)
      let initial := ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hc
      let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
        rate source rewards C_star C_h hc
      have hcanonical := ReferenceFirstLaunchNumericalCell.correctedLaunch_eq_some_launchState
        rate source rewards C_star C_h hc
      have hconnected := completeSuffix_connected_on_launch
        rate source rewards C_star C_h initial hcanonical
      have hstep : ∀ (n : Fin R.length),
          (∀ P l saved, R[n.val].input.state.coordinator = .collection P l saved →
            cutoffFrame R P l) →
          ∀ P l saved, R[n.val].output.next.coordinator = .collection P l saved →
            cutoffFrame R P l := by
        intro n hin P l saved hout
        have ht := coordinator_round_cutoff_frame rewards C_star C_h source n hin
        have heq : R[n.val].output.next.coordinator =
            (prepare R[n.val].input).observeCoordinator.configuration := by
          rw [R[n.val].output_eq]
          rfl
        rw [← heq, hout] at ht
        exact ht
      have hfold : ∀ n (hn : n < R.length),
          (∀ P l saved, R[n].input.state.coordinator = .collection P l saved →
            cutoffFrame R P l) ∧
          (∀ P l saved, R[n].output.next.coordinator = .collection P l saved →
            cutoffFrame R P l) := by
        intro n
        induction n with
        | zero =>
            intro hn
            have hstate := connected_first_input hconnected hn
            have hin : ∀ P l saved, R[0].input.state.coordinator = .collection P l saved →
                cutoffFrame R P l := by
              intro P l saved hconfiguration
              rw [hstate, seed.coordinatorFirst] at hconfiguration
              cases hconfiguration
            exact ⟨hin, hstep ⟨0, hn⟩ hin⟩
        | succ n ih =>
            intro hn
            obtain ⟨_hin, hout⟩ := ih (by omega)
            have hstate := connected_succ_input hconnected n hn
            have hin : ∀ P l saved, R[n + 1].input.state.coordinator = .collection P l saved →
                cutoffFrame R P l := by
              intro P l saved he
              rw [hstate] at he
              exact hout P l saved he
            exact ⟨hin, hstep ⟨n + 1, hn⟩ hin⟩
      exact (hfold k.val k.isLt).1

/-- The actual collection input retains the installation-relative complement
cutoff bounds, including the known current registers after any collection
round. No successful reconstruction is assumed. -/
theorem complete_collection_input_complement_cutoff_span
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (completeSuffixRecords rate source rewards C_star C_h).length)
    (P : Payload rate) (l : Ledger rate) (saved : Option (Fin p.T × Bool))
    (hinput : (completeSuffixRecords rate source rewards C_star C_h)[k.val].input.state.coordinator =
      .collection P l saved) :
    let R := completeSuffixRecords rate source rewards C_star C_h
    ∃ birth, birth ∈ R ∧ InstallationBirth birth P ∧
      ∃ z : Fin p.K → ℕ, installationScoreVector birth P z ∧
        ∀ j : CanonicalFastSampling.FastArm P.slowSet,
          ∃ cut : CutoffRegister, ∃ current : CurrentRegister,
            l.cutoffRegisters j.1 = some cut ∧
            l.currentRegisters j.1 = some current ∧
            z j.1 ≤ cut.score ∧
            cut.score ≤ z j.1 + (4 * rate.n) * (l.cutoff - (P.sigma.val + 1)) := by
  exact complete_collection_cutoff_frame rewards C_star C_h source k P l saved hinput

private theorem actual_firstChosen_installation_eq
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (installed : CoordinatorAssignmentRegisterInstall.FirstInstallation
      (CoordinatorRoundDispatch.firstLaunchInput (firstInput record.input)))
    (selected : CoordinatorRoundDispatch.ArmSelection installed.registers.payload
      installed.startRoundResult installed.registers.time
      installed.registers.complementWeights record.input.row)
    (hbranch : record.output.preparation.coordinator = .first (.chosen installed selected)) :
    installed = CoordinatorAssignmentRegisterInstall.installFirst
      (CoordinatorRoundDispatch.firstLaunchInput (firstInput record.input)) := by
  have hactual : record.output.preparation.coordinator =
      ReferenceActivePhysicalStep.dispatch record.input := by
    rw [record.output_eq]
    rfl
  have hdispatch := hactual.symm.trans hbranch
  have hstate : record.input.state.coordinator = .first := by
    cases hs : record.input.state.coordinator with
    | first => rfl
    | live r q base =>
        simp only [ReferenceActivePhysicalStep.dispatch, hs] at hdispatch
        cases hround : CoordinatorRoundDispatch.dispatch (.live (liveInput record.input r q base));
          simp [hround] at hdispatch
        all_goals cases hdispatch
    | collection payload ledger saved =>
        by_cases hc : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
        · let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
          let clock := collectionClock payload ledger saved cutoff
          cases hround : CoordinatorRoundDispatch.dispatch
              (.collection (collectionInput record.input payload ledger clock cutoff));
            simp [ReferenceActivePhysicalStep.dispatch, hs, hc, cutoff, clock, hround] at hdispatch
          all_goals cases hdispatch
        · simp [ReferenceActivePhysicalStep.dispatch, hs, hc] at hdispatch
    | dagger => simp [ReferenceActivePhysicalStep.dispatch, hs] at hdispatch
  have hcut := ReferenceActivePhysicalStep.dispatch_first record.input hstate
  rw [hcut] at hdispatch
  have hchosen : CoordinatorRoundDispatch.dispatchFirst (firstInput record.input) =
      .chosen installed selected := by
    injection hdispatch with hchosen
  exact ReferenceActivePhysicalStep.dispatchFirst_chosen_installation
    record.input installed selected hchosen

private theorem installation_time
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (P : Payload rate) (hbirth : InstallationBirth record P) :
    P.sigma.val = record.input.time.val := by
  cases hcoord : record.output.preparation.coordinator with
  | first outcome =>
      cases outcome <;> simp only [InstallationBirth, hcoord] at hbirth
      exact hbirth.2
  | live r q base outcome => simp [InstallationBirth, hcoord] at hbirth
  | collection old ledger clock cutoff outcome =>
      cases outcome <;> simp only [InstallationBirth, hcoord] at hbirth
      exact hbirth.2
  | invalidCollectionCutoff => simp [InstallationBirth, hcoord] at hbirth
  | dagger => simp [InstallationBirth, hcoord] at hbirth

private theorem complete_record_time
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (completeSuffixRecords rate source rewards C_star C_h).length) :
    (completeSuffixRecords rate source rewards C_star C_h)[k.val].input.time.val =
      physicalStart rate source rewards C_star C_h + k.val := by
  have htimes := completeSuffixRecords_time_values rate source rewards C_star C_h
  have hindex : k.val < ((completeSuffixRecords rate source rewards C_star C_h).map
      (fun r => r.input.time.val)).length := by simpa only [List.length_map] using k.isLt
  have hindex' : k.val < (ReferenceActivePhysicalHorizon.calendar
      (physicalStart rate source rewards C_star C_h)
      (p.T - physicalStart rate source rewards C_star C_h)).length := by
    rw [← htimes]
    exact hindex
  have h := congrArg (fun l : List ℕ => l[k.val]?) htimes
  rw [List.getElem?_map, List.getElem?_eq_getElem k.isLt,
    Option.map_some, List.getElem?_eq_getElem hindex'] at h
  exact Option.some.inj (by simpa [ReferenceActivePhysicalHorizon.calendar] using h)

private theorem same_birth_record
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (P : Payload rate)
    (birth : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hmem : birth ∈ completeSuffixRecords rate source rewards C_star C_h)
    (hbirth : InstallationBirth birth P)
    (b : Fin (completeSuffixRecords rate source rewards C_star C_h).length)
    (hb : InstallationBirth (completeSuffixRecords rate source rewards C_star C_h)[b.val] P) :
    birth = (completeSuffixRecords rate source rewards C_star C_h)[b.val] := by
  obtain ⟨j, hj, heq⟩ := List.mem_iff_getElem.mp hmem
  have htimeEq :
      (completeSuffixRecords rate source rewards C_star C_h)[j].input.time.val =
        (completeSuffixRecords rate source rewards C_star C_h)[b.val].input.time.val := by
    calc
      _ = birth.input.time.val := congrArg (fun r => r.input.time.val) heq
      _ = P.sigma.val := (installation_time birth P hbirth).symm
      _ = _ := installation_time _ P hb
  have hjtime := complete_record_time rewards C_star C_h source ⟨j, hj⟩
  have hbtime := complete_record_time rewards C_star C_h source b
  change (completeSuffixRecords rate source rewards C_star C_h)[j].input.time.val =
    physicalStart rate source rewards C_star C_h + j at hjtime
  have hindex : j = b.val := by
    rw [hjtime, hbtime] at htimeEq
    exact Nat.add_left_cancel htimeEq
  subst j
  exact heq.symm

private theorem installation_base_score
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (P : Payload rate) (z : Fin p.K → ℕ) (base : Fin (p.m - 1) → ℕ)
    (hz : installationScoreVector record P z)
    (hbase : ReferenceAssignmentCollectionMassSteps.installedBaseScore record = some base) :
    ∀ i, base i = z (P.assignment.assigned i) := by
  cases hcoord : record.output.preparation.coordinator with
  | first outcome =>
      cases outcome with
      | chosen installed selected =>
          have hinstalled := actual_firstChosen_installation_eq record installed selected hcoord
          simp only [installationScoreVector, hcoord] at hz
          obtain ⟨rfl, rfl, _hcomplement⟩ := hz
          simp only [ReferenceAssignmentCollectionMassSteps.installedBaseScore, hcoord] at hbase
          have hbaseEq := Option.some.inj hbase
          subst base
          cases hinstalled
          exact fun i => CoordinatorAssignmentRegisterInstall.first_follower_base_score _ i
      | choiceDomainFailure installed => simp [installationScoreVector, hcoord] at hz
      | recorderBoundaryFailure installed => simp [installationScoreVector, hcoord] at hz
      | choiceRejected installed => simp [installationScoreVector, hcoord] at hz
  | live r q base outcome => simp [installationScoreVector, hcoord] at hz
  | collection old ledger clock cutoff outcome =>
      cases outcome with
      | laterChosen core consistent started hstart instruction hinstruction output hlocal
          clockData installed selected =>
          have hactual : record.output.preparation.coordinator =
              ReferenceActivePhysicalStep.dispatch record.input := by
            rw [record.output_eq]
            rfl
          have hp := ReferenceLaterInstallationProvenance.dispatch_laterChosen_provenance record.input
          rw [← hactual, hcoord] at hp
          obtain ⟨hinstalled, _⟩ := hp
          simp only [installationScoreVector, hcoord] at hz
          obtain ⟨rfl, rfl, _hcomplement⟩ := hz
          simp only [ReferenceAssignmentCollectionMassSteps.installedBaseScore, hcoord] at hbase
          have hbaseEq := Option.some.inj hbase
          subst base
          cases hinstalled
          intro i
          exact CoordinatorAssignmentRegisterInstall.later_retained_base_score_eq_source output clockData i
      | clockFailure _ _ => simp [installationScoreVector, hcoord] at hz
      | localFailure _ _ _ _ => simp [installationScoreVector, hcoord] at hz
      | coreFailure _ _ _ _ => simp [installationScoreVector, hcoord] at hz
      | continuing _ _ _ _ => simp [installationScoreVector, hcoord] at hz
      | laterReconstructionFailure _ _ _ _ _ _ _ _ => simp [installationScoreVector, hcoord] at hz
      | laterPrefixFailure _ _ _ _ _ _ _ _ _ => simp [installationScoreVector, hcoord] at hz
      | laterOrientationFailure _ _ _ _ _ _ _ => simp [installationScoreVector, hcoord] at hz
      | laterChoiceFailure _ _ _ _ _ _ _ _ _ _ => simp [installationScoreVector, hcoord] at hz
  | invalidCollectionCutoff => simp [installationScoreVector, hcoord] at hz
  | dagger => simp [installationScoreVector, hcoord] at hz

/-- Both disjoint calendar intervals are measured from the same installed
whole vector. Successful reconstruction supplies all actual option entries. -/
private theorem collection_reconstruction_score_span
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (completeSuffixRecords rate source rewards C_star C_h).length)
    (P : Payload rate) (l : Ledger rate) (saved : Option (Fin p.T × Bool))
    (hinput : (completeSuffixRecords rate source rewards C_star C_h)[k.val].input.state.coordinator =
      .collection P l saved)
    (clock : CoordinatorPhaseClock.ClockRegisters p) (cutoff : Fin p.T)
    (core : CollectionCoreValid (collectionInput
      (completeSuffixRecords rate source rewards C_star C_h)[k.val].input P l clock cutoff))
    (instruction : CoordinatorPhaseClock.AssignmentStartInstruction p)
    (output : LaterAssignmentStartOperation.SuccessfulStart
      (collectionInput (completeSuffixRecords rate source rewards C_star C_h)[k.val].input
        P l clock cutoff).payload
      (collectionOperationLedger
        (collectionInput (completeSuffixRecords rate source rewards C_star C_h)[k.val].input
          P l clock cutoff) core.payload_n_eq)
      instruction
      (collectionInput (completeSuffixRecords rate source rewards C_star C_h)[k.val].input
        P l clock cutoff).row) :
    let R := completeSuffixRecords rate source rewards C_star C_h
    ∃ b : Fin R.length, b.val < k.val ∧ InstallationBirth R[b.val] P ∧
      ∃ z : Fin p.K → ℕ, installationScoreVector R[b.val] P z ∧
        P.sigma.val ≤ instruction.time.val ∧
        l.freezeAt = FollowerCutoffScan.gridBoundary p rate.eta.val P.sigma ∧
        (∀ a, z a ≤ AssignmentScoreReconstruction.sourceScore output.reconstruction a ∧
          AssignmentScoreReconstruction.sourceScore output.reconstruction a ≤
            z a + (4 * rate.n) * (instruction.time.val - P.sigma.val)) := by
  classical
  dsimp only
  let R := completeSuffixRecords rate source rewards C_star C_h
  obtain ⟨b, hbk, hbirth, hbase, hassignment, hsigma, hcutoff, hfreeze,
    _hpositive, hcutFreeze, _hterminal, hcutCursor, _htime, hincrement, hassigned⟩ :=
    ReferenceCompleteCollectionAssignedScoreSpan.complete_collection_input_assigned_score_span
      rate rewards C_star C_h source k P l saved hinput
  obtain ⟨birth, hmem, hborn, z, hz, hcomplement⟩ :=
    complete_collection_cutoff_frame rewards C_star C_h source k P l saved hinput
  have hsame := same_birth_record rewards C_star C_h source P birth hmem hborn b hbirth
  rw [hsame] at hz
  have hbaseScore := installation_base_score R[b.val] P z l.baseScore hz hbase
  obtain ⟨hchecks, hcut, hcurrent, hscore, _hqueue, _hweights⟩ :=
    AssignmentScoreReconstruction.reconstructLaterStart_success_equations
      _ instruction output.reconstruction output.reconstruction_eq
  have hcutRegisters (a : Fin p.K) :
      l.cutoffRegisters a = some (output.reconstruction.registers.cutoff a) := hcut a
  have hcurrentRegisters (a : Fin p.K) :
      l.currentRegisters a = some (output.reconstruction.registers.current a) := hcurrent a
  have hsourceScore (a : Fin p.K) :
      AssignmentScoreReconstruction.sourceScore output.reconstruction a =
        (output.reconstruction.registers.cutoff a).score + l.increment a := hscore a
  have hcursor : l.cursor = instruction.time.val + 1 := hchecks.2.2.1
  have hfirst := FollowerCutoffScan.firstCutoff_bounds p rate.eta.val
    rate.eta.property rate.sourceCap P.sigma
    (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
      (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)))
  have hsigmaCut : P.sigma.val + 1 ≤ l.cutoff := by rw [hcutoff]; omega
  have hbefore : P.sigma.val ≤ instruction.time.val := by omega
  have hlength : min l.cursor l.freezeAt - (P.sigma.val + 1) ≤
      instruction.time.val - P.sigma.val := by omega
  have hinterval : (l.cutoff - (P.sigma.val + 1)) +
      (min l.cursor l.freezeAt - l.cutoff) =
        min l.cursor l.freezeAt - (P.sigma.val + 1) := by
    have hcutMin := Nat.le_min.mpr ⟨hcutCursor, hcutFreeze⟩
    omega
  refine ⟨b, hbk, hbirth, z, hz, hbefore, hfreeze, ?_⟩
  intro a
  rw [hsourceScore]
  by_cases ha : a ∈ P.slowSet.1
  · rw [← P.assignment_image] at ha
    obtain ⟨i, _hi, harm⟩ := Finset.mem_image.mp ha
    have hledgerArm : l.assignment.arm i = a := by rw [hassignment, harm]
    have hcutI : l.cutoffRegisters (l.assignment.arm i) =
        some (output.reconstruction.registers.cutoff a) := by
      rw [hledgerArm]
      exact hcutRegisters a
    have hcurrentI : l.currentRegisters (l.assignment.arm i) =
        some (output.reconstruction.registers.current a) := by
      rw [hledgerArm]
      exact hcurrentRegisters a
    have hs := hassigned i _ _ hcutI hcurrentI
    have hbaseEq : l.baseScore i = z a := (hbaseScore i).trans (congrArg z harm)
    rw [hbaseEq] at hs
    constructor
    · exact hs.1.trans (Nat.le_add_right _ _)
    · have hlast := hs.2.2.2.2
      rw [hledgerArm, hsigma] at hlast
      exact hlast.trans (Nat.add_le_add_left (Nat.mul_le_mul_left (4 * rate.n) hlength) _)
  · let j : CanonicalFastSampling.FastArm P.slowSet := ⟨a, by
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
      exact ha⟩
    obtain ⟨cut, current, hcutOld, _hcurrentOld, hlo, hhi⟩ := hcomplement j
    have hcutEq : cut = output.reconstruction.registers.cutoff a :=
      Option.some.inj (hcutOld.symm.trans (hcutRegisters a))
    subst cut
    have hinc := hincrement a _ _ (hcutRegisters a) (hcurrentRegisters a)
    constructor
    · exact hlo.trans (Nat.le_add_right _ _)
    · calc
        (output.reconstruction.registers.cutoff a).score + l.increment a ≤
            (z a + (4 * rate.n) * (l.cutoff - (P.sigma.val + 1))) +
              (4 * rate.n) * (min l.cursor l.freezeAt - l.cutoff) :=
          Nat.add_le_add hhi hinc
        _ = z a + (4 * rate.n) *
            ((l.cutoff - (P.sigma.val + 1)) +
              (min l.cursor l.freezeAt - l.cutoff)) := by rw [Nat.mul_add]; omega
        _ = z a + (4 * rate.n) *
            (min l.cursor l.freezeAt - (P.sigma.val + 1)) := by rw [hinterval]
        _ ≤ z a + (4 * rate.n) * (instruction.time.val - P.sigma.val) :=
          Nat.add_le_add_left (Nat.mul_le_mul_left _ hlength) _

private theorem collection_branch_input
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (payload : Payload rate) (ledger : Ledger rate)
    (clock : CoordinatorPhaseClock.ClockRegisters p) (cutoff : Fin p.T)
    (outcome : CollectionOutcome (collectionInput record.input payload ledger clock cutoff))
    (hbranch : record.output.preparation.coordinator =
      .collection payload ledger clock cutoff outcome) :
    ∃ saved, record.input.state.coordinator = .collection payload ledger saved := by
  have hactual : record.output.preparation.coordinator =
      ReferenceActivePhysicalStep.dispatch record.input := by
    rw [record.output_eq]
    rfl
  have hdispatch := hactual.symm.trans hbranch
  cases hstate : record.input.state.coordinator with
  | first =>
      simp [ReferenceActivePhysicalStep.dispatch, hstate] at hdispatch
      cases hdispatch
  | live r q base =>
      simp only [ReferenceActivePhysicalStep.dispatch, hstate] at hdispatch
      cases hround : CoordinatorRoundDispatch.dispatch (.live (liveInput record.input r q base));
        simp [hround] at hdispatch
      all_goals cases hdispatch
  | collection old oldLedger saved =>
      by_cases hvalid : 1 ≤ oldLedger.cutoff ∧ oldLedger.cutoff ≤ p.T
      · let oldCutoff : Fin p.T := ⟨oldLedger.cutoff - 1, by omega⟩
        let oldClock := collectionClock old oldLedger saved oldCutoff
        cases hround : CoordinatorRoundDispatch.dispatch
            (.collection (collectionInput record.input old oldLedger oldClock oldCutoff));
          simp [ReferenceActivePhysicalStep.dispatch, hstate, hvalid,
            oldCutoff, oldClock, hround] at hdispatch
        all_goals
          cases hdispatch
          exact ⟨saved, rfl⟩
      · simp [ReferenceActivePhysicalStep.dispatch, hstate, hvalid] at hdispatch
  | dagger => simp [ReferenceActivePhysicalStep.dispatch, hstate] at hdispatch

/-- Every actual installation has one actual first/renewal episode origin.
Both whole score vectors are the existing literal installation readouts;
corrected starts compose comparisons on that same earlier vector. -/
theorem actual_installation_episode_score_span
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (completeSuffixRecords rate source rewards C_star C_h).length)
    (P : Payload rate)
    (hbirth : InstallationBirth
      (completeSuffixRecords rate source rewards C_star C_h)[k.val] P) :
    let R := completeSuffixRecords rate source rewards C_star C_h
    ∃ rho : Fin R.length, ∃ P_rho : Payload rate,
      ∃ z_sigma z_rho : Fin p.K → ℕ,
        rho.val ≤ k.val ∧ InstallationBirth R[rho.val] P_rho ∧
        IsEpisodeAnchorBirth R[rho.val] ∧
        installationScoreVector R[k.val] P z_sigma ∧
        installationScoreVector R[rho.val] P_rho z_rho ∧
        R[rho.val].input.time = P_rho.sigma ∧
        P_rho.sigma.val ≤ P.sigma.val ∧ P.anchor = P_rho.anchor ∧
        (∀ a, P_rho.anchor a = AssignmentScoreReconstruction.sourceWeightBase p ^ z_rho a) ∧
        FollowerCutoffScan.gridBoundary p rate.eta.val P_rho.sigma =
          FollowerCutoffScan.gridBoundary p rate.eta.val P.sigma ∧
        ∀ a : Fin p.K, z_rho a ≤ z_sigma a ∧
          z_sigma a ≤ z_rho a + (4 * rate.n) * (P.sigma.val - P_rho.sigma.val) := by
  classical
  dsimp only
  let R := completeSuffixRecords rate source rewards C_star C_h
  induction k using Fin.strong_induction_on generalizing P with
  | h k ih =>
      let record := R[k.val]
      change InstallationBirth record P at hbirth
      cases hcoord : record.output.preparation.coordinator with
      | first outcome =>
          cases outcome with
          | chosen installed selected =>
              simp only [InstallationBirth, hcoord] at hbirth
              obtain ⟨rfl, _⟩ := hbirth
              have hsource := first_installation_source record installed selected hcoord
              have hinstalled := actual_firstChosen_installation_eq record installed selected hcoord
              refine ⟨k, installed.registers.payload, (fun _ => 0), (fun _ => 0),
                le_rfl, hsource.1, ?_, hsource.2.1, hsource.2.1, ?_, le_rfl, rfl, ?_, rfl, ?_⟩
              · change IsEpisodeAnchorBirth record
                simp only [IsEpisodeAnchorBirth, hcoord]
              · apply Fin.ext
                exact hsource.2.2.symm
              · intro a
                have hone := CoordinatorAssignmentRegisterInstall.first_payload_anchor_one
                  (CoordinatorRoundDispatch.firstLaunchInput (firstInput record.input)) a
                rw [← hinstalled] at hone
                exact hone.trans (by simp)
              · intro a
                simp only [Nat.sub_self, Nat.mul_zero, Nat.add_zero, le_refl, and_self]
          | choiceDomainFailure installed => simp [InstallationBirth, hcoord] at hbirth
          | recorderBoundaryFailure installed => simp [InstallationBirth, hcoord] at hbirth
          | choiceRejected installed => simp [InstallationBirth, hcoord] at hbirth
      | live r q base outcome => simp [InstallationBirth, hcoord] at hbirth
      | invalidCollectionCutoff => simp [InstallationBirth, hcoord] at hbirth
      | dagger => simp [InstallationBirth, hcoord] at hbirth
      | collection old ledger clock cutoff outcome =>
          cases outcome with
          | laterChosen core consistent started hstart instruction hinstruction output hlocal
              clockData installed selected =>
              simp only [InstallationBirth, hcoord] at hbirth
              obtain ⟨rfl, _⟩ := hbirth
              have hsource := later_installation_source record old ledger clock cutoff
                core consistent started hstart instruction hinstruction output hlocal clockData
                installed selected hcoord
              have hactual : record.output.preparation.coordinator =
                  ReferenceActivePhysicalStep.dispatch record.input := by
                rw [record.output_eq]
                rfl
              have hprovenance :=
                ReferenceLaterInstallationProvenance.dispatch_laterChosen_provenance record.input
              rw [← hactual, hcoord] at hprovenance
              obtain ⟨hinstalled, _⟩ := hprovenance
              obtain ⟨_, _, _, _, _, _, _, _, hkindExpected⟩ :=
                CoordinatorAssignmentRegisterInstall.later_start_round_compatibility output clockData
              cases hkind : instruction.kind with
              | renewal =>
                  have hanchor := CoordinatorAssignmentRegisterInstall.later_payload_anchor_renewal
                    output clockData hkind
                  have hinstalledAnchor : installed.registers.payload.anchor =
                      AssignmentScoreReconstruction.currentWeight output.reconstruction := by
                    rw [hinstalled]
                    exact hanchor
                  refine ⟨k, installed.registers.payload,
                    (fun a => AssignmentScoreReconstruction.sourceScore output.reconstruction a),
                    (fun a => AssignmentScoreReconstruction.sourceScore output.reconstruction a),
                    le_rfl, hsource.1, ?_, hsource.2.1, hsource.2.1, ?_, le_rfl, rfl, ?_, rfl, ?_⟩
                  · change IsEpisodeAnchorBirth record
                    simp only [IsEpisodeAnchorBirth, hcoord, hkind]
                  · apply Fin.ext
                    exact hsource.2.2.symm
                  · intro a
                    calc
                      installed.registers.payload.anchor a =
                          AssignmentScoreReconstruction.currentWeight output.reconstruction a :=
                        congrArg (fun f => f a) hinstalledAnchor
                      _ = AssignmentScoreReconstruction.sourceWeightBase p ^
                          AssignmentScoreReconstruction.sourceScore output.reconstruction a := rfl
                  · intro a
                    simp only [Nat.sub_self, Nat.mul_zero, Nat.add_zero, le_refl, and_self]
              | corrected =>
                  obtain ⟨saved, hstate⟩ := collection_branch_input record old ledger clock cutoff
                    (.laterChosen core consistent started hstart instruction hinstruction output
                      hlocal clockData installed selected) hcoord
                  obtain ⟨prior, hpriorLt, hpriorBirth, z_old, hvector, holdBeforeNew,
                    hfreeze, hcompare⟩ := collection_reconstruction_score_span
                      rewards C_star C_h source k old ledger saved hstate clock cutoff core
                      instruction output
                  obtain ⟨rho, P_rho, z_prior, z_rho, hrhoLe, hrootBirth, hrootBranch,
                    hpriorVector, hrootVector, hrootTime, hrootBeforeOld, holdAnchor,
                    hrootPow, hrootGrid, hrootSpan⟩ :=
                    ih prior hpriorLt old hpriorBirth
                  have hjoin : z_prior = z_old := installationScoreVector_unique
                    R[prior.val] old z_prior z_old hpriorVector hvector
                  rw [hjoin] at hrootSpan
                  have hnewStart : installed.registers.payload.sigma = instruction.time := by
                    rw [hinstalled]
                    exact output.payload_start
                  have hlocalFreeze : output.localConsistency.oldFreezeAt =
                      FollowerCutoffScan.gridBoundary p rate.eta.val old.sigma :=
                    output.localConsistency.oldFreezeAt_eq.trans hfreeze
                  have hcorrected := CoordinatorAssignmentRegisterInstall.later_corrected_branch
                    output clockData hkind
                  have hgridNew := gridBoundary_eq_of_before rate old.sigma instruction.time
                    holdBeforeNew (by rw [← hlocalFreeze]; exact hcorrected.1)
                  have hnewAnchor : installed.registers.payload.anchor = old.anchor := by
                    rw [hinstalled]
                    exact CoordinatorAssignmentRegisterInstall.later_payload_anchor_corrected
                      output clockData hkind
                  have hrootBeforeNew : P_rho.sigma.val ≤ installed.registers.payload.sigma.val := by
                    rw [hnewStart]
                    exact hrootBeforeOld.trans holdBeforeNew
                  have hrootGridCurrent :
                      FollowerCutoffScan.gridBoundary p rate.eta.val P_rho.sigma =
                        FollowerCutoffScan.gridBoundary p rate.eta.val installed.registers.payload.sigma := by
                    rw [hnewStart]
                    exact hrootGrid.trans hgridNew.symm
                  refine ⟨rho, P_rho,
                    (fun a => AssignmentScoreReconstruction.sourceScore output.reconstruction a),
                    z_rho, hrhoLe.trans (Nat.le_of_lt hpriorLt), hrootBirth, hrootBranch,
                    hsource.2.1, hrootVector, hrootTime, hrootBeforeNew,
                    hnewAnchor.trans holdAnchor, hrootPow, hrootGridCurrent, ?_⟩
                  intro a
                  have hprevious := hrootSpan a
                  have hstep := hcompare a
                  have hinterval : (old.sigma.val - P_rho.sigma.val) +
                      (installed.registers.payload.sigma.val - old.sigma.val) =
                        installed.registers.payload.sigma.val - P_rho.sigma.val := by
                    rw [hnewStart]
                    omega
                  constructor
                  · exact hprevious.1.trans hstep.1
                  · calc
                      AssignmentScoreReconstruction.sourceScore output.reconstruction a ≤
                          z_old a + (4 * rate.n) *
                            (installed.registers.payload.sigma.val - old.sigma.val) := by
                        rw [hnewStart]
                        exact hstep.2
                      _ ≤ (z_rho a + (4 * rate.n) * (old.sigma.val - P_rho.sigma.val)) +
                          (4 * rate.n) * (installed.registers.payload.sigma.val - old.sigma.val) :=
                        Nat.add_le_add_right hprevious.2 _
                      _ = z_rho a + (4 * rate.n) *
                          ((old.sigma.val - P_rho.sigma.val) +
                            (installed.registers.payload.sigma.val - old.sigma.val)) := by
                        rw [Nat.mul_add]
                        omega
                      _ = z_rho a + (4 * rate.n) *
                          (installed.registers.payload.sigma.val - P_rho.sigma.val) := by
                        rw [hinterval]
              | first =>
                  have hnotfirst : AssignmentScoreReconstruction.expectedLaterStartKind
                      output.localConsistency.oldFreezeAt instruction.time ≠ .first := by
                    by_cases hbefore : instruction.time.val + 1 < output.localConsistency.oldFreezeAt
                    · simp [AssignmentScoreReconstruction.expectedLaterStartKind, hbefore]
                    · simp [AssignmentScoreReconstruction.expectedLaterStartKind, hbefore]
                  exact False.elim (hnotfirst (hkindExpected.symm.trans hkind))
          | clockFailure _ _ => simp [InstallationBirth, hcoord] at hbirth
          | localFailure _ _ _ _ => simp [InstallationBirth, hcoord] at hbirth
          | coreFailure _ _ _ _ => simp [InstallationBirth, hcoord] at hbirth
          | continuing _ _ _ _ => simp [InstallationBirth, hcoord] at hbirth
          | laterReconstructionFailure _ _ _ _ _ _ _ _ => simp [InstallationBirth, hcoord] at hbirth
          | laterPrefixFailure _ _ _ _ _ _ _ _ _ => simp [InstallationBirth, hcoord] at hbirth
          | laterOrientationFailure _ _ _ _ _ _ _ => simp [InstallationBirth, hcoord] at hbirth
          | laterChoiceFailure _ _ _ _ _ _ _ _ _ _ => simp [InstallationBirth, hcoord] at hbirth

end Bandits.Support.ReferenceCompleteInstallationEpisodeScoreSpan

end
