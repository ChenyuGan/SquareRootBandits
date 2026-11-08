/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceActivePhysicalStep
public import Bandits.Support.ReferenceDownReceptionCoupling
public import Bandits.Support.ReferenceUpReceptionCoupling
public import Bandits.Support.DeclaredFollowerLocalRound
public import Bandits.Support.CoordinatorUpReception

/-!
# The ordinary counterpart of one active physical round

This module constructs the ordinary post-choice observer on the canonical
`ReferenceActivePhysicalStep.State` and `RoundInput` carriers. It uses the
same dispatcher, preparation, simultaneous actions and feedback, local
recorders, ledger, decoder bank, and checked finish tails as the reference
round. The ordinary UP observer calls the unfiltered checked receiver.

Sources: `sources/zip4/manuscript/06_interruptions.tex:3-5,123-177,235-297`,
`sources/zip4/manuscript/08_main_theorem.tex:29-42,67-75`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:6-14`.

The all-active, common-selected-row mode is an input to this one-round
construction. Initialization, launch, horizon recursion, event exclusion,
and manuscript regret closure are outside this module.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions

namespace Bandits.Support.OrdinaryActivePhysicalStep

local instance propDecidable (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition

variable {p : Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

/-- The operational coordinator fields of an observation. The reference-only
UP diagnostic is intentionally not part of the coordinator's physical state.
-/
def coordinatorOperationalFields
    (observation : ReferenceActivePhysicalStep.CoordinatorObservation p rate) :=
  (observation.configuration, observation.upDecoderBank)

/-- The ordinary collection suffix uses the same recorder output, enable bit,
and literal ledger start as the reference suffix. After that one service pass
it invokes `CoordinatorUpReception.receiveUp` on the actual ledger, carried
bank, current time, and coordinator's own collision observation. The existing
collection finish consumes that result; the ordinary path has no reference
diagnostic.
-/
def collectionPostChoice {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ) :
    ReferenceActivePhysicalStep.CoordinatorObservation p rate := by
  classical
  match CoordinatorRecorderComplementBridge.run
      (ReferenceActivePhysicalStep.collectionRecordingInput prepared payload started weights) with
  | none =>
      exact ReferenceActivePhysicalStep.coordinatorFailure x.state.upDecoderBank
        (.collection .recorderDomain) none none
  | some recording =>
      let enabled := ReferenceActivePhysicalStep.collectionEnabled ledger x.time
      let raw := CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording
      match CoordinatorCollectionLedger.startRound ledger (x.time.val + 1) enabled raw with
      | .invalid =>
          exact ReferenceActivePhysicalStep.coordinatorFailure x.state.upDecoderBank
            (.collection .ledgerStartDomain) (some recording) none
      | .rejected _ =>
          exact ReferenceActivePhysicalStep.coordinatorFailure x.state.upDecoderBank
            (.collection .ledgerStartDomain) (some recording) none
      | .success ledgerStarted =>
          let input := ReferenceUpReception.receptionInputAtRow rate x.row
            (ReferenceActivePhysicalStep.upInputs prepared ledgerStarted) x.time
          let ordinaryResult := CoordinatorUpReception.receiveUp input
          let cut : ReferenceActivePhysicalStep.UpCut p rate := ⟨ordinaryResult, none⟩
          exact ReferenceActivePhysicalStep.collectionFinish (x := x)
            payload started recording cut

/-- Run the existing dispatch result through the ordinary post-choice tails.
First, live, and later-start branches call the accepted `livePostChoice`;
cutoff and continuing-collection branches use the ordinary UP suffix above.
All dispatch, alignment, recorder, service, reception, and finish failures are
retained by the existing checked operations.
-/
def observeCoordinator {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (prepared : ReferenceActivePhysicalStep.PreparedRound x) :
    ReferenceActivePhysicalStep.CoordinatorObservation p rate := by
  classical
  exact if prepared.coordinator.selection = none then
    match prepared.coordinator with
    | .dagger => ⟨.dagger, x.state.upDecoderBank, none, none, none⟩
    | _ => ReferenceActivePhysicalStep.coordinatorFailure x.state.upDecoderBank
        .dispatchRejected none none
  else
    match prepared.coordinator with
    | .first (.chosen installed _) =>
        ReferenceActivePhysicalStep.livePostChoice prepared installed.registers
          installed.ownedRegisters installed.followerBaseScore installed.startRoundResult
    | .live r q base (.continuingChosen dispatched _ _ _) =>
        ReferenceActivePhysicalStep.livePostChoice prepared
          (ReferenceActivePhysicalStep.liveRegistersAt r x.time)
          (ReferenceActivePhysicalStep.liveOwnedAt r q x.time) base dispatched.startResult
    | .live r q _ (.cutoffChosen dispatched _ ledger _ _ _ _ _ _ _) =>
        collectionPostChoice prepared r.payload
          (ReferenceActivePhysicalStep.sharedLedger ledger) dispatched.startResult
          (ReferenceActivePhysicalStep.liveRegistersAt r x.time).complementWeights
    | .collection payload ledger clock cutoff (.continuing _ snapshot _ _) =>
        let source := ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff
        collectionPostChoice prepared payload ledger snapshot.clockStarted
          (CoordinatorCollectionInteractive.PreObservationInputs.weights source
            snapshot.inputsValid.ledger_valid snapshot.inputsValid.assignment_eq)
    | .collection _ _ _ _
        (.laterChosen _ _ started _ _ _ _ _ _ installed _) =>
        ReferenceActivePhysicalStep.livePostChoice prepared installed.registers
          installed.ownedRegisters installed.retainedBaseScore started
    | _ => ReferenceActivePhysicalStep.coordinatorFailure x.state.upDecoderBank
        .dispatchRejected none none

/-- One ordinary physical round, retaining the shared preparation, computed
ordinary observations, canonical successor, and actual own entries.
-/
structure RoundOutput (x : ReferenceActivePhysicalStep.RoundInput p rate) where
  preparation : ReferenceActivePhysicalStep.PreparedRound x
  coordinator : ReferenceActivePhysicalStep.CoordinatorObservation p rate
  followers : Fin (p.m - 1) → DeclaredFollowerLocalRound.ObservedRound p rate
  next : ReferenceActivePhysicalStep.State p rate
  ownEntries : Fin p.m → Fin p.K × ReferencePrelaunchFollower.Observation p

/-- The ordinary suffix of the shared one-round preparation. No action is
chosen again, and no feedback entry is supplied by the caller.
-/
def step (x : ReferenceActivePhysicalStep.RoundInput p rate) : RoundOutput x :=
  let prepared := ReferenceActivePhysicalStep.prepare x
  let coordinator := observeCoordinator prepared
  let followers := fun i => DeclaredFollowerLocalRound.observe
    (prepared.followers.followers i)
    (prepared.feedback.observations (PublicDiscreteDraws.followerPlayer p.two_le_m i))
  { preparation := prepared
    coordinator := coordinator
    followers := followers
    next := {
      coordinator := coordinator.configuration
      upDecoderBank := coordinator.upDecoderBank
      activations := x.state.activations
      followers := fun i => (followers i).configuration }
    ownEntries := prepared.feedback.ownEntries }

/-- The stored coordinator, bank, activation, and follower fields are exactly
the outputs of the computed ordinary post-choice operations.
-/
theorem step_next_fields (x : ReferenceActivePhysicalStep.RoundInput p rate) :
    (step x).next.coordinator = (observeCoordinator (ReferenceActivePhysicalStep.prepare x)).configuration ∧
    (step x).next.upDecoderBank = (observeCoordinator (ReferenceActivePhysicalStep.prepare x)).upDecoderBank ∧
    (step x).next.activations = x.state.activations ∧
    (∀ i, (step x).next.followers i =
      (DeclaredFollowerLocalRound.observe
        ((ReferenceActivePhysicalStep.prepare x).followers.followers i)
        ((ReferenceActivePhysicalStep.prepare x).feedback.observations
          (PublicDiscreteDraws.followerPlayer p.two_le_m i))).configuration) :=
  ⟨rfl, rfl, rfl, fun _ => rfl⟩

/-- The ordinary round uses the coordinator action from the shared prepared
profile, including the existing checked dispatch fallback branch.
-/
theorem step_action_coordinator (x : ReferenceActivePhysicalStep.RoundInput p rate) :
    (step x).preparation.arms.actions (ActiveRoundActions.coordinator p.two_le_m) =
      (step x).preparation.coordinator.arm :=
  (step x).preparation.action_coordinator

/-- Every ordinary follower action is the arm selected by that same follower's
existing local preparation.
-/
theorem step_action_follower (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (i : Fin (p.m - 1)) :
    (step x).preparation.arms.actions (PublicDiscreteDraws.followerPlayer p.two_le_m i) =
      (DeclaredFollowerLocalRound.prepare rate i x.row (x.state.activations i)
        x.time (x.active i) (x.state.followers i)).arm :=
  (step x).preparation.action_follower i

/-- The feedback vector is the existing simultaneous collision construction
applied to the prepared action profile and the complete reward table.
-/
theorem step_feedback_rule (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (player : Fin p.m) :
    (step x).preparation.feedback.feedback player =
      if FiniteBanditModel.collisionFreeFor (step x).preparation.arms.actions player then
        x.rewards x.time ((step x).preparation.arms.actions player) else 0 :=
  (step x).preparation.feedback_rule player

/-- The stored own entry is the prepared action paired with its actual
collision-filtered grid observation.
-/
theorem step_own_entry (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (player : Fin p.m) :
    (step x).ownEntries player =
      ((step x).preparation.arms.actions player,
        ActualInitializationPhysicalStep.observationOfGrid p
          ((step x).preparation.feedback.feedback player)) :=
  (step x).preparation.own_entry player

/-- Both physical constructions store the same immediate actions and own
observations because they use the identical prepared collision vector.
-/
theorem step_ownEntries_eq_reference (x : ReferenceActivePhysicalStep.RoundInput p rate) :
    (step x).ownEntries = (ReferenceActivePhysicalStep.step x).ownEntries := rfl

/-- The ordinary successor preserves every activation coordinate.
-/
theorem step_activation_preserved (x : ReferenceActivePhysicalStep.RoundInput p rate) :
    (step x).next.activations = x.state.activations := (step_next_fields x).2.2.1

/-- A local dagger input remains dagger under the computed ordinary follower
observer; no update or proposal-memory operation is run for that player.
-/
theorem step_follower_dagger_absorbing
    (x : ReferenceActivePhysicalStep.RoundInput p rate) (i : Fin (p.m - 1))
    (hdagger : x.state.followers i = .dagger) :
    (step x).next.followers i = .dagger := by
  have hprepared :
      (ReferenceActivePhysicalStep.prepare x).followers.followers i =
        DeclaredFollowerLocalRound.prepare rate i x.row (x.state.activations i)
          x.time (x.active i) .dagger := by
    rw [(ReferenceActivePhysicalStep.prepare x).followers.followers_eq i]
    simp [ReferenceActiveFeedbackCut.prepareFollowers,
      ReferenceActivePhysicalStep.followerInput,
      ReferenceActivePhysicalStep.RoundInput.row, hdagger]
  have hlocal :
      ((ReferenceActivePhysicalStep.prepare x).followers.followers i).configuration = .dagger := by
    rw [hprepared]
    exact (DeclaredFollowerLocalRound.prepare_dagger rate i x.row
      (x.state.activations i) x.time (x.active i)).2
  rw [(step_next_fields x).2.2.2 i]
  exact DeclaredFollowerLocalRound.observe_dagger_absorbing _ _ hlocal

/-- A checked collection finish's operational fields depend on its receiver
result and not on the reference-only diagnostic annotation.
-/
theorem collectionFinish_operational_eq_of_same_result
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (recording : CoordinatorRecordingOperation.Output p)
    (left right : ReferenceActivePhysicalStep.UpCut p rate)
    (hresult : left.result = right.result) :
    coordinatorOperationalFields
      (ReferenceActivePhysicalStep.collectionFinish (x := x) payload started recording left) =
    coordinatorOperationalFields
      (ReferenceActivePhysicalStep.collectionFinish (x := x) payload started recording right) := by
  cases left with
  | mk leftResult leftDiagnostic =>
      cases right with
      | mk rightResult rightDiagnostic =>
          change leftResult = rightResult at hresult
          cases hresult
          cases leftResult with
          | invalid =>
              simp [coordinatorOperationalFields,
                ReferenceActivePhysicalStep.collectionFinish,
                ReferenceActivePhysicalStep.coordinatorFailure]
          | success output =>
              rcases output with ⟨ledger, bank⟩
              simp only [coordinatorOperationalFields,
                ReferenceActivePhysicalStep.collectionFinish]
              cases hfinish : CoordinatorCollectionLedger.finishRound ledger with
              | invalid =>
                  simp [ReferenceActivePhysicalStep.coordinatorFailure]
              | rejected _ =>
                  simp [ReferenceActivePhysicalStep.coordinatorFailure]
              | success ledgerFinished =>
                  cases hclock : CoordinatorPhaseClock.finishRound p rate.eta.val x.time
                      started.clock ledgerFinished.pending x.row with
                  | error _ =>
                      simp [hclock, ReferenceActivePhysicalStep.coordinatorFailure]
                  | ok _ => simp [hclock]
          | rejected output =>
              rcases output with ⟨ledger, bank⟩
              simp only [coordinatorOperationalFields,
                ReferenceActivePhysicalStep.collectionFinish]
              cases hfinish : CoordinatorCollectionLedger.finishRound ledger with
              | invalid =>
                  simp [ReferenceActivePhysicalStep.coordinatorFailure]
              | rejected _ =>
                  simp [ReferenceActivePhysicalStep.coordinatorFailure]
              | success ledgerFinished =>
                  cases hclock : CoordinatorPhaseClock.finishRound p rate.eta.val x.time
                      started.clock ledgerFinished.pending x.row with
                  | error _ =>
                      simp [hclock, ReferenceActivePhysicalStep.coordinatorFailure]
                  | ok _ => simp [hclock]

/-- The saved diagnostic on a reference collection result is precisely the
diagnostic produced by its actual UP reception, regardless of later finish
success or failure.
-/
theorem collectionFinish_up_eq_diagnostic
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (recording : CoordinatorRecordingOperation.Output p)
    (cut : ReferenceActivePhysicalStep.UpCut p rate) :
    (ReferenceActivePhysicalStep.collectionFinish (x := x) payload started recording cut).up =
      cut.diagnostic := by
  cases cut with
  | mk result diagnostic =>
      cases result with
      | invalid =>
          simp [ReferenceActivePhysicalStep.collectionFinish,
            ReferenceActivePhysicalStep.coordinatorFailure]
      | success output =>
          rcases output with ⟨ledger, bank⟩
          simp only [ReferenceActivePhysicalStep.collectionFinish]
          cases hfinish : CoordinatorCollectionLedger.finishRound ledger with
          | invalid =>
              simp [ReferenceActivePhysicalStep.coordinatorFailure]
          | rejected rejectedLedger =>
              simp [ReferenceActivePhysicalStep.coordinatorFailure]
          | success ledgerFinished =>
              cases hclock : CoordinatorPhaseClock.finishRound p rate.eta.val x.time
                  started.clock ledgerFinished.pending x.row with
              | error reason =>
                  simp [hclock, ReferenceActivePhysicalStep.coordinatorFailure]
              | ok clockFinished =>
                  simp [hclock]
      | rejected output =>
          rcases output with ⟨ledger, bank⟩
          simp only [ReferenceActivePhysicalStep.collectionFinish]
          cases hfinish : CoordinatorCollectionLedger.finishRound ledger with
          | invalid =>
              simp [ReferenceActivePhysicalStep.coordinatorFailure]
          | rejected rejectedLedger =>
              simp [ReferenceActivePhysicalStep.coordinatorFailure]
          | success ledgerFinished =>
              cases hclock : CoordinatorPhaseClock.finishRound p rate.eta.val x.time
                  started.clock ledgerFinished.pending x.row with
              | error reason =>
                  simp [hclock, ReferenceActivePhysicalStep.coordinatorFailure]
              | ok clockFinished =>
                  simp [hclock]

/-- On the saved per-round UP condition, the ordinary and reference
collection suffixes have identical operational configuration and complete
decoder bank. The condition is read from the reference suffix's own saved
diagnostic, so absent diagnostics and all pre-reception failures are vacuous.
-/
theorem collectionPostChoice_operational_eq_of_saved_diagnostics
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ)
    (hgood : ∀ d,
      (ReferenceActivePhysicalStep.collectionPostChoice prepared payload ledger started weights).up =
        some d → d.wrongUniqueAccepted = false) :
    coordinatorOperationalFields (collectionPostChoice prepared payload ledger started weights) =
    coordinatorOperationalFields
      (ReferenceActivePhysicalStep.collectionPostChoice prepared payload ledger started weights) := by
  classical
  unfold collectionPostChoice ReferenceActivePhysicalStep.collectionPostChoice
  cases hrecord : CoordinatorRecorderComplementBridge.run
      (ReferenceActivePhysicalStep.collectionRecordingInput prepared payload started weights) with
  | none =>
      simp [coordinatorOperationalFields,
        ReferenceActivePhysicalStep.coordinatorFailure]
  | some recording =>
      let enabled := ReferenceActivePhysicalStep.collectionEnabled ledger x.time
      let raw := CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording
      cases hstart : CoordinatorCollectionLedger.startRound ledger (x.time.val + 1) enabled raw with
      | invalid =>
          simp [hstart, enabled, raw, coordinatorOperationalFields,
            ReferenceActivePhysicalStep.coordinatorFailure]
      | rejected rejectedLedger =>
          simp [hstart, enabled, raw, coordinatorOperationalFields,
            ReferenceActivePhysicalStep.coordinatorFailure]
      | success ledgerStarted =>
          simp only [hstart, enabled, raw]
          let cut := ReferenceActivePhysicalStep.receiveUp prepared ledgerStarted
          have hdiagnostics : ∀ d, cut.diagnostic = some d → d.wrongUniqueAccepted = false := by
            intro d hd
            have hfinish := collectionFinish_up_eq_diagnostic
              (x := x) payload started recording cut
            have hobs :
                (ReferenceActivePhysicalStep.collectionPostChoice prepared payload ledger
                  started weights).up = some d := by
              simpa [ReferenceActivePhysicalStep.collectionPostChoice,
                hrecord, hstart, enabled, raw, cut] using hfinish.trans hd
            exact hgood d hobs
          have hreceive :=
            ReferenceUpReceptionCoupling.receiveUp_eq_ordinary_of_no_saved_wrong_unique_accepted
              prepared ledgerStarted hdiagnostics
          let ordinaryInput := ReferenceUpReception.receptionInputAtRow rate x.row
            (ReferenceActivePhysicalStep.upInputs prepared ledgerStarted) x.time
          let ordinaryResult := CoordinatorUpReception.receiveUp ordinaryInput
          have hresult : cut.result = ordinaryResult := by
            simpa [cut, ordinaryInput] using hreceive
          have hfinish :=
            ReferenceUpReceptionCoupling.collectionFinish_eq_with_ordinary_up_result
              payload started recording prepared ledgerStarted hdiagnostics
          let modifiedCut : ReferenceActivePhysicalStep.UpCut p rate :=
            { cut with result := ordinaryResult }
          let ordinaryCut : ReferenceActivePhysicalStep.UpCut p rate :=
            ⟨ordinaryResult, none⟩
          have hoperational := collectionFinish_operational_eq_of_same_result (x := x)
            payload started recording modifiedCut ordinaryCut (by rfl)
          calc
            coordinatorOperationalFields
                (ReferenceActivePhysicalStep.collectionFinish (x := x)
                  payload started recording ordinaryCut) =
                coordinatorOperationalFields
                  (ReferenceActivePhysicalStep.collectionFinish (x := x)
                    payload started recording modifiedCut) :=
              hoperational.symm
            _ = coordinatorOperationalFields
                (ReferenceActivePhysicalStep.collectionFinish (x := x)
                  payload started recording cut) := by
              exact (congrArg coordinatorOperationalFields hfinish).symm

/-- Operational equality of the reference and ordinary coordinator observers
follows by reusing the common live tail and applying the saved-UP coupling only
on the two real collection branches.
-/
theorem observeCoordinator_operational_eq_of_saved_diagnostics
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (hgood : ∀ d,
      (prepared.observeCoordinator).up = some d → d.wrongUniqueAccepted = false) :
    coordinatorOperationalFields (observeCoordinator prepared) =
      coordinatorOperationalFields prepared.observeCoordinator := by
  classical
  by_cases hselection : prepared.coordinator.selection = none
  · unfold observeCoordinator ReferenceActivePhysicalStep.PreparedRound.observeCoordinator
    simp only [ite_eq_left hselection, dite_eq_left hselection]
    rfl
  · cases hcut : prepared.coordinator with
    | first outcome =>
        have hselection' := hselection
        rw [hcut] at hselection'
        cases outcome with
        | choiceDomainFailure installation =>
            simp [observeCoordinator, ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
              hcut, hselection', coordinatorOperationalFields,
              ReferenceActivePhysicalStep.coordinatorFailure]
        | recorderBoundaryFailure installation =>
            simp [observeCoordinator, ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
              hcut, hselection', coordinatorOperationalFields,
              ReferenceActivePhysicalStep.coordinatorFailure]
        | choiceRejected installation =>
            simp [observeCoordinator, ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
              hcut, hselection', coordinatorOperationalFields,
              ReferenceActivePhysicalStep.coordinatorFailure]
        | chosen installation selection =>
            simp [observeCoordinator, ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
              hcut, hselection', coordinatorOperationalFields,
              ReferenceActivePhysicalStep.livePostChoice]
    | live registers owned base outcome =>
        have hselection' := hselection
        rw [hcut] at hselection'
        cases outcome with
        | clockFailure failure hdispatch =>
            simp [observeCoordinator, ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
              hcut, hselection', coordinatorOperationalFields,
              ReferenceActivePhysicalStep.coordinatorFailure]
        | initializerFailure dispatched hstart checked hchecked =>
            simp [observeCoordinator, ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
              hcut, hselection', coordinatorOperationalFields,
              ReferenceActivePhysicalStep.coordinatorFailure]
        | localFailure dispatched hstart reason =>
            simp [observeCoordinator, ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
              hcut, hselection', coordinatorOperationalFields,
              ReferenceActivePhysicalStep.coordinatorFailure]
        | cutoffChosen dispatched hstart ledger hinitialized hledger hdomain hclock
            hpending hnoAssignment selection =>
            have hcollection : ∀ d,
                (ReferenceActivePhysicalStep.collectionPostChoice prepared registers.payload
                  (ReferenceActivePhysicalStep.sharedLedger ledger) dispatched.startResult
                  (ReferenceActivePhysicalStep.liveRegistersAt registers x.time).complementWeights).up =
                  some d → d.wrongUniqueAccepted = false := by
              intro d hd
              apply hgood d
              simpa [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
                hcut, hselection'] using hd
            have heq := collectionPostChoice_operational_eq_of_saved_diagnostics
              prepared registers.payload (ReferenceActivePhysicalStep.sharedLedger ledger)
              dispatched.startResult
              (ReferenceActivePhysicalStep.liveRegistersAt registers x.time).complementWeights
              hcollection
            simpa [observeCoordinator, ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
              hcut, hselection', coordinatorOperationalFields] using heq
        | continuingChosen dispatched hstart continuation selection =>
            simp [observeCoordinator, ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
              hcut, hselection', coordinatorOperationalFields,
              ReferenceActivePhysicalStep.livePostChoice,
              ReferenceActivePhysicalStep.liveRegistersAt,
              ReferenceActivePhysicalStep.liveOwnedAt]
    | collection payload ledger clock cutoff outcome =>
        have hselection' := hselection
        rw [hcut] at hselection'
        cases outcome with
        | clockFailure failure hstart =>
            simp [observeCoordinator, ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
              hcut, hselection', coordinatorOperationalFields,
              ReferenceActivePhysicalStep.coordinatorFailure]
        | localFailure started hstart hcore reason =>
            simp [observeCoordinator, ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
              hcut, hselection', coordinatorOperationalFields,
              ReferenceActivePhysicalStep.coordinatorFailure]
        | coreFailure core started hstart reason =>
            simp [observeCoordinator, ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
              hcut, hselection', coordinatorOperationalFields,
              ReferenceActivePhysicalStep.coordinatorFailure]
        | continuing core snapshot hboundary hscores =>
            let source := ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff
            let weights := CoordinatorCollectionInteractive.PreObservationInputs.weights source
              snapshot.inputsValid.ledger_valid snapshot.inputsValid.assignment_eq
            have hcollection : ∀ d,
                (ReferenceActivePhysicalStep.collectionPostChoice prepared payload ledger
                  snapshot.clockStarted weights).up = some d → d.wrongUniqueAccepted = false := by
              intro d hd
              apply hgood d
              simpa [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
                hcut, hselection', source, weights] using hd
            have heq := collectionPostChoice_operational_eq_of_saved_diagnostics
              prepared payload ledger snapshot.clockStarted weights hcollection
            simpa [observeCoordinator, ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
              hcut, hselection', source, weights, coordinatorOperationalFields] using heq
        | laterReconstructionFailure core consistent started hstart instruction hinstruction
            reason hlater =>
            simp [observeCoordinator, ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
              hcut, hselection', coordinatorOperationalFields,
              ReferenceActivePhysicalStep.coordinatorFailure]
        | laterPrefixFailure core consistent started hstart instruction hinstruction arm reason hlater =>
            simp [observeCoordinator, ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
              hcut, hselection', coordinatorOperationalFields,
              ReferenceActivePhysicalStep.coordinatorFailure]
        | laterOrientationFailure core consistent started hstart instruction hinstruction set hlater =>
            simp [observeCoordinator, ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
              hcut, hselection', coordinatorOperationalFields,
              ReferenceActivePhysicalStep.coordinatorFailure]
        | laterChoiceFailure core consistent started hstart instruction hinstruction output hlocal
            clockData installation reason =>
            simp [observeCoordinator, ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
              hcut, hselection', coordinatorOperationalFields,
              ReferenceActivePhysicalStep.coordinatorFailure]
        | laterChosen core consistent started hstart instruction hinstruction output hlocal
            clockData installation selection =>
            simp [observeCoordinator, ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
              hcut, hselection', coordinatorOperationalFields,
              ReferenceActivePhysicalStep.livePostChoice]
    | invalidCollectionCutoff =>
        have hselection' := hselection
        rw [hcut] at hselection'
        simp [observeCoordinator, ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
          hcut, hselection', coordinatorOperationalFields,
          ReferenceActivePhysicalStep.coordinatorFailure]
    | dagger =>
        have hselection' := hselection
        rw [hcut] at hselection'
        have hfalse : False := by
          simp [ReferenceActivePhysicalStep.DispatchCut.selection] at hselection'
        exact hfalse.elim

/-- The complete ordinary successor equals the reference successor whenever
each diagnostic actually saved by this reference round avoids the unique
wrong-word acceptance event. The follower condition ranges only over actual
saved DOWN cuts; absent cuts and failed logging require no extra premise.
-/
theorem step_eq_reference_of_saved_diagnostics_not_wrongUniqueAccepted
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (hup : ∀ d,
      (ReferenceActivePhysicalStep.step x).coordinator.up = some d →
        d.wrongUniqueAccepted = false)
    (hdown : ∀ i cut,
      ((ReferenceActivePhysicalStep.step x).followers i).down = some cut →
        ¬ ReferenceDownReception.wrongUniqueAccepted cut) :
    (step x).next = (ReferenceActivePhysicalStep.step x).next := by
  let prepared := ReferenceActivePhysicalStep.prepare x
  have hgoodCoordinator : ∀ d, prepared.observeCoordinator.up = some d →
      d.wrongUniqueAccepted = false := by
    intro d hd
    apply hup d
    simpa [ReferenceActivePhysicalStep.step, prepared] using hd
  have hcoordinator := observeCoordinator_operational_eq_of_saved_diagnostics
    prepared hgoodCoordinator
  have hfields :
      ((observeCoordinator prepared).configuration,
        (observeCoordinator prepared).upDecoderBank) =
      (prepared.observeCoordinator.configuration,
        prepared.observeCoordinator.upDecoderBank) := by
    simpa [coordinatorOperationalFields] using hcoordinator
  have hconfiguration :
      (step x).next.coordinator = (ReferenceActivePhysicalStep.step x).next.coordinator := by
    simpa [step, prepared, ReferenceActivePhysicalStep.step] using congrArg Prod.fst hfields
  have hbank :
      (step x).next.upDecoderBank =
        (ReferenceActivePhysicalStep.step x).next.upDecoderBank := by
    simpa [step, prepared, ReferenceActivePhysicalStep.step] using congrArg Prod.snd hfields
  have hactivations :
      (step x).next.activations =
        (ReferenceActivePhysicalStep.step x).next.activations := by
    simp [step, ReferenceActivePhysicalStep.step]
  have hfollowers :
      (step x).next.followers =
        (ReferenceActivePhysicalStep.step x).next.followers := by
    funext i
    have hgoodFollower : ∀ cut,
        ((ReferenceActivePhysicalStep.step x).followers i).down = some cut →
          ¬ ReferenceDownReception.wrongUniqueAccepted cut := hdown i
    have hfollower :=
      ReferenceDownReceptionCoupling.step_follower_eq_ordinary_observe_of_saved_cuts_not_wrongUniqueAccepted
        rate x i hgoodFollower
    simpa [step, prepared, ReferenceActivePhysicalStep.step] using hfollower.symm
  change ReferenceActivePhysicalStep.State.mk _ _ _ _ =
    ReferenceActivePhysicalStep.State.mk _ _ _ _
  rw [ReferenceActivePhysicalStep.State.mk.injEq]
  exact ⟨hconfiguration, hbank, hactivations, hfollowers⟩

end Bandits.Support.OrdinaryActivePhysicalStep

end
