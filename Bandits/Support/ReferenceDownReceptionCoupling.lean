/-
Copyright (c) 2026 Bandits Lean regret formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceActivePhysicalStep
public import Bandits.Support.ReferenceDownReception
public import Bandits.Support.DeclaredFollowerLocalRound
public import Bandits.Support.ActiveFollowerDownAcceptance

/-!
# Conditional DOWN reception coupling

The checked reference DOWN cut and the ordinary receiver have the same
consumed local result whenever the cut is not a unique wrong word accepted by
the ordinary local test. This is a one-decision statement on the saved cut;
it does not assume event exclusion over a run.

Sources: `sources/zip4/manuscript/06_interruptions.tex:123-177,235-297`,
`sources/zip4/manuscript/08_main_theorem.tex:29-42,67-75`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:6-14`.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ReferenceDownReceptionCoupling

open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceDownReception
open Bandits.Support.DeclaredFollowerLocalRound
open Bandits.Support.ActiveFollowerDownAcceptance
open Bandits.Support.OrdinaryMessageCodec
open Bandits.Support.ReferencePrelaunchFollower
open Bandits.Support.ConstructorDimensions

variable {p : Parameters} {eta : LearningRate}
variable {rate : ActiveFollowerDownAcceptance.RateInput p}

/-- After consuming the decoder/recovery result, the reference-filtered cut
and the ordinary DOWN transition agree whenever the actual cut does not have
the manuscript's unique-wrong-word local-acceptance flag. In particular,
raw rejection and parsed-but-unaccepted diagnostics may differ. -/
theorem consumeDownResult_eq_of_not_wrongUniqueAccepted
    (view : Option (ReferenceDownReception.ChoiceTimeView p eta))
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (t : Fin p.T) (feedback : ReferencePrelaunchFollower.Observation p)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (hgood : ¬ ReferenceDownReception.wrongUniqueAccepted
      (ReferenceDownReception.referenceDownCut p view i row t feedback rate state)) :
    DeclaredFollowerLocalRound.consumeDownResult rate
        (ReferenceDownReception.referenceDownCut p view i row t feedback rate state).outcome =
      DeclaredFollowerLocalRound.consumeDownResult rate
        (ActiveFollowerDownAcceptance.downTransition p i row t feedback rate state) := by
  classical
  by_cases hselected : ActiveFollowerDownAcceptance.downSelected p i row t
  · by_cases hstatus : state.status = .unoccupied
    · by_cases hregisters : ActiveFollowerDownAcceptance.registerInputDomain p rate state
      · by_cases hbatch : ActiveFollowerDownAcceptance.decoderInputDomain p state.downBatch
        · by_cases hbuffer : ActiveFollowerDownAcceptance.bufferInputDomain p state.buffer
          · let decoded := ActiveFollowerDownAcceptance.currentDecodeStep
              p i row t feedback rate state
            by_cases hmatches : decoded.2 =
                ReferenceDownReception.expectedDownFlatWord view i row t
            · have hnotmismatch : ¬ ReferenceDownReception.rawMismatch
                  (ReferenceDownReception.referenceDownCut p view i row t
                    feedback rate state) := by
                intro hmismatch
                simp [ReferenceDownReception.rawMismatch,
                  ReferenceDownReception.referenceDownCut,
                  hselected, hstatus, hregisters, hbatch, hbuffer,
                  decoded, hmatches] at hmismatch
              have houtcome :=
                ReferenceDownReception.referenceDownCut_outcome_eq_downTransition_of_no_raw_mismatch
                  view i row t feedback rate state hnotmismatch
              exact congrArg (DeclaredFollowerLocalRound.consumeDownResult rate)
                houtcome
            · cases hparsed : OrdinaryMessageCodec.parseDown
                  (ReferencePrelaunchFollower.codecParams p rate.eta)
                  (decoded.2.map
                    (OrdinaryMessageCodec.wordEquivFlat
                      (ReferencePrelaunchFollower.codecParams p rate.eta)).symm) with
              | none =>
                  simp [ReferenceDownReception.referenceDownCut,
                    ActiveFollowerDownAcceptance.downTransition,
                    DeclaredFollowerLocalRound.consumeDownResult,
                    ReferenceDownReception.ordinaryParse,
                    hselected, hstatus, hregisters, hbatch, hbuffer,
                    decoded, hmatches, hparsed]
              | some message =>
                  have hraw : decoded.2 ≠ none := by
                    intro hnone
                    rw [hnone] at hparsed
                    change (none : Option (OrdinaryMessageCodec.DownRecord
                      (ReferencePrelaunchFollower.codecParams p rate.eta))) =
                        some message at hparsed
                    cases hparsed
                  have hnotAccepted :
                      ¬ OrdinaryMessageCodec.acceptDown
                        (ReferencePrelaunchFollower.codecParams p rate.eta)
                        (ReferencePrelaunchFollower.acceptedStart state)
                        (t.val + 1) message := by
                    intro haccepted
                    have hflag : ReferenceDownReception.wrongUniqueAccepted
                        (ReferenceDownReception.referenceDownCut p view i row t
                          feedback rate state) := by
                      change
                        (ReferenceDownReception.referenceDownCut p view i row t
                          feedback rate state).rawComparison = some false ∧
                        (ReferenceDownReception.referenceDownCut p view i row t
                          feedback rate state).raw ≠ none ∧
                        (ReferenceDownReception.referenceDownCut p view i row t
                          feedback rate state).ordinaryAcceptance
                      refine ⟨?_, ?_, ?_⟩
                      · simp [ReferenceDownReception.referenceDownCut,
                          hselected, hstatus, hregisters, hbatch, hbuffer,
                          decoded, hmatches]
                      · simpa [ReferenceDownReception.referenceDownCut,
                          hselected, hstatus, hregisters, hbatch, hbuffer,
                          decoded, hmatches] using hraw
                      · simpa [ReferenceDownReception.referenceDownCut,
                          ReferenceDownReception.ordinaryParse,
                          ReferenceDownReception.ordinaryLocalAcceptanceTest,
                          hselected, hstatus, hregisters, hbatch, hbuffer,
                          decoded, hmatches, hparsed] using haccepted
                    exact hgood hflag
                  have hdown : ActiveFollowerDownAcceptance.downTransition
                      p i row t feedback rate state =
                    .parsedButUnaccepted state
                      { state with downBatch := decoded.1 } decoded.2 message := by
                    have hparsed' : ActiveFollowerDownAcceptance.parsedCurrentOutput
                        p i row t feedback rate state = some message := by
                      simpa only [ActiveFollowerDownAcceptance.parsedCurrentOutput,
                        decoded] using hparsed
                    exact ActiveFollowerDownAcceptance.downTransition_unaccepted_equation
                      p i row t feedback rate state hselected hstatus hregisters
                      hbatch hbuffer message hparsed' hnotAccepted
                  rw [hdown]
                  simp [ReferenceDownReception.referenceDownCut,
                    DeclaredFollowerLocalRound.consumeDownResult,
                    ReferenceDownReception.ordinaryParse,
                    hselected, hstatus, hregisters, hbatch, hbuffer,
                    decoded, hmatches]
          · simp [ReferenceDownReception.referenceDownCut,
              ActiveFollowerDownAcceptance.downTransition,
              DeclaredFollowerLocalRound.consumeDownResult,
              hselected, hstatus, hregisters, hbatch, hbuffer]
        · simp [ReferenceDownReception.referenceDownCut,
            ActiveFollowerDownAcceptance.downTransition,
            DeclaredFollowerLocalRound.consumeDownResult,
            hselected, hstatus, hregisters, hbatch]
      · simp [ReferenceDownReception.referenceDownCut,
          ActiveFollowerDownAcceptance.downTransition,
          DeclaredFollowerLocalRound.consumeDownResult,
          hselected, hstatus, hregisters]
    · simp [ReferenceDownReception.referenceDownCut,
        ActiveFollowerDownAcceptance.downTransition,
        DeclaredFollowerLocalRound.consumeDownResult,
        hselected, hstatus]
  · simp [ReferenceDownReception.referenceDownCut,
      ActiveFollowerDownAcceptance.downTransition,
      DeclaredFollowerLocalRound.consumeDownResult,
      hselected]

/-- The complete logging/receiver stage agrees with the declared local-round
operation when each actual saved cut avoids `wrongUniqueAccepted`. Logging
failure and occupied service retain their ordinary checked behavior. -/
theorem recordFollower_result_eq_declared_of_saved_cuts_not_wrongUniqueAccepted
    (rate : ActiveFollowerDownAcceptance.RateInput p)
    (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (activation : ReferencePrelaunchFollower.Activation p) (t : Fin p.T)
    (active : activation.val ≤ t.val + 1) (arm : Fin p.K)
    (observation : ReferencePrelaunchFollower.Observation p)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (hgood : ∀ cut,
      (ReferenceActivePhysicalStep.recordFollower view i row activation t active
        arm observation state).down = some cut →
        ¬ ReferenceDownReception.wrongUniqueAccepted cut) :
    (ReferenceActivePhysicalStep.recordFollower view i row activation t active
      arm observation state).result =
    DeclaredFollowerLocalRound.recordOrServiceThenDown rate i row activation t
      active arm observation state := by
  classical
  rw [ReferenceActivePhysicalStep.recordFollower_result]
  by_cases hunoccupied : state.status = .unoccupied
  · cases hlogging : ActiveFollowerLogging.checkedLogging i row activation t
      (arm, observation) state with
    | error reason =>
        simp [ReferenceDownReception.loggingThenReferenceDown,
          DeclaredFollowerLocalRound.recordOrServiceThenDown,
          hunoccupied, hlogging]
    | ok logged =>
        have hcut : ¬ ReferenceDownReception.wrongUniqueAccepted
            (ReferenceDownReception.referenceDownCut p view i row t observation
              rate logged) := by
          apply hgood (ReferenceDownReception.referenceDownCut p view i row t
            observation rate logged)
          simp [ReferenceActivePhysicalStep.recordFollower,
            hunoccupied, hlogging]
        have hconsumed := consumeDownResult_eq_of_not_wrongUniqueAccepted
          view i row t observation logged hcut
        simp only [ReferenceDownReception.loggingThenReferenceDown,
          DeclaredFollowerLocalRound.recordOrServiceThenDown,
          dite_eq_left hunoccupied, hlogging]
        exact hconsumed
  · simp [ReferenceDownReception.loggingThenReferenceDown,
      DeclaredFollowerLocalRound.recordOrServiceThenDown,
      hunoccupied]

/-- The actual saved-cut condition carries through checked logging, release
eligibility, and the final proposal read. Both sides start from the same
prepared follower snapshot, row, and collision observation. -/
theorem finishFollower_configuration_eq_observe_of_saved_cuts_not_wrongUniqueAccepted
    (rate : ActiveFollowerDownAcceptance.RateInput p)
    (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (prepared : DeclaredFollowerLocalRound.PreparedRound p rate)
    (observation : ReferencePrelaunchFollower.Observation p)
    (hgood : ∀ cut,
      (ReferenceActivePhysicalStep.finishFollower view prepared observation).down =
        some cut → ¬ ReferenceDownReception.wrongUniqueAccepted cut) :
    (ReferenceActivePhysicalStep.finishFollower view prepared observation).configuration =
      (DeclaredFollowerLocalRound.observe prepared observation).configuration := by
  classical
  cases hconfiguration : prepared.configuration with
  | dagger =>
      simp [ReferenceActivePhysicalStep.finishFollower,
        DeclaredFollowerLocalRound.observe, hconfiguration]
  | ordinary state memory =>
      have hrecordGood : ∀ cut,
          (ReferenceActivePhysicalStep.recordFollower view prepared.follower
            prepared.row prepared.activation prepared.time prepared.active prepared.arm
            observation state).down = some cut →
            ¬ ReferenceDownReception.wrongUniqueAccepted cut := by
        intro cut hcut
        have hdownEq :
            (ReferenceActivePhysicalStep.finishFollower view prepared observation).down =
              (ReferenceActivePhysicalStep.recordFollower view prepared.follower
                prepared.row prepared.activation prepared.time prepared.active
                prepared.arm observation state).down := by
          cases hrecordResult :
              (ReferenceActivePhysicalStep.recordFollower view prepared.follower
                prepared.row prepared.activation prepared.time prepared.active
                prepared.arm observation state).result with
          | error failure =>
              simp [ReferenceActivePhysicalStep.finishFollower,
                hconfiguration, hrecordResult]
          | ok postRecord =>
              cases hfinish : DeclaredFollowerLocalRound.releaseAndFinish rate
                  prepared.follower prepared.row prepared.time observation state memory
                  postRecord <;>
                simp [ReferenceActivePhysicalStep.finishFollower,
                  hconfiguration, hrecordResult, hfinish]
        apply hgood cut
        rw [hdownEq]
        exact hcut
      have hrecord := recordFollower_result_eq_declared_of_saved_cuts_not_wrongUniqueAccepted
        rate view prepared.follower prepared.row prepared.activation prepared.time
        prepared.active prepared.arm observation state hrecordGood
      cases hstage : DeclaredFollowerLocalRound.recordOrServiceThenDown rate
          prepared.follower prepared.row prepared.activation prepared.time prepared.active
          prepared.arm observation state with
      | error reason =>
          simp [ReferenceActivePhysicalStep.finishFollower,
            DeclaredFollowerLocalRound.observe, hconfiguration, hrecord,
            DeclaredFollowerLocalRound.observeOrdinary, hstage]
      | ok postRecord =>
          cases hfinish : DeclaredFollowerLocalRound.releaseAndFinish rate
              prepared.follower prepared.row prepared.time observation state memory
              postRecord <;>
            simp [ReferenceActivePhysicalStep.finishFollower,
              DeclaredFollowerLocalRound.observe, hconfiguration, hrecord,
              DeclaredFollowerLocalRound.observeOrdinary, hstage, hfinish]

/-- On the actual computed physical step, absence of `wrongUniqueAccepted` on
every saved DOWN cut gives equality of this follower's next configuration
with the ordinary observer on the same prepared state and actual observation.
This is a deterministic per-round conditional comparison only. -/
theorem step_follower_eq_ordinary_observe_of_saved_cuts_not_wrongUniqueAccepted
    (rate : ActiveFollowerDownAcceptance.RateInput p)
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (i : Fin (p.m - 1))
    (hgood : ∀ cut,
      ((ReferenceActivePhysicalStep.step x).followers i).down = some cut →
        ¬ ReferenceDownReception.wrongUniqueAccepted cut) :
    (ReferenceActivePhysicalStep.step x).next.followers i =
      (DeclaredFollowerLocalRound.observe
        ((ReferenceActivePhysicalStep.prepare x).followers.followers i)
        ((ReferenceActivePhysicalStep.prepare x).feedback.observations
          (PublicDiscreteDraws.followerPlayer p.two_le_m i))).configuration := by
  let prepared := ReferenceActivePhysicalStep.prepare x
  let observation := prepared.feedback.observations
    (PublicDiscreteDraws.followerPlayer p.two_le_m i)
  have hgoodPrepared : ∀ cut,
      (ReferenceActivePhysicalStep.finishFollower prepared.coordinator.downView
        (prepared.followers.followers i) observation).down = some cut →
        ¬ ReferenceDownReception.wrongUniqueAccepted cut := by
    intro cut hcut
    apply hgood cut
    simpa [ReferenceActivePhysicalStep.step,
      ReferenceActivePhysicalStep.PreparedRound.observeFollower,
      prepared, observation] using hcut
  have hfinish :=
    finishFollower_configuration_eq_observe_of_saved_cuts_not_wrongUniqueAccepted
      rate prepared.coordinator.downView (prepared.followers.followers i) observation
      hgoodPrepared
  simpa [ReferenceActivePhysicalStep.step,
    ReferenceActivePhysicalStep.PreparedRound.observeFollower,
    prepared, observation] using hfinish

end Bandits.Support.ReferenceDownReceptionCoupling

end
