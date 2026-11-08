/-
Copyright (c) 2026 The Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.CoordinatorCollectionLedger
public import Bandits.Support.CoordinatorUpReception
public import Bandits.Support.ReferenceActivePhysicalStep
public import Bandits.Support.ReferenceUpReception

/-!
# Coupling checked reference UP reception to the ordinary receiver

This file proves a deterministic, one-decision comparison for the existing
checked receivers. Its operational claim follows
`sources/zip4/manuscript/06_interruptions.tex:123-177,235-297`,
`sources/zip4/manuscript/08_main_theorem.tex:29-42,67-75`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:6-14`.

The condition excludes a unique mismatching decoded word that also passes the
literal local acceptance check. It does not require equality of raw outputs,
successful reception, or correct offered scores. The result preserves the
ordinary decoder bank transition and the exact ledger rejection or acceptance
behavior.
-/

@[expose] public section

namespace Bandits.Support.ReferenceUpReceptionCoupling

open Bandits.Support.ActiveFollowerDownAcceptance
open Bandits.Support.AffineBatchDecoder
open Bandits.Support.AffineChannelLaw
open Bandits.Support.CompletePublicTable
open Bandits.Support.ConstructorDimensions
open Bandits.Support.CoordinatorCollectionLedger
open Bandits.Support.CoordinatorUpReception
open Bandits.Support.DeclaredFollowerLocalRound
open Bandits.Support.OrdinaryMessageCodec
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceUpReception

variable {p : ConstructorDimensions.Parameters}

/-- If the actual unique raw output is not both mismatching and locally
accepted, filtering the current UP offer has exactly the ordinary checked
receiver result. The raw option itself may differ from the expected option.
-/
theorem receiveUpFilteredAtRow_eq_receiveUp_of_no_wrong_unique_accepted
    (rate : ActiveFollowerDownAcceptance.RateInput p)
    (row : CompletePublicTable.CompleteRow p)
    (inputs : ReferenceUpReception.ReceptionLocalInputs rate) (t : Fin p.T)
    (prepared : DeclaredFollowerLocalRound.PreparedRound p rate)
    (hrow : prepared.row = row)
    (hfollower : prepared.follower =
      (ReferenceUpReception.receptionInputAtRow rate row inputs t).selectedFollower)
    (htime : prepared.time =
      (ReferenceUpReception.receptionInputAtRow rate row inputs t).time)
    (hinputTime : inputs.2.2.1 = t)
    (hwrong : ReferenceUpReception.wrongUniqueAndLocalAcceptanceAtRow rate row inputs t
      prepared hrow hfollower htime hinputTime = false) :
    ReferenceUpReception.receiveUpFilteredAtRow rate row inputs t prepared
        hrow hfollower htime hinputTime =
      CoordinatorUpReception.receiveUp
        (ReferenceUpReception.receptionInputAtRow rate row inputs t) := by
  classical
  let input := ReferenceUpReception.receptionInputAtRow rate row inputs t
  cases hcheck : CoordinatorUpReception.receptionInputCheck input with
  | false =>
      simp [ReferenceUpReception.receiveUpFilteredAtRow, input, hcheck,
        CoordinatorUpReception.receiveUp]
  | true =>
      have hdomain : CoordinatorUpReception.receptionInputDomain input :=
        (CoordinatorUpReception.receptionInputCheck_eq_true_iff input).mp hcheck
      have hfiltered := ReferenceUpReception.receiveUpFilteredAtRow_eq_filtered_decode
        rate row inputs t prepared hrow hfollower htime hinputTime hcheck
      have hordinary := CoordinatorUpReception.receiveUp_eq_existing_decodeUp input hcheck
      rw [hfiltered, hordinary]
      change
        CoordinatorUpReception.packDecodeResult
            (CoordinatorCollectionLedger.decodeUp input.ledger input.selectedFollower
              (CoordinatorUpReception.parseDecoderOutput
                (ReferenceUpReception.filterRawByExpected
                  (CoordinatorUpReception.decoderTransition input).2
                  (ReferenceUpReception.currentOfferWord rate row input.selectedFollower
                    input.time prepared hrow hfollower htime))))
            (CoordinatorUpReception.decoderBankAfter input) =
          CoordinatorUpReception.packDecodeResult
            (CoordinatorCollectionLedger.decodeUp input.ledger input.selectedFollower
              (CoordinatorUpReception.parseDecoderOutput
                (CoordinatorUpReception.decoderTransition input).2))
            (CoordinatorUpReception.decoderBankAfter input)
      have hdecode :
          CoordinatorCollectionLedger.decodeUp input.ledger input.selectedFollower
              (CoordinatorUpReception.parseDecoderOutput
                (ReferenceUpReception.filterRawByExpected
                  (CoordinatorUpReception.decoderTransition input).2
                  (ReferenceUpReception.currentOfferWord rate row input.selectedFollower
                    input.time prepared hrow hfollower htime))) =
            CoordinatorCollectionLedger.decodeUp input.ledger input.selectedFollower
              (CoordinatorUpReception.parseDecoderOutput
                (CoordinatorUpReception.decoderTransition input).2) := by
        cases hraw : (CoordinatorUpReception.decoderTransition input).2 with
        | none =>
            simp [ReferenceUpReception.filterRawByExpected,
            CoordinatorUpReception.parseDecoderOutput]
        | some word =>
            by_cases hmatch : some word =
                ReferenceUpReception.currentOfferWord rate row input.selectedFollower
                  input.time prepared hrow hfollower htime
            · have hfiltered :
                  ReferenceUpReception.filterRawByExpected (some word)
                    (ReferenceUpReception.currentOfferWord rate row input.selectedFollower
                      input.time prepared hrow hfollower htime) = some word :=
                ReferenceUpReception.filterRawByExpected_eq_raw_of_eq _ _ hmatch
              rw [hfiltered]
            · have hmismatch : (some word : Option
                  (AffineChannelLaw.Word (AffineBatchDecoder.width p))) ≠
                    ReferenceUpReception.currentOfferWord rate row input.selectedFollower
                      input.time prepared hrow hfollower htime := hmatch
              cases hparse : CoordinatorUpReception.parseDecoderOutput (some word) with
              | none =>
                  have hfiltered :
                      ReferenceUpReception.filterRawByExpected (some word)
                        (ReferenceUpReception.currentOfferWord rate row input.selectedFollower
                          input.time prepared hrow hfollower htime) = none :=
                    ReferenceUpReception.filterRawByExpected_eq_none_of_ne _ _ hmismatch
                  rw [hfiltered]
                  rfl
              | some record =>
                  by_cases haccepted : CoordinatorCollectionLedger.acceptUpCheck
                      input.ledger input.selectedFollower record = true
                  · have hflag : ReferenceUpReception.wrongUniqueAndLocalAcceptanceAtRow
                        rate row inputs t prepared hrow hfollower htime hinputTime = true := by
                      apply (ReferenceUpReception.wrongUniqueAndLocalAcceptanceAtRow_eq_true_iff
                        rate row inputs t prepared hrow hfollower htime hinputTime).2
                      exact ⟨word, record, by simpa [input] using hraw, hparse,
                        by simpa [input] using haccepted,
                        by simpa [input] using hmismatch⟩
                    rw [hwrong] at hflag
                    cases hflag
                  · have hnotAccepted : ¬ CoordinatorCollectionLedger.acceptUpCheck
                        input.ledger input.selectedFollower record := haccepted
                    have hfiltered :
                        ReferenceUpReception.filterRawByExpected (some word)
                          (ReferenceUpReception.currentOfferWord rate row input.selectedFollower
                            input.time prepared hrow hfollower htime) = none :=
                      ReferenceUpReception.filterRawByExpected_eq_none_of_ne _ _ hmismatch
                    have hfilteredParse :
                        CoordinatorUpReception.parseDecoderOutput (p := p)
                          (eta := rate.eta.val)
                          (ReferenceUpReception.filterRawByExpected (some word)
                            (ReferenceUpReception.currentOfferWord rate row input.selectedFollower
                              input.time prepared hrow hfollower htime)) =
                          (none : Option (OrdinaryMessageCodec.UpRecord
                            (CoordinatorCollectionLedger.codecParams p rate.eta.val))) := by
                      rw [hfiltered]
                      rfl
                    have hnone := CoordinatorUpReception.decodeUp_none_rejected input hdomain
                    have hunaccepted := CoordinatorUpReception.decodeUp_unaccepted_rejected
                      input hdomain record hnotAccepted
                    rw [hfilteredParse, hnone, hunaccepted]
      exact congrArg (fun decoded =>
        CoordinatorUpReception.packDecodeResult decoded
          (CoordinatorUpReception.decoderBankAfter input)) hdecode

variable {rate : ReferenceActivePhysicalStep.RateInput p}

/-- The physical step's saved diagnostics are the only condition. An absent
diagnostic, including the invalid-input branch, satisfies this implication
vacuously. The result uses the step's actual prepared sender, alignment, ledger,
and bank.
-/
theorem receiveUp_eq_ordinary_of_no_saved_wrong_unique_accepted
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (hdiagnostics : ∀ d : ReferenceActivePhysicalStep.UpDiagnostic p rate,
      (ReferenceActivePhysicalStep.receiveUp prepared ledger).diagnostic = some d →
        d.wrongUniqueAccepted = false) :
    (ReferenceActivePhysicalStep.receiveUp prepared ledger).result =
      CoordinatorUpReception.receiveUp
        (ReferenceUpReception.receptionInputAtRow rate x.row
          (ReferenceActivePhysicalStep.upInputs prepared ledger) x.time) := by
  classical
  let inputs := ReferenceActivePhysicalStep.upInputs prepared ledger
  let input := ReferenceUpReception.receptionInputAtRow rate x.row inputs x.time
  let sender := prepared.followers.followers
    (ReferenceActivePhysicalStep.upSenderIndex x)
  have hrow : sender.row = x.row := (prepared.follower_alignment _).1
  have hplayer : sender.follower = input.selectedFollower :=
    (prepared.follower_alignment _).2.1
  have htime : sender.time = input.time :=
    (prepared.follower_alignment _).2.2.1
  change ReferenceUpReception.receiveUpFilteredAtRow rate x.row inputs x.time
      sender hrow hplayer htime rfl = CoordinatorUpReception.receiveUp input
  cases hcheck : CoordinatorUpReception.receptionInputCheck input with
  | false =>
      simp [ReferenceUpReception.receiveUpFilteredAtRow, input, hcheck,
        CoordinatorUpReception.receiveUp]
  | true =>
      let wrong := ReferenceUpReception.wrongUniqueAndLocalAcceptanceAtRow rate x.row
        inputs x.time sender hrow hplayer htime rfl
      have hcheckActual : CoordinatorUpReception.receptionInputCheck
          (ReferenceUpReception.receptionInputAtRow rate x.row
            (ReferenceActivePhysicalStep.upInputs prepared ledger) x.time) = true := by
        simpa [inputs, input] using hcheck
      have hdiagnostic :
          ((ReferenceActivePhysicalStep.receiveUp prepared ledger).diagnostic.map
            (fun d => d.wrongUniqueAccepted)) = some wrong := by
        simp only [ReferenceActivePhysicalStep.receiveUp, hcheckActual]
        rfl
      have hwrong : wrong = false := by
        cases hdiag : (ReferenceActivePhysicalStep.receiveUp prepared ledger).diagnostic with
        | none =>
            simp [hdiag] at hdiagnostic
        | some d =>
            have hfield : d.wrongUniqueAccepted = wrong := by
              simpa [hdiag] using hdiagnostic
            exact hfield.symm.trans (hdiagnostics d hdiag)
      exact receiveUpFilteredAtRow_eq_receiveUp_of_no_wrong_unique_accepted
        rate x.row inputs x.time sender hrow hplayer htime rfl hwrong

/-- Collection finishing commutes with replacing the actual reception result
by its ordinary receiver result under the saved-diagnostic condition. The
original diagnostic and every actual finish output remain the ones produced by
`collectionFinish`; this theorem introduces no parallel round transition.
-/
theorem collectionFinish_eq_with_ordinary_up_result
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (recording : CoordinatorRecordingOperation.Output p)
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (hdiagnostics : ∀ d : ReferenceActivePhysicalStep.UpDiagnostic p rate,
      (ReferenceActivePhysicalStep.receiveUp prepared ledger).diagnostic = some d →
        d.wrongUniqueAccepted = false) :
    ReferenceActivePhysicalStep.collectionFinish (x := x) payload started recording
        (ReferenceActivePhysicalStep.receiveUp prepared ledger) =
      ReferenceActivePhysicalStep.collectionFinish (x := x) payload started recording
        { (ReferenceActivePhysicalStep.receiveUp prepared ledger) with
          result := CoordinatorUpReception.receiveUp
            (ReferenceUpReception.receptionInputAtRow rate x.row
              (ReferenceActivePhysicalStep.upInputs prepared ledger) x.time) } := by
  have hresult := receiveUp_eq_ordinary_of_no_saved_wrong_unique_accepted
    prepared ledger hdiagnostics
  have hcut :
      ReferenceActivePhysicalStep.receiveUp prepared ledger =
        { (ReferenceActivePhysicalStep.receiveUp prepared ledger) with
          result := CoordinatorUpReception.receiveUp
            (ReferenceUpReception.receptionInputAtRow rate x.row
              (ReferenceActivePhysicalStep.upInputs prepared ledger) x.time) } := by
    cases hactual : ReferenceActivePhysicalStep.receiveUp prepared ledger with
    | mk result diagnostic =>
        have hresult' : result = CoordinatorUpReception.receiveUp
            (ReferenceUpReception.receptionInputAtRow rate x.row
              (ReferenceActivePhysicalStep.upInputs prepared ledger) x.time) := by
          simpa [hactual] using hresult
        cases hresult'
        rfl
  exact congrArg
    (ReferenceActivePhysicalStep.collectionFinish (x := x) payload started recording) hcut

end Bandits.Support.ReferenceUpReceptionCoupling

end
