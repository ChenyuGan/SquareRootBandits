/-
Copyright (c) 2026 The Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionDownThresholdDetection

/-!
# Physical acceptance at the first-collection DOWN threshold

This module proves the physical consequence of a matching, ordinarily
accepted DOWN word when the actual checked follower operation succeeds.
It makes no threshold-attainment, event, stopping-time, or regret claim.

Sources: `sources/zip4/manuscript/06_interruptions.tex:476-481`,
`sources/zip4/manuscript/05_binary_transport.tex:27-53,100-124`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:139-157`.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions

namespace Bandits.Support.ReferenceFirstCollectionDownPhysicalThreshold

variable {p : Parameters}

/-- A successful actual `recordFollower` call rules out every nonaccepted
result of the same reference cut when the logged state passes the exact
register, decoder, and buffer checks, and its raw word is the expected word
with an ordinarily accepted parse.  In particular, recovery success is
derived by eliminating the real `checkedRecovery` error branch.
-/
theorem actual_physical_result_forces_accepted_cut
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (activation : ReferencePrelaunchFollower.Activation p) (time : Fin p.T)
    (hactive : activation.val ≤ time.val + 1) (arm : Fin p.K)
    (own : ReferencePrelaunchFollower.Observation p)
    (choice logged post : ReferencePrelaunchFollower.State p rate.eta)
    (word : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (message : OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))
    (hselected : ActiveFollowerDownAcceptance.downSelected p i row time)
    (hstatus : choice.status = .unoccupied)
    (hlogging : ActiveFollowerLogging.checkedLogging i row activation time
      (arm, own) choice = .ok logged)
    (hregister : ActiveFollowerDownAcceptance.registerInputDomain p rate logged)
    (hdecoder : ActiveFollowerDownAcceptance.decoderInputDomain p logged.downBatch)
    (hbuffer : ActiveFollowerDownAcceptance.bufferInputDomain p logged.buffer)
    (hrawCurrent : (ReferenceDownReception.referenceDownCut p view i row time own rate logged).raw =
      (ActiveFollowerDownAcceptance.currentDecodeStep p i row time own rate logged).2)
    (hraw : (ReferenceDownReception.referenceDownCut p view i row time own rate logged).raw = some word)
    (hexpected : (ReferenceDownReception.referenceDownCut p view i row time own rate logged).expectedWord =
      some word)
    (hparse : (ReferenceDownReception.referenceDownCut p view i row time own rate logged).ordinaryParse =
      some message)
    (hordinary : (ReferenceDownReception.referenceDownCut p view i row time own rate logged).ordinaryAcceptance)
    (hresult : (ReferenceActivePhysicalStep.recordFollower view i row activation time hactive arm own choice).result =
      .ok post) :
    ∃ after scan registers lastService,
      (ReferenceDownReception.referenceDownCut p view i row time own rate logged).outcome =
        ActiveFollowerDownAcceptance.LocalDownResult.accepted logged after word message
          scan registers lastService ∧
      post = after ∧ post.lastDown = some message := by
  classical
  let cut := ReferenceDownReception.referenceDownCut p view i row time own rate logged
  have hloggedStatus : logged.status = .unoccupied := by
    have hframe := ActiveFollowerLogging.checkedLogging_success_frame i row activation time
      (arm, own) choice logged hlogging
    exact hframe.2.2.2.2.1.trans hstatus
  have hconsume : DeclaredFollowerLocalRound.consumeDownResult rate cut.outcome = .ok post := by
    simpa only [ReferenceActivePhysicalStep.recordFollower, dif_pos hstatus, hlogging,
      cut] using hresult
  have hdecoded : (ActiveFollowerDownAcceptance.currentDecodeStep p i row time own rate logged).2 =
      some word := hrawCurrent.symm.trans hraw
  have hexpected' : ReferenceDownReception.expectedDownFlatWord view i row time = some word := by
    by_cases hmatches : (ActiveFollowerDownAcceptance.currentDecodeStep
        p i row time own rate logged).2 = ReferenceDownReception.expectedDownFlatWord view i row time
    · simpa [ReferenceDownReception.referenceDownCut, hselected, hloggedStatus,
        hregister, hdecoder, hbuffer, hmatches] using hexpected
    · simpa [ReferenceDownReception.referenceDownCut, hselected, hloggedStatus,
        hregister, hdecoder, hbuffer, hmatches] using hexpected
  have hmatched : (ActiveFollowerDownAcceptance.currentDecodeStep p i row time own rate logged).2 =
      ReferenceDownReception.expectedDownFlatWord view i row time := by
    rw [hdecoded]
    exact hexpected'.symm
  have hparseDecoded : ReferenceDownReception.ordinaryParse p rate
      (ActiveFollowerDownAcceptance.currentDecodeStep p i row time own rate logged).2 =
        some message := by
    by_cases hmatches : (ActiveFollowerDownAcceptance.currentDecodeStep
        p i row time own rate logged).2 = ReferenceDownReception.expectedDownFlatWord view i row time
    · simpa [ReferenceDownReception.referenceDownCut, hselected, hloggedStatus,
        hregister, hdecoder, hbuffer, hmatches] using hparse
    · simpa [ReferenceDownReception.referenceDownCut, hselected, hloggedStatus,
        hregister, hdecoder, hbuffer, hmatches] using hparse
  have hparseExpected : ReferenceDownReception.ordinaryParse p rate
      (ReferenceDownReception.expectedDownFlatWord view i row time) = some message := by
    rw [← hmatched]
    exact hparseDecoded
  have hparseWord : ReferenceDownReception.ordinaryParse p rate (some word) = some message := by
    simpa only [hdecoded] using hparseDecoded
  have haccepted : OrdinaryMessageCodec.acceptDown
      (ReferencePrelaunchFollower.codecParams p rate.eta)
      (ReferencePrelaunchFollower.acceptedStart logged) (time.val + 1) message := by
    have htest : cut.ordinaryAcceptance =
        OrdinaryMessageCodec.acceptDown (ReferencePrelaunchFollower.codecParams p rate.eta)
          (ReferencePrelaunchFollower.acceptedStart logged) (time.val + 1) message := by
      by_cases hmatches : (ActiveFollowerDownAcceptance.currentDecodeStep
          p i row time own rate logged).2 = ReferenceDownReception.expectedDownFlatWord view i row time
      · simp [cut, ReferenceDownReception.referenceDownCut, hselected, hloggedStatus,
          hregister, hdecoder, hbuffer, hmatches,
          ReferenceDownReception.ordinaryLocalAcceptanceTest, hparseExpected]
      · simp [cut, ReferenceDownReception.referenceDownCut, hselected, hloggedStatus,
          hregister, hdecoder, hbuffer, hmatches,
          ReferenceDownReception.ordinaryLocalAcceptanceTest, hparseDecoded]
    rw [htest] at hordinary
    exact hordinary
  let scan := ActiveFollowerDownAcceptance.acceptedCutoffScan p rate message time
    (ActiveFollowerDownAcceptance.acceptedDownStartLE p rate message time logged haccepted) row
  cases hrecovery : ActiveFollowerDownAcceptance.checkedRecovery p rate message logged scan.endpoint with
  | error failure =>
      have houtcome : cut.outcome = ActiveFollowerDownAcceptance.LocalDownResult.outputFailure
          logged (.replay failure) := by
        simp [cut, ReferenceDownReception.referenceDownCut, hselected, hloggedStatus,
          hregister, hdecoder, hbuffer, hmatched, hexpected', hparseExpected, hparseWord, haccepted,
          scan, hrecovery]
      simp [houtcome, hrecovery, DeclaredFollowerLocalRound.consumeDownResult] at hconsume
  | ok recovered =>
      let after : ReferencePrelaunchFollower.State p rate.eta :=
        { { logged with downBatch :=
              (ActiveFollowerDownAcceptance.currentDecodeStep p i row time own rate logged).1 } with
          lastDown := some message
          S := recovered.registers.1
          delta := recovered.lastService
          backlog := recovered.registers.2
          status := if scan.endpoint = time.val + 2 then .pending else .unoccupied
          buffer := [] }
      have houtcome : cut.outcome = ActiveFollowerDownAcceptance.LocalDownResult.accepted
          logged after word message scan recovered.registers recovered.lastService := by
        simp [cut, ReferenceDownReception.referenceDownCut, hselected, hloggedStatus,
          hregister, hdecoder, hbuffer, hmatched, hexpected', hparseExpected, hparseWord, haccepted,
          scan, hrecovery, after, hdecoded]
      have hpost : post = after := by
        have hstates : after = post := by
          have heq : (Except.ok after : Except DeclaredFollowerLocalRound.RoundFailure
              (ReferencePrelaunchFollower.State p rate.eta)) =
              (Except.ok post : Except DeclaredFollowerLocalRound.RoundFailure
                (ReferencePrelaunchFollower.State p rate.eta)) := by
            simpa [houtcome, DeclaredFollowerLocalRound.consumeDownResult] using hconsume
          exact Except.ok.inj heq
        exact hstates.symm
      refine ⟨after, scan, recovered.registers, recovered.lastService, houtcome, hpost, ?_⟩
      rw [hpost]

end Bandits.Support.ReferenceFirstCollectionDownPhysicalThreshold
