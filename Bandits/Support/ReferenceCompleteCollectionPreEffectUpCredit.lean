/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCompleteSuffixFollowerPreservation
public import Bandits.Support.ReferenceCompleteContinuingCollectionFinish

import Lean.Elab.Tactic.Omega

/-!
# Pre-effect credit at a filtered UP sender

Sources: `sources/zip4/manuscript/06_interruptions.tex:64-100,164-177,246-299`,
`sources/zip4/manuscript/04_slow_fast_learner.tex:157-188`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:8-64`.

The producer uses the actual complete physical suffix, the checked current UP
offer, the literal successful recorder/START branch, and local UP acceptance.
It identifies the offered fields with the prepared follower before any
receiver-success result. The credit remains conditional on these local branch
equations and does not assert source-truth coupling or regret closure.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ReferenceCompleteCollectionPreEffectUpCredit

open ConstructorDimensions
open ReferenceActivePhysicalStep

variable {p : Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
variable (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
variable (C_star C_h : ℝ)
variable (source : BootstrapPrivateRoundStreams.SourceInput p)

local notation "R" => ReferenceCompletePhysicalHistory.completeSuffixRecords
  rate source rewards C_star C_h

/-- A nonempty filtered parse is the same record as the checked current offer
from the prepared sender. The raw decoder word is first forced to equal the
current offer by the filter; the accepted codec then round-trips that offer. -/
private theorem effectiveParse_some_is_current_offer
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (started : ReferenceActivePhysicalStep.Ledger rate)
    (U : ReferenceCollectionPhaseHistory.UpRecord p rate)
    (hparse : ReferenceCollectionSegmentExtraction.effectiveParse x started = some U)
    (F : ReferencePrelaunchFollower.State p rate.eta)
    (mu : ActiveFollowerLifecycle.LocalMemory p)
    (hconfiguration :
      ((ReferenceActivePhysicalStep.prepare x).followers.followers
        (ReferenceActivePhysicalStep.upSenderIndex x)).configuration =
        .ordinary F mu) :
    ∃ offered : OrdinaryMessageCodec.UpRecord
        (ReferencePrelaunchFollower.codecParams p rate.eta),
      ActiveFollowerQueueOperation.checkedUpOffer rate.eta
        ((ReferenceActivePhysicalStep.prepare x).followers.followers
          (ReferenceActivePhysicalStep.upSenderIndex x)).follower
        ((ReferenceActivePhysicalStep.prepare x).followers.followers
          (ReferenceActivePhysicalStep.upSenderIndex x)).row
        ((ReferenceActivePhysicalStep.prepare x).followers.followers
          (ReferenceActivePhysicalStep.upSenderIndex x)).activation
        ((ReferenceActivePhysicalStep.prepare x).followers.followers
          (ReferenceActivePhysicalStep.upSenderIndex x)).time F =
          .offer offered ∧ U = offered := by
  let prepared := ReferenceActivePhysicalStep.prepare x
  let i := ReferenceActivePhysicalStep.upSenderIndex x
  let sender := prepared.followers.followers i
  let raw := (CoordinatorUpReception.decoderTransition
    (ReferenceUpReception.receptionInputAtRow rate x.row
      (ReferenceActivePhysicalStep.upInputs prepared started) x.time)).2
  let expected := ReferenceActivePhysicalStep.upExpected prepared
  have hfiltered : CoordinatorUpReception.parseDecoderOutput
      (ReferenceUpReception.filterRawByExpected raw expected) = some U := by
    change CoordinatorUpReception.parseDecoderOutput
      (ReferenceUpReception.filterRawByExpected
        ((CoordinatorUpReception.decoderTransition
          (ReferenceUpReception.receptionInputAtRow rate x.row
            (ReferenceActivePhysicalStep.upInputs prepared started) x.time)).2)
        (ReferenceActivePhysicalStep.upExpected prepared)) = some U at hparse
    exact hparse
  have hrawExpected : raw = expected := by
    by_contra hne
    rw [ReferenceUpReception.filterRawByExpected_eq_none_of_ne raw expected hne]
      at hfiltered
    simp [CoordinatorUpReception.parseDecoderOutput] at hfiltered
    cases hfiltered
  have hparsedExpected : CoordinatorUpReception.parseDecoderOutput expected = some U := by
    rw [ReferenceUpReception.filterRawByExpected_eq_raw_of_eq raw expected hrawExpected]
      at hfiltered
    simpa [raw, expected, hrawExpected] using hfiltered
  have hsenderConfiguration : sender.configuration = .ordinary F mu := by
    simpa [prepared, i, sender] using hconfiguration
  cases hoff : ActiveFollowerQueueOperation.checkedUpOffer rate.eta
      sender.follower sender.row sender.activation sender.time F with
  | failure =>
      have hoff' : ActiveFollowerQueueOperation.checkedUpOffer rate.eta
          ((ReferenceActivePhysicalStep.prepare x).followers.followers
            (ReferenceActivePhysicalStep.upSenderIndex x)).follower
          ((ReferenceActivePhysicalStep.prepare x).followers.followers
            (ReferenceActivePhysicalStep.upSenderIndex x)).row
          ((ReferenceActivePhysicalStep.prepare x).followers.followers
            (ReferenceActivePhysicalStep.upSenderIndex x)).activation
          ((ReferenceActivePhysicalStep.prepare x).followers.followers
            (ReferenceActivePhysicalStep.upSenderIndex x)).time F = .failure := by
        simpa [prepared, i, sender] using hoff
      have hexpected : expected = none := by
        have hcurrent := ReferenceUpReception.currentOfferWord_eq_none_of_checked_nonoffer
          rate x.row i x.time sender (prepared.follower_alignment i).1
          (prepared.follower_alignment i).2.1 (prepared.follower_alignment i).2.2.1
          F mu hsenderConfiguration (Or.inl hoff)
        simpa [expected, ReferenceActivePhysicalStep.upExpected, prepared, i, sender]
          using hcurrent
      rw [hexpected] at hparsedExpected
      change (none : Option (ReferenceCollectionPhaseHistory.UpRecord p rate)) =
        some U at hparsedExpected
      cases hparsedExpected
  | noOffer =>
      have hoff' : ActiveFollowerQueueOperation.checkedUpOffer rate.eta
          ((ReferenceActivePhysicalStep.prepare x).followers.followers
            (ReferenceActivePhysicalStep.upSenderIndex x)).follower
          ((ReferenceActivePhysicalStep.prepare x).followers.followers
            (ReferenceActivePhysicalStep.upSenderIndex x)).row
          ((ReferenceActivePhysicalStep.prepare x).followers.followers
            (ReferenceActivePhysicalStep.upSenderIndex x)).activation
          ((ReferenceActivePhysicalStep.prepare x).followers.followers
            (ReferenceActivePhysicalStep.upSenderIndex x)).time F = .noOffer := by
        simpa [prepared, i, sender] using hoff
      have hexpected : expected = none := by
        have hcurrent := ReferenceUpReception.currentOfferWord_eq_none_of_checked_nonoffer
          rate x.row i x.time sender (prepared.follower_alignment i).1
          (prepared.follower_alignment i).2.1 (prepared.follower_alignment i).2.2.1
          F mu hsenderConfiguration (Or.inr hoff)
        simpa [expected, ReferenceActivePhysicalStep.upExpected, prepared, i, sender]
          using hcurrent
      rw [hexpected] at hparsedExpected
      change (none : Option (ReferenceCollectionPhaseHistory.UpRecord p rate)) =
        some U at hparsedExpected
      cases hparsedExpected
  | offer offered =>
      have hword : expected = some
          ((OrdinaryMessageCodec.wordEquivFlat
            (CoordinatorCollectionLedger.codecParams p rate.eta.val))
            (OrdinaryMessageCodec.encodeUp
              (CoordinatorCollectionLedger.codecParams p rate.eta.val) offered)) := by
        change ReferenceUpReception.currentOfferWord rate x.row i x.time sender
          (prepared.follower_alignment i).1
          (prepared.follower_alignment i).2.1
          (prepared.follower_alignment i).2.2.1 = some _
        exact ReferenceUpReception.currentOfferWord_eq_encoded_offer rate x.row i x.time
          sender (prepared.follower_alignment i).1
          (prepared.follower_alignment i).2.1
          (prepared.follower_alignment i).2.2.1 F mu hconfiguration offered hoff
      have hencodedParse : CoordinatorUpReception.parseDecoderOutput
          (some ((OrdinaryMessageCodec.wordEquivFlat
            (CoordinatorCollectionLedger.codecParams p rate.eta.val))
            (OrdinaryMessageCodec.encodeUp
              (CoordinatorCollectionLedger.codecParams p rate.eta.val) offered))) =
            some offered := by
        change OrdinaryMessageCodec.parseUp
          (CoordinatorCollectionLedger.codecParams p rate.eta.val)
          (some ((OrdinaryMessageCodec.wordEquivFlat
            (CoordinatorCollectionLedger.codecParams p rate.eta.val)).symm
            ((OrdinaryMessageCodec.wordEquivFlat
              (CoordinatorCollectionLedger.codecParams p rate.eta.val))
              (OrdinaryMessageCodec.encodeUp
                (CoordinatorCollectionLedger.codecParams p rate.eta.val) offered)))) =
          some offered
        rw [Equiv.symm_apply_apply]
        exact OrdinaryMessageCodec.parseUp_encode
          (CoordinatorCollectionLedger.codecParams p rate.eta.val) offered
      rw [hword] at hparsedExpected
      have hrecord : U = offered :=
        Option.some.inj (hparsedExpected.symm.trans hencodedParse)
      exact ⟨offered, rfl, hrecord⟩

/-- Source witnesses for the accepted current-UP credit. The sender is the
actual PREPARE follower; its input state, start-round result, and prepared
configuration remain explicit and distinct. The mass estimate is attached to
an earlier installation and retained DOWN of the same payload. -/
theorem complete_filtered_up_pre_effect_credit_witnesses
    (k : Fin (R).length)
    (c : ReferenceCollectionSegmentExtraction.Choice rate)
    (hchoice : ReferenceCollectionSegmentExtraction.choice
      (R[k.val]'k.isLt).input = some c)
    (o : CoordinatorRecordingOperation.Output p)
    (s : ReferenceActivePhysicalStep.Ledger rate)
    (hstart : CoordinatorCollectionLedger.startRound c.preLedger
      ((R[k.val]'k.isLt).input.time.val + 1)
      (ReferenceActivePhysicalStep.collectionEnabled c.preLedger
        (R[k.val]'k.isLt).input.time)
      (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder o) = .success s)
    (U : ReferenceCollectionPhaseHistory.UpRecord p rate)
    (hparse : ReferenceCollectionSegmentExtraction.effectiveParse
      (R[k.val]'k.isLt).input s = some U)
    (hlocal : CoordinatorCollectionLedger.acceptUpCheck s
      (ReferenceActivePhysicalStep.upSenderIndex (R[k.val]'k.isLt).input) U = true) :
    ∃ (b j : Fin (R).length)
      (inputState : ReferencePrelaunchFollower.State p rate.eta)
      (F : ReferencePrelaunchFollower.State p rate.eta)
      (mu : ActiveFollowerLifecycle.LocalMemory p),
      b.val ≤ j.val ∧ j.val < k.val ∧
      ReferenceAssignmentPayloadPersistence.InstallationBirth
        (R[b.val]'b.isLt) c.payload ∧
      ReferenceAssignmentCollectionMassSteps.installedBaseScore
        (R[b.val]'b.isLt) = some c.preLedger.baseScore ∧
      ReferenceAcceptedUpFollowerHistory.RetainedDown
        (R[j.val]'j.isLt)
        (ReferenceActivePhysicalStep.upSenderIndex (R[k.val]'k.isLt).input)
        (c.payload.downRecord
          (ReferenceActivePhysicalStep.upSenderIndex (R[k.val]'k.isLt).input)) ∧
      (R[k.val]'k.isLt).input.state.followers
        (ReferenceActivePhysicalStep.upSenderIndex (R[k.val]'k.isLt).input) =
          .ordinary inputState mu ∧
      ActiveFollowerLifecycle.localStateDomainValid
        inputState ∧
      ActiveFollowerLifecycle.startRound rate.eta
        (R[k.val]'k.isLt).input.time inputState mu = .ok (F, mu) ∧
      (ReferenceFollowerFixedReply.actualChoice (R[k.val]'k.isLt)
        (ReferenceActivePhysicalStep.upSenderIndex (R[k.val]'k.isLt).input)).configuration =
          .ordinary F mu ∧
      ActiveFollowerLifecycle.localStateDomainValid F ∧
      ActiveFollowerDownAcceptance.operationInputDomain p rate F ∧
      F.lastDown = some (c.payload.downRecord
        (ReferenceActivePhysicalStep.upSenderIndex (R[k.val]'k.isLt).input)) ∧
      U.val.sigma = c.preLedger.sigma ∧
      c.preLedger.sigma = c.payload.sigma.val + 1 ∧
      U.val.S = F.S ∧ U.val.delta = F.delta ∧ U.val.q = F.backlog ∧
      c.preLedger.cutoff = FollowerCutoffScan.firstCutoff p rate.eta.val
        c.payload.sigma
        (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
          ((R[k.val]'k.isLt).input.row)) ∧
      (R[k.val]'k.isLt).input.row = source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) ∧
      c.preLedger.baseScore
          (ReferenceActivePhysicalStep.upSenderIndex (R[k.val]'k.isLt).input) +
        F.S + F.backlog ≤
          min (R[k.val]'k.isLt).input.time.val (c.preLedger.cutoff - 1) * D p ∧
      F.delta ≤ D p ∧
      c.preLedger.baseScore
          (ReferenceActivePhysicalStep.upSenderIndex (R[k.val]'k.isLt).input) +
        U.val.S + U.val.q ≤ (c.preLedger.cutoff - 1) * D p ∧
      U.val.delta ≤ D p := by
  let x := (R[k.val]'k.isLt).input
  let i := ReferenceActivePhysicalStep.upSenderIndex x
  obtain ⟨inputState, mu, F, hinput, hinputDomain,
    hpreparedStart, hpreparedChoice, hpreparedDomain, hoperationDomain⟩ :=
    ReferenceCompleteSuffixFollowerPreservation.complete_suffix_follower_choice
      rewards C_star C_h source k i
  have hconfiguration :
      ((ReferenceActivePhysicalStep.prepare x).followers.followers i).configuration =
        .ordinary F mu := by
    change (ReferenceFollowerFixedReply.actualChoice (R[k.val]'k.isLt) i).configuration =
      .ordinary F mu at hpreparedChoice
    rw [ReferenceFollowerFixedReply.actualChoice,
      (R[k.val]'k.isLt).output_eq] at hpreparedChoice
    simpa [ReferenceActivePhysicalStep.step] using hpreparedChoice
  obtain ⟨offered, hoff, hUOffered⟩ := effectiveParse_some_is_current_offer
    x s U hparse F mu hconfiguration
  have hfields := ReferenceUpReception.checkedPreparedOffer_field_equations
    rate x.row i x.time ((ReferenceActivePhysicalStep.prepare x).followers.followers i)
    ((ReferenceActivePhysicalStep.prepare x).follower_alignment i).1
    ((ReferenceActivePhysicalStep.prepare x).follower_alignment i).2.1
    ((ReferenceActivePhysicalStep.prepare x).follower_alignment i).2.2.1
    F mu hconfiguration offered hoff

  have hstartedCandidate := ReferenceActivePhysicalStep.collection_started_candidate
    c.preLedger s x.time
    (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder o) hstart
  have hstartedSigma : s.sigma = c.preLedger.sigma := by
    rw [hstartedCandidate]
    rfl
  have hlocalFields : s.cutoff ≤ s.cursor ∧ i ∈ s.pending ∧ U.val.sigma = s.sigma := by
    simpa [CoordinatorCollectionLedger.acceptUpCheck] using hlocal
  have hUsigma : U.val.sigma = c.preLedger.sigma :=
    hlocalFields.2.2.trans hstartedSigma
  have hprovenance :=
    ReferenceAssignmentRetainedBirthProvenance.complete_collection_choice_birth_provenance
      rate rewards C_star C_h source k c hchoice
  dsimp only at hprovenance
  obtain ⟨bProvenance, hbProvenance, hbirthProvenance, _harm,
    hprovenanceSigma, hprovenanceCutoff, hprovenanceBase⟩ := hprovenance

  have hacceptedStart :
      ReferencePrelaunchFollower.acceptedStart F = c.preLedger.sigma := by
    calc
      ReferencePrelaunchFollower.acceptedStart F = offered.val.sigma := hfields.1.symm
      _ = U.val.sigma := congrArg
        (fun value : OrdinaryMessageCodec.UpRecord
          (ReferencePrelaunchFollower.codecParams p rate.eta) => value.val.sigma)
        hUOffered.symm
      _ = c.preLedger.sigma := hUsigma
  have hsomeLastDown : ∃ M, F.lastDown = some M := by
    cases hlast : F.lastDown with
    | none =>
        have hzero : ReferencePrelaunchFollower.acceptedStart F = 0 := by
          simp [ReferencePrelaunchFollower.acceptedStart, hlast]
        rw [hzero, hprovenanceSigma] at hacceptedStart
        omega
    | some M => exact ⟨M, rfl⟩
  obtain ⟨M, hlast⟩ := hsomeLastDown
  have hmessageSigma : M.val.sigma = c.payload.sigma.val + 1 := by
    calc
      M.val.sigma = ReferencePrelaunchFollower.acceptedStart F := by
        simp [ReferencePrelaunchFollower.acceptedStart, hlast]
      _ = c.preLedger.sigma := hacceptedStart
      _ = c.payload.sigma.val + 1 := hprovenanceSigma

  obtain ⟨bMass, jMass, P, beta, hbjMass, hjkMass, hbirthMass, hbaseMass,
    hretainedMass, hmessage, hmass, hdelta⟩ :=
    ReferenceCompleteOrdinaryFollowerMass.complete_ordinary_follower_choice_mass
      rewards C_star C_h source k i F mu hpreparedChoice M hlast
  have hpayloadSigma : P.sigma.val = c.payload.sigma.val := by
    have hmassSigma := congrArg
      (fun record : OrdinaryMessageCodec.DownRecord
        (ReferencePrelaunchFollower.codecParams p rate.eta) => record.val.sigma)
      hmessage
    rw [P.downRecord_fields i] at hmassSigma
    change M.val.sigma = P.sigma.val + 1 at hmassSigma
    omega
  have hbirthTimeMass := ReferenceAssignmentPayloadChronology.installationBirth_time_eq
    (R[bMass.val]'bMass.isLt) P hbirthMass
  have hbirthTimeProvenance :=
    ReferenceAssignmentPayloadChronology.installationBirth_time_eq
      (R[bProvenance.val]'bProvenance.isLt) c.payload hbirthProvenance
  rw [ReferenceAssignmentFollowerMassSteps.complete_record_time
    rate rewards C_star C_h source bMass] at hbirthTimeMass
  rw [ReferenceAssignmentFollowerMassSteps.complete_record_time
    rate rewards C_star C_h source bProvenance] at hbirthTimeProvenance
  have hbirthIndex : bMass = bProvenance := by
    apply Fin.ext
    omega
  subst bProvenance
  have hpayload : P = c.payload :=
    ReferenceAssignmentPayloadChronology.installationBirth_payload_unique
      (R[bMass.val]'bMass.isLt) P c.payload hbirthMass hbirthProvenance
  have hbaseAtBirth :
      ReferenceAssignmentCollectionMassSteps.installedBaseScore
        (R[bMass.val]'bMass.isLt) = some c.preLedger.baseScore := by
    cases hcoord : (R[bMass.val]'bMass.isLt).output.preparation.coordinator with
    | first outcome =>
        cases outcome <;>
          simp_all only [ReferenceAssignmentCollectionMassSteps.installedBaseScore]
    | live registers owned base outcome =>
        simp_all only [ReferenceAssignmentCollectionMassSteps.installedBaseScore]
    | collection payload ledger clock cutoff outcome =>
        cases outcome <;>
          simp_all only [ReferenceAssignmentCollectionMassSteps.installedBaseScore]
    | invalidCollectionCutoff =>
        simp_all only [ReferenceAssignmentCollectionMassSteps.installedBaseScore]
    | dagger =>
        simp_all only [ReferenceAssignmentCollectionMassSteps.installedBaseScore]
  have hbeta : beta = c.preLedger.baseScore :=
    Option.some.inj (hbaseMass.symm.trans hbaseAtBirth)

  cases hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h with
  | none =>
      have hlength := k.isLt
      simp only [ReferenceCompletePhysicalHistory.completeSuffixRecords, hlaunch,
        dite_true, List.length_nil] at hlength
      omega
  | some active =>
      let start := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
      have hspan : start + (p.T - start) ≤ p.T := by
        have hs := ReferenceCompletePhysicalHistory.physicalStart_le_T
          rate source rewards C_star C_h
        dsimp only [start]
        omega
      let hmode := ReferenceCompletePhysicalHistory.activeMode_of_launch_eq_some
        rate source rewards C_star C_h active hlaunch
      let run := ReferenceActivePhysicalHorizon.run active source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start
        (p.T - start) hspan hmode
      have hrecords : R = run.records := by
        dsimp only [run, start, hmode]
        exact ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
          rate source rewards C_star C_h active hlaunch
      have hrecordMem : (R[k.val]'k.isLt) ∈ run.records := by
        rw [← hrecords]
        exact List.getElem_mem k.isLt
      obtain ⟨hrows, hselected, _hrewards⟩ :=
        ReferenceActivePhysicalHorizon.run_record_inputs active source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
          start (p.T - start) hspan hmode (R[k.val]'k.isLt) hrecordMem
      have hrow : x.row = source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source) := by
        change (R[k.val]'k.isLt).input.rows (R[k.val]'k.isLt).input.selected = _
        rw [hrows, hselected]

      have hmass' := hmass
      rw [hbeta, hpayload, hrow, ← hprovenanceCutoff] at hmass'
      have hbudget :
          c.preLedger.baseScore i + F.S + F.backlog ≤
            (c.preLedger.cutoff - 1) * D p :=
        hmass'.trans (Nat.mul_le_mul_right (D p) (Nat.min_le_right _ _))
      have hmessageCurrent : M = c.payload.downRecord i := by
        simpa only [hpayload] using hmessage
      have hretainedCurrent := hretainedMass
      rw [hmessageCurrent] at hretainedCurrent
      have hlastCurrent : F.lastDown = some (c.payload.downRecord i) := by
        exact hlast.trans (congrArg some hmessageCurrent)
      have hUS : U.val.S = F.S := by
        calc
          U.val.S = offered.val.S := congrArg
            (fun value : OrdinaryMessageCodec.UpRecord
              (ReferencePrelaunchFollower.codecParams p rate.eta) => value.val.S)
            hUOffered
          _ = F.S := hfields.2.1
      have hUdelta : U.val.delta = F.delta := by
        calc
          U.val.delta = offered.val.delta := congrArg
            (fun value : OrdinaryMessageCodec.UpRecord
              (ReferencePrelaunchFollower.codecParams p rate.eta) => value.val.delta)
            hUOffered
          _ = F.delta := hfields.2.2.1
      have hUq : U.val.q = F.backlog := by
        calc
          U.val.q = offered.val.q := congrArg
            (fun value : OrdinaryMessageCodec.UpRecord
              (ReferencePrelaunchFollower.codecParams p rate.eta) => value.val.q)
            hUOffered
          _ = F.backlog := hfields.2.2.2
      have hcutoffRow : c.preLedger.cutoff =
          FollowerCutoffScan.firstCutoff p rate.eta.val c.payload.sigma
            (FollowerCutoffScan.completeRowProposalBit p rate.eta.val x.row) := by
        rw [hrow]
        exact hprovenanceCutoff
      have hcredit : c.preLedger.baseScore i + U.val.S + U.val.q ≤
          (c.preLedger.cutoff - 1) * D p := by
        rw [hUS, hUq]
        exact hbudget
      have hUpDelta : U.val.delta ≤ D p := by
        rw [hUdelta]
        exact hdelta
      refine ⟨bMass, jMass, inputState, F, mu,
        hbjMass, hjkMass, ?_, ?_, ?_, hinput, hinputDomain,
        hpreparedStart, ?_, hpreparedDomain, hoperationDomain,
        hlastCurrent, hUsigma, hprovenanceSigma,
        hUS, hUdelta, hUq, hcutoffRow, hrow, hmass', hdelta, hcredit, hUpDelta⟩
      · simpa only [hpayload] using hbirthMass
      · exact hbaseAtBirth
      · exact hretainedCurrent
      · exact hpreparedChoice

/-- The literal numerical pre-effect service-credit bound and last-service
cap for the actual locally accepted filtered UP sender. -/
theorem complete_filtered_up_pre_effect_credit
    (k : Fin (R).length)
    (c : ReferenceCollectionSegmentExtraction.Choice rate)
    (hchoice : ReferenceCollectionSegmentExtraction.choice
      (R[k.val]'k.isLt).input = some c)
    (o : CoordinatorRecordingOperation.Output p)
    (s : ReferenceActivePhysicalStep.Ledger rate)
    (hstart : CoordinatorCollectionLedger.startRound c.preLedger
      ((R[k.val]'k.isLt).input.time.val + 1)
      (ReferenceActivePhysicalStep.collectionEnabled c.preLedger
        (R[k.val]'k.isLt).input.time)
      (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder o) = .success s)
    (U : ReferenceCollectionPhaseHistory.UpRecord p rate)
    (hparse : ReferenceCollectionSegmentExtraction.effectiveParse
      (R[k.val]'k.isLt).input s = some U)
    (hlocal : CoordinatorCollectionLedger.acceptUpCheck s
      (ReferenceActivePhysicalStep.upSenderIndex (R[k.val]'k.isLt).input) U = true) :
    c.preLedger.baseScore
        (ReferenceActivePhysicalStep.upSenderIndex (R[k.val]'k.isLt).input) +
      U.val.S + U.val.q ≤ (c.preLedger.cutoff - 1) * D p ∧
    U.val.delta ≤ D p := by
  obtain ⟨b, j, inputState, F, mu, _horder, _hbefore,
    _hbirth, _hbase, _hretained, _hinput, _hinputDomain, _hpreparedStart,
    _hpreparedChoice,
    _hpreparedDomain, _hoperationDomain, _hlast, _hUsigma, _hledgerSigma,
    _hS, _hdelta, _hq, _hcutoff, _hrow, _hmass, _hFdelta, hcredit, hdelta⟩ :=
    complete_filtered_up_pre_effect_credit_witnesses
      rate rewards C_star C_h source k c hchoice o s hstart U hparse hlocal
  exact ⟨hcredit, hdelta⟩

end Bandits.Support.ReferenceCompleteCollectionPreEffectUpCredit

end
