/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCompleteOrdinaryFollowerMass

import Lean.Elab.Tactic.Omega

/-!
# Numerical credit at an actually accepted UP

This composes the actual accepted-UP birth join with the public ordinary-input
mass producer. The installation, payload, base vector, and retained DOWN are
kept as the same historical witnesses. It proves a local numerical bound for
the actual collection branch only.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ReferenceCompleteAcceptedUpBaseCredit

open ConstructorDimensions
open ReferenceActivePhysicalStep
open ReferenceActivePhysicalHorizon

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

/-- An accepted UP has the numerical credit of the same actual installation
that produced the retained DOWN. The row and time are those of the original
complete suffix record; no sender output or historical score premise is
supplied. -/
theorem complete_accepted_up_base_credit
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (c : ReferenceCollectionSegmentExtraction.Choice rate)
    (hchoice : ReferenceCollectionSegmentExtraction.choice
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val]'k.isLt).input = some c)
    (i : Fin (p.m - 1)) (U : ReferenceCollectionPhaseHistory.UpRecord p rate)
    (haccepted : ReferenceCollectionPhaseHistory.AcceptedUp
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val]'k.isLt).input i U) :
    let R : List (ReferenceActivePhysicalHorizon.RoundRecord
      (p := p) (rate := rate)) :=
      ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
    ∃ (b j : Fin R.length) (F : ReferencePrelaunchFollower.State p rate.eta)
      (mu : ActiveFollowerLifecycle.LocalMemory p),
      b.val ≤ j.val ∧ j.val < k.val ∧
      ReferenceAssignmentPayloadPersistence.InstallationBirth R[b.val] c.payload ∧
      ReferenceAssignmentCollectionMassSteps.installedBaseScore R[b.val] =
        some c.preLedger.baseScore ∧
      ReferenceAcceptedUpFollowerHistory.RetainedDown R[j.val] i
        (c.payload.downRecord i) ∧
      R[k.val].input.state.followers i = .ordinary F mu ∧
      F.lastDown = some (c.payload.downRecord i) ∧
      U.val.sigma = c.preLedger.sigma ∧
      c.preLedger.sigma = c.payload.sigma.val + 1 ∧
      U.val.S = F.S ∧ U.val.delta = F.delta ∧ U.val.q = F.backlog ∧
      c.preLedger.baseScore i + F.S + F.backlog ≤
        min R[k.val].input.time.val (c.preLedger.cutoff - 1) * D p ∧
      F.delta ≤ D p ∧
      c.preLedger.baseScore i + U.val.S + U.val.q ≤
        (c.preLedger.cutoff - 1) * D p ∧
      U.val.delta ≤ D p := by
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
  obtain ⟨bJoin, _jJoin, F, mu, _hJoinOrder, _hJoinBefore, hbirthJoin,
    _hretainedJoin, hinput, hlast, hUsigma, hledgerSigma, hUS, hUdelta,
    hUq, hcutoff, hbaseJoin⟩ :=
    ReferenceAcceptedUpAssignmentBirthJoin.complete_accepted_up_birth_join
      rate rewards C_star C_h source k c hchoice i U haccepted
  obtain ⟨bMass, jMass, P, beta, hbMass, hjMass, hbirthMass, hbaseMass,
    hretainedMass, hmessage, hmass, hdelta⟩ :=
    ReferenceCompleteOrdinaryFollowerMass.complete_ordinary_follower_input_mass
      rewards C_star C_h source k i F mu hinput (c.payload.downRecord i) hlast

  have hpayloadSigma : P.sigma.val = c.payload.sigma.val := by
    have heq := congrArg
      (fun record : OrdinaryMessageCodec.DownRecord
        (ReferencePrelaunchFollower.codecParams p rate.eta) => record.val.sigma)
      hmessage
    rw [P.downRecord_fields i, c.payload.downRecord_fields i] at heq
    change c.payload.sigma.val + 1 = P.sigma.val + 1 at heq
    omega

  have hbirthTimeMass := ReferenceAssignmentPayloadChronology.installationBirth_time_eq
    (R[bMass.val]) P hbirthMass
  have hbirthTimeJoin := ReferenceAssignmentPayloadChronology.installationBirth_time_eq
    (R[bJoin.val]) c.payload hbirthJoin
  rw [ReferenceAssignmentFollowerMassSteps.complete_record_time
    rate rewards C_star C_h source bMass] at hbirthTimeMass
  rw [ReferenceAssignmentFollowerMassSteps.complete_record_time
    rate rewards C_star C_h source bJoin] at hbirthTimeJoin
  have hbirthIndex : bMass = bJoin := by
    apply Fin.ext
    omega
  subst bJoin

  have hpayload : P = c.payload :=
    ReferenceAssignmentPayloadChronology.installationBirth_payload_unique
      (R[bMass.val]) P c.payload hbirthMass hbirthJoin
  have hbaseAtBirth :
      ReferenceAssignmentCollectionMassSteps.installedBaseScore R[bMass.val] =
        some c.preLedger.baseScore := by
    cases hcoord : R[bMass.val].output.preparation.coordinator with
    | first outcome =>
        cases outcome <;>
          simp_all only [R, ReferenceAssignmentCollectionMassSteps.installedBaseScore]
    | live registers owned base outcome =>
        simp_all only [R, ReferenceAssignmentCollectionMassSteps.installedBaseScore]
    | collection payload ledger clock cutoff outcome =>
        cases outcome <;>
          simp_all only [R, ReferenceAssignmentCollectionMassSteps.installedBaseScore]
    | invalidCollectionCutoff =>
        simp_all only [R, ReferenceAssignmentCollectionMassSteps.installedBaseScore]
    | dagger =>
        simp_all only [R, ReferenceAssignmentCollectionMassSteps.installedBaseScore]
  have hbeta : beta = c.preLedger.baseScore :=
    Option.some.inj (hbaseMass.symm.trans hbaseAtBirth)

  cases hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h with
  | none =>
      have hindex : k.val < ([] : List
          (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))).length := by
        simpa [ReferenceCompletePhysicalHistory.completeSuffixRecords, hlaunch] using k.isLt
      simp at hindex
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
        dsimp only [R, run, start, hmode]
        exact ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
          rate source rewards C_star C_h active hlaunch
      have hrecordMem : R[k.val] ∈ run.records := by
        rw [← hrecords]
        exact List.getElem_mem k.isLt
      obtain ⟨hrows, hselected, _hrewards⟩ :=
        ReferenceActivePhysicalHorizon.run_record_inputs active source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
          start (p.T - start) hspan hmode (R[k.val]) hrecordMem
      have hrow : R[k.val].input.row =
          source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) := by
        change R[k.val].input.rows R[k.val].input.selected = _
        rw [hrows, hselected]

      have hmass' := hmass
      rw [hbeta, hpayload, hrow, ← hcutoff] at hmass'
      have hbudget : c.preLedger.baseScore i + F.S + F.backlog ≤
          (c.preLedger.cutoff - 1) * D p :=
        hmass'.trans (Nat.mul_le_mul_right (D p) (Nat.min_le_right _ _))
      refine ⟨bMass, jMass, F, mu, hbMass, hjMass, ?_, ?_, hretainedMass,
        hinput, hlast, hUsigma, hledgerSigma, hUS, hUdelta, hUq, hmass',
        hdelta, ?_, ?_⟩
      · simpa only [hpayload] using hbirthMass
      · exact hbaseAtBirth
      · rw [hUS, hUq]
        exact hbudget
      · rw [hUdelta]
        exact hdelta

end Bandits.Support.ReferenceCompleteAcceptedUpBaseCredit

end
