/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceAllKnownCollectionStartDomains

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Actual all-known checked sample and installation

At a local empty-pending collection boundary, this module classifies the same
checked reconstruction, checked assignment sample, and dispatcher call already
present in the project. Corrected reconstruction underflow and corrected
prefix probability failures remain literal alternatives; renewal reaches the
actual chosen installation. The original-source first-admission constructor
is a separate next task. All physical mass and service bounds here are overt
local inputs; stored scores are not identified with physical calendar scores.

Mathematical sources: `sources/zip4/manuscript/06_interruptions.tex:9-100,
246-299`, `sources/zip4/manuscript/appendix_a_local_protocol.tex:28-82`, and
`sources/zip4/manuscript/04_slow_fast_learner.tex:7-37,97-174,219-243`.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions

namespace Bandits.Support.ReferenceAllKnownCollectionSampleInstall

private theorem rawInitialMass_eq_one
    {K m : ℕ} (mass : PrefixSetSampler.SetCarrier K m → ℝ)
    (hsum : (∑ s : PrefixSetSampler.SetCarrier K m, mass s) = 1) :
    CheckedPrefixSampler.rawStateMass mass
    (PrefixSetSampler.initialState K m) = 1 := by
  simpa [CheckedPrefixSampler.rawStateMass,
    PrefixSetSampler.initialState, PrefixMassPartition.totalMass] using hsum

private theorem runCheckedPrefix_failure_has_predecessor
    {K m : ℕ} (mass : PrefixSetSampler.SetCarrier K m → ℝ)
    (values : Fin K → PrefixSetSampler.UnitScalar) :
    ∀ (n : ℕ) (hn : n ≤ K) (arm : Fin K)
      (reason : CheckedPrefixSampler.FailureReason),
      CheckedPrefixSampler.runCheckedPrefix mass values n hn =
        .failed arm reason →
      ∃ state : PrefixSetSampler.PrefixState K m,
        CheckedPrefixSampler.runCheckedPrefix mass values arm.val
          (Nat.le_of_lt arm.isLt) = .ready state ∧
        CheckedPrefixSampler.checkedStep mass
          (values arm) state arm = .failed arm reason := by
  intro n
  induction n with
  | zero =>
      intro hn arm reason hfail
      simp only [CheckedPrefixSampler.runCheckedPrefix] at hfail
      cases hfail
  | succ n ih =>
      intro hn arm reason hfail
      have hn' : n ≤ K := Nat.le_trans (Nat.le_succ n) hn
      change CheckedPrefixSampler.checkedTransition mass
          ⟨n, Nat.lt_of_succ_le hn⟩
          (CheckedPrefixSampler.runCheckedPrefix mass values n hn',
            values ⟨n, Nat.lt_of_succ_le hn⟩) = .failed arm reason at hfail
      cases hprev : CheckedPrefixSampler.runCheckedPrefix mass values n hn' with
      | failed failedArm failedReason =>
          simp only [CheckedPrefixSampler.checkedTransition, hprev] at hfail
          injection hfail with harm hreason
          subst arm
          subst reason
          obtain ⟨state, hready, hstep⟩ := ih hn' failedArm failedReason hprev
          exact ⟨state, hready, hstep⟩
      | ready state =>
          have hstep : CheckedPrefixSampler.checkedStep mass
              (values ⟨n, Nat.lt_of_succ_le hn⟩) state
              ⟨n, Nat.lt_of_succ_le hn⟩ = .failed arm reason := by
            simpa only [CheckedPrefixSampler.checkedTransition, hprev] using hfail
          have harm : arm = ⟨n, Nat.lt_of_succ_le hn⟩ := by
            cases reason <;>
              unfold CheckedPrefixSampler.checkedStep at hstep <;>
              split_ifs at hstep <;> cases hstep <;> rfl
          subst arm
          refine ⟨state, ?_, ?_⟩
          · change CheckedPrefixSampler.runCheckedPrefix mass values n hn' =
              .ready state
            exact hprev
          · simpa only using hstep

private theorem checkedSample_failure_has_first_ratio
    {K m : ℕ} (mass : PrefixSetSampler.SetCarrier K m → ℝ)
    (values : Fin K → PrefixSetSampler.UnitScalar)
    (hsum : (∑ s : PrefixSetSampler.SetCarrier K m, mass s) = 1)
    (hK : 0 < K)
    (arm : Fin K) (reason : CheckedPrefixSampler.FailureReason)
    (hfail : CheckedPrefixSampler.checkedSample mass values =
      .failed (some arm) reason) :

    ∃ state : PrefixSetSampler.PrefixState K m,
      CheckedPrefixSampler.runCheckedPrefix mass values arm.val
        (Nat.le_of_lt arm.isLt) = .ready state ∧
      CheckedPrefixSampler.checkedStep mass (values arm) state arm =
        .failed arm reason ∧
      0 < CheckedPrefixSampler.rawStateMass mass state ∧
      ((reason = .probabilityBelowZero ∧
          CheckedPrefixSampler.rawIncludedMass mass state arm /
            CheckedPrefixSampler.rawStateMass mass state < 0) ∨
       (reason = .probabilityAboveOne ∧
          1 < CheckedPrefixSampler.rawIncludedMass mass state arm /
            CheckedPrefixSampler.rawStateMass mass state)) := by
  have hinitial : 0 < CheckedPrefixSampler.rawStateMass mass
    (PrefixSetSampler.initialState K m) := by
    rw [rawInitialMass_eq_one mass hsum]
    norm_num
  unfold CheckedPrefixSampler.checkedSample at hfail
  cases hrun : CheckedPrefixSampler.runCheckedPrefix mass values K le_rfl with
  | failed failedArm failedReason =>
      simp [CheckedPrefixSampler.finishOutput, hrun] at hfail
      rcases hfail with ⟨hfailedArm, hfailedReason⟩
      subst failedArm
      subst failedReason
      obtain ⟨state, hready, hstep⟩ :=
        runCheckedPrefix_failure_has_predecessor mass values K le_rfl arm reason hrun
      have hpos : 0 < CheckedPrefixSampler.rawStateMass mass state := by
        have hspec := CheckedPrefixSampler.runCheckedPrefix_ready_specs mass values
          arm.val (Nat.le_of_lt arm.isLt) state hready
        rcases hspec.2.2.2 with hzero | hpos
        · have hstate : state = PrefixSetSampler.initialState K m := by
            simp only [hzero, CheckedPrefixSampler.runCheckedPrefix] at hready
            injection hready with hstate
            exact hstate.symm
          rw [hstate]
          exact hinitial
        · exact hpos
      let ratio := CheckedPrefixSampler.rawIncludedMass mass state arm /
        CheckedPrefixSampler.rawStateMass mass state
      refine ⟨state, hready, hstep, hpos, ?_⟩
      by_cases hlow : 0 ≤ ratio
      · by_cases hup : ratio ≤ 1
        · by_cases hbranch : CheckedPrefixSampler.rawIncludedMass mass state arm >
              (values arm).1 * CheckedPrefixSampler.rawStateMass mass state
          · rw [CheckedPrefixSampler.checkedStep_ready_in mass
              (values arm) state arm hpos hlow hup hbranch] at hstep
            cases hstep
          · rw [CheckedPrefixSampler.checkedStep_ready_out mass
              (values arm) state arm hpos hlow hup hbranch] at hstep
            cases hstep
        · rw [CheckedPrefixSampler.checkedStep_probability_above_one mass
            (values arm) state arm hpos hlow hup] at hstep
          cases hstep
          exact Or.inr ⟨rfl, lt_of_not_ge hup⟩
      · rw [CheckedPrefixSampler.checkedStep_probability_below_zero mass
          (values arm) state arm hpos hlow] at hstep
        cases hstep
        exact Or.inl ⟨rfl, lt_of_not_ge hlow⟩
  | ready state =>
      have hsupported := CheckedPrefixSampler.full_state_output_supported mass values
        state hK hrun
      simp [CheckedPrefixSampler.finishOutput, hrun, hsupported] at hfail

private theorem checkedSample_failure_arm_is_some
    {K m : ℕ} (mass : PrefixSetSampler.SetCarrier K m → ℝ)
    (values : Fin K → PrefixSetSampler.UnitScalar)
    (hK : 0 < K) (arm : Option (Fin K))
    (reason : CheckedPrefixSampler.FailureReason)
    (hfail : CheckedPrefixSampler.checkedSample mass values =
      .failed arm reason) :
    ∃ a, arm = some a := by
  unfold CheckedPrefixSampler.checkedSample at hfail
  cases hrun : CheckedPrefixSampler.runCheckedPrefix mass values K le_rfl with
  | failed failedArm failedReason =>
      simp [CheckedPrefixSampler.finishOutput, hrun] at hfail
      rcases hfail with ⟨rfl, _⟩
      exact ⟨failedArm, rfl⟩
  | ready state =>
      have hsupported := CheckedPrefixSampler.full_state_output_supported
        mass values state hK hrun
      simp [CheckedPrefixSampler.finishOutput, hrun, hsupported] at hfail

private theorem checkedAssignmentSample_prefixFailure_has_prefix
    {p : ConstructorDimensions.Parameters}
    (mass : PrefixSetSampler.SetCarrier p.K p.m → ℝ)
    (anchor : Fin p.K → ℝ) (vector : CheckedAssignmentSample.AssignmentVector p)
    (arm : Option (Fin p.K)) (reason : CheckedPrefixSampler.FailureReason)
    (hsample : CheckedAssignmentSample.checkedAssignmentSample p mass anchor vector =
      .prefixFailure arm reason) :
    CheckedPrefixSampler.checkedSample mass (PrefixSamplerLaw.prefixValues vector) =
      .failed arm reason := by
  rw [CheckedAssignmentSample.checkedAssignmentSample_eq_calls] at hsample
  cases hprefix : CheckedPrefixSampler.checkedSample mass
      (PrefixSamplerLaw.prefixValues vector) with
  | failed actualArm actualReason =>
      have htags : actualArm = arm ∧ actualReason = reason := by
        simpa [hprefix] using hsample
      rcases htags with ⟨rfl, rfl⟩
      rfl
  | sampled set =>
      exact False.elim
        ((CheckedAssignmentSample.finishOrientation_eq_prefixFailure_iff p set
          _ _ arm reason).mp (by simpa only [hprefix] using hsample))

private theorem laterAssignmentStart_eq_finishCheckedSample
    {p : ConstructorDimensions.Parameters}
    {eta : ReferencePrelaunchFollower.LearningRate}
    (old : AssignmentStartPayload.Input p eta)
    (ledger : LaterAssignmentStartOperation.LocalLedger old)
    (instruction : CoordinatorPhaseClock.AssignmentStartInstruction p)
    (row : CompletePublicTable.CompleteRow p)
    (consistent : LaterAssignmentStartOperation.LocalConsistency old ledger)
    (out : AssignmentScoreReconstruction.ReconstructedStart ledger instruction)
    (hcall : AssignmentScoreReconstruction.reconstructLaterStart ledger instruction =
      .success ledger instruction out)
    (hcutoff : ledger.cutoff ≤ instruction.time.val + 1)
    (hcurrentPos : ∀ i, 0 < AssignmentScoreReconstruction.currentWeight out i)
    (hcutoffPos : ∀ i, 0 < AssignmentScoreReconstruction.cutoffWeight out i)
    (hselected : ∃ law, LaterAssignmentStartOperation.selectLaw? old ledger
      instruction out hcutoff hcurrentPos = some law) :
    LaterAssignmentStartOperation.laterAssignmentStart old ledger instruction row
        consistent =
      LaterAssignmentStartOperation.finishCheckedSample old ledger instruction row
        consistent out hcall hcutoff hcurrentPos hcutoffPos
        (Classical.choose hselected) (Classical.choose_spec hselected) := by
  classical
  have hpair :
      (⟨AssignmentScoreReconstruction.reconstructLaterStart ledger instruction, rfl⟩ :
        LaterAssignmentStartOperation.ReconstructionCall old ledger instruction) =
      ⟨.success ledger instruction out, hcall⟩ := by
    apply LaterAssignmentStartOperation.ReconstructionCall.ext
    exact hcall
  have hdecision : LaterAssignmentStartOperation.decideReconstruction old ledger
      instruction = .success out hcall := by
    unfold LaterAssignmentStartOperation.decideReconstruction
    rw [hpair]
    rfl
  unfold LaterAssignmentStartOperation.laterAssignmentStart
  rw [hdecision]
  unfold LaterAssignmentStartOperation.runReconstructionDecision
  rfl

private theorem finishCheckedSample_prefixFailure_iff
    {p : ConstructorDimensions.Parameters}
    {eta : ReferencePrelaunchFollower.LearningRate}
    (old : AssignmentStartPayload.Input p eta)
    (ledger : LaterAssignmentStartOperation.LocalLedger old)
    (instruction : CoordinatorPhaseClock.AssignmentStartInstruction p)
    (row : CompletePublicTable.CompleteRow p)
    (consistent : LaterAssignmentStartOperation.LocalConsistency old ledger)
    (out : AssignmentScoreReconstruction.ReconstructedStart ledger instruction)
    (hcall : AssignmentScoreReconstruction.reconstructLaterStart ledger instruction =
      .success ledger instruction out)
    (hcutoff : ledger.cutoff ≤ instruction.time.val + 1)
    (hcurrentPos : ∀ i, 0 < AssignmentScoreReconstruction.currentWeight out i)
    (hcutoffPos : ∀ i, 0 < AssignmentScoreReconstruction.cutoffWeight out i)
    (law : LaterAssignmentStartOperation.SelectedLaw old ledger instruction out)
    (hselected : LaterAssignmentStartOperation.selectLaw? old ledger instruction out
      hcutoff hcurrentPos = some law)
    (arm : Option (Fin p.K)) (reason : CheckedPrefixSampler.FailureReason) :
    LaterAssignmentStartOperation.finishCheckedSample old ledger instruction row
      consistent out hcall hcutoff hcurrentPos hcutoffPos law hselected =
        .prefixFailure arm reason ↔
      CheckedAssignmentSample.checkedAssignmentSample p law.mass law.anchor
        (LaterAssignmentStartOperation.ownAssignmentVector row instruction.time) =
          .prefixFailure arm reason := by
  unfold LaterAssignmentStartOperation.finishCheckedSample
  split <;> simp_all

private theorem finishCheckedSample_orientationFailure_iff
    {p : ConstructorDimensions.Parameters}
    {eta : ReferencePrelaunchFollower.LearningRate}
    (old : AssignmentStartPayload.Input p eta)
    (ledger : LaterAssignmentStartOperation.LocalLedger old)
    (instruction : CoordinatorPhaseClock.AssignmentStartInstruction p)
    (row : CompletePublicTable.CompleteRow p)
    (consistent : LaterAssignmentStartOperation.LocalConsistency old ledger)
    (out : AssignmentScoreReconstruction.ReconstructedStart ledger instruction)
    (hcall : AssignmentScoreReconstruction.reconstructLaterStart ledger instruction =
      .success ledger instruction out)
    (hcutoff : ledger.cutoff ≤ instruction.time.val + 1)
    (hcurrentPos : ∀ i, 0 < AssignmentScoreReconstruction.currentWeight out i)
    (hcutoffPos : ∀ i, 0 < AssignmentScoreReconstruction.cutoffWeight out i)
    (law : LaterAssignmentStartOperation.SelectedLaw old ledger instruction out)
    (hselected : LaterAssignmentStartOperation.selectLaw? old ledger instruction out
      hcutoff hcurrentPos = some law)
    (set : PrefixSetSampler.SetCarrier p.K p.m) :
    LaterAssignmentStartOperation.finishCheckedSample old ledger instruction row
      consistent out hcall hcutoff hcurrentPos hcutoffPos law hselected =
        .orientationFailure set ↔
      CheckedAssignmentSample.checkedAssignmentSample p law.mass law.anchor
        (LaterAssignmentStartOperation.ownAssignmentVector row instruction.time) =
          .orientationFailure set := by
  unfold LaterAssignmentStartOperation.finishCheckedSample
  split <;> simp_all

private theorem laterAssignmentStart_prefixFailure_has_sample
    {p : ConstructorDimensions.Parameters}
    {eta : ReferencePrelaunchFollower.LearningRate}
    (old : AssignmentStartPayload.Input p eta)
    (ledger : LaterAssignmentStartOperation.LocalLedger old)
    (instruction : CoordinatorPhaseClock.AssignmentStartInstruction p)
    (row : CompletePublicTable.CompleteRow p)
    (consistent : LaterAssignmentStartOperation.LocalConsistency old ledger)
    (out : AssignmentScoreReconstruction.ReconstructedStart ledger instruction)
    (hcall : AssignmentScoreReconstruction.reconstructLaterStart ledger instruction =
      .success ledger instruction out)
    (hcutoff : ledger.cutoff ≤ instruction.time.val + 1)
    (hcurrentPos : ∀ i, 0 < AssignmentScoreReconstruction.currentWeight out i)
    (hcutoffPos : ∀ i, 0 < AssignmentScoreReconstruction.cutoffWeight out i)
    (arm : Option (Fin p.K)) (reason : CheckedPrefixSampler.FailureReason)
    (hlater : LaterAssignmentStartOperation.laterAssignmentStart old ledger
      instruction row consistent = .prefixFailure arm reason) :
    ∃ law : LaterAssignmentStartOperation.SelectedLaw old ledger instruction out,
      LaterAssignmentStartOperation.selectLaw? old ledger instruction out hcutoff
        hcurrentPos = some law ∧
      CheckedAssignmentSample.checkedAssignmentSample p law.mass law.anchor
        (LaterAssignmentStartOperation.ownAssignmentVector row instruction.time) =
          .prefixFailure arm reason := by
  classical
  let hselected := LaterAssignmentStartOperation.selectLaw?_isSome old ledger
    instruction out hcall hcutoff hcurrentPos
  let law := Classical.choose hselected
  have hlaw : LaterAssignmentStartOperation.selectLaw? old ledger instruction out
      hcutoff hcurrentPos = some law := Classical.choose_spec hselected
  have hfinish := laterAssignmentStart_eq_finishCheckedSample old ledger instruction
    row consistent out hcall hcutoff hcurrentPos hcutoffPos hselected
  have hsample := (finishCheckedSample_prefixFailure_iff old ledger instruction row
    consistent out hcall hcutoff hcurrentPos hcutoffPos law hlaw arm reason).mp
      (by rw [← hfinish]; exact hlater)
  exact ⟨law, hlaw, hsample⟩

private theorem renewal_checkedAssignmentSample_isSampled
    {p : ConstructorDimensions.Parameters}
    {eta : ReferencePrelaunchFollower.LearningRate}
    (old : AssignmentStartPayload.Input p eta)
    (ledger : LaterAssignmentStartOperation.LocalLedger old)
    (instruction : CoordinatorPhaseClock.AssignmentStartInstruction p)
    (out : AssignmentScoreReconstruction.ReconstructedStart ledger instruction)
    (law : LaterAssignmentStartOperation.SelectedLaw old ledger instruction out)
    (hcutoff : ledger.cutoff ≤ instruction.time.val + 1)
    (hcurrentPos : ∀ i, 0 < AssignmentScoreReconstruction.currentWeight out i)
    (hselect : LaterAssignmentStartOperation.selectLaw? old ledger instruction out
      hcutoff hcurrentPos = some law)
    (hrenewal : instruction.kind = .renewal)
    (vector : CheckedAssignmentSample.AssignmentVector p) :
    ∃ outcome : OrientedAssignmentLaw.AssignmentOutcome p.K p.m,
      CheckedAssignmentSample.checkedAssignmentSample p law.mass law.anchor vector =
        .sampled outcome := by
  have hlaw := LaterAssignmentStartOperation.selectLaw?_renewal_spec old ledger
    instruction out hcutoff hcurrentPos law hselect hrenewal
  have hmass : law.mass =
      (CanonicalAssignmentVector.productQNormalizedMass p.two_le_m p.m_lt_K
        (AssignmentScoreReconstruction.currentWeight out) hcurrentPos).weight := by
    funext S
    rw [hlaw.2 S]
    simp [LaterAssignmentStartOperation.renewalRawMass,
      LaterAssignmentStartOperation.productQOnPrefixCarrier,
      CanonicalAssignmentVector.productQNormalizedMass]
    congr 1
  rw [hlaw.1, hmass]
  exact ⟨CanonicalAssignmentVector.sampler p.two_le_m p.m_lt_K
      (AssignmentScoreReconstruction.currentWeight out)
      (AssignmentScoreReconstruction.currentWeight out)
      hcurrentPos hcurrentPos vector,
    CheckedAssignmentSample.productQ_checkedAssignmentSample_eq_sampler p
      (AssignmentScoreReconstruction.currentWeight out)
      (AssignmentScoreReconstruction.currentWeight out)
      hcurrentPos hcurrentPos vector⟩

private theorem laterAssignmentStart_orientationFailure_has_sample
    {p : ConstructorDimensions.Parameters}
    {eta : ReferencePrelaunchFollower.LearningRate}
    (old : AssignmentStartPayload.Input p eta)
    (ledger : LaterAssignmentStartOperation.LocalLedger old)
    (instruction : CoordinatorPhaseClock.AssignmentStartInstruction p)
    (row : CompletePublicTable.CompleteRow p)
    (consistent : LaterAssignmentStartOperation.LocalConsistency old ledger)
    (out : AssignmentScoreReconstruction.ReconstructedStart ledger instruction)
    (hcall : AssignmentScoreReconstruction.reconstructLaterStart ledger instruction =
      .success ledger instruction out)
    (hcutoff : ledger.cutoff ≤ instruction.time.val + 1)
    (hcurrentPos : ∀ i, 0 < AssignmentScoreReconstruction.currentWeight out i)
    (hcutoffPos : ∀ i, 0 < AssignmentScoreReconstruction.cutoffWeight out i)
    (set : PrefixSetSampler.SetCarrier p.K p.m)
    (hlater : LaterAssignmentStartOperation.laterAssignmentStart old ledger
      instruction row consistent = .orientationFailure set) :
    ∃ law : LaterAssignmentStartOperation.SelectedLaw old ledger instruction out,
      LaterAssignmentStartOperation.selectLaw? old ledger instruction out hcutoff
        hcurrentPos = some law ∧
      CheckedAssignmentSample.checkedAssignmentSample p law.mass law.anchor
        (LaterAssignmentStartOperation.ownAssignmentVector row instruction.time) =
          .orientationFailure set := by
  classical
  let hselected := LaterAssignmentStartOperation.selectLaw?_isSome old ledger
    instruction out hcall hcutoff hcurrentPos
  let law := Classical.choose hselected
  have hlaw : LaterAssignmentStartOperation.selectLaw? old ledger instruction out
      hcutoff hcurrentPos = some law := Classical.choose_spec hselected
  have hfinish := laterAssignmentStart_eq_finishCheckedSample old ledger instruction
    row consistent out hcall hcutoff hcurrentPos hcutoffPos hselected
  have hsample := (finishCheckedSample_orientationFailure_iff old ledger
    instruction row consistent out hcall hcutoff hcurrentPos hcutoffPos law hlaw set).mp
      (by rw [← hfinish]; exact hlater)
  exact ⟨law, hlaw, hsample⟩

private theorem orientationFailure_false_of_positive_anchor
    {p : ConstructorDimensions.Parameters}
    {eta : ReferencePrelaunchFollower.LearningRate}
    {old : AssignmentStartPayload.Input p eta}
    {ledger : LaterAssignmentStartOperation.LocalLedger old}
    {instruction : CoordinatorPhaseClock.AssignmentStartInstruction p}
    {out : AssignmentScoreReconstruction.ReconstructedStart ledger instruction}
    (law : LaterAssignmentStartOperation.SelectedLaw
      (p := p) (eta := eta) old ledger instruction out)
    (row : CompletePublicTable.CompleteRow p)
    (set : PrefixSetSampler.SetCarrier p.K p.m)
    (hsample : CheckedAssignmentSample.checkedAssignmentSample p law.mass law.anchor
      (LaterAssignmentStartOperation.ownAssignmentVector row instruction.time) =
        .orientationFailure set) : False := by
  rw [CheckedAssignmentSample.checkedAssignmentSample_eq_calls] at hsample
  cases hprefix : CheckedPrefixSampler.checkedSample law.mass
      (PrefixSamplerLaw.prefixValues
        (LaterAssignmentStartOperation.ownAssignmentVector row instruction.time)) with
  | failed arm reason =>
      simp [hprefix] at hsample
  | sampled sampledSet =>
      have hfinish : CheckedAssignmentSample.finishOrientation p sampledSet
          (CheckedAssignmentOrientation.checkedOrientation p sampledSet law.anchor
            ((LaterAssignmentStartOperation.ownAssignmentVector row instruction.time)
              (Fin.last p.K)))
          (fun j h => CheckedAssignmentOrientation.checkedOrientation_sampled_mem p
            sampledSet law.anchor
            ((LaterAssignmentStartOperation.ownAssignmentVector row instruction.time)
              (Fin.last p.K)) j h) = .orientationFailure set := by
        simpa [hprefix] using hsample
      have hfailure :=
        (CheckedAssignmentSample.finishOrientation_eq_orientationFailure_iff p
          sampledSet set
          (CheckedAssignmentOrientation.checkedOrientation p sampledSet law.anchor
            ((LaterAssignmentStartOperation.ownAssignmentVector row instruction.time)
              (Fin.last p.K)))
          (fun j h => CheckedAssignmentOrientation.checkedOrientation_sampled_mem p
            sampledSet law.anchor
            ((LaterAssignmentStartOperation.ownAssignmentVector row instruction.time)
              (Fin.last p.K)) j h)).mp hfinish
      rcases hfailure with ⟨_, horientation⟩
      have hpositive : ∀ i ∈ sampledSet.1, 0 < law.anchor i := by
        intro i _
        exact law.anchor_pos i
      have hnot := (CheckedAssignmentOrientation.checkedOrientation_eq_failure_iff
        p sampledSet law.anchor
        ((LaterAssignmentStartOperation.ownAssignmentVector row instruction.time)
          (Fin.last p.K))).mp horientation
      exact hnot hpositive

private def dispatcherCollectionConsistency
    {p : ConstructorDimensions.Parameters}
    (x : CoordinatorRoundDispatch.CollectionInput p)
    (core : CoordinatorRoundDispatch.CollectionCoreValid x) :
    LaterAssignmentStartOperation.LocalConsistency x.payload
      (CoordinatorRoundDispatch.collectionOperationLedger x core.payload_n_eq) := {
  oldStart_eq := by
    simpa [CoordinatorRecorderComplementBridge.sourceStart,
      CoordinatorRoundDispatch.collectionOperationLedger] using core.ledger_sigma_eq.symm
  oldAssignment_eq := by
    intro i
    simpa [CoordinatorRoundDispatch.collectionOperationLedger] using
      (core.assignment_eq i).symm
  oldFreezeAt := x.ledger.freezeAt
  oldFreezeAt_eq := by rfl }

private theorem dispatcherCollectionConsistency_eq
    {p : ConstructorDimensions.Parameters}
    (x : CoordinatorRoundDispatch.CollectionInput p)
    (core : CoordinatorRoundDispatch.CollectionCoreValid x)
    (consistent : LaterAssignmentStartOperation.LocalConsistency x.payload
      (CoordinatorRoundDispatch.collectionOperationLedger x core.payload_n_eq)) :
    dispatcherCollectionConsistency x core = consistent := by
  cases consistent with
  | mk hstart hassignment oldFreeze hfreeze =>
      have hfreeze' : oldFreeze = x.ledger.freezeAt := by
        simpa [CoordinatorRoundDispatch.collectionOperationLedger] using hfreeze
      subst oldFreeze
      rfl

private theorem dispatchCollection_laterReconstructionFailure
    {p : ConstructorDimensions.Parameters}
    (x : CoordinatorRoundDispatch.CollectionInput p)
    (core : CoordinatorRoundDispatch.CollectionCoreValid x)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (hstart : CoordinatorPhaseClock.startRound p x.etaReal x.time x.clock
      x.ledger.pending = .ok started)
    (instruction : CoordinatorPhaseClock.AssignmentStartInstruction p)
    (hassignment : started.assignmentStart = some instruction)
    (consistent : LaterAssignmentStartOperation.LocalConsistency x.payload
      (CoordinatorRoundDispatch.collectionOperationLedger x core.payload_n_eq))
    (reason : AssignmentScoreReconstruction.Failure)
    (hpending : x.ledger.pending = ∅)
    (hcall : AssignmentScoreReconstruction.reconstructLaterStart
      (CoordinatorRoundDispatch.collectionOperationLedger x core.payload_n_eq)
      instruction = .failure reason) :
    CoordinatorRoundDispatch.dispatchCollection x =
      .laterReconstructionFailure core consistent started hstart instruction
        hassignment reason
        (LaterAssignmentStartOperation.laterAssignmentStart_reconstructionFailure
          x.payload (CoordinatorRoundDispatch.collectionOperationLedger x core.payload_n_eq)
          instruction x.row consistent reason hcall) := by
  classical
  have hnotpending : ¬ x.ledger.pending.Nonempty := by
    rw [hpending]
    simp
  have hconsistent := dispatcherCollectionConsistency_eq x core consistent
  cases hconsistent
  have hlater : LaterAssignmentStartOperation.laterAssignmentStart x.payload
      (CoordinatorRoundDispatch.collectionOperationLedger x core.payload_n_eq)
      instruction x.row (dispatcherCollectionConsistency x core) = .reconstructionFailure reason :=
    LaterAssignmentStartOperation.laterAssignmentStart_reconstructionFailure
      x.payload (CoordinatorRoundDispatch.collectionOperationLedger x core.payload_n_eq)
      instruction x.row (dispatcherCollectionConsistency x core) reason hcall
  unfold CoordinatorRoundDispatch.dispatchCollection
  split
  · rename_i failure hactual
    rw [hstart] at hactual
    cases hactual
  · rename_i actual hactual
    have heq : actual = started := Except.ok.inj (hactual.symm.trans hstart)
    subst actual
    simp [core, hnotpending]
    split
    · rename_i hmissing
      rw [hassignment] at hmissing
      cases hmissing
    · rename_i actualInstruction hactualInstruction
      have hi : actualInstruction = instruction :=
        Option.some.inj (hactualInstruction.symm.trans hassignment)
      subst actualInstruction
      simp only [dispatcherCollectionConsistency] at hlater
      split
      · rename_i actualReason hactualLater
        have hr := hactualLater.symm.trans hlater
        injection hr with hr
        subst actualReason
        rfl
      · rename_i actualArm actualReason hactualLater
        rw [hlater] at hactualLater
        cases hactualLater
      · rename_i set hactualLater
        rw [hlater] at hactualLater
        cases hactualLater
      · rename_i output hlocal hactualLater
        rw [hlater] at hactualLater
        cases hactualLater

private theorem dispatchCollection_laterPrefixFailure
    {p : ConstructorDimensions.Parameters}
    (x : CoordinatorRoundDispatch.CollectionInput p)
    (core : CoordinatorRoundDispatch.CollectionCoreValid x)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (hstart : CoordinatorPhaseClock.startRound p x.etaReal x.time x.clock
      x.ledger.pending = .ok started)
    (instruction : CoordinatorPhaseClock.AssignmentStartInstruction p)
    (hassignment : started.assignmentStart = some instruction)
    (consistent : LaterAssignmentStartOperation.LocalConsistency x.payload
      (CoordinatorRoundDispatch.collectionOperationLedger x core.payload_n_eq))
    (arm : Option (Fin p.K)) (reason : CheckedPrefixSampler.FailureReason)
    (hpending : x.ledger.pending = ∅)
    (hlater : LaterAssignmentStartOperation.laterAssignmentStart x.payload
      (CoordinatorRoundDispatch.collectionOperationLedger x core.payload_n_eq)
      instruction x.row consistent = .prefixFailure arm reason) :
    CoordinatorRoundDispatch.dispatchCollection x =
      .laterPrefixFailure core consistent started hstart instruction hassignment
        arm reason hlater := by
  classical
  have hnotpending : ¬ x.ledger.pending.Nonempty := by
    rw [hpending]
    simp
  have hconsistent := dispatcherCollectionConsistency_eq x core consistent
  cases hconsistent
  unfold CoordinatorRoundDispatch.dispatchCollection
  split
  · rename_i failure hactual
    rw [hstart] at hactual
    cases hactual
  · rename_i actual hactual
    have heq : actual = started := Except.ok.inj (hactual.symm.trans hstart)
    subst actual
    simp [core, hnotpending]
    split
    · rename_i hmissing
      rw [hassignment] at hmissing
      cases hmissing
    · rename_i actualInstruction hactualInstruction
      have hi : actualInstruction = instruction :=
        Option.some.inj (hactualInstruction.symm.trans hassignment)
      subst actualInstruction
      simp only [dispatcherCollectionConsistency] at hlater
      split
      · rename_i actualReason hactualLater
        rw [hlater] at hactualLater
        cases hactualLater
      · rename_i actualArm actualReason hactualLater
        have heq := hactualLater.symm.trans hlater
        cases heq
        rfl
      · rename_i set hactualLater
        rw [hlater] at hactualLater
        cases hactualLater
      · rename_i output hlocal hactualLater
        rw [hlater] at hactualLater
        cases hactualLater

private theorem dispatchCollection_laterChosen
    {p : ConstructorDimensions.Parameters}
    (x : CoordinatorRoundDispatch.CollectionInput p)
    (core : CoordinatorRoundDispatch.CollectionCoreValid x)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (hstart : CoordinatorPhaseClock.startRound p x.etaReal x.time x.clock
      x.ledger.pending = .ok started)
    (instruction : CoordinatorPhaseClock.AssignmentStartInstruction p)
    (hassignment : started.assignmentStart = some instruction)
    (consistent : LaterAssignmentStartOperation.LocalConsistency x.payload
      (CoordinatorRoundDispatch.collectionOperationLedger x core.payload_n_eq))
    (output : LaterAssignmentStartOperation.SuccessfulStart x.payload
      (CoordinatorRoundDispatch.collectionOperationLedger x core.payload_n_eq)
      instruction x.row)
    (hlocal : output.localConsistency = consistent)
    (htime : instruction.time = x.time)
    (hfreeze : x.clock.g = output.localConsistency.oldFreezeAt)
    (hpending : x.ledger.pending = ∅)
    (hlater : LaterAssignmentStartOperation.laterAssignmentStart x.payload
      (CoordinatorRoundDispatch.collectionOperationLedger x core.payload_n_eq)
      instruction x.row consistent = .success output hlocal) :
    let clockData : CoordinatorAssignmentRegisterInstall.LaterStartRoundEvidence output := {
      priorClock := x.clock
      pending := x.ledger.pending
      proposalParameterValid := core.clock_parameter_valid
      priorClockValid := core.clock_registers_valid
      startTimeValid := by rw [htime]; exact core.clock_start_time_valid
      result := started
      startRound_eq := by rw [htime]; exact hstart
      assignmentStart_eq := hassignment
      priorSigma_eq := core.clock_sigma_eq
      priorGrid_eq_freezeAt := hfreeze }
    let installation := CoordinatorAssignmentRegisterInstall.installLater output clockData
    (∀ i, installation.retainedBaseScore i ≤ p.T * ConstructorDimensions.D p) →
    CoordinatorLocalArmChoice.ChoiceInputsValid installation.registers.payload
      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
      instruction.time installation.registers.complementWeights →
    installation.registers.complementEnvelopeValid →
    ∃ selection : CoordinatorRoundDispatch.ArmSelection installation.registers.payload
      started instruction.time installation.registers.complementWeights x.row,
      CoordinatorRoundDispatch.dispatchCollection x =
        .laterChosen core consistent started hstart instruction hassignment output hlocal
          clockData installation selection := by
  classical
  dsimp only
  intro hbase hchoice henvelope
  let clockData : CoordinatorAssignmentRegisterInstall.LaterStartRoundEvidence output := {
    priorClock := x.clock
    pending := x.ledger.pending
    proposalParameterValid := core.clock_parameter_valid
    priorClockValid := core.clock_registers_valid
    startTimeValid := by rw [htime]; exact core.clock_start_time_valid
    result := started
    startRound_eq := by rw [htime]; exact hstart
    assignmentStart_eq := hassignment
    priorSigma_eq := core.clock_sigma_eq
    priorGrid_eq_freezeAt := hfreeze }
  let installation := CoordinatorAssignmentRegisterInstall.installLater output clockData
  have hnotpending : ¬ x.ledger.pending.Nonempty := by
    rw [hpending]
    simp
  have hconsistent := dispatcherCollectionConsistency_eq x core consistent
  cases hconsistent
  unfold CoordinatorRoundDispatch.dispatchCollection
  split
  · rename_i failure hactual
    rw [hstart] at hactual
    cases hactual
  · rename_i actual hactual
    have heq : actual = started := Except.ok.inj (hactual.symm.trans hstart)
    subst actual
    simp [core, hnotpending]
    split
    · rename_i hmissing
      rw [hassignment] at hmissing
      cases hmissing
    · rename_i actualInstruction hactualInstruction
      have hi : actualInstruction = instruction :=
        Option.some.inj (hactualInstruction.symm.trans hassignment)
      subst actualInstruction
      simp only [dispatcherCollectionConsistency] at hlater
      split
      · rename_i actualReason hactualLater
        rw [hlater] at hactualLater
        cases hactualLater
      · rename_i actualArm actualReason hactualLater
        rw [hlater] at hactualLater
        cases hactualLater
      · rename_i set hactualLater
        rw [hlater] at hactualLater
        cases hactualLater
      · rename_i actualOutput actualLocal hactualLater
        have heq := hactualLater.symm.trans hlater
        cases heq
        rw [ite_eq_left hbase]
        rw [dite_eq_left hchoice]
        rw [ite_eq_left henvelope]
        have hclockEquations := CoordinatorPhaseClock.startRound_assignment_effect p
          x.etaReal x.time x.clock x.ledger.pending started instruction
          core.clock_parameter_valid core.clock_registers_valid
          core.clock_start_time_valid hstart hassignment
        rcases hclockEquations with
          ⟨htimeActual, _, hnewSigma, _, _, _, _, _⟩
        have hgrid : CoordinatorPhaseClock.clockGridDomain p started.clock := by
          simpa [hnewSigma] using started.gridDomain
        have hgrid' := hgrid
        simp only [CoordinatorPhaseClock.clockGridDomain, hnewSigma] at hgrid'
        have hboundary : started.clock.g ≤ p.T + 1 := hgrid'.2
        have hnonempty := CoordinatorLiveChoiceRecorderStep.coordinatorArmChoice_ne_none
          installation.registers.payload started.pending
          (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
          instruction.time installation.registers.complementWeights x.row hchoice
        split
        · rename_i hselected
          exact False.elim (hnonempty hselected)
        · rename_i arm hselected
          refine ⟨{
            arm := arm
            choiceInputsValid := hchoice
            recorderBoundaryValid := hboundary
            armChoice_eq := hselected }, ?_⟩
          rfl

private theorem successful_later_start_installs
    {p : ConstructorDimensions.Parameters}
    (x : CoordinatorRoundDispatch.CollectionInput p)
    (core : CoordinatorRoundDispatch.CollectionCoreValid x)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (hstart : CoordinatorPhaseClock.startRound p x.etaReal x.time x.clock
      x.ledger.pending = .ok started)
    (instruction : CoordinatorPhaseClock.AssignmentStartInstruction p)
    (hassignment : started.assignmentStart = some instruction)
    (consistent : LaterAssignmentStartOperation.LocalConsistency x.payload
      (CoordinatorRoundDispatch.collectionOperationLedger x core.payload_n_eq))
    (output : LaterAssignmentStartOperation.SuccessfulStart x.payload
      (CoordinatorRoundDispatch.collectionOperationLedger x core.payload_n_eq)
      instruction x.row)
    (hlocal : output.localConsistency = consistent)
    (hlater : LaterAssignmentStartOperation.laterAssignmentStart x.payload
      (CoordinatorRoundDispatch.collectionOperationLedger x core.payload_n_eq)
      instruction x.row consistent = .success output hlocal)
    (htime : instruction.time = x.time)
    (hpending : x.ledger.pending = ∅)
    (hanchor : ∀ a, x.payload.anchor a = 1)
    (hcurrentBounds : ∀ a,
      1 ≤ AssignmentScoreReconstruction.currentWeight output.reconstruction a ∧
        AssignmentScoreReconstruction.currentWeight output.reconstruction a ≤ 2) :
    ∃ clockData : CoordinatorAssignmentRegisterInstall.LaterStartRoundEvidence output,
      ∃ installation : CoordinatorAssignmentRegisterInstall.LaterInstallation
        output clockData,
      ∃ selection : CoordinatorRoundDispatch.ArmSelection installation.registers.payload
        started instruction.time installation.registers.complementWeights x.row,
        installation = CoordinatorAssignmentRegisterInstall.installLater output clockData ∧
        CoordinatorRoundDispatch.dispatchCollection x =
          .laterChosen core consistent started hstart instruction hassignment output
            hlocal clockData installation selection := by
  classical
  have hfreeze : x.clock.g = output.localConsistency.oldFreezeAt := by
    calc
      x.clock.g = x.ledger.freezeAt := core.ledger_freeze_eq.symm
      _ = consistent.oldFreezeAt := consistent.oldFreezeAt_eq.symm
      _ = output.localConsistency.oldFreezeAt := by rw [hlocal]
  let clockData : CoordinatorAssignmentRegisterInstall.LaterStartRoundEvidence output := {
    priorClock := x.clock
    pending := x.ledger.pending
    proposalParameterValid := core.clock_parameter_valid
    priorClockValid := core.clock_registers_valid
    startTimeValid := by rw [htime]; exact core.clock_start_time_valid
    result := started
    startRound_eq := by rw [htime]; exact hstart
    assignmentStart_eq := hassignment
    priorSigma_eq := core.clock_sigma_eq
    priorGrid_eq_freezeAt := hfreeze }
  let installation := CoordinatorAssignmentRegisterInstall.installLater output clockData
  have hequations := AssignmentScoreReconstruction.reconstructLaterStart_success_equations
    (CoordinatorRoundDispatch.collectionOperationLedger x core.payload_n_eq)
    instruction output.reconstruction output.reconstruction_eq
  rcases hequations with
    ⟨hchecks, _, _, _, _, _, _, _, _, hscoreBound, _⟩
  have hbase : ∀ i, installation.retainedBaseScore i ≤ p.T * ConstructorDimensions.D p := by
    intro i
    change Fin (p.m - 1) at i
    change output.baseScore i ≤ p.T * ConstructorDimensions.D p
    rw [output.baseScore_eq_source]
    exact hscoreBound (output.payload.assignment.assigned i)
  have hkindExpected : instruction.kind =
      AssignmentScoreReconstruction.expectedLaterStartKind
        (CoordinatorRoundDispatch.collectionOperationLedger x core.payload_n_eq).freezeAt
        instruction.time := hchecks.2.2.2.2.1
  have hkind : instruction.kind = .corrected ∨ instruction.kind = .renewal := by
    rw [hkindExpected]
    by_cases hbefore : instruction.time.val + 1 <
        (CoordinatorRoundDispatch.collectionOperationLedger x core.payload_n_eq).freezeAt
    · left
      simp [AssignmentScoreReconstruction.expectedLaterStartKind, hbefore]
    · right
      simp [AssignmentScoreReconstruction.expectedLaterStartKind, hbefore]
  have hcorrectedAnchor : instruction.kind = .corrected →
      installation.registers.payload.anchor = x.payload.anchor := by
    intro hk
    have h := CoordinatorAssignmentRegisterInstall.later_payload_anchor_corrected
      output clockData hk
    simpa [installation, CoordinatorAssignmentRegisterInstall.installLater] using h
  have hrenewalAnchor : instruction.kind = .renewal →
      installation.registers.payload.anchor =
        AssignmentScoreReconstruction.currentWeight output.reconstruction := by
    intro hk
    have h := CoordinatorAssignmentRegisterInstall.later_payload_anchor_renewal
      output clockData hk
    simpa [installation, CoordinatorAssignmentRegisterInstall.installLater] using h
  have henvelope : installation.registers.complementEnvelopeValid := by
    intro j
    change installation.registers.payload.anchor j.1 ≤
        AssignmentScoreReconstruction.currentWeight output.reconstruction j.1 ∧
      AssignmentScoreReconstruction.currentWeight output.reconstruction j.1 ≤
        2 * installation.registers.payload.anchor j.1
    rcases hkind with hk | hk
    · rw [hcorrectedAnchor hk, hanchor j.1]
      simpa using hcurrentBounds j.1
    · rw [hrenewalAnchor hk]
      have hw := hcurrentBounds j.1
      exact ⟨le_rfl, by nlinarith [hw.1]⟩
  have hclockEffects := CoordinatorPhaseClock.startRound_assignment_effect p x.etaReal
    x.time x.clock x.ledger.pending started instruction
    core.clock_parameter_valid core.clock_registers_valid
    core.clock_start_time_valid hstart hassignment
  rcases hclockEffects with ⟨_, _, _, hu, _, _, _, _⟩
  have hstarted :
      CoordinatorLocalArmChoice.assignmentStart installation.registers.payload ≤
        CoordinatorLocalArmChoice.sourceRound instruction.time := by
    change output.payload.sigma.val + 1 ≤ instruction.time.val + 1
    rw [output.payload_start]
  have hcutoff :
      CoordinatorLocalArmChoice.assignmentStart installation.registers.payload ≤
        CoordinatorLocalArmChoice.cutoffRound
          (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u) := by
    change installation.registers.payload.sigma.val + 1 ≤
      CoordinatorLocalArmChoice.cutoffRound
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
    rw [hu]
    simp [CoordinatorLocalArmChoice.cutoffRound,
      CoordinatorLiveChoiceRecorderStep.cutoffFromClock]
  have hweights : ∀ j, 0 < installation.registers.complementWeights j ∧
      installation.registers.payload.anchor j.1 ≤
        installation.registers.complementWeights j ∧
      installation.registers.complementWeights j ≤
        2 * installation.registers.payload.anchor j.1 := by
    intro j
    have henv := henvelope j
    have hpos : 0 < installation.registers.payload.anchor j.1 := by
      rcases hkind with hk | hk
      · rw [hcorrectedAnchor hk, hanchor j.1]
        norm_num
      · rw [hrenewalAnchor hk]
        exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
          (hcurrentBounds j.1).1
    change 0 < AssignmentScoreReconstruction.currentWeight
      output.reconstruction j.1 ∧ _ ∧ _
    exact ⟨lt_of_lt_of_le hpos henv.1, henv.1, henv.2⟩
  have hchoice := CoordinatorLocalArmChoice.choiceInputsValid_mk
    installation.registers.payload
    (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
    instruction.time installation.registers.complementWeights
    hstarted hcutoff hweights
  have hdispatch := dispatchCollection_laterChosen x core started hstart
    instruction hassignment consistent output hlocal htime hfreeze hpending hlater
    hbase hchoice henvelope
  rcases hdispatch with ⟨selection, hdispatch⟩
  exact ⟨clockData, installation, selection, rfl, hdispatch⟩

/-- Exact local empty-pending theorem inputs, with the same actual dispatcher,
reconstruction, selected raw law, and one checked sample call. The successful
constructor exposes the sampled outcome and its original installation. -/
theorem all_known_collection_next_dispatch_cases
    {p : ConstructorDimensions.Parameters}
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (l : ReferenceActivePhysicalStep.Ledger rate)
    (saved : Option (Fin p.T × Bool))
    (hstate : x.state.coordinator = .collection payload l saved)
    (hvalid : CoordinatorCollectionLedger.validLedgerCheck l = true)
    (hphase : l.phase = .ready)
    (hsigma : l.sigma = payload.sigma.val + 1)
    (horder : l.sigma < l.cutoff)
    (hcutoff : l.cutoff < l.cursor)
    (hcursor : l.cursor = x.time.val + 1)
    (hfreeze : l.freezeAt = FollowerCutoffScan.gridBoundary p rate.eta.val payload.sigma)
    (hassign : l.assignment.arm = payload.assignment.assigned)
    (hempty : l.pending = ∅)
    (hanchor : ∀ a, payload.anchor a = 1)
    (hmass : ∀ a c q, l.cutoffRegisters a = some c → l.currentRegisters a = some q →
      c.score + l.increment a + q.queue ≤ (l.cursor - l.sigma) * ConstructorDimensions.D p)
    (hservice : ∀ a c q, l.cutoffRegisters a = some c → l.currentRegisters a = some q →
      c.score + l.increment a ≤ 4 * rate.n * (min l.cursor l.freezeAt - l.sigma))
    (hbank : CoordinatorUpReception.decoderBankCheck p x.state.upDecoderBank = true) :
    ∃ cutoff : Fin p.T, cutoff.val + 1 = l.cutoff ∧
      let clock := ReferenceActivePhysicalStep.collectionClock payload l saved cutoff
      let input := ReferenceActivePhysicalStep.collectionInput x payload l clock cutoff
      ∃ core : CoordinatorRoundDispatch.CollectionCoreValid input,
      ∃ started : CoordinatorPhaseClock.StartRoundResult p,
      ∃ hstart : CoordinatorPhaseClock.startRound p rate.eta.val x.time clock l.pending =
        .ok started,
      ∃ instruction : CoordinatorPhaseClock.AssignmentStartInstruction p,
      ∃ hassignment : started.assignmentStart = some instruction,
      let operationLedger := CoordinatorRoundDispatch.collectionOperationLedger input
        core.payload_n_eq
      ∃ consistent : LaterAssignmentStartOperation.LocalConsistency input.payload
        operationLedger,
      instruction.time = x.time ∧
      instruction.kind = AssignmentScoreReconstruction.expectedLaterStartKind
        operationLedger.freezeAt instruction.time ∧
      (ReferenceActivePhysicalStep.prepare x).coordinator =
        .collection payload l clock cutoff (CoordinatorRoundDispatch.dispatchCollection input) ∧
      (AssignmentScoreReconstruction.reconstructLaterStart operationLedger instruction =
          .failure .previousOutputDomain ↔
        instruction.time.val + 1 < l.freezeAt ∧
          ∃ a c, l.cutoffRegisters a = some c ∧ c.score < c.lastService) ∧
      ((∃ a c, l.cutoffRegisters a = some c ∧ c.score < c.lastService ∧
          ∃ hrec : AssignmentScoreReconstruction.reconstructLaterStart operationLedger
            instruction = .failure .previousOutputDomain,
          instruction.kind = .corrected ∧
          CoordinatorRoundDispatch.dispatchCollection input =
            .laterReconstructionFailure core consistent started hstart instruction hassignment
              .previousOutputDomain
              (LaterAssignmentStartOperation.laterAssignmentStart_reconstructionFailure
                input.payload operationLedger instruction input.row consistent
                .previousOutputDomain hrec)) ∨
       ∃ out : AssignmentScoreReconstruction.ReconstructedStart operationLedger instruction,
       AssignmentScoreReconstruction.reconstructLaterStart operationLedger instruction =
          .success operationLedger instruction out ∧
       ((∃ hcutoffReached : operationLedger.cutoff ≤ instruction.time.val + 1,
          ∃ hcurrentPos : ∀ i, 0 < AssignmentScoreReconstruction.currentWeight out i,
          ∃ law : LaterAssignmentStartOperation.SelectedLaw input.payload operationLedger
            instruction out,
          ∃ arm : Fin p.K, ∃ reason : CheckedPrefixSampler.FailureReason,
          instruction.kind = .corrected ∧
          LaterAssignmentStartOperation.selectLaw? input.payload operationLedger instruction out
            hcutoffReached hcurrentPos = some law ∧
          ∃ previous, AssignmentScoreReconstruction.previousWeight out = some previous ∧
            (∀ i, 0 < previous i) ∧ law.anchor = input.payload.anchor ∧
            (∀ S, law.mass S = LaterAssignmentStartOperation.correctedRawMass
              input.payload operationLedger instruction out previous hcutoffReached S) ∧
          ∃ hlater : LaterAssignmentStartOperation.laterAssignmentStart input.payload
            operationLedger instruction input.row consistent = .prefixFailure (some arm) reason,
          CheckedAssignmentSample.checkedAssignmentSample p law.mass law.anchor
            (LaterAssignmentStartOperation.ownAssignmentVector input.row instruction.time) =
              .prefixFailure (some arm) reason ∧
          ∃ state : PrefixSetSampler.PrefixState p.K p.m,
            CheckedPrefixSampler.runCheckedPrefix law.mass
              (PrefixSamplerLaw.prefixValues
                (LaterAssignmentStartOperation.ownAssignmentVector input.row instruction.time))
              arm.val (Nat.le_of_lt arm.isLt) = .ready state ∧
            CheckedPrefixSampler.checkedStep law.mass
              ((PrefixSamplerLaw.prefixValues
                (LaterAssignmentStartOperation.ownAssignmentVector input.row instruction.time)) arm)
              state arm = .failed arm reason ∧
            0 < CheckedPrefixSampler.rawStateMass law.mass state ∧
            ((reason = .probabilityBelowZero ∧
                CheckedPrefixSampler.rawIncludedMass law.mass state arm /
                  CheckedPrefixSampler.rawStateMass law.mass state < 0) ∨
             (reason = .probabilityAboveOne ∧
                1 < CheckedPrefixSampler.rawIncludedMass law.mass state arm /
                  CheckedPrefixSampler.rawStateMass law.mass state)) ∧
          CoordinatorRoundDispatch.dispatchCollection input =
            .laterPrefixFailure core consistent started hstart instruction hassignment
              (some arm) reason hlater) ∨
        ∃ output : LaterAssignmentStartOperation.SuccessfulStart input.payload operationLedger
          instruction input.row,
        ∃ hlocal : output.localConsistency = consistent,
        ∃ clockData : CoordinatorAssignmentRegisterInstall.LaterStartRoundEvidence output,
        ∃ installation : CoordinatorAssignmentRegisterInstall.LaterInstallation output clockData,
        ∃ selection : CoordinatorRoundDispatch.ArmSelection installation.registers.payload
          started instruction.time installation.registers.complementWeights input.row,
          installation = CoordinatorAssignmentRegisterInstall.installLater output clockData ∧
          CoordinatorLocalArmChoice.coordinatorArmChoice installation.registers.payload
            started.pending
            (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
            instruction.time installation.registers.complementWeights input.row =
              some selection.arm ∧
          output.reconstruction = out ∧
          LaterAssignmentStartOperation.laterAssignmentStart input.payload operationLedger
            instruction input.row consistent = .success output hlocal ∧
          CoordinatorRoundDispatch.dispatchCollection input =
            .laterChosen core consistent started hstart instruction hassignment output hlocal
              clockData installation selection ∧
          LaterAssignmentStartOperation.selectLaw? input.payload operationLedger instruction
            output.reconstruction output.cutoffReached output.currentWeight_pos =
              some output.law ∧
          output.assignmentVector = LaterAssignmentStartOperation.ownAssignmentVector
            input.row instruction.time ∧
          CheckedAssignmentSample.checkedAssignmentSample p output.law.mass output.law.anchor
            output.assignmentVector = .sampled output.outcome ∧
          output.slowSet.1 = output.outcome.1.1.1.erase output.outcome.1.2 ∧
          Finset.univ.image output.payload.assignment.assigned = output.slowSet.1 ∧
          StrictMono output.payload.assignment.assigned ∧
          (output.payload.assignment.auxiliary ∈
            CanonicalFastSampling.fastArmFinset output.slowSet ∧
            (∀ j, j ∈ CanonicalFastSampling.fastArmFinset output.slowSet →
              output.payload.anchor output.payload.assignment.auxiliary ≤ output.payload.anchor j) ∧
            ∀ j, j ∈ CanonicalFastSampling.fastArmFinset output.slowSet →
              output.payload.anchor output.payload.assignment.auxiliary = output.payload.anchor j →
                output.payload.assignment.auxiliary ≤ j) ∧
          (∀ a, output.payload.queues a =
            AssignmentScoreReconstruction.initialQueue output.reconstruction a) ∧
          (∀ i, output.baseScore i = AssignmentScoreReconstruction.sourceScore
            output.reconstruction (output.payload.assignment.assigned i)) ∧
          (∀ i : ActiveRoundActions.Follower p.m,
            installation.retainedBaseScore i =
              AssignmentScoreReconstruction.sourceScore output.reconstruction
                (output.payload.assignment.assigned i)) ∧
          (instruction.kind = .corrected →
            instruction.time.val + 1 < output.localConsistency.oldFreezeAt ∧
            ∃ previous, AssignmentScoreReconstruction.previousWeight output.reconstruction =
              some previous ∧ (∀ i, 0 < previous i) ∧
              output.payload.anchor = input.payload.anchor ∧
              ∀ S, output.law.mass S = LaterAssignmentStartOperation.correctedRawMass
                input.payload operationLedger instruction output.reconstruction previous
                  output.cutoffReached S) ∧
          (instruction.kind = .renewal →
            AssignmentScoreReconstruction.previousScore output.reconstruction = none ∧
            AssignmentScoreReconstruction.previousWeight output.reconstruction = none ∧
            output.localConsistency.oldFreezeAt ≤ instruction.time.val + 1 ∧
            output.payload.anchor = AssignmentScoreReconstruction.currentWeight
              output.reconstruction ∧
            (∀ S, output.law.mass S = LaterAssignmentStartOperation.renewalRawMass
              output.reconstruction S) ∧
            ∀ vector : CheckedAssignmentSample.AssignmentVector p,
              ∃ outcome, CheckedAssignmentSample.checkedAssignmentSample p output.law.mass
                output.law.anchor vector = .sampled outcome) ∧
          (∀ i : ActiveRoundActions.Follower p.m,
            (output.payload.downRecord i).val =
              ⟨instruction.time.val + 1,
                (output.payload.assignment.assigned i).val + 1,
                output.payload.assignment.auxiliary.val + 1,
                output.payload.exponent (output.payload.assignment.assigned i),
                AssignmentScoreReconstruction.initialQueue output.reconstruction
                  (output.payload.assignment.assigned i)⟩) ∧
          (∀ i : ActiveRoundActions.Follower p.m,
            OrdinaryMessageCodec.dyadicRate (output.payload.downRecord i).val.h =
              CanonicalRecordingRates.xi p rate.eta.val output.payload.anchor
                (output.payload.assignment.assigned i)))) := by
  classical
  have hN := ReferenceAllKnownCollectionStartDomains.all_known_collection_reconstruction_cases
    x payload l saved hstate hvalid hphase hsigma horder hcutoff hcursor hfreeze hassign
    hempty hanchor hmass hservice hbank
  dsimp only at hN
  rcases hN with ⟨cutoff, hcutoffFin, core, started, hstart, instruction, hassignment,
    consistent, htime, hkind, hprepared, hcurrentDomains, hunderflow, hcases, hrenewal⟩
  let clock := ReferenceActivePhysicalStep.collectionClock payload l saved cutoff
  let input := ReferenceActivePhysicalStep.collectionInput x payload l clock cutoff
  let operationLedger := CoordinatorRoundDispatch.collectionOperationLedger input core.payload_n_eq
  refine ⟨cutoff, hcutoffFin, core, started, hstart, instruction, hassignment,
    consistent, htime, hkind, hprepared, hunderflow, ?_⟩
  rcases hcases with hfailed | hsuccess
  · rcases hfailed with ⟨hrec, hcorrected, hbad⟩
    rcases hbad with ⟨a, c, hcutSome, hscore⟩
    have hdispatch := dispatchCollection_laterReconstructionFailure input core started
      (by simpa [input, clock, ReferenceActivePhysicalStep.collectionInput] using hstart)
      instruction hassignment consistent .previousOutputDomain
      (by simpa [input, operationLedger, clock,
        ReferenceActivePhysicalStep.collectionInput,
        CoordinatorRoundDispatch.collectionOperationLedger] using hempty)
      (by simpa [input, operationLedger, clock,
        ReferenceActivePhysicalStep.collectionInput,
        CoordinatorRoundDispatch.collectionOperationLedger] using hrec)
    exact Or.inl ⟨a, c, hcutSome, hscore, hrec, hcorrected, hdispatch⟩
  · rcases hsuccess with ⟨out, hrec, hcutReg, hcurReg, hsource, hqueue,
      hcurrentFormula, hcutoffFormula, hcurrentBounds, hcutoffBounds,
      hanchorBounds, hcorrected, hrenewalAbsent⟩
    have hsuccessEquations :=
      AssignmentScoreReconstruction.reconstructLaterStart_success_equations
        operationLedger instruction out hrec
    rcases hsuccessEquations with
      ⟨hchecks, _, _, _, _, _, _, hcurrentPos, hcutoffPos, _, _⟩
    have hcutoffReached : operationLedger.cutoff ≤ instruction.time.val + 1 := by
      have hlt := hcutoff
      rw [hcursor] at hlt
      have hlt' : l.cutoff ≤ instruction.time.val + 1 := by
        rw [htime]
        exact Nat.le_of_lt hlt
      simpa [operationLedger, input, clock,
        ReferenceActivePhysicalStep.collectionInput,
        CoordinatorRoundDispatch.collectionOperationLedger] using hlt'
    have hselected := LaterAssignmentStartOperation.selectLaw?_isSome input.payload
      operationLedger instruction out hrec hcutoffReached hcurrentPos
    have hlaterPrefix (arm : Option (Fin p.K)) (reason : CheckedPrefixSampler.FailureReason)
        (hlater : LaterAssignmentStartOperation.laterAssignmentStart input.payload
          operationLedger instruction input.row consistent = .prefixFailure arm reason) :
        ∃ sampleLaw, LaterAssignmentStartOperation.selectLaw? input.payload operationLedger
          instruction out hcutoffReached hcurrentPos = some sampleLaw ∧
          CheckedAssignmentSample.checkedAssignmentSample p sampleLaw.mass sampleLaw.anchor
            (LaterAssignmentStartOperation.ownAssignmentVector input.row instruction.time) =
              .prefixFailure arm reason :=
      laterAssignmentStart_prefixFailure_has_sample input.payload operationLedger
        instruction input.row consistent out hrec hcutoffReached hcurrentPos hcutoffPos
        arm reason hlater
    have hprefixIsNotRenewal
        (arm : Option (Fin p.K)) (reason : CheckedPrefixSampler.FailureReason)
        (hlater : LaterAssignmentStartOperation.laterAssignmentStart input.payload
          operationLedger instruction input.row consistent = .prefixFailure arm reason)
        (hrenewalKind : instruction.kind = .renewal) : False := by
      obtain ⟨sampleLaw, hsampleSelect, hsample⟩ := hlaterPrefix arm reason hlater
      obtain ⟨_, hsuccessSample⟩ := renewal_checkedAssignmentSample_isSampled
        input.payload operationLedger instruction out sampleLaw hcutoffReached
        hcurrentPos hsampleSelect hrenewalKind
        (LaterAssignmentStartOperation.ownAssignmentVector input.row instruction.time)
      rw [hsample] at hsuccessSample
      cases hsuccessSample
    have horientationImpossible (set : PrefixSetSampler.SetCarrier p.K p.m)
        (hlater : LaterAssignmentStartOperation.laterAssignmentStart input.payload
          operationLedger instruction input.row consistent = .orientationFailure set) : False := by
      obtain ⟨sampleLaw, hsampleSelect, hsample⟩ :=
        laterAssignmentStart_orientationFailure_has_sample input.payload operationLedger
          instruction input.row consistent out hrec hcutoffReached hcurrentPos hcutoffPos
          set hlater
      exact orientationFailure_false_of_positive_anchor sampleLaw input.row set hsample
    have hsuccessFromLater (output : LaterAssignmentStartOperation.SuccessfulStart
        input.payload operationLedger instruction input.row)
        (hlocal : output.localConsistency = consistent)
        (hlater : LaterAssignmentStartOperation.laterAssignmentStart input.payload
          operationLedger instruction input.row consistent = .success output hlocal) :
        ∃ clockData : CoordinatorAssignmentRegisterInstall.LaterStartRoundEvidence output,
          ∃ installation : CoordinatorAssignmentRegisterInstall.LaterInstallation output clockData,
          ∃ selection : CoordinatorRoundDispatch.ArmSelection installation.registers.payload
            started instruction.time installation.registers.complementWeights input.row,
            installation = CoordinatorAssignmentRegisterInstall.installLater output clockData ∧
            CoordinatorRoundDispatch.dispatchCollection input =
              .laterChosen core consistent started
                (by simpa [input, clock, ReferenceActivePhysicalStep.collectionInput] using hstart)
                instruction hassignment output hlocal clockData installation selection := by
      have htimeInput : instruction.time = input.time := by
        simpa [input, ReferenceActivePhysicalStep.collectionInput] using htime
      have hanchorInput : ∀ a, input.payload.anchor a = 1 := by
        simpa [input, ReferenceActivePhysicalStep.collectionInput] using hanchor
      have hcurrentRange : ∀ a, 1 ≤ AssignmentScoreReconstruction.currentWeight
          output.reconstruction a ∧
          AssignmentScoreReconstruction.currentWeight output.reconstruction a ≤ 2 := by
        have hsame : output.reconstruction = out := by
          have hsuccessEq :
              AssignmentScoreReconstruction.Result.success operationLedger instruction
                  output.reconstruction =
                AssignmentScoreReconstruction.Result.success operationLedger instruction out :=
            output.reconstruction_eq.symm.trans hrec
          injection hsuccessEq with _ _ hsame
        intro a
        rw [hsame]
        exact hcurrentBounds a
      exact successful_later_start_installs input core started
        (by simpa [input, clock, ReferenceActivePhysicalStep.collectionInput] using hstart)
        instruction hassignment consistent output hlocal hlater htimeInput hempty
        hanchorInput hcurrentRange
    let laterResult := LaterAssignmentStartOperation.laterAssignmentStart input.payload
      operationLedger instruction input.row consistent
    cases hLaterResult : laterResult with
    | reconstructionFailure reason =>
        have hlater : LaterAssignmentStartOperation.laterAssignmentStart input.payload
            operationLedger instruction input.row consistent = .reconstructionFailure reason := by
          simpa [laterResult] using hLaterResult
        have hfinish := laterAssignmentStart_eq_finishCheckedSample input.payload
          operationLedger instruction input.row consistent out hrec hcutoffReached
          hcurrentPos hcutoffPos hselected
        rw [hfinish] at hlater
        unfold LaterAssignmentStartOperation.finishCheckedSample at hlater
        split at hlater <;> cases hlater
    | prefixFailure arm reason =>
        have hlater : LaterAssignmentStartOperation.laterAssignmentStart input.payload
            operationLedger instruction input.row consistent = .prefixFailure arm reason := by
          simpa [laterResult] using hLaterResult
        have hrenewalNo : instruction.kind ≠ .renewal := by
          intro hk
          exact hprefixIsNotRenewal arm reason hlater hk
        have hcorrectedKind : instruction.kind = .corrected := by
          have hkindExpected := hchecks.2.2.2.2.1
          rw [hkindExpected] at hrenewalNo ⊢
          by_cases hbefore : instruction.time.val + 1 < operationLedger.freezeAt
          · simp [AssignmentScoreReconstruction.expectedLaterStartKind, hbefore]
          · simp [AssignmentScoreReconstruction.expectedLaterStartKind, hbefore] at hrenewalNo ⊢
        obtain ⟨sampleLaw, hsampleSelect, hsample⟩ := hlaterPrefix arm reason hlater
        obtain ⟨previous, hprevious, hanchorLaw, hmassLaw⟩ :=
          LaterAssignmentStartOperation.selectLaw?_corrected_spec input.payload
            operationLedger instruction out hcutoffReached hcurrentPos sampleLaw
            hsampleSelect hcorrectedKind
        have hpreviousPos := LaterAssignmentStartOperation.previousWeight_pos_of_present
          input.payload operationLedger instruction out hrec hcorrectedKind previous hprevious
        have hsum : (∑ S : PrefixSetSampler.SetCarrier p.K p.m, sampleLaw.mass S) = 1 := by
          calc
            _ = ∑ S : PrefixSetSampler.SetCarrier p.K p.m,
                LaterAssignmentStartOperation.correctedRawMass input.payload operationLedger
                  instruction out previous hcutoffReached S := by
              apply Finset.sum_congr rfl
              intro S _
              exact hmassLaw S
            _ = 1 := LaterAssignmentStartOperation.correctedRawMass_sum_eq_one input.payload
              operationLedger instruction out previous hcutoffReached hcurrentPos hcutoffPos
              hpreviousPos
        cases arm with
        | none =>
            have hprefix := checkedAssignmentSample_prefixFailure_has_prefix sampleLaw.mass
              sampleLaw.anchor
              (LaterAssignmentStartOperation.ownAssignmentVector input.row instruction.time)
              .none reason hsample
            obtain ⟨a, hsome⟩ := checkedSample_failure_arm_is_some sampleLaw.mass
              (PrefixSamplerLaw.prefixValues
                (LaterAssignmentStartOperation.ownAssignmentVector input.row instruction.time))
              (ConstructorDimensions.K_pos p) .none reason hprefix
            cases hsome
        | some arm =>
            have hprefix := checkedAssignmentSample_prefixFailure_has_prefix sampleLaw.mass
              sampleLaw.anchor
              (LaterAssignmentStartOperation.ownAssignmentVector input.row instruction.time)
              (some arm) reason hsample
            obtain ⟨state, hready, hstep, hstatePos, hratio⟩ :=
              checkedSample_failure_has_first_ratio sampleLaw.mass
                (PrefixSamplerLaw.prefixValues
                  (LaterAssignmentStartOperation.ownAssignmentVector input.row instruction.time))
                hsum (ConstructorDimensions.K_pos p) arm reason hprefix
            have hdispatch := dispatchCollection_laterPrefixFailure input core started
              (by simpa [input, clock, ReferenceActivePhysicalStep.collectionInput] using hstart)
              instruction hassignment consistent arm reason
              (by simpa [input, operationLedger, clock,
                ReferenceActivePhysicalStep.collectionInput,
                CoordinatorRoundDispatch.collectionOperationLedger] using hempty)
              (by simpa [input, operationLedger, clock,
                ReferenceActivePhysicalStep.collectionInput,
                CoordinatorRoundDispatch.collectionOperationLedger] using hlater)
            exact Or.inr ⟨out, hrec,
              Or.inl ⟨hcutoffReached, hcurrentPos, sampleLaw, arm, reason,
                hcorrectedKind, hsampleSelect,
                previous, hprevious, hpreviousPos, hanchorLaw, hmassLaw, hlater,
                hsample, state, hready, hstep, hstatePos, hratio, hdispatch⟩⟩
    | orientationFailure set =>
        have hlater : LaterAssignmentStartOperation.laterAssignmentStart input.payload
            operationLedger instruction input.row consistent = .orientationFailure set := by
          simpa [laterResult] using hLaterResult
        exact False.elim (horientationImpossible set hlater)
    | success output hlocal =>
        have hlater : LaterAssignmentStartOperation.laterAssignmentStart input.payload
            operationLedger instruction input.row consistent = .success output hlocal := by
          simpa [laterResult] using hLaterResult
        obtain ⟨clockData, installation, selection, hinstallation, hdispatch⟩ :=
          hsuccessFromLater output hlocal hlater
        have hlawCorrected : ∀ hk : instruction.kind = .corrected,
            instruction.time.val + 1 < output.localConsistency.oldFreezeAt ∧
            ∃ previous, AssignmentScoreReconstruction.previousWeight output.reconstruction =
              some previous ∧ (∀ i, 0 < previous i) ∧
              output.payload.anchor = input.payload.anchor ∧
              ∀ S, output.law.mass S = LaterAssignmentStartOperation.correctedRawMass
                input.payload operationLedger instruction output.reconstruction previous
                  output.cutoffReached S := by
          intro hk
          exact LaterAssignmentStartOperation.successful_corrected_law_spec output hk
        have hslowSet := LaterAssignmentStartOperation.successfulSlowSet_eq_erase output
        have himage := LaterAssignmentStartOperation.successful_assignment_image output
        have haux := LaterAssignmentStartOperation.successful_auxiliary_minimum output
        have hsame : output.reconstruction = out := by
          have hsuccessEq :
              AssignmentScoreReconstruction.Result.success operationLedger instruction
                  output.reconstruction =
                AssignmentScoreReconstruction.Result.success operationLedger instruction out :=
            output.reconstruction_eq.symm.trans hrec
          injection hsuccessEq with _ _ hsame
        have hrenewalSpec : ∀ hk : instruction.kind = .renewal,
            AssignmentScoreReconstruction.previousScore output.reconstruction = none ∧
            AssignmentScoreReconstruction.previousWeight output.reconstruction = none ∧
            output.localConsistency.oldFreezeAt ≤ instruction.time.val + 1 ∧
            output.payload.anchor = AssignmentScoreReconstruction.currentWeight
              output.reconstruction ∧
            (∀ S, output.law.mass S = LaterAssignmentStartOperation.renewalRawMass
              output.reconstruction S) ∧
            ∀ vector : CheckedAssignmentSample.AssignmentVector p,
              ∃ outcome, CheckedAssignmentSample.checkedAssignmentSample p output.law.mass
                output.law.anchor vector = .sampled outcome := by
          intro hk
          have habsent := hrenewalAbsent hk
          rcases LaterAssignmentStartOperation.successful_renewal_law_spec output hk with
            ⟨hbefore, hanchor, hmass⟩
          refine ⟨?_, ?_, hbefore, hanchor, hmass, ?_⟩
          · rw [hsame]
            exact habsent.1
          · rw [hsame]
            exact habsent.2
          · intro vector
            exact renewal_checkedAssignmentSample_isSampled input.payload
              operationLedger instruction output.reconstruction output.law output.cutoffReached
              output.currentWeight_pos output.law_selected hk vector
        exact Or.inr ⟨out, hrec,
          Or.inr ⟨output, hlocal, clockData, installation, selection, hinstallation,
            selection.armChoice_eq, hsame, hlater, hdispatch, output.law_selected,
            output.assignmentVector_eq_row_projection, output.checkedSample_eq,
            hslowSet, himage, output.payload.assignment_strictMono, haux, output.payload_queues, output.baseScore_eq_source,
            (fun i => by
              rw [hinstallation]
              exact CoordinatorAssignmentRegisterInstall.later_retained_base_score_eq_source
                output clockData i), hlawCorrected, hrenewalSpec,
            (fun i => LaterAssignmentStartOperation.successful_downRecord_fields output i),
            (fun i => LaterAssignmentStartOperation.successful_downRecord_rate output i)⟩⟩

end Bandits.Support.ReferenceAllKnownCollectionSampleInstall

end
