/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.AssignmentScoreReconstruction
public import Bandits.Support.AssignmentStartPayload
public import Bandits.Support.CheckedAssignmentSample
public import Bandits.Support.CompletePublicTable
public import Bandits.Support.ContinuousControlSlice
public import Bandits.Support.CoordinatorPhaseClock
public import Bandits.Support.ProductSetLaw

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Coordinator local later assignment start

This module composes the existing completed-collection reconstruction, the
existing full-vector checked assignment sampler, and the existing DOWN-payload
constructor. It implements only this local computation. The caller must obtain
the supplied instruction from the actual StartRound result and thread that
clock output; this module installs no clock or ledger of its own.

Sources: sources/zip4/manuscript/06_interruptions.tex:16-61,80-100,
sources/zip4/manuscript/04_slow_fast_learner.tex:7-37, and
sources/zip4/manuscript/appendix_a_local_protocol.tex:8-12,66-77.
-/

@[expose] public section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.CoordinatorCollectionLedger
open Bandits.Support.CoordinatorPhaseClock
open Bandits.Support.AssignmentScoreReconstruction
open Bandits.Support.AssignmentStartPayload
open Bandits.Support.CheckedAssignmentSample
open Bandits.Support.CanonicalOrientedSetLaw
open Bandits.Support.PrefixSetSampler
open Bandits.Support.ProductSetLaw
open Bandits.Support.ContinuousControlSlice

namespace Bandits.Support.LaterAssignmentStartOperation

open Bandits.Support.ReferencePrelaunchFollower

variable {p : ConstructorDimensions.Parameters}
variable {eta : LearningRate}

/-- The ledger cap is the exact cap already carried by the retained old
payload. Thus its learning rate and integer n are shared by type with the
completed collection ledger. -/
theorem oldPayloadSourceCap (old : AssignmentStartPayload.Input p eta) :
    CoordinatorCollectionLedger.sourceLearningCap p eta.val := by
  exact old.eta_le_source_cap

abbrev LocalLedger (old : AssignmentStartPayload.Input p eta) :=
  AssignmentScoreReconstruction.LocalLedger p eta.val eta.property
    (oldPayloadSourceCap old) old.n old.n_eq_eta_mul_D

/-- Explicit local consistency data for retaining the old assignment. The
eta and n equalities are enforced by the dependent types of old and LocalLedger;
this structure records the old start and assignment identity. oldFreezeAt is
identified only with the existing ledger boundary, with no claim that either
value came from a physical execution. -/
structure LocalConsistency (old : AssignmentStartPayload.Input p eta)
    (ledger : LocalLedger old) where
  oldStart_eq : old.sigma.val + 1 = ledger.sigma
  oldAssignment_eq : ∀ i : Fin (p.m - 1),
    old.assignment.assigned i = ledger.assignment.arm i
  oldFreezeAt : ℕ
  oldFreezeAt_eq : oldFreezeAt = ledger.freezeAt

/-- Project the complete K+1 assignment vector from this coordinator's own
complete row at the requested local slice. -/
def ownAssignmentVector
    (row : CompletePublicTable.CompleteRow p) (time : Fin p.T) :
    CheckedAssignmentSample.AssignmentVector p :=
  ContinuousControlSlice.assignmentVector ((row.2 time).1)

/-- Every coordinate is the corresponding source assignment label in the
same complete-row slice, including the final orientation coordinate. -/
theorem ownAssignmentVector_apply
    (row : CompletePublicTable.CompleteRow p) (time : Fin p.T)
    (i : Fin (p.K + 1)) :
    ownAssignmentVector row time i =
      ((row.2 time).1 (ContinuousControlSlice.Label.assign i)) := rfl

/-- The actual product-weight atom on the checked prefix sampler's existing
supported m-set carrier. -/
noncomputable def productQOnPrefixCarrier
    (w : Fin p.K → ℝ) (S : PrefixSetSampler.SetCarrier p.K p.m) : ℝ :=
  ProductSetLaw.Q p.m w ⟨S.1, by
    simp [ProductSetLaw.support]⟩

/-- The literal source scale on the corrected same-episode branch. Its
exponent uses source round labels t and u; the proof argument records that the
checked local cutoff has been reached before natural subtraction is used. -/
noncomputable def correctionScale
    (old : AssignmentStartPayload.Input p eta)
    (ledger : LocalLedger old) (instruction : AssignmentStartInstruction p)
    (_hcutoff : ledger.cutoff ≤ instruction.time.val + 1) : ℝ :=
  let h : ℝ := 4 * (p.m : ℝ) * eta.val
  (1 - h) ^ (instruction.time.val + 1 - ledger.cutoff + 1) / h

/-- The correction denominator is strictly positive from the retained source
learning rate and the actual positive slow-set size. -/
theorem correctionScale_denominator_pos
    (_old : AssignmentStartPayload.Input p eta) :
    0 < 4 * (p.m : ℝ) * eta.val := by
  exact mul_pos (mul_pos (by norm_num)
    (by exact_mod_cast ConstructorDimensions.m_pos p)) eta.property

/-- The checked cutoff inequality makes the source subtraction the exact
nonnegative distance from cutoff round u to source round t. -/
theorem correctionScale_time_difference
    (old : AssignmentStartPayload.Input p eta)
    (ledger : LocalLedger old) (instruction : AssignmentStartInstruction p)
    (hcutoff : ledger.cutoff ≤ instruction.time.val + 1) :
    ledger.cutoff + (instruction.time.val + 1 - ledger.cutoff) =
      instruction.time.val + 1 := by
  calc
    _ = (instruction.time.val + 1 - ledger.cutoff) + ledger.cutoff := Nat.add_comm _ _
    _ = instruction.time.val + 1 := Nat.sub_add_cancel hcutoff

/-- The unmodified corrected raw masses on every supported m-set. The
checked previous vector is an explicit argument to this internal formula; the
operation supplies only the vector read from reconstruction.previousWeight.
No clipping or renormalization is performed. -/
noncomputable def correctedRawMass
    (old : AssignmentStartPayload.Input p eta)
    (ledger : LocalLedger old) (instruction : AssignmentStartInstruction p)
    (out : AssignmentScoreReconstruction.ReconstructedStart ledger instruction)
    (previous : Fin p.K → ℝ)
    (hcutoff : ledger.cutoff ≤ instruction.time.val + 1)
    (S : PrefixSetSampler.SetCarrier p.K p.m) : ℝ :=
  productQOnPrefixCarrier (AssignmentScoreReconstruction.currentWeight out) S +
    correctionScale old ledger instruction hcutoff *
      (productQOnPrefixCarrier (AssignmentScoreReconstruction.cutoffWeight out) S -
        productQOnPrefixCarrier previous S)

/-- The renewal law is exactly the current product-weight law. -/
noncomputable def renewalRawMass
    {old : AssignmentStartPayload.Input p eta}
    {ledger : LocalLedger old} {instruction : AssignmentStartInstruction p}
    (out : AssignmentScoreReconstruction.ReconstructedStart ledger instruction)
    (S : PrefixSetSampler.SetCarrier p.K p.m) : ℝ :=
  productQOnPrefixCarrier (AssignmentScoreReconstruction.currentWeight out) S

/-- A locally selected law contains only the raw masses and anchor that the
existing checked sampler consumes. -/
structure SelectedLaw (old : AssignmentStartPayload.Input p eta)
    (ledger : LocalLedger old) (instruction : AssignmentStartInstruction p)
    (out : AssignmentScoreReconstruction.ReconstructedStart ledger instruction) where
  mass : PrefixSetSampler.SetCarrier p.K p.m → ℝ
  anchor : Fin p.K → ℝ
  anchor_pos : ∀ i, 0 < anchor i

/-- Select the actual raw law after reconstruction. Corrected starts read the
checked present previousWeight; renewal starts do not mention or evaluate
previousScore, previousWeight, or the corrected expression. -/
noncomputable def selectLaw?
    (old : AssignmentStartPayload.Input p eta)
    (ledger : LocalLedger old) (instruction : AssignmentStartInstruction p)
    (out : AssignmentScoreReconstruction.ReconstructedStart ledger instruction)
    (hcutoff : ledger.cutoff ≤ instruction.time.val + 1)
    (hcurrentPos : ∀ i, 0 < AssignmentScoreReconstruction.currentWeight out i) :
    Option (SelectedLaw old ledger instruction out) :=
  match instruction.kind with
  | .first => none
  | .corrected =>
      match AssignmentScoreReconstruction.previousWeight out with
      | none => none
      | some previous => some {
          mass := correctedRawMass old ledger instruction out previous hcutoff
          anchor := old.anchor
          anchor_pos := old.anchor_pos
        }
  | .renewal => some {
      mass := renewalRawMass out
      anchor := AssignmentScoreReconstruction.currentWeight out
      anchor_pos := hcurrentPos
    }

/-- The checked present preceding weight vector is positive by the source
weight base and the literal natural-number powers. -/
theorem previousWeight_pos_of_present
    (old : AssignmentStartPayload.Input p eta)
    (ledger : LocalLedger old) (instruction : AssignmentStartInstruction p)
    (out : AssignmentScoreReconstruction.ReconstructedStart ledger instruction)
    (hcall : AssignmentScoreReconstruction.reconstructLaterStart ledger instruction =
      .success ledger instruction out)
    (hcorrected : instruction.kind = .corrected)
    (previous : Fin p.K → ℝ)
    (hpresent : AssignmentScoreReconstruction.previousWeight out = some previous) :
    ∀ i, 0 < previous i := by
  obtain ⟨_, _, ⟨weights, hweights, hformula⟩, _⟩ :=
    AssignmentScoreReconstruction.reconstructLaterStart_corrected_equations
      ledger instruction out hcall hcorrected
  have hsame : previous = weights := Option.some.inj (hpresent.symm.trans hweights)
  intro i
  rw [hsame, hformula i]
  exact pow_pos (AssignmentScoreReconstruction.sourceWeightBase_pos p) _

/-- Any successful reconstruction has a selected later-start law. The
corrected option is present by the reconstruction check; the renewal case
constructs only the current product law. -/
theorem selectLaw?_isSome
    (old : AssignmentStartPayload.Input p eta)
    (ledger : LocalLedger old) (instruction : AssignmentStartInstruction p)
    (out : AssignmentScoreReconstruction.ReconstructedStart ledger instruction)
    (hcall : AssignmentScoreReconstruction.reconstructLaterStart ledger instruction =
      .success ledger instruction out)
    (hcutoff : ledger.cutoff ≤ instruction.time.val + 1)
    (hcurrentPos : ∀ i, 0 < AssignmentScoreReconstruction.currentWeight out i) :
    ∃ law, selectLaw? old ledger instruction out hcutoff hcurrentPos = some law := by
  cases hkind : instruction.kind with
  | first =>
      have hequations := AssignmentScoreReconstruction.reconstructLaterStart_success_equations
        ledger instruction out hcall
      rcases hequations with ⟨hchecks, _, _, _, _, _, _, _, _, _, _⟩
      rcases hchecks with ⟨_, _, _, _, hkindCheck, _, _⟩
      rw [hkind] at hkindCheck
      have hfalse : False := by
        by_cases htime : instruction.time.val + 1 < ledger.freezeAt
        · simp [AssignmentScoreReconstruction.expectedLaterStartKind, htime] at hkindCheck
        · simp [AssignmentScoreReconstruction.expectedLaterStartKind, htime] at hkindCheck
      exact hfalse.elim
  | corrected =>
      have hcorrected := AssignmentScoreReconstruction.reconstructLaterStart_corrected_equations
        ledger instruction out hcall hkind
      rcases hcorrected with ⟨_, _, hprevious, _⟩
      obtain ⟨previous, hpresent, _⟩ := hprevious
      let law : SelectedLaw old ledger instruction out := {
        mass := correctedRawMass old ledger instruction out previous hcutoff
        anchor := old.anchor
        anchor_pos := old.anchor_pos
      }
      exact ⟨law, by simp [selectLaw?, hkind, hpresent, law]⟩
  | renewal =>
      let law : SelectedLaw old ledger instruction out := {
        mass := renewalRawMass out
        anchor := AssignmentScoreReconstruction.currentWeight out
        anchor_pos := hcurrentPos
      }
      exact ⟨law, by simp [selectLaw?, hkind, law]⟩

/-- The selected corrected law is exactly the branch formula and retains the
old payload's anchor. -/
theorem selectLaw?_corrected_spec
    (old : AssignmentStartPayload.Input p eta)
    (ledger : LocalLedger old) (instruction : AssignmentStartInstruction p)
    (out : AssignmentScoreReconstruction.ReconstructedStart ledger instruction)
    (hcutoff : ledger.cutoff ≤ instruction.time.val + 1)
    (hcurrentPos : ∀ i, 0 < AssignmentScoreReconstruction.currentWeight out i)
    (law : SelectedLaw old ledger instruction out)
    (hselect : selectLaw? old ledger instruction out hcutoff hcurrentPos = some law)
    (hcorrected : instruction.kind = .corrected) :
    ∃ previous, AssignmentScoreReconstruction.previousWeight out = some previous ∧
      law.anchor = old.anchor ∧
      ∀ S, law.mass S = correctedRawMass old ledger instruction out previous hcutoff S := by
  rw [selectLaw?, hcorrected] at hselect
  cases hprev : AssignmentScoreReconstruction.previousWeight out with
  | none => simp [hprev] at hselect
  | some previous =>
      simp only [hprev] at hselect
      have hlaw : law = {
        mass := correctedRawMass old ledger instruction out previous hcutoff
        anchor := old.anchor
        anchor_pos := old.anchor_pos } := (Option.some.inj hselect).symm
      subst law
      exact ⟨previous, rfl, rfl, fun _ => rfl⟩

/-- The selected renewal law is exactly Q(currentWeight) with the renewed
anchor currentWeight; no preceding vector occurs in this equation. -/
theorem selectLaw?_renewal_spec
    (old : AssignmentStartPayload.Input p eta)
    (ledger : LocalLedger old) (instruction : AssignmentStartInstruction p)
    (out : AssignmentScoreReconstruction.ReconstructedStart ledger instruction)
    (hcutoff : ledger.cutoff ≤ instruction.time.val + 1)
    (hcurrentPos : ∀ i, 0 < AssignmentScoreReconstruction.currentWeight out i)
    (law : SelectedLaw old ledger instruction out)
    (hselect : selectLaw? old ledger instruction out hcutoff hcurrentPos = some law)
    (hrenewal : instruction.kind = .renewal) :
    law.anchor = AssignmentScoreReconstruction.currentWeight out ∧
      ∀ S, law.mass S = renewalRawMass out S := by
  rw [selectLaw?, hrenewal] at hselect
  have hlaw : law = {
    mass := renewalRawMass out
    anchor := AssignmentScoreReconstruction.currentWeight out
    anchor_pos := hcurrentPos } := (Option.some.inj hselect).symm
  subst law
  exact ⟨rfl, fun _ => rfl⟩

/-- The actual product atoms sum to one on the existing checked-sampler
carrier. -/
theorem productQOnPrefixCarrier_sum_eq_one
    (w : Fin p.K → ℝ) (hw : ∀ i, 0 < w i) :
    (∑ S : PrefixSetSampler.SetCarrier p.K p.m, productQOnPrefixCarrier w S) = 1 := by
  change (∑ S : ProductSetLaw.ProductSet p.K p.m, ProductSetLaw.Q p.m w S) = 1
  exact ProductSetLaw.Q_sum_eq_one w (ConstructorDimensions.m_pos p) p.m_lt_K hw

/-- The corrected raw masses have total mass one from Q_sum_eq_one, even
when some individual corrected masses are negative. This identity alone does
not assert feasibility or sampler success. -/
theorem correctedRawMass_sum_eq_one
    (old : AssignmentStartPayload.Input p eta)
    (ledger : LocalLedger old) (instruction : AssignmentStartInstruction p)
    (out : AssignmentScoreReconstruction.ReconstructedStart ledger instruction)
    (previous : Fin p.K → ℝ)
    (hcutoff : ledger.cutoff ≤ instruction.time.val + 1)
    (hcurrentPos : ∀ i, 0 < AssignmentScoreReconstruction.currentWeight out i)
    (hcutoffPos : ∀ i, 0 < AssignmentScoreReconstruction.cutoffWeight out i)
    (hpreviousPos : ∀ i, 0 < previous i) :
    (∑ S : PrefixSetSampler.SetCarrier p.K p.m,
      correctedRawMass old ledger instruction out previous hcutoff S) = 1 := by
  unfold correctedRawMass
  calc
    _ = (∑ S : PrefixSetSampler.SetCarrier p.K p.m,
          productQOnPrefixCarrier (AssignmentScoreReconstruction.currentWeight out) S) +
        correctionScale old ledger instruction hcutoff *
          ((∑ S : PrefixSetSampler.SetCarrier p.K p.m,
            productQOnPrefixCarrier (AssignmentScoreReconstruction.cutoffWeight out) S) -
           (∑ S : PrefixSetSampler.SetCarrier p.K p.m,
            productQOnPrefixCarrier previous S)) := by
      rw [Finset.sum_add_distrib]
      congr 1
      rw [← Finset.mul_sum, Finset.sum_sub_distrib]
    _ = 1 := by
      rw [productQOnPrefixCarrier_sum_eq_one _ hcurrentPos,
        productQOnPrefixCarrier_sum_eq_one _ hcutoffPos,
        productQOnPrefixCarrier_sum_eq_one _ hpreviousPos]
      ring

/-- The renewal raw mass also sums to one. -/
theorem renewalRawMass_sum_eq_one
    {old : AssignmentStartPayload.Input p eta}
    {ledger : LocalLedger old} {instruction : AssignmentStartInstruction p}
    (out : AssignmentScoreReconstruction.ReconstructedStart ledger instruction)
    (hcurrentPos : ∀ i, 0 < AssignmentScoreReconstruction.currentWeight out i) :
    (∑ S : PrefixSetSampler.SetCarrier p.K p.m, renewalRawMass out S) = 1 :=
  productQOnPrefixCarrier_sum_eq_one _ hcurrentPos

/-- Build the payload from the selected slow set, selected anchor, and actual
reconstructed current queues. -/
def payloadInput
    (old : AssignmentStartPayload.Input p eta)
    {ledger : LocalLedger old}
    (instruction : AssignmentStartInstruction p)
    (out : AssignmentScoreReconstruction.ReconstructedStart ledger instruction)
    (law : SelectedLaw old ledger instruction out)
    (slowSet : CanonicalOrientedSetLaw.SlowSet p.K p.m) :
    AssignmentStartPayload.Input p eta := {
  eta_le_source_cap := old.eta_le_source_cap
  n := old.n
  n_eq_eta_mul_D := old.n_eq_eta_mul_D
  sigma := instruction.time
  slowSet := slowSet
  anchor := law.anchor
  anchor_pos := law.anchor_pos
  queues := AssignmentScoreReconstruction.initialQueue out
  queues_le_TD := out.initialQueue_le
}

/-- Retain the reconstructed current score on every newly assigned follower
arm. -/
noncomputable def retainedBaseScore
    {old : AssignmentStartPayload.Input p eta}
    {ledger : LocalLedger old} {instruction : AssignmentStartInstruction p}
    (out : AssignmentScoreReconstruction.ReconstructedStart ledger instruction)
    (payload : AssignmentStartPayload.Input p eta) : Fin (p.m - 1) → ℕ :=
  fun i => AssignmentScoreReconstruction.sourceScore out
    (payload.assignment.assigned i)

/-- A successful local result carries the checked sample and all exact
payload equations. Its ledger and instruction are indices, so success cannot
silently replace either local input. -/
structure SuccessfulStart
    (old : AssignmentStartPayload.Input p eta)
    (ledger : LocalLedger old) (instruction : AssignmentStartInstruction p)
    (row : CompletePublicTable.CompleteRow p) where
  localConsistency : LocalConsistency old ledger
  reconstruction : AssignmentScoreReconstruction.ReconstructedStart ledger instruction
  reconstruction_eq : AssignmentScoreReconstruction.reconstructLaterStart ledger instruction =
    .success ledger instruction reconstruction
  cutoffReached : ledger.cutoff ≤ instruction.time.val + 1
  currentWeight_pos : ∀ i, 0 < AssignmentScoreReconstruction.currentWeight reconstruction i
  cutoffWeight_pos : ∀ i, 0 < AssignmentScoreReconstruction.cutoffWeight reconstruction i
  law : SelectedLaw old ledger instruction reconstruction
  law_selected : selectLaw? old ledger instruction reconstruction cutoffReached
    currentWeight_pos = some law
  outcome : OrientedAssignmentLaw.AssignmentOutcome p.K p.m
  slowSet : CanonicalOrientedSetLaw.SlowSet p.K p.m
  slowSet_eq_erasure : slowSet = CheckedAssignmentOrientation.slowSetAfter p
    outcome.1.1 outcome.1.2 outcome.2
  assignmentVector : CheckedAssignmentSample.AssignmentVector p
  assignmentVector_eq_row_projection :
    assignmentVector = ownAssignmentVector row instruction.time
  checkedSample_eq : CheckedAssignmentSample.checkedAssignmentSample p law.mass
    law.anchor assignmentVector = .sampled outcome
  payload : AssignmentStartPayload.Input p eta
  payload_eq_input : payload = payloadInput old instruction reconstruction law slowSet
  payload_start : payload.sigma = instruction.time
  payload_anchor : payload.anchor = law.anchor
  payload_slowSet : payload.slowSet = slowSet
  payload_queues : ∀ a, payload.queues a =
    AssignmentScoreReconstruction.initialQueue reconstruction a
  baseScore : Fin (p.m - 1) → ℕ
  baseScore_eq_source : ∀ i, baseScore i =
    AssignmentScoreReconstruction.sourceScore reconstruction
      (payload.assignment.assigned i)

/-- A successful corrected start uses the checked preceding vector and the
retained old payload anchor in its literal raw law. -/
theorem successful_corrected_law_spec
    {old : AssignmentStartPayload.Input p eta}
    {ledger : LocalLedger old} {instruction : AssignmentStartInstruction p}
    {row : CompletePublicTable.CompleteRow p}
    (output : SuccessfulStart old ledger instruction row)
    (hcorrected : instruction.kind = .corrected) :
    instruction.time.val + 1 < output.localConsistency.oldFreezeAt ∧
    ∃ previous,
      AssignmentScoreReconstruction.previousWeight output.reconstruction = some previous ∧
      (∀ i, 0 < previous i) ∧
      output.payload.anchor = old.anchor ∧
      ∀ S, output.law.mass S = correctedRawMass old ledger instruction
        output.reconstruction previous output.cutoffReached S := by
  have hbefore :=
    (AssignmentScoreReconstruction.reconstructLaterStart_corrected_iff ledger instruction
      output.reconstruction output.reconstruction_eq).mp hcorrected
  rw [← output.localConsistency.oldFreezeAt_eq] at hbefore
  obtain ⟨previous, hprevious, hanchor, hmass⟩ :=
    selectLaw?_corrected_spec old ledger instruction output.reconstruction
      output.cutoffReached output.currentWeight_pos output.law output.law_selected hcorrected
  have hpreviousPos := previousWeight_pos_of_present old ledger instruction
    output.reconstruction output.reconstruction_eq hcorrected previous hprevious
  refine ⟨hbefore, previous, hprevious, hpreviousPos, ?_, hmass⟩
  exact output.payload_anchor.trans hanchor

/-- A successful renewal uses exactly Q(currentWeight) and renews its anchor
to currentWeight. -/
theorem successful_renewal_law_spec
    {old : AssignmentStartPayload.Input p eta}
    {ledger : LocalLedger old} {instruction : AssignmentStartInstruction p}
    {row : CompletePublicTable.CompleteRow p}
    (output : SuccessfulStart old ledger instruction row)
    (hrenewal : instruction.kind = .renewal) :
    output.localConsistency.oldFreezeAt ≤ instruction.time.val + 1 ∧
      output.payload.anchor = AssignmentScoreReconstruction.currentWeight output.reconstruction ∧
      ∀ S, output.law.mass S = renewalRawMass output.reconstruction S := by
  have hrenewed :=
    (AssignmentScoreReconstruction.reconstructLaterStart_renewal_iff ledger instruction
      output.reconstruction output.reconstruction_eq).mp hrenewal
  rw [← output.localConsistency.oldFreezeAt_eq] at hrenewed
  obtain ⟨hanchor, hmass⟩ :=
    selectLaw?_renewal_spec old ledger instruction output.reconstruction
      output.cutoffReached output.currentWeight_pos output.law output.law_selected hrenewal
  exact ⟨hrenewed, output.payload_anchor.trans hanchor, hmass⟩

/-- A failure result preserves both checked failure sites and the prefix
sampler's original arm/reason payload. -/
inductive Result (old : AssignmentStartPayload.Input p eta)
    (ledger : LocalLedger old) (instruction : AssignmentStartInstruction p)
    (row : CompletePublicTable.CompleteRow p)
    (consistent : LocalConsistency old ledger) where
  | reconstructionFailure (reason : AssignmentScoreReconstruction.Failure)
  | prefixFailure (arm : Option (Fin p.K))
      (reason : CheckedPrefixSampler.FailureReason)
  | orientationFailure (set : PrefixSetSampler.SetCarrier p.K p.m)
  | success (output : SuccessfulStart old ledger instruction row)
      (localConsistency_eq : output.localConsistency = consistent)

/-- After the single checked sampler call, preserve its failure or build the
existing sorted assignment and DOWN payload from the sampled erasure. -/
noncomputable def finishCheckedSample
    (old : AssignmentStartPayload.Input p eta)
    (ledger : LocalLedger old) (instruction : AssignmentStartInstruction p)
    (row : CompletePublicTable.CompleteRow p)
    (consistent : LocalConsistency old ledger)
    (out : AssignmentScoreReconstruction.ReconstructedStart ledger instruction)
    (hcall : AssignmentScoreReconstruction.reconstructLaterStart ledger instruction =
      .success ledger instruction out)
    (hcutoff : ledger.cutoff ≤ instruction.time.val + 1)
    (hcurrentPos : ∀ i, 0 < AssignmentScoreReconstruction.currentWeight out i)
    (hcutoffPos : ∀ i, 0 < AssignmentScoreReconstruction.cutoffWeight out i)
    (law : SelectedLaw old ledger instruction out)
    (hselected : selectLaw? old ledger instruction out hcutoff hcurrentPos = some law) :
    Result old ledger instruction row consistent := by
  match hsample : CheckedAssignmentSample.checkedAssignmentSample p law.mass law.anchor
      (ownAssignmentVector row instruction.time) with
  | .prefixFailure arm reason => exact .prefixFailure arm reason
  | .orientationFailure set => exact .orientationFailure set
  | .sampled outcome =>
      let slowSet := CheckedAssignmentOrientation.slowSetAfter p
        outcome.1.1 outcome.1.2 outcome.2
      let payload := payloadInput old instruction out law slowSet
      exact .success {
        localConsistency := consistent
        reconstruction := out
        reconstruction_eq := hcall
        cutoffReached := hcutoff
        currentWeight_pos := hcurrentPos
        cutoffWeight_pos := hcutoffPos
        law := law
        law_selected := hselected
        outcome := outcome
        slowSet := slowSet
        slowSet_eq_erasure := rfl
        assignmentVector := ownAssignmentVector row instruction.time
        assignmentVector_eq_row_projection := rfl
        checkedSample_eq := hsample
        payload := payload
        payload_eq_input := rfl
        payload_start := rfl
        payload_anchor := rfl
        payload_slowSet := rfl
        payload_queues := fun _ => rfl
        baseScore := retainedBaseScore out payload
        baseScore_eq_source := fun _ => rfl
      } rfl

/-- The two indices in a successful reconstruction are exactly its original
ledger and instruction. -/
theorem reconstructLaterStart_success_indices
    (old : AssignmentStartPayload.Input p eta)
    (ledger : LocalLedger old) (instruction : AssignmentStartInstruction p)
    (returnedLedger : LocalLedger old)
    (returnedInstruction : AssignmentStartInstruction p)
    (out : AssignmentScoreReconstruction.ReconstructedStart returnedLedger returnedInstruction)
    (hcall : AssignmentScoreReconstruction.reconstructLaterStart ledger instruction =
      .success returnedLedger returnedInstruction out) :
    returnedLedger = ledger ∧ returnedInstruction = instruction := by
  unfold AssignmentScoreReconstruction.reconstructLaterStart at hcall
  split_ifs at hcall
  all_goals
    injection hcall with hledger hinstruction hout
    exact ⟨hledger.symm, hinstruction.symm⟩

/-- A reconstruction decision carries the exact reconstruction equation in
each branch, while keeping the successful output indexed by the original
ledger and instruction. -/
inductive ReconstructionDecision
    (old : AssignmentStartPayload.Input p eta)
    (ledger : LocalLedger old) (instruction : AssignmentStartInstruction p) where
  | failure (reason : AssignmentScoreReconstruction.Failure)
  | success (out : AssignmentScoreReconstruction.ReconstructedStart ledger instruction)
      (call : AssignmentScoreReconstruction.reconstructLaterStart ledger instruction =
        .success ledger instruction out)

/-- The actual reconstruction value paired with its call equation. -/
@[ext] structure ReconstructionCall
    (old : AssignmentStartPayload.Input p eta)
    (ledger : LocalLedger old) (instruction : AssignmentStartInstruction p) where
  result : AssignmentScoreReconstruction.Result p eta.val eta.property
    (oldPayloadSourceCap old) old.n old.n_eq_eta_mul_D
  call : AssignmentScoreReconstruction.reconstructLaterStart ledger instruction = result

/-- Classify an already paired reconstruction value, transporting only the
existing successful output after proving its returned indices are original. -/
noncomputable def decideFromCall
    (old : AssignmentStartPayload.Input p eta)
    (ledger : LocalLedger old) (instruction : AssignmentStartInstruction p)
    (call : ReconstructionCall old ledger instruction) :
    ReconstructionDecision old ledger instruction := by
  rcases call with ⟨result, hcall⟩
  cases result with
  | failure reason => exact .failure reason
  | success returnedLedger returnedInstruction raw =>
      have hindices := reconstructLaterStart_success_indices old ledger instruction
        returnedLedger returnedInstruction raw hcall
      let out : AssignmentScoreReconstruction.ReconstructedStart ledger instruction :=
        hindices.1 ▸ (hindices.2 ▸ raw)
      have hsuccess : AssignmentScoreReconstruction.reconstructLaterStart ledger instruction =
          .success ledger instruction out := by
        rw [hcall]
        cases hindices.2
        cases hindices.1
        rfl
      exact .success out hsuccess

/-- Classify the result of the actual reconstruction call. -/
noncomputable def decideReconstruction
    (old : AssignmentStartPayload.Input p eta)
    (ledger : LocalLedger old) (instruction : AssignmentStartInstruction p) :
    ReconstructionDecision old ledger instruction :=
  decideFromCall old ledger instruction
    ⟨AssignmentScoreReconstruction.reconstructLaterStart ledger instruction, rfl⟩

/-- The computation after reconstruction has selected its branch. -/
noncomputable def runReconstructionDecision
    (old : AssignmentStartPayload.Input p eta)
    (ledger : LocalLedger old)
    (instruction : AssignmentStartInstruction p)
    (row : CompletePublicTable.CompleteRow p)
    (consistent : LocalConsistency old ledger) :
    ReconstructionDecision old ledger instruction →
      Result old ledger instruction row consistent
  | .failure reason => .reconstructionFailure reason
  | .success out hsuccess => by
      classical
      have hequations := AssignmentScoreReconstruction.reconstructLaterStart_success_equations
        ledger instruction out hsuccess
      rcases hequations with
        ⟨hchecks, _, _, _, _, _, _, hcurrentPos, hcutoffPos, _, _⟩
      rcases hchecks with ⟨hvalid, _, hcursor, _, _, _, _⟩
      have hcutoffCursor : ledger.cutoff ≤ ledger.cursor := by
        have h := hvalid
        simp only [CoordinatorCollectionLedger.validLedgerCheck,
          Bool.and_eq_true, decide_eq_true_eq] at h
        tauto
      have hcutoff : ledger.cutoff ≤ instruction.time.val + 1 := by
        rw [← hcursor]
        exact hcutoffCursor
      have hselected := selectLaw?_isSome old ledger instruction out hsuccess
        hcutoff hcurrentPos
      let law := Classical.choose hselected
      have hlaw := Classical.choose_spec hselected
      exact finishCheckedSample old ledger instruction row consistent out hsuccess hcutoff
        hcurrentPos hcutoffPos law hlaw

/-- The actual coordinator-local later assignment start. Reconstruction is
matched first, so its first failure is returned before any selected-law,
weight, queue, row-slice, or sampling computation is evaluated. There is one
call to the integrated checked sampler after law selection, on the original
K+1 assignment vector from the coordinator's own complete row. -/
noncomputable def laterAssignmentStart
    (old : AssignmentStartPayload.Input p eta)
    (ledger : LocalLedger old)
    (instruction : AssignmentStartInstruction p)
    (row : CompletePublicTable.CompleteRow p)
    (consistent : LocalConsistency old ledger) :
    Result old ledger instruction row consistent :=
  runReconstructionDecision old ledger instruction row consistent
    (decideReconstruction old ledger instruction)

/-- A reconstruction failure is returned exactly, before any later-start
computation is called. -/
theorem laterAssignmentStart_reconstructionFailure
    (old : AssignmentStartPayload.Input p eta)
    (ledger : LocalLedger old) (instruction : AssignmentStartInstruction p)
    (row : CompletePublicTable.CompleteRow p) (consistent : LocalConsistency old ledger)
    (reason : AssignmentScoreReconstruction.Failure)
    (hfail : AssignmentScoreReconstruction.reconstructLaterStart ledger instruction =
      .failure reason) :
    laterAssignmentStart old ledger instruction row consistent =
      .reconstructionFailure reason := by
  change runReconstructionDecision old ledger instruction row consistent
      (decideFromCall old ledger instruction
        ⟨AssignmentScoreReconstruction.reconstructLaterStart ledger instruction, rfl⟩) =
    .reconstructionFailure reason
  have hpair :
      (⟨AssignmentScoreReconstruction.reconstructLaterStart ledger instruction, rfl⟩ :
        ReconstructionCall old ledger instruction) = ⟨.failure reason, hfail⟩ := by
    apply ReconstructionCall.ext
    exact hfail
  rw [hpair]
  rfl

/-- Every successful output keeps the original ledger and instruction as its
indices; this module returns no updated clock or competing ledger. -/
theorem successful_reconstruction_keeps_original_inputs
    {old : AssignmentStartPayload.Input p eta}
    {ledger : LocalLedger old} {instruction : AssignmentStartInstruction p}
    {row : CompletePublicTable.CompleteRow p}
    (output : SuccessfulStart old ledger instruction row) :
    AssignmentScoreReconstruction.reconstructLaterStart ledger instruction =
      .success ledger instruction output.reconstruction := output.reconstruction_eq

/-- The successful slow set is the existing orientation erasure S.erase j.
The payload computes its auxiliary arm independently as the minimum-anchor
complement arm with label tie-break. -/
theorem successfulSlowSet_eq_erase
    {old : AssignmentStartPayload.Input p eta}
    {ledger : LocalLedger old} {instruction : AssignmentStartInstruction p}
    {row : CompletePublicTable.CompleteRow p}
    (output : SuccessfulStart old ledger instruction row) :
    output.slowSet.1 = output.outcome.1.1.1.erase output.outcome.1.2 := by
  rw [output.slowSet_eq_erasure]
  exact CheckedAssignmentSample.successfulSlowSet_erase p
    output.outcome.1.1 output.outcome.1.2 output.outcome.2

/-- The payload assignment is the existing sorted follower image of its
successful slow set. -/
theorem successful_assignment_image
    {old : AssignmentStartPayload.Input p eta}
    {ledger : LocalLedger old} {instruction : AssignmentStartInstruction p}
    {row : CompletePublicTable.CompleteRow p}
    (output : SuccessfulStart old ledger instruction row) :
    Finset.univ.image output.payload.assignment.assigned = output.slowSet.1 := by
  rw [← output.payload_slowSet]
  exact output.payload.assignment_image

/-- The existing payload's auxiliary arm is the minimum-anchor complement
arm, with the source label tie-break. It is not the orientation arm discarded
when forming the slow set. -/
theorem successful_auxiliary_minimum
    {old : AssignmentStartPayload.Input p eta}
    {ledger : LocalLedger old} {instruction : AssignmentStartInstruction p}
    {row : CompletePublicTable.CompleteRow p}
    (output : SuccessfulStart old ledger instruction row) :
    output.payload.assignment.auxiliary ∈ CanonicalFastSampling.fastArmFinset output.slowSet ∧
      (∀ j, j ∈ CanonicalFastSampling.fastArmFinset output.slowSet →
        output.payload.anchor output.payload.assignment.auxiliary ≤ output.payload.anchor j) ∧
      (∀ j, j ∈ CanonicalFastSampling.fastArmFinset output.slowSet →
        output.payload.anchor output.payload.assignment.auxiliary = output.payload.anchor j →
          output.payload.assignment.auxiliary ≤ j) := by
  have haux : output.payload.assignment.auxiliary = output.payload.auxiliaryArm := rfl
  rw [haux, ← output.payload_slowSet]
  exact output.payload.auxiliaryArm_spec

/-- Every emitted DOWN word parses back to the exact existing record. -/
theorem successful_downWord_parse
    {old : AssignmentStartPayload.Input p eta}
    {ledger : LocalLedger old} {instruction : AssignmentStartInstruction p}
    {row : CompletePublicTable.CompleteRow p}
    (output : SuccessfulStart old ledger instruction row)
    (i : ActiveRoundActions.Follower p.m) :
    OrdinaryMessageCodec.parseDown
        (ReferencePrelaunchFollower.codecParams p eta)
        (some (output.payload.downWord i)) = some (output.payload.downRecord i) :=
  output.payload.parseDown_downWord i

/-- The outgoing DOWN fields carry source round t, the sorted assigned arm,
the payload's canonical integer rate exponent, and the reconstructed current
queue on that assigned arm. -/
theorem successful_downRecord_fields
    {old : AssignmentStartPayload.Input p eta}
    {ledger : LocalLedger old} {instruction : AssignmentStartInstruction p}
    {row : CompletePublicTable.CompleteRow p}
    (output : SuccessfulStart old ledger instruction row)
    (i : ActiveRoundActions.Follower p.m) :
    (output.payload.downRecord i).val =
      ⟨instruction.time.val + 1,
        (output.payload.assignment.assigned i).val + 1,
        output.payload.assignment.auxiliary.val + 1,
        output.payload.exponent (output.payload.assignment.assigned i),
        AssignmentScoreReconstruction.initialQueue output.reconstruction
          (output.payload.assignment.assigned i)⟩ := by
  rw [output.payload.downRecord_fields, output.payload_start,
    output.payload_queues]

/-- The emitted integer exponent represents the exact canonical recording
rate at the assigned arm under the selected anchor. -/
theorem successful_downRecord_rate
    {old : AssignmentStartPayload.Input p eta}
    {ledger : LocalLedger old} {instruction : AssignmentStartInstruction p}
    {row : CompletePublicTable.CompleteRow p}
    (output : SuccessfulStart old ledger instruction row)
    (i : ActiveRoundActions.Follower p.m) :
    OrdinaryMessageCodec.dyadicRate (output.payload.downRecord i).val.h =
      CanonicalRecordingRates.xi p eta.val output.payload.anchor
        (output.payload.assignment.assigned i) :=
  output.payload.downRecord_rate i

/-- Each follower's retained base score is the reconstructed current score
on the payload's actual assigned arm. -/
theorem successful_baseScore_eq_source
    {old : AssignmentStartPayload.Input p eta}
    {ledger : LocalLedger old} {instruction : AssignmentStartInstruction p}
    {row : CompletePublicTable.CompleteRow p}
    (output : SuccessfulStart old ledger instruction row)
    (i : Fin (p.m - 1)) :
    output.baseScore i = AssignmentScoreReconstruction.sourceScore
      output.reconstruction (output.payload.assignment.assigned i) :=
  output.baseScore_eq_source i

/-- The assignment vector retained by success is exactly the projection of
all K+1 coordinates from the supplied complete-row slice. -/
theorem successful_assignmentVector_is_original_row_projection
    {old : AssignmentStartPayload.Input p eta}
    {ledger : LocalLedger old} {instruction : AssignmentStartInstruction p}
    {row : CompletePublicTable.CompleteRow p}
    (output : SuccessfulStart old ledger instruction row) :
    output.assignmentVector = ownAssignmentVector row instruction.time :=
  output.assignmentVector_eq_row_projection

/-- The payload retains the old integer-rate identity and learning cap. -/
theorem successful_payload_retains_source_parameters
    {old : AssignmentStartPayload.Input p eta}
    {ledger : LocalLedger old} {instruction : AssignmentStartInstruction p}
    {row : CompletePublicTable.CompleteRow p}
    (output : SuccessfulStart old ledger instruction row) :
    output.payload.eta_le_source_cap = old.eta_le_source_cap ∧
      output.payload.n = old.n ∧
      (output.payload.n : ℝ) = eta.val * (ConstructorDimensions.D p : ℝ) := by
  rw [output.payload_eq_input]
  exact ⟨rfl, rfl, old.n_eq_eta_mul_D⟩

end Bandits.Support.LaterAssignmentStartOperation

end
