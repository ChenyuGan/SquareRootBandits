/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ActualInitializationStepMeasurability
public import Bandits.Support.ActualInitializationRun

/-!
# Lossless boundary observations for actual initialization followers

This module codes the existing checked follower boundary operation on every
lossless follower input. Bootstrap outputs include incomplete-block errors and
the actual clipped-block update; declared outputs retain their row, activation,
and complete ordinary-or-dagger carry. A second code represents the existing
unchecked run output on arbitrary startup inputs, while the separate updated
weight observation remains available when a first declaration discards those
weights.

Sources: `sources/zip4/manuscript/07_public_setup.tex:93-112`,
`sources/zip4/manuscript/appendix_b_communication.tex:119-131,160-165`, and
`sources/zip4/manuscript/06_interruptions.tex:253-255,296`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.BootstrapObservedFollower
open Bandits.Support.ActualInitializationPhysicalStep
open Bandits.Support.ActualInitializationRoundMeasurability
open Bandits.Support.ActualBootstrapObservationCode
open Bandits.Support.FollowerPrepareJointMeasurability
open Bandits.Support.FollowerObservationStageMeasurabilityRepair
open Bandits.Support.FollowerLifecycleMeasurability
open Bandits.Support.DeclaredFollowerLocalRound

namespace Bandits.Support.ActualInitializationFollowerBoundaryMeasurability

abbrev Parameters := ActualInitializationRoundMeasurability.Parameters
abbrev RateInput := ActualInitializationRoundMeasurability.RateInput
abbrev Activation (p : Parameters) := ReferencePrelaunchFollower.Activation p
abbrev FollowerCode (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) :=
  ActualInitializationRoundMeasurability.FollowerCode p rate block
abbrev StartupCode (p : Parameters) (block : Fin (n_boot p)) :=
  ActualBootstrapObservationCode.StartupCode p block
abbrev CarriedState (p : Parameters) (rate : RateInput p) :=
  FollowerPrepareJointMeasurability.CarriedState p rate
abbrev LocalMemoryCode (p : Parameters) :=
  FollowerPrepareJointMeasurability.LocalMemoryCode p
abbrev IncomingConfiguration (p : Parameters) (rate : RateInput p) :=
  FollowerPrepareJointMeasurability.IncomingConfiguration p rate

/-- The existing bootstrap weight numerator together with its actual lower
bound invariant. -/
abbrev BoundaryWeightsCode (p : Parameters) :=
  { numerators : Fin p.K → ℕ //
    ∀ a, 1 ≤ BootstrapWeightPotential.weight (b_N p) numerators a }

/-- The original state and one-bit proposal-memory codes used by the first
declaration output. -/
abbrev FirstDeclarationFields (p : Parameters) (rate : RateInput p) :=
  CarriedState p rate × LocalMemoryCode p

/-- Literal three-tag code for the existing boundary output. The declared
configuration is its existing `Option` code, so every saved real fiber and the
ordinary/dagger distinction remain present. -/
abbrev BoundaryOutputCode (p : Parameters) (rate : RateInput p) :=
  (BoundaryWeightsCode p × Activation p) ⊕
    ((Fin (M p) × Activation p × FirstDeclarationFields p rate) ⊕
      (Fin (M p) × Activation p × IncomingConfiguration p rate))

/-- An incomplete finish retains both its processed count and expected block
length. -/
abbrev BoundaryErrorCode := ℕ × ℕ

/-- Total checked observation code, including the incomplete-block branch. -/
abbrev TotalBoundaryCode (p : Parameters) (rate : RateInput p) :=
  BoundaryErrorCode ⊕ BoundaryOutputCode p rate

/-- The source-prescribed initial reference state and proposal memory, encoded
in the already accepted continuous carry and local-memory carriers. -/
def firstDeclarationFields (p : Parameters) (rate : RateInput p) :
    FirstDeclarationFields p rate :=
  (FollowerObservationStageMeasurabilityRepair.carriedStateOfState rate
      (ReferencePrelaunchFollower.initial p rate.eta),
    FollowerLifecycleMeasurability.localMemoryCode
      (ActiveFollowerLifecycle.initialMemory p))

def decodeFirstDeclarationFields {p : Parameters} {rate : RateInput p}
    (fields : FirstDeclarationFields p rate) :
    ReferencePrelaunchFollower.State p rate.eta × ActiveFollowerLifecycle.LocalMemory p :=
  (FollowerObservationStageMeasurabilityRepair.reconstructCarriedState fields.1.1 fields.1.2,
    FollowerLifecycleMeasurability.localMemoryOfCode fields.2)

theorem decode_firstDeclarationFields (p : Parameters) (rate : RateInput p) :
    decodeFirstDeclarationFields (firstDeclarationFields p rate) =
      (ReferencePrelaunchFollower.initial p rate.eta,
        ActiveFollowerLifecycle.initialMemory p) := by
  have hstate : FollowerObservationStageMeasurabilityRepair.reconstructCarriedState
      (FollowerObservationStageMeasurabilityRepair.carriedStateOfState rate
        (ReferencePrelaunchFollower.initial p rate.eta)).1
      (FollowerObservationStageMeasurabilityRepair.carriedStateOfState rate
        (ReferencePrelaunchFollower.initial p rate.eta)).2 =
      ReferencePrelaunchFollower.initial p rate.eta := by
    simpa [FollowerObservationStageMeasurabilityRepair.reconstructCarriedState,
      FollowerObservationStageMeasurabilityRepair.carriedStateBuffer] using
        FollowerObservationStageMeasurabilityRepair.carriedStateOfState_reconstruct
          rate (ReferencePrelaunchFollower.initial p rate.eta)
  exact Prod.ext hstate
    (FollowerLifecycleMeasurability.localMemoryOfCode_code
      (ActiveFollowerLifecycle.initialMemory p))

def encodeBootstrapFinishResult {p : Parameters} (rate : RateInput p)
    (block : Fin (n_boot p))
    (result : Except (BootstrapObservedFollower.FinishFailure p block)
      (BootstrapObservedFollower.BoundaryOutput p block)) : TotalBoundaryCode p rate :=
  match result with
  | .error (.incomplete processed expected) => .inl (processed, expected)
  | .ok (.continueWithWeights numerators lowerBound activation) =>
      .inr (.inl (⟨numerators, lowerBound⟩, activation))
  | .ok (.declareRow row activation) =>
      .inr (.inr (.inl (row, (activation, firstDeclarationFields p rate))))

/-- The checked boundary observation on the full actual follower code. It is
total on arbitrary startup states and preserves both counts of an incomplete
bootstrap finish. -/
def boundaryFollowerCode (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) (follower : FollowerCode p rate block) :
    TotalBoundaryCode p rate :=
  match follower with
  | .inl startup =>
      encodeBootstrapFinishResult rate block
        (ActualBootstrapObservationCode.finishBlockCode p block startup)
  | .inr (row, (activation, configuration)) =>
      .inr (.inr (.inr (row, (activation, configuration))))

/-- Decode a stored boundary-output code by rebuilding each constructor from
its observed fields. This function never invokes a follower operation. -/
def decodeBoundaryOutputCode (p : Parameters) (rate : RateInput p)
    (code : BoundaryOutputCode p rate) : BoundaryFollowerOutput p rate :=
  match code with
  | .inl (weights, activation) =>
      .continueBootstrap weights.1 weights.2 activation
  | .inr (.inl (row, (activation, fields))) =>
      .firstDeclaration row activation
        (decodeFirstDeclarationFields fields).1
        (decodeFirstDeclarationFields fields).2
  | .inr (.inr (row, (activation, configuration))) =>
      .preserveDeclared row activation
        (FollowerPrepareJointMeasurability.localConfigurationOfIncoming rate configuration)

/-- The first-declaration code decodes to the source-prescribed initial state
and empty proposal memory. -/
theorem decode_firstDeclarationOutput (p : Parameters) (rate : RateInput p)
    (row : Fin (M p)) (activation : Activation p) :
    decodeBoundaryOutputCode p rate
      (.inr (.inl (row, (activation, firstDeclarationFields p rate)))) =
      .firstDeclaration row activation (ReferencePrelaunchFollower.initial p rate.eta)
        (ActiveFollowerLifecycle.initialMemory p) := by
  rw [decodeBoundaryOutputCode]
  rw [decode_firstDeclarationFields]

/-- Decode the total checked code, including its stored incomplete counts. -/
def decodeBoundaryFollowerCode (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) (code : TotalBoundaryCode p rate) :
    Except (BootstrapObservedFollower.FinishFailure p block)
      (BoundaryFollowerOutput p rate) :=
  match code with
  | .inl (processed, expected) => .error (.incomplete processed expected)
  | .inr output => .ok (decodeBoundaryOutputCode p rate output)

/-- On the same input, decoding the stored checked code is exactly the existing
physical `boundaryFollower`, including its error branch. -/
theorem decode_boundaryFollowerCode (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) (follower : FollowerCode p rate block) :
    decodeBoundaryFollowerCode p rate block (boundaryFollowerCode p rate block follower) =
      ActualInitializationPhysicalStep.boundaryFollower rate block
        (ActualInitializationRoundMeasurability.followerStateOfCode p rate block follower) := by
  cases follower with
  | inl startup =>
      change decodeBoundaryFollowerCode p rate block
          (encodeBootstrapFinishResult rate block
            (ActualBootstrapObservationCode.finishBlockCode p block startup)) =
        ActualInitializationPhysicalStep.adaptBootstrapFinish rate block
          (BootstrapObservedFollower.finishBlock p block startup)
      rw [ActualBootstrapObservationCode.finishBlockCode_reconstruction]
      cases hfinish : BootstrapObservedFollower.finishBlock p block startup with
      | error failure =>
          cases failure with
          | incomplete processed expected =>
              simp only [decodeBoundaryFollowerCode, encodeBootstrapFinishResult,
                ActualInitializationPhysicalStep.adaptBootstrapFinish]
      | ok output =>
          cases output with
          | continueWithWeights numerators lowerBound activation =>
              simp only [decodeBoundaryFollowerCode, encodeBootstrapFinishResult,
                decodeBoundaryOutputCode,
                ActualInitializationPhysicalStep.adaptBootstrapFinish]
          | declareRow row activation =>
              simp only [decodeBoundaryFollowerCode, encodeBootstrapFinishResult,
                ActualInitializationPhysicalStep.adaptBootstrapFinish]
              rw [decode_firstDeclarationOutput]
  | inr declared =>
      rcases declared with ⟨row, activation, configuration⟩
      simp [boundaryFollowerCode, decodeBoundaryFollowerCode, decodeBoundaryOutputCode,
        ActualInitializationPhysicalStep.boundaryFollower,
        ActualInitializationRoundMeasurability.followerStateOfCode]

/-- Joint Borel measurability of the total checked boundary code, on every
bootstrap or declared follower input. -/
theorem measurable_boundaryFollowerCode (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) :
    Measurable (boundaryFollowerCode p rate block) := by
  apply measurable_fun_sum
  · exact measurable_of_countable _
  · change Measurable (fun x : Fin (M p) ×
      (Activation p × IncomingConfiguration p rate) =>
        Sum.inr (Sum.inr (Sum.inr x)))
    exact measurable_inr.comp (measurable_inr.comp
      (measurable_inr.comp measurable_id))

/-- Measurability after an explicit measurable input map. -/
theorem measurable_boundaryFollowerCode_comp {Ω : Type*} [MeasurableSpace Ω]
    (p : Parameters) (rate : RateInput p) (block : Fin (n_boot p))
    (input : Ω → FollowerCode p rate block) (hinput : Measurable input) :
    Measurable (fun ω => boundaryFollowerCode p rate block (input ω)) :=
  (measurable_boundaryFollowerCode p rate block).comp hinput

/-- The unchecked run-boundary code on every follower input. Bootstrap states
use the existing updated-numerator code and pending-declaration tag, including
when startup is not complete; declared states copy their full incoming code. -/
def boundaryOutputFromFollowerCode (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) (follower : FollowerCode p rate block) :
    BoundaryOutputCode p rate :=
  match follower with
  | .inl startup =>
      match BootstrapObservedFollower.pendingDeclaration startup.blockCase with
      | none =>
          .inl (⟨ActualBootstrapObservationCode.updatedNumeratorsCode p block startup,
            BootstrapObservedFollower.updatedNumerators_lower_bound p block startup⟩,
            BootstrapObservedFollower.nextActivationRound p block)
      | some row =>
          .inr (.inl (row, (BootstrapObservedFollower.nextActivationRound p block,
            firstDeclarationFields p rate)))
  | .inr (row, (activation, configuration)) =>
      .inr (.inr (row, (activation, configuration)))

/-- The unchecked code decodes exactly to the existing run-boundary output,
without replacing the stored state and memory fields by a recomputation. -/
theorem boundaryOutputFromFollowerCode_reconstruction (p : Parameters)
    (rate : RateInput p) (block : Fin (n_boot p))
    (follower : FollowerCode p rate block) :
    decodeBoundaryOutputCode p rate (boundaryOutputFromFollowerCode p rate block follower) =
      ActualInitializationRun.boundaryOutputFromFollower p rate block
        (ActualInitializationRoundMeasurability.followerStateOfCode p rate block follower) := by
  cases follower with
  | inl startup =>
      cases hpending : BootstrapObservedFollower.pendingDeclaration startup.blockCase with
      | none =>
          simp [boundaryOutputFromFollowerCode, decodeBoundaryOutputCode,
            ActualInitializationRun.boundaryOutputFromFollower,
            ActualInitializationRoundMeasurability.followerStateOfCode, hpending,
            ActualBootstrapObservationCode.updatedNumeratorsCode_reconstruction]
      | some row =>
          rw [boundaryOutputFromFollowerCode, hpending]
          rw [decode_firstDeclarationOutput]
          simp [ActualInitializationRun.boundaryOutputFromFollower,
            ActualInitializationRoundMeasurability.followerStateOfCode, hpending]
  | inr declared =>
      rcases declared with ⟨row, activation, configuration⟩
      simp [boundaryOutputFromFollowerCode, decodeBoundaryOutputCode,
        ActualInitializationRun.boundaryOutputFromFollower,
        ActualInitializationRoundMeasurability.followerStateOfCode]

/-- Joint measurability of the unchecked boundary observation on the complete
continuous follower code. -/
theorem measurable_boundaryOutputFromFollowerCode (p : Parameters)
    (rate : RateInput p) (block : Fin (n_boot p)) :
    Measurable (boundaryOutputFromFollowerCode p rate block) := by
  apply measurable_fun_sum
  · exact measurable_of_countable _
  · change Measurable (fun x : Fin (M p) ×
      (Activation p × IncomingConfiguration p rate) =>
        Sum.inr (Sum.inr x))
    exact measurable_inr.comp (measurable_inr.comp measurable_id)

/-- Separate observable for the actual bootstrap weight update. It is present
on every startup input, including first declaration, and absent on declared
inputs whose bootstrap weights have already been discarded. -/
def boundaryUpdatedNumeratorsCode (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) (follower : FollowerCode p rate block) :
    Option (Fin p.K → ℕ) :=
  match follower with
  | .inl startup =>
      some (ActualBootstrapObservationCode.updatedNumeratorsCode p block startup)
  | .inr _ => none

/-- The Option observable uses the standard disjoint-union measurable
structure, matching the existing ordinary/dagger input convention. -/
def boundaryUpdatedNumeratorsToSum {p : Parameters}
    (code : Option (Fin p.K → ℕ)) : Unit ⊕ (Fin p.K → ℕ) :=
  code.elim (Sum.inl ()) Sum.inr

instance boundaryUpdatedNumeratorsMeasurableSpace (p : Parameters) :
    MeasurableSpace (Option (Fin p.K → ℕ)) :=
  (inferInstance : MeasurableSpace (Unit ⊕ (Fin p.K → ℕ))).comap
    (boundaryUpdatedNumeratorsToSum (p := p))

/-- The updated bootstrap numerator observation is measurable jointly with
the original follower input code. -/
theorem measurable_boundaryUpdatedNumeratorsCode (p : Parameters)
    (rate : RateInput p) (block : Fin (n_boot p)) :
    Measurable (boundaryUpdatedNumeratorsCode p rate block) := by
  apply measurable_fun_sum
  · exact measurable_of_countable _
  · exact measurable_const

/-- A measurable explicit-input-map form of the separate numerator
observation. -/
theorem measurable_boundaryUpdatedNumeratorsCode_comp {Ω : Type*}
    [MeasurableSpace Ω] (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) (input : Ω → FollowerCode p rate block)
    (hinput : Measurable input) :
    Measurable (fun ω => boundaryUpdatedNumeratorsCode p rate block (input ω)) :=
  (measurable_boundaryUpdatedNumeratorsCode p rate block).comp hinput

/-- The finite family of checked boundary codes, retaining one independent
constructor and its complete carry fields for each follower. -/
def boundaryFollowersCode (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p))
    (followers : Fin (p.m - 1) → FollowerCode p rate block) :
    Fin (p.m - 1) → TotalBoundaryCode p rate :=
  fun i => boundaryFollowerCode p rate block (followers i)

/-- The finite family code is jointly measurable in every follower input. -/
theorem measurable_boundaryFollowersCode (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) :
    Measurable (boundaryFollowersCode p rate block) := by
  apply measurable_pi_iff.mpr
  intro i
  exact (measurable_boundaryFollowerCode p rate block).comp (measurable_pi_apply i)

/-- Coordinatewise same-input decoding recovers the existing simultaneous
checked `boundaryFollowers` operation on the reconstructed follower family. -/
theorem decode_boundaryFollowersCode (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p))
    (followers : Fin (p.m - 1) → FollowerCode p rate block) :
    (fun i => decodeBoundaryFollowerCode p rate block
      (boundaryFollowersCode p rate block followers i)) =
      ActualInitializationPhysicalStep.boundaryFollowers rate block
        (fun i => ActualInitializationRoundMeasurability.followerStateOfCode
          p rate block (followers i)) := by
  funext i
  exact decode_boundaryFollowerCode p rate block (followers i)

/-- Applying the stored unchecked boundary observation and then the accepted
carry adapter gives exactly the run's existing boundary carry. -/
theorem boundaryCarry_reconstruction (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) (follower : FollowerCode p rate block) :
    ActualInitializationRun.followerCarryAtBlockBoundary p rate block
        (ActualInitializationRoundMeasurability.followerStateOfCode p rate block follower) =
      ActualInitializationRun.followerCarryOfBoundaryOutput rate
        (decodeBoundaryOutputCode p rate
          (boundaryOutputFromFollowerCode p rate block follower)) := by
  rw [boundaryOutputFromFollowerCode_reconstruction]
  rfl

/-- For an explicitly completed follower, the checked code decodes to the
same output as the unchecked code. Completion is supplied by the real block
producer, never assumed for arbitrary startup inputs. -/
theorem checked_boundaryOutput_agrees_of_complete (p : Parameters)
    (rate : RateInput p) (block : Fin (n_boot p))
    (follower : FollowerCode p rate block)
    (hcomplete : ActualInitializationRun.followerAtCursor p rate block
      (BootstrapObservedFollower.blockLength p block)
      (ActualInitializationRoundMeasurability.followerStateOfCode p rate block follower)) :
    decodeBoundaryFollowerCode p rate block (boundaryFollowerCode p rate block follower) =
      .ok (decodeBoundaryOutputCode p rate
        (boundaryOutputFromFollowerCode p rate block follower)) := by
  rw [decode_boundaryFollowerCode]
  rw [ActualInitializationRun.boundaryOutputAtCursor_step p rate block
    (ActualInitializationRoundMeasurability.followerStateOfCode p rate block follower)
    hcomplete]
  rw [ActualInitializationRun.boundaryOutputAtCursor,
    ← boundaryOutputFromFollowerCode_reconstruction]

/-- The real completed-fold producer supplies the completion fact used by the
checked/unchecked boundary agreement. -/
theorem checked_boundaryOutput_agrees_of_blockFold {p : Parameters}
    {rate : RateInput p} {block : Fin (n_boot p)}
    {source : BootstrapPrivateRoundStreams.SourceInput p}
    {rewards : ActualInitializationPhysicalStep.GridRewardTable p}
    {C_star C_h : ℝ} {cursor : ℕ}
    (folded : ActualInitializationRun.BlockFoldOutput p rate block source rewards
      C_star C_h cursor) (i : Fin (p.m - 1)) :
    decodeBoundaryFollowerCode p rate block
        (boundaryFollowerCode p rate block
          (ActualInitializationRoundMeasurability.followerCodeOfState p rate block
            (folded.followers i))) =
      .ok (decodeBoundaryOutputCode p rate
        (boundaryOutputFromFollowerCode p rate block
          (ActualInitializationRoundMeasurability.followerCodeOfState p rate block
            (folded.followers i)))) := by
  apply checked_boundaryOutput_agrees_of_complete
  simpa [ActualInitializationRoundMeasurability.followerStateOfCode_encode] using
    ActualInitializationRun.blockFold_follower_complete folded i

end Bandits.Support.ActualInitializationFollowerBoundaryMeasurability

end
