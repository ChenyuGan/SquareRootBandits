/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCollectionRecorderJointMeasurability
public import Bandits.Support.ReferenceCollectionServiceTailMeasurability

/-!
# Full collection post-choice tail composition

Sources: `sources/zip4/manuscript/06_interruptions.tex:235-295` and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:6-14,69-76`.

This module composes the accepted collection recorder and service/UP/finish
continuation on the same original round, payload, start result, full real
weight vector, own arm, and own grid observation. Its output code is the
canonical `CollectionTailCode`; decoding reconstructs the entire actual
coordinator observation. The prepared-round specialization uses the existing
computed arm and observation and a literal full-vector extension of an
arbitrary complement vector. These are internal deterministic results; they
do not establish a whole-step or horizon law, manuscript closure, or a regret
theorem.

Direct project imports, admitted and independently reviewed in review-0378:
`ReferenceCollectionRecorderJointMeasurability` at
`723c51604171be090e334708f796f2c0c2a8480cbcf288ad22f39594938b0fc4`, and
`ReferenceCollectionServiceTailMeasurability` at
`1b502cb297d64c95674a1e20ae5b59a8a86405af40e69ef82a6a71c1eff525cc`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions

namespace Bandits.Support.ReferenceCollectionTailComposition

open Bandits.Support.CanonicalFastSampling
open Bandits.Support.CoordinatorRecordingOperation
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceCollectionRecorderJointMeasurability
open Bandits.Support.ReferenceCollectionServiceTailMeasurability

variable {p : ConstructorDimensions.Parameters}
  {rate : ReferenceActivePhysicalStep.RateInput p}

/-- Fill a complete arm vector from retained slow-arm values and an arbitrary
vector on the payload's fast-arm subtype. The fast coordinates are supplied
literally; no envelope or probability-law condition is imposed. -/
def extendComplementWeights (payload : Payload rate)
    (retainedWeights : Fin p.K → ℝ)
    (complementWeights : FastArm payload.slowSet → ℝ) : Fin p.K → ℝ :=
  fun arm =>
    if hslow : arm ∈ payload.slowSet.val then retainedWeights arm
    else complementWeights ⟨arm, by
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hslow⟩⟩

/-- Restricting the literal full-vector extension recovers the arbitrary
complement vector pointwise. -/
theorem restrictedWeights_extendComplementWeights (payload : Payload rate)
    (retainedWeights : Fin p.K → ℝ)
    (complementWeights : FastArm payload.slowSet → ℝ) :
    ReferenceCollectionRecorderJointMeasurability.restrictedWeights payload
        (extendComplementWeights payload retainedWeights complementWeights) =
      complementWeights := by
  funext arm
  have hfast : (arm : Fin p.K) ∈
      (Finset.univ : Finset (Fin p.K)) \ payload.slowSet.val := arm.property
  have hnot : (arm : Fin p.K) ∉ payload.slowSet.val :=
    (Finset.mem_sdiff.mp hfast).2
  change extendComplementWeights payload retainedWeights complementWeights arm.1 =
    complementWeights arm
  unfold extendComplementWeights
  rw [dite_eq_right hnot]

/-- The extension agrees with the complement vector at every fast arm. -/
theorem extendComplementWeights_apply (payload : Payload rate)
    (retainedWeights : Fin p.K → ℝ)
    (complementWeights : FastArm payload.slowSet → ℝ)
    (arm : FastArm payload.slowSet) :
    extendComplementWeights payload retainedWeights complementWeights arm.val =
      complementWeights arm := by
  have h := congrFun
    (restrictedWeights_extendComplementWeights payload retainedWeights complementWeights)
    arm
  simpa [ReferenceCollectionRecorderJointMeasurability.restrictedWeights] using h

/-- The literal full collection continuation. The recording argument is
exactly the accepted recorder output on these same original primitives. -/
def collectionPostChoiceTail (x : RoundInput p rate) (payload : Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (weights : Fin p.K → ℝ) (ownArm : Fin p.K)
    (observation : Fin (D p + 1)) : CoordinatorObservation p rate :=
  ReferenceCollectionServiceTailMeasurability.collectionServiceTail x payload
    ledger started
    (ReferenceCollectionRecorderJointMeasurability.collectionRecordingAtComponents
      rate (fun _ : Unit => x) (fun _ => payload) (fun _ => started)
      (fun _ => weights) (fun _ => ownArm) (fun _ => observation) ())
    observation

/-- Full lossless output code for the literal collection post-choice tail. -/
def collectionPostChoiceTailCode (x : RoundInput p rate) (payload : Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (weights : Fin p.K → ℝ) (ownArm : Fin p.K)
    (observation : Fin (D p + 1)) : CollectionTailCode p rate :=
  encodeCollectionObservation
    (collectionPostChoiceTail x payload ledger started weights ownArm observation)

/-- Decoding the full code reconstructs the entire same-input collection
continuation, including its configuration, persistent UP bank, failure,
recording option, and complete UP diagnostic. -/
theorem collectionPostChoiceTailCode_reconstruct
    (x : RoundInput p rate) (payload : Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (weights : Fin p.K → ℝ) (ownArm : Fin p.K)
    (observation : Fin (D p + 1)) :
    decodeCollectionObservation
        (collectionPostChoiceTailCode x payload ledger started weights ownArm observation) =
      collectionPostChoiceTail x payload ledger started weights ownArm observation :=
  decodeCollectionObservation_encodeCollectionObservation _

/-- Full code measurability after separately measurable substitution of all
original primitives on an arbitrary measurable space. Only those primitive
maps are assumptions; the actual recorder and continuation are composed here.
-/
theorem measurable_collectionPostChoiceTailCode_comp {Ω : Type*}
    [MeasurableSpace Ω]
    (round : Ω → RoundInput p rate) (payload : Ω → Payload rate)
    (ledger : Ω → ReferenceActivePhysicalStep.Ledger rate)
    (started : Ω → CoordinatorPhaseClock.StartRoundResult p)
    (weights : Ω → Fin p.K → ℝ) (ownArm : Ω → Fin p.K)
    (observation : Ω → Fin (D p + 1))
    (hround : Measurable round) (hpayload : Measurable payload)
    (hledger : Measurable ledger) (hstarted : Measurable started)
    (hweights : Measurable weights) (harm : Measurable ownArm)
    (hobs : Measurable observation) :
    Measurable (fun ω =>
      collectionPostChoiceTailCode (round ω) (payload ω) (ledger ω)
        (started ω) (weights ω) (ownArm ω) (observation ω)) := by
  have hrecording :=
    ReferenceCollectionRecorderJointMeasurability.measurable_collectionRecordingAtComponents
      (round := round) (payload := payload) (started := started)
      (weights := weights) (ownArm := ownArm) (observation := observation)
      hround hpayload hstarted hweights harm hobs
  have hrecordingPoint (ω : Ω) :
      ReferenceCollectionRecorderJointMeasurability.collectionRecordingAtComponents
          rate (fun _ : Unit => round ω) (fun _ => payload ω) (fun _ => started ω)
          (fun _ => weights ω) (fun _ => ownArm ω) (fun _ => observation ω) () =
        ReferenceCollectionRecorderJointMeasurability.collectionRecordingAtComponents
          rate round payload started weights ownArm observation ω := rfl
  simpa only [collectionPostChoiceTailCode, collectionPostChoiceTail,
    hrecordingPoint] using
    (ReferenceCollectionServiceTailMeasurability.measurable_collectionServiceTailCode_comp
      round payload ledger started
      (ReferenceCollectionRecorderJointMeasurability.collectionRecordingAtComponents
        rate round payload started weights ownArm observation)
      observation hround hpayload hledger hstarted hrecording hobs)

/-- Same-input reconstruction for arbitrary jointly varying original
primitives. No measurability hypothesis is needed for this pointwise identity.
-/
theorem collectionPostChoiceTailCode_comp_reconstruct {Ω : Type*}
    (round : Ω → RoundInput p rate) (payload : Ω → Payload rate)
    (ledger : Ω → ReferenceActivePhysicalStep.Ledger rate)
    (started : Ω → CoordinatorPhaseClock.StartRoundResult p)
    (weights : Ω → Fin p.K → ℝ) (ownArm : Ω → Fin p.K)
    (observation : Ω → Fin (D p + 1)) (ω : Ω) :
    decodeCollectionObservation
        (collectionPostChoiceTailCode (round ω) (payload ω) (ledger ω)
          (started ω) (weights ω) (ownArm ω) (observation ω)) =
      collectionPostChoiceTail (round ω) (payload ω) (ledger ω) (started ω)
        (weights ω) (ownArm ω) (observation ω) :=
  collectionPostChoiceTailCode_reconstruct _ _ _ _ _ _ _

/-- The actual prepared-round specialization agrees exactly with the existing
collection post-choice operation. `extendComplementWeights` supplies the
literal full vector whose restricted fast coordinates are the arbitrary
`complementWeights`. -/
theorem collectionPostChoiceTail_eq_existing {x : RoundInput p rate}
    (prepared : PreparedRound x) (payload : Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (retainedWeights : Fin p.K → ℝ)
    (complementWeights : FastArm payload.slowSet → ℝ) :
    collectionPostChoiceTail x payload ledger started
        (extendComplementWeights payload retainedWeights complementWeights)
        prepared.coordinator.arm prepared.coordinatorObservation =
      ReferenceActivePhysicalStep.collectionPostChoice prepared payload ledger
        started complementWeights := by
  unfold collectionPostChoiceTail
  rw [ReferenceCollectionRecorderJointMeasurability.collectionRecordingAtComponents_eq_existing
    prepared payload started
    (extendComplementWeights payload retainedWeights complementWeights)
    complementWeights
    (extendComplementWeights_apply payload retainedWeights complementWeights)]
  exact ReferenceCollectionServiceTailMeasurability.collectionServiceTail_eq_collectionPostChoice
    prepared payload ledger started complementWeights

/-- Exact encoded specialization of the whole actual observation. -/
theorem collectionPostChoiceTailCode_eq_existing {x : RoundInput p rate}
    (prepared : PreparedRound x) (payload : Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (retainedWeights : Fin p.K → ℝ)
    (complementWeights : FastArm payload.slowSet → ℝ) :
    collectionPostChoiceTailCode x payload ledger started
        (extendComplementWeights payload retainedWeights complementWeights)
        prepared.coordinator.arm prepared.coordinatorObservation =
      encodeCollectionObservation
        (ReferenceActivePhysicalStep.collectionPostChoice prepared payload ledger
          started complementWeights) := by
  exact congrArg encodeCollectionObservation
    (collectionPostChoiceTail_eq_existing prepared payload ledger started
      retainedWeights complementWeights)

/-- Measurability of the canonical configuration projection of any
measurable full tail code. -/
theorem measurable_collectionPostChoiceConfiguration_comp {Ω : Type*}
    [MeasurableSpace Ω] {code : Ω → CollectionTailCode p rate}
    (hcode : Measurable code) :
    Measurable (fun ω => (code ω).1) :=
  measurable_fst.comp hcode

/-- Measurability of the persistent UP decoder-bank projection. -/
theorem measurable_collectionPostChoiceUpDecoderBank_comp {Ω : Type*}
    [MeasurableSpace Ω] {code : Ω → CollectionTailCode p rate}
    (hcode : Measurable code) :
    Measurable (fun ω => (code ω).2.1) :=
  measurable_fst.comp (measurable_snd.comp hcode)

/-- Measurability of the complete failure projection. -/
theorem measurable_collectionPostChoiceFailure_comp {Ω : Type*}
    [MeasurableSpace Ω] {code : Ω → CollectionTailCode p rate}
    (hcode : Measurable code) :
    Measurable (fun ω => (code ω).2.2.1) :=
  measurable_fst.comp (measurable_snd.comp (measurable_snd.comp hcode))

/-- Measurability of the recorder Option projection, preserving both invalid
recorder and complete successful output. -/
theorem measurable_collectionPostChoiceRecording_comp {Ω : Type*}
    [MeasurableSpace Ω] {code : Ω → CollectionTailCode p rate}
    (hcode : Measurable code) :
    Measurable (fun ω => (code ω).2.2.2.1) :=
  measurable_fst.comp
    (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp hcode)))

/-- Measurability of the complete UP diagnostic projection, including the
reception input and all raw/parsed/acceptance fields. -/
theorem measurable_collectionPostChoiceDiagnostic_comp {Ω : Type*}
    [MeasurableSpace Ω] {code : Ω → CollectionTailCode p rate}
    (hcode : Measurable code) :
    Measurable (fun ω => (code ω).2.2.2.2) :=
  measurable_snd.comp
    (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp hcode)))

end Bandits.Support.ReferenceCollectionTailComposition

end
