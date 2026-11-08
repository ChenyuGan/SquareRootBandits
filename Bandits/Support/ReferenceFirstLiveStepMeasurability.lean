/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveCoordinatorStepMeasurability
public import Bandits.Support.ReferenceFollowerVaryingFinishMeasurability

/-!
# Measurability of the canonical FIRST/LIVE/dagger physical STEP

Sources: `sources/zip4/manuscript/06_interruptions.tex:235-296`,
`sources/zip4/manuscript/appendix_a_local_protocol.tex:6-14,28-64`, and
`sources/zip4/manuscript/08_main_theorem.tex:29-42`.

This composes the existing FIRST/LIVE/dagger input fiber, physical preparation,
follower observations, and successor STORE code. The fiber excludes only the
incoming COLLECTION tag. Rows, selected index, time, reward table, full state,
and active typing remain the original `RoundInput` fields. This is internal
measurability infrastructure; it asserts no temporal law or manuscript
closure.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions

namespace Bandits.Support.ReferenceFirstLiveStepMeasurability

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput

variable {p : Parameters} {rate : RateInput p}

abbrev FirstLiveInput (p : Parameters) (rate : RateInput p) :=
  ReferenceFirstLiveCoordinatorStepMeasurability.FirstLiveInput p rate

/-- The existing whole follower observable from this same canonical
preparation, including its configuration, failure, logged DOWN input, and
complete DOWN cut. -/
def followerObservable (x : FirstLiveInput p rate) (i : Fin (p.m - 1)) :=
  ReferenceFollowerTailComposition.observeFollowerObservable
    (ReferenceActivePhysicalStep.prepare x.val) i

/-- PREPARE retains exactly the dispatcher DOWN view used by the existing
whole-observation physical code. -/
theorem preparedDownView_eq_dispatch
    (x : ReferenceActivePhysicalStep.RoundInput p rate) :
    (ReferenceActivePhysicalStep.prepare x).coordinator.downView =
      (ReferenceActivePhysicalStep.dispatch x).downView := rfl

private theorem measurable_preparedDownView : Measurable
    (fun x : FirstLiveInput p rate =>
      (ReferenceActivePhysicalStep.prepare x.val).coordinator.downView) := by
  have heq : (fun x : FirstLiveInput p rate =>
      (ReferenceActivePhysicalStep.prepare x.val).coordinator.downView) =
      fun x => (ReferenceActivePhysicalStep.dispatch x.val).downView := by
    funext x
    exact preparedDownView_eq_dispatch x.val
  rw [heq]
  exact ReferenceFirstLiveCoordinatorStepMeasurability.measurable_downView

/-- The actual follower observation is measurable on the original
FIRST/LIVE/dagger subtype, with both whole-step producers discharged. -/
theorem measurable_followerObservable (i : Fin (p.m - 1)) :
    Measurable (fun x : FirstLiveInput p rate => followerObservable x i) := by
  exact ReferenceFollowerVaryingFinishMeasurability.measurable_observeFollowerObservable_comp
    (p := p) (rate := rate)
    (input := Subtype.val) measurable_subtype_coe i measurable_preparedDownView
    (ReferenceFirstLiveCoordinatorStepMeasurability.measurable_playerFeedback
      (PublicDiscreteDraws.followerPlayer p.two_le_m i))

/-- The existing observable decoder reconstructs the follower result of this
very preparation; no second follower run is introduced. -/
theorem followerObservable_reconstruct (x : FirstLiveInput p rate)
    (i : Fin (p.m - 1)) :
    ReferenceFollowerTailComposition.reconstructFollowerObservable
        (followerObservable x i) =
      (ReferenceActivePhysicalStep.prepare x.val).observeFollower i := by
  exact ReferenceFollowerTailComposition.observeFollowerObservable_reconstruct
    (ReferenceActivePhysicalStep.prepare x.val) i

/-- Assemble all actual successor follower configuration codes by finite pi. -/
theorem measurable_successorFollowerCodes :
    Measurable (fun x : FirstLiveInput p rate =>
      fun i => ReferenceFollowerVaryingFinishMeasurability.successorFollowerConfigurationCode
        x.val i) := by
  apply measurable_pi_iff.mpr
  intro i
  exact ReferenceFollowerVaryingFinishMeasurability.measurable_successorFollowerConfigurationCode_comp
    (p := p) (rate := rate)
    (input := Subtype.val) measurable_subtype_coe i measurable_preparedDownView
    (ReferenceFirstLiveCoordinatorStepMeasurability.measurable_playerFeedback
      (PublicDiscreteDraws.followerPlayer p.two_le_m i))

private theorem measurable_successorActivations : Measurable
    (fun x : FirstLiveInput p rate =>
      (ReferenceActivePhysicalStepMeasurability.successorCode x.val).2.2.1) := by
  have hsource : Measurable (fun x : FirstLiveInput p rate => x.val.state.activations) :=
    (ReferenceActivePhysicalStepMeasurability.measurable_activations.comp
      ReferenceActivePhysicalStepMeasurability.measurable_state).comp measurable_subtype_coe
  have heq : (fun x : FirstLiveInput p rate =>
      (ReferenceActivePhysicalStepMeasurability.successorCode x.val).2.2.1) =
      fun x => x.val.state.activations := by
    funext x
    change (ReferenceActivePhysicalStep.step x.val).next.activations = x.val.state.activations
    exact (ReferenceActivePhysicalStep.step_next_fields x.val).2.2.1
  rw [heq]
  exact hsource

/-- The exact original `successorCode` is measurable. Its follower coordinates
come from the whole observable, its coordinator/bank from the physical code,
and its activations are the unchanged actual state fields. -/
theorem measurable_successorCode :
    Measurable (fun x : FirstLiveInput p rate =>
      ReferenceActivePhysicalStepMeasurability.successorCode x.val) := by
  have hcoordinatorBank :=
    ReferenceFirstLiveCoordinatorStepMeasurability.measurable_coordinatorBankSuccessor
      (p := p) (rate := rate)
  have hcoordinatorProjection : Measurable
      (fun z : ReferenceActivePhysicalStepMeasurability.CoordinatorCode p rate ×
        CoordinatorUpReception.UpDecoderBank p => z.1) := measurable_fst
  have hbankProjection : Measurable
      (fun z : ReferenceActivePhysicalStepMeasurability.CoordinatorCode p rate ×
        CoordinatorUpReception.UpDecoderBank p => z.2) := measurable_snd
  have hcoordinator : Measurable (fun x : FirstLiveInput p rate =>
      (ReferenceActivePhysicalStepMeasurability.successorCode x.val).1) :=
    hcoordinatorProjection.comp hcoordinatorBank
  have hbank : Measurable (fun x : FirstLiveInput p rate =>
      (ReferenceActivePhysicalStepMeasurability.successorCode x.val).2.1) :=
    hbankProjection.comp hcoordinatorBank
  have hfollower : Measurable (fun x : FirstLiveInput p rate =>
      (ReferenceActivePhysicalStepMeasurability.successorCode x.val).2.2.2) := by
    have heq : (fun x : FirstLiveInput p rate =>
        (ReferenceActivePhysicalStepMeasurability.successorCode x.val).2.2.2) =
        fun x i => ReferenceFollowerVaryingFinishMeasurability.successorFollowerConfigurationCode
          (p := p) (rate := rate) x.val i := by
      funext x i
      rfl
    rw [heq]
    exact measurable_successorFollowerCodes
  exact hcoordinator.prodMk (hbank.prodMk
    (measurable_successorActivations.prodMk hfollower))

/-- The literal next state is measurable in its existing STORE space, whose
measurable structure is the comap along the proved lossless `encodeState`. -/
theorem measurable_stepNext :
    Measurable (fun x : FirstLiveInput p rate =>
      (ReferenceActivePhysicalStep.step x.val).next) := by
  apply measurable_comap_iff.mpr
  convert measurable_successorCode using 1
  funext x
  rfl

/-- The actual original own-entry code is measurable from the action and
feedback profiles already present in the physical code. -/
theorem measurable_ownEntryCode (player : Fin p.m) :
    Measurable (fun x : FirstLiveInput p rate =>
      ReferenceActivePhysicalStepMeasurability.ownEntryCode x.val player) := by
  have hactions : Measurable (fun x : FirstLiveInput p rate =>
      (ReferenceActivePhysicalStep.prepare x.val).arms.actions) := by
    convert measurable_fst.comp (measurable_snd.comp
      (measurable_snd.comp
        ReferenceFirstLiveCoordinatorStepMeasurability.measurable_physicalCode)) using 1
    funext x
    rfl
  exact ((measurable_pi_apply player).comp hactions).prodMk
    (ReferenceFirstLiveCoordinatorStepMeasurability.measurable_playerFeedback player)

/-- The deterministic grid conversion is measurable, so the original step's
own entry in its existing typed observation space is measurable as well. -/
theorem measurable_stepOwnEntry (player : Fin p.m) :
    Measurable (fun x : FirstLiveInput p rate =>
      (ReferenceActivePhysicalStep.step x.val).ownEntries player) := by
  have hcode := measurable_ownEntryCode (p := p) (rate := rate) player
  have hgrid : Measurable (fun x : FirstLiveInput p rate =>
      (ReferenceActivePhysicalStepMeasurability.ownEntryCode x.val player).2) :=
    measurable_snd.comp hcode
  have hobservation : Measurable (fun x : FirstLiveInput p rate =>
      ActualInitializationPhysicalStep.observationOfGrid p
        (ReferenceActivePhysicalStepMeasurability.ownEntryCode x.val player).2) :=
    (measurable_of_countable (fun y : Fin (D p + 1) =>
      ActualInitializationPhysicalStep.observationOfGrid p y)).comp hgrid
  have hpair : Measurable (fun x : FirstLiveInput p rate =>
      ((ReferenceActivePhysicalStepMeasurability.ownEntryCode x.val player).1,
        ActualInitializationPhysicalStep.observationOfGrid p
          (ReferenceActivePhysicalStepMeasurability.ownEntryCode x.val player).2)) :=
    (measurable_fst.comp hcode).prodMk hobservation
  have heq : (fun x : FirstLiveInput p rate =>
      (ReferenceActivePhysicalStep.step x.val).ownEntries player) = fun x =>
        ((ReferenceActivePhysicalStepMeasurability.ownEntryCode x.val player).1,
          ActualInitializationPhysicalStep.observationOfGrid p
            (ReferenceActivePhysicalStepMeasurability.ownEntryCode x.val player).2) := by
    funext x
    exact (ReferenceActivePhysicalStepMeasurability.ownEntryCode_reconstruct
      x.val player).symm
  rw [heq]
  exact hpair

/-- Exact action and collision-sensitive feedback reconstruction for the
same original STEP entry. -/
theorem ownEntryCode_reconstruct (x : FirstLiveInput p rate)
    (player : Fin p.m) :
    ((ReferenceActivePhysicalStepMeasurability.ownEntryCode x.val player).1,
      ActualInitializationPhysicalStep.observationOfGrid p
        (ReferenceActivePhysicalStepMeasurability.ownEntryCode x.val player).2) =
      (ReferenceActivePhysicalStep.step x.val).ownEntries player :=
  ReferenceActivePhysicalStepMeasurability.ownEntryCode_reconstruct x.val player

/-- The joint code retains the admitted physical code, every whole follower
observable, and the exact canonical successor code from the same input. -/
def wholeStepCode (x : FirstLiveInput p rate) :=
  (ReferenceFirstLiveCoordinatorStepMeasurability.physicalCode x.val,
    (fun i => followerObservable x i,
      ReferenceActivePhysicalStepMeasurability.successorCode x.val))

/-- The complete actual FIRST/LIVE/dagger physical-to-successor composition
is measurable. -/
theorem measurable_wholeStepCode : Measurable (wholeStepCode (p := p) (rate := rate)) := by
  have hfollowers : Measurable (fun x : FirstLiveInput p rate =>
      fun i => followerObservable x i) := by
    apply measurable_pi_iff.mpr
    intro i
    exact measurable_followerObservable i
  exact ReferenceFirstLiveCoordinatorStepMeasurability.measurable_physicalCode.prodMk
    (hfollowers.prodMk measurable_successorCode)

/-- Every component of the joint code reconstructs the original prepared
coordinator observation, all original follower observations, and literal
successor from this same preparation and step. -/
theorem wholeStepCode_reconstructs (x : FirstLiveInput p rate) :
    ReferenceCollectionServiceTailMeasurability.decodeCollectionObservation
        (wholeStepCode x).1.2.2.2.2 =
        (ReferenceActivePhysicalStep.prepare x.val).observeCoordinator ∧
      (∀ i, ReferenceFollowerTailComposition.reconstructFollowerObservable
        ((wholeStepCode x).2.1 i) =
          (ReferenceActivePhysicalStep.prepare x.val).observeFollower i) ∧
      ReferenceActivePhysicalStepMeasurability.decodeState
        ((wholeStepCode x).2.2) = (ReferenceActivePhysicalStep.step x.val).next := by
  constructor
  · exact ReferenceFirstLiveCoordinatorStepMeasurability.physicalCode_observation_reconstructs x
  constructor
  · intro i
    exact followerObservable_reconstruct x i
  · exact ReferenceActivePhysicalStepMeasurability.successorCode_reconstruct x.val

end Bandits.Support.ReferenceFirstLiveStepMeasurability

end
