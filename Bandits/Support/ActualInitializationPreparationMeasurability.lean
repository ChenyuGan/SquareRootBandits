/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ActualInitializationRoundMeasurability

/-!
# Measurable preparation for one actual initialization round

This module codes the successful result of the existing physical
`prepare` operation over the exact `RoundInput` coordinates.  The code retains
the accepted coordinator prepared code, each bootstrap follower's existing
startup state and chosen arm, and each declared follower's own row, activation,
chosen arm, and full ordinary/dagger incoming configuration.  The failure
branch remains the physical `inputNotReady` result.

Sources: `sources/zip4/manuscript/07_public_setup.tex:55-114` and
`sources/zip4/manuscript/appendix_b_communication.tex:94-165`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.CompletePublicTable
open Bandits.Support.ActualBootstrapObservationCode
open Bandits.Support.BootstrapCoordinatorRoundMeasurability
open Bandits.Support.BootstrapObservedFollower
open Bandits.Support.BootstrapPhysicalInput
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.FollowerPrepareJointMeasurability
open Bandits.Support.FollowerVaryingActivationMeasurability
open Bandits.Support.ReferencePrelaunchFollower
open Bandits.Support.ActualInitializationPhysicalStep
open Bandits.Support.ActualInitializationRoundMeasurability
open Bandits.Support.ActiveRoundActions
open Bandits.Support.PublicDiscreteDraws

namespace Bandits.Support.ActualInitializationPreparationMeasurability

abbrev Parameters := ActualInitializationRoundMeasurability.Parameters
abbrev RateInput := ActualInitializationRoundMeasurability.RateInput
abbrev RoundInput (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) (C_star C_h : ℝ) :=
  ActualInitializationRoundMeasurability.RoundInput p rate block C_star C_h
abbrev ReadyInput (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) (C_star C_h : ℝ) :=
  {x : RoundInput p rate block C_star C_h //
    ActualInitializationRoundMeasurability.roundInputReady p rate block C_star C_h x}
abbrev FollowerCode (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) :=
  ActualInitializationRoundMeasurability.FollowerCode p rate block
abbrev StartupCode (p : Parameters) (block : Fin (n_boot p)) :=
  ActualBootstrapObservationCode.StartupCode p block
abbrev Activation (p : Parameters) := ReferencePrelaunchFollower.Activation p
abbrev IncomingCode (p : Parameters) (rate : RateInput p) :=
  FollowerPrepareJointMeasurability.IncomingConfiguration p rate
abbrev DeclaredInputCode (p : Parameters) (rate : RateInput p) :=
  Fin (M p) × (Activation p × IncomingCode p rate)
abbrev CoordinatorCode (p : Parameters) :=
  BootstrapCoordinatorRoundMeasurability.PreparedRoundCode p

private theorem prepareInputRow_assemblePrepareInput_exact {p : Parameters}
    {rate : RateInput p} {activation : Activation p}
    (incoming : IncomingCode p rate) (row : CompleteRow p)
    (time : FollowerPrepareJointMeasurability.ActiveCalendarTime p activation) :
    FollowerPrepareJointMeasurability.prepareInputRow
      (FollowerPrepareJointMeasurability.assemblePrepareInput incoming row time) = row := by
  cases incoming <;> rfl

private theorem prepareInputTime_assemblePrepareInput_exact {p : Parameters}
    {rate : RateInput p} {activation : Activation p}
    (incoming : IncomingCode p rate) (row : CompleteRow p)
    (time : FollowerPrepareJointMeasurability.ActiveCalendarTime p activation) :
    FollowerPrepareJointMeasurability.prepareInputTime
      (FollowerPrepareJointMeasurability.assemblePrepareInput incoming row time) = time := by
  cases incoming <;> rfl

private theorem measurable_of_sigma_sections_local {α : Type*} {β : α → Type*}
    [∀ a, MeasurableSpace (β a)] {γ : Type*} [MeasurableSpace γ]
    (f : Sigma β → γ) (hf : ∀ a, Measurable (fun x : β a => f ⟨a, x⟩)) :
    Measurable f := by
  intro s hs
  change MeasurableSet[(⨅ a, (inferInstance : MeasurableSpace (β a)).map (Sigma.mk a))]
    {x | f x ∈ s}
  rw [MeasurableSpace.measurableSet_iInf]
  intro a
  rw [MeasurableSpace.map_def]
  exact hf a hs

private theorem measurable_varyingPreparedOutputArm_local {p : Parameters}
    (rate : RateInput p) :
    Measurable (fun output : FollowerVaryingActivationMeasurability.VaryingPreparedOutput
      p rate => output.2.2.1) := by
  apply measurable_of_sigma_sections_local
  intro activation
  exact measurable_fst.comp measurable_snd

private theorem measurable_varyingPreparedOutputConfiguration_local {p : Parameters}
    (rate : RateInput p) :
    Measurable (fun output : FollowerVaryingActivationMeasurability.VaryingPreparedOutput
      p rate => output.2.2.2) := by
  apply measurable_of_sigma_sections_local
  intro activation
  exact measurable_snd.comp measurable_snd

/-! ## Literal lossless prepared-code carriers -/

/-- The bootstrap branch keeps the actual startup state and arm selected by
its own original player-round scalar. -/
abbrev PreparedBootstrapCode (p : Parameters) (block : Fin (n_boot p)) :=
  StartupCode p block × Fin p.K

/-- The declared branch keeps this follower's original row and activation,
the played arm, and the full ordinary/dagger incoming configuration. -/
abbrev PreparedDeclaredCode (p : Parameters) (rate : RateInput p) :=
  Fin (M p) × (Activation p × (Fin p.K × IncomingCode p rate))

/-- One follower's exact preparation code, with the actual startup and
declared physical branches kept disjoint. -/
abbrev PreparedFollowerCode (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) :=
  PreparedBootstrapCode p block ⊕ PreparedDeclaredCode p rate

/-- The joint preparation code consists of the accepted coordinator code and
the exact per-follower preparation codes. -/
abbrev PreparedRoundCode (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) :=
  CoordinatorCode p × (Fin (p.m - 1) → PreparedFollowerCode p rate block)

/-- Project the arm which is already present in either follower code branch. -/
def preparedFollowerCodeArm {p : Parameters} {rate : RateInput p}
    {block : Fin (n_boot p)} : PreparedFollowerCode p rate block → Fin p.K
  | .inl (_, arm) => arm
  | .inr (_, (_, (arm, _))) => arm

theorem measurable_preparedFollowerCodeArm {p : Parameters} {rate : RateInput p}
    {block : Fin (n_boot p)} :
    Measurable (preparedFollowerCodeArm (p := p) (rate := rate) (block := block)) := by
  apply Measurable.sumElim
  · exact measurable_snd
  · exact measurable_fst.comp (measurable_snd.comp measurable_snd)

/-! ## Coordinate measurability inherited from the accepted RoundInput -/

private theorem measurable_roundInputTime (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) (C_star C_h : ℝ) :
    Measurable (fun x : RoundInput p rate block C_star C_h => x.time) :=
  measurable_fst.comp
    (measurable_roundInputCoordinates p rate block C_star C_h)

private theorem measurable_roundInputCoordinatorRow (p : Parameters)
    (rate : RateInput p) (block : Fin (n_boot p)) (C_star C_h : ℝ) :
    Measurable (fun x : RoundInput p rate block C_star C_h => x.coordinatorRow) :=
  measurable_fst.comp <| measurable_snd.comp
    (measurable_roundInputCoordinates p rate block C_star C_h)

private theorem measurable_roundInputCoordinatorIDs (p : Parameters)
    (rate : RateInput p) (block : Fin (n_boot p)) (C_star C_h : ℝ) :
    Measurable (fun x : RoundInput p rate block C_star C_h => x.coordinatorIDs) :=
  measurable_fst.comp <| measurable_snd.comp <| measurable_snd.comp
    (measurable_roundInputCoordinates p rate block C_star C_h)

private theorem measurable_roundInputCoordinator (p : Parameters)
    (rate : RateInput p) (block : Fin (n_boot p)) (C_star C_h : ℝ) :
    Measurable (fun x : RoundInput p rate block C_star C_h => x.coordinator) :=
  measurable_fst.comp <| measurable_snd.comp <| measurable_snd.comp <| measurable_snd.comp
    (measurable_roundInputCoordinates p rate block C_star C_h)

private theorem measurable_roundInputFollowers (p : Parameters)
    (rate : RateInput p) (block : Fin (n_boot p)) (C_star C_h : ℝ) :
    Measurable (fun x : RoundInput p rate block C_star C_h => x.followers) :=
  measurable_fst.comp <| measurable_snd.comp <| measurable_snd.comp <|
    measurable_snd.comp <| measurable_snd.comp
      (measurable_roundInputCoordinates p rate block C_star C_h)

private theorem measurable_roundInputSource (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) (C_star C_h : ℝ) :
    Measurable (fun x : RoundInput p rate block C_star C_h => x.source) :=
  measurable_fst.comp <| measurable_snd.comp <| measurable_snd.comp <|
    measurable_snd.comp <| measurable_snd.comp <| measurable_snd.comp
      (measurable_roundInputCoordinates p rate block C_star C_h)

private theorem measurable_roundInputRewards (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) (C_star C_h : ℝ) :
    Measurable (fun x : RoundInput p rate block C_star C_h => x.rewards) :=
  measurable_snd.comp <| measurable_snd.comp <| measurable_snd.comp <|
    measurable_snd.comp <| measurable_snd.comp <| measurable_snd.comp
      (measurable_roundInputCoordinates p rate block C_star C_h)

private theorem measurable_playerRoundScalarAt_time (p : Parameters)
    (player : Fin p.m) :
    Measurable (fun z : BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p × Fin p.T =>
      BootstrapPhysicalInput.playerRoundScalarAt p z.1 player z.2) := by
  apply measurable_from_prod_countable_left
  intro time
  exact BootstrapPhysicalInput.measurable_playerRoundScalarAt p player time

private theorem measurable_roundInputFollowerCode (p : Parameters)
    (rate : RateInput p) (block : Fin (n_boot p)) (C_star C_h : ℝ)
    (i : Fin (p.m - 1)) :
    Measurable (fun x : RoundInput p rate block C_star C_h => x.followers i) :=
  (measurable_pi_apply i).comp
    (measurable_roundInputFollowers p rate block C_star C_h)

private theorem measurable_evalCompleteRows (p : Parameters) :
    Measurable (fun z : CompleteRows p × Fin (M p) => z.1 z.2) := by
  exact measurable_from_prod_countable_left fun j => measurable_pi_apply j

private theorem ready_time_mem_calendar {p : Parameters} (rate : RateInput p)
    (block : Fin (n_boot p)) (C_star C_h : ℝ)
    (x : ReadyInput p rate block C_star C_h) :
    x.1.time ∈ calendarBlock p block := by
  exact ((ActualInitializationRoundMeasurability.roundInputReady_iff_fields
    p rate block C_star C_h x.1).mp x.2).2.1

/-! ## The coordinator's accepted prepared-code producer -/

/-- The existing coordinator round input assembled from the original supplied
row, IDs, local code, constants, and calendar coordinate. -/
def coordinatorRoundInputOfReady {p : Parameters} (rate : RateInput p)
    (block : Fin (n_boot p)) (C_star C_h : ℝ)
    (x : ReadyInput p rate block C_star C_h) :
    BootstrapCoordinatorRoundMeasurability.CoordinatorRoundInput p := by
  have hfields := (ActualInitializationRoundMeasurability.roundInputReady_iff_fields
    p rate block C_star C_h x.1).mp x.2
  have hblock : x.1.coordinator.block = block := hfields.1
  refine ⟨((x.1.coordinatorRow, x.1.coordinatorIDs), (C_star, C_h)),
    x.1.coordinator, x.1.time, ?_⟩
  simpa [hblock] using hfields.2.1

/-- The coordinator's original private scalar at this calendar time. -/
def coordinatorOriginalRoundScalar {p : Parameters} (rate : RateInput p)
    (block : Fin (n_boot p)) (C_star C_h : ℝ)
    (x : ReadyInput p rate block C_star C_h) : BootstrapPrivateRoundStreams.Scalar :=
  BootstrapPhysicalInput.playerRoundScalarAt p
    (ActualBootstrapObservationCode.sourcePrivate p x.1.source)
    (ActiveRoundActions.coordinator p.two_le_m) x.1.time

/-- Consume the accepted coordinator prepared-code producer using the exact
original coordinator player-round scalar. -/
def preparedCoordinatorCodeOnReady {p : Parameters} (rate : RateInput p)
    (block : Fin (n_boot p)) (C_star C_h : ℝ)
    (x : ReadyInput p rate block C_star C_h) : CoordinatorCode p :=
  BootstrapCoordinatorRoundMeasurability.coordinatorPreparedRoundCode p
    (coordinatorRoundInputOfReady rate block C_star C_h x)
    (coordinatorOriginalRoundScalar rate block C_star C_h x)

theorem measurable_preparedCoordinatorCodeOnReady {p : Parameters}
    (rate : RateInput p) (block : Fin (n_boot p)) (C_star C_h : ℝ) :
    Measurable (preparedCoordinatorCodeOnReady rate block C_star C_h) := by
  let hcoe : Measurable
      (fun x : ReadyInput p rate block C_star C_h => (x.1 : RoundInput p rate block C_star C_h)) :=
    measurable_subtype_coe
  let hrow := (measurable_roundInputCoordinatorRow p rate block C_star C_h).comp hcoe
  let hids := (measurable_roundInputCoordinatorIDs p rate block C_star C_h).comp hcoe
  let hlocal := (measurable_roundInputCoordinator p rate block C_star C_h).comp hcoe
  let htime := (measurable_roundInputTime p rate block C_star C_h).comp hcoe
  have hbase : Measurable (fun x : ReadyInput p rate block C_star C_h =>
      ((x.1.coordinatorRow, x.1.coordinatorIDs), (C_star, C_h))) := by
    exact (hrow.prodMk hids).prodMk (measurable_const.prodMk measurable_const)
  have hroundInputCoordinates : Measurable
      (fun x : ReadyInput p rate block C_star C_h =>
        BootstrapCoordinatorRoundMeasurability.coordinatorRoundInputCoordinates p
          (coordinatorRoundInputOfReady rate block C_star C_h x)) := by
    exact hbase.prodMk (hlocal.prodMk htime)
  have hroundInput : Measurable
      (coordinatorRoundInputOfReady rate block C_star C_h) := by
    exact (measurable_comap_iff).2 hroundInputCoordinates
  have hsource := (measurable_roundInputSource p rate block C_star C_h).comp hcoe
  have hprivate := (ActualBootstrapObservationCode.measurable_sourcePrivate p).comp hsource
  have hscalar : Measurable (coordinatorOriginalRoundScalar rate block C_star C_h) := by
    exact (measurable_playerRoundScalarAt_time p
      (ActiveRoundActions.coordinator p.two_le_m)).comp (hprivate.prodMk htime)
  change Measurable (fun x : ReadyInput p rate block C_star C_h =>
    BootstrapCoordinatorRoundMeasurability.coordinatorPreparedRoundCode p
      (coordinatorRoundInputOfReady rate block C_star C_h x)
      (coordinatorOriginalRoundScalar rate block C_star C_h x))
  exact (BootstrapCoordinatorRoundMeasurability.measurable_coordinatorPreparedRoundCode p).comp
    (hroundInput.prodMk hscalar)

/-- The accepted coordinator decoder reconstructs exactly the prepared round
computed from the original coordinator scalar and this same ready input. -/
theorem reconstruct_preparedCoordinatorCodeOnReady {p : Parameters}
    (rate : RateInput p) (block : Fin (n_boot p)) (C_star C_h : ℝ)
    (x : ReadyInput p rate block C_star C_h) :
    BootstrapCoordinatorRoundMeasurability.reconstructPreparedRound p
      (coordinatorRoundInputOfReady rate block C_star C_h x)
      (preparedCoordinatorCodeOnReady rate block C_star C_h x) =
    some (BootstrapCoordinatorRoundMeasurability.coordinatorPreparedRound p
      (coordinatorRoundInputOfReady rate block C_star C_h x)
      (coordinatorOriginalRoundScalar rate block C_star C_h x)) :=
  BootstrapCoordinatorRoundMeasurability.reconstruct_coordinatorPreparedRoundCode p
    (coordinatorRoundInputOfReady rate block C_star C_h x)
    (coordinatorOriginalRoundScalar rate block C_star C_h x)

/-- The coordinator round reconstructed from the accepted code is exactly
the coordinator component of the existing physical `prepare` operation. -/
theorem coordinatorPreparedRoundOnReady_eq_physicalPrepare {p : Parameters}
    (rate : RateInput p) (block : Fin (n_boot p)) (C_star C_h : ℝ)
    (x : ReadyInput p rate block C_star C_h) :
    BootstrapCoordinatorRoundMeasurability.coordinatorPreparedRound p
      (coordinatorRoundInputOfReady rate block C_star C_h x)
      (coordinatorOriginalRoundScalar rate block C_star C_h x) =
    BootstrapCoordinatorLocalRound.prepare p
      (ActualInitializationRoundMeasurability.coordinatorOfInput
        p rate block C_star C_h x.1)
      x.1.time
      (by
        have hfields := (ActualInitializationRoundMeasurability.roundInputReady_iff_fields
          p rate block C_star C_h x.1).mp x.2
        change x.1.time ∈ calendarBlock p x.1.coordinator.block
        rw [hfields.1]
        exact hfields.2.1)
      (coordinatorOriginalRoundScalar rate block C_star C_h x) := by
  rfl

/-- Decoding the accepted coordinator code therefore returns the actual
physical coordinator preparation on the original row, IDs, constants, and
private scalar. -/
theorem reconstruct_preparedCoordinatorCodeOnReady_eq_physicalPrepare
    {p : Parameters} (rate : RateInput p) (block : Fin (n_boot p))
    (C_star C_h : ℝ) (x : ReadyInput p rate block C_star C_h) :
    BootstrapCoordinatorRoundMeasurability.reconstructPreparedRound p
      (coordinatorRoundInputOfReady rate block C_star C_h x)
      (preparedCoordinatorCodeOnReady rate block C_star C_h x) =
    some (BootstrapCoordinatorLocalRound.prepare p
      (ActualInitializationRoundMeasurability.coordinatorOfInput
        p rate block C_star C_h x.1)
      x.1.time
      (by
        have hfields := (ActualInitializationRoundMeasurability.roundInputReady_iff_fields
          p rate block C_star C_h x.1).mp x.2
        change x.1.time ∈ calendarBlock p x.1.coordinator.block
        rw [hfields.1]
        exact hfields.2.1)
      (coordinatorOriginalRoundScalar rate block C_star C_h x)) := by
  rw [reconstruct_preparedCoordinatorCodeOnReady,
    coordinatorPreparedRoundOnReady_eq_physicalPrepare]

/-! ## Bootstrap arm measurability from its original local inputs -/

/-- The actual bootstrap arm formula from one startup state, the original ID
array, calendar time, and that player's scalar at the same time. -/
def bootstrapLocalArmFromComponents {p : Parameters} (block : Fin (n_boot p))
    (z : StartupCode p block ×
      (IDArray p × (Fin p.T × BootstrapPrivateRoundStreams.Scalar))) : Fin p.K :=
  BootstrapObservedFollower.localArm p block z.1 z.2.1 z.2.2.1
    (fun _ => z.2.2.2)

theorem measurable_bootstrapLocalArmFromComponents {p : Parameters}
    (block : Fin (n_boot p)) :
    Measurable (bootstrapLocalArmFromComponents (p := p) block) := by
  apply measurable_from_prod_countable_right
  intro state
  unfold bootstrapLocalArmFromComponents
  cases hcase : state.blockCase with
  | inactive =>
      simp only [BootstrapObservedFollower.localArm, hcase]
      exact BootstrapPrivateRoundStreams.measurable_fullArmScalarDraw p |>.comp
        (measurable_snd.comp measurable_snd)
  | active held privateID gain registers =>
      have hid : Measurable (fun z : IDArray p × Fin p.T =>
          z.1 privateID z.2) := by
        apply measurable_from_prod_countable_left
        intro time
        exact (measurable_pi_apply time).comp (measurable_pi_apply privateID)
      have hidAt : Measurable (fun z : IDArray p ×
          (Fin p.T × BootstrapPrivateRoundStreams.Scalar) => z.1 privateID z.2.1) := by
        exact hid.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
      have hcondition : MeasurableSet {z : IDArray p ×
          (Fin p.T × BootstrapPrivateRoundStreams.Scalar) |
            z.1 privateID z.2.1 = true} :=
        (MeasurableSet.singleton true).preimage hidAt
      have hscalar : Measurable (fun z : IDArray p ×
          (Fin p.T × BootstrapPrivateRoundStreams.Scalar) => z.2.2) :=
        measurable_snd.comp measurable_snd
      have havoid : Measurable (fun z : IDArray p ×
          (Fin p.T × BootstrapPrivateRoundStreams.Scalar) =>
            (BootstrapPrivateRoundStreams.forbiddenArmScalarDraw p held
              (z.2.2)).val) := by
        exact (measurable_subtype_coe.comp
          (BootstrapPrivateRoundStreams.measurable_forbiddenArmScalarDraw p held)).comp hscalar
      simp only [BootstrapObservedFollower.localArm, hcase]
      exact Measurable.ite hcondition havoid measurable_const

/-! ## Heterogeneous follower preparation -/

/-- The measurable bootstrap branch of one follower's preparation code. -/
def followerBootstrapCodeSet {p : Parameters} (rate : RateInput p)
    (block : Fin (n_boot p)) (C_star C_h : ℝ) (i : Fin (p.m - 1)) :
    Set (ReadyInput p rate block C_star C_h) :=
  {x | x.1.followers i ∈ Set.range Sum.inl}

theorem measurableSet_followerBootstrapCodeSet {p : Parameters}
    (rate : RateInput p) (block : Fin (n_boot p)) (C_star C_h : ℝ)
    (i : Fin (p.m - 1)) :
    MeasurableSet (followerBootstrapCodeSet rate block C_star C_h i) := by
  have hfollowers : Measurable
      (fun x : ReadyInput p rate block C_star C_h => x.1.followers i) := by
    exact (measurable_roundInputFollowerCode p rate block C_star C_h i).comp
      measurable_subtype_coe
  exact (measurableSet_range_inl : MeasurableSet
    (Set.range (Sum.inl :
      StartupCode p block → FollowerCode p rate block))).preimage hfollowers

private theorem measurable_followerCodeOnReady {p : Parameters}
    (rate : RateInput p) (block : Fin (n_boot p)) (C_star C_h : ℝ)
    (i : Fin (p.m - 1)) :
    Measurable (fun x : ReadyInput p rate block C_star C_h => x.1.followers i) := by
  exact (measurable_roundInputFollowerCode p rate block C_star C_h i).comp
    measurable_subtype_coe

def followerStartupCodeOnBootstrap {p : Parameters}
    (rate : RateInput p) (block : Fin (n_boot p)) (C_star C_h : ℝ)
    (i : Fin (p.m - 1))
    (x : followerBootstrapCodeSet rate block C_star C_h i) : StartupCode p block :=
  Equiv.Set.rangeInl (StartupCode p block) (DeclaredInputCode p rate)
    ⟨x.1.1.followers i, x.2⟩

private theorem measurable_followerStartupCodeOnBootstrap {p : Parameters}
    (rate : RateInput p) (block : Fin (n_boot p)) (C_star C_h : ℝ)
    (i : Fin (p.m - 1)) :
    Measurable (followerStartupCodeOnBootstrap rate block C_star C_h i) := by
  have hcode := measurable_followerCodeOnReady rate block C_star C_h i
  have hrange : Measurable
      (fun x : followerBootstrapCodeSet rate block C_star C_h i =>
        (⟨x.1.1.followers i, x.2⟩ : Set.range
          (Sum.inl : StartupCode p block → FollowerCode p rate block))) := by
    exact (hcode.comp measurable_subtype_coe).subtype_mk
  exact MeasurableEquiv.Set.rangeInl.measurable_toFun.comp hrange

def followerDeclaredCodeOnReady {p : Parameters}
    (rate : RateInput p) (block : Fin (n_boot p)) (C_star C_h : ℝ)
    (i : Fin (p.m - 1))
    (x : ↥((followerBootstrapCodeSet rate block C_star C_h i)ᶜ)) :
    DeclaredInputCode p rate := by
  have hmem : x.1.1.followers i ∈ Set.range
      (Sum.inr : DeclaredInputCode p rate → FollowerCode p rate block) := by
    cases hcode : x.1.1.followers i with
    | inl startup => exact (x.2 ⟨startup, hcode.symm⟩).elim
    | inr fields => exact ⟨fields, rfl⟩
  exact Equiv.Set.rangeInr (StartupCode p block) (DeclaredInputCode p rate)
    ⟨x.1.1.followers i, hmem⟩

theorem followerCode_eq_inr_of_declared {p : Parameters}
    (rate : RateInput p) (block : Fin (n_boot p)) (C_star C_h : ℝ)
    (i : Fin (p.m - 1))
    (x : ↥((followerBootstrapCodeSet rate block C_star C_h i)ᶜ)) :
    x.1.1.followers i = Sum.inr (followerDeclaredCodeOnReady rate block C_star C_h i x) := by
  cases hcode : x.1.1.followers i with
  | inl startup => exact (x.2 ⟨startup, hcode.symm⟩).elim
  | inr fields =>
      have hfields : followerDeclaredCodeOnReady rate block C_star C_h i x = fields := by
        simp [followerDeclaredCodeOnReady, hcode]
      exact congrArg Sum.inr hfields.symm

private theorem measurable_followerDeclaredCodeOnReady {p : Parameters}
    (rate : RateInput p) (block : Fin (n_boot p)) (C_star C_h : ℝ)
    (i : Fin (p.m - 1)) :
    Measurable (followerDeclaredCodeOnReady rate block C_star C_h i) := by
  have hcode := measurable_followerCodeOnReady rate block C_star C_h i
  have hmem (x : ↥((followerBootstrapCodeSet rate block C_star C_h i)ᶜ)) :
      x.1.1.followers i ∈ Set.range
        (Sum.inr : DeclaredInputCode p rate → FollowerCode p rate block) := by
    cases hvalue : x.1.1.followers i with
    | inl startup => exact (x.2 ⟨startup, hvalue.symm⟩).elim
    | inr fields => exact ⟨fields, rfl⟩
  have hrange : Measurable
      (fun x : ↥((followerBootstrapCodeSet rate block C_star C_h i)ᶜ) =>
        (⟨x.1.1.followers i, hmem x⟩ : Set.range
          (Sum.inr : DeclaredInputCode p rate → FollowerCode p rate block))) := by
    have hraw : Measurable (fun x :
        ↥((followerBootstrapCodeSet rate block C_star C_h i)ᶜ) =>
          x.1.1.followers i) :=
      hcode.comp measurable_subtype_coe
    exact hraw.codRestrict (fun x => hmem x)
  exact MeasurableEquiv.Set.rangeInr.measurable_toFun.comp hrange

theorem declaredActivation_le_time_of_ready {p : Parameters}
    (rate : RateInput p) (block : Fin (n_boot p)) (C_star C_h : ℝ)
    (i : Fin (p.m - 1)) (x : ReadyInput p rate block C_star C_h)
    (fields : DeclaredInputCode p rate)
    (hcode : x.1.followers i = Sum.inr fields) :
    fields.2.1.val ≤ x.1.time.val + 1 := by
  have hcursor := ((ActualInitializationRoundMeasurability.roundInputReady_iff_fields
    p rate block C_star C_h x.1).mp x.2).2.2.2.2.2 i
  rw [hcode] at hcursor
  simpa [ActualInitializationRoundMeasurability.followerStateOfCode,
    ActualInitializationPhysicalStep.followerAtNextCursor] using hcursor

def followerPreparedCodeOnBootstrap {p : Parameters}
    (rate : RateInput p) (block : Fin (n_boot p)) (C_star C_h : ℝ)
    (i : Fin (p.m - 1))
    (x : followerBootstrapCodeSet rate block C_star C_h i) :
    PreparedFollowerCode p rate block := by
  let state := followerStartupCodeOnBootstrap rate block C_star C_h i x
  let input := x.1.1
  let ids := ActualBootstrapObservationCode.sourceIDs p input.source
  let scalar := BootstrapPhysicalInput.playerRoundScalarAt p
    (ActualBootstrapObservationCode.sourcePrivate p input.source)
    (PublicDiscreteDraws.followerPlayer p.two_le_m i) input.time
  exact Sum.inl (state, BootstrapObservedFollower.localArm p block state ids input.time
    (fun _ => scalar))

private theorem measurable_followerPreparedCodeOnBootstrap {p : Parameters}
    (rate : RateInput p) (block : Fin (n_boot p)) (C_star C_h : ℝ)
    (i : Fin (p.m - 1)) :
    Measurable (followerPreparedCodeOnBootstrap rate block C_star C_h i) := by
  have hstate := measurable_followerStartupCodeOnBootstrap rate block C_star C_h i
  have hcoe : Measurable (fun x : followerBootstrapCodeSet rate block C_star C_h i =>
      (x.1.1 : RoundInput p rate block C_star C_h)) :=
    measurable_subtype_coe.comp measurable_subtype_coe
  have hsource := (measurable_roundInputSource p rate block C_star C_h).comp hcoe
  have hids := (ActualBootstrapObservationCode.measurable_sourceIDs p).comp hsource
  have hprivate := (ActualBootstrapObservationCode.measurable_sourcePrivate p).comp hsource
  have htime := (measurable_roundInputTime p rate block C_star C_h).comp hcoe
  have hscalar : Measurable (fun x : followerBootstrapCodeSet rate block C_star C_h i =>
      BootstrapPhysicalInput.playerRoundScalarAt p
        (ActualBootstrapObservationCode.sourcePrivate p x.1.1.source)
        (PublicDiscreteDraws.followerPlayer p.two_le_m i) x.1.1.time) := by
    exact (measurable_playerRoundScalarAt_time p
      (PublicDiscreteDraws.followerPlayer p.two_le_m i)).comp (hprivate.prodMk htime)
  have harm : Measurable (fun x : followerBootstrapCodeSet rate block C_star C_h i =>
      BootstrapObservedFollower.localArm p block
        (followerStartupCodeOnBootstrap rate block C_star C_h i x)
        (ActualBootstrapObservationCode.sourceIDs p x.1.1.source) x.1.1.time
        (fun _ => BootstrapPhysicalInput.playerRoundScalarAt p
          (ActualBootstrapObservationCode.sourcePrivate p x.1.1.source)
          (PublicDiscreteDraws.followerPlayer p.two_le_m i) x.1.1.time)) := by
    change Measurable (fun x : followerBootstrapCodeSet rate block C_star C_h i =>
      bootstrapLocalArmFromComponents block
        (followerStartupCodeOnBootstrap rate block C_star C_h i x,
          (ActualBootstrapObservationCode.sourceIDs p x.1.1.source,
            (x.1.1.time,
              BootstrapPhysicalInput.playerRoundScalarAt p
                (ActualBootstrapObservationCode.sourcePrivate p x.1.1.source)
                (PublicDiscreteDraws.followerPlayer p.two_le_m i) x.1.1.time))))
    exact (measurable_bootstrapLocalArmFromComponents block).comp
      (hstate.prodMk (hids.prodMk (htime.prodMk hscalar)))
  change Measurable (fun x : followerBootstrapCodeSet rate block C_star C_h i =>
    Sum.inl (followerStartupCodeOnBootstrap rate block C_star C_h i x,
      BootstrapObservedFollower.localArm p block
        (followerStartupCodeOnBootstrap rate block C_star C_h i x)
        (ActualBootstrapObservationCode.sourceIDs p x.1.1.source) x.1.1.time
        (fun _ => BootstrapPhysicalInput.playerRoundScalarAt p
          (ActualBootstrapObservationCode.sourcePrivate p x.1.1.source)
          (PublicDiscreteDraws.followerPlayer p.two_le_m i) x.1.1.time)))
  exact measurable_inl.comp (hstate.prodMk harm)

def followerPreparedCodeOnDeclared {p : Parameters}
    (rate : RateInput p) (block : Fin (n_boot p)) (C_star C_h : ℝ)
    (i : Fin (p.m - 1))
    (x : ↥((followerBootstrapCodeSet rate block C_star C_h i)ᶜ)) :
    PreparedFollowerCode p rate block := by
  let fields := followerDeclaredCodeOnReady rate block C_star C_h i x
  let input := x.1.1
  let rowIndex := fields.1
  let activation := fields.2.1
  let incoming := fields.2.2
  let row := ActualBootstrapObservationCode.sourceRows p input.source rowIndex
  let time := input.time
  have hvalid : activation.val ≤ time.val + 1 :=
    declaredActivation_le_time_of_ready rate block C_star C_h i x.1 fields
      (followerCode_eq_inr_of_declared rate block C_star C_h i x)
  let varyingInput := FollowerVaryingActivationMeasurability.assembleVaryingPrepareInput
    activation incoming row time hvalid
  let output := FollowerVaryingActivationMeasurability.varyingPreparedOutput rate i
    varyingInput
  exact Sum.inr (rowIndex, (activation,
    (output.2.2.1, output.2.2.2)))

private theorem measurable_followerPreparedCodeOnDeclared {p : Parameters}
    (rate : RateInput p) (block : Fin (n_boot p)) (C_star C_h : ℝ)
    (i : Fin (p.m - 1)) :
    Measurable (followerPreparedCodeOnDeclared rate block C_star C_h i) := by
  let fields := followerDeclaredCodeOnReady rate block C_star C_h i
  let hcode := measurable_followerDeclaredCodeOnReady rate block C_star C_h i
  have hrowIndex : Measurable (fun x :
      ↥((followerBootstrapCodeSet rate block C_star C_h i)ᶜ) =>
        (followerDeclaredCodeOnReady rate block C_star C_h i x).1) :=
    measurable_fst.comp hcode
  have hactivation : Measurable (fun x :
      ↥((followerBootstrapCodeSet rate block C_star C_h i)ᶜ) =>
        (followerDeclaredCodeOnReady rate block C_star C_h i x).2.1) :=
    measurable_fst.comp (measurable_snd.comp hcode)
  have hincoming : Measurable (fun x :
      ↥((followerBootstrapCodeSet rate block C_star C_h i)ᶜ) =>
        (followerDeclaredCodeOnReady rate block C_star C_h i x).2.2) :=
    measurable_snd.comp (measurable_snd.comp hcode)
  have hcoe : Measurable (fun x :
      ↥((followerBootstrapCodeSet rate block C_star C_h i)ᶜ) =>
        (x.1.1 : RoundInput p rate block C_star C_h)) :=
    measurable_subtype_coe.comp measurable_subtype_coe
  have hsource := (measurable_roundInputSource p rate block C_star C_h).comp hcoe
  have hrows := (ActualBootstrapObservationCode.measurable_sourceRows p).comp hsource
  have hrow : Measurable (fun x :
      ↥((followerBootstrapCodeSet rate block C_star C_h i)ᶜ) =>
        ActualBootstrapObservationCode.sourceRows p x.1.1.source
          (followerDeclaredCodeOnReady rate block C_star C_h i x).1) := by
    exact (measurable_evalCompleteRows p).comp (hrows.prodMk hrowIndex)
  have htime : Measurable (fun x :
      ↥((followerBootstrapCodeSet rate block C_star C_h i)ᶜ) => x.1.1.time) :=
    (measurable_roundInputTime p rate block C_star C_h).comp hcoe
  have hvalid (x : ↥((followerBootstrapCodeSet rate block C_star C_h i)ᶜ)) :
      (followerDeclaredCodeOnReady rate block C_star C_h i x).2.1.val ≤
        x.1.1.time.val + 1 :=
    declaredActivation_le_time_of_ready rate block C_star C_h i x.1
      (followerDeclaredCodeOnReady rate block C_star C_h i x)
      (followerCode_eq_inr_of_declared rate block C_star C_h i x)
  let hinput : Measurable (fun x :
      ↥((followerBootstrapCodeSet rate block C_star C_h i)ᶜ) =>
        FollowerVaryingActivationMeasurability.assembleVaryingPrepareInput
          (followerDeclaredCodeOnReady rate block C_star C_h i x).2.1
          (followerDeclaredCodeOnReady rate block C_star C_h i x).2.2
          (ActualBootstrapObservationCode.sourceRows p x.1.1.source
            (followerDeclaredCodeOnReady rate block C_star C_h i x).1)
          x.1.1.time (hvalid x)) := by
    exact FollowerVaryingActivationMeasurability.measurable_assembleVaryingPrepareInput
      rate (fun x => (followerDeclaredCodeOnReady rate block C_star C_h i x).2.1)
      (fun x => (followerDeclaredCodeOnReady rate block C_star C_h i x).2.2)
      (fun x => ActualBootstrapObservationCode.sourceRows p x.1.1.source
        (followerDeclaredCodeOnReady rate block C_star C_h i x).1)
      (fun x => x.1.1.time) hactivation hincoming hrow htime hvalid
  have houtput : Measurable (fun x :
      ↥((followerBootstrapCodeSet rate block C_star C_h i)ᶜ) =>
        FollowerVaryingActivationMeasurability.varyingPreparedOutput rate i
          (FollowerVaryingActivationMeasurability.assembleVaryingPrepareInput
            (followerDeclaredCodeOnReady rate block C_star C_h i x).2.1
            (followerDeclaredCodeOnReady rate block C_star C_h i x).2.2
            (ActualBootstrapObservationCode.sourceRows p x.1.1.source
              (followerDeclaredCodeOnReady rate block C_star C_h i x).1)
            x.1.1.time (hvalid x))) := by
    exact (FollowerVaryingActivationMeasurability.measurable_varyingPreparedOutput
      rate i).comp hinput
  have harm : Measurable (fun x :
      ↥((followerBootstrapCodeSet rate block C_star C_h i)ᶜ) =>
        (FollowerVaryingActivationMeasurability.varyingPreparedOutput rate i
          (FollowerVaryingActivationMeasurability.assembleVaryingPrepareInput
            (followerDeclaredCodeOnReady rate block C_star C_h i x).2.1
            (followerDeclaredCodeOnReady rate block C_star C_h i x).2.2
            (ActualBootstrapObservationCode.sourceRows p x.1.1.source
              (followerDeclaredCodeOnReady rate block C_star C_h i x).1)
            x.1.1.time (hvalid x))).2.2.1) :=
    measurable_varyingPreparedOutputArm_local rate |>.comp houtput
  have hconfiguration : Measurable (fun x :
      ↥((followerBootstrapCodeSet rate block C_star C_h i)ᶜ) =>
        (FollowerVaryingActivationMeasurability.varyingPreparedOutput rate i
          (FollowerVaryingActivationMeasurability.assembleVaryingPrepareInput
            (followerDeclaredCodeOnReady rate block C_star C_h i x).2.1
            (followerDeclaredCodeOnReady rate block C_star C_h i x).2.2
            (ActualBootstrapObservationCode.sourceRows p x.1.1.source
              (followerDeclaredCodeOnReady rate block C_star C_h i x).1)
            x.1.1.time (hvalid x))).2.2.2) :=
    measurable_varyingPreparedOutputConfiguration_local rate |>.comp houtput
  change Measurable (fun x :
    ↥((followerBootstrapCodeSet rate block C_star C_h i)ᶜ) =>
      Sum.inr ((followerDeclaredCodeOnReady rate block C_star C_h i x).1,
        ((followerDeclaredCodeOnReady rate block C_star C_h i x).2.1,
          ((FollowerVaryingActivationMeasurability.varyingPreparedOutput rate i
              (FollowerVaryingActivationMeasurability.assembleVaryingPrepareInput
                (followerDeclaredCodeOnReady rate block C_star C_h i x).2.1
                (followerDeclaredCodeOnReady rate block C_star C_h i x).2.2
                (ActualBootstrapObservationCode.sourceRows p x.1.1.source
                  (followerDeclaredCodeOnReady rate block C_star C_h i x).1)
                x.1.1.time (hvalid x))).2.2.1,
            (FollowerVaryingActivationMeasurability.varyingPreparedOutput rate i
              (FollowerVaryingActivationMeasurability.assembleVaryingPrepareInput
                (followerDeclaredCodeOnReady rate block C_star C_h i x).2.1
                (followerDeclaredCodeOnReady rate block C_star C_h i x).2.2
                (ActualBootstrapObservationCode.sourceRows p x.1.1.source
                  (followerDeclaredCodeOnReady rate block C_star C_h i x).1)
                x.1.1.time (hvalid x))).2.2.2))))
  exact measurable_inr.comp (hrowIndex.prodMk (hactivation.prodMk
    (harm.prodMk hconfiguration)))

/-- The lossless code for an actual follower's preparation on the measurable
ready locus. -/
def preparedFollowerCodeOnReady {p : Parameters} (rate : RateInput p)
    (block : Fin (n_boot p)) (C_star C_h : ℝ) (i : Fin (p.m - 1))
    (x : ReadyInput p rate block C_star C_h) : PreparedFollowerCode p rate block :=
  by
  classical
  exact Sum.elim (followerPreparedCodeOnBootstrap rate block C_star C_h i)
    (followerPreparedCodeOnDeclared rate block C_star C_h i)
    ((MeasurableEquiv.sumCompl
      (s := followerBootstrapCodeSet rate block C_star C_h i)
      (measurableSet_followerBootstrapCodeSet rate block C_star C_h i)).symm x)

theorem measurable_preparedFollowerCodeOnReady {p : Parameters}
    (rate : RateInput p) (block : Fin (n_boot p)) (C_star C_h : ℝ)
    (i : Fin (p.m - 1)) :
    Measurable (preparedFollowerCodeOnReady rate block C_star C_h i) := by
  classical
  exact (Measurable.sumElim
    (measurable_followerPreparedCodeOnBootstrap rate block C_star C_h i)
    (measurable_followerPreparedCodeOnDeclared rate block C_star C_h i)).comp
      (MeasurableEquiv.sumCompl
        (s := followerBootstrapCodeSet rate block C_star C_h i)
        (measurableSet_followerBootstrapCodeSet rate block C_star C_h i)).symm.measurable_toFun

/-- The exact source preparation code on the ready subtype. -/
def preparedRoundCodeOnReady {p : Parameters} (rate : RateInput p)
    (block : Fin (n_boot p)) (C_star C_h : ℝ)
    (x : ReadyInput p rate block C_star C_h) : PreparedRoundCode p rate block :=
  (preparedCoordinatorCodeOnReady rate block C_star C_h x,
    fun i => preparedFollowerCodeOnReady rate block C_star C_h i x)

/-- Joint successful code assembly uses only the actual coordinator and
heterogeneous follower coordinates of the ready `RoundInput`. -/
theorem measurable_preparedRoundCodeOnReady {p : Parameters}
    (rate : RateInput p) (block : Fin (n_boot p)) (C_star C_h : ℝ) :
    Measurable (preparedRoundCodeOnReady rate block C_star C_h) := by
  have hfollowers : Measurable
      (fun x : ReadyInput p rate block C_star C_h =>
        fun i => preparedFollowerCodeOnReady rate block C_star C_h i x) := by
    apply measurable_pi_iff.mpr
    intro i
    exact measurable_preparedFollowerCodeOnReady rate block C_star C_h i
  exact (measurable_preparedCoordinatorCodeOnReady rate block C_star C_h).prodMk
    hfollowers

/-! ## Exact follower and coordinator decoding -/

/-- Decode one declared follower code to the existing prepared-round carrier,
using the original row and time supplied by the same `RoundInput`. -/
def decodePreparedFollowerCode {p : Parameters} (rate : RateInput p)
    {block : Fin (n_boot p)}
    (i : Fin (p.m - 1)) (source : ActualBootstrapObservationCode.ActualSource p)
    (time : Fin p.T) : PreparedFollowerCode p rate block →
      Option (ActualInitializationPhysicalStep.PreparedFollower p rate block)
  | .inl (state, arm) => some (.bootstrap state arm)
  | .inr (rowIndex, (activation, (arm, incoming))) => by
      classical
      by_cases hvalid : activation.val ≤ time.val + 1
      · exact some (.declared rowIndex activation
          (FollowerPrepareJointMeasurability.preparedRoundOfOutput rate i activation
            ((ActualBootstrapObservationCode.sourceRows p source rowIndex,
              ⟨time, hvalid⟩), (arm, incoming))))
      · exact none

theorem readyFollowerCursorProof {p : Parameters} (rate : RateInput p)
    (block : Fin (n_boot p)) (C_star C_h : ℝ)
    (i : Fin (p.m - 1)) (x : ReadyInput p rate block C_star C_h) :
    ActualInitializationPhysicalStep.followerAtNextCursor x.1.time
      (ActualInitializationRoundMeasurability.followerStateOfCode p rate block
        (x.1.followers i)) :=
  ((ActualInitializationRoundMeasurability.roundInputReady_iff_fields
    p rate block C_star C_h x.1).mp x.2).2.2.2.2.2 i

/-- The prepared follower code is decoded exactly to the accepted
`prepareFollowerValid` result on the ready branch. -/
theorem decode_preparedFollowerCodeOnReady {p : Parameters}
    (rate : RateInput p) (block : Fin (n_boot p)) (C_star C_h : ℝ)
    (i : Fin (p.m - 1)) (x : ReadyInput p rate block C_star C_h) :
    decodePreparedFollowerCode (rate := rate) (block := block) i x.1.source x.1.time
        (preparedFollowerCodeOnReady rate block C_star C_h i x) =
      some (ActualInitializationPhysicalStep.prepareFollowerValid rate block
        x.1.time x.1.source i
        (ActualInitializationRoundMeasurability.followerStateOfCode p rate block
          (x.1.followers i))
        (readyFollowerCursorProof rate block C_star C_h i x)) := by
  classical
  have hcursor : ActualInitializationPhysicalStep.followerAtNextCursor x.1.time
      (ActualInitializationRoundMeasurability.followerStateOfCode p rate block
        (x.1.followers i)) :=
    readyFollowerCursorProof rate block C_star C_h i x
  change decodePreparedFollowerCode (rate := rate) (block := block) i
      x.1.source x.1.time (preparedFollowerCodeOnReady rate block C_star C_h i x) =
    some (ActualInitializationPhysicalStep.prepareFollowerValid rate block
      x.1.time x.1.source i
      (ActualInitializationRoundMeasurability.followerStateOfCode p rate block
        (x.1.followers i)) hcursor)
  revert hcursor
  let split := MeasurableEquiv.sumCompl
    (s := followerBootstrapCodeSet rate block C_star C_h i)
    (measurableSet_followerBootstrapCodeSet rate block C_star C_h i)
  cases hcode : x.1.followers i with
  | inl startup =>
      intro hcursor
      have hmem : x ∈ followerBootstrapCodeSet rate block C_star C_h i := by
        exact ⟨startup, hcode.symm⟩
      let startupInput : followerBootstrapCodeSet rate block C_star C_h i := ⟨x, hmem⟩
      have hsplit : split.symm x = Sum.inl startupInput := by
        change (Equiv.Set.sumCompl
          (followerBootstrapCodeSet rate block C_star C_h i)).symm x =
            Sum.inl startupInput
        exact Equiv.Set.sumCompl_symm_apply_of_mem hmem
      have hstartup :
          followerStartupCodeOnBootstrap rate block C_star C_h i startupInput = startup := by
        simp [followerStartupCodeOnBootstrap, startupInput, hcode]
      let ids := ActualBootstrapObservationCode.sourceIDs p x.1.source
      let scalar := BootstrapPhysicalInput.playerRoundScalarAt p
        (ActualBootstrapObservationCode.sourcePrivate p x.1.source)
        (PublicDiscreteDraws.followerPlayer p.two_le_m i) x.1.time
      have hlocal :
          BootstrapObservedFollower.localArm p block startup ids x.1.time (fun _ => scalar) =
            BootstrapObservedFollower.localArm p block startup ids x.1.time
              (fun t => BootstrapPhysicalInput.playerRoundScalarAt p
                (ActualBootstrapObservationCode.sourcePrivate p x.1.source)
                (PublicDiscreteDraws.followerPlayer p.two_le_m i) t) := by
        exact BootstrapObservedFollower.localArm_current_scalar_locality p block startup ids
          x.1.time (fun _ => scalar)
          (fun t => BootstrapPhysicalInput.playerRoundScalarAt p
            (ActualBootstrapObservationCode.sourcePrivate p x.1.source)
            (PublicDiscreteDraws.followerPlayer p.two_le_m i) t) rfl
      simp [preparedFollowerCodeOnReady, split, hsplit,
        followerPreparedCodeOnBootstrap, hstartup, decodePreparedFollowerCode,
        ActualInitializationRoundMeasurability.followerStateOfCode,
        ActualInitializationPhysicalStep.prepareFollowerValid]
      rw [hlocal]
      simp [ids, ActualBootstrapObservationCode.sourceIDs,
        ActualBootstrapObservationCode.sourcePrivate]
  | inr fields =>
      intro hcursor
      have hnotmem : x ∈ (followerBootstrapCodeSet rate block C_star C_h i)ᶜ := by
        intro hmem
        rcases hmem with ⟨startup, hstartup⟩
        cases hstartup.trans hcode
      let declaredInput : ↥((followerBootstrapCodeSet rate block C_star C_h i)ᶜ) :=
        ⟨x, hnotmem⟩
      have hsplit : split.symm x = Sum.inr declaredInput := by
        change (Equiv.Set.sumCompl
          (followerBootstrapCodeSet rate block C_star C_h i)).symm x =
            Sum.inr declaredInput
        exact Equiv.Set.sumCompl_symm_apply_of_notMem hnotmem
      have hfields :
          followerDeclaredCodeOnReady rate block C_star C_h i declaredInput = fields := by
        simp [followerDeclaredCodeOnReady, declaredInput, hcode]
      have hvalid : fields.2.1.val ≤ x.1.time.val + 1 :=
        declaredActivation_le_time_of_ready rate block C_star C_h i x fields hcode
      have hvalidDecoded :
          (followerDeclaredCodeOnReady rate block C_star C_h i declaredInput).2.1.val ≤
            x.1.time.val + 1 := by
        simpa only [hfields] using hvalid
      have hprepare := FollowerVaryingActivationMeasurability.assembledPrepare_reconstructs_prepare
        rate i (followerDeclaredCodeOnReady rate block C_star C_h i declaredInput).2.1
        (followerDeclaredCodeOnReady rate block C_star C_h i declaredInput).2.2
        (ActualBootstrapObservationCode.sourceRows p x.1.source
          (followerDeclaredCodeOnReady rate block C_star C_h i declaredInput).1)
        x.1.time hvalidDecoded
      simp only [preparedFollowerCodeOnReady, split, hsplit, Sum.elim_inr]
      change decodePreparedFollowerCode (rate := rate) (block := block) i
          x.1.source x.1.time
          (followerPreparedCodeOnDeclared rate block C_star C_h i declaredInput) =
        some (ActualInitializationPhysicalStep.prepareFollowerValid rate block
          x.1.time x.1.source i
          (ActualInitializationRoundMeasurability.followerStateOfCode p rate block
            (Sum.inr fields)) hcursor)
      simp only [followerPreparedCodeOnDeclared,
        FollowerVaryingActivationMeasurability.varyingPreparedOutput,
        FollowerVaryingActivationMeasurability.assembleVaryingPrepareInput,
        decodePreparedFollowerCode]
      rw [dite_eq_left hvalidDecoded]
      have hprepareOption := congrArg
        (fun y : DeclaredFollowerLocalRound.PreparedRound p rate =>
          some (ActualInitializationPhysicalStep.PreparedFollower.declared
            (p := p) (rate := rate) (block := block)
            (followerDeclaredCodeOnReady rate block C_star C_h i declaredInput).1
            (followerDeclaredCodeOnReady rate block C_star C_h i declaredInput).2.1 y)) hprepare
      simpa [followerPreparedCodeOnDeclared, hfields, declaredInput,
        FollowerVaryingActivationMeasurability.varyingPreparedOutput,
        FollowerVaryingActivationMeasurability.assembleVaryingPrepareInput,
        FollowerPrepareJointMeasurability.prepareOutputOnInput,
        prepareInputRow_assemblePrepareInput_exact,
        prepareInputTime_assemblePrepareInput_exact,
        ActualInitializationPhysicalStep.prepareFollowerValid,
        ActualInitializationPhysicalStep.followerAtNextCursor,
        ActualInitializationRoundMeasurability.followerStateOfCode,
        ActualBootstrapObservationCode.sourceRows] using hprepareOption

/-- The actual readiness predicate is already measurable on the full input;
this subtype keeps its proof solely for constructing genuine active times. -/
theorem measurableSet_roundInputReady {p : Parameters}
    (rate : RateInput p) (block : Fin (n_boot p)) (C_star C_h : ℝ) :
    MeasurableSet {x : RoundInput p rate block C_star C_h |
      ActualInitializationRoundMeasurability.roundInputReady p rate block C_star C_h x} :=
  ActualInitializationRoundMeasurability.measurableSet_roundInputReady
    p rate block C_star C_h

/-! ## Actual arm maps and simultaneous physical output -/

/-- Coordinator's actual prepared arm, projected from its accepted prepared
code. -/
def preparedCoordinatorArmOnReady {p : Parameters} (rate : RateInput p)
    (block : Fin (n_boot p)) (C_star C_h : ℝ)
    (x : ReadyInput p rate block C_star C_h) : Fin p.K :=
  (preparedCoordinatorCodeOnReady rate block C_star C_h x).2.2

/-- Each follower's actual prepared arm, projected from its own prepared
code branch. -/
def preparedFollowerArmOnReady {p : Parameters} (rate : RateInput p)
    (block : Fin (n_boot p)) (C_star C_h : ℝ) (i : Fin (p.m - 1))
    (x : ReadyInput p rate block C_star C_h) : Fin p.K :=
  preparedFollowerCodeArm (preparedFollowerCodeOnReady rate block C_star C_h i x)

theorem measurable_preparedCoordinatorArmOnReady {p : Parameters}
    (rate : RateInput p) (block : Fin (n_boot p)) (C_star C_h : ℝ) :
    Measurable (preparedCoordinatorArmOnReady rate block C_star C_h) := by
  change Measurable (fun x : ReadyInput p rate block C_star C_h =>
    (preparedCoordinatorCodeOnReady rate block C_star C_h x).2.2)
  exact measurable_snd.comp (measurable_snd.comp
    (measurable_preparedCoordinatorCodeOnReady rate block C_star C_h))

theorem measurable_preparedFollowerArmOnReady {p : Parameters}
    (rate : RateInput p) (block : Fin (n_boot p)) (C_star C_h : ℝ)
    (i : Fin (p.m - 1)) :
    Measurable (preparedFollowerArmOnReady rate block C_star C_h i) :=
  (measurable_preparedFollowerCodeArm.comp
    (measurable_preparedFollowerCodeOnReady rate block C_star C_h i))

/-- The original fixed reward table and calendar index are retained when the
prepared arm maps are assembled into simultaneous play and derived feedback. -/
def actualJointPhysicalCodeOnReady {p : Parameters} (rate : RateInput p)
    (block : Fin (n_boot p)) (C_star C_h : ℝ)
    (x : ReadyInput p rate block C_star C_h) : JointPhysicalCode p :=
  ActualInitializationRoundMeasurability.jointPhysicalCodeFromComponents p
    x.1.rewards x.1.time (preparedCoordinatorArmOnReady rate block C_star C_h x)
    (fun i => preparedFollowerArmOnReady rate block C_star C_h i x)

theorem measurable_actualJointPhysicalCodeOnReady {p : Parameters}
    (rate : RateInput p) (block : Fin (n_boot p)) (C_star C_h : ℝ) :
    Measurable (actualJointPhysicalCodeOnReady rate block C_star C_h) := by
  have hcoe : Measurable (fun x : ReadyInput p rate block C_star C_h =>
      (x.1 : RoundInput p rate block C_star C_h)) := measurable_subtype_coe
  have hrewards := (measurable_roundInputRewards p rate block C_star C_h).comp hcoe
  have htime := (measurable_roundInputTime p rate block C_star C_h).comp hcoe
  have hfollowerArms : Measurable (fun x : ReadyInput p rate block C_star C_h =>
      fun i => preparedFollowerArmOnReady rate block C_star C_h i x) := by
    apply measurable_pi_iff.mpr
    intro i
    exact measurable_preparedFollowerArmOnReady rate block C_star C_h i
  exact (ActualInitializationRoundMeasurability.measurable_jointPhysicalCodeFromComponents
    p (fun x : ReadyInput p rate block C_star C_h => x.1.rewards)
      (fun x => x.1.time)
      (preparedCoordinatorArmOnReady rate block C_star C_h)
      (fun x i => preparedFollowerArmOnReady rate block C_star C_h i x)
      hrewards htime
      (measurable_preparedCoordinatorArmOnReady rate block C_star C_h)
      hfollowerArms)

/-! ## The full preparation result, including its invalid branch -/

/-- Code the exact existing `prepare` operation.  Its invalid-input branch is
the operation's `inputNotReady` error; no arm or default state is produced. -/
def actualPreparationCode {p : Parameters} (rate : RateInput p)
    (block : Fin (n_boot p)) (C_star C_h : ℝ)
    (x : RoundInput p rate block C_star C_h) :
    Unit ⊕ (PreparedRoundCode p rate block) := by
  classical
  by_cases hready : ActualInitializationRoundMeasurability.roundInputReady
      p rate block C_star C_h x
  · exact .inr (preparedRoundCodeOnReady rate block C_star C_h ⟨x, hready⟩)
  · exact .inl ()

/-- On the ready subtype the total code is exactly the successful joint
prepared code assembled from that same `RoundInput`. -/
theorem actualPreparationCode_eq_success_onReady {p : Parameters}
    (rate : RateInput p) (block : Fin (n_boot p)) (C_star C_h : ℝ)
    (x : ReadyInput p rate block C_star C_h) :
    actualPreparationCode rate block C_star C_h x.1 =
      .inr (preparedRoundCodeOnReady rate block C_star C_h x) := by
  simp [actualPreparationCode, x.2]

/-- Measurability of the total code follows from the proved ready set and the
prepared code on its induced ready subtype. -/
theorem measurable_actualPreparationCode {p : Parameters}
    (rate : RateInput p) (block : Fin (n_boot p)) (C_star C_h : ℝ) :
    Measurable (actualPreparationCode rate block C_star C_h) := by
  classical
  let readySet : Set (RoundInput p rate block C_star C_h) :=
    {x | ActualInitializationRoundMeasurability.roundInputReady
      p rate block C_star C_h x}
  have hreadySet : MeasurableSet readySet :=
    ActualInitializationRoundMeasurability.measurableSet_roundInputReady
      p rate block C_star C_h
  intro s hs
  let successfulCodes : Set (PreparedRoundCode p rate block) :=
    {code | Sum.inr code ∈ s}
  have hsuccessfulCodes : MeasurableSet successfulCodes := by
    change MeasurableSet ((Sum.inr : PreparedRoundCode p rate block →
      Unit ⊕ PreparedRoundCode p rate block) ⁻¹' s)
    exact hs.preimage measurable_inr
  have hreadyCode : Measurable
      (preparedRoundCodeOnReady rate block C_star C_h) :=
    measurable_preparedRoundCodeOnReady rate block C_star C_h
  have hsubtype : MeasurableSet
      (preparedRoundCodeOnReady rate block C_star C_h ⁻¹' successfulCodes) :=
    hreadyCode hsuccessfulCodes
  rw [MeasurableSpace.measurableSet_comap] at hsubtype
  rcases hsubtype with ⟨t, ht, hpreimage⟩
  have hpre :
      {x : RoundInput p rate block C_star C_h |
        actualPreparationCode rate block C_star C_h x ∈ s} =
        (if (Sum.inl () : Unit ⊕ PreparedRoundCode p rate block) ∈ s
          then readySetᶜ else ∅) ∪ (readySet ∩ t) := by
    ext x
    simp only [Set.mem_ofPred_eq]
    by_cases hready : ActualInitializationRoundMeasurability.roundInputReady
        p rate block C_star C_h x
    · have hsuccess :
          preparedRoundCodeOnReady rate block C_star C_h ⟨x, hready⟩ ∈ successfulCodes
            ↔ x ∈ t := by
        have hmembership := congrArg
          (fun q : Set (ReadyInput p rate block C_star C_h) =>
            (⟨x, hready⟩ : ReadyInput p rate block C_star C_h) ∈ q) hpreimage
        simpa [successfulCodes] using hmembership.symm
      simp only [actualPreparationCode, hready]
      simp [readySet, hready]
      change preparedRoundCodeOnReady rate block C_star C_h ⟨x, hready⟩ ∈
        successfulCodes ↔ x ∈ t
      exact hsuccess
    · simp [actualPreparationCode, hready, readySet]
  change MeasurableSet
    ({x : RoundInput p rate block C_star C_h |
      actualPreparationCode rate block C_star C_h x ∈ s} :
      Set (RoundInput p rate block C_star C_h))
  rw [hpre]
  have herr : MeasurableSet
      (if (Sum.inl () : Unit ⊕ PreparedRoundCode p rate block) ∈ s
        then readySetᶜ else ∅) := by
    by_cases he : (Sum.inl () : Unit ⊕ PreparedRoundCode p rate block) ∈ s
    · simp [he, hreadySet]
    · simp [he]
  exact herr.union (hreadySet.inter ht)

/-- The existing physical prepare operation is applied to the original
coordinator, heterogeneous followers, private source, and unchanged table. -/
def actualPrepareResult {p : Parameters} (rate : RateInput p)
    (block : Fin (n_boot p)) (C_star C_h : ℝ)
    (x : RoundInput p rate block C_star C_h) :=
  ActualInitializationPhysicalStep.prepare rate block x.time
    (ActualInitializationRoundMeasurability.coordinatorOfInput
      p rate block C_star C_h x)
    (ActualInitializationRoundMeasurability.followersOfInput p rate block x.followers)
    x.source x.rewards

/-- On the ready subtype, the literal physical preparation operation returns
its successful existing `PreparedRound`; readiness is the only premise. -/
theorem actualPrepareResult_exists_ok_onReady {p : Parameters}
    (rate : RateInput p) (block : Fin (n_boot p)) (C_star C_h : ℝ)
    (x : ReadyInput p rate block C_star C_h) :
    ∃ prepared : ActualInitializationPhysicalStep.PreparedRound p rate block,
      actualPrepareResult rate block C_star C_h x.1 = .ok prepared := by
  have hready : ActualInitializationPhysicalStep.ActualInputReady p rate block x.1.time
      (ActualInitializationRoundMeasurability.coordinatorOfInput
        p rate block C_star C_h x.1)
      (ActualInitializationRoundMeasurability.followersOfInput p rate block x.1.followers)
      x.1.source := by
    simpa [ActualInitializationRoundMeasurability.roundInputReady] using x.2
  rcases (ActualInitializationPhysicalStep.prepare_eq_ok_iff_ready rate block x.1.time
    (ActualInitializationRoundMeasurability.coordinatorOfInput
      p rate block C_star C_h x.1)
    (ActualInitializationRoundMeasurability.followersOfInput p rate block x.1.followers)
    x.1.source x.1.rewards).2 hready with ⟨prepared, hprepared⟩
  exact ⟨prepared, by simpa [actualPrepareResult] using hprepared⟩

theorem actualPreparationCode_eq_inputNotReady {p : Parameters}
    (rate : RateInput p) (block : Fin (n_boot p)) (C_star C_h : ℝ)
    (x : RoundInput p rate block C_star C_h)
    (hnotready : ¬ ActualInitializationRoundMeasurability.roundInputReady
      p rate block C_star C_h x) :
    actualPreparationCode rate block C_star C_h x = .inl () := by
  simp [actualPreparationCode, hnotready]

/-- The sole failure token in the preparation code decodes to the physical
operation's exact `inputNotReady` result. -/
def decodePreparationFailure {p : Parameters} (block : Fin (n_boot p))
    (_failure : Unit) : ActualInitializationPhysicalStep.InputFailure p block :=
  .inputNotReady

theorem decodePreparationFailure_eq_inputNotReady {p : Parameters}
    (block : Fin (n_boot p)) (failure : Unit) :
    decodePreparationFailure block failure = .inputNotReady := rfl

theorem actualPrepareResult_eq_inputNotReady {p : Parameters}
    (rate : RateInput p) (block : Fin (n_boot p)) (C_star C_h : ℝ)
    (x : RoundInput p rate block C_star C_h)
    (hnotready : ¬ ActualInitializationRoundMeasurability.roundInputReady
      p rate block C_star C_h x) :
    actualPrepareResult rate block C_star C_h x = .error .inputNotReady := by
  have hnotActual : ¬ ActualInitializationPhysicalStep.ActualInputReady p rate block
      x.time (ActualInitializationRoundMeasurability.coordinatorOfInput
        p rate block C_star C_h x)
      (ActualInitializationRoundMeasurability.followersOfInput p rate block x.followers)
      x.source := by
    simpa [ActualInitializationRoundMeasurability.roundInputReady] using hnotready
  simp [actualPrepareResult, ActualInitializationPhysicalStep.prepare, hnotActual]

/-! ## Complete physical preparation reconstruction -/

/-- The literal successful `PreparedRound` produced by the existing physical
`prepare`, assembled from the metadata and local operations of this same ready
round input. -/
noncomputable def actualPreparedRoundOnReady {p : Parameters}
    (rate : RateInput p) (block : Fin (n_boot p)) (C_star C_h : ℝ)
    (x : ReadyInput p rate block C_star C_h) :
    ActualInitializationPhysicalStep.PreparedRound p rate block := by
  let coordinator := ActualInitializationRoundMeasurability.coordinatorOfInput
    p rate block C_star C_h x.1
  let followers := ActualInitializationRoundMeasurability.followersOfInput
    p rate block x.1.followers
  have hready : ActualInitializationPhysicalStep.ActualInputReady p rate block
      x.1.time coordinator followers x.1.source := by
    simpa [ActualInitializationRoundMeasurability.roundInputReady,
      coordinator, followers] using x.2
  have hfields := (ActualInitializationRoundMeasurability.roundInputReady_iff_fields
    p rate block C_star C_h x.1).mp x.2
  have htime : x.1.time ∈ calendarBlock p block := hfields.2.1
  have htimeCoordinator : x.1.time ∈ calendarBlock p coordinator.data.block := by
    rw [hready.1]
    exact htime
  exact
    { time := x.1.time
      source := x.1.source
      rewards := x.1.rewards
      coordinatorInput := coordinator
      followerInputs := followers
      readiness := hready
      coordinator := BootstrapCoordinatorLocalRound.prepare p coordinator x.1.time
        htimeCoordinator
        (BootstrapPhysicalInput.playerRoundScalarAt p x.1.source.2
          (ActiveRoundActions.coordinator p.two_le_m) x.1.time)
      coordinator_eq := by rfl
      followers := fun i => ActualInitializationPhysicalStep.prepareFollowerValid
        rate block x.1.time x.1.source i (followers i)
        (readyFollowerCursorProof rate block C_star C_h i x)
      followers_eq := fun _ => rfl }

/-- The successful result is the exact computed `PreparedRound`, with its
source, reward table, readiness data and both operation equations retained. -/
theorem actualPrepareResult_eq_ok_actualPreparedRoundOnReady {p : Parameters}
    (rate : RateInput p) (block : Fin (n_boot p)) (C_star C_h : ℝ)
    (x : ReadyInput p rate block C_star C_h) :
    actualPrepareResult rate block C_star C_h x.1 =
      .ok (actualPreparedRoundOnReady rate block C_star C_h x) := by
  have hready : ActualInitializationPhysicalStep.ActualInputReady p rate block
      x.1.time
      (ActualInitializationRoundMeasurability.coordinatorOfInput
        p rate block C_star C_h x.1)
      (ActualInitializationRoundMeasurability.followersOfInput p rate block x.1.followers)
      x.1.source := by
    simpa [ActualInitializationRoundMeasurability.roundInputReady] using x.2
  simp [actualPrepareResult, ActualInitializationPhysicalStep.prepare, hready,
    actualPreparedRoundOnReady]

/-- Decode every follower component only when its existing local decoder
returns a value. The proof-indexed `Option.get` uses that computed value and
does not supply a physical fallback for malformed codes. -/
noncomputable def decodePreparedFollowerFamily {p : Parameters}
    (rate : RateInput p) (block : Fin (n_boot p))
    (C_star C_h : ℝ)
    (x : ReadyInput p rate block C_star C_h)
    (codes : Fin (p.m - 1) → PreparedFollowerCode p rate block) :
    Option (Fin (p.m - 1) → ActualInitializationPhysicalStep.PreparedFollower p rate block) := by
  classical
  let decoded := fun i => decodePreparedFollowerCode (rate := rate) (block := block)
    i x.1.source x.1.time (codes i)
  by_cases hdecoded : ∀ i, (decoded i).isSome
  · exact some (fun i => (decoded i).get (hdecoded i))
  · exact none

/-- On the generated follower family, pointwise exact local reconstruction
assembles into the exact family of `prepareFollowerValid` results. -/
theorem decodePreparedFollowerFamilyOnReady {p : Parameters}
    (rate : RateInput p) (block : Fin (n_boot p)) (C_star C_h : ℝ)
    (x : ReadyInput p rate block C_star C_h) :
    decodePreparedFollowerFamily rate block C_star C_h x
      (fun i => preparedFollowerCodeOnReady rate block C_star C_h i x) =
      some (fun i => ActualInitializationPhysicalStep.prepareFollowerValid rate block
        x.1.time x.1.source i
        (ActualInitializationRoundMeasurability.followerStateOfCode p rate block
          (x.1.followers i))
        (readyFollowerCursorProof rate block C_star C_h i x)) := by
  classical
  simp [decodePreparedFollowerFamily, decode_preparedFollowerCodeOnReady]

/-- A successful code is decoded relative to the original ready `RoundInput`.
The code's coordinator and every follower must reconstruct to the actual
prepared local operations; only then is the complete physical result returned.
All remaining fields are copied from that same input. -/
noncomputable def decodePreparedRoundCode {p : Parameters}
    (rate : RateInput p) (block : Fin (n_boot p)) (C_star C_h : ℝ)
    (x : ReadyInput p rate block C_star C_h)
    (code : PreparedRoundCode p rate block) :
    Option (ActualInitializationPhysicalStep.PreparedRound p rate block) := by
  classical
  let expected := actualPreparedRoundOnReady rate block C_star C_h x
  match BootstrapCoordinatorRoundMeasurability.reconstructPreparedRound p
      (coordinatorRoundInputOfReady rate block C_star C_h x) code.1 with
  | none => exact none
  | some coordinator =>
      match decodePreparedFollowerFamily rate block C_star C_h x code.2 with
      | none => exact none
      | some followers =>
          if hcoordinator : coordinator = expected.coordinator then
            if hfollowers : followers = expected.followers then
              exact some
                { time := x.1.time
                  source := x.1.source
                  rewards := x.1.rewards
                  coordinatorInput := expected.coordinatorInput
                  followerInputs := expected.followerInputs
                  readiness := expected.readiness
                  coordinator := coordinator
                  coordinator_eq := hcoordinator.trans expected.coordinator_eq
                  followers := followers
                  followers_eq := fun i => (congrFun hfollowers i).trans
                    (expected.followers_eq i) }
            else exact none
          else exact none

/-- The joint decoder consumes the accepted coordinator reconstruction and
all local follower reconstruction equations on the same ready input. -/
theorem decodePreparedRoundCodeOnReady {p : Parameters}
    (rate : RateInput p) (block : Fin (n_boot p)) (C_star C_h : ℝ)
    (x : ReadyInput p rate block C_star C_h) :
    decodePreparedRoundCode rate block C_star C_h x
      (preparedRoundCodeOnReady rate block C_star C_h x) =
      some (actualPreparedRoundOnReady rate block C_star C_h x) := by
  classical
  let expected := actualPreparedRoundOnReady rate block C_star C_h x
  have hcoordinator : BootstrapCoordinatorRoundMeasurability.coordinatorPreparedRound p
      (coordinatorRoundInputOfReady rate block C_star C_h x)
      (coordinatorOriginalRoundScalar rate block C_star C_h x) = expected.coordinator := by
    rw [coordinatorPreparedRoundOnReady_eq_physicalPrepare]
    rfl
  have hfollowers : (fun i => ActualInitializationPhysicalStep.prepareFollowerValid
      rate block x.1.time x.1.source i
      (ActualInitializationRoundMeasurability.followerStateOfCode p rate block
        (x.1.followers i))
      (readyFollowerCursorProof rate block C_star C_h i x)) = expected.followers := by
    funext i
    rfl
  simp [decodePreparedRoundCode, preparedRoundCodeOnReady, expected,
    reconstruct_preparedCoordinatorCodeOnReady,
    decodePreparedFollowerFamilyOnReady, hcoordinator, hfollowers]
  cases hcoordinator
  cases hfollowers
  rfl

/-- The exact `Except` result of physical preparation is recovered by
decoding the generated code, not merely by the existence of a successful
witness. -/
theorem actualPrepareResult_eq_decodedPreparedRoundOnReady {p : Parameters}
    (rate : RateInput p) (block : Fin (n_boot p)) (C_star C_h : ℝ)
    (x : ReadyInput p rate block C_star C_h) :
    actualPrepareResult rate block C_star C_h x.1 =
      .ok ((decodePreparedRoundCode rate block C_star C_h x
        (preparedRoundCodeOnReady rate block C_star C_h x)).get (by
          rw [decodePreparedRoundCodeOnReady]
          simp)) := by
  simpa [decodePreparedRoundCodeOnReady] using
    actualPrepareResult_eq_ok_actualPreparedRoundOnReady rate block C_star C_h x

/-- The coordinator code arm is the arm of the coordinator value obtained
from the accepted coordinator decoder. -/
private theorem coordinatorCodeArm_eq_of_reconstruction {p : Parameters}
    (input : BootstrapCoordinatorRoundMeasurability.CoordinatorRoundInput p)
    (code : BootstrapCoordinatorRoundMeasurability.PreparedRoundCode p)
    (prepared : BootstrapCoordinatorLocalRound.PreparedRound p)
    (hreconstruct : BootstrapCoordinatorRoundMeasurability.reconstructPreparedRound
      p input code = some prepared) :
    code.2.2 = prepared.arm := by
  unfold BootstrapCoordinatorRoundMeasurability.reconstructPreparedRound at hreconstruct
  split_ifs at hreconstruct with hlocal hround
  · cases hreconstruct
    rfl

/-- The coordinator arm projection therefore matches the actual successful
physical preparation on this ready input. -/
theorem preparedCoordinatorArmOnReady_eq_actualPreparedRoundOnReady {p : Parameters}
    (rate : RateInput p) (block : Fin (n_boot p)) (C_star C_h : ℝ)
    (x : ReadyInput p rate block C_star C_h) :
    preparedCoordinatorArmOnReady rate block C_star C_h x =
      (actualPreparedRoundOnReady rate block C_star C_h x).coordinator.arm := by
  have hdecode := reconstruct_preparedCoordinatorCodeOnReady rate block C_star C_h x
  have hcodeArm := coordinatorCodeArm_eq_of_reconstruction
    (coordinatorRoundInputOfReady rate block C_star C_h x)
    (preparedCoordinatorCodeOnReady rate block C_star C_h x)
    (BootstrapCoordinatorRoundMeasurability.coordinatorPreparedRound p
      (coordinatorRoundInputOfReady rate block C_star C_h x)
      (coordinatorOriginalRoundScalar rate block C_star C_h x)) hdecode
  calc
    preparedCoordinatorArmOnReady rate block C_star C_h x =
        (preparedCoordinatorCodeOnReady rate block C_star C_h x).2.2 := rfl
    _ = (BootstrapCoordinatorRoundMeasurability.coordinatorPreparedRound p
        (coordinatorRoundInputOfReady rate block C_star C_h x)
        (coordinatorOriginalRoundScalar rate block C_star C_h x)).arm := hcodeArm
    _ = (actualPreparedRoundOnReady rate block C_star C_h x).coordinator.arm := by
      rw [coordinatorPreparedRoundOnReady_eq_physicalPrepare]
      rfl

/-- A follower code's arm is the arm of its actual local decoder result. -/
private theorem preparedFollowerCodeArm_eq_of_decode {p : Parameters}
    (rate : RateInput p) {block : Fin (n_boot p)}
    (i : Fin (p.m - 1)) (source : ActualBootstrapObservationCode.ActualSource p)
    (time : Fin p.T) (code : PreparedFollowerCode p rate block)
    (prepared : ActualInitializationPhysicalStep.PreparedFollower p rate block)
    (hdecode : decodePreparedFollowerCode (rate := rate) (block := block)
      i source time code = some prepared) :
    preparedFollowerCodeArm code = prepared.arm := by
  cases code with
  | inl fields =>
      rcases fields with ⟨state, arm⟩
      simp [decodePreparedFollowerCode] at hdecode
      cases hdecode
      rfl
  | inr fields =>
      rcases fields with ⟨rowIndex, activation, arm, incoming⟩
      by_cases hvalid : activation.val ≤ time.val + 1
      · simp [decodePreparedFollowerCode, hvalid] at hdecode
        cases hdecode
        rfl
      · simp [decodePreparedFollowerCode, hvalid] at hdecode

/-- Each follower's prepared arm equals the arm reconstructed from its own
code and the same original source and time. -/
theorem preparedFollowerArmOnReady_eq_actualPreparedRoundOnReady {p : Parameters}
    (rate : RateInput p) (block : Fin (n_boot p)) (C_star C_h : ℝ)
    (i : Fin (p.m - 1)) (x : ReadyInput p rate block C_star C_h) :
    preparedFollowerArmOnReady rate block C_star C_h i x =
      ((actualPreparedRoundOnReady rate block C_star C_h x).followers i).arm := by
  have hdecode := decode_preparedFollowerCodeOnReady rate block C_star C_h i x
  have hcodeArm := preparedFollowerCodeArm_eq_of_decode rate i x.1.source x.1.time
    (preparedFollowerCodeOnReady rate block C_star C_h i x)
    (ActualInitializationPhysicalStep.prepareFollowerValid rate block x.1.time
      x.1.source i
      (ActualInitializationRoundMeasurability.followerStateOfCode p rate block
        (x.1.followers i))
      (readyFollowerCursorProof rate block C_star C_h i x)) hdecode
  calc
    preparedFollowerArmOnReady rate block C_star C_h i x =
        preparedFollowerCodeArm
          (preparedFollowerCodeOnReady rate block C_star C_h i x) := rfl
    _ = (ActualInitializationPhysicalStep.prepareFollowerValid rate block x.1.time
          x.1.source i
          (ActualInitializationRoundMeasurability.followerStateOfCode p rate block
            (x.1.followers i))
          (readyFollowerCursorProof rate block C_star C_h i x)).arm := hcodeArm
    _ = ((actualPreparedRoundOnReady rate block C_star C_h x).followers i).arm := rfl

/-- The joint action and derived-feedback code is exactly the physical output
of the same successful `prepare` result. The arm identities are discharged
from the coordinator and per-follower code reconstructions above. -/
theorem actualJointPhysicalCodeOnReady_eq_actualPreparedRoundOnReady {p : Parameters}
    (rate : RateInput p) (block : Fin (n_boot p)) (C_star C_h : ℝ)
    (x : ReadyInput p rate block C_star C_h) :
    actualJointPhysicalCodeOnReady rate block C_star C_h x =
      (ActualInitializationPhysicalStep.actionProfile
          (actualPreparedRoundOnReady rate block C_star C_h x),
        ActualInitializationPhysicalStep.physicalFeedback
          (actualPreparedRoundOnReady rate block C_star C_h x)) := by
  have hfollowers : (fun i => preparedFollowerArmOnReady rate block C_star C_h i x) =
      (fun i => ((actualPreparedRoundOnReady rate block C_star C_h x).followers i).arm) := by
    funext i
    exact preparedFollowerArmOnReady_eq_actualPreparedRoundOnReady
      rate block C_star C_h i x
  rw [actualJointPhysicalCodeOnReady,
    preparedCoordinatorArmOnReady_eq_actualPreparedRoundOnReady rate block C_star C_h x,
    hfollowers]
  exact ActualInitializationRoundMeasurability.jointPhysicalCodeFromPrepared_reconstructs
    p rate block (actualPreparedRoundOnReady rate block C_star C_h x)

/-- Both the full successful result and its simultaneous action/feedback
output are tied to one and the same reconstructed physical `PreparedRound`. -/
theorem actualPrepareResult_and_jointPhysicalCodeOnReady {p : Parameters}
    (rate : RateInput p) (block : Fin (n_boot p)) (C_star C_h : ℝ)
    (x : ReadyInput p rate block C_star C_h) :
    actualPrepareResult rate block C_star C_h x.1 =
        .ok (actualPreparedRoundOnReady rate block C_star C_h x) ∧
      actualJointPhysicalCodeOnReady rate block C_star C_h x =
        (ActualInitializationPhysicalStep.actionProfile
            (actualPreparedRoundOnReady rate block C_star C_h x),
          ActualInitializationPhysicalStep.physicalFeedback
            (actualPreparedRoundOnReady rate block C_star C_h x)) :=
  ⟨actualPrepareResult_eq_ok_actualPreparedRoundOnReady rate block C_star C_h x,
    actualJointPhysicalCodeOnReady_eq_actualPreparedRoundOnReady
      rate block C_star C_h x⟩

end Bandits.Support.ActualInitializationPreparationMeasurability

end
