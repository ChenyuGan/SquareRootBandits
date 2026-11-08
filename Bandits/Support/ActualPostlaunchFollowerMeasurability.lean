/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ActualPostlaunchPhysicalStep
public import Bandits.Support.ActualInitializationStepMeasurability

/-!
# Actual postlaunch follower-local measurability

This module produces the exact preparation, own-observation, and successor
codes for one heterogeneous follower at a fixed actual clipped-block cursor.
The input is the original source, that follower's existing cursor-restricted
state, and an independently supplied typed grid observation. It does not
construct a simultaneous arm profile or physical feedback.

Mathematical evidence: `sources/zip4/manuscript/07_public_setup.tex:55-114`,
`sources/zip4/manuscript/06_interruptions.tex:240-296`,
`sources/zip4/manuscript/appendix_a_local_protocol.tex:6-14`,
`sources/zip4/manuscript/appendix_b_communication.tex:94-131`, and
`sources/zip4/manuscript/08_main_theorem.tex:67-75`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.BootstrapObservedFollower
open Bandits.Support.CompletePublicTable
open Bandits.Support.PublicDiscreteDraws
open Bandits.Support.ActualInitializationPhysicalStep
open Bandits.Support.ActualInitializationRun
open Bandits.Support.ActualInitializationRoundMeasurability
open Bandits.Support.ActualInitializationPreparationMeasurability
open Bandits.Support.ActualBootstrapObservationCode
open Bandits.Support.FollowerVaryingActivationMeasurability
open Bandits.Support.DeclaredFollowerObservationMeasurability
open Bandits.Support.ActualInitializationStepMeasurability

namespace Bandits.Support.ActualPostlaunchFollowerMeasurability

abbrev Parameters := ActualPostlaunchPhysicalStep.Parameters
abbrev RateInput := ActualPostlaunchPhysicalStep.RateInput
abbrev SourceInput (p : Parameters) := ActualPostlaunchPhysicalStep.SourceInput p
abbrev FollowerState (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) :=
  ActualInitializationPhysicalStep.FollowerState p rate block
abbrev PreparedFollowerCode (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) :=
  ActualInitializationPreparationMeasurability.PreparedFollowerCode p rate block
abbrev FollowerObservationCode (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) :=
  ActualInitializationStepMeasurability.FollowerObservationCode p rate block
abbrev FollowerSuccessorCode (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) :=
  ActualInitializationPreparationMeasurability.FollowerCode p rate block

variable {p : Parameters} {rate : RateInput p}
  {block : Fin (n_boot p)} {cursor : Nat}

/-- The existing follower state restricted only by its real within-block
cursor invariant. -/
abbrev CursorFollowerInput (block : Fin (n_boot p)) (cursor : Nat) :=
  {follower : FollowerState p rate block //
    ActualInitializationRun.followerAtCursor p rate block cursor follower}

/-- The local input keeps the original source, one existing cursor-restricted
follower, and that follower's own finite-grid observation. -/
abbrev LocalInput (block : Fin (n_boot p)) (cursor : Nat) :=
  SourceInput p × (CursorFollowerInput (rate := rate) block cursor × Fin (D p + 1))

/-- Assemble the same local input from separately supplied source, typed
follower, cursor proof, and own finite-grid observation. -/
def localInputOfComponents {block : Fin (n_boot p)} {cursor : Nat}
    (source : SourceInput p) (follower : FollowerState p rate block)
    (hstate : ActualInitializationRun.followerAtCursor p rate block cursor follower)
    (ownY : Fin (D p + 1)) : LocalInput (rate := rate) block cursor :=
  (source, (⟨follower, hstate⟩, ownY))

/-- One code retains preparation, the exact observation code, and the
successor's existing follower-state code. -/
abbrev LocalCode (block : Fin (n_boot p)) :=
  PreparedFollowerCode p rate block ×
    (FollowerObservationCode p rate block × FollowerSuccessorCode p rate block)

/-- The actual calendar time determined by the fixed clipped-block cursor. -/
def localTime (block : Fin (n_boot p)) (cursor : Nat)
    (hcursor : cursor < BootstrapObservedFollower.blockLength p block) : Fin p.T :=
  ActualInitializationRun.blockTime p block cursor hcursor

/-- The cursor restriction implies the existing next-cursor premise required
by the actual follower preparation. -/
theorem follower_ready_of_cursor {block : Fin (n_boot p)} {cursor : Nat}
    (hcursor : cursor < BootstrapObservedFollower.blockLength p block)
    (x : CursorFollowerInput (rate := rate) block cursor) :
    ActualInitializationPhysicalStep.followerAtNextCursor
      (localTime block cursor hcursor) x.1 := by
  cases hf : x.1 with
  | bootstrap startup =>
      have hstate := x.2
      simp only [ActualInitializationRun.followerAtCursor, hf] at hstate
      change localTime block cursor hcursor ∈ BootstrapDimensions.calendarBlock p block ∧
        startup.processed.val < BootstrapObservedFollower.blockLength p block ∧
        (localTime block cursor hcursor).val =
          BootstrapObservedFollower.blockStart p block + startup.processed.val
      refine ⟨ActualInitializationRun.blockTime_mem p block cursor hcursor, ?_, ?_⟩
      · rw [hstate]
        exact hcursor
      · simp [localTime, ActualInitializationRun.blockTime, hstate]
  | declared row activation configuration =>
      have hstate := x.2
      simp only [ActualInitializationRun.followerAtCursor, hf] at hstate
      change activation.val ≤ (localTime block cursor hcursor).val + 1
      simpa [localTime, ActualInitializationRun.blockTime] using hstate

def localSource {block : Fin (n_boot p)} {cursor : Nat}
    (x : LocalInput (rate := rate) block cursor) : SourceInput p := x.1

def localFollower {block : Fin (n_boot p)} {cursor : Nat}
    (x : LocalInput (rate := rate) block cursor) : FollowerState p rate block := x.2.1.1

def localFeedback {block : Fin (n_boot p)} {cursor : Nat}
    (x : LocalInput (rate := rate) block cursor) : Fin (D p + 1) := x.2.2

theorem measurable_localSource {block : Fin (n_boot p)} {cursor : Nat} :
    Measurable (localSource (rate := rate) (block := block) (cursor := cursor)) :=
  measurable_fst

theorem measurable_localFollower {block : Fin (n_boot p)} {cursor : Nat} :
    Measurable (localFollower (rate := rate) (block := block) (cursor := cursor)) :=
  measurable_subtype_coe.comp (measurable_fst.comp measurable_snd)

theorem measurable_localFeedback {block : Fin (n_boot p)} {cursor : Nat} :
    Measurable (localFeedback (rate := rate) (block := block) (cursor := cursor)) :=
  measurable_snd.comp measurable_snd

/-- The already admitted lossless follower coordinate code on this local
input. -/
def localFollowerStateCode {block : Fin (n_boot p)} {cursor : Nat}
    (x : LocalInput (rate := rate) block cursor) :
    ActualInitializationRoundMeasurability.FollowerCode p rate block :=
  ActualInitializationRoundMeasurability.followerCodeOfState p rate block
    (localFollower (rate := rate) x)

theorem measurable_localFollowerStateCode {block : Fin (n_boot p)} {cursor : Nat} :
    Measurable (localFollowerStateCode (rate := rate) (block := block) (cursor := cursor)) :=
  (ActualInitializationRoundMeasurability.measurable_followerCodeOfState p rate block).comp
    measurable_localFollower

def bootstrapLocalSet {block : Fin (n_boot p)} {cursor : Nat}
    : Set (LocalInput (rate := rate) block cursor) :=
  {x | localFollowerStateCode (rate := rate) x ∈ Set.range Sum.inl}

theorem measurableSet_bootstrapLocalSet {block : Fin (n_boot p)} {cursor : Nat} :
    MeasurableSet (bootstrapLocalSet (rate := rate) (block := block) (cursor := cursor)) := by
  exact (measurableSet_range_inl : MeasurableSet
    (Set.range (Sum.inl :
      ActualBootstrapObservationCode.StartupCode p block →
        ActualInitializationRoundMeasurability.FollowerCode p rate block))).preimage
    measurable_localFollowerStateCode

def startupCodeOnBootstrap {block : Fin (n_boot p)} {cursor : Nat}
    (x : bootstrapLocalSet (rate := rate) (block := block) (cursor := cursor)) :
    ActualBootstrapObservationCode.StartupCode p block :=
  Equiv.Set.rangeInl
    (ActualBootstrapObservationCode.StartupCode p block)
    (ActualInitializationPreparationMeasurability.DeclaredInputCode p rate)
    ⟨localFollowerStateCode (rate := rate) x.1, x.2⟩

theorem measurable_startupCodeOnBootstrap {block : Fin (n_boot p)} {cursor : Nat} :
    Measurable (startupCodeOnBootstrap (rate := rate) (block := block)
      (cursor := cursor)) := by
  have hcode := measurable_localFollowerStateCode (rate := rate) (block := block)
    (cursor := cursor)
  have hrange : Measurable
      (fun x : bootstrapLocalSet (rate := rate) (block := block) (cursor := cursor) =>
        (⟨localFollowerStateCode (rate := rate) x.1, x.2⟩ : Set.range Sum.inl)) := by
    exact (hcode.comp measurable_subtype_coe).subtype_mk
  exact MeasurableEquiv.Set.rangeInl.measurable_toFun.comp hrange

abbrev DeclaredCode (p : Parameters) (rate : RateInput p) :=
  ActualInitializationPreparationMeasurability.DeclaredInputCode p rate

def declaredCodeOnBootstrapComplement {block : Fin (n_boot p)} {cursor : Nat}
    (x : ↥((bootstrapLocalSet (rate := rate) (block := block) (cursor := cursor))ᶜ)) :
    DeclaredCode p rate := by
  have hmem : localFollowerStateCode (rate := rate) x.1 ∈ Set.range Sum.inr := by
    cases hcode : localFollowerStateCode (rate := rate) x.1 with
    | inl startup => exact (x.2 ⟨startup, hcode.symm⟩).elim
    | inr fields => exact ⟨fields, rfl⟩
  exact Equiv.Set.rangeInr _ _ ⟨localFollowerStateCode (rate := rate) x.1, hmem⟩

theorem followerStateCode_eq_inr_on_bootstrap_complement
    {block : Fin (n_boot p)} {cursor : Nat}
    (x : ↥((bootstrapLocalSet (rate := rate) (block := block) (cursor := cursor))ᶜ)) :
    localFollowerStateCode (rate := rate) x.1 =
      Sum.inr (declaredCodeOnBootstrapComplement (rate := rate) x) := by
  cases hcode : localFollowerStateCode (rate := rate) x.1 with
  | inl startup => exact (x.2 ⟨startup, hcode.symm⟩).elim
  | inr fields =>
      have hfields : declaredCodeOnBootstrapComplement (rate := rate) x = fields := by
        simp [declaredCodeOnBootstrapComplement, hcode]
      exact congrArg Sum.inr hfields.symm

theorem measurable_declaredCodeOnBootstrapComplement
    {block : Fin (n_boot p)} {cursor : Nat} :
    Measurable (declaredCodeOnBootstrapComplement (rate := rate) (block := block)
      (cursor := cursor)) := by
  have hcode := measurable_localFollowerStateCode (rate := rate) (block := block)
    (cursor := cursor)
  have hmem (x : ↥((bootstrapLocalSet (rate := rate) (block := block)
      (cursor := cursor))ᶜ)) :
      localFollowerStateCode (rate := rate) x.1 ∈ Set.range Sum.inr := by
    cases hvalue : localFollowerStateCode (rate := rate) x.1 with
    | inl startup => exact (x.2 ⟨startup, hvalue.symm⟩).elim
    | inr fields => exact ⟨fields, rfl⟩
  have hrange : Measurable
      (fun x : ↥((bootstrapLocalSet (rate := rate) (block := block)
          (cursor := cursor))ᶜ) =>
        (⟨localFollowerStateCode (rate := rate) x.1, hmem x⟩ : Set.range Sum.inr)) := by
    exact (hcode.comp measurable_subtype_coe).subtype_mk
  exact MeasurableEquiv.Set.rangeInr.measurable_toFun.comp hrange

theorem measurable_evalCompleteRows_local (p : Parameters) :
    Measurable (fun z : CompleteRows p × Fin (M p) => z.1 z.2) := by
  apply measurable_from_prod_countable_left
  intro rowIndex
  exact measurable_pi_apply rowIndex

def preparedCodeOnBootstrap {block : Fin (n_boot p)} {cursor : Nat}
    (hcursor : cursor < BootstrapObservedFollower.blockLength p block)
    (i : Fin (p.m - 1))
    (x : bootstrapLocalSet (rate := rate) (block := block) (cursor := cursor)) :
    PreparedFollowerCode p rate block := by
  let startup := startupCodeOnBootstrap (rate := rate) x
  let source := localSource (rate := rate) x.1
  let ids := ActualBootstrapObservationCode.sourceIDs p source
  let time := localTime block cursor hcursor
  let scalar := BootstrapPhysicalInput.playerRoundScalarAt p
    (ActualBootstrapObservationCode.sourcePrivate p source)
    (PublicDiscreteDraws.followerPlayer p.two_le_m i) time
  exact Sum.inl (startup,
    ActualInitializationPreparationMeasurability.bootstrapLocalArmFromComponents block
      (startup, (ids, (time, scalar))))

theorem measurable_preparedCodeOnBootstrap {block : Fin (n_boot p)} {cursor : Nat}
    (hcursor : cursor < BootstrapObservedFollower.blockLength p block)
    (i : Fin (p.m - 1)) :
    Measurable (preparedCodeOnBootstrap (rate := rate) (block := block)
      (cursor := cursor) hcursor i) := by
  have hstartup := measurable_startupCodeOnBootstrap (rate := rate)
    (block := block) (cursor := cursor)
  have hsource : Measurable
      (fun x : bootstrapLocalSet (rate := rate) (block := block) (cursor := cursor) =>
        localSource (rate := rate) x.1) :=
    measurable_localSource.comp measurable_subtype_coe
  have hids := (ActualBootstrapObservationCode.measurable_sourceIDs p).comp hsource
  have hprivate := (ActualBootstrapObservationCode.measurable_sourcePrivate p).comp hsource
  have htime : Measurable (fun _ : bootstrapLocalSet (rate := rate)
      (block := block) (cursor := cursor) => localTime block cursor hcursor) :=
    measurable_const
  have hscalar : Measurable (fun x : bootstrapLocalSet (rate := rate)
      (block := block) (cursor := cursor) =>
        BootstrapPhysicalInput.playerRoundScalarAt p
          (ActualBootstrapObservationCode.sourcePrivate p
            (localSource (rate := rate) x.1))
          (PublicDiscreteDraws.followerPlayer p.two_le_m i)
          (localTime block cursor hcursor)) := by
    exact (BootstrapPhysicalInput.measurable_playerRoundScalarAt p
      (PublicDiscreteDraws.followerPlayer p.two_le_m i) (localTime block cursor hcursor)).comp
        hprivate
  have harm : Measurable (fun x : bootstrapLocalSet (rate := rate)
      (block := block) (cursor := cursor) =>
        ActualInitializationPreparationMeasurability.bootstrapLocalArmFromComponents block
          (startupCodeOnBootstrap (rate := rate) x,
            (ActualBootstrapObservationCode.sourceIDs p
              (localSource (rate := rate) x.1),
              (localTime block cursor hcursor,
                BootstrapPhysicalInput.playerRoundScalarAt p
                  (ActualBootstrapObservationCode.sourcePrivate p
                    (localSource (rate := rate) x.1))
                  (PublicDiscreteDraws.followerPlayer p.two_le_m i)
                  (localTime block cursor hcursor))))) := by
    exact (ActualInitializationPreparationMeasurability.measurable_bootstrapLocalArmFromComponents
      block).comp (hstartup.prodMk (hids.prodMk (htime.prodMk hscalar)))
  change Measurable (fun x : bootstrapLocalSet (rate := rate)
      (block := block) (cursor := cursor) =>
        Sum.inl (startupCodeOnBootstrap (rate := rate) x,
          ActualInitializationPreparationMeasurability.bootstrapLocalArmFromComponents block
            (startupCodeOnBootstrap (rate := rate) x,
              (ActualBootstrapObservationCode.sourceIDs p
                (localSource (rate := rate) x.1),
                (localTime block cursor hcursor,
                  BootstrapPhysicalInput.playerRoundScalarAt p
                    (ActualBootstrapObservationCode.sourcePrivate p
                      (localSource (rate := rate) x.1))
                    (PublicDiscreteDraws.followerPlayer p.two_le_m i)
                    (localTime block cursor hcursor))))))
  exact measurable_inl.comp (hstartup.prodMk harm)

theorem declaredActivation_le_time_of_code {block : Fin (n_boot p)}
    {cursor : Nat} (hcursor : cursor < BootstrapObservedFollower.blockLength p block)
    (x : LocalInput (rate := rate) block cursor) (fields : DeclaredCode p rate)
    (hcode : localFollowerStateCode (rate := rate) x = Sum.inr fields) :
    fields.2.1.val ≤ (localTime block cursor hcursor).val + 1 := by
  cases hfollower : x.2.1.1 with
  | bootstrap startup =>
      have hfalse := hcode
      simp [localFollowerStateCode, localFollower,
        ActualInitializationRoundMeasurability.followerCodeOfState, hfollower] at hfalse
  | declared row activation configuration =>
      have hfields : (row, (activation,
          FollowerPrepareJointMeasurability.incomingOfLocalConfiguration rate configuration)) =
          fields := by
        have hcode' : Sum.inr (α := ActualBootstrapObservationCode.StartupCode p block)
            (row, (activation,
            FollowerPrepareJointMeasurability.incomingOfLocalConfiguration rate configuration)) =
            Sum.inr (α := ActualBootstrapObservationCode.StartupCode p block) fields := by
          simpa [localFollowerStateCode, localFollower,
            ActualInitializationRoundMeasurability.followerCodeOfState, hfollower] using hcode
        exact Sum.inr.inj hcode'
      have hactivation : activation = fields.2.1 :=
        congrArg (fun z : DeclaredCode p rate => z.2.1) hfields
      have hstate : activation.val ≤
          BootstrapObservedFollower.blockStart p block + cursor + 1 := by
        simpa [ActualInitializationRun.followerAtCursor, hfollower] using x.2.1.2
      rw [← hactivation]
      change activation.val ≤ BootstrapObservedFollower.blockStart p block + cursor + 1
      simpa [localTime, ActualInitializationRun.blockTime] using hstate

def preparedCodeOnDeclared {block : Fin (n_boot p)} {cursor : Nat}
    (hcursor : cursor < BootstrapObservedFollower.blockLength p block)
    (i : Fin (p.m - 1))
    (x : ↥((bootstrapLocalSet (rate := rate) (block := block) (cursor := cursor))ᶜ)) :
    PreparedFollowerCode p rate block := by
  let fields := declaredCodeOnBootstrapComplement (rate := rate) x
  let source := localSource (rate := rate) x.1
  let row := ActualBootstrapObservationCode.sourceRows p source fields.1
  let time := localTime block cursor hcursor
  have hvalid := declaredActivation_le_time_of_code (rate := rate) hcursor x.1 fields
    (followerStateCode_eq_inr_on_bootstrap_complement (rate := rate) x)
  let output := FollowerVaryingActivationMeasurability.varyingPreparedOutput rate i
    (FollowerVaryingActivationMeasurability.assembleVaryingPrepareInput
      fields.2.1 fields.2.2 row time hvalid)
  exact Sum.inr (fields.1, (fields.2.1, (output.2.2.1, output.2.2.2)))

theorem measurable_preparedCodeOnDeclared {block : Fin (n_boot p)}
    {cursor : Nat} (hcursor : cursor < BootstrapObservedFollower.blockLength p block)
    (i : Fin (p.m - 1)) :
    Measurable (preparedCodeOnDeclared (rate := rate) (block := block)
      (cursor := cursor) hcursor i) := by
  let fields := declaredCodeOnBootstrapComplement (rate := rate)
    (block := block) (cursor := cursor)
  have hfields := measurable_declaredCodeOnBootstrapComplement (rate := rate)
    (block := block) (cursor := cursor)
  have hrowIndex : Measurable (fun x : ↥((bootstrapLocalSet (rate := rate)
      (block := block) (cursor := cursor))ᶜ) => (fields x).1) :=
    measurable_fst.comp hfields
  have hactivation : Measurable (fun x : ↥((bootstrapLocalSet (rate := rate)
      (block := block) (cursor := cursor))ᶜ) => (fields x).2.1) :=
    measurable_fst.comp (measurable_snd.comp hfields)
  have hincoming : Measurable (fun x : ↥((bootstrapLocalSet (rate := rate)
      (block := block) (cursor := cursor))ᶜ) => (fields x).2.2) :=
    measurable_snd.comp (measurable_snd.comp hfields)
  have hsource : Measurable
      (fun x : ↥((bootstrapLocalSet (rate := rate) (block := block)
          (cursor := cursor))ᶜ) => localSource (rate := rate) x.1) :=
    measurable_localSource.comp measurable_subtype_coe
  have hrows := (ActualBootstrapObservationCode.measurable_sourceRows p).comp hsource
  have hrow : Measurable (fun x : ↥((bootstrapLocalSet (rate := rate)
      (block := block) (cursor := cursor))ᶜ) =>
        ActualBootstrapObservationCode.sourceRows p (localSource (rate := rate) x.1)
          (fields x).1) := by
    exact (measurable_evalCompleteRows_local p).comp (hrows.prodMk hrowIndex)
  have htime : Measurable (fun _ : ↥((bootstrapLocalSet (rate := rate)
      (block := block) (cursor := cursor))ᶜ) => localTime block cursor hcursor) :=
    measurable_const
  have hvalid (x : ↥((bootstrapLocalSet (rate := rate)
      (block := block) (cursor := cursor))ᶜ)) :
      (fields x).2.1.val ≤ (localTime block cursor hcursor).val + 1 :=
    declaredActivation_le_time_of_code (rate := rate) hcursor x.1 (fields x)
      (followerStateCode_eq_inr_on_bootstrap_complement (rate := rate) x)
  have houtput : Measurable (fun x : ↥((bootstrapLocalSet (rate := rate)
      (block := block) (cursor := cursor))ᶜ) =>
        FollowerVaryingActivationMeasurability.varyingPreparedOutput rate i
          (FollowerVaryingActivationMeasurability.assembleVaryingPrepareInput
            (fields x).2.1 (fields x).2.2
            (ActualBootstrapObservationCode.sourceRows p
              (localSource (rate := rate) x.1) (fields x).1)
            (localTime block cursor hcursor) (hvalid x))) := by
    exact (FollowerVaryingActivationMeasurability.measurable_varyingPreparedOutput_atComponents
      rate i (fun x => (fields x).2.1) (fun x => (fields x).2.2)
      (fun x => ActualBootstrapObservationCode.sourceRows p
        (localSource (rate := rate) x.1) (fields x).1)
      (fun _ => localTime block cursor hcursor)
      hactivation hincoming hrow htime hvalid)
  have harm : Measurable (fun x : ↥((bootstrapLocalSet (rate := rate)
      (block := block) (cursor := cursor))ᶜ) =>
        (FollowerVaryingActivationMeasurability.varyingPreparedOutput rate i
          (FollowerVaryingActivationMeasurability.assembleVaryingPrepareInput
            (fields x).2.1 (fields x).2.2
            (ActualBootstrapObservationCode.sourceRows p
              (localSource (rate := rate) x.1) (fields x).1)
            (localTime block cursor hcursor) (hvalid x))).2.2.1) :=
    by
      simpa [FollowerVaryingActivationMeasurability.varyingPreparedOutput,
        FollowerVaryingActivationMeasurability.varyingPreparedArm] using
        FollowerVaryingActivationMeasurability.measurable_varyingPreparedArm_atComponents
          rate i (fun x => (fields x).2.1) (fun x => (fields x).2.2)
          (fun x => ActualBootstrapObservationCode.sourceRows p
            (localSource (rate := rate) x.1) (fields x).1)
          (fun _ => localTime block cursor hcursor)
          hactivation hincoming hrow htime hvalid
  have hincomingOutput : Measurable (fun x : ↥((bootstrapLocalSet (rate := rate)
      (block := block) (cursor := cursor))ᶜ) =>
        (FollowerVaryingActivationMeasurability.varyingPreparedOutput rate i
          (FollowerVaryingActivationMeasurability.assembleVaryingPrepareInput
            (fields x).2.1 (fields x).2.2
            (ActualBootstrapObservationCode.sourceRows p
              (localSource (rate := rate) x.1) (fields x).1)
            (localTime block cursor hcursor) (hvalid x))).2.2.2) :=
    by
      simpa [FollowerVaryingActivationMeasurability.varyingPreparedOutput,
        FollowerVaryingActivationMeasurability.varyingPreparedConfiguration] using
        FollowerVaryingActivationMeasurability.measurable_varyingPreparedConfiguration_atComponents
          rate i (fun x => (fields x).2.1) (fun x => (fields x).2.2)
          (fun x => ActualBootstrapObservationCode.sourceRows p
            (localSource (rate := rate) x.1) (fields x).1)
          (fun _ => localTime block cursor hcursor)
          hactivation hincoming hrow htime hvalid
  change Measurable (fun x : ↥((bootstrapLocalSet (rate := rate)
      (block := block) (cursor := cursor))ᶜ) =>
    Sum.inr ((fields x).1, ((fields x).2.1, (
      (FollowerVaryingActivationMeasurability.varyingPreparedOutput rate i
        (FollowerVaryingActivationMeasurability.assembleVaryingPrepareInput
          (fields x).2.1 (fields x).2.2
          (ActualBootstrapObservationCode.sourceRows p
            (localSource (rate := rate) x.1) (fields x).1)
          (localTime block cursor hcursor) (hvalid x))).2.2.1,
      (FollowerVaryingActivationMeasurability.varyingPreparedOutput rate i
        (FollowerVaryingActivationMeasurability.assembleVaryingPrepareInput
          (fields x).2.1 (fields x).2.2
          (ActualBootstrapObservationCode.sourceRows p
            (localSource (rate := rate) x.1) (fields x).1)
          (localTime block cursor hcursor) (hvalid x))).2.2.2))))
  exact measurable_inr.comp (hrowIndex.prodMk (hactivation.prodMk (harm.prodMk hincomingOutput)))

/-- The exact measurable prepared code on the fixed-cursor follower input. -/
def preparedCodeOnCursor {block : Fin (n_boot p)} {cursor : Nat}
    (hcursor : cursor < BootstrapObservedFollower.blockLength p block)
    (i : Fin (p.m - 1)) (x : LocalInput (rate := rate) block cursor) :
    PreparedFollowerCode p rate block := by
  classical
  exact if hx : x ∈ bootstrapLocalSet (rate := rate) then
    preparedCodeOnBootstrap (rate := rate) hcursor i ⟨x, hx⟩
  else preparedCodeOnDeclared (rate := rate) hcursor i ⟨x, hx⟩

theorem measurable_preparedCodeOnCursor {block : Fin (n_boot p)} {cursor : Nat}
    (hcursor : cursor < BootstrapObservedFollower.blockLength p block)
    (i : Fin (p.m - 1)) :
    Measurable (preparedCodeOnCursor (rate := rate) hcursor i) := by
  apply measurable_of_restrict_of_restrict_compl
    (measurableSet_bootstrapLocalSet (rate := rate) (block := block) (cursor := cursor))
  · change Measurable (fun x : bootstrapLocalSet
      (rate := rate) (block := block) (cursor := cursor) =>
        preparedCodeOnCursor (rate := rate) hcursor i x.1)
    convert measurable_preparedCodeOnBootstrap (rate := rate) hcursor i using 1
    funext x
    simp [preparedCodeOnCursor, x.2]
  · change Measurable (fun x : ↥((bootstrapLocalSet
      (rate := rate) (block := block) (cursor := cursor))ᶜ) =>
        preparedCodeOnCursor (rate := rate) hcursor i x.1)
    convert measurable_preparedCodeOnDeclared (rate := rate) hcursor i using 1
    funext x
    have hnot : x.1 ∉ bootstrapLocalSet (rate := rate) := x.2
    simp [preparedCodeOnCursor, hnot]

/-- The bootstrap observer's exact output code on the cursor-restricted
bootstrap branch. -/
def bootstrapObservationCodeOnCursor {block : Fin (n_boot p)} {cursor : Nat}
    (hcursor : cursor < BootstrapObservedFollower.blockLength p block)
    (_i : Fin (p.m - 1))
    (x : bootstrapLocalSet (rate := rate) (block := block) (cursor := cursor)) :
    FollowerObservationCode p rate block :=
  Sum.inl (BootstrapObservedFollower.observe p block
    (startupCodeOnBootstrap (rate := rate) x)
    (ActualBootstrapObservationCode.sourceIDs p (localSource (rate := rate) x.1))
    (ActualBootstrapObservationCode.sourceRows p (localSource (rate := rate) x.1))
    (localTime block cursor hcursor)
    (ActualInitializationPhysicalStep.observationOfGrid p
      (localFeedback (rate := rate) x.1)))

theorem measurable_bootstrapObservationCodeOnCursor
    {block : Fin (n_boot p)} {cursor : Nat}
    (hcursor : cursor < BootstrapObservedFollower.blockLength p block)
    (i : Fin (p.m - 1)) :
    Measurable (bootstrapObservationCodeOnCursor (rate := rate)
      (block := block) (cursor := cursor) hcursor i) := by
  have hsource : Measurable
      (fun x : bootstrapLocalSet (rate := rate) (block := block) (cursor := cursor) =>
        localSource (rate := rate) x.1) :=
    measurable_localSource.comp measurable_subtype_coe
  have hids := (ActualBootstrapObservationCode.measurable_sourceIDs p).comp hsource
  have hrows := (ActualBootstrapObservationCode.measurable_sourceRows p).comp hsource
  have hprivate := (ActualBootstrapObservationCode.measurable_sourcePrivate p).comp hsource
  have hstate := measurable_startupCodeOnBootstrap (rate := rate)
    (block := block) (cursor := cursor)
  have htime : Measurable (fun _ : bootstrapLocalSet (rate := rate)
      (block := block) (cursor := cursor) => localTime block cursor hcursor) :=
    measurable_const
  have hfeedback : Measurable (fun x : bootstrapLocalSet (rate := rate)
      (block := block) (cursor := cursor) => localFeedback (rate := rate) x.1) :=
    measurable_localFeedback.comp measurable_subtype_coe
  have hobservationOfGrid : Measurable (ActualInitializationPhysicalStep.observationOfGrid p) := by
    apply measurable_of_countable
  have hobservation : Measurable (fun x : bootstrapLocalSet (rate := rate)
      (block := block) (cursor := cursor) =>
        ActualInitializationPhysicalStep.observationOfGrid p
          (localFeedback (rate := rate) x.1)) :=
    hobservationOfGrid.comp hfeedback
  change Measurable (fun x : bootstrapLocalSet (rate := rate)
      (block := block) (cursor := cursor) =>
        Sum.inl (BootstrapObservedFollower.observe p block
          (startupCodeOnBootstrap (rate := rate) x)
          (ActualBootstrapObservationCode.sourceIDs p (localSource (rate := rate) x.1))
          (ActualBootstrapObservationCode.sourceRows p (localSource (rate := rate) x.1))
          (localTime block cursor hcursor)
          (ActualInitializationPhysicalStep.observationOfGrid p
            (localFeedback (rate := rate) x.1))))
  exact measurable_inl.comp <| ActualBootstrapObservationCode.measurable_observe_of_components
    (fun x => ActualBootstrapObservationCode.sourceIDs p (localSource (rate := rate) x.1))
    (fun x => ActualBootstrapObservationCode.sourceRows p (localSource (rate := rate) x.1))
    (fun x => ActualBootstrapObservationCode.sourcePrivate p (localSource (rate := rate) x.1))
    (startupCodeOnBootstrap (rate := rate))
    (fun _ => localTime block cursor hcursor)
    (fun x => ActualInitializationPhysicalStep.observationOfGrid p
      (localFeedback (rate := rate) x.1))
    hids hrows hprivate hstate htime hobservation

/-- The declared observer uses only the retained own row, activation,
incoming configuration, prepared arm, actual calendar time, and this
follower's supplied grid observation. -/
def declaredObservationCodeOnCursor {block : Fin (n_boot p)} {cursor : Nat}
    (hcursor : cursor < BootstrapObservedFollower.blockLength p block)
    (i : Fin (p.m - 1))
    (x : ↥((bootstrapLocalSet (rate := rate) (block := block) (cursor := cursor))ᶜ)) :
    FollowerObservationCode p rate block := by
  let fields := declaredCodeOnBootstrapComplement (rate := rate) x
  let source := localSource (rate := rate) x.1
  let row := ActualBootstrapObservationCode.sourceRows p source fields.1
  let time := localTime block cursor hcursor
  have hvalid := declaredActivation_le_time_of_code (rate := rate) hcursor x.1 fields
    (followerStateCode_eq_inr_on_bootstrap_complement (rate := rate) x)
  let output := FollowerVaryingActivationMeasurability.varyingPreparedOutput rate i
    (FollowerVaryingActivationMeasurability.assembleVaryingPrepareInput
      fields.2.1 fields.2.2 row time hvalid)
  let observe := DeclaredFollowerObservationMeasurability.observeVaryingCarriedOutputAtComponents
    rate i (fun _ : Unit => fields.2.1) (fun _ => output.2.2.2) (fun _ => row)
    (fun _ => time) (fun _ => output.2.2.1)
    (fun _ => localFeedback (rate := rate) x.1)
    (fun _ => hvalid)
  exact Sum.inr (observe ())

theorem measurable_declaredObservationCodeOnCursor
    {block : Fin (n_boot p)} {cursor : Nat}
    (hcursor : cursor < BootstrapObservedFollower.blockLength p block)
    (i : Fin (p.m - 1)) :
    Measurable (declaredObservationCodeOnCursor (rate := rate)
      (block := block) (cursor := cursor) hcursor i) := by
  let fields := declaredCodeOnBootstrapComplement (rate := rate)
    (block := block) (cursor := cursor)
  have hfields := measurable_declaredCodeOnBootstrapComplement (rate := rate)
    (block := block) (cursor := cursor)
  have hrowIndex : Measurable (fun x : ↥((bootstrapLocalSet (rate := rate)
      (block := block) (cursor := cursor))ᶜ) => (fields x).1) :=
    measurable_fst.comp hfields
  have hactivation : Measurable (fun x : ↥((bootstrapLocalSet (rate := rate)
      (block := block) (cursor := cursor))ᶜ) => (fields x).2.1) :=
    measurable_fst.comp (measurable_snd.comp hfields)
  have hincoming : Measurable (fun x : ↥((bootstrapLocalSet (rate := rate)
      (block := block) (cursor := cursor))ᶜ) => (fields x).2.2) :=
    measurable_snd.comp (measurable_snd.comp hfields)
  have hsource : Measurable
      (fun x : ↥((bootstrapLocalSet (rate := rate) (block := block)
          (cursor := cursor))ᶜ) => localSource (rate := rate) x.1) :=
    measurable_localSource.comp measurable_subtype_coe
  have hrows := (ActualBootstrapObservationCode.measurable_sourceRows p).comp hsource
  have hrow : Measurable (fun x : ↥((bootstrapLocalSet (rate := rate)
      (block := block) (cursor := cursor))ᶜ) =>
        ActualBootstrapObservationCode.sourceRows p (localSource (rate := rate) x.1)
          (fields x).1) := by
    exact (measurable_evalCompleteRows_local p).comp (hrows.prodMk hrowIndex)
  have htime : Measurable (fun _ : ↥((bootstrapLocalSet (rate := rate)
      (block := block) (cursor := cursor))ᶜ) => localTime block cursor hcursor) :=
    measurable_const
  have hvalid (x : ↥((bootstrapLocalSet (rate := rate)
      (block := block) (cursor := cursor))ᶜ)) :
      (fields x).2.1.val ≤ (localTime block cursor hcursor).val + 1 :=
    declaredActivation_le_time_of_code (rate := rate) hcursor x.1 (fields x)
      (followerStateCode_eq_inr_on_bootstrap_complement (rate := rate) x)
  have hprepared : Measurable (fun x : ↥((bootstrapLocalSet (rate := rate)
      (block := block) (cursor := cursor))ᶜ) =>
        FollowerVaryingActivationMeasurability.varyingPreparedOutput rate i
          (FollowerVaryingActivationMeasurability.assembleVaryingPrepareInput
            (fields x).2.1 (fields x).2.2
            (ActualBootstrapObservationCode.sourceRows p
              (localSource (rate := rate) x.1) (fields x).1)
            (localTime block cursor hcursor) (hvalid x))) := by
    exact FollowerVaryingActivationMeasurability.measurable_varyingPreparedOutput_atComponents
      rate i (fun x => (fields x).2.1) (fun x => (fields x).2.2)
      (fun x => ActualBootstrapObservationCode.sourceRows p
        (localSource (rate := rate) x.1) (fields x).1)
      (fun _ => localTime block cursor hcursor)
      hactivation hincoming hrow htime hvalid
  have harm : Measurable (fun x : ↥((bootstrapLocalSet (rate := rate)
      (block := block) (cursor := cursor))ᶜ) =>
        (FollowerVaryingActivationMeasurability.varyingPreparedOutput rate i
          (FollowerVaryingActivationMeasurability.assembleVaryingPrepareInput
            (fields x).2.1 (fields x).2.2
            (ActualBootstrapObservationCode.sourceRows p
              (localSource (rate := rate) x.1) (fields x).1)
            (localTime block cursor hcursor) (hvalid x))).2.2.1) := by
    simpa [FollowerVaryingActivationMeasurability.varyingPreparedOutput,
      FollowerVaryingActivationMeasurability.varyingPreparedArm] using
      FollowerVaryingActivationMeasurability.measurable_varyingPreparedArm_atComponents
        rate i (fun x => (fields x).2.1) (fun x => (fields x).2.2)
        (fun x => ActualBootstrapObservationCode.sourceRows p
          (localSource (rate := rate) x.1) (fields x).1)
        (fun _ => localTime block cursor hcursor)
        hactivation hincoming hrow htime hvalid
  have hincomingPrepared : Measurable (fun x : ↥((bootstrapLocalSet (rate := rate)
      (block := block) (cursor := cursor))ᶜ) =>
        FollowerVaryingActivationMeasurability.varyingPreparedConfiguration
          (rate := rate) i
          (FollowerVaryingActivationMeasurability.assembleVaryingPrepareInput
            (fields x).2.1 (fields x).2.2
            (ActualBootstrapObservationCode.sourceRows p
              (localSource (rate := rate) x.1) (fields x).1)
            (localTime block cursor hcursor) (hvalid x))) := by
    exact FollowerVaryingActivationMeasurability.measurable_varyingPreparedConfiguration_atComponents
      rate i (fun x => (fields x).2.1) (fun x => (fields x).2.2)
      (fun x => ActualBootstrapObservationCode.sourceRows p
        (localSource (rate := rate) x.1) (fields x).1)
      (fun _ => localTime block cursor hcursor)
      hactivation hincoming hrow htime hvalid
  have hfeedback : Measurable (fun x : ↥((bootstrapLocalSet (rate := rate)
      (block := block) (cursor := cursor))ᶜ) => localFeedback (rate := rate) x.1) :=
    measurable_localFeedback.comp measurable_subtype_coe
  have hcode : Measurable
      (DeclaredFollowerObservationMeasurability.observeVaryingCarriedOutputAtComponents
        rate i (fun x => (fields x).2.1)
        (fun x => FollowerVaryingActivationMeasurability.varyingPreparedConfiguration
          (rate := rate) i
          (FollowerVaryingActivationMeasurability.assembleVaryingPrepareInput
            (fields x).2.1 (fields x).2.2
            (ActualBootstrapObservationCode.sourceRows p
              (localSource (rate := rate) x.1) (fields x).1)
            (localTime block cursor hcursor) (hvalid x)))
        (fun x => ActualBootstrapObservationCode.sourceRows p
          (localSource (rate := rate) x.1) (fields x).1)
        (fun _ => localTime block cursor hcursor)
        (fun x => (FollowerVaryingActivationMeasurability.varyingPreparedOutput rate i
          (FollowerVaryingActivationMeasurability.assembleVaryingPrepareInput
            (fields x).2.1 (fields x).2.2
            (ActualBootstrapObservationCode.sourceRows p
              (localSource (rate := rate) x.1) (fields x).1)
            (localTime block cursor hcursor) (hvalid x))).2.2.1)
        (fun x => localFeedback (rate := rate) x.1) hvalid) := by
    exact DeclaredFollowerObservationMeasurability.measurable_observeVaryingCarriedOutputAtComponents
      rate i (fun x => (fields x).2.1)
      (fun x => FollowerVaryingActivationMeasurability.varyingPreparedConfiguration
        (rate := rate) i
        (FollowerVaryingActivationMeasurability.assembleVaryingPrepareInput
          (fields x).2.1 (fields x).2.2
          (ActualBootstrapObservationCode.sourceRows p
            (localSource (rate := rate) x.1) (fields x).1)
          (localTime block cursor hcursor) (hvalid x)))
      (fun x => ActualBootstrapObservationCode.sourceRows p
        (localSource (rate := rate) x.1) (fields x).1)
      (fun _ => localTime block cursor hcursor)
      (fun x => (FollowerVaryingActivationMeasurability.varyingPreparedOutput rate i
        (FollowerVaryingActivationMeasurability.assembleVaryingPrepareInput
          (fields x).2.1 (fields x).2.2
          (ActualBootstrapObservationCode.sourceRows p
            (localSource (rate := rate) x.1) (fields x).1)
          (localTime block cursor hcursor) (hvalid x))).2.2.1)
      (fun x => localFeedback (rate := rate) x.1)
      hactivation hincomingPrepared hrow htime harm hfeedback hvalid
  change Measurable (fun x : ↥((bootstrapLocalSet (rate := rate)
      (block := block) (cursor := cursor))ᶜ) =>
        Sum.inr (DeclaredFollowerObservationMeasurability.observeVaryingCarriedOutputAtComponents
          rate i (fun x => (fields x).2.1)
          (fun x => FollowerVaryingActivationMeasurability.varyingPreparedConfiguration
            (rate := rate) i
            (FollowerVaryingActivationMeasurability.assembleVaryingPrepareInput
              (fields x).2.1 (fields x).2.2
              (ActualBootstrapObservationCode.sourceRows p
                (localSource (rate := rate) x.1) (fields x).1)
              (localTime block cursor hcursor) (hvalid x)))
          (fun x => ActualBootstrapObservationCode.sourceRows p
            (localSource (rate := rate) x.1) (fields x).1)
          (fun _ => localTime block cursor hcursor)
          (fun x => (FollowerVaryingActivationMeasurability.varyingPreparedOutput rate i
            (FollowerVaryingActivationMeasurability.assembleVaryingPrepareInput
              (fields x).2.1 (fields x).2.2
              (ActualBootstrapObservationCode.sourceRows p
                (localSource (rate := rate) x.1) (fields x).1)
              (localTime block cursor hcursor) (hvalid x))).2.2.1)
          (fun x => localFeedback (rate := rate) x.1) hvalid x))
  exact measurable_inr.comp hcode

/-- The exact observation-code producer on the one local cursor domain. -/
def observationCodeOnCursor {block : Fin (n_boot p)} {cursor : Nat}
    (hcursor : cursor < BootstrapObservedFollower.blockLength p block)
    (i : Fin (p.m - 1)) (x : LocalInput (rate := rate) block cursor) :
    FollowerObservationCode p rate block := by
  classical
  exact if hx : x ∈ bootstrapLocalSet (rate := rate) then
    bootstrapObservationCodeOnCursor (rate := rate) hcursor i ⟨x, hx⟩
  else declaredObservationCodeOnCursor (rate := rate) hcursor i ⟨x, hx⟩

theorem measurable_observationCodeOnCursor {block : Fin (n_boot p)} {cursor : Nat}
    (hcursor : cursor < BootstrapObservedFollower.blockLength p block)
    (i : Fin (p.m - 1)) :
    Measurable (observationCodeOnCursor (rate := rate) hcursor i) := by
  apply measurable_of_restrict_of_restrict_compl
    (measurableSet_bootstrapLocalSet (rate := rate) (block := block) (cursor := cursor))
  · change Measurable (fun x : bootstrapLocalSet
      (rate := rate) (block := block) (cursor := cursor) =>
        observationCodeOnCursor (rate := rate) hcursor i x.1)
    convert measurable_bootstrapObservationCodeOnCursor (rate := rate) hcursor i using 1
    funext x
    simp [observationCodeOnCursor, x.2]
  · change Measurable (fun x : ↥((bootstrapLocalSet
      (rate := rate) (block := block) (cursor := cursor))ᶜ) =>
        observationCodeOnCursor (rate := rate) hcursor i x.1)
    convert measurable_declaredObservationCodeOnCursor (rate := rate) hcursor i using 1
    funext x
    have hnot : x.1 ∉ bootstrapLocalSet (rate := rate) := x.2
    simp [observationCodeOnCursor, hnot]

/-- The prepared code decodes to the literal accepted preparation on the
same source, time, and cursor-restricted follower. -/
theorem decode_preparedCodeOnCursor {block : Fin (n_boot p)} {cursor : Nat}
    (hcursor : cursor < BootstrapObservedFollower.blockLength p block)
    (i : Fin (p.m - 1)) (source : SourceInput p)
    (follower : FollowerState p rate block)
    (hstate : ActualInitializationRun.followerAtCursor p rate block cursor follower)
    (ownY : Fin (D p + 1)) :
    ActualInitializationPreparationMeasurability.decodePreparedFollowerCode
      (rate := rate) (block := block) i source
      (localTime block cursor hcursor)
      (preparedCodeOnCursor (rate := rate) hcursor i
        (source, (⟨follower, hstate⟩, ownY))) =
    some (ActualInitializationPhysicalStep.prepareFollowerValid rate block
      (localTime block cursor hcursor) source i
      follower (follower_ready_of_cursor (rate := rate) hcursor ⟨follower, hstate⟩)) := by
  classical
  let x : LocalInput (rate := rate) block cursor := (source, (⟨follower, hstate⟩, ownY))
  cases follower with
  | bootstrap startup =>
      have hmem : x ∈ bootstrapLocalSet (rate := rate) := by
        change localFollowerStateCode (rate := rate) x ∈ Set.range Sum.inl
        simp [x, localFollowerStateCode, localFollower,
          ActualInitializationRoundMeasurability.followerCodeOfState]
      let branch : bootstrapLocalSet (rate := rate) := ⟨x, hmem⟩
      have hstartup : startupCodeOnBootstrap (rate := rate) branch = startup := by
        simp [startupCodeOnBootstrap, branch, x, localFollowerStateCode, localFollower,
          ActualInitializationRoundMeasurability.followerCodeOfState]
      let source := localSource (rate := rate) x
      let time := localTime block cursor hcursor
      let ids := ActualBootstrapObservationCode.sourceIDs p source
      let scalar := BootstrapPhysicalInput.playerRoundScalarAt p
        (ActualBootstrapObservationCode.sourcePrivate p source)
        (PublicDiscreteDraws.followerPlayer p.two_le_m i) time
      have hlocal : BootstrapObservedFollower.localArm p block startup ids time
          (fun _ => scalar) =
          BootstrapObservedFollower.localArm p block startup ids time
            (fun t => BootstrapPhysicalInput.playerRoundScalarAt p
              (ActualBootstrapObservationCode.sourcePrivate p source)
              (PublicDiscreteDraws.followerPlayer p.two_le_m i) t) := by
        exact BootstrapObservedFollower.localArm_current_scalar_locality p block startup ids
          time (fun _ => scalar)
          (fun t => BootstrapPhysicalInput.playerRoundScalarAt p
            (ActualBootstrapObservationCode.sourcePrivate p source)
            (PublicDiscreteDraws.followerPlayer p.two_le_m i) t) rfl
      simp [x, preparedCodeOnCursor, hmem, preparedCodeOnBootstrap, branch,
        hstartup, ActualInitializationPreparationMeasurability.decodePreparedFollowerCode]
      simp only [ActualInitializationPhysicalStep.prepareFollowerValid]
      dsimp [ActualInitializationPreparationMeasurability.bootstrapLocalArmFromComponents,
        source, ids, scalar, time]
      simpa [x, localSource, source, ids, scalar, time,
        ActualBootstrapObservationCode.sourceIDs,
        ActualBootstrapObservationCode.sourcePrivate] using hlocal
  | declared row activation configuration =>
      have hnot : x ∉ bootstrapLocalSet (rate := rate) := by
        change localFollowerStateCode (rate := rate) x ∉ Set.range Sum.inl
        simp [x, localFollowerStateCode, localFollower,
          ActualInitializationRoundMeasurability.followerCodeOfState]
      let branch : ↥((bootstrapLocalSet (rate := rate))ᶜ) := ⟨x, hnot⟩
      let fields : DeclaredCode p rate :=
        (row, (activation,
          FollowerPrepareJointMeasurability.incomingOfLocalConfiguration rate configuration))
      have hfields : declaredCodeOnBootstrapComplement (rate := rate) branch = fields := by
        simp [declaredCodeOnBootstrapComplement, branch, x, localFollowerStateCode,
          localFollower, fields, ActualInitializationRoundMeasurability.followerCodeOfState]
      have hvalid : activation.val ≤ (localTime block cursor hcursor).val + 1 := by
        simpa [localTime, ActualInitializationRun.blockTime,
          ActualInitializationRun.followerAtCursor] using hstate
      let incoming := fields.2.2
      let rowValue := ActualBootstrapObservationCode.sourceRows p
        (localSource (rate := rate) x) fields.1
      let output := FollowerVaryingActivationMeasurability.varyingPreparedOutput rate i
        (FollowerVaryingActivationMeasurability.assembleVaryingPrepareInput
          activation incoming rowValue (localTime block cursor hcursor) hvalid)
      have hrowExact : FollowerPrepareJointMeasurability.prepareInputRow
          (FollowerPrepareJointMeasurability.assemblePrepareInput
            (FollowerPrepareJointMeasurability.incomingOfLocalConfiguration rate configuration)
            (source.1.2 row)
            ⟨localTime block cursor hcursor, hvalid⟩) = rowValue := by
        cases configuration <;> rfl
      have htimeExact : FollowerPrepareJointMeasurability.prepareInputTime
          (FollowerPrepareJointMeasurability.assemblePrepareInput
            (FollowerPrepareJointMeasurability.incomingOfLocalConfiguration rate configuration)
            (source.1.2 row)
            ⟨localTime block cursor hcursor, hvalid⟩) =
          ⟨localTime block cursor hcursor, hvalid⟩ := by
        cases configuration <;> rfl
      have hcode : preparedCodeOnCursor (rate := rate) hcursor i x =
          Sum.inr (row, (activation, (output.2.2.1, output.2.2.2))) := by
        simp only [preparedCodeOnCursor, dite_eq_right hnot]
        rfl
      have hprepare := FollowerVaryingActivationMeasurability.assembledPrepare_reconstructs_prepare
        rate i activation incoming rowValue (localTime block cursor hcursor) hvalid
      rw [hcode]
      simp only [ActualInitializationPreparationMeasurability.decodePreparedFollowerCode]
      rw [dite_eq_left hvalid]
      apply congrArg some
      apply congrArg (ActualInitializationPhysicalStep.PreparedFollower.declared
        (p := p) (rate := rate) (block := block) row activation)
      simpa [x, localSource, fields, incoming, rowValue, output,
        FollowerVaryingActivationMeasurability.varyingPreparedOutput,
        FollowerVaryingActivationMeasurability.assembleVaryingPrepareInput,
        FollowerPrepareJointMeasurability.prepareOutputOnInput,
        hrowExact, htimeExact,
        FollowerPrepareJointMeasurability.localConfigurationOfIncoming_incomingOfLocalConfiguration,
        ActualBootstrapObservationCode.sourceRows] using hprepare

/-- Every typed local grid input has a successful actual follower observation.
This is derived from its existing next-cursor restriction. -/
theorem observeFollower_success_on_cursor {block : Fin (n_boot p)} {cursor : Nat}
    (hcursor : cursor < BootstrapObservedFollower.blockLength p block)
    (i : Fin (p.m - 1)) (x : LocalInput (rate := rate) block cursor) :
    ∃ outcome, ActualInitializationPhysicalStep.observeFollower rate block
      (localTime block cursor hcursor) (localSource (rate := rate) x) i
      (ActualInitializationPhysicalStep.prepareFollowerValid rate block
        (localTime block cursor hcursor) (localSource (rate := rate) x) i
        (localFollower (rate := rate) x)
        (follower_ready_of_cursor (rate := rate) hcursor x.2.1))
      (localFeedback (rate := rate) x) = .ok outcome := by
  exact ActualInitializationPhysicalStep.observeFollower_success_of_state rate block
    (localTime block cursor hcursor) (localSource (rate := rate) x) i
    (localFollower (rate := rate) x)
    (follower_ready_of_cursor (rate := rate) hcursor x.2.1)
    (localFeedback (rate := rate) x)

/-- The partial successor producer on the exact preparation/observation pair.
Its rejected and incompatible tags are retained until the range proof below. -/
def partialSuccessorCodeOnCursor {block : Fin (n_boot p)} {cursor : Nat}
    (hcursor : cursor < BootstrapObservedFollower.blockLength p block)
    (i : Fin (p.m - 1)) (x : LocalInput (rate := rate) block cursor) :
    Unit ⊕ FollowerSuccessorCode p rate block :=
  ActualInitializationStepMeasurability.followerSuccessorCodeFromOutput rate block
    (preparedCodeOnCursor (rate := rate) hcursor i x,
      observationCodeOnCursor (rate := rate) hcursor i x)

/-- On the local cursor domain, the partial successor output is always a real
follower code. Bootstrap rejection is ruled out by the actual successful
observer theorem for this state and every typed own grid value. -/
theorem partialSuccessorCode_mem_inr_components {block : Fin (n_boot p)}
    {cursor : Nat} (hcursor : cursor < BootstrapObservedFollower.blockLength p block)
    (i : Fin (p.m - 1)) (source : SourceInput p)
    (follower : FollowerState p rate block)
    (hstate : ActualInitializationRun.followerAtCursor p rate block cursor follower)
    (ownY : Fin (D p + 1)) :
    partialSuccessorCodeOnCursor (rate := rate) hcursor i
      (localInputOfComponents (rate := rate) source follower hstate ownY) ∈
      Set.range Sum.inr := by
  classical
  let x := localInputOfComponents (rate := rate) source follower hstate ownY
  cases follower with
  | bootstrap startup =>
      have hready := follower_ready_of_cursor (rate := rate) hcursor
        ⟨FollowerState.bootstrap (rate := rate) startup, hstate⟩
      change localTime block cursor hcursor ∈ BootstrapDimensions.calendarBlock p block ∧
        startup.processed.val < BootstrapObservedFollower.blockLength p block ∧
        (localTime block cursor hcursor).val =
          BootstrapObservedFollower.blockStart p block + startup.processed.val at hready
      let next := BootstrapObservedFollower.observeOne p block startup
        (ActualBootstrapObservationCode.sourceIDs p source)
        (ActualBootstrapObservationCode.sourceRows p source)
        (localTime block cursor hcursor) (ActualInitializationPhysicalStep.observationOfGrid p ownY)
        hready.1 hready.2.1 hready.2.2
      have hobserve : BootstrapObservedFollower.observe p block startup
          (ActualBootstrapObservationCode.sourceIDs p source)
          (ActualBootstrapObservationCode.sourceRows p source)
          (localTime block cursor hcursor)
          (ActualInitializationPhysicalStep.observationOfGrid p ownY) = .accepted next := by
        exact BootstrapObservedFollower.observe_accepted_processed p block startup
          (ActualBootstrapObservationCode.sourceIDs p source)
          (ActualBootstrapObservationCode.sourceRows p source)
          (localTime block cursor hcursor)
          (ActualInitializationPhysicalStep.observationOfGrid p ownY)
          hready.1 hready.2.1 hready.2.2
      have hmem : (source, (⟨FollowerState.bootstrap startup, hstate⟩, ownY)) ∈
          bootstrapLocalSet (rate := rate) := by
        change localFollowerStateCode (rate := rate)
          (source, (⟨FollowerState.bootstrap startup, hstate⟩, ownY)) ∈ Set.range Sum.inl
        simp [localFollowerStateCode, localFollower,
          ActualInitializationRoundMeasurability.followerCodeOfState]
      have hstartup : startupCodeOnBootstrap (rate := rate)
          ⟨(source, (⟨FollowerState.bootstrap startup, hstate⟩, ownY)), hmem⟩ = startup := by
        simp [startupCodeOnBootstrap, localFollowerStateCode, localFollower,
          ActualInitializationRoundMeasurability.followerCodeOfState]
      have hprepared : ∃ code,
          preparedCodeOnCursor (rate := rate) hcursor i x = Sum.inl code := by
        change ∃ code, preparedCodeOnCursor (rate := rate) hcursor i
          (source, (⟨FollowerState.bootstrap startup, hstate⟩, ownY)) = Sum.inl code
        simp only [preparedCodeOnCursor, dite_eq_left hmem]
        exact ⟨_, rfl⟩
      rcases hprepared with ⟨prepared, hprepared⟩
      have hobserved : observationCodeOnCursor (rate := rate) hcursor i x =
          Sum.inl (.accepted next) := by
        change observationCodeOnCursor (rate := rate) hcursor i
          (source, (⟨FollowerState.bootstrap startup, hstate⟩, ownY)) = _
        simp only [observationCodeOnCursor, dite_eq_left hmem,
          bootstrapObservationCodeOnCursor]
        simpa [hstartup, localSource, localFeedback, ActualBootstrapObservationCode.sourceIDs,
          ActualBootstrapObservationCode.sourceRows] using hobserve
      rw [partialSuccessorCodeOnCursor, hprepared, hobserved]
      exact ⟨Sum.inl next, rfl⟩
  | declared row activation configuration =>
      have hnot : (source, (⟨FollowerState.declared row activation configuration, hstate⟩, ownY)) ∉
          bootstrapLocalSet (rate := rate) := by
        change localFollowerStateCode (rate := rate)
          (source, (⟨FollowerState.declared row activation configuration, hstate⟩, ownY)) ∉
          Set.range Sum.inl
        simp [localFollowerStateCode, localFollower,
          ActualInitializationRoundMeasurability.followerCodeOfState]
      have hprepared : ∃ code,
          preparedCodeOnCursor (rate := rate) hcursor i x = Sum.inr code := by
        change ∃ code, preparedCodeOnCursor (rate := rate) hcursor i
          (source, (⟨FollowerState.declared row activation configuration, hstate⟩, ownY)) =
            Sum.inr code
        simp only [preparedCodeOnCursor, dite_eq_right hnot]
        exact ⟨_, rfl⟩
      have hobserved : ∃ code,
          observationCodeOnCursor (rate := rate) hcursor i x = Sum.inr code := by
        change ∃ code, observationCodeOnCursor (rate := rate) hcursor i
          (source, (⟨FollowerState.declared row activation configuration, hstate⟩, ownY)) =
            Sum.inr code
        simp only [observationCodeOnCursor, dite_eq_right hnot]
        exact ⟨_, rfl⟩
      rcases hprepared with ⟨prepared, hprepared⟩
      rcases hobserved with ⟨observed, hobserved⟩
      rw [partialSuccessorCodeOnCursor, hprepared, hobserved]
      exact ⟨Sum.inr (prepared.1, (observed.1, observed.2.2)), rfl⟩

/-- The same range fact for an arbitrary point of the typed local domain. -/
theorem partialSuccessorCode_mem_inr {block : Fin (n_boot p)} {cursor : Nat}
    (hcursor : cursor < BootstrapObservedFollower.blockLength p block)
    (i : Fin (p.m - 1)) (x : LocalInput (rate := rate) block cursor) :
    partialSuccessorCodeOnCursor (rate := rate) hcursor i x ∈ Set.range Sum.inr := by
  rcases x with ⟨source, ⟨follower, hstate⟩, ownY⟩
  exact partialSuccessorCode_mem_inr_components (rate := rate) hcursor i
    source follower hstate ownY

/-- Extract the successor only on the proved `Sum.inr` range. There is no
operational default for a rejected bootstrap observer. -/
def successorCodeOnCursor {block : Fin (n_boot p)} {cursor : Nat}
    (hcursor : cursor < BootstrapObservedFollower.blockLength p block)
    (i : Fin (p.m - 1)) (x : LocalInput (rate := rate) block cursor) :
    FollowerSuccessorCode p rate block :=
  Equiv.Set.rangeInr _ _
    ⟨partialSuccessorCodeOnCursor (rate := rate) hcursor i x,
      partialSuccessorCode_mem_inr (rate := rate) hcursor i x⟩

theorem measurable_successorCodeOnCursor {block : Fin (n_boot p)} {cursor : Nat}
    (hcursor : cursor < BootstrapObservedFollower.blockLength p block)
    (i : Fin (p.m - 1)) :
    Measurable (successorCodeOnCursor (rate := rate) hcursor i) := by
  have hpartial : Measurable (partialSuccessorCodeOnCursor (rate := rate) hcursor i) :=
    (ActualInitializationStepMeasurability.measurable_followerSuccessorCodeFromOutput
      rate block).comp
      ((measurable_preparedCodeOnCursor (rate := rate) hcursor i).prodMk
        (measurable_observationCodeOnCursor (rate := rate) hcursor i))
  have hrange : Measurable (fun x : LocalInput (rate := rate) block cursor =>
      (⟨partialSuccessorCodeOnCursor (rate := rate) hcursor i x,
        partialSuccessorCode_mem_inr (rate := rate) hcursor i x⟩ : Set.range Sum.inr)) := by
    exact hpartial.subtype_mk
  exact MeasurableEquiv.Set.rangeInr.measurable_toFun.comp hrange

/-- The coherent three-part local output code, retaining its original
prepared output, exact observer output, and extracted actual successor. -/
def localCodeOnCursor {block : Fin (n_boot p)} {cursor : Nat}
    (hcursor : cursor < BootstrapObservedFollower.blockLength p block)
    (i : Fin (p.m - 1)) (x : LocalInput (rate := rate) block cursor) :
    LocalCode (rate := rate) block :=
  (preparedCodeOnCursor (rate := rate) hcursor i x,
    (observationCodeOnCursor (rate := rate) hcursor i x,
      successorCodeOnCursor (rate := rate) hcursor i x))

theorem measurable_localCodeOnCursor {block : Fin (n_boot p)} {cursor : Nat}
    (hcursor : cursor < BootstrapObservedFollower.blockLength p block)
    (i : Fin (p.m - 1)) :
    Measurable (localCodeOnCursor (rate := rate) hcursor i) := by
  exact (measurable_preparedCodeOnCursor (rate := rate) hcursor i).prodMk
    ((measurable_observationCodeOnCursor (rate := rate) hcursor i).prodMk
      (measurable_successorCodeOnCursor (rate := rate) hcursor i))

/-- Separate Borel source, typed cursor-follower, and own-grid maps may be
composed into the exact local output code. -/
theorem measurable_localCodeOnComponents {block : Fin (n_boot p)} {cursor : Nat}
    (hcursor : cursor < BootstrapObservedFollower.blockLength p block)
    (i : Fin (p.m - 1)) {Ω : Type*} [MeasurableSpace Ω]
    (source : Ω → SourceInput p)
    (follower : Ω → CursorFollowerInput (rate := rate) block cursor)
    (ownY : Ω → Fin (D p + 1))
    (hsource : Measurable source) (hfollower : Measurable follower)
    (hownY : Measurable ownY) :
    Measurable (fun ω => localCodeOnCursor (rate := rate) hcursor i
      (source ω, (follower ω, ownY ω))) :=
  (measurable_localCodeOnCursor (rate := rate) hcursor i).comp
    (hsource.prodMk (hfollower.prodMk hownY))

/-- The range extraction is an inverse of the already proved partial output. -/
theorem partialSuccessorCode_eq_inr_successorCode {block : Fin (n_boot p)}
    {cursor : Nat} (hcursor : cursor < BootstrapObservedFollower.blockLength p block)
    (i : Fin (p.m - 1)) (x : LocalInput (rate := rate) block cursor) :
    partialSuccessorCodeOnCursor (rate := rate) hcursor i x =
      Sum.inr (successorCodeOnCursor (rate := rate) hcursor i x) := by
  cases hpartial : partialSuccessorCodeOnCursor (rate := rate) hcursor i x with
  | inl rejected =>
      obtain ⟨code, hcode⟩ := partialSuccessorCode_mem_inr
        (rate := rate) hcursor i x
      rw [hpartial] at hcode
      cases hcode
  | inr code =>
      simp [successorCodeOnCursor, hpartial]

/-- Decode the retained preparation and successor codes to the existing
`FollowerOutcome` carrier. This decoder only reads codes; it does not rerun
PREPARE or OBSERVE. -/
def decodeLocalCode {block : Fin (n_boot p)}
    (source : SourceInput p) (time : Fin p.T) (i : Fin (p.m - 1))
    (code : LocalCode (rate := rate) block) :
    Option (ActualInitializationPhysicalStep.FollowerOutcome p rate block) :=
  (ActualInitializationPreparationMeasurability.decodePreparedFollowerCode
    (rate := rate) (block := block) i source time code.1).map
      (fun prepared =>
        ⟨prepared, ActualInitializationRoundMeasurability.followerStateOfCode p rate block
          code.2.2⟩)

/-- The code decoder reconstructs the actual local preparation and the
existing follower state represented by its successor code. -/
theorem decode_localCodeOnComponents {block : Fin (n_boot p)} {cursor : Nat}
    (hcursor : cursor < BootstrapObservedFollower.blockLength p block)
    (i : Fin (p.m - 1)) (source : SourceInput p)
    (follower : FollowerState p rate block)
    (hstate : ActualInitializationRun.followerAtCursor p rate block cursor follower)
    (ownY : Fin (D p + 1)) :
    decodeLocalCode (rate := rate) (block := block) source
      (localTime block cursor hcursor) i
      (localCodeOnCursor (rate := rate) hcursor i
        (localInputOfComponents (rate := rate) source follower hstate ownY)) =
    some ⟨ActualInitializationPhysicalStep.prepareFollowerValid rate block
      (localTime block cursor hcursor) source i follower
      (follower_ready_of_cursor (rate := rate) hcursor ⟨follower, hstate⟩),
      ActualInitializationRoundMeasurability.followerStateOfCode p rate block
        (successorCodeOnCursor (rate := rate) hcursor i
          (localInputOfComponents (rate := rate) source follower hstate ownY))⟩ := by
  simp only [decodeLocalCode, localCodeOnCursor, localInputOfComponents]
  rw [decode_preparedCodeOnCursor (rate := rate) hcursor i source follower hstate ownY]
  rfl

/-- The exact existing physical follower outcome represented by the local
three-part code. -/
def localOutcomeOnCursor {block : Fin (n_boot p)} {cursor : Nat}
    (hcursor : cursor < BootstrapObservedFollower.blockLength p block)
    (i : Fin (p.m - 1)) (source : SourceInput p)
    (follower : FollowerState p rate block)
    (hstate : ActualInitializationRun.followerAtCursor p rate block cursor follower)
    (ownY : Fin (D p + 1)) : ActualInitializationPhysicalStep.FollowerOutcome p rate block :=
  ⟨ActualInitializationPhysicalStep.prepareFollowerValid rate block
      (localTime block cursor hcursor) source i follower
      (follower_ready_of_cursor (rate := rate) hcursor ⟨follower, hstate⟩),
    ActualInitializationRoundMeasurability.followerStateOfCode p rate block
      (successorCodeOnCursor (rate := rate) hcursor i
        (localInputOfComponents (rate := rate) source follower hstate ownY))⟩

/-- The observation code and its extracted successor reconstruct the exact
`observeFollower` result, including its retained prepared component. Bootstrap
acceptance comes from the actual cursor proof for every typed own-grid value;
declared observation uses the complete carried D output. -/
theorem observeFollower_eq_localOutcomeOnCursor {block : Fin (n_boot p)}
    {cursor : Nat} (hcursor : cursor < BootstrapObservedFollower.blockLength p block)
    (i : Fin (p.m - 1)) (source : SourceInput p)
    (follower : FollowerState p rate block)
    (hstate : ActualInitializationRun.followerAtCursor p rate block cursor follower)
    (ownY : Fin (D p + 1)) :
    ActualInitializationPhysicalStep.observeFollower rate block
      (localTime block cursor hcursor) source i
      (ActualInitializationPhysicalStep.prepareFollowerValid rate block
        (localTime block cursor hcursor) source i follower
        (follower_ready_of_cursor (rate := rate) hcursor ⟨follower, hstate⟩)) ownY =
      .ok (localOutcomeOnCursor (rate := rate) hcursor i source follower hstate ownY) := by
  classical
  rcases ActualInitializationPhysicalStep.observeFollower_success_of_state rate block
      (localTime block cursor hcursor) source i follower
      (follower_ready_of_cursor (rate := rate) hcursor ⟨follower, hstate⟩) ownY with
    ⟨actualOutcome, hactual⟩
  cases follower with
  | bootstrap startup =>
      let x : LocalInput (rate := rate) block cursor :=
        (source, (⟨.bootstrap startup, hstate⟩, ownY))
      have hmem : x ∈ bootstrapLocalSet (rate := rate) := by
        change localFollowerStateCode (rate := rate) x ∈ Set.range Sum.inl
        simp [x, localFollowerStateCode, localFollower,
          ActualInitializationRoundMeasurability.followerCodeOfState]
      let branch : bootstrapLocalSet (rate := rate) := ⟨x, hmem⟩
      have hstartup : startupCodeOnBootstrap (rate := rate) branch = startup := by
        simp [startupCodeOnBootstrap, branch, x, localFollowerStateCode, localFollower,
          ActualInitializationRoundMeasurability.followerCodeOfState]
      let ready := follower_ready_of_cursor (rate := rate) hcursor ⟨.bootstrap startup, hstate⟩
      let next := BootstrapObservedFollower.observeOne p block startup
        (source.1.1) (source.1.2) (localTime block cursor hcursor)
        (ActualInitializationPhysicalStep.observationOfGrid p ownY)
        ready.1 ready.2.1 ready.2.2
      have haccepted := BootstrapObservedFollower.observe_accepted_processed p block startup
        source.1.1 source.1.2 (localTime block cursor hcursor)
        (ActualInitializationPhysicalStep.observationOfGrid p ownY)
        ready.1 ready.2.1 ready.2.2
      have hcodeObs : observationCodeOnCursor (rate := rate) hcursor i x =
          Sum.inl (.accepted next) := by
        simp [observationCodeOnCursor, x, hmem, bootstrapObservationCodeOnCursor,
          branch, hstartup, next, haccepted, localSource, localFeedback,
          ActualBootstrapObservationCode.sourceIDs,
          ActualBootstrapObservationCode.sourceRows]
      have hcodePrep : ∃ arm,
          preparedCodeOnCursor (rate := rate) hcursor i x = Sum.inl (startup, arm) := by
        simp [preparedCodeOnCursor, x, hmem, preparedCodeOnBootstrap, branch, hstartup]
      rcases hcodePrep with ⟨arm, hcodePrep⟩
      have hpartial : partialSuccessorCodeOnCursor (rate := rate) hcursor i x =
          Sum.inr (Sum.inl next) := by
        unfold partialSuccessorCodeOnCursor
        rw [hcodePrep, hcodeObs]
        rfl
      have hsuccessor : successorCodeOnCursor (rate := rate) hcursor i x = Sum.inl next := by
        have h := partialSuccessorCode_eq_inr_successorCode
          (rate := rate) hcursor i x
        rw [hpartial] at h
        exact (Sum.inr.inj h).symm
      have hsuccessor' : successorCodeOnCursor (rate := rate) hcursor i
          (localInputOfComponents (rate := rate) source (.bootstrap startup) hstate ownY) =
          Sum.inl next := by
        simpa [x, localInputOfComponents] using hsuccessor
      have hdecoded := decode_preparedCodeOnCursor
        (rate := rate) hcursor i source (.bootstrap startup) hstate ownY
      rw [hcodePrep] at hdecoded
      simp only [ActualInitializationPreparationMeasurability.decodePreparedFollowerCode,
        Option.some.injEq] at hdecoded
      have hprepared :
          ActualInitializationPhysicalStep.prepareFollowerValid rate block
            (localTime block cursor hcursor) source i (.bootstrap startup) ready =
          .bootstrap startup arm := hdecoded.symm
      unfold localOutcomeOnCursor
      rw [hprepared, hsuccessor']
      have hcode := ActualInitializationPhysicalStep.observeFollower_bootstrap_next_is_startup
        rate block (localTime block cursor hcursor) source i startup next arm ownY haccepted
      rw [hprepared] at hactual
      have hsame := Except.ok.inj (hactual.symm.trans hcode)
      rw [hsame] at hactual
      simpa only [ActualInitializationRoundMeasurability.followerStateOfCode] using hactual
  | declared row activation configuration =>
      let x : LocalInput (rate := rate) block cursor :=
        (source, (⟨.declared row activation configuration, hstate⟩, ownY))
      have hnot : x ∉ bootstrapLocalSet (rate := rate) := by
        change localFollowerStateCode (rate := rate) x ∉ Set.range Sum.inl
        simp [x, localFollowerStateCode, localFollower,
          ActualInitializationRoundMeasurability.followerCodeOfState]
      let branch : ↥((bootstrapLocalSet (rate := rate))ᶜ) := ⟨x, hnot⟩
      let fields := declaredCodeOnBootstrapComplement (rate := rate) branch
      let rowValue := ActualBootstrapObservationCode.sourceRows p source fields.1
      have hvalid : fields.2.1.val ≤ (localTime block cursor hcursor).val + 1 :=
        declaredActivation_le_time_of_code (rate := rate) hcursor x fields
          (followerStateCode_eq_inr_on_bootstrap_complement (rate := rate) branch)
      let prepInput := FollowerVaryingActivationMeasurability.assembleVaryingPrepareInput
        fields.2.1 fields.2.2 rowValue (localTime block cursor hcursor) hvalid
      let preparedOutput := FollowerVaryingActivationMeasurability.varyingPreparedOutput
        rate i prepInput
      let preparedData : FollowerPrepareJointMeasurability.PrepareOutput p rate fields.2.1 :=
        ((rowValue, ⟨localTime block cursor hcursor, hvalid⟩),
          (preparedOutput.2.2.1, preparedOutput.2.2.2))
      have hpreparedData : preparedData = preparedOutput.2 := by
        cases hin : fields.2.2 <;>
          simp [preparedData, preparedOutput, prepInput,
            FollowerVaryingActivationMeasurability.varyingPreparedOutput,
            FollowerVaryingActivationMeasurability.assembleVaryingPrepareInput,
            FollowerPrepareJointMeasurability.prepareOutputOnInput,
            FollowerPrepareJointMeasurability.assemblePrepareInput,
            FollowerPrepareJointMeasurability.prepareInputRow,
            FollowerPrepareJointMeasurability.prepareInputTime, rowValue, hin]
      have hcodePrep : preparedCodeOnCursor (rate := rate) hcursor i x =
          Sum.inr (fields.1, (fields.2.1,
            (preparedOutput.2.2.1, preparedOutput.2.2.2))) := by
        unfold preparedCodeOnCursor
        rw [dite_eq_right hnot]
        simp only [preparedCodeOnDeclared]
        rfl
      have hdecoded := decode_preparedCodeOnCursor
        (rate := rate) hcursor i source (.declared row activation configuration) hstate ownY
      rw [hcodePrep] at hdecoded
      simp only [ActualInitializationPreparationMeasurability.decodePreparedFollowerCode,
        dite_eq_left hvalid, Option.some.injEq] at hdecoded
      have hprepared :
          ActualInitializationPhysicalStep.prepareFollowerValid rate block
            (localTime block cursor hcursor) source i
            (.declared row activation configuration)
            (follower_ready_of_cursor (rate := rate) hcursor ⟨_, hstate⟩) =
          .declared fields.1 fields.2.1
            (FollowerPrepareJointMeasurability.preparedRoundOfOutput rate i fields.2.1
              preparedData) := by
        simpa [preparedData, rowValue] using hdecoded.symm
      have hpreparedRoundRaw :=
        FollowerVaryingActivationMeasurability.assembledPrepare_reconstructs_prepare
          rate i fields.2.1 fields.2.2 rowValue (localTime block cursor hcursor) hvalid
      have hpreparedRound' :
          FollowerPrepareJointMeasurability.preparedRoundOfOutput rate i fields.2.1
              preparedOutput.2 =
            DeclaredFollowerLocalRound.prepare rate i rowValue fields.2.1
              (localTime block cursor hcursor) hvalid
              (FollowerPrepareJointMeasurability.localConfigurationOfIncoming rate fields.2.2) := by
        simpa [preparedOutput, prepInput,
          FollowerVaryingActivationMeasurability.varyingPreparedOutput,
          FollowerVaryingActivationMeasurability.assembleVaryingPrepareInput,
          FollowerPrepareJointMeasurability.prepareOutputOnInput,
          FollowerPrepareJointMeasurability.assemblePrepareInput] using hpreparedRoundRaw
      have hpreparedRoundData :
          FollowerPrepareJointMeasurability.preparedRoundOfOutput rate i fields.2.1
              preparedData =
            DeclaredFollowerLocalRound.prepare rate i rowValue fields.2.1
              (localTime block cursor hcursor) hvalid
              (FollowerPrepareJointMeasurability.localConfigurationOfIncoming rate fields.2.2) := by
        rw [hpreparedData]
        exact hpreparedRound'
      let carried := DeclaredFollowerObservationMeasurability.observeVaryingCarriedOutputAtComponents
        rate i (fun _ : Unit => fields.2.1) (fun _ => preparedOutput.2.2.2)
        (fun _ => rowValue) (fun _ => localTime block cursor hcursor)
        (fun _ => preparedOutput.2.2.1) (fun _ => ownY) (fun _ => hvalid)
      have hcodeObs : observationCodeOnCursor (rate := rate) hcursor i x =
          Sum.inr (carried ()) := by
        unfold observationCodeOnCursor
        rw [dite_eq_right hnot]
        unfold declaredObservationCodeOnCursor
        rfl
      have hround :=
        DeclaredFollowerObservationMeasurability.observeVaryingCarriedOutputAtComponents_reconstructs
          rate i (fun _ : Unit => fields.2.1) (fun _ => preparedOutput.2.2.2)
          (fun _ => rowValue) (fun _ => localTime block cursor hcursor)
          (fun _ => preparedOutput.2.2.1) (fun _ => ownY) (fun _ => hvalid) ()
      have hconfiguration :
          FollowerPrepareJointMeasurability.localConfigurationOfIncoming rate
              (carried ()).2.2 =
              (DeclaredFollowerLocalRound.observe
              (FollowerPrepareJointMeasurability.preparedRoundOfOutput rate i fields.2.1
                preparedData)
              (FollowerDownMeasurability.feedbackAtGrid p ownY)).configuration := by
        have hc := congrArg DeclaredFollowerLocalRound.ObservedRound.configuration hround
        have hc' : FollowerPrepareJointMeasurability.localConfigurationOfIncoming rate
            (carried ()).2.2 =
              (DeclaredFollowerLocalRound.observe
                ⟨i, rowValue, fields.2.1, localTime block cursor hcursor, hvalid,
                  preparedOutput.2.2.1,
                  FollowerPrepareJointMeasurability.localConfigurationOfIncoming rate
                    preparedOutput.2.2.2⟩
                (FollowerDownMeasurability.feedbackAtGrid p ownY)).configuration := by
          simpa [DeclaredFollowerObservationMeasurability.observedRoundOfCarriedOutput,
            carried] using hc
        rw [show (⟨i, rowValue, fields.2.1, localTime block cursor hcursor, hvalid,
            preparedOutput.2.2.1,
            FollowerPrepareJointMeasurability.localConfigurationOfIncoming rate
              preparedOutput.2.2.2⟩ :
              DeclaredFollowerLocalRound.PreparedRound p rate) =
            FollowerPrepareJointMeasurability.preparedRoundOfOutput rate i fields.2.1
              preparedData by
                dsimp [FollowerPrepareJointMeasurability.preparedRoundOfOutput]] at hc'
        exact hc'
      have hpartial : partialSuccessorCodeOnCursor (rate := rate) hcursor i x =
          Sum.inr (Sum.inr (fields.1, (fields.2.1, (carried ()).2.2))) := by
        unfold partialSuccessorCodeOnCursor
        rw [hcodePrep, hcodeObs]
        rfl
      have hsuccessor : successorCodeOnCursor (rate := rate) hcursor i x =
          Sum.inr (fields.1, (fields.2.1, (carried ()).2.2)) := by
        have h := partialSuccessorCode_eq_inr_successorCode
          (rate := rate) hcursor i x
        rw [hpartial] at h
        exact (Sum.inr.inj h).symm
      have hsuccessor' : successorCodeOnCursor (rate := rate) hcursor i
          (localInputOfComponents (rate := rate) source
            (.declared row activation configuration) hstate ownY) =
          Sum.inr (fields.1, (fields.2.1, (carried ()).2.2)) := by
        simpa [x, localInputOfComponents] using hsuccessor
      have hcode :
          ActualInitializationPhysicalStep.observeFollower rate block
            (localTime block cursor hcursor) source i
            (ActualInitializationPhysicalStep.prepareFollowerValid rate block
              (localTime block cursor hcursor) source i
              (.declared row activation configuration)
              (follower_ready_of_cursor (rate := rate) hcursor ⟨_, hstate⟩)) ownY =
          .ok (localOutcomeOnCursor (rate := rate) hcursor i source
            (.declared row activation configuration) hstate ownY) := by
        unfold localOutcomeOnCursor
        rw [hprepared, hpreparedRoundData, hsuccessor']
        simp only [ActualInitializationRoundMeasurability.followerStateOfCode]
        rw [hconfiguration]
        rw [ActualInitializationPhysicalStep.observeFollower_declared_eq]
        rw [hpreparedRoundData]
        simp [FollowerDownMeasurability.feedbackAtGrid,
          ActualInitializationPhysicalStep.observationOfGrid]
      have hsame := Except.ok.inj (hactual.symm.trans hcode)
      rw [hsame] at hactual
      exact hactual

/-- The local successor is in the actual next clipped-block cursor domain.
This follows from the accepted concrete observer transition above. -/
theorem localOutcome_next_at_cursor {block : Fin (n_boot p)} {cursor : Nat}
    (hcursor : cursor < BootstrapObservedFollower.blockLength p block)
    (i : Fin (p.m - 1)) (source : SourceInput p)
    (follower : FollowerState p rate block)
    (hstate : ActualInitializationRun.followerAtCursor p rate block cursor follower)
    (ownY : Fin (D p + 1)) :
    ActualInitializationRun.followerAtCursor p rate block (cursor + 1)
      (localOutcomeOnCursor (rate := rate) hcursor i source follower hstate ownY).next := by
  exact ActualPostlaunchPhysicalStep.successful_follower_observation_next_cursor
    (localTime block cursor hcursor) source i follower hstate
    (follower_ready_of_cursor (rate := rate) hcursor ⟨follower, hstate⟩)
    ownY (localOutcomeOnCursor (rate := rate) hcursor i source follower hstate ownY)
    (observeFollower_eq_localOutcomeOnCursor (rate := rate) hcursor i source follower
      hstate ownY)

/-- For separately Borel source, cursor-follower, and own-grid inputs, the
three-part code is Borel and the literal observer operation agrees pointwise
with its reconstructed local outcome. -/
theorem measurable_localCode_and_observe_eq_components_comp
    {block : Fin (n_boot p)} {cursor : Nat}
    (hcursor : cursor < BootstrapObservedFollower.blockLength p block)
    (i : Fin (p.m - 1)) {Ω : Type*} [MeasurableSpace Ω]
    (source : Ω → SourceInput p)
    (follower : Ω → CursorFollowerInput (rate := rate) block cursor)
    (ownY : Ω → Fin (D p + 1))
    (hsource : Measurable source) (hfollower : Measurable follower)
    (hownY : Measurable ownY) :
    Measurable (fun ω => localCodeOnCursor (rate := rate) hcursor i
      (source ω, (follower ω, ownY ω))) ∧
    (∀ ω, ActualInitializationPhysicalStep.observeFollower rate block
        (localTime block cursor hcursor) (source ω) i
        (ActualInitializationPhysicalStep.prepareFollowerValid rate block
          (localTime block cursor hcursor) (source ω) i (follower ω).1
          (follower_ready_of_cursor (rate := rate) hcursor (follower ω))) (ownY ω) =
      .ok (localOutcomeOnCursor (rate := rate) hcursor i (source ω)
        (follower ω).1 (follower ω).2 (ownY ω))) := by
  refine ⟨measurable_localCodeOnComponents (rate := rate) hcursor i source follower ownY
    hsource hfollower hownY, ?_⟩
  intro ω
  exact observeFollower_eq_localOutcomeOnCursor (rate := rate) hcursor i (source ω)
    (follower ω).1 (follower ω).2 (ownY ω)

/-- Specialization to an arbitrary actual physical input. With its original
source and retained follower state, and the computed own entry of the actual
physical feedback vector, decoding this local code gives exactly the existing
`M.followerOutcome (M.prepare input) i`, including the already prepared
component. This is a deterministic equality and makes no measurability claim
about the whole physical input or its feedback. -/
theorem decode_localCode_eq_actual_physical_outcome {block : Fin (n_boot p)}
    {cursor : Nat}
    (input : ActualPostlaunchPhysicalStep.PhysicalInput (p := p) (rate := rate)
      block cursor) (i : Fin (p.m - 1)) :
    decodeLocalCode (rate := rate) (block := block) input.source input.time i
      (localCodeOnCursor (rate := rate) input.cursor_lt i
        (localInputOfComponents (rate := rate) input.source
          (input.state.followers i) (input.state.followers_at_cursor i)
          (ActualPostlaunchPhysicalStep.physicalFeedback
            (ActualPostlaunchPhysicalStep.prepare input)
            (PublicDiscreteDraws.followerPlayer p.two_le_m i)))) =
      some (ActualPostlaunchPhysicalStep.followerOutcome
        (ActualPostlaunchPhysicalStep.prepare input) i) := by
  let ownY := ActualPostlaunchPhysicalStep.physicalFeedback
    (ActualPostlaunchPhysicalStep.prepare input)
    (PublicDiscreteDraws.followerPlayer p.two_le_m i)
  have hready := follower_ready_of_cursor (rate := rate) input.cursor_lt
    ⟨input.state.followers i, input.state.followers_at_cursor i⟩
  have hprepared :
      (ActualPostlaunchPhysicalStep.prepare input).followers i =
        ActualInitializationPhysicalStep.prepareFollowerValid rate block input.time
          input.source i (input.state.followers i) hready := by
    rw [(ActualPostlaunchPhysicalStep.prepare input).followers_eq i]
  have hphysical := ActualPostlaunchPhysicalStep.followerOutcome_eq_observe
    (ActualPostlaunchPhysicalStep.prepare input) i
  rw [hprepared] at hphysical
  have hlocal := observeFollower_eq_localOutcomeOnCursor (rate := rate)
    input.cursor_lt i input.source (input.state.followers i)
    (input.state.followers_at_cursor i) ownY
  have houtcome :
      localOutcomeOnCursor (rate := rate) input.cursor_lt i input.source
        (input.state.followers i) (input.state.followers_at_cursor i) ownY =
      ActualPostlaunchPhysicalStep.followerOutcome
        (ActualPostlaunchPhysicalStep.prepare input) i := by
    apply Except.ok.inj
    exact hlocal.symm.trans (by
      simpa [ownY, ActualPostlaunchPhysicalStep.PhysicalInput.time, localTime] using hphysical)
  calc
    decodeLocalCode (rate := rate) (block := block) input.source input.time i
        (localCodeOnCursor (rate := rate) input.cursor_lt i
          (localInputOfComponents (rate := rate) input.source
            (input.state.followers i) (input.state.followers_at_cursor i) ownY)) =
        some (localOutcomeOnCursor (rate := rate) input.cursor_lt i input.source
          (input.state.followers i) (input.state.followers_at_cursor i) ownY) := by
      simpa [localOutcomeOnCursor, ActualPostlaunchPhysicalStep.PhysicalInput.time,
        localTime] using decode_localCodeOnComponents (rate := rate) input.cursor_lt i
          input.source (input.state.followers i) (input.state.followers_at_cursor i) ownY
    _ = some (ActualPostlaunchPhysicalStep.followerOutcome
        (ActualPostlaunchPhysicalStep.prepare input) i) := congrArg some houtcome

end Bandits.Support.ActualPostlaunchFollowerMeasurability

end
