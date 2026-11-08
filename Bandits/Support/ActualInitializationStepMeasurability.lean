/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ActualInitializationPreparationMeasurability
public import Bandits.Support.DeclaredFollowerObservationMeasurability

/-!
# Measurable output assembly for one actual initialization round

This file composes the accepted same-input preparation code with the actual
bootstrap and declared follower observation codes and the coordinator's actual
observation code. The full-input code retains the physical error branch and
every success output needed to reconstruct the existing `RoundResult`.

Sources: `sources/zip4/manuscript/07_public_setup.tex:55-114`,
`sources/zip4/manuscript/appendix_b_communication.tex:94-165`,
`sources/zip4/manuscript/06_interruptions.tex:235-296`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:6-14`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.CompletePublicTable
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.BootstrapPhysicalInput
open Bandits.Support.BootstrapObservedFollower
open Bandits.Support.BootstrapCoordinatorLocalRound
open Bandits.Support.BootstrapCoordinatorRoundMeasurability
open Bandits.Support.ActualBootstrapObservationCode
open Bandits.Support.ReferencePrelaunchFollower
open Bandits.Support.ActualInitializationPhysicalStep
open Bandits.Support.ActualInitializationRoundMeasurability
open Bandits.Support.ActualInitializationPreparationMeasurability
open Bandits.Support.DeclaredFollowerObservationMeasurability
open Bandits.Support.ActiveRoundActions
open Bandits.Support.PublicDiscreteDraws

namespace Bandits.Support.ActualInitializationStepMeasurability

abbrev Parameters := ActualInitializationPreparationMeasurability.Parameters
abbrev RateInput := ActualInitializationPreparationMeasurability.RateInput

variable {p : Parameters} (rate : RateInput p) (block : Fin (n_boot p)) (C_star C_h : ℝ)
abbrev RoundInput (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) (C_star C_h : ℝ) :=
  ActualInitializationPreparationMeasurability.RoundInput p rate block C_star C_h
abbrev ReadyInput (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) (C_star C_h : ℝ) :=
  ActualInitializationPreparationMeasurability.ReadyInput p rate block C_star C_h
abbrev PreparedRoundCode (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) :=
  ActualInitializationPreparationMeasurability.PreparedRoundCode p rate block
abbrev PreparedFollowerCode (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) :=
  ActualInitializationPreparationMeasurability.PreparedFollowerCode p rate block
abbrev PreparedDeclaredCode (p : Parameters) (rate : RateInput p) :=
  ActualInitializationPreparationMeasurability.PreparedDeclaredCode p rate
abbrev DeclaredInputCode (p : Parameters) (rate : RateInput p) :=
  ActualInitializationPreparationMeasurability.DeclaredInputCode p rate
abbrev Activation (p : Parameters) :=
  ActualInitializationPreparationMeasurability.Activation p
abbrev IncomingCode (p : Parameters) (rate : RateInput p) :=
  ActualInitializationPreparationMeasurability.IncomingCode p rate
abbrev FollowerSuccessorCode (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) :=
  ActualInitializationPreparationMeasurability.FollowerCode p rate block
/-- One follower's actual observation output code, tagged by the physical
bootstrap-versus-declared preparation branch. -/
abbrev FollowerObservationCode (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) :=
  ObserveResult p block ⊕
    VaryingObserveCarriedOutput p rate
/-- The complete successful output code keeps the preparation code, the
simultaneous action/feedback pair, the coordinator observation code, and the
whole heterogeneous follower observation-code family. -/
abbrev SuccessfulRoundCode (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) :=
  PreparedRoundCode p rate block ×
    (JointPhysicalCode p ×
      (CoordinatorObservationCode p ×
        (Fin (p.m - 1) → FollowerObservationCode p rate block)))
/-- The total code includes the exact physical `inputNotReady` error token. -/
abbrev ActualRoundOutputCode (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) := Unit ⊕ SuccessfulRoundCode p rate block

private theorem measurable_roundInputTime (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) (C_star C_h : ℝ) :
    Measurable (fun x : RoundInput p rate block C_star C_h => x.time) :=
  measurable_fst.comp (measurable_roundInputCoordinates p rate block C_star C_h)

private theorem measurable_roundInputCoordinatorRow (p : Parameters)
    (rate : RateInput p) (block : Fin (n_boot p)) (C_star C_h : ℝ) :
    Measurable (fun x : RoundInput p rate block C_star C_h => x.coordinatorRow) :=
  measurable_fst.comp <| measurable_snd.comp (measurable_roundInputCoordinates
      p rate block C_star C_h)

private theorem measurable_roundInputCoordinatorIDs (p : Parameters)
    (rate : RateInput p) (block : Fin (n_boot p)) (C_star C_h : ℝ) :
    Measurable (fun x : RoundInput p rate block C_star C_h => x.coordinatorIDs) :=
  measurable_fst.comp <| measurable_snd.comp <| measurable_snd.comp
    (measurable_roundInputCoordinates p rate block C_star C_h)

private theorem measurable_roundInputCoordinator (p : Parameters)
    (rate : RateInput p) (block : Fin (n_boot p)) (C_star C_h : ℝ) :
    Measurable (fun x : RoundInput p rate block C_star C_h => x.coordinator) :=
  measurable_fst.comp <| measurable_snd.comp <| measurable_snd.comp <|
    measurable_snd.comp (measurable_roundInputCoordinates p rate block C_star C_h)

private theorem measurable_roundInputSource (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) (C_star C_h : ℝ) :
    Measurable (fun x : RoundInput p rate block C_star C_h => x.source) :=
  measurable_fst.comp <| measurable_snd.comp <| measurable_snd.comp <|
    measurable_snd.comp <| measurable_snd.comp <| measurable_snd.comp
      (measurable_roundInputCoordinates p rate block C_star C_h)

private theorem measurable_roundInputFollowerCode (p : Parameters)
    (rate : RateInput p) (block : Fin (n_boot p)) (C_star C_h : ℝ)
    (i : Fin (p.m - 1)) :
    Measurable (fun x : RoundInput p rate block C_star C_h => x.followers i) :=
  (measurable_pi_apply i).comp <| measurable_fst.comp <| measurable_snd.comp <|
    measurable_snd.comp <| measurable_snd.comp <| measurable_snd.comp <|
      measurable_roundInputCoordinates p rate block C_star C_h

private theorem measurable_evalCompleteRows (p : Parameters) :
    Measurable (fun z : CompleteRows p × Fin (M p) => z.1 z.2) := by
  exact measurable_from_prod_countable_left fun j => measurable_pi_apply j

private theorem measurable_playerRoundScalarAt_time (p : Parameters)
    (player : Fin p.m) :
    Measurable (fun z : ExtendedPrivateCoordinates p × Fin p.T =>
      playerRoundScalarAt p z.1 player z.2) := by
  apply measurable_from_prod_countable_left
  intro time
  exact measurable_playerRoundScalarAt p player time
/-- The coordinator's actual observe input uses the same supplied row, IDs,
coordinator code, constants, and time as preparation, plus its own physically
derived feedback entry and original player-zero scalar. -/
def coordinatorObserveInputOnReady
    (x : ReadyInput p rate block C_star C_h) :
    CoordinatorObserveInput p C_star C_h :=
  ⟨⟨coordinatorRoundInputOfReady rate block C_star C_h x, rfl⟩,
    coordinatorOriginalRoundScalar rate block C_star C_h x,
    (actualJointPhysicalCodeOnReady rate block C_star C_h x).2 (coordinator p.two_le_m)⟩
/-- The coordinator's output code is the accepted local `observe (prepare ..)`
code, on the very same prepared coordinator and own feedback entry. -/
def coordinatorObservationCodeOnReady
    (x : ReadyInput p rate block C_star C_h) :
    CoordinatorObservationCode p :=
  coordinatorObserveCode p C_star C_h (coordinatorObserveInputOnReady rate block C_star C_h x)

private theorem measurable_coordinatorObserveInputOnReady :
    Measurable (coordinatorObserveInputOnReady rate block C_star C_h) := by
  let hcoe : Measurable (fun x : ReadyInput p rate block C_star C_h =>
        (x.1 : RoundInput p rate block C_star C_h)) := measurable_subtype_coe
  have hrow := (measurable_roundInputCoordinatorRow p rate block C_star C_h).comp hcoe
  have hids := (measurable_roundInputCoordinatorIDs p rate block C_star C_h).comp hcoe
  have hlocal := (measurable_roundInputCoordinator p rate block C_star C_h).comp hcoe
  have htime := (measurable_roundInputTime p rate block C_star C_h).comp hcoe
  have hbase : Measurable (fun x : ReadyInput p rate block C_star C_h =>
      ((x.1.coordinatorRow, x.1.coordinatorIDs), (C_star, C_h))) := by
    exact (hrow.prodMk hids).prodMk (measurable_const.prodMk measurable_const)
  have hroundCoordinates : Measurable (fun x : ReadyInput p rate block C_star C_h =>
        coordinatorRoundInputCoordinates p (coordinatorRoundInputOfReady
            rate block C_star C_h x)) :=
    hbase.prodMk (hlocal.prodMk htime)
  have hround : Measurable (fun x : ReadyInput p rate block C_star C_h =>
        coordinatorRoundInputOfReady
          rate block C_star C_h x) := (measurable_comap_iff).2 hroundCoordinates
  have hfixed : Measurable (fun x : ReadyInput p rate block C_star C_h =>
      (⟨coordinatorRoundInputOfReady rate block C_star C_h x, rfl⟩ :
        CoordinatorFixedRoundInput p C_star C_h)) :=
    (measurable_comap_iff).2 hround
  have hsource := (measurable_roundInputSource p rate block C_star C_h).comp hcoe
  have hprivate := (measurable_sourcePrivate p).comp hsource
  have hscalar : Measurable (coordinatorOriginalRoundScalar rate block C_star C_h) := by
    exact (measurable_playerRoundScalarAt_time p
      (coordinator p.two_le_m)).comp (hprivate.prodMk htime)
  have hjoint :=
    (measurable_actualJointPhysicalCodeOnReady rate block C_star C_h)
  have hfeedback : Measurable (fun x : ReadyInput p rate block C_star C_h =>
      (actualJointPhysicalCodeOnReady rate block C_star C_h x).2 (coordinator p.two_le_m)) :=
    (measurable_pi_apply (coordinator p.two_le_m)).comp (measurable_snd.comp hjoint)
  exact (measurable_comap_iff).2 <| hfixed.prodMk (hscalar.prodMk hfeedback)
/-- The same-input coordinator code is measurable on the ready subtype. -/
theorem measurable_coordinatorObservationCodeOnReady :
    Measurable (coordinatorObservationCodeOnReady rate block C_star C_h) :=
  (measurable_coordinatorObserveCode p C_star C_h).comp
      (measurable_coordinatorObserveInputOnReady rate block C_star C_h)
/-- Decoding this coordinator code returns the observation of this very
physical prepared coordinator with its own action and feedback entry. -/
theorem reconstruct_coordinatorObservationCodeOnReady
    (x : ReadyInput p rate block C_star C_h) :
    reconstructCoordinatorObservationCode
      p C_star C_h (coordinatorObserveInputOnReady rate block C_star C_h x).fixed
        (coordinatorObservationCodeOnReady rate block C_star C_h x) =
      some (BootstrapCoordinatorLocalRound.observe (actualPreparedRoundOnReady
          rate block C_star C_h x).coordinator
        ((actualJointPhysicalCodeOnReady rate block C_star C_h x).2 (coordinator p.two_le_m))) := by
  have hprepared :
      coordinatorPreparedRound p (coordinatorRoundInputOfReady rate block C_star C_h x)
        (coordinatorOriginalRoundScalar rate block C_star C_h x) =
      (actualPreparedRoundOnReady rate block C_star C_h x).coordinator := by
    rw [coordinatorPreparedRoundOnReady_eq_physicalPrepare]
    rfl
  simpa [coordinatorObservationCodeOnReady, coordinatorObserveInputOnReady,
    coordinatorObserveResult, hprepared] using
    (reconstruct_coordinatorObserveCode
      p C_star C_h (coordinatorObserveInputOnReady rate block C_star C_h x))
/-- The output code projection for a coordinator keeps the prepared arm,
updated local-state code, updated monitor counters/tag, and launch trigger. -/
abbrev CoordinatorSuccessorCode (p : Parameters) :=
  Fin p.K × (CoordinatorStateCode p ×
    (MonitorCode p × Option (Fin p.T)))

def coordinatorSuccessorCode {p : Parameters}
    (code : CoordinatorObservationCode p) :
    CoordinatorSuccessorCode p :=
  (code.arm, (code.coordinator, (code.monitor, code.trigger)))

theorem measurable_coordinatorSuccessorCode {p : Parameters} :
    Measurable (@coordinatorSuccessorCode p) := by
  have hfields : Measurable (coordinatorObservationCodeFields p) :=
    comap_measurable _
  have harm : Measurable (fun code :
      CoordinatorObservationCode p =>
      (coordinatorObservationCodeFields p code).1) :=
    measurable_fst.comp hfields
  have hstate : Measurable (fun code :
      CoordinatorObservationCode p =>
      code.coordinator) := by
    change Measurable (fun code =>
      (coordinatorObservationCodeFields p code).2.2.2.1)
    exact measurable_fst.comp (measurable_snd.comp (measurable_snd.comp
      (measurable_snd.comp hfields)))
  have hmonitor : Measurable (fun code :
      CoordinatorObservationCode p =>
      code.monitor) := by
    change Measurable (fun code =>
      (coordinatorObservationCodeFields p code).2.2.2.2.1)
    exact measurable_fst.comp (measurable_snd.comp (measurable_snd.comp
      (measurable_snd.comp (measurable_snd.comp hfields))))
  have htrigger : Measurable (fun code :
      CoordinatorObservationCode p =>
      code.trigger) := by
    change Measurable (fun code =>
      (coordinatorObservationCodeFields p code).2.2.2.2.2)
    exact measurable_snd.comp (measurable_snd.comp (measurable_snd.comp
      (measurable_snd.comp (measurable_snd.comp hfields))))
  unfold coordinatorSuccessorCode
  exact harm.prodMk (hstate.prodMk (hmonitor.prodMk htrigger))
/-- Decode one follower successor from the existing prepared local code and
that same follower's observation code. Rejected bootstrap observations and
branch/tag mismatches have no successor. -/
abbrev PartialFollowerSuccessorCode (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) := Unit ⊕ FollowerSuccessorCode p rate block

def followerSuccessorCodeFromOutput
    (z : PreparedFollowerCode p rate block × FollowerObservationCode p rate block) :
    PartialFollowerSuccessorCode p rate block := by
  classical
  rcases z with ⟨prepared, observed⟩
  cases prepared with
  | inl bootstrap =>
      cases observed with
      | inl result =>
          cases result with
          | rejected _ => exact Sum.inl ()
          | accepted state => exact Sum.inr (Sum.inl state)
      | inr _ => exact Sum.inl ()
  | inr declared =>
      cases observed with
      | inl _ => exact Sum.inl ()
      | inr carried =>
          exact Sum.inr (Sum.inr (declared.1, (carried.1, carried.2.2)))

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

private theorem measurable_varyingObservationData {p : Parameters} (rate : RateInput p) :
    Measurable (fun output : VaryingObserveCarriedOutput p rate => output.2) := by
  apply measurable_of_sigma_sections_local
  intro activation
  change Measurable (fun x : Fin p.K ×
    FollowerPrepareJointMeasurability.IncomingConfiguration p rate => x)
  exact measurable_id

private theorem measurable_varyingObservationActivation {p : Parameters}
    (rate : RateInput p) :
    Measurable (fun output : VaryingObserveCarriedOutput p rate => output.1) := by
  apply measurable_of_sigma_sections_local
  intro activation
  exact measurable_const

private def followerSuccessorCodeBootstrapBootstrap
    (z : PreparedBootstrapCode p block × ObserveResult p block) :
    PartialFollowerSuccessorCode p rate block := by
  cases z.2 with
  | rejected _ => exact Sum.inl ()
  | accepted state => exact Sum.inr (Sum.inl state)

theorem measurable_followerSuccessorCodeFromOutput :
    Measurable (followerSuccessorCodeFromOutput rate block) := by
  let A := PreparedBootstrapCode p block
  let B := PreparedDeclaredCode p rate
  let C := ObserveResult p block
  let D := VaryingObserveCarriedOutput p rate
  let distribute := MeasurableEquiv.sumProdSum A B C D
  have hAA : Measurable (followerSuccessorCodeBootstrapBootstrap rate block) :=
    measurable_of_countable _
  have hAD : Measurable (fun _ : PreparedBootstrapCode p block ×
      VaryingObserveCarriedOutput p rate =>
        (Sum.inl () : PartialFollowerSuccessorCode p rate block)) := measurable_const
  have hBC : Measurable (fun _ : PreparedDeclaredCode p rate ×
      ObserveResult p block =>
        (Sum.inl () : PartialFollowerSuccessorCode p rate block)) := measurable_const
  have hDD : Measurable (fun z : PreparedDeclaredCode p rate ×
      VaryingObserveCarriedOutput p rate =>
        (Sum.inr (Sum.inr (z.1.1, (z.2.1, z.2.2.2))) :
          PartialFollowerSuccessorCode p rate block)) := by
    have hprepared : Measurable (fun z : PreparedDeclaredCode p rate × D => z.1) :=
      measurable_fst
    have hrow : Measurable (fun z : PreparedDeclaredCode p rate × D => z.1.1) :=
      measurable_fst.comp hprepared
    have hdata : Measurable (fun z : PreparedDeclaredCode p rate × D => z.2) :=
      measurable_snd
    have hactivation := (measurable_varyingObservationActivation rate).comp hdata
    have hincoming : Measurable (fun z : PreparedDeclaredCode p rate × D =>
        z.2.2.2) :=
      (measurable_snd.comp (measurable_varyingObservationData rate)).comp measurable_snd
    exact measurable_inr.comp <| measurable_inr.comp <|
      hrow.prodMk (hactivation.prodMk hincoming)
  have hbranches : Measurable
      (Sum.elim (Sum.elim (followerSuccessorCodeBootstrapBootstrap rate block)
        (fun _ => Sum.inl ()))
        (Sum.elim (fun _ => Sum.inl ()) (fun z : PreparedDeclaredCode p rate × D =>
            Sum.inr (Sum.inr (z.1.1, (z.2.1, z.2.2.2)))))) :=
    Measurable.sumElim (Measurable.sumElim hAA hAD)
      (Measurable.sumElim hBC hDD)
  have hfactor : followerSuccessorCodeFromOutput rate block =
      (Sum.elim (Sum.elim (followerSuccessorCodeBootstrapBootstrap rate block)
        (fun _ => Sum.inl ()))
        (Sum.elim (fun _ => Sum.inl ()) (fun z : PreparedDeclaredCode p rate × D =>
            Sum.inr (Sum.inr (z.1.1, (z.2.1, z.2.2.2))))) ∘ distribute) := by
    funext z
    rcases z with ⟨prepared, observed⟩
    cases prepared with
    | inl bootstrap =>
        cases observed with
        | inl result => cases result <;> rfl
        | inr _ => rfl
    | inr declared =>
        cases observed with
        | inl _ => rfl
        | inr _ => rfl
  rw [hfactor]
  exact hbranches.comp distribute.measurable_toFun

abbrev FollowerBootstrapBranch (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) (C_star C_h : ℝ) (i : Fin (p.m - 1)) :=
  followerBootstrapCodeSet rate block C_star C_h i

abbrev FollowerDeclaredBranch (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) (C_star C_h : ℝ) (i : Fin (p.m - 1)) :=
  ↥((FollowerBootstrapBranch p rate block C_star C_h i)ᶜ)
/-- The bootstrap observation uses this follower's prepared startup state,
the original source IDs, entire row family and private coordinates, and this
round's own denominator-D feedback value. -/
def followerBootstrapObservationCodeOnBootstrap
    (i : Fin (p.m - 1))
    (x : FollowerBootstrapBranch p rate block C_star C_h i) :
    ObserveResult p block :=
  BootstrapObservedFollower.observe p block (followerStartupCodeOnBootstrap
      rate block C_star C_h i x)
    (sourceIDs p x.1.1.source)
    (sourceRows p x.1.1.source) x.1.1.time
    (observationOfGrid p
      ((actualJointPhysicalCodeOnReady rate block C_star C_h x.1).2 (followerPlayer p.two_le_m i)))

private theorem measurable_followerBootstrapObserverOnBootstrap
    (i : Fin (p.m - 1)) :
    Measurable (followerBootstrapObservationCodeOnBootstrap rate block C_star C_h i) := by
  let state : FollowerBootstrapBranch p rate block C_star C_h i →
      ActualBootstrapObservationCode.StartupCode p block :=
    followerStartupCodeOnBootstrap rate block C_star C_h i
  have hreadyCoe : Measurable (fun x : FollowerBootstrapBranch p rate block C_star C_h i => x.1) :=
    measurable_subtype_coe
  have hcoe : Measurable (fun x : FollowerBootstrapBranch p rate block C_star C_h i =>
      (x.1.1 : RoundInput p rate block C_star C_h)) :=
    measurable_subtype_coe.comp hreadyCoe
  have hraw : Measurable (fun x : FollowerBootstrapBranch p rate block C_star C_h i =>
      x.1.1.followers i) :=
    (measurable_roundInputFollowerCode p rate block C_star C_h i).comp hcoe
  have hrange : Measurable (fun x : FollowerBootstrapBranch p rate block C_star C_h i =>
      (⟨x.1.1.followers i, x.2⟩ : Set.range
        (Sum.inl : ActualBootstrapObservationCode.StartupCode p block →
          ActualInitializationPreparationMeasurability.FollowerCode p rate block))) := by
    exact hraw.codRestrict fun x => x.2
  have hstate : Measurable state := by
    exact MeasurableEquiv.Set.rangeInl.measurable_toFun.comp hrange
  have hsource := (measurable_roundInputSource p rate block C_star C_h).comp hcoe
  have hids := (measurable_sourceIDs p).comp hsource
  have hrows := (measurable_sourceRows p).comp hsource
  have hprivate := (measurable_sourcePrivate p).comp hsource
  have htime := (measurable_roundInputTime p rate block C_star C_h).comp hcoe
  have hjoint :=
    (measurable_actualJointPhysicalCodeOnReady rate block C_star C_h).comp hreadyCoe
  have hfeedback : Measurable (fun x : FollowerBootstrapBranch p rate block C_star C_h i =>
      (actualJointPhysicalCodeOnReady rate block C_star C_h x.1).2 (followerPlayer p.two_le_m i)) :=
    (measurable_pi_apply (followerPlayer p.two_le_m i)).comp (measurable_snd.comp hjoint)
  have hObservation : Measurable (fun x : FollowerBootstrapBranch p rate block C_star C_h i =>
      observationOfGrid p
        ((actualJointPhysicalCodeOnReady rate block C_star C_h x.1).2
          (followerPlayer p.two_le_m i))) := by
    exact (measurable_of_countable (fun y : Fin (D p + 1) => observationOfGrid p y)).comp
        hfeedback
  exact measurable_observe_of_components (p := p) (s := block)
    (fun x : FollowerBootstrapBranch p rate block C_star C_h i =>
      sourceIDs p x.1.1.source)
    (fun x => sourceRows p x.1.1.source)
    (fun x => sourcePrivate p x.1.1.source)
    (followerStartupCodeOnBootstrap rate block C_star C_h i) (fun x => x.1.1.time)
    (fun x => observationOfGrid p
      ((actualJointPhysicalCodeOnReady rate block C_star C_h x.1).2 (followerPlayer p.two_le_m i)))
    hids hrows hprivate hstate htime hObservation

private theorem measurable_followerBootstrapObservationCodeOnBootstrap
    (i : Fin (p.m - 1)) :
    Measurable (fun x : FollowerBootstrapBranch p rate block C_star C_h i =>
      (Sum.inl (followerBootstrapObservationCodeOnBootstrap rate block C_star C_h i x) :
        FollowerObservationCode p rate block)) := by
  exact measurable_inl.comp
    (measurable_followerBootstrapObserverOnBootstrap rate block C_star C_h i)

def followerDeclaredCodeOnReady
    (i : Fin (p.m - 1))
    (x : FollowerDeclaredBranch p rate block C_star C_h i) : DeclaredInputCode p rate :=
  ActualInitializationPreparationMeasurability.followerDeclaredCodeOnReady rate block C_star C_h i x

private theorem measurable_followerDeclaredCodeOnReady
    (i : Fin (p.m - 1)) :
    Measurable (followerDeclaredCodeOnReady rate block C_star C_h i) := by
  have hcoe : Measurable (fun x : FollowerDeclaredBranch p rate block C_star C_h i =>
      (x.1.1 : RoundInput p rate block C_star C_h)) :=
    measurable_subtype_coe.comp measurable_subtype_coe
  have hraw : Measurable (fun x : FollowerDeclaredBranch p rate block C_star C_h i =>
      x.1.1.followers i) :=
    (measurable_roundInputFollowerCode p rate block C_star C_h i).comp hcoe
  have hmem (x : FollowerDeclaredBranch p rate block C_star C_h i) :
      x.1.1.followers i ∈ Set.range
        (Sum.inr : DeclaredInputCode p rate →
          ActualInitializationPreparationMeasurability.FollowerCode p rate block) := by
    cases hcode : x.1.1.followers i with
    | inl startup => exact (x.2 ⟨startup, hcode.symm⟩).elim
    | inr fields => exact ⟨fields, rfl⟩
  have hrange : Measurable (fun x : FollowerDeclaredBranch p rate block C_star C_h i =>
      (⟨x.1.1.followers i, hmem x⟩ : Set.range
        (Sum.inr : DeclaredInputCode p rate →
          ActualInitializationPreparationMeasurability.FollowerCode p rate block))) :=
    hraw.codRestrict hmem
  exact MeasurableEquiv.Set.rangeInr.measurable_toFun.comp hrange

def preparedDeclaredCodeOnDeclared
    (i : Fin (p.m - 1))
    (x : FollowerDeclaredBranch p rate block C_star C_h i) : PreparedDeclaredCode p rate := by
  classical
  have hbranch : (MeasurableEquiv.sumCompl (s := FollowerBootstrapBranch p rate block C_star C_h i)
      (measurableSet_followerBootstrapCodeSet rate block C_star C_h i)).symm x = Sum.inr x := by
    change (Equiv.sumCompl
      (fun y => y ∈ FollowerBootstrapBranch p rate block C_star C_h i)).symm x = Sum.inr x
    exact Equiv.sumCompl_symm_apply_neg x
  have hmem :
      preparedFollowerCodeOnReady rate block C_star C_h i x.1 ∈ Set.range
            (Sum.inr : PreparedDeclaredCode p rate → PreparedFollowerCode p rate block) := by
    rw [preparedFollowerCodeOnReady, hbranch]
    simp [followerPreparedCodeOnDeclared]
  exact Equiv.Set.rangeInr
    (PreparedBootstrapCode p block) (PreparedDeclaredCode p rate)
      ⟨preparedFollowerCodeOnReady rate block C_star C_h i x.1, hmem⟩

private theorem preparedFollowerCodeOnDeclared_eq_ready
    (i : Fin (p.m - 1)) (x : FollowerDeclaredBranch p rate block C_star C_h i) :
    followerPreparedCodeOnDeclared rate block C_star C_h i x =
      preparedFollowerCodeOnReady rate block C_star C_h i x.1 := by
  classical
  have hbranch : (MeasurableEquiv.sumCompl (s := FollowerBootstrapBranch p rate block C_star C_h i)
      (measurableSet_followerBootstrapCodeSet rate block C_star C_h i)).symm x = Sum.inr x := by
    change (Equiv.sumCompl
      (fun y => y ∈ FollowerBootstrapBranch p rate block C_star C_h i)).symm x = Sum.inr x
    exact Equiv.sumCompl_symm_apply_neg x
  rw [preparedFollowerCodeOnReady, hbranch]
  simp [followerPreparedCodeOnDeclared]

private theorem measurable_preparedDeclaredCodeOnDeclared
    (i : Fin (p.m - 1)) :
    Measurable (preparedDeclaredCodeOnDeclared rate block C_star C_h i) := by
  have hreadyCoe : Measurable (fun x : FollowerDeclaredBranch p rate block C_star C_h i => x.1) :=
    measurable_subtype_coe
  have hready :=
    (measurable_preparedFollowerCodeOnReady rate block C_star C_h i).comp hreadyCoe
  have hmem (x : FollowerDeclaredBranch p rate block C_star C_h i) :
      preparedFollowerCodeOnReady rate block C_star C_h i x.1 ∈ Set.range
            (Sum.inr : PreparedDeclaredCode p rate → PreparedFollowerCode p rate block) := by
    rw [← preparedFollowerCodeOnDeclared_eq_ready rate block C_star C_h i x]
    simp [followerPreparedCodeOnDeclared]
  have hrange : Measurable (fun x : FollowerDeclaredBranch p rate block C_star C_h i =>
      (⟨preparedFollowerCodeOnReady rate block C_star C_h i x.1, hmem x⟩ : Set.range
          (Sum.inr : PreparedDeclaredCode p rate → PreparedFollowerCode p rate block))) :=
    hready.codRestrict hmem
  unfold preparedDeclaredCodeOnDeclared
  exact MeasurableEquiv.Set.rangeInr.measurable_toFun.comp hrange
/-- The declared observation consumes this follower's own prepared row,
activation, ordinary/dagger carry, prepared arm and physically derived grid
feedback. Its activation bound is extracted from the same ready input. -/
def followerDeclaredObservationCodeOnDeclared
    (i : Fin (p.m - 1))
    (x : FollowerDeclaredBranch p rate block C_star C_h i) :
    VaryingObserveCarriedOutput p rate := by
  let fields := followerDeclaredCodeOnReady rate block C_star C_h i x
  let prepared := preparedDeclaredCodeOnDeclared rate block C_star C_h i x
  let input := x.1.1
  let hvalid := declaredActivation_le_time_of_ready rate block C_star C_h i x.1 fields
    (followerCode_eq_inr_of_declared rate block C_star C_h i x)
  exact observeVaryingCarriedOutputAtComponents
    rate i (fun _ : FollowerDeclaredBranch p rate block C_star C_h i => fields.2.1)
    (fun _ : FollowerDeclaredBranch p rate block C_star C_h i => prepared.2.2.2)
    (fun _ : FollowerDeclaredBranch p rate block C_star C_h i =>
      sourceRows p input.source fields.1)
    (fun _ : FollowerDeclaredBranch p rate block C_star C_h i => input.time)
    (fun _ : FollowerDeclaredBranch p rate block C_star C_h i => prepared.2.2.1)
    (fun _ : FollowerDeclaredBranch p rate block C_star C_h i =>
      (actualJointPhysicalCodeOnReady
      rate block C_star C_h x.1).2 (followerPlayer p.two_le_m i))
    (fun _ : FollowerDeclaredBranch p rate block C_star C_h i => hvalid) x

private theorem measurable_followerDeclaredObservationCodeOnDeclared
    (i : Fin (p.m - 1)) :
    Measurable (followerDeclaredObservationCodeOnDeclared rate block C_star C_h i) := by
  let fields := followerDeclaredCodeOnReady rate block C_star C_h i
  let prepared := preparedDeclaredCodeOnDeclared rate block C_star C_h i
  let input := fun x : FollowerDeclaredBranch p rate block C_star C_h i => x.1.1
  have hfields := measurable_followerDeclaredCodeOnReady rate block C_star C_h i
  have hprepared := measurable_preparedDeclaredCodeOnDeclared rate block C_star C_h i
  have hactivation : Measurable (fun x : FollowerDeclaredBranch p rate block C_star C_h i =>
      (fields x).2.1) := measurable_fst.comp (measurable_snd.comp hfields)
  have hincoming : Measurable (fun x : FollowerDeclaredBranch p rate block C_star C_h i =>
      (prepared x).2.2.2) :=
    measurable_snd.comp (measurable_snd.comp (measurable_snd.comp hprepared))
  have hrowIndex : Measurable (fun x : FollowerDeclaredBranch p rate block C_star C_h i =>
      (fields x).1) := measurable_fst.comp hfields
  have hsource : Measurable (fun x : FollowerDeclaredBranch p rate block C_star C_h i =>
      (input x).source) :=
    (measurable_roundInputSource p rate block C_star C_h).comp
      (measurable_subtype_coe.comp measurable_subtype_coe)
  have hrows := (measurable_sourceRows p).comp hsource
  have hrow : Measurable (fun x : FollowerDeclaredBranch p rate block C_star C_h i =>
      sourceRows p (input x).source (fields x).1) :=
    (measurable_evalCompleteRows p).comp (hrows.prodMk hrowIndex)
  have htime : Measurable (fun x : FollowerDeclaredBranch p rate block C_star C_h i =>
      (input x).time) :=
    (measurable_roundInputTime p rate block C_star C_h).comp
      (measurable_subtype_coe.comp measurable_subtype_coe)
  have hreadyCoe : Measurable (fun x : FollowerDeclaredBranch p rate block C_star C_h i => x.1) :=
    measurable_subtype_coe
  have hjoint :=
    (measurable_actualJointPhysicalCodeOnReady rate block C_star C_h).comp hreadyCoe
  have hfeedback : Measurable (fun x : FollowerDeclaredBranch p rate block C_star C_h i =>
      (actualJointPhysicalCodeOnReady rate block C_star C_h x.1).2 (followerPlayer p.two_le_m i)) :=
    (measurable_pi_apply (followerPlayer p.two_le_m i)).comp (measurable_snd.comp hjoint)
  have harm : Measurable (fun x : FollowerDeclaredBranch p rate block C_star C_h i =>
      (prepared x).2.2.1) :=
    measurable_fst.comp (measurable_snd.comp (measurable_snd.comp hprepared))
  have hvalid (x : FollowerDeclaredBranch p rate block C_star C_h i) :
      (fields x).2.1.val ≤ (input x).time.val + 1 :=
    declaredActivation_le_time_of_ready rate block C_star C_h i x.1 (fields x)
      (followerCode_eq_inr_of_declared rate block C_star C_h i x)
  change Measurable
    (observeVaryingCarriedOutputAtComponents
      rate i (fun x => (fields x).2.1) (fun x => (prepared x).2.2.2)
      (fun x => sourceRows p (input x).source
        (fields x).1) (fun x => (input x).time) (fun x => (prepared x).2.2.1)
      (fun x => (actualJointPhysicalCodeOnReady rate block C_star C_h x.1).2
          (followerPlayer p.two_le_m i)) hvalid)
  exact measurable_observeVaryingCarriedOutputAtComponents
    rate i (fun x => (fields x).2.1) (fun x => (prepared x).2.2.2)
    (fun x => sourceRows p (input x).source
      (fields x).1) (fun x => (input x).time) (fun x => (prepared x).2.2.1)
    (fun x => (actualJointPhysicalCodeOnReady rate block C_star C_h x.1).2
        (followerPlayer p.two_le_m i))
    hactivation hincoming hrow htime harm hfeedback hvalid
/-- The full per-follower observation code is assembled by the actual
bootstrap/declaration tag of this follower's own input state. -/
def followerObservationCodeOnReady (i : Fin (p.m - 1))
    (x : ReadyInput p rate block C_star C_h) : FollowerObservationCode p rate block := by
  classical
  exact Sum.elim (fun x => Sum.inl (followerBootstrapObservationCodeOnBootstrap
      rate block C_star C_h i x))
    (fun x => Sum.inr (followerDeclaredObservationCodeOnDeclared rate block C_star C_h i x))
    ((MeasurableEquiv.sumCompl (s := FollowerBootstrapBranch p rate block C_star C_h i)
      (measurableSet_followerBootstrapCodeSet rate block C_star C_h i)).symm x)
/-- Ready bootstrap observations always return their accepted startup
continuation. The code is the same `observe` call used by the physical step. -/
theorem followerBootstrapObservationCodeOnBootstrap_accepted
    (i : Fin (p.m - 1)) (x : FollowerBootstrapBranch p rate block C_star C_h i) :
    ∃ next, followerBootstrapObservationCodeOnBootstrap rate block C_star C_h i x =
      .accepted next := by
  have hcursor := readyFollowerCursorProof rate block C_star C_h i x.1
  cases hcode : x.1.1.followers i with
  | inl startup =>
      have hcursor' : followerAtNextCursor (p := p) (rate := rate) x.1.1.time
          (FollowerState.bootstrap (rate := rate) startup) := by
        simpa [followerStateOfCode, hcode]
          using hcursor
      rcases hcursor' with ⟨htime, hopen, hnext⟩
      let next := observeOne p block startup
        (sourceIDs p x.1.1.source)
        (sourceRows p x.1.1.source)
        x.1.1.time
        (observationOfGrid p
          ((actualJointPhysicalCodeOnReady rate block C_star C_h x.1).2
            (followerPlayer p.two_le_m i))) htime hopen hnext
      have hobserve : BootstrapObservedFollower.observe p block startup
          (sourceIDs p x.1.1.source)
          (sourceRows p x.1.1.source) x.1.1.time
          (observationOfGrid p
            ((actualJointPhysicalCodeOnReady rate block C_star C_h x.1).2
              (followerPlayer p.two_le_m i))) = .accepted next := by
        exact observe_accepted_processed p block startup
          (sourceIDs p x.1.1.source)
          (sourceRows p x.1.1.source) x.1.1.time
          (observationOfGrid p
            ((actualJointPhysicalCodeOnReady rate block C_star C_h x.1).2
              (followerPlayer p.two_le_m i))) htime hopen hnext
      refine ⟨next, ?_⟩
      simp [followerBootstrapObservationCodeOnBootstrap,
        followerStartupCodeOnBootstrap,
        hcode, hobserve]
  | inr fields =>
      have hmem : x.1.1.followers i ∈ Set.range Sum.inl := x.2
      rw [hcode] at hmem
      simp at hmem
/-- The declared output's dependent-union decoder reconstructs the exact
ordinary/dagger local observation using this follower's own activation,
prepared carry, row, arm, and feedback. -/
theorem followerDeclaredObservationCodeOnDeclared_reconstructs
    (i : Fin (p.m - 1)) (x : FollowerDeclaredBranch p rate block C_star C_h i) :
    observedRoundOfCarriedOutput
        (followerDeclaredObservationCodeOnDeclared rate block C_star C_h i x).2 =
      DeclaredFollowerLocalRound.observe
        ⟨i,
          sourceRows p x.1.1.source (followerDeclaredCodeOnReady rate block C_star C_h i x).1,
          (followerDeclaredCodeOnReady rate block C_star C_h i x).2.1,
          x.1.1.time,
          declaredActivation_le_time_of_ready rate block C_star C_h i x.1
            (followerDeclaredCodeOnReady rate block C_star C_h i x)
            (followerCode_eq_inr_of_declared rate block C_star C_h i x),
          (preparedDeclaredCodeOnDeclared rate block C_star C_h i x).2.2.1,
          FollowerPrepareJointMeasurability.localConfigurationOfIncoming rate
            (preparedDeclaredCodeOnDeclared rate block C_star C_h i x).2.2.2⟩
        (FollowerDownMeasurability.feedbackAtGrid p
          ((actualJointPhysicalCodeOnReady rate block C_star C_h x.1).2
            (followerPlayer p.two_le_m i))) := by
  let fields := followerDeclaredCodeOnReady rate block C_star C_h i x
  let prepared := preparedDeclaredCodeOnDeclared rate block C_star C_h i x
  let input := x.1.1
  let hvalid := declaredActivation_le_time_of_ready rate block C_star C_h i x.1 fields
    (followerCode_eq_inr_of_declared rate block C_star C_h i x)
  simpa [followerDeclaredObservationCodeOnDeclared, fields, prepared, input, hvalid] using
    (observeVaryingCarriedOutputAtComponents_reconstructs
      rate i (fun _ : FollowerDeclaredBranch p rate block C_star C_h i => fields.2.1)
      (fun _ => prepared.2.2.2)
      (fun _ => sourceRows p input.source fields.1)
      (fun _ => input.time) (fun _ => prepared.2.2.1)
      (fun _ => (actualJointPhysicalCodeOnReady rate block C_star C_h x.1).2
          (followerPlayer p.two_le_m i))
      (fun _ => hvalid) x)
/-- Each heterogeneous follower output-code producer is measurable on the
same ready input as its preparation and physical feedback. -/
theorem measurable_followerObservationCodeOnReady
    (i : Fin (p.m - 1)) :
    Measurable (followerObservationCodeOnReady rate block C_star C_h i) := by
  classical
  exact (Measurable.sumElim
    (measurable_followerBootstrapObservationCodeOnBootstrap rate block C_star C_h i)
    (measurable_inr.comp
      (measurable_followerDeclaredObservationCodeOnDeclared rate block C_star C_h i))).comp
      (MeasurableEquiv.sumCompl (s := FollowerBootstrapBranch p rate block C_star C_h i)
        (measurableSet_followerBootstrapCodeSet rate block C_star C_h i)).symm.measurable_toFun
/-- Assemble the exact successful output codes from their separately proved
preparation, physical-feedback, coordinator, and heterogeneous follower
producers. -/
def successfulRoundCodeOnReady
    (x : ReadyInput p rate block C_star C_h) : SuccessfulRoundCode p rate block :=
  (preparedRoundCodeOnReady rate block C_star C_h x, (actualJointPhysicalCodeOnReady
      rate block C_star C_h x,
      (coordinatorObservationCodeOnReady rate block C_star C_h x,
        fun i => followerObservationCodeOnReady rate block C_star C_h i x)))
/-- Measurability of all success-code coordinates is derived from their local
producers, without assuming completed-operation measurability. -/
theorem measurable_successfulRoundCodeOnReady :
    Measurable (successfulRoundCodeOnReady rate block C_star C_h) := by
  have hfollower : Measurable (fun x : ReadyInput p rate block C_star C_h =>
        fun i => followerObservationCodeOnReady rate block C_star C_h i x) := by
    apply measurable_pi_iff.mpr
    intro i
    exact measurable_followerObservationCodeOnReady rate block C_star C_h i
  exact (measurable_preparedRoundCodeOnReady rate block C_star C_h).prodMk <|
    (measurable_actualJointPhysicalCodeOnReady rate block C_star C_h).prodMk <|
      (measurable_coordinatorObservationCodeOnReady rate block C_star C_h).prodMk hfollower
/-- Project one follower's next local-state code from the same successful
preparation and observation carriers. -/
def followerSuccessorCodeFromSuccessfulRoundCode
    (code : SuccessfulRoundCode p rate block) (i : Fin (p.m - 1)) :
    PartialFollowerSuccessorCode p rate block :=
  followerSuccessorCodeFromOutput rate block
    (code.1.2 i, code.2.2.2 i)

theorem measurable_followerSuccessorCodeFromSuccessfulRoundCode (i : Fin (p.m - 1)) :
    Measurable (fun code => followerSuccessorCodeFromSuccessfulRoundCode rate block code i) := by
  have hprepared : Measurable (fun code : SuccessfulRoundCode p rate block =>
      code.1.2 i) :=
    (measurable_pi_apply i).comp (measurable_snd.comp measurable_fst)
  have hobservation : Measurable (fun code : SuccessfulRoundCode p rate block =>
      code.2.2.2 i) :=
    (measurable_pi_apply i).comp (measurable_snd.comp (measurable_snd.comp (measurable_snd)))
  exact (measurable_followerSuccessorCodeFromOutput rate block).comp
    (hprepared.prodMk hobservation)
/-- Decode one observation code only when the existing physical
`observeFollower` operation confirms its concrete `FollowerOutcome`. The
proof-carrying result is used to build the physical `RoundResult`. -/
noncomputable def decodeFollowerOutcomeCode (time : Fin p.T)
    (source : SourceInput p)
    (i : Fin (p.m - 1)) (prepared : PreparedFollower p rate block) (feedback : Fin (D p + 1))
    (code : FollowerObservationCode p rate block) :
    Option {outcome : FollowerOutcome p rate block //
      observeFollower rate block time source i prepared feedback =
        .ok outcome} := by
  classical
  cases prepared with
  | bootstrap state arm =>
      cases code with
      | inl observed =>
          cases observed with
          | rejected _ => exact none
          | accepted next =>
              let outcome : FollowerOutcome p rate block :=
                ⟨.bootstrap state arm, .bootstrap next⟩
              by_cases h : observeFollower rate block time
                  source i (.bootstrap state arm) feedback = .ok outcome
              · exact some ⟨outcome, h⟩
              · exact none
      | inr _ => exact none
  | declared row activation round =>
      cases code with
      | inl _ => exact none
      | inr observed =>
          by_cases hactivation : observed.1 = activation
          · let outcome : FollowerOutcome p rate block :=
              ⟨.declared row activation round,
                .declared row activation
                  (FollowerPrepareJointMeasurability.localConfigurationOfIncoming rate
                    observed.2.2)⟩
            by_cases h : observeFollower rate block time
                source i (.declared row activation round) feedback = .ok outcome
            · exact some ⟨outcome, h⟩
            · exact none
          · exact none
/-- The family decoder assembles only code-certified local transitions. -/
noncomputable def decodeFollowerOutcomeFamily
    (prepared : ActualInitializationPhysicalStep.PreparedRound p rate block)
    (codes : Fin (p.m - 1) → FollowerObservationCode p rate block) :
    Option {outcomes : Fin (p.m - 1) →
        FollowerOutcome p rate block //
      ∀ i, observeFollower rate block prepared.time
        prepared.source i (prepared.followers i)
        (physicalFeedback prepared (followerPlayer p.two_le_m i)) = .ok (outcomes i)} := by
  classical
  let decoded := fun i => decodeFollowerOutcomeCode rate block prepared.time prepared.source i
    (prepared.followers i)
    (physicalFeedback prepared (followerPlayer p.two_le_m i)) (codes i)
  by_cases hdecoded : ∀ i, (decoded i).isSome
  · exact some ⟨(fun i => ((decoded i).get (hdecoded i)).1),
      (fun i => ((decoded i).get (hdecoded i)).2)⟩
  · exact none
/-- The generated bootstrap observation is accepted by the physical follower
observer on that same prepared follower and own feedback entry. -/
private theorem decodeFollowerOutcomeCodeOnReady_bootstrap_isSome
    (i : Fin (p.m - 1)) (x : ReadyInput p rate block C_star C_h)
    (startup : ActualBootstrapObservationCode.StartupCode p block)
    (hcode : x.1.followers i = Sum.inl startup) :
    (decodeFollowerOutcomeCode rate block x.1.time x.1.source i
      ((actualPreparedRoundOnReady rate block C_star C_h x).followers i)
      ((actualJointPhysicalCodeOnReady rate block C_star C_h x).2 (followerPlayer p.two_le_m i))
      (followerObservationCodeOnReady rate block C_star C_h i x)).isSome := by
  classical
  let branch : FollowerBootstrapBranch p rate block C_star C_h i :=
    ⟨x, ⟨startup, hcode.symm⟩⟩
  have hsplit : (MeasurableEquiv.sumCompl (s := FollowerBootstrapBranch p rate block C_star C_h i)
      (measurableSet_followerBootstrapCodeSet rate block C_star C_h i)).symm x =
      Sum.inl branch := Equiv.Set.sumCompl_symm_apply_of_mem branch.2
  obtain ⟨next, haccepted⟩ :=
    followerBootstrapObservationCodeOnBootstrap_accepted rate block C_star C_h i branch
  have houtput : followerObservationCodeOnReady rate block C_star C_h i x =
      Sum.inl (.accepted next) := by
    unfold followerObservationCodeOnReady
    rw [hsplit]
    exact congrArg Sum.inl haccepted
  have hstartup : followerStartupCodeOnBootstrap rate block C_star C_h i branch = startup := by
    simp [followerStartupCodeOnBootstrap, branch, hcode]
  let arm := localArm p block startup
    (sourceIDs p x.1.source) x.1.time
    (fun _ => playerRoundScalarAt p x.1.source.2 (followerPlayer p.two_le_m i) x.1.time)
  have hprepared : (actualPreparedRoundOnReady rate block C_star C_h x).followers i =
        .bootstrap startup arm := by
    have hd := decode_preparedFollowerCodeOnReady rate block C_star C_h i x
    have hd' : some (PreparedFollower.bootstrap startup arm) =
        some ((actualPreparedRoundOnReady rate block C_star C_h x).followers i) := by
      change some (.bootstrap startup arm) = some (prepareFollowerValid rate block
        x.1.time x.1.source i (followerStateOfCode p rate block (x.1.followers i)) _)
      simpa [preparedFollowerCodeOnReady, hsplit, followerPreparedCodeOnBootstrap,
        decodePreparedFollowerCode, hstartup, arm, branch, sourcePrivate] using hd
    exact (Option.some.inj hd').symm
  have hobs : BootstrapObservedFollower.observe p block startup
      (sourceIDs p x.1.source) (sourceRows p x.1.source) x.1.time
      (observationOfGrid p ((actualJointPhysicalCodeOnReady rate block C_star C_h x).2
        (followerPlayer p.two_le_m i))) = .accepted next := by
    simpa [followerBootstrapObservationCodeOnBootstrap, branch, hstartup] using haccepted
  have htransition := observeFollower_bootstrap_next_is_startup rate block x.1.time
    x.1.source i startup next arm
    ((actualJointPhysicalCodeOnReady rate block C_star C_h x).2 (followerPlayer p.two_le_m i)) hobs
  rw [hprepared, houtput]
  simp [decodeFollowerOutcomeCode, htransition]
/-- A declared output code validates against the same actual prepared local
round, including the full ordinary/dagger carry reconstructed by its accepted
preparation code. -/
private theorem decodeFollowerOutcomeCodeOnReady_declared_isSome
    (i : Fin (p.m - 1)) (x : ReadyInput p rate block C_star C_h)
    (fields : ActualInitializationPreparationMeasurability.DeclaredInputCode p rate)
    (hcode : x.1.followers i = Sum.inr fields) :
    (decodeFollowerOutcomeCode rate block x.1.time x.1.source i
      ((actualPreparedRoundOnReady rate block C_star C_h x).followers i)
      ((actualJointPhysicalCodeOnReady rate block C_star C_h x).2 (followerPlayer p.two_le_m i))
      (followerObservationCodeOnReady rate block C_star C_h i x)).isSome := by
  classical
  let split := MeasurableEquiv.sumCompl (s := FollowerBootstrapBranch p rate block C_star C_h i)
    (measurableSet_followerBootstrapCodeSet rate block C_star C_h i)
  have hnotmem : x ∈ (FollowerBootstrapBranch p rate block C_star C_h i)ᶜ := by
    intro hmem
    rcases hmem with ⟨startup, hstartup⟩
    have hsum : Sum.inl startup = Sum.inr fields := hstartup.trans hcode
    exact Sum.inl_ne_inr hsum
  let branch : FollowerDeclaredBranch p rate block C_star C_h i := ⟨x, hnotmem⟩
  have hsplit : split.symm x = Sum.inr branch := by
    change (Equiv.sumCompl (fun y => y ∈
      FollowerBootstrapBranch p rate block C_star C_h i)).symm x = Sum.inr branch
    exact Equiv.Set.sumCompl_symm_apply_of_notMem hnotmem
  have hfields :
      ActualInitializationPreparationMeasurability.followerDeclaredCodeOnReady
        rate block C_star C_h i branch = fields := by
    have hdecl := followerCode_eq_inr_of_declared rate block C_star C_h i branch
    have hx : branch.1.1.followers i = Sum.inr fields := by
      simpa [branch] using hcode
    exact Sum.inr.inj (hdecl.symm.trans hx)
  subst fields
  let fields := ActualInitializationPreparationMeasurability.followerDeclaredCodeOnReady
    rate block C_star C_h i branch
  let output := followerDeclaredObservationCodeOnDeclared rate block C_star C_h i branch
  have houtput : followerObservationCodeOnReady rate block C_star C_h i x = Sum.inr output := by
    unfold followerObservationCodeOnReady
    rw [hsplit]
    simp only [Sum.elim_inr]
    rfl
  have hactivation : output.1 = fields.2.1 := by
    rfl
  let preparedCode := preparedDeclaredCodeOnDeclared rate block C_star C_h i branch
  have hpreparedCode :
      Sum.inr preparedCode =
        preparedFollowerCodeOnReady rate block C_star C_h i x := by
    let readyCode := preparedFollowerCodeOnReady rate block C_star C_h i branch.1
    have hmem : readyCode ∈ Set.range
        (Sum.inr : PreparedDeclaredCode p rate → PreparedFollowerCode p rate block) := by
      change preparedFollowerCodeOnReady rate block C_star C_h i branch.1 ∈ Set.range
          (Sum.inr : PreparedDeclaredCode p rate → PreparedFollowerCode p rate block)
      rw [← preparedFollowerCodeOnDeclared_eq_ready rate block C_star C_h i branch]
      simp [followerPreparedCodeOnDeclared]
    let e := Equiv.Set.rangeInr (PreparedBootstrapCode p block) (PreparedDeclaredCode p rate)
    let z : Set.range (Sum.inr : PreparedDeclaredCode p rate → PreparedFollowerCode p rate block) :=
      ⟨readyCode, hmem⟩
    change Sum.inr (e z) = readyCode
    have hz := e.symm_apply_apply z
    simpa [e, Equiv.Set.rangeInr] using congrArg Subtype.val hz
  have hbranchPreparedCode :
      followerPreparedCodeOnDeclared rate block C_star C_h i branch = Sum.inr preparedCode := by
    calc
      followerPreparedCodeOnDeclared rate block C_star C_h i branch =
          preparedFollowerCodeOnReady rate block C_star C_h i branch.1 :=
        preparedFollowerCodeOnDeclared_eq_ready rate block C_star C_h i branch
      _ = Sum.inr preparedCode := hpreparedCode.symm
  have hpreparedActivation : preparedCode.2.1 = fields.2.1 := by
    have h := congrArg (fun code : PreparedFollowerCode p rate block =>
      match code with
      | .inl _ => none
      | .inr data => some data.2.1) hbranchPreparedCode
    have h' : some fields.2.1 = some preparedCode.2.1 := by
      simpa [followerPreparedCodeOnDeclared]
        using h
    exact (Option.some.inj h').symm
  have hpreparedRow : preparedCode.1 = fields.1 := by
    have h := congrArg (fun code : PreparedFollowerCode p rate block =>
      match code with
      | .inl _ => none
      | .inr data => some data.1) hbranchPreparedCode
    have h' : some fields.1 = some preparedCode.1 := by
      simpa [followerPreparedCodeOnDeclared]
        using h
    exact (Option.some.inj h').symm
  have hdecoded :=
    decode_preparedFollowerCodeOnReady rate block C_star C_h i x
  rw [← hpreparedCode] at hdecoded
  have hvalid := declaredActivation_le_time_of_ready rate block C_star C_h i x fields hcode
  simp only [decodePreparedFollowerCode] at hdecoded
  rw [hpreparedActivation, hpreparedRow] at hdecoded
  rw [dite_eq_left hvalid] at hdecoded
  let prepared := actualPreparedRoundOnReady rate block C_star C_h x
  have hprepared : prepared.followers i =
      .declared fields.1 fields.2.1
        (FollowerPrepareJointMeasurability.preparedRoundOfOutput rate i fields.2.1
          ((sourceRows p x.1.source fields.1,
            ⟨x.1.time, hvalid⟩), (preparedCode.2.2.1, preparedCode.2.2.2))) := by
    have hdecoded' := Option.some.inj hdecoded
    calc
      prepared.followers i =
          prepareFollowerValid rate block x.1.time x.1.source i (followerStateOfCode p rate block
              (x.1.followers i))
            (readyFollowerCursorProof rate block C_star C_h i x) := by
          rfl
      _ = .declared fields.1 fields.2.1
          (FollowerPrepareJointMeasurability.preparedRoundOfOutput rate i fields.2.1
            ((sourceRows p x.1.source fields.1,
              ⟨x.1.time, hvalid⟩), (preparedCode.2.2.1, preparedCode.2.2.2))) := by
          simpa [followerStateOfCode, hcode,
            prepareFollowerValid,
            preparedDeclaredCodeOnDeclared, preparedCode] using hdecoded'.symm
  have hvalid' := declaredActivation_le_time_of_ready rate block C_star C_h i x fields hcode
  have hroundCode := followerDeclaredObservationCodeOnDeclared_reconstructs
    rate block C_star C_h i branch
  have hround : DeclaredFollowerLocalRound.observe
      (FollowerPrepareJointMeasurability.preparedRoundOfOutput rate i fields.2.1
        ((sourceRows p x.1.source fields.1,
          ⟨x.1.time, hvalid'⟩), (preparedCode.2.2.1, preparedCode.2.2.2)))
      (FollowerDownMeasurability.feedbackAtGrid p
        ((actualJointPhysicalCodeOnReady rate block C_star C_h x).2
          (followerPlayer p.two_le_m i))) =
      observedRoundOfCarriedOutput output.2 := by
    simpa only [branch, fields, preparedCode, output, followerDeclaredCodeOnReady,
      FollowerPrepareJointMeasurability.preparedRoundOfOutput]
      using hroundCode.symm
  have hnext : FollowerPrepareJointMeasurability.localConfigurationOfIncoming rate output.2.2 =
      (DeclaredFollowerLocalRound.observe
        (FollowerPrepareJointMeasurability.preparedRoundOfOutput rate i fields.2.1
          ((sourceRows p x.1.source fields.1,
            ⟨x.1.time, hvalid'⟩), (preparedCode.2.2.1, preparedCode.2.2.2)))
        (FollowerDownMeasurability.feedbackAtGrid p
          ((actualJointPhysicalCodeOnReady rate block C_star C_h x).2
            (followerPlayer p.two_le_m i)))).configuration := by
    have hcfg := congrArg DeclaredFollowerLocalRound.ObservedRound.configuration hround
    simpa [observedRoundOfCarriedOutput] using hcfg.symm
  have htransition : observeFollower rate block x.1.time
      x.1.source i (prepared.followers i)
      ((actualJointPhysicalCodeOnReady rate block C_star C_h x).2 (followerPlayer p.two_le_m i)) =
      .ok ⟨prepared.followers i,
        .declared fields.1 fields.2.1
          (FollowerPrepareJointMeasurability.localConfigurationOfIncoming rate output.2.2)⟩ := by
    rw [hprepared]
    rw [observeFollower_declared_eq]
    have hfeedback : FollowerDownMeasurability.feedbackAtGrid p
        ((actualJointPhysicalCodeOnReady rate block C_star C_h x).2 (followerPlayer p.two_le_m i)) =
      observationOfGrid p
        ((actualJointPhysicalCodeOnReady rate block C_star C_h x).2
          (followerPlayer p.two_le_m i)) := rfl
    rw [← hfeedback]
    rw [← hnext]
  rw [hprepared] at htransition
  rw [houtput, hprepared]
  simp [decodeFollowerOutcomeCode, hactivation, htransition]
/-- The generated heterogeneous follower family decodes to the existing
`observeFollowers` result. Equality of local outcomes follows from
`Except.ok` injectivity and the existing transition certificate, so this
does not introduce a second choice-based protocol. -/
private theorem decodeFollowerOutcomeFamilyOnReady
    (x : ReadyInput p rate block C_star C_h) :
    decodeFollowerOutcomeFamily rate block (actualPreparedRoundOnReady rate block C_star C_h x)
      (fun i => followerObservationCodeOnReady rate block C_star C_h i x) =
    some (observeFollowers (actualPreparedRoundOnReady rate block C_star C_h x)) := by
  classical
  let prepared := actualPreparedRoundOnReady rate block C_star C_h x
  let observed := observeFollowers prepared
  let decoded := fun i => decodeFollowerOutcomeCode rate block prepared.time prepared.source i
    (prepared.followers i)
    (physicalFeedback prepared (followerPlayer p.two_le_m i))
    (followerObservationCodeOnReady rate block C_star C_h i x)
  have hdecoded : ∀ i, (decoded i).isSome := by
    intro i
    cases hcode : x.1.followers i with
    | inl startup =>
        have h := decodeFollowerOutcomeCodeOnReady_bootstrap_isSome
          rate block C_star C_h i x startup hcode
        rw [actualJointPhysicalCodeOnReady_eq_actualPreparedRoundOnReady
          rate block C_star C_h x] at h
        exact h
    | inr fields =>
        have h := decodeFollowerOutcomeCodeOnReady_declared_isSome
          rate block C_star C_h i x fields hcode
        rw [actualJointPhysicalCodeOnReady_eq_actualPreparedRoundOnReady
          rate block C_star C_h x] at h
        exact h
  have houtcomes : (fun i => ((decoded i).get (hdecoded i)).1) = observed.1 := by
    funext i
    apply Except.ok.inj
    exact (((decoded i).get (hdecoded i)).2).symm.trans (observed.2 i)
  let decodedFamily : {outcomes : Fin (p.m - 1) →
      FollowerOutcome p rate block //
      ∀ i, observeFollower rate block prepared.time
        prepared.source i (prepared.followers i)
        (physicalFeedback prepared (followerPlayer p.two_le_m i)) = .ok (outcomes i)} :=
    ⟨(fun i => ((decoded i).get (hdecoded i)).1), fun i => ((decoded i).get (hdecoded i)).2⟩
  have hfamily : decodeFollowerOutcomeFamily rate block prepared
      (fun i => followerObservationCodeOnReady rate block C_star C_h i x) =
      some decodedFamily := by
    simp [decodeFollowerOutcomeFamily, decoded, hdecoded, decodedFamily]
  have hdecodedOutcomes : decodedFamily.1 = observed.1 := houtcomes
  rw [hfamily]
  congr 1
  apply Subtype.ext
  exact hdecodedOutcomes
/-- The coordinator's measurable successor code is a projection of the same
successful result carrier. -/
def coordinatorSuccessorCodeFromSuccessfulRoundCode
    (code : SuccessfulRoundCode p rate block) : CoordinatorSuccessorCode p :=
  coordinatorSuccessorCode code.2.2.1

theorem measurable_coordinatorSuccessorCodeFromSuccessfulRoundCode :
    Measurable (coordinatorSuccessorCodeFromSuccessfulRoundCode rate block) := by
  exact measurable_coordinatorSuccessorCode.comp
    (measurable_fst.comp (measurable_snd.comp measurable_snd))
/-- The code for one physical own entry retains this player's actual arm and
its own finite-grid feedback. -/
abbrev PhysicalOwnEntryCode (p : Parameters) := Fin p.K × Fin (D p + 1)

def physicalOwnEntryFromSuccessfulRoundCode (code : SuccessfulRoundCode p rate block)
    (player : Fin p.m) : PhysicalOwnEntryCode p :=
  ((code.2.1).1 player, (code.2.1).2 player)

theorem measurable_physicalOwnEntryFromSuccessfulRoundCode (player : Fin p.m) :
    Measurable (physicalOwnEntryFromSuccessfulRoundCode rate block · player) := by
  have hjoint : Measurable (fun code : SuccessfulRoundCode p rate block => code.2.1) :=
    measurable_fst.comp measurable_snd
  exact (measurable_pi_apply player).comp (measurable_fst.comp hjoint) |>.prodMk
    ((measurable_pi_apply player).comp (measurable_snd.comp hjoint))
/-- The total output code for the existing physical `step` operation. Every
unready input gets the physical `inputNotReady` token; ready inputs use the
same-input successful code assembler. -/
def actualRoundOutputCode
    (x : RoundInput p rate block C_star C_h) : ActualRoundOutputCode p rate block := by
  classical
  exact Sum.elim (fun ready => Sum.inr (successfulRoundCodeOnReady rate block C_star C_h ready))
    (fun _ => Sum.inl ())
    ((MeasurableEquiv.sumCompl (s := {x | roundInputReady p rate block C_star C_h x})
      (ActualInitializationPreparationMeasurability.measurableSet_roundInputReady
        rate block C_star C_h)).symm x)
/-- The existing heterogeneous physical `step` applied to the complete same
`RoundInput`, including its unready `inputNotReady` path. -/
def actualPhysicalStepOnRoundInput
    (x : RoundInput p rate block C_star C_h) :
    Except (InputFailure p block)
      (RoundResult p rate block) :=
  ActualInitializationPhysicalStep.step rate block x.time (coordinatorOfInput
      p rate block C_star C_h x)
    (followersOfInput p rate block x.followers)
    x.source x.rewards
/-- Partially decode all successful-round fields relative to the same ready
input. Malformed prepared, physical, follower, or coordinator codes return
`none`; no fallback successful witness is manufactured. -/
noncomputable def decodeSuccessfulRoundCode
    (x : ReadyInput p rate block C_star C_h)
    (code : SuccessfulRoundCode p rate block) :
    Option (RoundResult p rate block) := by
  classical
  match decodePreparedRoundCode rate block C_star C_h x code.1 with
  | none => exact none
  | some prepared =>
      if hphysical : code.2.1 =
          (actionProfile prepared,
            physicalFeedback prepared) then
        match decodeFollowerOutcomeFamily rate block prepared code.2.2.2 with
        | none => exact none
        | some outcomes =>
            if hcoordinator : reconstructCoordinatorObservationCode
                p C_star C_h (coordinatorObserveInputOnReady rate block C_star C_h x).fixed
                  code.2.2.1 =
                some (BootstrapCoordinatorLocalRound.observe prepared.coordinator
                  (physicalFeedback prepared (coordinator p.two_le_m))) then
              exact some ⟨prepared, outcomes.1, outcomes.2⟩
            else exact none
      else exact none
/-- Decode the total output code relative to its original full input. The
physical failure code is admitted exactly on the unready branch; successful
codes are decoded only on the ready subtype. -/
noncomputable def decodeActualRoundOutputCode
    (x : RoundInput p rate block C_star C_h)
    (code : ActualRoundOutputCode p rate block) :
    Option (Except (InputFailure p block)
      (RoundResult p rate block)) := by
  classical
  cases code with
  | inl _ =>
      by_cases hready : roundInputReady p rate block C_star C_h x
      · exact none
      · exact some (.error .inputNotReady)
  | inr successful =>
      by_cases hready : roundInputReady p rate block C_star C_h x
      · match decodeSuccessfulRoundCode rate block C_star C_h ⟨x, hready⟩ successful with
        | none => exact none
        | some result => exact some (.ok result)
      · exact none
/-- The full-input round code is measurable, including its exact unready
branch, on the existing full `RoundInput` measurable space. -/
theorem measurable_actualRoundOutputCode :
    Measurable (actualRoundOutputCode rate block C_star C_h) := by
  classical
  exact (Measurable.sumElim (measurable_inr.comp
      (measurable_successfulRoundCodeOnReady rate block C_star C_h)) measurable_const).comp
    (MeasurableEquiv.sumCompl (s := {x : RoundInput p rate block C_star C_h |
        roundInputReady p rate block C_star C_h x})
      (ActualInitializationPreparationMeasurability.measurableSet_roundInputReady
        rate block C_star C_h)).symm.measurable_toFun
/-- The total-output successor projection carries the exact encoded follower
continuation on success and a separate tag on the physical error branch. -/
def followerSuccessorCodeFromActualRoundOutput
    (code : ActualRoundOutputCode p rate block) (i : Fin (p.m - 1)) :
    Unit ⊕ FollowerSuccessorCode p rate block :=
  Sum.elim (fun _ => Sum.inl ())
    (fun successful => followerSuccessorCodeFromSuccessfulRoundCode rate block successful i)
    code

theorem measurable_followerSuccessorCodeFromActualRoundOutput (i : Fin (p.m - 1)) :
    Measurable (followerSuccessorCodeFromActualRoundOutput rate block · i) := by
  exact Measurable.sumElim measurable_const
    (measurable_followerSuccessorCodeFromSuccessfulRoundCode rate block i)

def actualFollowerSuccessorCodeOnRoundInput
    (x : RoundInput p rate block C_star C_h) (i : Fin (p.m - 1)) :
    Unit ⊕ FollowerSuccessorCode p rate block :=
  followerSuccessorCodeFromActualRoundOutput rate block
    (actualRoundOutputCode rate block C_star C_h x) i

theorem measurable_actualFollowerSuccessorCodeOnRoundInput
    (i : Fin (p.m - 1)) :
    Measurable (actualFollowerSuccessorCodeOnRoundInput rate block C_star C_h · i) :=
  (measurable_followerSuccessorCodeFromActualRoundOutput rate block i).comp
    (measurable_actualRoundOutputCode rate block C_star C_h)

abbrev PartialCoordinatorSuccessorCode (p : Parameters) :=
  Unit ⊕ CoordinatorSuccessorCode p

def coordinatorSuccessorCodeFromActualRoundOutput
    (code : ActualRoundOutputCode p rate block) : PartialCoordinatorSuccessorCode p :=
  Sum.elim (fun _ => Sum.inl ()) (fun successful => Sum.inr
      (coordinatorSuccessorCodeFromSuccessfulRoundCode rate block successful)) code

theorem measurable_coordinatorSuccessorCodeFromActualRoundOutput :
    Measurable (coordinatorSuccessorCodeFromActualRoundOutput rate block) :=
  Measurable.sumElim measurable_const (measurable_inr.comp
      (measurable_coordinatorSuccessorCodeFromSuccessfulRoundCode rate block))

def actualCoordinatorSuccessorCodeOnRoundInput
    (x : RoundInput p rate block C_star C_h) : PartialCoordinatorSuccessorCode p :=
  coordinatorSuccessorCodeFromActualRoundOutput rate block
    (actualRoundOutputCode rate block C_star C_h x)

theorem measurable_actualCoordinatorSuccessorCodeOnRoundInput :
    Measurable (actualCoordinatorSuccessorCodeOnRoundInput rate block C_star C_h) :=
  (measurable_coordinatorSuccessorCodeFromActualRoundOutput rate block).comp
    (measurable_actualRoundOutputCode rate block C_star C_h)

abbrev PartialPhysicalOwnEntryCode (p : Parameters) :=
  Unit ⊕ PhysicalOwnEntryCode p

def physicalOwnEntryFromActualRoundOutput
    (code : ActualRoundOutputCode p rate block) (player : Fin p.m) :
    PartialPhysicalOwnEntryCode p :=
  Sum.elim (fun _ => Sum.inl ()) (fun successful => Sum.inr
      (physicalOwnEntryFromSuccessfulRoundCode rate block successful player)) code

theorem measurable_physicalOwnEntryFromActualRoundOutput (player : Fin p.m) :
    Measurable (physicalOwnEntryFromActualRoundOutput rate block · player) :=
  Measurable.sumElim measurable_const (measurable_inr.comp
      (measurable_physicalOwnEntryFromSuccessfulRoundCode rate block player))

def actualPhysicalOwnEntryOnRoundInput
    (x : RoundInput p rate block C_star C_h) (player : Fin p.m) :
    PartialPhysicalOwnEntryCode p :=
  physicalOwnEntryFromActualRoundOutput rate block
    (actualRoundOutputCode rate block C_star C_h x) player

theorem measurable_actualPhysicalOwnEntryOnRoundInput
    (player : Fin p.m) :
    Measurable (actualPhysicalOwnEntryOnRoundInput rate block C_star C_h · player) :=
  (measurable_physicalOwnEntryFromActualRoundOutput rate block player).comp
    (measurable_actualRoundOutputCode rate block C_star C_h)
/-- The existing physical observation assembly on the same prepared input.
This merely packages `observeFollowers`; it defines no new local transition. -/
def actualRoundResultOnReady
    (x : ReadyInput p rate block C_star C_h) :
    RoundResult p rate block :=
  let prepared := actualPreparedRoundOnReady rate block C_star C_h x
  let outcomes := observeFollowers prepared
  ⟨prepared, outcomes.1, outcomes.2⟩
/-- The result is the actual successful computation, including every field. -/
theorem actualPhysicalStepOnRoundInput_eq_ok_onReady
    (x : ReadyInput p rate block C_star C_h) :
    actualPhysicalStepOnRoundInput rate block C_star C_h x.1 =
      .ok (actualRoundResultOnReady rate block C_star C_h x) := by
  have h := (actualPrepareResult_and_jointPhysicalCodeOnReady rate block C_star C_h x).1
  change ActualInitializationPhysicalStep.prepare rate block x.1.time _ _ _ _ = _ at h
  change (match ActualInitializationPhysicalStep.prepare rate block x.1.time _ _ _ _ with
    | .error failure => (Except.error failure : Except
        (InputFailure p block) (RoundResult p rate block))
    | .ok prepared => observePrepared prepared) = _
  rw [h]
  rfl
/-- The coordinator code reconstructs the observation of this exact result. -/
theorem reconstruct_coordinatorObservationCodeOnReady_eq_actualResult
    (x : ReadyInput p rate block C_star C_h) :
    reconstructCoordinatorObservationCode p C_star C_h
      (coordinatorObserveInputOnReady rate block C_star C_h x).fixed
      (coordinatorObservationCodeOnReady rate block C_star C_h x) =
      some (actualRoundResultOnReady rate block C_star C_h x).coordinator := by
  have h := reconstruct_coordinatorObservationCodeOnReady rate block C_star C_h x
  rw [actualJointPhysicalCodeOnReady_eq_actualPreparedRoundOnReady] at h
  exact h
/-- Complete relative-input reconstruction, retaining preparation metadata,
all follower outcomes and the exact coordinator continuation. -/
theorem decodeSuccessfulRoundCodeOnReady
    (x : ReadyInput p rate block C_star C_h) :
    decodeSuccessfulRoundCode rate block C_star C_h x
      (successfulRoundCodeOnReady rate block C_star C_h x) =
      some (actualRoundResultOnReady rate block C_star C_h x) := by
  have hphysical := (actualPrepareResult_and_jointPhysicalCodeOnReady rate block C_star C_h x).2
  have hcoordinator := reconstruct_coordinatorObservationCodeOnReady_eq_actualResult
    rate block C_star C_h x
  simp only [actualRoundResultOnReady, RoundResult.coordinator,
    RoundResult.feedback] at hcoordinator
  simp [decodeSuccessfulRoundCode, successfulRoundCodeOnReady,
    decodePreparedRoundCodeOnReady, hphysical, decodeFollowerOutcomeFamilyOnReady,
    hcoordinator, actualRoundResultOnReady]
/-- Exact ready branch of the full-input code. -/
theorem actualRoundOutputCode_eq_success_onReady
    (x : ReadyInput p rate block C_star C_h) :
    actualRoundOutputCode rate block C_star C_h x.1 =
      .inr (successfulRoundCodeOnReady rate block C_star C_h x) := by
  classical
  unfold actualRoundOutputCode
  have hsplit : (MeasurableEquiv.sumCompl (s := {y : RoundInput p rate block C_star C_h |
        roundInputReady p rate block C_star C_h y})
      (measurableSet_roundInputReady rate block C_star C_h)).symm x.1 = Sum.inl x :=
    Equiv.Set.sumCompl_symm_apply_of_mem (show x.1 ∈ {y |
      roundInputReady p rate block C_star C_h y} from x.2)
  rw [hsplit]
  rfl
/-- Every unready full input retains both the exact code tag and the complete
physical `inputNotReady` result; no local observation is silently substituted. -/
theorem actualRoundOutputCode_and_step_eq_inputNotReady
    (x : RoundInput p rate block C_star C_h)
    (hnotready : ¬ roundInputReady p rate block C_star C_h x) :
    actualRoundOutputCode rate block C_star C_h x = .inl () ∧
      actualPhysicalStepOnRoundInput rate block C_star C_h x = .error .inputNotReady := by
  classical
  constructor
  · unfold actualRoundOutputCode
    have hsplit : (MeasurableEquiv.sumCompl (s := {y : RoundInput p rate block C_star C_h |
          roundInputReady p rate block C_star C_h y})
        (measurableSet_roundInputReady rate block C_star C_h)).symm x =
        Sum.inr ⟨x, hnotready⟩ :=
      Equiv.Set.sumCompl_symm_apply_of_notMem (show x ∉ {y |
        roundInputReady p rate block C_star C_h y} from hnotready)
    rw [hsplit]
    rfl
  · have h := actualPrepareResult_eq_inputNotReady rate block C_star C_h x hnotready
    change ActualInitializationPhysicalStep.prepare rate block x.time _ _ _ _ = _ at h
    change (match ActualInitializationPhysicalStep.prepare rate block x.time _ _ _ _ with
      | .error failure => (Except.error failure : Except
          (InputFailure p block) (RoundResult p rate block))
      | .ok prepared => observePrepared prepared) = _
    rw [h]
/-- Total same-input reconstruction of the full existing physical Except.
No preparation-decoder measurability or completed-operation premise is used. -/
theorem decodeActualRoundOutputCode_eq_actualPhysicalStep
    (x : RoundInput p rate block C_star C_h) :
    decodeActualRoundOutputCode rate block C_star C_h x
      (actualRoundOutputCode rate block C_star C_h x) =
      some (actualPhysicalStepOnRoundInput rate block C_star C_h x) := by
  classical
  by_cases hready : roundInputReady p rate block C_star C_h x
  · rw [actualRoundOutputCode_eq_success_onReady rate block C_star C_h ⟨x, hready⟩,
      actualPhysicalStepOnRoundInput_eq_ok_onReady rate block C_star C_h ⟨x, hready⟩]
    simp only [decodeActualRoundOutputCode, hready, dite_true,
      decodeSuccessfulRoundCodeOnReady]
  · obtain ⟨hcode, hstep⟩ := actualRoundOutputCode_and_step_eq_inputNotReady
      rate block C_star C_h x hready
    rw [hcode, hstep]
    simp only [decodeActualRoundOutputCode, hready, dite_false]
/-- Ordinary arbitrary-base composition requires only a measurable map into
this existing full input carrier. -/
theorem measurable_actualRoundOutputCode_comp
    {Ω : Type*} [MeasurableSpace Ω]
    (input : Ω → RoundInput p rate block C_star C_h) (hinput : Measurable input) :
    Measurable (fun ω => actualRoundOutputCode rate block C_star C_h (input ω)) :=
  (measurable_actualRoundOutputCode rate block C_star C_h).comp hinput
/-- The measurable own-entry projection is the same physical arm and feedback
of the complete computed successful round. -/
theorem actualPhysicalOwnEntryOnRoundInput_eq_onReady
    (x : ReadyInput p rate block C_star C_h) (player : Fin p.m) :
    actualPhysicalOwnEntryOnRoundInput rate block C_star C_h x.1 player =
      .inr ((actualRoundResultOnReady rate block C_star C_h x).actions player,
        (actualRoundResultOnReady rate block C_star C_h x).feedback player) := by
  rw [actualPhysicalOwnEntryOnRoundInput, actualRoundOutputCode_eq_success_onReady]
  change Sum.inr ((actualJointPhysicalCodeOnReady rate block C_star C_h x).1 player,
    (actualJointPhysicalCodeOnReady rate block C_star C_h x).2 player) = _
  rw [actualJointPhysicalCodeOnReady_eq_actualPreparedRoundOnReady]
  rfl
/-- Conditional codec lemma: the two explicit successful decoder equations
identify the projected code with the decoded outcome's entire next state. -/
private theorem followerSuccessorCodeFromOutput_reconstructs (time : Fin p.T)
    (source : ActualSource p) (i : Fin (p.m - 1))
    (preparedCode : PreparedFollowerCode p rate block)
    (prepared : PreparedFollower p rate block)
    (feedback : Fin (D p + 1)) (code : FollowerObservationCode p rate block)
    (outcome : {o : FollowerOutcome p rate block //
      observeFollower rate block time source i prepared feedback = .ok o})
    (hprepared : decodePreparedFollowerCode rate i source time preparedCode = some prepared)
    (houtcome : decodeFollowerOutcomeCode rate block time source i prepared feedback code =
      some outcome) :
    Sum.map id (followerStateOfCode p rate block)
      (followerSuccessorCodeFromOutput rate block (preparedCode, code)) =
      .inr outcome.1.next := by
  classical
  cases preparedCode with
  | inl bootstrap =>
      rcases bootstrap with ⟨state, arm⟩
      simp only [decodePreparedFollowerCode] at hprepared
      have hp := Option.some.inj hprepared
      subst prepared
      cases code with
      | inr declared => simp only [decodeFollowerOutcomeCode] at houtcome; cases houtcome
      | inl observed =>
          cases observed with
          | rejected failure => simp only [decodeFollowerOutcomeCode] at houtcome; cases houtcome
          | accepted next =>
              simp only [decodeFollowerOutcomeCode] at houtcome
              split at houtcome
              · have hnext := congrArg (fun o => o.1.next) (Option.some.inj houtcome)
                rw [← hnext]
                rfl
              · cases houtcome
  | inr declared =>
      rcases declared with ⟨row, activation, arm, incoming⟩
      simp only [decodePreparedFollowerCode] at hprepared
      split at hprepared
      · have hp := Option.some.inj hprepared
        subst prepared
        cases code with
        | inl observed => simp only [decodeFollowerOutcomeCode] at houtcome; cases houtcome
        | inr observed =>
            simp only [decodeFollowerOutcomeCode] at houtcome
            split at houtcome
            · rename_i hactivation
              split at houtcome
              · have hnext := congrArg (fun o => o.1.next) (Option.some.inj houtcome)
                rw [← hnext]
                change Sum.inr (FollowerState.declared row observed.1 _) = _
                rw [hactivation]
              · cases houtcome
            · cases houtcome
      · cases hprepared
/-- The actual follower projection reconstructs the complete next state of
the same successful round, including its own row, activation and real buffers. -/
theorem actualFollowerSuccessorCodeOnRoundInput_reconstructs_onReady
    (x : ReadyInput p rate block C_star C_h) (i : Fin (p.m - 1)) :
    Sum.map id (followerStateOfCode p rate block)
      (actualFollowerSuccessorCodeOnRoundInput rate block C_star C_h x.1 i) =
      .inr ((actualRoundResultOnReady rate block C_star C_h x).followers i).next := by
  classical
  let prepared := actualPreparedRoundOnReady rate block C_star C_h x
  let decoded := decodeFollowerOutcomeCode rate block prepared.time prepared.source i
    (prepared.followers i) (physicalFeedback prepared (followerPlayer p.two_le_m i))
    (followerObservationCodeOnReady rate block C_star C_h i x)
  have hsome : decoded.isSome := by
    cases hcode : x.1.followers i with
    | inl startup =>
        have h := decodeFollowerOutcomeCodeOnReady_bootstrap_isSome
          rate block C_star C_h i x startup hcode
        rw [actualJointPhysicalCodeOnReady_eq_actualPreparedRoundOnReady] at h
        exact h
    | inr fields =>
        have h := decodeFollowerOutcomeCodeOnReady_declared_isSome
          rate block C_star C_h i x fields hcode
        rw [actualJointPhysicalCodeOnReady_eq_actualPreparedRoundOnReady] at h
        exact h
  have hprepared : decodePreparedFollowerCode rate i prepared.source prepared.time
      (preparedFollowerCodeOnReady rate block C_star C_h i x) =
      some (prepared.followers i) := decode_preparedFollowerCodeOnReady rate block C_star C_h i x
  have h := followerSuccessorCodeFromOutput_reconstructs rate block prepared.time
    prepared.source i (preparedFollowerCodeOnReady rate block C_star C_h i x)
    (prepared.followers i) (physicalFeedback prepared (followerPlayer p.two_le_m i))
    (followerObservationCodeOnReady rate block C_star C_h i x)
    (decoded.get hsome) hprepared (Option.some_get hsome).symm
  have hactual : (decoded.get hsome).1 =
      (actualRoundResultOnReady rate block C_star C_h x).followers i := by
    apply Except.ok.inj
    exact (decoded.get hsome).2.symm.trans
      ((actualRoundResultOnReady rate block C_star C_h x).followerTransition i)
  rw [hactual] at h
  rw [actualFollowerSuccessorCodeOnRoundInput, followerSuccessorCodeFromActualRoundOutput,
    actualRoundOutputCode_eq_success_onReady]
  exact h
/-- Literal successor fields of an existing coordinator observation: its arm,
updated local state, monitor, and actual continue/launch constructor. -/
def coordinatorSuccessorCodeOfObservation {p : Parameters}
    (observed : ObservationResult p) :
    CoordinatorSuccessorCode p :=
  (observed.arm, (coordinatorStateCode p observed.next.coordinatorState,
    (monitorCode p observed.next.monitorState, match observed.next with
      | .prelaunch _ => none
      | .launched launched => some launched.triggerRound)))
/-- Conditional decoder projection lemma; its sole logical input is the
explicit successful reconstruction equation. -/
private theorem coordinatorSuccessorCode_eq_of_reconstruction {p : Parameters}
    (C_star C_h : ℝ) (input : CoordinatorFixedRoundInput p C_star C_h)
    (code : CoordinatorObservationCode p)
    (observed : ObservationResult p)
    (h : reconstructCoordinatorObservationCode p C_star C_h input code = some observed) :
    coordinatorSuccessorCode code = coordinatorSuccessorCodeOfObservation observed := by
  classical
  unfold reconstructCoordinatorObservationCode at h
  split_ifs at h <;> cases h <;>
    simp_all [coordinatorSuccessorCode, coordinatorSuccessorCodeOfObservation,
      Continuation.coordinatorState,
      Continuation.monitorState,
      coordinatorObservationDataOfCode, coordinatorStateCode, coordinatorStateOfCode,
      monitorCode, monitorStateOfCode]
  all_goals
    apply monitorCodeFields_injective p
    simp_all
/-- The measurable coordinator projection contains exactly the actual
continue/launch outcome, counters, local registers, and prepared arm. -/
theorem actualCoordinatorSuccessorCodeOnRoundInput_eq_onReady
    (x : ReadyInput p rate block C_star C_h) :
    actualCoordinatorSuccessorCodeOnRoundInput rate block C_star C_h x.1 =
      .inr (coordinatorSuccessorCodeOfObservation
        (actualRoundResultOnReady rate block C_star C_h x).coordinator) := by
  rw [actualCoordinatorSuccessorCodeOnRoundInput,
    coordinatorSuccessorCodeFromActualRoundOutput, actualRoundOutputCode_eq_success_onReady]
  change Sum.inr (coordinatorSuccessorCode
    (coordinatorObservationCodeOnReady rate block C_star C_h x)) = _
  congr 1
  exact coordinatorSuccessorCode_eq_of_reconstruction C_star C_h _ _ _
    (reconstruct_coordinatorObservationCodeOnReady_eq_actualResult rate block C_star C_h x)

end Bandits.Support.ActualInitializationStepMeasurability

end
