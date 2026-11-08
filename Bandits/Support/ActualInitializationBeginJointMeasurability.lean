/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ActualInitializationBlockMeasurability

/-!
# Joint measurability of the actual initialization block start

The actual block-start code is Borel in the complete original source and the
existing carried block input. The follower proof uses countable sections only
for the valid bootstrap numerator subtype; its declared branch copies the
complete incoming configuration, including the original continuous saved-real
fibers. The coordinator is the accepted joint begin code. Reconstruction is
always relative to the same source and carry input.

Sources: `sources/zip4/manuscript/07_public_setup.tex:55-114` and
`sources/zip4/manuscript/appendix_b_communication.tex:94-131,160-165`.

The next consumer is the actual recursive within-block fold at a
source-dependent incoming carry. The actual next-carry coordinate constructor
belongs to the boundary module.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.BootstrapObservedFollower
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.ActualInitializationBlockMeasurability
open Bandits.Support.ActualInitializationRoundMeasurability
open Bandits.Support.BootstrapCoordinatorRoundMeasurability

namespace Bandits.Support.ActualInitializationBeginJointMeasurability

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ActiveFollowerDownAcceptance.RateInput

private abbrev BeginNumeratorCode (p : Parameters) :=
  ActualInitializationBlockMeasurability.ValidNumeratorCode p

private abbrev DeclaredFollowerCarryCode (p : Parameters) (rate : RateInput p) :=
  Fin (M p) × (ReferencePrelaunchFollower.Activation p ×
    FollowerPrepareJointMeasurability.IncomingConfiguration p rate)

/-- Start one follower directly from its lossless carry code. The bootstrap
branch uses the original source's three private scalars, and the declared
branch copies its row, activation, ordinary/dagger code, and saved-real fibers. -/
def beginFollowerCodeOfCarryCode {p : Parameters} {rate : RateInput p}
    (block : Fin (n_boot p)) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1))
    (code : ActualInitializationBlockMeasurability.FollowerCarryCode p rate) :
    ActualInitializationRoundMeasurability.FollowerCode p rate block :=
  match code with
  | .inl numerators =>
      .inl (BootstrapObservedFollower.beginBlock p block numerators.1 numerators.2
        (ActualInitializationBlockMeasurability.sourceBlockScalars block i source))
  | .inr declared => .inr declared

/-- On the code of an existing carry, the direct adapter is exactly the
accepted source-order started follower code. -/
theorem beginFollowerCodeOfCarryCode_followerCarryCodeOf
    {p : Parameters} {rate : RateInput p} (block : Fin (n_boot p))
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (carry : ActualInitializationRun.FollowerCarry p rate) :
    beginFollowerCodeOfCarryCode block source i
        (ActualInitializationBlockMeasurability.followerCarryCodeOf carry) =
      ActualInitializationBlockMeasurability.beginFollowerCodeOfCarry block source i carry := by
  cases carry with
  | bootstrap numerators lowerBound => rfl
  | declared row activation configuration => rfl

/-! The bootstrap numerator subtype is countable. The declared code remains a
continuous product, so its start map is proved by coordinate projection. -/

/-- The started follower code is jointly measurable in the whole original
source and the existing lossless follower carry code. -/
theorem measurable_beginFollowerCodeOfCarryCode
    {p : Parameters} {rate : RateInput p} (block : Fin (n_boot p))
    (i : Fin (p.m - 1)) :
    Measurable (fun x : BootstrapPrivateRoundStreams.SourceInput p ×
        ActualInitializationBlockMeasurability.FollowerCarryCode p rate =>
      beginFollowerCodeOfCarryCode block x.1 i x.2) := by
  let split := MeasurableEquiv.prodSumDistrib
    (BootstrapPrivateRoundStreams.SourceInput p) (BeginNumeratorCode p)
      (DeclaredFollowerCarryCode p rate)
  let leftSpace : MeasurableSpace
      (BootstrapPrivateRoundStreams.SourceInput p × BeginNumeratorCode p) := inferInstance
  let rightSpace : MeasurableSpace
      (BootstrapPrivateRoundStreams.SourceInput p × DeclaredFollowerCarryCode p rate) :=
    inferInstance
  let branchSpace : MeasurableSpace
      ((BootstrapPrivateRoundStreams.SourceInput p × BeginNumeratorCode p) ⊕
        (BootstrapPrivateRoundStreams.SourceInput p × DeclaredFollowerCarryCode p rate)) :=
    @Sum.instMeasurableSpace _ _ leftSpace rightSpace
  have hboot : Measurable (fun x : BootstrapPrivateRoundStreams.SourceInput p ×
      BeginNumeratorCode p =>
      beginFollowerCodeOfCarryCode (p := p) (rate := rate) block x.1 i
        (.inl x.2 : ActualInitializationBlockMeasurability.FollowerCarryCode p rate)) := by
    apply measurable_from_prod_countable_left
    intro numerators
    change Measurable (fun source : BootstrapPrivateRoundStreams.SourceInput p =>
      Sum.inl (BootstrapObservedFollower.beginBlock p block numerators.1 numerators.2
        (ActualInitializationBlockMeasurability.sourceBlockScalars block i source)))
    exact measurable_inl.comp
      (ActualInitializationBlockMeasurability.measurable_bootstrapBeginBlockSource
        block i numerators.1 numerators.2)
  have hdecl : Measurable (fun x : BootstrapPrivateRoundStreams.SourceInput p ×
      DeclaredFollowerCarryCode p rate =>
      beginFollowerCodeOfCarryCode (p := p) (rate := rate) block x.1 i
        (.inr x.2 : ActualInitializationBlockMeasurability.FollowerCarryCode p rate)) := by
    change Measurable (fun x : BootstrapPrivateRoundStreams.SourceInput p ×
        DeclaredFollowerCarryCode p rate =>
      Sum.inr (x.2.1, (x.2.2.1, x.2.2.2)))
    exact measurable_inr.comp
      ((measurable_fst.comp measurable_snd).prodMk
        ((measurable_fst.comp (measurable_snd.comp measurable_snd)).prodMk
          (measurable_snd.comp (measurable_snd.comp measurable_snd))))
  have hsum : @Measurable
      ((BootstrapPrivateRoundStreams.SourceInput p × BeginNumeratorCode p) ⊕
        (BootstrapPrivateRoundStreams.SourceInput p × DeclaredFollowerCarryCode p rate))
      (ActualInitializationRoundMeasurability.FollowerCode p rate block)
      branchSpace inferInstance (Sum.elim
      (fun x : BootstrapPrivateRoundStreams.SourceInput p × BeginNumeratorCode p =>
        beginFollowerCodeOfCarryCode (p := p) (rate := rate) block x.1 i
          (.inl x.2 : ActualInitializationBlockMeasurability.FollowerCarryCode p rate))
      (fun x : BootstrapPrivateRoundStreams.SourceInput p × DeclaredFollowerCarryCode p rate =>
        beginFollowerCodeOfCarryCode (p := p) (rate := rate) block x.1 i
          (.inr x.2 : ActualInitializationBlockMeasurability.FollowerCarryCode p rate))) := by
    intro s hs
    rw [measurableSet_sum_iff]
    constructor
    · convert hboot hs using 1
      ext x
      rfl
    · convert hdecl hs using 1
      ext x
      rfl
  have hsplit : @Measurable
      (BootstrapPrivateRoundStreams.SourceInput p ×
        (BeginNumeratorCode p ⊕ DeclaredFollowerCarryCode p rate))
      ((BootstrapPrivateRoundStreams.SourceInput p × BeginNumeratorCode p) ⊕
        (BootstrapPrivateRoundStreams.SourceInput p × DeclaredFollowerCarryCode p rate))
      inferInstance branchSpace
      (split : BootstrapPrivateRoundStreams.SourceInput p ×
        (BeginNumeratorCode p ⊕ DeclaredFollowerCarryCode p rate) →
          (BootstrapPrivateRoundStreams.SourceInput p × BeginNumeratorCode p) ⊕
            (BootstrapPrivateRoundStreams.SourceInput p × DeclaredFollowerCarryCode p rate)) :=
    split.measurable
  have hcompose : Measurable ((Sum.elim
      (fun x : BootstrapPrivateRoundStreams.SourceInput p × BeginNumeratorCode p =>
        beginFollowerCodeOfCarryCode (p := p) (rate := rate) block x.1 i
          (.inl x.2 : ActualInitializationBlockMeasurability.FollowerCarryCode p rate))
      (fun x : BootstrapPrivateRoundStreams.SourceInput p × DeclaredFollowerCarryCode p rate =>
        beginFollowerCodeOfCarryCode (p := p) (rate := rate) block x.1 i
          (.inr x.2 : ActualInitializationBlockMeasurability.FollowerCarryCode p rate))) ∘ split) :=
    hsum.comp hsplit
  have hrepresentation :
      (fun x : BootstrapPrivateRoundStreams.SourceInput p ×
          ActualInitializationBlockMeasurability.FollowerCarryCode p rate =>
        beginFollowerCodeOfCarryCode block x.1 i x.2) =
      (Sum.elim
        (fun x : BootstrapPrivateRoundStreams.SourceInput p × BeginNumeratorCode p =>
          beginFollowerCodeOfCarryCode (p := p) (rate := rate) block x.1 i
            (.inl x.2 : ActualInitializationBlockMeasurability.FollowerCarryCode p rate))
        (fun x : BootstrapPrivateRoundStreams.SourceInput p × DeclaredFollowerCarryCode p rate =>
          beginFollowerCodeOfCarryCode (p := p) (rate := rate) block x.1 i
            (.inr x.2 : ActualInitializationBlockMeasurability.FollowerCarryCode p rate))) ∘ split := by
    funext x
    rcases x with ⟨source, code⟩
    cases code with
    | inl numerators => rfl
    | inr declared => rfl
  rw [hrepresentation]
  exact hcompose

/-! ## Actual joint block-start code -/

/-- The actual `R.beginBlock` code is Borel on the accepted `BlockInput`.
Its carry dependence is read through `blockCarryCodeOf`, the same lossless
code that induces the existing carry measurable space. -/
theorem measurable_actualBeginBlockCodeOfInput {p : Parameters} {rate : RateInput p}
    {block : Fin (n_boot p)} {C_star C_h : ℝ} :
    Measurable (ActualInitializationBlockMeasurability.actualBeginBlockCodeOfInput
      (p := p) (rate := rate) (block := block) (C_star := C_star) (C_h := C_h)) := by
  have hblockCode : Measurable
      (ActualInitializationBlockMeasurability.blockInputCodeOf
        (p := p) (rate := rate) (block := block) (C_star := C_star) (C_h := C_h)) :=
    ActualInitializationBlockMeasurability.measurable_blockInputCodeOf
  have hfields : Measurable (fun input :
      ActualInitializationBlockMeasurability.BlockInput p rate block C_star C_h =>
        (ActualInitializationBlockMeasurability.blockInputCodeOf input).2.1) :=
    measurable_subtype_coe.comp (measurable_snd.comp hblockCode)
  have hcoordinates : Measurable (fun input :
      ActualInitializationBlockMeasurability.BlockInput p rate block C_star C_h =>
        ActualInitializationBlockMeasurability.blockCarryCodeFieldsCoordinates
          ((ActualInitializationBlockMeasurability.blockInputCodeOf input).2.1)) :=
    (comap_measurable _).comp hfields
  have hcarryFollowers : Measurable (fun input :
      ActualInitializationBlockMeasurability.BlockInput p rate block C_star C_h =>
        ((ActualInitializationBlockMeasurability.blockInputCodeOf input).2.1).followers) :=
    measurable_snd.comp (measurable_snd.comp hcoordinates)
  have hsource : Measurable (fun input :
      ActualInitializationBlockMeasurability.BlockInput p rate block C_star C_h =>
        (ActualInitializationBlockMeasurability.blockInputCodeOf input).1) :=
    measurable_fst.comp hblockCode
  have hcoordinatorInput : Measurable
      (ActualInitializationBlockMeasurability.coordinatorBeginBlockInputOfBlockInput
        (p := p) (rate := rate) (block := block) (C_star := C_star) (C_h := C_h)) :=
    ActualInitializationBlockMeasurability.measurable_coordinatorBeginBlockInputOfBlockInput
  have hcoordinatorCode :=
    (BootstrapCoordinatorRoundMeasurability.measurable_coordinatorBeginBlockCode p).comp
      hcoordinatorInput
  have hcoordinator : Measurable (fun input :
      ActualInitializationBlockMeasurability.BlockInput p rate block C_star C_h =>
        (BootstrapCoordinatorRoundMeasurability.coordinatorBeginBlockCode p
          (ActualInitializationBlockMeasurability.coordinatorBeginBlockInputOfBlockInput
            input)).2) := measurable_snd.comp hcoordinatorCode
  have hfollowers : Measurable (fun input :
      ActualInitializationBlockMeasurability.BlockInput p rate block C_star C_h =>
        fun i : Fin (p.m - 1) =>
          ActualInitializationBlockMeasurability.beginFollowerCodeOfCarry block input.1 i
            (input.2.1.followers i)) := by
    apply measurable_pi_iff.mpr
    intro i
    have hcodeAt : Measurable (fun input :
        ActualInitializationBlockMeasurability.BlockInput p rate block C_star C_h =>
          ((ActualInitializationBlockMeasurability.blockInputCodeOf input).2.1).followers i) :=
      (measurable_pi_apply i).comp hcarryFollowers
    have hstartedCode : Measurable (fun input :
        ActualInitializationBlockMeasurability.BlockInput p rate block C_star C_h =>
          beginFollowerCodeOfCarryCode block
            (ActualInitializationBlockMeasurability.blockInputCodeOf input).1 i
            (((ActualInitializationBlockMeasurability.blockInputCodeOf input).2.1).followers i)) :=
      (measurable_beginFollowerCodeOfCarryCode block i).comp (hsource.prodMk hcodeAt)
    have hsame : (fun input :
        ActualInitializationBlockMeasurability.BlockInput p rate block C_star C_h =>
          ActualInitializationBlockMeasurability.beginFollowerCodeOfCarry block input.1 i
            (input.2.1.followers i)) =
        (fun input => beginFollowerCodeOfCarryCode block
          (ActualInitializationBlockMeasurability.blockInputCodeOf input).1 i
          (((ActualInitializationBlockMeasurability.blockInputCodeOf input).2.1).followers i)) := by
      funext input
      exact (beginFollowerCodeOfCarryCode_followerCarryCodeOf block input.1 i
        (input.2.1.followers i)).symm
    rw [hsame]
    exact hstartedCode
  change Measurable (fun input :
      ActualInitializationBlockMeasurability.BlockInput p rate block C_star C_h =>
        ((BootstrapCoordinatorRoundMeasurability.coordinatorBeginBlockCode p
            (ActualInitializationBlockMeasurability.coordinatorBeginBlockInputOfBlockInput
              input)).2,
          fun i : Fin (p.m - 1) =>
            ActualInitializationBlockMeasurability.beginFollowerCodeOfCarry block input.1 i
              (input.2.1.followers i)))
  exact hcoordinator.prodMk hfollowers

/-- Borel composition of the actual block-start producer through any
measurable map into the same whole-source and actual-carry `BlockInput`. This
input is only a standard composition domain; it supplies no physical successor
or probability law. -/
theorem measurable_actualBeginBlockCodeOfInput_comp
    {p : Parameters} {rate : RateInput p} {block : Fin (n_boot p)}
    {C_star C_h : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    (input : Ω → ActualInitializationBlockMeasurability.BlockInput
      p rate block C_star C_h) (hinput : Measurable input) :
    Measurable
      (ActualInitializationBlockMeasurability.actualBeginBlockCodeOfInput
        (p := p) (rate := rate) (block := block) (C_star := C_star) (C_h := C_h) ∘
          input) :=
  measurable_actualBeginBlockCodeOfInput.comp hinput

/-- The exact accepted coordinator and every heterogeneous follower started
state reconstruct after composing the block-start code with any input map.
The reconstruction is pointwise and requires no law for the map. -/
theorem actualBeginBlockCodeOfInput_comp_reconstructs
    {p : Parameters} {rate : RateInput p} {block : Fin (n_boot p)}
    {C_star C_h : ℝ} {Ω : Type*}
    (input : Ω → ActualInitializationBlockMeasurability.BlockInput
      p rate block C_star C_h) :
    ∀ ω, BootstrapCoordinatorRoundMeasurability.assemblePrelaunch p
        (BootstrapCoordinatorRoundMeasurability.selectedCoordinatorBase p
          (input ω).1 C_star C_h)
        (ActualInitializationBlockMeasurability.actualBeginBlockCodeOfInput
          (input ω)).1 =
        (ActualInitializationRun.beginBlock p rate block (input ω).1
          (input ω).2.1).coordinator ∧
      (∀ i, ActualInitializationRoundMeasurability.followerStateOfCode p rate block
        ((ActualInitializationBlockMeasurability.actualBeginBlockCodeOfInput
          (input ω)).2 i) =
          (ActualInitializationRun.beginBlock p rate block (input ω).1
            (input ω).2.1).followers i) := by
  intro ω
  exact ActualInitializationBlockMeasurability.actualBeginBlockCodeOfInput_reconstructs
    (input ω)

end Bandits.Support.ActualInitializationBeginJointMeasurability

end
