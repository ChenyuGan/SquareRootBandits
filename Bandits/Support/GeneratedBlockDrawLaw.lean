/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceInitializationRun
public import Bandits.Support.ReferenceInitializationPrefixInvariance
public import Bandits.Support.ReferenceInitializationMeasurability
public import Bandits.Support.BootstrapPrivateRoundStreams
public import Bandits.Support.BootstrapPhysicalInput
public import Bandits.Support.PrivateSourceStreams
public import Bandits.Support.BootstrapBlockConstruction
public import Bandits.Support.BootstrapBlockIsolation
public import Bandits.Support.BootstrapWeightPotential

import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Tactic.NormNum

/-!
# Current block-start private draws on the generated reference run

For fixed public input, rounded rewards, row, and incoming boundary, this
module isolates exactly the current block's existing follower-triple profile
and coordinator target scalar from all other private coordinates.  The
generated boundary at the start of that block is a function of the other
coordinates, by the accepted run-prefix invariance theorem.  The current
profile remains latent labelled data when a follower has already activated or
the run has stopped; no physical action is asserted for such labels.

Sources: `sources/zip4/manuscript/07_public_setup.tex:27-40,63-112` and
`sources/zip4/manuscript/appendix_b_communication.tex:306-308,658-702`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal

open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.BootstrapWeightPotential
open Bandits.Support.BootstrapBlockConstruction
open Bandits.Support.BootstrapBlockIsolation
open Bandits.Support.PrivateSourceStreams
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.ReferenceInitializationRun

namespace Bandits.Support.GeneratedBlockDrawLaw

abbrev FollowerTripleProfile (p : Parameters) :=
  Fin (p.m - 1) → PrivateSourceStreams.BlockScalars

abbrev OtherBlockLabels (p : Parameters) (s : Fin (n_boot p)) :=
  {r : Fin (n_boot p) // ¬ (r = s)}

abbrev OtherFollowerBlocks (p : Parameters) (s : Fin (n_boot p)) :=
  (r : {r : Fin (n_boot p) // ¬ (r = s)}) → FollowerTripleProfile p

abbrev OtherTargetScalars (p : Parameters) (s : Fin (n_boot p)) :=
  (r : {r : Fin (n_boot p) // ¬ (r = s)}) → BootstrapPrivateRoundStreams.Scalar

/-- The coordinates retained outside this block's follower triples and target.
This includes the separate coordinator-J scalar and every original calendar
round scalar, including all rounds lying in block `s`. -/
abbrev OtherPrivateCoordinates (p : Parameters) (s : Fin (n_boot p)) :=
  ((OtherFollowerBlocks p s × PrivateSourceStreams.Scalar) ×
    BootstrapPrivateRoundStreams.PlayerRoundScalars p) × OtherTargetScalars p s

/-- The two current block-start coordinates whose law is established here. -/
abbrev CurrentBlockCoordinates (p : Parameters) :=
  FollowerTripleProfile p × BootstrapPrivateRoundStreams.Scalar

/-- The singleton fiber of the chosen block label as an explicit unit index. -/
def currentBlockLabelEquiv (p : Parameters) (s : Fin (n_boot p)) :
    {r : Fin (n_boot p) // r = s} ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨s, rfl⟩
  left_inv r := by
    apply Subtype.ext
    exact r.property.symm
  right_inv _ := rfl

/-- Split the accepted follower/block Pi space at exactly the labelled block.
The returned first coordinate keeps every other original block triple. -/
def followerBlocksSplitEquiv (p : Parameters) (s : Fin (n_boot p)) :
    PrivateSourceStreams.FollowerBlockInputs p ≃ᵐ
      (OtherFollowerBlocks p s × FollowerTripleProfile p) := by
  let ePi := MeasurableEquiv.piEquivPiSubtypeProd
      (fun _ : Fin (n_boot p) => FollowerTripleProfile p) (fun r => r = s)
  let eCurrent :
      ({r : Fin (n_boot p) // r = s} → FollowerTripleProfile p) ≃ᵐ
        FollowerTripleProfile p :=
    (MeasurableEquiv.piCongrLeft (fun _ : Unit => FollowerTripleProfile p)
      (currentBlockLabelEquiv p s)).trans
        (MeasurableEquiv.piUnique (fun _ : Unit => FollowerTripleProfile p))
  simpa [OtherFollowerBlocks, OtherBlockLabels] using
    ePi.trans <| (MeasurableEquiv.prodCongr eCurrent (MeasurableEquiv.refl _)).trans
      MeasurableEquiv.prodComm

/-- The block Pi split preserves its exact product of accepted triple laws. -/
theorem followerBlocksSplit_measurePreserving (p : Parameters)
    (s : Fin (n_boot p)) :
    MeasurePreserving (followerBlocksSplitEquiv p s)
      (PrivateSourceStreams.followerBlockInputsLaw p)
      ((Measure.pi (fun _ : OtherBlockLabels p s =>
          PrivateSourceStreams.blockScalarProfileLaw p)).prod
        (PrivateSourceStreams.blockScalarProfileLaw p)) := by
  let : Fintype {r : Fin (n_boot p) // r = s} :=
    Subtype.fintype (fun r : Fin (n_boot p) => r = s)
  let ePi := MeasurableEquiv.piEquivPiSubtypeProd
      (fun _ : Fin (n_boot p) => FollowerTripleProfile p) (fun r => r = s)
  let eCurrent :
      ({r : Fin (n_boot p) // r = s} → FollowerTripleProfile p) ≃ᵐ
        FollowerTripleProfile p :=
    (MeasurableEquiv.piCongrLeft (fun _ : Unit => FollowerTripleProfile p)
      (currentBlockLabelEquiv p s)).trans
        (MeasurableEquiv.piUnique (fun _ : Unit => FollowerTripleProfile p))
  have hPi : MeasurePreserving ePi
      (Measure.pi (fun _ : Fin (n_boot p) =>
        PrivateSourceStreams.blockScalarProfileLaw p))
      ((Measure.pi (fun r : {r : Fin (n_boot p) // r = s} =>
          PrivateSourceStreams.blockScalarProfileLaw p)).prod
        (Measure.pi (fun r : {r : Fin (n_boot p) // ¬ (r = s)} =>
          PrivateSourceStreams.blockScalarProfileLaw p))) := by
    exact measurePreserving_piEquivPiSubtypeProd
      (fun _ : Fin (n_boot p) => PrivateSourceStreams.blockScalarProfileLaw p)
      (fun r => r = s)
  have hReindex : MeasurePreserving
      (MeasurableEquiv.piCongrLeft (fun _ : Unit => FollowerTripleProfile p)
        (currentBlockLabelEquiv p s))
      (Measure.pi (fun _ : {r : Fin (n_boot p) // r = s} =>
        PrivateSourceStreams.blockScalarProfileLaw p))
      (Measure.pi (fun _ : Unit => PrivateSourceStreams.blockScalarProfileLaw p)) := by
    exact measurePreserving_piCongrLeft
      (fun _ : Unit => PrivateSourceStreams.blockScalarProfileLaw p)
      (currentBlockLabelEquiv p s)
  have hEval : MeasurePreserving
      (MeasurableEquiv.piUnique (fun _ : Unit => FollowerTripleProfile p))
      (Measure.pi (fun _ : Unit => PrivateSourceStreams.blockScalarProfileLaw p))
      (PrivateSourceStreams.blockScalarProfileLaw p) := by
    change MeasurePreserving (Function.eval ())
      (Measure.pi (fun _ : Unit => PrivateSourceStreams.blockScalarProfileLaw p)) _
    exact measurePreserving_eval
      (fun _ : Unit => PrivateSourceStreams.blockScalarProfileLaw p) ()
  have hCurrent := hEval.comp hReindex
  have hReorder : MeasurePreserving
      (MeasurableEquiv.prodCongr eCurrent (MeasurableEquiv.refl _)
        |>.trans MeasurableEquiv.prodComm)
      ((Measure.pi (fun _ : {r : Fin (n_boot p) // r = s} =>
          PrivateSourceStreams.blockScalarProfileLaw p)).prod
        (Measure.pi (fun r : {r : Fin (n_boot p) // ¬ (r = s)} =>
          PrivateSourceStreams.blockScalarProfileLaw p)))
      ((Measure.pi (fun r : {r : Fin (n_boot p) // ¬ (r = s)} =>
          PrivateSourceStreams.blockScalarProfileLaw p)).prod
        (PrivateSourceStreams.blockScalarProfileLaw p)) := by
    exact (hCurrent.prod (MeasurePreserving.id _)).trans Measure.measurePreserving_swap
  have hsource : PrivateSourceStreams.followerBlockInputsLaw p =
      Measure.pi (fun _ : Fin (n_boot p) =>
        PrivateSourceStreams.blockScalarProfileLaw p) := rfl
  rw [hsource]
  exact hReorder.comp hPi

/-- Split the target scalar Pi space at exactly the chosen block label. -/
def targetScalarsSplitEquiv (p : Parameters) (s : Fin (n_boot p)) :
    BootstrapPrivateRoundStreams.CoordinatorTargetScalars p ≃ᵐ
      (OtherTargetScalars p s × BootstrapPrivateRoundStreams.Scalar) := by
  let ePi := MeasurableEquiv.piEquivPiSubtypeProd
      (fun _ : Fin (n_boot p) => BootstrapPrivateRoundStreams.Scalar) (fun r => r = s)
  let eCurrent :
      ({r : Fin (n_boot p) // r = s} → BootstrapPrivateRoundStreams.Scalar) ≃ᵐ
        BootstrapPrivateRoundStreams.Scalar :=
    (MeasurableEquiv.piCongrLeft (fun _ : Unit => BootstrapPrivateRoundStreams.Scalar)
      (currentBlockLabelEquiv p s)).trans
        (MeasurableEquiv.piUnique (fun _ : Unit => BootstrapPrivateRoundStreams.Scalar))
  simpa [OtherTargetScalars, OtherBlockLabels] using
    ePi.trans <| (MeasurableEquiv.prodCongr eCurrent (MeasurableEquiv.refl _)).trans
      MeasurableEquiv.prodComm

theorem targetScalarsSplit_measurePreserving (p : Parameters)
    (s : Fin (n_boot p)) :
    MeasurePreserving (targetScalarsSplitEquiv p s)
      (BootstrapPrivateRoundStreams.coordinatorTargetScalarLaw p)
      ((Measure.pi (fun _ : OtherBlockLabels p s =>
          ContinuousCategorical.uniform)).prod ContinuousCategorical.uniform) := by
  let : Fintype {r : Fin (n_boot p) // r = s} :=
    Subtype.fintype (fun r : Fin (n_boot p) => r = s)
  let ePi := MeasurableEquiv.piEquivPiSubtypeProd
      (fun _ : Fin (n_boot p) => BootstrapPrivateRoundStreams.Scalar) (fun r => r = s)
  let eCurrent :
      ({r : Fin (n_boot p) // r = s} → BootstrapPrivateRoundStreams.Scalar) ≃ᵐ
        BootstrapPrivateRoundStreams.Scalar :=
    (MeasurableEquiv.piCongrLeft (fun _ : Unit => BootstrapPrivateRoundStreams.Scalar)
      (currentBlockLabelEquiv p s)).trans
        (MeasurableEquiv.piUnique (fun _ : Unit => BootstrapPrivateRoundStreams.Scalar))
  have hPi : MeasurePreserving ePi
      (Measure.pi (fun _ : Fin (n_boot p) => ContinuousCategorical.uniform))
      ((Measure.pi (fun r : {r : Fin (n_boot p) // r = s} =>
          ContinuousCategorical.uniform)).prod
        (Measure.pi (fun r : {r : Fin (n_boot p) // ¬ (r = s)} =>
          ContinuousCategorical.uniform))) := by
    exact measurePreserving_piEquivPiSubtypeProd
      (fun _ : Fin (n_boot p) => ContinuousCategorical.uniform) (fun r => r = s)
  have hReindex : MeasurePreserving
      (MeasurableEquiv.piCongrLeft (fun _ : Unit => BootstrapPrivateRoundStreams.Scalar)
        (currentBlockLabelEquiv p s))
      (Measure.pi (fun _ : {r : Fin (n_boot p) // r = s} =>
        ContinuousCategorical.uniform))
      (Measure.pi (fun _ : Unit => ContinuousCategorical.uniform)) := by
    exact measurePreserving_piCongrLeft
      (fun _ : Unit => ContinuousCategorical.uniform) (currentBlockLabelEquiv p s)
  have hEval : MeasurePreserving
      (MeasurableEquiv.piUnique (fun _ : Unit => BootstrapPrivateRoundStreams.Scalar))
      (Measure.pi (fun _ : Unit => ContinuousCategorical.uniform))
      ContinuousCategorical.uniform := by
    change MeasurePreserving (Function.eval ())
      (Measure.pi (fun _ : Unit => ContinuousCategorical.uniform)) _
    exact measurePreserving_eval (fun _ : Unit => ContinuousCategorical.uniform) ()
  have hCurrent := hEval.comp hReindex
  have hReorder : MeasurePreserving
      (MeasurableEquiv.prodCongr eCurrent (MeasurableEquiv.refl _)
        |>.trans MeasurableEquiv.prodComm)
      ((Measure.pi (fun _ : {r : Fin (n_boot p) // r = s} =>
          ContinuousCategorical.uniform)).prod
        (Measure.pi (fun r : {r : Fin (n_boot p) // ¬ (r = s)} => ContinuousCategorical.uniform)))
      ((Measure.pi (fun r : {r : Fin (n_boot p) // ¬ (r = s)} => ContinuousCategorical.uniform)).prod
        ContinuousCategorical.uniform) := by
    exact (hCurrent.prod (MeasurePreserving.id _)).trans Measure.measurePreserving_swap
  have hsource : BootstrapPrivateRoundStreams.coordinatorTargetScalarLaw p =
      Measure.pi (fun _ : Fin (n_boot p) => ContinuousCategorical.uniform) := rfl
  rw [hsource]
  exact hReorder.comp hPi

/-- Product law of the private coordinates outside the current block's two
draw-bearing fields. -/
def otherPrivateLaw (p : Parameters) (s : Fin (n_boot p)) :
    Measure (OtherPrivateCoordinates p s) :=
  (((Measure.pi (fun _ : OtherBlockLabels p s =>
      PrivateSourceStreams.blockScalarProfileLaw p)).prod
      ContinuousCategorical.uniform).prod
      (BootstrapPrivateRoundStreams.playerRoundScalarLaw p)).prod
    (Measure.pi (fun _ : OtherBlockLabels p s => ContinuousCategorical.uniform))

/-- The actual measurable coordinate equivalence. Its inverse restores the
original follower block Pi and target Pi coordinatewise; it does not create
new random variables or duplicate any original scalar. -/
def extendedPrivateBlockSplitEquiv (p : Parameters) (s : Fin (n_boot p)) :
    BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p ≃ᵐ
      (OtherPrivateCoordinates p s × CurrentBlockCoordinates p) := by
  let eBase : (PrivateSourceStreams.FollowerBlockInputs p ×
      PrivateSourceStreams.Scalar) ≃ᵐ
        ((OtherFollowerBlocks p s × FollowerTripleProfile p) ×
          PrivateSourceStreams.Scalar) :=
    MeasurableEquiv.prodCongr (followerBlocksSplitEquiv p s) (MeasurableEquiv.refl _)
  let eExtra : (BootstrapPrivateRoundStreams.PlayerRoundScalars p ×
      BootstrapPrivateRoundStreams.CoordinatorTargetScalars p) ≃ᵐ
        (BootstrapPrivateRoundStreams.PlayerRoundScalars p ×
          (OtherTargetScalars p s × BootstrapPrivateRoundStreams.Scalar)) :=
    MeasurableEquiv.prodCongr (MeasurableEquiv.refl _)
      (targetScalarsSplitEquiv p s)
  let eProduct := MeasurableEquiv.prodCongr eBase eExtra
  let ePrefix : ((OtherFollowerBlocks p s × FollowerTripleProfile p) ×
      PrivateSourceStreams.Scalar) ≃ᵐ
        ((OtherFollowerBlocks p s × PrivateSourceStreams.Scalar) ×
          FollowerTripleProfile p) :=
    MeasurableEquiv.prodAssoc.trans <|
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _) MeasurableEquiv.prodComm).trans
        MeasurableEquiv.prodAssoc.symm
  let eSuffix : (BootstrapPrivateRoundStreams.PlayerRoundScalars p ×
      (OtherTargetScalars p s × BootstrapPrivateRoundStreams.Scalar)) ≃ᵐ
        ((BootstrapPrivateRoundStreams.PlayerRoundScalars p × OtherTargetScalars p s) ×
          BootstrapPrivateRoundStreams.Scalar) := MeasurableEquiv.prodAssoc.symm
  let eMiddle : FollowerTripleProfile p ×
      (((BootstrapPrivateRoundStreams.PlayerRoundScalars p × OtherTargetScalars p s) ×
        BootstrapPrivateRoundStreams.Scalar)) ≃ᵐ
        ((BootstrapPrivateRoundStreams.PlayerRoundScalars p × OtherTargetScalars p s) ×
          (FollowerTripleProfile p × BootstrapPrivateRoundStreams.Scalar)) :=
    MeasurableEquiv.prodAssoc.symm.trans <|
      (MeasurableEquiv.prodCongr MeasurableEquiv.prodComm (MeasurableEquiv.refl _)).trans
        MeasurableEquiv.prodAssoc
  let eReorder : (((OtherFollowerBlocks p s × FollowerTripleProfile p) ×
      PrivateSourceStreams.Scalar) ×
      (BootstrapPrivateRoundStreams.PlayerRoundScalars p ×
        (OtherTargetScalars p s × BootstrapPrivateRoundStreams.Scalar))) ≃ᵐ
        (OtherPrivateCoordinates p s × CurrentBlockCoordinates p) := by
    exact (MeasurableEquiv.prodCongr ePrefix eSuffix).trans <|
      (MeasurableEquiv.prodAssoc.trans <|
        (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _) eMiddle).trans <|
          MeasurableEquiv.prodAssoc.symm.trans <|
            MeasurableEquiv.prodCongr MeasurableEquiv.prodAssoc.symm
              (MeasurableEquiv.refl _))
  exact eProduct.trans eReorder

/-- The split has exact inverse coordinate identities at every original label.
These equations fix the dependent coordinates as well as the visible Pi
entries. -/
theorem extendedPrivateBlockSplit_profile (p : Parameters)
    (s : Fin (n_boot p)) (rho : BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p) :
    (extendedPrivateBlockSplitEquiv p s rho).2.1 = rho.1.1 s := by
  simp [extendedPrivateBlockSplitEquiv, followerBlocksSplitEquiv,
    targetScalarsSplitEquiv, currentBlockLabelEquiv,
    MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd,
    MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft,
    MeasurableEquiv.piUnique, Equiv.piUnique, MeasurableEquiv.prodAssoc,
    MeasurableEquiv.prodComm, MeasurableEquiv.prodCongr]

theorem extendedPrivateBlockSplit_target (p : Parameters)
    (s : Fin (n_boot p)) (rho : BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p) :
    (extendedPrivateBlockSplitEquiv p s rho).2.2 = rho.2.2 s := by
  simp [extendedPrivateBlockSplitEquiv, followerBlocksSplitEquiv,
    targetScalarsSplitEquiv, currentBlockLabelEquiv,
    MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd,
    MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft,
    MeasurableEquiv.piUnique, Equiv.piUnique, MeasurableEquiv.prodAssoc,
    MeasurableEquiv.prodComm, MeasurableEquiv.prodCongr]

theorem extendedPrivateBlockSplit_other_block (p : Parameters)
    (s : Fin (n_boot p)) (rho : BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
    (r : OtherBlockLabels p s) :
    ((extendedPrivateBlockSplitEquiv p s rho).1.1.1.1 r,
      (extendedPrivateBlockSplitEquiv p s rho).2.1) =
        (rho.1.1 r.1, rho.1.1 s) := by
  simp [extendedPrivateBlockSplitEquiv, followerBlocksSplitEquiv,
    targetScalarsSplitEquiv, currentBlockLabelEquiv,
    MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd,
    MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft,
    MeasurableEquiv.piUnique, Equiv.piUnique, MeasurableEquiv.prodAssoc,
    MeasurableEquiv.prodComm, MeasurableEquiv.prodCongr]

theorem extendedPrivateBlockSplit_other_target (p : Parameters)
    (s : Fin (n_boot p)) (rho : BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
    (r : OtherBlockLabels p s) :
    ((extendedPrivateBlockSplitEquiv p s rho).1.2) r = rho.2.2 r.1 := by
  simp [extendedPrivateBlockSplitEquiv, followerBlocksSplitEquiv,
    targetScalarsSplitEquiv, currentBlockLabelEquiv,
    MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd,
    MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft,
    MeasurableEquiv.piUnique, Equiv.piUnique, MeasurableEquiv.prodAssoc,
    MeasurableEquiv.prodComm, MeasurableEquiv.prodCongr]

theorem extendedPrivateBlockSplit_round_scalars (p : Parameters)
    (s : Fin (n_boot p)) (rho : BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p) :
    (extendedPrivateBlockSplitEquiv p s rho).1.1.2 = rho.2.1 := by
  simp [extendedPrivateBlockSplitEquiv, followerBlocksSplitEquiv,
    targetScalarsSplitEquiv, currentBlockLabelEquiv,
    MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd,
    MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft,
    MeasurableEquiv.piUnique, Equiv.piUnique, MeasurableEquiv.prodAssoc,
    MeasurableEquiv.prodComm, MeasurableEquiv.prodCongr]

theorem extendedPrivateBlockSplit_coordinatorJ (p : Parameters)
    (s : Fin (n_boot p)) (rho : BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p) :
    (extendedPrivateBlockSplitEquiv p s rho).1.1.1.2 = rho.1.2 := by
  simp [extendedPrivateBlockSplitEquiv, followerBlocksSplitEquiv,
    targetScalarsSplitEquiv, currentBlockLabelEquiv,
    MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd,
    MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft,
    MeasurableEquiv.piUnique, Equiv.piUnique, MeasurableEquiv.prodAssoc,
    MeasurableEquiv.prodComm, MeasurableEquiv.prodCongr]

/-- The inverse restores both current draws, every other labelled block draw,
the original coordinator-J scalar, every calendar round scalar, and every
other target scalar at its original label. -/
theorem extendedPrivateBlockSplit_symm_currentProfile (p : Parameters)
    (s : Fin (n_boot p)) (w : OtherPrivateCoordinates p s)
    (profile : FollowerTripleProfile p) (target : BootstrapPrivateRoundStreams.Scalar) :
    ((extendedPrivateBlockSplitEquiv p s).symm (w, (profile, target))).1.1 s = profile := by
  let rho := (extendedPrivateBlockSplitEquiv p s).symm (w, (profile, target))
  have h := extendedPrivateBlockSplit_profile p s rho
  rw [show extendedPrivateBlockSplitEquiv p s rho = (w, (profile, target)) from
    (extendedPrivateBlockSplitEquiv p s).apply_symm_apply _] at h
  simpa [rho] using h.symm

theorem extendedPrivateBlockSplit_symm_currentTarget (p : Parameters)
    (s : Fin (n_boot p)) (w : OtherPrivateCoordinates p s)
    (profile : FollowerTripleProfile p) (target : BootstrapPrivateRoundStreams.Scalar) :
    ((extendedPrivateBlockSplitEquiv p s).symm (w, (profile, target))).2.2 s = target := by
  let rho := (extendedPrivateBlockSplitEquiv p s).symm (w, (profile, target))
  have h := extendedPrivateBlockSplit_target p s rho
  rw [show extendedPrivateBlockSplitEquiv p s rho = (w, (profile, target)) from
    (extendedPrivateBlockSplitEquiv p s).apply_symm_apply _] at h
  simpa [rho] using h.symm

theorem extendedPrivateBlockSplit_symm_otherBlock (p : Parameters)
    (s : Fin (n_boot p)) (w : OtherPrivateCoordinates p s)
    (profile : FollowerTripleProfile p) (target : BootstrapPrivateRoundStreams.Scalar)
    (r : OtherBlockLabels p s) :
    ((extendedPrivateBlockSplitEquiv p s).symm (w, (profile, target))).1.1 r.1 =
      w.1.1.1 r := by
  let rho := (extendedPrivateBlockSplitEquiv p s).symm (w, (profile, target))
  have h := congrArg Prod.fst (extendedPrivateBlockSplit_other_block p s rho r)
  rw [show extendedPrivateBlockSplitEquiv p s rho = (w, (profile, target)) from
    (extendedPrivateBlockSplitEquiv p s).apply_symm_apply _] at h
  simpa [rho] using h.symm

theorem extendedPrivateBlockSplit_symm_otherTarget (p : Parameters)
    (s : Fin (n_boot p)) (w : OtherPrivateCoordinates p s)
    (profile : FollowerTripleProfile p) (target : BootstrapPrivateRoundStreams.Scalar)
    (r : OtherBlockLabels p s) :
    ((extendedPrivateBlockSplitEquiv p s).symm (w, (profile, target))).2.2 r.1 = w.2 r := by
  let rho := (extendedPrivateBlockSplitEquiv p s).symm (w, (profile, target))
  have h := extendedPrivateBlockSplit_other_target p s rho r
  rw [show extendedPrivateBlockSplitEquiv p s rho = (w, (profile, target)) from
    (extendedPrivateBlockSplitEquiv p s).apply_symm_apply _] at h
  simpa [rho] using h.symm

theorem extendedPrivateBlockSplit_symm_roundScalars (p : Parameters)
    (s : Fin (n_boot p)) (w : OtherPrivateCoordinates p s)
    (profile : FollowerTripleProfile p) (target : BootstrapPrivateRoundStreams.Scalar) :
    ((extendedPrivateBlockSplitEquiv p s).symm (w, (profile, target))).2.1 = w.1.2 := by
  let rho := (extendedPrivateBlockSplitEquiv p s).symm (w, (profile, target))
  have h := extendedPrivateBlockSplit_round_scalars p s rho
  rw [show extendedPrivateBlockSplitEquiv p s rho = (w, (profile, target)) from
    (extendedPrivateBlockSplitEquiv p s).apply_symm_apply _] at h
  simpa [rho] using h.symm

theorem extendedPrivateBlockSplit_symm_coordinatorJ (p : Parameters)
    (s : Fin (n_boot p)) (w : OtherPrivateCoordinates p s)
    (profile : FollowerTripleProfile p) (target : BootstrapPrivateRoundStreams.Scalar) :
    ((extendedPrivateBlockSplitEquiv p s).symm (w, (profile, target))).1.2 =
      w.1.1.2 := by
  let rho := (extendedPrivateBlockSplitEquiv p s).symm (w, (profile, target))
  have h := extendedPrivateBlockSplit_coordinatorJ p s rho
  rw [show extendedPrivateBlockSplitEquiv p s rho = (w, (profile, target)) from
    (extendedPrivateBlockSplitEquiv p s).apply_symm_apply _] at h
  simpa [rho] using h.symm

theorem extendedPrivateBlockSplit_measurePreserving (p : Parameters)
    (s : Fin (n_boot p)) :
    MeasurePreserving (extendedPrivateBlockSplitEquiv p s)
      (BootstrapPrivateRoundStreams.extendedPrivateLaw p)
      ((otherPrivateLaw p s).prod
        ((PrivateSourceStreams.blockScalarProfileLaw p).prod
          ContinuousCategorical.uniform)) := by
  let μO := Measure.pi (fun _ : OtherBlockLabels p s =>
    PrivateSourceStreams.blockScalarProfileLaw p)
  let μP := PrivateSourceStreams.blockScalarProfileLaw p
  let μJ := PrivateSourceStreams.coordinatorScalarLaw
  let μR := BootstrapPrivateRoundStreams.playerRoundScalarLaw p
  let μOT := Measure.pi (fun _ : OtherBlockLabels p s => ContinuousCategorical.uniform)
  let μU := ContinuousCategorical.uniform
  let hBase := (followerBlocksSplit_measurePreserving p s).prod
    (MeasurePreserving.id PrivateSourceStreams.coordinatorScalarLaw)
  let hExtra := (MeasurePreserving.id
      (BootstrapPrivateRoundStreams.playerRoundScalarLaw p)).prod
    (targetScalarsSplit_measurePreserving p s)
  let hSource := hBase.prod hExtra
  have hPrefixAssoc : MeasurePreserving MeasurableEquiv.prodAssoc
      ((μO.prod μP).prod μJ) (μO.prod (μP.prod μJ)) := by
    exact measurePreserving_prodAssoc μO μP μJ
  have hPrefixSwap : MeasurePreserving
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _)
        MeasurableEquiv.prodComm)
      (μO.prod (μP.prod μJ)) (μO.prod (μJ.prod μP)) := by
    exact (MeasurePreserving.id _).prod Measure.measurePreserving_swap
  have hPrefixAssocBack : MeasurePreserving MeasurableEquiv.prodAssoc.symm
      (μO.prod (μJ.prod μP)) ((μO.prod μJ).prod μP) := by
    exact (measurePreserving_prodAssoc μO μJ μP).symm
  have hPrefix := hPrefixAssocBack.comp (hPrefixSwap.comp hPrefixAssoc)
  have hSuffix : MeasurePreserving MeasurableEquiv.prodAssoc.symm
      (μR.prod (μOT.prod μU)) ((μR.prod μOT).prod μU) := by
    exact (measurePreserving_prodAssoc μR μOT μU).symm
  have hFirst := (hPrefix.prod hSuffix).comp hSource
  have hMiddleAssoc : MeasurePreserving MeasurableEquiv.prodAssoc
      (((μO.prod μJ).prod μP).prod ((μR.prod μOT).prod μU))
      ((μO.prod μJ).prod (μP.prod ((μR.prod μOT).prod μU))) := by
    exact measurePreserving_prodAssoc (μO.prod μJ) μP ((μR.prod μOT).prod μU)
  have hMiddleAssocTo : MeasurePreserving MeasurableEquiv.prodAssoc.symm
      (μP.prod ((μR.prod μOT).prod μU)) ((μP.prod (μR.prod μOT)).prod μU) := by
    exact (measurePreserving_prodAssoc μP (μR.prod μOT) μU).symm
  have hMiddleSwap : MeasurePreserving
      (MeasurableEquiv.prodCongr MeasurableEquiv.prodComm (MeasurableEquiv.refl _))
      ((μP.prod (μR.prod μOT)).prod μU)
      (((μR.prod μOT).prod μP).prod μU) := by
    exact Measure.measurePreserving_swap.prod (MeasurePreserving.id _)
  have hMiddleAssocBack : MeasurePreserving MeasurableEquiv.prodAssoc
      (((μR.prod μOT).prod μP).prod μU)
      ((μR.prod μOT).prod (μP.prod μU)) := by
    exact measurePreserving_prodAssoc (μR.prod μOT) μP μU
  have hMiddle := hMiddleAssocBack.comp (hMiddleSwap.comp hMiddleAssocTo)
  have hMiddleFull := (MeasurePreserving.id (μO.prod μJ)).prod hMiddle
  have hOuterAssocBack : MeasurePreserving MeasurableEquiv.prodAssoc.symm
      ((μO.prod μJ).prod ((μR.prod μOT).prod (μP.prod μU)))
      (((μO.prod μJ).prod (μR.prod μOT)).prod (μP.prod μU)) := by
    exact (measurePreserving_prodAssoc (μO.prod μJ) (μR.prod μOT) (μP.prod μU)).symm
  have hInnerAssocBack : MeasurePreserving
      (MeasurableEquiv.prodCongr MeasurableEquiv.prodAssoc.symm
        (MeasurableEquiv.refl _))
      (((μO.prod μJ).prod (μR.prod μOT)).prod (μP.prod μU))
      ((((μO.prod μJ).prod μR).prod μOT).prod (μP.prod μU)) := by
    exact ((measurePreserving_prodAssoc (μO.prod μJ) μR μOT).symm).prod
      (MeasurePreserving.id _)
  have hFinal := hInnerAssocBack.comp <| hOuterAssocBack.comp <|
    hMiddleFull.comp <| hMiddleAssoc.comp hFirst
  convert hFinal using 1 <;> rfl

/-- Fix every public, row, reward and scalar parameter exactly as in the
accepted reference-run input. -/
def fixedReferenceInput (p : Parameters) (ids : CompletePublicTable.IDArray p)
    (row : CompletePublicTable.CompleteRow p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (rho : BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p) :
    ReferenceInitializationRun.Input p where
  ids := ids
  row := row
  rewards := rewards
  coordinates := rho
  C_star := C_star
  C_h := C_h
  eta := eta

/-- The actual generated reference boundary at block opportunity `s`. -/
def generatedBoundary (p : Parameters) (s : Fin (n_boot p))
    (ids : CompletePublicTable.IDArray p) (row : CompletePublicTable.CompleteRow p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (rho : BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p) :
    ReferenceInitializationRun.Boundary p :=
  ReferenceInitializationRun.run (fixedReferenceInput p ids row rewards C_star C_h eta rho)
    s.val

/-- The existing block-draw map on the full original follower label set. For
an activated follower or a stopped run, entries remain latent labelled data. -/
def generatedCurrentBlockProfile (p : Parameters) (s : Fin (n_boot p))
    (b : ReferenceInitializationRun.Boundary p)
    (rho : BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p) :
    PrivateSourceStreams.BlockDrawProfile p :=
  PrivateSourceStreams.blockDrawProfileMap p b.numerators b.weight_ge_one
    (rho.1.1 s)

/-- The current target arm from its original separately-labelled scalar. -/
def generatedCurrentTarget (p : Parameters) (s : Fin (n_boot p))
    (rho : BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p) : Fin p.K :=
  BootstrapPrivateRoundStreams.coordinatorTargetDraw p (rho.2.2 s)

/-- The run at opportunity `s.val` is constant on each fiber of the genuine
current-block coordinate split. The proof invokes the accepted read-set
comparison on the original labels. In particular, the comparison retains the
stopped branch after an earlier launch. -/
theorem generatedBoundary_eq_of_same_otherCoordinates (p : Parameters)
    (s : Fin (n_boot p)) (ids : CompletePublicTable.IDArray p)
    (row : CompletePublicTable.CompleteRow p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (rho tau : BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
    (hrest : (extendedPrivateBlockSplitEquiv p s rho).1 =
      (extendedPrivateBlockSplitEquiv p s tau).1) :
    generatedBoundary p s ids row rewards C_star C_h eta rho =
      generatedBoundary p s ids row rewards C_star C_h eta tau := by
  let x := fixedReferenceInput p ids row rewards C_star C_h eta rho
  let y := fixedReferenceInput p ids row rewards C_star C_h eta tau
  have hblocks : ∀ r : Fin (n_boot p), r.val < s.val →
      rho.1.1 r = tau.1.1 r := by
    intro r hr
    have hne : r ≠ s := by
      intro he
      subst r
      omega
    let rr : OtherBlockLabels p s := ⟨r, hne⟩
    have hO := congrArg (fun w : OtherPrivateCoordinates p s => w.1.1.1) hrest
    have hO' := congrFun hO rr
    have hrho := congrArg Prod.fst (extendedPrivateBlockSplit_other_block p s rho rr)
    have htau := congrArg Prod.fst (extendedPrivateBlockSplit_other_block p s tau rr)
    calc
      rho.1.1 r = (extendedPrivateBlockSplitEquiv p s rho).1.1.1.1 rr := hrho.symm
      _ = (extendedPrivateBlockSplitEquiv p s tau).1.1.1.1 rr := hO'
      _ = tau.1.1 r := htau
  have htargets : ∀ r : Fin (n_boot p), r.val < s.val →
      rho.2.2 r = tau.2.2 r := by
    intro r hr
    have hne : r ≠ s := by
      intro he
      subst r
      omega
    let rr : OtherBlockLabels p s := ⟨r, hne⟩
    have hO := congrArg (fun w : OtherPrivateCoordinates p s => w.2) hrest
    have hO' := congrFun hO rr
    have hrho := extendedPrivateBlockSplit_other_target p s rho rr
    have htau := extendedPrivateBlockSplit_other_target p s tau rr
    calc
      rho.2.2 r = (extendedPrivateBlockSplitEquiv p s rho).1.2 rr := hrho.symm
      _ = (extendedPrivateBlockSplitEquiv p s tau).1.2 rr := hO'
      _ = tau.2.2 r := htau
  have hrounds : ∀ i : Fin p.m, ∀ t : Fin p.T,
      rho.2.1 (i, t) = tau.2.1 (i, t) := by
    have hR := congrArg (fun w : OtherPrivateCoordinates p s => w.1.2) hrest
    intro i t
    exact congrFun hR (i, t)
  have hprefix : ReferenceInitializationCausality.runPrefixInputEq x y s.val := by
    refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
    · intro t ht
      exact ⟨fun _ => rfl, rfl⟩
    · intro r hr j
      exact congrFun (hblocks r hr) j
    · intro r hr
      exact htargets r hr
    · intro i t ht
      exact hrounds i t
  exact ReferenceInitializationPrefixInvariance.run_eq_of_runPrefixInputEq x y s.val hprefix

/-- The accepted generated boundary is a measurable map of the original
extended private coordinates. Its singleton atoms therefore use the complete
countable boundary encoding proved by `ReferenceInitializationMeasurability`.
-/
theorem measurable_generatedBoundary (p : Parameters) (s : Fin (n_boot p))
    (ids : CompletePublicTable.IDArray p) (row : CompletePublicTable.CompleteRow p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) :
    Measurable (generatedBoundary p s ids row rewards C_star C_h eta) := by
  have hcoords : Measurable (fun rho : BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p =>
      (ids, (row, rho)) : BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p →
        ReferenceInitializationMeasurability.InputCoordinates p) :=
    measurable_const.prodMk (measurable_const.prodMk measurable_id)
  change Measurable (fun rho => ReferenceInitializationRun.run
    (ReferenceInitializationMeasurability.inputOfCoordinates p C_star C_h eta rewards
      (ids, (row, rho))) s.val)
  exact (ReferenceInitializationMeasurability.measurable_run p C_star C_h eta rewards s.val).comp
    hcoords

theorem measurable_generatedBoundary_atom (p : Parameters) (s : Fin (n_boot p))
    (ids : CompletePublicTable.IDArray p) (row : CompletePublicTable.CompleteRow p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (b : ReferenceInitializationRun.Boundary p) :
    MeasurableSet {rho : BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p |
      generatedBoundary p s ids row rewards C_star C_h eta rho = b} := by
  exact (measurable_generatedBoundary p s ids row rewards C_star C_h eta)
    (measurableSet_singleton b)

/-- A concrete point in the genuine current-coordinate carrier, used only as a
section of the measurable coordinate equivalence. The invariance theorem
proves that the generated prefix boundary is independent of this section; it
does not assert any future physical play at these scalar values. -/
def zeroScalar : BootstrapPrivateRoundStreams.Scalar := ⟨0, by norm_num⟩

def zeroCurrentBlockCoordinates (p : Parameters) : CurrentBlockCoordinates p :=
  (fun _ => (zeroScalar, zeroScalar, zeroScalar), zeroScalar)

/-- The run-prefix boundary represented on the retained-coordinate space via
the explicit coordinate section. By the proved fiber invariance, its value is
the actual generated boundary for every possible current draw pair. -/
def boundaryFromOther (p : Parameters) (s : Fin (n_boot p))
    (ids : CompletePublicTable.IDArray p) (row : CompletePublicTable.CompleteRow p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (w : OtherPrivateCoordinates p s) :
    ReferenceInitializationRun.Boundary p :=
  generatedBoundary p s ids row rewards C_star C_h eta
    ((extendedPrivateBlockSplitEquiv p s).symm (w, zeroCurrentBlockCoordinates p))

theorem generatedBoundary_eq_boundaryFromOther (p : Parameters)
    (s : Fin (n_boot p)) (ids : CompletePublicTable.IDArray p)
    (row : CompletePublicTable.CompleteRow p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (rho : BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p) :
    generatedBoundary p s ids row rewards C_star C_h eta rho =
      boundaryFromOther p s ids row rewards C_star C_h eta
        (extendedPrivateBlockSplitEquiv p s rho).1 := by
  let tau := (extendedPrivateBlockSplitEquiv p s).symm
    ((extendedPrivateBlockSplitEquiv p s rho).1, zeroCurrentBlockCoordinates p)
  have hrest : (extendedPrivateBlockSplitEquiv p s rho).1 =
      (extendedPrivateBlockSplitEquiv p s tau).1 := by
    rw [show extendedPrivateBlockSplitEquiv p s tau =
        ((extendedPrivateBlockSplitEquiv p s rho).1, zeroCurrentBlockCoordinates p) from
          (extendedPrivateBlockSplitEquiv p s).apply_symm_apply _]
  exact generatedBoundary_eq_of_same_otherCoordinates p s ids row rewards C_star C_h eta
    rho tau hrest

theorem measurable_boundaryFromOther (p : Parameters) (s : Fin (n_boot p))
    (ids : CompletePublicTable.IDArray p) (row : CompletePublicTable.CompleteRow p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) :
    Measurable (boundaryFromOther p s ids row rewards C_star C_h eta) := by
  have hcoordinates : Measurable
      (fun w : OtherPrivateCoordinates p s =>
        (ids, (row, (extendedPrivateBlockSplitEquiv p s).symm
          (w, zeroCurrentBlockCoordinates p)))) := by
    exact measurable_const.prodMk <| measurable_const.prodMk <|
      (extendedPrivateBlockSplitEquiv p s).symm.measurable.comp
        (measurable_id.prodMk measurable_const)
  change Measurable (fun w => ReferenceInitializationRun.run
    (ReferenceInitializationMeasurability.inputOfCoordinates p C_star C_h eta rewards
      (ids, (row, (extendedPrivateBlockSplitEquiv p s).symm
        (w, zeroCurrentBlockCoordinates p)))) s.val)
  exact (ReferenceInitializationMeasurability.measurable_run p C_star C_h eta rewards s.val).comp
    hcoordinates

theorem measurable_boundaryFromOther_atom (p : Parameters) (s : Fin (n_boot p))
    (ids : CompletePublicTable.IDArray p) (row : CompletePublicTable.CompleteRow p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (b : ReferenceInitializationRun.Boundary p) :
    MeasurableSet {w : OtherPrivateCoordinates p s |
      boundaryFromOther p s ids row rewards C_star C_h eta w = b} := by
  exact (measurable_boundaryFromOther p s ids row rewards C_star C_h eta)
    (measurableSet_singleton b)

theorem measurable_generatedCurrentBlockProfile (p : Parameters)
    (s : Fin (n_boot p)) (b : ReferenceInitializationRun.Boundary p) :
    Measurable (generatedCurrentBlockProfile p s b) := by
  exact (PrivateSourceStreams.measurable_blockDrawProfileMap p b.numerators
    b.weight_ge_one).comp ((measurable_pi_apply s).comp (measurable_fst.comp measurable_fst))

theorem measurable_generatedCurrentTarget (p : Parameters) (s : Fin (n_boot p)) :
    Measurable (generatedCurrentTarget p s) := by
  change Measurable (BootstrapPhysicalInput.targetArmMap p s)
  exact BootstrapPhysicalInput.measurable_targetArmMap p s

/-- The actual generated-boundary/current-labelled-profile/current-target
event. The profile is always the complete original follower-labelled output
of `blockDrawProfileMap`; its uninstantiated entries are latent data. -/
def generatedBoundaryDrawEvent (p : Parameters) (s : Fin (n_boot p))
    (ids : CompletePublicTable.IDArray p) (row : CompletePublicTable.CompleteRow p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (b : ReferenceInitializationRun.Boundary p)
    (c : PrivateSourceStreams.BlockDrawProfile p) (z : Fin p.K) :
    Set (BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p) :=
  {rho | generatedBoundary p s ids row rewards C_star C_h eta rho = b ∧
    generatedCurrentBlockProfile p s b rho = c ∧ generatedCurrentTarget p s rho = z}

theorem measurableSet_generatedBoundaryDrawEvent (p : Parameters)
    (s : Fin (n_boot p)) (ids : CompletePublicTable.IDArray p)
    (row : CompletePublicTable.CompleteRow p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (b : ReferenceInitializationRun.Boundary p)
    (c : PrivateSourceStreams.BlockDrawProfile p) (z : Fin p.K) :
    MeasurableSet (generatedBoundaryDrawEvent p s ids row rewards C_star C_h eta b c z) := by
  change MeasurableSet {rho |
    generatedBoundary p s ids row rewards C_star C_h eta rho = b ∧
      generatedCurrentBlockProfile p s b rho = c ∧ generatedCurrentTarget p s rho = z}
  exact (measurable_generatedBoundary_atom p s ids row rewards C_star C_h eta b).inter
    ((measurableSet_eq_fun (measurable_generatedCurrentBlockProfile p s b)
      measurable_const).inter
      (measurableSet_eq_fun (measurable_generatedCurrentTarget p s)
        measurable_const))

/-- Exact ENNReal product-of-PMF formula for the accepted follower profile
atom at the boundary's visible positive numerator state. -/
theorem privateBlockProfileLaw_atom_expanded (p : Parameters)
    (n : Fin (p.m - 1) → Fin p.K → ℕ)
    (hn : ∀ j a, 1 ≤ BootstrapWeightPotential.weight (b_N p) (n j) a)
    (c : PrivateSourceStreams.BlockDrawProfile p) :
    BootstrapBlockIsolation.privateBlockProfileLaw p n hn c =
      ∏ j : Fin (p.m - 1), ENNReal.ofReal
        (BootstrapBlockConstruction.activityProbability p (c j).1 *
          BootstrapWeightPotential.probability (b_N p) (n j) (c j).2.1 *
          BootstrapBlockConstruction.privateIdProbability p (c j).2.2) := by
  rw [BootstrapBlockIsolation.privateBlockProfileLaw_apply]
  apply Finset.prod_congr rfl
  intro j hj
  rw [BootstrapBlockConstruction.privateBlockDrawLaw_apply,
    BootstrapBlockConstruction.privateDrawMass]

/-- The preceding atom expanded through the source Bernoulli, state-dependent
held-arm mixture and uniform-ID definitions. The target remains a separate
factor `ENNReal.ofReal (1 / K)`. -/
theorem privateBlockProfileLaw_atom_fully_expanded (p : Parameters)
    (n : Fin (p.m - 1) → Fin p.K → ℕ)
    (hn : ∀ j a, 1 ≤ BootstrapWeightPotential.weight (b_N p) (n j) a)
    (c : PrivateSourceStreams.BlockDrawProfile p) :
    BootstrapBlockIsolation.privateBlockProfileLaw p n hn c =
      ∏ j : Fin (p.m - 1), ENNReal.ofReal
        (((if (c j).1 then 1 / (p.m : ℝ) else 1 - 1 / (p.m : ℝ)) *
          ((BootstrapWeightPotential.weight (b_N p) (n j) (c j).2.1 /
              BootstrapWeightPotential.total (b_N p) (n j) +
                1 / (p.K : ℝ)) / 2)) *
          (1 / (A_id p : ℝ))) := by
  rw [privateBlockProfileLaw_atom_expanded]
  apply Finset.prod_congr rfl
  intro j hj
  simp [BootstrapBlockConstruction.activityProbability,
    BootstrapBlockConstruction.privateIdProbability,
    BootstrapWeightPotential.probability]

/-- Unnormalized atom factorization at the actual generated block boundary.
The `run = b` atom is not assumed positive; this equality includes zero-mass
boundary atoms. The follower factor is the exact accepted PMF atom, and the
target factor is the actual uniform law of its separately-labelled scalar. -/
theorem generatedBoundary_currentProfile_target_atom (p : Parameters)
    (s : Fin (n_boot p)) (ids : CompletePublicTable.IDArray p)
    (row : CompletePublicTable.CompleteRow p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (b : ReferenceInitializationRun.Boundary p)
    (c : PrivateSourceStreams.BlockDrawProfile p) (z : Fin p.K) :
    BootstrapPrivateRoundStreams.extendedPrivateLaw p
      (generatedBoundaryDrawEvent p s ids row rewards C_star C_h eta b c z) =
      BootstrapPrivateRoundStreams.extendedPrivateLaw p
        {rho | generatedBoundary p s ids row rewards C_star C_h eta rho = b} *
        BootstrapBlockIsolation.privateBlockProfileLaw p b.numerators b.weight_ge_one c *
        ENNReal.ofReal (1 / (p.K : ℝ)) := by
  let e := extendedPrivateBlockSplitEquiv p s
  let restEvent : Set (OtherPrivateCoordinates p s) :=
    {w | boundaryFromOther p s ids row rewards C_star C_h eta w = b}
  let profileEvent : Set (FollowerTripleProfile p) :=
    {x | PrivateSourceStreams.blockDrawProfileMap p b.numerators b.weight_ge_one x = c}
  let targetEvent : Set BootstrapPrivateRoundStreams.Scalar :=
    {u | BootstrapPrivateRoundStreams.coordinatorTargetDraw p u = z}
  let splitEvent : Set (OtherPrivateCoordinates p s ×
      (FollowerTripleProfile p × BootstrapPrivateRoundStreams.Scalar)) :=
    restEvent ×ˢ (profileEvent ×ˢ targetEvent)
  have hprofileEventMeasurable : MeasurableSet profileEvent := by
    change MeasurableSet {x | PrivateSourceStreams.blockDrawProfileMap p
      b.numerators b.weight_ge_one x = c}
    exact measurableSet_eq_fun
      (PrivateSourceStreams.measurable_blockDrawProfileMap p b.numerators b.weight_ge_one)
      measurable_const
  have htargetEventMeasurable : MeasurableSet targetEvent := by
    change MeasurableSet (BootstrapPrivateRoundStreams.fullArmScalarDraw p ⁻¹' {z})
    exact measurableSet_preimage
      (BootstrapPrivateRoundStreams.measurable_fullArmScalarDraw p)
      (measurableSet_singleton z)
  have hsplitEventMeasurable : MeasurableSet splitEvent :=
    MeasurableSet.prod (measurable_boundaryFromOther_atom p s ids row rewards C_star C_h eta b)
      (MeasurableSet.prod hprofileEventMeasurable htargetEventMeasurable)
  have hsplit := extendedPrivateBlockSplit_measurePreserving p s
  have hsplitEvent : e ⁻¹' splitEvent =
      generatedBoundaryDrawEvent p s ids row rewards C_star C_h eta b c z := by
    ext rho
    change (boundaryFromOther p s ids row rewards C_star C_h eta (e rho).1 = b ∧
      PrivateSourceStreams.blockDrawProfileMap p b.numerators b.weight_ge_one
        (e rho).2.1 = c ∧
      BootstrapPrivateRoundStreams.coordinatorTargetDraw p (e rho).2.2 = z) ↔
        (generatedBoundary p s ids row rewards C_star C_h eta rho = b ∧
          generatedCurrentBlockProfile p s b rho = c ∧
          generatedCurrentTarget p s rho = z)
    rw [← generatedBoundary_eq_boundaryFromOther p s ids row rewards C_star C_h eta rho,
      extendedPrivateBlockSplit_profile p s rho,
      extendedPrivateBlockSplit_target p s rho]
    simp [generatedCurrentBlockProfile, generatedCurrentTarget]
  have hsplitBoundary : e ⁻¹' (restEvent ×ˢ
      (Set.univ : Set (CurrentBlockCoordinates p))) =
      {rho | generatedBoundary p s ids row rewards C_star C_h eta rho = b} := by
    ext rho
    simp only [Set.mem_preimage, restEvent, Set.mem_prod, Set.mem_univ,
      Set.mem_ofPred_eq]
    rw [← generatedBoundary_eq_boundaryFromOther p s ids row rewards C_star C_h eta rho]
    simp
  have hrestMeasurable : MeasurableSet restEvent :=
    measurable_boundaryFromOther_atom p s ids row rewards C_star C_h eta b
  have hsplitBoundaryMeasurable : MeasurableSet (restEvent ×ˢ
      (Set.univ : Set (CurrentBlockCoordinates p))) :=
    MeasurableSet.prod hrestMeasurable MeasurableSet.univ
  have hboundaryMass : BootstrapPrivateRoundStreams.extendedPrivateLaw p
      {rho | generatedBoundary p s ids row rewards C_star C_h eta rho = b} =
      otherPrivateLaw p s restEvent := by
    calc
      _ = (BootstrapPrivateRoundStreams.extendedPrivateLaw p).map e
          (restEvent ×ˢ (Set.univ : Set (CurrentBlockCoordinates p))) := by
            symm
            rw [Measure.map_apply hsplit.measurable hsplitBoundaryMeasurable]
            rw [hsplitBoundary]
      _ = (((otherPrivateLaw p s).prod
          ((PrivateSourceStreams.blockScalarProfileLaw p).prod
            ContinuousCategorical.uniform))
            (restEvent ×ˢ (Set.univ : Set (CurrentBlockCoordinates p)))) := by
            rw [hsplit.map_eq]
      _ = otherPrivateLaw p s restEvent := by
            rw [Measure.prod_prod, measure_univ]
            exact mul_one _
  have hprofileMass : PrivateSourceStreams.blockScalarProfileLaw p profileEvent =
      BootstrapBlockIsolation.privateBlockProfileLaw p b.numerators b.weight_ge_one c := by
    calc
      _ = (PrivateSourceStreams.blockScalarProfileLaw p).map
          (PrivateSourceStreams.blockDrawProfileMap p b.numerators b.weight_ge_one) {c} := by
            symm
            exact Measure.map_apply
              (PrivateSourceStreams.measurable_blockDrawProfileMap p b.numerators
                b.weight_ge_one) (measurableSet_singleton c)
      _ = (BootstrapBlockIsolation.privateBlockProfileLaw p b.numerators
          b.weight_ge_one).toMeasure {c} := by
            rw [PrivateSourceStreams.blockDrawProfileMap_law]
      _ = BootstrapBlockIsolation.privateBlockProfileLaw p b.numerators
          b.weight_ge_one c :=
            PMF.toMeasure_apply_singleton _ c (measurableSet_singleton c)
  have htargetMass : ContinuousCategorical.uniform targetEvent =
      ENNReal.ofReal (1 / (p.K : ℝ)) := by
    change ContinuousCategorical.uniform
      (BootstrapPrivateRoundStreams.fullArmScalarDraw p ⁻¹' {z}) = _
    exact BootstrapPrivateRoundStreams.fullArmScalarDraw_uniform_atom p z
  calc
    _ = (BootstrapPrivateRoundStreams.extendedPrivateLaw p).map e splitEvent := by
          symm
          rw [Measure.map_apply hsplit.measurable hsplitEventMeasurable, hsplitEvent]
    _ = ((otherPrivateLaw p s).prod
        ((PrivateSourceStreams.blockScalarProfileLaw p).prod
          ContinuousCategorical.uniform)) splitEvent := by
          rw [hsplit.map_eq]
    _ = otherPrivateLaw p s restEvent *
        (PrivateSourceStreams.blockScalarProfileLaw p profileEvent *
          ContinuousCategorical.uniform targetEvent) := by
          simp only [splitEvent, Measure.prod_prod]
    _ = BootstrapPrivateRoundStreams.extendedPrivateLaw p
          {rho | generatedBoundary p s ids row rewards C_star C_h eta rho = b} *
        BootstrapBlockIsolation.privateBlockProfileLaw p b.numerators b.weight_ge_one c *
          ENNReal.ofReal (1 / (p.K : ℝ)) := by
          rw [hprofileMass, htargetMass, ← hboundaryMass]
          simp only [mul_assoc]

/-- At a genuinely processed generated block boundary, each incoming
uninformed follower's three physical block-start fields are exactly its own
original-label entry in the current full profile, and the coordinator target
is exactly the draw from the original target scalar. -/
theorem actualProcessedBlock_draw_fields (p : Parameters)
    (s : Fin (n_boot p)) (ids : CompletePublicTable.IDArray p)
    (row : CompletePublicTable.CompleteRow p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (rho : BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
    (b : ReferenceInitializationRun.Boundary p)
    (hboundary : generatedBoundary p s ids row rewards C_star C_h eta rho = b)
    (hcompleted : b.completed = s.val) (hnotStopped : b.crossing = none) :
    let x := fixedReferenceInput p ids row rewards C_star C_h eta rho
    let h : b.completed < n_boot p := by rw [hcompleted]; exact s.isLt
    (ReferenceInitializationRun.run x (s.val + 1) =
      ReferenceInitializationRun.finishBlock x b h) ∧
    (∀ i : {i // i ∈ ReferenceInitializationRun.uninformed b},
      ((ReferenceInitializationRun.physical x b h).active i,
        (ReferenceInitializationRun.physical x b h).held i,
        (ReferenceInitializationRun.physical x b h).privateId i) =
        generatedCurrentBlockProfile p s b rho
          (BootstrapPhysicalInput.sourceFollowerIndex p i.1)) ∧
    (ReferenceInitializationRun.physical x b h).target =
      generatedCurrentTarget p s rho := by
  dsimp only
  let x := fixedReferenceInput p ids row rewards C_star C_h eta rho
  let h : b.completed < n_boot p := by rw [hcompleted]; exact s.isLt
  have hs : ReferenceInitializationRun.nextBlock b h = s := by
    apply Fin.ext
    simp [ReferenceInitializationRun.nextBlock, hcompleted]
  constructor
  · calc
      ReferenceInitializationRun.run x (s.val + 1) =
          ReferenceInitializationRun.advance x (ReferenceInitializationRun.run x s.val) := by
            rw [ReferenceInitializationRun.run_succ]
      _ = ReferenceInitializationRun.finishBlock x b h := by
            rw [show ReferenceInitializationRun.run x s.val = b from hboundary]
            exact ReferenceInitializationRun.advance_of_no_crossing x b hnotStopped h
  constructor
  · intro i
    rw [ReferenceInitializationRun.physical_own_block_draw x b h i, hs]
    rfl
  · change BootstrapPrivateRoundStreams.coordinatorTargetDraw p
      (rho.2.2 (ReferenceInitializationRun.nextBlock b h)) =
        BootstrapPrivateRoundStreams.coordinatorTargetDraw p (rho.2.2 s)
    rw [hs]

/-- The physical triple of an incoming follower at an actual non-stopped
generated boundary. The boundary index equality makes the physical map use
the actual block label `s`; the stopped proof rules out inventing a block
after an earlier launch. -/
def generatedPhysicalBlockDraw (p : Parameters) (s : Fin (n_boot p))
    (ids : CompletePublicTable.IDArray p) (row : CompletePublicTable.CompleteRow p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (b : ReferenceInitializationRun.Boundary p) (hcompleted : b.completed = s.val)
    (_hnotStopped : b.crossing = none) (i : {i // i ∈ ReferenceInitializationRun.uninformed b})
    (rho : BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p) :
    PrivateSourceStreams.BlockDraw p :=
  let h : b.completed < n_boot p := by rw [hcompleted]; exact s.isLt
  let x := fixedReferenceInput p ids row rewards C_star C_h eta rho
  ((ReferenceInitializationRun.physical x b h).active i,
    (ReferenceInitializationRun.physical x b h).held i,
    (ReferenceInitializationRun.physical x b h).privateId i)

/-- The physical coordinator target at an actual non-stopped generated
boundary, from its original current-block target scalar. -/
def generatedPhysicalBlockTarget (p : Parameters) (s : Fin (n_boot p))
    (ids : CompletePublicTable.IDArray p) (row : CompletePublicTable.CompleteRow p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (b : ReferenceInitializationRun.Boundary p) (hcompleted : b.completed = s.val)
    (_hnotStopped : b.crossing = none)
    (rho : BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p) : Fin p.K :=
  let h : b.completed < n_boot p := by rw [hcompleted]; exact s.isLt
  let x := fixedReferenceInput p ids row rewards C_star C_h eta rho
  (ReferenceInitializationRun.physical x b h).target

/-- The actual processed-block event that records the complete current
original-label profile and target, together with the physical triple of a
specified incoming follower and the physical coordinator target. Profile
entries for followers already activated before this block remain latent data. -/
def generatedProcessedBlockDrawEvent (p : Parameters) (s : Fin (n_boot p))
    (ids : CompletePublicTable.IDArray p) (row : CompletePublicTable.CompleteRow p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (b : ReferenceInitializationRun.Boundary p) (hcompleted : b.completed = s.val)
    (hnotStopped : b.crossing = none)
    (i : {i // i ∈ ReferenceInitializationRun.uninformed b})
    (c : PrivateSourceStreams.BlockDrawProfile p) (z : Fin p.K) :
    Set (BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p) :=
  {rho | generatedBoundary p s ids row rewards C_star C_h eta rho = b ∧
    generatedCurrentBlockProfile p s b rho = c ∧ generatedCurrentTarget p s rho = z ∧
    generatedPhysicalBlockDraw p s ids row rewards C_star C_h eta b hcompleted
      hnotStopped i rho = c (BootstrapPhysicalInput.sourceFollowerIndex p i.1) ∧
    generatedPhysicalBlockTarget p s ids row rewards C_star C_h eta b hcompleted
      hnotStopped rho = z}

/-- The processed physical event is the generated boundary/profile/target atom
whenever the boundary really is an ordinary block start. Thus its
unnormalized law has the same exact PMF and target factors, even for a
zero-mass boundary atom. -/
theorem generatedProcessedBlockDrawEvent_atom (p : Parameters)
    (s : Fin (n_boot p)) (ids : CompletePublicTable.IDArray p)
    (row : CompletePublicTable.CompleteRow p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (b : ReferenceInitializationRun.Boundary p) (hcompleted : b.completed = s.val)
    (hnotStopped : b.crossing = none)
    (i : {i // i ∈ ReferenceInitializationRun.uninformed b})
    (c : PrivateSourceStreams.BlockDrawProfile p) (z : Fin p.K) :
    BootstrapPrivateRoundStreams.extendedPrivateLaw p
      (generatedProcessedBlockDrawEvent p s ids row rewards C_star C_h eta b hcompleted
        hnotStopped i c z) =
      BootstrapPrivateRoundStreams.extendedPrivateLaw p
        {rho | generatedBoundary p s ids row rewards C_star C_h eta rho = b} *
      BootstrapBlockIsolation.privateBlockProfileLaw p b.numerators b.weight_ge_one c *
        ENNReal.ofReal (1 / (p.K : ℝ)) := by
  have hevent : generatedProcessedBlockDrawEvent p s ids row rewards C_star C_h eta b
      hcompleted hnotStopped i c z =
      generatedBoundaryDrawEvent p s ids row rewards C_star C_h eta b c z := by
    ext rho
    constructor
    · intro h
      exact ⟨h.1, h.2.1, h.2.2.1⟩
    · rintro ⟨hboundary, hprofile, htarget⟩
      have hfields := actualProcessedBlock_draw_fields p s ids row rewards C_star C_h eta
        rho b hboundary hcompleted hnotStopped
      rcases hfields with ⟨_, hphysical, hphysicalTarget⟩
      refine ⟨hboundary, hprofile, htarget, ?_, ?_⟩
      · calc
          generatedPhysicalBlockDraw p s ids row rewards C_star C_h eta b hcompleted
              hnotStopped i rho =
              generatedCurrentBlockProfile p s b rho
                (BootstrapPhysicalInput.sourceFollowerIndex p i.1) := by
                  simpa [generatedPhysicalBlockDraw] using hphysical i
          _ = c (BootstrapPhysicalInput.sourceFollowerIndex p i.1) :=
            congrFun hprofile (BootstrapPhysicalInput.sourceFollowerIndex p i.1)
      · calc
          generatedPhysicalBlockTarget p s ids row rewards C_star C_h eta b hcompleted
              hnotStopped rho = generatedCurrentTarget p s rho := by
                simpa [generatedPhysicalBlockTarget] using hphysicalTarget
          _ = z := htarget
  rw [hevent]
  exact generatedBoundary_currentProfile_target_atom p s ids row rewards C_star C_h eta b c z

end Bandits.Support.GeneratedBlockDrawLaw

end
