/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.GeneratedBootstrapRoundLaw
public import Bandits.Support.ContinuousLearningRows
public import Bandits.Support.CompletePublicTable
public import Bandits.Support.BootstrapPrivateRoundStreams
public import Bandits.Support.AffineChannelLaw
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.Independence.Basic

/-!
# Original-law prelaunch DOWN affine product

Sources: `sources/zip4/manuscript/appendix_b_communication.tex:40-55,724-736`
and `sources/zip4/manuscript/05_binary_transport.tex:7-25`.

This is an exact coordinate rearrangement of the original full continuous
row/private law. It separates every selected-row DOWN affine sample from the
forward bits, every continuous scalar slice, all UP affine samples, and the
complete original private coordinate. It does not describe physical execution
or conditioning on a published event.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.CompletePublicTable
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.ContinuousLearningRows
open Bandits.Support.AffineChannelLaw
open ProbabilityTheory
open scoped Classical

namespace Bandits.Support.PrelaunchDownAffineProduct

abbrev Parameters := ConstructorDimensions.Parameters

/-- All selected-row DOWN samples, retaining every round and follower. -/
abbrev DownAtTime (p : Parameters) :=
  Fin (p.m - 1) → AffineChannelLaw.Sample (ContinuousLearningRows.B p)

/-- The DOWN law at one time, with every follower coordinate retained. -/
def downAtTimeLaw (p : Parameters) : Measure (DownAtTime p) :=
  Measure.pi (fun _ : Fin (p.m - 1) =>
    (AffineChannelLaw.jointLaw (ContinuousLearningRows.B p)).toMeasure)

instance downAtTimeLaw_probability (p : Parameters) : IsProbabilityMeasure (downAtTimeLaw p) := by
  unfold downAtTimeLaw
  infer_instance

/-- All selected-row DOWN samples, retaining every round and follower. -/
abbrev DownBank (p : Parameters) :=
  Fin p.T → DownAtTime p

/-- All direction-UP samples at one round. -/
abbrev UpAtTime (p : Parameters) :=
  Fin (p.m - 1) → AffineChannelLaw.Sample (ContinuousLearningRows.B p)

/-- All selected-row UP samples, retaining every follower and round. -/
abbrev UpBank (p : Parameters) := Fin p.T → UpAtTime p

/-- The complete non-DOWN part of the original coordinates: original forward
bits, all scalar slices and UP samples, and all original private coordinates. -/
abbrev Side (p : Parameters) :=
  (CompletePublicTable.ForwardRow p ×
    ((Fin p.T → ContinuousLearningRows.Slice p) × UpBank p)) ×
      BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p

/-- The original DOWN sample law, as the literal finite pi of the existing
one-channel joint law. -/
def downBankLaw (p : Parameters) : Measure (DownBank p) :=
  Measure.pi (fun _ : Fin p.T => downAtTimeLaw p)

instance downBankLaw_probability (p : Parameters) : IsProbabilityMeasure (downBankLaw p) := by
  unfold downBankLaw
  infer_instance

/-- The UP law at one time, with every follower coordinate retained. -/
def upAtTimeLaw (p : Parameters) : Measure (UpAtTime p) :=
  Measure.pi (fun _ : Fin (p.m - 1) =>
    (AffineChannelLaw.jointLaw (ContinuousLearningRows.B p)).toMeasure)

instance upAtTimeLaw_probability (p : Parameters) : IsProbabilityMeasure (upAtTimeLaw p) := by
  unfold upAtTimeLaw
  infer_instance

/-- The full original UP bank law. -/
def upBankLaw (p : Parameters) : Measure (UpBank p) :=
  Measure.pi (fun _ : Fin p.T => upAtTimeLaw p)

instance upBankLaw_probability (p : Parameters) : IsProbabilityMeasure (upBankLaw p) := by
  unfold upBankLaw
  infer_instance

/-- The full continuous scalar-slice law, with the original time grouping. -/
def sliceStreamLaw (p : Parameters) : Measure (Fin p.T → ContinuousLearningRows.Slice p) :=
  Measure.pi (fun _ : Fin p.T => ContinuousControlSlice.sliceLaw p.m p.K)

instance sliceStreamLaw_probability (p : Parameters) :
    IsProbabilityMeasure (sliceStreamLaw p) := by
  unfold sliceStreamLaw
  infer_instance

/-- Side law in the carrier's explicit grouping: forward row, complete
continuous-slice/UP streams, then the original extended private law. -/
def sideLaw (p : Parameters) : Measure (Side p) :=
  ((CompletePublicTable.forwardRowMeasure p).prod
    ((sliceStreamLaw p).prod (upBankLaw p))).prod
        (BootstrapPrivateRoundStreams.extendedPrivateLaw p)

instance sideLaw_probability (p : Parameters) : IsProbabilityMeasure (sideLaw p) := by
  unfold sideLaw
  infer_instance

/-- Product law of the DOWN bank and all remaining original coordinates. -/
def downSideLaw (p : Parameters) : Measure (DownBank p × Side p) :=
  (downBankLaw p).prod (sideLaw p)

instance downSideLaw_probability (p : Parameters) : IsProbabilityMeasure (downSideLaw p) := by
  unfold downSideLaw
  infer_instance

/-- The DOWN-index subset of all direction/follower labels. -/
def downChannelEquiv (p : Parameters) :
    {c : ContinuousLearningRows.Channel p // c.1 = (0 : Fin 2)} ≃ Fin (p.m - 1) where
  toFun c := c.1.2
  invFun i := ⟨(0, i), by simp⟩
  left_inv c := by
    rcases c with ⟨⟨dir, i⟩, hdir⟩
    apply Subtype.ext
    change ((0 : Fin 2), i) = (dir, i)
    cases hdir
    rfl
  right_inv _ := rfl

@[simp] theorem downChannelEquiv_symm_val (p : Parameters)
    (i : Fin (ContinuousLearningRows.d p)) :
    ((downChannelEquiv p).symm i).val = ((0 : Fin 2), i) := rfl

/-- The UP-index subset of all direction/follower labels. -/
def upChannelEquiv (p : Parameters) :
    {c : ContinuousLearningRows.Channel p // c.1 ≠ (0 : Fin 2)} ≃ Fin (p.m - 1) where
  toFun c := c.1.2
  invFun i := ⟨((1 : Fin 2), i), by
    change (1 : Fin 2) ≠ 0
    decide⟩
  left_inv c := by
    rcases c with ⟨⟨dir, i⟩, hdir⟩
    apply Subtype.ext
    apply Prod.ext
    · have hd : dir = (1 : Fin 2) := by
        fin_cases dir <;> simp_all
      exact hd.symm
    · rfl
  right_inv _ := rfl

@[simp] theorem upChannelEquiv_symm_val (p : Parameters)
    (i : Fin (ContinuousLearningRows.d p)) :
    ((upChannelEquiv p).symm i).val = ((1 : Fin 2), i) := rfl

/-- Reindex all affine samples at one time into the literal DOWN and UP
follower vectors. This uses Mathlib's pi split and pi reindex equivalences. -/
def affineSamplesDirectionEquiv (p : Parameters) :
    ContinuousLearningRows.AffineSamples p ≃ᵐ (DownAtTime p × UpAtTime p) := by
  let split := MeasurableEquiv.piEquivPiSubtypeProd
    (fun _ : ContinuousLearningRows.Channel p =>
      AffineChannelLaw.Sample (ContinuousLearningRows.B p))
    (fun c => c.1 = (0 : Fin 2))
  let down := MeasurableEquiv.piCongrLeft
    (fun _ : Fin (p.m - 1) => AffineChannelLaw.Sample (ContinuousLearningRows.B p))
    (downChannelEquiv p)
  let up := MeasurableEquiv.piCongrLeft
    (fun _ : Fin (p.m - 1) => AffineChannelLaw.Sample (ContinuousLearningRows.B p))
    (upChannelEquiv p)
  exact split.trans (down.prodCongr up)

/-- The pointwise direction split preserves the existing joint affine law. -/
theorem measurePreserving_affineSamplesDirectionEquiv (p : Parameters) :
    MeasurePreserving (affineSamplesDirectionEquiv p)
      (ContinuousLearningRows.affineSamplesLaw p)
      ((downAtTimeLaw p).prod (upAtTimeLaw p)) := by
  have hsplit := measurePreserving_piEquivPiSubtypeProd
    (fun _ : ContinuousLearningRows.Channel p =>
      (AffineChannelLaw.jointLaw (ContinuousLearningRows.B p)).toMeasure)
    (fun c : ContinuousLearningRows.Channel p => c.1 = (0 : Fin 2))
  have hdown := measurePreserving_piCongrLeft
    (fun _ : Fin (p.m - 1) =>
      (AffineChannelLaw.jointLaw (ContinuousLearningRows.B p)).toMeasure)
    (downChannelEquiv p)
  have hup := measurePreserving_piCongrLeft
    (fun _ : Fin (p.m - 1) =>
      (AffineChannelLaw.jointLaw (ContinuousLearningRows.B p)).toMeasure)
    (upChannelEquiv p)
  have h := (hdown.prod hup).comp hsplit
  change MeasurePreserving (affineSamplesDirectionEquiv p)
    (Measure.pi (fun _ : ContinuousLearningRows.Channel p =>
      (AffineChannelLaw.jointLaw (ContinuousLearningRows.B p)).toMeasure))
    ((downAtTimeLaw p).prod (upAtTimeLaw p))
  change MeasurePreserving (affineSamplesDirectionEquiv p)
    (ContinuousLearningRows.affineSamplesLaw p)
    ((downAtTimeLaw p).prod (upAtTimeLaw p)) at h
  exact h

/-- Reindex every time's affine coordinates into the complete DOWN and UP
banks. -/
def affineTimeSplitEquiv (p : Parameters) :
    (Fin p.T → ContinuousLearningRows.AffineSamples p) ≃ᵐ (DownBank p × UpBank p) :=
  (MeasurableEquiv.piCongrRight (fun _ : Fin p.T => affineSamplesDirectionEquiv p)).trans
    (MeasurableEquiv.arrowProdEquivProdArrow (DownAtTime p) (UpAtTime p) (Fin p.T))

theorem measurePreserving_affineTimeSplitEquiv (p : Parameters) :
    MeasurePreserving (affineTimeSplitEquiv p)
      (Measure.pi (fun _ : Fin p.T => ContinuousLearningRows.affineSamplesLaw p))
      ((downBankLaw p).prod (upBankLaw p)) := by
  have hpi := measurePreserving_pi
    (fun _ : Fin p.T => ContinuousLearningRows.affineSamplesLaw p)
    (fun _ : Fin p.T => (downAtTimeLaw p).prod (upAtTimeLaw p))
    (fun _ => measurePreserving_affineSamplesDirectionEquiv p)
  have harrow := measurePreserving_arrowProdEquivProdArrow
    (DownAtTime p) (UpAtTime p) (Fin p.T)
    (fun _ => downAtTimeLaw p) (fun _ => upAtTimeLaw p)
  have h := harrow.comp hpi
  change MeasurePreserving (affineTimeSplitEquiv p)
    (Measure.pi (fun _ : Fin p.T => ContinuousLearningRows.affineSamplesLaw p))
    ((downBankLaw p).prod (upBankLaw p)) at h
  exact h

/-- Split one complete learning row into every scalar slice and its DOWN/UP
affine banks. -/
def learningRowSplitEquiv (p : Parameters) :
    ContinuousLearningRows.LearningRow p ≃ᵐ
      ((Fin p.T → ContinuousLearningRows.Slice p) × (DownBank p × UpBank p)) :=
  (MeasurableEquiv.arrowProdEquivProdArrow
    (ContinuousLearningRows.Slice p) (ContinuousLearningRows.AffineSamples p) (Fin p.T)).trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _) (affineTimeSplitEquiv p))

theorem measurePreserving_learningRowSplitEquiv (p : Parameters) :
    MeasurePreserving (learningRowSplitEquiv p)
      (ContinuousLearningRows.learningRowLaw p)
      ((sliceStreamLaw p).prod ((downBankLaw p).prod (upBankLaw p))) := by
  have hsplit : MeasurePreserving
      (MeasurableEquiv.arrowProdEquivProdArrow
        (ContinuousLearningRows.Slice p) (ContinuousLearningRows.AffineSamples p) (Fin p.T))
      (ContinuousLearningRows.learningRowLaw p)
      ((sliceStreamLaw p).prod
        (Measure.pi (fun _ : Fin p.T => ContinuousLearningRows.affineSamplesLaw p))) := by
    change MeasurePreserving ContinuousLearningRows.splitRow
      (ContinuousLearningRows.learningRowLaw p)
      ((sliceStreamLaw p).prod
        (Measure.pi (fun _ : Fin p.T => ContinuousLearningRows.affineSamplesLaw p)))
    exact ContinuousLearningRows.measurePreserving_splitRow p
  exact ((MeasurePreserving.id (sliceStreamLaw p)).prod
    (measurePreserving_affineTimeSplitEquiv p)).comp hsplit

/-- Split a complete original row while retaining its full forward vector. -/
def completeRowSplitEquiv (p : Parameters) :
    CompletePublicTable.CompleteRow p ≃ᵐ
      (CompletePublicTable.ForwardRow p ×
        ((Fin p.T → ContinuousLearningRows.Slice p) × (DownBank p × UpBank p))) :=
  (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _)
    (learningRowSplitEquiv p))

theorem measurePreserving_completeRowSplitEquiv (p : Parameters) :
    MeasurePreserving (completeRowSplitEquiv p)
      (CompletePublicTable.completeRowMeasure p)
      ((CompletePublicTable.forwardRowMeasure p).prod
        ((sliceStreamLaw p).prod ((downBankLaw p).prod (upBankLaw p)))) := by
  exact (MeasurePreserving.id (CompletePublicTable.forwardRowMeasure p)).prod
    (measurePreserving_learningRowSplitEquiv p)

/-- Split the original coordinate pair without modifying its private member. -/
def sourceCoordinateSplitEquiv (p : Parameters) :
    GeneratedBootstrapRoundLaw.Coordinates p ≃ᵐ
      ((CompletePublicTable.ForwardRow p ×
        ((Fin p.T → ContinuousLearningRows.Slice p) × (DownBank p × UpBank p))) ×
          BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p) :=
  (completeRowSplitEquiv p).prodCongr (MeasurableEquiv.refl _)

def innerDirectionsLayout (p : Parameters) :
    (Fin p.T → ContinuousLearningRows.Slice p) × (DownBank p × UpBank p) ≃ᵐ
      DownBank p × ((Fin p.T → ContinuousLearningRows.Slice p) × UpBank p) :=
  let S := Fin p.T → ContinuousLearningRows.Slice p
  let D := DownBank p
  let U := UpBank p
  let e₁ : S × (D × U) ≃ᵐ (S × D) × U := MeasurableEquiv.prodAssoc.symm
  let e₂ : (S × D) × U ≃ᵐ (D × S) × U :=
    MeasurableEquiv.prodCongr MeasurableEquiv.prodComm (MeasurableEquiv.refl U)
  let e₃ : (D × S) × U ≃ᵐ D × (S × U) := MeasurableEquiv.prodAssoc
  e₁.trans (e₂.trans e₃)

def forwardDirectionsLayout (p : Parameters) :
    CompletePublicTable.ForwardRow p ×
      ((Fin p.T → ContinuousLearningRows.Slice p) × (DownBank p × UpBank p)) ≃ᵐ
        DownBank p ×
          (CompletePublicTable.ForwardRow p ×
            ((Fin p.T → ContinuousLearningRows.Slice p) × UpBank p)) :=
  let F := CompletePublicTable.ForwardRow p
  let S := Fin p.T → ContinuousLearningRows.Slice p
  let D := DownBank p
  let U := UpBank p
  let V := S × U
  let e₀ : F × (S × (D × U)) ≃ᵐ F × (D × V) :=
    MeasurableEquiv.prodCongr (MeasurableEquiv.refl F) (innerDirectionsLayout p)
  let e₁ : F × (D × V) ≃ᵐ (F × D) × V := MeasurableEquiv.prodAssoc.symm
  let e₂ : (F × D) × V ≃ᵐ (D × F) × V :=
    MeasurableEquiv.prodCongr MeasurableEquiv.prodComm (MeasurableEquiv.refl V)
  let e₃ : (D × F) × V ≃ᵐ D × (F × V) := MeasurableEquiv.prodAssoc
  e₀.trans (e₁.trans (e₂.trans e₃))

/-- Final parenthesization places the complete DOWN bank first and leaves every
other original coordinate grouped in `Side`. -/
def affineDownLayoutEquiv (p : Parameters) :
    ((CompletePublicTable.ForwardRow p ×
      ((Fin p.T → ContinuousLearningRows.Slice p) × (DownBank p × UpBank p))) ×
        BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p) ≃ᵐ
      (DownBank p × Side p) :=
  let F := CompletePublicTable.ForwardRow p
  let S := Fin p.T → ContinuousLearningRows.Slice p
  let D := DownBank p
  let U := UpBank p
  let R := BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p
  let e₁ : (F × (S × (D × U))) × R ≃ᵐ (D × (F × (S × U))) × R :=
    MeasurableEquiv.prodCongr (forwardDirectionsLayout p) (MeasurableEquiv.refl R)
  let e₂ : (D × (F × (S × U))) × R ≃ᵐ D × ((F × (S × U)) × R) :=
    MeasurableEquiv.prodAssoc
  e₁.trans e₂

private theorem measurePreserving_innerDirectionsLayout (p : Parameters) :
    MeasurePreserving (innerDirectionsLayout p)
      (sliceStreamLaw p |>.prod ((downBankLaw p).prod (upBankLaw p)))
      ((downBankLaw p).prod (sliceStreamLaw p |>.prod (upBankLaw p))) := by
  let μS := sliceStreamLaw p
  let μD := downBankLaw p
  let μU := upBankLaw p
  have h1 := (measurePreserving_prodAssoc μS μD μU).symm
  have h2 := (Measure.measurePreserving_swap (μ := μS) (ν := μD)).prod
    (MeasurePreserving.id μU)
  have h3 := measurePreserving_prodAssoc μD μS μU
  have h := h3.comp (h2.comp h1)
  change MeasurePreserving (innerDirectionsLayout p)
    (μS.prod (μD.prod μU)) (μD.prod (μS.prod μU))
  exact h

theorem measurePreserving_forwardDirectionsLayout (p : Parameters) :
    MeasurePreserving (forwardDirectionsLayout p)
      ((CompletePublicTable.forwardRowMeasure p).prod
        (sliceStreamLaw p |>.prod ((downBankLaw p).prod (upBankLaw p))))
      ((downBankLaw p).prod
        ((CompletePublicTable.forwardRowMeasure p).prod
          (sliceStreamLaw p |>.prod (upBankLaw p)))) := by
  let μF := CompletePublicTable.forwardRowMeasure p
  let μS := sliceStreamLaw p
  let μD := downBankLaw p
  let μU := upBankLaw p
  have h1 := (MeasurePreserving.id μF).prod (measurePreserving_innerDirectionsLayout p)
  have h2 := (measurePreserving_prodAssoc μF μD (μS.prod μU)).symm
  have h3 := (Measure.measurePreserving_swap (μ := μF) (ν := μD)).prod
    (MeasurePreserving.id (μS.prod μU))
  have h4 := measurePreserving_prodAssoc μD μF (μS.prod μU)
  have h := h4.comp (h3.comp (h2.comp h1))
  change MeasurePreserving (forwardDirectionsLayout p)
    (μF.prod (μS.prod (μD.prod μU)))
    (μD.prod (μF.prod (μS.prod μU)))
  exact h

private theorem measurePreserving_affineDownLayoutEquiv (p : Parameters) :
    MeasurePreserving (affineDownLayoutEquiv p)
      (((CompletePublicTable.forwardRowMeasure p).prod
        (sliceStreamLaw p |>.prod ((downBankLaw p).prod (upBankLaw p)))).prod
          (BootstrapPrivateRoundStreams.extendedPrivateLaw p))
      (downBankLaw p |>.prod (sideLaw p)) := by
  let μD := downBankLaw p
  let μS := sliceStreamLaw p
  let μF := CompletePublicTable.forwardRowMeasure p
  let μU := upBankLaw p
  let μR := BootstrapPrivateRoundStreams.extendedPrivateLaw p
  have h1 := (measurePreserving_forwardDirectionsLayout p).prod (MeasurePreserving.id μR)
  have h2 := measurePreserving_prodAssoc μD (μF.prod (μS.prod μU)) μR
  have h := h2.comp h1
  change MeasurePreserving (affineDownLayoutEquiv p)
    ((μF.prod (μS.prod (μD.prod μU))).prod μR)
    (μD.prod ((μF.prod (μS.prod μU)).prod μR))
  exact h

/-- Exact measurable equivalence from the original law to the selected-row
DOWN affine bank and complete remaining side data. -/
def affineDownSplitEquiv (p : Parameters) :
    GeneratedBootstrapRoundLaw.Coordinates p ≃ᵐ (DownBank p × Side p) :=
  (sourceCoordinateSplitEquiv p).trans (affineDownLayoutEquiv p)

/-- The bank projection is literally the original row's direction-zero affine
sample at each `(time, follower)` coordinate. -/
theorem affineDownSplitEquiv_bank (p : Parameters)
    (e : GeneratedBootstrapRoundLaw.Coordinates p) :
    (affineDownSplitEquiv p e).1 = fun t i =>
      (e.1.2 t).2 (0, i) := by
  funext t
  funext i
  change Fin (ContinuousLearningRows.d p) at i
  simp [affineDownSplitEquiv, affineDownLayoutEquiv, forwardDirectionsLayout,
    innerDirectionsLayout, sourceCoordinateSplitEquiv, completeRowSplitEquiv,
    learningRowSplitEquiv, affineTimeSplitEquiv, affineSamplesDirectionEquiv,
    MeasurableEquiv.prodAssoc,
    MeasurableEquiv.prodComm, MeasurableEquiv.prodCongr,
    MeasurableEquiv.arrowProdEquivProdArrow, MeasurableEquiv.piCongrRight,
    MeasurableEquiv.piEquivPiSubtypeProd, MeasurableEquiv.piCongrLeft,
    Equiv.piCongrLeft, Equiv.piCongrLeft', Equiv.piEquivPiSubtypeProd]

/-- Forward bits are copied as the original complete-row forward coordinate. -/
theorem affineDownSplitEquiv_forward (p : Parameters)
    (e : GeneratedBootstrapRoundLaw.Coordinates p) :
    (affineDownSplitEquiv p e).2.1.1 = e.1.1 := by
  simp [affineDownSplitEquiv, affineDownLayoutEquiv, forwardDirectionsLayout,
    innerDirectionsLayout, sourceCoordinateSplitEquiv, completeRowSplitEquiv,
    learningRowSplitEquiv, affineTimeSplitEquiv, MeasurableEquiv.prodAssoc,
    MeasurableEquiv.prodComm, MeasurableEquiv.prodCongr,
    MeasurableEquiv.arrowProdEquivProdArrow, MeasurableEquiv.piCongrRight]

/-- Every original continuous slice is copied at its original time. -/
theorem affineDownSplitEquiv_slice (p : Parameters)
    (e : GeneratedBootstrapRoundLaw.Coordinates p) (t : Fin p.T) :
    (affineDownSplitEquiv p e).2.1.2.1 t = (e.1.2 t).1 := by
  simp [affineDownSplitEquiv, affineDownLayoutEquiv, forwardDirectionsLayout,
    innerDirectionsLayout, sourceCoordinateSplitEquiv, completeRowSplitEquiv,
    learningRowSplitEquiv, affineTimeSplitEquiv, MeasurableEquiv.prodAssoc,
    MeasurableEquiv.prodComm, MeasurableEquiv.prodCongr,
    MeasurableEquiv.arrowProdEquivProdArrow, MeasurableEquiv.piCongrRight]

/-- Every original direction-one affine sample is copied at its original time
and follower. -/
theorem affineDownSplitEquiv_up (p : Parameters)
    (e : GeneratedBootstrapRoundLaw.Coordinates p) (t : Fin p.T) (i : Fin (p.m - 1)) :
    (affineDownSplitEquiv p e).2.1.2.2 t i = (e.1.2 t).2 (1, i) := by
  change Fin (ContinuousLearningRows.d p) at i
  simp [affineDownSplitEquiv, affineDownLayoutEquiv, forwardDirectionsLayout,
    innerDirectionsLayout, sourceCoordinateSplitEquiv, completeRowSplitEquiv,
    learningRowSplitEquiv, affineTimeSplitEquiv, affineSamplesDirectionEquiv,
    MeasurableEquiv.prodAssoc, MeasurableEquiv.prodComm,
    MeasurableEquiv.prodCongr, MeasurableEquiv.arrowProdEquivProdArrow,
    MeasurableEquiv.piCongrRight, MeasurableEquiv.piEquivPiSubtypeProd,
    MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft, Equiv.piCongrLeft',
    Equiv.piEquivPiSubtypeProd]

/-- The complete original private coordinate is preserved verbatim. This
includes the original J scalar, all block arrays and all player/target streams. -/
theorem affineDownSplitEquiv_private (p : Parameters)
    (e : GeneratedBootstrapRoundLaw.Coordinates p) :
    (affineDownSplitEquiv p e).2.2 = e.2 := by
  simp [affineDownSplitEquiv, affineDownLayoutEquiv, forwardDirectionsLayout,
    innerDirectionsLayout, sourceCoordinateSplitEquiv, MeasurableEquiv.prodAssoc,
    MeasurableEquiv.prodComm, MeasurableEquiv.prodCongr]

/-- The original J scalar and the remaining base private source arrays are
retained separately and exactly. -/
theorem affineDownSplitEquiv_privateBase (p : Parameters)
    (e : GeneratedBootstrapRoundLaw.Coordinates p) :
    (affineDownSplitEquiv p e).2.2.1 = e.2.1 := by
  simp [affineDownSplitEquiv, affineDownLayoutEquiv, forwardDirectionsLayout,
    innerDirectionsLayout, sourceCoordinateSplitEquiv, MeasurableEquiv.prodAssoc,
    MeasurableEquiv.prodComm, MeasurableEquiv.prodCongr]

theorem affineDownSplitEquiv_jScalar (p : Parameters)
    (e : GeneratedBootstrapRoundLaw.Coordinates p) :
    (affineDownSplitEquiv p e).2.2.1.2 = e.2.1.2 := by
  simp [affineDownSplitEquiv, affineDownLayoutEquiv, forwardDirectionsLayout,
    innerDirectionsLayout, sourceCoordinateSplitEquiv, MeasurableEquiv.prodAssoc,
    MeasurableEquiv.prodComm, MeasurableEquiv.prodCongr]

theorem affineDownSplitEquiv_privateRemainder (p : Parameters)
    (e : GeneratedBootstrapRoundLaw.Coordinates p) :
    (affineDownSplitEquiv p e).2.2.2 = e.2.2 := by
  simp [affineDownSplitEquiv, affineDownLayoutEquiv, forwardDirectionsLayout,
    innerDirectionsLayout, sourceCoordinateSplitEquiv, MeasurableEquiv.prodAssoc,
    MeasurableEquiv.prodComm, MeasurableEquiv.prodCongr]

/-- The inverse restores the complete row and private coordinate exactly. -/
theorem affineDownSplitEquiv_symm_apply (p : Parameters)
    (x : DownBank p × Side p) :
    affineDownSplitEquiv p ((affineDownSplitEquiv p).symm x) = x :=
  (affineDownSplitEquiv p).apply_symm_apply x

/-- Applying the split inverse to an original coordinate returns that exact
complete row and private coordinate. -/
theorem affineDownSplitEquiv_symm_apply_apply (p : Parameters)
    (e : GeneratedBootstrapRoundLaw.Coordinates p) :
    (affineDownSplitEquiv p).symm (affineDownSplitEquiv p e) = e :=
  (affineDownSplitEquiv p).symm_apply_apply e

/-- The split map preserves the original law onto the stated literal product. -/
theorem measurePreserving_affineDownSplitEquiv (p : Parameters) :
    MeasurePreserving (affineDownSplitEquiv p)
      (GeneratedBootstrapRoundLaw.originalLaw p) (downSideLaw p) := by
  have hrow := measurePreserving_completeRowSplitEquiv p
  have hsource : MeasurePreserving (sourceCoordinateSplitEquiv p)
      (GeneratedBootstrapRoundLaw.originalLaw p)
      (((CompletePublicTable.forwardRowMeasure p).prod
        ((sliceStreamLaw p).prod ((downBankLaw p).prod (upBankLaw p)))).prod
          (BootstrapPrivateRoundStreams.extendedPrivateLaw p)) := by
    change MeasurePreserving
      ((completeRowSplitEquiv p).prodCongr (MeasurableEquiv.refl _))
      ((CompletePublicTable.completeRowMeasure p).prod
        (BootstrapPrivateRoundStreams.extendedPrivateLaw p)) _
    exact hrow.prod (MeasurePreserving.id _)
  have h := (measurePreserving_affineDownLayoutEquiv p).comp hsource
  change MeasurePreserving (affineDownSplitEquiv p)
    (GeneratedBootstrapRoundLaw.originalLaw p) (downSideLaw p)
  exact h

/-- The inverse equivalence also preserves measure. -/
theorem measurePreserving_affineDownSplitEquiv_symm (p : Parameters) :
    MeasurePreserving (affineDownSplitEquiv p).symm (downSideLaw p)
      (GeneratedBootstrapRoundLaw.originalLaw p) :=
  (measurePreserving_affineDownSplitEquiv p).symm

/-- Pushforward equality for the complete original law. -/
theorem originalLaw_map_affineDownSplitEquiv (p : Parameters) :
    (GeneratedBootstrapRoundLaw.originalLaw p).map (affineDownSplitEquiv p) = downSideLaw p :=
  (measurePreserving_affineDownSplitEquiv p).map_eq

/-- Arbitrary measurable bank/side cylinders factor exactly, including cells
of zero measure. -/
theorem affineDownSplitEquiv_cylinder (p : Parameters)
    (A : Set (DownBank p)) (S : Set (Side p))
    (hA : MeasurableSet A) (hS : MeasurableSet S) :
    (GeneratedBootstrapRoundLaw.originalLaw p)
      {e | (affineDownSplitEquiv p e).1 ∈ A ∧ (affineDownSplitEquiv p e).2 ∈ S} =
        downBankLaw p A * sideLaw p S := by
  let box : Set (DownBank p × Side p) := A ×ˢ S
  have hbox : MeasurableSet box := MeasurableSet.prod hA hS
  have hpre : (affineDownSplitEquiv p) ⁻¹' box =
      {e | (affineDownSplitEquiv p e).1 ∈ A ∧ (affineDownSplitEquiv p e).2 ∈ S} := by
    ext e
    simp [box, Set.mem_preimage, Set.mem_prod]
  calc
    _ = (GeneratedBootstrapRoundLaw.originalLaw p)
        ((affineDownSplitEquiv p) ⁻¹' box) := by rw [hpre]
    _ = ((GeneratedBootstrapRoundLaw.originalLaw p).map (affineDownSplitEquiv p)) box := by
      rw [Measure.map_apply (affineDownSplitEquiv p).measurable hbox]
    _ = downSideLaw p box := by rw [originalLaw_map_affineDownSplitEquiv]
    _ = downBankLaw p A * sideLaw p S := by
      simp [downSideLaw, box, Measure.prod_prod]

private theorem indepFun_pullback {Ω Ω' X Y : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure Ω} {ν : Measure Ω'} {g : Ω → Ω'}
    (hg : MeasurePreserving g μ ν) {f : Ω' → X} {k : Ω' → Y}
    (hf : Measurable f) (hk : Measurable k) (h : IndepFun f k ν) :
    IndepFun (f ∘ g) (k ∘ g) μ := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul] at h ⊢
  intro s t hs ht
  have hst := h s t hs ht
  rw [← hg.map_eq, Measure.map_apply hg.measurable ((hf hs).inter (hk ht)),
    Measure.map_apply hg.measurable (hf hs), Measure.map_apply hg.measurable (hk ht)] at hst
  exact hst

/-- The DOWN bank and the complete remaining side are independent under the
unconditioned original law. -/
theorem indepFun_affineDownSplitEquiv (p : Parameters) :
    IndepFun (fun e : GeneratedBootstrapRoundLaw.Coordinates p =>
      (affineDownSplitEquiv p e).1)
      (fun e => (affineDownSplitEquiv p e).2)
      (GeneratedBootstrapRoundLaw.originalLaw p) := by
  exact indepFun_pullback (measurePreserving_affineDownSplitEquiv p)
    measurable_fst measurable_snd
    (indepFun_prod measurable_id measurable_id)

end Bandits.Support.PrelaunchDownAffineProduct

end
