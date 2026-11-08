/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.GeneratedBootstrapBlockFiltrationRepair
public import Bandits.Support.GeneratedBlockStartLaw
public import Bandits.Support.GeneratedBlockDrawLaw
public import Bandits.Support.GeneratedBootstrapRoundLaw
public import Bandits.Support.CompleteRowStoppingLaw
public import Bandits.Support.BootstrapPrivateRoundStreams
public import Bandits.Support.PrivateSourceStreams

public import Mathlib.MeasureTheory.Constructions.Pi
import Lean.Elab.Tactic.Omega

/-!
# Original-coordinate causal bootstrap block products

Sources: `sources/zip4/manuscript/appendix_b_communication.tex:376-379,
403-415,533-656` and `sources/zip4/manuscript/07_public_setup.tex:27-38,
63-113`.

At a genuine bootstrap block, this module decomposes the accepted original
complete-row/private product into the literal source prefix, original current
block draws, the entire future calendar row, and the remaining original
labelled coordinates.  The coordinator's separate scalar for `J` remains in
the remainder.  Nothing is resampled or conditioned upon.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.CompletePublicTable
open Bandits.Support.CompleteRowStoppingLaw
open Bandits.Support.ContinuousCategorical
open Bandits.Support.GeneratedBlockDrawLaw
open Bandits.Support.GeneratedBlockStartLaw
open Bandits.Support.GeneratedBootstrapBlockFiltrationRepair
open Bandits.Support.GeneratedBootstrapRoundLaw
open Bandits.Support.PrivateSourceStreams
open Bandits.Support.ReferenceInitializationRun
open scoped ENNReal
open scoped Classical

namespace Bandits.Support.CausalBootstrapBlockProduct

abbrev Parameters := ConstructorDimensions.Parameters

/-- The original profiles at labels strictly after this genuine block. -/
abbrev LaterBlockProfiles (p : Parameters) (s : Fin (n_boot p)) :=
  {q : Fin (n_boot p) // s.val < q.val} →
    GeneratedBlockDrawLaw.FollowerTripleProfile p

/-- Original coordinator target scalars at labels strictly after this block. -/
abbrev LaterTargetScalars (p : Parameters) (s : Fin (n_boot p)) :=
  {q : Fin (n_boot p) // s.val < q.val} → BootstrapPrivateRoundStreams.Scalar

/-- Original player-round scalars at calendar labels on or after this block's
elapsed boundary. -/
abbrev FutureRoundScalars (p : Parameters) (s : Fin (n_boot p)) :=
  {label : BootstrapPrivateRoundStreams.PlayerRoundLabel p //
    ReferenceInitializationRun.elapsed p s.val ≤ label.2.val} →
      BootstrapPrivateRoundStreams.Scalar

/-- The untouched source coordinates, in this fixed order: coordinator `J`,
later follower profiles, later coordinator targets, and player-round scalars
whose calendar label is at least the elapsed boundary. -/
abbrev Remainder (p : Parameters) (s : Fin (n_boot p)) :=
  BootstrapPrivateRoundStreams.Scalar ×
    (LaterBlockProfiles p s ×
      (LaterTargetScalars p s × FutureRoundScalars p s))

/-- Literal product marginal of the four source-prefix coordinate groups. -/
def sourcePrefixLaw (p : Parameters) (s : Fin (n_boot p)) :
    Measure (GeneratedBootstrapBlockFiltrationRepair.SourcePrefix p s.val) :=
  (Measure.pi (fun _ : {t : Fin p.T //
      t.val < ReferenceInitializationRun.elapsed p s.val} =>
        CompleteRowStoppingLaw.calendarEntryLaw p)).prod
    ((Measure.pi (fun _ : {q : Fin (n_boot p) // q.val < s.val} =>
        PrivateSourceStreams.blockScalarProfileLaw p)).prod
      ((Measure.pi (fun _ : {q : Fin (n_boot p) // q.val < s.val} =>
          ContinuousCategorical.uniform)).prod
        (Measure.pi (fun _ : {label : BootstrapPrivateRoundStreams.PlayerRoundLabel p //
          label.2.val < ReferenceInitializationRun.elapsed p s.val} =>
            ContinuousCategorical.uniform))))

instance sourcePrefixLaw_probability (p : Parameters) (s : Fin (n_boot p)) :
    IsProbabilityMeasure (sourcePrefixLaw p s) := by
  dsimp [sourcePrefixLaw]
  infer_instance

/-- Literal product marginal of exactly the coordinates left after the
source prefix, current block, and entire future calendar row are removed. -/
def remainderLaw (p : Parameters) (s : Fin (n_boot p)) : Measure (Remainder p s) :=
  ContinuousCategorical.uniform.prod
    ((Measure.pi (fun _ : {q : Fin (n_boot p) // s.val < q.val} =>
        PrivateSourceStreams.blockScalarProfileLaw p)).prod
      ((Measure.pi (fun _ : {q : Fin (n_boot p) // s.val < q.val} =>
          ContinuousCategorical.uniform)).prod
        (Measure.pi (fun _ : {label : BootstrapPrivateRoundStreams.PlayerRoundLabel p //
          ReferenceInitializationRun.elapsed p s.val ≤ label.2.val} =>
            ContinuousCategorical.uniform))))

instance remainderLaw_probability (p : Parameters) (s : Fin (n_boot p)) :
    IsProbabilityMeasure (remainderLaw p s) := by
  dsimp [remainderLaw]
  infer_instance

abbrev RawCurrentBlock (p : Parameters) := GeneratedBlockStartLaw.CurrentCoordinates p

abbrev EntireFutureRow (p : Parameters) (s : Fin (n_boot p)) :=
  CompleteRowStoppingLaw.FutureArray p (GeneratedBlockStartLaw.blockStartIndex p s)

abbrev SourcePrefixPrivate (p : Parameters) (s : Fin (n_boot p)) :=
  GeneratedBootstrapBlockFiltrationRepair.BlockPrefix p s.val ×
    (GeneratedBootstrapBlockFiltrationRepair.TargetPrefix p s.val ×
      GeneratedBootstrapBlockFiltrationRepair.RoundScalarPrefix p s.val)

local instance sourcePrefixMeasurableSpace (p : Parameters) (s : Fin (n_boot p)) :
    MeasurableSpace (GeneratedBootstrapBlockFiltrationRepair.SourcePrefix p s.val) :=
  inferInstance

local instance remainderMeasurableSpace (p : Parameters) (s : Fin (n_boot p)) :
    MeasurableSpace (Remainder p s) := inferInstance

local instance rawCurrentBlockMeasurableSpace (p : Parameters) :
    MeasurableSpace (RawCurrentBlock p) := inferInstance

local instance entireFutureRowMeasurableSpace (p : Parameters) (s : Fin (n_boot p)) :
    MeasurableSpace (EntireFutureRow p s) := inferInstance

local instance futureCoordinatesMeasurableSpace (p : Parameters) (s : Fin (n_boot p)) :
    MeasurableSpace (GeneratedBlockStartLaw.FutureCoordinates p s) := inferInstance

/-! ### Splitting the already-separated noncurrent block labels -/

abbrev BeforeOtherBlockLabel (p : Parameters) (s : Fin (n_boot p)) :=
  {q : GeneratedBlockDrawLaw.OtherBlockLabels p s // q.1.val < s.val}

abbrev AfterOtherBlockLabel (p : Parameters) (s : Fin (n_boot p)) :=
  {q : GeneratedBlockDrawLaw.OtherBlockLabels p s // ¬ q.1.val < s.val}

def beforeOtherBlockLabelEquiv (p : Parameters) (s : Fin (n_boot p)) :
    BeforeOtherBlockLabel p s ≃ {q : Fin (n_boot p) // q.val < s.val} where
  toFun q := ⟨q.1.1, q.2⟩
  invFun q := ⟨⟨q.1, by
    intro h
    have hv : q.1.val = s.val := congrArg Fin.val h
    omega⟩, q.2⟩
  left_inv q := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv q := by
    apply Subtype.ext
    rfl

def afterOtherBlockLabelEquiv (p : Parameters) (s : Fin (n_boot p)) :
    AfterOtherBlockLabel p s ≃ {q : Fin (n_boot p) // s.val < q.val} where
  toFun q := ⟨q.1.1, by
    have hnotlt : ¬ q.1.1.val < s.val := q.2
    have hne : s.val ≠ q.1.1.val := by
      intro h
      apply q.1.2
      exact Fin.ext h.symm
    exact Nat.lt_of_le_of_ne (Nat.le_of_not_gt hnotlt) hne⟩
  invFun q := ⟨⟨q.1, by
    intro h
    exact (ne_of_gt q.2) (congrArg Fin.val h)⟩,
    not_lt_of_ge (Nat.le_of_lt q.2)⟩
  left_inv q := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv q := by
    apply Subtype.ext
    rfl

/-- Split other original follower profiles into strict-prefix and strict-later
labels. The omitted singleton label is exactly the current block already held
by `RawCurrentBlock`. -/
def otherFollowerBlocksPrefixLaterEquiv (p : Parameters) (s : Fin (n_boot p)) :
    GeneratedBlockDrawLaw.OtherFollowerBlocks p s ≃ᵐ
      (GeneratedBootstrapBlockFiltrationRepair.BlockPrefix p s.val ×
        LaterBlockProfiles p s) := by
  let e := MeasurableEquiv.piEquivPiSubtypeProd
    (fun _ : GeneratedBlockDrawLaw.OtherBlockLabels p s =>
      GeneratedBlockDrawLaw.FollowerTripleProfile p)
    (fun q => q.1.val < s.val)
  let eBefore := MeasurableEquiv.piCongrLeft
    (fun _ : {q : Fin (n_boot p) // q.val < s.val} =>
      GeneratedBlockDrawLaw.FollowerTripleProfile p)
    (beforeOtherBlockLabelEquiv p s)
  let eAfter := MeasurableEquiv.piCongrLeft
    (fun _ : {q : Fin (n_boot p) // s.val < q.val} =>
      GeneratedBlockDrawLaw.FollowerTripleProfile p)
    (afterOtherBlockLabelEquiv p s)
  exact e.trans (eBefore.prodCongr eAfter)

theorem measurePreserving_otherFollowerBlocksPrefixLaterEquiv
    (p : Parameters) (s : Fin (n_boot p)) :
    MeasurePreserving (otherFollowerBlocksPrefixLaterEquiv p s)
      (Measure.pi (fun _ : GeneratedBlockDrawLaw.OtherBlockLabels p s =>
        PrivateSourceStreams.blockScalarProfileLaw p))
      ((Measure.pi (fun _ : {q : Fin (n_boot p) // q.val < s.val} =>
          PrivateSourceStreams.blockScalarProfileLaw p)).prod
        (Measure.pi (fun _ : {q : Fin (n_boot p) // s.val < q.val} =>
          PrivateSourceStreams.blockScalarProfileLaw p))) := by
  let e := MeasurableEquiv.piEquivPiSubtypeProd
    (fun _ : GeneratedBlockDrawLaw.OtherBlockLabels p s =>
      GeneratedBlockDrawLaw.FollowerTripleProfile p)
    (fun q => q.1.val < s.val)
  have hsplit := measurePreserving_piEquivPiSubtypeProd
    (fun _ : GeneratedBlockDrawLaw.OtherBlockLabels p s =>
      PrivateSourceStreams.blockScalarProfileLaw p)
    (fun q => q.1.val < s.val)
  have hbefore := measurePreserving_piCongrLeft
    (fun _ : {q : Fin (n_boot p) // q.val < s.val} =>
      PrivateSourceStreams.blockScalarProfileLaw p)
    (beforeOtherBlockLabelEquiv p s)
  have hafter := measurePreserving_piCongrLeft
    (fun _ : {q : Fin (n_boot p) // s.val < q.val} =>
      PrivateSourceStreams.blockScalarProfileLaw p)
    (afterOtherBlockLabelEquiv p s)
  let eBefore := MeasurableEquiv.piCongrLeft
    (fun _ : {q : Fin (n_boot p) // q.val < s.val} =>
      GeneratedBlockDrawLaw.FollowerTripleProfile p)
    (beforeOtherBlockLabelEquiv p s)
  let eAfter := MeasurableEquiv.piCongrLeft
    (fun _ : {q : Fin (n_boot p) // s.val < q.val} =>
      GeneratedBlockDrawLaw.FollowerTripleProfile p)
    (afterOtherBlockLabelEquiv p s)
  change MeasurePreserving (e.trans (eBefore.prodCongr eAfter)) _ _
  exact (hbefore.prod hafter).comp hsplit

def beforeOtherTargetLabelEquiv (p : Parameters) (s : Fin (n_boot p)) :
    BeforeOtherBlockLabel p s ≃ {q : Fin (n_boot p) // q.val < s.val} :=
  beforeOtherBlockLabelEquiv p s

def afterOtherTargetLabelEquiv (p : Parameters) (s : Fin (n_boot p)) :
    AfterOtherBlockLabel p s ≃ {q : Fin (n_boot p) // s.val < q.val} :=
  afterOtherBlockLabelEquiv p s

def otherTargetScalarsPrefixLaterEquiv (p : Parameters) (s : Fin (n_boot p)) :
    GeneratedBlockDrawLaw.OtherTargetScalars p s ≃ᵐ
      (GeneratedBootstrapBlockFiltrationRepair.TargetPrefix p s.val ×
        LaterTargetScalars p s) := by
  let e := MeasurableEquiv.piEquivPiSubtypeProd
    (fun _ : GeneratedBlockDrawLaw.OtherBlockLabels p s =>
      BootstrapPrivateRoundStreams.Scalar) (fun q => q.1.val < s.val)
  let eBefore := MeasurableEquiv.piCongrLeft
    (fun _ : {q : Fin (n_boot p) // q.val < s.val} =>
      BootstrapPrivateRoundStreams.Scalar) (beforeOtherTargetLabelEquiv p s)
  let eAfter := MeasurableEquiv.piCongrLeft
    (fun _ : {q : Fin (n_boot p) // s.val < q.val} =>
      BootstrapPrivateRoundStreams.Scalar) (afterOtherTargetLabelEquiv p s)
  exact e.trans (eBefore.prodCongr eAfter)

theorem measurePreserving_otherTargetScalarsPrefixLaterEquiv
    (p : Parameters) (s : Fin (n_boot p)) :
    MeasurePreserving (otherTargetScalarsPrefixLaterEquiv p s)
      (Measure.pi (fun _ : GeneratedBlockDrawLaw.OtherBlockLabels p s =>
        ContinuousCategorical.uniform))
      ((Measure.pi (fun _ : {q : Fin (n_boot p) // q.val < s.val} =>
          ContinuousCategorical.uniform)).prod
        (Measure.pi (fun _ : {q : Fin (n_boot p) // s.val < q.val} =>
          ContinuousCategorical.uniform))) := by
  let e := MeasurableEquiv.piEquivPiSubtypeProd
    (fun _ : GeneratedBlockDrawLaw.OtherBlockLabels p s =>
      BootstrapPrivateRoundStreams.Scalar) (fun q => q.1.val < s.val)
  have hsplit := measurePreserving_piEquivPiSubtypeProd
    (fun _ : GeneratedBlockDrawLaw.OtherBlockLabels p s => ContinuousCategorical.uniform)
    (fun q => q.1.val < s.val)
  have hbefore := measurePreserving_piCongrLeft
    (fun _ : {q : Fin (n_boot p) // q.val < s.val} =>
      ContinuousCategorical.uniform) (beforeOtherTargetLabelEquiv p s)
  have hafter := measurePreserving_piCongrLeft
    (fun _ : {q : Fin (n_boot p) // s.val < q.val} =>
      ContinuousCategorical.uniform) (afterOtherTargetLabelEquiv p s)
  let eBefore := MeasurableEquiv.piCongrLeft
    (fun _ : {q : Fin (n_boot p) // q.val < s.val} =>
      BootstrapPrivateRoundStreams.Scalar) (beforeOtherTargetLabelEquiv p s)
  let eAfter := MeasurableEquiv.piCongrLeft
    (fun _ : {q : Fin (n_boot p) // s.val < q.val} =>
      BootstrapPrivateRoundStreams.Scalar) (afterOtherTargetLabelEquiv p s)
  change MeasurePreserving (e.trans (eBefore.prodCongr eAfter)) _ _
  exact (hbefore.prod hafter).comp hsplit

abbrev BeforeOtherRoundLabel (p : Parameters) (s : Fin (n_boot p)) :=
  {label : BootstrapPrivateRoundStreams.PlayerRoundLabel p //
    label.2.val < ReferenceInitializationRun.elapsed p s.val}

abbrev AfterOtherRoundLabel (p : Parameters) (s : Fin (n_boot p)) :=
  {label : BootstrapPrivateRoundStreams.PlayerRoundLabel p //
    ¬ label.2.val < ReferenceInitializationRun.elapsed p s.val}

def afterOtherRoundLabelEquiv (p : Parameters) (s : Fin (n_boot p)) :
    AfterOtherRoundLabel p s ≃
      {label : BootstrapPrivateRoundStreams.PlayerRoundLabel p //
        ReferenceInitializationRun.elapsed p s.val ≤ label.2.val} where
  toFun label := ⟨label.1, by omega⟩
  invFun label := ⟨label.1, by omega⟩
  left_inv label := by apply Subtype.ext; rfl
  right_inv label := by apply Subtype.ext; rfl

def playerRoundScalarsPrefixFutureEquiv (p : Parameters) (s : Fin (n_boot p)) :
    BootstrapPrivateRoundStreams.PlayerRoundScalars p ≃ᵐ
      (GeneratedBootstrapBlockFiltrationRepair.RoundScalarPrefix p s.val ×
        FutureRoundScalars p s) := by
  let e := MeasurableEquiv.piEquivPiSubtypeProd
    (fun _ : BootstrapPrivateRoundStreams.PlayerRoundLabel p =>
      BootstrapPrivateRoundStreams.Scalar)
    (fun label => label.2.val < ReferenceInitializationRun.elapsed p s.val)
  let eAfter := MeasurableEquiv.piCongrLeft
    (fun _ : {label : BootstrapPrivateRoundStreams.PlayerRoundLabel p //
      ReferenceInitializationRun.elapsed p s.val ≤ label.2.val} =>
        BootstrapPrivateRoundStreams.Scalar) (afterOtherRoundLabelEquiv p s)
  exact e.trans ((MeasurableEquiv.refl _).prodCongr eAfter)

theorem measurePreserving_playerRoundScalarsPrefixFutureEquiv
    (p : Parameters) (s : Fin (n_boot p)) :
    MeasurePreserving (playerRoundScalarsPrefixFutureEquiv p s)
      (BootstrapPrivateRoundStreams.playerRoundScalarLaw p)
      ((Measure.pi (fun _ : {label : BootstrapPrivateRoundStreams.PlayerRoundLabel p //
          label.2.val < ReferenceInitializationRun.elapsed p s.val} =>
            ContinuousCategorical.uniform)).prod
        (Measure.pi (fun _ : {label : BootstrapPrivateRoundStreams.PlayerRoundLabel p //
          ReferenceInitializationRun.elapsed p s.val ≤ label.2.val} =>
            ContinuousCategorical.uniform))) := by
  let e := MeasurableEquiv.piEquivPiSubtypeProd
    (fun _ : BootstrapPrivateRoundStreams.PlayerRoundLabel p =>
      BootstrapPrivateRoundStreams.Scalar)
    (fun label => label.2.val < ReferenceInitializationRun.elapsed p s.val)
  have hsplit := measurePreserving_piEquivPiSubtypeProd
    (fun _ : BootstrapPrivateRoundStreams.PlayerRoundLabel p =>
      ContinuousCategorical.uniform)
    (fun label => label.2.val < ReferenceInitializationRun.elapsed p s.val)
  have hafter := measurePreserving_piCongrLeft
    (fun _ : {label : BootstrapPrivateRoundStreams.PlayerRoundLabel p //
      ReferenceInitializationRun.elapsed p s.val ≤ label.2.val} =>
        ContinuousCategorical.uniform) (afterOtherRoundLabelEquiv p s)
  let eAfter := MeasurableEquiv.piCongrLeft
    (fun _ : {label : BootstrapPrivateRoundStreams.PlayerRoundLabel p //
      ReferenceInitializationRun.elapsed p s.val ≤ label.2.val} =>
        BootstrapPrivateRoundStreams.Scalar) (afterOtherRoundLabelEquiv p s)
  change MeasurePreserving (e.trans ((MeasurableEquiv.refl _).prodCongr eAfter)) _ _
  exact ((MeasurePreserving.id _).prod hafter).comp hsplit

/-- Reorder the seven independent factors after the three subtype splits.
Every leaf keeps its label and only the displayed product grouping changes. -/
def privateFactorLayoutEquiv {A B J C D E F : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace J]
    [MeasurableSpace C] [MeasurableSpace D] [MeasurableSpace E]
    [MeasurableSpace F] :
    ((A × B) × (J × ((C × D) × (E × F)))) ≃ᵐ
      ((A × (E × C)) × (J × (B × (F × D)))) := by
  let eFlat : ((A × B) × (J × ((C × D) × (E × F)))) ≃ᵐ
      A × (B × (J × (C × (D × (E × F))))) :=
    MeasurableEquiv.prodAssoc.trans <|
      MeasurableEquiv.prodCongr (MeasurableEquiv.refl A) <|
        MeasurableEquiv.prodCongr (MeasurableEquiv.refl B) <|
          MeasurableEquiv.prodCongr (MeasurableEquiv.refl J)
            MeasurableEquiv.prodAssoc
  let eRecoverChunks : A × (B × (J × (C × (D × (E × F))))) ≃ᵐ
      A × (B × (J × ((C × D) × (E × F)))) :=
    MeasurableEquiv.prodCongr (MeasurableEquiv.refl A) <|
      MeasurableEquiv.prodCongr (MeasurableEquiv.refl B) <|
        MeasurableEquiv.prodCongr (MeasurableEquiv.refl J)
          MeasurableEquiv.prodAssoc.symm
  let eGroupTail : A × (B × (J × ((C × D) × (E × F)))) ≃ᵐ
      ((A × (B × (J × (C × D)))) × (E × F)) :=
    ((MeasurableEquiv.prodCongr (MeasurableEquiv.refl A)
        (MeasurableEquiv.prodCongr (MeasurableEquiv.refl B)
          MeasurableEquiv.prodAssoc.symm)).trans <|
      MeasurableEquiv.prodCongr (MeasurableEquiv.refl A)
        MeasurableEquiv.prodAssoc.symm).trans MeasurableEquiv.prodAssoc.symm
  let eMoveE : ((A × (B × (J × (C × D)))) × (E × F)) ≃ᵐ
      A × (E × (F × (B × (J × (C × D))))) :=
    MeasurableEquiv.prodAssoc.trans <|
      MeasurableEquiv.prodCongr (MeasurableEquiv.refl A)
        (MeasurableEquiv.prodComm.trans MeasurableEquiv.prodAssoc)
  let eRest1 : F × (B × (J × (C × D))) ≃ᵐ
      (F × (B × J)) × (C × D) :=
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl F)
      MeasurableEquiv.prodAssoc.symm).trans MeasurableEquiv.prodAssoc.symm
  let eRest2 : (F × (B × J)) × (C × D) ≃ᵐ
      C × (D × (F × (B × J))) :=
    MeasurableEquiv.prodComm.trans MeasurableEquiv.prodAssoc
  let eTail : D × (F × (B × J)) ≃ᵐ J × (B × (F × D)) :=
    (MeasurableEquiv.prodAssoc.symm.trans MeasurableEquiv.prodComm).trans <|
      (MeasurableEquiv.prodCongr MeasurableEquiv.prodComm MeasurableEquiv.prodComm).trans
        MeasurableEquiv.prodAssoc
  let eFinish : A × (E × (C × (J × (B × (F × D))))) ≃ᵐ
      (A × (E × C)) × (J × (B × (F × D))) :=
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl A)
      MeasurableEquiv.prodAssoc.symm).trans MeasurableEquiv.prodAssoc.symm
  exact eFlat.trans <| eRecoverChunks.trans <| eGroupTail.trans <| eMoveE.trans <|
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl A)
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl E)
        (eRest1.trans <| eRest2.trans <|
          MeasurableEquiv.prodCongr (MeasurableEquiv.refl C) eTail))).trans eFinish

theorem measurePreserving_privateFactorLayoutEquiv
    {A B J C D E F : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace J]
    [MeasurableSpace C] [MeasurableSpace D] [MeasurableSpace E]
    [MeasurableSpace F]
    (μA : Measure A) (μB : Measure B) (μJ : Measure J)
    (μC : Measure C) (μD : Measure D) (μE : Measure E) (μF : Measure F)
    [SFinite μA] [SFinite μB] [SFinite μJ] [SFinite μC]
    [SFinite μD] [SFinite μE] [SFinite μF] :
    MeasurePreserving (privateFactorLayoutEquiv :
      ((A × B) × (J × ((C × D) × (E × F)))) ≃ᵐ
        ((A × (E × C)) × (J × (B × (F × D)))))
      ((μA.prod μB).prod (μJ.prod ((μC.prod μD).prod (μE.prod μF))))
      ((μA.prod (μE.prod μC)).prod (μJ.prod (μB.prod (μF.prod μD)))) := by
  let μCD := μC.prod μD
  let μEF := μE.prod μF
  let μX := μB.prod (μJ.prod μCD)
  let hFlat0 := measurePreserving_prodAssoc μA μB (μJ.prod (μCD.prod μEF))
  let hFlat1 := (MeasurePreserving.id μA).prod <|
    (MeasurePreserving.id μB).prod <|
      (MeasurePreserving.id μJ).prod (measurePreserving_prodAssoc μC μD μEF)
  let hFlat := hFlat1.comp hFlat0
  let hRecover := (MeasurePreserving.id μA).prod <|
    (MeasurePreserving.id μB).prod <|
      (MeasurePreserving.id μJ).prod
        (measurePreserving_prodAssoc μC μD μEF).symm
  let hGroup1 := (MeasurePreserving.id μA).prod <|
    (MeasurePreserving.id μB).prod
      (measurePreserving_prodAssoc μJ μCD μEF).symm
  let hGroup2 := (MeasurePreserving.id μA).prod
    (measurePreserving_prodAssoc μB (μJ.prod μCD) μEF).symm
  let hGroup3 := (measurePreserving_prodAssoc μA μX μEF).symm
  let hGroup := hGroup3.comp (hGroup2.comp hGroup1)
  let hMove0 := measurePreserving_prodAssoc μA μX μEF
  let hMove1 := (MeasurePreserving.id μA).prod
    (Measure.measurePreserving_swap (μ := μX) (ν := μEF))
  let hMove2 := (MeasurePreserving.id μA).prod
    (measurePreserving_prodAssoc μE μF μX)
  let hMove := hMove2.comp (hMove1.comp hMove0)
  let hRest1 := ((measurePreserving_prodAssoc μF (μB.prod μJ) μCD).symm).comp <|
    (MeasurePreserving.id μF).prod (measurePreserving_prodAssoc μB μJ μCD).symm
  let hRest2 := (measurePreserving_prodAssoc μC μD (μF.prod (μB.prod μJ))).comp <|
    Measure.measurePreserving_swap (μ := μF.prod (μB.prod μJ)) (ν := μCD)
  let hTail1 := (measurePreserving_prodAssoc μD μF (μB.prod μJ)).symm
  let hTail2 := Measure.measurePreserving_swap (μ := μD.prod μF) (ν := μB.prod μJ)
  let hTail3 := (Measure.measurePreserving_swap (μ := μB) (ν := μJ)).prod
    (Measure.measurePreserving_swap (μ := μD) (ν := μF))
  let hTail4 := measurePreserving_prodAssoc μJ μB (μF.prod μD)
  let hTail := hTail4.comp (hTail3.comp (hTail2.comp hTail1))
  let hRest := ((MeasurePreserving.id μC).prod hTail).comp <|
    hRest2.comp hRest1
  let hEnd0 := (MeasurePreserving.id μA).prod <|
    (MeasurePreserving.id μE).prod hRest
  let μY := μJ.prod (μB.prod (μF.prod μD))
  let hEnd1 := (MeasurePreserving.id μA).prod
    (measurePreserving_prodAssoc μE μC μY).symm
  let hEnd2 := (measurePreserving_prodAssoc μA (μE.prod μC) μY).symm
  let hEnd := hEnd2.comp (hEnd1.comp hEnd0)
  change MeasurePreserving (privateFactorLayoutEquiv) _ _
  exact hEnd.comp (hMove.comp (hGroup.comp (hRecover.comp hFlat)))

/-- The source-private prefix marginal, before adding the calendar prefix. -/
def sourcePrefixPrivateLaw (p : Parameters) (s : Fin (n_boot p)) :
    Measure (SourcePrefixPrivate p s) :=
  (Measure.pi (fun _ : {q : Fin (n_boot p) // q.val < s.val} =>
      PrivateSourceStreams.blockScalarProfileLaw p)).prod
    ((Measure.pi (fun _ : {q : Fin (n_boot p) // q.val < s.val} =>
        ContinuousCategorical.uniform)).prod
      (Measure.pi (fun _ : {label : BootstrapPrivateRoundStreams.PlayerRoundLabel p //
        label.2.val < ReferenceInitializationRun.elapsed p s.val} =>
          ContinuousCategorical.uniform)))

instance sourcePrefixPrivateLaw_probability (p : Parameters) (s : Fin (n_boot p)) :
    IsProbabilityMeasure (sourcePrefixPrivateLaw p s) := by
  dsimp [sourcePrefixPrivateLaw]
  infer_instance

/-- Reassociate the accepted other-private carrier without changing labels. -/
def otherPrivateReassocEquiv (p : Parameters) (s : Fin (n_boot p)) :
    GeneratedBlockDrawLaw.OtherPrivateCoordinates p s ≃ᵐ
      GeneratedBlockDrawLaw.OtherFollowerBlocks p s ×
        (BootstrapPrivateRoundStreams.Scalar ×
          (BootstrapPrivateRoundStreams.PlayerRoundScalars p ×
            GeneratedBlockDrawLaw.OtherTargetScalars p s)) :=
  ((MeasurableEquiv.prodCongr MeasurableEquiv.prodAssoc
      (MeasurableEquiv.refl _)).trans MeasurableEquiv.prodAssoc).trans <|
    MeasurableEquiv.prodCongr (MeasurableEquiv.refl _)
      MeasurableEquiv.prodAssoc

/-- Split the exact `otherPrivateLaw` carrier into its source-prefix
coordinates and the retained later/J/future-scalar remainder. -/
def otherPrivatePrefixRemainderEquiv (p : Parameters) (s : Fin (n_boot p)) :
    GeneratedBlockDrawLaw.OtherPrivateCoordinates p s ≃ᵐ
      (SourcePrefixPrivate p s × Remainder p s) := by
  let e := otherPrivateReassocEquiv p s
  let f := MeasurableEquiv.prodCongr
    (otherFollowerBlocksPrefixLaterEquiv p s)
    (MeasurableEquiv.prodCongr
      (MeasurableEquiv.refl BootstrapPrivateRoundStreams.Scalar)
      (MeasurableEquiv.prodCongr
        (playerRoundScalarsPrefixFutureEquiv p s)
        (otherTargetScalarsPrefixLaterEquiv p s)))
  exact e.trans (f.trans (privateFactorLayoutEquiv))

theorem measurePreserving_otherPrivatePrefixRemainderEquiv
    (p : Parameters) (s : Fin (n_boot p)) :
    MeasurePreserving (otherPrivatePrefixRemainderEquiv p s)
      (GeneratedBlockDrawLaw.otherPrivateLaw p s)
      ((sourcePrefixPrivateLaw p s).prod (remainderLaw p s)) := by
  let μOtherBlocks := Measure.pi (fun _ : GeneratedBlockDrawLaw.OtherBlockLabels p s =>
    PrivateSourceStreams.blockScalarProfileLaw p)
  let μJ := ContinuousCategorical.uniform
  let μRounds := BootstrapPrivateRoundStreams.playerRoundScalarLaw p
  let μOtherTargets := Measure.pi
    (fun _ : GeneratedBlockDrawLaw.OtherBlockLabels p s => ContinuousCategorical.uniform)
  let μBlockPrefix := Measure.pi
    (fun _ : {q : Fin (n_boot p) // q.val < s.val} =>
      PrivateSourceStreams.blockScalarProfileLaw p)
  let μBlockLater := Measure.pi
    (fun _ : {q : Fin (n_boot p) // s.val < q.val} =>
      PrivateSourceStreams.blockScalarProfileLaw p)
  let μTargetPrefix := Measure.pi
    (fun _ : {q : Fin (n_boot p) // q.val < s.val} => ContinuousCategorical.uniform)
  let μTargetLater := Measure.pi
    (fun _ : {q : Fin (n_boot p) // s.val < q.val} => ContinuousCategorical.uniform)
  let μRoundPrefix := Measure.pi
    (fun _ : {label : BootstrapPrivateRoundStreams.PlayerRoundLabel p //
      label.2.val < ReferenceInitializationRun.elapsed p s.val} =>
        ContinuousCategorical.uniform)
  let μRoundFuture := Measure.pi
    (fun _ : {label : BootstrapPrivateRoundStreams.PlayerRoundLabel p //
      ReferenceInitializationRun.elapsed p s.val ≤ label.2.val} =>
        ContinuousCategorical.uniform)
  let hReassoc0 := (measurePreserving_prodAssoc μOtherBlocks μJ μRounds).prod
    (MeasurePreserving.id μOtherTargets)
  let hReassoc1 := measurePreserving_prodAssoc μOtherBlocks (μJ.prod μRounds)
    μOtherTargets
  let hReassoc2 := (MeasurePreserving.id μOtherBlocks).prod
    (measurePreserving_prodAssoc μJ μRounds μOtherTargets)
  let hReassoc := hReassoc2.comp (hReassoc1.comp hReassoc0)
  let hSplitBlocks := measurePreserving_otherFollowerBlocksPrefixLaterEquiv p s
  let hSplitRounds := measurePreserving_playerRoundScalarsPrefixFutureEquiv p s
  let hSplitTargets := measurePreserving_otherTargetScalarsPrefixLaterEquiv p s
  let hSplit := (hSplitBlocks.prod <|
      (MeasurePreserving.id μJ).prod (hSplitRounds.prod hSplitTargets)).comp hReassoc
  let hLayout := measurePreserving_privateFactorLayoutEquiv
    μBlockPrefix μBlockLater μJ μRoundPrefix μRoundFuture μTargetPrefix μTargetLater
  have hResult := hLayout.comp hSplit
  let eSplit := (otherFollowerBlocksPrefixLaterEquiv p s).prodCongr
    ((MeasurableEquiv.refl BootstrapPrivateRoundStreams.Scalar).prodCongr
      ((playerRoundScalarsPrefixFutureEquiv p s).prodCongr
        (otherTargetScalarsPrefixLaterEquiv p s)))
  let f : GeneratedBlockDrawLaw.OtherPrivateCoordinates p s →
      SourcePrefixPrivate p s × Remainder p s := fun x =>
    privateFactorLayoutEquiv (eSplit (otherPrivateReassocEquiv p s x))
  change MeasurePreserving f
    (GeneratedBlockDrawLaw.otherPrivateLaw p s)
    ((sourcePrefixPrivateLaw p s).prod (remainderLaw p s)) at hResult
  have hfun : f = otherPrivatePrefixRemainderEquiv p s := by
    funext x
    rfl
  exact hResult.congr (otherPrivatePrefixRemainderEquiv p s).measurable_toFun
    (Filter.Eventually.of_forall fun x => congrFun hfun x)

theorem otherPrivatePrefixRemainderEquiv_coordinatorJ
    (p : Parameters) (s : Fin (n_boot p))
    (x : GeneratedBlockDrawLaw.OtherPrivateCoordinates p s) :
    (otherPrivatePrefixRemainderEquiv p s x).2.1 = x.1.1.2 := by
  simp [otherPrivatePrefixRemainderEquiv, otherPrivateReassocEquiv,
    privateFactorLayoutEquiv,
    MeasurableEquiv.prodAssoc, MeasurableEquiv.prodComm,
    MeasurableEquiv.prodCongr]

theorem otherPrivatePrefixRemainderEquiv_laterFollower
    (p : Parameters) (s : Fin (n_boot p))
    (x : GeneratedBlockDrawLaw.OtherPrivateCoordinates p s)
    (q : {q : Fin (n_boot p) // s.val < q.val}) :
    (otherPrivatePrefixRemainderEquiv p s x).2.2.1 q =
      (otherFollowerBlocksPrefixLaterEquiv p s x.1.1.1).2 q := by
  simp [otherPrivatePrefixRemainderEquiv, otherPrivateReassocEquiv,
    privateFactorLayoutEquiv,
    MeasurableEquiv.prodAssoc, MeasurableEquiv.prodComm,
    MeasurableEquiv.prodCongr]

theorem otherPrivatePrefixRemainderEquiv_laterTarget
    (p : Parameters) (s : Fin (n_boot p))
    (x : GeneratedBlockDrawLaw.OtherPrivateCoordinates p s)
    (q : {q : Fin (n_boot p) // s.val < q.val}) :
    (otherPrivatePrefixRemainderEquiv p s x).2.2.2.1 q =
      (otherTargetScalarsPrefixLaterEquiv p s x.2).2 q := by
  simp [otherPrivatePrefixRemainderEquiv, otherPrivateReassocEquiv,
    privateFactorLayoutEquiv,
    MeasurableEquiv.prodAssoc, MeasurableEquiv.prodComm,
    MeasurableEquiv.prodCongr]

theorem otherPrivatePrefixRemainderEquiv_futureRound
    (p : Parameters) (s : Fin (n_boot p))
    (x : GeneratedBlockDrawLaw.OtherPrivateCoordinates p s)
    (label : {label : BootstrapPrivateRoundStreams.PlayerRoundLabel p //
      ReferenceInitializationRun.elapsed p s.val ≤ label.2.val}) :
    (otherPrivatePrefixRemainderEquiv p s x).2.2.2.2 label =
      (playerRoundScalarsPrefixFutureEquiv p s x.1.2).2 label := by
  simp [otherPrivatePrefixRemainderEquiv, otherPrivateReassocEquiv,
    privateFactorLayoutEquiv,
    MeasurableEquiv.prodAssoc, MeasurableEquiv.prodComm,
    MeasurableEquiv.prodCongr]

/-- Move the exact strict-calendar past before the source-private prefix and
leave the remainder last. -/
def sidePrefixLayoutEquiv {P R C : Type*}
    [MeasurableSpace P] [MeasurableSpace R] [MeasurableSpace C] :
    ((P × R) × C) ≃ᵐ ((C × P) × R) :=
  MeasurableEquiv.prodAssoc.trans <|
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl P)
      MeasurableEquiv.prodComm).trans <|
      MeasurableEquiv.prodAssoc.symm.trans <|
        MeasurableEquiv.prodCongr MeasurableEquiv.prodComm
          (MeasurableEquiv.refl R)

theorem measurePreserving_sidePrefixLayoutEquiv
    {P R C : Type*} [MeasurableSpace P] [MeasurableSpace R] [MeasurableSpace C]
    (μP : Measure P) (μR : Measure R) (μC : Measure C)
    [SFinite μP] [SFinite μR] [SFinite μC] :
    MeasurePreserving (sidePrefixLayoutEquiv : ((P × R) × C) ≃ᵐ ((C × P) × R))
      ((μP.prod μR).prod μC) ((μC.prod μP).prod μR) := by
  let h0 := measurePreserving_prodAssoc μP μR μC
  let h1 := (MeasurePreserving.id μP).prod
    (Measure.measurePreserving_swap (μ := μR) (ν := μC))
  let h2 := (measurePreserving_prodAssoc μP μC μR).symm
  let h3 := (Measure.measurePreserving_swap (μ := μP) (ν := μC)).prod
    (MeasurePreserving.id μR)
  change MeasurePreserving (sidePrefixLayoutEquiv : ((P × R) × C) ≃ᵐ ((C × P) × R)) _ _
  exact h3.comp (h2.comp (h1.comp h0))

/-- The calendar strict-past and source-private prefix already form the exact
four-component `sourcePrefix` order; all other coordinates stay in `Remainder`. -/
def sidePastPrefixRemainderEquiv (p : Parameters) (s : Fin (n_boot p)) :
    GeneratedBlockStartLaw.SidePast p s ≃ᵐ
      (GeneratedBootstrapBlockFiltrationRepair.SourcePrefix p s.val × Remainder p s) := by
  let e0 := MeasurableEquiv.prodCongr
    (otherPrivatePrefixRemainderEquiv p s)
    (MeasurableEquiv.refl
      (CompleteRowStoppingLaw.PastArray p (GeneratedBlockStartLaw.blockStartIndex p s)))
  exact e0.trans sidePrefixLayoutEquiv

theorem measurePreserving_sidePastPrefixRemainderEquiv
    (p : Parameters) (s : Fin (n_boot p)) :
    MeasurePreserving (sidePastPrefixRemainderEquiv p s)
      (GeneratedBlockStartLaw.sidePastLaw p s)
      ((sourcePrefixLaw p s).prod (remainderLaw p s)) := by
  let μPast := CompleteRowStoppingLaw.pastArrayLaw p
    (GeneratedBlockStartLaw.blockStartIndex p s)
  let hFirst := (measurePreserving_otherPrivatePrefixRemainderEquiv p s).prod
    (MeasurePreserving.id μPast)
  let hLast := measurePreserving_sidePrefixLayoutEquiv
    (sourcePrefixPrivateLaw p s) (remainderLaw p s) μPast
  have hResult := hLast.comp hFirst
  let f : GeneratedBlockStartLaw.SidePast p s →
      GeneratedBootstrapBlockFiltrationRepair.SourcePrefix p s.val × Remainder p s :=
    fun x => sidePrefixLayoutEquiv
      (otherPrivatePrefixRemainderEquiv p s x.1, x.2)
  change MeasurePreserving f (GeneratedBlockStartLaw.sidePastLaw p s)
    ((sourcePrefixLaw p s).prod (remainderLaw p s)) at hResult
  have hfun : f = sidePastPrefixRemainderEquiv p s := by
    funext x
    rfl
  exact hResult.congr (sidePastPrefixRemainderEquiv p s).measurable_toFun
    (Filter.Eventually.of_forall fun x => congrFun hfun x)

/-- Literal law of the original follower triple profile and coordinator target
scalar at block `s`, in the same order as `CurrentCoordinates`. -/
def rawCurrentBlockLaw (p : Parameters) : Measure (RawCurrentBlock p) :=
  PrivateSourceStreams.blockScalarProfileLaw p |>.prod ContinuousCategorical.uniform

instance rawCurrentBlockLaw_probability (p : Parameters) :
    IsProbabilityMeasure (rawCurrentBlockLaw p) := by
  dsimp [rawCurrentBlockLaw]
  infer_instance

/-- The current marginal is the existing current-profile/target factor of the
accepted `profileTargetFutureLaw`; only its enclosing product was reassociated. -/
theorem profileTargetFutureLaw_eq_currentFuture (p : Parameters)
    (s : Fin (n_boot p)) :
    GeneratedBlockStartLaw.profileTargetFutureLaw p s =
      (rawCurrentBlockLaw p).prod
        (CompleteRowStoppingLaw.futureArrayLaw p
          (GeneratedBlockStartLaw.blockStartIndex p s)) := rfl

/-- Final product order: prefix, current original block, full calendar future,
then every retained original remainder coordinate. -/
def causalProductLayoutEquiv {P C F R : Type*}
    [MeasurableSpace P] [MeasurableSpace C] [MeasurableSpace F] [MeasurableSpace R] :
    ((P × R) × (C × F)) ≃ᵐ P × (C × (F × R)) := by
  let eCF : R × (C × F) ≃ᵐ C × (F × R) :=
    (MeasurableEquiv.prodAssoc.symm.trans <|
      (MeasurableEquiv.prodCongr MeasurableEquiv.prodComm
        (MeasurableEquiv.refl F)).trans <|
        (MeasurableEquiv.prodAssoc.trans <|
          MeasurableEquiv.prodCongr (MeasurableEquiv.refl C)
            MeasurableEquiv.prodComm))
  exact MeasurableEquiv.prodAssoc.trans <|
    MeasurableEquiv.prodCongr (MeasurableEquiv.refl P) eCF

theorem measurePreserving_causalProductLayoutEquiv
    {P C F R : Type*} [MeasurableSpace P] [MeasurableSpace C]
    [MeasurableSpace F] [MeasurableSpace R]
    (μP : Measure P) (μC : Measure C) (μF : Measure F) (μR : Measure R)
    [SFinite μP] [SFinite μC] [SFinite μF] [SFinite μR] :
    MeasurePreserving (causalProductLayoutEquiv : ((P × R) × (C × F)) ≃ᵐ
      P × (C × (F × R)))
      ((μP.prod μR).prod (μC.prod μF))
      (μP.prod (μC.prod (μF.prod μR))) := by
  let h0 := measurePreserving_prodAssoc μP μR (μC.prod μF)
  let h1 := (MeasurePreserving.id μP).prod <|
    (measurePreserving_prodAssoc μR μC μF).symm
  let h2 := (MeasurePreserving.id μP).prod <|
    ((Measure.measurePreserving_swap (μ := μR) (ν := μC)).prod
      (MeasurePreserving.id μF))
  let h3 := (MeasurePreserving.id μP).prod (measurePreserving_prodAssoc μC μR μF)
  let h4 := (MeasurePreserving.id μP).prod <|
    (MeasurePreserving.id μC).prod
      (Measure.measurePreserving_swap (μ := μR) (ν := μF))
  have h := h4.comp (h3.comp (h2.comp (h1.comp h0)))
  change MeasurePreserving (causalProductLayoutEquiv : ((P × R) × (C × F)) ≃ᵐ
    P × (C × (F × R))) _ _
  exact h

/-- The original-coordinate causal product equivalence. It is obtained by
splitting the original row/private carrier, splitting the accepted strict
past into the literal source prefix and labelled remainder, and only then
reordering product factors. -/
def causalProductEquiv (p : Parameters) (s : Fin (n_boot p)) :
    GeneratedBootstrapRoundLaw.Coordinates p ≃ᵐ
      (GeneratedBootstrapBlockFiltrationRepair.SourcePrefix p s.val ×
        (RawCurrentBlock p ×
          (EntireFutureRow p s × Remainder p s))) := by
  classical
  let eSplit :
      (GeneratedBlockStartLaw.SidePast p s × GeneratedBlockStartLaw.FutureCoordinates p s) ≃ᵐ
        ((GeneratedBootstrapBlockFiltrationRepair.SourcePrefix p s.val × Remainder p s) ×
          (RawCurrentBlock p × EntireFutureRow p s)) :=
    (sidePastPrefixRemainderEquiv p s).prodCongr
      (MeasurableEquiv.refl (GeneratedBlockStartLaw.FutureCoordinates p s))
  let eLayout :
      ((GeneratedBootstrapBlockFiltrationRepair.SourcePrefix p s.val × Remainder p s) ×
          (RawCurrentBlock p × EntireFutureRow p s)) ≃ᵐ
        (GeneratedBootstrapBlockFiltrationRepair.SourcePrefix p s.val ×
          (RawCurrentBlock p × (EntireFutureRow p s × Remainder p s))) :=
    causalProductLayoutEquiv
  exact (GeneratedBlockStartLaw.analysisSplitEquiv p s).trans (eSplit.trans eLayout)

/-- Exact product marginal of the original current profile/target, entire
future calendar row, and remainder. This is the parenthesization exported by
`causalProductEquiv`. -/
def causalProductLaw (p : Parameters) (s : Fin (n_boot p)) :
    Measure (GeneratedBootstrapBlockFiltrationRepair.SourcePrefix p s.val ×
      (RawCurrentBlock p × (EntireFutureRow p s × Remainder p s))) :=
  sourcePrefixLaw p s |>.prod
    (rawCurrentBlockLaw p |>.prod
      (CompleteRowStoppingLaw.futureArrayLaw p
        (GeneratedBlockStartLaw.blockStartIndex p s) |>.prod (remainderLaw p s)))

instance causalProductLaw_probability (p : Parameters) (s : Fin (n_boot p)) :
    IsProbabilityMeasure (causalProductLaw p s) := by
  dsimp [causalProductLaw]
  infer_instance

/-- The exposed equivalence preserves the exact original law and the stated
four-factor product law. -/
theorem measurePreserving_causalProductEquiv (p : Parameters)
    (s : Fin (n_boot p)) :
    MeasurePreserving (causalProductEquiv p s)
      (GeneratedBootstrapRoundLaw.originalLaw p) (causalProductLaw p s) := by
  classical
  let μCurrent := (PrivateSourceStreams.blockScalarProfileLaw p).prod
    ContinuousCategorical.uniform
  let μFuture := CompleteRowStoppingLaw.futureArrayLaw p
    (GeneratedBlockStartLaw.blockStartIndex p s)
  let hAnalysis := GeneratedBlockStartLaw.measurePreserving_analysisSplitEquiv p s
  let hSide := (measurePreserving_sidePastPrefixRemainderEquiv p s).prod
    (MeasurePreserving.id (GeneratedBlockStartLaw.profileTargetFutureLaw p s))
  let hLayout := measurePreserving_causalProductLayoutEquiv
    (sourcePrefixLaw p s) μCurrent μFuture (remainderLaw p s)
  let h := hLayout.comp (hSide.comp hAnalysis)
  change MeasurePreserving (causalProductEquiv p s)
    (GeneratedBootstrapRoundLaw.originalLaw p) (causalProductLaw p s)
  change MeasurePreserving
    (fun e : GeneratedBootstrapRoundLaw.Coordinates p =>
      causalProductLayoutEquiv
        ((sidePastPrefixRemainderEquiv p s
          (GeneratedBlockStartLaw.analysisSplitEquiv p s e).1),
          (GeneratedBlockStartLaw.analysisSplitEquiv p s e).2))
    (GeneratedBootstrapRoundLaw.originalLaw p) (causalProductLaw p s) at h
  have hfun : (fun e : GeneratedBootstrapRoundLaw.Coordinates p =>
      causalProductLayoutEquiv
        ((sidePastPrefixRemainderEquiv p s (GeneratedBlockStartLaw.analysisSplitEquiv p s e).1),
          (GeneratedBlockStartLaw.analysisSplitEquiv p s e).2)) =
      causalProductEquiv p s := by
    funext e
    simp only [causalProductEquiv, MeasurableEquiv.coe_trans]
    change causalProductLayoutEquiv
      (sidePastPrefixRemainderEquiv p s
        (GeneratedBlockStartLaw.analysisSplitEquiv p s e).1,
        (GeneratedBlockStartLaw.analysisSplitEquiv p s e).2) =
      causalProductLayoutEquiv
        ((sidePastPrefixRemainderEquiv p s).prodCongr
          (MeasurableEquiv.refl (GeneratedBlockStartLaw.FutureCoordinates p s))
          (GeneratedBlockStartLaw.analysisSplitEquiv p s e))
    congr 1
  have h' : MeasurePreserving (fun e : GeneratedBootstrapRoundLaw.Coordinates p =>
      causalProductLayoutEquiv
        ((sidePastPrefixRemainderEquiv p s (GeneratedBlockStartLaw.analysisSplitEquiv p s e).1),
          (GeneratedBlockStartLaw.analysisSplitEquiv p s e).2))
      (GeneratedBootstrapRoundLaw.originalLaw p) (causalProductLaw p s) := by
    simpa only [GeneratedBlockStartLaw.regroupedCoordinatesLaw,
      GeneratedBlockStartLaw.profileTargetFutureLaw, rawCurrentBlockLaw,
      causalProductLaw] using h
  exact h'.congr (causalProductEquiv p s).measurable_toFun
    (Filter.Eventually.of_forall fun e => congrFun hfun e)

/-- Pushforward equality for every measurable set in the displayed product
space, including state-dependent finite partitions chosen downstream. -/
theorem causalProduct_map_eq (p : Parameters) (s : Fin (n_boot p)) :
    (GeneratedBootstrapRoundLaw.originalLaw p).map (causalProductEquiv p s) =
      causalProductLaw p s :=
  (measurePreserving_causalProductEquiv p s).map_eq

/-- Evaluation form of `causalProduct_map_eq`: every measurable set in the
displayed product carrier has exactly its literal product-law mass. -/
theorem causalProduct_preimage_apply (p : Parameters) (s : Fin (n_boot p))
    (E : Set (GeneratedBootstrapBlockFiltrationRepair.SourcePrefix p s.val ×
      (RawCurrentBlock p × (EntireFutureRow p s × Remainder p s))))
    (hE : MeasurableSet E) :
    (GeneratedBootstrapRoundLaw.originalLaw p)
      ((causalProductEquiv p s) ⁻¹' E) = causalProductLaw p s E := by
  rw [← Measure.map_apply (causalProductEquiv p s).measurable hE,
    causalProduct_map_eq]

/-- The first projection is exactly the accepted original-coordinate
`sourcePrefix`; it is not a conditioning history or a replacement carrier. -/
theorem causalProductEquiv_sourcePrefix (p : Parameters) (s : Fin (n_boot p))
    (e : GeneratedBootstrapRoundLaw.Coordinates p) :
    (causalProductEquiv p s e).1 =
      GeneratedBootstrapBlockFiltrationRepair.sourcePrefix p s.val e := by
  apply Prod.ext
  · funext t
    let tPast : CompleteRowStoppingLaw.PastIndex p
        (GeneratedBlockStartLaw.blockStartIndex p s) :=
      ⟨t.1, by rw [GeneratedBlockStartLaw.blockStartIndex_val]; exact t.2⟩
    change (GeneratedBlockStartLaw.analysisSplitEquiv p s e).1.2 tPast =
      GeneratedBootstrapBlockFiltrationRepair.calendarPrefix p s.val e t
    rw [GeneratedBlockStartLaw.analysisSplitEquiv_strictPastRow p s e tPast]
    rfl
  · apply Prod.ext
    · funext q
      change (otherFollowerBlocksPrefixLaterEquiv p s
        ((GeneratedBlockStartLaw.analysisSplitEquiv p s e).1.1.1.1.1)).1 q =
          e.2.1.1 q.1
      simp [otherFollowerBlocksPrefixLaterEquiv, beforeOtherBlockLabelEquiv,
        afterOtherBlockLabelEquiv, GeneratedBlockStartLaw.analysisSplitEquiv_apply,
        MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd,
        MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft,
        MeasurableEquiv.prodCongr]
      let r : GeneratedBlockDrawLaw.OtherBlockLabels p s :=
        ⟨q.1, by
          intro h
          have hv : q.1.val = s.val := congrArg Fin.val h
          omega⟩
      have hsplit := congrArg Prod.fst
        (GeneratedBlockDrawLaw.extendedPrivateBlockSplit_other_block p s e.2 r)
      change ((GeneratedBlockDrawLaw.extendedPrivateBlockSplitEquiv p s e.2).1.1.1.1 r) =
        e.2.1.1 q.1
      simpa [r] using hsplit
    · apply Prod.ext
      · funext q
        change (otherTargetScalarsPrefixLaterEquiv p s
          ((GeneratedBlockStartLaw.analysisSplitEquiv p s e).1.1.2)).1 q =
            e.2.2.2 q.1
        have hindex : ((beforeOtherTargetLabelEquiv p s).symm q).1.1 = q.1 := rfl
        simp [otherTargetScalarsPrefixLaterEquiv, beforeOtherTargetLabelEquiv,
          afterOtherTargetLabelEquiv, GeneratedBlockStartLaw.analysisSplitEquiv_apply,
          GeneratedBlockDrawLaw.extendedPrivateBlockSplit_other_target,
          MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd,
          MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft,
          MeasurableEquiv.prodCongr]
        exact congrArg (fun z : Fin (n_boot p) => e.2.2.2 z) hindex
      · funext label
        change (playerRoundScalarsPrefixFutureEquiv p s
          ((GeneratedBlockStartLaw.analysisSplitEquiv p s e).1.1.1.2)).1 label =
            e.2.2.1 label.1
        simp [playerRoundScalarsPrefixFutureEquiv, afterOtherRoundLabelEquiv,
          GeneratedBlockStartLaw.analysisSplitEquiv_apply,
          GeneratedBlockDrawLaw.extendedPrivateBlockSplit_round_scalars,
          MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd,
          MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft,
          MeasurableEquiv.prodCongr]

/-- The original raw profile and coordinator target scalar remain the current
component pointwise. -/
theorem causalProductEquiv_currentProfile (p : Parameters) (s : Fin (n_boot p))
    (e : GeneratedBootstrapRoundLaw.Coordinates p) :
    (causalProductEquiv p s e).2.1.1 = e.2.1.1 s := by
  change (GeneratedBlockStartLaw.analysisSplitEquiv p s e).2.1.1 = _
  exact GeneratedBlockStartLaw.analysisSplitEquiv_currentProfile p s e

theorem causalProductEquiv_currentTarget (p : Parameters) (s : Fin (n_boot p))
    (e : GeneratedBootstrapRoundLaw.Coordinates p) :
    (causalProductEquiv p s e).2.1.2 = e.2.2.2 s := by
  change (GeneratedBlockStartLaw.analysisSplitEquiv p s e).2.1.2 = _
  exact GeneratedBlockStartLaw.analysisSplitEquiv_currentTargetScalar p s e

/-- Every future calendar entry is the corresponding original complete-row
entry, including all forward bits and the entire continuous control slice. -/
theorem causalProductEquiv_futureEntry (p : Parameters) (s : Fin (n_boot p))
    (e : GeneratedBootstrapRoundLaw.Coordinates p)
    (t : CompleteRowStoppingLaw.FutureIndex p (GeneratedBlockStartLaw.blockStartIndex p s)) :
    (causalProductEquiv p s e).2.2.1 t =
      CompleteRowStoppingLaw.calendarizeRow p e.1 t.1 := by
  change (GeneratedBlockStartLaw.analysisSplitEquiv p s e).2.2 t = _
  exact GeneratedBlockStartLaw.analysisSplitEquiv_entireFutureRow p s e t

/-- The two inverse identities are exposed for the full original carrier and
the displayed product carrier. -/
theorem causalProductEquiv_reconstructOriginal (p : Parameters) (s : Fin (n_boot p))
    (e : GeneratedBootstrapRoundLaw.Coordinates p) :
    (causalProductEquiv p s).symm (causalProductEquiv p s e) = e :=
  (causalProductEquiv p s).symm_apply_apply e

theorem causalProductEquiv_reconstructProduct (p : Parameters) (s : Fin (n_boot p))
    (z : GeneratedBootstrapBlockFiltrationRepair.SourcePrefix p s.val ×
      (RawCurrentBlock p × (EntireFutureRow p s × Remainder p s))) :
    causalProductEquiv p s ((causalProductEquiv p s).symm z) = z :=
  (causalProductEquiv p s).apply_symm_apply z

/-- Every original block label is assigned exactly once to the strict prefix,
the current block, or the strict later-block remainder. -/
theorem blockLabel_partition (p : Parameters) (s q : Fin (n_boot p)) :
    q.val < s.val ∨ q = s ∨ s.val < q.val := by
  rcases lt_trichotomy q.val s.val with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl (Fin.ext h))
  · exact Or.inr (Or.inr h)

/-- Every original player-round scalar is assigned exactly once to the
source prefix or to the remainder at and after the elapsed boundary. -/
theorem playerRoundLabel_partition (p : Parameters) (s : Fin (n_boot p))
    (label : BootstrapPrivateRoundStreams.PlayerRoundLabel p) :
    label.2.val < ReferenceInitializationRun.elapsed p s.val ∨
      ReferenceInitializationRun.elapsed p s.val ≤ label.2.val := by
  omega

/-- The whole calendar is split exactly into the accepted strict past and the
complete future row beginning at the elapsed boundary. -/
theorem calendarLabel_partition (p : Parameters) (s : Fin (n_boot p))
    (t : Fin p.T) :
    t.val < ReferenceInitializationRun.elapsed p s.val ∨
      ReferenceInitializationRun.elapsed p s.val ≤ t.val := by
  omega

/-- The separate coordinator `J` scalar stays in the remainder and is exactly
the original coordinate. -/
theorem causalProductEquiv_remainderCoordinatorJ (p : Parameters)
    (s : Fin (n_boot p)) (e : GeneratedBootstrapRoundLaw.Coordinates p) :
    (causalProductEquiv p s e).2.2.2.1 = e.2.1.2 := by
  change (otherPrivatePrefixRemainderEquiv p s
    (GeneratedBlockStartLaw.analysisSplitEquiv p s e).1.1).2.1 = _
  simp only [otherPrivatePrefixRemainderEquiv_coordinatorJ]
  rw [GeneratedBlockStartLaw.analysisSplitEquiv_apply]
  exact GeneratedBlockDrawLaw.extendedPrivateBlockSplit_coordinatorJ p s e.2

/-- Later follower profiles in the remainder are the original profile entries
at their strict-later labels. -/
theorem causalProductEquiv_remainderFollower (p : Parameters)
    (s : Fin (n_boot p)) (e : GeneratedBootstrapRoundLaw.Coordinates p)
    (q : {q : Fin (n_boot p) // s.val < q.val}) :
    (causalProductEquiv p s e).2.2.2.2.1 q = e.2.1.1 q.1 := by
  change (otherPrivatePrefixRemainderEquiv p s
    (GeneratedBlockStartLaw.analysisSplitEquiv p s e).1.1).2.2.1 q = _
  rw [otherPrivatePrefixRemainderEquiv_laterFollower]
  have ha : (GeneratedBlockStartLaw.analysisSplitEquiv p s e).1.1 =
      (GeneratedBlockDrawLaw.extendedPrivateBlockSplitEquiv p s e.2).1 := by
    rw [GeneratedBlockStartLaw.analysisSplitEquiv_apply]
  rw [ha]
  let r : GeneratedBlockDrawLaw.OtherBlockLabels p s :=
    ((afterOtherBlockLabelEquiv p s).symm q).1
  have hmap : (otherFollowerBlocksPrefixLaterEquiv p s
      ((GeneratedBlockDrawLaw.extendedPrivateBlockSplitEquiv p s e.2).1.1.1.1)).2 q =
      ((GeneratedBlockDrawLaw.extendedPrivateBlockSplitEquiv p s e.2).1.1.1.1) r := by
    simp [otherFollowerBlocksPrefixLaterEquiv, afterOtherBlockLabelEquiv,
      MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd,
      MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft,
      MeasurableEquiv.prodCongr]
    congr 1
  rw [hmap]
  have hsplit := congrArg Prod.fst
    (GeneratedBlockDrawLaw.extendedPrivateBlockSplit_other_block p s e.2 r)
  calc
    _ = e.2.1.1 r.1 := hsplit
    _ = e.2.1.1 q.1 := by
      congr 1

/-- Later target scalars in the remainder are the original target entries at
their strict-later labels. -/
theorem causalProductEquiv_remainderTarget (p : Parameters)
    (s : Fin (n_boot p)) (e : GeneratedBootstrapRoundLaw.Coordinates p)
    (q : {q : Fin (n_boot p) // s.val < q.val}) :
    (causalProductEquiv p s e).2.2.2.2.2.1 q = e.2.2.2 q.1 := by
  change (otherPrivatePrefixRemainderEquiv p s
    (GeneratedBlockStartLaw.analysisSplitEquiv p s e).1.1).2.2.2.1 q = _
  rw [otherPrivatePrefixRemainderEquiv_laterTarget]
  have ha : (GeneratedBlockStartLaw.analysisSplitEquiv p s e).1.1 =
      (GeneratedBlockDrawLaw.extendedPrivateBlockSplitEquiv p s e.2).1 := by
    rw [GeneratedBlockStartLaw.analysisSplitEquiv_apply]
  rw [ha]
  let r : GeneratedBlockDrawLaw.OtherBlockLabels p s :=
    ((afterOtherTargetLabelEquiv p s).symm q).1
  have hmap : (otherTargetScalarsPrefixLaterEquiv p s
      ((GeneratedBlockDrawLaw.extendedPrivateBlockSplitEquiv p s e.2).1.2)).2 q =
      ((GeneratedBlockDrawLaw.extendedPrivateBlockSplitEquiv p s e.2).1.2) r := by
    simp [otherTargetScalarsPrefixLaterEquiv, afterOtherTargetLabelEquiv,
      MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd,
      MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft,
      MeasurableEquiv.prodCongr, r]
  rw [hmap]
  exact GeneratedBlockDrawLaw.extendedPrivateBlockSplit_other_target p s e.2 r

/-- Every player-round scalar on or after the elapsed boundary remains in the
remainder with its original label and value. -/
theorem causalProductEquiv_remainderRoundScalar (p : Parameters)
    (s : Fin (n_boot p)) (e : GeneratedBootstrapRoundLaw.Coordinates p)
    (label : {label : BootstrapPrivateRoundStreams.PlayerRoundLabel p //
      ReferenceInitializationRun.elapsed p s.val ≤ label.2.val}) :
    (causalProductEquiv p s e).2.2.2.2.2.2 label = e.2.2.1 label.1 := by
  change (otherPrivatePrefixRemainderEquiv p s
    (GeneratedBlockStartLaw.analysisSplitEquiv p s e).1.1).2.2.2.2 label = _
  rw [otherPrivatePrefixRemainderEquiv_futureRound]
  have ha : (GeneratedBlockStartLaw.analysisSplitEquiv p s e).1.1 =
      (GeneratedBlockDrawLaw.extendedPrivateBlockSplitEquiv p s e.2).1 := by
    rw [GeneratedBlockStartLaw.analysisSplitEquiv_apply]
  rw [ha]
  have hmap : (playerRoundScalarsPrefixFutureEquiv p s
      ((GeneratedBlockDrawLaw.extendedPrivateBlockSplitEquiv p s e.2).1.1.2)).2 label =
      ((GeneratedBlockDrawLaw.extendedPrivateBlockSplitEquiv p s e.2).1.1.2) label.1 := by
    simp [playerRoundScalarsPrefixFutureEquiv, afterOtherRoundLabelEquiv,
      MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd,
      MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft,
      MeasurableEquiv.prodCongr]
  rw [hmap, GeneratedBlockDrawLaw.extendedPrivateBlockSplit_round_scalars]

/-- Unnormalized cylinder identity for arbitrary measurable events in all four
displayed factors. Null cells stay in the formula as zero products. -/
theorem causalProduct_cylinder (p : Parameters) (s : Fin (n_boot p))
    (A : Set (GeneratedBootstrapBlockFiltrationRepair.SourcePrefix p s.val))
    (B : Set (RawCurrentBlock p)) (F : Set (EntireFutureRow p s))
    (D : Set (Remainder p s))
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hF : MeasurableSet F) (hD : MeasurableSet D) :
    (GeneratedBootstrapRoundLaw.originalLaw p)
      {e | (causalProductEquiv p s e).1 ∈ A ∧
        (causalProductEquiv p s e).2.1 ∈ B ∧
        (causalProductEquiv p s e).2.2.1 ∈ F ∧
        (causalProductEquiv p s e).2.2.2 ∈ D} =
      sourcePrefixLaw p s A *
        (rawCurrentBlockLaw p B *
          (CompleteRowStoppingLaw.futureArrayLaw p
            (GeneratedBlockStartLaw.blockStartIndex p s) F * remainderLaw p s D)) := by
  let box := A ×ˢ (B ×ˢ (F ×ˢ D))
  have hbox : MeasurableSet box :=
    MeasurableSet.prod hA (MeasurableSet.prod hB (MeasurableSet.prod hF hD))
  have hpre : (causalProductEquiv p s) ⁻¹' box =
      {e | (causalProductEquiv p s e).1 ∈ A ∧
        (causalProductEquiv p s e).2.1 ∈ B ∧
        (causalProductEquiv p s e).2.2.1 ∈ F ∧
        (causalProductEquiv p s e).2.2.2 ∈ D} := by
    ext e
    simp [box, Set.mem_preimage, Set.mem_prod]
  calc
    _ = (GeneratedBootstrapRoundLaw.originalLaw p)
        ((causalProductEquiv p s) ⁻¹' box) := by rw [hpre]
    _ = ((GeneratedBootstrapRoundLaw.originalLaw p).map (causalProductEquiv p s)) box := by
      rw [Measure.map_apply (causalProductEquiv p s).measurable hbox]
    _ = causalProductLaw p s box := by rw [causalProduct_map_eq]
    _ = sourcePrefixLaw p s A *
        (rawCurrentBlockLaw p B *
          (CompleteRowStoppingLaw.futureArrayLaw p
            (GeneratedBlockStartLaw.blockStartIndex p s) F * remainderLaw p s D)) := by
      simp only [causalProductLaw, box, Measure.prod_prod]

end Bandits.Support.CausalBootstrapBlockProduct

end
