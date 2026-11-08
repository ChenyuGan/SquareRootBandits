/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.PrelaunchDownAffineProduct
public import Bandits.Support.ReferenceActiveAffinePositiveTest

/-!
# Original-coordinate selected affine pair law

Sources: `sources/zip4/manuscript/appendix_b_communication.tex:25-55`,
`sources/zip4/manuscript/appendix_a_local_protocol.tex:112-137`, and
`sources/zip4/manuscript/08_main_theorem.tex:29-42`.

Only one original affine pair is removed. The remainder retains every other
original coordinate, including all continuous slices and the entire extended
private input with its separate coordinator scalar. The selector uses the
actual continuous slot/follower draws and the original private row index.
The resulting cylinder identities do not assert physical adaptedness,
measurability of physical history, a Boolean hash rule, or manuscript closure.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.CompletePublicTable
open Bandits.Support.ContinuousLearningRows
open Bandits.Support.BootstrapPrivateRoundStreams
open scoped Classical

namespace Bandits.Support.ReferenceSelectedAffinePairLaw

abbrev Parameters := ConstructorDimensions.Parameters
abbrev Pair (p : Parameters) := AffineChannelLaw.Sample (B p)

/-- Original indices other than the single removed index. -/
abbrev Other {ι : Type*} (i : ι) := {j : ι // j ≠ i}

/-- A singleton split of a finite product, using the original factor spaces. -/
def piExtract {ι X : Type*} [DecidableEq ι] [MeasurableSpace X] (i : ι) :
    (ι → X) ≃ᵐ X × (Other i → X) := by
  letI : Unique {j : ι // j = i} :=
    { default := ⟨i, rfl⟩
      uniq := fun j => Subtype.ext j.property }
  exact (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => X) (fun j => j = i)).trans
    ((MeasurableEquiv.piUnique (fun _ : {j : ι // j = i} => X)).prodCongr
      (MeasurableEquiv.refl _))

theorem piExtract_apply {ι X : Type*} [DecidableEq ι] [MeasurableSpace X]
    (i : ι) (x : ι → X) :
    piExtract i x = (x i, fun j : Other i => x j) := rfl

theorem measurePreserving_piExtract {ι X : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace X]
    (i : ι) (μ : Measure X) [SigmaFinite μ] :
    MeasurePreserving (piExtract i) (Measure.pi (fun _ : ι => μ))
      (μ.prod (Measure.pi (fun _ : Other i => μ))) := by
  let : Unique {j : ι // j = i} :=
    { default := ⟨i, rfl⟩
      uniq := fun j => Subtype.ext j.property }
  let : Fintype {j : ι // j = i} := @Subtype.fintype ι (fun j => j = i) _ _
  exact ((measurePreserving_piUnique (fun _ : {j : ι // j = i} => μ)).prod
    (MeasurePreserving.id _)).comp
      (measurePreserving_piEquivPiSubtypeProd (fun _ : ι => μ) (fun j => j = i))

/-- Lift an extraction through a product on its left. -/
def extractLeft {X S R Y : Type*}
    [MeasurableSpace X] [MeasurableSpace S] [MeasurableSpace R] [MeasurableSpace Y]
    (e : X ≃ᵐ S × R) : X × Y ≃ᵐ S × (R × Y) :=
  (e.prodCongr (MeasurableEquiv.refl _)).trans MeasurableEquiv.prodAssoc

/-- Lift an extraction through a product on its right. -/
def extractRight {X S R Y : Type*}
    [MeasurableSpace X] [MeasurableSpace S] [MeasurableSpace R] [MeasurableSpace Y]
    (e : X ≃ᵐ S × R) : Y × X ≃ᵐ S × (Y × R) :=
  ((MeasurableEquiv.refl _).prodCongr e).trans
    (MeasurableEquiv.prodAssoc.symm.trans
      (((MeasurableEquiv.prodComm).prodCongr (MeasurableEquiv.refl _)).trans
        MeasurableEquiv.prodAssoc))

theorem measurePreserving_extractLeft {X S R Y : Type*}
    [MeasurableSpace X] [MeasurableSpace S] [MeasurableSpace R] [MeasurableSpace Y]
    (e : X ≃ᵐ S × R) (μ : Measure X) (σ : Measure S) (ρ : Measure R) (ν : Measure Y)
    [SigmaFinite μ] [SigmaFinite σ] [SigmaFinite ρ] [SigmaFinite ν]
    (h : MeasurePreserving e μ (σ.prod ρ)) :
    MeasurePreserving (extractLeft e) (μ.prod ν) (σ.prod (ρ.prod ν)) :=
  (measurePreserving_prodAssoc σ ρ ν).comp (h.prod (MeasurePreserving.id ν))

theorem measurePreserving_extractRight {X S R Y : Type*}
    [MeasurableSpace X] [MeasurableSpace S] [MeasurableSpace R] [MeasurableSpace Y]
    (e : X ≃ᵐ S × R) (μ : Measure X) (σ : Measure S) (ρ : Measure R) (ν : Measure Y)
    [SigmaFinite μ] [SigmaFinite σ] [SigmaFinite ρ] [SigmaFinite ν]
    (h : MeasurePreserving e μ (σ.prod ρ)) :
    MeasurePreserving (extractRight e) (ν.prod μ) (σ.prod (ν.prod ρ)) := by
  exact (measurePreserving_prodAssoc σ ν ρ).comp
    (((Measure.measurePreserving_swap (μ := ν) (ν := σ)).prod (MeasurePreserving.id ρ)).comp
      ((measurePreserving_prodAssoc ν σ ρ).symm.comp ((MeasurePreserving.id ν).prod h)))

/-- At the distinguished time: the entire continuous slice and all other channels. -/
abbrev TimeRemainder (p : Parameters) (c : Channel p) :=
  Slice p × (Other c → Pair p)

/-- At the distinguished row: current remainder and all other complete times. -/
abbrev LearningRemainder (p : Parameters) (t : Fin p.T) (c : Channel p) :=
  TimeRemainder p c × (Other t → TimeControl p)

/-- The original forward row is retained verbatim. -/
abbrev RowRemainder (p : Parameters) (t : Fin p.T) (c : Channel p) :=
  ForwardRow p × LearningRemainder p t c

/-- All other complete rows, including their forward arrays, are retained verbatim. -/
abbrev RowsRemainder (p : Parameters) (q : Fin (M p)) (t : Fin p.T) (c : Channel p) :=
  RowRemainder p t c × (Other q → CompleteRow p)

/-- The full original source product with only `(q,t,c)`'s pair removed. -/
abbrev Remainder (p : Parameters) (q : Fin (M p)) (t : Fin p.T) (c : Channel p) :=
  (IDArray p × RowsRemainder p q t c) × ExtendedPrivateCoordinates p

def pairLaw (p : Parameters) : Measure (Pair p) := (AffineChannelLaw.jointLaw (B p)).toMeasure

instance (p : Parameters) : IsProbabilityMeasure (pairLaw p) := by
  unfold pairLaw
  infer_instance

def timeRemainderLaw (p : Parameters) (c : Channel p) : Measure (TimeRemainder p c) :=
  (ContinuousControlSlice.sliceLaw p.m p.K).prod (Measure.pi (fun _ : Other c => pairLaw p))

instance (p : Parameters) (c : Channel p) : IsProbabilityMeasure (timeRemainderLaw p c) := by
  unfold timeRemainderLaw
  infer_instance

def learningRemainderLaw (p : Parameters) (t : Fin p.T) (c : Channel p) :
    Measure (LearningRemainder p t c) :=
  (timeRemainderLaw p c).prod (Measure.pi (fun _ : Other t => timeControlLaw p))

instance (p : Parameters) (t : Fin p.T) (c : Channel p) :
    IsProbabilityMeasure (learningRemainderLaw p t c) := by
  unfold learningRemainderLaw
  infer_instance

def rowRemainderLaw (p : Parameters) (t : Fin p.T) (c : Channel p) :
    Measure (RowRemainder p t c) :=
  (forwardRowMeasure p).prod (learningRemainderLaw p t c)

instance (p : Parameters) (t : Fin p.T) (c : Channel p) :
    IsProbabilityMeasure (rowRemainderLaw p t c) := by
  unfold rowRemainderLaw
  infer_instance

def rowsRemainderLaw (p : Parameters) (q : Fin (M p)) (t : Fin p.T) (c : Channel p) :
    Measure (RowsRemainder p q t c) :=
  (rowRemainderLaw p t c).prod (Measure.pi (fun _ : Other q => completeRowMeasure p))

instance (p : Parameters) (q : Fin (M p)) (t : Fin p.T) (c : Channel p) :
    IsProbabilityMeasure (rowsRemainderLaw p q t c) := by
  unfold rowsRemainderLaw
  infer_instance

/-- Literal product of all original retained factors. -/
def remainderLaw (p : Parameters) (q : Fin (M p)) (t : Fin p.T) (c : Channel p) :
    Measure (Remainder p q t c) :=
  ((idArrayMeasure p).prod (rowsRemainderLaw p q t c)).prod (extendedPrivateLaw p)

instance (p : Parameters) (q : Fin (M p)) (t : Fin p.T) (c : Channel p) :
    IsProbabilityMeasure (remainderLaw p q t c) := by
  unfold remainderLaw
  infer_instance

def timePairSplit (p : Parameters) (c : Channel p) :
    TimeControl p ≃ᵐ Pair p × TimeRemainder p c := extractRight (piExtract c)

theorem measurePreserving_timePairSplit (p : Parameters) (c : Channel p) :
    MeasurePreserving (timePairSplit p c) (timeControlLaw p)
      ((pairLaw p).prod (timeRemainderLaw p c)) :=
  measurePreserving_extractRight (piExtract c) _ _ _ _
    (measurePreserving_piExtract c (pairLaw p))

def learningPairSplit (p : Parameters) (t : Fin p.T) (c : Channel p) :
    LearningRow p ≃ᵐ Pair p × LearningRemainder p t c :=
  (piExtract t).trans (extractLeft (timePairSplit p c))

theorem measurePreserving_learningPairSplit (p : Parameters) (t : Fin p.T) (c : Channel p) :
    MeasurePreserving (learningPairSplit p t c) (learningRowLaw p)
      ((pairLaw p).prod (learningRemainderLaw p t c)) :=
  (measurePreserving_extractLeft (timePairSplit p c) _ _ _ _
    (measurePreserving_timePairSplit p c)).comp
      (measurePreserving_piExtract t (timeControlLaw p))

def completeRowPairSplit (p : Parameters) (t : Fin p.T) (c : Channel p) :
    CompleteRow p ≃ᵐ Pair p × RowRemainder p t c :=
  extractRight (learningPairSplit p t c)

theorem measurePreserving_completeRowPairSplit (p : Parameters) (t : Fin p.T) (c : Channel p) :
    MeasurePreserving (completeRowPairSplit p t c) (completeRowMeasure p)
      ((pairLaw p).prod (rowRemainderLaw p t c)) :=
  measurePreserving_extractRight (learningPairSplit p t c) _ _ _ _
    (measurePreserving_learningPairSplit p t c)

def rowsPairSplit (p : Parameters) (q : Fin (M p)) (t : Fin p.T) (c : Channel p) :
    CompleteRows p ≃ᵐ Pair p × RowsRemainder p q t c :=
  (piExtract q).trans (extractLeft (completeRowPairSplit p t c))

theorem measurePreserving_rowsPairSplit (p : Parameters)
    (q : Fin (M p)) (t : Fin p.T) (c : Channel p) :
    MeasurePreserving (rowsPairSplit p q t c) (completeRowsMeasure p)
      ((pairLaw p).prod (rowsRemainderLaw p q t c)) :=
  (measurePreserving_extractLeft (completeRowPairSplit p t c) _ _ _ _
    (measurePreserving_completeRowPairSplit p t c)).comp
      (measurePreserving_piExtract q (completeRowMeasure p))

/-- Lossless measurable split on the full original source input. -/
def fixedPairSplit (p : Parameters) (q : Fin (M p)) (t : Fin p.T) (c : Channel p) :
    SourceInput p ≃ᵐ Pair p × Remainder p q t c :=
  extractLeft (extractRight (rowsPairSplit p q t c))

theorem fixedPairSplit_measurePreserving (p : Parameters)
    (q : Fin (M p)) (t : Fin p.T) (c : Channel p) :
    MeasurePreserving (fixedPairSplit p q t c) (sourceInputLaw p)
      ((AffineChannelLaw.jointLaw (B p)).toMeasure.prod (remainderLaw p q t c)) :=
  measurePreserving_extractLeft (extractRight (rowsPairSplit p q t c)) _ _ _ _
    (measurePreserving_extractRight (rowsPairSplit p q t c) _ _ _ _
      (measurePreserving_rowsPairSplit p q t c))

theorem fixedPairSplit_measurePreserving_symm (p : Parameters)
    (q : Fin (M p)) (t : Fin p.T) (c : Channel p) :
    MeasurePreserving (fixedPairSplit p q t c).symm
      ((AffineChannelLaw.jointLaw (B p)).toMeasure.prod (remainderLaw p q t c))
      (sourceInputLaw p) :=
  (fixedPairSplit_measurePreserving p q t c).symm

theorem sourceInputLaw_map_fixedPairSplit (p : Parameters)
    (q : Fin (M p)) (t : Fin p.T) (c : Channel p) :
    (sourceInputLaw p).map (fixedPairSplit p q t c) =
      (AffineChannelLaw.jointLaw (B p)).toMeasure.prod (remainderLaw p q t c) :=
  (fixedPairSplit_measurePreserving p q t c).map_eq

/-- The extracted pair is literally the reserved original product coordinate. -/
theorem fixedPairSplit_pair (p : Parameters) (q : Fin (M p)) (t : Fin p.T)
    (c : Channel p) (source : SourceInput p) :
    (fixedPairSplit p q t c source).1 = ((source.1.2 q).2 t).2 c := rfl

/-- Reconstruction in both directions uses every retained original coordinate. -/
theorem fixedPairSplit_reconstruct (p : Parameters) (q : Fin (M p)) (t : Fin p.T)
    (c : Channel p) (source : SourceInput p) :
    (fixedPairSplit p q t c).symm (fixedPairSplit p q t c source) = source :=
  (fixedPairSplit p q t c).symm_apply_apply source

theorem fixedPairSplit_split_reconstruct (p : Parameters) (q : Fin (M p)) (t : Fin p.T)
    (c : Channel p) (x : Pair p × Remainder p q t c) :
    fixedPairSplit p q t c ((fixedPairSplit p q t c).symm x) = x :=
  (fixedPairSplit p q t c).apply_symm_apply x

/-- Literal retained coordinates; the two restrictions omit exactly one time
and one row, and the affine restriction omits exactly one channel. -/
theorem fixedPairSplit_remainder (p : Parameters) (q : Fin (M p)) (t : Fin p.T)
    (c : Channel p) (source : SourceInput p) :
    (fixedPairSplit p q t c source).2 =
      ((source.1.1,
        (((source.1.2 q).1,
          ((((source.1.2 q).2 t).1, fun k : Other c => ((source.1.2 q).2 t).2 k),
            fun s : Other t => (source.1.2 q).2 s)),
          fun j : Other q => source.1.2 j)), source.2) := rfl

theorem fixedPairSplit_id (p : Parameters) (q : Fin (M p)) (t : Fin p.T)
    (c : Channel p) (source : SourceInput p) :
    (fixedPairSplit p q t c source).2.1.1 = source.1.1 := rfl

theorem fixedPairSplit_private (p : Parameters) (q : Fin (M p)) (t : Fin p.T)
    (c : Channel p) (source : SourceInput p) :
    (fixedPairSplit p q t c source).2.2 = source.2 := rfl

theorem fixedPairSplit_forward (p : Parameters) (q : Fin (M p)) (t : Fin p.T)
    (c : Channel p) (source : SourceInput p) :
    (fixedPairSplit p q t c source).2.1.2.1.1 = (source.1.2 q).1 := rfl

theorem fixedPairSplit_slice (p : Parameters) (q : Fin (M p)) (t : Fin p.T)
    (c : Channel p) (source : SourceInput p) :
    (fixedPairSplit p q t c source).2.1.2.1.2.1.1 = ((source.1.2 q).2 t).1 := rfl

theorem fixedPairSplit_other_channel (p : Parameters) (q : Fin (M p)) (t : Fin p.T)
    (c : Channel p) (source : SourceInput p) (k : Other c) :
    (fixedPairSplit p q t c source).2.1.2.1.2.1.2 k = ((source.1.2 q).2 t).2 k := rfl

theorem fixedPairSplit_other_time (p : Parameters) (q : Fin (M p)) (t : Fin p.T)
    (c : Channel p) (source : SourceInput p) (s : Other t) :
    (fixedPairSplit p q t c source).2.1.2.1.2.2 s = (source.1.2 q).2 s := rfl

theorem fixedPairSplit_other_row (p : Parameters) (q : Fin (M p)) (t : Fin p.T)
    (c : Channel p) (source : SourceInput p) (j : Other q) :
    (fixedPairSplit p q t c source).2.1.2.2 j = source.1.2 j := rfl

/-- Inverse recovery of the pair, common ID, entire private input, forward row,
entire current continuous slice, every other channel/time/row. -/
theorem fixedPairSplit_inverse_coordinates (p : Parameters) (q : Fin (M p)) (t : Fin p.T)
    (c : Channel p) (a : Pair p) (r : Remainder p q t c) :
    let source := (fixedPairSplit p q t c).symm (a, r)
    ((source.1.2 q).2 t).2 c = a ∧
      source.1.1 = r.1.1 ∧ source.2 = r.2 ∧
      (source.1.2 q).1 = r.1.2.1.1 ∧
      ((source.1.2 q).2 t).1 = r.1.2.1.2.1.1 ∧
      (∀ k : Other c, ((source.1.2 q).2 t).2 k = r.1.2.1.2.1.2 k) ∧
      (∀ s : Other t, (source.1.2 q).2 s = r.1.2.1.2.2 s) ∧
      (∀ j : Other q, source.1.2 j = r.1.2.2 j) := by
  have h := fixedPairSplit_split_reconstruct p q t c (a, r)
  exact ⟨congrArg Prod.fst h, congrArg (fun x => x.2.1.1) h,
    congrArg (fun x => x.2.2) h, congrArg (fun x => x.2.1.2.1.1) h,
    congrArg (fun x => x.2.1.2.1.2.1.1) h,
    fun k => congrArg (fun x => x.2.1.2.1.2.1.2 k) h,
    fun s => congrArg (fun x => x.2.1.2.1.2.2 s) h,
    fun j => congrArg (fun x => x.2.1.2.2 j) h⟩

/-- In particular the separate original coordinator scalar is preserved. -/
theorem fixedPairSplit_jScalar (p : Parameters) (q : Fin (M p)) (t : Fin p.T)
    (c : Channel p) (source : SourceInput p) :
    (fixedPairSplit p q t c source).2.2.1.2 = source.2.1.2 := rfl

/-- All scalar labels survive, including every entry of the full assignment vector. -/
theorem fixedPairSplit_scalar (p : Parameters) (q : Fin (M p)) (t : Fin p.T)
    (c : Channel p) (source : SourceInput p) (l : ContinuousLearningRows.Label p) :
    (fixedPairSplit p q t c source).2.1.2.1.2.1.1 l = ((source.1.2 q).2 t).1 l := rfl

theorem fixedPairSplit_assignmentVector (p : Parameters) (q : Fin (M p)) (t : Fin p.T)
    (c : Channel p) (source : SourceInput p) :
    ContinuousControlSlice.assignmentVector (fixedPairSplit p q t c source).2.1.2.1.2.1.1 =
      ContinuousControlSlice.assignmentVector ((source.1.2 q).2 t).1 := rfl

/-- The same extraction on one original complete row times the entire original
extended private input; no new sampling law is substituted. -/
def originalPairSplit (p : Parameters) (t : Fin p.T) (c : Channel p) :
    GeneratedBootstrapRoundLaw.Coordinates p ≃ᵐ
      Pair p × (RowRemainder p t c × ExtendedPrivateCoordinates p) :=
  extractLeft (completeRowPairSplit p t c)

theorem originalPairSplit_measurePreserving (p : Parameters) (t : Fin p.T) (c : Channel p) :
    MeasurePreserving (originalPairSplit p t c) (GeneratedBootstrapRoundLaw.originalLaw p)
      ((AffineChannelLaw.jointLaw (B p)).toMeasure.prod
        ((rowRemainderLaw p t c).prod (extendedPrivateLaw p))) :=
  measurePreserving_extractLeft (completeRowPairSplit p t c) _ _ _ _
    (measurePreserving_completeRowPairSplit p t c)

theorem originalPairSplit_pair (p : Parameters) (t : Fin p.T) (c : Channel p)
    (source : GeneratedBootstrapRoundLaw.Coordinates p) :
    (originalPairSplit p t c source).1 = (source.1.2 t).2 c := rfl

theorem originalPairSplit_private (p : Parameters) (t : Fin p.T) (c : Channel p)
    (source : GeneratedBootstrapRoundLaw.Coordinates p) :
    (originalPairSplit p t c source).2.2 = source.2 := rfl

theorem originalPairSplit_remainder (p : Parameters) (t : Fin p.T) (c : Channel p)
    (source : GeneratedBootstrapRoundLaw.Coordinates p) :
    (originalPairSplit p t c source).2 =
      ((source.1.1, (((source.1.2 t).1, fun k : Other c => (source.1.2 t).2 k),
        fun s : Other t => source.1.2 s)), source.2) := rfl

theorem originalPairSplit_reconstruct (p : Parameters) (t : Fin p.T) (c : Channel p)
    (source : GeneratedBootstrapRoundLaw.Coordinates p) :
    (originalPairSplit p t c).symm (originalPairSplit p t c source) = source :=
  (originalPairSplit p t c).symm_apply_apply source

theorem originalPairSplit_cylinder (p : Parameters) (t : Fin p.T) (c : Channel p)
    (E : Set (Pair p)) (S : Set (RowRemainder p t c × ExtendedPrivateCoordinates p))
    (hE : MeasurableSet E) (hS : MeasurableSet S) :
    GeneratedBootstrapRoundLaw.originalLaw p
      {source | (originalPairSplit p t c source).1 ∈ E ∧
        (originalPairSplit p t c source).2 ∈ S} =
      (AffineChannelLaw.jointLaw (B p)).toMeasure E *
        ((rowRemainderLaw p t c).prod (extendedPrivateLaw p)) S := by
  change GeneratedBootstrapRoundLaw.originalLaw p (originalPairSplit p t c ⁻¹' (E ×ˢ S)) = _
  rw [← Measure.map_apply (originalPairSplit p t c).measurable (hE.prod hS),
    (originalPairSplit_measurePreserving p t c).map_eq, Measure.prod_prod]

/-- Every measurable original pair/remainder cylinder factors, including null cells. -/
theorem fixedPairSplit_cylinder (p : Parameters) (q : Fin (M p)) (t : Fin p.T)
    (c : Channel p) (E : Set (Pair p)) (S : Set (Remainder p q t c))
    (hE : MeasurableSet E) (hS : MeasurableSet S) :
    sourceInputLaw p {source | (fixedPairSplit p q t c source).1 ∈ E ∧
      (fixedPairSplit p q t c source).2 ∈ S} =
      (AffineChannelLaw.jointLaw (B p)).toMeasure E * remainderLaw p q t c S := by
  change sourceInputLaw p (fixedPairSplit p q t c ⁻¹' (E ×ˢ S)) = _
  rw [← Measure.map_apply (fixedPairSplit p q t c).measurable (hE.prod hS),
    (fixedPairSplit_measurePreserving p q t c).map_eq, Measure.prod_prod]

theorem fixedPairSplit_remainderLaw (p : Parameters) (q : Fin (M p)) (t : Fin p.T)
    (c : Channel p) (S : Set (Remainder p q t c)) (hS : MeasurableSet S) :
    sourceInputLaw p {source | (fixedPairSplit p q t c source).2 ∈ S} =
      remainderLaw p q t c S := by
  simpa only [Set.mem_univ, true_and, measure_univ, one_mul] using
    fixedPairSplit_cylinder p q t c Set.univ S MeasurableSet.univ hS

/-- Literal direction/follower selection; DATA has no affine channel. -/
def channelFromDraws (p : Parameters) (x : PublicDiscreteDraws.Slot × Fin (d p)) :
    Option (Channel p) :=
  if x.1 = PublicDiscreteDraws.downSlot then some (0, x.2)
  else if x.1 = PublicDiscreteDraws.upSlot then some (1, x.2)
  else none

/-- The selector reads the original continuous `slot` and `sel` coordinates.
The follower formula is the one identified with the actual UP sender by
`ReferenceActiveAffinePositiveTest.upSenderIndex_eq_draw`. -/
def selectedChannel (p : Parameters) (slice : Slice p) : Option (Channel p) :=
  channelFromDraws p (PublicDiscreteDraws.slotDraw slice,
    PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K slice)

theorem measurable_selectedChannel (p : Parameters) : Measurable (selectedChannel p) :=
  (measurable_of_finite (channelFromDraws p)).comp
    (PublicDiscreteDraws.measurable_slotDraw.prodMk
      (PublicDiscreteDraws.measurable_selectedFollowerDraw p.two_le_m p.m_lt_K))

/-- Actual original row index and optional selected channel. Keeping the index
also on DATA does not create a DATA affine sample. -/
def selector (p : Parameters) (t : Fin p.T) (source : SourceInput p) :
    Fin (M p) × Option (Channel p) :=
  let j := ActualInitializationPhysicalStep.selectedRowIndex p source
  (j, selectedChannel p ((source.1.2 j).2 t).1)

theorem selector_rowIndex (p : Parameters) (t : Fin p.T) (source : SourceInput p) :
    (selector p t source).1 = PrivateSourceStreams.coordinatorIndex p source.2.1.2 := rfl

theorem selector_eq_iff (p : Parameters) (q : Fin (M p)) (t : Fin p.T)
    (c : Channel p) (source : SourceInput p) :
    selector p t source = (q, some c) ↔
      PrivateSourceStreams.coordinatorIndex p source.2.1.2 = q ∧
        selectedChannel p ((source.1.2 q).2 t).1 = some c := by
  constructor
  · intro h
    have hj := congrArg Prod.fst h
    have hc := congrArg Prod.snd h
    change PrivateSourceStreams.coordinatorIndex p source.2.1.2 = q at hj
    exact ⟨hj, by simpa only [selector, ActualInitializationPhysicalStep.selectedRowIndex, hj]
      using hc⟩
  · rintro ⟨hj, hc⟩
    apply Prod.ext hj
    change selectedChannel p ((source.1.2
      (PrivateSourceStreams.coordinatorIndex p source.2.1.2)).2 t).1 = some c
    rw [hj]
    exact hc

/-- A fixed selector stratum as an event entirely in the retained coordinates. -/
def remainderSelectorEvent (p : Parameters) (q : Fin (M p)) (t : Fin p.T) (c : Channel p) :
    Set (Remainder p q t c) :=
  {r | PrivateSourceStreams.coordinatorIndex p r.2.1.2 = q ∧
    selectedChannel p r.1.2.1.2.1.1 = some c}

theorem measurableSet_remainderSelectorEvent (p : Parameters)
    (q : Fin (M p)) (t : Fin p.T) (c : Channel p) :
    MeasurableSet (remainderSelectorEvent p q t c) := by
  have hj : Measurable (fun r : Remainder p q t c =>
      PrivateSourceStreams.coordinatorIndex p r.2.1.2) :=
    (PrivateSourceStreams.measurable_coordinatorIndex p).comp
      (measurable_snd.comp (measurable_fst.comp measurable_snd))
  have hs : Measurable (fun r : Remainder p q t c =>
      selectedChannel p r.1.2.1.2.1.1) := by
    apply (measurable_selectedChannel p).comp
    fun_prop
  exact (hj (measurableSet_singleton q)).inter (hs (measurableSet_singleton (some c)))

theorem selector_remainder_iff (p : Parameters) (q : Fin (M p)) (t : Fin p.T)
    (c : Channel p) (source : SourceInput p) :
    selector p t source = (q, some c) ↔
      (fixedPairSplit p q t c source).2 ∈ remainderSelectorEvent p q t c :=
  selector_eq_iff p q t c source

/-- Each stratum can impose its own measurable remainder condition. -/
def stratumEvent (p : Parameters) (q : Fin (M p)) (t : Fin p.T) (c : Channel p)
    (S : Set (Remainder p q t c)) : Set (SourceInput p) :=
  {source | selector p t source = (q, some c) ∧ (fixedPairSplit p q t c source).2 ∈ S}

theorem stratumEvent_eq_preimage (p : Parameters) (q : Fin (M p)) (t : Fin p.T)
    (c : Channel p) (S : Set (Remainder p q t c)) :
    stratumEvent p q t c S =
      (fun source => (fixedPairSplit p q t c source).2) ⁻¹'
        (remainderSelectorEvent p q t c ∩ S) := by
  ext source
  exact and_congr_left (fun _ => selector_remainder_iff p q t c source)

theorem measurableSet_stratumEvent (p : Parameters) (q : Fin (M p)) (t : Fin p.T)
    (c : Channel p) (S : Set (Remainder p q t c)) (hS : MeasurableSet S) :
    MeasurableSet (stratumEvent p q t c S) := by
  rw [stratumEvent_eq_preimage]
  exact ((measurableSet_remainderSelectorEvent p q t c).inter hS).preimage
    (measurable_snd.comp (fixedPairSplit p q t c).measurable)

/-- Conditional uniformity without division, valid also on zero-mass strata. -/
theorem selectedPair_stratum_cylinder (p : Parameters) (q : Fin (M p)) (t : Fin p.T)
    (c : Channel p) (S : Set (Remainder p q t c)) (E : Set (Pair p))
    (hS : MeasurableSet S) (hE : MeasurableSet E) :
    sourceInputLaw p {source | source ∈ stratumEvent p q t c S ∧
      ((source.1.2 q).2 t).2 c ∈ E} =
      (AffineChannelLaw.jointLaw (B p)).toMeasure E *
        sourceInputLaw p (stratumEvent p q t c S) := by
  let R := remainderSelectorEvent p q t c ∩ S
  have hR : MeasurableSet R := (measurableSet_remainderSelectorEvent p q t c).inter hS
  have hbase : stratumEvent p q t c S =
      {source | (fixedPairSplit p q t c source).2 ∈ R} :=
    stratumEvent_eq_preimage p q t c S
  have hcyl : {source | source ∈ stratumEvent p q t c S ∧
      ((source.1.2 q).2 t).2 c ∈ E} =
      {source | (fixedPairSplit p q t c source).1 ∈ E ∧
        (fixedPairSplit p q t c source).2 ∈ R} := by
    rw [hbase]
    ext source
    exact and_comm
  rw [hcyl, fixedPairSplit_cylinder p q t c E R hE hR, hbase,
    fixedPairSplit_remainderLaw p q t c R hR]

theorem selectedChannel_of_down (p : Parameters) (slice : Slice p)
    (h : PublicDiscreteDraws.slotDraw slice = PublicDiscreteDraws.downSlot) :
    selectedChannel p slice = some (0,
      PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K slice) := by
  simp only [selectedChannel, channelFromDraws, h, ite_true]
  rfl

theorem selectedChannel_of_up (p : Parameters) (slice : Slice p)
    (h : PublicDiscreteDraws.slotDraw slice = PublicDiscreteDraws.upSlot) :
    selectedChannel p slice = some (1,
      PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K slice) := by
  have hne : PublicDiscreteDraws.upSlot ≠ PublicDiscreteDraws.downSlot := by decide
  simp only [selectedChannel, channelFromDraws, h, hne, ite_false, ite_true]
  rfl

theorem selectedChannel_of_data (p : Parameters) (slice : Slice p)
    (h : PublicDiscreteDraws.slotDraw slice = PublicDiscreteDraws.dataSlot) :
    selectedChannel p slice = none := by
  have hd : PublicDiscreteDraws.dataSlot ≠ PublicDiscreteDraws.downSlot := by decide
  have hu : PublicDiscreteDraws.dataSlot ≠ PublicDiscreteDraws.upSlot := by decide
  simp only [selectedChannel, channelFromDraws, h, hd, hu, ite_false]

/-- The genuinely selected original pair; there is no sample on a DATA slot. -/
def selectedPair (p : Parameters) (t : Fin p.T) (source : SourceInput p) : Option (Pair p) :=
  (selector p t source).2.map
    (fun c => ((source.1.2 (selector p t source).1).2 t).2 c)

theorem selectedPair_of_selector (p : Parameters) (q : Fin (M p)) (t : Fin p.T)
    (c : Channel p) (source : SourceInput p) (h : selector p t source = (q, some c)) :
    selectedPair p t source = some (((source.1.2 q).2 t).2 c) := by
  unfold selectedPair
  rw [h]
  rfl

theorem selectedPair_of_data (p : Parameters) (t : Fin p.T) (source : SourceInput p)
    (h : PublicDiscreteDraws.slotDraw
      ((source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).2 t).1 =
        PublicDiscreteDraws.dataSlot) : selectedPair p t source = none := by
  change (selectedChannel p _).map _ = none
  rw [selectedChannel_of_data p _ h]
  rfl

theorem stratumEvent_disjoint (p : Parameters) (t : Fin p.T)
    (S : (q : Fin (M p)) → (c : Channel p) → Set (Remainder p q t c)) :
    Pairwise (fun a b : Fin (M p) × Channel p =>
      Disjoint (stratumEvent p a.1 t a.2 (S a.1 a.2))
        (stratumEvent p b.1 t b.2 (S b.1 b.2))) := by
  intro a b hab
  apply Set.disjoint_left.mpr
  intro source ha hb
  have heq : (a.1, some a.2) = (b.1, some b.2) := ha.1.symm.trans hb.1
  have hj : a.1 = b.1 :=
    congrArg (fun x : Fin (M p) × Option (Channel p) => x.1) heq
  have hc : some a.2 = some b.2 :=
    congrArg (fun x : Fin (M p) × Option (Channel p) => x.2) heq
  exact hab (Prod.ext hj (Option.some.inj hc))

theorem measurableSet_stratum_pair (p : Parameters) (q : Fin (M p)) (t : Fin p.T)
    (c : Channel p) (S : Set (Remainder p q t c)) (E : Set (Pair p))
    (hS : MeasurableSet S) (hE : MeasurableSet E) :
    MeasurableSet {source | source ∈ stratumEvent p q t c S ∧
      ((source.1.2 q).2 t).2 c ∈ E} :=
  (measurableSet_stratumEvent p q t c S hS).inter
    ((measurable_fst.comp (fixedPairSplit p q t c).measurable) hE)

/-- Exact disjoint-stratum sum, allowing a different remainder condition in
each cell. All row/channel cells are included, even when their mass is zero. -/
theorem selectedPair_cylinder_sum (p : Parameters) (t : Fin p.T)
    (S : (q : Fin (M p)) → (c : Channel p) → Set (Remainder p q t c))
    (E : Set (Pair p)) (hS : ∀ q c, MeasurableSet (S q c)) (hE : MeasurableSet E) :
    sourceInputLaw p (⋃ a : Fin (M p) × Channel p,
      {source | source ∈ stratumEvent p a.1 t a.2 (S a.1 a.2) ∧
        ((source.1.2 a.1).2 t).2 a.2 ∈ E}) =
      (AffineChannelLaw.jointLaw (B p)).toMeasure E *
        ∑ a : Fin (M p) × Channel p,
          sourceInputLaw p (stratumEvent p a.1 t a.2 (S a.1 a.2)) := by
  have hd := stratumEvent_disjoint p t S
  have hde : Pairwise (fun a b : Fin (M p) × Channel p =>
      Disjoint {source | source ∈ stratumEvent p a.1 t a.2 (S a.1 a.2) ∧
        ((source.1.2 a.1).2 t).2 a.2 ∈ E}
      {source | source ∈ stratumEvent p b.1 t b.2 (S b.1 b.2) ∧
        ((source.1.2 b.1).2 t).2 b.2 ∈ E}) := by
    intro a b hab
    exact (hd hab).mono (fun _ h => h.1) (fun _ h => h.1)
  rw [measure_iUnion hde (fun a => measurableSet_stratum_pair p a.1 t a.2
    (S a.1 a.2) E (hS a.1 a.2) hE), tsum_fintype]
  simp_rw [selectedPair_stratum_cylinder p _ t _ _ E (hS _ _) hE]
  exact (Finset.mul_sum _ _ _).symm

theorem selectedPair_strata_cylinder (p : Parameters) (t : Fin p.T)
    (S : (q : Fin (M p)) → (c : Channel p) → Set (Remainder p q t c))
    (E : Set (Pair p)) (hS : ∀ q c, MeasurableSet (S q c)) (hE : MeasurableSet E) :
    sourceInputLaw p (⋃ a : Fin (M p) × Channel p,
      {source | source ∈ stratumEvent p a.1 t a.2 (S a.1 a.2) ∧
        ((source.1.2 a.1).2 t).2 a.2 ∈ E}) =
      (AffineChannelLaw.jointLaw (B p)).toMeasure E *
        sourceInputLaw p (⋃ a : Fin (M p) × Channel p,
          stratumEvent p a.1 t a.2 (S a.1 a.2)) := by
  rw [selectedPair_cylinder_sum p t S E hS hE,
    measure_iUnion (stratumEvent_disjoint p t S)
      (fun a => measurableSet_stratumEvent p a.1 t a.2 (S a.1 a.2) (hS a.1 a.2)),
    tsum_fintype]

/-- The union is a cylinder for the actual optional selected pair. The event
on the right contains only DOWN/UP selections; DATA contributes no sample. -/
theorem selectedPair_cylinder (p : Parameters) (t : Fin p.T)
    (S : (q : Fin (M p)) → (c : Channel p) → Set (Remainder p q t c))
    (E : Set (Pair p)) (hS : ∀ q c, MeasurableSet (S q c)) (hE : MeasurableSet E) :
    sourceInputLaw p {source |
      (∃ q c, source ∈ stratumEvent p q t c (S q c)) ∧
        ∃ a ∈ E, selectedPair p t source = some a} =
      (AffineChannelLaw.jointLaw (B p)).toMeasure E *
        sourceInputLaw p {source | ∃ q c, source ∈ stratumEvent p q t c (S q c)} := by
  have hbase : {source | ∃ q c, source ∈ stratumEvent p q t c (S q c)} =
      ⋃ a : Fin (M p) × Channel p, stratumEvent p a.1 t a.2 (S a.1 a.2) := by
    ext source
    simp only [Set.mem_ofPred, Set.mem_iUnion, Prod.exists]
  have hfull : {source |
      (∃ q c, source ∈ stratumEvent p q t c (S q c)) ∧
        ∃ a ∈ E, selectedPair p t source = some a} =
      ⋃ a : Fin (M p) × Channel p,
        {source | source ∈ stratumEvent p a.1 t a.2 (S a.1 a.2) ∧
          ((source.1.2 a.1).2 t).2 a.2 ∈ E} := by
    ext source
    simp only [Set.mem_ofPred, Set.mem_iUnion]
    constructor
    · rintro ⟨⟨q, c, hqc⟩, a, ha, heq⟩
      have hpair := selectedPair_of_selector p q t c source hqc.1
      have he : ((source.1.2 q).2 t).2 c = a := Option.some.inj (hpair.symm.trans heq)
      exact ⟨(q, c), hqc, he ▸ ha⟩
    · rintro ⟨⟨q, c⟩, hqc, ha⟩
      exact ⟨⟨q, c, hqc⟩, _, ha, selectedPair_of_selector p q t c source hqc.1⟩
  rw [hfull, hbase]
  exact selectedPair_strata_cylinder p t S E hS hE

/-- A fibre of the original coordinator scalar's categorical row draw. -/
def remainderRowFibre (p : Parameters) (q : Fin (M p)) (t : Fin p.T) (c : Channel p)
    (j : Fin (M p)) : Set (Remainder p q t c) :=
  {r | PrivateSourceStreams.coordinatorIndex p r.2.1.2 = j}

theorem measurableSet_remainderRowFibre (p : Parameters) (q : Fin (M p)) (t : Fin p.T)
    (c : Channel p) (j : Fin (M p)) : MeasurableSet (remainderRowFibre p q t c j) :=
  ((PrivateSourceStreams.measurable_coordinatorIndex p).comp
    (measurable_snd.comp (measurable_fst.comp measurable_snd))) (measurableSet_singleton j)

/-- The actual selected-pair law on every original `J=j` fibre. No division
by the fibre probability, and no positivity assumption, is used. -/
theorem selectedPair_cylinder_row_fibre (p : Parameters) (t : Fin p.T) (j : Fin (M p))
    (S : (q : Fin (M p)) → (c : Channel p) → Set (Remainder p q t c))
    (E : Set (Pair p)) (hS : ∀ q c, MeasurableSet (S q c)) (hE : MeasurableSet E) :
    sourceInputLaw p {source |
      (PrivateSourceStreams.coordinatorIndex p source.2.1.2 = j ∧
        ∃ q c, source ∈ stratumEvent p q t c (S q c)) ∧
        ∃ a ∈ E, selectedPair p t source = some a} =
      (AffineChannelLaw.jointLaw (B p)).toMeasure E *
        sourceInputLaw p {source |
          PrivateSourceStreams.coordinatorIndex p source.2.1.2 = j ∧
            ∃ q c, source ∈ stratumEvent p q t c (S q c)} := by
  let S' := fun q c => S q c ∩ remainderRowFibre p q t c j
  have hS' : ∀ q c, MeasurableSet (S' q c) :=
    fun q c => (hS q c).inter (measurableSet_remainderRowFibre p q t c j)
  have hiff (source : SourceInput p) :
      (∃ q c, source ∈ stratumEvent p q t c (S' q c)) ↔
        PrivateSourceStreams.coordinatorIndex p source.2.1.2 = j ∧
          ∃ q c, source ∈ stratumEvent p q t c (S q c) := by
    constructor
    · rintro ⟨q, c, hsel, hs, hj⟩
      exact ⟨hj, q, c, hsel, hs⟩
    · rintro ⟨hj, q, c, hsel, hs⟩
      exact ⟨q, c, hsel, hs, hj⟩
  simpa only [hiff] using selectedPair_cylinder p t S' E hS' hE

end Bandits.Support.ReferenceSelectedAffinePairLaw
