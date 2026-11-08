/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedInheritedDownPostlaunchOccurrence
public import Bandits.Support.ReferenceGeneratedPrelaunchDownOccurrenceRecurrence

import Mathlib.MeasureTheory.Measure.Basic
import Lean.Elab.Tactic.Omega

/-!
# Localized original-source inherited postlaunch DOWN detector mass

For a measurable cell of the strict past at `a ≤ alpha`, this module restricts
the actual postlaunch occurrence strata back to that same past view and sums
their source masses. The inherited old tests, actual launch source, current
physical test, selected row, and original affine sample stay on the existing
source carrier.

Sources: `sources/zip4/manuscript/appendix_a_local_protocol.tex:111-138`,
`sources/zip4/manuscript/appendix_b_communication.tex:724-736`,
`sources/zip4/manuscript/07_public_setup.tex:127-164`, and
`sources/zip4/manuscript/05_binary_transport.tex:20-42`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Function
open scoped Classical ENNReal
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.ContinuousLearningRows
open Bandits.Support.AffineChannelLaw
open Bandits.Support.GeneratedBootstrapRoundLaw
open Bandits.Support.ReferenceGeneratedInheritedDownPostlaunchOccurrence
open Bandits.Support.ReferenceGeneratedInheritedDownSourceHalf
open Bandits.Support.ReferenceGeneratedPrelaunchDownCurrentPair
open Bandits.Support.ReferenceGeneratedPrelaunchDownOccurrenceRecurrence
open Bandits.Support.ReferenceGeneratedPrelaunchDownOccurrenceTail

namespace Bandits.Support.ReferenceGeneratedInheritedDownPostlaunchDetectorMass

abbrev Parameters := ConstructorDimensions.Parameters
abbrev SourceInput := BootstrapPrivateRoundStreams.SourceInput
abbrev Candidate (p : Parameters) :=
  AffineChannelLaw.Word (AffineBatchDecoder.width p)

variable {p : Parameters}

/-- The exact original-source cell at the earlier strict-past cutoff. -/
def inheritedDownPostlaunchPastCell
    (a : Fin p.T)
    (Cell : Set (CompletePublicTable.IDArray p × GeneratedBootstrapRoundLaw.Past p a)) :
    Set (SourceInput p) :=
  {z | ReferenceGeneratedPrelaunchDownCurrentPair.sourcePastView a z ∈ Cell}

/-- Pull an earlier cell back along O's actual restriction of the original
strict past at a postlaunch round. The original IDs, base arrays and `J`,
whole targets, and retained continuous coordinates are those of O's map. -/
def inheritedDownPostlaunchCellAtRound
    (alpha : ℕ) (a : Fin p.T) (ha : a.val ≤ alpha)
    (Cell : Set (CompletePublicTable.IDArray p × GeneratedBootstrapRoundLaw.Past p a))
    (δ : ReferenceGeneratedInheritedDownPostlaunchOccurrence.Lambda p alpha) :
    Set (CompletePublicTable.IDArray p × GeneratedBootstrapRoundLaw.Past p δ.1.2.2) :=
  (ReferenceGeneratedPrelaunchDownOccurrenceTail.prelaunchPastRestriction a δ.1.2.2
    (ha.trans (δ.2.1.trans δ.2.2))) ⁻¹' Cell

/-- The pulled-back earlier cell is measurable under the same actual past
restriction used by the localized source events. -/
theorem measurableSet_inheritedDownPostlaunchCellAtRound
    (alpha : ℕ) (a : Fin p.T) (ha : a.val ≤ alpha)
    (Cell : Set (CompletePublicTable.IDArray p × GeneratedBootstrapRoundLaw.Past p a))
    (hCell : MeasurableSet Cell)
    (δ : ReferenceGeneratedInheritedDownPostlaunchOccurrence.Lambda p alpha) :
    MeasurableSet (inheritedDownPostlaunchCellAtRound alpha a ha Cell δ) := by
  let har := ha.trans (δ.2.1.trans δ.2.2)
  change MeasurableSet
    ((ReferenceGeneratedPrelaunchDownOccurrenceTail.prelaunchPastRestriction a δ.1.2.2 har) ⁻¹' Cell)
  exact hCell.preimage
    (ReferenceGeneratedPrelaunchDownOccurrenceTail.measurable_prelaunchPastRestriction
      a δ.1.2.2 har)

/-- The inherited source event localized to the same earlier past cell, using
the existing physical half-law event at round `r` with O's pulled-back cell. -/
def inheritedDownPostlaunchLocalizedSourceEvent
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (alpha k q : ℕ)
    (hAlpha : alpha ≤ p.T) (w : Candidate p) (hq : 1 ≤ q)
    (hqQ : q ≤ AffineBatchDecoder.quota p)
    (control0 : ContinuousLearningRows.TimeControl p)
    (a : Fin p.T) (ha : a.val ≤ alpha)
    (Cell : Set (CompletePublicTable.IDArray p × GeneratedBootstrapRoundLaw.Past p a))
    (hCell : MeasurableSet Cell)
    (δ : ReferenceGeneratedInheritedDownPostlaunchOccurrence.Lambda p alpha) :
    Set (SourceInput p) :=
  let CellAtR := inheritedDownPostlaunchCellAtRound alpha a ha Cell δ
  let hCellAtR : MeasurableSet CellAtR :=
    measurableSet_inheritedDownPostlaunchCellAtRound alpha a ha Cell hCell δ
  ReferenceGeneratedInheritedDownSourceHalf.inheritedDownSourceEvent
    (rate := rate) rewards C_star C_h alpha k q hAlpha w hq hqQ
    δ.1.1 δ.1.2.2 δ.1.2.1.val δ.2.2 control0 CellAtR hCellAtR i

/-- The hashed inherited source event localized to the same earlier past
cell. Its hash remains the original selected-row pair at the physical round. -/
def inheritedDownPostlaunchLocalizedHashedSourceEvent
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (alpha k q : ℕ)
    (hAlpha : alpha ≤ p.T) (w : Candidate p) (hq : 1 ≤ q)
    (hqQ : q ≤ AffineBatchDecoder.quota p)
    (control0 : ContinuousLearningRows.TimeControl p)
    (a : Fin p.T) (ha : a.val ≤ alpha)
    (Cell : Set (CompletePublicTable.IDArray p × GeneratedBootstrapRoundLaw.Past p a))
    (hCell : MeasurableSet Cell)
    (δ : ReferenceGeneratedInheritedDownPostlaunchOccurrence.Lambda p alpha) :
    Set (SourceInput p) :=
  let CellAtR := inheritedDownPostlaunchCellAtRound alpha a ha Cell δ
  let hCellAtR : MeasurableSet CellAtR :=
    measurableSet_inheritedDownPostlaunchCellAtRound alpha a ha Cell hCell δ
  ReferenceGeneratedInheritedDownSourceHalf.inheritedDownHashOneSourceEvent
    (rate := rate) rewards C_star C_h alpha k q hAlpha w hq hqQ
    δ.1.1 δ.1.2.2 δ.1.2.1.val δ.2.2 control0 CellAtR hCellAtR i

/-- The unhashed occurrence union inside one fixed selected-row and launch
stratum, with only physical rounds `s ≤ r` included. -/
def inheritedDownPostlaunchFixedStratumOccurrenceUnion
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (alpha k q : ℕ)
    (hAlpha : alpha ≤ p.T) (w : Candidate p) (hq : 1 ≤ q)
    (hqQ : q ≤ AffineBatchDecoder.quota p)
    (control0 : ContinuousLearningRows.TimeControl p)
    (j : Fin (M p)) (s : Fin p.T) (hAlphaS : alpha ≤ s.val) :
    Set (SourceInput p) :=
  ⋃ r : {r : Fin p.T // s.val ≤ r.val},
    ReferenceGeneratedInheritedDownPostlaunchOccurrence.inheritedDownPostlaunchOccurrence
      (rate := rate) rewards C_star C_h i alpha k q hAlpha w hq hqQ control0
      ⟨(j, s, r.1), ⟨hAlphaS, r.2⟩⟩

/-- The hashed detector union inside one fixed selected-row and launch
stratum, with only physical rounds `s ≤ r` included. -/
def inheritedDownPostlaunchFixedStratumDetector
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (alpha k q : ℕ)
    (hAlpha : alpha ≤ p.T) (w : Candidate p) (hq : 1 ≤ q)
    (hqQ : q ≤ AffineBatchDecoder.quota p)
    (control0 : ContinuousLearningRows.TimeControl p)
    (j : Fin (M p)) (s : Fin p.T) (hAlphaS : alpha ≤ s.val) :
    Set (SourceInput p) :=
  ⋃ r : {r : Fin p.T // s.val ≤ r.val},
    ReferenceGeneratedInheritedDownPostlaunchOccurrence.inheritedDownPostlaunchHashedOccurrence
      (rate := rate) rewards C_star C_h i alpha k q hAlpha w hq hqQ control0
      ⟨(j, s, r.1), ⟨hAlphaS, r.2⟩⟩

/-- Identifies the localized inherited source event with the earlier past
cell intersected with the public actual postlaunch occurrence. -/
theorem inheritedDownPostlaunchLocalizedSourceEvent_eq_pastCell_inter_occurrence
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (alpha k q : ℕ)
    (hAlpha : alpha ≤ p.T) (w : Candidate p) (hq : 1 ≤ q)
    (hqQ : q ≤ AffineBatchDecoder.quota p)
    (control0 : ContinuousLearningRows.TimeControl p)
    (a : Fin p.T) (ha : a.val ≤ alpha)
    (Cell : Set (CompletePublicTable.IDArray p × GeneratedBootstrapRoundLaw.Past p a))
    (hCell : MeasurableSet Cell)
    (δ : ReferenceGeneratedInheritedDownPostlaunchOccurrence.Lambda p alpha) :
    inheritedDownPostlaunchLocalizedSourceEvent rate rewards C_star C_h i alpha k q
      hAlpha w hq hqQ control0 a ha Cell hCell δ =
    {z | z ∈ inheritedDownPostlaunchPastCell a Cell ∧
      z ∈ ReferenceGeneratedInheritedDownPostlaunchOccurrence.inheritedDownPostlaunchOccurrence
        (rate := rate) rewards C_star C_h i alpha k q hAlpha w hq hqQ control0 δ} := by
  let har := ha.trans (δ.2.1.trans δ.2.2)
  let CellAtR := inheritedDownPostlaunchCellAtRound alpha a ha Cell δ
  have hCellAtR : MeasurableSet CellAtR :=
    measurableSet_inheritedDownPostlaunchCellAtRound alpha a ha Cell hCell δ
  have hview (z : SourceInput p) :
      ReferenceGeneratedPrelaunchDownCurrentPair.sourcePastView δ.1.2.2 z ∈ CellAtR ↔
        ReferenceGeneratedPrelaunchDownCurrentPair.sourcePastView a z ∈ Cell := by
    change ReferenceGeneratedPrelaunchDownOccurrenceTail.prelaunchPastRestriction a δ.1.2.2 har
        (ReferenceGeneratedPrelaunchDownCurrentPair.sourcePastView δ.1.2.2 z) ∈ Cell ↔ _
    rw [ReferenceGeneratedPrelaunchDownOccurrenceTail.prelaunchPastRestriction_sourcePastView
      a δ.1.2.2 har z]
  have hP :=
    ReferenceGeneratedInheritedDownPostlaunchOccurrence.inheritedDownPostlaunchOccurrence_eq_sourceEvent
      (rate := rate) rewards C_star C_h i alpha k q hAlpha w hq hqQ control0 δ
  have hCellRestrict :
      ReferenceGeneratedInheritedDownSourceHalf.inheritedDownSourceEvent
          (rate := rate) rewards C_star C_h alpha k q hAlpha w hq hqQ
          δ.1.1 δ.1.2.2 δ.1.2.1.val δ.2.2 control0 CellAtR hCellAtR i =
        {z | z ∈ inheritedDownPostlaunchPastCell a Cell ∧
          z ∈ ReferenceGeneratedInheritedDownSourceHalf.inheritedDownSourceEvent
            (rate := rate) rewards C_star C_h alpha k q hAlpha w hq hqQ
            δ.1.1 δ.1.2.2 δ.1.2.1.val δ.2.2 control0 Set.univ MeasurableSet.univ i} := by
    ext z
    simp only [ReferenceGeneratedInheritedDownSourceHalf.inheritedDownSourceEvent,
      inheritedDownPostlaunchPastCell, Set.mem_ofPred_eq, Set.mem_univ, true_and]
    rw [hview z]
    constructor
    · rintro ⟨hsel, hpast, hrest⟩
      exact ⟨hpast, hsel, hrest⟩
    · rintro ⟨hpast, hsel, hrest⟩
      exact ⟨hsel, hpast, hrest⟩
  calc
    inheritedDownPostlaunchLocalizedSourceEvent rate rewards C_star C_h i alpha k q
        hAlpha w hq hqQ control0 a ha Cell hCell δ = _ := hCellRestrict
    _ = {z | z ∈ inheritedDownPostlaunchPastCell a Cell ∧
          z ∈ ReferenceGeneratedInheritedDownPostlaunchOccurrence.inheritedDownPostlaunchOccurrence
            (rate := rate) rewards C_star C_h i alpha k q hAlpha w hq hqQ control0 δ} := by
      exact congrArg (fun E : Set (SourceInput p) =>
        {z | z ∈ inheritedDownPostlaunchPastCell a Cell ∧ z ∈ E}) hP.symm

/-- Identifies the localized hashed source event with the earlier past cell
intersected with the public actual hashed postlaunch occurrence. -/
theorem inheritedDownPostlaunchLocalizedHashedSourceEvent_eq_pastCell_inter_hashedOccurrence
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (alpha k q : ℕ)
    (hAlpha : alpha ≤ p.T) (w : Candidate p) (hq : 1 ≤ q)
    (hqQ : q ≤ AffineBatchDecoder.quota p)
    (control0 : ContinuousLearningRows.TimeControl p)
    (a : Fin p.T) (ha : a.val ≤ alpha)
    (Cell : Set (CompletePublicTable.IDArray p × GeneratedBootstrapRoundLaw.Past p a))
    (hCell : MeasurableSet Cell)
    (δ : ReferenceGeneratedInheritedDownPostlaunchOccurrence.Lambda p alpha) :
    inheritedDownPostlaunchLocalizedHashedSourceEvent rate rewards C_star C_h i alpha k q
      hAlpha w hq hqQ control0 a ha Cell hCell δ =
    {z | z ∈ inheritedDownPostlaunchPastCell a Cell ∧
      z ∈ ReferenceGeneratedInheritedDownPostlaunchOccurrence.inheritedDownPostlaunchHashedOccurrence
        (rate := rate) rewards C_star C_h i alpha k q hAlpha w hq hqQ control0 δ} := by
  let har := ha.trans (δ.2.1.trans δ.2.2)
  let CellAtR := inheritedDownPostlaunchCellAtRound alpha a ha Cell δ
  have hCellAtR : MeasurableSet CellAtR :=
    measurableSet_inheritedDownPostlaunchCellAtRound alpha a ha Cell hCell δ
  have hview (z : SourceInput p) :
      ReferenceGeneratedPrelaunchDownCurrentPair.sourcePastView δ.1.2.2 z ∈ CellAtR ↔
        ReferenceGeneratedPrelaunchDownCurrentPair.sourcePastView a z ∈ Cell := by
    change ReferenceGeneratedPrelaunchDownOccurrenceTail.prelaunchPastRestriction a δ.1.2.2 har
        (ReferenceGeneratedPrelaunchDownCurrentPair.sourcePastView δ.1.2.2 z) ∈ Cell ↔ _
    rw [ReferenceGeneratedPrelaunchDownOccurrenceTail.prelaunchPastRestriction_sourcePastView
      a δ.1.2.2 har z]
  have hP :=
    ReferenceGeneratedInheritedDownPostlaunchOccurrence.inheritedDownPostlaunchHashedOccurrence_eq_hashOneSourceEvent
      (rate := rate) rewards C_star C_h i alpha k q hAlpha w hq hqQ control0 δ
  have hSource := inheritedDownPostlaunchLocalizedSourceEvent_eq_pastCell_inter_occurrence rate rewards C_star C_h i
    alpha k q hAlpha w hq hqQ control0 a ha Cell hCell δ
  have hPSource :=
    ReferenceGeneratedInheritedDownPostlaunchOccurrence.inheritedDownPostlaunchOccurrence_eq_sourceEvent
      (rate := rate) rewards C_star C_h i alpha k q hAlpha w hq hqQ control0 δ
  have hSourceRestrict :
      ReferenceGeneratedInheritedDownSourceHalf.inheritedDownSourceEvent
          (rate := rate) rewards C_star C_h alpha k q hAlpha w hq hqQ
          δ.1.1 δ.1.2.2 δ.1.2.1.val δ.2.2 control0 CellAtR hCellAtR i =
        {z | z ∈ inheritedDownPostlaunchPastCell a Cell ∧
          z ∈ ReferenceGeneratedInheritedDownSourceHalf.inheritedDownSourceEvent
            (rate := rate) rewards C_star C_h alpha k q hAlpha w hq hqQ
            δ.1.1 δ.1.2.2 δ.1.2.1.val δ.2.2 control0 Set.univ MeasurableSet.univ i} := by
    calc
      _ = {z | z ∈ inheritedDownPostlaunchPastCell a Cell ∧
          z ∈ ReferenceGeneratedInheritedDownPostlaunchOccurrence.inheritedDownPostlaunchOccurrence
            (rate := rate) rewards C_star C_h i alpha k q hAlpha w hq hqQ control0 δ} := hSource
      _ = _ := congrArg (fun E : Set (SourceInput p) =>
        {z | z ∈ inheritedDownPostlaunchPastCell a Cell ∧ z ∈ E}) hPSource
  have hHashRestrict :
      ReferenceGeneratedInheritedDownSourceHalf.inheritedDownHashOneSourceEvent
          (rate := rate) rewards C_star C_h alpha k q hAlpha w hq hqQ
          δ.1.1 δ.1.2.2 δ.1.2.1.val δ.2.2 control0 CellAtR hCellAtR i =
        {z | z ∈ inheritedDownPostlaunchPastCell a Cell ∧
          z ∈ ReferenceGeneratedInheritedDownSourceHalf.inheritedDownHashOneSourceEvent
            (rate := rate) rewards C_star C_h alpha k q hAlpha w hq hqQ
            δ.1.1 δ.1.2.2 δ.1.2.1.val δ.2.2 control0 Set.univ MeasurableSet.univ i} := by
    ext z
    change (z ∈ ReferenceGeneratedInheritedDownSourceHalf.inheritedDownSourceEvent
          (rate := rate) rewards C_star C_h alpha k q hAlpha w hq hqQ
          δ.1.1 δ.1.2.2 δ.1.2.1.val δ.2.2 control0 CellAtR hCellAtR i ∧
        AffineChannelLaw.affineHash (((z.1.2 δ.1.1).2 δ.1.2.2).2 (0, i)) w = 1) ↔
      (ReferenceGeneratedPrelaunchDownCurrentPair.sourcePastView a z ∈ Cell ∧
       z ∈ ReferenceGeneratedInheritedDownSourceHalf.inheritedDownSourceEvent
          (rate := rate) rewards C_star C_h alpha k q hAlpha w hq hqQ
          δ.1.1 δ.1.2.2 δ.1.2.1.val δ.2.2 control0 Set.univ MeasurableSet.univ i ∧
       AffineChannelLaw.affineHash (((z.1.2 δ.1.1).2 δ.1.2.2).2 (0, i)) w = 1)
    rw [hSourceRestrict]
    simp only [inheritedDownPostlaunchPastCell, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨⟨hcell, hsource⟩, hhash⟩
      exact ⟨hcell, hsource, hhash⟩
    · rintro ⟨hcell, hsource, hhash⟩
      exact ⟨⟨hcell, hsource⟩, hhash⟩
  calc
    inheritedDownPostlaunchLocalizedHashedSourceEvent rate rewards C_star C_h i alpha k q
        hAlpha w hq hqQ control0 a ha Cell hCell δ =
        {z | z ∈ inheritedDownPostlaunchPastCell a Cell ∧
          z ∈ ReferenceGeneratedInheritedDownSourceHalf.inheritedDownHashOneSourceEvent
            (rate := rate) rewards C_star C_h alpha k q hAlpha w hq hqQ
            δ.1.1 δ.1.2.2 δ.1.2.1.val δ.2.2 control0 Set.univ MeasurableSet.univ i} := hHashRestrict
    _ = {z | z ∈ inheritedDownPostlaunchPastCell a Cell ∧
          z ∈ ReferenceGeneratedInheritedDownPostlaunchOccurrence.inheritedDownPostlaunchHashedOccurrence
            (rate := rate) rewards C_star C_h i alpha k q hAlpha w hq hqQ control0 δ} := by
      exact congrArg (fun E : Set (SourceInput p) =>
        {z | z ∈ inheritedDownPostlaunchPastCell a Cell ∧ z ∈ E}) hP.symm

/-- Measurability of the localized source event follows from H's event API
after pulling back the same measurable earlier cell. -/
theorem measurableSet_inheritedDownPostlaunchLocalizedSourceEvent
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (alpha k q : ℕ)
    (hAlpha : alpha ≤ p.T) (w : Candidate p) (hq : 1 ≤ q)
    (hqQ : q ≤ AffineBatchDecoder.quota p)
    (control0 : ContinuousLearningRows.TimeControl p)
    (a : Fin p.T) (ha : a.val ≤ alpha)
    (Cell : Set (CompletePublicTable.IDArray p × GeneratedBootstrapRoundLaw.Past p a))
    (hCell : MeasurableSet Cell)
    (δ : ReferenceGeneratedInheritedDownPostlaunchOccurrence.Lambda p alpha) :
    MeasurableSet (inheritedDownPostlaunchLocalizedSourceEvent rate rewards C_star C_h i
      alpha k q hAlpha w hq hqQ control0 a ha Cell hCell δ) := by
  let har := ha.trans (δ.2.1.trans δ.2.2)
  let CellAtR := inheritedDownPostlaunchCellAtRound alpha a ha Cell δ
  have hCellAtR : MeasurableSet CellAtR :=
    measurableSet_inheritedDownPostlaunchCellAtRound alpha a ha Cell hCell δ
  change MeasurableSet
    (ReferenceGeneratedInheritedDownSourceHalf.inheritedDownSourceEvent
      (rate := rate) rewards C_star C_h alpha k q hAlpha w hq hqQ
      δ.1.1 δ.1.2.2 δ.1.2.1.val δ.2.2 control0 CellAtR hCellAtR i)
  exact ReferenceGeneratedInheritedDownSourceHalf.measurableSet_inheritedDownSourceEvent
    (rate := rate) rewards C_star C_h alpha k q hAlpha w hq hqQ
    δ.1.1 δ.1.2.2 δ.1.2.1.val δ.2.2 control0 CellAtR hCellAtR i

/-- Measurability of the localized hashed source event follows from H's
hashed-event API on the pulled-back earlier cell. -/
theorem measurableSet_inheritedDownPostlaunchLocalizedHashedSourceEvent
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (alpha k q : ℕ)
    (hAlpha : alpha ≤ p.T) (w : Candidate p) (hq : 1 ≤ q)
    (hqQ : q ≤ AffineBatchDecoder.quota p)
    (control0 : ContinuousLearningRows.TimeControl p)
    (a : Fin p.T) (ha : a.val ≤ alpha)
    (Cell : Set (CompletePublicTable.IDArray p × GeneratedBootstrapRoundLaw.Past p a))
    (hCell : MeasurableSet Cell)
    (δ : ReferenceGeneratedInheritedDownPostlaunchOccurrence.Lambda p alpha) :
    MeasurableSet (inheritedDownPostlaunchLocalizedHashedSourceEvent rate rewards C_star C_h i
      alpha k q hAlpha w hq hqQ control0 a ha Cell hCell δ) := by
  let har := ha.trans (δ.2.1.trans δ.2.2)
  let CellAtR := inheritedDownPostlaunchCellAtRound alpha a ha Cell δ
  have hCellAtR : MeasurableSet CellAtR :=
    measurableSet_inheritedDownPostlaunchCellAtRound alpha a ha Cell hCell δ
  change MeasurableSet
    (ReferenceGeneratedInheritedDownSourceHalf.inheritedDownHashOneSourceEvent
      (rate := rate) rewards C_star C_h alpha k q hAlpha w hq hqQ
      δ.1.1 δ.1.2.2 δ.1.2.1.val δ.2.2 control0 CellAtR hCellAtR i)
  exact ReferenceGeneratedInheritedDownSourceHalf.measurableSet_inheritedDownHashOneSourceEvent
    (rate := rate) rewards C_star C_h alpha k q hAlpha w hq hqQ
    δ.1.1 δ.1.2.2 δ.1.2.1.val δ.2.2 control0 CellAtR hCellAtR i

private theorem inheritedDownPostlaunch_localizedSourceEvent_hash_half
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (alpha k q : ℕ)
    (hAlpha : alpha ≤ p.T) (w : Candidate p) (hq : 1 ≤ q)
    (hqQ : q ≤ AffineBatchDecoder.quota p)
    (control0 : ContinuousLearningRows.TimeControl p)
    (a : Fin p.T) (ha : a.val ≤ alpha)
    (Cell : Set (CompletePublicTable.IDArray p × GeneratedBootstrapRoundLaw.Past p a))
    (hCell : MeasurableSet Cell)
    (δ : ReferenceGeneratedInheritedDownPostlaunchOccurrence.Lambda p alpha) :
    BootstrapPrivateRoundStreams.sourceInputLaw p
      (inheritedDownPostlaunchLocalizedHashedSourceEvent rate rewards C_star C_h i alpha k q
        hAlpha w hq hqQ control0 a ha Cell hCell δ) =
    ((1 : ENNReal) / 2) * BootstrapPrivateRoundStreams.sourceInputLaw p
      (inheritedDownPostlaunchLocalizedSourceEvent rate rewards C_star C_h i alpha k q
        hAlpha w hq hqQ control0 a ha Cell hCell δ) := by
  let har := ha.trans (δ.2.1.trans δ.2.2)
  let CellAtR := inheritedDownPostlaunchCellAtRound alpha a ha Cell δ
  have hCellAtR : MeasurableSet CellAtR :=
    measurableSet_inheritedDownPostlaunchCellAtRound alpha a ha Cell hCell δ
  change BootstrapPrivateRoundStreams.sourceInputLaw p
      (ReferenceGeneratedInheritedDownSourceHalf.inheritedDownHashOneSourceEvent
        (rate := rate) rewards C_star C_h alpha k q hAlpha w hq hqQ
        δ.1.1 δ.1.2.2 δ.1.2.1.val δ.2.2 control0 CellAtR hCellAtR i) =
    ((1 : ENNReal) / 2) * BootstrapPrivateRoundStreams.sourceInputLaw p
      (ReferenceGeneratedInheritedDownSourceHalf.inheritedDownSourceEvent
        (rate := rate) rewards C_star C_h alpha k q hAlpha w hq hqQ
        δ.1.1 δ.1.2.2 δ.1.2.1.val δ.2.2 control0 CellAtR hCellAtR i)
  exact ReferenceGeneratedInheritedDownSourceHalf.inheritedDownSourceEvent_hash_half
    (rate := rate) rewards C_star C_h alpha k q hAlpha w hq hqQ
    δ.1.1 δ.1.2.2 δ.1.2.1.val δ.2.2 control0 CellAtR hCellAtR i

/-- On a fixed stratum, different physical rounds are disjoint because the
public uniqueness theorem applies to the larger unhashed occurrences. -/
private theorem inheritedDownPostlaunch_fixedStratum_pairwiseDisjoint
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (alpha k q : ℕ)
    (hAlpha : alpha ≤ p.T) (w : Candidate p) (hq : 1 ≤ q)
    (hqQ : q ≤ AffineBatchDecoder.quota p)
    (control0 : ContinuousLearningRows.TimeControl p)
    (a : Fin p.T) (ha : a.val ≤ alpha)
    (Cell : Set (CompletePublicTable.IDArray p × GeneratedBootstrapRoundLaw.Past p a))
    (hCell : MeasurableSet Cell) (j : Fin (M p)) (s : Fin p.T)
    (hAlphaS : alpha ≤ s.val) :
    Pairwise (Disjoint on fun r : {r : Fin p.T // s.val ≤ r.val} =>
      inheritedDownPostlaunchLocalizedSourceEvent rate rewards C_star C_h i alpha k q
        hAlpha w hq hqQ control0 a ha Cell hCell ⟨(j, s, r.1), ⟨hAlphaS, r.2⟩⟩) := by
  intro r r' hne
  change Disjoint
    (inheritedDownPostlaunchLocalizedSourceEvent rate rewards C_star C_h i alpha k q hAlpha w hq hqQ
      control0 a ha Cell hCell ⟨(j, s, r.1), ⟨hAlphaS, r.2⟩⟩)
    (inheritedDownPostlaunchLocalizedSourceEvent rate rewards C_star C_h i alpha k q hAlpha w hq hqQ
      control0 a ha Cell hCell ⟨(j, s, r'.1), ⟨hAlphaS, r'.2⟩⟩)
  rw [Set.disjoint_left]
  intro z hz hz'
  have hzOcc :=
    inheritedDownPostlaunchLocalizedSourceEvent_eq_pastCell_inter_occurrence rate rewards C_star C_h i alpha k q
      hAlpha w hq hqQ control0 a ha Cell hCell ⟨(j, s, r.1), ⟨hAlphaS, r.2⟩⟩
  rw [hzOcc] at hz
  change z ∈ inheritedDownPostlaunchPastCell a Cell ∧
      z ∈ ReferenceGeneratedInheritedDownPostlaunchOccurrence.inheritedDownPostlaunchOccurrence
        (rate := rate) rewards C_star C_h i alpha k q hAlpha w hq hqQ control0
        ⟨(j, s, r.1), ⟨hAlphaS, r.2⟩⟩ at hz
  have hzOcc' :=
    inheritedDownPostlaunchLocalizedSourceEvent_eq_pastCell_inter_occurrence rate rewards C_star C_h i alpha k q
      hAlpha w hq hqQ control0 a ha Cell hCell ⟨(j, s, r'.1), ⟨hAlphaS, r'.2⟩⟩
  rw [hzOcc'] at hz'
  change z ∈ inheritedDownPostlaunchPastCell a Cell ∧
      z ∈ ReferenceGeneratedInheritedDownPostlaunchOccurrence.inheritedDownPostlaunchOccurrence
        (rate := rate) rewards C_star C_h i alpha k q hAlpha w hq hqQ control0
        ⟨(j, s, r'.1), ⟨hAlphaS, r'.2⟩⟩ at hz'
  have hdelta :=
    ReferenceGeneratedInheritedDownPostlaunchOccurrence.inheritedDownPostlaunchOccurrence_unique
      (rate := rate) rewards C_star C_h i alpha k q hAlpha w hq hqQ control0 z
      ⟨(j, s, r.1), ⟨hAlphaS, r.2⟩⟩ ⟨(j, s, r'.1), ⟨hAlphaS, r'.2⟩⟩ hz.2 hz'.2
  exact hne (by cases r; cases r'; cases hdelta; rfl)

/-- Exact source-mass decompositions of the localized inherited detector and
its unhashed occurrence union over the original `(j,s,r)` strata. -/
theorem inheritedDownPostlaunchDetector_source_sum
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (alpha k q : ℕ)
    (hAlpha : alpha ≤ p.T) (w : Candidate p) (hq : 1 ≤ q)
    (hqQ : q ≤ AffineBatchDecoder.quota p)
    (control0 : ContinuousLearningRows.TimeControl p)
    (a : Fin p.T) (ha : a.val ≤ alpha)
    (Cell : Set (CompletePublicTable.IDArray p × GeneratedBootstrapRoundLaw.Past p a))
    (hCell : MeasurableSet Cell) :
    let B := inheritedDownPostlaunchPastCell a Cell
    (BootstrapPrivateRoundStreams.sourceInputLaw p
        {z | z ∈ B ∧ z ∈
          ReferenceGeneratedInheritedDownPostlaunchOccurrence.inheritedDownPostlaunchDetector
            (rate := rate) rewards C_star C_h i alpha k q hAlpha w hq hqQ control0} =
      ∑ δ : ReferenceGeneratedInheritedDownPostlaunchOccurrence.Lambda p alpha,
        BootstrapPrivateRoundStreams.sourceInputLaw p
          (inheritedDownPostlaunchLocalizedHashedSourceEvent rate rewards C_star C_h i alpha k q
            hAlpha w hq hqQ control0 a ha Cell hCell δ)) ∧
    (BootstrapPrivateRoundStreams.sourceInputLaw p
        {z | z ∈ B ∧ z ∈
          ReferenceGeneratedInheritedDownPostlaunchOccurrence.inheritedDownPostlaunchOccurrenceUnion
            (rate := rate) rewards C_star C_h i alpha k q hAlpha w hq hqQ control0} =
      ∑ δ : ReferenceGeneratedInheritedDownPostlaunchOccurrence.Lambda p alpha,
        BootstrapPrivateRoundStreams.sourceInputLaw p
          (inheritedDownPostlaunchLocalizedSourceEvent rate rewards C_star C_h i alpha k q
            hAlpha w hq hqQ control0 a ha Cell hCell δ)) := by
  classical
  dsimp
  let B := inheritedDownPostlaunchPastCell a Cell
  let Hset : ReferenceGeneratedInheritedDownPostlaunchOccurrence.Lambda p alpha → Set (SourceInput p) :=
    fun δ => inheritedDownPostlaunchLocalizedHashedSourceEvent rate rewards C_star C_h i alpha k q
      hAlpha w hq hqQ control0 a ha Cell hCell δ
  let Sset : ReferenceGeneratedInheritedDownPostlaunchOccurrence.Lambda p alpha → Set (SourceInput p) :=
    fun δ => inheritedDownPostlaunchLocalizedSourceEvent rate rewards C_star C_h i alpha k q
      hAlpha w hq hqQ control0 a ha Cell hCell δ
  have hHunion : {z | z ∈ B ∧ z ∈
      ReferenceGeneratedInheritedDownPostlaunchOccurrence.inheritedDownPostlaunchDetector
        (rate := rate) rewards C_star C_h i alpha k q hAlpha w hq hqQ control0} =
      ⋃ δ, Hset δ := by
    ext z
    constructor
    · rintro ⟨hBz, hdet⟩
      change z ∈ ⋃ δ, ReferenceGeneratedInheritedDownPostlaunchOccurrence.inheritedDownPostlaunchHashedOccurrence
        (rate := rate) rewards C_star C_h i alpha k q hAlpha w hq hqQ control0 δ at hdet
      rcases Set.mem_iUnion.mp hdet with ⟨δ, hδ⟩
      have hlocal : z ∈ Hset δ := by
        change z ∈ inheritedDownPostlaunchLocalizedHashedSourceEvent rate rewards C_star C_h i
          alpha k q hAlpha w hq hqQ control0 a ha Cell hCell δ
        rw [inheritedDownPostlaunchLocalizedHashedSourceEvent_eq_pastCell_inter_hashedOccurrence rate rewards C_star C_h i
          alpha k q hAlpha w hq hqQ control0 a ha Cell hCell δ]
        exact ⟨hBz, hδ⟩
      exact Set.mem_iUnion.mpr ⟨δ, hlocal⟩
    · intro hz
      rcases Set.mem_iUnion.mp hz with ⟨δ, hδ⟩
      change z ∈ inheritedDownPostlaunchLocalizedHashedSourceEvent rate rewards C_star C_h i
        alpha k q hAlpha w hq hqQ control0 a ha Cell hCell δ at hδ
      rw [inheritedDownPostlaunchLocalizedHashedSourceEvent_eq_pastCell_inter_hashedOccurrence rate rewards C_star C_h i
        alpha k q hAlpha w hq hqQ control0 a ha Cell hCell δ] at hδ
      change z ∈ inheritedDownPostlaunchPastCell a Cell ∧
        z ∈ ReferenceGeneratedInheritedDownPostlaunchOccurrence.inheritedDownPostlaunchHashedOccurrence
          (rate := rate) rewards C_star C_h i alpha k q hAlpha w hq hqQ control0 δ at hδ
      exact ⟨hδ.1, Set.mem_iUnion.mpr ⟨δ, hδ.2⟩⟩
  have hSunion : {z | z ∈ B ∧ z ∈
      ReferenceGeneratedInheritedDownPostlaunchOccurrence.inheritedDownPostlaunchOccurrenceUnion
        (rate := rate) rewards C_star C_h i alpha k q hAlpha w hq hqQ control0} =
      ⋃ δ, Sset δ := by
    ext z
    constructor
    · rintro ⟨hBz, hocc⟩
      change z ∈ ⋃ δ, ReferenceGeneratedInheritedDownPostlaunchOccurrence.inheritedDownPostlaunchOccurrence
        (rate := rate) rewards C_star C_h i alpha k q hAlpha w hq hqQ control0 δ at hocc
      rcases Set.mem_iUnion.mp hocc with ⟨δ, hδ⟩
      have hlocal : z ∈ Sset δ := by
        change z ∈ inheritedDownPostlaunchLocalizedSourceEvent rate rewards C_star C_h i alpha k q
          hAlpha w hq hqQ control0 a ha Cell hCell δ
        rw [inheritedDownPostlaunchLocalizedSourceEvent_eq_pastCell_inter_occurrence rate rewards C_star C_h i
          alpha k q hAlpha w hq hqQ control0 a ha Cell hCell δ]
        exact ⟨hBz, hδ⟩
      exact Set.mem_iUnion.mpr ⟨δ, hlocal⟩
    · intro hz
      rcases Set.mem_iUnion.mp hz with ⟨δ, hδ⟩
      change z ∈ inheritedDownPostlaunchLocalizedSourceEvent rate rewards C_star C_h i alpha k q
        hAlpha w hq hqQ control0 a ha Cell hCell δ at hδ
      rw [inheritedDownPostlaunchLocalizedSourceEvent_eq_pastCell_inter_occurrence rate rewards C_star C_h i
        alpha k q hAlpha w hq hqQ control0 a ha Cell hCell δ] at hδ
      change z ∈ inheritedDownPostlaunchPastCell a Cell ∧
        z ∈ ReferenceGeneratedInheritedDownPostlaunchOccurrence.inheritedDownPostlaunchOccurrence
          (rate := rate) rewards C_star C_h i alpha k q hAlpha w hq hqQ control0 δ at hδ
      exact ⟨hδ.1, Set.mem_iUnion.mpr ⟨δ, hδ.2⟩⟩
  have hHpair : Pairwise (Disjoint on Hset) := by
    intro δ ε hne
    change Disjoint (Hset δ) (Hset ε)
    rw [Set.disjoint_left]
    intro z hz hz'
    change z ∈ inheritedDownPostlaunchLocalizedHashedSourceEvent rate rewards C_star C_h i alpha k q
      hAlpha w hq hqQ control0 a ha Cell hCell δ at hz
    change z ∈ inheritedDownPostlaunchLocalizedHashedSourceEvent rate rewards C_star C_h i alpha k q
      hAlpha w hq hqQ control0 a ha Cell hCell ε at hz'
    rw [inheritedDownPostlaunchLocalizedHashedSourceEvent_eq_pastCell_inter_hashedOccurrence rate rewards C_star C_h i alpha k q
      hAlpha w hq hqQ control0 a ha Cell hCell δ] at hz
    rw [inheritedDownPostlaunchLocalizedHashedSourceEvent_eq_pastCell_inter_hashedOccurrence rate rewards C_star C_h i alpha k q
      hAlpha w hq hqQ control0 a ha Cell hCell ε] at hz'
    change z ∈ inheritedDownPostlaunchPastCell a Cell ∧
      z ∈ ReferenceGeneratedInheritedDownPostlaunchOccurrence.inheritedDownPostlaunchHashedOccurrence
        (rate := rate) rewards C_star C_h i alpha k q hAlpha w hq hqQ control0 δ at hz
    change z ∈ inheritedDownPostlaunchPastCell a Cell ∧
      z ∈ ReferenceGeneratedInheritedDownPostlaunchOccurrence.inheritedDownPostlaunchHashedOccurrence
        (rate := rate) rewards C_star C_h i alpha k q hAlpha w hq hqQ control0 ε at hz'
    have hHit := hz.2
    have hHit' := hz'.2
    change z ∈ ReferenceGeneratedInheritedDownPostlaunchOccurrence.inheritedDownPostlaunchOccurrence
      (rate := rate) rewards C_star C_h i alpha k q hAlpha w hq hqQ control0 δ ∧ _ at hHit
    change z ∈ ReferenceGeneratedInheritedDownPostlaunchOccurrence.inheritedDownPostlaunchOccurrence
      (rate := rate) rewards C_star C_h i alpha k q hAlpha w hq hqQ control0 ε ∧ _ at hHit'
    exact hne (ReferenceGeneratedInheritedDownPostlaunchOccurrence.inheritedDownPostlaunchOccurrence_unique
      (rate := rate) rewards C_star C_h i alpha k q hAlpha w hq hqQ control0 z δ ε hHit.1 hHit'.1)
  have hSpair : Pairwise (Disjoint on Sset) := by
    intro δ ε hne
    change Disjoint (Sset δ) (Sset ε)
    rw [Set.disjoint_left]
    intro z hz hz'
    change z ∈ inheritedDownPostlaunchLocalizedSourceEvent rate rewards C_star C_h i alpha k q
      hAlpha w hq hqQ control0 a ha Cell hCell δ at hz
    change z ∈ inheritedDownPostlaunchLocalizedSourceEvent rate rewards C_star C_h i alpha k q
      hAlpha w hq hqQ control0 a ha Cell hCell ε at hz'
    rw [inheritedDownPostlaunchLocalizedSourceEvent_eq_pastCell_inter_occurrence rate rewards C_star C_h i alpha k q
      hAlpha w hq hqQ control0 a ha Cell hCell δ] at hz
    rw [inheritedDownPostlaunchLocalizedSourceEvent_eq_pastCell_inter_occurrence rate rewards C_star C_h i alpha k q
      hAlpha w hq hqQ control0 a ha Cell hCell ε] at hz'
    change z ∈ inheritedDownPostlaunchPastCell a Cell ∧
      z ∈ ReferenceGeneratedInheritedDownPostlaunchOccurrence.inheritedDownPostlaunchOccurrence
        (rate := rate) rewards C_star C_h i alpha k q hAlpha w hq hqQ control0 δ at hz
    change z ∈ inheritedDownPostlaunchPastCell a Cell ∧
      z ∈ ReferenceGeneratedInheritedDownPostlaunchOccurrence.inheritedDownPostlaunchOccurrence
        (rate := rate) rewards C_star C_h i alpha k q hAlpha w hq hqQ control0 ε at hz'
    exact hne (ReferenceGeneratedInheritedDownPostlaunchOccurrence.inheritedDownPostlaunchOccurrence_unique
      (rate := rate) rewards C_star C_h i alpha k q hAlpha w hq hqQ control0 z δ ε hz.2 hz'.2)
  have hHmeas (δ : ReferenceGeneratedInheritedDownPostlaunchOccurrence.Lambda p alpha) :
      MeasurableSet (Hset δ) :=
    measurableSet_inheritedDownPostlaunchLocalizedHashedSourceEvent rate rewards C_star C_h i alpha k q
      hAlpha w hq hqQ control0 a ha Cell hCell δ
  have hSmeas (δ : ReferenceGeneratedInheritedDownPostlaunchOccurrence.Lambda p alpha) :
      MeasurableSet (Sset δ) :=
    measurableSet_inheritedDownPostlaunchLocalizedSourceEvent rate rewards C_star C_h i alpha k q
      hAlpha w hq hqQ control0 a ha Cell hCell δ
  constructor
  · calc
      BootstrapPrivateRoundStreams.sourceInputLaw p
          {z | z ∈ B ∧ z ∈
            ReferenceGeneratedInheritedDownPostlaunchOccurrence.inheritedDownPostlaunchDetector
              (rate := rate) rewards C_star C_h i alpha k q hAlpha w hq hqQ control0} =
          BootstrapPrivateRoundStreams.sourceInputLaw p (⋃ δ, Hset δ) := by rw [hHunion]
      _ = ∑' δ, BootstrapPrivateRoundStreams.sourceInputLaw p (Hset δ) :=
        measure_iUnion hHpair hHmeas
      _ = ∑ δ, BootstrapPrivateRoundStreams.sourceInputLaw p (Hset δ) := by rw [tsum_fintype]
  · calc
      BootstrapPrivateRoundStreams.sourceInputLaw p
          {z | z ∈ B ∧ z ∈
            ReferenceGeneratedInheritedDownPostlaunchOccurrence.inheritedDownPostlaunchOccurrenceUnion
              (rate := rate) rewards C_star C_h i alpha k q hAlpha w hq hqQ control0} =
          BootstrapPrivateRoundStreams.sourceInputLaw p (⋃ δ, Sset δ) := by rw [hSunion]
      _ = ∑' δ, BootstrapPrivateRoundStreams.sourceInputLaw p (Sset δ) :=
        measure_iUnion hSpair hSmeas
      _ = ∑ δ, BootstrapPrivateRoundStreams.sourceInputLaw p (Sset δ) := by rw [tsum_fintype]

/-- Localized original-source half mass for the full inherited postlaunch
detector union. The sums run over the actual selected row, launch index, and
physical round, with no normalization or extra union-bound factor. -/
theorem inheritedDownPostlaunchDetector_source_mass_half
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (alpha k q : ℕ)
    (hAlpha : alpha ≤ p.T) (w : Candidate p) (hq : 1 ≤ q)
    (hqQ : q ≤ AffineBatchDecoder.quota p)
    (control0 : ContinuousLearningRows.TimeControl p)
    (a : Fin p.T) (ha : a.val ≤ alpha)
    (Cell : Set (CompletePublicTable.IDArray p × GeneratedBootstrapRoundLaw.Past p a))
    (hCell : MeasurableSet Cell) :
    let B := inheritedDownPostlaunchPastCell a Cell
    BootstrapPrivateRoundStreams.sourceInputLaw p
        {z | z ∈ B ∧ z ∈
          ReferenceGeneratedInheritedDownPostlaunchOccurrence.inheritedDownPostlaunchDetector
            (rate := rate) rewards C_star C_h i alpha k q hAlpha w hq hqQ control0} =
      ((1 : ENNReal) / 2) * BootstrapPrivateRoundStreams.sourceInputLaw p
        {z | z ∈ B ∧ z ∈
          ReferenceGeneratedInheritedDownPostlaunchOccurrence.inheritedDownPostlaunchOccurrenceUnion
            (rate := rate) rewards C_star C_h i alpha k q hAlpha w hq hqQ control0} := by
  classical
  dsimp
  let B := inheritedDownPostlaunchPastCell a Cell
  have hsum := inheritedDownPostlaunchDetector_source_sum rate rewards C_star C_h i alpha k q
    hAlpha w hq hqQ control0 a ha Cell hCell
  calc
    BootstrapPrivateRoundStreams.sourceInputLaw p
        {z | z ∈ B ∧ z ∈
          ReferenceGeneratedInheritedDownPostlaunchOccurrence.inheritedDownPostlaunchDetector
            (rate := rate) rewards C_star C_h i alpha k q hAlpha w hq hqQ control0} =
        ∑ δ : ReferenceGeneratedInheritedDownPostlaunchOccurrence.Lambda p alpha,
          BootstrapPrivateRoundStreams.sourceInputLaw p
            (inheritedDownPostlaunchLocalizedHashedSourceEvent rate rewards C_star C_h i alpha k q
              hAlpha w hq hqQ control0 a ha Cell hCell δ) := hsum.1
    _ = ∑ δ : ReferenceGeneratedInheritedDownPostlaunchOccurrence.Lambda p alpha,
          ((1 : ENNReal) / 2) * BootstrapPrivateRoundStreams.sourceInputLaw p
            (inheritedDownPostlaunchLocalizedSourceEvent rate rewards C_star C_h i alpha k q
              hAlpha w hq hqQ control0 a ha Cell hCell δ) := by
      apply Finset.sum_congr rfl
      intro δ hδ
      exact inheritedDownPostlaunch_localizedSourceEvent_hash_half rate rewards C_star C_h i alpha k q
        hAlpha w hq hqQ control0 a ha Cell hCell δ
    _ = ((1 : ENNReal) / 2) *
          ∑ δ : ReferenceGeneratedInheritedDownPostlaunchOccurrence.Lambda p alpha,
            BootstrapPrivateRoundStreams.sourceInputLaw p
              (inheritedDownPostlaunchLocalizedSourceEvent rate rewards C_star C_h i alpha k q
                hAlpha w hq hqQ control0 a ha Cell hCell δ) := by
      rw [Finset.mul_sum]
    _ = ((1 : ENNReal) / 2) * BootstrapPrivateRoundStreams.sourceInputLaw p
          {z | z ∈ B ∧ z ∈
            ReferenceGeneratedInheritedDownPostlaunchOccurrence.inheritedDownPostlaunchOccurrenceUnion
              (rate := rate) rewards C_star C_h i alpha k q hAlpha w hq hqQ control0} := by
      rw [← hsum.2]

private theorem inheritedDownPostlaunch_fixedStratum_source_sum
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (alpha k q : ℕ)
    (hAlpha : alpha ≤ p.T) (w : Candidate p) (hq : 1 ≤ q)
    (hqQ : q ≤ AffineBatchDecoder.quota p)
    (control0 : ContinuousLearningRows.TimeControl p)
    (a : Fin p.T) (ha : a.val ≤ alpha)
    (Cell : Set (CompletePublicTable.IDArray p × GeneratedBootstrapRoundLaw.Past p a))
    (hCell : MeasurableSet Cell)
    (j : Fin (M p)) (s : Fin p.T) (hAlphaS : alpha ≤ s.val) :
    let B := inheritedDownPostlaunchPastCell a Cell
    (BootstrapPrivateRoundStreams.sourceInputLaw p
        {z | z ∈ B ∧ z ∈ inheritedDownPostlaunchFixedStratumDetector rate rewards C_star C_h i
          alpha k q hAlpha w hq hqQ control0 j s hAlphaS} =
      ∑ r : {r : Fin p.T // s.val ≤ r.val},
        BootstrapPrivateRoundStreams.sourceInputLaw p
          (inheritedDownPostlaunchLocalizedHashedSourceEvent rate rewards C_star C_h i alpha k q
            hAlpha w hq hqQ control0 a ha Cell hCell ⟨(j, s, r.1), ⟨hAlphaS, r.2⟩⟩)) ∧
    (BootstrapPrivateRoundStreams.sourceInputLaw p
        {z | z ∈ B ∧ z ∈ inheritedDownPostlaunchFixedStratumOccurrenceUnion rate rewards C_star C_h i
          alpha k q hAlpha w hq hqQ control0 j s hAlphaS} =
      ∑ r : {r : Fin p.T // s.val ≤ r.val},
        BootstrapPrivateRoundStreams.sourceInputLaw p
          (inheritedDownPostlaunchLocalizedSourceEvent rate rewards C_star C_h i alpha k q
            hAlpha w hq hqQ control0 a ha Cell hCell ⟨(j, s, r.1), ⟨hAlphaS, r.2⟩⟩)) := by
  classical
  dsimp
  let B := inheritedDownPostlaunchPastCell a Cell
  let Δ : {r : Fin p.T // s.val ≤ r.val} →
      ReferenceGeneratedInheritedDownPostlaunchOccurrence.Lambda p alpha :=
    fun r => ⟨(j, s, r.1), ⟨hAlphaS, r.2⟩⟩
  let Hset : {r : Fin p.T // s.val ≤ r.val} → Set (SourceInput p) :=
    fun r => inheritedDownPostlaunchLocalizedHashedSourceEvent rate rewards C_star C_h i alpha k q
      hAlpha w hq hqQ control0 a ha Cell hCell (Δ r)
  let Sset : {r : Fin p.T // s.val ≤ r.val} → Set (SourceInput p) :=
    fun r => inheritedDownPostlaunchLocalizedSourceEvent rate rewards C_star C_h i alpha k q
      hAlpha w hq hqQ control0 a ha Cell hCell (Δ r)
  have hHunion : {z | z ∈ B ∧ z ∈
      inheritedDownPostlaunchFixedStratumDetector rate rewards C_star C_h i alpha k q
        hAlpha w hq hqQ control0 j s hAlphaS} = ⋃ r, Hset r := by
    ext z
    constructor
    · rintro ⟨hBz, hdet⟩
      change z ∈ ⋃ r : {r : Fin p.T // s.val ≤ r.val},
        ReferenceGeneratedInheritedDownPostlaunchOccurrence.inheritedDownPostlaunchHashedOccurrence
          (rate := rate) rewards C_star C_h i alpha k q hAlpha w hq hqQ control0
          ⟨(j, s, r.1), ⟨hAlphaS, r.2⟩⟩ at hdet
      rcases Set.mem_iUnion.mp hdet with ⟨r, hhit⟩
      have hlocal : z ∈ Hset r := by
        change z ∈ inheritedDownPostlaunchLocalizedHashedSourceEvent rate rewards C_star C_h i
          alpha k q hAlpha w hq hqQ control0 a ha Cell hCell (Δ r)
        rw [inheritedDownPostlaunchLocalizedHashedSourceEvent_eq_pastCell_inter_hashedOccurrence rate rewards C_star C_h i
          alpha k q hAlpha w hq hqQ control0 a ha Cell hCell (Δ r)]
        exact ⟨hBz, hhit⟩
      exact Set.mem_iUnion.mpr ⟨r, hlocal⟩
    · intro hz
      rcases Set.mem_iUnion.mp hz with ⟨r, hhit⟩
      change z ∈ inheritedDownPostlaunchLocalizedHashedSourceEvent rate rewards C_star C_h i
        alpha k q hAlpha w hq hqQ control0 a ha Cell hCell (Δ r) at hhit
      rw [inheritedDownPostlaunchLocalizedHashedSourceEvent_eq_pastCell_inter_hashedOccurrence rate rewards C_star C_h i alpha k q
        hAlpha w hq hqQ control0 a ha Cell hCell (Δ r)] at hhit
      change z ∈ inheritedDownPostlaunchPastCell a Cell ∧
        z ∈ ReferenceGeneratedInheritedDownPostlaunchOccurrence.inheritedDownPostlaunchHashedOccurrence
          (rate := rate) rewards C_star C_h i alpha k q hAlpha w hq hqQ control0 (Δ r) at hhit
      exact ⟨hhit.1, Set.mem_iUnion.mpr ⟨r, hhit.2⟩⟩
  have hSunion : {z | z ∈ B ∧ z ∈
      inheritedDownPostlaunchFixedStratumOccurrenceUnion rate rewards C_star C_h i alpha k q
        hAlpha w hq hqQ control0 j s hAlphaS} = ⋃ r, Sset r := by
    ext z
    constructor
    · rintro ⟨hBz, hocc⟩
      change z ∈ ⋃ r : {r : Fin p.T // s.val ≤ r.val},
        ReferenceGeneratedInheritedDownPostlaunchOccurrence.inheritedDownPostlaunchOccurrence
          (rate := rate) rewards C_star C_h i alpha k q hAlpha w hq hqQ control0
          ⟨(j, s, r.1), ⟨hAlphaS, r.2⟩⟩ at hocc
      rcases Set.mem_iUnion.mp hocc with ⟨r, hocc⟩
      have hlocal : z ∈ Sset r := by
        change z ∈ inheritedDownPostlaunchLocalizedSourceEvent rate rewards C_star C_h i alpha k q
          hAlpha w hq hqQ control0 a ha Cell hCell (Δ r)
        rw [inheritedDownPostlaunchLocalizedSourceEvent_eq_pastCell_inter_occurrence rate rewards C_star C_h i
          alpha k q hAlpha w hq hqQ control0 a ha Cell hCell (Δ r)]
        exact ⟨hBz, hocc⟩
      exact Set.mem_iUnion.mpr ⟨r, hlocal⟩
    · intro hz
      rcases Set.mem_iUnion.mp hz with ⟨r, hocc⟩
      change z ∈ inheritedDownPostlaunchLocalizedSourceEvent rate rewards C_star C_h i alpha k q
        hAlpha w hq hqQ control0 a ha Cell hCell (Δ r) at hocc
      rw [inheritedDownPostlaunchLocalizedSourceEvent_eq_pastCell_inter_occurrence rate rewards C_star C_h i alpha k q
        hAlpha w hq hqQ control0 a ha Cell hCell (Δ r)] at hocc
      change z ∈ inheritedDownPostlaunchPastCell a Cell ∧
        z ∈ ReferenceGeneratedInheritedDownPostlaunchOccurrence.inheritedDownPostlaunchOccurrence
          (rate := rate) rewards C_star C_h i alpha k q hAlpha w hq hqQ control0 (Δ r) at hocc
      exact ⟨hocc.1, Set.mem_iUnion.mpr ⟨r, hocc.2⟩⟩
  have hpair := inheritedDownPostlaunch_fixedStratum_pairwiseDisjoint rate rewards C_star C_h i alpha k q
    hAlpha w hq hqQ control0 a ha Cell hCell j s hAlphaS
  have hHpair : Pairwise (Disjoint on Hset) := by
    intro r r' hne
    change Disjoint (Hset r) (Hset r')
    rw [Set.disjoint_left]
    intro z hz hz'
    change z ∈ inheritedDownPostlaunchLocalizedHashedSourceEvent rate rewards C_star C_h i alpha k q
      hAlpha w hq hqQ control0 a ha Cell hCell (Δ r) at hz
    change z ∈ inheritedDownPostlaunchLocalizedHashedSourceEvent rate rewards C_star C_h i alpha k q
      hAlpha w hq hqQ control0 a ha Cell hCell (Δ r') at hz'
    rw [inheritedDownPostlaunchLocalizedHashedSourceEvent_eq_pastCell_inter_hashedOccurrence rate rewards C_star C_h i alpha k q
      hAlpha w hq hqQ control0 a ha Cell hCell (Δ r)] at hz
    rw [inheritedDownPostlaunchLocalizedHashedSourceEvent_eq_pastCell_inter_hashedOccurrence rate rewards C_star C_h i alpha k q
      hAlpha w hq hqQ control0 a ha Cell hCell (Δ r')] at hz'
    change z ∈ inheritedDownPostlaunchPastCell a Cell ∧
      z ∈ ReferenceGeneratedInheritedDownPostlaunchOccurrence.inheritedDownPostlaunchHashedOccurrence
        (rate := rate) rewards C_star C_h i alpha k q hAlpha w hq hqQ control0 (Δ r) at hz
    change z ∈ inheritedDownPostlaunchPastCell a Cell ∧
      z ∈ ReferenceGeneratedInheritedDownPostlaunchOccurrence.inheritedDownPostlaunchHashedOccurrence
        (rate := rate) rewards C_star C_h i alpha k q hAlpha w hq hqQ control0 (Δ r') at hz'
    have hOcc := hz.2
    have hOcc' := hz'.2
    change z ∈ ReferenceGeneratedInheritedDownPostlaunchOccurrence.inheritedDownPostlaunchOccurrence
      (rate := rate) rewards C_star C_h i alpha k q hAlpha w hq hqQ control0 (Δ r) ∧ _ at hOcc
    change z ∈ ReferenceGeneratedInheritedDownPostlaunchOccurrence.inheritedDownPostlaunchOccurrence
      (rate := rate) rewards C_star C_h i alpha k q hAlpha w hq hqQ control0 (Δ r') ∧ _ at hOcc'
    have hsub : z ∈ Sset r := by
      change z ∈ inheritedDownPostlaunchLocalizedSourceEvent rate rewards C_star C_h i alpha k q
        hAlpha w hq hqQ control0 a ha Cell hCell (Δ r)
      rw [inheritedDownPostlaunchLocalizedSourceEvent_eq_pastCell_inter_occurrence rate rewards C_star C_h i
        alpha k q hAlpha w hq hqQ control0 a ha Cell hCell (Δ r)]
      change z ∈ ReferenceGeneratedInheritedDownPostlaunchOccurrence.inheritedDownPostlaunchOccurrence
        (rate := rate) rewards C_star C_h i alpha k q hAlpha w hq hqQ control0 (Δ r) ∧ _ at hOcc
      exact ⟨hz.1, hOcc.1⟩
    have hsub' : z ∈ Sset r' := by
      change z ∈ inheritedDownPostlaunchLocalizedSourceEvent rate rewards C_star C_h i alpha k q
        hAlpha w hq hqQ control0 a ha Cell hCell (Δ r')
      rw [inheritedDownPostlaunchLocalizedSourceEvent_eq_pastCell_inter_occurrence rate rewards C_star C_h i
        alpha k q hAlpha w hq hqQ control0 a ha Cell hCell (Δ r')]
      change z ∈ ReferenceGeneratedInheritedDownPostlaunchOccurrence.inheritedDownPostlaunchOccurrence
        (rate := rate) rewards C_star C_h i alpha k q hAlpha w hq hqQ control0 (Δ r') ∧ _ at hOcc'
      exact ⟨hz'.1, hOcc'.1⟩
    exact (Set.disjoint_left.mp (hpair hne)) hsub hsub'
  have hHmeas (r : {r : Fin p.T // s.val ≤ r.val}) : MeasurableSet (Hset r) := by
    exact measurableSet_inheritedDownPostlaunchLocalizedHashedSourceEvent rate rewards C_star C_h i alpha k q
      hAlpha w hq hqQ control0 a ha Cell hCell (Δ r)
  have hSmeas (r : {r : Fin p.T // s.val ≤ r.val}) : MeasurableSet (Sset r) := by
    exact measurableSet_inheritedDownPostlaunchLocalizedSourceEvent rate rewards C_star C_h i alpha k q
      hAlpha w hq hqQ control0 a ha Cell hCell (Δ r)
  have hSpair : Pairwise (Disjoint on Sset) := by
    intro r r' hne
    change Disjoint (Sset r) (Sset r')
    rw [Set.disjoint_left]
    intro z hz hz'
    exact (Set.disjoint_left.mp (hpair hne)) hz hz'
  constructor
  · calc
      BootstrapPrivateRoundStreams.sourceInputLaw p
          {z | z ∈ B ∧ z ∈ inheritedDownPostlaunchFixedStratumDetector rate rewards C_star C_h i
            alpha k q hAlpha w hq hqQ control0 j s hAlphaS} =
          BootstrapPrivateRoundStreams.sourceInputLaw p (⋃ r, Hset r) := by rw [hHunion]
      _ = ∑' r, BootstrapPrivateRoundStreams.sourceInputLaw p (Hset r) :=
        measure_iUnion hHpair hHmeas
      _ = ∑ r, BootstrapPrivateRoundStreams.sourceInputLaw p (Hset r) := by rw [tsum_fintype]
  · calc
      BootstrapPrivateRoundStreams.sourceInputLaw p
          {z | z ∈ B ∧ z ∈ inheritedDownPostlaunchFixedStratumOccurrenceUnion rate rewards C_star C_h i
            alpha k q hAlpha w hq hqQ control0 j s hAlphaS} =
          BootstrapPrivateRoundStreams.sourceInputLaw p (⋃ r, Sset r) := by rw [hSunion]
      _ = ∑' r, BootstrapPrivateRoundStreams.sourceInputLaw p (Sset r) :=
        measure_iUnion hSpair hSmeas
      _ = ∑ r, BootstrapPrivateRoundStreams.sourceInputLaw p (Sset r) := by rw [tsum_fintype]

/-- The unnormalized localized half-mass identity with the selected row and
launch round fixed. The round union contains exactly `r : Fin T` satisfying
`s ≤ r`; it is not a conditional probability. -/
theorem inheritedDownPostlaunchDetector_fixed_stratum_mass_half
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (alpha k q : ℕ)
    (hAlpha : alpha ≤ p.T) (w : Candidate p) (hq : 1 ≤ q)
    (hqQ : q ≤ AffineBatchDecoder.quota p)
    (control0 : ContinuousLearningRows.TimeControl p)
    (a : Fin p.T) (ha : a.val ≤ alpha)
    (Cell : Set (CompletePublicTable.IDArray p × GeneratedBootstrapRoundLaw.Past p a))
    (hCell : MeasurableSet Cell)
    (j : Fin (M p)) (s : Fin p.T) (hAlphaS : alpha ≤ s.val) :
    let B := inheritedDownPostlaunchPastCell a Cell
    BootstrapPrivateRoundStreams.sourceInputLaw p
        {z | z ∈ B ∧ z ∈ inheritedDownPostlaunchFixedStratumDetector rate rewards C_star C_h i
          alpha k q hAlpha w hq hqQ control0 j s hAlphaS} =
      ((1 : ENNReal) / 2) * BootstrapPrivateRoundStreams.sourceInputLaw p
        {z | z ∈ B ∧ z ∈ inheritedDownPostlaunchFixedStratumOccurrenceUnion rate rewards C_star C_h i
          alpha k q hAlpha w hq hqQ control0 j s hAlphaS} := by
  classical
  dsimp
  let B := inheritedDownPostlaunchPastCell a Cell
  have hsum := inheritedDownPostlaunch_fixedStratum_source_sum rate rewards C_star C_h i alpha k q
    hAlpha w hq hqQ control0 a ha Cell hCell j s hAlphaS
  calc
    BootstrapPrivateRoundStreams.sourceInputLaw p
        {z | z ∈ B ∧ z ∈ inheritedDownPostlaunchFixedStratumDetector rate rewards C_star C_h i
          alpha k q hAlpha w hq hqQ control0 j s hAlphaS} =
        ∑ r : {r : Fin p.T // s.val ≤ r.val},
          BootstrapPrivateRoundStreams.sourceInputLaw p
            (inheritedDownPostlaunchLocalizedHashedSourceEvent rate rewards C_star C_h i alpha k q
              hAlpha w hq hqQ control0 a ha Cell hCell ⟨(j, s, r.1), ⟨hAlphaS, r.2⟩⟩) := hsum.1
    _ = ∑ r : {r : Fin p.T // s.val ≤ r.val},
          ((1 : ENNReal) / 2) * BootstrapPrivateRoundStreams.sourceInputLaw p
            (inheritedDownPostlaunchLocalizedSourceEvent rate rewards C_star C_h i alpha k q
              hAlpha w hq hqQ control0 a ha Cell hCell ⟨(j, s, r.1), ⟨hAlphaS, r.2⟩⟩) := by
      apply Finset.sum_congr rfl
      intro r hr
      exact inheritedDownPostlaunch_localizedSourceEvent_hash_half rate rewards C_star C_h i alpha k q
        hAlpha w hq hqQ control0 a ha Cell hCell ⟨(j, s, r.1), ⟨hAlphaS, r.2⟩⟩
    _ = ((1 : ENNReal) / 2) *
          ∑ r : {r : Fin p.T // s.val ≤ r.val},
            BootstrapPrivateRoundStreams.sourceInputLaw p
              (inheritedDownPostlaunchLocalizedSourceEvent rate rewards C_star C_h i alpha k q
                hAlpha w hq hqQ control0 a ha Cell hCell ⟨(j, s, r.1), ⟨hAlphaS, r.2⟩⟩) := by
      rw [Finset.mul_sum]
    _ = ((1 : ENNReal) / 2) * BootstrapPrivateRoundStreams.sourceInputLaw p
          {z | z ∈ B ∧ z ∈ inheritedDownPostlaunchFixedStratumOccurrenceUnion rate rewards C_star C_h i
            alpha k q hAlpha w hq hqQ control0 j s hAlphaS} := by
      rw [← hsum.2]

end Bandits.Support.ReferenceGeneratedInheritedDownPostlaunchDetectorMass

end
