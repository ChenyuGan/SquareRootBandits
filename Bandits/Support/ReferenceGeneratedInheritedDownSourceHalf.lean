/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedInheritedDownPrefixMarker

import Lean.Elab.Tactic.Omega

/-!
# Original-source half law for an inherited DOWN prefix

Sources: `sources/zip4/manuscript/appendix_a_local_protocol.tex:111-138`,
`sources/zip4/manuscript/appendix_b_communication.tex:724-736`,
`sources/zip4/manuscript/07_public_setup.tex:127-164`, and
`sources/zip4/manuscript/05_binary_transport.tex:20-42`.

The event below retains the actual initialized pending bank and its actual
cohort boundary, then appends the positive executed tests in the actual DOWN
calendar. Its current test is generated from the original selected source and
the actual current physical step. The removed current affine pair is used only
for the hash-one refinement. The resulting half identity is with respect to
the original source probability law and uses no conditional normalization.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal
open scoped Classical
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.ContinuousLearningRows
open Bandits.Support.AffineChannelLaw
open Bandits.Support.ReferenceGeneratedDownBatchCalendar
open Bandits.Support.ReferenceGeneratedInheritedDownCompletion
open Bandits.Support.ReferenceGeneratedInheritedDownCohort
open Bandits.Support.ReferenceGeneratedAffineHashHalf

namespace Bandits.Support.ReferenceGeneratedInheritedDownSourceHalf

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceGeneratedDownBatchCalendar.RateInput
abbrev SourceInput := BootstrapPrivateRoundStreams.SourceInput
abbrev Candidate (p : Parameters) :=
  AffineChannelLaw.Word (AffineBatchDecoder.width p)
abbrev PairRemainder (p : Parameters) (j : Fin (M p)) (r : Fin p.T)
    (i : Fin (p.m - 1)) :=
  ReferenceSelectedAffinePairLaw.Remainder p j r (0, i)
abbrev LaunchSource {p : Parameters} {rate : RateInput p}
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T) :=
  ReferenceGeneratedDownBatchCalendar.LaunchSource rate rewards C_star C_h s hs

variable {p : Parameters} {rate : RateInput p}

/-- The literal inherited DOWN source event. Membership retains the selected
row and DOWN follower, the full admitted past cell, the actual launch source,
the actual old-plus-new marker, and the actual executed current test. The
current test is filtered only by execution and its sent word; `none` and a
stored `some false` comparison remain represented by the calendar test. -/
def inheritedDownSourceEvent
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (alpha k q : ℕ) (_hAlpha : alpha ≤ p.T)
    (w : Candidate p) (_hq : 1 ≤ q) (_hqQ : q ≤ AffineBatchDecoder.quota p)
    (j : Fin (M p)) (r : Fin p.T) (s : ℕ) (hsr : s ≤ r.val)
    (_control0 : ContinuousLearningRows.TimeControl p)
    (Cell : Set (CompletePublicTable.IDArray p × GeneratedBootstrapRoundLaw.Past p r))
    (_hCell : MeasurableSet Cell) (i : Fin (p.m - 1)) : Set (SourceInput p) :=
  {z | ReferenceSelectedAffinePairLaw.selector p r z = (j, some ((0, i) : Channel p)) ∧
    ReferenceGeneratedPrelaunchDownCurrentPair.sourcePastView r z ∈ Cell ∧
    ∃ x : ReferenceGeneratedInheritedDownPrefixMarker.LaunchSource
        (rate := rate) rewards C_star C_h s (by omega),
      x.1 = z ∧
      ReferenceGeneratedInheritedDownPrefixMarker.inheritedDownMarker
        (rate := rate) rewards C_star C_h alpha k q w s (by omega) i x (r.val - s) ∧
      ∃ test : ReferenceGeneratedDownBatchCalendar.ExecutedTest p,
        ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate
          ((ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
            rate rewards C_star C_h s (by omega) i x).2 ⟨r.val - s, by omega⟩) = some test ∧
        test.sent ≠ some w}

/-- Add the affine equation for the original pair at `(j,r,DOWN,i)`. -/
def inheritedDownHashOneSourceEvent
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (alpha k q : ℕ) (hAlpha : alpha ≤ p.T)
    (w : Candidate p) (hq : 1 ≤ q) (hqQ : q ≤ AffineBatchDecoder.quota p)
    (j : Fin (M p)) (r : Fin p.T) (s : ℕ) (hsr : s ≤ r.val)
    (control0 : ContinuousLearningRows.TimeControl p)
    (Cell : Set (CompletePublicTable.IDArray p × GeneratedBootstrapRoundLaw.Past p r))
    (hCell : MeasurableSet Cell) (i : Fin (p.m - 1)) : Set (SourceInput p) :=
  {z | z ∈ inheritedDownSourceEvent (rate := rate) rewards C_star C_h alpha k q hAlpha
      w hq hqQ j r s hsr control0 Cell hCell i ∧
    AffineChannelLaw.affineHash (((z.1.2 j).2 r).2 (0, i)) w = 1}

private theorem inheritedDownCurrentInput_eq_generatedNextInput
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (j : Fin (M p)) (r : Fin p.T) (s : ℕ)
    (hsr : s ≤ r.val) (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1)) (z : SourceInput p)
    (x : ReferenceGeneratedInheritedDownPrefixMarker.LaunchSource
      (rate := rate) rewards C_star C_h s (by omega))
    (hx : x.1 = z)
    (hselector : ReferenceSelectedAffinePairLaw.selector p r z =
      (j, some ((0, i) : Channel p)))
    (hbranch : z ∈ ReferenceGeneratedAffineHashHalf.generatedLaunchBranch
      (rate := rate) rewards C_star C_h j r (0, i) s) :
    ReferenceGeneratedInheritedDownPrefixMarker.inheritedDownCurrentInput
        (rate := rate) rewards C_star C_h j r s hsr control0 i x
        (by rw [hx]; exact hselector) =
      ReferenceGeneratedAffineHashHalf.generatedNextInputOfBranch (rate := rate)
        rewards C_star C_h j r (0, i) s hsr control0 ⟨z, hbranch⟩ := by
  have branchEq :
      (⟨x.1, ⟨(by rw [hx]; exact hselector), x.property.1, x.property.2⟩⟩ :
        {source : SourceInput p // source ∈
          ReferenceGeneratedAffineHashHalf.generatedLaunchBranch (rate := rate)
            rewards C_star C_h j r (0, i) s}) = ⟨z, hbranch⟩ := by
    apply Subtype.ext
    exact hx
  change ReferenceGeneratedAffineHashHalf.generatedNextInputOfBranch (rate := rate)
      rewards C_star C_h j r (0, i) s hsr control0
        ⟨x.1, ⟨(by rw [hx]; exact hselector), x.property.1, x.property.2⟩⟩ = _
  rw [branchEq]

/-- The concrete source event is exactly Z's generated positive event over
P's actual inherited-marker remainder cylinder. -/
theorem inheritedDownSourceEvent_eq_generatedPositiveSourceEvent
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (alpha k q : ℕ) (hAlpha : alpha ≤ p.T)
    (w : Candidate p) (hq : 1 ≤ q) (hqQ : q ≤ AffineBatchDecoder.quota p)
    (j : Fin (M p)) (r : Fin p.T) (s : ℕ) (hsr : s ≤ r.val)
    (control0 : ContinuousLearningRows.TimeControl p)
    (Cell : Set (CompletePublicTable.IDArray p × GeneratedBootstrapRoundLaw.Past p r))
    (hCell : MeasurableSet Cell) (i : Fin (p.m - 1)) :
    inheritedDownSourceEvent (rate := rate) rewards C_star C_h alpha k q hAlpha
        w hq hqQ j r s hsr control0 Cell hCell i =
      ReferenceGeneratedAffineHashHalf.generatedPositiveSourceEvent (rate := rate)
        rewards C_star C_h j r 0 i s hsr control0 w
        (ReferenceGeneratedInheritedDownPrefixMarker.inheritedDownMarkerRemainder
          rate rewards C_star C_h alpha k q hAlpha w hq hqQ j r s hsr control0
          Cell hCell i) := by
  classical
  let C := ReferenceGeneratedInheritedDownPrefixMarker.inheritedDownMarkerRemainder
    rate rewards C_star C_h alpha k q hAlpha w hq hqQ j r s hsr control0 Cell hCell i
  ext z
  constructor
  · intro hsource
    rcases hsource with ⟨hselector, hcell, x, hx, hmarker, test, htest, hsent⟩
    let split := ReferenceSelectedAffinePairLaw.fixedPairSplit p j r (0, i)
    let a := (split z).1
    let v := (split z).2
    have hsplit : split.symm (a, v) = z := by
      dsimp [a, v]
      exact split.symm_apply_apply z
    have hpair := ReferenceGeneratedInheritedDownPrefixMarker.inheritedDownMarkerRemainder_pair_iff
      (rate := rate) rewards C_star C_h alpha k q hAlpha w hq hqQ j r s hsr control0
      Cell hCell i a v
    have hremainder : v ∈ C := by
      simpa only [C, v] using hpair.mpr (by
        change ReferenceSelectedAffinePairLaw.selector p r (split.symm (a, v)) =
          (j, some ((0, i) : Channel p)) ∧
          ReferenceGeneratedPrelaunchDownCurrentPair.sourcePastView r
            (split.symm (a, v)) ∈ Cell ∧
          ∃ x : ReferenceGeneratedInheritedDownPrefixMarker.LaunchSource
              (rate := rate) rewards C_star C_h s (by omega),
            x.1 = split.symm (a, v) ∧
            ReferenceGeneratedInheritedDownPrefixMarker.inheritedDownMarker
              (rate := rate) rewards C_star C_h alpha k q w s (by omega) i x
              (r.val - s)
        refine ⟨?_, ?_, x, ?_, hmarker⟩
        · rw [hsplit]
          exact hselector
        · rw [hsplit]
          exact hcell
        · rw [hsplit]
          exact hx)
    have hbranch : z ∈ ReferenceGeneratedAffineHashHalf.generatedLaunchBranch
        (rate := rate) rewards C_star C_h j r (0, i) s := by
      exact ⟨hselector, by rw [← hx]; exact x.property.1,
        by rw [← hx]; exact x.property.2⟩
    have hselectorX : ReferenceSelectedAffinePairLaw.selector p r x.1 =
        (j, some ((0, i) : Channel p)) := by
      rw [hx]
      exact hselector
    have hinput := inheritedDownCurrentInput_eq_generatedNextInput
      (rate := rate) rewards C_star C_h j r s hsr control0 i z x hx hselector hbranch
    have hcurrent := ReferenceGeneratedInheritedDownPrefixMarker.inheritedDownCurrentPositiveSent_iff
      (rate := rate) rewards C_star C_h j r s hsr control0 i x hselectorX w
    have hphysical := hcurrent.mp ⟨test, htest, hsent⟩
    have hpositiveZ :
        ReferenceGeneratedAffineHashHalf.directionPositive 0
          (ReferenceGeneratedAffineHashHalf.generatedNextInputOfBranch (rate := rate)
            rewards C_star C_h j r (0, i) s hsr control0 ⟨z, hbranch⟩) = true := by
      simpa [ReferenceGeneratedAffineHashHalf.directionPositive, hinput] using hphysical.1
    have hsentZ :
        ReferenceGeneratedAffineHashHalf.directionSent 0
          (ReferenceGeneratedAffineHashHalf.generatedNextInputOfBranch (rate := rate)
            rewards C_star C_h j r (0, i) s hsr control0 ⟨z, hbranch⟩) ≠ some w := by
      simpa [ReferenceGeneratedAffineHashHalf.directionSent, hinput] using hphysical.2
    change ∃ hz : z ∈ ReferenceGeneratedAffineHashHalf.generatedLaunchBranch
        (rate := rate) rewards C_star C_h j r (0, i) s,
      (ReferenceSelectedAffinePairLaw.fixedPairSplit p j r (0, i) z).2 ∈ C ∧
        ReferenceGeneratedAffineHashHalf.directionPositive 0
          (ReferenceGeneratedAffineHashHalf.generatedNextInputOfBranch (rate := rate)
            rewards C_star C_h j r (0, i) s hsr control0 ⟨z, hz⟩) = true ∧
        ReferenceGeneratedAffineHashHalf.directionSent 0
          (ReferenceGeneratedAffineHashHalf.generatedNextInputOfBranch (rate := rate)
            rewards C_star C_h j r (0, i) s hsr control0 ⟨z, hz⟩) ≠ some w
    refine ⟨hbranch, ?_, hpositiveZ, hsentZ⟩
    · rw [show (ReferenceSelectedAffinePairLaw.fixedPairSplit p j r (0, i) z).2 = v by rfl]
      exact hremainder
  · intro hgenerated
    change ∃ hbranch : z ∈ ReferenceGeneratedAffineHashHalf.generatedLaunchBranch
        (rate := rate) rewards C_star C_h j r (0, i) s,
      (ReferenceSelectedAffinePairLaw.fixedPairSplit p j r (0, i) z).2 ∈ C ∧
        ReferenceGeneratedAffineHashHalf.directionPositive 0
          (ReferenceGeneratedAffineHashHalf.generatedNextInputOfBranch (rate := rate)
            rewards C_star C_h j r (0, i) s hsr control0 ⟨z, hbranch⟩) = true ∧
        ReferenceGeneratedAffineHashHalf.directionSent 0
          (ReferenceGeneratedAffineHashHalf.generatedNextInputOfBranch (rate := rate)
            rewards C_star C_h j r (0, i) s hsr control0 ⟨z, hbranch⟩) ≠ some w at hgenerated
    rcases hgenerated with ⟨hbranch, hremainder, hpositive, hsent⟩
    let split := ReferenceSelectedAffinePairLaw.fixedPairSplit p j r (0, i)
    let a := (split z).1
    let v := (split z).2
    have hsplit : split.symm (a, v) = z := by
      dsimp [a, v]
      exact split.symm_apply_apply z
    have hpair := ReferenceGeneratedInheritedDownPrefixMarker.inheritedDownMarkerRemainder_pair_iff
      (rate := rate) rewards C_star C_h alpha k q hAlpha w hq hqQ j r s hsr control0
      Cell hCell i a v
    have hphysical := hpair.mp (by simpa only [C] using hremainder)
    rcases hphysical with ⟨hselector0, hcell0, x, hx0, hmarker⟩
    have hselector : ReferenceSelectedAffinePairLaw.selector p r z =
        (j, some ((0, i) : Channel p)) := by
      rw [← hsplit]
      exact hselector0
    have hcell : ReferenceGeneratedPrelaunchDownCurrentPair.sourcePastView r z ∈ Cell := by
      rw [← hsplit]
      exact hcell0
    have hx : x.1 = z := by rw [← hsplit]; exact hx0
    have hselectorX : ReferenceSelectedAffinePairLaw.selector p r x.1 =
        (j, some ((0, i) : Channel p)) := by
      rw [hx]
      exact hselector
    have hinput := inheritedDownCurrentInput_eq_generatedNextInput
      (rate := rate) rewards C_star C_h j r s hsr control0 i z x hx hselector hbranch
    have hphysical := ReferenceGeneratedInheritedDownPrefixMarker.inheritedDownCurrentPositiveSent_iff
      (rate := rate) rewards C_star C_h j r s hsr control0 i x hselectorX w
    have hdownPositive :
        ReferenceActiveAffinePositiveTest.downPositive
            (ReferenceGeneratedInheritedDownPrefixMarker.inheritedDownCurrentInput
              (rate := rate) rewards C_star C_h j r s hsr control0 i x hselectorX) = true ∧
          ReferenceActiveAffinePositiveTest.downSent
            (ReferenceGeneratedInheritedDownPrefixMarker.inheritedDownCurrentInput
              (rate := rate) rewards C_star C_h j r s hsr control0 i x hselectorX) ≠ some w := by
      constructor
      · rw [hinput]
        simpa [ReferenceGeneratedAffineHashHalf.directionPositive] using hpositive
      · rw [hinput]
        simpa [ReferenceGeneratedAffineHashHalf.directionSent] using hsent
    have htestSource := hphysical.mpr hdownPositive
    rcases htestSource with ⟨test, htest, hsent⟩
    exact ⟨hselector, hcell, x, hx, hmarker, test, htest, hsent⟩

/-- The source event with the original hash-one condition is exactly Z's
corresponding generated hash-one event. -/
theorem inheritedDownHashOneSourceEvent_eq_generatedPositiveHashOneSourceEvent
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (alpha k q : ℕ) (hAlpha : alpha ≤ p.T)
    (w : Candidate p) (hq : 1 ≤ q) (hqQ : q ≤ AffineBatchDecoder.quota p)
    (j : Fin (M p)) (r : Fin p.T) (s : ℕ) (hsr : s ≤ r.val)
    (control0 : ContinuousLearningRows.TimeControl p)
    (Cell : Set (CompletePublicTable.IDArray p × GeneratedBootstrapRoundLaw.Past p r))
    (hCell : MeasurableSet Cell) (i : Fin (p.m - 1)) :
    inheritedDownHashOneSourceEvent (rate := rate) rewards C_star C_h alpha k q hAlpha
        w hq hqQ j r s hsr control0 Cell hCell i =
      ReferenceGeneratedAffineHashHalf.generatedPositiveHashOneSourceEvent (rate := rate)
        rewards C_star C_h j r 0 i s hsr control0 w
        (ReferenceGeneratedInheritedDownPrefixMarker.inheritedDownMarkerRemainder
          rate rewards C_star C_h alpha k q hAlpha w hq hqQ j r s hsr control0
          Cell hCell i) := by
  ext z
  change (z ∈ inheritedDownSourceEvent (rate := rate) rewards C_star C_h alpha k q hAlpha
      w hq hqQ j r s hsr control0 Cell hCell i ∧
    AffineChannelLaw.affineHash (((z.1.2 j).2 r).2 (0, i)) w = 1) ↔
    (z ∈ ReferenceGeneratedAffineHashHalf.generatedPositiveSourceEvent (rate := rate)
        rewards C_star C_h j r 0 i s hsr control0 w
        (ReferenceGeneratedInheritedDownPrefixMarker.inheritedDownMarkerRemainder
          rate rewards C_star C_h alpha k q hAlpha w hq hqQ j r s hsr control0
          Cell hCell i) ∧
      AffineChannelLaw.affineHash (((z.1.2 j).2 r).2 (0, i)) w = 1)
  rw [inheritedDownSourceEvent_eq_generatedPositiveSourceEvent]

/-- The physical inherited source event is Borel in the original source law. -/
theorem measurableSet_inheritedDownSourceEvent
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (alpha k q : ℕ) (hAlpha : alpha ≤ p.T)
    (w : Candidate p) (hq : 1 ≤ q) (hqQ : q ≤ AffineBatchDecoder.quota p)
    (j : Fin (M p)) (r : Fin p.T) (s : ℕ) (hsr : s ≤ r.val)
    (control0 : ContinuousLearningRows.TimeControl p)
    (Cell : Set (CompletePublicTable.IDArray p × GeneratedBootstrapRoundLaw.Past p r))
    (hCell : MeasurableSet Cell) (i : Fin (p.m - 1)) :
    MeasurableSet (inheritedDownSourceEvent (rate := rate) rewards C_star C_h alpha k q hAlpha
      w hq hqQ j r s hsr control0 Cell hCell i) := by
  rw [inheritedDownSourceEvent_eq_generatedPositiveSourceEvent]
  exact ReferenceGeneratedAffineHashHalf.measurableSet_generatedPositiveSourceEvent
    (rate := rate) rewards C_star C_h j r 0 i s hsr control0 w
    (ReferenceGeneratedInheritedDownPrefixMarker.inheritedDownMarkerRemainder
      rate rewards C_star C_h alpha k q hAlpha w hq hqQ j r s hsr control0
      Cell hCell i)
    (ReferenceGeneratedInheritedDownPrefixMarker.measurableSet_inheritedDownMarkerRemainder
      rate rewards C_star C_h alpha k q hAlpha w hq hqQ j r s hsr control0 Cell hCell i)

/-- The original-pair hash-one refinement is Borel in the original source
law, by Z's measurable hash-one event theorem. -/
theorem measurableSet_inheritedDownHashOneSourceEvent
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (alpha k q : ℕ) (hAlpha : alpha ≤ p.T)
    (w : Candidate p) (hq : 1 ≤ q) (hqQ : q ≤ AffineBatchDecoder.quota p)
    (j : Fin (M p)) (r : Fin p.T) (s : ℕ) (hsr : s ≤ r.val)
    (control0 : ContinuousLearningRows.TimeControl p)
    (Cell : Set (CompletePublicTable.IDArray p × GeneratedBootstrapRoundLaw.Past p r))
    (hCell : MeasurableSet Cell) (i : Fin (p.m - 1)) :
    MeasurableSet (inheritedDownHashOneSourceEvent (rate := rate) rewards C_star C_h
      alpha k q hAlpha w hq hqQ j r s hsr control0 Cell hCell i) := by
  rw [inheritedDownHashOneSourceEvent_eq_generatedPositiveHashOneSourceEvent]
  exact ReferenceGeneratedAffineHashHalf.measurableSet_generatedPositiveHashOneSourceEvent
    (rate := rate) rewards C_star C_h j r 0 i s hsr control0 w
    (ReferenceGeneratedInheritedDownPrefixMarker.inheritedDownMarkerRemainder
      rate rewards C_star C_h alpha k q hAlpha w hq hqQ j r s hsr control0
      Cell hCell i)
    (ReferenceGeneratedInheritedDownPrefixMarker.measurableSet_inheritedDownMarkerRemainder
      rate rewards C_star C_h alpha k q hAlpha w hq hqQ j r s hsr control0 Cell hCell i)

/-- Applying Z's one-round hash identity to the actual inherited event gives
the exact factor one half under the full original-source probability law. -/
theorem inheritedDownSourceEvent_hash_half
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (alpha k q : ℕ) (hAlpha : alpha ≤ p.T)
    (w : Candidate p) (hq : 1 ≤ q) (hqQ : q ≤ AffineBatchDecoder.quota p)
    (j : Fin (M p)) (r : Fin p.T) (s : ℕ) (hsr : s ≤ r.val)
    (control0 : ContinuousLearningRows.TimeControl p)
    (Cell : Set (CompletePublicTable.IDArray p × GeneratedBootstrapRoundLaw.Past p r))
    (hCell : MeasurableSet Cell) (i : Fin (p.m - 1)) :
    BootstrapPrivateRoundStreams.sourceInputLaw p
        (inheritedDownHashOneSourceEvent (rate := rate) rewards C_star C_h alpha k q hAlpha
          w hq hqQ j r s hsr control0 Cell hCell i) =
      ((1 : ℝ≥0∞) / 2) * BootstrapPrivateRoundStreams.sourceInputLaw p
        (inheritedDownSourceEvent (rate := rate) rewards C_star C_h alpha k q hAlpha
          w hq hqQ j r s hsr control0 Cell hCell i) := by
  let C := ReferenceGeneratedInheritedDownPrefixMarker.inheritedDownMarkerRemainder
    rate rewards C_star C_h alpha k q hAlpha w hq hqQ j r s hsr control0 Cell hCell i
  calc
    BootstrapPrivateRoundStreams.sourceInputLaw p
        (inheritedDownHashOneSourceEvent (rate := rate) rewards C_star C_h alpha k q hAlpha
          w hq hqQ j r s hsr control0 Cell hCell i) =
        BootstrapPrivateRoundStreams.sourceInputLaw p
          (ReferenceGeneratedAffineHashHalf.generatedPositiveHashOneSourceEvent
            (rate := rate) rewards C_star C_h j r 0 i s hsr control0 w C) := by
      rw [inheritedDownHashOneSourceEvent_eq_generatedPositiveHashOneSourceEvent]
    _ = ((1 : ℝ≥0∞) / 2) * BootstrapPrivateRoundStreams.sourceInputLaw p
          (ReferenceGeneratedAffineHashHalf.generatedPositiveSourceEvent
            (rate := rate) rewards C_star C_h j r 0 i s hsr control0 w C) :=
      ReferenceGeneratedAffineHashHalf.downGeneratedPositive_hash_half
        (rate := rate) rewards C_star C_h j r i s hsr control0 w C
        (ReferenceGeneratedInheritedDownPrefixMarker.measurableSet_inheritedDownMarkerRemainder
          rate rewards C_star C_h alpha k q hAlpha w hq hqQ j r s hsr control0 Cell hCell i)
    _ = ((1 : ℝ≥0∞) / 2) * BootstrapPrivateRoundStreams.sourceInputLaw p
          (inheritedDownSourceEvent (rate := rate) rewards C_star C_h alpha k q hAlpha
            w hq hqQ j r s hsr control0 Cell hCell i) := by
      rw [inheritedDownSourceEvent_eq_generatedPositiveSourceEvent]

/-- Any hash-one event member carries the actual good current test into the
same inherited first cohort, with the old equations still occupying their
original positions. The test's time, sample, and sent option are reconstructed
from the original source and the operational current input. -/
theorem inheritedDownHashOneSourceEvent_current_test
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (alpha k q : ℕ) (hAlpha : alpha ≤ p.T)
    (w : Candidate p) (hq : 1 ≤ q) (hqQ : q ≤ AffineBatchDecoder.quota p)
    (j : Fin (M p)) (r : Fin p.T) (s : ℕ) (hsr : s ≤ r.val)
    (control0 : ContinuousLearningRows.TimeControl p)
    (Cell : Set (CompletePublicTable.IDArray p × GeneratedBootstrapRoundLaw.Past p r))
    (hCell : MeasurableSet Cell) (i : Fin (p.m - 1))
    (z : SourceInput p)
    (hevent : z ∈ inheritedDownHashOneSourceEvent (rate := rate) rewards C_star C_h
      alpha k q hAlpha w hq hqQ j r s hsr control0 Cell hCell i) :
    ∃ (x : ReferenceGeneratedInheritedDownPrefixMarker.LaunchSource
        (rate := rate) rewards C_star C_h s (by omega))
      (test : ReferenceGeneratedDownBatchCalendar.ExecutedTest p),
        ReferenceSelectedAffinePairLaw.selector p r z = (j, some ((0, i) : Channel p)) ∧
        x.1 = z ∧
        ReferenceGeneratedInheritedDownPrefixMarker.inheritedDownMarker
          (rate := rate) rewards C_star C_h alpha k q w s (by omega) i x (r.val - s) ∧
        ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate
          ((ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
            rate rewards C_star C_h s (by omega) i x).2 ⟨r.val - s, by omega⟩) = some test ∧
        test.time = r ∧
        test.sample = (((z.1.2 j).2 r).2 (0, i)) ∧
        test.sent = ReferenceActiveAffinePositiveTest.downSent
          (ReferenceDownCompletedAmbiguityMeasurability.prefixInput s (r.val - s) (by omega)
            (ReferenceGeneratedDownBatchCalendar.generatedSourceRunInput
              rate rewards C_star C_h s (by omega) x)) ∧
        ReferenceGeneratedDownBatchCalendar.ExecutedTest.good w test ∧
        test ∈ ReferenceGeneratedInheritedDownCohort.generatedInheritedDownNewFirstTests
          rate rewards C_star C_h s (by omega) i x ∧
        ReferenceGeneratedInheritedDownPrefixMarker.inheritedDownPrefix
            (rate := rate) rewards C_star C_h s (by omega) i x (r.val - s) ++ [test] =
          (ReferenceGeneratedInheritedDownCohort.generatedInheritedDownFirstCohortTests
            rate rewards C_star C_h s (by omega) i x).take q := by
  classical
  change z ∈ inheritedDownSourceEvent (rate := rate) rewards C_star C_h alpha k q hAlpha
      w hq hqQ j r s hsr control0 Cell hCell i ∧
    AffineChannelLaw.affineHash (((z.1.2 j).2 r).2 (0, i)) w = 1 at hevent
  rcases hevent with ⟨hsource, hhash⟩
  rcases hsource with ⟨hselector, hcell, x, hx, hmarker, test, hcurrent, hsent⟩
  have hselectorX : ReferenceSelectedAffinePairLaw.selector p r x.1 =
      (j, some ((0, i) : Channel p)) := by
    rw [hx]
    exact hselector
  let input := ReferenceGeneratedInheritedDownPrefixMarker.inheritedDownCurrentInput
    (rate := rate) rewards C_star C_h j r s hsr control0 i x hselectorX
  let record := ReferenceGeneratedInheritedDownPrefixMarker.inheritedDownCurrentRecord
    (rate := rate) rewards C_star C_h j r s hsr control0 i x hselectorX
  have hsender := ReferenceGeneratedInheritedDownPrefixMarker.inheritedDownCurrent_senderIndex
    (rate := rate) rewards C_star C_h j r s hsr control0 i x hselectorX
  have hiff := ReferenceGeneratedDownPrefixPositiveHalf.executedTestOfRound_iff_downPositive
    (rate := rate) record i (by simpa [record, ReferenceGeneratedInheritedDownPrefixMarker.inheritedDownCurrentRecord] using hsender)
  have hsourceTest := ReferenceGeneratedInheritedDownPrefixMarker.inheritedDownCurrentTest_eq_sourcePrefixTest
    (rate := rate) rewards C_star C_h j r s hsr control0 i x hselectorX
  have htestRecord :
      ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate
        (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation record.input i) =
      some test := by
    change ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate
        (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation
          (ReferenceGeneratedInheritedDownPrefixMarker.inheritedDownCurrentInput
            (rate := rate) rewards C_star C_h j r s hsr control0 i x hselectorX) i) =
      some test
    rw [← hsourceTest]
    exact hcurrent
  have hphysical := ReferenceGeneratedInheritedDownPrefixMarker.inheritedDownCurrentPositiveSent_iff
    (rate := rate) rewards C_star C_h j r s hsr control0 i x hselectorX w
  have hpositive := (hphysical.mp ⟨test, hcurrent, hsent⟩).1
  have hcanonical := hiff.mpr (by
    simpa [record, ReferenceGeneratedInheritedDownPrefixMarker.inheritedDownCurrentRecord] using hpositive)
  have htestEq : test =
      ⟨record.input.time, (record.input.row.2 record.input.time).2 (0, i),
        ReferenceActiveAffinePositiveTest.downSent record.input⟩ :=
    Option.some.inj (htestRecord.symm.trans hcanonical)
  have hbranch : z ∈ ReferenceGeneratedAffineHashHalf.generatedLaunchBranch
      (rate := rate) rewards C_star C_h j r (0, i) s := by
    exact ⟨hselector, by rw [← hx]; exact x.property.1,
      by rw [← hx]; exact x.property.2⟩
  have hinput := inheritedDownCurrentInput_eq_generatedNextInput
    (rate := rate) rewards C_star C_h j r s hsr control0 i z x hx hselector hbranch
  have hfields := ReferenceGeneratedAffineHashHalf.generatedNextInputOfBranch_original_fields
    (rate := rate) rewards C_star C_h j r (0, i) s hsr control0 ⟨z, hbranch⟩
  rcases hfields with ⟨hrows, hselected, htimeInput, _hrewards⟩
  have hrecordInput : record.input = input := rfl
  have htimeInput' : input.time = r := by
    change (ReferenceGeneratedInheritedDownPrefixMarker.inheritedDownCurrentInput
      (rate := rate) rewards C_star C_h j r s hsr control0 i x hselectorX).time = r
    rw [hinput]
    exact htimeInput
  have htimeRecord : record.input.time = r := by
    rw [hrecordInput]
    exact htimeInput'
  have hindex : ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p z = j := by
    rw [ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex]
    exact congrArg Prod.fst hselector
  have hrow : input.row = z.1.2 j := by
    change input.rows input.selected = z.1.2 j
    rw [show input = ReferenceGeneratedAffineHashHalf.generatedNextInputOfBranch
        (rate := rate) rewards C_star C_h j r (0, i) s hsr control0 ⟨z, hbranch⟩ from hinput,
      hrows, hselected]
    change z.1.2 (ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p z) = z.1.2 j
    rw [hindex]
  have htime : test.time = r := by
    have htimeEq := congrArg ReferenceGeneratedDownBatchCalendar.ExecutedTest.time htestEq
    calc
      test.time = record.input.time := htimeEq
      _ = r := htimeRecord
  have hsample : test.sample = (((z.1.2 j).2 r).2
      ((0, i) : ContinuousLearningRows.Channel p)) := by
    have hsampleEq := congrArg ReferenceGeneratedDownBatchCalendar.ExecutedTest.sample htestEq
    rw [hsampleEq, hrecordInput, hrow, htimeInput']
  have hsentOperational : test.sent = ReferenceActiveAffinePositiveTest.downSent input := by
    simpa [record, ReferenceGeneratedInheritedDownPrefixMarker.inheritedDownCurrentRecord,
      input, ReferenceGeneratedInheritedDownPrefixMarker.inheritedDownCurrentInput] using
      congrArg ReferenceGeneratedDownBatchCalendar.ExecutedTest.sent htestEq
  have hsourceInput :=
    ReferenceGeneratedInheritedDownPrefixMarker.inheritedDownCurrentInput_eq_sourcePrefixInput
      (rate := rate) rewards C_star C_h j r s hsr control0 i x hselectorX
  have hsentFields : test.sent = ReferenceActiveAffinePositiveTest.downSent
      (ReferenceDownCompletedAmbiguityMeasurability.prefixInput s (r.val - s) (by omega)
        (ReferenceGeneratedDownBatchCalendar.generatedSourceRunInput
          rate rewards C_star C_h s (by omega) x)) := by
    calc
      test.sent = ReferenceActiveAffinePositiveTest.downSent input := hsentOperational
      _ = ReferenceActiveAffinePositiveTest.downSent
          (ReferenceDownCompletedAmbiguityMeasurability.prefixInput s (r.val - s) (by omega)
            (ReferenceGeneratedDownBatchCalendar.generatedSourceRunInput
              rate rewards C_star C_h s (by omega) x)) :=
        congrArg ReferenceActiveAffinePositiveTest.downSent hsourceInput
  have hgood : ReferenceGeneratedDownBatchCalendar.ExecutedTest.good w test := by
    change test.sent ≠ some w ∧ AffineChannelLaw.affineHash test.sample w = 1
    refine ⟨hsent, ?_⟩
    rw [hsample]
    exact hhash
  have hlen :
      (ReferenceGeneratedInheritedDownPrefixMarker.inheritedDownPrefix
        (rate := rate) rewards C_star C_h s (by omega) i x (r.val - s)).length = q - 1 :=
    hmarker.2.2.2.1
  have hnew := ReferenceGeneratedInheritedDownPrefixMarker.inheritedDownPrefix_current_mem
    (rate := rate) rewards C_star C_h s (by omega) i x (r.val - s) q (by omega)
    hq hqQ hlen test hcurrent
  have htake := ReferenceGeneratedInheritedDownPrefixMarker.inheritedDownPrefix_current_take
    (rate := rate) rewards C_star C_h s (by omega) i x (r.val - s) q (by omega)
    hq hqQ hlen test hcurrent
  exact ⟨x, test, hselector, hx, hmarker, hcurrent, htime, hsample,
    hsentFields, hgood, hnew, htake⟩

end Bandits.Support.ReferenceGeneratedInheritedDownSourceHalf

end
