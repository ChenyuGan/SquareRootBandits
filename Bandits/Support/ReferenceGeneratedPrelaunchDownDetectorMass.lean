/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedPrelaunchDownOccurrenceTail

import Mathlib.MeasureTheory.Measure.Basic

/-!
# Original-source prelaunch DOWN detector mass

This module proves Borel measurability of the existing actual hashed events and
detectors, then sums the existing fixed-pair affine half law over the original
private row index and the unique actual calendar occurrence.  The localized
identity is for the complete original source measure and an arbitrary
measurable strict-past cell.

Sources: `appendix_a_local_protocol.tex:111-153`,
`appendix_b_communication.tex:724-736`, `07_public_setup.tex:60-112,127-164`,
and `05_binary_transport.tex:20-42` in `sources/zip4/manuscript/`.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ReferenceGeneratedPrelaunchDownDetectorMass

open MeasureTheory ConstructorDimensions BootstrapDimensions
open Function
open ReferenceGeneratedPrelaunchDownOccurrenceTail
open ReferenceGeneratedPrelaunchDownCurrentPair
open ReferenceSelectedAffinePairLaw GeneratedBootstrapRoundLaw
open scoped Classical ENNReal

variable {p : ConstructorDimensions.Parameters}

private theorem measurable_originalDownSample (j : Fin (M p)) (i : Fin (p.m - 1))
    (r : Fin p.T) :
    Measurable (fun z : BootstrapPrivateRoundStreams.SourceInput p =>
      ((z.1.2 j).2 r).2 (0, i)) := by
  have hrows : Measurable
      (fun z : BootstrapPrivateRoundStreams.SourceInput p => z.1.2) :=
    measurable_snd.comp measurable_fst
  have hrow : Measurable
      (fun z : BootstrapPrivateRoundStreams.SourceInput p => z.1.2 j) :=
    (measurable_pi_apply j).comp hrows
  have hlearning : Measurable
      (fun z : BootstrapPrivateRoundStreams.SourceInput p => (z.1.2 j).2) :=
    measurable_snd.comp hrow
  have htime : Measurable
      (fun z : BootstrapPrivateRoundStreams.SourceInput p => (z.1.2 j).2 r) :=
    (measurable_pi_apply r).comp hlearning
  have hchannels : Measurable
      (fun z : BootstrapPrivateRoundStreams.SourceInput p => ((z.1.2 j).2 r).2) :=
    measurable_snd.comp htime
  exact (measurable_pi_apply (0, i)).comp hchannels

private theorem measurable_selectedDownSample (i : Fin (p.m - 1)) (r : Fin p.T) :
    Measurable (fun z : BootstrapPrivateRoundStreams.SourceInput p =>
      ((z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)).2 r).2 (0, i)) := by
  have hJ : Measurable (ActualInitializationPhysicalStep.selectedRowIndex p) := by
    change Measurable (BootstrapPrivateRoundStreams.sourceCoordinatorIndex p)
    exact BootstrapPrivateRoundStreams.measurable_sourceCoordinatorIndex p
  have hbranches : Measurable
      (fun v : Fin (M p) × BootstrapPrivateRoundStreams.SourceInput p =>
        ((v.2.1.2 v.1).2 r).2 (0, i)) := by
    apply measurable_from_prod_countable_right
    intro j
    exact measurable_originalDownSample j i r
  exact hbranches.comp (hJ.prodMk measurable_id)

/-- The actual original selected-row hash event is Borel. -/
theorem measurableSet_prelaunchDownHashedOccurrence
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (alpha k q : ℕ)
    (hAlpha : alpha ≤ p.T)
    (w : AffineChannelLaw.Word (AffineBatchDecoder.width p)) (r : Fin p.T) :
    MeasurableSet {z | prelaunchDownHashedOccurrence rate rewards C_star C_h i alpha k q
      hAlpha w z r} := by
  have hHash : MeasurableSet {z : BootstrapPrivateRoundStreams.SourceInput p |
      AffineChannelLaw.affineHash
        (((z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)).2 r).2 (0, i)) w = 1} := by
    have hHashEvent : MeasurableSet
        {s : AffineChannelLaw.Sample (AffineBatchDecoder.width p) |
          AffineChannelLaw.affineHash s w = 1} := MeasurableSet.of_discrete
    exact (measurable_selectedDownSample i r) hHashEvent
  change MeasurableSet {z | prelaunchDownOccurrence rate rewards C_star C_h i alpha k q
    hAlpha w z r ∧ AffineChannelLaw.affineHash
      (((z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)).2 r).2 (0, i)) w = 1}
  exact (measurableSet_prelaunchDownOccurrence rate rewards C_star C_h i alpha k q
    hAlpha w r).inter hHash

/-- Every detector level is Borel, including the level-zero birth readout. -/
theorem measurableSet_prelaunchDownDetector
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (alpha k : ℕ)
    (hAlpha : alpha ≤ p.T)
    (w : AffineChannelLaw.Word (AffineBatchDecoder.width p)) (q : ℕ) :
    MeasurableSet {z | z ∈ prelaunchDownDetector rate rewards C_star C_h i alpha k
      hAlpha w q} := by
  cases q with
  | zero =>
      rw [prelaunchDownDetector_zero]
      simpa only [Set.mem_ofPred_eq] using
        (ReferenceGeneratedPrelaunchDownPastFactor.measurableSet_birthAt
          rate rewards C_star C_h i alpha hAlpha k)
  | succ q =>
      rw [prelaunchDownDetector_succ]
      have hUnion := MeasurableSet.iUnion fun r =>
        measurableSet_prelaunchDownHashedOccurrence rate rewards C_star C_h i alpha k
          (q + 1) hAlpha w r
      rw [Set.ofPred_exists]
      exact hUnion

/-- The literal existential union of actual positive occurrences is Borel. -/
theorem measurableSet_prelaunchDownOccurrenceUnion
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (alpha k q : ℕ)
    (hAlpha : alpha ≤ p.T)
    (w : AffineChannelLaw.Word (AffineBatchDecoder.width p)) :
    MeasurableSet {z | ∃ r : Fin p.T,
      prelaunchDownOccurrence rate rewards C_star C_h i alpha k q hAlpha w z r} := by
  have hUnion := MeasurableSet.iUnion fun r =>
    measurableSet_prelaunchDownOccurrence rate rewards C_star C_h i alpha k q hAlpha w r
  rw [Set.ofPred_exists]
  exact hUnion

private theorem source_prelaunch_down_cell_half_at
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (alpha k q : ℕ)
    (hAlpha : alpha ≤ p.T) (w : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (a r : Fin p.T) (har : a.val ≤ r.val)
    (Cell : Set (CompletePublicTable.IDArray p × GeneratedBootstrapRoundLaw.Past p a))
    (hCell : MeasurableSet Cell) :
    BootstrapPrivateRoundStreams.sourceInputLaw p
      {z | ReferenceGeneratedPrelaunchDownCurrentPair.sourcePastView a z ∈ Cell ∧
        prelaunchDownHashedOccurrence rate rewards C_star C_h i alpha k q hAlpha w z r} =
      (1 : ENNReal) / 2 * BootstrapPrivateRoundStreams.sourceInputLaw p
        {z | ReferenceGeneratedPrelaunchDownCurrentPair.sourcePastView a z ∈ Cell ∧
          prelaunchDownOccurrence rate rewards C_star C_h i alpha k q hAlpha w z r} := by
  classical
  let CellAtR : Set (CompletePublicTable.IDArray p × GeneratedBootstrapRoundLaw.Past p r) :=
    {v | prelaunchPastRestriction a r har v ∈ Cell}
  have hCellAtR : MeasurableSet CellAtR :=
    hCell.preimage (measurable_prelaunchPastRestriction a r har)
  have hViewR : Measurable
      (ReferenceGeneratedPrelaunchDownCurrentPair.sourcePastView (p := p) r) :=
    ReferenceGeneratedPrelaunchDownCurrentPair.measurable_sourcePastView r
  have hPastR : MeasurableSet
      {z : BootstrapPrivateRoundStreams.SourceInput p |
        ReferenceGeneratedPrelaunchDownCurrentPair.sourcePastView r z ∈ CellAtR} :=
    hCellAtR.preimage hViewR
  have hJ : Measurable (ActualInitializationPhysicalStep.selectedRowIndex p) := by
    change Measurable (BootstrapPrivateRoundStreams.sourceCoordinatorIndex p)
    exact BootstrapPrivateRoundStreams.measurable_sourceCoordinatorIndex p
  let BaseStratum (j : Fin (M p)) : Set (BootstrapPrivateRoundStreams.SourceInput p) :=
    {z | ActualInitializationPhysicalStep.selectedRowIndex p z = j ∧
      ReferenceGeneratedPrelaunchDownCurrentPair.sourcePastView r z ∈ CellAtR ∧
      ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_past_indicator
        rate rewards C_star C_h z i alpha k q hAlpha r w ∧
      ReferenceGeneratedPrelaunchDownCurrentPair.A_r rate rewards C_star C_h z i r}
  let HashStratum (j : Fin (M p)) : Set (BootstrapPrivateRoundStreams.SourceInput p) :=
    {z | ActualInitializationPhysicalStep.selectedRowIndex p z = j ∧
      ReferenceGeneratedPrelaunchDownCurrentPair.sourcePastView r z ∈ CellAtR ∧
      ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_past_indicator
        rate rewards C_star C_h z i alpha k q hAlpha r w ∧
      ReferenceGeneratedPrelaunchDownCurrentPair.A_r rate rewards C_star C_h z i r ∧
      AffineChannelLaw.affineHash (((z.1.2 j).2 r).2 (0, i)) w = 1}
  have hJSet (j : Fin (M p)) : MeasurableSet
      {z : BootstrapPrivateRoundStreams.SourceInput p |
        ActualInitializationPhysicalStep.selectedRowIndex p z = j} :=
    measurableSet_eq_fun hJ measurable_const
  have hI : MeasurableSet
      {z : BootstrapPrivateRoundStreams.SourceInput p |
        ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_past_indicator
          rate rewards C_star C_h z i alpha k q hAlpha r w} :=
    ReferenceGeneratedPrelaunchDownPastFactor.measurableSet_source_prelaunch_down_past_indicator
      rate rewards C_star C_h i alpha k q hAlpha r w
  have hA : MeasurableSet
      {z : BootstrapPrivateRoundStreams.SourceInput p |
        ReferenceGeneratedPrelaunchDownCurrentPair.A_r rate rewards C_star C_h z i r} :=
    ReferenceGeneratedPrelaunchDownCurrentPair.measurableSet_A_r rate rewards C_star C_h i r
  have hBaseMeas (j : Fin (M p)) : MeasurableSet (BaseStratum j) := by
    exact (hJSet j).inter (hPastR.inter (hI.inter hA))
  have hHashMeas (j : Fin (M p)) : MeasurableSet (HashStratum j) := by
    have hHash : MeasurableSet
        {z : BootstrapPrivateRoundStreams.SourceInput p |
          AffineChannelLaw.affineHash (((z.1.2 j).2 r).2 (0, i)) w = 1} := by
      have hHashEvent : MeasurableSet
          {s : AffineChannelLaw.Sample (AffineBatchDecoder.width p) |
            AffineChannelLaw.affineHash s w = 1} := MeasurableSet.of_discrete
      exact (measurable_originalDownSample j i r) hHashEvent
    exact (hJSet j).inter (hPastR.inter (hI.inter (hA.inter hHash)))
  have hLocal (j : Fin (M p)) :
      BootstrapPrivateRoundStreams.sourceInputLaw p (HashStratum j) =
        (1 : ENNReal) / 2 * BootstrapPrivateRoundStreams.sourceInputLaw p (BaseStratum j) := by
    have h := ReferenceGeneratedPrelaunchDownCurrentPair.source_prelaunch_down_hash_half
      rate rewards C_star C_h i alpha k q hAlpha w j r CellAtR hCellAtR
    dsimp [HashStratum, BaseStratum, CellAtR,
      ReferenceGeneratedPrelaunchDownCurrentPair.sourcePastView,
      ReferenceGeneratedPrelaunchDownCurrentPair.A_r] at h ⊢
    exact h
  have hBaseUnion : (⋃ j : Fin (M p), BaseStratum j) =
      {z | ReferenceGeneratedPrelaunchDownCurrentPair.sourcePastView a z ∈ Cell ∧
        prelaunchDownOccurrence rate rewards C_star C_h i alpha k q hAlpha w z r} := by
    ext z
    constructor
    · intro hz
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hz
      rcases hj with ⟨hrow, hcell, hindicator, hpositive⟩
      have hrestriction := prelaunchPastRestriction_sourcePastView a r har z
      refine ⟨?_, ⟨hindicator, hpositive⟩⟩
      dsimp [CellAtR] at hcell
      rw [← hrestriction]
      exact hcell
    · rintro ⟨hcell, hocc⟩
      change ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_past_indicator
          rate rewards C_star C_h z i alpha k q hAlpha r w ∧
        ReferenceGeneratedPrelaunchDownCurrentPair.A_r rate rewards C_star C_h z i r at hocc
      refine Set.mem_iUnion.mpr ⟨ActualInitializationPhysicalStep.selectedRowIndex p z,
        ?_⟩
      refine ⟨rfl, ?_, hocc.1, hocc.2⟩
      dsimp [CellAtR]
      rw [prelaunchPastRestriction_sourcePastView a r har z]
      exact hcell
  have hHashUnion : (⋃ j : Fin (M p), HashStratum j) =
      {z | ReferenceGeneratedPrelaunchDownCurrentPair.sourcePastView a z ∈ Cell ∧
        prelaunchDownHashedOccurrence rate rewards C_star C_h i alpha k q hAlpha w z r} := by
    ext z
    constructor
    · intro hz
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hz
      rcases hj with ⟨hrow, hcell, hindicator, hpositive, hhash⟩
      have hrestriction := prelaunchPastRestriction_sourcePastView a r har z
      refine ⟨?_, ⟨⟨hindicator, hpositive⟩, ?_⟩⟩
      · dsimp [CellAtR] at hcell
        rw [← hrestriction]
        exact hcell
      · change AffineChannelLaw.affineHash
          (((z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)).2 r).2 (0, i)) w = 1
        rw [hrow]
        exact hhash
    · rintro ⟨hcell, hhit⟩
      rcases hhit with ⟨hocc, hhash⟩
      change ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_past_indicator
          rate rewards C_star C_h z i alpha k q hAlpha r w ∧
        ReferenceGeneratedPrelaunchDownCurrentPair.A_r rate rewards C_star C_h z i r at hocc
      refine Set.mem_iUnion.mpr ⟨ActualInitializationPhysicalStep.selectedRowIndex p z,
        ?_⟩
      refine ⟨rfl, ?_, hocc.1, hocc.2, ?_⟩
      · dsimp [CellAtR]
        rw [prelaunchPastRestriction_sourcePastView a r har z]
        exact hcell
      · simpa using hhash
  have hBaseDisjoint : Pairwise (Disjoint on BaseStratum) := by
    intro j j' hj
    change Disjoint (BaseStratum j) (BaseStratum j')
    rw [Set.disjoint_left]
    intro z hz hz'
    exact hj (hz.1.symm.trans hz'.1)
  have hHashDisjoint : Pairwise (Disjoint on HashStratum) := by
    intro j j' hj
    change Disjoint (HashStratum j) (HashStratum j')
    rw [Set.disjoint_left]
    intro z hz hz'
    exact hj (hz.1.symm.trans hz'.1)
  rw [← hHashUnion, measure_iUnion hHashDisjoint hHashMeas,
    ← hBaseUnion, measure_iUnion hBaseDisjoint hBaseMeas]
  simp_rw [hLocal]
  rw [ENNReal.tsum_mul_left]

/-- Exact source-mass identity for every positive detector level and every
measurable cell of the original strict past at `a ≤ alpha`. -/
theorem prelaunchDownDetector_source_mass_half
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (alpha k q : ℕ)
    (hAlpha : alpha ≤ p.T)
    (w : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (a : Fin p.T) (ha : a.val ≤ alpha)
    (Cell : Set (CompletePublicTable.IDArray p × GeneratedBootstrapRoundLaw.Past p a))
    (hCell : MeasurableSet Cell) (hq : 1 ≤ q) :
    BootstrapPrivateRoundStreams.sourceInputLaw p
      {z | ReferenceGeneratedPrelaunchDownCurrentPair.sourcePastView a z ∈ Cell ∧
        z ∈ prelaunchDownDetector rate rewards C_star C_h i alpha k hAlpha w q} =
      (1 : ENNReal) / 2 * BootstrapPrivateRoundStreams.sourceInputLaw p
        {z | ReferenceGeneratedPrelaunchDownCurrentPair.sourcePastView a z ∈ Cell ∧
          ∃ r : Fin p.T,
            prelaunchDownOccurrence rate rewards C_star C_h i alpha k q hAlpha w z r} := by
  classical
  have hB : MeasurableSet
      {z : BootstrapPrivateRoundStreams.SourceInput p |
        ReferenceGeneratedPrelaunchDownCurrentPair.sourcePastView a z ∈ Cell} :=
    hCell.preimage (ReferenceGeneratedPrelaunchDownCurrentPair.measurable_sourcePastView a)
  have hTimesHit (r : Fin p.T) : MeasurableSet
      {z : BootstrapPrivateRoundStreams.SourceInput p |
        ReferenceGeneratedPrelaunchDownCurrentPair.sourcePastView a z ∈ Cell ∧
          prelaunchDownHashedOccurrence rate rewards C_star C_h i alpha k q hAlpha w z r} :=
    hB.inter (measurableSet_prelaunchDownHashedOccurrence rate rewards C_star C_h i alpha k
      q hAlpha w r)
  have hTimesOcc (r : Fin p.T) : MeasurableSet
      {z : BootstrapPrivateRoundStreams.SourceInput p |
        ReferenceGeneratedPrelaunchDownCurrentPair.sourcePastView a z ∈ Cell ∧
          prelaunchDownOccurrence rate rewards C_star C_h i alpha k q hAlpha w z r} :=
    hB.inter (measurableSet_prelaunchDownOccurrence rate rewards C_star C_h i alpha k q
      hAlpha w r)
  have hTimesHitDisjoint : Pairwise (Disjoint on fun r : Fin p.T =>
      {z | ReferenceGeneratedPrelaunchDownCurrentPair.sourcePastView a z ∈ Cell ∧
        prelaunchDownHashedOccurrence rate rewards C_star C_h i alpha k q hAlpha w z r}) := by
    intro r s hrs
    change Disjoint
      {z | ReferenceGeneratedPrelaunchDownCurrentPair.sourcePastView a z ∈ Cell ∧
        prelaunchDownHashedOccurrence rate rewards C_star C_h i alpha k q hAlpha w z r}
      {z | ReferenceGeneratedPrelaunchDownCurrentPair.sourcePastView a z ∈ Cell ∧
        prelaunchDownHashedOccurrence rate rewards C_star C_h i alpha k q hAlpha w z s}
    rw [Set.disjoint_left]
    rintro z ⟨_, hhit⟩ ⟨_, hhit'⟩
    exact hrs (prelaunch_occurrence_unique rate rewards C_star C_h i alpha k q hAlpha w z r s
      hhit.1 hhit'.1)
  have hTimesOccDisjoint : Pairwise (Disjoint on fun r : Fin p.T =>
      {z | ReferenceGeneratedPrelaunchDownCurrentPair.sourcePastView a z ∈ Cell ∧
        prelaunchDownOccurrence rate rewards C_star C_h i alpha k q hAlpha w z r}) := by
    intro r s hrs
    change Disjoint
      {z | ReferenceGeneratedPrelaunchDownCurrentPair.sourcePastView a z ∈ Cell ∧
        prelaunchDownOccurrence rate rewards C_star C_h i alpha k q hAlpha w z r}
      {z | ReferenceGeneratedPrelaunchDownCurrentPair.sourcePastView a z ∈ Cell ∧
        prelaunchDownOccurrence rate rewards C_star C_h i alpha k q hAlpha w z s}
    rw [Set.disjoint_left]
    rintro z ⟨_, hocc⟩ ⟨_, hocc'⟩
    exact hrs (prelaunch_occurrence_unique rate rewards C_star C_h i alpha k q hAlpha w z r s
      hocc hocc')
  have hLocal (r : Fin p.T) (har : a.val ≤ r.val) :=
    source_prelaunch_down_cell_half_at rate rewards C_star C_h i alpha k q hAlpha w
      a r har Cell hCell
  have hBefore (r : Fin p.T) (hr : r.val < alpha) :
      BootstrapPrivateRoundStreams.sourceInputLaw p
        {z | ReferenceGeneratedPrelaunchDownCurrentPair.sourcePastView a z ∈ Cell ∧
          prelaunchDownHashedOccurrence rate rewards C_star C_h i alpha k q hAlpha w z r} = 0 ∧
      BootstrapPrivateRoundStreams.sourceInputLaw p
        {z | ReferenceGeneratedPrelaunchDownCurrentPair.sourcePastView a z ∈ Cell ∧
          prelaunchDownOccurrence rate rewards C_star C_h i alpha k q hAlpha w z r} = 0 := by
    have hOccEmpty : {z : BootstrapPrivateRoundStreams.SourceInput p |
        ReferenceGeneratedPrelaunchDownCurrentPair.sourcePastView a z ∈ Cell ∧
          prelaunchDownOccurrence rate rewards C_star C_h i alpha k q hAlpha w z r} = ∅ := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro _ hocc
      exact ReferenceGeneratedPrelaunchDownCurrentPair.past_indicator_false_of_lt
        rate rewards C_star C_h z i alpha k q hAlpha r w hr hocc.1
    have hHitEmpty : {z : BootstrapPrivateRoundStreams.SourceInput p |
        ReferenceGeneratedPrelaunchDownCurrentPair.sourcePastView a z ∈ Cell ∧
          prelaunchDownHashedOccurrence rate rewards C_star C_h i alpha k q hAlpha w z r} = ∅ := by
      ext z
      constructor
      · rintro ⟨hcell, hhit⟩
        have hmember : z ∈ {z | ReferenceGeneratedPrelaunchDownCurrentPair.sourcePastView a z ∈ Cell ∧
            prelaunchDownOccurrence rate rewards C_star C_h i alpha k q hAlpha w z r} :=
          ⟨hcell, hhit.1⟩
        rw [hOccEmpty] at hmember
        exact hmember.elim
      · simp
    exact ⟨by rw [hHitEmpty]; exact measure_empty,
      by rw [hOccEmpty]; exact measure_empty⟩
  have hOccurrenceUnion :
      {z : BootstrapPrivateRoundStreams.SourceInput p |
        ReferenceGeneratedPrelaunchDownCurrentPair.sourcePastView a z ∈ Cell ∧
          ∃ r : Fin p.T,
            prelaunchDownOccurrence rate rewards C_star C_h i alpha k q hAlpha w z r} =
        ⋃ r : Fin p.T, {z |
          ReferenceGeneratedPrelaunchDownCurrentPair.sourcePastView a z ∈ Cell ∧
            prelaunchDownOccurrence rate rewards C_star C_h i alpha k q hAlpha w z r} := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨hcell, r, hocc⟩
      exact ⟨r, hcell, hocc⟩
    · rintro ⟨r, hcell, hocc⟩
      exact ⟨hcell, r, hocc⟩
  have hDetectorUnion :
      {z : BootstrapPrivateRoundStreams.SourceInput p |
        ReferenceGeneratedPrelaunchDownCurrentPair.sourcePastView a z ∈ Cell ∧
          z ∈ prelaunchDownDetector rate rewards C_star C_h i alpha k hAlpha w q} =
        ⋃ r : Fin p.T, {z |
          ReferenceGeneratedPrelaunchDownCurrentPair.sourcePastView a z ∈ Cell ∧
            prelaunchDownHashedOccurrence rate rewards C_star C_h i alpha k q hAlpha w z r} := by
    cases q with
    | zero => omega
    | succ n =>
        rw [prelaunchDownDetector_succ]
        ext z
        simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
        constructor
        · rintro ⟨hcell, r, hhit⟩
          exact ⟨r, hcell, hhit⟩
        · rintro ⟨r, hcell, hhit⟩
          exact ⟨hcell, r, hhit⟩
  have hLevelLocal (r : Fin p.T) :
      BootstrapPrivateRoundStreams.sourceInputLaw p
        {z | ReferenceGeneratedPrelaunchDownCurrentPair.sourcePastView a z ∈ Cell ∧
          prelaunchDownHashedOccurrence rate rewards C_star C_h i alpha k q hAlpha w z r} =
      (1 : ENNReal) / 2 * BootstrapPrivateRoundStreams.sourceInputLaw p
        {z | ReferenceGeneratedPrelaunchDownCurrentPair.sourcePastView a z ∈ Cell ∧
          prelaunchDownOccurrence rate rewards C_star C_h i alpha k q hAlpha w z r} := by
    by_cases hr : r.val < alpha
    · obtain ⟨hHitZero, hOccZero⟩ := hBefore r hr
      rw [hHitZero, hOccZero]
      simp
    · exact hLocal r (ha.trans (Nat.le_of_not_gt hr))
  rw [hDetectorUnion, hOccurrenceUnion]
  rw [measure_iUnion hTimesHitDisjoint hTimesHit,
    measure_iUnion hTimesOccDisjoint hTimesOcc]
  simp_rw [hLevelLocal]
  rw [ENNReal.tsum_mul_left]

/-- The first occurrence level is bounded by half of the actual birth mass.
This is only the base half-step; it does not assert a later recurrence. -/
theorem prelaunchDownDetector_one_le_birth_mass_half
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (alpha k : ℕ)
    (hAlpha : alpha ≤ p.T)
    (w : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (a : Fin p.T) (ha : a.val ≤ alpha)
    (Cell : Set (CompletePublicTable.IDArray p × GeneratedBootstrapRoundLaw.Past p a))
    (hCell : MeasurableSet Cell) :
    BootstrapPrivateRoundStreams.sourceInputLaw p
      {z | ReferenceGeneratedPrelaunchDownCurrentPair.sourcePastView a z ∈ Cell ∧
        z ∈ prelaunchDownDetector rate rewards C_star C_h i alpha k hAlpha w 1} ≤
      (1 : ENNReal) / 2 * BootstrapPrivateRoundStreams.sourceInputLaw p
        {z | ReferenceGeneratedPrelaunchDownCurrentPair.sourcePastView a z ∈ Cell ∧
          z ∈ prelaunchDownDetector rate rewards C_star C_h i alpha k hAlpha w 0} := by
  have hIdentity := prelaunchDownDetector_source_mass_half rate rewards C_star C_h i alpha k 1
    hAlpha w a ha Cell hCell (by norm_num)
  have hSubset :
      {z : BootstrapPrivateRoundStreams.SourceInput p |
        ReferenceGeneratedPrelaunchDownCurrentPair.sourcePastView a z ∈ Cell ∧
          ∃ r : Fin p.T,
            prelaunchDownOccurrence rate rewards C_star C_h i alpha k 1 hAlpha w z r} ⊆
      {z | ReferenceGeneratedPrelaunchDownCurrentPair.sourcePastView a z ∈ Cell ∧
        z ∈ prelaunchDownDetector rate rewards C_star C_h i alpha k hAlpha w 0} := by
    rintro z ⟨hcell, r, hocc⟩
    exact ⟨hcell, prelaunch_occurrence_previous_one rate rewards C_star C_h i alpha k
      hAlpha w z r hocc⟩
  calc
    BootstrapPrivateRoundStreams.sourceInputLaw p
        {z | ReferenceGeneratedPrelaunchDownCurrentPair.sourcePastView a z ∈ Cell ∧
          z ∈ prelaunchDownDetector rate rewards C_star C_h i alpha k hAlpha w 1} =
        (1 : ENNReal) / 2 * BootstrapPrivateRoundStreams.sourceInputLaw p
          {z | ReferenceGeneratedPrelaunchDownCurrentPair.sourcePastView a z ∈ Cell ∧
            ∃ r : Fin p.T,
              prelaunchDownOccurrence rate rewards C_star C_h i alpha k 1 hAlpha w z r} := hIdentity
    _ ≤ (1 : ENNReal) / 2 * BootstrapPrivateRoundStreams.sourceInputLaw p
          {z | ReferenceGeneratedPrelaunchDownCurrentPair.sourcePastView a z ∈ Cell ∧
            z ∈ prelaunchDownDetector rate rewards C_star C_h i alpha k hAlpha w 0} := by
      exact mul_le_mul_of_nonneg_left (measure_mono hSubset) (by norm_num)

end Bandits.Support.ReferenceGeneratedPrelaunchDownDetectorMass

end
