/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.GeneratedBootstrapFiltration
public import Bandits.Support.GeneratedBootstrapRoundLaw
public import Bandits.Support.GeneratedBlockStartLaw
public import Bandits.Support.ReferenceInitializationCausality
public import Bandits.Support.ReferenceInitializationMeasurability
public import Bandits.Support.ReferenceInitializationPrefixInvariance

import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Causal block-boundary source prefixes

Sources: `sources/zip4/manuscript/appendix_b_communication.tex:376-379,
403-415,638-682` and `sources/zip4/manuscript/07_public_setup.tex:63-113`.

This module gives the literal finite-coordinate source prefix at each clipped
bootstrap boundary.  It is an analytical enlargement retaining original
round-scalar coordinates already sampled in the ambient product.  It does not
identify that enlargement with exposed player information or with the existing
round-analysis past.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.CompleteRowStoppingLaw
open Bandits.Support.CompletePublicTable
open Bandits.Support.PrivateSourceStreams
open Bandits.Support.GeneratedBootstrapRoundLaw
open Bandits.Support.ReferenceInitializationRun
open Bandits.Support.ReferencePrelaunchFollower
open scoped Classical

namespace Bandits.Support.GeneratedBootstrapBlockFiltrationRepair

private theorem analysisPastCalendarEntry (p : ConstructorDimensions.Parameters)
    (σ : Fin (p.T + 1))
    (row : CompleteRowStoppingLaw.CalendarArray p)
    (q : CompleteRowStoppingLaw.PastIndex p σ) :
    (CompleteRowStoppingLaw.calendarSplitEquiv p σ row).1 q = row q.1 := rfl

private theorem analysisPastPlayerScalar (p : ConstructorDimensions.Parameters) (t : Fin p.T)
    (x : ExtendedPrivateCoordinates p)
    (q : PrivateRoundFreshness.PastRoundLabel p t) :
    (PrivateRoundFreshness.extendedPrivateRoundSplitEquiv p t x).1.2.1 q =
      x.2.1 (PrivateRoundFreshness.pastRoundLabelUnderlying p t q) := rfl

private theorem analysisPastPrivateBlockProfile (p : ConstructorDimensions.Parameters)
    (t : Fin p.T) (x : ExtendedPrivateCoordinates p) (q : Fin (n_boot p)) :
    (PrivateRoundFreshness.extendedPrivateRoundSplitEquiv p t x).1.1.1 q =
      x.1.1 q := rfl

abbrev Parameters := ConstructorDimensions.Parameters

/-- The original complete-row/private carrier used by `originalLaw`. -/
abbrev Coordinates (p : Parameters) := GeneratedBootstrapRoundLaw.Coordinates p

/-- Calendar entries already present at source elapsed time `elapsed p r`. -/
abbrev CalendarPrefix (p : Parameters) (r : ℕ) :=
  {t : Fin p.T // t.val < ReferenceInitializationRun.elapsed p r} →
    CompleteRowStoppingLaw.CalendarEntry p

/-- Raw follower block-triple profiles at labels strictly before `r`. -/
abbrev BlockPrefix (p : Parameters) (r : ℕ) :=
  {q : Fin (n_boot p) // q.val < r} →
    (Fin (p.m - 1) → PrivateSourceStreams.BlockScalars)

/-- Raw coordinator target scalars at labels strictly before `r`. -/
abbrev TargetPrefix (p : Parameters) (r : ℕ) :=
  {q : Fin (n_boot p) // q.val < r} → BootstrapPrivateRoundStreams.Scalar

/-- Original player/round scalars whose calendar labels precede the boundary. -/
abbrev RoundScalarPrefix (p : Parameters) (r : ℕ) :=
  {label : BootstrapPrivateRoundStreams.PlayerRoundLabel p //
    label.2.val < ReferenceInitializationRun.elapsed p r} →
      BootstrapPrivateRoundStreams.Scalar

/-- Literal source prefix, grouped in manuscript order: complete calendar
entries, follower block triples, coordinator targets, then original
player-round scalars. -/
abbrev SourcePrefix (p : Parameters) (r : ℕ) :=
  CalendarPrefix p r ×
    (BlockPrefix p r × (TargetPrefix p r × RoundScalarPrefix p r))

/-- Restrict the actual complete row to calendar labels before the clipped
boundary. -/
def calendarPrefix (p : Parameters) (r : ℕ)
    (e : Coordinates p) : CalendarPrefix p r :=
  fun t => ((fun u => e.1.1 u t.1), e.1.2 t.1)

/-- Restrict the original raw follower/block triple array to labels before
the boundary. -/
def blockPrefix (p : Parameters) (r : ℕ)
    (e : Coordinates p) : BlockPrefix p r :=
  fun q => e.2.1.1 q.1

/-- Restrict the original target-scalar array to labels before the boundary. -/
def targetPrefix (p : Parameters) (r : ℕ)
    (e : Coordinates p) : TargetPrefix p r :=
  fun q => e.2.2.2 q.1

/-- Restrict, without resampling, the original player/round scalar array to
round labels before the boundary. -/
def roundScalarPrefix (p : Parameters) (r : ℕ)
    (e : Coordinates p) : RoundScalarPrefix p r :=
  fun label => e.2.2.1 label.1

/-- The exact source-prefix projection.  The separate coordinator `J` scalar
is deliberately absent from the prefix and remains in the ambient law. -/
def sourcePrefix (p : Parameters) (r : ℕ) (e : Coordinates p) :
    SourcePrefix p r :=
  (calendarPrefix p r e,
    (blockPrefix p r e, (targetPrefix p r e, roundScalarPrefix p r e)))

theorem measurable_calendarPrefix (p : Parameters) (r : ℕ) :
    Measurable (calendarPrefix p r) := by
  apply measurable_pi_iff.mpr
  intro t
  have hforward : Measurable (fun e : Coordinates p =>
      fun u : Fin (A_id p) => e.1.1 u t.1) := by
    apply measurable_pi_iff.mpr
    intro u
    exact (measurable_pi_apply t.1).comp
      ((measurable_pi_apply u).comp
        (measurable_fst.comp measurable_fst))
  have hcontrol : Measurable (fun e : Coordinates p => e.1.2 t.1) := by
    exact (measurable_pi_apply t.1).comp
      (measurable_snd.comp measurable_fst)
  exact hforward.prodMk hcontrol

theorem measurable_blockPrefix (p : Parameters) (r : ℕ) :
    Measurable (blockPrefix p r) := by
  apply measurable_pi_iff.mpr
  intro q
  exact (measurable_pi_apply q.1).comp
    (measurable_fst.comp (measurable_fst.comp measurable_snd))

theorem measurable_targetPrefix (p : Parameters) (r : ℕ) :
    Measurable (targetPrefix p r) := by
  apply measurable_pi_iff.mpr
  intro q
  exact (measurable_pi_apply q.1).comp
    (measurable_snd.comp (measurable_snd.comp measurable_snd))

theorem measurable_roundScalarPrefix (p : Parameters) (r : ℕ) :
    Measurable (roundScalarPrefix p r) := by
  apply measurable_pi_iff.mpr
  intro label
  exact (measurable_pi_apply label.1).comp
    (measurable_fst.comp (measurable_snd.comp measurable_snd))

/-- The source-prefix projection is measurable for the literal product
measurable spaces on the finite subtype-indexed carriers. -/
theorem measurable_sourcePrefix (p : Parameters) (r : ℕ) :
    Measurable (sourcePrefix p r) := by
  exact (measurable_calendarPrefix p r).prodMk
    ((measurable_blockPrefix p r).prodMk
      ((measurable_targetPrefix p r).prodMk (measurable_roundScalarPrefix p r)))

/-- Restriction of all four prefix factors from a later block boundary to an
earlier one. -/
def sourcePrefixRestrict (p : Parameters) (r s : ℕ) (hrs : r ≤ s) :
    SourcePrefix p s → SourcePrefix p r := fun a =>
  ((fun t => a.1 ⟨t.1, Nat.lt_of_lt_of_le t.2
      (ReferenceInitializationRun.elapsed_mono p hrs)⟩),
    ((fun q => a.2.1 ⟨q.1, Nat.lt_of_lt_of_le q.2 hrs⟩),
      ((fun q => a.2.2.1 ⟨q.1, Nat.lt_of_lt_of_le q.2 hrs⟩),
        (fun label => a.2.2.2 ⟨label.1,
          Nat.lt_of_lt_of_le label.2 (ReferenceInitializationRun.elapsed_mono p hrs)⟩))))

theorem measurable_sourcePrefixRestrict (p : Parameters) (r s : ℕ) (hrs : r ≤ s) :
    Measurable (sourcePrefixRestrict p r s hrs) := by
  have hcal : Measurable (fun a : SourcePrefix p s =>
      fun t : {t : Fin p.T // t.val < ReferenceInitializationRun.elapsed p r} =>
        a.1 ⟨t.1, Nat.lt_of_lt_of_le t.2
          (ReferenceInitializationRun.elapsed_mono p hrs)⟩) := by
    fun_prop
  have hblock : Measurable (fun a : SourcePrefix p s =>
      fun q : {q : Fin (n_boot p) // q.val < r} =>
        a.2.1 ⟨q.1, Nat.lt_of_lt_of_le q.2 hrs⟩) := by
    fun_prop
  have htarget : Measurable (fun a : SourcePrefix p s =>
      fun q : {q : Fin (n_boot p) // q.val < r} =>
        a.2.2.1 ⟨q.1, Nat.lt_of_lt_of_le q.2 hrs⟩) := by
    fun_prop
  have hround : Measurable (fun a : SourcePrefix p s =>
      fun label : {label : BootstrapPrivateRoundStreams.PlayerRoundLabel p //
          label.2.val < ReferenceInitializationRun.elapsed p r} =>
        a.2.2.2 ⟨label.1,
          Nat.lt_of_lt_of_le label.2 (ReferenceInitializationRun.elapsed_mono p hrs)⟩) := by
    fun_prop
  exact hcal.prodMk (hblock.prodMk (htarget.prodMk hround))

theorem sourcePrefixRestrict_sourcePrefix (p : Parameters) (r s : ℕ) (hrs : r ≤ s)
    (e : Coordinates p) :
    sourcePrefixRestrict p r s hrs (sourcePrefix p s e) = sourcePrefix p r e := by
  apply Prod.ext
  · funext t
    rfl
  · apply Prod.ext
    · funext q
      rfl
    · apply Prod.ext
      · funext q
        rfl
      · funext label
        rfl

/-- The source-prefix sigma algebra at a natural block index. -/
@[instance_reducible] def boundarySigma (p : Parameters) (r : ℕ) : MeasurableSpace (Coordinates p) :=
  MeasurableSpace.comap (sourcePrefix p r) inferInstance

/-- Nat-indexed causal source-prefix filtration on the existing original law
carrier. -/
def boundaryFiltration (p : Parameters) :
    Filtration ℕ (inferInstance : MeasurableSpace (Coordinates p)) where
  seq := boundarySigma p
  mono' := by
    intro r s hrs
    exact MeasurableSpace.comap_le_comap_of_eq_comp
      (sourcePrefixRestrict p r s hrs)
      (measurable_sourcePrefixRestrict p r s hrs)
      (by
        funext e
        exact (sourcePrefixRestrict_sourcePrefix p r s hrs e).symm)
  le' := by
    intro r
    exact (measurable_sourcePrefix p r).comap_le

theorem boundaryFiltration_le_ambient (p : Parameters) (r : ℕ) :
    boundaryFiltration p r ≤ (inferInstance : MeasurableSpace (Coordinates p)) :=
  (measurable_sourcePrefix p r).comap_le

theorem boundaryFiltration_initial (p : Parameters) :
    boundaryFiltration p 0 = ⊥ := by
  let e₀ : Coordinates p := Classical.choice (nonempty_of_isProbabilityMeasure
    (GeneratedBootstrapRoundLaw.originalLaw p))
  have hconst : sourcePrefix p 0 = fun _ : Coordinates p => sourcePrefix p 0 e₀ := by
    funext e
    apply Prod.ext
    · funext t
      have ht := t.2
      simp [ReferenceInitializationRun.elapsed] at ht
    · apply Prod.ext
      · funext q
        have hq := q.2
        simp at hq
      · apply Prod.ext
        · funext q
          have hq := q.2
          simp at hq
        · funext label
          have hl := label.2
          simp [ReferenceInitializationRun.elapsed] at hl
  change MeasurableSpace.comap (sourcePrefix p 0) inferInstance = ⊥
  rw [hconst, MeasurableSpace.comap_const]

/-- The clipped calendar coordinate has reached the complete horizon at the
last bootstrap boundary. -/
theorem elapsed_eq_horizon_of_block_le (p : Parameters) (r : ℕ)
    (hr : n_boot p ≤ r) :
    ReferenceInitializationRun.elapsed p r = p.T := by
  have hlow : p.T ≤ ReferenceInitializationRun.elapsed p r := by
    rw [← ReferenceInitializationRun.elapsed_all_blocks p]
    exact ReferenceInitializationRun.elapsed_mono p hr
  exact le_antisymm (ReferenceInitializationRun.elapsed_le_T p r) hlow

/-- Extend a full boundary prefix to a later index. Since every block label
and calendar label is already present, this only changes subtype proofs. -/
def sourcePrefixExtendAfterHorizon (p : Parameters) (r : ℕ)
    (hr : n_boot p ≤ r) : SourcePrefix p (n_boot p) → SourcePrefix p r := fun a =>
  ((fun t => a.1 ⟨t.1, by
      have he : ReferenceInitializationRun.elapsed p r =
          ReferenceInitializationRun.elapsed p (n_boot p) := by
        rw [elapsed_eq_horizon_of_block_le p r hr,
          ReferenceInitializationRun.elapsed_all_blocks]
      exact Nat.lt_of_lt_of_eq t.2 he⟩),
    ((fun q => a.2.1 ⟨q.1, q.1.isLt⟩),
      ((fun q => a.2.2.1 ⟨q.1, q.1.isLt⟩),
        (fun label => a.2.2.2 ⟨label.1, by
          have he : ReferenceInitializationRun.elapsed p r =
              ReferenceInitializationRun.elapsed p (n_boot p) := by
            rw [elapsed_eq_horizon_of_block_le p r hr,
              ReferenceInitializationRun.elapsed_all_blocks]
          exact Nat.lt_of_lt_of_eq label.2 he⟩))))

theorem measurable_sourcePrefixExtendAfterHorizon (p : Parameters) (r : ℕ)
    (hr : n_boot p ≤ r) :
    Measurable (sourcePrefixExtendAfterHorizon p r hr) := by
  have he : ReferenceInitializationRun.elapsed p r =
      ReferenceInitializationRun.elapsed p (n_boot p) := by
    rw [elapsed_eq_horizon_of_block_le p r hr,
      ReferenceInitializationRun.elapsed_all_blocks]
  have hcal : Measurable (fun a : SourcePrefix p (n_boot p) =>
      fun t : {t : Fin p.T // t.val < ReferenceInitializationRun.elapsed p r} =>
        a.1 ⟨t.1, Nat.lt_of_lt_of_eq t.2 he⟩) := by
    apply measurable_pi_iff.mpr
    intro t
    exact (measurable_pi_apply
      (⟨t.1, Nat.lt_of_lt_of_eq t.2 he⟩ :
        {t : Fin p.T // t.val < ReferenceInitializationRun.elapsed p (n_boot p)})).comp
      measurable_fst
  have hblock : Measurable (fun a : SourcePrefix p (n_boot p) =>
      fun q : {q : Fin (n_boot p) // q.val < r} =>
        a.2.1 ⟨q.1, q.1.isLt⟩) := by
    apply measurable_pi_iff.mpr
    intro q
    exact (measurable_pi_apply
      (⟨q.1, q.1.isLt⟩ : {q : Fin (n_boot p) // q.val < n_boot p})).comp
        (measurable_fst.comp measurable_snd)
  have htarget : Measurable (fun a : SourcePrefix p (n_boot p) =>
      fun q : {q : Fin (n_boot p) // q.val < r} =>
        a.2.2.1 ⟨q.1, q.1.isLt⟩) := by
    apply measurable_pi_iff.mpr
    intro q
    exact (measurable_pi_apply
      (⟨q.1, q.1.isLt⟩ : {q : Fin (n_boot p) // q.val < n_boot p})).comp
        (measurable_fst.comp (measurable_snd.comp measurable_snd))
  have hround : Measurable (fun a : SourcePrefix p (n_boot p) =>
      fun label : {label : BootstrapPrivateRoundStreams.PlayerRoundLabel p //
          label.2.val < ReferenceInitializationRun.elapsed p r} =>
        a.2.2.2 ⟨label.1, Nat.lt_of_lt_of_eq label.2 he⟩) := by
    apply measurable_pi_iff.mpr
    intro label
    exact (measurable_pi_apply
      (⟨label.1, Nat.lt_of_lt_of_eq label.2 he⟩ :
        {label : BootstrapPrivateRoundStreams.PlayerRoundLabel p //
          label.2.val < ReferenceInitializationRun.elapsed p (n_boot p)})).comp
        (measurable_snd.comp (measurable_snd.comp measurable_snd))
  exact hcal.prodMk (hblock.prodMk (htarget.prodMk hround))

theorem sourcePrefixExtendAfterHorizon_sourcePrefix (p : Parameters) (r : ℕ)
    (hr : n_boot p ≤ r) (e : Coordinates p) :
    sourcePrefixExtendAfterHorizon p r hr (sourcePrefix p (n_boot p) e) =
      sourcePrefix p r e := by
  apply Prod.ext
  · funext t
    simp [sourcePrefixExtendAfterHorizon, sourcePrefix, calendarPrefix]
  · apply Prod.ext
    · funext q
      rfl
    · apply Prod.ext
      · funext q
        rfl
      · funext label
        rfl

/-- The Nat-indexed boundary filtration freezes at the full calendar
boundary. -/
theorem boundaryFiltration_eq_of_block_le (p : Parameters) (r : ℕ)
    (hr : n_boot p ≤ r) :
    boundaryFiltration p r = boundaryFiltration p (n_boot p) := by
  apply le_antisymm
  · change MeasurableSpace.comap (sourcePrefix p r) inferInstance ≤
      MeasurableSpace.comap (sourcePrefix p (n_boot p)) inferInstance
    exact MeasurableSpace.comap_le_comap_of_eq_comp
      (sourcePrefixExtendAfterHorizon p r hr)
      (measurable_sourcePrefixExtendAfterHorizon p r hr)
      (by
        funext e
        exact (sourcePrefixExtendAfterHorizon_sourcePrefix p r hr e).symm)
  · change MeasurableSpace.comap (sourcePrefix p (n_boot p)) inferInstance ≤
      MeasurableSpace.comap (sourcePrefix p r) inferInstance
    exact MeasurableSpace.comap_le_comap_of_eq_comp
      (sourcePrefixRestrict p (n_boot p) r hr)
      (measurable_sourcePrefixRestrict p (n_boot p) r hr)
      (by
        funext e
        exact sourcePrefixRestrict_sourcePrefix p (n_boot p) r hr e)

/-- Re-express the literal block-boundary prefix using the accepted strict
round past. The past retains all raw block profiles and targets; this adapter
restricts those arrays to the boundary's block labels. -/
def sourcePrefixFromAnalysisPast (p : Parameters) (r : ℕ)
    (hElapsed : ReferenceInitializationRun.elapsed p r < p.T) :
    GeneratedBootstrapRoundLaw.Past p
      ⟨ReferenceInitializationRun.elapsed p r, hElapsed⟩ → SourcePrefix p r := fun w =>
  ((fun t => w.1 ⟨t.1, t.2⟩),
    ((fun q => w.2.1.1 q.1),
      ((fun q => w.2.2.2 q.1),
        (fun label => w.2.2.1
          ⟨⟨label.1,
            Fin.le_iff_val_le_val.mpr (Nat.le_of_lt label.2)⟩,
            Fin.lt_def.mpr label.2⟩))))

theorem measurable_sourcePrefixFromAnalysisPast (p : Parameters) (r : ℕ)
    (hElapsed : ReferenceInitializationRun.elapsed p r < p.T) :
    Measurable (sourcePrefixFromAnalysisPast p r hElapsed) := by
  have hcalendar : Measurable (fun w : GeneratedBootstrapRoundLaw.Past p
      ⟨ReferenceInitializationRun.elapsed p r, hElapsed⟩ =>
        fun t : {t : Fin p.T // t.val < ReferenceInitializationRun.elapsed p r} =>
          w.1 ⟨t.1, t.2⟩) := by
    apply measurable_pi_iff.mpr
    intro t
    exact (measurable_pi_apply
      (⟨t.1, t.2⟩ : CompleteRowStoppingLaw.PastIndex p
        (GeneratedBootstrapRoundLaw.cutoff p
          ⟨ReferenceInitializationRun.elapsed p r, hElapsed⟩))).comp measurable_fst
  have hblock : Measurable (fun w : GeneratedBootstrapRoundLaw.Past p
      ⟨ReferenceInitializationRun.elapsed p r, hElapsed⟩ =>
        fun q : {q : Fin (n_boot p) // q.val < r} => w.2.1.1 q.1) := by
    apply measurable_pi_iff.mpr
    intro q
    exact (measurable_pi_apply q.1).comp
      (measurable_fst.comp (measurable_fst.comp measurable_snd))
  have htarget : Measurable (fun w : GeneratedBootstrapRoundLaw.Past p
      ⟨ReferenceInitializationRun.elapsed p r, hElapsed⟩ =>
        fun q : {q : Fin (n_boot p) // q.val < r} => w.2.2.2 q.1) := by
    apply measurable_pi_iff.mpr
    intro q
    exact (measurable_pi_apply q.1).comp
      (measurable_snd.comp (measurable_snd.comp measurable_snd))
  have hround : Measurable (fun w : GeneratedBootstrapRoundLaw.Past p
      ⟨ReferenceInitializationRun.elapsed p r, hElapsed⟩ =>
        fun label : {label : BootstrapPrivateRoundStreams.PlayerRoundLabel p //
            label.2.val < ReferenceInitializationRun.elapsed p r} =>
          w.2.2.1
            ⟨⟨label.1,
              Fin.le_iff_val_le_val.mpr (Nat.le_of_lt label.2)⟩,
              Fin.lt_def.mpr label.2⟩) := by
    apply measurable_pi_iff.mpr
    intro label
    exact (measurable_pi_apply
      (⟨⟨label.1, Fin.le_iff_val_le_val.mpr (Nat.le_of_lt label.2)⟩,
        Fin.lt_def.mpr label.2⟩ :
          PrivateRoundFreshness.PastRoundLabel p
            ⟨ReferenceInitializationRun.elapsed p r, hElapsed⟩)).comp
      (measurable_fst.comp (measurable_snd.comp measurable_snd))
  exact hcalendar.prodMk (hblock.prodMk (htarget.prodMk hround))

theorem sourcePrefixFromAnalysisPast_past (p : Parameters) (r : ℕ)
    (hElapsed : ReferenceInitializationRun.elapsed p r < p.T) (e : Coordinates p) :
    sourcePrefixFromAnalysisPast p r hElapsed
      (GeneratedBootstrapRoundLaw.past p
        ⟨ReferenceInitializationRun.elapsed p r, hElapsed⟩ e) =
      sourcePrefix p r e := by
  apply Prod.ext
  · funext t
    simp only [sourcePrefixFromAnalysisPast, sourcePrefix, calendarPrefix,
      GeneratedBootstrapRoundLaw.past]
    rw [analysisPastCalendarEntry]
    rfl
  · apply Prod.ext
    · funext q
      change (PrivateRoundFreshness.extendedPrivateRoundSplitEquiv
        p ⟨ReferenceInitializationRun.elapsed p r, hElapsed⟩ e.2).1.1.1 q.1 = _
      rw [analysisPastPrivateBlockProfile]
      rfl
    · apply Prod.ext
      · funext q
        rfl
      · funext label
        change (PrivateRoundFreshness.extendedPrivateRoundSplitEquiv
          p ⟨ReferenceInitializationRun.elapsed p r, hElapsed⟩ e.2).1.2.1 _ = _
        rw [analysisPastPlayerScalar]
        rfl

/-- At the calendar elapsed boundary, the source-prefix sigma algebra is
contained in the existing round-analysis past. -/
theorem boundaryFiltration_le_analysis_at_elapsed (p : Parameters) (r : ℕ) :
    boundaryFiltration p r ≤
      GeneratedBootstrapFiltration.analysisFiltration p
        (ReferenceInitializationRun.elapsed p r) := by
  by_cases hElapsed : ReferenceInitializationRun.elapsed p r < p.T
  · let t : Fin p.T := ⟨ReferenceInitializationRun.elapsed p r, hElapsed⟩
    rw [GeneratedBootstrapFiltration.analysisFiltration_at p t]
    change MeasurableSpace.comap (sourcePrefix p r) inferInstance ≤
      MeasurableSpace.comap (GeneratedBootstrapRoundLaw.past p t) inferInstance
    exact MeasurableSpace.comap_le_comap_of_eq_comp
      (sourcePrefixFromAnalysisPast p r hElapsed)
      (measurable_sourcePrefixFromAnalysisPast p r hElapsed)
      (by
        funext e
        exact (sourcePrefixFromAnalysisPast_past p r hElapsed e).symm)
  · rw [GeneratedBootstrapFiltration.analysisFiltration_eq_top_of_horizon]
    · exact boundaryFiltration_le_ambient p r
    · exact Nat.le_of_not_gt hElapsed

/-- The literal prefix input adapter: only the selected ID array, rounded
reward table, numerical constants and learning rate are fixed parameters. -/
def referenceInput (p : Parameters) (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (e : Coordinates p) :
    ReferenceInitializationRun.Input p :=
  GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e

/-- Equality of the literal prefix implies equality of exactly the original
coordinates read through boundary `r`. -/
theorem runPrefixInputEq_of_sourcePrefix_eq (p : Parameters) (r : ℕ)
    (ids : CompletePublicTable.IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (x y : Coordinates p) (h : sourcePrefix p r x = sourcePrefix p r y) :
    ReferenceInitializationCausality.runPrefixInputEq
      (referenceInput p ids rewards C_star C_h eta x)
      (referenceInput p ids rewards C_star C_h eta y) r := by
  have hrow := congrArg Prod.fst h
  have hblocks := congrArg (fun z : SourcePrefix p r => z.2.1) h
  have htargets := congrArg (fun z : SourcePrefix p r => z.2.2.1) h
  have hrounds := congrArg (fun z : SourcePrefix p r => z.2.2.2) h
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · intro t ht
    have he := congrFun hrow ⟨t, ht⟩
    exact ⟨fun u => congrFun (congrArg Prod.fst he) u,
      congrArg Prod.snd he⟩
  · intro q hq j
    exact congrFun (congrFun hblocks ⟨q, hq⟩) j
  · intro q hq
    exact congrFun htargets ⟨q, hq⟩
  · intro i t ht
    exact congrFun hrounds ⟨(i, t), ht⟩

/-- Measurable section completing only coordinates omitted by a prefix with
fixed entries from one original ambient point. It is used to prove
factorization; it does not change the run's input carrier or law. -/
def completeSourcePrefix (p : Parameters) (r : ℕ) (e₀ : Coordinates p)
    (a : SourcePrefix p r) : Coordinates p :=
  (((fun u t => if ht : t.val < ReferenceInitializationRun.elapsed p r then
        (a.1 ⟨t, ht⟩).1 u else e₀.1.1 u t),
      (fun t => if ht : t.val < ReferenceInitializationRun.elapsed p r then
        (a.1 ⟨t, ht⟩).2 else e₀.1.2 t)),
    ((fun q => if hq : q.val < r then a.2.1 ⟨q, hq⟩ else e₀.2.1.1 q,
      e₀.2.1.2),
      (fun label => if ht : label.2.val < ReferenceInitializationRun.elapsed p r then
        a.2.2.2 ⟨label, ht⟩ else e₀.2.2.1 label,
        fun q => if hq : q.val < r then a.2.2.1 ⟨q, hq⟩ else e₀.2.2.2 q)))

theorem measurable_completeSourcePrefix (p : Parameters) (r : ℕ) (e₀ : Coordinates p) :
    Measurable (completeSourcePrefix p r e₀) := by
  have hforward : Measurable (fun a : SourcePrefix p r =>
      fun u t => if ht : t.val < ReferenceInitializationRun.elapsed p r then
        (a.1 ⟨t, ht⟩).1 u else e₀.1.1 u t) := by
    fun_prop
  have hlearning : Measurable (fun a : SourcePrefix p r =>
      fun t => if ht : t.val < ReferenceInitializationRun.elapsed p r then
        (a.1 ⟨t, ht⟩).2 else e₀.1.2 t) := by
    fun_prop
  have hrow := hforward.prodMk hlearning
  have hblocks : Measurable (fun a : SourcePrefix p r =>
      fun q : Fin (n_boot p) => if hq : q.val < r then a.2.1 ⟨q, hq⟩ else e₀.2.1.1 q) := by
    fun_prop
  have hrounds : Measurable (fun a : SourcePrefix p r =>
      fun label : BootstrapPrivateRoundStreams.PlayerRoundLabel p =>
        if ht : label.2.val < ReferenceInitializationRun.elapsed p r then
          a.2.2.2 ⟨label, ht⟩ else e₀.2.2.1 label) := by
    fun_prop
  have htargets : Measurable (fun a : SourcePrefix p r =>
      fun q : Fin (n_boot p) => if hq : q.val < r then a.2.2.1 ⟨q, hq⟩ else e₀.2.2.2 q) := by
    fun_prop
  exact hrow.prodMk ((hblocks.prodMk measurable_const).prodMk
    (hrounds.prodMk htargets))

theorem sourcePrefix_completeSourcePrefix (p : Parameters) (r : ℕ) (e₀ : Coordinates p)
    (a : SourcePrefix p r) :
    sourcePrefix p r (completeSourcePrefix p r e₀ a) = a := by
  apply Prod.ext
  · funext t
    apply Prod.ext
    · funext u
      simp [sourcePrefix, calendarPrefix, completeSourcePrefix, dite_eq_left t.2]
    · simp [sourcePrefix, calendarPrefix, completeSourcePrefix, dite_eq_left t.2]
  · apply Prod.ext
    · funext q
      simp [sourcePrefix, blockPrefix, completeSourcePrefix, dite_eq_left q.2]
    · apply Prod.ext
      · funext q
        simp [sourcePrefix, targetPrefix, completeSourcePrefix, dite_eq_left q.2]
      · funext label
        simp [sourcePrefix, roundScalarPrefix, completeSourcePrefix, dite_eq_left label.2]

/-- The actual stopped run is constant on the fibers of the exact source
prefix, by the accepted prefix-input invariance theorem. -/
theorem run_eq_of_sourcePrefix_eq (p : Parameters) (r : ℕ)
    (ids : CompletePublicTable.IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (x y : Coordinates p) (h : sourcePrefix p r x = sourcePrefix p r y) :
    ReferenceInitializationRun.run (referenceInput p ids rewards C_star C_h eta x) r =
      ReferenceInitializationRun.run (referenceInput p ids rewards C_star C_h eta y) r := by
  exact ReferenceInitializationPrefixInvariance.run_eq_of_runPrefixInputEq _ _ r
    (runPrefixInputEq_of_sourcePrefix_eq p r ids rewards C_star C_h eta x y h)

/-- The actual run at boundary `r` factors measurably through the literal
source prefix. The completion used in the proof is fixed from the original
ambient point and contributes no extra source coordinate. -/
theorem measurable_run (p : Parameters) (r : ℕ) (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) :
    @Measurable (Coordinates p) (ReferenceInitializationRun.Boundary p)
      (boundarySigma p r) inferInstance
      (fun e => ReferenceInitializationRun.run
        (referenceInput p ids rewards C_star C_h eta e) r) := by
  let e₀ : Coordinates p := Classical.choice (nonempty_of_isProbabilityMeasure
    (GeneratedBootstrapRoundLaw.originalLaw p))
  let sectionRun : SourcePrefix p r → ReferenceInitializationRun.Boundary p :=
    fun a => ReferenceInitializationRun.run
      (referenceInput p ids rewards C_star C_h eta
        (completeSourcePrefix p r e₀ a)) r
  have hsection : Measurable sectionRun := by
    change Measurable
      (fun a => ReferenceInitializationRun.run
        (ReferenceInitializationMeasurability.inputOfCoordinates p C_star C_h eta rewards
          (ids, completeSourcePrefix p r e₀ a)) r)
    exact (ReferenceInitializationMeasurability.measurable_run p C_star C_h eta rewards r).comp
      (measurable_const.prodMk (measurable_completeSourcePrefix p r e₀))
  let : MeasurableSpace (Coordinates p) := boundarySigma p r
  have hprefix : Measurable (sourcePrefix p r) := comap_measurable (sourcePrefix p r)
  have hfactor :
      (fun e => ReferenceInitializationRun.run
        (referenceInput p ids rewards C_star C_h eta e) r) =
        sectionRun ∘ sourcePrefix p r := by
    funext e
    symm
    exact run_eq_of_sourcePrefix_eq p r ids rewards C_star C_h eta
      (completeSourcePrefix p r e₀ (sourcePrefix p r e)) e
      (sourcePrefix_completeSourcePrefix p r e₀ (sourcePrefix p r e))
  rw [hfactor]
  exact hsection.comp hprefix

/-- The completed-block counter of the actual run is measurable in the
source-prefix filtration. -/
theorem measurable_run_completed (p : Parameters) (r : ℕ)
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) :
    @Measurable (Coordinates p) ℕ (boundarySigma p r) inferInstance
      (fun e => (ReferenceInitializationRun.run
        (referenceInput p ids rewards C_star C_h eta e) r).completed) := by
  exact (measurable_of_countable (fun b : ReferenceInitializationRun.Boundary p =>
    b.completed)).comp (measurable_run p r ids rewards C_star C_h eta)

/-- Effective activation counters factor through the causal source prefix. -/
theorem measurable_run_activation (p : Parameters) (r : ℕ)
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) :
    @Measurable (Coordinates p) (ActiveRoundActions.Follower p.m →
      Option (ReferencePrelaunchFollower.Activation p)) (boundarySigma p r) inferInstance
      (fun e => (ReferenceInitializationRun.run
        (referenceInput p ids rewards C_star C_h eta e) r).activation) := by
  exact (measurable_of_countable (fun b : ReferenceInitializationRun.Boundary p =>
    b.activation)).comp (measurable_run p r ids rewards C_star C_h eta)

/-- The updated numerator vector, including every completed block update, is
measurable in the boundary filtration. -/
theorem measurable_run_numerators (p : Parameters) (r : ℕ)
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) :
    @Measurable (Coordinates p) (Fin (p.m - 1) → Fin p.K → ℕ)
      (boundarySigma p r) inferInstance
      (fun e => (ReferenceInitializationRun.run
        (referenceInput p ids rewards C_star C_h eta e) r).numerators) := by
  exact (measurable_of_countable (fun b : ReferenceInitializationRun.Boundary p =>
    b.numerators)).comp (measurable_run p r ids rewards C_star C_h eta)

/-- Cumulative launch-monitor counters are measurable in the causal
source-prefix filtration. -/
theorem measurable_run_counters (p : Parameters) (r : ℕ)
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) :
    @Measurable (Coordinates p) (Fin p.K → ℕ) (boundarySigma p r) inferInstance
      (fun e => (ReferenceInitializationRun.run
        (referenceInput p ids rewards C_star C_h eta e) r).counters) := by
  exact (measurable_of_countable (fun b : ReferenceInitializationRun.Boundary p =>
    b.counters)).comp (measurable_run p r ids rewards C_star C_h eta)

/-- The first crossing block is measurable in the causal source-prefix
filtration. -/
theorem measurable_run_crossing (p : Parameters) (r : ℕ)
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) :
    @Measurable (Coordinates p) (Option (Fin (n_boot p))) (boundarySigma p r)
      inferInstance
      (fun e => (ReferenceInitializationRun.run
        (referenceInput p ids rewards C_star C_h eta e) r).crossing) := by
  exact (measurable_of_countable (fun b : ReferenceInitializationRun.Boundary p =>
    b.crossing)).comp (measurable_run p r ids rewards C_star C_h eta)

/-- The generated physical history, represented in a fixed padded carrier, is
measurable in the boundary filtration. On elapsed rounds this is exactly the
run's completed history; outside it the padding is `none`. -/
theorem measurable_run_log (p : Parameters) (r : ℕ)
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) :
    @Measurable (Coordinates p) (ReferenceInitializationMeasurability.PaddedPhysicalLog p)
      (boundarySigma p r) inferInstance
      (fun e => ReferenceInitializationMeasurability.boundaryLog p
        (ReferenceInitializationRun.run
          (referenceInput p ids rewards C_star C_h eta e) r)) := by
  exact (measurable_of_countable
    (ReferenceInitializationMeasurability.boundaryLog p)).comp
      (measurable_run p r ids rewards C_star C_h eta)

/-- Before processing the next block, the no-launch guard is the measurable
event that the stopped run has not yet recorded a crossing. -/
theorem measurableSet_noLaunchGuard (p : Parameters) (r : ℕ)
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) :
    @MeasurableSet (Coordinates p) (boundarySigma p r)
      {e | (ReferenceInitializationRun.run
        (referenceInput p ids rewards C_star C_h eta e) r).crossing = none} := by
  exact (measurableSet_singleton none).preimage
    (measurable_run_crossing p r ids rewards C_star C_h eta)

end Bandits.Support.GeneratedBootstrapBlockFiltrationRepair

end
