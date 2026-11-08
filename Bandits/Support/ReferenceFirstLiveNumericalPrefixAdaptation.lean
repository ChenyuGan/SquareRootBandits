/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveNumericalQueueBorel
public import Bandits.Support.ReferenceFirstLiveNumericalPrefixTemporal

import Lean.Elab.Tactic.Omega

/-!
# Strict-past adaptation of the first-live numerical queue readouts

Sources: `sources/zip4/manuscript/04_slow_fast_learner.tex:140-188,256-264`,
`sources/zip4/manuscript/06_interruptions.tex:391-397,425-426`,
`sources/zip4/manuscript/07_public_setup.tex:127-164`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-64`.

The strict prefix consists of the first `t.val - s` actual numerical cells
from the variable first-live window with `t.val - s + 1` calendar records.
The output retains absence tags, all-arm reward and rate vectors, queue
registers, the persistent overflow flag, and chronological per-arm records.
The overflow event below checks only that strict prefix, so the first overflow
update at the current round remains included in the retained run. These are
adaptation results for the inherited source comaps; they assert no conditional
law, authentic history, or regret conclusion.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.ContinuousLearningRows
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceFirstWindowNumericalStream
open Bandits.Support.RecordedQueueRun
open Bandits.Support.ReferenceFirstLiveNumericalPrefixBorel
open Bandits.Support.ReferenceFirstLiveNumericalQueueBorel
open Bandits.Support.ReferenceFirstLiveNumericalPrefixTemporal
open Bandits.Support.ReferenceFirstLiveSourceSavedMoments
open Bandits.Support.ReferenceSourcePhysicalFlagConditionalLaw
open Bandits.Support.ReferenceSourceCurrentControlFreshness
open Bandits.Support.ReferenceSourcePrefixHistoryFiltration

namespace Bandits.Support.ReferenceFirstLiveNumericalPrefixAdaptation

variable {p : ConstructorDimensions.Parameters}
  (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ)
  (q : Fin (M p))
  (t : Fin p.T)
  (s : ℕ)
  (hs : s ≤ t.val)
  (control0 : ContinuousLearningRows.TimeControl p)

local notation "Z" => ReferenceTotalSourceDisintegration.SourceStratum rate rewards C_star C_h t
  (ReferenceFirstLiveRecordingSourceCylinder.stratumIndex q t s hs)
local notation "n" => t.val - s

private theorem measurable_strictPast_outputs :
    Measurable[(MeasurableSpace.comap
    (fun z : Z => ReferenceSourceCurrentControlFreshness.c_t p control0 t z.val)
    (inferInstance : MeasurableSpace (ReferenceSourcePrefixHistoryFiltration.SourceInput p)))]
      (ReferenceFirstLiveNumericalPrefixBorel.numericalCountPastReadout rate rewards C_star C_h q t s hs control0) ∧
    Measurable[(MeasurableSpace.comap
    (fun z : Z => ReferenceSourceCurrentControlFreshness.c_t p control0 t z.val)
    (inferInstance : MeasurableSpace (ReferenceSourcePrefixHistoryFiltration.SourceInput p)))]
      (ReferenceFirstLiveNumericalQueueBorel.numericalCountRunReadout rate rewards C_star C_h q t s hs control0) ∧
    MeasurableSet[(MeasurableSpace.comap
    (fun z : Z => ReferenceSourceCurrentControlFreshness.c_t p control0 t z.val)
    (inferInstance : MeasurableSpace (ReferenceSourcePrefixHistoryFiltration.SourceInput p)))]
      {z : Z |
        (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate)
          ((ReferenceFirstWindowNumericalStream.actualLiveSourceCells rate z.val rewards C_star C_h
            (ReferenceFirstLiveNumericalPrefixTemporal.sourceStratum_facts rate rewards C_star C_h q t s hs z).2.1
            (n + 1)
            (by
              have hz := ReferenceFirstLiveNumericalPrefixTemporal.sourceStratum_facts rate rewards C_star C_h q t s hs z
              rw [hz.2.2]
              omega)).take n)).overflow = false} := by
  let prefixSubtype : Z → Z := fun z =>
    ⟨ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z.val,
      ReferenceFirstLiveNumericalPrefixTemporal.actualSourcePrefix_mem rate rewards C_star C_h q t s hs control0 z⟩

  have hCurrentControl : Measurable[(MeasurableSpace.comap
    (fun z : Z => ReferenceSourceCurrentControlFreshness.c_t p control0 t z.val)
    (inferInstance : MeasurableSpace (ReferenceSourcePrefixHistoryFiltration.SourceInput p)))]
      (fun z : Z => ReferenceSourceCurrentControlFreshness.c_t p control0 t z.val) := by
    exact comap_measurable _

  have hSourcePrefix : Measurable[(MeasurableSpace.comap
    (fun z : Z => ReferenceSourceCurrentControlFreshness.c_t p control0 t z.val)
    (inferInstance : MeasurableSpace (ReferenceSourcePrefixHistoryFiltration.SourceInput p)))]
      (fun z : Z => ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z.val) := by
    have heq :
        (fun z : Z => ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z.val) =
          fun z : Z => ReferenceSourceCurrentControlFreshness.c_t p control0 t z.val := by
      funext z
      exact (ReferenceSourcePhysicalFlagConditionalLaw.c_t_eq_sourcePrefix control0 t z.val).symm
    rw [heq]
    exact hCurrentControl

  have hPrefixSubtype : Measurable[(MeasurableSpace.comap
    (fun z : Z => ReferenceSourceCurrentControlFreshness.c_t p control0 t z.val)
    (inferInstance : MeasurableSpace (ReferenceSourcePrefixHistoryFiltration.SourceInput p)))] prefixSubtype := by
    change Measurable[(MeasurableSpace.comap
    (fun z : Z => ReferenceSourceCurrentControlFreshness.c_t p control0 t z.val)
    (inferInstance : MeasurableSpace (ReferenceSourcePrefixHistoryFiltration.SourceInput p)))]
      (fun z : Z =>
        (⟨ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z.val,
          ReferenceFirstLiveNumericalPrefixTemporal.actualSourcePrefix_mem rate rewards C_star C_h q t s hs control0 z⟩ : Z))
    exact hSourcePrefix.subtype_mk

  have hPastCells (z : Z) :
      ReferenceFirstWindowNumericalStream.actualLiveSourceCells rate z.val rewards C_star C_h
          (ReferenceFirstLiveNumericalPrefixTemporal.sourceStratum_facts rate rewards C_star C_h q t s hs z).2.1 n
          (by
            have hz := ReferenceFirstLiveNumericalPrefixTemporal.sourceStratum_facts rate rewards C_star C_h q t s hs z
            rw [hz.2.2]
            omega) =
        ReferenceFirstWindowNumericalStream.actualLiveSourceCells rate (prefixSubtype z).val rewards C_star C_h
          (ReferenceFirstLiveNumericalPrefixTemporal.sourceStratum_facts rate rewards C_star C_h q t s hs (prefixSubtype z)).2.1 n
          (by
            have hz := ReferenceFirstLiveNumericalPrefixTemporal.sourceStratum_facts rate rewards C_star C_h q t s hs (prefixSubtype z)
            rw [hz.2.2]
            omega) := by
    rw [← ReferenceFirstLiveNumericalPrefixTemporal.actualNumericalCells_take_successor rate rewards C_star C_h q t s hs control0 z,
      ← ReferenceFirstLiveNumericalPrefixTemporal.actualNumericalCells_take_successor rate rewards C_star C_h q t s hs control0
        (prefixSubtype z)]
    exact ReferenceFirstLiveNumericalPrefixTemporal.numerical_past_prefix_eq rate rewards C_star C_h q t s hs control0 z
      (prefixSubtype z) (by rfl)

  have hPastFactor :
      (fun z : Z => ReferenceFirstLiveNumericalPrefixBorel.numericalCountPastReadout rate rewards C_star C_h q t s hs control0 z) =
        fun z : Z =>
          ReferenceFirstLiveNumericalPrefixBorel.numericalCountPastReadout rate rewards C_star C_h q t s hs control0
            (prefixSubtype z) := by
    funext z
    simp only [ReferenceFirstLiveNumericalPrefixBorel.numericalCountPastReadout]
    rw [hPastCells z]

  have hPastAmbient : Measurable
      (ReferenceFirstLiveNumericalPrefixBorel.numericalCountPastReadout rate rewards C_star C_h q t s hs control0) :=
    ReferenceFirstLiveNumericalPrefixBorel.measurable_numericalCountPastReadout rate rewards C_star C_h q t s hs control0
  have hPastAdapted : Measurable[(MeasurableSpace.comap
    (fun z : Z => ReferenceSourceCurrentControlFreshness.c_t p control0 t z.val)
    (inferInstance : MeasurableSpace (ReferenceSourcePrefixHistoryFiltration.SourceInput p)))]
      (ReferenceFirstLiveNumericalPrefixBorel.numericalCountPastReadout rate rewards C_star C_h q t s hs control0) := by
    change Measurable[(MeasurableSpace.comap
      (fun z : Z => ReferenceSourceCurrentControlFreshness.c_t p control0 t z.val)
      (inferInstance : MeasurableSpace (ReferenceSourcePrefixHistoryFiltration.SourceInput p)))]
        (fun z : Z =>
          ReferenceFirstLiveNumericalPrefixBorel.numericalCountPastReadout rate rewards C_star C_h q t s hs control0 z)
    rw [hPastFactor]
    exact hPastAmbient.comp hPrefixSubtype

  have hRunPastFactor : ∀ z : Z,
      RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate)
        ((ReferenceFirstWindowNumericalStream.actualLiveSourceCells rate z.val rewards C_star C_h
          (ReferenceFirstLiveNumericalPrefixTemporal.sourceStratum_facts rate rewards C_star C_h q t s hs z).2.1
          (n + 1)
          (by
            have hz := ReferenceFirstLiveNumericalPrefixTemporal.sourceStratum_facts rate rewards C_star C_h q t s hs z
            rw [hz.2.2]
            omega)).take n) =
      RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate)
        ((ReferenceFirstWindowNumericalStream.actualLiveSourceCells rate (prefixSubtype z).val rewards C_star C_h
          (ReferenceFirstLiveNumericalPrefixTemporal.sourceStratum_facts rate rewards C_star C_h q t s hs
            (prefixSubtype z)).2.1
          (n + 1)
          (by
            have hz := ReferenceFirstLiveNumericalPrefixTemporal.sourceStratum_facts rate rewards C_star C_h q t s hs (prefixSubtype z)
            rw [hz.2.2]
            omega)).take n) := by
    intro z
    exact congrArg (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate))
      (ReferenceFirstLiveNumericalPrefixTemporal.numerical_past_prefix_eq rate rewards C_star C_h q t s hs
        control0 z (prefixSubtype z) (by rfl))

  have hRunCountFactor (z : Z) :
      RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate)
        (ReferenceFirstWindowNumericalStream.actualLiveSourceCells rate z.val rewards C_star C_h
          (ReferenceFirstLiveNumericalPrefixTemporal.sourceStratum_facts rate rewards C_star C_h q t s hs z).2.1
          n
          (by
            have hz := ReferenceFirstLiveNumericalPrefixTemporal.sourceStratum_facts rate rewards C_star C_h q t s hs z
            rw [hz.2.2]
            omega)) =
      RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate)
        (ReferenceFirstWindowNumericalStream.actualLiveSourceCells rate (prefixSubtype z).val rewards C_star C_h
          (ReferenceFirstLiveNumericalPrefixTemporal.sourceStratum_facts rate rewards C_star C_h q t s hs
            (prefixSubtype z)).2.1
          n
          (by
            have hz := ReferenceFirstLiveNumericalPrefixTemporal.sourceStratum_facts rate rewards C_star C_h q t s hs
              (prefixSubtype z)
            rw [hz.2.2]
            omega)) := by
    calc
      _ = RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate)
          ((ReferenceFirstWindowNumericalStream.actualLiveSourceCells rate z.val rewards C_star C_h
            (ReferenceFirstLiveNumericalPrefixTemporal.sourceStratum_facts rate rewards C_star C_h q t s hs z).2.1
            (n + 1)
            (by
              have hz := ReferenceFirstLiveNumericalPrefixTemporal.sourceStratum_facts rate rewards C_star C_h q t s hs z
              rw [hz.2.2]
              omega)).take n) :=
        (ReferenceFirstLiveNumericalPrefixTemporal.numerical_run_count_eq rate rewards C_star C_h q t s hs
          control0 z).symm
      _ = RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate)
          ((ReferenceFirstWindowNumericalStream.actualLiveSourceCells rate (prefixSubtype z).val rewards C_star C_h
            (ReferenceFirstLiveNumericalPrefixTemporal.sourceStratum_facts rate rewards C_star C_h q t s hs
              (prefixSubtype z)).2.1
            (n + 1)
            (by
              have hz := ReferenceFirstLiveNumericalPrefixTemporal.sourceStratum_facts rate rewards C_star C_h q t s hs
                (prefixSubtype z)
              rw [hz.2.2]
              omega)).take n) := hRunPastFactor z
      _ = _ :=
        ReferenceFirstLiveNumericalPrefixTemporal.numerical_run_count_eq rate rewards C_star C_h q t s hs
          control0 (prefixSubtype z)

  have hRunFactor :
      (fun z : Z => ReferenceFirstLiveNumericalQueueBorel.numericalCountRunReadout rate rewards C_star C_h q t s hs control0 z) =
        fun z : Z =>
          ReferenceFirstLiveNumericalQueueBorel.numericalCountRunReadout rate rewards C_star C_h q t s hs control0
            (prefixSubtype z) := by
    funext z
    have hrun := hRunCountFactor z
    simpa [ReferenceFirstLiveNumericalQueueBorel.numericalCountRunReadout] using
      congrArg
        (fun state : RecordedQueueRun.RunState p.K => (state.registers, (state.overflow, state.records))) hrun

  have hRunAmbient : Measurable
      (ReferenceFirstLiveNumericalQueueBorel.numericalCountRunReadout rate rewards C_star C_h q t s hs control0) :=
    ReferenceFirstLiveNumericalQueueBorel.measurable_numericalCountRunReadout rate rewards C_star C_h q t s hs control0
  have hRunAdapted : Measurable[(MeasurableSpace.comap
    (fun z : Z => ReferenceSourceCurrentControlFreshness.c_t p control0 t z.val)
    (inferInstance : MeasurableSpace (ReferenceSourcePrefixHistoryFiltration.SourceInput p)))]
      (ReferenceFirstLiveNumericalQueueBorel.numericalCountRunReadout rate rewards C_star C_h q t s hs control0) := by
    change Measurable[(MeasurableSpace.comap
      (fun z : Z => ReferenceSourceCurrentControlFreshness.c_t p control0 t z.val)
      (inferInstance : MeasurableSpace (ReferenceSourcePrefixHistoryFiltration.SourceInput p)))]
        (fun z : Z =>
          ReferenceFirstLiveNumericalQueueBorel.numericalCountRunReadout rate rewards C_star C_h q t s hs control0 z)
    rw [hRunFactor]
    exact hRunAmbient.comp hPrefixSubtype

  have hOverflowAdapted : Measurable[(MeasurableSpace.comap
    (fun z : Z => ReferenceSourceCurrentControlFreshness.c_t p control0 t z.val)
    (inferInstance : MeasurableSpace (ReferenceSourcePrefixHistoryFiltration.SourceInput p)))]
      (fun z : Z =>
        (ReferenceFirstLiveNumericalQueueBorel.numericalCountRunReadout rate rewards C_star C_h q t s hs control0 z).2.1) :=
    measurable_fst.comp (measurable_snd.comp hRunAdapted)

  have hOverflowSet : MeasurableSet[(MeasurableSpace.comap
    (fun z : Z => ReferenceSourceCurrentControlFreshness.c_t p control0 t z.val)
    (inferInstance : MeasurableSpace (ReferenceSourcePrefixHistoryFiltration.SourceInput p)))]
      {z : Z |
        (ReferenceFirstLiveNumericalQueueBorel.numericalCountRunReadout rate rewards C_star C_h q t s hs control0 z).2.1 = false} :=
    (measurableSet_singleton false).preimage hOverflowAdapted

  have hStrictPastOverflowEq (z : Z) :
      (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate)
        ((ReferenceFirstWindowNumericalStream.actualLiveSourceCells rate z.val rewards C_star C_h
          (ReferenceFirstLiveNumericalPrefixTemporal.sourceStratum_facts rate rewards C_star C_h q t s hs z).2.1
          (n + 1)
          (by
            have hz := ReferenceFirstLiveNumericalPrefixTemporal.sourceStratum_facts rate rewards C_star C_h q t s hs z
            rw [hz.2.2]
            omega)).take n)).overflow =
        (ReferenceFirstLiveNumericalQueueBorel.numericalCountRunReadout rate rewards C_star C_h q t s hs control0 z).2.1 := by
    simpa [ReferenceFirstLiveNumericalQueueBorel.numericalCountRunReadout] using
      congrArg (fun state : RecordedQueueRun.RunState p.K => state.overflow)
        (ReferenceFirstLiveNumericalPrefixTemporal.numerical_run_count_eq rate rewards C_star C_h q t s hs control0 z)

  have hLiteralOverflowSet :
      {z : Z |
        (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate)
          ((ReferenceFirstWindowNumericalStream.actualLiveSourceCells rate z.val rewards C_star C_h z.property.2.1
            (n + 1)
            (by
              have hz := ReferenceFirstLiveNumericalPrefixTemporal.sourceStratum_facts rate rewards C_star C_h q t s hs z
              rw [hz.2.2]
              omega)).take n)).overflow = false} =
      {z : Z |
        (ReferenceFirstLiveNumericalQueueBorel.numericalCountRunReadout rate rewards C_star C_h q t s hs control0 z).2.1 = false} := by
    ext z
    change (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate)
        ((ReferenceFirstWindowNumericalStream.actualLiveSourceCells rate z.val rewards C_star C_h
          (ReferenceFirstLiveNumericalPrefixTemporal.sourceStratum_facts rate rewards C_star C_h q t s hs z).2.1
          (n + 1)
          (by
            have hz := ReferenceFirstLiveNumericalPrefixTemporal.sourceStratum_facts rate rewards C_star C_h q t s hs z
            rw [hz.2.2]
            omega)).take n)).overflow = false ↔
      (ReferenceFirstLiveNumericalQueueBorel.numericalCountRunReadout rate rewards C_star C_h q t s hs control0 z).2.1 = false
    rw [hStrictPastOverflowEq z]

  refine ⟨hPastAdapted, hRunAdapted, ?_⟩
  rw [hLiteralOverflowSet]
  exact hOverflowSet

/-- The faithful finite tuple observation of the actual strict-past cells is
measurable on the current-control comap. Absent entries keep their left tag,
and the complete real-valued reward and rate vectors remain intact. -/
theorem measurable_numericalCountPastReadout :
    Measurable[(MeasurableSpace.comap
    (fun z : Z => ReferenceSourceCurrentControlFreshness.c_t p control0 t z.val)
    (inferInstance : MeasurableSpace (ReferenceSourcePrefixHistoryFiltration.SourceInput p)))]
      (ReferenceFirstLiveNumericalPrefixBorel.numericalCountPastReadout rate rewards C_star C_h q t s hs control0) :=
  (measurable_strictPast_outputs rate rewards C_star C_h q t s hs control0).1

/-- The complete strict-past queue output, including every register, the
persistent overflow bit, and chronological per-arm accepted/no-op records,
is measurable on the current-control comap. -/
theorem measurable_numericalCountRunReadout :
    Measurable[(MeasurableSpace.comap
    (fun z : Z => ReferenceSourceCurrentControlFreshness.c_t p control0 t z.val)
    (inferInstance : MeasurableSpace (ReferenceSourcePrefixHistoryFiltration.SourceInput p)))]
      (ReferenceFirstLiveNumericalQueueBorel.numericalCountRunReadout rate rewards C_star C_h q t s hs control0) :=
  (measurable_strictPast_outputs rate rewards C_star C_h q t s hs control0).2.1

/-- The literal strict-past overflow test is measurable. Its input is exactly
`(actualLiveSourceCells ... (t.val - s + 1)).take (t.val - s)`; hence the
current update, including a first overflow update, is retained. -/
theorem measurableSet_numericalCountRunOverflowFalse :
    MeasurableSet[(MeasurableSpace.comap
    (fun z : Z => ReferenceSourceCurrentControlFreshness.c_t p control0 t z.val)
    (inferInstance : MeasurableSpace (ReferenceSourcePrefixHistoryFiltration.SourceInput p)))]
      {z : Z |
        (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate)
          ((ReferenceFirstWindowNumericalStream.actualLiveSourceCells rate z.val rewards C_star C_h
            (ReferenceFirstLiveNumericalPrefixTemporal.sourceStratum_facts rate rewards C_star C_h q t s hs z).2.1
            (n + 1)
            (by
              have hz := ReferenceFirstLiveNumericalPrefixTemporal.sourceStratum_facts rate rewards C_star C_h q t s hs z
              rw [hz.2.2]
              omega)).take n)).overflow = false} :=
  (measurable_strictPast_outputs rate rewards C_star C_h q t s hs control0).2.2

private theorem measurable_sourceFollowerProjection (i : Fin (p.m - 1)) :
    let Zi := ReferenceFirstLiveSourceSavedMoments.SourceFollower rate rewards C_star C_h q t s hs control0 i
    let Fi := (inferInstance : MeasurableSpace (ReferenceSourcePrefixHistoryFiltration.SourceInput p)).comap
      (fun z : Zi => ReferenceSourceCurrentControlFreshness.c_t p control0 t z.val.val)
    Measurable[Fi, (MeasurableSpace.comap
    (fun z : Z => ReferenceSourceCurrentControlFreshness.c_t p control0 t z.val)
    (inferInstance : MeasurableSpace (ReferenceSourcePrefixHistoryFiltration.SourceInput p)))] (fun z : Zi => z.val) := by
  dsimp
  rw [measurable_comap_iff]
  change Measurable[
    (inferInstance : MeasurableSpace (ReferenceSourcePrefixHistoryFiltration.SourceInput p)).comap
      (fun z : ReferenceFirstLiveSourceSavedMoments.SourceFollower rate rewards C_star C_h q t s hs control0 i =>
        ReferenceSourceCurrentControlFreshness.c_t p control0 t z.val.val)]
    (fun z : ReferenceFirstLiveSourceSavedMoments.SourceFollower rate rewards C_star C_h q t s hs control0 i =>
      ReferenceSourceCurrentControlFreshness.c_t p control0 t z.val.val)
  exact comap_measurable _

/-- Both inherited source comaps project to the same original stratum, so the
past-cell tuple readout remains measurable on every existing follower source
subtype. -/
theorem measurable_numericalCountPastReadout_follower (i : Fin (p.m - 1)) :
    let Zi := ReferenceFirstLiveSourceSavedMoments.SourceFollower rate rewards C_star C_h q t s hs control0 i
    let Fi := (inferInstance : MeasurableSpace (ReferenceSourcePrefixHistoryFiltration.SourceInput p)).comap
      (fun z : Zi => ReferenceSourceCurrentControlFreshness.c_t p control0 t z.val.val)
    Measurable[Fi]
      (fun z : Zi =>
        ReferenceFirstLiveNumericalPrefixBorel.numericalCountPastReadout rate rewards C_star C_h q t s hs control0 z.val) := by
  let Zi := ReferenceFirstLiveSourceSavedMoments.SourceFollower rate rewards C_star C_h q t s hs control0 i
  let Fi := (inferInstance : MeasurableSpace (ReferenceSourcePrefixHistoryFiltration.SourceInput p)).comap
    (fun z : Zi => ReferenceSourceCurrentControlFreshness.c_t p control0 t z.val.val)
  have hproj : Measurable[Fi, (MeasurableSpace.comap
    (fun z : Z => ReferenceSourceCurrentControlFreshness.c_t p control0 t z.val)
    (inferInstance : MeasurableSpace (ReferenceSourcePrefixHistoryFiltration.SourceInput p)))] (fun z : Zi => z.val) :=
    measurable_sourceFollowerProjection rate rewards C_star C_h q t s hs control0 i
  exact (measurable_numericalCountPastReadout rate rewards C_star C_h q t s hs control0).comp hproj

/-- The same complete queue run readout is measurable after projection to each
existing unnormalized follower source subtype. -/
theorem measurable_numericalCountRunReadout_follower (i : Fin (p.m - 1)) :
    let Zi := ReferenceFirstLiveSourceSavedMoments.SourceFollower rate rewards C_star C_h q t s hs control0 i
    let Fi := (inferInstance : MeasurableSpace (ReferenceSourcePrefixHistoryFiltration.SourceInput p)).comap
      (fun z : Zi => ReferenceSourceCurrentControlFreshness.c_t p control0 t z.val.val)
    Measurable[Fi]
      (fun z : Zi =>
        ReferenceFirstLiveNumericalQueueBorel.numericalCountRunReadout rate rewards C_star C_h q t s hs control0 z.val) := by
  let Zi := ReferenceFirstLiveSourceSavedMoments.SourceFollower rate rewards C_star C_h q t s hs control0 i
  let Fi := (inferInstance : MeasurableSpace (ReferenceSourcePrefixHistoryFiltration.SourceInput p)).comap
    (fun z : Zi => ReferenceSourceCurrentControlFreshness.c_t p control0 t z.val.val)
  have hproj : Measurable[Fi, (MeasurableSpace.comap
    (fun z : Z => ReferenceSourceCurrentControlFreshness.c_t p control0 t z.val)
    (inferInstance : MeasurableSpace (ReferenceSourcePrefixHistoryFiltration.SourceInput p)))] (fun z : Zi => z.val) :=
    measurable_sourceFollowerProjection rate rewards C_star C_h q t s hs control0 i
  exact (measurable_numericalCountRunReadout rate rewards C_star C_h q t s hs control0).comp hproj

/-- The same literal strict-past overflow test is measurable on every
existing follower subtype, with no current-control invariance assertion. -/
theorem measurableSet_numericalCountRunOverflowFalse_follower (i : Fin (p.m - 1)) :
    let Zi := ReferenceFirstLiveSourceSavedMoments.SourceFollower rate rewards C_star C_h q t s hs control0 i
    let Fi := (inferInstance : MeasurableSpace (ReferenceSourcePrefixHistoryFiltration.SourceInput p)).comap
      (fun z : Zi => ReferenceSourceCurrentControlFreshness.c_t p control0 t z.val.val)
    MeasurableSet[Fi]
      {z : Zi |
        (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate)
          ((ReferenceFirstWindowNumericalStream.actualLiveSourceCells rate z.val.val rewards C_star C_h
            (ReferenceFirstLiveNumericalPrefixTemporal.sourceStratum_facts rate rewards C_star C_h q t s hs z.val).2.1
            (n + 1)
            (by
              have hz := ReferenceFirstLiveNumericalPrefixTemporal.sourceStratum_facts rate rewards C_star C_h q t s hs z.val
              rw [hz.2.2]
              omega)).take n)).overflow = false} := by
  let Zi := ReferenceFirstLiveSourceSavedMoments.SourceFollower rate rewards C_star C_h q t s hs control0 i
  let Fi := (inferInstance : MeasurableSpace (ReferenceSourcePrefixHistoryFiltration.SourceInput p)).comap
    (fun z : Zi => ReferenceSourceCurrentControlFreshness.c_t p control0 t z.val.val)
  have hproj : Measurable[Fi, (MeasurableSpace.comap
    (fun z : Z => ReferenceSourceCurrentControlFreshness.c_t p control0 t z.val)
    (inferInstance : MeasurableSpace (ReferenceSourcePrefixHistoryFiltration.SourceInput p)))] (fun z : Zi => z.val) :=
    measurable_sourceFollowerProjection rate rewards C_star C_h q t s hs control0 i
  have hset := measurableSet_numericalCountRunOverflowFalse rate rewards C_star C_h q t s hs control0
  exact hset.preimage hproj

end Bandits.Support.ReferenceFirstLiveNumericalPrefixAdaptation

end
