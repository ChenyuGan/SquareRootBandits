/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionAwaitedDownFailureReadout
public import Bandits.Support.ReferencePrelaunchInspectedDecoderPast

import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-!
# Inclusive first-collection decoder stopping calendar

This internal producer joins the existing dated prelaunch DOWN readout with
the existing postlaunch saved-wrong, fixed-awaited DOWN, and fixed-awaited UP
readouts. The fixed-word branches retain their actual completed receiver
banks, stamped equations, one common awaited word, and every selected channel
date in the closed interval, including dates with zero feedback. The prelaunch
branch is the actual ordinary passing DOWN decision suppressed before
assignment effects; that phase has no fixed-sent-word completed batch and no
eligible UP receiver. The postlaunch wrong-unique branch uses the saved actual
receiver diagnostic.

The stop is the first EXCLUDED one-based date. Its detecting calendar update
is kept, and physical records continue on the original source through the
horizon. This is only a decoder-branch union. It does not establish exhaustive
source-error coverage, the complete source collection stop, a probability
bound, or a stopped-charge theorem; reverse source coverage remains open.
The intended consumer is `ReferenceFirstCollectionLiteralStoppedCharge`.

Sources: `05_binary_transport.tex:23-55`, `06_interruptions.tex:425-487`,
`07_public_setup.tex:127-164`, and `appendix_a_local_protocol.tex:8-14,92-108,141-157`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support
open ConstructorDimensions
open BootstrapPrivateRoundStreams
open ReferencePrelaunchFollower
open ReferenceGeneratedPrelaunchDownPrefix
open ReferenceInitializationRun
open BootstrapPhysicalBlock
open OrdinaryMessageCodec
open scoped Classical

namespace Bandits.Support.ReferenceFirstCollectionInclusiveDecoderStop

variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
variable (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
variable (C_star C_h : ℝ)

/-- The original complete private source carrier used by both readouts. -/
abbrev Z := BootstrapPrivateRoundStreams.SourceInput p

/-- The literal finite-calendar union of the existing prelaunch and
postlaunch dated decoder diagnostics. No source-coverage converse is built
into this definition. -/
def decoderFailureAt (z : Z (p := p)) (t : Fin p.T) : Prop :=
  (∃ i : Fin (p.m - 1),
    ReferencePrelaunchDownDecisionReadout.prelaunchDownFailureAt
      rate rewards C_star C_h z i t = true) ∨
    ReferenceFirstCollectionAwaitedDownFailureReadout.failureAt
      rate rewards C_star C_h z t

/-- A candidate detector index is either the horizon sentinel or the
successor offset of an actual dated decoder witness. -/
def detectorIndexOccurs (z : Z (p := p)) (n : ℕ) : Prop :=
  n = p.T ∨ ∃ t : Fin p.T, t.val + 1 = n ∧
    decoderFailureAt rate rewards C_star C_h z t

/-- Every source has a finite detector scan endpoint, supplied by the
horizon sentinel. -/
theorem detectorIndexOccurs_exists (z : Z (p := p)) :
    ∃ n, detectorIndexOccurs rate rewards C_star C_h z n :=
  ⟨p.T, Or.inl rfl⟩

/-- The least index at which the strict-past scan detects the union, using
`T` as its no-detection sentinel. -/
def firstDetectionIndex (z : Z (p := p)) : ℕ :=
  Nat.find (detectorIndexOccurs_exists rate rewards C_star C_h z)

/-- The first excluded one-based date, clipped to the horizon endpoint. -/
def firstExcludedDate (z : Z (p := p)) : ℕ :=
  min (p.T + 1) (firstDetectionIndex rate rewards C_star C_h z + 1)

/-- The sentinel or a real detecting successor occurs no later than `T`. -/
theorem firstDetectionIndex_le_horizon (z : Z (p := p)) :
    firstDetectionIndex rate rewards C_star C_h z ≤ p.T := by
  exact Nat.find_min' (detectorIndexOccurs_exists rate rewards C_star C_h z)
    (Or.inl rfl)

/-- The detector index is positive, since every physical date starts at one. -/
theorem firstDetectionIndex_pos (z : Z (p := p)) :
    1 ≤ firstDetectionIndex rate rewards C_star C_h z := by
  have hs := Nat.find_spec (detectorIndexOccurs_exists rate rewards C_star C_h z)
  change firstDetectionIndex rate rewards C_star C_h z = p.T ∨
    ∃ t : Fin p.T,
      t.val + 1 = firstDetectionIndex rate rewards C_star C_h z ∧
        decoderFailureAt rate rewards C_star C_h z t at hs
  rcases hs with hsent | ⟨t, hdate, _⟩
  · have hT : 1 ≤ p.T := p.one_le_T
    omega
  · omega

/-- Being strictly before the first detector is equivalent to having no
failure on any strictly earlier original date. -/
theorem firstDetectionIndex_lt_iff_no_earlier_failure
    (z : Z (p := p)) (t : Fin p.T) :
    t.val < firstDetectionIndex rate rewards C_star C_h z ↔
      ∀ u : Fin p.T, u.val < t.val →
        ¬ decoderFailureAt rate rewards C_star C_h z u := by
  constructor
  · intro hfirst u hu hfail
    have hle := Nat.find_min'
      (detectorIndexOccurs_exists rate rewards C_star C_h z)
      (Or.inr ⟨u, rfl, hfail⟩)
    change firstDetectionIndex rate rewards C_star C_h z ≤ u.val + 1 at hle
    omega
  · intro hno
    by_contra hlt
    have hle : firstDetectionIndex rate rewards C_star C_h z ≤ t.val :=
      Nat.le_of_not_gt hlt
    have hs := Nat.find_spec (detectorIndexOccurs_exists rate rewards C_star C_h z)
    change firstDetectionIndex rate rewards C_star C_h z = p.T ∨
      ∃ u : Fin p.T,
        u.val + 1 = firstDetectionIndex rate rewards C_star C_h z ∧
          decoderFailureAt rate rewards C_star C_h z u at hs
    rcases hs with hsent | ⟨u, hdate, hfail⟩
    · omega
    · have hut : u.val < t.val := by omega
      exact (hno u hut) hfail

/-- The explicit clipping is inactive because the detector index is at most
the horizon. -/
theorem firstExcludedDate_eq_firstDetectionIndex_add_one (z : Z (p := p)) :
    firstExcludedDate rate rewards C_star C_h z =
      firstDetectionIndex rate rewards C_star C_h z + 1 := by
  have hle : firstDetectionIndex rate rewards C_star C_h z ≤ p.T :=
    firstDetectionIndex_le_horizon rate rewards C_star C_h z
  unfold firstExcludedDate
  exact Nat.min_eq_right (Nat.succ_le_succ hle)

/-- The first excluded date lies in `[2,T+1]`, including the no-detection
sentinel at `T+1`. -/
theorem firstExcludedDate_bounds (z : Z (p := p)) :
    2 ≤ firstExcludedDate rate rewards C_star C_h z ∧
      firstExcludedDate rate rewards C_star C_h z ≤ p.T + 1 := by
  rw [firstExcludedDate_eq_firstDetectionIndex_add_one]
  have hle := firstDetectionIndex_le_horizon rate rewards C_star C_h z
  have hpos : 1 ≤ firstDetectionIndex rate rewards C_star C_h z :=
    firstDetectionIndex_pos rate rewards C_star C_h z
  omega

/-- Same-date physical classification of the union. The second branch is the
saved actual wrong-unique receiver diagnostic; the final two branches are the
unchanged actual completed fixed-awaited DOWN and UP readouts. -/
theorem decoderFailureAt_sourceWitnesses (z : Z (p := p)) (t : Fin p.T) :
    decoderFailureAt rate rewards C_star C_h z t ↔
      (∃ i : Fin (p.m - 1),
        ReferencePrelaunchDownDecisionReadout.prelaunchDownFailureAt
          rate rewards C_star C_h z i t = true) ∨
      (∃ r : ReferenceFirstCollectionAwaitedDownFailureReadout.Record
            (rate := rate),
        ReferenceFirstCollectionAwaitedDownFailureReadout.actualRecord
            rate rewards C_star C_h t z = some r ∧
          ReferenceActiveStoppedPrefixCoupling.saved_wrong_unique_accepted r) ∨
      ReferenceFirstCollectionAwaitedDownFailureReadout.fixedAwaitedDownFailureAt
        rate rewards C_star C_h z t ∨
      ReferenceCollectionUpFailureReadoutV2.fixedAwaitedUpFailureAt
        rate rewards C_star C_h z t := by
  change ((∃ i : Fin (p.m - 1),
      ReferencePrelaunchDownDecisionReadout.prelaunchDownFailureAt
        rate rewards C_star C_h z i t = true) ∨
    ((∃ r : ReferenceFirstCollectionAwaitedDownFailureReadout.Record
          (rate := rate),
        ReferenceFirstCollectionAwaitedDownFailureReadout.actualRecord
            rate rewards C_star C_h t z = some r ∧
          ReferenceActiveStoppedPrefixCoupling.saved_wrong_unique_accepted r) ∨
      ReferenceFirstCollectionAwaitedDownFailureReadout.fixedAwaitedDownFailureAt
        rate rewards C_star C_h z t ∨
      ReferenceCollectionUpFailureReadoutV2.fixedAwaitedUpFailureAt
        rate rewards C_star C_h z t)) ↔ _
  rfl

/-- An actual prelaunch passing DOWN decision is the completed ordinary batch
and acceptance test of the generated prefix, while the saved follower
registers remain unassigned. The same phase has no fixed-sent-word batch and
the coordinator UP receiver is disabled. -/
theorem prelaunchFailureAt_suppressed_before_effects
    (z : Z (p := p)) (i : Fin (p.m - 1)) (t : Fin p.T)
    (hfail : ReferencePrelaunchDownDecisionReadout.prelaunchDownFailureAt
      rate rewards C_star C_h z i t = true) :
    (∃ active,
      ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix
        rate rewards C_star C_h z i t = .inl (.inl active) ∧
      active.val.2.2.2.lastDown = none ∧
      acceptedStart active.val.2.2.2 = 0 ∧
      active.val.2.2.2.S = 0 ∧ active.val.2.2.2.delta = 0 ∧
      active.val.2.2.2.backlog = 0 ∧ active.val.2.2.2.status = .unoccupied) ∧
    (∃ active : ReferenceGeneratedPrelaunchDownPrefix.ActiveProjection p i t.val
        (ReferenceGeneratedPrelaunchDownPrefix.sourceReferenceInput
          rate rewards C_star C_h z).row (Nat.le_of_lt t.isLt)
        (ReferenceGeneratedPrelaunchDownPrefix.sourceReferenceInput
          rate rewards C_star C_h z)
        (BootstrapDimensions.roundBlockIndex p t),
      ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix
        rate rewards C_star C_h z i t = .inl (.inl active) ∧
      ReferencePrelaunchFollower.passing_at rate.eta i
        (ReferenceGeneratedPrelaunchDownPrefix.sourceReferenceInput
          rate rewards C_star C_h z).row active.val.2.1 t
        (ReferenceInitializationRun.ownEntry
          (ReferenceInitializationRun.physical
            (ReferenceGeneratedPrelaunchDownPrefix.sourceReferenceInput
              rate rewards C_star C_h z)
            active.val.1.val active.val.1.property.1)
          (PublicDiscreteDraws.followerPlayer p.two_le_m
            (ActualReferenceInitializationBlock.refFollower i)) t)
        active.val.2.2.2.downBatch) ∧
    (∀ test : ReferenceGeneratedDownBatchCalendar.ExecutedTest p,
      test ∈ (ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix_tests
          rate rewards C_star C_h z i t ++
        (ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_current_test
          rate rewards C_star C_h z i t).toList) → test.sent = none) ∧
    (∀ b : ReferenceInitializationRun.Boundary p,
      ReferenceInitializationRun.coordinatorUpEnabled b = false) ∧
    BootstrapPhysicalBlock.initialUpRecord p =
      ⟨OrdinaryMessageCodec.upPlaceholder, Or.inl rfl⟩ := by
  have hactive :=
    (ReferencePrelaunchDownDecisionReadout.prelaunchDownFailureAt_true_iff
      rate rewards C_star C_h z i t).mp hfail
  obtain ⟨active, hpref, hpassing⟩ := hactive
  have hregisters :=
    ReferencePrelaunchDownDecisionReadout.prelaunch_active_registers
      rate rewards C_star C_h z i t active
  refine ⟨⟨active, hpref, hregisters.1, hregisters.2.1, hregisters.2.2.1,
      hregisters.2.2.2.1, hregisters.2.2.2.2.1, hregisters.2.2.2.2.2⟩,
    ⟨active, hpref, hpassing⟩, ?_, ?_,
    ReferencePrelaunchDownDecisionReadout.prelaunchActualInitialUpPlaceholder⟩
  · intro test htest
    exact ReferencePrelaunchDownDecisionReadout.source_prelaunch_down_tests_through_sent_none
      rate rewards C_star C_h z i t test htest
  · intro b
    exact ReferencePrelaunchDownDecisionReadout.prelaunchCoordinatorUpDisabled b

/-- Borel measurability of one literal date of the decoder union, obtained
from the admitted actual prelaunch and postlaunch readouts. -/
theorem decoderFailureAt_borel (t : Fin p.T) :
    MeasurableSet {z : Z (p := p) | decoderFailureAt rate rewards C_star C_h z t} := by
  have hpre : MeasurableSet {z : Z (p := p) |
      ∃ i : Fin (p.m - 1),
        ReferencePrelaunchDownDecisionReadout.prelaunchDownFailureAt
          rate rewards C_star C_h z i t = true} := by
    have heq : {z : Z (p := p) |
        ∃ i : Fin (p.m - 1),
          ReferencePrelaunchDownDecisionReadout.prelaunchDownFailureAt
            rate rewards C_star C_h z i t = true} =
        ⋃ i : Fin (p.m - 1), {z : Z (p := p) |
          ReferencePrelaunchDownDecisionReadout.prelaunchDownFailureAt
            rate rewards C_star C_h z i t = true} := by
      ext z
      simp
    rw [heq]
    exact MeasurableSet.iUnion fun i => by
      have hi :=
        ReferencePrelaunchInspectedDecoderPast.prelaunchDownFailureAt_measurable
          rate rewards C_star C_h (t.val + 1) (by omega) t (by omega) i
      exact measurableSet_preimage hi (measurableSet_singleton true)
  exact hpre.union
    (ReferenceFirstCollectionAwaitedDownFailureReadout.failureAt_borel
      rate rewards C_star C_h t)

/-- Each fixed detector-index fiber is Borel, since it is a finite union of
the actual dated decoder atoms and possibly the constant horizon sentinel. -/
theorem detectorIndexOccurs_measurable (n : ℕ) :
    MeasurableSet {z : Z (p := p) | detectorIndexOccurs rate rewards C_star C_h z n} := by
  by_cases hsent : n = p.T
  · simp [detectorIndexOccurs, hsent]
  · have heq : {z : Z (p := p) |
        detectorIndexOccurs rate rewards C_star C_h z n} =
      ⋃ t : Fin p.T, {z : Z (p := p) |
        t.val + 1 = n ∧ decoderFailureAt rate rewards C_star C_h z t} := by
      ext z
      simp [detectorIndexOccurs, hsent]
    rw [heq]
    exact MeasurableSet.iUnion fun t => by
      by_cases hdate : t.val + 1 = n
      · simpa [hdate] using decoderFailureAt_borel rate rewards C_star C_h t
      · simp [hdate]

/-- Ambient measurability of the clipped first excluded date on the original
continuous source carrier. -/
theorem firstExcludedDate_measurable :
    Measurable (firstExcludedDate rate rewards C_star C_h) := by
  have hfind := measurable_find
    (p := fun z n => detectorIndexOccurs rate rewards C_star C_h z n)
    (fun z => detectorIndexOccurs_exists rate rewards C_star C_h z)
    (by intro n; exact detectorIndexOccurs_measurable rate rewards C_star C_h n)
  have hplus : Measurable (fun z : Z (p := p) =>
      firstDetectionIndex rate rewards C_star C_h z + 1) :=
    hfind.add_const 1
  have heq : firstExcludedDate rate rewards C_star C_h =
      fun z => firstDetectionIndex rate rewards C_star C_h z + 1 := by
    funext z
    exact firstExcludedDate_eq_firstDetectionIndex_add_one rate rewards C_star C_h z
  simpa only [heq] using hplus

/-- The strict-past Bool gate is exactly the union of the two admitted flags.
Its index `n` scans source offsets strictly smaller than `n`. -/
def decoderPastFlag (n : ℕ) (hn : n ≤ p.T) (z : Z (p := p)) : Bool :=
  ReferencePrelaunchDownDecisionReadout.prelaunchPastDecoderFlag
      rate rewards C_star C_h z n hn ||
    ReferenceFirstCollectionAwaitedDownFailureReadout.pastFailureFlag
      rate rewards C_star C_h n z

/-- Exact constituent identity for the strict-past Bool gate. -/
theorem decoderPastFlag_eq_constituent_flags (n : ℕ) (hn : n ≤ p.T)
    (z : Z (p := p)) :
    decoderPastFlag rate rewards C_star C_h n hn z =
      (ReferencePrelaunchDownDecisionReadout.prelaunchPastDecoderFlag
          rate rewards C_star C_h z n hn ||
        ReferenceFirstCollectionAwaitedDownFailureReadout.pastFailureFlag
          rate rewards C_star C_h n z) := rfl

/-- The gate is false exactly when no earlier dated decoder witness exists. -/
theorem decoderPastFlag_false_iff_no_earlier_failure
    (n : ℕ) (hn : n ≤ p.T) (z : Z (p := p)) :
    decoderPastFlag rate rewards C_star C_h n hn z = false ↔
      ∀ t : Fin p.T, t.val < n →
        ¬ decoderFailureAt rate rewards C_star C_h z t := by
  constructor
  · intro hflag t ht hfail
    have hor := (Bool.or_eq_false_iff.mp hflag)
    rcases hfail with hpre | hpost
    · obtain ⟨i, hreadout⟩ := hpre
      let j : Fin n := ⟨t.val, ht⟩
      have hcast : (Fin.castLE hn j : Fin p.T) = t := by
        apply Fin.ext
        rfl
      have hfalse :=
        (ReferencePrelaunchInspectedDecoderPast.prelaunchPastDecoderFlag_eq_false_iff_no_dated_readout
          rate rewards C_star C_h n hn z).mp hor.1 j i
      rw [hcast] at hfalse
      rw [hreadout] at hfalse
      contradiction
    · exact
        (ReferenceFirstCollectionAwaitedDownFailureReadout.pastFailureFlag_false_iff_no_earlier_failure
          rate rewards C_star C_h z n).mp hor.2 t ht hpost
  · intro hno
    apply Bool.or_eq_false_iff.mpr
    constructor
    · apply
        (ReferencePrelaunchInspectedDecoderPast.prelaunchPastDecoderFlag_eq_false_iff_no_dated_readout
          rate rewards C_star C_h n hn z).mpr
      intro j i
      have ht : (Fin.castLE hn j : Fin p.T).val < n := by
        simp
      have hfail := hno (Fin.castLE hn j) ht
      cases hreadout : ReferencePrelaunchDownDecisionReadout.prelaunchDownFailureAt
          rate rewards C_star C_h z i (Fin.castLE hn j) with
      | false => rfl
      | true => exact False.elim (hfail (Or.inl ⟨i, hreadout⟩))
    · apply
        (ReferenceFirstCollectionAwaitedDownFailureReadout.pastFailureFlag_false_iff_no_earlier_failure
          rate rewards C_star C_h z n).mpr
      intro t ht hpost
      exact hno t ht (Or.inr hpost)

/-- The strict-past detector is empty at offset zero. -/
theorem decoderPastFlag_zero (z : Z (p := p)) :
    decoderPastFlag rate rewards C_star C_h 0 (Nat.zero_le p.T) z = false := by
  apply (decoderPastFlag_false_iff_no_earlier_failure
    rate rewards C_star C_h 0 (Nat.zero_le p.T) z).mpr
  intro t ht
  omega

/-- The current physical date enters the strict-past scan at its successor. -/
theorem decoderPastFlag_succ (n : ℕ) (hn : n + 1 ≤ p.T) (z : Z (p := p)) :
    decoderPastFlag rate rewards C_star C_h (n + 1) hn z =
      (decoderPastFlag rate rewards C_star C_h n (Nat.le_of_succ_le hn) z ||
        decide (decoderFailureAt rate rewards C_star C_h z
          ⟨n, Nat.lt_of_lt_of_le (Nat.lt_succ_self n) hn⟩)) := by
  let current : Fin p.T := ⟨n, Nat.lt_of_lt_of_le (Nat.lt_succ_self n) hn⟩
  change decoderPastFlag rate rewards C_star C_h (n + 1) hn z =
    (decoderPastFlag rate rewards C_star C_h n (Nat.le_of_succ_le hn) z ||
      decide (decoderFailureAt rate rewards C_star C_h z current))
  have hnle : n ≤ p.T := Nat.le_of_succ_le hn
  cases hprev : decoderPastFlag rate rewards C_star C_h n hnle z with
  | true =>
      have hnext : decoderPastFlag rate rewards C_star C_h (n + 1) hn z = true := by
        by_contra hnot
        have hfalse : decoderPastFlag rate rewards C_star C_h (n + 1) hn z = false := by
          cases h : decoderPastFlag rate rewards C_star C_h (n + 1) hn z <;> simp_all
        have hno := (decoderPastFlag_false_iff_no_earlier_failure
          rate rewards C_star C_h (n + 1) hn z).mp hfalse
        have hprevFalse := (decoderPastFlag_false_iff_no_earlier_failure
          rate rewards C_star C_h n hnle z).mpr fun t ht hf => hno t (by omega) hf
        rw [hprev] at hprevFalse
        contradiction
      simp [hnext]
  | false =>
      by_cases hcurrent : decoderFailureAt rate rewards C_star C_h z current
      ·
          have hnext : decoderPastFlag rate rewards C_star C_h (n + 1) hn z = true := by
            by_contra hnot
            have hfalse : decoderPastFlag rate rewards C_star C_h (n + 1) hn z = false := by
              cases h : decoderPastFlag rate rewards C_star C_h (n + 1) hn z <;> simp_all
            have hno := (decoderPastFlag_false_iff_no_earlier_failure
              rate rewards C_star C_h (n + 1) hn z).mp hfalse
            exact hno current (by simp [current]) (by simpa [current] using hcurrent)
          simp [hcurrent, hnext]
      ·
          have hnoPrev := (decoderPastFlag_false_iff_no_earlier_failure
            rate rewards C_star C_h n hnle z).mp hprev
          have hnoNext : ∀ t : Fin p.T, t.val < n + 1 →
              ¬ decoderFailureAt rate rewards C_star C_h z t := by
            intro t ht hfail
            by_cases htn : t.val < n
            · exact hnoPrev t htn hfail
            · have hval : t.val = n := by omega
              have heq : t = current := Fin.ext hval
              subst t
              exact hcurrent (by simpa [current] using hfail)
          have hnextFalse := (decoderPastFlag_false_iff_no_earlier_failure
            rate rewards C_star C_h (n + 1) hn z).mpr hnoNext
          simp [hcurrent, hnextFalse]

/-- A detected decoder date remains in every longer strict-past scan. -/
theorem decoderPastFlag_mono (z : Z (p := p)) {a b : ℕ}
    (ha : a ≤ p.T) (hb : b ≤ p.T) (hab : a ≤ b)
    (hflag : decoderPastFlag rate rewards C_star C_h a ha z = true) :
    decoderPastFlag rate rewards C_star C_h b hb z = true := by
  cases hbf : decoderPastFlag rate rewards C_star C_h b hb z with
  | true => rfl
  | false =>
      have hnoB := (decoderPastFlag_false_iff_no_earlier_failure
        rate rewards C_star C_h b hb z).mp hbf
      have hafalse : decoderPastFlag rate rewards C_star C_h a ha z = false :=
        (decoderPastFlag_false_iff_no_earlier_failure
          rate rewards C_star C_h a ha z).mpr fun t hta hf =>
            hnoB t (lt_of_lt_of_le hta hab) hf
      rw [hafalse] at hflag
      cases hflag

/-- Ambient Borel measurability of the strict-past decoder gate on the original
source input. -/
theorem decoderPastFlag_measurable (n : ℕ) (hn : n ≤ p.T) :
    Measurable (fun z : Z (p := p) => decoderPastFlag rate rewards C_star C_h n hn z) := by
  apply measurable_to_bool
  change MeasurableSet {z : Z (p := p) |
    decoderPastFlag rate rewards C_star C_h n hn z = true}
  have heq : {z : Z (p := p) |
      decoderPastFlag rate rewards C_star C_h n hn z = true} =
      {z | ReferencePrelaunchDownDecisionReadout.prelaunchPastDecoderFlag
          rate rewards C_star C_h z n hn = true} ∪
        {z | ReferenceFirstCollectionAwaitedDownFailureReadout.pastFailureFlag
          rate rewards C_star C_h n z = true} := by
    ext z
    simp [decoderPastFlag]
  rw [heq]
  exact (measurableSet_preimage
      (ReferencePrelaunchInspectedDecoderPast.prelaunchPastDecoderFlag_measurable
        rate rewards C_star C_h n hn) (measurableSet_singleton true)).union
    (by
      change MeasurableSet {z : Z (p := p) |
        ReferenceFirstCollectionAwaitedDownFailureReadout.pastFailureFlag
          rate rewards C_star C_h n z = true}
      simp only [ReferenceFirstCollectionAwaitedDownFailureReadout.pastFailureFlag,
        decide_eq_true_eq]
      have heq : {z : Z (p := p) | ∃ t : Fin p.T, t.val < n ∧
          ReferenceFirstCollectionAwaitedDownFailureReadout.failureAt
            rate rewards C_star C_h z t} =
          ⋃ t : Fin p.T, {z : Z (p := p) | t.val < n ∧
            ReferenceFirstCollectionAwaitedDownFailureReadout.failureAt
              rate rewards C_star C_h z t} := by
        ext z
        simp
      rw [heq]
      exact MeasurableSet.iUnion fun t => by
        by_cases ht : t.val < n
        · simpa only [ht, true_and] using
            ReferenceFirstCollectionAwaitedDownFailureReadout.failureAt_borel
              rate rewards C_star C_h t
        · simp [ht])

/-- A one-based date is kept exactly when its strict-past gate is still false,
equivalently when every earlier original calendar date has no union witness. -/
def decoderDateKeptAt (z : Z (p := p)) (t : Fin p.T) : Prop :=
  t.val + 1 < firstExcludedDate rate rewards C_star C_h z

/-- Exact kept-date characterization against the first finite detection. -/
theorem decoderDateKeptAt_iff_no_earlier
    (z : Z (p := p)) (t : Fin p.T) :
    decoderDateKeptAt rate rewards C_star C_h z t ↔
      ∀ u : Fin p.T, u.val < t.val →
        ¬ decoderFailureAt rate rewards C_star C_h z u := by
  rw [decoderDateKeptAt, firstExcludedDate_eq_firstDetectionIndex_add_one]
  have hfirst := firstDetectionIndex_lt_iff_no_earlier_failure
    rate rewards C_star C_h z t
  simpa only [Nat.add_lt_add_iff_right] using hfirst

/-- At every actual date, the inclusive stop keeps the detecting update. -/
theorem decoderDateKeptAt_iff_gate_false
    (z : Z (p := p)) (t : Fin p.T) :
    decoderDateKeptAt rate rewards C_star C_h z t ↔
      decoderPastFlag rate rewards C_star C_h t.val (Nat.le_of_lt t.isLt) z = false := by
  rw [decoderDateKeptAt_iff_no_earlier rate rewards C_star C_h z t,
    decoderPastFlag_false_iff_no_earlier_failure rate rewards C_star C_h
      t.val (Nat.le_of_lt t.isLt) z]

/-- Predictability of the combined strict-past gate in the original
source-prefix filtration. The prelaunch measurable factor is first placed in
its actual inspected analysis field and then moved by the admitted containment
to the source prefix. -/
theorem decoderPastFlag_adapted
    (control0 : ContinuousLearningRows.TimeControl p) (n : ℕ) (hn : n ≤ p.T) :
    Measurable[
      ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0
        (n + 1)]
      (fun z : Z (p := p) => decoderPastFlag rate rewards C_star C_h n hn z) := by
  let K := ReferenceSourceOwnHistoryContainment.inspectedHistorySpace
    rate rewards C_star C_h n hn
  have hpre : Measurable[K]
      (fun z : Z (p := p) =>
        ReferencePrelaunchDownDecisionReadout.prelaunchPastDecoderFlag
          rate rewards C_star C_h z n hn) :=
    ReferencePrelaunchInspectedDecoderPast.prelaunchPastDecoderFlag_measurable_in_inspectedHistorySpace
      rate rewards C_star C_h n hn
  have hcontain : K ≤
      ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (n + 1) :=
    ReferenceSourceOwnHistoryContainment.inspectedHistorySpace_le_sourcePrefixFiltration
      rate rewards C_star C_h control0 n hn
  have hpre' : Measurable[
      ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (n + 1)]
      (fun z : Z (p := p) =>
        ReferencePrelaunchDownDecisionReadout.prelaunchPastDecoderFlag
          rate rewards C_star C_h z n hn) := hpre.mono hcontain le_rfl
  have hpost : Measurable[
      ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (n + 1)]
      (fun z : Z (p := p) =>
        ReferenceFirstCollectionAwaitedDownFailureReadout.pastFailureFlag
          rate rewards C_star C_h n z) :=
    ReferenceFirstCollectionAwaitedDownFailureReadout.pastFailureFlag_adapted
      rate rewards C_star C_h control0 n
  have hpreSet := measurableSet_preimage hpre' (measurableSet_singleton true)
  have hpostSet := measurableSet_preimage hpost (measurableSet_singleton true)
  apply measurable_to_bool
  change MeasurableSet[
    ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (n + 1)]
    {z : Z (p := p) | decoderPastFlag rate rewards C_star C_h n hn z = true}
  have heq : {z : Z (p := p) |
      decoderPastFlag rate rewards C_star C_h n hn z = true} =
      {z | ReferencePrelaunchDownDecisionReadout.prelaunchPastDecoderFlag
          rate rewards C_star C_h z n hn = true} ∪
        {z | ReferenceFirstCollectionAwaitedDownFailureReadout.pastFailureFlag
          rate rewards C_star C_h n z = true} := by
    ext z
    simp [decoderPastFlag]
  rw [heq]
  exact hpreSet.union hpostSet

/-- The kept-date test is measurable in the pre-round source-prefix field. The
analysis field used to obtain the prelaunch factor is included in that field;
it is never identified with a player-local sigma field. -/
theorem decoderDateKeptAt_measurable_preRound
    (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T) :
    MeasurableSet[
      ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0
        (t.val + 1)]
      {z : Z (p := p) | decoderDateKeptAt rate rewards C_star C_h z t} := by
  have hn : t.val ≤ p.T := Nat.le_of_lt t.isLt
  have hgate := decoderPastFlag_adapted rate rewards C_star C_h control0 t.val hn
  have hset : {z : Z (p := p) | decoderDateKeptAt rate rewards C_star C_h z t} =
      (fun z : Z (p := p) => decoderPastFlag rate rewards C_star C_h t.val hn z) ⁻¹'
        {false} := by
    ext z
    change decoderDateKeptAt rate rewards C_star C_h z t ↔
      decoderPastFlag rate rewards C_star C_h t.val hn z = false
    exact decoderDateKeptAt_iff_gate_false rate rewards C_star C_h z t
  rw [hset]
  exact measurableSet_preimage hgate (measurableSet_singleton false)

end Bandits.Support.ReferenceFirstCollectionInclusiveDecoderStop

end
