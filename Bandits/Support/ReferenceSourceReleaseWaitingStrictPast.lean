/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceSourceReleaseWaitingReadouts

import Lean.Elab.Tactic.Omega

/-!
# Strict-past original-source release readouts

Sources: `sources/zip4/manuscript/05_binary_transport.tex:74-88,180-240,293-348`,
`sources/zip4/manuscript/06_interruptions.tex:435-492`,
`sources/zip4/manuscript/07_public_setup.tex:121-164`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-79`.

The source maps below retain the existing whole source event and the exact
retained-launch factor.  The only measurable space added here is the pullback
of R's existing strict-past space along that factor; it is not identified with
the source filtration.  No probability law, stopping property, or conditional
service estimate is asserted.

The later consumers are the task and total-charge conditional-expectation
bounds in `PhaseStartConditionalWaiting`. Their genuine source probability,
pre-round history/filtration, inclusive stopping support, conditional service,
and quota inputs remain separate obligations. In particular these results
assert no predictability of physical flags, future gate endpoints, or an
arbitrary endpoint query.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped Classical

namespace Bandits.Support.ReferenceSourceReleaseWaitingStrictPast

variable {p : ConstructorDimensions.Parameters}

abbrev SourceEvent (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) :=
  ReferenceSourceReleaseWaitingReadouts.SourceEvent rate rewards C_star C_h s

abbrev SourceFiber (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (q : Fin (ConstructorDimensions.M p)) :=
  ReferenceSourceReleaseWaitingReadouts.SourceFiber rate rewards C_star C_h s q

variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ) (s : ℕ) (hs : s ≤ p.T)

/-- The original source event's exact selected-row fiber, as in the accepted
readouts root. -/
abbrev E (q : Fin (ConstructorDimensions.M p)) :=
  SourceFiber rate rewards C_star C_h s q

/-- The retained-launch map already reconstructed by the accepted source
readouts module. -/
abbrev rho (q : Fin (ConstructorDimensions.M p)) (t : Fin p.T)
    (hst : s ≤ t.val) (control0 : ContinuousLearningRows.TimeControl p) :=
  ReferenceSourceReleaseWaitingReadouts.retainedLaunchOfSource
    rate rewards C_star C_h s q t hst control0

/-- The only sigma algebra used below: R's existing strict-past sigma algebra
pulled back along the literal source-to-retained-launch map.  It keeps every
side coordinate in the source fiber and carries no source-filtration claim. -/
abbrev sourceStrictPastSpace (q : Fin (ConstructorDimensions.M p))
    (t : Fin p.T) (hst : s ≤ t.val)
    (control0 : ContinuousLearningRows.TimeControl p) :
    MeasurableSpace (E rate rewards C_star C_h s q) :=
  (ReferenceReleaseStrictPastFactor.strictPastSpace rate rewards C_star C_h
    q t s hst control0).comap (rho rate rewards C_star C_h s q t hst control0)

/-- C's gate is the first coordinate of its actual source entry. -/
private theorem calendarGate_eq_entry_fst
    (z : SourceEvent rate rewards C_star C_h s) (b k : ℕ) :
    ReferenceLocalReleaseCalendarCounts.calendarGate rate z.val rewards C_star C_h
      z.property.1 s (p.T - s) z.property.2 (by omega) b k =
    (ReferenceLocalReleaseCalendarCounts.calendarEntry rate z.val rewards C_star C_h
      z.property.1 s (p.T - s) z.property.2 (by omega) b k).map Prod.fst := by
  unfold ReferenceLocalReleaseCalendarCounts.calendarGate
    ReferenceLocalReleaseCalendarCounts.calendarEntry
  rw [Option.map_map]
  cases ReferenceLocalReleaseCalendarCounts.calendarRecord rate z.val rewards C_star C_h
      z.property.1 s (p.T - s) z.property.2 (by omega) k <;>
    rfl

/-- The pending projection used by W: absent entries, false gates, and a true
gate with no pending set remain distinct in the source calendar entry. -/
def pendingProjection :
    Option (Bool × Option (Finset (Fin (p.m - 1)))) → Option (Finset (Fin (p.m - 1)))
  | some (true, some pending) => some pending
  | _ => none

/-- A true gate with an empty pending set is an observed `some ∅`.
The full entry also distinguishes a false gate from an absent record. -/
theorem pendingProjection_true_empty :
    pendingProjection (p := p) (some (true, some ∅)) = some ∅ := rfl

/-- Measurability of the finite projection through the actual option-sum
measurable structure. -/
theorem measurable_pendingProjection : Measurable (pendingProjection (p := p)) := by
  let A := Bool × Option (Finset (Fin (p.m - 1)))
  let B := Option (Finset (Fin (p.m - 1)))
  let onSome : A → B := fun z => if z.1 = true then z.2 else none
  have hgate : MeasurableSet {z : A | z.1 = true} :=
    measurable_fst (measurableSet_singleton true)
  have honSome : Measurable onSome :=
    Measurable.ite hgate measurable_snd measurable_const
  let onSum : A ⊕ PUnit → B := Sum.elim onSome (fun _ => none)
  have honSum : Measurable onSum := honSome.sumElim measurable_const
  let optionSplit := Equiv.optionEquivSumPUnit A
  have hsplit : @Measurable (Option A) (A ⊕ PUnit)
      LaterAssignmentStartMeasurability.optionMeasurableSpace inferInstance optionSplit :=
    comap_measurable _
  have h := honSum.comp hsplit
  convert h using 1
  funext z
  cases z with
  | none => rfl
  | some z =>
      rcases z with ⟨gate, pending⟩
      cases gate <;> cases pending <;> rfl

/-- The `getD ∅` follower-membership indicator is measurable on the original
optional finite-set carrier. -/
private theorem measurable_getD_empty_mem (i : Fin (p.m - 1)) :
    Measurable (fun pending : Option (Finset (Fin (p.m - 1))) =>
      decide (i ∈ pending.getD ∅)) := by
  let onSome : Finset (Fin (p.m - 1)) → Bool := fun pending => decide (i ∈ pending)
  have honSome : Measurable onSome := measurable_of_countable _
  let onSum : Finset (Fin (p.m - 1)) ⊕ PUnit → Bool :=
    Sum.elim onSome (fun _ => false)
  have honSum : Measurable onSum := honSome.sumElim measurable_const
  let optionSplit := Equiv.optionEquivSumPUnit (Finset (Fin (p.m - 1)))
  have hsplit : @Measurable (Option (Finset (Fin (p.m - 1))))
      (Finset (Fin (p.m - 1)) ⊕ PUnit)
      LaterAssignmentStartMeasurability.optionMeasurableSpace inferInstance optionSplit :=
    comap_measurable _
  have h := honSum.comp hsplit
  convert h using 1
  funext z
  cases z with
  | none => simp [onSome, onSum, optionSplit, Equiv.optionEquivSumPUnit]
  | some pending => simp [onSome, onSum, optionSplit, Equiv.optionEquivSumPUnit]

/-- The follower-membership event is measurable on the project's actual
optional finite-set sigma algebra. -/
private theorem measurableSet_getD_empty_mem (i : Fin (p.m - 1)) :
    MeasurableSet {pending : Option (Finset (Fin (p.m - 1))) |
      i ∈ pending.getD ∅} := by
  let mem : Option (Finset (Fin (p.m - 1))) → Bool :=
    fun pending => decide (i ∈ pending.getD ∅)
  have hmem : Measurable mem := measurable_getD_empty_mem (p := p) i
  have heq : {pending : Option (Finset (Fin (p.m - 1))) |
      i ∈ pending.getD ∅} = mem ⁻¹' {true} := by
    ext pending
    simp [mem]
  rw [heq]
  exact measurableSet_preimage hmem (measurableSet_singleton true)

section ObservedPrefix

variable (q : Fin (ConstructorDimensions.M p)) (t : Fin p.T)
  (hst : s ≤ t.val) (control0 : ContinuousLearningRows.TimeControl p)

private theorem gateAlpha_le_iff_support_witness
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (b n : ℕ) (hn : n < p.T + 1) :
    ReferenceLocalReleaseGateChronology.gateAlpha b records ≤ n ↔
      ∃ v, v ∈ ReferenceLocalReleaseGateChronology.gateSupport b records ∧ v ≤ n := by
  classical
  let support := ReferenceLocalReleaseGateChronology.gateSupport b records
  by_cases hne : support.Nonempty
  · change (if h : support.Nonempty then support.min' h else p.T + 1) ≤ n ↔ _
    rw [dite_eq_left hne]
    constructor
    · intro h
      exact ⟨support.min' hne, Finset.min'_mem support hne, h⟩
    · rintro ⟨v, hv, hvn⟩
      exact (Finset.min'_le support v hv).trans hvn
  · have hempty : support = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    change (if h : support.Nonempty then support.min' h else p.T + 1) ≤ n ↔
      ∃ v, v ∈ support ∧ v ≤ n
    rw [dite_eq_right hne]
    rw [hempty]
    constructor
    · intro h
      omega
    · rintro ⟨v, hv, _⟩
      simp at hv

private theorem source_calendar_gate_factor_for_sublevel
    (z : E rate rewards C_star C_h s q) (b : ℕ)
    (j : Fin (t.val - s + 1)) :
    ReferenceLocalReleaseCalendarCounts.calendarGate rate z.val.val rewards C_star C_h
      z.val.property.1 s (p.T - s) z.val.property.2 (by omega) b (s + j.val) =
    some (ReferenceReleaseStrictPastFactor.releaseEntries rate rewards C_star C_h
      q t s hst control0 b (rho rate rewards C_star C_h s q t hst control0 z) j).1 := by
  have hj := j.isLt
  have hk : s ≤ s + j.val := by omega
  have hkt : s + j.val ≤ t.val := by omega
  have hindex : j.val = s + j.val - s := by omega
  rw [calendarGate_eq_entry_fst rate rewards C_star C_h s hs z.val b (s + j.val)]
  rw [ReferenceSourceReleaseWaitingReadouts.source_calendar_entry_factor
    rate rewards C_star C_h s q t hst control0 z b (s + j.val) hk hkt j hindex]
  rfl

/-- The actual source gate sublevel is witnessed by one of the retained
coordinates through `t`.  The proof uses the original run's gate support and
B's actual source entry factors; it does not truncate the full alpha search. -/
private theorem source_gate_sublevel_iff_release_entry
    (z : E rate rewards C_star C_h s q) (b n : ℕ) (hn : n ≤ t.val + 1) :
    ReferenceLocalReleaseWaitingPaths.localGateAlpha rate rewards C_star C_h s hs b z.val ≤ n ↔
      ∃ j : Fin (t.val - s + 1),
        (ReferenceReleaseStrictPastFactor.releaseEntries rate rewards C_star C_h
          q t s hst control0 b (rho rate rewards C_star C_h s q t hst control0 z) j).1 = true ∧
        s + j.val + 1 ≤ n := by
  have hnT : n < p.T + 1 := by have ht := t.isLt; omega
  let run := ReferenceLocalReleaseWaitingPaths.sourceRunAtLaunch
    rate rewards C_star C_h s hs z.val
  change ReferenceLocalReleaseGateChronology.gateAlpha b run.records ≤ n ↔ _
  rw [gateAlpha_le_iff_support_witness rate run.records b n hnT]
  constructor
  · rintro ⟨v, hv, hvn⟩
    obtain ⟨r, hr, hgate, rfl⟩ :=
      (ReferenceLocalReleaseGateChronology.mem_gateSupport b v run.records).mp hv
    obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hr
    have hlen : run.records.length = p.T - s := by
      have hrun := ReferenceActivePhysicalHorizon.run_record_count
        (ReferenceLocalReleaseGateChronology.sourceSeed rate z.val.val rewards C_star C_h
          z.val.property.1)
        z.val.val.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z.val.val)
        rewards s (p.T - s) (by omega)
        (by simpa only [z.val.property.2] using
          (ReferenceLocalReleaseGateChronology.canonical_seed_release_inputs
            rate z.val.val rewards C_star C_h z.val.property.1).2.1)
      simpa only [run, ReferenceLocalReleaseWaitingPaths.sourceRunAtLaunch,
        ReferenceLocalReleaseGateChronology.sourceRun] using hrun
    have hi' : i < p.T - s := by rw [← hlen]; exact hi
    let index : Fin (p.T - s) := ⟨i, hi'⟩
    have hround := ReferenceLocalReleasePendingHistory.sourceRecord_sourceRound
      rate z.val.val rewards C_star C_h z.val.property.1 s (p.T - s) z.val.property.2
      (by omega) index
    have htimeIndex : (run.records[i]'hi).input.time.val = s + i := by
      simpa [run, ReferenceLocalReleaseWaitingPaths.sourceRunAtLaunch,
        ReferenceLocalReleasePendingHistory.sourceRecord,
        ReferenceLocalReleaseGateChronology.sourceRun] using hround.1
    have htime : r.input.time.val = s + i := by
      rw [← hget]
      exact htimeIndex
    have htimeBound : r.input.time.val ≤ t.val := by omega
    let j : Fin (t.val - s + 1) := ⟨i, by omega⟩
    have hround : s + j.val = r.input.time.val := by dsimp [j]; omega
    have hrecord :=
      (ReferenceLocalReleaseCalendarCounts.calendarRecord_eq_some_iff
        rate z.val.val rewards C_star C_h z.val.property.1 s (p.T - s) z.val.property.2
        (by omega) r.input.time.val r).mpr ⟨by
          simpa only [run, ReferenceLocalReleaseWaitingPaths.sourceRunAtLaunch,
            ReferenceLocalReleaseCalendarCounts.SourceRun,
            ReferenceLocalReleaseGateChronology.sourceRun,
            ReferenceLocalReleaseGateChronology.Record] using hr,
        rfl⟩
    have hcalendarGate :
        ReferenceLocalReleaseCalendarCounts.calendarGate rate z.val.val rewards C_star C_h
          z.val.property.1 s (p.T - s) z.val.property.2 (by omega) b r.input.time.val = some true := by
      unfold ReferenceLocalReleaseCalendarCounts.calendarGate
      rw [hrecord]
      simp [hgate]
    have hfactor := source_calendar_gate_factor_for_sublevel
      rate rewards C_star C_h s hs q t hst control0 z b j
    rw [← hround] at hcalendarGate
    rw [hfactor] at hcalendarGate
    refine ⟨j, ?_, ?_⟩
    · exact Option.some.inj hcalendarGate
    · omega
  · rintro ⟨j, hgate, hjn⟩
    let k := s + j.val
    let actual := ReferenceAssignmentPayloadChronology.actualRunRecordAt
      (ReferenceLocalReleaseGateChronology.sourceSeed rate z.val.val rewards C_star C_h
        z.val.property.1)
      z.val.val.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z.val.val)
      rewards s (k - s) (by omega)
      (by simpa only [z.val.property.2] using
        (ReferenceLocalReleaseGateChronology.canonical_seed_release_inputs
          rate z.val.val rewards C_star C_h z.val.property.1).2.1)
    have hrecord :
        ReferenceLocalReleaseCalendarCounts.calendarRecord rate z.val.val rewards C_star C_h
          z.val.property.1 s (p.T - s) z.val.property.2 (by omega) k = some actual := by
      simpa only [actual, k] using
        ReferenceSourceReleaseWaitingReadouts.source_calendar_record_eq_actual_run_record
          rate rewards C_star C_h s q t hst z k (by omega) (by omega)
    have hcalendarGate :
        ReferenceLocalReleaseCalendarCounts.calendarGate rate z.val.val rewards C_star C_h
          z.val.property.1 s (p.T - s) z.val.property.2 (by omega) b k = some true := by
      have hfactor := source_calendar_gate_factor_for_sublevel
        rate rewards C_star C_h s hs q t hst control0 z b j
      rw [hfactor]
      simp [hgate]
    have hactualGate : ReferenceRetainedReleasePhaseObservation.localReleaseGate rate b
        actual.input.time
        (ReferenceActivePhysicalStepMeasurability.encodeState actual.input.state) = true := by
      unfold ReferenceLocalReleaseCalendarCounts.calendarGate at hcalendarGate
      rw [hrecord] at hcalendarGate
      simpa using hcalendarGate
    have hrecordFacts :=
      (ReferenceLocalReleaseCalendarCounts.calendarRecord_eq_some_iff
        rate z.val.val rewards C_star C_h z.val.property.1 s (p.T - s) z.val.property.2
        (by omega) k actual).mp hrecord
    have hr : actual ∈ run.records := by
      simpa only [run, ReferenceLocalReleaseWaitingPaths.sourceRunAtLaunch,
        ReferenceLocalReleaseCalendarCounts.SourceRun,
        ReferenceLocalReleaseGateChronology.sourceRun,
        ReferenceLocalReleaseGateChronology.Record] using hrecordFacts.1
    have hsupport :=
      (ReferenceLocalReleaseGateChronology.mem_gateSupport b (k + 1) run.records).mpr
        ⟨actual, hr, hactualGate, by
          simpa [k, actual] using hrecordFacts.2⟩
    exact ⟨k + 1, hsupport, by dsimp [k] at *; omega⟩

/-- The source sublevel is the inverse image of O's actual finite first-gate
search. The bound `n ≤ t+1` is essential: it includes the current incoming
record while excluding any future first gate from the comparison. -/
theorem source_localGateAlpha_sublevel_eq_firstLocalReleaseGateRound
    (b n : ℕ) (hn : n ≤ t.val + 1) :
    {z : E rate rewards C_star C_h s q |
      ReferenceLocalReleaseWaitingPaths.localGateAlpha rate rewards C_star C_h s hs b z.val ≤ n} =
    (rho rate rewards C_star C_h s q t hst control0) ⁻¹'
      {x : ReferenceRetainedReleasePhaseObservation.LaunchStart
        rate rewards C_star C_h q t s hst control0 |
        ReferenceRetainedReleasePhaseObservation.firstLocalReleaseGateRound
          rate rewards C_star C_h q t s hst control0 x b ≤ n} := by
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_preimage]
  rw [source_gate_sublevel_iff_release_entry rate rewards C_star C_h s hs q t hst control0
    z b n hn]
  rw [ReferenceRetainedReleasePhaseObservation.firstLocalReleaseGateRound_le_iff
    rate rewards C_star C_h q t s hst control0
    (rho rate rewards C_star C_h s q t hst control0 z) b n (by
      have ht := t.isLt
      omega)]
  simp only [ReferenceReleaseStrictPastFactor.releaseEntries,
    ReferenceRetainedReleasePhaseObservation.localReleaseEntry]

/-- Measurability of the actual original-source alpha sublevel on the
strict-past pullback. -/
theorem measurableSet_source_localGateAlpha_sublevel_strictPast
    (b n : ℕ) (hn : n ≤ t.val + 1) :
    MeasurableSet[sourceStrictPastSpace rate rewards C_star C_h s q t hst control0]
      {z : E rate rewards C_star C_h s q |
        ReferenceLocalReleaseWaitingPaths.localGateAlpha rate rewards C_star C_h s hs b z.val ≤ n} := by
  rw [source_localGateAlpha_sublevel_eq_firstLocalReleaseGateRound
    rate rewards C_star C_h s hs q t hst control0 b n hn]
  exact (ReferenceReleaseStrictPastFactor.measurableSet_firstLocalReleaseGateRound_le_strictPast
    rate rewards C_star C_h q t s hst control0 b n).preimage
      (comap_measurable (rho rate rewards C_star C_h s q t hst control0))

/-- The full-span original C entry at each coordinate of R's inclusive
`s,...,t` vector is exactly R's release entry composed with `rho`. -/
theorem source_calendar_entry_factor_strictPast
    (z : E rate rewards C_star C_h s q) (b : ℕ)
    (j : Fin (t.val - s + 1)) :
    ReferenceLocalReleaseCalendarCounts.calendarEntry rate z.val.val rewards C_star C_h
      z.val.property.1 s (p.T - s) z.val.property.2 (by omega) b (s + j.val) =
    some (ReferenceReleaseStrictPastFactor.releaseEntries rate rewards C_star C_h
      q t s hst control0 b (rho rate rewards C_star C_h s q t hst control0 z) j) := by
  have hj := j.isLt
  have hk : s ≤ s + j.val := by omega
  have hkt : s + j.val ≤ t.val := by omega
  have hindex : j.val = s + j.val - s := by omega
  exact ReferenceSourceReleaseWaitingReadouts.source_calendar_entry_factor
    rate rewards C_star C_h s q t hst control0 z b (s + j.val) hk hkt j hindex

/-- The normalized factor gives the same original calendar entry.  This is
R's literal normalization identity, not a replacement source or a baseline
source identification. -/
theorem source_calendar_entry_factor_normalize_strictPast
    (z : E rate rewards C_star C_h s q) (b : ℕ)
    (j : Fin (t.val - s + 1)) :
    ReferenceLocalReleaseCalendarCounts.calendarEntry rate z.val.val rewards C_star C_h
      z.val.property.1 s (p.T - s) z.val.property.2 (by omega) b (s + j.val) =
    some (ReferenceReleaseStrictPastFactor.releaseEntries rate rewards C_star C_h
      q t s hst control0 b
        (ReferenceReleaseStrictPastFactor.normalize rate rewards C_star C_h q t s hst
          control0 (rho rate rewards C_star C_h s q t hst control0 z)) j) := by
  have hj := j.isLt
  have hk : s ≤ s + j.val := by omega
  have hkt : s + j.val ≤ t.val := by omega
  have hindex : j.val = s + j.val - s := by omega
  exact ReferenceSourceReleaseWaitingReadouts.source_calendar_entry_factor_normalize
    rate rewards C_star C_h s q t hst control0 z b (s + j.val) hk hkt j hindex

/-- C's actual gate projection factors through the exact retained R entry. -/
theorem source_calendar_gate_factor_strictPast
    (z : E rate rewards C_star C_h s q) (b : ℕ)
    (j : Fin (t.val - s + 1)) :
    ReferenceLocalReleaseCalendarCounts.calendarGate rate z.val.val rewards C_star C_h
      z.val.property.1 s (p.T - s) z.val.property.2 (by omega) b (s + j.val) =
    some (ReferenceReleaseStrictPastFactor.releaseEntries rate rewards C_star C_h
      q t s hst control0 b (rho rate rewards C_star C_h s q t hst control0 z) j).1 := by
  rw [calendarGate_eq_entry_fst rate rewards C_star C_h s hs z.val b (s + j.val)]
  rw [source_calendar_entry_factor_strictPast rate rewards C_star C_h s hs q t hst control0
    z b j]
  rfl

/-- The actual gate projection also factors through the normalized entry. -/
theorem source_calendar_gate_factor_normalize_strictPast
    (z : E rate rewards C_star C_h s q) (b : ℕ)
    (j : Fin (t.val - s + 1)) :
    ReferenceLocalReleaseCalendarCounts.calendarGate rate z.val.val rewards C_star C_h
      z.val.property.1 s (p.T - s) z.val.property.2 (by omega) b (s + j.val) =
    some (ReferenceReleaseStrictPastFactor.releaseEntries rate rewards C_star C_h
      q t s hst control0 b
        (ReferenceReleaseStrictPastFactor.normalize rate rewards C_star C_h q t s hst
          control0 (rho rate rewards C_star C_h s q t hst control0 z)) j).1 := by
  rw [calendarGate_eq_entry_fst rate rewards C_star C_h s hs z.val b (s + j.val)]
  rw [source_calendar_entry_factor_normalize_strictPast rate rewards C_star C_h s hs q t hst
    control0 z b j]
  rfl

/-- W's uncut pending readout is the literal true-gate/some-pending
projection of the same R entry. -/
theorem source_calendar_pending_projection_strictPast
    (z : E rate rewards C_star C_h s q) (b : ℕ)
    (j : Fin (t.val - s + 1)) :
    ReferenceLocalReleaseWaitingPaths.calendarPendingReadout rate rewards C_star C_h s hs b
      z.val (s + j.val) =
    pendingProjection (some (ReferenceReleaseStrictPastFactor.releaseEntries
      rate rewards C_star C_h q t s hst control0 b
        (rho rate rewards C_star C_h s q t hst control0 z) j)) := by
  change ReferenceLocalReleaseCalendarCounts.calendarPending rate z.val.val rewards C_star C_h
    z.val.property.1 s (p.T - s) z.val.property.2 (by omega) b (s + j.val) = _
  rw [ReferenceLocalReleaseCalendarCounts.calendarPending]
  rw [source_calendar_entry_factor_strictPast rate rewards C_star C_h s hs q t hst control0
    z b j]
  rfl

/-- The same pending projection after R normalization. -/
theorem source_calendar_pending_projection_normalize_strictPast
    (z : E rate rewards C_star C_h s q) (b : ℕ)
    (j : Fin (t.val - s + 1)) :
    ReferenceLocalReleaseWaitingPaths.calendarPendingReadout rate rewards C_star C_h s hs b
      z.val (s + j.val) =
    pendingProjection (some (ReferenceReleaseStrictPastFactor.releaseEntries rate rewards C_star C_h
      q t s hst control0 b
        (ReferenceReleaseStrictPastFactor.normalize rate rewards C_star C_h q t s hst
          control0 (rho rate rewards C_star C_h s q t hst control0 z)) j)) := by
  change ReferenceLocalReleaseCalendarCounts.calendarPending rate z.val.val rewards C_star C_h
    z.val.property.1 s (p.T - s) z.val.property.2 (by omega) b (s + j.val) = _
  rw [ReferenceLocalReleaseCalendarCounts.calendarPending]
  rw [source_calendar_entry_factor_normalize_strictPast rate rewards C_star C_h s hs q t hst
    control0 z b j]
  rfl

/-- The actual entry vector, on the original full-span source event and with
the literal zero-based coordinates `s+j`. -/
theorem measurable_source_calendar_entries_strictPast (b : ℕ) :
    Measurable[sourceStrictPastSpace rate rewards C_star C_h s q t hst control0]
      (fun z : E rate rewards C_star C_h s q =>
        fun j : Fin (t.val - s + 1) =>
          ReferenceLocalReleaseCalendarCounts.calendarEntry rate z.val.val rewards C_star C_h
            z.val.property.1 s (p.T - s) z.val.property.2 (by omega) b (s + j.val)) := by
  let : MeasurableSpace (E rate rewards C_star C_h s q) :=
    sourceStrictPastSpace rate rewards C_star C_h s q t hst control0
  let rhoMap := rho rate rewards C_star C_h s q t hst control0
  let entries : E rate rewards C_star C_h s q →
      Fin (t.val - s + 1) → Bool × Option (Finset (Fin (p.m - 1))) :=
    fun z => ReferenceReleaseStrictPastFactor.releaseEntries rate rewards C_star C_h
      q t s hst control0 b (rhoMap z)
  have hentries : Measurable entries := by
    change Measurable[(ReferenceReleaseStrictPastFactor.strictPastSpace rate rewards C_star C_h
      q t s hst control0).comap rhoMap] entries
    exact (ReferenceReleaseStrictPastFactor.measurable_releaseEntries rate rewards C_star C_h
      q t s hst control0 b).comp (comap_measurable rhoMap)
  have hsome : Measurable (some :
      Bool × Option (Finset (Fin (p.m - 1))) →
        Option (Bool × Option (Finset (Fin (p.m - 1))))) := by
    apply measurable_comap_iff.mpr
    exact measurable_inl
  apply measurable_pi_iff.mpr
  intro j
  have hcoord : Measurable[sourceStrictPastSpace rate rewards C_star C_h s q t hst control0]
      (fun z : E rate rewards C_star C_h s q => some (entries z j)) :=
    hsome.comp ((measurable_pi_apply j).comp hentries)
  have hfactor :
      (fun z : E rate rewards C_star C_h s q =>
        ReferenceLocalReleaseCalendarCounts.calendarEntry rate z.val.val rewards C_star C_h
          z.val.property.1 s (p.T - s) z.val.property.2 (by omega) b (s + j.val)) =
      fun z => some (entries z j) := by
    funext z
    exact source_calendar_entry_factor_strictPast rate rewards C_star C_h s hs q t hst control0
      z b j
  rw [hfactor]
  exact hcoord

/-- Countability of the timestamp gives a joint entry readout on the SAME
source strict-past pullback, with its ordinary product space on `ℕ`. -/
theorem measurable_source_calendar_entries_strictPast_joint :
    Measurable[(sourceStrictPastSpace rate rewards C_star C_h s q t hst control0).prod
      (inferInstance : MeasurableSpace ℕ)]
      (fun zb : E rate rewards C_star C_h s q × ℕ =>
        fun j : Fin (t.val - s + 1) =>
          ReferenceLocalReleaseCalendarCounts.calendarEntry rate zb.1.val.val rewards C_star C_h
            zb.1.val.property.1 s (p.T - s) zb.1.val.property.2 (by omega)
            zb.2 (s + j.val)) := by
  let : MeasurableSpace (E rate rewards C_star C_h s q) :=
    sourceStrictPastSpace rate rewards C_star C_h s q t hst control0
  exact measurable_from_prod_countable_left fun b =>
    measurable_source_calendar_entries_strictPast rate rewards C_star C_h s hs q t hst
      control0 b

/-- The uncut current-round pending readout is measurable in the pullback
strict-past space. -/
theorem measurable_source_calendar_pending_strictPast (b : ℕ) :
    Measurable[sourceStrictPastSpace rate rewards C_star C_h s q t hst control0]
      (fun z : E rate rewards C_star C_h s q =>
        ReferenceLocalReleaseWaitingPaths.calendarPendingReadout rate rewards C_star C_h s hs b
          z.val t.val) := by
  let j : Fin (t.val - s + 1) := ⟨t.val - s, by omega⟩
  let : MeasurableSpace (E rate rewards C_star C_h s q) :=
    sourceStrictPastSpace rate rewards C_star C_h s q t hst control0
  have hvector :=
    measurable_source_calendar_entries_strictPast rate rewards C_star C_h s hs q t hst
      control0 b
  have hentry : Measurable[sourceStrictPastSpace rate rewards C_star C_h s q t hst control0]
      (fun z : E rate rewards C_star C_h s q =>
        ReferenceLocalReleaseCalendarCounts.calendarEntry rate z.val.val rewards C_star C_h
          z.val.property.1 s (p.T - s) z.val.property.2 (by omega) b t.val) := by
    have h := (measurable_pi_apply j).comp hvector
    have hcoord : s + j.val = t.val := by dsimp [j]; omega
    change Measurable (fun z : E rate rewards C_star C_h s q =>
      ReferenceLocalReleaseCalendarCounts.calendarEntry rate z.val.val rewards C_star C_h
        z.val.property.1 s (p.T - s) z.val.property.2 (by omega) b (s + j.val)) at h
    rw [hcoord] at h
    exact h
  have hproject := measurable_pendingProjection (p := p)
  have heq :
      (fun z : E rate rewards C_star C_h s q =>
        ReferenceLocalReleaseWaitingPaths.calendarPendingReadout rate rewards C_star C_h s hs b
          z.val t.val) =
      fun z => pendingProjection
        (ReferenceLocalReleaseCalendarCounts.calendarEntry rate z.val.val rewards C_star C_h
          z.val.property.1 s (p.T - s) z.val.property.2 (by omega) b t.val) := by
    funext z
    have hfactor := source_calendar_pending_projection_strictPast rate rewards C_star C_h s hs q t
      hst control0 z b j
    have hcoord : s + j.val = t.val := by dsimp [j]; omega
    have hentryFactor := source_calendar_entry_factor_strictPast rate rewards C_star C_h s hs q t
      hst control0 z b j
    rw [← hcoord, hfactor, hentryFactor]
  rw [heq]
  exact hproject.comp hentry

/-- Membership in the `getD ∅` pending set is measurable for every actual
follower index at every coordinate in the observed prefix. -/
theorem measurable_source_pending_getD_empty_membership_strictPast
    (b : ℕ) (j : Fin (t.val - s + 1)) (i : Fin (p.m - 1)) :
    MeasurableSet[sourceStrictPastSpace rate rewards C_star C_h s q t hst control0]
      {z : E rate rewards C_star C_h s q |
        i ∈ (ReferenceLocalReleaseWaitingPaths.calendarPendingReadout rate rewards C_star C_h
          s hs b z.val (s + j.val)).getD ∅} := by
  let : MeasurableSpace (E rate rewards C_star C_h s q) :=
    sourceStrictPastSpace rate rewards C_star C_h s q t hst control0
  have hvector :=
    measurable_source_calendar_entries_strictPast rate rewards C_star C_h s hs q t hst
      control0 b
  let pending : E rate rewards C_star C_h s q → Option (Finset (Fin (p.m - 1))) :=
    fun z => ReferenceLocalReleaseWaitingPaths.calendarPendingReadout rate rewards C_star C_h
      s hs b z.val (s + j.val)
  have hpending : Measurable[sourceStrictPastSpace rate rewards C_star C_h s q t hst control0]
      pending := by
    let project : Option (Bool × Option (Finset (Fin (p.m - 1)))) →
        Option (Finset (Fin (p.m - 1))) := pendingProjection (p := p)
    have hproject : Measurable project := measurable_pendingProjection (p := p)
    have hentry := (measurable_pi_apply j).comp hvector
    have heq : pending = fun z => project
        (ReferenceLocalReleaseCalendarCounts.calendarEntry rate z.val.val rewards C_star C_h
          z.val.property.1 s (p.T - s) z.val.property.2 (by omega) b (s + j.val)) := by
      funext z
      change ReferenceLocalReleaseWaitingPaths.calendarPendingReadout rate rewards C_star C_h s hs b
        z.val (s + j.val) = project
          (ReferenceLocalReleaseCalendarCounts.calendarEntry rate z.val.val rewards C_star C_h
            z.val.property.1 s (p.T - s) z.val.property.2 (by omega) b (s + j.val))
      rw [source_calendar_pending_projection_strictPast rate rewards C_star C_h s hs q t hst
        control0 z b j]
      rw [source_calendar_entry_factor_strictPast rate rewards C_star C_h s hs q t hst
        control0 z b j]
    rw [heq]
    exact hproject.comp hentry
  have hset : MeasurableSet (pending ⁻¹' {P : Option (Finset (Fin (p.m - 1))) |
      i ∈ P.getD ∅}) :=
    (measurableSet_getD_empty_mem (p := p) i).preimage hpending
  have heq : {z : E rate rewards C_star C_h s q |
      i ∈ (ReferenceLocalReleaseWaitingPaths.calendarPendingReadout rate rewards C_star C_h
        s hs b z.val (s + j.val)).getD ∅} =
      pending ⁻¹' {P : Option (Finset (Fin (p.m - 1))) | i ∈ P.getD ∅} := by
    ext z
    rfl
  rw [heq]
  exact hset

/-- In particular, membership at the current inclusive incoming coordinate
is measurable for each real follower. No endpoint cut is applied. -/
theorem measurable_source_current_pending_getD_empty_membership_strictPast
    (b : ℕ) (i : Fin (p.m - 1)) :
    MeasurableSet[sourceStrictPastSpace rate rewards C_star C_h s q t hst control0]
      {z : E rate rewards C_star C_h s q |
        i ∈ (ReferenceLocalReleaseWaitingPaths.calendarPendingReadout rate rewards C_star C_h
          s hs b z.val t.val).getD ∅} := by
  let j : Fin (t.val - s + 1) := ⟨t.val - s, by omega⟩
  have h := measurable_source_pending_getD_empty_membership_strictPast
    rate rewards C_star C_h s hs q t hst control0 b j i
  have hcoord : s + j.val = t.val := by dsimp [j]; omega
  simpa only [hcoord] using h

private theorem launchSource_rho_eq_replaceSourceControl
    (z : E rate rewards C_star C_h s q) :
    ReferenceReleaseStrictPastFactor.launchSource rate rewards C_star C_h q t s hst control0
      (rho rate rewards C_star C_h s q t hst control0 z) =
    ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z.val.val control0 := by
  have hreconstruction :=
    ReferenceSourceReleaseWaitingReadouts.source_launch_reconstruction
      rate rewards C_star C_h s q t hst control0 z
  have hselected :
      ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p z.val.val = q := by
    calc
      _ = ActualInitializationPhysicalStep.selectedRowIndex p z.val.val :=
        ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex
          p z.val.val
      _ = q := z.property
  change (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t).symm
      (control0, (rho rate rewards C_star C_h s q t hst control0 z).val) = _
  rw [hreconstruction.1]
  exact ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_replaceSourceControl
    p q t z.val.val control0 hselected

/-- On a fixed actual selected-row fiber, replacing the selected source
controls from `t` onward preserves the original crossing/elapsed event. Its
calendar entries, pending projections, and observed alpha sublevels agree
through the inclusive incoming coordinate `t`. -/
theorem replaceSelectedControlSuffix_source_fiber_invariance
    (z : E rate rewards C_star C_h s q)
    (hst : s ≤ t.val) (control0 : ContinuousLearningRows.TimeControl p)
    (suffix : Fin p.T → ContinuousLearningRows.TimeControl p) :
    ∃ z' : E rate rewards C_star C_h s q,
      z'.val.val = ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix
        z.val.val t suffix ∧
      (∀ b k, k ≤ t.val →
        ReferenceLocalReleaseCalendarCounts.calendarEntry rate z.val.val rewards C_star C_h
          z.val.property.1 s (p.T - s) z.val.property.2 (by omega) b k =
        ReferenceLocalReleaseCalendarCounts.calendarEntry rate z'.val.val rewards C_star C_h
          z'.val.property.1 s (p.T - s) z'.val.property.2 (by omega) b k ∧
        ReferenceLocalReleaseWaitingPaths.calendarPendingReadout rate rewards C_star C_h s hs b
          z.val k =
        ReferenceLocalReleaseWaitingPaths.calendarPendingReadout rate rewards C_star C_h s hs b
          z'.val k) ∧
      (∀ b n, n ≤ t.val + 1 →
        (ReferenceLocalReleaseWaitingPaths.localGateAlpha rate rewards C_star C_h s hs b
          z.val ≤ n ↔
        ReferenceLocalReleaseWaitingPaths.localGateAlpha rate rewards C_star C_h s hs b
          z'.val ≤ n)) := by
  let source' := ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix
    z.val.val t suffix
  let source := z.val.val
  have hpres :=
    ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix_preserves_actual_launch
      (rate := rate) rewards C_star C_h q t s hst z.val.val z.property suffix
      z.val.property.1 z.val.property.2
  dsimp only [source'] at hpres
  rcases hpres with ⟨hselected', hcross', helapsed', _⟩
  let z' : E rate rewards C_star C_h s q :=
    ⟨⟨source', ⟨hcross', helapsed'⟩⟩, hselected'⟩
  have hsourceIndex :
      ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p z.val.val = q := by
    calc
      _ = ActualInitializationPhysicalStep.selectedRowIndex p z.val.val :=
        ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex
          p z.val.val
      _ = q := z.property
  have hselectedSource :
      ActualInitializationPhysicalStep.selectedRowIndex p source = q := z.property
  have hsourceIndex' :
      ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p source' = q := by
    calc
      _ = ActualInitializationPhysicalStep.selectedRowIndex p source' :=
        ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex
          p source'
      _ = q := hselected'
  have hlaunch := launchSource_rho_eq_replaceSourceControl
    (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
    (s := s) (q := q) (t := t) (hst := hst) (control0 := control0) z
  have hlaunch' := launchSource_rho_eq_replaceSourceControl
    (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
    (s := s) (q := q) (t := t) (hst := hst) (control0 := control0) z'
  have hids :
      (ReferenceReleaseStrictPastFactor.launchSource rate rewards C_star C_h q t s hst control0
        (rho rate rewards C_star C_h s q t hst control0 z)).1.1 =
      (ReferenceReleaseStrictPastFactor.launchSource rate rewards C_star C_h q t s hst control0
        (rho rate rewards C_star C_h s q t hst control0 z')).1.1 := by
    calc
      _ = (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t source control0).1.1 :=
        congrArg (fun src : ReferenceFixedTimeSourceControlCoupling.SourceInput p => src.1.1) hlaunch
      _ = source.1.1 := ReferenceFixedTimeSourceControlCoupling.replaceSourceControl_id
        p t source control0
      _ = source'.1.1 :=
        (ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix_id
          source t suffix).symm
      _ = (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t source' control0).1.1 :=
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl_id p t source' control0).symm
      _ = _ := congrArg
        (fun src : ReferenceFixedTimeSourceControlCoupling.SourceInput p => src.1.1)
          hlaunch'.symm
  have hprivate :
      (ReferenceReleaseStrictPastFactor.launchSource rate rewards C_star C_h q t s hst control0
        (rho rate rewards C_star C_h s q t hst control0 z)).2 =
      (ReferenceReleaseStrictPastFactor.launchSource rate rewards C_star C_h q t s hst control0
        (rho rate rewards C_star C_h s q t hst control0 z')).2 := by
    calc
      _ = (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t source control0).2 :=
        congrArg (fun src : ReferenceFixedTimeSourceControlCoupling.SourceInput p => src.2) hlaunch
      _ = source.2 := ReferenceFixedTimeSourceControlCoupling.replaceSourceControl_private
        p t source control0
      _ = source'.2 :=
        (ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix_private
          source t suffix).symm
      _ = (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t source' control0).2 :=
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl_private p t source' control0).symm
      _ = _ := congrArg
        (fun src : ReferenceFixedTimeSourceControlCoupling.SourceInput p => src.2)
          hlaunch'.symm
  have hforward :
      ((ReferenceReleaseStrictPastFactor.launchSource rate rewards C_star C_h q t s hst control0
        (rho rate rewards C_star C_h s q t hst control0 z)).1.2 q).1 =
      ((ReferenceReleaseStrictPastFactor.launchSource rate rewards C_star C_h q t s hst control0
        (rho rate rewards C_star C_h s q t hst control0 z')).1.2 q).1 := by
    have hleft :
        ((ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t source control0).1.2 q).1 =
          (source.1.2 q).1 := by
      rw [← hsourceIndex]
      exact ReferenceFixedTimeSourceControlCoupling.replaceSourceControl_forward
        p t source control0
    have hmiddle : (source.1.2 q).1 = (source'.1.2 q).1 := by
      rw [← hselectedSource]
      exact (ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix_forward
        source t suffix).symm
    have hright :
        ((ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t source' control0).1.2 q).1 =
          (source'.1.2 q).1 := by
      rw [← hsourceIndex']
      exact ReferenceFixedTimeSourceControlCoupling.replaceSourceControl_forward
        p t source' control0
    calc
      _ = ((ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t source control0).1.2 q).1 :=
        congrArg (fun src : ReferenceFixedTimeSourceControlCoupling.SourceInput p =>
          (src.1.2 q).1) hlaunch
      _ = (source.1.2 q).1 := hleft
      _ = (source'.1.2 q).1 := hmiddle
      _ = ((ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t source' control0).1.2 q).1 :=
        hright.symm
      _ = _ := congrArg (fun src : ReferenceFixedTimeSourceControlCoupling.SourceInput p =>
        (src.1.2 q).1) hlaunch'.symm
  have hother : ∀ row, row ≠ q →
      (ReferenceReleaseStrictPastFactor.launchSource rate rewards C_star C_h q t s hst control0
        (rho rate rewards C_star C_h s q t hst control0 z)).1.2 row =
      (ReferenceReleaseStrictPastFactor.launchSource rate rewards C_star C_h q t s hst control0
        (rho rate rewards C_star C_h s q t hst control0 z')).1.2 row := by
    intro row hrow
    have hmiddle : source.1.2 row = source'.1.2 row := by
      have hrow' : row ≠ ActualInitializationPhysicalStep.selectedRowIndex p source := by
        rw [hselectedSource]
        exact hrow
      exact (ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix_otherRow
        source t suffix row hrow').symm
    have hleft :
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t source control0).1.2 row =
          source.1.2 row := by
      unfold ReferenceFixedTimeSourceControlCoupling.replaceSourceControl
      rw [hsourceIndex]
      simp [hrow]
    have hright :
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t source' control0).1.2 row =
          source'.1.2 row := by
      unfold ReferenceFixedTimeSourceControlCoupling.replaceSourceControl
      rw [hsourceIndex']
      simp [hrow]
    calc
      _ = (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t source control0).1.2 row :=
        congrArg (fun src : ReferenceFixedTimeSourceControlCoupling.SourceInput p => src.1.2 row)
          hlaunch
      _ = source.1.2 row := hleft
      _ = source'.1.2 row := hmiddle
      _ = (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t source' control0).1.2 row :=
        hright.symm
      _ = _ := congrArg
        (fun src : ReferenceFixedTimeSourceControlCoupling.SourceInput p => src.1.2 row)
          hlaunch'.symm
  have hbefore : ∀ v : Fin p.T, v.val < t.val →
      ((ReferenceReleaseStrictPastFactor.launchSource rate rewards C_star C_h q t s hst control0
        (rho rate rewards C_star C_h s q t hst control0 z)).1.2 q).2 v =
      ((ReferenceReleaseStrictPastFactor.launchSource rate rewards C_star C_h q t s hst control0
        (rho rate rewards C_star C_h s q t hst control0 z')).1.2 q).2 v := by
    intro v hv
    have hvne : v ≠ t := by
      intro heq
      have hval := congrArg Fin.val heq
      omega
    have hmiddle : (source.1.2 q).2 v = (source'.1.2 q).2 v := by
      rw [← hselectedSource]
      exact (ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix_control_before
        source t v suffix hv).symm
    have hleft :
        ((ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t source control0).1.2 q).2 v =
          (source.1.2 q).2 v := by
      unfold ReferenceFixedTimeSourceControlCoupling.replaceSourceControl
      rw [hsourceIndex]
      simp [hvne]
    have hright :
        ((ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t source' control0).1.2 q).2 v =
          (source'.1.2 q).2 v := by
      unfold ReferenceFixedTimeSourceControlCoupling.replaceSourceControl
      rw [hsourceIndex']
      simp [hvne]
    calc
      _ = ((ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t source control0).1.2 q).2 v :=
        congrArg (fun src : ReferenceFixedTimeSourceControlCoupling.SourceInput p =>
          (src.1.2 q).2 v) hlaunch
      _ = (source.1.2 q).2 v := hleft
      _ = (source'.1.2 q).2 v := hmiddle
      _ = ((ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t source' control0).1.2 q).2 v :=
        hright.symm
      _ = _ := congrArg (fun src : ReferenceFixedTimeSourceControlCoupling.SourceInput p =>
        (src.1.2 q).2 v) hlaunch'.symm
  have hnormalize :=
    ReferenceReleaseStrictPastFactor.normalize_eq_of_strictPast
      rate rewards C_star C_h q t s hst control0
      (rho rate rewards C_star C_h s q t hst control0 z)
      (rho rate rewards C_star C_h s q t hst control0 z')
      hids hprivate hforward hother hbefore
  have hentries (b : ℕ) :
      ReferenceReleaseStrictPastFactor.releaseEntries rate rewards C_star C_h
        q t s hst control0 b (rho rate rewards C_star C_h s q t hst control0 z) =
      ReferenceReleaseStrictPastFactor.releaseEntries rate rewards C_star C_h
        q t s hst control0 b (rho rate rewards C_star C_h s q t hst control0 z') := by
    calc
      _ = ReferenceReleaseStrictPastFactor.releaseEntries rate rewards C_star C_h
          q t s hst control0 b
            (ReferenceReleaseStrictPastFactor.normalize rate rewards C_star C_h q t s hst
              control0 (rho rate rewards C_star C_h s q t hst control0 z)) :=
        ReferenceReleaseStrictPastFactor.releaseEntries_normalize
          rate rewards C_star C_h q t s hst control0 b
            (rho rate rewards C_star C_h s q t hst control0 z)
      _ = ReferenceReleaseStrictPastFactor.releaseEntries rate rewards C_star C_h
          q t s hst control0 b
            (ReferenceReleaseStrictPastFactor.normalize rate rewards C_star C_h q t s hst
              control0 (rho rate rewards C_star C_h s q t hst control0 z')) :=
        congrArg (ReferenceReleaseStrictPastFactor.releaseEntries rate rewards C_star C_h
          q t s hst control0 b) hnormalize
      _ = _ := (ReferenceReleaseStrictPastFactor.releaseEntries_normalize
        rate rewards C_star C_h q t s hst control0 b
          (rho rate rewards C_star C_h s q t hst control0 z')).symm
  refine ⟨z', rfl, ?_, ?_⟩
  · intro b k hk
    by_cases hsk : s ≤ k
    · let j : Fin (t.val - s + 1) := ⟨k - s, by omega⟩
      have hcoord : s + j.val = k := by dsimp [j]; omega
      have hentry := source_calendar_entry_factor_strictPast
        rate rewards C_star C_h s hs q t hst control0 z b j
      have hentry' := source_calendar_entry_factor_strictPast
        rate rewards C_star C_h s hs q t hst control0 z' b j
      have hentriesAt := congrFun (hentries b) j
      have hentryEq :
          ReferenceLocalReleaseCalendarCounts.calendarEntry rate z.val.val rewards C_star C_h
            z.val.property.1 s (p.T - s) z.val.property.2 (by omega) b k =
          ReferenceLocalReleaseCalendarCounts.calendarEntry rate z'.val.val rewards C_star C_h
            z'.val.property.1 s (p.T - s) z'.val.property.2 (by omega) b k := by
        simpa only [hcoord] using
          hentry.trans ((congrArg some hentriesAt).trans hentry'.symm)
      have hpending := source_calendar_pending_projection_strictPast
        rate rewards C_star C_h s hs q t hst control0 z b j
      have hpending' := source_calendar_pending_projection_strictPast
        rate rewards C_star C_h s hs q t hst control0 z' b j
      have hpendingEq :
          ReferenceLocalReleaseWaitingPaths.calendarPendingReadout rate rewards C_star C_h s hs b
            z.val k =
          ReferenceLocalReleaseWaitingPaths.calendarPendingReadout rate rewards C_star C_h s hs b
            z'.val k := by
        simpa only [hcoord] using
          hpending.trans
            ((congrArg (fun e => pendingProjection (some e)) hentriesAt).trans hpending'.symm)
      exact ⟨hentryEq, hpendingEq⟩
    · have hnone : ¬ s ≤ k := by omega
      have hentryEq :
          ReferenceLocalReleaseCalendarCounts.calendarEntry rate z.val.val rewards C_star C_h
            z.val.property.1 s (p.T - s) z.val.property.2 (by omega) b k =
          ReferenceLocalReleaseCalendarCounts.calendarEntry rate z'.val.val rewards C_star C_h
            z'.val.property.1 s (p.T - s) z'.val.property.2 (by omega) b k := by
        simp [ReferenceLocalReleaseCalendarCounts.calendarEntry,
          ReferenceLocalReleaseCalendarCounts.calendarRecord, hnone]
      have hpendingEq :
          ReferenceLocalReleaseWaitingPaths.calendarPendingReadout rate rewards C_star C_h s hs b
            z.val k =
          ReferenceLocalReleaseWaitingPaths.calendarPendingReadout rate rewards C_star C_h s hs b
            z'.val k := by
        simp [ReferenceLocalReleaseWaitingPaths.calendarPendingReadout,
          ReferenceLocalReleaseCalendarCounts.calendarPending,
          ReferenceLocalReleaseCalendarCounts.calendarEntry,
          ReferenceLocalReleaseCalendarCounts.calendarRecord, hnone]
      exact ⟨hentryEq, hpendingEq⟩
  · intro b n hn
    have hsub := source_gate_sublevel_iff_release_entry
      rate rewards C_star C_h s hs q t hst control0 z b n hn
    have hsub' := source_gate_sublevel_iff_release_entry
      rate rewards C_star C_h s hs q t hst control0 z' b n hn
    rw [hsub, hsub']
    constructor
    · rintro ⟨j, hj, hjn⟩
      exact ⟨j, by rw [← congrArg Prod.fst (congrFun (hentries b) j)]; exact hj, hjn⟩
    · rintro ⟨j, hj, hjn⟩
      exact ⟨j, by rw [congrArg Prod.fst (congrFun (hentries b) j)]; exact hj, hjn⟩

end ObservedPrefix

/-- The suffix result on the whole original source event. The selected-row
index is read from the source itself, and the fixed-time control supplied to
the retained factor is its actual selected-row control. -/
theorem replaceSelectedControlSuffix_source_invariance
    (z : SourceEvent rate rewards C_star C_h s) (t : Fin p.T)
    (hst : s ≤ t.val)
    (suffix : Fin p.T → ContinuousLearningRows.TimeControl p) :
    ∃ z' : SourceEvent rate rewards C_star C_h s,
      z'.val = ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix
        z.val t suffix ∧
      ActualInitializationPhysicalStep.selectedRowIndex p z'.val =
        ActualInitializationPhysicalStep.selectedRowIndex p z.val ∧
      (∀ b k, k ≤ t.val →
        ReferenceLocalReleaseCalendarCounts.calendarEntry rate z.val rewards C_star C_h
          z.property.1 s (p.T - s) z.property.2 (by omega) b k =
        ReferenceLocalReleaseCalendarCounts.calendarEntry rate z'.val rewards C_star C_h
          z'.property.1 s (p.T - s) z'.property.2 (by omega) b k ∧
        ReferenceLocalReleaseWaitingPaths.calendarPendingReadout rate rewards C_star C_h s hs b
          z k =
        ReferenceLocalReleaseWaitingPaths.calendarPendingReadout rate rewards C_star C_h s hs b
          z' k) ∧
      (∀ b n, n ≤ t.val + 1 →
        (ReferenceLocalReleaseWaitingPaths.localGateAlpha rate rewards C_star C_h s hs b z ≤ n ↔
        ReferenceLocalReleaseWaitingPaths.localGateAlpha rate rewards C_star C_h s hs b z' ≤ n)) := by
  let q := ActualInitializationPhysicalStep.selectedRowIndex p z.val
  let zq : E rate rewards C_star C_h s q := ⟨z, rfl⟩
  let control0 := ReferenceSourceReleaseWaitingReadouts.sourceCurrentControl
    rate rewards C_star C_h s q t zq
  obtain ⟨zq', hvalue, hreadouts, halpha⟩ :=
    replaceSelectedControlSuffix_source_fiber_invariance
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
      (s := s) (hs := hs) (q := q) (t := t) (hst := hst)
      (control0 := control0) zq suffix
  let z' : SourceEvent rate rewards C_star C_h s := zq'.val
  refine ⟨z', ?_, ?_, ?_, ?_⟩
  · simpa only [z', zq] using hvalue
  · change ActualInitializationPhysicalStep.selectedRowIndex p zq'.val.val =
      ActualInitializationPhysicalStep.selectedRowIndex p z.val
    calc
      _ = q := zq'.property
      _ = _ := by simp only [q]
  · intro b k hk
    simpa only [z', zq] using hreadouts b k hk
  · intro b n hn
    simpa only [z', zq] using halpha b n hn

private theorem source_run_record_time_ge_start
    (z : SourceEvent rate rewards C_star C_h s)
    (r : ReferenceLocalReleaseGateChronology.Record (p := p) (rate := rate))
    (hr : r ∈ (ReferenceLocalReleaseWaitingPaths.sourceRunAtLaunch
      rate rewards C_star C_h s hs z).records) :
    s ≤ r.input.time.val := by
  let run := ReferenceLocalReleaseWaitingPaths.sourceRunAtLaunch
    rate rewards C_star C_h s hs z
  obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hr
  have hlen : run.records.length = p.T - s := by
    have hrun := ReferenceActivePhysicalHorizon.run_record_count
      (ReferenceLocalReleaseGateChronology.sourceSeed rate z.val rewards C_star C_h z.property.1)
      z.val.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z.val)
      rewards s (p.T - s) (by omega)
      (by simpa only [z.property.2] using
        (ReferenceLocalReleaseGateChronology.canonical_seed_release_inputs
          rate z.val rewards C_star C_h z.property.1).2.1)
    simpa only [run, ReferenceLocalReleaseWaitingPaths.sourceRunAtLaunch,
      ReferenceLocalReleaseGateChronology.sourceRun] using hrun
  have hi' : i < p.T - s := by rw [← hlen]; exact hi
  let index : Fin (p.T - s) := ⟨i, hi'⟩
  have hround := ReferenceLocalReleasePendingHistory.sourceRecord_sourceRound
    rate z.val rewards C_star C_h z.property.1 s (p.T - s) z.property.2
    (by omega) index
  have htimeIndex : (run.records[i]'hi).input.time.val = s + i := by
    simpa [run, ReferenceLocalReleaseWaitingPaths.sourceRunAtLaunch,
      ReferenceLocalReleasePendingHistory.sourceRecord,
      ReferenceLocalReleaseGateChronology.sourceRun] using hround.1
  have htime : r.input.time.val = s + i := by
    rw [← hget]
    exact htimeIndex
  omega

/-- Every actual-source first gate is at or after the elapsed launch round;
the empty support keeps G's `T+1` sentinel. -/
theorem source_localGateAlpha_ge_elapsed
    (z : SourceEvent rate rewards C_star C_h s) (b : ℕ) :
    s + 1 ≤ ReferenceLocalReleaseWaitingPaths.localGateAlpha
      rate rewards C_star C_h s hs b z := by
  let run := ReferenceLocalReleaseWaitingPaths.sourceRunAtLaunch
    rate rewards C_star C_h s hs z
  change s + 1 ≤ ReferenceLocalReleaseGateChronology.gateAlpha b run.records
  let support := ReferenceLocalReleaseGateChronology.gateSupport b run.records
  have hbound : ∀ v, v ∈ support → s + 1 ≤ v := by
    intro v hv
    obtain ⟨r, hr, _, rfl⟩ :=
      (ReferenceLocalReleaseGateChronology.mem_gateSupport b v run.records).mp hv
    have htime := source_run_record_time_ge_start rate rewards C_star C_h s hs z r hr
    omega
  by_cases hnonempty : support.Nonempty
  · change s + 1 ≤ if h : support.Nonempty then support.min' h else p.T + 1
    rw [dite_eq_left hnonempty]
    exact hbound _ (Finset.min'_mem support hnonempty)
  · have hempty : support = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnonempty
    change s + 1 ≤ if h : support.Nonempty then support.min' h else p.T + 1
    rw [dite_eq_right hnonempty]
    omega

/-- At a coordinate before elapsed time, C has no record and W has no pending
readout. The absence remains distinct from an observed false gate. -/
theorem source_calendar_readout_absent_outside_span
    (z : SourceEvent rate rewards C_star C_h s) (b k : ℕ)
    (hk : k < s ∨ p.T ≤ k) :
    ReferenceLocalReleaseCalendarCounts.calendarEntry rate z.val rewards C_star C_h
      z.property.1 s (p.T - s) z.property.2 (by omega) b k = none ∧
    ReferenceLocalReleaseWaitingPaths.calendarPendingReadout rate rewards C_star C_h s hs b z k =
      none := by
  have hguard : ¬ (s ≤ k ∧ k < s + (p.T - s)) := by omega
  constructor
  · simp [ReferenceLocalReleaseCalendarCounts.calendarEntry,
      ReferenceLocalReleaseCalendarCounts.calendarRecord, hguard]
  · simp [ReferenceLocalReleaseWaitingPaths.calendarPendingReadout,
      ReferenceLocalReleaseCalendarCounts.calendarPending,
      ReferenceLocalReleaseCalendarCounts.calendarEntry,
      ReferenceLocalReleaseCalendarCounts.calendarRecord, hguard]

/-- If the observation coordinate precedes elapsed time, its first-gate
sublevel through the inclusive coordinate is empty. No retained launch or
impossible `s ≤ t` witness is formed. -/
theorem source_localGateAlpha_sublevel_empty_before_start
    (t : Fin p.T) (hts : t.val < s) (b n : ℕ) (hn : n ≤ t.val + 1) :
    {z : SourceEvent rate rewards C_star C_h s |
      ReferenceLocalReleaseWaitingPaths.localGateAlpha rate rewards C_star C_h s hs b z ≤ n} =
    ∅ := by
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  intro hle
  have halpha := source_localGateAlpha_ge_elapsed rate rewards C_star C_h s hs z b
  omega

/-- The zero sublevel is empty even when the observation coordinate is at
or after the launch; the actual gate rounds are one-based. -/
theorem source_localGateAlpha_sublevel_zero (b : ℕ) :
    {z : SourceEvent rate rewards C_star C_h s |
      ReferenceLocalReleaseWaitingPaths.localGateAlpha rate rewards C_star C_h s hs b z ≤ 0} =
    ∅ := by
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  intro hle
  have halpha := source_localGateAlpha_ge_elapsed rate rewards C_star C_h s hs z b
  omega

/-- At `s=T` every `Fin T` coordinate is before elapsed time. Thus the branch
is wholly terminal and has no action coordinate. -/
theorem terminal_elapsed_has_no_action_coordinate (hterminal : s = p.T) :
    ¬ ∃ t : Fin p.T, s ≤ t.val := by
  rintro ⟨t, ht⟩
  rw [hterminal] at ht
  exact (not_le_of_gt t.isLt) ht

/-- Literal coordinate equations for S's suffix replacement. The private tuple
retains `J` and every original private array; no selected forward data or
whole other row is changed. -/
theorem replaceSelectedControlSuffix_source_coordinates
    (source : BootstrapPrivateRoundStreams.SourceInput p) (t : Fin p.T)
    (suffix : Fin p.T → ContinuousLearningRows.TimeControl p) :
    let source' := ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix
      source t suffix
    source'.1.1 = source.1.1 ∧
    source'.2 = source.2 ∧
    ActualInitializationPhysicalStep.selectedRowIndex p source' =
      ActualInitializationPhysicalStep.selectedRowIndex p source ∧
    ((source'.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).1) =
      ((source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).1) ∧
    (∀ row, row ≠ ActualInitializationPhysicalStep.selectedRowIndex p source →
      source'.1.2 row = source.1.2 row) ∧
    (∀ v : Fin p.T, v.val < t.val →
      ((source'.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).2 v) =
        ((source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).2 v)) ∧
    (∀ v : Fin p.T, t.val ≤ v.val →
      ((source'.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).2 v) = suffix v) := by
  dsimp only
  refine ⟨
    ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix_id source t suffix,
    ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix_private source t suffix,
    ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix_selected source t suffix,
    ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix_forward source t suffix,
    ?_, ?_, ?_⟩
  · intro row hrow
    exact ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix_otherRow
      source t suffix row hrow
  · intro v hv
    exact ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix_control_before
      source t v suffix hv
  · intro v hv
    exact ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix_control_from
      source t v suffix hv

/-- The actual full source alpha always respects G's empty-support `T+1`
sentinel. -/
theorem source_localGateAlpha_le_horizon_sentinel
    (z : SourceEvent rate rewards C_star C_h s) (b : ℕ) :
    ReferenceLocalReleaseWaitingPaths.localGateAlpha rate rewards C_star C_h s hs b z ≤
      p.T + 1 := by
  let run := ReferenceLocalReleaseWaitingPaths.sourceRunAtLaunch
    rate rewards C_star C_h s hs z
  change ReferenceLocalReleaseGateChronology.gateAlpha b run.records ≤ p.T + 1
  have hb := ReferenceLocalReleaseGateChronology.gate_endpoints_bounds b run.records
  exact hb.2.1.trans hb.2.2

/-- On literally empty actual gate support, the full alpha is exactly G's
`T+1` sentinel, even when an observed prefix ends earlier. -/
theorem source_localGateAlpha_eq_horizon_sentinel_of_empty_support
    (z : SourceEvent rate rewards C_star C_h s) (b : ℕ)
    (hempty : ReferenceLocalReleaseGateChronology.gateSupport b
      (ReferenceLocalReleaseWaitingPaths.sourceRunAtLaunch
        rate rewards C_star C_h s hs z).records = ∅) :
    ReferenceLocalReleaseWaitingPaths.localGateAlpha rate rewards C_star C_h s hs b z =
      p.T + 1 := by
  change ReferenceLocalReleaseGateChronology.gateAlpha b
    (ReferenceLocalReleaseWaitingPaths.sourceRunAtLaunch
      rate rewards C_star C_h s hs z).records = p.T + 1
  simp [ReferenceLocalReleaseGateChronology.gateAlpha, hempty]

/-- Terminal launch has no entry at any calendar index, and its full first
gate is exactly the empty-support sentinel. No `Fin T` action is constructed. -/
theorem terminal_source_entries_pending_and_alpha
    (hterminal : s = p.T) (z : SourceEvent rate rewards C_star C_h s) (b : ℕ) :
    (∀ k,
      ReferenceLocalReleaseCalendarCounts.calendarEntry rate z.val rewards C_star C_h
        z.property.1 s (p.T - s) z.property.2 (by omega) b k = none ∧
      ReferenceLocalReleaseWaitingPaths.calendarPendingReadout
        rate rewards C_star C_h s hs b z k = none) ∧
    ReferenceLocalReleaseWaitingPaths.localGateAlpha rate rewards C_star C_h s hs b z =
      p.T + 1 := by
  constructor
  · intro k
    apply source_calendar_readout_absent_outside_span rate rewards C_star C_h s hs z b k
    omega
  · have hlo := source_localGateAlpha_ge_elapsed rate rewards C_star C_h s hs z b
    have hhi := source_localGateAlpha_le_horizon_sentinel rate rewards C_star C_h s hs z b
    omega

end Bandits.Support.ReferenceSourceReleaseWaitingStrictPast

end noncomputable section
