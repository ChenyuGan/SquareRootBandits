/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceLocalReleasePendingHistory

import Lean.Elab.Tactic.Omega

/-!
# Original-source local-release calendar counts

Sources: `sources/zip4/manuscript/05_binary_transport.tex:74-88,180-240,293-348`,
`sources/zip4/manuscript/06_interruptions.tex:435-492`,
`sources/zip4/manuscript/07_public_setup.tex:121-164`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-79`.

All observations below are projections of the exact original-source run from
`ReferenceLocalReleaseGateChronology.sourceRun`, with its original source,
whole rewards, unrestricted constants, crossing, elapsed launch, and finite
physical interval. Missing calendar records and false gates contribute no
pending task or observation to these finite counts; they do not alter the
physical run or its reward/state semantics. The local gate entry separately
retains a true gate with an empty pending set.

These are deterministic calendar ingredients for a later
`PhaseStartConditionalWaiting` construction. They do not identify stopped
support, construct a filtration or stopping time, or establish a conditional
service law or release-cost theorem.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ReferenceLocalReleaseCalendarCounts

open ConstructorDimensions ReferenceActivePhysicalStep
open ReferenceActivePhysicalStepMeasurability
open ReferenceAssignmentPayloadPersistence
open ReferenceLocalReleaseGateChronology
open ReferenceLocalReleasePendingHistory
open ReferencePhysicalReleaseQuota
open ReferenceRetainedReleasePhaseObservation
open scoped Classical

variable {p : ConstructorDimensions.Parameters}
  {rate : ReferenceActivePhysicalStep.RateInput p}

abbrev Record := ReferenceLocalReleasePendingHistory.Record (p := p) (rate := rate)
abbrev Payload := ReferenceActivePhysicalStep.Payload rate

/-- Exact alias for the actual original-source execution; it introduces no
new execution or state carrier. -/
abbrev SourceRun (rate : ReferenceActivePhysicalStep.RateInput p)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true)
    (s count : ℕ)
    (helapsed : ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed = s)
    (hspan : s + count ≤ p.T) :=
  ReferenceLocalReleaseGateChronology.sourceRun rate z rewards C_star C_h hcross
    s count helapsed hspan

/-- The record observed at zero-based calendar round `k`. The offset is
selected in the records of the actual source run; outside its physical
interval the lookup is absent. -/
def calendarRecord (rate : ReferenceActivePhysicalStep.RateInput p)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true)
    (s count : ℕ)
    (helapsed : ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed = s)
    (hspan : s + count ≤ p.T) (k : ℕ) : Option (Record (p := p) (rate := rate)) :=
  if hk : s ≤ k ∧ k < s + count then
    some (ReferenceLocalReleasePendingHistory.sourceRecord rate z rewards C_star C_h
      hcross s count helapsed hspan (k - s) (by omega))
  else none

/-- The local gate observed on the unique source-run record at calendar `k`.
`none` means no record was observed there; `some false` means an actual record
was observed and its local gate failed. -/
def calendarGate (rate : ReferenceActivePhysicalStep.RateInput p)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true)
    (s count : ℕ)
    (helapsed : ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed = s)
    (hspan : s + count ≤ p.T) (b k : ℕ) : Option Bool :=
  (calendarRecord rate z rewards C_star C_h hcross s count helapsed hspan k).map
    fun r => ReferenceRetainedReleasePhaseObservation.localReleaseGate rate b r.input.time
      (ReferenceActivePhysicalStepMeasurability.encodeState r.input.state)

/-- The exact `localReleaseEntry` readout on the source record. In particular,
`some (true, some ∅)` is retained distinctly from a failed gate and from an
absent record. -/
def calendarEntry (rate : ReferenceActivePhysicalStep.RateInput p)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true)
    (s count : ℕ)
    (helapsed : ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed = s)
    (hspan : s + count ≤ p.T) (b k : ℕ) : Option (Bool × Option (Finset (Fin (p.m - 1)))) :=
  (calendarRecord rate z rewards C_star C_h hcross s count helapsed hspan k).map
    fun r => ReferenceRetainedReleasePhaseObservation.localReleaseEntry rate b r.input.time
      (ReferenceActivePhysicalStepMeasurability.encodeState r.input.state)

/-- The pending set from a true local-release entry. The option records that a
false gate or absent record has no local pending observation. -/
def calendarPending (rate : ReferenceActivePhysicalStep.RateInput p)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true)
    (s count : ℕ)
    (helapsed : ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed = s)
    (hspan : s + count ≤ p.T) (b k : ℕ) : Option (Finset (Fin (p.m - 1))) :=
  match calendarEntry rate z rewards C_star C_h hcross s count helapsed hspan b k with
  | some (true, some pending) => some pending
  | _ => none

/-- Apply a release-flag predicate to the actual stored payload of the looked-up
record. A missing record or missing stored payload remains `none`. -/
def calendarFlag (rate : ReferenceActivePhysicalStep.RateInput p)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true)
    (s count : ℕ)
    (helapsed : ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed = s)
    (hspan : s + count ≤ p.T) (b k : ℕ) (i : Fin (p.m - 1))
    (flag : Payload (p := p) (rate := rate) → Record (p := p) (rate := rate) →
      Fin (p.m - 1) → Bool) : Option Bool :=
  match calendarRecord rate z rewards C_star C_h hcross s count helapsed hspan k with
  | none => none
  | some r =>
      (ReferenceAssignmentPayloadPersistence.storedPayload r.input.state.coordinator).map
        fun M => flag M r i

/-- The release observation on the record's own stored whole payload and its
own physical feedback. No payload is supplied by a caller. -/
def calendarReleaseFlag (rate : ReferenceActivePhysicalStep.RateInput p)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true)
    (s count : ℕ)
    (helapsed : ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed = s)
    (hspan : s + count ≤ p.T) (b k : ℕ) (i : Fin (p.m - 1)) : Option Bool :=
  calendarFlag rate z rewards C_star C_h hcross s count helapsed hspan b k i
    (ReferencePhysicalReleaseQuota.releaseFlag (p := p) (rate := rate))

/-- The UP component of the release observation on the record's own stored
whole payload and physical feedback. -/
def calendarUpFlag (rate : ReferenceActivePhysicalStep.RateInput p)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true)
    (s count : ℕ)
    (helapsed : ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed = s)
    (hspan : s + count ≤ p.T) (b k : ℕ) (i : Fin (p.m - 1)) : Option Bool :=
  calendarFlag rate z rewards C_star C_h hcross s count helapsed hspan b k i
    (ReferencePhysicalReleaseQuota.upFlag (p := p) (rate := rate))

/-- The DATA component of the release observation on the record's own stored
whole payload and physical feedback. -/
def calendarDataFlag (rate : ReferenceActivePhysicalStep.RateInput p)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true)
    (s count : ℕ)
    (helapsed : ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed = s)
    (hspan : s + count ≤ p.T) (b k : ℕ) (i : Fin (p.m - 1)) : Option Bool :=
  calendarFlag rate z rewards C_star C_h hcross s count helapsed hspan b k i
    (ReferencePhysicalReleaseQuota.dataFlag (p := p) (rate := rate))

/-- The finite-count indicator for an optional observed pending set and an
optional Boolean observation. -/
def calendarIndicator (i : Fin (p.m - 1)) (pending : Option (Finset (Fin (p.m - 1))))
    (observation : Option Bool) : ℕ :=
  match pending, observation with
  | some tasks, some true => if i ∈ tasks then 1 else 0
  | _, _ => 0

/-- Number of UP release observations in the zero-based calendar prefix
`range v`, read from true-gate `localReleaseEntry` pending sets and each
record's own stored payload and feedback. -/
def calendarUpCount (rate : ReferenceActivePhysicalStep.RateInput p)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true)
    (s count : ℕ)
    (helapsed : ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed = s)
    (hspan : s + count ≤ p.T) (b v : ℕ) (i : Fin (p.m - 1)) : ℕ :=
  ∑ k ∈ Finset.range v,
    calendarIndicator i
      (calendarPending rate z rewards C_star C_h hcross s count helapsed hspan b k)
      (calendarUpFlag rate z rewards C_star C_h hcross s count helapsed hspan b k i)

/-- Number of DATA release observations in the zero-based calendar prefix
`range v`. -/
def calendarDataCount (rate : ReferenceActivePhysicalStep.RateInput p)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true)
    (s count : ℕ)
    (helapsed : ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed = s)
    (hspan : s + count ≤ p.T) (b v : ℕ) (i : Fin (p.m - 1)) : ℕ :=
  ∑ k ∈ Finset.range v,
    calendarIndicator i
      (calendarPending rate z rewards C_star C_h hcross s count helapsed hspan b k)
      (calendarDataFlag rate z rewards C_star C_h hcross s count helapsed hspan b k i)

/-- Number of combined release observations in the zero-based calendar prefix
`range v`. -/
def calendarReleaseCount (rate : ReferenceActivePhysicalStep.RateInput p)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true)
    (s count : ℕ)
    (helapsed : ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed = s)
    (hspan : s + count ≤ p.T) (b v : ℕ) (i : Fin (p.m - 1)) : ℕ :=
  ∑ k ∈ Finset.range v,
    calendarIndicator i
      (calendarPending rate z rewards C_star C_h hcross s count helapsed hspan b k)
      (calendarReleaseFlag rate z rewards C_star C_h hcross s count helapsed hspan b k i)

/-- The one-based gate support obtained from the finite calendar readout.
This support depends on the local gate only, not on pending-set nonemptiness. -/
def calendarGateSupport (rate : ReferenceActivePhysicalStep.RateInput p)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true)
    (s count : ℕ)
    (helapsed : ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed = s)
    (hspan : s + count ≤ p.T) (b : ℕ) : Finset ℕ :=
  (Finset.range p.T).filter fun k =>
    calendarGate rate z rewards C_star C_h hcross s count helapsed hspan b k = some true

private theorem sourceRun_active
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true)
    (s : ℕ)
    (helapsed : ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed = s) :
    ReferenceActivePhysicalHorizon.allActiveAtStart
      (ReferenceLocalReleaseGateChronology.sourceSeed rate z rewards C_star C_h hcross) s := by
  simpa only [helapsed] using
    (ReferenceLocalReleaseGateChronology.canonical_seed_release_inputs
      rate z rewards C_star C_h hcross).2.1

variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (z : BootstrapPrivateRoundStreams.SourceInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ)
  (hcross : (ReferenceInitializationRun.output
    (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true)
  (s count : ℕ)
  (helapsed : ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.output
    (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed = s)
  (hspan : s + count ≤ p.T)
  (b : ℕ)

private theorem sourceRun_record_count :
    (SourceRun rate z rewards C_star C_h hcross s count helapsed hspan).records.length = count := by
  simpa only [SourceRun, ReferenceLocalReleaseGateChronology.sourceRun] using
    (ReferenceActivePhysicalHorizon.run_record_count
      (ReferenceLocalReleaseGateChronology.sourceSeed rate z rewards C_star C_h hcross)
      z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s count hspan
      (sourceRun_active rate z rewards C_star C_h hcross s helapsed))

/-- The indexed source record belongs to `E.records` and its zero-based source
round is exactly `s + j`. -/
private theorem sourceRecord_mem (j : Fin count) :
    ReferenceLocalReleasePendingHistory.sourceRecord rate z rewards C_star C_h hcross s count
        helapsed hspan j.val j.isLt ∈ (SourceRun rate z rewards C_star C_h hcross s count helapsed hspan).records := by
  have hmem := List.getElem_mem (show j.val <
      (SourceRun rate z rewards C_star C_h hcross s count helapsed hspan).records.length by
    rw [sourceRun_record_count rate z rewards C_star C_h hcross s count helapsed hspan]
    exact j.isLt)
  simpa only [ReferenceLocalReleasePendingHistory.sourceRecord, SourceRun,
    ReferenceLocalReleaseGateChronology.sourceRun] using hmem

/-- Any actual record at a given calendar coordinate is the selected lookup;
thus lookup never aliases two source records. -/
theorem calendarRecord_eq_some_iff (k : ℕ) (r : Record (p := p) (rate := rate)) :
    calendarRecord rate z rewards C_star C_h hcross s count helapsed hspan k = some r ↔
      r ∈ (SourceRun rate z rewards C_star C_h hcross s count helapsed hspan).records ∧
        r.input.time.val = k := by
  constructor
  · intro hlookup
    by_cases hk : s ≤ k ∧ k < s + count
    · simp only [calendarRecord, dif_pos hk, Option.some.injEq] at hlookup
      subst r
      constructor
      · exact sourceRecord_mem rate z rewards C_star C_h hcross s count helapsed hspan
          ⟨k - s, by omega⟩
      · have hround := ReferenceLocalReleasePendingHistory.sourceRecord_sourceRound
          rate z rewards C_star C_h hcross s count helapsed hspan ⟨k - s, by omega⟩
        calc
          _ = s + (k - s) := hround.1
          _ = k := by omega
    · simp [calendarRecord, hk] at hlookup
  · rintro ⟨hr, htime⟩
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hr
    have hlen := sourceRun_record_count rate z rewards C_star C_h hcross s count helapsed hspan
    have hj' : j < count := by simpa only [hlen] using hj
    let index : Fin count := ⟨j, hj'⟩
    have hround := ReferenceLocalReleasePendingHistory.sourceRecord_sourceRound
      rate z rewards C_star C_h hcross s count helapsed hspan index
    let records := (SourceRun rate z rewards C_star C_h hcross s count helapsed hspan).records
    have hjRecords : j < records.length := by
      simpa only [records, sourceRun_record_count rate z rewards C_star C_h hcross s count
        helapsed hspan] using hj
    have hround' : (records[j]'hjRecords).input.time.val = s + j := by
      simpa only [ReferenceLocalReleasePendingHistory.sourceRecord, SourceRun,
        ReferenceLocalReleaseGateChronology.sourceRun, records] using hround.1
    have hjtime : s + j = k := by
      calc
        s + j = (records[j]'hjRecords).input.time.val := hround'.symm
        _ = k := htime
    have hk : s ≤ k ∧ k < s + count := by
      omega
    have hidx : k - s = j := by omega
    have hfin : (⟨k - s, by omega⟩ : Fin count) = index := by
      apply Fin.ext
      exact hidx
    simp [calendarRecord, hk, hidx, ReferenceLocalReleasePendingHistory.sourceRecord]

/-- Uniqueness follows from the actual source-round coordinate, not from an
assumed trace or state equality. -/
theorem calendarRecord_actual_unique (k : ℕ) (r₁ r₂ : Record (p := p) (rate := rate))
    (hr₁ : r₁ ∈ (SourceRun rate z rewards C_star C_h hcross s count helapsed hspan).records)
    (hr₂ : r₂ ∈ (SourceRun rate z rewards C_star C_h hcross s count helapsed hspan).records)
    (ht₁ : r₁.input.time.val = k) (ht₂ : r₂.input.time.val = k) : r₁ = r₂ := by
  have hlookup₁ := (calendarRecord_eq_some_iff rate z rewards C_star C_h hcross s count helapsed
    hspan  k r₁).mpr ⟨hr₁, ht₁⟩
  have hlookup₂ := (calendarRecord_eq_some_iff rate z rewards C_star C_h hcross s count helapsed
    hspan  k r₂).mpr ⟨hr₂, ht₂⟩
  exact Option.some.inj (hlookup₁.symm.trans hlookup₂)

/-- A successful local gate always has an actual stored whole assignment
payload. -/
theorem storedPayload_eq_some_of_calendarGate (k : ℕ)
    (r : Record (p := p) (rate := rate))
    (hlookup : calendarRecord rate z rewards C_star C_h hcross s count helapsed hspan k = some r)
    (hgate : ReferenceRetainedReleasePhaseObservation.localReleaseGate rate b r.input.time
      (ReferenceActivePhysicalStepMeasurability.encodeState r.input.state) = true) :
    ∃ M : Payload (p := p) (rate := rate),
      ReferenceAssignmentPayloadPersistence.storedPayload r.input.state.coordinator = some M ∧
        M.sigma.val = b := by
  have hmem := (calendarRecord_eq_some_iff rate z rewards C_star C_h hcross s count helapsed
    hspan  k r).mp hlookup |>.1
  have hchrono := ReferenceLocalReleaseGateChronology.source_gate_birth_and_payload_chronology
    rate z rewards C_star C_h hcross s count helapsed hspan b
  obtain ⟨M, birth, hstored, _, hsigma, _, _, _, _, _⟩ := hchrono r hmem r hmem hgate hgate
  exact ⟨M, hstored, hsigma⟩

/-- One actual payload is shared by every true gate in this exact source run.
It is extracted from a real gate record; no default payload is selected. -/
theorem commonPayload_of_calendarGate (k : ℕ)
    (r : Record (p := p) (rate := rate))
    (hlookup : calendarRecord rate z rewards C_star C_h hcross s count helapsed hspan k = some r)
    (hgate : ReferenceRetainedReleasePhaseObservation.localReleaseGate rate b r.input.time
      (ReferenceActivePhysicalStepMeasurability.encodeState r.input.state) = true) :
    ∃ M : Payload (p := p) (rate := rate),
      M.sigma.val = b ∧
        ReferenceAssignmentPayloadPersistence.storedPayload r.input.state.coordinator = some M ∧
        ∀ r' ∈ (SourceRun rate z rewards C_star C_h hcross s count helapsed hspan).records,
          ReferenceRetainedReleasePhaseObservation.localReleaseGate rate b r'.input.time
            (ReferenceActivePhysicalStepMeasurability.encodeState r'.input.state) = true →
          ReferenceAssignmentPayloadPersistence.storedPayload r'.input.state.coordinator = some M := by
  obtain ⟨M, hstored, hsigma⟩ := storedPayload_eq_some_of_calendarGate rate z rewards C_star C_h
    hcross s count helapsed hspan b k r hlookup hgate
  have hmem := (calendarRecord_eq_some_iff rate z rewards C_star C_h hcross s count helapsed
    hspan  k r).mp hlookup |>.1
  have hchrono := ReferenceLocalReleaseGateChronology.source_gate_birth_and_payload_chronology
    rate z rewards C_star C_h hcross s count helapsed hspan b
  refine ⟨M, hsigma, hstored, ?_⟩
  intro r' hr' hgate'
  obtain ⟨N, birth, hleft, hright, _, _, _, _, _, _⟩ := hchrono r hmem r' hr' hgate hgate'
  have hNM : N = M := Option.some.inj (hleft.symm.trans hstored)
  simpa only [hNM] using hright

/-- On nonempty actual gate support, one actual whole payload is extracted
from a gate record and is the stored payload of every gate record. -/
theorem commonPayload_of_nonempty_gateSupport
    (hsupport : (ReferenceLocalReleaseGateChronology.gateSupport b
      (SourceRun rate z rewards C_star C_h hcross s count helapsed hspan).records).Nonempty) :
    ∃ M : Payload (p := p) (rate := rate), M.sigma.val = b ∧
      ∀ r ∈ (SourceRun rate z rewards C_star C_h hcross s count helapsed hspan).records,
        ReferenceRetainedReleasePhaseObservation.localReleaseGate rate b r.input.time
          (ReferenceActivePhysicalStepMeasurability.encodeState r.input.state) = true →
        ReferenceAssignmentPayloadPersistence.storedPayload r.input.state.coordinator = some M := by
  obtain ⟨t, ht⟩ := hsupport
  obtain ⟨r, hr, hgate, htime⟩ :=
    (ReferenceLocalReleaseGateChronology.mem_gateSupport b t
      (SourceRun rate z rewards C_star C_h hcross s count helapsed hspan).records).mp ht
  have hlookup : calendarRecord rate z rewards C_star C_h hcross s count helapsed hspan
      r.input.time.val = some r :=
    (calendarRecord_eq_some_iff rate z rewards C_star C_h hcross s count helapsed hspan
      r.input.time.val r).mpr ⟨hr, rfl⟩
  obtain ⟨M, hsigma, hstored, hwhole⟩ := commonPayload_of_calendarGate rate z rewards C_star C_h
    hcross s count helapsed hspan b r.input.time.val r hlookup hgate
  exact ⟨M, hsigma, hwhole⟩

/-- At a true current gate, its own extracted payload is the same payload used
by every gate in the original-source run. -/
theorem commonPayload_at_calendarGate (k : ℕ)
    (hgate : calendarGate rate z rewards C_star C_h hcross s count helapsed hspan b k = some true) :
    ∃ r : Record (p := p) (rate := rate), ∃ M : Payload (p := p) (rate := rate),
      calendarRecord rate z rewards C_star C_h hcross s count helapsed hspan k = some r ∧
      ReferenceAssignmentPayloadPersistence.storedPayload r.input.state.coordinator = some M ∧
      M.sigma.val = b ∧
      ∀ r' ∈ (SourceRun rate z rewards C_star C_h hcross s count helapsed hspan).records,
        ReferenceRetainedReleasePhaseObservation.localReleaseGate rate b r'.input.time
          (ReferenceActivePhysicalStepMeasurability.encodeState r'.input.state) = true →
        ReferenceAssignmentPayloadPersistence.storedPayload r'.input.state.coordinator = some M := by
  cases hrecord : calendarRecord rate z rewards C_star C_h hcross s count helapsed hspan k with
  | none => simp [calendarGate, hrecord] at hgate
  | some r =>
    have hactualGate : ReferenceRetainedReleasePhaseObservation.localReleaseGate rate b r.input.time
        (ReferenceActivePhysicalStepMeasurability.encodeState r.input.state) = true := by
      simpa [calendarGate, hrecord] using hgate
    obtain ⟨M, hsigma, hstored, hwhole⟩ := commonPayload_of_calendarGate rate z rewards C_star C_h
      hcross s count helapsed hspan b k r hrecord hactualGate
    exact ⟨r, M, rfl, hstored, hsigma, hwhole⟩

/-- The literal local entry's pending set agrees with Q's actual pending
projection when its own stored payload is `M`. -/
theorem calendarEntry_eq_actualPending (k : ℕ) (r : Record (p := p) (rate := rate))
    (M : Payload (p := p) (rate := rate))
    (hlookup : calendarRecord rate z rewards C_star C_h hcross s count helapsed hspan k = some r)
    (hgate : ReferenceRetainedReleasePhaseObservation.localReleaseGate rate b r.input.time
      (ReferenceActivePhysicalStepMeasurability.encodeState r.input.state) = true)
    (hstored : ReferenceAssignmentPayloadPersistence.storedPayload r.input.state.coordinator = some M) :
    calendarEntry rate z rewards C_star C_h hcross s count helapsed hspan b k =
      some (true, some (ReferencePhysicalReleaseQuota.pendingSet M r)) := by
  have hlocalPending := ReferenceLocalReleasePendingHistory.source_localReleasePending_eq_pendingSet
    rate b M r hgate
  simp only [calendarEntry, hlookup, Option.map_some]
  rw [ReferenceRetainedReleasePhaseObservation.localReleaseEntry,
    ReferenceRetainedReleasePhaseObservation.localStoredPayload_eq_decoded,
    ReferenceActivePhysicalStepMeasurability.decodeState_encodeState, hstored]
  simpa [hgate, ReferenceRetainedReleasePhaseObservation.localReleasePending,
    ReferencePhysicalReleaseQuota.pendingSet] using hlocalPending

/-- The actual record flags use its own stored payload. This lemma exposes the
whole-payload substitution used in the count assembly. -/
theorem calendarFlag_eq_actual (k : ℕ) (r : Record (p := p) (rate := rate))
    (M : Payload (p := p) (rate := rate))
    (hlookup : calendarRecord rate z rewards C_star C_h hcross s count helapsed hspan k = some r)
    (hstored : ReferenceAssignmentPayloadPersistence.storedPayload r.input.state.coordinator = some M)
    (flag : Payload (p := p) (rate := rate) → Record (p := p) (rate := rate) →
      Fin (p.m - 1) → Bool) (i : Fin (p.m - 1)) :
    calendarFlag rate z rewards C_star C_h hcross s count helapsed hspan b k i flag =
      some (flag M r i) := by
  simp [calendarFlag, hlookup, hstored]

private theorem sourceRun_records_nodup :
    (SourceRun rate z rewards C_star C_h hcross s count helapsed hspan).records.Nodup := by
  have htimes : ((SourceRun rate z rewards C_star C_h hcross s count helapsed hspan).records.map
      fun r => r.input.time.val) = ReferenceActivePhysicalHorizon.calendar s count := by
    simpa only [SourceRun, ReferenceLocalReleaseGateChronology.sourceRun] using
      (ReferenceActivePhysicalHorizon.run_time_values
        (ReferenceLocalReleaseGateChronology.sourceSeed rate z rewards C_star C_h hcross)
        z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s count hspan
        (sourceRun_active rate z rewards C_star C_h hcross s helapsed))
  have hcalendar : (ReferenceActivePhysicalHorizon.calendar s count).Nodup := by
    simpa [ReferenceActivePhysicalHorizon.calendar] using
      (List.nodup_range' : (List.range' s count).Nodup)
  exact List.Nodup.of_map _ (htimes ▸ hcalendar)

private theorem sourceCalendarBefore_records_nodup (v : ℕ) :
    (ReferenceLocalReleasePendingHistory.sourceLocalGateRecordsBefore rate z rewards C_star C_h
      hcross s count helapsed hspan b (v + 1)).Nodup := by
  apply List.Nodup.filter
  apply List.Nodup.filter
  exact sourceRun_records_nodup rate z rewards C_star C_h hcross s count helapsed hspan

/-- A pending-set observation is only present on an actual true local gate. -/
theorem calendarPending_some_implies_gate (k : ℕ) (P : Finset (Fin (p.m - 1)))
    (hP : calendarPending rate z rewards C_star C_h hcross s count helapsed hspan b k = some P) :
    calendarGate rate z rewards C_star C_h hcross s count helapsed hspan b k = some true := by
  cases hrecord : calendarRecord rate z rewards C_star C_h hcross s count helapsed hspan k with
  | none => simp [calendarPending, calendarEntry, hrecord] at hP
  | some r =>
      by_cases hgate : ReferenceRetainedReleasePhaseObservation.localReleaseGate rate b r.input.time
          (ReferenceActivePhysicalStepMeasurability.encodeState r.input.state) = true
      · simpa [calendarPending, calendarEntry, calendarGate, hrecord,
          ReferenceRetainedReleasePhaseObservation.localReleaseEntry, hgate] using hP
      · simp [calendarPending, calendarEntry, calendarGate, hrecord,
          ReferenceRetainedReleasePhaseObservation.localReleaseEntry, hgate] at hP

/-- Reindex a retained local-gate list sum by its unique actual calendar
coordinates. This is the additional whole-calendar reindexing beyond H's
already-proved retained-list finite-sum identities. -/
private theorem sourceCalendar_sum_reindex (M : Payload (p := p) (rate := rate))
    (v : ℕ) (i : Fin (p.m - 1))
    (flag : Record (p := p) (rate := rate) → Bool)
    (calendarFlag : ℕ → Option Bool)
    (hwhole : ∀ r ∈ (SourceRun rate z rewards C_star C_h hcross s count helapsed hspan).records,
      ReferenceRetainedReleasePhaseObservation.localReleaseGate rate b r.input.time
        (ReferenceActivePhysicalStepMeasurability.encodeState r.input.state) = true →
      ReferenceAssignmentPayloadPersistence.storedPayload r.input.state.coordinator = some M)
    (hflag : ∀ k r,
      calendarRecord rate z rewards C_star C_h hcross s count helapsed hspan k = some r →
      ReferenceRetainedReleasePhaseObservation.localReleaseGate rate b r.input.time
        (ReferenceActivePhysicalStepMeasurability.encodeState r.input.state) = true →
      calendarFlag k = some (flag r)) :
    (∑ j : Fin (ReferenceLocalReleasePendingHistory.sourceLocalGateRecordsBefore rate z rewards C_star C_h
        hcross s count helapsed hspan b (v + 1)).length,
      if decide (i ∈ ReferencePhysicalReleaseQuota.pendingSet M
          (ReferenceLocalReleasePendingHistory.sourceLocalGateRecordsBefore rate z rewards C_star C_h
            hcross s count helapsed hspan b (v + 1))[j.val]) &&
          flag (ReferenceLocalReleasePendingHistory.sourceLocalGateRecordsBefore rate z rewards C_star C_h
            hcross s count helapsed hspan b (v + 1))[j.val] then 1 else 0) =
      ∑ k ∈ Finset.range v,
        calendarIndicator i
          (calendarPending rate z rewards C_star C_h hcross s count helapsed hspan b k)
          (calendarFlag k) := by
  classical
  let records := ReferenceLocalReleasePendingHistory.sourceLocalGateRecordsBefore rate z rewards C_star C_h
    hcross s count helapsed hspan b (v + 1)
  let target := (Finset.range v).filter fun k =>
    calendarGate rate z rewards C_star C_h hcross s count helapsed hspan b k = some true
  have hnodup : records.Nodup := by
    simpa only [records] using
      sourceCalendarBefore_records_nodup rate z rewards C_star C_h hcross s count helapsed hspan b v
  let g : ℕ → ℕ := fun k => calendarIndicator i
    (calendarPending rate z rewards C_star C_h hcross s count helapsed hspan b k)
    (calendarFlag k)
  have hbij :
      (∑ j : Fin records.length,
        if decide (i ∈ ReferencePhysicalReleaseQuota.pendingSet M records[j.val]) &&
          flag records[j.val] then 1 else 0) = ∑ k ∈ target, g k := by
    apply Finset.sum_bij (s := Finset.univ) (t := target)
      (fun j _ => (records[j.val]'(j.isLt)).input.time.val)
    · intro j _
      have hmem := List.getElem_mem (show j.val < records.length by exact j.isLt)
      have hmem' : (records[j.val]'(j.isLt)) ∈
          ((SourceRun rate z rewards C_star C_h hcross s count helapsed hspan).records.filter
            (fun r => ReferenceRetainedReleasePhaseObservation.localReleaseGate rate b r.input.time
              (ReferenceActivePhysicalStepMeasurability.encodeState r.input.state))).filter
            (fun r => decide (r.input.time.val + 1 < v + 1)) := by
        simpa only [records, ReferenceLocalReleasePendingHistory.sourceLocalGateRecordsBefore,
          ReferenceLocalReleasePendingHistory.sourceLocalGateRecords,
          ReferenceLocalReleaseGateChronology.sourceRun] using hmem
      have hfiltered := List.mem_filter.mp hmem'
      have hgate := (List.mem_filter.mp hfiltered.1).2
      have htime : (records[j.val]'(j.isLt)).input.time.val < v := by
        have := of_decide_eq_true hfiltered.2
        omega
      have hlookup := (calendarRecord_eq_some_iff rate z rewards C_star C_h hcross s count helapsed
        hspan  (records[j.val]'(j.isLt)).input.time.val (records[j.val]'(j.isLt))).mpr
        ⟨(List.mem_filter.mp hfiltered.1).1, rfl⟩
      simp only [target, Finset.mem_filter, Finset.mem_range]
      exact ⟨htime, by simp [calendarGate, hlookup, hgate]⟩
    · intro j _ k _ heq
      have rjmem := List.getElem_mem (show j.val < records.length by exact j.isLt)
      have rkmem := List.getElem_mem (show k.val < records.length by exact k.isLt)
      have rjfilter : records[j.val]'(j.isLt) ∈
          ((SourceRun rate z rewards C_star C_h hcross s count helapsed hspan).records.filter
            (fun r => ReferenceRetainedReleasePhaseObservation.localReleaseGate rate b r.input.time
              (ReferenceActivePhysicalStepMeasurability.encodeState r.input.state))).filter
            (fun r => decide (r.input.time.val + 1 < v + 1)) := by
        simpa only [records, ReferenceLocalReleasePendingHistory.sourceLocalGateRecordsBefore,
          ReferenceLocalReleasePendingHistory.sourceLocalGateRecords,
          ReferenceLocalReleaseGateChronology.sourceRun] using rjmem
      have rkfilter : records[k.val]'(k.isLt) ∈
          ((SourceRun rate z rewards C_star C_h hcross s count helapsed hspan).records.filter
            (fun r => ReferenceRetainedReleasePhaseObservation.localReleaseGate rate b r.input.time
              (ReferenceActivePhysicalStepMeasurability.encodeState r.input.state))).filter
            (fun r => decide (r.input.time.val + 1 < v + 1)) := by
        simpa only [records, ReferenceLocalReleasePendingHistory.sourceLocalGateRecordsBefore,
          ReferenceLocalReleasePendingHistory.sourceLocalGateRecords,
          ReferenceLocalReleaseGateChronology.sourceRun] using rkmem
      have hlookJ := (calendarRecord_eq_some_iff rate z rewards C_star C_h hcross s count helapsed
        hspan  (records[j.val]'(j.isLt)).input.time.val (records[j.val]'(j.isLt))).mpr
        ⟨(List.mem_filter.mp (List.mem_filter.mp rjfilter).1).1, rfl⟩
      have hlookK := (calendarRecord_eq_some_iff rate z rewards C_star C_h hcross s count helapsed
        hspan  (records[k.val]'(k.isLt)).input.time.val (records[k.val]'(k.isLt))).mpr
        ⟨(List.mem_filter.mp (List.mem_filter.mp rkfilter).1).1, rfl⟩
      have hrecordsEq : records[j.val]'(j.isLt) = records[k.val]'(k.isLt) := by
        have hlookJ' := hlookJ
        rw [heq] at hlookJ'
        apply Option.some.inj
        exact hlookJ'.symm.trans hlookK
      have hindex := (List.Nodup.getElem_inj_iff hnodup).mp hrecordsEq
      exact Fin.ext hindex
    · intro t ht
      have ht' := Finset.mem_filter.mp ht
      cases hrecord : calendarRecord rate z rewards C_star C_h hcross s count helapsed hspan t with
      | none => simp [calendarGate, hrecord] at ht'
      | some r =>
          have hgate : ReferenceRetainedReleasePhaseObservation.localReleaseGate rate b r.input.time
              (ReferenceActivePhysicalStepMeasurability.encodeState r.input.state) = true := by
            simpa [calendarGate, hrecord] using ht'.2
          have hrecordFacts := (calendarRecord_eq_some_iff rate z rewards C_star C_h hcross s count
            helapsed hspan  t r).mp hrecord
          have hmem : r ∈ records := by
            apply List.mem_filter.mpr
            refine ⟨List.mem_filter.mpr ⟨hrecordFacts.1, hgate⟩, ?_⟩
            simp only [decide_eq_true_eq]
            rw [hrecordFacts.2]
            have htlt : t < v := by simpa [target] using ht'.1
            omega
          obtain ⟨j, hj, hjr⟩ := List.mem_iff_getElem.mp hmem
          have htime : (records[j]'(by simpa only [records] using hj)).input.time.val = t := by
            simpa only [hjr] using hrecordFacts.2
          refine ⟨⟨j, by simpa only [records] using hj⟩, Finset.mem_univ _, ?_⟩
          simpa only [records, htime]
    · intro j _
      let r := records[j.val]'(j.isLt)
      have hmem := List.getElem_mem (show j.val < records.length by exact j.isLt)
      have hmem' : r ∈
          ((SourceRun rate z rewards C_star C_h hcross s count helapsed hspan).records.filter
            (fun r => ReferenceRetainedReleasePhaseObservation.localReleaseGate rate b r.input.time
              (ReferenceActivePhysicalStepMeasurability.encodeState r.input.state))).filter
            (fun r => decide (r.input.time.val + 1 < v + 1)) := by
        simpa only [r, records, ReferenceLocalReleasePendingHistory.sourceLocalGateRecordsBefore,
          ReferenceLocalReleasePendingHistory.sourceLocalGateRecords,
          ReferenceLocalReleaseGateChronology.sourceRun] using hmem
      have hfiltered := List.mem_filter.mp hmem'
      have hgate := (List.mem_filter.mp hfiltered.1).2
      have hstored := hwhole r ((List.mem_filter.mp hfiltered.1).1) hgate
      have hlookup := (calendarRecord_eq_some_iff rate z rewards C_star C_h hcross s count helapsed
        hspan  r.input.time.val r).mpr ⟨(List.mem_filter.mp hfiltered.1).1, rfl⟩
      have hentry := calendarEntry_eq_actualPending rate z rewards C_star C_h hcross s count
        helapsed hspan b r.input.time.val r M hlookup hgate hstored
      have hflag := hflag r.input.time.val r hlookup hgate
      have htime : r.input.time.val < v := by
        have := of_decide_eq_true hfiltered.2
        omega
      have hlookup' : calendarRecord rate z rewards C_star C_h hcross s count helapsed hspan
          (records[j.val]'(j.isLt)).input.time.val = some (records[j.val]'(j.isLt)) := by
        simpa only [r] using hlookup
      have hentry' : calendarEntry rate z rewards C_star C_h hcross s count helapsed hspan b
          (records[j.val]'(j.isLt)).input.time.val =
            some (true, some (ReferencePhysicalReleaseQuota.pendingSet M
              (records[j.val]'(j.isLt)))) := by
        simpa only [r] using hentry
      have hflag' : calendarFlag (records[j.val]'(j.isLt)).input.time.val =
          some (flag (records[j.val]'(j.isLt))) := by
        simpa only [r] using hflag
      by_cases hi : i ∈ ReferencePhysicalReleaseQuota.pendingSet M
          (records[j.val]'(j.isLt))
      · cases hv : flag (records[j.val]'(j.isLt)) <;>
          simp [g, calendarIndicator, calendarPending, hentry', hflag', hi, hv]
      · cases hv : flag (records[j.val]'(j.isLt)) <;>
          simp [g, calendarIndicator, calendarPending, hentry', hflag', hi, hv]
  have hzeroOff : ∀ k ∈ Finset.range v, k ∉ target → g k = 0 := by
    intro k hk hnot
    cases hpending : calendarPending rate z rewards C_star C_h hcross s count helapsed hspan b k with
    | none => simp [g, calendarIndicator, hpending]
    | some P =>
        have hgate := calendarPending_some_implies_gate rate z rewards C_star C_h hcross s count
          helapsed hspan b k P hpending
        have hmem : k ∈ target := by simp [target, hk, hgate]
        exact (hnot hmem).elim
  have hsubset : ∑ k ∈ target, g k = ∑ k ∈ Finset.range v, g k := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro k hk hnot
    exact hzeroOff k hk hnot
  exact hbij.trans hsubset

private theorem calendarReleaseCount_eq_of_commonPayload (M : Payload (p := p) (rate := rate))
    (hwhole : ∀ r ∈ (SourceRun rate z rewards C_star C_h hcross s count helapsed hspan).records,
      ReferenceRetainedReleasePhaseObservation.localReleaseGate rate b r.input.time
        (ReferenceActivePhysicalStepMeasurability.encodeState r.input.state) = true →
      ReferenceAssignmentPayloadPersistence.storedPayload r.input.state.coordinator = some M)
    (v : ℕ) (i : Fin (p.m - 1)) :
    calendarReleaseCount rate z rewards C_star C_h hcross s count helapsed hspan b v i =
      ReferencePhysicalReleaseQuota.releaseCount M
        (ReferenceLocalReleasePendingHistory.sourceLocalGateRecordsBefore rate z rewards C_star C_h
          hcross s count helapsed hspan b (v + 1)) i := by
  let records := ReferenceLocalReleasePendingHistory.sourceLocalGateRecordsBefore rate z rewards C_star C_h
    hcross s count helapsed hspan b (v + 1)
  have hfinite := ReferenceLocalReleasePendingHistory.releaseCount_fin_sum M records i
  have hflag : ∀ k r,
      calendarRecord rate z rewards C_star C_h hcross s count helapsed hspan k = some r →
      ReferenceRetainedReleasePhaseObservation.localReleaseGate rate b r.input.time
        (ReferenceActivePhysicalStepMeasurability.encodeState r.input.state) = true →
      calendarReleaseFlag rate z rewards C_star C_h hcross s count helapsed hspan b k i =
        some (ReferencePhysicalReleaseQuota.releaseFlag M r i) := by
    intro k r hlookup hgate
    have hrmem := (calendarRecord_eq_some_iff rate z rewards C_star C_h hcross s count helapsed
      hspan  k r).mp hlookup |>.1
    have hstored := hwhole r hrmem hgate
    simpa only [calendarReleaseFlag] using
      (calendarFlag_eq_actual rate z rewards C_star C_h hcross s count helapsed hspan b k r M
        hlookup hstored ReferencePhysicalReleaseQuota.releaseFlag i)
  have hsum := sourceCalendar_sum_reindex rate z rewards C_star C_h hcross s count helapsed hspan b
    M v i (fun r => ReferencePhysicalReleaseQuota.releaseFlag M r i)
    (fun k => calendarReleaseFlag rate z rewards C_star C_h hcross s count helapsed hspan b k i)
    hwhole hflag
  simpa only [calendarReleaseCount] using hsum.symm.trans hfinite.symm

private theorem calendarUpCount_eq_of_commonPayload (M : Payload (p := p) (rate := rate))
    (hwhole : ∀ r ∈ (SourceRun rate z rewards C_star C_h hcross s count helapsed hspan).records,
      ReferenceRetainedReleasePhaseObservation.localReleaseGate rate b r.input.time
        (ReferenceActivePhysicalStepMeasurability.encodeState r.input.state) = true →
      ReferenceAssignmentPayloadPersistence.storedPayload r.input.state.coordinator = some M)
    (v : ℕ) (i : Fin (p.m - 1)) :
    calendarUpCount rate z rewards C_star C_h hcross s count helapsed hspan b v i =
      ReferencePhysicalReleaseQuota.upCount M
        (ReferenceLocalReleasePendingHistory.sourceLocalGateRecordsBefore rate z rewards C_star C_h
          hcross s count helapsed hspan b (v + 1)) i := by
  let records := ReferenceLocalReleasePendingHistory.sourceLocalGateRecordsBefore rate z rewards C_star C_h
    hcross s count helapsed hspan b (v + 1)
  have hfinite := ReferenceLocalReleasePendingHistory.upCount_fin_sum M records i
  have hflag : ∀ k r,
      calendarRecord rate z rewards C_star C_h hcross s count helapsed hspan k = some r →
      ReferenceRetainedReleasePhaseObservation.localReleaseGate rate b r.input.time
        (ReferenceActivePhysicalStepMeasurability.encodeState r.input.state) = true →
      calendarUpFlag rate z rewards C_star C_h hcross s count helapsed hspan b k i =
        some (ReferencePhysicalReleaseQuota.upFlag M r i) := by
    intro k r hlookup hgate
    have hrmem := (calendarRecord_eq_some_iff rate z rewards C_star C_h hcross s count helapsed
      hspan  k r).mp hlookup |>.1
    have hstored := hwhole r hrmem hgate
    simpa only [calendarUpFlag] using
      (calendarFlag_eq_actual rate z rewards C_star C_h hcross s count helapsed hspan b k r M
        hlookup hstored ReferencePhysicalReleaseQuota.upFlag i)
  have hsum := sourceCalendar_sum_reindex rate z rewards C_star C_h hcross s count helapsed hspan b
    M v i (fun r => ReferencePhysicalReleaseQuota.upFlag M r i)
    (fun k => calendarUpFlag rate z rewards C_star C_h hcross s count helapsed hspan b k i)
    hwhole hflag
  simpa only [calendarUpCount] using hsum.symm.trans hfinite.symm

private theorem calendarDataCount_eq_of_commonPayload (M : Payload (p := p) (rate := rate))
    (hwhole : ∀ r ∈ (SourceRun rate z rewards C_star C_h hcross s count helapsed hspan).records,
      ReferenceRetainedReleasePhaseObservation.localReleaseGate rate b r.input.time
        (ReferenceActivePhysicalStepMeasurability.encodeState r.input.state) = true →
      ReferenceAssignmentPayloadPersistence.storedPayload r.input.state.coordinator = some M)
    (v : ℕ) (i : Fin (p.m - 1)) :
    calendarDataCount rate z rewards C_star C_h hcross s count helapsed hspan b v i =
      ReferencePhysicalReleaseQuota.dataCount M
        (ReferenceLocalReleasePendingHistory.sourceLocalGateRecordsBefore rate z rewards C_star C_h
          hcross s count helapsed hspan b (v + 1)) i := by
  let records := ReferenceLocalReleasePendingHistory.sourceLocalGateRecordsBefore rate z rewards C_star C_h
    hcross s count helapsed hspan b (v + 1)
  have hfinite := ReferenceLocalReleasePendingHistory.dataCount_fin_sum M records i
  have hflag : ∀ k r,
      calendarRecord rate z rewards C_star C_h hcross s count helapsed hspan k = some r →
      ReferenceRetainedReleasePhaseObservation.localReleaseGate rate b r.input.time
        (ReferenceActivePhysicalStepMeasurability.encodeState r.input.state) = true →
      calendarDataFlag rate z rewards C_star C_h hcross s count helapsed hspan b k i =
        some (ReferencePhysicalReleaseQuota.dataFlag M r i) := by
    intro k r hlookup hgate
    have hrmem := (calendarRecord_eq_some_iff rate z rewards C_star C_h hcross s count helapsed
      hspan  k r).mp hlookup |>.1
    have hstored := hwhole r hrmem hgate
    simpa only [calendarDataFlag] using
      (calendarFlag_eq_actual rate z rewards C_star C_h hcross s count helapsed hspan b k r M
        hlookup hstored ReferencePhysicalReleaseQuota.dataFlag i)
  have hsum := sourceCalendar_sum_reindex rate z rewards C_star C_h hcross s count helapsed hspan b
    M v i (fun r => ReferencePhysicalReleaseQuota.dataFlag M r i)
    (fun k => calendarDataFlag rate z rewards C_star C_h hcross s count helapsed hspan b k i)
    hwhole hflag
  simpa only [calendarDataCount] using hsum.symm.trans hfinite.symm

/-- On nonempty actual gate support, one real whole payload serves every
calendar identity and quota statement. The witness is extracted from the
source run and is shared across every horizon and follower. -/
theorem sourceCalendar_counts_on_nonempty_gateSupport
    (hsupport : (ReferenceLocalReleaseGateChronology.gateSupport b
      (SourceRun rate z rewards C_star C_h hcross s count helapsed hspan).records).Nonempty) :
    ∃ M : Payload (p := p) (rate := rate), M.sigma.val = b ∧
      (∀ r ∈ (SourceRun rate z rewards C_star C_h hcross s count helapsed hspan).records,
        ReferenceRetainedReleasePhaseObservation.localReleaseGate rate b r.input.time
          (ReferenceActivePhysicalStepMeasurability.encodeState r.input.state) = true →
        ReferenceAssignmentPayloadPersistence.storedPayload r.input.state.coordinator = some M) ∧
      ∀ v i,
        calendarUpCount rate z rewards C_star C_h hcross s count helapsed hspan b v i =
          ReferencePhysicalReleaseQuota.upCount M
            (ReferenceLocalReleasePendingHistory.sourceLocalGateRecordsBefore rate z rewards C_star C_h
              hcross s count helapsed hspan b (v + 1)) i ∧
        calendarDataCount rate z rewards C_star C_h hcross s count helapsed hspan b v i =
          ReferencePhysicalReleaseQuota.dataCount M
            (ReferenceLocalReleasePendingHistory.sourceLocalGateRecordsBefore rate z rewards C_star C_h
              hcross s count helapsed hspan b (v + 1)) i ∧
        calendarReleaseCount rate z rewards C_star C_h hcross s count helapsed hspan b v i =
          ReferencePhysicalReleaseQuota.releaseCount M
            (ReferenceLocalReleasePendingHistory.sourceLocalGateRecordsBefore rate z rewards C_star C_h
              hcross s count helapsed hspan b (v + 1)) i ∧
        calendarUpCount rate z rewards C_star C_h hcross s count helapsed hspan b v i ≤ 1 ∧
        calendarDataCount rate z rewards C_star C_h hcross s count helapsed hspan b v i ≤ 1 ∧
        calendarReleaseCount rate z rewards C_star C_h hcross s count helapsed hspan b v i ≤ 1 := by
  obtain ⟨M, hsigma, hwhole⟩ := commonPayload_of_nonempty_gateSupport rate z rewards C_star C_h
    hcross s count helapsed hspan b hsupport
  refine ⟨M, hsigma, hwhole, ?_⟩
  intro v i
  have hup := calendarUpCount_eq_of_commonPayload rate z rewards C_star C_h hcross s count
    helapsed hspan b M hwhole v i
  have hdata := calendarDataCount_eq_of_commonPayload rate z rewards C_star C_h hcross s count
    helapsed hspan b M hwhole v i
  have hrelease := calendarReleaseCount_eq_of_commonPayload rate z rewards C_star C_h hcross s count
    helapsed hspan b M hwhole v i
  have hupBound := ReferenceLocalReleasePendingHistory.sourceLocalGateRecordsBefore_upCount_le_one
    rate z rewards C_star C_h hcross s count helapsed hspan b (v + 1) M i
  have hdataBound := ReferenceLocalReleasePendingHistory.sourceLocalGateRecordsBefore_dataCount_le_one
    rate z rewards C_star C_h hcross s count helapsed hspan b (v + 1) M i
  have hreleaseBound := ReferenceLocalReleasePendingHistory.sourceLocalGateRecordsBefore_releaseCount_le_one
    rate z rewards C_star C_h hcross s count helapsed hspan b (v + 1) M i
  rw [hup, hdata, hrelease]
  exact ⟨rfl, rfl, rfl, hupBound, hdataBound, hreleaseBound⟩

/-- The full finite calendar gate support is exactly G's support under the
zero-based to one-based round map. -/
theorem calendarGateSupport_image :
    Finset.image (fun k : ℕ => k + 1) (calendarGateSupport rate z rewards C_star C_h
      hcross s count helapsed hspan b) =
      ReferenceLocalReleaseGateChronology.gateSupport b
        (SourceRun rate z rewards C_star C_h hcross s count helapsed hspan).records := by
  ext t
  constructor
  · intro ht
    obtain ⟨k, hk, hkt⟩ := Finset.mem_image.mp ht
    have hcal := Finset.mem_filter.mp hk
    have hrecord : calendarRecord rate z rewards C_star C_h hcross s count helapsed hspan k ≠ none := by
      cases hrec : calendarRecord rate z rewards C_star C_h hcross s count helapsed hspan k with
      | none => simp [calendarGate, hrec] at hcal
      | some r => exact Option.some_ne_none _
    cases hrec : calendarRecord rate z rewards C_star C_h hcross s count helapsed hspan k with
    | none => exact (hrecord hrec).elim
    | some r =>
        have hgate : ReferenceRetainedReleasePhaseObservation.localReleaseGate rate b r.input.time
            (ReferenceActivePhysicalStepMeasurability.encodeState r.input.state) = true := by
          simpa [calendarGate, hrec] using hcal.2
        have hfacts := (calendarRecord_eq_some_iff rate z rewards C_star C_h hcross s count
          helapsed hspan  k r).mp hrec
        have hmember := (ReferenceLocalReleaseGateChronology.mem_gateSupport b (k + 1)
              (SourceRun rate z rewards C_star C_h hcross s count helapsed hspan).records).2
              ⟨r, hfacts.1, hgate, by omega⟩
        simpa [hkt] using hmember
  · intro ht
    obtain ⟨r, hr, hgate, htime⟩ :=
      (ReferenceLocalReleaseGateChronology.mem_gateSupport b t
        (SourceRun rate z rewards C_star C_h hcross s count helapsed hspan).records).mp
        (by simpa only [SourceRun] using ht)
    let k := r.input.time.val
    have hklt : k < p.T := r.input.time.isLt
    have hlookup : calendarRecord rate z rewards C_star C_h hcross s count helapsed hspan k = some r :=
      (calendarRecord_eq_some_iff rate z rewards C_star C_h hcross s count helapsed hspan  k r).mpr
        ⟨hr, rfl⟩
    have hcal : k ∈ calendarGateSupport rate z rewards C_star C_h hcross s count helapsed hspan b := by
      simp [calendarGateSupport, Finset.mem_filter, hklt, calendarGate, hlookup, hgate]
    refine Finset.mem_image.mpr ⟨k, hcal, ?_⟩
    simpa [k] using htime

/-- The local gate interval survives restriction to any supplied one-based
endpoint `theta` in `[1,T+1]`. This endpoint is pathwise only; it is not
asserted to be a stopping time. -/
theorem sourceCalendar_gate_interval_restrict (theta : ℕ)
    (htheta : 1 ≤ theta ∧ theta ≤ p.T + 1) :
    let E := ReferenceLocalReleaseGateChronology.sourceRun rate z rewards C_star C_h hcross
      s count helapsed hspan
    let alpha := ReferenceLocalReleaseGateChronology.gateAlpha b E.records
    let beta := min (ReferenceLocalReleaseGateChronology.gateBeta b E.records) theta
    let left := if alpha < beta then alpha else p.T + 1
    let right := if alpha < beta then beta else p.T + 1
    Finset.image (fun k : ℕ => k + 1)
        ((calendarGateSupport rate z rewards C_star C_h hcross s count helapsed hspan b).filter
          (fun k => k + 1 < theta)) = Finset.Ico left right ∧
      1 ≤ left ∧ left ≤ right ∧ right ≤ p.T + 1 := by
  let E := ReferenceLocalReleaseGateChronology.sourceRun rate z rewards C_star C_h hcross
    s count helapsed hspan
  let alpha := ReferenceLocalReleaseGateChronology.gateAlpha b E.records
  let beta := min (ReferenceLocalReleaseGateChronology.gateBeta b E.records) theta
  let left := if alpha < beta then alpha else p.T + 1
  let right := if alpha < beta then beta else p.T + 1
  have himage :
      Finset.image (fun k : ℕ => k + 1)
          ((calendarGateSupport rate z rewards C_star C_h hcross s count helapsed hspan b).filter
            (fun k => k + 1 < theta)) =
        (ReferenceLocalReleaseGateChronology.gateSupport b E.records).filter (· < theta) := by
    ext t
    constructor
    · intro ht
      obtain ⟨k, hk, hkt⟩ := Finset.mem_image.mp ht
      have hmember : t ∈ ReferenceLocalReleaseGateChronology.gateSupport b E.records := by
        rw [← calendarGateSupport_image rate z rewards C_star C_h hcross s count helapsed hspan b]
        exact Finset.mem_image.mpr ⟨k, (Finset.mem_filter.mp hk).1, hkt⟩
      have hthetaT : t < theta := by simpa [hkt] using (Finset.mem_filter.mp hk).2
      exact Finset.mem_filter.mpr ⟨hmember, hthetaT⟩
    · intro ht
      rcases Finset.mem_filter.mp ht with ⟨hgate, htheta'⟩
      have himage' : t ∈ Finset.image (fun k : ℕ => k + 1)
          (calendarGateSupport rate z rewards C_star C_h hcross s count helapsed hspan b) := by
        rw [calendarGateSupport_image rate z rewards C_star C_h hcross s count helapsed hspan b]
        simpa only [E] using hgate
      obtain ⟨k, hk, hkt⟩ := Finset.mem_image.mp himage'
      have hthetaK : k + 1 < theta := by simpa [hkt] using htheta'
      exact Finset.mem_image.mpr ⟨k, Finset.mem_filter.mpr ⟨hk, hthetaK⟩, hkt⟩
  have hrestrict := ReferenceLocalReleasePendingHistory.source_local_gate_interval_restrict
    rate z rewards C_star C_h hcross s count helapsed hspan b theta htheta
  dsimp only [E, alpha, beta, left, right] at hrestrict ⊢
  rw [himage]
  exact hrestrict

/-- Every observed true local gate lies in G's produced gate interval. The
interval is determined by gates alone and makes no pending-nonempty assumption. -/
theorem calendarGate_inside_interval (k : ℕ)
    (hgate : calendarGate rate z rewards C_star C_h hcross s count helapsed hspan b k = some true) :
    ReferenceLocalReleaseGateChronology.gateAlpha b
        (SourceRun rate z rewards C_star C_h hcross s count helapsed hspan).records ≤ k + 1 ∧
      k + 1 < ReferenceLocalReleaseGateChronology.gateBeta b
        (SourceRun rate z rewards C_star C_h hcross s count helapsed hspan).records := by
  have hrecord : ∃ r, calendarRecord rate z rewards C_star C_h hcross s count helapsed hspan k = some r := by
    cases hr : calendarRecord rate z rewards C_star C_h hcross s count helapsed hspan k with
    | none => simp [calendarGate, hr] at hgate
    | some r => exact ⟨r, rfl⟩
  obtain ⟨r, hr⟩ := hrecord
  have hfacts := (calendarRecord_eq_some_iff rate z rewards C_star C_h hcross s count helapsed
    hspan  k r).mp hr
  have hactualGate : ReferenceRetainedReleasePhaseObservation.localReleaseGate rate b r.input.time
      (ReferenceActivePhysicalStepMeasurability.encodeState r.input.state) = true := by
    simpa [calendarGate, hr] using hgate
  have hmem := (ReferenceLocalReleaseGateChronology.mem_gateSupport b (k + 1)
      (SourceRun rate z rewards C_star C_h hcross s count helapsed hspan).records).2
    ⟨r, hfacts.1, hactualGate, by omega⟩
  have hinterval := ReferenceLocalReleaseGateChronology.source_local_gate_interval
    rate z rewards C_star C_h hcross s count helapsed hspan b
  rcases hinterval with ⟨hsupport, _⟩
  rw [hsupport] at hmem
  exact Finset.mem_Ico.mp hmem

/-- Nonempty calendar pending observations are inside the gate interval. The
gate interval itself is independent of pending-set nonemptiness. -/
theorem calendarPending_nonempty_inside_interval (k : ℕ)
    (P : Finset (Fin (p.m - 1)))
    (hP : calendarPending rate z rewards C_star C_h hcross s count helapsed hspan b k = some P) :
    ReferenceLocalReleaseGateChronology.gateAlpha b
        (SourceRun rate z rewards C_star C_h hcross s count helapsed hspan).records ≤ k + 1 ∧
      k + 1 < ReferenceLocalReleaseGateChronology.gateBeta b
        (SourceRun rate z rewards C_star C_h hcross s count helapsed hspan).records :=
  calendarGate_inside_interval rate z rewards C_star C_h hcross s count helapsed hspan b k
    (calendarPending_some_implies_gate rate z rewards C_star C_h hcross s count helapsed
      hspan b k P hP)

/-- Every present lookup is one actual indexed source record, with offset
`k-s`; this makes the calendar lookup unique by source-round identity. -/
theorem calendarRecord_sourceIndex (k : ℕ) (r : Record (p := p) (rate := rate))
    (hlookup : calendarRecord rate z rewards C_star C_h hcross s count helapsed hspan k = some r) :
    ∃ j : Fin count,
      j.val = k - s ∧
      ReferenceLocalReleasePendingHistory.sourceRecord rate z rewards C_star C_h hcross s count
        helapsed hspan j.val j.isLt = r := by
  by_cases hk : s ≤ k ∧ k < s + count
  · have hEq := Option.some.inj (by simpa [calendarRecord, hk] using hlookup)
    refine ⟨⟨k - s, by omega⟩, rfl, hEq⟩
  · simp [calendarRecord, hk] at hlookup

/-- Pending sets from two true calendar gates are nested in source order.
Both coordinates are within G's actual gate interval, whether or not either
pending set is empty. -/
theorem calendarPending_nested_inside_interval (j k : ℕ) (hjk : j < k)
    (hgateJ : calendarGate rate z rewards C_star C_h hcross s count helapsed hspan b j = some true)
    (hgateK : calendarGate rate z rewards C_star C_h hcross s count helapsed hspan b k = some true)
    (pendingJ pendingK : Finset (Fin (p.m - 1)))
    (hPendingJ : calendarPending rate z rewards C_star C_h hcross s count helapsed hspan b j =
      some pendingJ)
    (hPendingK : calendarPending rate z rewards C_star C_h hcross s count helapsed hspan b k =
      some pendingK) :
    ReferenceLocalReleaseGateChronology.gateAlpha b
        (SourceRun rate z rewards C_star C_h hcross s count helapsed hspan).records ≤ j + 1 ∧
      j + 1 < ReferenceLocalReleaseGateChronology.gateBeta b
        (SourceRun rate z rewards C_star C_h hcross s count helapsed hspan).records ∧
      ReferenceLocalReleaseGateChronology.gateAlpha b
        (SourceRun rate z rewards C_star C_h hcross s count helapsed hspan).records ≤ k + 1 ∧
      k + 1 < ReferenceLocalReleaseGateChronology.gateBeta b
        (SourceRun rate z rewards C_star C_h hcross s count helapsed hspan).records ∧
      pendingK ⊆ pendingJ := by
  have hintervalJ := calendarGate_inside_interval rate z rewards C_star C_h hcross s count
    helapsed hspan b j hgateJ
  have hintervalK := calendarGate_inside_interval rate z rewards C_star C_h hcross s count
    helapsed hspan b k hgateK
  have hlookupJExists : ∃ r : Record (p := p) (rate := rate),
      calendarRecord rate z rewards C_star C_h hcross s count helapsed hspan j = some r := by
    cases hrec : calendarRecord rate z rewards C_star C_h hcross s count helapsed hspan j with
    | none => simp [calendarGate, hrec] at hgateJ
    | some r => exact ⟨r, rfl⟩
  obtain ⟨rJ, hlookupJ⟩ := hlookupJExists
  have hlookupKExists : ∃ r : Record (p := p) (rate := rate),
      calendarRecord rate z rewards C_star C_h hcross s count helapsed hspan k = some r := by
    cases hrec : calendarRecord rate z rewards C_star C_h hcross s count helapsed hspan k with
    | none => simp [calendarGate, hrec] at hgateK
    | some r => exact ⟨r, rfl⟩
  obtain ⟨rK, hlookupK⟩ := hlookupKExists
  have hactualGateJ : ReferenceRetainedReleasePhaseObservation.localReleaseGate rate b rJ.input.time
      (ReferenceActivePhysicalStepMeasurability.encodeState rJ.input.state) = true := by
    simpa [calendarGate, hlookupJ] using hgateJ
  have hactualGateK : ReferenceRetainedReleasePhaseObservation.localReleaseGate rate b rK.input.time
      (ReferenceActivePhysicalStepMeasurability.encodeState rK.input.state) = true := by
    simpa [calendarGate, hlookupK] using hgateK
  obtain ⟨jIndex, hjoffset, hjRecord⟩ := calendarRecord_sourceIndex rate z rewards C_star C_h hcross
    s count helapsed hspan j rJ hlookupJ
  obtain ⟨kIndex, hkoffset, hkRecord⟩ := calendarRecord_sourceIndex rate z rewards C_star C_h hcross
    s count helapsed hspan k rK hlookupK
  obtain ⟨M, hsigma, hstoredK, hwhole⟩ := commonPayload_of_calendarGate rate z rewards C_star C_h
    hcross s count helapsed hspan b k rK hlookupK hactualGateK
  have hstoredJ := hwhole rJ
    ((calendarRecord_eq_some_iff rate z rewards C_star C_h hcross s count helapsed hspan  j rJ).mp
      hlookupJ).1 hactualGateJ
  have hentryJ := calendarEntry_eq_actualPending rate z rewards C_star C_h hcross s count
    helapsed hspan b j rJ M hlookupJ hactualGateJ hstoredJ
  have hentryK := calendarEntry_eq_actualPending rate z rewards C_star C_h hcross s count
    helapsed hspan b k rK M hlookupK hactualGateK hstoredK
  have hPendingJ' : calendarPending rate z rewards C_star C_h hcross s count helapsed hspan b j =
      some (ReferencePhysicalReleaseQuota.pendingSet M rJ) := by
    simp [calendarPending, hentryJ]
  have hPendingK' : calendarPending rate z rewards C_star C_h hcross s count helapsed hspan b k =
      some (ReferencePhysicalReleaseQuota.pendingSet M rK) := by
    simp [calendarPending, hentryK]
  have hsetJ : pendingJ = ReferencePhysicalReleaseQuota.pendingSet M rJ :=
    Option.some.inj (hPendingJ.symm.trans hPendingJ')
  have hsetK : pendingK = ReferencePhysicalReleaseQuota.pendingSet M rK :=
    Option.some.inj (hPendingK.symm.trans hPendingK')
  have hroundJ := ReferenceLocalReleasePendingHistory.sourceRecord_sourceRound rate z rewards C_star C_h
    hcross s count helapsed hspan jIndex
  have hroundK := ReferenceLocalReleasePendingHistory.sourceRecord_sourceRound rate z rewards C_star C_h
    hcross s count helapsed hspan kIndex
  have htimeJ : rJ.input.time.val = s + jIndex.val := by
    rw [← hjRecord]
    exact hroundJ.1
  have htimeK : rK.input.time.val = s + kIndex.val := by
    rw [← hkRecord]
    exact hroundK.1
  have hindex : jIndex.val < kIndex.val := by
    have hcalendarJ := (calendarRecord_eq_some_iff rate z rewards C_star C_h hcross s count
      helapsed hspan j rJ).mp hlookupJ |>.2
    have hcalendarK := (calendarRecord_eq_some_iff rate z rewards C_star C_h hcross s count
      helapsed hspan k rK).mp hlookupK |>.2
    omega
  refine ⟨hintervalJ.1, hintervalJ.2, hintervalK.1, hintervalK.2, ?_⟩
  intro i hi
  have hsourceGateJ := hactualGateJ
  rw [← hjRecord] at hsourceGateJ
  have hsourceGateK := hactualGateK
  rw [← hkRecord] at hsourceGateK
  obtain ⟨N, hstoredJ', hstoredK', hNσ, hback⟩ :=
    ReferenceLocalReleasePendingHistory.source_local_gate_pending_history rate z rewards C_star C_h
      hcross s count helapsed hspan b jIndex kIndex hindex i hsourceGateJ hsourceGateK
  have hstoredK'' : ReferenceAssignmentPayloadPersistence.storedPayload
      rK.input.state.coordinator = some N := by
    simpa only [hkRecord] using hstoredK'
  have hNM : N = M := Option.some.inj (hstoredK''.symm.trans hstoredK)
  subst N
  have hiK : i ∈ ReferencePhysicalReleaseQuota.pendingSet M rK := by
    simpa only [hsetK] using hi
  have hiKsource : i ∈ ReferencePhysicalReleaseQuota.pendingSet M
      (ReferenceLocalReleasePendingHistory.sourceRecord rate z rewards C_star C_h hcross s count
        helapsed hspan kIndex.val kIndex.isLt) := by
    simpa only [hkRecord] using hiK
  have hiJ := (hback hiKsource).1
  have hiJ' : i ∈ ReferencePhysicalReleaseQuota.pendingSet M rJ := by
    simpa only [hjRecord] using hiJ
  simpa only [hsetJ] using hiJ'

/-- For a pending follower at calendar `k`, all strictly earlier combined,
UP, and DATA observation counts are zero (hence strictly below quota one).
The payload is extracted from that actual pending record. -/
theorem calendarStrictPriorQuotaAtPending (k : ℕ)
    (pending : Finset (Fin (p.m - 1)))
    (hPending : calendarPending rate z rewards C_star C_h hcross s count helapsed hspan b k =
      some pending)
    (i : Fin (p.m - 1)) (hi : i ∈ pending) :
    calendarReleaseCount rate z rewards C_star C_h hcross s count helapsed hspan b k i = 0 ∧
      calendarUpCount rate z rewards C_star C_h hcross s count helapsed hspan b k i = 0 ∧
      calendarDataCount rate z rewards C_star C_h hcross s count helapsed hspan b k i = 0 ∧
      calendarReleaseCount rate z rewards C_star C_h hcross s count helapsed hspan b k i < 1 ∧
      calendarUpCount rate z rewards C_star C_h hcross s count helapsed hspan b k i < 1 ∧
      calendarDataCount rate z rewards C_star C_h hcross s count helapsed hspan b k i < 1 := by
  have hgate := calendarPending_some_implies_gate rate z rewards C_star C_h hcross s count
    helapsed hspan b k pending hPending
  obtain ⟨r, M, hlookup, hstored, hsigma, hwhole⟩ := commonPayload_at_calendarGate rate z rewards C_star C_h
    hcross s count helapsed hspan b k hgate
  have hactualGate : ReferenceRetainedReleasePhaseObservation.localReleaseGate rate b r.input.time
      (ReferenceActivePhysicalStepMeasurability.encodeState r.input.state) = true := by
    simpa [calendarGate, hlookup] using hgate
  have hentry := calendarEntry_eq_actualPending rate z rewards C_star C_h hcross s count
    helapsed hspan b k r M hlookup hactualGate hstored
  have hcalendarPending : calendarPending rate z rewards C_star C_h hcross s count helapsed hspan b k =
      some (ReferencePhysicalReleaseQuota.pendingSet M r) := by
    simp [calendarPending, hentry]
  have hset : pending = ReferencePhysicalReleaseQuota.pendingSet M r :=
    Option.some.inj (hPending.symm.trans hcalendarPending)
  have hiCurrent : i ∈ ReferencePhysicalReleaseQuota.pendingSet M r := by
    simpa only [hset] using hi
  have hpriorFlags : ∀ r' ∈ ReferenceLocalReleasePendingHistory.sourceLocalGateRecordsBefore rate z rewards
      C_star C_h hcross s count helapsed hspan b (k + 1),
      ReferencePhysicalReleaseQuota.releaseFlag M r' i = false ∧
      ReferencePhysicalReleaseQuota.upFlag M r' i = false ∧
      ReferencePhysicalReleaseQuota.dataFlag M r' i = false := by
    intro r' hr'
    have hfiltered : r' ∈
        ((SourceRun rate z rewards C_star C_h hcross s count helapsed hspan).records.filter
          (fun record => ReferenceRetainedReleasePhaseObservation.localReleaseGate rate b record.input.time
            (ReferenceActivePhysicalStepMeasurability.encodeState record.input.state))).filter
          (fun record => decide (record.input.time.val + 1 < k + 1)) := by
      simpa only [ReferenceLocalReleasePendingHistory.sourceLocalGateRecordsBefore,
        ReferenceLocalReleasePendingHistory.sourceLocalGateRecords,
        ReferenceLocalReleaseGateChronology.sourceRun] using hr'
    have hcut := List.mem_filter.mp hfiltered
    have hpreviousGate := (List.mem_filter.mp hcut.1).2
    have hpreviousMem := (List.mem_filter.mp hcut.1).1
    have hpreviousTime : r'.input.time.val < k := by
      have := of_decide_eq_true hcut.2
      omega
    obtain ⟨j, hj, hrecord⟩ := List.mem_iff_getElem.mp hpreviousMem
    have hlen := sourceRun_record_count rate z rewards C_star C_h hcross s count helapsed hspan
    have hjlt : j < count := by simpa only [hlen] using hj
    let jIndex : Fin count := ⟨j, hjlt⟩
    obtain ⟨kIndex, hkoffset, hcurrentRecord⟩ := calendarRecord_sourceIndex rate z rewards C_star C_h
      hcross s count helapsed hspan k r hlookup
    have hcurrentTime := (calendarRecord_eq_some_iff rate z rewards C_star C_h hcross s count
      helapsed hspan  k r).mp hlookup |>.2
    have hpreviousRecord : r' =
        ReferenceLocalReleasePendingHistory.sourceRecord rate z rewards C_star C_h hcross s count
          helapsed hspan jIndex.val jIndex.isLt := by
      have hget : (SourceRun rate z rewards C_star C_h hcross s count helapsed hspan).records[j]'hj = r' := hrecord
      calc
        r' = (SourceRun rate z rewards C_star C_h hcross s count helapsed hspan).records[j]'hj := hget.symm
        _ = ReferenceLocalReleasePendingHistory.sourceRecord rate z rewards C_star C_h hcross s count
              helapsed hspan jIndex.val jIndex.isLt := by
          rfl
    rw [hpreviousRecord] at hpreviousGate
    have hactualGateCurrent := hactualGate
    rw [← hcurrentRecord] at hactualGateCurrent
    have hroundPrevious := ReferenceLocalReleasePendingHistory.sourceRecord_sourceRound rate z rewards
      C_star C_h hcross s count helapsed hspan jIndex
    have hroundCurrent := ReferenceLocalReleasePendingHistory.sourceRecord_sourceRound rate z rewards
      C_star C_h hcross s count helapsed hspan kIndex
    have hpreviousRoundVal : r'.input.time.val = s + jIndex.val := by
      rw [hpreviousRecord]
      exact hroundPrevious.1
    have hcurrentRoundVal : r.input.time.val = s + kIndex.val := by
      rw [← hcurrentRecord]
      exact hroundCurrent.1
    have hjk : jIndex.val < kIndex.val := by
      omega
    obtain ⟨N, hstoredPrevious, hstoredCurrent, hNsigma, hback⟩ :=
      ReferenceLocalReleasePendingHistory.source_local_gate_pending_history rate z rewards C_star C_h
        hcross s count helapsed hspan b jIndex kIndex hjk i hpreviousGate hactualGateCurrent
    have hstoredCurrent' : ReferenceAssignmentPayloadPersistence.storedPayload
        r.input.state.coordinator = some N := by
      simpa only [hcurrentRecord] using hstoredCurrent
    have hNM : N = M := Option.some.inj (hstoredCurrent'.symm.trans hstored)
    subst N
    have hback' := hback (by simpa only [hcurrentRecord] using hiCurrent)
    refine ⟨?_, ?_, ?_⟩
    · simpa only [hpreviousRecord] using hback'.2.1
    · simpa only [hpreviousRecord] using hback'.2.2.1
    · simpa only [hpreviousRecord] using hback'.2.2.2
  have hreleaseBefore : ReferencePhysicalReleaseQuota.releaseCount M
      (ReferenceLocalReleasePendingHistory.sourceLocalGateRecordsBefore rate z rewards C_star C_h
        hcross s count helapsed hspan b (k + 1)) i = 0 := by
    unfold ReferencePhysicalReleaseQuota.releaseCount
    apply List.countP_eq_zero.mpr
    intro r' hr' htest
    have hfalse := (hpriorFlags r' hr').1
    simp [hfalse] at htest
  have hupBefore : ReferencePhysicalReleaseQuota.upCount M
      (ReferenceLocalReleasePendingHistory.sourceLocalGateRecordsBefore rate z rewards C_star C_h
        hcross s count helapsed hspan b (k + 1)) i = 0 :=
    Nat.eq_zero_of_le_zero (by
      calc
        ReferencePhysicalReleaseQuota.upCount M
            (ReferenceLocalReleasePendingHistory.sourceLocalGateRecordsBefore rate z rewards C_star C_h
              hcross s count helapsed hspan b (k + 1)) i ≤
          ReferencePhysicalReleaseQuota.releaseCount M
            (ReferenceLocalReleasePendingHistory.sourceLocalGateRecordsBefore rate z rewards C_star C_h
              hcross s count helapsed hspan b (k + 1)) i :=
          ReferencePhysicalReleaseQuota.upCount_le_releaseCount M _ i
        _ = 0 := hreleaseBefore)
  have hdataBefore : ReferencePhysicalReleaseQuota.dataCount M
      (ReferenceLocalReleasePendingHistory.sourceLocalGateRecordsBefore rate z rewards C_star C_h
        hcross s count helapsed hspan b (k + 1)) i = 0 :=
    Nat.eq_zero_of_le_zero (by
      calc
        ReferencePhysicalReleaseQuota.dataCount M
            (ReferenceLocalReleasePendingHistory.sourceLocalGateRecordsBefore rate z rewards C_star C_h
              hcross s count helapsed hspan b (k + 1)) i ≤
          ReferencePhysicalReleaseQuota.releaseCount M
            (ReferenceLocalReleasePendingHistory.sourceLocalGateRecordsBefore rate z rewards C_star C_h
              hcross s count helapsed hspan b (k + 1)) i :=
          ReferencePhysicalReleaseQuota.dataCount_le_releaseCount M _ i
        _ = 0 := hreleaseBefore)
  have hcalendarRelease := calendarReleaseCount_eq_of_commonPayload rate z rewards C_star C_h
    hcross s count helapsed hspan b M hwhole k i
  have hcalendarUp := calendarUpCount_eq_of_commonPayload rate z rewards C_star C_h
    hcross s count helapsed hspan b M hwhole k i
  have hcalendarData := calendarDataCount_eq_of_commonPayload rate z rewards C_star C_h
    hcross s count helapsed hspan b M hwhole k i
  have hrelease : calendarReleaseCount rate z rewards C_star C_h hcross s count helapsed hspan b k i = 0 := by
    rw [hcalendarRelease, hreleaseBefore]
  have hup : calendarUpCount rate z rewards C_star C_h hcross s count helapsed hspan b k i = 0 := by
    rw [hcalendarUp, hupBefore]
  have hdata : calendarDataCount rate z rewards C_star C_h hcross s count helapsed hspan b k i = 0 := by
    rw [hcalendarData, hdataBefore]
  omega


/-- Current-record specialization: the common payload is extracted from the
actual record at `k`, so a caller need not supply a global payload witness. -/
theorem sourceCalendar_counts_at_currentGate (k : ℕ)
    (hgate : calendarGate rate z rewards C_star C_h hcross s count helapsed hspan b k = some true) :
    ∃ r : Record (p := p) (rate := rate), ∃ M : Payload (p := p) (rate := rate),
      calendarRecord rate z rewards C_star C_h hcross s count helapsed hspan k = some r ∧
      ReferenceAssignmentPayloadPersistence.storedPayload r.input.state.coordinator = some M ∧
      M.sigma.val = b ∧
      (∀ r' ∈ (SourceRun rate z rewards C_star C_h hcross s count helapsed hspan).records,
        ReferenceRetainedReleasePhaseObservation.localReleaseGate rate b r'.input.time
          (ReferenceActivePhysicalStepMeasurability.encodeState r'.input.state) = true →
        ReferenceAssignmentPayloadPersistence.storedPayload r'.input.state.coordinator = some M) ∧
      ∀ v i,
        calendarUpCount rate z rewards C_star C_h hcross s count helapsed hspan b v i =
          ReferencePhysicalReleaseQuota.upCount M
            (ReferenceLocalReleasePendingHistory.sourceLocalGateRecordsBefore rate z rewards C_star C_h
              hcross s count helapsed hspan b (v + 1)) i ∧
        calendarDataCount rate z rewards C_star C_h hcross s count helapsed hspan b v i =
          ReferencePhysicalReleaseQuota.dataCount M
            (ReferenceLocalReleasePendingHistory.sourceLocalGateRecordsBefore rate z rewards C_star C_h
              hcross s count helapsed hspan b (v + 1)) i ∧
        calendarReleaseCount rate z rewards C_star C_h hcross s count helapsed hspan b v i =
          ReferencePhysicalReleaseQuota.releaseCount M
            (ReferenceLocalReleasePendingHistory.sourceLocalGateRecordsBefore rate z rewards C_star C_h
              hcross s count helapsed hspan b (v + 1)) i ∧
        calendarUpCount rate z rewards C_star C_h hcross s count helapsed hspan b v i ≤ 1 ∧
        calendarDataCount rate z rewards C_star C_h hcross s count helapsed hspan b v i ≤ 1 ∧
        calendarReleaseCount rate z rewards C_star C_h hcross s count helapsed hspan b v i ≤ 1 := by
  obtain ⟨r, M, hlookup, hstored, hsigma, hwhole⟩ := commonPayload_at_calendarGate rate z rewards C_star C_h
    hcross s count helapsed hspan b k hgate
  refine ⟨r, M, hlookup, hstored, hsigma, hwhole, ?_⟩
  intro v i
  have hup := calendarUpCount_eq_of_commonPayload rate z rewards C_star C_h hcross s count
    helapsed hspan b M hwhole v i
  have hdata := calendarDataCount_eq_of_commonPayload rate z rewards C_star C_h hcross s count
    helapsed hspan b M hwhole v i
  have hrelease := calendarReleaseCount_eq_of_commonPayload rate z rewards C_star C_h hcross s count
    helapsed hspan b M hwhole v i
  have hupBound := ReferenceLocalReleasePendingHistory.sourceLocalGateRecordsBefore_upCount_le_one
    rate z rewards C_star C_h hcross s count helapsed hspan b (v + 1) M i
  have hdataBound := ReferenceLocalReleasePendingHistory.sourceLocalGateRecordsBefore_dataCount_le_one
    rate z rewards C_star C_h hcross s count helapsed hspan b (v + 1) M i
  have hreleaseBound := ReferenceLocalReleasePendingHistory.sourceLocalGateRecordsBefore_releaseCount_le_one
    rate z rewards C_star C_h hcross s count helapsed hspan b (v + 1) M i
  rw [hup, hdata, hrelease]
  exact ⟨rfl, rfl, rfl, hupBound, hdataBound, hreleaseBound⟩

/-- An empty gate support yields empty finite observations and zero calendar
counts. No default or invented payload is chosen in this branch. -/
theorem sourceCalendar_counts_zero_of_empty_gateSupport
    (hempty : ¬ (ReferenceLocalReleaseGateChronology.gateSupport b
      (SourceRun rate z rewards C_star C_h hcross s count helapsed hspan).records).Nonempty) :
    ∀ v i,
      calendarReleaseCount rate z rewards C_star C_h hcross s count helapsed hspan b v i = 0 ∧
      calendarUpCount rate z rewards C_star C_h hcross s count helapsed hspan b v i = 0 ∧
      calendarDataCount rate z rewards C_star C_h hcross s count helapsed hspan b v i = 0 := by
  intro v i
  have hpendingNone : ∀ k,
      calendarPending rate z rewards C_star C_h hcross s count helapsed hspan b k = none := by
    intro k
    cases hpending : calendarPending rate z rewards C_star C_h hcross s count helapsed hspan b k with
    | none => rfl
    | some P =>
        have hgate := calendarPending_some_implies_gate rate z rewards C_star C_h hcross s count
          helapsed hspan b k P hpending
        cases hrecord : calendarRecord rate z rewards C_star C_h hcross s count helapsed hspan k with
        | none => simp [calendarGate, hrecord] at hgate
        | some r =>
            have hactualGate : ReferenceRetainedReleasePhaseObservation.localReleaseGate rate b r.input.time
                (ReferenceActivePhysicalStepMeasurability.encodeState r.input.state) = true := by
              simpa [calendarGate, hrecord] using hgate
            have hfacts := (calendarRecord_eq_some_iff rate z rewards C_star C_h hcross s count
              helapsed hspan  k r).mp hrecord
            have hmem := (ReferenceLocalReleaseGateChronology.mem_gateSupport b (k + 1)
                (SourceRun rate z rewards C_star C_h hcross s count helapsed hspan).records).2
              ⟨r, hfacts.1, hactualGate, by omega⟩
            exact (hempty ⟨k + 1, hmem⟩).elim
  have hrelease : calendarReleaseCount rate z rewards C_star C_h hcross s count helapsed hspan b v i = 0 := by
    simp [calendarReleaseCount, calendarIndicator, hpendingNone]
  have hup : calendarUpCount rate z rewards C_star C_h hcross s count helapsed hspan b v i = 0 := by
    simp [calendarUpCount, calendarIndicator, hpendingNone]
  have hdata : calendarDataCount rate z rewards C_star C_h hcross s count helapsed hspan b v i = 0 := by
    simp [calendarDataCount, calendarIndicator, hpendingNone]
  exact ⟨hrelease, hup, hdata⟩

/-- With zero observed physical rounds, G's actual source run has no records
and every finite calendar lookup is absent. -/
theorem sourceCalendar_absent_of_zero_count (hzero : count = 0) (i : Fin (p.m - 1)) :
    (SourceRun rate z rewards C_star C_h hcross s count helapsed hspan).records = [] ∧
      ∀ k,
        calendarRecord rate z rewards C_star C_h hcross s count helapsed hspan k = none ∧
        calendarGate rate z rewards C_star C_h hcross s count helapsed hspan b k = none ∧
        calendarEntry rate z rewards C_star C_h hcross s count helapsed hspan b k = none ∧
        calendarPending rate z rewards C_star C_h hcross s count helapsed hspan b k = none ∧
        calendarReleaseFlag rate z rewards C_star C_h hcross s count helapsed hspan b k i = none ∧
        calendarUpFlag rate z rewards C_star C_h hcross s count helapsed hspan b k i = none ∧
        calendarDataFlag rate z rewards C_star C_h hcross s count helapsed hspan b k i = none := by
  subst count
  have hrecords := ReferenceLocalReleaseGateChronology.sourceRun_zero_records
    rate z rewards C_star C_h hcross s helapsed hspan
  refine ⟨?_, ?_⟩
  · simpa only [SourceRun] using hrecords
  · intro k
    have hlookup : calendarRecord rate z rewards C_star C_h hcross s 0 helapsed hspan k = none := by
      unfold calendarRecord
      split
      · rename_i hk
        omega
      · rfl
    simp [hlookup, calendarGate, calendarEntry, calendarPending, calendarReleaseFlag,
      calendarUpFlag, calendarDataFlag, calendarFlag]

/-- At terminal launch `s=T`, the span condition forces zero rounds. The
terminal case has no `Fin T` action or calendar record. -/
theorem sourceCalendar_absent_of_terminal (hterminal : s = p.T) :
    (SourceRun rate z rewards C_star C_h hcross s count helapsed hspan).records = [] ∧
      ∀ k,
        calendarRecord rate z rewards C_star C_h hcross s count helapsed hspan k = none ∧
        calendarGate rate z rewards C_star C_h hcross s count helapsed hspan b k = none ∧
        calendarEntry rate z rewards C_star C_h hcross s count helapsed hspan b k = none ∧
        calendarPending rate z rewards C_star C_h hcross s count helapsed hspan b k = none := by
  have hzero : count = 0 := by omega
  let i0 : Fin (p.m - 1) := ⟨0, by have hm := p.two_le_m; omega⟩
  obtain ⟨hrecords, hreadouts⟩ := sourceCalendar_absent_of_zero_count rate z rewards C_star C_h
    hcross s count helapsed hspan b hzero i0
  refine ⟨hrecords, ?_⟩
  intro k
  exact ⟨(hreadouts k).1, (hreadouts k).2.1, (hreadouts k).2.2.1, (hreadouts k).2.2.2.1⟩





end Bandits.Support.ReferenceLocalReleaseCalendarCounts

end noncomputable section
