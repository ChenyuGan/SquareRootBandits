/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceLocalReleaseCalendarCounts
public import Bandits.Support.PhaseServiceWaiting

import Lean.Elab.Tactic.Omega

/-!
# Actual-source local-release waiting paths

Sources: `sources/zip4/manuscript/05_binary_transport.tex:74-88,180-240,293-348`,
`sources/zip4/manuscript/06_interruptions.tex:435-492`,
`sources/zip4/manuscript/07_public_setup.tex:121-164`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-79`.

This module restricts the finite actual-source calendar observations to an
arbitrary pathwise endpoint. Its carrier is the original source input subtype
at the actual crossing and launch-at-`s` branch. The endpoint is not asserted to
be a stopping time. The resulting `PhaseServiceWaiting.N` identities and
within-local-gate interval facts are deterministic; this module constructs no
measure, filtration, conditional-service law, or stopped-source support.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ReferenceLocalReleaseWaitingPaths

open ConstructorDimensions ReferenceActivePhysicalStep
open ReferenceActivePhysicalStepMeasurability
open ReferenceLocalReleaseGateChronology
open ReferencePhysicalReleaseQuota
open ReferenceRetainedReleasePhaseObservation
open scoped Classical

variable {p : ConstructorDimensions.Parameters}

/-- The literal original-source branch with actual crossing and elapsed
launch. Every value retains the full `SourceInput`, including all rows,
private arrays, and the original selected index `J`. -/
abbrev SourceEvent (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) :=
  { z : BootstrapPrivateRoundStreams.SourceInput p //
    (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true ∧
    ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed = s }

variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ) (s : ℕ) (hs : s ≤ p.T) (b : ℕ)

/-- The existing G source run on the full original source input, with the
remaining physical span derived from `s ≤ T`. -/
def sourceRunAtLaunch (z : SourceEvent rate rewards C_star C_h s) :=
  ReferenceLocalReleaseGateChronology.sourceRun rate z.val rewards C_star C_h
    z.property.1 s (p.T - s) z.property.2 (by omega)

/-- The actual C pending readout on the source event's original run. -/
def calendarPendingReadout (z : SourceEvent rate rewards C_star C_h s) (k : ℕ) :=
  ReferenceLocalReleaseCalendarCounts.calendarPending rate z.val rewards C_star C_h
    z.property.1 s (p.T - s) z.property.2 (by omega) b k

/-- The actual C UP flag on its own calendar record and stored whole payload. -/
def calendarUpReadout (z : SourceEvent rate rewards C_star C_h s)
    (i : Fin (p.m - 1)) (k : ℕ) :=
  ReferenceLocalReleaseCalendarCounts.calendarUpFlag rate z.val rewards C_star C_h
    z.property.1 s (p.T - s) z.property.2 (by omega) b k i

/-- The actual C DATA flag on its own calendar record and stored whole payload. -/
def calendarDataReadout (z : SourceEvent rate rewards C_star C_h s)
    (i : Fin (p.m - 1)) (k : ℕ) :=
  ReferenceLocalReleaseCalendarCounts.calendarDataFlag rate z.val rewards C_star C_h
    z.property.1 s (p.T - s) z.property.2 (by omega) b k i

/-- The actual combined-release flag on its own calendar record and stored
whole payload. -/
def calendarReleaseReadout (z : SourceEvent rate rewards C_star C_h s)
    (i : Fin (p.m - 1)) (k : ℕ) :=
  ReferenceLocalReleaseCalendarCounts.calendarReleaseFlag rate z.val rewards C_star C_h
    z.property.1 s (p.T - s) z.property.2 (by omega) b k i

/-- The arbitrary endpoint-restricted pending set. `∅` records absence from
this finite phase observation only; it is not an operational fallback. -/
def pendingTheta (theta : SourceEvent rate rewards C_star C_h s → ℕ)
    (k : ℕ) (z : SourceEvent rate rewards C_star C_h s) : Finset (Fin (p.m - 1)) :=
  if k + 1 < theta z then (calendarPendingReadout rate rewards C_star C_h s hs b z k).getD ∅
  else ∅

/-- The raw UP readout with absence represented by `false` only in this finite
observation process. The pending set supplies the separate gate. -/
def upObservation (i : Fin (p.m - 1)) (k : ℕ)
    (z : SourceEvent rate rewards C_star C_h s) : Bool :=
  (calendarUpReadout rate rewards C_star C_h s hs b z i k).getD false

/-- The raw DATA readout with absence represented by `false` only in this
finite observation process. -/
def dataObservation (i : Fin (p.m - 1)) (k : ℕ)
    (z : SourceEvent rate rewards C_star C_h s) : Bool :=
  (calendarDataReadout rate rewards C_star C_h s hs b z i k).getD false

/-- The raw combined-release readout with absence represented by `false` only
in this finite observation process. -/
def releaseObservation (i : Fin (p.m - 1)) (k : ℕ)
    (z : SourceEvent rate rewards C_star C_h s) : Bool :=
  (calendarReleaseReadout rate rewards C_star C_h s hs b z i k).getD false

/-- The first actual one-based local gate coordinate, with G's empty-support
convention. -/
def localGateAlpha (z : SourceEvent rate rewards C_star C_h s) : ℕ :=
  ReferenceLocalReleaseGateChronology.gateAlpha b (sourceRunAtLaunch rate rewards
    C_star C_h s hs z).records

/-- The first excluded local gate coordinate before endpoint restriction. -/
def localGateBeta (z : SourceEvent rate rewards C_star C_h s) : ℕ :=
  ReferenceLocalReleaseGateChronology.gateBeta b (sourceRunAtLaunch rate rewards
    C_star C_h s hs z).records

/-- The source-indexed local phase start after clipping the local gate support
by an arbitrary one-based endpoint. -/
def localPhaseSigma (theta : SourceEvent rate rewards C_star C_h s → ℕ)
    (z : SourceEvent rate rewards C_star C_h s) : ℕ :=
  let beta := min (localGateBeta rate rewards C_star C_h s hs b z) (theta z)
  if localGateAlpha rate rewards C_star C_h s hs b z < beta then
    localGateAlpha rate rewards C_star C_h s hs b z else p.T + 1

/-- The source-indexed first excluded local phase round. Empty restricted
support uses the common `T+1` sentinel. -/
def localPhaseEndpoint (theta : SourceEvent rate rewards C_star C_h s → ℕ)
    (z : SourceEvent rate rewards C_star C_h s) : ℕ :=
  let alpha := localGateAlpha rate rewards C_star C_h s hs b z
  let beta := min (localGateBeta rate rewards C_star C_h s hs b z) (theta z)
  if alpha < beta then beta else p.T + 1

/-- The calendar lookup is exactly the unique record of E at physical round
`k`; no independent trace or state is introduced. -/
theorem calendarRecord_reconstruction
    (z : SourceEvent rate rewards C_star C_h s) (k : ℕ)
    (r : ReferenceLocalReleaseCalendarCounts.Record (p := p) (rate := rate)) :
    ReferenceLocalReleaseCalendarCounts.calendarRecord rate z.val rewards C_star C_h
        z.property.1 s (p.T - s) z.property.2 (by omega) k = some r ↔
      r ∈ (sourceRunAtLaunch rate rewards C_star C_h s hs z).records ∧
        r.input.time.val = k := by
  simpa only [sourceRunAtLaunch, ReferenceLocalReleaseCalendarCounts.SourceRun] using
    (ReferenceLocalReleaseCalendarCounts.calendarRecord_eq_some_iff rate z.val rewards C_star C_h
      z.property.1 s (p.T - s) z.property.2 (by omega) k r)

/-- A present entry is the literal O local-release entry on that actual
record. In particular this equation does not merge `some false` with `none`. -/
theorem calendarEntry_reconstruction
    (z : SourceEvent rate rewards C_star C_h s) (k : ℕ)
    (r : ReferenceLocalReleaseCalendarCounts.Record (p := p) (rate := rate))
    (hlookup : ReferenceLocalReleaseCalendarCounts.calendarRecord rate z.val rewards C_star C_h
      z.property.1 s (p.T - s) z.property.2 (by omega) k = some r) :
    ReferenceLocalReleaseCalendarCounts.calendarEntry rate z.val rewards C_star C_h
      z.property.1 s (p.T - s) z.property.2 (by omega) b k =
      some (ReferenceRetainedReleasePhaseObservation.localReleaseEntry rate b r.input.time
        (ReferenceActivePhysicalStepMeasurability.encodeState r.input.state)) := by
  simp [ReferenceLocalReleaseCalendarCounts.calendarEntry, hlookup]

/-- A present gate is the literal O gate on that same actual record. -/
theorem calendarGate_reconstruction
    (z : SourceEvent rate rewards C_star C_h s) (k : ℕ)
    (r : ReferenceLocalReleaseCalendarCounts.Record (p := p) (rate := rate))
    (hlookup : ReferenceLocalReleaseCalendarCounts.calendarRecord rate z.val rewards C_star C_h
      z.property.1 s (p.T - s) z.property.2 (by omega) k = some r) :
    ReferenceLocalReleaseCalendarCounts.calendarGate rate z.val rewards C_star C_h
      z.property.1 s (p.T - s) z.property.2 (by omega) b k =
      some (ReferenceRetainedReleasePhaseObservation.localReleaseGate rate b r.input.time
        (ReferenceActivePhysicalStepMeasurability.encodeState r.input.state)) := by
  simp [ReferenceLocalReleaseCalendarCounts.calendarGate, hlookup]

/-- At every true actual local gate, C extracts the current record's stored
whole payload and reconstructs its entry, pending set, and all three Q flags.
The pending set may be empty; no pending-nonempty premise is used. -/
theorem sourceReadouts_at_trueGate
    (z : SourceEvent rate rewards C_star C_h s) (k : ℕ)
    (hgate : ReferenceLocalReleaseCalendarCounts.calendarGate rate z.val rewards C_star C_h
      z.property.1 s (p.T - s) z.property.2 (by omega) b k = some true) :
    ∃ (r : ReferenceLocalReleaseCalendarCounts.Record (p := p) (rate := rate))
      (M : ReferenceActivePhysicalStep.Payload rate),
      ReferenceLocalReleaseCalendarCounts.calendarRecord rate z.val rewards C_star C_h
        z.property.1 s (p.T - s) z.property.2 (by omega) k = some r ∧
      ReferenceAssignmentPayloadPersistence.storedPayload r.input.state.coordinator = some M ∧
      M.sigma.val = b ∧
      ReferenceLocalReleaseCalendarCounts.calendarEntry rate z.val rewards C_star C_h
        z.property.1 s (p.T - s) z.property.2 (by omega) b k =
        some (true, some (ReferencePhysicalReleaseQuota.pendingSet M r)) ∧
      ReferenceLocalReleaseCalendarCounts.calendarPending rate z.val rewards C_star C_h
        z.property.1 s (p.T - s) z.property.2 (by omega) b k =
        some (ReferencePhysicalReleaseQuota.pendingSet M r) ∧
      ∀ i,
        ReferenceLocalReleaseCalendarCounts.calendarUpFlag rate z.val rewards C_star C_h
          z.property.1 s (p.T - s) z.property.2 (by omega) b k i =
          some (ReferencePhysicalReleaseQuota.upFlag M r i) ∧
        ReferenceLocalReleaseCalendarCounts.calendarDataFlag rate z.val rewards C_star C_h
          z.property.1 s (p.T - s) z.property.2 (by omega) b k i =
          some (ReferencePhysicalReleaseQuota.dataFlag M r i) ∧
        ReferenceLocalReleaseCalendarCounts.calendarReleaseFlag rate z.val rewards C_star C_h
          z.property.1 s (p.T - s) z.property.2 (by omega) b k i =
          some (ReferencePhysicalReleaseQuota.releaseFlag M r i) := by
  obtain ⟨r, M, hlookup, hstored, hsigma, _⟩ :=
    ReferenceLocalReleaseCalendarCounts.commonPayload_at_calendarGate rate z.val rewards C_star C_h
      z.property.1 s (p.T - s) z.property.2 (by omega) b k hgate
  have hactualGate : ReferenceRetainedReleasePhaseObservation.localReleaseGate rate b r.input.time
      (ReferenceActivePhysicalStepMeasurability.encodeState r.input.state) = true := by
    simpa [ReferenceLocalReleaseCalendarCounts.calendarGate, hlookup] using hgate
  have hentry := ReferenceLocalReleaseCalendarCounts.calendarEntry_eq_actualPending rate z.val
    rewards C_star C_h z.property.1 s (p.T - s) z.property.2 (by omega) b k r M hlookup
    hactualGate hstored
  have hpending : ReferenceLocalReleaseCalendarCounts.calendarPending rate z.val rewards C_star C_h
      z.property.1 s (p.T - s) z.property.2 (by omega) b k =
      some (ReferencePhysicalReleaseQuota.pendingSet M r) := by
    simp [ReferenceLocalReleaseCalendarCounts.calendarPending, hentry]
  refine ⟨r, M, hlookup, hstored, hsigma, hentry, hpending, ?_⟩
  intro i
  have hup := ReferenceLocalReleaseCalendarCounts.calendarFlag_eq_actual rate z.val rewards C_star C_h
    z.property.1 s (p.T - s) z.property.2 (by omega) b k r M hlookup hstored
    ReferencePhysicalReleaseQuota.upFlag i
  have hdata := ReferenceLocalReleaseCalendarCounts.calendarFlag_eq_actual rate z.val rewards C_star C_h
    z.property.1 s (p.T - s) z.property.2 (by omega) b k r M hlookup hstored
    ReferencePhysicalReleaseQuota.dataFlag i
  have hrelease := ReferenceLocalReleaseCalendarCounts.calendarFlag_eq_actual rate z.val rewards C_star C_h
    z.property.1 s (p.T - s) z.property.2 (by omega) b k r M hlookup hstored
    ReferencePhysicalReleaseQuota.releaseFlag i
  exact ⟨by simpa only [ReferenceLocalReleaseCalendarCounts.calendarUpFlag] using hup,
    by simpa only [ReferenceLocalReleaseCalendarCounts.calendarDataFlag] using hdata,
    by simpa only [ReferenceLocalReleaseCalendarCounts.calendarReleaseFlag] using hrelease⟩

/-- The endpoint-restricted process preserves a true gate with an empty Q
pending set as `some ∅`; the gate remains separately observable as true. -/
theorem trueGate_emptyPending_preserved
    (theta : SourceEvent rate rewards C_star C_h s → ℕ)
    (z : SourceEvent rate rewards C_star C_h s) (k : ℕ)
    (hcut : k + 1 < theta z)
    (hgate : ReferenceLocalReleaseCalendarCounts.calendarGate rate z.val rewards C_star C_h
      z.property.1 s (p.T - s) z.property.2 (by omega) b k = some true) :
    ∃ r M,
      ReferenceLocalReleaseCalendarCounts.calendarRecord rate z.val rewards C_star C_h
        z.property.1 s (p.T - s) z.property.2 (by omega) k = some r ∧
      ReferenceAssignmentPayloadPersistence.storedPayload r.input.state.coordinator = some M ∧
      (ReferencePhysicalReleaseQuota.pendingSet M r = ∅ →
        ReferenceLocalReleaseCalendarCounts.calendarGate rate z.val rewards C_star C_h
          z.property.1 s (p.T - s) z.property.2 (by omega) b k = some true ∧
        ReferenceLocalReleaseCalendarCounts.calendarEntry rate z.val rewards C_star C_h
          z.property.1 s (p.T - s) z.property.2 (by omega) b k = some (true, some ∅) ∧
        pendingTheta rate rewards C_star C_h s hs b theta k z = ∅) := by
  obtain ⟨r, M, hlookup, hstored, _, hentry, hpending, _⟩ :=
    sourceReadouts_at_trueGate rate rewards C_star C_h s hs b z k hgate
  refine ⟨r, M, hlookup, hstored, ?_⟩
  intro hempty
  refine ⟨hgate, ?_, ?_⟩
  · simp only [hentry, hempty]
  · simp [pendingTheta, calendarPendingReadout, hcut, hpending, hempty]

private theorem gatedIndicator_eq (cut : Prop) [Decidable cut]
    (i : Fin (p.m - 1)) (pending : Option (Finset (Fin (p.m - 1))))
    (observation : Option Bool) :
    (if i ∈ (if cut then pending.getD ∅ else ∅) ∧ observation.getD false then 1 else 0) =
      if cut then ReferenceLocalReleaseCalendarCounts.calendarIndicator i pending observation else 0 := by
  by_cases hcut : cut
  · cases pending with
    | none => cases observation <;>
        simp [hcut, ReferenceLocalReleaseCalendarCounts.calendarIndicator]
    | some P =>
        cases observation with
        | none => simp [hcut, ReferenceLocalReleaseCalendarCounts.calendarIndicator]
        | some b => cases b <;>
            simp [hcut, ReferenceLocalReleaseCalendarCounts.calendarIndicator]
  · simp [hcut]

/-- Reindex the literal W process against the endpoint-restricted C readout.
This private assembly lemma has an explicit raw-flag equation; the public
specializations below discharge it by reflexivity from C's own projections. -/
private theorem waitingN_eq_restrictedCalendarSum
    (theta : SourceEvent rate rewards C_star C_h s → ℕ)
    (z : SourceEvent rate rewards C_star C_h s) (hlo : 1 ≤ theta z)
    (i : Fin (p.m - 1)) (v : ℕ)
    (X : Fin (p.m - 1) → ℕ → SourceEvent rate rewards C_star C_h s → Bool)
    (flag : Fin (p.m - 1) → ℕ → SourceEvent rate rewards C_star C_h s → Option Bool)
    (hX : ∀ i k, X i k z = (flag i k z).getD false) :
    PhaseServiceWaiting.N (pendingTheta rate rewards C_star C_h s hs b theta)
        X i v z =
      ∑ k ∈ Finset.range (min v (theta z - 1)),
        ReferenceLocalReleaseCalendarCounts.calendarIndicator i
          (calendarPendingReadout rate rewards C_star C_h s hs b z k) (flag i k z) := by
  have hterm : ∀ k ∈ Finset.range v,
      (if i ∈ pendingTheta rate rewards C_star C_h s hs b theta k z ∧ X i k z then 1 else 0) =
        if k + 1 < theta z then
          ReferenceLocalReleaseCalendarCounts.calendarIndicator i
            (calendarPendingReadout rate rewards C_star C_h s hs b z k) (flag i k z)
        else 0 := by
    intro k hk
    rw [hX i k]
    change (if i ∈ (if k + 1 < theta z then
        (calendarPendingReadout rate rewards C_star C_h s hs b z k).getD ∅ else ∅) ∧
        (flag i k z).getD false then 1 else 0) =
      if k + 1 < theta z then ReferenceLocalReleaseCalendarCounts.calendarIndicator i
        (calendarPendingReadout rate rewards C_star C_h s hs b z k) (flag i k z) else 0
    exact gatedIndicator_eq (p := p) (cut := k + 1 < theta z) i
      (calendarPendingReadout rate rewards C_star C_h s hs b z k) (flag i k z)
  let m := min v (theta z - 1)
  have hsubset : Finset.range m ⊆ Finset.range v := by
    exact Finset.range_mono (Nat.min_le_left v (theta z - 1))
  have hzero : ∀ k ∈ Finset.range v, k ∉ Finset.range m →
      (if k + 1 < theta z then
        ReferenceLocalReleaseCalendarCounts.calendarIndicator i
          (calendarPendingReadout rate rewards C_star C_h s hs b z k) (flag i k z)
       else 0) = 0 := by
    intro k hk hnot
    have hkv : k < v := Finset.mem_range.mp hk
    have hknot : ¬ k < m := by
      simpa only [Finset.mem_range] using hnot
    have hknotTheta : ¬ k < theta z - 1 := by
      intro hkTheta
      exact hknot (Nat.lt_min.mpr ⟨hkv, hkTheta⟩)
    have hcut : ¬ k + 1 < theta z := by omega
    simp [hcut]
  have hsumSubset := Finset.sum_subset hsubset hzero
  have hsmall :
      (∑ k ∈ Finset.range m,
        if k + 1 < theta z then
          ReferenceLocalReleaseCalendarCounts.calendarIndicator i
            (calendarPendingReadout rate rewards C_star C_h s hs b z k) (flag i k z)
        else 0) =
      ∑ k ∈ Finset.range m,
        ReferenceLocalReleaseCalendarCounts.calendarIndicator i
          (calendarPendingReadout rate rewards C_star C_h s hs b z k) (flag i k z) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hkm : k < m := Finset.mem_range.mp hk
    have hkTheta : k < theta z - 1 := lt_of_lt_of_le hkm (Nat.min_le_right v (theta z - 1))
    have hcut : k + 1 < theta z := by omega
    simp [hcut]
  rw [PhaseServiceWaiting.N]
  calc
    (∑ k ∈ Finset.range v,
        if i ∈ pendingTheta rate rewards C_star C_h s hs b theta k z ∧ X i k z then 1 else 0) =
      ∑ k ∈ Finset.range v,
        if k + 1 < theta z then
          ReferenceLocalReleaseCalendarCounts.calendarIndicator i
            (calendarPendingReadout rate rewards C_star C_h s hs b z k) (flag i k z)
        else 0 := by
          apply Finset.sum_congr rfl
          intro k hk
          exact hterm k hk
    _ = ∑ k ∈ Finset.range m,
        if k + 1 < theta z then
          ReferenceLocalReleaseCalendarCounts.calendarIndicator i
            (calendarPendingReadout rate rewards C_star C_h s hs b z k) (flag i k z)
        else 0 := hsumSubset.symm
    _ = ∑ k ∈ Finset.range m,
        ReferenceLocalReleaseCalendarCounts.calendarIndicator i
          (calendarPendingReadout rate rewards C_star C_h s hs b z k) (flag i k z) := hsmall

/-- The endpoint-restricted W UP count is exactly C's actual calendar count
through `min v (theta-1)`, with W's zero-based horizon unchanged. -/
theorem up_N_eq_calendarUpCount
    (theta : SourceEvent rate rewards C_star C_h s → ℕ)
    (htheta : ∀ z, 1 ≤ theta z ∧ theta z ≤ p.T + 1)
    (z : SourceEvent rate rewards C_star C_h s) (v : ℕ) (i : Fin (p.m - 1)) :
    PhaseServiceWaiting.N (pendingTheta rate rewards C_star C_h s hs b theta)
        (upObservation rate rewards C_star C_h s hs b) i v z =
      ReferenceLocalReleaseCalendarCounts.calendarUpCount rate z.val rewards C_star C_h
        z.property.1 s (p.T - s) z.property.2 (by omega) b (min v (theta z - 1)) i := by
  have h := waitingN_eq_restrictedCalendarSum rate rewards C_star C_h s hs b theta
    z (htheta z).1 i v (upObservation rate rewards C_star C_h s hs b)
    (fun i' k' z' => calendarUpReadout rate rewards C_star C_h s hs b z' i' k')
    (by intro i' k'; rfl)
  simpa [upObservation, calendarUpReadout, calendarPendingReadout,
    ReferenceLocalReleaseCalendarCounts.calendarUpCount] using h

/-- The endpoint-restricted W DATA count is exactly C's actual calendar count
through `min v (theta-1)`. -/
theorem data_N_eq_calendarDataCount
    (theta : SourceEvent rate rewards C_star C_h s → ℕ)
    (htheta : ∀ z, 1 ≤ theta z ∧ theta z ≤ p.T + 1)
    (z : SourceEvent rate rewards C_star C_h s) (v : ℕ) (i : Fin (p.m - 1)) :
    PhaseServiceWaiting.N (pendingTheta rate rewards C_star C_h s hs b theta)
        (dataObservation rate rewards C_star C_h s hs b) i v z =
      ReferenceLocalReleaseCalendarCounts.calendarDataCount rate z.val rewards C_star C_h
        z.property.1 s (p.T - s) z.property.2 (by omega) b (min v (theta z - 1)) i := by
  have h := waitingN_eq_restrictedCalendarSum rate rewards C_star C_h s hs b theta
    z (htheta z).1 i v (dataObservation rate rewards C_star C_h s hs b)
    (fun i' k' z' => calendarDataReadout rate rewards C_star C_h s hs b z' i' k')
    (by intro i' k'; rfl)
  simpa [dataObservation, calendarDataReadout, calendarPendingReadout,
    ReferenceLocalReleaseCalendarCounts.calendarDataCount] using h

/-- The endpoint-restricted W combined-release count is exactly C's actual
calendar count through `min v (theta-1)`. -/
theorem release_N_eq_calendarReleaseCount
    (theta : SourceEvent rate rewards C_star C_h s → ℕ)
    (htheta : ∀ z, 1 ≤ theta z ∧ theta z ≤ p.T + 1)
    (z : SourceEvent rate rewards C_star C_h s) (v : ℕ) (i : Fin (p.m - 1)) :
    PhaseServiceWaiting.N (pendingTheta rate rewards C_star C_h s hs b theta)
        (releaseObservation rate rewards C_star C_h s hs b) i v z =
      ReferenceLocalReleaseCalendarCounts.calendarReleaseCount rate z.val rewards C_star C_h
        z.property.1 s (p.T - s) z.property.2 (by omega) b (min v (theta z - 1)) i := by
  have h := waitingN_eq_restrictedCalendarSum rate rewards C_star C_h s hs b theta
    z (htheta z).1 i v (releaseObservation rate rewards C_star C_h s hs b)
    (fun i' k' z' => calendarReleaseReadout rate rewards C_star C_h s hs b z' i' k')
    (by intro i' k'; rfl)
  simpa [releaseObservation, calendarReleaseReadout, calendarPendingReadout,
    ReferenceLocalReleaseCalendarCounts.calendarReleaseCount] using h

/-- With the unrestricted endpoint `T+1`, the W UP process agrees with C's
calendar count at every physical horizon `v ≤ T`. -/
theorem up_N_eq_calendarUpCount_unrestricted
    (z : SourceEvent rate rewards C_star C_h s) (v : ℕ) (hv : v ≤ p.T)
    (i : Fin (p.m - 1)) :
    PhaseServiceWaiting.N
        (pendingTheta rate rewards C_star C_h s hs b (fun _ => p.T + 1))
        (upObservation rate rewards C_star C_h s hs b) i v z =
      ReferenceLocalReleaseCalendarCounts.calendarUpCount rate z.val rewards C_star C_h
        z.property.1 s (p.T - s) z.property.2 (by omega) b v i := by
  have h := up_N_eq_calendarUpCount rate rewards C_star C_h s hs b
    (fun _ => p.T + 1) (by intro z; constructor <;> omega) z v i
  have hmin : min v p.T = v := Nat.min_eq_left hv
  simpa [hmin] using h

/-- Unrestricted-endpoint DATA counts agree at every physical horizon. -/
theorem data_N_eq_calendarDataCount_unrestricted
    (z : SourceEvent rate rewards C_star C_h s) (v : ℕ) (hv : v ≤ p.T)
    (i : Fin (p.m - 1)) :
    PhaseServiceWaiting.N
        (pendingTheta rate rewards C_star C_h s hs b (fun _ => p.T + 1))
        (dataObservation rate rewards C_star C_h s hs b) i v z =
      ReferenceLocalReleaseCalendarCounts.calendarDataCount rate z.val rewards C_star C_h
        z.property.1 s (p.T - s) z.property.2 (by omega) b v i := by
  have h := data_N_eq_calendarDataCount rate rewards C_star C_h s hs b
    (fun _ => p.T + 1) (by intro z; constructor <;> omega) z v i
  have hmin : min v p.T = v := Nat.min_eq_left hv
  simpa [hmin] using h

/-- Unrestricted-endpoint combined-release counts agree at every physical
horizon. -/
theorem release_N_eq_calendarReleaseCount_unrestricted
    (z : SourceEvent rate rewards C_star C_h s) (v : ℕ) (hv : v ≤ p.T)
    (i : Fin (p.m - 1)) :
    PhaseServiceWaiting.N
        (pendingTheta rate rewards C_star C_h s hs b (fun _ => p.T + 1))
        (releaseObservation rate rewards C_star C_h s hs b) i v z =
      ReferenceLocalReleaseCalendarCounts.calendarReleaseCount rate z.val rewards C_star C_h
        z.property.1 s (p.T - s) z.property.2 (by omega) b v i := by
  have h := release_N_eq_calendarReleaseCount rate rewards C_star C_h s hs b
    (fun _ => p.T + 1) (by intro z; constructor <;> omega) z v i
  have hmin : min v p.T = v := Nat.min_eq_left hv
  simpa [hmin] using h

/-- The exact one-based image of the restricted actual gate support is the
closed-at-start/open-at-end local interval with the required empty sentinel. -/
theorem local_gate_interval_restrict
    (theta : SourceEvent rate rewards C_star C_h s → ℕ)
    (htheta : ∀ z, 1 ≤ theta z ∧ theta z ≤ p.T + 1)
    (z : SourceEvent rate rewards C_star C_h s) :
    Finset.image (fun k : ℕ => k + 1)
        ((ReferenceLocalReleaseCalendarCounts.calendarGateSupport rate z.val rewards C_star C_h
          z.property.1 s (p.T - s) z.property.2 (by omega) b).filter
          (fun k => k + 1 < theta z)) =
        Finset.Ico (localPhaseSigma rate rewards C_star C_h s hs b theta z)
          (localPhaseEndpoint rate rewards C_star C_h s hs b theta z) ∧
      1 ≤ localPhaseSigma rate rewards C_star C_h s hs b theta z ∧
      localPhaseSigma rate rewards C_star C_h s hs b theta z ≤
        localPhaseEndpoint rate rewards C_star C_h s hs b theta z ∧
      localPhaseEndpoint rate rewards C_star C_h s hs b theta z ≤ p.T + 1 := by
  have h := ReferenceLocalReleaseCalendarCounts.sourceCalendar_gate_interval_restrict rate z.val
    rewards C_star C_h z.property.1 s (p.T - s) z.property.2 (by omega) b (theta z) (htheta z)
  simpa [localPhaseSigma, localPhaseEndpoint, localGateAlpha, localGateBeta,
    sourceRunAtLaunch] using h

/-- Numerical interval membership recovers the actual calendar gate and its
endpoint condition. The caller supplies only the interval coordinates. -/
private theorem calendarGate_of_interval_membership
    (theta : SourceEvent rate rewards C_star C_h s → ℕ)
    (htheta : ∀ z, 1 ≤ theta z ∧ theta z ≤ p.T + 1)
    (z : SourceEvent rate rewards C_star C_h s) (k : ℕ)
    (hstart : localPhaseSigma rate rewards C_star C_h s hs b theta z ≤ k + 1)
    (hexit : k + 1 < localPhaseEndpoint rate rewards C_star C_h s hs b theta z) :
    ReferenceLocalReleaseCalendarCounts.calendarGate rate z.val rewards C_star C_h
      z.property.1 s (p.T - s) z.property.2 (by omega) b k = some true ∧
      k + 1 < theta z := by
  have hinterval := local_gate_interval_restrict rate rewards C_star C_h s hs b theta htheta z
  have hcoord : k + 1 ∈ Finset.Ico
      (localPhaseSigma rate rewards C_star C_h s hs b theta z)
      (localPhaseEndpoint rate rewards C_star C_h s hs b theta z) :=
    Finset.mem_Ico.mpr ⟨hstart, hexit⟩
  have himage : k + 1 ∈ Finset.image (fun j : ℕ => j + 1)
      ((ReferenceLocalReleaseCalendarCounts.calendarGateSupport rate z.val rewards C_star C_h
        z.property.1 s (p.T - s) z.property.2 (by omega) b).filter
        (fun j => j + 1 < theta z)) := by
    rw [hinterval.1]
    exact hcoord
  obtain ⟨j, hj, hjk⟩ := Finset.mem_image.mp himage
  have hEq : j = k := by omega
  subst j
  rcases Finset.mem_filter.mp hj with ⟨hsupport, hcut⟩
  have hsupport' := hsupport
  unfold ReferenceLocalReleaseCalendarCounts.calendarGateSupport at hsupport'
  exact ⟨(Finset.mem_filter.mp hsupport').2, hcut⟩

/-- A nonempty endpoint-restricted pending set lies within the produced local
phase interval. Gate support, not pending nonemptiness, defines the endpoints. -/
theorem pendingTheta_phase_support
    (theta : SourceEvent rate rewards C_star C_h s → ℕ)
    (z : SourceEvent rate rewards C_star C_h s) (k : ℕ)
    (hP : (pendingTheta rate rewards C_star C_h s hs b theta k z).Nonempty) :
    localPhaseSigma rate rewards C_star C_h s hs b theta z ≤ k + 1 ∧
      k + 1 < localPhaseEndpoint rate rewards C_star C_h s hs b theta z := by
  by_cases hcut : k + 1 < theta z
  · cases hraw : calendarPendingReadout rate rewards C_star C_h s hs b z k with
    | none => simp [pendingTheta, hcut, hraw] at hP
    | some P =>
        have hPtheta : pendingTheta rate rewards C_star C_h s hs b theta k z = P := by
          simp [pendingTheta, hcut, hraw]
        have hgateInterval :=
          ReferenceLocalReleaseCalendarCounts.calendarPending_nonempty_inside_interval rate z.val
            rewards C_star C_h z.property.1 s (p.T - s) z.property.2 (by omega) b k P hraw
        have hstart : localGateAlpha rate rewards C_star C_h s hs b z ≤ k + 1 := by
          simpa [localGateAlpha, sourceRunAtLaunch] using hgateInterval.1
        have hbeta : k + 1 < min (localGateBeta rate rewards C_star C_h s hs b z) (theta z) :=
          Nat.lt_min.mpr ⟨by simpa [localGateBeta, sourceRunAtLaunch] using hgateInterval.2,
            hcut⟩
        have halphaBeta : localGateAlpha rate rewards C_star C_h s hs b z <
            min (localGateBeta rate rewards C_star C_h s hs b z) (theta z) :=
          lt_of_le_of_lt hstart hbeta
        constructor
        · simpa [localPhaseSigma, halphaBeta] using hstart
        · simpa [localPhaseEndpoint, halphaBeta] using hbeta
  · simp [pendingTheta, hcut] at hP

/-- The endpoint-restricted readout is empty outside its local interval. -/
theorem pendingTheta_empty_outside_interval
    (theta : SourceEvent rate rewards C_star C_h s → ℕ)
    (z : SourceEvent rate rewards C_star C_h s) (k : ℕ)
    (hout : ¬ (localPhaseSigma rate rewards C_star C_h s hs b theta z ≤ k + 1 ∧
      k + 1 < localPhaseEndpoint rate rewards C_star C_h s hs b theta z)) :
    pendingTheta rate rewards C_star C_h s hs b theta k z = ∅ := by
  by_cases hcut : k + 1 < theta z
  · cases hraw : calendarPendingReadout rate rewards C_star C_h s hs b z k with
    | none => simp [pendingTheta, hcut, hraw]
    | some P =>
        have hPtheta : pendingTheta rate rewards C_star C_h s hs b theta k z = P := by
          simp [pendingTheta, hcut, hraw]
        rw [hPtheta]
        have hgateInterval :=
          ReferenceLocalReleaseCalendarCounts.calendarPending_nonempty_inside_interval rate z.val
            rewards C_star C_h z.property.1 s (p.T - s) z.property.2 (by omega) b k P hraw
        have hstart : localGateAlpha rate rewards C_star C_h s hs b z ≤ k + 1 := by
          simpa [localGateAlpha, sourceRunAtLaunch] using hgateInterval.1
        have hbeta : k + 1 < min (localGateBeta rate rewards C_star C_h s hs b z) (theta z) :=
          Nat.lt_min.mpr ⟨by simpa [localGateBeta, sourceRunAtLaunch] using hgateInterval.2,
            hcut⟩
        have halphaBeta : localGateAlpha rate rewards C_star C_h s hs b z <
            min (localGateBeta rate rewards C_star C_h s hs b z) (theta z) :=
          lt_of_le_of_lt hstart hbeta
        have hstart' : localPhaseSigma rate rewards C_star C_h s hs b theta z ≤ k + 1 := by
          simpa [localPhaseSigma, halphaBeta] using hstart
        have hexit' : k + 1 < localPhaseEndpoint rate rewards C_star C_h s hs b theta z := by
          simpa [localPhaseEndpoint, halphaBeta] using hbeta
        exact (hout ⟨hstart', hexit'⟩).elim
  · simp [pendingTheta, hcut]

/-- Numerical interval membership produces both genuine entries and payloads
before the actual C nesting theorem is applied. -/
theorem pendingTheta_nested_inside_interval
    (theta : SourceEvent rate rewards C_star C_h s → ℕ)
    (htheta : ∀ z, 1 ≤ theta z ∧ theta z ≤ p.T + 1)
    (z : SourceEvent rate rewards C_star C_h s) (j k : ℕ)
    (hjk : j ≤ k) (hkT : k < p.T)
    (hstart : localPhaseSigma rate rewards C_star C_h s hs b theta z ≤ j + 1)
    (hexit : k + 1 < localPhaseEndpoint rate rewards C_star C_h s hs b theta z) :
    pendingTheta rate rewards C_star C_h s hs b theta k z ⊆
      pendingTheta rate rewards C_star C_h s hs b theta j z := by
  by_cases hsame : j = k
  · subst k
    exact Finset.Subset.rfl
  · have hjk' : j < k := by omega
    have hjexit : j + 1 < localPhaseEndpoint rate rewards C_star C_h s hs b theta z := by
      omega
    have hkstart : localPhaseSigma rate rewards C_star C_h s hs b theta z ≤ k + 1 := by
      omega
    obtain ⟨hgateJ, hcutJ⟩ := calendarGate_of_interval_membership rate rewards C_star C_h s hs b
      theta htheta z j hstart hjexit
    obtain ⟨hgateK, hcutK⟩ := calendarGate_of_interval_membership rate rewards C_star C_h s hs b
      theta htheta z k hkstart hexit
    obtain ⟨rJ, MJ, _, _, _, hentryJ, _, _⟩ :=
      sourceReadouts_at_trueGate rate rewards C_star C_h s hs b z j hgateJ
    obtain ⟨rK, MK, _, _, _, hentryK, _, _⟩ :=
      sourceReadouts_at_trueGate rate rewards C_star C_h s hs b z k hgateK
    have hPendingJ : calendarPendingReadout rate rewards C_star C_h s hs b z j =
        some (ReferencePhysicalReleaseQuota.pendingSet MJ rJ) := by
      simp [calendarPendingReadout, ReferenceLocalReleaseCalendarCounts.calendarPending, hentryJ]
    have hPendingK : calendarPendingReadout rate rewards C_star C_h s hs b z k =
        some (ReferencePhysicalReleaseQuota.pendingSet MK rK) := by
      simp [calendarPendingReadout, ReferenceLocalReleaseCalendarCounts.calendarPending, hentryK]
    have hPthetaJ : pendingTheta rate rewards C_star C_h s hs b theta j z =
        ReferencePhysicalReleaseQuota.pendingSet MJ rJ := by
      simp [pendingTheta, hcutJ, hPendingJ]
    have hPthetaK : pendingTheta rate rewards C_star C_h s hs b theta k z =
        ReferencePhysicalReleaseQuota.pendingSet MK rK := by
      simp [pendingTheta, hcutK, hPendingK]
    have hnested := ReferenceLocalReleaseCalendarCounts.calendarPending_nested_inside_interval
      rate z.val rewards C_star C_h z.property.1 s (p.T - s) z.property.2 (by omega) b j k hjk'
      hgateJ hgateK (ReferencePhysicalReleaseQuota.pendingSet MJ rJ)
      (ReferencePhysicalReleaseQuota.pendingSet MK rK) hPendingJ hPendingK
    rw [hPthetaK, hPthetaJ]
    exact hnested.2.2.2.2

/-- Every endpoint-restricted UP `N` count is at most one. The proof splits
the actual gate-support cases: C supplies the real quota on nonempty support,
and no payload is invented on empty support. -/
theorem up_N_le_one
    (theta : SourceEvent rate rewards C_star C_h s → ℕ)
    (htheta : ∀ z, 1 ≤ theta z ∧ theta z ≤ p.T + 1)
    (z : SourceEvent rate rewards C_star C_h s) (v : ℕ) (i : Fin (p.m - 1)) :
    PhaseServiceWaiting.N (pendingTheta rate rewards C_star C_h s hs b theta)
        (upObservation rate rewards C_star C_h s hs b) i v z ≤ 1 := by
  rw [up_N_eq_calendarUpCount rate rewards C_star C_h s hs b theta htheta z v i]
  by_cases hsupport : (ReferenceLocalReleaseGateChronology.gateSupport b
      (sourceRunAtLaunch rate rewards C_star C_h s hs z).records).Nonempty
  · obtain ⟨M, hsigma, hwhole, hcounts⟩ :=
      ReferenceLocalReleaseCalendarCounts.sourceCalendar_counts_on_nonempty_gateSupport rate z.val
        rewards C_star C_h z.property.1 s (p.T - s) z.property.2 (by omega) b hsupport
    rcases hcounts (min v (theta z - 1)) i with ⟨_, _, _, hup, _, _⟩
    exact hup
  · obtain ⟨_, hup, _⟩ :=
      ReferenceLocalReleaseCalendarCounts.sourceCalendar_counts_zero_of_empty_gateSupport rate z.val
        rewards C_star C_h z.property.1 s (p.T - s) z.property.2 (by omega) b hsupport
        (min v (theta z - 1)) i
    rw [hup]
    exact Nat.zero_le 1

/-- Every endpoint-restricted DATA `N` count is at most one, by the actual
source quota or the empty actual-support branch. -/
theorem data_N_le_one
    (theta : SourceEvent rate rewards C_star C_h s → ℕ)
    (htheta : ∀ z, 1 ≤ theta z ∧ theta z ≤ p.T + 1)
    (z : SourceEvent rate rewards C_star C_h s) (v : ℕ) (i : Fin (p.m - 1)) :
    PhaseServiceWaiting.N (pendingTheta rate rewards C_star C_h s hs b theta)
        (dataObservation rate rewards C_star C_h s hs b) i v z ≤ 1 := by
  rw [data_N_eq_calendarDataCount rate rewards C_star C_h s hs b theta htheta z v i]
  by_cases hsupport : (ReferenceLocalReleaseGateChronology.gateSupport b
      (sourceRunAtLaunch rate rewards C_star C_h s hs z).records).Nonempty
  · obtain ⟨M, hsigma, hwhole, hcounts⟩ :=
      ReferenceLocalReleaseCalendarCounts.sourceCalendar_counts_on_nonempty_gateSupport rate z.val
        rewards C_star C_h z.property.1 s (p.T - s) z.property.2 (by omega) b hsupport
    rcases hcounts (min v (theta z - 1)) i with ⟨_, _, _, _, hdata, _⟩
    exact hdata
  · obtain ⟨_, _, hdata⟩ :=
      ReferenceLocalReleaseCalendarCounts.sourceCalendar_counts_zero_of_empty_gateSupport rate z.val
        rewards C_star C_h z.property.1 s (p.T - s) z.property.2 (by omega) b hsupport
        (min v (theta z - 1)) i
    rw [hdata]
    exact Nat.zero_le 1

/-- Every endpoint-restricted combined-release `N` count is at most one, by
the actual source quota or the empty actual-support branch. -/
theorem release_N_le_one
    (theta : SourceEvent rate rewards C_star C_h s → ℕ)
    (htheta : ∀ z, 1 ≤ theta z ∧ theta z ≤ p.T + 1)
    (z : SourceEvent rate rewards C_star C_h s) (v : ℕ) (i : Fin (p.m - 1)) :
    PhaseServiceWaiting.N (pendingTheta rate rewards C_star C_h s hs b theta)
        (releaseObservation rate rewards C_star C_h s hs b) i v z ≤ 1 := by
  rw [release_N_eq_calendarReleaseCount rate rewards C_star C_h s hs b theta htheta z v i]
  by_cases hsupport : (ReferenceLocalReleaseGateChronology.gateSupport b
      (sourceRunAtLaunch rate rewards C_star C_h s hs z).records).Nonempty
  · obtain ⟨M, hsigma, hwhole, hcounts⟩ :=
      ReferenceLocalReleaseCalendarCounts.sourceCalendar_counts_on_nonempty_gateSupport rate z.val
        rewards C_star C_h z.property.1 s (p.T - s) z.property.2 (by omega) b hsupport
    rcases hcounts (min v (theta z - 1)) i with ⟨_, _, _, _, _, hrelease⟩
    exact hrelease
  · obtain ⟨hrelease, _, _⟩ :=
      ReferenceLocalReleaseCalendarCounts.sourceCalendar_counts_zero_of_empty_gateSupport rate z.val
        rewards C_star C_h z.property.1 s (p.T - s) z.property.2 (by omega) b hsupport
        (min v (theta z - 1)) i
    rw [hrelease]
    exact Nat.zero_le 1

/-- The three endpoint-restricted W processes all obey quota one at every
horizon, including zero and horizons beyond the physical calendar. -/
theorem all_waiting_N_le_one
    (theta : SourceEvent rate rewards C_star C_h s → ℕ)
    (htheta : ∀ z, 1 ≤ theta z ∧ theta z ≤ p.T + 1)
    (z : SourceEvent rate rewards C_star C_h s) (v : ℕ) (i : Fin (p.m - 1)) :
    PhaseServiceWaiting.N (pendingTheta rate rewards C_star C_h s hs b theta)
        (upObservation rate rewards C_star C_h s hs b) i v z ≤ 1 ∧
    PhaseServiceWaiting.N (pendingTheta rate rewards C_star C_h s hs b theta)
        (dataObservation rate rewards C_star C_h s hs b) i v z ≤ 1 ∧
    PhaseServiceWaiting.N (pendingTheta rate rewards C_star C_h s hs b theta)
        (releaseObservation rate rewards C_star C_h s hs b) i v z ≤ 1 := by
  exact ⟨up_N_le_one rate rewards C_star C_h s hs b theta htheta z v i,
    data_N_le_one rate rewards C_star C_h s hs b theta htheta z v i,
    release_N_le_one rate rewards C_star C_h s hs b theta htheta z v i⟩

/-- A task still pending at endpoint-restricted round `k` has no strictly
prior UP, DATA, or combined-release observation in its W process. The actual
C strict-prior theorem supplies the result after restriction. -/
theorem strict_prior_N_zero_at_pending
    (theta : SourceEvent rate rewards C_star C_h s → ℕ)
    (htheta : ∀ z, 1 ≤ theta z ∧ theta z ≤ p.T + 1)
    (z : SourceEvent rate rewards C_star C_h s) (k : ℕ) (i : Fin (p.m - 1))
    (hi : i ∈ pendingTheta rate rewards C_star C_h s hs b theta k z) :
    PhaseServiceWaiting.N (pendingTheta rate rewards C_star C_h s hs b theta)
        (releaseObservation rate rewards C_star C_h s hs b) i k z = 0 ∧
      PhaseServiceWaiting.N (pendingTheta rate rewards C_star C_h s hs b theta)
        (upObservation rate rewards C_star C_h s hs b) i k z = 0 ∧
      PhaseServiceWaiting.N (pendingTheta rate rewards C_star C_h s hs b theta)
        (dataObservation rate rewards C_star C_h s hs b) i k z = 0 ∧
      PhaseServiceWaiting.N (pendingTheta rate rewards C_star C_h s hs b theta)
        (releaseObservation rate rewards C_star C_h s hs b) i k z < 1 ∧
      PhaseServiceWaiting.N (pendingTheta rate rewards C_star C_h s hs b theta)
        (upObservation rate rewards C_star C_h s hs b) i k z < 1 ∧
      PhaseServiceWaiting.N (pendingTheta rate rewards C_star C_h s hs b theta)
        (dataObservation rate rewards C_star C_h s hs b) i k z < 1 := by
  by_cases hcut : k + 1 < theta z
  · cases hraw : calendarPendingReadout rate rewards C_star C_h s hs b z k with
    | none => simp [pendingTheta, hcut, hraw] at hi
    | some P =>
        have hPtheta : pendingTheta rate rewards C_star C_h s hs b theta k z = P := by
          simp [pendingTheta, hcut, hraw]
        have hiP : i ∈ P := by simpa only [hPtheta] using hi
        have hquota := ReferenceLocalReleaseCalendarCounts.calendarStrictPriorQuotaAtPending rate z.val
          rewards C_star C_h z.property.1 s (p.T - s) z.property.2 (by omega) b k P hraw i hiP
        have hmin : min k (theta z - 1) = k := by omega
        have hrelease : PhaseServiceWaiting.N (pendingTheta rate rewards C_star C_h s hs b theta)
            (releaseObservation rate rewards C_star C_h s hs b) i k z = 0 := by
          rw [release_N_eq_calendarReleaseCount rate rewards C_star C_h s hs b theta htheta z k i,
            hmin]
          exact hquota.1
        have hup : PhaseServiceWaiting.N (pendingTheta rate rewards C_star C_h s hs b theta)
            (upObservation rate rewards C_star C_h s hs b) i k z = 0 := by
          rw [up_N_eq_calendarUpCount rate rewards C_star C_h s hs b theta htheta z k i, hmin]
          exact hquota.2.1
        have hdata : PhaseServiceWaiting.N (pendingTheta rate rewards C_star C_h s hs b theta)
            (dataObservation rate rewards C_star C_h s hs b) i k z = 0 := by
          rw [data_N_eq_calendarDataCount rate rewards C_star C_h s hs b theta htheta z k i, hmin]
          exact hquota.2.2.1
        refine ⟨hrelease, hup, hdata, ?_, ?_, ?_⟩ <;> omega
  · simp [pendingTheta, hcut] at hi

/-- Every zero horizon contributes no W observations, for each of the three
literal processes. -/
theorem waiting_N_zero_horizon
    (theta : SourceEvent rate rewards C_star C_h s → ℕ)
    (z : SourceEvent rate rewards C_star C_h s) (i : Fin (p.m - 1)) :
    PhaseServiceWaiting.N (pendingTheta rate rewards C_star C_h s hs b theta)
        (upObservation rate rewards C_star C_h s hs b) i 0 z = 0 ∧
    PhaseServiceWaiting.N (pendingTheta rate rewards C_star C_h s hs b theta)
        (dataObservation rate rewards C_star C_h s hs b) i 0 z = 0 ∧
    PhaseServiceWaiting.N (pendingTheta rate rewards C_star C_h s hs b theta)
        (releaseObservation rate rewards C_star C_h s hs b) i 0 z = 0 := by
  simp [PhaseServiceWaiting.N]

/-- Endpoint `1` has empty phase support and zero W counts at every horizon. -/
theorem theta_one_empty
    (theta : SourceEvent rate rewards C_star C_h s → ℕ)
    (z : SourceEvent rate rewards C_star C_h s) (hθ : theta z = 1) (k : ℕ) :
    pendingTheta rate rewards C_star C_h s hs b theta k z = ∅ := by
  simp [pendingTheta, hθ]

/-- Under the constant endpoint `1`, all three W counts vanish for every
horizon and follower. -/
theorem waiting_N_zero_at_theta_one
    (theta : SourceEvent rate rewards C_star C_h s → ℕ)
    (z : SourceEvent rate rewards C_star C_h s) (hθ : theta z = 1)
    (v : ℕ) (i : Fin (p.m - 1)) :
    PhaseServiceWaiting.N (pendingTheta rate rewards C_star C_h s hs b theta)
        (upObservation rate rewards C_star C_h s hs b) i v z = 0 ∧
    PhaseServiceWaiting.N (pendingTheta rate rewards C_star C_h s hs b theta)
        (dataObservation rate rewards C_star C_h s hs b) i v z = 0 ∧
    PhaseServiceWaiting.N (pendingTheta rate rewards C_star C_h s hs b theta)
        (releaseObservation rate rewards C_star C_h s hs b) i v z = 0 := by
  simp [PhaseServiceWaiting.N, pendingTheta, hθ]

/-- Empty actual local-gate support produces zero for all three restricted W
counts. This branch uses C's absence theorem and chooses no assignment payload. -/
theorem all_waiting_N_zero_of_empty_gate_support
    (theta : SourceEvent rate rewards C_star C_h s → ℕ)
    (htheta : ∀ z, 1 ≤ theta z ∧ theta z ≤ p.T + 1)
    (z : SourceEvent rate rewards C_star C_h s) (v : ℕ) (i : Fin (p.m - 1))
    (hempty : ¬ (ReferenceLocalReleaseGateChronology.gateSupport b
      (sourceRunAtLaunch rate rewards C_star C_h s hs z).records).Nonempty) :
    PhaseServiceWaiting.N (pendingTheta rate rewards C_star C_h s hs b theta)
        (upObservation rate rewards C_star C_h s hs b) i v z = 0 ∧
    PhaseServiceWaiting.N (pendingTheta rate rewards C_star C_h s hs b theta)
        (dataObservation rate rewards C_star C_h s hs b) i v z = 0 ∧
    PhaseServiceWaiting.N (pendingTheta rate rewards C_star C_h s hs b theta)
        (releaseObservation rate rewards C_star C_h s hs b) i v z = 0 := by
  obtain ⟨hrelease, hup, hdata⟩ :=
    ReferenceLocalReleaseCalendarCounts.sourceCalendar_counts_zero_of_empty_gateSupport rate z.val
      rewards C_star C_h z.property.1 s (p.T - s) z.property.2 (by omega) b hempty
      (min v (theta z - 1)) i
  refine ⟨?_, ?_, ?_⟩
  · rw [up_N_eq_calendarUpCount rate rewards C_star C_h s hs b theta htheta z v i]
    exact hup
  · rw [data_N_eq_calendarDataCount rate rewards C_star C_h s hs b theta htheta z v i]
    exact hdata
  · rw [release_N_eq_calendarReleaseCount rate rewards C_star C_h s hs b theta htheta z v i]
    exact hrelease

/-- A calendar lookup at or after `T` is absent: each actual record has a
`Fin T` round coordinate. No action at round `T` is constructed. -/
theorem calendarRecord_absent_at_or_after_horizon
    (z : SourceEvent rate rewards C_star C_h s) (k : ℕ) (hk : p.T ≤ k) :
    ReferenceLocalReleaseCalendarCounts.calendarRecord rate z.val rewards C_star C_h
      z.property.1 s (p.T - s) z.property.2 (by omega) k = none := by
  cases hlookup : ReferenceLocalReleaseCalendarCounts.calendarRecord rate z.val rewards C_star C_h
      z.property.1 s (p.T - s) z.property.2 (by omega) k with
  | none => rfl
  | some r =>
      have hfacts :=
        (ReferenceLocalReleaseCalendarCounts.calendarRecord_eq_some_iff rate z.val rewards C_star C_h
          z.property.1 s (p.T - s) z.property.2 (by omega) k r).mp hlookup
      omega

/-- At every calendar index `k ≥ T`, the endpoint-restricted task set and all
three finite observations are absent. The physical final round is `T-1`. -/
theorem readouts_absent_at_or_after_horizon
    (theta : SourceEvent rate rewards C_star C_h s → ℕ)
    (htheta : ∀ z, 1 ≤ theta z ∧ theta z ≤ p.T + 1)
    (z : SourceEvent rate rewards C_star C_h s) (k : ℕ) (hk : p.T ≤ k) :
    pendingTheta rate rewards C_star C_h s hs b theta k z = ∅ ∧
      ∀ i,
        upObservation rate rewards C_star C_h s hs b i k z = false ∧
        dataObservation rate rewards C_star C_h s hs b i k z = false ∧
        releaseObservation rate rewards C_star C_h s hs b i k z = false := by
  have hthetaUpper := (htheta z).2
  have hcut : ¬ k + 1 < theta z := by omega
  have hlookup := calendarRecord_absent_at_or_after_horizon rate rewards C_star C_h s hs z k hk
  refine ⟨by simp [pendingTheta, hcut], ?_⟩
  intro i
  have hup : calendarUpReadout rate rewards C_star C_h s hs b z i k = none := by
    simp [calendarUpReadout, ReferenceLocalReleaseCalendarCounts.calendarUpFlag,
      ReferenceLocalReleaseCalendarCounts.calendarFlag, hlookup]
  have hdata : calendarDataReadout rate rewards C_star C_h s hs b z i k = none := by
    simp [calendarDataReadout, ReferenceLocalReleaseCalendarCounts.calendarDataFlag,
      ReferenceLocalReleaseCalendarCounts.calendarFlag, hlookup]
  have hrelease : calendarReleaseReadout rate rewards C_star C_h s hs b z i k = none := by
    simp [calendarReleaseReadout, ReferenceLocalReleaseCalendarCounts.calendarReleaseFlag,
      ReferenceLocalReleaseCalendarCounts.calendarFlag, hlookup]
  exact ⟨by simp [upObservation, hup], by simp [dataObservation, hdata],
    by simp [releaseObservation, hrelease]⟩

/-- At terminal launch `s=T`, the derived full physical span is zero and G's
actual source run has no records. All restricted readouts are absent. -/
theorem terminal_launch_has_empty_source_run
    (hterminal : s = p.T)
    (theta : SourceEvent rate rewards C_star C_h s → ℕ)
    (z : SourceEvent rate rewards C_star C_h s) (k : ℕ) :
    p.T - s = 0 ∧
      (sourceRunAtLaunch rate rewards C_star C_h s hs z).records = [] ∧
      pendingTheta rate rewards C_star C_h s hs b theta k z = ∅ ∧
      ∀ i,
        upObservation rate rewards C_star C_h s hs b i k z = false ∧
        dataObservation rate rewards C_star C_h s hs b i k z = false ∧
        releaseObservation rate rewards C_star C_h s hs b i k z = false := by
  have hzero : p.T - s = 0 := by omega
  let i₀ : Fin (p.m - 1) := ⟨0, by have hm := p.two_le_m; omega⟩
  obtain ⟨hrecords, hreadouts⟩ :=
    ReferenceLocalReleaseCalendarCounts.sourceCalendar_absent_of_zero_count rate z.val rewards
      C_star C_h z.property.1 s (p.T - s) z.property.2 (by omega) b hzero i₀
  have hsourceRecords : (sourceRunAtLaunch rate rewards C_star C_h s hs z).records = [] := by
    simpa only [sourceRunAtLaunch, ReferenceLocalReleaseCalendarCounts.SourceRun] using hrecords
  have hpending : calendarPendingReadout rate rewards C_star C_h s hs b z k = none := by
    exact (hreadouts k).2.2.2.1
  refine ⟨hzero, hsourceRecords, ?_, ?_⟩
  · simp [pendingTheta, hpending]
  · intro i
    have hreadoutsI := ReferenceLocalReleaseCalendarCounts.sourceCalendar_absent_of_zero_count
      rate z.val rewards C_star C_h z.property.1 s (p.T - s) z.property.2 (by omega) b hzero i
    obtain ⟨_, _, _, _, hrelease, hup, hdata⟩ := hreadoutsI.2 k
    have hup' : calendarUpReadout rate rewards C_star C_h s hs b z i k = none := by
      simpa only [calendarUpReadout, ReferenceLocalReleaseCalendarCounts.calendarUpFlag] using hup
    have hdata' : calendarDataReadout rate rewards C_star C_h s hs b z i k = none := by
      simpa only [calendarDataReadout, ReferenceLocalReleaseCalendarCounts.calendarDataFlag] using hdata
    have hrelease' : calendarReleaseReadout rate rewards C_star C_h s hs b z i k = none := by
      simpa only [calendarReleaseReadout, ReferenceLocalReleaseCalendarCounts.calendarReleaseFlag] using
        hrelease
    exact ⟨by simp [upObservation, hup'], by simp [dataObservation, hdata'],
      by simp [releaseObservation, hrelease']⟩

end Bandits.Support.ReferenceLocalReleaseWaitingPaths

end noncomputable section
