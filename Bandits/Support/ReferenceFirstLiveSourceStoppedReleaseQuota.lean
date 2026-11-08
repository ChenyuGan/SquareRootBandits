/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveSourceStoppedReleaseEndpoint
public import Bandits.Support.ReferenceLocalReleaseWaitingPaths

import Lean.Elab.Tactic.Omega

/-!
# Actual stopped first-release calendar quotas

Sources: `sources/zip4/manuscript/05_binary_transport.tex:180-240,293-348`,
`sources/zip4/manuscript/04_slow_fast_learner.tex:140-188,256-264`,
`sources/zip4/manuscript/07_public_setup.tex:127-164`, and
`sources/zip4/manuscript/08_main_theorem.tex:29-42,85-100`.

The natural calendar processes below are finite observations of the original
physical run. Their absence at and beyond `T` does not alter continuation of
physical play. On an actual launch, the processes are identified with the
pathwise waiting readouts at the endpoint already computed by the stopped
source endpoint. Quotas and strict prior counts are then transported without
introducing a service law, safety premise, or alternate trace.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalStepMeasurability
open Bandits.Support.ReferenceLocalReleaseCalendarCounts
open Bandits.Support.ReferenceSourcePrefixHistoryFiltration
open scoped Classical BigOperators

namespace Bandits.Support.ReferenceFirstLiveSourceStoppedReleaseQuota

variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ)

abbrev Source (p : ConstructorDimensions.Parameters) :=
  BootstrapPrivateRoundStreams.SourceInput p

/-! The `Nat` argument is the zero-based source offset; the `Fin T` cast keeps
the original record and its original final physical action. -/

/-- The actual stopped pending readout on the natural calendar. -/
def firstReleasePendingNat (k : ℕ) (z : Source p) : Finset (Fin (p.m - 1)) :=
  if hk : k < p.T then
    ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstReleasePending
      rate rewards C_star C_h z ⟨k, hk⟩
  else ∅

/-- The actual raw UP flag on the natural calendar, with no pending gate
conjoined to the physical observation. -/
def firstReleaseUp (i : Fin (p.m - 1)) (k : ℕ) (z : Source p) : Bool :=
  if hk : k < p.T then
    ReferenceSourcePrefixHistoryFiltration.actualUp rate rewards C_star C_h i
      ⟨k, hk⟩ z
  else false

/-- The actual raw DATA flag on the natural calendar. -/
def firstReleaseData (i : Fin (p.m - 1)) (k : ℕ) (z : Source p) : Bool :=
  if hk : k < p.T then
    ReferenceSourcePrefixHistoryFiltration.actualData rate rewards C_star C_h i
      ⟨k, hk⟩ z
  else false

/-- The actual raw combined-release flag on the natural calendar. -/
def firstReleaseRelease (i : Fin (p.m - 1)) (k : ℕ) (z : Source p) : Bool :=
  if hk : k < p.T then
    ReferenceSourcePrefixHistoryFiltration.actualRelease rate rewards C_star C_h i
      ⟨k, hk⟩ z
  else false

/-- At an actual physical `Fin T` date the pending lift is exactly E's
existing stopped pending readout. -/
theorem firstReleasePendingNat_fin (t : Fin p.T) (z : Source p) :
    firstReleasePendingNat rate rewards C_star C_h t.val z =
      ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstReleasePending
        rate rewards C_star C_h z t := by
  simp [firstReleasePendingNat, t.isLt]

/-- At an actual physical date the UP lift is exactly H's actual UP flag. -/
theorem firstReleaseUp_fin (i : Fin (p.m - 1)) (t : Fin p.T) (z : Source p) :
    firstReleaseUp rate rewards C_star C_h i t.val z =
      ReferenceSourcePrefixHistoryFiltration.actualUp rate rewards C_star C_h i t z := by
  simp [firstReleaseUp, t.isLt]

/-- At an actual physical date the DATA lift is exactly H's actual DATA flag. -/
theorem firstReleaseData_fin (i : Fin (p.m - 1)) (t : Fin p.T) (z : Source p) :
    firstReleaseData rate rewards C_star C_h i t.val z =
      ReferenceSourcePrefixHistoryFiltration.actualData rate rewards C_star C_h i t z := by
  simp [firstReleaseData, t.isLt]

/-- At an actual physical date the combined-release lift is exactly H's actual
release flag. -/
theorem firstReleaseRelease_fin (i : Fin (p.m - 1)) (t : Fin p.T) (z : Source p) :
    firstReleaseRelease rate rewards C_star C_h i t.val z =
      ReferenceSourcePrefixHistoryFiltration.actualRelease rate rewards C_star C_h i t z := by
  simp [firstReleaseRelease, t.isLt]

/-- The pending observation is absent at and after the horizon sentinel. -/
theorem firstReleasePendingNat_absent (z : Source p) (k : ℕ) (hk : p.T ≤ k) :
    firstReleasePendingNat rate rewards C_star C_h k z = ∅ := by
  simp [firstReleasePendingNat, Nat.not_lt.mpr hk]

/-- The UP observation is absent at and after the horizon sentinel. -/
theorem firstReleaseUp_absent (i : Fin (p.m - 1)) (z : Source p) (k : ℕ)
    (hk : p.T ≤ k) : firstReleaseUp rate rewards C_star C_h i k z = false := by
  simp [firstReleaseUp, Nat.not_lt.mpr hk]

/-- The DATA observation is absent at and after the horizon sentinel. -/
theorem firstReleaseData_absent (i : Fin (p.m - 1)) (z : Source p) (k : ℕ)
    (hk : p.T ≤ k) : firstReleaseData rate rewards C_star C_h i k z = false := by
  simp [firstReleaseData, Nat.not_lt.mpr hk]

/-- The combined-release observation is absent at and after the horizon
sentinel. -/
theorem firstReleaseRelease_absent (i : Fin (p.m - 1)) (z : Source p) (k : ℕ)
    (hk : p.T ≤ k) : firstReleaseRelease rate rewards C_star C_h i k z = false := by
  simp [firstReleaseRelease, Nat.not_lt.mpr hk]

private theorem waitingN_ext {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P Q : ℕ → Ω → Finset (Fin d)) (X Y : Fin d → ℕ → Ω → Bool)
    (i : Fin d) (v : ℕ) (z : Ω)
    (hP : ∀ k, P k z = Q k z) (hX : ∀ k, X i k z = Y i k z) :
    PhaseServiceWaiting.N P X i v z = PhaseServiceWaiting.N Q Y i v z := by
  unfold PhaseServiceWaiting.N
  apply Finset.sum_congr rfl
  intro k hk
  rw [hP k, hX k]

private theorem noLaunch_empty (z : Source p)
    (hcross : ¬ (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true) :
    ReferenceFirstLiveSourceStoppedReleaseEndpoint.actualFirstReleaseSupport
        rate rewards C_star C_h z = ∅ ∧
      ∀ t : Fin p.T,
        ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = none := by
  have hnone : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing = none := by
    cases h : (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing with
    | none => rfl
    | some crossing => simp [h] at hcross
  have hlaunch := (ReferenceCorrectedInitializationLaunch.correctedLaunch_eq_none_iff
    rate z rewards C_star C_h).2 hnone
  have hhistory := ReferenceCompletePhysicalHistory.no_launch_complete_history
    rate z rewards C_star C_h hlaunch
  have hrecords : ReferenceFirstLiveSourceStoppedReleaseEndpoint.completeRecords
      rate rewards C_star C_h z = [] := by
    simpa [ReferenceFirstLiveSourceStoppedReleaseEndpoint.completeRecords] using hhistory.2.1
  have hgate : ReferenceFirstLiveSourceStoppedReleaseEndpoint.actualGateSupport
      rate rewards C_star C_h z = ∅ := by
    unfold ReferenceFirstLiveSourceStoppedReleaseEndpoint.actualGateSupport
    rw [hrecords]
    simp [ReferenceLocalReleaseGateChronology.gateSupport]
  constructor
  · simp [ReferenceFirstLiveSourceStoppedReleaseEndpoint.actualFirstReleaseSupport, hgate]
  · intro t
    simp [ReferenceSourcePrefixHistoryFiltration.actualRecord, hhistory.1, hhistory.2.1]

/-- On a genuine crossing-and-launch source, these lifts are exactly W's
endpoint-restricted calendar readouts at `firstExcluded`. The source event is
an explicit conditional input; no quota, trace, safety, law, or endpoint is
assumed. -/
theorem firstReleaseNat_lifts_eq_waiting_on_launch
    (s : ℕ) (hs : s ≤ p.T)
    (z : ReferenceLocalReleaseWaitingPaths.SourceEvent rate rewards C_star C_h s) :
    (∀ k,
      firstReleasePendingNat rate rewards C_star C_h k z.val =
        ReferenceLocalReleaseWaitingPaths.pendingTheta rate rewards C_star C_h s hs s
          (fun w => ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstExcluded
            rate rewards C_star C_h w.val) k z) ∧
    (∀ i k,
      firstReleaseUp rate rewards C_star C_h i k z.val =
        ReferenceLocalReleaseWaitingPaths.upObservation rate rewards C_star C_h s hs s i k z ∧
      firstReleaseData rate rewards C_star C_h i k z.val =
        ReferenceLocalReleaseWaitingPaths.dataObservation rate rewards C_star C_h s hs s i k z ∧
      firstReleaseRelease rate rewards C_star C_h i k z.val =
        ReferenceLocalReleaseWaitingPaths.releaseObservation rate rewards C_star C_h s hs s i k z) := by
  let theta : ReferenceLocalReleaseWaitingPaths.SourceEvent rate rewards C_star C_h s → ℕ :=
    fun w => ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstExcluded
      rate rewards C_star C_h w.val
  have htheta : ∀ w, 1 ≤ theta w ∧ theta w ≤ p.T + 1 := by
    intro w
    exact ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstExcluded_bounds
      rate rewards C_star C_h w.val
  have hstart : ReferenceFirstLiveSourceStoppedReleaseEndpoint.physicalStart
      rate rewards C_star C_h z.val = s := by
    change ReferenceCompletePhysicalHistory.physicalStart rate z.val rewards C_star C_h = s
    simpa [ReferenceCompletePhysicalHistory.physicalStart,
      ReferenceCompletePhysicalHistory.generatedBoundary,
      ReferenceCompletePhysicalHistory.generatedInput] using z.property.2
  let zH : ReferenceSourceReleaseWaitingReadouts.SourceEvent rate rewards C_star C_h s :=
    ⟨z.val, z.property.1, z.property.2⟩
  constructor
  · intro k
    by_cases hkT : p.T ≤ k
    · have hW := ReferenceLocalReleaseWaitingPaths.readouts_absent_at_or_after_horizon
        rate rewards C_star C_h s hs s theta htheta z k hkT
      rw [firstReleasePendingNat_absent rate rewards C_star C_h z.val k hkT]
      simpa [theta] using hW.1.symm
    · have hk : k < p.T := Nat.lt_of_not_ge hkT
      let t : Fin p.T := ⟨k, hk⟩
      by_cases hsk : s ≤ k
      · have hst : s ≤ t.val := by simpa [t] using hsk
        have hactualRecord := ReferenceSourcePrefixHistoryFiltration.actualRecord_source_calendar
          rate rewards C_star C_h t s hst zH
        have hentry := ReferenceSourcePrefixHistoryFiltration.entry_source_calendar
          rate rewards C_star C_h s t s hst zH
        have hentryGate :
            (ReferenceSourcePrefixHistoryFiltration.entry rate rewards C_star C_h s t z.val).map Prod.fst =
              ReferenceLocalReleaseCalendarCounts.calendarGate rate z.val rewards C_star C_h
                z.property.1 s (p.T - s) z.property.2 (by omega) s k := by
          change (ReferenceSourcePrefixHistoryFiltration.entry rate rewards C_star C_h s t zH.val).map
              Prod.fst = _
          calc
            _ = (ReferenceLocalReleaseCalendarCounts.calendarEntry rate z.val rewards C_star C_h
                z.property.1 s (p.T - s) z.property.2 (by omega) s k).map Prod.fst := by
                  rw [hentry]
            _ = _ := by
              simp [ReferenceLocalReleaseCalendarCounts.calendarEntry,
                ReferenceLocalReleaseCalendarCounts.calendarGate, Function.comp_def,
                ReferenceRetainedReleasePhaseObservation.localReleaseEntry]
        have hgate : k + 1 ∈
            ReferenceFirstLiveSourceStoppedReleaseEndpoint.actualGateSupport
                rate rewards C_star C_h z.val ↔
              ReferenceLocalReleaseCalendarCounts.calendarGate rate z.val rewards C_star C_h
                z.property.1 s (p.T - s) z.property.2 (by omega) s k = some true := by
          rw [ReferenceFirstLiveSourceStoppedReleaseEndpoint.actual_gate_support_mem_iff_entry
            rate rewards C_star C_h z.val t]
          rw [hstart, hentryGate]
        by_cases hcut : k + 1 < theta z
        · by_cases hcalendarGate :
            ReferenceLocalReleaseCalendarCounts.calendarGate rate z.val rewards C_star C_h
              z.property.1 s (p.T - s) z.property.2 (by omega) s k = some true
          · have hmemGate := hgate.mpr hcalendarGate
            have hmemStopped : k + 1 ∈
                ReferenceFirstLiveSourceStoppedReleaseEndpoint.actualFirstReleaseSupport
                  rate rewards C_star C_h z.val :=
              Finset.mem_filter.mpr ⟨hmemGate, by simpa [theta] using hcut⟩
            have hquotaReadouts := ReferenceLocalReleaseWaitingPaths.sourceReadouts_at_trueGate
              rate rewards C_star C_h s hs s z k hcalendarGate
            rcases hquotaReadouts with
              ⟨r, M, hlookup, _, _, hentryCalendar, _, _⟩
            obtain ⟨hrun, htime⟩ :=
              (ReferenceLocalReleaseWaitingPaths.calendarRecord_reconstruction
                rate rewards C_star C_h s hs z k r).mp hlookup
            have hlookup' :=
              (ReferenceLocalReleaseWaitingPaths.calendarRecord_reconstruction
                rate rewards C_star C_h s hs z k r).mpr ⟨hrun, htime⟩
            have hactualRecordR :
                ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z.val =
                  some r := by
              change ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t zH.val =
                some r
              rw [hactualRecord]
              exact hlookup'
            have htimeFin : r.input.time = t := by
              apply Fin.ext
              simpa [t] using htime
            have hlocalEntry :
                ReferenceRetainedReleasePhaseObservation.localReleaseEntry rate s t
                  (ReferenceActivePhysicalStepMeasurability.encodeState r.input.state) =
                (true, some (ReferencePhysicalReleaseQuota.pendingSet M r)) := by
              have h := hentryCalendar
              simp only [ReferenceLocalReleaseCalendarCounts.calendarEntry,
                hlookup', Option.map_some] at h
              have h' := Option.some.inj h
              simpa only [htimeFin] using h'
            have hentryActual :
                ReferenceSourcePrefixHistoryFiltration.entry rate rewards C_star C_h s t z.val =
                  some (true, some (ReferencePhysicalReleaseQuota.pendingSet M r)) := by
              simp [ReferenceSourcePrefixHistoryFiltration.entry,
                ReferenceSourcePrefixHistoryFiltration.incoming, hactualRecordR, hlocalEntry]
            have hpendingActual :
                ReferenceSourcePrefixHistoryFiltration.pending rate rewards C_star C_h s t z.val =
                  ReferencePhysicalReleaseQuota.pendingSet M r := by
              simp [ReferenceSourcePrefixHistoryFiltration.pending, hentryActual]
            have hpendingSource := ReferenceSourcePrefixHistoryFiltration.pending_source_calendar
              rate rewards C_star C_h s t s hst zH
            have hcalendarPendingGetD :
                (ReferenceLocalReleaseWaitingPaths.calendarPendingReadout
                  rate rewards C_star C_h s hs s z k).getD ∅ =
                    ReferencePhysicalReleaseQuota.pendingSet M r :=
              hpendingSource.symm.trans hpendingActual
            have hE : ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstReleasePending
                rate rewards C_star C_h z.val t =
                  ReferenceSourcePrefixHistoryFiltration.pending rate rewards C_star C_h s t z.val := by
              have hmemStoppedFin : t.val + 1 ∈
                  ReferenceFirstLiveSourceStoppedReleaseEndpoint.actualFirstReleaseSupport
                    rate rewards C_star C_h z.val := by
                simpa [t] using hmemStopped
              unfold ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstReleasePending
              rw [ite_eq_left hmemStoppedFin, hstart]
            calc
              firstReleasePendingNat rate rewards C_star C_h k z.val =
                  ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstReleasePending
                    rate rewards C_star C_h z.val t := by
                      rw [firstReleasePendingNat_fin rate rewards C_star C_h t z.val]
              _ = ReferenceSourcePrefixHistoryFiltration.pending
                    rate rewards C_star C_h s t z.val := hE
              _ = ReferencePhysicalReleaseQuota.pendingSet M r := hpendingActual
              _ = (ReferenceLocalReleaseWaitingPaths.pendingTheta
                    rate rewards C_star C_h s hs s theta k z) := by
                    rw [ReferenceLocalReleaseWaitingPaths.pendingTheta, ite_eq_left hcut]
                    simpa [theta] using hcalendarPendingGetD.symm
          · have hnotGate : k + 1 ∉
                ReferenceFirstLiveSourceStoppedReleaseEndpoint.actualGateSupport
                  rate rewards C_star C_h z.val := by
              intro hmem
              exact hcalendarGate ((hgate.mp hmem))
            have hnotStopped : k + 1 ∉
                ReferenceFirstLiveSourceStoppedReleaseEndpoint.actualFirstReleaseSupport
                  rate rewards C_star C_h z.val := by
              intro hmem
              exact hnotGate (Finset.mem_filter.mp hmem).1
            have hcalendarPendingNone :
                ReferenceLocalReleaseCalendarCounts.calendarPending rate z.val rewards C_star C_h
                  z.property.1 s (p.T - s) z.property.2 (by omega) s k = none := by
              unfold ReferenceLocalReleaseCalendarCounts.calendarPending
              cases he : ReferenceLocalReleaseCalendarCounts.calendarEntry rate z.val rewards C_star C_h
                  z.property.1 s (p.T - s) z.property.2 (by omega) s k with
              | none => rfl
              | some entry =>
                  rcases entry with ⟨flag, pending⟩
                  cases flag with
                  | false => rfl
                  | true =>
                      cases pending with
                      | none => rfl
                      | some P =>
                          have htrue : ReferenceLocalReleaseCalendarCounts.calendarGate rate z.val
                              rewards C_star C_h z.property.1 s (p.T - s) z.property.2
                              (by omega) s k = some true := by
                            have hentry' :
                                ReferenceSourcePrefixHistoryFiltration.entry rate rewards C_star C_h
                                  s t z.val =
                                  ReferenceLocalReleaseCalendarCounts.calendarEntry rate z.val
                                    rewards C_star C_h z.property.1 s (p.T - s) z.property.2
                                      (by omega) s k := by
                              simpa only [zH] using hentry
                            exact hentryGate.symm.trans (by
                              rw [hentry']
                              simp [he])
                          exact (hcalendarGate htrue).elim
            have hE : ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstReleasePending
                rate rewards C_star C_h z.val t = ∅ := by
              have hnotStoppedFin : t.val + 1 ∉
                  ReferenceFirstLiveSourceStoppedReleaseEndpoint.actualFirstReleaseSupport
                    rate rewards C_star C_h z.val := by
                simpa [t] using hnotStopped
              unfold ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstReleasePending
              rw [ite_eq_right hnotStoppedFin]
            have hNat : firstReleasePendingNat rate rewards C_star C_h k z.val = ∅ := by
              rw [firstReleasePendingNat_fin rate rewards C_star C_h t z.val]
              exact hE
            have hWait : ReferenceLocalReleaseWaitingPaths.pendingTheta
                rate rewards C_star C_h s hs s theta k z = ∅ := by
              simp [ReferenceLocalReleaseWaitingPaths.pendingTheta, hcut, theta,
                ReferenceLocalReleaseWaitingPaths.calendarPendingReadout,
                hcalendarPendingNone]
            exact hNat.trans hWait.symm
        · have hnotStopped : k + 1 ∉
              ReferenceFirstLiveSourceStoppedReleaseEndpoint.actualFirstReleaseSupport
                rate rewards C_star C_h z.val := by
            intro hmem
            exact hcut (by
              have := (Finset.mem_filter.mp hmem).2
              simpa [theta] using this)
          have hE : ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstReleasePending
              rate rewards C_star C_h z.val t = ∅ := by
            have hnotStoppedFin : t.val + 1 ∉
                ReferenceFirstLiveSourceStoppedReleaseEndpoint.actualFirstReleaseSupport
                  rate rewards C_star C_h z.val := by
              simpa [t] using hnotStopped
            unfold ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstReleasePending
            rw [ite_eq_right hnotStoppedFin]
          have hNat : firstReleasePendingNat rate rewards C_star C_h k z.val = ∅ := by
            rw [firstReleasePendingNat_fin rate rewards C_star C_h t z.val]
            exact hE
          have hWait : ReferenceLocalReleaseWaitingPaths.pendingTheta
              rate rewards C_star C_h s hs s theta k z = ∅ := by
            simp [ReferenceLocalReleaseWaitingPaths.pendingTheta, hcut, theta]
          exact hNat.trans hWait.symm
      · have hrecordNone :
            ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z.val = none := by
          have hfuture : t.val <
              ReferenceCompletePhysicalHistory.physicalStart rate z.val rewards C_star C_h := by
            change t.val < ReferenceFirstLiveSourceStoppedReleaseEndpoint.physicalStart
              rate rewards C_star C_h z.val
            have hk' : k < s := Nat.lt_of_not_ge hsk
            rw [hstart]
            simpa [t] using hk'
          exact ReferenceSourcePrefixHistoryFiltration.actualRecord_eq_none_of_future_start
            rate rewards C_star C_h t z.val hfuture
        have hentryNone : ReferenceSourcePrefixHistoryFiltration.entry rate rewards C_star C_h
            (ReferenceFirstLiveSourceStoppedReleaseEndpoint.physicalStart
              rate rewards C_star C_h z.val) t z.val = none := by
          simp [ReferenceSourcePrefixHistoryFiltration.entry,
            ReferenceSourcePrefixHistoryFiltration.incoming, hrecordNone]
        have hnotGate : k + 1 ∉
            ReferenceFirstLiveSourceStoppedReleaseEndpoint.actualGateSupport
              rate rewards C_star C_h z.val := by
          intro hmem
          have hentry :=
            (ReferenceFirstLiveSourceStoppedReleaseEndpoint.actual_gate_support_mem_iff_entry
              rate rewards C_star C_h z.val t).mp hmem
          rw [hentryNone] at hentry
          simp at hentry
        have hnotStopped : k + 1 ∉
            ReferenceFirstLiveSourceStoppedReleaseEndpoint.actualFirstReleaseSupport
              rate rewards C_star C_h z.val := by
          intro hmem
          exact hnotGate (Finset.mem_filter.mp hmem).1
        have hcalendarRecordNone :
            ReferenceLocalReleaseCalendarCounts.calendarRecord rate z.val rewards C_star C_h
              z.property.1 s (p.T - s) z.property.2 (by omega) k = none := by
          simp [ReferenceLocalReleaseCalendarCounts.calendarRecord, hsk]
        have hpendingNone : ReferenceLocalReleaseWaitingPaths.calendarPendingReadout
            rate rewards C_star C_h s hs s z k = none := by
          simp [ReferenceLocalReleaseWaitingPaths.calendarPendingReadout,
            ReferenceLocalReleaseCalendarCounts.calendarPending,
            ReferenceLocalReleaseCalendarCounts.calendarEntry,
            ReferenceLocalReleaseCalendarCounts.calendarRecord, hsk]
        have hNat : firstReleasePendingNat rate rewards C_star C_h k z.val = ∅ := by
          rw [firstReleasePendingNat_fin rate rewards C_star C_h t z.val]
          have hnotStoppedFin : t.val + 1 ∉
              ReferenceFirstLiveSourceStoppedReleaseEndpoint.actualFirstReleaseSupport
                rate rewards C_star C_h z.val := by
            simpa [t] using hnotStopped
          unfold ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstReleasePending
          rw [ite_eq_right hnotStoppedFin]
        have hWait : ReferenceLocalReleaseWaitingPaths.pendingTheta
            rate rewards C_star C_h s hs s theta k z = ∅ := by
          simp [ReferenceLocalReleaseWaitingPaths.pendingTheta, theta, hpendingNone]
        exact hNat.trans hWait.symm
  · intro i k
    by_cases hkT : p.T ≤ k
    · have hW := ReferenceLocalReleaseWaitingPaths.readouts_absent_at_or_after_horizon
        rate rewards C_star C_h s hs s theta htheta z k hkT
      have hW' := hW.2 i
      rw [firstReleaseUp_absent rate rewards C_star C_h i z.val k hkT,
        firstReleaseData_absent rate rewards C_star C_h i z.val k hkT,
        firstReleaseRelease_absent rate rewards C_star C_h i z.val k hkT]
      exact ⟨by simpa [theta] using hW'.1.symm,
        by simpa [theta] using hW'.2.1.symm,
        by simpa [theta] using hW'.2.2.symm⟩
    · have hk : k < p.T := Nat.lt_of_not_ge hkT
      let t : Fin p.T := ⟨k, hk⟩
      by_cases hsk : s ≤ k
      · have hst : s ≤ t.val := by simpa [t] using hsk
        have hflags := ReferenceSourcePrefixHistoryFiltration.flags_source_calendar
          rate rewards C_star C_h s i t s hst zH
        rw [firstReleaseUp_fin rate rewards C_star C_h i t z.val,
          firstReleaseData_fin rate rewards C_star C_h i t z.val,
          firstReleaseRelease_fin rate rewards C_star C_h i t z.val]
        simpa only [zH] using hflags
      · have hrecordNone :
            ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z.val = none := by
          have hfuture : t.val <
              ReferenceCompletePhysicalHistory.physicalStart rate z.val rewards C_star C_h := by
            change t.val < ReferenceFirstLiveSourceStoppedReleaseEndpoint.physicalStart
              rate rewards C_star C_h z.val
            have hk' : k < s := Nat.lt_of_not_ge hsk
            rw [hstart]
            simpa [t] using hk'
          exact ReferenceSourcePrefixHistoryFiltration.actualRecord_eq_none_of_future_start
            rate rewards C_star C_h t z.val hfuture
        have hcalendarRecordNone :
            ReferenceLocalReleaseCalendarCounts.calendarRecord rate z.val rewards C_star C_h
              z.property.1 s (p.T - s) z.property.2 (by omega) k = none := by
          simp [ReferenceLocalReleaseCalendarCounts.calendarRecord, hsk]
        rw [firstReleaseUp_fin rate rewards C_star C_h i t z.val,
          firstReleaseData_fin rate rewards C_star C_h i t z.val,
          firstReleaseRelease_fin rate rewards C_star C_h i t z.val]
        have hupW : ReferenceLocalReleaseWaitingPaths.upObservation
            rate rewards C_star C_h s hs s i k z = false := by
          simp [ReferenceLocalReleaseWaitingPaths.upObservation,
            ReferenceLocalReleaseWaitingPaths.calendarUpReadout,
            ReferenceLocalReleaseCalendarCounts.calendarUpFlag,
            ReferenceLocalReleaseCalendarCounts.calendarFlag, hcalendarRecordNone]
        have hdataW : ReferenceLocalReleaseWaitingPaths.dataObservation
            rate rewards C_star C_h s hs s i k z = false := by
          simp [ReferenceLocalReleaseWaitingPaths.dataObservation,
            ReferenceLocalReleaseWaitingPaths.calendarDataReadout,
            ReferenceLocalReleaseCalendarCounts.calendarDataFlag,
            ReferenceLocalReleaseCalendarCounts.calendarFlag, hcalendarRecordNone]
        have hreleaseW : ReferenceLocalReleaseWaitingPaths.releaseObservation
            rate rewards C_star C_h s hs s i k z = false := by
          simp [ReferenceLocalReleaseWaitingPaths.releaseObservation,
            ReferenceLocalReleaseWaitingPaths.calendarReleaseReadout,
            ReferenceLocalReleaseCalendarCounts.calendarReleaseFlag,
            ReferenceLocalReleaseCalendarCounts.calendarFlag, hcalendarRecordNone]
        have hflagsLocal :
            ReferenceSourcePrefixHistoryFiltration.actualUp rate rewards C_star C_h i t z.val = false ∧
            ReferenceSourcePrefixHistoryFiltration.actualData rate rewards C_star C_h i t z.val = false ∧
            ReferenceSourcePrefixHistoryFiltration.actualRelease rate rewards C_star C_h i t z.val = false := by
          simp [ReferenceSourcePrefixHistoryFiltration.actualUp,
            ReferenceSourcePrefixHistoryFiltration.actualData,
            ReferenceSourcePrefixHistoryFiltration.actualRelease, hrecordNone]
        exact ⟨hflagsLocal.1.trans hupW.symm,
          hflagsLocal.2.1.trans hdataW.symm,
          hflagsLocal.2.2.trans hreleaseW.symm⟩

/-- On an actual launch the stopped endpoint pair is the pair computed from
W's very same full-run gate support and the literal endpoint `firstExcluded`. -/
theorem firstRelease_endpoints_eq_waiting_on_launch
    (s : ℕ) (hs : s ≤ p.T)
    (z : ReferenceLocalReleaseWaitingPaths.SourceEvent rate rewards C_star C_h s) :
    ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstReleaseSigma rate rewards C_star C_h z.val =
        ReferenceLocalReleaseWaitingPaths.localPhaseSigma rate rewards C_star C_h s hs s
          (fun w => ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstExcluded
            rate rewards C_star C_h w.val) z ∧
      ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstReleaseTheta rate rewards C_star C_h z.val =
        ReferenceLocalReleaseWaitingPaths.localPhaseEndpoint rate rewards C_star C_h s hs s
          (fun w => ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstExcluded
            rate rewards C_star C_h w.val) z := by
  have hstart : ReferenceFirstLiveSourceStoppedReleaseEndpoint.physicalStart
      rate rewards C_star C_h z.val = s := by
    change ReferenceCompletePhysicalHistory.physicalStart rate z.val rewards C_star C_h = s
    simpa [ReferenceCompletePhysicalHistory.physicalStart,
      ReferenceCompletePhysicalHistory.generatedBoundary,
      ReferenceCompletePhysicalHistory.generatedInput] using z.property.2
  have hstartH : ReferenceCompletePhysicalHistory.physicalStart
      rate z.val rewards C_star C_h = s := by
    change ReferenceFirstLiveSourceStoppedReleaseEndpoint.physicalStart
      rate rewards C_star C_h z.val = s
    exact hstart
  let active := ReferenceLocalReleaseGateChronology.sourceSeed
    rate z.val rewards C_star C_h z.property.1
  have hlaunch := ReferenceLocalReleaseGateChronology.sourceSeed_launch
    rate z.val rewards C_star C_h z.property.1
  have hrecords :
      (ReferenceLocalReleaseWaitingPaths.sourceRunAtLaunch rate rewards C_star C_h s hs z).records =
        ReferenceFirstLiveSourceStoppedReleaseEndpoint.completeRecords rate rewards C_star C_h z.val := by
    have hfull := ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
      rate z.val rewards C_star C_h active hlaunch
    simpa [active, ReferenceLocalReleaseWaitingPaths.sourceRunAtLaunch,
      ReferenceLocalReleaseGateChronology.sourceRun,
      ReferenceFirstLiveSourceStoppedReleaseEndpoint.completeRecords, hstartH] using hfull.symm
  have halpha : ReferenceFirstLiveSourceStoppedReleaseEndpoint.actualGateAlpha
      rate rewards C_star C_h z.val =
        ReferenceLocalReleaseWaitingPaths.localGateAlpha rate rewards C_star C_h s hs s z := by
    unfold ReferenceFirstLiveSourceStoppedReleaseEndpoint.actualGateAlpha
      ReferenceLocalReleaseWaitingPaths.localGateAlpha
    rw [hstart, hrecords]
  have hbeta : ReferenceFirstLiveSourceStoppedReleaseEndpoint.actualGateBeta
      rate rewards C_star C_h z.val =
        ReferenceLocalReleaseWaitingPaths.localGateBeta rate rewards C_star C_h s hs s z := by
    unfold ReferenceFirstLiveSourceStoppedReleaseEndpoint.actualGateBeta
      ReferenceLocalReleaseWaitingPaths.localGateBeta
    rw [hstart, hrecords]
  constructor
  · simp [ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstReleaseSigma,
      ReferenceLocalReleaseWaitingPaths.localPhaseSigma, halpha, hbeta]
  · simp [ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstReleaseTheta,
      ReferenceLocalReleaseWaitingPaths.localPhaseEndpoint, halpha, hbeta]

/-- E's stopped gate support is exactly W's one-based calendar gate support
restricted before the same first excluded round. The gate support remains
separate from pending-set nonemptiness. -/
theorem actual_first_release_support_eq_waiting_interval
    (s : ℕ) (hs : s ≤ p.T)
    (z : ReferenceLocalReleaseWaitingPaths.SourceEvent rate rewards C_star C_h s) :
    ReferenceFirstLiveSourceStoppedReleaseEndpoint.actualFirstReleaseSupport
        rate rewards C_star C_h z.val =
      Finset.image (fun k : ℕ => k + 1)
        ((ReferenceLocalReleaseCalendarCounts.calendarGateSupport rate z.val rewards C_star C_h
          z.property.1 s (p.T - s) z.property.2 (by omega) s).filter
          (fun k => k + 1 <
            ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstExcluded
              rate rewards C_star C_h z.val)) := by
  let theta : ReferenceLocalReleaseWaitingPaths.SourceEvent rate rewards C_star C_h s → ℕ :=
    fun w => ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstExcluded
      rate rewards C_star C_h w.val
  have htheta : ∀ w, 1 ≤ theta w ∧ theta w ≤ p.T + 1 := by
    intro w
    exact ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstExcluded_bounds
      rate rewards C_star C_h w.val
  have hE := ReferenceFirstLiveSourceStoppedReleaseEndpoint.actual_first_release_interval
    rate rewards C_star C_h z.val
  have hW := ReferenceLocalReleaseWaitingPaths.local_gate_interval_restrict
    rate rewards C_star C_h s hs s theta htheta z
  have hend := firstRelease_endpoints_eq_waiting_on_launch rate rewards C_star C_h s hs z
  calc
    ReferenceFirstLiveSourceStoppedReleaseEndpoint.actualFirstReleaseSupport
        rate rewards C_star C_h z.val =
      Finset.Ico
        (ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstReleaseSigma rate rewards C_star C_h z.val)
        (ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstReleaseTheta rate rewards C_star C_h z.val) := hE.1
    _ = Finset.Ico
        (ReferenceLocalReleaseWaitingPaths.localPhaseSigma rate rewards C_star C_h s hs s theta z)
        (ReferenceLocalReleaseWaitingPaths.localPhaseEndpoint rate rewards C_star C_h s hs s theta z) := by
          rw [hend.1, hend.2]
    _ = Finset.image (fun k : ℕ => k + 1)
        ((ReferenceLocalReleaseCalendarCounts.calendarGateSupport rate z.val rewards C_star C_h
          z.property.1 s (p.T - s) z.property.2 (by omega) s).filter
          (fun k => k + 1 < theta z)) := hW.1.symm
    _ = _ := by simp [theta]

/-- The complete original stopped-support interval is empty outside E's
`[sigma,theta)` interval. -/
theorem firstReleasePendingNat_empty_outside_interval (z : Source p) (k : ℕ)
    (hout : ¬
      (ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstReleaseSigma rate rewards C_star C_h z ≤ k + 1 ∧
       k + 1 < ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstReleaseTheta rate rewards C_star C_h z)) :
    firstReleasePendingNat rate rewards C_star C_h k z = ∅ := by
  by_cases hk : p.T ≤ k
  · exact firstReleasePendingNat_absent rate rewards C_star C_h z k hk
  · have hk' : k < p.T := Nat.lt_of_not_ge hk
    let t : Fin p.T := ⟨k, hk'⟩
    have hnot : k + 1 ∉ ReferenceFirstLiveSourceStoppedReleaseEndpoint.actualFirstReleaseSupport
        rate rewards C_star C_h z := by
      intro hmem
      have hinterval :=
        (ReferenceFirstLiveSourceStoppedReleaseEndpoint.actual_first_release_interval
          rate rewards C_star C_h z).1
      have hmemIco : k + 1 ∈ Finset.Ico
          (ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstReleaseSigma rate rewards C_star C_h z)
          (ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstReleaseTheta rate rewards C_star C_h z) :=
        hinterval ▸ hmem
      exact hout (Finset.mem_Ico.mp hmemIco)
    have hnotT : t.val + 1 ∉
        ReferenceFirstLiveSourceStoppedReleaseEndpoint.actualFirstReleaseSupport
          rate rewards C_star C_h z := by
      simpa [t] using hnot
    rw [firstReleasePendingNat_fin rate rewards C_star C_h t z]
    simp [ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstReleasePending, hnotT]

/-- Pending sets are nested through the actual stopped calendar interval, in
the original chronological direction. -/
theorem firstReleasePendingNat_nested_inside_interval
    (z : Source p) (k l : ℕ) (hkl : k ≤ l)
    (hstart : ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstReleaseSigma
      rate rewards C_star C_h z ≤ k + 1)
    (hexit : l + 1 < ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstReleaseTheta
      rate rewards C_star C_h z) :
    firstReleasePendingNat rate rewards C_star C_h l z ⊆
      firstReleasePendingNat rate rewards C_star C_h k z := by
  by_cases hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true
  · let s := ReferenceFirstLiveSourceStoppedReleaseEndpoint.physicalStart rate rewards C_star C_h z
    have hs : s ≤ p.T := by
      simpa [s, ReferenceFirstLiveSourceStoppedReleaseEndpoint.physicalStart] using
        ReferenceCompletePhysicalHistory.physicalStart_le_T rate z rewards C_star C_h
    have hElapsed : ReferenceInitializationRun.elapsed p
        (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed = s := by
      simp [s, ReferenceFirstLiveSourceStoppedReleaseEndpoint.physicalStart,
        ReferenceCompletePhysicalHistory.physicalStart,
        ReferenceCompletePhysicalHistory.generatedBoundary,
        ReferenceCompletePhysicalHistory.generatedInput]
    let w : ReferenceLocalReleaseWaitingPaths.SourceEvent rate rewards C_star C_h s :=
      ⟨z, hcross, hElapsed⟩
    let theta : ReferenceLocalReleaseWaitingPaths.SourceEvent rate rewards C_star C_h s → ℕ :=
      fun w' => ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstExcluded
        rate rewards C_star C_h w'.val
    have htheta : ∀ w', 1 ≤ theta w' ∧ theta w' ≤ p.T + 1 := by
      intro w'
      exact ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstExcluded_bounds
        rate rewards C_star C_h w'.val
    have hend := firstRelease_endpoints_eq_waiting_on_launch rate rewards C_star C_h s hs w
    have hkT : l < p.T := by
      have hthetaUpper :=
        (ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstExcluded_bounds
          rate rewards C_star C_h z).2
      have hintervalTheta :
          ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstReleaseTheta rate rewards C_star C_h z ≤ p.T + 1 := by
        have := (ReferenceFirstLiveSourceStoppedReleaseEndpoint.actual_first_release_interval
          rate rewards C_star C_h z).2.2.2
        exact this
      omega
    have hstart' : ReferenceLocalReleaseWaitingPaths.localPhaseSigma
        rate rewards C_star C_h s hs s theta w ≤ k + 1 := by
      rw [← hend.1]
      exact hstart
    have hexit' : l + 1 < ReferenceLocalReleaseWaitingPaths.localPhaseEndpoint
        rate rewards C_star C_h s hs s theta w := by
      rw [← hend.2]
      exact hexit
    have hnest := ReferenceLocalReleaseWaitingPaths.pendingTheta_nested_inside_interval
      rate rewards C_star C_h s hs s theta htheta w k l hkl hkT hstart' hexit'
    have hPendingK := (firstReleaseNat_lifts_eq_waiting_on_launch
      rate rewards C_star C_h s hs w).1 k
    have hPendingL := (firstReleaseNat_lifts_eq_waiting_on_launch
      rate rewards C_star C_h s hs w).1 l
    calc
      firstReleasePendingNat rate rewards C_star C_h l z =
          ReferenceLocalReleaseWaitingPaths.pendingTheta rate rewards C_star C_h s hs s theta l w := by
            simpa [w] using hPendingL
      _ ⊆ ReferenceLocalReleaseWaitingPaths.pendingTheta rate rewards C_star C_h s hs s theta k w := hnest
      _ = firstReleasePendingNat rate rewards C_star C_h k z := by
            simpa [w] using hPendingK.symm
  · have hempty := noLaunch_empty rate rewards C_star C_h z hcross
    have hendpoints := ReferenceFirstLiveSourceStoppedReleaseEndpoint.empty_first_release_endpoints
      rate rewards C_star C_h z hempty.1
    omega

/-- Every original source has at most one actual UP service observation for
each follower, at every natural horizon. -/
theorem actual_first_release_all_N_le_one (z : Source p) (i : Fin (p.m - 1)) (v : ℕ) :
    PhaseServiceWaiting.N (firstReleasePendingNat rate rewards C_star C_h)
        (firstReleaseUp rate rewards C_star C_h) i v z ≤ 1 ∧
      PhaseServiceWaiting.N (firstReleasePendingNat rate rewards C_star C_h)
        (firstReleaseData rate rewards C_star C_h) i v z ≤ 1 ∧
      PhaseServiceWaiting.N (firstReleasePendingNat rate rewards C_star C_h)
        (firstReleaseRelease rate rewards C_star C_h) i v z ≤ 1 := by
  by_cases hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true
  · let s := ReferenceFirstLiveSourceStoppedReleaseEndpoint.physicalStart rate rewards C_star C_h z
    have hs : s ≤ p.T := by
      simpa [s, ReferenceFirstLiveSourceStoppedReleaseEndpoint.physicalStart] using
        ReferenceCompletePhysicalHistory.physicalStart_le_T rate z rewards C_star C_h
    have hElapsed : ReferenceInitializationRun.elapsed p
        (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed = s := by
      simp [s, ReferenceFirstLiveSourceStoppedReleaseEndpoint.physicalStart,
        ReferenceCompletePhysicalHistory.physicalStart,
        ReferenceCompletePhysicalHistory.generatedBoundary,
        ReferenceCompletePhysicalHistory.generatedInput]
    let w : ReferenceLocalReleaseWaitingPaths.SourceEvent rate rewards C_star C_h s :=
      ⟨z, hcross, hElapsed⟩
    let EP : ℕ → ReferenceLocalReleaseWaitingPaths.SourceEvent rate rewards C_star C_h s →
        Finset (Fin (p.m - 1)) := fun k w' =>
          firstReleasePendingNat rate rewards C_star C_h k w'.val
    let EU : Fin (p.m - 1) → ℕ →
        ReferenceLocalReleaseWaitingPaths.SourceEvent rate rewards C_star C_h s → Bool :=
          fun j k w' => firstReleaseUp rate rewards C_star C_h j k w'.val
    let ED : Fin (p.m - 1) → ℕ →
        ReferenceLocalReleaseWaitingPaths.SourceEvent rate rewards C_star C_h s → Bool :=
          fun j k w' => firstReleaseData rate rewards C_star C_h j k w'.val
    let ER : Fin (p.m - 1) → ℕ →
        ReferenceLocalReleaseWaitingPaths.SourceEvent rate rewards C_star C_h s → Bool :=
          fun j k w' => firstReleaseRelease rate rewards C_star C_h j k w'.val
    let theta : ReferenceLocalReleaseWaitingPaths.SourceEvent rate rewards C_star C_h s → ℕ :=
      fun w' => ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstExcluded
        rate rewards C_star C_h w'.val
    have htheta : ∀ w', 1 ≤ theta w' ∧ theta w' ≤ p.T + 1 := by
      intro w'
      exact ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstExcluded_bounds
        rate rewards C_star C_h w'.val
    have hlifts := firstReleaseNat_lifts_eq_waiting_on_launch rate rewards C_star C_h s hs w
    have hP : ∀ k, EP k w =
        ReferenceLocalReleaseWaitingPaths.pendingTheta rate rewards C_star C_h s hs s theta k w := by
      intro k
      simpa [EP, theta] using hlifts.1 k
    have hU : ∀ k, EU i k w =
        ReferenceLocalReleaseWaitingPaths.upObservation rate rewards C_star C_h s hs s i k w := by
      intro k
      simpa [EU, theta] using (hlifts.2 i k).1
    have hD : ∀ k, ED i k w =
        ReferenceLocalReleaseWaitingPaths.dataObservation rate rewards C_star C_h s hs s i k w := by
      intro k
      simpa [ED, theta] using (hlifts.2 i k).2.1
    have hR : ∀ k, ER i k w =
        ReferenceLocalReleaseWaitingPaths.releaseObservation rate rewards C_star C_h s hs s i k w := by
      intro k
      simpa [ER, theta] using (hlifts.2 i k).2.2
    have hNup : PhaseServiceWaiting.N (firstReleasePendingNat rate rewards C_star C_h)
        (firstReleaseUp rate rewards C_star C_h) i v z =
        PhaseServiceWaiting.N (ReferenceLocalReleaseWaitingPaths.pendingTheta rate rewards C_star C_h s hs s theta)
          (ReferenceLocalReleaseWaitingPaths.upObservation rate rewards C_star C_h s hs s) i v w := by
      calc
        _ = PhaseServiceWaiting.N EP EU i v w := by rfl
        _ = _ := waitingN_ext EP
          (ReferenceLocalReleaseWaitingPaths.pendingTheta rate rewards C_star C_h s hs s theta)
          EU (ReferenceLocalReleaseWaitingPaths.upObservation rate rewards C_star C_h s hs s)
          i v w hP hU
    have hNdata : PhaseServiceWaiting.N (firstReleasePendingNat rate rewards C_star C_h)
        (firstReleaseData rate rewards C_star C_h) i v z =
        PhaseServiceWaiting.N (ReferenceLocalReleaseWaitingPaths.pendingTheta rate rewards C_star C_h s hs s theta)
          (ReferenceLocalReleaseWaitingPaths.dataObservation rate rewards C_star C_h s hs s) i v w := by
      calc
        _ = PhaseServiceWaiting.N EP ED i v w := by rfl
        _ = _ := waitingN_ext EP
          (ReferenceLocalReleaseWaitingPaths.pendingTheta rate rewards C_star C_h s hs s theta)
          ED (ReferenceLocalReleaseWaitingPaths.dataObservation rate rewards C_star C_h s hs s)
          i v w hP hD
    have hNrelease : PhaseServiceWaiting.N (firstReleasePendingNat rate rewards C_star C_h)
        (firstReleaseRelease rate rewards C_star C_h) i v z =
        PhaseServiceWaiting.N (ReferenceLocalReleaseWaitingPaths.pendingTheta rate rewards C_star C_h s hs s theta)
          (ReferenceLocalReleaseWaitingPaths.releaseObservation rate rewards C_star C_h s hs s) i v w := by
      calc
        _ = PhaseServiceWaiting.N EP ER i v w := by rfl
        _ = _ := waitingN_ext EP
          (ReferenceLocalReleaseWaitingPaths.pendingTheta rate rewards C_star C_h s hs s theta)
          ER (ReferenceLocalReleaseWaitingPaths.releaseObservation rate rewards C_star C_h s hs s)
          i v w hP hR
    obtain ⟨hup, hdata, hrelease⟩ :=
      ReferenceLocalReleaseWaitingPaths.all_waiting_N_le_one
        rate rewards C_star C_h s hs s theta htheta w v i
    exact ⟨by rw [hNup]; exact hup,
      by rw [hNdata]; exact hdata,
      by rw [hNrelease]; exact hrelease⟩
  · have hempty := noLaunch_empty rate rewards C_star C_h z hcross
    have hP : ∀ k, firstReleasePendingNat rate rewards C_star C_h k z = ∅ := by
      intro k
      by_cases hk : k < p.T
      · let t : Fin p.T := ⟨k, hk⟩
        rw [firstReleasePendingNat_fin rate rewards C_star C_h t z]
        simp [ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstReleasePending, hempty.1]
      · exact firstReleasePendingNat_absent rate rewards C_star C_h z k (Nat.le_of_not_gt hk)
    have hU : ∀ k, firstReleaseUp rate rewards C_star C_h i k z = false := by
      intro k
      by_cases hk : k < p.T
      · let t : Fin p.T := ⟨k, hk⟩
        rw [firstReleaseUp_fin rate rewards C_star C_h i t z]
        simp [ReferenceSourcePrefixHistoryFiltration.actualUp, hempty.2 t]
      · exact firstReleaseUp_absent rate rewards C_star C_h i z k (Nat.le_of_not_gt hk)
    have hD : ∀ k, firstReleaseData rate rewards C_star C_h i k z = false := by
      intro k
      by_cases hk : k < p.T
      · let t : Fin p.T := ⟨k, hk⟩
        rw [firstReleaseData_fin rate rewards C_star C_h i t z]
        simp [ReferenceSourcePrefixHistoryFiltration.actualData, hempty.2 t]
      · exact firstReleaseData_absent rate rewards C_star C_h i z k (Nat.le_of_not_gt hk)
    have hR : ∀ k, firstReleaseRelease rate rewards C_star C_h i k z = false := by
      intro k
      by_cases hk : k < p.T
      · let t : Fin p.T := ⟨k, hk⟩
        rw [firstReleaseRelease_fin rate rewards C_star C_h i t z]
        simp [ReferenceSourcePrefixHistoryFiltration.actualRelease, hempty.2 t]
      · exact firstReleaseRelease_absent rate rewards C_star C_h i z k (Nat.le_of_not_gt hk)
    simp [PhaseServiceWaiting.N, hP, hU, hD, hR]

/-- UP release quota for every original source and every natural horizon. -/
theorem actual_first_release_up_N_le_one (z : Source p) (i : Fin (p.m - 1)) (v : ℕ) :
    PhaseServiceWaiting.N (firstReleasePendingNat rate rewards C_star C_h)
      (firstReleaseUp rate rewards C_star C_h) i v z ≤ 1 :=
  (actual_first_release_all_N_le_one rate rewards C_star C_h z i v).1

/-- DATA release quota for every original source and every natural horizon. -/
theorem actual_first_release_data_N_le_one (z : Source p) (i : Fin (p.m - 1)) (v : ℕ) :
    PhaseServiceWaiting.N (firstReleasePendingNat rate rewards C_star C_h)
      (firstReleaseData rate rewards C_star C_h) i v z ≤ 1 :=
  (actual_first_release_all_N_le_one rate rewards C_star C_h z i v).2.1

/-- Combined-release quota for every original source and every natural
horizon. -/
theorem actual_first_release_release_N_le_one (z : Source p) (i : Fin (p.m - 1)) (v : ℕ) :
    PhaseServiceWaiting.N (firstReleasePendingNat rate rewards C_star C_h)
      (firstReleaseRelease rate rewards C_star C_h) i v z ≤ 1 :=
  (actual_first_release_all_N_le_one rate rewards C_star C_h z i v).2.2

/-- A task pending at source offset `k` has no strictly earlier UP, DATA, or
combined-release count through horizon `k`; the current offset is excluded. -/
theorem actual_first_release_strict_prior_zero_at_pending
    (z : Source p) (k : ℕ) (i : Fin (p.m - 1))
    (hi : i ∈ firstReleasePendingNat rate rewards C_star C_h k z) :
    PhaseServiceWaiting.N (firstReleasePendingNat rate rewards C_star C_h)
        (firstReleaseUp rate rewards C_star C_h) i k z = 0 ∧
      PhaseServiceWaiting.N (firstReleasePendingNat rate rewards C_star C_h)
        (firstReleaseData rate rewards C_star C_h) i k z = 0 ∧
      PhaseServiceWaiting.N (firstReleasePendingNat rate rewards C_star C_h)
        (firstReleaseRelease rate rewards C_star C_h) i k z = 0 := by
  by_cases hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true
  · let s := ReferenceFirstLiveSourceStoppedReleaseEndpoint.physicalStart rate rewards C_star C_h z
    have hs : s ≤ p.T := by
      simpa [s, ReferenceFirstLiveSourceStoppedReleaseEndpoint.physicalStart] using
        ReferenceCompletePhysicalHistory.physicalStart_le_T rate z rewards C_star C_h
    have hElapsed : ReferenceInitializationRun.elapsed p
        (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed = s := by
      simp [s, ReferenceFirstLiveSourceStoppedReleaseEndpoint.physicalStart,
        ReferenceCompletePhysicalHistory.physicalStart,
        ReferenceCompletePhysicalHistory.generatedBoundary,
        ReferenceCompletePhysicalHistory.generatedInput]
    let w : ReferenceLocalReleaseWaitingPaths.SourceEvent rate rewards C_star C_h s :=
      ⟨z, hcross, hElapsed⟩
    let EP : ℕ → ReferenceLocalReleaseWaitingPaths.SourceEvent rate rewards C_star C_h s →
        Finset (Fin (p.m - 1)) := fun j w' =>
          firstReleasePendingNat rate rewards C_star C_h j w'.val
    let EU : Fin (p.m - 1) → ℕ →
        ReferenceLocalReleaseWaitingPaths.SourceEvent rate rewards C_star C_h s → Bool :=
          fun j n w' => firstReleaseUp rate rewards C_star C_h j n w'.val
    let ED : Fin (p.m - 1) → ℕ →
        ReferenceLocalReleaseWaitingPaths.SourceEvent rate rewards C_star C_h s → Bool :=
          fun j n w' => firstReleaseData rate rewards C_star C_h j n w'.val
    let ER : Fin (p.m - 1) → ℕ →
        ReferenceLocalReleaseWaitingPaths.SourceEvent rate rewards C_star C_h s → Bool :=
          fun j n w' => firstReleaseRelease rate rewards C_star C_h j n w'.val
    let theta : ReferenceLocalReleaseWaitingPaths.SourceEvent rate rewards C_star C_h s → ℕ :=
      fun w' => ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstExcluded
        rate rewards C_star C_h w'.val
    have htheta : ∀ w', 1 ≤ theta w' ∧ theta w' ≤ p.T + 1 := by
      intro w'
      exact ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstExcluded_bounds
        rate rewards C_star C_h w'.val
    have hlifts := firstReleaseNat_lifts_eq_waiting_on_launch rate rewards C_star C_h s hs w
    have hP : ∀ n, EP n w =
        ReferenceLocalReleaseWaitingPaths.pendingTheta rate rewards C_star C_h s hs s theta n w := by
      intro n
      simpa [EP, theta] using hlifts.1 n
    have hU : ∀ n, EU i n w =
        ReferenceLocalReleaseWaitingPaths.upObservation rate rewards C_star C_h s hs s i n w := by
      intro n
      simpa [EU, theta] using (hlifts.2 i n).1
    have hD : ∀ n, ED i n w =
        ReferenceLocalReleaseWaitingPaths.dataObservation rate rewards C_star C_h s hs s i n w := by
      intro n
      simpa [ED, theta] using (hlifts.2 i n).2.1
    have hR : ∀ n, ER i n w =
        ReferenceLocalReleaseWaitingPaths.releaseObservation rate rewards C_star C_h s hs s i n w := by
      intro n
      simpa [ER, theta] using (hlifts.2 i n).2.2
    have hiW : i ∈ ReferenceLocalReleaseWaitingPaths.pendingTheta
        rate rewards C_star C_h s hs s theta k w := by
      have hi' : i ∈ EP k w := by simpa [EP, w] using hi
      rw [hP k] at hi'
      exact hi'
    obtain ⟨hrelease, hup, hdata, _, _, _⟩ :=
      ReferenceLocalReleaseWaitingPaths.strict_prior_N_zero_at_pending
        rate rewards C_star C_h s hs s theta htheta w k i hiW
    have hNup : PhaseServiceWaiting.N (firstReleasePendingNat rate rewards C_star C_h)
        (firstReleaseUp rate rewards C_star C_h) i k z =
        PhaseServiceWaiting.N
          (ReferenceLocalReleaseWaitingPaths.pendingTheta rate rewards C_star C_h s hs s theta)
          (ReferenceLocalReleaseWaitingPaths.upObservation rate rewards C_star C_h s hs s) i k w := by
      calc
        _ = PhaseServiceWaiting.N EP EU i k w := by rfl
        _ = _ := waitingN_ext EP
          (ReferenceLocalReleaseWaitingPaths.pendingTheta rate rewards C_star C_h s hs s theta)
          EU (ReferenceLocalReleaseWaitingPaths.upObservation rate rewards C_star C_h s hs s)
          i k w hP hU
    have hNdata : PhaseServiceWaiting.N (firstReleasePendingNat rate rewards C_star C_h)
        (firstReleaseData rate rewards C_star C_h) i k z =
        PhaseServiceWaiting.N
          (ReferenceLocalReleaseWaitingPaths.pendingTheta rate rewards C_star C_h s hs s theta)
          (ReferenceLocalReleaseWaitingPaths.dataObservation rate rewards C_star C_h s hs s) i k w := by
      calc
        _ = PhaseServiceWaiting.N EP ED i k w := by rfl
        _ = _ := waitingN_ext EP
          (ReferenceLocalReleaseWaitingPaths.pendingTheta rate rewards C_star C_h s hs s theta)
          ED (ReferenceLocalReleaseWaitingPaths.dataObservation rate rewards C_star C_h s hs s)
          i k w hP hD
    have hNrelease : PhaseServiceWaiting.N (firstReleasePendingNat rate rewards C_star C_h)
        (firstReleaseRelease rate rewards C_star C_h) i k z =
        PhaseServiceWaiting.N
          (ReferenceLocalReleaseWaitingPaths.pendingTheta rate rewards C_star C_h s hs s theta)
          (ReferenceLocalReleaseWaitingPaths.releaseObservation rate rewards C_star C_h s hs s) i k w := by
      calc
        _ = PhaseServiceWaiting.N EP ER i k w := by rfl
        _ = _ := waitingN_ext EP
          (ReferenceLocalReleaseWaitingPaths.pendingTheta rate rewards C_star C_h s hs s theta)
          ER (ReferenceLocalReleaseWaitingPaths.releaseObservation rate rewards C_star C_h s hs s)
          i k w hP hR
    exact ⟨hNup.trans hup, hNdata.trans hdata, hNrelease.trans hrelease⟩
  · have hempty := noLaunch_empty rate rewards C_star C_h z hcross
    have hP : firstReleasePendingNat rate rewards C_star C_h k z = ∅ := by
      by_cases hk : k < p.T
      · let t : Fin p.T := ⟨k, hk⟩
        rw [firstReleasePendingNat_fin rate rewards C_star C_h t z]
        simp [ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstReleasePending, hempty.1]
      · exact firstReleasePendingNat_absent rate rewards C_star C_h z k (Nat.le_of_not_gt hk)
    rw [hP] at hi
    simp at hi

/-- The finite first horizon has no observations, by the literal empty sum
initialization `N 0 = 0`. -/
theorem actual_first_release_N_zero_horizon (z : Source p) (i : Fin (p.m - 1)) :
    PhaseServiceWaiting.N (firstReleasePendingNat rate rewards C_star C_h)
        (firstReleaseUp rate rewards C_star C_h) i 0 z = 0 ∧
      PhaseServiceWaiting.N (firstReleasePendingNat rate rewards C_star C_h)
        (firstReleaseData rate rewards C_star C_h) i 0 z = 0 ∧
      PhaseServiceWaiting.N (firstReleasePendingNat rate rewards C_star C_h)
        (firstReleaseRelease rate rewards C_star C_h) i 0 z = 0 := by
  simp [PhaseServiceWaiting.N]

end Bandits.Support.ReferenceFirstLiveSourceStoppedReleaseQuota

end noncomputable section
