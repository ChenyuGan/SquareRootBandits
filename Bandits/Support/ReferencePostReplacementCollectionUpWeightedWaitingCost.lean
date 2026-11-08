/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferencePostReplacementCollectionUpServiceLaw
public import Bandits.Support.ReferencePostReplacementCollectionSentinelSectionLaw

import Mathlib.Tactic

/-!
# Conditional waiting cost for stopped post-rawK UP releases

The charge uses the actual stopped pending set and the actual whole-weight
auxiliary-arm mass on the original source-input space.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.ContinuousLearningRows
open Bandits.Support.PhaseServiceWaiting
open Bandits.Support.PhaseStartConditionalWaiting
open Bandits.Support.ReferenceFirstLiveReleaseGeometry
open Bandits.Support.ReferenceLocalReleaseWaitingPaths
open Bandits.Support.ReferencePhysicalReleaseQuota
open Bandits.Support.ReferencePostReplacementCollectionStoppedReleaseAdaptation
open Bandits.Support.ReferencePostReplacementCollectionUpServiceLaw
open Bandits.Support.ReferencePostReplacementCollectionSentinelSectionLaw
open Bandits.Support.ReferenceSourcePrefixHistoryFiltration
open scoped Classical BigOperators

namespace Bandits.Support.ReferencePostReplacementCollectionUpWeightedWaitingCost

variable {p : ConstructorDimensions.Parameters}

/-- The actual finite UP waiting charge, including supported dates on which
the pending set is empty. -/
def postRawKUpWeightedWaitingCharge
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p) : ℝ :=
  ∑ t : Fin p.T,
    (if (postRawKStoppedPendingSet rate rewards C_star C_h t z).Nonempty then
      (1 : ℝ) else 0) *
        postRawKReleaseOmega rate rewards C_star C_h t z

private def upWaitingPending
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) :
    ℕ → BootstrapPrivateRoundStreams.SourceInput p → Finset (Fin (p.m - 1)) :=
  fun n z => if hn : n < p.T then
    postRawKStoppedPendingSet rate rewards C_star C_h ⟨n, hn⟩ z
  else ∅

private def upWaitingObservation
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) :
    Fin (p.m - 1) → ℕ → BootstrapPrivateRoundStreams.SourceInput p → Bool :=
  fun i n z => if hn : n < p.T then
    ReferenceSourcePrefixHistoryFiltration.actualUp rate rewards C_star C_h i ⟨n, hn⟩ z
  else false

private def upWaitingWeight
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) :
    ℕ → BootstrapPrivateRoundStreams.SourceInput p → ℝ :=
  fun n z => if hn : n < p.T then
    postRawKReleaseOmega rate rewards C_star C_h ⟨n, hn⟩ z
  else 0

private theorem selectedFastArmMass_le_one
    (rate : ReferenceActivePhysicalStep.RateInput p)
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (selected : ReferenceActivePhysicalStep.Selection x)
    (j : CanonicalFastSampling.FastArm selected.view.payload.slowSet) :
    selectedFastArmMass rate selected j ≤ 1 := by
  have hnonneg (k : CanonicalFastSampling.FastArm selected.view.payload.slowSet) :
      0 ≤ selectedFastArmMass rate selected k :=
    CanonicalFastSampling.qGamma_nonneg p rate.eta.property
      selected.view.payload.eta_le_source_cap selected.view.payload.anchor
      (completeCurrentWeights selected) selected.view.payload.anchor_pos
      (fun a => (completeCurrentWeights_bounds selected
        (ReferenceLaterLiveNumericalReadout.selection_choiceValid selected) a).1)
      (fun a => (completeCurrentWeights_bounds selected
        (ReferenceLaterLiveNumericalReadout.selection_choiceValid selected) a).2.1)
      (fun a => (completeCurrentWeights_bounds selected
        (ReferenceLaterLiveNumericalReadout.selection_choiceValid selected) a).2.2) _ k
  have hsum : ∑ k, selectedFastArmMass rate selected k = 1 :=
    CanonicalFastSampling.qGamma_sum_eq_one p rate.eta.property
      selected.view.payload.eta_le_source_cap selected.view.payload.anchor
      (completeCurrentWeights selected) selected.view.payload.anchor_pos
      (fun a => (completeCurrentWeights_bounds selected
        (ReferenceLaterLiveNumericalReadout.selection_choiceValid selected) a).1)
      (fun a => (completeCurrentWeights_bounds selected
        (ReferenceLaterLiveNumericalReadout.selection_choiceValid selected) a).2.1)
      (fun a => (completeCurrentWeights_bounds selected
        (ReferenceLaterLiveNumericalReadout.selection_choiceValid selected) a).2.2) _
  rw [← hsum]
  exact Finset.single_le_sum (fun k _ => hnonneg k) (Finset.mem_univ j)

private theorem stoppedDate_source_start_le
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hkeep : postRawKStoppedDate rate rewards C_star C_h t z) :
    ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h ≤ t.val := by
  have hrel : ReferencePostReplacementCollectionReleaseSupport.rawReleaseRecords
      rate rewards C_star C_h z ≠ [] := by
    intro hnil
    obtain ⟨r, hr, _⟩ :=
      (ReferencePostReplacementCollectionReleaseSupport.rawReleaseRecords_support_iff
        rate rewards C_star C_h z t).mpr hkeep.1
    rw [hnil] at hr
    simp at hr
  obtain ⟨_, _, _, _, _, _, _, hdates⟩ :=
    ReferencePostReplacementCollectionStoppedReleaseAdaptation.postRawKReleaseSupport_inherited_prefix
      rate rewards C_star C_h control0 z hrel
  exact (hdates t hkeep.1).1

private theorem stoppedPending_localTask_mem
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s b : ℕ)
    (source : ReferenceLocalReleaseWaitingPaths.SourceEvent rate rewards C_star C_h s)
    (theta : ReferenceLocalReleaseWaitingPaths.SourceEvent rate rewards C_star C_h s → ℕ)
    (horizon : s ≤ p.T)
    (i : Fin (p.m - 1)) (t : Fin p.T) (hst : s ≤ t.val)
    (hcut : t.val + 1 < theta source)
    (hpending : i ∈ ReferenceSourcePrefixHistoryFiltration.pending
      rate rewards C_star C_h b t source.val) :
    i ∈ ReferenceLocalReleaseWaitingPaths.pendingTheta rate rewards C_star C_h
      s horizon b theta t.val source := by
  have hcalendar := ReferenceSourcePrefixHistoryFiltration.pending_source_calendar
    rate rewards C_star C_h b t s hst source
  rw [ReferenceLocalReleaseWaitingPaths.pendingTheta, ite_eq_left hcut]
  rw [← hcalendar]
  exact hpending

private theorem localTask_pending_actual_mem
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s b : ℕ)
    (source : ReferenceLocalReleaseWaitingPaths.SourceEvent rate rewards C_star C_h s)
    (horizon : s ≤ p.T) (t : Fin p.T) (hst : s ≤ t.val)
    (hcut : t.val + 1 < postRawKReleaseTheta rate rewards C_star C_h source.val)
    (i : Fin (p.m - 1))
    (hi : i ∈ ReferenceLocalReleaseWaitingPaths.pendingTheta rate rewards C_star C_h
      s horizon b (fun x => postRawKReleaseTheta rate rewards C_star C_h x.val)
      t.val source) :
    i ∈ ReferenceSourcePrefixHistoryFiltration.pending rate rewards C_star C_h b t source.val := by
  have hcalendar := ReferenceSourcePrefixHistoryFiltration.pending_source_calendar
    rate rewards C_star C_h b t s hst source
  have hi' : i ∈
      (ReferenceLocalReleaseWaitingPaths.calendarPendingReadout rate rewards C_star C_h
        s horizon b source t.val).getD ∅ := by
    simpa [ReferenceLocalReleaseWaitingPaths.pendingTheta, hcut] using hi
  rw [hcalendar]
  exact hi'

private theorem postRawKStoppedPendingSet_subset_of_phase
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (s t : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hst : s.val ≤ t.val)
    (hstart : postRawKReleaseSigma rate rewards C_star C_h z ≤ s.val + 1)
    (hcut : t.val + 1 < postRawKReleaseTheta rate rewards C_star C_h z)
    (i : Fin (p.m - 1))
    (hpending : i ∈ postRawKStoppedPendingSet rate rewards C_star C_h t z) :
    i ∈ postRawKStoppedPendingSet rate rewards C_star C_h s z := by
  have hkeepLater :=
    (postRawKStoppedPendingSet_mem_iff rate rewards C_star C_h t z i).mp hpending |>.1
  have hdateLater :=
    (postRawKStoppedPendingSet_mem_iff rate rewards C_star C_h t z i).mp hpending |>.2
  have hrel : ReferencePostReplacementCollectionReleaseSupport.rawReleaseRecords
      rate rewards C_star C_h z ≠ [] := by
    intro hnil
    have hsupport : t.val + 1 ∈ postRawKStoppedSupport rate rewards C_star C_h z :=
      (postRawKStoppedSupport_mem_iff rate rewards C_star C_h z (t.val + 1)).mpr
        ⟨t, hkeepLater, rfl⟩
    rw [postRawKStoppedSupport_empty_of_rawReleaseRecords_empty
      rate rewards C_star C_h z hnil] at hsupport
    simp at hsupport
  obtain ⟨hc, _a, _cutoff, _M, _hcutLow, _hcutHigh, _hstamp, _hrecords, _hread⟩ :=
    postRawKStoppedRecords_source rate rewards C_star C_h control0 z hrel
  let startSource := ReferenceCompletePhysicalHistory.physicalStart
    rate z rewards C_star C_h
  let source : ReferenceLocalReleaseWaitingPaths.SourceEvent
      rate rewards C_star C_h startSource := ⟨z, hc, rfl⟩
  let thetaLocal : ReferenceLocalReleaseWaitingPaths.SourceEvent
      rate rewards C_star C_h startSource → ℕ :=
    fun x => postRawKReleaseTheta rate rewards C_star C_h x.val
  have hthetaLocal : ∀ x, 1 ≤ thetaLocal x ∧ thetaLocal x ≤ p.T + 1 := by
    intro x
    have hi := postRawKRelease_interval rate rewards C_star C_h control0 x.val
    constructor
    · dsimp [thetaLocal]
      exact le_trans hi.2.1 hi.2.2.1
    · dsimp [thetaLocal]
      exact hi.2.2.2
  obtain ⟨u, hut, hu, huPending⟩ :=
    postRawKStoppedPendingDate_same_occurrence rate rewards C_star C_h t i z
      hkeepLater hdateLater
  have hI := (postRawKRelease_interval rate rewards C_star C_h control0 z).1
  have hsuppS : s.val + 1 ∈ postRawKStoppedSupport rate rewards C_star C_h z := by
    rw [hI, Finset.mem_Ico]
    exact ⟨hstart, by omega⟩
  obtain ⟨tS, hkeepS, htSEq⟩ :=
    (postRawKStoppedSupport_mem_iff rate rewards C_star C_h z (s.val + 1)).mp hsuppS
  have htSEq' : tS = s := by
    apply Fin.ext
    omega
  subst tS
  obtain ⟨uS, huSLt, huS, _hentryS⟩ := hkeepS.1
  have huSEq : uS = u :=
    ReferencePostReplacementCollectionReleaseSupport.postRawKOccurrence_unique
      rate rewards C_star C_h uS u z huS hu
  subst uS
  obtain ⟨uT, huTLt, huT, _hentryT⟩ := hkeepLater.1
  have huTEq : uT = u :=
    ReferencePostReplacementCollectionReleaseSupport.postRawKOccurrence_unique
      rate rewards C_star C_h uT u z huT hu
  subst uT
  have hsSource := stoppedDate_source_start_le rate rewards C_star C_h control0 s z hkeepS
  have htSource := stoppedDate_source_start_le rate rewards C_star C_h control0 t z hkeepLater
  have hstartHorizon : startSource ≤ p.T := le_trans hsSource (Nat.le_of_lt s.isLt)
  have hentryCalS := ReferenceSourcePrefixHistoryFiltration.entry_source_calendar
    rate rewards C_star C_h u.val s startSource hsSource source
  have hentryCalT := ReferenceSourcePrefixHistoryFiltration.entry_source_calendar
    rate rewards C_star C_h u.val t startSource htSource source
  have hgateS : ReferenceLocalReleaseCalendarCounts.calendarGate rate z rewards C_star C_h
      hc startSource (p.T - startSource) rfl (by omega) u.val s.val = some true := by
    have hmap := congrArg (Option.map Prod.fst) hentryCalS
    rw [hmap] at _hentryS
    simpa [ReferenceLocalReleaseCalendarCounts.calendarGate,
      ReferenceLocalReleaseCalendarCounts.calendarEntry,
      ReferenceRetainedReleasePhaseObservation.localReleaseEntry,
      ReferenceRetainedReleasePhaseObservation.localReleaseGate] using _hentryS
  have hgateT : ReferenceLocalReleaseCalendarCounts.calendarGate rate z rewards C_star C_h
      hc startSource (p.T - startSource) rfl (by omega) u.val t.val = some true := by
    have hmap := congrArg (Option.map Prod.fst) hentryCalT
    rw [hmap] at _hentryT
    simpa [ReferenceLocalReleaseCalendarCounts.calendarGate,
      ReferenceLocalReleaseCalendarCounts.calendarEntry,
      ReferenceRetainedReleasePhaseObservation.localReleaseEntry,
      ReferenceRetainedReleasePhaseObservation.localReleaseGate] using _hentryT
  have hintervalS := ReferenceLocalReleaseCalendarCounts.calendarGate_inside_interval
    rate z rewards C_star C_h hc startSource (p.T - startSource) rfl (by omega)
    u.val s.val hgateS
  have hintervalT := ReferenceLocalReleaseCalendarCounts.calendarGate_inside_interval
    rate z rewards C_star C_h hc startSource (p.T - startSource) rfl (by omega)
    u.val t.val hgateT
  have hcutS : s.val + 1 < thetaLocal source := by
    have hsupp := hsuppS
    rw [hI, Finset.mem_Ico] at hsupp
    simpa [thetaLocal] using hsupp.2
  have hcutT : t.val + 1 < thetaLocal source := by
    have hsuppT : t.val + 1 ∈ postRawKStoppedSupport rate rewards C_star C_h z :=
      (postRawKStoppedSupport_mem_iff rate rewards C_star C_h z (t.val + 1)).mpr
        ⟨t, hkeepLater, rfl⟩
    rw [hI, Finset.mem_Ico] at hsuppT
    simpa [thetaLocal] using hsuppT.2
  let alpha := ReferenceLocalReleaseGateChronology.gateAlpha u.val
    (ReferenceLocalReleaseWaitingPaths.sourceRunAtLaunch rate rewards C_star C_h
      startSource hstartHorizon source).records
  let beta := ReferenceLocalReleaseGateChronology.gateBeta u.val
    (ReferenceLocalReleaseWaitingPaths.sourceRunAtLaunch rate rewards C_star C_h
      startSource hstartHorizon source).records
  have halphaBeta : alpha < min beta (thetaLocal source) := by
    have hAlphaBeta : alpha < beta := by
      dsimp [alpha, beta, ReferenceLocalReleaseWaitingPaths.sourceRunAtLaunch]
      exact Nat.lt_of_le_of_lt hintervalS.1 hintervalS.2
    have hAlphaTheta : alpha < thetaLocal source :=
      lt_of_le_of_lt (by
        dsimp [alpha, ReferenceLocalReleaseWaitingPaths.sourceRunAtLaunch]
        exact hintervalS.1) hcutS
    exact Nat.lt_min.mpr ⟨hAlphaBeta, hAlphaTheta⟩
  have hAlphaLocal : ReferenceLocalReleaseWaitingPaths.localGateAlpha
      rate rewards C_star C_h startSource hstartHorizon u.val source = alpha := rfl
  have hBetaLocal : ReferenceLocalReleaseWaitingPaths.localGateBeta
      rate rewards C_star C_h startSource hstartHorizon u.val source = beta := rfl
  have hlocalStart : ReferenceLocalReleaseWaitingPaths.localPhaseSigma
      rate rewards C_star C_h startSource hstartHorizon u.val thetaLocal source ≤ s.val + 1 := by
    unfold ReferenceLocalReleaseWaitingPaths.localPhaseSigma
    simp only [hAlphaLocal, hBetaLocal, ite_eq_left halphaBeta]
    simpa [alpha, ReferenceLocalReleaseWaitingPaths.sourceRunAtLaunch] using hintervalS.1
  have hlocalEnd : t.val + 1 < ReferenceLocalReleaseWaitingPaths.localPhaseEndpoint
      rate rewards C_star C_h startSource hstartHorizon u.val thetaLocal source := by
    have hmin : t.val + 1 < min beta (thetaLocal source) :=
      Nat.lt_min.mpr ⟨hintervalT.2, hcutT⟩
    unfold ReferenceLocalReleaseWaitingPaths.localPhaseEndpoint
    simp only [hAlphaLocal, hBetaLocal, ite_eq_left halphaBeta]
    exact hmin
  have hlocalLater : i ∈ ReferenceLocalReleaseWaitingPaths.pendingTheta
      rate rewards C_star C_h startSource hstartHorizon u.val thetaLocal t.val source :=
    stoppedPending_localTask_mem rate rewards C_star C_h startSource u.val source thetaLocal
      hstartHorizon i t htSource hcutT huPending.2
  have hlocalEarlier :=
    ReferenceLocalReleaseWaitingPaths.pendingTheta_nested_inside_interval
      rate rewards C_star C_h startSource hstartHorizon u.val thetaLocal hthetaLocal
      source s.val t.val hst t.isLt hlocalStart hlocalEnd hlocalLater
  have hPendingAtS : i ∈ ReferenceSourcePrefixHistoryFiltration.pending
      rate rewards C_star C_h u.val s z :=
    localTask_pending_actual_mem rate rewards C_star C_h startSource u.val source
      hstartHorizon s hsSource hcutS i hlocalEarlier
  have hpendingSupportS : ReferencePostReplacementCollectionReleaseSupport.postRawKPendingSupport
      rate rewards C_star C_h s i z := ⟨u, huSLt, hu, hPendingAtS⟩
  have hdateS : postRawKStoppedPendingDate rate rewards C_star C_h s i z :=
    ⟨hpendingSupportS, hkeepS.2.1, hkeepS.2.2⟩
  exact (postRawKStoppedPendingSet_mem_iff rate rewards C_star C_h s z i).mpr
    ⟨hkeepS, hdateS⟩

private theorem upWaiting_quota_at_pending
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hpending : i ∈ postRawKStoppedPendingSet rate rewards C_star C_h t z) :
    PhaseServiceWaiting.N (upWaitingPending rate rewards C_star C_h)
      (upWaitingObservation rate rewards C_star C_h) i t.val z < 1 := by
  have hkeep :=
    (postRawKStoppedPendingSet_mem_iff rate rewards C_star C_h t z i).mp hpending |>.1
  have hdate :=
    (postRawKStoppedPendingSet_mem_iff rate rewards C_star C_h t z i).mp hpending |>.2
  have hrel : ReferencePostReplacementCollectionReleaseSupport.rawReleaseRecords
      rate rewards C_star C_h z ≠ [] := by
    intro hnil
    have hsupport : t.val + 1 ∈ postRawKStoppedSupport rate rewards C_star C_h z :=
      (postRawKStoppedSupport_mem_iff rate rewards C_star C_h z (t.val + 1)).mpr
        ⟨t, hkeep, rfl⟩
    rw [postRawKStoppedSupport_empty_of_rawReleaseRecords_empty
      rate rewards C_star C_h z hnil] at hsupport
    simp at hsupport
  obtain ⟨hc, _a, _cutoff, _M, _hcutLow, _hcutHigh, _hstamp, _hrecords, _hread⟩ :=
    postRawKStoppedRecords_source rate rewards C_star C_h control0 z hrel
  let startSource := ReferenceCompletePhysicalHistory.physicalStart
    rate z rewards C_star C_h
  let source : ReferenceLocalReleaseWaitingPaths.SourceEvent
      rate rewards C_star C_h startSource := ⟨z, hc, rfl⟩
  let thetaLocal : ReferenceLocalReleaseWaitingPaths.SourceEvent
      rate rewards C_star C_h startSource → ℕ :=
    fun x => postRawKReleaseTheta rate rewards C_star C_h x.val
  have hthetaLocal : ∀ x, 1 ≤ thetaLocal x ∧ thetaLocal x ≤ p.T + 1 := by
    intro x
    have hi := postRawKRelease_interval rate rewards C_star C_h control0 x.val
    constructor
    · dsimp [thetaLocal]
      exact le_trans hi.2.1 hi.2.2.1
    · dsimp [thetaLocal]
      exact hi.2.2.2
  obtain ⟨u, hut, hu, huPending⟩ :=
    postRawKStoppedPendingDate_same_occurrence rate rewards C_star C_h t i z hkeep hdate
  have hsSource := stoppedDate_source_start_le rate rewards C_star C_h control0 t z hkeep
  have hstartHorizon : startSource ≤ p.T := le_trans hsSource (Nat.le_of_lt t.isLt)
  have hsupport : t.val + 1 ∈ postRawKStoppedSupport rate rewards C_star C_h z :=
    (postRawKStoppedSupport_mem_iff rate rewards C_star C_h z (t.val + 1)).mpr
      ⟨t, hkeep, rfl⟩
  have hthetaCurrent : t.val + 1 < thetaLocal source := by
    have hI := (postRawKRelease_interval rate rewards C_star C_h control0 z).1
    rw [hI, Finset.mem_Ico] at hsupport
    simpa [thetaLocal] using hsupport.2
  have hcurrentLocal : i ∈ ReferenceLocalReleaseWaitingPaths.pendingTheta
      rate rewards C_star C_h startSource hstartHorizon u.val thetaLocal t.val source :=
    stoppedPending_localTask_mem rate rewards C_star C_h startSource u.val source thetaLocal
      hstartHorizon i t hsSource hthetaCurrent huPending.2
  have hstrict := ReferenceLocalReleaseWaitingPaths.strict_prior_N_zero_at_pending
    rate rewards C_star C_h startSource hstartHorizon u.val thetaLocal hthetaLocal
    source t.val i hcurrentLocal
  have hNle : PhaseServiceWaiting.N (upWaitingPending rate rewards C_star C_h)
      (upWaitingObservation rate rewards C_star C_h) i t.val z ≤
      PhaseServiceWaiting.N
        (ReferenceLocalReleaseWaitingPaths.pendingTheta rate rewards C_star C_h
          startSource hstartHorizon u.val thetaLocal)
        (ReferenceLocalReleaseWaitingPaths.upObservation rate rewards C_star C_h
          startSource hstartHorizon u.val) i t.val source := by
    unfold PhaseServiceWaiting.N
    apply Finset.sum_le_sum
    intro k hk
    have hklt : k < t.val := Finset.mem_range.mp hk
    have hkT : k < p.T := by omega
    let tk : Fin p.T := ⟨k, hkT⟩
    by_cases htask : i ∈ upWaitingPending rate rewards C_star C_h k z
    · have hpendingK : i ∈ postRawKStoppedPendingSet rate rewards C_star C_h tk z := by
        simpa [upWaitingPending, hkT, tk] using htask
      have hkeepK :=
        (postRawKStoppedPendingSet_mem_iff rate rewards C_star C_h tk z i).mp hpendingK |>.1
      have hdateK :=
        (postRawKStoppedPendingSet_mem_iff rate rewards C_star C_h tk z i).mp hpendingK |>.2
      obtain ⟨u', hu'lt, hu', hu'Pending⟩ :=
        postRawKStoppedPendingDate_same_occurrence rate rewards C_star C_h tk i z hkeepK hdateK
      have huEq : u' = u :=
        ReferencePostReplacementCollectionReleaseSupport.postRawKOccurrence_unique
          rate rewards C_star C_h u' u z hu' hu
      subst u'
      have hsK := stoppedDate_source_start_le rate rewards C_star C_h control0 tk z hkeepK
      have hcutK : k + 1 < thetaLocal source := by
        have hsupportK : k + 1 ∈ postRawKStoppedSupport rate rewards C_star C_h z :=
          (postRawKStoppedSupport_mem_iff rate rewards C_star C_h z (k + 1)).mpr
            ⟨tk, hkeepK, rfl⟩
        have hI := (postRawKRelease_interval rate rewards C_star C_h control0 z).1
        rw [hI, Finset.mem_Ico] at hsupportK
        simpa [thetaLocal] using hsupportK.2
      have hlocalPendingK : i ∈ ReferenceLocalReleaseWaitingPaths.pendingTheta
          rate rewards C_star C_h startSource hstartHorizon u.val thetaLocal k source :=
        stoppedPending_localTask_mem rate rewards C_star C_h startSource u.val source thetaLocal
          hstartHorizon i tk hsK hcutK hu'Pending.2
      have hflag : upWaitingObservation rate rewards C_star C_h i k z =
          ReferenceLocalReleaseWaitingPaths.upObservation rate rewards C_star C_h
            startSource hstartHorizon u.val i k source := by
        simpa [upWaitingObservation, hkT, tk] using
          (ReferenceSourcePrefixHistoryFiltration.flags_source_calendar
            rate rewards C_star C_h u.val i tk startSource hsK source).1
      simp [htask, hlocalPendingK, hflag]
    · simp [htask]
  rw [hstrict.2.1] at hNle
  omega

private theorem upWaiting_service_bound
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (a : ℝ)
    (ha : a = 1 / (12 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ))) :
    ∀ i n, n < p.T → ∀ᵐ z ∂(BootstrapPrivateRoundStreams.sourceInputLaw p),
      i ∈ upWaitingPending rate rewards C_star C_h n z →
        a * upWaitingWeight rate rewards C_star C_h n z ≤
          (BootstrapPrivateRoundStreams.sourceInputLaw p)[
            PhaseServiceWaiting.observation
              (upWaitingObservation rate rewards C_star C_h) i n |
            ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0
              (n + 1)] z := by
  intro i n hn
  let t : Fin p.T := ⟨n, hn⟩
  let μ := BootstrapPrivateRoundStreams.sourceInputLaw p
  let F := ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0
  have hmask := postRawKStoppedPendingSet_mem_measurable_preRound
    rate rewards C_star C_h control0 t i
  have hobsEq : PhaseServiceWaiting.observation
      (upWaitingObservation rate rewards C_star C_h) i n =
      (fun z => if ReferenceSourcePrefixHistoryFiltration.actualUp
        rate rewards C_star C_h i t z then (1 : ℝ) else 0) := by
    funext z
    simp [PhaseServiceWaiting.observation, upWaitingObservation, t, hn]
  have hobsInt : Integrable
      (PhaseServiceWaiting.observation (upWaitingObservation rate rewards C_star C_h) i n) μ := by
    rw [hobsEq]
    exact ReferenceSourcePhysicalFlagConditionalLaw.actualUp_observation_integrable
      rate rewards C_star C_h control0 i t
  have hfactor := condExp_indicator hobsInt hmask
  have hmasked := stoppedPending_actualUp_condExp rate rewards C_star C_h control0
  filter_upwards [hfactor, hmasked] with z hf hm
  intro hpending
  have hpendingT : i ∈ postRawKStoppedPendingSet rate rewards C_star C_h t z := by
    simpa [upWaitingPending, t, hn] using hpending
  have hzmem : z ∈ {x | i ∈ postRawKStoppedPendingSet rate rewards C_star C_h t x} :=
    hpendingT
  have hfactor' := hf
  rw [Set.indicator_of_mem hzmem] at hfactor'
  have hmaskedAt := hm i t
  have hmaskedObs :
      ({x | i ∈ postRawKStoppedPendingSet rate rewards C_star C_h t x}.indicator
        (PhaseServiceWaiting.observation (upWaitingObservation rate rewards C_star C_h) i n)) =
      ({x | i ∈ postRawKStoppedPendingSet rate rewards C_star C_h t x}.indicator
        (fun x => if ReferenceSourcePrefixHistoryFiltration.actualUp
          rate rewards C_star C_h i t x then (1 : ℝ) else 0)) := by
    funext x
    simp [hobsEq]
  have hmaskedCE :
      μ[({x | i ∈ postRawKStoppedPendingSet rate rewards C_star C_h t x}.indicator
        (PhaseServiceWaiting.observation (upWaitingObservation rate rewards C_star C_h) i n)) |
          F (n + 1)] z =
      μ[({x | i ∈ postRawKStoppedPendingSet rate rewards C_star C_h t x}.indicator
        (fun x => if ReferenceSourcePrefixHistoryFiltration.actualUp
          rate rewards C_star C_h i t x then (1 : ℝ) else 0)) | F (n + 1)] z := by
    exact congrArg (fun f => μ[f | F (n + 1)] z) hmaskedObs
  have hmean :
      μ[PhaseServiceWaiting.observation (upWaitingObservation rate rewards C_star C_h) i n |
          F (n + 1)] z =
        μ[({x | i ∈ postRawKStoppedPendingSet rate rewards C_star C_h t x}.indicator
          (fun x => if ReferenceSourcePrefixHistoryFiltration.actualUp
            rate rewards C_star C_h i t x then (1 : ℝ) else 0)) | F (n + 1)] z := by
    calc
      _ = μ[({x | i ∈ postRawKStoppedPendingSet rate rewards C_star C_h t x}.indicator
          (PhaseServiceWaiting.observation (upWaitingObservation rate rewards C_star C_h) i n)) |
            F (n + 1)] z := hfactor'.symm
      _ = _ := hmaskedCE
  have hwitness : ∃ (r : ReferenceActivePhysicalHorizon.RoundRecord
      (p := p) (rate := rate)),
      ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z =
        some r ∧ ∃ (selected : ReferenceActivePhysicalStep.Selection r.input),
      r.output.preparation.coordinator.selection = some selected ∧
      μ[({x | i ∈ postRawKStoppedPendingSet rate rewards C_star C_h t x}.indicator
        (fun x => if ReferenceSourcePrefixHistoryFiltration.actualUp
          rate rewards C_star C_h i t x then (1 : ℝ) else 0)) | F (n + 1)] z =
        ReferenceFirstLiveReleaseSliceMass.upReleaseMassFormula selected
          (ReferenceLaterLiveNumericalReadout.selection_choiceValid selected)
          (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t) ∧
      ReleaseRoundKernel.chi
        (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t)
        selected.view.payload.assignment.auxiliary /
        (12 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ)) ≤
        μ[({x | i ∈ postRawKStoppedPendingSet rate rewards C_star C_h t x}.indicator
          (fun x => if ReferenceSourcePrefixHistoryFiltration.actualUp
            rate rewards C_star C_h i t x then (1 : ℝ) else 0)) | F (n + 1)] z := by
    have hm1 : 1 ≤ p.m := by have hm := p.two_le_m; omega
    simpa [μ, F, t, hpendingT, Nat.cast_sub hm1] using hmaskedAt.2
  rcases hwitness with
    ⟨r, hrecord, selected, hselection, _hformula, hchiLower⟩
  let e := selectedAuxiliaryFastArm rate selected
  have haux : e.1 = selected.view.payload.assignment.auxiliary := rfl
  have hOmegaEq : postRawKReleaseOmega rate rewards C_star C_h t z =
      selectedFastArmMass rate selected e *
        ReleaseRoundKernel.chi (wholeGridRewardRow rewards t) e.1 := by
    simp only [postRawKReleaseOmega,
      (postRawKStoppedPendingSet_mem_iff rate rewards C_star C_h t z i).mp hpendingT |>.1,
      ite_true, hrecord, hselection]
    rfl
  have hchiNonneg : 0 ≤ ReleaseRoundKernel.chi
      (wholeGridRewardRow rewards t) e.1 := by
    unfold ReleaseRoundKernel.chi
    split_ifs <;> norm_num
  have hOmegaLeChi : postRawKReleaseOmega rate rewards C_star C_h t z ≤
      ReleaseRoundKernel.chi (wholeGridRewardRow rewards t) e.1 := by
    rw [hOmegaEq]
    calc
      selectedFastArmMass rate selected e *
          ReleaseRoundKernel.chi (wholeGridRewardRow rewards t) e.1 ≤
        1 * ReleaseRoundKernel.chi (wholeGridRewardRow rewards t) e.1 :=
          mul_le_mul_of_nonneg_right
            (selectedFastArmMass_le_one rate selected e) hchiNonneg
      _ = _ := by rw [one_mul]
  have hchiLower' : ReleaseRoundKernel.chi (wholeGridRewardRow rewards t) e.1 /
      (12 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ)) ≤
        μ[({x | i ∈ postRawKStoppedPendingSet rate rewards C_star C_h t x}.indicator
          (fun x => if ReferenceSourcePrefixHistoryFiltration.actualUp
            rate rewards C_star C_h i t x then (1 : ℝ) else 0)) | F (n + 1)] z := by
    have hchiLower'' := hchiLower
    rw [← haux] at hchiLower''
    exact hchiLower''
  have hchiLowerObs :
      ReleaseRoundKernel.chi (wholeGridRewardRow rewards t) e.1 /
        (12 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ)) ≤
          μ[PhaseServiceWaiting.observation (upWaitingObservation rate rewards C_star C_h) i n |
            F (n + 1)] z := by
    rw [hmean]
    exact hchiLower'
  have hscaled :
      (1 / (12 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ))) *
          postRawKReleaseOmega rate rewards C_star C_h t z ≤
        μ[PhaseServiceWaiting.observation (upWaitingObservation rate rewards C_star C_h) i n |
          F (n + 1)] z := by
    calc
      _ ≤ (1 / (12 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ))) *
          ReleaseRoundKernel.chi (wholeGridRewardRow rewards t) e.1 :=
        mul_le_mul_of_nonneg_left hOmegaLeChi (by positivity)
      _ = ReleaseRoundKernel.chi (wholeGridRewardRow rewards t) e.1 /
          (12 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ)) := by
        rw [div_eq_mul_inv]
        ring
      _ ≤ _ := hchiLowerObs
  calc
    a * upWaitingWeight rate rewards C_star C_h n z =
        (1 / (12 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ))) *
          postRawKReleaseOmega rate rewards C_star C_h t z := by
      rw [ha]
      simp [upWaitingWeight, hn, t]
    _ ≤ _ := hscaled

private theorem upWaiting_phase
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hpending : (upWaitingPending rate rewards C_star C_h t.val z).Nonempty) :
    postRawKReleaseSigma rate rewards C_star C_h z ≤ t.val + 1 ∧
      t.val + 1 < postRawKReleaseTheta rate rewards C_star C_h z := by
  have hpending' : (postRawKStoppedPendingSet rate rewards C_star C_h t z).Nonempty := by
    simpa only [upWaitingPending, dite_eq_left t.isLt] using hpending
  obtain ⟨i, hi⟩ := hpending'
  have hkeep :=
    (postRawKStoppedPendingSet_mem_iff rate rewards C_star C_h t z i).mp hi |>.1
  have hsupport : t.val + 1 ∈ postRawKStoppedSupport rate rewards C_star C_h z :=
    (postRawKStoppedSupport_mem_iff rate rewards C_star C_h z (t.val + 1)).mpr
      ⟨t, hkeep, rfl⟩
  have hI := (postRawKRelease_interval rate rewards C_star C_h control0 z).1
  rw [hI, Finset.mem_Ico] at hsupport
  exact hsupport

private theorem upWaiting_charge_eq_totalCharge
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (z : BootstrapPrivateRoundStreams.SourceInput p) :
    postRawKUpWeightedWaitingCharge rate rewards C_star C_h z =
      PhaseServiceWaiting.totalCharge (upWaitingPending rate rewards C_star C_h)
        (postRawKReleaseSigma rate rewards C_star C_h)
        (postRawKReleaseTheta rate rewards C_star C_h)
        (upWaitingWeight rate rewards C_star C_h) p.T z := by
  classical
  unfold postRawKUpWeightedWaitingCharge
  rw [Finset.sum_fin_eq_sum_range]
  unfold PhaseServiceWaiting.totalCharge
  apply Finset.sum_congr rfl
  intro n hn
  have hnT : n < p.T := Finset.mem_range.mp hn
  let t : Fin p.T := ⟨n, hnT⟩
  by_cases hpending : (postRawKStoppedPendingSet rate rewards C_star C_h t z).Nonempty
  · have hphase := upWaiting_phase rate rewards C_star C_h control0 t z (by
    simpa only [upWaitingPending, dite_eq_left t.isLt] using hpending)
    simp [PhaseServiceWaiting.A, upWaitingPending, upWaitingWeight,
      hnT, t, hpending, hphase.1, hphase.2]
  · simp [PhaseServiceWaiting.A, upWaitingPending,
      hnT, t, hpending]

/-- The literal stopped UP waiting charge is integrable under the original
source-input law. -/
theorem postRawKUpWeightedWaitingCharge_integrable
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p) :
    Integrable (postRawKUpWeightedWaitingCharge rate rewards C_star C_h)
      (BootstrapPrivateRoundStreams.sourceInputLaw p) := by
  let μ := BootstrapPrivateRoundStreams.sourceInputLaw p
  let F := ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0
  let P := upWaitingPending rate rewards C_star C_h
  let w := upWaitingWeight rate rewards C_star C_h
  let sigma := postRawKReleaseSigma rate rewards C_star C_h
  let theta := postRawKReleaseTheta rate rewards C_star C_h
  let d : ℝ := ((p.m - 1 : ℕ) : ℝ)
  let a : ℝ := 1 / (12 * d * (p.K : ℝ))
  have hm := p.two_le_m
  have hd : 0 < p.m - 1 := by omega
  have hKnat : 0 < p.K := ConstructorDimensions.K_pos p
  have hT : 0 < p.T := ConstructorDimensions.T_pos p
  have hK : 0 < (p.K : ℝ) := by exact_mod_cast hKnat
  have hKone : (1 : ℝ) ≤ (p.K : ℝ) := by
    exact_mod_cast (show 1 ≤ p.K by omega)
  have ha : 0 < a := by
    dsimp [a, d]
    positivity
  have hsigma : IsPreRoundStoppingTime F sigma := by
    simpa [F, sigma] using
      postRawKRelease_sigma_stopping rate rewards C_star C_h control0
  have htheta : IsPreRoundStoppingTime F theta := by
    simpa [F, theta] using
      postRawKRelease_theta_stopping rate rewards C_star C_h control0
  have hstart : ∀ z, 1 ≤ sigma z := by
    intro z
    exact (postRawKRelease_interval rate rewards C_star C_h control0 z).2.1
  have hordered : ∀ z, sigma z ≤ theta z := by
    intro z
    exact (postRawKRelease_interval rate rewards C_star C_h control0 z).2.2.1
  have hthetaBound : ∀ z, theta z ≤ p.T + 1 := by
    intro z
    exact (postRawKRelease_interval rate rewards C_star C_h control0 z).2.2.2
  have hP : ∀ i n, n < p.T →
      MeasurableSet[F (n + 1)] {z | i ∈ P n z} := by
    intro i n hn
    let t : Fin p.T := ⟨n, hn⟩
    simpa only [F, P, upWaitingPending, dite_eq_left hn] using
      (postRawKStoppedPendingSet_mem_measurable_preRound
        rate rewards C_star C_h control0 t i)
  have hphase : ∀ n, n < p.T → ∀ z, (P n z).Nonempty →
      sigma z ≤ n + 1 ∧ n + 1 < theta z := by
    intro n hn z hne
    let t : Fin p.T := ⟨n, hn⟩
    have hne' : (upWaitingPending rate rewards C_star C_h t.val z).Nonempty := by
      simpa only [P, t, upWaitingPending, dite_eq_left hn] using hne
    simpa [sigma, theta, t] using
      upWaiting_phase rate rewards C_star C_h control0 t z hne'
  have hwMeas : ∀ n, n < p.T → StronglyMeasurable[F (n + 1)] (w n) := by
    intro n hn
    let t : Fin p.T := ⟨n, hn⟩
    have hwEq : w n = postRawKReleaseOmega rate rewards C_star C_h t := by
      funext z
      simp [w, upWaitingWeight, t, hn]
    rw [hwEq]
    simpa [F] using
      (postRawKReleaseOmega_measurable_preChoice
        rate rewards C_star C_h control0 t).stronglyMeasurable
  have hwBound : ∀ n, n < p.T → ∀ z, w n z ∈ Set.Icc (0 : ℝ) (p.K : ℝ) := by
    intro n hn z
    let t : Fin p.T := ⟨n, hn⟩
    have hb := postRawKReleaseOmega_bounds rate rewards C_star C_h t z
    constructor
    · simpa [w, upWaitingWeight, t, hn] using hb.1
    · exact le_trans (by simpa [w, upWaitingWeight, t, hn] using hb.2) hKone
  have htotal := PhaseServiceWaiting.totalCharge_exp_integrable
    μ F P sigma theta w a ha hsigma htheta hP hwMeas hphase hwBound
  have hchargeEq (z : BootstrapPrivateRoundStreams.SourceInput p) :
      postRawKUpWeightedWaitingCharge rate rewards C_star C_h z =
        PhaseServiceWaiting.totalCharge P sigma theta w p.T z := by
    simpa [P, sigma, theta, w] using
      upWaiting_charge_eq_totalCharge rate rewards C_star C_h control0 z
  have hchargeFunEq :
      (fun z => postRawKUpWeightedWaitingCharge rate rewards C_star C_h z) =
        PhaseServiceWaiting.totalCharge P sigma theta w p.T := by
    funext z
    exact hchargeEq z
  change Integrable (fun z => postRawKUpWeightedWaitingCharge rate rewards C_star C_h z) μ
  rw [hchargeFunEq]
  exact htotal.1

/-- The total UP weighted waiting cost has the source logarithmic bound
conditional on the actual stopped release start, under the original source
input law. -/
theorem postRawKUpWeightedWaitingCharge_condExp_bound
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p) :
    (BootstrapPrivateRoundStreams.sourceInputLaw p)[
      postRawKUpWeightedWaitingCharge rate rewards C_star C_h |
        PhaseStartConditionalWaiting.phaseStartSigmaAlgebra
          (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0)
          (postRawKReleaseSigma rate rewards C_star C_h)
          (postRawKRelease_sigma_stopping rate rewards C_star C_h control0)] ≤ᵐ[
            BootstrapPrivateRoundStreams.sourceInputLaw p]
      fun _ =>
        12 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ) /
          (1 - Real.exp (-1)) *
            (Real.log ((p.m - 1 : ℕ) : ℝ) + 1) := by
  let μ := BootstrapPrivateRoundStreams.sourceInputLaw p
  let F := ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0
  let P := upWaitingPending rate rewards C_star C_h
  let X := upWaitingObservation rate rewards C_star C_h
  let w := upWaitingWeight rate rewards C_star C_h
  let sigma := postRawKReleaseSigma rate rewards C_star C_h
  let theta := postRawKReleaseTheta rate rewards C_star C_h
  let a : ℝ :=
    1 / (12 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ))
  have hm := p.two_le_m
  have hd : 0 < p.m - 1 := by omega
  have hT : 0 < p.T := ConstructorDimensions.T_pos p
  have hKnat : 0 < p.K := ConstructorDimensions.K_pos p
  have hdReal : 0 < ((p.m - 1 : ℕ) : ℝ) := by exact_mod_cast hd
  have hKReal : 0 < (p.K : ℝ) := by exact_mod_cast hKnat
  have hKone : (1 : ℝ) ≤ (p.K : ℝ) := by
    exact_mod_cast (show 1 ≤ p.K by omega)
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have haEq : a = 1 / (12 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ)) := rfl
  have hq : 0 < 1 := by omega
  have hsigma : IsPreRoundStoppingTime F sigma := by
    simpa [F, sigma] using
      postRawKRelease_sigma_stopping rate rewards C_star C_h control0
  have htheta : IsPreRoundStoppingTime F theta := by
    simpa [F, theta] using
      postRawKRelease_theta_stopping rate rewards C_star C_h control0
  have hstart : ∀ z, 1 ≤ sigma z := by
    intro z
    exact (postRawKRelease_interval rate rewards C_star C_h control0 z).2.1
  have hordered : ∀ z, sigma z ≤ theta z := by
    intro z
    exact (postRawKRelease_interval rate rewards C_star C_h control0 z).2.2.1
  have hthetaBound : ∀ z, theta z ≤ p.T + 1 := by
    intro z
    exact (postRawKRelease_interval rate rewards C_star C_h control0 z).2.2.2
  have hP : ∀ i n, n < p.T → MeasurableSet[F (n + 1)] {z | i ∈ P n z} := by
    intro i n hn
    let t : Fin p.T := ⟨n, hn⟩
    simpa only [F, P, upWaitingPending, dite_eq_left hn] using
      (postRawKStoppedPendingSet_mem_measurable_preRound
        rate rewards C_star C_h control0 t i)
  have hphase : ∀ n, n < p.T → ∀ z, (P n z).Nonempty →
      sigma z ≤ n + 1 ∧ n + 1 < theta z := by
    intro n hn z hne
    let t : Fin p.T := ⟨n, hn⟩
    have hne' : (upWaitingPending rate rewards C_star C_h t.val z).Nonempty := by
      simpa only [P, t, upWaitingPending, dite_eq_left hn] using hne
    simpa [sigma, theta, t] using
      upWaiting_phase rate rewards C_star C_h control0 t z hne'
  have hwMeas : ∀ n, n < p.T → StronglyMeasurable[F (n + 1)] (w n) := by
    intro n hn
    let t : Fin p.T := ⟨n, hn⟩
    have hwEq : w n = postRawKReleaseOmega rate rewards C_star C_h t := by
      funext z
      simp [w, upWaitingWeight, t, hn]
    rw [hwEq]
    simpa [F] using
      (postRawKReleaseOmega_measurable_preChoice
        rate rewards C_star C_h control0 t).stronglyMeasurable
  have hwBound : ∀ n, n < p.T → ∀ z, w n z ∈ Set.Icc (0 : ℝ) (p.K : ℝ) := by
    intro n hn z
    let t : Fin p.T := ⟨n, hn⟩
    have hb := postRawKReleaseOmega_bounds rate rewards C_star C_h t z
    constructor
    · simpa [w, upWaitingWeight, t, hn] using hb.1
    · exact le_trans (by simpa [w, upWaitingWeight, t, hn] using hb.2) hKone
  have hXMeas : ∀ i n, n < p.T →
      StronglyMeasurable[F (n + 2)]
        (PhaseServiceWaiting.observation X i n) := by
    intro i n hn
    let t : Fin p.T := ⟨n, hn⟩
    have hobs : PhaseServiceWaiting.observation X i n =
        (fun z => if ReferenceSourcePrefixHistoryFiltration.actualUp
          rate rewards C_star C_h i t z then (1 : ℝ) else 0) := by
      funext z
      simp [PhaseServiceWaiting.observation, X, upWaitingObservation, t, hn]
    rw [hobs]
    simpa [F] using
      (ReferenceSourcePrefixHistoryFiltration.flags_stronglyMeasurable
        rate rewards C_star C_h control0 i t).1
  have hnested : ∀ s t, s ≤ t → t < p.T → ∀ z,
      sigma z ≤ s + 1 → t + 1 < theta z → P t z ⊆ P s z := by
    intro s t hst ht z hstartS hcutT i hi
    let ts : Fin p.T := ⟨s, by omega⟩
    let tt : Fin p.T := ⟨t, ht⟩
    have hpendingT : i ∈ postRawKStoppedPendingSet rate rewards C_star C_h tt z := by
      simpa only [P, upWaitingPending, dite_eq_left ht] using hi
    have hpendingS := postRawKStoppedPendingSet_subset_of_phase
      rate rewards C_star C_h control0 ts tt z (by omega)
      (by simpa [sigma, ts] using hstartS)
      (by simpa [theta, tt] using hcutT) i hpendingT
    have hsT : s < p.T := lt_of_le_of_lt hst ht
    simpa only [P, upWaitingPending, dite_eq_left hsT] using hpendingS
  have hquota : ∀ i n, n < p.T → ∀ z, i ∈ P n z →
      PhaseServiceWaiting.N P X i n z < 1 := by
    intro i n hn z hi
    let t : Fin p.T := ⟨n, hn⟩
    have hpending : i ∈ postRawKStoppedPendingSet rate rewards C_star C_h t z := by
      simpa only [P, upWaitingPending, dite_eq_left hn] using hi
    have hq := upWaiting_quota_at_pending
      rate rewards C_star C_h control0 i t z hpending
    simpa [P, X, upWaitingPending, upWaitingObservation, t] using hq
  have hservice := upWaiting_service_bound
    rate rewards C_star C_h control0 a haEq
  have hgeneric := PhaseStartConditionalWaiting.phase_start_totalCharge_condExp_bound
    μ hd hT hKnat hq F P X w sigma theta a ha hsigma htheta hstart hordered
    hthetaBound hP hphase hnested hwMeas hwBound hXMeas hquota
    (by simpa [μ, F, P, X, w] using hservice)
  have hchargeEq (z : BootstrapPrivateRoundStreams.SourceInput p) :
      postRawKUpWeightedWaitingCharge rate rewards C_star C_h z =
        PhaseServiceWaiting.totalCharge P sigma theta w p.T z := by
    simpa [P, sigma, theta, w] using
      upWaiting_charge_eq_totalCharge rate rewards C_star C_h control0 z
  have hchargeFunEq :
      postRawKUpWeightedWaitingCharge rate rewards C_star C_h =
        PhaseServiceWaiting.totalCharge P sigma theta w p.T := by
    funext z
    exact hchargeEq z
  have hkappa : 0 < 1 - Real.exp (-1) := PhaseServiceWaiting.kappa_pos
  have hden : 0 < 12 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ) := by
    positivity
  have hcoef :
      ((1 : ℝ) + Real.log ((p.m - 1 : ℕ) : ℝ)) /
          (PhaseServiceWaiting.kappa * a) =
        12 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ) /
          (1 - Real.exp (-1)) *
            (Real.log ((p.m - 1 : ℕ) : ℝ) + 1) := by
    dsimp [a, PhaseServiceWaiting.kappa]
    field_simp [ne_of_gt hden, ne_of_gt hkappa]
    ring
  change μ[postRawKUpWeightedWaitingCharge rate rewards C_star C_h |
      PhaseStartConditionalWaiting.phaseStartSigmaAlgebra F sigma hsigma] ≤ᵐ[μ]
        fun _ => 12 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ) /
          (1 - Real.exp (-1)) *
            (Real.log ((p.m - 1 : ℕ) : ℝ) + 1)
  rw [hchargeFunEq]
  simpa [μ, F, sigma, hcoef] using hgeneric
