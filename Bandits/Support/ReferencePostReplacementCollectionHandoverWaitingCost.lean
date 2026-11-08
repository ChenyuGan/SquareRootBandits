/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferencePostReplacementCollectionHandoverReplayQuota
public import Bandits.Support.ReferencePostReplacementCollectionHandoverPhaseEndpoints
public import Bandits.Support.ReferencePostReplacementCollectionStoppedReleaseAdaptation
public import Bandits.Support.PhaseStartConditionalWaiting

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Conditional waiting cost of the literal post-replacement handover

The task sets in this module are the source's literal, globally stopped H
support.  The physical phase start and end remain the accepted raw H endpoints;
the decoder and launch-queue tests only mask the charge on the original source.

Sources: ZIP4 `05_binary_transport.tex:244-289`,
`06_interruptions.tex:431-490`, and `appendix_a_local_protocol.tex:28-79`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.ReferencePostReplacementCollectionHandoverSourcePrefix
open Bandits.Support.ReferencePostReplacementCollectionHandoverPhaseEndpoints
open Bandits.Support.ReferencePostReplacementCollectionHandoverDecoderCorrespondence
open Bandits.Support.ReferencePostReplacementCollectionHandoverReplayQuota
open Bandits.Support.ReferencePostReplacementCollectionHandoverFreshService
open Bandits.Support.PhaseServiceWaiting
open scoped BigOperators Classical ENNReal

namespace Bandits.Support.ReferencePostReplacementCollectionHandoverWaitingCost

variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ)
  (control0 : ContinuousLearningRows.TimeControl p)

local notation "Source" => BootstrapPrivateRoundStreams.SourceInput p
local notation "μ" => BootstrapPrivateRoundStreams.sourceInputLaw p
local notation "F" =>
  ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0
local notation "rawPending" =>
  ReferencePostReplacementCollectionHandoverPhaseEndpoints.rawHPendingNat
    rate rewards C_star C_h
local notation "sigmaH" =>
  ReferencePostReplacementCollectionHandoverPhaseEndpoints.rawHSigma
    rate rewards C_star C_h
local notation "thetaH" =>
  ReferencePostReplacementCollectionHandoverPhaseEndpoints.rawHTheta
    rate rewards C_star C_h
local notation "quotaH" => 2 * AffineBatchDecoder.quota p + 1
local notation "aH" => 1 / (8 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ))

/-- The literal later-H task at a calendar index.  The index `k` denotes
source date `k + 1`; out-of-horizon indices are empty. -/
public def literalPending (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (_control0 : ContinuousLearningRows.TimeControl p)
    (k : ℕ) (z : Source) : Finset (Fin (p.m - 1)) :=
  if hk : k < p.T then
    Finset.univ.filter fun i =>
      ReferencePostReplacementCollectionHandoverSourcePrefix.literalStoppedHTaskSupport
        rate rewards C_star C_h ⟨k, hk⟩ i z
  else ∅

/-- The whole reward row's number of arms with positive rounded reward. -/
public def gH (_rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (_C_star _C_h : ℝ) (_control0 : ContinuousLearningRows.TimeControl p)
    (k : ℕ) (_z : Source) : ℝ :=
  if hk : k < p.T then
    ((Finset.univ.filter fun a : Fin p.K => 0 < (rewards ⟨k, hk⟩ a).val).card : ℝ)
  else 0

/-- The literal globally stopped H support charge, summed over calendar
indices and retaining the round that detects decoder failure or overflow. -/
public def G_H (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (z : Source) : ℝ :=
  ∑ k ∈ Finset.range p.T,
    if (literalPending rate rewards C_star C_h control0 k z).Nonempty then
      gH rate rewards C_star C_h control0 k z else 0

/-- The source's capped support envelope, retained only for consequences. -/
public def gbarH (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (_control0 : ContinuousLearningRows.TimeControl p)
    (k : ℕ) (z : Source) : ℝ :=
  min (p.m : ℝ) (gH rate rewards C_star C_h _control0 k z)

/-- The actual whole-source binary service observation, using both the
pre-acceptance and post-acceptance physical branches. -/
public def XH (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (_control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1)) (k : ℕ) (z : Source) : Bool :=
  if hk : k < p.T then
    decide (X_before rate rewards C_star C_h ⟨k, hk⟩ i z +
      X_after rate rewards C_star C_h ⟨k, hk⟩ i z = 1)
  else false

/-- Pointwise the capped support envelope is bounded by the literal charge
weight; the requested charge itself remains uncapped. -/
public theorem gbarH_le_gH (k : ℕ) (z : Source) :
    gbarH rate rewards C_star C_h control0 k z ≤ gH rate rewards C_star C_h control0 k z :=
  min_le_right _ _

/-- The original literal decoder condition is exactly the accepted
same-source strict-past kept-date condition. -/
private theorem literalSafe_iff_kept (z : Source) (t : Fin p.T) :
    ReferenceFirstReplacementCollectionLiteralDecoderSafeSupport.Safe
      rate rewards C_star C_h z t.val ↔
    ReferenceFirstCollectionInclusiveDecoderStop.decoderDateKeptAt
      rate rewards C_star C_h z t :=
  ReferencePostReplacementCollectionStoppedReleaseAdaptation.safe_iff_decoderDateKeptAt
    rate rewards C_star C_h z t

/-- The literal H task and its same-date diagnostic envelope agree exactly.
The reverse direction extracts the original launch-prefix word from the
retained readout and then applies the accepted literal queue equivalence. -/
public theorem literalStoppedHTaskSupport_iff_diagnostic
    (t : Fin p.T) (i : Fin (p.m - 1)) (z : Source) :
    ReferencePostReplacementCollectionHandoverSourcePrefix.literalStoppedHTaskSupport
        rate rewards C_star C_h t i z ↔
      z ∈ ReferencePostReplacementCollectionHandoverSourcePrefix.diagnosticHTaskSupport
        rate rewards C_star C_h t i := by
  classical
  change
    (rawHTaskSupport rate rewards C_star C_h t i z ∧
      ReferenceFirstReplacementCollectionLiteralDecoderSafeSupport.Safe
        rate rewards C_star C_h z t.val ∧
      ∃ N,
        ReferenceFirstReplacementCollectionInclusiveStoppedCharge.originalPrefixInputs
          rate rewards C_star C_h t z = some N ∧
        ReferenceFirstCollectionLiteralStoppedCharge.literalQueueSafe rate N) ↔
    (rawHTaskSupport rate rewards C_star C_h t i z ∧
      ReferenceFirstCollectionInclusiveDecoderStop.decoderDateKeptAt
        rate rewards C_star C_h z t ∧
      z ∈ ReferenceFirstCollectionCurrentRetainedGate.H rate rewards C_star C_h t)
  constructor
  · rintro ⟨hraw, hsafe, N, hN, hqueue⟩
    exact ⟨hraw, (literalSafe_iff_kept rate rewards C_star C_h z t).mp hsafe,
      (ReferencePostReplacementCollectionStoppedReleaseAdaptation.retainedQueue_iff_literalQueueSafe
        rate rewards C_star C_h t z N hN).mpr hqueue⟩
  · rintro ⟨hraw, hkept, hretained⟩
    have hsafe := (literalSafe_iff_kept rate rewards C_star C_h z t).mpr hkept
    have hprefix :=
      ReferenceFirstReplacementCollectionInclusiveStoppedCharge.originalPrefixInputs_eq_pastCells?
        rate rewards C_star C_h t z
    have hread := hretained
    rw [ReferenceFirstCollectionCurrentRetainedGate.H] at hread
    change ∃ v,
      ReferenceFirstCollectionCurrentRetainedGate.prefixReadout?
        rate rewards C_star C_h t z = some v ∧ v.2.1 = false at hread
    rcases hread with ⟨v, hv, _hnotOverflow⟩
    change (ReferenceFirstCollectionCurrentRetainedGate.pastCells?
      rate rewards C_star C_h t z).map
        (fun N => ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
          (RecordedQueueRun.run
            (ReferenceFirstLaunchNumericalCell.queueParameters rate) N)) = some v at hv
    cases hpast : ReferenceFirstCollectionCurrentRetainedGate.pastCells?
        rate rewards C_star C_h t z with
    | none => simp [hpast] at hv
    | some N =>
      have hN : ReferenceFirstReplacementCollectionInclusiveStoppedCharge.originalPrefixInputs
          rate rewards C_star C_h t z = some N := by
        rw [hprefix, hpast]
      exact ⟨hraw, hsafe, N, hN,
        (ReferencePostReplacementCollectionStoppedReleaseAdaptation.retainedQueue_iff_literalQueueSafe
          rate rewards C_star C_h t z N hN).mp hretained⟩

/-- Membership in the literal pending set spells out its literal source
predicate at the same zero-based calendar index. -/
public theorem mem_literalPending_iff (k : ℕ) (z : Source) (i : Fin (p.m - 1)) :
    i ∈ literalPending rate rewards C_star C_h control0 k z ↔
      ∃ hk : k < p.T,
        ReferencePostReplacementCollectionHandoverSourcePrefix.literalStoppedHTaskSupport
          rate rewards C_star C_h ⟨k, hk⟩ i z := by
  by_cases hk : k < p.T
  · simp [literalPending, hk]
  · simp [literalPending, hk]

/-- Adaptation of each literal task at the original source-prefix field. -/
public theorem literalPending_mem_measurable
    (i : Fin (p.m - 1)) (k : ℕ) (hk : k < p.T) :
    MeasurableSet[F (k + 1)] {z : Source | i ∈ literalPending rate rewards C_star C_h control0 k z} := by
  have hdiag :=
    ReferencePostReplacementCollectionHandoverPredictableSupport.diagnosticHTaskSupport_measurableSet
      rate rewards C_star C_h control0 ⟨k, hk⟩ i
  have heq : {z : Source | i ∈ literalPending rate rewards C_star C_h control0 k z} =
      {z | z ∈ ReferencePostReplacementCollectionHandoverSourcePrefix.diagnosticHTaskSupport
        rate rewards C_star C_h ⟨k, hk⟩ i} := by
    ext z
    simp only [Set.mem_ofPred_eq, literalPending, dite_eq_left hk, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact (literalStoppedHTaskSupport_iff_diagnostic rate rewards C_star C_h
      ⟨k, hk⟩ i z)
  rw [heq]
  exact hdiag

/-- Every literal task is among the actual raw H tasks on the same date. -/
private theorem literalPending_subset_raw (k : ℕ) (z : Source) :
    literalPending rate rewards C_star C_h control0 k z ⊆ rawPending k z := by
  intro i hi
  rcases (mem_literalPending_iff rate rewards C_star C_h control0 k z i).mp hi with ⟨hk, h⟩
  have hraw := h.1
  exact (rawHPendingNat_mem rate rewards C_star C_h z k i).2 ⟨hk, hraw⟩

/-- A literal supported round lies inside the actual raw H interval. The
global endpoint theorem handles empty, absent-endpoint and horizon branches. -/
public theorem phase_bounds (k : ℕ) (z : Source)
    (hne : (literalPending rate rewards C_star C_h control0 k z).Nonempty) :
    sigmaH z ≤ k + 1 ∧ k + 1 < thetaH z := by
  have hraw : (rawPending k z).Nonempty := by
    rcases hne with ⟨i, hi⟩
    exact ⟨i, literalPending_subset_raw rate rewards C_star C_h control0 k z hi⟩
  exact (rawHPendingNat_nonempty_iff_interval_all rate rewards C_star C_h z k).mp hraw

private theorem rawH_support_actual_handover_index
    (t : Fin p.T) (i : Fin (p.m - 1)) (z : Source)
    (hsupport : rawHTaskSupport rate rewards C_star C_h t i z) :
    ∃ b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h).length,
      b.val = rawKEndpointIndex rate rewards C_star C_h z +
        (ReferenceFirstReplacementCollectionGlobalDecoderCharge.rawK
          rate rewards C_star C_h z).length ∧
      ReferenceCollectionPhaseHistory.laterChosen
          (ReferenceCompletePhysicalHistory.completeSuffixRecords
            rate z rewards C_star C_h)[b.val].input = true ∧
      ∃ j : Fin (actualHandoverRecords rate rewards C_star C_h z b).length,
        (actualHandoverRecords rate rewards C_star C_h z b)[j.val].input.time = t ∧
        ∃ selected : ReferenceActivePhysicalStep.Selection
            (actualHandoverRecords rate rewards C_star C_h z b)[j.val].input,
          (actualHandoverRecords rate rewards C_star C_h z b)[j.val].output.preparation.coordinator.selection =
              some selected ∧
          i ∈ selected.view.pendingAtChoice := by
  classical
  have hsupport0 := hsupport
  obtain ⟨r, hr, htime, selected, hselected, hi⟩ := hsupport
  have hK : ReferenceFirstReplacementCollectionGlobalDecoderCharge.rawK
      rate rewards C_star C_h z ≠ [] := by
    intro hnil
    rw [rawHRecords_eq_nil_of_rawK_eq_nil rate rewards C_star C_h z hnil] at hr
    cases hr
  rcases rawH_endpoint_cases rate rewards C_star C_h z hK with hempty | hactual
  · rcases hempty with ⟨hnil, _⟩
    rw [hnil] at hr
    cases hr
  · rcases hactual with ⟨b, hbindex, hlater, _payload, _ledger, _saved,
      _hstate, _hempty, hrecords⟩
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    have hbIndex : rawKEndpointIndex rate rewards C_star C_h z +
        (ReferenceFirstReplacementCollectionGlobalDecoderCharge.rawK
          rate rewards C_star C_h z).length = b.val := by
      simpa only [rawKEndpointIndex, R] using hbindex.symm
    have hbBirth : rawKEndpointRecord? rate rewards C_star C_h z = some R[b.val] := by
      change R[rawKEndpointIndex rate rewards C_star C_h z +
        (ReferenceFirstReplacementCollectionGlobalDecoderCharge.rawK
          rate rewards C_star C_h z).length]? = some R[b.val]
      rw [hbIndex]
      exact List.getElem?_eq_getElem b.isLt
    have _hseg := (rawHTaskSupport_iff_actual_segment rate rewards C_star C_h z
      hK R[b.val] hbBirth t i).mp hsupport0
    have hrecords' : rawHRecords rate rewards C_star C_h z =
        actualHandoverRecords rate rewards C_star C_h z b := by
      simpa only [actualHandoverRecords, ← hbIndex] using hrecords
    have hrH : r ∈ actualHandoverRecords rate rewards C_star C_h z b := by
      rw [← hrecords']
      exact hr
    obtain ⟨j, hj, hrEq⟩ := List.mem_iff_getElem.mp hrH
    let j' : Fin (actualHandoverRecords rate rewards C_star C_h z b).length := ⟨j, hj⟩
    cases hrEq
    refine ⟨b, hbIndex.symm, hlater, j', ?_, ?_⟩
    · simpa [j'] using htime
    · simpa [j'] using ⟨selected, hselected, hi⟩

private theorem option_mapM_take {α : Type*} (xs : List (Option α))
    (out : List α) (hout : xs.mapM id = some out) (n : ℕ) :
    (xs.take n).mapM id = some (out.take n) := by
  induction xs generalizing out n with
  | nil =>
      have he : out = [] := (Option.some.inj hout).symm
      subst out
      simp
  | cons x xs ih =>
      cases x with
      | none => simp [List.mapM_cons] at hout
      | some a =>
          cases ht : xs.mapM id with
          | none => simp [List.mapM_cons, ht] at hout
          | some rest =>
              have he : a :: rest = out := by simpa [List.mapM_cons, ht] using hout
              subst out
              cases n with
              | zero => rfl
              | succ n => simp [List.take_succ_cons, List.mapM_cons, ih rest ht n]

private theorem originalPrefixInputs_take
    (z : Source) (t : Fin p.T) (N : List (RecordedQueueRun.RoundInput p.K))
    (hN : ReferenceFirstReplacementCollectionInclusiveStoppedCharge.originalPrefixInputs
      rate rewards C_star C_h t z = some N)
    (n : ℕ)
    (hs : ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h ≤ n)
    (hnt : n ≤ t.val) :
    ReferenceFirstReplacementCollectionInclusiveStoppedCharge.originalPrefixInputs
      rate rewards C_star C_h ⟨n, lt_of_le_of_lt hnt t.isLt⟩ z =
        some (N.take (n - ReferenceCompletePhysicalHistory.physicalStart
          rate z rewards C_star C_h)) := by
  have hlaunch := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs_launch
    rate rewards C_star C_h t.val z N hN
  have hlaunchN : ReferenceSourcePrefixHistoryFiltration.actualLaunchBy
      rate rewards C_star C_h n z := ⟨hlaunch.1, hs⟩
  change ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
      rate rewards C_star C_h t.val z = some N at hN
  rw [ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs,
    ite_eq_left hlaunch] at hN
  have htaken := option_mapM_take _ N hN
    (n - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
  simp only [← List.map_take, List.take_take] at htaken
  have hle : n - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h ≤
      t.val - ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart
        rate rewards C_star C_h z := by
    dsimp [ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart]
    omega
  rw [Nat.min_eq_left hle] at htaken
  change ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
      rate rewards C_star C_h n z = _
  rw [ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs,
    ite_eq_left hlaunchN]
  exact htaken

private theorem literalQueueSafe_take
    (N : List (RecordedQueueRun.RoundInput p.K))
    (hN : ReferenceFirstCollectionLiteralStoppedCharge.literalQueueSafe rate N)
    (n : ℕ) :
    ReferenceFirstCollectionLiteralStoppedCharge.literalQueueSafe rate (N.take n) := by
  intro h hh a
  have hhn : h ≤ n := le_trans hh (List.length_take_le n N)
  have hhN : h ≤ N.length := le_trans hh (List.length_take_le' n N)
  have hsafe := hN h hhN a
  unfold ReferenceFirstCollectionLiteralStoppedCharge.calendarQueue at hsafe ⊢
  rw [List.take_take, Nat.min_eq_left hhn]
  exact hsafe

private theorem literalStoppedHTaskSupport_backward
    (z : Source) (s t : Fin p.T) (hst : s.val ≤ t.val)
    (hstart : sigmaH z ≤ s.val + 1) (i : Fin (p.m - 1))
    (hi : i ∈ literalPending rate rewards C_star C_h control0 t.val z) :
    ReferencePostReplacementCollectionHandoverSourcePrefix.literalStoppedHTaskSupport
      rate rewards C_star C_h s i z := by
  rcases (mem_literalPending_iff rate rewards C_star C_h control0 t.val z i).mp hi with
    ⟨_ht, htSupport⟩
  have hrawT : i ∈ rawPending t.val z :=
    (rawHPendingNat_mem rate rewards C_star C_h z t.val i).2 ⟨t.isLt, htSupport.1⟩
  have hrawS : i ∈ rawPending s.val z :=
    rawHPendingNat_subset_after_start rate rewards C_star C_h z s.val t.val hst hstart hrawT
  obtain ⟨hsT, hsSupport⟩ :=
    (rawHPendingNat_mem rate rewards C_star C_h z s.val i).mp hrawS
  have hsSupport' : rawHTaskSupport rate rewards C_star C_h s i z := by
    have hEq : (⟨s.val, hsT⟩ : Fin p.T) = s := Fin.ext rfl
    rw [← hEq]
    exact hsSupport
  have hsafeS : ReferenceFirstReplacementCollectionLiteralDecoderSafeSupport.Safe
      rate rewards C_star C_h z s.val := by
    intro u hu hfailure
    exact htSupport.2.1 u (lt_of_lt_of_le hu hst) hfailure
  rcases htSupport.2.2 with ⟨N, hN, hqueue⟩
  rcases ReferencePostReplacementCollectionHandoverPhaseEndpoints.rawHTaskSupport_same_actual_record
      rate rewards C_star C_h z s i hsSupport' with
    ⟨r, _hr, hactual, _selected, _hselected, _hi, _hrtime⟩
  have hlaunchS : ReferenceSourcePrefixHistoryFiltration.actualLaunchBy
      rate rewards C_star C_h s.val z := by
    by_cases hl : ReferenceSourcePrefixHistoryFiltration.actualLaunchBy
        rate rewards C_star C_h s.val z
    · exact hl
    · rw [ReferenceSourcePrefixHistoryFiltration.actualRecord_eq_none_of_not_launchBy
        rate rewards C_star C_h s z hl] at hactual
      cases hactual
  have hsPhysical : ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h ≤ s.val :=
    hlaunchS.2
  have hprefix := originalPrefixInputs_take rate rewards C_star C_h z t N hN
    s.val hsPhysical hst
  have hqueueS := literalQueueSafe_take rate N hqueue
    (s.val - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
  exact ⟨hsSupport', hsafeS,
    N.take (s.val - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h),
    hprefix, hqueueS⟩

public theorem literalPending_nested
    (s t : ℕ) (hst : s ≤ t) (ht : t < p.T) (z : Source)
    (hstart : sigmaH z ≤ s + 1) :
    literalPending rate rewards C_star C_h control0 t z ⊆
      literalPending rate rewards C_star C_h control0 s z := by
  intro i hi
  let ss : Fin p.T := ⟨s, lt_of_le_of_lt hst ht⟩
  let tt : Fin p.T := ⟨t, ht⟩
  exact (mem_literalPending_iff rate rewards C_star C_h control0 s z i).mpr
    ⟨ss.isLt, literalStoppedHTaskSupport_backward rate rewards C_star C_h control0 z
      ss tt hst hstart i hi⟩

private theorem actualLiteralHandoverServiceTick_eq_pending
    (z : Source)
    (b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h).length)
    (t : Fin p.T) (i : Fin (p.m - 1))
    (hindex : ∀ _h : ReferencePostReplacementCollectionHandoverSourcePrefix.literalStoppedHTaskSupport
        rate rewards C_star C_h t i z,
      ∃ j : Fin (actualHandoverRecords rate rewards C_star C_h z b).length,
        (actualHandoverRecords rate rewards C_star C_h z b)[j.val].input.time = t) :
    actualLiteralHandoverServiceTick rate rewards C_star C_h z b i t =
      if i ∈ literalPending rate rewards C_star C_h control0 t.val z ∧
          XH rate rewards C_star C_h control0 i t.val z then 1 else 0 := by
  classical
  by_cases hmem : i ∈ literalPending rate rewards C_star C_h control0 t.val z
  · rcases (mem_literalPending_iff rate rewards C_star C_h control0 t.val z i).mp hmem with
      ⟨ht, hs⟩
    let t' : Fin p.T := ⟨t.val, ht⟩
    have htEq : t' = t := Fin.ext rfl
    have hs' : ReferencePostReplacementCollectionHandoverSourcePrefix.literalStoppedHTaskSupport
        rate rewards C_star C_h t i z := by
      rw [← htEq]
      exact hs
    obtain ⟨j, htime⟩ := hindex hs'
    have hservice := service_zero_or_one rate rewards C_star C_h t i z
    have hX : XH rate rewards C_star C_h control0 i t.val z = true ↔
        X_before rate rewards C_star C_h t i z + X_after rate rewards C_star C_h t i z = 1 := by
      rcases hservice with hz | ho
      · simp [XH, t.isLt, hz]
      · simp [XH, t.isLt, ho]
    by_cases hx : XH rate rewards C_star C_h control0 i t.val z
    · have hone := hX.mp hx
      have htick : ∃ j : Fin (actualHandoverRecords rate rewards C_star C_h z b).length,
          (actualHandoverRecords rate rewards C_star C_h z b)[j.val].input.time = t ∧
          ReferencePostReplacementCollectionHandoverSourcePrefix.literalStoppedHTaskSupport
            rate rewards C_star C_h t i z ∧
          X_before rate rewards C_star C_h t i z + X_after rate rewards C_star C_h t i z = 1 :=
        ⟨j, htime, hs', hone⟩
      unfold actualLiteralHandoverServiceTick
      rw [ite_eq_left htick]
      simp [hmem, hx]
    · have hzero : X_before rate rewards C_star C_h t i z +
        X_after rate rewards C_star C_h t i z = 0 := by
        rcases hservice with hzero | hone
        · exact hzero
        · exact (hx (hX.mpr hone)).elim
      have hnot : ¬ ∃ j : Fin (actualHandoverRecords rate rewards C_star C_h z b).length,
          (actualHandoverRecords rate rewards C_star C_h z b)[j.val].input.time = t ∧
          ReferencePostReplacementCollectionHandoverSourcePrefix.literalStoppedHTaskSupport
            rate rewards C_star C_h t i z ∧
          X_before rate rewards C_star C_h t i z + X_after rate rewards C_star C_h t i z = 1 := by
        rintro ⟨_, _, _, hone⟩
        rw [hzero] at hone
        exact zero_ne_one hone
      unfold actualLiteralHandoverServiceTick
      rw [ite_eq_right hnot]
      simp [hmem, hx]
  · have hnot : ¬ ∃ j : Fin (actualHandoverRecords rate rewards C_star C_h z b).length,
        (actualHandoverRecords rate rewards C_star C_h z b)[j.val].input.time = t ∧
        ReferencePostReplacementCollectionHandoverSourcePrefix.literalStoppedHTaskSupport
          rate rewards C_star C_h t i z ∧
        X_before rate rewards C_star C_h t i z + X_after rate rewards C_star C_h t i z = 1 := by
      rintro ⟨j, _, hs, _⟩
      exact hmem ((mem_literalPending_iff rate rewards C_star C_h control0 t.val z i).mpr
        ⟨t.isLt, hs⟩)
    unfold actualLiteralHandoverServiceTick
    rw [ite_eq_right hnot]
    simp [hmem]

public theorem rawH_physical_incoming_quota_strict
    (k : ℕ) (hk : k < p.T) (z : Source) (i : Fin (p.m - 1))
    (hi : i ∈ literalPending rate rewards C_star C_h control0 k z) :
    ∃ b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h).length,
      ReferenceCollectionPhaseHistory.laterChosen
        (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[b.val].input = true ∧
      actualLiteralHandoverServiceCount rate rewards C_star C_h z b i k < quotaH := by
  classical
  let t : Fin p.T := ⟨k, hk⟩
  have hsupport : ReferencePostReplacementCollectionHandoverSourcePrefix.literalStoppedHTaskSupport
      rate rewards C_star C_h t i z := by
    rcases (mem_literalPending_iff rate rewards C_star C_h control0 k z i).mp hi with ⟨h, hs⟩
    have hEq : h = hk := Subsingleton.elim _ _
    subst h
    exact hs
  have hraw := hsupport.1
  obtain ⟨b, _hbidx, hb, j, htime, _hpending⟩ :=
    rawH_support_actual_handover_index rate rewards C_star C_h t i z hraw
  refine ⟨b, hb, ?_⟩
  have hquota := actual_later_handover_physical_service_count_lt_of_supported
    rate rewards C_star C_h z b hb i j (by simpa only [htime] using hsupport)
  have htimeval : (actualHandoverRecords rate rewards C_star C_h z b)[j.val].input.time.val = k :=
    congrArg Fin.val htime
  rw [← htimeval]
  exact hquota

private theorem range_fin_sum (T n : ℕ) (hn : n ≤ T) (f : ℕ → ℕ) :
    (∑ r ∈ Finset.range n, f r) =
      ∑ t : Fin T, if t.val < n then f t.val else 0 := by
  classical
  let g : ℕ → ℕ := fun r => if r < T then if r < n then f r else 0 else 0
  have hleft : (∑ r ∈ Finset.range n, f r) = ∑ r ∈ Finset.range n, g r := by
    apply Finset.sum_congr rfl
    intro r hr
    have hrn := Finset.mem_range.mp hr
    have hrT := lt_of_lt_of_le hrn hn
    simp [g, hrn, hrT]
  have hright : (∑ t : Fin T, if t.val < n then f t.val else 0) =
      ∑ r ∈ Finset.range T, g r := by
    calc
      _ = ∑ t : Fin T, g t.val := by
        apply Finset.sum_congr rfl
        intro t ht
        by_cases htn : t.val < n <;> simp [g, t.isLt, htn]
      _ = _ := Fin.sum_univ_eq_sum_range g T
  have hsub : Finset.range n ⊆ Finset.range T := Finset.range_subset_range.mpr hn
  have hzero : ∀ r ∈ Finset.range T, r ∉ Finset.range n → g r = 0 := by
    intro r hrT hrn
    have hnle : n ≤ r := Nat.le_of_not_gt (fun hlt => hrn (Finset.mem_range.mpr hlt))
    simp [g, not_lt.mpr hnle]
  calc
    (∑ r ∈ Finset.range n, f r) = ∑ r ∈ Finset.range n, g r := hleft
    _ = ∑ r ∈ Finset.range T, g r := Finset.sum_subset hsub hzero
    _ = ∑ t : Fin T, if t.val < n then f t.val else 0 := hright.symm

/-- The generic literal Boolean count is exactly the actual H handover's
uncapped physical service count for its actual rawK-endpoint birth. -/
private theorem literalN_eq_actualHandoverServiceCount
    (z : Source) (i : Fin (p.m - 1)) (n : ℕ) (hn : n ≤ p.T)
    (b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (hbIndex : b.val = rawKEndpointIndex rate rewards C_star C_h z +
      (ReferenceFirstReplacementCollectionGlobalDecoderCharge.rawK
        rate rewards C_star C_h z).length) :
    PhaseServiceWaiting.N (literalPending rate rewards C_star C_h control0)
        (XH rate rewards C_star C_h control0) i n z =
      actualLiteralHandoverServiceCount rate rewards C_star C_h z b i n := by
  classical
  let f : ℕ → ℕ := fun k =>
    if i ∈ literalPending rate rewards C_star C_h control0 k z ∧
        XH rate rewards C_star C_h control0 i k z then 1 else 0
  unfold PhaseServiceWaiting.N
  change (∑ k ∈ Finset.range n, f k) = _
  rw [range_fin_sum p.T n hn f]
  unfold actualLiteralHandoverServiceCount
  apply Finset.sum_congr rfl
  intro t ht
  have hindex : ∀ hs : ReferencePostReplacementCollectionHandoverSourcePrefix.literalStoppedHTaskSupport
      rate rewards C_star C_h t i z,
      ∃ j : Fin (actualHandoverRecords rate rewards C_star C_h z b).length,
        (actualHandoverRecords rate rewards C_star C_h z b)[j.val].input.time = t := by
    intro hs
    obtain ⟨b', hbIndex', _hb', j, htime, _hselected⟩ :=
      rawH_support_actual_handover_index rate rewards C_star C_h t i z hs.1
    have hbEq : b' = b := by
      apply Fin.ext
      omega
    subst b'
    exact ⟨j, htime⟩
  have htick := actualLiteralHandoverServiceTick_eq_pending
    rate rewards C_star C_h control0 z b t i hindex
  by_cases htn : t.val < n
  · simp [htn, f, htick]
  · simp [htn]

/-- Immediately before each supported H date, the generic waiting count is
strictly below the incoming physical service quota. -/
public theorem rawH_incoming_quota_strict
    (k : ℕ) (hk : k < p.T) (z : Source) (i : Fin (p.m - 1))
    (hi : i ∈ literalPending rate rewards C_star C_h control0 k z) :
    PhaseServiceWaiting.N (literalPending rate rewards C_star C_h control0)
        (XH rate rewards C_star C_h control0) i k z < quotaH := by
  let t : Fin p.T := ⟨k, hk⟩
  have hs : ReferencePostReplacementCollectionHandoverSourcePrefix.literalStoppedHTaskSupport
      rate rewards C_star C_h t i z := by
    rcases (mem_literalPending_iff rate rewards C_star C_h control0 k z i).mp hi with
      ⟨_hk, hs⟩
    exact hs
  obtain ⟨b, hbIndex, hb, j, htime, _hselected⟩ :=
    rawH_support_actual_handover_index rate rewards C_star C_h t i z hs.1
  have hphysical := actual_later_handover_physical_service_count_lt_of_supported
    rate rewards C_star C_h z b hb i j (by simpa only [htime] using hs)
  rw [literalN_eq_actualHandoverServiceCount rate rewards C_star C_h control0 z i k
    (Nat.le_of_lt hk) b hbIndex]
  have htimeval : (actualHandoverRecords rate rewards C_star C_h z b)[j.val].input.time.val = k :=
    congrArg Fin.val htime
  rw [← htimeval]
  exact hphysical

/-- The raw H start and end retain their accepted, finite source endpoint
bounds. -/
public theorem endpoint_bounds (z : Source) :
    1 ≤ sigmaH z ∧ sigmaH z ≤ p.T + 1 ∧
      sigmaH z ≤ thetaH z ∧ 1 ≤ thetaH z ∧ thetaH z ≤ p.T + 1 := by
  have hs := rawHSigma_bounds rate rewards C_star C_h z
  have ht := rawHTheta_bounds rate rewards C_star C_h z
  exact ⟨hs.1, hs.2, rawHSigma_le_rawHTheta rate rewards C_star C_h z, ht.1, ht.2⟩

/-- The literal, uncapped calendar charge is exactly the generic phase
totalCharge for the same raw endpoints and literal pending sets. -/
public theorem G_H_eq_totalCharge (z : Source) :
    G_H rate rewards C_star C_h control0 z =
      PhaseServiceWaiting.totalCharge (literalPending rate rewards C_star C_h control0)
        sigmaH thetaH (gH rate rewards C_star C_h control0) p.T z := by
  classical
  unfold G_H
  unfold PhaseServiceWaiting.totalCharge
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hne : (literalPending rate rewards C_star C_h control0 k z).Nonempty
  · have hph := phase_bounds rate rewards C_star C_h control0 k z hne
    have hcond : sigmaH z ≤ k + 1 ∧ k + 1 < thetaH z ∧
        (literalPending rate rewards C_star C_h control0 k z).Nonempty :=
      ⟨hph.1, hph.2, hne⟩
    simp only [PhaseServiceWaiting.A, Set.indicator_apply, Set.mem_ofPred_eq]
    simp [hne, hcond]
  · have hcond : ¬ (sigmaH z ≤ k + 1 ∧ k + 1 < thetaH z ∧
        (literalPending rate rewards C_star C_h control0 k z).Nonempty) := by
      rintro ⟨_, _, hP⟩
      exact hne hP
    simp only [PhaseServiceWaiting.A, Set.indicator_apply, Set.mem_ofPred_eq]
    simp [hne]

/-- The positive-reward arm count is a predictable, deterministic weight. -/
public theorem gH_preRound_stronglyMeasurable (k : ℕ) :
    StronglyMeasurable[F (k + 1)] (fun z : Source => gH rate rewards C_star C_h control0 k z) := by
  by_cases hk : k < p.T
  · simp only [gH, dite_eq_left hk]
    exact stronglyMeasurable_const
  · simp only [gH, dite_eq_right hk]
    exact stronglyMeasurable_const

/-- The whole-row support weight lies in the generic waiting theorem's
nonnegative `K`-bounded interval. -/
public theorem gH_bounds (k : ℕ) (hk : k < p.T) (z : Source) :
    gH rate rewards C_star C_h control0 k z ∈ Set.Icc (0 : ℝ) (p.K : ℝ) := by
  rw [gH, dite_eq_left hk]
  have hcard :
      (Finset.univ.filter fun a : Fin p.K => 0 < (rewards ⟨k, hk⟩ a).val).card ≤ p.K := by
    calc
      _ ≤ (Finset.univ : Finset (Fin p.K)).card := Finset.card_filter_le _ _
      _ = p.K := Finset.card_fin _
  exact ⟨Nat.cast_nonneg _, Nat.cast_le.mpr hcard⟩

/-- The actual before/after service is exactly the Boolean observation used
by the waiting process, with the two physical acceptance branches retained. -/
public theorem observation_eq_physical_service
    (t : Fin p.T) (i : Fin (p.m - 1)) :
    PhaseServiceWaiting.observation (XH rate rewards C_star C_h control0)
        i t.val =
      fun z : Source => X_before rate rewards C_star C_h t i z +
        X_after rate rewards C_star C_h t i z := by
  funext z
  have h01 := service_zero_or_one rate rewards C_star C_h t i z
  rcases h01 with hzero | hone
  · simp [PhaseServiceWaiting.observation, XH, t.isLt, hzero]
  · simp [PhaseServiceWaiting.observation, XH, t.isLt, hone]

/-- Round-end strong measurability is established from the actual Borel
acceptance and service factors, not inferred from integrability. -/
public theorem observation_roundEnd_stronglyMeasurable
    (t : Fin p.T) (i : Fin (p.m - 1)) :
    StronglyMeasurable[F (t.val + 2)]
      (PhaseServiceWaiting.observation (XH rate rewards C_star C_h control0) i t.val) := by
  rw [observation_eq_physical_service rate rewards C_star C_h control0 t i]
  have hbase : StronglyMeasurable[F (t.val + 2)]
      (X_before rate rewards C_star C_h t i) := by
    let E := A_before rate rewards C_star C_h t i
    let V := fun z : Source =>
      if ReferenceFirstLiveHandoverBoundaryFactorization.V_before
        rate rewards C_star C_h i t z then (1 : ℝ) else 0
    have hE : MeasurableSet[F (t.val + 2)] E := by
      change ∃ S, MeasurableSet S ∧
        ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 (t.val + 1) ⁻¹' S = E
      rcases ReferencePostReplacementCollectionHandoverFreshService.measurableSet_A_before
          rate rewards C_star C_h control0 t i with ⟨S, hS, hpre⟩
      let S' := ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val ⁻¹' S
      refine ⟨S', hS.preimage (ReferenceSourcePrefixHistoryFiltration.measurable_sourcePrefix
        control0 t.val), ?_⟩
      ext z
      change ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val
          (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 (t.val + 1) z) ∈ S ↔
        z ∈ A_before rate rewards C_star C_h t i
      rw [ReferenceSourcePrefixHistoryFiltration.sourcePrefix_sourcePrefix
        control0 t.val (t.val + 1) (by omega) z]
      have hz := congrArg (fun A : Set Source => z ∈ A) hpre
      exact Iff.of_eq hz
    have hEsm : StronglyMeasurable[F (t.val + 2)]
        (fun z : Source => if z ∈ E then (1 : ℝ) else 0) := by
      change StronglyMeasurable[F (t.val + 2)] (E.indicator fun _ : Source => (1 : ℝ))
      exact stronglyMeasurable_const.indicator hE
    have hV : StronglyMeasurable[F (t.val + 2)] V := by
      dsimp [V]
      exact ReferenceFirstLiveHandoverBoundaryFactorization.V_before_roundEnd_stronglyMeasurable
        rate rewards C_star C_h control0 i t
    change StronglyMeasurable[F (t.val + 2)] (fun z =>
      (if z ∈ E then (1 : ℝ) else 0) * V z)
    exact hEsm.mul hV
  have hafter : StronglyMeasurable[F (t.val + 2)]
      (X_after rate rewards C_star C_h t i) := by
    let E := A_after rate rewards C_star C_h t i
    let V := fun z : Source =>
      if ReferenceFirstLiveHandoverBoundaryFactorization.V_after
        rate rewards C_star C_h i t z then (1 : ℝ) else 0
    have hE : MeasurableSet[F (t.val + 2)] E := by
      change ∃ S, MeasurableSet S ∧
        ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 (t.val + 1) ⁻¹' S = E
      rcases ReferencePostReplacementCollectionHandoverFreshService.measurableSet_A_after
          rate rewards C_star C_h control0 t i with ⟨S, hS, hpre⟩
      let S' := ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val ⁻¹' S
      refine ⟨S', hS.preimage (ReferenceSourcePrefixHistoryFiltration.measurable_sourcePrefix
        control0 t.val), ?_⟩
      ext z
      change ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val
          (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 (t.val + 1) z) ∈ S ↔
        z ∈ A_after rate rewards C_star C_h t i
      rw [ReferenceSourcePrefixHistoryFiltration.sourcePrefix_sourcePrefix
        control0 t.val (t.val + 1) (by omega) z]
      have hz := congrArg (fun A : Set Source => z ∈ A) hpre
      exact Iff.of_eq hz
    have hEsm : StronglyMeasurable[F (t.val + 2)]
        (fun z : Source => if z ∈ E then (1 : ℝ) else 0) := by
      change StronglyMeasurable[F (t.val + 2)] (E.indicator fun _ : Source => (1 : ℝ))
      exact stronglyMeasurable_const.indicator hE
    have hV : StronglyMeasurable[F (t.val + 2)] V := by
      dsimp [V]
      exact ReferenceFirstLiveHandoverBoundaryFactorization.V_after_roundEnd_stronglyMeasurable
        rate rewards C_star C_h control0 i t
    change StronglyMeasurable[F (t.val + 2)] (fun z =>
      (if z ∈ E then (1 : ℝ) else 0) * V z)
    exact hEsm.mul hV
  exact hbase.add hafter

/-- On literal H support, the two actual physical service branches give the
source conditional service coefficient under the original source law. -/
public theorem phaseStart_hservice
    (t : Fin p.T) (i : Fin (p.m - 1)) :
    ∀ᵐ z ∂BootstrapPrivateRoundStreams.sourceInputLaw p,
      i ∈ literalPending rate rewards C_star C_h control0 t.val z →
        aH * gH rate rewards C_star C_h control0 t.val z ≤
          (BootstrapPrivateRoundStreams.sourceInputLaw p)[
            PhaseServiceWaiting.observation
              (XH rate rewards C_star C_h control0) i t.val |
            F (t.val + 1)] z := by
  have hcond := ReferencePostReplacementCollectionHandoverFreshService.combined_service_condExp
    rate rewards C_star C_h control0 t i
  have hcond' :
      (BootstrapPrivateRoundStreams.sourceInputLaw p)[
        PhaseServiceWaiting.observation
          (XH rate rewards C_star C_h control0) i t.val | F (t.val + 1)] =ᵐ[
            BootstrapPrivateRoundStreams.sourceInputLaw p]
        fun z => (if rawHTaskSupport rate rewards C_star C_h t i z then (1 : ℝ) else 0) *
          ReferencePostReplacementCollectionHandoverFreshService.serviceCoefficient
            rewards t := by
    simpa only [← observation_eq_physical_service rate rewards C_star C_h
      control0 t i] using hcond
  have hcoeff (z : Source) :
      aH * gH rate rewards C_star C_h control0 t.val z =
        ReferencePostReplacementCollectionHandoverFreshService.serviceCoefficient rewards t := by
    have ht : (⟨t.val, t.isLt⟩ : Fin p.T) = t := Fin.ext rfl
    rw [gH, dite_eq_left t.isLt]
    unfold ReferencePostReplacementCollectionHandoverFreshService.serviceCoefficient
    rw [← ht]
    ring
  filter_upwards [hcond'] with z hz hi
  rcases (mem_literalPending_iff rate rewards C_star C_h control0 t.val z i).mp hi with
    ⟨_ht, hs⟩
  have hraw : rawHTaskSupport rate rewards C_star C_h t i z := hs.1
  simp [hraw] at hz
  rw [hcoeff z]
  exact le_of_eq hz.symm

/-- This start is the endpoint's true source-prefix stopping time. -/
public theorem sigma_preRound_stopping :
    PhaseServiceWaiting.IsPreRoundStoppingTime F sigmaH :=
  rawHSigma_preRoundStoppingTime rate rewards C_star C_h control0

/-- The first excluded endpoint is also adapted to the original strict
source-prefix filtration. -/
public theorem theta_preRound_stopping :
    PhaseServiceWaiting.IsPreRoundStoppingTime F thetaH :=
  rawHTheta_preRoundStoppingTime rate rewards C_star C_h control0

/-- The literal source charge is integrable under the original whole-source
probability law. -/
public theorem G_H_integrable :
    Integrable (G_H rate rewards C_star C_h control0)
      (BootstrapPrivateRoundStreams.sourceInputLaw p) := by
  let P := literalPending rate rewards C_star C_h control0
  let w := gH rate rewards C_star C_h control0
  let sigma := sigmaH
  let theta := thetaH
  have hd : 0 < p.m - 1 := by
    have hm := p.two_le_m
    omega
  have hKR : 0 < (p.K : ℝ) := Nat.cast_pos.mpr (ConstructorDimensions.K_pos p)
  have hdR : 0 < ((p.m - 1 : ℕ) : ℝ) := Nat.cast_pos.mpr hd
  have ha : 0 < aH := by positivity
  have htotal := PhaseServiceWaiting.totalCharge_exp_integrable
    (BootstrapPrivateRoundStreams.sourceInputLaw p) F P sigma theta w aH ha
    (sigma_preRound_stopping rate rewards C_star C_h control0)
    (theta_preRound_stopping rate rewards C_star C_h control0)
    (fun i k hk => literalPending_mem_measurable
      rate rewards C_star C_h control0 i k hk)
    (fun k hk => gH_preRound_stronglyMeasurable
      rate rewards C_star C_h control0 k)
    (fun k hk z hne => phase_bounds rate rewards C_star C_h control0 k z hne)
    (fun k hk z => gH_bounds rate rewards C_star C_h control0 k hk z)
  change Integrable (fun z => G_H rate rewards C_star C_h control0 z)
    (BootstrapPrivateRoundStreams.sourceInputLaw p)
  have hEq : (fun z => G_H rate rewards C_star C_h control0 z) =
      PhaseServiceWaiting.totalCharge P sigma theta w p.T := by
    funext z
    exact G_H_eq_totalCharge rate rewards C_star C_h control0 z
  rw [hEq]
  exact htotal.1

/-- The literal later-H charge satisfies the conditional waiting estimate at
the actual raw H start field under the original whole-source law. -/
public theorem G_H_condExp_bound :
    (BootstrapPrivateRoundStreams.sourceInputLaw p)[
      G_H rate rewards C_star C_h control0 |
        PhaseStartConditionalWaiting.phaseStartSigmaAlgebra F sigmaH
          (sigma_preRound_stopping rate rewards C_star C_h control0)] ≤ᵐ[
            BootstrapPrivateRoundStreams.sourceInputLaw p]
      fun _ =>
        (8 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ) /
          (1 - Real.exp (-1))) *
          (2 * (AffineBatchDecoder.quota p : ℝ) +
            Real.log ((p.m - 1 : ℕ) : ℝ) + 1) := by
  let P := literalPending rate rewards C_star C_h control0
  let X := XH rate rewards C_star C_h control0
  let w := gH rate rewards C_star C_h control0
  let sigma := sigmaH
  let theta := thetaH
  have hd : 0 < p.m - 1 := by
    have hm := p.two_le_m
    omega
  have hT : 0 < p.T := ConstructorDimensions.T_pos p
  have hK : 0 < p.K := ConstructorDimensions.K_pos p
  have hq : 0 < quotaH := by
    omega
  have hdR : 0 < ((p.m - 1 : ℕ) : ℝ) := Nat.cast_pos.mpr hd
  have hKR : 0 < (p.K : ℝ) := Nat.cast_pos.mpr hK
  have ha : 0 < aH := by positivity
  have hbounds := fun z => endpoint_bounds rate rewards C_star C_h z
  have hgeneric := PhaseStartConditionalWaiting.phase_start_totalCharge_condExp_bound
    (BootstrapPrivateRoundStreams.sourceInputLaw p)
    (d := p.m - 1) (T := p.T) (K := p.K) (q := quotaH)
    hd hT hK hq F P X w sigma theta aH ha
    (sigma_preRound_stopping rate rewards C_star C_h control0)
    (theta_preRound_stopping rate rewards C_star C_h control0)
    (fun z => (hbounds z).1)
    (fun z => (hbounds z).2.2.1)
    (fun z => (hbounds z).2.2.2.2)
    (fun i k hk => literalPending_mem_measurable rate rewards C_star C_h control0 i k hk)
    (fun k hk z hne => phase_bounds rate rewards C_star C_h control0 k z hne)
    (fun s t hst ht z hs _hend =>
      literalPending_nested rate rewards C_star C_h control0 s t hst ht z hs)
    (fun k hk => gH_preRound_stronglyMeasurable rate rewards C_star C_h control0 k)
    (fun k hk z => gH_bounds rate rewards C_star C_h control0 k hk z)
    (fun i k hk => observation_roundEnd_stronglyMeasurable
      rate rewards C_star C_h control0 ⟨k, hk⟩ i)
    (fun i k hk z hi => rawH_incoming_quota_strict
      rate rewards C_star C_h control0 k hk z i hi)
    (fun i k hk => phaseStart_hservice rate rewards C_star C_h control0
      ⟨k, hk⟩ i)
  have hcharge : (fun z => G_H rate rewards C_star C_h control0 z) =
      PhaseServiceWaiting.totalCharge P sigma theta w p.T := by
    funext z
    exact G_H_eq_totalCharge rate rewards C_star C_h control0 z
  have hgeneric' :
      (BootstrapPrivateRoundStreams.sourceInputLaw p)[
        G_H rate rewards C_star C_h control0 |
          PhaseStartConditionalWaiting.phaseStartSigmaAlgebra F sigmaH
            (sigma_preRound_stopping rate rewards C_star C_h control0)] ≤ᵐ[
              BootstrapPrivateRoundStreams.sourceInputLaw p]
        fun _ => ((quotaH : ℝ) + Real.log ((p.m - 1 : ℕ) : ℝ)) /
          (PhaseServiceWaiting.kappa * aH) := by
    have hgeneric_source := hgeneric
    rw [← hcharge] at hgeneric_source
    push_cast at hgeneric_source
    simpa only [sigma, theta, w, P] using hgeneric_source
  have hqcast : (quotaH : ℝ) =
      2 * (AffineBatchDecoder.quota p : ℝ) + 1 := by
    ring
  have hkappa : 0 < 1 - Real.exp (-1) := by
    simpa only [PhaseServiceWaiting.kappa] using PhaseServiceWaiting.kappa_pos
  have hconst : ((quotaH : ℝ) + Real.log ((p.m - 1 : ℕ) : ℝ)) /
      (PhaseServiceWaiting.kappa * aH) =
      (8 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ) /
        (1 - Real.exp (-1))) *
        (2 * (AffineBatchDecoder.quota p : ℝ) +
          Real.log ((p.m - 1 : ℕ) : ℝ) + 1) := by
    rw [PhaseServiceWaiting.kappa, hqcast]
    field_simp [ne_of_gt hkappa, ne_of_gt hdR, ne_of_gt hKR]
    ring
  simpa only [hconst] using hgeneric'

/-- Localization of the literal H charge to a measurable event in the actual
raw H start field. -/
public theorem G_H_setIntegral_bound
    (B : Set Source)
    (hB : MeasurableSet[PhaseStartConditionalWaiting.phaseStartSigmaAlgebra F sigmaH
      (sigma_preRound_stopping rate rewards C_star C_h control0)] B) :
    ∫ z in B, G_H rate rewards C_star C_h control0 z ∂
        BootstrapPrivateRoundStreams.sourceInputLaw p ≤
      ((8 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ) /
        (1 - Real.exp (-1))) *
        (2 * (AffineBatchDecoder.quota p : ℝ) +
          Real.log ((p.m - 1 : ℕ) : ℝ) + 1)) *
        (BootstrapPrivateRoundStreams.sourceInputLaw p).real B := by
  let mσ := PhaseStartConditionalWaiting.phaseStartSigmaAlgebra F sigmaH
    (sigma_preRound_stopping rate rewards C_star C_h control0)
  have hmσ := PhaseStartConditionalWaiting.phaseStartSigmaAlgebra_le F sigmaH
    (sigma_preRound_stopping rate rewards C_star C_h control0)
  have hcond := G_H_condExp_bound rate rewards C_star C_h control0
  have hInt := G_H_integrable rate rewards C_star C_h control0
  have hB' : MeasurableSet[mσ] B := by simpa only [mσ] using hB
  have hcond' : (BootstrapPrivateRoundStreams.sourceInputLaw p)[
      G_H rate rewards C_star C_h control0 | mσ] ≤ᵐ[
        BootstrapPrivateRoundStreams.sourceInputLaw p]
      fun _ => (8 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ) /
        (1 - Real.exp (-1))) *
        (2 * (AffineBatchDecoder.quota p : ℝ) +
          Real.log ((p.m - 1 : ℕ) : ℝ) + 1) := by
    simpa only [mσ] using hcond
  have hbound :=
    PhaseStartConditionalWaiting.setIntegral_iff_condExp_le
      (BootstrapPrivateRoundStreams.sourceInputLaw p) mσ hmσ
      (fun z => G_H rate rewards C_star C_h control0 z)
      ((8 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ) /
        (1 - Real.exp (-1))) *
        (2 * (AffineBatchDecoder.quota p : ℝ) +
          Real.log ((p.m - 1 : ℕ) : ℝ) + 1)) hInt
  exact hbound.mpr hcond' B hB'

/-- The corresponding unconditional whole-source mean bound. -/
public theorem G_H_integral_bound :
    ∫ z, G_H rate rewards C_star C_h control0 z ∂
        BootstrapPrivateRoundStreams.sourceInputLaw p ≤
      (8 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ) /
        (1 - Real.exp (-1))) *
        (2 * (AffineBatchDecoder.quota p : ℝ) +
          Real.log ((p.m - 1 : ℕ) : ℝ) + 1) := by
  have h := G_H_setIntegral_bound rate rewards C_star C_h control0
    Set.univ (MeasurableSet.univ : MeasurableSet[PhaseStartConditionalWaiting.phaseStartSigmaAlgebra
      F sigmaH (sigma_preRound_stopping rate rewards C_star C_h control0)] Set.univ)
  simpa using h

end Bandits.Support.ReferencePostReplacementCollectionHandoverWaitingCost

end
