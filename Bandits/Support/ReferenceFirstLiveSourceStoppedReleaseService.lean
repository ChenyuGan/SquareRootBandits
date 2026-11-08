/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveSourceStoppedReleaseAdaptation
public import Bandits.Support.ReferenceFirstLiveSourceStoppedReleaseQuota
public import Bandits.Support.ReferenceFirstLiveInspectedConditionalService

import Lean.Elab.Tactic.Omega
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Whole-source stopped first-release service weights

Sources: sources/zip4/manuscript/05_binary_transport.tex:180-240,293-345;
sources/zip4/manuscript/04_slow_fast_learner.tex:140-188,256-264;
sources/zip4/manuscript/07_public_setup.tex:127-164; and
sources/zip4/manuscript/08_main_theorem.tex:29-42,85-100.

The readouts are computed from the original complete source, its whole reward
table, actual physical flags, and inspected coefficients. They make no
conditional-law or successful-trace premise. The raw observations remain
ungated outside stopped support; this module proves their predictability and
service only on the literal stopped pending set.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open scoped Classical BigOperators

namespace Bandits.Support.ReferenceFirstLiveSourceStoppedReleaseService

variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)

abbrev Source (p₀ : ConstructorDimensions.Parameters) :=
  BootstrapPrivateRoundStreams.SourceInput p₀

local notation "μ" => BootstrapPrivateRoundStreams.sourceInputLaw p
local notation "P" =>
  ReferenceFirstLiveSourceStoppedReleaseQuota.firstReleasePendingNat
    rate rewards C_star C_h
local notation "Hfield" =>
  ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0

/-- The literal stratum guard with the elapsed source offset retained as a
finite calendar coordinate and used as the physical assignment timestamp. -/
def g (i : Fin (p.m - 1)) (t : Fin p.T) (q : Fin (M p))
    (s : Fin (t.val + 1)) : Set (Source p) :=
  ReferenceFirstLiveInspectedCoefficients.guardedEvent
    rate rewards C_star C_h control0 i t q s.val
    (Nat.le_of_lt_succ s.isLt) s.val

/-- Whole-source sum of the follower's guarded assigned-arm coefficients. -/
def c (i : Fin (p.m - 1)) (t : Fin p.T) (z : Source p) : ℝ :=
  ∑ q : Fin (M p), ∑ s : Fin (t.val + 1),
    ReferenceFirstLiveInspectedCoefficients.firstLiveInspectedAssignedChi
      rate rewards C_star C_h control0 i t q s.val
      (Nat.le_of_lt_succ s.isLt) s.val z

/-- Whole-source sum of the guarded auxiliary-weighted coefficients. -/
def u (i : Fin (p.m - 1)) (t : Fin p.T) (z : Source p) : ℝ :=
  ∑ q : Fin (M p), ∑ s : Fin (t.val + 1),
    ReferenceFirstLiveInspectedCoefficients.firstLiveInspectedAuxiliaryWeightedChi
      rate rewards C_star C_h control0 i t q s.val
      (Nat.le_of_lt_succ s.isLt) s.val z

/-- The common auxiliary service weight is the maximum over actual followers. -/
def o (t : Fin p.T) (z : Source p) : ℝ :=
  Finset.univ.sup' (by
    have hm : 2 ≤ p.m := p.two_le_m
    refine ⟨⟨0, ?_⟩, Finset.mem_univ _⟩
    omega) (fun i : Fin (p.m - 1) => u rate rewards C_star C_h control0 i t z)

/-- The whole-source analytical assigned-arm coefficient on the natural
calendar. Its zero extension begins only beyond the finite physical horizon. -/
def firstReleaseAssignedChi (i : Fin (p.m - 1)) (k : ℕ) (z : Source p) : ℝ :=
  if hk : k < p.T then c rate rewards C_star C_h control0 i ⟨k, hk⟩ z else 0

/-- The whole-source analytical auxiliary-weighted coefficient on the natural
calendar. Its zero extension begins only beyond the finite physical horizon. -/
def firstReleaseAuxiliaryWeight (k : ℕ) (z : Source p) : ℝ :=
  if hk : k < p.T then o rate rewards C_star C_h control0 ⟨k, hk⟩ z else 0

private theorem incomingFirst_live_disjoint
    (code : Option (ReferenceActivePhysicalStepMeasurability.StateCode p rate)) :
    ReferenceFirstLiveInspectedGuardReadout.incomingFirst code = true →
      ReferenceFirstLiveInspectedGuardReadout.incomingLive code = true → False := by
  cases code with
  | none => simp [ReferenceFirstLiveInspectedGuardReadout.incomingFirst,
      ReferenceFirstLiveInspectedGuardReadout.incomingLive]
  | some code =>
      rcases code with ⟨tag, rest⟩
      cases tag with
      | inl first =>
          simp [ReferenceFirstLiveInspectedGuardReadout.incomingFirst,
            ReferenceFirstLiveInspectedGuardReadout.incomingLive]
      | inr tail =>
          cases tail with
          | inl live =>
              simp [ReferenceFirstLiveInspectedGuardReadout.incomingFirst,
                ReferenceFirstLiveInspectedGuardReadout.incomingLive]
          | inr other =>
              simp [ReferenceFirstLiveInspectedGuardReadout.incomingFirst,
                ReferenceFirstLiveInspectedGuardReadout.incomingLive]

/-- A source point cannot lie in two guarded strata at the same calendar time.
The conclusion includes guards for different followers. -/
theorem guard_strata_exclusive (i j : Fin (p.m - 1)) (t : Fin p.T)
    (q q' : Fin (M p)) (s s' : Fin (t.val + 1)) (z : Source p)
    (hi : z ∈ g rate rewards C_star C_h control0 i t q s)
    (hj : z ∈ g rate rewards C_star C_h control0 j t q' s') :
    q = q' ∧ s = s' := by
  have hi' := (ReferenceFirstLiveInspectedGuardReadout.inspected_guard_iff
    rate rewards C_star C_h control0 i t q s.val
    (Nat.le_of_lt_succ s.isLt) s.val z).mp hi
  have hj' := (ReferenceFirstLiveInspectedGuardReadout.inspected_guard_iff
    rate rewards C_star C_h control0 j t q' s'.val
    (Nat.le_of_lt_succ s'.isLt) s'.val z).mp hj
  rcases hi' with ⟨hqi, hfirst, hlive, _hentry, _hpending⟩
  rcases hj' with ⟨hqj, hfirst', hlive', _hentry', _hpending'⟩
  refine ⟨hqi.symm.trans hqj, ?_⟩
  apply Fin.ext
  by_contra hneq
  rcases lt_or_gt_of_ne hneq with hlt | hgt
  · let v : Fin p.T := ⟨s'.val,
      lt_of_le_of_lt (Nat.le_of_lt_succ s'.isLt) t.isLt⟩
    have hFirstAtV :
        ReferenceFirstLiveInspectedGuardReadout.incomingFirst
          (ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h
            ⟨s'.val, v.isLt⟩ z) = true := by
      simpa [v] using hfirst'
    have hLiveAtV := hlive v hlt (Nat.le_of_lt_succ s'.isLt)
    exact incomingFirst_live_disjoint rate
      (code := ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h
        ⟨s'.val, v.isLt⟩ z) hFirstAtV hLiveAtV
  · let v : Fin p.T := ⟨s.val,
      lt_of_le_of_lt (Nat.le_of_lt_succ s.isLt) t.isLt⟩
    have hFirstAtV :
        ReferenceFirstLiveInspectedGuardReadout.incomingFirst
          (ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h
            ⟨s.val, v.isLt⟩ z) = true := by
      simpa [v] using hfirst
    have hLiveAtV := hlive' v hgt (Nat.le_of_lt_succ s.isLt)
    exact incomingFirst_live_disjoint rate
      (code := ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h
        ⟨s.val, v.isLt⟩ z) hFirstAtV hLiveAtV

private theorem actual_source_prefix_incoming_first_live
    (initial : ReferenceActivePhysicalStep.State p rate) (z : Source p)
    (q : Fin (M p)) (s : ℕ) (t : Fin p.T)
    (hq : q = ActualInitializationPhysicalStep.selectedRowIndex p z)
    (hLaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate z rewards C_star C_h = some initial)
    (hStart : ReferenceCompletePhysicalHistory.physicalStart
      rate z rewards C_star C_h = s)
    (hActive : ReferenceActivePhysicalHorizon.allActiveAtStart initial s)
    (hFirst : initial.coordinator = .first)
    (hspan : s + (p.T - s) ≤ p.T)
    (hwindow : t.val - s < (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceActivePhysicalHorizon.run initial z.1.2 q rewards s
        (p.T - s) hspan hActive).records).length)
    (hs : s ≤ t.val) :
    ReferenceFirstLiveInspectedGuardReadout.incomingFirst
        (ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h
          ⟨s, by omega⟩ z) = true ∧
      (∀ v : Fin p.T, s < v.val → v.val ≤ t.val →
        ReferenceFirstLiveInspectedGuardReadout.incomingLive
          (ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h v z) = true) := by
  have hSafety := ReferenceFirstLiveCoordinatorSafety.run_first_live_coordinator_safety
    initial z.1.2 q rewards s (p.T - s) hspan hActive hFirst
  have hIncomingFirst :
      ReferenceFirstLiveInspectedGuardReadout.incomingFirst
        (ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h
          ⟨s, by omega⟩ z) = true := by
    have hrec := ReferenceSourcePrefixHistoryFiltration.actualRecord_on_launch
      rate rewards C_star C_h ⟨s, by omega⟩ z initial hLaunch (by rw [hStart])
    have hrec' : ReferenceSourcePrefixHistoryFiltration.actualRecord
        rate rewards C_star C_h ⟨s, by omega⟩ z =
        some (ReferenceAssignmentPayloadChronology.actualRunRecordAt initial z.1.2 q
          rewards s 0 (by omega) hActive) := by
      simpa [hStart, hq] using hrec
    have hstate :
        (ReferenceAssignmentPayloadChronology.actualRunRecordAt initial z.1.2 q
          rewards s 0 (by omega) hActive).input.state = initial := by
      simp [ReferenceAssignmentPayloadChronology.actualRunRecordAt,
        ReferenceActivePhysicalHorizon.roundInputAt,
        ReferenceActivePhysicalHorizon.run_zero_final]
    simp only [ReferenceSourcePrefixHistoryFiltration.incoming, hrec', Option.map_some, hstate]
    exact (ReferenceFirstLiveInspectedGuardReadout.incomingFirst_encode initial).2 hFirst
  have hIncomingLive : ∀ v : Fin p.T, s < v.val → v.val ≤ t.val →
      ReferenceFirstLiveInspectedGuardReadout.incomingLive
        (ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h v z) = true := by
    intro v hsv hvt
    let k := v.val - s
    have hkpos : 0 < k := by dsimp [k]; omega
    have hkWindow : k ≤
        (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
          (ReferenceActivePhysicalHorizon.run initial z.1.2 q rewards s
            (p.T - s) hspan hActive).records).length := by
      dsimp [k]
      exact (Nat.sub_le_sub_right hvt s).trans (Nat.le_of_lt hwindow)
    have hprefix := hSafety.2.1 k hkWindow
    obtain ⟨registers, owned, base, hlive⟩ := hprefix.2 hkpos
    have hrec := ReferenceSourcePrefixHistoryFiltration.actualRecord_on_launch
      rate rewards C_star C_h v z initial hLaunch (by rw [hStart]; omega)
    have hrec' : ReferenceSourcePrefixHistoryFiltration.actualRecord
        rate rewards C_star C_h v z =
        some (ReferenceAssignmentPayloadChronology.actualRunRecordAt initial z.1.2 q
          rewards s k (by omega) hActive) := by
      simpa [hStart, hq, k] using hrec
    have hstate :
        (ReferenceAssignmentPayloadChronology.actualRunRecordAt initial z.1.2 q
          rewards s k (by omega) hActive).input.state =
          (ReferenceActivePhysicalHorizon.run initial z.1.2 q rewards s k
            (by omega) hActive).finalState := by
      simp [ReferenceAssignmentPayloadChronology.actualRunRecordAt,
        ReferenceActivePhysicalHorizon.roundInputAt]
    simp only [ReferenceSourcePrefixHistoryFiltration.incoming, hrec', Option.map_some, hstate]
    exact (ReferenceFirstLiveInspectedGuardReadout.incomingLive_encode _).2
      ⟨registers, owned, base, hlive⟩
  exact ⟨hIncomingFirst, hIncomingLive⟩

private theorem pending_source_facts
    (i : Fin (p.m - 1)) (t : Fin p.T) (z : Source p)
    (hpending : i ∈ P t.val z) :
    (t.val + 1 ∈ ReferenceFirstLiveSourceStoppedReleaseEndpoint.actualFirstReleaseSupport
      rate rewards C_star C_h z) ∧
    (i ∈ ReferenceSourcePrefixHistoryFiltration.pending rate rewards C_star C_h
      (ReferenceFirstLiveSourceStoppedReleaseEndpoint.physicalStart rate rewards C_star C_h z)
      t z) ∧
    (t.val + 1 ∈ ReferenceFirstLiveSourceStoppedReleaseEndpoint.actualGateSupport
      rate rewards C_star C_h z) ∧
    ((ReferenceSourcePrefixHistoryFiltration.entry rate rewards C_star C_h
      (ReferenceFirstLiveSourceStoppedReleaseEndpoint.physicalStart rate rewards C_star C_h z)
      t z).map Prod.fst = some true) ∧
    (ReferenceSourcePrefixHistoryFiltration.actualLaunchBy rate rewards C_star C_h t.val z) ∧
    ((ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true) := by
  have hPendingFin :
      i ∈ ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstReleasePending
        rate rewards C_star C_h z t := by
    change i ∈ ReferenceFirstLiveSourceStoppedReleaseQuota.firstReleasePendingNat
      rate rewards C_star C_h t.val z at hpending
    rw [ReferenceFirstLiveSourceStoppedReleaseQuota.firstReleasePendingNat_fin
      rate rewards C_star C_h t z] at hpending
    exact hpending
  have hStop :
      t.val + 1 ∈ ReferenceFirstLiveSourceStoppedReleaseEndpoint.actualFirstReleaseSupport
        rate rewards C_star C_h z := by
    by_contra hnot
    simp [ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstReleasePending,
      hnot] at hPendingFin
  have hPendingActual :
      i ∈ ReferenceSourcePrefixHistoryFiltration.pending rate rewards C_star C_h
        (ReferenceFirstLiveSourceStoppedReleaseEndpoint.physicalStart rate rewards C_star C_h z)
        t z := by
    simpa [ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstReleasePending,
      hStop] using hPendingFin
  have hRawGate :
      t.val + 1 ∈ ReferenceFirstLiveSourceStoppedReleaseEndpoint.actualGateSupport
        rate rewards C_star C_h z := by
    have hmem := hStop
    change t.val + 1 ∈
      (ReferenceFirstLiveSourceStoppedReleaseEndpoint.actualGateSupport
        rate rewards C_star C_h z).filter _ at hmem
    exact (Finset.mem_filter.mp hmem).1
  have hEntryTrue :=
    (ReferenceFirstLiveSourceStoppedReleaseEndpoint.actual_gate_support_mem_iff_entry
      rate rewards C_star C_h z t).mp hRawGate
  have hIncomingSome : ∃ code,
      ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t z = some code := by
    cases hcode : ReferenceSourcePrefixHistoryFiltration.incoming
        rate rewards C_star C_h t z with
    | none => simp [ReferenceSourcePrefixHistoryFiltration.entry, hcode] at hEntryTrue
    | some code => exact ⟨code, rfl⟩
  obtain ⟨code, hcode⟩ := hIncomingSome
  have hRecordExists : ∃ r,
      ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some r := by
    cases hr : ReferenceSourcePrefixHistoryFiltration.actualRecord
        rate rewards C_star C_h t z with
    | none =>
        have hnone : ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t z = none := by
          simp [ReferenceSourcePrefixHistoryFiltration.incoming, hr]
        rw [hnone] at hcode
        cases hcode
    | some r => exact ⟨r, rfl⟩
  obtain ⟨_, hrecord⟩ := hRecordExists
  have hLaunchBy :
      ReferenceSourcePrefixHistoryFiltration.actualLaunchBy rate rewards C_star C_h t.val z := by
    by_contra hnot
    rw [ReferenceSourcePrefixHistoryFiltration.actualRecord_eq_none_of_not_launchBy
      rate rewards C_star C_h t z hnot] at hrecord
    cases hrecord
  have hCrossing := hLaunchBy.1
  have hCrossingInit :
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true := by
    simpa [ReferenceCompletePhysicalHistory.generatedBoundary,
      ReferenceCompletePhysicalHistory.generatedInput] using hCrossing
  exact ⟨hStop, hPendingActual, hRawGate, hEntryTrue, hLaunchBy, hCrossingInit⟩

private theorem pending_actual_stratum
    (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T) (z : Source p)
    (hpending : i ∈ P t.val z) :
    ∃ q : Fin (M p), ∃ s : ℕ,
      q = ActualInitializationPhysicalStep.selectedRowIndex p z ∧
      s = ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h ∧
      s ≤ t.val ∧
      (t.val + 1 ∈ ReferenceFirstLiveSourceStoppedReleaseEndpoint.actualFirstReleaseSupport
        rate rewards C_star C_h z) ∧
      (i ∈ ReferenceSourcePrefixHistoryFiltration.pending rate rewards C_star C_h
        (ReferenceFirstLiveSourceStoppedReleaseEndpoint.physicalStart rate rewards C_star C_h z)
        t z) ∧
      (t.val + 1 ∈ ReferenceFirstLiveSourceStoppedReleaseEndpoint.actualGateSupport
        rate rewards C_star C_h z) ∧
      ((ReferenceSourcePrefixHistoryFiltration.entry rate rewards C_star C_h
        (ReferenceFirstLiveSourceStoppedReleaseEndpoint.physicalStart rate rewards C_star C_h z)
        t z).map Prod.fst = some true) ∧
      ReferenceSourcePrefixHistoryFiltration.actualLaunchBy rate rewards C_star C_h t.val z ∧
      ((ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true) := by
  obtain ⟨hStop, hPendingActual, hRawGate, hEntryTrue, hLaunchBy, hCrossingInit⟩ :=
    pending_source_facts rate rewards C_star C_h i t z hpending
  let q := ActualInitializationPhysicalStep.selectedRowIndex p z
  let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  have hs : s ≤ t.val := hLaunchBy.2
  have hElapsed :
      ReferenceInitializationRun.elapsed p
        (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed =
        s := rfl
  have hzStratum : z ∈
      ReferenceTotalSourcePairCoupling.sourceStratumEvent rate rewards C_star C_h t
        (ReferenceFirstLiveRecordingSourceCylinder.stratumIndex q t s hs) := by
    change z ∈ ReferenceRetainedSourceCoupling.retainedSourceEvent
      rate rewards C_star C_h q s
    exact ⟨ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex
      p z, hCrossingInit, hElapsed⟩
  let zStratum : ReferenceTotalSourceDisintegration.SourceStratum rate rewards C_star C_h t
      (ReferenceFirstLiveRecordingSourceCylinder.stratumIndex q t s hs) := ⟨z, hzStratum⟩
  have hMaskFacts :=
    (ReferenceFirstLiveSourceStoppedReleaseAdaptation.actual_gate_current_mask
      rate rewards C_star C_h q t s hs control0 zStratum hRawGate).mp hStop
  have _hPrelaunchDecoderFalse := hMaskFacts.1
  have _hStrictPastDecoderFalse := hMaskFacts.2.1
  have _hOldOverflowFalse := hMaskFacts.2.2
  exact ⟨q, s, rfl, rfl, hs, hStop, hPendingActual, hRawGate, hEntryTrue,
    hLaunchBy, hCrossingInit⟩

private theorem pending_actual_window_context
    (t : Fin p.T) (z : Source p)
    (hLaunchBy : ReferenceSourcePrefixHistoryFiltration.actualLaunchBy
      rate rewards C_star C_h t.val z)
    (hCrossingInit :
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true)
    (hEntryTrue : (ReferenceSourcePrefixHistoryFiltration.entry rate rewards C_star C_h
      (ReferenceFirstLiveSourceStoppedReleaseEndpoint.physicalStart
        rate rewards C_star C_h z) t z).map Prod.fst = some true) :
    ∃ initial : ReferenceActivePhysicalStep.State p rate,
      ReferenceCorrectedInitializationLaunch.correctedLaunch rate z rewards C_star C_h =
        some initial ∧
      initial.coordinator = .first ∧
      ∃ hActive : ReferenceActivePhysicalHorizon.allActiveAtStart initial
          (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h),
        ∃ hspan : ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h +
            (p.T - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h) ≤ p.T,
          t.val - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h <
            (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
              (ReferenceActivePhysicalHorizon.run initial z.1.2
                (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards
                (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
                (p.T - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
                hspan hActive).records).length := by
  let q := ActualInitializationPhysicalStep.selectedRowIndex p z
  let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  have hs : s ≤ t.val := hLaunchBy.2
  have hElapsed :
      ReferenceInitializationRun.elapsed p
        (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed = s := rfl
  have hLaunch :
      ReferenceCorrectedInitializationLaunch.correctedLaunch rate z rewards C_star C_h =
        some (ReferenceLocalReleaseGateChronology.sourceSeed
          rate z rewards C_star C_h hCrossingInit) :=
    ReferenceLocalReleaseGateChronology.sourceSeed_launch
      rate z rewards C_star C_h hCrossingInit
  let initial := ReferenceLocalReleaseGateChronology.sourceSeed
    rate z rewards C_star C_h hCrossingInit
  have hCanonical :=
    ReferenceLocalReleaseGateChronology.canonical_seed_release_inputs
      rate z rewards C_star C_h hCrossingInit
  have hFirst : initial.coordinator = .first := by
    simpa [initial] using hCanonical.1
  have hActive : ReferenceActivePhysicalHorizon.allActiveAtStart initial s := by
    simpa [initial, hElapsed] using hCanonical.2.1
  have hspan : s + (p.T - s) ≤ p.T := by omega
  have hRecordAtT := ReferenceSourcePrefixHistoryFiltration.actualRecord_on_launch
    rate rewards C_star C_h t z initial hLaunch hLaunchBy.2
  have hLocalGateAtT :
      ReferenceRetainedReleasePhaseObservation.localReleaseGate rate
        (ReferenceFirstLiveSourceStoppedReleaseEndpoint.physicalStart
          rate rewards C_star C_h z) t
        (ReferenceActivePhysicalStepMeasurability.encodeState
          (ReferenceAssignmentPayloadChronology.actualRunRecordAt initial z.1.2 q
            rewards (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
            (t.val - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
            (by omega) hActive).input.state) = true := by
    simpa [ReferenceSourcePrefixHistoryFiltration.entry,
      ReferenceSourcePrefixHistoryFiltration.incoming, hRecordAtT,
      ReferenceRetainedReleasePhaseObservation.localReleaseEntry] using hEntryTrue
  have hcountPos : t.val - s < p.T - s := by omega
  let run := ReferenceLocalReleaseGateChronology.sourceRun
    rate z rewards C_star C_h hCrossingInit s (p.T - s) hElapsed hspan
  have hrecordRun := ReferenceLocalReleaseGateChronology.run_record_at
    initial z.1.2 q rewards s hActive (p.T - s) hspan
    (⟨t.val - s, hcountPos⟩ : Fin (p.T - s))
  have hrecordRun' : run.records[t.val - s]'(by
      simp [run, ReferenceLocalReleaseGateChronology.sourceRun,
        ReferenceActivePhysicalHorizon.run_record_count]
      exact hcountPos) =
      ReferenceAssignmentPayloadChronology.actualRunRecordAt initial z.1.2 q rewards s
        (t.val - s) (by omega) hActive := by
    simpa [run, ReferenceLocalReleaseGateChronology.sourceRun] using hrecordRun
  have hrunGate :
      ReferenceRetainedReleasePhaseObservation.localReleaseGate rate s t
        (ReferenceActivePhysicalStepMeasurability.encodeState
          (run.records[t.val - s]'(by
            simp [run, ReferenceLocalReleaseGateChronology.sourceRun,
              ReferenceActivePhysicalHorizon.run_record_count]
            exact hcountPos)).input.state) = true := by
    rw [hrecordRun']
    simpa [q, s, ReferenceFirstLiveSourceStoppedReleaseEndpoint.physicalStart] using
      hLocalGateAtT
  have hspanElapsed :
      ReferenceInitializationRun.elapsed p
          (ReferenceInitializationRun.output
            (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed +
        (p.T - s) ≤ p.T := by
    simpa [hElapsed] using hspan
  let actualRun := ReferenceLocalReleaseGateChronology.sourceRun
    rate z rewards C_star C_h hCrossingInit
    (ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed)
    (p.T - s) rfl hspanElapsed
  have hrunGateElapsed :
      ReferenceRetainedReleasePhaseObservation.localReleaseGate rate
        (ReferenceInitializationRun.elapsed p
          (ReferenceInitializationRun.output
            (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed) t
        (ReferenceActivePhysicalStepMeasurability.encodeState
          (actualRun.records[t.val - s]'(by
            simp [actualRun, ReferenceLocalReleaseGateChronology.sourceRun,
              ReferenceActivePhysicalHorizon.run_record_count, hElapsed]
            exact hcountPos)).input.state) = true := by
    simpa [actualRun, run, ReferenceLocalReleaseGateChronology.sourceRun,
      hElapsed, hspanElapsed, q, s] using hrunGate
  have hrecordRunElapsed : actualRun.records[t.val - s]'(by
      simp [actualRun, ReferenceLocalReleaseGateChronology.sourceRun,
        ReferenceActivePhysicalHorizon.run_record_count, hElapsed]
      exact hcountPos) =
      ReferenceAssignmentPayloadChronology.actualRunRecordAt initial z.1.2 q rewards s
        (t.val - s) (by omega) hActive := by
    simpa [actualRun, run, ReferenceLocalReleaseGateChronology.sourceRun,
      hElapsed, hspanElapsed, q, s] using hrecordRun'
  have hrecordTime :
      (actualRun.records[t.val - s]'(by
        simp [actualRun, ReferenceLocalReleaseGateChronology.sourceRun,
          ReferenceActivePhysicalHorizon.run_record_count, hElapsed]
        exact hcountPos)).input.time = t := by
    rw [hrecordRunElapsed]
    apply Fin.ext
    simp only [ReferenceAssignmentPayloadChronology.actualRunRecordAt,
      ReferenceActivePhysicalHorizon.roundInputAt]
    omega
  have hrunGateRecordTime :
      ReferenceRetainedReleasePhaseObservation.localReleaseGate rate
        (ReferenceInitializationRun.elapsed p
          (ReferenceInitializationRun.output
            (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed)
        (actualRun.records[t.val - s]'(by
          simp [actualRun, ReferenceLocalReleaseGateChronology.sourceRun,
            ReferenceActivePhysicalHorizon.run_record_count, hElapsed]
          exact hcountPos)).input.time
        (ReferenceActivePhysicalStepMeasurability.encodeState
          (actualRun.records[t.val - s]'(by
            simp [actualRun, ReferenceLocalReleaseGateChronology.sourceRun,
              ReferenceActivePhysicalHorizon.run_record_count, hElapsed]
            exact hcountPos)).input.state) = true := by
    simpa [hrecordTime] using hrunGateElapsed
  have hWindow := ReferenceFirstLiveSourceReleaseSupport.actual_first_live_gate_in_window
    (rate := rate) z rewards C_star C_h (p.T - s) hspanElapsed hCrossingInit
    (⟨t.val - s, hcountPos⟩ : Fin (p.T - s)) hrunGateRecordTime
  have hWindow' : t.val - s <
      (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (ReferenceActivePhysicalHorizon.run initial z.1.2 q rewards s
          (p.T - s) hspan hActive).records).length := by
    simpa [actualRun, run, ReferenceLocalReleaseGateChronology.sourceRun,
      hElapsed, hspanElapsed, q, s] using hWindow
  exact ⟨initial, hLaunch, hFirst, hActive, hspan, hWindow'⟩

private theorem pending_guard_exists
    (i : Fin (p.m - 1)) (t : Fin p.T) (z : Source p)
    (hpending : i ∈ P t.val z) :
    ∃ q : Fin (M p), ∃ s : Fin (t.val + 1),
      z ∈ g rate rewards C_star C_h control0 i t q s := by
  classical
  obtain ⟨_qWitness, _sWitness, _hq, _hsEq, _hWitnessBound, hStop, hPendingActual,
    hRawGate, hEntryTrue,
    hLaunchBy, hCrossingInit⟩ :=
    pending_actual_stratum rate rewards C_star C_h control0 i t z hpending
  let q := ActualInitializationPhysicalStep.selectedRowIndex p z
  let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  have hs : s ≤ t.val := hLaunchBy.2
  obtain ⟨initial, hLaunch, hFirst, hActive, hspan, hWindow'⟩ :=
    pending_actual_window_context rate rewards C_star C_h t z hLaunchBy
      hCrossingInit hEntryTrue
  have hincoming := actual_source_prefix_incoming_first_live
    rate rewards C_star C_h initial z q s t rfl hLaunch (by rfl) hActive hFirst
      hspan hWindow' hs
  have hGuard :
      z ∈ g rate rewards C_star C_h control0 i t q
        ⟨s, Nat.lt_succ_of_le hs⟩ := by
    apply (ReferenceFirstLiveInspectedGuardReadout.inspected_guard_iff
      rate rewards C_star C_h control0 i t q s hs s z).2
    exact ⟨rfl, hincoming.1, hincoming.2, hEntryTrue, hPendingActual⟩
  exact ⟨q, ⟨s, Nat.lt_succ_of_le hs⟩, hGuard⟩

/-- Every stopped pending follower has its actual unique selected-row and
elapsed-time guard on the original whole source. -/
theorem pending_guard_coverage (i : Fin (p.m - 1)) (t : Fin p.T) (z : Source p)
    (hpending : i ∈ P t.val z) :
    ∃! a : Fin (M p) × Fin (t.val + 1),
      z ∈ g rate rewards C_star C_h control0 i t a.1 a.2 := by
  obtain ⟨q, s, hg⟩ := pending_guard_exists
    rate rewards C_star C_h control0 i t z hpending
  refine ⟨(q, s), hg, ?_⟩
  intro a ha
  rcases a with ⟨q', s'⟩
  obtain ⟨hq, hs⟩ := guard_strata_exclusive
    rate rewards C_star C_h control0 i i t q q' s s' z hg ha
  exact Prod.ext hq.symm hs.symm

private theorem doubleSum_eq_of_guard
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (f : α → β → ℝ) (guard : α → β → Prop)
    (hzero : ∀ a b, ¬ guard a b → f a b = 0)
    (hexclusive : ∀ a b a' b', guard a b → guard a' b' → a = a' ∧ b = b')
    (a₀ : α) (b₀ : β) (hguard : guard a₀ b₀) :
    (∑ a : α, ∑ b : β, f a b) = f a₀ b₀ := by
  classical
  calc
    (∑ a : α, ∑ b : β, f a b) =
        ∑ a : α, if a = a₀ then ∑ b : β, f a₀ b else 0 := by
      apply Finset.sum_congr rfl
      intro a ha
      by_cases haa : a = a₀
      · subst a
        simp
      · have hz : ∀ b : β, f a b = 0 := by
          intro b
          apply hzero
          intro hg
          exact haa (hexclusive a b a₀ b₀ hg hguard).1
        have hsum : (∑ b : β, f a b) = 0 := by
          apply Finset.sum_eq_zero
          intro b hb
          exact hz b
        simp [hsum, haa]
    _ = ∑ a : α, if a = a₀ then f a₀ b₀ else 0 := by
      apply Finset.sum_congr rfl
      intro a ha
      by_cases haa : a = a₀
      · subst a
        rw [Finset.sum_eq_single_of_mem b₀ (Finset.mem_univ b₀)
          (fun b _ hne => by
            apply hzero
            intro hg
            exact hne (hexclusive a₀ b a₀ b₀ hg hguard).2)]
      · simp [haa]
    _ = f a₀ b₀ := by simp

private theorem doubleSum_zero_of_no_guard
    {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β → ℝ) (guard : α → β → Prop)
    (hzero : ∀ a b, ¬ guard a b → f a b = 0)
    (hno : ∀ a b, ¬ guard a b) :
    (∑ a : α, ∑ b : β, f a b) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro a ha
  apply Finset.sum_eq_zero
  intro b hb
  exact hzero a b (hno a b)

private theorem assignedCoefficient_zero_off_guard
    (i : Fin (p.m - 1)) (t : Fin p.T) (q : Fin (M p))
    (s : Fin (t.val + 1)) (z : Source p)
    (hnot : z ∉ g rate rewards C_star C_h control0 i t q s) :
    ReferenceFirstLiveInspectedCoefficients.firstLiveInspectedAssignedChi
      rate rewards C_star C_h control0 i t q s.val
      (Nat.le_of_lt_succ s.isLt) s.val z = 0 := by
  change z ∉ ReferenceFirstLiveInspectedCoefficients.guardedEvent
    rate rewards C_star C_h control0 i t q s.val
      (Nat.le_of_lt_succ s.isLt) s.val at hnot
  simp [ReferenceFirstLiveInspectedCoefficients.firstLiveInspectedAssignedChi,
    ReferenceFirstLiveInspectedCoefficients.firstLiveInspectedCoefficientValues,
    ReferenceFirstLiveInspectedCoefficients.zeroValues, hnot]

private theorem weightedCoefficient_zero_off_guard
    (i : Fin (p.m - 1)) (t : Fin p.T) (q : Fin (M p))
    (s : Fin (t.val + 1)) (z : Source p)
    (hnot : z ∉ g rate rewards C_star C_h control0 i t q s) :
    ReferenceFirstLiveInspectedCoefficients.firstLiveInspectedAuxiliaryWeightedChi
      rate rewards C_star C_h control0 i t q s.val
      (Nat.le_of_lt_succ s.isLt) s.val z = 0 := by
  change z ∉ ReferenceFirstLiveInspectedCoefficients.guardedEvent
    rate rewards C_star C_h control0 i t q s.val
      (Nat.le_of_lt_succ s.isLt) s.val at hnot
  simp [ReferenceFirstLiveInspectedCoefficients.firstLiveInspectedAuxiliaryWeightedChi,
    ReferenceFirstLiveInspectedCoefficients.firstLiveInspectedCoefficientValues,
    ReferenceFirstLiveInspectedCoefficients.zeroValues, hnot]

private theorem assignedSum_eq_of_guard
    (i : Fin (p.m - 1)) (t : Fin p.T) (z : Source p)
    (q : Fin (M p)) (s : Fin (t.val + 1))
    (hguard : z ∈ g rate rewards C_star C_h control0 i t q s) :
    c rate rewards C_star C_h control0 i t z =
      ReferenceFirstLiveInspectedCoefficients.firstLiveInspectedAssignedChi
        rate rewards C_star C_h control0 i t q s.val
          (Nat.le_of_lt_succ s.isLt) s.val z := by
  unfold c
  apply doubleSum_eq_of_guard
    (f := fun q s =>
      ReferenceFirstLiveInspectedCoefficients.firstLiveInspectedAssignedChi
        rate rewards C_star C_h control0 i t q s.val
          (Nat.le_of_lt_succ s.isLt) s.val z)
    (guard := fun q s => z ∈ g rate rewards C_star C_h control0 i t q s)
  · intro q s hnot
    exact assignedCoefficient_zero_off_guard rate rewards C_star C_h control0 i t q s z hnot
  · intro q s q' s' hq hs
    exact (guard_strata_exclusive rate rewards C_star C_h control0 i i t
      q q' s s' z hq hs)
  · exact hguard

private theorem weightedSum_eq_of_guard
    (i : Fin (p.m - 1)) (t : Fin p.T) (z : Source p)
    (q : Fin (M p)) (s : Fin (t.val + 1))
    (hguard : z ∈ g rate rewards C_star C_h control0 i t q s) :
    u rate rewards C_star C_h control0 i t z =
      ReferenceFirstLiveInspectedCoefficients.firstLiveInspectedAuxiliaryWeightedChi
        rate rewards C_star C_h control0 i t q s.val
          (Nat.le_of_lt_succ s.isLt) s.val z := by
  unfold u
  apply doubleSum_eq_of_guard
    (f := fun q s =>
      ReferenceFirstLiveInspectedCoefficients.firstLiveInspectedAuxiliaryWeightedChi
        rate rewards C_star C_h control0 i t q s.val
          (Nat.le_of_lt_succ s.isLt) s.val z)
    (guard := fun q s => z ∈ g rate rewards C_star C_h control0 i t q s)
  · intro q s hnot
    exact weightedCoefficient_zero_off_guard rate rewards C_star C_h control0 i t q s z hnot
  · intro q s q' s' hq hs
    exact (guard_strata_exclusive rate rewards C_star C_h control0 i i t
      q q' s s' z hq hs)
  · exact hguard

private theorem assignedSum_zero_of_no_guard
    (i : Fin (p.m - 1)) (t : Fin p.T) (z : Source p)
    (hno : ∀ q : Fin (M p), ∀ s : Fin (t.val + 1),
      z ∉ g rate rewards C_star C_h control0 i t q s) :
    c rate rewards C_star C_h control0 i t z = 0 := by
  unfold c
  apply doubleSum_zero_of_no_guard
    (f := fun q s =>
      ReferenceFirstLiveInspectedCoefficients.firstLiveInspectedAssignedChi
        rate rewards C_star C_h control0 i t q s.val
          (Nat.le_of_lt_succ s.isLt) s.val z)
    (guard := fun q s => z ∈ g rate rewards C_star C_h control0 i t q s)
  · intro q s hnot
    exact assignedCoefficient_zero_off_guard rate rewards C_star C_h control0 i t q s z hnot
  · exact hno

private theorem weightedSum_zero_of_no_guard
    (i : Fin (p.m - 1)) (t : Fin p.T) (z : Source p)
    (hno : ∀ q : Fin (M p), ∀ s : Fin (t.val + 1),
      z ∉ g rate rewards C_star C_h control0 i t q s) :
    u rate rewards C_star C_h control0 i t z = 0 := by
  unfold u
  apply doubleSum_zero_of_no_guard
    (f := fun q s =>
      ReferenceFirstLiveInspectedCoefficients.firstLiveInspectedAuxiliaryWeightedChi
        rate rewards C_star C_h control0 i t q s.val
          (Nat.le_of_lt_succ s.isLt) s.val z)
    (guard := fun q s => z ∈ g rate rewards C_star C_h control0 i t q s)
  · intro q s hnot
    exact weightedCoefficient_zero_off_guard rate rewards C_star C_h control0 i t q s z hnot
  · exact hno

private theorem inspectedCoefficient_bounds
    (i : Fin (p.m - 1)) (t : Fin p.T) (q : Fin (M p))
    (s : Fin (t.val + 1)) (z : Source p) :
    (0 ≤ ReferenceFirstLiveInspectedCoefficients.firstLiveInspectedAssignedChi
        rate rewards C_star C_h control0 i t q s.val
          (Nat.le_of_lt_succ s.isLt) s.val z ∧
      ReferenceFirstLiveInspectedCoefficients.firstLiveInspectedAssignedChi
        rate rewards C_star C_h control0 i t q s.val
          (Nat.le_of_lt_succ s.isLt) s.val z ≤ 1) ∧
    (0 ≤ ReferenceFirstLiveInspectedCoefficients.firstLiveInspectedAuxiliaryWeightedChi
        rate rewards C_star C_h control0 i t q s.val
          (Nat.le_of_lt_succ s.isLt) s.val z ∧
      ReferenceFirstLiveInspectedCoefficients.firstLiveInspectedAuxiliaryWeightedChi
        rate rewards C_star C_h control0 i t q s.val
          (Nat.le_of_lt_succ s.isLt) s.val z ≤ 1) := by
  rcases ReferenceFirstLiveInspectedCoefficients.firstLiveInspectedCoefficientValues_bounds
      rate rewards C_star C_h control0 i t q s.val
        (Nat.le_of_lt_succ s.isLt) s.val z with
    ⟨_, _, _, _, _, _, hA0, hA1, hW0, hW1⟩
  exact ⟨⟨hA0, hA1⟩, ⟨hW0, hW1⟩⟩

private theorem assignedSum_bounds
    (i : Fin (p.m - 1)) (t : Fin p.T) (z : Source p) :
    0 ≤ c rate rewards C_star C_h control0 i t z ∧
      c rate rewards C_star C_h control0 i t z ≤ 1 := by
  by_cases hsome : ∃ q : Fin (M p), ∃ s : Fin (t.val + 1),
      z ∈ g rate rewards C_star C_h control0 i t q s
  · obtain ⟨q, s, hg⟩ := hsome
    rw [assignedSum_eq_of_guard rate rewards C_star C_h control0 i t z q s hg]
    exact (inspectedCoefficient_bounds rate rewards C_star C_h control0 i t q s z).1
  · have hno : ∀ q : Fin (M p), ∀ s : Fin (t.val + 1),
        z ∉ g rate rewards C_star C_h control0 i t q s := by
      intro q s hg
      exact hsome ⟨q, s, hg⟩
    rw [assignedSum_zero_of_no_guard rate rewards C_star C_h control0 i t z hno]
    norm_num

private theorem weightedSum_bounds
    (i : Fin (p.m - 1)) (t : Fin p.T) (z : Source p) :
    0 ≤ u rate rewards C_star C_h control0 i t z ∧
      u rate rewards C_star C_h control0 i t z ≤ 1 := by
  by_cases hsome : ∃ q : Fin (M p), ∃ s : Fin (t.val + 1),
      z ∈ g rate rewards C_star C_h control0 i t q s
  · obtain ⟨q, s, hg⟩ := hsome
    rw [weightedSum_eq_of_guard rate rewards C_star C_h control0 i t z q s hg]
    exact (inspectedCoefficient_bounds rate rewards C_star C_h control0 i t q s z).2
  · have hno : ∀ q : Fin (M p), ∀ s : Fin (t.val + 1),
        z ∉ g rate rewards C_star C_h control0 i t q s := by
      intro q s hg
      exact hsome ⟨q, s, hg⟩
    rw [weightedSum_zero_of_no_guard rate rewards C_star C_h control0 i t z hno]
    norm_num

/-- The finite assigned coefficient is strongly measurable on the stopped
pre-choice source field, by lifting C's inspected-field measurability through
the established inclusion. -/
theorem assignedChi_predictable (i : Fin (p.m - 1)) (k : ℕ) (hk : k < p.T) :
    StronglyMeasurable[Hfield (k + 1)]
      (firstReleaseAssignedChi rate rewards C_star C_h control0 i k) := by
  classical
  let t : Fin p.T := ⟨k, hk⟩
  have hfield := ReferenceSourceOwnHistoryContainment.inspectedHistorySpace_le_sourcePrefixFiltration
    rate rewards C_star C_h control0 k (Nat.le_of_lt hk)
  have hterm : ∀ q : Fin (M p), ∀ s : Fin (t.val + 1),
      StronglyMeasurable[Hfield (k + 1)]
        (fun z => ReferenceFirstLiveInspectedCoefficients.firstLiveInspectedAssignedChi
          rate rewards C_star C_h control0 i t q s.val
            (Nat.le_of_lt_succ s.isLt) s.val z) := by
    intro q s
    have hm := ReferenceFirstLiveInspectedCoefficients.firstLiveInspectedAssignedChi_measurable_in_inspectedField
      rate rewards C_star C_h control0 i t q s.val
        (Nat.le_of_lt_succ s.isLt) s.val
    exact hm.stronglyMeasurable.mono hfield
  have hinner : ∀ q : Fin (M p),
      StronglyMeasurable[Hfield (k + 1)]
        (fun z => ∑ s : Fin (t.val + 1),
          ReferenceFirstLiveInspectedCoefficients.firstLiveInspectedAssignedChi
            rate rewards C_star C_h control0 i t q s.val
              (Nat.le_of_lt_succ s.isLt) s.val z) := by
    intro q
    exact Finset.stronglyMeasurable_fun_sum Finset.univ
      (fun s _ => hterm q s)
  have hsum : StronglyMeasurable[Hfield (k + 1)]
      (fun z => ∑ q : Fin (M p), ∑ s : Fin (t.val + 1),
        ReferenceFirstLiveInspectedCoefficients.firstLiveInspectedAssignedChi
          rate rewards C_star C_h control0 i t q s.val
            (Nat.le_of_lt_succ s.isLt) s.val z) :=
    Finset.stronglyMeasurable_fun_sum Finset.univ (fun q _ => hinner q)
  have hreadout : firstReleaseAssignedChi rate rewards C_star C_h control0 i k =
      (fun z => ∑ q : Fin (M p), ∑ s : Fin (t.val + 1),
        ReferenceFirstLiveInspectedCoefficients.firstLiveInspectedAssignedChi
          rate rewards C_star C_h control0 i t q s.val
            (Nat.le_of_lt_succ s.isLt) s.val z) := by
    funext z
    simp [firstReleaseAssignedChi, c, t, hk]
  rw [hreadout]
  exact hsum

/-- The common finite maximum of auxiliary coefficients is strongly measurable
on the stopped pre-choice source field. -/
theorem auxiliaryWeight_predictable (k : ℕ) (hk : k < p.T) :
    StronglyMeasurable[Hfield (k + 1)]
      (firstReleaseAuxiliaryWeight rate rewards C_star C_h control0 k) := by
  classical
  let t : Fin p.T := ⟨k, hk⟩
  have hfield := ReferenceSourceOwnHistoryContainment.inspectedHistorySpace_le_sourcePrefixFiltration
    rate rewards C_star C_h control0 k (Nat.le_of_lt hk)
  have hterm : ∀ i : Fin (p.m - 1), ∀ q : Fin (M p),
      ∀ s : Fin (t.val + 1),
      StronglyMeasurable[Hfield (k + 1)]
        (fun z => ReferenceFirstLiveInspectedCoefficients.firstLiveInspectedAuxiliaryWeightedChi
          rate rewards C_star C_h control0 i t q s.val
            (Nat.le_of_lt_succ s.isLt) s.val z) := by
    intro i q s
    have hm := ReferenceFirstLiveInspectedCoefficients.firstLiveInspectedAuxiliaryWeightedChi_measurable_in_inspectedField
      rate rewards C_star C_h control0 i t q s.val
        (Nat.le_of_lt_succ s.isLt) s.val
    exact hm.stronglyMeasurable.mono hfield
  have hu : ∀ i : Fin (p.m - 1),
      StronglyMeasurable[Hfield (k + 1)] (fun z => u rate rewards C_star C_h control0 i t z) := by
    intro i
    have hinner : ∀ q : Fin (M p),
        StronglyMeasurable[Hfield (k + 1)]
          (fun z => ∑ s : Fin (t.val + 1),
            ReferenceFirstLiveInspectedCoefficients.firstLiveInspectedAuxiliaryWeightedChi
              rate rewards C_star C_h control0 i t q s.val
                (Nat.le_of_lt_succ s.isLt) s.val z) := by
      intro q
      exact Finset.stronglyMeasurable_fun_sum Finset.univ
        (fun s _ => hterm i q s)
    have hsum : StronglyMeasurable[Hfield (k + 1)]
        (fun z => ∑ q : Fin (M p), ∑ s : Fin (t.val + 1),
          ReferenceFirstLiveInspectedCoefficients.firstLiveInspectedAuxiliaryWeightedChi
            rate rewards C_star C_h control0 i t q s.val
              (Nat.le_of_lt_succ s.isLt) s.val z) :=
      Finset.stronglyMeasurable_fun_sum Finset.univ (fun q _ => hinner q)
    simpa [u] using hsum
  have hne : (Finset.univ : Finset (Fin (p.m - 1))).Nonempty := by
    have hm : 2 ≤ p.m := p.two_le_m
    refine ⟨⟨0, ?_⟩, Finset.mem_univ _⟩
    omega
  have hmeas : Measurable[Hfield (k + 1)] (fun z => o rate rewards C_star C_h control0 t z) := by
    let inst : MeasurableSpace (Source p) := Hfield (k + 1)
    have hsup : Measurable[Hfield (k + 1)]
        ((Finset.univ : Finset (Fin (p.m - 1))).sup' hne
          (fun i z => u rate rewards C_star C_h control0 i t z)) :=
      Finset.measurable_sup' hne (fun i hi => (hu i).measurable)
    have hreadout : (fun z => o rate rewards C_star C_h control0 t z) =
        (Finset.univ : Finset (Fin (p.m - 1))).sup' hne
          (fun i z => u rate rewards C_star C_h control0 i t z) := by
      funext z
      simp [o]
    rw [hreadout]
    exact hsup
  have hstrong := hmeas.stronglyMeasurable
  have hreadout : firstReleaseAuxiliaryWeight rate rewards C_star C_h control0 k =
      (fun z => o rate rewards C_star C_h control0 t z) := by
    funext z
    simp [firstReleaseAuxiliaryWeight, o, t, hk]
  rw [hreadout]
  exact hstrong

/-- Pointwise bounds for the assigned readout, including its zero extension
past the original horizon. -/
theorem assignedChi_bounds (i : Fin (p.m - 1)) (k : ℕ) (z : Source p) :
    0 ≤ firstReleaseAssignedChi rate rewards C_star C_h control0 i k z ∧
      firstReleaseAssignedChi rate rewards C_star C_h control0 i k z ≤ 1 := by
  by_cases hk : k < p.T
  · simpa [firstReleaseAssignedChi, hk] using
      assignedSum_bounds rate rewards C_star C_h control0 i ⟨k, hk⟩ z
  · simp [firstReleaseAssignedChi, hk]

/-- Pointwise bounds for the shared auxiliary readout, including its zero
extension past the original horizon. -/
theorem auxiliaryWeight_bounds (k : ℕ) (z : Source p) :
    0 ≤ firstReleaseAuxiliaryWeight rate rewards C_star C_h control0 k z ∧
      firstReleaseAuxiliaryWeight rate rewards C_star C_h control0 k z ≤ 1 := by
  by_cases hk : k < p.T
  · have hne : (Finset.univ : Finset (Fin (p.m - 1))).Nonempty := by
      have hm : 2 ≤ p.m := p.two_le_m
      refine ⟨⟨0, ?_⟩, Finset.mem_univ _⟩
      omega
    simp only [firstReleaseAuxiliaryWeight, dite_eq_left hk]
    have hU : ∀ i : Fin (p.m - 1),
        0 ≤ u rate rewards C_star C_h control0 i ⟨k, hk⟩ z ∧
          u rate rewards C_star C_h control0 i ⟨k, hk⟩ z ≤ 1 := by
      intro i
      exact weightedSum_bounds rate rewards C_star C_h control0 i ⟨k, hk⟩ z
    constructor
    · have hi := hne.choose
      have hmem : u rate rewards C_star C_h control0 hi ⟨k, hk⟩ z ≤
          o rate rewards C_star C_h control0 ⟨k, hk⟩ z := by
        exact Finset.le_sup' (f := fun i : Fin (p.m - 1) =>
          u rate rewards C_star C_h control0 i ⟨k, hk⟩ z) (Finset.mem_univ hi)
      exact (hU hi).1.trans hmem
    · apply Finset.sup'_le hne
      intro i hi
      exact (hU i).2
  · simp [firstReleaseAuxiliaryWeight, hk]

/-- At a stopped pending follower, the common maximum equals this follower's
coefficient and the canonical coefficient in its unique actual stratum. -/
theorem auxiliaryWeight_eq_at_pending (i : Fin (p.m - 1)) (t : Fin p.T)
    (z : Source p) (hpending : i ∈ P t.val z) :
    ∃ q : Fin (M p), ∃ s : Fin (t.val + 1),
      z ∈ g rate rewards C_star C_h control0 i t q s ∧
      o rate rewards C_star C_h control0 t z = u rate rewards C_star C_h control0 i t z ∧
      u rate rewards C_star C_h control0 i t z =
        ReferenceFirstLiveInspectedCoefficients.firstLiveInspectedAuxiliaryWeightedChi
          rate rewards C_star C_h control0 i t q s.val
            (Nat.le_of_lt_succ s.isLt) s.val z := by
  classical
  obtain ⟨a, hga, _hunique⟩ := pending_guard_coverage
    rate rewards C_star C_h control0 i t z hpending
  rcases a with ⟨q, s⟩
  have hiSum := weightedSum_eq_of_guard rate rewards C_star C_h control0 i t z q s hga
  have hle : ∀ j : Fin (p.m - 1),
      u rate rewards C_star C_h control0 j t z ≤ u rate rewards C_star C_h control0 i t z := by
    intro j
    by_cases hsome : ∃ q' : Fin (M p), ∃ s' : Fin (t.val + 1),
        z ∈ g rate rewards C_star C_h control0 j t q' s'
    · obtain ⟨q', s', hgj⟩ := hsome
      obtain ⟨hq, hs⟩ := guard_strata_exclusive
        rate rewards C_star C_h control0 i j t q q' s s' z hga hgj
      have hjSum := weightedSum_eq_of_guard rate rewards C_star C_h control0 j t z q' s' hgj
      change z ∈ ReferenceFirstLiveInspectedCoefficients.guardedEvent
        rate rewards C_star C_h control0 i t q s.val
          (Nat.le_of_lt_succ s.isLt) s.val at hga
      change z ∈ ReferenceFirstLiveInspectedCoefficients.guardedEvent
        rate rewards C_star C_h control0 j t q' s'.val
          (Nat.le_of_lt_succ s'.isLt) s'.val at hgj
      have hq' := hq
      have hs' := hs
      rw [← hq', ← hs'] at hgj
      have hoverlap :=
        ReferenceFirstLiveInspectedCoefficients.firstLiveInspectedAuxiliaryWeightedChi_eq_of_overlapping_guarded_branches
          rate rewards C_star C_h control0 i j t q s.val
            (Nat.le_of_lt_succ s.isLt) s.val z hga hgj
      rw [← hq', ← hs'] at hjSum
      have hEqual : u rate rewards C_star C_h control0 j t z =
          u rate rewards C_star C_h control0 i t z := by
        rw [hjSum, hiSum]
        exact hoverlap.symm
      exact le_of_eq hEqual
    · have hno : ∀ q' : Fin (M p), ∀ s' : Fin (t.val + 1),
          z ∉ g rate rewards C_star C_h control0 j t q' s' := by
        intro q' s' hgj
        exact hsome ⟨q', s', hgj⟩
      rw [weightedSum_zero_of_no_guard rate rewards C_star C_h control0 j t z hno]
      exact (weightedSum_bounds rate rewards C_star C_h control0 i t z).1
  have hsup : o rate rewards C_star C_h control0 t z ≤
      u rate rewards C_star C_h control0 i t z := by
    apply Finset.sup'_le
    intro j hj
    exact hle j
  have hleSup : u rate rewards C_star C_h control0 i t z ≤
      o rate rewards C_star C_h control0 t z :=
    Finset.le_sup' (f := fun j : Fin (p.m - 1) =>
      u rate rewards C_star C_h control0 j t z) (Finset.mem_univ i)
  exact ⟨q, s, hga, le_antisymm hsup hleSup, hiSum⟩

/-- The natural assigned weight agrees with the finite calendar readout. -/
theorem assignedChi_fin (i : Fin (p.m - 1)) (t : Fin p.T) (z : Source p) :
    firstReleaseAssignedChi rate rewards C_star C_h control0 i t.val z =
      c rate rewards C_star C_h control0 i t z := by
  simp [firstReleaseAssignedChi, t.isLt]

/-- The natural auxiliary weight agrees with the finite calendar readout. -/
theorem auxiliaryWeight_fin (t : Fin p.T) (z : Source p) :
    firstReleaseAuxiliaryWeight rate rewards C_star C_h control0 t.val z =
      o rate rewards C_star C_h control0 t z := by
  simp [firstReleaseAuxiliaryWeight, t.isLt]

/-- The analytical assigned weight is absent at and beyond the horizon. -/
theorem assignedChi_absent (i : Fin (p.m - 1)) (k : ℕ) (z : Source p)
    (hk : p.T ≤ k) : firstReleaseAssignedChi rate rewards C_star C_h control0 i k z = 0 := by
  simp [firstReleaseAssignedChi, Nat.not_lt.mpr hk]

/-- The analytical auxiliary weight is absent at and beyond the horizon. -/
theorem auxiliaryWeight_absent (k : ℕ) (z : Source p) (hk : p.T ≤ k) :
    firstReleaseAuxiliaryWeight rate rewards C_star C_h control0 k z = 0 := by
  simp [firstReleaseAuxiliaryWeight, Nat.not_lt.mpr hk]

private theorem assignedSection_eq_at_pending
    (i : Fin (p.m - 1)) (t : Fin p.T) (z : Source p)
    (hpending : i ∈ P t.val z) :
    c rate rewards C_star C_h control0 i t z / (2 * (p.K : ℝ)) =
      ReferenceSourcePhysicalFlagConditionalLaw.actualDataControlSection
        rate rewards C_star C_h control0 i t z := by
  obtain ⟨a, hga, _hunique⟩ := pending_guard_coverage
    rate rewards C_star C_h control0 i t z hpending
  rcases a with ⟨q, s⟩
  have hg := hga
  have hsum := assignedSum_eq_of_guard rate rewards C_star C_h control0 i t z q s hg
  have hdata :=
    ReferenceFirstLiveInspectedCoefficients.firstLiveInspectedDataCoefficient_eq_guarded_actualDataControlSection
      rate rewards C_star C_h control0 i t q s.val
        (Nat.le_of_lt_succ s.isLt) s.val z
  change z ∈ ReferenceFirstLiveInspectedCoefficients.guardedEvent
    rate rewards C_star C_h control0 i t q s.val
      (Nat.le_of_lt_succ s.isLt) s.val at hg
  rw [Set.indicator_of_mem hg] at hdata
  have hdataAssigned :
      ReferenceFirstLiveInspectedCoefficients.firstLiveInspectedDataCoefficient
          rate rewards C_star C_h control0 i t q s.val
            (Nat.le_of_lt_succ s.isLt) s.val z =
        ReferenceFirstLiveInspectedCoefficients.firstLiveInspectedAssignedChi
          rate rewards C_star C_h control0 i t q s.val
            (Nat.le_of_lt_succ s.isLt) s.val z / (2 * (p.K : ℝ)) := by
    simp [ReferenceFirstLiveInspectedCoefficients.firstLiveInspectedDataCoefficient,
      ReferenceFirstLiveInspectedCoefficients.firstLiveInspectedAssignedChi,
      ReferenceFirstLiveInspectedCoefficients.firstLiveInspectedCoefficientValues, hg]
  calc
    c rate rewards C_star C_h control0 i t z / (2 * (p.K : ℝ)) =
        ReferenceFirstLiveInspectedCoefficients.firstLiveInspectedAssignedChi
          rate rewards C_star C_h control0 i t q s.val
            (Nat.le_of_lt_succ s.isLt) s.val z / (2 * (p.K : ℝ)) := by rw [hsum]
    _ = ReferenceFirstLiveInspectedCoefficients.firstLiveInspectedDataCoefficient
          rate rewards C_star C_h control0 i t q s.val
            (Nat.le_of_lt_succ s.isLt) s.val z := hdataAssigned.symm
    _ = ReferenceSourcePhysicalFlagConditionalLaw.actualDataControlSection
          rate rewards C_star C_h control0 i t z := hdata

private theorem auxiliarySection_lower_at_pending
    (i : Fin (p.m - 1)) (t : Fin p.T) (z : Source p)
    (hpending : i ∈ P t.val z) :
    o rate rewards C_star C_h control0 t z /
        (12 * (p.m - 1 : ℝ) * (p.K : ℝ)) ≤
      ReferenceSourcePhysicalFlagConditionalLaw.actualUpControlSection
        rate rewards C_star C_h control0 i t z := by
  obtain ⟨q, s, hg, hmax, hcanonical⟩ :=
    auxiliaryWeight_eq_at_pending rate rewards C_star C_h control0 i t z hpending
  have hbounds :=
    ReferenceFirstLiveInspectedConditionalService.firstLiveInspected_auxiliaryWeightedChi_bounds
      rate rewards C_star C_h control0 i t q s.val
        (Nat.le_of_lt_succ s.isLt) s.val z
  have hlower :=
    ReferenceFirstLiveInspectedCoefficients.firstLiveInspectedUpCoefficient_ge_guarded_auxiliary_lower_bound
      rate rewards C_star C_h control0 i t q s.val
        (Nat.le_of_lt_succ s.isLt) s.val z
  have hup :=
    ReferenceFirstLiveInspectedCoefficients.firstLiveInspectedUpCoefficient_eq_guarded_actualUpControlSection
      rate rewards C_star C_h control0 i t q s.val
        (Nat.le_of_lt_succ s.isLt) s.val z
  change z ∈ ReferenceFirstLiveInspectedCoefficients.guardedEvent
    rate rewards C_star C_h control0 i t q s.val
      (Nat.le_of_lt_succ s.isLt) s.val at hg
  rw [Set.indicator_of_mem hg] at hup
  have hm : 2 ≤ p.m := p.two_le_m
  have hmR : (2 : ℝ) ≤ (p.m : ℝ) := by exact_mod_cast hm
  have hmnR : 0 < (p.m : ℝ) - 1 := by linarith
  have hden : 0 ≤ 12 * (p.m - 1 : ℝ) * (p.K : ℝ) := by
    have hKR : 0 < (p.K : ℝ) := by
      exact_mod_cast Bandits.Support.ConstructorDimensions.K_pos p
    positivity
  have hdiv := div_le_div_of_nonneg_right hbounds.2 hden
  calc
    o rate rewards C_star C_h control0 t z /
        (12 * (p.m - 1 : ℝ) * (p.K : ℝ)) =
      ReferenceFirstLiveInspectedCoefficients.firstLiveInspectedAuxiliaryWeightedChi
        rate rewards C_star C_h control0 i t q s.val
          (Nat.le_of_lt_succ s.isLt) s.val z /
            (12 * (p.m - 1 : ℝ) * (p.K : ℝ)) := by rw [hmax, hcanonical]
    _ ≤ ReferenceFirstLiveInspectedCoefficients.firstLiveInspectedAuxiliaryChi
          rate rewards C_star C_h control0 i t q s.val
            (Nat.le_of_lt_succ s.isLt) s.val z /
              (12 * (p.m - 1 : ℝ) * (p.K : ℝ)) := hdiv
    _ ≤ ReferenceFirstLiveInspectedCoefficients.firstLiveInspectedUpCoefficient
          rate rewards C_star C_h control0 i t q s.val
            (Nat.le_of_lt_succ s.isLt) s.val z := hlower
    _ = ReferenceSourcePhysicalFlagConditionalLaw.actualUpControlSection
          rate rewards C_star C_h control0 i t z := hup

/-- On one source-null set, every stopped pending follower has the actual DATA
and UP conditional service means under its source-prefix pre-choice field. -/
theorem actual_service_means :
    ∀ᵐ z ∂μ, ∀ (i : Fin (p.m - 1)) (t : Fin p.T),
      i ∈ P t.val z →
        (μ[PhaseServiceWaiting.observation
            (ReferenceFirstLiveSourceStoppedReleaseQuota.firstReleaseData
              rate rewards C_star C_h) i t.val | Hfield (t.val + 1)] z =
          c rate rewards C_star C_h control0 i t z / (2 * (p.K : ℝ))) ∧
        (o rate rewards C_star C_h control0 t z /
            (12 * (p.m - 1 : ℝ) * (p.K : ℝ)) ≤
          μ[PhaseServiceWaiting.observation
            (ReferenceFirstLiveSourceStoppedReleaseQuota.firstReleaseUp
              rate rewards C_star C_h) i t.val | Hfield (t.val + 1)] z) := by
  apply ae_all_iff.mpr
  intro i
  apply ae_all_iff.mpr
  intro t
  have hdataCE :=
    ReferenceSourcePhysicalFlagConditionalLaw.actual_data_condExp
      rate rewards C_star C_h control0 i t
  have hupCE :=
    ReferenceSourcePhysicalFlagConditionalLaw.actual_up_condExp
      rate rewards C_star C_h control0 i t
  have hdataObservation :
      μ[PhaseServiceWaiting.observation
          (ReferenceFirstLiveSourceStoppedReleaseQuota.firstReleaseData
            rate rewards C_star C_h) i t.val | Hfield (t.val + 1)] =ᵐ[μ]
        ReferenceSourcePhysicalFlagConditionalLaw.actualDataControlSection
          rate rewards C_star C_h control0 i t := by
    have hobs : (fun source : Source p => PhaseServiceWaiting.observation
        (ReferenceFirstLiveSourceStoppedReleaseQuota.firstReleaseData
          rate rewards C_star C_h) i t.val source) =
        (fun source => if ReferenceSourcePrefixHistoryFiltration.actualData
          rate rewards C_star C_h i t source = true then 1 else 0) := by
      funext source
      simpa [PhaseServiceWaiting.observation] using
        congrArg (fun b : Bool => if b then (1 : ℝ) else 0)
          (ReferenceFirstLiveSourceStoppedReleaseQuota.firstReleaseData_fin
            rate rewards C_star C_h i t source)
    have hcond := congrArg (fun f : Source p → ℝ => μ[f | Hfield (t.val + 1)]) hobs
    rw [hcond]
    exact hdataCE
  have hupObservation :
      μ[PhaseServiceWaiting.observation
          (ReferenceFirstLiveSourceStoppedReleaseQuota.firstReleaseUp
            rate rewards C_star C_h) i t.val | Hfield (t.val + 1)] =ᵐ[μ]
        ReferenceSourcePhysicalFlagConditionalLaw.actualUpControlSection
          rate rewards C_star C_h control0 i t := by
    have hobs : (fun source : Source p => PhaseServiceWaiting.observation
        (ReferenceFirstLiveSourceStoppedReleaseQuota.firstReleaseUp
          rate rewards C_star C_h) i t.val source) =
        (fun source => if ReferenceSourcePrefixHistoryFiltration.actualUp
          rate rewards C_star C_h i t source = true then 1 else 0) := by
      funext source
      simpa [PhaseServiceWaiting.observation] using
        congrArg (fun b : Bool => if b then (1 : ℝ) else 0)
          (ReferenceFirstLiveSourceStoppedReleaseQuota.firstReleaseUp_fin
            rate rewards C_star C_h i t source)
    have hcond := congrArg (fun f : Source p → ℝ => μ[f | Hfield (t.val + 1)]) hobs
    rw [hcond]
    exact hupCE
  have hdataPending : ∀ᵐ z ∂μ,
      i ∈ P t.val z →
        μ[PhaseServiceWaiting.observation
            (ReferenceFirstLiveSourceStoppedReleaseQuota.firstReleaseData
              rate rewards C_star C_h) i t.val | Hfield (t.val + 1)] z =
          c rate rewards C_star C_h control0 i t z / (2 * (p.K : ℝ)) := by
    filter_upwards [hdataObservation] with z hce
    intro hpending
    calc
      μ[PhaseServiceWaiting.observation
          (ReferenceFirstLiveSourceStoppedReleaseQuota.firstReleaseData
            rate rewards C_star C_h) i t.val | Hfield (t.val + 1)] z =
        ReferenceSourcePhysicalFlagConditionalLaw.actualDataControlSection
          rate rewards C_star C_h control0 i t z := hce
      _ = c rate rewards C_star C_h control0 i t z / (2 * (p.K : ℝ)) :=
        (assignedSection_eq_at_pending rate rewards C_star C_h control0 i t z hpending).symm
  have hupPending : ∀ᵐ z ∂μ,
      i ∈ P t.val z →
        o rate rewards C_star C_h control0 t z /
            (12 * (p.m - 1 : ℝ) * (p.K : ℝ)) ≤
          μ[PhaseServiceWaiting.observation
            (ReferenceFirstLiveSourceStoppedReleaseQuota.firstReleaseUp
              rate rewards C_star C_h) i t.val | Hfield (t.val + 1)] z := by
    filter_upwards [hupObservation] with z hce
    intro hpending
    calc
      o rate rewards C_star C_h control0 t z /
          (12 * (p.m - 1 : ℝ) * (p.K : ℝ)) ≤
        ReferenceSourcePhysicalFlagConditionalLaw.actualUpControlSection
          rate rewards C_star C_h control0 i t z :=
        auxiliarySection_lower_at_pending rate rewards C_star C_h control0 i t z hpending
      _ = μ[PhaseServiceWaiting.observation
            (ReferenceFirstLiveSourceStoppedReleaseQuota.firstReleaseUp
              rate rewards C_star C_h) i t.val | Hfield (t.val + 1)] z := hce.symm
  filter_upwards [hdataPending, hupPending] with z hdata hup
  intro hpending
  exact ⟨hdata hpending, hup hpending⟩

/-- The raw actual UP observation is measurable in the outcome source field. -/
theorem up_observation_predictable (i : Fin (p.m - 1)) (k : ℕ) (hk : k < p.T) :
    StronglyMeasurable[Hfield (k + 2)]
      (PhaseServiceWaiting.observation
        (ReferenceFirstLiveSourceStoppedReleaseQuota.firstReleaseUp
          rate rewards C_star C_h) i k) := by
  let t : Fin p.T := ⟨k, hk⟩
  have h := ReferenceSourcePrefixHistoryFiltration.flags_stronglyMeasurable
    rate rewards C_star C_h control0 i t
  have hobs : PhaseServiceWaiting.observation
      (ReferenceFirstLiveSourceStoppedReleaseQuota.firstReleaseUp rate rewards C_star C_h)
      i k = (fun z => if ReferenceSourcePrefixHistoryFiltration.actualUp
          rate rewards C_star C_h i t z = true then 1 else 0) := by
    funext z
    simpa [t, PhaseServiceWaiting.observation] using
      congrArg (fun b : Bool => if b then (1 : ℝ) else 0)
        (ReferenceFirstLiveSourceStoppedReleaseQuota.firstReleaseUp_fin
          rate rewards C_star C_h i t z)
  rw [hobs]
  exact h.1

/-- The raw actual DATA observation is measurable in the outcome source field. -/
theorem data_observation_predictable (i : Fin (p.m - 1)) (k : ℕ) (hk : k < p.T) :
    StronglyMeasurable[Hfield (k + 2)]
      (PhaseServiceWaiting.observation
        (ReferenceFirstLiveSourceStoppedReleaseQuota.firstReleaseData
          rate rewards C_star C_h) i k) := by
  let t : Fin p.T := ⟨k, hk⟩
  have h := ReferenceSourcePrefixHistoryFiltration.flags_stronglyMeasurable
    rate rewards C_star C_h control0 i t
  have hobs : PhaseServiceWaiting.observation
      (ReferenceFirstLiveSourceStoppedReleaseQuota.firstReleaseData rate rewards C_star C_h)
      i k = (fun z => if ReferenceSourcePrefixHistoryFiltration.actualData
          rate rewards C_star C_h i t z = true then 1 else 0) := by
    funext z
    simpa [t, PhaseServiceWaiting.observation] using
      congrArg (fun b : Bool => if b then (1 : ℝ) else 0)
        (ReferenceFirstLiveSourceStoppedReleaseQuota.firstReleaseData_fin
          rate rewards C_star C_h i t z)
  rw [hobs]
  exact h.2.1

/-- The raw actual combined-release observation is measurable in the outcome
source field. -/
theorem release_observation_predictable (i : Fin (p.m - 1)) (k : ℕ) (hk : k < p.T) :
    StronglyMeasurable[Hfield (k + 2)]
      (PhaseServiceWaiting.observation
        (ReferenceFirstLiveSourceStoppedReleaseQuota.firstReleaseRelease
          rate rewards C_star C_h) i k) := by
  let t : Fin p.T := ⟨k, hk⟩
  have h := ReferenceSourcePrefixHistoryFiltration.flags_stronglyMeasurable
    rate rewards C_star C_h control0 i t
  have hobs : PhaseServiceWaiting.observation
      (ReferenceFirstLiveSourceStoppedReleaseQuota.firstReleaseRelease rate rewards C_star C_h)
      i k = (fun z => if ReferenceSourcePrefixHistoryFiltration.actualRelease
          rate rewards C_star C_h i t z = true then 1 else 0) := by
    funext z
    simpa [t, PhaseServiceWaiting.observation] using
      congrArg (fun b : Bool => if b then (1 : ℝ) else 0)
        (ReferenceFirstLiveSourceStoppedReleaseQuota.firstReleaseRelease_fin
          rate rewards C_star C_h i t z)
  rw [hobs]
  exact h.2.2

end Bandits.Support.ReferenceFirstLiveSourceStoppedReleaseService

end
