/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveStoppedHandoverSectionService
public import Bandits.Support.ReferenceFirstLiveStoppedReleaseSignedCost
public import Mathlib.Probability.Process.Stopping

import Lean.Elab.Tactic.Omega

/-!
# Initial transfer launch and later phase starts

The genuine initialization launch is a stopping time in the original
source-prefix filtration and precedes the actual handover and release starts.
The phase-start σ-algebras therefore inherit the corresponding inclusions.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open scoped Classical

namespace Bandits.Support.ReferenceFirstLiveInitialTransferStartFields

section InitialFields

variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ)

local notation "Source" => BootstrapPrivateRoundStreams.SourceInput p
local notation "L" => fun z : Source =>
  ReferenceInitializationRun.launchRound
    (ReferenceCompletePhysicalHistory.generatedInput rate z rewards C_star C_h)
local notation "s" => fun z : Source =>
  ReferenceFirstLiveSourceStoppedReleaseEndpoint.physicalStart rate rewards C_star C_h z

private theorem launch_eq_physicalStart_succ (z : Source) :
    L z = s z + 1 := by
  change ReferenceInitializationRun.launchRound
      (ReferenceCompletePhysicalHistory.generatedInput rate z rewards C_star C_h) =
    ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + 1
  unfold ReferenceInitializationRun.launchRound
  by_cases hcross : (ReferenceInitializationRun.output
      (ReferenceCompletePhysicalHistory.generatedInput rate z rewards C_star C_h)).crossing.isSome = true
  · simp [hcross, ReferenceCompletePhysicalHistory.physicalStart,
      ReferenceCompletePhysicalHistory.generatedBoundary]
  · have hboundary : (ReferenceInitializationRun.output
        (ReferenceCompletePhysicalHistory.generatedInput rate z rewards C_star C_h)).crossing = none := by
      cases hc : (ReferenceInitializationRun.output
          (ReferenceCompletePhysicalHistory.generatedInput rate z rewards C_star C_h)).crossing with
      | none => rfl
      | some value => simp [hc] at hcross
    have hnone : ReferenceCorrectedInitializationLaunch.correctedLaunch
        rate z rewards C_star C_h = none :=
      (ReferenceCorrectedInitializationLaunch.correctedLaunch_eq_none_iff
        rate z rewards C_star C_h).2 (by
          simpa [ReferenceCompletePhysicalHistory.generatedInput] using hboundary)
    have hstart := ReferenceCompletePhysicalHistory.correctedLaunch_none_start_eq_T
      rate z rewards C_star C_h hnone
    have hsElapsed : ReferenceInitializationRun.elapsed p
        (ReferenceInitializationRun.output
          (ReferenceCompletePhysicalHistory.generatedInput rate z rewards C_star C_h)).completed = p.T := by
      change ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h = p.T at hstart
      simpa [ReferenceCompletePhysicalHistory.physicalStart,
        ReferenceCompletePhysicalHistory.generatedBoundary] using hstart
    simp [hboundary, ReferenceCompletePhysicalHistory.physicalStart,
      ReferenceCompletePhysicalHistory.generatedBoundary, hsElapsed]

private theorem launch_le_handover_start (z : Source) :
    L z ≤ ReferenceFirstLiveSourceStoppedHandoverEndpoint.sigma rate rewards C_star C_h z := by
  have hlaunch := launch_eq_physicalStart_succ rate rewards C_star C_h z
  by_cases hne : (ReferenceFirstLiveSourceStoppedHandoverEndpoint.supportDates rate rewards C_star C_h z).Nonempty
  · rw [ReferenceFirstLiveSourceStoppedHandoverEndpoint.sigma_eq_physicalStart_succ rate rewards C_star C_h z hne]
    exact Nat.le_of_eq hlaunch
  · have hempty : ReferenceFirstLiveSourceStoppedHandoverEndpoint.supportDates rate rewards C_star C_h z = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hne
    have hsigma : ReferenceFirstLiveSourceStoppedHandoverEndpoint.sigma rate rewards C_star C_h z = p.T + 1 := by
      simp [ReferenceFirstLiveSourceStoppedHandoverEndpoint.sigma, hempty]
    rw [hsigma, hlaunch]
    have hs : s z ≤ p.T := by
      change ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h ≤ p.T
      exact ReferenceCompletePhysicalHistory.physicalStart_le_T rate z rewards C_star C_h
    exact Nat.succ_le_succ hs

private theorem actual_gate_after_initial_launch (z : Source) (v : ℕ)
    (hv : v ∈ ReferenceFirstLiveSourceStoppedReleaseEndpoint.actualGateSupport rate rewards C_star C_h z) :
    s z + 1 ≤ v := by
  let start := s z
  have hcross : (ReferenceCompletePhysicalHistory.generatedBoundary
      rate z rewards C_star C_h).crossing.isSome = true := by
    by_contra hnot
    have hnoneCross : (ReferenceCompletePhysicalHistory.generatedBoundary
        rate z rewards C_star C_h).crossing = none := by
      cases hc : (ReferenceCompletePhysicalHistory.generatedBoundary
          rate z rewards C_star C_h).crossing with
      | none => rfl
      | some value => simp [hc] at hnot
    have hnone : ReferenceCorrectedInitializationLaunch.correctedLaunch
        rate z rewards C_star C_h = none :=
      (ReferenceCorrectedInitializationLaunch.correctedLaunch_eq_none_iff
        rate z rewards C_star C_h).2 (by
          simpa [ReferenceCompletePhysicalHistory.generatedBoundary,
            ReferenceCompletePhysicalHistory.generatedInput] using hnoneCross)
    have hhistory := ReferenceCompletePhysicalHistory.no_launch_complete_history
      rate z rewards C_star C_h hnone
    have hgate : ReferenceFirstLiveSourceStoppedReleaseEndpoint.actualGateSupport rate rewards C_star C_h z = ∅ := by
      change ReferenceLocalReleaseGateChronology.gateSupport
        (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
        (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h) = ∅
      rw [hhistory.2.1]
      simp [ReferenceLocalReleaseGateChronology.gateSupport]
    rw [hgate] at hv
    simp at hv
  have hcrossRun : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true := by
    simpa [ReferenceCompletePhysicalHistory.generatedBoundary,
      ReferenceCompletePhysicalHistory.generatedInput] using hcross
  have hlaunch := ReferenceLocalReleaseGateChronology.sourceSeed_launch rate z rewards C_star C_h hcrossRun
  have hseed := ReferenceLocalReleaseGateChronology.canonical_seed_release_inputs rate z rewards C_star C_h hcrossRun
  have hactive : ReferenceActivePhysicalHorizon.allActiveAtStart
      (ReferenceLocalReleaseGateChronology.sourceSeed rate z rewards C_star C_h hcrossRun) start := by
    simpa only [start, ReferenceFirstLiveSourceStoppedReleaseEndpoint.physicalStart,
      ReferenceCompletePhysicalHistory.physicalStart,
      ReferenceCompletePhysicalHistory.generatedBoundary,
      ReferenceCompletePhysicalHistory.generatedInput] using hseed.2.1
  have hspan : start + (p.T - start) ≤ p.T := by
    have hs : start ≤ p.T := by
      change ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h ≤ p.T
      exact ReferenceCompletePhysicalHistory.physicalStart_le_T rate z rewards C_star C_h
    omega
  have hrecords :
      (ReferenceLocalReleaseGateChronology.sourceRun rate z rewards C_star C_h hcrossRun start (p.T - start) rfl hspan).records =
        ReferenceFirstLiveSourceStoppedReleaseEndpoint.completeRecords rate rewards C_star C_h z := by
    exact (ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
      rate z rewards C_star C_h (ReferenceLocalReleaseGateChronology.sourceSeed rate z rewards C_star C_h hcrossRun) hlaunch).symm
  have hsupport : ReferenceFirstLiveSourceStoppedReleaseEndpoint.actualGateSupport rate rewards C_star C_h z =
      ReferenceLocalReleaseGateChronology.gateSupport start
        (ReferenceLocalReleaseGateChronology.sourceRun rate z rewards C_star C_h hcrossRun start (p.T - start) rfl hspan).records := by
    change ReferenceLocalReleaseGateChronology.gateSupport
        (ReferenceFirstLiveSourceStoppedReleaseEndpoint.physicalStart rate rewards C_star C_h z)
        (ReferenceFirstLiveSourceStoppedReleaseEndpoint.completeRecords rate rewards C_star C_h z) = _
    calc
      _ = ReferenceLocalReleaseGateChronology.gateSupport start
          (ReferenceFirstLiveSourceStoppedReleaseEndpoint.completeRecords rate rewards C_star C_h z) := by
            rfl
      _ = ReferenceLocalReleaseGateChronology.gateSupport start
          (ReferenceLocalReleaseGateChronology.sourceRun rate z rewards C_star C_h hcrossRun start
            (p.T - start) rfl hspan).records := by
            rw [hrecords]
  have hv' : v ∈ ReferenceLocalReleaseGateChronology.gateSupport start
      (ReferenceLocalReleaseGateChronology.sourceRun rate z rewards C_star C_h hcrossRun start (p.T - start) rfl hspan).records := by
    rw [← hsupport]
    exact hv
  obtain ⟨r, hr, hgate, hdate⟩ :=
    (ReferenceLocalReleaseGateChronology.mem_gateSupport start v
      (ReferenceLocalReleaseGateChronology.sourceRun rate z rewards C_star C_h hcrossRun start (p.T - start) rfl hspan).records).mp hv'
  have hborn := ReferenceLocalReleaseGateChronology.run_gate_record_birth
    (ReferenceLocalReleaseGateChronology.sourceSeed rate z rewards C_star C_h hcrossRun) z.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards start hactive
    (p.T - start) hspan hseed.1 r hr start hgate
  omega

private theorem launch_le_release_start (z : Source) :
    L z ≤ ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstReleaseSigma rate rewards C_star C_h z := by
  have hlaunch := launch_eq_physicalStart_succ rate rewards C_star C_h z
  by_cases hne : (ReferenceFirstLiveSourceStoppedReleaseEndpoint.actualFirstReleaseSupport rate rewards C_star C_h z).Nonempty
  · obtain ⟨hinterval, hlow, horder, hhigh⟩ :=
      ReferenceFirstLiveSourceStoppedReleaseEndpoint.actual_first_release_interval rate rewards C_star C_h z
    have hsigmem : ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstReleaseSigma rate rewards C_star C_h z ∈
        ReferenceFirstLiveSourceStoppedReleaseEndpoint.actualFirstReleaseSupport rate rewards C_star C_h z := by
      rw [hinterval]
      obtain ⟨v, hv⟩ := hne
      have hv' := Finset.mem_Ico.mp (hinterval ▸ hv)
      exact Finset.mem_Ico.mpr ⟨le_rfl, lt_of_le_of_lt hv'.1 hv'.2⟩
    have hgate : ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstReleaseSigma rate rewards C_star C_h z ∈
        ReferenceFirstLiveSourceStoppedReleaseEndpoint.actualGateSupport rate rewards C_star C_h z :=
      Finset.mem_filter.mp hsigmem |>.1
    have hafter := actual_gate_after_initial_launch rate rewards C_star C_h z _ hgate
    exact (Nat.le_of_eq hlaunch).trans hafter
  · have hempty : ReferenceFirstLiveSourceStoppedReleaseEndpoint.actualFirstReleaseSupport rate rewards C_star C_h z = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hne
    have hendpoints := ReferenceFirstLiveSourceStoppedReleaseEndpoint.empty_first_release_endpoints
      rate rewards C_star C_h z hempty
    rw [hendpoints.1, hlaunch]
    have hs : s z ≤ p.T := by
      change ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h ≤ p.T
      exact ReferenceCompletePhysicalHistory.physicalStart_le_T rate z rewards C_star C_h
    exact Nat.succ_le_succ hs

/-- The actual initialization output fixes the genuine launch one round after
the physical start, and that launch precedes both later stopped starts. -/
theorem initial_transfer_start_fields (z : Source) :
    L z = s z + 1 ∧
      L z ≤ ReferenceFirstLiveSourceStoppedHandoverEndpoint.sigma rate rewards C_star C_h z ∧
      L z ≤ ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstReleaseSigma rate rewards C_star C_h z := by
  exact ⟨launch_eq_physicalStart_succ rate rewards C_star C_h z,
    launch_le_handover_start rate rewards C_star C_h z,
    launch_le_release_start rate rewards C_star C_h z⟩

end InitialFields

section StoppingAndInclusions

variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)

local notation "Source" => BootstrapPrivateRoundStreams.SourceInput p
local notation "L" => fun z : Source =>
  ReferenceInitializationRun.launchRound
    (ReferenceCompletePhysicalHistory.generatedInput rate z rewards C_star C_h)
local notation "F" =>
  ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0

/-- The actual initialization launch is a pre-round stopping time in the
canonical original-source prefix filtration. -/
theorem initial_launch_preRound_stopping :
    PhaseServiceWaiting.IsPreRoundStoppingTime F L := by
  intro n
  by_cases hn0 : n = 0
  · subst n
    have heq : {z : Source | L z ≤ 0} = ∅ := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      have hstart : ReferenceInitializationRun.launchRound
          (ReferenceCompletePhysicalHistory.generatedInput rate z rewards C_star C_h) =
            ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + 1 := by
        simpa [ReferenceFirstLiveSourceStoppedReleaseEndpoint.physicalStart,
          ReferenceCompletePhysicalHistory.physicalStart] using
            (initial_transfer_start_fields rate rewards C_star C_h z).1
      change ¬ ReferenceInitializationRun.launchRound
        (ReferenceCompletePhysicalHistory.generatedInput rate z rewards C_star C_h) ≤ 0
      rw [hstart]
      exact Nat.not_succ_le_zero _
    rw [heq]
    exact @MeasurableSet.empty Source (F 0)
  by_cases hnT : n ≤ p.T
  · let t : Fin p.T := ⟨n - 1, by omega⟩
    have ht : t.val + 1 = n := by simp [t]; omega
    have hset : {z : Source | L z ≤ n} =
        ⋃ b : Fin n,
          ReferenceGeneratedDownAmbiguityMeasurability.generatedLaunchFiberSet
            (rate := rate) rewards C_star C_h b.val := by
      ext z
      constructor
      · intro hz
        have hstart' : ReferenceInitializationRun.launchRound
            (ReferenceCompletePhysicalHistory.generatedInput rate z rewards C_star C_h) =
              ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + 1 := by
          simpa [ReferenceFirstLiveSourceStoppedReleaseEndpoint.physicalStart,
            ReferenceCompletePhysicalHistory.physicalStart] using
              (initial_transfer_start_fields rate rewards C_star C_h z).1
        have hslt : ReferenceCompletePhysicalHistory.physicalStart
            rate z rewards C_star C_h < n := by
          change ReferenceInitializationRun.launchRound
            (ReferenceCompletePhysicalHistory.generatedInput rate z rewards C_star C_h) ≤ n at hz
          rw [hstart'] at hz
          omega
        have hcross : (ReferenceCompletePhysicalHistory.generatedBoundary
            rate z rewards C_star C_h).crossing.isSome = true := by
          by_contra hnot
          have hnoneCross : (ReferenceCompletePhysicalHistory.generatedBoundary
              rate z rewards C_star C_h).crossing = none := by
            cases hc : (ReferenceCompletePhysicalHistory.generatedBoundary
                rate z rewards C_star C_h).crossing with
            | none => rfl
            | some value => simp [hc] at hnot
          have hnone : ReferenceCorrectedInitializationLaunch.correctedLaunch
              rate z rewards C_star C_h = none :=
            (ReferenceCorrectedInitializationLaunch.correctedLaunch_eq_none_iff
              rate z rewards C_star C_h).2 (by
                simpa [ReferenceCompletePhysicalHistory.generatedBoundary,
                  ReferenceCompletePhysicalHistory.generatedInput] using hnoneCross)
          have hstartT := ReferenceCompletePhysicalHistory.correctedLaunch_none_start_eq_T
            rate z rewards C_star C_h hnone
          have hsT : ReferenceCompletePhysicalHistory.physicalStart
              rate z rewards C_star C_h = p.T := hstartT
          omega
        refine Set.mem_iUnion.mpr ⟨⟨
          ReferenceFirstLiveSourceStoppedReleaseEndpoint.physicalStart
            rate rewards C_star C_h z, hslt⟩, ?_⟩
        exact ⟨hcross, rfl⟩
      · intro hz
        obtain ⟨b, hb⟩ := Set.mem_iUnion.mp hz
        have hfiber := hb
        simp [ReferenceGeneratedDownAmbiguityMeasurability.generatedLaunchFiberSet] at hfiber
        have hstart' : ReferenceInitializationRun.launchRound
            (ReferenceCompletePhysicalHistory.generatedInput rate z rewards C_star C_h) =
              ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + 1 := by
          simpa [ReferenceFirstLiveSourceStoppedReleaseEndpoint.physicalStart,
            ReferenceCompletePhysicalHistory.physicalStart] using
              (initial_transfer_start_fields rate rewards C_star C_h z).1
        change ReferenceInitializationRun.launchRound
          (ReferenceCompletePhysicalHistory.generatedInput rate z rewards C_star C_h) ≤ n
        rw [hstart', hfiber.2]
        exact Nat.succ_le_of_lt b.isLt
    rw [hset]
    apply MeasurableSet.iUnion
    intro b
    have hb : b.val ≤ t.val := by have hb' := b.isLt; omega
    have hm := ReferenceSourcePrefixHistoryFiltration.actualLaunchStratum_measurable
      (rate := rate) rewards C_star C_h control0 t b.val hb
    have hfield : F (t.val + 1) = F n := congrArg (fun k : ℕ => F k) ht
    exact hfield ▸ hm
  · have hset : {z : Source | L z ≤ n} = Set.univ := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      have hstart := launch_eq_physicalStart_succ rate rewards C_star C_h z
      have hs := ReferenceCompletePhysicalHistory.physicalStart_le_T
        rate z rewards C_star C_h
      have hstart : ReferenceInitializationRun.launchRound
          (ReferenceCompletePhysicalHistory.generatedInput rate z rewards C_star C_h) =
            ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + 1 := by
        simpa [ReferenceFirstLiveSourceStoppedReleaseEndpoint.physicalStart,
          ReferenceCompletePhysicalHistory.physicalStart] using
            (initial_transfer_start_fields rate rewards C_star C_h z).1
      change ReferenceInitializationRun.launchRound
        (ReferenceCompletePhysicalHistory.generatedInput rate z rewards C_star C_h) ≤ n
      rw [hstart]
      omega
    rw [hset]
    exact @MeasurableSet.univ Source (F n)

/-- The launch-start σ-algebra is included in each actual phase-start
σ-algebra, using the original source law's canonical filtration. -/
theorem initial_phase_start_sigmaAlgebra_inclusions :
    let hL := initial_launch_preRound_stopping rate rewards C_star C_h control0
    let FL := PhaseStartConditionalWaiting.phaseStartSigmaAlgebra F L hL
    let hH := ReferenceFirstLiveStoppedHandoverAdaptation.sigma_preRound_stopping
      rate rewards C_star C_h control0
    let FH := PhaseStartConditionalWaiting.phaseStartSigmaAlgebra F
      (ReferenceFirstLiveSourceStoppedHandoverEndpoint.sigma rate rewards C_star C_h) hH
    let hR := ReferenceFirstLiveSourceStoppedReleaseAdaptation.first_release_sigma_stopping
      rate rewards C_star C_h control0
    let FR := PhaseStartConditionalWaiting.phaseStartSigmaAlgebra F
      (ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstReleaseSigma rate rewards C_star C_h) hR
    FL ≤ FH ∧ FL ≤ FR := by
  dsimp only
  let hL := initial_launch_preRound_stopping rate rewards C_star C_h control0
  let hH := ReferenceFirstLiveStoppedHandoverAdaptation.sigma_preRound_stopping
    rate rewards C_star C_h control0
  let hR := ReferenceFirstLiveSourceStoppedReleaseAdaptation.first_release_sigma_stopping
    rate rewards C_star C_h control0
  have htimes := fun z => initial_transfer_start_fields rate rewards C_star C_h z
  have hLstop := PhaseStartConditionalWaiting.isStoppingTime_of_preRound F L hL
  have hHstop := PhaseStartConditionalWaiting.isStoppingTime_of_preRound F
    (ReferenceFirstLiveSourceStoppedHandoverEndpoint.sigma rate rewards C_star C_h) hH
  have hRstop := PhaseStartConditionalWaiting.isStoppingTime_of_preRound F
    (ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstReleaseSigma rate rewards C_star C_h) hR
  change hLstop.measurableSpace ≤ hHstop.measurableSpace ∧
    hLstop.measurableSpace ≤ hRstop.measurableSpace
  constructor
  · apply MeasureTheory.IsStoppingTime.measurableSpace_mono hLstop hHstop
    intro z
    exact WithTop.coe_le_coe.mpr (htimes z).2.1
  · apply MeasureTheory.IsStoppingTime.measurableSpace_mono hLstop hRstop
    intro z
    exact WithTop.coe_le_coe.mpr (htimes z).2.2

end StoppingAndInclusions

end Bandits.Support.ReferenceFirstLiveInitialTransferStartFields

end
