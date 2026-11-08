/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCorrectedNativeUpReplayCalendarJoin
public import Bandits.Support.ReferenceFirstCorrectedCollectionPostCutoffNumericalOverflow

import Mathlib.Tactic

/-!
# Native UP first-prefix overflow cover

The computed prefixes of an accepted native UP reply on the first corrected
collection calendar are covered by the existing original-source all-arm
collection overflow event. The inherited finite-union probability estimate
then applies without changing its source law or endpoint.

Sources: ZIP4 `04_slow_fast_learner.tex:157-187,256-290`,
`06_interruptions.tex:192-233,246-299`, and
`appendix_a_local_protocol.tex:28-64` under `sources/zip4/manuscript/`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Bandits.Support ConstructorDimensions
open BootstrapPrivateRoundStreams (SourceInput sourceInputLaw)
open ContinuousLearningRows (TimeControl)
open ReferenceFirstCollectionCorrectedSliceNumericalPrefix
  (correctedCell sourceRecords sourceStart birthIndex liveTail prefixReadout)
open scoped Classical

namespace Bandits.Support.ReferenceFirstCorrectedNativeUpOverflowCover

variable {p : Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ)

local notation "X" => SourceInput p
local notation "Q" => ReferenceFirstLaunchNumericalCell.queueParameters rate

local instance sourceInputMeasurableSpace : MeasurableSpace X := by
  change MeasurableSpace
    (CompletePublicTable.PublishedOutput p ×
      BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

private theorem sourceRecord_actualRecord (z : X) (date : Fin p.T) (e : ℕ)
    (hdate : sourceStart rate rewards C_star C_h z + e = date.val)
    (entry : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hentry : (sourceRecords rate rewards C_star C_h z)[e]? = some entry) :
    ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h date z =
      some entry := by
  unfold ReferenceSourcePrefixHistoryFiltration.actualRecord
  change (if sourceStart rate rewards C_star C_h z ≤ date.val then
      (sourceRecords rate rewards C_star C_h z)[date.val -
        sourceStart rate rewards C_star C_h z]? else none) = some entry
  have hle : sourceStart rate rewards C_star C_h z ≤ date.val := by omega
  rw [ite_eq_left hle]
  have hindex : date.val - sourceStart rate rewards C_star C_h z = e := by omega
  rw [hindex]
  exact hentry

/-- Every literal first-cell native-UP computed queue prefix whose integer
backlog crosses the source threshold produces an arm crossing in the same
initialized stopped run. The detecting arm may differ from the accepted
reply's observed arm, and the zero-length cutoff-seed prefix is retained. -/
theorem firstNativeUpPrefixEvent_subset_allArmCollectionOverflowEvent
    (u t : Fin p.T) :
    ReferenceFirstCorrectedNativeUpComputedPrefixObservation.firstNativeUpPrefixEvent
        rate rewards C_star C_h u t ⊆
      ReferenceFirstCorrectedCollectionPostCutoffNumericalOverflow.allArmCollectionOverflowEvent
        rate rewards C_star C_h := by
  intro z hz
  change z ∈ correctedCell rate rewards C_star C_h u t ∧ _ at hz
  rcases hz with ⟨hz, j, k, a, q, hqueue, hthreshold⟩
  let R := sourceRecords rate rewards C_star C_h z
  let s := sourceStart rate rewards C_star C_h z
  let e := birthIndex rate rewards C_star C_h z + 1 +
    (liveTail rate rewards C_star C_h z).length
  obtain ⟨entry, record, seg, d0, M, past, current, A, D, P,
    hentry, hentrySeg, hcutEntry, hseg, hjpos, hjlt, hrecordBound, hkle,
    hrecord, hdiag, hsender, hparsed, haccepted, hassigned, hdecoded,
    hdomains, hword, hqueueCalendar, hAlen, hDlen, hPdef, hPlen,
    hprefixA, hprefixSegment, hprefixP, htBound, hwithin, hsegmentBound,
    hqCalendar⟩ :=
      ReferenceFirstCorrectedNativeUpReplayCalendarJoin.firstCell_nativeUp_replay_calendar_join
        rate rewards C_star C_h u t z hz j k a q hqueue

  have hbirth := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.firstCell_birth_time
    rate rewards C_star C_h u t z hz
  have hlive := ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.continuingLength_actual
    rate rewards C_star C_h u t z hz
  let d := t.val + 1 +
    ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.continuingLength
      rate rewards C_star C_h t z
  have hde : s + e = d := by
    dsimp only [s, e, d]
    rw [← hlive]
    omega

  have hEpos : 0 < e := by
    dsimp only [e]
    omega
  have hPpos : 0 < P.length := by
    rw [hPlen]
    omega
  have hn : d + k = s + e + k := by omega
  have htn : t.val + 1 ≤ d + k := by
    exact htBound.trans (by rw [hde])

  have hnorm : ∃ i : Fin p.K,
      ((UnstoppedRecordedQueueComparison.unstoppedReplay Q P P.length i).2 : ℝ) /
        ((Q).n : ℝ) > 1 / (32 * (Q).eta) := by
    refine ⟨a, ?_⟩
    rw [← hqCalendar]
    simpa only [ReferenceFirstLaunchNumericalCell.queueParameters] using hthreshold
  have hcross :
      UnstoppedRecordedQueueComparison.replay_crosses_overflow Q P P.length :=
    (UnstoppedRecordedQueueComparison.replay_crosses_overflow_iff_normalized
      Q P P.length).2 hnorm
  have hcrossExists : ∃ m, 1 ≤ m ∧ m ≤ P.length ∧
      UnstoppedRecordedQueueComparison.replay_crosses_overflow Q P m :=
    ⟨P.length, by omega, le_rfl, hcross⟩
  have hfirstle : UnstoppedRecordedQueueComparison.firstOverflowPrefix Q P ≤ P.length := by
    dsimp [UnstoppedRecordedQueueComparison.firstOverflowPrefix]
    rw [dite_eq_left hcrossExists]
    exact Nat.find_min' hcrossExists ⟨by omega, le_rfl, hcross⟩
  have hrunOverflow : (RecordedQueueRun.run Q P).overflow = true := by
    have hprefix :=
      UnstoppedRecordedQueueComparison.prefix_overflow_iff_first_overflow_prefix_le
        Q P P.length (by omega)
    have h := hprefix.mpr hfirstle
    simpa only [List.take_length] using h
  obtain ⟨detector, hdetector⟩ :=
    (StoppedQueueBound.run_overflow_iff_terminal_threshold Q P).mp hrunOverflow

  have hdateBound : d < p.T := by
    have hsegLen : 0 < seg.records.length := by omega
    have hsE : s + e < p.T := by omega
    rw [← hde]
    exact hsE
  let date : Fin p.T := ⟨d, hdateBound⟩
  have hdateIndex : s + e = date.val := by
    dsimp only [date]
    exact hde
  have hactualRecord := sourceRecord_actualRecord rate rewards C_star C_h z date e
    hdateIndex entry hentry
  have hcutDate :
      ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.horizonCutoff
        rate rewards C_star C_h date z =
      ReferenceCollectionPhaseHistory.cutoffChosen entry.input := by
    unfold ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.horizonCutoff
      ReferenceFirstCollectionCorrectedNextPhysicalReadout.actualInput?
    simp only [hactualRecord, Option.map_some, Option.bind_some]
    unfold ReferenceFirstCollectionRenewalNextRecordingPriorView.dispatchTag
      ReferenceCollectionPhaseHistory.cutoffChosen
    have hprepare :
        (ReferenceActivePhysicalStep.prepare entry.input).coordinator =
          ReferenceActivePhysicalStep.dispatch entry.input := rfl
    rw [hprepare]
    cases ReferenceActivePhysicalStep.dispatch entry.input with
    | live registers owned base outcome => cases outcome <;> rfl
    | first outcome => rfl
    | collection payload ledger clock cutoff outcome => rfl
    | invalidCollectionCutoff => rfl
    | dagger => rfl
  have hcutFlag :
      ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.horizonCutoff
        rate rewards C_star C_h date z = true := hcutDate.trans hcutEntry
  obtain ⟨entry', actualSeg, hentry', hcut', hseg', hendpoint⟩ :=
    Bandits.Support.ReferenceFirstCorrectedCollectionPostCutoffNumericalOverflow.collectionEndpoint_eq_actualSegment_of_cutoff
        rate rewards C_star C_h u t z hz hdateBound hcutFlag
  have hsameSeg : actualSeg = seg := Option.some.inj (hseg'.symm.trans hseg)
  rw [hsameSeg] at hendpoint
  have hnEndpoint : d + k ≤
      Bandits.Support.ReferenceFirstCorrectedCollectionPostCutoffNumericalOverflow.collectionEndpoint
        rate rewards C_star C_h t z := by
    rw [hendpoint]
    have hsegmentPrefix : d + k ≤ s + e + seg.records.length := by
      calc
        d + k = s + e + k := by rw [hde]
        _ ≤ s + e + seg.records.length := hwithin
    exact hsegmentPrefix.trans (Nat.le_max_right _ _)

  have hprefixAtN :
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
        rate rewards C_star C_h (d + k) z = some P := by
    rw [← hde]
    exact hprefixP
  let out : ReferenceFirstCollectionCurrentQueueReadout.QueueReadout p.K :=
    ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
      (RecordedQueueRun.run Q P)
  have hout : prefixReadout rate rewards C_star C_h (d + k) z = some out := by
    simp only [ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout,
      hprefixAtN, Option.map_some, out]
  have hdetectorThreshold :
      ((out.1 detector).2 : ℝ) / ((Q).n : ℝ) >
        1 / (32 * rate.eta.val) := by
    simpa only [out,
      ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout,
      StoppedQueueBound.normalizedBacklog,
      ReferenceFirstLaunchNumericalCell.queueParameters] using hdetector
  have hmember : z ∈
      Bandits.Support.ReferenceFirstCorrectedCollectionPostCutoffNumericalOverflow.collectionOverflowEvent
        rate rewards C_star C_h u t detector := by
    change z ∈ correctedCell rate rewards C_star C_h u t ∧ _
    exact ⟨hz, d + k, htn, hnEndpoint, out, hout, hdetectorThreshold⟩
  change z ∈ ⋃ a : Fin p.K, ⋃ u : Fin p.T, ⋃ t : Fin p.T,
      Bandits.Support.ReferenceFirstCorrectedCollectionPostCutoffNumericalOverflow.collectionOverflowEvent
      rate rewards C_star C_h u t a
  exact Set.mem_iUnion.mpr ⟨detector,
    Set.mem_iUnion.mpr ⟨u, Set.mem_iUnion.mpr ⟨t, hmember⟩⟩⟩

/-- The original source-law probability of the finite union over every first
cell and calendar round inherits the existing all-arm collection bound. -/
theorem firstNativeUpPrefixEvent_union_measure_le (control0 : TimeControl p) :
    (sourceInputLaw p).real
        (⋃ u : Fin p.T, ⋃ t : Fin p.T,
          ReferenceFirstCorrectedNativeUpComputedPrefixObservation.firstNativeUpPrefixEvent
            rate rewards C_star C_h u t) ≤
      2 * (p.K : ℝ) * ((p.T : ℝ) + 1) *
        Real.exp (-CanonicalRecordingRates.beta p rate.eta.val /
          (32 * rate.eta.val)) := by
  have hsubset :
      (⋃ u : Fin p.T, ⋃ t : Fin p.T,
        ReferenceFirstCorrectedNativeUpComputedPrefixObservation.firstNativeUpPrefixEvent
          rate rewards C_star C_h u t) ⊆
        Bandits.Support.ReferenceFirstCorrectedCollectionPostCutoffNumericalOverflow.allArmCollectionOverflowEvent
          rate rewards C_star C_h := by
    intro z hz
    simp only [Set.mem_iUnion] at hz
    obtain ⟨u, t, hzt⟩ := hz
    exact firstNativeUpPrefixEvent_subset_allArmCollectionOverflowEvent
      rate rewards C_star C_h u t hzt
  calc
    (sourceInputLaw p).real
        (⋃ u : Fin p.T, ⋃ t : Fin p.T,
          ReferenceFirstCorrectedNativeUpComputedPrefixObservation.firstNativeUpPrefixEvent
            rate rewards C_star C_h u t) ≤
      (sourceInputLaw p).real
        (Bandits.Support.ReferenceFirstCorrectedCollectionPostCutoffNumericalOverflow.allArmCollectionOverflowEvent
          rate rewards C_star C_h) :=
            measureReal_mono (μ := sourceInputLaw p) hsubset (by finiteness)
    _ ≤ 2 * (p.K : ℝ) * ((p.T : ℝ) + 1) *
        Real.exp (-CanonicalRecordingRates.beta p rate.eta.val /
          (32 * rate.eta.val)) :=
      Bandits.Support.ReferenceFirstCorrectedCollectionPostCutoffNumericalOverflow.allArmCollectionOverflowEvent_measure_le
          rate rewards C_star C_h control0

end Bandits.Support.ReferenceFirstCorrectedNativeUpOverflowCover

end noncomputable section
