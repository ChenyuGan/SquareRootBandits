/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCorrectedNativeDownCalendarReplay

import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic

/-!
# Computed prefixes of an accepted native DOWN recovery

This event records the literal current-payload DOWN acceptance and tests the
initial queue as well as every successful checked computed prefix.  Its cover
uses the existing original-source stopped overflow event.

Sources: ZIP4 `04_slow_fast_learner.tex:157-187,256-290`,
`06_interruptions.tex:40-100,192-233,256-290,355-426`, and
`appendix_a_local_protocol.tex:28-64` under `sources/zip4/manuscript/`.
-/

@[expose] public section
noncomputable section

open Bandits.Support ConstructorDimensions MeasureTheory
open BootstrapPrivateRoundStreams (SourceInput sourceInputLaw)
open ContinuousLearningRows (TimeControl)
open scoped Classical

namespace Bandits.Support.ReferenceFirstCorrectedNativeDownOverflowCover

variable {p : Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ)

local notation "X" => SourceInput p
local notation "Q" => ReferenceFirstLaunchNumericalCell.queueParameters rate

local instance sourceInputMeasurableSpace : MeasurableSpace (SourceInput p) := by
  change MeasurableSpace
    (CompletePublicTable.PublishedOutput p ×
      BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

/-- A current selection of the installed payload was accepted by an actual
follower DOWN operation, and either its untouched initial queue or one of the
successful checked computed prefixes crosses the source overflow threshold.
The witnesses are all read from the original complete suffix execution. -/
def nativeDownComputedOverflowEvent (u t : Fin p.T) : Set X :=
  {z | z ∈ ReferenceFirstCollectionCorrectedSliceNumericalPrefix.correctedCell
        rate rewards C_star C_h u t ∧
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h
    let b := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.birthIndex
      rate rewards C_star C_h z
    ∃ (birth : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
      (P : ReferenceActivePhysicalStep.Payload rate),
      R[b]? = some birth ∧
      ReferenceAssignmentPayloadPersistence.InstallationBirth birth P ∧
      P.sigma = t ∧
      ∃ (j : Fin R.length), b ≤ j.val ∧
        ∃ current : ReferenceActivePhysicalStep.Selection R[j.val].input,
          R[j.val].output.preparation.coordinator.selection = some current ∧
          current.view.payload = P ∧
          ∃ (i : Fin (p.m - 1))
            (logged : ReferencePrelaunchFollower.State p rate.eta)
            (cut : ReferenceDownReception.ReferenceDownCutOutput p rate),
            (R[j.val].output.followers i).downInput = some logged ∧
            (R[j.val].output.followers i).down = some cut ∧
            ∃ (before after : ReferencePrelaunchFollower.State p rate.eta)
              (raw : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p)))
              (M : OrdinaryMessageCodec.DownRecord
                (ReferencePrelaunchFollower.codecParams p rate.eta))
              (scan : FollowerCutoffScan.ScanResult p.T)
              (registers : ℕ × ℕ) (lastService : ℕ),
              cut.outcome = ActiveFollowerDownAcceptance.LocalDownResult.accepted
                before after raw M scan registers lastService ∧
              M = P.downRecord i ∧
              let A := ActiveFollowerDownAcceptance.recoveryQueueRecords
                p rate M logged scan.endpoint
              (((M.val.q : ℝ) / (rate.n : ℝ) > 1 / (32 * rate.eta.val)) ∨
                ∃ (k : ℕ) (middle : ActiveFollowerDownAcceptance.ReplayRegisters),
                  1 ≤ k ∧ k ≤ A.length ∧
                  ActiveFollowerDownAcceptance.checkedReplay (D p) (p.T * D p)
                    (4 * rate.n) 0 ⟨(0, M.val.q), 0⟩ (A.take k) = Except.ok middle ∧
                  ((middle.registers.2 : ℝ) / (rate.n : ℝ) >
                    1 / (32 * rate.eta.val)))}

private theorem list_mapM_take_of_some {α β : Type*}
    (f : α → Option β) :
    ∀ (xs : List α) (ys : List β), xs.mapM f = some ys →
      ∀ k, ∃ ys', (xs.take k).mapM f = some ys' ∧ ys' = ys.take k := by
  intro xs
  induction xs with
  | nil =>
      intro ys h k
      have hy : ys = [] := by simpa using h.symm
      subst ys
      cases k <;> simp
  | cons x xs ih =>
      intro ys h k
      cases k with
      | zero => exact ⟨[], by simp, by simp⟩
      | succ k =>
          simp only [List.mapM_cons] at h
          cases hf : f x with
          | none => simp [hf] at h
          | some y =>
              cases ht : xs.mapM f with
              | none => simp [hf, ht] at h
              | some ys0 =>
                  have hys : ys = y :: ys0 := by
                    have heq : some (y :: ys0) = some ys := by
                      simpa [List.mapM_cons, hf, ht] using h
                    exact (Option.some.inj heq).symm
                  subst ys
                  obtain ⟨ys1, htake, hys1⟩ := ih ys0 ht k
                  refine ⟨y :: ys1, ?_, ?_⟩
                  · simp [List.take_succ_cons, List.mapM_cons, hf, htake]
                  · simp only [List.take_succ_cons, hys1]

private theorem list_mapM_length_of_some {α β : Type*}
    (f : α → Option β) :
    ∀ (xs : List α) (ys : List β), xs.mapM f = some ys → xs.length = ys.length := by
  intro xs
  induction xs with
  | nil =>
      intro ys h
      have hy : ys = [] := by simpa using h.symm
      simp [hy]
  | cons x xs ih =>
      intro ys h
      simp only [List.mapM_cons] at h
      cases hf : f x with
      | none => simp [hf] at h
      | some y =>
          cases ht : xs.mapM f with
          | none => simp [hf, ht] at h
          | some ys0 =>
              have hys : ys = y :: ys0 := by
                have heq : some (y :: ys0) = some ys := by
                  simpa [List.mapM_cons, hf, ht] using h
                exact (Option.some.inj heq).symm
              subst ys
              simp only [List.length_cons, ih ys0 ht]

private theorem continuingWindows_eq (z : X) :
    ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
        rate rewards C_star C_h z
        (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.birthIndex
          rate rewards C_star C_h z + 1) =
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.liveTail
        rate rewards C_star C_h z := by
  simp only [ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix,
    ReferenceFirstCollectionCorrectedSliceNumericalPrefix.liveTail,
    ReferenceFirstReplacementLiveFollowerPrefix.continuingTail,
    ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords]
  have htest :
      ReferenceCompleteLaterLiveComplementPrefixReplay.continuingTest
          (p := p) (rate := rate) =
        ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen := by
    funext r
    unfold ReferenceCompleteLaterLiveComplementPrefixReplay.continuingTest
      ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen
    cases r.output.preparation.coordinator with
    | live rv qv base chosen => cases chosen <;> rfl
    | first _ | collection _ _ _ _ _ | invalidCollectionCutoff | dagger => rfl
  rw [htest]

/-- Every event outcome supplies an excessive arm in the existing stopped
overflow union.  Positive prefixes use the assigned-attributed queue cover;
the zero prefix uses the initial installed queue and the stopped full prefix. -/
theorem nativeDownComputedOverflowEvent_subset_allArmOverflowEvent
    (u t : Fin p.T) :
    nativeDownComputedOverflowEvent rate rewards C_star C_h u t ⊆
      ReferenceFirstCollectionCorrectedNumericalOverflowSum.allArmOverflowEvent
        rate rewards C_star C_h := by
  classical
  intro z hzEvent
  change z ∈ ReferenceFirstCollectionCorrectedSliceNumericalPrefix.correctedCell
      rate rewards C_star C_h u t ∧ _ at hzEvent
  rcases hzEvent with ⟨hz, birth, P, hbirth, hborn, hSigma,
    j, hbj, current, hselection, hcurrentPayload,
    i, logged, cut, hdownInput, hdown, before, after, raw, M, scan,
    registers, lastService, haccepted, hM, hcase⟩
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let b := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.birthIndex
    rate rewards C_star C_h z
  let W := ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
    rate rewards C_star C_h z (b + 1)
  let N := 1 + W.length
  let V := (R.drop b).take N
  have hroot :=
    ReferenceFirstCorrectedNativeDownCalendarReplay.firstCell_native_down_calendar_replay
      rate rewards C_star C_h u t z hz
  rcases hroot with ⟨L, c, birth0, P0, hL, hc, hinputs, hlenL, hbirth0,
    hborn0, hSigma0, hqueues, hdownQueues, hVbirth, hNbound,
    htotal, hcollection, hdiag⟩
  have hbirthEq : birth = birth0 := Option.some.inj (hbirth.symm.trans hbirth0)
  subst birth
  have hpayloadEq : P = P0 :=
    ReferenceAssignmentPayloadChronology.installationBirth_payload_unique
      birth0 P P0 hborn hborn0
  have hcurrentPayload0 : current.view.payload = P0 := hcurrentPayload.trans hpayloadEq
  have hMeq : M = P0.downRecord i := by
    simpa only [hpayloadEq] using hM
  have haccepted0 : cut.outcome =
      ActiveFollowerDownAcceptance.LocalDownResult.accepted before after raw
        (P0.downRecord i) scan registers lastService := by
    simpa only [hMeq] using haccepted
  have hqInitial : (P0.downRecord i).val.q = P0.queues (P0.assignment.assigned i) := by
    exact (hdownQueues i).trans (hqueues (P0.assignment.assigned i)).symm
  have hdiagI := (hdiag j hbj i).2.2 current hselection
  have hdiagI' := by
    simpa only [ite_eq_left hcurrentPayload0] using hdiagI
  have hnative := hdiagI' logged before after cut raw (P0.downRecord i)
    scan registers lastService hdownInput hdown haccepted0
  rcases hnative with ⟨_, _, word, hmap, _hMroot, _hscan, hvpos, hvle,
    _, _, _, hword, _, _, hprefix, _⟩
  rcases hcase with hseed | ⟨k, middle, hkpos, hkA, hkchecked, hkcross⟩
  · have hseed0 : ((P0.downRecord i).val.q : ℝ) / (rate.n : ℝ) >
        1 / (32 * rate.eta.val) := by
      simpa only [hMeq] using hseed
    have hseedQueueNorm : (P0.queues (P0.assignment.assigned i) : ℝ) /
        (Q).n > 1 / (32 * (Q).eta) := by
      simpa only [ReferenceFirstLaunchNumericalCell.queueParameters] using
        (by rw [← hqInitial]; exact hseed0)
    have hseedCutoff : 32 * P0.queues (P0.assignment.assigned i) > (Q).D :=
      (RecordedQueueRun.overflowCutoff_iff Q _).mp (by
        exact hseedQueueNorm)
    let A0 := L ++ [c]
    have hlenL' : L.length = b := by simpa only [b] using hlenL
    have hlenA0 : A0.length = b + 1 := by simp [A0, hlenL']
    have htakeA0 : A0.take b = L := by
      change (L ++ [c]).take b = L
      rw [List.take_append, List.take_of_length_le (by omega : L.length ≤ b)]
      simp [hlenL']
    have hqueueL :
        (UnstoppedRecordedQueueComparison.unstoppedReplay Q L L.length
          (P0.assignment.assigned i)).2 = (P0.queues (P0.assignment.assigned i)) :=
      (hqueues (P0.assignment.assigned i)).symm
    have hcross : UnstoppedRecordedQueueComparison.replay_crosses_overflow Q A0 b := by
      refine ⟨P0.assignment.assigned i, ?_⟩
      have hsame :
          (UnstoppedRecordedQueueComparison.unstoppedReplay Q A0 b
            (P0.assignment.assigned i)).2 =
          (UnstoppedRecordedQueueComparison.unstoppedReplay Q L L.length
            (P0.assignment.assigned i)).2 := by
        simp [UnstoppedRecordedQueueComparison.unstoppedReplay, htakeA0]
      rw [hsame, hqueueL]
      exact hseedCutoff
    have hbpos : 1 ≤ b := by
      by_contra hnot
      have hbzero : b = 0 := by omega
      have hLnil : L = [] := by
        have hLlen : L.length = 0 := by omega
        cases L with
        | nil => rfl
        | cons x xs => simp at hLlen
      have hqzero : P0.queues (P0.assignment.assigned i) = 0 := by
        rw [← hqueueL, hLnil]
        simp [UnstoppedRecordedQueueComparison.unstoppedReplay, QueueReplay.replay]
      omega
    have hcrossExists : ∃ n, 1 ≤ n ∧ n ≤ A0.length ∧
        UnstoppedRecordedQueueComparison.replay_crosses_overflow Q A0 n :=
      ⟨b, hbpos, by rw [hlenA0]; omega, hcross⟩
    have hfirstle :
        UnstoppedRecordedQueueComparison.firstOverflowPrefix Q A0 ≤ b := by
      dsimp [UnstoppedRecordedQueueComparison.firstOverflowPrefix]
      rw [dite_eq_left hcrossExists]
      exact Nat.find_min' hcrossExists ⟨hbpos, by rw [hlenA0]; omega, hcross⟩
    have hprefixFlag : (RecordedQueueRun.run Q A0).overflow = true := by
      have hflag := UnstoppedRecordedQueueComparison.prefix_overflow_iff_first_overflow_prefix_le
        Q A0 A0.length (by simp)
      simpa only [List.take_length] using hflag.mpr (by
        exact hfirstle.trans (by rw [hlenA0]; omega))
    obtain ⟨a, hterminal⟩ :=
      (StoppedQueueBound.run_overflow_iff_terminal_threshold Q A0).1 hprefixFlag
    have hdetector :
        (((RecordedQueueRun.run Q A0).registers a).2 : ℝ) / (rate.n : ℝ) >
          1 / (32 * rate.eta.val) := by
      change StoppedQueueBound.normalizedBacklog Q (RecordedQueueRun.run Q A0) a > _ at hterminal
      simpa only [StoppedQueueBound.normalizedBacklog,
        ReferenceFirstLaunchNumericalCell.queueParameters] using hterminal
    have hread :
        ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout
          rate rewards C_star C_h (t.val + 1) z =
        some (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
          (RecordedQueueRun.run Q A0)) := by
      simp only [ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout,
        hinputs, Option.map_some, A0]
    have hend := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.endDate_bounds
      rate rewards C_star C_h u t z hz
    have hmember : z ∈
        ReferenceFirstCollectionCorrectedSliceNumericalPrefix.overflowEvent
          rate rewards C_star C_h u t a := by
      refine ⟨hz, t.val + 1, le_rfl, hend.1, _, hread, ?_⟩
      simpa only [ReferenceFirstLaunchNumericalCell.queueParameters,
        ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout] using hdetector
    exact Set.mem_iUnion.mpr ⟨a, Set.mem_iUnion.mpr ⟨u,
      Set.mem_iUnion.mpr ⟨t, hmember⟩⟩⟩
  · have hkA0 := hkA
    rw [hMeq, hword] at hkA0
    have hkWord : k ≤ word.length := hkA0
    have hVlen : V.length = N := by
      dsimp [V]
      rw [hVbirth]
      simp only [List.length_cons]
      change W.length + 1 = 1 + W.length
      omega
    have hlenV :
        (V.take (scan.endpoint - (P0.sigma.val + 1))).length =
          scan.endpoint - (P0.sigma.val + 1) := by
      rw [List.length_take, hVlen, Nat.min_eq_left hvle]
    have hmapLen := list_mapM_length_of_some
      (ReferenceFirstCorrectedAssignedArrivalPrefix.attributedArrival? P0 i)
      (V.take (scan.endpoint - (P0.sigma.val + 1))) word hmap
    rw [hlenV] at hmapLen
    have hwordLen' : word.length = scan.endpoint - (P0.sigma.val + 1) := by omega
    have hkV : k ≤ scan.endpoint - (P0.sigma.val + 1) := by
      rw [← hwordLen']
      exact hkWord
    have hkN : k ≤ N := hkV.trans hvle
    have htailEq : W = ReferenceFirstCollectionCorrectedSliceNumericalPrefix.liveTail
        rate rewards C_star C_h z := by
      simpa only [b, W] using continuingWindows_eq rate rewards C_star C_h z
    have hNvalue : N = 1 +
        (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.liveTail
          rate rewards C_star C_h z).length := by simp [N, htailEq]
    have hkBound : k ≤ 1 +
        (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.liveTail
          rate rewards C_star C_h z).length := by
      rw [← hNvalue]
      exact hkN
    obtain ⟨wordK, hmapK, hwordK⟩ := list_mapM_take_of_some
      (ReferenceFirstCorrectedAssignedArrivalPrefix.attributedArrival? P0 i)
      (V.take (scan.endpoint - (P0.sigma.val + 1))) word hmap k
    have hmapPrefix :
        ((R.drop b).take k).mapM
          (ReferenceFirstCorrectedAssignedArrivalPrefix.attributedArrival? P0 i) =
          some wordK := by
      have htakeV : V.take k = (R.drop b).take k := by
        dsimp [V]
        rw [List.take_take, Nat.min_eq_left hkN]
      have htakePrefix : (V.take (scan.endpoint - (P0.sigma.val + 1))).take k =
          V.take k := by
        rw [List.take_take, Nat.min_eq_left hkV]
      simpa only [htakePrefix, htakeV] using hmapK
    have hqInitial' : (P0.downRecord i).val.q =
        P0.queues (P0.assignment.assigned i) := hqInitial
    have hqueueReplay :
        (QueueReplay.replay (4 * rate.n) (0, P0.queues (P0.assignment.assigned i))
          wordK).2 = middle.registers.2 := by
      obtain ⟨middle0, hcheckRoot, _hdomain, hregisters⟩ := hprefix k
      have hkchecked0 := hkchecked
      rw [hMeq, hword] at hkchecked0
      have hmiddleEq : middle0 = middle := Except.ok.inj (hcheckRoot.symm.trans hkchecked0)
      rw [hmiddleEq] at hregisters
      rw [← hqInitial', hwordK]
      exact (congrArg Prod.snd hregisters).symm
    have hassigned :
        z ∈ ReferenceFirstCollectionCorrectedAssignedOverflowCover.assignedAttributedOverflowEvent
          rate rewards C_star C_h u t := by
      refine ⟨hz, birth0, P0, ?_, hborn0, hSigma0, Or.inl ?_⟩
      · simpa only [R, b, ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords]
          using hbirth0
      · refine ⟨i, k, wordK, hkpos, hkBound, hmapPrefix, ?_⟩
        rw [hqueueReplay]
        exact hkcross
    exact ReferenceFirstCollectionCorrectedAssignedOverflowCover.assignedAttributedOverflowEvent_subset_allArmOverflowEvent
      rate rewards C_star C_h u t hassigned

/-- The union over both cell indices is bounded under the unchanged original
source-input law by the existing all-arm estimate. This is an outer
`measureReal` bound; measurability of this new event is a separate producer. -/
theorem nativeDownComputedOverflowEvent_union_measure_le
    (control0 : TimeControl p) :
    (sourceInputLaw p).real
        (⋃ u : Fin p.T, ⋃ t : Fin p.T,
          nativeDownComputedOverflowEvent rate rewards C_star C_h u t) ≤
      2 * (p.K : ℝ) * ((p.T : ℝ) + 1) *
        Real.exp (-(CanonicalRecordingRates.beta p rate.eta.val) /
          (32 * rate.eta.val)) := by
  have hsubset :
      (⋃ u : Fin p.T, ⋃ t : Fin p.T,
        nativeDownComputedOverflowEvent rate rewards C_star C_h u t) ⊆
      ReferenceFirstCollectionCorrectedNumericalOverflowSum.allArmOverflowEvent
        rate rewards C_star C_h := by
    intro z hz
    simp only [Set.mem_iUnion] at hz
    obtain ⟨u, t, hzt⟩ := hz
    exact nativeDownComputedOverflowEvent_subset_allArmOverflowEvent
      rate rewards C_star C_h u t hzt
  calc
    (sourceInputLaw p).real
        (⋃ u : Fin p.T, ⋃ t : Fin p.T,
          nativeDownComputedOverflowEvent rate rewards C_star C_h u t) ≤
      (sourceInputLaw p).real
        (ReferenceFirstCollectionCorrectedNumericalOverflowSum.allArmOverflowEvent
          rate rewards C_star C_h) :=
        MeasureTheory.measureReal_mono (μ := sourceInputLaw p) hsubset (by finiteness)
    _ ≤ 2 * (p.K : ℝ) * ((p.T : ℝ) + 1) *
        Real.exp (-(CanonicalRecordingRates.beta p rate.eta.val) /
          (32 * rate.eta.val)) :=
      ReferenceFirstCollectionCorrectedNumericalOverflowSum.allArmOverflowEvent_measure_le
        rate rewards C_star C_h control0

end Bandits.Support.ReferenceFirstCorrectedNativeDownOverflowCover

end
