/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCorrectedNextInstallationNumericalSeed
public import Bandits.Support.ReferenceFirstCollectionCorrectedNumericalOverflowSum

import Mathlib.Tactic

/-!
# Literal stored outside-queue overflow on the first corrected slice

This module covers only threshold crossings in actual stored outside-arm
registers during the first corrected replacement slice. The queue projection
reads the coordinator's live registers or initialized collection ledger; it
does not substitute an unstopped replay for a missing register.

Sources: `04_slow_fast_learner.tex:157-187,256-290`,
`06_interruptions.tex:355-361,391-408,425-426`, and
`appendix_a_local_protocol.tex:28-64` in `sources/zip4/manuscript/`.
-/

@[expose] public section
noncomputable section

open Bandits.Support ConstructorDimensions
open BootstrapPrivateRoundStreams (SourceInput)
open ReferenceFirstCollectionCorrectedSliceNumericalPrefix
  (correctedCell sourceRecords sourceStart birthIndex liveTail cutoffDelta endDate
    prefixInputs prefixReadout overflowEvent)
open scoped Classical

namespace Bandits.Support.ReferenceFirstCollectionCorrectedStoredOutsideOverflowCover

variable {p : Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ)

local notation "X" => SourceInput p
local notation "Q" => ReferenceFirstLaunchNumericalCell.queueParameters rate
local notation "Record" => ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)
local notation "Input" => RecordedQueueRun.RoundInput p.K

/-- Read only an actual outside-arm queue stored by the record's coordinator.
Missing and slow-arm registers remain absent. -/
def storedOutsideQueue (r : Record) (a : Fin p.K) : Option ℕ :=
  match r.output.next.coordinator with
  | .live rv qv _ =>
      if h : a ∉ rv.payload.slowSet.val then
        some (qv.queue ⟨a, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, h⟩⟩)
      else none
  | .collection P lf _ =>
      if _h : a ∉ P.slowSet.val then
        (lf.currentRegisters a).map CoordinatorCollectionLedger.CurrentRegister.queue
      else none
  | .first | .dagger => none

/-- The literal first-slice event of a stored outside queue above the cap. -/
def storedOutsideOverflowEvent (u t : Fin p.T) : Set X :=
  {z | z ∈ correctedCell rate rewards C_star C_h u t ∧
    ∃ (k : ℕ) (r : Record) (a : Fin p.K) (q : ℕ),
      (sourceRecords rate rewards C_star C_h z)[k]? = some r ∧
      birthIndex rate rewards C_star C_h z ≤ k ∧
      k < birthIndex rate rewards C_star C_h z + 1 +
        (liveTail rate rewards C_star C_h z).length + cutoffDelta rate rewards C_star C_h z ∧
      storedOutsideQueue rate r a = some q ∧
      (q : ℝ) / (rate.n : ℝ) > 1 / (32 * rate.eta.val)}

/-- Literal actual birth outputs whose next coordinator is the absorbing
dagger. Their stored-queue projection is absent. -/
def firstCellBirthDagger (u t : Fin p.T) : Set X :=
  {z | z ∈ correctedCell rate rewards C_star C_h u t ∧
    ∃ birth : Record,
      (sourceRecords rate rewards C_star C_h z)[birthIndex rate rewards C_star C_h z]? =
        some birth ∧
      ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z =
        some birth ∧ birth.output.next.coordinator = .dagger}

private theorem event_of_present_prefix_crossing
    (u t : Fin p.T) (z : X)
    (hz : z ∈ correctedCell rate rewards C_star C_h u t)
    (n0 : ℕ) (hn0 : t.val + 1 ≤ n0)
    (hne : n0 ≤ endDate rate rewards C_star C_h t z)
    (inputs : List Input)
    (hinputs : prefixInputs rate rewards C_star C_h n0 z = some inputs)
    (hlen : inputs.length = n0 - sourceStart rate rewards C_star C_h z)
    (hfull : UnstoppedRecordedQueueComparison.replay_crosses_overflow
      Q inputs inputs.length) :
    ∃ a : Fin p.K, z ∈ overflowEvent rate rewards C_star C_h u t a := by
  let s := sourceStart rate rewards C_star C_h z
  let b := birthIndex rate rewards C_star C_h z
  let h := UnstoppedRecordedQueueComparison.firstOverflowPrefix Q inputs
  have htime : s + b = t.val :=
    ReferenceFirstCollectionCorrectedSliceNumericalPrefix.firstCell_birth_time
      rate rewards C_star C_h u t z hz
  have hlenpos : 0 < inputs.length := by rw [hlen]; omega
  have hex : ∃ n, 1 ≤ n ∧ n ≤ inputs.length ∧
      UnstoppedRecordedQueueComparison.replay_crosses_overflow Q inputs n :=
    ⟨inputs.length, by omega, le_rfl, hfull⟩
  have hfirstle : h ≤ inputs.length := by
    dsimp [h, UnstoppedRecordedQueueComparison.firstOverflowPrefix]
    rw [dite_eq_left hex]
    exact Nat.find_min' hex ⟨by omega, le_rfl, hfull⟩
  have hfirstpos : 0 < h :=
    UnstoppedRecordedQueueComparison.first_overflow_prefix_pos Q inputs
  obtain ⟨a₀, hcross₀⟩ :=
    UnstoppedRecordedQueueComparison.replay_crosses_overflow_at_first Q inputs hfirstle
  have hlen' : inputs.length = n0 - s := by simpa [s] using hlen
  have hmle : s + h ≤ n0 := by omega
  by_cases hearly : h ≤ b
  · let m := t.val + 1
    have hmstart : t.val + 1 ≤ m := le_rfl
    have hmend : m ≤ n0 := by change t.val + 1 ≤ n0; exact hn0
    obtain ⟨inputsM, hM, hMlen, hMread⟩ :=
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.firstCell_prefix_inputs
        rate rewards C_star C_h u t z hz m hmstart (hmend.trans hne)
    obtain ⟨suffix, hjoin, _hsuffix⟩ :=
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.firstCell_prefix_append
        rate rewards C_star C_h u t z hz m n0 hmstart hmend hne inputsM inputs
        hM hinputs
    have htake : inputsM = inputs.take inputsM.length := by
      rw [hjoin]
      simp
    have hMlen' : inputsM.length = m - s := by simpa [s] using hMlen
    have hlenM : inputsM.length = b + 1 := by
      rw [hMlen']
      dsimp [m]
      omega
    have htake' : inputsM = inputs.take (b + 1) := by rw [htake, hlenM]
    have hrun := (UnstoppedRecordedQueueComparison.prefix_state_comparison
      Q inputs (b + 1) (by rw [hlen']; omega)).1 a₀
    have hmin : min (b + 1) h = h := Nat.min_eq_right (by omega)
    rw [← htake', hmin] at hrun
    let on := ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
      (RecordedQueueRun.run Q inputsM)
    have hon : prefixReadout rate rewards C_star C_h m z = some on := by
      simpa only [on] using hMread
    have hcrossM : ((on.1 a₀).2 : ℝ) /
        ((ReferenceFirstLaunchNumericalCell.queueParameters rate).n : ℝ) >
          1 / (32 * rate.eta.val) := by
      have hq : (on.1 a₀).2 =
          (UnstoppedRecordedQueueComparison.unstoppedReplay Q inputs h a₀).2 := by
        change ((RecordedQueueRun.run Q inputsM).registers a₀).2 = _
        exact congrArg Prod.snd hrun
      have hcut : 32 * (on.1 a₀).2 >
          (ReferenceFirstLaunchNumericalCell.queueParameters rate).D := by
        rw [hq]
        exact hcross₀
      have hnorm := (RecordedQueueRun.overflowCutoff_iff Q (on.1 a₀).2).mpr hcut
      change _ > 1 / (32 * rate.eta.val) at hnorm
      exact hnorm
    have hflag :=
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefix_threshold_overflow
        rate rewards C_star C_h m z a₀ on hon hcrossM
    obtain ⟨oe, hoe, heq, _hflag, _hrecords⟩ :=
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.firstCell_overflow_endpoint
        rate rewards C_star C_h u t z hz m hmstart (hmend.trans hne) on hon hflag
    have hcrossE : ((oe.1 a₀).2 : ℝ) /
        ((ReferenceFirstLaunchNumericalCell.queueParameters rate).n : ℝ) >
          1 / (32 * rate.eta.val) := by
      rw [heq]
      exact hcrossM
    refine ⟨a₀, ?_⟩
    exact (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.overflowEvent_iff_endpoint
      rate rewards C_star C_h u t a₀ z).mpr ⟨hz, oe, hoe, hcrossE⟩
  · let m := s + h
    have hmstart : t.val + 1 ≤ m := by dsimp [m]; rw [← htime]; omega
    have hmend : m ≤ n0 := hmle
    obtain ⟨inputsM, hM, hMlen, hMread⟩ :=
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.firstCell_prefix_inputs
        rate rewards C_star C_h u t z hz m hmstart (hmend.trans hne)
    obtain ⟨suffix, hjoin, _hsuffix⟩ :=
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.firstCell_prefix_append
        rate rewards C_star C_h u t z hz m n0 hmstart hmend hne inputsM inputs
        hM hinputs
    have htake : inputsM = inputs.take inputsM.length := by
      rw [hjoin]
      simp
    have hMlen' : inputsM.length = m - s := by simpa [s] using hMlen
    have hlenM : inputsM.length = h := by
      rw [hMlen']
      dsimp [m]
      omega
    have htake' : inputsM = inputs.take h := by rw [htake, hlenM]
    have hrun := (UnstoppedRecordedQueueComparison.prefix_state_comparison
      Q inputs h (by rw [hlen']; omega)).1 a₀
    have hmin : min h h = h := min_self h
    rw [← htake', hmin] at hrun
    let on := ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
      (RecordedQueueRun.run Q inputsM)
    have hon : prefixReadout rate rewards C_star C_h m z = some on := by
      simpa only [on] using hMread
    have hcrossM : ((on.1 a₀).2 : ℝ) /
        ((ReferenceFirstLaunchNumericalCell.queueParameters rate).n : ℝ) >
          1 / (32 * rate.eta.val) := by
      have hq : (on.1 a₀).2 =
          (UnstoppedRecordedQueueComparison.unstoppedReplay Q inputs h a₀).2 := by
        change ((RecordedQueueRun.run Q inputsM).registers a₀).2 = _
        exact congrArg Prod.snd hrun
      have hcut : 32 * (on.1 a₀).2 >
          (ReferenceFirstLaunchNumericalCell.queueParameters rate).D := by
        rw [hq]
        exact hcross₀
      have hnorm := (RecordedQueueRun.overflowCutoff_iff Q (on.1 a₀).2).mpr hcut
      change _ > 1 / (32 * rate.eta.val) at hnorm
      exact hnorm
    have hflag :=
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefix_threshold_overflow
        rate rewards C_star C_h m z a₀ on hon hcrossM
    obtain ⟨oe, hoe, heq, _hflag, _hrecords⟩ :=
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.firstCell_overflow_endpoint
        rate rewards C_star C_h u t z hz m hmstart (hmend.trans hne) on hon hflag
    have hcrossE : ((oe.1 a₀).2 : ℝ) /
        ((ReferenceFirstLaunchNumericalCell.queueParameters rate).n : ℝ) >
          1 / (32 * rate.eta.val) := by
      rw [heq]
      exact hcrossM
    refine ⟨a₀, ?_⟩
    exact (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.overflowEvent_iff_endpoint
      rate rewards C_star C_h u t a₀ z).mpr ⟨hz, oe, hoe, hcrossE⟩


private theorem stored_replay_crossing
    (inputs : List Input) (a : Fin p.K) (q : ℕ)
    (hqueue : q =
      (UnstoppedRecordedQueueComparison.unstoppedReplay Q inputs inputs.length a).2)
    (hcross : (q : ℝ) / (rate.n : ℝ) > 1 / (32 * rate.eta.val)) :
    UnstoppedRecordedQueueComparison.replay_crosses_overflow Q inputs inputs.length := by
  have hnorm :
      ((UnstoppedRecordedQueueComparison.unstoppedReplay Q inputs inputs.length a).2 : ℝ) /
        ((ReferenceFirstLaunchNumericalCell.queueParameters rate).n : ℝ) >
          1 / (32 * (ReferenceFirstLaunchNumericalCell.queueParameters rate).eta) := by
    change _ > 1 / (32 * rate.eta.val)
    rw [← hqueue]
    exact hcross
  exact (UnstoppedRecordedQueueComparison.replay_crosses_overflow_iff_normalized
    Q inputs inputs.length).2 ⟨a, hnorm⟩

private theorem stored_prefix_event
    (u t : Fin p.T) (z : X)
    (hz : z ∈ correctedCell rate rewards C_star C_h u t)
    (n0 : ℕ) (hn0 : t.val + 1 ≤ n0)
    (hne : n0 ≤ endDate rate rewards C_star C_h t z)
    (inputs : List Input)
    (hinputs : prefixInputs rate rewards C_star C_h n0 z = some inputs)
    (hlen : inputs.length = n0 - sourceStart rate rewards C_star C_h z)
    (a : Fin p.K) (q : ℕ)
    (hqueue : q =
      (UnstoppedRecordedQueueComparison.unstoppedReplay Q inputs inputs.length a).2)
    (hcross : (q : ℝ) / (rate.n : ℝ) > 1 / (32 * rate.eta.val)) :
    ∃ a₀ : Fin p.K, z ∈ overflowEvent rate rewards C_star C_h u t a₀ := by
  exact event_of_present_prefix_crossing rate rewards C_star C_h u t z hz n0 hn0 hne
    inputs hinputs hlen (stored_replay_crossing rate inputs a q hqueue hcross)

private theorem continuing_windows_eq (z : X) :
    ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
      rate rewards C_star C_h z
      (birthIndex rate rewards C_star C_h z + 1) =
    liveTail rate rewards C_star C_h z := by
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

/-- Actual stored outside queues in the first corrected replacement slice
are covered by the existing numerical union over detecting arms. -/
theorem storedOutsideOverflowEvent_subset_arm_union (u t : Fin p.T) :
    storedOutsideOverflowEvent rate rewards C_star C_h u t ⊆
      ⋃ a : Fin p.K, overflowEvent rate rewards C_star C_h u t a := by
  classical
  intro z hzEvent
  change z ∈ correctedCell rate rewards C_star C_h u t ∧ _ at hzEvent
  obtain ⟨hz, k, r, a, q, hrecord, hbirthBound, hindexBound, hstored, hcross⟩ := hzEvent
  let R := sourceRecords rate rewards C_star C_h z
  let s := sourceStart rate rewards C_star C_h z
  let b := birthIndex rate rewards C_star C_h z
  let W0 := liveTail rate rewards C_star C_h z
  let delta := cutoffDelta rate rewards C_star C_h z
  let e := b + 1 + W0.length
  change R[k]? = some r at hrecord
  obtain ⟨hk, hget⟩ := List.getElem?_eq_some_iff.mp hrecord
  have hstoredActual : storedOutsideQueue rate r a = some q := hstored
  have htime : s + b = t.val := by
    dsimp [s, b]
    exact ReferenceFirstCollectionCorrectedSliceNumericalPrefix.firstCell_birth_time
      rate rewards C_star C_h u t z hz
  have hdelta_le : delta ≤ 1 := by
    dsimp [delta]
    unfold cutoffDelta
    split
    · rename_i rec hrec
      split <;> omega
    · omega
  have hrange : k < e + delta := by
    change k < b + 1 + W0.length + delta at hindexBound
    dsimp [e]
    exact hindexBound
  obtain ⟨Lc, cc, birth, hpastC, hcellC, hprefixC, hlenC, hbsubC,
    htimeC, henabledC, hbirthC, hactualC, hdateC, hrowsC, hselectedC,
    hrewardsC, hcurrentC, hnextC⟩ :=
      ReferenceFirstCollectionCorrectedCurrentNumericalOutput.firstCell_current_output
        rate rewards C_star C_h u t z hz
  obtain ⟨Lk, ck, birthK, hpastK, hcellK, hprefixK, hlenK, hbsubK,
    htimeK, henabledK, hbirthK, hactualK, hdateK, hrowsK, hselectedK,
    hrewardsK, _hcurrentK, _hnextK, hcontK⟩ :=
      ReferenceFirstCollectionCorrectedOutsideCutoffNumericalJoin.firstCell_outside_cutoff_numerical_join
        rate rewards C_star C_h u t z hz
  have hbirthEq : birthK = birth := Option.some.inj (hactualK.symm.trans hactualC)
  have hpastEq : Lk = Lc := Option.some.inj (hpastK.symm.trans hpastC)
  have hcellEq : ck = cc := Option.some.inj (hcellK.symm.trans hcellC)
  subst birthK
  subst Lk
  subst ck
  have hbirthActual : R[b]? = some birth := by
    change (sourceRecords rate rewards C_star C_h z)[b]? = some birth
    exact hbirthC
  cases hprepBirth : birth.output.preparation.coordinator <;>
    simp only [hprepBirth] at hcurrentC
  rename_i old ledger clock cutoff outcome
  cases outcome <;> simp only at hcurrentC
  rename_i core consistent started hstart instruction hi output hlocal clockData installed selection
  obtain ⟨_hinstTime, _hkind, _hinstall, _hpay, _hsigma, _hvector,
    _hvectorRow, _hreconstruction, _hall, _hfollowers, _hcomplement,
    _hrate, _hreward, _hco, _hconfiguration, hseedC⟩ := hcurrentC
  cases hnextBirth : birth.output.next.coordinator with
  | live rout qout beta =>
      simp only [hnextBirth] at hseedC
      obtain ⟨_hpayload, _hbase, recording, serviced, pending, finished,
        _hrecording, _hservice, _hconfirmation, _hfinish, _houtput, hqueuesBirth⟩ := hseedC
      by_cases hkb : k = b
      · have hrecordAtB : R[b]? = some r := by simpa [hkb] using hrecord
        have hrecordBirth : r = birth :=
          Option.some.inj (hrecordAtB.symm.trans hbirthActual)
        have hstoredBirth : storedOutsideQueue rate birth a = some q := by
          rw [← hrecordBirth]
          exact hstoredActual
        have ha : a ∉ rout.payload.slowSet.val := by
          by_contra hmem
          simp [storedOutsideQueue, hnextBirth, hmem] at hstoredBirth
        let j : CanonicalFastSampling.FastArm rout.payload.slowSet :=
          ⟨a, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ha⟩⟩
        have hqueue : q =
            (UnstoppedRecordedQueueComparison.unstoppedReplay Q (Lc ++ [cc])
              (Lc ++ [cc]).length a).2 := by
          have hsome : some (qout.queue j) = some q := by
            simpa [storedOutsideQueue, hnextBirth, ha, j] using hstoredBirth
          have hstoredEq : qout.queue j = q := Option.some.inj hsome
          exact hstoredEq.symm.trans (congrArg Prod.snd (hqueuesBirth j).1)
        have hlenInput : (Lc ++ [cc]).length =
            (t.val + 1) - sourceStart rate rewards C_star C_h z := by
          simp only [List.length_append, List.length_singleton]
          omega
        have hEnd : t.val + 1 ≤ endDate rate rewards C_star C_h t z :=
          (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.endDate_bounds
            rate rewards C_star C_h u t z hz).1
        obtain ⟨det, hevent⟩ := stored_prefix_event rate rewards C_star C_h u t z hz
          (t.val + 1) le_rfl hEnd (Lc ++ [cc]) hprefixC hlenInput a q hqueue hcross
        exact Set.mem_iUnion.mpr ⟨det, hevent⟩
      · have hbklt : b < k := by omega
        have hlenR := ReferenceCompletePhysicalHistory.completeSuffixRecords_length
          rate z rewards C_star C_h
        change R.length = p.T - s at hlenR
        have hsucc : t.val + 1 < p.T := by omega
        obtain ⟨_hsigma, htailK⟩ := hcontK rout qout beta hnextBirth
        obtain ⟨next, hk1, hstate, hlater, _hnextRecord, _hnextState,
          hB, hbound, _hT, _htimes, hallv, hprefixEnd, hAlen, hAdate,
          rE, qE, hpE, hnextLive, hinputLive, hvaluesEnd, hboundary⟩ := htailK hsucc
        let W := ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
          rate rewards C_star C_h z (b + 1)
        let B := ReferenceCompleteLaterLiveComplementPrefixReplay.prefixCells
          rewards C_star C_h z ⟨b + 1, hk1⟩ rout qout beta hstate hlater
        let n := W.length
        let eK := b + 1 + n
        let A := (Lc ++ [cc]) ++ B
        have hW : W = W0 := by
          dsimp [W, W0]
          exact continuing_windows_eq rate rewards C_star C_h z
        have hWlen : W.length = W0.length := congrArg List.length hW
        have hEindex : e = eK := by
          dsimp [e, eK, n]
          rw [hWlen]
        by_cases hkTail : k < e
        · let v := k - b
          have hvpos : 0 < v := by dsimp [v]; omega
          have hvle : v ≤ W.length := by
            rw [hWlen]
            dsimp [v, e, W0] at hkTail ⊢
            omega
          obtain ⟨hprefixV, hAlenV, hAdateV, _hrecordTimes, houtputs⟩ := hallv v hvle
          obtain ⟨rv, qv, hp, hout, hin, hqueuesV⟩ := houtputs
          let jidx : Fin W.length := ⟨v - 1, by omega⟩
          let Wtail := ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R b
          have hWtail : W = Wtail := by
            simpa [W, Wtail, W0, R, b, liveTail, sourceRecords,
              ReferenceFirstCollectionCorrectedSliceNumericalPrefix.liveTail] using hW
          have hjtail : v - 1 < Wtail.length := by rw [← hWtail]; exact jidx.isLt
          have hidx : b + 1 + (v - 1) = k := by dsimp [v]; omega
          have hgetTail := ReferenceFirstReplacementLiveFollowerPrefix.continuingTail_get
            R b ⟨v - 1, hjtail⟩
          rw [hidx] at hgetTail
          have hWget : R[k]? = some (W.get jidx) := by
            have hgetTail' : R[k]? = some (Wtail.get ⟨v - 1, hjtail⟩) := hgetTail
            have hgetValues : W.get jidx = Wtail.get ⟨v - 1, hjtail⟩ := by
              have hgetElem : W[jidx.val]? = Wtail[(v - 1)]? := by
                exact congrArg (fun xs : List Record => xs[v - 1]?) hWtail
              have hWsome : W[jidx.val]? = some (W.get jidx) := by
                exact List.getElem?_eq_getElem jidx.isLt
              have hWtailSome : Wtail[(v - 1)]? =
                  some (Wtail.get ⟨v - 1, hjtail⟩) := by
                exact List.getElem?_eq_getElem hjtail
              rw [hWsome, hWtailSome] at hgetElem
              exact Option.some.inj hgetElem
            rw [hgetValues.symm] at hgetTail'
            exact hgetTail'
          have hrEq : r = W.get jidx := Option.some.inj (hrecord.symm.trans hWget)
          have hcoord : (W.get jidx).output.next.coordinator = .live rv qv beta := by
            have h := hout hvpos
            simpa only [List.get_eq_getElem, jidx] using h
          rw [hrEq] at hstoredActual
          have hstoredAtRecord : storedOutsideQueue rate (W.get jidx) a = some q := by
            exact hstoredActual
          have hcoordIndex : (W[↑jidx]).output.next.coordinator = .live rv qv beta := by
            simpa using hcoord
          have haRv : a ∉ rv.payload.slowSet.val := by
            by_contra hmem
            have hnone : storedOutsideQueue rate (W.get jidx) a = none := by
              unfold storedOutsideQueue
              rw [hcoord]
              simp [hmem]
            rw [hnone] at hstoredAtRecord
            contradiction
          have ha : a ∉ rout.payload.slowSet.val := by
            intro hmem
            apply haRv
            rw [hp]
            exact hmem
          let j : CanonicalFastSampling.FastArm rout.payload.slowSet :=
            ⟨a, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ha⟩⟩
          have hqueue : q =
              (UnstoppedRecordedQueueComparison.unstoppedReplay Q
                ((Lc ++ [cc]) ++ B.take v)
                ((Lc ++ [cc]) ++ B.take v).length a).2 := by
            let jv : CanonicalFastSampling.FastArm rv.payload.slowSet :=
              ⟨a, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, haRv⟩⟩
            have hsome : some (qv.queue jv) = some q := by
              have h := hstoredAtRecord
              unfold storedOutsideQueue at h
              rw [hcoord] at h
              simpa [storedOutsideQueue, haRv, jv] using h
            have hstoredEq := Option.some.inj hsome
            have hqueueReplay : qv.queue jv =
                (UnstoppedRecordedQueueComparison.unstoppedReplay Q
                  ((Lc ++ [cc]) ++ B.take v)
                  ((Lc ++ [cc]) ++ B.take v).length a).2 := by
              have hpair := (hqueuesV j).1
              simpa [jv] using congrArg Prod.snd hpair
            exact hstoredEq.symm.trans (by simpa using hqueueReplay)
          have hdate : t.val + 1 ≤ t.val + 1 + v := by omega
          have hEnd : t.val + 1 + v ≤ endDate rate rewards C_star C_h t z := by
            unfold endDate
            rw [← hWlen]
            omega
          have hlenInput : ((Lc ++ [cc]) ++ B.take v).length =
              (t.val + 1 + v) - sourceStart rate rewards C_star C_h z := by
            have hdate' : s + ((Lc ++ [cc]) ++ B.take v).length = t.val + 1 + v := by
              simpa only [s] using hAdateV
            omega
          obtain ⟨det, hevent⟩ := stored_prefix_event rate rewards C_star C_h u t z hz
            (t.val + 1 + v) hdate hEnd ((Lc ++ [cc]) ++ B.take v)
            hprefixV hlenInput a q hqueue hcross
          exact Set.mem_iUnion.mpr ⟨det, hevent⟩
        · have hkeq : k = e := by omega
          have hdeltaEq : delta = 1 := by dsimp [e] at hrange; omega
          rcases hboundary with hEndR | ⟨heCut, chosen, hchosen, hprepared, hcutData⟩
          · have hEndEq : e = R.length := hEindex.trans hEndR
            have hnone : R[e]? = none := by
              rw [hEndEq]
              exact List.getElem?_eq_none (Nat.le_refl _)
            have hdeltaZero : delta = 0 := by
              dsimp [delta]
              unfold cutoffDelta
              rw [show (sourceRecords rate rewards C_star C_h z)[b + 1 +
                (liveTail rate rewards C_star C_h z).length]? = none by
                  simpa [e, W0] using hnone]
            omega
          · revert hcutData
            cases chosen with
            | clockFailure =>
                intro hcutData
                exfalso
                simp at hcutData
            | initializerFailure =>
                intro hcutData
                exfalso
                simp at hcutData
            | localFailure =>
                intro hcutData
                exfalso
                simp at hcutData
            | continuingChosen =>
                intro hcutData
                exfalso
                simp at hcutData
            | cutoffChosen dispatched hstart ledger hinit hcand hdomain hclock
                hpending hno selected =>
                intro hcutData
                let cut : Record := R[eK]'heCut
                let tau : Fin p.T := cut.input.time
                let uc : ℕ := tau.val + 1
                obtain ⟨htau, htau', huc, hfirstCutoff, seg, I, hseg, hentry,
                  hpayload, hpre, hI, hchecked, hassignment, hIsigma, hIcutoff,
                  hfreeze, hbase, hnonempty, hpartition, hexit, hfold,
                  hcalendar, hcount, hnonzero, hknown, hfollowers, _hassigned, c_cut,
                  hcell, hcollection, hprefixCut, hcellEnabled, hcellRate,
                  hreward, recording, started, decoded, bank, lf, clock, hrecordCut,
                  hrun, hstartLedger, hreceive, hdecoded, hfinish, hclockFinish,
                  hnextCollection, hfailure, hbaseScore, hgamma, _harrival, hfirstUpdate,
                  hfinal⟩ := hcutData
                let cut : Record := R[eK]'heCut
                have hrootIndex : k = eK := hkeq.trans hEindex
                have hrootRecord : R[eK]? = some r := by
                  simpa [hrootIndex] using hrecord
                have hcutRecord : R[eK]? = some cut :=
                  List.getElem?_eq_getElem heCut
                have hrCut : r = cut := Option.some.inj (hrootRecord.symm.trans hcutRecord)
                have hstoredCut : storedOutsideQueue rate cut a = some q := by
                  rw [← hrCut]
                  exact hstoredActual
                have hstoredCut' :
                    (if _h : a ∉ rout.payload.slowSet.val then
                      (lf.currentRegisters a).map
                        CoordinatorCollectionLedger.CurrentRegister.queue
                     else none) = some q := by
                  unfold storedOutsideQueue at hstoredCut
                  rw [hnextCollection] at hstoredCut
                  exact hstoredCut
                have ha : a ∉ rout.payload.slowSet.val := by
                  by_contra hmem
                  simp [hmem] at hstoredCut'
                let j : CanonicalFastSampling.FastArm rout.payload.slowSet :=
                  ⟨a, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ha⟩⟩
                obtain ⟨_hrecordEq, _hplusEq, _hcutRegisters, hcur, _hincrement⟩ :=
                  hfirstUpdate j
                have hmapStored :
                    (lf.currentRegisters a).map CoordinatorCollectionLedger.CurrentRegister.queue =
                      some q := by
                  simpa [ha] using hstoredCut'
                have hmapQueue :
                    (lf.currentRegisters a).map CoordinatorCollectionLedger.CurrentRegister.queue =
                      some ((UnstoppedRecordedQueueComparison.unstoppedReplay Q
                        (A ++ [c_cut]) (A ++ [c_cut]).length a).2) := by
                  have hmap := congrArg
                    (fun x => x.map CoordinatorCollectionLedger.CurrentRegister.queue) hcur
                  simpa [j, A] using hmap
                have hqueue : q =
                    (UnstoppedRecordedQueueComparison.unstoppedReplay Q
                      (A ++ [c_cut]) (A ++ [c_cut]).length a).2 := by
                  exact (Option.some.inj (hmapQueue.symm.trans hmapStored)).symm
                have htimeCut : tau.val = t.val + 1 + W.length := by
                  simpa [tau, cut, n, eK] using htau'
                have hWlive : W.length =
                    (liveTail rate rewards C_star C_h z).length := by
                  simpa [W0] using hWlen
                have hcutoffEq : cutoffDelta rate rewards C_star C_h z = 1 := by
                  simpa [delta] using hdeltaEq
                have hdate : t.val + 1 ≤ tau.val + 1 := by omega
                have hEnd : tau.val + 1 ≤ endDate rate rewards C_star C_h t z := by
                  unfold endDate
                  rw [hcutoffEq, ← hWlive, htimeCut]
                have hlistLen : (A ++ [c_cut]).length = A.length + 1 := by simp
                have hsourceDate : s + (A ++ [c_cut]).length = tau.val + 1 := by
                  rw [hlistLen]
                  have hAlen' : A.length = b + 1 + W.length := by
                    simpa [A, eK, n] using hAlen
                  have hAdate' : s + A.length = t.val + 1 + W.length := by
                    rw [hAlen']
                    simpa [s, b, W] using hAdate
                  calc
                    s + (A.length + 1) = (s + A.length) + 1 := by omega
                    _ = (t.val + 1 + W.length) + 1 := by rw [hAdate']
                    _ = tau.val + 1 := by rw [htimeCut]
                have hlenInput : (A ++ [c_cut]).length =
                    (tau.val + 1) - sourceStart rate rewards C_star C_h z := by
                  unfold s at hsourceDate
                  omega
                obtain ⟨det, hevent⟩ := stored_prefix_event rate rewards C_star C_h u t z hz
                  (tau.val + 1) hdate hEnd (A ++ [c_cut]) hprefixCut
                  hlenInput a q hqueue hcross
                exact Set.mem_iUnion.mpr ⟨det, hevent⟩
  | dagger =>
      simp only [hnextBirth] at hseedC
      by_cases hkb : k = b
      · have hrecordBirth : R[b]? = some birth := hbirthActual
        have hrecordAtB : R[b]? = some r := by simpa [hkb] using hrecord
        have hrecordEq : r = birth :=
          Option.some.inj (hrecordAtB.symm.trans hrecordBirth)
        have hstoredBirth : storedOutsideQueue rate birth a = some q := by
          rw [← hrecordEq]
          exact hstoredActual
        simp [storedOutsideQueue, hnextBirth] at hstoredBirth
      · have hbklt : b < k := by omega
        have hlenR := ReferenceCompletePhysicalHistory.completeSuffixRecords_length
          rate z rewards C_star C_h
        change R.length = p.T - s at hlenR
        have hsucc : t.val + 1 < p.T := by omega
        obtain ⟨next, hnextRecord, hnextActual, hnextTime, hnextState,
          _hnextRows, _hnextSelected, _hnextRewards⟩ := hnextC hsucc
        have hstateDag : next.input.state.coordinator = .dagger := by
          exact (congrArg ReferenceActivePhysicalStep.State.coordinator hnextState).trans hnextBirth
        have hprepNext : next.output.preparation.coordinator =
            ReferenceActivePhysicalStep.dispatch next.input := by
          rw [next.output_eq]
          rfl
        have hprepDag : next.output.preparation.coordinator = .dagger :=
          hprepNext.trans
            (ReferenceActivePhysicalStep.dispatch_dagger next.input hstateDag)
        have htailEmpty :
            ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R b = [] := by
          unfold ReferenceFirstReplacementLiveFollowerPrefix.continuingTail
          apply List.takeWhile_eq_nil_iff.mpr
          intro hlen
          have hget : (R.drop (b + 1)).get ⟨0, hlen⟩ = next := by
            have he := List.getElem?_eq_getElem hlen
            simp only [List.getElem?_drop, Nat.add_zero] at he
            have hnextRecord' : R[b + 1]? = some next := by
              simpa [R, b] using hnextRecord
            rw [hnextRecord'] at he
            exact (Option.some.inj he).symm
          rw [hget]
          simp [ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen, hprepDag]
        have hW0Empty : W0 = [] := by
          simpa [W0, R, b, liveTail, sourceRecords,
            ReferenceFirstCollectionCorrectedSliceNumericalPrefix.liveTail] using htailEmpty
        have hLiveEmpty : liveTail rate rewards C_star C_h z = [] := by
          simpa [W0] using hW0Empty
        have hdeltaZero : delta = 0 := by
          have hnone : (sourceRecords rate rewards C_star C_h z)[birthIndex rate rewards C_star C_h z + 1 +
              (liveTail rate rewards C_star C_h z).length]? = some next := by
            rw [hLiveEmpty]
            simpa [R, b] using hnextRecord
          dsimp [delta]
          unfold cutoffDelta
          rw [hnone]
          simp [hprepDag]
        have hkeq : k = b := by
          have hrange' : k < birthIndex rate rewards C_star C_h z + 1 +
              (liveTail rate rewards C_star C_h z).length +
              cutoffDelta rate rewards C_star C_h z := hindexBound
          have hcutoffZero : cutoffDelta rate rewards C_star C_h z = 0 := by
            simpa [delta] using hdeltaZero
          rw [hLiveEmpty, hcutoffZero] at hrange'
          have hrangeB : k < b + 1 := by simpa [b] using hrange'
          omega
        omega
  | first =>
      simp only [hnextBirth] at hseedC
  | collection payload ledger proposal =>
      simp only [hnextBirth] at hseedC

end Bandits.Support.ReferenceFirstCollectionCorrectedStoredOutsideOverflowCover
