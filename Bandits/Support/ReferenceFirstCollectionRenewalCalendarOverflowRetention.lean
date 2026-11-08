/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionRenewalFutureSupportChain

import Mathlib.Tactic

/-!
# Actual calendar overflow retention

For a present prefix of the literal original calendar, an already detected
queue overflow freezes every integer register and appends one disabled zero
record for every remaining calendar date.  The first detecting update stays
in the prefix.

Sources: `sources/zip4/manuscript/04_slow_fast_learner.tex:140-188,245-290`,
`sources/zip4/manuscript/05_binary_transport.tex:354-431`, and
`sources/zip4/manuscript/06_interruptions.tex:391-426`.
-/

@[expose] public section
noncomputable section

open Bandits.Support
open ReferenceFirstCollectionRenewalFutureControlLaw
open ReferenceFirstCollectionRenewalFutureNumericalPrefix
open ReferenceFirstCollectionRenewalIncomingQueueMeasurability

namespace Bandits.Support.ReferenceFirstCollectionRenewalCalendarOverflowRetention

variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ) (u t : Fin p.T)

local notation "Z" => ReferenceFirstCollectionRenewalFutureControlLaw.Source
  rate rewards C_star C_h u t
local notation "Q" => _root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate
local notation "O" => _root_.Bandits.Support.ReferenceFirstCollectionRenewalFutureNumericalPrefix.futurePrefixReadout rate rewards C_star C_h u t

private theorem sourceRecords_length (z : Z) :
    (_root_.Bandits.Support.ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceRecords rate rewards C_star C_h u t z).length =
      p.T - _root_.Bandits.Support.ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceStart rate rewards C_star C_h u t z := by
  change (_root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.sourceRecords
      rate rewards C_star C_h u t z).length =
    p.T - ReferenceCompletePhysicalHistory.physicalStart rate z.val rewards C_star C_h
  rw [← _root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.start_eq_physicalStart
    rate rewards C_star C_h u t z]
  exact _root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.sourceRecords_length
    rate rewards C_star C_h u t z

private theorem calendarCells_length (n : ℕ) (z : Z)
    (hstart : _root_.Bandits.Support.ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceStart rate rewards C_star C_h u t z ≤ n)
    (hnT : n ≤ p.T) :
    (_root_.Bandits.Support.ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells rate rewards C_star C_h u t n z).length =
      n - _root_.Bandits.Support.ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceStart rate rewards C_star C_h u t z := by
  rw [_root_.Bandits.Support.ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells, List.length_map, List.length_take, sourceRecords_length]
  omega

private theorem mapM_id_length {α : Type*} {cells : List (Option α)}
    {inputs : List α} (h : cells.mapM id = some inputs) :
    inputs.length = cells.length := by
  induction cells generalizing inputs with
  | nil => simp at h; simp [h]
  | cons cell cells ih =>
    cases cell with
    | none => simp at h
    | some value =>
      simp only [List.mapM_cons] at h
      cases htail : cells.mapM id with
      | none => simp [htail] at h
      | some tail =>
        simp [htail] at h
        cases h
        simp [ih htail]

/-- The same actual `mapM id` lists used by the future readout split at the
earlier natural calendar date.  The appended list has exactly the elapsed
calendar length, derived from the complete original source horizon. -/
theorem actual_calendar_prefix_inputs (n k : ℕ) (z : Z)
    (hnStart : _root_.Bandits.Support.ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceStart rate rewards C_star C_h u t z ≤ n)
    (hnk : n ≤ k) (hkT : k ≤ p.T)
    (hk : (O k z).isSome = true) :
    ∃ inputsN inputsK suffix,
      _root_.Bandits.Support.ReferenceFirstCollectionRenewalFutureNumericalPrefix.optionalPrefixCells (_root_.Bandits.Support.ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells rate rewards C_star C_h u t n z) =
        some inputsN ∧
      _root_.Bandits.Support.ReferenceFirstCollectionRenewalFutureNumericalPrefix.optionalPrefixCells (_root_.Bandits.Support.ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells rate rewards C_star C_h u t k z) =
        some inputsK ∧
      (O n z) = some (stateReadout (RecordedQueueRun.run Q inputsN)) ∧
      (O k z) = some (stateReadout (RecordedQueueRun.run Q inputsK)) ∧
      inputsK = inputsN ++ suffix ∧ suffix.length = k - n := by
  have hp := _root_.Bandits.Support.ReferenceFirstCollectionRenewalFutureSupportChain.futurePrefixReadout_present_input_prefix rate rewards C_star C_h u t
    n k hnk z hk
  rcases hp with ⟨_, inputsN, inputsK, hinputsN, hinputsK, hprefix,
    hreadN, hreadK⟩
  rcases hprefix with ⟨suffix, hsplit⟩
  have hnT : n ≤ p.T := le_trans hnk hkT
  have hlenN := calendarCells_length rate rewards C_star C_h u t n z hnStart hnT
  have hstartK : _root_.Bandits.Support.ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceStart rate rewards C_star C_h u t z ≤ k := le_trans hnStart hnk
  have hlenK := calendarCells_length rate rewards C_star C_h u t k z hstartK hkT
  have hmapN :
      (_root_.Bandits.Support.ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells rate rewards C_star C_h u t n z).mapM id = some inputsN := by
    simpa [_root_.Bandits.Support.ReferenceFirstCollectionRenewalFutureNumericalPrefix.optionalPrefixCells] using hinputsN
  have hmapK :
      (_root_.Bandits.Support.ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells rate rewards C_star C_h u t k z).mapM id = some inputsK := by
    simpa [_root_.Bandits.Support.ReferenceFirstCollectionRenewalFutureNumericalPrefix.optionalPrefixCells] using hinputsK
  have hinputsNLength := mapM_id_length hmapN
  have hinputsKLength := mapM_id_length hmapK
  have hsuffixLength : suffix.length = k - n := by
    rw [← hsplit, List.length_append] at hinputsKLength
    rw [hinputsNLength, hlenN, hlenK] at hinputsKLength
    omega
  exact ⟨inputsN, inputsK, suffix, hinputsN, hinputsK, hreadN, hreadK,
    hsplit.symm, hsuffixLength⟩

private theorem execute_after_overflow_records (qp : RecordedQueueRun.Parameters)
    (rounds : List (RecordedQueueRun.RoundInput p.K))
    (state : RecordedQueueRun.RunState p.K) (hoverflow : state.overflow = true) :
    (RecordedQueueRun.execute qp rounds state).overflow = true ∧
    (∀ a, (RecordedQueueRun.execute qp rounds state).registers a = state.registers a) ∧
    (∀ a, (RecordedQueueRun.execute qp rounds state).records a =
      state.records a ++ List.replicate rounds.length (false, 0)) := by
  induction rounds generalizing state with
  | nil => simp [RecordedQueueRun.execute, hoverflow]
  | cons round rounds ih =>
    have hstep := RecordedQueueRun.step_after_overflow_preserves qp state round hoverflow
    have hnext : (RecordedQueueRun.step qp state round).overflow = true := by
      simp [RecordedQueueRun.step, hoverflow]
    obtain ⟨hflag, hregs, hrecords⟩ := ih (RecordedQueueRun.step qp state round) hnext
    have hstepRecords (a : Fin p.K) :
        (RecordedQueueRun.step qp state round).records a = state.records a ++ [(false, 0)] := by
      simp [RecordedQueueRun.step, (hstep a).2]
    refine ⟨hflag, ?_, ?_⟩
    · intro a
      calc
        (RecordedQueueRun.execute qp rounds (RecordedQueueRun.step qp state round)).registers a =
            (RecordedQueueRun.step qp state round).registers a := hregs a
        _ = state.registers a := (hstep a).1
    · intro a
      calc
        (RecordedQueueRun.execute qp rounds (RecordedQueueRun.step qp state round)).records a =
            (RecordedQueueRun.step qp state round).records a ++
              List.replicate rounds.length (false, 0) := hrecords a
        _ = state.records a ++ List.replicate (rounds.length + 1) (false, 0) := by
          rw [hstepRecords a]
          simp [List.append_assoc, List.replicate_succ]

/-- Once the literal prefix readout has its overflow flag set, every remaining
actual calendar date is recorded as `(false, 0)`.  Registers are unchanged;
the readout histories grow by the exact suffix length. -/
theorem actual_calendar_overflow_suffix_retention (n k : ℕ) (z : Z)
    (hnStart : _root_.Bandits.Support.ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceStart rate rewards C_star C_h u t z ≤ n)
    (hnk : n ≤ k) (hkT : k ≤ p.T)
    (hk : (O k z).isSome = true)
    (on : (Fin p.K → ℕ × ℕ) × (Bool × (Fin p.K → List (Bool × ℕ))))
    (hon : O n z = some on) (hoverflow : on.2.1 = true) :
    ∃ ok, O k z = some ok ∧ ok.2.1 = true ∧
      (∀ a, ok.1 a = on.1 a) ∧
      (∀ a, ok.2.2 a = on.2.2 a ++ List.replicate (k - n) (false, 0)) := by
  obtain ⟨inputsN, inputsK, suffix, _, _, hreadN, hreadK, hsplit, hlen⟩ :=
    actual_calendar_prefix_inputs rate rewards C_star C_h u t n k z hnStart hnk hkT hk
  have honReadout : on = stateReadout (RecordedQueueRun.run Q inputsN) :=
    Option.some.inj (hon.symm.trans hreadN)
  have hrunOverflow : (RecordedQueueRun.run Q inputsN).overflow = true := by
    change (stateReadout (RecordedQueueRun.run Q inputsN)).2.1 = true
    rw [← honReadout]
    exact hoverflow
  have hretain := RecordedQueueRun.execute_after_overflow_preserves Q suffix
    (RecordedQueueRun.run Q inputsN) hrunOverflow
  have hretainRecords := execute_after_overflow_records Q suffix
    (RecordedQueueRun.run Q inputsN) hrunOverflow
  have hrunAppend : RecordedQueueRun.run Q inputsK =
      RecordedQueueRun.execute Q suffix (RecordedQueueRun.run Q inputsN) := by
    calc
      RecordedQueueRun.run Q inputsK = RecordedQueueRun.run Q (inputsN ++ suffix) := by
        rw [hsplit]
      _ = RecordedQueueRun.execute Q suffix (RecordedQueueRun.run Q inputsN) := by
        simpa [RecordedQueueRun.run] using
          (CanonicalQueueProcess.execute_append Q inputsN suffix
            (RecordedQueueRun.initialState p.K))
  refine ⟨stateReadout (RecordedQueueRun.run Q inputsK), hreadK, ?_, ?_, ?_⟩
  · change (RecordedQueueRun.run Q inputsK).overflow = true
    rw [hrunAppend]
    exact hretain.1
  · intro a
    rw [honReadout]
    change (RecordedQueueRun.run Q inputsK).registers a =
      (RecordedQueueRun.run Q inputsN).registers a
    rw [hrunAppend]
    exact hretain.2 a
  · intro a
    rw [honReadout]
    change (RecordedQueueRun.run Q inputsK).records a =
      (RecordedQueueRun.run Q inputsN).records a ++
        List.replicate (k - n) (false, 0)
    rw [hrunAppend, ← hlen]
    exact hretainRecords.2.2 a

/-- The inclusive arm threshold is attained in `[n₀,k]` exactly when it holds
at the same present actual calendar readout at `k`.  The strict integer cutoff
and first detecting post-state are those of the existing stopped run. -/
theorem actual_calendar_threshold_iff (a : Fin p.K) (n0 k : ℕ) (z : Z)
    (hn0 : _root_.Bandits.Support.ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceStart rate rewards C_star C_h u t z ≤ n0)
    (hnk : n0 ≤ k) (hkT : k ≤ p.T)
    (hk : (O k z).isSome = true) :
    (∃ n, n0 ≤ n ∧ n ≤ k ∧ ∃ on, O n z = some on ∧
      ((on.1 a).2 : ℝ) / ((_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate).n : ℝ) > 1 / (32 * rate.eta.val)) ↔
    ∃ ok, O k z = some ok ∧
      ((ok.1 a).2 : ℝ) / ((_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate).n : ℝ) > 1 / (32 * rate.eta.val) := by
  constructor
  · rintro ⟨n, hn0n, hnk', on, hon, hthreshold⟩
    have hnStart := le_trans hn0 hn0n
    have hsource := actual_calendar_prefix_inputs rate rewards C_star C_h u t n k z
      hnStart hnk' hkT hk
    rcases hsource with ⟨inputsN, inputsK, suffix, _, _, hreadN, hreadK,
      hsplit, hlen⟩
    have honReadout : on = stateReadout (RecordedQueueRun.run Q inputsN) :=
      Option.some.inj (hon.symm.trans hreadN)
    have hthresholdQ : ((on.1 a).2 : ℝ) / ((_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate).n : ℝ) > 1 / (32 * (_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate).eta) := by
      simpa [ReferenceFirstLaunchNumericalCell.queueParameters] using hthreshold
    have hcut := (RecordedQueueRun.overflowCutoff_iff Q (on.1 a).2).mp hthresholdQ
    have hrunCut : ∃ i, 32 * ((RecordedQueueRun.run Q inputsN).registers i).2 > (_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate).D := by
      refine ⟨a, ?_⟩
      simpa [honReadout, stateReadout, _root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters] using hcut
    have hrunOverflow := (RecordedQueueRun.run_overflow_iff_cutoff Q inputsN).2 hrunCut
    have honOverflow : on.2.1 = true := by
      rw [honReadout]
      change (RecordedQueueRun.run Q inputsN).overflow = true
      exact hrunOverflow
    obtain ⟨ok, hok, hokflag, hregs, _⟩ :=
      actual_calendar_overflow_suffix_retention rate rewards C_star C_h u t n k z
        hnStart hnk' hkT hk on hon honOverflow
    refine ⟨ok, hok, ?_⟩
    have hthresholdEndQ : ((ok.1 a).2 : ℝ) / ((_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate).n : ℝ) > 1 / (32 * (_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate).eta) := by
      apply (RecordedQueueRun.overflowCutoff_iff Q (ok.1 a).2).2
      simpa [hregs a, _root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters] using hcut
    simpa [ReferenceFirstLaunchNumericalCell.queueParameters] using hthresholdEndQ
  · rintro ⟨ok, hok, hthreshold⟩
    exact ⟨k, hnk, le_rfl, ok, hok, hthreshold⟩

end Bandits.Support.ReferenceFirstCollectionRenewalCalendarOverflowRetention
