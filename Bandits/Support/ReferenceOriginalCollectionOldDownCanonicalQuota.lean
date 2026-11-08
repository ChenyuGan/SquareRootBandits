/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceOriginalCollectionOldDownPendingPrefix

import Lean.Elab.Tactic.Omega

/-!
# Original-source OLD DOWN canonical quota

Sources: `sources/zip4/manuscript/06_interruptions.tex:477-481`,
`sources/zip4/manuscript/05_binary_transport.tex:180-191`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:151-157`.

The threshold replay is tied to the original complete-suffix run and its
inherited DOWN bank. Its actual second completion gives checked retained
acceptance or literal fixed-awaited ambiguity. This yields the inclusive
first-bad-date prefix quota and the strict PRE quota while the receiver is OLD.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceFirstReplacementCollectionOldDownCallDates
open scoped Classical

namespace Bandits.Support.ReferenceOriginalCollectionOldDownCanonicalQuota

abbrev Parameters := ReferenceOriginalCollectionOldDownPendingPrefix.Parameters
abbrev RateInput := ReferenceOriginalCollectionOldDownPendingPrefix.RateInput
abbrev SourceInput (p : Parameters) :=
  ReferenceOriginalCollectionOldDownPendingPrefix.SourceInput p
abbrev GridRewardTable (p : Parameters) :=
  ReferenceOriginalCollectionOldDownPendingPrefix.GridRewardTable p
abbrev Record {p : Parameters} (rate : RateInput p) :=
  ReferenceOriginalCollectionOldDownPendingPrefix.Record (rate := rate)
abbrev DownRecord {p : Parameters} (rate : RateInput p) :=
  ReferenceOriginalCollectionOldDownPendingPrefix.DownRecord (rate := rate)

variable {p : Parameters}
variable (rate : RateInput p) (rewards : GridRewardTable p)
  (C_star C_h : ℝ)

/-- At an actual still-OLD choice, a prefix whose positive count equals the
real `Q - nD + Q` threshold has an actual completed second-bank diagnostic.
The same original cutoff bank is replayed, and the accepted pending-prefix
producer supplies the actual OLD, zero-inclusive awaited calls up to the
threshold. -/
public theorem actual_old_down_reached_threshold_diagnostic
    (z : SourceInput p) (e : ℕ) (i : Fin (p.m - 1)) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h
    match R[e]? with
    | none => True
    | some cut =>
      match cut.output.preparation.coordinator with
      | .live registers _ _ (.cutoffChosen _ _ _ _ _ _ _ _ _ _) =>
        let P := registers.payload
        let M := P.downRecord i
        let K := cut :: (R.drop (e + 1)).takeWhile
          (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
        ∀ a : Fin K.length, actualOldAt (K.get a) i M →
          ∃ (base : ReferencePrelaunchFollower.State p rate.eta)
            (baseMemory : ActiveFollowerLifecycle.LocalMemory p),
            cut.input.state.followers i = .ordinary base baseMemory ∧
            base.downBatch.pending.length < AffineBatchDecoder.quota p ∧
            0 < AffineBatchDecoder.quota p - base.downBatch.pending.length +
              AffineBatchDecoder.quota p ∧
            AffineBatchDecoder.quota p - base.downBatch.pending.length +
                AffineBatchDecoder.quota p ≤ 2 * AffineBatchDecoder.quota p ∧
            (ReferenceFollowerDownDecoderReplay.actualDownPositives i
              (K.take (a.val + 1))).length =
              ReferenceFirstReplacementCollectionOldDownCountOrAmbiguity.oldDownCount
                K (a.val + 1) i M ∧
            (∀ b : Fin K.length, b.val ≤ a.val →
              ∃ (k : Fin R.length)
                (selected : ReferenceActivePhysicalStep.Selection R[k.val].input),
                k.val = e + b.val ∧ R[k.val] = K.get b ∧
                R[k.val].output.preparation.coordinator.selection = some selected ∧
                selected.view.payload = P ∧ i ∈ selected.view.pendingAtChoice ∧
                actualOldAt (K.get b) i M ∧
                (ActiveFollowerDownAcceptance.downSelected p i R[k.val].input.row
                    R[k.val].input.time →
                  ReferenceCompleteAwaitedBatchSourceCoverage.originalDownAwaitedCallAt
                    rate R[k.val] i
                    (CoordinatorLocalArmChoice.storedDownFlatWord P i) ∧
                  ReferenceCompleteAwaitedBatchSourceCoverage.sourceDownAwaitedAt
                    rate rewards C_star C_h z i
                    (CoordinatorLocalArmChoice.storedDownFlatWord P i)
                    R[k.val].input.time)) ∧
            (∀ hthreshold :
                ReferenceFirstReplacementCollectionOldDownCountOrAmbiguity.oldDownCount
                    K (a.val + 1) i M =
                  AffineBatchDecoder.quota p - base.downBatch.pending.length +
                    AffineBatchDecoder.quota p,
              ∃ (record : Record rate)
                (logged : ReferencePrelaunchFollower.State p rate.eta)
                (diag : ReferenceDownReception.ReferenceDownCutOutput p rate),
                record ∈ K.take (a.val + 1) ∧
                (record.output.followers i).downInput = some logged ∧
                (record.output.followers i).down = some diag ∧
                diag.rawComparison.isSome = true ∧
                ReferenceFirstLiveDownCompletionReadout.completedDownBatch record i =
                  some ((ReferenceFollowerDownDecoderReplay.actualDownPositives i
                    (K.take (a.val + 1))).drop
                      (AffineBatchDecoder.quota p - base.downBatch.pending.length)) ∧
                diag.raw = AffineBatchDecoder.batchOutput
                  ((ReferenceFollowerDownDecoderReplay.actualDownPositives i
                    (K.take (a.val + 1))).drop
                      (AffineBatchDecoder.quota p - base.downBatch.pending.length)))
            ∧ ¬ ∃ (choice : ReferencePrelaunchFollower.State p rate.eta)
                (memory : ActiveFollowerLifecycle.LocalMemory p),
                (ReferenceFollowerFixedReply.actualChoice cut i).configuration =
                  .ordinary choice memory ∧ choice.lastDown = some M
      | _ => True := by
  dsimp only
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  cases hget : R[e]? with
  | none => trivial
  | some cut =>
    simp only
    obtain ⟨he, hcut⟩ := List.getElem?_eq_some_iff.mp hget
    subst cut
    let cut := R[e]'he
    cases hbranch : cut.output.preparation.coordinator with
    | first outcome => trivial
    | collection payload ledger clock cutoff outcome => trivial
    | invalidCollectionCutoff => trivial
    | dagger => trivial
    | live registers owned base outcome =>
      cases outcome with
      | continuingChosen dispatched hstart continuation selected => trivial
      | clockFailure failure hfailure => trivial
      | initializerFailure dispatched hstart checked hfailure => trivial
      | localFailure dispatched hstart failure => trivial
      | cutoffChosen dispatched hstart ledger hinitialization hledger hdomains
          hclock hpending hassignment selected =>
        dsimp only
        let P := registers.payload
        let M := P.downRecord i
        let K := cut :: (R.drop (e + 1)).takeWhile
          (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
        have hback :=
          ReferenceOriginalCollectionOldDownPendingPrefix.actual_cutoff_old_backward_positive_count
            rate rewards C_star C_h z e i
        have hprefix :=
          ReferenceOriginalCollectionOldDownPendingPrefix.actual_cutoff_old_pending_prefix
            rate rewards C_star C_h z e i
        have halready :=
          ReferenceOriginalCollectionOldDownPendingPrefix.actual_cutoff_already_current_has_no_old
            rate rewards C_star C_h z e i
        dsimp only at hback hprefix halready
        rw [show (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h)[e]? = some cut from hget] at hback hprefix halready
        dsimp only at hback hprefix halready
        rw [hbranch] at hback hprefix halready
        dsimp only at hback hprefix halready
        intro a holdA
        have hbank :=
          ReferenceOriginalCollectionOldDownChronology.actual_live_cutoff_old_down_bank_replay
            rate rewards C_star C_h z e (a.val + 1) i
        dsimp only at hbank
        rw [show (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h)[e]? = some cut from hget] at hbank
        dsimp only at hbank
        rw [hbranch] at hbank
        dsimp only at hbank
        have hnotCurrent : ¬ ∃ (choice : ReferencePrelaunchFollower.State p rate.eta)
            (memory : ActiveFollowerLifecycle.LocalMemory p),
            (ReferenceFollowerFixedReply.actualChoice cut i).configuration =
              .ordinary choice memory ∧ choice.lastDown = some M := by
          rintro ⟨choice, memory, hchoice, hcurrent⟩
          have hnoOld := halready choice memory hchoice hcurrent a
          exact hnoOld holdA
        have hcount :
            ReferenceFirstReplacementCollectionOldDownCountOrAmbiguity.oldDownCount
                K (a.val + 1) i M =
              (ReferenceFollowerDownDecoderReplay.actualDownPositives i
                (K.take (a.val + 1))).length := by
          exact hback a holdA (a.val + 1) (by omega)
        obtain ⟨base, state, baseMemory, memory, hbase, _hstate, _hfold, _hcollected,
          hquota, _hbaseStamps, _hpairCalls, _hcalendar, _hpairPositives,
          _hpositiveTimes, hcompletion⟩ := hbank
        refine ⟨base, baseMemory, hbase, hquota, ?_, ?_, hcount.symm, ?_, ?_, hnotCurrent⟩
        · omega
        · omega
        · intro b hba
          exact hprefix a holdA b hba
        · intro hthreshold
          have hpositiveLength :
              (ReferenceFollowerDownDecoderReplay.actualDownPositives i
                (K.take (a.val + 1))).length =
                AffineBatchDecoder.quota p - base.downBatch.pending.length +
                  AffineBatchDecoder.quota p := by
            exact hcount.symm.trans hthreshold
          obtain ⟨record, logged, diag, hrecord, hlogged, hdiag, hcompared,
            hcompleted, hraw⟩ := hcompletion hpositiveLength
          exact ⟨record, logged, diag, hrecord, hlogged, hdiag, hcompared,
            hcompleted, hraw⟩

/-- The actual first `Q - nD + Q` OLD-positive threshold in a date-gated
prefix is a real coordinate of the original cutoff run.  The pending length
`nD` is read from the inherited state at the actual cutoff. -/
public theorem actual_old_down_prefix_first_threshold
    (z : SourceInput p) (e : ℕ) (i : Fin (p.m - 1)) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h
    match R[e]? with
    | none => True
    | some cut =>
      match cut.output.preparation.coordinator with
      | .live registers _ _ (.cutoffChosen _ _ _ _ _ _ _ _ _ _) =>
        let P := registers.payload
        let M := P.downRecord i
        let K := cut :: (R.drop (e + 1)).takeWhile
          (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
        let beta := ReferenceCompleteSignedFirstBadCalendar.firstBadDate
          rate rewards C_star C_h z
        ∃ (base : ReferencePrelaunchFollower.State p rate.eta)
          (baseMemory : ActiveFollowerLifecycle.LocalMemory p),
          cut.input.state.followers i = .ordinary base baseMemory ∧
          base.downBatch.pending.length < AffineBatchDecoder.quota p ∧
          AffineBatchDecoder.quota p - base.downBatch.pending.length +
              AffineBatchDecoder.quota p ≤ 2 * AffineBatchDecoder.quota p ∧
          (∀ j : ℕ,
            ReferenceOriginalCollectionOldDownPendingPrefix.actualOldDownPrefixReadoutSum
                rate rewards C_star C_h z K j beta i =
              (ReferenceFirstReplacementCollectionOldDownCountOrAmbiguity.oldDownCount
                K (ReferenceOriginalCollectionOldDownPendingPrefix.actualOldDownPrefixLength
                  rate K j beta) i M : ℝ)) ∧
          ∀ j : ℕ, j ≤ K.length →
            AffineBatchDecoder.quota p - base.downBatch.pending.length +
                AffineBatchDecoder.quota p ≤
              ReferenceFirstReplacementCollectionOldDownCountOrAmbiguity.oldDownCount
                K j i M →
            ∃ a : Fin K.length,
              a.val < j ∧
              ReferenceFirstReplacementCollectionOldDownCountOrAmbiguity.oldDownCount
                  K (a.val + 1) i M =
                AffineBatchDecoder.quota p - base.downBatch.pending.length +
                  AffineBatchDecoder.quota p ∧
              (∀ b : ℕ, b ≤ a.val →
                ReferenceFirstReplacementCollectionOldDownCountOrAmbiguity.oldDownCount
                  K b i M <
                    AffineBatchDecoder.quota p - base.downBatch.pending.length +
                      AffineBatchDecoder.quota p) ∧
              actualOldAt (K.get a) i M
      | _ => True := by
  dsimp only
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  cases hget : R[e]? with
  | none => trivial
  | some cut =>
    simp only
    obtain ⟨he, hcut⟩ := List.getElem?_eq_some_iff.mp hget
    subst cut
    let cut := R[e]'he
    cases hbranch : cut.output.preparation.coordinator with
    | first outcome => trivial
    | collection payload ledger clock cutoff outcome => trivial
    | invalidCollectionCutoff => trivial
    | dagger => trivial
    | live registers owned base outcome =>
      cases outcome with
      | continuingChosen dispatched hstart continuation selected => trivial
      | clockFailure failure hfailure => trivial
      | initializerFailure dispatched hstart checked hfailure => trivial
      | localFailure dispatched hstart failure => trivial
      | cutoffChosen dispatched hstart ledger hinitialization hledger hdomains
          hclock hpending hassignment selected =>
        dsimp only
        let P := registers.payload
        let M := P.downRecord i
        let K := cut :: (R.drop (e + 1)).takeWhile
          (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
        have hbank :=
          ReferenceOriginalCollectionOldDownChronology.actual_live_cutoff_old_down_bank_replay
            rate rewards C_star C_h z e 0 i
        dsimp only at hbank
        rw [show (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h)[e]? = some cut from hget] at hbank
        dsimp only at hbank
        rw [hbranch] at hbank
        dsimp only at hbank
        obtain ⟨base, _state, baseMemory, _memory, hbase, _hstate, _hfold,
          _hcollected, hquota, _hbaseStamps, _hpairCalls, _hcalendar,
          _hpairPositives, _hpositiveTimes, _hcompletion⟩ := hbank
        refine ⟨base, baseMemory, hbase, hquota, ?_, ?_, ?_⟩
        · omega
        · intro j
          have hreadout :=
            ReferenceOriginalCollectionOldDownPendingPrefix.actual_cutoff_old_readout_eq_count
              rate rewards C_star C_h z e j i
          dsimp only at hreadout
          rw [show (ReferenceCompletePhysicalHistory.completeSuffixRecords
            rate z rewards C_star C_h)[e]? = some cut from hget] at hreadout
          dsimp only at hreadout
          rw [hbranch] at hreadout
          dsimp only at hreadout
          exact hreadout
        · intro j hj hreach
          let need := AffineBatchDecoder.quota p - base.downBatch.pending.length +
            AffineBatchDecoder.quota p
          have hneed : 0 < need := by
            dsimp [need]
            omega
          have hfirst :=
            ReferenceFirstReplacementCollectionOldDownCountOrAmbiguity.oldDownCount_small_or_first_threshold
              K j i M need hneed hj
          change need ≤ ReferenceFirstReplacementCollectionOldDownCountOrAmbiguity.oldDownCount
            K j i M at hreach
          rcases hfirst with hsmall | ⟨a, ha, hat, hbefore⟩
          · change ReferenceFirstReplacementCollectionOldDownCountOrAmbiguity.oldDownCount
              K j i M < need at hsmall
            exact False.elim ((not_lt_of_ge hreach) hsmall)
          · have hservice :=
              ReferenceFirstReplacementCollectionOldDownCountOrAmbiguity.oldDownServiceAt_of_first_threshold
                K i M a need (hbefore a.val (by omega)) hat
            refine ⟨a, ha, ?_, ?_, hservice.1⟩
            · simpa only [need] using hat
            · intro b hba
              simpa only [need] using hbefore b hba

/- A first-bad-date-gated source readout at the real inherited-bank
threshold identifies its first actual OLD service coordinate in the same
physical prefix.  The readout equality is the uncapped source equality from
the accepted pending-prefix producer. -/
public theorem actual_old_down_gated_readout_reaches_threshold
    (z : SourceInput p) (e : ℕ) (i : Fin (p.m - 1)) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h
    match R[e]? with
    | none => True
    | some cut =>
      match cut.output.preparation.coordinator with
      | .live registers _ _ (.cutoffChosen _ _ _ _ _ _ _ _ _ _) =>
        let P := registers.payload
        let M := P.downRecord i
        let K := cut :: (R.drop (e + 1)).takeWhile
          (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
        let beta := ReferenceCompleteSignedFirstBadCalendar.firstBadDate
          rate rewards C_star C_h z
        ∃ (base : ReferencePrelaunchFollower.State p rate.eta)
          (baseMemory : ActiveFollowerLifecycle.LocalMemory p),
          cut.input.state.followers i = .ordinary base baseMemory ∧
          base.downBatch.pending.length < AffineBatchDecoder.quota p ∧
          ∀ j : ℕ, j ≤ K.length →
            (AffineBatchDecoder.quota p - base.downBatch.pending.length +
                AffineBatchDecoder.quota p : ℝ) ≤
              ReferenceOriginalCollectionOldDownPendingPrefix.actualOldDownPrefixReadoutSum
                rate rewards C_star C_h z K j beta i →
            ∃ a : Fin K.length,
              a.val < ReferenceOriginalCollectionOldDownPendingPrefix.actualOldDownPrefixLength
                rate K j beta ∧
              ReferenceFirstReplacementCollectionOldDownCountOrAmbiguity.oldDownCount
                K (a.val + 1) i M =
                  AffineBatchDecoder.quota p - base.downBatch.pending.length +
                    AffineBatchDecoder.quota p ∧
              (∀ b : ℕ, b ≤ a.val →
                ReferenceFirstReplacementCollectionOldDownCountOrAmbiguity.oldDownCount
                  K b i M <
                    AffineBatchDecoder.quota p - base.downBatch.pending.length +
                      AffineBatchDecoder.quota p) ∧
              actualOldAt (K.get a) i M
      | _ => True := by
  dsimp only
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  cases hget : R[e]? with
  | none => trivial
  | some cut =>
    simp only
    obtain ⟨he, hcut⟩ := List.getElem?_eq_some_iff.mp hget
    subst cut
    let cut := R[e]'he
    cases hbranch : cut.output.preparation.coordinator with
    | first outcome => trivial
    | collection payload ledger clock cutoff outcome => trivial
    | invalidCollectionCutoff => trivial
    | dagger => trivial
    | live registers owned base outcome =>
      cases outcome with
      | continuingChosen dispatched hstart continuation selected => trivial
      | clockFailure failure hfailure => trivial
      | initializerFailure dispatched hstart checked hfailure => trivial
      | localFailure dispatched hstart failure => trivial
      | cutoffChosen dispatched hstart ledger hinitialization hledger hdomains
          hclock hpending hassignment selected =>
        dsimp only
        let P := registers.payload
        let M := P.downRecord i
        let K := cut :: (R.drop (e + 1)).takeWhile
          (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
        let beta := ReferenceCompleteSignedFirstBadCalendar.firstBadDate
          rate rewards C_star C_h z
        have hfirst := actual_old_down_prefix_first_threshold
          rate rewards C_star C_h z e i
        dsimp only at hfirst
        rw [show (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h)[e]? = some cut from hget] at hfirst
        dsimp only at hfirst
        rw [hbranch] at hfirst
        dsimp only at hfirst
        obtain ⟨base, baseMemory, hbase, hquota, _hneedle, hreadout, hthreshold⟩ := hfirst
        refine ⟨base, baseMemory, hbase, hquota, ?_⟩
        intro j hj hread
        let need := AffineBatchDecoder.quota p - base.downBatch.pending.length +
          AffineBatchDecoder.quota p
        let gateLength :=
          ReferenceOriginalCollectionOldDownPendingPrefix.actualOldDownPrefixLength
            rate K j beta
        have hgateLength : gateLength ≤ K.length := by
          dsimp only [gateLength,
            ReferenceOriginalCollectionOldDownPendingPrefix.actualOldDownPrefixLength]
          have hprefix :
              ((K.take j).takeWhile
                (fun r => r.input.time.val + 1 ≤ beta)) <+:
              K.take j := List.takeWhile_prefix _
          have htakeLength : (K.take j).length ≤ K.length := by
            simp only [List.length_take]
            omega
          exact hprefix.length_le.trans htakeLength
        have hread' := hread
        rw [hreadout j] at hread'
        rw [← Nat.cast_sub (Nat.le_of_lt hquota), ← Nat.cast_add] at hread'
        have hreadReal : (need : ℝ) ≤
            (ReferenceFirstReplacementCollectionOldDownCountOrAmbiguity.oldDownCount
              K gateLength i M : ℝ) := by
          simpa only [need, gateLength,
            ReferenceOriginalCollectionOldDownPendingPrefix.actualOldDownPrefixLength,
            K, M, beta] using hread'
        have hnat : need ≤
            ReferenceFirstReplacementCollectionOldDownCountOrAmbiguity.oldDownCount
              K gateLength i M := by
          exact (Nat.cast_le.mp hreadReal)
        obtain ⟨a, ha, hat, hbefore, hservice⟩ := hthreshold gateLength
          hgateLength hnat
        refine ⟨a, ?_, ?_, ?_, hservice⟩
        · simpa only [gateLength] using ha
        · simpa only [need] using hat
        · intro b hba
          simpa only [need] using hbefore b hba


private theorem positive_origin
    (records : List (Record rate)) (i : Fin (p.m - 1))
    (entry : AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p))
    (he : entry ∈ ReferenceFollowerDownDecoderReplay.actualDownPositives i records) :
    ∃ r ∈ records, entry.time = r.input.time ∧
      ActiveFollowerDownAcceptance.downSelected p i r.input.row r.input.time := by
  obtain ⟨call, hcall, hentry⟩ := List.mem_flatMap.mp he
  obtain ⟨r, hr, hcall⟩ := List.mem_filterMap.mp hcall
  have hel : AffineBatchDecoder.eligible call.2 := by
    by_contra hn
    simp only [AffineBatchDecoder.positiveAt,
      ActiveFollowerDownAcceptance.currentInputExtension, hn, ite_false,
      List.not_mem_nil] at hentry
  have heq : entry = ⟨call.1, call.2.sample⟩ := by
    simpa only [AffineBatchDecoder.positiveAt,
      ActiveFollowerDownAcceptance.currentInputExtension, hel, ite_true,
      List.mem_singleton, AffineBatchDecoder.entry] using hentry
  have hf := ReferenceDownCompletedAmbiguityMeasurability.actualDownCall_fields r i call hcall
  exact ⟨r, hr, (congrArg AffineBatchDecoder.Entry.time heq).trans hf.1,
    hf.2.2.mp hel.1⟩

private theorem down_selected_of_channel
    (row : CompletePublicTable.CompleteRow p) (t : Fin p.T) (i : Fin (p.m - 1))
    (h : ReferenceSelectedAffinePairLaw.selectedChannel p (row.2 t).1 = some (0, i)) :
    ActiveFollowerDownAcceptance.downSelected p i row t := by
  have hd : PublicDiscreteDraws.slotDraw (row.2 t).1 = PublicDiscreteDraws.downSlot := by
    by_contra hn
    unfold ReferenceSelectedAffinePairLaw.selectedChannel
      ReferenceSelectedAffinePairLaw.channelFromDraws at h
    simp only [ite_eq_right hn] at h
    by_cases hu : PublicDiscreteDraws.slotDraw (row.2 t).1 = PublicDiscreteDraws.upSlot
    · simp only [ite_eq_left hu] at h
      have hf := congrArg Prod.fst (Option.some.inj h)
      cases hf
    · simp only [ite_eq_right hu] at h
      cases h
  rw [ReferenceSelectedAffinePairLaw.selectedChannel_of_down p (row.2 t).1 hd] at h
  exact ⟨hd, (Prod.mk.inj (Option.some.inj h)).2⟩

/-- At the real inherited-bank threshold, the actual original completion
retains the current DOWN, or witnesses the literal whole-source fixed-awaited
DOWN ambiguity. All selected calls, including zeros, are derived internally. -/
public theorem actual_old_down_threshold_outcome
    (z : SourceInput p) (e : ℕ) (i : Fin (p.m - 1)) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    match R[e]? with
    | none => True
    | some cut =>
      match cut.output.preparation.coordinator with
      | .live registers _ _ (.cutoffChosen _ _ _ _ _ _ _ _ _ _) =>
        let P := registers.payload
        let M := P.downRecord i
        let K := cut :: (R.drop (e + 1)).takeWhile
          (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
        ∃ (base : ReferencePrelaunchFollower.State p rate.eta)
          (baseMemory : ActiveFollowerLifecycle.LocalMemory p),
          cut.input.state.followers i = .ordinary base baseMemory ∧
          base.downBatch.pending.length < AffineBatchDecoder.quota p ∧
          ∀ a : Fin K.length, actualOldAt (K.get a) i M →
            ReferenceFirstReplacementCollectionOldDownCountOrAmbiguity.oldDownCount
                K (a.val + 1) i M =
              AffineBatchDecoder.quota p - base.downBatch.pending.length +
                AffineBatchDecoder.quota p →
            ∃ b : Fin K.length, b.val ≤ a.val ∧
              (ReferenceAcceptedUpFollowerHistory.RetainedDown (K.get b) i M ∨
                ReferenceCompleteAwaitedBatchSourceCoverage.sourceDownFixedAwaitedCompletionAt
                  rate rewards C_star C_h z (K.get b).input.time)
      | _ => True := by
  dsimp only
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  cases hget : R[e]? with
  | none => trivial
  | some cut =>
    simp only
    obtain ⟨he, hcut⟩ := List.getElem?_eq_some_iff.mp hget
    subst cut
    let cut := R[e]'he
    cases hbranch : cut.output.preparation.coordinator with
    | first outcome => trivial
    | collection payload ledger clock cutoff outcome => trivial
    | invalidCollectionCutoff => trivial
    | dagger => trivial
    | live registers owned base outcome =>
      cases outcome with
      | continuingChosen dispatched hstart continuation selected => trivial
      | clockFailure failure hfailure => trivial
      | initializerFailure dispatched hstart checked hfailure => trivial
      | localFailure dispatched hstart failure => trivial
      | cutoffChosen dispatched hstart ledger hinitialization hledger hdomains
          hclock hpending hassignment selected =>
        dsimp only
        let P := registers.payload
        let M := P.downRecord i
        let K := cut :: (R.drop (e + 1)).takeWhile
          (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
        have hinit := ReferenceOriginalCollectionOldDownChronology.actual_live_cutoff_old_down_initialization
          rate rewards C_star C_h z e i
        have hbank0 := ReferenceOriginalCollectionOldDownChronology.actual_live_cutoff_old_down_bank_replay
          rate rewards C_star C_h z e 0 i
        have hdiagnostic := actual_old_down_reached_threshold_diagnostic
          rate rewards C_star C_h z e i
        dsimp only at hinit hbank0 hdiagnostic
        rw [show (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h)[e]? = some cut from hget] at hinit hbank0 hdiagnostic
        dsimp only at hinit hbank0 hdiagnostic
        rw [hbranch] at hinit hbank0 hdiagnostic
        dsimp only at hinit hbank0 hdiagnostic
        obtain ⟨_c, _birth, _hc, _hcP, _hstored, _hpend, _hcutoff, _hbirthLt,
          _hbirth, _hbirthTime, hscan, _hrest⟩ := hinit
        obtain ⟨base, _state0, baseMemory, _memory0, hbase, _hstate0, _hfold0,
          _hcollected0, hquota, _hrest0⟩ := hbank0
        refine ⟨base, baseMemory, hbase, hquota, ?_⟩
        intro a holdA hthreshold
        obtain ⟨base', baseMemory', hbase', _hquota', _hneedPos, _hneedLe,
          hcount, hprefix, hcompletion, _hnotCurrent⟩ := hdiagnostic a holdA
        have hbaseEq : base' = base :=
          (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj (hbase'.symm.trans hbase)).1
        subst base'
        obtain ⟨r, logged, diag, hr, hlogged, hdiag, hcompare, hcompleted, hraw⟩ :=
          hcompletion hthreshold
        obtain ⟨bn, hbn, hrb⟩ := List.mem_take_iff_getElem.mp hr
        let b : Fin K.length := ⟨bn, (lt_min_iff.mp hbn).2⟩
        have hba : b.val ≤ a.val := by
          dsimp only [b]
          exact Nat.le_of_lt_succ (lt_min_iff.mp hbn).1
        have hrb' : K.get b = r := hrb
        obtain ⟨kb, sb, hkb, hrecordB, hselectedB, hPB, hpendingB, holdB, hawaitedB⟩ :=
          hprefix b hba
        have hRr : (ReferenceCompletePhysicalHistory.completeSuffixRecords
            rate z rewards C_star C_h)[kb.val] = r := hrecordB.trans hrb'
        have hactual : ReferenceSourcePrefixHistoryFiltration.actualRecord
            rate rewards C_star C_h r.input.time z = some r := by
          have h := ReferenceOriginalCollectionOldDownChronology.actualRecord_at_completeSuffix_get
            rate rewards C_star C_h z kb.val kb.isLt
          simpa only [hRr] using h
        have hfields := ReferenceFirstLiveDownCompletionReadout.retained_call_fields
          r i logged diag hlogged hdiag hcompare
        have hdownR := hfields.1
        have hawR := (hawaitedB (by simpa only [hRr] using hdownR)).1
        rw [hRr] at hawR
        have htime (d : Fin K.length) (hda : d.val ≤ a.val) :
            (K.get d).input.time.val = cut.input.time.val + d.val := by
          obtain ⟨kd, _sd, hkd, hrd, _⟩ := hprefix d hda
          have hd := (ReferenceFirstReplacementCollectionOldDownSenderReadiness.complete_record_fields
            rate z rewards C_star C_h kd).1
          have hc := (ReferenceFirstReplacementCollectionOldDownSenderReadiness.complete_record_fields
            rate z rewards C_star C_h ⟨e, he⟩).1
          change (R[kd.val]).input.time.val = _ at hd
          rw [hrd, hkd] at hd
          change (K.get d).input.time.val = _ at hd
          change cut.input.time.val = ReferenceCompletePhysicalHistory.physicalStart
            rate z rewards C_star C_h + e at hc
          omega
        have htimeB : r.input.time.val = cut.input.time.val + b.val := by
          rw [← hrb']; exact htime b hba
        let positives := ReferenceFollowerDownDecoderReplay.actualDownPositives i (K.take (a.val + 1))
        let W := positives.drop (AffineBatchDecoder.quota p - base.downBatch.pending.length)
        have hsatisfies : AffineBatchDecoder.satisfies (AffineBatchDecoder.samples positives)
            (CoordinatorLocalArmChoice.storedDownFlatWord P i) := by
          apply ReferenceFirstReplacementCollectionOldDownCountOrAmbiguity.actualDownPositives_satisfy_sent_word
          intro rd hrd hdown
          obtain ⟨dn, hdn, hrdEq⟩ := List.mem_take_iff_getElem.mp hrd
          let d : Fin K.length := ⟨dn, (lt_min_iff.mp hdn).2⟩
          have hda : d.val ≤ a.val := by
            dsimp only [d]
            exact Nat.le_of_lt_succ (lt_min_iff.mp hdn).1
          obtain ⟨kd, _sd, _hkd, hkdR, _hs, _hP, _hp, _hold, haw⟩ := hprefix d hda
          have hrd' : (ReferenceCompletePhysicalHistory.completeSuffixRecords
              rate z rewards C_star C_h)[kd.val] = rd := hkdR.trans hrdEq
          have haw' := (haw (by simpa only [hrd'] using hdown)).1
          rw [hrd'] at haw'
          have hsaved := ReferenceLiteralSourceDecoderCoverage.awaitedDownAt_of_physicalAwaitedDownAt
            rd i _ ((ReferenceCompleteAwaitedBatchSourceCoverage.originalDownAwaitedCallAt_iff_physical
              rate rd i _).mp haw')
          obtain ⟨l, d, hl, hd, hc, _⟩ := hsaved
          obtain ⟨_l, _d, _M, _hl, _hd, _hsel, _hu, _hr, _hb, _hbuf, hsent, _⟩ := haw'
          exact ⟨l, d, hl, hd, hc, hsent⟩
        have hsatisfiesW : AffineBatchDecoder.satisfies (AffineBatchDecoder.samples W)
            (CoordinatorLocalArmChoice.storedDownFlatWord P i) := by
          apply (AffineBatchDecoder.satisfies_samples_iff _ _).2
          intro entry hentry
          exact (AffineBatchDecoder.satisfies_samples_iff _ _).1 hsatisfies
            entry (List.mem_of_mem_drop hentry)
        rcases ReferenceFirstReplacementCollectionOldDownCountOrAmbiguity.batchOutput_eq_sent_or_multiple
            W (CoordinatorLocalArmChoice.storedDownFlatWord P i) hsatisfiesW with hunique | hmultiple
        · have hrawCurrent : diag.raw = some (CoordinatorLocalArmChoice.storedDownFlatWord P i) :=
            hraw.trans hunique
          obtain ⟨choice, memory, hchoice, hu, hlast, hstatus, hbatch⟩ :=
            ReferenceFirstLiveDownCompletionReadout.retained_input_origin r i logged hlogged
          have hdecoded :
              (ActiveFollowerDownAcceptance.currentDecodeStep p i r.input.row r.input.time
                (ReferenceFollowerDownDecoderReplay.preparedOwnObservation r i) rate choice).2 =
              some (CoordinatorLocalArmChoice.storedDownFlatWord P i) := by
            have heq : ActiveFollowerDownAcceptance.currentDecodeStep p i r.input.row r.input.time
                (ReferenceFollowerDownDecoderReplay.preparedOwnObservation r i) rate choice =
              ActiveFollowerDownAcceptance.currentDecodeStep p i r.input.row r.input.time
                (ReferenceFollowerDownDecoderReplay.preparedOwnObservation r i) rate logged := by
              simp only [ActiveFollowerDownAcceptance.currentDecodeStep,
                ActiveFollowerDownAcceptance.currentRoundInput, hstatus, hbatch]
            rw [heq, ← hfields.2.2.2.2.2.1]
            exact hrawCurrent
          have hsender := ReferenceFirstReplacementCollectionOldDownSenderReadiness.selected_sender
            _ P i sb hselectedB hPB (hRr.symm ▸ hdownR) hpendingB
          have hexpected := hsender.2.2.1
          rw [hRr] at hexpected
          obtain ⟨l, d, cohort, hl, _hd, _hs, _hu, _hr, _hb, _hbuf, _hsent,
            hparse, hstrict, hdate⟩ := hawR
          have hlEq : l = logged := Option.some.inj (hl.symm.trans hlogged)
          subst l
          have hcohort : cohort = M := by
            rw [ReferenceFirstReplacementCollectionOldDownSenderReadiness.parse_stored_word P i] at hparse
            exact (Option.some.inj hparse).symm
          subst cohort
          have haccept : OrdinaryMessageCodec.acceptDown
              (ReferencePrelaunchFollower.codecParams p rate.eta)
              (ReferencePrelaunchFollower.acceptedStart choice) (r.input.time.val + 1) M := by
            have heq : ReferencePrelaunchFollower.acceptedStart logged =
                ReferencePrelaunchFollower.acceptedStart choice := by
              simp only [ReferencePrelaunchFollower.acceptedStart, hlast]
            exact ⟨heq ▸ hstrict, hdate⟩
          have hrecordFields := ReferenceFirstReplacementCollectionOldDownSenderReadiness.complete_record_fields
            rate z rewards C_star C_h kb
          have hrow : r.input.row = z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) := by
            have hrows : (ReferenceCompletePhysicalHistory.completeSuffixRecords
                rate z rewards C_star C_h)[kb.val].input.rows = z.1.2 := hrecordFields.2.1
            have hselected : (ReferenceCompletePhysicalHistory.completeSuffixRecords
                rate z rewards C_star C_h)[kb.val].input.selected =
                ActualInitializationPhysicalStep.selectedRowIndex p z := hrecordFields.2.2.1
            change r.input.rows r.input.selected = _
            rw [← hRr, hrows, hselected]
          have hscanR : FollowerCutoffScan.firstCutoff p rate.eta.val P.sigma
              (FollowerCutoffScan.completeRowProposalBit p rate.eta.val r.input.row) =
              cut.input.time.val + 1 := by rw [hrow]; exact hscan
          have hchoiceR : (ReferenceFollowerFixedReply.actualChoice R[kb.val] i).configuration =
              .ordinary choice memory := by rw [hRr]; exact hchoice
          obtain ⟨_accepted, _recovered, _post, _hscan, _hchecked, _hregisters,
            _hprefixRecovery, _hlast, _hstatusPost, _hbuffer, _hbatchPost,
            _hdiagRaw, _houtcome, _houtput, _hnext, hretained⟩ :=
            ReferenceFirstReplacementCollectionOldDownSenderReadiness.current_word_reception
              z rewards C_star C_h kb _ rfl i choice memory P (cut.input.time.val + 1)
              sb hselectedB hPB hchoiceR hu (hRr.symm ▸ hdownR)
              (hRr.symm ▸ hexpected) (hRr.symm ▸ haccept) (hRr.symm ▸ hscanR)
              (hRr.symm ▸ (show cut.input.time.val + 1 ≤ r.input.time.val + 1 by omega))
              (hRr.symm ▸ hdecoded)
          refine ⟨b, hba, Or.inl ?_⟩
          rw [← hrecordB]; exact hretained
        · refine ⟨b, hba, Or.inr ?_⟩
          rw [hrb']
          refine ⟨i, CoordinatorLocalArmChoice.storedDownFlatWord P i, W, cut.input.time,
            ?_, by omega, (ReferenceFirstLiveDownCompletionReadout.multipleSolutions_iff W).mp
              hmultiple.2.1, ?_, ?_⟩
          · unfold ReferenceCompleteAwaitedBatchSourceCoverage.sourceDownCompletedAt
            rw [hactual]
            exact (ReferenceLiteralAwaitedAmbiguityRowObservation.physicalDownCompletedAt_iff_completedDownBatch
              rate r i W).mpr hcompleted
          · intro entry hentry
            have hpos : entry ∈ positives := List.mem_of_mem_drop hentry
            obtain ⟨rd, hrd, hentryTime, hdown⟩ := positive_origin rate _ i entry hpos
            obtain ⟨dn, hdn, hrdEq⟩ := List.mem_take_iff_getElem.mp hrd
            let d : Fin K.length := ⟨dn, (lt_min_iff.mp hdn).2⟩
            have hda : d.val ≤ a.val := by
              dsimp only [d]
              exact Nat.le_of_lt_succ (lt_min_iff.mp hdn).1
            obtain ⟨kd, _sd, _hkd, hkdR, _hs, _hP, _hp, _hold, haw⟩ := hprefix d hda
            have hrd' : (ReferenceCompletePhysicalHistory.completeSuffixRecords
              rate z rewards C_star C_h)[kd.val] = rd := hkdR.trans hrdEq
            have hactualD := ReferenceOriginalCollectionOldDownChronology.actualRecord_at_completeSuffix_get
              rate rewards C_star C_h z kd.val kd.isLt
            rw [hrd', ← hentryTime] at hactualD
            have hentryLo : cut.input.time.val ≤ entry.time.val := by
              have ht : entry.time.val = cut.input.time.val + d.val := by
                rw [hentryTime]
                rw [← hrdEq]
                exact htime d hda
              omega
            have hentryHi : entry.time.val ≤ r.input.time.val := by
              have hprovenance :=
                ReferenceCompleteCompletedBankOriginalProvenance.completedDownBatch_original_entry_provenance
                  rate rewards C_star C_h z r.input.time r i W hactual hcompleted entry hentry
              rcases hprovenance with hpre | hsuf
              · obtain ⟨test, _ht, heq, hbefore, _⟩ := hpre
                have htEq := congrArg AffineBatchDecoder.Entry.time heq
                have hc := (ReferenceFirstReplacementCollectionOldDownSenderReadiness.complete_record_fields
                  rate z rewards C_star C_h ⟨e, he⟩).1
                change cut.input.time.val = _ at hc
                change test.time = entry.time at htEq
                rw [htEq] at hbefore
                omega
              · obtain ⟨_re, _hr, _hp, _hstart, hle, _⟩ := hsuf
                exact hle
            have haw' := (haw (by simpa only [hrd'] using hdown)).1
            rw [hrd'] at haw'
            obtain ⟨_l, _d, _M, _hl, _hd, _hs, _hu, _hr, _hb, _hbuf, hsent, _⟩ := haw'
            refine ⟨hentryLo, hentryHi, ?_⟩
            unfold ReferenceCompleteAwaitedBatchSourceCoverage.sourceDownSentAt
            rw [hactualD]
            exact hsent
          · intro v hv hvt hchannel
            let dn := v.val - cut.input.time.val
            have hdb : dn ≤ b.val := by dsimp only [dn]; omega
            have hdn : dn < K.length := lt_of_le_of_lt hdb b.isLt
            let d : Fin K.length := ⟨dn, hdn⟩
            have hda : d.val ≤ a.val := hdb.trans hba
            obtain ⟨kd, _sd, _hkd, hkdR, _hs, _hP, _hp, _hold, haw⟩ := hprefix d hda
            have htimeD : (R[kd.val]).input.time = v := by
              apply Fin.ext
              rw [hkdR, htime d hda]
              dsimp only [d, dn]
              omega
            have hf := ReferenceFirstReplacementCollectionOldDownSenderReadiness.complete_record_fields
              rate z rewards C_star C_h kd
            have hrowD : (R[kd.val]).input.row =
                z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) := by
              have hrows : R[kd.val].input.rows = z.1.2 := hf.2.1
              have hselected : R[kd.val].input.selected =
                  ActualInitializationPhysicalStep.selectedRowIndex p z := hf.2.2.1
              change (R[kd.val]).input.rows (R[kd.val]).input.selected = _
              rw [hrows, hselected]
            have hdownD : ActiveFollowerDownAcceptance.downSelected p i
                (R[kd.val]).input.row (R[kd.val]).input.time := by
              rw [hrowD, htimeD]
              exact down_selected_of_channel _ _ i hchannel
            have hawD := (haw hdownD).2
            rw [htimeD] at hawD
            exact hawD


private theorem gated_prefix_length_le
    (K : List (Record rate)) (j beta : ℕ) :
    ReferenceOriginalCollectionOldDownPendingPrefix.actualOldDownPrefixLength
      rate K j beta ≤ min j K.length := by
  have hp : ((K.take j).takeWhile (fun r => r.input.time.val + 1 ≤ beta)) <+:
      K.take j := List.takeWhile_prefix _
  simpa only [ReferenceOriginalCollectionOldDownPendingPrefix.actualOldDownPrefixLength,
    List.length_take] using hp.length_le

private theorem date_of_gated_prefix
    (K : List (Record rate)) (j beta : ℕ) (a : Fin K.length)
    (ha : a.val < ReferenceOriginalCollectionOldDownPendingPrefix.actualOldDownPrefixLength
      rate K j beta) :
    (K.get a).input.time.val + 1 ≤ beta := by
  let L := (K.take j).takeWhile (fun r => r.input.time.val + 1 ≤ beta)
  have haL : a.val < L.length := ha
  have hp : L <+: K := (List.takeWhile_prefix _).trans (List.take_prefix j K)
  have hentry : L[a.val] = K.get a := by
    exact hp.getElem haL
  have hdate := List.mem_takeWhile_imp (List.getElem_mem haL)
  rw [hentry] at hdate
  exact of_decide_eq_true hdate

/-- Canonical original-source OLD DOWN quota. Every inclusive first-bad-date
prefix has at most `2Q` counted observations. At every still-OLD choice through
that date, its strict physical past has fewer than `2Q`, as does the literal
source readout of that past. The detecting date is included and the physical
cutoff run is never truncated at the analytical first-bad date. -/
public theorem actual_old_down_canonical_quota
    (z : SourceInput p) (e : ℕ) (i : Fin (p.m - 1)) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    match R[e]? with
    | none => True
    | some cut =>
      match cut.output.preparation.coordinator with
      | .live registers _ _ (.cutoffChosen _ _ _ _ _ _ _ _ _ _) =>
        let P := registers.payload
        let M := P.downRecord i
        let K := cut :: (R.drop (e + 1)).takeWhile
          (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
        let beta := ReferenceCompleteSignedFirstBadCalendar.firstBadDate
          rate rewards C_star C_h z
        (∀ j : ℕ,
          ReferenceFirstReplacementCollectionOldDownCountOrAmbiguity.oldDownCount
              K (ReferenceOriginalCollectionOldDownPendingPrefix.actualOldDownPrefixLength
                rate K j beta) i M ≤ 2 * AffineBatchDecoder.quota p ∧
          ReferenceOriginalCollectionOldDownPendingPrefix.actualOldDownPrefixReadoutSum
              rate rewards C_star C_h z K j beta i ≤
            2 * (AffineBatchDecoder.quota p : ℝ)) ∧
        ∀ a : Fin K.length, actualOldAt (K.get a) i M →
          (K.get a).input.time.val + 1 ≤ beta →
          ReferenceFirstReplacementCollectionOldDownCountOrAmbiguity.oldDownCount
              K a.val i M < 2 * AffineBatchDecoder.quota p ∧
          ReferenceOriginalCollectionOldDownPendingPrefix.actualOldDownPrefixReadoutSum
              rate rewards C_star C_h z K a.val beta i <
            2 * (AffineBatchDecoder.quota p : ℝ)
      | _ => True := by
  dsimp only
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  cases hget : R[e]? with
  | none => trivial
  | some cut =>
    simp only
    obtain ⟨he, hcut⟩ := List.getElem?_eq_some_iff.mp hget
    subst cut
    let cut := R[e]'he
    cases hbranch : cut.output.preparation.coordinator with
    | first outcome => trivial
    | collection payload ledger clock cutoff outcome => trivial
    | invalidCollectionCutoff => trivial
    | dagger => trivial
    | live registers owned base outcome =>
      cases outcome with
      | continuingChosen dispatched hstart continuation selected => trivial
      | clockFailure failure hfailure => trivial
      | initializerFailure dispatched hstart checked hfailure => trivial
      | localFailure dispatched hstart failure => trivial
      | cutoffChosen dispatched hstart ledger hinitialization hledger hdomains
          hclock hpending hassignment selected =>
        dsimp only
        let P := registers.payload
        let M := P.downRecord i
        let K := cut :: (R.drop (e + 1)).takeWhile
          (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
        let beta := ReferenceCompleteSignedFirstBadCalendar.firstBadDate
          rate rewards C_star C_h z
        have houtcome := actual_old_down_threshold_outcome rate rewards C_star C_h z e i
        have hfirst := actual_old_down_prefix_first_threshold rate rewards C_star C_h z e i
        have hprefix := ReferenceOriginalCollectionOldDownPendingPrefix.actual_cutoff_old_pending_prefix
          rate rewards C_star C_h z e i
        have hfixed := ReferenceOriginalCollectionOldDownChronology.actual_live_cutoff_old_down_fixed_awaited_prefix
          rate rewards C_star C_h z e i
        dsimp only at houtcome hfirst hprefix hfixed
        rw [show (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h)[e]? = some cut from hget] at houtcome hfirst hprefix hfixed
        dsimp only at houtcome hfirst hprefix hfixed
        rw [hbranch] at houtcome hfirst hprefix hfixed
        dsimp only at houtcome hfirst hprefix hfixed
        obtain ⟨base, baseMemory, hbase, hquota, houtcome⟩ := houtcome
        obtain ⟨base', _baseMemory', hbase', _hquota', _hneedLe,
          hreadout, hthreshold⟩ := hfirst
        have hbaseEq : base' = base :=
          (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj (hbase'.symm.trans hbase)).1
        subst base'
        let need := AffineBatchDecoder.quota p - base.downBatch.pending.length +
          AffineBatchDecoder.quota p
        have hneedPos : 0 < need := by dsimp only [need]; omega
        have hneedLe : need ≤ 2 * AffineBatchDecoder.quota p := by dsimp only [need]; omega
        have hstrict : ∀ a : Fin K.length, actualOldAt (K.get a) i M →
            (K.get a).input.time.val + 1 ≤ beta →
            ReferenceFirstReplacementCollectionOldDownCountOrAmbiguity.oldDownCount
              K a.val i M < need := by
          intro a holdA hdateA
          by_contra hn
          have hreach : need ≤
              ReferenceFirstReplacementCollectionOldDownCountOrAmbiguity.oldDownCount
                K a.val i M := Nat.le_of_not_gt hn
          obtain ⟨f, hfa, hfat, _hbefore, holdF⟩ :=
            hthreshold a.val (Nat.le_of_lt a.isLt) hreach
          obtain ⟨b, hbf, hresult⟩ := houtcome f holdF hfat
          have hba : b.val < a.val := lt_of_le_of_lt hbf hfa
          obtain ⟨ka, sa, hka, hrecordA, hselectedA, hPA, _hpendingA, _holdA, _hawA⟩ :=
            hprefix a holdA a le_rfl
          obtain ⟨kb, _sb, hkb, hrecordB, _hselectedB, _hPB, _hpendingB, _holdB, _hawB⟩ :=
            hprefix a holdA b (Nat.le_of_lt hba)
          have hkab : kb.val < ka.val := by omega
          have htimeA : (K.get a).input.time.val =
              ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + ka.val := by
            rw [← hrecordA]
            exact (ReferenceFirstReplacementCollectionOldDownSenderReadiness.complete_record_fields
              rate z rewards C_star C_h ka).1
          have htimeB : (K.get b).input.time.val =
              ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + kb.val := by
            rw [← hrecordB]
            exact (ReferenceFirstReplacementCollectionOldDownSenderReadiness.complete_record_fields
              rate z rewards C_star C_h kb).1
          rcases hresult with hretained | hambiguity
          · obtain ⟨other, hother, _hrOther, hfields⟩ := hfixed a
            have heq : other = ka := Fin.ext (hother.trans hka.symm)
            subst other
            have hstored := (hfields sa hselectedA).2.1
            obtain ⟨choice, memory, hchoice, _hu, hnotCurrent⟩ := holdA
            have hchoiceA : (ReferenceFollowerFixedReply.actualChoice
                (ReferenceCompletePhysicalHistory.completeSuffixRecords
                  rate z rewards C_star C_h)[ka.val] i).configuration =
                  .ordinary choice memory := by rw [hrecordA]; exact hchoice
            have horder := ReferenceOriginalCollectionOldDownChronology.actual_stored_choice_current_or_older
              rate rewards C_star C_h z ka P hstored i choice memory hchoiceA
            have hstale : ReferencePrelaunchFollower.acceptedStart choice < M.val.sigma :=
              horder.resolve_left hnotCurrent
            have hretainedB : ReferenceAcceptedUpFollowerHistory.RetainedDown
                (ReferenceCompletePhysicalHistory.completeSuffixRecords
                  rate z rewards C_star C_h)[kb.val] i M := by
              rw [hrecordB]; exact hretained
            cases hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
                rate z rewards C_star C_h with
            | none =>
              have hbad := ka.isLt
              simp only [ReferenceCompletePhysicalHistory.completeSuffixRecords, hlaunch,
                dite_true, List.length_nil, Nat.not_lt_zero] at hbad
            | some initial =>
              have hchain := ReferenceCompletePhysicalHistory.completeSuffix_connected_on_launch
                rate z rewards C_star C_h initial hlaunch
              exact ReferenceFirstReplacementCollectionOldDownSenderReadiness.no_earlier_retained_down
                hchain ka i M choice memory hchoiceA hstale kb hkab hretainedB
          · have hdateB : (K.get b).input.time.val + 1 < beta := by omega
            have hgate := ReferenceCompleteSignedFirstBadCalendar.inclusive_gate_through_first_bad_date
              rate rewards C_star C_h z (K.get b).input.time (Nat.le_of_lt hdateB)
            have habsent := (ReferenceCompleteSignedFirstBadCalendar.strict_prefix_branch_absence
              rate rewards C_star C_h z (K.get b).input.time hdateB).1
            exact habsent ⟨hgate, Or.inr (Or.inl hambiguity)⟩
        have hinclusive : ∀ j : ℕ,
            ReferenceFirstReplacementCollectionOldDownCountOrAmbiguity.oldDownCount
              K (ReferenceOriginalCollectionOldDownPendingPrefix.actualOldDownPrefixLength
                rate K j beta) i M ≤ need := by
          intro j
          let g := ReferenceOriginalCollectionOldDownPendingPrefix.actualOldDownPrefixLength
            rate K j beta
          have hg : g ≤ K.length :=
            (gated_prefix_length_le rate K j beta).trans (Nat.min_le_right _ _)
          change ReferenceFirstReplacementCollectionOldDownCountOrAmbiguity.oldDownCount K g i M ≤ need
          by_contra hn
          have hreach : need + 1 ≤
              ReferenceFirstReplacementCollectionOldDownCountOrAmbiguity.oldDownCount K g i M := by omega
          obtain ⟨a, hag, hat, hbefore⟩ :=
            ReferenceFirstReplacementCollectionOldDownCountOrAmbiguity.exists_first_oldDownCount_threshold
              K g i M (need + 1) (by omega) hg hreach
          have hservice :=
            ReferenceFirstReplacementCollectionOldDownCountOrAmbiguity.oldDownServiceAt_of_first_threshold
              K i M a (need + 1) (hbefore a.val le_rfl) hat
          have hdate := date_of_gated_prefix rate K j beta a hag
          have hsmall := hstrict a hservice.1 hdate
          have hincrement :=
            ReferenceFirstReplacementCollectionOldDownCountOrAmbiguity.oldDownCount_succ_le
              K a.val i M a.isLt
          omega
        constructor
        · intro j
          have hnat := (hinclusive j).trans hneedLe
          refine ⟨hnat, ?_⟩
          rw [hreadout j]
          have hreal :
              (ReferenceFirstReplacementCollectionOldDownCountOrAmbiguity.oldDownCount
                K (ReferenceOriginalCollectionOldDownPendingPrefix.actualOldDownPrefixLength
                  rate K j beta) i M : ℝ) ≤ (2 * AffineBatchDecoder.quota p : ℕ) :=
            Nat.cast_le.mpr hnat
          simpa only [Nat.cast_mul, Nat.cast_ofNat] using hreal
        · intro a holdA hdateA
          have hnat : ReferenceFirstReplacementCollectionOldDownCountOrAmbiguity.oldDownCount
              K a.val i M < 2 * AffineBatchDecoder.quota p :=
            lt_of_lt_of_le (hstrict a holdA hdateA) hneedLe
          refine ⟨hnat, ?_⟩
          rw [hreadout a.val]
          have hlength := (gated_prefix_length_le rate K a.val beta).trans (Nat.min_le_left _ _)
          have hmono := ReferenceFirstReplacementCollectionOldDownCountOrAmbiguity.oldDownCount_mono
            K _ a.val i M hlength
          have hnat' := lt_of_le_of_lt hmono hnat
          have hreal :
              (ReferenceFirstReplacementCollectionOldDownCountOrAmbiguity.oldDownCount
                K (ReferenceOriginalCollectionOldDownPendingPrefix.actualOldDownPrefixLength
                  rate K a.val beta) i M : ℝ) < (2 * AffineBatchDecoder.quota p : ℕ) :=
            Nat.cast_lt.mpr hnat'
          simpa only [Nat.cast_mul, Nat.cast_ofNat] using hreal

end Bandits.Support.ReferenceOriginalCollectionOldDownCanonicalQuota

end
