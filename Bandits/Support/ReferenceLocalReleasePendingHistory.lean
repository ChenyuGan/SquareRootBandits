/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceLocalReleaseGateChronology
public import Bandits.Support.ReferenceLocalReleasePendingPredecessor

/-!
# Actual local release pending histories

Sources: `sources/zip4/manuscript/05_binary_transport.tex:74-88,293-348`,
`sources/zip4/manuscript/06_interruptions.tex:246-297,435-492`,
`sources/zip4/manuscript/07_public_setup.tex:121-164`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-79`.

These results compose the actual local gate chronology with the actual
one-record follower predecessor. Their domain is the deterministic local
gate on the original physical execution. They do not identify that domain
with the source stopped release support or construct a conditional service
law, filtration, stopping time, or regret estimate.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ReferenceLocalReleasePendingHistory

open ConstructorDimensions ReferenceActivePhysicalStep

variable {p : Parameters} {rate : ReferenceActivePhysicalStep.RateInput p}

abbrev Record := ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)

/-- The indexed actual record of G's original-source run. This is only a
literal projection; it introduces no execution or state carrier. -/
def sourceRecord (rate : ReferenceActivePhysicalStep.RateInput p)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true)
    (s count : ℕ)
    (helapsed : ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed = s)
    (hspan : s + count ≤ p.T) (j : ℕ) (hj : j < count) :
    Record (p := p) (rate := rate) :=
  (ReferenceLocalReleaseGateChronology.sourceRun rate z rewards C_star C_h hcross s count
    helapsed hspan).records[j]'(by
      simp only [ReferenceLocalReleaseGateChronology.sourceRun,
        ReferenceActivePhysicalHorizon.run_record_count]
      exact hj)

/-- Actual records in the local b-gate support, retaining their original list
order and all physical records outside the projection in the underlying run. -/
def sourceLocalGateRecords (rate : ReferenceActivePhysicalStep.RateInput p)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true)
    (s count : ℕ)
    (helapsed : ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed = s)
    (hspan : s + count ≤ p.T) (b : ℕ) : List (Record (p := p) (rate := rate)) :=
  (ReferenceLocalReleaseGateChronology.sourceRun rate z rewards C_star C_h hcross s count
    helapsed hspan).records.filter fun r =>
      ReferenceRetainedReleasePhaseObservation.localReleaseGate rate b r.input.time
        (ReferenceActivePhysicalStepMeasurability.encodeState r.input.state)

/-- Optional source-round restriction of the actual local gate readout. The
cutoff selects records by their one-based physical round coordinate. -/
def sourceLocalGateRecordsBefore (rate : ReferenceActivePhysicalStep.RateInput p)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true)
    (s count : ℕ)
    (helapsed : ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed = s)
    (hspan : s + count ≤ p.T) (b v : ℕ) : List (Record (p := p) (rate := rate)) :=
  (sourceLocalGateRecords rate z rewards C_star C_h hcross s count helapsed hspan b).filter fun r =>
    decide (r.input.time.val + 1 < v)

private theorem sourceRun_record_eq
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true)
    (s short long : ℕ)
    (helapsed : ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed = s)
    (hshort : s + short ≤ p.T) (hlong : s + long ≤ p.T) (horder : short ≤ long)
    (j : Fin short) :
    sourceRecord rate z rewards C_star C_h hcross s short helapsed hshort j.val j.isLt =
      sourceRecord rate z rewards C_star C_h hcross s long helapsed hlong j.val
        (by omega) := by
  let seed := ReferenceLocalReleaseGateChronology.sourceSeed rate z rewards C_star C_h hcross
  have hactive : ReferenceActivePhysicalHorizon.allActiveAtStart seed s := by
    simpa only [helapsed] using
      (ReferenceLocalReleaseGateChronology.canonical_seed_release_inputs
        rate z rewards C_star C_h hcross).2.1
  have hleft := ReferenceLocalReleaseGateChronology.run_record_at seed z.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s hactive short hshort j
  have hright := ReferenceLocalReleaseGateChronology.run_record_at seed z.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s hactive long hlong
    ⟨j.val, by omega⟩
  exact hleft.trans hright.symm

private theorem sourceRun_record_eq_of_seed_eq
    (left right : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (s count : ℕ) (hspan : s + count ≤ p.T)
    (hl : ReferenceActivePhysicalHorizon.allActiveAtStart left s)
    (hr : ReferenceActivePhysicalHorizon.allActiveAtStart right s) (heq : left = right)
    (j : Fin count) :
    (ReferenceActivePhysicalHorizon.run left rows J rewards s count hspan hl).records[j.val]'(by
      rw [ReferenceActivePhysicalHorizon.run_record_count]
      exact j.isLt) =
      (ReferenceActivePhysicalHorizon.run right rows J rewards s count hspan hr).records[j.val]'(by
        rw [ReferenceActivePhysicalHorizon.run_record_count]
        exact j.isLt) := by
  cases heq
  rfl

private theorem startRound_pending_input (time : Fin p.T)
    (before choice : ReferencePrelaunchFollower.State p rate.eta)
    (memory choiceMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hstart : ActiveFollowerLifecycle.startRound rate.eta time before memory =
      .ok (choice, choiceMemory)) (hchoice : choice.status = .pending) :
    before.status = .pending := by
  cases hd : ActiveFollowerLifecycle.interruptionDecision rate.eta time before memory with
  | error failure => simp [ActiveFollowerLifecycle.startRound, hd] at hstart
  | ok interrupted =>
      have hstart' :
          (Except.ok ({before with status := if interrupted then .unoccupied else before.status}, memory) :
            ActiveFollowerLifecycle.LifecycleCheck
              (ReferencePrelaunchFollower.State p rate.eta × ActiveFollowerLifecycle.LocalMemory p)) =
            .ok (choice, choiceMemory) := by
        simpa [ActiveFollowerLifecycle.startRound, hd] using hstart
      have hpair := Except.ok.inj hstart'
      have hstatus := congrArg (fun pair :
          ReferencePrelaunchFollower.State p rate.eta × ActiveFollowerLifecycle.LocalMemory p =>
          pair.1.status) hpair
      rw [hchoice] at hstatus
      by_cases h : interrupted
      · simp [h] at hstatus
      · simpa [h] using hstatus

private theorem sourceRecord_eq_actualRunRecordAt
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true)
    (s count : ℕ)
    (helapsed : ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed = s)
    (hspan : s + count ≤ p.T) (j : Fin count) :
    sourceRecord rate z rewards C_star C_h hcross s count helapsed hspan j.val j.isLt =
      ReferenceAssignmentPayloadChronology.actualRunRecordAt
        (ReferenceLocalReleaseGateChronology.sourceSeed rate z rewards C_star C_h hcross)
        z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s j.val
        (by have _hj := j.isLt; omega)
        (by simpa only [helapsed] using
          (ReferenceLocalReleaseGateChronology.canonical_seed_release_inputs
            rate z rewards C_star C_h hcross).2.1) := by
  simpa only [sourceRecord, ReferenceLocalReleaseGateChronology.sourceRun] using
    (ReferenceLocalReleaseGateChronology.run_record_at
      (ReferenceLocalReleaseGateChronology.sourceSeed rate z rewards C_star C_h hcross)
      z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s
      (by simpa only [helapsed] using
        (ReferenceLocalReleaseGateChronology.canonical_seed_release_inputs
          rate z rewards C_star C_h hcross).2.1) count hspan j)

/-- Zero-based and one-based calendar coordinates of the indexed source
record. These are identities of G's actual run records. -/
theorem sourceRecord_sourceRound
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true)
    (s count : ℕ)
    (helapsed : ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed = s)
    (hspan : s + count ≤ p.T) (j : Fin count) :
    (sourceRecord rate z rewards C_star C_h hcross s count helapsed hspan j.val j.isLt).input.time.val =
        s + j.val ∧
      (sourceRecord rate z rewards C_star C_h hcross s count helapsed hspan j.val j.isLt).input.time.val + 1 =
        s + j.val + 1 := by
  rw [sourceRecord_eq_actualRunRecordAt]
  constructor <;> rfl

private theorem list_countP_fin_sum {α : Type} (records : List α) (test : α → Bool) :
    records.countP test = ∑ j : Fin records.length,
      if test (records[j.val]'(j.isLt)) then 1 else 0 := by
  induction records with
  | nil => simp
  | cons head tail ih =>
      rw [List.countP_cons]
      simp only [List.length_cons]
      rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, List.getElem_cons_zero, Fin.val_succ,
        List.getElem_cons_succ]
      rw [← ih]
      exact Nat.add_comm _ _

private theorem filter_getElem_origin {α : Type} (records : List α)
    (test : α → Bool) (n : ℕ) (hn : n < (records.filter test).length) :
    ∃ j : Fin records.length, test (records[j.val]'(j.isLt)) = true ∧
      (records.filter test)[n]'(hn) = records[j.val]'(j.isLt) := by
  induction records generalizing n with
  | nil => simp at hn
  | cons head tail ih =>
      by_cases hp : test head = true
      · cases n with
        | zero =>
            refine ⟨⟨0, by simp⟩, hp, ?_⟩
            simp [hp]
        | succ n =>
            have hn' : n < (tail.filter test).length := by
              simpa [hp] using hn
            obtain ⟨j, hj, hval⟩ := ih n hn'
            refine ⟨⟨j.val + 1, by simp⟩, ?_, ?_⟩
            · simpa using hj
            · simpa [List.filter_cons, hp, Fin.val_mk, List.getElem_cons_succ] using hval
      · have hn' : n < (tail.filter test).length := by
            simpa [hp] using hn
        obtain ⟨j, hj, hval⟩ := ih n hn'
        refine ⟨⟨j.val + 1, by simp⟩, ?_, ?_⟩
        · simpa using hj
        · simpa [List.filter_cons, hp, Fin.val_mk, List.getElem_cons_succ] using hval

private theorem filter_getElem_pair {α : Type} (records : List α)
    (test : α → Bool) (a b : ℕ) (ha : a < (records.filter test).length)
    (hb : b < (records.filter test).length) (hab : a < b) :
    ∃ j k : Fin records.length,
      j.val < k.val ∧ test (records[j.val]'(j.isLt)) = true ∧
      test (records[k.val]'(k.isLt)) = true ∧
      (records.filter test)[a]'(ha) = records[j.val]'(j.isLt) ∧
      (records.filter test)[b]'(hb) = records[k.val]'(k.isLt) := by
  induction records generalizing a b with
  | nil => simp at ha
  | cons head tail ih =>
      by_cases hp : test head = true
      · cases a with
        | zero =>
            cases b with
            | zero => omega
            | succ b =>
                have hb' : b < (tail.filter test).length := by
                  simpa [List.filter_cons, hp] using hb
                obtain ⟨k, hk, hvalK⟩ := filter_getElem_origin tail test b hb'
                let shifted : Fin (head :: tail).length := ⟨k.val + 1, by simp⟩
                refine ⟨⟨0, by simp⟩, shifted,
                  by simp [shifted], hp, ?_, ?_, ?_⟩
                · simpa [shifted, List.getElem_cons_succ] using hk
                · simp [hp]
                · have hfiltered : (List.filter test (head :: tail))[b + 1]'(hb) =
                      (List.filter test tail)[b]'(hb') := by
                    simp [hp]
                  have hsource : (head :: tail)[shifted.val]'(shifted.isLt) =
                      tail[k.val]'(k.isLt) := by
                    simp [shifted, List.getElem_cons_succ]
                  calc
                    (List.filter test (head :: tail))[b + 1]'(hb) =
                        (List.filter test tail)[b]'(hb') := hfiltered
                    _ = tail[k.val]'(k.isLt) := hvalK
                    _ = (head :: tail)[shifted.val]'(shifted.isLt) := hsource.symm
        | succ a =>
            cases b with
            | zero => omega
            | succ b =>
                have ha' : a < (tail.filter test).length := by
                  simpa [List.filter_cons, hp] using ha
                have hb' : b < (tail.filter test).length := by
                  simpa [List.filter_cons, hp] using hb
                obtain ⟨j, k, hjk, hj, hk, hvalJ, hvalK⟩ := ih a b ha' hb' (by omega)
                refine ⟨⟨j.val + 1, by simp⟩, ⟨k.val + 1, by simp⟩,
                  Nat.add_lt_add_right hjk 1, ?_, ?_, ?_, ?_⟩
                · simpa using hj
                · simpa using hk
                · simpa [List.filter_cons, hp, Fin.val_mk, List.getElem_cons_succ] using hvalJ
                · simpa [List.filter_cons, hp, Fin.val_mk, List.getElem_cons_succ] using hvalK
      · have ha' : a < (tail.filter test).length := by
          simpa [List.filter_cons, hp] using ha
        have hb' : b < (tail.filter test).length := by
          simpa [List.filter_cons, hp] using hb
        obtain ⟨j, k, hjk, hj, hk, hvalJ, hvalK⟩ := ih a b ha' hb' hab
        refine ⟨⟨j.val + 1, by simp⟩, ⟨k.val + 1, by simp⟩,
          Nat.add_lt_add_right hjk 1, ?_, ?_, ?_, ?_⟩
        · simpa using hj
        · simpa using hk
        · simpa [List.filter_cons, hp, Fin.val_mk, List.getElem_cons_succ] using hvalJ
        · simpa [List.filter_cons, hp, Fin.val_mk, List.getElem_cons_succ] using hvalK

/-- Each literal quota count is the finite sum of its indexed indicator over
the retained records. Applying this to `sourceLocalGateRecords` gives the
deterministic calendar summand without importing a probability module. -/
theorem releaseCount_fin_sum (M : Payload rate)
    (records : List (Record (p := p) (rate := rate))) (i : Fin (p.m - 1)) :
    ReferencePhysicalReleaseQuota.releaseCount M records i =
      ∑ j : Fin records.length,
        if decide (i ∈ ReferencePhysicalReleaseQuota.pendingSet M (records[j.val]'(j.isLt))) &&
            ReferencePhysicalReleaseQuota.releaseFlag M (records[j.val]'(j.isLt)) i then 1 else 0 := by
  exact list_countP_fin_sum records
    (fun r => decide (i ∈ ReferencePhysicalReleaseQuota.pendingSet M r) &&
      ReferencePhysicalReleaseQuota.releaseFlag M r i)

theorem upCount_fin_sum (M : Payload rate)
    (records : List (Record (p := p) (rate := rate))) (i : Fin (p.m - 1)) :
    ReferencePhysicalReleaseQuota.upCount M records i =
      ∑ j : Fin records.length,
        if decide (i ∈ ReferencePhysicalReleaseQuota.pendingSet M (records[j.val]'(j.isLt))) &&
            ReferencePhysicalReleaseQuota.upFlag M (records[j.val]'(j.isLt)) i then 1 else 0 := by
  exact list_countP_fin_sum records
    (fun r => decide (i ∈ ReferencePhysicalReleaseQuota.pendingSet M r) &&
      ReferencePhysicalReleaseQuota.upFlag M r i)

theorem dataCount_fin_sum (M : Payload rate)
    (records : List (Record (p := p) (rate := rate))) (i : Fin (p.m - 1)) :
    ReferencePhysicalReleaseQuota.dataCount M records i =
      ∑ j : Fin records.length,
        if decide (i ∈ ReferencePhysicalReleaseQuota.pendingSet M (records[j.val]'(j.isLt))) &&
            ReferencePhysicalReleaseQuota.dataFlag M (records[j.val]'(j.isLt)) i then 1 else 0 := by
  exact list_countP_fin_sum records
    (fun r => decide (i ∈ ReferencePhysicalReleaseQuota.pendingSet M r) &&
      ReferencePhysicalReleaseQuota.dataFlag M r i)

private theorem sourceRecord_mem
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true)
    (s count : ℕ)
    (helapsed : ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed = s)
    (hspan : s + count ≤ p.T) (j : Fin count) :
    sourceRecord rate z rewards C_star C_h hcross s count helapsed hspan j.val j.isLt ∈
      (ReferenceLocalReleaseGateChronology.sourceRun rate z rewards C_star C_h hcross s count
        helapsed hspan).records := by
  have hactive : ReferenceActivePhysicalHorizon.allActiveAtStart
      (ReferenceLocalReleaseGateChronology.sourceSeed rate z rewards C_star C_h hcross) s := by
    simpa only [helapsed] using
      (ReferenceLocalReleaseGateChronology.canonical_seed_release_inputs
        rate z rewards C_star C_h hcross).2.1
  have hlen := ReferenceActivePhysicalHorizon.run_record_count
    (ReferenceLocalReleaseGateChronology.sourceSeed rate z rewards C_star C_h hcross)
    z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s count hspan hactive
  have hmem := List.getElem_mem (show j.val <
      (ReferenceLocalReleaseGateChronology.sourceRun rate z rewards C_star C_h hcross s count
        helapsed hspan).records.length by
    simpa only [ReferenceLocalReleaseGateChronology.sourceRun, hlen] using j.isLt)
  simpa only [sourceRecord] using hmem

private theorem source_gate_between
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true)
    (s count : ℕ)
    (helapsed : ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed = s)
    (hspan : s + count ≤ p.T) (b : ℕ) (first middle last : Fin count)
    (hfirst : first.val ≤ middle.val) (hlast : middle.val ≤ last.val)
    (hgateFirst : ReferenceRetainedReleasePhaseObservation.localReleaseGate rate b
      (sourceRecord rate z rewards C_star C_h hcross s count helapsed hspan first.val first.isLt).input.time
      (ReferenceActivePhysicalStepMeasurability.encodeState
        (sourceRecord rate z rewards C_star C_h hcross s count helapsed hspan first.val first.isLt).input.state) = true)
    (hgateLast : ReferenceRetainedReleasePhaseObservation.localReleaseGate rate b
      (sourceRecord rate z rewards C_star C_h hcross s count helapsed hspan last.val last.isLt).input.time
      (ReferenceActivePhysicalStepMeasurability.encodeState
        (sourceRecord rate z rewards C_star C_h hcross s count helapsed hspan last.val last.isLt).input.state) = true) :
    ReferenceRetainedReleasePhaseObservation.localReleaseGate rate b
      (sourceRecord rate z rewards C_star C_h hcross s count helapsed hspan middle.val middle.isLt).input.time
      (ReferenceActivePhysicalStepMeasurability.encodeState
        (sourceRecord rate z rewards C_star C_h hcross s count helapsed hspan middle.val middle.isLt).input.state) = true := by
  let seed := ReferenceLocalReleaseGateChronology.sourceSeed rate z rewards C_star C_h hcross
  have hactive : ReferenceActivePhysicalHorizon.allActiveAtStart seed s := by
    simpa only [helapsed, seed] using
      (ReferenceLocalReleaseGateChronology.canonical_seed_release_inputs
        rate z rewards C_star C_h hcross).2.1
  have hinitial : seed.coordinator = .first := by
    simpa only [seed] using
      (ReferenceLocalReleaseGateChronology.canonical_seed_release_inputs
        rate z rewards C_star C_h hcross).1
  have hgateFirst' : ReferenceRetainedReleasePhaseObservation.localReleaseGate rate b
      (ReferenceAssignmentPayloadChronology.actualRunRecordAt seed z.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s first.val
        (by have _hj := first.isLt; omega) hactive).input.time
      (ReferenceActivePhysicalStepMeasurability.encodeState
        (ReferenceAssignmentPayloadChronology.actualRunRecordAt seed z.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s first.val
          (by have _hj := first.isLt; omega) hactive).input.state) = true := by
    simpa only [sourceRecord_eq_actualRunRecordAt] using hgateFirst
  have hgateLast' : ReferenceRetainedReleasePhaseObservation.localReleaseGate rate b
      (ReferenceAssignmentPayloadChronology.actualRunRecordAt seed z.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s last.val
        (by have _hj := last.isLt; omega) hactive).input.time
      (ReferenceActivePhysicalStepMeasurability.encodeState
        (ReferenceAssignmentPayloadChronology.actualRunRecordAt seed z.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s last.val
          (by have _hj := last.isLt; omega) hactive).input.state) = true := by
    simpa only [sourceRecord_eq_actualRunRecordAt] using hgateLast
  have hmiddle := ReferenceLocalReleaseGateChronology.run_gate_convex seed z.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s hactive count hspan
    hinitial first middle last hfirst hlast b hgateFirst' hgateLast'
  simpa only [sourceRecord_eq_actualRunRecordAt] using hmiddle

private theorem source_gate_payload_at
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true)
    (s count : ℕ)
    (helapsed : ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed = s)
    (hspan : s + count ≤ p.T) (b : ℕ) (first target : Fin count)
    (hgateFirst : ReferenceRetainedReleasePhaseObservation.localReleaseGate rate b
      (sourceRecord rate z rewards C_star C_h hcross s count helapsed hspan first.val first.isLt).input.time
      (ReferenceActivePhysicalStepMeasurability.encodeState
        (sourceRecord rate z rewards C_star C_h hcross s count helapsed hspan first.val first.isLt).input.state) = true)
    (hgateTarget : ReferenceRetainedReleasePhaseObservation.localReleaseGate rate b
      (sourceRecord rate z rewards C_star C_h hcross s count helapsed hspan target.val target.isLt).input.time
      (ReferenceActivePhysicalStepMeasurability.encodeState
        (sourceRecord rate z rewards C_star C_h hcross s count helapsed hspan target.val target.isLt).input.state) = true)
    (M : Payload rate)
    (hstoredFirst : ReferenceAssignmentPayloadPersistence.storedPayload
      (sourceRecord rate z rewards C_star C_h hcross s count helapsed hspan first.val first.isLt).input.state.coordinator = some M) :
    ReferenceAssignmentPayloadPersistence.storedPayload
      (sourceRecord rate z rewards C_star C_h hcross s count helapsed hspan target.val target.isLt).input.state.coordinator = some M := by
  have hchrono := ReferenceLocalReleaseGateChronology.source_gate_birth_and_payload_chronology
    rate z rewards C_star C_h hcross s count helapsed hspan b
  obtain ⟨N, birth, hleft, hright, _, _, _, _, _, _⟩ := hchrono
    (sourceRecord rate z rewards C_star C_h hcross s count helapsed hspan first.val first.isLt)
    (sourceRecord_mem rate z rewards C_star C_h hcross s count helapsed hspan first)
    (sourceRecord rate z rewards C_star C_h hcross s count helapsed hspan target.val target.isLt)
    (sourceRecord_mem rate z rewards C_star C_h hcross s count helapsed hspan target)
    hgateFirst hgateTarget
  have hN : N = M := Option.some.inj (hleft.symm.trans hstoredFirst)
  simpa only [hN] using hright

theorem source_localReleasePending_eq_pendingSet
    (rate : ReferenceActivePhysicalStep.RateInput p) (b : ℕ) (M : Payload rate)
    (r : Record (p := p) (rate := rate))
    (hgate : ReferenceRetainedReleasePhaseObservation.localReleaseGate rate b r.input.time
      (ReferenceActivePhysicalStepMeasurability.encodeState r.input.state) = true) :
    ReferenceRetainedReleasePhaseObservation.localReleasePending rate b M r.input.time r.input.state =
      ReferencePhysicalReleaseQuota.pendingSet M r := by
  simp [ReferenceRetainedReleasePhaseObservation.localReleasePending, hgate,
    ReferencePhysicalReleaseQuota.pendingSet]

/-- Backward persistence of one follower's pending observation within an
actual local-gate interval. The payload is extracted from both actual gated
endpoints on the same original-source run. Every intermediate record is
selected from that run, and every adjacent predecessor uses its actual
pending ordinary successor. -/
private theorem source_local_gate_pending_step
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true)
    (s count : ℕ)
    (helapsed : ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed = s)
    (hspan : s + count ≤ p.T) (b : ℕ) (M : Payload rate)
    (a : ℕ) (ha : a + 1 < count) (i : Fin (p.m - 1))
    (hgateA : ReferenceRetainedReleasePhaseObservation.localReleaseGate rate b
      (sourceRecord rate z rewards C_star C_h hcross s count helapsed hspan a (by omega)).input.time
      (ReferenceActivePhysicalStepMeasurability.encodeState
        (sourceRecord rate z rewards C_star C_h hcross s count helapsed hspan a (by omega)).input.state) = true)
    (hgateNext : ReferenceRetainedReleasePhaseObservation.localReleaseGate rate b
      (sourceRecord rate z rewards C_star C_h hcross s count helapsed hspan (a + 1) ha).input.time
      (ReferenceActivePhysicalStepMeasurability.encodeState
        (sourceRecord rate z rewards C_star C_h hcross s count helapsed hspan (a + 1) ha).input.state) = true)
    (hstoredA : ReferenceAssignmentPayloadPersistence.storedPayload
      (sourceRecord rate z rewards C_star C_h hcross s count helapsed hspan a (by omega)).input.state.coordinator =
        some M)
    (hstoredNext : ReferenceAssignmentPayloadPersistence.storedPayload
      (sourceRecord rate z rewards C_star C_h hcross s count helapsed hspan (a + 1) ha).input.state.coordinator =
        some M)
    (hpending : i ∈ ReferencePhysicalReleaseQuota.pendingSet M
      (sourceRecord rate z rewards C_star C_h hcross s count helapsed hspan (a + 1) ha)) :
    i ∈ ReferencePhysicalReleaseQuota.pendingSet M
        (sourceRecord rate z rewards C_star C_h hcross s count helapsed hspan a (by omega)) ∧
      ReferencePhysicalReleaseQuota.releaseFlag M
        (sourceRecord rate z rewards C_star C_h hcross s count helapsed hspan a (by omega)) i = false ∧
      ReferencePhysicalReleaseQuota.upFlag M
        (sourceRecord rate z rewards C_star C_h hcross s count helapsed hspan a (by omega)) i = false ∧
      ReferencePhysicalReleaseQuota.dataFlag M
        (sourceRecord rate z rewards C_star C_h hcross s count helapsed hspan a (by omega)) i = false := by
  have hacount : a + 1 ≤ count := Nat.le_of_lt ha
  let t : Fin p.T := ⟨s + a, by omega⟩
  have hs : s ≤ t.val := by simp [t]
  let previous : Fin (a + 1) := ⟨a, by omega⟩
  have hspanPrefix : s + (a + 1) ≤ p.T := by omega
  let prefixRecord := sourceRecord rate z rewards C_star C_h hcross s (a + 1)
    helapsed hspanPrefix a (by omega)
  let fullPrevious := sourceRecord rate z rewards C_star C_h hcross s count
    helapsed hspan a (by omega)
  let fullNext := sourceRecord rate z rewards C_star C_h hcross s count
    helapsed hspan (a + 1) ha
  have hprefixEq : prefixRecord = fullPrevious := by
    dsimp only [prefixRecord, fullPrevious]
    exact sourceRun_record_eq rate z rewards C_star C_h hcross s (a + 1) count
      helapsed hspanPrefix hspan (by omega) previous
  have hgatePrefix : ReferenceRetainedReleasePhaseObservation.localReleaseGate rate b
      prefixRecord.input.time
      (ReferenceActivePhysicalStepMeasurability.encodeState prefixRecord.input.state) = true := by
    rw [hprefixEq]
    exact hgateA
  obtain ⟨regs, owned, base, hcoord, _, hempty, _, _⟩ :=
    ReferenceLocalReleaseGateChronology.gate_live b fullNext.input.time fullNext.input.state hgateNext
  have hregPayload : regs.payload = M := by
    have hstored := hstoredNext
    simp only [fullNext, ReferenceAssignmentPayloadPersistence.storedPayload, hcoord] at hstored
    exact Option.some.inj hstored
  have hpendingStart : i ∈ ReferencePhysicalReleaseQuota.pendingAtStart M
      fullNext.input.time fullNext.input.state := by
    simpa only [ReferencePhysicalReleaseQuota.pendingSet] using hpending
  obtain ⟨before, beforeMemory, choice, choiceMemory, hordinary, hstart, hchoicePending⟩ :=
    (ReferencePhysicalReleaseQuota.mem_pendingAtStart_live M fullNext.input.time fullNext.input.state
      regs owned base hcoord hregPayload hempty i).mp (by simpa only [fullNext] using hpendingStart)
  have hbeforePending := startRound_pending_input fullNext.input.time before choice
    beforeMemory choiceMemory hstart hchoicePending
  have hconnected := ReferenceFollowerReplyChronology.connected_drop_from_output
    (ReferenceLocalReleaseGateChronology.sourceRun rate z rewards C_star C_h hcross s count
      helapsed hspan).connected a (by
        simp only [ReferenceLocalReleaseGateChronology.sourceRun,
          ReferenceActivePhysicalHorizon.run_record_count]
        omega)
  rw [List.drop_eq_getElem_cons (by
    simp only [ReferenceLocalReleaseGateChronology.sourceRun,
      ReferenceActivePhysicalHorizon.run_record_count]
    omega)] at hconnected
  have hnextState : fullNext.input.state = fullPrevious.output.next := hconnected.1
  have hout : fullPrevious.output.next.followers i = .ordinary before beforeMemory := by
    rw [← hnextState]
    exact hordinary
  let q := ActualInitializationPhysicalStep.selectedRowIndex p z
  let t : Fin p.T := ⟨s + a, by omega⟩
  have hs : s ≤ t.val := by simp [t]
  let split := ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t z
  let control := split.1
  let remainder := split.2
  have hremainder : remainder ∈
      ReferenceFixedTimeSourceControlCoupling.fixedControlRemainderStratum p q t := by
    change PrivateSourceStreams.coordinatorIndex p (split.2.2.1.2) = q
    rw [ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_private]
    change ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p z = q
    rw [ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex]
  have hstart : remainder ∈ ReferenceInitializationControlRemainder.launchStartRemainderEvent
      rate rewards C_star C_h q t s control := by
    apply (ReferenceInitializationControlRemainder.launchStartRemainderEvent_iff_source
      rate rewards C_star C_h q t control z rfl s hs).mpr
    exact ⟨hcross, helapsed⟩
  have hgeneratedSpec := ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec
    rate rewards C_star C_h q t control remainder hremainder s hs hstart
  have hsplitSource : ReferenceGeneratedActivePrefixFactor.splitSource q t control remainder = z := by
    dsimp [split, control, remainder]
    exact (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t).symm_apply_apply z
  have hgeneratedLaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch rate z rewards
      C_star C_h = some (ReferenceGeneratedActivePrefixFactor.generatedActiveSeed rate rewards
        C_star C_h q t control remainder hremainder s hs hstart) := by
    simpa only [hsplitSource] using hgeneratedSpec.1
  have hseed : ReferenceGeneratedActivePrefixFactor.generatedActiveSeed rate rewards C_star C_h
      q t control remainder hremainder s hs hstart =
      ReferenceLocalReleaseGateChronology.sourceSeed rate z rewards C_star C_h hcross :=
    Option.some.inj (hgeneratedLaunch.symm.trans
      (ReferenceLocalReleaseGateChronology.sourceSeed_launch rate z rewards C_star C_h hcross))
  have hprefixGateIndex : a < t.val - s + 1 := by simp [t]
  have hsourceActive : ReferenceActivePhysicalHorizon.allActiveAtStart
      (ReferenceLocalReleaseGateChronology.sourceSeed rate z rewards C_star C_h hcross) s := by
    simpa only [helapsed] using
      (ReferenceLocalReleaseGateChronology.canonical_seed_release_inputs
        rate z rewards C_star C_h hcross).2.1
  have hgeneratedSpan : s + (t.val - s + 1) ≤ p.T := by
    have ht := t.isLt
    omega
  let generatedRun := ReferenceActivePhysicalHorizon.run
    (ReferenceGeneratedActivePrefixFactor.generatedActiveSeed rate rewards C_star C_h
      q t control remainder hremainder s hs hstart) z.1.2 q rewards s (t.val - s + 1)
    hgeneratedSpan hgeneratedSpec.2.1
  let generatedRecord := generatedRun.records[a]'(by
    have hlen := ReferenceActivePhysicalHorizon.run_record_count
      (ReferenceGeneratedActivePrefixFactor.generatedActiveSeed rate rewards C_star C_h
        q t control remainder hremainder s hs hstart) z.1.2 q rewards s (t.val - s + 1)
      (by have ht := t.isLt; omega) hgeneratedSpec.2.1
    rw [hlen]
    exact hprefixGateIndex)
  have hgeneratedRecord : generatedRecord = prefixRecord := by
    let sourceLong := sourceRecord rate z rewards C_star C_h hcross s (t.val - s + 1)
      helapsed hgeneratedSpan a (by omega)
    have hsame : generatedRecord = sourceLong := by
      dsimp only [generatedRecord, generatedRun, sourceLong, sourceRecord,
        ReferenceLocalReleaseGateChronology.sourceRun]
      exact sourceRun_record_eq_of_seed_eq
        (ReferenceGeneratedActivePrefixFactor.generatedActiveSeed rate rewards C_star C_h
          q t control remainder hremainder s hs hstart)
        (ReferenceLocalReleaseGateChronology.sourceSeed rate z rewards C_star C_h hcross)
        z.1.2 q rewards s (t.val - s + 1) hgeneratedSpan hgeneratedSpec.2.1
        hsourceActive hseed ⟨a, hprefixGateIndex⟩
    have hlongPrefix : sourceLong = prefixRecord := by
      dsimp only [sourceLong, prefixRecord, sourceRecord]
      exact (sourceRun_record_eq rate z rewards C_star C_h hcross s (a + 1)
        (t.val - s + 1) helapsed hspanPrefix hgeneratedSpan (by omega) previous).symm
    exact hsame.trans hlongPrefix
  let prefixGateIndex : Fin (t.val - s + 1) := ⟨a, by dsimp [t]; omega⟩
  have hinv := ReferenceLocalReleasePendingPredecessor.originalSource_localReleasePendingSuccessor
    rate rewards C_star C_h q t s hs z rfl
    hcross helapsed b prefixGateIndex i
  have hgateGenerated : ReferenceRetainedReleasePhaseObservation.localReleaseGate rate b
      generatedRecord.input.time
      (ReferenceActivePhysicalStepMeasurability.encodeState generatedRecord.input.state) = true := by
    rw [hgeneratedRecord]
    exact hgatePrefix
  have houtPrefix : generatedRecord.output.next.followers i = .ordinary before beforeMemory := by
    rw [hgeneratedRecord, hprefixEq]
    exact hout
  have hresult := hinv hgateGenerated
    before beforeMemory houtPrefix hbeforePending
  rcases hresult with ⟨actualRegs, actualOwned, actualBase, hactualCoord, _, _, _, _, _, _, _,
    hfields, _, hfollower⟩
  rcases hfollower with ⟨followerBefore, followerMemory, followerChoice, followerChoiceMemory,
    post, service, released, hordinaryFollower, hstartFollower, hbeforePending, hchoicePending,
    hlastDown, hprepared, hrecorded, hservice, hpost, hrelease, hfinish, hnotReleased,
    hactualPending, hreleaseFalse, hupFalse, hdataFalse⟩
  have hstoredPrefix : ReferenceAssignmentPayloadPersistence.storedPayload
      prefixRecord.input.state.coordinator = some M := by
    rw [hprefixEq]
    exact hstoredA
  have hcoordPrefix : prefixRecord.input.state.coordinator =
      .live actualRegs actualOwned actualBase := by
    simpa only [← hgeneratedRecord] using hactualCoord
  have hpayloadEq : actualRegs.payload = M := by
    have h := hstoredPrefix
    simp only [ReferenceAssignmentPayloadPersistence.storedPayload, hcoordPrefix] at h
    exact Option.some.inj h
  have hactualPendingAt : i ∈ ReferencePhysicalReleaseQuota.pendingAtStart M
      prefixRecord.input.time prefixRecord.input.state := by
    have hactualPending' : i ∈ ReferencePhysicalReleaseQuota.pendingAtStart actualRegs.payload
        prefixRecord.input.time prefixRecord.input.state := by
      simpa only [← hgeneratedRecord] using hactualPending
    rw [← hpayloadEq]
    exact hactualPending'
  have hmember : i ∈ ReferencePhysicalReleaseQuota.pendingSet M prefixRecord := by
    simpa only [ReferencePhysicalReleaseQuota.pendingSet] using hactualPendingAt
  have hrelease : ReferencePhysicalReleaseQuota.releaseFlag M prefixRecord i = false := by
    have hrelease' : ReferencePhysicalReleaseQuota.releaseFlag actualRegs.payload prefixRecord i = false := by
      simpa only [← hgeneratedRecord] using hreleaseFalse
    rw [← hpayloadEq]
    exact hrelease'
  have hup : ReferencePhysicalReleaseQuota.upFlag M prefixRecord i = false := by
    have hup' : ReferencePhysicalReleaseQuota.upFlag actualRegs.payload prefixRecord i = false := by
      simpa only [← hgeneratedRecord] using hupFalse
    rw [← hpayloadEq]
    exact hup'
  have hdata : ReferencePhysicalReleaseQuota.dataFlag M prefixRecord i = false := by
    have hdata' : ReferencePhysicalReleaseQuota.dataFlag actualRegs.payload prefixRecord i = false := by
      simpa only [← hgeneratedRecord] using hdataFalse
    rw [← hpayloadEq]
    exact hdata'
  exact ⟨by simpa only [prefixRecord, hprefixEq] using hmember,
    by simpa only [prefixRecord, hprefixEq] using hrelease,
    by simpa only [prefixRecord, hprefixEq] using hup,
    by simpa only [prefixRecord, hprefixEq] using hdata⟩


theorem source_local_gate_pending_history
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true)
    (s count : ℕ)
    (helapsed : ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed = s)
    (hspan : s + count ≤ p.T) (b : ℕ) (j k : Fin count) (hjk : j.val < k.val)
    (i : Fin (p.m - 1))
    (hgateJ : ReferenceRetainedReleasePhaseObservation.localReleaseGate rate b
      (sourceRecord rate z rewards C_star C_h hcross s count helapsed hspan j.val j.isLt).input.time
      (ReferenceActivePhysicalStepMeasurability.encodeState
        (sourceRecord rate z rewards C_star C_h hcross s count helapsed hspan j.val j.isLt).input.state) = true)
    (hgateK : ReferenceRetainedReleasePhaseObservation.localReleaseGate rate b
      (sourceRecord rate z rewards C_star C_h hcross s count helapsed hspan k.val k.isLt).input.time
      (ReferenceActivePhysicalStepMeasurability.encodeState
        (sourceRecord rate z rewards C_star C_h hcross s count helapsed hspan k.val k.isLt).input.state) = true) :
    ∃ M : Payload rate,
      ReferenceAssignmentPayloadPersistence.storedPayload
          (sourceRecord rate z rewards C_star C_h hcross s count helapsed hspan j.val j.isLt).input.state.coordinator =
        some M ∧
      ReferenceAssignmentPayloadPersistence.storedPayload
          (sourceRecord rate z rewards C_star C_h hcross s count helapsed hspan k.val k.isLt).input.state.coordinator =
        some M ∧ M.sigma.val = b ∧
      (i ∈ ReferencePhysicalReleaseQuota.pendingSet M
          (sourceRecord rate z rewards C_star C_h hcross s count helapsed hspan k.val k.isLt) →
        i ∈ ReferencePhysicalReleaseQuota.pendingSet M
            (sourceRecord rate z rewards C_star C_h hcross s count helapsed hspan j.val j.isLt) ∧
        ReferencePhysicalReleaseQuota.releaseFlag M
            (sourceRecord rate z rewards C_star C_h hcross s count helapsed hspan j.val j.isLt) i = false ∧
        ReferencePhysicalReleaseQuota.upFlag M
            (sourceRecord rate z rewards C_star C_h hcross s count helapsed hspan j.val j.isLt) i = false ∧
        ReferencePhysicalReleaseQuota.dataFlag M
            (sourceRecord rate z rewards C_star C_h hcross s count helapsed hspan j.val j.isLt) i = false) := by
  have hchrono := ReferenceLocalReleaseGateChronology.source_gate_birth_and_payload_chronology
    rate z rewards C_star C_h hcross s count helapsed hspan b
  obtain ⟨M, birth, hstoredJ, hstoredK, hMσ, _, _, _, _, _⟩ := hchrono
    (sourceRecord rate z rewards C_star C_h hcross s count helapsed hspan j.val j.isLt)
    (sourceRecord_mem rate z rewards C_star C_h hcross s count helapsed hspan j)
    (sourceRecord rate z rewards C_star C_h hcross s count helapsed hspan k.val k.isLt)
    (sourceRecord_mem rate z rewards C_star C_h hcross s count helapsed hspan k)
    hgateJ hgateK
  refine ⟨M, hstoredJ, hstoredK, hMσ, ?_⟩
  intro hpendingK
  have hback : ∀ n, ∀ (current : Fin count), current.val = n → j.val < n → n ≤ k.val →
      i ∈ ReferencePhysicalReleaseQuota.pendingSet M
        (sourceRecord rate z rewards C_star C_h hcross s count helapsed hspan current.val current.isLt) →
      i ∈ ReferencePhysicalReleaseQuota.pendingSet M
          (sourceRecord rate z rewards C_star C_h hcross s count helapsed hspan j.val j.isLt) ∧
        ReferencePhysicalReleaseQuota.releaseFlag M
          (sourceRecord rate z rewards C_star C_h hcross s count helapsed hspan j.val j.isLt) i = false ∧
        ReferencePhysicalReleaseQuota.upFlag M
          (sourceRecord rate z rewards C_star C_h hcross s count helapsed hspan j.val j.isLt) i = false ∧
        ReferencePhysicalReleaseQuota.dataFlag M
          (sourceRecord rate z rewards C_star C_h hcross s count helapsed hspan j.val j.isLt) i = false := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro current hcurrent hjn hnk hpendingCurrent
        let previous : Fin count := ⟨n - 1, by have hk := k.isLt; omega⟩
        have hgatePrevious := source_gate_between rate z rewards C_star C_h hcross s count
          helapsed hspan b j previous k (by simp [previous]; omega) (by simp [previous]; omega)
          hgateJ hgateK
        have hgateCurrent := source_gate_between rate z rewards C_star C_h hcross s count
          helapsed hspan b j current k (by omega) (by omega) hgateJ hgateK
        have hstoredPrevious := source_gate_payload_at rate z rewards C_star C_h hcross s
          count helapsed hspan b j previous hgateJ hgatePrevious M hstoredJ
        have hstoredCurrent := source_gate_payload_at rate z rewards C_star C_h hcross s
          count helapsed hspan b j current hgateJ hgateCurrent M hstoredJ
        have hcurrentAtStep : n - 1 + 1 = current.val := by omega
        have hgateCurrentAtStep : ReferenceRetainedReleasePhaseObservation.localReleaseGate rate b
            (sourceRecord rate z rewards C_star C_h hcross s count helapsed hspan
              (n - 1 + 1) (by have hk := k.isLt; omega)).input.time
            (ReferenceActivePhysicalStepMeasurability.encodeState
              (sourceRecord rate z rewards C_star C_h hcross s count helapsed hspan
                (n - 1 + 1) (by have hk := k.isLt; omega)).input.state) = true := by
          simpa only [hcurrentAtStep] using hgateCurrent
        have hpendingAtStep : i ∈ ReferencePhysicalReleaseQuota.pendingSet M
            (sourceRecord rate z rewards C_star C_h hcross s count helapsed hspan
              (n - 1 + 1) (by have hk := k.isLt; omega)) := by
          simpa only [hcurrentAtStep] using hpendingCurrent
        have hstoredCurrentAtStep : ReferenceAssignmentPayloadPersistence.storedPayload
            (sourceRecord rate z rewards C_star C_h hcross s count helapsed hspan
              (n - 1 + 1) (by have hk := k.isLt; omega)).input.state.coordinator = some M := by
          simpa only [hcurrentAtStep] using hstoredCurrent
        have hstep := source_local_gate_pending_step rate z rewards C_star C_h hcross s count
          helapsed hspan b M (n - 1) (by have hk := k.isLt; omega) i
          hgatePrevious hgateCurrentAtStep hstoredPrevious hstoredCurrentAtStep hpendingAtStep
        rcases hstep with ⟨hpendingPrevious, hreleasePrevious, hupPrevious, hdataPrevious⟩
        by_cases hnext : n = j.val + 1
        · have hprevious : previous.val = j.val := by simp [previous, hnext]
          have hpreviousNat : n - 1 = j.val := by omega
          have hpendingJ : i ∈ ReferencePhysicalReleaseQuota.pendingSet M
              (sourceRecord rate z rewards C_star C_h hcross s count helapsed hspan j.val j.isLt) := by
            simpa only [hpreviousNat] using hpendingPrevious
          have hreleaseJ : ReferencePhysicalReleaseQuota.releaseFlag M
              (sourceRecord rate z rewards C_star C_h hcross s count helapsed hspan j.val j.isLt) i = false := by
            simpa only [hpreviousNat] using hreleasePrevious
          have hupJ : ReferencePhysicalReleaseQuota.upFlag M
              (sourceRecord rate z rewards C_star C_h hcross s count helapsed hspan j.val j.isLt) i = false := by
            simpa only [hpreviousNat] using hupPrevious
          have hdataJ : ReferencePhysicalReleaseQuota.dataFlag M
              (sourceRecord rate z rewards C_star C_h hcross s count helapsed hspan j.val j.isLt) i = false := by
            simpa only [hpreviousNat] using hdataPrevious
          exact ⟨hpendingJ, hreleaseJ, hupJ, hdataJ⟩
        · have hpreviousGt : j.val < previous.val := by simp [previous]; omega
          have hpreviousLe : previous.val ≤ k.val := by simp [previous]; omega
          exact ih (n - 1) (by omega) previous rfl hpreviousGt hpreviousLe
            (by simpa only [previous] using hpendingPrevious)
  exact hback k.val k rfl hjk (by rfl) hpendingK

private theorem storedPayload_eq_of_pendingSet (M : Payload rate)
    (r : Record (p := p) (rate := rate)) (i : Fin (p.m - 1))
    (hpending : i ∈ ReferencePhysicalReleaseQuota.pendingSet M r) :
    ReferenceAssignmentPayloadPersistence.storedPayload r.input.state.coordinator = some M := by
  have hpendingStart : i ∈ ReferencePhysicalReleaseQuota.pendingAtStart M r.input.time r.input.state := by
    simpa only [ReferencePhysicalReleaseQuota.pendingSet] using hpending
  cases hc : r.input.state.coordinator with
  | first => simp [ReferencePhysicalReleaseQuota.pendingAtStart, hc] at hpendingStart
  | collection payload ledger proposal =>
      simp [ReferencePhysicalReleaseQuota.pendingAtStart, hc] at hpendingStart
  | dagger => simp [ReferencePhysicalReleaseQuota.pendingAtStart, hc] at hpendingStart
  | live regs owned base =>
      have hpayload : regs.payload = M := by
        by_contra hne
        simp [ReferencePhysicalReleaseQuota.pendingAtStart, hc, hne] at hpendingStart
      simp [ReferenceAssignmentPayloadPersistence.storedPayload, hpayload]

/-- The backward endpoint result on two elements of the gate-filtered actual
list, including both nesting and the strict-prior own-observation result. -/
private theorem sourceLocalGateRecords_pairwise_history
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true)
    (s count : ℕ)
    (helapsed : ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed = s)
    (hspan : s + count ≤ p.T) (b : ℕ) (M : Payload rate) (i : Fin (p.m - 1))
    (a c : Fin (sourceLocalGateRecords rate z rewards C_star C_h hcross s count helapsed hspan b).length)
    (hac : a.val < c.val)
    (hpending : i ∈ ReferencePhysicalReleaseQuota.pendingSet M
      (sourceLocalGateRecords rate z rewards C_star C_h hcross s count helapsed hspan b)[c.val]) :
    i ∈ ReferencePhysicalReleaseQuota.pendingSet M
        (sourceLocalGateRecords rate z rewards C_star C_h hcross s count helapsed hspan b)[a.val] ∧
      ReferencePhysicalReleaseQuota.releaseFlag M
        (sourceLocalGateRecords rate z rewards C_star C_h hcross s count helapsed hspan b)[a.val] i = false := by
  let raw := (ReferenceLocalReleaseGateChronology.sourceRun rate z rewards C_star C_h hcross
    s count helapsed hspan).records
  let test := fun r : Record (p := p) (rate := rate) =>
    ReferenceRetainedReleasePhaseObservation.localReleaseGate rate b r.input.time
      (ReferenceActivePhysicalStepMeasurability.encodeState r.input.state)
  have hactive : ReferenceActivePhysicalHorizon.allActiveAtStart
      (ReferenceLocalReleaseGateChronology.sourceSeed rate z rewards C_star C_h hcross) s := by
    simpa only [helapsed] using
      (ReferenceLocalReleaseGateChronology.canonical_seed_release_inputs
        rate z rewards C_star C_h hcross).2.1
  have hlen : raw.length = count := by
    dsimp [raw, ReferenceLocalReleaseGateChronology.sourceRun]
    exact ReferenceActivePhysicalHorizon.run_record_count
      (ReferenceLocalReleaseGateChronology.sourceSeed rate z rewards C_star C_h hcross)
      z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s count hspan hactive
  obtain ⟨u, v, huv, hgateUraw, hgateVraw, hfilterU, hfilterV⟩ :=
    filter_getElem_pair raw test a.val c.val a.isLt c.isLt hac
  have huLt : u.val < count := by simpa only [hlen] using u.isLt
  have hvLt : v.val < count := by simpa only [hlen] using v.isLt
  let ju : Fin count := ⟨u.val, huLt⟩
  let jv : Fin count := ⟨v.val, hvLt⟩
  have hgateU : ReferenceRetainedReleasePhaseObservation.localReleaseGate rate b
      (sourceRecord rate z rewards C_star C_h hcross s count helapsed hspan u.val huLt).input.time
      (ReferenceActivePhysicalStepMeasurability.encodeState
        (sourceRecord rate z rewards C_star C_h hcross s count helapsed hspan u.val huLt).input.state) = true := by
    simpa only [test, sourceRecord, raw, ReferenceLocalReleaseGateChronology.sourceRun] using hgateUraw
  have hgateV : ReferenceRetainedReleasePhaseObservation.localReleaseGate rate b
      (sourceRecord rate z rewards C_star C_h hcross s count helapsed hspan v.val hvLt).input.time
      (ReferenceActivePhysicalStepMeasurability.encodeState
        (sourceRecord rate z rewards C_star C_h hcross s count helapsed hspan v.val hvLt).input.state) = true := by
    simpa only [test, sourceRecord, raw, ReferenceLocalReleaseGateChronology.sourceRun] using hgateVraw
  have hpendingV : i ∈ ReferencePhysicalReleaseQuota.pendingSet M
      (sourceRecord rate z rewards C_star C_h hcross s count helapsed hspan v.val hvLt) := by
    have hpendingRaw : i ∈ ReferencePhysicalReleaseQuota.pendingSet M (raw[v.val]'(v.isLt)) := by
      have hpendingFilter : i ∈ ReferencePhysicalReleaseQuota.pendingSet M
          ((raw.filter test)[c.val]'(c.isLt)) := by
        simpa only [sourceLocalGateRecords, raw, test,
          ReferenceLocalReleaseGateChronology.sourceRun] using hpending
      rw [hfilterV] at hpendingFilter
      exact hpendingFilter
    simpa only [sourceRecord, raw, ReferenceLocalReleaseGateChronology.sourceRun] using hpendingRaw
  obtain ⟨N, hstoredU, hstoredV, hNsigma, hback⟩ :=
    source_local_gate_pending_history rate z rewards C_star C_h hcross s count helapsed hspan
      b ju jv (by exact huv) i hgateU hgateV
  have hstoredM := storedPayload_eq_of_pendingSet M
    (sourceRecord rate z rewards C_star C_h hcross s count helapsed hspan v.val hvLt) i hpendingV
  have hNM : N = M := Option.some.inj (hstoredV.symm.trans hstoredM)
  subst N
  have hrecordU : sourceRecord rate z rewards C_star C_h hcross s count helapsed hspan
      u.val huLt =
      (sourceLocalGateRecords rate z rewards C_star C_h hcross s count helapsed hspan b)[a.val] := by
    simpa only [sourceRecord, sourceLocalGateRecords, raw, test,
      ReferenceLocalReleaseGateChronology.sourceRun, ju] using hfilterU.symm
  have hfalse := (hback hpendingV).2.1
  have hpendingU := (hback hpendingV).1
  rw [hrecordU] at hfalse hpendingU
  exact ⟨hpendingU, hfalse⟩

theorem sourceLocalGateRecords_pairwise_pending
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true)
    (s count : ℕ)
    (helapsed : ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed = s)
    (hspan : s + count ≤ p.T) (b : ℕ) (M : Payload rate) (i : Fin (p.m - 1))
    (a c : Fin (sourceLocalGateRecords rate z rewards C_star C_h hcross s count helapsed hspan b).length)
    (hac : a.val < c.val)
    (hpending : i ∈ ReferencePhysicalReleaseQuota.pendingSet M
      (sourceLocalGateRecords rate z rewards C_star C_h hcross s count helapsed hspan b)[c.val]) :
    i ∈ ReferencePhysicalReleaseQuota.pendingSet M
      (sourceLocalGateRecords rate z rewards C_star C_h hcross s count helapsed hspan b)[a.val] :=
  (sourceLocalGateRecords_pairwise_history rate z rewards C_star C_h hcross s count
    helapsed hspan b M i a c hac hpending).1

theorem sourceLocalGateRecords_pairwise_no_release
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true)
    (s count : ℕ)
    (helapsed : ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed = s)
    (hspan : s + count ≤ p.T) (b : ℕ) (M : Payload rate) (i : Fin (p.m - 1))
    (a c : Fin (sourceLocalGateRecords rate z rewards C_star C_h hcross s count helapsed hspan b).length)
    (hac : a.val < c.val)
    (hpending : i ∈ ReferencePhysicalReleaseQuota.pendingSet M
      (sourceLocalGateRecords rate z rewards C_star C_h hcross s count helapsed hspan b)[c.val]) :
    ReferencePhysicalReleaseQuota.releaseFlag M
      (sourceLocalGateRecords rate z rewards C_star C_h hcross s count helapsed hspan b)[a.val] i = false :=
  (sourceLocalGateRecords_pairwise_history rate z rewards C_star C_h hcross s count
    helapsed hspan b M i a c hac hpending).2

private theorem local_history_count_le_one (M : Payload rate)
    (records : List (Record (p := p) (rate := rate))) (i : Fin (p.m - 1))
    (history : ∀ (a c : ℕ) (ha : a < records.length) (hc : c < records.length),
      a < c → i ∈ ReferencePhysicalReleaseQuota.pendingSet M records[c] →
        ReferencePhysicalReleaseQuota.releaseFlag M records[a] i = false) :
    ReferencePhysicalReleaseQuota.releaseCount M records i ≤ 1 := by
  induction records with
  | nil => exact Nat.zero_le 1
  | cons r rest ih =>
      have htail : ∀ (a c : ℕ) (ha : a < rest.length) (hc : c < rest.length),
          a < c → i ∈ ReferencePhysicalReleaseQuota.pendingSet M rest[c] →
            ReferencePhysicalReleaseQuota.releaseFlag M rest[a] i = false := by
        intro a c ha hc hac hp
        have haa : a + 1 < (r :: rest).length := by
          simpa only [List.length_cons] using Nat.succ_lt_succ ha
        have hcc : c + 1 < (r :: rest).length := by
          simpa only [List.length_cons] using Nat.succ_lt_succ hc
        exact history (a + 1) (c + 1) haa hcc (Nat.succ_lt_succ hac) hp
      have hbound := ih htail
      cases hhead : decide (i ∈ ReferencePhysicalReleaseQuota.pendingSet M r) &&
          ReferencePhysicalReleaseQuota.releaseFlag M r i with
      | false =>
          simpa only [ReferencePhysicalReleaseQuota.releaseCount, List.countP_cons, hhead,
            Bool.false_eq_true, ite_false, Nat.add_zero] using hbound
      | true =>
          have hzero : ReferencePhysicalReleaseQuota.releaseCount M rest i = 0 := by
            apply List.countP_eq_zero.mpr
            intro record hr hflag
            obtain ⟨c, hc, rfl⟩ := List.mem_iff_getElem.mp hr
            have hp := of_decide_eq_true (Bool.and_eq_true_iff.mp hflag).1
            have hfirst : 0 < (r :: rest).length := by simp
            have hlater : c + 1 < (r :: rest).length := by
              simpa only [List.length_cons] using Nat.succ_lt_succ hc
            have hrelease := history 0 (c + 1) hfirst hlater (by omega) hp
            change ReferencePhysicalReleaseQuota.releaseFlag M r i = false at hrelease
            have hheadRelease := (Bool.and_eq_true_iff.mp hhead).2
            rw [hrelease] at hheadRelease
            cases hheadRelease
          change ReferencePhysicalReleaseQuota.releaseCount M (r :: rest) i ≤ 1
          rw [ReferencePhysicalReleaseQuota.releaseCount, List.countP_cons, hhead]
          change ReferencePhysicalReleaseQuota.releaseCount M rest i + 1 ≤ 1
          rw [hzero]

theorem sourceLocalGateRecords_releaseCount_le_one
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true)
    (s count : ℕ)
    (helapsed : ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed = s)
    (hspan : s + count ≤ p.T) (b : ℕ) (M : Payload rate) (i : Fin (p.m - 1)) :
    ReferencePhysicalReleaseQuota.releaseCount M
      (sourceLocalGateRecords rate z rewards C_star C_h hcross s count helapsed hspan b) i ≤ 1 := by
  apply local_history_count_le_one M _ i
  intro a c ha hc hac hpending
  exact sourceLocalGateRecords_pairwise_no_release rate z rewards C_star C_h hcross s count
    helapsed hspan b M i ⟨a, ha⟩ ⟨c, hc⟩ hac hpending

theorem sourceLocalGateRecords_upCount_le_one
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true)
    (s count : ℕ)
    (helapsed : ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed = s)
    (hspan : s + count ≤ p.T) (b : ℕ) (M : Payload rate) (i : Fin (p.m - 1)) :
    ReferencePhysicalReleaseQuota.upCount M
      (sourceLocalGateRecords rate z rewards C_star C_h hcross s count helapsed hspan b) i ≤ 1 :=
  (ReferencePhysicalReleaseQuota.upCount_le_releaseCount M _ i).trans
    (sourceLocalGateRecords_releaseCount_le_one rate z rewards C_star C_h hcross s count
      helapsed hspan b M i)

theorem sourceLocalGateRecords_dataCount_le_one
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true)
    (s count : ℕ)
    (helapsed : ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed = s)
    (hspan : s + count ≤ p.T) (b : ℕ) (M : Payload rate) (i : Fin (p.m - 1)) :
    ReferencePhysicalReleaseQuota.dataCount M
      (sourceLocalGateRecords rate z rewards C_star C_h hcross s count helapsed hspan b) i ≤ 1 :=
  (ReferencePhysicalReleaseQuota.dataCount_le_releaseCount M _ i).trans
    (sourceLocalGateRecords_releaseCount_le_one rate z rewards C_star C_h hcross s count
      helapsed hspan b M i)

private theorem filter_preserves_release_history (M : Payload rate)
    (records : List (Record (p := p) (rate := rate))) (test : Record (p := p) (rate := rate) → Bool)
    (i : Fin (p.m - 1))
    (history : ∀ (a c : ℕ) (ha : a < records.length) (hc : c < records.length),
      a < c → i ∈ ReferencePhysicalReleaseQuota.pendingSet M records[c] →
        ReferencePhysicalReleaseQuota.releaseFlag M records[a] i = false) :
    ∀ (a c : ℕ) (ha : a < (records.filter test).length)
      (hc : c < (records.filter test).length),
      a < c → i ∈ ReferencePhysicalReleaseQuota.pendingSet M (records.filter test)[c] →
        ReferencePhysicalReleaseQuota.releaseFlag M (records.filter test)[a] i = false := by
  intro a c ha hc hac hpending
  obtain ⟨u, v, huv, _, _, hfilterU, hfilterV⟩ :=
    filter_getElem_pair records test a c ha hc hac
  have hpendingV : i ∈ ReferencePhysicalReleaseQuota.pendingSet M records[v.val] := by
    rw [hfilterV] at hpending
    exact hpending
  have hfalse := history u.val v.val u.isLt v.isLt huv hpendingV
  rw [← hfilterU] at hfalse
  exact hfalse

private theorem filter_preserves_pending_history (M : Payload rate)
    (records : List (Record (p := p) (rate := rate))) (test : Record (p := p) (rate := rate) → Bool)
    (i : Fin (p.m - 1))
    (history : ∀ (a c : ℕ) (ha : a < records.length) (hc : c < records.length),
      a < c → i ∈ ReferencePhysicalReleaseQuota.pendingSet M records[c] →
        i ∈ ReferencePhysicalReleaseQuota.pendingSet M records[a]) :
    ∀ (a c : ℕ) (ha : a < (records.filter test).length)
      (hc : c < (records.filter test).length),
      a < c → i ∈ ReferencePhysicalReleaseQuota.pendingSet M (records.filter test)[c] →
        i ∈ ReferencePhysicalReleaseQuota.pendingSet M (records.filter test)[a] := by
  intro a c ha hc hac hpending
  obtain ⟨u, v, huv, _, _, hfilterU, hfilterV⟩ :=
    filter_getElem_pair records test a c ha hc hac
  have hpendingV : i ∈ ReferencePhysicalReleaseQuota.pendingSet M records[v.val] := by
    rw [hfilterV] at hpending
    exact hpending
  have hpendingU := history u.val v.val u.isLt v.isLt huv hpendingV
  rw [← hfilterU] at hpendingU
  exact hpendingU

private theorem local_history_strict_prior_counts_zero (M : Payload rate)
    (records : List (Record (p := p) (rate := rate))) (i : Fin (p.m - 1))
    (history : ∀ (a c : ℕ) (ha : a < records.length) (hc : c < records.length),
      a < c → i ∈ ReferencePhysicalReleaseQuota.pendingSet M records[c] →
        ReferencePhysicalReleaseQuota.releaseFlag M records[a] i = false)
    (current : Fin records.length)
    (hpending : i ∈ ReferencePhysicalReleaseQuota.pendingSet M records[current.val]) :
    ReferencePhysicalReleaseQuota.releaseCount M (records.take current.val) i = 0 ∧
      ReferencePhysicalReleaseQuota.upCount M (records.take current.val) i = 0 ∧
      ReferencePhysicalReleaseQuota.dataCount M (records.take current.val) i = 0 := by
  have hrelease : ReferencePhysicalReleaseQuota.releaseCount M (records.take current.val) i = 0 := by
    change List.countP (fun r => decide (i ∈ ReferencePhysicalReleaseQuota.pendingSet M r) &&
      ReferencePhysicalReleaseQuota.releaseFlag M r i) (records.take current.val) = 0
    apply List.countP_eq_zero.mpr
    intro r hr hflag
    obtain ⟨a, ha, rfl⟩ := List.mem_iff_getElem.mp hr
    have hprefixLen : (records.take current.val).length = current.val := by
      simp [List.length_take]
    have haCurrent : a < current.val := by simpa only [hprefixLen] using ha
    have haRecords : a < records.length := lt_trans haCurrent current.isLt
    have hprior := history a current.val haRecords current.isLt haCurrent hpending
    have hflagRelease := (Bool.and_eq_true_iff.mp hflag).2
    simp only [List.getElem_take] at hflagRelease
    rw [hflagRelease] at hprior
    cases hprior
  have hup : ReferencePhysicalReleaseQuota.upCount M (records.take current.val) i = 0 :=
    Nat.eq_zero_of_le_zero (by
      simpa only [hrelease] using
        (ReferencePhysicalReleaseQuota.upCount_le_releaseCount M (records.take current.val) i))
  have hdata : ReferencePhysicalReleaseQuota.dataCount M (records.take current.val) i = 0 :=
    Nat.eq_zero_of_le_zero (by
      simpa only [hrelease] using
        (ReferencePhysicalReleaseQuota.dataCount_le_releaseCount M (records.take current.val) i))
  exact ⟨hrelease, hup, hdata⟩

theorem sourceLocalGateRecords_strict_prior_counts_zero
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true)
    (s count : ℕ)
    (helapsed : ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed = s)
    (hspan : s + count ≤ p.T) (b : ℕ) (M : Payload rate) (i : Fin (p.m - 1))
    (current : Fin (sourceLocalGateRecords rate z rewards C_star C_h hcross s count helapsed hspan b).length)
    (hpending : i ∈ ReferencePhysicalReleaseQuota.pendingSet M
      (sourceLocalGateRecords rate z rewards C_star C_h hcross s count helapsed hspan b)[current.val]) :
    ReferencePhysicalReleaseQuota.releaseCount M
        ((sourceLocalGateRecords rate z rewards C_star C_h hcross s count helapsed hspan b).take current.val) i = 0 ∧
      ReferencePhysicalReleaseQuota.upCount M
        ((sourceLocalGateRecords rate z rewards C_star C_h hcross s count helapsed hspan b).take current.val) i = 0 ∧
      ReferencePhysicalReleaseQuota.dataCount M
        ((sourceLocalGateRecords rate z rewards C_star C_h hcross s count helapsed hspan b).take current.val) i = 0 := by
  apply local_history_strict_prior_counts_zero M _ i _ current hpending
  intro a c ha hc hac hp
  exact sourceLocalGateRecords_pairwise_no_release rate z rewards C_star C_h hcross s count
    helapsed hspan b M i ⟨a, ha⟩ ⟨c, hc⟩ hac hp

theorem sourceLocalGateRecordsBefore_releaseCount_le_one
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true)
    (s count : ℕ)
    (helapsed : ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed = s)
    (hspan : s + count ≤ p.T) (b v : ℕ) (M : Payload rate) (i : Fin (p.m - 1)) :
    ReferencePhysicalReleaseQuota.releaseCount M
      (sourceLocalGateRecordsBefore rate z rewards C_star C_h hcross s count helapsed hspan b v) i ≤ 1 := by
  apply local_history_count_le_one M _ i
  apply filter_preserves_release_history
  intro a c ha hc hac hp
  exact sourceLocalGateRecords_pairwise_no_release rate z rewards C_star C_h hcross s count
    helapsed hspan b M i ⟨a, ha⟩ ⟨c, hc⟩ hac hp

theorem sourceLocalGateRecordsBefore_upCount_le_one
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true)
    (s count : ℕ)
    (helapsed : ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed = s)
    (hspan : s + count ≤ p.T) (b v : ℕ) (M : Payload rate) (i : Fin (p.m - 1)) :
    ReferencePhysicalReleaseQuota.upCount M
      (sourceLocalGateRecordsBefore rate z rewards C_star C_h hcross s count helapsed hspan b v) i ≤ 1 :=
  (ReferencePhysicalReleaseQuota.upCount_le_releaseCount M _ i).trans
    (sourceLocalGateRecordsBefore_releaseCount_le_one rate z rewards C_star C_h hcross s count
      helapsed hspan b v M i)

theorem sourceLocalGateRecordsBefore_dataCount_le_one
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true)
    (s count : ℕ)
    (helapsed : ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed = s)
    (hspan : s + count ≤ p.T) (b v : ℕ) (M : Payload rate) (i : Fin (p.m - 1)) :
    ReferencePhysicalReleaseQuota.dataCount M
      (sourceLocalGateRecordsBefore rate z rewards C_star C_h hcross s count helapsed hspan b v) i ≤ 1 :=
  (ReferencePhysicalReleaseQuota.dataCount_le_releaseCount M _ i).trans
    (sourceLocalGateRecordsBefore_releaseCount_le_one rate z rewards C_star C_h hcross s count
      helapsed hspan b v M i)

theorem sourceLocalGateRecordsBefore_pairwise_pending
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true)
    (s count : ℕ)
    (helapsed : ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed = s)
    (hspan : s + count ≤ p.T) (b v : ℕ) (M : Payload rate) (i : Fin (p.m - 1))
    (a c : Fin (sourceLocalGateRecordsBefore rate z rewards C_star C_h hcross s count helapsed hspan b v).length)
    (hac : a.val < c.val)
    (hpending : i ∈ ReferencePhysicalReleaseQuota.pendingSet M
      (sourceLocalGateRecordsBefore rate z rewards C_star C_h hcross s count helapsed hspan b v)[c.val]) :
    i ∈ ReferencePhysicalReleaseQuota.pendingSet M
      (sourceLocalGateRecordsBefore rate z rewards C_star C_h hcross s count helapsed hspan b v)[a.val] := by
  dsimp only [sourceLocalGateRecordsBefore]
  exact filter_preserves_pending_history M
    (sourceLocalGateRecords rate z rewards C_star C_h hcross s count helapsed hspan b)
    (fun r => decide (r.input.time.val + 1 < v)) i
    (by
      intro x y hx hy hxy hpendingY
      exact sourceLocalGateRecords_pairwise_pending rate z rewards C_star C_h hcross s count
        helapsed hspan b M i ⟨x, hx⟩ ⟨y, hy⟩ hxy hpendingY)
    a.val c.val a.isLt c.isLt hac hpending

theorem sourceLocalGateRecordsBefore_strict_prior_counts_zero
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true)
    (s count : ℕ)
    (helapsed : ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed = s)
    (hspan : s + count ≤ p.T) (b v : ℕ) (M : Payload rate) (i : Fin (p.m - 1))
    (current : Fin (sourceLocalGateRecordsBefore rate z rewards C_star C_h hcross s count helapsed hspan b v).length)
    (hpending : i ∈ ReferencePhysicalReleaseQuota.pendingSet M
      (sourceLocalGateRecordsBefore rate z rewards C_star C_h hcross s count helapsed hspan b v)[current.val]) :
    ReferencePhysicalReleaseQuota.releaseCount M
        ((sourceLocalGateRecordsBefore rate z rewards C_star C_h hcross s count helapsed hspan b v).take current.val) i = 0 ∧
      ReferencePhysicalReleaseQuota.upCount M
        ((sourceLocalGateRecordsBefore rate z rewards C_star C_h hcross s count helapsed hspan b v).take current.val) i = 0 ∧
      ReferencePhysicalReleaseQuota.dataCount M
        ((sourceLocalGateRecordsBefore rate z rewards C_star C_h hcross s count helapsed hspan b v).take current.val) i = 0 := by
  apply local_history_strict_prior_counts_zero M _ i _ current hpending
  apply filter_preserves_release_history
  intro a c ha hc hac hp
  exact sourceLocalGateRecords_pairwise_no_release rate z rewards C_star C_h hcross s count
    helapsed hspan b M i ⟨a, ha⟩ ⟨c, hc⟩ hac hp

/-- The source-round restriction retains G's literal empty-support sentinel
`T + 1` and uses `min (gateBeta) v` when the intersection is nonempty. -/
theorem source_local_gate_interval_restrict
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true)
    (s count : ℕ)
    (helapsed : ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed = s)
    (hspan : s + count ≤ p.T) (b v : ℕ) (hv : 1 ≤ v ∧ v ≤ p.T + 1) :
    let E := ReferenceLocalReleaseGateChronology.sourceRun rate z rewards C_star C_h hcross
      s count helapsed hspan
    let α := ReferenceLocalReleaseGateChronology.gateAlpha b E.records
    let β := min (ReferenceLocalReleaseGateChronology.gateBeta b E.records) v
    let left := if α < β then α else p.T + 1
    let right := if α < β then β else p.T + 1
    (ReferenceLocalReleaseGateChronology.gateSupport b E.records).filter (· < v) =
        Finset.Ico left right ∧ 1 ≤ left ∧ left ≤ right ∧ right ≤ p.T + 1 :=
  ReferenceLocalReleaseGateChronology.source_gate_interval_restrict rate z rewards C_star C_h
    hcross s count helapsed hspan b v hv

/-- The actual-source retained launch specialization of the filtered gate
readout. The current control is the actual fixed split of the original source. -/
theorem sourceLocalGateRecords_launchRun_eq
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (q : Fin (M p)) (t : Fin p.T) (s : ℕ) (hs : s ≤ t.val)
    (control0 : ContinuousLearningRows.TimeControl p) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hselected : ActualInitializationPhysicalStep.selectedRowIndex p z = q)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true)
    (helapsed : ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed = s)
    (b : ℕ) :
    let split := ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t z
    let x := ReferenceRetainedBoundaryMeasurability.retainedLaunchStartInputOfSource
      rate rewards C_star C_h q t s hs control0 z hselected hcross helapsed
    (ReferenceLocalReleaseGateChronology.launchRun rate rewards C_star C_h q t s hs control0 x split.1).records.filter
        (fun r => ReferenceRetainedReleasePhaseObservation.localReleaseGate rate b r.input.time
          (ReferenceActivePhysicalStepMeasurability.encodeState r.input.state)) =
      sourceLocalGateRecords rate z rewards C_star C_h hcross s (t.val - s + 1) helapsed
        (by have _ht := t.isLt; omega) b := by
  intro split x
  have heq := ReferenceLocalReleaseGateChronology.launchRun_original_source rate rewards C_star C_h
    q t s hs control0 z hselected hcross helapsed
  change (ReferenceLocalReleaseGateChronology.launchRun rate rewards C_star C_h q t s hs
    control0 x split.1).records =
      (ReferenceLocalReleaseGateChronology.sourceRun rate z rewards C_star C_h hcross s
        (t.val - s + 1) helapsed (by have _ht := t.isLt; omega)).records at heq
  simpa only [sourceLocalGateRecords] using congrArg
    (fun records => records.filter fun r =>
      ReferenceRetainedReleasePhaseObservation.localReleaseGate rate b r.input.time
        (ReferenceActivePhysicalStepMeasurability.encodeState r.input.state)) heq

/-- R's retained release-entry readout is exactly G's local entry evaluated
on the indexed original-source record, including the actual current feedback. -/
theorem releaseEntries_source_local_entry
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (q : Fin (M p)) (t : Fin p.T) (s : ℕ) (hs : s ≤ t.val)
    (control0 : ContinuousLearningRows.TimeControl p) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hselected : ActualInitializationPhysicalStep.selectedRowIndex p z = q)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true)
    (helapsed : ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed = s)
    (b : ℕ) (j : Fin (t.val - s + 1)) :
    ReferenceReleaseStrictPastFactor.releaseEntries rate rewards C_star C_h q t s hs control0 b
        (ReferenceRetainedBoundaryMeasurability.retainedLaunchStartInputOfSource
          rate rewards C_star C_h q t s hs control0 z hselected hcross helapsed) j =
      ReferenceRetainedReleasePhaseObservation.localReleaseEntry rate b
        (sourceRecord rate z rewards C_star C_h hcross s (t.val - s + 1) helapsed
          (by have _ht := t.isLt; omega) j.val j.isLt).input.time
        (ReferenceActivePhysicalStepMeasurability.encodeState
          (sourceRecord rate z rewards C_star C_h hcross s (t.val - s + 1) helapsed
            (by have _ht := t.isLt; omega) j.val j.isLt).input.state) := by
  have hentry := ReferenceLocalReleaseGateChronology.releaseEntries_original_source_record
    rate rewards C_star C_h q t s hs control0 z hselected hcross helapsed b
  simpa only [sourceRecord, ReferenceLocalReleaseGateChronology.sourceRun] using hentry j


end Bandits.Support.ReferenceLocalReleasePendingHistory

end noncomputable section
