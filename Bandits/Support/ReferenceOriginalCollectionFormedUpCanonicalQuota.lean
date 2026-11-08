/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceOriginalCollectionFormedUpThreshold
public import Bandits.Support.ReferenceOriginalCollectionOldDownPendingPrefix

import Mathlib.Tactic

/-!
# Canonical quota for the original formed UP collection prefix

Sources: `sources/zip4/manuscript/06_interruptions.tex:477-481`,
`sources/zip4/manuscript/05_binary_transport.tex:180-191`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:151-157`.

This module keeps the original complete-suffix cutoff run and its literal
source readout. The physical run continues after the inclusive first-bad
date; only the readout prefix is stopped.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions
open ReferenceOriginalCollectionFormedUpThreshold
open ReferenceOriginalCollectionOldDownPendingPrefix
open scoped Classical

namespace Bandits.Support.ReferenceOriginalCollectionFormedUpCanonicalQuota

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev SourceInput := BootstrapPrivateRoundStreams.SourceInput
abbrev GridRewardTable := ActualInitializationPhysicalStep.GridRewardTable
abbrev Record {p : Parameters} (rate : RateInput p) :=
  ReferenceCompletePhysicalHistory.RoundRecord (p := p) (rate := rate)

variable {p : Parameters}
variable (rate : RateInput p) (rewards : GridRewardTable p)
  (C_star C_h : ℝ)

/-- Literal original-source FORMED-UP readout on the canonical cutoff run.
It uses the inclusive first-bad-date gate, the actual incoming pending set and
the checked FORMED stage, and the original source's actual UP readout. -/
def actualFormedUpPrefixReadoutSum
    (source : SourceInput p) (K : List (Record rate)) (j beta : ℕ)
    (i : Fin (p.m - 1)) : ℝ :=
  ((K.take (min j K.length)).map fun r =>
    let t := r.input.time
    (if t.val + 1 ≤ beta then (1 : ℝ) else 0) *
      (if ∃ pending : Finset (Fin (p.m - 1)),
          i ∈ pending ∧
            ReferenceOriginalKthCollectionSourceSections.kthCPrechoiceStage
              rate rewards C_star C_h t i source = some (pending, .formed)
        then (1 : ℝ) else 0) *
      ReferenceFirstCollectionUpConditionalService.actualFirstCollectionUpReadout
        (rate := rate) rewards C_star C_h i t source).sum

/-- On an actual incoming COLLECTION coordinator record, the literal source
prechoice is FORMED exactly when the same current DOWN reply is formed and the
same actual ledger still lists the follower as pending. -/
theorem actual_source_formed_stage_iff
    (source : SourceInput p) (r : Record rate)
    (hactual : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h r.input.time source = some r)
    (P : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (saved : Option (Fin p.T × Bool))
    (hcoord : r.input.state.coordinator = .collection P ledger saved)
    (i : Fin (p.m - 1)) :
    (∃ pending : Finset (Fin (p.m - 1)), i ∈ pending ∧
      ReferenceOriginalKthCollectionSourceSections.kthCPrechoiceStage
        rate rewards C_star C_h r.input.time i source = some (pending, .formed)) ↔
      (ReferenceFirstReplacementCollectionStoppedPureUpQuota.replyFormedAt r i
        (P.downRecord
          (ReferenceOriginalKthCollectionSourceSections.kthFollowerIndex (p := p) i)) ∧
        i ∈ ledger.pending) := by
  have hdata := ReferenceOriginalKthCollectionSourceSections.kthCPrechoiceData_actualRecord
    rate rewards C_star C_h r.input.time source r hactual
  have hdata' :
      ReferenceOriginalKthCollectionSourceSections.kthCPrechoiceData
        rate rewards C_star C_h r.input.time source =
        if ledger.pending.Nonempty then
          some (P, (ledger.pending, (ledger.cutoff,
            ReferenceOriginalKthCollectionSourceSections.kthCollectionCoordinatorCode
              rate (P, (ledger, saved)))))
        else none := by
    rw [hdata]
    simp [ReferenceOriginalKthCollectionSourceSections.kthCPrechoiceDataFromCoordinatorCode,
      ReferenceActivePhysicalStepMeasurability.encodeCoordinator, hcoord]
  by_cases hnonempty : ledger.pending.Nonempty
  · have hsource :
        ReferenceOriginalKthCollectionSourceSections.kthCPrechoiceStage
          rate rewards C_star C_h r.input.time i source =
          some (ledger.pending, .formed) ↔
        ReferenceFirstReplacementCollectionPredictableStages.choiceStage r P i = .formed := by
      rw [ReferenceOriginalKthCollectionSourceSections.kthCPrechoiceStage,
        hdata']
      simp only [hnonempty, ↓reduceIte, Option.map_some]
      have hindex :
          ReferenceOriginalKthCollectionSourceSections.kthFollowerIndex (p := p) i = i := by
        apply Fin.ext
        rfl
      rw [hindex]
      rw [ReferenceFirstReplacementCollectionPredictableStages.preRoundStart_choiceStage
        rate rewards C_star C_h r.input.time i source r P hactual]
      simp only [Option.some.injEq, Prod.mk.injEq]
      simp
    constructor
    · rintro ⟨pending, hip, hstage⟩
      have hpending : pending = ledger.pending := by
        unfold ReferenceOriginalKthCollectionSourceSections.kthCPrechoiceStage at hstage
        rw [hdata'] at hstage
        simp only [hnonempty, ↓reduceIte, Option.map_some] at hstage
        exact (Prod.mk.inj (Option.some.inj hstage)).1.symm
      subst pending
      have hformed :
          ReferenceFirstReplacementCollectionPredictableStages.choiceStage r P i = .formed :=
        hsource.mp hstage
      exact ⟨(ReferenceFirstReplacementCollectionPredictableStages.choiceStage_formed_iff
        r P i).mp hformed, hip⟩
    · rintro ⟨hformed, hip⟩
      refine ⟨ledger.pending, hip, ?_⟩
      unfold ReferenceOriginalKthCollectionSourceSections.kthCPrechoiceStage
      rw [hdata']
      simp only [hnonempty, ↓reduceIte, Option.map_some]
      have hindex :
          ReferenceOriginalKthCollectionSourceSections.kthFollowerIndex (p := p) i = i := by
        apply Fin.ext
        rfl
      have hchoice := hsource.mpr
        ((ReferenceFirstReplacementCollectionPredictableStages.choiceStage_formed_iff
          r P i).2 hformed)
      simpa [ReferenceOriginalKthCollectionSourceSections.kthCPrechoiceStage,
        hdata', hnonempty, hindex,
        ReferenceFirstReplacementCollectionPredictableStages.preRoundStart_choiceStage
          rate rewards C_star C_h r.input.time i source r P hactual] using hchoice
  · have hempty : ledger.pending = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnonempty
    unfold ReferenceOriginalKthCollectionSourceSections.kthCPrechoiceStage
    rw [hdata']
    simp [hempty]

/-- An actual physical row contributes at most one retained UP-positive
entry for a fixed follower. -/
theorem actual_record_up_positive_entries_length_le_one
    (r : Record rate) (i : Fin (p.m - 1)) :
    (ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries r i).length ≤ 1 :=
  ReferenceFirstReplacementCollectionStoppedPureUpQuota.recordUpPositiveEntries_length_le_one
    r i

private theorem flatMap_length_le_rows
    {α β : Type} (xs : List α) (f : α → List β)
    (hunit : ∀ x, (f x).length ≤ 1) :
    (xs.flatMap f).length ≤ xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      rw [List.flatMap_cons, List.length_append]
      have hx := hunit x
      have htail := ih
      simp only [List.length_cons]
      omega

/-- The formed-UP count on any actual prefix is at most its number of
physical rows. The source-specific 2Q bound is supplied by the canonical
stopping argument, not by this one-row accounting fact. -/
theorem actual_formed_up_count_le_rows
    (K : List (Record rate)) (i : Fin (p.m - 1))
    (M : OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta)) (j : ℕ) :
    (ReferenceFirstReplacementCollectionStoppedPureUpQuota.formedPositiveEntries
      (K.take j) i M).length ≤ (K.take j).length := by
  apply flatMap_length_le_rows
  intro r
  by_cases hformed :
      ReferenceFirstReplacementCollectionStoppedPureUpQuota.replyFormedAt r i M
  · simpa [ReferenceFirstReplacementCollectionStoppedPureUpQuota.formedPositiveEntries,
      hformed] using actual_record_up_positive_entries_length_le_one (rate := rate) r i
  · simp [hformed]

/-- Every summand of the literal formed-UP source readout is between zero and
one, so its finite-prefix total is bounded by the number of actual rows. -/
theorem actualFormedUpPrefixReadoutSum_bounds
    (source : SourceInput p) (K : List (Record rate)) (j beta : ℕ)
    (i : Fin (p.m - 1)) :
    0 ≤ actualFormedUpPrefixReadoutSum rate rewards C_star C_h source K j beta i ∧
      actualFormedUpPrefixReadoutSum rate rewards C_star C_h source K j beta i ≤
        ((K.take (min j K.length)).length : ℝ) := by
  let f : Record rate → ℝ := fun r =>
    (if r.input.time.val + 1 ≤ beta then (1 : ℝ) else 0) *
      (if ∃ pending : Finset (Fin (p.m - 1)),
          i ∈ pending ∧
            ReferenceOriginalKthCollectionSourceSections.kthCPrechoiceStage
              rate rewards C_star C_h r.input.time i source = some (pending, .formed)
        then (1 : ℝ) else 0) *
      ReferenceFirstCollectionUpConditionalService.actualFirstCollectionUpReadout
        (rate := rate) rewards C_star C_h i r.input.time source
  have hf : ∀ r, 0 ≤ f r ∧ f r ≤ 1 := by
    intro r
    dsimp only [f]
    by_cases hdate : r.input.time.val + 1 ≤ beta <;>
      by_cases hstage : ∃ pending : Finset (Fin (p.m - 1)), i ∈ pending ∧
        ReferenceOriginalKthCollectionSourceSections.kthCPrechoiceStage
          rate rewards C_star C_h r.input.time i source = some (pending, .formed)
    all_goals simp only [hdate, hstage, ite_true, ite_false, zero_mul, mul_zero,
      one_mul]
    all_goals
      have hread := ReferenceFirstCollectionUpConditionalService.actualFirstCollectionUpReadout_bounds
        (rate := rate) rewards C_star C_h i r.input.time source
      constructor <;> nlinarith
  unfold actualFormedUpPrefixReadoutSum
  have hsum := List.sum_nonneg (l := (K.take (min j K.length)).map f)
    (fun x hx => by
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hx
      exact (hf r).1)
  have hsumle := List.sum_le_sum (l := K.take (min j K.length))
    (f := f) (g := fun _ : Record rate => (1 : ℝ))
    (fun r _hr => (hf r).2)
  change 0 ≤ ((K.take (min j K.length)).map f).sum ∧
    ((K.take (min j K.length)).map f).sum ≤
      ((K.take (min j K.length)).length : ℝ)
  constructor
  · exact hsum
  · simpa using hsumle


private theorem choice_of_tail
    {rate : RateInput p} (r : ReferenceCompletePhysicalHistory.RoundRecord p rate)
    (tail : ReferenceCollectionPhaseHistory.Tail r.input)
    (htail : ReferenceCollectionPhaseHistory.executedTail r.input = some tail) :
    ∃ c : ReferenceCollectionSegmentExtraction.Choice rate,
      ReferenceCollectionSegmentExtraction.choice r.input = some c ∧
      tail = ⟨c.payload, c.preLedger, c.started, c.weights⟩ := by
  classical
  unfold ReferenceCollectionPhaseHistory.executedTail at htail
  dsimp only at htail
  split at htail <;> try contradiction
  rename_i hselected
  unfold ReferenceCollectionSegmentExtraction.choice
  rw [ite_eq_right hselected]
  cases hc : (ReferenceActivePhysicalStep.prepare r.input).coordinator with
  | first o => cases o <;> simp only [hc] at htail <;> contradiction
  | live registers owned base o =>
    cases o <;> simp only [hc] at htail <;> try contradiction
    cases Option.some.inj htail
    exact ⟨_, rfl, rfl⟩
  | collection payload ledger clock cutoff o =>
    cases o <;> simp only [hc] at htail <;> try contradiction
    cases Option.some.inj htail
    exact ⟨_, rfl, rfl⟩
  | dagger => simp only [hc, reduceCtorEq] at htail
  | invalidCollectionCutoff => simp only [hc, reduceCtorEq] at htail

private theorem choice_frame
    {rate : RateInput p} (r : ReferenceCompletePhysicalHistory.RoundRecord p rate)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (out : ReferenceActivePhysicalStep.Ledger rate) (saved : Option (Fin p.T × Bool))
    (hout : r.output.next.coordinator = .collection payload out saved) :
    ∃ c : ReferenceCollectionSegmentExtraction.Choice rate,
      ReferenceCollectionSegmentExtraction.choice r.input = some c ∧
      c.payload = payload ∧
      out.pending = ReferenceCollectionPhaseHistory.eraseEvent c.preLedger.pending
        (ReferenceCollectionPhaseHistory.acceptedLabel r.input) := by
  obtain ⟨tail, htail, hframe, _hsigma⟩ :=
    ReferenceCollectionPhaseHistory.step_collection_frame r.input payload out saved (by
      rw [← r.output_eq]
      exact hout)
  obtain ⟨c, hc, ht⟩ := choice_of_tail r tail htail
  have hpost : r.output.coordinator = ReferenceActivePhysicalStep.collectionPostChoice
      (ReferenceActivePhysicalStep.prepare r.input) c.payload c.preLedger c.started c.weights := by
    rw [r.output_eq]
    exact ReferenceCollectionSegmentExtraction.choice_tail r.input c hc
  have hnext : r.output.coordinator.configuration = .collection payload out saved := by
    rw [r.output_eq] at hout ⊢
    exact hout
  have hpayload := ReferenceAssignmentPayloadPersistence.collectionPostChoice_payload_frame
    (ReferenceActivePhysicalStep.prepare r.input) c.payload c.preLedger c.started c.weights
  rw [← hpost, hnext] at hpayload
  simp only [ReferenceAssignmentPayloadPersistence.storedPayload, reduceCtorEq,
    Option.some.injEq, false_or] at hpayload
  refine ⟨c, hc, hpayload.symm, ?_⟩
  rw [ht] at hframe
  exact hframe

private theorem actual_record_of_index
    (rate : RateInput p) (source : SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (n : ℕ) (r : ReferenceCompletePhysicalHistory.RoundRecord p rate)
    (hr : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[n]? = some r)
    (htime : r.input.time.val =
      ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h + n) :
    ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h r.input.time source = some r := by
  have hstart : ReferenceCompletePhysicalHistory.physicalStart
      rate source rewards C_star C_h ≤ r.input.time.val := by omega
  have hindex : r.input.time.val - ReferenceCompletePhysicalHistory.physicalStart
      rate source rewards C_star C_h = n := by omega
  unfold ReferenceSourcePrefixHistoryFiltration.actualRecord
  rw [ite_eq_left hstart, hindex]
  exact hr

private theorem pending_antitone
    (L : ℕ) (P : Fin L → Finset (Fin (p.m - 1)))
    (hstep : ∀ n (hn : n + 1 < L),
      P ⟨n + 1, hn⟩ ⊆ P ⟨n, by omega⟩) :
    ∀ a b : Fin L, a.val ≤ b.val → P b ⊆ P a := by
  intro a ⟨b, hb⟩ hab
  change a.val ≤ b at hab
  induction b with
  | zero =>
    have ha : a = (⟨0, hb⟩ : Fin L) := by
      apply Fin.ext
      change a.val = 0
      omega
    rw [ha]
  | succ b ih =>
    by_cases heq : a.val = b + 1
    · have ha : a = ⟨b + 1, hb⟩ := Fin.ext heq
      rw [ha]
    · exact (hstep b hb).trans (ih (by omega) (by omega))


/-- Choices, incoming banks and outgoing pending sets on the original cutoff
collection. Pending removal persists throughout this same physical collection. -/
theorem actual_cutoff_choice_trace
    (source : SourceInput p) (e : ℕ) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h
    match R[e]? with
    | none => True
    | some cut =>
      match cut.output.preparation.coordinator with
      | .live registers _ _ (.cutoffChosen ..) =>
        let K := cut :: (R.drop (e + 1)).takeWhile
          (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
        ∃ (cs : Fin K.length → ReferenceCollectionSegmentExtraction.Choice rate)
          (out : Fin K.length → ReferenceActivePhysicalStep.Ledger rate)
          (saved : Fin K.length → Option (Fin p.T × Bool)),
          (∀ q : Fin K.length,
            ReferenceCollectionSegmentExtraction.choice (K.get q).input = some (cs q) ∧
            (cs q).payload = registers.payload ∧
            ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
              (K.get q).input.time source = some (K.get q) ∧
            (K.get q).input.time.val =
              ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h +
                (e + q.val) ∧
            (K.get q).output.next.coordinator =
              .collection registers.payload (out q) (saved q)) ∧
          (∀ a b : Fin K.length, a.val ≤ b.val →
            (cs b).preLedger.pending ⊆ (cs a).preLedger.pending) ∧
          (∀ q a : Fin K.length, q.val < a.val →
            (cs a).preLedger.pending ⊆ (out q).pending)
      | _ => True := by
  have hframes :=
    ReferenceOriginalCollectionReplyFormationChronology.actual_cutoff_collection_prefix
      rate source rewards C_star C_h e
  dsimp only at hframes ⊢
  set R := ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate source rewards C_star C_h
  cases hcut : R[e]? with
  | none => trivial
  | some cut =>
    simp only [hcut] at hframes ⊢
    cases hcoord : cut.output.preparation.coordinator with
    | first _ => trivial
    | collection _ _ _ _ _ => trivial
    | dagger => trivial
    | invalidCollectionCutoff => trivial
    | live registers owned base outcome =>
      simp only [hcoord] at hframes ⊢
      cases outcome <;> try trivial
      rename_i dispatched hstart ledger hinitialization hledger hdomains
        hclock hpending hassignment selection
      dsimp only at hframes ⊢
      let K := cut :: (R.drop (e + 1)).takeWhile
        (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
      let Z := fun j => ReferenceCollectionSegmentExtraction.endpointState
        cut.input.state (K.take j)
      obtain ⟨hrecords, _hnoLater, hcollections⟩ := hframes
      change (∀ j : ℕ, 1 ≤ j → j ≤ K.length →
        ∃ out saved, (Z j).coordinator = .collection registers.payload out saved) at hcollections
      have houtputs : ∀ q : Fin K.length, ∃ out saved,
          (Z (q.val + 1)).coordinator = .collection registers.payload out saved := by
        intro q
        exact hcollections (q.val + 1) (by omega) (by have := q.isLt; omega)
      choose out saved hout using houtputs
      have hchoiceData : ∀ q : Fin K.length,
          ∃ c : ReferenceCollectionSegmentExtraction.Choice rate,
            ReferenceCollectionSegmentExtraction.choice (K.get q).input = some c ∧
            c.payload = registers.payload ∧
            (out q).pending = ReferenceCollectionPhaseHistory.eraseEvent c.preLedger.pending
              (ReferenceCollectionPhaseHistory.acceptedLabel (K.get q).input) := by
        intro q
        apply choice_frame (K.get q) registers.payload (out q) (saved q)
        rw [(hrecords q).2.2.2.2]
        exact hout q
      choose cs hc hpayload hframe using hchoiceData
      have hnext : ∀ n (hn : n + 1 < K.length),
          (cs ⟨n + 1, hn⟩).preLedger.pending = (out ⟨n, by omega⟩).pending := by
        intro n hn
        let q : Fin K.length := ⟨n, by omega⟩
        let next : Fin K.length := ⟨n + 1, hn⟩
        have hstate : (K.get next).input.state.coordinator =
            .collection registers.payload (out q) (saved q) := by
          rw [(hrecords next).2.2.2.1]
          exact hout q
        exact congrArg (fun L => L.pending)
          (ReferenceCollectionSegmentExtraction.choice_collection_pre
            (K.get next).input registers.payload (out q) (saved q) (cs next)
            hstate (hc next)).1
      have hstep : ∀ n (hn : n + 1 < K.length),
          (cs ⟨n + 1, hn⟩).preLedger.pending ⊆ (cs ⟨n, by omega⟩).preLedger.pending := by
        intro n hn
        rw [hnext n hn, hframe]
        cases ReferenceCollectionPhaseHistory.acceptedLabel (K.get ⟨n, by omega⟩).input with
        | none => exact Finset.Subset.refl _
        | some j => exact Finset.erase_subset j _
      have hmono := pending_antitone K.length
        (fun q => (cs q).preLedger.pending) hstep
      refine ⟨cs, out, saved, ?_, hmono, ?_⟩
      · intro q
        refine ⟨hc q, hpayload q, ?_, (hrecords q).2.1, ?_⟩
        · exact actual_record_of_index rate source rewards C_star C_h (e + q.val)
            (K.get q) (hrecords q).1 (hrecords q).2.1
        · rw [(hrecords q).2.2.2.2]
          exact hout q
      · change ∀ q a : Fin K.length, q.val < a.val →
          (cs a).preLedger.pending ⊆ (out q).pending
        intro q a hqa
        have hn : q.val + 1 < K.length := by have := a.isLt; omega
        have hsub := hmono ⟨q.val + 1, hn⟩ a (by change q.val + 1 ≤ a.val; omega)
        rw [hnext q.val hn] at hsub
        exact hsub

private theorem no_up_ambiguity_before
    (source : SourceInput p) (t : Fin p.T)
    (ht : t.val + 1 < ReferenceCompleteSignedFirstBadCalendar.firstBadDate
      rate rewards C_star C_h source) :
    ¬ ReferenceCompleteAwaitedBatchSourceCoverage.sourceUpFixedAwaitedCompletionAt
      rate rewards C_star C_h source t := by
  intro h
  have habsent := (ReferenceCompleteSignedFirstBadCalendar.strict_prefix_branch_absence
    rate rewards C_star C_h source t ht).1
  apply habsent
  refine ⟨ReferenceCompleteSignedFirstBadCalendar.inclusive_gate_through_first_bad_date
    rate rewards C_star C_h source t (Nat.le_of_lt ht), Or.inr ?_⟩
  exact Or.inr h

private theorem retained_prefix_length_le
    (K : List (Record rate)) (i : Fin (p.m - 1)) (j : ℕ) :
    (ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries (K.take j) i).length ≤
      (ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries K i).length := by
  exact ((List.take_prefix j K).flatMap
    (fun r => ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries r i)).length_le

/-- Before any actual still-pending choice, the formed-UP count is strictly
below two decoder batches. Both acceptance and the original fixed-awaited
failure are excluded in its strict physical past, with no assumed history. -/
theorem actual_cutoff_pending_pre_count_lt
    (source : SourceInput p) (e : ℕ) (i : Fin (p.m - 1)) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h
    match R[e]? with
    | none => True
    | some cut =>
      match cut.output.preparation.coordinator with
      | .live registers _ _ (.cutoffChosen ..) =>
        let K := cut :: (R.drop (e + 1)).takeWhile
          (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
        let beta := ReferenceCompleteSignedFirstBadCalendar.firstBadDate
          rate rewards C_star C_h source
        ∀ (a : Fin K.length) (c : ReferenceCollectionSegmentExtraction.Choice rate),
          ReferenceCollectionSegmentExtraction.choice (K.get a).input = some c →
          i ∈ c.preLedger.pending → (K.get a).input.time.val + 1 ≤ beta →
          (ReferenceFirstReplacementCollectionStoppedPureUpQuota.formedPositiveEntries
            (K.take a.val) i (registers.payload.downRecord i)).length <
              2 * AffineBatchDecoder.quota p
      | _ => True := by
  have hdet := actual_cutoff_formed_up_first_threshold_detector
    rate source rewards C_star C_h e i
  have htrace := actual_cutoff_choice_trace rate rewards C_star C_h source e
  dsimp only at hdet htrace ⊢
  set R := ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate source rewards C_star C_h
  cases hcut : R[e]? with
  | none => trivial
  | some cut =>
    simp only [hcut] at hdet htrace ⊢
    cases hcoord : cut.output.preparation.coordinator with
    | first _ => trivial
    | collection _ _ _ _ _ => trivial
    | dagger => trivial
    | invalidCollectionCutoff => trivial
    | live registers owned base outcome =>
      simp only [hcoord] at hdet htrace ⊢
      cases outcome <;> try trivial
      rename_i dispatched hstart ledger hinitialization hledger hdomains
        hclock hpending hassignment selection
      dsimp only at hdet htrace ⊢
      let K := cut :: (R.drop (e + 1)).takeWhile
        (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
      let Z := fun j => ReferenceCollectionSegmentExtraction.endpointState
        cut.input.state (K.take j)
      let Q := AffineBatchDecoder.quota p
      let M := registers.payload.downRecord i
      obtain ⟨cs, out, saved, hrows, _hmono, hremoved⟩ := htrace
      change ∀ (a : Fin K.length) (c : ReferenceCollectionSegmentExtraction.Choice rate), _
      intro a c hc hip hdate
      have hca : cs a = c := Option.some.inj ((hrows a).1.symm.trans hc)
      have hipA : i ∈ (cs a).preLedger.pending := hca.symm ▸ hip
      rcases hdet with hnone | hformed
      · rw [hnone.2 a.val]
        have hQ : 0 < Q := AffineBatchDecoder.quota_pos p
        change 0 < 2 * Q
        omega
      · obtain ⟨b, hb, anchor, U, _hstatus, _hdomain, _hlast, _hfields,
          _hsigma, _hpositive, _hbank, hnU, hentries, hthreshold⟩ := hformed
        let N := Q - ((Z b).upDecoderBank i).pending.length + Q
        have hN : N ≤ 2 * Q := by dsimp [N]; omega
        change (ReferenceFirstReplacementCollectionStoppedPureUpQuota.formedPositiveEntries
          (K.take a.val) i M).length < 2 * Q
        suffices hsmall :
            (ReferenceFirstReplacementCollectionStoppedPureUpQuota.formedPositiveEntries
              (K.take a.val) i M).length < N by omega
        rw [hentries a.val]
        rcases hthreshold with hshort | ⟨m, hm, hmlen, _hcount, hbefore,
            _hformedCount, q, _hbq, hqm, houtcome⟩
        · have hle := retained_prefix_length_le (rate := rate) (K.drop b) i (a.val - b)
          rw [List.drop_take]
          exact lt_of_le_of_lt hle hshort
        · by_contra hnot
          have hma : m ≤ a.val - b := by
            by_contra hnotma
            have hsmall := hbefore (a.val - b) (by omega)
            rw [List.drop_take] at hnot
            exact hnot hsmall
          have hqa : q.val < a.val := by omega
          rcases houtcome with ⟨_haccepted, finished, proposal, hout, hnotpending⟩ | hbad
          · have hsub := hremoved q a hqa
            have hpending : i ∈ (out q).pending := hsub hipA
            have hsame := (hrows q).2.2.2.2.symm.trans hout
            have hpendingEq := congrArg (fun config => match config with
              | .collection _ L _ => L.pending
              | _ => ∅) hsame
            change (out q).pending = finished.pending at hpendingEq
            exact hnotpending (hpendingEq ▸ hpending)
          · have htimeA : (K.get a).input.time.val =
                ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h +
                  (e + a.val) := (hrows a).2.2.2.1
            have htimeQ : (K.get q).input.time.val =
                ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h +
                  (e + q.val) := (hrows q).2.2.2.1
            change (K.get a).input.time.val + 1 ≤ _ at hdate
            exact no_up_ambiguity_before rate rewards C_star C_h source
              (K.get q).input.time (by omega) hbad

private theorem actual_record_index_exists
    (source : SourceInput p) (r : Record rate)
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h r.input.time source = some r) :
    ∃ k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h).length,
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val]'k.isLt = r := by
  unfold ReferenceSourcePrefixHistoryFiltration.actualRecord at hr
  split at hr
  · obtain ⟨hk, he⟩ := List.getElem?_eq_some_iff.mp hr
    exact ⟨⟨_, hk⟩, he⟩
  · cases hr

private theorem receiver_ledger_pending
    (rate : RateInput p) (source : SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (r : ReferenceCompletePhysicalHistory.RoundRecord p rate)
    (hr : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[k.val]'k.isLt = r)
    (c : ReferenceCollectionSegmentExtraction.Choice rate)
    (hc : ReferenceCollectionSegmentExtraction.choice r.input = some c)
    (d : ReferenceActivePhysicalStep.UpDiagnostic p rate)
    (hd : r.output.coordinator.up = some d) :
    d.input.ledger.pending = c.preLedger.pending := by
  have hreceiver :=
    ReferenceOriginalCollectionCurrentUpReceiver.actual_collection_current_up_receiver
      rate rewards C_star C_h source k
  dsimp only at hreceiver
  rw [hr] at hreceiver
  rcases hreceiver with hnone | ⟨actual, hactual, hdata⟩
  · rw [hc] at hnone
    contradiction
  · have heq : actual = c := Option.some.inj (hactual.symm.trans hc)
    subst actual
    obtain ⟨_birth, _hbefore, _hbirth, _hsigma, _hrows, _hJ, _hrewards,
      _recording, L, actualD, _received, _bank, _finished, _clock,
      _htail, _hrecording, _hstart, hpendingL, _hsigmaL, _hsite, _hcheck,
      hdiag, hinput, _hrest⟩ := hdata
    have hD : actualD = d := Option.some.inj (hdiag.symm.trans hd)
    subst actualD
    rw [hinput]
    exact hpendingL

private theorem actual_record_up_positive_pending
    (source : SourceInput p) (r : Record rate)
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h r.input.time source = some r)
    (c : ReferenceCollectionSegmentExtraction.Choice rate)
    (hc : ReferenceCollectionSegmentExtraction.choice r.input = some c)
    (i : Fin (p.m - 1))
    (hpositive : 0 < (ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries r i).length) :
    i ∈ c.preLedger.pending := by
  obtain ⟨k, hk⟩ := actual_record_index_exists rate rewards C_star C_h source r hr
  cases hd : r.output.coordinator.up with
  | none => simp [ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries, hd] at hpositive
  | some d =>
    by_cases hi : ReferenceCoordinatorUpDecoderReplay.retainedUpFollower d = i
    · have heligible : AffineBatchDecoder.eligible (CoordinatorUpReception.roundInput d.input) := by
        by_contra hn
        simp [ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries, hd, hi,
          AffineBatchDecoder.positiveAt, ReferenceCoordinatorUpDecoderReplay.constantInputTrace,
          hn] at hpositive
      have hpending :=
        ((CoordinatorUpReception.roundInput_selected_iff_gate d.input).mp heligible.1).2.2
      rw [receiver_ledger_pending rate source rewards C_star C_h k r hk c hc d hd] at hpending
      change d.input.selectedFollower = i at hi
      exact hi ▸ hpending
    · simp [ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries, hd, hi] at hpositive

/-- The original source UP readout counts exactly the retained eligible
physical UP entry. The diagnostic index and Boolean test are derived from the
actual row; no source/diagnostic equality is supplied by the caller. -/
theorem actual_record_up_readout_eq_length
    (source : SourceInput p) (r : Record rate)
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h r.input.time source = some r)
    (i : Fin (p.m - 1)) :
    ReferenceFirstCollectionUpConditionalService.actualFirstCollectionUpReadout
      (rate := rate) rewards C_star C_h i r.input.time source =
        ((ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries r i).length : ℝ) := by
  unfold ReferenceFirstCollectionUpConditionalService.actualFirstCollectionUpReadout
  rw [hr]
  dsimp only
  rw [ReferenceActiveAffinePositiveTest.record_upPositive]
  cases hd : r.output.coordinator.up with
  | none => simp [ReferenceActiveAffinePositiveTest.upDiagnosticPositive,
      ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries, hd]
  | some d =>
    obtain ⟨_L, _hsite, _hledger, _hbank, _htime, _hobs, hsender, _hrest⟩ :=
      ReferenceCoordinatorUpPhysicalCall.record_retained_up_input_fields r d hd
    have hindex : ReferenceCoordinatorUpDecoderReplay.retainedUpFollower d =
        PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
          (r.input.row.2 r.input.time).1 :=
      hsender.trans (CoordinatorUpMeasurability.selectedFollowerIndex_eq_draw _)
    have hiff :
        PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
          (r.input.row.2 r.input.time).1 =
            ReferenceFirstCollectionUpConditionalService.followerIndex i ↔
          ReferenceCoordinatorUpDecoderReplay.retainedUpFollower d = i := by
      constructor
      · intro h
        exact hindex.trans h
      · intro h
        exact hindex.symm.trans h
    simp only [ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries, hd,
      ReferenceActiveAffinePositiveTest.upDiagnosticPositive]
    by_cases hi : ReferenceCoordinatorUpDecoderReplay.retainedUpFollower d = i
    · have hdraw := hiff.mpr hi
      by_cases he : AffineBatchDecoder.eligible (CoordinatorUpReception.roundInput d.input)
      · simp only [hi, hdraw, true_and, ite_true, he, decide_true,
          AffineBatchDecoder.positiveAt, ReferenceCoordinatorUpDecoderReplay.constantInputTrace,
          List.length_singleton, Nat.cast_one]
      · simp only [hi, hdraw, true_and, ite_true, he, decide_false, Bool.false_eq_true,
          ite_false, AffineBatchDecoder.positiveAt,
          ReferenceCoordinatorUpDecoderReplay.constantInputTrace, List.length_nil, Nat.cast_zero]
    · have hdraw := mt hiff.mp hi
      simp only [hi, hdraw, false_and, ite_false, List.length_nil, Nat.cast_zero]

private theorem formed_prefix_succ
    (K : List (Record rate)) (i : Fin (p.m - 1))
    (M : OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (n : ℕ) (hn : n < K.length) :
    (ReferenceFirstReplacementCollectionStoppedPureUpQuota.formedPositiveEntries
      (K.take (n + 1)) i M).length =
    (ReferenceFirstReplacementCollectionStoppedPureUpQuota.formedPositiveEntries
      (K.take n) i M).length +
      (if ReferenceFirstReplacementCollectionStoppedPureUpQuota.replyFormedAt K[n] i M
        then (ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries K[n] i).length else 0) := by
  rw [List.take_succ_eq_append_getElem hn]
  simp only [ReferenceFirstReplacementCollectionStoppedPureUpQuota.formedPositiveEntries,
    List.flatMap_append, List.flatMap_singleton, List.length_append]
  split <;> rfl

/-- Every natural prefix of the same original cutoff collection, stopped
inclusively at its literal first bad date, has at most two batches of formed
UP positives. The detecting physical row is retained. -/
theorem actual_cutoff_formed_up_count_le
    (source : SourceInput p) (e j : ℕ) (i : Fin (p.m - 1)) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h
    match R[e]? with
    | none => True
    | some cut =>
      match cut.output.preparation.coordinator with
      | .live registers _ _ (.cutoffChosen ..) =>
        let K := cut :: (R.drop (e + 1)).takeWhile
          (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
        let beta := ReferenceCompleteSignedFirstBadCalendar.firstBadDate
          rate rewards C_star C_h source
        (ReferenceFirstReplacementCollectionStoppedPureUpQuota.formedPositiveEntries
          (K.take (actualOldDownPrefixLength rate K j beta)) i
          (registers.payload.downRecord i)).length ≤ 2 * AffineBatchDecoder.quota p
      | _ => True := by
  have hstrict := actual_cutoff_pending_pre_count_lt rate rewards C_star C_h source e i
  have htrace := actual_cutoff_choice_trace rate rewards C_star C_h source e
  dsimp only at hstrict htrace ⊢
  set R := ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate source rewards C_star C_h
  cases hcut : R[e]? with
  | none => trivial
  | some cut =>
    simp only [hcut] at hstrict htrace ⊢
    cases hcoord : cut.output.preparation.coordinator with
    | first _ => trivial
    | collection _ _ _ _ _ => trivial
    | dagger => trivial
    | invalidCollectionCutoff => trivial
    | live registers owned base outcome =>
      simp only [hcoord] at hstrict htrace ⊢
      cases outcome <;> try trivial
      rename_i dispatched hstart ledger hinitialization hledger hdomains
        hclock hpending hassignment selection
      dsimp only at hstrict htrace ⊢
      let K := cut :: (R.drop (e + 1)).takeWhile
        (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
      let M := registers.payload.downRecord i
      let beta := ReferenceCompleteSignedFirstBadCalendar.firstBadDate
        rate rewards C_star C_h source
      obtain ⟨cs, _out, _saved, hrows, _hmono, _hremoved⟩ := htrace
      have hbounded : ∀ n : ℕ, n ≤ K.length →
          (∀ a : Fin K.length, a.val < n → (K.get a).input.time.val + 1 ≤ beta) →
          (ReferenceFirstReplacementCollectionStoppedPureUpQuota.formedPositiveEntries
            (K.take n) i M).length ≤ 2 * AffineBatchDecoder.quota p := by
        intro n
        induction n with
        | zero =>
          intro _ _
          simp [ReferenceFirstReplacementCollectionStoppedPureUpQuota.formedPositiveEntries]
        | succ n ih =>
          intro hn hdates
          have hnK : n < K.length := by omega
          let a : Fin K.length := ⟨n, hnK⟩
          have hpre := ih (by omega) (fun q hq => hdates q (by omega))
          rw [formed_prefix_succ (rate := rate) K i M n hnK]
          by_cases hf : ReferenceFirstReplacementCollectionStoppedPureUpQuota.replyFormedAt K[n] i M
          · rw [ite_eq_left hf]
            by_cases hp : 0 < (ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries K[n] i).length
            · have hpend := actual_record_up_positive_pending rate rewards C_star C_h source
                (K.get a) (hrows a).2.2.1 (cs a) (hrows a).1 i hp
              have hs := hstrict a (cs a) (hrows a).1 hpend (hdates a (by dsimp [a]; omega))
              have hu := actual_record_up_positive_entries_length_le_one (rate := rate) K[n] i
              change (ReferenceFirstReplacementCollectionStoppedPureUpQuota.formedPositiveEntries
                (K.take n) i M).length < 2 * AffineBatchDecoder.quota p at hs
              omega
            · have hz : (ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries K[n] i).length = 0 := by omega
              rw [hz, Nat.add_zero]
              exact hpre
          · rw [ite_eq_right hf, Nat.add_zero]
            exact hpre
      let L := actualOldDownPrefixLength rate K j beta
      have hpref : (K.take j).takeWhile (fun r => decide (r.input.time.val + 1 ≤ beta)) <+: K :=
        (List.takeWhile_prefix _).trans (List.take_prefix j K)
      have hL : L ≤ K.length := hpref.length_le
      have htake : (K.take j).takeWhile (fun r => decide (r.input.time.val + 1 ≤ beta)) =
          K.take L := (List.prefix_iff_eq_take.mp hpref)
      apply hbounded L hL
      intro a ha
      have hmem : K.get a ∈ K.take L := List.mem_take_iff_getElem.mpr
        ⟨a.val, lt_min ha a.isLt, by simp only [List.get_eq_getElem]⟩
      rw [← htake] at hmem
      have hgate := List.mem_takeWhile_imp hmem
      exact of_decide_eq_true hgate

/-- The literal source FORMED mask selects the same current reply and actual
pending set, including the initial LIVE cutoff row. Formation alone does not
imply that the follower remains pending. -/
theorem actual_cutoff_source_formed_mask
    (source : SourceInput p) (e : ℕ) (i : Fin (p.m - 1)) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h
    match R[e]? with
    | none => True
    | some cut =>
      match cut.output.preparation.coordinator with
      | .live registers _ _ (.cutoffChosen ..) =>
        let K := cut :: (R.drop (e + 1)).takeWhile
          (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
        ∀ (a : Fin K.length) (c : ReferenceCollectionSegmentExtraction.Choice rate),
          ReferenceCollectionSegmentExtraction.choice (K.get a).input = some c →
          ((∃ pending : Finset (Fin (p.m - 1)), i ∈ pending ∧
              ReferenceOriginalKthCollectionSourceSections.kthCPrechoiceStage
                rate rewards C_star C_h (K.get a).input.time i source =
                  some (pending, .formed)) ↔
            ReferenceFirstReplacementCollectionStoppedPureUpQuota.replyFormedAt
              (K.get a) i (registers.payload.downRecord i) ∧ i ∈ c.preLedger.pending)
      | _ => True := by
  have htrace := actual_cutoff_choice_trace rate rewards C_star C_h source e
  have hframes :=
    ReferenceOriginalCollectionReplyFormationChronology.actual_cutoff_collection_prefix
      rate source rewards C_star C_h e
  dsimp only at htrace hframes ⊢
  set R := ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate source rewards C_star C_h
  cases hcut : R[e]? with
  | none => trivial
  | some cut =>
    simp only [hcut] at htrace hframes ⊢
    obtain ⟨he, _hget⟩ := List.getElem?_eq_some_iff.mp hcut
    have hhead := ReferenceOriginalCollectionOldDownChronology.actual_live_cutoff_choice_at
      rate rewards C_star C_h source e he i
    dsimp only at hhead
    rw [show (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[e]? = some cut from hcut] at hhead
    dsimp only at hhead
    cases hcoord : cut.output.preparation.coordinator with
    | first _ => trivial
    | collection _ _ _ _ _ => trivial
    | dagger => trivial
    | invalidCollectionCutoff => trivial
    | live registers owned base outcome =>
      simp only [hcoord] at htrace hframes hhead ⊢
      cases outcome <;> try trivial
      rename_i dispatched hstart ledger hinitialization hledger hdomains
        hclock hpending hassignment selection
      dsimp only at htrace hframes hhead ⊢
      let K := cut :: (R.drop (e + 1)).takeWhile
        (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
      let Z := fun j => ReferenceCollectionSegmentExtraction.endpointState
        cut.input.state (K.take j)
      obtain ⟨cs, _out, _saved, hrows, _hmono, _hremoved⟩ := htrace
      obtain ⟨hrecords, _hnolater, hcollections⟩ := hframes
      change ∀ (a : Fin K.length) (c : ReferenceCollectionSegmentExtraction.Choice rate), _
      intro a c hc
      have hactual := (hrows a).2.2.1
      by_cases ha0 : a.val = 0
      · have hr0 : K.get a = cut := by simp only [List.get_eq_getElem, K, ha0, List.getElem_cons_zero]
        rw [hr0] at hc hactual ⊢
        obtain ⟨headC, hheadC, hheadP, _hword, data, hd, hdP, hdPending, _hdCutoff⟩ := hhead
        have hcc : c = headC := Option.some.inj (hc.symm.trans hheadC)
        subst c
        have hstage : ReferenceOriginalKthCollectionSourceSections.kthCPrechoiceStage
            rate rewards C_star C_h cut.input.time i source =
            some (headC.preLedger.pending,
              ReferenceFirstReplacementCollectionPredictableStages.choiceStage cut registers.payload i) := by
          unfold ReferenceOriginalKthCollectionSourceSections.kthCPrechoiceStage
          rw [hd]
          simp only [Option.map_some, hdP, hdPending, hheadP]
          apply congrArg some
          apply congrArg (fun stage => (headC.preLedger.pending, stage))
          exact ReferenceFirstReplacementCollectionPredictableStages.preRoundStart_choiceStage
            rate rewards C_star C_h cut.input.time i source cut registers.payload hactual
        rw [hstage]
        constructor
        · rintro ⟨pending, hip, hs⟩
          obtain ⟨hp, hformed⟩ := Prod.mk.inj (Option.some.inj hs)
          refine ⟨(ReferenceFirstReplacementCollectionPredictableStages.choiceStage_formed_iff
            cut registers.payload i).mp hformed, ?_⟩
          exact hp ▸ hip
        · rintro ⟨hf, hip⟩
          exact ⟨headC.preLedger.pending, hip, congrArg (fun stage => some (_, stage))
            ((ReferenceFirstReplacementCollectionPredictableStages.choiceStage_formed_iff
              cut registers.payload i).mpr hf)⟩
      · obtain ⟨L, proposal, hL⟩ := hcollections a.val (by omega) (Nat.le_of_lt a.isLt)
        have hstate : (K.get a).input.state.coordinator = .collection registers.payload L proposal := by
          rw [(hrecords a).2.2.2.1]
          exact hL
        have hpre := (ReferenceCollectionSegmentExtraction.choice_collection_pre
          (K.get a).input registers.payload L proposal c hstate hc).1
        have hiff := actual_source_formed_stage_iff rate rewards C_star C_h source
          (K.get a) hactual registers.payload L proposal hstate i
        change _ ↔ ReferenceFirstReplacementCollectionStoppedPureUpQuota.replyFormedAt
          (K.get a) i (registers.payload.downRecord i) ∧ i ∈ L.pending at hiff
        rw [hpre]
        exact hiff

private theorem date_gated_formed_sum
    (K : List (Record rate)) (i : Fin (p.m - 1)) (M : OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (beta : ℕ) (f : Record rate → ℝ)
    (hpoint : ∀ a : Fin K.length, f (K.get a) =
      if ReferenceFirstReplacementCollectionStoppedPureUpQuota.replyFormedAt (K.get a) i M
        then ((ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries (K.get a) i).length : ℝ) else 0)
    (hmono : ∀ a b : Fin K.length, b.val ≤ a.val →
      (K.get b).input.time.val ≤ (K.get a).input.time.val)
    (j : ℕ) :
    ((K.take j).map fun r => if r.input.time.val + 1 ≤ beta then f r else 0).sum =
      ((ReferenceFirstReplacementCollectionStoppedPureUpQuota.formedPositiveEntries
        (K.take (actualOldDownPrefixLength rate K j beta)) i M).length : ℝ) := by
  have hbounded : ∀ n : ℕ, n ≤ K.length →
      ((K.take n).map fun r => if r.input.time.val + 1 ≤ beta then f r else 0).sum =
        ((ReferenceFirstReplacementCollectionStoppedPureUpQuota.formedPositiveEntries
          (K.take (actualOldDownPrefixLength rate K n beta)) i M).length : ℝ) := by
    intro n
    induction n with
    | zero =>
        intro _hn
        simp only [List.take_zero, List.map_nil, List.sum_nil, actualOldDownPrefixLength,
          List.takeWhile_nil, List.length_nil,
          ReferenceFirstReplacementCollectionStoppedPureUpQuota.formedPositiveEntries,
          List.flatMap_nil, List.length_nil, Nat.cast_zero]
    | succ n ih =>
        intro hn
        have hnK : n < K.length := by omega
        have hih := ih (by omega)
        have hsum : ((K.take (n + 1)).map fun r =>
              if r.input.time.val + 1 ≤ beta then f r else 0).sum =
            ((K.take n).map fun r =>
              if r.input.time.val + 1 ≤ beta then f r else 0).sum +
            (if K[n].input.time.val + 1 ≤ beta then f K[n] else 0) := by
          rw [List.take_succ_eq_append_getElem hnK, List.map_append, List.sum_append]
          simp only [List.map_singleton, List.sum_singleton]
        rw [hsum, hih]
        by_cases hgood : K[n].input.time.val + 1 ≤ beta
        · have hall : ∀ r ∈ K.take (n + 1),
              (decide (r.input.time.val + 1 ≤ beta) : Bool) = true := by
            intro r hr
            obtain ⟨b, hb, hbr⟩ := List.mem_take_iff_getElem.mp hr
            have hbK : b < K.length := (lt_min_iff.mp hb).2
            have hbn : b ≤ n := by have := (lt_min_iff.mp hb).1; omega
            have htime := hmono ⟨n, hnK⟩ ⟨b, hbK⟩ hbn
            change K[b].input.time.val ≤ K[n].input.time.val at htime
            rw [hbr] at htime
            exact decide_eq_true (by omega)
          have hLn : actualOldDownPrefixLength rate K n beta = n := by
            unfold actualOldDownPrefixLength
            have hallPre : ∀ r ∈ K.take n,
                (decide (r.input.time.val + 1 ≤ beta) : Bool) = true := by
              intro r hr
              obtain ⟨b, hb, hbr⟩ := List.mem_take_iff_getElem.mp hr
              apply hall r
              exact List.mem_take_iff_getElem.mpr ⟨b,
                lt_min (by have := (lt_min_iff.mp hb).1; omega)
                  (lt_min_iff.mp hb).2, hbr⟩
            rw [(List.takeWhile_eq_self_iff).mpr hallPre]
            simp only [List.length_take, Nat.min_eq_left (Nat.le_of_lt hnK)]
          have hLsucc : actualOldDownPrefixLength rate K (n + 1) beta = n + 1 := by
            unfold actualOldDownPrefixLength
            rw [(List.takeWhile_eq_self_iff).mpr hall]
            simp only [List.length_take, Nat.min_eq_left hn]
          rw [hLn, hLsucc, formed_prefix_succ (rate := rate) K i M n hnK, Nat.cast_add]
          rw [ite_eq_left hgood, show f K[n] =
            if ReferenceFirstReplacementCollectionStoppedPureUpQuota.replyFormedAt K[n] i M then
              ((ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries K[n] i).length : ℝ) else 0 from hpoint ⟨n, hnK⟩]
          split <;> simp only [Nat.cast_zero]
        · have hL : actualOldDownPrefixLength rate K (n + 1) beta =
              actualOldDownPrefixLength rate K n beta := by
            unfold actualOldDownPrefixLength
            rw [List.take_succ_eq_append_getElem hnK, List.takeWhile_append]
            simp only [List.takeWhile_cons, hgood, decide_false, Bool.false_eq_true,
              ite_false, List.takeWhile_nil, List.append_nil]
            split
            · rename_i hlen
              exact hlen.symm
            · rfl
          rw [hL, ite_eq_right hgood, add_zero]
  have htake : K.take (min j K.length) = K.take j := by
    by_cases hj : j ≤ K.length
    · rw [Nat.min_eq_left hj]
    · have hle : K.length ≤ j := by omega
      rw [Nat.min_eq_right hle, List.take_length, List.take_of_length_le hle]
  have h := hbounded (min j K.length) (Nat.min_le_right _ _)
  simpa only [actualOldDownPrefixLength, htake] using h

/-- The literal original-source masked UP sum equals the formed-positive
count on the same date-inclusive prefix. No rewards, diagnostics, source
indices or stage equalities are replaced by surrogates. -/
theorem actual_cutoff_formed_up_readout_eq_count
    (source : SourceInput p) (e j : ℕ) (i : Fin (p.m - 1)) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h
    match R[e]? with
    | none => True
    | some cut =>
      match cut.output.preparation.coordinator with
      | .live registers _ _ (.cutoffChosen ..) =>
        let K := cut :: (R.drop (e + 1)).takeWhile
          (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
        let beta := ReferenceCompleteSignedFirstBadCalendar.firstBadDate
          rate rewards C_star C_h source
        actualFormedUpPrefixReadoutSum rate rewards C_star C_h source K j beta i =
          ((ReferenceFirstReplacementCollectionStoppedPureUpQuota.formedPositiveEntries
            (K.take (actualOldDownPrefixLength rate K j beta)) i
            (registers.payload.downRecord i)).length : ℝ)
      | _ => True := by
  have htrace := actual_cutoff_choice_trace rate rewards C_star C_h source e
  have hmask := actual_cutoff_source_formed_mask rate rewards C_star C_h source e i
  dsimp only at htrace hmask ⊢
  set R := ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate source rewards C_star C_h
  cases hcut : R[e]? with
  | none => trivial
  | some cut =>
    simp only [hcut] at htrace hmask ⊢
    cases hcoord : cut.output.preparation.coordinator with
    | first _ => trivial
    | collection _ _ _ _ _ => trivial
    | dagger => trivial
    | invalidCollectionCutoff => trivial
    | live registers owned base outcome =>
      simp only [hcoord] at htrace hmask ⊢
      cases outcome <;> try trivial
      rename_i dispatched hstart ledger hinitialization hledger hdomains
        hclock hpending hassignment selection
      dsimp only at htrace hmask ⊢
      let K := cut :: (R.drop (e + 1)).takeWhile
        (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
      let M := registers.payload.downRecord i
      let beta := ReferenceCompleteSignedFirstBadCalendar.firstBadDate
        rate rewards C_star C_h source
      obtain ⟨cs, _out, _saved, hrows, _hmono, _hremoved⟩ := htrace
      let f : Record rate → ℝ := fun r =>
        (if ∃ pending : Finset (Fin (p.m - 1)), i ∈ pending ∧
            ReferenceOriginalKthCollectionSourceSections.kthCPrechoiceStage
              rate rewards C_star C_h r.input.time i source = some (pending, .formed)
          then (1 : ℝ) else 0) *
          ReferenceFirstCollectionUpConditionalService.actualFirstCollectionUpReadout
            (rate := rate) rewards C_star C_h i r.input.time source
      have hpoint : ∀ a : Fin K.length, f (K.get a) =
          if ReferenceFirstReplacementCollectionStoppedPureUpQuota.replyFormedAt (K.get a) i M
            then ((ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries (K.get a) i).length : ℝ)
            else 0 := by
        intro a
        dsimp only [f]
        rw [actual_record_up_readout_eq_length rate rewards C_star C_h source
          (K.get a) (hrows a).2.2.1 i]
        let mask : Prop := ∃ pending : Finset (Fin (p.m - 1)), i ∈ pending ∧
          ReferenceOriginalKthCollectionSourceSections.kthCPrechoiceStage
            rate rewards C_star C_h (K.get a).input.time i source = some (pending, .formed)
        have hmaskA : mask ↔
            ReferenceFirstReplacementCollectionStoppedPureUpQuota.replyFormedAt (K.get a) i M ∧
              i ∈ (cs a).preLedger.pending := hmask a (cs a) (hrows a).1
        by_cases hf : ReferenceFirstReplacementCollectionStoppedPureUpQuota.replyFormedAt (K.get a) i M
        · by_cases hip : i ∈ (cs a).preLedger.pending
          · have hs := hmaskA.mpr ⟨hf, hip⟩
            change mask at hs
            dsimp only [mask] at hs
            simp only [hs, hf, ite_true, one_mul]
          · have hs : ¬ mask := fun h => hip (hmaskA.mp h).2
            dsimp only [mask] at hs
            have hz : (ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries (K.get a) i).length = 0 := by
              by_contra hn
              have hp := actual_record_up_positive_pending rate rewards C_star C_h source
                (K.get a) (hrows a).2.2.1 (cs a) (hrows a).1 i (by omega)
              exact hip hp
            simp only [hs, hf, ite_false, ite_true, hz, Nat.cast_zero, mul_zero]
        · have hs : ¬ mask := fun h => hf (hmaskA.mp h).1
          dsimp only [mask] at hs
          simp only [hs, hf, ite_false, zero_mul]
      have htime : ∀ a b : Fin K.length, b.val ≤ a.val →
          (K.get b).input.time.val ≤ (K.get a).input.time.val := by
        intro a b hba
        have ha : (K.get a).input.time.val = _ := (hrows a).2.2.2.1
        have hb : (K.get b).input.time.val = _ := (hrows b).2.2.2.1
        omega
      have htake : K.take (min j K.length) = K.take j := by
        by_cases hj : j ≤ K.length
        · rw [Nat.min_eq_left hj]
        · have hle : K.length ≤ j := by omega
          rw [Nat.min_eq_right hle, List.take_length, List.take_of_length_le hle]
      have hform : actualFormedUpPrefixReadoutSum rate rewards C_star C_h source K j beta i =
          ((K.take j).map fun r => if r.input.time.val + 1 ≤ beta then f r else 0).sum := by
        unfold actualFormedUpPrefixReadoutSum
        rw [htake]
        congr 1
        apply List.map_congr_left
        intro r _hr
        dsimp only [f]
        by_cases ht : r.input.time.val + 1 ≤ beta
        · simp only [ht, ite_true, one_mul]
        · simp only [ht, ite_false, zero_mul]
      exact hform.trans (date_gated_formed_sum rate K i M beta f hpoint htime j)

/-- Canonical formed-UP quota on the literal original LIVE-cutoff collection.
Every inclusive stopped prefix has count and masked readout at most `2Q`.
At an actual current FORMED/pending prechoice the incoming count and readout
are strictly below `2Q`, and the original source stage is produced here. -/
theorem actual_cutoff_formed_up_canonical_quota
    (source : SourceInput p) (e : ℕ) (i : Fin (p.m - 1)) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h
    match R[e]? with
    | none => True
    | some cut =>
      match cut.output.preparation.coordinator with
      | .live registers _ _ (.cutoffChosen ..) =>
        let K := cut :: (R.drop (e + 1)).takeWhile
          (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
        let M := registers.payload.downRecord i
        let beta := ReferenceCompleteSignedFirstBadCalendar.firstBadDate
          rate rewards C_star C_h source
        let Q := AffineBatchDecoder.quota p
        (∀ j : ℕ,
          actualFormedUpPrefixReadoutSum rate rewards C_star C_h source K j beta i =
            ((ReferenceFirstReplacementCollectionStoppedPureUpQuota.formedPositiveEntries
              (K.take (actualOldDownPrefixLength rate K j beta)) i M).length : ℝ) ∧
          (ReferenceFirstReplacementCollectionStoppedPureUpQuota.formedPositiveEntries
            (K.take (actualOldDownPrefixLength rate K j beta)) i M).length ≤ 2 * Q ∧
          actualFormedUpPrefixReadoutSum rate rewards C_star C_h source K j beta i ≤
            (2 * Q : ℕ)) ∧
        ∀ (a : Fin K.length) (c : ReferenceCollectionSegmentExtraction.Choice rate),
          ReferenceCollectionSegmentExtraction.choice (K.get a).input = some c →
          ReferenceFirstReplacementCollectionStoppedPureUpQuota.replyFormedAt (K.get a) i M →
          i ∈ c.preLedger.pending → (K.get a).input.time.val + 1 ≤ beta →
          (∃ pending : Finset (Fin (p.m - 1)), i ∈ pending ∧
            ReferenceOriginalKthCollectionSourceSections.kthCPrechoiceStage
              rate rewards C_star C_h (K.get a).input.time i source =
                some (pending, .formed)) ∧
          (ReferenceFirstReplacementCollectionStoppedPureUpQuota.formedPositiveEntries
            (K.take a.val) i M).length < 2 * Q ∧
          actualFormedUpPrefixReadoutSum rate rewards C_star C_h source K a.val beta i <
            (2 * Q : ℕ)
      | _ => True := by
  have hcounts := fun j : ℕ => actual_cutoff_formed_up_count_le
    rate rewards C_star C_h source e j i
  have hreads := fun j : ℕ => actual_cutoff_formed_up_readout_eq_count
    rate rewards C_star C_h source e j i
  have hstrict := actual_cutoff_pending_pre_count_lt rate rewards C_star C_h source e i
  have hmask := actual_cutoff_source_formed_mask rate rewards C_star C_h source e i
  have htrace := actual_cutoff_choice_trace rate rewards C_star C_h source e
  dsimp only at hcounts hreads hstrict hmask htrace ⊢
  set R := ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate source rewards C_star C_h
  cases hcut : R[e]? with
  | none => trivial
  | some cut =>
    simp only [hcut] at hcounts hreads hstrict hmask htrace ⊢
    cases hcoord : cut.output.preparation.coordinator with
    | first _ => trivial
    | collection _ _ _ _ _ => trivial
    | dagger => trivial
    | invalidCollectionCutoff => trivial
    | live registers owned base outcome =>
      simp only [hcoord] at hcounts hreads hstrict hmask htrace ⊢
      cases outcome <;> try trivial
      rename_i dispatched hstart ledger hinitialization hledger hdomains
        hclock hpending hassignment selection
      dsimp only at hcounts hreads hstrict hmask htrace ⊢
      let K := cut :: (R.drop (e + 1)).takeWhile
        (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
      let M := registers.payload.downRecord i
      let beta := ReferenceCompleteSignedFirstBadCalendar.firstBadDate
        rate rewards C_star C_h source
      obtain ⟨cs, _out, _saved, hrows, _hmono, _hremoved⟩ := htrace
      constructor
      · intro j
        refine ⟨hreads j, hcounts j, ?_⟩
        rw [hreads j]
        exact_mod_cast hcounts j
      · change ∀ (a : Fin K.length) (c : ReferenceCollectionSegmentExtraction.Choice rate), _
        intro a c hc hf hip hdate
        refine ⟨(hmask a c hc).mpr ⟨hf, hip⟩, hstrict a c hc hip hdate, ?_⟩
        have hL : actualOldDownPrefixLength rate K a.val beta = a.val := by
          unfold actualOldDownPrefixLength
          have hall : ∀ r ∈ K.take a.val,
              (decide (r.input.time.val + 1 ≤ beta) : Bool) = true := by
            intro r hr
            obtain ⟨b, hb, hbr⟩ := List.mem_take_iff_getElem.mp hr
            have hbK : b < K.length := (lt_min_iff.mp hb).2
            have hba : b < a.val := (lt_min_iff.mp hb).1
            have htimeA : (K.get a).input.time.val = _ := (hrows a).2.2.2.1
            have htimeB : (K.get ⟨b, hbK⟩).input.time.val = _ := (hrows ⟨b, hbK⟩).2.2.2.1
            change K[b].input.time.val =
              ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h + (e + b) at htimeB
            rw [hbr] at htimeB
            change (K.get a).input.time.val + 1 ≤ beta at hdate
            exact decide_eq_true (by omega)
          rw [(List.takeWhile_eq_self_iff).mpr hall]
          exact List.length_take_of_le (Nat.le_of_lt a.isLt)
        have hr := hreads a.val
        change actualFormedUpPrefixReadoutSum rate rewards C_star C_h source K a.val beta i =
          ((ReferenceFirstReplacementCollectionStoppedPureUpQuota.formedPositiveEntries
            (K.take (actualOldDownPrefixLength rate K a.val beta)) i M).length : ℝ) at hr
        rw [hL] at hr
        rw [hr]
        exact_mod_cast hstrict a c hc hip hdate

end Bandits.Support.ReferenceOriginalCollectionFormedUpCanonicalQuota

end
