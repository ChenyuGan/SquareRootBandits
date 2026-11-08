/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstReplacementCollectionPendingLocalization
public import Bandits.Support.ReferenceFirstReplacementCollectionPredictableStages

/-!
# Actual calendar observations for first replacement collection

Sources: pinned ZIP4 `06_interruptions.tex:425-431,459-487`,
`05_binary_transport.tex:180-240`, and
`appendix_a_local_protocol.tex:141-157`.

These are deterministic observations of the original complete physical run.
The pending mask retains the detecting round. UP service counts the actual
saved decoder entries only after formation of the current reply.
-/

@[expose] public section

noncomputable section

open Bandits.Support ConstructorDimensions
open scoped Classical BigOperators

namespace Bandits.Support.ReferenceFirstReplacementCollectionActualCalendarTasks


variable {p : Parameters} {rate : ReferenceActivePhysicalStep.RateInput p}

abbrev Record := ReferenceFirstReplacementCollectionPendingFoundation.Record (rate := rate)
abbrev Payload := ReferenceFirstReplacementCollectionPendingFoundation.Payload (rate := rate)
abbrev Source := ReferenceFirstReplacementCollectionPendingFoundation.Source (p := p)

/-- Selected positive own DOWN feedback, without a decoding-success test. -/
def downPositive (r : Record (rate := rate)) (i : Fin (p.m - 1)) : ℕ :=
  if ReferenceSelectedAffinePairLaw.selectedChannel p
      (r.input.row.2 r.input.time).1 = some (0, i) ∧
      0 < (ReferenceFollowerDownDecoderReplay.preparedOwnObservation r i).val.val
  then 1 else 0

/-- Number of equations in the actual saved coordinator call to this label. -/
def upPositive (r : Record (rate := rate)) (i : Fin (p.m - 1)) : ℕ :=
  (ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries r i).length

variable (rate)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)

/-- Natural-calendar OLD contribution. `OLD` already includes membership in
exactly `ReferenceFirstReplacementCollectionPendingFoundation.P_repl`, with its strict-past mask. -/
def oldService (n : ℕ) (i : Fin (p.m - 1)) (z : Source (p := p)) : ℕ :=
  if ReferenceFirstReplacementCollectionPredictableStages.OLD rate rewards C_star C_h control0 n i z then
    if hn : n < p.T then
      match ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h ⟨n, hn⟩ z with
      | none => 0
      | some r => downPositive r i
    else 0
  else 0

/-- Natural-calendar current-reply UP contribution, preserving the actual
saved entry time, label, affine sample and receiver input. -/
def formedService (n : ℕ) (i : Fin (p.m - 1)) (z : Source (p := p)) : ℕ :=
  if ReferenceFirstReplacementCollectionPredictableStages.FORMED rate rewards C_star C_h control0 n i z then
    if hn : n < p.T then
      match ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h ⟨n, hn⟩ z with
      | none => 0
      | some r => upPositive r i
    else 0
  else 0

/-- Literal pending-task service on the complete natural calendar. -/
def service (n : ℕ) (i : Fin (p.m - 1)) (z : Source (p := p)) : ℕ :=
  oldService rate rewards C_star C_h control0 n i z +
    formedService rate rewards C_star C_h control0 n i z

/-- Calendar prefix means dates strictly below `H`. -/
def oldCount (H : ℕ) (i : Fin (p.m - 1)) (z : Source (p := p)) : ℕ :=
  ∑ n ∈ Finset.range H, oldService rate rewards C_star C_h control0 n i z

def formedCount (H : ℕ) (i : Fin (p.m - 1)) (z : Source (p := p)) : ℕ :=
  ∑ n ∈ Finset.range H, formedService rate rewards C_star C_h control0 n i z

def taskCount (H : ℕ) (i : Fin (p.m - 1)) (z : Source (p := p)) : ℕ :=
  ∑ n ∈ Finset.range H, service rate rewards C_star C_h control0 n i z

variable {rate rewards C_star C_h control0}

theorem downPositive_le_one (r : Record (rate := rate)) (i : Fin (p.m - 1)) :
    downPositive r i ≤ 1 := by
  unfold downPositive
  split <;> omega

theorem upPositive_le_one (r : Record (rate := rate)) (i : Fin (p.m - 1)) :
    upPositive r i ≤ 1 := by
  unfold upPositive ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries
    AffineBatchDecoder.positiveAt
  split <;> (try split_ifs) <;> simp

theorem oldService_le_one (n : ℕ) (i : Fin (p.m - 1)) (z : Source (p := p)) :
    oldService rate rewards C_star C_h control0 n i z ≤ 1 := by
  unfold oldService
  split
  · split
    · split
      · omega
      · exact downPositive_le_one _ _
    · omega
  · omega

theorem formedService_le_one (n : ℕ) (i : Fin (p.m - 1)) (z : Source (p := p)) :
    formedService rate rewards C_star C_h control0 n i z ≤ 1 := by
  unfold formedService
  split
  · split
    · split
      · omega
      · exact upPositive_le_one _ _
    · omega
  · omega

theorem service_le_one (n : ℕ) (i : Fin (p.m - 1)) (z : Source (p := p)) :
    service rate rewards C_star C_h control0 n i z ≤ 1 := by
  have hd := oldService_le_one (rate := rate) (rewards := rewards)
    (C_star := C_star) (C_h := C_h) (control0 := control0) n i z
  have hu := formedService_le_one (rate := rate) (rewards := rewards)
    (C_star := C_star) (C_h := C_h) (control0 := control0) n i z
  have hdis := ReferenceFirstReplacementCollectionPredictableStages.OLD_FORMED_disjoint rate rewards C_star C_h control0 n i z
  unfold service
  by_cases ho : ReferenceFirstReplacementCollectionPredictableStages.OLD rate rewards C_star C_h control0 n i z
  · have hf : ¬ ReferenceFirstReplacementCollectionPredictableStages.FORMED rate rewards C_star C_h control0 n i z := fun h => hdis ⟨ho, h⟩
    simp only [formedService, ite_eq_right hf, Nat.add_zero]
    exact hd
  · simp only [oldService, ite_eq_right ho, Nat.zero_add]
    exact hu

theorem services_of_not_pending (n : ℕ) (i : Fin (p.m - 1)) (z : Source (p := p))
    (hi : i ∉ ReferenceFirstReplacementCollectionPendingFoundation.P_repl rate rewards C_star C_h control0 n z) :
    oldService rate rewards C_star C_h control0 n i z = 0 ∧
      formedService rate rewards C_star C_h control0 n i z = 0 ∧
      service rate rewards C_star C_h control0 n i z = 0 := by
  have ho := ReferenceFirstReplacementCollectionPredictableStages.not_OLD_of_not_pending rate rewards C_star C_h control0 n i z hi
  have hf := ReferenceFirstReplacementCollectionPredictableStages.not_FORMED_of_not_pending rate rewards C_star C_h control0 n i z hi
  simp only [oldService, formedService, service, ite_eq_right ho, ite_eq_right hf,
    Nat.zero_add, and_self]

theorem services_of_horizon_le (n : ℕ) (i : Fin (p.m - 1)) (z : Source (p := p))
    (hn : p.T ≤ n) :
    oldService rate rewards C_star C_h control0 n i z = 0 ∧
      formedService rate rewards C_star C_h control0 n i z = 0 ∧
      service rate rewards C_star C_h control0 n i z = 0 := by
  apply services_of_not_pending
  rw [ReferenceFirstReplacementCollectionPendingFoundation.P_repl_of_horizon_le rate rewards C_star C_h control0 n hn]
  exact Finset.notMem_empty i

theorem taskCount_eq (H : ℕ) (i : Fin (p.m - 1)) (z : Source (p := p)) :
    taskCount rate rewards C_star C_h control0 H i z =
      oldCount rate rewards C_star C_h control0 H i z +
      formedCount rate rewards C_star C_h control0 H i z := by
  exact Finset.sum_add_distrib

/-- Present-record readout: the SAME pending indicator and literal stage
control which physical positive is counted. No ordinariness is inferred. -/
theorem services_at_record (t : Fin p.T) (i : Fin (p.m - 1)) (z : Source (p := p))
    (r : Record (rate := rate)) (payload : Payload (rate := rate)) (u : ℕ)
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some r)
    (hp : ReferenceFirstReplacementCollectionPendingFoundation.payloadOnset rate rewards C_star C_h t.val z = some (payload, u)) :
    oldService rate rewards C_star C_h control0 t.val i z =
      (if i ∈ ReferenceFirstReplacementCollectionPendingFoundation.P_repl rate rewards C_star C_h control0 t.val z ∧
        ReferenceFirstReplacementCollectionOldDownCallDates.actualOldAt r i (payload.downRecord i) then downPositive r i else 0) ∧
    formedService rate rewards C_star C_h control0 t.val i z =
      if i ∈ ReferenceFirstReplacementCollectionPendingFoundation.P_repl rate rewards C_star C_h control0 t.val z ∧
        ReferenceFirstReplacementCollectionStoppedPureUpQuota.replyFormedAt r i (payload.downRecord i) then upPositive r i else 0 := by
  have hs := ReferenceFirstReplacementCollectionPredictableStages.taskStage_at_record rate rewards C_star C_h control0 t i z r payload u hr hp
  have ho : ReferenceFirstReplacementCollectionPredictableStages.OLD rate rewards C_star C_h control0 t.val i z ↔
      i ∈ ReferenceFirstReplacementCollectionPendingFoundation.P_repl rate rewards C_star C_h control0 t.val z ∧
        ReferenceFirstReplacementCollectionOldDownCallDates.actualOldAt r i (payload.downRecord i) := by
    unfold ReferenceFirstReplacementCollectionPredictableStages.OLD
    rw [hs]
    by_cases hi : i ∈ ReferenceFirstReplacementCollectionPendingFoundation.P_repl rate rewards C_star C_h control0 t.val z
    · simp [hi, ReferenceFirstReplacementCollectionPredictableStages.choiceStage_old_iff]
    · simp [hi]
  have hf : ReferenceFirstReplacementCollectionPredictableStages.FORMED rate rewards C_star C_h control0 t.val i z ↔
      i ∈ ReferenceFirstReplacementCollectionPendingFoundation.P_repl rate rewards C_star C_h control0 t.val z ∧
        ReferenceFirstReplacementCollectionStoppedPureUpQuota.replyFormedAt r i (payload.downRecord i) := by
    unfold ReferenceFirstReplacementCollectionPredictableStages.FORMED
    rw [hs]
    by_cases hi : i ∈ ReferenceFirstReplacementCollectionPendingFoundation.P_repl rate rewards C_star C_h control0 t.val z
    · simp [hi, ReferenceFirstReplacementCollectionPredictableStages.choiceStage_formed_iff,
        ReferenceFirstReplacementCollectionStoppedPureUpQuota.replyFormedAt]
    · simp [hi]
  simp only [oldService, formedService, dite_eq_left t.isLt, hr, ho, hf, and_self]

private theorem calendar_sum (f : ℕ → ℕ) (b len H : ℕ)
    (hzero : ∀ n, n < b ∨ b + len ≤ n → f n = 0) :
    ∑ n ∈ Finset.range H, f n =
      ∑ a ∈ Finset.range (min len (H - b)), f (b + a) := by
  let A := (Finset.range H).filter fun n => b ≤ n ∧ n < b + len
  have he : ∑ n ∈ Finset.range H, f n = ∑ n ∈ A, f n := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro n hn hnot
    have hout : n < b ∨ b + len ≤ n := by
      simp only [Finset.mem_filter, hn, true_and, not_and_or, not_le, not_lt] at hnot
      exact hnot
    exact hzero n hout
  rw [he]
  apply Finset.sum_bij (fun n _ => n - b)
  · intro n hn
    simp only [A, Finset.mem_filter, Finset.mem_range] at hn
    simp only [Finset.mem_range]
    omega
  · intro n hn m hm hnm
    simp only [A, Finset.mem_filter, Finset.mem_range] at hn hm
    omega
  · intro a ha
    simp only [Finset.mem_range] at ha
    refine ⟨b + a, ?_, by omega⟩
    simp only [A, Finset.mem_filter, Finset.mem_range]
    omega
  · intro n hn
    simp only [A, Finset.mem_filter, Finset.mem_range] at hn
    congr 1
    omega

private theorem sum_range_to_fin (f : ℕ → ℕ) (len j : ℕ) (hj : j ≤ len) :
    ∑ a ∈ Finset.range j, f a =
      ∑ a : Fin len, if a.val < j then f a.val else 0 := by
  have he : (Finset.range len).filter (fun a => a < j) = Finset.range j := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [Fin.sum_univ_eq_sum_range (fun a : ℕ => if a < j then f a else 0),
    ← Finset.sum_filter, he]

private theorem list_prefix_sum {A : Type*} (K : List A) (g : A → ℕ) (j : ℕ) :
    ((K.take j).map g).sum =
      ∑ a : Fin K.length, if a.val < j then g (K.get a) else 0 := by
  induction K generalizing j with
  | nil => simp
  | cons r rs ih =>
    cases j with
    | zero => simp
    | succ j =>
      rw [List.take_succ_cons, List.map_cons, List.sum_cons, ih j]
      simp [Fin.sum_univ_succ]

private theorem common_old_sum (s : ℕ) (K : List (Record (rate := rate)))
    (z : Source (p := p)) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1))
    (M : OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta)) (j : ℕ) :
    ReferenceFirstReplacementCollectionStoppedCompositeQuota.commonOldCount
      s K z rewards C_star C_h control0 i M j =
    ∑ a : Fin K.length,
      if a.val < ReferenceFirstReplacementCollectionStoppedCompositeQuota.commonPrefixLength
          s K z rewards C_star C_h control0 i j then
        if ReferenceFirstReplacementCollectionOldDownCallDates.actualOldAt (K.get a) i M
        then downPositive (K.get a) i else 0
      else 0 := by
  let q := ReferenceFirstReplacementCollectionStoppedCompositeQuota.commonPrefixLength
    s K z rewards C_star C_h control0 i j
  have hn : (ReferenceFirstReplacementCollectionOldDownCallDates.countedOldDownServiceIndices
      K q i M).Nodup := (List.nodup_finRange K.length).filter _
  have he : ReferenceFirstReplacementCollectionStoppedCompositeQuota.commonOldCount
      s K z rewards C_star C_h control0 i M j =
      (ReferenceFirstReplacementCollectionOldDownCountOrAmbiguity.oldDownServiceFinset K q i M).card := by
    unfold ReferenceFirstReplacementCollectionStoppedCompositeQuota.commonOldCount
      ReferenceFirstReplacementCollectionOldDownCountOrAmbiguity.oldDownCount
    rw [← List.toFinset_card_of_nodup hn]
    congr 1
    simp [ReferenceFirstReplacementCollectionOldDownCallDates.countedOldDownServiceIndices,
      ReferenceFirstReplacementCollectionOldDownCallDates.countedOldDownServiceAt,
      ReferenceFirstReplacementCollectionOldDownCountOrAmbiguity.oldDownServiceFinset,
      ReferenceFirstReplacementCollectionOldDownCountOrAmbiguity.oldDownServiceAt,
      List.toFinset_filter, List.toFinset_finRange, q]
  rw [he, ReferenceFirstReplacementCollectionOldDownCountOrAmbiguity.oldDownServiceFinset,
    Finset.card_filter]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : a.val < q
  · have hno := ReferenceFirstReplacementCollectionStoppedCompositeQuota.no_commonStop_before_counted
      s K z rewards C_star C_h control0 i j a ha
    have hpast : ∀ r ∈ K.take a.val,
        ¬ ReferenceFirstReplacementCollectionStoppedPureUpQuota.physicalFailureAt r := by
      intro r hr hfail
      exact hno r hr (Or.inr (Or.inl hfail))
    have hpast_eq : (∀ r ∈ K.take a.val,
        ¬ ReferenceFirstReplacementCollectionStoppedPureUpQuota.physicalFailureAt r) ↔ True :=
      iff_true_intro hpast
    by_cases hold : ReferenceFirstReplacementCollectionOldDownCallDates.actualOldAt (K.get a) i M <;>
      by_cases hpos : ReferenceSelectedAffinePairLaw.selectedChannel p
        ((K.get a).input.row.2 (K.get a).input.time).1 = some (0, i) ∧
        0 < (ReferenceFollowerDownDecoderReplay.preparedOwnObservation (K.get a) i).val.val <;>
      simp only [ReferenceFirstReplacementCollectionOldDownCountOrAmbiguity.oldDownServiceAt,
        ha, true_and, hpast_eq, and_true, hold, hpos, downPositive, q, ↓reduceIte,
        false_and, and_self]

  · simp [ReferenceFirstReplacementCollectionOldDownCountOrAmbiguity.oldDownServiceAt,
      ha, q]

private theorem common_up_sum (s : ℕ) (K : List (Record (rate := rate)))
    (z : Source (p := p)) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1))
    (M : OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta)) (j : ℕ) :
    ReferenceFirstReplacementCollectionStoppedCompositeQuota.commonUpCount
      s K z rewards C_star C_h control0 i M j =
    ∑ a : Fin K.length,
      if a.val < ReferenceFirstReplacementCollectionStoppedCompositeQuota.commonPrefixLength
          s K z rewards C_star C_h control0 i j then
        if ReferenceFirstReplacementCollectionStoppedPureUpQuota.replyFormedAt (K.get a) i M
        then upPositive (K.get a) i else 0
      else 0 := by
  unfold ReferenceFirstReplacementCollectionStoppedCompositeQuota.commonUpCount
    ReferenceFirstReplacementCollectionStoppedPureUpQuota.formedPositiveEntries
  rw [List.length_flatMap]
  have he : ∀ L : List (Record (rate := rate)),
      (L.map (fun r => (if ReferenceFirstReplacementCollectionStoppedPureUpQuota.replyFormedAt r i M
        then ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries r i else []).length)) =
      L.map (fun r => if ReferenceFirstReplacementCollectionStoppedPureUpQuota.replyFormedAt r i M
        then upPositive r i else 0) := by
    intro L
    apply List.map_congr_left
    intro r _
    split <;> rfl
  rw [he]
  exact list_prefix_sum K _ _

private theorem calendar_counts_le
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (z : Source (p := p)) (payload : Payload (rate := rate)) (u s : ℕ)
    (K : List (Record (rate := rate)))
    (hloc : ∀ n, (ReferenceFirstReplacementCollectionPendingFoundation.P_repl rate rewards C_star C_h control0 n z).Nonempty →
      ∃ a : Fin K.length, n = u - 1 + a.val)
    (hcoord : ∀ a : Fin K.length,
      (K.get a).input.time.val = u - 1 + a.val ∧
      ReferenceFirstReplacementCollectionPendingFoundation.payloadOnset rate rewards C_star C_h (u - 1 + a.val) z = some (payload, u) ∧
      ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
        (K.get a).input.time z = some (K.get a) ∧
      ∀ i, i ∈ ReferenceFirstReplacementCollectionPendingFoundation.P_repl rate rewards C_star C_h control0 (u - 1 + a.val) z →
        a.val ≤ ReferenceFirstReplacementCollectionStoppedCompositeQuota.commonStopIndex s K z rewards C_star C_h control0 i) :
    ∀ (i : Fin (p.m - 1)) (H : ℕ),
      let j := min K.length (H - (u - 1))
      oldCount rate rewards C_star C_h control0 H i z ≤
        ReferenceFirstReplacementCollectionStoppedCompositeQuota.commonOldCount s K z rewards C_star C_h control0 i (payload.downRecord i) j ∧
      formedCount rate rewards C_star C_h control0 H i z ≤
        ReferenceFirstReplacementCollectionStoppedCompositeQuota.commonUpCount s K z rewards C_star C_h control0 i (payload.downRecord i) j ∧
      taskCount rate rewards C_star C_h control0 H i z ≤
        ReferenceFirstReplacementCollectionStoppedCompositeQuota.compositeCount s K z rewards C_star C_h control0 i (payload.downRecord i) j := by
  intro i H j
  have hzero : ∀ n, n < u - 1 ∨ u - 1 + K.length ≤ n →
      oldService rate rewards C_star C_h control0 n i z = 0 ∧
      formedService rate rewards C_star C_h control0 n i z = 0 := by
    intro n hout
    have hi : i ∉ ReferenceFirstReplacementCollectionPendingFoundation.P_repl rate rewards C_star C_h control0 n z := by
      intro hi
      obtain ⟨a, ha⟩ := hloc n ⟨i, hi⟩
      have := a.isLt
      omega
    have hs := services_of_not_pending n i z hi
    exact ⟨hs.1, hs.2.1⟩
  have ho : oldCount rate rewards C_star C_h control0 H i z =
      ∑ a : Fin K.length, if a.val < j then
        oldService rate rewards C_star C_h control0 (u - 1 + a.val) i z else 0 := by
    unfold oldCount
    rw [calendar_sum _ (u - 1) K.length H (fun n hn => (hzero n hn).1)]
    exact sum_range_to_fin _ K.length j (Nat.min_le_left _ _)
  have hu : formedCount rate rewards C_star C_h control0 H i z =
      ∑ a : Fin K.length, if a.val < j then
        formedService rate rewards C_star C_h control0 (u - 1 + a.val) i z else 0 := by
    unfold formedCount
    rw [calendar_sum _ (u - 1) K.length H (fun n hn => (hzero n hn).2)]
    exact sum_range_to_fin _ K.length j (Nat.min_le_left _ _)
  have hpoint : ∀ a : Fin K.length,
      (if a.val < j then oldService rate rewards C_star C_h control0
        (u - 1 + a.val) i z else 0) ≤
      (if a.val < ReferenceFirstReplacementCollectionStoppedCompositeQuota.commonPrefixLength s K z rewards C_star C_h control0 i j then
        if ReferenceFirstReplacementCollectionOldDownCallDates.actualOldAt (K.get a) i (payload.downRecord i)
        then downPositive (K.get a) i else 0 else 0) ∧
      (if a.val < j then formedService rate rewards C_star C_h control0
        (u - 1 + a.val) i z else 0) ≤
      (if a.val < ReferenceFirstReplacementCollectionStoppedCompositeQuota.commonPrefixLength s K z rewards C_star C_h control0 i j then
        if ReferenceFirstReplacementCollectionStoppedPureUpQuota.replyFormedAt (K.get a) i (payload.downRecord i)
        then upPositive (K.get a) i else 0 else 0) := by
    intro a
    obtain ⟨htime, hp, hr, hstop⟩ := hcoord a
    by_cases ha : a.val < j
    · by_cases hi : i ∈ ReferenceFirstReplacementCollectionPendingFoundation.P_repl rate rewards C_star C_h control0 (u - 1 + a.val) z
      · have hclip : a.val < ReferenceFirstReplacementCollectionStoppedCompositeQuota.commonPrefixLength s K z rewards C_star C_h control0 i j :=
          (ReferenceFirstReplacementCollectionStoppedCompositeQuota.commonPrefixLength_coordinate_iff s K z rewards C_star C_h control0 i j a.val).2
            ⟨ha, hstop i hi⟩
        have hread := services_at_record (control0 := control0) (K.get a).input.time i z (K.get a) payload u hr
          (by rw [htime]; exact hp)
        rw [htime] at hread
        simp only [ha, hclip, ↓reduceIte, hread.1, hread.2, hi, true_and, le_refl, and_self]
      · have hs := services_of_not_pending (u - 1 + a.val) i z hi
        simp only [ha, ↓reduceIte, hs.1, hs.2.1, Nat.zero_le, and_self]
    · simp only [ha, ↓reduceIte, Nat.zero_le, and_self]
  have hold : oldCount rate rewards C_star C_h control0 H i z ≤
      ReferenceFirstReplacementCollectionStoppedCompositeQuota.commonOldCount s K z rewards C_star C_h control0 i (payload.downRecord i) j := by
    rw [ho, common_old_sum]
    exact Finset.sum_le_sum fun a _ => (hpoint a).1
  have hformed : formedCount rate rewards C_star C_h control0 H i z ≤
      ReferenceFirstReplacementCollectionStoppedCompositeQuota.commonUpCount s K z rewards C_star C_h control0 i (payload.downRecord i) j := by
    rw [hu, common_up_sum]
    exact Finset.sum_le_sum fun a _ => (hpoint a).2
  refine ⟨hold, hformed, ?_⟩
  rw [taskCount_eq]
  exact Nat.add_le_add hold hformed

private theorem dispatch_live_origin (x : ReferenceActivePhysicalStep.RoundInput p rate) :
    match ReferenceActivePhysicalStep.dispatch x with
    | .live r q base _ => x.state.coordinator = .live r q base
    | _ => True := by
  unfold ReferenceActivePhysicalStep.dispatch
  cases x.state.coordinator with
  | first => trivial
  | live r q base =>
      simp only [CoordinatorRoundDispatch.dispatch]
      cases CoordinatorRoundDispatch.dispatchLive
        (ReferenceActivePhysicalStep.liveInput x r q base) <;> rfl
  | collection payload ledger saved =>
      by_cases hc : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
      · simp only [CoordinatorRoundDispatch.dispatch, dite_eq_left hc]
        cases CoordinatorRoundDispatch.dispatchCollection
          (ReferenceActivePhysicalStep.collectionInput x payload ledger
            (ReferenceActivePhysicalStep.collectionClock payload ledger saved ⟨ledger.cutoff - 1, by omega⟩)
            ⟨ledger.cutoff - 1, by omega⟩) <;> trivial
      · simp only [CoordinatorRoundDispatch.dispatch, dite_eq_right hc]
  | dagger => trivial

private theorem linked_dagger_forward
    (K : List (Record (rate := rate))) (Z : ℕ → ReferenceActivePhysicalStep.State p rate)
    (hlinks : ∀ a : Fin K.length,
      (K.get a).input.state = Z a.val ∧ (K.get a).output.next = Z (a.val + 1))
    (a b : ℕ) (hab : a ≤ b) (hb : b ≤ K.length)
    (hd : (Z a).coordinator = .dagger) : (Z b).coordinator = .dagger := by
  induction b with
  | zero =>
    have ha : a = 0 := by omega
    simpa only [ha] using hd
  | succ b ih =>
    by_cases he : a = b + 1
    · simpa only [he] using hd
    · have hprev := ih (by omega) (by omega)
      let idx : Fin K.length := ⟨b, by omega⟩
      have hl := hlinks idx
      have hin : (K.get idx).input.state.coordinator = .dagger := by rw [hl.1]; exact hprev
      have hout := (ReferenceActivePhysicalStep.step_coordinator_dagger (K.get idx).input hin).1
      rw [← (K.get idx).output_eq, hl.2] at hout
      exact hout

private theorem pending_coordinates_nested
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : Source (p := p))
    (payload : Payload (rate := rate)) (cut : Record (rate := rate))
    (W : List (Record (rate := rate)))
    (hactual : ∀ a : Fin (cut :: W).length,
      ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
        ((cut :: W).get a).input.time z = some ((cut :: W).get a))
    (hcut : ReferenceFirstCollectionPendingObservation.Q rate rewards C_star C_h
      payload.sigma.val cut.input.time z = Finset.univ)
    (hlinks : ∀ a : Fin (cut :: W).length,
      ((cut :: W).get a).input.state = ReferenceCollectionSegmentExtraction.endpointState
        cut.input.state ((cut :: W).take a.val) ∧
      ((cut :: W).get a).output.next = ReferenceCollectionSegmentExtraction.endpointState
        cut.input.state ((cut :: W).take (a.val + 1)))
    (hE : ∀ j : ℕ, j ≤ W.length →
      let E := ReferenceCollectionSegmentExtraction.endpointState cut.output.next (W.take j)
      E.coordinator = .dagger ∨ ∃ ledger saved,
        E.coordinator = .collection payload ledger saved ∧
        ledger.sigma = payload.sigma.val + 1 ∧ ledger.cutoff = cut.input.time.val + 1 ∧
        ledger.pending = Finset.univ \
          (ReferenceCollectionPhaseHistory.acceptedLabels (cut :: W.take j)).toFinset) :
    ∀ a b : Fin (cut :: W).length, a.val ≤ b.val →
      ReferenceFirstCollectionPendingObservation.Q rate rewards C_star C_h payload.sigma.val
        ((cut :: W).get b).input.time z ⊆
      ReferenceFirstCollectionPendingObservation.Q rate rewards C_star C_h payload.sigma.val
        ((cut :: W).get a).input.time z := by
  let K := cut :: W
  let Z := fun n => ReferenceCollectionSegmentExtraction.endpointState cut.input.state (K.take n)
  have hstate : ∀ a : Fin K.length, 0 < a.val →
      (K.get a).input.state =
        ReferenceCollectionSegmentExtraction.endpointState cut.output.next (W.take (a.val - 1)) := by
    intro a ha
    rw [(hlinks a).1]
    have he : a.val = (a.val - 1) + 1 := by omega
    conv_lhs => rw [he]
    simp only [List.take_succ_cons, ReferenceCollectionSegmentExtraction.endpointState, List.foldl_cons]
  intro a b hab i hi
  by_cases ha0 : a.val = 0
  · have he : K.get a = cut := by simp [K, List.get_eq_getElem, ha0]
    rw [he, hcut]
    exact Finset.mem_univ i
  · have ha : 0 < a.val := by omega
    have hb : 0 < b.val := by omega
    have hsa := hstate a ha
    have hsb := hstate b hb
    have hpa := hE (a.val - 1) (by have := a.isLt; simp only [List.length_cons] at this; omega)
    have hpb := hE (b.val - 1) (by have := b.isLt; simp only [List.length_cons] at this; omega)
    rcases hpb with hdagger | ⟨lb, sb, hcb, _hsb, _hcutb, hpendb⟩
    · have hdb : ((cut :: W).get b).input.state.coordinator = .dagger := by rw [hsb]; exact hdagger
      simp only [ReferenceFirstCollectionPendingObservation.Q, hactual b, hdb,
        Finset.notMem_empty] at hi
    · have hinputb : ((cut :: W).get b).input.state.coordinator = .collection payload lb sb := by
        rw [hsb]; exact hcb
      have hib : i ∈ lb.pending := by
        simpa only [ReferenceFirstCollectionPendingObservation.Q, hactual b, hinputb,
          ↓reduceIte] using hi
      rcases hpa with hdagger | ⟨la, sa, hca, _hsa, _hcuta, hpenda⟩
      · have hda : (Z a.val).coordinator = .dagger :=
          (congrArg (fun st : ReferenceActivePhysicalStep.State p rate => st.coordinator)
            (hlinks a).1).symm.trans
              ((congrArg (fun st : ReferenceActivePhysicalStep.State p rate => st.coordinator)
                hsa).trans hdagger)
        have hdb := linked_dagger_forward K Z hlinks a.val b.val hab (Nat.le_of_lt b.isLt) hda
        have hdbInput := (congrArg
          (fun st : ReferenceActivePhysicalStep.State p rate => st.coordinator) (hlinks b).1).trans hdb
        rw [hinputb] at hdbInput
        contradiction
      · have hinputa : ((cut :: W).get a).input.state.coordinator = .collection payload la sa := by
          rw [hsa]; exact hca
        have heA : cut :: W.take (a.val - 1) = K.take a.val := by
          have he : a.val = (a.val - 1) + 1 := by omega
          conv_rhs => rw [he]
          rfl
        have heB : cut :: W.take (b.val - 1) = K.take b.val := by
          have he : b.val = (b.val - 1) + 1 := by omega
          conv_rhs => rw [he]
          rfl
        rw [heA] at hpenda
        rw [heB] at hpendb
        have hsub : (ReferenceCollectionPhaseHistory.acceptedLabels (K.take a.val)).toFinset ⊆
            (ReferenceCollectionPhaseHistory.acceptedLabels (K.take b.val)).toFinset := by
          intro x hx
          apply List.mem_toFinset.mpr
          apply ((List.take_sublist_take_left hab).filterMap
            (fun r : Record (rate := rate) => ReferenceCollectionPhaseHistory.acceptedLabel r.input)).subset
          exact List.mem_toFinset.mp hx
        have hia : i ∈ la.pending := by
          rw [hpenda]
          rw [hpendb] at hib
          exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ i,
            fun hin => (Finset.mem_sdiff.mp hib).2 (hsub hin)⟩
        simpa only [ReferenceFirstCollectionPendingObservation.Q, hactual a, hinputa,
          ↓reduceIte] using hia

private theorem empty_calendar
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (z : Source (p := p))
    (h : ∀ n, ¬ (ReferenceFirstReplacementCollectionPendingFoundation.P_repl
      rate rewards C_star C_h control0 n z).Nonempty) :
    ∀ n, ReferenceFirstReplacementCollectionPendingFoundation.P_repl
      rate rewards C_star C_h control0 n z = ∅ := by
  intro n
  exact Finset.not_nonempty_iff_eq_empty.mp (h n)

/-- Deterministic all-calendar constructor. Every absent or failed branch has
empty support. In the actual branch the literal observations inject, date for
date, into the SAME inclusively stopped composite count. The finite count may
also include nonpending records, so the conclusion is faithful domination. -/
theorem complete_first_replacement_actual_calendar_tasks
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p) :
    ∀ z : Source (p := p),
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
    let v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
    let tail := ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v
    let c := v + 1 + tail.length
    match R[v]? with
    | none => ∀ n, ReferenceFirstReplacementCollectionPendingFoundation.P_repl rate rewards C_star C_h control0 n z = ∅
    | some birth =>
      match birth.output.preparation.coordinator with
      | .collection _ _ _ _ (.laterChosen _ _ _ _ _ _ _ _ _ installed _) =>
        let payload := installed.registers.payload
        match R[c]? with
        | none => ∀ n, ReferenceFirstReplacementCollectionPendingFoundation.P_repl rate rewards C_star C_h control0 n z = ∅
        | some cut =>
          match cut.output.preparation.coordinator with
          | .live _ _ _ (.cutoffChosen _ _ _ _ _ _ _ _ _ _) =>
            let u := cut.input.time.val + 1
            let K := cut :: (R.drop (c + 1)).takeWhile
              (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
            (∀ n, (ReferenceFirstReplacementCollectionPendingFoundation.P_repl rate rewards C_star C_h control0 n z).Nonempty →
              ∃ a : Fin K.length, n = u - 1 + a.val ∧
                (K.get a).input.time.val = n ∧
                ReferenceFirstReplacementCollectionPendingFoundation.payloadOnset rate rewards C_star C_h n z = some (payload, u)) ∧
            (∀ n, n < u - 1 ∨ u - 1 + K.length ≤ n →
              ReferenceFirstReplacementCollectionPendingFoundation.P_repl rate rewards C_star C_h control0 n z = ∅) ∧
            (∀ a : Fin K.length,
              let n := u - 1 + a.val
              (K.get a).input.time.val = n ∧
              ReferenceFirstReplacementCollectionPendingFoundation.payloadOnset rate rewards C_star C_h n z = some (payload, u) ∧
              ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
                (K.get a).input.time z = some (K.get a) ∧
              ∀ i, (i ∈ ReferenceFirstReplacementCollectionPendingFoundation.P_repl rate rewards C_star C_h control0 n z ↔
                i ∈ ReferenceFirstCollectionPendingObservation.Q rate rewards C_star C_h
                  payload.sigma.val (K.get a).input.time z ∧
                a.val ≤ ReferenceFirstReplacementCollectionStoppedCompositeQuota.commonStopIndex s K z rewards C_star C_h control0 i)) ∧
            (∀ n m : ℕ, u - 1 ≤ n → n ≤ m →
              ReferenceFirstReplacementCollectionPendingFoundation.P_repl rate rewards C_star C_h control0 m z ⊆
              ReferenceFirstReplacementCollectionPendingFoundation.P_repl rate rewards C_star C_h control0 n z) ∧
            ∀ (i : Fin (p.m - 1)) (H : ℕ),
              let j := min K.length (H - (u - 1))
              oldCount rate rewards C_star C_h control0 H i z ≤
                ReferenceFirstReplacementCollectionStoppedCompositeQuota.commonOldCount s K z rewards C_star C_h control0 i (payload.downRecord i) j ∧
              formedCount rate rewards C_star C_h control0 H i z ≤
                ReferenceFirstReplacementCollectionStoppedCompositeQuota.commonUpCount s K z rewards C_star C_h control0 i (payload.downRecord i) j ∧
              taskCount rate rewards C_star C_h control0 H i z ≤
                ReferenceFirstReplacementCollectionStoppedCompositeQuota.compositeCount s K z rewards C_star C_h control0 i (payload.downRecord i) j ∧
              oldCount rate rewards C_star C_h control0 H i z ≤ 2 * AffineBatchDecoder.quota p ∧
              formedCount rate rewards C_star C_h control0 H i z ≤ 2 * AffineBatchDecoder.quota p ∧
              taskCount rate rewards C_star C_h control0 H i z ≤ 4 * AffineBatchDecoder.quota p
          | _ => ∀ n, ReferenceFirstReplacementCollectionPendingFoundation.P_repl rate rewards C_star C_h control0 n z = ∅
      | _ => ∀ n, ReferenceFirstReplacementCollectionPendingFoundation.P_repl rate rewards C_star C_h control0 n z = ∅ := by
  intro z
  have hL := fun n => ReferenceFirstReplacementCollectionPendingLocalization.complete_first_replacement_pending_localization
    rate rewards C_star C_h control0 z n
  have hN := ReferenceFirstReplacementCollectionPendingFoundation.complete_first_replacement_pending_coordinates rate rewards C_star C_h control0 z
  have hQ := ReferenceFirstReplacementCollectionStoppedCompositeQuota.complete_first_replacement_collection_stopped_composite_quota
    rate z rewards C_star C_h control0
  have hR := ReferenceFirstReplacementCollectionUpReceiverProvenance.complete_first_replacement_collection_up_receiver_provenance
    rate z rewards C_star C_h
  have hZ := ReferenceFirstReplacementCollectionPureUpAcceptanceRoot.complete_first_replacement_collection_pure_up_acceptance
    rate z rewards C_star C_h
  have hB := ReferenceFirstReplacementCutoffPreparedBoundary.complete_first_replacement_cutoff_follower_boundary
    rate z rewards C_star C_h
  dsimp only at hR hZ hB
  dsimp only at hL hN hQ ⊢
  set R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  set s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  set w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
  set v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
  set tail := ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v
  set c := v + 1 + tail.length
  cases hb : R[v]? with
  | none =>
    apply empty_calendar
    intro n hn
    simpa only [hb] using hL n hn
  | some birth =>
    rw [hb] at hN hQ hR hZ hB
    dsimp only at hN hQ hR hZ hB ⊢
    cases hbirth : birth.output.preparation.coordinator <;>
      try (apply empty_calendar; intro n hn; simpa only [hb, hbirth] using hL n hn)
    rename_i old ledger clock cutoff outcome
    rw [hbirth] at hN hQ hR hZ hB
    cases outcome <;>
      try (apply empty_calendar; intro n hn; simpa only [hb, hbirth] using hL n hn)
    rename_i core consistent started hstart instruction hinstruction output hconsistent
      clockData installed selectedBirth
    dsimp only [ReferenceActivePhysicalStep.collectionInput] at hN hQ hR hZ hB ⊢
    obtain ⟨_, _, hR⟩ := hR
    obtain ⟨_, _, hZ⟩ := hZ
    cases hc : R[c]? with
    | none =>
      apply empty_calendar
      intro n hn
      simpa only [hb, hbirth, hc] using hL n hn
    | some cut =>
      rw [hc] at hN hQ hR hZ hB
      dsimp only at hN hQ hR hZ hB ⊢
      obtain ⟨_, hB⟩ := hB
      cases hcut : cut.output.preparation.coordinator <;>
        try (apply empty_calendar; intro n hn; simpa only [hb, hbirth, hc, hcut] using hL n hn)
      rename_i registers owned base outcome
      rw [hcut] at hN hQ hR hZ hB
      cases outcome <;>
        try (apply empty_calendar; intro n hn; simpa only [hb, hbirth, hc, hcut] using hL n hn)
      rename_i dispatched hs ledger hi hledger hdata hclock hpending hnone selectedCut
      dsimp only at hN hQ hR hZ hB ⊢
      let payload := installed.registers.payload
      let u := cut.input.time.val + 1
      let K := cut :: (R.drop (c + 1)).takeWhile
        (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
      obtain ⟨hcuttime, hcalendar, hinjective, hquota⟩ := hQ
      have hloc : ∀ n, (ReferenceFirstReplacementCollectionPendingFoundation.P_repl rate rewards C_star C_h control0 n z).Nonempty →
          ∃ a : Fin K.length, n = u - 1 + a.val ∧
            (K.get a).input.time.val = n ∧
            ReferenceFirstReplacementCollectionPendingFoundation.payloadOnset rate rewards C_star C_h n z = some (payload, u) := by
        intro n hn
        simpa only [hb, hbirth, hc, hcut] using hL n hn
      have hcoord : ∀ a : Fin K.length,
          (K.get a).input.time.val = u - 1 + a.val ∧
          ReferenceFirstReplacementCollectionPendingFoundation.payloadOnset rate rewards C_star C_h (u - 1 + a.val) z = some (payload, u) ∧
          ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
            (K.get a).input.time z = some (K.get a) ∧
          ∀ i, (i ∈ ReferenceFirstReplacementCollectionPendingFoundation.P_repl rate rewards C_star C_h control0 (u - 1 + a.val) z ↔
            i ∈ ReferenceFirstCollectionPendingObservation.Q rate rewards C_star C_h
              payload.sigma.val (K.get a).input.time z ∧
            a.val ≤ ReferenceFirstReplacementCollectionStoppedCompositeQuota.commonStopIndex s K z rewards C_star C_h control0 i) := by
        intro a
        have ht := hcalendar a
        obtain ⟨hp, hr, _, hmem⟩ := hN a
        refine ⟨?_, hp, hr, hmem⟩
        change (K.get a).input.time.val + 1 = u + a.val at ht
        dsimp only [u]
        omega
      let W := (R.drop (c + 1)).takeWhile
        (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
      let Z := fun n => ReferenceCollectionSegmentExtraction.endpointState cut.input.state (K.take n)
      obtain ⟨_hcalZ, hlinksZ, _hfollowersZ, _hboundaryZ⟩ := hZ
      have hlinks : ∀ a : Fin K.length,
          (K.get a).input.state = Z a.val ∧ (K.get a).output.next = Z (a.val + 1) := hlinksZ.2.2
      have hprep : (ReferenceActivePhysicalStep.prepare cut.input).coordinator =
          .live registers owned base
            (.cutoffChosen dispatched hs ledger hi hledger hdata hclock hpending hnone selectedCut) := by
        have he := hcut
        rw [cut.output_eq] at he
        exact he
      have hin := dispatch_live_origin cut.input
      rw [← (ReferenceActivePhysicalStep.prepare cut.input).coordinator_eq] at hin
      rw [hprep] at hin
      have hcutflag : ReferenceCollectionPhaseHistory.cutoffChosen cut.input = true := by
        simp only [ReferenceCollectionPhaseHistory.cutoffChosen, hprep]
      have hactual0 := (hcoord ⟨0, by simp [K]⟩).2.2.1
      have hcutQ : ReferenceFirstCollectionPendingObservation.Q rate rewards C_star C_h
          payload.sigma.val cut.input.time z = Finset.univ := by
        change ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
          cut.input.time z = some cut at hactual0
        have hpay : registers.payload = payload := hB.1
        simp only [ReferenceFirstCollectionPendingObservation.Q, hactual0, hin, hpay,
          hcutflag, and_self, ↓reduceIte]
      have hnested := pending_coordinates_nested rate rewards C_star C_h z payload cut W
        (fun a => (hcoord a).2.2.1) hcutQ hlinks hR.1
      refine ⟨hloc, ?_, hcoord, ?_, ?_⟩
      · intro n hout
        change n < u - 1 ∨ u - 1 + K.length ≤ n at hout
        apply Finset.not_nonempty_iff_eq_empty.mp
        intro hn
        obtain ⟨a, ha, _⟩ := hloc n hn
        have := a.isLt
        omega
      · intro n m hn hnm i him
        obtain ⟨b, hmb, _htb, _hpb⟩ := hloc m ⟨i, him⟩
        let a : Fin K.length := ⟨n - (u - 1), by
          have := b.isLt
          change n - (u - 1) < K.length
          omega⟩
        have hna : n = u - 1 + a.val := by dsimp only [a]; omega
        have hab : a.val ≤ b.val := by dsimp only [a]; omega
        have hbmem := ((hcoord b).2.2.2 i).mp (by rw [← hmb]; exact him)
        have hraw := hnested a b hab hbmem.1
        rw [hna]
        apply ((hcoord a).2.2.2 i).mpr
        exact ⟨hraw, hab.trans hbmem.2⟩
      · intro i H
        let j := min K.length (H - (u - 1))
        have hcounts := calendar_counts_le rate rewards C_star C_h control0 z payload u s K
          (fun n hn => by obtain ⟨a, ha, _⟩ := hloc n hn; exact ⟨a, ha⟩)
          (fun a => ⟨(hcoord a).1, (hcoord a).2.1, (hcoord a).2.2.1,
            fun i hi => ((hcoord a).2.2.2 i).mp hi |>.2⟩) i H
        have hbounds := (hquota i).2.2.2.2.2 j (Nat.min_le_left _ _)
        exact ⟨hcounts.1, hcounts.2.1, hcounts.2.2,
          hcounts.1.trans hbounds.1, hcounts.2.1.trans hbounds.2.1,
          hcounts.2.2.trans hbounds.2.2⟩

end Bandits.Support.ReferenceFirstReplacementCollectionActualCalendarTasks

end
