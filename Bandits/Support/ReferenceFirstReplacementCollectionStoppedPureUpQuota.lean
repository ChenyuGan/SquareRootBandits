/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstReplacementCollectionPureUpSourceAwaited

import Lean.Elab.Tactic.Omega

/-!
# Inclusive local stopping for the first replacement collection's formed UP stage

Sources: `sources/zip4/manuscript/06_interruptions.tex:110-177,246-299,477-481`
and `sources/zip4/manuscript/appendix_a_local_protocol.tex:100-108,151-157`.

The stopping readouts below use the physical records. A completed ambiguity
requires the whole actual batch and an interval of the same awaited offer,
including selected calls with zero feedback. The detecting round is included.
This module concerns a deterministic local count; no probability, source-event
coverage, composite DOWN/UP quota, or waiting law is asserted.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions
open ReferenceFirstReplacementCollectionPureUpWindowCut (physicalPositives)

namespace Bandits.Support.ReferenceFirstReplacementCollectionStoppedPureUpQuota

variable {p : Parameters} {rate : ReferenceActivePhysicalStep.RateInput p}

/-- Acceptance is the actual checked reception, with its parsed-record witness. -/
def acceptanceAt (r : ReferenceCompletePhysicalHistory.RoundRecord p rate)
    (i : Fin (p.m - 1)) : Prop :=
  ReferenceCollectionPhaseHistory.acceptedLabel r.input = some i ∧
    ∃ U, ReferenceCollectionPhaseHistory.AcceptedUp r.input i U

theorem acceptanceAt_iff (r : ReferenceCompletePhysicalHistory.RoundRecord p rate)
    (i : Fin (p.m - 1)) :
    acceptanceAt r i ↔ ReferenceCollectionPhaseHistory.acceptedLabel r.input = some i := by
  exact ⟨And.left, fun h => ⟨h, ReferenceCollectionPhaseHistory.acceptedLabel_witness h⟩⟩

/-- A real retained coordinator or follower failure, without a failure-time identity. -/
def physicalFailureAt (r : ReferenceCompletePhysicalHistory.RoundRecord p rate) : Prop :=
  (∃ reason, r.output.coordinator.failure = some reason) ∨
    ∃ i : Fin (p.m - 1), ∃ reason, (r.output.followers i).failure = some reason

theorem physicalFailureAt_iff (r : ReferenceCompletePhysicalHistory.RoundRecord p rate) :
    physicalFailureAt r ↔ r.output.coordinator.failure.isSome = true ∨
      ∃ i : Fin (p.m - 1), (r.output.followers i).failure.isSome = true := by
  simp only [physicalFailureAt, Option.isSome_iff_exists]

/-- A selected physical call has the same sent offer and passes its own started
ledger's acceptance test. There is deliberately no positivity condition. -/
def awaitedCall (r : ReferenceCompletePhysicalHistory.RoundRecord p rate)
    (i : Fin (p.m - 1)) (U : OrdinaryMessageCodec.UpRecord (ReferencePrelaunchFollower.codecParams p rate.eta)) : Prop :=
  ReferenceActiveAffinePositiveTest.upSent r.input =
      some (ActiveFollowerArmChoice.offeredUpWord rate.eta U) ∧
    ∃ d : ReferenceActivePhysicalStep.UpDiagnostic p rate,
      r.output.coordinator.up = some d ∧ d.input.selectedFollower = i ∧
      CoordinatorUpReception.receptionInputCheck d.input = true ∧
      (CoordinatorUpReception.roundInput d.input).selected = true ∧
      (CoordinatorUpReception.roundInput d.input).receiverEnabled = true ∧
      CoordinatorCollectionLedger.acceptUpCheck d.input.ledger i U = true ∧
      d.expected = some (ActiveFollowerArmChoice.offeredUpWord rate.eta U)

/-- A literal full fixed-awaited ambiguity. The stamped interval covers EVERY
entry of the incoming pending batch plus the current positive equation, and
EVERY selected focal UP call in that interval, including zero observations. -/
def fixedAwaitedAmbiguityAt
    (K : List (ReferenceCompletePhysicalHistory.RoundRecord p rate))
    (i : Fin (p.m - 1)) (U : OrdinaryMessageCodec.UpRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (r : ReferenceCompletePhysicalHistory.RoundRecord p rate) : Prop :=
  0 < U.val.sigma ∧
    ∃ (d : ReferenceActivePhysicalStep.UpDiagnostic p rate) (beta : ℕ),
      r.output.coordinator.up = some d ∧ d.input.selectedFollower = i ∧
      CoordinatorUpReception.receptionInputCheck d.input = true ∧
      AffineBatchDecoder.eligible (CoordinatorUpReception.roundInput d.input) ∧
      d.input.upDecoderBank = r.input.state.upDecoderBank ∧
      d.input.time = r.input.time ∧
      let batch := (r.input.state.upDecoderBank i).pending ++
        [AffineBatchDecoder.entry p
          (ReferenceCoordinatorUpDecoderReplay.constantInputTrace d.input) d.input.time]
      batch.length = AffineBatchDecoder.quota p ∧
      d.raw = AffineBatchDecoder.batchOutput batch ∧ d.raw = none ∧
      (∀ e ∈ batch, AffineBatchDecoder.equation e.sample
        (ActiveFollowerArmChoice.offeredUpWord rate.eta U)) ∧
      (∃ other, other ≠ ActiveFollowerArmChoice.offeredUpWord rate.eta U ∧
        ∀ e ∈ batch, AffineBatchDecoder.equation e.sample other) ∧
      (∀ e ∈ batch, beta ≤ e.time.val ∧ e.time.val ≤ r.input.time.val) ∧
      (∀ x ∈ K, beta ≤ x.input.time.val → x.input.time.val ≤ r.input.time.val →
        ReferenceSelectedAffinePairLaw.selectedChannel p (x.input.row.2 x.input.time).1 =
          some (1, i) → awaitedCall x i U)

/-- Complete literal characterization; no raw-none partial or mixed batch,
empty pending bank, or numerical count alone supplies these readouts. -/
theorem fixedAwaitedAmbiguityAt_iff
    (K : List (ReferenceCompletePhysicalHistory.RoundRecord p rate))
    (i : Fin (p.m - 1)) (U : OrdinaryMessageCodec.UpRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (r : ReferenceCompletePhysicalHistory.RoundRecord p rate) :
    fixedAwaitedAmbiguityAt K i U r ↔
  0 < U.val.sigma ∧
    ∃ (d : ReferenceActivePhysicalStep.UpDiagnostic p rate) (beta : ℕ),
      r.output.coordinator.up = some d ∧ d.input.selectedFollower = i ∧
      CoordinatorUpReception.receptionInputCheck d.input = true ∧
      AffineBatchDecoder.eligible (CoordinatorUpReception.roundInput d.input) ∧
      d.input.upDecoderBank = r.input.state.upDecoderBank ∧
      d.input.time = r.input.time ∧
      let batch := (r.input.state.upDecoderBank i).pending ++
        [AffineBatchDecoder.entry p
          (ReferenceCoordinatorUpDecoderReplay.constantInputTrace d.input) d.input.time]
      batch.length = AffineBatchDecoder.quota p ∧
      d.raw = AffineBatchDecoder.batchOutput batch ∧ d.raw = none ∧
      (∀ e ∈ batch, AffineBatchDecoder.equation e.sample
        (ActiveFollowerArmChoice.offeredUpWord rate.eta U)) ∧
      (∃ other, other ≠ ActiveFollowerArmChoice.offeredUpWord rate.eta U ∧
        ∀ e ∈ batch, AffineBatchDecoder.equation e.sample other) ∧
      (∀ e ∈ batch, beta ≤ e.time.val ∧ e.time.val ≤ r.input.time.val) ∧
      (∀ x ∈ K, beta ≤ x.input.time.val → x.input.time.val ≤ r.input.time.val →
        ReferenceSelectedAffinePairLaw.selectedChannel p (x.input.row.2 x.input.time).1 =
          some (1, i) → awaitedCall x i U) := Iff.rfl

/-- Only actual protocol readouts stop the local charge. -/
def localStop
    (K : List (ReferenceCompletePhysicalHistory.RoundRecord p rate))
    (i : Fin (p.m - 1)) (U : OrdinaryMessageCodec.UpRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (r : ReferenceCompletePhysicalHistory.RoundRecord p rate) : Prop :=
  acceptanceAt r i ∨ physicalFailureAt r ∨ fixedAwaitedAmbiguityAt K i U r

/-- The first actual readout, or the length when there is no such readout. -/
def stopIndex (K : List (ReferenceCompletePhysicalHistory.RoundRecord p rate))
    (i : Fin (p.m - 1)) (U : OrdinaryMessageCodec.UpRecord (ReferencePrelaunchFollower.codecParams p rate.eta)) : ℕ := by
  classical
  exact K.findIdx (fun r => decide (localStop K i U r))

/-- Strict-past exclusion includes the accepting/failing/detecting update. -/
def kept (K : List (ReferenceCompletePhysicalHistory.RoundRecord p rate))
    (i : Fin (p.m - 1)) (U : OrdinaryMessageCodec.UpRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (a : ℕ) : Prop :=
  ∀ r ∈ K.take a, ¬ localStop K i U r

/-- Actual retained UP positives, after formation and through the first stop,
restricted to the requested physical prefix. The protocol itself keeps playing. -/
def stoppedFormedCount
    (K : List (ReferenceCompletePhysicalHistory.RoundRecord p rate))
    (b : ℕ) (i : Fin (p.m - 1))
    (U : OrdinaryMessageCodec.UpRecord (ReferencePrelaunchFollower.codecParams p rate.eta)) (j : ℕ) : ℕ :=
  (ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries
    ((K.take (min j (stopIndex K i U + 1))).drop b) i).length

/-- Literal arm-choice formation of the current reply. No UP observation before
the current DOWN acceptance is a formed-stage service. -/
def replyFormedAt (r : ReferenceCompletePhysicalHistory.RoundRecord p rate)
    (i : Fin (p.m - 1))
    (M : OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta)) : Prop :=
  ∃ state memory, (ReferenceFollowerFixedReply.actualChoice r i).configuration =
    .ordinary state memory ∧ state.status = .unoccupied ∧ state.lastDown = some M

/-- Unmasked physical entries restricted to the actual current-reply stage.
This also expresses the zero formed-stage count when there is no origin. -/
def formedPositiveEntries
    (records : List (ReferenceCompletePhysicalHistory.RoundRecord p rate))
    (i : Fin (p.m - 1))
    (M : OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta)) :
    List (AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p)) := by
  classical
  exact records.flatMap fun r =>
    if replyFormedAt r i M then ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries r i else []

theorem kept_iff_le_stopIndex
    (K : List (ReferenceCompletePhysicalHistory.RoundRecord p rate))
    (i : Fin (p.m - 1)) (U : OrdinaryMessageCodec.UpRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (a : ℕ) (ha : a ≤ K.length) : kept K i U a ↔ a ≤ stopIndex K i U := by
  classical
  constructor
  · intro h
    by_contra hn
    have hs : stopIndex K i U < a := by omega
    have hi : stopIndex K i U < K.length := by omega
    have hstop : localStop K i U K[stopIndex K i U] := by
      exact of_decide_eq_true (List.findIdx_getElem (w := hi))
    apply h K[stopIndex K i U] _ hstop
    exact List.mem_iff_getElem.mpr ⟨stopIndex K i U, by simp; omega, by simp⟩
  · intro h r hr
    obtain ⟨a', ha', he⟩ := List.mem_iff_getElem.mp hr
    have ha'K : a' < K.length := by simp only [List.length_take] at ha'; omega
    have ht : a' < stopIndex K i U := by simp only [List.length_take] at ha'; omega
    change a' < K.findIdx (fun r => decide (localStop K i U r)) at ht
    have hn := List.not_of_lt_findIdx (xs := K)
      (p := fun r => decide (localStop K i U r)) ht
    simp only [List.getElem_take] at he
    rw [he] at hn
    exact of_decide_eq_false hn

theorem kept_iff_no_prior_readouts
    (K : List (ReferenceCompletePhysicalHistory.RoundRecord p rate))
    (i : Fin (p.m - 1))
    (U : OrdinaryMessageCodec.UpRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (a : ℕ) : kept K i U a ↔
      ∀ r ∈ K.take a, ReferenceCollectionPhaseHistory.acceptedLabel r.input ≠ some i ∧
        ¬ physicalFailureAt r ∧ ¬ fixedAwaitedAmbiguityAt K i U r := by
  simp only [kept, localStop, not_or, acceptanceAt_iff]

/-- The certificate names a real first stop, or literal absence of any stop. -/
theorem stopIndex_certificate
    (K : List (ReferenceCompletePhysicalHistory.RoundRecord p rate))
    (i : Fin (p.m - 1)) (U : OrdinaryMessageCodec.UpRecord (ReferencePrelaunchFollower.codecParams p rate.eta)) :
    (∃ a : Fin K.length, stopIndex K i U = a.val ∧
      localStop K i U (K.get a) ∧ kept K i U a.val) ∨
      (stopIndex K i U = K.length ∧ ∀ r ∈ K, ¬ localStop K i U r) := by
  classical
  have hle : stopIndex K i U ≤ K.length := List.findIdx_le_length
  by_cases hlt : stopIndex K i U < K.length
  · refine Or.inl ⟨⟨stopIndex K i U, hlt⟩, rfl, ?_, ?_⟩
    · exact of_decide_eq_true (List.findIdx_getElem (w := hlt))
    · exact (kept_iff_le_stopIndex K i U _ (by omega)).mpr le_rfl
  · have heq : stopIndex K i U = K.length := by omega
    refine Or.inr ⟨heq, ?_⟩
    have hfalse := List.findIdx_eq_length.mp heq
    intro r hr
    exact of_decide_eq_false (hfalse r hr)

/-- The exact coordinate restriction is formation, requested prefix, and no
PRIOR physical stop. In particular the first detecting coordinate is kept. -/
theorem counted_coordinate_iff
    (K : List (ReferenceCompletePhysicalHistory.RoundRecord p rate))
    (b : ℕ) (i : Fin (p.m - 1))
    (U : OrdinaryMessageCodec.UpRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (j : ℕ) (a : Fin K.length) :
    (b ≤ a.val ∧ a.val < min j (stopIndex K i U + 1)) ↔
      (b ≤ a.val ∧ a.val < j ∧ kept K i U a.val) := by
  rw [kept_iff_le_stopIndex K i U a.val (Nat.le_of_lt a.isLt)]
  omega

/-- Once the detecting update has been counted, all later prefixes keep the
same charge even though physical play continues. -/
theorem stoppedFormedCount_eq_after_stop
    (K : List (ReferenceCompletePhysicalHistory.RoundRecord p rate))
    (b : ℕ) (i : Fin (p.m - 1))
    (U : OrdinaryMessageCodec.UpRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (j : ℕ) (hj : stopIndex K i U + 1 ≤ j) :
    stoppedFormedCount K b i U j =
      stoppedFormedCount K b i U (stopIndex K i U + 1) := by
  simp only [stoppedFormedCount, Nat.min_eq_right hj, Nat.min_self]

theorem stoppedFormedCount_eq_zero_before_formation
    (K : List (ReferenceCompletePhysicalHistory.RoundRecord p rate))
    (b : ℕ) (i : Fin (p.m - 1))
    (U : OrdinaryMessageCodec.UpRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (j : ℕ) (hj : j ≤ b) : stoppedFormedCount K b i U j = 0 := by
  have hlen : (K.take (min j (stopIndex K i U + 1))).length ≤ b := by
    simp only [List.length_take]
    omega
  simp only [stoppedFormedCount, List.drop_eq_nil_of_le hlen,
    ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries, List.flatMap_nil, List.length_nil]

/-- A kept update contributes its actual retained increment, including an
accepting or failing update. No receiver replay through that update is used. -/
theorem stoppedFormedCount_succ_of_kept
    (K : List (ReferenceCompletePhysicalHistory.RoundRecord p rate))
    (b : ℕ) (i : Fin (p.m - 1))
    (U : OrdinaryMessageCodec.UpRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (a : Fin K.length) (hb : b ≤ a.val) (hkept : kept K i U a.val) :
    stoppedFormedCount K b i U (a.val + 1) =
      stoppedFormedCount K b i U a.val +
        (ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries (K.get a) i).length := by
  have ha := (kept_iff_le_stopIndex K i U a.val (Nat.le_of_lt a.isLt)).mp hkept
  have htake : (K.take a.val).length = a.val := List.length_take_of_le (Nat.le_of_lt a.isLt)
  simp only [stoppedFormedCount, Nat.min_eq_left (show a.val + 1 ≤ stopIndex K i U + 1 by omega),
    Nat.min_eq_left (show a.val ≤ stopIndex K i U + 1 by omega)]
  rw [List.take_succ_eq_append_getElem a.isLt,
    List.drop_append_of_le_length (by omega)]
  simp only [ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries,
    List.flatMap_append, List.flatMap_singleton, List.length_append, List.get_eq_getElem]

private theorem formedPositiveEntries_eq_nil_of_unformed
    (records : List (ReferenceCompletePhysicalHistory.RoundRecord p rate))
    (i : Fin (p.m - 1))
    (M : OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (h : ∀ r ∈ records, ¬ replyFormedAt r i M) : formedPositiveEntries records i M = [] := by
  classical
  induction records with
  | nil => rfl
  | cons r rest ih =>
      have hr := h r List.mem_cons_self
      have ht : ∀ x ∈ rest, ¬ replyFormedAt x i M := fun x hx => h x (List.mem_cons_of_mem r hx)
      simpa only [formedPositiveEntries, List.flatMap_cons, ite_eq_right hr, List.nil_append]
        using ih ht

theorem recordUpPositiveEntries_length_le_one
    (r : ReferenceCompletePhysicalHistory.RoundRecord p rate) (i : Fin (p.m - 1)) :
    (ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries r i).length ≤ 1 := by
  classical
  cases hd : r.output.coordinator.up with
  | none => simp [ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries, hd]
  | some d =>
      by_cases hs : ReferenceCoordinatorUpDecoderReplay.retainedUpFollower d = i
      · simp only [ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries, hd,
          ite_eq_left hs, AffineBatchDecoder.positiveAt]
        split <;> simp
      · simp [ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries, hd, hs]

/-- The inclusive counter advances by at most one physical positive. This
also applies to the detecting update of the first real failure. -/
theorem stoppedFormedCount_succ_le_one
    (K : List (ReferenceCompletePhysicalHistory.RoundRecord p rate))
    (b : ℕ) (i : Fin (p.m - 1))
    (U : OrdinaryMessageCodec.UpRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (a : Fin K.length) :
    stoppedFormedCount K b i U (a.val + 1) ≤ stoppedFormedCount K b i U a.val + 1 := by
  classical
  by_cases hb : b ≤ a.val
  · by_cases hk : kept K i U a.val
    · rw [stoppedFormedCount_succ_of_kept K b i U a hb hk]
      exact Nat.add_le_add_left (recordUpPositiveEntries_length_le_one (K.get a) i) _
    · have hs : stopIndex K i U + 1 ≤ a.val := by
        have hnot : ¬ a.val ≤ stopIndex K i U :=
          fun h => hk ((kept_iff_le_stopIndex K i U a.val (Nat.le_of_lt a.isLt)).mpr h)
        omega
      rw [stoppedFormedCount_eq_after_stop K b i U (a.val + 1) (by omega),
        stoppedFormedCount_eq_after_stop K b i U a.val hs]
      omega
  · rw [stoppedFormedCount_eq_zero_before_formation K b i U (a.val + 1) (by omega)]
    exact Nat.zero_le _

private theorem fields_of_not_dagger
    (coordinator : ReferenceActivePhysicalStep.CoordinatorConfiguration p rate)
    {P : Prop} (h : match coordinator with | .dagger => True | _ => P)
    (hne : coordinator ≠ .dagger) : P := by
  cases coordinator <;> try exact h
  exact False.elim (hne rfl)

private theorem stopped_count_le
    (K : List (ReferenceCompletePhysicalHistory.RoundRecord p rate))
    (b : ℕ) (i : Fin (p.m - 1)) (U : OrdinaryMessageCodec.UpRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (need : ℕ) (hneed : 0 < need)
    (hchronological : K.Pairwise
      (fun earlier later => earlier.input.time.val < later.input.time.val))
    (hthreshold : ∀ m : ℕ, 0 < m → b + m ≤ stopIndex K i U →
      b + m ≤ K.length →
      (ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries
        ((K.drop b).take m) i).length = need →
      ∃ r ∈ K.take (b + m), localStop K i U r) :
    ∀ j : ℕ, j ≤ K.length → stoppedFormedCount K b i U j ≤ need := by
  intro j hj
  classical
  let l := min j (stopIndex K i U + 1)
  let A := (K.take l).drop b
  have hl : l ≤ K.length := le_trans (Nat.min_le_left _ _) hj
  have hAlen : A.length = l - b := by simp [A, List.length_take, Nat.min_eq_left hl]
  by_contra hn
  have hexcess : need < (ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries A i).length :=
    Nat.lt_of_not_ge hn
  have hchronA : A.Pairwise
      (fun earlier later => earlier.input.time.val < later.input.time.val) := hchronological.take.drop
  have hphysical : physicalPositives A i =
      ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries A i :=
    ReferenceCoordinatorUpIntervalWindow.actual_trace_positives_eq_retained A i hchronA
  rcases ReferenceFirstReplacementCollectionPureUpWindowCut.physical_positive_prefix_cut
      A i need hneed hchronA with hshort | ⟨m, hm, hmA, hcount, _hleast⟩
  · rw [hphysical] at hshort
    omega
  · rw [physicalPositives,
      ReferenceCoordinatorUpIntervalWindow.actual_trace_positives_eq_retained
        (A.take m) i hchronA.take] at hcount
    have hmLt : m < A.length := by
      by_contra h
      have heq : m = A.length := by omega
      rw [heq, List.take_length] at hcount
      omega
    have hb : b < l := by rw [hAlen] at hmLt; omega
    have hbm : b + m ≤ stopIndex K i U := by
      have hlim : l ≤ stopIndex K i U + 1 := Nat.min_le_right _ _
      rw [hAlen] at hmLt
      omega
    have hbmK : b + m ≤ K.length := by rw [hAlen] at hmLt; omega
    have hprefix : A.take m = (K.drop b).take m := by
      dsimp only [A]
      rw [List.drop_take, List.take_take, Nat.min_eq_left (by rw [hAlen] at hmA; omega)]
    obtain ⟨r, hr, hstop⟩ := hthreshold m hm hbm hbmK (by rw [← hprefix]; exact hcount)
    exact (kept_iff_le_stopIndex K i U (b + m) hbmK).mpr hbm r hr hstop

private theorem ordinary_before_stop
    (K : List (ReferenceCompletePhysicalHistory.RoundRecord p rate))
    (Z : ℕ → ReferenceActivePhysicalStep.State p rate)
    (i : Fin (p.m - 1)) (U : OrdinaryMessageCodec.UpRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (hlinks : ∀ q : Fin K.length,
      (K.get q).input.state = Z q.val ∧ (K.get q).output.next = Z (q.val + 1))
    (hzero : (Z 0).coordinator ≠ .dagger) :
    ∀ j : ℕ, j ≤ K.length → j ≤ stopIndex K i U → (Z j).coordinator ≠ .dagger := by
  intro j
  induction j with
  | zero => exact fun _ _ => hzero
  | succ j ih =>
      intro hj hs
      have hjK : j < K.length := by omega
      have hbefore := ih (by omega) (by omega)
      intro hd
      obtain ⟨reason, hreason⟩ :=
        ReferenceFirstReplacementCollectionPureUpWindowCut.first_dagger_record_failure
          (K.get ⟨j, hjK⟩) (by rw [(hlinks ⟨j, hjK⟩).1]; exact hbefore)
          (by rw [(hlinks ⟨j, hjK⟩).2]; exact hd)
      have hkept := (kept_iff_le_stopIndex K i U (j + 1) hj).mpr hs
      apply hkept (K.get ⟨j, hjK⟩) _ (Or.inr (Or.inl (Or.inl ⟨reason, hreason⟩)))
      exact List.mem_iff_getElem.mpr ⟨j, by simp; omega, by simp⟩

private theorem mem_positive_drop_tail
    (trace : AffineBatchDecoder.Trace p) (rounds : List (Fin p.T)) (skip : ℕ)
    (entry : AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p))
    (hskip : 0 < skip)
    (hentry : entry ∈ (AffineBatchDecoder.positives p trace rounds).drop skip) :
    entry.time ∈ rounds.drop 1 := by
  induction rounds generalizing skip with
  | nil => simp [AffineBatchDecoder.positives] at hentry
  | cons round rest ih =>
      cases skip with
      | zero => omega
      | succ skip =>
          by_cases hp : AffineBatchDecoder.eligible (trace round)
          · have ht : entry ∈ (AffineBatchDecoder.positives p trace rest).drop skip := by
              simpa [AffineBatchDecoder.positives_cons, AffineBatchDecoder.positiveAt, hp]
                using hentry
            cases skip with
            | zero =>
                exact (AffineBatchDecoder.mem_positives_iff p trace rest entry).mp ht |>.1
            | succ skip =>
                exact List.mem_of_mem_drop (ih (skip + 1) (by omega) ht)
          · have ht : entry ∈ (AffineBatchDecoder.positives p trace rest).drop (skip + 1) := by
              simpa [AffineBatchDecoder.positives_cons, AffineBatchDecoder.positiveAt, hp]
                using hentry
            exact List.mem_of_mem_drop (ih (skip + 1) (by omega) ht)

private theorem mem_drop_take_index
    (K : List (ReferenceCompletePhysicalHistory.RoundRecord p rate))
    (b m : ℕ) (r : ReferenceCompletePhysicalHistory.RoundRecord p rate)
    (hr : r ∈ (K.drop b).take m) :
    ∃ a : Fin K.length, b ≤ a.val ∧ a.val < b + m ∧ K.get a = r := by
  obtain ⟨j, hj, hget⟩ := List.mem_iff_getElem.mp hr
  have hjm : j < m := by simp only [List.length_take] at hj; omega
  have hjK : b + j < K.length := by
    simp only [List.length_take, List.length_drop] at hj
    omega
  refine ⟨⟨b + j, hjK⟩, ?_, ?_, ?_⟩
  · change b ≤ b + j
    omega
  · change b + j < b + m
    omega
  · simpa only [List.get_eq_getElem, List.getElem_take, List.getElem_drop] using hget

private theorem pure_window_lower
    (K : List (ReferenceCompletePhysicalHistory.RoundRecord p rate))
    (i : Fin (p.m - 1)) (b m u skip : ℕ)
    (hcalendar : ∀ a : Fin K.length, (K.get a).input.time.val + 1 = u + a.val)
    (hskip : 0 < skip)
    (e : AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p))
    (he : e ∈ (physicalPositives ((K.drop b).take m) i).drop skip) :
    u + b ≤ e.time.val := by
  dsimp only [physicalPositives] at he
  have ht := mem_positive_drop_tail
    (ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace ((K.drop b).take m) i)
    (((K.drop b).take m).map (fun r : ReferenceCompletePhysicalHistory.RoundRecord p rate =>
      r.input.time)) skip e hskip he
  rw [← List.map_drop] at ht
  obtain ⟨r, hr, htime⟩ := List.mem_map.mp ht
  have hr' : r ∈ (K.drop (b + 1)).take (m - 1) := by
    simpa only [List.drop_take, List.drop_drop] using hr
  obtain ⟨a, ha, _, hget⟩ := mem_drop_take_index K (b + 1) (m - 1) r hr'
  have hc := hcalendar a
  rw [hget, htime] at hc
  omega

/-- The source-root quota uses only the original execution inputs. The actual
formation, inherited bank, fixed reply and stopping readouts are produced
inside the proof. Absence of a current origin and terminal/next-birth cases
remain separate. -/
theorem complete_first_replacement_collection_stopped_pure_up_quota
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
    let v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
    let tail := ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v
    let c := v + 1 + tail.length
    match R[v]? with
    | none => True
    | some birth =>
      match birth.output.preparation.coordinator with
      | .collection _ _ _ _ (.laterChosen _ _ _ _ _ _ _ _ _ installed _) =>
        let payload := installed.registers.payload
        let X := (R.drop v).take (1 + tail.length)
        match R[c]? with
        | none => True
        | some cut =>
          match cut.output.preparation.coordinator with
          | .live _ _ _ (.cutoffChosen _ _ _ _ _ _ _ _ _ _) =>
            let W := (R.drop (c + 1)).takeWhile
              (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
            let K := cut :: W
            let Z := fun j => ReferenceCollectionSegmentExtraction.endpointState
              cut.input.state (K.take j)
            let E := fun j => ReferenceCollectionSegmentExtraction.endpointState
              cut.output.next (W.take j)
            let M := fun i => payload.downRecord i
            (∀ i : Fin (p.m - 1),
              (∃ (b : ℕ) (anchor : ReferencePrelaunchFollower.State p rate.eta)
                (memory : ActiveFollowerLifecycle.LocalMemory p)
                (U : OrdinaryMessageCodec.UpRecord (ReferencePrelaunchFollower.codecParams p rate.eta)),
                ((b = 0 ∧
                  (ReferenceFollowerFixedReply.actualChoice cut i).configuration =
                    .ordinary anchor memory ∧
                  ∃! x : Fin X.length,
                    ReferenceAcceptedUpFollowerHistory.RetainedDown (X.get x) i (M i)) ∨
                 (∃ q : Fin K.length, b = q.val + 1 ∧
                  ReferenceAcceptedUpFollowerHistory.RetainedDown (K.get q) i (M i) ∧
                  (∀ a : Fin K.length, a.val < q.val →
                    ¬ ReferenceAcceptedUpFollowerHistory.RetainedDown (K.get a) i (M i)) ∧
                  (K.get q).output.next.followers i = .ordinary anchor memory)) ∧
                b ≤ K.length ∧ anchor.status = .unoccupied ∧
                ActiveFollowerLifecycle.localStateDomainValid anchor ∧
                anchor.lastDown = some (M i) ∧
                U.val = ActiveFollowerQueueOperation.upOfferFields anchor ∧
                U.val.sigma = (M i).val.sigma ∧ 0 < U.val.sigma ∧
                let channel := (Z b).upDecoderBank i
                let Q := AffineBatchDecoder.quota p
                let need := Q - channel.pending.length + Q
                channel.pending.length < Q ∧ need ≤ 2 * Q ∧
                (∀ j : ℕ, j ≤ K.length → stoppedFormedCount K b i U j ≤ need) ∧
                ((∃ a : Fin K.length, stopIndex K i U = a.val ∧
                  localStop K i U (K.get a) ∧ kept K i U a.val) ∨
                 (stopIndex K i U = K.length ∧ ∀ r ∈ K, ¬ localStop K i U r))) ∨
              ((∀ a : Fin K.length, ∃ state memory,
                  (ReferenceFollowerFixedReply.actualChoice (K.get a) i).configuration =
                    .ordinary state memory ∧ state.status = .unoccupied ∧
                  state.lastDown ≠ some (M i) ∧
                  ReferencePrelaunchFollower.acceptedStart state < (M i).val.sigma ∧
                  ((state.lastDown = none ∧ state.S = 0 ∧ state.delta = 0 ∧ state.backlog = 0) ∨
                   ∃ old, state.lastDown = some old ∧ 0 < old.val.sigma ∧
                     old.val.sigma < (M i).val.sigma)) ∧
               (∀ a : Fin K.length,
                 ¬ ReferenceAcceptedUpFollowerHistory.RetainedDown (K.get a) i (M i)) ∧
               R[c + 1 + W.length]? = none ∧
               ∀ j : ℕ, j ≤ K.length → formedPositiveEntries (K.take j) i (M i) = [])) ∧
            (∀ (a : Fin K.length) (d : ReferenceActivePhysicalStep.UpDiagnostic p rate),
              let r := K.get a
              r.output.coordinator.up = some d →
              d.input.upDecoderBank = (Z a.val).upDecoderBank ∧
              d.expected = ReferenceActivePhysicalStep.upExpected
                (ReferenceActivePhysicalStep.prepare r.input) ∧
              d.raw = (CoordinatorUpReception.decoderTransition d.input).2 ∧
              ∃ ledger,
                ReferenceCoordinatorUpPhysicalCall.siteLedger? (x := r.input) = some ledger ∧
                CoordinatorUpReception.receptionInputCheck
                  (ReferenceCoordinatorUpPhysicalCall.actualUpInput r.input ledger) = true ∧
                d.input = ReferenceCoordinatorUpPhysicalCall.actualUpInput r.input ledger ∧
                d.decoderAfter = (CoordinatorUpReception.decoderTransition
                  (ReferenceCoordinatorUpPhysicalCall.actualUpInput r.input ledger)).1 ∧
                (((ReferenceActivePhysicalStep.receiveUp
                    (ReferenceActivePhysicalStep.prepare r.input) ledger).result = .invalid ∧
                    r.output.next.upDecoderBank = r.input.state.upDecoderBank) ∨
                  ∃ out,
                    ((ReferenceActivePhysicalStep.receiveUp
                      (ReferenceActivePhysicalStep.prepare r.input) ledger).result = .success out ∨
                     (ReferenceActivePhysicalStep.receiveUp
                      (ReferenceActivePhysicalStep.prepare r.input) ledger).result = .rejected out) ∧
                    out.2 = CoordinatorUpReception.decoderBankAfter d.input ∧
                    r.output.next.upDecoderBank = out.2)) ∧
            match R[c + 1 + W.length]? with
            | none => c + 1 + W.length = R.length ∧
                ReferenceCompletePhysicalHistory.completeTerminalState rate source rewards C_star C_h =
                  some (E W.length)
            | some next => next.input.state = E W.length ∧
                ReferenceCollectionPhaseHistory.laterChosen next.input = true ∧
                ∃ ledger saved, (E W.length).coordinator = .collection payload ledger saved ∧
                  ledger.pending = ∅ ∧
                  ∀ i : Fin (p.m - 1), ∃ r ∈ K, ∃ U,
                    ReferenceCollectionPhaseHistory.AcceptedUp r.input i U
          | _ => True
      | _ => True := by
  classical
  have hRoot :=
    ReferenceFirstReplacementCollectionPureUpAcceptanceRoot.complete_first_replacement_collection_pure_up_acceptance
      rate source rewards C_star C_h
  have hSelected :=
    ReferenceFirstReplacementCollectionSelectedUpAwaitedFields.complete_first_replacement_collection_selected_up_awaited_fields
      rate source rewards C_star C_h
  have hStarted :=
    ReferenceFirstReplacementCollectionUpStartedFields.complete_first_replacement_collection_up_started_fields
      rate source rewards C_star C_h
  simp (config := { zeta := true }) only [] at hRoot hSelected hStarted ⊢
  set R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
  set s := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
  set w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
  set v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
  set tail := ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v
  set c := v + 1 + tail.length
  cases hb : R[v]? with
  | none => trivial
  | some birth =>
    simp only [hb] at hRoot hSelected hStarted ⊢
    cases hbirth : birth.output.preparation.coordinator with
    | first _ => trivial
    | live _ _ _ _ => trivial
    | dagger => trivial
    | invalidCollectionCutoff => trivial
    | collection _ _ _ _ outcome =>
      simp only [hbirth] at hRoot hSelected hStarted ⊢
      cases outcome <;> try trivial
      rename_i core consistent birthStarted hstart instruction hinstruction output hconsistent
        clockData installed selectedBirth
      dsimp only [ReferenceActivePhysicalStep.collectionInput] at hRoot hSelected hStarted ⊢
      let payload : ReferenceActivePhysicalStep.Payload rate := installed.registers.payload
      rcases hRoot with ⟨_, _, hRoot⟩
      cases hc : R[c]? with
      | none => trivial
      | some cut =>
        simp only [hc] at hRoot hSelected hStarted ⊢
        cases hcut : cut.output.preparation.coordinator with
        | first _ => trivial
        | collection _ _ _ _ _ => trivial
        | dagger => trivial
        | invalidCollectionCutoff => trivial
        | live registers owned base outcome =>
          simp only [hcut] at hRoot hSelected hStarted ⊢
          cases outcome <;> try trivial
          rename_i dispatched hs ledger hi hledger hdata hclock hpending hnone selectedCut
          dsimp only at hRoot hSelected hStarted ⊢
          let u := cut.input.time.val + 1
          let W := (R.drop (c + 1)).takeWhile
            (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
          let K := cut :: W
          let E := fun j => ReferenceCollectionSegmentExtraction.endpointState
            cut.output.next (W.take j)
          let Z := fun j => ReferenceCollectionSegmentExtraction.endpointState
            cut.input.state (K.take j)
          let M := fun i => payload.downRecord i
          rcases hRoot with ⟨hcalendar, hZ, hfollowers, hboundary⟩
          have hKprefix : K <+: R.drop c := by
            obtain ⟨hci, hce⟩ := List.getElem?_eq_some_iff.mp hc
            rw [List.drop_eq_getElem_cons hci, hce]
            refine ⟨(R.drop (c + 1)).dropWhile
              (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input), ?_⟩
            simp only [K, W, List.cons_append, List.takeWhile_append_dropWhile]
          obtain ⟨initial, active, _hlaunch, _hfirst, _hbank, hInvInitial,
              hseed, _hfull, hRuns⟩ :=
            ReferenceFirstReplacementCollectionPureUpWindowCut.source_interval_runs
              rate source rewards C_star C_h c cut hc K hKprefix
          have hInv : ∀ j, j ≤ K.length → ReferenceUpDecoderBankInvariant.upBankInvariant (Z j) := by
            intro j hj
            obtain ⟨span, _, hend⟩ := hRuns j hj
            change (ReferenceActivePhysicalHorizon.run initial source.1.2
              (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s
              (c + j) span active).finalState = Z j at hend
            rw [← hend]
            exact ReferenceUpDecoderBankInvariant.run_upBankInvariant initial source.1.2
              (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s
              (c + j) span active hInvInitial
          have hchronR :=
            ReferenceFirstReplacementCollectionPureUpWindowCut.complete_records_chronological
              rate source rewards C_star C_h
          have hchronK : K.Pairwise
              (fun earlier later => earlier.input.time.val < later.input.time.val) :=
            List.Pairwise.sublist hKprefix.sublist hchronR.drop
          have hzero : (Z 0).coordinator ≠ .dagger := by
            change cut.input.state.coordinator ≠ .dagger
            intro hd
            have hp := ReferenceActivePhysicalStep.dispatch_dagger cut.input hd
            change (ReferenceActivePhysicalStep.prepare cut.input).coordinator = .dagger at hp
            have hactual := hcut
            rw [cut.output_eq] at hactual
            change (ReferenceActivePhysicalStep.prepare cut.input).coordinator = _ at hactual
            rw [hp] at hactual
            cases hactual
          refine ⟨?_, ?_, ?_⟩
          · intro i
            rcases hfollowers i with hcurrent | habsent
            · rcases hcurrent with ⟨b, anchor, memory, horigin, hbK, hstatus, hdomain,
                  hlastDown, _hfinal, U, hfields, hsigma, hpositive, hchoices,
                  hentries, hpure, _hcases⟩
              refine Or.inl ⟨b, anchor, memory, U, ?_, hbK, hstatus, hdomain,
                hlastDown, hfields, hsigma, hpositive, ?_⟩
              · rcases horigin with hzero | ⟨q, hbq, hretained, hbefore, hnext, _⟩
                · exact Or.inl hzero
                · exact Or.inr ⟨q, hbq, hretained, hbefore, hnext⟩
              · let H := K.drop b
                let channel := (Z b).upDecoderBank i
                let Q := AffineBatchDecoder.quota p
                let need := Q - channel.pending.length + Q
                have hn : channel.pending.length < Q := ((hInv b hbK).1 i).1
                have hneed : 0 < need := by
                  have hQ := AffineBatchDecoder.quota_pos p
                  dsimp only [need, Q]
                  omega
                have hskip : 0 < Q - channel.pending.length := by omega
                refine ⟨hn, by change Q - channel.pending.length + Q ≤ 2 * Q; omega,
                  ?_, stopIndex_certificate K i U⟩
                apply stopped_count_le K b i U need hneed hchronK
                intro m hm hsafe hbm hcount
                have hordinary := ordinary_before_stop K Z i U hZ.2.2 hzero
                have hprefixOrdinary := hordinary (b + m) hbm hsafe
                obtain ⟨span, hdrop, hendRun⟩ := hRuns (b + m) hbm
                obtain ⟨spanPre, _, hpre⟩ := hRuns b hbK
                let full := ReferenceActivePhysicalHorizon.run initial source.1.2
                  (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s
                  (c + (b + m)) span active
                have hinterval : full.records.drop (c + b) = H.take m := by
                  rw [← List.drop_drop, hdrop, List.drop_take]
                  simp only [Nat.add_sub_cancel_left]
                  rfl
                change (ReferenceActivePhysicalHorizon.run initial source.1.2
                  (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s
                  (c + b) spanPre active).finalState = Z b at hpre
                change full.finalState = Z (b + m) at hendRun
                dsimp only [full] at hinterval
                have hcountRun : (physicalPositives (full.records.drop (c + b)) i).length =
                    AffineBatchDecoder.quota p -
                      ((ReferenceActivePhysicalHorizon.run initial source.1.2
                        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s
                        (c + b) spanPre active).finalState.upDecoderBank i).pending.length +
                      AffineBatchDecoder.quota p := by
                  rw [hinterval, hpre]
                  rw [physicalPositives,
                    ReferenceCoordinatorUpIntervalWindow.actual_trace_positives_eq_retained
                      (H.take m) i hchronK.drop.take]
                  exact hcount
                have hsaved :=
                  ReferenceCoordinatorUpWindowCompletedCut.run_interval_saved_completed_cut
                    initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
                    rewards s (c + b) (c + (b + m)) (by omega) span active hInvInitial
                    (by rw [hendRun]; exact hprefixOrdinary) i (hseed i) hcountRun
                dsimp only [ReferenceCoordinatorUpIntervalWindow.intervalRounds,
                  ReferenceCoordinatorUpIntervalWindow.intervalRecords] at hsaved
                obtain ⟨first, last, index, r, d, hfirst, hfirstLen, hwindowLen, hchron,
                  hlast, hdecision, _hround, hr, htime, hd, hdi, hdt, hentry, hsample,
                  hphysical, _hconnected, _hreplay, hbank, hbefore, hpending,
                  _hclear, _hcompleted, _hafter, _hraw, hbatch, _htransition,
                  _hrun, _hfinalBank⟩ := hsaved
                simp only [hinterval, hpre] at hfirst hfirstLen hwindowLen hchron hlast hdecision hr hentry hbefore hpending hbatch
                let positive := physicalPositives (H.take m) i
                let window := positive.drop (Q - channel.pending.length)
                change last ∈ window at hlast
                change window.Pairwise (fun e f => e.time.val < f.time.val) at hchron
                change AffineBatchDecoder.decisionTime window = some last.time at hdecision
                change window.length = Q at hwindowLen
                have hwindowPure : ∀ e ∈ window, AffineBatchDecoder.equation e.sample
                    (ActiveFollowerArmChoice.offeredUpWord rate.eta U) := by
                  intro e he
                  apply hpure e
                  rw [physicalPositives,
                    ReferenceCoordinatorUpIntervalWindow.actual_trace_positives_eq_retained H i hchronK.drop]
                  have he' : e ∈ physicalPositives (H.take m) i := List.mem_of_mem_drop he
                  rw [physicalPositives,
                    ReferenceCoordinatorUpIntervalWindow.actual_trace_positives_eq_retained
                      (H.take m) i hchronK.drop.take] at he'
                  obtain ⟨x, hx, he''⟩ := List.mem_flatMap.mp he'
                  exact List.mem_flatMap.mpr ⟨x, List.mem_of_mem_take hx, he''⟩
                have hlower : ∀ e ∈ window, u + b ≤ e.time.val := by
                  intro e he
                  exact pure_window_lower K i b m u _ hcalendar hskip e he
                obtain ⟨a, hba, ham, hget⟩ := mem_drop_take_index K b m r hr
                have haSafe : a.val < stopIndex K i U := by omega
                have hcal := hcalendar a
                rw [hget] at hcal
                have hlastLower := hlower last hlast
                rw [← htime] at hlastLower
                have hbaStrict : b < a.val := by omega
                have haPositive : 0 < a.val := by omega
                have hnonDagger : r.output.next.coordinator ≠ .dagger := by
                  rw [← hget, (hZ.2.2 a).2]
                  exact hordinary (a.val + 1) (by have := a.isLt; omega) (by omega)
                have hawaited : ∀ x ∈ K, u + b ≤ x.input.time.val →
                    x.input.time.val ≤ r.input.time.val →
                    ReferenceSelectedAffinePairLaw.selectedChannel p (x.input.row.2 x.input.time).1 =
                      some (1, i) → awaitedCall x i U := by
                  intro x hx hlow hupp hselected
                  obtain ⟨z, hz, hzx⟩ := List.mem_iff_getElem.mp hx
                  let qa : Fin K.length := ⟨z, hz⟩
                  have hxGet : K.get qa = x := hzx
                  have hcalendarX := hcalendar qa
                  rw [hxGet] at hcalendarX
                  change x.input.time.val + 1 = u + z at hcalendarX
                  have hzlow : b < z := by omega
                  have hzupper : z ≤ a.val := by omega
                  have hzsafe : z < stopIndex K i U := by omega
                  have hxOrdinary : x.output.next.coordinator ≠ .dagger := by
                    rw [← hxGet, (hZ.2.2 qa).2]
                    exact hordinary (z + 1) (by omega) (by omega)
                  let j : Fin W.length := ⟨z - 1, by
                    have hlen : z < W.length + 1 := hz
                    omega⟩
                  have hjplus : j.val + 1 = z := by dsimp only [j]; omega
                  have hxW : W.get j = x := by
                    have hsucc : (Fin.succ j : Fin K.length) = qa := by
                      apply Fin.ext
                      exact hjplus
                    rw [← hxGet, ← hsucc]
                    simp only [K, List.get_eq_getElem, Fin.val_succ, List.getElem_cons_succ]
                  have hSF := hSelected j
                  rw [hxW] at hSF
                  have hSF := fields_of_not_dagger x.output.next.coordinator hSF hxOrdinary
                  have hselCast : ReferenceSelectedAffinePairLaw.selectedChannel p
                      (x.input.row.2 x.input.time).1 = some (1, Fin.cast
                        (show p.m - 1 = ContinuousLearningRows.d p by rfl) i) := by
                    have hcast : Fin.cast
                        (show p.m - 1 = ContinuousLearningRows.d p by rfl) i = i := Fin.ext rfl
                    rw [hcast]
                    exact hselected
                  obtain ⟨stateA, memA, UA, LA, dA, hcfgA, _hstatusA, _hfieldsA,
                    hcheckedA, hsentA, _hsiteA, hcheckA, hdA, hinputA, hiA,
                    hexpectedA, _hsigmaA, _hcutoffA, _hcursorA, _hcutCursorA,
                    _hpendingA, hselectedIffA, henabledA, hcaseA⟩ := hSF i hselCast
                  obtain ⟨stateP, memP, hcfgP, _hstatusP, _hdownP, _hreplyP, hofferP, _⟩ :=
                    hchoices qa (by change b ≤ z; omega)
                  rw [hxGet] at hcfgP hofferP
                  have hstateEq : stateA = stateP := by
                    exact (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
                      (hcfgA.symm.trans hcfgP)).1
                  have hdraw : ReferenceActivePhysicalStep.upSenderIndex x.input = i := by
                    unfold ReferenceSelectedAffinePairLaw.selectedChannel
                      ReferenceSelectedAffinePairLaw.channelFromDraws at hselected
                    split_ifs at hselected with hdown hup
                    · have he := congrArg Prod.fst (Option.some.inj hselected)
                      exact (zero_ne_one he).elim
                    · have hi := (Prod.mk.inj (Option.some.inj hselected)).2
                      change CoordinatorUpMeasurability.selectedFollowerIndex
                        (x.input.row.2 x.input.time) = i
                      rw [CoordinatorUpMeasurability.selectedFollowerIndex_eq_draw]
                      exact hi
                  have hslot : PublicDiscreteDraws.slotDraw (x.input.row.2 x.input.time).1 =
                      PublicDiscreteDraws.upSlot := by
                    unfold ReferenceSelectedAffinePairLaw.selectedChannel
                      ReferenceSelectedAffinePairLaw.channelFromDraws at hselected
                    split_ifs at hselected with hdown hup
                    · have he := congrArg Prod.fst (Option.some.inj hselected)
                      exact (zero_ne_one he).elim
                    · exact hup
                  have hoffer := (hofferP hdraw hslot).1
                  have hcodec := ReferenceUpReception.ledgerCodecParams_eq_followerCodecParams rate
                  cases hcodec
                  have hUA : UA = U := by
                    apply ActiveFollowerQueueOperation.UpOfferResult.offer.inj
                    rw [← hcheckedA, hstateEq]
                    exact hoffer
                  have hnotPrior : i ∉ (ReferenceCollectionPhaseHistory.acceptedLabels
                      (K.take z)).toFinset := by
                    intro hmem
                    rw [List.mem_toFinset] at hmem
                    obtain ⟨y, hy, hlabel⟩ := List.mem_filterMap.mp hmem
                    have hkept := (kept_iff_le_stopIndex K i U z (by omega)).mpr (by omega)
                    exact hkept y hy (Or.inl ((acceptanceAt_iff y i).mpr hlabel))
                  have hnotPriorJ : i ∉ (ReferenceCollectionPhaseHistory.acceptedLabels
                      (K.take (j.val + 1))).toFinset := by simpa only [hjplus] using hnotPrior
                  have hacceptA : CoordinatorCollectionLedger.acceptUpCheck LA i UA = true := by
                    rcases hcaseA with hstale | hcurrentA
                    · rw [hUA, hsigma] at hstale
                      exact (lt_irrefl _ hstale.2.1).elim
                    · exact hcurrentA.2.2.mpr hnotPriorJ
                  refine ⟨?_, dA, hdA, hiA, ?_, hselectedIffA.mpr hnotPriorJ, henabledA, ?_, ?_⟩
                  · simpa only [hUA] using hsentA
                  · simpa only [hinputA] using hcheckA
                  · have hledgerEq : dA.input.ledger = LA := by rw [hinputA]; rfl
                    rw [hledgerEq, ← hUA]
                    exact hacceptA
                  · simpa only [hUA] using hexpectedA
                have hdiagFields := ReferenceCoordinatorUpPhysicalCall.record_retained_up_input_fields r d hd
                obtain ⟨L, hsite, hledgerD, _hbankD, _htimeD, _hobs, hsender,
                  hsampleD, hslotD, _⟩ := hdiagFields
                have hlastSample : last.sample = d.input.affineSample := hsample.trans hsampleD.symm
                have heligible : AffineBatchDecoder.eligible (CoordinatorUpReception.roundInput d.input) := by
                  have hlastPositive : last ∈ physicalPositives (H.take m) i := List.mem_of_mem_drop hlast
                  have he := (AffineBatchDecoder.mem_positives_iff p
                    (ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace (H.take m) i)
                    _ last).mp hlastPositive
                  have htrace := ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace_at_record
                    (H.take m) i hchronK.drop.take r hr
                  rw [← htime, htrace] at he
                  simpa only [ReferenceCoordinatorUpIntervalWindow.recordFocalInput,
                    hd, hdi, ite_eq_left, ReferenceCoordinatorUpDecoderReplay.retainedUpRoundInput] using he.2.1
                have hselectedChannel : ReferenceSelectedAffinePairLaw.selectedChannel p
                    (r.input.row.2 r.input.time).1 = some (1, i) := by
                  have hgate := (CoordinatorUpReception.roundInput_selected_iff_gate d.input).mp heligible.1
                  have hslot : PublicDiscreteDraws.slotDraw (r.input.row.2 r.input.time).1 =
                      PublicDiscreteDraws.upSlot := hslotD.symm.trans hgate.2.1
                  have hiDraw : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
                      (r.input.row.2 r.input.time).1 = i := by
                    rw [← CoordinatorUpMeasurability.selectedFollowerIndex_eq_draw]
                    exact hsender.symm.trans hdi
                  rw [ReferenceSelectedAffinePairLaw.selectedChannel_of_up p _ hslot, hiDraw]
                  rfl
                have hawaitedR := hawaited r (by rw [← hget]; exact List.getElem_mem _)
                  hlastLower le_rfl hselectedChannel
                obtain ⟨_hsentR, dA, hdA, _hiA, hcheckA, _hselectA, _henableA,
                  hacceptA, hexpectedA⟩ := hawaitedR
                have hdEq : dA = d := Option.some.inj (hdA.symm.trans hd)
                subst dA
                have hlastEntry : last = AffineBatchDecoder.entry p
                    (ReferenceCoordinatorUpDecoderReplay.constantInputTrace d.input) d.input.time := by
                  cases last with
                  | mk lastTime lastSample =>
                    simp only [AffineBatchDecoder.entry,
                      ReferenceCoordinatorUpDecoderReplay.constantInputTrace,
                      AffineBatchDecoder.Entry.mk.injEq]
                    exact ⟨htime.symm.trans hdt.symm, hlastSample⟩
                have hbatchEq : (r.input.state.upDecoderBank i).pending ++
                    [AffineBatchDecoder.entry p
                      (ReferenceCoordinatorUpDecoderReplay.constantInputTrace d.input) d.input.time] = window := by
                  rw [← hbank, ← hbefore, ← hlastEntry, hentry]
                  exact hpending
                have hrPrefix : r ∈ K.take (b + m) := by
                  apply List.mem_iff_getElem.mpr
                  exact ⟨a.val, by simp; omega, by simpa only [List.getElem_take, List.get_eq_getElem] using hget⟩
                refine ⟨r, hrPrefix, ?_⟩
                rcases ReferenceFirstReplacementCollectionPureUpWindowCut.pure_batch_raw_cases
                    window (ActiveFollowerArmChoice.offeredUpWord rate.eta U) hwindowPure with
                  ⟨hrawNone, hother⟩ | ⟨hrawSome, _hunique⟩
                · right
                  right
                  refine ⟨hpositive, d, u + b, hd, hdi, hcheckA, heligible, hbank, hdt, ?_⟩
                  rw [hbatchEq]
                  refine ⟨hwindowLen, hbatch, hbatch.trans hrawNone, hwindowPure,
                    hother, ?_, hawaited⟩
                  intro e he
                  refine ⟨hlower e he, ?_⟩
                  have hne : window ≠ [] := by
                    intro h
                    rw [h] at hlast
                    cases hlast
                  have hlastTime : (window.getLast hne).time = last.time := by
                    have hdtime := hdecision
                    change (window.map (fun e => e.time)).getLast? = some last.time at hdtime
                    rw [List.getLast?_map, List.getLast?_eq_some_getLast hne] at hdtime
                    exact Option.some.inj hdtime
                  have hchronLe : window.Pairwise (fun e f => e.time.val ≤ f.time.val) :=
                    hchron.imp (by intro e f h; exact Nat.le_of_lt h)
                  have hle := hchronLe.rel_getLast_of_rel_getLast_getLast he (Nat.le_refl _)
                  rw [hlastTime, ← htime] at hle
                  exact hle
                · left
                  let j : Fin W.length := ⟨a.val - 1, by
                    have haLength := a.isLt
                    change a.val < W.length + 1 at haLength
                    omega⟩
                  have hjplus : j.val + 1 = a.val := by dsimp only [j]; omega
                  have hrW : W.get j = r := by
                    have hsucc : (Fin.succ j : Fin K.length) = a := Fin.ext hjplus
                    rw [← hget, ← hsucc]
                    simp only [K, List.get_eq_getElem, Fin.val_succ, List.getElem_cons_succ]
                  have hstart := hStarted j
                  rw [hrW] at hstart
                  have hstart := fields_of_not_dagger r.output.next.coordinator hstart hnonDagger
                  obtain ⟨ledger, saved, t, _, _, _, hstate, htail, _⟩ := hstart
                  obtain ⟨recording, started, dB, _hrecording, _hstart, hsiteB, _hcheckB,
                    hdB, hinputB, _hreception, _hnotInvalid, _hfinish, _hdecoderB,
                    _hrawB, _hparsedB, _hlocalB, _hexpectedB, _hmatchesB, _hbankB,
                    _htimeB, _hsampleB, _hobsB, _hwrongB, hmatching⟩ :=
                    ReferenceCollectionUpReceiverLocal.actual_collection_up_receiver_matching_word
                      r payload ledger saved t hstate htail hnonDagger
                  have hdBEq : dB = d := Option.some.inj (hdB.symm.trans hd)
                  subst dB
                  have hstartedEq : started = d.input.ledger := by rw [hinputB]; rfl
                  have hsenderI : ReferenceActivePhysicalStep.upSenderIndex r.input = i := hsender.symm.trans hdi
                  have hmatch := hmatching U (hbatch.trans hrawSome) hexpectedA
                    (by rw [hsenderI, hstartedEq]; exact hacceptA)
                  obtain ⟨_hfiltered, _hparsed, _hlocal, _hmatches, _hwrong,
                    decoded, bank, hreceive, haccepted⟩ := hmatch
                  have hacceptedI : ReferenceCollectionPhaseHistory.AcceptedUp r.input i U := by
                    simpa only [hsenderI] using haccepted
                  refine ⟨?_, U, hacceptedI⟩
                  unfold ReferenceCollectionPhaseHistory.acceptedLabel
                  rw [htail]
                  simp only [Option.bind_some, _hreception, hreceive, hsenderI]
            · refine Or.inr ⟨habsent.1, habsent.2.2.1, habsent.2.2.2.2, ?_⟩
              intro j _hj
              apply formedPositiveEntries_eq_nil_of_unformed
              intro r hr hformed
              obtain ⟨a, ha, hget⟩ := List.mem_iff_getElem.mp (List.mem_of_mem_take hr)
              obtain ⟨state, memory, hconfig, _hstatus, hnot, _⟩ := habsent.1 ⟨a, ha⟩
              have hrGet : K.get ⟨a, ha⟩ = r := hget
              rw [hrGet] at hconfig
              obtain ⟨state', memory', hconfig', _hstatus', hdown⟩ := hformed
              have hstate := (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
                (hconfig.symm.trans hconfig')).1
              exact hnot (by rw [hstate]; exact hdown)
          · intro a d hd
            obtain ⟨_, _, _, hbank, _⟩ :=
              ReferenceCoordinatorUpPhysicalCall.record_retained_up_input_fields (K.get a) d hd
            have hraw :=
              ReferenceFirstReplacementCollectionPureUpWindowCut.retained_diagnostic_raw_expected
                (K.get a) d hd
            refine ⟨hbank.trans (congrArg ReferenceActivePhysicalStep.State.upDecoderBank
              (hZ.2.2 a).1), hraw.1, hraw.2, ?_⟩
            apply ReferenceCoordinatorUpPhysicalCall.record_up_commit_cases (K.get a) d hd
            rw [(hZ.2.2 a).1]
            exact hInv a.val (Nat.le_of_lt a.isLt)
          · cases hterminal : R[c + 1 + W.length]? with
            | none =>
              simp only [W, hterminal] at hboundary ⊢
              exact hboundary
            | some next =>
              simp only [W, hterminal] at hboundary ⊢
              obtain ⟨hstate, hlater, ledger, saved, hcoord, _hnextCoord, hpending, haccepted⟩ := hboundary
              exact ⟨hstate, hlater, ledger, saved, hcoord, hpending, haccepted⟩

end Bandits.Support.ReferenceFirstReplacementCollectionStoppedPureUpQuota

end
