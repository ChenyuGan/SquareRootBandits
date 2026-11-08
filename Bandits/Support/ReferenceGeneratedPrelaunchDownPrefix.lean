/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedPrelaunchDownCohort
public import Bandits.Support.GeneratedBootstrapRoundLaw
public import Bandits.Support.ReferenceSuppressedDownCoverage

/-!
# Generated prelaunch DOWN prefixes and cohort births

Source ranges: `appendix_a_local_protocol.tex:92-153`,
`appendix_b_communication.tex:724-736`, `05_binary_transport.tex:20-42`,
`07_public_setup.tex:60-112,127-142`, and `08_main_theorem.tex:29-42`.

The constructions below retain projections of the existing generated
initialization boundary and the existing follower replay. At round `r`, the
local history is restricted to its first `r.val` entries, so it ends strictly
before observation `r`. No probability or manuscript closure claim is made.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ReferenceGeneratedPrelaunchDownPrefix

open ConstructorDimensions BootstrapDimensions
open ReferenceInitializationRun ReferencePrelaunchFollower
open ReferenceGeneratedDownBatchCalendar
open AffineBatchDecoder AffineChannelLaw
open scoped Classical

variable {p : ConstructorDimensions.Parameters}

/-- A processed boundary, retaining its actual proof that another initialization
block remains. This is only a subtype of the accepted run boundary. -/
abbrev ProcessedBoundary (x : ReferenceInitializationRun.Input p)
    (s : Fin (n_boot p)) :=
  {b : ReferenceInitializationRun.Boundary p //
    b.completed < n_boot p ∧ b.crossing = none ∧
      b = ReferenceInitializationRun.run x s.val}

/-- The processed active projection retains the actual activation selector. -/
abbrev ActiveProjection (p : ConstructorDimensions.Parameters)
    (i : Fin (p.m - 1)) (n : ℕ) (row : CompletePublicTable.CompleteRow p)
    (hn : n ≤ p.T) (x : ReferenceInitializationRun.Input p) (s : Fin (n_boot p)) :=
  {v : ProcessedBoundary x s × Activation p × LocalHistory p n × State p x.eta //
    ∃ hbefore : n ≤ ReferenceInitializationRun.elapsed p (v.1.val.completed + 1),
      v.1.val.activation (ActualReferenceInitializationBlock.refFollower i) = some v.2.1 ∧
      v.2.2.2 = ReferencePrelaunchFollower.replay x.eta i row v.2.1 v.2.2.1 hn ∧
      v.2.2.1 = ReferencePrelaunchLifecycleReplay.prefixHistory
        (ReferenceInitializationRun.extendedHistory x v.1.val v.1.property.1
          (PublicDiscreteDraws.followerPlayer p.two_le_m
            (ActualReferenceInitializationBlock.refFollower i))) n hbefore}

/-- The processed inactive projection retains the actual absence selector. -/
abbrev InactiveProjection (p : ConstructorDimensions.Parameters)
    (i : Fin (p.m - 1)) (n : ℕ) (_hn : n ≤ p.T)
    (x : ReferenceInitializationRun.Input p)
    (s : Fin (n_boot p)) :=
  {v : ProcessedBoundary x s × LocalHistory p n //
    ∃ hbefore : n ≤ ReferenceInitializationRun.elapsed p (v.1.val.completed + 1),
      v.1.val.activation (ActualReferenceInitializationBlock.refFollower i) = none ∧
      v.2 = ReferencePrelaunchLifecycleReplay.prefixHistory
        (ReferenceInitializationRun.extendedHistory x v.1.val v.1.property.1
          (PublicDiscreteDraws.followerPlayer p.two_le_m
            (ActualReferenceInitializationBlock.refFollower i))) n hbefore}

/-- The stopped projection retains the actual crossing selector. -/
abbrev StoppedProjection (p : ConstructorDimensions.Parameters)
    (x : ReferenceInitializationRun.Input p) (s : Fin (n_boot p))
    (i : Fin (p.m - 1)) :=
  {v : ReferenceInitializationRun.Boundary p × State p x.eta //
    v.1.crossing ≠ none ∧
      v.1 = ReferenceInitializationRun.run x s.val ∧
      v.2 = ReferenceInitializationRun.ordinary x v.1
        (ActualReferenceInitializationBlock.refFollower i)}

/-- Existing active, inactive, or stopped projections, with actual selectors. -/
abbrev PrefixAt (p : ConstructorDimensions.Parameters)
    (i : Fin (p.m - 1)) (n : ℕ) (row : CompletePublicTable.CompleteRow p)
    (hn : n ≤ p.T) (x : ReferenceInitializationRun.Input p) (s : Fin (n_boot p)) :=
  Sum
    (Sum
      (ActiveProjection p i n row hn x s)
      (InactiveProjection p i n hn x s))
      (StoppedProjection p x s i)

/-- Proof-erased view retaining the actual boundary, history, activation and state. -/
abbrev PrefixObservation (p : ConstructorDimensions.Parameters) (eta : LearningRate)
    (_i : Fin (p.m - 1)) (n : ℕ) :=
  Sum
    (Sum
      (ReferenceInitializationRun.Boundary p × Activation p × LocalHistory p n × State p eta)
      (ReferenceInitializationRun.Boundary p × LocalHistory p n))
    (ReferenceInitializationRun.Boundary p × State p eta)

/-- Forget only proof fields carried by the generated selectors. -/
def forgetPrefixProofs {p : ConstructorDimensions.Parameters}
    {i : Fin (p.m - 1)} {n : ℕ} {row : CompletePublicTable.CompleteRow p}
    {hn : n ≤ p.T} {x : ReferenceInitializationRun.Input p} {s : Fin (n_boot p)} :
    PrefixAt p i n row hn x s → PrefixObservation p x.eta i n
  | .inl (.inl active) =>
      .inl (.inl (active.val.1.val, active.val.2.1, active.val.2.2.1,
        active.val.2.2.2))
  | .inl (.inr inactive) => .inl (.inr (inactive.val.1.val, inactive.val.2))
  | .inr stopped => .inr stopped.val

/-- Original generated reference input retaining the full selected row and private arrays. -/
def sourceReferenceInput (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p) :
    ReferenceInitializationRun.Input p :=
  ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate

/-- Actual prefix at `r`: processed history is cut strictly before `r`; crossing
uses the stopped ordinary projection and has no current prelaunch test. -/
def source_prelaunch_down_prefix
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (r : Fin p.T) :
    PrefixAt p i r.val
      (sourceReferenceInput rate rewards C_star C_h z).row (Nat.le_of_lt r.isLt)
      (sourceReferenceInput rate rewards C_star C_h z) (roundBlockIndex p r) := by
  classical
  let x := ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate
  let s := roundBlockIndex p r
  let b := ReferenceInitializationRun.run x s.val
  let f := ActualReferenceInitializationBlock.refFollower i
  by_cases hc : b.crossing = none
  · have hcompleted : b.completed = s.val := by
      change (ReferenceInitializationRun.run
        (GeneratedBootstrapRoundLaw.input p x.ids x.rewards x.C_star x.C_h x.eta
          (x.row, x.coordinates)) s.val).completed = s.val
      exact GeneratedBootstrapRoundLaw.processed_completed x.ids x.rewards
        x.C_star x.C_h x.eta s (x.row, x.coordinates) hc
    have hremain : b.completed < n_boot p := by
      rw [hcompleted]
      exact s.isLt
    have hcalendar : r ∈ calendarBlock p s :=
      round_mem_quotient_block p r
    have hbefore : r.val ≤ ReferenceInitializationRun.elapsed p (b.completed + 1) := by
      have hr := (mem_calendarBlock_iff p s r).mp hcalendar
      have hr' : r.val < ReferenceInitializationRun.elapsed p (s.val + 1) := by
        simpa only [ReferenceInitializationRun.elapsed] using hr.2
      rw [hcompleted]
      exact hr'.le
    let full := ReferenceInitializationRun.extendedHistory x b hremain
      (PublicDiscreteDraws.followerPlayer p.two_le_m f)
    let history := ReferencePrelaunchLifecycleReplay.prefixHistory full r.val hbefore
    cases ha : b.activation f with
    | none =>
        exact Sum.inl (Sum.inr ⟨(⟨b, ⟨hremain, hc, rfl⟩⟩, history),
          ⟨hbefore, ha, rfl⟩⟩)
    | some a =>
        exact Sum.inl (Sum.inl ⟨(⟨b, ⟨hremain, hc, rfl⟩⟩, a, history,
          ReferencePrelaunchFollower.replay rate.eta i x.row a history
            (Nat.le_of_lt r.isLt)), ⟨hbefore, ha, rfl, rfl⟩⟩)
  · exact Sum.inr ⟨(b, ReferenceInitializationRun.ordinary x b f), ⟨hc, rfl, rfl⟩⟩

/-- The generated prefix with selector proofs erased but every data projection
retained, for comparison across original inputs. -/
def source_prelaunch_down_prefix_observation
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (r : Fin p.T) : PrefixObservation p rate.eta i r.val :=
  forgetPrefixProofs (source_prelaunch_down_prefix rate rewards C_star C_h z i r)

/-- Chronological prelaunch tests before `r`, using `C.prelaunchTest` on the
actual strict history or the actual stopped boundary census. -/
def source_prelaunch_down_prefix_tests
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (r : Fin p.T) :
    List (ReferenceGeneratedDownBatchCalendar.ExecutedTest p) := by
  classical
  let x := sourceReferenceInput rate rewards C_star C_h z
  exact match source_prelaunch_down_prefix rate rewards C_star C_h z i r with
  | .inl (.inl active) =>
      let a := active.val.2.1
      let history := active.val.2.2.1
      (List.ofFn (fun u : Fin r.val => u)).filterMap (fun u =>
        ReferenceGeneratedPrelaunchDownCohort.prelaunchTest i x.row a
          (ReferencePrelaunchFollower.calendar (Nat.le_of_lt r.isLt) u) (history u))
  | .inl (.inr _) => []
  | .inr stopped =>
      let b := stopped.val.1
      ReferenceGeneratedPrelaunchDownCohort.boundaryPrelaunchDownTests x b i

/-- Current physical test on a processed active branch; stopped or undeclared
branches have no current prelaunch test. -/
def source_prelaunch_down_current_test
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (r : Fin p.T) :
    Option (ReferenceGeneratedDownBatchCalendar.ExecutedTest p) := by
  classical
  let x := sourceReferenceInput rate rewards C_star C_h z
  exact match source_prelaunch_down_prefix rate rewards C_star C_h z i r with
  | .inl (.inl active) =>
      let bsub := active.val.1
      let a := active.val.2.1
      let b := bsub.val
      let h := bsub.property.1
      ReferenceGeneratedPrelaunchDownCohort.prelaunchTest i x.row a r
        (ReferenceInitializationRun.ownEntry
          (ReferenceInitializationRun.physical x b h)
          (PublicDiscreteDraws.followerPlayer p.two_le_m
            (ActualReferenceInitializationBlock.refFollower i)) r)
  | .inl (.inr _) => none
  | .inr _ => none

/-- Chronological sent-word and affine-hash flags for each collected test. -/
def source_prelaunch_down_prefix_flags
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (r : Fin p.T)
    (w : AffineChannelLaw.Word (AffineBatchDecoder.width p)) :
    List (Prop × Prop) :=
  (source_prelaunch_down_prefix_tests rate rewards C_star C_h z i r).map
    (fun test =>
      (test.sent ≠ some w,
        AffineChannelLaw.affineHash test.sample w = 1))

/-- Current bank birth: activation minus one initially, otherwise one after the
previous completed batch's actual last test. Missing entries remain `none`. -/
def bankBirth (activation : Activation p)
    (bank : AffineBatchDecoder.State p.T (AffineBatchDecoder.width p)) : Option ℕ :=
  if bank.completed.isEmpty then some (activation.val - 1)
  else
    (bank.completed.getLast?).bind List.getLast? |>.map (fun entry => entry.time.val + 1)

/-- The source-computed birth at the strict prefix before round `r`. -/
def source_prelaunch_down_prefix_birth
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (r : Fin p.T) : Option ℕ := by
  classical
  exact match source_prelaunch_down_prefix rate rewards C_star C_h z i r with
  | .inl (.inl active) => bankBirth active.val.2.1 active.val.2.2.2.downBatch
  | .inl (.inr _) => none
  | .inr stopped =>
      let b := stopped.val.1
      let ordinary := stopped.val.2
      (b.activation (ActualReferenceInitializationBlock.refFollower i)).bind
        (fun a => bankBirth a ordinary.downBatch)

/-- Actual empty-bank birth at `alpha`, read from that prefix or terminal
boundary. No later completion, launch selection, or solver result is required. -/
def birthAt
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (alpha : ℕ) (_hα : alpha ≤ p.T) (k : ℕ) : Prop := by
  classical
  exact if h : alpha < p.T then
    match source_prelaunch_down_prefix rate rewards C_star C_h z i ⟨alpha, h⟩ with
    | .inl (.inl active) =>
          active.val.2.2.2.downBatch.completed.length = k ∧
            active.val.2.2.2.downBatch.pending =
              ([] : List (AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p))) ∧
            bankBirth active.val.2.1 active.val.2.2.2.downBatch = some alpha
    | .inl (.inr _) => False
    | .inr stopped =>
        let b := stopped.val.1
        let ordinary := stopped.val.2
        ∃ a, b.activation (ActualReferenceInitializationBlock.refFollower i) = some a ∧
          ordinary.downBatch.completed.length = k ∧
            ordinary.downBatch.pending =
              ([] : List (AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p))) ∧
          bankBirth a ordinary.downBatch = some alpha
  else
    let x := sourceReferenceInput rate rewards C_star C_h z
    let b := ReferenceInitializationRun.output x
    let ordinary := ReferenceInitializationRun.ordinary x b
      (ActualReferenceInitializationBlock.refFollower i)
    ∃ a, b.activation (ActualReferenceInitializationBlock.refFollower i) = some a ∧
      ordinary.downBatch.completed.length = k ∧
        ordinary.downBatch.pending =
          ([] : List (AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p))) ∧
      bankBirth a ordinary.downBatch = some alpha

/-- Candidate flags for the pending cohort, excluding completed cohorts. -/
def source_prelaunch_down_current_cohort_flags
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (r : Fin p.T)
    (w : AffineChannelLaw.Word (AffineBatchDecoder.width p)) : List (Prop × Prop) := by
  classical
  let flags := source_prelaunch_down_prefix_flags rate rewards C_star C_h z i r w
  exact match source_prelaunch_down_prefix rate rewards C_star C_h z i r with
  | .inl (.inl active) =>
      flags.drop (AffineBatchDecoder.quota p * active.val.2.2.2.downBatch.completed.length)
  | .inl (.inr _) => []
  | .inr stopped =>
      let ordinary := stopped.val.2
      flags.drop (AffineBatchDecoder.quota p * ordinary.downBatch.completed.length)

/-- Strict-past DOWN indicator requiring the actual birth, active tag, ordinal,
`ell - 1` pending entries, and candidate flags for preceding entries. The
current test remains the separate `source_prelaunch_down_current_test`. -/
def source_prelaunch_down_past_indicator
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (alpha k ell : ℕ) (hα : alpha ≤ p.T)
    (r : Fin p.T)
    (w : AffineChannelLaw.Word (AffineBatchDecoder.width p)) : Prop := by
  classical
  exact 1 ≤ ell ∧ ell ≤ AffineBatchDecoder.quota p ∧ alpha ≤ r.val ∧
    birthAt rate rewards C_star C_h z i alpha hα k ∧
    match source_prelaunch_down_prefix rate rewards C_star C_h z i r with
    | .inl (.inl active) =>
        let activation := active.val.2.1
        let bank := active.val.2.2.2.downBatch
        bank.completed.length = k ∧ bankBirth activation bank = some alpha ∧
          bank.pending.length = ell - 1 ∧
          List.Forall (fun flags => flags.1 ∧ flags.2)
            (source_prelaunch_down_current_cohort_flags rate rewards C_star C_h z i r w)
    | .inl (.inr _) => False
    | .inr _ => False

private theorem test_entries (i : Fin (p.m - 1))
    (row : CompletePublicTable.CompleteRow p) (a : Activation p)
    (t : Fin p.T) (own : Fin p.K × Observation p) :
    ((ReferenceGeneratedPrelaunchDownCohort.prelaunchTest i row a t own).toList.map
        ReferenceGeneratedPrelaunchDownCohort.testEntry) =
      AffineBatchDecoder.positiveAt p (ReferencePrelaunchFollower.traceAt i row a t own) t := by
  by_cases h : (ReferencePrelaunchFollower.downInput i row a t own).selected = true ∧
      0 < own.2.val.val
  · have he : AffineBatchDecoder.eligible
        (ReferencePrelaunchFollower.traceAt i row a t own t) := ⟨h.1, rfl, h.2⟩
    rw [ReferenceGeneratedPrelaunchDownCohort.prelaunchTest,
      ite_eq_left h, AffineBatchDecoder.positiveAt, ite_eq_left he]
    rfl
  · have he : ¬ AffineBatchDecoder.eligible
        (ReferencePrelaunchFollower.traceAt i row a t own t) := by
      intro he
      exact h ⟨he.1, he.2.2⟩
    simp only [ReferenceGeneratedPrelaunchDownCohort.prelaunchTest, h, ↓reduceIte,
      Option.toList_none, List.map_nil, AffineBatchDecoder.positiveAt, he]

private theorem tests_entries (i : Fin (p.m - 1))
    (row : CompletePublicTable.CompleteRow p) (a : Activation p)
    {n : ℕ} (history : LocalHistory p n) (hn : n ≤ p.T) (us : List (Fin n)) :
    (us.filterMap (fun u => ReferenceGeneratedPrelaunchDownCohort.prelaunchTest i row a
      (ReferencePrelaunchFollower.calendar hn u) (history u))).map
        ReferenceGeneratedPrelaunchDownCohort.testEntry =
      us.flatMap (fun u => AffineBatchDecoder.positiveAt p
        (ReferencePrelaunchFollower.traceAt i row a
          (ReferencePrelaunchFollower.calendar hn u) (history u))
          (ReferencePrelaunchFollower.calendar hn u)) := by
  induction us with
  | nil => rfl
  | cons u us ih =>
      rw [List.filterMap_cons, List.flatMap_cons]
      cases h : ReferenceGeneratedPrelaunchDownCohort.prelaunchTest i row a
          (ReferencePrelaunchFollower.calendar hn u) (history u) with
      | none =>
          have he := test_entries i row a (ReferencePrelaunchFollower.calendar hn u)
            (history u)
          simp only [h, Option.toList_none, List.map_nil] at he
          simp only [List.nil_append, ← he, ih]
      | some test =>
          have he := test_entries i row a (ReferencePrelaunchFollower.calendar hn u)
            (history u)
          simp only [h, Option.toList_some, List.map_cons, List.map_nil] at he
          simp only [List.map_cons, List.singleton_append, ← he, ih]

private theorem completed_slice
    (batches : List (List (AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p))))
    (pending : List (AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p)))
    (hall : ∀ batch ∈ batches, batch.length = AffineBatchDecoder.quota p) :
    (batches.flatten ++ pending).drop (AffineBatchDecoder.quota p * batches.length) = pending ∧
      ∀ k (hk : k < batches.length),
        ((batches.flatten ++ pending).drop (k * AffineBatchDecoder.quota p)).take
          (AffineBatchDecoder.quota p) = batches[k] := by
  induction batches with
  | nil => exact ⟨rfl, fun k hk => (Nat.not_lt_zero k hk).elim⟩
  | cons batch batches ih =>
      have hb := hall batch List.mem_cons_self
      have ht := ih (fun c hc => hall c (List.mem_cons_of_mem _ hc))
      constructor
      · rw [List.length_cons, Nat.mul_succ, Nat.add_comm, List.flatten_cons,
          List.append_assoc, ← hb, ← List.drop_drop, List.drop_left, hb]
        exact ht.1
      · intro k hk
        cases k with
        | zero =>
            simp only [Nat.zero_mul, List.drop_zero, List.flatten_cons,
              List.append_assoc, List.getElem_cons_zero]
            rw [← hb, List.take_left]
        | succ k =>
            simp only [List.length_cons] at hk
            rw [Nat.succ_mul, Nat.add_comm, List.flatten_cons, List.append_assoc,
              ← hb, ← List.drop_drop, List.drop_left, hb, List.getElem_cons_succ]
            exact ht.2 k (by omega)

private theorem boundary_test_census (x : ReferenceInitializationRun.Input p)
    (b : ReferenceInitializationRun.Boundary p) (i : Fin (p.m - 1)) :
    let bank := (ReferenceInitializationRun.ordinary x b
      (ActualReferenceInitializationBlock.refFollower i)).downBatch
    (ReferenceGeneratedPrelaunchDownCohort.boundaryPrelaunchDownTests x b i).map
        ReferenceGeneratedPrelaunchDownCohort.testEntry =
        AffineBatchDecoder.collected bank ∧
      bank.pending.length < AffineBatchDecoder.quota p ∧
      ∀ batch ∈ bank.completed, batch.length = AffineBatchDecoder.quota p := by
  dsimp only
  dsimp only [ReferenceGeneratedPrelaunchDownCohort.boundaryPrelaunchDownTests]
  unfold ReferenceInitializationRun.ordinary
  split_ifs with hf
  · exact ⟨rfl, AffineBatchDecoder.quota_pos p, by
      simp only [ReferencePrelaunchFollower.forcedAtLaunch,
        ReferencePrelaunchFollower.initial, AffineBatchDecoder.initial,
        List.not_mem_nil, false_implies, implies_true]⟩
  · cases ha : b.activation (ActualReferenceInitializationBlock.refFollower i) with
    | none => exact ⟨rfl, AffineBatchDecoder.quota_pos p, by
        simp only [ReferencePrelaunchFollower.initial, AffineBatchDecoder.initial,
          List.not_mem_nil, false_implies, implies_true]⟩
    | some a =>
        have hs := ReferencePrelaunchFollower.replay_batch_spec x.eta i x.row a
          (b.history (PublicDiscreteDraws.followerPlayer p.two_le_m
            (ActualReferenceInitializationBlock.refFollower i)))
          (ReferenceInitializationRun.elapsed_le_T p b.completed)
        refine ⟨?_, hs.1, hs.2.1⟩
        exact tests_entries i x.row a _ _ _ |>.trans hs.2.2.symm

private theorem localCoordinates_comparison
    (x y : ReferenceInitializationRun.Input p)
    (b : ReferenceInitializationRun.Boundary p) (h : b.completed < n_boot p)
    (k : ℕ)
    (hids : x.ids = y.ids) (hrew : x.rewards = y.rewards)
    (hdraw : ∀ j : Fin (p.m - 1),
      x.coordinates.1.1 (ReferenceInitializationRun.nextBlock b h) j =
        y.coordinates.1.1 (ReferenceInitializationRun.nextBlock b h) j)
    (htarget : x.coordinates.2.2 (ReferenceInitializationRun.nextBlock b h) =
      y.coordinates.2.2 (ReferenceInitializationRun.nextBlock b h))
    (hrow : ∀ u : Fin (A_id p), ∀ q : Fin p.T, q.val < k →
      x.row.1 u q = y.row.1 u q)
    (hlearning : ∀ q : Fin p.T, q.val < k → x.row.2 q = y.row.2 q)
    (hround : ∀ i : Fin p.m, ∀ q : Fin p.T, q.val < k →
      x.coordinates.2.1 (i, q) = y.coordinates.2.1 (i, q)) :
    ∃ w : BootstrapBlockCausality.LocalCoordinates p
        (ReferenceInitializationRun.uninformed b)
        (ReferenceInitializationRun.physical x b h).held
        (ReferenceInitializationRun.physical x b h).target,
      BootstrapBlockCausality.blockInput (s := ReferenceInitializationRun.nextBlock b h)
        (ReferenceInitializationRun.uninformed b)
        (ReferenceInitializationRun.physical x b h).active
        (ReferenceInitializationRun.physical x b h).held
        (ReferenceInitializationRun.physical x b h).privateId
        (ReferenceInitializationRun.physical x b h).ids
        (ReferenceInitializationRun.physical x b h).target
        (ReferenceInitializationRun.physical x b h).rewards w =
          ReferenceInitializationRun.physical y b h ∧
      ∀ q : Fin p.T, q.val < k →
        BootstrapBlockCausality.roundCoordinatesEq
          (ReferenceInitializationRun.uninformed b)
          (ReferenceInitializationRun.physical x b h).held
          (ReferenceInitializationRun.physical x b h).target
          (ReferenceInitializationRun.localCoordinates x b h) w q := by
  let vx := ReferenceInitializationRun.physical x b h
  let vy := ReferenceInitializationRun.physical y b h
  have hdrawProfile : ∀ j : {j // j ∈ ReferenceInitializationRun.uninformed b},
      (vx.active j, vx.held j, vx.privateId j) =
        (vy.active j, vy.held j, vy.privateId j) := by
    intro j
    calc
      (vx.active j, vx.held j, vx.privateId j) =
          PrivateSourceStreams.blockDrawProfileMap p b.numerators b.weight_ge_one
            (x.coordinates.1.1 (ReferenceInitializationRun.nextBlock b h))
            (BootstrapPhysicalInput.sourceFollowerIndex p j.1) :=
        ReferenceInitializationRun.physical_own_block_draw x b h j
      _ = PrivateSourceStreams.blockDrawProfileMap p b.numerators b.weight_ge_one
            (y.coordinates.1.1 (ReferenceInitializationRun.nextBlock b h))
            (BootstrapPhysicalInput.sourceFollowerIndex p j.1) := by
        simpa only [BootstrapPhysicalInput.currentBlockDrawProfile] using
          (BootstrapPhysicalInput.incoming_blockDraw_eq_of_own_triple_eq p
            (ReferenceInitializationRun.nextBlock b h)
            (ReferenceInitializationRun.uninformed b) b.numerators b.weight_ge_one
            x.coordinates y.coordinates j
            (hdraw (BootstrapPhysicalInput.sourceFollowerIndex p j.1)))
      _ = (vy.active j, vy.held j, vy.privateId j) :=
        (ReferenceInitializationRun.physical_own_block_draw y b h j).symm
  have hactive : vx.active = vy.active := by
    funext j
    exact congrArg Prod.fst (hdrawProfile j)
  have hheld : vx.held = vy.held := by
    funext j
    exact congrArg (fun z => z.2.1) (hdrawProfile j)
  have hprivateId : vx.privateId = vy.privateId := by
    funext j
    exact congrArg (fun z => z.2.2) (hdrawProfile j)
  have htargetArm : vx.target = vy.target := by
    change BootstrapPhysicalInput.targetArmMap p
      (ReferenceInitializationRun.nextBlock b h) x.coordinates =
        BootstrapPhysicalInput.targetArmMap p
          (ReferenceInitializationRun.nextBlock b h) y.coordinates
    exact BootstrapPhysicalInput.targetArmMap_eq_of_target_scalar_eq p
      (ReferenceInitializationRun.nextBlock b h) x.coordinates y.coordinates htarget
  let w : BootstrapBlockCausality.LocalCoordinates p
      (ReferenceInitializationRun.uninformed b) vx.held vx.target :=
    (y.row, (vy.uniform,
      (fun q => ⟨(vy.coordinatorAvoid q).val, by
          simpa only [htargetArm] using (vy.coordinatorAvoid q).property⟩,
        fun j q => ⟨(vy.followerAvoid j q).val, by
          simpa only [congrFun hheld j] using (vy.followerAvoid j q).property⟩)))
  have hroundCoordinates : ∀ q : Fin p.T, q.val < k →
      BootstrapBlockCausality.roundCoordinatesEq (ReferenceInitializationRun.uninformed b)
        vx.held vx.target (ReferenceInitializationRun.localCoordinates x b h) w q := by
    intro q hq
    dsimp only [BootstrapBlockCausality.roundCoordinatesEq,
      ReferenceInitializationRun.localCoordinates, w]
    have hrowq : ∀ u : Fin (A_id p), x.row.1 u q = y.row.1 u q :=
      fun u => hrow u q hq
    have hlearningq := hlearning q hq
    refine ⟨hrowq, hlearningq, ?_, ?_, ?_⟩
    · intro i
      change BootstrapPrivateRoundStreams.fullArmScalarDraw p
        (BootstrapPhysicalInput.playerRoundScalarAt p x.coordinates i q) =
          BootstrapPrivateRoundStreams.fullArmScalarDraw p
            (BootstrapPhysicalInput.playerRoundScalarAt p y.coordinates i q)
      exact congrArg (BootstrapPrivateRoundStreams.fullArmScalarDraw p)
        (hround i q hq)
    · apply Subtype.ext
      change BootstrapPhysicalInput.coordinatorAvoidArmValueMap p
        (ReferenceInitializationRun.nextBlock b h) x.coordinates q =
          BootstrapPhysicalInput.coordinatorAvoidArmValueMap p
            (ReferenceInitializationRun.nextBlock b h) y.coordinates q
      rcases BootstrapPhysicalInput.coordinator_roundDraws_eq_of_own_coordinates_eq
          p (ReferenceInitializationRun.nextBlock b h) x.coordinates y.coordinates q
          htarget (hround (ActiveRoundActions.coordinator p.two_le_m) q hq)
        with ⟨_, _, havoid⟩
      exact havoid
    · intro j
      apply Subtype.ext
      change BootstrapPhysicalInput.followerAvoidArmValueMap p
        (ReferenceInitializationRun.nextBlock b h) (ReferenceInitializationRun.uninformed b)
        b.numerators b.weight_ge_one x.coordinates j q =
          BootstrapPhysicalInput.followerAvoidArmValueMap p
            (ReferenceInitializationRun.nextBlock b h)
            (ReferenceInitializationRun.uninformed b) b.numerators b.weight_ge_one
            y.coordinates j q
      have htriple : x.coordinates.1.1 (ReferenceInitializationRun.nextBlock b h)
          (BootstrapPhysicalInput.sourceFollowerIndex p j.1) =
            y.coordinates.1.1 (ReferenceInitializationRun.nextBlock b h)
              (BootstrapPhysicalInput.sourceFollowerIndex p j.1) :=
        hdraw (BootstrapPhysicalInput.sourceFollowerIndex p j.1)
      rcases BootstrapPhysicalInput.follower_roundDraws_eq_of_own_coordinates_eq
          p (ReferenceInitializationRun.nextBlock b h)
          (ReferenceInitializationRun.uninformed b) b.numerators b.weight_ge_one
          x.coordinates y.coordinates j q htriple
          (hround (PublicDiscreteDraws.followerPlayer p.two_le_m j.1) q hq)
        with ⟨_, havoid⟩
      exact havoid
  have hinputW : BootstrapBlockCausality.blockInput
      (s := ReferenceInitializationRun.nextBlock b h)
      (ReferenceInitializationRun.uninformed b) vx.active vx.held vx.privateId
      vx.ids vx.target vx.rewards w = vy := by
    simp only [vy, ReferenceInitializationRun.physical, BootstrapPhysicalInput.blockInput,
      BootstrapBlockCausality.blockInput, BootstrapBlockCausality.inputOf]
    congr 1
    all_goals simp [w]
    case e_11 =>
      apply Function.hfunext rfl
      intro q q' hq
      cases hq
      exact (Subtype.heq_iff_coe_eq (by
        intro a
        exact (congrArg (fun z => a ≠ z) htargetArm).to_iff)).2 rfl
    case e_12 =>
      apply Function.hfunext rfl
      intro j j' hj
      cases hj
      apply Function.hfunext rfl
      intro q q' hq
      cases hq
      exact (Subtype.heq_iff_coe_eq (by
        intro a
        exact (congrArg (fun z => a ≠ z) (congrFun hheld j)).to_iff)).2 rfl
  exact ⟨w, hinputW, hroundCoordinates⟩

private theorem physical_ownEntry_eq_of_actual_past
    (x y : ReferenceInitializationRun.Input p)
    (b : ReferenceInitializationRun.Boundary p) (h : b.completed < n_boot p)
    (hids : x.ids = y.ids) (hrew : x.rewards = y.rewards)
    (hdraw : ∀ j : Fin (p.m - 1),
      x.coordinates.1.1 (ReferenceInitializationRun.nextBlock b h) j =
        y.coordinates.1.1 (ReferenceInitializationRun.nextBlock b h) j)
    (htarget : x.coordinates.2.2 (ReferenceInitializationRun.nextBlock b h) =
      y.coordinates.2.2 (ReferenceInitializationRun.nextBlock b h))
    (t : Fin p.T)
    (hrow : ∀ u : Fin (A_id p), ∀ q : Fin p.T, q.val ≤ t.val →
      x.row.1 u q = y.row.1 u q)
    (hlearning : ∀ q : Fin p.T, q.val ≤ t.val → x.row.2 q = y.row.2 q)
    (hround : ∀ i : Fin p.m, ∀ q : Fin p.T, q.val ≤ t.val →
      x.coordinates.2.1 (i, q) = y.coordinates.2.1 (i, q))
    (player : Fin p.m) :
    ReferenceInitializationRun.ownEntry (ReferenceInitializationRun.physical x b h) player t =
      ReferenceInitializationRun.ownEntry (ReferenceInitializationRun.physical y b h) player t := by
  have hstate := ReferenceInitializationCausality.physical_prechoice_eq_of_actual_past
    x y b h hids hrew hdraw htarget t
    (fun u q hq => hrow u q (Nat.le_of_lt hq))
    (fun q hq => hlearning q (Nat.le_of_lt hq))
    (fun j q hq => hround j q (Nat.le_of_lt hq))
  obtain ⟨w, hinputW, hcoords⟩ := localCoordinates_comparison x y b h
    (t.val + 1) hids hrew hdraw htarget
    (fun u q hq => hrow u q (by omega))
    (fun q hq => hlearning q (by omega))
    (fun j q hq => hround j q (by omega))
  have hcoord := hcoords t (by omega)
  have hactions := BootstrapBlockCausality.actions_eq_of_roundCoordinatesEq
    (s := ReferenceInitializationRun.nextBlock b h)
    (ReferenceInitializationRun.uninformed b)
    (ReferenceInitializationRun.physical x b h).active
    (ReferenceInitializationRun.physical x b h).held
    (ReferenceInitializationRun.physical x b h).privateId
    (ReferenceInitializationRun.physical x b h).ids
    (ReferenceInitializationRun.physical x b h).target
    (ReferenceInitializationRun.physical x b h).rewards
    (ReferenceInitializationRun.localCoordinates x b h) w
    (BootstrapPhysicalBlock.run (ReferenceInitializationRun.physical x b h) t.val) t hcoord
  have hfeedback := BootstrapBlockCausality.feedback_eq_of_roundCoordinatesEq
    (s := ReferenceInitializationRun.nextBlock b h)
    (ReferenceInitializationRun.uninformed b)
    (ReferenceInitializationRun.physical x b h).active
    (ReferenceInitializationRun.physical x b h).held
    (ReferenceInitializationRun.physical x b h).privateId
    (ReferenceInitializationRun.physical x b h).ids
    (ReferenceInitializationRun.physical x b h).target
    (ReferenceInitializationRun.physical x b h).rewards
    (ReferenceInitializationRun.localCoordinates x b h) w
    (BootstrapPhysicalBlock.run (ReferenceInitializationRun.physical x b h) t.val) t player hcoord
  have hactions' :
      BootstrapPhysicalBlock.actions (ReferenceInitializationRun.physical x b h)
          (BootstrapPhysicalBlock.run (ReferenceInitializationRun.physical x b h) t.val) t =
        BootstrapPhysicalBlock.actions (ReferenceInitializationRun.physical y b h)
          (BootstrapPhysicalBlock.run (ReferenceInitializationRun.physical y b h) t.val) t := by
    calc
      _ = BootstrapPhysicalBlock.actions
          (BootstrapBlockCausality.blockInput
            (s := ReferenceInitializationRun.nextBlock b h)
            (ReferenceInitializationRun.uninformed b)
            (ReferenceInitializationRun.physical x b h).active
            (ReferenceInitializationRun.physical x b h).held
            (ReferenceInitializationRun.physical x b h).privateId
            (ReferenceInitializationRun.physical x b h).ids
            (ReferenceInitializationRun.physical x b h).target
            (ReferenceInitializationRun.physical x b h).rewards w)
          (BootstrapPhysicalBlock.run (ReferenceInitializationRun.physical x b h) t.val) t := by
            simpa only [ReferenceInitializationRun.physical, BootstrapPhysicalInput.blockInput,
              BootstrapBlockCausality.blockInput, BootstrapBlockCausality.inputOf,
              ReferenceInitializationRun.localCoordinates] using hactions
      _ = BootstrapPhysicalBlock.actions (ReferenceInitializationRun.physical y b h)
          (BootstrapPhysicalBlock.run (ReferenceInitializationRun.physical x b h) t.val) t := by
            rw [hinputW]
      _ = BootstrapPhysicalBlock.actions (ReferenceInitializationRun.physical y b h)
          (BootstrapPhysicalBlock.run (ReferenceInitializationRun.physical y b h) t.val) t := by
            rw [hstate]
  have hfeedback' :
      BootstrapPhysicalBlock.feedback (ReferenceInitializationRun.physical x b h)
          (BootstrapPhysicalBlock.run (ReferenceInitializationRun.physical x b h) t.val) t player =
        BootstrapPhysicalBlock.feedback (ReferenceInitializationRun.physical y b h)
          (BootstrapPhysicalBlock.run (ReferenceInitializationRun.physical y b h) t.val) t player := by
    calc
      _ = BootstrapPhysicalBlock.feedback
          (BootstrapBlockCausality.blockInput
            (s := ReferenceInitializationRun.nextBlock b h)
            (ReferenceInitializationRun.uninformed b)
            (ReferenceInitializationRun.physical x b h).active
            (ReferenceInitializationRun.physical x b h).held
            (ReferenceInitializationRun.physical x b h).privateId
            (ReferenceInitializationRun.physical x b h).ids
            (ReferenceInitializationRun.physical x b h).target
            (ReferenceInitializationRun.physical x b h).rewards w)
          (BootstrapPhysicalBlock.run (ReferenceInitializationRun.physical x b h) t.val) t player := by
            simpa only [ReferenceInitializationRun.physical, BootstrapPhysicalInput.blockInput,
              BootstrapBlockCausality.blockInput, BootstrapBlockCausality.inputOf,
              ReferenceInitializationRun.localCoordinates] using hfeedback
      _ = BootstrapPhysicalBlock.feedback (ReferenceInitializationRun.physical y b h)
          (BootstrapPhysicalBlock.run (ReferenceInitializationRun.physical x b h) t.val) t player := by
            rw [hinputW]
      _ = BootstrapPhysicalBlock.feedback (ReferenceInitializationRun.physical y b h)
          (BootstrapPhysicalBlock.run (ReferenceInitializationRun.physical y b h) t.val) t player := by
            rw [hstate]
  have hobs :
      ReferenceInitializationRun.ownObservation (ReferenceInitializationRun.physical x b h) player t =
        ReferenceInitializationRun.ownObservation (ReferenceInitializationRun.physical y b h) player t := by
    unfold ReferenceInitializationRun.ownObservation
    apply Subtype.ext
    apply Subtype.ext
    exact hfeedback'
  change (BootstrapPhysicalBlock.actions (ReferenceInitializationRun.physical x b h)
      (BootstrapPhysicalBlock.run (ReferenceInitializationRun.physical x b h) t.val) t player,
      ReferenceInitializationRun.ownObservation (ReferenceInitializationRun.physical x b h) player t) =
    (BootstrapPhysicalBlock.actions (ReferenceInitializationRun.physical y b h)
      (BootstrapPhysicalBlock.run (ReferenceInitializationRun.physical y b h) t.val) t player,
      ReferenceInitializationRun.ownObservation (ReferenceInitializationRun.physical y b h) player t)
  exact Prod.ext (congrArg (fun actions => actions player) hactions') hobs

private theorem source_past_round_reads
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (z z' : BootstrapPrivateRoundStreams.SourceInput p) (r t : Fin p.T)
    (hpast : GeneratedBootstrapRoundLaw.past p r
        (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z), z.2) =
      GeneratedBootstrapRoundLaw.past p r
        (z'.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z'), z'.2))
    (ht : t.val < r.val) :
    (∀ arm : Fin (A_id p),
      (sourceReferenceInput rate rewards C_star C_h z).row.1 arm t =
        (sourceReferenceInput rate rewards C_star C_h z').row.1 arm t) ∧
      (sourceReferenceInput rate rewards C_star C_h z).row.2 t =
        (sourceReferenceInput rate rewards C_star C_h z').row.2 t ∧
      (∀ player : Fin p.m,
        (sourceReferenceInput rate rewards C_star C_h z).coordinates.2.1 (player, t) =
          (sourceReferenceInput rate rewards C_star C_h z').coordinates.2.1 (player, t)) := by
  let x := sourceReferenceInput rate rewards C_star C_h z
  let y := sourceReferenceInput rate rewards C_star C_h z'
  have he := congrArg (fun w : GeneratedBootstrapRoundLaw.Past p r => w.1 ⟨t, ht⟩) hpast
  refine ⟨?_, ?_, ?_⟩
  · intro arm
    change (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)).1 arm t =
      (z'.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z')).1 arm t
    exact congrArg (fun entry => entry.1 arm) he
  · change (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)).2 t =
      (z'.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z')).2 t
    exact congrArg Prod.snd he
  · intro player
    exact congrArg (fun w : GeneratedBootstrapRoundLaw.Past p r =>
      w.2.2.1 ⟨⟨(player, t), ht.le⟩, ht⟩) hpast

private theorem source_past_block_reads
    (z z' : BootstrapPrivateRoundStreams.SourceInput p) (r : Fin p.T)
    (hpast : GeneratedBootstrapRoundLaw.past p r
        (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z), z.2) =
      GeneratedBootstrapRoundLaw.past p r
        (z'.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z'), z'.2))
    (s : Fin (n_boot p)) :
    (∀ j : Fin (p.m - 1), z.2.1.1 s j = z'.2.1.1 s j) ∧
      z.2.2.2 s = z'.2.2.2 s := by
  refine ⟨?_, ?_⟩
  · intro j
    exact congrArg (fun w : GeneratedBootstrapRoundLaw.Past p r => w.2.1.1 s j) hpast
  · exact congrArg (fun w : GeneratedBootstrapRoundLaw.Past p r => w.2.2.2 s) hpast

private theorem source_extendedHistory_prefix_eq
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (z z' : BootstrapPrivateRoundStreams.SourceInput p) (i : Fin (p.m - 1))
    (r : Fin p.T) (b : ReferenceInitializationRun.Boundary p)
    (h : b.completed < n_boot p) (h' : b.completed < n_boot p)
    (hids : z.1.1 = z'.1.1)
    (hpast : GeneratedBootstrapRoundLaw.past p r
        (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z), z.2) =
      GeneratedBootstrapRoundLaw.past p r
        (z'.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z'), z'.2))
    (u : Fin r.val) (hu : u.val < ReferenceInitializationRun.elapsed p (b.completed + 1)) :
    ReferenceInitializationRun.extendedHistory (sourceReferenceInput rate rewards C_star C_h z)
        b h (PublicDiscreteDraws.followerPlayer p.two_le_m
          (ActualReferenceInitializationBlock.refFollower i))
        ⟨u.val, hu⟩ =
      ReferenceInitializationRun.extendedHistory (sourceReferenceInput rate rewards C_star C_h z')
        b h' (PublicDiscreteDraws.followerPlayer p.two_le_m
          (ActualReferenceInitializationBlock.refFollower i))
        ⟨u.val, hu⟩ := by
  let x := sourceReferenceInput rate rewards C_star C_h z
  let y := sourceReferenceInput rate rewards C_star C_h z'
  by_cases hpastBlock : u.val < ReferenceInitializationRun.elapsed p b.completed
  · simp only [ReferenceInitializationRun.extendedHistory, dite_eq_left hpastBlock]
  · let t : Fin p.T := ⟨u.val, Nat.lt_of_lt_of_le u.isLt (Nat.le_of_lt r.isLt)⟩
    have htval : t.val = u.val := by simp [t]
    have hqBefore : ∀ q : Fin p.T, q.val ≤ t.val → q.val < r.val := by
      intro q hq
      rw [htval] at hq
      omega
    have hblock := source_past_block_reads z z' r hpast (ReferenceInitializationRun.nextBlock b h)
    have hown := physical_ownEntry_eq_of_actual_past x y b h hids rfl
      hblock.1 hblock.2 t
      (fun arm q hq =>
        (source_past_round_reads rate rewards C_star C_h z z' r q hpast
          (hqBefore q hq)).1 arm)
      (fun q hq =>
        (source_past_round_reads rate rewards C_star C_h z z' r q hpast
          (hqBefore q hq)).2.1)
      (fun player q hq =>
        (source_past_round_reads rate rewards C_star C_h z z' r q hpast
          (hqBefore q hq)).2.2 player)
      (PublicDiscreteDraws.followerPlayer p.two_le_m
        (ActualReferenceInitializationBlock.refFollower i))
    simp only [ReferenceInitializationRun.extendedHistory, dite_eq_right hpastBlock]
    have htimeT : (⟨u.val, Nat.lt_of_lt_of_le hu
          (ReferenceInitializationRun.elapsed_le_T p (b.completed + 1))⟩ : Fin p.T) = t := by
      apply Fin.ext
      simp [t]
    rw [← htimeT] at hown
    exact hown

private theorem source_prefixHistory_eq
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (z z' : BootstrapPrivateRoundStreams.SourceInput p) (i : Fin (p.m - 1))
    (r : Fin p.T) (b b' : ReferenceInitializationRun.Boundary p)
    (hb : b = b')
    (h : b.completed < n_boot p) (h' : b'.completed < n_boot p)
    (hbefore : r.val ≤ ReferenceInitializationRun.elapsed p (b.completed + 1))
    (hbefore' : r.val ≤ ReferenceInitializationRun.elapsed p (b'.completed + 1))
    (hids : z.1.1 = z'.1.1)
    (hpast : GeneratedBootstrapRoundLaw.past p r
        (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z), z.2) =
      GeneratedBootstrapRoundLaw.past p r
        (z'.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z'), z'.2)) :
    ReferencePrelaunchLifecycleReplay.prefixHistory
        (ReferenceInitializationRun.extendedHistory (sourceReferenceInput rate rewards C_star C_h z)
          b h (PublicDiscreteDraws.followerPlayer p.two_le_m
            (ActualReferenceInitializationBlock.refFollower i))) r.val hbefore =
      ReferencePrelaunchLifecycleReplay.prefixHistory
        (ReferenceInitializationRun.extendedHistory (sourceReferenceInput rate rewards C_star C_h z')
          b' h' (PublicDiscreteDraws.followerPlayer p.two_le_m
            (ActualReferenceInitializationBlock.refFollower i))) r.val hbefore' := by
  cases hb
  funext u
  unfold ReferencePrelaunchLifecycleReplay.prefixHistory
  have hcast : Fin.castLE hbefore u = Fin.castLE hbefore' u := by
    apply Fin.ext
    rfl
  rw [hcast]
  exact source_extendedHistory_prefix_eq rate rewards C_star C_h z z' i r b h h'
    hids hpast u (Fin.castLE hbefore' u).isLt

private theorem generated_run_completed_le (x : ReferenceInitializationRun.Input p)
    (n : ℕ) : (ReferenceInitializationRun.run x n).completed ≤ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      by_cases hc : (ReferenceInitializationRun.run x n).crossing.isSome = true
      · rw [ReferenceInitializationRun.run_succ,
          ReferenceInitializationRun.advance_of_crossing x _ hc]
        omega
      · have hn : (ReferenceInitializationRun.run x n).crossing = none := by
          cases hh : (ReferenceInitializationRun.run x n).crossing <;> simp_all
        by_cases hcompleted : (ReferenceInitializationRun.run x n).completed < n_boot p
        · rw [ReferenceInitializationRun.run_succ,
            ReferenceInitializationRun.advance_of_no_crossing x _ hn hcompleted]
          simp [ReferenceInitializationRun.finishBlock]
          omega
        · rw [ReferenceInitializationRun.run_succ,
            ReferenceInitializationRun.advance_of_exhausted x _ (Nat.le_of_not_gt hcompleted)]
          omega

private theorem source_ordinary_eq_of_past
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (z z' : BootstrapPrivateRoundStreams.SourceInput p) (i : Fin (p.m - 1))
    (r : Fin p.T) (b b' : ReferenceInitializationRun.Boundary p)
    (hb : b = b')
    (hgen : b = ReferenceInitializationRun.run
      (sourceReferenceInput rate rewards C_star C_h z) (roundBlockIndex p r).val)
    (hpast : GeneratedBootstrapRoundLaw.past p r
        (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z), z.2) =
      GeneratedBootstrapRoundLaw.past p r
        (z'.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z'), z'.2)) :
    ReferenceInitializationRun.ordinary (sourceReferenceInput rate rewards C_star C_h z) b
        (ActualReferenceInitializationBlock.refFollower i) =
      ReferenceInitializationRun.ordinary (sourceReferenceInput rate rewards C_star C_h z') b'
        (ActualReferenceInitializationBlock.refFollower i) := by
  subst b'
  let x := sourceReferenceInput rate rewards C_star C_h z
  let y := sourceReferenceInput rate rewards C_star C_h z'
  have htime : ReferenceInitializationRun.elapsed p b.completed ≤ r.val := by
    calc
      ReferenceInitializationRun.elapsed p b.completed ≤
          ReferenceInitializationRun.elapsed p (roundBlockIndex p r).val :=
        ReferenceInitializationRun.elapsed_mono p (by
          rw [hgen]
          exact generated_run_completed_le x (roundBlockIndex p r).val)
      _ ≤ r.val := GeneratedBootstrapRoundLaw.elapsed_le_of_mem_calendarBlock
        (s := roundBlockIndex p r) (t := r) (round_mem_quotient_block p r)
  unfold ReferenceInitializationRun.ordinary
  by_cases hf : b.forcedFailure (ActualReferenceInitializationBlock.refFollower i)
  · simp [hf, sourceReferenceInput, ActualReferenceInitializationBlock.referenceInput]
  · cases ha : b.activation (ActualReferenceInitializationBlock.refFollower i) with
    | none => simp [hf, sourceReferenceInput, ActualReferenceInitializationBlock.referenceInput]
    | some a =>
        have hn := ReferenceInitializationRun.elapsed_le_T p b.completed
        have hindex : BootstrapPhysicalInput.sourceFollowerIndex p
            (ActualReferenceInitializationBlock.refFollower i) = i := by
          apply Fin.ext
          rfl
        have hrep := ReferencePrelaunchFollower.replay_eq_of_past_reads
          x.eta i x.row y.row a
          (b.history (PublicDiscreteDraws.followerPlayer p.two_le_m
            (ActualReferenceInitializationBlock.refFollower i)))
          (b.history (PublicDiscreteDraws.followerPlayer p.two_le_m
            (ActualReferenceInitializationBlock.refFollower i)))
          hn
          (fun u _ => by
            let t := ReferencePrelaunchFollower.calendar hn u
            have htval : t.val = u.val := by simp [t, ReferencePrelaunchFollower.calendar]
            have huR : u.val < r.val := Nat.lt_of_lt_of_le u.isLt htime
            have hread := source_past_round_reads rate rewards C_star C_h z z' r t hpast
              (by rw [htval]; exact huR)
            unfold ReferencePrelaunchFollower.reads_agree
            refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
            · exact congrArg (fun control => control.1
                ContinuousControlSlice.Label.slot) hread.2.1
            · exact congrArg (fun control => control.1
                ContinuousControlSlice.Label.rec) hread.2.1
            · exact congrArg (fun control => control.1
                ContinuousControlSlice.Label.sel) hread.2.1
            · exact congrArg (fun control => control.1
                ContinuousControlSlice.Label.thin) hread.2.1
            · intro j _
              exact congrArg (fun control => control.1
                (ContinuousControlSlice.Label.pilot j)) hread.2.1
            · exact congrArg (fun control => control.2 (0, i)) hread.2.1)
          (fun _ _ => rfl)
        simp only [hf]
        change ReferencePrelaunchFollower.atLaunch
            (ReferencePrelaunchFollower.replay rate.eta
              (BootstrapPhysicalInput.sourceFollowerIndex p
                (ActualReferenceInitializationBlock.refFollower i))
              x.row a (b.history (PublicDiscreteDraws.followerPlayer p.two_le_m
                (ActualReferenceInitializationBlock.refFollower i))) hn) =
          ReferencePrelaunchFollower.atLaunch
            (ReferencePrelaunchFollower.replay rate.eta
              (BootstrapPhysicalInput.sourceFollowerIndex p
                (ActualReferenceInitializationBlock.refFollower i))
              y.row a (b.history (PublicDiscreteDraws.followerPlayer p.two_le_m
                (ActualReferenceInitializationBlock.refFollower i))) hn)
        have hrep' : ReferencePrelaunchFollower.replay rate.eta i x.row a
            (b.history (PublicDiscreteDraws.followerPlayer p.two_le_m
              (ActualReferenceInitializationBlock.refFollower i))) hn =
          ReferencePrelaunchFollower.replay rate.eta i y.row a
            (b.history (PublicDiscreteDraws.followerPlayer p.two_le_m
              (ActualReferenceInitializationBlock.refFollower i))) hn := by
          simpa [x, y, sourceReferenceInput,
            ActualReferenceInitializationBlock.referenceInput] using hrep
        rw [hindex, hrep']

private theorem source_replay_eq_of_past
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (z z' : BootstrapPrivateRoundStreams.SourceInput p) (i : Fin (p.m - 1))
    (r : Fin p.T) (n : ℕ) (hn : n ≤ p.T) (hnr : n ≤ r.val)
    (a : Activation p) (history history' : LocalHistory p n)
    (hhistory : ∀ u : Fin n, history u = history' u)
    (hpast : GeneratedBootstrapRoundLaw.past p r
        (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z), z.2) =
      GeneratedBootstrapRoundLaw.past p r
        (z'.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z'), z'.2)) :
    ReferencePrelaunchFollower.replay rate.eta i
      (sourceReferenceInput rate rewards C_star C_h z).row a history hn =
    ReferencePrelaunchFollower.replay rate.eta i
      (sourceReferenceInput rate rewards C_star C_h z').row a history' hn := by
  apply ReferencePrelaunchFollower.replay_eq_of_past_reads
  · intro u _
    let t := ReferencePrelaunchFollower.calendar hn u
    have huR : u.val < r.val := Nat.lt_of_lt_of_le u.isLt hnr
    have ht : t.val < r.val := by simpa [t, ReferencePrelaunchFollower.calendar] using huR
    have hread := source_past_round_reads rate rewards C_star C_h z z' r t hpast ht
    unfold ReferencePrelaunchFollower.reads_agree
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact congrArg (fun control => control.1 ContinuousControlSlice.Label.slot) hread.2.1
    · exact congrArg (fun control => control.1 ContinuousControlSlice.Label.rec) hread.2.1
    · exact congrArg (fun control => control.1 ContinuousControlSlice.Label.sel) hread.2.1
    · exact congrArg (fun control => control.1 ContinuousControlSlice.Label.thin) hread.2.1
    · intro j _
      exact congrArg (fun control => control.1 (ContinuousControlSlice.Label.pilot j)) hread.2.1
    · exact congrArg (fun control => control.2 (0, i)) hread.2.1
  · intro u _
    exact hhistory u

private theorem generated_boundaries_eq_of_same_run
    (x y : ReferenceInitializationRun.Input p) (s : Fin (n_boot p))
    (b b' : ReferenceInitializationRun.Boundary p)
    (hb : b = ReferenceInitializationRun.run x s.val)
    (hb' : b' = ReferenceInitializationRun.run y s.val)
    (hrun : ReferenceInitializationRun.run x s.val = ReferenceInitializationRun.run y s.val) :
    b = b' := by
  exact hb.trans (hrun.trans hb'.symm)

/-- Equality of the actual generated block boundary follows from equality of
the original strict-past coordinate `W`. The selected whole row is the one
indexed by the same actual private coordinator scalar; IDs are fixed. -/
theorem source_prelaunch_down_run_boundary_past_invariant
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z z' : BootstrapPrivateRoundStreams.SourceInput p)
    (r : Fin p.T)
    (hids : z.1.1 = z'.1.1)
    (hpast : GeneratedBootstrapRoundLaw.past p r
        (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z), z.2) =
      GeneratedBootstrapRoundLaw.past p r
        (z'.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z'), z'.2)) :
    ReferenceInitializationRun.run (sourceReferenceInput rate rewards C_star C_h z)
        (roundBlockIndex p r).val =
      ReferenceInitializationRun.run (sourceReferenceInput rate rewards C_star C_h z')
        (roundBlockIndex p r).val := by
  let e : GeneratedBootstrapRoundLaw.Coordinates p :=
    (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z), z.2)
  let e' : GeneratedBootstrapRoundLaw.Coordinates p :=
    (z'.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z'), z'.2)
  change ReferenceInitializationRun.run
      (GeneratedBootstrapRoundLaw.input p z.1.1 rewards C_star C_h rate.eta e)
      (roundBlockIndex p r).val =
    ReferenceInitializationRun.run
      (GeneratedBootstrapRoundLaw.input p z'.1.1 rewards C_star C_h rate.eta e')
      (roundBlockIndex p r).val
  rw [← hids]
  exact ReferenceInitializationPrefixInvariance.run_eq_of_runPrefixInputEq
    (GeneratedBootstrapRoundLaw.input p z.1.1 rewards C_star C_h rate.eta e)
    (GeneratedBootstrapRoundLaw.input p z.1.1 rewards C_star C_h rate.eta e')
    (roundBlockIndex p r).val
    (GeneratedBootstrapRoundLaw.runPrefixInputEq_of_past_eq
      z.1.1 rewards C_star C_h rate.eta (roundBlockIndex p r) r
      (round_mem_quotient_block p r) e e' hpast)

/-- Equality of the complete proof-erased prefix follows from equality of the
original strict-past coordinate. All three generated branches are aligned by
their actual run boundary; the current observation is not read. -/
theorem source_prelaunch_down_prefix_past_invariant
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z z' : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (r : Fin p.T)
    (hids : z.1.1 = z'.1.1)
    (hpast : GeneratedBootstrapRoundLaw.past p r
        (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z), z.2) =
      GeneratedBootstrapRoundLaw.past p r
        (z'.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z'), z'.2)) :
    source_prelaunch_down_prefix_observation rate rewards C_star C_h z i r =
      source_prelaunch_down_prefix_observation rate rewards C_star C_h z' i r := by
  let x := sourceReferenceInput rate rewards C_star C_h z
  let y := sourceReferenceInput rate rewards C_star C_h z'
  let s := roundBlockIndex p r
  have hrun := source_prelaunch_down_run_boundary_past_invariant
    rate rewards C_star C_h z z' r hids hpast
  cases hleft : source_prelaunch_down_prefix rate rewards C_star C_h z i r with
  | inl left =>
      cases left with
      | inl active =>
          cases hright : source_prelaunch_down_prefix rate rewards C_star C_h z' i r with
          | inl right =>
              cases right with
              | inl active' =>
                  rcases active.property with ⟨hbefore, hact, hstate, hhistory⟩
                  rcases active'.property with ⟨hbefore', hact', hstate', hhistory'⟩
                  let b := active.val.1.val
                  let b' := active'.val.1.val
                  have hgen := active.val.1.property.2.2
                  have hgen' := active'.val.1.property.2.2
                  have hb := generated_boundaries_eq_of_same_run x y s b b' hgen hgen' hrun
                  have hremain := active.val.1.property.1
                  have hremain' := active'.val.1.property.1
                  have hhist := source_prefixHistory_eq rate rewards C_star C_h z z' i r b b'
                    hb hremain hremain' hbefore hbefore' hids hpast
                  have hhistoryEq : active.val.2.2.1 = active'.val.2.2.1 := by
                    calc
                      active.val.2.2.1 =
                          ReferencePrelaunchLifecycleReplay.prefixHistory
                            (ReferenceInitializationRun.extendedHistory x b hremain
                              (PublicDiscreteDraws.followerPlayer p.two_le_m
                                (ActualReferenceInitializationBlock.refFollower i))) r.val hbefore := by
                            exact hhistory
                      _ = ReferencePrelaunchLifecycleReplay.prefixHistory
                            (ReferenceInitializationRun.extendedHistory y b' hremain'
                              (PublicDiscreteDraws.followerPlayer p.two_le_m
                                (ActualReferenceInitializationBlock.refFollower i))) r.val hbefore' := hhist
                      _ = active'.val.2.2.1 := hhistory'.symm
                  have hsome : some active.val.2.1 = some active'.val.2.1 := by
                    calc
                      some active.val.2.1 = b.activation
                          (ActualReferenceInitializationBlock.refFollower i) := hact.symm
                      _ = b'.activation (ActualReferenceInitializationBlock.refFollower i) :=
                        congrArg (fun boundary => boundary.activation
                          (ActualReferenceInitializationBlock.refFollower i)) hb
                      _ = some active'.val.2.1 := hact'
                  have hacteq : active.val.2.1 = active'.val.2.1 := Option.some.inj hsome
                  have hrep := source_replay_eq_of_past rate rewards C_star C_h z z' i r r.val
                    (Nat.le_of_lt r.isLt) le_rfl active.val.2.1
                    active.val.2.2.1 active'.val.2.2.1
                    (fun u => congrFun hhistoryEq u) hpast
                  have hstateEq : active.val.2.2.2 = active'.val.2.2.2 := by
                    rw [hstate, hstate', ← hacteq]
                    simpa [x, y, sourceReferenceInput,
                      ActualReferenceInitializationBlock.referenceInput] using hrep
                  have htuple :
                      (active.val.1.val, active.val.2.1, active.val.2.2.1, active.val.2.2.2) =
                        (active'.val.1.val, active'.val.2.1, active'.val.2.2.1,
                          active'.val.2.2.2) := by
                    apply Prod.ext hb
                    apply Prod.ext hacteq
                    exact Prod.ext hhistoryEq hstateEq
                  simp only [source_prelaunch_down_prefix_observation, hleft, hright,
                    forgetPrefixProofs]
                  exact congrArg (fun data => Sum.inl (Sum.inl data)) htuple
              | inr inactive' =>
                  rcases active.property with ⟨_, hact, _, _⟩
                  rcases inactive'.property with ⟨_, hact', _⟩
                  have hb := generated_boundaries_eq_of_same_run x y s
                    active.val.1.val inactive'.val.1.val
                    active.val.1.property.2.2 inactive'.val.1.property.2.2 hrun
                  have hsome : some active.val.2.1 = none := by
                    calc
                      some active.val.2.1 = active.val.1.val.activation
                          (ActualReferenceInitializationBlock.refFollower i) := hact.symm
                      _ = inactive'.val.1.val.activation
                          (ActualReferenceInitializationBlock.refFollower i) := by
                            rw [hb]
                      _ = none := hact'
                  simp at hsome
          | inr stopped' =>
              have hb := generated_boundaries_eq_of_same_run x y s
                active.val.1.val stopped'.val.1
                active.val.1.property.2.2 stopped'.property.2.1 hrun
              have hcross := congrArg ReferenceInitializationRun.Boundary.crossing hb
              exact False.elim
                (stopped'.property.1 (hcross.symm.trans active.val.1.property.2.1))
      | inr inactive =>
          cases hright : source_prelaunch_down_prefix rate rewards C_star C_h z' i r with
          | inl right =>
              cases right with
              | inl active' =>
                  rcases inactive.property with ⟨_, hact, _⟩
                  rcases active'.property with ⟨_, hact', _, _⟩
                  have hb := generated_boundaries_eq_of_same_run x y s
                    inactive.val.1.val active'.val.1.val
                    inactive.val.1.property.2.2 active'.val.1.property.2.2 hrun
                  have hsome : none = some active'.val.2.1 := by
                    calc
                      none = inactive.val.1.val.activation
                          (ActualReferenceInitializationBlock.refFollower i) := hact.symm
                      _ = active'.val.1.val.activation
                          (ActualReferenceInitializationBlock.refFollower i) := by
                            rw [hb]
                      _ = some active'.val.2.1 := hact'
                  simp at hsome
              | inr inactive' =>
                  rcases inactive.property with ⟨hbefore, hact, hhistory⟩
                  rcases inactive'.property with ⟨hbefore', hact', hhistory'⟩
                  let b := inactive.val.1.val
                  let b' := inactive'.val.1.val
                  have hb := generated_boundaries_eq_of_same_run x y s b b'
                    inactive.val.1.property.2.2 inactive'.val.1.property.2.2 hrun
                  have hremain := inactive.val.1.property.1
                  have hremain' := inactive'.val.1.property.1
                  have hhist := source_prefixHistory_eq rate rewards C_star C_h z z' i r b b'
                    hb hremain hremain' hbefore hbefore' hids hpast
                  have hhistoryEq : inactive.val.2 = inactive'.val.2 := by
                    calc
                      inactive.val.2 = ReferencePrelaunchLifecycleReplay.prefixHistory
                          (ReferenceInitializationRun.extendedHistory x b hremain
                            (PublicDiscreteDraws.followerPlayer p.two_le_m
                              (ActualReferenceInitializationBlock.refFollower i))) r.val hbefore :=
                        hhistory
                      _ = ReferencePrelaunchLifecycleReplay.prefixHistory
                          (ReferenceInitializationRun.extendedHistory y b' hremain'
                            (PublicDiscreteDraws.followerPlayer p.two_le_m
                              (ActualReferenceInitializationBlock.refFollower i))) r.val hbefore' := hhist
                      _ = inactive'.val.2 := hhistory'.symm
                  have htuple : (inactive.val.1.val, inactive.val.2) =
                      (inactive'.val.1.val, inactive'.val.2) := Prod.ext hb hhistoryEq
                  simp only [source_prelaunch_down_prefix_observation, hleft, hright,
                    forgetPrefixProofs]
                  exact congrArg (fun data => Sum.inl (Sum.inr data)) htuple
          | inr stopped' =>
              have hb := generated_boundaries_eq_of_same_run x y s
                inactive.val.1.val stopped'.val.1
                inactive.val.1.property.2.2 stopped'.property.2.1 hrun
              have hcross := congrArg ReferenceInitializationRun.Boundary.crossing hb
              exact False.elim
                (stopped'.property.1 (hcross.symm.trans inactive.val.1.property.2.1))
  | inr stopped =>
      cases hright : source_prelaunch_down_prefix rate rewards C_star C_h z' i r with
      | inl right =>
          cases right with
          | inl active' =>
              have hb := generated_boundaries_eq_of_same_run x y s
                stopped.val.1 active'.val.1.val stopped.property.2.1
                active'.val.1.property.2.2 hrun
              have hcross := congrArg ReferenceInitializationRun.Boundary.crossing hb
              exact False.elim
                (stopped.property.1 (hcross.trans active'.val.1.property.2.1))
          | inr inactive' =>
              have hb := generated_boundaries_eq_of_same_run x y s
                stopped.val.1 inactive'.val.1.val stopped.property.2.1
                inactive'.val.1.property.2.2 hrun
              have hcross := congrArg ReferenceInitializationRun.Boundary.crossing hb
              exact False.elim
                (stopped.property.1 (hcross.trans inactive'.val.1.property.2.1))
      | inr stopped' =>
          have hb := generated_boundaries_eq_of_same_run x y s
            stopped.val.1 stopped'.val.1 stopped.property.2.1 stopped'.property.2.1 hrun
          have hordinary := source_ordinary_eq_of_past rate rewards C_star C_h z z' i r
            stopped.val.1 stopped'.val.1 hb stopped.property.2.1 hpast
          have hstate : stopped.val.2 = stopped'.val.2 := by
            rw [stopped.property.2.2, stopped'.property.2.2]
            exact hordinary
          have htuple : stopped.val = stopped'.val := Prod.ext hb hstate
          simp only [source_prelaunch_down_prefix_observation, hleft, hright,
            forgetPrefixProofs]
          exact congrArg Sum.inr htuple

/-- The actual test list is the replay census; pending is its chronological
suffix after completed quota batches, including on the stopped projection. -/
theorem source_prelaunch_down_prefix_census
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (r : Fin p.T) :
    match source_prelaunch_down_prefix rate rewards C_star C_h z i r with
    | .inl (.inl active) =>
        let bank := active.val.2.2.2.downBatch
        let tests := source_prelaunch_down_prefix_tests rate rewards C_star C_h z i r
        tests.map ReferenceGeneratedPrelaunchDownCohort.testEntry =
            AffineBatchDecoder.collected bank ∧
          bank.pending = (tests.map ReferenceGeneratedPrelaunchDownCohort.testEntry).drop
            (AffineBatchDecoder.quota p * bank.completed.length) ∧
          (∀ batch ∈ bank.completed, batch.length = AffineBatchDecoder.quota p) ∧
          bank.pending.length < AffineBatchDecoder.quota p
    | .inl (.inr _) => source_prelaunch_down_prefix_tests rate rewards C_star C_h z i r = []
    | .inr stopped =>
        let bank := stopped.val.2.downBatch
        let tests := source_prelaunch_down_prefix_tests rate rewards C_star C_h z i r
        tests.map ReferenceGeneratedPrelaunchDownCohort.testEntry =
            AffineBatchDecoder.collected bank ∧
          bank.pending = (tests.map ReferenceGeneratedPrelaunchDownCohort.testEntry).drop
            (AffineBatchDecoder.quota p * bank.completed.length) ∧
          (∀ batch ∈ bank.completed, batch.length = AffineBatchDecoder.quota p) ∧
          bank.pending.length < AffineBatchDecoder.quota p := by
  classical
  let x := sourceReferenceInput rate rewards C_star C_h z
  cases hpref : source_prelaunch_down_prefix rate rewards C_star C_h z i r with
  | inl branch =>
      cases branch with
      | inl active =>
          simp only [hpref, source_prelaunch_down_prefix_tests]
          let a := active.val.2.1
          let history := active.val.2.2.1
          let state := active.val.2.2.2
          let tests := (List.ofFn (fun u : Fin r.val => u)).filterMap (fun u =>
            ReferenceGeneratedPrelaunchDownCohort.prelaunchTest i x.row a
              (ReferencePrelaunchFollower.calendar (Nat.le_of_lt r.isLt) u) (history u))
          have hs := ReferencePrelaunchFollower.replay_batch_spec rate.eta i x.row a
            history (Nat.le_of_lt r.isLt)
          rcases active.property with ⟨_, _, hstate, _⟩
          have hbank : state.downBatch =
              (ReferencePrelaunchFollower.replay rate.eta i x.row a history
                (Nat.le_of_lt r.isLt)).downBatch := congrArg State.downBatch hstate
          have he := tests_entries i x.row a history (Nat.le_of_lt r.isLt)
            (List.ofFn (fun u : Fin r.val => u))
          have hmap : tests.map ReferenceGeneratedPrelaunchDownCohort.testEntry =
              AffineBatchDecoder.collected state.downBatch := by
            dsimp only [tests, state, a, history]
            exact (he.trans hs.2.2.symm).trans
              (congrArg (fun state : State p rate.eta =>
                AffineBatchDecoder.collected state.downBatch) hstate).symm
          have hcompleted : ∀ batch ∈ state.downBatch.completed,
              batch.length = AffineBatchDecoder.quota p := by
            rw [hbank]
            exact hs.2.1
          have hshort : state.downBatch.pending.length < AffineBatchDecoder.quota p := by
            rw [hbank]
            exact hs.1
          have hslice := completed_slice
            (ReferencePrelaunchFollower.replay rate.eta i x.row a history
              (Nat.le_of_lt r.isLt)).downBatch.completed
            (ReferencePrelaunchFollower.replay rate.eta i x.row a history
              (Nat.le_of_lt r.isLt)).downBatch.pending hs.2.1
          refine ⟨hmap, ?_, hcompleted, hshort⟩
          rw [hbank, hmap, hbank]
          exact hslice.1.symm
      | inr inactive =>
          simp only [hpref, source_prelaunch_down_prefix_tests]
  | inr stopped =>
      simp only [hpref, source_prelaunch_down_prefix_tests]
      let b := stopped.val.1
      let ordinary := stopped.val.2
      let tests := ReferenceGeneratedPrelaunchDownCohort.boundaryPrelaunchDownTests x b i
      have hc := boundary_test_census x b i
      have hstate : ordinary = ReferenceInitializationRun.ordinary x b
          (ActualReferenceInitializationBlock.refFollower i) := stopped.property.2.2
      have hbank : ordinary.downBatch =
          (ReferenceInitializationRun.ordinary x b
            (ActualReferenceInitializationBlock.refFollower i)).downBatch :=
        congrArg State.downBatch hstate
      have hcompleted : ∀ batch ∈ ordinary.downBatch.completed,
          batch.length = AffineBatchDecoder.quota p := by
        rw [hbank]
        exact hc.2.2
      have hshort : ordinary.downBatch.pending.length < AffineBatchDecoder.quota p := by
        rw [hbank]
        exact hc.2.1
      have hmap : tests.map ReferenceGeneratedPrelaunchDownCohort.testEntry =
          AffineBatchDecoder.collected ordinary.downBatch := by
        dsimp only [tests]
        rw [hbank]
        exact hc.1
      have hslice := completed_slice ordinary.downBatch.completed
        ordinary.downBatch.pending hcompleted
      refine ⟨hmap, ?_, hcompleted, hshort⟩
      calc
        ordinary.downBatch.pending = (AffineBatchDecoder.collected ordinary.downBatch).drop
            (AffineBatchDecoder.quota p * ordinary.downBatch.completed.length) := hslice.1.symm
        _ = (tests.map ReferenceGeneratedPrelaunchDownCohort.testEntry).drop
            (AffineBatchDecoder.quota p * ordinary.downBatch.completed.length) :=
          congrArg (fun xs : List (AffineBatchDecoder.Entry p.T
            (AffineBatchDecoder.width p)) => xs.drop
              (AffineBatchDecoder.quota p * ordinary.downBatch.completed.length)) hmap.symm

/-- Exact birth projection for an activated prefix. -/
theorem source_prelaunch_down_birth_spec
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (r : Fin p.T) :
    source_prelaunch_down_prefix_birth rate rewards C_star C_h z i r =
      match source_prelaunch_down_prefix rate rewards C_star C_h z i r with
      | .inl (.inl active) => bankBirth active.val.2.1 active.val.2.2.2.downBatch
      | .inl (.inr _) => none
      | .inr stopped =>
          let b := stopped.val.1
          let ordinary := stopped.val.2
          (b.activation (ActualReferenceInitializationBlock.refFollower i)).bind
            (fun a => bankBirth a ordinary.downBatch) := by
  rfl

/-- Initial birth and each terminal quota clearing use the actual cohort API.
Completion evidence retains the raw decoder result, including `none`. -/
theorem source_prelaunch_down_terminal_actual_origins
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) :
    let x := sourceReferenceInput rate rewards C_star C_h z
    let b := ReferenceInitializationRun.output x
    let f := ActualReferenceInitializationBlock.refFollower i
    let bank := (ReferenceInitializationRun.ordinary x b f).downBatch
    ReferenceGeneratedPrelaunchDownCohort.sourcePrelaunchDownCohortBoundary
        rate rewards C_star C_h z i 0 =
        (b.activation f).map (fun a => a.val - 1) ∧
      ∀ k (hk : k < bank.completed.length),
        ∃ t : Fin p.T, t.val < ReferenceInitializationRun.elapsed p b.completed ∧
          bank.completed[k].getLast? =
            some ⟨t, (x.row.2 t).2 (0, i)⟩ ∧
          ReferenceGeneratedPrelaunchDownCohort.sourcePrelaunchDownCohortBoundary
              rate rewards C_star C_h z i (k + 1) = some (t.val + 1) := by
  dsimp only
  refine ⟨(ReferenceGeneratedPrelaunchDownCohort.source_prelaunch_down_initial_boundary
    rate rewards C_star C_h z i).1, ?_⟩
  intro k hk
  exact ReferenceGeneratedPrelaunchDownCohort.source_prelaunch_down_reset_boundary
    rate rewards C_star C_h z i k hk

/-- Natural endpoint projection after the initialization run. There is no
`Fin T` action or current prelaunch test at this boundary. -/
def source_prelaunch_down_terminal
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) :
    ReferenceInitializationRun.Boundary p × State p rate.eta := by
  let x := sourceReferenceInput rate rewards C_star C_h z
  let b := ReferenceInitializationRun.output x
  exact (b, ReferenceInitializationRun.ordinary x b
    (ActualReferenceInitializationBlock.refFollower i))

/-- The terminal birth projection is computed from the actual terminal
activation and the ordinary bank's actual completed batches. -/
def source_prelaunch_down_terminal_birth
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) : Option ℕ := by
  let x := sourceReferenceInput rate rewards C_star C_h z
  let b := ReferenceInitializationRun.output x
  exact (b.activation (ActualReferenceInitializationBlock.refFollower i)).bind
    (fun a => bankBirth a
      (ReferenceInitializationRun.ordinary x b
        (ActualReferenceInitializationBlock.refFollower i)).downBatch)

/-- The corrected launch seed carries this same ordinary state; old stamped
tests are the actual pending suffix, with launch and failure evidence retained. -/
theorem source_launch_down_pending_prefix
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1))
    (hs : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (sourceReferenceInput rate rewards C_star C_h z)).completed < p.T)
    (hc : (ReferenceInitializationRun.output
      (sourceReferenceInput rate rewards C_star C_h z)).crossing.isSome = true) :
    let x := sourceReferenceInput rate rewards C_star C_h z
    let b := ReferenceInitializationRun.output x
    let bank := (ReferenceInitializationRun.ordinary x b
      (ActualReferenceInitializationBlock.refFollower i)).downBatch
    ∃ launchSource : ReferenceGeneratedDownBatchCalendar.LaunchSource rate rewards C_star C_h
        (ReferenceInitializationRun.elapsed p b.completed) hs,
      launchSource.val = z ∧
      ReferenceCorrectedInitializationLaunch.correctedLaunch rate z rewards C_star C_h =
        some (ReferenceGeneratedDownBatchCalendar.generatedSourceSeed rate rewards C_star C_h
          (ReferenceInitializationRun.elapsed p b.completed) hs launchSource) ∧
      (ReferenceGeneratedDownBatchCalendar.generatedSourceSeed rate rewards C_star C_h
        (ReferenceInitializationRun.elapsed p b.completed) hs launchSource).followers i =
        .ordinary (ReferenceInitializationRun.ordinary x b
          (ActualReferenceInitializationBlock.refFollower i))
          (ActiveFollowerLifecycle.initialMemory p) ∧
      ReferenceFollowerDecoderChronology.downBatchSeed
        (ReferenceGeneratedDownBatchCalendar.generatedSourceSeed rate rewards C_star C_h
          (ReferenceInitializationRun.elapsed p b.completed) hs launchSource)
        (ReferenceInitializationRun.elapsed p b.completed) ∧
      ReferenceInitializationRun.initializationFailure x b
        (ActualReferenceInitializationBlock.refFollower i) =
        (b.forcedFailure (ActualReferenceInitializationBlock.refFollower i) ||
          (ReferenceInitializationRun.ordinary x b
            (ActualReferenceInitializationBlock.refFollower i)).initializationFailure) ∧
      (∃ a, b.activation (ActualReferenceInitializationBlock.refFollower i) = some a ∧
        ((b.forcedFailure (ActualReferenceInitializationBlock.refFollower i) = true ∧
          ReferenceInitializationRun.ordinary x b
            (ActualReferenceInitializationBlock.refFollower i) =
              ReferencePrelaunchFollower.initial p rate.eta ∧
          a.val = ReferenceInitializationRun.elapsed p b.completed + 1) ∨
         (b.forcedFailure (ActualReferenceInitializationBlock.refFollower i) = false ∧
          ReferenceInitializationRun.ordinary x b
            (ActualReferenceInitializationBlock.refFollower i) =
              ReferencePrelaunchFollower.replay rate.eta i x.row a
                (b.history (PublicDiscreteDraws.followerPlayer p.two_le_m
                  (ActualReferenceInitializationBlock.refFollower i)))
                (ReferenceInitializationRun.elapsed_le_T p b.completed)))) ∧
      (∀ a, b.activation (ActualReferenceInitializationBlock.refFollower i) = some a →
        a.val = ReferenceInitializationRun.elapsed p b.completed + 1 →
        bank.pending = [] ∧ bank.completed.length = 0 ∧
          bankBirth a bank = some (ReferenceInitializationRun.elapsed p b.completed)) ∧
      bank.pending.length < AffineBatchDecoder.quota p ∧
      bank.pending =
        ((ReferenceGeneratedPrelaunchDownCohort.sourcePrelaunchDownTests
          rate rewards C_star C_h z i).map
            ReferenceGeneratedPrelaunchDownCohort.testEntry).drop
          (AffineBatchDecoder.quota p * bank.completed.length) := by
  dsimp only
  let x := sourceReferenceInput rate rewards C_star C_h z
  let b := ReferenceInitializationRun.output x
  let bank := (ReferenceInitializationRun.ordinary x b
    (ActualReferenceInitializationBlock.refFollower i)).downBatch
  have hlaunch := ReferenceGeneratedPrelaunchDownCohort.source_launch_down_cohort_provenance
    rate rewards C_star C_h z i hs hc
  have hcensus := ReferenceGeneratedPrelaunchDownCohort.source_prelaunch_down_cohorts
    rate rewards C_star C_h z i
  rcases hlaunch with ⟨launchSource, hsource, hcorrect, hseed, hbatch, hfailure,
    a, ha, hcase⟩
  refine ⟨launchSource, hsource, hcorrect, hseed, hbatch, hfailure, ?_, ?_,
    hcensus.2.2.2, ?_⟩
  · exact ⟨a, ha, hcase⟩
  · intro a' ha' hnew
    have hinitial := (ReferenceGeneratedPrelaunchDownCohort.source_prelaunch_down_initial_cases
      rate rewards C_star C_h z i).2 a' ha' hnew
    have hstate : ReferenceInitializationRun.ordinary x b
        (ActualReferenceInitializationBlock.refFollower i) =
          ReferencePrelaunchFollower.initial p rate.eta := by
      simpa [x, b, sourceReferenceInput,
        ActualReferenceInitializationBlock.referenceInput] using hinitial.1
    have hnew' : a'.val = ReferenceInitializationRun.elapsed p b.completed + 1 := by
      simpa [x, b, sourceReferenceInput,
        ActualReferenceInitializationBlock.referenceInput] using hnew
    refine ⟨?_, ?_, ?_⟩
    · change (ReferenceInitializationRun.ordinary x b
        (ActualReferenceInitializationBlock.refFollower i)).downBatch.pending = []
      rw [hstate]
      simp [ReferencePrelaunchFollower.initial, AffineBatchDecoder.initial]
    · change (ReferenceInitializationRun.ordinary x b
        (ActualReferenceInitializationBlock.refFollower i)).downBatch.completed.length = 0
      rw [hstate]
      simp [ReferencePrelaunchFollower.initial, AffineBatchDecoder.initial]
    · change bankBirth a' (ReferenceInitializationRun.ordinary x b
        (ActualReferenceInitializationBlock.refFollower i)).downBatch =
          some (ReferenceInitializationRun.elapsed p b.completed)
      rw [hstate]
      simp [bankBirth, ReferencePrelaunchFollower.initial,
        AffineBatchDecoder.initial, hnew']
  · exact hcensus.2.1

end Bandits.Support.ReferenceGeneratedPrelaunchDownPrefix
