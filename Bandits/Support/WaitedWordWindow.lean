/-
Copyright (c) 2026 The Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.AffineBatchDecoder
public import Bandits.Support.ActiveObservationBridge
public import Bandits.Support.OrdinaryMessageCodec

import Mathlib.Data.List.TakeDrop
import Lean.Elab.Tactic.Omega

/-!
# The deterministic two-batch waited-word acceptance window

The two-batch count and decoder transition are from
`sources/zip4/manuscript/05_binary_transport.tex:36-48,50-53` and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:151-157`. The local
DOWN/UP predicates and record carriers are from
`sources/zip4/manuscript/06_interruptions.tex:103-177`.

This module starts the existing decoder with an arbitrary older pending list,
feeds a chronological list of explicitly eligible positive rounds, and
identifies the second completed batch as the last quota entries of that list.
The first batch may contain the older pending equations. Physical equation
facts are derived from `ActiveObservationBridge`; word persistence, local
receiver state, and uniqueness of this concrete second batch remain explicit
inputs. In particular, uniqueness is the deterministic per-batch input
corresponding to excluding the source event `E_amb`. No probability,
execution history, stale-word exclusion, or service quota is proved here.
-/

@[expose] public section

namespace Bandits.Support.WaitedWordWindow

open Bandits.Support.ActiveRoundActions
open Bandits.Support.AffineChannelLaw
open Bandits.Support.AffineBatchDecoder
open Bandits.Support.OrdinaryMessageCodec
open Bandits.Support.PublicDiscreteDraws

/-- The manuscript round number represented by a zero-based `Fin T` index. -/
def sourceRound {T : ℕ} (t : Fin T) : ℕ := t.val + 1

/-- The source follower number represented by the formal zero-based follower index. -/
def sourceFollowerId {m : ℕ} (i : Follower m) : ℕ := i.val + 1

/-- The source-facing natural-number form of a finite pending-follower set. -/
def sourcePendingSet {m : ℕ} (P : Finset (Follower m)) : Set ℕ :=
  {j | ∃ i, i ∈ P ∧ sourceFollowerId i = j}

theorem sourceFollowerId_mem_sourcePendingSet_iff {m : ℕ}
    (P : Finset (Follower m)) (i : Follower m) :
    sourceFollowerId i ∈ sourcePendingSet P ↔ i ∈ P := by
  constructor
  · rintro ⟨j, hj, heq⟩
    have hij : j = i := by
      apply Fin.ext
      dsimp [sourceFollowerId] at heq
      omega
    simpa [hij] using hj
  · intro hi
    exact ⟨i, hi, rfl⟩

/-- The literal UP decoder inputs on one live channel. `upClockOpen` is the
source cutoff test `u ≤ t`; `upPending` is the contemporaneous coordinator set.
The additional live-snapshot membership and unoccupied-state gates are exactly
the hypotheses required by the accepted physical UP observation lemma. -/
noncomputable def upObservationTrace
    (p : ConstructorDimensions.Parameters)
    (a : Assignment p.m p.K)
    (liveRounds : Fin p.T → LiveRoundData a (AffineBatchDecoder.width p))
    (i : Follower p.m) (cutoff : ℕ)
    (upPending : Fin p.T → Finset (Follower p.m)) : AffineBatchDecoder.Trace p :=
  fun t =>
    let s := ActiveObservationBridge.liveSnapshotBefore p a liveRounds t
    let d := liveRounds t
    { selected := decide
        (cutoff ≤ sourceRound t ∧ i ∈ upPending t ∧ d.input.slot = upSlot ∧
          d.input.selected = i ∧ i ∈ s.missing ∧ s.status i = .unoccupied)
      receiverEnabled := true
      sample := d.input.up.sample
      roundedReward := ActiveRoundActions.feedback p.two_le_m s d.input d.rewards
        (Bandits.Support.ActiveRoundActions.coordinator p.two_le_m) }

/-- An eligible UP decoder input gives the exact source gates and a positive
coordinator observation needed by the physical UP equation lemma. -/
theorem upObservationTrace_eligible_source_conditions
    (p : ConstructorDimensions.Parameters)
    (a : Assignment p.m p.K)
    (liveRounds : Fin p.T → LiveRoundData a (AffineBatchDecoder.width p))
    (i : Follower p.m) (cutoff : ℕ)
    (upPending : Fin p.T → Finset (Follower p.m)) (t : Fin p.T)
    (h : AffineBatchDecoder.eligible (upObservationTrace p a liveRounds i cutoff upPending t)) :
    cutoff ≤ sourceRound t ∧ i ∈ upPending t ∧
      (liveRounds t).input.slot = upSlot ∧ (liveRounds t).input.selected = i ∧
      i ∈ (ActiveObservationBridge.liveSnapshotBefore p a liveRounds t).missing ∧
      (ActiveObservationBridge.liveSnapshotBefore p a liveRounds t).status i = .unoccupied ∧
      0 < ActiveRoundActions.feedback p.two_le_m
        (ActiveObservationBridge.liveSnapshotBefore p a liveRounds t)
        (liveRounds t).input (liveRounds t).rewards
        (Bandits.Support.ActiveRoundActions.coordinator p.two_le_m) := by
  change (upObservationTrace p a liveRounds i cutoff upPending t).selected = true ∧
    (upObservationTrace p a liveRounds i cutoff upPending t).receiverEnabled = true ∧
    0 < (upObservationTrace p a liveRounds i cutoff upPending t).roundedReward at h
  have hgate : cutoff ≤ sourceRound t ∧ i ∈ upPending t ∧
      (liveRounds t).input.slot = upSlot ∧ (liveRounds t).input.selected = i ∧
      i ∈ (ActiveObservationBridge.liveSnapshotBefore p a liveRounds t).missing ∧
      (ActiveObservationBridge.liveSnapshotBefore p a liveRounds t).status i = .unoccupied := by
    simpa only [upObservationTrace, decide_eq_true_eq] using h.1
  refine ⟨hgate.1, hgate.2.1, hgate.2.2.1, hgate.2.2.2.1,
    hgate.2.2.2.2.1, hgate.2.2.2.2.2, ?_⟩
  simpa only [upObservationTrace] using h.2.2

/-- The suffix after the first quota threshold, under the source condition that
the supplied pending list is strictly below quota. -/
noncomputable def secondPositiveWindow
    (p : ConstructorDimensions.Parameters) (tr : AffineBatchDecoder.Trace p)
    (rounds : List (Fin p.T)) (pending : List (AffineBatchDecoder.Entry p.T
      (AffineBatchDecoder.width p))) (_hpending : pending.length < AffineBatchDecoder.quota p) :
    List (AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p)) :=
  (AffineBatchDecoder.positives p tr rounds).drop
    (AffineBatchDecoder.quota p - pending.length)

private theorem mem_of_mem_drop_list {α : Type} (xs : List α) (n : ℕ)
    {x : α} (h : x ∈ xs.drop n) : x ∈ xs := by
  induction n generalizing xs with
  | zero => simpa using h
  | succ n ih =>
      cases xs with
      | nil => simp at h
      | cons a xs =>
          exact List.mem_cons_of_mem a (ih xs (by simpa using h))

private theorem run_with_history
    (p : ConstructorDimensions.Parameters) (tr : AffineBatchDecoder.Trace p)
    (rounds : List (Fin p.T)) (pending : List (AffineBatchDecoder.Entry p.T
      (AffineBatchDecoder.width p))) (history : List (List (AffineBatchDecoder.Entry p.T
      (AffineBatchDecoder.width p)))) :
    AffineBatchDecoder.run p tr rounds ⟨pending, history⟩ =
      let base := AffineBatchDecoder.run p tr rounds ⟨pending, []⟩
      ⟨base.pending, history ++ base.completed⟩ := by
  induction rounds generalizing pending history with
  | nil => simp [AffineBatchDecoder.run]
  | cons t rounds ih =>
      simp only [AffineBatchDecoder.run]
      let added := pending ++ AffineBatchDecoder.positiveAt p tr t
      by_cases hsmall : pending.length +
          (AffineBatchDecoder.positiveAt p tr t).length < AffineBatchDecoder.quota p
      · have hstep₁ : AffineBatchDecoder.step p tr ⟨pending, history⟩ t =
            ⟨added, history⟩ := by simp [AffineBatchDecoder.step, added, hsmall]
        have hstep₂ : AffineBatchDecoder.step p tr ⟨pending, []⟩ t =
            ⟨added, []⟩ := by simp [AffineBatchDecoder.step, added, hsmall]
        rw [hstep₁, hstep₂]
        exact ih (pending := added) (history := history)
      · have hstep₁ : AffineBatchDecoder.step p tr ⟨pending, history⟩ t =
            ⟨[], history ++ [added]⟩ := by simp [AffineBatchDecoder.step, added, hsmall]
        have hstep₂ : AffineBatchDecoder.step p tr ⟨pending, []⟩ t =
            ⟨[], [added]⟩ := by simp [AffineBatchDecoder.step, added, hsmall]
        rw [hstep₁, hstep₂]
        have hleft := ih (pending := []) (history := history ++ [added])
        have hright := ih (pending := []) (history := [added])
        rw [hright]
        simpa [List.append_assoc] using hleft

private theorem decoderState_ext {T B : ℕ}
    (s t : AffineBatchDecoder.State T B)
    (hpending : s.pending = t.pending) (hcompleted : s.completed = t.completed) :
    s = t := by
  cases s
  cases t
  cases hpending
  cases hcompleted
  rfl

private theorem two_batches_from_empty_history
    (p : ConstructorDimensions.Parameters) (tr : AffineBatchDecoder.Trace p)
    (rounds : List (Fin p.T))
    (pending : List (AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p)))
    (hpending : pending.length < AffineBatchDecoder.quota p)
    (hcount : (AffineBatchDecoder.positives p tr rounds).length =
      AffineBatchDecoder.quota p - pending.length + AffineBatchDecoder.quota p) :
    ∃ first : List (AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p)),
      AffineBatchDecoder.run p tr rounds ⟨pending, []⟩ = ⟨[], [first,
        secondPositiveWindow p tr rounds pending hpending]⟩ ∧
      first = pending ++ (AffineBatchDecoder.positives p tr rounds).take
        (AffineBatchDecoder.quota p - pending.length) ∧
      first.length = AffineBatchDecoder.quota p ∧
      (secondPositiveWindow p tr rounds pending hpending).length =
        AffineBatchDecoder.quota p := by
  let out := AffineBatchDecoder.run p tr rounds ⟨pending, []⟩
  have hdec := AffineBatchDecoder.second_decision p tr rounds pending hpending hcount
  have hspec := AffineBatchDecoder.run_spec p tr rounds ⟨pending, []⟩ hpending (by simp)
  have hcompLen : out.completed.length = 2 := by simpa only [out] using hdec.1
  have hpend : out.pending = [] := by simpa only [out] using hdec.2
  have hbatchSizes : ∀ batch ∈ out.completed, batch.length = AffineBatchDecoder.quota p := by
    simpa only [out] using hspec.2.1
  have hcollected : out.completed.flatten ++ out.pending =
      pending ++ AffineBatchDecoder.positives p tr rounds := by
    simpa only [out, AffineBatchDecoder.collected, List.flatten_nil,
      List.nil_append] using hspec.2.2
  cases hcompleted : out.completed with
  | nil =>
      simp only [hcompleted, List.length_nil] at hcompLen
      omega
  | cons first tail =>
    cases htail : tail with
    | nil =>
        simp only [hcompleted, htail, List.length_cons, List.length_nil] at hcompLen
        omega
    | cons second rest =>
      have hrestNil : rest = [] := by
        have hcompLen' : rest.length + 1 + 1 = 2 := by
          simpa only [hcompleted, htail, List.length_cons] using hcompLen
        have hzero : rest.length = 0 := by omega
        exact List.length_eq_zero_iff.mp hzero
      have htwo : out.completed = [first, second] := by
        rw [hcompleted, htail, hrestNil]
      have hfirstLen : first.length = AffineBatchDecoder.quota p :=
        hbatchSizes first (by simp [htwo])
      have hsecondLen : second.length = AffineBatchDecoder.quota p :=
        hbatchSizes second (by simp [htwo])
      have hjoined : first ++ second = pending ++ AffineBatchDecoder.positives p tr rounds := by
        simpa [htwo, hpend] using hcollected
      have hfirstWhole : first =
          (pending ++ AffineBatchDecoder.positives p tr rounds).take
            (AffineBatchDecoder.quota p) := by
        calc
          first = (first ++ second).take (AffineBatchDecoder.quota p) := by
            rw [List.take_append]
            simp [hfirstLen]
          _ = (pending ++ AffineBatchDecoder.positives p tr rounds).take
              (AffineBatchDecoder.quota p) := by rw [hjoined]
      have hfirstExpected :
          (pending ++ AffineBatchDecoder.positives p tr rounds).take
              (AffineBatchDecoder.quota p) =
            pending ++ (AffineBatchDecoder.positives p tr rounds).take
              (AffineBatchDecoder.quota p - pending.length) := by
        rw [List.take_append]
        have hplen : pending.length ≤ AffineBatchDecoder.quota p := by omega
        simp [List.take_of_length_le hplen]
      have hfirst : first = pending ++
          (AffineBatchDecoder.positives p tr rounds).take
            (AffineBatchDecoder.quota p - pending.length) :=
        hfirstWhole.trans hfirstExpected
      have hsecondWhole : second =
          (pending ++ AffineBatchDecoder.positives p tr rounds).drop
            (AffineBatchDecoder.quota p) := by
        calc
          second = (first ++ second).drop (AffineBatchDecoder.quota p) := by
            rw [List.drop_append]
            simp [hfirstLen]
          _ = (pending ++ AffineBatchDecoder.positives p tr rounds).drop
              (AffineBatchDecoder.quota p) := by rw [hjoined]
      have hsecondExpected :
          (pending ++ AffineBatchDecoder.positives p tr rounds).drop
              (AffineBatchDecoder.quota p) =
            (AffineBatchDecoder.positives p tr rounds).drop
              (AffineBatchDecoder.quota p - pending.length) := by
        rw [List.drop_append]
        have hplen : pending.length ≤ AffineBatchDecoder.quota p := by omega
        simp [List.drop_eq_nil_of_le hplen]
      have hsecond : second = secondPositiveWindow p tr rounds pending hpending := by
        rw [hsecondWhole, hsecondExpected, secondPositiveWindow]
      have hout : out = ⟨[], [first, second]⟩ := by
        apply decoderState_ext
        · exact hpend
        · exact htwo
      refine ⟨first, ?_, hfirst, hfirstLen, ?_⟩
      · simpa only [out, hsecond] using hout
      · rw [← hsecond]
        exact hsecondLen

/-- Exact two-batch assembly for an arbitrary decoder state. The older pending
entries are all before the supplied chronological round list; no condition is
placed on their samples or equations. The second completed batch is exactly
the last quota eligible entries and contains none of the old pending entries. -/
theorem run_two_batch_window
    (p : ConstructorDimensions.Parameters) (tr : AffineBatchDecoder.Trace p)
    (rounds : List (Fin p.T))
    (s : AffineBatchDecoder.State p.T (AffineBatchDecoder.width p))
    (hpending : s.pending.length < AffineBatchDecoder.quota p)
    (hcount : (AffineBatchDecoder.positives p tr rounds).length =
      AffineBatchDecoder.quota p - s.pending.length + AffineBatchDecoder.quota p)
    (hchronological : rounds.Pairwise (fun t₁ t₂ => t₁.val < t₂.val))
    (hpendingOlder : ∀ e ∈ s.pending, ∀ t ∈ rounds, e.time.val < t.val) :
    ∃ first : List (AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p)),
      AffineBatchDecoder.run p tr rounds s =
        ⟨[], s.completed ++ [first, secondPositiveWindow p tr rounds s.pending hpending]⟩ ∧
      first = s.pending ++ (AffineBatchDecoder.positives p tr rounds).take
        (AffineBatchDecoder.quota p - s.pending.length) ∧
      first.length = AffineBatchDecoder.quota p ∧
      (secondPositiveWindow p tr rounds s.pending hpending).length =
        AffineBatchDecoder.quota p ∧
      (secondPositiveWindow p tr rounds s.pending hpending).Pairwise
        (fun e₁ e₂ => e₁.time.val < e₂.time.val) ∧
      (∀ e ∈ s.pending,
        e ∉ secondPositiveWindow p tr rounds s.pending hpending) ∧
      (AffineBatchDecoder.positives p tr rounds).length ≤ 2 * AffineBatchDecoder.quota p := by
  obtain ⟨first, hbase, hfirst, hfirstLen, hwindowLen⟩ :=
    two_batches_from_empty_history p tr rounds s.pending hpending hcount
  have hhistory := run_with_history p tr rounds s.pending s.completed
  have hrun : AffineBatchDecoder.run p tr rounds s =
      ⟨[], s.completed ++ [first, secondPositiveWindow p tr rounds s.pending hpending]⟩ := by
    calc
      AffineBatchDecoder.run p tr rounds s =
          let base := AffineBatchDecoder.run p tr rounds ⟨s.pending, []⟩
          ⟨base.pending, s.completed ++ base.completed⟩ := hhistory
      _ = ⟨[], s.completed ++ [first,
          secondPositiveWindow p tr rounds s.pending hpending]⟩ := by rw [hbase]
  have hwindowChronological :
      (secondPositiveWindow p tr rounds s.pending hpending).Pairwise
        (fun e₁ e₂ => e₁.time.val < e₂.time.val) := by
    have hpositives : (AffineBatchDecoder.positives p tr rounds).Pairwise
        (fun e₁ e₂ => e₁.time.val < e₂.time.val) := by
      classical
      change (((rounds.filter (fun t => decide (AffineBatchDecoder.eligible (tr t)))).map
        (AffineBatchDecoder.entry p tr)).Pairwise
          (fun e₁ e₂ => e₁.time.val < e₂.time.val))
      apply List.pairwise_map.mpr
      simpa only [AffineBatchDecoder.entry, AffineBatchDecoder.Entry.time] using
        hchronological.filter _
    change ((AffineBatchDecoder.positives p tr rounds).drop
      (AffineBatchDecoder.quota p - s.pending.length)).Pairwise _
    apply List.Pairwise.sublist (List.drop_sublist _ _)
    exact hpositives
  have hpendingDisjoint : ∀ e ∈ s.pending,
      e ∉ secondPositiveWindow p tr rounds s.pending hpending := by
    intro e heold hewindow
    have hepositive : e ∈ AffineBatchDecoder.positives p tr rounds :=
      mem_of_mem_drop_list _ _ hewindow
    obtain ⟨ht, _, _⟩ :=
      (AffineBatchDecoder.mem_positives_iff p tr rounds e).mp hepositive
    exact (Nat.lt_irrefl e.time.val) (hpendingOlder e heold e.time ht)
  refine ⟨first, hrun, hfirst, hfirstLen, hwindowLen,
    hwindowChronological, hpendingDisjoint, ?_⟩
  omega

private theorem unique_window_decodes
    (p : ConstructorDimensions.Parameters) (beta : ℝ)
    (dir : OrdinaryMessageCodec.Direction)
    (window : List (AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p)))
    (x : OrdinaryMessageCodec.MessageRecord (AffineBatchDecoder.codecParams p beta) dir)
    (hequation : ∀ e ∈ window, AffineBatchDecoder.equation e.sample
      (OrdinaryMessageCodec.wordEquivFlat (AffineBatchDecoder.codecParams p beta)
        (OrdinaryMessageCodec.encode (AffineBatchDecoder.codecParams p beta) dir x)))
    (hunique : ∃! v, AffineBatchDecoder.satisfies
      (AffineBatchDecoder.samples window) v) :
    AffineBatchDecoder.batchOutput window = some
        (OrdinaryMessageCodec.wordEquivFlat (AffineBatchDecoder.codecParams p beta)
          (OrdinaryMessageCodec.encode (AffineBatchDecoder.codecParams p beta) dir x)) ∧
      AffineBatchDecoder.parseBatch p beta dir (AffineBatchDecoder.samples window) = some x := by
  let word := OrdinaryMessageCodec.wordEquivFlat (AffineBatchDecoder.codecParams p beta)
    (OrdinaryMessageCodec.encode (AffineBatchDecoder.codecParams p beta) dir x)
  have hsolution : ∀ v, (∀ e ∈ window, AffineBatchDecoder.equation e.sample v) → v = word := by
    intro v hv
    have hvsat : AffineBatchDecoder.satisfies (AffineBatchDecoder.samples window) v :=
      (AffineBatchDecoder.satisfies_samples_iff window v).2 hv
    have hwordsat : AffineBatchDecoder.satisfies (AffineBatchDecoder.samples window) word :=
      (AffineBatchDecoder.satisfies_samples_iff window word).2 (by
        intro e he
        exact hequation e he)
    rcases hunique with ⟨witness, hwitness, huniqueWitness⟩
    have hvwitness : v = witness := huniqueWitness v hvsat
    have hwordWitness : word = witness := huniqueWitness word hwordsat
    exact hvwitness.trans hwordWitness.symm
  have houtput : AffineBatchDecoder.batchOutput window = some word :=
    (AffineBatchDecoder.batchOutput_eq_some_iff window word).2
      ⟨hequation, hsolution⟩
  have hsolve : AffineBatchDecoder.solve (AffineBatchDecoder.samples window) = some word := by
    simpa only [AffineBatchDecoder.batchOutput] using houtput
  refine ⟨houtput, ?_⟩
  exact (AffineBatchDecoder.parseBatch_eq_some_iff p beta dir
    (AffineBatchDecoder.samples window) x).2 hsolve

private theorem down_positive_entry_equation
    (p : ConstructorDimensions.Parameters) (beta : ℝ)
    (a : Assignment p.m p.K)
    (liveRounds : Fin p.T → LiveRoundData a (AffineBatchDecoder.width p))
    (i : Follower p.m) (rounds : List (Fin p.T))
    (x : OrdinaryMessageCodec.MessageRecord (AffineBatchDecoder.codecParams p beta)
      .DOWN)
    (e : AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p))
    (he : e ∈ AffineBatchDecoder.positives p
      (ActiveObservationBridge.downObservationTrace p a liveRounds i) rounds)
    (hfixed : ∀ e ∈ AffineBatchDecoder.positives p
        (ActiveObservationBridge.downObservationTrace p a liveRounds i) rounds,
      (liveRounds e.time).input.down.word =
        OrdinaryMessageCodec.wordEquivFlat (AffineBatchDecoder.codecParams p beta)
          (OrdinaryMessageCodec.encode (AffineBatchDecoder.codecParams p beta) .DOWN x)) :
    AffineBatchDecoder.equation e.sample
      (OrdinaryMessageCodec.wordEquivFlat (AffineBatchDecoder.codecParams p beta)
        (OrdinaryMessageCodec.encode (AffineBatchDecoder.codecParams p beta) .DOWN x)) := by
  obtain ⟨_, heligible, hsample⟩ :=
    (AffineBatchDecoder.mem_positives_iff p
      (ActiveObservationBridge.downObservationTrace p a liveRounds i) rounds e).mp he
  change (ActiveObservationBridge.downObservationTrace p a liveRounds i e.time).selected = true ∧
    (ActiveObservationBridge.downObservationTrace p a liveRounds i e.time).receiverEnabled = true ∧
    0 < (ActiveObservationBridge.downObservationTrace p a liveRounds i e.time).roundedReward
      at heligible
  have hselected := heligible.1
  have hreceiver := heligible.2.1
  have hpositive := heligible.2.2
  have hsource : (liveRounds e.time).input.slot = downSlot ∧
      (liveRounds e.time).input.selected = i ∧
      i ∈ (ActiveObservationBridge.liveSnapshotBefore p a liveRounds e.time).missing := by
    simpa only [ActiveObservationBridge.downObservationTrace, decide_eq_true_eq] using hselected
  have hstatus :
      (ActiveObservationBridge.liveSnapshotBefore p a liveRounds e.time).status i = .unoccupied := by
    simpa only [ActiveObservationBridge.downObservationTrace, decide_eq_true_eq] using hreceiver
  have hphysical := ActiveObservationBridge.live_unoccupied_down_positive_equation
    p a liveRounds e.time i hsource.1 hsource.2.1 hsource.2.2 hstatus (by
      simpa only [ActiveObservationBridge.downObservationTrace,
        ActiveObservationBridge.liveSnapshotBefore] using hpositive)
  have hsampleActual : e.sample = (liveRounds e.time).input.down.sample := by
    simpa only [ActiveObservationBridge.downObservationTrace] using hsample
  rw [hfixed e he] at hphysical
  rw [← hsampleActual] at hphysical
  exact hphysical

private theorem up_positive_entry_equation
    (p : ConstructorDimensions.Parameters) (beta : ℝ)
    (a : Assignment p.m p.K)
    (liveRounds : Fin p.T → LiveRoundData a (AffineBatchDecoder.width p))
    (i : Follower p.m) (cutoff : ℕ)
    (upPending : Fin p.T → Finset (Follower p.m)) (rounds : List (Fin p.T))
    (x : OrdinaryMessageCodec.MessageRecord (AffineBatchDecoder.codecParams p beta)
      .UP)
    (e : AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p))
    (he : e ∈ AffineBatchDecoder.positives p
      (upObservationTrace p a liveRounds i cutoff upPending) rounds)
    (hfixed : ∀ e ∈ AffineBatchDecoder.positives p
        (upObservationTrace p a liveRounds i cutoff upPending) rounds,
      (liveRounds e.time).input.up.word =
        OrdinaryMessageCodec.wordEquivFlat (AffineBatchDecoder.codecParams p beta)
          (OrdinaryMessageCodec.encode (AffineBatchDecoder.codecParams p beta) .UP x)) :
    AffineBatchDecoder.equation e.sample
      (OrdinaryMessageCodec.wordEquivFlat (AffineBatchDecoder.codecParams p beta)
        (OrdinaryMessageCodec.encode (AffineBatchDecoder.codecParams p beta) .UP x)) := by
  obtain ⟨_, heligible, hsample⟩ :=
    (AffineBatchDecoder.mem_positives_iff p
      (upObservationTrace p a liveRounds i cutoff upPending) rounds e).mp he
  have hsource := upObservationTrace_eligible_source_conditions p a liveRounds i cutoff
    upPending e.time heligible
  have hphysical := ActiveObservationBridge.live_unoccupied_up_positive_equation
    p a liveRounds e.time i hsource.2.2.1 hsource.2.2.2.1 hsource.2.2.2.2.1
    hsource.2.2.2.2.2.1 hsource.2.2.2.2.2.2
  have hsampleActual : e.sample = (liveRounds e.time).input.up.sample := by
    simpa only [upObservationTrace] using hsample
  rw [hfixed e he] at hphysical
  rw [← hsampleActual] at hphysical
  exact hphysical

private theorem window_entries_satisfy
    (p : ConstructorDimensions.Parameters) (tr : AffineBatchDecoder.Trace p)
    (rounds : List (Fin p.T))
    (pending : List (AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p)))
    (hpending : pending.length < AffineBatchDecoder.quota p)
    (word : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (hpositive : ∀ e ∈ AffineBatchDecoder.positives p tr rounds,
      AffineBatchDecoder.equation e.sample word) :
    ∀ e ∈ secondPositiveWindow p tr rounds pending hpending,
      AffineBatchDecoder.equation e.sample word := by
  intro e he
  exact hpositive e (mem_of_mem_drop_list _ _ he)

/-- DOWN acceptance after the deterministic two-batch window. The count, word
persistence, concrete-batch uniqueness, and local receiver inequalities are
explicit inputs. Physical equations are proved from the live DOWN observations.
The local inequalities are precisely `sigma_i < x.sigma ≤ decision round` from
the manuscript acceptance test. -/
theorem down_acceptance_window
    (p : ConstructorDimensions.Parameters) (beta : ℝ)
    (a : Assignment p.m p.K)
    (liveRounds : Fin p.T → LiveRoundData a (AffineBatchDecoder.width p))
    (i : Follower p.m) (rounds : List (Fin p.T))
    (s : AffineBatchDecoder.State p.T (AffineBatchDecoder.width p))
    (x : OrdinaryMessageCodec.MessageRecord (AffineBatchDecoder.codecParams p beta)
      .DOWN)
    (hpending : s.pending.length < AffineBatchDecoder.quota p)
    (hcount : (AffineBatchDecoder.positives p
      (ActiveObservationBridge.downObservationTrace p a liveRounds i) rounds).length =
        AffineBatchDecoder.quota p - s.pending.length + AffineBatchDecoder.quota p)
    (hchronological : rounds.Pairwise (fun t₁ t₂ => t₁.val < t₂.val))
    (hpendingOlder : ∀ e ∈ s.pending, ∀ t ∈ rounds, e.time.val < t.val)
    (hfixed : ∀ e ∈ AffineBatchDecoder.positives p
        (ActiveObservationBridge.downObservationTrace p a liveRounds i) rounds,
      (liveRounds e.time).input.down.word =
        OrdinaryMessageCodec.wordEquivFlat (AffineBatchDecoder.codecParams p beta)
          (OrdinaryMessageCodec.encode (AffineBatchDecoder.codecParams p beta) .DOWN x))
    (hunique : ∃! v, AffineBatchDecoder.satisfies
      (AffineBatchDecoder.samples (secondPositiveWindow p
        (ActiveObservationBridge.downObservationTrace p a liveRounds i) rounds
        s.pending hpending)) v)
    (sigmaOld : ℕ)
    (hlocal : ∀ t,
      AffineBatchDecoder.decisionTime (secondPositiveWindow p
        (ActiveObservationBridge.downObservationTrace p a liveRounds i) rounds
        s.pending hpending) = some t →
        sigmaOld < x.val.sigma ∧ x.val.sigma ≤ sourceRound t) :
    ∃ first t,
      AffineBatchDecoder.run p (ActiveObservationBridge.downObservationTrace p a liveRounds i)
          rounds s = ⟨[], s.completed ++ [first, secondPositiveWindow p
            (ActiveObservationBridge.downObservationTrace p a liveRounds i) rounds
            s.pending hpending]⟩ ∧
      first = s.pending ++ (AffineBatchDecoder.positives p
        (ActiveObservationBridge.downObservationTrace p a liveRounds i) rounds).take
          (AffineBatchDecoder.quota p - s.pending.length) ∧
      first.length = AffineBatchDecoder.quota p ∧
      (secondPositiveWindow p (ActiveObservationBridge.downObservationTrace p a liveRounds i)
        rounds s.pending hpending).length = AffineBatchDecoder.quota p ∧
      (secondPositiveWindow p (ActiveObservationBridge.downObservationTrace p a liveRounds i)
        rounds s.pending hpending).Pairwise (fun e₁ e₂ => e₁.time.val < e₂.time.val) ∧
      (∀ e ∈ s.pending, e ∉ secondPositiveWindow p
        (ActiveObservationBridge.downObservationTrace p a liveRounds i) rounds
        s.pending hpending) ∧
      (AffineBatchDecoder.positives p
        (ActiveObservationBridge.downObservationTrace p a liveRounds i) rounds).length ≤
          2 * AffineBatchDecoder.quota p ∧
      (∀ e ∈ secondPositiveWindow p (ActiveObservationBridge.downObservationTrace p a liveRounds i)
        rounds s.pending hpending,
        AffineBatchDecoder.equation e.sample
          (OrdinaryMessageCodec.wordEquivFlat (AffineBatchDecoder.codecParams p beta)
            (OrdinaryMessageCodec.encode (AffineBatchDecoder.codecParams p beta) .DOWN x))) ∧
      AffineBatchDecoder.batchOutput (secondPositiveWindow p
        (ActiveObservationBridge.downObservationTrace p a liveRounds i) rounds s.pending hpending) =
        some (OrdinaryMessageCodec.wordEquivFlat (AffineBatchDecoder.codecParams p beta)
          (OrdinaryMessageCodec.encode (AffineBatchDecoder.codecParams p beta) .DOWN x)) ∧
      AffineBatchDecoder.parseBatch p beta .DOWN
        (AffineBatchDecoder.samples (secondPositiveWindow p
          (ActiveObservationBridge.downObservationTrace p a liveRounds i) rounds
          s.pending hpending)) = some x ∧
      AffineBatchDecoder.decisionTime (secondPositiveWindow p
        (ActiveObservationBridge.downObservationTrace p a liveRounds i) rounds
        s.pending hpending) = some t ∧
      OrdinaryMessageCodec.acceptDown (AffineBatchDecoder.codecParams p beta)
        sigmaOld (sourceRound t) x := by
  let trace := ActiveObservationBridge.downObservationTrace p a liveRounds i
  let window := secondPositiveWindow p trace rounds s.pending hpending
  obtain ⟨first, hrun, hfirst, hfirstLen, hwindowLen, hwindowChronological,
      hpendingDisjoint, hcountLe⟩ :=
    run_two_batch_window p trace rounds s hpending hcount hchronological hpendingOlder
  have hequation : ∀ e ∈ window, AffineBatchDecoder.equation e.sample
      (OrdinaryMessageCodec.wordEquivFlat (AffineBatchDecoder.codecParams p beta)
        (OrdinaryMessageCodec.encode (AffineBatchDecoder.codecParams p beta) .DOWN x)) := by
    apply window_entries_satisfy p trace rounds s.pending hpending _
    intro e he
    exact down_positive_entry_equation p beta a liveRounds i rounds x e he hfixed
  obtain ⟨houtput, hparse⟩ := unique_window_decodes p beta .DOWN window x hequation hunique
  have hnonempty : window ≠ [] := by
    intro hnil
    simp [window, hnil] at hwindowLen
    omega
  let last := window.getLast hnonempty
  have hdecision : AffineBatchDecoder.decisionTime window = some last.time := by
    simp only [last, window, AffineBatchDecoder.decisionTime, List.getLast?_map,
      List.getLast?_eq_some_getLast hnonempty, Option.map_some]
  have hlocalLast := hlocal last.time hdecision
  refine ⟨first, last.time, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hequation,
    houtput, hparse, hdecision, ?_⟩
  · simpa only [trace] using hrun
  · simpa only [window, trace] using hfirst
  · exact hfirstLen
  · exact hwindowLen
  · exact hwindowChronological
  · exact hpendingDisjoint
  · exact hcountLe
  · exact ⟨hlocalLast.1, hlocalLast.2⟩

/-- UP acceptance after the deterministic two-batch window. The local clock and
current pending set are read from the final eligible UP round. The equality of
the UP record's sigma with the current DOWN record's sigma is explicit; the
valid current DOWN record itself proves that this sigma is at least one, which
excludes the UP placeholder. -/
theorem up_acceptance_window
    (p : ConstructorDimensions.Parameters) (beta : ℝ)
    (a : Assignment p.m p.K)
    (liveRounds : Fin p.T → LiveRoundData a (AffineBatchDecoder.width p))
    (i : Follower p.m) (cutoff : ℕ)
    (upPending : Fin p.T → Finset (Follower p.m)) (rounds : List (Fin p.T))
    (s : AffineBatchDecoder.State p.T (AffineBatchDecoder.width p))
    (x : OrdinaryMessageCodec.MessageRecord (AffineBatchDecoder.codecParams p beta)
      .UP)
    (currentDown : OrdinaryMessageCodec.DownRecord (AffineBatchDecoder.codecParams p beta))
    (hcurrentSigma : x.val.sigma = currentDown.val.sigma)
    (hpending : s.pending.length < AffineBatchDecoder.quota p)
    (hcount : (AffineBatchDecoder.positives p
      (upObservationTrace p a liveRounds i cutoff upPending) rounds).length =
        AffineBatchDecoder.quota p - s.pending.length + AffineBatchDecoder.quota p)
    (hchronological : rounds.Pairwise (fun t₁ t₂ => t₁.val < t₂.val))
    (hpendingOlder : ∀ e ∈ s.pending, ∀ t ∈ rounds, e.time.val < t.val)
    (hfixed : ∀ e ∈ AffineBatchDecoder.positives p
        (upObservationTrace p a liveRounds i cutoff upPending) rounds,
      (liveRounds e.time).input.up.word =
        OrdinaryMessageCodec.wordEquivFlat (AffineBatchDecoder.codecParams p beta)
          (OrdinaryMessageCodec.encode (AffineBatchDecoder.codecParams p beta) .UP x))
    (hunique : ∃! v, AffineBatchDecoder.satisfies
      (AffineBatchDecoder.samples (secondPositiveWindow p
        (upObservationTrace p a liveRounds i cutoff upPending) rounds
        s.pending hpending)) v) :
    ∃ first t,
      AffineBatchDecoder.run p (upObservationTrace p a liveRounds i cutoff upPending)
          rounds s = ⟨[], s.completed ++ [first, secondPositiveWindow p
            (upObservationTrace p a liveRounds i cutoff upPending) rounds
            s.pending hpending]⟩ ∧
      first = s.pending ++ (AffineBatchDecoder.positives p
        (upObservationTrace p a liveRounds i cutoff upPending) rounds).take
          (AffineBatchDecoder.quota p - s.pending.length) ∧
      first.length = AffineBatchDecoder.quota p ∧
      (secondPositiveWindow p (upObservationTrace p a liveRounds i cutoff upPending)
        rounds s.pending hpending).length = AffineBatchDecoder.quota p ∧
      (secondPositiveWindow p (upObservationTrace p a liveRounds i cutoff upPending)
        rounds s.pending hpending).Pairwise (fun e₁ e₂ => e₁.time.val < e₂.time.val) ∧
      (∀ e ∈ s.pending, e ∉ secondPositiveWindow p
        (upObservationTrace p a liveRounds i cutoff upPending) rounds
        s.pending hpending) ∧
      (AffineBatchDecoder.positives p
        (upObservationTrace p a liveRounds i cutoff upPending) rounds).length ≤
          2 * AffineBatchDecoder.quota p ∧
      (∀ e ∈ secondPositiveWindow p (upObservationTrace p a liveRounds i cutoff upPending)
        rounds s.pending hpending,
        AffineBatchDecoder.equation e.sample
          (OrdinaryMessageCodec.wordEquivFlat (AffineBatchDecoder.codecParams p beta)
            (OrdinaryMessageCodec.encode (AffineBatchDecoder.codecParams p beta) .UP x))) ∧
      AffineBatchDecoder.batchOutput (secondPositiveWindow p
        (upObservationTrace p a liveRounds i cutoff upPending) rounds s.pending hpending) =
        some (OrdinaryMessageCodec.wordEquivFlat (AffineBatchDecoder.codecParams p beta)
          (OrdinaryMessageCodec.encode (AffineBatchDecoder.codecParams p beta) .UP x)) ∧
      AffineBatchDecoder.parseBatch p beta .UP
        (AffineBatchDecoder.samples (secondPositiveWindow p
          (upObservationTrace p a liveRounds i cutoff upPending) rounds
          s.pending hpending)) = some x ∧
      AffineBatchDecoder.decisionTime (secondPositiveWindow p
        (upObservationTrace p a liveRounds i cutoff upPending) rounds
        s.pending hpending) = some t ∧
      OrdinaryMessageCodec.acceptUp (AffineBatchDecoder.codecParams p beta)
        cutoff (sourceRound t) (sourceFollowerId i)
        (sourcePendingSet (upPending t)) currentDown.val.sigma x ∧
      1 ≤ currentDown.val.sigma ∧ x.val ≠ OrdinaryMessageCodec.upPlaceholder := by
  let trace := upObservationTrace p a liveRounds i cutoff upPending
  let window := secondPositiveWindow p trace rounds s.pending hpending
  obtain ⟨first, hrun, hfirst, hfirstLen, hwindowLen, hwindowChronological,
      hpendingDisjoint, hcountLe⟩ :=
    run_two_batch_window p trace rounds s hpending hcount hchronological hpendingOlder
  have hequation : ∀ e ∈ window, AffineBatchDecoder.equation e.sample
      (OrdinaryMessageCodec.wordEquivFlat (AffineBatchDecoder.codecParams p beta)
        (OrdinaryMessageCodec.encode (AffineBatchDecoder.codecParams p beta) .UP x)) := by
    apply window_entries_satisfy p trace rounds s.pending hpending _
    intro e he
    exact up_positive_entry_equation p beta a liveRounds i cutoff upPending rounds x e he hfixed
  obtain ⟨houtput, hparse⟩ := unique_window_decodes p beta .UP window x hequation hunique
  have hnonempty : window ≠ [] := by
    intro hnil
    simp [window, hnil] at hwindowLen
    omega
  let last := window.getLast hnonempty
  have hdecision : AffineBatchDecoder.decisionTime window = some last.time := by
    simp only [last, window, AffineBatchDecoder.decisionTime, List.getLast?_map,
      List.getLast?_eq_some_getLast hnonempty, Option.map_some]
  have hlastWindow : last ∈ window := by
    simp only [last]
    exact List.getLast_mem hnonempty
  have hlastPositive : last ∈ AffineBatchDecoder.positives p trace rounds := by
    exact mem_of_mem_drop_list _ _ hlastWindow
  obtain ⟨_, hlastEligible, _⟩ :=
    (AffineBatchDecoder.mem_positives_iff p trace rounds last).mp hlastPositive
  have hsource := upObservationTrace_eligible_source_conditions p a liveRounds i cutoff
    upPending last.time hlastEligible
  have hcurrentPositive : 1 ≤ currentDown.val.sigma := currentDown.property.1
  have hnotPlaceholder : x.val ≠ OrdinaryMessageCodec.upPlaceholder := by
    intro hplaceholder
    have hzero : x.val.sigma = 0 := by
      rw [hplaceholder]
      rfl
    rw [hcurrentSigma] at hzero
    omega
  have haccepted : OrdinaryMessageCodec.acceptUp (AffineBatchDecoder.codecParams p beta)
      cutoff (sourceRound last.time) (sourceFollowerId i)
      (sourcePendingSet (upPending last.time)) currentDown.val.sigma x := by
    unfold OrdinaryMessageCodec.acceptUp
    refine ⟨hsource.1, ?_, hcurrentSigma⟩
    exact (sourceFollowerId_mem_sourcePendingSet_iff (upPending last.time) i).2 hsource.2.1
  refine ⟨first, last.time, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hequation,
    houtput, hparse, hdecision, haccepted, hcurrentPositive, hnotPlaceholder⟩
  · simpa only [trace] using hrun
  · simpa only [window, trace] using hfirst
  · exact hfirstLen
  · exact hwindowLen
  · exact hwindowChronological
  · exact hpendingDisjoint
  · exact hcountLe

end Bandits.Support.WaitedWordWindow

end
