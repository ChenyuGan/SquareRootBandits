/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ActualReferenceInitializationBlock
public import Bandits.Support.InitializationFailureProvenance

/-!
# One actual initialization block and its generated reference block

Internal deterministic comparisons, using the original source coordinates and
`ActualInitializationRun.foldBlockAux`; no second physical execution is defined.
Sources: `sources/zip4/manuscript/07_public_setup.tex:63-115,123-164`,
`appendix_b_communication.tex:94-165`, and `08_main_theorem.tex:29-42`.

`foldBlock_related` discharges the per-round replay conditions from the honest
prior `BlockStartRelated` and the accepted `generatedBlockDown` complement.
`foldBlock_bootstrap_comparison` additionally uses the accepted literal virtual
incorrect-row prefix-pass complement: the forward obstruction remains separate
from initialization failure. `foldBlock_past_related` and
`foldBlock_declared_comparison` identify the generated histories and retained
ordinary states. The original all-candidate register recursion supplies the
actual saved row, and the full all-slot stay gain supplies its weight update.

This file completes the physical fold induction, before its boundary adapter.
The remaining consumer must compare actual `countersAfterObservation` with
reference `updatedCounters`, derive strict crossing after pending saves, and
compare `combinedBoundaryHandoff` with `finishBlock`, including the next
`BlockStartRelated`, zero launch seed and terminal exhaustion or a crossing at
`T + 1`. No physical sentinel action, horizon coupling, global event,
probability estimate, source-facing anchor or manuscript closure is claimed.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ActualReferenceInitializationFold

open ConstructorDimensions BootstrapDimensions ActiveRoundActions
open ReferencePrelaunchFollower ActualReferenceInitializationBlock ActiveFollowerDownAcceptance
open scoped Classical

variable {p : Parameters}

/-- Full stay gain through a calendar prefix. Pending candidate saves and the
candidate's DATA restriction do not occur in this literal count. -/
def gainPrefix {s : Fin (n_boot p)} (v : BootstrapPhysicalBlock.Input p s)
    (i : {i // i ∈ v.uninformed}) (k : ℕ) : ℕ :=
  ((BootstrapPhysicalBlock.physicalStayRounds v i).filter fun t => t.val < k).card

theorem gainPrefix_start {s : Fin (n_boot p)} (v : BootstrapPhysicalBlock.Input p s)
    (i : {i // i ∈ v.uninformed}) :
    gainPrefix v i (BootstrapObservedFollower.blockStart p s) = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro t ht
  obtain ⟨ht, hlt⟩ := Finset.mem_filter.mp ht
  have hmem := (Finset.mem_filter.mp ht).1
  have hstart := (mem_calendarBlock_iff p s t).mp hmem
  exact Nat.not_lt_of_ge hstart.1 hlt

theorem gainPrefix_succ {s : Fin (n_boot p)} (v : BootstrapPhysicalBlock.Input p s)
    (i : {i // i ∈ v.uninformed}) (t : Fin p.T) (ht : t ∈ calendarBlock p s) :
    gainPrefix v i (t.val + 1) =
      if BootstrapObservedFollower.positiveStay v.ids (v.privateId i) t
          (BootstrapObservedFollower.physicalObservation v i t)
      then gainPrefix v i t.val + 1 else gainPrefix v i t.val := by
  have hm : t ∈ BootstrapPhysicalBlock.physicalStayRounds v i ↔
      BootstrapObservedFollower.positiveStay v.ids (v.privateId i) t
        (BootstrapObservedFollower.physicalObservation v i t) := by
    simp only [BootstrapPhysicalBlock.physicalStayRounds, Finset.mem_filter,
      ht, true_and, BootstrapObservedFollower.positiveStay,
      BootstrapObservedFollower.physicalObservation_value]
  have hset : (BootstrapPhysicalBlock.physicalStayRounds v i).filter
      (fun u => u.val < t.val + 1) =
      if t ∈ BootstrapPhysicalBlock.physicalStayRounds v i then
        insert t ((BootstrapPhysicalBlock.physicalStayRounds v i).filter fun u => u.val < t.val)
      else (BootstrapPhysicalBlock.physicalStayRounds v i).filter fun u => u.val < t.val := by
    ext u
    by_cases he : t ∈ BootstrapPhysicalBlock.physicalStayRounds v i
    · simp only [he, ite_true, Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨hu, hlt⟩
        by_cases hut : u = t
        · exact Or.inl hut
        · exact Or.inr ⟨hu, by have := Fin.val_ne_of_ne hut; omega⟩
      · rintro (rfl | ⟨hu, hlt⟩)
        · exact ⟨he, Nat.lt_succ_self _⟩
        · exact ⟨hu, Nat.lt_succ_of_lt hlt⟩
    · simp only [he, ite_false, Finset.mem_filter]
      constructor
      · rintro ⟨hu, hlt⟩
        have hne : u.val ≠ t.val := fun hh => he (Fin.ext hh ▸ hu)
        exact ⟨hu, by omega⟩
      · rintro ⟨hu, hlt⟩
        exact ⟨hu, Nat.lt_succ_of_lt hlt⟩
  unfold gainPrefix
  rw [hset]
  by_cases he : t ∈ BootstrapPhysicalBlock.physicalStayRounds v i
  · rw [ite_eq_left he, ite_eq_left (hm.mp he), Finset.card_insert_of_notMem]
    simp only [Finset.mem_filter, lt_self_iff_false, and_false, not_false_eq_true]
  · rw [ite_eq_right he, ite_eq_right (fun hp => he (hm.mpr hp))]

theorem gainPrefix_end {s : Fin (n_boot p)} (v : BootstrapPhysicalBlock.Input p s)
    (i : {i // i ∈ v.uninformed}) (ha : v.active i = true) :
    gainPrefix v i (BootstrapObservedFollower.blockStop p s) =
      BootstrapPhysicalBlock.physicalStayGain v i := by
  rw [BootstrapPhysicalBlock.physicalStayGain, ite_eq_left ha]
  unfold gainPrefix
  congr 1
  apply Finset.filter_eq_self.mpr
  intro t ht
  exact ((mem_calendarBlock_iff p s t).mp (Finset.mem_filter.mp ht).1).2

/-- The exact all-candidate registers and full gain of an uninformed follower.
The original sampled activity, held arm, ID and numerator vector are retained. -/
def startup_prefix_related {s : Fin (n_boot p)} (v : BootstrapPhysicalBlock.Input p s)
    (rows : CompletePublicTable.CompleteRows p) (i : {i // i ∈ v.uninformed})
    (numerators : Fin p.K → ℕ) (k : ℕ)
    (state : BootstrapObservedFollower.StartupState p s) : Prop :=
  state.numerators = numerators ∧
    state.blockCase = if v.active i then
      .active (v.held i) (v.privateId i) (gainPrefix v i k)
        (BootstrapAllCandidateController.run v rows i k)
    else .inactive

theorem startup_prefix_draws {s : Fin (n_boot p)} (v : BootstrapPhysicalBlock.Input p s)
    (rows : CompletePublicTable.CompleteRows p) (i : {i // i ∈ v.uninformed})
    (numerators : Fin p.K → ℕ) (k : ℕ)
    (state : BootstrapObservedFollower.StartupState p s)
    (hr : startup_prefix_related v rows i numerators k state) :
    startup_draws_related v i state := by
  unfold startup_draws_related
  rw [hr.2]
  cases ha : v.active i with
  | false => simp only [Bool.false_eq_true, ite_false]
  | true => simp only [ite_true, and_self]

/-- Both candidate controllers are reset before the first real block round. -/
theorem allCandidate_run_start {s : Fin (n_boot p)} (v : BootstrapPhysicalBlock.Input p s)
    (rows : CompletePublicTable.CompleteRows p) (i : {i // i ∈ v.uninformed}) :
    BootstrapAllCandidateController.run v rows i (BootstrapObservedFollower.blockStart p s) =
      BootstrapAllCandidateController.initialRegisters p := by
  have hb : BootstrapObservedFollower.blockStart p s ≤ p.T :=
    ReferencePrelaunchPhysicalReplay.blockStart_le_T p s
  generalize hk : BootstrapObservedFollower.blockStart p s = k
  have aux : ∀ n, n ≤ k → BootstrapAllCandidateController.run v rows i n =
      BootstrapAllCandidateController.initialRegisters p := by
    intro n hn
    induction n with
    | zero => rfl
    | succ n ih =>
        let t : Fin p.T := ⟨n, by omega⟩
        have ht : t ∉ calendarBlock p s := by
          intro hm
          have hstart := ((mem_calendarBlock_iff p s t).mp hm).1
          change BootstrapObservedFollower.blockStart p s ≤ n at hstart
          omega
        rw [show n + 1 = t.val + 1 from rfl,
          BootstrapAllCandidateController.run_succ,
          BootstrapAllCandidateController.advance_eq_of_outside_block v rows i _ t ht]
        exact ih (by omega)
  exact aux k le_rfl

/-- Readiness at any interior cursor comes from the accepted actual invariant. -/
theorem ready_of_invariant (rate : RateInput p) (s : Fin (n_boot p))
    (source : BootstrapPrivateRoundStreams.SourceInput p) (C_star C_h : ℝ)
    (cursor : ℕ) (hc : cursor < BootstrapObservedFollower.blockLength p s)
    (coord : BootstrapCoordinatorLocalRound.PrelaunchBlock p)
    (followers : Fin (p.m - 1) → ActualInitializationPhysicalStep.FollowerState p rate s)
    (hi : ActualInitializationRun.BlockInvariant p rate s source C_star C_h cursor
      (.prelaunch coord) followers) :
    ActualInitializationPhysicalStep.ActualInputReady p rate s
      (ActualInitializationRun.blockTime p s cursor hc) coord followers source := by
  refine ⟨hi.1.1, ActualInitializationRun.blockTime_mem p s cursor hc,
    hi.1.2.1, hi.1.2.2.1, hi.1.2.2.2.1, ?_⟩
  intro i
  have hf := hi.2.2.1 i
  generalize he : followers i = f at hf ⊢
  cases f with
  | bootstrap state =>
      change state.processed.val = cursor at hf
      refine ⟨ActualInitializationRun.blockTime_mem p s cursor hc, ?_, ?_⟩
      · rw [hf]; exact hc
      · change BootstrapObservedFollower.blockStart p s + cursor =
          BootstrapObservedFollower.blockStart p s + state.processed.val
        rw [hf]
  | declared row activation configuration => exact hf

/-- Unfolding equation for the EXISTING actual recursion. Its next invariant
is the proof already constructed by that recursion. -/
theorem foldBlockAux_succ (rate : RateInput p) (s : Fin (n_boot p))
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (cursor fuel : ℕ) (hb : cursor + (fuel + 1) = BootstrapObservedFollower.blockLength p s)
    (coord : BootstrapCoordinatorLocalRound.PrelaunchBlock p)
    (followers : Fin (p.m - 1) → ActualInitializationPhysicalStep.FollowerState p rate s)
    (hi : ActualInitializationRun.BlockInvariant p rate s source C_star C_h cursor
      (.prelaunch coord) followers) :
    let hc : cursor < BootstrapObservedFollower.blockLength p s := by omega
    let record := executeAt rate s (ActualInitializationRun.blockTime p s cursor hc)
      coord followers source rewards (ready_of_invariant rate s source C_star C_h cursor hc coord followers hi)
    ∃ hnext : ActualInitializationRun.BlockInvariant p rate s source C_star C_h (cursor + 1)
        record.result.coordinator.next (fun i => (record.result.followers i).next),
      let tail := ActualInitializationRun.foldBlockAux p rate s source rewards C_star C_h
        (cursor + 1) fuel (by omega) record.result.coordinator.next
        (fun i => (record.result.followers i).next) hnext
      let whole := ActualInitializationRun.foldBlockAux p rate s source rewards C_star C_h
        cursor (fuel + 1) hb (.prelaunch coord) followers hi
      whole.phase = tail.phase ∧ whole.followers = tail.followers ∧
        whole.records = record :: tail.records := by
  dsimp only
  unfold ActualInitializationRun.foldBlockAux
  dsimp (config := { zeta := false }) only [Nat.casesAuxOn, Nat.add]
  extract_lets +underBinder hc ht ready hct cp prep hp obs res hs fs inv rec tail
  have hrec : rec = executeAt rate s (ActualInitializationRun.blockTime p s cursor hc)
      coord followers source rewards ready := by
    rfl
  refine ⟨?_, ?_⟩
  · exact inv
  · change tail.phase = _ ∧ tail.followers = _ ∧ rec :: tail.records = _
    rw [hrec]
    exact ⟨rfl, rfl, rfl⟩

/-- A restriction of the existing reference extended history to the rounds
strictly before a genuine round in this block. -/
def beforeHistory (x : ReferenceInitializationRun.Input p)
    (b : ReferenceInitializationRun.Boundary p) (h : b.completed < n_boot p)
    (time : Fin p.T) (ht : time ∈ calendarBlock p (ReferenceInitializationRun.nextBlock b h))
    (i : Fin p.m) : LocalHistory p time.val := fun u =>
  ReferenceInitializationRun.extendedHistory x b h i
    ⟨u.val, u.isLt.trans ((mem_calendarBlock_iff p _ time).mp ht).2⟩

/-- Equality of only the accumulated own histories: prior entries come from
the incoming boundary; current-block entries come from its physical block. -/
def histories_related (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (rate : RateInput p)
    (C_star C_h : ℝ) (b : ReferenceInitializationRun.Boundary p)
    (h : b.completed < n_boot p)
    (past : List (ActualInitializationRun.PhysicalRoundRecord p rate source rewards))
    (hn : past.length ≤ p.T) : Prop :=
  ∀ (i : Fin p.m) (u : Fin past.length), recordHistory past i u =
    if hu : u.val < ReferenceInitializationRun.elapsed p b.completed then
      b.history i ⟨u.val, hu⟩
    else ReferenceInitializationRun.ownEntry
      (ReferenceInitializationRun.physical (referenceInput source rewards C_star C_h rate) b h)
      i (calendar hn u)

/-- Stronger follower induction data. The bootstrap branch includes EVERY
candidate register, the unfrozen full gain, and the unchanged numerators. -/
def followers_related (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (rate : RateInput p)
    (C_star C_h : ℝ) (b : ReferenceInitializationRun.Boundary p)
    (h : b.completed < n_boot p)
    (past : List (ActualInitializationRun.PhysicalRoundRecord p rate source rewards))
    (hn : past.length ≤ p.T)
    (followers : Fin (p.m - 1) → ActualInitializationPhysicalStep.FollowerState p rate
      (ReferenceInitializationRun.nextBlock b h)) : Prop :=
  ∀ i, round_follower_related source rewards rate C_star C_h b h past hn i (followers i) ∧
    match followers i with
    | .bootstrap state =>
        ∃ hi : refFollower i ∈ ReferenceInitializationRun.uninformed b,
          startup_prefix_related
            (ReferenceInitializationRun.physical (referenceInput source rewards C_star C_h rate) b h)
            source.1.2 ⟨refFollower i, hi⟩ (b.numerators i) past.length state
    | .declared _ _ _ => True

/-- Induction relation at the EXISTING actual fold cursor. It has no current
action, collision feedback, passing oracle, or assumed successful local check. -/
def cursor_related (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (rate : RateInput p)
    (C_star C_h : ℝ) (b : ReferenceInitializationRun.Boundary p)
    (h : b.completed < n_boot p) (cursor : ℕ)
    (past : List (ActualInitializationRun.PhysicalRoundRecord p rate source rewards))
    (hn : past.length ≤ p.T) (phase : BootstrapCoordinatorLocalRound.Continuation p)
    (followers : Fin (p.m - 1) → ActualInitializationPhysicalStep.FollowerState p rate
      (ReferenceInitializationRun.nextBlock b h)) : Prop :=
  past.length = BootstrapObservedFollower.blockStart p (ReferenceInitializationRun.nextBlock b h) + cursor ∧
    (∀ u : Fin past.length, past[u.val].time.val = u.val) ∧
    histories_related source rewards rate C_star C_h b h past hn ∧
    BootstrapCoordinatorLocalRound.Continuation.coordinatorState phase = BootstrapPhysicalBlock.run
      (ReferenceInitializationRun.physical (referenceInput source rewards C_star C_h rate) b h) past.length ∧
    followers_related source rewards rate C_star C_h b h past hn followers

/-- A prefix relation gives the reference replay of exactly that prefix. -/
theorem replay_eq_beforeHistory
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (rate : RateInput p)
    (C_star C_h : ℝ) (b : ReferenceInitializationRun.Boundary p)
    (h : b.completed < n_boot p)
    (past : List (ActualInitializationRun.PhysicalRoundRecord p rate source rewards))
    (hn : past.length ≤ p.T)
    (hh : histories_related source rewards rate C_star C_h b h past hn)
    (time : Fin p.T) (ht : time ∈ calendarBlock p (ReferenceInitializationRun.nextBlock b h))
    (he : time.val = past.length) (i : Fin (p.m - 1)) (a : Activation p) :
    replay rate.eta i (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)) a
      (recordHistory past (PublicDiscreteDraws.followerPlayer p.two_le_m (refFollower i))) hn =
    replay rate.eta i (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)) a
      (beforeHistory (referenceInput source rewards C_star C_h rate) b h time ht
        (PublicDiscreteDraws.followerPlayer p.two_le_m (refFollower i))) (Nat.le_of_lt time.isLt) := by
  rw [← ReferenceInitializationRun.replay_cast rate.eta i _ a _ hn
    (Nat.le_of_lt time.isLt) he.symm]
  congr 1
  funext u
  rw [hh]
  rfl

/-- The physical relation needed by the accepted one-round seam is a
consequence of the stronger cursor induction data. -/
theorem round_related_of_cursor
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (rate : RateInput p)
    (C_star C_h : ℝ) (b : ReferenceInitializationRun.Boundary p)
    (h : b.completed < n_boot p) (cursor : ℕ)
    (past : List (ActualInitializationRun.PhysicalRoundRecord p rate source rewards))
    (hn : past.length ≤ p.T) (hc : cursor < BootstrapObservedFollower.blockLength p
      (ReferenceInitializationRun.nextBlock b h))
    (coord : BootstrapCoordinatorLocalRound.PrelaunchBlock p)
    (followers : Fin (p.m - 1) → ActualInitializationPhysicalStep.FollowerState p rate
      (ReferenceInitializationRun.nextBlock b h))
    (hi : ActualInitializationRun.BlockInvariant p rate (ReferenceInitializationRun.nextBlock b h)
      source C_star C_h cursor (.prelaunch coord) followers)
    (hr : cursor_related source rewards rate C_star C_h b h cursor past hn
      (.prelaunch coord) followers) :
    round_related source rewards rate C_star C_h b h past hn
      (prepareAt rate _ (ActualInitializationRun.blockTime p _ cursor hc) coord followers
        source rewards (ready_of_invariant rate _ source C_star C_h cursor hc coord followers hi)) := by
  refine ⟨rfl, rfl, hr.1.symm, ?_, fun i => (hr.2.2.2.2 i).1⟩
  change coord.data.coordinator = BootstrapPhysicalBlock.run
    (ReferenceInitializationRun.physical (referenceInput source rewards C_star C_h rate) b h)
    (ActualInitializationRun.blockTime p _ cursor hc).val
  rw [show (ActualInitializationRun.blockTime p _ cursor hc).val = past.length from hr.1.symm]
  exact hr.2.2.2.1

/-- The literal bootstrap initial state agrees with the reference sampler,
zero gain and all-candidate reset at the physical block start. -/
theorem startup_prefix_begin
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (rate : RateInput p)
    (C_star C_h : ℝ) (b : ReferenceInitializationRun.Boundary p)
    (h : b.completed < n_boot p)
    (i : {i // i ∈ (ReferenceInitializationRun.physical
      (referenceInput source rewards C_star C_h rate) b h).uninformed}) :
    startup_prefix_related
      (ReferenceInitializationRun.physical (referenceInput source rewards C_star C_h rate) b h)
      source.1.2 i (b.numerators (BootstrapPhysicalInput.sourceFollowerIndex p i.val))
      (BootstrapObservedFollower.blockStart p (ReferenceInitializationRun.nextBlock b h))
      (BootstrapObservedFollower.beginBlock p (ReferenceInitializationRun.nextBlock b h)
        (b.numerators (BootstrapPhysicalInput.sourceFollowerIndex p i.val)) (b.weight_ge_one (BootstrapPhysicalInput.sourceFollowerIndex p i.val))
        (source.2.1.1 (ReferenceInitializationRun.nextBlock b h) (BootstrapPhysicalInput.sourceFollowerIndex p i.val))) := by
  let v := ReferenceInitializationRun.physical (referenceInput source rewards C_star C_h rate) b h
  refine ⟨BootstrapObservedFollower.beginBlock_numerators p _ _ _ _, ?_⟩
  rw [gainPrefix_start, allCandidate_run_start]
  cases ha : PrivateSourceStreams.activityScalarDraw p
      (source.2.1.1 (ReferenceInitializationRun.nextBlock b h) (BootstrapPhysicalInput.sourceFollowerIndex p i.val)).1 with
  | false =>
      rw [BootstrapObservedFollower.beginBlock_inactive_case p _ _ _ _ ha]
      have ha' : v.active i = false := ha
      rw [ite_eq_right (by rw [ha']; decide)]
  | true =>
      rw [BootstrapObservedFollower.beginBlock_active_case p _ _ _ _ ha]
      rw [ite_eq_left (show v.active i = true from ha)]
      rfl

/-- Proved base of the stronger fold relation, from honest PRIOR boundary
data and the accepted block-start operation. -/
theorem begin_cursor_related
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (rate : RateInput p)
    (C_star C_h : ℝ) (b : ReferenceInitializationRun.Boundary p)
    (h : b.completed < n_boot p)
    (actual : ActualInitializationRun.BlockCarry p rate (ReferenceInitializationRun.nextBlock b h))
    (past : List (ActualInitializationRun.PhysicalRoundRecord p rate source rewards))
    (hr : BlockStartRelated source rewards C_star C_h rate
      (ReferenceInitializationRun.nextBlock b h) actual b past) :
    let started := ActualInitializationRun.beginBlock p rate (ReferenceInitializationRun.nextBlock b h) source actual
    cursor_related source rewards rate C_star C_h b h 0 past
      (by rw [hr.2.2.2.2.2.2.1.choose]; exact ReferenceInitializationRun.elapsed_le_T p _)
      (.prelaunch started.coordinator) started.followers := by
  obtain ⟨hlength, hchron, hhistory⟩ := hr.2.2.2.2.2.2.1
  have hbase := begin_round_related source rewards rate C_star C_h b h actual past hr
  refine ⟨?_, hchron, ?_, ?_, ?_⟩
  · rw [hlength, ReferenceInitializationRun.elapsed_eq_blockStart b h]
    rfl
  · intro i u
    have hu : u.val < ReferenceInitializationRun.elapsed p b.completed := by
      rw [← hlength]; exact u.isLt
    rw [dite_eq_left hu]
    exact (hhistory i (Fin.cast hlength u)).symm
  · rw [← hbase.2.2.1]
    exact hbase.2.2.2.1
  · intro i
    refine ⟨hbase.2.2.2.2 i, ?_⟩
    change (match ActualInitializationRun.beginFollowerBlock p rate
      (ReferenceInitializationRun.nextBlock b h) source i (actual.followers i) with
      | .bootstrap state => _
      | .declared _ _ _ => True)
    have hf := hr.2.2.2.2.2.2.2 i
    generalize he : actual.followers i = f at hf ⊢
    cases f with
    | bootstrap numerators lower =>
        obtain ⟨ha, hnum⟩ := hf
        subst numerators
        have hi := (ReferenceInitializationRun.mem_uninformed b (refFollower i)).mpr ha
        refine ⟨hi, ?_⟩
        rw [hlength, ReferenceInitializationRun.elapsed_eq_blockStart b h]
        exact startup_prefix_begin source rewards rate C_star C_h b h ⟨_, hi⟩
    | declared row activation configuration => trivial

/-- One actual bootstrap continuation carries the entire all-candidate run
and every positive stay gain, including the rounds after a pending save. -/
theorem startup_prefix_step {s : Fin (n_boot p)}
    (v : BootstrapPhysicalBlock.Input p s) (rows : CompletePublicTable.CompleteRows p)
    (i : {i // i ∈ v.uninformed}) (numerators : Fin p.K → ℕ)
    (state next : BootstrapObservedFollower.StartupState p s) (time : Fin p.T)
    (ht : time ∈ calendarBlock p s)
    (hr : startup_prefix_related v rows i numerators time.val state)
    (hn : next.numerators = state.numerators)
    (hc : next.blockCase = match state.blockCase with
      | .inactive => .inactive
      | .active held privateID gain registers =>
          .active held privateID
            (if BootstrapObservedFollower.positiveStay v.ids privateID time
              (BootstrapObservedFollower.physicalObservation v i time) then gain + 1 else gain)
            (BootstrapObservedFollower.observationAdvance p s v.ids rows true privateID registers time
              (BootstrapObservedFollower.physicalObservation v i time))) :
    startup_prefix_related v rows i numerators (time.val + 1) next := by
  refine ⟨hn.trans hr.1, ?_⟩
  rw [hc, hr.2]
  cases ha : v.active i with
  | false => simp only [Bool.false_eq_true, ite_false]
  | true =>
      simp only [ite_true]
      rw [← ha, BootstrapObservedFollower.observationAdvance_eq_accepted,
        ← BootstrapAllCandidateController.run_succ, gainPrefix_succ v i time ht]

/-- Retained ordinary proposal memory; bootstrap and dagger have none. -/
def followerMemory (rate : RateInput p) (s : Fin (n_boot p)) :
    ActualInitializationPhysicalStep.FollowerState p rate s →
      Option (ActiveFollowerLifecycle.LocalMemory p)
  | .declared _ _ (.ordinary _ memory) => some memory
  | _ => none

/-- Preservation of the stronger cursor relation by the accepted physical
round. The excluded predicate is an actual ordinary parse/acceptance on the
GENERATED reference replay; it is not a decoder-success assumption. -/
theorem cursor_related_step
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (rate : RateInput p)
    (C_star C_h : ℝ) (b : ReferenceInitializationRun.Boundary p)
    (h : b.completed < n_boot p) (cursor : ℕ)
    (past : List (ActualInitializationRun.PhysicalRoundRecord p rate source rewards))
    (hn : past.length ≤ p.T) (hc : cursor < BootstrapObservedFollower.blockLength p
      (ReferenceInitializationRun.nextBlock b h))
    (coord : BootstrapCoordinatorLocalRound.PrelaunchBlock p)
    (followers : Fin (p.m - 1) → ActualInitializationPhysicalStep.FollowerState p rate
      (ReferenceInitializationRun.nextBlock b h))
    (hi : ActualInitializationRun.BlockInvariant p rate (ReferenceInitializationRun.nextBlock b h)
      source C_star C_h cursor (.prelaunch coord) followers)
    (hr : cursor_related source rewards rate C_star C_h b h cursor past hn
      (.prelaunch coord) followers)
    (hdown : ∀ (i : Fin (p.m - 1)) (a : Activation p),
      b.activation (refFollower i) = some a →
      ∀ (t : Fin p.T) (ht : t ∈ calendarBlock p (ReferenceInitializationRun.nextBlock b h)),
      ¬ passing_at rate.eta i
        (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)) a t
        (ReferenceInitializationRun.ownEntry
          (ReferenceInitializationRun.physical (referenceInput source rewards C_star C_h rate) b h)
          (PublicDiscreteDraws.followerPlayer p.two_le_m (refFollower i)) t)
        (replay rate.eta i
          (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)) a
          (beforeHistory (referenceInput source rewards C_star C_h rate) b h t ht
            (PublicDiscreteDraws.followerPlayer p.two_le_m (refFollower i)))
          (Nat.le_of_lt t.isLt)).downBatch) :
    let time := ActualInitializationRun.blockTime p (ReferenceInitializationRun.nextBlock b h) cursor hc
    let ready := ready_of_invariant rate _ source C_star C_h cursor hc coord followers hi
    let record := executeAt rate _ time coord followers source rewards ready
    ∃ hm : (past ++ [record]).length ≤ p.T,
      cursor_related source rewards rate C_star C_h b h (cursor + 1)
        (past ++ [record]) hm record.result.coordinator.next
        (fun i => (record.result.followers i).next) ∧
      ∀ i, followerMemory rate _ ((record.result.followers i).next) =
        followerMemory rate _ (followers i) := by
  let v := ReferenceInitializationRun.physical (referenceInput source rewards C_star C_h rate) b h
  let time := ActualInitializationRun.blockTime p (ReferenceInitializationRun.nextBlock b h) cursor hc
  let ready := ready_of_invariant rate _ source C_star C_h cursor hc coord followers hi
  let record := executeAt rate _ time coord followers source rewards ready
  have hround := round_related_of_cursor source rewards rate C_star C_h b h cursor past hn hc
    coord followers hi hr
  have htime : time.val = past.length := hr.1.symm
  have ht : time ∈ calendarBlock p (ReferenceInitializationRun.nextBlock b h) :=
    ActualInitializationRun.blockTime_mem p _ cursor hc
  have hm : (past ++ [record]).length ≤ p.T := by
    simp only [List.length_append, List.length_singleton]
    have hT := time.isLt
    omega
  have hcorr := executeAt_correspondence source rewards rate C_star C_h b h past hn time
    coord followers ready hround
  have hhist := executeAt_history_extension source rewards rate C_star C_h b h past hn time
    coord followers ready hround
  have hfollowers : followers_related source rewards rate C_star C_h b h
      (past ++ [record]) hm (fun i => (record.result.followers i).next) ∧
      ∀ i, followerMemory rate _ ((record.result.followers i).next) =
        followerMemory rate _ (followers i) := by
    have each (i : Fin (p.m - 1)) :
        (round_follower_related source rewards rate C_star C_h b h (past ++ [record]) hm i
            ((record.result.followers i).next) ∧
          match (record.result.followers i).next with
          | .bootstrap state =>
              ∃ hi : refFollower i ∈ ReferenceInitializationRun.uninformed b,
                startup_prefix_related v source.1.2 ⟨refFollower i, hi⟩ (b.numerators i)
                  (past ++ [record]).length state
          | .declared _ _ _ => True) ∧
        followerMemory rate _ ((record.result.followers i).next) = followerMemory rate _ (followers i) := by
      have hf := hr.2.2.2.2 i
      cases he : followers i with
      | bootstrap state =>
          rw [he] at hf
          obtain ⟨hmem, hprefix⟩ := hf.2
          obtain ⟨next, hnext, _, hnum, hcase⟩ := executeAt_bootstrap_continuation rate _ time
            coord followers source rewards ready i state he
          have hown : ActualInitializationPhysicalStep.observationOfGrid p
              (record.result.feedback (PublicDiscreteDraws.followerPlayer p.two_le_m (refFollower i))) =
              BootstrapObservedFollower.physicalObservation v ⟨refFollower i, hmem⟩ time :=
            congrArg Prod.snd (hcorr.2.2 _)
          have hp : startup_prefix_related v source.1.2 ⟨refFollower i, hmem⟩ (b.numerators i)
              (past ++ [record]).length next := by
            have hpast : startup_prefix_related v source.1.2 ⟨refFollower i, hmem⟩ (b.numerators i)
                time.val state := by rw [htime]; exact hprefix
            have hc' : next.blockCase = match state.blockCase with
                | .inactive => .inactive
                | .active held privateID gain registers =>
                    .active held privateID
                      (if BootstrapObservedFollower.positiveStay v.ids privateID time
                        (BootstrapObservedFollower.physicalObservation v ⟨refFollower i, hmem⟩ time)
                        then gain + 1 else gain)
                      (BootstrapObservedFollower.observationAdvance p (ReferenceInitializationRun.nextBlock b h) v.ids source.1.2 true privateID
                        registers time (BootstrapObservedFollower.physicalObservation v ⟨refFollower i, hmem⟩ time)) := by
              rw [← hown]
              exact hcase
            have hpnext := startup_prefix_step v source.1.2 ⟨refFollower i, hmem⟩ (b.numerators i)
              state next time ht hpast hnum hc'
            simpa only [List.length_append, List.length_singleton, htime] using hpnext
          rw [hnext]
          refine ⟨⟨?_, hmem, hp⟩, rfl⟩
          exact ⟨hmem, hp.1, startup_prefix_draws v source.1.2 _ _ _ next hp⟩
      | declared row a configuration =>
          rw [he] at hf
          cases configuration with
          | dagger => exact False.elim hf.1
          | ordinary state memory =>
              obtain ⟨hrow, ha, hstate, hmarker⟩ := hf.1
              change state = replay rate.eta i v.row a
                (recordHistory past (PublicDiscreteDraws.followerPlayer p.two_le_m (refFollower i))) hn at hstate
              have hbefore := replay_eq_beforeHistory source rewards rate C_star C_h b h past hn
                hr.2.2.1 time ht htime i a
              change replay rate.eta i v.row a
                (recordHistory past (PublicDiscreteDraws.followerPlayer p.two_le_m (refFollower i))) hn = _ at hbefore
              have hnot : ¬ passing_at rate.eta i v.row a time
                  (ReferenceInitializationRun.ownEntry v
                    (PublicDiscreteDraws.followerPlayer p.two_le_m (refFollower i)) time) state.downBatch := by
                rw [hstate, hbefore]
                exact hdown i a ha time ht
              have hnext := executeAt_declared_continuation source rewards rate C_star C_h b h past hn
                time coord followers ready hround i row a state memory he hnot
              have hext : replay rate.eta i v.row a
                  (recordHistory (past ++ [record])
                    (PublicDiscreteDraws.followerPlayer p.two_le_m (refFollower i))) hm =
                  step i v.row a time (ReferenceInitializationRun.ownEntry v
                    (PublicDiscreteDraws.followerPlayer p.two_le_m (refFollower i)) time) state := by
                rw [replay_recordHistory_append rate source rewards past record i v.row a hn hm htime,
                  hcorr.2.2, ← hstate]
                rfl
              have hfalse : (replay rate.eta i v.row a
                  (recordHistory (past ++ [record])
                    (PublicDiscreteDraws.followerPlayer p.two_le_m (refFollower i))) hm).initializationFailure = false := by
                rw [hext]
                apply Bool.eq_false_iff.mpr
                intro hbad
                have hu := (replay_registers rate.eta i v.row a
                  (recordHistory past (PublicDiscreteDraws.followerPlayer p.two_le_m (refFollower i))) hn).2.2.2.2.2
                rw [← hstate] at hu
                rcases (step_failure_iff i v.row a time _ state hu).mp hbad with hbad | hbad
                · rw [hmarker] at hbad
                  cases hbad
                · exact hnot hbad
              rw [hnext]
              exact ⟨⟨⟨rfl, ha, rfl, hfalse⟩, trivial⟩, rfl⟩
    refine ⟨?_, fun i => (each i).2⟩
    intro i
    refine ⟨(each i).1.1, ?_⟩
    have hx := (each i).1.2
    dsimp only
    generalize he : (record.result.followers i).next = f at hx ⊢
    cases f with
    | bootstrap state =>
        obtain ⟨hm, hp⟩ := hx
        exact ⟨hm, hp⟩
    | declared row a configuration => trivial
  refine ⟨hm, ⟨?_, ?_, ?_, ?_, hfollowers.1⟩, hfollowers.2⟩
  · simp only [List.length_append, List.length_singleton]
    rw [hr.1]
    omega
  · exact chronological_append past record hr.2.1 htime
  · intro i u
    by_cases hu : u.val < past.length
    · have hp := hhist.1 i ⟨u.val, hu⟩
      change recordHistory (past ++ [record]) i u = _ at hp
      rw [hp, hr.2.2.1 i ⟨u.val, hu⟩]
      rfl
    · have he : u.val = past.length := by
        have hb := u.isLt
        simp only [List.length_append, List.length_singleton] at hb
        omega
      have hu' : u = ⟨past.length, by simp only [List.length_append, List.length_singleton]; omega⟩ := Fin.ext he
      rw [hu', hhist.2]
      have hpast : ¬ past.length < ReferenceInitializationRun.elapsed p b.completed := by
        rw [ReferenceInitializationRun.elapsed_eq_blockStart b h, hr.1]
        exact Nat.not_lt_of_ge (Nat.le_add_right _ _)
      rw [dite_eq_right hpast]
      congr 1
      exact Fin.ext htime
  · have he := executeAt_coordinator_extension source rewards rate C_star C_h b h past hn time
      coord followers ready hround
    convert he using 1
    simp only [List.length_append, List.length_singleton, htime]

/-- The empty suffix of the existing fold has no invented endpoint action. -/
theorem foldBlockAux_zero (rate : RateInput p) (s : Fin (n_boot p))
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (cursor : ℕ) (hb : cursor + 0 = BootstrapObservedFollower.blockLength p s)
    (phase : BootstrapCoordinatorLocalRound.Continuation p)
    (followers : Fin (p.m - 1) → ActualInitializationPhysicalStep.FollowerState p rate s)
    (hi : ActualInitializationRun.BlockInvariant p rate s source C_star C_h cursor phase followers) :
    let whole := ActualInitializationRun.foldBlockAux p rate s source rewards C_star C_h
      cursor 0 hb phase followers hi
    whole.phase = phase ∧ whole.followers = followers ∧ whole.records = [] := by
  unfold ActualInitializationRun.foldBlockAux
  dsimp only [Nat.casesAuxOn]
  exact ⟨rfl, rfl, rfl⟩

/-- COMPLETE induction over the EXISTING actual block suffix. It relates all
produced physical records and own histories, the full gain, every candidate
register and pending row, and the exact ordinary replay, with retained memory.
The only excluded within-block event is the explicit generated ordinary DOWN
parse predicate below. False-row passes are not needed for physical play inside
this block; their complement is used when comparing the saved row. -/
theorem foldBlockAux_related
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (rate : RateInput p)
    (C_star C_h : ℝ) (b : ReferenceInitializationRun.Boundary p)
    (h : b.completed < n_boot p) (cursor fuel : ℕ)
    (hb : cursor + fuel = BootstrapObservedFollower.blockLength p (ReferenceInitializationRun.nextBlock b h))
    (phase : BootstrapCoordinatorLocalRound.Continuation p)
    (followers : Fin (p.m - 1) → ActualInitializationPhysicalStep.FollowerState p rate
      (ReferenceInitializationRun.nextBlock b h))
    (hi : ActualInitializationRun.BlockInvariant p rate (ReferenceInitializationRun.nextBlock b h)
      source C_star C_h cursor phase followers)
    (past : List (ActualInitializationRun.PhysicalRoundRecord p rate source rewards))
    (hn : past.length ≤ p.T)
    (hr : cursor_related source rewards rate C_star C_h b h cursor past hn phase followers)
    (hdown : ∀ (i : Fin (p.m - 1)) (a : Activation p),
      b.activation (refFollower i) = some a →
      ∀ (t : Fin p.T) (ht : t ∈ calendarBlock p (ReferenceInitializationRun.nextBlock b h)),
      ¬ passing_at rate.eta i
        (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)) a t
        (ReferenceInitializationRun.ownEntry
          (ReferenceInitializationRun.physical (referenceInput source rewards C_star C_h rate) b h)
          (PublicDiscreteDraws.followerPlayer p.two_le_m (refFollower i)) t)
        (replay rate.eta i
          (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)) a
          (beforeHistory (referenceInput source rewards C_star C_h rate) b h t ht
            (PublicDiscreteDraws.followerPlayer p.two_le_m (refFollower i)))
          (Nat.le_of_lt t.isLt)).downBatch) :
    let out := ActualInitializationRun.foldBlockAux p rate (ReferenceInitializationRun.nextBlock b h)
      source rewards C_star C_h cursor fuel hb phase followers hi
    let v := ReferenceInitializationRun.physical (referenceInput source rewards C_star C_h rate) b h
    ∃ hm : (past ++ out.records).length ≤ p.T,
      cursor_related source rewards rate C_star C_h b h
        (BootstrapObservedFollower.blockLength p (ReferenceInitializationRun.nextBlock b h))
        (past ++ out.records) hm out.phase out.followers ∧
      (∀ record ∈ out.records,
        record.result.actions = BootstrapPhysicalBlock.actions v (BootstrapPhysicalBlock.run v record.time.val) record.time ∧
        record.result.feedback = (fun i => BootstrapPhysicalBlock.observationIndex v
          (BootstrapPhysicalBlock.run v record.time.val) record.time i) ∧
        ∀ i, recordEntry record i = ReferenceInitializationRun.ownEntry v i record.time) ∧
      ∀ i, followerMemory rate _ (out.followers i) = followerMemory rate _ (followers i) := by
  induction fuel generalizing cursor phase followers past with
  | zero =>
      obtain ⟨hp, hf, hrecords⟩ := foldBlockAux_zero rate _ source rewards C_star C_h cursor hb phase followers hi
      dsimp only
      rw [hp, hf, hrecords]
      simp only [List.append_nil]
      have he : cursor = BootstrapObservedFollower.blockLength p (ReferenceInitializationRun.nextBlock b h) := by omega
      refine ⟨hn, he ▸ hr, ?_, fun _ => by trivial⟩
      intro record hm
      exact False.elim (List.not_mem_nil hm)
  | succ fuel ih =>
      cases phase with
      | launched launch =>
          have he := hi.2.2.2
          omega
      | prelaunch coord =>
          have hc : cursor < BootstrapObservedFollower.blockLength p (ReferenceInitializationRun.nextBlock b h) := by omega
          let time := ActualInitializationRun.blockTime p (ReferenceInitializationRun.nextBlock b h) cursor hc
          let ready := ready_of_invariant rate _ source C_star C_h cursor hc coord followers hi
          let record := executeAt rate _ time coord followers source rewards ready
          obtain ⟨hnext, hp, hf, hrecords⟩ := foldBlockAux_succ rate _ source rewards C_star C_h
            cursor fuel hb coord followers hi
          obtain ⟨hm, hrel, hmem⟩ := cursor_related_step source rewards rate C_star C_h b h cursor
            past hn hc coord followers hi hr hdown
          have iht := ih (cursor := cursor + 1) (phase := record.result.coordinator.next)
            (followers := fun i => (record.result.followers i).next)
            (past := past ++ [record]) (hn := hm) (hb := by omega) hnext hrel
          obtain ⟨ht, hrt, hrecordsTail, hmemTail⟩ := iht
          dsimp only
          rw [hp, hf, hrecords]
          simp only [List.append_assoc, List.singleton_append] at ht hrt
          refine ⟨ht, hrt, ?_, fun i => (hmemTail i).trans (hmem i)⟩
          intro r hmemr
          rcases List.mem_cons.mp hmemr with rfl | htail
          · exact executeAt_correspondence source rewards rate C_star C_h b h past hn time
              coord followers ready (round_related_of_cursor source rewards rate C_star C_h b h cursor
                past hn hc coord followers hi hr)
          · exact hrecordsTail r htail

/-- An actual accepted parse in a chronological replay prefix marks the full
replay as failed. This uses the accepted parser and failure register literally. -/
theorem replay_failure_of_passing_prefix {n : ℕ} (eta : LearningRate)
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p) (a : Activation p)
    (history : LocalHistory p n) (hn : n ≤ p.T) (t : Fin n)
    (hp : passing_at eta i row a (calendar hn t) (history t)
      (replay eta i row a
        (fun u : Fin t.val => history ⟨u.val, u.isLt.trans t.isLt⟩)
        ((Nat.le_of_lt t.isLt).trans hn)).downBatch) :
    (replay eta i row a history hn).initializationFailure = true := by
  induction n with
  | zero => exact Fin.elim0 t
  | succ n ih =>
      rw [replay_succ]
      have hu := (replay_registers eta i row a (fun u : Fin n => history u.castSucc) (by omega)).2.2.2.2.2
      apply (step_failure_iff i row a _ _ _ hu).mpr
      by_cases ht : t.val < n
      · left
        apply ih (fun u : Fin n => history u.castSucc) (by omega) ⟨t.val, ht⟩
        exact hp
      · right
        have he : t = Fin.last n := Fin.ext (by change t.val = n; have := t.isLt; omega)
        subst t
        exact hp

/-- The accepted generated block DOWN obstruction supplies every excluded
per-round acceptance predicate. No domain-validity or local-success premise is
added: those checks are already consequences of the related replay. -/
theorem not_passing_of_not_generatedBlockDown
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (rate : RateInput p)
    (C_star C_h : ℝ) (b : ReferenceInitializationRun.Boundary p)
    (h : b.completed < n_boot p)
    (actual : ActualInitializationRun.BlockCarry p rate (ReferenceInitializationRun.nextBlock b h))
    (past : List (ActualInitializationRun.PhysicalRoundRecord p rate source rewards))
    (hr : BlockStartRelated source rewards C_star C_h rate
      (ReferenceInitializationRun.nextBlock b h) actual b past)
    (hdown : ∀ i, ¬ InitializationFailureProvenance.generatedBlockDown
      (referenceInput source rewards C_star C_h rate) b h i)
    (i : Fin (p.m - 1)) (a : Activation p) (ha : b.activation (refFollower i) = some a)
    (t : Fin p.T) (ht : t ∈ calendarBlock p (ReferenceInitializationRun.nextBlock b h)) :
    ¬ passing_at rate.eta i
      (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)) a t
      (ReferenceInitializationRun.ownEntry
        (ReferenceInitializationRun.physical (referenceInput source rewards C_star C_h rate) b h)
        (PublicDiscreteDraws.followerPlayer p.two_le_m (refFollower i)) t)
      (replay rate.eta i
        (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)) a
        (beforeHistory (referenceInput source rewards C_star C_h rate) b h t ht
          (PublicDiscreteDraws.followerPlayer p.two_le_m (refFollower i)))
        (Nat.le_of_lt t.isLt)).downBatch := by
  let x := referenceInput source rewards C_star C_h rate
  have hf : b.forcedFailure (refFollower i) = false := hr.2.2.1 _
  have hprior : (ReferenceInitializationRun.ordinary x b (refFollower i)).initializationFailure = false := by
    have hrel := hr.2.2.2.2.2.2.2 i
    cases he : actual.followers i with
    | bootstrap numerators lower =>
        rw [he] at hrel
        have hn : b.activation (refFollower i) = none := hrel.1
        rw [ha] at hn
        cases hn
    | declared row activation config =>
        rw [he] at hrel
        cases config with
        | dagger => exact False.elim hrel
        | ordinary state memory =>
            have hs : state = ReferenceInitializationRun.ordinary x b (refFollower i) := hrel.2.2.1
            obtain ⟨_, _, _, _, _, _, _, _, _, hmarker, _⟩ := hrel
            rw [← hs]
            exact hmarker
  have hterminal : (ReferenceInitializationRun.ordinary x
      (ReferenceInitializationRun.finishBlock x b h) (refFollower i)).initializationFailure = false := by
    apply Bool.eq_false_iff.mpr
    intro hbad
    have heq := InitializationFailureProvenance.ordinary_finishBlock_suppressed_blockReplay
      x b h (refFollower i) a ha hf
    rcases heq.mp hbad with hbad | hbad
    · rw [hprior] at hbad
      cases hbad
    · exact hdown (refFollower i) ⟨hf, a, ha, hbad⟩
  have hff : (ReferenceInitializationRun.finishBlock x b h).forcedFailure (refFollower i) = false := by
    change (b.forcedFailure (refFollower i) || ReferenceInitializationRun.forced x b h (refFollower i)) = false
    rw [hf, ReferenceInitializationRun.activated_not_forced x b h (refFollower i) a ha]
    rfl
  have hfull : ReferenceInitializationRun.ordinary x
      (ReferenceInitializationRun.finishBlock x b h) (refFollower i) =
      replay rate.eta i x.row a
        (ReferenceInitializationRun.extendedHistory x b h
          (PublicDiscreteDraws.followerPlayer p.two_le_m (refFollower i)))
        (ReferenceInitializationRun.elapsed_le_T p (b.completed + 1)) := by
    simp only [ReferenceInitializationRun.ordinary, hff, Bool.false_eq_true, ite_false,
      ReferenceInitializationRun.activated_activation x b h (refFollower i) a ha, atLaunch]
    rfl
  rw [hfull] at hterminal
  intro hp
  let u : Fin (ReferenceInitializationRun.elapsed p (b.completed + 1)) :=
    ⟨t.val, ((mem_calendarBlock_iff p _ t).mp ht).2⟩
  have hentry : ReferenceInitializationRun.extendedHistory x b h
      (PublicDiscreteDraws.followerPlayer p.two_le_m (refFollower i)) u =
      ReferenceInitializationRun.ownEntry (ReferenceInitializationRun.physical x b h)
        (PublicDiscreteDraws.followerPlayer p.two_le_m (refFollower i)) t := by
    have hnot : ¬ t.val < ReferenceInitializationRun.elapsed p b.completed := by
      rw [ReferenceInitializationRun.elapsed_eq_blockStart b h]
      exact Nat.not_lt_of_ge ((mem_calendarBlock_iff p _ t).mp ht).1
    simp only [ReferenceInitializationRun.extendedHistory, u, dite_eq_right hnot]
  have hpass : passing_at rate.eta i x.row a
      (calendar (ReferenceInitializationRun.elapsed_le_T p (b.completed + 1)) u)
      (ReferenceInitializationRun.extendedHistory x b h
        (PublicDiscreteDraws.followerPlayer p.two_le_m (refFollower i)) u)
      (replay rate.eta i x.row a
        (fun v : Fin u.val => ReferenceInitializationRun.extendedHistory x b h
          (PublicDiscreteDraws.followerPlayer p.two_le_m (refFollower i)) ⟨v.val, v.isLt.trans u.isLt⟩)
        ((Nat.le_of_lt u.isLt).trans (ReferenceInitializationRun.elapsed_le_T p (b.completed + 1)))).downBatch := by
    rw [hentry]
    exact hp
  have hbad := replay_failure_of_passing_prefix rate.eta i x.row a _ _ u hpass
  rw [hterminal] at hbad
  cases hbad

/-- ONE BLOCK from honest PRIOR boundary data and the complement of the
accepted generated ordinary DOWN obstruction. The actual fold is the accepted
producer, and no current history or matching register is supplied as a premise.
This statement stops before the boundary adapter. -/
theorem foldBlock_related
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (rate : RateInput p)
    (C_star C_h : ℝ) (b : ReferenceInitializationRun.Boundary p)
    (h : b.completed < n_boot p)
    (actual : ActualInitializationRun.BlockCarry p rate (ReferenceInitializationRun.nextBlock b h))
    (past : List (ActualInitializationRun.PhysicalRoundRecord p rate source rewards))
    (hr : BlockStartRelated source rewards C_star C_h rate
      (ReferenceInitializationRun.nextBlock b h) actual b past)
    (hdown : ∀ i, ¬ InitializationFailureProvenance.generatedBlockDown
      (referenceInput source rewards C_star C_h rate) b h i) :
    let out := ActualInitializationRun.foldBlock p rate (ReferenceInitializationRun.nextBlock b h) source rewards actual
    let v := ReferenceInitializationRun.physical (referenceInput source rewards C_star C_h rate) b h
    ∃ hm : (past ++ out.records).length ≤ p.T,
      cursor_related source rewards rate C_star C_h b h
        (BootstrapObservedFollower.blockLength p (ReferenceInitializationRun.nextBlock b h))
        (past ++ out.records) hm out.phase out.followers ∧
      (∀ record ∈ out.records,
        record.result.actions = BootstrapPhysicalBlock.actions v (BootstrapPhysicalBlock.run v record.time.val) record.time ∧
        record.result.feedback = (fun i => BootstrapPhysicalBlock.observationIndex v
          (BootstrapPhysicalBlock.run v record.time.val) record.time i) ∧
        ∀ i, recordEntry record i = ReferenceInitializationRun.ownEntry v i record.time) ∧
      ∀ i, followerMemory rate _ (out.followers i) = followerMemory rate _
        ((ActualInitializationRun.beginBlock p rate (ReferenceInitializationRun.nextBlock b h) source actual).followers i) := by
  have hc1 := hr.2.2.2.2.1
  have hc2 := hr.2.2.2.2.2.1
  rw [← hc1, ← hc2] at hr hdown ⊢
  have hbase := begin_cursor_related source rewards rate actual.C_star actual.C_h b h actual past hr
  have hnot := not_passing_of_not_generatedBlockDown source rewards rate actual.C_star actual.C_h b h actual past hr hdown
  exact foldBlockAux_related source rewards rate actual.C_star actual.C_h b h 0 _ (by omega)
    _ _ (ActualInitializationRun.beginBlock p rate _ source actual).invariant past _ hbase hnot

/-- No candidate update occurs after this clipped block. Calendar `T` here
is a prefix bound, not a new physical action at the sentinel `T + 1`. -/
theorem allCandidate_run_end {s : Fin (n_boot p)} (v : BootstrapPhysicalBlock.Input p s)
    (rows : CompletePublicTable.CompleteRows p) (i : {i // i ∈ v.uninformed}) :
    BootstrapAllCandidateController.run v rows i (BootstrapObservedFollower.blockStop p s) =
      BootstrapAllCandidateController.run v rows i p.T := by
  have aux : ∀ n, BootstrapObservedFollower.blockStop p s ≤ n → n ≤ p.T →
      BootstrapAllCandidateController.run v rows i n =
        BootstrapAllCandidateController.run v rows i (BootstrapObservedFollower.blockStop p s) := by
    intro n
    induction n with
    | zero =>
        intro hs _
        have he : BootstrapObservedFollower.blockStop p s = 0 := by omega
        rw [he]
    | succ n ih =>
        intro hs hn
        by_cases he : BootstrapObservedFollower.blockStop p s = n + 1
        · rw [he]
        · let t : Fin p.T := ⟨n, by omega⟩
          have ht : t ∉ calendarBlock p s := by
            intro hm
            have hb := ((mem_calendarBlock_iff p s t).mp hm).2
            change n < BootstrapObservedFollower.blockStop p s at hb
            omega
          rw [show n + 1 = t.val + 1 from rfl, BootstrapAllCandidateController.run_succ,
            BootstrapAllCandidateController.advance_eq_of_outside_block v rows i _ t ht]
          exact ih (by omega) (by omega)
  exact (aux p.T (Nat.min_le_left _ _) le_rfl).symm

theorem allCandidate_run_inactive {s : Fin (n_boot p)} (v : BootstrapPhysicalBlock.Input p s)
    (rows : CompletePublicTable.CompleteRows p) (i : {i // i ∈ v.uninformed})
    (ha : v.active i = false) (k : ℕ) (hk : k ≤ p.T) :
    BootstrapAllCandidateController.run v rows i k = BootstrapAllCandidateController.initialRegisters p := by
  induction k with
  | zero => rfl
  | succ k ih =>
      let t : Fin p.T := ⟨k, by omega⟩
      rw [show k + 1 = t.val + 1 from rfl, BootstrapAllCandidateController.run_succ,
        BootstrapAllCandidateController.advance_eq_of_inactive v rows i _ t ha]
      exact ih (by omega)

/-- At the clipped endpoint, the saved declaration has not changed the full
gain or sampled fields. All candidate registers are the accepted full-block
controller, including their permanent rejection flags. -/
theorem startup_prefix_end_case {s : Fin (n_boot p)}
    (v : BootstrapPhysicalBlock.Input p s) (rows : CompletePublicTable.CompleteRows p)
    (i : {i // i ∈ v.uninformed}) (numerators : Fin p.K → ℕ)
    (state : BootstrapObservedFollower.StartupState p s)
    (hr : startup_prefix_related v rows i numerators (BootstrapObservedFollower.blockStop p s) state) :
    state.blockCase = if v.active i then
      .active (v.held i) (v.privateId i) (BootstrapPhysicalBlock.physicalStayGain v i)
        (BootstrapAllCandidateController.run v rows i p.T)
    else .inactive := by
  rw [hr.2, allCandidate_run_end]
  cases ha : v.active i with
  | false => rfl
  | true => rw [gainPrefix_end v i ha]

/-- Extensionality for the accepted literal weight input, ignoring only its
proof that the recorded gain is bounded. -/
theorem weightBlock_ext {K B : ℕ} (left right : BootstrapWeightPotential.Block K B)
    (he : left.enabled = right.enabled) (hh : left.held = right.held)
    (hg : left.gain = right.gain) : left = right := by
  cases left
  cases right
  simp only [BootstrapWeightPotential.Block.mk.injEq]
  exact ⟨he, hh, hg⟩

/-- The actual literal floor update receives the same FULL gain as the
reference update. No equality of postblock numerators is assumed. -/
theorem startup_updatedNumerators_eq
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (rate : RateInput p)
    (C_star C_h : ℝ) (b : ReferenceInitializationRun.Boundary p)
    (h : b.completed < n_boot p) (i : Fin (p.m - 1))
    (hi : refFollower i ∈ (ReferenceInitializationRun.physical
      (referenceInput source rewards C_star C_h rate) b h).uninformed)
    (state : BootstrapObservedFollower.StartupState p (ReferenceInitializationRun.nextBlock b h))
    (hr : startup_prefix_related
      (ReferenceInitializationRun.physical (referenceInput source rewards C_star C_h rate) b h)
      source.1.2 ⟨refFollower i, hi⟩ (b.numerators i)
      (BootstrapObservedFollower.blockStop p (ReferenceInitializationRun.nextBlock b h)) state) :
    BootstrapObservedFollower.updatedNumerators p (ReferenceInitializationRun.nextBlock b h) state =
      ReferenceInitializationRun.updatedNumerators (referenceInput source rewards C_star C_h rate) b h i := by
  let x := referenceInput source rewards C_star C_h rate
  let v := ReferenceInitializationRun.physical x b h
  let j : {j // j ∈ v.uninformed} := ⟨refFollower i, hi⟩
  let jr : {j // j ∈ ReferenceInitializationRun.uninformed b} := ⟨refFollower i, hi⟩
  have hcase := startup_prefix_end_case v source.1.2 j (b.numerators i) state hr
  have he : (ReferenceInitializationRun.weightInput x b h jr).enabled = v.active j :=
    BootstrapPhysicalBlock.observationTrace_blockEnabled v j (BootstrapTruePrefixController.savedAt v j) false
  change _ = (if hij : refFollower i ∈ ReferenceInitializationRun.uninformed b then
    BootstrapWeightPotential.next (b_N p) (b.numerators i)
      (ReferenceInitializationRun.weightInput x b h ⟨refFollower i, hij⟩) else b.numerators i)
  have hi' : refFollower i ∈ ReferenceInitializationRun.uninformed b := hi
  rw [dite_eq_left hi']
  cases ha : v.active j with
  | false =>
      rw [ite_eq_right (by rw [ha]; decide)] at hcase
      rw [BootstrapObservedFollower.updatedNumerators_inactive p _ state hcase, hr.1]
      exact (BootstrapWeightPotential.next_disabled (b.numerators i)
        (ReferenceInitializationRun.weightInput x b h jr) (he.trans ha)).symm
  | true =>
      rw [ite_eq_left ha] at hcase
      rw [BootstrapObservedFollower.updatedNumerators_active_eq_next p _ state _ _ _ _ hcase, hr.1]
      have hg := ReferenceInitializationRun.weightInput_full_gain x b h jr
      change (if (ReferenceInitializationRun.weightInput x b h jr).enabled = true then
        (ReferenceInitializationRun.weightInput x b h jr).gain else 0) = _ at hg
      rw [he, ha, ite_eq_left rfl] at hg
      change (ReferenceInitializationRun.weightInput x b h jr).gain =
        BootstrapPhysicalBlock.physicalStayGain v j at hg
      have hb : BootstrapObservedFollower.activeWeightBlock p (v.held j)
          (BootstrapPhysicalBlock.physicalStayGain v j)
          (BootstrapObservedFollower.activeGain_le_B_boot p _ state _ _ _ _ hcase) = ReferenceInitializationRun.weightInput x b h jr := by
        apply weightBlock_ext
        · exact (he.trans ha).symm
        · rfl
        · exact hg.symm
      rw [hb]

/-- History output of the complete physical fold is exactly the existing
reference boundary history. This says nothing about the yet-uncompared
coordinator monitor or boundary disposition. -/
theorem foldBlock_past_related
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (rate : RateInput p)
    (C_star C_h : ℝ) (b : ReferenceInitializationRun.Boundary p)
    (h : b.completed < n_boot p)
    (actual : ActualInitializationRun.BlockCarry p rate (ReferenceInitializationRun.nextBlock b h))
    (past : List (ActualInitializationRun.PhysicalRoundRecord p rate source rewards))
    (hr : BlockStartRelated source rewards C_star C_h rate
      (ReferenceInitializationRun.nextBlock b h) actual b past)
    (hdown : ∀ i, ¬ InitializationFailureProvenance.generatedBlockDown
      (referenceInput source rewards C_star C_h rate) b h i) :
    past_related
      (past ++ (ActualInitializationRun.foldBlock p rate (ReferenceInitializationRun.nextBlock b h)
        source rewards actual).records)
      (ReferenceInitializationRun.finishBlock (referenceInput source rewards C_star C_h rate) b h) := by
  obtain ⟨hn, hrel, _, _⟩ := foldBlock_related source rewards rate C_star C_h b h actual past hr hdown
  have hlength : (past ++ (ActualInitializationRun.foldBlock p rate
      (ReferenceInitializationRun.nextBlock b h) source rewards actual).records).length =
      ReferenceInitializationRun.elapsed p (b.completed + 1) := by
    rw [hrel.1]
    have hs := Nat.le_of_lt (BootstrapObservedFollower.blockStart_lt_blockStop p
      (ReferenceInitializationRun.nextBlock b h))
    change BootstrapObservedFollower.blockStart p (ReferenceInitializationRun.nextBlock b h) +
      (BootstrapObservedFollower.blockStop p (ReferenceInitializationRun.nextBlock b h) -
        BootstrapObservedFollower.blockStart p (ReferenceInitializationRun.nextBlock b h)) =
      BootstrapObservedFollower.blockStop p (ReferenceInitializationRun.nextBlock b h)
    omega
  refine ⟨hlength, hrel.2.1, ?_⟩
  intro i u
  change ReferenceInitializationRun.extendedHistory _ b h i u = _
  rw [hrel.2.2.1]
  rfl

/-- The generated actual final startup state, its full-gain weight update and
its pending row agree with the true-only reference under the LITERAL accepted
incorrect-row prefix-pass complement. This is the forward obstruction, separate
from `generatedBlockDown`; no correct-choice oracle is supplied. -/
theorem foldBlock_bootstrap_comparison
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (rate : RateInput p)
    (C_star C_h : ℝ) (b : ReferenceInitializationRun.Boundary p)
    (h : b.completed < n_boot p)
    (actual : ActualInitializationRun.BlockCarry p rate (ReferenceInitializationRun.nextBlock b h))
    (past : List (ActualInitializationRun.PhysicalRoundRecord p rate source rewards))
    (hr : BlockStartRelated source rewards C_star C_h rate
      (ReferenceInitializationRun.nextBlock b h) actual b past)
    (hdown : ∀ i, ¬ InitializationFailureProvenance.generatedBlockDown
      (referenceInput source rewards C_star C_h rate) b h i)
    (i : Fin (p.m - 1))
    (hi : refFollower i ∈ (ReferenceInitializationRun.physical
      (referenceInput source rewards C_star C_h rate) b h).uninformed)
    (hforward : BootstrapAllCandidateController.cleanPrefix
      (ReferenceInitializationRun.physical (referenceInput source rewards C_star C_h rate) b h)
      source.1.2 ⟨refFollower i, hi⟩
      (ActualInitializationPhysicalStep.selectedRowIndex p source) p.T) :
    let x := referenceInput source rewards C_star C_h rate
    let v := ReferenceInitializationRun.physical x b h
    let j := (⟨refFollower i, hi⟩ : {j // j ∈ v.uninformed})
    let J := ActualInitializationPhysicalStep.selectedRowIndex p source
    let out := ActualInitializationRun.foldBlock p rate (ReferenceInitializationRun.nextBlock b h) source rewards actual
    ∃ state : BootstrapObservedFollower.StartupState p (ReferenceInitializationRun.nextBlock b h),
      out.followers i = .bootstrap state ∧
      state.processed.val = BootstrapObservedFollower.blockLength p (ReferenceInitializationRun.nextBlock b h) ∧
      state.numerators = b.numerators i ∧
      state.blockCase = (if v.active j then
        .active (v.held j) (v.privateId j) (BootstrapPhysicalBlock.physicalStayGain v j)
          (BootstrapAllCandidateController.run v source.1.2 j p.T) else .inactive) ∧
      BootstrapObservedFollower.updatedNumerators p (ReferenceInitializationRun.nextBlock b h) state =
        ReferenceInitializationRun.updatedNumerators x b h i ∧
      BootstrapObservedFollower.pendingDeclaration state.blockCase =
        (if (ReferenceInitializationRun.candidate x b h j).pending = true then some J else none) ∧
      (BootstrapAllCandidateController.run v source.1.2 j p.T).count J =
        (ReferenceInitializationRun.candidate x b h j).count ∧
      (BootstrapAllCandidateController.run v source.1.2 j p.T).dead J =
        (ReferenceInitializationRun.candidate x b h j).dead := by
  let x := referenceInput source rewards C_star C_h rate
  let v := ReferenceInitializationRun.physical x b h
  let j : {j // j ∈ v.uninformed} := ⟨refFollower i, hi⟩
  let out := ActualInitializationRun.foldBlock p rate (ReferenceInitializationRun.nextBlock b h) source rewards actual
  obtain ⟨hn, hrel, _, _⟩ := foldBlock_related source rewards rate C_star C_h b h actual past hr hdown
  have hf := hrel.2.2.2.2 i
  have hend : (past ++ out.records).length = BootstrapObservedFollower.blockStop p
      (ReferenceInitializationRun.nextBlock b h) := by
    rw [hrel.1]
    have hs := Nat.le_of_lt (BootstrapObservedFollower.blockStart_lt_blockStop p (ReferenceInitializationRun.nextBlock b h))
    unfold BootstrapObservedFollower.blockLength
    omega
  have hcomp := BootstrapAllCandidateController.run_eq_true_on_cleanPrefix v source.1.2 j
    (ActualInitializationPhysicalStep.selectedRowIndex p source) rfl p.T p.T le_rfl le_rfl hforward
  cases he : out.followers i with
  | bootstrap state =>
      rw [he] at hf
      obtain ⟨hm, hp⟩ := hf.2
      rw [hend] at hp
      have hc := startup_prefix_end_case v source.1.2 j (b.numerators i) state hp
      have hn' := startup_updatedNumerators_eq source rewards rate C_star C_h b h i hi state hp
      have hprocessed := ActualInitializationRun.blockFold_follower_complete out i
      rw [he] at hprocessed
      have hpend : BootstrapObservedFollower.pendingDeclaration state.blockCase =
          if (ReferenceInitializationRun.candidate x b h j).pending = true then
            some (ActualInitializationPhysicalStep.selectedRowIndex p source) else none := by
        rw [hc]
        cases ha : v.active j with
        | false =>
            have hz := allCandidate_run_inactive v source.1.2 j ha p.T le_rfl
            have hz' := hcomp.2.2
            rw [hz] at hz'
            exact hz'
        | true => exact hcomp.2.2
      exact ⟨state, he, hprocessed, hp.1, hc, hn', hpend, hcomp.1, hcomp.2.1⟩
  | declared row a configuration =>
      rw [he] at hf
      cases configuration with
      | dagger => exact False.elim hf.1
      | ordinary state memory =>
          have ha := hf.1.2.1
          have hnone := (ReferenceInitializationRun.mem_uninformed b (refFollower i)).mp hi
          rw [hnone] at ha
          cases ha

/-- Existing declared followers return the existing reference ordinary state
with their ORIGINAL local memory. Equality of the whole ordinary state includes
all DATA buffers and the partial DOWN decoder bank, as well as its zero learner
registers; no block-boundary reset is inserted into the replay. -/
theorem foldBlock_declared_comparison
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (rate : RateInput p)
    (C_star C_h : ℝ) (b : ReferenceInitializationRun.Boundary p)
    (h : b.completed < n_boot p)
    (actual : ActualInitializationRun.BlockCarry p rate (ReferenceInitializationRun.nextBlock b h))
    (past : List (ActualInitializationRun.PhysicalRoundRecord p rate source rewards))
    (hr : BlockStartRelated source rewards C_star C_h rate
      (ReferenceInitializationRun.nextBlock b h) actual b past)
    (hdown : ∀ i, ¬ InitializationFailureProvenance.generatedBlockDown
      (referenceInput source rewards C_star C_h rate) b h i)
    (i : Fin (p.m - 1)) (row : Fin (M p)) (a : Activation p)
    (state : State p rate.eta) (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hstart : actual.followers i = .declared row a (.ordinary state memory)) :
    (ActualInitializationRun.foldBlock p rate (ReferenceInitializationRun.nextBlock b h)
      source rewards actual).followers i =
      .declared (ActualInitializationPhysicalStep.selectedRowIndex p source) a
        (.ordinary (ReferenceInitializationRun.ordinary
          (referenceInput source rewards C_star C_h rate)
          (ReferenceInitializationRun.finishBlock (referenceInput source rewards C_star C_h rate) b h)
          (refFollower i)) memory) := by
  let x := referenceInput source rewards C_star C_h rate
  let out := ActualInitializationRun.foldBlock p rate (ReferenceInitializationRun.nextBlock b h) source rewards actual
  obtain ⟨hn, hrel, _, hmemory⟩ := foldBlock_related source rewards rate C_star C_h b h actual past hr hdown
  obtain ⟨hlength, _, hhistory⟩ := foldBlock_past_related source rewards rate C_star C_h b h actual past hr hdown
  have hprior := hr.2.2.2.2.2.2.2 i
  rw [hstart] at hprior
  have ha : b.activation (refFollower i) = some a := hprior.2.1
  have hf : b.forcedFailure (refFollower i) = false := hr.2.2.1 _
  have hff : (ReferenceInitializationRun.finishBlock x b h).forcedFailure (refFollower i) = false := by
    change (b.forcedFailure (refFollower i) || ReferenceInitializationRun.forced x b h (refFollower i)) = false
    rw [hf, ReferenceInitializationRun.activated_not_forced x b h (refFollower i) a ha]
    rfl
  have hord : ReferenceInitializationRun.ordinary x (ReferenceInitializationRun.finishBlock x b h)
      (refFollower i) = replay rate.eta i x.row a
        ((ReferenceInitializationRun.finishBlock x b h).history
          (PublicDiscreteDraws.followerPlayer p.two_le_m (refFollower i)))
        (ReferenceInitializationRun.elapsed_le_T p (b.completed + 1)) := by
    simp only [ReferenceInitializationRun.ordinary, hff, Bool.false_eq_true, ite_false,
      ReferenceInitializationRun.activated_activation x b h (refFollower i) a ha, atLaunch]
    rfl
  have hh : (ReferenceInitializationRun.finishBlock x b h).history
      (PublicDiscreteDraws.followerPlayer p.two_le_m (refFollower i)) =
      fun u => recordHistory (past ++ out.records)
        (PublicDiscreteDraws.followerPlayer p.two_le_m (refFollower i)) (Fin.cast hlength.symm u) :=
    funext (hhistory _)
  have hcast := ReferenceInitializationRun.replay_cast rate.eta i x.row a
    (recordHistory (past ++ out.records) (PublicDiscreteDraws.followerPlayer p.two_le_m (refFollower i)))
    hn (ReferenceInitializationRun.elapsed_le_T p (b.completed + 1)) hlength
  rw [hh] at hord
  have hcast' := hord.trans hcast
  have hfol := (hrel.2.2.2.2 i).1
  cases he : out.followers i with
  | bootstrap startup =>
      rw [he] at hfol
      obtain ⟨hmem, _⟩ := hfol
      have hnone := (ReferenceInitializationRun.mem_uninformed b (refFollower i)).mp hmem
      rw [ha] at hnone
      cases hnone
  | declared row' a' config =>
      rw [he] at hfol
      cases config with
      | dagger => exact False.elim hfol
      | ordinary state' memory' =>
          obtain ⟨hrow, ha', hstate, _⟩ := hfol
          have haeq : a' = a := Option.some.inj (ha'.symm.trans ha)
          have hm := hmemory i
          change followerMemory rate _ (out.followers i) = followerMemory rate _
            (ActualInitializationRun.beginFollowerBlock p rate _ source i (actual.followers i)) at hm
          rw [he, hstart] at hm
          have hmeq : memory' = memory := Option.some.inj hm
          rw [hrow, haeq, hmeq]
          congr 2
          rw [hstate, haeq]
          exact hcast'.symm

end Bandits.Support.ActualReferenceInitializationFold

end
