/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ActualReferenceInitializationHorizon
import Lean.Elab.Tactic.Omega
import Mathlib.Data.List.OfFn

/-!
# Lifecycle memory along corrected prelaunch replay

Sources: `sources/zip4/manuscript/07_public_setup.tex:93-114,123-164`,
`sources/zip4/manuscript/06_interruptions.tex:235-296`,
`sources/zip4/manuscript/appendix_a_local_protocol.tex:6-14`, and
`sources/zip4/manuscript/08_main_theorem.tex:29-42`.

The existing corrected follower replay suppresses every prelaunch DOWN
installation while retaining its actual decoder update, sparse log, and
initialization-failure marker. This module composes that replay with the
checked unoccupied local lifecycle and characterizes its unique proposal
memory without introducing another state machine or replay.
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Bandits.Support.ReferencePrelaunchLifecycleReplay

abbrev Parameters := Bandits.Support.ConstructorDimensions.Parameters
abbrev RateInput := Bandits.Support.ActiveFollowerDownAcceptance.RateInput

open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.CompletePublicTable
open Bandits.Support.ReferencePrelaunchFollower
open Bandits.Support.ActiveFollowerLifecycle
open Bandits.Support.ActiveFollowerLogging
open Bandits.Support.SparseCalendarReplay
open Bandits.Support.DeclaredFollowerLocalRound
open Bandits.Support.ActualReferenceInitializationBlock
open Bandits.Support.ReferenceInitializationRun

variable {p : Parameters}

/-- The literal restriction of a typed local history to its first `k` offsets.
No physical trace or new run is introduced. -/
def prefixHistory {n : ℕ} (history : LocalHistory p n) (k : ℕ)
    (hk : k ≤ n) : LocalHistory p k :=
  fun u => history (Fin.castLE hk u)

private theorem prefixHistory_castSucc {n k : ℕ}
    (history : LocalHistory p n) (hk : k ≤ n) (hk' : k + 1 ≤ n)
    (u : Fin k) :
    prefixHistory history (k + 1) hk' u.castSucc = prefixHistory history k hk u := by
  apply congrArg history
  exact Fin.ext rfl

/-- Restrict the existing corrected replay to one more entry. The result is
the existing corrected step on the previous replay state. -/
private theorem replay_prefix_succ {n : ℕ} (eta : LearningRate)
    (i : Fin (p.m - 1)) (row : CompleteRow p) (alpha : Activation p)
    (history : LocalHistory p n) (hn : n ≤ p.T) (k : ℕ) (hk : k < n) :
    replay eta i row alpha (prefixHistory history (k + 1) (Nat.succ_le_of_lt hk))
        (Nat.le_trans (Nat.succ_le_of_lt hk) hn) =
      step i row alpha ⟨k, by omega⟩ (prefixHistory history (k + 1)
        (Nat.succ_le_of_lt hk) (Fin.last k))
        (replay eta i row alpha (prefixHistory history k (Nat.le_of_lt hk))
          (Nat.le_trans (Nat.le_of_lt hk) hn)) := by
  have hshort : (fun u : Fin k => prefixHistory history (k + 1)
      (Nat.succ_le_of_lt hk) u.castSucc) =
      prefixHistory history k (Nat.le_of_lt hk) := by
    funext u
    exact prefixHistory_castSucc history (Nat.le_of_lt hk) (Nat.succ_le_of_lt hk) u
  rw [ActualReferenceInitializationBlock.replay_succ]
  rw [hshort]

/-- For a corrected unoccupied step, both lifecycle boundaries succeed with
the same memory. Checked logging records exactly the existing `buffer ++
logAt` update; the corrected replay still retains its actual decoder batch
and ORs `passing_at` into the failure marker. -/
theorem corrected_step_lifecycle (rate : RateInput p)
    (i : Fin (p.m - 1)) (row : CompleteRow p) (alpha : Activation p)
    (t : Fin p.T) (own : Fin p.K × Observation p)
    (s : State p rate.eta) (memory : LocalMemory p)
    (hactive : alpha.val ≤ t.val + 1)
    (hunoccupied : s.status = .unoccupied)
    (hdomain : localStateDomainValid s)
    (hchronological : ∀ r ∈ s.buffer, r.calendarRound < t.val + 1) :
    startRound rate.eta t s memory = .ok (s, memory) ∧
    (∃ logged, checkedLogging i row alpha t own s = .ok logged ∧
      logged = {s with buffer := s.buffer ++ logAt i row alpha t own}) ∧
    localStateDomainValid (step i row alpha t own s) ∧
    (step i row alpha t own s).lastDown = s.lastDown ∧
    (step i row alpha t own s).S = s.S ∧
    (step i row alpha t own s).delta = s.delta ∧
    (step i row alpha t own s).backlog = s.backlog ∧
    (step i row alpha t own s).status = .unoccupied ∧
    (step i row alpha t own s).downBatch = (decodeAt i row alpha t own s.downBatch).1 ∧
    (step i row alpha t own s).buffer = s.buffer ++ logAt i row alpha t own ∧
    (step i row alpha t own s).downBatch.pending.length <
      Bandits.Support.AffineBatchDecoder.quota p ∧
    (∀ b ∈ (step i row alpha t own s).downBatch.completed,
      b.length = Bandits.Support.AffineBatchDecoder.quota p) ∧
    Bandits.Support.AffineBatchDecoder.collected (step i row alpha t own s).downBatch =
      Bandits.Support.AffineBatchDecoder.collected s.downBatch ++
        Bandits.Support.AffineBatchDecoder.positiveAt p
          (traceAt i row alpha t own) t ∧
    (step i row alpha t own s).initializationFailure =
      (s.initializationFailure || decide (passing_at rate.eta i row alpha t own s.downBatch)) ∧
    releaseAndFinish rate i row t own.2 s memory (step i row alpha t own s) =
      .ok (step i row alpha t own s, memory) := by
  have hlogging := checkedLogging_success_of_chronological i row alpha t own s
    hdomain.2.1 hchronological hunoccupied
  obtain ⟨logged, hchecked, _, _, _, hloggedDomain⟩ := hlogging
  have hloggedEq : logged = loggingUpdate i row alpha t own s :=
    (checkedLogging_success_iff i row alpha t own s logged).mp hchecked |>.2.1
  have hloggedExact : logged = {s with buffer := s.buffer ++ logAt i row alpha t own} := by
    simpa [loggingUpdate, loggingBranch, hactive, hunoccupied] using hloggedEq
  have hregs := step_registers i row alpha t own s
  obtain ⟨hdown, hS, hdelta, hbacklog, hstatus⟩ := hregs
  have hbatch := step_batch_spec i row alpha t own s hunoccupied
    hdomain.2.2.1 hdomain.2.2.2
  obtain ⟨hpending, hcompleted, hcollected⟩ := hbatch
  have hstepBuffer : (step i row alpha t own s).buffer = s.buffer ++ logAt i row alpha t own := by
    simp [step, hunoccupied]
  have hloggedBuffer : (step i row alpha t own s).buffer = logged.buffer := by
    rw [hstepBuffer, hloggedExact]
  have hstepBufferValid : localBufferValid (step i row alpha t own s) := by
    rcases hloggedDomain with ⟨hrounds, hkeys, hobservations⟩
    refine ⟨?_, ?_, ?_⟩
    · intro r hr
      exact hrounds r (hloggedBuffer ▸ hr)
    · simpa only [hloggedBuffer] using hkeys
    · intro r hr
      exact hobservations r (hloggedBuffer ▸ hr)
  have hstepDomain : localStateDomainValid (step i row alpha t own s) := by
    rcases hdomain.1 with ⟨hSdom, hdeltadom, hbacklogdom⟩
    refine ⟨?_, hstepBufferValid, ⟨hpending, hcompleted⟩⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [hS]
      exact hSdom
    · rw [hdelta]
      exact hdeltadom
    · rw [hbacklog]
      exact hbacklogdom
  have hstart := startRound_unoccupied rate.eta t s memory hdomain hunoccupied
  have hstatus' : (step i row alpha t own s).status = .unoccupied := by
    rw [hstatus, hunoccupied]
  have hrelease := releaseAfterService_unoccupied rate.eta
    i t
    (publicRowOfCompleteRow row t) own.2 s (step i row alpha t own s) hunoccupied
  have hfinish := releaseAndFinish_unoccupied_memory rate i row t own.2 s memory
    (step i row alpha t own s) (step i row alpha t own s) hrelease hstepDomain hstatus'
  refine ⟨hstart, ⟨logged, hchecked, hloggedExact⟩, hstepDomain, hdown, hS, hdelta,
    hbacklog, hstatus', ?_, hstepBuffer, hpending, hcompleted, hcollected, ?_, hfinish⟩
  · simp [step, hunoccupied]
  · simp [step, hunoccupied]

/-- Every adjacent prefix of the existing corrected replay composes with the
local lifecycle for an arbitrary carried memory. This is the frame used when
an already activated follower continues through a block replay. -/
theorem replay_prefix_step_lifecycle {n : ℕ} (rate : RateInput p)
    (i : Fin (p.m - 1)) (row : CompleteRow p) (alpha : Activation p)
    (history : LocalHistory p n) (hn : n ≤ p.T) (k : ℕ) (hbefore : k < n)
    (hactive : alpha.val ≤ k + 1) (memory : LocalMemory p) :
    let state := replay rate.eta i row alpha (prefixHistory history k (Nat.le_of_lt hbefore))
      (Nat.le_trans (Nat.le_of_lt hbefore) hn)
    let nextState := replay rate.eta i row alpha
      (prefixHistory history (k + 1) (Nat.succ_le_of_lt hbefore))
      (Nat.le_trans (Nat.succ_le_of_lt hbefore) hn)
    startRound rate.eta ⟨k, by omega⟩ state memory = .ok (state, memory) ∧
      releaseAndFinish rate i row ⟨k, by omega⟩ (history ⟨k, by omega⟩).2
        state memory nextState = .ok (nextState, memory) := by
  dsimp only
  let hk : k ≤ n := Nat.le_of_lt hbefore
  let hk1 : k + 1 ≤ n := Nat.succ_le_of_lt hbefore
  let state := replay rate.eta i row alpha (prefixHistory history k hk)
    (Nat.le_trans hk hn)
  let nextState := replay rate.eta i row alpha (prefixHistory history (k + 1) hk1)
    (Nat.le_trans hk1 hn)
  let t : Fin p.T := ⟨k, by omega⟩
  let own := history (⟨k, by omega⟩ : Fin n)
  have hdomain : localStateDomainValid state :=
    ActualReferenceInitializationBlock.replay_domain_valid rate.eta i row alpha
      (prefixHistory history k hk) (Nat.le_trans hk hn)
  have hunoccupied : state.status = .unoccupied :=
    (replay_registers rate.eta i row alpha (prefixHistory history k hk)
      (Nat.le_trans hk hn)).2.2.2.2.2
  have hchronological : ∀ r ∈ state.buffer, r.calendarRound < t.val + 1 := by
    intro r hr
    obtain ⟨u, _, hround, _, _, _⟩ :=
      replay_buffer_fields rate.eta i row alpha (prefixHistory history k hk)
        (Nat.le_trans hk hn) r hr
    rw [hround]
    exact Nat.add_lt_add_right u.isLt 1
  have hstep := corrected_step_lifecycle rate i row alpha t own state memory
    (by simpa [t] using hactive) hunoccupied hdomain hchronological
  rcases hstep with ⟨hstart, _, _, _, _, _, _, _, _, _, _, _, _, _, hrelease⟩
  have hsuccessor := replay_prefix_succ rate.eta i row alpha history hn k hbefore
  have hown : prefixHistory history (k + 1) (Nat.succ_le_of_lt hbefore) (Fin.last k) =
      history ⟨k, by omega⟩ := by
    apply congrArg history
    exact Fin.ext rfl
  rw [hsuccessor]
  rw [hown]
  exact ⟨by simpa [t, state, own] using hstart,
    by simpa [t, state, own] using hrelease⟩

/-- Before activation, adjacent prefixes use the existing skipped-step branch:
the actual replay state is unchanged, no sparse record is logged, and the
decoder returns no parsed DOWN record. No local lifecycle call is made in
these rounds. -/
theorem replay_prefix_before_activation {n : ℕ} (rate : RateInput p)
    (i : Fin (p.m - 1)) (row : CompleteRow p) (alpha : Activation p)
    (history : LocalHistory p n) (hn : n ≤ p.T) (k : ℕ) (hbefore : k < n)
    (hpre : k + 1 < alpha.val) :
    let state := replay rate.eta i row alpha
      (prefixHistory history k (Nat.le_of_lt hbefore))
      (Nat.le_trans (Nat.le_of_lt hbefore) hn)
    let nextState := replay rate.eta i row alpha
      (prefixHistory history (k + 1) (Nat.succ_le_of_lt hbefore))
      (Nat.le_trans (Nat.succ_le_of_lt hbefore) hn)
    step i row alpha ⟨k, by omega⟩ (history ⟨k, by omega⟩) state = state ∧
      nextState = state ∧
      logAt i row alpha ⟨k, by omega⟩ (history ⟨k, by omega⟩) = [] ∧
      decodeAt i row alpha ⟨k, by omega⟩ (history ⟨k, by omega⟩) state.downBatch =
        (state.downBatch, none) ∧
      parsedAt rate.eta i row alpha ⟨k, by omega⟩ (history ⟨k, by omega⟩)
        state.downBatch = none := by
  dsimp only
  let hk : k ≤ n := Nat.le_of_lt hbefore
  let hk1 : k + 1 ≤ n := Nat.succ_le_of_lt hbefore
  let state := replay rate.eta i row alpha (prefixHistory history k hk)
    (Nat.le_trans hk hn)
  let nextState := replay rate.eta i row alpha (prefixHistory history (k + 1) hk1)
    (Nat.le_trans hk1 hn)
  let t : Fin p.T := ⟨k, by omega⟩
  let own := history (⟨k, by omega⟩ : Fin n)
  have hpre' : t.val + 1 < alpha.val := by simpa [t] using hpre
  have hna : ¬ alpha.val ≤ t.val + 1 := Nat.not_le.mpr hpre'
  have hstepNoop : step i row alpha t own state = state :=
    step_before_activation i row alpha t own state hpre'
  have hlog : logAt i row alpha t own = [] := by
    simp only [logAt, loggingTestsPass, loggingRound, hna, decide_false,
      Bool.false_eq_true, false_and, ite_false]
  have hdecode : decodeAt i row alpha t own state.downBatch =
      (state.downBatch, none) := by
    simp only [decodeAt, downInput, hna, false_and, decide_false,
      Bool.false_eq_true, ite_false]
  have hparsed : parsedAt rate.eta i row alpha t own state.downBatch = none := by
    unfold parsedAt
    rw [hdecode]
    rfl
  have hsuccessor := replay_prefix_succ rate.eta i row alpha history hn k hbefore
  have hown : prefixHistory history (k + 1) hk1 (Fin.last k) =
      history ⟨k, by omega⟩ := by
    apply congrArg history
    exact Fin.ext rfl
  have hnext : nextState = step i row alpha t own state := by
    dsimp only [nextState, state, t, own]
    rw [hsuccessor, hown]
  refine ⟨by simpa [t, state, own] using hstepNoop, hnext.trans hstepNoop, ?_, ?_, ?_⟩
  · simpa [t, own] using hlog
  · simpa [t, own] using hdecode
  · simpa [t, own] using hparsed

/-- Memory indices start at the first effective local round `alpha-1` and
include the terminal prefix value. The state at each cut is exactly the
existing corrected replay of the restricted supplied history. -/
theorem replay_proposal_memory_characterization {n : ℕ}
    (rate : RateInput p) (i : Fin (p.m - 1)) (row : CompleteRow p)
    (alpha : Activation p) (history : LocalHistory p n) (hn : n ≤ p.T)
    (hcut : alpha.val ≤ n + 1) :
    let a0 := alpha.val - 1
    let stateAt : (k : ℕ) → k ≤ n → State p rate.eta := fun k hk =>
      replay rate.eta i row alpha (prefixHistory history k hk) (Nat.le_trans hk hn)
    stateAt a0 (by omega) = initial p rate.eta ∧
    (∃! memory : Fin (n - a0 + 1) → LocalMemory p,
      memory ⟨0, by omega⟩ = initialMemory p ∧
      (∀ k (hactive : a0 ≤ k) (hbefore : k < n),
        let hk : k ≤ n := Nat.le_of_lt hbefore
        let state := replay rate.eta i row alpha (prefixHistory history k hk)
          (Nat.le_trans hk hn)
        let nextState := replay rate.eta i row alpha
          (prefixHistory history (k + 1) (Nat.succ_le_of_lt hbefore))
          (Nat.le_trans (Nat.succ_le_of_lt hbefore) hn)
        let index : Fin (n - a0 + 1) := ⟨k - a0, by omega⟩
        let nextIndex : Fin (n - a0 + 1) := ⟨k + 1 - a0, by omega⟩
        startRound rate.eta ⟨k, by omega⟩ state (memory index) =
            .ok (state, memory index) ∧
          releaseAndFinish rate i row ⟨k, by omega⟩ (history ⟨k, by omega⟩).2
            state (memory index) nextState = .ok (nextState, memory nextIndex))) ∧
    (∀ memory : Fin (n - a0 + 1) → LocalMemory p,
      memory ⟨0, by omega⟩ = initialMemory p →
      (∀ k (hactive : a0 ≤ k) (hbefore : k < n),
        let hk : k ≤ n := Nat.le_of_lt hbefore
        let state := replay rate.eta i row alpha (prefixHistory history k hk)
          (Nat.le_trans hk hn)
        let nextState := replay rate.eta i row alpha
          (prefixHistory history (k + 1) (Nat.succ_le_of_lt hbefore))
          (Nat.le_trans (Nat.succ_le_of_lt hbefore) hn)
        let index : Fin (n - a0 + 1) := ⟨k - a0, by omega⟩
        let nextIndex : Fin (n - a0 + 1) := ⟨k + 1 - a0, by omega⟩
        startRound rate.eta ⟨k, by omega⟩ state (memory index) =
            .ok (state, memory index) ∧
          releaseAndFinish rate i row ⟨k, by omega⟩ (history ⟨k, by omega⟩).2
            state (memory index) nextState = .ok (nextState, memory nextIndex)) →
      (∀ j, memory j = initialMemory p) ∧
        memory (Fin.last (n - a0)) = initialMemory p) := by
  classical
  dsimp only
  let a0 : ℕ := alpha.val - 1
  have ha0le : a0 ≤ n := by dsimp [a0]; omega
  let stateAt : (k : ℕ) → k ≤ n → State p rate.eta := fun k hk =>
    replay rate.eta i row alpha (prefixHistory history k hk) (Nat.le_trans hk hn)
  have hpre : a0 < alpha.val := by dsimp [a0]; omega
  have hbase : stateAt a0 ha0le = initial p rate.eta := by
    simpa [stateAt] using replay_before_activation rate.eta i row alpha
      (prefixHistory history a0 ha0le) (Nat.le_trans ha0le hn) hpre
  let memory0 : Fin (n - a0 + 1) → LocalMemory p := fun _ => initialMemory p
  have hrec (memory : Fin (n - a0 + 1) → LocalMemory p)
      (hzero : memory ⟨0, by omega⟩ = initialMemory p)
      (heqs : ∀ k (hactive : alpha.val - 1 ≤ k) (hbefore : k < n),
        let hk : k ≤ n := Nat.le_of_lt hbefore
        let state := replay rate.eta i row alpha (prefixHistory history k hk)
          (Nat.le_trans hk hn)
        let nextState := replay rate.eta i row alpha
          (prefixHistory history (k + 1) (Nat.succ_le_of_lt hbefore))
          (Nat.le_trans (Nat.succ_le_of_lt hbefore) hn)
        let index : Fin (n - (alpha.val - 1) + 1) := ⟨k - (alpha.val - 1), by omega⟩
        let nextIndex : Fin (n - (alpha.val - 1) + 1) :=
          ⟨k + 1 - (alpha.val - 1), by omega⟩
        startRound rate.eta ⟨k, by omega⟩ state (memory index) =
            .ok (state, memory index) ∧
          releaseAndFinish rate i row ⟨k, by omega⟩ (history ⟨k, by omega⟩).2
            state (memory index) nextState = .ok (nextState, memory nextIndex)) :
      ∀ j, memory j = initialMemory p := by
    have hindices : ∀ q (hq : q ≤ n - a0),
        memory (⟨q, Nat.lt_succ_of_le hq⟩ : Fin (n - a0 + 1)) = initialMemory p := by
      intro q
      induction q with
      | zero =>
          intro _
          simpa using hzero
      | succ q ih =>
          intro hq
          have hbefore : a0 + q < n := by
            calc
              a0 + q < a0 + (n - a0) :=
                Nat.add_lt_add_left (Nat.lt_of_succ_le hq) a0
              _ = n := Nat.add_sub_of_le ha0le
          have hactive : alpha.val - 1 ≤ a0 + q := by dsimp [a0]; omega
          let index : Fin (n - a0 + 1) :=
            ⟨q, Nat.lt_succ_of_le (Nat.le_of_lt (Nat.lt_of_succ_le hq))⟩
          let nextIndex : Fin (n - a0 + 1) := ⟨q + 1, Nat.lt_succ_of_le hq⟩
          have hspecified := heqs (a0 + q) hactive hbefore
          rcases hspecified with ⟨_, hspecified⟩
          have hactual := replay_prefix_step_lifecycle rate i row alpha history hn
            (a0 + q) hbefore (by dsimp [a0]; omega)
            (memory index)
          rcases hactual with ⟨_, hactual⟩
          have hidx :
              (⟨a0 + q - (alpha.val - 1), by omega⟩ :
                Fin (n - (alpha.val - 1) + 1)) = index := by
            apply Fin.ext
            simp [index, a0]
          have hidxNext :
              (⟨a0 + q + 1 - (alpha.val - 1), by omega⟩ :
                Fin (n - (alpha.val - 1) + 1)) = nextIndex := by
            apply Fin.ext
            simp [nextIndex, a0, Nat.add_assoc]
          rw [hidx, hidxNext] at hspecified
          have hmem : memory nextIndex = memory index := by
            have hpair := Except.ok.inj (hactual.symm.trans hspecified)
            exact (Prod.mk.inj hpair).2.symm
          have hprev := ih (Nat.le_of_lt (Nat.lt_of_succ_le hq))
          have hnext := hmem.trans hprev
          simpa [nextIndex] using hnext
    intro j
    have hj : j.val ≤ n - a0 := by omega
    have h := hindices j.val hj
    simpa using h
  have hrec0 : ∀ k (hactive : alpha.val - 1 ≤ k) (hbefore : k < n),
      let hk : k ≤ n := Nat.le_of_lt hbefore
      let state := replay rate.eta i row alpha (prefixHistory history k hk)
        (Nat.le_trans hk hn)
      let nextState := replay rate.eta i row alpha
        (prefixHistory history (k + 1) (Nat.succ_le_of_lt hbefore))
        (Nat.le_trans (Nat.succ_le_of_lt hbefore) hn)
      let index : Fin (n - (alpha.val - 1) + 1) := ⟨k - (alpha.val - 1), by omega⟩
      let nextIndex : Fin (n - (alpha.val - 1) + 1) :=
        ⟨k + 1 - (alpha.val - 1), by omega⟩
      startRound rate.eta ⟨k, by omega⟩ state (memory0 index) =
          .ok (state, memory0 index) ∧
        releaseAndFinish rate i row ⟨k, by omega⟩ (history ⟨k, by omega⟩).2
          state (memory0 index) nextState = .ok (nextState, memory0 nextIndex) := by
    intro k hactive hbefore
    dsimp only
    have hactiveRound : alpha.val ≤ k + 1 := by omega
    have hlocal := replay_prefix_step_lifecycle rate i row alpha history hn k hbefore
      hactiveRound (memory0 ⟨k - (alpha.val - 1), by omega⟩)
    simpa [memory0] using hlocal
  have hconstant : ∀ memory : Fin (n - (alpha.val - 1) + 1) → LocalMemory p,
      memory ⟨0, by omega⟩ = initialMemory p →
      (∀ k (hactive : alpha.val - 1 ≤ k) (hbefore : k < n),
        let hk : k ≤ n := Nat.le_of_lt hbefore
        let state := replay rate.eta i row alpha (prefixHistory history k hk)
          (Nat.le_trans hk hn)
        let nextState := replay rate.eta i row alpha
          (prefixHistory history (k + 1) (Nat.succ_le_of_lt hbefore))
          (Nat.le_trans (Nat.succ_le_of_lt hbefore) hn)
        let index : Fin (n - (alpha.val - 1) + 1) := ⟨k - (alpha.val - 1), by omega⟩
        let nextIndex : Fin (n - (alpha.val - 1) + 1) :=
          ⟨k + 1 - (alpha.val - 1), by omega⟩
        startRound rate.eta ⟨k, by omega⟩ state (memory index) =
            .ok (state, memory index) ∧
          releaseAndFinish rate i row ⟨k, by omega⟩ (history ⟨k, by omega⟩).2
            state (memory index) nextState = .ok (nextState, memory nextIndex)) →
      (∀ j, memory j = initialMemory p) ∧
        memory (Fin.last (n - (alpha.val - 1))) = initialMemory p := by
    intro memory hzero heqs
    have hconst := hrec memory hzero heqs
    exact ⟨hconst, hconst (Fin.last (n - a0))⟩
  refine ⟨hbase, ?_, hconstant⟩
  refine ⟨memory0, ?_, ?_⟩
  · constructor
    · rfl
    · exact hrec0
  · intro memory hmemory
    have hconst := hconstant memory hmemory.1 hmemory.2
    funext j
    exact hconst.1 j

/-- A generated boundary before launch has not exhausted its block counter. -/
theorem run_completed_lt_of_no_crossing (x : ReferenceInitializationRun.Input p)
    (r : ℕ) (hr : r < n_boot p)
    (hc : (ReferenceInitializationRun.run x r).crossing = none) :
    (ReferenceInitializationRun.run x r).completed < n_boot p := by
  have hcompleted := ActualReferenceInitializationHorizon.run_completed_eq_of_no_crossing
    x r (Nat.le_of_lt hr) hc
  rw [hcompleted]
  exact hr

/-- A saved first declaration is generated at the clipped block end plus one.
Its ordinary state is the actual saved-branch initial state, so the lifecycle
starts with no saved proposal token and has made no preactivation call. -/
theorem saved_declaration_initial_lifecycle (x : ReferenceInitializationRun.Input p)
    (r : ℕ) (hr : r < n_boot p)
    (hc : (ReferenceInitializationRun.run x r).crossing = none)
    (i : ActiveRoundActions.Follower p.m)
    (hi : i ∈ ReferenceInitializationRun.uninformed (ReferenceInitializationRun.run x r))
    (hsaved : (ReferenceInitializationRun.candidate x (ReferenceInitializationRun.run x r)
      (run_completed_lt_of_no_crossing x r hr hc) ⟨i, hi⟩).pending = true) :
    (ReferenceInitializationRun.finishBlock x (ReferenceInitializationRun.run x r)
      (run_completed_lt_of_no_crossing x r hr hc)).activation i =
        some (ReferenceInitializationRun.boundaryActivation (ReferenceInitializationRun.run x r)) ∧
    ReferenceInitializationRun.ordinary x
      (ReferenceInitializationRun.finishBlock x (ReferenceInitializationRun.run x r)
        (run_completed_lt_of_no_crossing x r hr hc)) i =
      ReferencePrelaunchFollower.initial p x.eta ∧
    ReferenceInitializationRun.elapsed p
      ((ReferenceInitializationRun.run x r).completed + 1) <
        (ReferenceInitializationRun.boundaryActivation (ReferenceInitializationRun.run x r)).val ∧
    ActiveFollowerLifecycle.initialMemory p = ⟨none⟩ := by
  have hforced := ReferenceInitializationRun.run_no_forced_before_launch x r hc i
  have hactivation := ReferenceInitializationRun.saved_activation x
    (ReferenceInitializationRun.run x r) (run_completed_lt_of_no_crossing x r hr hc)
    ⟨i, hi⟩ hsaved
  have hstate := ReferenceInitializationRun.ordinary_finishBlock_of_saved x
    (ReferenceInitializationRun.run x r) (run_completed_lt_of_no_crossing x r hr hc)
    ⟨i, hi⟩ hsaved hforced
  refine ⟨hactivation, hstate, ?_, rfl⟩
  simp [ReferenceInitializationRun.boundaryActivation]

/-- A forced correction also uses the actual clipped block-end activation.
The source forcing equation retains its failure marker while the new ordinary
state and its proposal memory both start fresh, with zero preceding local
calls and no fabricated proposal read. -/
theorem forced_correction_initial_lifecycle (x : ReferenceInitializationRun.Input p)
    (r : ℕ) (hr : r < n_boot p)
    (hc : (ReferenceInitializationRun.run x r).crossing = none)
    (i : ActiveRoundActions.Follower p.m)
    (hforced : ReferenceInitializationRun.forced x (ReferenceInitializationRun.run x r)
      (run_completed_lt_of_no_crossing x r hr hc) i = true) :
    (ReferenceInitializationRun.finishBlock x (ReferenceInitializationRun.run x r)
      (run_completed_lt_of_no_crossing x r hr hc)).activation i =
        some (ReferenceInitializationRun.boundaryActivation (ReferenceInitializationRun.run x r)) ∧
    ReferenceInitializationRun.ordinary x
      (ReferenceInitializationRun.finishBlock x (ReferenceInitializationRun.run x r)
        (run_completed_lt_of_no_crossing x r hr hc)) i =
      ReferencePrelaunchFollower.initial p x.eta ∧
    (ReferenceInitializationRun.finishBlock x (ReferenceInitializationRun.run x r)
      (run_completed_lt_of_no_crossing x r hr hc)).forcedFailure i = true ∧
    ReferenceInitializationRun.elapsed p
      ((ReferenceInitializationRun.run x r).completed + 1) <
        (ReferenceInitializationRun.boundaryActivation (ReferenceInitializationRun.run x r)).val ∧
    ActiveFollowerLifecycle.initialMemory p = ⟨none⟩ := by
  have hactivation :
      (ReferenceInitializationRun.finishBlock x (ReferenceInitializationRun.run x r)
        (run_completed_lt_of_no_crossing x r hr hc)).activation i =
          some (ReferenceInitializationRun.boundaryActivation (ReferenceInitializationRun.run x r)) := by
    change ReferenceInitializationRun.finalActivation x (ReferenceInitializationRun.run x r)
      (run_completed_lt_of_no_crossing x r hr hc) i = _
    simp [ReferenceInitializationRun.finalActivation, hforced]
  have hstate := ReferenceInitializationRun.forced_ordinary x
    (ReferenceInitializationRun.run x r) (run_completed_lt_of_no_crossing x r hr hc) i hforced
  have hstate' : ReferenceInitializationRun.ordinary x
      (ReferenceInitializationRun.finishBlock x (ReferenceInitializationRun.run x r)
        (run_completed_lt_of_no_crossing x r hr hc)) i =
      ReferencePrelaunchFollower.initial p x.eta := by
    rw [hstate, ReferencePrelaunchFollower.forcedAtLaunch_state]
  have hfailure :
      (ReferenceInitializationRun.finishBlock x (ReferenceInitializationRun.run x r)
        (run_completed_lt_of_no_crossing x r hr hc)).forcedFailure i = true := by
    change (ReferenceInitializationRun.run x r).forcedFailure i ||
      ReferenceInitializationRun.forced x (ReferenceInitializationRun.run x r)
        (run_completed_lt_of_no_crossing x r hr hc) i = true
    simp [hforced]
  refine ⟨hactivation, hstate', hfailure, ?_, rfl⟩
  simp [ReferenceInitializationRun.boundaryActivation]

end Bandits.Support.ReferencePrelaunchLifecycleReplay

end
