/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.InitializationRowObservables
public import Bandits.Support.ReferenceInitializationRun
public import Bandits.Support.ReferencePrelaunchPhysicalReplay

/-!
# Operational provenance for reference initialization failure

The source event is the union of a launch correction after the strict monitor
crossing and an accepted ordinary DOWN parse suppressed before launch. The
definitions here witness each cause in the generated reference run, including
the processed block, its generated histories, and its carried decoder state.

Sources: `sources/zip4/manuscript/07_public_setup.tex:129-140`,
`sources/zip4/manuscript/08_main_theorem.tex:29-42,67-83`, and
`sources/zip4/manuscript/appendix_b_communication.tex:376-379`.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.ActiveRoundActions
open Bandits.Support.ReferenceInitializationRun
open Bandits.Support.ReferencePrelaunchPhysicalReplay
open Bandits.Support.ReferencePrelaunchFollower
open Bandits.Support.InitializationRowObservables
open Bandits.Support.OrdinaryMessageCodec
open scoped Classical BigOperators

namespace Bandits.Support.InitializationFailureProvenance

abbrev Parameters := ConstructorDimensions.Parameters

/-- The focal follower is corrected on this processed block. The incoming run
has not crossed and has not previously forced this follower. The monitor is
tested after the physical counter update, and `declaredActivation` includes
pending declarations before the correction test. -/
def forcedCorrectionAt {p : Parameters} (x : ReferenceInitializationRun.Input p)
    (s : Fin (n_boot p)) (i : ActiveRoundActions.Follower p.m) : Prop :=
  ∃ h : (ReferenceInitializationRun.run x s.val).completed < n_boot p,
    let b := ReferenceInitializationRun.run x s.val
    b.crossing = none ∧ b.completed = s.val ∧ b.forcedFailure i = false ∧
      BootstrapLaunchMonitor.monitorValue p (ReferenceInitializationRun.updatedCounters x b h) >
        4 * BootstrapStartupCostScale.Q x.C_star x.C_h p ∧
      ReferenceInitializationRun.declaredActivation x b h i = none ∧
      ReferenceInitializationRun.forced x b h i = true ∧
      (ReferenceInitializationRun.finishBlock x b h).forcedFailure i = true

/-- The raw generated-block DOWN witness before the terminal endpoint bound is
proved. Every decision is a member of the parser audit for `blockIndices`,
starting with the carried ordinary state. -/
def generatedBlockDown {p : Parameters} (x : ReferenceInitializationRun.Input p)
    (b : ReferenceInitializationRun.Boundary p) (h : b.completed < n_boot p)
    (i : ActiveRoundActions.Follower p.m) : Prop :=
  b.forcedFailure i = false ∧
    ∃ a, ∃ ha : b.activation i = some a,
      let z := ReferenceInitializationRun.replayInput x b h i a ha;
      ∃ d ∈ ReferencePrelaunchFollower.decisions
        (BootstrapPhysicalInput.sourceFollowerIndex p i) x.row a
        (ReferencePrelaunchPhysicalReplay.chronologicalHistory z)
        (ReferencePrelaunchPhysicalReplay.blockEnd_le_T p (ReferenceInitializationRun.nextBlock b h))
        (ReferencePrelaunchPhysicalReplay.blockIndices z)
        (ReferenceInitializationRun.ordinary x b i),
        OrdinaryMessageCodec.acceptDown (ReferencePrelaunchFollower.codecParams p x.eta)
          0 (d.1.val + 1) d.2

/-- One accepted parsed DOWN decision from the generated chronological replay
of a processed block. `blockIndices` preserves the physical block interval;
the incoming ordinary state carries earlier logs and partial decoder batches.
The explicit `Fin T` time and strict launch-prefix inequality are part of the
witness. -/
def suppressedDownAt {p : Parameters} (x : ReferenceInitializationRun.Input p)
    (s : Fin (n_boot p)) (i : ActiveRoundActions.Follower p.m) : Prop :=
  ∃ h : (ReferenceInitializationRun.run x s.val).completed < n_boot p,
    let b := ReferenceInitializationRun.run x s.val
    b.crossing = none ∧ b.completed = s.val ∧ b.forcedFailure i = false ∧
      ∃ a, ∃ ha : b.activation i = some a,
        let z := ReferenceInitializationRun.replayInput x b h i a ha;
        ∃ d ∈ ReferencePrelaunchFollower.decisions
          (BootstrapPhysicalInput.sourceFollowerIndex p i) x.row a
          (ReferencePrelaunchPhysicalReplay.chronologicalHistory z)
          (ReferencePrelaunchPhysicalReplay.blockEnd_le_T p (ReferenceInitializationRun.nextBlock b h))
          (ReferencePrelaunchPhysicalReplay.blockIndices z)
          (ReferenceInitializationRun.ordinary x b i),
          OrdinaryMessageCodec.acceptDown (ReferencePrelaunchFollower.codecParams p x.eta)
            0 (d.1.val + 1) d.2 ∧ d.1.val + 1 < ReferenceInitializationRun.launchRound x

/-- The two witnessed reference causes: a corrected follower at a strict
post-declaration crossing, or an accepted ordinary DOWN parse in a processed
physical prelaunch block. -/
def operationalInitializationFailure {p : Parameters}
    (x : ReferenceInitializationRun.Input p) : Prop :=
  (∃ i : ActiveRoundActions.Follower p.m,
    ∃ s : Fin (n_boot p), forcedCorrectionAt x s i) ∨
  (∃ i : ActiveRoundActions.Follower p.m,
    ∃ s : Fin (n_boot p), suppressedDownAt x s i)

/-- The ordinary state stays in the selected-row unoccupied regime, so its
accepted start remains zero and the parsed-DOWN test is precisely the source
`acceptDown codecParams 0 (decisionTime+1)` test. -/
theorem ordinary_replay_unoccupied_registers {p : Parameters}
    (x : ReferenceInitializationRun.Input p)
    (b : ReferenceInitializationRun.Boundary p) (i : ActiveRoundActions.Follower p.m) :
    (ReferenceInitializationRun.ordinary x b i).lastDown = none ∧
      ReferencePrelaunchFollower.acceptedStart (ReferenceInitializationRun.ordinary x b i) = 0 ∧
      (ReferenceInitializationRun.ordinary x b i).status = .unoccupied := by
  obtain ⟨hdown, hstart, _, _, _, hstatus⟩ :=
    ReferenceInitializationRun.ordinary_registers x b i
  exact ⟨hdown, hstart, hstatus⟩

/-- One step of the generated run never moves the completed-block counter
backwards. -/
theorem run_completed_succ_le {p : Parameters}
    (x : ReferenceInitializationRun.Input p) (r : ℕ) :
    (ReferenceInitializationRun.run x r).completed ≤
      (ReferenceInitializationRun.run x (r + 1)).completed := by
  rw [ReferenceInitializationRun.run_succ]
  by_cases hc : (ReferenceInitializationRun.run x r).crossing.isSome = true
  · rw [ReferenceInitializationRun.advance_of_crossing x _ hc]
  · have hn : (ReferenceInitializationRun.run x r).crossing = none := by
      cases hh : (ReferenceInitializationRun.run x r).crossing <;> simp_all
    by_cases he : (ReferenceInitializationRun.run x r).completed < n_boot p
    · rw [ReferenceInitializationRun.advance_of_no_crossing x _ hn he]
      simp [ReferenceInitializationRun.finishBlock]
    · rw [ReferenceInitializationRun.advance_of_exhausted x _ (Nat.le_of_not_gt he)]

/-- The generated run's completed-block field is monotone in its opportunity
index, including the stopped tail after launch. -/
theorem run_completed_mono {p : Parameters}
    (x : ReferenceInitializationRun.Input p) {r q : ℕ} (hr : r ≤ q) :
    (ReferenceInitializationRun.run x r).completed ≤
      (ReferenceInitializationRun.run x q).completed := by
  induction q with
  | zero =>
      have : r = 0 := by omega
      subst r
      exact le_rfl
  | succ q ih =>
      by_cases hrq : r ≤ q
      · exact (ih hrq).trans (run_completed_succ_le x q)
      · have hq : r = q + 1 := by omega
        subst r
        exact le_rfl

/-- Every physical round already present in the generated terminal history is
strictly before its accepted one-based launch endpoint. -/
theorem output_history_round_before_launch {p : Parameters}
    (x : ReferenceInitializationRun.Input p) (t : Fin p.T)
    (ht : t.val + 1 ≤ ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output x).completed) :
    t.val + 1 < ReferenceInitializationRun.launchRound x := by
  by_cases hc : (ReferenceInitializationRun.output x).crossing.isSome = true
  · unfold ReferenceInitializationRun.launchRound
    have htlt : t.val < ReferenceInitializationRun.elapsed p
        (ReferenceInitializationRun.output x).completed :=
      Nat.lt_of_lt_of_le (Nat.lt_succ_self _) ht
    simpa [hc] using htlt
  · have hn : (ReferenceInitializationRun.output x).crossing = none := by
      cases hh : (ReferenceInitializationRun.output x).crossing <;> simp_all
    have he := ReferenceInitializationRun.output_elapsed_of_no_crossing x hn
    have ht' : t.val + 1 ≤ p.T := by simp [he] at ht ⊢
    have hstrict : t.val + 1 < p.T + 1 := Nat.lt_succ_of_le ht'
    simp [ReferenceInitializationRun.launchRound, hn, hstrict]

/-- An element of a generated block's replay list lies in its actual clipped
calendar interval. -/
theorem blockIndices_member_bounds {p : Parameters} {s : Fin (n_boot p)}
    (z : ReferencePrelaunchPhysicalReplay.Input p s)
    {u : Fin (ReferencePrelaunchPhysicalReplay.blockEnd p s)}
    (hu : u ∈ ReferencePrelaunchPhysicalReplay.blockIndices z) :
    ReferencePrelaunchPhysicalReplay.blockStart p s ≤ u.val ∧
      u.val < ReferencePrelaunchPhysicalReplay.blockEnd p s := by
  have hu' : u ∈
      (List.ofFn (fun v : Fin (ReferencePrelaunchPhysicalReplay.blockLength p s) => v)).map
        (ReferencePrelaunchPhysicalReplay.blockEmbed (p := p) (s := s)) := by
    simpa only [ReferencePrelaunchPhysicalReplay.blockIndices] using hu
  rcases List.mem_map.mp hu' with ⟨v, hv, hvu⟩
  have hval : (ReferencePrelaunchPhysicalReplay.blockEmbed v).val = u.val :=
    congrArg Fin.val hvu
  constructor
  · rw [← hval]
    simp only [ReferencePrelaunchPhysicalReplay.blockEmbed]
    exact Nat.le_add_right _ _
  · rw [← hval]
    exact (ReferencePrelaunchPhysicalReplay.blockEmbed v).isLt

/-- Every parsed decision in a processed reference block is at a genuine
physical round strictly before the terminal launch endpoint. -/
theorem blockDecision_before_launch {p : Parameters}
    (x : ReferenceInitializationRun.Input p) (s : Fin (n_boot p))
    (b : ReferenceInitializationRun.Boundary p)
    (h : b.completed < n_boot p) (hb : b = ReferenceInitializationRun.run x s.val)
    (hcross : b.crossing = none) (hcompleted : b.completed = s.val)
    (i : ActiveRoundActions.Follower p.m) (a : Activation p)
    (ha : b.activation i = some a)
    (d : Fin p.T × DownRecord (ReferencePrelaunchFollower.codecParams p x.eta))
    (hd : d ∈ ReferencePrelaunchFollower.decisions
      (BootstrapPhysicalInput.sourceFollowerIndex p i) x.row a
      (ReferencePrelaunchPhysicalReplay.chronologicalHistory
        (ReferenceInitializationRun.replayInput x b h i a ha))
      (ReferencePrelaunchPhysicalReplay.blockEnd_le_T p
        (ReferenceInitializationRun.nextBlock b h))
      (ReferencePrelaunchPhysicalReplay.blockIndices
        (ReferenceInitializationRun.replayInput x b h i a ha))
      (ReferenceInitializationRun.ordinary x b i)) :
    d.1.val + 1 < ReferenceInitializationRun.launchRound x := by
  let z := ReferenceInitializationRun.replayInput x b h i a ha
  have hparsed := (ReferencePrelaunchFollower.mem_decisions_iff
    (BootstrapPhysicalInput.sourceFollowerIndex p i) x.row a
    (ReferencePrelaunchPhysicalReplay.chronologicalHistory z)
    (ReferencePrelaunchPhysicalReplay.blockEnd_le_T p
      (ReferenceInitializationRun.nextBlock b h))
    (ReferencePrelaunchPhysicalReplay.blockIndices z)
    (ReferenceInitializationRun.ordinary x b i) d).mp hd
  obtain ⟨before, u, after, hlist, htime, _⟩ := hparsed
  have humem : u ∈ ReferencePrelaunchPhysicalReplay.blockIndices z := by
    rw [hlist]
    simp
  have hubounds := blockIndices_member_bounds z humem
  have htimeval : d.1.val = u.val := by
    calc
      d.1.val =
          (ReferencePrelaunchFollower.calendar
            (ReferencePrelaunchPhysicalReplay.blockEnd_le_T p
              (ReferenceInitializationRun.nextBlock b h)) u).val :=
        congrArg Fin.val htime
      _ = u.val := rfl
  have hstep : ReferenceInitializationRun.run x (s.val + 1) =
      ReferenceInitializationRun.finishBlock x b h := by
    calc
      ReferenceInitializationRun.run x (s.val + 1) =
          ReferenceInitializationRun.advance x (ReferenceInitializationRun.run x s.val) :=
        ReferenceInitializationRun.run_succ x s.val
      _ = ReferenceInitializationRun.advance x b := by rw [← hb]
      _ = ReferenceInitializationRun.finishBlock x b h :=
        ReferenceInitializationRun.advance_of_no_crossing x b hcross h
  have hstepCompleted :
      (ReferenceInitializationRun.run x (s.val + 1)).completed = s.val + 1 := by
    rw [hstep]
    simp [ReferenceInitializationRun.finishBlock, hcompleted]
  have hindex : s.val + 1 ≤ n_boot p := Nat.succ_le_of_lt s.isLt
  have hout : s.val + 1 ≤ (ReferenceInitializationRun.output x).completed := by
    change s.val + 1 ≤ (ReferenceInitializationRun.run x (n_boot p)).completed
    rw [← hstepCompleted]
    exact run_completed_mono x hindex
  have helapsed := ReferenceInitializationRun.elapsed_mono p hout
  have hphysical : d.1.val + 1 ≤ ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output x).completed := by
    calc
      d.1.val + 1 ≤ ReferencePrelaunchPhysicalReplay.blockEnd p
          (ReferenceInitializationRun.nextBlock b h) := by
        rw [htimeval]
        exact Nat.succ_le_of_lt hubounds.2
      _ = ReferenceInitializationRun.elapsed p (b.completed + 1) :=
        (ReferenceInitializationRun.elapsed_succ_eq_blockEnd b h).symm
      _ = ReferenceInitializationRun.elapsed p (s.val + 1) := by rw [hcompleted]
      _ ≤ ReferenceInitializationRun.elapsed p
          (ReferenceInitializationRun.output x).completed := helapsed
  exact output_history_round_before_launch x d.1 hphysical

/-- The generated block decision list records exactly parser outputs at actual
offsets in that block's physical calendar interval. -/
theorem blockDecision_is_parsed {p : Parameters} (x : ReferenceInitializationRun.Input p)
    (b : ReferenceInitializationRun.Boundary p) (h : b.completed < n_boot p)
    (i : ActiveRoundActions.Follower p.m) (a : Activation p)
    (ha : b.activation i = some a)
    (d : Fin p.T × DownRecord (ReferencePrelaunchFollower.codecParams p x.eta))
    (hd : d ∈ ReferencePrelaunchFollower.decisions
      (BootstrapPhysicalInput.sourceFollowerIndex p i) x.row a
      (ReferencePrelaunchPhysicalReplay.chronologicalHistory
        (ReferenceInitializationRun.replayInput x b h i a ha))
      (ReferencePrelaunchPhysicalReplay.blockEnd_le_T p
        (ReferenceInitializationRun.nextBlock b h))
      (ReferencePrelaunchPhysicalReplay.blockIndices
        (ReferenceInitializationRun.replayInput x b h i a ha))
      (ReferenceInitializationRun.ordinary x b i)) :
    ∃ before u after,
      ReferencePrelaunchPhysicalReplay.blockIndices
          (ReferenceInitializationRun.replayInput x b h i a ha) = before ++ u :: after ∧
      d.1 = ReferencePrelaunchFollower.calendar
          (ReferencePrelaunchPhysicalReplay.blockEnd_le_T p
            (ReferenceInitializationRun.nextBlock b h)) u ∧
      ReferencePrelaunchFollower.parsedAt x.eta
          (BootstrapPhysicalInput.sourceFollowerIndex p i) x.row a
          (ReferencePrelaunchFollower.calendar
            (ReferencePrelaunchPhysicalReplay.blockEnd_le_T p
              (ReferenceInitializationRun.nextBlock b h)) u)
          (ReferencePrelaunchPhysicalReplay.chronologicalHistory
            (ReferenceInitializationRun.replayInput x b h i a ha) u)
          (ReferencePrelaunchFollower.run
            (BootstrapPhysicalInput.sourceFollowerIndex p i) x.row a
            (ReferencePrelaunchPhysicalReplay.chronologicalHistory
              (ReferenceInitializationRun.replayInput x b h i a ha))
            (ReferencePrelaunchPhysicalReplay.blockEnd_le_T p
              (ReferenceInitializationRun.nextBlock b h)) before
            (ReferenceInitializationRun.ordinary x b i)).downBatch = some d.2 := by
  let z := ReferenceInitializationRun.replayInput x b h i a ha
  exact (ReferencePrelaunchFollower.mem_decisions_iff
    (BootstrapPhysicalInput.sourceFollowerIndex p i) x.row a
    (ReferencePrelaunchPhysicalReplay.chronologicalHistory z)
    (ReferencePrelaunchPhysicalReplay.blockEnd_le_T p
      (ReferenceInitializationRun.nextBlock b h))
    (ReferencePrelaunchPhysicalReplay.blockIndices z)
    (ReferenceInitializationRun.ordinary x b i) d).mp hd

/-- The block's decision projection is the one produced by the accepted
`blockReplay`; it carries the ordinary decoder state without resetting partial
batches or DATA logs. -/
theorem ordinary_finishBlock_blockReplay {p : Parameters}
    (x : ReferenceInitializationRun.Input p)
    (b : ReferenceInitializationRun.Boundary p) (h : b.completed < n_boot p)
    (i : ActiveRoundActions.Follower p.m) (a : Activation p)
    (ha : b.activation i = some a) (hf : b.forcedFailure i = false) :
    ReferenceInitializationRun.ordinary x (ReferenceInitializationRun.finishBlock x b h) i =
      ReferencePrelaunchPhysicalReplay.blockReplay
        (ReferenceInitializationRun.replayInput x b h i a ha) :=
  ReferenceInitializationRun.ordinary_finishBlock_of_activated x b h i a ha hf

/-- Ordinary failure after this boundary is the accepted block replay's failure
criterion. `incomingState` is the previously generated ordinary state, and the
block replay continues its DATA log and partial DOWN decoder unchanged. -/
theorem ordinary_finishBlock_suppressed_blockReplay {p : Parameters}
    (x : ReferenceInitializationRun.Input p) (b : ReferenceInitializationRun.Boundary p)
    (h : b.completed < n_boot p) (i : ActiveRoundActions.Follower p.m)
    (a : Activation p) (ha : b.activation i = some a)
    (hf : b.forcedFailure i = false) :
    (ReferenceInitializationRun.ordinary x
      (ReferenceInitializationRun.finishBlock x b h) i).initializationFailure = true ↔
      (ReferenceInitializationRun.ordinary x b i).initializationFailure = true ∨
        ∃ d ∈ ReferencePrelaunchFollower.decisions
          (BootstrapPhysicalInput.sourceFollowerIndex p i) x.row a
          (ReferencePrelaunchPhysicalReplay.chronologicalHistory
            (ReferenceInitializationRun.replayInput x b h i a ha))
          (ReferencePrelaunchPhysicalReplay.blockEnd_le_T p
            (ReferenceInitializationRun.nextBlock b h))
          (ReferencePrelaunchPhysicalReplay.blockIndices
            (ReferenceInitializationRun.replayInput x b h i a ha))
          (ReferenceInitializationRun.ordinary x b i),
          OrdinaryMessageCodec.acceptDown
            (ReferencePrelaunchFollower.codecParams p x.eta) 0 (d.1.val + 1) d.2 := by
  rw [ReferenceInitializationRun.ordinary_finishBlock_of_activated x b h i a ha hf]
  have hh := ReferenceInitializationRun.ordinary_finishBlock_suppressed_failure
    x b h i a ha hf
  rw [← ReferenceInitializationRun.replayInput_history x b h i a ha,
    ordinary_finishBlock_blockReplay x b h i a ha hf] at hh
  exact hh

/-- A follower declared by this block starts a fresh unoccupied replay. If it
was not declared, then absent a launch correction the ordinary failure flag
stays false. -/
theorem ordinary_finishBlock_failure_false_of_unactivated {p : Parameters}
    (x : ReferenceInitializationRun.Input p) (b : ReferenceInitializationRun.Boundary p)
    (h : b.completed < n_boot p) (i : ActiveRoundActions.Follower p.m)
    (ha : b.activation i = none) (hf : b.forcedFailure i = false)
    (hforce : ReferenceInitializationRun.forced x b h i = false) :
    (ReferenceInitializationRun.ordinary x
      (ReferenceInitializationRun.finishBlock x b h) i).initializationFailure = false := by
  have hi : i ∈ ReferenceInitializationRun.uninformed b :=
    (ReferenceInitializationRun.mem_uninformed b i).2 ha
  let i' : {j // j ∈ ReferenceInitializationRun.uninformed b} := ⟨i, hi⟩
  by_cases hp : (ReferenceInitializationRun.candidate x b h i').pending = true
  · rw [ReferenceInitializationRun.ordinary_finishBlock_of_saved x b h i' hp hf]
    rfl
  · have hdecl : ReferenceInitializationRun.declaredActivation x b h i = none := by
      have hpFalse : (ReferenceInitializationRun.candidate x b h i').pending = false :=
        Bool.eq_false_iff.mpr hp
      have hpFalse' : (ReferenceInitializationRun.candidate x b h ⟨i, hi⟩).pending = false := by
        simpa [i'] using hpFalse
      simp [ReferenceInitializationRun.declaredActivation, hi, hpFalse']
    have hcross : ReferenceInitializationRun.crosses x b h = false := by
      cases hc : ReferenceInitializationRun.crosses x b h with
      | false => rfl
      | true =>
          have hforced : ReferenceInitializationRun.forced x b h i = true :=
            (ReferenceInitializationRun.forced_iff x b h i).2 ⟨hc, hdecl⟩
          simp [hforced] at hforce
    have houtForced :
        (ReferenceInitializationRun.finishBlock x b h).forcedFailure i = false := by
      change (b.forcedFailure i || ReferenceInitializationRun.forced x b h i) = false
      simp [hf, hforce]
    have houtActivation :
        (ReferenceInitializationRun.finishBlock x b h).activation i = none := by
      change ReferenceInitializationRun.finalActivation x b h i = none
      simp [ReferenceInitializationRun.finalActivation, hforce, hdecl]
    have houtOrd : ReferenceInitializationRun.ordinary x
        (ReferenceInitializationRun.finishBlock x b h) i =
        ReferencePrelaunchFollower.initial p x.eta := by
      simp [ReferenceInitializationRun.ordinary, houtForced, houtActivation]
    rw [houtOrd]
    rfl

/-- The terminal initialization bit advances one processed block exactly by a
previous failure, a correction after the strict crossing, or a parsed DOWN
decision in the accepted generated block replay. -/
theorem finishBlock_initializationFailure_iff {p : Parameters}
    (x : ReferenceInitializationRun.Input p) (b : ReferenceInitializationRun.Boundary p)
    (h : b.completed < n_boot p) (i : ActiveRoundActions.Follower p.m) :
    ReferenceInitializationRun.initializationFailure x
        (ReferenceInitializationRun.finishBlock x b h) i = true ↔
      ReferenceInitializationRun.initializationFailure x b i = true ∨
        ReferenceInitializationRun.forced x b h i = true ∨
          generatedBlockDown x b h i := by
  constructor
  · intro hout
    by_cases hprev : ReferenceInitializationRun.initializationFailure x b i = true
    · exact Or.inl hprev
    · have hf : b.forcedFailure i = false := by
        cases hh : b.forcedFailure i <;>
          simp [ReferenceInitializationRun.initializationFailure, hh] at hprev ⊢
      by_cases hforce : ReferenceInitializationRun.forced x b h i = true
      · exact Or.inr (Or.inl hforce)
      · have hforceFalse : ReferenceInitializationRun.forced x b h i = false :=
          Bool.eq_false_iff.mpr hforce
        have houtForced :
            (ReferenceInitializationRun.finishBlock x b h).forcedFailure i = false := by
          change (b.forcedFailure i || ReferenceInitializationRun.forced x b h i) = false
          simp [hf, hforceFalse]
        have houtOrd :
            (ReferenceInitializationRun.ordinary x
              (ReferenceInitializationRun.finishBlock x b h) i).initializationFailure = true := by
          unfold ReferenceInitializationRun.initializationFailure at hout
          simp only [houtForced, Bool.false_or] at hout
          exact hout
        cases ha : b.activation i with
        | none =>
            have hfalse := ordinary_finishBlock_failure_false_of_unactivated
              x b h i ha hf hforceFalse
            rw [hfalse] at houtOrd
            cases houtOrd
        | some a =>
            have hprevOrd :
                ¬ (ReferenceInitializationRun.ordinary x b i).initializationFailure = true := by
              intro ho
              apply hprev
              unfold ReferenceInitializationRun.initializationFailure
              simp [hf, ho]
            have hrec := ordinary_finishBlock_suppressed_blockReplay x b h i a ha hf
            rcases hrec.mp houtOrd with hold | hlocal
            · exact False.elim (hprevOrd hold)
            · exact Or.inr (Or.inr ⟨hf, a, ha, hlocal⟩)
  · rintro (hprev | hforce | ⟨hf, a, ha, hlocal⟩)
    · by_cases hforced : b.forcedFailure i = true
      · have hout : (ReferenceInitializationRun.finishBlock x b h).forcedFailure i = true := by
          change (b.forcedFailure i || ReferenceInitializationRun.forced x b h i) = true
          simp [hforced]
        simp [ReferenceInitializationRun.initializationFailure, hout]
      · have hf : b.forcedFailure i = false := Bool.eq_false_iff.mpr hforced
        have hprevOrd :
            (ReferenceInitializationRun.ordinary x b i).initializationFailure = true := by
          unfold ReferenceInitializationRun.initializationFailure at hprev
          simp only [hf, Bool.false_or] at hprev
          exact hprev
        cases ha : b.activation i with
        | none =>
            simp [ReferenceInitializationRun.ordinary, hf, ha,
              ReferencePrelaunchFollower.initial] at hprevOrd
        | some a =>
            by_cases hforce : ReferenceInitializationRun.forced x b h i = true
            · have hout :
                  (ReferenceInitializationRun.finishBlock x b h).forcedFailure i = true := by
                change (b.forcedFailure i || ReferenceInitializationRun.forced x b h i) = true
                simp [hf, hforce]
              simp [ReferenceInitializationRun.initializationFailure, hout]
            · have hrec := ordinary_finishBlock_suppressed_blockReplay x b h i a ha hf
              have hnextOrd := hrec.mpr (Or.inl hprevOrd)
              unfold ReferenceInitializationRun.initializationFailure
              rw [Bool.or_eq_true]
              right
              exact hnextOrd
    · have hout : (ReferenceInitializationRun.finishBlock x b h).forcedFailure i = true := by
        change (b.forcedFailure i || ReferenceInitializationRun.forced x b h i) = true
        simp [hforce]
      simp [ReferenceInitializationRun.initializationFailure, hout]
    · by_cases hforce : ReferenceInitializationRun.forced x b h i = true
      · have hout : (ReferenceInitializationRun.finishBlock x b h).forcedFailure i = true := by
          change (b.forcedFailure i || ReferenceInitializationRun.forced x b h i) = true
          simp [hf, hforce]
        simp [ReferenceInitializationRun.initializationFailure, hout]
      · have hrec := ordinary_finishBlock_suppressed_blockReplay x b h i a ha hf
        have hnextOrd := hrec.mpr (Or.inr hlocal)
        unfold ReferenceInitializationRun.initializationFailure
        rw [Bool.or_eq_true]
        right
        exact hnextOrd

/-- Witnesses already generated during the first `n` run opportunities for a
fixed follower. The cause predicates remain literal block witnesses. -/
def failureCausesBefore {p : Parameters} (x : ReferenceInitializationRun.Input p)
    (n : ℕ) (i : ActiveRoundActions.Follower p.m) : Prop :=
  ∃ s : Fin (n_boot p), s.val < n ∧
    (forcedCorrectionAt x s i ∨ suppressedDownAt x s i)

/-- Splitting the next opportunity exposes exactly its own possible cause. -/
theorem failureCausesBefore_succ_iff {p : Parameters}
    (x : ReferenceInitializationRun.Input p) (n : ℕ) (hn : n < n_boot p)
    (i : ActiveRoundActions.Follower p.m) :
    failureCausesBefore x (n + 1) i ↔
      failureCausesBefore x n i ∨
        (forcedCorrectionAt x ⟨n, hn⟩ i ∨ suppressedDownAt x ⟨n, hn⟩ i) := by
  constructor
  · rintro ⟨s, hs, hc⟩
    by_cases hsn : s.val < n
    · exact Or.inl ⟨s, hsn, hc⟩
    · have hval : s.val = n := by omega
      have heq : s = ⟨n, hn⟩ := Fin.ext hval
      subst s
      exact Or.inr hc
  · rintro (⟨s, hs, hc⟩ | (hc | hc))
    · exact ⟨s, by omega, hc⟩
    · exact ⟨⟨n, hn⟩, Nat.lt_succ_self n, Or.inl hc⟩
    · exact ⟨⟨n, hn⟩, Nat.lt_succ_self n, Or.inr hc⟩

/-- The explicit strict monitor crossing and post-declaration correction at
the current generated boundary are equivalent to its correction witness. -/
theorem forcedCorrectionAt_current_iff {p : Parameters}
    (x : ReferenceInitializationRun.Input p) (n : ℕ) (hn : n < n_boot p)
    (hcross : (ReferenceInitializationRun.run x n).crossing = none)
    (hcompleted : (ReferenceInitializationRun.run x n).completed = n)
    (i : ActiveRoundActions.Follower p.m)
    (hforced : (ReferenceInitializationRun.run x n).forcedFailure i = false) :
    forcedCorrectionAt x ⟨n, hn⟩ i ↔
      ReferenceInitializationRun.forced x (ReferenceInitializationRun.run x n)
        (by rw [hcompleted]; exact hn) i = true := by
  let b := ReferenceInitializationRun.run x n
  let h : b.completed < n_boot p := by rw [hcompleted]; exact hn
  constructor
  · rintro ⟨_, _, _, _, _, _, hforce, _⟩
    exact hforce
  · intro hforce
    have hcauses := (ReferenceInitializationRun.forced_iff x b h i).mp hforce
    have hcrosses := hcauses.1
    have hthreshold : BootstrapLaunchMonitor.monitorValue p
        (ReferenceInitializationRun.updatedCounters x b h) >
          4 * BootstrapStartupCostScale.Q x.C_star x.C_h p := by
      change ReferenceInitializationRun.crosses x b h = true at hcrosses
      change decide (BootstrapLaunchMonitor.monitorValue p
        (ReferenceInitializationRun.updatedCounters x b h) >
          4 * BootstrapStartupCostScale.Q x.C_star x.C_h p) = true at hcrosses
      exact of_decide_eq_true hcrosses
    refine ⟨h, hcross, hcompleted, hforced, hthreshold, hcauses.2, hforce, ?_⟩
    change (b.forcedFailure i || ReferenceInitializationRun.forced x b h i) = true
    have hforced' : b.forcedFailure i = false := by simpa [b] using hforced
    have hforce' : ReferenceInitializationRun.forced x b h i = true := by
      simpa [b, h] using hforce
    simp [hforced', hforce']

/-- Any accepted parser decision in the currently processed block is strictly
before the terminal endpoint, including the final clipped block and a crossing
at elapsed `T`. -/
theorem generatedBlockDown_current_iff {p : Parameters}
    (x : ReferenceInitializationRun.Input p) (n : ℕ) (hn : n < n_boot p)
    (h : (ReferenceInitializationRun.run x n).completed < n_boot p)
    (hcross : (ReferenceInitializationRun.run x n).crossing = none)
    (hcompleted : (ReferenceInitializationRun.run x n).completed = n)
    (i : ActiveRoundActions.Follower p.m) :
    generatedBlockDown x (ReferenceInitializationRun.run x n) h i ↔
      suppressedDownAt x ⟨n, hn⟩ i := by
  constructor
  · rintro ⟨hf, a, ha, d, hd, hdown⟩
    have htime := blockDecision_before_launch x ⟨n, hn⟩
      (ReferenceInitializationRun.run x n) h rfl hcross hcompleted i a ha d hd
    exact ⟨h, hcross, hcompleted, hf, a, ha, d, hd, hdown, htime⟩
  · rintro ⟨h', hcross', hcompleted', hf, a, ha, d, hd, hdown, _⟩
    exact ⟨hf, a, ha, d, hd, hdown⟩

/-- At every finite run prefix, the accepted flag is exactly the union of the
two causes accumulated from its processed generated blocks. -/
theorem run_initializationFailure_iff_causesBefore {p : Parameters}
    (x : ReferenceInitializationRun.Input p) (i : ActiveRoundActions.Follower p.m)
    (n : ℕ) : ∀ _hn : n ≤ n_boot p,
    ReferenceInitializationRun.initializationFailure x
      (ReferenceInitializationRun.run x n) i = true ↔ failureCausesBefore x n i := by
  induction n with
  | zero =>
      intro hn
      simp [failureCausesBefore, ReferenceInitializationRun.run_zero,
        ReferenceInitializationRun.initializationFailure, ReferenceInitializationRun.initial,
        ReferenceInitializationRun.ordinary, ReferencePrelaunchFollower.initial,
        forcedCorrectionAt, suppressedDownAt]
  | succ n ih =>
      intro hn
      have hnlt : n < n_boot p := by omega
      by_cases hc : (ReferenceInitializationRun.run x n).crossing.isSome = true
      · have hstep : ReferenceInitializationRun.run x (n + 1) =
            ReferenceInitializationRun.run x n := by
          rw [ReferenceInitializationRun.run_succ,
            ReferenceInitializationRun.advance_of_crossing x _ hc]
        rw [hstep, ih (by omega), failureCausesBefore_succ_iff x n hnlt i]
        have hforce : ¬ forcedCorrectionAt x ⟨n, hnlt⟩ i := by
          rintro ⟨_, hnone, _, _, _, _, _, _⟩
          simp [hnone] at hc
        have hdown : ¬ suppressedDownAt x ⟨n, hnlt⟩ i := by
          rintro ⟨_, hnone, _, _, _, _, _, _, _, _⟩
          simp [hnone] at hc
        simp [hforce, hdown]
      · have hnone : (ReferenceInitializationRun.run x n).crossing = none := by
          cases hh : (ReferenceInitializationRun.run x n).crossing <;> simp_all
        have hcompleted : (ReferenceInitializationRun.run x n).completed = n := by
          rcases ReferenceInitializationRun.run_progress x n (by omega) with hstop | hdone
          · simp [hnone] at hstop
          · exact hdone
        have hblock : (ReferenceInitializationRun.run x n).completed < n_boot p := by
          rw [hcompleted]
          exact hnlt
        have hforceBefore := ReferenceInitializationRun.run_no_forced_before_launch
          x n hnone i
        have hstep : ReferenceInitializationRun.run x (n + 1) =
            ReferenceInitializationRun.finishBlock x (ReferenceInitializationRun.run x n) hblock := by
          rw [ReferenceInitializationRun.run_succ,
            ReferenceInitializationRun.advance_of_no_crossing x _ hnone hblock]
        rw [hstep,
          finishBlock_initializationFailure_iff x (ReferenceInitializationRun.run x n) hblock i,
          ih (by omega), failureCausesBefore_succ_iff x n hnlt i,
          ← forcedCorrectionAt_current_iff x n hnlt hnone hcompleted i hforceBefore,
          generatedBlockDown_current_iff x n hnlt hblock hnone hcompleted i]

/-- Exact terminal operational characterization, follower by follower. Each
DOWN decision in the right side comes from a generated block replay; each
correction is the first strict crossing after that boundary's pending saves. -/
theorem initializationFailure_iff_operational {p : Parameters}
    (x : ReferenceInitializationRun.Input p) :
    (∃ i : ActiveRoundActions.Follower p.m,
      ReferenceInitializationRun.initializationFailure x
        (ReferenceInitializationRun.output x) i = true) ↔
      operationalInitializationFailure x := by
  constructor
  · rintro ⟨i, hi⟩
    change ReferenceInitializationRun.initializationFailure x
      (ReferenceInitializationRun.run x (n_boot p)) i = true at hi
    have h := (run_initializationFailure_iff_causesBefore x i (n_boot p) le_rfl).mp hi
    rcases h with ⟨s, hs, hc | hc⟩
    · exact Or.inl ⟨i, s, hc⟩
    · exact Or.inr ⟨i, s, hc⟩
  · rintro (⟨i, s, hc⟩ | ⟨i, s, hc⟩)
    · refine ⟨i, ?_⟩
      change ReferenceInitializationRun.initializationFailure x
        (ReferenceInitializationRun.run x (n_boot p)) i = true
      apply (run_initializationFailure_iff_causesBefore x i (n_boot p) le_rfl).2
      exact ⟨s, s.isLt, Or.inl hc⟩
    · refine ⟨i, ?_⟩
      change ReferenceInitializationRun.initializationFailure x
        (ReferenceInitializationRun.run x (n_boot p)) i = true
      apply (run_initializationFailure_iff_causesBefore x i (n_boot p) le_rfl).2
      exact ⟨s, s.isLt, Or.inr hc⟩

/-- The fixed-row witnessed event is measurable by its proved equality with
the finite existential union of generated terminal flags. -/
theorem measurable_fixedRowOperationalInitializationFailure (p : Parameters)
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (row : CompletePublicTable.CompleteRow p) :
    MeasurableSet {e : BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p |
      operationalInitializationFailure
        (ReferenceInitializationIndexMixture.fixedRowInput p ids rewards C_star C_h eta row e)} := by
  have hinput : Measurable (fun e : BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p =>
      (ids, (row, e))) := measurable_const.prodMk (measurable_const.prodMk measurable_id)
  have hfail : ∀ i : ActiveRoundActions.Follower p.m,
      Measurable (fun e : BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p =>
        ReferenceInitializationRun.initializationFailure
          (ReferenceInitializationIndexMixture.fixedRowInput p ids rewards C_star C_h eta row e)
          (ReferenceInitializationRun.output
            (ReferenceInitializationIndexMixture.fixedRowInput p ids rewards C_star C_h eta row e)) i) := by
    intro i
    change Measurable (fun e : BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p =>
      let x := ReferenceInitializationMeasurability.inputOfCoordinates p C_star C_h eta rewards
        (ids, (row, e))
      ReferenceInitializationRun.initializationFailure x (ReferenceInitializationRun.output x) i)
    exact (ReferenceInitializationMeasurability.measurable_output_initializationFailure
      p C_star C_h eta rewards i).comp hinput
  have hset :
      {e : BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p |
        operationalInitializationFailure
          (ReferenceInitializationIndexMixture.fixedRowInput p ids rewards C_star C_h eta row e)} =
      ⋃ i : ActiveRoundActions.Follower p.m,
        {e : BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p |
          ReferenceInitializationRun.initializationFailure
            (ReferenceInitializationIndexMixture.fixedRowInput p ids rewards C_star C_h eta row e)
            (ReferenceInitializationRun.output
              (ReferenceInitializationIndexMixture.fixedRowInput p ids rewards C_star C_h eta row e)) i = true} := by
    ext e
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    exact (initializationFailure_iff_operational
      (ReferenceInitializationIndexMixture.fixedRowInput p ids rewards C_star C_h eta row e)).symm
  rw [hset]
  exact MeasurableSet.iUnion fun i => hfail i (measurableSet_singleton true)

/-- The selected-row witnessed event is measurable by its proved equality with
the finite existential union of selected-row terminal flags. -/
theorem measurable_actualSelectedRowOperationalInitializationFailure (p : Parameters)
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (rows : CompletePublicTable.CompleteRows p) :
    MeasurableSet {e : BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p |
      operationalInitializationFailure
        (ReferenceInitializationIndexMixture.fixedRowInput p ids rewards C_star C_h eta
          (rows (PrivateSourceStreams.coordinatorIndex p e.1.2)) e)} := by
  have hJ : Measurable (fun e : BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p =>
      PrivateSourceStreams.coordinatorIndex p e.1.2) :=
    (PrivateSourceStreams.measurable_coordinatorIndex p).comp
      (measurable_snd.comp measurable_fst)
  have hrow : Measurable (fun e : BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p =>
      rows (PrivateSourceStreams.coordinatorIndex p e.1.2)) :=
    (measurable_from_prod_countable_right
      (f := fun z : Fin (M p) × BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p =>
        rows z.1)
      (fun j => by
        change Measurable (fun _ : BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p => rows j)
        exact measurable_const)).comp (hJ.prodMk measurable_id)
  have hinput : Measurable
      (fun e : BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p =>
        (ids, (rows (PrivateSourceStreams.coordinatorIndex p e.1.2), e))) :=
    measurable_const.prodMk (hrow.prodMk measurable_id)
  have hfail : ∀ i : ActiveRoundActions.Follower p.m,
      Measurable (fun e : BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p =>
        ReferenceInitializationRun.initializationFailure
          (ReferenceInitializationIndexMixture.fixedRowInput p ids rewards C_star C_h eta
            (rows (PrivateSourceStreams.coordinatorIndex p e.1.2)) e)
          (ReferenceInitializationRun.output
            (ReferenceInitializationIndexMixture.fixedRowInput p ids rewards C_star C_h eta
              (rows (PrivateSourceStreams.coordinatorIndex p e.1.2)) e)) i) := by
    intro i
    change Measurable (fun e : BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p =>
      let x := ReferenceInitializationMeasurability.inputOfCoordinates p C_star C_h eta rewards
        (ids, (rows (PrivateSourceStreams.coordinatorIndex p e.1.2), e))
      ReferenceInitializationRun.initializationFailure x (ReferenceInitializationRun.output x) i)
    exact (ReferenceInitializationMeasurability.measurable_output_initializationFailure
      p C_star C_h eta rewards i).comp hinput
  have hset :
      {e : BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p |
        operationalInitializationFailure
          (ReferenceInitializationIndexMixture.fixedRowInput p ids rewards C_star C_h eta
            (rows (PrivateSourceStreams.coordinatorIndex p e.1.2)) e)} =
      ⋃ i : ActiveRoundActions.Follower p.m,
        {e : BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p |
          ReferenceInitializationRun.initializationFailure
            (ReferenceInitializationIndexMixture.fixedRowInput p ids rewards C_star C_h eta
              (rows (PrivateSourceStreams.coordinatorIndex p e.1.2)) e)
            (ReferenceInitializationRun.output
              (ReferenceInitializationIndexMixture.fixedRowInput p ids rewards C_star C_h eta
                (rows (PrivateSourceStreams.coordinatorIndex p e.1.2)) e)) i = true} := by
    ext e
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    exact (initializationFailure_iff_operational
      (ReferenceInitializationIndexMixture.fixedRowInput p ids rewards C_star C_h eta
        (rows (PrivateSourceStreams.coordinatorIndex p e.1.2)) e)).symm
  rw [hset]
  exact MeasurableSet.iUnion fun i => hfail i (measurableSet_singleton true)

/-- If fewer than `n_boot` blocks have been completed, the source elapsed
time is strictly below `T`. This makes the final clipped block distinct from
the terminal sentinel. -/
theorem elapsed_lt_T_of_lt_n_boot (p : Parameters) (r : ℕ) (hr : r < n_boot p) :
    ReferenceInitializationRun.elapsed p r < p.T := by
  have hrNat : r + 1 ≤ n_boot p := Nat.succ_le_of_lt hr
  have hrReal : (r : ℝ) + 1 ≤ (n_boot p : ℝ) := by exact_mod_cast hrNat
  have hceil := BootstrapDimensions.n_boot_real_upper_bound p
  have hquotient : (r : ℝ) < (p.T : ℝ) / (B_boot p : ℝ) := by
    linarith
  have hBpos : 0 < (B_boot p : ℝ) := Nat.cast_pos.mpr (B_boot_pos p)
  have hmulReal : (r : ℝ) * (B_boot p : ℝ) < (p.T : ℝ) :=
    (lt_div_iff₀ hBpos).mp hquotient
  have hmul : r * B_boot p < p.T := by exact_mod_cast hmulReal
  unfold ReferenceInitializationRun.elapsed
  exact (Nat.min_le_right _ _).trans_lt hmul

/-- The generated reference run completes at most one block opportunity per
step, including the frozen tail after crossing. -/
theorem run_completed_le_index {p : Parameters}
    (x : ReferenceInitializationRun.Input p) (r : ℕ) :
    (ReferenceInitializationRun.run x r).completed ≤ r := by
  induction r with
  | zero => simp [ReferenceInitializationRun.run_zero, ReferenceInitializationRun.initial]
  | succ r ih =>
      rw [ReferenceInitializationRun.run_succ]
      by_cases hc : (ReferenceInitializationRun.run x r).crossing.isSome = true
      · rw [ReferenceInitializationRun.advance_of_crossing x _ hc]
        exact ih.trans (Nat.le_succ _)
      · have hnone : (ReferenceInitializationRun.run x r).crossing = none := by
          cases hh : (ReferenceInitializationRun.run x r).crossing <;> simp_all
        by_cases h : (ReferenceInitializationRun.run x r).completed < n_boot p
        · rw [ReferenceInitializationRun.advance_of_no_crossing x _ hnone h]
          simp [ReferenceInitializationRun.finishBlock]
          omega
        · rw [ReferenceInitializationRun.advance_of_exhausted x _ (Nat.le_of_not_gt h)]
          exact ih.trans (Nat.le_succ _)

/-- A stopped run prefix cannot have a crossing in an earlier opportunity.
This supports the first-crossing interpretation of every correction witness. -/
theorem run_prefix_no_crossing_of_no_crossing {p : Parameters}
    (x : ReferenceInitializationRun.Input p) {r q : ℕ} (hqr : q ≤ r)
    (hr : (ReferenceInitializationRun.run x r).crossing = none) :
    (ReferenceInitializationRun.run x q).crossing = none := by
  by_contra hq
  have hsome : (ReferenceInitializationRun.run x q).crossing.isSome = true := by
    cases hh : (ReferenceInitializationRun.run x q).crossing <;> simp_all
  have hstop := ReferenceInitializationRun.run_stops_at_crossing x q (r - q) hsome
  rw [Nat.add_sub_of_le hqr] at hstop
  rw [hstop] at hr
  simp [hr] at hsome

/-- Every earlier monitor boundary is at or below threshold for the crossing
that witnesses a correction. The current block's strict test is therefore the
first actual crossing, evaluated after pending declarations. -/
theorem forcedCorrectionAt_priorMonitorBounds {p : Parameters}
    (x : ReferenceInitializationRun.Input p) (s : Fin (n_boot p))
    (i : ActiveRoundActions.Follower p.m) (hc : forcedCorrectionAt x s i) :
    ∀ q ≤ s.val,
      BootstrapLaunchMonitor.monitorValue p (ReferenceInitializationRun.run x q).counters ≤
        4 * BootstrapStartupCostScale.Q x.C_star x.C_h p := by
  rcases hc with ⟨_, hnone, _, _, _, _, _, _⟩
  intro q hq
  have hqnone := run_prefix_no_crossing_of_no_crossing x hq hnone
  exact ReferenceInitializationRun.run_monitor_le_before_launch x q hqnone

/-- With no output crossing there is no launch-correction witness anywhere in
the finite generated run. Earlier suppressions may still have occurred. -/
theorem no_forcedCorrectionAt_of_no_output_crossing {p : Parameters}
    (x : ReferenceInitializationRun.Input p)
    (hnone : (ReferenceInitializationRun.output x).crossing = none) :
    ∀ i : ActiveRoundActions.Follower p.m, ∀ s : Fin (n_boot p),
      ¬ forcedCorrectionAt x s i := by
  intro i s hc
  rcases hc with ⟨h, hnonePrior, _, _, _, _, hforce, _⟩
  have hcross := (ReferenceInitializationRun.forced_iff x
    (ReferenceInitializationRun.run x s.val) h i).mp hforce |>.1
  have hnext : (ReferenceInitializationRun.run x (s.val + 1)).crossing.isSome = true := by
    rw [ReferenceInitializationRun.run_succ,
      ReferenceInitializationRun.advance_of_no_crossing x _ hnonePrior h]
    change (if ReferenceInitializationRun.crosses x
      (ReferenceInitializationRun.run x s.val) h then
        some (ReferenceInitializationRun.nextBlock (ReferenceInitializationRun.run x s.val) h)
      else none).isSome = true
    simp [hcross]
  have hle : s.val + 1 ≤ n_boot p := Nat.succ_le_of_lt s.isLt
  have hstop := ReferenceInitializationRun.run_stops_at_crossing x (s.val + 1)
    (n_boot p - (s.val + 1)) hnext
  rw [Nat.add_sub_of_le hle] at hstop
  have hout : (ReferenceInitializationRun.output x).crossing.isSome = true := by
    change (ReferenceInitializationRun.run x (n_boot p)).crossing.isSome = true
    rw [hstop]
    exact hnext
  simp [hnone] at hout

/-- At a final-boundary crossing, the current block's strict monitor update
can still force every follower left undeclared after that block's pending
saves. The witness is the last processed source block, even though its endpoint
is the `T+1` sentinel. -/
theorem terminalCrossing_forces_remaining_follower {p : Parameters}
    (x : ReferenceInitializationRun.Input p)
    (hc : (ReferenceInitializationRun.output x).crossing.isSome = true)
    (hT : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output x).completed = p.T)
    (i : ActiveRoundActions.Follower p.m)
    (hdecl : ReferenceInitializationRun.declaredActivation x
      (ReferenceInitializationRun.run x (n_boot p - 1))
      ((run_completed_le_index x (n_boot p - 1)).trans_lt
        (by have hp := BootstrapDimensions.n_boot_pos p; omega)) i = none) :
    forcedCorrectionAt x ⟨n_boot p - 1, by have hp := BootstrapDimensions.n_boot_pos p; omega⟩ i := by
  let q := n_boot p - 1
  have hnpos : 0 < n_boot p := BootstrapDimensions.n_boot_pos p
  have hqSucc : q + 1 = n_boot p := by dsimp [q]; omega
  have hqLt : q < n_boot p := by dsimp [q]; omega
  have hcompletedOut : (ReferenceInitializationRun.output x).completed = n_boot p := by
    by_contra hne
    have hlt : (ReferenceInitializationRun.output x).completed < n_boot p := by
      have hle := (ReferenceInitializationRun.output x).completed_le
      omega
    have htime := elapsed_lt_T_of_lt_n_boot p _ hlt
    rw [hT] at htime
    omega
  have hcompletedOutRun :
      (ReferenceInitializationRun.run x (n_boot p)).completed = n_boot p := by
    simpa [ReferenceInitializationRun.output] using hcompletedOut
  have hprior : (ReferenceInitializationRun.run x q).crossing = none := by
    by_contra hprior
    have hsome : (ReferenceInitializationRun.run x q).crossing.isSome = true := by
      cases hh : (ReferenceInitializationRun.run x q).crossing <;> simp_all
    have hstop := ReferenceInitializationRun.run_stops_at_crossing x q
      (n_boot p - q) hsome
    have hqle : q ≤ n_boot p := by omega
    rw [Nat.add_sub_of_le hqle] at hstop
    have hcompletedQ : (ReferenceInitializationRun.run x q).completed ≤ q :=
      run_completed_le_index x q
    rw [hstop] at hcompletedOutRun
    omega
  have hcompletedQ : (ReferenceInitializationRun.run x q).completed = q := by
    rcases ReferenceInitializationRun.run_progress x q (by omega) with hcross | hdone
    · simp [hprior] at hcross
    · exact hdone
  have hblock : (ReferenceInitializationRun.run x q).completed < n_boot p := by
    rw [hcompletedQ]
    exact hqLt
  have hstep : ReferenceInitializationRun.run x (q + 1) =
      ReferenceInitializationRun.finishBlock x (ReferenceInitializationRun.run x q) hblock := by
    rw [ReferenceInitializationRun.run_succ,
      ReferenceInitializationRun.advance_of_no_crossing x _ hprior hblock]
  have houtput : ReferenceInitializationRun.output x =
      ReferenceInitializationRun.finishBlock x (ReferenceInitializationRun.run x q) hblock := by
    change ReferenceInitializationRun.run x (n_boot p) = _
    rw [← hqSucc, hstep]
  have hterminal :
      (ReferenceInitializationRun.finishBlock x (ReferenceInitializationRun.run x q) hblock).crossing.isSome = true := by
    rw [← houtput]
    exact hc
  have hcrossBlock : ReferenceInitializationRun.crosses x
      (ReferenceInitializationRun.run x q) hblock = true := by
    cases hcBlock : ReferenceInitializationRun.crosses x
        (ReferenceInitializationRun.run x q) hblock with
    | false => simp [ReferenceInitializationRun.finishBlock, hcBlock] at hterminal
    | true => simp
  have hthreshold : BootstrapLaunchMonitor.monitorValue p
      (ReferenceInitializationRun.updatedCounters x (ReferenceInitializationRun.run x q) hblock) >
        4 * BootstrapStartupCostScale.Q x.C_star x.C_h p := by
    change decide _ = true at hcrossBlock
    exact of_decide_eq_true hcrossBlock
  have hforce := (ReferenceInitializationRun.forced_iff x
    (ReferenceInitializationRun.run x q) hblock i).2 ⟨hcrossBlock, hdecl⟩
  have hforcePrior := ReferenceInitializationRun.run_no_forced_before_launch x q hprior i
  refine ⟨hblock, hprior, hcompletedQ, hforcePrior, hthreshold, hdecl, hforce, ?_⟩
  change ((ReferenceInitializationRun.run x q).forcedFailure i ||
    ReferenceInitializationRun.forced x (ReferenceInitializationRun.run x q) hblock i) = true
  simp [hforcePrior, hforce]

/-- At either no crossing or a crossing whose completed elapsed time is `T`,
the source endpoint is `T+1` and the strict comparator prefix charges the
entire physical horizon. -/
theorem output_no_crossing_sentinel_and_full_charge {p : Parameters}
    (x : ReferenceInitializationRun.Input p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (S : Finset (Fin p.K))
    (hnone : (ReferenceInitializationRun.output x).crossing = none) :
    ReferenceInitializationRun.launchRound x = p.T + 1 ∧
      ReferenceInitializationRun.elapsed p
        (ReferenceInitializationRun.output x).completed = p.T ∧
      comparatorChargeAtBoundary p rewards S (ReferenceInitializationRun.output x) =
        ∑ t : Fin p.T, ∑ a ∈ S, ((rewards t a).val : ℝ) / (D p : ℝ) := by
  have hendpoint : launchRoundAtBoundary p (ReferenceInitializationRun.output x) = p.T + 1 :=
    (InitializationRowObservables.launchRoundAtBoundary_sentinel p
      (ReferenceInitializationRun.output x)).2 (Or.inl (by simp [hnone]))
  constructor
  · rw [InitializationRowObservables.launchRound_output_boundary]
    exact hendpoint
  · constructor
    · exact ReferenceInitializationRun.output_elapsed_of_no_crossing x hnone
    · exact InitializationRowObservables.comparatorChargeAtBoundary_eq_full_of_launch_sentinel
        p rewards S (ReferenceInitializationRun.output x) hendpoint

/-- A crossing at elapsed `T` has the same honest `T+1` endpoint and full
comparator charge as no crossing. -/
theorem output_terminal_crossing_sentinel_and_full_charge {p : Parameters}
    (x : ReferenceInitializationRun.Input p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (S : Finset (Fin p.K))
    (hc : (ReferenceInitializationRun.output x).crossing.isSome = true)
    (hT : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output x).completed = p.T) :
    ReferenceInitializationRun.launchRound x = p.T + 1 ∧
      comparatorChargeAtBoundary p rewards S (ReferenceInitializationRun.output x) =
        ∑ t : Fin p.T, ∑ a ∈ S, ((rewards t a).val : ℝ) / (D p : ℝ) := by
  have hendpoint : launchRoundAtBoundary p (ReferenceInitializationRun.output x) = p.T + 1 :=
    (InitializationRowObservables.launchRoundAtBoundary_sentinel p
      (ReferenceInitializationRun.output x)).2 (Or.inr ⟨hc, hT⟩)
  constructor
  · rw [InitializationRowObservables.launchRound_output_boundary]
    exact hendpoint
  · exact InitializationRowObservables.comparatorChargeAtBoundary_eq_full_of_launch_sentinel
      p rewards S (ReferenceInitializationRun.output x) hendpoint

/-- No physical action has one-based time `T+1`; the sentinel is an exclusive
endpoint while the generated physical histories remain indexed by `Fin T`. -/
theorem no_physical_action_at_T_sentinel {p : Parameters} :
    ¬ ∃ t : Fin p.T, t.val + 1 = p.T + 1 := by
  rintro ⟨t, ht⟩
  omega

end Bandits.Support.InitializationFailureProvenance

end
