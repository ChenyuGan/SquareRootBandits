/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.BootstrapPhysicalInput
public import Bandits.Support.BootstrapTruePrefixController
public import Bandits.Support.ReferencePrelaunchPhysicalReplay
public import Bandits.Support.BootstrapLaunchMonitor
public import Bandits.Support.BootstrapBlockCausality
public import Bandits.Support.RecordedQueueRun

/-!
# Chronological, stopped reference initialization

Literal deterministic producer for `07_public_setup.tex:27-40,52-140` and
`appendix_b_communication.tex:97-165`. Only one complete row is an input.
Physical histories, incoming sets, weights, saves, declarations and launch are
computed. The ordinary state is the accepted replay of the generated physical
prefix; the block continuation identity below identifies its carried decoder
and buffer. No postlaunch physical history is supplied or manufactured.

The constants are explicit real inputs; this construction needs no lower bound
on them. The learning rate is positive, as required by the ordinary codec.
There is no probability, product-law, coupling or manuscript closure claim.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ReferenceInitializationRun

open ConstructorDimensions BootstrapDimensions ActiveRoundActions
open CompletePublicTable ReferencePrelaunchFollower
open scoped Classical BigOperators

/-- The entire external input: one selected row and the existing private draw.
No histories, activation times, saves or feedback policies are arguments. -/
structure Input (p : Parameters) where
  ids : IDArray p
  row : CompleteRow p
  rewards : Fin p.T → Fin p.K → Fin (D p + 1)
  coordinates : BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p
  C_star : ℝ
  C_h : ℝ
  eta : LearningRate

/-- Number of physical rounds through `r` complete, clipped calendar blocks. -/
def elapsed (p : Parameters) (r : ℕ) : ℕ := min p.T (r * B_boot p)

theorem elapsed_le_T (p : Parameters) (r : ℕ) : elapsed p r ≤ p.T :=
  Nat.min_le_left _ _

theorem elapsed_mono (p : Parameters) {r q : ℕ} (h : r ≤ q) :
    elapsed p r ≤ elapsed p q :=
  min_le_min_left _ (Nat.mul_le_mul_right _ h)

/-- Finite physical prefix at a block boundary. Proof fields are established
by `initial` and `finishBlock`, not assumed by `run`. -/
structure Boundary (p : Parameters) where
  completed : ℕ
  completed_le : completed ≤ n_boot p
  history : Fin p.m → LocalHistory p (elapsed p completed)
  activation : Follower p.m → Option (Activation p)
  activation_le : ∀ i a, activation i = some a → a.val ≤ elapsed p completed + 1
  numerators : Fin (p.m - 1) → Fin p.K → ℕ
  weight_ge_one : ∀ i a, 1 ≤ BootstrapWeightPotential.weight (b_N p) (numerators i) a
  counters : Fin p.K → ℕ
  crossing : Option (Fin (n_boot p))
  forcedFailure : Follower p.m → Bool

variable {p : Parameters}

/-- All followers initially uninformed; weights one, counters zero, no launch.
The empty physical history has no default arm or observation. -/
def initial (p : Parameters) : Boundary p where
  completed := 0
  completed_le := Nat.zero_le _
  history := fun _ t => Fin.elim0 (Fin.cast (by simp [elapsed]) t)
  activation := fun _ => none
  activation_le := by intro i a h; cases h
  numerators := fun _ => BootstrapWeightPotential.initial p.K (b_N p)
  weight_ge_one := fun _ a => (BootstrapWeightPotential.weight_initial a).ge
  counters := fun _ => 0
  crossing := none
  forcedFailure := fun _ => false

/-- Incoming uninformed set, derived from effective activations. -/
def uninformed (b : Boundary p) : Finset (Follower p.m) :=
  Finset.univ.filter fun i => b.activation i = none

theorem mem_uninformed (b : Boundary p) (i : Follower p.m) :
    i ∈ uninformed b ↔ b.activation i = none := by
  simp only [uninformed, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The next genuine block, only when a block remains. -/
def nextBlock (b : Boundary p) (h : b.completed < n_boot p) : Fin (n_boot p) :=
  ⟨b.completed, h⟩

theorem elapsed_eq_blockStart (b : Boundary p) (h : b.completed < n_boot p) :
    elapsed p b.completed = ReferencePrelaunchPhysicalReplay.blockStart p (nextBlock b h) := by
  exact Nat.min_eq_right (ReferencePrelaunchPhysicalReplay.blockStart_le_T p (nextBlock b h))

theorem elapsed_succ_eq_blockEnd (b : Boundary p) (h : b.completed < n_boot p) :
    elapsed p (b.completed + 1) =
      ReferencePrelaunchPhysicalReplay.blockEnd p (nextBlock b h) := rfl

/-- Accepted scalar-to-block adapter on this run's incoming set and weights. -/
def physical (x : Input p) (b : Boundary p) (h : b.completed < n_boot p) :
    BootstrapPhysicalBlock.Input p (nextBlock b h) :=
  BootstrapPhysicalInput.blockInput p (nextBlock b h) (uninformed b)
    b.numerators b.weight_ge_one x.ids x.row x.rewards x.coordinates

/-- Typed quantized feedback from the existing simultaneous physical run. -/
def ownObservation {s : Fin (n_boot p)} (v : BootstrapPhysicalBlock.Input p s)
    (i : Fin p.m) (t : Fin p.T) : Observation p := by
  refine ⟨⟨BootstrapPhysicalBlock.feedback v (BootstrapPhysicalBlock.run v t.val) t i,
    BootstrapPhysicalBlock.feedback_mem_Icc v _ t i⟩,
    BootstrapPhysicalBlock.observationIndex v (BootstrapPhysicalBlock.run v t.val) t i, ?_⟩
  exact (BootstrapPhysicalBlock.observationIndex_value v _ t i).symm

/-- Actual own action and own feedback; no independent local history input. -/
def ownEntry {s : Fin (n_boot p)} (v : BootstrapPhysicalBlock.Input p s)
    (i : Fin p.m) (t : Fin p.T) : Fin p.K × Observation p :=
  (BootstrapPhysicalBlock.actions v (BootstrapPhysicalBlock.run v t.val) t i,
    ownObservation v i t)

/-- Append precisely this physical block, leaving earlier rounds unchanged. -/
def extendedHistory (x : Input p) (b : Boundary p) (h : b.completed < n_boot p)
    (i : Fin p.m) : LocalHistory p (elapsed p (b.completed + 1)) := fun t =>
  if ht : t.val < elapsed p b.completed then b.history i ⟨t.val, ht⟩
  else ownEntry (physical x b h) i
    ⟨t.val, Nat.lt_of_lt_of_le t.isLt (elapsed_le_T p _)⟩

theorem extendedHistory_prefix (x : Input p) (b : Boundary p)
    (h : b.completed < n_boot p) (i : Fin p.m) (t : Fin (elapsed p b.completed)) :
    extendedHistory x b h i
      ⟨t.val, Nat.lt_of_lt_of_le t.isLt (elapsed_mono p (Nat.le_succ _))⟩ =
      b.history i t := by
  simp only [extendedHistory, dite_eq_left t.isLt]

theorem extendedHistory_block (x : Input p) (b : Boundary p)
    (h : b.completed < n_boot p) (i : Fin p.m)
    (u : Fin (ReferencePrelaunchPhysicalReplay.blockLength p (nextBlock b h))) :
    extendedHistory x b h i (ReferencePrelaunchPhysicalReplay.blockEmbed u) =
      ownEntry (physical x b h) i
        (ReferencePrelaunchPhysicalReplay.blockRound p (nextBlock b h) u) := by
  have hn : ¬ (ReferencePrelaunchPhysicalReplay.blockEmbed u).val <
      elapsed p b.completed := by
    rw [elapsed_eq_blockStart b h]
    simp only [ReferencePrelaunchPhysicalReplay.blockEmbed]
    omega
  simp only [extendedHistory, dite_eq_right hn]
  rfl

/-- Accepted true-candidate controller, fed this block's physical observations. -/
def candidate (x : Input p) (b : Boundary p) (h : b.completed < n_boot p)
    (i : {i // i ∈ uninformed b}) : BootstrapTruePrefixController.Registers :=
  BootstrapTruePrefixController.run (physical x b h) i p.T

/-- Accepted full block weight input, with saves supplied by the true test. -/
def weightInput (x : Input p) (b : Boundary p) (h : b.completed < n_boot p)
    (i : {i // i ∈ uninformed b}) : BootstrapWeightPotential.Block p.K (B_boot p) :=
  BootstrapBlockConstruction.blockInput
    (BootstrapTruePrefixController.observationTrace (physical x b h) i false) (nextBlock b h)

/-- Full held-arm update precedes any declaration or launch correction. -/
def updatedNumerators (x : Input p) (b : Boundary p) (h : b.completed < n_boot p) :
    Fin (p.m - 1) → Fin p.K → ℕ := fun j =>
  let i : Follower p.m := ⟨j.val, j.isLt⟩
  if hi : i ∈ uninformed b then
    BootstrapWeightPotential.next (b_N p) (b.numerators j) (weightInput x b h ⟨i, hi⟩)
  else b.numerators j

theorem updatedNumerators_weight_ge_one (x : Input p) (b : Boundary p)
    (h : b.completed < n_boot p) (j : Fin (p.m - 1)) (a : Fin p.K) :
    1 ≤ BootstrapWeightPotential.weight (b_N p) (updatedNumerators x b h j) a := by
  unfold updatedNumerators
  dsimp only
  split_ifs
  · exact (b.weight_ge_one j a).trans
      (BootstrapWeightPotential.weight_next_mono (K_pos p) (B_boot_pos p) _ _ a)
  · exact b.weight_ge_one j a

theorem weightInput_full_gain (x : Input p) (b : Boundary p)
    (h : b.completed < n_boot p) (i : {i // i ∈ uninformed b}) :
    BootstrapWeightPotential.effectiveGain (weightInput x b h i) =
      BootstrapPhysicalBlock.physicalStayGain (physical x b h) i := by
  exact BootstrapPhysicalBlock.blockInput_effectiveGain_eq_physicalStayGain
    (physical x b h) i (BootstrapTruePrefixController.savedAt (physical x b h) i) false

/-- Effective activation is the next manuscript round after the clipped end. -/
def boundaryActivation (b : Boundary p) : Activation p :=
  ⟨elapsed p (b.completed + 1) + 1, by
    constructor
    · omega
    · exact Nat.add_le_add_right (elapsed_le_T p _) 1⟩

/-- Pending declarations take effect before the launch test. Old activations
are retained; only previously uninformed followers can acquire a declaration. -/
def declaredActivation (x : Input p) (b : Boundary p) (h : b.completed < n_boot p)
    (i : Follower p.m) : Option (Activation p) :=
  if hi : i ∈ uninformed b then
    if (candidate x b h ⟨i, hi⟩).pending then some (boundaryActivation b) else none
  else b.activation i

/-- Coordinator DOWN-positive credit from the same physical feedback. -/
def downArm (x : Input p) (b : Boundary p) (h : b.completed < n_boot p)
    (t : Fin p.T) : Option (Fin p.K) :=
  if BootstrapPhysicalBlock.slot (physical x b h) t = PublicDiscreteDraws.downSlot ∧
      0 < BootstrapPhysicalBlock.feedback (physical x b h)
        (BootstrapPhysicalBlock.run (physical x b h) t.val) t
        (coordinator p.two_le_m) then
    some ((BootstrapPhysicalBlock.tuple (physical x b h) t).val (coordinator p.two_le_m))
  else none

/-- Cumulative counters, including every physical DOWN positive of this block. -/
def updatedCounters (x : Input p) (b : Boundary p) (h : b.completed < n_boot p) :
    Fin p.K → ℕ := fun a => b.counters a +
  ∑ t ∈ calendarBlock p (nextBlock b h), if downArm x b h t = some a then 1 else 0

/-- Actual boundary monitor; the existing source threshold and maximum are used. -/
def crosses (x : Input p) (b : Boundary p) (h : b.completed < n_boot p) : Bool :=
  decide (BootstrapLaunchMonitor.monitorValue p (updatedCounters x b h) >
    4 * BootstrapStartupCostScale.Q x.C_star x.C_h p)

/-- Exact force event, tested after the pending declaration has taken effect. -/
def forced (x : Input p) (b : Boundary p) (h : b.completed < n_boot p)
    (i : Follower p.m) : Bool :=
  crosses x b h && (declaredActivation x b h i).isNone

/-- After declarations, only the remaining uninformed followers are forced. -/
def finalActivation (x : Input p) (b : Boundary p) (h : b.completed < n_boot p)
    (i : Follower p.m) : Option (Activation p) :=
  if forced x b h i then some (boundaryActivation b) else declaredActivation x b h i

theorem declaredActivation_le (x : Input p) (b : Boundary p)
    (h : b.completed < n_boot p) (i : Follower p.m) (a : Activation p)
    (ha : declaredActivation x b h i = some a) : a.val ≤ elapsed p (b.completed + 1) + 1 := by
  unfold declaredActivation at ha
  split_ifs at ha with hi hp
  · have he := Option.some.inj ha
    rw [← he]
    exact le_rfl
  · exact (b.activation_le i a ha).trans
      (Nat.add_le_add_right (elapsed_mono p (Nat.le_succ _)) 1)

/-- Boundary order: generated physical prefix and full weight update, pending
declarations, then the cumulative launch monitor and exceptional forcing. -/
def finishBlock (x : Input p) (b : Boundary p) (h : b.completed < n_boot p) : Boundary p where
  completed := b.completed + 1
  completed_le := Nat.succ_le_of_lt h
  history := extendedHistory x b h
  activation := finalActivation x b h
  activation_le := by
    intro i a ha
    unfold finalActivation at ha
    split_ifs at ha
    · cases ha
      exact le_rfl
    · exact declaredActivation_le x b h i a ha
  numerators := updatedNumerators x b h
  weight_ge_one := updatedNumerators_weight_ge_one x b h
  counters := updatedCounters x b h
  crossing := if crosses x b h then some (nextBlock b h) else none
  forcedFailure := fun i => b.forcedFailure i || forced x b h i

/-- Once launched, or once the finite horizon is exhausted, there is no next
physical block. In particular there are no default postlaunch arms. -/
def advance (x : Input p) (b : Boundary p) : Boundary p :=
  if b.crossing.isSome then b else
    if h : b.completed < n_boot p then finishBlock x b h else b

/-- Finite stopped prefix after at most `r` block opportunities. -/
def run (x : Input p) : ℕ → Boundary p
  | 0 => initial p
  | r + 1 => advance x (run x r)

/-- The finite initialization output, with at most `n_boot` physical blocks. -/
def output (x : Input p) : Boundary p := run x (n_boot p)

/-- Source launch round; `T+1` also covers no crossing and a final-boundary crossing. -/
def launchRound (x : Input p) : ℕ :=
  if (output x).crossing.isSome then elapsed p (output x).completed + 1 else p.T + 1

/-- Ordinary unoccupied replay on the generated prefix. Forced followers use
the accepted fresh handoff; existing followers use the identity handoff. -/
def ordinary (x : Input p) (b : Boundary p) (i : Follower p.m) : State p x.eta :=
  if b.forcedFailure i then forcedAtLaunch p x.eta else
    match b.activation i with
    | none => ReferencePrelaunchFollower.initial p x.eta
    | some a => atLaunch (replay x.eta (BootstrapPhysicalInput.sourceFollowerIndex p i)
        x.row a (b.history (PublicDiscreteDraws.followerPlayer p.two_le_m i))
        (elapsed_le_T p b.completed))

/-- Both exceptional failure causes are observable outputs, never inputs. -/
def initializationFailure (x : Input p) (b : Boundary p) (i : Follower p.m) : Bool :=
  b.forcedFailure i || (ordinary x b i).initializationFailure

/-- Coordinator ordinary UP decoding is disabled throughout this prefix. -/
def coordinatorUpEnabled (_b : Boundary p) : Bool := false

/-- Only the first ordinary learning launch creates these zero registers.
`none` means the coordinator has not launched an ordinary learner. -/
def coordinatorLearner (b : Boundary p) : Option (RecordedQueueRun.RunState p.K) :=
  if b.crossing.isSome then some (RecordedQueueRun.initialState p.K) else none

@[simp] theorem run_zero (x : Input p) : run x 0 = initial p := rfl

theorem run_succ (x : Input p) (r : ℕ) : run x (r + 1) = advance x (run x r) := rfl

theorem initial_equations (i : Follower p.m) (j : Fin (p.m - 1)) (a : Fin p.K) :
    (initial p).activation i = none ∧ (initial p).forcedFailure i = false ∧
    (initial p).numerators j a = BootstrapWeightPotential.scale (b_N p) ∧
    (initial p).counters a = 0 ∧ (initial p).crossing = none :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem advance_of_crossing (x : Input p) (b : Boundary p) (hc : b.crossing.isSome = true) :
    advance x b = b := by
  simp only [advance, hc, ↓reduceIte]

theorem advance_of_no_crossing (x : Input p) (b : Boundary p)
    (hc : b.crossing = none) (h : b.completed < n_boot p) :
    advance x b = finishBlock x b h := by
  simp only [advance, hc, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, h, dite_true]

theorem advance_of_exhausted (x : Input p) (b : Boundary p) (h : n_boot p ≤ b.completed) :
    advance x b = b := by
  simp only [advance]
  split_ifs with hc hb
  · rfl
  · omega
  · rfl

theorem finishBlock_equations (x : Input p) (b : Boundary p) (h : b.completed < n_boot p) :
    (finishBlock x b h).completed = b.completed + 1 ∧
    (finishBlock x b h).history = extendedHistory x b h ∧
    (finishBlock x b h).numerators = updatedNumerators x b h ∧
    (finishBlock x b h).activation = finalActivation x b h ∧
    (finishBlock x b h).counters = updatedCounters x b h ∧
    (finishBlock x b h).crossing =
      (if crosses x b h then some (nextBlock b h) else none) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem run_weight_ge_one (x : Input p) (r : ℕ) (j : Fin (p.m - 1)) (a : Fin p.K) :
    1 ≤ BootstrapWeightPotential.weight (b_N p) ((run x r).numerators j) a :=
  (run x r).weight_ge_one j a

theorem ordinary_registers (x : Input p) (b : Boundary p) (i : Follower p.m) :
    (ordinary x b i).lastDown = none ∧ acceptedStart (ordinary x b i) = 0 ∧
    (ordinary x b i).S = 0 ∧ (ordinary x b i).delta = 0 ∧
    (ordinary x b i).backlog = 0 ∧ (ordinary x b i).status = .unoccupied := by
  unfold ordinary
  split_ifs
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  · split
    · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    · exact replay_registers _ _ _ _ _ _

theorem forced_iff (x : Input p) (b : Boundary p) (h : b.completed < n_boot p)
    (i : Follower p.m) :
    forced x b h i = true ↔ crosses x b h = true ∧ declaredActivation x b h i = none := by
  simp only [forced, Bool.and_eq_true, Option.isNone_iff_eq_none]

theorem saved_not_forced (x : Input p) (b : Boundary p) (h : b.completed < n_boot p)
    (i : {i // i ∈ uninformed b}) (hs : (candidate x b h i).pending = true) :
    forced x b h i.val = false := by
  simp only [forced, declaredActivation, dite_eq_left i.property, hs, ↓reduceIte,
    Option.isNone_some, Bool.and_false]

theorem saved_activation (x : Input p) (b : Boundary p) (h : b.completed < n_boot p)
    (i : {i // i ∈ uninformed b}) (hs : (candidate x b h i).pending = true) :
    (finishBlock x b h).activation i.val = some (boundaryActivation b) := by
  change finalActivation x b h i.val = _
  rw [finalActivation, saved_not_forced x b h i hs]
  simp only [Bool.false_eq_true, ↓reduceIte, declaredActivation, dite_eq_left i.property, hs]

theorem forced_ordinary (x : Input p) (b : Boundary p) (h : b.completed < n_boot p)
    (i : Follower p.m) (hf : forced x b h i = true) :
    ordinary x (finishBlock x b h) i = forcedAtLaunch p x.eta := by
  simp only [ordinary, finishBlock, hf, Bool.or_true, ↓reduceIte]

theorem forced_failure_provenance (x : Input p) (b : Boundary p)
    (h : b.completed < n_boot p) (i : Follower p.m) :
    (finishBlock x b h).forcedFailure i = true ↔
      b.forcedFailure i = true ∨
        (crosses x b h = true ∧ declaredActivation x b h i = none) := by
  change (b.forcedFailure i || forced x b h i) = true ↔ _
  rw [Bool.or_eq_true, forced_iff]

theorem launchRound_bounds (x : Input p) : 1 ≤ launchRound x ∧ launchRound x ≤ p.T + 1 := by
  unfold launchRound
  split_ifs
  · exact ⟨by omega, Nat.add_le_add_right (elapsed_le_T p _) 1⟩
  · omega


/-- Reindexing a finite history changes no accepted replay operation. -/
theorem replay_cast {n m : ℕ} (eta : LearningRate) (i : Fin (p.m - 1))
    (row : CompleteRow p) (a : Activation p) (hist : LocalHistory p n)
    (hn : n ≤ p.T) (hm : m ≤ p.T) (e : n = m) :
    replay eta i row a (fun u : Fin m => hist (Fin.cast e.symm u)) hm =
      replay eta i row a hist hn := by
  subst m
  rfl

/-- The physical replay adapter's earlier prefix is this run's generated
history. Its activation and uninformed-set conditions are derived here. -/
def replayInput (x : Input p) (b : Boundary p) (h : b.completed < n_boot p)
    (i : Follower p.m) (a : Activation p) (ha : b.activation i = some a) :
    ReferencePrelaunchPhysicalReplay.Input p (nextBlock b h) where
  physical := physical x b h
  follower := i
  follower_outside := by
    change i ∉ uninformed b
    rw [mem_uninformed, ha]
    simp only [reduceCtorEq, not_false_eq_true]
  eta := x.eta
  activation := a
  activation_le_blockStart := by
    rw [← elapsed_eq_blockStart b h]
    exact b.activation_le i a ha
  earlierHistory := fun u => b.history (PublicDiscreteDraws.followerPlayer p.two_le_m i)
    (Fin.cast (elapsed_eq_blockStart b h).symm u)

theorem replayInput_incoming (x : Input p) (b : Boundary p) (h : b.completed < n_boot p)
    (i : Follower p.m) (a : Activation p) (ha : b.activation i = some a)
    (hf : b.forcedFailure i = false) :
    ReferencePrelaunchPhysicalReplay.incomingState (replayInput x b h i a ha) =
      ordinary x b i := by
  simp only [ordinary, hf, Bool.false_eq_true, ↓reduceIte, ha, atLaunch]
  exact replay_cast x.eta _ x.row a _ _ _ (elapsed_eq_blockStart b h)

theorem replayInput_history (x : Input p) (b : Boundary p) (h : b.completed < n_boot p)
    (i : Follower p.m) (a : Activation p) (ha : b.activation i = some a) :
    ReferencePrelaunchPhysicalReplay.chronologicalHistory (replayInput x b h i a ha) =
      extendedHistory x b h (PublicDiscreteDraws.followerPlayer p.two_le_m i) := by
  funext t
  unfold ReferencePrelaunchPhysicalReplay.chronologicalHistory extendedHistory
  by_cases ht : t.val < elapsed p b.completed
  · have hs : t.val < ReferencePrelaunchPhysicalReplay.blockStart p (nextBlock b h) := by
      rwa [← elapsed_eq_blockStart b h]
    rw [dite_eq_left ht, dite_eq_left hs]
    rfl
  · have hs : ¬ t.val < ReferencePrelaunchPhysicalReplay.blockStart p (nextBlock b h) := by
      rwa [← elapsed_eq_blockStart b h]
    rw [dite_eq_right ht, dite_eq_right hs]
    rfl


/-- The adapter's prefix and block lists exhaust the clipped calendar. -/
theorem replay_indices {s : Fin (n_boot p)}
    (z : ReferencePrelaunchPhysicalReplay.Input p s) :
    List.ofFn (fun u : Fin (ReferencePrelaunchPhysicalReplay.blockEnd p s) => u) =
      ReferencePrelaunchPhysicalReplay.prefixIndices z ++
        ReferencePrelaunchPhysicalReplay.blockIndices z := by
  rw [List.ofFn_congr (ReferencePrelaunchPhysicalReplay.blockEnd_eq_start_add_length p s),
    List.ofFn_add]
  simp only [ReferencePrelaunchPhysicalReplay.prefixIndices,
    ReferencePrelaunchPhysicalReplay.blockIndices, List.map_ofFn, Function.comp_def]
  rfl

/-- This is ordinary continuation on the physical block, carrying the earlier
buffer and partial DOWN batch. It is not a separately supplied feedback law. -/
theorem replayInput_continued (x : Input p) (b : Boundary p)
    (h : b.completed < n_boot p) (i : Follower p.m) (a : Activation p)
    (ha : b.activation i = some a) :
    replay x.eta (BootstrapPhysicalInput.sourceFollowerIndex p i) x.row a
        (extendedHistory x b h (PublicDiscreteDraws.followerPlayer p.two_le_m i))
        (elapsed_le_T p (b.completed + 1)) =
      ReferencePrelaunchPhysicalReplay.blockReplay (replayInput x b h i a ha) := by
  let z := replayInput x b h i a ha
  rw [← replayInput_history x b h i a ha]
  change replay z.eta (ReferencePrelaunchPhysicalReplay.followerIndex z) z.physical.row
    z.activation (ReferencePrelaunchPhysicalReplay.chronologicalHistory z)
    (ReferencePrelaunchPhysicalReplay.blockEnd_le_T p (nextBlock b h)) = _
  unfold replay
  rw [replay_indices z]
  exact ReferencePrelaunchPhysicalReplay.run_append_block z

theorem declaredActivation_of_activated (x : Input p) (b : Boundary p)
    (h : b.completed < n_boot p) (i : Follower p.m) (a : Activation p)
    (ha : b.activation i = some a) : declaredActivation x b h i = some a := by
  have hn : i ∉ uninformed b := by simp only [mem_uninformed, ha, reduceCtorEq, not_false_eq_true]
  simp only [declaredActivation, dite_eq_right hn, ha]

theorem activated_not_forced (x : Input p) (b : Boundary p)
    (h : b.completed < n_boot p) (i : Follower p.m) (a : Activation p)
    (ha : b.activation i = some a) : forced x b h i = false := by
  simp only [forced, declaredActivation_of_activated x b h i a ha,
    Option.isNone_some, Bool.and_false]

/-- Existing activation times survive the boundary, including launch. -/
theorem activated_activation (x : Input p) (b : Boundary p)
    (h : b.completed < n_boot p) (i : Follower p.m) (a : Activation p)
    (ha : b.activation i = some a) : (finishBlock x b h).activation i = some a := by
  change finalActivation x b h i = _
  simp only [finalActivation, activated_not_forced x b h i a ha,
    Bool.false_eq_true, ↓reduceIte, declaredActivation_of_activated x b h i a ha]

/-- Exact ordinary block successor, on every already activated follower. -/
theorem ordinary_finishBlock_of_activated (x : Input p) (b : Boundary p)
    (h : b.completed < n_boot p) (i : Follower p.m) (a : Activation p)
    (ha : b.activation i = some a) (hf : b.forcedFailure i = false) :
    ordinary x (finishBlock x b h) i =
      ReferencePrelaunchPhysicalReplay.blockReplay (replayInput x b h i a ha) := by
  have hff : (finishBlock x b h).forcedFailure i = false := by
    change (b.forcedFailure i || forced x b h i) = false
    rw [hf, activated_not_forced x b h i a ha]
    rfl
  simp only [ordinary, hff, Bool.false_eq_true, ↓reduceIte,
    activated_activation x b h i a ha, atLaunch]
  exact replayInput_continued x b h i a ha

/-- New declarations initialize only their own ordinary state at `end+1`;
the just-finished physical prefix is strictly before that activation. -/
theorem ordinary_finishBlock_of_saved (x : Input p) (b : Boundary p)
    (h : b.completed < n_boot p) (i : {i // i ∈ uninformed b})
    (hs : (candidate x b h i).pending = true) (hf : b.forcedFailure i.val = false) :
    ordinary x (finishBlock x b h) i.val = ReferencePrelaunchFollower.initial p x.eta := by
  have hff : (finishBlock x b h).forcedFailure i.val = false := by
    change (b.forcedFailure i.val || forced x b h i.val) = false
    rw [hf, saved_not_forced x b h i hs]
    rfl
  simp only [ordinary, hff, Bool.false_eq_true, ↓reduceIte,
    saved_activation x b h i hs, atLaunch]
  apply replay_before_activation
  exact Nat.lt_succ_self _

/-- At launch, all ordinary registers of existing followers are handed over
by identity, including full logs and incomplete decoder batches. -/
theorem launch_handoff_preserves (x : Input p) (b : Boundary p) (i : Follower p.m) :
    (atLaunch (ordinary x b i)).buffer = (ordinary x b i).buffer ∧
      (atLaunch (ordinary x b i)).downBatch = (ordinary x b i).downBatch :=
  atLaunch_preserves _

/-- Actual physical DATA logs append to the existing buffer across blocks. -/
theorem ordinary_finishBlock_buffer (x : Input p) (b : Boundary p)
    (h : b.completed < n_boot p) (i : Follower p.m) (a : Activation p)
    (ha : b.activation i = some a) (hf : b.forcedFailure i = false) :
    (ordinary x (finishBlock x b h) i).buffer = (ordinary x b i).buffer ++
      (ReferencePrelaunchPhysicalReplay.blockIndices (replayInput x b h i a ha)).flatMap
        (fun u => logAt (BootstrapPhysicalInput.sourceFollowerIndex p i) x.row a
          (calendar (elapsed_le_T p (b.completed + 1)) u)
          (extendedHistory x b h (PublicDiscreteDraws.followerPlayer p.two_le_m i) u)) := by
  rw [ordinary_finishBlock_of_activated x b h i a ha hf,
    ReferencePrelaunchPhysicalReplay.blockReplay_buffer,
    replayInput_incoming x b h i a ha hf, replayInput_history]
  rfl

/-- Suppression is exactly the accepted ordinary DOWN test on decisions from
this physical block, before any assignment-dependent effects. -/
theorem ordinary_finishBlock_suppressed_failure (x : Input p) (b : Boundary p)
    (h : b.completed < n_boot p) (i : Follower p.m) (a : Activation p)
    (ha : b.activation i = some a) (hf : b.forcedFailure i = false) :
    (ordinary x (finishBlock x b h) i).initializationFailure = true ↔
      (ordinary x b i).initializationFailure = true ∨
        ∃ d ∈ decisions (BootstrapPhysicalInput.sourceFollowerIndex p i) x.row a
          (extendedHistory x b h (PublicDiscreteDraws.followerPlayer p.two_le_m i))
          (elapsed_le_T p (b.completed + 1))
          (ReferencePrelaunchPhysicalReplay.blockIndices (replayInput x b h i a ha))
          (ordinary x b i),
          OrdinaryMessageCodec.acceptDown (codecParams p x.eta) 0 (d.1.val + 1) d.2 := by
  rw [ordinary_finishBlock_of_activated x b h i a ha hf]
  have hh := ReferencePrelaunchPhysicalReplay.blockReplay_failure_iff
    (replayInput x b h i a ha)
  rw [replayInput_incoming x b h i a ha hf, replayInput_history] at hh
  exact hh


/-- Before launch no exceptional forcing has occurred. This is proved from
the recursion, so continuation lemmas need no user-supplied success premise. -/
theorem run_no_forced_before_launch (x : Input p) (r : ℕ)
    (hc : (run x r).crossing = none) (i : Follower p.m) :
    (run x r).forcedFailure i = false := by
  induction r with
  | zero => rfl
  | succ r ih =>
      by_cases hp : (run x r).crossing.isSome = true
      · rw [run_succ, advance_of_crossing x _ hp] at hc ⊢
        exact ih hc
      · have hn : (run x r).crossing = none := by
          cases he : (run x r).crossing <;> simp_all only [Option.isSome_some, not_true_eq_false]
        by_cases h : (run x r).completed < n_boot p
        · rw [run_succ, advance_of_no_crossing x _ hn h] at hc ⊢
          have hcross : crosses x (run x r) h = false := by
            change (if crosses x (run x r) h then some (nextBlock (run x r) h) else none) = none at hc
            cases he : crosses x (run x r) h <;> simp_all only [↓reduceIte, reduceCtorEq]
          change ((run x r).forcedFailure i || forced x (run x r) h i) = false
          rw [ih hn]
          simp only [forced, hcross, Bool.false_and, Bool.false_or]
        · rw [run_succ, advance_of_exhausted x _ (Nat.le_of_not_gt h)]
          exact ih hn

/-- Each opportunity processes the next block unless launch has already
stopped initialization. There are enough opportunities to cover the horizon. -/
theorem run_progress (x : Input p) (r : ℕ) (hr : r ≤ n_boot p) :
    (run x r).crossing.isSome = true ∨ (run x r).completed = r := by
  induction r with
  | zero => exact Or.inr rfl
  | succ r ih =>
      by_cases hc : (run x r).crossing.isSome = true
      · left
        rw [run_succ, advance_of_crossing x _ hc]
        exact hc
      · have he := (ih (by omega)).resolve_left hc
        have hn : (run x r).crossing = none := by
          cases hh : (run x r).crossing <;> simp_all only [Option.isSome_some, not_true_eq_false]
        have h : (run x r).completed < n_boot p := by omega
        right
        rw [run_succ, advance_of_no_crossing x _ hn h]
        change (run x r).completed + 1 = r + 1
        rw [he]

/-- Output is stopped by a genuine crossing or by exhaustion of all blocks. -/
theorem output_stopped (x : Input p) : advance x (output x) = output x := by
  rcases run_progress x (n_boot p) le_rfl with hc | he
  · exact advance_of_crossing x _ hc
  · exact advance_of_exhausted x _ he.ge

/-- No new physical actions are produced after the finite initialization. -/
theorem run_after_output (x : Input p) (k : ℕ) : run x (n_boot p + k) = output x := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Nat.add_succ, run_succ, ih, output_stopped]

/-- At a crossing, declarations have already taken effect and every remaining
uninformed follower is forced into the selected-row unoccupied state. -/
theorem finishBlock_all_activated (x : Input p) (b : Boundary p)
    (h : b.completed < n_boot p) (hc : crosses x b h = true) (i : Follower p.m) :
    ((finishBlock x b h).activation i).isSome = true := by
  change (finalActivation x b h i).isSome = true
  unfold finalActivation forced
  rw [hc, Bool.true_and]
  cases he : declaredActivation x b h i <;> rfl

/-- This invariant includes the shortened final block and all stopped tails. -/
theorem run_all_activated_at_crossing (x : Input p) (r : ℕ)
    (hc : (run x r).crossing.isSome = true) (i : Follower p.m) :
    ((run x r).activation i).isSome = true := by
  induction r with
  | zero => change false = true at hc; cases hc
  | succ r ih =>
      by_cases hp : (run x r).crossing.isSome = true
      · rw [run_succ, advance_of_crossing x _ hp]
        exact ih hp
      · have hn : (run x r).crossing = none := by
          cases he : (run x r).crossing <;> simp_all only [Option.isSome_some, not_true_eq_false]
        by_cases h : (run x r).completed < n_boot p
        · rw [run_succ, advance_of_no_crossing x _ hn h] at hc ⊢
          have hcross : crosses x (run x r) h = true := by
            change (if crosses x (run x r) h then some (nextBlock (run x r) h) else none).isSome = true at hc
            cases he : crosses x (run x r) h <;> simp_all only [↓reduceIte, Option.isSome_none, Bool.false_eq_true]
          exact finishBlock_all_activated x _ h hcross i
        · rw [run_succ, advance_of_exhausted x _ (Nat.le_of_not_gt h)] at hc ⊢
          exact ih hc

/-- The counters and launch threshold are taken after the current physical
block, including the update which first crosses the threshold. -/
theorem crossing_boundary_equation (x : Input p) (b : Boundary p)
    (h : b.completed < n_boot p) :
    (finishBlock x b h).crossing = some (nextBlock b h) ↔
      BootstrapLaunchMonitor.monitorValue p (updatedCounters x b h) >
        4 * BootstrapStartupCostScale.Q x.C_star x.C_h p := by
  change (if crosses x b h then some (nextBlock b h) else none) = _ ↔ _
  simp only [crosses, decide_eq_true_eq, ite_eq_left_iff, reduceCtorEq, imp_false,
    not_not]

/-- Literal boundary credit, using the accepted monitor's one-round operation. -/
theorem updatedCounters_eq_credit_fold (x : Input p) (b : Boundary p)
    (h : b.completed < n_boot p) (a : Fin p.K) :
    updatedCounters x b h a = b.counters a +
      ∑ t ∈ calendarBlock p (nextBlock b h),
        (BootstrapLaunchMonitor.creditCounter (fun _ => 0) (downArm x b h t)) a := by
  simp only [updatedCounters, BootstrapLaunchMonitor.creditCounter, zero_add]

/-- The complete true test is a function of the selected row only. -/
theorem selected_row_dependence (x y : Input p) (hids : x.ids = y.ids)
    (hrow : x.row = y.row) (hr : x.rewards = y.rewards)
    (hprivate : x.coordinates = y.coordinates) (hstar : x.C_star = y.C_star)
    (hh : x.C_h = y.C_h) (heta : x.eta = y.eta) : output x = output y := by
  have he : x = y := by
    cases x
    cases y
    dsimp only at hids hrow hr hprivate hstar hh heta
    cases hids
    cases hrow
    cases hr
    cases hprivate
    cases hstar
    cases hh
    cases heta
    rfl
  rw [he]


/-- The run starts no ordinary coordinator learner before launch. -/
theorem coordinatorLearner_initial : coordinatorLearner (initial p) = none := rfl

theorem coordinatorLearner_at_crossing (b : Boundary p) (hc : b.crossing.isSome = true) :
    coordinatorLearner b = some (RecordedQueueRun.initialState p.K) := by
  simp only [coordinatorLearner, hc, ↓reduceIte]

/-- Direct use of the accepted zero-score, zero-queue learner carrier. -/
theorem coordinatorLearner_zero (a : Fin p.K) :
    (RecordedQueueRun.initialState p.K).registers a = (0, 0) ∧
      (RecordedQueueRun.initialState p.K).records a = [] ∧
      (RecordedQueueRun.initialState p.K).overflow = false := ⟨rfl, rfl, rfl⟩

/-- Instantiation on the actual recursion eliminates the conditional helper's
no-prior-force argument: the producer proves it from no coordinator launch. -/
theorem run_ordinary_successor (x : Input p) (r : ℕ)
    (hc : (run x r).crossing = none) (h : (run x r).completed < n_boot p)
    (i : Follower p.m) (a : Activation p) (ha : (run x r).activation i = some a) :
    ordinary x (run x (r + 1)) i =
      ReferencePrelaunchPhysicalReplay.blockReplay (replayInput x (run x r) h i a ha) := by
  rw [run_succ, advance_of_no_crossing x _ hc h]
  exact ordinary_finishBlock_of_activated x _ h i a ha (run_no_forced_before_launch x r hc i)

/-- The full ordinary decoder collection, including its partial pending batch,
is carried through the physical block; launch introduces no decoder reset. -/
theorem ordinary_finishBlock_batch (x : Input p) (b : Boundary p)
    (h : b.completed < n_boot p) (i : Follower p.m) (a : Activation p)
    (ha : b.activation i = some a) (hf : b.forcedFailure i = false) :
    (ordinary x (finishBlock x b h) i).downBatch.pending.length < AffineBatchDecoder.quota p ∧
    (∀ batch ∈ (ordinary x (finishBlock x b h) i).downBatch.completed,
      batch.length = AffineBatchDecoder.quota p) ∧
    AffineBatchDecoder.collected (ordinary x (finishBlock x b h) i).downBatch =
      AffineBatchDecoder.collected (ordinary x b i).downBatch ++
        (ReferencePrelaunchPhysicalReplay.blockIndices (replayInput x b h i a ha)).flatMap
          (fun u => AffineBatchDecoder.positiveAt p
            (traceAt (BootstrapPhysicalInput.sourceFollowerIndex p i) x.row a
              (calendar (elapsed_le_T p (b.completed + 1)) u)
              (extendedHistory x b h (PublicDiscreteDraws.followerPlayer p.two_le_m i) u))
            (calendar (elapsed_le_T p (b.completed + 1)) u)) := by
  rw [ordinary_finishBlock_of_activated x b h i a ha hf]
  have hh := ReferencePrelaunchPhysicalReplay.blockReplay_batch_spec (replayInput x b h i a ha)
  rw [replayInput_incoming x b h i a ha hf, replayInput_history] at hh
  exact hh

/-- Exact true-row pending declaration criterion on this physical block. -/
theorem candidate_pending_iff (x : Input p) (b : Boundary p)
    (h : b.completed < n_boot p) (i : {i // i ∈ uninformed b}) :
    (candidate x b h i).pending = true ↔
      BootstrapTruePrefixController.hasPassingPrefix (physical x b h) i p.T :=
  BootstrapTruePrefixController.pending_iff_passingPrefix _ _ _ le_rfl

/-- Save freezes candidate testing only. Every positive stay after a save
still belongs to the full physical gain, regardless of its slot. -/
theorem full_gain_independent_of_save (x : Input p) (b : Boundary p)
    (h : b.completed < n_boot p) (i : {i // i ∈ uninformed b})
    (save₁ save₂ : Fin p.T → Bool) (launch₁ launch₂ : Bool) :
    BootstrapBlockConstruction.effectiveCalendarBlockGain
        (BootstrapPhysicalBlock.observationTrace (physical x b h) i save₁ launch₁)
        (nextBlock b h) =
      BootstrapBlockConstruction.effectiveCalendarBlockGain
        (BootstrapPhysicalBlock.observationTrace (physical x b h) i save₂ launch₂)
        (nextBlock b h) :=
  BootstrapTruePrefixController.effectiveGain_independent_of_candidate_output _ _ _ _ _ _

theorem boundaryActivation_timing (b : Boundary p) (h : b.completed < n_boot p) :
    (boundaryActivation b).val =
      min p.T (((nextBlock b h).val + 1) * B_boot p) + 1 := rfl

/-- Full weights are updated even for the declaration which takes effect at
this boundary. No pending/save input can replace the physical gain. -/
theorem updatedNumerators_incoming (x : Input p) (b : Boundary p)
    (h : b.completed < n_boot p) (i : {i // i ∈ uninformed b}) :
    updatedNumerators x b h (BootstrapPhysicalInput.sourceFollowerIndex p i.val) =
      BootstrapWeightPotential.next (b_N p)
        (b.numerators (BootstrapPhysicalInput.sourceFollowerIndex p i.val))
        (weightInput x b h i) := by
  unfold updatedNumerators
  dsimp only
  split_ifs with hi
  · rfl
  · exact False.elim (hi i.property)

theorem elapsed_all_blocks (p : Parameters) : elapsed p (n_boot p) = p.T := by
  have hreal : (p.T : ℝ) ≤ (n_boot p : ℝ) * (B_boot p : ℝ) :=
    (div_le_iff₀ (Nat.cast_pos.mpr (B_boot_pos p))).mp (n_boot_real_lower_bound p)
  have hnat : p.T ≤ n_boot p * B_boot p := by exact_mod_cast hreal
  exact Nat.min_eq_left hnat

/-- Without a crossing the entire physical horizon has been processed. -/
theorem output_elapsed_of_no_crossing (x : Input p) (hc : (output x).crossing = none) :
    elapsed p (output x).completed = p.T := by
  have hp := run_progress x (n_boot p) le_rfl
  have hn : ¬ (output x).crossing.isSome = true := by simp only [hc, Option.isSome_none, Bool.false_eq_true, not_false_eq_true]
  have he : (output x).completed = n_boot p := hp.resolve_left hn
  rw [he, elapsed_all_blocks]

/-- There is no physical horizon action at a launch of `T+1`: the stored
history remains a finite prefix whose offsets are strictly below `T`. -/
theorem output_history_round_lt_T (x : Input p)
    (t : Fin (elapsed p (output x).completed)) : t.val < p.T :=
  Nat.lt_of_lt_of_le t.isLt (elapsed_le_T p _)

/-- Crossing freezes initialization at exactly this boundary state. -/
theorem run_stops_at_crossing (x : Input p) (r k : ℕ)
    (hc : (run x r).crossing.isSome = true) : run x (r + k) = run x r := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Nat.add_succ, run_succ, ih, advance_of_crossing x _ hc]

/-- Every earlier genuine boundary is below threshold if launch has not yet
occurred. In particular the first overflowing block is fully included. -/
theorem run_monitor_le_before_launch (x : Input p) (r : ℕ)
    (hc : (run x r).crossing = none) :
    BootstrapLaunchMonitor.monitorValue p (run x r).counters ≤
      4 * BootstrapStartupCostScale.Q x.C_star x.C_h p := by
  induction r with
  | zero =>
      change BootstrapLaunchMonitor.monitorValue p (fun _ => 0) ≤ _
      rw [BootstrapLaunchMonitor.monitorValue_zero]
      exact Nat.zero_le _
  | succ r ih =>
      by_cases hp : (run x r).crossing.isSome = true
      · rw [run_succ, advance_of_crossing x _ hp] at hc ⊢
        exact ih hc
      · have hn : (run x r).crossing = none := by
          cases he : (run x r).crossing <;> simp_all only [Option.isSome_some, not_true_eq_false]
        by_cases h : (run x r).completed < n_boot p
        · rw [run_succ, advance_of_no_crossing x _ hn h] at hc ⊢
          change BootstrapLaunchMonitor.monitorValue p (updatedCounters x (run x r) h) ≤ _
          have hfalse : crosses x (run x r) h = false := by
            change (if crosses x (run x r) h then some (nextBlock (run x r) h) else none) = none at hc
            cases he : crosses x (run x r) h <;> simp_all only [↓reduceIte, reduceCtorEq]
          exact Nat.le_of_not_lt (of_decide_eq_false hfalse)
        · rw [run_succ, advance_of_exhausted x _ (Nat.le_of_not_gt h)]
          exact ih hn

/-- Finite first-boundary crossing characterization, using the accepted
monitor value, without completing the stopped physical history by defaults. -/
theorem first_boundary_crossing (x : Input p) (r : ℕ)
    (hc : (run x r).crossing = none) (h : (run x r).completed < n_boot p)
    (hcross : crosses x (run x r) h = true) :
    (run x (r + 1)).crossing = some (nextBlock (run x r) h) ∧
      BootstrapLaunchMonitor.monitorValue p (run x (r + 1)).counters >
        4 * BootstrapStartupCostScale.Q x.C_star x.C_h p ∧
      ∀ q ≤ r, BootstrapLaunchMonitor.monitorValue p (run x q).counters ≤
        4 * BootstrapStartupCostScale.Q x.C_star x.C_h p := by
  have hs : run x (r + 1) = finishBlock x (run x r) h := by
    rw [run_succ, advance_of_no_crossing x _ hc h]
  refine ⟨?_, ?_, ?_⟩
  · rw [hs]
    change (if crosses x (run x r) h then some _ else none) = _
    simp only [hcross, ↓reduceIte]
  · rw [hs]
    exact of_decide_eq_true hcross
  · intro q hq
    apply run_monitor_le_before_launch
    by_contra hn
    have hsome : (run x q).crossing.isSome = true := by
      cases he : (run x q).crossing <;> simp_all only [Option.isSome_some, not_true_eq_false]
    have hf := run_stops_at_crossing x q (r - q) hsome
    rw [Nat.add_sub_of_le hq] at hf
    rw [hf] at hc
    rw [hc] at hsome
    cases hsome


/-- Generated finite-history DOWN credit, using exactly the accepted monitor
slot and labelled tuple-arm projections. It has no post-prefix branch. -/
def generatedDownArm (x : Input p) (n : ℕ) (hn : n ≤ p.T)
    (hist : LocalHistory p n) (u : Fin n) : Option (Fin p.K) :=
  if BootstrapLaunchMonitor.trueCoordinatorSlot p x.row (calendar hn u) =
        PublicDiscreteDraws.downSlot ∧ 0 < (hist u).2.val.val then
    some (BootstrapLaunchMonitor.trueCoordinatorArm p x.row (calendar hn u)) else none

/-- The counter update reads the coordinator observations which are actually
appended to the history; no history-physicality predicate is an input. -/
theorem downArm_eq_generatedDownArm (x : Input p) (b : Boundary p)
    (h : b.completed < n_boot p)
    (u : Fin (ReferencePrelaunchPhysicalReplay.blockLength p (nextBlock b h))) :
    downArm x b h (ReferencePrelaunchPhysicalReplay.blockRound p (nextBlock b h) u) =
      generatedDownArm x (elapsed p (b.completed + 1)) (elapsed_le_T p _)
        (extendedHistory x b h (coordinator p.two_le_m))
        (ReferencePrelaunchPhysicalReplay.blockEmbed u) := by
  unfold generatedDownArm
  rw [extendedHistory_block]
  rfl

/-- Exact failure provenance in the generated physical prefix. The first
alternative is launch forcing; the second is a parsed ordinary DOWN decision
which passes the literal accepted-start-zero test and is suppressed. -/
theorem initializationFailure_provenance (x : Input p) (b : Boundary p)
    (i : Follower p.m) : initializationFailure x b i = true ↔
    b.forcedFailure i = true ∨
      ∃ a, b.activation i = some a ∧
        ∃ d ∈ decisions (BootstrapPhysicalInput.sourceFollowerIndex p i) x.row a
          (b.history (PublicDiscreteDraws.followerPlayer p.two_le_m i))
          (elapsed_le_T p b.completed)
          (List.ofFn (fun u : Fin (elapsed p b.completed) => u))
          (ReferencePrelaunchFollower.initial p x.eta),
          OrdinaryMessageCodec.acceptDown (codecParams p x.eta) 0 (d.1.val + 1) d.2 := by
  by_cases hf : b.forcedFailure i = true
  · simp only [initializationFailure, hf, Bool.true_or, true_or]
  · have hfalse : b.forcedFailure i = false := Bool.eq_false_iff.mpr hf
    simp only [initializationFailure, hfalse, Bool.false_or, Bool.false_eq_true, false_or]
    cases ha : b.activation i with
    | none =>
        simp only [ordinary, hfalse, Bool.false_eq_true, ↓reduceIte, ha,
          ReferencePrelaunchFollower.initial, reduceCtorEq, false_and, exists_false]
    | some a =>
        simp only [ordinary, hfalse, Bool.false_eq_true, ↓reduceIte, ha, atLaunch,
          Option.some.injEq, replay_failure_iff]
        constructor
        · intro hd
          exact ⟨a, rfl, hd⟩
        · rintro ⟨a', haa, hd⟩
          cases haa
          exact hd

/-- At actual launch all followers are selected-row unoccupied with zero
ordinary reply registers. This is a deterministic initialization invariant. -/
theorem output_launch_state (x : Input p) (hc : (output x).crossing.isSome = true)
    (i : Follower p.m) :
    ((output x).activation i).isSome = true ∧
      (ordinary x (output x) i).lastDown = none ∧
      acceptedStart (ordinary x (output x) i) = 0 ∧
      (ordinary x (output x) i).S = 0 ∧
      (ordinary x (output x) i).delta = 0 ∧
      (ordinary x (output x) i).backlog = 0 ∧
      (ordinary x (output x) i).status = .unoccupied :=
  ⟨run_all_activated_at_crossing x (n_boot p) hc i, ordinary_registers x _ i⟩


/-- Current block choices are the accepted private-stream sampler on the
incoming weights. Only this follower's block triple is read by its entry. -/
theorem physical_own_block_draw (x : Input p) (b : Boundary p)
    (h : b.completed < n_boot p) (i : {i // i ∈ uninformed b}) :
    ((physical x b h).active i, (physical x b h).held i, (physical x b h).privateId i) =
      PrivateSourceStreams.blockDrawProfileMap p b.numerators b.weight_ge_one
        (x.coordinates.1.1 (nextBlock b h))
        (BootstrapPhysicalInput.sourceFollowerIndex p i.val) := rfl

/-- Each player uses its own existing round scalar for the full-arm branch. -/
theorem physical_own_uniform (x : Input p) (b : Boundary p)
    (h : b.completed < n_boot p) (i : Fin p.m) (t : Fin p.T) :
    (physical x b h).uniform i t = BootstrapPrivateRoundStreams.fullArmScalarDraw p
      (x.coordinates.2.1 (i, t)) := rfl

/-- The physical block's DISCOVER state resets at its genuine block start;
the cumulative launch counters are carried separately by `updatedCounters`. -/
theorem physical_block_start (x : Input p) (b : Boundary p)
    (h : b.completed < n_boot p) :
    BootstrapPhysicalBlock.run (physical x b h) (elapsed p b.completed) =
      BootstrapPhysicalBlock.initialState p := by
  rw [elapsed_eq_blockStart b h]
  exact BootstrapPhysicalBlock.run_at_block_start _

/-- Repackage the literal physical input for the accepted block-causality
API. No new draw carrier or action recursion is introduced. -/
def localCoordinates (x : Input p) (b : Boundary p) (h : b.completed < n_boot p) :
    BootstrapBlockCausality.LocalCoordinates p (uninformed b)
      (physical x b h).held (physical x b h).target :=
  (x.row, ((physical x b h).uniform,
    ((physical x b h).coordinatorAvoid, (physical x b h).followerAvoid)))

/-- Current pre-choice state uses strict past coordinates within the block.
The alternative coordinate tuple is only a comparison argument to the accepted
causality theorem, never an input of the initialization producer. -/
theorem physical_prechoice_eq_of_past (x : Input p) (b : Boundary p)
    (h : b.completed < n_boot p) (t : Fin p.T)
    (w : BootstrapBlockCausality.LocalCoordinates p (uninformed b)
      (physical x b h).held (physical x b h).target)
    (hpast : ∀ u : Fin p.T, u.val < t.val →
      BootstrapBlockCausality.roundCoordinatesEq (uninformed b)
        (physical x b h).held (physical x b h).target (localCoordinates x b h) w u) :
    BootstrapPhysicalBlock.run (physical x b h) t.val =
      BootstrapBlockCausality.blockRun (s := nextBlock b h) (uninformed b)
        (physical x b h).active (physical x b h).held (physical x b h).privateId
        x.ids (physical x b h).target x.rewards w t.val :=
  BootstrapBlockCausality.run_at_current_eq_of_strictPast
    (s := nextBlock b h) (uninformed b) (physical x b h).active (physical x b h).held
    (physical x b h).privateId x.ids (physical x b h).target x.rewards
    (localCoordinates x b h) w t hpast


/-- A crossing observed in a finite prefix is exactly the final output state. -/
theorem output_eq_of_crossing (x : Input p) (r : ℕ) (hr : r ≤ n_boot p)
    (hc : (run x r).crossing.isSome = true) : output x = run x r := by
  have he := run_stops_at_crossing x r (n_boot p - r) hc
  rw [Nat.add_sub_of_le hr] at he
  exact he

/-- The actual launch output is the next round after the first crossing
block's clipped end, including a possible `T+1` launch. -/
theorem launchRound_of_first_crossing (x : Input p) (r : ℕ) (hr : r + 1 ≤ n_boot p)
    (hc : (run x r).crossing = none) (h : (run x r).completed < n_boot p)
    (hcross : crosses x (run x r) h = true) :
    launchRound x = ReferencePrelaunchPhysicalReplay.blockEnd p (nextBlock (run x r) h) + 1 := by
  have hs : run x (r + 1) = finishBlock x (run x r) h := by
    rw [run_succ, advance_of_no_crossing x _ hc h]
  have hsome : (run x (r + 1)).crossing.isSome = true := by
    rw [hs]
    change (if crosses x (run x r) h then some _ else none).isSome = true
    simp only [hcross, ↓reduceIte, Option.isSome_some]
  unfold launchRound
  rw [output_eq_of_crossing x (r + 1) hr hsome, hsome, ite_eq_left rfl, hs]
  rfl

/-- Already activated followers retain the entire continued state at the
actual launch output. Only the newly forced branch uses `forcedAtLaunch`. -/
theorem launch_existing_state (x : Input p) (r : ℕ) (hr : r + 1 ≤ n_boot p)
    (hc : (run x r).crossing = none) (h : (run x r).completed < n_boot p)
    (hcross : crosses x (run x r) h = true)
    (i : Follower p.m) (a : Activation p) (ha : (run x r).activation i = some a) :
    ordinary x (output x) i = atLaunch
      (ReferencePrelaunchPhysicalReplay.blockReplay (replayInput x (run x r) h i a ha)) := by
  have hs : run x (r + 1) = finishBlock x (run x r) h := by
    rw [run_succ, advance_of_no_crossing x _ hc h]
  have hsome : (run x (r + 1)).crossing.isSome = true := by
    rw [hs]
    change (if crosses x (run x r) h then some _ else none).isSome = true
    simp only [hcross, ↓reduceIte, Option.isSome_some]
  rw [output_eq_of_crossing x (r + 1) hr hsome]
  exact run_ordinary_successor x r hc h i a ha

end Bandits.Support.ReferenceInitializationRun

end
