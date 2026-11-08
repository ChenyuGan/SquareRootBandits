/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceInitializationRun

/-!
# Chronological prefix dependence of reference initialization

Sources: `sources/zip4/manuscript/07_public_setup.tex:27-40,55-140,150-164`
and `sources/zip4/manuscript/appendix_b_communication.tex:786-798`.

The results compare the actual stopped `ReferenceInitializationRun.run` and its
actual launch output. They expose its read coordinates; they do not assert
measurability, a product law, a stopping-time law, or manuscript closure.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.ReferenceInitializationRun
open Bandits.Support.BootstrapPhysicalBlock
open scoped Classical BigOperators

namespace Bandits.Support.ReferenceInitializationCausality

variable {p : Parameters}

/-- The latent private `J` scalar is absent from the actual physical block
input: changing only this scalar requires no equality hypothesis. -/
theorem physical_independent_of_latentJ (x : Input p) (b : Boundary p)
    (h : b.completed < n_boot p) (j : BootstrapPrivateRoundStreams.Scalar) :
    physical
      { x with coordinates := ((x.coordinates.1.1, j), x.coordinates.2) } b h =
        physical x b h := rfl

/-- Exact equality of the input coordinates read by the first `r` actual block
opportunities. The private `J` scalar, follower triples at labels `s ≥ r`,
target scalars at labels `s ≥ r`, and calendar coordinates at or after
`elapsed p r` are absent. -/
def runPrefixInputEq (x y : Input p) (r : ℕ) : Prop :=
  x.ids = y.ids ∧ x.rewards = y.rewards ∧ x.C_star = y.C_star ∧
  x.C_h = y.C_h ∧ x.eta = y.eta ∧
  (∀ t : Fin p.T, t.val < elapsed p r →
    (∀ u : Fin (A_id p), x.row.1 u t = y.row.1 u t) ∧
      x.row.2 t = y.row.2 t) ∧
  (∀ s : Fin (n_boot p), s.val < r →
    ∀ j : Fin (p.m - 1), x.coordinates.1.1 s j = y.coordinates.1.1 s j) ∧
  (∀ s : Fin (n_boot p), s.val < r →
    x.coordinates.2.2 s = y.coordinates.2.2 s) ∧
  (∀ i : Fin p.m, ∀ t : Fin p.T, t.val < elapsed p r →
    x.coordinates.2.1 (i, t) = y.coordinates.2.1 (i, t))

/-- Strict-past input agreement for a source round `n`. A block's draws and
target are included exactly when its clipped end is before `n`; this excludes
the current partial block when `n` lies inside one. -/
def launchPrefixInputEq (x y : Input p) (n : ℕ) : Prop :=
  x.ids = y.ids ∧ x.rewards = y.rewards ∧ x.C_star = y.C_star ∧
  x.C_h = y.C_h ∧ x.eta = y.eta ∧
  (∀ t : Fin p.T, t.val + 1 < n →
    (∀ u : Fin (A_id p), x.row.1 u t = y.row.1 u t) ∧
      x.row.2 t = y.row.2 t) ∧
  (∀ s : Fin (n_boot p), elapsed p (s.val + 1) < n →
    (∀ j : Fin (p.m - 1), x.coordinates.1.1 s j = y.coordinates.1.1 s j) ∧
      x.coordinates.2.2 s = y.coordinates.2.2 s) ∧
  (∀ i : Fin p.m, ∀ t : Fin p.T, t.val + 1 < n →
    x.coordinates.2.1 (i, t) = y.coordinates.2.1 (i, t))

theorem runPrefixInputEq_mono (x y : Input p) {r q : ℕ} (hrq : r ≤ q)
    (h : runPrefixInputEq x y q) : runPrefixInputEq x y r := by
  rcases h with ⟨hids, hrew, hstar, hh, heta, hrow, hblock, htarget, hround⟩
  refine ⟨hids, hrew, hstar, hh, heta, ?_, ?_, ?_, ?_⟩
  · intro t ht
    exact hrow t (Nat.lt_of_lt_of_le ht (elapsed_mono p hrq))
  · intro s hs j
    exact hblock s (by omega) j
  · intro s hs
    exact htarget s (by omega)
  · intro i t ht
    exact hround i t (Nat.lt_of_lt_of_le ht (elapsed_mono p hrq))

theorem runPrefixInputEq_of_launchPrefixInputEq (x y : Input p) {n r : ℕ}
    (hr : elapsed p r < n) (h : launchPrefixInputEq x y n) :
    runPrefixInputEq x y r := by
  rcases h with ⟨hids, hrew, hstar, hh, heta, hrow, hblock, hround⟩
  refine ⟨hids, hrew, hstar, hh, heta, ?_, ?_, ?_, ?_⟩
  · intro t ht
    have htn : t.val + 1 < n := by omega
    exact hrow t htn
  · intro s hs j
    have hsEnd : elapsed p (s.val + 1) ≤ elapsed p r := by
      apply elapsed_mono p
      omega
    exact (hblock s (hsEnd.trans_lt hr)).1 j
  · intro s hs
    have hsEnd : elapsed p (s.val + 1) ≤ elapsed p r := by
      apply elapsed_mono p
      omega
    exact (hblock s (hsEnd.trans_lt hr)).2
  · intro i t ht
    have htn : t.val + 1 < n := by omega
    exact hround i t htn

/-- Equality of one physical block's generated pre-choice state follows from
the existing block-causality theorem once its actual incoming draws, target,
and calendar strict past agree. -/
theorem physical_prechoice_eq_of_actual_past
    (x y : Input p) (b : Boundary p) (h : b.completed < n_boot p)
    (hids : x.ids = y.ids) (hrew : x.rewards = y.rewards)
    (hdraw : ∀ j : Fin (p.m - 1),
      x.coordinates.1.1 (nextBlock b h) j = y.coordinates.1.1 (nextBlock b h) j)
    (htarget : x.coordinates.2.2 (nextBlock b h) =
      y.coordinates.2.2 (nextBlock b h))
    (t : Fin p.T)
    (hrow : ∀ u : Fin (A_id p), ∀ q : Fin p.T, q.val < t.val →
      x.row.1 u q = y.row.1 u q)
    (hlearning : ∀ q : Fin p.T, q.val < t.val → x.row.2 q = y.row.2 q)
    (hround : ∀ i : Fin p.m, ∀ q : Fin p.T, q.val < t.val →
      x.coordinates.2.1 (i, q) = y.coordinates.2.1 (i, q)) :
    BootstrapPhysicalBlock.run (physical x b h) t.val =
      BootstrapPhysicalBlock.run (physical y b h) t.val := by
  let vx := physical x b h
  let vy := physical y b h
  have hdrawProfile : ∀ j : {j // j ∈ uninformed b},
      (vx.active j, vx.held j, vx.privateId j) =
        (vy.active j, vy.held j, vy.privateId j) := by
    intro j
    calc
      (vx.active j, vx.held j, vx.privateId j) =
          PrivateSourceStreams.blockDrawProfileMap p b.numerators b.weight_ge_one
            (x.coordinates.1.1 (nextBlock b h))
            (BootstrapPhysicalInput.sourceFollowerIndex p j.1) :=
        physical_own_block_draw x b h j
      _ = PrivateSourceStreams.blockDrawProfileMap p b.numerators b.weight_ge_one
            (y.coordinates.1.1 (nextBlock b h))
            (BootstrapPhysicalInput.sourceFollowerIndex p j.1) := by
        simpa only [BootstrapPhysicalInput.currentBlockDrawProfile] using
          (BootstrapPhysicalInput.incoming_blockDraw_eq_of_own_triple_eq
            p (nextBlock b h) (uninformed b) b.numerators b.weight_ge_one
            x.coordinates y.coordinates j
            (hdraw (BootstrapPhysicalInput.sourceFollowerIndex p j.1)))
      _ = (vy.active j, vy.held j, vy.privateId j) :=
        (physical_own_block_draw y b h j).symm
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
    change BootstrapPhysicalInput.targetArmMap p (nextBlock b h) x.coordinates =
      BootstrapPhysicalInput.targetArmMap p (nextBlock b h) y.coordinates
    exact BootstrapPhysicalInput.targetArmMap_eq_of_target_scalar_eq p
      (nextBlock b h) x.coordinates y.coordinates htarget
  let w : BootstrapBlockCausality.LocalCoordinates p (uninformed b) vx.held vx.target :=
    (y.row, (vy.uniform,
      (fun q => ⟨(vy.coordinatorAvoid q).val, by
          simpa only [htargetArm] using (vy.coordinatorAvoid q).property⟩,
        fun j q => ⟨(vy.followerAvoid j q).val, by
          simpa only [congrFun hheld j] using (vy.followerAvoid j q).property⟩)))
  have hroundCoordinates : ∀ q : Fin p.T, q.val < t.val →
      BootstrapBlockCausality.roundCoordinatesEq (uninformed b) vx.held vx.target
        (localCoordinates x b h) w q := by
    intro q hq
    dsimp only [BootstrapBlockCausality.roundCoordinatesEq, localCoordinates, w]
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
        (nextBlock b h) x.coordinates q =
          BootstrapPhysicalInput.coordinatorAvoidArmValueMap p
            (nextBlock b h) y.coordinates q
      rcases BootstrapPhysicalInput.coordinator_roundDraws_eq_of_own_coordinates_eq
          p (nextBlock b h) x.coordinates y.coordinates q htarget
          (hround (Bandits.Support.ActiveRoundActions.coordinator p.two_le_m) q hq)
        with ⟨_, _, havoid⟩
      exact havoid
    · intro j
      apply Subtype.ext
      change BootstrapPhysicalInput.followerAvoidArmValueMap p
        (nextBlock b h) (uninformed b) b.numerators b.weight_ge_one
        x.coordinates j q =
          BootstrapPhysicalInput.followerAvoidArmValueMap p
            (nextBlock b h) (uninformed b) b.numerators b.weight_ge_one
            y.coordinates j q
      have htriple : x.coordinates.1.1 (nextBlock b h)
          (BootstrapPhysicalInput.sourceFollowerIndex p j.1) =
            y.coordinates.1.1 (nextBlock b h)
              (BootstrapPhysicalInput.sourceFollowerIndex p j.1) :=
        hdraw (BootstrapPhysicalInput.sourceFollowerIndex p j.1)
      rcases BootstrapPhysicalInput.follower_roundDraws_eq_of_own_coordinates_eq
          p (nextBlock b h) (uninformed b) b.numerators b.weight_ge_one
          x.coordinates y.coordinates j q htriple
          (hround (Bandits.Support.PublicDiscreteDraws.followerPlayer p.two_le_m j.1) q hq) with
        ⟨_, havoid⟩
      exact havoid
  have hrun := BootstrapBlockCausality.run_eq_of_prefixCoordinatesEq
    (s := nextBlock b h) (uninformed b) vx.active vx.held vx.privateId vx.ids vx.target
    vx.rewards (localCoordinates x b h) w t.val hroundCoordinates
  have hinputW : BootstrapBlockCausality.blockInput
      (s := nextBlock b h) (uninformed b) vx.active vx.held vx.privateId
      vx.ids vx.target vx.rewards w = vy := by
    simp only [vy, physical, BootstrapPhysicalInput.blockInput,
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
  rw [hinputW] at hrun
  simpa only [vx, vy, physical, BootstrapPhysicalInput.blockInput,
    BootstrapBlockCausality.blockInput, BootstrapBlockCausality.inputOf,
    localCoordinates] using hrun

/-- The existing physical block's pre-choice state at a calendar coordinate
already reached by opportunity `r` is fixed by the exact run read set. The
incoming draws are selected only for this supplied boundary's actual label. -/
theorem physical_prechoice_eq_of_runPrefixInputEq
    (x y : Input p) (b : Boundary p) (h : b.completed < n_boot p)
    {r : ℕ} (hr : b.completed < r) (hp : runPrefixInputEq x y r)
    (t : Fin p.T) (ht : t.val < elapsed p r) :
    BootstrapPhysicalBlock.run (physical x b h) t.val =
      BootstrapPhysicalBlock.run (physical y b h) t.val := by
  rcases hp with ⟨hids, hrew, _, _, _, hrows, hblocks, htargets, hrounds⟩
  apply physical_prechoice_eq_of_actual_past x y b h hids hrew
  · intro j
    exact hblocks (nextBlock b h) (by simpa [nextBlock] using hr) j
  · exact htargets (nextBlock b h) (by simpa [nextBlock] using hr)
  · intro u q hqt
    exact (hrows q (by omega)).1 u
  · intro q hqt
    exact (hrows q (by omega)).2
  · intro i q hqt
    exact hrounds i q (by omega)

/-- Transfer strict-past block causality across equal generated boundaries.
The histories, activations, numerators, counters and exceptional flags are
identified by the boundary equality itself. -/
theorem physical_prechoice_eq_of_equal_boundaries
    (x y : Input p) (bx b2 : Boundary p) (hboundary : bx = b2)
    (hx : bx.completed < n_boot p) (h2 : b2.completed < n_boot p)
    {r : ℕ} (hr : bx.completed < r) (hp : runPrefixInputEq x y r)
    (t : Fin p.T) (ht : t.val < elapsed p r) :
    BootstrapPhysicalBlock.run (physical x bx hx) t.val =
      BootstrapPhysicalBlock.run (physical y b2 h2) t.val := by
  cases hboundary
  have hproof : h2 = hx := Subsingleton.elim _ _
  cases hproof
  exact physical_prechoice_eq_of_runPrefixInputEq x y bx hx hr hp t ht

/-- The within-block pre-choice comparison follows from the strict-past
calendar read set whenever the supplied boundary is among the completed
opportunities before source round `n`. -/
theorem physical_prechoice_eq_of_launchPrefixInputEq
    (x y : Input p) (b : Boundary p) (h : b.completed < n_boot p)
    {r n : ℕ} (hr : b.completed < r) (hcut : elapsed p r < n)
    (hp : launchPrefixInputEq x y n) (t : Fin p.T)
    (ht : t.val < elapsed p r) :
    BootstrapPhysicalBlock.run (physical x b h) t.val =
      BootstrapPhysicalBlock.run (physical y b h) t.val := by
  apply physical_prechoice_eq_of_runPrefixInputEq x y b h hr _ t ht
  exact runPrefixInputEq_of_launchPrefixInputEq x y hcut hp

/-- Exact arithmetic characterization of the launch sublevel event. Below
`T+1`, launch has happened by `n` precisely when the output's crossing
boundary ends strictly before `n`; at `T+1` the no-launch sentinel is included. -/
theorem launchSublevel_characterization (x : Input p) {n : ℕ}
    (hnT : n ≤ p.T + 1) :
    launchRound x ≤ n ↔
      (((output x).crossing.isSome = true ∧
          elapsed p (output x).completed < n) ∨
        ((output x).crossing = none ∧ n = p.T + 1)) := by
  unfold launchRound
  cases hcross : (output x).crossing with
  | none =>
      simp
      omega
  | some s =>
      simp

end Bandits.Support.ReferenceInitializationCausality

end
