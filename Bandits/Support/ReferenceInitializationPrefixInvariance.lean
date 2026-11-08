/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceInitializationCausality

/-!
# Generated reference-run prefix invariance

Sources: `sources/zip4/manuscript/07_public_setup.tex:27-40,55-140,150-164`
and `sources/zip4/manuscript/appendix_b_communication.tex:786-798`.

Deterministic comparisons on the existing input, block recursion and stopped
boundary. No measurable encoding, probabilistic law, or manuscript closure is
asserted here. All comparison premises are literal original-coordinate equalities.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ReferenceInitializationPrefixInvariance

open ConstructorDimensions BootstrapDimensions ReferenceInitializationRun
open ReferenceInitializationCausality BootstrapPrivateRoundStreams
open BootstrapPhysicalBlock hiding Input run
open scoped Classical BigOperators

variable {p : Parameters}

-- Transport only dependent arm certificates into the existing coordinate API.
-- This is a comparison of the accepted physical inputs, not a new execution.
private theorem physical_coordinate_comparison
    (x y : Input p) (b : Boundary p) (h : b.completed < n_boot p)
    (k : ℕ) (hids : x.ids = y.ids) (hrew : x.rewards = y.rewards)
    (hdraw : ∀ j : Fin (p.m - 1),
      x.coordinates.1.1 (nextBlock b h) j = y.coordinates.1.1 (nextBlock b h) j)
    (htarget : x.coordinates.2.2 (nextBlock b h) = y.coordinates.2.2 (nextBlock b h))
    (hrow : ∀ u : Fin (A_id p), ∀ q : Fin p.T, q.val < k →
      x.row.1 u q = y.row.1 u q)
    (hlearning : ∀ q : Fin p.T, q.val < k → x.row.2 q = y.row.2 q)
    (hround : ∀ i : Fin p.m, ∀ q : Fin p.T, q.val < k →
      x.coordinates.2.1 (i, q) = y.coordinates.2.1 (i, q)) :
    ∃ w : BootstrapBlockCausality.LocalCoordinates p (uninformed b)
        (physical x b h).held (physical x b h).target,
      BootstrapBlockCausality.blockInput (s := nextBlock b h) (uninformed b)
        (physical x b h).active (physical x b h).held (physical x b h).privateId
        (physical x b h).ids (physical x b h).target (physical x b h).rewards w =
          physical y b h ∧
      ∀ q : Fin p.T, q.val < k →
        BootstrapBlockCausality.roundCoordinatesEq (uninformed b)
          (physical x b h).held (physical x b h).target (localCoordinates x b h) w q := by
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
  have hroundCoordinates : ∀ q : Fin p.T, q.val < k →
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
  exact ⟨w, hinputW, hroundCoordinates⟩

/-- The physical recursion agrees through a natural cutoff, including `T`.
Every current action and typed observation strictly before the cutoff agrees. -/
theorem physical_prefix_eq (x y : Input p) (b : Boundary p)
    (h : b.completed < n_boot p) {r : ℕ} (hr : b.completed < r)
    (hp : runPrefixInputEq x y r) :
    (∀ k ≤ elapsed p r,
      BootstrapPhysicalBlock.run (physical x b h) k =
        BootstrapPhysicalBlock.run (physical y b h) k) ∧
    (∀ t : Fin p.T, t.val < elapsed p r →
      BootstrapPhysicalBlock.actions (physical x b h)
          (BootstrapPhysicalBlock.run (physical x b h) t.val) t =
        BootstrapPhysicalBlock.actions (physical y b h)
          (BootstrapPhysicalBlock.run (physical y b h) t.val) t ∧
      ∀ i : Fin p.m, ownObservation (physical x b h) i t =
        ownObservation (physical y b h) i t) := by
  rcases hp with ⟨hids, hrew, _, _, _, hrows, hblocks, htargets, hrounds⟩
  obtain ⟨w, hw, hc⟩ := physical_coordinate_comparison x y b h (elapsed p r)
    hids hrew (hblocks (nextBlock b h) hr) (htargets (nextBlock b h) hr)
    (fun u q hq => (hrows q hq).1 u) (fun q hq => (hrows q hq).2) hrounds
  let v := localCoordinates x b h
  let vx := physical x b h
  have hx : BootstrapBlockCausality.blockInput (s := nextBlock b h) (uninformed b)
      vx.active vx.held vx.privateId vx.ids vx.target vx.rewards v = vx := rfl
  have hk : ∀ k ≤ elapsed p r,
      BootstrapPhysicalBlock.run vx k = BootstrapPhysicalBlock.run (physical y b h) k := by
    intro k hk
    have he := BootstrapBlockCausality.run_eq_of_prefixCoordinatesEq
      (s := nextBlock b h) (uninformed b) vx.active vx.held vx.privateId vx.ids
      vx.target vx.rewards v w k (fun q hq => hc q (Nat.lt_of_lt_of_le hq hk))
    rw [hx, hw] at he
    exact he
  refine ⟨hk, ?_⟩
  intro t ht
  have ha := BootstrapBlockCausality.actions_eq_of_roundCoordinatesEq
    (s := nextBlock b h) (uninformed b) vx.active vx.held vx.privateId vx.ids
    vx.target vx.rewards v w (BootstrapPhysicalBlock.run vx t.val) t (hc t ht)
  have hf := BootstrapBlockCausality.feedback_eq_of_roundCoordinatesEq
    (s := nextBlock b h) (uninformed b) vx.active vx.held vx.privateId vx.ids
    vx.target vx.rewards v w (BootstrapPhysicalBlock.run vx t.val) t
  rw [hx, hw] at ha
  have ha' : BootstrapPhysicalBlock.actions vx (BootstrapPhysicalBlock.run vx t.val) t =
      BootstrapPhysicalBlock.actions (physical y b h)
        (BootstrapPhysicalBlock.run (physical y b h) t.val) t :=
    ha.trans (congrArg (fun st => BootstrapPhysicalBlock.actions (physical y b h) st t)
      (hk t.val ht.le))
  refine ⟨ha', ?_⟩
  intro i
  apply Subtype.ext
  apply Subtype.ext
  change BootstrapPhysicalBlock.feedback vx (BootstrapPhysicalBlock.run vx t.val) t i = _
  have he := hf i (hc t ht)
  rw [hx, hw] at he
  exact he.trans (congrArg (fun st => BootstrapPhysicalBlock.feedback
    (physical y b h) st t i) (hk t.val ht.le))

private theorem block_round_lt_elapsed (b : Boundary p) (h : b.completed < n_boot p)
    {r : ℕ} (hr : b.completed < r) (t : Fin p.T)
    (ht : t ∈ calendarBlock p (nextBlock b h)) : t.val < elapsed p r := by
  have he := ((mem_calendarBlock_iff p (nextBlock b h) t).mp ht).2
  change t.val < elapsed p (b.completed + 1) at he
  exact he.trans_le (elapsed_mono p (show b.completed + 1 ≤ r by omega))

/-- The full true-candidate scan agrees, even though it scans through `T`.
Its actual eligibility gate makes every observation outside this block inert. -/
theorem controller_prefix_eq (x y : Input p) (b : Boundary p)
    (h : b.completed < n_boot p) {r : ℕ} (hr : b.completed < r)
    (hp : runPrefixInputEq x y r) (i : {i // i ∈ uninformed b}) (k : ℕ) :
    BootstrapTruePrefixController.run (physical x b h) i k =
      BootstrapTruePrefixController.run (physical y b h) i k := by
  have hdraw := BootstrapPhysicalInput.incoming_blockDraw_eq_of_own_triple_eq
    p (nextBlock b h) (uninformed b) b.numerators b.weight_ge_one
    x.coordinates y.coordinates i
    (hp.2.2.2.2.2.2.1 (nextBlock b h) hr
      (BootstrapPhysicalInput.sourceFollowerIndex p i.val))
  have ha : (physical x b h).active i = (physical y b h).active i :=
    congrArg Prod.fst hdraw
  have hid : (physical x b h).privateId i = (physical y b h).privateId i :=
    congrArg (fun z => z.2.2) hdraw
  have hobs := (physical_prefix_eq x y b h hr hp).2
  induction k with
  | zero => rfl
  | succ k ih =>
      by_cases hk : k < p.T
      · let t : Fin p.T := ⟨k, hk⟩
        change BootstrapTruePrefixController.run (physical x b h) i (t.val + 1) =
          BootstrapTruePrefixController.run (physical y b h) i (t.val + 1)
        rw [BootstrapTruePrefixController.run_succ (physical x b h) i t,
          BootstrapTruePrefixController.run_succ (physical y b h) i t, ih]
        by_cases ht : t ∈ calendarBlock p (nextBlock b h)
        · have hlt := block_round_lt_elapsed b h hr t ht
          have hrow := hp.2.2.2.2.2.1 t hlt
          have hindex : BootstrapPhysicalBlock.observationIndex (physical x b h)
                (BootstrapPhysicalBlock.run (physical x b h) t.val) t
                (PublicDiscreteDraws.followerPlayer p.two_le_m i.val) =
              BootstrapPhysicalBlock.observationIndex (physical y b h)
                (BootstrapPhysicalBlock.run (physical y b h) t.val) t
                (PublicDiscreteDraws.followerPlayer p.two_le_m i.val) := by
            unfold BootstrapPhysicalBlock.observationIndex
            rw [(hobs t hlt).1]
            change (if _ then x.rewards t _ else _) = (if _ then y.rewards t _ else _)
            rw [hp.2.1]
          have hslot : BootstrapPhysicalBlock.slot (physical x b h) t =
              BootstrapPhysicalBlock.slot (physical y b h) t := by
            change PublicDiscreteDraws.slotDraw (x.row.2 t).1 =
              PublicDiscreteDraws.slotDraw (y.row.2 t).1
            rw [hrow.2]
          have he : BootstrapTruePrefixController.eligible (physical x b h) i t ↔
              BootstrapTruePrefixController.eligible (physical y b h) i t := by
            simp only [BootstrapTruePrefixController.eligible, ha, hid, hslot, hindex]
            change (_ ∧ _ ∧ x.ids _ _ = false ∧ _) ↔
              (_ ∧ _ ∧ y.ids _ _ = false ∧ _)
            rw [hp.1]
          have hf : BootstrapTruePrefixController.trueForwardBit (physical x b h) i t =
              BootstrapTruePrefixController.trueForwardBit (physical y b h) i t := by
            unfold BootstrapTruePrefixController.trueForwardBit
            rw [hid]
            exact hrow.1 _
          simp only [BootstrapTruePrefixController.advance,
            BootstrapTruePrefixController.eligibleFlag, propext he, hf]
          rfl
        · rw [BootstrapTruePrefixController.advance_eq_of_outside_block (physical x b h) i _ t ht,
            BootstrapTruePrefixController.advance_eq_of_outside_block (physical y b h) i _ t ht]
      · simp only [BootstrapTruePrefixController.run, hk, ↓reduceDIte, ih]

private theorem observationIndex_prefix_eq (x y : Input p) (b : Boundary p)
    (h : b.completed < n_boot p) {r : ℕ} (hr : b.completed < r)
    (hp : runPrefixInputEq x y r) (t : Fin p.T) (ht : t.val < elapsed p r)
    (i : Fin p.m) :
    BootstrapPhysicalBlock.observationIndex (physical x b h)
        (BootstrapPhysicalBlock.run (physical x b h) t.val) t i =
      BootstrapPhysicalBlock.observationIndex (physical y b h)
        (BootstrapPhysicalBlock.run (physical y b h) t.val) t i := by
  unfold BootstrapPhysicalBlock.observationIndex
  rw [((physical_prefix_eq x y b h hr hp).2 t ht).1]
  change (if _ then x.rewards t _ else _) = (if _ then y.rewards t _ else _)
  rw [hp.2.1]

/-- The accepted weight inputs agree with their full calendar gains. In
particular the true save does not truncate the observations after saving. -/
theorem weightInput_prefix_eq (x y : Input p) (b : Boundary p)
    (h : b.completed < n_boot p) {r : ℕ} (hr : b.completed < r)
    (hp : runPrefixInputEq x y r) (i : {i // i ∈ uninformed b}) :
    weightInput x b h i = weightInput y b h i := by
  have hd := BootstrapPhysicalInput.incoming_blockDraw_eq_of_own_triple_eq
    p (nextBlock b h) (uninformed b) b.numerators b.weight_ge_one
    x.coordinates y.coordinates i
    (hp.2.2.2.2.2.2.1 (nextBlock b h) hr
      (BootstrapPhysicalInput.sourceFollowerIndex p i.val))
  have ha : (physical x b h).active i = (physical y b h).active i :=
    congrArg Prod.fst hd
  have hh : (physical x b h).held i = (physical y b h).held i :=
    congrArg (fun z => z.2.1) hd
  have hid : (physical x b h).privateId i = (physical y b h).privateId i :=
    congrArg (fun z => z.2.2) hd
  have hids : (physical x b h).ids = (physical y b h).ids := hp.1
  have hs : BootstrapTruePrefixController.savedAt (physical x b h) i =
      BootstrapTruePrefixController.savedAt (physical y b h) i := by
    funext t
    simp only [BootstrapTruePrefixController.savedAt,
      controller_prefix_eq x y b h hr hp]
  have ho : (fun t : Fin p.T => if t ∈ calendarBlock p (nextBlock b h) then
        BootstrapPhysicalBlock.observationIndex (physical x b h)
          (BootstrapPhysicalBlock.run (physical x b h) t.val) t
          (PublicDiscreteDraws.followerPlayer p.two_le_m i.val) else ⟨0, Nat.zero_lt_succ _⟩) =
      (fun t : Fin p.T => if t ∈ calendarBlock p (nextBlock b h) then
        BootstrapPhysicalBlock.observationIndex (physical y b h)
          (BootstrapPhysicalBlock.run (physical y b h) t.val) t
          (PublicDiscreteDraws.followerPlayer p.two_le_m i.val) else ⟨0, Nat.zero_lt_succ _⟩) := by
    funext t
    split_ifs with ht
    · exact observationIndex_prefix_eq x y b h hr hp t
        (block_round_lt_elapsed b h hr t ht) _
    · rfl
  unfold weightInput
  congr 1
  simp only [BootstrapTruePrefixController.observationTrace,
    BootstrapPhysicalBlock.observationTrace, ha, hh, hid, hids, hs, ho]

/-- One actual block transition preserves the entire boundary under the
literal run-prefix input comparison. The incoming boundary is common only
in this local induction step; the generated-run theorem supplies it below. -/
theorem finishBlock_eq_of_runPrefixInputEq (x y : Input p) (b : Boundary p)
    (h : b.completed < n_boot p) {r : ℕ} (hr : b.completed < r)
    (hp : runPrefixInputEq x y r) : finishBlock x b h = finishBlock y b h := by
  have hext : extendedHistory x b h = extendedHistory y b h := by
    funext i t
    unfold extendedHistory
    split_ifs with ht
    · rfl
    · have hlt : t.val < elapsed p r :=
        t.isLt.trans_le (elapsed_mono p (by omega))
      have ho := (physical_prefix_eq x y b h hr hp).2
        ⟨t.val, t.isLt.trans_le (elapsed_le_T p _)⟩ hlt
      exact Prod.ext (congrFun ho.1 i) (ho.2 i)
  have hn : updatedNumerators x b h = updatedNumerators y b h := by
    funext j
    unfold updatedNumerators
    dsimp only
    split_ifs with hi
    · rw [weightInput_prefix_eq x y b h hr hp]
    · rfl
  have hd : declaredActivation x b h = declaredActivation y b h := by
    funext i
    unfold declaredActivation
    by_cases hi : i ∈ uninformed b
    · rw [dite_eq_left hi, dite_eq_left hi]
      have he : candidate x b h ⟨i, hi⟩ = candidate y b h ⟨i, hi⟩ :=
        controller_prefix_eq x y b h hr hp ⟨i, hi⟩ p.T
      rw [he]
    · rw [dite_eq_right hi, dite_eq_right hi]
  have hc : updatedCounters x b h = updatedCounters y b h := by
    funext a
    unfold updatedCounters
    congr 1
    apply Finset.sum_congr rfl
    intro t ht
    have hlt := block_round_lt_elapsed b h hr t ht
    have hrow := (hp.2.2.2.2.2.1 t hlt).2
    have hfeedback : BootstrapPhysicalBlock.feedback (physical x b h)
          (BootstrapPhysicalBlock.run (physical x b h) t.val) t
          (ActiveRoundActions.coordinator p.two_le_m) =
        BootstrapPhysicalBlock.feedback (physical y b h)
          (BootstrapPhysicalBlock.run (physical y b h) t.val) t
          (ActiveRoundActions.coordinator p.two_le_m) :=
      congrArg (fun o : ReferencePrelaunchFollower.Observation p => o.val.val)
        (((physical_prefix_eq x y b h hr hp).2 t hlt).2 _)
    have hslot : BootstrapPhysicalBlock.slot (physical x b h) t =
        BootstrapPhysicalBlock.slot (physical y b h) t := by
      change PublicDiscreteDraws.slotDraw (x.row.2 t).1 =
        PublicDiscreteDraws.slotDraw (y.row.2 t).1
      rw [hrow]
    have htuple : BootstrapPhysicalBlock.tuple (physical x b h) t =
        BootstrapPhysicalBlock.tuple (physical y b h) t := by
      unfold BootstrapPhysicalBlock.tuple
      change OrderedTupleSampler.sample p.two_le_m p.m_lt_K (x.row.2 t).1 = _
      rw [hrow]
      rfl
    simp only [downArm, hslot, hfeedback, htuple]
    rfl
  have hcross : crosses x b h = crosses y b h := by
    simp only [crosses, hc, hp.2.2.1, hp.2.2.2.1]
  have hf : forced x b h = forced y b h := by
    funext i
    simp only [forced, hcross, hd]
  have hfinal : finalActivation x b h = finalActivation y b h := by
    funext i
    simp only [finalActivation, hf, hd]
  unfold finishBlock
  congr 1
  · rw [hcross]
  · rw [hf]

/-- Completed physical blocks never exceed the number of opportunities.
This supplies the actual private-block label bound in the two-input induction. -/
theorem run_completed_le (x : Input p) (r : ℕ) : (run x r).completed ≤ r := by
  induction r with
  | zero => exact le_rfl
  | succ r ih =>
      rw [ReferenceInitializationRun.run_succ]
      unfold advance
      split_ifs with hc h
      · exact ih.trans (Nat.le_succ _)
      · exact Nat.succ_le_succ ih
      · exact ih.trans (Nat.le_succ _)

/-- Full generated boundary equality from the exact existing coordinate
prefix. No boundary, controller, history, or finished-block equality is an
input. Stopped and exhausted branches retain the complete boundary. -/
theorem run_eq_of_runPrefixInputEq (x y : Input p) (r : ℕ)
    (hp : runPrefixInputEq x y r) : run x r = run y r := by
  induction r with
  | zero => rfl
  | succ r ih =>
      have he := ih (runPrefixInputEq_mono x y (Nat.le_succ _) hp)
      rw [ReferenceInitializationRun.run_succ, ReferenceInitializationRun.run_succ, ← he]
      unfold advance
      split_ifs with hc h
      · rfl
      · apply finishBlock_eq_of_runPrefixInputEq x y (run x r) h _ hp
        exact Nat.lt_succ_of_le (run_completed_le x r)
      · rfl

/-- A generated boundary is reached at its own completed-block index. The
proof uses progress before crossing and the actual stopped branch afterward. -/
theorem run_at_completed (x : Input p) (r : ℕ) (hr : r ≤ n_boot p) :
    run x (run x r).completed = run x r := by
  induction r with
  | zero => rfl
  | succ r ih =>
      by_cases hc : (run x r).crossing.isSome = true
      · rw [ReferenceInitializationRun.run_succ, advance_of_crossing x _ hc]
        exact ih (by omega)
      · have he := (run_progress x r (by omega)).resolve_left hc
        have hn : (run x r).crossing = none := by
          cases hcross : (run x r).crossing with
          | none => rfl
          | some s => exact False.elim (hc (by rw [hcross]; rfl))
        have hb : (run x r).completed < n_boot p := by omega
        have hs : run x (r + 1) = finishBlock x (run x r) hb := by
          rw [ReferenceInitializationRun.run_succ, advance_of_no_crossing x _ hn hb]
        rw [hs]
        change run x ((run x r).completed + 1) = finishBlock x (run x r) hb
        rw [he, hs]

/-- Below the sentinel, the actual launch event has a witness consisting only
of completed blocks whose clipped end is strictly before the queried round.
It never requires the final output to be determined by a shorter prefix. -/
theorem launchSublevel_iff_completed_prefix (x : Input p) {n : ℕ}
    (hn : n < p.T + 1) :
    launchRound x ≤ n ↔ ∃ r ≤ n_boot p,
      elapsed p r < n ∧ (run x r).crossing.isSome = true := by
  rw [launchSublevel_characterization x hn.le]
  constructor
  · rintro (⟨hc, he⟩ | ⟨_, heq⟩)
    · refine ⟨(output x).completed, (output x).completed_le, he, ?_⟩
      have hid := run_at_completed x (n_boot p) le_rfl
      change run x (output x).completed = output x at hid
      rw [hid]
      exact hc
    · omega
  · rintro ⟨r, hr, he, hc⟩
    left
    rw [output_eq_of_crossing x r hr hc]
    exact ⟨hc, (elapsed_mono p (run_completed_le x r)).trans_lt he⟩

/-- The actual launch sublevel event is invariant under the existing strict
past comparison, for every source query through the `T+1` sentinel. Only
completed blocks ending before `n` are compared, including when `n` lies
inside a block or the last block is shortened. -/
theorem launchSublevel_eq_of_launchPrefixInputEq (x y : Input p) {n : ℕ}
    (hn : n ≤ p.T + 1) (hp : launchPrefixInputEq x y n) :
    launchRound x ≤ n ↔ launchRound y ≤ n := by
  by_cases hlast : n = p.T + 1
  · subst n
    exact iff_of_true (launchRound_bounds x).2 (launchRound_bounds y).2
  · have hlt : n < p.T + 1 := by omega
    rw [launchSublevel_iff_completed_prefix x hlt,
      launchSublevel_iff_completed_prefix y hlt]
    have he : ∀ r, elapsed p r < n → run x r = run y r := by
      intro r hr
      exact run_eq_of_runPrefixInputEq x y r
        (runPrefixInputEq_of_launchPrefixInputEq x y hr hp)
    constructor
    · rintro ⟨r, hr, hcut, hc⟩
      exact ⟨r, hr, hcut, by rw [← he r hcut]; exact hc⟩
    · rintro ⟨r, hr, hcut, hc⟩
      exact ⟨r, hr, hcut, by rw [he r hcut]; exact hc⟩

end Bandits.Support.ReferenceInitializationPrefixInvariance

end
