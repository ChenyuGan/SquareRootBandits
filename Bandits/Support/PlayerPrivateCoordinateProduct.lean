/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.BootstrapPrivateRoundStreams
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Raw player-private coordinate regrouping

This module repackages the original exogenous private coordinates into the
coordinator's and followers' own raw views, and proves that the resulting
views still have their literal independent product law. It does not define a
physical execution or an adaptive conditional law.

The source passages describe the coordinator and follower labels and their
private randomness in `sources/zip4/manuscript/01_introduction.tex:18-36` and
`sources/zip4/manuscript/07_public_setup.tex:27-38,55-114`. The regret
interpretation and fixed-public expectation are in
`sources/zip4/manuscript/08_main_theorem.tex:26-42,67-75`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.PrivateSourceStreams
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.BootstrapDimensions
open Bandits.Support.FiniteBanditModel
open Bandits.Support.MeasurableLocalRollout

namespace Bandits.Support.PlayerPrivateCoordinateProduct

/-- The genuine half-open scalar carrier shared by the admitted source laws. -/
abbrev Scalar := ContinuousCategorical.Scalar

/-- The coordinator's original raw private coordinates: the raw scalar for
`J`, its entire player-round scalar stream, and the entire target-scalar
array. -/
abbrev CoordinatorRaw (p : Parameters) :=
  ContinuousCategorical.Scalar ×
    ((Fin p.T → ContinuousCategorical.Scalar) × CoordinatorTargetScalars p)

/-- A follower's original raw block-triple stream and player-round scalar
stream. -/
abbrev FollowerRaw (p : Parameters) :=
  FollowerStream p × PlayerRoundScalarStream p

/-- The coordinator view followed by one raw view for every follower. -/
abbrev RawProfile (p : Parameters) :=
  CoordinatorRaw p × (Fin (p.m - 1) → FollowerRaw p)

/-- Player zero in the manuscript's zero-based `Fin` labels. -/
def coordinatorPlayer (p : Parameters) : Fin p.m :=
  ⟨0, by have hm := p.two_le_m; omega⟩

/-- The manuscript player labelled `i.val + 1`, for follower slot `i`. -/
def followerPlayer (p : Parameters) (i : Fin (p.m - 1)) : Fin p.m :=
  ⟨i.val + 1, by have hm := p.two_le_m; have hi := i.isLt; omega⟩

/-- Convert a nonzero player label back to its follower slot. -/
def followerSlotOfPlayer (p : Parameters) (j : Fin p.m)
    (hj : j ≠ coordinatorPlayer p) : Fin (p.m - 1) :=
  ⟨j.val - 1, by
    have hm := p.two_le_m
    have hj0 : j.val ≠ 0 := by
      intro h
      apply hj
      apply Fin.ext
      simpa [coordinatorPlayer] using h
    have hlt := j.isLt
    omega⟩

theorem coordinatorPlayer_ne_followerPlayer (p : Parameters)
    (i : Fin (p.m - 1)) : coordinatorPlayer p ≠ followerPlayer p i := by
  intro h
  have hval := congrArg Fin.val h
  simp [coordinatorPlayer, followerPlayer] at hval

/-- Literal forward coordinate rearrangement of the complete original raw
private tuple. -/
def rawRegroupForward (p : Parameters)
    (e : ExtendedPrivateCoordinates p) : RawProfile p :=
  ((e.1.2,
      ((fun t => e.2.1 (coordinatorPlayer p, t)), e.2.2)),
    fun i =>
      ((fun b => e.1.1 b i),
        fun t => e.2.1 (followerPlayer p i, t)))

/-- Literal inverse coordinate rearrangement. The two cases partition the
actual player labels into coordinator and follower labels. -/
def rawRegroupBackward (p : Parameters)
    (x : RawProfile p) : ExtendedPrivateCoordinates p :=
  ((fun b => fun i => (x.2 i).1 b, x.1.1),
    ((fun z => if h : z.1 = coordinatorPlayer p then x.1.2.1 z.2
      else (x.2 (followerSlotOfPlayer p z.1 h)).2 z.2), x.1.2.2))

theorem followerSlotOfPlayer_followerPlayer (p : Parameters)
    (i : Fin (p.m - 1)) :
    followerSlotOfPlayer p (followerPlayer p i)
      (coordinatorPlayer_ne_followerPlayer p i).symm = i := by
  apply Fin.ext
  simp only [followerSlotOfPlayer, followerPlayer]
  omega

theorem followerPlayer_followerSlotOfPlayer (p : Parameters) (j : Fin p.m)
    (hj : j ≠ coordinatorPlayer p) :
    followerPlayer p (followerSlotOfPlayer p j hj) = j := by
  apply Fin.ext
  simp only [followerPlayer, followerSlotOfPlayer]
  have hj0 : j.val ≠ 0 := by
    intro h
    apply hj
    apply Fin.ext
    simpa [coordinatorPlayer] using h
  omega

theorem rawRegroupBackward_forward (p : Parameters)
    (e : ExtendedPrivateCoordinates p) :
    rawRegroupBackward p (rawRegroupForward p e) = e := by
  apply Prod.ext
  · apply Prod.ext
    · funext b i
      rfl
    · rfl
  · apply Prod.ext
    · funext z
      rcases z with ⟨j, t⟩
      by_cases hj : j = coordinatorPlayer p
      · subst j
        rfl
      · have hslot :
            followerPlayer p (followerSlotOfPlayer p j hj) = j :=
          followerPlayer_followerSlotOfPlayer p j hj
        simp only [rawRegroupBackward, rawRegroupForward, dite_eq_right hj]
        rw [hslot]
    · rfl

theorem rawRegroupForward_backward (p : Parameters) (x : RawProfile p) :
    rawRegroupForward p (rawRegroupBackward p x) = x := by
  apply Prod.ext
  · apply Prod.ext
    · rfl
    · apply Prod.ext
      · funext t
        rfl
      · rfl
  · funext i
    apply Prod.ext
    · funext b
      rfl
    · funext t
      simp only [rawRegroupForward, rawRegroupBackward]
      have hneq : followerPlayer p i ≠ coordinatorPlayer p :=
        (coordinatorPlayer_ne_followerPlayer p i).symm
      simp only [dite_eq_right hneq]
      rw [followerSlotOfPlayer_followerPlayer]

/-- The full raw coordinate rearrangement as a genuine measurable
equivalence, with no coordinate discarded or filled. -/
def rawRegroup (p : Parameters) :
    ExtendedPrivateCoordinates p ≃ᵐ RawProfile p where
  toEquiv :=
    { toFun := rawRegroupForward p
      invFun := rawRegroupBackward p
      left_inv := rawRegroupBackward_forward p
      right_inv := rawRegroupForward_backward p }
  measurable_toFun := by
    change Measurable (rawRegroupForward p)
    unfold rawRegroupForward
    measurability
  measurable_invFun := by
    change Measurable (rawRegroupBackward p)
    unfold rawRegroupBackward
    measurability

/-- Forward extraction of the retained `J` scalar. -/
theorem rawRegroup_coordinatorJ (p : Parameters)
    (e : ExtendedPrivateCoordinates p) :
    (rawRegroup p e).1.1 = e.1.2 := rfl

/-- Forward extraction of every coordinator round scalar. -/
theorem rawRegroup_coordinatorRound (p : Parameters)
    (e : ExtendedPrivateCoordinates p) (t : Fin p.T) :
    (rawRegroup p e).1.2.1 t = e.2.1 (coordinatorPlayer p, t) := rfl

/-- Forward extraction of every coordinator target scalar. -/
theorem rawRegroup_coordinatorTargets (p : Parameters)
    (e : ExtendedPrivateCoordinates p) :
    (rawRegroup p e).1.2.2 = e.2.2 := rfl

/-- Forward extraction of every block/follower triple. -/
theorem rawRegroup_followerBlock (p : Parameters)
    (e : ExtendedPrivateCoordinates p) (b : Fin (n_boot p))
    (i : Fin (p.m - 1)) :
    ((rawRegroup p e).2 i).1 b = e.1.1 b i := rfl

/-- Forward extraction of every follower round scalar. -/
theorem rawRegroup_followerRound (p : Parameters)
    (e : ExtendedPrivateCoordinates p) (i : Fin (p.m - 1))
    (t : Fin p.T) :
    ((rawRegroup p e).2 i).2 t = e.2.1 (followerPlayer p i, t) := rfl

/-- The inverse restores every block/follower triple. -/
theorem rawRegroup_inverse_followerBlock (p : Parameters)
    (x : RawProfile p) (b : Fin (n_boot p)) (i : Fin (p.m - 1)) :
    (rawRegroupBackward p x).1.1 b i = (x.2 i).1 b := rfl

/-- The inverse restores the original raw `J` scalar. -/
theorem rawRegroup_inverse_coordinatorJ (p : Parameters)
    (x : RawProfile p) : (rawRegroupBackward p x).1.2 = x.1.1 := rfl

/-- The inverse restores the original target-scalar array. -/
theorem rawRegroup_inverse_targets (p : Parameters)
    (x : RawProfile p) : (rawRegroupBackward p x).2.2 = x.1.2.2 := rfl

/-- The inverse restores the coordinator's complete round stream. -/
theorem rawRegroup_inverse_coordinatorRound (p : Parameters)
    (x : RawProfile p) (t : Fin p.T) :
    (rawRegroupBackward p x).2.1 (coordinatorPlayer p, t) = x.1.2.1 t := by
  simp [rawRegroupBackward, coordinatorPlayer]

/-- The inverse restores the complete round stream of every follower. -/
theorem rawRegroup_inverse_followerRound (p : Parameters)
    (x : RawProfile p) (i : Fin (p.m - 1)) (t : Fin p.T) :
    (rawRegroupBackward p x).2.1 (followerPlayer p i, t) = (x.2 i).2 t := by
  simp only [rawRegroupBackward]
  have hneq : followerPlayer p i ≠ coordinatorPlayer p :=
    (coordinatorPlayer_ne_followerPlayer p i).symm
  simp only [dite_eq_right hneq]
  rw [followerSlotOfPlayer_followerPlayer]

/-- Independent product law of one original player-round scalar stream. -/
def roundStreamLaw (p : Parameters) : Measure (Fin p.T → Scalar) :=
  Measure.pi (fun _ : Fin p.T => ContinuousCategorical.uniform)

instance roundStreamLaw_probability (p : Parameters) :
    IsProbabilityMeasure (roundStreamLaw p) := by
  change IsProbabilityMeasure
    (Measure.pi (fun _ : Fin p.T => ContinuousCategorical.uniform))
  infer_instance

/-- Independent product law of one follower's original block triples. -/
def followerStreamLaw (p : Parameters) : Measure (FollowerStream p) :=
  Measure.pi (fun _ : Fin (n_boot p) => PrivateSourceStreams.blockScalarsLaw)

instance followerStreamLaw_probability (p : Parameters) :
    IsProbabilityMeasure (followerStreamLaw p) := by
  change IsProbabilityMeasure
    (Measure.pi (fun _ : Fin (n_boot p) => PrivateSourceStreams.blockScalarsLaw))
  infer_instance

/-- The coordinator's literal raw law: its original `J` scalar, own round
stream, and complete target-scalar array. -/
def coordinatorRawLaw (p : Parameters) : Measure (CoordinatorRaw p) :=
  PrivateSourceStreams.coordinatorScalarLaw.prod
    ((roundStreamLaw p).prod (coordinatorTargetScalarLaw p))

instance coordinatorRawLaw_probability (p : Parameters) :
    IsProbabilityMeasure (coordinatorRawLaw p) := by
  dsimp [coordinatorRawLaw]
  infer_instance

/-- The literal product law of one follower's complete block and round
streams. -/
def followerRawLaw (p : Parameters) : Measure (FollowerRaw p) :=
  (followerStreamLaw p).prod (roundStreamLaw p)

instance followerRawLaw_probability (p : Parameters) :
    IsProbabilityMeasure (followerRawLaw p) := by
  dsimp [followerRawLaw]
  infer_instance

/-- A measurable equivalence between a flat finite product index and the
corresponding nested function carrier. -/
private def finProdCurryEquiv {r c : ℕ} {X : Type*} [MeasurableSpace X] :
    (Fin r × Fin c → X) ≃ᵐ (Fin r → Fin c → X) :=
  MeasurableEquiv.curry (Fin r) (Fin c) X

/-- Split a flat matrix of coordinates into its zero row and the remaining
rows. -/
private def zeroRowIndexEquiv (r c : ℕ) :
    Fin c ≃ {z : Fin (r + 1) × Fin c // z.1.val = 0} where
  toFun j := ⟨(0, j), rfl⟩
  invFun z := z.1.2
  left_inv _ := rfl
  right_inv z := by
    rcases z with ⟨⟨i, j⟩, hi⟩
    have hi0 : i.val = 0 := hi
    apply Subtype.ext
    apply Prod.ext
    · apply Fin.ext
      change 0 = i.val
      omega
    · rfl

/-- Reindex the nonzero rows of a flat matrix by the preceding `Fin` size. -/
private def successorRowIndexEquiv (r c : ℕ) :
    Fin r × Fin c ≃ {z : Fin (r + 1) × Fin c // z.1.val ≠ 0} where
  toFun ij := ⟨(ij.1.succ, ij.2), by simp⟩
  invFun z :=
    (⟨z.1.1.val - 1, by
      have hlt := z.1.1.isLt
      have hzero := z.2
      omega⟩, z.1.2)
  left_inv ij := by
    apply Prod.ext
    · apply Fin.ext
      change (ij.1.val + 1) - 1 = ij.1.val
      omega
    · rfl
  right_inv z := by
    rcases z with ⟨⟨i, j⟩, hi⟩
    have hzero : i.val ≠ 0 := hi
    apply Subtype.ext
    apply Prod.ext
    · apply Fin.ext
      simp only [Fin.val_succ]
      omega
    · rfl

/-- The Mathlib subtype split expressed with the literal first-row/remaining
row coordinates. -/
private def finProdSplitEquiv {r c : ℕ} {X : Type*} [MeasurableSpace X] :
    (Fin (r + 1) × Fin c → X) ≃ᵐ
      (Fin c → X) × (Fin r × Fin c → X) := by
  let pred : Fin (r + 1) × Fin c → Prop := fun z => z.1.val = 0
  let split := MeasurableEquiv.piEquivPiSubtypeProd
    (fun _ : Fin (r + 1) × Fin c => X) pred
  let first := MeasurableEquiv.piCongrLeft
    (fun _ : {z : Fin (r + 1) × Fin c // pred z} => X)
    (zeroRowIndexEquiv r c)
  let rest := MeasurableEquiv.piCongrLeft
    (fun _ : {z : Fin (r + 1) × Fin c // ¬pred z} => X)
    (successorRowIndexEquiv r c)
  exact split.trans (MeasurableEquiv.prodCongr first.symm rest.symm)

private theorem measurePreserving_finProdSplitEquiv {r c : ℕ} {X : Type*}
    [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ] :
    MeasurePreserving (finProdSplitEquiv (r := r) (c := c) (X := X))
      (Measure.pi fun _ : Fin (r + 1) × Fin c => μ)
      ((Measure.pi fun _ : Fin c => μ).prod
        (Measure.pi fun _ : Fin r × Fin c => μ)) := by
  let pred : Fin (r + 1) × Fin c → Prop := fun z => z.1.val = 0
  let hsplit := measurePreserving_piEquivPiSubtypeProd
    (fun _ : Fin (r + 1) × Fin c => μ) pred
  let first := MeasurableEquiv.piCongrLeft
    (fun _ : {z : Fin (r + 1) × Fin c // pred z} => X)
    (zeroRowIndexEquiv r c)
  let rest := MeasurableEquiv.piCongrLeft
    (fun _ : {z : Fin (r + 1) × Fin c // ¬pred z} => X)
    (successorRowIndexEquiv r c)
  let hfirst := measurePreserving_piCongrLeft
    (fun _ : {z : Fin (r + 1) × Fin c // pred z} => μ)
    (zeroRowIndexEquiv r c)
  let hrest := measurePreserving_piCongrLeft
    (fun _ : {z : Fin (r + 1) × Fin c // ¬pred z} => μ)
    (successorRowIndexEquiv r c)
  change MeasurePreserving
    ((MeasurableEquiv.piEquivPiSubtypeProd
        (fun _ : Fin (r + 1) × Fin c => X) pred).trans
      (MeasurableEquiv.prodCongr first.symm rest.symm)) _ _
  exact (MeasurePreserving.prod hfirst.symm hrest.symm).comp hsplit

private theorem measurePreserving_unique_probability
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [Unique α] [Unique β] (e : α ≃ᵐ β) (μ : Measure α) (ν : Measure β)
    (hμ : IsProbabilityMeasure μ) (hν : IsProbabilityMeasure ν) :
    MeasurePreserving e μ ν := by
  refine ⟨e.measurable, ?_⟩
  apply Measure.ext
  intro s hs
  by_cases h : (default : β) ∈ s
  · have hset : s = Set.univ := by
      ext y
      constructor
      · intro _
        simp
      · intro _
        have hy : y = (default : β) := Subsingleton.elim _ _
        simpa [hy] using h
    rw [hset, Measure.map_apply e.measurable MeasurableSet.univ]
    simp [hμ.measure_univ, hν.measure_univ]
  · have hset : s = ∅ := by
      ext y
      constructor
      · intro hy
        have hy' : (default : β) ∈ s := by
          simpa [Subsingleton.elim y (default : β)] using hy
        exact (h hy').elim
      · simp
    rw [hset, Measure.map_apply e.measurable MeasurableSet.empty]
    simp

/-- Curry preserves the literal finite product law. The proof splits one row
with Mathlib's product-Pi equivalence, applies the induction hypothesis to
the remaining rows, and reassembles with `piFinSuccAbove`. -/
private theorem measurePreserving_finProdCurry {r c : ℕ} {X : Type*}
    [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ] [IsProbabilityMeasure μ] :
    MeasurePreserving (finProdCurryEquiv (r := r) (c := c) (X := X))
      (Measure.pi fun _ : Fin r × Fin c => μ)
      (Measure.pi fun _ : Fin r => Measure.pi fun _ : Fin c => μ) := by
  induction r with
  | zero =>
      have hsource : IsProbabilityMeasure
          (Measure.pi fun _ : Fin 0 × Fin c => μ) := by
        constructor
        rw [Measure.pi_univ]
        simp
      have htarget : IsProbabilityMeasure
          (Measure.pi fun _ : Fin 0 => Measure.pi fun _ : Fin c => μ) := by
        constructor
        rw [Measure.pi_univ]
        simp
      exact measurePreserving_unique_probability
        (finProdCurryEquiv (r := 0) (c := c) (X := X)) _ _ hsource htarget
  | succ r ih =>
      let hsplit := measurePreserving_finProdSplitEquiv (r := r) (c := c) μ
      let hrest := ih
      let hprod := MeasurePreserving.prod
        (MeasurePreserving.id (Measure.pi fun _ : Fin c => μ)) hrest
      let hjoin := (measurePreserving_piFinSuccAbove
        (fun _ : Fin (r + 1) => Measure.pi fun _ : Fin c => μ) 0).symm
      have hcomp := hjoin.comp (hprod.comp hsplit)
      convert hcomp using 1
      ext x i j
      cases i using Fin.cases with
      | zero =>
          simp [finProdCurryEquiv, finProdSplitEquiv, zeroRowIndexEquiv,
            successorRowIndexEquiv, MeasurableEquiv.piEquivPiSubtypeProd,
            MeasurableEquiv.piCongrLeft, MeasurableEquiv.prodCongr,
            MeasurableEquiv.piFinSuccAbove]
      | succ i =>
          simp [finProdCurryEquiv, finProdSplitEquiv, zeroRowIndexEquiv,
            successorRowIndexEquiv, MeasurableEquiv.piEquivPiSubtypeProd,
            MeasurableEquiv.piCongrLeft, MeasurableEquiv.prodCongr,
            MeasurableEquiv.piFinSuccAbove]

/-- Follower block triples regroup from block-major to follower-major
coordinates while retaining every complete triple. -/
private def followerBlockRegroup (p : Parameters) :
    FollowerBlockInputs p ≃ᵐ (Fin (p.m - 1) → FollowerStream p) :=
  (((finProdCurryEquiv (r := n_boot p) (c := p.m - 1)
        (X := PrivateSourceStreams.BlockScalars)).symm).trans
    ((MeasurableEquiv.piCongrLeft
        (fun _ : Fin (n_boot p) × Fin (p.m - 1) => PrivateSourceStreams.BlockScalars)
        (Equiv.prodComm (Fin (p.m - 1)) (Fin (n_boot p)))).symm)).trans
    (finProdCurryEquiv (r := p.m - 1) (c := n_boot p)
      (X := PrivateSourceStreams.BlockScalars))

private theorem followerBlockRegroup_apply (p : Parameters)
    (x : FollowerBlockInputs p) (i : Fin (p.m - 1))
    (b : Fin (n_boot p)) :
    followerBlockRegroup p x i b = x b i := by
  simp [followerBlockRegroup, finProdCurryEquiv,
    MeasurableEquiv.curry, MeasurableEquiv.piCongrLeft,
    Equiv.piCongrLeft, Equiv.prodComm]

private theorem followerBlockRegroup_measurePreserving (p : Parameters) :
    MeasurePreserving (followerBlockRegroup p)
      (PrivateSourceStreams.followerBlockInputsLaw p)
      (Measure.pi fun _ : Fin (p.m - 1) => followerStreamLaw p) := by
  change MeasurePreserving (followerBlockRegroup p)
    (Measure.pi fun _ : Fin (n_boot p) =>
      Measure.pi fun _ : Fin (p.m - 1) => PrivateSourceStreams.blockScalarsLaw)
    (Measure.pi fun _ : Fin (p.m - 1) =>
      Measure.pi fun _ : Fin (n_boot p) => PrivateSourceStreams.blockScalarsLaw)
  have hsource := (measurePreserving_finProdCurry
    (r := n_boot p) (c := p.m - 1) PrivateSourceStreams.blockScalarsLaw).symm
  have htranspose := measurePreserving_piCongrLeft
    (fun _ : Fin (n_boot p) × Fin (p.m - 1) => PrivateSourceStreams.blockScalarsLaw)
    (Equiv.prodComm (Fin (p.m - 1)) (Fin (n_boot p)))
  have htarget := measurePreserving_finProdCurry
    (r := p.m - 1) (c := n_boot p) PrivateSourceStreams.blockScalarsLaw
  exact htarget.comp (htranspose.symm.comp hsource)

/-- Coordinator-round labels are exactly the zero-player slice of the original
player-round array. -/
private def coordinatorRoundIndexEquiv (p : Parameters) :
    Fin p.T ≃ {z : PlayerRoundLabel p // z.1 = coordinatorPlayer p} where
  toFun t := ⟨(coordinatorPlayer p, t), rfl⟩
  invFun z := z.1.2
  left_inv _ := rfl
  right_inv z := by
    apply Subtype.ext
    rcases z with ⟨⟨j, t⟩, hj⟩
    apply Prod.ext
    · exact hj.symm
    · rfl

/-- The nonzero player-round labels are exactly the follower/round pairs. -/
private def followerRoundIndexEquiv (p : Parameters) :
    Fin (p.m - 1) × Fin p.T ≃
      {z : PlayerRoundLabel p // z.1 ≠ coordinatorPlayer p} where
  toFun it := ⟨(followerPlayer p it.1, it.2),
    (coordinatorPlayer_ne_followerPlayer p it.1).symm⟩
  invFun z := (followerSlotOfPlayer p z.1.1 z.2, z.1.2)
  left_inv it := by
    apply Prod.ext
    · exact followerSlotOfPlayer_followerPlayer p it.1
    · rfl
  right_inv z := by
    apply Subtype.ext
    rcases z with ⟨⟨j, t⟩, hj⟩
    apply Prod.ext
    · exact followerPlayer_followerSlotOfPlayer p j hj
    · rfl

/-- Split the original player-round array into the coordinator row and the
remaining flat follower/round array. -/
private def roundCoordinateSplit (p : Parameters) :
    PlayerRoundScalars p ≃ᵐ
      (Fin p.T → Scalar) × (Fin (p.m - 1) × Fin p.T → Scalar) := by
  let pred : PlayerRoundLabel p → Prop := fun z => z.1 = coordinatorPlayer p
  let split := MeasurableEquiv.piEquivPiSubtypeProd
    (fun _ : PlayerRoundLabel p => Scalar) pred
  let first := MeasurableEquiv.piCongrLeft
    (fun _ : {z : PlayerRoundLabel p // pred z} => Scalar)
    (coordinatorRoundIndexEquiv p)
  let rest := MeasurableEquiv.piCongrLeft
    (fun _ : {z : PlayerRoundLabel p // ¬pred z} => Scalar)
    (followerRoundIndexEquiv p)
  exact split.trans (MeasurableEquiv.prodCongr first.symm rest.symm)

/-- The full round-array rearrangement, with one product stream per player. -/
private def roundArrayRegroup (p : Parameters) :
    PlayerRoundScalars p ≃ᵐ
      (Fin p.T → Scalar) × (Fin (p.m - 1) → Fin p.T → Scalar) :=
  (roundCoordinateSplit p).trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _)
      (finProdCurryEquiv (r := p.m - 1) (c := p.T) (X := Scalar)))

private theorem roundArrayRegroup_apply (p : Parameters)
    (x : PlayerRoundScalars p) :
    roundArrayRegroup p x =
      ((fun t => x (coordinatorPlayer p, t)),
        fun i t => x (followerPlayer p i, t)) := by
  apply Prod.ext
  · funext t
    simp [roundArrayRegroup, roundCoordinateSplit, MeasurableEquiv.prodCongr,
      MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd,
      MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft, Equiv.piCongrLeft',
      coordinatorRoundIndexEquiv]
  · funext i t
    simp [roundArrayRegroup, roundCoordinateSplit, MeasurableEquiv.prodCongr,
      MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd,
      MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft, Equiv.piCongrLeft',
      coordinatorRoundIndexEquiv, followerRoundIndexEquiv,
      finProdCurryEquiv, MeasurableEquiv.curry, Equiv.curry]

private theorem roundArrayRegroup_measurePreserving (p : Parameters) :
    MeasurePreserving (roundArrayRegroup p) (playerRoundScalarLaw p)
      ((roundStreamLaw p).prod
        (Measure.pi fun _ : Fin (p.m - 1) => roundStreamLaw p)) := by
  change MeasurePreserving (roundArrayRegroup p)
    (Measure.pi fun _ : PlayerRoundLabel p => ContinuousCategorical.uniform)
    ((Measure.pi fun _ : Fin p.T => ContinuousCategorical.uniform).prod
      (Measure.pi fun _ : Fin (p.m - 1) =>
        Measure.pi fun _ : Fin p.T => ContinuousCategorical.uniform))
  let pred : PlayerRoundLabel p → Prop := fun z => z.1 = coordinatorPlayer p
  let hsplit := measurePreserving_piEquivPiSubtypeProd
    (fun _ : PlayerRoundLabel p => ContinuousCategorical.uniform) pred
  let hfirst := measurePreserving_piCongrLeft
    (fun _ : {z : PlayerRoundLabel p // pred z} => ContinuousCategorical.uniform)
    (coordinatorRoundIndexEquiv p)
  let hrest := measurePreserving_piCongrLeft
    (fun _ : {z : PlayerRoundLabel p // ¬pred z} => ContinuousCategorical.uniform)
    (followerRoundIndexEquiv p)
  let hcurry := measurePreserving_finProdCurry
    (r := p.m - 1) (c := p.T) ContinuousCategorical.uniform
  exact (MeasurePreserving.prod hfirst.symm (hcurry.comp hrest.symm)).comp hsplit

private abbrev FollowerBlockProfile (p : Parameters) :=
  Fin (p.m - 1) → FollowerStream p

private abbrev FollowerRoundProfile (p : Parameters) :=
  Fin (p.m - 1) → Fin p.T → Scalar

private abbrev CoordinatorRounds (p : Parameters) := Fin p.T → Scalar

/-- Reassociate and permute the five independent factor groups into the
coordinator block and the paired follower block/round views. -/
private def factorArrange (p : Parameters) :
    ((FollowerBlockProfile p × Scalar) ×
      ((CoordinatorRounds p × FollowerRoundProfile p) ×
        CoordinatorTargetScalars p)) ≃ᵐ
    ((Scalar × (CoordinatorRounds p × CoordinatorTargetScalars p)) ×
      (FollowerBlockProfile p × FollowerRoundProfile p)) := by
  let F := FollowerBlockProfile p
  let J := Scalar
  let C := CoordinatorRounds p
  let R := FollowerRoundProfile p
  let T := CoordinatorTargetScalars p
  let e₁ : ((F × J) × ((C × R) × T)) ≃ᵐ F × (J × ((C × R) × T)) :=
    MeasurableEquiv.prodAssoc
  let e₂ : (F × (J × ((C × R) × T))) ≃ᵐ
      F × (J × (C × (R × T))) :=
    MeasurableEquiv.prodCongr (MeasurableEquiv.refl _)
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _)
        MeasurableEquiv.prodAssoc)
  let e₃ : (F × (J × (C × (R × T)))) ≃ᵐ
      (J × (C × (R × T))) × F := MeasurableEquiv.prodComm
  let e₄ : ((J × (C × (R × T))) × F) ≃ᵐ
      ((J × (C × (T × R))) × F) :=
    MeasurableEquiv.prodCongr
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _)
        (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _)
          MeasurableEquiv.prodComm))
      (MeasurableEquiv.refl _)
  let e₅ : ((J × (C × (T × R))) × F) ≃ᵐ
      J × ((C × (T × R)) × F) := MeasurableEquiv.prodAssoc
  let e₆ : (J × ((C × (T × R)) × F)) ≃ᵐ
      J × (C × ((T × R) × F)) :=
    MeasurableEquiv.prodCongr (MeasurableEquiv.refl _)
      MeasurableEquiv.prodAssoc
  let e₇ : (J × (C × ((T × R) × F))) ≃ᵐ
      J × (C × (T × (R × F))) :=
    MeasurableEquiv.prodCongr (MeasurableEquiv.refl _)
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _)
        MeasurableEquiv.prodAssoc)
  let e₈ : (J × (C × (T × (R × F)))) ≃ᵐ
      J × (C × (T × (F × R))) :=
    MeasurableEquiv.prodCongr (MeasurableEquiv.refl _)
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _)
        (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _)
          MeasurableEquiv.prodComm))
  let e₉ : (J × (C × (T × (F × R)))) ≃ᵐ
      J × ((C × T) × (F × R)) :=
    MeasurableEquiv.prodCongr (MeasurableEquiv.refl _)
      MeasurableEquiv.prodAssoc.symm
  let e₁₀ : (J × ((C × T) × (F × R))) ≃ᵐ
      ((J × (C × T)) × (F × R)) :=
    MeasurableEquiv.prodAssoc.symm
  exact e₁.trans (e₂.trans (e₃.trans (e₄.trans
    (e₅.trans (e₆.trans (e₇.trans (e₈.trans (e₉.trans e₁₀))))))))

private theorem factorArrange_apply (p : Parameters)
    (x : ((FollowerBlockProfile p × Scalar) ×
      ((CoordinatorRounds p × FollowerRoundProfile p) ×
        CoordinatorTargetScalars p))) :
    factorArrange p x =
      ((x.1.2, (x.2.1.1, x.2.2)), (x.1.1, x.2.1.2)) := by
  rfl

private theorem measurePreserving_prodComm {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν] :
    MeasurePreserving (MeasurableEquiv.prodComm) (μ.prod ν) (ν.prod μ) := by
  simpa [MeasurableEquiv.prodComm] using
    (Measure.measurePreserving_swap (μ := μ) (ν := ν))

/-- The five-factor rearrangement preserves the full nested product law. -/
private theorem factorArrange_measurePreserving (p : Parameters)
    (μF : Measure (FollowerBlockProfile p)) (μJ : Measure Scalar)
    (μC : Measure (CoordinatorRounds p)) (μR : Measure (FollowerRoundProfile p))
    (μT : Measure (CoordinatorTargetScalars p))
    [SFinite μF] [SFinite μJ] [SFinite μC] [SFinite μR] [SFinite μT] :
    MeasurePreserving (factorArrange p)
      ((μF.prod μJ).prod ((μC.prod μR).prod μT))
      ((μJ.prod (μC.prod μT)).prod (μF.prod μR)) := by
  let F := FollowerBlockProfile p
  let J := Scalar
  let C := CoordinatorRounds p
  let R := FollowerRoundProfile p
  let T := CoordinatorTargetScalars p
  let μF' := μF
  let μJ' := μJ
  let μC' := μC
  let μR' := μR
  let μT' := μT
  let h₁ := measurePreserving_prodAssoc μF' μJ' ((μC'.prod μR').prod μT')
  let h₂ := MeasurePreserving.prod (MeasurePreserving.id μF')
    (MeasurePreserving.prod (MeasurePreserving.id μJ')
      (measurePreserving_prodAssoc μC' μR' μT'))
  let h₃ := measurePreserving_prodComm μF' (μJ'.prod (μC'.prod (μR'.prod μT')))
  let h₄ := MeasurePreserving.prod
    (MeasurePreserving.prod (MeasurePreserving.id μJ')
      (MeasurePreserving.prod (MeasurePreserving.id μC')
        (measurePreserving_prodComm μR' μT')))
    (MeasurePreserving.id μF')
  let h₅ := measurePreserving_prodAssoc μJ' (μC'.prod (μT'.prod μR')) μF'
  let h₆ := MeasurePreserving.prod (MeasurePreserving.id μJ')
    (measurePreserving_prodAssoc μC' (μT'.prod μR') μF')
  let h₇ := MeasurePreserving.prod (MeasurePreserving.id μJ')
    (MeasurePreserving.prod (MeasurePreserving.id μC')
      (measurePreserving_prodAssoc μT' μR' μF'))
  let h₈ := MeasurePreserving.prod (MeasurePreserving.id μJ')
    (MeasurePreserving.prod (MeasurePreserving.id μC')
      (MeasurePreserving.prod (MeasurePreserving.id μT')
        (measurePreserving_prodComm μR' μF')))
  let h₉ := MeasurePreserving.prod (MeasurePreserving.id μJ')
    (measurePreserving_prodAssoc μC' μT' (μF'.prod μR')).symm
  let h₁₀ := (measurePreserving_prodAssoc μJ' (μC'.prod μT') (μF'.prod μR')).symm
  change MeasurePreserving (factorArrange p)
    ((μF'.prod μJ').prod ((μC'.prod μR').prod μT'))
    ((μJ'.prod (μC'.prod μT')).prod (μF'.prod μR'))
  have hcomp := h₁₀.comp (h₉.comp (h₈.comp (h₇.comp (h₆.comp
    (h₅.comp (h₄.comp (h₃.comp (h₂.comp h₁))))))))
  refine ⟨(factorArrange p).measurable, ?_⟩
  convert hcomp.map_eq using 1
  all_goals congr 1

/-- Interleave each follower's independently regrouped block and round
coordinates into that follower's complete raw view. -/
private def followerPairInterleave (p : Parameters) :
    (FollowerBlockProfile p × FollowerRoundProfile p) ≃ᵐ
      (Fin (p.m - 1) → FollowerRaw p) :=
  (MeasurableEquiv.arrowProdEquivProdArrow
    (FollowerStream p) (Fin p.T → Scalar) (Fin (p.m - 1))).symm

private theorem followerPairInterleave_apply (p : Parameters)
    (x : FollowerBlockProfile p × FollowerRoundProfile p)
    (i : Fin (p.m - 1)) :
    followerPairInterleave p x i = (x.1 i, x.2 i) := by
  rfl

private theorem followerPairInterleave_measurePreserving (p : Parameters) :
    MeasurePreserving (followerPairInterleave p)
      ((Measure.pi fun _ : Fin (p.m - 1) => followerStreamLaw p).prod
        (Measure.pi fun _ : Fin (p.m - 1) => roundStreamLaw p))
      (Measure.pi fun _ : Fin (p.m - 1) => followerRawLaw p) := by
  change MeasurePreserving (followerPairInterleave p)
    ((Measure.pi fun i : Fin (p.m - 1) => followerStreamLaw p).prod
      (Measure.pi fun i : Fin (p.m - 1) => roundStreamLaw p))
    (Measure.pi fun i : Fin (p.m - 1) =>
      (followerStreamLaw p).prod (roundStreamLaw p))
  exact (measurePreserving_arrowProdEquivProdArrow
    (FollowerStream p) (Fin p.T → Scalar) (Fin (p.m - 1))
    (fun _ => followerStreamLaw p) (fun _ => roundStreamLaw p)).symm

/-- First stage: regroup follower/block and player/round arrays, retaining
the independent coordinator scalar and target array. -/
private def rawSourceFactorRegroup (p : Parameters) :
    ExtendedPrivateCoordinates p ≃ᵐ
      ((FollowerBlockProfile p × Scalar) ×
        ((CoordinatorRounds p × FollowerRoundProfile p) ×
          CoordinatorTargetScalars p)) :=
  MeasurableEquiv.prodCongr
    (MeasurableEquiv.prodCongr (followerBlockRegroup p)
      (MeasurableEquiv.refl _))
    (MeasurableEquiv.prodCongr (roundArrayRegroup p)
      (MeasurableEquiv.refl _))

private theorem rawSourceFactorRegroup_apply (p : Parameters)
    (e : ExtendedPrivateCoordinates p) :
    rawSourceFactorRegroup p e =
      ((followerBlockRegroup p e.1.1, e.1.2),
        ((roundArrayRegroup p e.2.1, e.2.2))) := rfl

/-- The full transparent chain of finite product reindexings. -/
private def rawRegroupMeasureEquiv (p : Parameters) :
    ExtendedPrivateCoordinates p ≃ᵐ RawProfile p :=
  (rawSourceFactorRegroup p).trans
    ((factorArrange p).trans
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _)
        (followerPairInterleave p)))

private theorem rawRegroupMeasureEquiv_apply (p : Parameters)
    (e : ExtendedPrivateCoordinates p) :
    rawRegroupMeasureEquiv p e = rawRegroupForward p e := by
  apply Prod.ext
  · apply Prod.ext
    · rfl
    · apply Prod.ext
      · funext t
        simp [rawRegroupMeasureEquiv, rawSourceFactorRegroup_apply,
          factorArrange_apply, roundArrayRegroup_apply, rawRegroupForward,
          MeasurableEquiv.trans_apply, MeasurableEquiv.prodCongr]
      · rfl
  · funext i
    apply Prod.ext
    · funext b
      simp [rawRegroupMeasureEquiv, rawSourceFactorRegroup_apply,
        factorArrange_apply, followerPairInterleave_apply,
        followerBlockRegroup_apply, rawRegroupForward,
        MeasurableEquiv.trans_apply, MeasurableEquiv.prodCongr]
    · funext t
      simp [rawRegroupMeasureEquiv, rawSourceFactorRegroup_apply,
        factorArrange_apply, roundArrayRegroup_apply, followerPairInterleave_apply,
        rawRegroupForward, MeasurableEquiv.trans_apply, MeasurableEquiv.prodCongr]

/-- The complete original nested source law maps, by its actual product
reindexing, to independent coordinator and follower raw views. -/
theorem rawRegroup_preserves_extendedPrivateLaw (p : Parameters) :
    MeasurePreserving (rawRegroup p) (extendedPrivateLaw p)
      ((coordinatorRawLaw p).prod
        (Measure.pi fun _ : Fin (p.m - 1) => followerRawLaw p)) := by
  change MeasurePreserving (rawRegroup p)
    ((followerBlockInputsLaw p).prod coordinatorScalarLaw |>.prod
      ((playerRoundScalarLaw p).prod (coordinatorTargetScalarLaw p)))
    ((coordinatorRawLaw p).prod
      (Measure.pi fun _ : Fin (p.m - 1) => followerRawLaw p))
  let hfirst := MeasurePreserving.prod
    (MeasurePreserving.prod (followerBlockRegroup_measurePreserving p)
      (MeasurePreserving.id PrivateSourceStreams.coordinatorScalarLaw))
    (MeasurePreserving.prod (roundArrayRegroup_measurePreserving p)
      (MeasurePreserving.id (coordinatorTargetScalarLaw p)))
  let hfactor := factorArrange_measurePreserving p
    (Measure.pi fun _ : Fin (p.m - 1) => followerStreamLaw p)
    PrivateSourceStreams.coordinatorScalarLaw (roundStreamLaw p)
    (Measure.pi fun _ : Fin (p.m - 1) => roundStreamLaw p)
    (coordinatorTargetScalarLaw p)
  let hinterleave := MeasurePreserving.prod (MeasurePreserving.id (coordinatorRawLaw p))
    (followerPairInterleave_measurePreserving p)
  have hchain := hinterleave.comp (hfactor.comp hfirst)
  have hfun : (rawRegroupMeasureEquiv p : ExtendedPrivateCoordinates p → RawProfile p) =
      rawRegroup p := by
    funext e
    simpa [rawRegroup] using rawRegroupMeasureEquiv_apply p e
  change MeasurePreserving (rawRegroupMeasureEquiv p) _ _ at hchain
  rw [hfun] at hchain
  exact hchain

/-- The common role-tagged private carrier for the local profile endpoint. -/
abbrev RawPlayerPrivateInput (p : Parameters) := CoordinatorRaw p ⊕ FollowerRaw p

/-- The coordinator's raw law and each follower's raw law, tagged by their
fixed source role. -/
def rawPlayerPrivateLaw (p : Parameters) (j : Fin p.m) :
    Measure (RawPlayerPrivateInput p) :=
  if j = coordinatorPlayer p then
    (coordinatorRawLaw p).map Sum.inl
  else (followerRawLaw p).map Sum.inr

theorem rawPlayerPrivateLaw_coordinator (p : Parameters) :
    rawPlayerPrivateLaw p (coordinatorPlayer p) =
      (coordinatorRawLaw p).map Sum.inl := by
  simp [rawPlayerPrivateLaw]

theorem rawPlayerPrivateLaw_follower (p : Parameters)
    (i : Fin (p.m - 1)) :
    rawPlayerPrivateLaw p (followerPlayer p i) =
      (followerRawLaw p).map Sum.inr := by
  simp [rawPlayerPrivateLaw,
    (coordinatorPlayer_ne_followerPlayer p i).symm]

instance rawPlayerPrivateLaw_probability (p : Parameters) (j : Fin p.m) :
    IsProbabilityMeasure (rawPlayerPrivateLaw p j) := by
  by_cases h : j = coordinatorPlayer p
  · rw [rawPlayerPrivateLaw, ite_eq_left h]
    infer_instance
  · rw [rawPlayerPrivateLaw, ite_eq_right h]
    infer_instance

/-- The all-player raw profile, using label zero for the coordinator and
labels `i.val + 1` for the followers. -/
def rawPlayerPrivateProfile (p : Parameters) (x : RawProfile p) :
    Fin p.m → RawPlayerPrivateInput p :=
  fun j => if h : j = coordinatorPlayer p then Sum.inl x.1
    else Sum.inr (x.2 (followerSlotOfPlayer p j h))

theorem rawPlayerPrivateProfile_coordinator (p : Parameters)
    (x : RawProfile p) :
    rawPlayerPrivateProfile p x (coordinatorPlayer p) = Sum.inl x.1 := by
  simp [rawPlayerPrivateProfile]

theorem rawPlayerPrivateProfile_follower (p : Parameters)
    (x : RawProfile p) (i : Fin (p.m - 1)) :
    rawPlayerPrivateProfile p x (followerPlayer p i) = Sum.inr (x.2 i) := by
  simp [rawPlayerPrivateProfile,
    (coordinatorPlayer_ne_followerPlayer p i).symm,
    followerSlotOfPlayer_followerPlayer]

theorem measurable_rawPlayerPrivateProfile (p : Parameters) :
    Measurable (rawPlayerPrivateProfile p) := by
  classical
  rw [measurable_pi_iff]
  intro j
  by_cases h : j = coordinatorPlayer p
  · subst j
    have hinl : Measurable
        (Sum.inl : CoordinatorRaw p → RawPlayerPrivateInput p) := measurable_inl
    change Measurable (fun x : RawProfile p => (Sum.inl x.1 : RawPlayerPrivateInput p))
    exact hinl.comp measurable_fst
  · simp only [rawPlayerPrivateProfile, dite_eq_right h]
    change Measurable (fun x : RawProfile p =>
      (Sum.inr (x.2 (followerSlotOfPlayer p j h)) : RawPlayerPrivateInput p))
    exact measurable_inr.comp
      ((measurable_pi_apply (followerSlotOfPlayer p j h)).comp measurable_snd)

private def coordinatorPlayerPredicate (p : Parameters) (j : Fin p.m) : Prop :=
  j = coordinatorPlayer p

@[instance_reducible] private instance coordinatorPlayerSubtypeUnique (p : Parameters) :
    Unique {j : Fin p.m // coordinatorPlayerPredicate p j} where
  default := ⟨coordinatorPlayer p, rfl⟩
  uniq j := by
    apply Subtype.ext
    exact j.2

private def followerPlayerIndexEquiv (p : Parameters) :
    Fin (p.m - 1) ≃ {j : Fin p.m // ¬ coordinatorPlayerPredicate p j} where
  toFun i := ⟨followerPlayer p i, by
    simpa [coordinatorPlayerPredicate] using
      (coordinatorPlayer_ne_followerPlayer p i).symm⟩
  invFun j := followerSlotOfPlayer p j.1 j.2
  left_inv i := followerSlotOfPlayer_followerPlayer p i
  right_inv j := by
    apply Subtype.ext
    exact followerPlayer_followerSlotOfPlayer p j.1 j.2

/-- Split an arbitrary tagged player profile at the coordinator label. This
is only a reindexing of the complete profile space; the raw inverse remains
typed by `RawProfile`. -/
private def rawPlayerProfileSplit (p : Parameters) :
    (Fin p.m → RawPlayerPrivateInput p) ≃ᵐ
      RawPlayerPrivateInput p × (Fin (p.m - 1) → RawPlayerPrivateInput p) := by
  classical
  let pred : Fin p.m → Prop := coordinatorPlayerPredicate p
  let split := MeasurableEquiv.piEquivPiSubtypeProd
    (fun _ : Fin p.m => RawPlayerPrivateInput p) pred
  let first := MeasurableEquiv.piUnique
    (fun _ : {j : Fin p.m // coordinatorPlayerPredicate p j} => RawPlayerPrivateInput p)
  let rest := MeasurableEquiv.piCongrLeft
    (fun _ : Fin (p.m - 1) => RawPlayerPrivateInput p)
    (followerPlayerIndexEquiv p).symm
  exact split.trans (MeasurableEquiv.prodCongr first rest)

private theorem rawPlayerProfileSplit_measurePreserving (p : Parameters) :
    MeasurePreserving (rawPlayerProfileSplit p)
      (Measure.pi (rawPlayerPrivateLaw p))
      (((coordinatorRawLaw p).map Sum.inl).prod
        (Measure.pi fun _ : Fin (p.m - 1) => (followerRawLaw p).map Sum.inr)) := by
  classical
  let pred : Fin p.m → Prop := coordinatorPlayerPredicate p
  let hsplit := measurePreserving_piEquivPiSubtypeProd
    (fun j : Fin p.m => rawPlayerPrivateLaw p j) pred
  let hcoordCollapse := measurePreserving_piUnique
    (fun j : {j : Fin p.m // coordinatorPlayerPredicate p j} =>
      rawPlayerPrivateLaw p j.1)
  let hrestForward := measurePreserving_piCongrLeft
    (fun j : Fin (p.m - 1) => rawPlayerPrivateLaw p (followerPlayer p j))
    (followerPlayerIndexEquiv p).symm
  have hcoord : MeasurePreserving
      (MeasurableEquiv.piUnique
      (fun _ : {j : Fin p.m // coordinatorPlayerPredicate p j} => RawPlayerPrivateInput p))
      (Measure.pi fun j : {j : Fin p.m // coordinatorPlayerPredicate p j} =>
        rawPlayerPrivateLaw p j.1)
      ((coordinatorRawLaw p).map Sum.inl) := by
    have hdefault :
        (default : {j : Fin p.m // coordinatorPlayerPredicate p j}).1 =
          coordinatorPlayer p := by
      change (coordinatorPlayerSubtypeUnique p).default.1 = coordinatorPlayer p
      rfl
    simpa [hdefault, rawPlayerPrivateLaw_coordinator] using hcoordCollapse
  have hrestFinal : MeasurePreserving
      (MeasurableEquiv.piCongrLeft
        (fun _ : Fin (p.m - 1) => RawPlayerPrivateInput p)
        (followerPlayerIndexEquiv p).symm)
      (Measure.pi fun j : {j : Fin p.m // ¬ coordinatorPlayerPredicate p j} =>
        rawPlayerPrivateLaw p j.1)
      (Measure.pi fun i : Fin (p.m - 1) => (followerRawLaw p).map Sum.inr) := by
    convert hrestForward using 1
    · congr 1
      funext j
      have hne : j.1 ≠ coordinatorPlayer p := by
        simpa [coordinatorPlayerPredicate] using j.2
      change rawPlayerPrivateLaw p j.1 =
        rawPlayerPrivateLaw p (followerPlayer p (followerSlotOfPlayer p j.1 hne))
      rw [followerPlayer_followerSlotOfPlayer]
    · congr 1
  have hsplitFinal := MeasurePreserving.prod hcoord hrestFinal
  convert hsplitFinal.comp hsplit using 1
  all_goals congr 1

private theorem rawPlayerProfileSplit_fst (p : Parameters)
    (f : Fin p.m → RawPlayerPrivateInput p) :
    (rawPlayerProfileSplit p f).1 = f (coordinatorPlayer p) := by
  classical
  have hdefault :
      (default : {j : Fin p.m // coordinatorPlayerPredicate p j}).1 =
        coordinatorPlayer p := by
    change (coordinatorPlayerSubtypeUnique p).default.1 = coordinatorPlayer p
    rfl
  change f (default : {j : Fin p.m // coordinatorPlayerPredicate p j}) =
    f (coordinatorPlayer p)
  exact congrArg f hdefault

private theorem rawPlayerProfileSplit_snd (p : Parameters)
    (f : Fin p.m → RawPlayerPrivateInput p) (i : Fin (p.m - 1)) :
    (rawPlayerProfileSplit p f).2 i = f (followerPlayer p i) := by
  classical
  change f ((followerPlayerIndexEquiv p i).1) = f (followerPlayer p i)
  rfl

private theorem rawPlayerProfileSplit_rawPlayerPrivateProfile (p : Parameters)
    (x : RawProfile p) :
    rawPlayerProfileSplit p (rawPlayerPrivateProfile p x) =
      (Sum.inl x.1, fun i => Sum.inr (x.2 i)) := by
  apply Prod.ext
  · rw [rawPlayerProfileSplit_fst, rawPlayerPrivateProfile_coordinator]
  · funext i
    rw [rawPlayerProfileSplit_snd, rawPlayerPrivateProfile_follower]

/-- Pushing the full raw product through the role-tagged profile map gives
exactly the independent local private profile law. -/
theorem rawPlayerPrivateProfile_map_rawProduct (p : Parameters) :
    Measure.map (rawPlayerPrivateProfile p)
      ((coordinatorRawLaw p).prod
        (Measure.pi fun _ : Fin (p.m - 1) => followerRawLaw p)) =
      MeasurableLocalRollout.privateProfileLaw (rawPlayerPrivateLaw p) := by
  let source := (coordinatorRawLaw p).prod
    (Measure.pi fun _ : Fin (p.m - 1) => followerRawLaw p)
  let pairMap : CoordinatorRaw p × (Fin (p.m - 1) → FollowerRaw p) →
      RawPlayerPrivateInput p × (Fin (p.m - 1) → RawPlayerPrivateInput p) :=
    fun x => (Sum.inl x.1, fun i => Sum.inr (x.2 i))
  have hinl : Measurable
      (Sum.inl : CoordinatorRaw p → RawPlayerPrivateInput p) := measurable_inl
  have hinr : Measurable
      (Sum.inr : FollowerRaw p → RawPlayerPrivateInput p) := measurable_inr
  have hpairMap : Measurable pairMap := by
    exact (hinl.comp measurable_fst).prodMk
      (measurable_pi_iff.mpr fun i =>
        hinr.comp ((measurable_pi_apply i).comp measurable_snd))
  have hpairLaw : Measure.map pairMap source =
      (((coordinatorRawLaw p).map Sum.inl).prod
        (Measure.pi fun _ : Fin (p.m - 1) => (followerRawLaw p).map Sum.inr)) := by
    let followerTagMap : (Fin (p.m - 1) → FollowerRaw p) →
        (Fin (p.m - 1) → RawPlayerPrivateInput p) :=
      fun f i => Sum.inr (f i)
    have hfollower : Measurable followerTagMap :=
      measurable_pi_iff.mpr fun i => hinr.comp (measurable_pi_apply i)
    have hpi := Measure.pi_map_pi
      (μ := fun _ : Fin (p.m - 1) => followerRawLaw p)
      (f := fun _ : Fin (p.m - 1) => (Sum.inr : FollowerRaw p → RawPlayerPrivateInput p))
      (fun _ => hinr.aemeasurable)
    calc
      Measure.map pairMap source =
          Measure.map (Prod.map Sum.inl followerTagMap) source := rfl
      _ = ((coordinatorRawLaw p).map Sum.inl).prod
          (Measure.map followerTagMap
            (Measure.pi fun _ : Fin (p.m - 1) => followerRawLaw p)) :=
        (Measure.map_prod_map _ _
          hinl hfollower).symm
      _ = ((coordinatorRawLaw p).map Sum.inl).prod
          (Measure.pi fun _ : Fin (p.m - 1) => (followerRawLaw p).map Sum.inr) := by
        rw [hpi]
  have hsplit := (rawPlayerProfileSplit_measurePreserving p).map_eq
  apply MeasurableEquiv.map_measurableEquiv_injective (rawPlayerProfileSplit p)
  calc
    (Measure.map (rawPlayerPrivateProfile p) source).map (rawPlayerProfileSplit p) =
        Measure.map pairMap source := by
          rw [Measure.map_map (rawPlayerProfileSplit p).measurable
            (measurable_rawPlayerPrivateProfile p)]
          have hfun : rawPlayerProfileSplit p ∘ rawPlayerPrivateProfile p = pairMap := by
            funext x
            exact rawPlayerProfileSplit_rawPlayerPrivateProfile p x
          rw [hfun]
    _ = (((coordinatorRawLaw p).map Sum.inl).prod
        (Measure.pi fun _ : Fin (p.m - 1) => (followerRawLaw p).map Sum.inr)) := hpairLaw
    _ = (MeasurableLocalRollout.privateProfileLaw (rawPlayerPrivateLaw p)).map
        (rawPlayerProfileSplit p) := by
          simpa [MeasurableLocalRollout.privateProfileLaw] using hsplit.symm

/-- The actual all-player private profile read from the original extended
coordinates, retaining their full raw contents. -/
def extendedRawPlayerPrivateProfile (p : Parameters)
    (e : ExtendedPrivateCoordinates p) : Fin p.m → RawPlayerPrivateInput p :=
  rawPlayerPrivateProfile p (rawRegroup p e)

theorem measurable_extendedRawPlayerPrivateProfile (p : Parameters) :
    Measurable (extendedRawPlayerPrivateProfile p) := by
  exact (measurable_rawPlayerPrivateProfile p).comp (rawRegroup p).measurable

/-- The original extended exogenous law maps to precisely the local rollout's
player-indexed private profile law. -/
theorem extendedRawPlayerPrivateProfile_map_extendedPrivateLaw (p : Parameters) :
    Measure.map (extendedRawPlayerPrivateProfile p) (extendedPrivateLaw p) =
      MeasurableLocalRollout.privateProfileLaw (rawPlayerPrivateLaw p) := by
  change Measure.map (rawPlayerPrivateProfile p ∘ rawRegroup p) (extendedPrivateLaw p) = _
  rw [← Measure.map_map (measurable_rawPlayerPrivateProfile p) (rawRegroup p).measurable]
  rw [(rawRegroup_preserves_extendedPrivateLaw p).map_eq]
  exact rawPlayerPrivateProfile_map_rawProduct p

/-- For every fixed published output and reward matrix, the source's
fixed-public private law induces the same role-tagged local profile law. -/
theorem extendedRawPlayerPrivateProfile_map_fixedPublicPrivateLaw (p : Parameters)
    (published : CompletePublicTable.PublishedOutput p)
    (rewards : RewardMatrix p.T p.K) :
    Measure.map (extendedRawPlayerPrivateProfile p)
      (fixedPublicPrivateLaw p published rewards) =
      MeasurableLocalRollout.privateProfileLaw (rawPlayerPrivateLaw p) := by
  rw [BootstrapPrivateRoundStreams.fixedPublicPrivateLaw_eq_product p published rewards]
  change Measure.map (extendedRawPlayerPrivateProfile p) (extendedPrivateLaw p) = _
  exact extendedRawPlayerPrivateProfile_map_extendedPrivateLaw p

end Bandits.Support.PlayerPrivateCoordinateProduct

end
