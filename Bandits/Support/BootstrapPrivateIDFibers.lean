/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.BootstrapPrivateRoundStreams
public import Bandits.Support.PrivateSourceStreams
public import Bandits.Support.ContinuousCategorical
public import Bandits.Support.BootstrapDimensions
public import Bandits.Support.BootstrapPhysicalInput
public import Bandits.Support.BootstrapPhysicalBlock
public import Bandits.Support.ReferenceInitializationRun

/-!
# Original private ID-coordinate fibers

This module splits the existing extended private product at one follower's
ID scalar and the coordinator and follower round scalars of the same actual
calendar block. The inverse reconstructs every labelled scalar. It then
restricts the original uniform ID coordinate to its literal categorical
fiber and proves the unnormalized cylinder identity.

Sources: `appendix_b_communication.tex:306-308,338,357-365` and
`07_public_setup.tex:27-38,61-94`.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal

open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.ContinuousCategorical
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.BootstrapBlockConstruction
open Bandits.Support.CompletePublicTable
open Bandits.Support.ActiveRoundActions
open Bandits.Support.BootstrapPhysicalBlock
open Bandits.Support.BootstrapPhysicalInput
open Bandits.Support.ReferenceInitializationRun

namespace Bandits.Support.BootstrapPrivateIDFibers

/-- The scalar carrier already used by the accepted private streams. -/
abbrev Scalar := ContinuousCategorical.Scalar

@[expose] def coordinatorPlayer (p : Parameters) : Fin p.m := ⟨0, m_pos p⟩

/-- The actual shortened calendar block, without padding the last block. -/
abbrev BlockTime (p : Parameters) (s : Fin (n_boot p)) :=
  {t : Fin p.T // t ∈ calendarBlock p s}

abbrev FollowerProfile (p : Parameters) :=
  Fin (p.m - 1) → PrivateSourceStreams.BlockScalars

abbrev OtherBlocks (p : Parameters) (s : Fin (n_boot p)) :=
  {r : Fin (n_boot p) // r ≠ s} → FollowerProfile p

abbrev OtherFollowers (p : Parameters) (j : Fin (p.m - 1)) :=
  {k : Fin (p.m - 1) // k ≠ j} → PrivateSourceStreams.BlockScalars

abbrev OtherRoundLabels (p : Parameters) (s : Fin (n_boot p)) (i : Fin p.m) :=
  {q : PlayerRoundLabel p // ¬
    ((q.1 = coordinatorPlayer p ∧ q.2 ∈ calendarBlock p s) ∨
      (q.1 = i ∧ q.2 ∈ calendarBlock p s))}

abbrev RoundSelection (p : Parameters) (s : Fin (n_boot p)) (i : Fin p.m) :=
  {q : PlayerRoundLabel p //
    (q.1 = coordinatorPlayer p ∧ q.2 ∈ calendarBlock p s) ∨
    (q.1 = i ∧ q.2 ∈ calendarBlock p s)}

abbrev SelectedRoundCoordinates (p : Parameters) (s : Fin (n_boot p))
    (i : Fin p.m) :=
  ((BlockTime p s → Scalar) × (BlockTime p s → Scalar)) ×
    (OtherRoundLabels p s i → Scalar)

abbrev WBase (p : Parameters) (s : Fin (n_boot p)) (j : Fin (p.m - 1)) :=
  (Scalar × Scalar) × (OtherFollowers p j × OtherBlocks p s)

abbrev JRest (p : Parameters) (s : Fin (n_boot p)) (i : Fin p.m) :=
  Scalar × ((OtherRoundLabels p s i → Scalar) × CoordinatorTargetScalars p)

/-- Every original coordinate outside the three extracted local groups. -/
abbrev Complement (p : Parameters) (s : Fin (n_boot p))
    (j : Fin (p.m - 1)) (i : Fin p.m) := WBase p s j × JRest p s i

/-- The exact local factor: original ID scalar followed by the original
coordinator and follower round scalar streams on this actual block. -/
abbrev LocalCoordinates (p : Parameters) (s : Fin (n_boot p)) :=
  Scalar × ((BlockTime p s → Scalar) × (BlockTime p s → Scalar))

@[expose] noncomputable def localRoundLaw (p : Parameters) (s : Fin (n_boot p)) :
    Measure (BlockTime p s → Scalar) :=
  by
    classical
    exact Measure.pi (fun _ : BlockTime p s => ContinuousCategorical.uniform)

@[expose] noncomputable def otherFollowerLaw (p : Parameters)
    (j : Fin (p.m - 1)) : Measure (OtherFollowers p j) :=
  by
    classical
    exact Measure.pi (fun _ : {k : Fin (p.m - 1) // k ≠ j} =>
      PrivateSourceStreams.blockScalarsLaw)

@[expose] noncomputable def otherBlockLaw (p : Parameters)
    (s : Fin (n_boot p)) : Measure (OtherBlocks p s) :=
  by
    classical
    exact Measure.pi (fun _ : {r : Fin (n_boot p) // r ≠ s} =>
      PrivateSourceStreams.blockScalarProfileLaw p)

@[expose] noncomputable def otherRoundLaw (p : Parameters)
    (s : Fin (n_boot p)) (i : Fin p.m) :
    Measure (OtherRoundLabels p s i → Scalar) :=
  by
    classical
    exact Measure.pi (fun _ : OtherRoundLabels p s i => ContinuousCategorical.uniform)

@[expose] noncomputable def wBaseLaw (p : Parameters) (s : Fin (n_boot p))
    (j : Fin (p.m - 1)) : Measure (WBase p s j) :=
  (ContinuousCategorical.uniform.prod ContinuousCategorical.uniform).prod
    ((otherFollowerLaw p j).prod (otherBlockLaw p s))

@[expose] noncomputable def jRestLaw (p : Parameters) (s : Fin (n_boot p))
    (i : Fin p.m) : Measure (JRest p s i) :=
  by
    classical
    exact ContinuousCategorical.uniform.prod
      ((otherRoundLaw p s i).prod
        (BootstrapPrivateRoundStreams.coordinatorTargetScalarLaw p))

@[expose] noncomputable def complementLaw (p : Parameters) (s : Fin (n_boot p))
    (j : Fin (p.m - 1)) (i : Fin p.m) : Measure (Complement p s j i) :=
  (wBaseLaw p s j).prod (jRestLaw p s i)

@[expose] noncomputable def roundPairLaw (p : Parameters) (s : Fin (n_boot p)) :
    Measure ((BlockTime p s → Scalar) × (BlockTime p s → Scalar)) :=
  (localRoundLaw p s).prod (localRoundLaw p s)

@[expose] noncomputable def localCoordinatesLaw (p : Parameters)
    (s : Fin (n_boot p)) : Measure (LocalCoordinates p s) :=
  ContinuousCategorical.uniform.prod (roundPairLaw p s)

instance localRoundLaw_probability (p : Parameters) (s : Fin (n_boot p)) :
    IsProbabilityMeasure (localRoundLaw p s) := by
  classical
  dsimp [localRoundLaw]
  infer_instance

instance otherFollowerLaw_probability (p : Parameters) (j : Fin (p.m - 1)) :
    IsProbabilityMeasure (otherFollowerLaw p j) := by
  classical
  dsimp [otherFollowerLaw]
  infer_instance

instance otherBlockLaw_probability (p : Parameters) (s : Fin (n_boot p)) :
    IsProbabilityMeasure (otherBlockLaw p s) := by
  classical
  dsimp [otherBlockLaw]
  infer_instance

instance otherRoundLaw_probability (p : Parameters) (s : Fin (n_boot p))
    (i : Fin p.m) : IsProbabilityMeasure (otherRoundLaw p s i) := by
  classical
  dsimp [otherRoundLaw]
  infer_instance

instance roundPairLaw_probability (p : Parameters) (s : Fin (n_boot p)) :
    IsProbabilityMeasure (roundPairLaw p s) := by
  dsimp [roundPairLaw]
  infer_instance

instance wBaseLaw_probability (p : Parameters) (s : Fin (n_boot p))
    (j : Fin (p.m - 1)) : IsProbabilityMeasure (wBaseLaw p s j) := by
  dsimp [wBaseLaw]
  infer_instance

instance jRestLaw_probability (p : Parameters) (s : Fin (n_boot p))
    (i : Fin p.m) : IsProbabilityMeasure (jRestLaw p s i) := by
  dsimp [jRestLaw]
  infer_instance

instance complementLaw_probability (p : Parameters) (s : Fin (n_boot p))
    (j : Fin (p.m - 1)) (i : Fin p.m) :
    IsProbabilityMeasure (complementLaw p s j i) := by
  dsimp [complementLaw]
  infer_instance

instance localCoordinatesLaw_probability (p : Parameters) (s : Fin (n_boot p)) :
    IsProbabilityMeasure (localCoordinatesLaw p s) := by
  dsimp [localCoordinatesLaw]
  infer_instance

/-- Split one follower/block product at its actual labelled triple. -/
@[expose] def followerSplitEquiv (p : Parameters) (s : Fin (n_boot p))
    (j : Fin (p.m - 1)) :
    PrivateSourceStreams.FollowerBlockInputs p ≃ᵐ Scalar ×
      ((Scalar × Scalar) × (OtherFollowers p j × OtherBlocks p s)) := by
  classical
  let eBlock : MeasurableEquiv (PrivateSourceStreams.FollowerBlockInputs p)
      (FollowerProfile p × OtherBlocks p s) := by
    let e0 := MeasurableEquiv.piEquivPiSubtypeProd
      (fun _ : Fin (n_boot p) => FollowerProfile p) (fun r => r = s)
    letI : Unique {r : Fin (n_boot p) // r = s} :=
      ⟨⟨s, rfl⟩, fun r => Subtype.ext r.property⟩
    let e1 := MeasurableEquiv.piUnique
      (fun _ : {r : Fin (n_boot p) // r = s} => FollowerProfile p)
    exact e0.trans (e1.prodCongr (MeasurableEquiv.refl _))
  let eFollower : MeasurableEquiv (FollowerProfile p)
      (PrivateSourceStreams.BlockScalars × OtherFollowers p j) := by
    let e0 := MeasurableEquiv.piEquivPiSubtypeProd
      (fun _ : Fin (p.m - 1) => PrivateSourceStreams.BlockScalars) (fun k => k = j)
    letI : Unique {k : Fin (p.m - 1) // k = j} :=
      ⟨⟨j, rfl⟩, fun k => Subtype.ext k.property⟩
    let e1 := MeasurableEquiv.piUnique
      (fun _ : {k : Fin (p.m - 1) // k = j} => PrivateSourceStreams.BlockScalars)
    exact e0.trans (e1.prodCongr (MeasurableEquiv.refl _))
  let eTriple : MeasurableEquiv PrivateSourceStreams.BlockScalars
      (Scalar × (Scalar × Scalar)) :=
    MeasurableEquiv.prodAssoc.symm.trans MeasurableEquiv.prodComm
  exact eBlock.trans <|
    (eFollower.prodCongr (MeasurableEquiv.refl (OtherBlocks p s))).trans <|
      MeasurableEquiv.prodAssoc.trans <|
        (eTriple.prodCongr
          (MeasurableEquiv.refl (OtherFollowers p j × OtherBlocks p s))).trans <|
            MeasurableEquiv.prodAssoc

/-- The follower/block split preserves each original product marginal. -/
theorem followerSplit_measurePreserving (p : Parameters) (s : Fin (n_boot p))
    (j : Fin (p.m - 1)) :
    MeasurePreserving (followerSplitEquiv p s j)
      (PrivateSourceStreams.followerBlockInputsLaw p)
      (ContinuousCategorical.uniform.prod
        ((ContinuousCategorical.uniform.prod ContinuousCategorical.uniform).prod
          ((otherFollowerLaw p j).prod (otherBlockLaw p s)))) := by
  classical
  let μTriple := PrivateSourceStreams.blockScalarsLaw
  let μProfile := PrivateSourceStreams.blockScalarProfileLaw p
  let μOtherFollowers := otherFollowerLaw p j
  let μOtherBlocks := otherBlockLaw p s
  have : IsProbabilityMeasure μProfile := by
    dsimp [μProfile]
    infer_instance
  have : IsProbabilityMeasure μTriple := by
    dsimp [μTriple]
    infer_instance
  have : IsProbabilityMeasure μOtherFollowers := by
    dsimp [μOtherFollowers, otherFollowerLaw]
    infer_instance
  have : IsProbabilityMeasure μOtherBlocks := by
    dsimp [μOtherBlocks, otherBlockLaw]
    infer_instance
  let eBlock := MeasurableEquiv.piEquivPiSubtypeProd
    (fun _ : Fin (n_boot p) => FollowerProfile p) (fun r => r = s)
  let : Unique {r : Fin (n_boot p) // r = s} :=
    ⟨⟨s, rfl⟩, fun r => Subtype.ext r.property⟩
  let : Fintype {r : Fin (n_boot p) // r = s} :=
    Fintype.subtype (Finset.univ.filter (fun r : Fin (n_boot p) => r = s)) (by simp)
  let eBlock' := MeasurableEquiv.piUnique
    (fun _ : {r : Fin (n_boot p) // r = s} => FollowerProfile p)
  let hBlockSplit := measurePreserving_piEquivPiSubtypeProd
    (μ := fun _ : Fin (n_boot p) => μProfile)
    (fun r : Fin (n_boot p) => r = s)
  have hBlockSingleton : MeasurePreserving eBlock'
      (Measure.pi (fun _ : {r : Fin (n_boot p) // r = s} => μProfile)) μProfile :=
    measurePreserving_piUnique (fun _ : {r : Fin (n_boot p) // r = s} => μProfile)
  have hBlock : MeasurePreserving (eBlock.trans
      (eBlock'.prodCongr (MeasurableEquiv.refl _)))
      (PrivateSourceStreams.followerBlockInputsLaw p)
      (μProfile.prod μOtherBlocks) := by
    change MeasurePreserving (eBlock.trans
      (eBlock'.prodCongr (MeasurableEquiv.refl _)))
      (Measure.pi (fun _ : Fin (n_boot p) => μProfile)) _
    exact (hBlockSingleton.prod (MeasurePreserving.id μOtherBlocks)).comp hBlockSplit
  let eFollower := MeasurableEquiv.piEquivPiSubtypeProd
    (fun _ : Fin (p.m - 1) => PrivateSourceStreams.BlockScalars) (fun k => k = j)
  let : Unique {k : Fin (p.m - 1) // k = j} :=
    ⟨⟨j, rfl⟩, fun k => Subtype.ext k.property⟩
  let : Fintype {k : Fin (p.m - 1) // k = j} :=
    Fintype.subtype (Finset.univ.filter (fun k : Fin (p.m - 1) => k = j)) (by simp)
  let eFollower' := MeasurableEquiv.piUnique
    (fun _ : {k : Fin (p.m - 1) // k = j} => PrivateSourceStreams.BlockScalars)
  let hFollowerSplit := measurePreserving_piEquivPiSubtypeProd
    (μ := fun _ : Fin (p.m - 1) => μTriple)
    (fun k : Fin (p.m - 1) => k = j)
  have hFollowerSingleton : MeasurePreserving eFollower'
      (Measure.pi (fun _ : {k : Fin (p.m - 1) // k = j} => μTriple)) μTriple :=
    measurePreserving_piUnique (fun _ : {k : Fin (p.m - 1) // k = j} => μTriple)
  have hFollower : MeasurePreserving
      (eFollower.trans (eFollower'.prodCongr (MeasurableEquiv.refl _)))
      μProfile (μTriple.prod μOtherFollowers) := by
    change MeasurePreserving
      (eFollower.trans (eFollower'.prodCongr (MeasurableEquiv.refl _)))
      (Measure.pi (fun _ : Fin (p.m - 1) => μTriple)) _
    exact (hFollowerSingleton.prod (MeasurePreserving.id μOtherFollowers)).comp
      hFollowerSplit
  let eTriple : MeasurableEquiv PrivateSourceStreams.BlockScalars
      (Scalar × (Scalar × Scalar)) :=
    MeasurableEquiv.prodAssoc.symm.trans MeasurableEquiv.prodComm
  have hTripleAssoc :=
    (measurePreserving_prodAssoc ContinuousCategorical.uniform
      ContinuousCategorical.uniform ContinuousCategorical.uniform).symm
  have hTripleSwap : MeasurePreserving Prod.swap
      ((ContinuousCategorical.uniform.prod ContinuousCategorical.uniform).prod
        ContinuousCategorical.uniform)
      (ContinuousCategorical.uniform.prod
        (ContinuousCategorical.uniform.prod ContinuousCategorical.uniform)) :=
    Measure.measurePreserving_swap
  have hTriple : MeasurePreserving eTriple μTriple
      (ContinuousCategorical.uniform.prod
        (ContinuousCategorical.uniform.prod ContinuousCategorical.uniform)) := by
    change MeasurePreserving (MeasurableEquiv.prodAssoc.symm.trans
      MeasurableEquiv.prodComm) _ _
    exact hTripleSwap.comp hTripleAssoc
  have h1 := (hFollower.prod (MeasurePreserving.id μOtherBlocks)).comp hBlock
  have h2 := (measurePreserving_prodAssoc μTriple μOtherFollowers μOtherBlocks).comp h1
  have h3 := (hTriple.prod (MeasurePreserving.id (μOtherFollowers.prod μOtherBlocks))).comp h2
  have h4 := (measurePreserving_prodAssoc ContinuousCategorical.uniform
      (ContinuousCategorical.uniform.prod ContinuousCategorical.uniform)
      (μOtherFollowers.prod μOtherBlocks)).comp h3
  have hfun : followerSplitEquiv p s j =
      ((eBlock.trans (eBlock'.prodCongr (MeasurableEquiv.refl _))).trans <|
        ((eFollower.trans (eFollower'.prodCongr (MeasurableEquiv.refl _))).prodCongr
          (MeasurableEquiv.refl (OtherBlocks p s))).trans <|
            MeasurableEquiv.prodAssoc.trans <|
              (eTriple.prodCongr
                (MeasurableEquiv.refl (OtherFollowers p j × OtherBlocks p s))).trans <|
                  MeasurableEquiv.prodAssoc) := by
    rfl
  have hfunMap : (followerSplitEquiv p s j : _ → _) =
      MeasurableEquiv.prodAssoc ∘ Prod.map eTriple id ∘ MeasurableEquiv.prodAssoc ∘
        Prod.map (eFollower.trans (eFollower'.prodCongr (MeasurableEquiv.refl _))) id ∘
          (eBlock.trans (eBlock'.prodCongr (MeasurableEquiv.refl _))) := by
    rw [hfun]
    funext x
    simp [MeasurableEquiv.coe_trans, MeasurableEquiv.prodCongr,
      Equiv.prodCongr_apply]
  rw [hfunMap]
  simpa only [PrivateSourceStreams.followerBlockInputsLaw, μProfile, μTriple,
    otherFollowerLaw, otherBlockLaw, μOtherFollowers, μOtherBlocks,
    PrivateSourceStreams.FollowerBlockInputs, FollowerProfile,
    OtherFollowers, OtherBlocks, MeasurableEquiv.coe_trans,
    MeasurableEquiv.prodCongr,
    Equiv.prodCongr_apply, Equiv.prodAssoc, Equiv.prodComm_apply,
    eBlock, eBlock', eFollower, eFollower', eTriple] using h4

/-- Index equivalence for the two selected player-round streams. -/
@[expose] def roundSelectionEquiv (p : Parameters) (s : Fin (n_boot p))
    (i : Fin p.m) (hne : i ≠ coordinatorPlayer p) :
    RoundSelection p s i ≃ BlockTime p s ⊕ BlockTime p s := by
  refine
    { toFun := fun q => if hq : q.1.1 = coordinatorPlayer p then
          Sum.inl ⟨q.1.2, (q.2.resolve_right
            (fun h => hne (h.1.symm.trans hq))).2⟩
        else Sum.inr ⟨q.1.2, (q.2.resolve_left (fun h => hq h.1)).2⟩
      invFun := fun q => match q with
        | .inl t => ⟨(coordinatorPlayer p, t.1), Or.inl ⟨rfl, t.2⟩⟩
        | .inr t => ⟨(i, t.1), Or.inr ⟨rfl, t.2⟩⟩
      left_inv := by
        intro q
        apply Subtype.ext
        by_cases hq : q.1.1 = coordinatorPlayer p
        · simp only [dite_eq_left hq]
          exact Prod.ext hq.symm rfl
        · simp only [dite_eq_right hq]
          have hqi : q.1.1 = i := (q.2.resolve_left (fun h => hq h.1)).1
          exact Prod.ext hqi.symm rfl
      right_inv := by
        intro q
        cases q with
        | inl t => simp
        | inr t => simp [hne]
    }

@[expose] def roundSplitEquiv (p : Parameters) (s : Fin (n_boot p))
    (i : Fin p.m) (hne : i ≠ coordinatorPlayer p) : PlayerRoundScalars p ≃ᵐ
      ((BlockTime p s → Scalar) × (BlockTime p s → Scalar)) ×
        (OtherRoundLabels p s i → Scalar) := by
  classical
  let e0 := MeasurableEquiv.piEquivPiSubtypeProd
    (fun _ : PlayerRoundLabel p => Scalar)
    (fun q => q.1 = coordinatorPlayer p ∧ q.2 ∈ calendarBlock p s ∨
      q.1 = i ∧ q.2 ∈ calendarBlock p s)
  let e1 := MeasurableEquiv.piCongrLeft (fun _ : _ => Scalar)
    (roundSelectionEquiv p s i hne)
  exact e0.trans <| (e1.trans (MeasurableEquiv.sumPiEquivProdPi
    (fun _ : BlockTime p s ⊕ BlockTime p s => Scalar))).prodCongr
    (MeasurableEquiv.refl _)

theorem roundSplit_measurePreserving (p : Parameters) (s : Fin (n_boot p))
    (i : Fin p.m) (hne : i ≠ coordinatorPlayer p) :
    MeasurePreserving (roundSplitEquiv p s i hne)
      (BootstrapPrivateRoundStreams.playerRoundScalarLaw p)
      ((roundPairLaw p s).prod (otherRoundLaw p s i)) := by
  classical
  let μ := ContinuousCategorical.uniform
  let e0 := MeasurableEquiv.piEquivPiSubtypeProd
    (fun _ : PlayerRoundLabel p => Scalar)
    (fun q => q.1 = coordinatorPlayer p ∧ q.2 ∈ calendarBlock p s ∨
      q.1 = i ∧ q.2 ∈ calendarBlock p s)
  let e1 := MeasurableEquiv.piCongrLeft (fun _ : _ => Scalar)
    (roundSelectionEquiv p s i hne)
  have h0 : MeasurePreserving e0
      (Measure.pi (fun _ : PlayerRoundLabel p => μ))
      ((Measure.pi (fun _ : RoundSelection p s i => μ)).prod
        (otherRoundLaw p s i)) :=
    measurePreserving_piEquivPiSubtypeProd
      (fun _ : PlayerRoundLabel p => μ)
      (fun q => q.1 = coordinatorPlayer p ∧ q.2 ∈ calendarBlock p s ∨
        q.1 = i ∧ q.2 ∈ calendarBlock p s)
  have h1 : MeasurePreserving e1
      (Measure.pi (fun _ : RoundSelection p s i => μ))
      (Measure.pi (fun _ : BlockTime p s ⊕ BlockTime p s => μ)) := by
    exact measurePreserving_piCongrLeft
      (fun _ : BlockTime p s ⊕ BlockTime p s => μ)
      (roundSelectionEquiv p s i hne)
  have h2 : MeasurePreserving (MeasurableEquiv.sumPiEquivProdPi
      (fun _ : BlockTime p s ⊕ BlockTime p s => Scalar))
      (Measure.pi (fun _ : BlockTime p s ⊕ BlockTime p s => μ))
      ((localRoundLaw p s).prod (localRoundLaw p s)) := by
    simpa only [localRoundLaw] using
      (measurePreserving_sumPiEquivProdPi
        (fun _ : BlockTime p s ⊕ BlockTime p s => μ))
  have h3 := (h2.prod (MeasurePreserving.id (otherRoundLaw p s i))).comp <|
    (h1.prod (MeasurePreserving.id (otherRoundLaw p s i))).comp h0
  have hfun : roundSplitEquiv p s i hne =
      e0.trans ((e1.trans (MeasurableEquiv.sumPiEquivProdPi
        (fun _ : BlockTime p s ⊕ BlockTime p s => Scalar))).prodCongr
        (MeasurableEquiv.refl _)) := rfl
  have hfunMap : (roundSplitEquiv p s i hne : _ → _) =
      Prod.map (MeasurableEquiv.sumPiEquivProdPi
        (fun _ : BlockTime p s ⊕ BlockTime p s => Scalar)) id ∘
        Prod.map e1 id ∘ e0 := by
    rw [hfun]
    funext x
    rfl
  rw [hfunMap]
  simpa only [BootstrapPrivateRoundStreams.playerRoundScalarLaw, roundPairLaw,
    localRoundLaw, otherRoundLaw, BootstrapPrivateRoundStreams.PlayerRoundScalars,
    BootstrapPrivateRoundStreams.Scalar, Scalar, PlayerRoundLabel, μ,
    MeasurableEquiv.coe_trans, MeasurableEquiv.prodCongr,
    Equiv.prodCongr_apply] using h3

/-- Reorder the separated factors so the same local pair appears together in
the local factor, with every residual label in the complement. -/
@[expose] noncomputable def gatherEquiv {α β γ δ ε ζ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSpace δ] [MeasurableSpace ε] [MeasurableSpace ζ] :
    ((α × β) × (γ × ((δ × ε) × ζ))) ≃ᵐ
      ((β × (γ × (ε × ζ))) × (α × δ)) := by
  let eRight : γ × ((δ × ε) × ζ) ≃ᵐ (γ × (ε × ζ)) × δ := by
    exact (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _) MeasurableEquiv.prodAssoc).trans <|
      (MeasurableEquiv.prodAssoc.symm).trans <|
        (MeasurableEquiv.prodCongr MeasurableEquiv.prodComm
          (MeasurableEquiv.refl _)).trans <|
            MeasurableEquiv.prodAssoc.trans MeasurableEquiv.prodComm
  let eFinal : α × (β × ((γ × (ε × ζ)) × δ)) ≃ᵐ
      ((β × (γ × (ε × ζ))) × (α × δ)) := by
    exact MeasurableEquiv.prodAssoc.symm.trans <|
      (MeasurableEquiv.prodAssoc.trans <|
        (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _) MeasurableEquiv.prodAssoc.symm).trans <|
          (MeasurableEquiv.prodAssoc.symm.trans <|
            (MeasurableEquiv.prodCongr MeasurableEquiv.prodComm
              (MeasurableEquiv.refl _)).trans MeasurableEquiv.prodAssoc))
  exact MeasurableEquiv.prodAssoc.trans <|
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _) <|
      MeasurableEquiv.prodCongr (MeasurableEquiv.refl _) eRight).trans eFinal

theorem gather_measurePreserving {α β γ δ ε ζ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSpace δ] [MeasurableSpace ε] [MeasurableSpace ζ]
    (μα : Measure α) (μβ : Measure β) (μγ : Measure γ)
    (μδ : Measure δ) (με : Measure ε) (μζ : Measure ζ)
    [SFinite μα] [SFinite μβ] [SFinite μγ] [SFinite μδ] [SFinite με] [SFinite μζ] :
    MeasurePreserving (gatherEquiv (α := α) (β := β) (γ := γ)
      (δ := δ) (ε := ε) (ζ := ζ))
      ((μα.prod μβ).prod (μγ.prod ((μδ.prod με).prod μζ)))
      ((μβ.prod (μγ.prod (με.prod μζ))).prod (μα.prod μδ)) := by
  let μRest := με.prod μζ
  let μGammaRest := μγ.prod (μδ.prod μRest)
  have hDE := measurePreserving_prodAssoc μδ με μζ
  have hGammaAssoc := (measurePreserving_prodAssoc μγ μδ μRest).symm
  have hGammaSwap : MeasurePreserving Prod.swap (μγ.prod μδ) (μδ.prod μγ) :=
    Measure.measurePreserving_swap
  have hGammaAssoc' := measurePreserving_prodAssoc μδ μγ μRest
  have hGammaSwap' : MeasurePreserving Prod.swap
      (μδ.prod (μγ.prod μRest)) ((μγ.prod μRest).prod μδ) :=
    Measure.measurePreserving_swap
  let hPermGamma := hGammaSwap'.comp <|
    hGammaAssoc'.comp ((hGammaSwap.prod (MeasurePreserving.id μRest)).comp hGammaAssoc)
  let hRight := hPermGamma.comp ((MeasurePreserving.id μγ).prod hDE)
  have hRightAll := (MeasurePreserving.id μα).prod
    ((MeasurePreserving.id μβ).prod hRight)
  let μJRest := μγ.prod μRest
  let μBR := μβ.prod μJRest
  have h1 := measurePreserving_prodAssoc μα μβ (μJRest.prod μδ)
  have h2 := (MeasurePreserving.id μα).prod
    (measurePreserving_prodAssoc μβ μJRest μδ).symm
  have h3 := (measurePreserving_prodAssoc μα μBR μδ).symm
  have h4 : MeasurePreserving Prod.swap (μα.prod μBR) (μBR.prod μα) :=
    Measure.measurePreserving_swap
  have h5 := measurePreserving_prodAssoc μBR μα μδ
  let hPermute := h5.comp ((h4.prod (MeasurePreserving.id μδ)).comp <|
    h3.comp (h2.comp h1))
  have hBack := (measurePreserving_prodAssoc μα μβ (μJRest.prod μδ)).symm
  unfold gatherEquiv
  dsimp
  exact hPermute.comp (hBack.comp (hRightAll.comp
    (measurePreserving_prodAssoc μα μβ
      (μγ.prod ((μδ.prod με).prod μζ)))))

@[expose] def splitEquiv (p : Parameters) (s : Fin (n_boot p))
    (j : Fin (p.m - 1)) (hj : j.val + 1 < p.m) :
    ExtendedPrivateCoordinates p ≃ᵐ Complement p s j ⟨j.val + 1, hj⟩ ×
      LocalCoordinates p s := by
  classical
  let i : Fin p.m := ⟨j.val + 1, hj⟩
  have hi : i ≠ coordinatorPlayer p := by
    intro h
    have hv := congrArg Fin.val h
    simp [i, coordinatorPlayer] at hv
  let eOuter :
      ((PrivateSourceStreams.FollowerBlockInputs p × Scalar) ×
          (PlayerRoundScalars p × CoordinatorTargetScalars p)) ≃ᵐ
        PrivateSourceStreams.FollowerBlockInputs p ×
          (Scalar × (PlayerRoundScalars p × CoordinatorTargetScalars p)) :=
    MeasurableEquiv.prodAssoc
  let eFollowers := followerSplitEquiv p s j
  let eRounds := roundSplitEquiv p s i hi
  let eMid :
      ((Scalar × WBase p s j) ×
          (Scalar × (PlayerRoundScalars p × CoordinatorTargetScalars p))) ≃ᵐ
        ((Scalar × WBase p s j) ×
          (Scalar × (SelectedRoundCoordinates p s i × CoordinatorTargetScalars p))) :=
    (MeasurableEquiv.refl (Scalar × WBase p s j)).prodCongr <|
      (MeasurableEquiv.refl Scalar).prodCongr <|
        (eRounds.prodCongr (MeasurableEquiv.refl (CoordinatorTargetScalars p)))
  exact eOuter.trans <|
    (MeasurableEquiv.prodCongr eFollowers (MeasurableEquiv.refl _)).trans <|
      eMid.trans (gatherEquiv (α := Scalar) (β := WBase p s j)
        (γ := Scalar) (δ := (BlockTime p s → Scalar) × (BlockTime p s → Scalar))
        (ε := OtherRoundLabels p s i → Scalar)
        (ζ := CoordinatorTargetScalars p))

theorem split_measurePreserving (p : Parameters) (s : Fin (n_boot p))
    (j : Fin (p.m - 1)) (hj : j.val + 1 < p.m) :
    MeasurePreserving (splitEquiv p s j hj) (extendedPrivateLaw p)
      ((complementLaw p s j ⟨j.val + 1, hj⟩).prod
        (localCoordinatesLaw p s)) := by
  classical
  let i : Fin p.m := ⟨j.val + 1, hj⟩
  have hi : i ≠ coordinatorPlayer p := by
    intro h
    have hv := congrArg Fin.val h
    simp [i, coordinatorPlayer] at hv
  let μFollowers := PrivateSourceStreams.followerBlockInputsLaw p
  let μJ := PrivateSourceStreams.coordinatorScalarLaw
  let μRounds := BootstrapPrivateRoundStreams.playerRoundScalarLaw p
  let μTarget := BootstrapPrivateRoundStreams.coordinatorTargetScalarLaw p
  let μID := ContinuousCategorical.uniform
  let μActHeld := ContinuousCategorical.uniform.prod ContinuousCategorical.uniform
  let μOtherFollowers := otherFollowerLaw p j
  let μOtherBlocks := otherBlockLaw p s
  let μWBase := wBaseLaw p s j
  let μOtherRounds := otherRoundLaw p s i
  let μPair := roundPairLaw p s
  let μJRest := jRestLaw p s i
  let hOuter := measurePreserving_prodAssoc μFollowers μJ (μRounds.prod μTarget)
  have hFollowers := followerSplit_measurePreserving p s j
  have hRounds := roundSplit_measurePreserving p s i hi
  have hTargetId : MeasurePreserving id μTarget μTarget := MeasurePreserving.id _
  have hMiddle := (MeasurePreserving.id μJ).prod (hRounds.prod hTargetId)
  have hBeforeGather :=
    (((MeasurePreserving.id (μID.prod μWBase)).prod hMiddle).comp <|
      (hFollowers.prod (MeasurePreserving.id (μJ.prod (μRounds.prod μTarget)))).comp hOuter)
  have hGather := gather_measurePreserving (α := Scalar) (β := WBase p s j)
    (γ := Scalar) (δ := (BlockTime p s → Scalar) × (BlockTime p s → Scalar))
    (ε := OtherRoundLabels p s i → Scalar) (ζ := CoordinatorTargetScalars p)
    μID μWBase μJ μPair μOtherRounds μTarget
  have hFinal := hGather.comp hBeforeGather
  let eOuter :
      ((PrivateSourceStreams.FollowerBlockInputs p × Scalar) ×
          (PlayerRoundScalars p × CoordinatorTargetScalars p)) ≃ᵐ
        PrivateSourceStreams.FollowerBlockInputs p ×
          (Scalar × (PlayerRoundScalars p × CoordinatorTargetScalars p)) :=
    MeasurableEquiv.prodAssoc
  let eFollowers := followerSplitEquiv p s j
  let eRounds := roundSplitEquiv p s i hi
  let eMid :
      ((Scalar × WBase p s j) ×
          (Scalar × (PlayerRoundScalars p × CoordinatorTargetScalars p))) ≃ᵐ
        ((Scalar × WBase p s j) ×
          (Scalar × (SelectedRoundCoordinates p s i × CoordinatorTargetScalars p))) :=
    (MeasurableEquiv.refl (Scalar × WBase p s j)).prodCongr <|
      (MeasurableEquiv.refl Scalar).prodCongr <|
        (eRounds.prodCongr (MeasurableEquiv.refl (CoordinatorTargetScalars p)))
  let eGather := gatherEquiv (α := Scalar) (β := WBase p s j)
    (γ := Scalar) (δ := (BlockTime p s → Scalar) × (BlockTime p s → Scalar))
    (ε := OtherRoundLabels p s i → Scalar) (ζ := CoordinatorTargetScalars p)
  have hfun : splitEquiv p s j hj =
      eOuter.trans ((MeasurableEquiv.prodCongr eFollowers
        (MeasurableEquiv.refl _)).trans (eMid.trans eGather)) := by
    rfl
  have hfunMap : (splitEquiv p s j hj : _ → _) =
      eGather ∘ Prod.map id (Prod.map id (Prod.map eRounds id)) ∘
        Prod.map eFollowers id ∘ eOuter := by
    rw [hfun]
    funext x
    simp [eMid, eRounds, MeasurableEquiv.prodCongr, Equiv.prodCongr_apply]
  rw [hfunMap]
  simpa only [BootstrapPrivateRoundStreams.extendedPrivateLaw,
    PrivateSourceStreams.privateCoordinatesLaw,
    BootstrapPrivateRoundStreams.extraPrivateStreamsLaw,
    BootstrapPrivateRoundStreams.playerRoundScalarLaw,
    BootstrapPrivateRoundStreams.coordinatorTargetScalarLaw,
    PrivateSourceStreams.coordinatorScalarLaw,
    complementLaw, jRestLaw, otherRoundLaw, localCoordinatesLaw, roundPairLaw,
    μFollowers, μJ,
    μRounds, μTarget, μID, μActHeld, μOtherFollowers, μOtherBlocks,
    μWBase, μOtherRounds, μPair, μJRest, MeasurableEquiv.coe_trans,
    MeasurableEquiv.prodCongr,
    Equiv.prodCongr_apply, Equiv.prodAssoc, Equiv.prodComm_apply,
    eOuter, eFollowers, eRounds, eMid, eGather] using hFinal

/-- The original ID map restricted to its exact scalar fiber. -/
@[expose] def idFiber (p : Parameters) (u : Fin (A_id p)) : Set Scalar :=
  PrivateSourceStreams.privateIDScalarDraw p ⁻¹' {u}

theorem idFiber_eq_cumulative_interval (p : Parameters) (u : Fin (A_id p)) :
    idFiber p u = Subtype.val ⁻¹'
      Set.Ico (ContinuousCategorical.lower (privateIdProbability p) u)
        (ContinuousCategorical.upper (privateIdProbability p) u) := by
  change PrivateSourceStreams.privateIDScalarDraw p ⁻¹' {u} = _
  have hdraw : PrivateSourceStreams.privateIDScalarDraw p =
      (fun v => ContinuousCategorical.sample (A_id_pos p)
        (privateIdProbability p) (privateIdProbability_sum p) v) := by
    funext v
    rfl
  rw [hdraw]
  exact ContinuousCategorical.sample_preimage_singleton
    (n := A_id p) (p := privateIdProbability p) (A_id_pos p)
    (fun _ => (one_div_pos.mpr (Nat.cast_pos.mpr (A_id_pos p))).le)
    (privateIdProbability_sum p) u

theorem measurableSet_idFiber (p : Parameters) (u : Fin (A_id p)) :
    MeasurableSet (idFiber p u) := by
  rw [idFiber_eq_cumulative_interval]
  exact measurableSet_Ico.preimage measurable_subtype_coe

theorem idFiber_mass (p : Parameters) (u : Fin (A_id p)) :
    ContinuousCategorical.uniform (idFiber p u) =
      ENNReal.ofReal (1 / (A_id p : ℝ)) := by
  rw [idFiber, PrivateSourceStreams.privateIDScalarDraw_uniform_atom]
  simp [privateIdProbability]

theorem idFiber_mass_pos (p : Parameters) (u : Fin (A_id p)) :
    0 < ContinuousCategorical.uniform (idFiber p u) := by
  rw [idFiber_mass]
  exact ENNReal.ofReal_pos.mpr (one_div_pos.mpr (Nat.cast_pos.mpr (A_id_pos p)))

@[expose] noncomputable def normalizedFiberLaw (p : Parameters)
    (u : Fin (A_id p)) : Measure Scalar :=
  (ContinuousCategorical.uniform (idFiber p u))⁻¹ •
    ContinuousCategorical.uniform.restrict (idFiber p u)

theorem normalizedFiberLaw_isProbabilityMeasure (p : Parameters)
    (u : Fin (A_id p)) : IsProbabilityMeasure (normalizedFiberLaw p u) := by
  refine ⟨?_⟩
  rw [normalizedFiberLaw, Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply' (measurableSet_idFiber p u), Set.univ_inter,
    idFiber_mass]
  exact ENNReal.inv_mul_cancel
    (ne_of_gt (ENNReal.ofReal_pos.mpr
      (one_div_pos.mpr (Nat.cast_pos.mpr (A_id_pos p))))) (by simp)

theorem normalizedFiberLaw_map_id (p : Parameters) (u : Fin (A_id p)) :
    (normalizedFiberLaw p u).map (PrivateSourceStreams.privateIDScalarDraw p) =
      Measure.dirac u := by
  classical
  apply Measure.ext
  intro S hS
  rw [Measure.map_apply (PrivateSourceStreams.measurable_privateIDScalarDraw p) hS]
  have hpre :
      (PrivateSourceStreams.privateIDScalarDraw p ⁻¹' S) ∩ idFiber p u =
        if u ∈ S then idFiber p u else ∅ := by
    ext v
    by_cases hv : PrivateSourceStreams.privateIDScalarDraw p v = u
    · simp [idFiber, hv]
    · simp [idFiber, hv]
  rw [normalizedFiberLaw, Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply' (measurableSet_idFiber p u), hpre]
  by_cases hu : u ∈ S
  · rw [ite_eq_left hu, idFiber_mass]
    have hne : ENNReal.ofReal (1 / (A_id p : ℝ)) ≠ 0 :=
      ne_of_gt (ENNReal.ofReal_pos.mpr
        (one_div_pos.mpr (Nat.cast_pos.mpr (A_id_pos p))))
    have htop : ENNReal.ofReal (1 / (A_id p : ℝ)) ≠ ⊤ := by simp
    simpa [hu] using (ENNReal.inv_mul_cancel hne htop)
  · rw [ite_eq_right hu, measure_empty, mul_zero]
    simp [hu]

/-- The raw ID fiber has exactly the uniform categorical mass, including the
actual continuous scalar coordinate rather than a substituted private ID. -/
theorem idFiber_mass_eq_uniform_atom (p : Parameters) (u : Fin (A_id p)) :
    ContinuousCategorical.uniform (idFiber p u) =
      ENNReal.ofReal (privateIdProbability p u) :=
  PrivateSourceStreams.privateIDScalarDraw_uniform_atom p u

/-- The unnormalized W-cylinder identity. `D` is an event of the two original
local round streams together; zero-mass complement events are included. -/
theorem split_cylinder_measure (p : Parameters) (s : Fin (n_boot p))
    (j : Fin (p.m - 1)) (hj : j.val + 1 < p.m)
    (E : Set (Complement p s j ⟨j.val + 1, hj⟩))
    (D : Set ((BlockTime p s → Scalar) × (BlockTime p s → Scalar)))
    (u : Fin (A_id p)) (hE : MeasurableSet E) (hD : MeasurableSet D) :
    extendedPrivateLaw p
      {rho | (splitEquiv p s j hj rho).1 ∈ E ∧
        PrivateSourceStreams.privateIDScalarDraw p
          (splitEquiv p s j hj rho).2.1 = u ∧
        (splitEquiv p s j hj rho).2.2 ∈ D} =
      complementLaw p s j ⟨j.val + 1, hj⟩ E *
        ENNReal.ofReal (1 / (A_id p : ℝ)) * roundPairLaw p s D := by
  let i : Fin p.m := ⟨j.val + 1, hj⟩
  let F := idFiber p u
  have hF : MeasurableSet F := measurableSet_idFiber p u
  let hMP := split_measurePreserving p s j hj
  let C : Set (Complement p s j i × LocalCoordinates p s) := E ×ˢ (F ×ˢ D)
  have hEvent : {rho : ExtendedPrivateCoordinates p |
      (splitEquiv p s j hj rho).1 ∈ E ∧
        PrivateSourceStreams.privateIDScalarDraw p
          (splitEquiv p s j hj rho).2.1 = u ∧
        (splitEquiv p s j hj rho).2.2 ∈ D} = (splitEquiv p s j hj) ⁻¹' C := by
    ext rho
    simp [C, F, idFiber]
  calc
    extendedPrivateLaw p {rho | (splitEquiv p s j hj rho).1 ∈ E ∧
        PrivateSourceStreams.privateIDScalarDraw p
          (splitEquiv p s j hj rho).2.1 = u ∧
        (splitEquiv p s j hj rho).2.2 ∈ D} =
      (extendedPrivateLaw p).map (splitEquiv p s j hj) C := by
          calc
            _ = extendedPrivateLaw p ((splitEquiv p s j hj) ⁻¹' C) :=
              congrArg (extendedPrivateLaw p) hEvent
            _ = (extendedPrivateLaw p).map (splitEquiv p s j hj) C :=
              (Measure.map_apply (splitEquiv p s j hj).measurable
                (hE.prod (hF.prod hD))).symm
    _ = (complementLaw p s j i).prod (localCoordinatesLaw p s)
          C := by rw [hMP.map_eq]
    _ = complementLaw p s j i E *
          (ContinuousCategorical.uniform F * roundPairLaw p s D) := by
          rw [show C = E ×ˢ (F ×ˢ D) from rfl,
            Measure.prod_prod E (F ×ˢ D), localCoordinatesLaw,
            Measure.prod_prod F D]
    _ = complementLaw p s j i E *
          ENNReal.ofReal (1 / (A_id p : ℝ)) * roundPairLaw p s D := by
          rw [idFiber_mass]
          simp only [mul_assoc]

/-- The selected W-base coordinates retain every nonselected original
follower triple, including its block and follower labels. -/
theorem followerSplit_other_triple (p : Parameters) (s : Fin (n_boot p))
    (j : Fin (p.m - 1)) (x : PrivateSourceStreams.FollowerBlockInputs p)
    (k : Fin (p.m - 1)) (hkj : k ≠ j) :
    (followerSplitEquiv p s j x).2.2.1 ⟨k, hkj⟩ = x s k := by
  classical
  rfl

theorem split_wBase_eq_followerSplit (p : Parameters) (s : Fin (n_boot p))
    (j : Fin (p.m - 1)) (hj : j.val + 1 < p.m)
    (rho : ExtendedPrivateCoordinates p) :
    (splitEquiv p s j hj rho).1.1 =
      (followerSplitEquiv p s j rho.1.1).2 := by
  classical
  rfl

theorem split_activity_scalar (p : Parameters) (s : Fin (n_boot p))
    (j : Fin (p.m - 1)) (hj : j.val + 1 < p.m)
    (rho : ExtendedPrivateCoordinates p) :
    (splitEquiv p s j hj rho).1.1.1.1 = (rho.1.1 s j).1 := by
  rfl

theorem split_held_scalar (p : Parameters) (s : Fin (n_boot p))
    (j : Fin (p.m - 1)) (hj : j.val + 1 < p.m)
    (rho : ExtendedPrivateCoordinates p) :
    (splitEquiv p s j hj rho).1.1.1.2 = (rho.1.1 s j).2.1 := by
  rfl

theorem split_target_scalar (p : Parameters) (s : Fin (n_boot p))
    (j : Fin (p.m - 1)) (hj : j.val + 1 < p.m)
    (rho : ExtendedPrivateCoordinates p) :
    (splitEquiv p s j hj rho).1.2.2.2 s = rho.2.2 s := by
  rfl

theorem split_otherRound_scalar (p : Parameters) (s : Fin (n_boot p))
    (j : Fin (p.m - 1)) (hj : j.val + 1 < p.m)
    (rho : ExtendedPrivateCoordinates p)
    (q : OtherRoundLabels p s ⟨j.val + 1, hj⟩) :
    (splitEquiv p s j hj rho).1.2.2.1 q = rho.2.1 q.1 := by
  rfl

theorem split_id_scalar (p : Parameters) (s : Fin (n_boot p))
    (j : Fin (p.m - 1)) (hj : j.val + 1 < p.m)
    (rho : ExtendedPrivateCoordinates p) :
    (splitEquiv p s j hj rho).2.1 = (rho.1.1 s j).2.2 := rfl

theorem split_coordinatorRound_scalar (p : Parameters) (s : Fin (n_boot p))
    (j : Fin (p.m - 1)) (hj : j.val + 1 < p.m)
    (rho : ExtendedPrivateCoordinates p) (t : BlockTime p s) :
    (splitEquiv p s j hj rho).2.2.1 t =
      rho.2.1 (coordinatorPlayer p, t.1) := rfl

theorem split_followerRound_scalar (p : Parameters) (s : Fin (n_boot p))
    (j : Fin (p.m - 1)) (hj : j.val + 1 < p.m)
    (rho : ExtendedPrivateCoordinates p) (t : BlockTime p s) :
    (splitEquiv p s j hj rho).2.2.2 t =
      rho.2.1 (⟨j.val + 1, hj⟩, t.1) := rfl

theorem split_otherBlock_triple (p : Parameters) (s : Fin (n_boot p))
    (j : Fin (p.m - 1)) (hj : j.val + 1 < p.m)
    (rho : ExtendedPrivateCoordinates p) (r : {r : Fin (n_boot p) // r ≠ s}) :
    (splitEquiv p s j hj rho).1.1.2.2 r = rho.1.1 r.1 := rfl

theorem split_J_scalar (p : Parameters) (s : Fin (n_boot p))
    (j : Fin (p.m - 1)) (hj : j.val + 1 < p.m)
    (rho : ExtendedPrivateCoordinates p) :
    (splitEquiv p s j hj rho).1.2.1 = rho.1.2 := rfl

theorem split_target_scalars (p : Parameters) (s : Fin (n_boot p))
    (j : Fin (p.m - 1)) (hj : j.val + 1 < p.m)
    (rho : ExtendedPrivateCoordinates p) :
    (splitEquiv p s j hj rho).1.2.2.2 = rho.2.2 := rfl

theorem split_reconstruction (p : Parameters) (s : Fin (n_boot p))
    (j : Fin (p.m - 1)) (hj : j.val + 1 < p.m)
    (rho : ExtendedPrivateCoordinates p) :
    (splitEquiv p s j hj).symm (splitEquiv p s j hj rho) = rho :=
  (splitEquiv p s j hj).symm_apply_apply rho

/-- The physical follower label corresponding to a source `Fin (m-1)` index. -/
@[expose] def sourceFollower (p : Parameters) (j : Fin (p.m - 1)) :
    ActiveRoundActions.Follower p.m :=
  ⟨j.val, by simpa only [PublicDiscreteDraws.followerCount] using j.isLt⟩

theorem sourceFollowerIndex_eq (p : Parameters) (j : Fin (p.m - 1)) :
    BootstrapPhysicalInput.sourceFollowerIndex p (sourceFollower p j) = j := by
  apply Fin.ext
  rfl

/-- Peer round labels are precisely residual coordinates of this split. -/
@[expose] def peerRoundLabel (p : Parameters) (s : Fin (n_boot p))
    (j : Fin (p.m - 1)) (hj : j.val + 1 < p.m)
    (k : {k : Fin (p.m - 1) // k ≠ j}) (t : BlockTime p s) :
    OtherRoundLabels p s ⟨j.val + 1, hj⟩ := by
  let fk := sourceFollower p k.1
  let fj := sourceFollower p j
  have hneCoord : PublicDiscreteDraws.followerPlayer p.two_le_m fk ≠
      coordinatorPlayer p :=
    ActiveRoundActions.followerPlayer_ne_coordinator p.two_le_m fk
  have hfj : PublicDiscreteDraws.followerPlayer p.two_le_m fj =
      ⟨j.val + 1, hj⟩ := by
    apply Fin.ext
    rfl
  have hneFocal : PublicDiscreteDraws.followerPlayer p.two_le_m fk ≠
      ⟨j.val + 1, hj⟩ := by
    intro h
    apply k.property
    apply Fin.ext
    have hk := ActiveRoundActions.followerPlayer_injective p.two_le_m (h.trans hfj.symm)
    exact congrArg Fin.val hk
  exact ⟨(PublicDiscreteDraws.followerPlayer p.two_le_m fk, t.1), by
    intro h
    rcases h with hcoord | hfocal
    · exact hneCoord hcoord.1
    · exact hneFocal hfocal.1⟩

/-- An initial-block peer arm, read only from its original W triple, its own
original round scalar, and the fixed published ID array. -/
@[expose] noncomputable def initialPeerArmFromW (p : Parameters)
    (s : Fin (n_boot p)) (j : Fin (p.m - 1)) (hj : j.val + 1 < p.m)
    (P : PublishedOutput p) (w : Complement p s j ⟨j.val + 1, hj⟩)
    (t : BlockTime p s) (k : {k : Fin (p.m - 1) // k ≠ j}) : Fin p.K := by
  let fk := sourceFollower p k.1
  let idx := BootstrapPhysicalInput.sourceFollowerIndex p fk
  let draws := PrivateSourceStreams.privateBlockDrawMap p
    ((ReferenceInitializationRun.initial p).numerators idx)
    ((ReferenceInitializationRun.initial p).weight_ge_one idx) (w.1.2.1 k)
  let v := w.2.2.1 (peerRoundLabel p s j hj k t)
  exact if draws.1 then
    if P.1 draws.2.2 t.1 then
      (BootstrapPrivateRoundStreams.forbiddenArmScalarDraw p draws.2.1 v).val
    else draws.2.1
  else BootstrapPrivateRoundStreams.fullArmScalarDraw p v

theorem measurableSet_initialPeerArmFromW_fiber (p : Parameters)
    (s : Fin (n_boot p)) (j : Fin (p.m - 1)) (hj : j.val + 1 < p.m)
    (P : PublishedOutput p)
    (k : {k : Fin (p.m - 1) // k ≠ j}) (t : BlockTime p s) (b : Fin p.K) :
    MeasurableSet {w : Complement p s j ⟨j.val + 1, hj⟩ |
      initialPeerArmFromW p s j hj P w t k = b} := by
  classical
  let α := Complement p s j ⟨j.val + 1, hj⟩
  let fk := sourceFollower p k.1
  let idx := BootstrapPhysicalInput.sourceFollowerIndex p fk
  let n := (ReferenceInitializationRun.initial p).numerators idx
  let hn := (ReferenceInitializationRun.initial p).weight_ge_one idx
  let draws : α → PrivateSourceStreams.BlockDraw p := fun w =>
    PrivateSourceStreams.privateBlockDrawMap p n hn (w.1.2.1 k)
  let scalar : α → Scalar := fun w =>
    w.2.2.1 (peerRoundLabel p s j hj k t)
  let active : α → Bool := fun w => (draws w).1
  let held : α → Fin p.K := fun w => (draws w).2.1
  let idbit : α → Bool := fun w => P.1 (draws w).2.2 t.1
  let full : α → Fin p.K := fun w =>
    BootstrapPrivateRoundStreams.fullArmScalarDraw p (scalar w)
  let avoid (a : Fin p.K) : α → Fin p.K := fun w =>
    (BootstrapPrivateRoundStreams.forbiddenArmScalarDraw p a (scalar w)).val
  have htriple : Measurable (fun w : α => w.1.2.1 k) := by
    exact (measurable_pi_apply k).comp
      (measurable_fst.comp (measurable_snd.comp measurable_fst))
  have hdraws : Measurable draws := by
    dsimp [draws]
    exact (PrivateSourceStreams.measurable_privateBlockDrawMap p n hn).comp htriple
  have hactive : Measurable active := by
    dsimp [active]
    exact measurable_fst.comp hdraws
  have hheld : Measurable held := by
    dsimp [held]
    exact (measurable_fst.comp measurable_snd).comp hdraws
  have hid : Measurable (fun w : α => (draws w).2.2) := by
    exact (measurable_snd.comp measurable_snd).comp hdraws
  have hidbit : Measurable idbit := by
    dsimp [idbit]
    exact (Measurable.of_discrete (f := fun u : Fin (A_id p) => P.1 u t.1)).comp hid
  have hscalar : Measurable scalar := by
    dsimp [scalar]
    exact (measurable_pi_apply (peerRoundLabel p s j hj k t)).comp
      (measurable_fst.comp (measurable_snd.comp measurable_snd))
  have hfull : Measurable full := by
    dsimp [full]
    exact (BootstrapPrivateRoundStreams.measurable_fullArmScalarDraw p).comp hscalar
  have havoid (a : Fin p.K) : Measurable (avoid a) := by
    dsimp [avoid]
    exact (measurable_subtype_coe.comp
      (BootstrapPrivateRoundStreams.measurable_forbiddenArmScalarDraw p a)).comp hscalar
  let E0 : Set α := {w | active w = false} ∩ {w | full w = b}
  let E1 : Set α := {w | active w = true} ∩
    (({w | idbit w = false} ∩ {w | held w = b}) ∪
      ⋃ a : Fin p.K, {w | idbit w = true} ∩
        ({w | held w = a} ∩ {w | avoid a w = b}))
  have hformula (w : α) : initialPeerArmFromW p s j hj P w t k =
      if active w then if idbit w then avoid (held w) w else held w else full w := rfl
  have hset : {w : α | initialPeerArmFromW p s j hj P w t k = b} = E0 ∪ E1 := by
    ext w
    change initialPeerArmFromW p s j hj P w t k = b ↔ w ∈ E0 ∪ E1
    rw [hformula w]
    cases hA : (draws w).1 <;>
      cases hB : P.1 (draws w).2.2 t.1 <;>
        simp [E0, E1, active, held, idbit, full, avoid, hA, hB]
  rw [hset]
  apply MeasurableSet.union
  · change MeasurableSet ({w | active w = false} ∩ {w | full w = b})
    exact (measurableSet_singleton false).preimage hactive |>.inter
      ((measurableSet_singleton b).preimage hfull)
  · change MeasurableSet ({w | active w = true} ∩
      (({w | idbit w = false} ∩ {w | held w = b}) ∪
        ⋃ a : Fin p.K, {w | idbit w = true} ∩
          ({w | held w = a} ∩ {w | avoid a w = b})))
    apply (measurableSet_singleton true).preimage hactive |>.inter
    apply MeasurableSet.union
    · exact (measurableSet_singleton false).preimage hidbit |>.inter
        ((measurableSet_singleton b).preimage hheld)
    · apply MeasurableSet.iUnion
      intro a
      exact (measurableSet_singleton true).preimage hidbit |>.inter
        ((measurableSet_singleton a).preimage hheld |>.inter
          ((measurableSet_singleton b).preimage (havoid a)))

/-- The actual first physical block selected by the deterministic initialization
producer. -/
theorem initialBoundaryHasNextBlock (p : Parameters) :
    (ReferenceInitializationRun.initial p).completed < n_boot p := by
  change 0 < n_boot p
  exact BootstrapDimensions.n_boot_pos p

@[expose] def initialBlockIndex (p : Parameters) : Fin (n_boot p) :=
  ReferenceInitializationRun.nextBlock (ReferenceInitializationRun.initial p)
    (initialBoundaryHasNextBlock p)

theorem initialBoundary_processesFirstBlock (p : Parameters) :
    (ReferenceInitializationRun.initial p).completed < n_boot p ∧
      ReferenceInitializationRun.nextBlock (ReferenceInitializationRun.initial p)
        (initialBoundaryHasNextBlock p) =
        initialBlockIndex p := by
  exact ⟨initialBoundaryHasNextBlock p, rfl⟩

/-- The exact initialization input at fixed published output, row index,
rounded rewards, constants, and original private coordinates. -/
@[expose] def initialRunInput (p : Parameters) (P : PublishedOutput p)
    (J : Fin (ConstructorDimensions.M p))
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (rho : ExtendedPrivateCoordinates p) : ReferenceInitializationRun.Input p where
  ids := P.1
  row := P.2 J
  rewards := rewards
  coordinates := rho
  C_star := C_star
  C_h := C_h
  eta := eta

/-- Existing physical input at the producer's actual initial boundary. -/
@[expose] def initialPhysicalInput (p : Parameters) (P : PublishedOutput p)
    (J : Fin (ConstructorDimensions.M p))
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (rho : ExtendedPrivateCoordinates p) :
    BootstrapPhysicalBlock.Input p (initialBlockIndex p) :=
  ReferenceInitializationRun.physical (initialRunInput p P J rewards C_star C_h eta rho)
    (ReferenceInitializationRun.initial p)
    (initialBoundaryHasNextBlock p)

/-- W-only event fixing the initial activity, held arm, coordinator target,
and every peer follower arm on the literal shortened first block. -/
@[expose] def initialBlockWEvent (p : Parameters) (P : PublishedOutput p)
    (j : Fin (p.m - 1)) (hj : j.val + 1 < p.m) (a z : Fin p.K)
    (peer : BlockTime p (initialBlockIndex p) →
      {k : Fin (p.m - 1) // k ≠ j} → Fin p.K) :
    Set (Complement p (initialBlockIndex p) j ⟨j.val + 1, hj⟩) :=
  {w | PrivateSourceStreams.activityScalarDraw p w.1.1.1 = true ∧
    PrivateSourceStreams.heldArmScalarDraw p
      ((ReferenceInitializationRun.initial p).numerators j)
      ((ReferenceInitializationRun.initial p).weight_ge_one j) w.1.1.2 = a ∧
    BootstrapPrivateRoundStreams.coordinatorTargetDraw p
      (w.2.2.2 (initialBlockIndex p)) = z ∧
    ∀ t k, initialPeerArmFromW p (initialBlockIndex p) j hj P w t k = peer t k}

theorem measurableSet_initialBlockWEvent (p : Parameters) (P : PublishedOutput p)
    (j : Fin (p.m - 1)) (hj : j.val + 1 < p.m) (a z : Fin p.K)
    (peer : BlockTime p (initialBlockIndex p) →
      {k : Fin (p.m - 1) // k ≠ j} → Fin p.K) :
    MeasurableSet (initialBlockWEvent p P j hj a z peer) := by
  classical
  let α := Complement p (initialBlockIndex p) j ⟨j.val + 1, hj⟩
  have hactivity : Measurable (fun w : α =>
      PrivateSourceStreams.activityScalarDraw p w.1.1.1) :=
    (PrivateSourceStreams.activityScalarDraw_measurable p).comp
      (measurable_fst.comp (measurable_fst.comp measurable_fst))
  have hheld : Measurable (fun w : α =>
      PrivateSourceStreams.heldArmScalarDraw p
        ((ReferenceInitializationRun.initial p).numerators j)
        ((ReferenceInitializationRun.initial p).weight_ge_one j) w.1.1.2) :=
    (PrivateSourceStreams.measurable_heldArmScalarDraw p
      ((ReferenceInitializationRun.initial p).numerators j)
      ((ReferenceInitializationRun.initial p).weight_ge_one j)).comp
      (measurable_snd.comp (measurable_fst.comp measurable_fst))
  have htarget : Measurable (fun w : α =>
      BootstrapPrivateRoundStreams.coordinatorTargetDraw p
        (w.2.2.2 (initialBlockIndex p))) := by
    exact (BootstrapPrivateRoundStreams.measurable_fullArmScalarDraw p).comp
      ((measurable_pi_apply (initialBlockIndex p)).comp
        (measurable_snd.comp (measurable_snd.comp measurable_snd)))
  have hpeer : MeasurableSet {w : α | ∀ t k,
      initialPeerArmFromW p (initialBlockIndex p) j hj P w t k = peer t k} := by
    rw [show {w : α | ∀ t k,
        initialPeerArmFromW p (initialBlockIndex p) j hj P w t k = peer t k} =
      Set.iInter (fun t : BlockTime p (initialBlockIndex p) =>
        Set.iInter (fun k : {k : Fin (p.m - 1) // k ≠ j} =>
          {w : α | initialPeerArmFromW p (initialBlockIndex p) j hj P w t k = peer t k})) by
        ext w
        simp]
    exact MeasurableSet.iInter fun t => MeasurableSet.iInter fun k =>
      measurableSet_initialPeerArmFromW_fiber p (initialBlockIndex p) j hj P k t (peer t k)
  change MeasurableSet {w : α |
    PrivateSourceStreams.activityScalarDraw p w.1.1.1 = true ∧
    PrivateSourceStreams.heldArmScalarDraw p
      ((ReferenceInitializationRun.initial p).numerators j)
      ((ReferenceInitializationRun.initial p).weight_ge_one j) w.1.1.2 = a ∧
    BootstrapPrivateRoundStreams.coordinatorTargetDraw p
      (w.2.2.2 (initialBlockIndex p)) = z ∧
    ∀ t k, initialPeerArmFromW p (initialBlockIndex p) j hj P w t k = peer t k}
  exact ((measurableSet_singleton true).preimage hactivity).inter
    (((measurableSet_singleton a).preimage hheld).inter
      (((measurableSet_singleton z).preimage htarget).inter hpeer))

theorem initialPeerAction_eq_fromW (p : Parameters) (P : PublishedOutput p)
    (J : Fin (ConstructorDimensions.M p))
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (rho : ExtendedPrivateCoordinates p) (j : Fin (p.m - 1))
    (hj : j.val + 1 < p.m)
    (k : {k : Fin (p.m - 1) // k ≠ j})
    (t : BlockTime p (initialBlockIndex p)) :
    BootstrapPhysicalBlock.actions
      (initialPhysicalInput p P J rewards C_star C_h eta rho)
      (BootstrapPhysicalBlock.run
        (initialPhysicalInput p P J rewards C_star C_h eta rho) t.1.val)
      t.1 (PublicDiscreteDraws.followerPlayer p.two_le_m (sourceFollower p k.1)) =
    initialPeerArmFromW p (initialBlockIndex p) j hj P
      (splitEquiv p (initialBlockIndex p) j hj rho).1 t k := by
  have htriple :
      (splitEquiv p (initialBlockIndex p) j hj rho).1.1.2.1 k =
        rho.1.1 (initialBlockIndex p) k.1 := by
    rw [split_wBase_eq_followerSplit]
    exact followerSplit_other_triple p (initialBlockIndex p) j rho.1.1 k.1 k.2
  have hround :
      (splitEquiv p (initialBlockIndex p) j hj rho).1.2.2.1
        (peerRoundLabel p (initialBlockIndex p) j hj k t) =
      rho.2.1 (peerRoundLabel p (initialBlockIndex p) j hj k t).1 :=
    split_otherRound_scalar p (initialBlockIndex p) j hj rho
      (peerRoundLabel p (initialBlockIndex p) j hj k t)
  let fk := sourceFollower p k.1
  let incoming := ReferenceInitializationRun.uninformed
    (ReferenceInitializationRun.initial p)
  have hmem : fk ∈ incoming := by
    rw [ReferenceInitializationRun.mem_uninformed]
    rfl
  let d := PrivateSourceStreams.blockDrawProfileMap p
    (ReferenceInitializationRun.initial p).numerators
    (ReferenceInitializationRun.initial p).weight_ge_one
    (rho.1.1 (initialBlockIndex p)) k.1
  have hnext := (initialBoundary_processesFirstBlock p).2
  let v := initialPhysicalInput p P J rewards C_star C_h eta rho
  have hdraw0 := ReferenceInitializationRun.physical_own_block_draw
    (initialRunInput p P J rewards C_star C_h eta rho)
    (ReferenceInitializationRun.initial p)
    (initialBoundaryHasNextBlock p)
    ⟨fk, hmem⟩
  simp only [fk] at hdraw0
  rw [sourceFollowerIndex_eq p k.1] at hdraw0
  have hdraw :
      (v.active ⟨fk, hmem⟩, v.held ⟨fk, hmem⟩, v.privateId ⟨fk, hmem⟩) = d := by
    dsimp [v, initialPhysicalInput, initialRunInput,
      ReferenceInitializationRun.physical, initialBlockIndex,
      initialBoundaryHasNextBlock, d]
    exact hdraw0
  have hactive : v.active ⟨fk, hmem⟩ = d.1 := by
    exact congrArg (fun q => q.1) hdraw
  have hheld : v.held ⟨fk, hmem⟩ = d.2.1 := by
    exact congrArg (fun q => q.2.1) hdraw
  have hid : v.privateId ⟨fk, hmem⟩ = d.2.2 := by
    exact congrArg (fun q => q.2.2) hdraw
  have hroundActual : BootstrapPhysicalInput.playerRoundScalarAt p rho
      (PublicDiscreteDraws.followerPlayer p.two_le_m fk) t.1 =
        (splitEquiv p (initialBlockIndex p) j hj rho).1.2.2.1
          (peerRoundLabel p (initialBlockIndex p) j hj k t) := by
    rw [hround]
    rfl
  have hids : v.ids (v.privateId ⟨fk, hmem⟩) t.1 = P.1 d.2.2 t.1 := by
    change P.1 (v.privateId ⟨fk, hmem⟩) t.1 = P.1 d.2.2 t.1
    rw [hid]
  have havoid : v.followerAvoid ⟨fk, hmem⟩ t.1 =
      (BootstrapPrivateRoundStreams.forbiddenArmScalarDraw p d.2.1
        ((splitEquiv p (initialBlockIndex p) j hj rho).1.2.2.1
          (peerRoundLabel p (initialBlockIndex p) j hj k t))).val := by
    change (BootstrapPrivateRoundStreams.forbiddenArmScalarDraw p
      (v.held ⟨fk, hmem⟩)
      (BootstrapPhysicalInput.playerRoundScalarAt p rho
        (PublicDiscreteDraws.followerPlayer p.two_le_m fk) t.1)).val = _
    rw [hheld, hroundActual]
  have hpeerDraw : PrivateSourceStreams.privateBlockDrawMap p
      ((ReferenceInitializationRun.initial p).numerators
        (BootstrapPhysicalInput.sourceFollowerIndex p (sourceFollower p k.1)))
      ((ReferenceInitializationRun.initial p).weight_ge_one
        (BootstrapPhysicalInput.sourceFollowerIndex p (sourceFollower p k.1)))
      ((splitEquiv p (initialBlockIndex p) j hj rho).1.1.2.1 k) = d := by
    rw [sourceFollowerIndex_eq p k.1, htriple]
    rfl
  have hmemV : fk ∈ v.uninformed := by
    simpa [v, initialPhysicalInput, initialRunInput,
      ReferenceInitializationRun.physical,
      BootstrapPhysicalInput.blockInput_uninformed] using hmem
  have huniform : v.uniform (PublicDiscreteDraws.followerPlayer p.two_le_m fk) t.1 =
      BootstrapPrivateRoundStreams.fullArmScalarDraw p
        (BootstrapPhysicalInput.playerRoundScalarAt p rho
          (PublicDiscreteDraws.followerPlayer p.two_le_m fk) t.1) := by
    change BootstrapPrivateRoundStreams.fullArmScalarDraw p
      (BootstrapPhysicalInput.playerRoundScalarAt p rho
        (PublicDiscreteDraws.followerPlayer p.two_le_m fk) t.1) = _
    rfl
  change BootstrapPhysicalBlock.actions v
      (BootstrapPhysicalBlock.run v t.1.val) t.1
        (PublicDiscreteDraws.followerPlayer p.two_le_m fk) = _
  rw [BootstrapPhysicalBlock.actions_follower]
  rw [BootstrapPhysicalBlock.followerAction]
  simp only [dite_eq_left hmemV]
  unfold BootstrapPhysicalBlock.uninformedAction
  rw [hactive]
  by_cases ha : d.1 = true
  · rw [ha, hids]
    by_cases hid' : P.1 d.2.2 t.1 = true
    · rw [hid']
      rw [havoid]
      simp only [initialPeerArmFromW]
      rw [hpeerDraw]
      simp [ha, hid']
    · simp [hid']
      rw [hheld]
      simp only [initialPeerArmFromW]
      rw [hpeerDraw]
      simp [ha, hid']
  · simp only [ite_eq_right ha]
    rw [huniform, hroundActual]
    simp only [initialPeerArmFromW]
    rw [hpeerDraw]
    simp [ha]

/-- Initial membership is discharged from the producer's literal empty
activation map; it is not an input event. -/
theorem initialFollower_uninformed (p : Parameters) (j : Fin (p.m - 1)) :
    sourceFollower p j ∈
      ReferenceInitializationRun.uninformed (ReferenceInitializationRun.initial p) := by
  rw [ReferenceInitializationRun.mem_uninformed]
  rfl

/-- The initial numerator vector is the producer's literal source initial
state. -/
theorem initialNumerator_eq (p : Parameters) (j : Fin (p.m - 1)) (a : Fin p.K) :
    (ReferenceInitializationRun.initial p).numerators j a =
      BootstrapWeightPotential.scale (b_N p) := rfl

/-- The actual initial block input keeps the accepted block draw from the
same original triple at the selected follower label. -/
theorem initialPhysical_draw (p : Parameters) (P : PublishedOutput p)
    (J : Fin (ConstructorDimensions.M p))
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (rho : ExtendedPrivateCoordinates p) (j : Fin (p.m - 1)) :
    ((initialPhysicalInput p P J rewards C_star C_h eta rho).active
        ⟨sourceFollower p j, initialFollower_uninformed p j⟩,
      (initialPhysicalInput p P J rewards C_star C_h eta rho).held
        ⟨sourceFollower p j, initialFollower_uninformed p j⟩,
      (initialPhysicalInput p P J rewards C_star C_h eta rho).privateId
        ⟨sourceFollower p j, initialFollower_uninformed p j⟩) =
      PrivateSourceStreams.blockDrawProfileMap p
        (ReferenceInitializationRun.initial p).numerators
        (ReferenceInitializationRun.initial p).weight_ge_one
        (rho.1.1 (initialBlockIndex p))
        (BootstrapPhysicalInput.sourceFollowerIndex p (sourceFollower p j)) := by
  exact ReferenceInitializationRun.physical_own_block_draw
    (initialRunInput p P J rewards C_star C_h eta rho)
    (ReferenceInitializationRun.initial p)
    (initialBoundaryHasNextBlock p)
    ⟨sourceFollower p j, initialFollower_uninformed p j⟩

theorem initialPhysical_privateId (p : Parameters) (P : PublishedOutput p)
    (J : Fin (ConstructorDimensions.M p))
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (rho : ExtendedPrivateCoordinates p) (j : Fin (p.m - 1))
    (hj : j.val + 1 < p.m) :
    (initialPhysicalInput p P J rewards C_star C_h eta rho).privateId
        ⟨sourceFollower p j, initialFollower_uninformed p j⟩ =
      PrivateSourceStreams.privateIDScalarDraw p
        (splitEquiv p (initialBlockIndex p) j hj rho).2.1 := by
  have h := initialPhysical_draw p P J rewards C_star C_h eta rho j
  rw [sourceFollowerIndex_eq p j] at h
  simpa only [PrivateSourceStreams.blockDrawProfileMap,
    PrivateSourceStreams.privateBlockDrawMap, split_id_scalar] using
    congrArg (fun d => d.2.2) h

/-- The actual first-block event: the producer processes its literal initial
block, the focal follower starts uninformed and active with held arm `a`, the
actual target is `z`, and every other follower's generated physical action is
the prescribed vector. Peers may be active or inactive. -/
@[expose] noncomputable def initialBlockActualEvent (p : Parameters)
    (P : PublishedOutput p) (J : Fin (ConstructorDimensions.M p))
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (j : Fin (p.m - 1)) (_hj : j.val + 1 < p.m) (a z : Fin p.K)
    (peer : BlockTime p (initialBlockIndex p) →
      {k : Fin (p.m - 1) // k ≠ j} → Fin p.K) : Set (ExtendedPrivateCoordinates p) :=
  {rho | (ReferenceInitializationRun.initial p).completed < n_boot p ∧
    sourceFollower p j ∈
      ReferenceInitializationRun.uninformed (ReferenceInitializationRun.initial p) ∧
    (initialPhysicalInput p P J rewards C_star C_h eta rho).active
      ⟨sourceFollower p j, initialFollower_uninformed p j⟩ = true ∧
    (initialPhysicalInput p P J rewards C_star C_h eta rho).held
      ⟨sourceFollower p j, initialFollower_uninformed p j⟩ = a ∧
    (initialPhysicalInput p P J rewards C_star C_h eta rho).target = z ∧
    ∀ t k, BootstrapPhysicalBlock.actions
      (initialPhysicalInput p P J rewards C_star C_h eta rho)
      (BootstrapPhysicalBlock.run
        (initialPhysicalInput p P J rewards C_star C_h eta rho) t.1.val)
      t.1 (PublicDiscreteDraws.followerPlayer p.two_le_m (sourceFollower p k.1)) =
        peer t k}

/-- On the deterministic initial boundary this actual physical event is a
`W`-cylinder under the original-coordinate split. Its fixed processing and
uninformed-status clauses are discharged from `initial`; its random clauses
use the producer's actual block draw and unchanged peer round scalars.

Source: `appendix_b_communication.tex:302-308,357-365`. -/
theorem initialBlockActualEvent_eq_splitCylinder (p : Parameters)
    (P : PublishedOutput p) (J : Fin (ConstructorDimensions.M p))
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (j : Fin (p.m - 1)) (hj : j.val + 1 < p.m) (a z : Fin p.K)
    (peer : BlockTime p (initialBlockIndex p) →
      {k : Fin (p.m - 1) // k ≠ j} → Fin p.K) :
    initialBlockActualEvent p P J rewards C_star C_h eta j hj a z peer =
      (fun rho => (splitEquiv p (initialBlockIndex p) j hj rho).1) ⁻¹'
        initialBlockWEvent p P j hj a z peer := by
  have hdraw (rho : ExtendedPrivateCoordinates p) :=
    initialPhysical_draw p P J rewards C_star C_h eta rho j
  have hactive (rho : ExtendedPrivateCoordinates p) :
      (initialPhysicalInput p P J rewards C_star C_h eta rho).active
          ⟨sourceFollower p j, initialFollower_uninformed p j⟩ =
        PrivateSourceStreams.activityScalarDraw p (rho.1.1 (initialBlockIndex p) j).1 := by
    have h := hdraw rho
    rw [sourceFollowerIndex_eq p j] at h
    simpa only [PrivateSourceStreams.blockDrawProfileMap,
      PrivateSourceStreams.privateBlockDrawMap] using congrArg (fun d => d.1) h
  have hheld (rho : ExtendedPrivateCoordinates p) :
      (initialPhysicalInput p P J rewards C_star C_h eta rho).held
          ⟨sourceFollower p j, initialFollower_uninformed p j⟩ =
        PrivateSourceStreams.heldArmScalarDraw p
          ((ReferenceInitializationRun.initial p).numerators j)
          ((ReferenceInitializationRun.initial p).weight_ge_one j)
          (rho.1.1 (initialBlockIndex p) j).2.1 := by
    have h := hdraw rho
    rw [sourceFollowerIndex_eq p j] at h
    simpa only [PrivateSourceStreams.blockDrawProfileMap,
      PrivateSourceStreams.privateBlockDrawMap] using congrArg (fun d => d.2.1) h
  have htarget (rho : ExtendedPrivateCoordinates p) :
      (initialPhysicalInput p P J rewards C_star C_h eta rho).target =
        BootstrapPrivateRoundStreams.coordinatorTargetDraw p
          (rho.2.2 (initialBlockIndex p)) := rfl
  ext rho
  constructor
  · rintro ⟨_, _, hact, hheldActual, htargetActual, hpeer⟩
    have hactRaw : PrivateSourceStreams.activityScalarDraw p
        (rho.1.1 (initialBlockIndex p) j).1 = true := by
      rw [← hactive rho]
      exact hact
    have hheldRaw : PrivateSourceStreams.heldArmScalarDraw p
        ((ReferenceInitializationRun.initial p).numerators j)
        ((ReferenceInitializationRun.initial p).weight_ge_one j)
        (rho.1.1 (initialBlockIndex p) j).2.1 = a := by
      rw [← hheld rho]
      exact hheldActual
    have htargetRaw : BootstrapPrivateRoundStreams.coordinatorTargetDraw p
        (rho.2.2 (initialBlockIndex p)) = z := by
      rw [← htarget rho]
      exact htargetActual
    change PrivateSourceStreams.activityScalarDraw p
          (((splitEquiv p (initialBlockIndex p) j hj rho).1).1.1.1) = true ∧
        PrivateSourceStreams.heldArmScalarDraw p
          ((ReferenceInitializationRun.initial p).numerators j)
          ((ReferenceInitializationRun.initial p).weight_ge_one j)
          (((splitEquiv p (initialBlockIndex p) j hj rho).1).1.1.2) = a ∧
        BootstrapPrivateRoundStreams.coordinatorTargetDraw p
          (((splitEquiv p (initialBlockIndex p) j hj rho).1).2.2.2
            (initialBlockIndex p)) = z ∧
        ∀ t k, initialPeerArmFromW p (initialBlockIndex p) j hj P
          (splitEquiv p (initialBlockIndex p) j hj rho).1 t k = peer t k
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa only [split_activity_scalar] using hactRaw
    · simpa only [split_held_scalar] using hheldRaw
    · simpa only [split_target_scalar] using htargetRaw
    · intro t k
      rw [← initialPeerAction_eq_fromW p P J rewards C_star C_h eta rho j hj k t]
      exact hpeer t k
  · intro hW
    change (splitEquiv p (initialBlockIndex p) j hj rho).1 ∈
      initialBlockWEvent p P j hj a z peer at hW
    change PrivateSourceStreams.activityScalarDraw p
          (((splitEquiv p (initialBlockIndex p) j hj rho).1).1.1.1) = true ∧
        PrivateSourceStreams.heldArmScalarDraw p
          ((ReferenceInitializationRun.initial p).numerators j)
          ((ReferenceInitializationRun.initial p).weight_ge_one j)
          (((splitEquiv p (initialBlockIndex p) j hj rho).1).1.1.2) = a ∧
        BootstrapPrivateRoundStreams.coordinatorTargetDraw p
          (((splitEquiv p (initialBlockIndex p) j hj rho).1).2.2.2
            (initialBlockIndex p)) = z ∧
        ∀ t k, initialPeerArmFromW p (initialBlockIndex p) j hj P
          (splitEquiv p (initialBlockIndex p) j hj rho).1 t k = peer t k at hW
    rcases hW with ⟨hactRaw, hheldRaw, htargetRaw, hpeer⟩
    refine ⟨initialBoundaryHasNextBlock p, initialFollower_uninformed p j,
      ?_, ?_, ?_, ?_⟩
    · rw [hactive rho, ← split_activity_scalar]
      exact hactRaw
    · rw [hheld rho, ← split_held_scalar]
      exact hheldRaw
    · rw [htarget rho, ← split_target_scalar]
      exact htargetRaw
    · intro t k
      rw [initialPeerAction_eq_fromW p P J rewards C_star C_h eta rho j hj k t]
      exact hpeer t k

/-- The actual first-block event inherits measurability from its W-cylinder
description. -/
theorem measurableSet_initialBlockActualEvent (p : Parameters)
    (P : PublishedOutput p) (J : Fin (ConstructorDimensions.M p))
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (j : Fin (p.m - 1)) (hj : j.val + 1 < p.m) (a z : Fin p.K)
    (peer : BlockTime p (initialBlockIndex p) →
      {k : Fin (p.m - 1) // k ≠ j} → Fin p.K) :
    MeasurableSet (initialBlockActualEvent p P J rewards C_star C_h eta j hj a z peer) := by
  rw [initialBlockActualEvent_eq_splitCylinder]
  exact (measurableSet_initialBlockWEvent p P j hj a z peer).preimage
    (measurable_fst.comp (splitEquiv p (initialBlockIndex p) j hj).measurable)

/-- The W-event mass is exactly the probability of the generated event. -/
theorem initialBlockActualEvent_measure (p : Parameters)
    (P : PublishedOutput p) (J : Fin (ConstructorDimensions.M p))
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (j : Fin (p.m - 1)) (hj : j.val + 1 < p.m) (a z : Fin p.K)
    (peer : BlockTime p (initialBlockIndex p) →
      {k : Fin (p.m - 1) // k ≠ j} → Fin p.K) :
    extendedPrivateLaw p
        (initialBlockActualEvent p P J rewards C_star C_h eta j hj a z peer) =
      complementLaw p (initialBlockIndex p) j ⟨j.val + 1, hj⟩
        (initialBlockWEvent p P j hj a z peer) := by
  rw [initialBlockActualEvent_eq_splitCylinder]
  exact (measurePreserving_fst.comp
    (split_measurePreserving p (initialBlockIndex p) j hj)).measure_preimage
      (measurableSet_initialBlockWEvent p P j hj a z peer).nullMeasurableSet

/-- Specialization of the original-fiber cylinder formula to the actual
initial physical block. It holds for every measurable local-round event `D`,
including zero-mass W events; no atom is conditioned on or normalized here.

Source: `appendix_b_communication.tex:306-308,357-365`. -/
theorem initialBlockActual_cylinder_measure (p : Parameters)
    (P : PublishedOutput p) (J : Fin (ConstructorDimensions.M p))
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (j : Fin (p.m - 1)) (hj : j.val + 1 < p.m) (a z : Fin p.K)
    (peer : BlockTime p (initialBlockIndex p) →
      {k : Fin (p.m - 1) // k ≠ j} → Fin p.K)
    (D : Set ((BlockTime p (initialBlockIndex p) → Scalar) ×
      (BlockTime p (initialBlockIndex p) → Scalar)))
    (u : Fin (A_id p)) (hD : MeasurableSet D) :
    extendedPrivateLaw p
      {rho | rho ∈ initialBlockActualEvent p P J rewards C_star C_h eta j hj a z peer ∧
        PrivateSourceStreams.privateIDScalarDraw p
          (splitEquiv p (initialBlockIndex p) j hj rho).2.1 = u ∧
        (splitEquiv p (initialBlockIndex p) j hj rho).2.2 ∈ D} =
      complementLaw p (initialBlockIndex p) j ⟨j.val + 1, hj⟩
        (initialBlockWEvent p P j hj a z peer) *
        ENNReal.ofReal (1 / (A_id p : ℝ)) *
        roundPairLaw p (initialBlockIndex p) D := by
  rw [initialBlockActualEvent_eq_splitCylinder]
  exact split_cylinder_measure p (initialBlockIndex p) j hj
    (initialBlockWEvent p P j hj a z peer) D u
    (measurableSet_initialBlockWEvent p P j hj a z peer) hD

/-- Original-coordinate form with the actual generated event mass; no
positivity premise or conditioning on a continuous atom is needed. -/
theorem initialBlockActual_id_rounds_measure (p : Parameters)
    (P : PublishedOutput p) (J : Fin (ConstructorDimensions.M p))
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (j : Fin (p.m - 1)) (hj : j.val + 1 < p.m) (a z : Fin p.K)
    (peer : BlockTime p (initialBlockIndex p) →
      {k : Fin (p.m - 1) // k ≠ j} → Fin p.K)
    (D : Set ((BlockTime p (initialBlockIndex p) → Scalar) ×
      (BlockTime p (initialBlockIndex p) → Scalar)))
    (u : Fin (A_id p)) (hD : MeasurableSet D) :
    extendedPrivateLaw p
      {rho | rho ∈ initialBlockActualEvent p P J rewards C_star C_h eta j hj a z peer ∧
        (initialPhysicalInput p P J rewards C_star C_h eta rho).privateId
          ⟨sourceFollower p j, initialFollower_uninformed p j⟩ = u ∧
        ((fun t => rho.2.1 (coordinatorPlayer p, t.1)),
          (fun t => rho.2.1 (⟨j.val + 1, hj⟩, t.1))) ∈ D} =
      extendedPrivateLaw p
        (initialBlockActualEvent p P J rewards C_star C_h eta j hj a z peer) *
        ENNReal.ofReal (1 / (A_id p : ℝ)) * roundPairLaw p (initialBlockIndex p) D := by
  simpa only [initialBlockActualEvent_measure, initialPhysical_privateId p P J rewards
    C_star C_h eta _ j hj, ← split_coordinatorRound_scalar p (initialBlockIndex p) j hj,
    ← split_followerRound_scalar p (initialBlockIndex p) j hj, Prod.eta] using
    initialBlockActual_cylinder_measure p P J rewards C_star C_h eta j hj a z peer D u hD

end Bandits.Support.BootstrapPrivateIDFibers

end
