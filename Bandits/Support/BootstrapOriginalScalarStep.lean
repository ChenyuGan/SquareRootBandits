/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.BootstrapPrivateRoundStreams
public import Bandits.Support.BootstrapPhysicalInput
public import Bandits.Support.BootstrapPhysicalBlock
public import Bandits.Support.BootstrapModeService
public import Bandits.Support.BootstrapModeMeans
public import Bandits.Support.BootstrapStayAvoidance
public import Bandits.Support.BootstrapStayGainMean
public import Bandits.Support.BootstrapBlockCausality
public import Bandits.Support.ContinuousCategorical

import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic.Linarith

/-!
# Original-scalar observable law for one bootstrap round

The adapter below reuses each player's existing labelled uniform scalar for
both its full-arm and complement alternatives.  It does not have the product
law of all latent alternatives.  The intended bridge is equality of the full
simultaneous action-profile laws at a fixed public row coordinate, followed by
the corresponding joint law and the existing stay-positive consumer.

Sources: `sources/zip4/manuscript/07_public_setup.tex:27-38,61-109` and
`sources/zip4/manuscript/appendix_b_communication.tex:399-407,485-506`.

This module currently proves the literal adapter, the accepted latent-product
reindexing, fixed-row pointwise action identities, and the actual source
pullback identities. It does not yet prove equality of the fixed-row observable
action laws, equality of the joint public-row/action laws, or transfer the
existing stay-positive mean to the original-scalar measure. It also makes no
claim about a chronological conditional law given generated history, fresh
public symbols after publication, conditional uniformity of U, whole-block
gain, startup success, or any manuscript theorem.
-/

public section

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Bandits.Support.BootstrapOriginalScalarStep

open ConstructorDimensions BootstrapDimensions FiniteBanditModel
open BootstrapPrivateRoundStreams BootstrapPhysicalInput BootstrapPhysicalBlock
open BootstrapModeService BootstrapStayAvoidance BootstrapStayGainMean
open PublicDiscreteDraws ContinuousCategorical
open ActiveRoundActions

variable {p : ConstructorDimensions.Parameters} {s : Fin (n_boot p)}

abbrev Scalar := ContinuousCategorical.Scalar
abbrev RoundCoordinates := BootstrapModeService.RoundCoordinates
abbrev RoundPrivateValues (x : BootstrapPhysicalBlock.Input p s) :=
  BootstrapModeService.RoundPrivateValues x

/-- The original independent scalar at every player label in one calendar
round. -/
abbrev OriginalScalarVector (p : ConstructorDimensions.Parameters) :=
  Player p.m → Scalar

/-- Product law of the original, distinctly labelled player scalars. -/
@[expose] def originalScalarVectorMeasure (p : ConstructorDimensions.Parameters) :
    Measure (OriginalScalarVector p) :=
  Measure.pi (fun _ : Player p.m => ContinuousCategorical.uniform)

instance originalScalarVectorMeasure_probability (p : ConstructorDimensions.Parameters) :
    IsProbabilityMeasure (originalScalarVectorMeasure p) := by
  dsimp [originalScalarVectorMeasure]
  infer_instance

/-- Literal original-scalar adapter into the existing latent one-round values.
Each player's full-arm and complement alternatives use that same player's
scalar.  This definition makes no assertion that the latent tuple has the
independent `roundPrivateMeasure` law. -/
@[expose] def roundPrivateValuesOfOriginalScalars
    (x : BootstrapPhysicalBlock.Input p s) (v : OriginalScalarVector p) :
    RoundPrivateValues x :=
  (fun i => fullArmScalarDraw p (v i),
    (forbiddenArmScalarDraw p x.target (v (coordinator p.two_le_m)),
      fun j => forbiddenArmScalarDraw p (x.held j)
        (v (followerPlayer p.two_le_m j.1))))

/-- The original-scalar one-round source keeps the public row coordinate
independent of the product of its original labelled player scalars. -/
@[expose] def originalScalarSnapshotMeasure (_x : BootstrapPhysicalBlock.Input p s) :
    Measure (RoundCoordinates p × OriginalScalarVector p) :=
  (roundCoordinatesMeasure p).prod (originalScalarVectorMeasure p)

instance originalScalarSnapshotMeasure_probability
    (x : BootstrapPhysicalBlock.Input p s) :
    IsProbabilityMeasure (originalScalarSnapshotMeasure x) := by
  dsimp [originalScalarSnapshotMeasure]
  infer_instance

/-- Labels for the independent latent coordinates in the accepted
`RoundPrivateValues` product. -/
abbrev PrivateBranchIndex (x : BootstrapPhysicalBlock.Input p s) :=
  Option (Player p.m ⊕ {j // j ∈ x.uninformed})

/-- The finite carrier of a labelled latent full-arm or complement value. -/
abbrev privateBranchValue (x : BootstrapPhysicalBlock.Input p s) :
    PrivateBranchIndex x → Type
  | none => BootstrapPhysicalBlock.AvoidArm p x.target
  | some (.inl _) => Fin p.K
  | some (.inr j) => BootstrapPhysicalBlock.AvoidArm p (x.held j)

abbrev privateBranchValueMeasurableSpace (x : BootstrapPhysicalBlock.Input p s)
    (k : PrivateBranchIndex x) : MeasurableSpace (privateBranchValue x k) :=
  match k with
  | none => Subtype.instMeasurableSpace
  | some (.inl _) => Fin.instMeasurableSpace p.K
  | some (.inr _) => Subtype.instMeasurableSpace

attribute [instance] privateBranchValueMeasurableSpace

/-- The accepted product law on distinct full-arm, coordinator-complement,
and active-follower-complement labels. -/
@[expose] def privateBranchMeasure (x : BootstrapPhysicalBlock.Input p s)
    (k : PrivateBranchIndex x) : Measure (privateBranchValue x k) :=
  match k with
  | none => privateAvoidMeasure p x.target
  | some (.inl _) => privateArmMeasure p
  | some (.inr j) => privateAvoidMeasure p (x.held j)

instance privateBranchMeasure_probability (x : BootstrapPhysicalBlock.Input p s)
    (k : PrivateBranchIndex x) : IsProbabilityMeasure (privateBranchMeasure x k) := by
  cases k with
  | none =>
      change @IsProbabilityMeasure (BootstrapPhysicalBlock.AvoidArm p x.target)
        Subtype.instMeasurableSpace (privateAvoidMeasure p x.target)
      exact privateAvoidMeasure_probability p x.target
  | some q =>
      cases q with
      | inl i =>
          change @IsProbabilityMeasure (Fin p.K) (Fin.instMeasurableSpace p.K)
            (privateArmMeasure p)
          exact privateArmMeasure_probability p
      | inr j =>
          change @IsProbabilityMeasure (BootstrapPhysicalBlock.AvoidArm p (x.held j))
            Subtype.instMeasurableSpace (privateAvoidMeasure p (x.held j))
          exact privateAvoidMeasure_probability p (x.held j)

@[expose] def privateBranchProductMeasure (x : BootstrapPhysicalBlock.Input p s) :
    Measure ((k : PrivateBranchIndex x) → privateBranchValue x k) :=
  Measure.pi (privateBranchMeasure x)

/-- Reindex the accepted latent values by their distinct player and
complement labels. This is only a rearrangement of the existing independent
product coordinates. -/
@[expose] def privateBranchCoordinates (x : BootstrapPhysicalBlock.Input p s)
    (d : RoundPrivateValues x) :
    (k : PrivateBranchIndex x) → privateBranchValue x k
  | none => d.2.1
  | some (.inl i) => d.1 i
  | some (.inr j) => d.2.2 j

/-- The accepted latent product remains a product after reindexing by
distinct source labels. -/
theorem map_privateBranchCoordinates (x : BootstrapPhysicalBlock.Input p s) :
    (roundPrivateMeasure x).map (privateBranchCoordinates x) =
      privateBranchProductMeasure x := by
  classical
  let μfull : Measure (Player p.m → Fin p.K) := privateArmVectorMeasure p
  let μcoord : Measure (BootstrapPhysicalBlock.AvoidArm p x.target) :=
    privateAvoidMeasure p x.target
  let μfollowers : Measure ((j : {j // j ∈ x.uninformed}) →
      BootstrapPhysicalBlock.AvoidArm p (x.held j)) :=
    Measure.pi (fun j => privateAvoidMeasure p (x.held j))
  let μsum : (i : Player p.m ⊕ {j // j ∈ x.uninformed}) →
      Measure (privateBranchValue x (some i)) :=
    fun i => privateBranchMeasure x (some i)
  have hswap : MeasurePreserving Prod.swap (μcoord.prod μfollowers)
      (μfollowers.prod μcoord) := by
    exact Measure.measurePreserving_swap
  have hfirst : MeasurePreserving (fun z : (Player p.m → Fin p.K) ×
      (BootstrapPhysicalBlock.AvoidArm p x.target ×
        ((j : {j // j ∈ x.uninformed}) →
          BootstrapPhysicalBlock.AvoidArm p (x.held j))) =>
        (z.1, (z.2.2, z.2.1)))
      (μfull.prod (μcoord.prod μfollowers)) (μfull.prod (μfollowers.prod μcoord)) := by
    have h := (MeasurePreserving.id μfull).prod hswap
    exact h
  have hassoc : MeasurePreserving (MeasurableEquiv.prodAssoc.symm :
      (Player p.m → Fin p.K) ×
        (((j : {j // j ∈ x.uninformed}) →
          BootstrapPhysicalBlock.AvoidArm p (x.held j)) ×
          BootstrapPhysicalBlock.AvoidArm p x.target) ≃ᵐ
        ((Player p.m → Fin p.K) ×
          ((j : {j // j ∈ x.uninformed}) →
            BootstrapPhysicalBlock.AvoidArm p (x.held j))) ×
          BootstrapPhysicalBlock.AvoidArm p x.target)
      (μfull.prod (μfollowers.prod μcoord)) ((μfull.prod μfollowers).prod μcoord) := by
    exact (measurePreserving_prodAssoc μfull μfollowers μcoord).symm
  have hsum : MeasurePreserving (MeasurableEquiv.sumPiEquivProdPi
      (fun i : Player p.m ⊕ {j // j ∈ x.uninformed} =>
        privateBranchValue x (some i))).symm
      ((Measure.pi (fun i : Player p.m => privateArmMeasure p)).prod μfollowers)
      (Measure.pi μsum) :=
    measurePreserving_sumPiEquivProdPi_symm μsum
  have hmiddle : MeasurePreserving
      (fun z : ((Player p.m → Fin p.K) ×
        ((j : {j // j ∈ x.uninformed}) →
          BootstrapPhysicalBlock.AvoidArm p (x.held j))) ×
        BootstrapPhysicalBlock.AvoidArm p x.target =>
        (((MeasurableEquiv.sumPiEquivProdPi
          (fun i : Player p.m ⊕ {j // j ∈ x.uninformed} =>
            privateBranchValue x (some i))).symm z.1), z.2))
      ((μfull.prod μfollowers).prod μcoord)
      ((Measure.pi μsum).prod μcoord) := by
    let f := (MeasurableEquiv.sumPiEquivProdPi
      (fun i : Player p.m ⊕ {j // j ∈ x.uninformed} =>
        privateBranchValue x (some i))).symm
    refine ⟨(f.measurable.comp measurable_fst).prodMk measurable_snd, ?_⟩
    change Measure.map (Prod.map f id)
      (((Measure.pi (fun i : Player p.m => privateArmMeasure p)).prod μfollowers).prod μcoord) =
        (Measure.pi μsum).prod μcoord
    rw [← Measure.map_prod_map
      ((Measure.pi (fun i : Player p.m => privateArmMeasure p)).prod μfollowers)
      μcoord f.measurable measurable_id]
    rw [hsum.map_eq, Measure.map_id]
  let optionEquiv :=
    (MeasurableEquiv.piOptionEquivProd (privateBranchValue x)).symm
  have hoption : MeasurePreserving optionEquiv
      ((Measure.pi (fun i : Player p.m ⊕ {j // j ∈ x.uninformed} =>
        privateBranchMeasure x (some i))).prod (privateAvoidMeasure p x.target))
      (privateBranchProductMeasure x) := by
    refine ⟨optionEquiv.measurable, ?_⟩
    exact Measure.pi_map_piOptionEquivProd (privateBranchMeasure x)
  have hcomp := hoption.comp (hmiddle.comp (hassoc.comp hfirst))
  have hfun : (optionEquiv ∘
      (fun z => (((MeasurableEquiv.sumPiEquivProdPi
          (fun i : Player p.m ⊕ {j // j ∈ x.uninformed} =>
            privateBranchValue x (some i))).symm z.1), z.2)) ∘
      (MeasurableEquiv.prodAssoc.symm ∘
        (fun z : (Player p.m → Fin p.K) ×
          (BootstrapPhysicalBlock.AvoidArm p x.target ×
            ((j : {j // j ∈ x.uninformed}) →
              BootstrapPhysicalBlock.AvoidArm p (x.held j))) =>
            (z.1, (z.2.2, z.2.1))))) = privateBranchCoordinates x := by
    funext d k
    cases d with
    | mk arms rest =>
      cases rest with
      | mk coord followers =>
        cases k with
        | none => rfl
        | some i => cases i with
          | inl i => rfl
          | inr j => rfl
  change (roundPrivateMeasure x).map (privateBranchCoordinates x) = _
  rw [show roundPrivateMeasure x =
    μfull.prod (μcoord.prod μfollowers) by rfl]
  rw [← hfun]
  exact hcomp.map_eq

/-- The already supplied current private values, used only to insert a fixed
public row coordinate into the existing snapshot adapter. -/
def storedRoundPrivateValues (x : BootstrapPhysicalBlock.Input p s) (t : Fin p.T) :
    RoundPrivateValues x :=
  ((fun i => x.uniform i t), (x.coordinatorAvoid t, fun j => x.followerAvoid j t))

/-- The simultaneous physical action profile as a function of distinct
player-labelled latent coordinates.  Each randomized branch reads only that
player's selected label; row-only UP and tuple branches retain the original
public row coordinate. -/
@[expose] def actionsOfPrivateBranches (x : BootstrapPhysicalBlock.Input p s)
    (st : BootstrapPhysicalBlock.State p) (t : Fin p.T)
    (r : RoundCoordinates p)
    (b : (k : PrivateBranchIndex x) → privateBranchValue x k) :
    ActionProfile p.m p.K := by
  classical
  exact fun i =>
    if hi : i = coordinator p.two_le_m then
      if roundSlot r = dataSlot then
        if st.mode = .multicast ∧ r.1 ∈ forwardReleaseSet p st.list then
          (b none).val
        else x.target
      else if roundSlot r = downSlot then
        (BootstrapPhysicalBlock.tuple
          (currentInputOf x t r (storedRoundPrivateValues x t)) t).val i
      else b (some (.inl i))
    else
      let j := followerIndex p.two_le_m i hi
      if hj : j ∈ x.uninformed then
        if x.active ⟨j, hj⟩ = true then
          if x.ids (x.privateId ⟨j, hj⟩) t = true then
            (b (some (.inr ⟨j, hj⟩))).val
          else x.held ⟨j, hj⟩
        else b (some (.inl i))
      else BootstrapPhysicalBlock.unoccupiedAction
        (currentInputOf x t r (storedRoundPrivateValues x t)) t j

/-- The reindexed accepted latent coordinates reproduce the existing
simultaneous action profile at every fixed public row. -/
theorem actionsOfPrivateBranches_eq_actions (x : BootstrapPhysicalBlock.Input p s)
    (st : BootstrapPhysicalBlock.State p) (t : Fin p.T)
    (r : RoundCoordinates p) (d : RoundPrivateValues x) :
    actionsOfPrivateBranches x st t r (privateBranchCoordinates x d) =
      BootstrapPhysicalBlock.actions (currentInputOf x t r d) st t := by
  classical
  funext i
  by_cases hi : i = coordinator p.two_le_m
  · subst i
    simp [actionsOfPrivateBranches, BootstrapPhysicalBlock.actions,
      BootstrapPhysicalBlock.coordinatorAction,
      privateBranchCoordinates,
      storedRoundPrivateValues, currentInputOf, currentInput,
      BootstrapPhysicalBlock.slot, BootstrapModeService.roundSlot,
      BootstrapModeService.roundSlice, BootstrapPhysicalBlock.tuple,
      BootstrapPhysicalBlock.forwardProduct, BootstrapModeService.forwardReleaseSet,
      Finset.prod_eq_one_iff]
  · simp [actionsOfPrivateBranches, BootstrapPhysicalBlock.actions, hi,
      BootstrapPhysicalBlock.followerAction, BootstrapPhysicalBlock.uninformedAction,
      BootstrapPhysicalBlock.unoccupiedAction,
      privateBranchCoordinates, storedRoundPrivateValues,
      currentInputOf, currentInput, BootstrapPhysicalBlock.slot,
      BootstrapPhysicalBlock.tuple, BootstrapPhysicalBlock.pilot,
      BootstrapPhysicalBlock.selected, BootstrapPhysicalBlock.initialUpBit,
      BootstrapPhysicalBlock.initialUpWord,
      ActiveRoundActions.followerPlayer_followerIndex]

/-- Existing simultaneous actions after inserting the original scalar adapter
at the fixed public row coordinate. -/
@[expose] def originalScalarActions
    (x : BootstrapPhysicalBlock.Input p s) (st : BootstrapPhysicalBlock.State p)
    (t : Fin p.T) (r : RoundCoordinates p) (v : OriginalScalarVector p) :
    ActionProfile p.m p.K :=
  BootstrapPhysicalBlock.actions
    (currentInputOf x t r (roundPrivateValuesOfOriginalScalars x v)) st t

/-- Evaluating the branch profile on the literal scalar adapter gives exactly
the adapter's existing simultaneous action profile, pointwise in every
original labelled scalar. -/
theorem actionsOfPrivateBranches_originalScalars
    (x : BootstrapPhysicalBlock.Input p s) (st : BootstrapPhysicalBlock.State p)
    (t : Fin p.T) (r : RoundCoordinates p) (v : OriginalScalarVector p) :
    actionsOfPrivateBranches x st t r
      (privateBranchCoordinates x (roundPrivateValuesOfOriginalScalars x v)) =
        originalScalarActions x st t r v := by
  rw [actionsOfPrivateBranches_eq_actions]
  rfl

/-- The deterministic observable output used by the physical stay indicator.
The current public row coordinate and the complete simultaneous arm profile
are retained together. -/
@[expose] def originalScalarObservable
    (x : BootstrapPhysicalBlock.Input p s) (st : BootstrapPhysicalBlock.State p)
    (t : Fin p.T) (r : RoundCoordinates p) (v : OriginalScalarVector p) :
    RoundCoordinates p × ActionProfile p.m p.K :=
  (r, originalScalarActions x st t r v)

/-- At an actual existing `BootstrapPhysicalInput.blockInput`, the original
round-labelled scalars reproduce its already installed current fields exactly. -/
theorem roundPrivateValuesOfOriginalScalars_blockInput
    (s : Fin (n_boot p)) (incoming : Finset (Follower p.m))
    (numerators : Fin (p.m - 1) → Fin p.K → ℕ)
    (hpos : ∀ (j : Fin (p.m - 1)) (a : Fin p.K),
      (1 : ℝ) ≤ BootstrapWeightPotential.weight (b_N p) (numerators j) a)
    (ids : CompletePublicTable.IDArray p) (row : CompletePublicTable.CompleteRow p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (rho : ExtendedPrivateCoordinates p) (t : Fin p.T) :
    let x := BootstrapPhysicalInput.blockInput p s incoming numerators hpos ids row rewards rho
    roundPrivateValuesOfOriginalScalars x
        (fun i => BootstrapPhysicalInput.playerRoundScalarAt p rho i t) =
      ((fun i => x.uniform i t),
        (x.coordinatorAvoid t, fun j => x.followerAvoid j t)) := by
  dsimp [roundPrivateValuesOfOriginalScalars,
    BootstrapPhysicalInput.blockInput, BootstrapPhysicalInput.uniformArmMap,
    BootstrapPhysicalInput.coordinatorAvoidArmValueMap,
    BootstrapPhysicalInput.followerAvoidArmValueMap,
    BootstrapPhysicalInput.targetArmMap,
    BootstrapPhysicalInput.heldMap,
    BootstrapPhysicalInput.playerRoundScalarAt]

/-- The current input reconstructed from the actual source row and its
original labelled current scalars is the same existing physical input. -/
theorem currentInputOf_originalScalar_blockInput
    (s : Fin (n_boot p)) (incoming : Finset (Follower p.m))
    (numerators : Fin (p.m - 1) → Fin p.K → ℕ)
    (hpos : ∀ (j : Fin (p.m - 1)) (a : Fin p.K),
      (1 : ℝ) ≤ BootstrapWeightPotential.weight (b_N p) (numerators j) a)
    (ids : CompletePublicTable.IDArray p) (row : CompletePublicTable.CompleteRow p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (rho : ExtendedPrivateCoordinates p) (t : Fin p.T) :
    let x := BootstrapPhysicalInput.blockInput p s incoming numerators hpos ids row rewards rho
    currentInputOf x t (roundCoordinates p t x.row)
        (roundPrivateValuesOfOriginalScalars x
          (fun i => BootstrapPhysicalInput.playerRoundScalarAt p rho i t)) = x := by
  dsimp only
  rw [roundPrivateValuesOfOriginalScalars_blockInput]
  cases BootstrapPhysicalInput.blockInput p s incoming numerators hpos ids row rewards rho with
  | mk uninformed active held privateId ids' row' target uniform coordinatorAvoid followerAvoid rewards' =>
      have hrow₁ :
          (fun u q => if q = t then row'.1 u t else row'.1 u q) = row'.1 := by
        funext u q
        by_cases hq : q = t
        · subst q
          simp
        · simp [hq]
      have hrow₂ :
          (fun q => if q = t then row'.2 t else row'.2 q) = row'.2 := by
        funext q
        by_cases hq : q = t
        · subst q
          simp
        · simp [hq]
      have huniform :
          (fun i q => if q = t then uniform i t else uniform i q) = uniform := by
        funext i q
        by_cases hq : q = t
        · subst q
          simp
        · simp [hq]
      have hcoord :
          (fun q => if q = t then coordinatorAvoid t else coordinatorAvoid q) =
            coordinatorAvoid := by
        funext q
        by_cases hq : q = t
        · subst q
          simp
        · simp [hq]
      have hfollower :
          (fun j q => if q = t then followerAvoid j t else followerAvoid j q) =
            followerAvoid := by
        funext j q
        by_cases hq : q = t
        · subst q
          simp
        · simp [hq]
      simp [BootstrapModeService.currentInputOf, BootstrapModeService.currentInput,
        BootstrapModeService.roundCoordinates, hrow₁, hrow₂, huniform, hcoord, hfollower]

/-- Pointwise action identity at the actual source pullback. -/
theorem originalScalarActions_blockInput
    (s : Fin (n_boot p)) (incoming : Finset (Follower p.m))
    (numerators : Fin (p.m - 1) → Fin p.K → ℕ)
    (hpos : ∀ (j : Fin (p.m - 1)) (a : Fin p.K),
      (1 : ℝ) ≤ BootstrapWeightPotential.weight (b_N p) (numerators j) a)
    (ids : CompletePublicTable.IDArray p) (row : CompletePublicTable.CompleteRow p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (rho : ExtendedPrivateCoordinates p) (t : Fin p.T)
    (st : BootstrapPhysicalBlock.State p) :
    let x := BootstrapPhysicalInput.blockInput p s incoming numerators hpos ids row rewards rho
    originalScalarActions x st t (roundCoordinates p t x.row)
        (fun i => BootstrapPhysicalInput.playerRoundScalarAt p rho i t) =
      BootstrapPhysicalBlock.actions x st t := by
  dsimp [originalScalarActions]
  rw [currentInputOf_originalScalar_blockInput]

/-- The same pointwise pullback identity holds for every player's actual
feedback, integer observation, and fixed-state protocol step. -/
theorem originalScalar_feedback_observation_step_blockInput
    (s : Fin (n_boot p)) (incoming : Finset (Follower p.m))
    (numerators : Fin (p.m - 1) → Fin p.K → ℕ)
    (hpos : ∀ (j : Fin (p.m - 1)) (a : Fin p.K),
      (1 : ℝ) ≤ BootstrapWeightPotential.weight (b_N p) (numerators j) a)
    (ids : CompletePublicTable.IDArray p) (row : CompletePublicTable.CompleteRow p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (rho : ExtendedPrivateCoordinates p) (t : Fin p.T)
    (st : BootstrapPhysicalBlock.State p) (i : Player p.m) :
    let x := BootstrapPhysicalInput.blockInput p s incoming numerators hpos ids row rewards rho
    (BootstrapPhysicalBlock.feedback
        (currentInputOf x t (roundCoordinates p t x.row)
          (roundPrivateValuesOfOriginalScalars x
            (fun q => BootstrapPhysicalInput.playerRoundScalarAt p rho q t))) st t i =
      BootstrapPhysicalBlock.feedback x st t i) ∧
    (BootstrapPhysicalBlock.observationIndex
        (currentInputOf x t (roundCoordinates p t x.row)
          (roundPrivateValuesOfOriginalScalars x
            (fun q => BootstrapPhysicalInput.playerRoundScalarAt p rho q t))) st t i =
      BootstrapPhysicalBlock.observationIndex x st t i) ∧
    (BootstrapPhysicalBlock.step
        (currentInputOf x t (roundCoordinates p t x.row)
          (roundPrivateValuesOfOriginalScalars x
            (fun q => BootstrapPhysicalInput.playerRoundScalarAt p rho q t))) st t =
      BootstrapPhysicalBlock.step x st t) := by
  dsimp only
  rw [currentInputOf_originalScalar_blockInput]
  exact ⟨rfl, rfl, rfl⟩

/-- The existing physical `dataStayPositive` indicator also pulls back
pointwise along the same original labelled scalars at an actual block input. -/
theorem originalScalar_dataStayPositive_blockInput
    (s : Fin (n_boot p)) (incoming : Finset (Follower p.m))
    (numerators : Fin (p.m - 1) → Fin p.K → ℕ)
    (hpos : ∀ (j : Fin (p.m - 1)) (a : Fin p.K),
      (1 : ℝ) ≤ BootstrapWeightPotential.weight (b_N p) (numerators j) a)
    (ids : CompletePublicTable.IDArray p) (row : CompletePublicTable.CompleteRow p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (rho : ExtendedPrivateCoordinates p) (t : Fin p.T)
    (st : BootstrapPhysicalBlock.State p) (j : {j // j ∈ incoming}) :
    let x := BootstrapPhysicalInput.blockInput p s incoming numerators hpos ids row rewards rho
    BootstrapStayAvoidance.dataStayPositive x st t j
      (roundCoordinates p t x.row)
      (roundPrivateValuesOfOriginalScalars x
        (fun i => BootstrapPhysicalInput.playerRoundScalarAt p rho i t)) =
      BootstrapStayAvoidance.dataStayPositive x st t j
        (roundCoordinates p t x.row)
        ((fun i => x.uniform i t),
          (x.coordinatorAvoid t, fun k => x.followerAvoid k t)) := by
  dsimp only
  rw [roundPrivateValuesOfOriginalScalars_blockInput]


end Bandits.Support.BootstrapOriginalScalarStep

end
