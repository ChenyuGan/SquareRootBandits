/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.BootstrapBlockConstruction
public import Bandits.Support.BootstrapBlockIsolation
public import Bandits.Support.CompletePublicTable
public import Bandits.Support.ContinuousCategorical
public import Bandits.Support.MeasurableLocalRollout

/-!
# Exogenous private source streams

This module constructs the finite-horizon private scalar inputs used for the
source bootstrap activation, held-arm, and private-ID draws, together with the
coordinator's separate scalar for the row index `J`. Public preprocessing
keeps its accepted `CompletePublicTable.publishedOutputMeasure`. At a fixed
public output and fixed reward matrix, the private law is the explicit product
of the follower/block scalar laws and the coordinator scalar law.

The scalars are exogenous inputs indexed by follower and calendar block. The
fixed-state sampler theorem below identifies its complete pushforward with the
accepted `BootstrapBlockConstruction.privateBlockDrawLaw`; nested product
maps and `BootstrapBlockIsolation` then give the full follower/block product
law. These inputs do not encode physical histories, adaptive conditional laws,
or causal protocol execution. The local-view adapter gives the coordinator
only its `J` scalar and gives each follower only that follower's block stream.
Sources: `sources/zip4/manuscript/07_public_setup.tex:11-38`,
`sources/zip4/manuscript/01_introduction.tex:19-36`, and
`sources/zip4/manuscript/08_main_theorem.tex:29-42`.
-/

public section

open MeasureTheory ProbabilityTheory Set
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.BootstrapWeightPotential
open Bandits.Support.BootstrapBlockConstruction
open Bandits.Support.BootstrapBlockIsolation
open Bandits.Support.ContinuousCategorical
open Bandits.Support.CompletePublicTable
open Bandits.Support.MeasurableLocalRollout
open Bandits.Support.FiniteBanditModel
open scoped BigOperators ENNReal

namespace Bandits.Support.PrivateSourceStreams

/-- A single genuine scalar input in the source half-open interval `[0,1)`. -/
abbrev Scalar := ContinuousCategorical.Scalar

/-- The three independently labelled scalar inputs for a follower/block pair:
coin first, held-arm second, and private-ID third. -/
abbrev BlockScalars := Scalar × Scalar × Scalar

/-- One follower's complete finite sequence of block-labelled inputs. -/
abbrev FollowerStream (p : Parameters) := Fin (n_boot p) → BlockScalars

/-- Scalar inputs for every follower and every calendar block, grouped first
by block and then by follower. Both labels remain explicit in the carrier. -/
abbrev FollowerBlockInputs (p : Parameters) :=
  Fin (n_boot p) → (Fin (p.m - 1) → BlockScalars)

/-- The result of one follower's source block coin, held-arm, and private-ID
draw. -/
abbrev BlockDraw (p : Parameters) := Bool × Fin p.K × Fin (A_id p)

/-- The simultaneous draw profile of all source followers in one block. -/
abbrev BlockDrawProfile (p : Parameters) := Fin (p.m - 1) → BlockDraw p

/-- All follower draw profiles over the finite bootstrap horizon. -/
abbrev BlockDrawProfiles (p : Parameters) := Fin (n_boot p) → BlockDrawProfile p

/-- One labelled product of three independent uniform half-open scalars. -/
@[expose] noncomputable def blockScalarsLaw : Measure BlockScalars :=
  ContinuousCategorical.uniform.prod
    (ContinuousCategorical.uniform.prod ContinuousCategorical.uniform)

instance blockScalarsLaw_probability : IsProbabilityMeasure blockScalarsLaw := by
  dsimp [blockScalarsLaw]
  infer_instance

/-- Product law for the follower-labelled triple inputs in a fixed calendar
block. -/
@[expose] noncomputable def blockScalarProfileLaw (p : Parameters) :
    Measure (Fin (p.m - 1) → BlockScalars) :=
  MeasurableLocalRollout.privateProfileLaw
    (m := p.m - 1) (fun _ : Fin (p.m - 1) => blockScalarsLaw)

instance blockScalarProfileLaw_probability (p : Parameters) :
    IsProbabilityMeasure (blockScalarProfileLaw p) := by
  exact MeasurableLocalRollout.privateProfileLaw_isProbabilityMeasure
    (fun _ : Fin (p.m - 1) => blockScalarsLaw)

/-- Product law for the full follower/block array, with independent labelled
block profiles and the three independent scalars inside each follower label. -/
@[expose] noncomputable def followerBlockInputsLaw (p : Parameters) :
    Measure (FollowerBlockInputs p) :=
  MeasurableLocalRollout.privateProfileLaw
    (m := n_boot p)
    (fun _ : Fin (n_boot p) => blockScalarProfileLaw p)

instance followerBlockInputsLaw_probability (p : Parameters) :
    IsProbabilityMeasure (followerBlockInputsLaw p) := by
  exact MeasurableLocalRollout.privateProfileLaw_isProbabilityMeasure
    (fun _ : Fin (n_boot p) => blockScalarProfileLaw p)

/-- The coordinator's separate genuine scalar source for `J`. -/
@[expose] noncomputable def coordinatorScalarLaw : Measure Scalar :=
  ContinuousCategorical.uniform

instance coordinatorScalarLaw_probability : IsProbabilityMeasure coordinatorScalarLaw := by
  dsimp [coordinatorScalarLaw]
  infer_instance

/-- Independent private source coordinates paired with all follower/block
inputs. The scalar for `J` is a separate final product factor. -/
abbrev PrivateCoordinates (p : Parameters) := FollowerBlockInputs p × Scalar

/-- The source parameter space includes the public output, all follower/block
inputs, and the coordinator scalar for `J`. -/
abbrev SourceInput (p : Parameters) :=
  (PublishedOutput p × FollowerBlockInputs p) × Scalar

/-- Product law of the follower/block inputs and the distinct coordinator
scalar. -/
@[expose] noncomputable def privateCoordinatesLaw (p : Parameters) :
    Measure (PrivateCoordinates p) :=
  followerBlockInputsLaw p |>.prod coordinatorScalarLaw

instance privateCoordinatesLaw_probability (p : Parameters) :
    IsProbabilityMeasure (privateCoordinatesLaw p) := by
  dsimp [privateCoordinatesLaw]
  infer_instance

/-- Full source law: accepted public preprocessing, followed by the explicit
product of private follower/block inputs and the coordinator's `J` scalar. -/
@[expose] noncomputable def sourceInputLaw (p : Parameters) : Measure (SourceInput p) :=
  (publishedOutputMeasure p |>.prod (followerBlockInputsLaw p)) |>.prod coordinatorScalarLaw

instance sourceInputLaw_probability (p : Parameters) :
    IsProbabilityMeasure (sourceInputLaw p) := by
  dsimp [sourceInputLaw]
  infer_instance

/-- The product law of private inputs after fixing any published output and
any source reward matrix. It includes no public randomness and no unused `J`
coordinate for a follower. -/
@[expose] noncomputable def fixedPublicPrivateLaw (p : Parameters)
    (_published : PublishedOutput p) (_rewards : RewardMatrix p.T p.K) :
    Measure (PrivateCoordinates p) :=
  privateCoordinatesLaw p

theorem fixedPublicPrivateLaw_eq_product (p : Parameters)
    (published : PublishedOutput p) (rewards : RewardMatrix p.T p.K) :
    fixedPublicPrivateLaw p published rewards =
      (followerBlockInputsLaw p).prod coordinatorScalarLaw := rfl

instance fixedPublicPrivateLaw_probability (p : Parameters)
    (published : PublishedOutput p) (rewards : RewardMatrix p.T p.K) :
    IsProbabilityMeasure (fixedPublicPrivateLaw p published rewards) := by
  change IsProbabilityMeasure (privateCoordinatesLaw p)
  infer_instance

/-- The published output coordinate of a full source input. -/
@[expose] def sourcePublishedOutput (p : Parameters) (x : SourceInput p) :
    PublishedOutput p := x.1.1

/-- The joint public-output and follower-input coordinate, before the
coordinator's separate scalar is drawn. -/
@[expose] def sourcePublicFollowerInputs (p : Parameters) (x : SourceInput p) :
    PublishedOutput p × FollowerBlockInputs p := x.1

/-- The scalar used to select `J`, after public preprocessing and rewards have
been fixed. -/
@[expose] def sourceCoordinatorScalar (p : Parameters) (x : SourceInput p) : Scalar := x.2

theorem measurable_sourcePublishedOutput (p : Parameters) :
    Measurable (sourcePublishedOutput p) :=
  measurable_fst.comp measurable_fst

theorem measurePreserving_sourcePublishedOutput (p : Parameters) :
    MeasurePreserving (sourcePublishedOutput p) (sourceInputLaw p)
      (publishedOutputMeasure p) := by
  have houter : MeasurePreserving (Prod.fst : SourceInput p →
      PublishedOutput p × FollowerBlockInputs p) (sourceInputLaw p)
      ((publishedOutputMeasure p).prod (followerBlockInputsLaw p)) := by
    exact measurePreserving_fst
  have hinner : MeasurePreserving (Prod.fst :
      PublishedOutput p × FollowerBlockInputs p → PublishedOutput p)
      ((publishedOutputMeasure p).prod (followerBlockInputsLaw p))
      (publishedOutputMeasure p) := by
    exact measurePreserving_fst
  exact hinner.comp houter

theorem map_sourcePublishedOutput (p : Parameters) :
    (sourceInputLaw p).map (sourcePublishedOutput p) = publishedOutputMeasure p :=
  (measurePreserving_sourcePublishedOutput p).map_eq

/-- The private product remaining when the published output is fixed. -/
@[expose] def sourcePrivateCoordinates (p : Parameters) (x : SourceInput p) :
    PrivateCoordinates p := (x.1.2, x.2)

theorem measurable_sourcePrivateCoordinates (p : Parameters) :
    Measurable (sourcePrivateCoordinates p) := by
  exact (measurable_snd.comp measurable_fst).prodMk measurable_snd

theorem map_sourcePrivateCoordinates (p : Parameters) :
    (sourceInputLaw p).map (sourcePrivateCoordinates p) = privateCoordinatesLaw p := by
  calc
    (sourceInputLaw p).map (sourcePrivateCoordinates p) =
        (((publishedOutputMeasure p).prod (followerBlockInputsLaw p)).map Prod.snd).prod
          (coordinatorScalarLaw.map id) := by
            change (((publishedOutputMeasure p).prod (followerBlockInputsLaw p)).prod
              coordinatorScalarLaw).map (Prod.map Prod.snd id) = _
            exact (Measure.map_prod_map
              (μa := (publishedOutputMeasure p).prod (followerBlockInputsLaw p))
              (μc := coordinatorScalarLaw) (f := Prod.snd) (g := id)
              measurable_snd measurable_id).symm
    _ = (followerBlockInputsLaw p).prod coordinatorScalarLaw := by
      rw [Measure.map_id]
      congr 1
      exact measurePreserving_snd.map_eq
    _ = privateCoordinatesLaw p := rfl

/-- The normalized uniform atom vector on the accepted row-index carrier. -/
@[expose] noncomputable def coordinatorIndexMass (p : Parameters) : Fin (M p) → ℝ :=
  fun _ => 1 / (M p : ℝ)

theorem coordinatorIndexMass_nonneg (p : Parameters) (j : Fin (M p)) :
    0 ≤ coordinatorIndexMass p j := by
  exact div_nonneg (by norm_num) (Nat.cast_nonneg _)

theorem coordinatorIndexMass_sum (p : Parameters) :
    (∑ j : Fin (M p), coordinatorIndexMass p j) = 1 := by
  change (∑ j : Fin (M p), 1 / (M p : ℝ)) = 1
  rw [← Finset.sum_div]
  have hsum : (∑ _j : Fin (M p), (1 : ℝ)) = (M p : ℝ) := by simp
  rw [hsum]
  exact div_self (Nat.cast_ne_zero.mpr (M_pos p).ne' : (M p : ℝ) ≠ 0)

/-- The accepted inverse-cumulative map from the coordinator's scalar to the
source row index `J`. -/
@[expose] noncomputable def coordinatorIndex (p : Parameters) : Scalar → Fin (M p) :=
  ContinuousCategorical.sample (M_pos p) (coordinatorIndexMass p)
    (coordinatorIndexMass_sum p)

theorem measurable_coordinatorIndex (p : Parameters) :
    Measurable (coordinatorIndex p) := by
  exact ContinuousCategorical.measurable_sample (M_pos p)
    (coordinatorIndexMass_nonneg p) (coordinatorIndexMass_sum p)

theorem coordinatorIndex_uniform_atom (p : Parameters) (j : Fin (M p)) :
    ContinuousCategorical.uniform (coordinatorIndex p ⁻¹' {j}) =
      ENNReal.ofReal (1 / (M p : ℝ)) := by
  unfold coordinatorIndex
  exact ContinuousCategorical.uniform_sample_singleton (M_pos p)
    (coordinatorIndexMass_nonneg p) (coordinatorIndexMass_sum p) j

theorem coordinatorIndex_uniform_map (p : Parameters) :
    ContinuousCategorical.uniform.map (coordinatorIndex p) =
      (ContinuousCategorical.massPMF (coordinatorIndexMass p)
        (coordinatorIndexMass_nonneg p) (coordinatorIndexMass_sum p)).toMeasure :=
  ContinuousCategorical.uniform_map_sample (M_pos p)
    (coordinatorIndexMass_nonneg p) (coordinatorIndexMass_sum p)

theorem coordinatorIndex_uniform_map_atom (p : Parameters) (j : Fin (M p)) :
    (ContinuousCategorical.uniform.map (coordinatorIndex p)) {j} =
      ENNReal.ofReal (1 / (M p : ℝ)) := by
  rw [Measure.map_apply (measurable_coordinatorIndex p) (measurableSet_singleton j),
    coordinatorIndex_uniform_atom]

/-- The per-block private activity coin, realized from its own uniform scalar.
Its true threshold is exactly the source mean `1/m`. -/
@[expose] noncomputable def activityScalarDraw (p : Parameters) (v : Scalar) : Bool :=
  decide (v.val < 1 / (p.m : ℝ))

theorem activityScalarDraw_measurable (p : Parameters) :
    Measurable (activityScalarDraw p) := by
  apply measurable_to_countable'
  intro b
  cases b with
  | false =>
      have hset : activityScalarDraw p ⁻¹' {false} =
          Subtype.val ⁻¹' Ico (1 / (p.m : ℝ)) 1 := by
        ext v
        simp only [Set.mem_preimage, Set.mem_singleton_iff, activityScalarDraw,
          decide_eq_false_iff_not, Set.mem_Ico]
        exact ⟨fun h => ⟨le_of_not_gt h, v.property.2⟩,
          fun h => not_lt.mpr h.1⟩
      rw [hset]
      exact measurableSet_Ico.preimage measurable_subtype_coe
  | true =>
      have hset : activityScalarDraw p ⁻¹' {true} =
          Subtype.val ⁻¹' Ico 0 (1 / (p.m : ℝ)) := by
        ext v
        simp only [Set.mem_preimage, Set.mem_singleton_iff, activityScalarDraw,
          decide_eq_true_eq, Set.mem_Ico]
        exact ⟨fun h => ⟨v.property.1, h⟩, fun h => h.2⟩
      rw [hset]
      exact measurableSet_Ico.preimage measurable_subtype_coe

theorem activityScalarDraw_uniform_mass (p : Parameters) (b : Bool) :
    ContinuousCategorical.uniform (activityScalarDraw p ⁻¹' {b}) =
      ENNReal.ofReal (activityProbability p b) := by
  have hmpos : (0 : ℝ) < (p.m : ℝ) := Nat.cast_pos.mpr (m_pos p)
  have hmltNat : 1 < p.m := lt_of_lt_of_le (by decide) p.two_le_m
  have hmlt : (1 : ℝ) < (p.m : ℝ) := by exact_mod_cast hmltNat
  have hinv_nonneg : (0 : ℝ) ≤ 1 / (p.m : ℝ) := (one_div_pos.mpr hmpos).le
  have hinv_lt_one : 1 / (p.m : ℝ) < 1 := by
    rw [div_lt_one hmpos]
    exact hmlt
  cases b with
  | false =>
      rw [show activityScalarDraw p ⁻¹' {false} =
        Subtype.val ⁻¹' Ico (1 / (p.m : ℝ)) 1 by
          ext v
          simp only [Set.mem_preimage, Set.mem_singleton_iff, activityScalarDraw,
            decide_eq_false_iff_not, Set.mem_Ico]
          exact ⟨fun h => ⟨le_of_not_gt h, v.property.2⟩,
            fun h => not_lt.mpr h.1⟩]
      rw [ContinuousCategorical.uniform_preimage_val]
      have hinter : Ico (1 / (p.m : ℝ)) 1 ∩ Ico 0 1 =
          Ico (1 / (p.m : ℝ)) 1 := by
        ext x
        simp only [Set.mem_inter_iff, Set.mem_Ico]
        constructor
        · rintro ⟨⟨hlo, hhi⟩, _⟩
          exact ⟨hlo, hhi⟩
        · intro h
          exact ⟨h, ⟨hinv_nonneg.trans h.1, h.2⟩⟩
      rw [hinter, Real.volume_Ico]
      simp only [activityProbability, Bool.false_eq_true, ↓reduceIte]
  | true =>
      rw [show activityScalarDraw p ⁻¹' {true} =
        Subtype.val ⁻¹' Ico 0 (1 / (p.m : ℝ)) by
          ext v
          simp only [Set.mem_preimage, Set.mem_singleton_iff, activityScalarDraw,
            decide_eq_true_eq, Set.mem_Ico]
          exact ⟨fun h => ⟨v.property.1, h⟩, fun h => h.2⟩]
      rw [ContinuousCategorical.uniform_preimage_val]
      have hinter : Ico 0 (1 / (p.m : ℝ)) ∩ Ico 0 1 =
          Ico 0 (1 / (p.m : ℝ)) := by
        ext x
        simp only [Set.mem_inter_iff, Set.mem_Ico]
        constructor
        · rintro ⟨h, _⟩
          exact h
        · intro h
          exact ⟨h, ⟨le_trans (by norm_num) h.1, h.2.trans hinv_lt_one⟩⟩
      rw [hinter, Real.volume_Ico]
      simp only [sub_zero, activityProbability, ↓reduceIte]

/-- The held-arm draw uses the current explicit positive numerator state and
the accepted bootstrap mixture, sampled by the continuous categorical map. -/
@[expose] noncomputable def heldArmScalarDraw (p : Parameters)
    (n : Fin p.K → ℕ) (hn : ∀ a, 1 ≤ weight (b_N p) n a) (v : Scalar) : Fin p.K :=
  ContinuousCategorical.sample (K_pos p)
    (fun a => probability (b_N p) n a) (heldArmProbability_sum p n hn) v

theorem measurable_heldArmScalarDraw (p : Parameters) (n : Fin p.K → ℕ)
    (hn : ∀ a, 1 ≤ weight (b_N p) n a) :
    Measurable (heldArmScalarDraw p n hn) := by
  exact ContinuousCategorical.measurable_sample (K_pos p)
    (fun a => (probability_pos (K_pos p) n a).le)
    (heldArmProbability_sum p n hn)

theorem heldArmScalarDraw_uniform_atom (p : Parameters) (n : Fin p.K → ℕ)
    (hn : ∀ a, 1 ≤ weight (b_N p) n a) (a : Fin p.K) :
    ContinuousCategorical.uniform (heldArmScalarDraw p n hn ⁻¹' {a}) =
      ENNReal.ofReal (probability (b_N p) n a) := by
  exact ContinuousCategorical.uniform_sample_singleton (K_pos p)
    (fun j => (probability_pos (K_pos p) n j).le)
    (heldArmProbability_sum p n hn) a

/-- Uniform private-ID draw on the full source alphabet. -/
@[expose] noncomputable def privateIDScalarDraw (p : Parameters) (v : Scalar) :
    Fin (A_id p) :=
  ContinuousCategorical.sample (A_id_pos p)
    (privateIdProbability p) (privateIdProbability_sum p) v

theorem measurable_privateIDScalarDraw (p : Parameters) :
    Measurable (privateIDScalarDraw p) := by
  exact ContinuousCategorical.measurable_sample (A_id_pos p)
    (fun _ => (one_div_pos.mpr (Nat.cast_pos.mpr (A_id_pos p))).le)
    (privateIdProbability_sum p)

theorem privateIDScalarDraw_uniform_atom (p : Parameters) (u : Fin (A_id p)) :
    ContinuousCategorical.uniform (privateIDScalarDraw p ⁻¹' {u}) =
      ENNReal.ofReal (privateIdProbability p u) := by
  exact ContinuousCategorical.uniform_sample_singleton (A_id_pos p)
    (fun _ => (one_div_pos.mpr (Nat.cast_pos.mpr (A_id_pos p))).le)
    (privateIdProbability_sum p) u

/-- One follower's block draw from the three labelled scalars. The held-arm
positivity premise is precisely the accepted weight-at-least-one premise. -/
@[expose] noncomputable def privateBlockDrawMap (p : Parameters)
    (n : Fin p.K → ℕ) (hn : ∀ a, 1 ≤ weight (b_N p) n a)
    (x : BlockScalars) : BlockDraw p :=
  (activityScalarDraw p x.1,
    heldArmScalarDraw p n hn x.2.1,
    privateIDScalarDraw p x.2.2)

theorem measurable_privateBlockDrawMap (p : Parameters) (n : Fin p.K → ℕ)
    (hn : ∀ a, 1 ≤ weight (b_N p) n a) :
    Measurable (privateBlockDrawMap p n hn) := by
  exact (activityScalarDraw_measurable p).comp measurable_fst |>.prodMk
    ((measurable_heldArmScalarDraw p n hn).comp
        (measurable_fst.comp measurable_snd) |>.prodMk
      ((measurable_privateIDScalarDraw p).comp (measurable_snd.comp measurable_snd)))

theorem privateBlockDrawMap_law (p : Parameters) (n : Fin p.K → ℕ)
    (hn : ∀ a, 1 ≤ weight (b_N p) n a) :
    (blockScalarsLaw.map (privateBlockDrawMap p n hn)) =
      (privateBlockDrawLaw p n hn).toMeasure := by
  classical
  apply Measure.ext_of_singleton
  intro outcome
  have hpreimage : privateBlockDrawMap p n hn ⁻¹' {outcome} =
      {x : Scalar | activityScalarDraw p x = outcome.1} ×ˢ
        ({x : Scalar | heldArmScalarDraw p n hn x = outcome.2.1} ×ˢ
          {x : Scalar | privateIDScalarDraw p x = outcome.2.2}) := by
    ext x
    change (activityScalarDraw p x.1, (heldArmScalarDraw p n hn x.2.1,
        privateIDScalarDraw p x.2.2)) = outcome ↔
      (activityScalarDraw p x.1 = outcome.1 ∧
        (heldArmScalarDraw p n hn x.2.1 = outcome.2.1 ∧
          privateIDScalarDraw p x.2.2 = outcome.2.2))
    constructor
    · intro h
      have hcoin : activityScalarDraw p x.1 = outcome.1 := congrArg Prod.fst h
      have htail : (heldArmScalarDraw p n hn x.2.1, privateIDScalarDraw p x.2.2) =
          outcome.2 := congrArg Prod.snd h
      have harm : heldArmScalarDraw p n hn x.2.1 = outcome.2.1 :=
        congrArg Prod.fst htail
      have hid : privateIDScalarDraw p x.2.2 = outcome.2.2 := congrArg Prod.snd htail
      exact ⟨hcoin, harm, hid⟩
    · rintro ⟨hcoin, harm, hid⟩
      exact Prod.ext hcoin (Prod.ext harm hid)
  change (Measure.map (privateBlockDrawMap p n hn)
      (ContinuousCategorical.uniform.prod
        (ContinuousCategorical.uniform.prod ContinuousCategorical.uniform)))
        {outcome} = _
  have hcoinSet : {x : Scalar | activityScalarDraw p x = outcome.1} =
      activityScalarDraw p ⁻¹' {outcome.1} := by
    ext x
    rfl
  have harmSet : {x : Scalar | heldArmScalarDraw p n hn x = outcome.2.1} =
      heldArmScalarDraw p n hn ⁻¹' {outcome.2.1} := by
    ext x
    rfl
  have hidSet : {x : Scalar | privateIDScalarDraw p x = outcome.2.2} =
      privateIDScalarDraw p ⁻¹' {outcome.2.2} := by
    ext x
    rfl
  rw [Measure.map_apply (measurable_privateBlockDrawMap p n hn)
      (measurableSet_singleton outcome), hpreimage, Measure.prod_prod, Measure.prod_prod,
    hcoinSet, harmSet, hidSet,
    activityScalarDraw_uniform_mass, heldArmScalarDraw_uniform_atom,
    privateIDScalarDraw_uniform_atom,
    PMF.toMeasure_apply_singleton (privateBlockDrawLaw p n hn) outcome
      (measurableSet_singleton outcome), privateBlockDrawLaw_apply]
  have hcoin := activityProbability_nonneg p outcome.1
  have harm :=
    (BootstrapWeightPotential.probability_pos (b := b_N p) (K_pos p) n outcome.2.1).le
  change ENNReal.ofReal (activityProbability p outcome.1) *
      (ENNReal.ofReal (probability (b_N p) n outcome.2.1) *
        ENNReal.ofReal (privateIdProbability p outcome.2.2)) =
    ENNReal.ofReal
      ((activityProbability p outcome.1 * probability (b_N p) n outcome.2.1) *
        privateIdProbability p outcome.2.2)
  calc
    _ = (ENNReal.ofReal (activityProbability p outcome.1) *
        ENNReal.ofReal (probability (b_N p) n outcome.2.1)) *
          ENNReal.ofReal (privateIdProbability p outcome.2.2) := by
            rw [← mul_assoc]
    _ = _ := by
      rw [ENNReal.ofReal_mul (mul_nonneg hcoin harm),
        ENNReal.ofReal_mul hcoin]

/-- The accepted isolation profile PMF, as a measure, is exactly the product
of the accepted one-follower block laws. -/
theorem privateBlockProfileLaw_toMeasure_eq_pi (p : Parameters)
    (n : Fin (p.m - 1) → Fin p.K → ℕ)
    (hn : ∀ (i : Fin (p.m - 1)) (a : Fin p.K),
      (1 : ℝ) ≤ weight (b_N p) (n i) a) :
    (BootstrapBlockIsolation.privateBlockProfileLaw p n hn).toMeasure =
      Measure.pi (fun i : Fin (p.m - 1) =>
        (privateBlockDrawLaw p (n i) (hn i)).toMeasure) := by
  classical
  apply Measure.ext_of_singleton
  intro profile
  have hset : ({profile} : Set (Fin (p.m - 1) → BlockDraw p)) =
      Set.univ.pi (fun i => {profile i}) := by
    ext x
    simp only [Set.mem_singleton_iff, Set.mem_pi, Set.mem_univ,
      true_implies]
    exact ⟨fun h => h ▸ fun _ => rfl, fun h => funext h⟩
  rw [PMF.toMeasure_apply_singleton _ profile (measurableSet_singleton profile),
    BootstrapBlockIsolation.privateBlockProfileLaw_apply, hset, Measure.pi_pi]
  congr 1
  funext i
  exact (PMF.toMeasure_apply_singleton
    (privateBlockDrawLaw p (n i) (hn i)) (profile i)
    (measurableSet_singleton (profile i))).symm

/-- The blockwise map from all follower-labelled triples to the simultaneous
follower draw profile. -/
@[expose] noncomputable def blockDrawProfileMap (p : Parameters)
    (n : Fin (p.m - 1) → Fin p.K → ℕ)
    (hn : ∀ (i : Fin (p.m - 1)) (a : Fin p.K),
      (1 : ℝ) ≤ weight (b_N p) (n i) a)
    (x : Fin (p.m - 1) → BlockScalars) : BlockDrawProfile p :=
  fun i => privateBlockDrawMap p (n i) (hn i) (x i)

theorem measurable_blockDrawProfileMap (p : Parameters)
    (n : Fin (p.m - 1) → Fin p.K → ℕ)
    (hn : ∀ (i : Fin (p.m - 1)) (a : Fin p.K),
      (1 : ℝ) ≤ weight (b_N p) (n i) a) :
    Measurable (blockDrawProfileMap p n hn) := by
  apply measurable_pi_iff.mpr
  intro i
  exact (measurable_privateBlockDrawMap p (n i) (hn i)).comp
    (measurable_pi_apply i)

/-- For each fixed vector of existing positive weight states, the entire
follower profile pushforward equals the accepted `BootstrapBlockIsolation`
product law. -/
theorem blockDrawProfileMap_law (p : Parameters)
    (n : Fin (p.m - 1) → Fin p.K → ℕ)
    (hn : ∀ (i : Fin (p.m - 1)) (a : Fin p.K),
      (1 : ℝ) ≤ weight (b_N p) (n i) a) :
    (blockScalarProfileLaw p).map (blockDrawProfileMap p n hn) =
      (BootstrapBlockIsolation.privateBlockProfileLaw p n hn).toMeasure := by
  calc
    (blockScalarProfileLaw p).map (blockDrawProfileMap p n hn) =
        Measure.pi (fun i : Fin (p.m - 1) =>
          blockScalarsLaw.map (privateBlockDrawMap p (n i) (hn i))) := by
            change (Measure.pi (fun _ : Fin (p.m - 1) => blockScalarsLaw)).map _ = _
            exact Measure.pi_map_pi (fun i =>
              (measurable_privateBlockDrawMap p (n i) (hn i)).aemeasurable)
    _ = Measure.pi (fun i : Fin (p.m - 1) =>
          (privateBlockDrawLaw p (n i) (hn i)).toMeasure) := by
            congr 1
            funext i
            exact privateBlockDrawMap_law p (n i) (hn i)
    _ = (BootstrapBlockIsolation.privateBlockProfileLaw p n hn).toMeasure :=
          (privateBlockProfileLaw_toMeasure_eq_pi p n hn).symm

/-- Map all labelled scalar inputs through their fixed-state block samplers.
The states and their visible positivity proof are inputs; this is not an
adaptive conditional draw law. -/
@[expose] noncomputable def followerBlockDrawMap (p : Parameters)
    (n : Fin (n_boot p) → Fin (p.m - 1) → Fin p.K → ℕ)
    (hn : ∀ (s : Fin (n_boot p)) (i : Fin (p.m - 1)) (a : Fin p.K),
      (1 : ℝ) ≤ weight (b_N p) (n s i) a)
    (x : FollowerBlockInputs p) : BlockDrawProfiles p :=
  fun s => blockDrawProfileMap p (n s) (hn s) (x s)

theorem measurable_followerBlockDrawMap (p : Parameters)
    (n : Fin (n_boot p) → Fin (p.m - 1) → Fin p.K → ℕ)
    (hn : ∀ (s : Fin (n_boot p)) (i : Fin (p.m - 1)) (a : Fin p.K),
      (1 : ℝ) ≤ weight (b_N p) (n s i) a) :
    Measurable (followerBlockDrawMap p n hn) := by
  apply measurable_pi_iff.mpr
  intro s
  exact (measurable_blockDrawProfileMap p (n s) (hn s)).comp
    (measurable_pi_apply s)

/-- The complete finite-horizon pushforward is the product over block labels
of the accepted follower isolation laws. Independence across calendar blocks
is derived from the distinct product coordinates. -/
theorem followerBlockDrawMap_law (p : Parameters)
    (n : Fin (n_boot p) → Fin (p.m - 1) → Fin p.K → ℕ)
    (hn : ∀ (s : Fin (n_boot p)) (i : Fin (p.m - 1)) (a : Fin p.K),
      (1 : ℝ) ≤ weight (b_N p) (n s i) a) :
    (followerBlockInputsLaw p).map (followerBlockDrawMap p n hn) =
      Measure.pi (fun s : Fin (n_boot p) =>
        (BootstrapBlockIsolation.privateBlockProfileLaw p (n s) (hn s)).toMeasure) := by
  calc
    (followerBlockInputsLaw p).map (followerBlockDrawMap p n hn) =
        Measure.pi (fun s : Fin (n_boot p) =>
          (blockScalarProfileLaw p).map (blockDrawProfileMap p (n s) (hn s))) := by
            change (Measure.pi (fun _ : Fin (n_boot p) => blockScalarProfileLaw p)).map _ = _
            exact Measure.pi_map_pi (fun s =>
              (measurable_blockDrawProfileMap p (n s) (hn s)).aemeasurable)
    _ = _ := by
      congr 1
      funext s
      exact blockDrawProfileMap_law p (n s) (hn s)

/-- At a fixed block, the scalar-labelled follower draws are independent as a
consequence of their `Measure.pi` input law. -/
theorem independent_followers_at_block (p : Parameters)
    (n : Fin (p.m - 1) → Fin p.K → ℕ)
    (hn : ∀ (i : Fin (p.m - 1)) (a : Fin p.K),
      (1 : ℝ) ≤ weight (b_N p) (n i) a) :
    iIndepFun (fun i x => privateBlockDrawMap p (n i) (hn i) (x i))
      (blockScalarProfileLaw p) := by
  change iIndepFun
    (fun i x => privateBlockDrawMap p (n i) (hn i) (x i))
    (Measure.pi (fun _ : Fin (p.m - 1) => blockScalarsLaw))
  exact iIndepFun_pi (fun i =>
    (measurable_privateBlockDrawMap p (n i) (hn i)).aemeasurable)

/-- Simultaneous follower profiles in distinct calendar blocks are independent
because their source block labels are distinct product coordinates. -/
theorem independent_calendarBlocks (p : Parameters)
    (n : Fin (n_boot p) → Fin (p.m - 1) → Fin p.K → ℕ)
    (hn : ∀ (s : Fin (n_boot p)) (i : Fin (p.m - 1)) (a : Fin p.K),
      (1 : ℝ) ≤ weight (b_N p) (n s i) a) :
    iIndepFun (fun s x => blockDrawProfileMap p (n s) (hn s) (x s))
      (followerBlockInputsLaw p) := by
  change iIndepFun
    (fun s x => blockDrawProfileMap p (n s) (hn s) (x s))
    (Measure.pi (fun _ : Fin (n_boot p) => blockScalarProfileLaw p))
  exact iIndepFun_pi (fun s =>
    (measurable_blockDrawProfileMap p (n s) (hn s)).aemeasurable)

/-- Fixed public data and rewards leave the exact finite-horizon product
pushforward of all follower block draws unchanged. -/
theorem fixedPublic_followerBlockDrawMap_law (p : Parameters)
    (published : PublishedOutput p) (rewards : RewardMatrix p.T p.K)
    (n : Fin (n_boot p) → Fin (p.m - 1) → Fin p.K → ℕ)
    (hn : ∀ (s : Fin (n_boot p)) (i : Fin (p.m - 1)) (a : Fin p.K),
      (1 : ℝ) ≤ weight (b_N p) (n s i) a) :
    ((fixedPublicPrivateLaw p published rewards).map
      (fun x : PrivateCoordinates p => followerBlockDrawMap p n hn x.1)) =
        Measure.pi (fun s : Fin (n_boot p) =>
          (BootstrapBlockIsolation.privateBlockProfileLaw p (n s) (hn s)).toMeasure) := by
  have hfst : MeasurePreserving (Prod.fst : PrivateCoordinates p →
      FollowerBlockInputs p) (fixedPublicPrivateLaw p published rewards)
      (followerBlockInputsLaw p) := by
    rw [fixedPublicPrivateLaw_eq_product]
    exact measurePreserving_fst
  calc
    (fixedPublicPrivateLaw p published rewards).map
        (fun x : PrivateCoordinates p => followerBlockDrawMap p n hn x.1) =
      ((fixedPublicPrivateLaw p published rewards).map Prod.fst).map
        (followerBlockDrawMap p n hn) := by
          exact (Measure.map_map (measurable_followerBlockDrawMap p n hn)
            measurable_fst).symm
    _ = (followerBlockInputsLaw p).map (followerBlockDrawMap p n hn) := by
      rw [hfst.map_eq]
    _ = _ := followerBlockDrawMap_law p n hn

/-- The J atom law is the exact finite uniform law obtained from the accepted
inverse-CDF sampler, rather than a finite random variable assumed uniform. -/
theorem fixedPublic_coordinatorIndexLaw (p : Parameters)
    (published : PublishedOutput p) (rewards : RewardMatrix p.T p.K) :
    (fixedPublicPrivateLaw p published rewards).map
      (fun x : PrivateCoordinates p => coordinatorIndex p x.2) =
        ContinuousCategorical.uniform.map (coordinatorIndex p) := by
  have hsnd : MeasurePreserving (Prod.snd : PrivateCoordinates p → Scalar)
      (fixedPublicPrivateLaw p published rewards) coordinatorScalarLaw := by
    rw [fixedPublicPrivateLaw_eq_product]
    exact measurePreserving_snd
  have hscalar : MeasurePreserving (coordinatorIndex p)
      coordinatorScalarLaw (ContinuousCategorical.uniform.map (coordinatorIndex p)) :=
    ⟨measurable_coordinatorIndex p, rfl⟩
  exact (hscalar.comp hsnd).map_eq

/-- After fixing public preprocessing and rewards, every row index has its
exact uniform atom probability. -/
theorem fixedPublic_coordinatorIndex_uniform_atom (p : Parameters)
    (published : PublishedOutput p) (rewards : RewardMatrix p.T p.K)
    (j : Fin (M p)) :
    (fixedPublicPrivateLaw p published rewards).map
        (fun x : PrivateCoordinates p => coordinatorIndex p x.2) {j} =
      ENNReal.ofReal (1 / (M p : ℝ)) := by
  rw [fixedPublic_coordinatorIndexLaw, coordinatorIndex_uniform_map_atom]

/-- Joint independence of the coordinator's `J` draw from all public
preprocessing and every follower/block input. The independent pair is the
entire public output together with the full follower input array. -/
theorem coordinatorIndex_independent_publicAndFollowerInputs (p : Parameters) :
    (sourcePublicFollowerInputs p) ⟂ᵢ[sourceInputLaw p]
        (fun x => coordinatorIndex p (sourceCoordinatorScalar p x)) := by
  change (fun x : SourceInput p => x.1) ⟂ᵢ[sourceInputLaw p]
    (fun x => coordinatorIndex p x.2)
  change (fun x : (PublishedOutput p × FollowerBlockInputs p) × Scalar => x.1) ⟂ᵢ[
    ((publishedOutputMeasure p).prod (followerBlockInputsLaw p)).prod coordinatorScalarLaw]
    (fun x => coordinatorIndex p x.2)
  exact indepFun_prod (X := id) (Y := coordinatorIndex p)
    measurable_id (measurable_coordinatorIndex p)

/-- The exact law of `J` under the full source law is still the inverse-CDF
uniform law; it is not included in public preprocessing. -/
theorem sourceCoordinatorIndexLaw (p : Parameters) :
    (sourceInputLaw p).map
      (fun x : SourceInput p => coordinatorIndex p (sourceCoordinatorScalar p x)) =
        ContinuousCategorical.uniform.map (coordinatorIndex p) := by
  have hsnd : MeasurePreserving (Prod.snd : SourceInput p → Scalar)
      (sourceInputLaw p) coordinatorScalarLaw := by
    change MeasurePreserving Prod.snd
      (((publishedOutputMeasure p).prod (followerBlockInputsLaw p)).prod
        coordinatorScalarLaw) coordinatorScalarLaw
    exact measurePreserving_snd
  have hscalar : MeasurePreserving (coordinatorIndex p)
      coordinatorScalarLaw (ContinuousCategorical.uniform.map (coordinatorIndex p)) :=
    ⟨measurable_coordinatorIndex p, rfl⟩
  exact (hscalar.comp hsnd).map_eq

/-- Each player receives a role-tagged local input: only the coordinator's
variant contains the separate `J` scalar, and follower variants contain only
that follower's own block stream. -/
abbrev PlayerPrivateInput (p : Parameters) := Scalar ⊕ FollowerStream p

/-- The source follower label belonging to a player label. This total map is
used only in the follower branch of the local-view projection. -/
@[expose] def followerIndexOfPlayer (p : Parameters) (i : Fin p.m) : Fin (p.m - 1) :=
  ⟨i.val - 1, by
    have hi := i.isLt
    have hm := p.two_le_m
    omega⟩

/-- The local private input visible to player `i` in a full source input. -/
@[expose] def sourcePlayerPrivateInput (p : Parameters) (i : Fin p.m)
    (x : SourceInput p) : PlayerPrivateInput p :=
  if i.val = 0 then Sum.inl (sourceCoordinatorScalar p x)
  else Sum.inr (fun s => x.1.2 s (followerIndexOfPlayer p i))

theorem sourcePlayerPrivateInput_coordinator (p : Parameters) (x : SourceInput p) :
    sourcePlayerPrivateInput p ⟨0, m_pos p⟩ x = Sum.inl (sourceCoordinatorScalar p x) := by
  simp [sourcePlayerPrivateInput]

theorem sourcePlayerPrivateInput_follower (p : Parameters) (i : Fin (p.m - 1))
    (x : SourceInput p) :
    sourcePlayerPrivateInput p ⟨i.val + 1, by omega⟩ x =
      Sum.inr (fun s => x.1.2 s i) := by
  have hi_lt := i.isLt
  have hindex : followerIndexOfPlayer p ⟨i.val + 1, by omega⟩ = i := by
    apply Fin.ext
    simp only [followerIndexOfPlayer]
    omega
  simp [sourcePlayerPrivateInput, hindex]

theorem measurable_sourcePlayerPrivateInput (p : Parameters) (i : Fin p.m) :
    Measurable (sourcePlayerPrivateInput p i) := by
  by_cases hcoord : i.val = 0
  · have hview : sourcePlayerPrivateInput p i =
        fun x : SourceInput p => Sum.inl (sourceCoordinatorScalar p x) := by
      funext x
      simp [sourcePlayerPrivateInput, hcoord]
    rw [hview]
    exact (measurable_inl :
      Measurable (@Sum.inl Scalar (FollowerStream p))).comp
      measurable_snd
  · have hview : sourcePlayerPrivateInput p i =
        fun x : SourceInput p => Sum.inr (fun s => x.1.2 s (followerIndexOfPlayer p i)) := by
      funext x
      simp [sourcePlayerPrivateInput, hcoord]
    rw [hview]
    apply (measurable_inr :
      Measurable (@Sum.inr Scalar (FollowerStream p))).comp
    apply measurable_pi_iff.mpr
    intro s
    exact (measurable_pi_apply (followerIndexOfPlayer p i)).comp
      ((measurable_pi_apply s).comp (measurable_snd.comp measurable_fst))

/-- The module's source input represented in the accepted local-rollout
parameter carrier, with one tagged private input per player. -/
@[expose] def sourceRolloutParameter (p : Parameters) (x : SourceInput p) :
    MeasurableLocalRollout.RolloutParameter p.m (PublishedOutput p)
      (PlayerPrivateInput p) :=
  (sourcePublishedOutput p x, fun i => sourcePlayerPrivateInput p i x)

theorem measurable_sourceRolloutParameter (p : Parameters) :
    Measurable (sourceRolloutParameter p) := by
  exact (measurable_sourcePublishedOutput p).prodMk (measurable_pi_iff.mpr fun i =>
    measurable_sourcePlayerPrivateInput p i)

theorem sourceRolloutParameter_public_law (p : Parameters) :
    (sourceInputLaw p).map (fun x => (sourceRolloutParameter p x).1) =
      publishedOutputMeasure p := by
  change (sourceInputLaw p).map (sourcePublishedOutput p) = _
  exact map_sourcePublishedOutput p

end Bandits.Support.PrivateSourceStreams

end
