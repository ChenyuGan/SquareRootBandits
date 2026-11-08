/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.PrivateSourceStreams
public import Mathlib.MeasureTheory.Constructions.Pi

import Mathlib.Tactic.FieldSimp

/-!
# Private bootstrap round and coordinator target streams

This module extends the accepted `PrivateSourceStreams` law by one fresh
uniform scalar for every `(player, calendar round)` label and a separate
uniform scalar for each coordinator block target.  It preserves the accepted
public-output measure and the entire existing product of follower block
triples and the coordinator's `J` scalar.

Each player-round scalar is used only by whichever mutually exclusive source
branch is active at that round: coordinator UP or DATA avoidance, and follower
inactive uniform or active ID-one avoidance.  These alternatives do not get
separate random coordinates.  The block target scalars are separately labelled
and available only in the coordinator local view.

Fixed forbidden-arm vectors are deterministic inputs to the product theorem.
That theorem does not assert independence after a forbidden arm is selected
adaptively from a state history, and these coordinates do not implement or
certify physical play, observations, or causal protocol execution.

Sources: `sources/zip4/manuscript/07_public_setup.tex:27-38,61-94`,
`sources/zip4/manuscript/appendix_b_communication.tex:398-432`, and
`sources/zip4/manuscript/01_introduction.tex:19-36`.
-/

public section

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.ContinuousCategorical
open Bandits.Support.PrivateSourceStreams
open Bandits.Support.CompletePublicTable
open Bandits.Support.FiniteBanditModel

namespace Bandits.Support.BootstrapPrivateRoundStreams

/-- The shared scalar carrier is the accepted genuine half-open interval. -/
abbrev Scalar := ContinuousCategorical.Scalar

/-- One scalar coordinate, indexed by both its player and calendar round. -/
abbrev PlayerRoundLabel (p : Parameters) := Fin p.m × Fin p.T

/-- All genuine `[0,1)` player-round scalar coordinates. -/
abbrev PlayerRoundScalars (p : Parameters) := PlayerRoundLabel p → Scalar

/-- One separately labelled coordinator scalar for each bootstrap block. -/
abbrev CoordinatorTargetScalars (p : Parameters) := Fin (n_boot p) → Scalar

/-- The source carrier after adjoining player-round and target scalars to the
accepted `PrivateSourceStreams.PrivateCoordinates`. -/
abbrev ExtendedPrivateCoordinates (p : Parameters) :=
  PrivateCoordinates p × (PlayerRoundScalars p × CoordinatorTargetScalars p)

/-- The full source carrier, with the accepted published output retained as
the first coordinate. -/
abbrev SourceInput (p : Parameters) :=
  PublishedOutput p × ExtendedPrivateCoordinates p

/-- A follower's calendar-round view of its own fresh scalar labels. -/
abbrev PlayerRoundScalarStream (p : Parameters) := Fin p.T → Scalar

/-- The coordinator's block target arms after applying the inverse-CDF map. -/
abbrev CoordinatorTargetArms (p : Parameters) := Fin (n_boot p) → Fin p.K

/-- The actual arm label in the increasing complement of a fixed forbidden
arm. -/
abbrev ArmAvoiding (p : Parameters) (a : Fin p.K) := {b : Fin p.K // b ≠ a}

/-- The full vector of arms selected by fixed forbidden arms. -/
abbrev ArmAvoidingVector (p : Parameters)
    (forbidden : PlayerRoundLabel p → Fin p.K) :=
  (label : PlayerRoundLabel p) → ArmAvoiding p (forbidden label)

/-- Product law of the distinct player-round scalar coordinates. -/
@[expose] noncomputable def playerRoundScalarLaw (p : Parameters) :
    Measure (PlayerRoundScalars p) :=
  Measure.pi (fun _ : PlayerRoundLabel p => ContinuousCategorical.uniform)

instance playerRoundScalarLaw_probability (p : Parameters) :
    IsProbabilityMeasure (playerRoundScalarLaw p) := by
  change IsProbabilityMeasure
    (Measure.pi (fun _ : PlayerRoundLabel p => ContinuousCategorical.uniform))
  infer_instance

/-- Product law of the separate coordinator target scalar coordinates. -/
@[expose] noncomputable def coordinatorTargetScalarLaw (p : Parameters) :
    Measure (CoordinatorTargetScalars p) :=
  Measure.pi (fun _ : Fin (n_boot p) => ContinuousCategorical.uniform)

instance coordinatorTargetScalarLaw_probability (p : Parameters) :
    IsProbabilityMeasure (coordinatorTargetScalarLaw p) := by
  change IsProbabilityMeasure
    (Measure.pi (fun _ : Fin (n_boot p) => ContinuousCategorical.uniform))
  infer_instance

/-- The extra private streams, explicitly independent of the accepted
block-triple and `J` coordinates. -/
@[expose] noncomputable def extraPrivateStreamsLaw (p : Parameters) :
    Measure (PlayerRoundScalars p × CoordinatorTargetScalars p) :=
  (playerRoundScalarLaw p).prod (coordinatorTargetScalarLaw p)

instance extraPrivateStreamsLaw_probability (p : Parameters) :
    IsProbabilityMeasure (extraPrivateStreamsLaw p) := by
  dsimp [extraPrivateStreamsLaw]
  infer_instance

/-- Full fixed-public private law: the accepted private product followed by
the new, separately labelled product factors. -/
@[expose] noncomputable def extendedPrivateLaw (p : Parameters) :
    Measure (ExtendedPrivateCoordinates p) :=
  (PrivateSourceStreams.privateCoordinatesLaw p).prod (extraPrivateStreamsLaw p)

instance extendedPrivateLaw_probability (p : Parameters) :
    IsProbabilityMeasure (extendedPrivateLaw p) := by
  dsimp [extendedPrivateLaw]
  infer_instance

/-- Full joint law: the unchanged accepted public output law, followed by the
explicit extended private product. -/
@[expose] noncomputable def sourceInputLaw (p : Parameters) : Measure (SourceInput p) :=
  (publishedOutputMeasure p).prod (extendedPrivateLaw p)

instance sourceInputLaw_probability (p : Parameters) :
    IsProbabilityMeasure (sourceInputLaw p) := by
  dsimp [sourceInputLaw]
  infer_instance

/-- Fixing any published output and reward matrix leaves exactly the same
independent private product. -/
@[expose] def fixedPublicPrivateLaw (p : Parameters)
    (_published : PublishedOutput p) (_rewards : RewardMatrix p.T p.K) :
    Measure (ExtendedPrivateCoordinates p) :=
  extendedPrivateLaw p

theorem fixedPublicPrivateLaw_eq_product (p : Parameters)
    (published : PublishedOutput p) (rewards : RewardMatrix p.T p.K) :
    fixedPublicPrivateLaw p published rewards =
      (PrivateSourceStreams.privateCoordinatesLaw p).prod
        ((playerRoundScalarLaw p).prod (coordinatorTargetScalarLaw p)) := rfl

instance fixedPublicPrivateLaw_probability (p : Parameters)
    (published : PublishedOutput p) (rewards : RewardMatrix p.T p.K) :
    IsProbabilityMeasure (fixedPublicPrivateLaw p published rewards) := by
  change IsProbabilityMeasure (extendedPrivateLaw p)
  infer_instance

/-- Published output projection from the jointly sampled source. -/
@[expose] def sourcePublishedOutput (p : Parameters) (x : SourceInput p) :
    PublishedOutput p := x.1

/-- Accepted block-triple and coordinator-`J` coordinates. -/
@[expose] def sourceBasePrivateCoordinates (p : Parameters) (x : SourceInput p) :
    PrivateCoordinates p := x.2.1

/-- All fresh player-round scalar coordinates. -/
@[expose] def sourcePlayerRoundScalars (p : Parameters) (x : SourceInput p) :
    PlayerRoundScalars p := x.2.2.1

/-- All separate coordinator target scalar coordinates. -/
@[expose] def sourceCoordinatorTargetScalars (p : Parameters) (x : SourceInput p) :
    CoordinatorTargetScalars p := x.2.2.2

theorem measurable_sourcePublishedOutput (p : Parameters) :
    Measurable (sourcePublishedOutput p) := measurable_fst

theorem measurable_sourceBasePrivateCoordinates (p : Parameters) :
    Measurable (sourceBasePrivateCoordinates p) :=
  measurable_fst.comp measurable_snd

theorem measurable_sourcePlayerRoundScalars (p : Parameters) :
    Measurable (sourcePlayerRoundScalars p) :=
  measurable_fst.comp (measurable_snd.comp measurable_snd)

theorem measurable_sourceCoordinatorTargetScalars (p : Parameters) :
    Measurable (sourceCoordinatorTargetScalars p) :=
  measurable_snd.comp (measurable_snd.comp measurable_snd)

/-- The accepted published-output marginal survives the joint product law. -/
theorem sourcePublishedOutput_measurePreserving (p : Parameters) :
    MeasurePreserving (sourcePublishedOutput p) (sourceInputLaw p)
      (publishedOutputMeasure p) := by
  change MeasurePreserving Prod.fst
    ((publishedOutputMeasure p).prod (extendedPrivateLaw p))
    (publishedOutputMeasure p)
  exact measurePreserving_fst

theorem map_sourcePublishedOutput (p : Parameters) :
    (sourceInputLaw p).map (sourcePublishedOutput p) = publishedOutputMeasure p :=
  (sourcePublishedOutput_measurePreserving p).map_eq

/-- The all-player round coordinate has the exact product of its original
uniform scalar marginals when projected from the full source. -/
theorem sourcePlayerRoundScalars_measurePreserving (p : Parameters) :
    MeasurePreserving (sourcePlayerRoundScalars p) (sourceInputLaw p)
      (playerRoundScalarLaw p) := by
  have hbase : MeasurePreserving (Prod.snd :
      PrivateCoordinates p × (PlayerRoundScalars p × CoordinatorTargetScalars p) →
        PlayerRoundScalars p × CoordinatorTargetScalars p)
      (extendedPrivateLaw p) (extraPrivateStreamsLaw p) := by
    change MeasurePreserving Prod.snd
      ((PrivateSourceStreams.privateCoordinatesLaw p).prod
        (extraPrivateStreamsLaw p)) (extraPrivateStreamsLaw p)
    exact measurePreserving_snd
  have hround : MeasurePreserving (Prod.fst :
      PlayerRoundScalars p × CoordinatorTargetScalars p → PlayerRoundScalars p)
      (extraPrivateStreamsLaw p) (playerRoundScalarLaw p) := by
    change MeasurePreserving Prod.fst
      ((playerRoundScalarLaw p).prod (coordinatorTargetScalarLaw p))
      (playerRoundScalarLaw p)
    exact measurePreserving_fst
  have hprivate : MeasurePreserving (fun x : ExtendedPrivateCoordinates p =>
      (x.2.1)) (extendedPrivateLaw p) (playerRoundScalarLaw p) := by
    exact hround.comp hbase
  have hsource : MeasurePreserving (fun x : SourceInput p =>
      (x.2.2.1)) (sourceInputLaw p) (playerRoundScalarLaw p) := by
    change MeasurePreserving
      (fun x : PublishedOutput p × ExtendedPrivateCoordinates p => x.2.2.1)
      ((publishedOutputMeasure p).prod (extendedPrivateLaw p))
      (playerRoundScalarLaw p)
    exact hprivate.comp measurePreserving_snd
  change MeasurePreserving (fun x : SourceInput p => x.2.2.1)
    (sourceInputLaw p) (playerRoundScalarLaw p)
  exact hsource

/-- The coordinator target coordinates remain an independent product when
projected from the full source. -/
theorem sourceCoordinatorTargetScalars_measurePreserving (p : Parameters) :
    MeasurePreserving (sourceCoordinatorTargetScalars p) (sourceInputLaw p)
      (coordinatorTargetScalarLaw p) := by
  have hbase : MeasurePreserving (Prod.snd :
      PrivateCoordinates p × (PlayerRoundScalars p × CoordinatorTargetScalars p) →
        PlayerRoundScalars p × CoordinatorTargetScalars p)
      (extendedPrivateLaw p) (extraPrivateStreamsLaw p) := by
    change MeasurePreserving Prod.snd
      ((PrivateSourceStreams.privateCoordinatesLaw p).prod
        (extraPrivateStreamsLaw p)) (extraPrivateStreamsLaw p)
    exact measurePreserving_snd
  have htarget : MeasurePreserving (Prod.snd :
      PlayerRoundScalars p × CoordinatorTargetScalars p → CoordinatorTargetScalars p)
      (extraPrivateStreamsLaw p) (coordinatorTargetScalarLaw p) := by
    change MeasurePreserving Prod.snd
      ((playerRoundScalarLaw p).prod (coordinatorTargetScalarLaw p))
      (coordinatorTargetScalarLaw p)
    exact measurePreserving_snd
  have hprivate : MeasurePreserving (fun x : ExtendedPrivateCoordinates p =>
      x.2.2) (extendedPrivateLaw p) (coordinatorTargetScalarLaw p) := by
    exact htarget.comp hbase
  have hsource : MeasurePreserving (fun x : SourceInput p => x.2.2.2)
      (sourceInputLaw p) (coordinatorTargetScalarLaw p) := by
    change MeasurePreserving
      (fun x : PublishedOutput p × ExtendedPrivateCoordinates p => x.2.2.2)
      ((publishedOutputMeasure p).prod (extendedPrivateLaw p))
      (coordinatorTargetScalarLaw p)
    exact hprivate.comp measurePreserving_snd
  change MeasurePreserving (fun x : SourceInput p => x.2.2.2)
    (sourceInputLaw p) (coordinatorTargetScalarLaw p)
  exact hsource

/-- Projection to the already accepted private coordinates is unchanged. -/
theorem sourceBasePrivateCoordinates_measurePreserving (p : Parameters) :
    MeasurePreserving (sourceBasePrivateCoordinates p) (sourceInputLaw p)
      (PrivateSourceStreams.privateCoordinatesLaw p) := by
  have hbase : MeasurePreserving (Prod.fst :
      PrivateCoordinates p × (PlayerRoundScalars p × CoordinatorTargetScalars p) →
        PrivateCoordinates p)
      (extendedPrivateLaw p) (PrivateSourceStreams.privateCoordinatesLaw p) := by
    change MeasurePreserving Prod.fst
      ((PrivateSourceStreams.privateCoordinatesLaw p).prod
        (extraPrivateStreamsLaw p)) (PrivateSourceStreams.privateCoordinatesLaw p)
    exact measurePreserving_fst
  have hsource : MeasurePreserving (fun x : SourceInput p => x.2.1)
      (sourceInputLaw p) (PrivateSourceStreams.privateCoordinatesLaw p) := by
    change MeasurePreserving
      (fun x : PublishedOutput p × ExtendedPrivateCoordinates p => x.2.1)
      ((publishedOutputMeasure p).prod (extendedPrivateLaw p))
      (PrivateSourceStreams.privateCoordinatesLaw p)
    exact hbase.comp measurePreserving_snd
  change MeasurePreserving (fun x : SourceInput p => x.2.1)
    (sourceInputLaw p) (PrivateSourceStreams.privateCoordinatesLaw p)
  exact hsource

/-- Equal mass on every arm of a finite nonempty alphabet. -/
@[expose] def equalArmMass (n : ℕ) : Fin n → ℝ := fun _ => 1 / (n : ℝ)

theorem equalArmMass_nonneg (n : ℕ) (a : Fin n) : 0 ≤ equalArmMass n a := by
  simp only [equalArmMass]
  positivity

theorem equalArmMass_sum (n : ℕ) (hn : 0 < n) :
    (∑ a : Fin n, equalArmMass n a) = 1 := by
  rw [show (∑ a : Fin n, equalArmMass n a) = (n : ℝ) * (1 / (n : ℝ)) by
    simp [equalArmMass]]
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  field_simp

/-- Literal inverse-cumulative full-arm draw in increasing arm order. -/
@[expose] noncomputable def fullArmScalarDraw (p : Parameters) (v : Scalar) :
    Fin p.K :=
  ContinuousCategorical.sample (K_pos p) (equalArmMass p.K)
    (equalArmMass_sum p.K (K_pos p)) v

theorem measurable_fullArmScalarDraw (p : Parameters) :
    Measurable (fullArmScalarDraw p) :=
  ContinuousCategorical.measurable_sample (K_pos p)
    (equalArmMass_nonneg p.K) (equalArmMass_sum p.K (K_pos p))

/-- Exact singleton law of the genuine full-arm inverse-CDF draw. -/
theorem fullArmScalarDraw_uniform_atom (p : Parameters) (a : Fin p.K) :
    ContinuousCategorical.uniform (fullArmScalarDraw p ⁻¹' {a}) =
      ENNReal.ofReal (1 / (p.K : ℝ)) := by
  exact ContinuousCategorical.uniform_sample_singleton (K_pos p)
    (equalArmMass_nonneg p.K) (equalArmMass_sum p.K (K_pos p)) a

/-- The corresponding pushforward singleton mass on arms. -/
theorem fullArmScalarDraw_map_atom (p : Parameters) (a : Fin p.K) :
    (ContinuousCategorical.uniform.map (fullArmScalarDraw p)) {a} =
      ENNReal.ofReal (1 / (p.K : ℝ)) := by
  rw [Measure.map_apply (measurable_fullArmScalarDraw p) (measurableSet_singleton a)]
  exact fullArmScalarDraw_uniform_atom p a

/-- The complement carrier, with arm membership represented by the genuine
subtype `b ≠ a`. -/
@[expose] def forbiddenArms (p : Parameters) (a : Fin p.K) : Finset (Fin p.K) :=
  Finset.univ.erase a

theorem forbiddenArms_card (p : Parameters) (a : Fin p.K) :
    (forbiddenArms p a).card = p.K - 1 := by
  simp [forbiddenArms]

theorem forbiddenArms_card_pos (p : Parameters) : 0 < p.K - 1 := by
  have hK : 2 ≤ p.K := le_trans p.two_le_m (Nat.le_of_lt p.m_lt_K)
  omega

theorem forbiddenArms_nonempty (p : Parameters) (a : Fin p.K) :
    (forbiddenArms p a).Nonempty := by
  apply Finset.card_pos.mp
  rw [forbiddenArms_card]
  exact forbiddenArms_card_pos p

/-- Identify the erased finset subtype with the requested forbidden-arm
subtype without changing the underlying arm. -/
@[expose] def forbiddenArmFinsetEquiv (p : Parameters) (a : Fin p.K) :
    {b : Fin p.K // b ∈ forbiddenArms p a} ≃ ArmAvoiding p a where
  toFun b := ⟨b.1, (Finset.mem_erase.mp b.2).1⟩
  invFun b := ⟨b.1, Finset.mem_erase.mpr ⟨b.2, Finset.mem_univ _⟩⟩
  left_inv b := by
    apply Subtype.ext
    rfl
  right_inv b := by
    apply Subtype.ext
    rfl

/-- Increasing-arm-order bijection from zero-based ranks onto the genuine
forbidden-arm subtype. -/
@[expose] noncomputable def forbiddenArmOrder (p : Parameters) (a : Fin p.K) :
    Fin (p.K - 1) ≃ ArmAvoiding p a :=
  ((forbiddenArms p a).orderIsoOfFin (forbiddenArms_card p a)).toEquiv.trans
    (forbiddenArmFinsetEquiv p a)

theorem forbiddenArmOrder_val (p : Parameters) (a : Fin p.K)
    (r : Fin (p.K - 1)) :
    (forbiddenArmOrder p a r).val =
      (forbiddenArms p a).orderEmbOfFin (forbiddenArms_card p a) r := by
  simp [forbiddenArmOrder, forbiddenArmFinsetEquiv,
    Finset.coe_orderIsoOfFin_apply]

/-- Increasing ranks in `Fin (K-1)` map to strictly increasing arm labels in
the complement. -/
theorem forbiddenArmOrder_strictMono (p : Parameters) (a : Fin p.K) :
    StrictMono (fun r : Fin (p.K - 1) => (forbiddenArmOrder p a r).val) := by
  simpa only [forbiddenArmOrder_val] using
    ((forbiddenArms p a).orderEmbOfFin (forbiddenArms_card p a)).strictMono

/-- Literal inverse-cumulative uniform draw from `[K] \ {a}`, by the increasing
arm order of the complement. There is no arbitrary choice or fallback value. -/
@[expose] noncomputable def forbiddenArmScalarDraw (p : Parameters)
    (a : Fin p.K) (v : Scalar) : ArmAvoiding p a :=
  forbiddenArmOrder p a
    (ContinuousCategorical.sample (forbiddenArms_card_pos p)
      (equalArmMass (p.K - 1))
      (equalArmMass_sum (p.K - 1) (forbiddenArms_card_pos p)) v)

theorem measurable_forbiddenArmScalarDraw (p : Parameters) (a : Fin p.K) :
    Measurable (forbiddenArmScalarDraw p a) := by
  exact (Measurable.of_discrete :
      Measurable (forbiddenArmOrder p a)).comp
    (ContinuousCategorical.measurable_sample (forbiddenArms_card_pos p)
      (equalArmMass_nonneg (p.K - 1))
      (equalArmMass_sum (p.K - 1) (forbiddenArms_card_pos p)))

/-- The fiber over a forbidden-arm subtype element is exactly the scalar
fiber of its unique increasing complement rank. -/
theorem forbiddenArmScalarDraw_fiber (p : Parameters) (a : Fin p.K)
    (b : ArmAvoiding p a) :
    forbiddenArmScalarDraw p a ⁻¹' {b} =
      (ContinuousCategorical.sample (forbiddenArms_card_pos p)
        (equalArmMass (p.K - 1))
        (equalArmMass_sum (p.K - 1) (forbiddenArms_card_pos p))) ⁻¹'
        {(forbiddenArmOrder p a).symm b} := by
  ext v
  change forbiddenArmOrder p a
      (ContinuousCategorical.sample (forbiddenArms_card_pos p)
        (equalArmMass (p.K - 1))
        (equalArmMass_sum (p.K - 1) (forbiddenArms_card_pos p)) v) = b ↔
    ContinuousCategorical.sample (forbiddenArms_card_pos p)
        (equalArmMass (p.K - 1))
        (equalArmMass_sum (p.K - 1) (forbiddenArms_card_pos p)) v =
      (forbiddenArmOrder p a).symm b
  constructor
  · intro h
    exact (forbiddenArmOrder p a).symm_apply_apply _ |>.symm |>.trans
      (congrArg (forbiddenArmOrder p a).symm h)
  · intro h
    rw [h, (forbiddenArmOrder p a).apply_symm_apply]

/-- Every complement element is selected with exact mass `1/(K-1)`. -/
theorem forbiddenArmScalarDraw_uniform_atom (p : Parameters) (a : Fin p.K)
    (b : ArmAvoiding p a) :
    ContinuousCategorical.uniform (forbiddenArmScalarDraw p a ⁻¹' {b}) =
      ENNReal.ofReal (1 / ((p.K - 1 : ℕ) : ℝ)) := by
  rw [forbiddenArmScalarDraw_fiber]
  exact ContinuousCategorical.uniform_sample_singleton (forbiddenArms_card_pos p)
    (equalArmMass_nonneg (p.K - 1))
    (equalArmMass_sum (p.K - 1) (forbiddenArms_card_pos p)) _

/-- The forbidden-arm output law assigns exact mass `1/(K-1)` to every arm
in the genuine complement subtype. -/
theorem forbiddenArmScalarDraw_map_atom (p : Parameters) (a : Fin p.K)
    (b : ArmAvoiding p a) :
    (ContinuousCategorical.uniform.map (forbiddenArmScalarDraw p a)) {b} =
      ENNReal.ofReal (1 / ((p.K - 1 : ℕ) : ℝ)) := by
  rw [Measure.map_apply (measurable_forbiddenArmScalarDraw p a)
    (measurableSet_singleton b)]
  exact forbiddenArmScalarDraw_uniform_atom p a b

/-- The actual product measure for one fixed forbidden arm's categorical
output. -/
@[expose] noncomputable def forbiddenArmLaw (p : Parameters) (a : Fin p.K) :
    Measure (ArmAvoiding p a) :=
  ContinuousCategorical.uniform.map (forbiddenArmScalarDraw p a)

instance forbiddenArmLaw_probability (p : Parameters) (a : Fin p.K) :
    IsProbabilityMeasure (forbiddenArmLaw p a) := by
  dsimp [forbiddenArmLaw]
  infer_instance

/-- Product law of the fixed-forbidden-arm outputs over all player-round
labels. -/
@[expose] noncomputable def fixedForbiddenArmVectorLaw (p : Parameters)
    (forbidden : PlayerRoundLabel p → Fin p.K) :
    Measure (ArmAvoidingVector p forbidden) :=
  Measure.pi (fun label => forbiddenArmLaw p (forbidden label))

instance fixedForbiddenArmVectorLaw_probability (p : Parameters)
    (forbidden : PlayerRoundLabel p → Fin p.K) :
    IsProbabilityMeasure (fixedForbiddenArmVectorLaw p forbidden) := by
  change IsProbabilityMeasure (Measure.pi (fun label => forbiddenArmLaw p (forbidden label)))
  infer_instance

/-- The coordinator's target arm at one block, from its separate target
scalar, using the same literal full-arm inverse-CDF map. -/
@[expose] def coordinatorTargetDraw (p : Parameters) : Scalar → Fin p.K :=
  fullArmScalarDraw p

/-- Product law of the sampled coordinator target arms over calendar blocks. -/
@[expose] noncomputable def coordinatorTargetArmLaw (p : Parameters) :
    Measure (CoordinatorTargetArms p) :=
  Measure.pi (fun _ : Fin (n_boot p) =>
    ContinuousCategorical.uniform.map (coordinatorTargetDraw p))

instance coordinatorTargetArmLaw_probability (p : Parameters) :
    IsProbabilityMeasure (coordinatorTargetArmLaw p) := by
  change IsProbabilityMeasure (Measure.pi (fun _ : Fin (n_boot p) =>
    ContinuousCategorical.uniform.map (coordinatorTargetDraw p)))
  infer_instance

/-- Apply the per-block target map to the entire coordinator scalar stream. -/
@[expose] def coordinatorTargetArmMap (p : Parameters)
    (x : CoordinatorTargetScalars p) : CoordinatorTargetArms p :=
  fun s => coordinatorTargetDraw p (x s)

theorem measurable_coordinatorTargetArmMap (p : Parameters) :
    Measurable (coordinatorTargetArmMap p) := by
  apply measurable_pi_iff.mpr
  intro s
  exact (measurable_fullArmScalarDraw p).comp (measurable_pi_apply s)

/-- The complete vector law of coordinator target arms factors over block
labels, with each target uniform on all `K` arms. -/
theorem coordinatorTargetArmMap_law (p : Parameters) :
    (coordinatorTargetScalarLaw p).map (coordinatorTargetArmMap p) =
      coordinatorTargetArmLaw p := by
  change (Measure.pi (fun _ : Fin (n_boot p) => ContinuousCategorical.uniform)).map _ =
    Measure.pi (fun _ : Fin (n_boot p) =>
      ContinuousCategorical.uniform.map (coordinatorTargetDraw p))
  exact Measure.pi_map_pi (fun s =>
    (measurable_fullArmScalarDraw p).aemeasurable)

/-- Each coordinator block target remains exactly uniform after taking its
coordinate from the complete target vector. -/
theorem coordinatorTargetArmLaw_coordinate_measurePreserving (p : Parameters)
    (s : Fin (n_boot p)) :
    MeasurePreserving (Function.eval s) (coordinatorTargetArmLaw p)
      (ContinuousCategorical.uniform.map (coordinatorTargetDraw p)) := by
  change MeasurePreserving (Function.eval s)
    (Measure.pi (fun _ : Fin (n_boot p) =>
      ContinuousCategorical.uniform.map (coordinatorTargetDraw p)))
    (ContinuousCategorical.uniform.map (coordinatorTargetDraw p))
  exact measurePreserving_eval
    (μ := fun _ : Fin (n_boot p) =>
      ContinuousCategorical.uniform.map (coordinatorTargetDraw p)) s

theorem coordinatorTargetArmLaw_coordinate_atom (p : Parameters)
    (s : Fin (n_boot p)) (a : Fin p.K) :
    (coordinatorTargetArmLaw p).map (Function.eval s) {a} =
      ENNReal.ofReal (1 / (p.K : ℝ)) := by
  rw [(coordinatorTargetArmLaw_coordinate_measurePreserving p s).map_eq]
  exact fullArmScalarDraw_map_atom p a

/-- Apply fixed forbidden-arm maps to the whole labelled player-round array. -/
@[expose] def fixedForbiddenArmVectorMap (p : Parameters)
    (forbidden : PlayerRoundLabel p → Fin p.K)
    (x : PlayerRoundScalars p) : ArmAvoidingVector p forbidden :=
  fun label => forbiddenArmScalarDraw p (forbidden label) (x label)

theorem measurable_fixedForbiddenArmVectorMap (p : Parameters)
    (forbidden : PlayerRoundLabel p → Fin p.K) :
    Measurable (fixedForbiddenArmVectorMap p forbidden) := by
  apply measurable_pi_iff.mpr
  intro label
  exact (measurable_forbiddenArmScalarDraw p (forbidden label)).comp
    (measurable_pi_apply label)

/-- The complete fixed-forbidden-arm vector pushforward factors over every
player-round label. -/
theorem fixedForbiddenArmVectorMap_law (p : Parameters)
    (forbidden : PlayerRoundLabel p → Fin p.K) :
    (playerRoundScalarLaw p).map (fixedForbiddenArmVectorMap p forbidden) =
      fixedForbiddenArmVectorLaw p forbidden := by
  change (Measure.pi (fun _ : PlayerRoundLabel p =>
    ContinuousCategorical.uniform)).map _ =
      Measure.pi (fun label : PlayerRoundLabel p => forbiddenArmLaw p (forbidden label))
  exact Measure.pi_map_pi (fun label =>
    (measurable_forbiddenArmScalarDraw p (forbidden label)).aemeasurable)

/-- The private product's arm and target pushforward, before adjoining the
public-output coordinate. -/
theorem extendedPrivate_roundArms_and_targets_law (p : Parameters)
    (forbidden : PlayerRoundLabel p → Fin p.K) :
    (extendedPrivateLaw p).map
      (fun x : ExtendedPrivateCoordinates p =>
        Prod.mk x.1 (Prod.mk (fixedForbiddenArmVectorMap p forbidden x.2.1)
          (coordinatorTargetArmMap p x.2.2))) =
      (PrivateSourceStreams.privateCoordinatesLaw p).prod
        ((fixedForbiddenArmVectorLaw p forbidden).prod
          (coordinatorTargetArmLaw p)) := by
  have hroundMeas := measurable_fixedForbiddenArmVectorMap p forbidden
  have htargetMeas := measurable_coordinatorTargetArmMap p
  let hextraMap : PlayerRoundScalars p × CoordinatorTargetScalars p →
      ArmAvoidingVector p forbidden × CoordinatorTargetArms p :=
    fun x => Prod.mk (fixedForbiddenArmVectorMap p forbidden x.1)
      (coordinatorTargetArmMap p x.2)
  have hextraMeas : Measurable hextraMap := by
    change Measurable (fun x : PlayerRoundScalars p × CoordinatorTargetScalars p =>
      Prod.mk (fixedForbiddenArmVectorMap p forbidden x.1)
        (coordinatorTargetArmMap p x.2))
    exact (hroundMeas.comp measurable_fst).prodMk (htargetMeas.comp measurable_snd)
  unfold extendedPrivateLaw
  change ((PrivateSourceStreams.privateCoordinatesLaw p).prod
      (extraPrivateStreamsLaw p)).map (Prod.map id hextraMap) = _
  calc
    _ = (Measure.map id (PrivateSourceStreams.privateCoordinatesLaw p)).prod
        ((extraPrivateStreamsLaw p).map hextraMap) := by
          exact (Measure.map_prod_map
            (PrivateSourceStreams.privateCoordinatesLaw p)
            (extraPrivateStreamsLaw p) measurable_id hextraMeas).symm
    _ = (PrivateSourceStreams.privateCoordinatesLaw p).prod
        (((playerRoundScalarLaw p).map (fixedForbiddenArmVectorMap p forbidden)).prod
          ((coordinatorTargetScalarLaw p).map (coordinatorTargetArmMap p))) := by
          rw [Measure.map_id]
          exact congrArg (fun μ => (PrivateSourceStreams.privateCoordinatesLaw p).prod μ)
            ((Measure.map_prod_map (playerRoundScalarLaw p)
              (coordinatorTargetScalarLaw p) hroundMeas htargetMeas).symm)
    _ = _ := by
          rw [fixedForbiddenArmVectorMap_law, coordinatorTargetArmMap_law]

/-- The round-arm and target maps are independent of each other and of all
accepted private inputs: their joint law is the product of the accepted base
law and the two coordinatewise pushforward products. -/
theorem fixedPublic_roundArms_and_targets_law (p : Parameters)
    (published : PublishedOutput p) (rewards : RewardMatrix p.T p.K)
    (forbidden : PlayerRoundLabel p → Fin p.K) :
    (fixedPublicPrivateLaw p published rewards).map
      (fun x : ExtendedPrivateCoordinates p =>
        Prod.mk x.1 (Prod.mk (fixedForbiddenArmVectorMap p forbidden x.2.1)
          (coordinatorTargetArmMap p x.2.2))) =
      (PrivateSourceStreams.privateCoordinatesLaw p).prod
        ((fixedForbiddenArmVectorLaw p forbidden).prod
          (coordinatorTargetArmLaw p)) := by
  rw [fixedPublicPrivateLaw_eq_product]
  exact extendedPrivate_roundArms_and_targets_law p forbidden

/-- Jointly sampling the accepted public output and all new maps preserves the
accepted public marginal and factors the fixed-forbidden-arm vector over
player-round labels and independent coordinator block targets. -/
theorem sourceInput_roundArms_and_targets_law (p : Parameters)
    (forbidden : PlayerRoundLabel p → Fin p.K) :
    (sourceInputLaw p).map
      (fun x : SourceInput p =>
        Prod.mk x.1 (Prod.mk x.2.1
          (Prod.mk (fixedForbiddenArmVectorMap p forbidden x.2.2.1)
            (coordinatorTargetArmMap p x.2.2.2)))) =
      (publishedOutputMeasure p).prod
        ((PrivateSourceStreams.privateCoordinatesLaw p).prod
          ((fixedForbiddenArmVectorLaw p forbidden).prod
            (coordinatorTargetArmLaw p))) := by
  have hinner : Measurable (fun z : PlayerRoundScalars p ×
      CoordinatorTargetScalars p =>
        Prod.mk (fixedForbiddenArmVectorMap p forbidden z.1)
          (coordinatorTargetArmMap p z.2)) :=
    ((measurable_fixedForbiddenArmVectorMap p forbidden).comp measurable_fst).prodMk
      ((measurable_coordinatorTargetArmMap p).comp measurable_snd)
  let privateMap : ExtendedPrivateCoordinates p →
      PrivateCoordinates p × (ArmAvoidingVector p forbidden × CoordinatorTargetArms p) :=
    fun z => Prod.mk z.1 (Prod.mk (fixedForbiddenArmVectorMap p forbidden z.2.1)
      (coordinatorTargetArmMap p z.2.2))
  have hprivate : Measurable privateMap := by
    change Measurable (fun z : ExtendedPrivateCoordinates p =>
      Prod.mk z.1 (Prod.mk (fixedForbiddenArmVectorMap p forbidden z.2.1)
        (coordinatorTargetArmMap p z.2.2)))
    exact measurable_fst.prodMk (hinner.comp measurable_snd)
  calc
    _ = (Measure.map id (publishedOutputMeasure p)).prod
        ((extendedPrivateLaw p).map privateMap) := by
          change ((publishedOutputMeasure p).prod (extendedPrivateLaw p)).map
            (Prod.map id privateMap) = _
          exact (Measure.map_prod_map (publishedOutputMeasure p)
            (extendedPrivateLaw p) measurable_id hprivate).symm
    _ = (publishedOutputMeasure p).prod
        ((PrivateSourceStreams.privateCoordinatesLaw p).prod
          ((fixedForbiddenArmVectorLaw p forbidden).prod
            (coordinatorTargetArmLaw p))) := by
          rw [Measure.map_id]
          exact congrArg (fun μ => (publishedOutputMeasure p).prod μ)
            (extendedPrivate_roundArms_and_targets_law p forbidden)

/-- Player-local input. The coordinator receives its actual `J`, its sampled
block target stream, and only its own round scalars. A follower receives only
its own existing block stream and its own round scalars. -/
abbrev PlayerPrivateInput (p : Parameters) :=
  Sum (Fin (M p) × (CoordinatorTargetArms p × PlayerRoundScalarStream p))
    (FollowerStream p × PlayerRoundScalarStream p)

/-- The existing follower coordinate belonging to a non-coordinator player. -/
@[expose] def followerIndexOfPlayer (p : Parameters) (i : Fin p.m) :
    Fin (p.m - 1) :=
  ⟨i.val - 1, by
    have hi := i.isLt
    have hm := p.two_le_m
    omega⟩

/-- The source coordinator's actual row index `J`. -/
@[expose] def sourceCoordinatorIndex (p : Parameters) (x : SourceInput p) :
    Fin (M p) :=
  PrivateSourceStreams.coordinatorIndex p (x.2.1.2)

/-- The coordinator's sampled block target stream. -/
@[expose] def sourceCoordinatorTargetArms (p : Parameters) (x : SourceInput p) :
    CoordinatorTargetArms p :=
  coordinatorTargetArmMap p (x.2.2.2)

/-- A player's own scalar stream extracted from the joint player-round array. -/
@[expose] def sourcePlayerRoundScalarStream (p : Parameters) (i : Fin p.m)
    (x : SourceInput p) : PlayerRoundScalarStream p :=
  fun t => x.2.2.1 (i, t)

/-- The role-tagged local private view of player `i`. -/
@[expose] def sourcePlayerPrivateInput (p : Parameters) (i : Fin p.m)
    (x : SourceInput p) : PlayerPrivateInput p :=
  if i.val = 0 then
    Sum.inl (sourceCoordinatorIndex p x,
      (sourceCoordinatorTargetArms p x, sourcePlayerRoundScalarStream p i x))
  else
    Sum.inr (fun s => x.2.1.1 s (followerIndexOfPlayer p i),
      sourcePlayerRoundScalarStream p i x)

theorem sourcePlayerPrivateInput_coordinator (p : Parameters) (x : SourceInput p) :
    sourcePlayerPrivateInput p ⟨0, m_pos p⟩ x =
      Sum.inl (sourceCoordinatorIndex p x,
        (sourceCoordinatorTargetArms p x,
          sourcePlayerRoundScalarStream p ⟨0, m_pos p⟩ x)) := by
  simp [sourcePlayerPrivateInput]

theorem sourcePlayerPrivateInput_follower (p : Parameters)
    (i : Fin (p.m - 1)) (x : SourceInput p) :
    sourcePlayerPrivateInput p ⟨i.val + 1, by omega⟩ x =
      Sum.inr (fun s => x.2.1.1 s i,
        sourcePlayerRoundScalarStream p ⟨i.val + 1, by omega⟩ x) := by
  have hindex : followerIndexOfPlayer p ⟨i.val + 1, by omega⟩ = i := by
    apply Fin.ext
    simp only [followerIndexOfPlayer]
    omega
  simp [sourcePlayerPrivateInput, hindex]

theorem measurable_sourceCoordinatorIndex (p : Parameters) :
    Measurable (sourceCoordinatorIndex p) := by
  exact (PrivateSourceStreams.measurable_coordinatorIndex p).comp
    (measurable_snd.comp (measurable_fst.comp measurable_snd))

theorem measurable_sourceCoordinatorTargetArms (p : Parameters) :
    Measurable (sourceCoordinatorTargetArms p) :=
  (measurable_coordinatorTargetArmMap p).comp
    (measurable_snd.comp (measurable_snd.comp measurable_snd))

theorem measurable_sourcePlayerRoundScalarStream (p : Parameters) (i : Fin p.m) :
    Measurable (sourcePlayerRoundScalarStream p i) := by
  apply measurable_pi_iff.mpr
  intro t
  exact (measurable_pi_apply (i, t)).comp (measurable_sourcePlayerRoundScalars p)

theorem measurable_sourcePlayerPrivateInput (p : Parameters) (i : Fin p.m) :
    Measurable (sourcePlayerPrivateInput p i) := by
  by_cases hcoord : i.val = 0
  · have hview : sourcePlayerPrivateInput p i = fun x : SourceInput p =>
        Sum.inl (sourceCoordinatorIndex p x,
          (sourceCoordinatorTargetArms p x, sourcePlayerRoundScalarStream p i x)) := by
      funext x
      simp [sourcePlayerPrivateInput, hcoord]
    rw [hview]
    exact (measurable_inl :
      Measurable (@Sum.inl
        (Fin (M p) × (CoordinatorTargetArms p × PlayerRoundScalarStream p))
        (FollowerStream p × PlayerRoundScalarStream p))).comp
      ((measurable_sourceCoordinatorIndex p).prodMk
        ((measurable_sourceCoordinatorTargetArms p).prodMk
          (measurable_sourcePlayerRoundScalarStream p i)))
  · have hview : sourcePlayerPrivateInput p i = fun x : SourceInput p =>
        Sum.inr ((fun s => x.2.1.1 s (followerIndexOfPlayer p i)),
          sourcePlayerRoundScalarStream p i x) := by
      funext x
      simp [sourcePlayerPrivateInput, hcoord]
    rw [hview]
    apply (measurable_inr :
      Measurable (@Sum.inr
        (Fin (M p) × (CoordinatorTargetArms p × PlayerRoundScalarStream p))
        (FollowerStream p × PlayerRoundScalarStream p))).comp
    have hblocks : Measurable (fun x : SourceInput p =>
        fun s => x.2.1.1 s (followerIndexOfPlayer p i)) := by
      apply measurable_pi_iff.mpr
      intro s
      exact (measurable_pi_apply (followerIndexOfPlayer p i)).comp
        ((measurable_pi_apply s).comp
          ((measurable_fst.comp (measurable_sourceBasePrivateCoordinates p))))
    exact hblocks.prodMk (measurable_sourcePlayerRoundScalarStream p i)

/-- Changing any other player's private coordinates leaves a follower's local
view unchanged as long as its own accepted block and round streams agree. -/
theorem follower_local_view_eq_of_own_coordinates_eq (p : Parameters)
    (i : Fin p.m) (hi : i.val ≠ 0) (x y : SourceInput p)
    (hblocks : ∀ s : Fin (n_boot p),
      x.2.1.1 s (followerIndexOfPlayer p i) =
        y.2.1.1 s (followerIndexOfPlayer p i))
    (hround : ∀ t : Fin p.T, x.2.2.1 (i, t) = y.2.2.1 (i, t)) :
    sourcePlayerPrivateInput p i x = sourcePlayerPrivateInput p i y := by
  have hblockStream :
      (fun s => x.2.1.1 s (followerIndexOfPlayer p i)) =
        (fun s => y.2.1.1 s (followerIndexOfPlayer p i)) := funext hblocks
  have hroundStream : sourcePlayerRoundScalarStream p i x =
      sourcePlayerRoundScalarStream p i y := funext hround
  simp [sourcePlayerPrivateInput, hi, hblockStream, hroundStream]

/-- Changing follower coordinates and other players' round coordinates leaves
the coordinator view unchanged when `J`, its targets, and its own round stream
agree. -/
theorem coordinator_local_view_eq_of_own_coordinates_eq (p : Parameters)
    (i : Fin p.m) (hi : i.val = 0) (x y : SourceInput p)
    (hJ : sourceCoordinatorIndex p x = sourceCoordinatorIndex p y)
    (htargets : sourceCoordinatorTargetArms p x = sourceCoordinatorTargetArms p y)
    (hround : ∀ t : Fin p.T, x.2.2.1 (i, t) = y.2.2.1 (i, t)) :
    sourcePlayerPrivateInput p i x = sourcePlayerPrivateInput p i y := by
  have hroundStream : sourcePlayerRoundScalarStream p i x =
      sourcePlayerRoundScalarStream p i y := funext hround
  simp [sourcePlayerPrivateInput, hi, hJ, htargets, hroundStream]

end Bandits.Support.BootstrapPrivateRoundStreams

end
