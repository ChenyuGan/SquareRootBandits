/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.PlayerPrivateCoordinateProduct

/-!
# Sampled player-private inputs

This module maps the accepted raw player coordinates to the protocol's
existing local input: the coordinator's sampled row index and target arms,
and each player's own calendar-round scalar stream. It proves the resulting
independent product law from the specified factor laws. The source discussion
of player roles and private randomness is in
`sources/zip4/manuscript/01_introduction.tex:18-36` and
`sources/zip4/manuscript/07_public_setup.tex:27-38,55-114`; the
fixed-public private expectation is in
`sources/zip4/manuscript/08_main_theorem.tex:26-42,67-75`.

These exogenous product laws do not assert independence after adaptive
history-dependent choices.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.PrivateSourceStreams
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.PlayerPrivateCoordinateProduct
open Bandits.Support.MeasurableLocalRollout
open Bandits.Support.FiniteBanditModel

namespace Bandits.Support.PlayerPrivateSampledProduct

/-- Recover the admitted product Borel structure beneath the public-output
abbreviation for maps whose codomain pairs that original output. -/
local instance sampledPublishedOutputMeasurableSpace (p : Parameters) :
    MeasurableSpace (CompletePublicTable.PublishedOutput p) := by
  change MeasurableSpace
    (CompletePublicTable.IDArray p × CompletePublicTable.CompleteRows p)
  infer_instance

local instance sampledPlayerProfileMeasurableSpace (p : Parameters) :
    MeasurableSpace
      (FiniteBanditModel.Player p.m →
        BootstrapPrivateRoundStreams.PlayerPrivateInput p) := by
  change MeasurableSpace
    (Fin p.m → BootstrapPrivateRoundStreams.PlayerPrivateInput p)
  infer_instance

/-- Sample only the coordinator's prescribed row and target coordinates,
keeping its complete own-round stream unchanged. -/
def sampleCoordinatorRawInput (p : Parameters)
    (x : PlayerPrivateCoordinateProduct.CoordinatorRaw p) :
    Fin (M p) ×
      (CoordinatorTargetArms p × PlayerRoundScalarStream p) :=
  (coordinatorIndex p x.1,
    (coordinatorTargetArmMap p x.2.2, x.2.1))

/-- Convert each raw player view to its existing role-specific protocol
input. Followers keep every block-triple and round coordinate unchanged. -/
def samplePrivateInput (p : Parameters) :
    PlayerPrivateCoordinateProduct.RawPlayerPrivateInput p →
      BootstrapPrivateRoundStreams.PlayerPrivateInput p :=
  Sum.elim
    (fun x => Sum.inl (sampleCoordinatorRawInput p x))
    (fun x => Sum.inr x)

theorem samplePrivateInput_coordinator (p : Parameters)
    (rawJ : ContinuousCategorical.Scalar)
    (rounds : Fin p.T → ContinuousCategorical.Scalar)
    (targets : CoordinatorTargetScalars p) :
    samplePrivateInput p (Sum.inl (rawJ, (rounds, targets))) =
      Sum.inl (coordinatorIndex p rawJ,
        (coordinatorTargetArmMap p targets, rounds)) := rfl

theorem samplePrivateInput_follower (p : Parameters)
    (follower : PlayerPrivateCoordinateProduct.FollowerRaw p) :
    samplePrivateInput p (Sum.inr follower) = Sum.inr follower := rfl

theorem measurable_sampleCoordinatorRawInput (p : Parameters) :
    Measurable (sampleCoordinatorRawInput p) := by
  have hindex : Measurable
      (fun x : PlayerPrivateCoordinateProduct.CoordinatorRaw p =>
        coordinatorIndex p x.1) :=
    (PrivateSourceStreams.measurable_coordinatorIndex p).comp measurable_fst
  have htargets : Measurable
      (fun x : PlayerPrivateCoordinateProduct.CoordinatorRaw p =>
        coordinatorTargetArmMap p x.2.2) :=
    (BootstrapPrivateRoundStreams.measurable_coordinatorTargetArmMap p).comp
      (measurable_snd.comp measurable_snd)
  have hrounds : Measurable
      (fun x : PlayerPrivateCoordinateProduct.CoordinatorRaw p => x.2.1) :=
    measurable_fst.comp measurable_snd
  exact hindex.prodMk (htargets.prodMk hrounds)

theorem measurable_samplePrivateInput (p : Parameters) :
    Measurable (samplePrivateInput p) := by
  have hleft : Measurable
      (Sum.inl ∘ sampleCoordinatorRawInput p :
        PlayerPrivateCoordinateProduct.CoordinatorRaw p →
          BootstrapPrivateRoundStreams.PlayerPrivateInput p) :=
    measurable_inl.comp (measurable_sampleCoordinatorRawInput p)
  have hright : Measurable
      (Sum.inr : PlayerPrivateCoordinateProduct.FollowerRaw p →
        BootstrapPrivateRoundStreams.PlayerPrivateInput p) := measurable_inr
  exact hleft.sumElim hright

/-- Independently specified product law of the sampled coordinator row,
complete target-arm stream, and own-round scalar stream. -/
def sampledCoordinatorProductLaw (p : Parameters) :
    Measure
      (Fin (M p) × (CoordinatorTargetArms p × PlayerRoundScalarStream p)) :=
  ((ContinuousCategorical.massPMF
      (PrivateSourceStreams.coordinatorIndexMass p)
      (PrivateSourceStreams.coordinatorIndexMass_nonneg p)
      (PrivateSourceStreams.coordinatorIndexMass_sum p)).toMeasure).prod
    ((BootstrapPrivateRoundStreams.coordinatorTargetArmLaw p).prod
      (PlayerPrivateCoordinateProduct.roundStreamLaw p))

instance sampledCoordinatorProductLaw_probability (p : Parameters) :
    IsProbabilityMeasure (sampledCoordinatorProductLaw p) := by
  dsimp [sampledCoordinatorProductLaw]
  infer_instance

/-- The sampled law of one player, defined by role from independent
coordinator factors or the follower's original raw factors. -/
def sampledPlayerPrivateLaw (p : Parameters) (j : Fin p.m) :
    Measure (BootstrapPrivateRoundStreams.PlayerPrivateInput p) :=
  if j = PlayerPrivateCoordinateProduct.coordinatorPlayer p then
    (sampledCoordinatorProductLaw p).map Sum.inl
  else (PlayerPrivateCoordinateProduct.followerRawLaw p).map Sum.inr

theorem sampledPlayerPrivateLaw_coordinator (p : Parameters) :
    sampledPlayerPrivateLaw p (PlayerPrivateCoordinateProduct.coordinatorPlayer p) =
      (sampledCoordinatorProductLaw p).map Sum.inl := by
  simp [sampledPlayerPrivateLaw]

theorem sampledPlayerPrivateLaw_follower (p : Parameters)
    (i : Fin (p.m - 1)) :
    sampledPlayerPrivateLaw p (PlayerPrivateCoordinateProduct.followerPlayer p i) =
      (PlayerPrivateCoordinateProduct.followerRawLaw p).map Sum.inr := by
  have hne :
      PlayerPrivateCoordinateProduct.followerPlayer p i ≠
        PlayerPrivateCoordinateProduct.coordinatorPlayer p :=
    (PlayerPrivateCoordinateProduct.coordinatorPlayer_ne_followerPlayer p i).symm
  simp [sampledPlayerPrivateLaw, hne]

instance sampledPlayerPrivateLaw_probability (p : Parameters) (j : Fin p.m) :
    IsProbabilityMeasure (sampledPlayerPrivateLaw p j) := by
  unfold sampledPlayerPrivateLaw
  split_ifs
  · infer_instance
  · infer_instance

/-- Swapping the round and target-scalar factors before mapping the complete
target vector. -/
private theorem map_sampledTargetAndRounds (p : Parameters) :
    Measure.map
        (fun z : PlayerRoundScalarStream p × CoordinatorTargetScalars p =>
          (coordinatorTargetArmMap p z.2, z.1))
        ((PlayerPrivateCoordinateProduct.roundStreamLaw p).prod
          (BootstrapPrivateRoundStreams.coordinatorTargetScalarLaw p)) =
      (BootstrapPrivateRoundStreams.coordinatorTargetArmLaw p).prod
        (PlayerPrivateCoordinateProduct.roundStreamLaw p) := by
  let targetMap := BootstrapPrivateRoundStreams.coordinatorTargetArmMap p
  let μround := PlayerPrivateCoordinateProduct.roundStreamLaw p
  let μtarget := BootstrapPrivateRoundStreams.coordinatorTargetScalarLaw p
  let targetRoundMap :
      CoordinatorTargetScalars p × PlayerRoundScalarStream p →
        CoordinatorTargetArms p × PlayerRoundScalarStream p :=
    fun z => (targetMap z.1, z.2)
  have hmap : Measurable targetRoundMap :=
    ((BootstrapPrivateRoundStreams.measurable_coordinatorTargetArmMap p).comp
      measurable_fst).prodMk measurable_snd
  have hfun :
      (fun z : PlayerRoundScalarStream p × CoordinatorTargetScalars p =>
        (targetMap z.2, z.1)) =
        targetRoundMap ∘ Prod.swap := by
    funext z
    rfl
  calc
    Measure.map
        (fun z : PlayerRoundScalarStream p × CoordinatorTargetScalars p =>
          (coordinatorTargetArmMap p z.2, z.1))
        (μround.prod μtarget) =
      Measure.map targetRoundMap
        (Measure.map Prod.swap (μround.prod μtarget)) := by
          rw [hfun]
          exact (Measure.map_map hmap measurable_swap).symm
    _ = Measure.map targetRoundMap (μtarget.prod μround) := by
      rw [Measure.prod_swap]
    _ = (μtarget.map targetMap).prod (μround.map id) := by
      change Measure.map (Prod.map targetMap id) (μtarget.prod μround) = _
      exact (Measure.map_prod_map μtarget μround
        (BootstrapPrivateRoundStreams.measurable_coordinatorTargetArmMap p)
        measurable_id).symm
    _ = (BootstrapPrivateRoundStreams.coordinatorTargetArmLaw p).prod μround := by
      rw [BootstrapPrivateRoundStreams.coordinatorTargetArmMap_law, Measure.map_id]

/-- The raw coordinator law maps to the required joint law of its sampled
row, all block targets, and complete round stream. -/
theorem sampleCoordinatorRawInput_map_coordinatorRawLaw (p : Parameters) :
    Measure.map (sampleCoordinatorRawInput p)
        (PlayerPrivateCoordinateProduct.coordinatorRawLaw p) =
      sampledCoordinatorProductLaw p := by
  change Measure.map
      (Prod.map (PrivateSourceStreams.coordinatorIndex p)
        (fun z : PlayerRoundScalarStream p × CoordinatorTargetScalars p =>
          (BootstrapPrivateRoundStreams.coordinatorTargetArmMap p z.2, z.1)))
      (PrivateSourceStreams.coordinatorScalarLaw.prod
        ((PlayerPrivateCoordinateProduct.roundStreamLaw p).prod
          (BootstrapPrivateRoundStreams.coordinatorTargetScalarLaw p))) =
    sampledCoordinatorProductLaw p
  calc
    _ =
      (PrivateSourceStreams.coordinatorScalarLaw.map
        (PrivateSourceStreams.coordinatorIndex p)).prod
        (Measure.map
          (fun z : PlayerRoundScalarStream p × CoordinatorTargetScalars p =>
            (BootstrapPrivateRoundStreams.coordinatorTargetArmMap p z.2, z.1))
          ((PlayerPrivateCoordinateProduct.roundStreamLaw p).prod
            (BootstrapPrivateRoundStreams.coordinatorTargetScalarLaw p))) :=
      (Measure.map_prod_map PrivateSourceStreams.coordinatorScalarLaw
        ((PlayerPrivateCoordinateProduct.roundStreamLaw p).prod
          (BootstrapPrivateRoundStreams.coordinatorTargetScalarLaw p))
        (PrivateSourceStreams.measurable_coordinatorIndex p)
        (((BootstrapPrivateRoundStreams.measurable_coordinatorTargetArmMap p).comp
          measurable_snd).prodMk measurable_fst)).symm
    _ =
      (PrivateSourceStreams.coordinatorScalarLaw.map
        (PrivateSourceStreams.coordinatorIndex p)).prod
        ((BootstrapPrivateRoundStreams.coordinatorTargetArmLaw p).prod
          (PlayerPrivateCoordinateProduct.roundStreamLaw p)) := by
      rw [map_sampledTargetAndRounds]
    _ = sampledCoordinatorProductLaw p := by
      change (ContinuousCategorical.uniform.map (PrivateSourceStreams.coordinatorIndex p)).prod _ =
        sampledCoordinatorProductLaw p
      rw [PrivateSourceStreams.coordinatorIndex_uniform_map]
      rfl

/-- Sampling every raw per-player view gives its independently specified
sampled law, with the coordinator and every complementary follower case. -/
theorem samplePrivateInput_map_rawPlayerPrivateLaw (p : Parameters)
    (j : Fin p.m) :
    Measure.map (samplePrivateInput p)
        (PlayerPrivateCoordinateProduct.rawPlayerPrivateLaw p j) =
      sampledPlayerPrivateLaw p j := by
  by_cases hj : j = PlayerPrivateCoordinateProduct.coordinatorPlayer p
  · subst j
    rw [PlayerPrivateCoordinateProduct.rawPlayerPrivateLaw_coordinator,
      sampledPlayerPrivateLaw_coordinator]
    calc
      Measure.map (samplePrivateInput p)
          ((PlayerPrivateCoordinateProduct.coordinatorRawLaw p).map Sum.inl) =
        Measure.map (samplePrivateInput p ∘ Sum.inl)
          (PlayerPrivateCoordinateProduct.coordinatorRawLaw p) :=
        Measure.map_map (measurable_samplePrivateInput p) measurable_inl
      _ = Measure.map (Sum.inl ∘ sampleCoordinatorRawInput p)
          (PlayerPrivateCoordinateProduct.coordinatorRawLaw p) := by
        congr 1
      _ = Measure.map Sum.inl
          (Measure.map (sampleCoordinatorRawInput p)
            (PlayerPrivateCoordinateProduct.coordinatorRawLaw p)) :=
        (Measure.map_map measurable_inl
          (measurable_sampleCoordinatorRawInput p)).symm
      _ = (sampledCoordinatorProductLaw p).map Sum.inl := by
        rw [sampleCoordinatorRawInput_map_coordinatorRawLaw]
  · let i := PlayerPrivateCoordinateProduct.followerSlotOfPlayer p j hj
    have hplayer :
        PlayerPrivateCoordinateProduct.followerPlayer p i = j :=
      PlayerPrivateCoordinateProduct.followerPlayer_followerSlotOfPlayer p j hj
    rw [← hplayer, PlayerPrivateCoordinateProduct.rawPlayerPrivateLaw_follower,
      sampledPlayerPrivateLaw_follower]
    rw [Measure.map_map (measurable_samplePrivateInput p) measurable_inr]
    congr 1

/-- Apply the same role-respecting map at every player label. -/
def sampledPlayerPrivateProfile (p : Parameters)
    (profile : Fin p.m →
      PlayerPrivateCoordinateProduct.RawPlayerPrivateInput p) :
    FiniteBanditModel.Player p.m →
      BootstrapPrivateRoundStreams.PlayerPrivateInput p :=
  fun j => samplePrivateInput p (profile j)

theorem measurable_sampledPlayerPrivateProfile (p : Parameters) :
    Measurable (sampledPlayerPrivateProfile p) := by
  apply measurable_pi_iff.mpr
  intro j
  exact (measurable_samplePrivateInput p).comp (measurable_pi_apply j)

/-- The full raw profile product maps to the local rollout's exact
player-indexed law for the sampled inputs. -/
theorem sampledPlayerPrivateProfile_map_privateProfileLaw (p : Parameters) :
    Measure.map (sampledPlayerPrivateProfile p)
        (MeasurableLocalRollout.privateProfileLaw
          (PlayerPrivateCoordinateProduct.rawPlayerPrivateLaw p)) =
      MeasurableLocalRollout.privateProfileLaw (sampledPlayerPrivateLaw p) := by
  change (Measure.pi (PlayerPrivateCoordinateProduct.rawPlayerPrivateLaw p)).map
      (fun profile j => samplePrivateInput p (profile j)) =
    Measure.pi (sampledPlayerPrivateLaw p)
  calc
    _ = Measure.pi (fun j =>
        Measure.map (samplePrivateInput p)
          (PlayerPrivateCoordinateProduct.rawPlayerPrivateLaw p j)) :=
      Measure.pi_map_pi
        (μ := PlayerPrivateCoordinateProduct.rawPlayerPrivateLaw p)
        (f := fun _ : Fin p.m => samplePrivateInput p)
        (fun _ => (measurable_samplePrivateInput p).aemeasurable)
    _ = Measure.pi (sampledPlayerPrivateLaw p) := by
      congr 1
      funext j
      exact samplePrivateInput_map_rawPlayerPrivateLaw p j

private theorem samplePrivateInput_extendedRawPlayerPrivateProfile_core
    (p : Parameters) (published : CompletePublicTable.PublishedOutput p)
    (e : ExtendedPrivateCoordinates p) (j : Fin p.m) :
    samplePrivateInput p
        (PlayerPrivateCoordinateProduct.extendedRawPlayerPrivateProfile p e j) =
      BootstrapPrivateRoundStreams.sourcePlayerPrivateInput p j (published, e) := by
  classical
  change samplePrivateInput p
      (PlayerPrivateCoordinateProduct.rawPlayerPrivateProfile p
        (PlayerPrivateCoordinateProduct.rawRegroup p e) j) =
    BootstrapPrivateRoundStreams.sourcePlayerPrivateInput p j (published, e)
  by_cases hj : j = PlayerPrivateCoordinateProduct.coordinatorPlayer p
  · subst j
    have hcoord :
        PlayerPrivateCoordinateProduct.coordinatorPlayer p =
          (⟨0, ConstructorDimensions.m_pos p⟩ : Fin p.m) := by
      apply Fin.ext
      rfl
    rw [PlayerPrivateCoordinateProduct.rawPlayerPrivateProfile_coordinator,
      samplePrivateInput_coordinator, hcoord,
      BootstrapPrivateRoundStreams.sourcePlayerPrivateInput_coordinator]
    apply congrArg Sum.inl
    apply Prod.ext
    · change coordinatorIndex p
          ((PlayerPrivateCoordinateProduct.rawRegroup p e).1.1) =
        coordinatorIndex p e.1.2
      rw [PlayerPrivateCoordinateProduct.rawRegroup_coordinatorJ]
    · apply Prod.ext
      · change coordinatorTargetArmMap p
            ((PlayerPrivateCoordinateProduct.rawRegroup p e).1.2.2) =
          coordinatorTargetArmMap p e.2.2
        rw [PlayerPrivateCoordinateProduct.rawRegroup_coordinatorTargets]
      · funext t
        change (PlayerPrivateCoordinateProduct.rawRegroup p e).1.2.1 t =
          e.2.1 (PlayerPrivateCoordinateProduct.coordinatorPlayer p, t)
        rw [PlayerPrivateCoordinateProduct.rawRegroup_coordinatorRound]
  · let i := PlayerPrivateCoordinateProduct.followerSlotOfPlayer p j hj
    have hplayer :
        PlayerPrivateCoordinateProduct.followerPlayer p i = j :=
      PlayerPrivateCoordinateProduct.followerPlayer_followerSlotOfPlayer p j hj
    rw [← hplayer]
    change samplePrivateInput p
        (PlayerPrivateCoordinateProduct.rawPlayerPrivateProfile p
          (PlayerPrivateCoordinateProduct.rawRegroup p e)
          (PlayerPrivateCoordinateProduct.followerPlayer p i)) =
      BootstrapPrivateRoundStreams.sourcePlayerPrivateInput p
        (PlayerPrivateCoordinateProduct.followerPlayer p i) (published, e)
    rw [PlayerPrivateCoordinateProduct.rawPlayerPrivateProfile_follower,
      samplePrivateInput_follower]
    have hlabel :
        PlayerPrivateCoordinateProduct.followerPlayer p i =
          ⟨i.val + 1, by have hi := i.isLt; have hm := p.two_le_m; omega⟩ := rfl
    rw [hlabel, BootstrapPrivateRoundStreams.sourcePlayerPrivateInput_follower]
    apply congrArg Sum.inr
    apply Prod.ext
    · funext b
      exact PlayerPrivateCoordinateProduct.rawRegroup_followerBlock p e b i
    · funext t
      exact PlayerPrivateCoordinateProduct.rawRegroup_followerRound p e i t

/-- For every public output, reward matrix, extended private tuple and player,
the sampled raw view is exactly the protocol's existing local input. The
identity is independent of rewards. -/
theorem samplePrivateInput_extendedRawPlayerPrivateProfile
    (p : Parameters) (published : CompletePublicTable.PublishedOutput p)
    (_rewards : RewardMatrix p.T p.K) (e : ExtendedPrivateCoordinates p)
    (j : Fin p.m) :
    samplePrivateInput p
        (PlayerPrivateCoordinateProduct.extendedRawPlayerPrivateProfile p e j) =
      BootstrapPrivateRoundStreams.sourcePlayerPrivateInput p j (published, e) :=
  samplePrivateInput_extendedRawPlayerPrivateProfile_core p published e j

/-- The actual source local-profile map after fixing its original published
output. -/
def fixedPublicPlayerPrivateProfile (p : Parameters)
    (published : CompletePublicTable.PublishedOutput p)
    (e : ExtendedPrivateCoordinates p) :
    FiniteBanditModel.Player p.m →
      BootstrapPrivateRoundStreams.PlayerPrivateInput p :=
  fun j => BootstrapPrivateRoundStreams.sourcePlayerPrivateInput p j (published, e)

theorem measurable_fixedPublicPlayerPrivateProfile (p : Parameters)
    (published : CompletePublicTable.PublishedOutput p) :
    Measurable (fixedPublicPlayerPrivateProfile p published) := by
  apply measurable_pi_iff.mpr
  intro j
  exact (BootstrapPrivateRoundStreams.measurable_sourcePlayerPrivateInput p j).comp
    (measurable_const.prodMk measurable_id)

/-- Extending the exact pointwise identity to a profile gives the full
fixed-output pushforward of the original private law. -/
theorem fixedPublicPlayerPrivateProfile_map_fixedPublicPrivateLaw
    (p : Parameters) (published : CompletePublicTable.PublishedOutput p)
    (rewards : RewardMatrix p.T p.K) :
    Measure.map (fun e => fun j =>
        BootstrapPrivateRoundStreams.sourcePlayerPrivateInput p j (published, e))
      (BootstrapPrivateRoundStreams.fixedPublicPrivateLaw p published rewards) =
      MeasurableLocalRollout.privateProfileLaw (sampledPlayerPrivateLaw p) := by
  have hprofile :
      (fun e => fun j =>
        BootstrapPrivateRoundStreams.sourcePlayerPrivateInput p j (published, e)) =
      sampledPlayerPrivateProfile p ∘
        PlayerPrivateCoordinateProduct.extendedRawPlayerPrivateProfile p := by
    funext e j
    exact (samplePrivateInput_extendedRawPlayerPrivateProfile_core
      p published e j).symm
  calc
    Measure.map (fun e => fun j =>
        BootstrapPrivateRoundStreams.sourcePlayerPrivateInput p j (published, e))
        (BootstrapPrivateRoundStreams.fixedPublicPrivateLaw p published rewards) =
      Measure.map
        (sampledPlayerPrivateProfile p ∘
          PlayerPrivateCoordinateProduct.extendedRawPlayerPrivateProfile p)
        (BootstrapPrivateRoundStreams.fixedPublicPrivateLaw p published rewards) := by
          rw [hprofile]
    _ = Measure.map (sampledPlayerPrivateProfile p)
        (Measure.map
          (PlayerPrivateCoordinateProduct.extendedRawPlayerPrivateProfile p)
          (BootstrapPrivateRoundStreams.fixedPublicPrivateLaw p published rewards)) :=
      (Measure.map_map (measurable_sampledPlayerPrivateProfile p)
        (PlayerPrivateCoordinateProduct.measurable_extendedRawPlayerPrivateProfile p)).symm
    _ = MeasurableLocalRollout.privateProfileLaw (sampledPlayerPrivateLaw p) := by
      rw [PlayerPrivateCoordinateProduct.extendedRawPlayerPrivateProfile_map_fixedPublicPrivateLaw]
      exact sampledPlayerPrivateProfile_map_privateProfileLaw p

/-- The sampled all-player profile induced directly by the extended private
coordinates. -/
def sampledExtendedPrivateProfile (p : Parameters)
    (e : ExtendedPrivateCoordinates p) :
    FiniteBanditModel.Player p.m →
      BootstrapPrivateRoundStreams.PlayerPrivateInput p :=
  sampledPlayerPrivateProfile p
    (PlayerPrivateCoordinateProduct.extendedRawPlayerPrivateProfile p e)

theorem measurable_sampledExtendedPrivateProfile (p : Parameters) :
    Measurable (sampledExtendedPrivateProfile p) :=
  (measurable_sampledPlayerPrivateProfile p).comp
    (PlayerPrivateCoordinateProduct.measurable_extendedRawPlayerPrivateProfile p)

theorem sampledExtendedPrivateProfile_map_extendedPrivateLaw (p : Parameters) :
    Measure.map (sampledExtendedPrivateProfile p)
        (BootstrapPrivateRoundStreams.extendedPrivateLaw p) =
      MeasurableLocalRollout.privateProfileLaw (sampledPlayerPrivateLaw p) := by
  change Measure.map
      (sampledPlayerPrivateProfile p ∘
        PlayerPrivateCoordinateProduct.extendedRawPlayerPrivateProfile p)
      (BootstrapPrivateRoundStreams.extendedPrivateLaw p) = _
  calc
    _ = Measure.map (sampledPlayerPrivateProfile p)
        (Measure.map
          (PlayerPrivateCoordinateProduct.extendedRawPlayerPrivateProfile p)
          (BootstrapPrivateRoundStreams.extendedPrivateLaw p)) :=
      (Measure.map_map (measurable_sampledPlayerPrivateProfile p)
        (PlayerPrivateCoordinateProduct.measurable_extendedRawPlayerPrivateProfile p)).symm
    _ = MeasurableLocalRollout.privateProfileLaw (sampledPlayerPrivateLaw p) := by
      rw [PlayerPrivateCoordinateProduct.extendedRawPlayerPrivateProfile_map_extendedPrivateLaw]
      exact sampledPlayerPrivateProfile_map_privateProfileLaw p

/-- The original full source input paired with its actual player-local
profile, retaining the original published output as the first coordinate. -/
def sourcePublishedPlayerPrivateProfile
    (p : Parameters) (source : BootstrapPrivateRoundStreams.SourceInput p) :
    CompletePublicTable.PublishedOutput p ×
      (FiniteBanditModel.Player p.m →
        BootstrapPrivateRoundStreams.PlayerPrivateInput p) :=
  (source.1, fun j => BootstrapPrivateRoundStreams.sourcePlayerPrivateInput p j source)

theorem measurable_sourcePublishedPlayerPrivateProfile (p : Parameters) :
    Measurable (sourcePublishedPlayerPrivateProfile p) := by
  have hprofile :
      Measurable (fun source : BootstrapPrivateRoundStreams.SourceInput p =>
        fun j : FiniteBanditModel.Player p.m =>
          BootstrapPrivateRoundStreams.sourcePlayerPrivateInput p j source) := by
    apply measurable_pi_iff.mpr
    intro j
    exact BootstrapPrivateRoundStreams.measurable_sourcePlayerPrivateInput p j
  exact (BootstrapPrivateRoundStreams.measurable_sourcePublishedOutput p).prodMk hprofile

/-- The literal full-source joint law of the published output and actual
sampled local profile. -/
theorem sourcePublishedPlayerPrivateProfile_map_sourceInputLaw (p : Parameters) :
    Measure.map
        (fun source => (source.1, fun j =>
          BootstrapPrivateRoundStreams.sourcePlayerPrivateInput p j source))
        (BootstrapPrivateRoundStreams.sourceInputLaw p) =
      (CompletePublicTable.publishedOutputMeasure p).prod
        (MeasurableLocalRollout.privateProfileLaw (sampledPlayerPrivateLaw p)) := by
  have hmap :
      (fun source : BootstrapPrivateRoundStreams.SourceInput p =>
        (source.1, fun j : FiniteBanditModel.Player p.m =>
          BootstrapPrivateRoundStreams.sourcePlayerPrivateInput p j source)) =
      Prod.map id (sampledExtendedPrivateProfile p) := by
    funext source
    apply Prod.ext
    · rfl
    · funext j
      exact (samplePrivateInput_extendedRawPlayerPrivateProfile_core
        p source.1 source.2 j).symm
  calc
    Measure.map
        (fun source => (source.1, fun j : FiniteBanditModel.Player p.m =>
          BootstrapPrivateRoundStreams.sourcePlayerPrivateInput p j source))
        (BootstrapPrivateRoundStreams.sourceInputLaw p) =
      Measure.map (Prod.map id (sampledExtendedPrivateProfile p))
        (BootstrapPrivateRoundStreams.sourceInputLaw p) := by
          rw [hmap]
    _ = (CompletePublicTable.publishedOutputMeasure p).prod
        (Measure.map (sampledExtendedPrivateProfile p)
          (BootstrapPrivateRoundStreams.extendedPrivateLaw p)) := by
      change Measure.map (Prod.map id (sampledExtendedPrivateProfile p))
          ((CompletePublicTable.publishedOutputMeasure p).prod
            (BootstrapPrivateRoundStreams.extendedPrivateLaw p)) = _
      simpa only [Measure.map_id] using
        (Measure.map_prod_map (CompletePublicTable.publishedOutputMeasure p)
          (BootstrapPrivateRoundStreams.extendedPrivateLaw p)
          measurable_id (measurable_sampledExtendedPrivateProfile p)).symm
    _ = (CompletePublicTable.publishedOutputMeasure p).prod
        (MeasurableLocalRollout.privateProfileLaw (sampledPlayerPrivateLaw p)) := by
      rw [sampledExtendedPrivateProfile_map_extendedPrivateLaw]

end Bandits.Support.PlayerPrivateSampledProduct

end
