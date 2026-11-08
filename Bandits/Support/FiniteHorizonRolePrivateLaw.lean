/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ActualSampledBoundedCoordinatorDecision
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.MeasurableSpace.Embedding

/-!
# Role-correct whole private-profile laws

Each player input is restricted to its actual source role: the coordinator
uses the left-tagged sampled coordinator tuple and each follower uses the
right-tagged complete block and round streams. The source-to-profile map
retains every original coordinate, including the coordinator's sampled row
index. The fixed-output and joint-output laws below are whole-profile laws,
derived from the existing whole-source laws by an injective measurable
erasure map.

The source conventions are in `sources/zip4/manuscript/01_introduction.tex:18-36`,
`sources/zip4/manuscript/07_public_setup.tex:27-38,55-114`, and
`sources/zip4/manuscript/08_main_theorem.tex:26-42,67-75`. These exogenous
private-input laws alone do not establish adaptive independence, a physical
execution identity, a reference coupling, or a regret bound.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions

namespace Bandits.Support.FiniteHorizonRolePrivateLaw

abbrev Parameters := ConstructorDimensions.Parameters

abbrev CoordinatorSampledInput (p : Parameters) :=
  Fin (ConstructorDimensions.M p) ×
    (BootstrapPrivateRoundStreams.CoordinatorTargetArms p ×
      BootstrapPrivateRoundStreams.PlayerRoundScalarStream p)

/-- The actual tagged player-input space used by the source sampler. -/
abbrev PlayerInput (p : Parameters) :=
  BootstrapPrivateRoundStreams.PlayerPrivateInput p

local instance publishedOutputMeasurableSpace (p : Parameters) :
    MeasurableSpace (CompletePublicTable.PublishedOutput p) := by
  change MeasurableSpace
    (CompletePublicTable.IDArray p × CompletePublicTable.CompleteRows p)
  infer_instance

/-- The exact source range available to a player label. -/
def roleValues (p : Parameters) (i : Fin p.m) : Set (PlayerInput p) :=
  if i = PlayerPrivateCoordinateProduct.coordinatorPlayer p then
    Set.range Sum.inl
  else
    Set.range Sum.inr

/-- A player input together with its exact coordinator/follower source tag. -/
abbrev Role (p : Parameters) (i : Fin p.m) :=
  {v : PlayerInput p // v ∈ roleValues p i}

/-- The coordinator's sampled input and its role subtype are measurably
equivalent through the original left sum tag. -/
def coordinatorRoleEquiv (p : Parameters) :
    CoordinatorSampledInput p ≃ᵐ Role p
      (PlayerPrivateCoordinateProduct.coordinatorPlayer p) := by
  change CoordinatorSampledInput p ≃ᵐ
    {v : PlayerInput p // v ∈ Set.range Sum.inl}
  exact (MeasurableEquiv.Set.rangeInl).symm

/-- At every follower label, the original complete follower stream and its
right-tagged role subtype are measurably equivalent. -/
def followerRoleEquiv (p : Parameters) (i : Fin (p.m - 1)) :
    PlayerPrivateCoordinateProduct.FollowerRaw p ≃ᵐ Role p
      (PlayerPrivateCoordinateProduct.followerPlayer p i) := by
  have hrole : roleValues p (PlayerPrivateCoordinateProduct.followerPlayer p i) =
      Set.range Sum.inr := by
    have hne : PlayerPrivateCoordinateProduct.followerPlayer p i ≠
        PlayerPrivateCoordinateProduct.coordinatorPlayer p :=
      (PlayerPrivateCoordinateProduct.coordinatorPlayer_ne_followerPlayer p i).symm
    simp [roleValues, hne]
  change PlayerPrivateCoordinateProduct.FollowerRaw p ≃ᵐ
    {v : PlayerInput p // v ∈
      roleValues p (PlayerPrivateCoordinateProduct.followerPlayer p i)}
  rw [hrole]
  exact (MeasurableEquiv.Set.rangeInr).symm

def coordinatorRoleMap (p : Parameters) (j : Fin p.m)
    (hj : j = PlayerPrivateCoordinateProduct.coordinatorPlayer p) :
    CoordinatorSampledInput p → Role p j :=
  fun z => ⟨Sum.inl z, by
    simp only [roleValues, ite_eq_left hj]
    exact ⟨z, rfl⟩⟩

theorem measurable_coordinatorRoleMap (p : Parameters) (j : Fin p.m)
    (hj : j = PlayerPrivateCoordinateProduct.coordinatorPlayer p) :
    Measurable (coordinatorRoleMap p j hj) := by
  unfold coordinatorRoleMap
  exact Measurable.subtype_mk
    (measurable_inl : Measurable (Sum.inl : CoordinatorSampledInput p → PlayerInput p))

def followerRoleMap (p : Parameters) (j : Fin p.m)
    (hj : j ≠ PlayerPrivateCoordinateProduct.coordinatorPlayer p) :
    PlayerPrivateCoordinateProduct.FollowerRaw p → Role p j :=
  fun z => ⟨Sum.inr z, by
    simp only [roleValues, ite_eq_right hj]
    exact ⟨z, rfl⟩⟩

theorem measurable_followerRoleMap (p : Parameters) (j : Fin p.m)
    (hj : j ≠ PlayerPrivateCoordinateProduct.coordinatorPlayer p) :
    Measurable (followerRoleMap p j hj) := by
  unfold followerRoleMap
  exact Measurable.subtype_mk
    (measurable_inr :
      Measurable (Sum.inr : PlayerPrivateCoordinateProduct.FollowerRaw p → PlayerInput p))

/-- The genuine Borel role law: the coordinator branch maps the sampled
coordinator product into the left-tag range; every other label maps the
original follower product into the right-tag range. -/
def nu (p : Parameters) (i : Fin p.m) : Measure (Role p i) :=
  if h : i = PlayerPrivateCoordinateProduct.coordinatorPlayer p then
    (PlayerPrivateSampledProduct.sampledCoordinatorProductLaw p).map
      (coordinatorRoleMap p i h)
  else
    (PlayerPrivateCoordinateProduct.followerRawLaw p).map
      (followerRoleMap p i h)

instance nu_isProbabilityMeasure (p : Parameters) (i : Fin p.m) :
    IsProbabilityMeasure (nu p i) := by
  unfold nu
  split_ifs <;> infer_instance

/-- The complete dependent product of exact role-specific private inputs. -/
def Profile (p : Parameters) := (i : Fin p.m) → Role p i

local instance playerInputMeasurableSpace (p : Parameters) :
    MeasurableSpace (PlayerInput p) := by
  change MeasurableSpace
    (Sum (Fin (ConstructorDimensions.M p) ×
        (BootstrapPrivateRoundStreams.CoordinatorTargetArms p ×
          BootstrapPrivateRoundStreams.PlayerRoundScalarStream p))
      (PlayerPrivateCoordinateProduct.FollowerRaw p))
  infer_instance

local instance roleProfileMeasurableSpace (p : Parameters) :
    MeasurableSpace (Profile p) := by
  change MeasurableSpace ((i : Fin p.m) → Role p i)
  infer_instance

/-- The product law of the original role-correct private coordinates. -/
def mu (p : Parameters) : Measure (Profile p) := Measure.pi (nu p)

instance mu_isProbabilityMeasure (p : Parameters) : IsProbabilityMeasure (mu p) := by
  change IsProbabilityMeasure (Measure.pi (nu p))
  infer_instance

/-- Erase only the role-membership proofs, retaining each original tagged
player input. -/
def erase (p : Parameters) (rho : Profile p) : Fin p.m → PlayerInput p :=
  fun i => (rho i).val

theorem measurable_erase (p : Parameters) : Measurable (erase p) := by
  apply measurable_pi_iff.mpr
  intro i
  exact measurable_subtype_coe.comp (measurable_pi_apply i)

private theorem roleValues_measurable (p : Parameters) (i : Fin p.m) :
    MeasurableSet (roleValues p i) := by
  unfold roleValues
  split_ifs
  · exact measurableSet_range_inl
  · exact measurableSet_range_inr

private def constrainedProfileSet (p : Parameters) :
    Set (Fin p.m → PlayerInput p) :=
  {f | ∀ i, f i ∈ roleValues p i}

private theorem measurableSet_constrainedProfileSet (p : Parameters) :
    MeasurableSet (constrainedProfileSet p) := by
  rw [show constrainedProfileSet p =
      ⋂ i : Fin p.m, {f : Fin p.m → PlayerInput p | f i ∈ roleValues p i} by
        ext f
        simp [constrainedProfileSet]]
  exact MeasurableSet.iInter (fun i => by
    change MeasurableSet ((fun f : Fin p.m → PlayerInput p => f i) ⁻¹'
      roleValues p i)
    exact measurable_pi_apply i (roleValues_measurable p i))

private def constrainedProfileEquiv (p : Parameters) :
    {f : Fin p.m → PlayerInput p // f ∈ constrainedProfileSet p} ≃ᵐ Profile p :=
  MeasurableEquiv.subtypePiEquivPi (p := fun i v => v ∈ roleValues p i)

private def eraseViaConstrainedProfile (p : Parameters) (rho : Profile p) :
    Fin p.m → PlayerInput p :=
  ((constrainedProfileEquiv p).symm rho).val

private theorem erase_eq_eraseViaConstrainedProfile (p : Parameters) :
    erase p = eraseViaConstrainedProfile p := by
  funext rho i
  rfl

/-- Erasure is a measurable embedding because the role ranges form a
measurable intersection of coordinate constraints. -/
theorem measurableEmbedding_erase (p : Parameters) :
    MeasurableEmbedding (erase p) := by
  rw [erase_eq_eraseViaConstrainedProfile p]
  exact (MeasurableEmbedding.subtype_coe
      (measurableSet_constrainedProfileSet p)).comp
    (constrainedProfileEquiv p).symm.measurableEmbedding

private theorem erase_nu (p : Parameters) (i : Fin p.m) :
    Measure.map (fun x : Role p i => x.val) (nu p i) =
      PlayerPrivateSampledProduct.sampledPlayerPrivateLaw p i := by
  unfold nu
  by_cases hi : i = PlayerPrivateCoordinateProduct.coordinatorPlayer p
  · simp only [dite_eq_left hi]
    rw [Measure.map_map measurable_subtype_coe (measurable_coordinatorRoleMap p i hi)]
    subst i
    change (PlayerPrivateSampledProduct.sampledCoordinatorProductLaw p).map Sum.inl =
      PlayerPrivateSampledProduct.sampledPlayerPrivateLaw p
        (PlayerPrivateCoordinateProduct.coordinatorPlayer p)
    exact (PlayerPrivateSampledProduct.sampledPlayerPrivateLaw_coordinator p).symm
  · simp only [dite_eq_right hi]
    rw [Measure.map_map measurable_subtype_coe (measurable_followerRoleMap p i hi)]
    change (PlayerPrivateCoordinateProduct.followerRawLaw p).map Sum.inr =
      PlayerPrivateSampledProduct.sampledPlayerPrivateLaw p i
    simp [PlayerPrivateSampledProduct.sampledPlayerPrivateLaw, hi]

/-- Erasing the entire dependent product law recovers the accepted
player-indexed law, coordinate by coordinate through `Measure.pi_map_pi`. -/
theorem erase_map_mu (p : Parameters) :
    Measure.map (erase p) (mu p) =
      MeasurableLocalRollout.privateProfileLaw
        (PlayerPrivateSampledProduct.sampledPlayerPrivateLaw p) := by
  change Measure.map (fun rho i => (rho i).val) (Measure.pi (nu p)) =
    Measure.pi (PlayerPrivateSampledProduct.sampledPlayerPrivateLaw p)
  calc
    _ = Measure.pi (fun i =>
        Measure.map (fun x : Role p i => x.val) (nu p i)) :=
      Measure.pi_map_pi
        (μ := nu p)
        (f := fun _ x => x.val)
        (fun i => measurable_subtype_coe.aemeasurable)
    _ = Measure.pi (PlayerPrivateSampledProduct.sampledPlayerPrivateLaw p) := by
      congr 1
      funext i
      exact erase_nu p i

theorem sourceInput_mem_roleValues (p : Parameters)
    (source : BootstrapPrivateRoundStreams.SourceInput p) (i : Fin p.m) :
    BootstrapPrivateRoundStreams.sourcePlayerPrivateInput p i source ∈
      roleValues p i := by
  by_cases hi : i = PlayerPrivateCoordinateProduct.coordinatorPlayer p
  · subst i
    have hlabel : PlayerPrivateCoordinateProduct.coordinatorPlayer p =
        (⟨0, ConstructorDimensions.m_pos p⟩ : Fin p.m) := by
      apply Fin.ext
      rfl
    have hview :
        BootstrapPrivateRoundStreams.sourcePlayerPrivateInput p
          (PlayerPrivateCoordinateProduct.coordinatorPlayer p) source =
        Sum.inl
          (BootstrapPrivateRoundStreams.sourceCoordinatorIndex p source,
            (BootstrapPrivateRoundStreams.sourceCoordinatorTargetArms p source,
              BootstrapPrivateRoundStreams.sourcePlayerRoundScalarStream p
                (PlayerPrivateCoordinateProduct.coordinatorPlayer p) source)) := by
      simpa [hlabel] using
        (BootstrapPrivateRoundStreams.sourcePlayerPrivateInput_coordinator p source)
    simp only [roleValues]
    rw [hview]
    exact ⟨_, rfl⟩
  · let slot := PlayerPrivateCoordinateProduct.followerSlotOfPlayer p i hi
    have hlabel : PlayerPrivateCoordinateProduct.followerPlayer p slot = i :=
      PlayerPrivateCoordinateProduct.followerPlayer_followerSlotOfPlayer p i hi
    have hview :
        BootstrapPrivateRoundStreams.sourcePlayerPrivateInput p i source =
          Sum.inr
            ((fun s => source.2.1.1 s slot),
              BootstrapPrivateRoundStreams.sourcePlayerRoundScalarStream p
                (PlayerPrivateCoordinateProduct.followerPlayer p slot) source) := by
      rw [← hlabel]
      simpa [PlayerPrivateCoordinateProduct.followerPlayer] using
        (BootstrapPrivateRoundStreams.sourcePlayerPrivateInput_follower p slot source)
    simp only [roleValues, ite_eq_right hi]
    rw [hview]
    exact ⟨_, rfl⟩

/-- The actual source-to-profile map, with every subtype proof built from
the source's role tag and the public follower/player inverse. -/
def phi (p : Parameters) (source : BootstrapPrivateRoundStreams.SourceInput p) :
    Profile p :=
  fun i => ⟨BootstrapPrivateRoundStreams.sourcePlayerPrivateInput p i source,
    sourceInput_mem_roleValues p source i⟩

theorem measurable_phi (p : Parameters) :
    Measurable (phi p : BootstrapPrivateRoundStreams.SourceInput p → Profile p) := by
  apply measurable_pi_iff.mpr
  intro i
  exact Measurable.subtype_mk
    (BootstrapPrivateRoundStreams.measurable_sourcePlayerPrivateInput p i)

theorem erase_phi (p : Parameters) (source : BootstrapPrivateRoundStreams.SourceInput p) :
    erase p (phi p source) = fun i =>
      BootstrapPrivateRoundStreams.sourcePlayerPrivateInput p i source := rfl

private theorem measurable_fixedPublicPhi (p : Parameters)
    (published : CompletePublicTable.PublishedOutput p) :
    Measurable (fun e : BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p =>
      phi p (published, e)) :=
  (measurable_phi p).comp (measurable_const.prodMk measurable_id)

private theorem measurable_sourcePhiPair (p : Parameters) :
    Measurable (fun source : BootstrapPrivateRoundStreams.SourceInput p =>
      (source.1, phi p source)) :=
  (BootstrapPrivateRoundStreams.measurable_sourcePublishedOutput p).prodMk
    (measurable_phi p)

/-- For each fixed published output and then every original reward matrix,
the actual role-correct source profile has the literal product law. -/
theorem phi_map_fixedPublicPrivateLaw (p : Parameters)
    (published : CompletePublicTable.PublishedOutput p)
    (rewards : FiniteBanditModel.RewardMatrix p.T p.K) :
    Measure.map (fun e => phi p (published, e))
      (BootstrapPrivateRoundStreams.fixedPublicPrivateLaw p published rewards) =
        mu p := by
  apply (measurableEmbedding_erase p).map_injective
  calc
    Measure.map (erase p)
        (Measure.map (fun e => phi p (published, e))
          (BootstrapPrivateRoundStreams.fixedPublicPrivateLaw p published rewards)) =
      MeasurableLocalRollout.privateProfileLaw
        (PlayerPrivateSampledProduct.sampledPlayerPrivateLaw p) := by
          rw [Measure.map_map (measurable_erase p)
            (measurable_fixedPublicPhi p published)]
          rw [show erase p ∘ (fun e => phi p (published, e)) =
            (fun e => fun i =>
              BootstrapPrivateRoundStreams.sourcePlayerPrivateInput p i
                (published, e)) by
              funext e
              exact erase_phi p (published, e)]
          exact PlayerPrivateSampledProduct.fixedPublicPlayerPrivateProfile_map_fixedPublicPrivateLaw
            p published rewards
    _ = Measure.map (erase p) (mu p) := (erase_map_mu p).symm

private theorem measurableEmbedding_publicErase (p : Parameters) :
    MeasurableEmbedding
      (Prod.map id (erase p) :
        CompletePublicTable.PublishedOutput p × Profile p →
          CompletePublicTable.PublishedOutput p ×
            (Fin p.m → PlayerInput p)) :=
  MeasurableEmbedding.prodMap MeasurableEmbedding.id (measurableEmbedding_erase p)

/-- The joint law retains the original published output and has the same
role-correct private product law; no conditioning or replacement sampler is
introduced. -/
theorem sourcePhiPair_map_sourceInputLaw (p : Parameters) :
    Measure.map (fun source => (source.1, phi p source))
      (BootstrapPrivateRoundStreams.sourceInputLaw p) =
        (CompletePublicTable.publishedOutputMeasure p).prod (mu p) := by
  apply (measurableEmbedding_publicErase p).map_injective
  calc
    Measure.map (Prod.map id (erase p))
        (Measure.map (fun source => (source.1, phi p source))
          (BootstrapPrivateRoundStreams.sourceInputLaw p)) =
      Measure.map
        (fun source => (source.1, fun i =>
          BootstrapPrivateRoundStreams.sourcePlayerPrivateInput p i source))
        (BootstrapPrivateRoundStreams.sourceInputLaw p) := by
          rw [Measure.map_map
            (Measurable.prodMap measurable_id (measurable_erase p))
            (measurable_sourcePhiPair p)]
          congr 1
    _ = (CompletePublicTable.publishedOutputMeasure p).prod
        (MeasurableLocalRollout.privateProfileLaw
          (PlayerPrivateSampledProduct.sampledPlayerPrivateLaw p)) :=
      PlayerPrivateSampledProduct.sourcePublishedPlayerPrivateProfile_map_sourceInputLaw p
    _ = Measure.map (Prod.map id (erase p))
        ((CompletePublicTable.publishedOutputMeasure p).prod (mu p)) := by
          rw [← erase_map_mu p]
          calc
            (CompletePublicTable.publishedOutputMeasure p).prod
                (Measure.map (erase p) (mu p)) =
              (Measure.map id (CompletePublicTable.publishedOutputMeasure p)).prod
                (Measure.map (erase p) (mu p)) := by rw [Measure.map_id]
            _ = Measure.map (Prod.map id (erase p))
                ((CompletePublicTable.publishedOutputMeasure p).prod (mu p)) :=
              Measure.map_prod_map
                (CompletePublicTable.publishedOutputMeasure p) (mu p)
                measurable_id (measurable_erase p)

end Bandits.Support.FiniteHorizonRolePrivateLaw

end
