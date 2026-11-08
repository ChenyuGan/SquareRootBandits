/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.BootstrapModeService

public import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Fixed-snapshot physical bootstrap mode means

The results here concern the existing current-snapshot measure and the
physical actions and feedback from `BootstrapPhysicalBlock`.  They prove the
mixed public-pilot/private-uniform peer law from disjoint coordinates of that
measure, then derive fixed-snapshot DISCOVER, MULTICAST, and one-clock means.
They do not assert a conditional law given physical history or chronological
reachability of a state.

Sources: `sources/zip4/manuscript/07_public_setup.tex:74-103` and
`sources/zip4/manuscript/appendix_b_communication.tex:398-445`.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.BootstrapModeMeans

open ConstructorDimensions BootstrapDimensions FiniteBanditModel
open BootstrapPhysicalBlock BootstrapModeService CompletePublicTable
open ContinuousLearningRows PublicDiscreteDraws
open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical

variable {p : ConstructorDimensions.Parameters} {s : Fin (n_boot p)}

abbrev SlotPilotIndex (p : ConstructorDimensions.Parameters) := Unit ⊕ Player p.m

def slotPilotDrawIndex (p : ConstructorDimensions.Parameters) :
    SlotPilotIndex p → PublicDiscreteDraws.DrawIndex p.m p.K
  | Sum.inl _ => .slot
  | Sum.inr i => .pilot i

def slotPilotOutputMeasure (p : ConstructorDimensions.Parameters) :
    (i : SlotPilotIndex p) →
      Measure (PublicDiscreteDraws.DrawOutput (slotPilotDrawIndex p i))
  | Sum.inl _ => PublicDiscreteDraws.slotPMF.toMeasure
  | Sum.inr _ => privateArmMeasure p

def slotPilotFamily (p : ConstructorDimensions.Parameters) :
    (i : SlotPilotIndex p) → ContinuousControlSlice.Slice p.m p.K →
      PublicDiscreteDraws.DrawOutput (slotPilotDrawIndex p i)
  | Sum.inl _ => PublicDiscreteDraws.drawFamily p.two_le_m p.m_lt_K (K_pos p) .slot
  | Sum.inr i => PublicDiscreteDraws.drawFamily p.two_le_m p.m_lt_K (K_pos p) (.pilot i)

/-- The all-true forward event is measurable in the finite public bit vector. -/
theorem forwardReleaseSet_measurable (p : ConstructorDimensions.Parameters)
    (list : Finset (Fin (A_id p))) :
    MeasurableSet (forwardReleaseSet p list) := by
  classical
  rw [forwardReleaseSet]
  exact MeasurableSet.pi list.countable_toSet (fun _ _ => measurableSet_singleton true)

private theorem privateArmAvoidanceSet_measurable
    (p : ConstructorDimensions.Parameters) (I : Finset (Player p.m)) (a : Arm p.K) :
    MeasurableSet (privateArmAvoidanceSet p I a) := by
  classical
  have hset : privateArmAvoidanceSet p I a =
      Set.univ.pi (fun i : Player p.m =>
        if i ∈ I then {b : Arm p.K | b ≠ a} else Set.univ) := by
    ext v
    simp [privateArmAvoidanceSet, Set.mem_pi]
  rw [hset]
  exact MeasurableSet.univ_pi (fun i => by
    split_ifs <;> exact MeasurableSet.of_discrete)

/-- The actual player labels other than the coordinator and distinguished
follower. -/
def peerPlayers (x : BootstrapPhysicalBlock.Input p s)
    (j : {j // j ∈ x.uninformed}) : Finset (Player p.m) :=
  (Finset.univ.erase (followerPlayer p.two_le_m j.1)).erase
    (ActiveRoundActions.coordinator p.two_le_m)

/-- The physical peer carrier keeps every other player's original label. -/
abbrev Peer (x : BootstrapPhysicalBlock.Input p s)
    (j : {j // j ∈ x.uninformed}) :=
  {i : Player p.m // i ∈ peerPlayers x j}

local instance peerFintype (x : BootstrapPhysicalBlock.Input p s)
    (j : {j // j ∈ x.uninformed}) : Fintype (Peer x j) := Subtype.fintype _

theorem peer_ne_coordinator (x : BootstrapPhysicalBlock.Input p s)
    (j : {j // j ∈ x.uninformed}) (i : Peer x j) :
    i.1 ≠ ActiveRoundActions.coordinator p.two_le_m := by
  have hi := i.2
  simp only [peerPlayers, Finset.mem_erase, Finset.mem_univ] at hi
  exact hi.1

theorem peer_ne_distinguished (x : BootstrapPhysicalBlock.Input p s)
    (j : {j // j ∈ x.uninformed}) (i : Peer x j) :
    i.1 ≠ followerPlayer p.two_le_m j.1 := by
  have hi := i.2
  simp only [peerPlayers, Finset.mem_erase, Finset.mem_univ] at hi
  exact hi.2.1

theorem peer_card (x : BootstrapPhysicalBlock.Input p s)
    (j : {j // j ∈ x.uninformed}) : Fintype.card (Peer x j) = p.m - 2 := by
  classical
  have hcard : Fintype.card (Peer x j) = (peerPlayers x j).card := by
    change Fintype.card {i : Player p.m // i ∈ peerPlayers x j} = _
    rw [Fintype.card_subtype]
    simp
  have hmemJ : followerPlayer p.two_le_m j.1 ∈ (Finset.univ : Finset (Player p.m)) :=
    Finset.mem_univ _
  have hmemC : ActiveRoundActions.coordinator p.two_le_m ∈
      (Finset.univ.erase (followerPlayer p.two_le_m j.1) : Finset (Player p.m)) := by
    simp only [Finset.mem_erase, Finset.mem_univ]
    exact ⟨(ActiveRoundActions.followerPlayer_ne_coordinator p.two_le_m j.1).symm, trivial⟩
  rw [hcard, peerPlayers, Finset.card_erase_of_mem hmemC,
    Finset.card_erase_of_mem hmemJ]
  simp only [Finset.card_univ, Fintype.card_fin]
  omega

/-- A peer is informed precisely when its follower label is outside the
fixed uninformed set. -/
def peerInformed (x : BootstrapPhysicalBlock.Input p s)
    (j : {j // j ∈ x.uninformed}) (i : Peer x j) : Prop :=
  ActiveRoundActions.followerIndex p.two_le_m i.1 (peer_ne_coordinator x j i)
    ∉ x.uninformed

/-- The DATA arm assigned to each peer by the actual policy: public pilot
coordinates for informed followers and the existing private full-arm values
for inactive uninformed followers. -/
def peerDataArms (x : BootstrapPhysicalBlock.Input p s)
    (j : {j // j ∈ x.uninformed})
    (z : RoundCoordinates p × RoundPrivateValues x) : Peer x j → Arm p.K :=
  fun i => if peerInformed x j i then
    publicPilotVectorOnSlice p (roundSlice z.1) i.1
  else z.2.1 i.1

/-- The coordinatewise pair of actual public pilot values and the existing
private full-arm vector. -/
def publicPrivateArmPair (p : ConstructorDimensions.Parameters)
    (q : RoundCoordinates p × (Player p.m → Arm p.K)) :
    Player p.m → Arm p.K × Arm p.K :=
  fun i => (publicPilotVectorOnSlice p (roundSlice q.1) i, q.2 i)

private def armPairMeasure (p : ConstructorDimensions.Parameters) :
    Measure (Arm p.K × Arm p.K) :=
  (privateArmMeasure p).prod (privateArmMeasure p)

private def playerArmPairMeasure (p : ConstructorDimensions.Parameters) :
    Measure (Player p.m → Arm p.K × Arm p.K) :=
  Measure.pi (fun _ : Player p.m => armPairMeasure p)

private instance armPairMeasure_probability (p : ConstructorDimensions.Parameters) :
    IsProbabilityMeasure (armPairMeasure p) := by
  unfold armPairMeasure
  infer_instance

private def peerPairMeasure (x : BootstrapPhysicalBlock.Input p s)
    (j : {j // j ∈ x.uninformed}) : Measure (Peer x j → Arm p.K × Arm p.K) :=
  Measure.pi (fun _ : Peer x j => armPairMeasure p)

def peerPairSplitEquiv (x : BootstrapPhysicalBlock.Input p s)
    (j : {j // j ∈ x.uninformed}) :
    (Player p.m → Arm p.K × Arm p.K) ≃ᵐ
      (Peer x j → Arm p.K × Arm p.K) ×
        ({i : Player p.m // i ∉ peerPlayers x j} → Arm p.K × Arm p.K) :=
  MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Player p.m => Arm p.K × Arm p.K)
    (fun i => i ∈ peerPlayers x j)

private theorem measurePreserving_peerPairSplit
    (x : BootstrapPhysicalBlock.Input p s) (j : {j // j ∈ x.uninformed}) :
    MeasurePreserving (peerPairSplitEquiv x j) (playerArmPairMeasure p)
      ((peerPairMeasure x j).prod
        (Measure.pi fun _ : {i : Player p.m // i ∉ peerPlayers x j} => armPairMeasure p)) := by
  change MeasurePreserving (peerPairSplitEquiv x j)
    (Measure.pi (fun _ : Player p.m => armPairMeasure p))
    ((peerPairMeasure x j).prod
      (Measure.pi fun _ : {i : Player p.m // i ∉ peerPlayers x j} => armPairMeasure p))
  simpa [peerPairSplitEquiv, peerPairMeasure] using
    (measurePreserving_piEquivPiSubtypeProd
      (fun _ : Player p.m => armPairMeasure p)
      (fun i => i ∈ peerPlayers x j))

def peerMixedArmMap (x : BootstrapPhysicalBlock.Input p s)
    (j : {j // j ∈ x.uninformed})
    (q : Peer x j → Arm p.K × Arm p.K) : Peer x j → Arm p.K :=
  fun i => if peerInformed x j i then (q i).1 else (q i).2

private theorem measurePreserving_peerMixedArmMap
    (x : BootstrapPhysicalBlock.Input p s) (j : {j // j ∈ x.uninformed}) :
    MeasurePreserving (peerMixedArmMap x j) (peerPairMeasure x j)
      (Measure.pi (fun _ : Peer x j => privateArmMeasure p)) := by
  classical
  change MeasurePreserving (fun q i =>
      if peerInformed x j i then (q i).1 else (q i).2)
    (Measure.pi fun _ : Peer x j => armPairMeasure p)
    (Measure.pi fun _ : Peer x j => privateArmMeasure p)
  let f : (i : Peer x j) → (Arm p.K × Arm p.K) → Arm p.K :=
    fun i q => if peerInformed x j i then q.1 else q.2
  have hf : ∀ i : Peer x j,
      MeasurePreserving (f i) (armPairMeasure p) (privateArmMeasure p) := by
    intro i
    by_cases hi : peerInformed x j i
    · simpa [f, hi, armPairMeasure] using
        (measurePreserving_fst : MeasurePreserving Prod.fst
          ((privateArmMeasure p).prod (privateArmMeasure p)) (privateArmMeasure p))
    · simpa [f, hi, armPairMeasure] using
        (measurePreserving_snd : MeasurePreserving Prod.snd
          ((privateArmMeasure p).prod (privateArmMeasure p)) (privateArmMeasure p))
  have h := measurePreserving_pi (fun _ : Peer x j => armPairMeasure p)
    (fun _ : Peer x j => privateArmMeasure p) hf
  exact h

private theorem measurePreserving_publicPrivateArmPair
    :
    MeasurePreserving
      (fun q : RoundCoordinates p × (Player p.m → Arm p.K) => publicPrivateArmPair p q)
      ((roundCoordinatesMeasure p).prod (privateArmVectorMeasure p))
      (playerArmPairMeasure p) := by
  let hreshape :=
    (measurePreserving_arrowProdEquivProdArrow (Arm p.K) (Arm p.K) (Player p.m)
      (fun _ => privateArmMeasure p) (fun _ => privateArmMeasure p)).symm
  have hpilot : MeasurePreserving (fun r : RoundCoordinates p =>
      publicPilotVectorOnSlice p (roundSlice r)) (roundCoordinatesMeasure p)
      (privateArmVectorMeasure p) :=
    measurePreserving_roundPublicPilotVector p
  have hpair := hreshape.comp (hpilot.prod (MeasurePreserving.id _))
  change MeasurePreserving (fun q : RoundCoordinates p × (Player p.m → Arm p.K) =>
      publicPrivateArmPair p q) _ (playerArmPairMeasure p)
  exact hpair

/-- Projection of the same physical snapshot onto its public row coordinates
and the actual private full-arm vector. -/
theorem currentSnapshot_coordinates_uniform_measurePreserving
    (x : BootstrapPhysicalBlock.Input p s) (t : Fin p.T) :
    MeasurePreserving (fun z : RoundCoordinates p × RoundPrivateValues x =>
      (z.1, z.2.1)) (currentSnapshotMeasure x t)
      ((roundCoordinatesMeasure p).prod (privateArmVectorMeasure p)) := by
  have huniform : MeasurePreserving Prod.fst (roundPrivateMeasure x)
      (privateArmVectorMeasure p) := by
    change MeasurePreserving Prod.fst
      ((privateArmVectorMeasure p).prod
        ((privateAvoidMeasure p x.target).prod
          (Measure.pi fun k => privateAvoidMeasure p (x.held k))))
      (privateArmVectorMeasure p)
    exact measurePreserving_fst
  exact (MeasurePreserving.id _).prod huniform

private theorem measurePreserving_peerProjection
    (x : BootstrapPhysicalBlock.Input p s) (j : {j // j ∈ x.uninformed}) :
    MeasurePreserving (fun q : (Peer x j → Arm p.K × Arm p.K) ×
        ({i : Player p.m // i ∉ peerPlayers x j} → Arm p.K × Arm p.K) =>
      peerMixedArmMap x j q.1)
      ((peerPairMeasure x j).prod
        (Measure.pi fun _ : {i : Player p.m // i ∉ peerPlayers x j} => armPairMeasure p))
      (Measure.pi (fun _ : Peer x j => privateArmMeasure p)) := by
  classical
  have hfst : MeasurePreserving Prod.fst
      ((peerPairMeasure x j).prod
        (Measure.pi fun _ : {i : Player p.m // i ∉ peerPlayers x j} => armPairMeasure p))
      (peerPairMeasure x j) := measurePreserving_fst
  exact (measurePreserving_peerMixedArmMap x j).comp hfst

/-- The actual mixed public/private peer DATA-arm vector has a product of
uniform arm laws under the same physical current-snapshot measure. This is
derived by splitting the original product coordinates, so it includes the
independence between the public pilot coordinates and private uniform values. -/
def peerDataArmsFromCoordinatesUniform (x : BootstrapPhysicalBlock.Input p s)
    (j : {j // j ∈ x.uninformed})
    (q : RoundCoordinates p × (Player p.m → Arm p.K)) : Peer x j → Arm p.K :=
  peerMixedArmMap x j ((peerPairSplitEquiv x j (publicPrivateArmPair p q)).1)

theorem peerDataArms_eq_coordinatesUniform (x : BootstrapPhysicalBlock.Input p s)
    (j : {j // j ∈ x.uninformed})
    (z : RoundCoordinates p × RoundPrivateValues x) :
    peerDataArms x j z =
      peerDataArmsFromCoordinatesUniform x j (z.1, z.2.1) := by
  funext i
  rfl

theorem peerDataArmsFromCoordinatesUniform_measurePreserving
    (x : BootstrapPhysicalBlock.Input p s) (j : {j // j ∈ x.uninformed}) :
    MeasurePreserving (peerDataArmsFromCoordinatesUniform x j)
      ((roundCoordinatesMeasure p).prod (privateArmVectorMeasure p))
      (Measure.pi (fun _ : Peer x j => privateArmMeasure p)) := by
  classical
  have hFactor := (measurePreserving_peerProjection x j).comp
    ((measurePreserving_peerPairSplit x j).comp
      (measurePreserving_publicPrivateArmPair (p := p)))
  change MeasurePreserving
    (fun q => peerMixedArmMap x j ((peerPairSplitEquiv x j
      (publicPrivateArmPair p q)).1)) _ _
  exact hFactor

theorem peerDataArms_measurePreserving (x : BootstrapPhysicalBlock.Input p s)
    (t : Fin p.T) (j : {j // j ∈ x.uninformed}) :
    MeasurePreserving (peerDataArms x j)
      (currentSnapshotMeasure x t)
      (Measure.pi (fun _ : Peer x j => privateArmMeasure p)) := by
  exact (peerDataArmsFromCoordinatesUniform_measurePreserving x j).comp
    (currentSnapshot_coordinates_uniform_measurePreserving x t)

/-- The entire current public row and private full-arm vector are jointly
independent of the original coordinator complement value. In particular a
consumer may keep DATA, all forward bits, and every peer arm together. -/
theorem currentSnapshot_coordinates_uniform_coordinator_measurePreserving
    (x : BootstrapPhysicalBlock.Input p s) (t : Fin p.T) :
    MeasurePreserving
      (fun z : RoundCoordinates p × RoundPrivateValues x => ((z.1, z.2.1), z.2.2.1))
      (currentSnapshotMeasure x t)
      (((roundCoordinatesMeasure p).prod (privateArmVectorMeasure p)).prod
        (privateAvoidMeasure p x.target)) := by
  have hprivate : MeasurePreserving
      (fun d : RoundPrivateValues x => (d.1, d.2.1)) (roundPrivateMeasure x)
      ((privateArmVectorMeasure p).prod (privateAvoidMeasure p x.target)) := by
    change MeasurePreserving (fun d => (d.1, d.2.1))
      ((privateArmVectorMeasure p).prod
        ((privateAvoidMeasure p x.target).prod
          (Measure.pi fun k => privateAvoidMeasure p (x.held k)))) _
    exact (MeasurePreserving.id _).prod measurePreserving_fst
  exact (measurePreserving_prodAssoc (roundCoordinatesMeasure p)
    (privateArmVectorMeasure p) (privateAvoidMeasure p x.target)).symm.comp
      ((MeasurePreserving.id (roundCoordinatesMeasure p)).prod hprivate)

/-- Any measurable event of the original row and full-arm vector factors
from the coordinator complement value. DATA, forward-list release, and mixed
peer avoidance may be kept jointly in `E`, using the exposed coordinate map. -/
theorem currentSnapshot_event_coordinatorAvoid_mass
    (x : BootstrapPhysicalBlock.Input p s) (t : Fin p.T)
    (E : Set (RoundCoordinates p × (Player p.m → Arm p.K)))
    (B : Set (BootstrapPhysicalBlock.AvoidArm p x.target))
    (hE : MeasurableSet E) (hB : MeasurableSet B) :
    (currentSnapshotMeasure x t).real {z | (z.1, z.2.1) ∈ E ∧ z.2.2.1 ∈ B} =
      ((roundCoordinatesMeasure p).prod (privateArmVectorMeasure p)).real E *
        (privateAvoidMeasure p x.target).real B := by
  calc
    _ = (((roundCoordinatesMeasure p).prod (privateArmVectorMeasure p)).prod
        (privateAvoidMeasure p x.target)).real (E ×ˢ B) :=
      (currentSnapshot_coordinates_uniform_coordinator_measurePreserving x t).measureReal_preimage (hE.prod hB).nullMeasurableSet
    _ = _ := measureReal_prod_prod E B

/-- The mixed peer DATA-arm vector is jointly independent, under the same
current-snapshot measure, of the existing coordinator complement-arm draw.
The second marginal is the actual complement subtype used by multicast. -/
theorem peerData_coordinatorAvoid_measurePreserving
    (x : BootstrapPhysicalBlock.Input p s) (t : Fin p.T)
    (j : {j // j ∈ x.uninformed}) :
    MeasurePreserving (fun z : RoundCoordinates p × RoundPrivateValues x =>
      (peerDataArms x j z, z.2.2.1)) (currentSnapshotMeasure x t)
      ((Measure.pi (fun _ : Peer x j => privateArmMeasure p)).prod
        (privateAvoidMeasure p x.target)) := by
  have hbase := currentSnapshot_coordinates_uniform_coordinator_measurePreserving x t
  have hcombine := (peerDataArmsFromCoordinatesUniform_measurePreserving x j).prod
      (MeasurePreserving.id (privateAvoidMeasure p x.target))
  have heq : (fun z : RoundCoordinates p × RoundPrivateValues x =>
      (peerDataArms x j z, z.2.2.1)) =
      (Prod.map (peerDataArmsFromCoordinatesUniform x j) id) ∘
        (fun z => ((z.1, z.2.1), z.2.2.1)) := by
    funext z
    exact Prod.ext (peerDataArms_eq_coordinatesUniform x j z) rfl
  rw [heq]
  exact hcombine.comp hbase

/-- The public DATA-slot pilots are jointly independent of the slot draw,
because their continuous inputs are the distinct accepted pilot and slot
coordinates of the same slice. -/
theorem measurePreserving_slotPilotVector (p : ConstructorDimensions.Parameters) :
    MeasurePreserving
      (fun u : ContinuousControlSlice.Slice p.m p.K =>
        (slotDraw u, publicPilotVectorOnSlice p u))
      (ContinuousControlSlice.sliceLaw p.m p.K)
      (PublicDiscreteDraws.slotPMF.toMeasure.prod (privateArmVectorMeasure p)) := by
  classical
  have hInjective : Function.Injective (slotPilotDrawIndex p) := by
    intro i k hik
    cases i with
    | inl i => cases k with
      | inl k => have : i = k := Subsingleton.elim _ _; subst k; rfl
      | inr k => cases hik
    | inr i => cases k with
      | inl k => cases hik
      | inr k => cases hik; rfl
  have hdraw := PublicDiscreteDraws.iIndepFun_drawFamily
    p.two_le_m p.m_lt_K (K_pos p)
  have hindDraw : iIndepFun
      (fun i => PublicDiscreteDraws.drawFamily p.two_le_m p.m_lt_K (K_pos p)
        (slotPilotDrawIndex p i)) (ContinuousControlSlice.sliceLaw p.m p.K) :=
    hdraw.precomp (g := slotPilotDrawIndex p) hInjective
  have hind : iIndepFun (slotPilotFamily p) (ContinuousControlSlice.sliceLaw p.m p.K) := by
    convert hindDraw using 1
    funext i u
    cases i <;> rfl
  have hmeas : ∀ i, AEMeasurable (slotPilotFamily p i)
      (ContinuousControlSlice.sliceLaw p.m p.K) := by
    intro i
    cases i with
    | inl q =>
        cases q
        change AEMeasurable (PublicDiscreteDraws.drawFamily p.two_le_m p.m_lt_K
          (K_pos p) .slot) _
        exact (PublicDiscreteDraws.measurable_drawFamily p.two_le_m p.m_lt_K
          (K_pos p) .slot).aemeasurable
    | inr q =>
        change AEMeasurable (PublicDiscreteDraws.drawFamily p.two_le_m p.m_lt_K
          (K_pos p) (.pilot q)) _
        exact (PublicDiscreteDraws.measurable_drawFamily p.two_le_m p.m_lt_K
          (K_pos p) (.pilot q)).aemeasurable
  have hmap := hind.map_fun_eq_pi_map hmeas
  have hmeasureEq : (fun i : SlotPilotIndex p =>
      (ContinuousControlSlice.sliceLaw p.m p.K).map (slotPilotFamily p i)) =
      slotPilotOutputMeasure p := by
    funext i
    cases i with
    | inl q =>
        cases q
        change (ContinuousControlSlice.sliceLaw p.m p.K).map slotDraw =
          PublicDiscreteDraws.slotPMF.toMeasure
        exact PublicDiscreteDraws.map_slotDraw
    | inr q =>
        change (ContinuousControlSlice.sliceLaw p.m p.K).map
            (pilotDraw (K_pos p) q) = privateArmMeasure p
        simpa [privateArmVectorMeasure, privateArmMeasure] using
          (PublicDiscreteDraws.map_pilotDraw (K_pos p) q)
  have hfamily : MeasurePreserving (fun u i => slotPilotFamily p i u)
      (ContinuousControlSlice.sliceLaw p.m p.K)
      (Measure.pi (slotPilotOutputMeasure p)) := by
    refine ⟨measurable_pi_iff.mpr (fun i =>
      match i with
      | Sum.inl _ => PublicDiscreteDraws.measurable_drawFamily p.two_le_m p.m_lt_K
          (K_pos p) .slot
      | Sum.inr q => PublicDiscreteDraws.measurable_drawFamily p.two_le_m p.m_lt_K
          (K_pos p) (.pilot q)), ?_⟩
    change (ContinuousControlSlice.sliceLaw p.m p.K).map (fun u i => slotPilotFamily p i u) = _
    rw [hmap, hmeasureEq]
  have hSigma : ∀ i : SlotPilotIndex p, SigmaFinite (slotPilotOutputMeasure p i) := by
    intro i
    cases i with
    | inl q =>
        cases q
        change SigmaFinite (PublicDiscreteDraws.slotPMF.toMeasure)
        exact IsFiniteMeasure.toSigmaFinite _
    | inr _ =>
        change SigmaFinite (privateArmMeasure p)
        exact IsFiniteMeasure.toSigmaFinite _
  let : ∀ i : SlotPilotIndex p, SigmaFinite (slotPilotOutputMeasure p i) := hSigma
  let e := MeasurableEquiv.sumPiEquivProdPi
    (fun i : SlotPilotIndex p => PublicDiscreteDraws.DrawOutput (slotPilotDrawIndex p i))
  have hsum := measurePreserving_sumPiEquivProdPi (slotPilotOutputMeasure p)
  have hslot : MeasurePreserving
      (MeasurableEquiv.piUnique (fun _ : Unit => PublicDiscreteDraws.Slot))
      (Measure.pi (fun _ : Unit => PublicDiscreteDraws.slotPMF.toMeasure))
      (PublicDiscreteDraws.slotPMF.toMeasure) :=
    measurePreserving_piUnique (fun _ : Unit => PublicDiscreteDraws.slotPMF.toMeasure)
  have hpair := (hslot.prod (MeasurePreserving.id (privateArmVectorMeasure p))).comp hsum
  have hfinal := hpair.comp hfamily
  have heq : (fun u => ((MeasurableEquiv.piUnique
        (fun _ : Unit => PublicDiscreteDraws.Slot))
        ((e ((fun i => slotPilotFamily p i u) : (i : SlotPilotIndex p) →
          PublicDiscreteDraws.DrawOutput (slotPilotDrawIndex p i))).1),
      (e ((fun i => slotPilotFamily p i u) : (i : SlotPilotIndex p) →
        PublicDiscreteDraws.DrawOutput (slotPilotDrawIndex p i))).2)) =
      (fun u => (slotDraw u, publicPilotVectorOnSlice p u)) := by
    funext u
    apply Prod.ext
    · rfl
    · funext i
      rfl
  rw [← heq]
  exact hfinal

/-- The subset of peers supplied by public pilot coordinates. -/
def informedPeers (x : BootstrapPhysicalBlock.Input p s)
    (j : {j // j ∈ x.uninformed}) : Finset (Peer x j) :=
  Finset.univ.filter (fun i => peerInformed x j i)

/-- The subset of peers supplied by private full-arm values. -/
def inactivePeers (x : BootstrapPhysicalBlock.Input p s)
    (j : {j // j ∈ x.uninformed}) : Finset (Peer x j) :=
  Finset.univ.filter (fun i => ¬ peerInformed x j i)

private def peerPlayerImage (x : BootstrapPhysicalBlock.Input p s)
    (j : {j // j ∈ x.uninformed}) (I : Finset (Peer x j)) : Finset (Player p.m) :=
  I.image Subtype.val

private theorem peerPartition_card (x : BootstrapPhysicalBlock.Input p s)
    (j : {j // j ∈ x.uninformed}) :
    (informedPeers x j).card + (inactivePeers x j).card = Fintype.card (Peer x j) := by
  classical
  simpa [informedPeers, inactivePeers] using
    (Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (p := peerInformed x j))

private theorem peerPlayerImage_card (x : BootstrapPhysicalBlock.Input p s)
    (j : {j // j ∈ x.uninformed}) (I : Finset (Peer x j)) :
    (peerPlayerImage x j I).card = I.card := by
  classical
  unfold peerPlayerImage
  exact Finset.card_image_iff.mpr (fun a ha b hb hab => Subtype.val_injective hab)

theorem peerDataAvoidance_mass (x : BootstrapPhysicalBlock.Input p s)
    (t : Fin p.T) (j : {j // j ∈ x.uninformed}) (a : Arm p.K) :
    (currentSnapshotMeasure x t).real
      {z | ∀ i : Peer x j, peerDataArms x j z i ≠ a} =
      (1 - 1 / (p.K : ℝ)) ^ (p.m - 2) := by
  classical
  have hmap := peerDataArms_measurePreserving x t j
  have hset : {v : Peer x j → Arm p.K | ∀ i, v i ≠ a} =
      Set.univ.pi (fun _ : Peer x j => {b : Arm p.K | b ≠ a}) := by
    ext v
    simp [Set.mem_pi]
  have havoid : MeasurableSet ({v : Peer x j → Arm p.K | ∀ i, v i ≠ a}) := by
    rw [hset]
    exact MeasurableSet.univ_pi (fun _ => (measurableSet_singleton a).compl)
  have hpre := hmap.measure_preimage havoid.nullMeasurableSet
  rw [show {z | ∀ i : Peer x j, peerDataArms x j z i ≠ a} =
      (peerDataArms x j) ⁻¹' {v | ∀ i, v i ≠ a} by ext z; simp]
  rw [Measure.real, hpre, hset]
  rw [Measure.pi_pi, ENNReal.toReal_prod]
  have hbase : 0 ≤ 1 - 1 / (p.K : ℝ) := by
    have hK : (1 : ℝ) ≤ (p.K : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt (K_pos p))
    have hinv : 1 / (p.K : ℝ) ≤ 1 := by
      simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hK
    linarith
  calc
    (∏ i : Peer x j, ((privateArmMeasure p) {b : Arm p.K | b ≠ a}).toReal) =
        ∏ _i : Peer x j, (1 - 1 / (p.K : ℝ)) := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [privateArm_noncollision_mass]
      exact ENNReal.toReal_ofReal hbase
    _ = (1 - 1 / (p.K : ℝ)) ^ Fintype.card (Peer x j) := by simp
    _ = (1 - 1 / (p.K : ℝ)) ^ (p.m - 2) := by rw [peer_card]

/-- The same-snapshot mixed peer avoidance event has mass at least a quarter. -/
theorem peerDataAvoidance_mass_ge_quarter (x : BootstrapPhysicalBlock.Input p s)
    (t : Fin p.T) (j : {j // j ∈ x.uninformed}) (a : Arm p.K) :
    (1 / 4 : ℝ) ≤ (currentSnapshotMeasure x t).real
      {z | ∀ i : Peer x j, peerDataArms x j z i ≠ a} := by
  rw [peerDataAvoidance_mass]
  exact BootstrapModeService.otherPlayerAvoidance_power p

/-- Exact probability of DATA, the actual forward-list release event, and
simultaneous avoidance by every physical peer. The public pilot coordinates,
private inactive-follower values, slot coordinate, and forward bits factor
under the same current-snapshot measure. -/
theorem peerData_release_data_mass (x : BootstrapPhysicalBlock.Input p s)
    (t : Fin p.T) (j : {j // j ∈ x.uninformed}) (a : Arm p.K)
    (list : Finset (Fin (A_id p))) :
    (currentSnapshotMeasure x t).real
      {z | roundSlot z.1 = dataSlot ∧
        z.1.1 ∈ forwardReleaseSet p list ∧
        ∀ i : Peer x j, peerDataArms x j z i ≠ a} =
      (1 / 2 : ℝ) * (1 - 1 / (L0 p : ℝ)) ^ list.card *
        (1 - 1 / (p.K : ℝ)) ^ (p.m - 2) := by
  classical
  -- The released DATA event is a rectangle in the original forward, continuous,
  -- and private-vector product coordinates.
  let controlEvent : Set (Slot × (Player p.m → Arm p.K)) :=
    ({dataSlot} : Set Slot) ×ˢ
      privateArmAvoidanceSet p (peerPlayerImage x j (informedPeers x j)) a
  let controlMap : ContinuousControlSlice.Slice p.m p.K →
      Slot × (Player p.m → Arm p.K) :=
    fun u => (slotDraw u, publicPilotVectorOnSlice p u)
  let controlTimeEvent : Set (ContinuousLearningRows.TimeControl p) :=
    {u | controlMap u.1 ∈ controlEvent}
  let uniformEvent : Set (Player p.m → Arm p.K) :=
    privateArmAvoidanceSet p (peerPlayerImage x j (inactivePeers x j)) a
  let rowEvent : Set (RoundCoordinates p) :=
    {r | r.1 ∈ forwardReleaseSet p list ∧ r.2 ∈ controlTimeEvent}
  let relevantEvent : Set (RoundCoordinates p × (Player p.m → Arm p.K)) :=
    rowEvent ×ˢ uniformEvent
  have hslotPilot : MeasurePreserving controlMap
      (ContinuousControlSlice.sliceLaw p.m p.K)
      (PublicDiscreteDraws.slotPMF.toMeasure.prod (privateArmVectorMeasure p)) :=
    measurePreserving_slotPilotVector p
  have hcontrolTime : MeasurePreserving (fun u : ContinuousLearningRows.TimeControl p =>
      controlMap u.1) (ContinuousLearningRows.timeControlLaw p)
      (PublicDiscreteDraws.slotPMF.toMeasure.prod (privateArmVectorMeasure p)) :=
    hslotPilot.comp (ContinuousLearningRows.measurePreserving_slice p)
  have hcontrolAvoid : MeasurableSet controlEvent := by
    exact (measurableSet_singleton dataSlot).prod
      (privateArmAvoidanceSet_measurable p
        (peerPlayerImage x j (informedPeers x j)) a)
  have huniformAvoid : MeasurableSet uniformEvent :=
    privateArmAvoidanceSet_measurable p
      (peerPlayerImage x j (inactivePeers x j)) a
  have hcontrolTimeMeas : MeasurableSet controlTimeEvent :=
    hcontrolAvoid.preimage hcontrolTime.measurable
  have hrowSet : rowEvent =
      forwardReleaseSet p list ×ˢ controlTimeEvent := by
    ext r
    simp [rowEvent, Set.mem_prod]
  have hrowMeas : MeasurableSet rowEvent := by
    rw [hrowSet]
    exact (forwardReleaseSet_measurable p list).prod hcontrolTimeMeas
  have hrelMeas : MeasurableSet relevantEvent := hrowMeas.prod huniformAvoid
  have hRelevant := currentSnapshot_coordinates_uniform_measurePreserving x t
  have hEventEq :
      {z : RoundCoordinates p × RoundPrivateValues x |
        roundSlot z.1 = dataSlot ∧ z.1.1 ∈ forwardReleaseSet p list ∧
        ∀ i : Peer x j, peerDataArms x j z i ≠ a} =
      (fun z : RoundCoordinates p × RoundPrivateValues x => (z.1, z.2.1)) ⁻¹'
        relevantEvent := by
    ext z
    change (roundSlot z.1 = dataSlot ∧ z.1.1 ∈ forwardReleaseSet p list ∧
        ∀ i : Peer x j, peerDataArms x j z i ≠ a) ↔
      ((z.1.1 ∈ forwardReleaseSet p list ∧
        (roundSlot z.1 = dataSlot ∧
          ∀ i ∈ peerPlayerImage x j (informedPeers x j),
            publicPilotVectorOnSlice p (roundSlice z.1) i ≠ a)) ∧
        ∀ k ∈ peerPlayerImage x j (inactivePeers x j), z.2.1 k ≠ a)
    constructor
    · rintro ⟨hdata, hrelease, havoid⟩
      refine ⟨⟨hrelease, hdata, ?_⟩, ?_⟩
      · intro i hi
        rcases Finset.mem_image.mp hi with ⟨q, hq, hqi⟩
        have hqI : peerInformed x j q := (Finset.mem_filter.mp hq).2
        subst i
        have hphysical := havoid q
        simpa [peerDataArms, hqI] using hphysical
      · intro k hk
        rcases Finset.mem_image.mp hk with ⟨q, hq, hqk⟩
        have hqI : ¬ peerInformed x j q := (Finset.mem_filter.mp hq).2
        subst k
        have hphysical := havoid q
        simpa [peerDataArms, hqI] using hphysical
    · rintro ⟨⟨hrelease, hdata, hpublic⟩, huniform⟩
      refine ⟨hdata, hrelease, ?_⟩
      intro i
      by_cases hi : peerInformed x j i
      · have hmem : i.1 ∈ peerPlayerImage x j (informedPeers x j) :=
          Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, rfl⟩
        have hp := hpublic i.1 hmem
        simpa [peerDataArms, hi] using hp
      · have hmem : i.1 ∈ peerPlayerImage x j (inactivePeers x j) :=
          Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, rfl⟩
        have hp : z.2.1 i.1 ≠ a := huniform i.1 hmem
        simpa [peerDataArms, hi] using hp
  rw [hEventEq]
  calc
    (currentSnapshotMeasure x t).real
        ((fun z : RoundCoordinates p × RoundPrivateValues x => (z.1, z.2.1)) ⁻¹'
          relevantEvent) =
        ((roundCoordinatesMeasure p).prod (privateArmVectorMeasure p)).real relevantEvent := by
      exact hRelevant.measureReal_preimage hrelMeas.nullMeasurableSet
    _ = (roundCoordinatesMeasure p).real rowEvent *
        (privateArmVectorMeasure p).real uniformEvent := by
      exact measureReal_prod_prod rowEvent uniformEvent
  have hrow : (roundCoordinatesMeasure p).real rowEvent =
      (1 - 1 / (L0 p : ℝ)) ^ list.card *
        ((1 / 2 : ℝ) *
          (1 - 1 / (p.K : ℝ)) ^ (informedPeers x j).card) := by
    have hcontrolMass : (PublicDiscreteDraws.slotPMF.toMeasure.prod
        (privateArmVectorMeasure p)).real controlEvent =
        (1 / 2 : ℝ) *
          (1 - 1 / (p.K : ℝ)) ^ (informedPeers x j).card := by
      have hset : controlEvent =
          ({dataSlot} : Set Slot) ×ˢ
            privateArmAvoidanceSet p (peerPlayerImage x j (informedPeers x j)) a := by
        ext q
        simp [controlEvent, privateArmAvoidanceSet, Set.mem_pi]
      rw [hset, measureReal_prod_prod]
      have hslot : (PublicDiscreteDraws.slotPMF.toMeasure).real {dataSlot} = 1 / 2 := by
        rw [Measure.real, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
        simp [PublicDiscreteDraws.slotPMF, PublicDiscreteDraws.slotMass_data,
          ContinuousCategorical.massPMF_apply]
      rw [hslot, privateArmVectorAvoidance_mass,
        peerPlayerImage_card]
    have hrelease := BootstrapModeService.forwardRelease_mass p list
    have hmapMass : (ContinuousLearningRows.timeControlLaw p).real
        controlTimeEvent =
        (PublicDiscreteDraws.slotPMF.toMeasure.prod
          (privateArmVectorMeasure p)).real controlEvent := by
      have hpre : (ContinuousLearningRows.timeControlLaw p) controlTimeEvent =
          (PublicDiscreteDraws.slotPMF.toMeasure.prod (privateArmVectorMeasure p))
            controlEvent := by
        calc
          (ContinuousLearningRows.timeControlLaw p) controlTimeEvent =
              ((ContinuousLearningRows.timeControlLaw p).map (fun u => controlMap u.1))
                controlEvent := (Measure.map_apply hcontrolTime.measurable hcontrolAvoid).symm
          _ = _ := congrArg (fun μ => μ controlEvent) hcontrolTime.map_eq
      exact congrArg ENNReal.toReal hpre
    rw [hrowSet]
    change ((roundForwardMeasure p).prod (ContinuousLearningRows.timeControlLaw p)).real
      (forwardReleaseSet p list ×ˢ controlTimeEvent) = _
    rw [measureReal_prod_prod, hrelease, hmapMass, hcontrolMass]
  have huniform : (privateArmVectorMeasure p).real uniformEvent =
      (1 - 1 / (p.K : ℝ)) ^ (inactivePeers x j).card := by
    change (privateArmVectorMeasure p).real
      (privateArmAvoidanceSet p (peerPlayerImage x j (inactivePeers x j)) a) = _
    rw [privateArmVectorAvoidance_mass, peerPlayerImage_card]
  rw [hrow, huniform]
  calc
    _ = (1 / 2 : ℝ) * (1 - 1 / (L0 p : ℝ)) ^ list.card *
        ((1 - 1 / (p.K : ℝ)) ^ (informedPeers x j).card *
          (1 - 1 / (p.K : ℝ)) ^ (inactivePeers x j).card) := by ring
    _ = (1 / 2 : ℝ) * (1 - 1 / (L0 p : ℝ)) ^ list.card *
        (1 - 1 / (p.K : ℝ)) ^ (p.m - 2) := by
      rw [← pow_add, peerPartition_card, peer_card]

/-- On DATA, each physical peer action is exactly its public-pilot or private
full-arm coordinate. The only private followers excluded here are the fixed
distinguished follower and coordinator. -/
theorem peerAction_eq_peerDataArms
    (x : BootstrapPhysicalBlock.Input p s) (st : BootstrapPhysicalBlock.State p)
    (t : Fin p.T) (j : {j // j ∈ x.uninformed}) (i : Peer x j)
    (r : RoundCoordinates p) (d : RoundPrivateValues x)
    (hdata : BootstrapPhysicalBlock.slot (currentInputOf x t r d) t = dataSlot)
    (hinactive : ∀ k : {k // k ∈ x.uninformed}, k ≠ j → x.active k = false) :
    BootstrapPhysicalBlock.actions (currentInputOf x t r d) st t i.1 =
      peerDataArms x j (r, d) i := by
  let y := currentInputOf x t r d
  let k := ActiveRoundActions.followerIndex p.two_le_m i.1
    (peer_ne_coordinator x j i)
  have hplayer : followerPlayer p.two_le_m k = i.1 :=
    ActiveRoundActions.followerPlayer_followerIndex p.two_le_m i.1
      (peer_ne_coordinator x j i)
  by_cases hk : k ∈ x.uninformed
  · let kj : {q // q ∈ x.uninformed} := ⟨k, hk⟩
    have hkneqj : kj ≠ j := by
      intro heq
      apply peer_ne_distinguished x j i
      calc
        i.1 = followerPlayer p.two_le_m k := hplayer.symm
        _ = followerPlayer p.two_le_m j.1 := by
          simpa [kj] using congrArg (fun q : {q // q ∈ x.uninformed} =>
            followerPlayer p.two_le_m q.1) heq
    have hactive : x.active kj = false := hinactive kj hkneqj
    have hmemY : k ∈ y.uninformed := by
      simpa [y, currentInputOf, currentInput] using hk
    have hpeerData : peerDataArms x j (r, d) i = d.1 i.1 := by
      simp [peerDataArms, peerInformed, k, hk]
    calc
      BootstrapPhysicalBlock.actions y st t i.1 =
          BootstrapPhysicalBlock.actions y st t (followerPlayer p.two_le_m k) := by
            rw [hplayer]
      _ = BootstrapPhysicalBlock.followerAction y t k :=
        BootstrapPhysicalBlock.actions_follower y st t k
      _ = BootstrapPhysicalBlock.uninformedAction y t kj := by
        simp only [BootstrapPhysicalBlock.followerAction, dite_eq_left hmemY]
        congr 1
      _ = d.1 i.1 := by
        simpa [BootstrapPhysicalBlock.uninformedAction, hactive, kj, y,
          currentInputOf, currentInput] using congrArg d.1 hplayer
      _ = peerDataArms x j (r, d) i := hpeerData.symm
  · have hnotY : k ∉ y.uninformed := by
      simpa [y, currentInputOf, currentInput] using hk
    have hdataY : BootstrapPhysicalBlock.slot y t = dataSlot := by
      simpa [y] using hdata
    have hpeerData : peerDataArms x j (r, d) i =
        publicPilotVectorOnSlice p (roundSlice r) i.1 := by
      simp [peerDataArms, peerInformed, k, hk]
    calc
      BootstrapPhysicalBlock.actions y st t i.1 =
          BootstrapPhysicalBlock.actions y st t (followerPlayer p.two_le_m k) := by
            rw [hplayer]
      _ = BootstrapPhysicalBlock.followerAction y t k :=
        BootstrapPhysicalBlock.actions_follower y st t k
      _ = BootstrapPhysicalBlock.unoccupiedAction y t k := by
        simp [BootstrapPhysicalBlock.followerAction, hnotY]
      _ = BootstrapPhysicalBlock.pilot y t (followerPlayer p.two_le_m k) := by
        simp [BootstrapPhysicalBlock.unoccupiedAction, hdataY]
      _ = peerDataArms x j (r, d) i := by
        simpa [BootstrapPhysicalBlock.pilot, y, currentInputOf, currentInput,
          publicPilotVectorOnSlice, roundSlice, hplayer] using hpeerData.symm

/-- DISCOVER collision freedom on DATA is exactly the ID-one branch for the
distinguished follower together with avoidance by every other physical peer. -/
theorem discover_collisionFree_iff_peerAvoid
    (x : BootstrapPhysicalBlock.Input p s) (st : BootstrapPhysicalBlock.State p)
    (t : Fin p.T) (j : {j // j ∈ x.uninformed})
    (r : RoundCoordinates p) (d : RoundPrivateValues x) (a : Arm p.K)
    (hmode : st.mode = .discover)
    (hdata : BootstrapPhysicalBlock.slot (currentInputOf x t r d) t = dataSlot)
    (hactive : x.active j = true) (hheld : x.held j = a)
    (htarget : x.target = a)
    (hinactive : ∀ k : {k // k ∈ x.uninformed}, k ≠ j → x.active k = false) :
    FiniteBanditModel.collisionFreeFor
      (BootstrapPhysicalBlock.actions (currentInputOf x t r d) st t)
      (ActiveRoundActions.coordinator p.two_le_m) ↔
      (x.ids (x.privateId j) t = true ∧
        ∀ i : Peer x j, peerDataArms x j (r, d) i ≠ a) := by
  let y := currentInputOf x t r d
  have hcoord : BootstrapPhysicalBlock.actions y st t
      (ActiveRoundActions.coordinator p.two_le_m) = a :=
    coordinatorAction_discover_current x st t r d hmode hdata a htarget
  constructor
  · intro hfree
    have hid : x.ids (x.privateId j) t = true := by
      cases hbit : x.ids (x.privateId j) t with
      | true => rfl
      | false =>
          have hstay := distinguishedFollower_IDzero_action x st t j r d hactive hbit
          have hcollision := hfree (followerPlayer p.two_le_m j.1)
            (ActiveRoundActions.followerPlayer_ne_coordinator p.two_le_m j.1)
          exact False.elim (hcollision (by rw [hstay, hheld, hcoord]))
    refine ⟨hid, ?_⟩
    intro i
    have haction := peerAction_eq_peerDataArms x st t j i r d hdata hinactive
    have hcollision := hfree i.1 (peer_ne_coordinator x j i)
    rw [haction, hcoord] at hcollision
    exact hcollision
  · rintro ⟨hid, hpeer⟩ other hother
    by_cases hj : other = followerPlayer p.two_le_m j.1
    · subst other
      have havoid := distinguishedFollower_IDone_avoids_held
        x st t j r d hactive hid
      rw [hcoord]
      rw [hheld] at havoid
      exact havoid
    · have hmem : other ∈ peerPlayers x j := by
        simp [peerPlayers, hother, hj]
      let i : Peer x j := ⟨other, hmem⟩
      have haction := peerAction_eq_peerDataArms x st t j i r d hdata hinactive
      have havoid := hpeer i
      rw [haction, hcoord]
      exact havoid

/-- The policy's first forward-product update in this snapshot is exactly
the manuscript's all-listed-bits release event, including an empty list. -/
theorem currentForwardProduct_eq_one_iff_release
    (x : BootstrapPhysicalBlock.Input p s) (st : BootstrapPhysicalBlock.State p)
    (t : Fin p.T) (r : RoundCoordinates p) (d : RoundPrivateValues x) :
    BootstrapPhysicalBlock.forwardProduct (currentInputOf x t r d) st t = 1 ↔
      r.1 ∈ forwardReleaseSet p st.list := by
  simp [BootstrapPhysicalBlock.forwardProduct, currentInputOf, currentInput,
    forwardReleaseSet, Finset.prod_eq_one_iff]

/-- In MULTICAST with the stipulated held target, feedback for the ID-zero
distinguished follower is collision-free exactly when the same-round
forward-list release occurs and all other physical peers avoid that target. -/
theorem multicast_collisionFree_iff_release_peerAvoid
    (x : BootstrapPhysicalBlock.Input p s) (st : BootstrapPhysicalBlock.State p)
    (t : Fin p.T) (j : {j // j ∈ x.uninformed})
    (r : RoundCoordinates p) (d : RoundPrivateValues x) (a : Arm p.K)
    (hcal : t ∈ BootstrapDimensions.calendarBlock p s)
    (hmode : st.mode = .multicast)
    (hdata : BootstrapPhysicalBlock.slot (currentInputOf x t r d) t = dataSlot)
    (hactive : x.active j = true) (hid : x.ids (x.privateId j) t = false)
    (hheld : x.held j = a) (htarget : x.target = a)
    (hinactive : ∀ k : {k // k ∈ x.uninformed}, k ≠ j → x.active k = false) :
    FiniteBanditModel.collisionFreeFor
      (BootstrapPhysicalBlock.actions (currentInputOf x t r d) st t)
      (followerPlayer p.two_le_m j.1) ↔
      (r.1 ∈ forwardReleaseSet p st.list ∧
        ∀ i : Peer x j, peerDataArms x j (r, d) i ≠ a) := by
  let y := currentInputOf x t r d
  have hproduct := currentForwardProduct_eq_one_iff_release x st t r d
  have hcoord := multicastCoordinatorAction_current x st t r d hcal hmode hdata
  have hdist : BootstrapPhysicalBlock.actions y st t
      (followerPlayer p.two_le_m j.1) = a := by
    have hstay := distinguishedFollower_IDzero_action x st t j r d hactive hid
    rw [hstay, hheld]
  constructor
  · intro hfree
    have hcoordFree := hfree (ActiveRoundActions.coordinator p.two_le_m)
      (ActiveRoundActions.followerPlayer_ne_coordinator p.two_le_m j.1).symm
    have hrelease : r.1 ∈ forwardReleaseSet p st.list := by
      by_cases hr : r.1 ∈ forwardReleaseSet p st.list
      · exact hr
      · have hno : BootstrapPhysicalBlock.forwardProduct y st t ≠ 1 :=
          fun hp => hr (hproduct.mp hp)
        have hnoCurrent : BootstrapPhysicalBlock.forwardProduct
            (currentInputOf x t r d) st t ≠ 1 := by
          simpa [y] using hno
        have hcoordTarget : BootstrapPhysicalBlock.actions y st t
            (ActiveRoundActions.coordinator p.two_le_m) = a := by
          rw [hcoord]
          rw [ite_eq_right hnoCurrent]
          simpa [currentInputOf, currentInput] using htarget
        exact False.elim (hcoordFree (by rw [hcoordTarget, hdist]))
    refine ⟨hrelease, ?_⟩
    intro i
    have haction := peerAction_eq_peerDataArms x st t j i r d hdata hinactive
    have hcollision := hfree i.1 (peer_ne_distinguished x j i)
    rw [haction, hdist] at hcollision
    exact hcollision
  · rintro ⟨hrelease, hpeer⟩ other hother
    by_cases hc : other = ActiveRoundActions.coordinator p.two_le_m
    · subst other
      have hcoordAvoid : (d.2.1).val ≠ a := by
        intro heq
        exact (d.2.1).property (heq.trans htarget.symm)
      have hcoordEq : BootstrapPhysicalBlock.actions y st t
          (ActiveRoundActions.coordinator p.two_le_m) = (d.2.1).val := by
        rw [hcoord, hproduct.mpr hrelease]
        simp [currentInputOf, currentInput]
      rw [hcoordEq, hdist]
      exact hcoordAvoid
    · by_cases hj : other = followerPlayer p.two_le_m j.1
      · exact False.elim (hother hj)
      · have hmem : other ∈ peerPlayers x j := by simp [peerPlayers, hc, hj]
        let i : Peer x j := ⟨other, hmem⟩
        have haction := peerAction_eq_peerDataArms x st t j i r d hdata hinactive
        have havoid := hpeer i
        rw [haction, hdist]
        exact havoid

/-- The measurable peer-coordinate avoidance event. -/
def peerDataAvoidSet (x : BootstrapPhysicalBlock.Input p s)
    (j : {j // j ∈ x.uninformed}) (a : Arm p.K) : Set (Peer x j → Arm p.K) :=
  {v | ∀ i, v i ≠ a}

theorem peerDataAvoidSet_measurable (x : BootstrapPhysicalBlock.Input p s)
    (j : {j // j ∈ x.uninformed}) (a : Arm p.K) :
    MeasurableSet (peerDataAvoidSet x j a) := by
  have hset : peerDataAvoidSet x j a =
      Set.univ.pi (fun _ : Peer x j => {b : Arm p.K | b ≠ a}) := by
    ext v
    simp [peerDataAvoidSet, Set.mem_pi]
  rw [hset]
  exact MeasurableSet.univ_pi (fun _ => (measurableSet_singleton a).compl)

/-- DATA and simultaneous avoidance by every physical peer, under the actual
current-snapshot measure. -/
def dataPeerAvoidEvent (x : BootstrapPhysicalBlock.Input p s) (_t : Fin p.T)
    (j : {j // j ∈ x.uninformed}) (a : Arm p.K) :
    Set (RoundCoordinates p × RoundPrivateValues x) :=
  {z | roundSlot z.1 = dataSlot ∧
    peerDataArms x j z ∈ peerDataAvoidSet x j a}

/-- DATA, the actual same-round forward-list release, and simultaneous
avoidance by every physical peer. -/
def dataReleasePeerAvoidEvent (x : BootstrapPhysicalBlock.Input p s)
    (_t : Fin p.T) (j : {j // j ∈ x.uninformed}) (a : Arm p.K)
    (list : Finset (Fin (A_id p))) : Set (RoundCoordinates p × RoundPrivateValues x) :=
  {z | roundSlot z.1 = dataSlot ∧ z.1.1 ∈ forwardReleaseSet p list ∧
    peerDataArms x j z ∈ peerDataAvoidSet x j a}

theorem dataPeerAvoidEvent_measurable (x : BootstrapPhysicalBlock.Input p s)
    (t : Fin p.T) (j : {j // j ∈ x.uninformed}) (a : Arm p.K) :
    MeasurableSet (dataPeerAvoidEvent x t j a) := by
  have hslot : Measurable (fun z : RoundCoordinates p × RoundPrivateValues x =>
      roundSlot z.1) :=
    (BootstrapModeService.measurePreserving_roundSlot p).measurable.comp measurable_fst
  have hpeer : Measurable (fun z : RoundCoordinates p × RoundPrivateValues x =>
      peerDataArms x j z) := (peerDataArms_measurePreserving x t j).measurable
  exact ((measurableSet_singleton dataSlot).preimage hslot).inter
    ((peerDataAvoidSet_measurable x j a).preimage hpeer)

theorem dataReleasePeerAvoidEvent_measurable
    (x : BootstrapPhysicalBlock.Input p s) (t : Fin p.T)
    (j : {j // j ∈ x.uninformed}) (a : Arm p.K)
    (list : Finset (Fin (A_id p))) :
    MeasurableSet (dataReleasePeerAvoidEvent x t j a list) := by
  have hslot : Measurable (fun z : RoundCoordinates p × RoundPrivateValues x =>
      roundSlot z.1) :=
    (BootstrapModeService.measurePreserving_roundSlot p).measurable.comp measurable_fst
  have hforward : Measurable
      (fun z : RoundCoordinates p × RoundPrivateValues x => z.1.1) :=
    measurable_fst.comp measurable_fst
  have hpeer : Measurable (fun z : RoundCoordinates p × RoundPrivateValues x =>
      peerDataArms x j z) := (peerDataArms_measurePreserving x t j).measurable
  have hdata := (measurableSet_singleton dataSlot).preimage hslot
  have hrelease := (forwardReleaseSet_measurable p list).preimage hforward
  have havoid := (peerDataAvoidSet_measurable x j a).preimage hpeer
  have hset : dataReleasePeerAvoidEvent x t j a list =
      (((fun z : RoundCoordinates p × RoundPrivateValues x => roundSlot z.1) ⁻¹'
          ({dataSlot} : Set Slot)) ∩
        ((fun z : RoundCoordinates p × RoundPrivateValues x => z.1.1) ⁻¹'
          forwardReleaseSet p list)) ∩
        ((fun z : RoundCoordinates p × RoundPrivateValues x => peerDataArms x j z) ⁻¹'
          peerDataAvoidSet x j a) := by
    ext z
    simp [dataReleasePeerAvoidEvent, peerDataAvoidSet, and_assoc]
  rw [hset]
  exact (hdata.inter hrelease).inter havoid

/-- The existing DISCOVER indicator is one exactly on DATA rounds where the
fixed reward is supported, the distinguished follower takes the genuine
held-arm complement, and every other physical DATA arm avoids the target. -/
theorem discoveryIndicator_eq_one_iff_peerDataEvent
    (x : BootstrapPhysicalBlock.Input p s) (st : BootstrapPhysicalBlock.State p)
    (t : Fin p.T) (j : {j // j ∈ x.uninformed})
    (r : RoundCoordinates p) (d : RoundPrivateValues x) (a : Arm p.K)
    (hcal : t ∈ BootstrapDimensions.calendarBlock p s)
    (hmode : st.mode = .discover)
    (hactive : x.active j = true) (hheld : x.held j = a)
    (htarget : x.target = a)
    (hinactive : ∀ k : {k // k ∈ x.uninformed}, k ≠ j → x.active k = false) :
    discoveryIndicator x st t r d = 1 ↔
      (x.ids (x.privateId j) t = true ∧ chi x t a = 1 ∧
        (r, d) ∈ dataPeerAvoidEvent x t j a) := by
  have hslotEq : BootstrapPhysicalBlock.slot (currentInputOf x t r d) t =
      roundSlot r := by
    simp [currentInputOf, currentInput, BootstrapPhysicalBlock.slot,
      roundSlot, roundSlice]
  by_cases hdata : BootstrapPhysicalBlock.slot (currentInputOf x t r d) t = dataSlot
  · rw [BootstrapModeService.discoveryIndicator_eq_one_iff
      x st t r d hcal a hmode hdata htarget]
    rw [discover_collisionFree_iff_peerAvoid
      x st t j r d a hmode hdata hactive hheld htarget hinactive]
    have hdataRound : roundSlot r = dataSlot := by rw [← hslotEq, hdata]
    simp only [dataPeerAvoidEvent, Set.mem_ofPred_eq, peerDataAvoidSet]
    constructor
    · rintro ⟨hchi, hid, hpeer⟩
      exact ⟨hid, hchi, hdataRound, hpeer⟩
    · rintro ⟨hid, hchi, _hslot, hpeer⟩
      exact ⟨hchi, hid, hpeer⟩
  · have hdataRound : roundSlot r ≠ dataSlot := by
      intro hr
      exact hdata (by rw [hslotEq, hr])
    simp [discoveryIndicator, hmode, hdata, dataPeerAvoidEvent, hdataRound]

/-- The existing MULTICAST indicator is one exactly on the same-round DATA
release event, with ID zero and supported held-target reward. -/
theorem multicastIndicator_eq_one_iff_releasePeerEvent
    (x : BootstrapPhysicalBlock.Input p s) (st : BootstrapPhysicalBlock.State p)
    (t : Fin p.T) (j : {j // j ∈ x.uninformed})
    (r : RoundCoordinates p) (d : RoundPrivateValues x) (a : Arm p.K)
    (hcal : t ∈ BootstrapDimensions.calendarBlock p s)
    (hmem : x.privateId j ∈ st.list) (hcard : st.list.card ≤ L0 p)
    (hmode : st.mode = .multicast)
    (hactive : x.active j = true) (hheld : x.held j = a) (htarget : x.target = a)
    (hinactive : ∀ k : {k // k ∈ x.uninformed}, k ≠ j → x.active k = false) :
    multicastIndicator x st t j r d = 1 ↔
      (x.ids (x.privateId j) t = false ∧ chi x t a = 1 ∧
        (r, d) ∈ dataReleasePeerAvoidEvent x t j a st.list) := by
  have _hlistNonempty : st.list.Nonempty :=
    BootstrapModeService.multicast_membership_nonempty x st j hmem
  have hslotEq : BootstrapPhysicalBlock.slot (currentInputOf x t r d) t =
      roundSlot r := by
    simp [currentInputOf, currentInput, BootstrapPhysicalBlock.slot,
      roundSlot, roundSlice]
  by_cases hdata : BootstrapPhysicalBlock.slot (currentInputOf x t r d) t = dataSlot
  · by_cases hid : x.ids (x.privateId j) t = false
    · rw [BootstrapModeService.multicastIndicator_eq_one_iff
        x st t j r d hcal hmem hcard a hmode hdata hactive hid hheld htarget]
      rw [multicast_collisionFree_iff_release_peerAvoid
        x st t j r d a hcal hmode hdata hactive hid hheld htarget hinactive]
      have hdataRound : roundSlot r = dataSlot := by rw [← hslotEq, hdata]
      simp only [dataReleasePeerAvoidEvent, Set.mem_ofPred_eq, peerDataAvoidSet]
      constructor
      · rintro ⟨hchi, hrelease, hpeer⟩
        exact ⟨hid, hchi, hdataRound, hrelease, hpeer⟩
      · rintro ⟨_hid, hchi, _hslot, hrelease, hpeer⟩
        exact ⟨hchi, hrelease, hpeer⟩
    · have hidOne : x.ids (x.privateId j) t = true := by
        cases hbit : x.ids (x.privateId j) t with
        | false => exact False.elim (hid hbit)
        | true => rfl
      simp [multicastIndicator, hmode, hidOne, dataReleasePeerAvoidEvent]
  · have hdataRound : roundSlot r ≠ dataSlot := by
      intro hr
      exact hdata (by rw [hslotEq, hr])
    simp [multicastIndicator, hmode, hdata, dataReleasePeerAvoidEvent,
      hdataRound]

private theorem function_eq_event_indicator {Ω : Type*} (f : Ω → ℝ)
    (E : Set Ω) (h01 : ∀ z, f z = 0 ∨ f z = 1)
    (hone : ∀ z, f z = 1 ↔ z ∈ E) :
    f = E.indicator (fun _ => (1 : ℝ)) := by
  funext z
  by_cases hz : z ∈ E
  · have hvalue := (hone z).2 hz
    simp [hz, hvalue]
  · have hne : f z ≠ 1 := fun hvalue => hz ((hone z).1 hvalue)
    rcases h01 z with hzero | honeValue
    · simp [hz, hzero]
    · exact False.elim (hne honeValue)

private theorem function_eq_zero_of_no_one {Ω : Type*} (f : Ω → ℝ)
    (h01 : ∀ z, f z = 0 ∨ f z = 1) (hone : ∀ z, f z ≠ 1) :
    f = fun _ => 0 := by
  funext z
  rcases h01 z with hzero | honeValue
  · exact hzero
  · exact False.elim (hone z honeValue)

private theorem chi_zero_or_one (x : BootstrapPhysicalBlock.Input p s)
    (t : Fin p.T) (a : Arm p.K) : chi x t a = 0 ∨ chi x t a = 1 := by
  unfold chi
  split_ifs <;> simp

private theorem chi_eq_zero_of_ne_one (x : BootstrapPhysicalBlock.Input p s)
    (t : Fin p.T) (a : Arm p.K) (h : chi x t a ≠ 1) : chi x t a = 0 := by
  rcases chi_zero_or_one x t a with hzero | hone
  · exact hzero
  · exact False.elim (h hone)

private theorem dataPeerAvoidEvent_mass (x : BootstrapPhysicalBlock.Input p s)
    (t : Fin p.T) (j : {j // j ∈ x.uninformed}) (a : Arm p.K) :
    (currentSnapshotMeasure x t).real (dataPeerAvoidEvent x t j a) =
      (1 / 2 : ℝ) * (1 - 1 / (p.K : ℝ)) ^ (p.m - 2) := by
  have h := peerData_release_data_mass x t j a ∅
  simpa [dataPeerAvoidEvent, peerDataAvoidSet, forwardReleaseSet] using h

private theorem discoveryFunction_event_eq
    (x : BootstrapPhysicalBlock.Input p s) (st : BootstrapPhysicalBlock.State p)
    (t : Fin p.T) (j : {j // j ∈ x.uninformed}) (a : Arm p.K)
    (hcal : t ∈ BootstrapDimensions.calendarBlock p s)
    (hmode : st.mode = .discover) (hactive : x.active j = true)
    (hheld : x.held j = a) (htarget : x.target = a)
    (hinactive : ∀ k : {k // k ∈ x.uninformed}, k ≠ j → x.active k = false)
    (hid : x.ids (x.privateId j) t = true) (hchi : chi x t a = 1) :
    (fun z : RoundCoordinates p × RoundPrivateValues x =>
      discoveryIndicator x st t z.1 z.2) =
      (dataPeerAvoidEvent x t j a).indicator (fun _ => (1 : ℝ)) := by
  apply function_eq_event_indicator
  · intro z
    unfold discoveryIndicator
    split_ifs <;> simp
  · intro z
    simpa [hid, hchi] using
      (discoveryIndicator_eq_one_iff_peerDataEvent x st t j z.1 z.2 a
        hcal hmode hactive hheld htarget hinactive)

private theorem discoveryFunction_zero
    (x : BootstrapPhysicalBlock.Input p s) (st : BootstrapPhysicalBlock.State p)
    (t : Fin p.T) (j : {j // j ∈ x.uninformed}) (a : Arm p.K)
    (hcal : t ∈ BootstrapDimensions.calendarBlock p s)
    (hmode : st.mode = .discover) (hactive : x.active j = true)
    (hheld : x.held j = a) (htarget : x.target = a)
    (hinactive : ∀ k : {k // k ∈ x.uninformed}, k ≠ j → x.active k = false)
    (hflag : ¬ (x.ids (x.privateId j) t = true ∧ chi x t a = 1)) :
    (fun z : RoundCoordinates p × RoundPrivateValues x =>
      discoveryIndicator x st t z.1 z.2) = fun _ => 0 := by
  apply function_eq_zero_of_no_one
  · intro z
    unfold discoveryIndicator
    split_ifs <;> simp
  · intro z hone
    have h := discoveryIndicator_eq_one_iff_peerDataEvent x st t j z.1 z.2 a
      hcal hmode hactive hheld htarget hinactive
    exact hflag ⟨h.mp hone |>.1, (h.mp hone).2.1⟩

private theorem multicastFunction_event_eq
    (x : BootstrapPhysicalBlock.Input p s) (st : BootstrapPhysicalBlock.State p)
    (t : Fin p.T) (j : {j // j ∈ x.uninformed}) (a : Arm p.K)
    (hcal : t ∈ BootstrapDimensions.calendarBlock p s)
    (hmem : x.privateId j ∈ st.list) (hcard : st.list.card ≤ L0 p)
    (hmode : st.mode = .multicast) (hactive : x.active j = true)
    (hheld : x.held j = a) (htarget : x.target = a)
    (hinactive : ∀ k : {k // k ∈ x.uninformed}, k ≠ j → x.active k = false)
    (hid : x.ids (x.privateId j) t = false) (hchi : chi x t a = 1) :
    (fun z : RoundCoordinates p × RoundPrivateValues x =>
      multicastIndicator x st t j z.1 z.2) =
      (dataReleasePeerAvoidEvent x t j a st.list).indicator (fun _ => (1 : ℝ)) := by
  apply function_eq_event_indicator
  · intro z
    unfold multicastIndicator
    split_ifs <;> simp
  · intro z
    simpa [hid, hchi] using
      (multicastIndicator_eq_one_iff_releasePeerEvent x st t j z.1 z.2 a
        hcal hmem hcard hmode hactive hheld htarget hinactive)

private theorem multicastFunction_zero
    (x : BootstrapPhysicalBlock.Input p s) (st : BootstrapPhysicalBlock.State p)
    (t : Fin p.T) (j : {j // j ∈ x.uninformed}) (a : Arm p.K)
    (hcal : t ∈ BootstrapDimensions.calendarBlock p s)
    (hmem : x.privateId j ∈ st.list) (hcard : st.list.card ≤ L0 p)
    (hmode : st.mode = .multicast) (hactive : x.active j = true)
    (hheld : x.held j = a) (htarget : x.target = a)
    (hinactive : ∀ k : {k // k ∈ x.uninformed}, k ≠ j → x.active k = false)
    (hflag : ¬ (x.ids (x.privateId j) t = false ∧ chi x t a = 1)) :
    (fun z : RoundCoordinates p × RoundPrivateValues x =>
      multicastIndicator x st t j z.1 z.2) = fun _ => 0 := by
  apply function_eq_zero_of_no_one
  · intro z
    unfold multicastIndicator
    split_ifs <;> simp
  · intro z hone
    have h := multicastIndicator_eq_one_iff_releasePeerEvent x st t j z.1 z.2 a
      hcal hmem hcard hmode hactive hheld htarget hinactive
    exact hflag ⟨h.mp hone |>.1, (h.mp hone).2.1⟩

/-- Measurability includes both ID values and zero supported reward. -/
theorem discoveryIndicator_measurable
    (x : BootstrapPhysicalBlock.Input p s) (st : BootstrapPhysicalBlock.State p)
    (t : Fin p.T) (j : {j // j ∈ x.uninformed}) (a : Arm p.K)
    (hcal : t ∈ BootstrapDimensions.calendarBlock p s)
    (hmode : st.mode = .discover) (hactive : x.active j = true)
    (hheld : x.held j = a) (htarget : x.target = a)
    (hinactive : ∀ k : {k // k ∈ x.uninformed}, k ≠ j → x.active k = false) :
    Measurable (fun z : RoundCoordinates p × RoundPrivateValues x =>
      discoveryIndicator x st t z.1 z.2) := by
  by_cases hflag : x.ids (x.privateId j) t = true ∧ chi x t a = 1
  · rw [discoveryFunction_event_eq x st t j a hcal hmode hactive hheld htarget
      hinactive hflag.1 hflag.2]
    exact measurable_const.indicator (dataPeerAvoidEvent_measurable x t j a)
  · rw [discoveryFunction_zero x st t j a hcal hmode hactive hheld htarget hinactive hflag]
    exact measurable_const

/-- The actual multicast indicator is measurable with its explicit list inputs. -/
theorem multicastIndicator_measurable
    (x : BootstrapPhysicalBlock.Input p s) (st : BootstrapPhysicalBlock.State p)
    (t : Fin p.T) (j : {j // j ∈ x.uninformed}) (a : Arm p.K)
    (hcal : t ∈ BootstrapDimensions.calendarBlock p s)
    (hmem : x.privateId j ∈ st.list) (hcard : st.list.card ≤ L0 p)
    (hmode : st.mode = .multicast) (hactive : x.active j = true)
    (hheld : x.held j = a) (htarget : x.target = a)
    (hinactive : ∀ k : {k // k ∈ x.uninformed}, k ≠ j → x.active k = false) :
    Measurable (fun z : RoundCoordinates p × RoundPrivateValues x =>
      multicastIndicator x st t j z.1 z.2) := by
  by_cases hflag : x.ids (x.privateId j) t = false ∧ chi x t a = 1
  · rw [multicastFunction_event_eq x st t j a hcal hmem hcard hmode hactive hheld
      htarget hinactive hflag.1 hflag.2]
    exact measurable_const.indicator (dataReleasePeerAvoidEvent_measurable x t j a st.list)
  · rw [multicastFunction_zero x st t j a hcal hmem hcard hmode hactive hheld
      htarget hinactive hflag]
    exact measurable_const

theorem discoveryIndicator_integrable
    (x : BootstrapPhysicalBlock.Input p s) (st : BootstrapPhysicalBlock.State p)
    (t : Fin p.T) (j : {j // j ∈ x.uninformed}) (a : Arm p.K)
    (hcal : t ∈ BootstrapDimensions.calendarBlock p s)
    (hmode : st.mode = .discover) (hactive : x.active j = true)
    (hheld : x.held j = a) (htarget : x.target = a)
    (hinactive : ∀ k : {k // k ∈ x.uninformed}, k ≠ j → x.active k = false) :
    Integrable (fun z : RoundCoordinates p × RoundPrivateValues x =>
      discoveryIndicator x st t z.1 z.2) (currentSnapshotMeasure x t) := by
  by_cases hid : x.ids (x.privateId j) t = true
  · by_cases hchi : chi x t a = 1
    · rw [discoveryFunction_event_eq x st t j a hcal hmode hactive hheld htarget
        hinactive hid hchi]
      exact (integrable_const (1 : ℝ)).indicator
        (dataPeerAvoidEvent_measurable x t j a)
    · rw [discoveryFunction_zero x st t j a hcal hmode hactive hheld htarget
        hinactive (by simp [hid, hchi])]
      exact integrable_zero _ _ (currentSnapshotMeasure x t)
  · rw [discoveryFunction_zero x st t j a hcal hmode hactive hheld htarget
      hinactive (by simp [hid])]
    exact integrable_zero _ _ (currentSnapshotMeasure x t)

theorem multicastIndicator_integrable
    (x : BootstrapPhysicalBlock.Input p s) (st : BootstrapPhysicalBlock.State p)
    (t : Fin p.T) (j : {j // j ∈ x.uninformed}) (a : Arm p.K)
    (hcal : t ∈ BootstrapDimensions.calendarBlock p s)
    (hmem : x.privateId j ∈ st.list) (hcard : st.list.card ≤ L0 p)
    (hmode : st.mode = .multicast) (hactive : x.active j = true)
    (hheld : x.held j = a) (htarget : x.target = a)
    (hinactive : ∀ k : {k // k ∈ x.uninformed}, k ≠ j → x.active k = false) :
    Integrable (fun z : RoundCoordinates p × RoundPrivateValues x =>
      multicastIndicator x st t j z.1 z.2) (currentSnapshotMeasure x t) := by
  by_cases hid : x.ids (x.privateId j) t = false
  · by_cases hchi : chi x t a = 1
    · rw [multicastFunction_event_eq x st t j a hcal hmem hcard hmode hactive
        hheld htarget hinactive hid hchi]
      exact (integrable_const (1 : ℝ)).indicator
        (dataReleasePeerAvoidEvent_measurable x t j a st.list)
    · rw [multicastFunction_zero x st t j a hcal hmem hcard hmode hactive hheld
        htarget hinactive (by simp [hid, hchi])]
      exact integrable_zero _ _ (currentSnapshotMeasure x t)
  · rw [multicastFunction_zero x st t j a hcal hmem hcard hmode hactive hheld
      htarget hinactive (by simp [hid])]
    exact integrable_zero _ _ (currentSnapshotMeasure x t)

theorem discoveryIndicator_integral_eq
    (x : BootstrapPhysicalBlock.Input p s) (st : BootstrapPhysicalBlock.State p)
    (t : Fin p.T) (j : {j // j ∈ x.uninformed}) (a : Arm p.K)
    (hcal : t ∈ BootstrapDimensions.calendarBlock p s)
    (hmode : st.mode = .discover) (hactive : x.active j = true)
    (hheld : x.held j = a) (htarget : x.target = a)
    (hinactive : ∀ k : {k // k ∈ x.uninformed}, k ≠ j → x.active k = false) :
    (∫ z : RoundCoordinates p × RoundPrivateValues x,
      discoveryIndicator x st t z.1 z.2 ∂currentSnapshotMeasure x t) =
      (if x.ids (x.privateId j) t = true ∧ chi x t a = 1 then
        (1 / 2 : ℝ) * (1 - 1 / (p.K : ℝ)) ^ (p.m - 2) else 0) := by
  by_cases hflag : (x.ids (x.privateId j) t = true ∧ chi x t a = 1)
  · obtain ⟨hid, hchi⟩ := hflag
    have hfun := discoveryFunction_event_eq x st t j a hcal hmode hactive hheld
      htarget hinactive hid hchi
    rw [integral_congr_ae (Filter.Eventually.of_forall (fun z => congrFun hfun z))]
    rw [integral_indicator_const (1 : ℝ) (dataPeerAvoidEvent_measurable x t j a),
      smul_eq_mul, mul_one, ite_eq_left ⟨hid, hchi⟩]
    exact dataPeerAvoidEvent_mass x t j a
  · have hfun := discoveryFunction_zero x st t j a hcal hmode hactive hheld
      htarget hinactive hflag
    rw [integral_congr_ae (Filter.Eventually.of_forall (fun z => congrFun hfun z))]
    simp [hflag]

theorem multicastIndicator_integral_eq
    (x : BootstrapPhysicalBlock.Input p s) (st : BootstrapPhysicalBlock.State p)
    (t : Fin p.T) (j : {j // j ∈ x.uninformed}) (a : Arm p.K)
    (hcal : t ∈ BootstrapDimensions.calendarBlock p s)
    (hmem : x.privateId j ∈ st.list) (hcard : st.list.card ≤ L0 p)
    (hmode : st.mode = .multicast) (hactive : x.active j = true)
    (hheld : x.held j = a) (htarget : x.target = a)
    (hinactive : ∀ k : {k // k ∈ x.uninformed}, k ≠ j → x.active k = false) :
    (∫ z : RoundCoordinates p × RoundPrivateValues x,
      multicastIndicator x st t j z.1 z.2 ∂currentSnapshotMeasure x t) =
      (if x.ids (x.privateId j) t = false ∧ chi x t a = 1 then
        (1 / 2 : ℝ) * (1 - 1 / (L0 p : ℝ)) ^ st.list.card *
          (1 - 1 / (p.K : ℝ)) ^ (p.m - 2) else 0) := by
  by_cases hflag : (x.ids (x.privateId j) t = false ∧ chi x t a = 1)
  · obtain ⟨hid, hchi⟩ := hflag
    have hfun := multicastFunction_event_eq x st t j a hcal hmem hcard hmode hactive
      hheld htarget hinactive hid hchi
    rw [integral_congr_ae (Filter.Eventually.of_forall (fun z => congrFun hfun z))]
    rw [integral_indicator_const (1 : ℝ)
      (dataReleasePeerAvoidEvent_measurable x t j a st.list),
      smul_eq_mul, mul_one, ite_eq_left ⟨hid, hchi⟩]
    exact peerData_release_data_mass x t j a st.list
  · have hfun := multicastFunction_zero x st t j a hcal hmem hcard hmode hactive hheld
      htarget hinactive hflag
    rw [integral_congr_ae (Filter.Eventually.of_forall (fun z => congrFun hfun z))]
    simp [hflag]

theorem discoveryIndicator_mean_ge
    (x : BootstrapPhysicalBlock.Input p s) (st : BootstrapPhysicalBlock.State p)
    (t : Fin p.T) (j : {j // j ∈ x.uninformed}) (a : Arm p.K)
    (hcal : t ∈ BootstrapDimensions.calendarBlock p s)
    (hmode : st.mode = .discover) (hactive : x.active j = true)
    (hheld : x.held j = a) (htarget : x.target = a)
    (hinactive : ∀ k : {k // k ∈ x.uninformed}, k ≠ j → x.active k = false) :
    (∫ z : RoundCoordinates p × RoundPrivateValues x,
      discoveryIndicator x st t z.1 z.2 ∂currentSnapshotMeasure x t) ≥
      chi x t a / 8 * (if x.ids (x.privateId j) t = true then 1 else 0) := by
  rw [discoveryIndicator_integral_eq x st t j a hcal hmode hactive hheld htarget hinactive]
  by_cases hid : x.ids (x.privateId j) t = true
  · by_cases hchi : chi x t a = 1
    · have hp := BootstrapModeService.otherPlayerAvoidance_power p
      simp only [hid, hchi, and_self, ite_true, mul_one]
      calc
        (1 / 2 : ℝ) * (1 - 1 / (p.K : ℝ)) ^ (p.m - 2) ≥
            (1 / 2 : ℝ) * (1 / 4 : ℝ) :=
          mul_le_mul_of_nonneg_left hp (by norm_num)
        _ = 1 / 8 := by norm_num
    · have hchi0 := chi_eq_zero_of_ne_one x t a hchi
      simp [hid, hchi0]
  · simp [hid]

theorem multicastIndicator_mean_ge
    (x : BootstrapPhysicalBlock.Input p s) (st : BootstrapPhysicalBlock.State p)
    (t : Fin p.T) (j : {j // j ∈ x.uninformed}) (a : Arm p.K)
    (hcal : t ∈ BootstrapDimensions.calendarBlock p s)
    (hmem : x.privateId j ∈ st.list) (hcard : st.list.card ≤ L0 p)
    (hmode : st.mode = .multicast) (hactive : x.active j = true)
    (hheld : x.held j = a) (htarget : x.target = a)
    (hinactive : ∀ k : {k // k ∈ x.uninformed}, k ≠ j → x.active k = false) :
    (∫ z : RoundCoordinates p × RoundPrivateValues x,
      multicastIndicator x st t j z.1 z.2 ∂currentSnapshotMeasure x t) ≥
      chi x t a / 64 * (if x.ids (x.privateId j) t = false then 1 else 0) := by
  rw [multicastIndicator_integral_eq x st t j a hcal hmem hcard hmode hactive
    hheld htarget hinactive]
  by_cases hid : x.ids (x.privateId j) t = false
  · by_cases hchi : chi x t a = 1
    · have hrelease := BootstrapModeService.forwardRelease_ge_quarter p st.list hcard
      have havoid := BootstrapModeService.otherPlayerAvoidance_power p
      have havoidNonneg : 0 ≤ (1 - 1 / (p.K : ℝ)) ^ (p.m - 2) :=
        (by norm_num : (0 : ℝ) ≤ 1 / 4).trans havoid
      have hproduct : (1 / 2 : ℝ) *
          (1 - 1 / (L0 p : ℝ)) ^ st.list.card *
          (1 - 1 / (p.K : ℝ)) ^ (p.m - 2) ≥ 1 / 32 := by
        calc
          (1 / 2 : ℝ) * (1 - 1 / (L0 p : ℝ)) ^ st.list.card *
              (1 - 1 / (p.K : ℝ)) ^ (p.m - 2) =
            (1 / 2 : ℝ) * ((1 - 1 / (L0 p : ℝ)) ^ st.list.card *
              (1 - 1 / (p.K : ℝ)) ^ (p.m - 2)) := by ring
          _ ≥ (1 / 2 : ℝ) * ((1 / 4 : ℝ) *
              (1 - 1 / (p.K : ℝ)) ^ (p.m - 2)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hrelease havoidNonneg) (by norm_num)
          _ ≥ (1 / 2 : ℝ) * ((1 / 4 : ℝ) * (1 / 4 : ℝ)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left havoid (by norm_num)) (by norm_num)
          _ = 1 / 32 := by norm_num
      simp only [hid, hchi, and_self, ite_true, mul_one]
      exact le_trans (by norm_num : (1 / 64 : ℝ) ≤ 1 / 32) hproduct
    · have hchi0 := chi_eq_zero_of_ne_one x t a hchi
      simp [hid, hchi0]
  · simp [hid]

/-- The one-clock observable is measurable on the existing snapshot space. -/
theorem oneClock_measurable
    (x : BootstrapPhysicalBlock.Input p s) (st : BootstrapPhysicalBlock.State p)
    (t : Fin p.T) (j : {j // j ∈ x.uninformed}) (a : Arm p.K)
    (hcal : t ∈ BootstrapDimensions.calendarBlock p s)
    (hactive : x.active j = true) (hheld : x.held j = a) (htarget : x.target = a)
    (hinactive : ∀ k : {k // k ∈ x.uninformed}, k ≠ j → x.active k = false)
    (hmulticast : st.mode = .multicast →
      x.privateId j ∈ st.list ∧ st.list.card ≤ L0 p) :
    Measurable (fun z : RoundCoordinates p × RoundPrivateValues x =>
      oneClock x st t j z.1 z.2) := by
  cases hm : st.mode with
  | discover =>
      have hd := discoveryIndicator_measurable x st t j a hcal hm hactive hheld
        htarget hinactive
      simpa only [oneClock, multicastIndicator, hm, reduceCtorEq, false_and,
        ite_false, add_zero] using hd.div_const 8
  | multicast =>
      obtain ⟨hmem, hcard⟩ := hmulticast hm
      have hmult := multicastIndicator_measurable x st t j a hcal hmem hcard hm
        hactive hheld htarget hinactive
      simpa only [oneClock, discoveryIndicator, hm, reduceCtorEq, false_and,
        ite_false, zero_div, zero_add] using hmult

theorem oneClock_integrable
    (x : BootstrapPhysicalBlock.Input p s) (st : BootstrapPhysicalBlock.State p)
    (t : Fin p.T) (j : {j // j ∈ x.uninformed}) (a : Arm p.K)
    (hcal : t ∈ BootstrapDimensions.calendarBlock p s)
    (hactive : x.active j = true) (hheld : x.held j = a) (htarget : x.target = a)
    (hinactive : ∀ k : {k // k ∈ x.uninformed}, k ≠ j → x.active k = false)
    (hmulticast : st.mode = .multicast →
      x.privateId j ∈ st.list ∧ st.list.card ≤ L0 p) :
    Integrable (fun z : RoundCoordinates p × RoundPrivateValues x =>
      oneClock x st t j z.1 z.2) (currentSnapshotMeasure x t) := by
  cases hm : st.mode with
  | discover =>
      have hd := discoveryIndicator_integrable x st t j a hcal hm hactive hheld
        htarget hinactive
      have hfun : (fun z : RoundCoordinates p × RoundPrivateValues x =>
          oneClock x st t j z.1 z.2) = fun z => discoveryIndicator x st t z.1 z.2 / 8 := by
        funext z
        simp [oneClock, multicastIndicator, hm]
      rw [hfun]
      exact hd.div_const 8
  | multicast =>
      obtain ⟨hmem, hcard⟩ := hmulticast hm
      have hm' : st.mode = BootstrapPhysicalBlock.Mode.multicast := hm
      have hmult := multicastIndicator_integrable x st t j a hcal hmem hcard hm'
        hactive hheld htarget hinactive
      have hfun : (fun z : RoundCoordinates p × RoundPrivateValues x =>
          oneClock x st t j z.1 z.2) = fun z => multicastIndicator x st t j z.1 z.2 := by
        funext z
        simp [oneClock, discoveryIndicator, hm']
      rw [hfun]
      exact hmult

theorem oneClock_integral_mean_ge
    (x : BootstrapPhysicalBlock.Input p s) (st : BootstrapPhysicalBlock.State p)
    (t : Fin p.T) (j : {j // j ∈ x.uninformed}) (a : Arm p.K)
    (hcal : t ∈ BootstrapDimensions.calendarBlock p s)
    (hactive : x.active j = true) (hheld : x.held j = a) (htarget : x.target = a)
    (hinactive : ∀ k : {k // k ∈ x.uninformed}, k ≠ j → x.active k = false)
    (hmulticast : st.mode = .multicast →
      x.privateId j ∈ st.list ∧ st.list.card ≤ L0 p) :
    (∫ z : RoundCoordinates p × RoundPrivateValues x,
      oneClock x st t j z.1 z.2 ∂currentSnapshotMeasure x t) ≥
      chi x t a / 64 *
        ((if st.mode = .discover ∧ x.ids (x.privateId j) t = true then 1 else 0) +
         (if st.mode = .multicast ∧ x.ids (x.privateId j) t = false then 1 else 0)) := by
  cases hm : st.mode with
  | discover =>
      have hbound := discoveryIndicator_mean_ge x st t j a hcal hm hactive hheld
        htarget hinactive
      have hfun : (fun z : RoundCoordinates p × RoundPrivateValues x =>
          oneClock x st t j z.1 z.2) = fun z => discoveryIndicator x st t z.1 z.2 / 8 := by
        funext z
        simp [oneClock, multicastIndicator, hm]
      rw [integral_congr_ae (Filter.Eventually.of_forall (fun z => congrFun hfun z)),
        integral_div]
      have hscaled := div_le_div_of_nonneg_right hbound (by norm_num : (0 : ℝ) ≤ 8)
      have hresult :
          (∫ z : RoundCoordinates p × RoundPrivateValues x,
            discoveryIndicator x st t z.1 z.2 ∂currentSnapshotMeasure x t) / 8 ≥
          chi x t a / 64 * (if x.ids (x.privateId j) t = true then 1 else 0) := by
        calc
          _ ≥ (chi x t a / 8 *
              (if x.ids (x.privateId j) t = true then 1 else 0)) / 8 := hscaled
          _ = _ := by ring
      simpa only [hm, reduceCtorEq, true_and, false_and, ite_false, add_zero] using hresult
  | multicast =>
      obtain ⟨hmem, hcard⟩ := hmulticast hm
      have hm' : st.mode = BootstrapPhysicalBlock.Mode.multicast := hm
      have hmMean := multicastIndicator_mean_ge x st t j a hcal hmem hcard hm'
        hactive hheld htarget hinactive
      have hfun : (fun z : RoundCoordinates p × RoundPrivateValues x =>
          oneClock x st t j z.1 z.2) = fun z => multicastIndicator x st t j z.1 z.2 := by
        funext z
        simp [oneClock, discoveryIndicator, hm']
      rw [integral_congr_ae (Filter.Eventually.of_forall (fun z => congrFun hfun z))]
      simpa [hm'] using hmMean

end Bandits.Support.BootstrapModeMeans

end
