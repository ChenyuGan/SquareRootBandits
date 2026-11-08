/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.BootstrapPrivateIDFibers
public import Bandits.Support.GeneratedBlockDrawLaw
public import Bandits.Support.ReferenceInitializationPrefixInvariance
public import Bandits.Support.ReferenceInitializationMeasurability

/-!
# Private ID fibres after generated peer paths

Internal fixed-numerical-public-output results for every generated reference
prelaunch block, including a shortened final block. The retained coordinates
are exactly `BootstrapPrivateIDFibers.Complement`: only the focal current ID
scalar and the coordinator/focal current-block round sequences are removed.

Sources: `sources/zip4/manuscript/appendix_b_communication.tex:298-338,94-131`
and `sources/zip4/manuscript/07_public_setup.tex:123-164`. The conditional
execution argument at Appendix B 302-314 is the scope of this module. No
public future-row law, numerical failure bound, coupling, or manuscript
closure is asserted.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions Bandits.Support.BootstrapDimensions
open Bandits.Support.CompletePublicTable Bandits.Support.ActiveRoundActions
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.BootstrapPrivateIDFibers
open Bandits.Support.ReferenceInitializationRun
open scoped ENNReal Classical

namespace Bandits.Support.GeneratedPrivateIDFibers

variable (p : Parameters) (s : Fin (n_boot p))
  (j : Fin (p.m - 1)) (hj : j.val + 1 < p.m)

/-- Prior calendar rounds cannot belong to the removed current block. -/
theorem not_mem_currentBlock_of_prior (t : Fin p.T)
    (ht : t.val < elapsed p s.val) : t ∉ calendarBlock p s := by
  intro hm
  have hl := ((mem_calendarBlock_iff p s t).mp hm).1
  have he : elapsed p s.val ≤ s.val * B_boot p := Nat.min_le_right _ _
  omega

/-- Literal prior input agreement from equality of the accepted retained
coordinates. Current activity and held scalars remain visible in W. -/
theorem runPrefixInputEq_of_same_W
    (P : PublishedOutput p) (J : Fin (M p))
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (rho tau : ExtendedPrivateCoordinates p)
    (hw : (splitEquiv p s j hj rho).1 = (splitEquiv p s j hj tau).1) :
    ReferenceInitializationCausality.runPrefixInputEq
      (initialRunInput p P J rewards C_star C_h eta rho)
      (initialRunInput p P J rewards C_star C_h eta tau) s.val := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · intro t ht
    exact ⟨fun _ => rfl, rfl⟩
  · intro r hr k
    have hne : r ≠ s := fun he => by subst r; omega
    have h := congrArg (fun w : Complement p s j ⟨j.val + 1, hj⟩ =>
      w.1.2.2 ⟨r, hne⟩ k) hw
    simpa only [initialRunInput, split_otherBlock_triple] using h
  · intro r hr
    have h := congrArg (fun w : Complement p s j ⟨j.val + 1, hj⟩ => w.2.2.2 r) hw
    simpa only [initialRunInput, split_target_scalars] using h
  · intro i t ht
    have hnot := not_mem_currentBlock_of_prior p s t ht
    let q : OtherRoundLabels p s ⟨j.val + 1, hj⟩ :=
      ⟨(i, t), fun h => h.elim (fun hc => hnot hc.2) (fun hf => hnot hf.2)⟩
    have h := congrArg (fun w : Complement p s j ⟨j.val + 1, hj⟩ => w.2.2.1 q) hw
    simpa only [initialRunInput, split_otherRound_scalar] using h

/-- The full generated boundary is invariant under all three removed groups,
proved from prior original coordinates, including stopped branches. -/
theorem generatedBoundary_eq_of_same_W
    (P : PublishedOutput p) (J : Fin (M p))
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate)
    (rho tau : ExtendedPrivateCoordinates p)
    (hw : (splitEquiv p s j hj rho).1 = (splitEquiv p s j hj tau).1) :
    GeneratedBlockDrawLaw.generatedBoundary p s P.1 (P.2 J) rewards C_star C_h eta rho =
      GeneratedBlockDrawLaw.generatedBoundary p s P.1 (P.2 J) rewards C_star C_h eta tau :=
  ReferenceInitializationPrefixInvariance.run_eq_of_runPrefixInputEq _ _ s.val
    (runPrefixInputEq_of_same_W p s j hj P J rewards C_star C_h eta rho tau hw)

/-- A section of the exact split, used only to evaluate proved invariants.
It introduces no physical reset or replacement randomness. -/
def completeW (w : Complement p s j ⟨j.val + 1, hj⟩) : ExtendedPrivateCoordinates p :=
  (splitEquiv p s j hj).symm
    (w, GeneratedBlockDrawLaw.zeroScalar,
      (fun _ => GeneratedBlockDrawLaw.zeroScalar),
      (fun _ => GeneratedBlockDrawLaw.zeroScalar))

theorem split_completeW (w : Complement p s j ⟨j.val + 1, hj⟩) :
    (splitEquiv p s j hj (completeW p s j hj w)).1 = w :=
  congrArg Prod.fst ((splitEquiv p s j hj).apply_symm_apply _)

theorem measurable_completeW : Measurable (completeW p s j hj) :=
  (splitEquiv p s j hj).symm.measurable.comp
    (measurable_id.prodMk measurable_const)

variable (P : PublishedOutput p) (J : Fin (M p))
  (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
  (eta : ReferencePrelaunchFollower.LearningRate)

/-- W representation of the actual boundary, justified by fibre invariance. -/
def boundaryFromW (w : Complement p s j ⟨j.val + 1, hj⟩) : Boundary p :=
  GeneratedBlockDrawLaw.generatedBoundary p s P.1 (P.2 J) rewards C_star C_h eta
    (completeW p s j hj w)

theorem generatedBoundary_eq_boundaryFromW (rho : ExtendedPrivateCoordinates p) :
    GeneratedBlockDrawLaw.generatedBoundary p s P.1 (P.2 J) rewards C_star C_h eta rho =
      boundaryFromW p s j hj P J rewards C_star C_h eta (splitEquiv p s j hj rho).1 := by
  apply generatedBoundary_eq_of_same_W p s j hj P J rewards C_star C_h eta
  rw [split_completeW]

theorem measurable_boundaryFromW :
    Measurable (boundaryFromW p s j hj P J rewards C_star C_h eta) :=
  (GeneratedBlockDrawLaw.measurable_generatedBoundary p s P.1 (P.2 J)
    rewards C_star C_h eta).comp (measurable_completeW p s j hj)

/-- A non-stopped opportunity really processes s, by actual run progress. -/
theorem generatedBoundary_processed (rho : ExtendedPrivateCoordinates p)
    (hn : (GeneratedBlockDrawLaw.generatedBoundary p s P.1 (P.2 J)
      rewards C_star C_h eta rho).crossing = none) :
    let b := GeneratedBlockDrawLaw.generatedBoundary p s P.1 (P.2 J)
      rewards C_star C_h eta rho
    b.completed = s.val ∧ ∃ h : b.completed < n_boot p,
      nextBlock b h = s ∧
      run (initialRunInput p P J rewards C_star C_h eta rho) (s.val + 1) =
        finishBlock (initialRunInput p P J rewards C_star C_h eta rho) b h := by
  dsimp only
  let x := initialRunInput p P J rewards C_star C_h eta rho
  let b := run x s.val
  have hc : b.crossing = none := hn
  have he : b.completed = s.val :=
    (run_progress x s.val s.isLt.le).resolve_left (by rw [hc]; exact Bool.false_ne_true)
  have h : b.completed < n_boot p := by rw [he]; exact s.isLt
  refine ⟨he, h, Fin.ext he, ?_⟩
  rw [run_succ]
  exact advance_of_no_crossing x b hc h

/-- The observation-free uninformed arm rule, on its own genuine draws. -/
def privateArm (ids : IDArray p) (t : Fin p.T)
    (d : PrivateSourceStreams.BlockDraw p) (v : BootstrapPrivateIDFibers.Scalar) : Fin p.K :=
  if d.1 then
    if ids d.2.2 t then (forbiddenArmScalarDraw p d.2.1 v).val else d.2.1
  else fullArmScalarDraw p v

theorem measurable_privateArm (ids : IDArray p) (t : Fin p.T)
    (d : PrivateSourceStreams.BlockDraw p) : Measurable (privateArm p ids t d) := by
  unfold privateArm
  split_ifs
  · exact measurable_subtype_coe.comp (measurable_forbiddenArmScalarDraw p d.2.1)
  · exact measurable_const
  · exact measurable_fullArmScalarDraw p

/-- Informed peers use exactly pilots, tuple arms, and the initial UP word.
This literal arm formula has no observations or pending declarations. -/
def informedArm (row : CompleteRow p) (t : Fin p.T) (k : Follower p.m) : Fin p.K :=
  let draws := (row.2 t).1
  let tuple := OrderedTupleSampler.sample p.two_le_m p.m_lt_K draws
  if PublicDiscreteDraws.slotDraw draws = PublicDiscreteDraws.dataSlot then
    PublicDiscreteDraws.pilotDraw (K_pos p) (PublicDiscreteDraws.followerPlayer p.two_le_m k) draws
  else if PublicDiscreteDraws.slotDraw draws = PublicDiscreteDraws.upSlot ∧
      PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K draws = k then
    sendArm (((row.2 t).2 (1, k)).2)
      (tuple.val (PublicDiscreteDraws.followerPlayer p.two_le_m k))
      (tuple.val (coordinator p.two_le_m))
  else tuple.val (PublicDiscreteDraws.followerPlayer p.two_le_m k)

/-- Entire peer path on W. Each uninformed peer uses its OWN retained triple
and OWN retained round scalar; informed peers use the fixed selected row. -/
def peerArmFromW (b : Boundary p) (w : Complement p s j ⟨j.val + 1, hj⟩)
    (t : BlockTime p s) (k : {k : Fin (p.m - 1) // k ≠ j}) : Fin p.K :=
  if sourceFollower p k.1 ∈ uninformed b then
    privateArm p P.1 t.1
      (PrivateSourceStreams.privateBlockDrawMap p (b.numerators k.1)
        (b.weight_ge_one k.1) (w.1.2.1 k))
      (w.2.2.1 (peerRoundLabel p s j hj k t))
  else informedArm p (P.2 J) t.1 (sourceFollower p k.1)

theorem measurable_peerArmFromW (b : Boundary p)
    (t : BlockTime p s) (k : {k : Fin (p.m - 1) // k ≠ j}) :
    Measurable (fun w => peerArmFromW p s j hj P J b w t k) := by
  classical
  unfold peerArmFromW
  split_ifs
  · have hd : Measurable (fun w : Complement p s j ⟨j.val + 1, hj⟩ =>
        PrivateSourceStreams.privateBlockDrawMap p (b.numerators k.1)
          (b.weight_ge_one k.1) (w.1.2.1 k)) :=
      (PrivateSourceStreams.measurable_privateBlockDrawMap p _ _).comp
        ((measurable_pi_apply k).comp
          (measurable_fst.comp (measurable_snd.comp measurable_fst)))
    have hv : Measurable (fun w : Complement p s j ⟨j.val + 1, hj⟩ =>
        w.2.2.1 (peerRoundLabel p s j hj k t)) :=
      (measurable_pi_apply _).comp
        (measurable_fst.comp (measurable_snd.comp measurable_snd))
    exact (measurable_from_prod_countable_right
      (f := fun q : PrivateSourceStreams.BlockDraw p × BootstrapPrivateIDFibers.Scalar =>
        privateArm p P.1 t.1 q.1 q.2)
      (fun d => measurable_privateArm p P.1 t.1 d)).comp (hd.prodMk hv)
  · exact measurable_const

/-- All of a peer's physical actions in the calendar block factor through W,
including active peers and initially informed peers. The physical recursion's
state disappears by `actions_follower`, not by an independence assumption. -/
theorem physical_peerAction_eq_fromW (rho : ExtendedPrivateCoordinates p)
    (b : Boundary p) (h : b.completed < n_boot p) (hs : nextBlock b h = s)
    (t : BlockTime p s) (k : {k : Fin (p.m - 1) // k ≠ j}) :
    BootstrapPhysicalBlock.actions
      (physical (initialRunInput p P J rewards C_star C_h eta rho) b h)
      (BootstrapPhysicalBlock.run
        (physical (initialRunInput p P J rewards C_star C_h eta rho) b h) t.1.val)
      t.1 (PublicDiscreteDraws.followerPlayer p.two_le_m (sourceFollower p k.1)) =
      peerArmFromW p s j hj P J b (splitEquiv p s j hj rho).1 t k := by
  let x := initialRunInput p P J rewards C_star C_h eta rho
  let v := physical x b h
  have htriple : (splitEquiv p s j hj rho).1.1.2.1 k = rho.1.1 s k.1 := by
    rw [split_wBase_eq_followerSplit]
    exact followerSplit_other_triple p s j rho.1.1 k.1 k.2
  have hround := split_otherRound_scalar p s j hj rho (peerRoundLabel p s j hj k t)
  have hr : (splitEquiv p s j hj rho).1.2.2.1 (peerRoundLabel p s j hj k t) =
      rho.2.1 (PublicDiscreteDraws.followerPlayer p.two_le_m (sourceFollower p k.1), t.1) :=
    hround
  change BootstrapPhysicalBlock.actions v (BootstrapPhysicalBlock.run v t.1.val)
    t.1 (PublicDiscreteDraws.followerPlayer p.two_le_m (sourceFollower p k.1)) = _
  rw [BootstrapPhysicalBlock.actions_follower]
  by_cases hk : sourceFollower p k.1 ∈ uninformed b
  · have hm : sourceFollower p k.1 ∈ v.uninformed := hk
    rw [BootstrapPhysicalBlock.followerAction, dite_eq_left hm]
    change privateArm p P.1 t.1
      (PrivateSourceStreams.privateBlockDrawMap p (b.numerators k.1)
        (b.weight_ge_one k.1) (rho.1.1 (nextBlock b h) k.1))
      (rho.2.1 (PublicDiscreteDraws.followerPlayer p.two_le_m (sourceFollower p k.1), t.1)) = _
    rw [hs]
    simp only [peerArmFromW, ite_eq_left hk, htriple, hr]
  · have hm : sourceFollower p k.1 ∉ v.uninformed := hk
    rw [BootstrapPhysicalBlock.followerAction, dite_eq_right hm]
    rw [peerArmFromW, ite_eq_right hk]
    unfold BootstrapPhysicalBlock.unoccupiedAction
    rw [BootstrapPhysicalBlock.initialUpBit_eq_offset]
    rfl

/-- The full generated peer vector, with its incoming status obtained from
the actual W-boundary. No coordinator or focal action is part of this vector. -/
def generatedPeerPathFromW (w : Complement p s j ⟨j.val + 1, hj⟩) :
    BlockTime p s → {k : Fin (p.m - 1) // k ≠ j} → Fin p.K :=
  peerArmFromW p s j hj P J
    (boundaryFromW p s j hj P J rewards C_star C_h eta w) w

/-- Countable incoming-boundary decomposition for a retained-coordinate map. -/
theorem measurable_peerArmFromW_boundary
    (B : Complement p s j ⟨j.val + 1, hj⟩ → Boundary p) (hB : Measurable B)
    (t : BlockTime p s) (k : {k : Fin (p.m - 1) // k ≠ j}) :
    Measurable (fun w => peerArmFromW p s j hj P J (B w) w t k) := by
  apply measurable_to_countable'
  intro c
  change MeasurableSet {w | peerArmFromW p s j hj P J (B w) w t k = c}
  have he : {w | peerArmFromW p s j hj P J (B w) w t k = c} =
      ⋃ b : Boundary p, {w | B w = b} ∩
        {w | peerArmFromW p s j hj P J b w t k = c} := by
    ext w
    constructor
    · intro hw
      exact Set.mem_iUnion.mpr ⟨B w, rfl, hw⟩
    · intro hw
      rcases Set.mem_iUnion.mp hw with ⟨b, hb, hc⟩
      change peerArmFromW p s j hj P J (B w) w t k = c
      rw [hb]
      exact hc
  rw [he]
  exact MeasurableSet.iUnion fun b =>
    ((measurableSet_singleton b).preimage hB).inter
      ((measurableSet_singleton c).preimage
        (measurable_peerArmFromW p s j hj P J b t k))

theorem measurable_generatedPeerArmFromW
    (t : BlockTime p s) (k : {k : Fin (p.m - 1) // k ≠ j}) :
    Measurable (fun w : Complement p s j ⟨j.val + 1, hj⟩ =>
      peerArmFromW p s j hj P J
        (boundaryFromW p s j hj P J rewards C_star C_h eta w) w t k) :=
  measurable_peerArmFromW_boundary p s j hj P J
    (boundaryFromW p s j hj P J rewards C_star C_h eta)
    (measurable_boundaryFromW p s j hj P J rewards C_star C_h eta) t k

theorem measurable_generatedPeerPathFromW :
    Measurable (generatedPeerPathFromW p s j hj P J rewards C_star C_h eta) :=
  Measurable.of_eval fun t => Measurable.of_eval fun k =>
    measurable_generatedPeerArmFromW p s j hj P J rewards C_star C_h eta t k

/-- Equality of ENTIRE physical peer vectors at a generated processed block. -/
theorem generated_peer_path_factor (rho : ExtendedPrivateCoordinates p)
    (b : Boundary p) (h : b.completed < n_boot p)
    (hb : GeneratedBlockDrawLaw.generatedBoundary p s P.1 (P.2 J)
      rewards C_star C_h eta rho = b) (hc : b.completed = s.val)
    (hn : b.crossing = none) :
    run (initialRunInput p P J rewards C_star C_h eta rho) (s.val + 1) =
      finishBlock (initialRunInput p P J rewards C_star C_h eta rho) b h ∧
    (fun (t : BlockTime p s) (k : {k : Fin (p.m - 1) // k ≠ j}) =>
      BootstrapPhysicalBlock.actions
        (physical (initialRunInput p P J rewards C_star C_h eta rho) b h)
        (BootstrapPhysicalBlock.run
          (physical (initialRunInput p P J rewards C_star C_h eta rho) b h) t.1.val)
        t.1 (PublicDiscreteDraws.followerPlayer p.two_le_m (sourceFollower p k.1))) =
      generatedPeerPathFromW p s j hj P J rewards C_star C_h eta
        (splitEquiv p s j hj rho).1 := by
  have hw : boundaryFromW p s j hj P J rewards C_star C_h eta
      (splitEquiv p s j hj rho).1 = b :=
    (generatedBoundary_eq_boundaryFromW p s j hj P J rewards C_star C_h eta rho).symm.trans hb
  constructor
  · have hd := GeneratedBlockDrawLaw.actualProcessedBlock_draw_fields p s P.1 (P.2 J)
      rewards C_star C_h eta rho b hb hc hn
    exact hd.1
  · funext t k
    rw [generatedPeerPathFromW, hw]
    exact physical_peerAction_eq_fromW p s j hj P J rewards C_star C_h eta rho b h
      (Fin.ext hc) t k

/-- The actual focal physical fields use the retained activity/held scalars
and the removed ORIGINAL ID scalar, with the actual incoming weights. -/
theorem physical_focal_fields (rho : ExtendedPrivateCoordinates p)
    (b : Boundary p) (h : b.completed < n_boot p) (hc : b.completed = s.val)
    (hf : sourceFollower p j ∈ uninformed b) :
    let v := physical (initialRunInput p P J rewards C_star C_h eta rho) b h
    (v.active ⟨sourceFollower p j, hf⟩, v.held ⟨sourceFollower p j, hf⟩,
      v.privateId ⟨sourceFollower p j, hf⟩) =
      (PrivateSourceStreams.activityScalarDraw p (splitEquiv p s j hj rho).1.1.1.1,
        PrivateSourceStreams.heldArmScalarDraw p (b.numerators j) (b.weight_ge_one j)
          (splitEquiv p s j hj rho).1.1.1.2,
        PrivateSourceStreams.privateIDScalarDraw p (splitEquiv p s j hj rho).2.1) := by
  change (PrivateSourceStreams.activityScalarDraw p (rho.1.1 (nextBlock b h) j).1,
    PrivateSourceStreams.heldArmScalarDraw p (b.numerators j) (b.weight_ge_one j)
      (rho.1.1 (nextBlock b h) j).2.1,
    PrivateSourceStreams.privateIDScalarDraw p (rho.1.1 (nextBlock b h) j).2.2) = _
  rw [show nextBlock b h = s from Fin.ext hc,
    split_activity_scalar, split_held_scalar, split_id_scalar]

theorem physical_target_fromW (rho : ExtendedPrivateCoordinates p)
    (b : Boundary p) (h : b.completed < n_boot p) (hc : b.completed = s.val) :
    (physical (initialRunInput p P J rewards C_star C_h eta rho) b h).target =
      coordinatorTargetDraw p ((splitEquiv p s j hj rho).1.2.2.2 s) := by
  change coordinatorTargetDraw p (rho.2.2 (nextBlock b h)) = _
  rw [show nextBlock b h = s from Fin.ext hc, split_target_scalar]

variable (a z : Fin p.K)
  (peer : BlockTime p s → {k : Fin (p.m - 1) // k ≠ j} → Fin p.K)

/-- The numerical W-side conditions at one incoming boundary. Processing,
noncrossing, and focal incoming status are literal guards. -/
def blockWCondition (b : Boundary p) : Set (Complement p s j ⟨j.val + 1, hj⟩) :=
  {w | b.completed = s.val ∧ b.crossing = none ∧ sourceFollower p j ∈ uninformed b ∧
    PrivateSourceStreams.activityScalarDraw p w.1.1.1 = true ∧
    PrivateSourceStreams.heldArmScalarDraw p (b.numerators j) (b.weight_ge_one j) w.1.1.2 = a ∧
    coordinatorTargetDraw p (w.2.2.2 s) = z ∧
    ∀ t k, peerArmFromW p s j hj P J b w t k = peer t k}

theorem measurableSet_blockWCondition (b : Boundary p) :
    MeasurableSet (blockWCondition p s j hj P J a z peer b) := by
  have ha : Measurable (fun w : Complement p s j ⟨j.val + 1, hj⟩ =>
      PrivateSourceStreams.activityScalarDraw p w.1.1.1) :=
    (PrivateSourceStreams.activityScalarDraw_measurable p).comp
      (measurable_fst.comp (measurable_fst.comp measurable_fst))
  have hh : Measurable (fun w : Complement p s j ⟨j.val + 1, hj⟩ =>
      PrivateSourceStreams.heldArmScalarDraw p (b.numerators j) (b.weight_ge_one j) w.1.1.2) :=
    (PrivateSourceStreams.measurable_heldArmScalarDraw p _ _).comp
      (measurable_snd.comp (measurable_fst.comp measurable_fst))
  have hz : Measurable (fun w : Complement p s j ⟨j.val + 1, hj⟩ =>
      coordinatorTargetDraw p (w.2.2.2 s)) :=
    (measurable_fullArmScalarDraw p).comp
      ((measurable_pi_apply s).comp
        (measurable_snd.comp (measurable_snd.comp measurable_snd)))
  have hp : MeasurableSet {w | ∀ t k, peerArmFromW p s j hj P J b w t k = peer t k} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun t => MeasurableSet.iInter fun k =>
      (measurableSet_singleton (peer t k)).preimage
        (measurable_peerArmFromW p s j hj P J b t k)
  exact (MeasurableSet.const _).inter ((MeasurableSet.const _).inter
    ((MeasurableSet.const _).inter (((measurableSet_singleton true).preimage ha).inter
      (((measurableSet_singleton a).preimage hh).inter
        (((measurableSet_singleton z).preimage hz).inter hp)))))

/-- The physical conditions: actual active/held/target fields and every peer's
full generated arm path. No observations or other players' activity are assumed. -/
def physicalCondition (rho : ExtendedPrivateCoordinates p) (b : Boundary p)
    (h : b.completed < n_boot p) (hf : sourceFollower p j ∈ uninformed b) : Prop :=
  let v := physical (initialRunInput p P J rewards C_star C_h eta rho) b h
  v.active ⟨sourceFollower p j, hf⟩ = true ∧
    v.held ⟨sourceFollower p j, hf⟩ = a ∧ v.target = z ∧
    ∀ t k, BootstrapPhysicalBlock.actions v (BootstrapPhysicalBlock.run v t.1.val)
      t.1 (PublicDiscreteDraws.followerPlayer p.two_le_m (sourceFollower p k.1)) = peer t k

/-- Every physical condition is derived from the literal W rules. -/
theorem physicalCondition_iff_blockWCondition (rho : ExtendedPrivateCoordinates p)
    (b : Boundary p) (h : b.completed < n_boot p) (hc : b.completed = s.val)
    (hn : b.crossing = none) (hf : sourceFollower p j ∈ uninformed b) :
    physicalCondition p s j P J rewards C_star C_h eta a z peer rho b h hf ↔
      (splitEquiv p s j hj rho).1 ∈ blockWCondition p s j hj P J a z peer b := by
  have hd := physical_focal_fields p s j hj P J rewards C_star C_h eta rho b h hc hf
  have ha := congrArg Prod.fst hd
  have hh := congrArg (fun d => d.2.1) hd
  dsimp only [Prod.fst, Prod.snd] at ha hh
  have hz := physical_target_fromW p s j hj P J rewards C_star C_h eta rho b h hc
  have hs : nextBlock b h = s := Fin.ext hc
  have hp := physical_peerAction_eq_fromW p s j hj P J rewards C_star C_h eta rho b h hs
  simp only [physicalCondition, blockWCondition, Set.mem_ofPred_eq, hc, hn, hf,
    true_and, ha, hh, hz, hp]

variable (H : Set (Complement p s j ⟨j.val + 1, hj⟩))

/-- Optional measurable W-history may include any actual boundary atom. -/
def generatedWEvent : Set (Complement p s j ⟨j.val + 1, hj⟩) :=
  {w | w ∈ H ∧ ∃ b, boundaryFromW p s j hj P J rewards C_star C_h eta w = b ∧
    w ∈ blockWCondition p s j hj P J a z peer b}

theorem measurableSet_generatedWEvent (hH : MeasurableSet H) :
    MeasurableSet (generatedWEvent p s j hj P J rewards C_star C_h eta a z peer H) := by
  have he : generatedWEvent p s j hj P J rewards C_star C_h eta a z peer H =
      H ∩ ⋃ b : Boundary p,
        {w | boundaryFromW p s j hj P J rewards C_star C_h eta w = b} ∩
          blockWCondition p s j hj P J a z peer b := by
    ext w
    simp only [generatedWEvent, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iUnion]
  rw [he]
  exact hH.inter (MeasurableSet.iUnion fun b =>
    ((measurableSet_singleton b).preimage
      (measurable_boundaryFromW p s j hj P J rewards C_star C_h eta)).inter
        (measurableSet_blockWCondition p s j hj P J a z peer b))

/-- ACTUAL generated event. A physical input is used only with a genuine
remaining-block proof, actual generated-boundary equality, and no crossing.
Stopped/exhausted opportunities have no witness and no physical trace. -/
def generatedActualEvent : Set (ExtendedPrivateCoordinates p) :=
  {rho | (splitEquiv p s j hj rho).1 ∈ H ∧
    ∃ (b : Boundary p) (h : b.completed < n_boot p)
      (hf : sourceFollower p j ∈ uninformed b),
      GeneratedBlockDrawLaw.generatedBoundary p s P.1 (P.2 J)
        rewards C_star C_h eta rho = b ∧ b.completed = s.val ∧ b.crossing = none ∧
      physicalCondition p s j P J rewards C_star C_h eta a z peer rho b h hf}

/-- Exact W-cylinder identity for every real generated block. -/
theorem generatedActualEvent_eq_splitCylinder :
    generatedActualEvent p s j hj P J rewards C_star C_h eta a z peer H =
      (fun rho => (splitEquiv p s j hj rho).1) ⁻¹'
        generatedWEvent p s j hj P J rewards C_star C_h eta a z peer H := by
  ext rho
  change (_ ∧ _) ↔ (_ ∧ _)
  constructor
  · rintro ⟨hH, b, h, hf, hb, hc, hn, hp⟩
    refine ⟨hH, b, ?_, ?_⟩
    · exact (generatedBoundary_eq_boundaryFromW p s j hj P J rewards C_star C_h eta rho).symm.trans hb
    · exact (physicalCondition_iff_blockWCondition p s j hj P J rewards C_star C_h eta
        a z peer rho b h hc hn hf).mp hp
  · rintro ⟨hH, b, hb, hc, hn, hf, ha, hh, hz, hp⟩
    have h : b.completed < n_boot p := by rw [hc]; exact s.isLt
    refine ⟨hH, b, h, hf, ?_, hc, hn, ?_⟩
    · exact (generatedBoundary_eq_boundaryFromW p s j hj P J rewards C_star C_h eta rho).trans hb
    · exact (physicalCondition_iff_blockWCondition p s j hj P J rewards C_star C_h eta
        a z peer rho b h hc hn hf).mpr ⟨hc, hn, hf, ha, hh, hz, hp⟩

theorem measurableSet_generatedActualEvent (hH : MeasurableSet H) :
    MeasurableSet (generatedActualEvent p s j hj P J rewards C_star C_h eta a z peer H) := by
  rw [generatedActualEvent_eq_splitCylinder]
  exact (measurableSet_generatedWEvent p s j hj P J rewards C_star C_h eta a z peer H hH).preimage
    (measurable_fst.comp (splitEquiv p s j hj).measurable)

/-- Actual event mass, with no positivity assumption or atom normalization. -/
theorem generatedActualEvent_measure (hH : MeasurableSet H) :
    extendedPrivateLaw p
      (generatedActualEvent p s j hj P J rewards C_star C_h eta a z peer H) =
      complementLaw p s j ⟨j.val + 1, hj⟩
        (generatedWEvent p s j hj P J rewards C_star C_h eta a z peer H) := by
  rw [generatedActualEvent_eq_splitCylinder]
  exact (measurePreserving_fst.comp (split_measurePreserving p s j hj)).measure_preimage
    (measurableSet_generatedWEvent p s j hj P J rewards C_star C_h eta a z peer H hH).nullMeasurableSet

/-- The fibre law before replacing the raw ID draw by its proved physical field. -/
theorem generatedActual_cylinder_measure
    (D : Set ((BlockTime p s → BootstrapPrivateIDFibers.Scalar) ×
      (BlockTime p s → BootstrapPrivateIDFibers.Scalar)))
    (u : Fin (A_id p)) (hH : MeasurableSet H) (hD : MeasurableSet D) :
    extendedPrivateLaw p
      {rho | rho ∈ generatedActualEvent p s j hj P J rewards C_star C_h eta a z peer H ∧
        PrivateSourceStreams.privateIDScalarDraw p (splitEquiv p s j hj rho).2.1 = u ∧
        (splitEquiv p s j hj rho).2.2 ∈ D} =
      extendedPrivateLaw p
        (generatedActualEvent p s j hj P J rewards C_star C_h eta a z peer H) *
        ENNReal.ofReal (1 / (A_id p : ℝ)) * roundPairLaw p s D := by
  rw [generatedActualEvent_measure p s j hj P J rewards C_star C_h eta a z peer H hH,
    generatedActualEvent_eq_splitCylinder]
  exact split_cylinder_measure p s j hj
    (generatedWEvent p s j hj P J rewards C_star C_h eta a z peer H) D u
    (measurableSet_generatedWEvent p s j hj P J rewards C_star C_h eta a z peer H hH) hD

/-- Partial physical ID field as an event, with no value assigned when there
is no processed incoming focal block. The witness uses the actual producer. -/
def actualPrivateIDEvent (u : Fin (A_id p)) : Set (ExtendedPrivateCoordinates p) :=
  {rho | ∃ (b : Boundary p) (h : b.completed < n_boot p)
      (hf : sourceFollower p j ∈ uninformed b),
      GeneratedBlockDrawLaw.generatedBoundary p s P.1 (P.2 J)
        rewards C_star C_h eta rho = b ∧ b.completed = s.val ∧ b.crossing = none ∧
      (physical (initialRunInput p P J rewards C_star C_h eta rho) b h).privateId
        ⟨sourceFollower p j, hf⟩ = u}

/-- On E the genuine physical ID event is exactly the original scalar fibre. -/
theorem mem_actualPrivateIDEvent_iff (rho : ExtendedPrivateCoordinates p)
    (hE : rho ∈ generatedActualEvent p s j hj P J rewards C_star C_h eta a z peer H)
    (u : Fin (A_id p)) :
    rho ∈ actualPrivateIDEvent p s j P J rewards C_star C_h eta u ↔
      PrivateSourceStreams.privateIDScalarDraw p (splitEquiv p s j hj rho).2.1 = u := by
  constructor
  · rintro ⟨b, h, hf, _, hc, _, hi⟩
    have hd := physical_focal_fields p s j hj P J rewards C_star C_h eta rho b h hc hf
    exact (congrArg (fun d => d.2.2) hd).symm.trans hi
  · intro hi
    rcases hE with ⟨_, b, h, hf, hb, hc, hn, _⟩
    refine ⟨b, h, hf, hb, hc, hn, ?_⟩
    have hd := physical_focal_fields p s j hj P J rewards C_star C_h eta rho b h hc hf
    exact (congrArg (fun d => d.2.2) hd).trans hi

/-- The two ORIGINAL round scalar sequences on the actual shortened block.
These are the inputs of the coordinator and focal physical arm alternatives. -/
def originalRoundPair (rho : ExtendedPrivateCoordinates p) :
    (BlockTime p s → BootstrapPrivateIDFibers.Scalar) ×
      (BlockTime p s → BootstrapPrivateIDFibers.Scalar) :=
  ((fun t => rho.2.1 (coordinatorPlayer p, t.1)),
    (fun t => rho.2.1 (⟨j.val + 1, hj⟩, t.1)))

theorem originalRoundPair_eq_split (rho : ExtendedPrivateCoordinates p) :
    originalRoundPair p s j hj rho = (splitEquiv p s j hj rho).2.2 := rfl

/-- Exact original-coordinate joint event identity, with ACTUAL physical ID. -/
theorem generatedActual_joint_eq_cylinder
    (D : Set ((BlockTime p s → BootstrapPrivateIDFibers.Scalar) ×
      (BlockTime p s → BootstrapPrivateIDFibers.Scalar))) (u : Fin (A_id p)) :
    {rho | rho ∈ generatedActualEvent p s j hj P J rewards C_star C_h eta a z peer H ∧
      rho ∈ actualPrivateIDEvent p s j P J rewards C_star C_h eta u ∧
      originalRoundPair p s j hj rho ∈ D} =
    {rho | (splitEquiv p s j hj rho).1 ∈
        generatedWEvent p s j hj P J rewards C_star C_h eta a z peer H ∧
      PrivateSourceStreams.privateIDScalarDraw p (splitEquiv p s j hj rho).2.1 = u ∧
      (splitEquiv p s j hj rho).2.2 ∈ D} := by
  ext rho
  have he : rho ∈ generatedActualEvent p s j hj P J rewards C_star C_h eta a z peer H ↔
      (splitEquiv p s j hj rho).1 ∈
        generatedWEvent p s j hj P J rewards C_star C_h eta a z peer H := by
    rw [generatedActualEvent_eq_splitCylinder]
    rfl
  constructor
  · rintro ⟨hE, hi, hd⟩
    exact ⟨he.mp hE, (mem_actualPrivateIDEvent_iff p s j hj P J rewards C_star C_h eta
      a z peer H rho hE u).mp hi, by rwa [← originalRoundPair_eq_split]⟩
  · rintro ⟨hw, hi, hd⟩
    have hE := he.mpr hw
    exact ⟨hE, (mem_actualPrivateIDEvent_iff p s j hj P J rewards C_star C_h eta
      a z peer H rho hE u).mpr hi, by rwa [originalRoundPair_eq_split]⟩

/-- The actual physical joint event is measurable for every measurable local
pair event, including all zero-mass history/peer-path events. -/
theorem measurableSet_generatedActual_joint
    (D : Set ((BlockTime p s → BootstrapPrivateIDFibers.Scalar) ×
      (BlockTime p s → BootstrapPrivateIDFibers.Scalar)))
    (u : Fin (A_id p)) (hH : MeasurableSet H) (hD : MeasurableSet D) :
    MeasurableSet {rho | rho ∈
      generatedActualEvent p s j hj P J rewards C_star C_h eta a z peer H ∧
      rho ∈ actualPrivateIDEvent p s j P J rewards C_star C_h eta u ∧
      originalRoundPair p s j hj rho ∈ D} := by
  rw [generatedActual_joint_eq_cylinder]
  have hw := (measurableSet_generatedWEvent p s j hj P J rewards C_star C_h eta a z peer H hH).preimage
    (measurable_fst.comp (splitEquiv p s j hj).measurable)
  have hi := (measurableSet_idFiber p u).preimage
    (measurable_fst.comp (measurable_snd.comp (splitEquiv p s j hj).measurable))
  have hd := hD.preimage (measurable_snd.comp (measurable_snd.comp
    (splitEquiv p s j hj).measurable))
  exact hw.inter (hi.inter hd)

/-- Main internal consumer: the focal ID remains uniform after fixing every
peer's ENTIRE generated physical arm path, with independent original local
round sequences. No positive-mass assumption is needed. The proof consumes
the accepted measure-preserving split and raw ID-fibre mass, after proving
actual boundary causality, physical fields and peer-path factorization.

Source: `appendix_b_communication.tex:302-314`. -/
theorem generatedActual_id_rounds_measure
    (D : Set ((BlockTime p s → BootstrapPrivateIDFibers.Scalar) ×
      (BlockTime p s → BootstrapPrivateIDFibers.Scalar)))
    (u : Fin (A_id p)) (hH : MeasurableSet H) (hD : MeasurableSet D) :
    extendedPrivateLaw p
      {rho | rho ∈ generatedActualEvent p s j hj P J rewards C_star C_h eta a z peer H ∧
        rho ∈ actualPrivateIDEvent p s j P J rewards C_star C_h eta u ∧
        originalRoundPair p s j hj rho ∈ D} =
      extendedPrivateLaw p
        (generatedActualEvent p s j hj P J rewards C_star C_h eta a z peer H) *
        ENNReal.ofReal (1 / (A_id p : ℝ)) * roundPairLaw p s D := by
  rw [generatedActual_joint_eq_cylinder,
    generatedActualEvent_measure p s j hj P J rewards C_star C_h eta a z peer H hH]
  exact split_cylinder_measure p s j hj
    (generatedWEvent p s j hj P J rewards C_star C_h eta a z peer H) D u
    (measurableSet_generatedWEvent p s j hj P J rewards C_star C_h eta a z peer H hH) hD

/-- No event membership can invent a block after a crossing or exhaustion. -/
theorem generatedActualEvent_guards (rho : ExtendedPrivateCoordinates p)
    (hE : rho ∈ generatedActualEvent p s j hj P J rewards C_star C_h eta a z peer H) :
    let b := GeneratedBlockDrawLaw.generatedBoundary p s P.1 (P.2 J)
      rewards C_star C_h eta rho
    b.completed = s.val ∧ b.completed < n_boot p ∧ b.crossing = none ∧
      sourceFollower p j ∈ uninformed b := by
  rcases hE with ⟨_, b, h, hf, hb, hc, hn, _⟩
  dsimp only
  rw [hb]
  exact ⟨hc, h, hn, hf⟩

/-- Stopped or exhausted branches are absent events of zero mass. -/
theorem generatedActual_stopped_exhausted_measure_zero :
    extendedPrivateLaw p
      (generatedActualEvent p s j hj P J rewards C_star C_h eta a z peer H ∩
        {rho | (GeneratedBlockDrawLaw.generatedBoundary p s P.1 (P.2 J)
          rewards C_star C_h eta rho).crossing.isSome = true ∨
          n_boot p ≤ (GeneratedBlockDrawLaw.generatedBoundary p s P.1 (P.2 J)
            rewards C_star C_h eta rho).completed}) = 0 := by
  have he : generatedActualEvent p s j hj P J rewards C_star C_h eta a z peer H ∩
        {rho | (GeneratedBlockDrawLaw.generatedBoundary p s P.1 (P.2 J)
          rewards C_star C_h eta rho).crossing.isSome = true ∨
          n_boot p ≤ (GeneratedBlockDrawLaw.generatedBoundary p s P.1 (P.2 J)
            rewards C_star C_h eta rho).completed} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro rho ⟨hE, hs⟩
    have hg := generatedActualEvent_guards p s j hj P J rewards C_star C_h eta a z peer H rho hE
    rcases hs with hn | hn
    · rw [hg.2.2.1] at hn
      exact Bool.false_ne_true hn
    · exact (Nat.not_le_of_lt hg.2.1) hn
  rw [he, measure_empty]

end Bandits.Support.GeneratedPrivateIDFibers

end
