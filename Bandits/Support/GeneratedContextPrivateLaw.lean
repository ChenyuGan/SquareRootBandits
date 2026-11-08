/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.GeneratedPrivateIDFibers
public import Bandits.Support.GeneratedBootstrapSupportContext
public import Bandits.Support.GeneratedFalseForwardEvent

/-!
# Generated context cells and the original private ID fibre

For a fixed complete published output, true index, rounded rewards, numerical
parameters, block, and original focal follower, this module codes the actual
incoming active context by the accepted source `Context` carrier. The code is
absent on stopped, exhausted, informed, or inactive branches. Its masks use
rounded support and the entire generated path of all other followers.

The context code factors through the accepted private-ID split. Each context
cell therefore obeys the exact unnormalized law for the original ID and the
original coordinator/focal round pair, with an optional measurable event of
the retained coordinates. Zero-mass cells are included.

Sources: `sources/zip4/manuscript/appendix_b_communication.tex:302-338` and
`sources/zip4/manuscript/07_public_setup.tex:123-140`.
-/

public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.CompletePublicTable
open Bandits.Support.ActiveRoundActions
open Bandits.Support.PublicDiscreteDraws
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.BootstrapPrivateIDFibers
open Bandits.Support.ReferencePrelaunchFollower
open Bandits.Support.ReferenceInitializationRun
open Bandits.Support.GeneratedForwardPrefixTests
open Bandits.Support.GeneratedPrivateIDFibers
open Bandits.Support.GeneratedBootstrapSupportContext
open Bandits.Support.GeneratedEligibleFamily
open scoped ENNReal Classical

namespace Bandits.Support.GeneratedContextPrivateLaw

variable {p : Parameters} (s : Fin (n_boot p))
  (j : Fin (p.m - 1)) (hj : j.val + 1 < p.m)
  (P : PublishedOutput p) (J : Fin (M p))
  (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
  (C_star C_h : ℝ) (eta : LearningRate)

abbrev SourceContext (p : Parameters) := FalseForwardContextBound.Context p

abbrev PeerLabel (j : Fin (p.m - 1)) := {k : Fin (p.m - 1) // k ≠ j}

abbrev PeerPath (s : Fin (n_boot p)) (j : Fin (p.m - 1)) :=
  BlockTime p s → PeerLabel j → Fin p.K

private theorem cast_blockInput_eq
    {s₁ s₂ : Fin (n_boot p)} (e : s₁ = s₂)
    (incoming : Finset (Follower p.m))
    (numerators : Fin (p.m - 1) → Fin p.K → ℕ)
    (hpos : ∀ (j : Fin (p.m - 1)) (a : Fin p.K),
      (1 : ℝ) ≤ BootstrapWeightPotential.weight (b_N p) (numerators j) a)
    (ids : IDArray p) (row : CompleteRow p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (coordinates : ExtendedPrivateCoordinates p) :
    e ▸ BootstrapPhysicalInput.blockInput p s₁ incoming numerators hpos
        ids row rewards coordinates =
      BootstrapPhysicalInput.blockInput p s₂ incoming numerators hpos
        ids row rewards coordinates := by
  cases e
  rfl

private theorem cast_held
    {s₁ s₂ : Fin (n_boot p)} (e : s₁ = s₂)
    (v : BootstrapPhysicalBlock.Input p s₁)
    (q : {i // i ∈ v.uninformed}) :
    (e ▸ v).held (GeneratedEligibleFamily.castPhysicalFollower e v q) = v.held q := by
  cases e
  rfl

private theorem cast_target
    {s₁ s₂ : Fin (n_boot p)} (e : s₁ = s₂)
    (v : BootstrapPhysicalBlock.Input p s₁) : (e ▸ v).target = v.target := by
  cases e
  rfl

private theorem cast_rewards
    {s₁ s₂ : Fin (n_boot p)} (e : s₁ = s₂)
    (v : BootstrapPhysicalBlock.Input p s₁) :
    (e ▸ v).rewards = v.rewards := by
  cases e
  rfl

private theorem cast_actions_run
    {s₁ s₂ : Fin (n_boot p)} (e : s₁ = s₂)
    (v : BootstrapPhysicalBlock.Input p s₁) (t : Fin p.T) (i : Fin p.m) :
    BootstrapPhysicalBlock.actions (e ▸ v)
        (BootstrapPhysicalBlock.run (e ▸ v) t.val) t i =
      BootstrapPhysicalBlock.actions v (BootstrapPhysicalBlock.run v t.val) t i := by
  cases e
  rfl

theorem inputEq_subtype_val
    {s : Fin (n_boot p)} (v w : BootstrapPhysicalBlock.Input p s)
    (e : v = w) (q : {i // i ∈ w.uninformed}) :
    (e.symm ▸ q).val = q.val := by
  cases e
  rfl

theorem inputEq_active
    {s : Fin (n_boot p)} (v w : BootstrapPhysicalBlock.Input p s)
    (e : v = w) (q : {i // i ∈ w.uninformed}) :
    v.active (e.symm ▸ q) = w.active q := by
  cases e
  rfl

theorem inputEq_held
    {s : Fin (n_boot p)} (v w : BootstrapPhysicalBlock.Input p s)
    (e : v = w) (q : {i // i ∈ w.uninformed}) :
    v.held (e.symm ▸ q) = w.held q := by
  cases e
  rfl

theorem inputEq_support
    {s : Fin (n_boot p)} (v w : BootstrapPhysicalBlock.Input p s)
    (e : v = w) (q : {i // i ∈ w.uninformed}) (arm : Fin p.K) :
    GeneratedBootstrapSupportContext.supportAvoidanceVector v (e.symm ▸ q) arm =
      GeneratedBootstrapSupportContext.supportAvoidanceVector w q arm := by
  cases e
  rfl

@[expose] def publishedInput
    (P : PublishedOutput p) (J : Fin (M p))
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : LearningRate)
    (rho : ExtendedPrivateCoordinates p) :
    ReferenceInitializationRun.Input p :=
  GeneratedEligibleFamily.referenceInputOfPublishedOutput
    C_star C_h eta rewards J (P, rho)

@[expose] def splitW (s : Fin (n_boot p)) (j : Fin (p.m - 1))
    (hj : j.val + 1 < p.m) (rho : ExtendedPrivateCoordinates p) :
    Complement p s j ⟨j.val + 1, hj⟩ :=
  (BootstrapPrivateIDFibers.splitEquiv p s j hj rho).1

@[expose] def wBoundary (s : Fin (n_boot p)) (j : Fin (p.m - 1))
    (hj : j.val + 1 < p.m) (P : PublishedOutput p) (J : Fin (M p))
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : LearningRate)
    (w : Complement p s j ⟨j.val + 1, hj⟩) : Boundary p :=
  GeneratedPrivateIDFibers.boundaryFromW p s j hj P J rewards C_star C_h eta w

@[expose] def wPeerPath (s : Fin (n_boot p)) (j : Fin (p.m - 1))
    (hj : j.val + 1 < p.m) (P : PublishedOutput p) (J : Fin (M p))
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : LearningRate)
    (w : Complement p s j ⟨j.val + 1, hj⟩) : PeerPath s j :=
  GeneratedPrivateIDFibers.generatedPeerPathFromW p s j hj P J rewards C_star C_h eta w

@[expose] def contextMask (s : Fin (n_boot p)) (j : Fin (p.m - 1))
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (peer : PeerPath s j) (c : Fin p.K) :
    BlockTime p s → Bool := fun t =>
  decide (0 < (rewards t.1 c).val ∧
    ∀ k : Fin (p.m - 1), ∀ hkj : k ≠ j, peer t ⟨k, hkj⟩ ≠ c)

/-- The source context determined by an incoming boundary, the genuine
activity/held/target draws, and a complete peer path. The two masks are the
rounded support indicator conjoined with avoidance by every other follower. -/
@[expose] def contextValueFromBoundary
    (s : Fin (n_boot p)) (j : Fin (p.m - 1)) (J : Fin (M p))
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (a z : Fin p.K) (peer : PeerPath s j) : SourceContext p :=
  ⟨s, (J, (j, (a, (z, (contextMask s j rewards peer a,
    contextMask s j rewards peer z)))))⟩

/-- The W-side observation code. It returns a context only on the actual
processed, incoming-uninformed, active branch. -/
@[expose] def contextCodeFromW
    (s : Fin (n_boot p)) (j : Fin (p.m - 1)) (hj : j.val + 1 < p.m)
    (P : PublishedOutput p) (J : Fin (M p))
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : LearningRate)
    (w : Complement p s j ⟨j.val + 1, hj⟩) : Option (SourceContext p) := by
  classical
  let b := wBoundary s j hj P J rewards C_star C_h eta w
  exact if hguard : b.crossing = none ∧ b.completed = s.val then
    if hin : sourceFollower p j ∈ ReferenceInitializationRun.uninformed b then
      if hactive : PrivateSourceStreams.activityScalarDraw p w.1.1.1 = true then
        let a := PrivateSourceStreams.heldArmScalarDraw p (b.numerators j)
          (b.weight_ge_one j) w.1.1.2
        let z := coordinatorTargetDraw p (w.2.2.2 s)
        some (contextValueFromBoundary s j J rewards a z
          (wPeerPath s j hj P J rewards C_star C_h eta w))
      else none
    else none
  else none

structure FocalActiveWitness (s : Fin (n_boot p))
    (j : Fin (p.m - 1)) (x : ReferenceInitializationRun.Input p) where
  processed : GeneratedForwardPrefixTests.processesBlock x s
  activeFollower : GeneratedForwardPrefixTests.ActiveIncomingFollower x s processed
  focal_eq : activeFollower.val.val = sourceFollower p j

/-- The actual generated witness for a focal incoming active follower. -/
@[expose] def actualFocalActiveWitness
    (s : Fin (n_boot p)) (j : Fin (p.m - 1)) (hj : j.val + 1 < p.m)
    (P : PublishedOutput p) (J : Fin (M p))
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : LearningRate)
    (rho : ExtendedPrivateCoordinates p) :
    Option (FocalActiveWitness s j (publishedInput P J rewards C_star C_h eta rho)) := by
  classical
  let x := publishedInput P J rewards C_star C_h eta rho
  exact if h : GeneratedForwardPrefixTests.processesBlock x s then
    let phys := GeneratedForwardPrefixTests.actualPhysicalBlock x s h
    if hin : sourceFollower p j ∈ phys.uninformed then
      let f : {i // i ∈ phys.uninformed} := ⟨sourceFollower p j, hin⟩
      if hactive : phys.active f = true then
        some ⟨h, ⟨f, hactive⟩, rfl⟩
      else none
    else none
  else none

theorem actualPhysicalInput_eq_actualPhysicalBlock
    (x : ReferenceInitializationRun.Input p)
    (h : GeneratedForwardPrefixTests.processesBlock x s) :
    GeneratedBootstrapSupportContext.actualPhysicalInput x
        (GeneratedForwardPrefixTests.actualBoundary x s) s =
      GeneratedForwardPrefixTests.actualPhysicalBlock x s h := by
  let hrem := GeneratedForwardPrefixTests.actualBlockRemaining x s h
  let hindex := GeneratedForwardPrefixTests.actualBlockIndex x s h
  change GeneratedBootstrapSupportContext.actualPhysicalInput x
      (ReferenceInitializationRun.run x s.val) s =
    hindex ▸ ReferenceInitializationRun.physical x
      (ReferenceInitializationRun.run x s.val) hrem
  change BootstrapPhysicalInput.blockInput p s
      (ReferenceInitializationRun.uninformed (ReferenceInitializationRun.run x s.val))
      (ReferenceInitializationRun.run x s.val).numerators
      (ReferenceInitializationRun.run x s.val).weight_ge_one
      x.ids x.row x.rewards x.coordinates =
    hindex ▸ BootstrapPhysicalInput.blockInput p
      (ReferenceInitializationRun.nextBlock (ReferenceInitializationRun.run x s.val) hrem)
      (ReferenceInitializationRun.uninformed (ReferenceInitializationRun.run x s.val))
      (ReferenceInitializationRun.run x s.val).numerators
      (ReferenceInitializationRun.run x s.val).weight_ge_one
      x.ids x.row x.rewards x.coordinates
  exact (cast_blockInput_eq (p := p) hindex
    (ReferenceInitializationRun.uninformed (ReferenceInitializationRun.run x s.val))
    (ReferenceInitializationRun.run x s.val).numerators
    (ReferenceInitializationRun.run x s.val).weight_ge_one x.ids x.row x.rewards
    x.coordinates).symm

@[expose] def actualLocalBlockOfWitness
    (s : Fin (n_boot p)) (j : Fin (p.m - 1)) (hj : j.val + 1 < p.m)
    (P : PublishedOutput p) (J : Fin (M p))
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : LearningRate)
    (rho : ExtendedPrivateCoordinates p)
    (w : FocalActiveWitness s j (publishedInput P J rewards C_star C_h eta rho)) :
    GeneratedBootstrapSupportContext.ActualLocalBlock P J
      (publishedInput P J rewards C_star C_h eta rho) s := by
  let x := publishedInput P J rewards C_star C_h eta rho
  let h := w.processed
  let q := w.activeFollower
  let b := GeneratedForwardPrefixTests.actualBoundary x s
  let heq := actualPhysicalInput_eq_actualPhysicalBlock s x h
  let f : {i // i ∈
      (GeneratedBootstrapSupportContext.actualPhysicalInput x b s).uninformed} :=
    heq.symm ▸ q.val
  refine ⟨rfl, rfl, b, rfl, h.2, f, ?_, ?_⟩
  · have hmem : q.val.val ∈
        (GeneratedBootstrapSupportContext.actualPhysicalInput x b s).uninformed := by
      change q.val.val ∈ (GeneratedBootstrapSupportContext.actualPhysicalInput x b s).uninformed
      rw [heq]
      exact q.val.property
    have hval : f.val = q.val.val := inputEq_subtype_val _ _ heq q.val
    change f.val ∈ ReferenceInitializationRun.uninformed b
    rw [hval]
    simpa [GeneratedBootstrapSupportContext.actualPhysicalInput,
      BootstrapPhysicalInput.blockInput_uninformed] using hmem
  · change (GeneratedBootstrapSupportContext.actualPhysicalInput x b s).active f = true
    exact (inputEq_active _ _ heq q.val).trans q.property

/-- The actual observation code, formed from `actualContextMap` on the real
generated stopped run. It has no default context on failure or stop branches. -/
@[expose] def contextCode
    (s : Fin (n_boot p)) (j : Fin (p.m - 1)) (hj : j.val + 1 < p.m)
    (P : PublishedOutput p) (J : Fin (M p))
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : LearningRate)
    (rho : ExtendedPrivateCoordinates p) : Option (SourceContext p) :=
  (actualFocalActiveWitness s j hj P J rewards C_star C_h eta rho).map fun w =>
    GeneratedBootstrapSupportContext.actualContextMap P J
      (publishedInput P J rewards C_star C_h eta rho) s
      (actualLocalBlockOfWitness s j hj P J rewards C_star C_h eta rho w)

@[expose] def contextWCell
    (s : Fin (n_boot p)) (j : Fin (p.m - 1)) (hj : j.val + 1 < p.m)
    (P : PublishedOutput p) (J : Fin (M p))
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : LearningRate)
    (H : Set (Complement p s j ⟨j.val + 1, hj⟩))
    (c : SourceContext p) : Set (Complement p s j ⟨j.val + 1, hj⟩) :=
  {w | contextCodeFromW s j hj P J rewards C_star C_h eta w = some c ∧ w ∈ H}

private def contextWCellUnion
    (s : Fin (n_boot p)) (j : Fin (p.m - 1)) (hj : j.val + 1 < p.m)
    (P : PublishedOutput p) (J : Fin (M p))
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : LearningRate)
    (H : Set (Complement p s j ⟨j.val + 1, hj⟩))
    (c : SourceContext p) : Set (Complement p s j ⟨j.val + 1, hj⟩) :=
  ⋃ b : Boundary p, ⋃ a : Fin p.K, ⋃ z : Fin p.K, ⋃ peer : PeerPath s j,
    if contextValueFromBoundary s j J rewards a z peer = c then
      GeneratedPrivateIDFibers.generatedWEvent p s j hj P J rewards C_star C_h eta
        a z peer H ∩ {w | GeneratedPrivateIDFibers.boundaryFromW p s j hj P J rewards C_star C_h eta w = b}
    else ∅

private theorem contextWCell_eq_union
    (H : Set (Complement p s j ⟨j.val + 1, hj⟩)) (c : SourceContext p) :
    contextWCell s j hj P J rewards C_star C_h eta H c =
      contextWCellUnion s j hj P J rewards C_star C_h eta H c := by
  classical
  ext w
  constructor
  · rintro ⟨hc, hH⟩
    unfold contextCodeFromW at hc
    dsimp only at hc
    split_ifs at hc with hguard hin hactive
    · simp only [Option.some.injEq] at hc
      let b := wBoundary s j hj P J rewards C_star C_h eta w
      let a := PrivateSourceStreams.heldArmScalarDraw p (b.numerators j)
        (b.weight_ge_one j) w.1.1.2
      let z := coordinatorTargetDraw p (w.2.2.2 s)
      let peer := wPeerPath s j hj P J rewards C_star C_h eta w
      have hblock : w ∈ GeneratedPrivateIDFibers.blockWCondition p s j hj P J a z peer b := by
        exact ⟨hguard.2, hguard.1, hin, hactive, rfl, rfl, fun _ _ => rfl⟩
      refine Set.mem_iUnion.mpr ⟨b, Set.mem_iUnion.mpr ⟨a,
        Set.mem_iUnion.mpr ⟨z, Set.mem_iUnion.mpr ⟨peer, ?_⟩⟩⟩⟩
      have hgen : w ∈ GeneratedPrivateIDFibers.generatedWEvent p s j hj P J
          rewards C_star C_h eta a z peer H := by
        exact ⟨hH, b, rfl, hblock⟩
      change w ∈ (if contextValueFromBoundary s j J rewards a z peer = c then
        GeneratedPrivateIDFibers.generatedWEvent p s j hj P J rewards C_star C_h eta
          a z peer H ∩
          {w | GeneratedPrivateIDFibers.boundaryFromW p s j hj P J rewards C_star C_h eta w = b}
        else ∅)
      rw [if_pos hc]
      exact ⟨hgen, rfl⟩
  · intro hw
    rcases Set.mem_iUnion.mp hw with ⟨b, hw⟩
    rcases Set.mem_iUnion.mp hw with ⟨a, hw⟩
    rcases Set.mem_iUnion.mp hw with ⟨z, hw⟩
    rcases Set.mem_iUnion.mp hw with ⟨peer, hw⟩
    by_cases hv : contextValueFromBoundary s j J rewards a z peer = c
    · simp only [if_pos hv, Set.mem_inter_iff, Set.mem_setOf_eq] at hw
      rcases hw with ⟨hGenerated, hboundary⟩
      rcases hGenerated with ⟨hH, b', hb', hblock'⟩
      have hbeq : b' = b := hb'.symm.trans hboundary
      subst b'
      rcases hblock' with ⟨hcompleted, hcrossing, hin, hactive, hheld, htarget, hpeer⟩
      have hguard : (wBoundary s j hj P J rewards C_star C_h eta w).crossing = none ∧
          (wBoundary s j hj P J rewards C_star C_h eta w).completed = s.val :=
        ⟨by simpa [wBoundary] using hcrossing,
          by simpa [wBoundary] using hcompleted⟩
      have hin' : sourceFollower p j ∈
          ReferenceInitializationRun.uninformed (wBoundary s j hj P J rewards C_star C_h eta w) := by
        simpa [wBoundary] using hin
      have hactive' : PrivateSourceStreams.activityScalarDraw p w.1.1.1 = true := by
        simpa [wBoundary] using hactive
      have hheld' : PrivateSourceStreams.heldArmScalarDraw p
          ((wBoundary s j hj P J rewards C_star C_h eta w).numerators j)
          ((wBoundary s j hj P J rewards C_star C_h eta w).weight_ge_one j) w.1.1.2 = a := by
        simpa [wBoundary] using hheld
      have htarget' : coordinatorTargetDraw p (w.2.2.2 s) = z := by
        exact htarget
      have hpeer' : wPeerPath s j hj P J rewards C_star C_h eta w = peer := by
        funext t
        funext k
        simpa [wPeerPath, GeneratedPrivateIDFibers.generatedPeerPathFromW] using hpeer t k
      have hcode : contextCodeFromW s j hj P J rewards C_star C_h eta w =
          some (contextValueFromBoundary s j J rewards a z peer) := by
        have hvalue : contextValueFromBoundary s j J rewards
            (PrivateSourceStreams.heldArmScalarDraw p
              ((wBoundary s j hj P J rewards C_star C_h eta w).numerators j)
              ((wBoundary s j hj P J rewards C_star C_h eta w).weight_ge_one j) w.1.1.2)
            (coordinatorTargetDraw p (w.2.2.2 s))
            (wPeerPath s j hj P J rewards C_star C_h eta w) =
          contextValueFromBoundary s j J rewards a z peer := by
          rw [hheld', htarget', hpeer']
        simp [contextCodeFromW, hguard, hin', hactive', hvalue]
      exact ⟨by simpa [hv] using hcode, hH⟩
    · simp [hv] at hw

/-- Every W-context cell is measurable from the literal generated W-event and
the measurable boundary fibres. -/
theorem measurableSet_contextWCell
    (H : Set (Complement p s j ⟨j.val + 1, hj⟩)) (hH : MeasurableSet H)
    (c : SourceContext p) : MeasurableSet (contextWCell s j hj P J rewards C_star C_h eta H c) := by
  classical
  rw [contextWCell_eq_union s j hj P J rewards C_star C_h eta H c]
  apply MeasurableSet.iUnion
  intro b
  apply MeasurableSet.iUnion
  intro a
  apply MeasurableSet.iUnion
  intro z
  apply MeasurableSet.iUnion
  intro peer
  split_ifs with hc
  · have hgen := GeneratedPrivateIDFibers.measurableSet_generatedWEvent
      p s j hj P J rewards C_star C_h eta a z peer H hH
    have hb := (measurableSet_singleton b).preimage
      (GeneratedPrivateIDFibers.measurable_boundaryFromW p s j hj P J rewards C_star C_h eta)
    exact hgen.inter hb
  · exact MeasurableSet.empty

private theorem actualContextCode_eq_W
    (rho : ExtendedPrivateCoordinates p) :
    contextCode s j hj P J rewards C_star C_h eta rho =
      contextCodeFromW s j hj P J rewards C_star C_h eta
        (splitW s j hj rho) := by
  classical
  let x := publishedInput P J rewards C_star C_h eta rho
  let w := splitW s j hj rho
  let b := GeneratedForwardPrefixTests.actualBoundary x s
  have hboundary :
      GeneratedBlockDrawLaw.generatedBoundary p s P.1 (P.2 J) rewards C_star C_h eta rho =
        wBoundary s j hj P J rewards C_star C_h eta w := by
    exact GeneratedPrivateIDFibers.generatedBoundary_eq_boundaryFromW
      p s j hj P J rewards C_star C_h eta rho
  change _ = _
  by_cases hproc : GeneratedForwardPrefixTests.processesBlock x s
  · let phys := GeneratedForwardPrefixTests.actualPhysicalBlock x s hproc
    have hcrossGen : (GeneratedBlockDrawLaw.generatedBoundary p s P.1 (P.2 J)
        rewards C_star C_h eta rho).crossing = none := by
      change (ReferenceInitializationRun.run x s.val).crossing = none
      exact hproc.1
    have hcross : (wBoundary s j hj P J rewards C_star C_h eta w).crossing = none := by
      rw [← hboundary]
      exact hcrossGen
    have hcompletedGen : (GeneratedBlockDrawLaw.generatedBoundary p s P.1 (P.2 J)
        rewards C_star C_h eta rho).completed = s.val := by
      change (ReferenceInitializationRun.run x s.val).completed = s.val
      exact hproc.2
    have hcompleted : (wBoundary s j hj P J rewards C_star C_h eta w).completed = s.val := by
      rw [← hboundary]
      exact hcompletedGen
    have hguard : (wBoundary s j hj P J rewards C_star C_h eta w).crossing = none ∧
        (wBoundary s j hj P J rewards C_star C_h eta w).completed = s.val :=
      ⟨hcross, hcompleted⟩
    have hrem : (wBoundary s j hj P J rewards C_star C_h eta w).completed < n_boot p := by
      rw [hcompleted]
      exact s.isLt
    have hinputActual := actualPhysicalInput_eq_actualPhysicalBlock s x hproc
    have hsetActual : phys.uninformed = ReferenceInitializationRun.uninformed
        (GeneratedForwardPrefixTests.actualBoundary x s) := by
      have hh := congrArg (fun v : BootstrapPhysicalBlock.Input p s => v.uninformed) hinputActual
      simpa [GeneratedBootstrapSupportContext.actualPhysicalInput,
        BootstrapPhysicalInput.blockInput_uninformed] using hh.symm
    by_cases hin : sourceFollower p j ∈ phys.uninformed
    · let f : {i // i ∈ phys.uninformed} := ⟨sourceFollower p j, hin⟩
      have hfocalActualBoundary : sourceFollower p j ∈
          ReferenceInitializationRun.uninformed (GeneratedForwardPrefixTests.actualBoundary x s) := by
        rw [← hsetActual]
        exact hin
      have hfocalGenerated : sourceFollower p j ∈
          ReferenceInitializationRun.uninformed
            (GeneratedBlockDrawLaw.generatedBoundary p s P.1 (P.2 J) rewards C_star C_h eta rho) := by
        have hactualBoundary : GeneratedBlockDrawLaw.generatedBoundary p s P.1 (P.2 J)
            rewards C_star C_h eta rho =
            GeneratedForwardPrefixTests.actualBoundary x s := by
          rfl
        exact hactualBoundary.symm ▸ hfocalActualBoundary
      have hfocalW : sourceFollower p j ∈ ReferenceInitializationRun.uninformed
          (wBoundary s j hj P J rewards C_star C_h eta w) := by
        rw [hboundary] at hfocalGenerated
        exact hfocalGenerated
      by_cases hactive : phys.active f = true
      ·
        have hbW : b = wBoundary s j hj P J rewards C_star C_h eta w := by
          change GeneratedBlockDrawLaw.generatedBoundary p s P.1 (P.2 J)
            rewards C_star C_h eta rho = wBoundary s j hj P J rewards C_star C_h eta w
          exact hboundary
        let hremActual := GeneratedForwardPrefixTests.actualBlockRemaining x s hproc
        let raw := ReferenceInitializationRun.physical x b hremActual
        let hindex := GeneratedForwardPrefixTests.actualBlockIndex x s hproc
        have hphys : phys = hindex ▸ raw := rfl
        have hcastUninformed : phys.uninformed = raw.uninformed := by
          rw [hphys]
          exact GeneratedEligibleFamily.castPhysicalBlock_uninformed hindex raw
        have hfocalActual : sourceFollower p j ∈ ReferenceInitializationRun.uninformed b := by
          have hinRaw : sourceFollower p j ∈ raw.uninformed := by
            rw [← hcastUninformed]
            exact hin
          simpa [raw, ReferenceInitializationRun.physical,
            BootstrapPhysicalInput.blockInput] using hinRaw
        let fRaw : {i // i ∈ raw.uninformed} := ⟨sourceFollower p j, by
          simpa [raw, ReferenceInitializationRun.physical,
            BootstrapPhysicalInput.blockInput] using hfocalActual⟩
        have hf : f = GeneratedEligibleFamily.castPhysicalFollower hindex raw fRaw := by
          apply Subtype.ext
          rfl
        have hcastFollower : hphys ▸ f =
            GeneratedEligibleFamily.castPhysicalFollower hindex raw fRaw := by
          apply Subtype.ext
          calc
            (hphys ▸ f).val = f.val :=
              inputEq_subtype_val (hindex ▸ raw) phys hphys.symm f
            _ = fRaw.val := rfl
            _ = (GeneratedEligibleFamily.castPhysicalFollower hindex raw fRaw).val := rfl
        have hfields := GeneratedPrivateIDFibers.physical_focal_fields
          p s j hj P J rewards C_star C_h eta rho b hremActual hproc.2 hfocalActual
        have hactivity : PrivateSourceStreams.activityScalarDraw p w.1.1.1 = true := by
          have hactiveTransport := inputEq_active (hindex ▸ raw) phys hphys.symm f
          rw [hcastFollower] at hactiveTransport
          have hactiveCast : (hindex ▸ raw).active
              (GeneratedEligibleFamily.castPhysicalFollower hindex raw fRaw) = true :=
            hactiveTransport.trans hactive
          have hactiveRaw : raw.active fRaw = true := by
            rw [GeneratedEligibleFamily.castPhysicalFollower_active] at hactiveCast
            exact hactiveCast
          have hdraw := (congrArg Prod.fst hfields).symm.trans hactiveRaw
          simpa [w, splitW] using hdraw
        have hheld : phys.held f = PrivateSourceStreams.heldArmScalarDraw p
            ((wBoundary s j hj P J rewards C_star C_h eta w).numerators j)
            ((wBoundary s j hj P J rewards C_star C_h eta w).weight_ge_one j) w.1.1.2 := by
          calc
            phys.held f = raw.held fRaw := by
              calc
                phys.held f = (hindex ▸ raw).held (hphys ▸ f) :=
                  (inputEq_held (hindex ▸ raw) phys hphys.symm f).symm
                _ = (hindex ▸ raw).held
                    (GeneratedEligibleFamily.castPhysicalFollower hindex raw fRaw) := by
                  rw [hcastFollower]
                _ = raw.held fRaw := cast_held hindex raw fRaw
            _ = PrivateSourceStreams.heldArmScalarDraw p
                ((wBoundary s j hj P J rewards C_star C_h eta w).numerators j)
                ((wBoundary s j hj P J rewards C_star C_h eta w).weight_ge_one j) w.1.1.2 := by
              simpa [raw, hbW, w, splitW, x, BootstrapPrivateIDFibers.initialRunInput,
                publishedInput, fRaw, GeneratedEligibleFamily.referenceInputOfPublishedOutput] using
                congrArg (fun d => d.2.1) hfields
        have htarget : phys.target = coordinatorTargetDraw p (w.2.2.2 s) := by
          calc
            phys.target = raw.target := by
              change (hindex ▸ raw).target = raw.target
              exact cast_target hindex raw
            _ = coordinatorTargetDraw p (w.2.2.2 s) := by
              simpa [raw, hbW, w, splitW, x, ReferenceInitializationRun.physical,
                BootstrapPhysicalInput.blockInput, BootstrapPrivateIDFibers.initialRunInput,
                publishedInput, GeneratedEligibleFamily.referenceInputOfPublishedOutput] using
                (GeneratedPrivateIDFibers.physical_target_fromW
                  p s j hj P J rewards C_star C_h eta rho b hremActual hproc.2)
        have hboundaryActual : GeneratedBlockDrawLaw.generatedBoundary p s P.1 (P.2 J)
            rewards C_star C_h eta rho = b := by
          rfl
        have hpeer := GeneratedPrivateIDFibers.generated_peer_path_factor
          p s j hj P J rewards C_star C_h eta rho b hremActual hboundaryActual
          hproc.2 hproc.1
        have hpeerAction : ∀ t k,
            BootstrapPhysicalBlock.actions phys (BootstrapPhysicalBlock.run phys t.1.val)
              t.1 (PublicDiscreteDraws.followerPlayer p.two_le_m (sourceFollower p k.1)) =
              wPeerPath s j hj P J rewards C_star C_h eta w t k := by
          intro t k
          calc
            BootstrapPhysicalBlock.actions phys (BootstrapPhysicalBlock.run phys t.1.val)
                t.1 (PublicDiscreteDraws.followerPlayer p.two_le_m (sourceFollower p k.1)) =
              BootstrapPhysicalBlock.actions raw (BootstrapPhysicalBlock.run raw t.1.val)
                t.1 (PublicDiscreteDraws.followerPlayer p.two_le_m (sourceFollower p k.1)) := by
                  rw [hphys]
                  exact cast_actions_run hindex raw t.1
                    (PublicDiscreteDraws.followerPlayer p.two_le_m (sourceFollower p k.1))
            _ = wPeerPath s j hj P J rewards C_star C_h eta w t k := by
              simpa [raw, w, splitW, x, wPeerPath,
                GeneratedPrivateIDFibers.generatedPeerPathFromW,
                ReferenceInitializationRun.physical, BootstrapPhysicalInput.blockInput,
                BootstrapPrivateIDFibers.initialRunInput, publishedInput,
                GeneratedEligibleFamily.referenceInputOfPublishedOutput] using
                congrFun (congrFun hpeer.2 t) k
        have hreward : phys.rewards = rewards := by
          rw [hphys, cast_rewards]
          simp [raw, x, ReferenceInitializationRun.physical,
            BootstrapPhysicalInput.blockInput, publishedInput,
            GeneratedEligibleFamily.referenceInputOfPublishedOutput]
        have hmask (arm : Fin p.K) :
            GeneratedBootstrapSupportContext.supportAvoidanceVector phys f arm =
              contextMask s j rewards
                (wPeerPath s j hj P J rewards C_star C_h eta w) arm := by
          funext t
          have hphysical :=
            GeneratedBootstrapSupportContext.supportAvoidanceVector_true_iff phys f arm t
          have hiff :
              GeneratedBootstrapSupportContext.supportAvoidanceVector phys f arm t = true ↔
                contextMask s j rewards
                  (wPeerPath s j hj P J rewards C_star C_h eta w) arm t = true := by
            rw [hphysical]
            simp only [contextMask, decide_eq_true_eq]
            rw [hreward]
            constructor
            · rintro ⟨hr, havoid⟩
              refine ⟨hr, ?_⟩
              intro k hkj
              let k' : PeerLabel j := ⟨k, hkj⟩
              have hact := hpeerAction t k'
              have hne : PublicDiscreteDraws.followerPlayer p.two_le_m
                  (sourceFollower p k) ≠ PublicDiscreteDraws.followerPlayer p.two_le_m f.1 := by
                intro heq
                have hsource := ActiveRoundActions.followerPlayer_injective p.two_le_m heq
                have hindexEq := congrArg (BootstrapPhysicalInput.sourceFollowerIndex p) hsource
                apply hkj
                simpa [f, BootstrapPrivateIDFibers.sourceFollowerIndex_eq] using hindexEq
              have hnotcoord :=
                (ActiveRoundActions.followerPlayer_ne_coordinator p.two_le_m
                  (sourceFollower p k))
              have hv := havoid _ hnotcoord hne
              rw [hact] at hv
              exact hv
            · rintro ⟨hr, havoid⟩
              refine ⟨hr, ?_⟩
              intro player hcoord hfocus
              rcases ActiveRoundActions.player_cases p.two_le_m player with hzero | ⟨i, rfl⟩
              · exact (hcoord hzero).elim
              · have hi : i ≠ j := by
                  intro heq
                  apply hfocus
                  have hsourceEq : sourceFollower p i = sourceFollower p j :=
                    congrArg (sourceFollower p) heq
                  exact congrArg (PublicDiscreteDraws.followerPlayer p.two_le_m) hsourceEq
                let k' : PeerLabel j := ⟨i, hi⟩
                have hact := hpeerAction t k'
                have hplayer : PublicDiscreteDraws.followerPlayer p.two_le_m
                    (sourceFollower p i) = PublicDiscreteDraws.followerPlayer p.two_le_m i := by
                  exact congrArg (PublicDiscreteDraws.followerPlayer p.two_le_m)
                    (by apply Fin.ext; rfl)
                have hv := havoid i hi
                rw [← hplayer, hact]
                exact hv
          exact Bool.eq_iff_iff.mpr hiff
        let witness : FocalActiveWitness s j x := ⟨hproc, ⟨f, hactive⟩, rfl⟩
        let localBlock := actualLocalBlockOfWitness s j hj P J rewards C_star C_h eta rho witness
        have hinput : GeneratedBootstrapSupportContext.actualPhysicalInput x
            (GeneratedForwardPrefixTests.actualBoundary x s) s = phys := by
          simpa [phys] using actualPhysicalInput_eq_actualPhysicalBlock s x hproc
        have hlocalFollower : localBlock.follower = hinput.symm ▸ f := by
          apply Subtype.ext
          rfl
        have hlocalHeld :
            (GeneratedBootstrapSupportContext.actualPhysicalInput x localBlock.incoming s).held
                localBlock.follower = phys.held f := by
          change (GeneratedBootstrapSupportContext.actualPhysicalInput x
            (GeneratedForwardPrefixTests.actualBoundary x s) s).held localBlock.follower = _
          rw [hlocalFollower]
          exact inputEq_held _ _ hinput f
        have hlocalTarget :
            (GeneratedBootstrapSupportContext.actualPhysicalInput x localBlock.incoming s).target =
              phys.target := by
          change (GeneratedBootstrapSupportContext.actualPhysicalInput x
            (GeneratedForwardPrefixTests.actualBoundary x s) s).target = _
          exact congrArg (fun v : BootstrapPhysicalBlock.Input p s => v.target) hinput
        have hlocalMask (arm : Fin p.K) :
            GeneratedBootstrapSupportContext.supportAvoidanceVector
              (GeneratedBootstrapSupportContext.actualPhysicalInput x localBlock.incoming s)
              localBlock.follower arm =
            GeneratedBootstrapSupportContext.supportAvoidanceVector phys f arm := by
          change GeneratedBootstrapSupportContext.supportAvoidanceVector
            (GeneratedBootstrapSupportContext.actualPhysicalInput x
              (GeneratedForwardPrefixTests.actualBoundary x s) s) localBlock.follower arm = _
          rw [hlocalFollower]
          exact inputEq_support _ _ hinput f arm
        have hcontext : GeneratedBootstrapSupportContext.actualContextMap P J x s
            localBlock =
          contextValueFromBoundary s j J rewards
            (PrivateSourceStreams.heldArmScalarDraw p
              ((wBoundary s j hj P J rewards C_star C_h eta w).numerators j)
              ((wBoundary s j hj P J rewards C_star C_h eta w).weight_ge_one j) w.1.1.2)
            (coordinatorTargetDraw p (w.2.2.2 s))
            (wPeerPath s j hj P J rewards C_star C_h eta w) := by
          change (⟨s, (J, (BootstrapPhysicalInput.sourceFollowerIndex p localBlock.follower.val,
            (GeneratedBootstrapSupportContext.actualPhysicalInput x localBlock.incoming s).held
              localBlock.follower,
            (GeneratedBootstrapSupportContext.actualPhysicalInput x localBlock.incoming s).target,
            GeneratedBootstrapSupportContext.supportAvoidanceVector
              (GeneratedBootstrapSupportContext.actualPhysicalInput x localBlock.incoming s)
              localBlock.follower
              ((GeneratedBootstrapSupportContext.actualPhysicalInput x localBlock.incoming s).held
                localBlock.follower),
            GeneratedBootstrapSupportContext.supportAvoidanceVector
              (GeneratedBootstrapSupportContext.actualPhysicalInput x localBlock.incoming s)
              localBlock.follower
              (GeneratedBootstrapSupportContext.actualPhysicalInput x localBlock.incoming s).target))⟩ :
              SourceContext p) = _
          rw [hlocalHeld, hlocalTarget,
            hlocalMask (phys.held f), hlocalMask phys.target]
          rw [hheld, htarget,
            hmask (PrivateSourceStreams.heldArmScalarDraw p
              ((wBoundary s j hj P J rewards C_star C_h eta w).numerators j)
              ((wBoundary s j hj P J rewards C_star C_h eta w).weight_ge_one j) w.1.1.2),
            hmask (coordinatorTargetDraw p (w.2.2.2 s))]
          have hlocalVal : localBlock.follower.val = sourceFollower p j := by
            rw [hlocalFollower]
            exact (inputEq_subtype_val _ _ hinput f).trans rfl
          have hsourceIndex : BootstrapPhysicalInput.sourceFollowerIndex p localBlock.follower.val = j := by
            rw [hlocalVal]
            exact BootstrapPrivateIDFibers.sourceFollowerIndex_eq p j
          rw [hsourceIndex]
          rfl
        have hactualWitness : actualFocalActiveWitness s j hj P J rewards C_star C_h eta rho =
            some witness := by
          simp only [actualFocalActiveWitness, x, dif_pos hproc]
          have hmem : sourceFollower p j ∈
              (GeneratedForwardPrefixTests.actualPhysicalBlock
                (publishedInput P J rewards C_star C_h eta rho) s hproc).uninformed := by
            simpa [phys] using hin
          rw [dif_pos hmem]
          have hq : (⟨sourceFollower p j, hmem⟩ :
              {i // i ∈ (GeneratedForwardPrefixTests.actualPhysicalBlock
                (publishedInput P J rewards C_star C_h eta rho) s hproc).uninformed}) = f := by
            apply Subtype.ext
            rfl
          have hact : (GeneratedForwardPrefixTests.actualPhysicalBlock
              (publishedInput P J rewards C_star C_h eta rho) s hproc).active
                ⟨sourceFollower p j, hmem⟩ = true := by
            rw [hq]
            simpa [phys] using hactive
          rw [dif_pos hact]
        rw [contextCode, hactualWitness]
        simpa [contextCodeFromW, w, hguard, hfocalW, hactivity, x] using hcontext
      · have hactivity : PrivateSourceStreams.activityScalarDraw p w.1.1.1 = false := by
          let bActual := GeneratedForwardPrefixTests.actualBoundary x s
          let hremActual := GeneratedForwardPrefixTests.actualBlockRemaining x s hproc
          let raw := ReferenceInitializationRun.physical x bActual hremActual
          let hindex := GeneratedForwardPrefixTests.actualBlockIndex x s hproc
          have hphys : phys = hindex ▸ raw := rfl
          have hcastUninformed : phys.uninformed = raw.uninformed := by
            rw [hphys]
            exact GeneratedEligibleFamily.castPhysicalBlock_uninformed hindex raw
          have hfocalActual : sourceFollower p j ∈ ReferenceInitializationRun.uninformed bActual := by
            have hinRaw : sourceFollower p j ∈ raw.uninformed := by
              rw [← hcastUninformed]
              exact hin
            simpa [raw, bActual, ReferenceInitializationRun.physical,
              BootstrapPhysicalInput.blockInput] using hinRaw
          let fRaw : {i // i ∈ raw.uninformed} := ⟨sourceFollower p j, by
            simpa [raw, bActual, ReferenceInitializationRun.physical,
              BootstrapPhysicalInput.blockInput] using hfocalActual⟩
          have hcastFollower : hphys ▸ f =
              GeneratedEligibleFamily.castPhysicalFollower hindex raw fRaw := by
            apply Subtype.ext
            calc
              (hphys ▸ f).val = f.val :=
                inputEq_subtype_val (hindex ▸ raw) phys hphys.symm f
              _ = fRaw.val := rfl
          have hfields := GeneratedPrivateIDFibers.physical_focal_fields
            p s j hj P J rewards C_star C_h eta rho
            bActual hremActual hproc.2 hfocalActual
          have hphysFalse : phys.active f = false := Bool.eq_false_of_not_eq_true hactive
          have hactiveTransport := inputEq_active (hindex ▸ raw) phys hphys.symm f
          rw [hcastFollower] at hactiveTransport
          have hactiveCast : (hindex ▸ raw).active
              (GeneratedEligibleFamily.castPhysicalFollower hindex raw fRaw) = false :=
            hactiveTransport.trans hphysFalse
          have hactiveRaw : raw.active fRaw = false := by
            rw [GeneratedEligibleFamily.castPhysicalFollower_active] at hactiveCast
            exact hactiveCast
          have hdraw := (congrArg Prod.fst hfields).symm.trans hactiveRaw
          simpa [w, splitW, raw, bActual, x, BootstrapPrivateIDFibers.initialRunInput,
            ReferenceInitializationRun.physical, BootstrapPhysicalInput.blockInput,
            publishedInput, GeneratedEligibleFamily.referenceInputOfPublishedOutput] using hdraw
        have hactiveFalse : ∀ (h : sourceFollower p j ∈ phys.uninformed),
            phys.active ⟨sourceFollower p j, h⟩ = false := by
          intro h
          have hq : (⟨sourceFollower p j, h⟩ : {i // i ∈ phys.uninformed}) = f := by
            apply Subtype.ext
            rfl
          rw [hq]
          exact Bool.eq_false_of_not_eq_true hactive
        have hactualWitness : actualFocalActiveWitness s j hj P J rewards C_star C_h eta rho = none := by
          simp only [actualFocalActiveWitness, x, dif_pos hproc]
          have hmem : sourceFollower p j ∈
              (GeneratedForwardPrefixTests.actualPhysicalBlock
                (publishedInput P J rewards C_star C_h eta rho) s hproc).uninformed := by
            simpa [phys] using hin
          rw [dif_pos hmem]
          have hact : ¬((GeneratedForwardPrefixTests.actualPhysicalBlock
              (publishedInput P J rewards C_star C_h eta rho) s hproc).active
                ⟨sourceFollower p j, hmem⟩ = true) := by
            intro hh
            have hq : (⟨sourceFollower p j, hmem⟩ :
                {i // i ∈ (GeneratedForwardPrefixTests.actualPhysicalBlock
                  (publishedInput P J rewards C_star C_h eta rho) s hproc).uninformed}) = f := by
              apply Subtype.ext
              rfl
            rw [hq] at hh
            exact hactive (by simpa [phys] using hh)
          rw [dif_neg hact]
        rw [contextCode, hactualWitness]
        simp [contextCodeFromW, w, hguard, hfocalW, hactivity]
    · have hinW : sourceFollower p j ∉ ReferenceInitializationRun.uninformed
          (wBoundary s j hj P J rewards C_star C_h eta w) := by
        intro hm
        apply hin
        have hmActual : sourceFollower p j ∈
            ReferenceInitializationRun.uninformed (GeneratedForwardPrefixTests.actualBoundary x s) := by
          have hmGen : sourceFollower p j ∈
              ReferenceInitializationRun.uninformed
                (GeneratedBlockDrawLaw.generatedBoundary p s P.1 (P.2 J)
                  rewards C_star C_h eta rho) := by
            rw [hboundary]
            exact hm
          have hx : x = GeneratedBlockDrawLaw.fixedReferenceInput p P.1 (P.2 J)
              rewards C_star C_h eta rho := by
            rfl
          rw [GeneratedForwardPrefixTests.actualBoundary, hx]
          simpa [GeneratedBlockDrawLaw.generatedBoundary] using hmGen
        have hinput := actualPhysicalInput_eq_actualPhysicalBlock s x hproc
        have hset : (GeneratedForwardPrefixTests.actualPhysicalBlock x s hproc).uninformed =
            ReferenceInitializationRun.uninformed (GeneratedForwardPrefixTests.actualBoundary x s) := by
          have hh := congrArg (fun v : BootstrapPhysicalBlock.Input p s => v.uninformed) hinput
          simpa [GeneratedBootstrapSupportContext.actualPhysicalInput,
            BootstrapPhysicalInput.blockInput_uninformed] using hh.symm
        rw [hset]
        exact hmActual
      have hactualWitness : actualFocalActiveWitness s j hj P J rewards C_star C_h eta rho = none := by
        simp only [actualFocalActiveWitness, x, dif_pos hproc]
        have hmem : ¬(sourceFollower p j ∈
            (GeneratedForwardPrefixTests.actualPhysicalBlock
              (publishedInput P J rewards C_star C_h eta rho) s hproc).uninformed) := by
          simpa [phys] using hin
        rw [dif_neg hmem]
      rw [contextCode, hactualWitness]
      simp [contextCodeFromW, w, hboundary, hinW]
  · have hguardW : ¬ ((wBoundary s j hj P J rewards C_star C_h eta w).crossing = none ∧
        (wBoundary s j hj P J rewards C_star C_h eta w).completed = s.val) := by
      intro hw
      have hwGen : (GeneratedBlockDrawLaw.generatedBoundary p s P.1 (P.2 J)
          rewards C_star C_h eta rho).crossing = none ∧
          (GeneratedBlockDrawLaw.generatedBoundary p s P.1 (P.2 J)
            rewards C_star C_h eta rho).completed = s.val := by
        rw [hboundary]
        exact hw
      apply hproc
      change (ReferenceInitializationRun.run x s.val).crossing = none ∧
        (ReferenceInitializationRun.run x s.val).completed = s.val
      have hx : x = GeneratedBlockDrawLaw.fixedReferenceInput p P.1 (P.2 J)
          rewards C_star C_h eta rho := by
        rfl
      rw [hx]
      simpa [GeneratedBlockDrawLaw.generatedBoundary] using hwGen
    have hactualWitness : actualFocalActiveWitness s j hj P J rewards C_star C_h eta rho = none := by
      simp only [actualFocalActiveWitness, x, dif_neg hproc]
    rw [contextCode, hactualWitness]
    simp [contextCodeFromW, w, hguardW]

/-- The context observation code is exactly the W-code of the original
private-coordinate split. -/
theorem contextCode_eq_contextCodeFromW
    (rho : ExtendedPrivateCoordinates p) :
    contextCode s j hj P J rewards C_star C_h eta rho =
      contextCodeFromW s j hj P J rewards C_star C_h eta
        (splitW s j hj rho) :=
  actualContextCode_eq_W s j hj P J rewards C_star C_h eta rho

/-- On a nonempty actual context cell, the existing output-side private-ID
guard returns exactly the original focal ID coordinate of the private split. -/
theorem contextCode_some_implies_activeID_eq_original
    (rho : ExtendedPrivateCoordinates p) (c : SourceContext p)
    (hc : contextCode s j hj P J rewards C_star C_h eta rho = some c)
    (u : Fin (A_id p)) :
    (activePrivateIDCodeOnPublishedOutput C_star C_h eta rewards J s
      (sourceFollower p j) (P, rho) = some u) ↔
      PrivateSourceStreams.privateIDScalarDraw p
        (BootstrapPrivateIDFibers.splitEquiv p s j hj rho).2.1 = u := by
  classical
  let x := publishedInput P J rewards C_star C_h eta rho
  cases hw : actualFocalActiveWitness s j hj P J rewards C_star C_h eta rho with
  | none => simp [contextCode, hw] at hc
  | some w =>
    have hctx : GeneratedBootstrapSupportContext.actualContextMap P J x s
        (actualLocalBlockOfWitness s j hj P J rewards C_star C_h eta rho w) = c := by
      simpa [contextCode, hw] using hc
    have hproc := w.processed
    let q := w.activeFollower
    have hsource : q.val.val = sourceFollower p j := w.focal_eq
    have hrem := GeneratedForwardPrefixTests.actualBlockRemaining x s hproc
    have hb := GeneratedPrivateIDFibers.generatedBoundary_eq_boundaryFromW
      p s j hj P J rewards C_star C_h eta rho
    let b := GeneratedForwardPrefixTests.actualBoundary x s
    have hcompleted : b.completed = s.val := hproc.2
    let raw := ReferenceInitializationRun.physical x b hrem
    have hindex := GeneratedForwardPrefixTests.actualBlockIndex x s hproc
    have hfocal : sourceFollower p j ∈ ReferenceInitializationRun.uninformed b := by
      have hm := q.val.property
      have hcast : (GeneratedForwardPrefixTests.actualPhysicalBlock x s hproc).uninformed =
          raw.uninformed := by
        change (hindex ▸ raw).uninformed = raw.uninformed
        exact GeneratedEligibleFamily.castPhysicalBlock_uninformed hindex raw
      change q.val.val ∈ (hindex ▸ raw).uninformed at hm
      rw [GeneratedEligibleFamily.castPhysicalBlock_uninformed hindex raw] at hm
      simpa [hsource, raw, ReferenceInitializationRun.physical,
        BootstrapPhysicalInput.blockInput, b, GeneratedForwardPrefixTests.actualBoundary] using hm
    have hfields := GeneratedPrivateIDFibers.physical_focal_fields
      p s j hj P J rewards C_star C_h eta rho b hrem hcompleted hfocal
    have hidCode : activePrivateIDCodeOnPublishedOutput C_star C_h eta rewards J s
        (sourceFollower p j) (P, rho) =
          some ((GeneratedForwardPrefixTests.actualPhysicalBlock x s hproc).privateId q.val) := by
      apply (GeneratedFalseForwardEvent.activePrivateIDCodeOnPublishedOutput_eq_some_iff_actualContext
        C_star C_h eta rewards J P rho s (sourceFollower p j)
        ((GeneratedForwardPrefixTests.actualPhysicalBlock x s hproc).privateId q.val)).2
      exact ⟨hproc, q, hsource, rfl⟩
    have hidPhysical :
        (GeneratedForwardPrefixTests.actualPhysicalBlock x s hproc).privateId q.val =
          PrivateSourceStreams.privateIDScalarDraw p (BootstrapPrivateIDFibers.splitEquiv p s j hj rho).2.1 := by
      have hthird := congrArg (fun d => d.2.2) hfields
      let qRaw : {i // i ∈ raw.uninformed} := ⟨sourceFollower p j, by
        simpa [raw, ReferenceInitializationRun.physical,
          BootstrapPhysicalInput.blockInput, b, GeneratedForwardPrefixTests.actualBoundary] using hfocal⟩
      have hq : q.val = GeneratedEligibleFamily.castPhysicalFollower hindex raw qRaw := by
        apply Subtype.ext
        exact hsource
      change (hindex ▸ raw).privateId q.val = _
      rw [hq, GeneratedEligibleFamily.castPhysicalFollower_privateID]
      exact hthird
    have hidCode' : activePrivateIDCodeOnPublishedOutput C_star C_h eta rewards J s
        (sourceFollower p j) (P, rho) =
          some ((GeneratedForwardPrefixTests.actualPhysicalBlock x s hproc).privateId q.val) := by
      simpa [hsource, x, publishedInput,
        GeneratedEligibleFamily.referenceInputOfPublishedOutput] using hidCode
    rw [hidCode', hidPhysical]
    simp

/-- Exact unnormalized context/ID/original-round-pair disintegration.
`H` is any measurable event of the retained W coordinates; no positive-cell
premise is used, and the ID and round pair are the original draws. -/
theorem context_id_originalRoundPair_measure
    (H : Set (Complement p s j ⟨j.val + 1, hj⟩)) (hH : MeasurableSet H)
    (D : Set ((BlockTime p s → BootstrapPrivateIDFibers.Scalar) × (BlockTime p s → BootstrapPrivateIDFibers.Scalar)))
    (hD : MeasurableSet D) (c : SourceContext p) (u : Fin (A_id p)) :
    extendedPrivateLaw p
      {rho | contextCode s j hj P J rewards C_star C_h eta rho = some c ∧
        (BootstrapPrivateIDFibers.splitEquiv p s j hj rho).1 ∈ H ∧
        activePrivateIDCodeOnPublishedOutput C_star C_h eta rewards J s
          (sourceFollower p j) (P, rho) = some u ∧
        originalRoundPair p s j hj rho ∈ D} =
      extendedPrivateLaw p
        {rho | contextCode s j hj P J rewards C_star C_h eta rho = some c ∧
          (BootstrapPrivateIDFibers.splitEquiv p s j hj rho).1 ∈ H} *
        ENNReal.ofReal (1 / (A_id p : ℝ)) * BootstrapPrivateIDFibers.roundPairLaw p s D := by
  classical
  let E := contextWCell s j hj P J rewards C_star C_h eta H c
  have hE : MeasurableSet E :=
    measurableSet_contextWCell s j hj P J rewards C_star C_h eta H hH c
  have hden : {rho | contextCode s j hj P J rewards C_star C_h eta rho = some c ∧
      (BootstrapPrivateIDFibers.splitEquiv p s j hj rho).1 ∈ H} =
      (fun rho => (BootstrapPrivateIDFibers.splitEquiv p s j hj rho).1) ⁻¹' E := by
    ext rho
    simp [E, contextWCell, contextCode_eq_contextCodeFromW,
      splitW, Set.mem_preimage]
  have hnum : {rho | contextCode s j hj P J rewards C_star C_h eta rho = some c ∧
      (BootstrapPrivateIDFibers.splitEquiv p s j hj rho).1 ∈ H ∧
      activePrivateIDCodeOnPublishedOutput C_star C_h eta rewards J s
        (sourceFollower p j) (P, rho) = some u ∧
      originalRoundPair p s j hj rho ∈ D} =
      {rho | (BootstrapPrivateIDFibers.splitEquiv p s j hj rho).1 ∈ E ∧
        PrivateSourceStreams.privateIDScalarDraw p
          (BootstrapPrivateIDFibers.splitEquiv p s j hj rho).2.1 = u ∧
        (BootstrapPrivateIDFibers.splitEquiv p s j hj rho).2.2 ∈ D} := by
    ext rho
    constructor
    · rintro ⟨hc, hH', hid, hD'⟩
      refine ⟨?_, ?_, ?_⟩
      · have hcW : contextCodeFromW s j hj P J rewards C_star C_h eta
            (splitW s j hj rho) = some c := by
          have hcodeEq := contextCode_eq_contextCodeFromW s j hj P J rewards C_star C_h eta rho
          rw [hcodeEq] at hc
          simpa [splitW] using hc
        simpa [E, contextWCell, splitW] using ⟨hcW, hH'⟩
      · exact (contextCode_some_implies_activeID_eq_original
          s j hj P J rewards C_star C_h eta rho c hc u).mp hid
      · simpa [GeneratedPrivateIDFibers.originalRoundPair_eq_split] using hD'
    · rintro ⟨hE', hid, hD'⟩
      have hcWH : contextCodeFromW s j hj P J rewards C_star C_h eta
          (splitW s j hj rho) = some c ∧
          (BootstrapPrivateIDFibers.splitEquiv p s j hj rho).1 ∈ H := by
        simpa [E, contextWCell, splitW] using hE'
      have hc : contextCode s j hj P J rewards C_star C_h eta rho = some c := by
        rw [contextCode_eq_contextCodeFromW s j hj P J rewards C_star C_h eta rho]
        exact hcWH.1
      have hcH : contextCode s j hj P J rewards C_star C_h eta rho = some c ∧
          (BootstrapPrivateIDFibers.splitEquiv p s j hj rho).1 ∈ H := ⟨hc, hcWH.2⟩
      refine ⟨hcH.1, hcH.2,
        (contextCode_some_implies_activeID_eq_original
          s j hj P J rewards C_star C_h eta rho c hcH.1 u).mpr hid, ?_⟩
      simpa [GeneratedPrivateIDFibers.originalRoundPair_eq_split] using hD'
  calc
    extendedPrivateLaw p
        {rho | contextCode s j hj P J rewards C_star C_h eta rho = some c ∧
          (BootstrapPrivateIDFibers.splitEquiv p s j hj rho).1 ∈ H ∧
          activePrivateIDCodeOnPublishedOutput C_star C_h eta rewards J s
            (sourceFollower p j) (P, rho) = some u ∧
          originalRoundPair p s j hj rho ∈ D} =
      extendedPrivateLaw p
        {rho | (BootstrapPrivateIDFibers.splitEquiv p s j hj rho).1 ∈ E ∧
          PrivateSourceStreams.privateIDScalarDraw p
            (BootstrapPrivateIDFibers.splitEquiv p s j hj rho).2.1 = u ∧
          (BootstrapPrivateIDFibers.splitEquiv p s j hj rho).2.2 ∈ D} := by rw [hnum]
    _ = complementLaw p s j ⟨j.val + 1, hj⟩ E *
          ENNReal.ofReal (1 / (A_id p : ℝ)) * BootstrapPrivateIDFibers.roundPairLaw p s D :=
      BootstrapPrivateIDFibers.split_cylinder_measure p s j hj E D u hE hD
    _ = extendedPrivateLaw p
          {rho | contextCode s j hj P J rewards C_star C_h eta rho = some c ∧
            (BootstrapPrivateIDFibers.splitEquiv p s j hj rho).1 ∈ H} *
          ENNReal.ofReal (1 / (A_id p : ℝ)) * BootstrapPrivateIDFibers.roundPairLaw p s D := by
      rw [hden]
      have hMP := (measurePreserving_fst.comp
        (BootstrapPrivateIDFibers.split_measurePreserving p s j hj))
      have hmeasure := hMP.measure_preimage hE.nullMeasurableSet
      have hmeasure' : extendedPrivateLaw p
          ((fun rho => (BootstrapPrivateIDFibers.splitEquiv p s j hj rho).1) ⁻¹' E) =
          complementLaw p s j ⟨j.val + 1, hj⟩ E := by
        simpa [Function.comp_def] using hmeasure
      rw [← hmeasure']

end Bandits.Support.GeneratedContextPrivateLaw

end
