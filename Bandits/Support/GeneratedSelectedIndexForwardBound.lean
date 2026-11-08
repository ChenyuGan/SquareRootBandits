/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.GeneratedFixedPublicForwardBound
public import Bandits.Support.ReferenceInitializationIndexMixture

/-!
# Actual false-forward bound for the original selected index

The selected event retains the coordinator's original private scalar and the
actual selected row in the published output. Its fixed-index sections are the
existing generated false-forward event, transported through the actual
reference run's scalar invariance.

Sources: `sources/zip4/manuscript/07_public_setup.tex:11,123-140`,
`sources/zip4/manuscript/appendix_b_communication.tex:294-367`, and
`sources/zip4/manuscript/08_main_theorem.tex:40,65-75`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.CompletePublicTable
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.ReferencePrelaunchFollower
open Bandits.Support.GeneratedEligibleFamily
open Bandits.Support.GeneratedForwardPrefixTests
open Bandits.Support.GeneratedFalseForwardEvent
open Bandits.Support.GeneratedFixedPublicForwardBound
open Bandits.Support.ReferenceInitializationRun
open Bandits.Support.BootstrapPhysicalInput
open scoped ENNReal Classical BigOperators

namespace Bandits.Support.GeneratedSelectedIndexForwardBound

variable {p : ConstructorDimensions.Parameters}

/-- The literal actual false-forward event using the original coordinator
scalar to select the row index. -/
def actualSelectedIndexAnyFalseForwardPrefixPassSet
    (C_star C_h : ℝ) (eta : LearningRate)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) :
    Set (PublishedOutput p × ExtendedPrivateCoordinates p) :=
  {z | (z.1, z.2) ∈ actualAnyFalseForwardPrefixPassSet C_star C_h eta rewards
    (PrivateSourceStreams.coordinatorIndex p z.2.1.2)}

/-- The private section of the selected-index event at one published output. -/
def actualSelectedIndexAnyFalseForwardPrefixPassSection
    (C_star C_h : ℝ) (eta : LearningRate)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (P : PublishedOutput p) :
    Set (ExtendedPrivateCoordinates p) :=
  {rho | (P, rho) ∈ actualSelectedIndexAnyFalseForwardPrefixPassSet
    C_star C_h eta rewards}

/-- The event section for one fixed external row index, using the same
published output and original private coordinates. -/
def fixedIndexActualAnyFalseForwardPrefixPassSection
    (C_star C_h : ℝ) (eta : LearningRate)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (P : PublishedOutput p) (j : Fin (M p)) :
    Set (ExtendedPrivateCoordinates p) :=
  {rho | (P, rho) ∈ actualAnyFalseForwardPrefixPassSet C_star C_h eta rewards j}

/-- The published-output input is the exact fixed-row adapter on `P.1`,
`P.2 j`, and the unchanged private point. -/
theorem referenceInputOfPublishedOutput_eq_fixedRowInput
    (C_star C_h : ℝ) (eta : LearningRate)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (P : PublishedOutput p) (j : Fin (M p)) (rho : ExtendedPrivateCoordinates p) :
    GeneratedEligibleFamily.referenceInputOfPublishedOutput C_star C_h eta rewards j
        (P, rho) =
      ReferenceInitializationIndexMixture.fixedRowInput p P.1 rewards C_star C_h eta
        (P.2 j) rho := rfl

/-- The actual stopped boundary at every block index is unchanged when only
the original coordinator scalar varies and the fixed row is held constant. -/
theorem referenceRun_eq_of_coordinatorScalar_change
    (C_star C_h : ℝ) (eta : LearningRate)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (P : PublishedOutput p) (j : Fin (M p)) (rho : ExtendedPrivateCoordinates p)
    (s : BootstrapPrivateRoundStreams.Scalar) (r : ℕ) :
    ReferenceInitializationRun.run
        (GeneratedEligibleFamily.referenceInputOfPublishedOutput C_star C_h eta rewards j
          (P, ReferenceInitializationIndexMixture.withCoordinatorScalar rho s)) r =
      ReferenceInitializationRun.run
        (GeneratedEligibleFamily.referenceInputOfPublishedOutput C_star C_h eta rewards j
          (P, rho)) r := by
  rw [referenceInputOfPublishedOutput_eq_fixedRowInput,
    referenceInputOfPublishedOutput_eq_fixedRowInput]
  exact ReferenceInitializationIndexMixture.fixedRow_run_eq_of_coordinatorScalar_change
    p P.1 rewards C_star C_h eta (P.2 j) rho s r

/-- A block is processed at the same indices after changing the coordinator
scalar, as witnessed by the exact existing run equality. -/
theorem processesBlock_iff_of_coordinatorScalar_change
    (C_star C_h : ℝ) (eta : LearningRate)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (P : PublishedOutput p) (j : Fin (M p)) (rho : ExtendedPrivateCoordinates p)
    (scalar : BootstrapPrivateRoundStreams.Scalar) (block : Fin (n_boot p)) :
    processesBlock
        (GeneratedEligibleFamily.referenceInputOfPublishedOutput C_star C_h eta rewards j
          (P, ReferenceInitializationIndexMixture.withCoordinatorScalar rho scalar)) block ↔
      processesBlock
        (GeneratedEligibleFamily.referenceInputOfPublishedOutput C_star C_h eta rewards j
          (P, rho)) block := by
  simp only [GeneratedForwardPrefixTests.processesBlock]
  rw [referenceRun_eq_of_coordinatorScalar_change C_star C_h eta rewards P j rho scalar
    block.val]

private theorem actualPhysicalBlock_eq_of_boundary
    (x : ReferenceInitializationRun.Input p) (b : ReferenceInitializationRun.Boundary p)
    (h : b.completed < n_boot p) (block : Fin (n_boot p))
    (hp : processesBlock x block)
    (hb : GeneratedForwardPrefixTests.actualBoundary x block = b)
    (hs : ReferenceInitializationRun.nextBlock b h = block) :
    GeneratedForwardPrefixTests.actualPhysicalBlock x block hp =
      hs ▸ ReferenceInitializationRun.physical x b h := by
  cases hb
  rfl

private theorem referencePhysical_eq_of_coordinatorScalar_change
    (C_star C_h : ℝ) (eta : LearningRate)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (P : PublishedOutput p) (j : Fin (M p)) (rho : ExtendedPrivateCoordinates p)
    (scalar : BootstrapPrivateRoundStreams.Scalar)
    (b : ReferenceInitializationRun.Boundary p)
    (h : b.completed < n_boot p) :
    ReferenceInitializationRun.physical
        (GeneratedEligibleFamily.referenceInputOfPublishedOutput C_star C_h eta rewards j
          (P, ReferenceInitializationIndexMixture.withCoordinatorScalar rho scalar)) b h =
      ReferenceInitializationRun.physical
        (GeneratedEligibleFamily.referenceInputOfPublishedOutput C_star C_h eta rewards j
          (P, rho)) b h := by
  cases rho with
  | mk privateCoordinates extra =>
    cases privateCoordinates with
    | mk blockInputs oldScalar =>
      rfl

private theorem actualPhysicalBlock_eq_of_coordinatorScalar_change
    (C_star C_h : ℝ) (eta : LearningRate)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (P : PublishedOutput p) (j : Fin (M p)) (rho : ExtendedPrivateCoordinates p)
    (scalar : BootstrapPrivateRoundStreams.Scalar) (block : Fin (n_boot p))
    (hchanged : processesBlock
      (GeneratedEligibleFamily.referenceInputOfPublishedOutput C_star C_h eta rewards j
        (P, ReferenceInitializationIndexMixture.withCoordinatorScalar rho scalar)) block)
    (hfixed : processesBlock
      (GeneratedEligibleFamily.referenceInputOfPublishedOutput C_star C_h eta rewards j
        (P, rho)) block) :
    GeneratedForwardPrefixTests.actualPhysicalBlock
        (GeneratedEligibleFamily.referenceInputOfPublishedOutput C_star C_h eta rewards j
          (P, ReferenceInitializationIndexMixture.withCoordinatorScalar rho scalar)) block
        hchanged =
      GeneratedForwardPrefixTests.actualPhysicalBlock
        (GeneratedEligibleFamily.referenceInputOfPublishedOutput C_star C_h eta rewards j
          (P, rho)) block hfixed := by
  let xchanged := GeneratedEligibleFamily.referenceInputOfPublishedOutput C_star C_h eta rewards j
    (P, ReferenceInitializationIndexMixture.withCoordinatorScalar rho scalar)
  let xfixed := GeneratedEligibleFamily.referenceInputOfPublishedOutput C_star C_h eta rewards j
    (P, rho)
  have hrun : ReferenceInitializationRun.run xchanged block.val =
      ReferenceInitializationRun.run xfixed block.val := by
    simpa [xchanged, xfixed] using
      referenceRun_eq_of_coordinatorScalar_change C_star C_h eta rewards P j rho
        scalar block.val
  let b := GeneratedForwardPrefixTests.actualBoundary xchanged block
  have hb : GeneratedForwardPrefixTests.actualBoundary xfixed block = b := hrun.symm
  have hremChanged := GeneratedForwardPrefixTests.actualBlockRemaining xchanged block hchanged
  have hremFixed : b.completed < n_boot p :=
    hb ▸ GeneratedForwardPrefixTests.actualBlockRemaining xfixed block hfixed
  have hsChanged := GeneratedForwardPrefixTests.actualBlockIndex xchanged block hchanged
  have hsFixed : ReferenceInitializationRun.nextBlock b hremFixed = block := by
    apply Fin.ext
    calc
      b.completed = (GeneratedForwardPrefixTests.actualBoundary xfixed block).completed :=
        congrArg ReferenceInitializationRun.Boundary.completed hb.symm
      _ = block.val := hfixed.2
  have hphysicalChanged := actualPhysicalBlock_eq_of_boundary xchanged b hremChanged block
    hchanged rfl hsChanged
  have hphysicalFixed := actualPhysicalBlock_eq_of_boundary xfixed b hremFixed block
    hfixed hb hsFixed
  have hraw := referencePhysical_eq_of_coordinatorScalar_change C_star C_h eta rewards P j rho
    scalar b hremFixed
  have hindexEq : hsChanged = hsFixed := Subsingleton.elim _ _
  calc
    _ = hsChanged ▸ ReferenceInitializationRun.physical xchanged b hremFixed := hphysicalChanged
    _ = hsChanged ▸ ReferenceInitializationRun.physical xfixed b hremFixed :=
      congrArg (fun v => hsChanged ▸ v) hraw
    _ = hsFixed ▸ ReferenceInitializationRun.physical xfixed b hremFixed := by
      rw [hindexEq]
    _ = _ := hphysicalFixed.symm

private theorem activeIncomingFollower_val_val_cast
    {block : Fin (n_boot p)}
    {left right : BootstrapPhysicalBlock.Input p block} (e : left = right)
    (j : {j : {i // i ∈ left.uninformed} // left.active j = true}) :
    (e ▸ j).val.val = j.val.val := by
  cases e
  rfl

private abbrev PhysicalActiveIncomingFollower {block : Fin (n_boot p)}
    (phys : BootstrapPhysicalBlock.Input p block) :=
  {j : {i // i ∈ phys.uninformed} // phys.active j = true}

/-- The existing generated prefix predicate exposed on the exact physical
block and selected follower that it reads. -/
private def falseCandidateEligibleOnPhysical {block : Fin (n_boot p)}
    (phys : BootstrapPhysicalBlock.Input p block)
    (j : PhysicalActiveIncomingFollower phys) (rows : CompleteRows p)
    (v : Fin (M p)) (t : Fin p.T) : Prop :=
  t ∈ BootstrapDimensions.calendarBlock p block ∧
    phys.active j.val = true ∧
    phys.ids (phys.privateId j.val) t = false ∧
    PublicDiscreteDraws.slotDraw ((rows v).2 t).1 = PublicDiscreteDraws.dataSlot ∧
    0 < (ReferenceInitializationRun.ownEntry phys
      (PublicDiscreteDraws.followerPlayer p.two_le_m j.val.val) t).2.val.val

private def falseCandidatePassesOnPhysical {block : Fin (n_boot p)}
    (phys : BootstrapPhysicalBlock.Input p block)
    (j : PhysicalActiveIncomingFollower phys) (rows : CompleteRows p)
    (J : Fin (M p)) (v : FalseRowSliceFactorization.FalseRow p J) : Prop :=
  ForwardPrefixSlice.prefixPasses
    ((BootstrapDimensions.calendarBlock p block).filter
      (falseCandidateEligibleOnPhysical phys j rows v.1)).sort
    (fun t => (rows v.1).1 (phys.privateId j.val) t) (q_dec p)

private theorem falseCandidatePasses_eq_on_actualPhysicalBlock
    (x : ReferenceInitializationRun.Input p) (block : Fin (n_boot p))
    (h : processesBlock x block) (j : ActiveIncomingFollower x block h)
    (rows : CompleteRows p) (J : Fin (M p))
    (v : FalseRowSliceFactorization.FalseRow p J) :
    GeneratedForwardPrefixTests.falseCandidatePasses x block h j rows J v =
      falseCandidatePassesOnPhysical
        (GeneratedForwardPrefixTests.actualPhysicalBlock x block h) j rows J v := by
  let phys := GeneratedForwardPrefixTests.actualPhysicalBlock x block h
  have hset : GeneratedForwardPrefixTests.eligibleSet x block h j rows v.1 =
      (BootstrapDimensions.calendarBlock p block).filter
        (falseCandidateEligibleOnPhysical phys j rows v.1) := by
    ext t
    simp only [GeneratedForwardPrefixTests.eligibleSet, Finset.mem_filter,
      GeneratedForwardPrefixTests.candidateEligible, falseCandidateEligibleOnPhysical]
    rfl
  have hslice : GeneratedForwardPrefixTests.candidateForwardSlice x block h j rows v.1 =
      (fun t => (rows v.1).1 (phys.privateId j.val) t) := by
    funext t
    rfl
  unfold GeneratedForwardPrefixTests.falseCandidatePasses
  rw [GeneratedForwardPrefixTests.chronologicalEligibleTimes, hset, hslice]
  rfl

private theorem falseCandidatePassesOnPhysical_iff_of_eq
    {block : Fin (n_boot p)}
    (left right : BootstrapPhysicalBlock.Input p block) (hphysical : left = right)
    (jl : PhysicalActiveIncomingFollower left) (jr : PhysicalActiveIncomingFollower right)
    (rows : CompleteRows p) (J : Fin (M p))
    (v : FalseRowSliceFactorization.FalseRow p J)
    (hindex : jl.val.val = jr.val.val) :
    falseCandidatePassesOnPhysical left jl rows J v ↔
      falseCandidatePassesOnPhysical right jr rows J v := by
  cases hphysical
  have hinner : jl.val = jr.val := Subtype.ext hindex
  have hactive : jl = jr := Subtype.ext hinner
  cases hactive
  rfl

private theorem existsFalseForwardPrefixPass_of_physical_eq
    (x y : ReferenceInitializationRun.Input p) (block : Fin (n_boot p))
    (hx : processesBlock x block) (hy : processesBlock y block)
    (jx : ActiveIncomingFollower x block hx) (jy : ActiveIncomingFollower y block hy)
    (rows : CompleteRows p) (J : Fin (M p))
    (hphysical : GeneratedForwardPrefixTests.actualPhysicalBlock x block hx =
      GeneratedForwardPrefixTests.actualPhysicalBlock y block hy)
    (hindex : jx.val.val = jy.val.val) :
    GeneratedForwardPrefixTests.existsFalseForwardPrefixPass x block hx jx rows J →
      GeneratedForwardPrefixTests.existsFalseForwardPrefixPass y block hy jy rows J := by
  intro hpass
  change ∃ v : FalseRowSliceFactorization.FalseRow p J,
    GeneratedForwardPrefixTests.falseCandidatePasses x block hx jx rows J v at hpass
  change ∃ v : FalseRowSliceFactorization.FalseRow p J,
    GeneratedForwardPrefixTests.falseCandidatePasses y block hy jy rows J v
  rcases hpass with ⟨v, hpass⟩
  refine ⟨v, ?_⟩
  rw [falseCandidatePasses_eq_on_actualPhysicalBlock] at hpass ⊢
  exact (falseCandidatePassesOnPhysical_iff_of_eq
    (GeneratedForwardPrefixTests.actualPhysicalBlock x block hx)
    (GeneratedForwardPrefixTests.actualPhysicalBlock y block hy)
    hphysical jx jy rows J v hindex).mp hpass

private theorem existsFalseForwardPrefixPass_iff_of_physical_eq
    (x y : ReferenceInitializationRun.Input p) (block : Fin (n_boot p))
    (hx : processesBlock x block) (hy : processesBlock y block)
    (jx : ActiveIncomingFollower x block hx) (jy : ActiveIncomingFollower y block hy)
    (rows : CompleteRows p) (J : Fin (M p))
    (hphysical : GeneratedForwardPrefixTests.actualPhysicalBlock x block hx =
      GeneratedForwardPrefixTests.actualPhysicalBlock y block hy)
    (hindex : jx.val.val = jy.val.val) :
    GeneratedForwardPrefixTests.existsFalseForwardPrefixPass x block hx jx rows J ↔
      GeneratedForwardPrefixTests.existsFalseForwardPrefixPass y block hy jy rows J := by
  constructor
  · exact existsFalseForwardPrefixPass_of_physical_eq x y block hx hy jx jy rows J
      hphysical hindex
  · exact existsFalseForwardPrefixPass_of_physical_eq y x block hy hx jy jx rows J
      hphysical.symm hindex.symm

/-- Membership in the original fixed-index event is invariant under changing
only the coordinator scalar. The proof transports the processed-block and
active-follower witnesses through the actual run and physical block. -/
theorem actualAnyFalseForwardPrefixPass_mem_withCoordinatorScalar_iff
    (C_star C_h : ℝ) (eta : LearningRate)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (P : PublishedOutput p) (J : Fin (M p)) (rho : ExtendedPrivateCoordinates p)
    (scalar : BootstrapPrivateRoundStreams.Scalar) :
    ((P, ReferenceInitializationIndexMixture.withCoordinatorScalar rho scalar) ∈
        actualAnyFalseForwardPrefixPassSet C_star C_h eta rewards J) ↔
      ((P, rho) ∈ actualAnyFalseForwardPrefixPassSet C_star C_h eta rewards J) := by
  classical
  rw [GeneratedFalseForwardEvent.actualAnyFalseForwardPrefixPassSet]
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨block, i, hchangedBlock, jchanged, hindexChanged, htestChanged⟩
    let xchanged := GeneratedEligibleFamily.referenceInputOfPublishedOutput C_star C_h eta
      rewards J (P, ReferenceInitializationIndexMixture.withCoordinatorScalar rho scalar)
    let xfixed := GeneratedEligibleFamily.referenceInputOfPublishedOutput C_star C_h eta
      rewards J (P, rho)
    let hfixed : processesBlock xfixed block :=
      (processesBlock_iff_of_coordinatorScalar_change C_star C_h eta rewards P J rho scalar
        block).mp hchangedBlock
    have hphysical := actualPhysicalBlock_eq_of_coordinatorScalar_change C_star C_h eta
      rewards P J rho scalar block hchangedBlock hfixed
    let jfixed : ActiveIncomingFollower xfixed block hfixed := by
      change {j : {i // i ∈
          (GeneratedForwardPrefixTests.actualPhysicalBlock xfixed block hfixed).uninformed} //
        (GeneratedForwardPrefixTests.actualPhysicalBlock xfixed block hfixed).active j = true}
      exact hphysical ▸ jchanged
    have hindex : jfixed.val.val = i := by
      calc
        jfixed.val.val = jchanged.val.val :=
          activeIncomingFollower_val_val_cast hphysical jchanged
        _ = i := hindexChanged
    have hindexTransport : jchanged.val.val = jfixed.val.val := by
      exact hindexChanged.trans hindex.symm
    have htest := (existsFalseForwardPrefixPass_iff_of_physical_eq xchanged xfixed block
      hchangedBlock hfixed jchanged jfixed P.2 J hphysical hindexTransport).mp htestChanged
    exact ⟨block, i, hfixed, jfixed, hindex, htest⟩
  · rintro ⟨block, i, hfixedBlock, jfixed, hindexFixed, htestFixed⟩
    let xchanged := GeneratedEligibleFamily.referenceInputOfPublishedOutput C_star C_h eta
      rewards J (P, ReferenceInitializationIndexMixture.withCoordinatorScalar rho scalar)
    let xfixed := GeneratedEligibleFamily.referenceInputOfPublishedOutput C_star C_h eta
      rewards J (P, rho)
    let hchanged : processesBlock xchanged block :=
      (processesBlock_iff_of_coordinatorScalar_change C_star C_h eta rewards P J rho scalar
        block).mpr hfixedBlock
    have hphysical := actualPhysicalBlock_eq_of_coordinatorScalar_change C_star C_h eta
      rewards P J rho scalar block hchanged hfixedBlock
    let jchanged : ActiveIncomingFollower xchanged block hchanged := by
      change {j : {i // i ∈
          (GeneratedForwardPrefixTests.actualPhysicalBlock xchanged block hchanged).uninformed} //
        (GeneratedForwardPrefixTests.actualPhysicalBlock xchanged block hchanged).active j = true}
      exact hphysical.symm ▸ jfixed
    have hindex : jchanged.val.val = i := by
      calc
        jchanged.val.val = jfixed.val.val :=
          activeIncomingFollower_val_val_cast hphysical.symm jfixed
        _ = i := hindexFixed
    have hindexTransport : jchanged.val.val = jfixed.val.val := by
      exact hindex.trans hindexFixed.symm
    have htest := (existsFalseForwardPrefixPass_iff_of_physical_eq xchanged xfixed block
      hchanged hfixedBlock jchanged jfixed P.2 J hphysical hindexTransport).mpr htestFixed
    exact ⟨block, i, hchanged, jchanged, hindex, htest⟩

/-- The literal joint event is measurable by its finite fixed-index sections. -/
theorem measurableSet_actualSelectedIndexAnyFalseForwardPrefixPassSet
    (C_star C_h : ℝ) (eta : LearningRate)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) :
    MeasurableSet (actualSelectedIndexAnyFalseForwardPrefixPassSet
      (p := p) C_star C_h eta rewards) := by
  classical
  rw [actualSelectedIndexAnyFalseForwardPrefixPassSet]
  have hparts (j : Fin (M p)) :
      MeasurableSet
        ({z : PublishedOutput p × ExtendedPrivateCoordinates p |
          PrivateSourceStreams.coordinatorIndex p z.2.1.2 = j} ∩
         {z | (z.1, z.2) ∈ actualAnyFalseForwardPrefixPassSet
           C_star C_h eta rewards j}) := by
    apply MeasurableSet.inter
    · have hset :
          {z : PublishedOutput p × ExtendedPrivateCoordinates p |
            PrivateSourceStreams.coordinatorIndex p z.2.1.2 = j} =
            (fun z : PublishedOutput p × ExtendedPrivateCoordinates p =>
              PrivateSourceStreams.coordinatorIndex p z.2.1.2) ⁻¹' {j} := by
        ext z
        simp
      rw [hset]
      exact ((PrivateSourceStreams.measurable_coordinatorIndex p).comp
        (measurable_snd.comp (measurable_fst.comp measurable_snd)))
        (measurableSet_singleton j)
    · exact (GeneratedFalseForwardEvent.measurableSet_actualAnyFalseForwardPrefixPassSet
        C_star C_h eta rewards j).preimage
        (measurable_fst.prodMk measurable_snd)
  have hdecomp :
      {z : PublishedOutput p × ExtendedPrivateCoordinates p |
        (z.1, z.2) ∈ actualAnyFalseForwardPrefixPassSet C_star C_h eta rewards
          (PrivateSourceStreams.coordinatorIndex p z.2.1.2)} =
      ⋃ j : Fin (M p),
        ({z | PrivateSourceStreams.coordinatorIndex p z.2.1.2 = j} ∩
         {z | (z.1, z.2) ∈ actualAnyFalseForwardPrefixPassSet
           C_star C_h eta rewards j}) := by
    ext z
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · intro h
      exact ⟨PrivateSourceStreams.coordinatorIndex p z.2.1.2, rfl, h⟩
    · rintro ⟨j, hj, h⟩
      simpa [hj] using h
  rw [hdecomp]
  exact MeasurableSet.iUnion hparts

private theorem scalarInvariant_event_atom_factorization
    (E : Set (ExtendedPrivateCoordinates p)) (hE : MeasurableSet E)
    (hinv : ∀ (q : ReferenceInitializationIndexMixture.PrivateResidual p)
      (s t : ReferenceInitializationIndexMixture.Scalar),
        ReferenceInitializationIndexMixture.insertScalarResidual (s, q) ∈ E ↔
          ReferenceInitializationIndexMixture.insertScalarResidual (t, q) ∈ E)
    (j : Fin (M p)) :
    BootstrapPrivateRoundStreams.extendedPrivateLaw p
        {rho | PrivateSourceStreams.coordinatorIndex p rho.1.2 = j ∧ rho ∈ E} =
      ENNReal.ofReal (1 / (M p : ℝ)) *
        BootstrapPrivateRoundStreams.extendedPrivateLaw p E := by
  classical
  let mu := BootstrapPrivateRoundStreams.extendedPrivateLaw p
  let s₀ : ReferenceInitializationIndexMixture.Scalar := ⟨0, by norm_num⟩
  let atom : Set ReferenceInitializationIndexMixture.Scalar :=
    {s | PrivateSourceStreams.coordinatorIndex p s = j}
  let residualEvent : Set (ReferenceInitializationIndexMixture.PrivateResidual p) :=
    {q | ReferenceInitializationIndexMixture.insertScalarResidual (s₀, q) ∈ E}
  have hJ : MeasurableSet atom := by
    have hset : atom = PrivateSourceStreams.coordinatorIndex p ⁻¹' {j} := by
      ext s
      simp [atom]
    rw [hset]
    exact PrivateSourceStreams.measurable_coordinatorIndex p (measurableSet_singleton j)
  have hrestore : Measurable
      (fun q : ReferenceInitializationIndexMixture.PrivateResidual p =>
        ReferenceInitializationIndexMixture.insertScalarResidual (s₀, q)) := by
    exact (measurable_fst.prodMk measurable_const).prodMk measurable_snd
  have hresidualEvent : MeasurableSet residualEvent := hE.preimage hrestore
  have hrect : MeasurableSet (atom ×ˢ residualEvent) := hJ.prod hresidualEvent
  have hpre :
      ReferenceInitializationIndexMixture.scalarAndResidual (p := p) ⁻¹'
          (atom ×ˢ residualEvent) =
        {rho : ExtendedPrivateCoordinates p |
          PrivateSourceStreams.coordinatorIndex p rho.1.2 = j ∧ rho ∈ E} := by
    ext rho
    rcases rho with ⟨⟨blocks, scalar⟩, extra⟩
    simp only [Set.mem_preimage, Set.mem_prod, atom, residualEvent,
      ReferenceInitializationIndexMixture.scalarAndResidual,
      ReferenceInitializationIndexMixture.insertScalarResidual, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hindex, hevent⟩
      exact ⟨hindex, (hinv (blocks, extra) scalar s₀).mpr hevent⟩
    · rintro ⟨hindex, he⟩
      exact ⟨hindex, (hinv (blocks, extra) scalar s₀).mp he⟩
  have hpreRight :
      ReferenceInitializationIndexMixture.scalarAndResidual (p := p) ⁻¹'
          (Set.univ ×ˢ residualEvent) = E := by
    ext rho
    rcases rho with ⟨⟨blocks, scalar⟩, extra⟩
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ, true_and,
      residualEvent, ReferenceInitializationIndexMixture.scalarAndResidual,
      ReferenceInitializationIndexMixture.insertScalarResidual, Set.mem_ofPred_eq]
    exact ⟨fun hevent => (hinv (blocks, extra) scalar s₀).mpr hevent,
      fun he => (hinv (blocks, extra) scalar s₀).mp he⟩
  have hmp := ReferenceInitializationIndexMixture.measurePreserving_scalarAndResidual p
  have hleft : mu
      {rho | PrivateSourceStreams.coordinatorIndex p rho.1.2 = j ∧ rho ∈ E} =
        ContinuousCategorical.uniform atom *
          ReferenceInitializationIndexMixture.privateResidualLaw p residualEvent := by
    calc
      mu {rho | PrivateSourceStreams.coordinatorIndex p rho.1.2 = j ∧ rho ∈ E} =
          mu.map (ReferenceInitializationIndexMixture.scalarAndResidual (p := p))
            (atom ×ˢ residualEvent) := by
              rw [← hpre, Measure.map_apply hmp.measurable hrect]
      _ = ContinuousCategorical.uniform atom *
            ReferenceInitializationIndexMixture.privateResidualLaw p residualEvent := by
              rw [hmp.map_eq, Measure.prod_prod]
  have hatom : ContinuousCategorical.uniform atom =
      ENNReal.ofReal (1 / (M p : ℝ)) := by
    have hset : atom = PrivateSourceStreams.coordinatorIndex p ⁻¹' {j} := by
      ext s
      simp [atom]
    rw [hset]
    exact PrivateSourceStreams.coordinatorIndex_uniform_atom p j
  have hright : mu E =
      ReferenceInitializationIndexMixture.privateResidualLaw p residualEvent := by
    calc
      mu E = mu.map (ReferenceInitializationIndexMixture.scalarAndResidual (p := p))
          (Set.univ ×ˢ residualEvent) := by
            rw [← hpreRight, Measure.map_apply hmp.measurable
              (MeasurableSet.univ.prod hresidualEvent)]
      _ = ReferenceInitializationIndexMixture.privateResidualLaw p residualEvent := by
            rw [hmp.map_eq, Measure.prod_prod, ContinuousCategorical.uniform_univ, one_mul]
  rw [hleft, hatom, ← hright]

/-- For one fixed external row index, its unchanged actual event section has
exactly the uniform mass of the original private scalar atom. -/
theorem fixedIndexActualAnyFalseForwardPrefixPassSection_atom_factorization
    (C_star C_h : ℝ) (eta : LearningRate)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (P : PublishedOutput p) (j : Fin (M p)) :
    BootstrapPrivateRoundStreams.extendedPrivateLaw p
        {rho | PrivateSourceStreams.coordinatorIndex p rho.1.2 = j ∧
          rho ∈ fixedIndexActualAnyFalseForwardPrefixPassSection
            C_star C_h eta rewards P j} =
      ENNReal.ofReal (1 / (M p : ℝ)) *
        BootstrapPrivateRoundStreams.extendedPrivateLaw p
          (fixedIndexActualAnyFalseForwardPrefixPassSection
            C_star C_h eta rewards P j) := by
  let E := fixedIndexActualAnyFalseForwardPrefixPassSection
    (p := p) C_star C_h eta rewards P j
  have hE : MeasurableSet E := by
    change MeasurableSet
      {rho | (P, rho) ∈ actualAnyFalseForwardPrefixPassSet C_star C_h eta rewards j}
    exact (GeneratedFalseForwardEvent.measurableSet_actualAnyFalseForwardPrefixPassSet
      C_star C_h eta rewards j).preimage (measurable_const.prodMk measurable_id)
  have hinv : ∀ (q : ReferenceInitializationIndexMixture.PrivateResidual p)
      (s t : ReferenceInitializationIndexMixture.Scalar),
        ReferenceInitializationIndexMixture.insertScalarResidual (s, q) ∈ E ↔
          ReferenceInitializationIndexMixture.insertScalarResidual (t, q) ∈ E := by
    intro q s t
    change (P, ReferenceInitializationIndexMixture.insertScalarResidual (s, q)) ∈
        actualAnyFalseForwardPrefixPassSet C_star C_h eta rewards j ↔
      (P, ReferenceInitializationIndexMixture.insertScalarResidual (t, q)) ∈
        actualAnyFalseForwardPrefixPassSet C_star C_h eta rewards j
    simpa only [ReferenceInitializationIndexMixture.insertScalarResidual,
      ReferenceInitializationIndexMixture.withCoordinatorScalar] using
      (actualAnyFalseForwardPrefixPass_mem_withCoordinatorScalar_iff
        C_star C_h eta rewards P j
        (ReferenceInitializationIndexMixture.insertScalarResidual (s, q)) t).symm
  simpa only [E] using scalarInvariant_event_atom_factorization E hE hinv j

/-- The original private-J event is the exact finite uniform average of its
fixed-index sections under the same extended private law. -/
theorem actualSelectedIndexAnyFalseForwardPrefixPassSection_real_eq_uniform_average
    (C_star C_h : ℝ) (eta : LearningRate)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (P : PublishedOutput p) :
    (BootstrapPrivateRoundStreams.extendedPrivateLaw p).real
        (actualSelectedIndexAnyFalseForwardPrefixPassSection
          C_star C_h eta rewards P) =
      (1 / (M p : ℝ)) *
        ∑ j : Fin (M p),
          (BootstrapPrivateRoundStreams.extendedPrivateLaw p).real
            (fixedIndexActualAnyFalseForwardPrefixPassSection
              C_star C_h eta rewards P j) := by
  classical
  let mu := BootstrapPrivateRoundStreams.extendedPrivateLaw p
  let fixedSection (j : Fin (M p)) :=
    fixedIndexActualAnyFalseForwardPrefixPassSection
      (p := p) C_star C_h eta rewards P j
  let part (j : Fin (M p)) : Set (ExtendedPrivateCoordinates p) :=
    {rho | PrivateSourceStreams.coordinatorIndex p rho.1.2 = j ∧ rho ∈ fixedSection j}
  have hindex : Measurable (fun rho : ExtendedPrivateCoordinates p =>
      PrivateSourceStreams.coordinatorIndex p rho.1.2) :=
    (PrivateSourceStreams.measurable_coordinatorIndex p).comp
      (measurable_snd.comp measurable_fst)
  have hparts : ∀ j, MeasurableSet (part j) := by
    intro j
    exact (hindex (measurableSet_singleton j)).inter
      ((GeneratedFalseForwardEvent.measurableSet_actualAnyFalseForwardPrefixPassSet
        C_star C_h eta rewards j).preimage (measurable_const.prodMk measurable_id))
  have hdisj : Pairwise (fun j k => Disjoint (part j) (part k)) := by
    intro j k hjk
    apply Set.disjoint_left.mpr
    intro rho hrj hrk
    exact hjk (hrj.1.symm.trans hrk.1)
  have hunion : actualSelectedIndexAnyFalseForwardPrefixPassSection
      C_star C_h eta rewards P = ⋃ j : Fin (M p), part j := by
    ext rho
    simp only [actualSelectedIndexAnyFalseForwardPrefixPassSection,
      actualSelectedIndexAnyFalseForwardPrefixPassSet, Set.mem_ofPred_eq,
      Set.mem_iUnion, part, fixedSection]
    constructor
    · intro h
      exact ⟨PrivateSourceStreams.coordinatorIndex p rho.1.2, rfl, h⟩
    · rintro ⟨j, hindex, h⟩
      simpa [hindex, fixedIndexActualAnyFalseForwardPrefixPassSection] using h
  have hmeasure : mu
      (actualSelectedIndexAnyFalseForwardPrefixPassSection
        C_star C_h eta rewards P) =
      ∑ j : Fin (M p), ENNReal.ofReal (1 / (M p : ℝ)) * mu (fixedSection j) := by
    calc
      _ = mu (⋃ j : Fin (M p), part j) := by rw [hunion]
      _ = ∑' j : Fin (M p), mu (part j) := measure_iUnion hdisj hparts
      _ = ∑ j : Fin (M p), mu (part j) := by rw [tsum_fintype]
      _ = ∑ j : Fin (M p), ENNReal.ofReal (1 / (M p : ℝ)) * mu (fixedSection j) := by
        apply Finset.sum_congr rfl
        intro j hj
        exact fixedIndexActualAnyFalseForwardPrefixPassSection_atom_factorization
          C_star C_h eta rewards P j
  have hsumFinite : ∀ j : Fin (M p),
      ENNReal.ofReal (1 / (M p : ℝ)) * mu (fixedSection j) ≠ ∞ := by
    intro j
    apply ENNReal.mul_ne_top
    · exact ENNReal.ofReal_ne_top
    · exact measure_ne_top mu (fixedSection j)
  have hcoeff : 0 ≤ (1 / (M p : ℝ)) := by positivity
  change (mu (actualSelectedIndexAnyFalseForwardPrefixPassSection
      C_star C_h eta rewards P)).toReal =
    (1 / (M p : ℝ)) * ∑ j : Fin (M p), (mu (fixedSection j)).toReal
  rw [hmeasure, ENNReal.toReal_sum (fun j hj => hsumFinite j)]
  calc
    ∑ j : Fin (M p),
        (ENNReal.ofReal (1 / (M p : ℝ)) * mu (fixedSection j)).toReal =
      ∑ j : Fin (M p), (1 / (M p : ℝ)) * (mu (fixedSection j)).toReal := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hcoeff]
    _ = (1 / (M p : ℝ)) * ∑ j : Fin (M p), (mu (fixedSection j)).toReal := by
      rw [Finset.mul_sum]

/-- The exact selected-index average is bounded by the accepted fixed-output
false-forward estimate, with no union factor. -/
theorem actualSelectedIndexAnyFalseForwardPrefixPassSection_real_le_inv_Bboot
    (C_star C_h : ℝ) (eta : LearningRate)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (P : PublishedOutput p)
    (hP : P ∈ BootstrapContextPassingTail.commonNumericPublicGoodSet p) :
    (BootstrapPrivateRoundStreams.extendedPrivateLaw p).real
        (actualSelectedIndexAnyFalseForwardPrefixPassSection
          C_star C_h eta rewards P) ≤ 1 / (B_boot p : ℝ) := by
  have hfixed (j : Fin (M p)) :
      (BootstrapPrivateRoundStreams.extendedPrivateLaw p).real
          (fixedIndexActualAnyFalseForwardPrefixPassSection
            C_star C_h eta rewards P j) ≤ 1 / (B_boot p : ℝ) :=
    fixedOutput_actualAnyFalseForwardPrefixPass_measure_le_inv_Bboot
      C_star C_h eta rewards P j hP
  have hsum :
      (∑ j : Fin (M p),
        (BootstrapPrivateRoundStreams.extendedPrivateLaw p).real
          (fixedIndexActualAnyFalseForwardPrefixPassSection
            C_star C_h eta rewards P j)) ≤
      ∑ _j : Fin (M p), (1 / (B_boot p : ℝ)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact hfixed j
  have hcoeff : 0 ≤ (1 / (M p : ℝ)) := by positivity
  have hM : 0 < (M p : ℝ) := Nat.cast_pos.mpr (ConstructorDimensions.M_pos p)
  have hB : 0 < (B_boot p : ℝ) :=
    Nat.cast_pos.mpr (BootstrapDimensions.B_boot_pos p)
  calc
    _ = (1 / (M p : ℝ)) *
          ∑ j : Fin (M p),
            (BootstrapPrivateRoundStreams.extendedPrivateLaw p).real
              (fixedIndexActualAnyFalseForwardPrefixPassSection
                C_star C_h eta rewards P j) :=
      actualSelectedIndexAnyFalseForwardPrefixPassSection_real_eq_uniform_average
        C_star C_h eta rewards P
    _ ≤ (1 / (M p : ℝ)) * ∑ _j : Fin (M p), (1 / (B_boot p : ℝ)) :=
      mul_le_mul_of_nonneg_left hsum hcoeff
    _ = 1 / (B_boot p : ℝ) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp [ne_of_gt hM, ne_of_gt hB]

/-- The accepted universal public-output witness and its public failure event
specialized to the actual original-private-J forward event. -/
theorem exists_universal_N0_commonGoodSet_and_actualSelectedIndexForward_bound :
    ∃ N₀ : ℕ, ∀ p : ConstructorDimensions.Parameters, N₀ ≤ N p →
      (16 : ℝ) * (p.m : ℝ) * (p.K : ℝ) * (b_N p : ℝ) ^ 2 < (p.T : ℝ) →
      MeasurableSet (BootstrapContextPassingTail.commonNumericPublicGoodSet p) ∧
      (CompletePublicTable.publishedOutputMeasure p).real
        (BootstrapContextPassingTail.commonNumericPublicGoodSet p)ᶜ ≤ 1 / (N p : ℝ) ∧
      ∀ P : CompletePublicTable.PublishedOutput p,
        P ∈ BootstrapContextPassingTail.commonNumericPublicGoodSet p →
        ∀ rewards : Fin p.T → Fin p.K → Fin (D p + 1),
          ∀ C_star C_h : ℝ, ∀ eta : LearningRate,
            (BootstrapPrivateRoundStreams.extendedPrivateLaw p).real
              (actualSelectedIndexAnyFalseForwardPrefixPassSection
                C_star C_h eta rewards P) ≤ 1 / (B_boot p : ℝ) := by
  obtain ⟨N₀, hbase⟩ :=
    exists_universal_N0_commonGoodSet_and_fixedOutput_actualAnyFalseForwardPrefixPass_bound
  refine ⟨N₀, ?_⟩
  intro p hN₀ hbranch
  rcases hbase p hN₀ hbranch with ⟨hmeas, hfailure, _hfixed⟩
  refine ⟨hmeas, hfailure, ?_⟩
  intro P hP rewards C_star C_h eta
  exact actualSelectedIndexAnyFalseForwardPrefixPassSection_real_le_inv_Bboot
    C_star C_h eta rewards P hP

end Bandits.Support.GeneratedSelectedIndexForwardBound

end
