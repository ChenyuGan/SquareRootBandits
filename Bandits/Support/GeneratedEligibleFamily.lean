/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.GeneratedForwardPrefixTests
public import Bandits.Support.ReferenceInitializationMeasurability
public import Bandits.Support.FalseForwardBaseTail

/-!
# Measurable eligible families for generated false-forward tests

For a fixed block and original follower, this module packages the literal
eligibility sets of the existing generated reference initialization as a
base-measurable family. Candidate DATA slots come from the complete base's
continuous learning rows. ID-zero and positive-feedback tests come from the
actual generated physical block. Outside the processed, incoming-active test
domain the event family is padded by the empty set.

Sources: `sources/zip4/manuscript/appendix_b_communication.tex:101-126,294-326`
and `sources/zip4/manuscript/07_public_setup.tex:123-140`.

This is a deterministic measurability adapter. It proves no private-ID law,
conditional probability statement, support-context reduction, independent
slice tail, coupling, or source-facing closure.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.CompletePublicTable
open Bandits.Support.ContinuousLearningRows
open Bandits.Support.ActiveRoundActions
open Bandits.Support.PublicDiscreteDraws
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.BootstrapPhysicalBlock
open Bandits.Support.ReferenceInitializationRun
open Bandits.Support.ReferenceInitializationMeasurability
open Bandits.Support.ReferencePrelaunchFollower
open Bandits.Support.GeneratedForwardPrefixTests
open Bandits.Support.ForwardPrefixSlice
open Bandits.Support.FalseRowSliceFactorization
open Bandits.Support.FalseForwardBaseTail
open scoped Classical

namespace Bandits.Support.GeneratedEligibleFamily

variable {p : ConstructorDimensions.Parameters}

/-- Insert a false-factor base and the original private coordinates into the
accepted varying-coordinate carrier of the reference initialization. The
complete row is the selected true forward row paired with its learning row. -/
def inputCoordinatesOfBase (J : Fin (M p))
    (z : FalseFactorBase p × ExtendedPrivateCoordinates p) :
    ReferenceInitializationMeasurability.InputCoordinates p :=
  (z.1.1, ((z.1.2.2, z.1.2.1 J), z.2))

/-- The actual reference input determined by the shared base, fixed parameters,
true index, rewards, and same private-coordinate point. -/
def referenceInputOfBase (C_star C_h : ℝ) (eta : LearningRate)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (J : Fin (M p))
    (z : FalseFactorBase p × ExtendedPrivateCoordinates p) :
    ReferenceInitializationRun.Input p :=
  ReferenceInitializationMeasurability.inputOfCoordinates p C_star C_h eta rewards
    (inputCoordinatesOfBase J z)

/-- The selected true-row reference input read directly from a published
output. -/
def referenceInputOfPublishedOutput (C_star C_h : ℝ) (eta : LearningRate)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (J : Fin (M p))
    (z : PublishedOutput p × ExtendedPrivateCoordinates p) :
    ReferenceInitializationRun.Input p where
  ids := z.1.1
  row := z.1.2 J
  rewards := rewards
  coordinates := z.2
  C_star := C_star
  C_h := C_h
  eta := eta

/-- A candidate's literal eligibility test on an already generated physical
block. Its DATA slot is supplied by the base learning row. Feedback is the
actual own observation on every source slot, and the private ID is the actual
ID installed in the physical block. -/
def candidateEligibleOnPhysical
    (base : FalseFactorBase p)
    {s' : Fin (n_boot p)} (phys : BootstrapPhysicalBlock.Input p s')
    (j : {i // i ∈ phys.uninformed}) (v : Fin (M p)) (t : Fin p.T) : Prop :=
  phys.active j = true ∧
    phys.ids (phys.privateId j) t = false ∧
    slotDraw ((base.2.1 v) t).1 = dataSlot ∧
    0 < (BootstrapPhysicalBlock.observationIndex phys
      (BootstrapPhysicalBlock.run phys t.val) t
      (followerPlayer p.two_le_m j.1)).val

/-- The event set for one candidate on an existing physical block. The only
calendar filter is the source block `s`; no physical block or default trace
is constructed outside the tested domain. -/
def candidateEligibleSetOnPhysical
    (base : FalseFactorBase p) (s : Fin (n_boot p))
    {s' : Fin (n_boot p)} (phys : BootstrapPhysicalBlock.Input p s')
    (j : {i // i ∈ phys.uninformed}) (v : Fin (M p)) : Finset (Fin p.T) :=
  (calendarBlock p s).filter (candidateEligibleOnPhysical base phys j v)

/-- Eligibility on a fixed actual initialization boundary. This boundary case
is selected only when it is exactly the processed opportunity for `s`; its
physical block is then the accepted `ReferenceInitializationRun.physical`. -/
def chooseAtBoundary (C_star C_h : ℝ) (eta : LearningRate)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (J : Fin (M p))
    (s : Fin (n_boot p)) (i : Follower p.m)
    (b : ReferenceInitializationRun.Boundary p)
    (z : FalseFactorBase p × ExtendedPrivateCoordinates p) (v : Fin (M p)) :
    Finset (Fin p.T) :=
  if hguard : b.crossing = none ∧ b.completed = s.val then
    let hrem : b.completed < n_boot p := by omega
    if hin : i ∈ ReferenceInitializationRun.uninformed b then
      candidateEligibleSetOnPhysical z.1 s
        (ReferenceInitializationRun.physical
          (referenceInputOfBase C_star C_h eta rewards J z) b hrem)
        ⟨i, by
          change i ∈ ReferenceInitializationRun.uninformed b
          exact hin⟩ v
    else ∅
  else ∅

/-- The padded event family for one original candidate label. The second label
coordinate is intentionally absent here: it indexes the false forward slice
tested by the consumer, while physical eligibility retains the actual draw. -/
def chooseFromBase (C_star C_h : ℝ) (eta : LearningRate)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (J : Fin (M p))
    (s : Fin (n_boot p)) (i : Follower p.m)
    (z : FalseFactorBase p × ExtendedPrivateCoordinates p)
    (v : Fin (M p)) : Finset (Fin p.T) :=
  chooseAtBoundary C_star C_h eta rewards J s i
    (ReferenceInitializationRun.run
      (referenceInputOfBase C_star C_h eta rewards J z) s.val) z v

/-- The eligible list is a subset of the exact source calendar block, including
in the padded cases. -/
theorem chooseFromBase_subset_calendarBlock (C_star C_h : ℝ) (eta : LearningRate)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (J : Fin (M p))
    (s : Fin (n_boot p)) (i : Follower p.m)
    (z : FalseFactorBase p × ExtendedPrivateCoordinates p) (v : Fin (M p)) :
    chooseFromBase C_star C_h eta rewards J s i z v ⊆ calendarBlock p s := by
  dsimp [chooseFromBase, chooseAtBoundary]
  split_ifs with hproc hi
  · intro t ht
    exact (Finset.mem_filter.mp ht).1
  · simp
  · simp

/-- If the actual generated incoming follower is inactive, the event padding
is empty. -/
theorem candidateEligibleSetOnPhysical_eq_empty_of_inactive
    (base : FalseFactorBase p) (s : Fin (n_boot p))
    {s' : Fin (n_boot p)} (phys : BootstrapPhysicalBlock.Input p s')
    (j : {i // i ∈ phys.uninformed}) (v : Fin (M p))
    (hinactive : phys.active j = false) :
    candidateEligibleSetOnPhysical base s phys j v = ∅ := by
  apply Finset.ext
  intro t
  simp [candidateEligibleSetOnPhysical, candidateEligibleOnPhysical, hinactive]

/-- Measurability of the literal candidate set when the incoming boundary is
fixed. Slot and feedback observables are the accepted fixed-boundary physical
maps; block-start activity and ID use the accepted private draw adapter. -/
theorem measurable_candidateEligibleSet_fixedBoundary
    (C_star C_h : ℝ) (eta : LearningRate)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (J : Fin (M p))
    (s : Fin (n_boot p)) (i : Follower p.m) (v : Fin (M p))
    (b : ReferenceInitializationRun.Boundary p)
    (hrem : b.completed < n_boot p) (hin : i ∈ ReferenceInitializationRun.uninformed b) :
    Measurable (fun z : FalseFactorBase p × ExtendedPrivateCoordinates p =>
      candidateEligibleSetOnPhysical z.1 s
        (ReferenceInitializationRun.physical
          (referenceInputOfBase C_star C_h eta rewards J z) b hrem)
        ⟨i, by
          change i ∈ ReferenceInitializationRun.uninformed b
          exact hin⟩ v) := by
  classical
  let s' := ReferenceInitializationRun.nextBlock b hrem
  let coords := fun z : FalseFactorBase p × ExtendedPrivateCoordinates p =>
    inputCoordinatesOfBase J z
  let x := fun z : FalseFactorBase p × ExtendedPrivateCoordinates p =>
    ReferenceInitializationMeasurability.inputOfCoordinates p C_star C_h eta rewards
      (coords z)
  let incoming := ReferenceInitializationRun.uninformed b
  have hcoords : Measurable coords := by
    dsimp [coords, inputCoordinatesOfBase]
    have hid : Measurable (fun z : FalseFactorBase p × ExtendedPrivateCoordinates p => z.1.1) :=
      (measurable_fst.comp measurable_fst)
    have hforward : Measurable
        (fun z : FalseFactorBase p × ExtendedPrivateCoordinates p => z.1.2.2) :=
      (measurable_snd.comp (measurable_snd.comp measurable_fst))
    have hlearning : Measurable
        (fun z : FalseFactorBase p × ExtendedPrivateCoordinates p => z.1.2.1 J) :=
      (measurable_pi_apply J).comp
        (measurable_fst.comp (measurable_snd.comp measurable_fst))
    exact hid.prodMk ((hforward.prodMk hlearning).prodMk measurable_snd)
  have hdraws : Measurable
      (fun z : FalseFactorBase p × ExtendedPrivateCoordinates p =>
        ReferenceInitializationMeasurability.blockDrawCode p s' incoming
          b.numerators b.weight_ge_one (coords z)) :=
    (ReferenceInitializationMeasurability.measurable_blockDrawCode p s' incoming
      b.numerators b.weight_ge_one).comp hcoords
  let observationAt (t : Fin p.T) :
      FalseFactorBase p × ExtendedPrivateCoordinates p → Fin (D p + 1) :=
    fun z => BootstrapPhysicalBlock.observationIndex
      (ReferenceInitializationRun.physical (x z) b hrem)
      (BootstrapPhysicalBlock.run (ReferenceInitializationRun.physical (x z) b hrem)
        t.val) t (followerPlayer p.two_le_m i)
  have hphysical (t : Fin p.T) : Measurable (observationAt t) := by
    have hobs := (ReferenceInitializationMeasurability.measurable_physicalObservationIndex_at_fixedBoundary
      p C_star C_h eta rewards b hrem).comp hcoords
    exact (measurable_pi_apply (followerPlayer p.two_le_m i)).comp
      ((measurable_pi_apply t).comp hobs)
  let activityAt : FalseFactorBase p × ExtendedPrivateCoordinates p → Bool :=
    fun z => (ReferenceInitializationRun.physical (x z) b hrem).active
      ⟨i, by
        change i ∈ ReferenceInitializationRun.uninformed b
        exact hin⟩
  have hactive : Measurable activityAt := by
    change Measurable (fun z : FalseFactorBase p × ExtendedPrivateCoordinates p =>
      (ReferenceInitializationMeasurability.blockDrawCode p s' incoming
        b.numerators b.weight_ge_one (coords z)).1 ⟨i, hin⟩)
    exact (measurable_pi_apply ⟨i, hin⟩).comp (measurable_fst.comp hdraws)
  let privateIDMap := fun z : FalseFactorBase p × ExtendedPrivateCoordinates p =>
    (ReferenceInitializationMeasurability.blockDrawCode p s' incoming
      b.numerators b.weight_ge_one (coords z)).2.2.1
  have hprivateMap : Measurable privateIDMap := by
    change Measurable (fun z : FalseFactorBase p × ExtendedPrivateCoordinates p =>
      (ReferenceInitializationMeasurability.blockDrawCode p s' incoming
        b.numerators b.weight_ge_one (coords z)).2.2.1)
    exact measurable_fst.comp (measurable_snd.comp (measurable_snd.comp hdraws))
  let privateAt : FalseFactorBase p × ExtendedPrivateCoordinates p → Fin (A_id p) :=
    fun z => (ReferenceInitializationRun.physical (x z) b hrem).privateId
      ⟨i, by
        change i ∈ ReferenceInitializationRun.uninformed b
        exact hin⟩
  have hprivate : Measurable privateAt := by
    change Measurable (fun z : FalseFactorBase p × ExtendedPrivateCoordinates p =>
      privateIDMap z ⟨i, hin⟩)
    exact (measurable_pi_apply (⟨i, hin⟩ : {j // j ∈ incoming})).comp hprivateMap
  let idBitAt (t : Fin p.T) :
      FalseFactorBase p × ExtendedPrivateCoordinates p → Bool :=
    fun z => z.1.1 (privateAt z) t
  have hids (t : Fin p.T) : Measurable (idBitAt t) := by
    let eval : Fin (A_id p) × IDArray p → Bool := fun q => q.2 q.1 t
    have heval : Measurable eval := by
      apply measurable_from_prod_countable_right
      intro u
      exact (measurable_pi_apply t).comp (measurable_pi_apply u)
    have hpair : Measurable (fun z : FalseFactorBase p × ExtendedPrivateCoordinates p =>
        (privateAt z, z.1.1)) :=
      hprivate.prodMk (measurable_fst.comp measurable_fst)
    exact heval.comp hpair
  let slotAt (t : Fin p.T) : FalseFactorBase p × ExtendedPrivateCoordinates p → Slot :=
    fun z => slotDraw ((z.1.2.1 v) t).1
  have hslot (t : Fin p.T) : Measurable (slotAt t) := by
    let learn : FalseFactorBase p × ExtendedPrivateCoordinates p → LearningRows p :=
      fun z => z.1.2.1
    have hlearn : Measurable learn :=
      measurable_fst.comp (measurable_snd.comp measurable_fst)
    exact (PublicDiscreteDraws.measurable_slotDraw.comp
      (measurable_fst.comp ((ContinuousLearningRows.measurable_rowsControlAt v t).comp hlearn)))
  apply (measurable_finset_iff).2
  intro t
  change Measurable (fun z : FalseFactorBase p × ExtendedPrivateCoordinates p =>
    t ∈ (calendarBlock p s).filter fun t =>
      let phys := ReferenceInitializationRun.physical (x z) b hrem
      let ji : {j // j ∈ phys.uninformed} := ⟨i, by
        change i ∈ ReferenceInitializationRun.uninformed b
        exact hin⟩
      candidateEligibleOnPhysical z.1 phys ji v t)
  simp only [Finset.mem_filter]
  by_cases ht : t ∈ calendarBlock p s
  · simp only [ht, true_and]
    apply measurableSet_setOfPred.mp
    change MeasurableSet {z : FalseFactorBase p × ExtendedPrivateCoordinates p |
      activityAt z = true ∧ idBitAt t z = false ∧ slotAt t z = dataSlot ∧
        0 < (observationAt t z).val}
    have hactiveSet : MeasurableSet
        {z : FalseFactorBase p × ExtendedPrivateCoordinates p | activityAt z = true} :=
      hactive (measurableSet_singleton true)
    have hidsSet : MeasurableSet
        {z : FalseFactorBase p × ExtendedPrivateCoordinates p | idBitAt t z = false} :=
      hids t (measurableSet_singleton false)
    have hslotSet : MeasurableSet
        {z : FalseFactorBase p × ExtendedPrivateCoordinates p | slotAt t z = dataSlot} :=
      hslot t (measurableSet_singleton dataSlot)
    let positive : Fin (D p + 1) → Bool := fun q => decide (0 < q.val)
    have hpositive : Measurable (positive ∘ observationAt t) :=
      (measurable_of_finite positive).comp (hphysical t)
    have hpositiveSet : MeasurableSet
        {z : FalseFactorBase p × ExtendedPrivateCoordinates p |
          positive (observationAt t z) = true} :=
      hpositive (measurableSet_singleton true)
    have hposEq : {z : FalseFactorBase p × ExtendedPrivateCoordinates p |
        0 < (observationAt t z).val} =
        {z | positive (observationAt t z) = true} := by
      ext z
      simp [positive]
    have hpositiveProp : MeasurableSet
        {z : FalseFactorBase p × ExtendedPrivateCoordinates p |
          0 < (observationAt t z).val} := by
      rw [hposEq]
      exact hpositiveSet
    have hconj := hactiveSet.inter (hidsSet.inter (hslotSet.inter hpositiveProp))
    simpa only [Set.ofPred_and] using hconj
  · simp only [ht, false_and]
    apply measurableSet_setOfPred.mp
    change MeasurableSet (∅ : Set (FalseFactorBase p × ExtendedPrivateCoordinates p))
    exact MeasurableSet.empty

/-- Measurability of the family choice function on base and original private
coordinates. Each boundary fiber uses fixed-boundary slot and feedback maps. -/
theorem measurable_chooseFromBase (C_star C_h : ℝ) (eta : LearningRate)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (J : Fin (M p))
    (s : Fin (n_boot p)) (i : Follower p.m) (v : Fin (M p)) :
    Measurable (chooseFromBase C_star C_h eta rewards J s i · v) := by
  classical
  let coords := inputCoordinatesOfBase J
  let x := fun z : FalseFactorBase p × ExtendedPrivateCoordinates p =>
    ReferenceInitializationMeasurability.inputOfCoordinates p C_star C_h eta rewards
      (coords z)
  have hcoords : Measurable coords := by
    dsimp [coords, inputCoordinatesOfBase]
    have hid : Measurable (fun z : FalseFactorBase p × ExtendedPrivateCoordinates p => z.1.1) :=
      (measurable_fst.comp measurable_fst)
    have hforward : Measurable
        (fun z : FalseFactorBase p × ExtendedPrivateCoordinates p => z.1.2.2) :=
      (measurable_snd.comp (measurable_snd.comp measurable_fst))
    have hlearning : Measurable
        (fun z : FalseFactorBase p × ExtendedPrivateCoordinates p => z.1.2.1 J) :=
      (measurable_pi_apply J).comp
        (measurable_fst.comp (measurable_snd.comp measurable_fst))
    exact hid.prodMk ((hforward.prodMk hlearning).prodMk measurable_snd)
  have hrun : Measurable (fun z : FalseFactorBase p × ExtendedPrivateCoordinates p =>
      ReferenceInitializationRun.run (x z) s.val) :=
    (ReferenceInitializationMeasurability.measurable_run
      p C_star C_h eta rewards s.val).comp hcoords
  have hbranches : ∀ b : ReferenceInitializationRun.Boundary p,
      Measurable (chooseAtBoundary C_star C_h eta rewards J s i b · v) := by
    intro b
    by_cases hguard : b.crossing = none ∧ b.completed = s.val
    · have hrem : b.completed < n_boot p := by omega
      by_cases hin : i ∈ ReferenceInitializationRun.uninformed b
      · simpa [chooseAtBoundary, hguard, hin] using
          measurable_candidateEligibleSet_fixedBoundary C_star C_h eta rewards J s i v b hrem hin
      · simp [chooseAtBoundary, hguard, hin]
    · simp [chooseAtBoundary, hguard]
  have hboundary : Measurable
      (fun z : ReferenceInitializationRun.Boundary p ×
          (FalseFactorBase p × ExtendedPrivateCoordinates p) =>
        chooseAtBoundary C_star C_h eta rewards J s i z.1 z.2 v) :=
    measurable_from_prod_countable_right hbranches
  have hpair : Measurable (fun z : FalseFactorBase p × ExtendedPrivateCoordinates p =>
      (ReferenceInitializationRun.run (x z) s.val, z)) := hrun.prodMk measurable_id
  change Measurable (fun z : FalseFactorBase p × ExtendedPrivateCoordinates p =>
    chooseAtBoundary C_star C_h eta rewards J s i
      (ReferenceInitializationRun.run
        (referenceInputOfBase C_star C_h eta rewards J z) s.val) z v)
  exact hboundary.comp hpair

/-- The produced family is an `EligibleListFunction` for every original
slice label; its first coordinate selects candidate data and its second
coordinate remains reserved for the tested forward slice. -/
def eligibleListFunction (C_star C_h : ℝ) (eta : LearningRate)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (J : Fin (M p))
    (s : Fin (n_boot p)) (i : Follower p.m) (label : SliceLabel p) :
    EligibleListFunction p s (FalseFactorBase p × ExtendedPrivateCoordinates p) where
  choose := fun z => chooseFromBase C_star C_h eta rewards J s i z label.1
  choose_subset := fun z =>
    chooseFromBase_subset_calendarBlock C_star C_h eta rewards J s i z label.1
  measurable_choose := measurable_chooseFromBase C_star C_h eta rewards J s i label.1

/-- Package the event-functional producer in the exact family type consumed
by `FalseForwardBaseTail`. -/
def family (C_star C_h : ℝ) (eta : LearningRate)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (J : Fin (M p))
    (s : Fin (n_boot p)) (i : Follower p.m) :
    FalseForwardBaseTail.BaseMeasurableEligibleFamily p s
      (ExtendedPrivateCoordinates p) :=
  fun label => eligibleListFunction C_star C_h eta rewards J s i label

/-- Regrouping the factor base restores exactly the selected actual
reference initialization of the published output. -/
theorem referenceInputOfBase_eq_publishedOutput
    (C_star C_h : ℝ) (eta : LearningRate)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (J : Fin (M p))
    (P : PublishedOutput p) (rho : ExtendedPrivateCoordinates p) :
    referenceInputOfBase C_star C_h eta rewards J
        ((falseRowFactorEquiv p J P).1, rho) =
      referenceInputOfPublishedOutput C_star C_h eta rewards J (P, rho) := by
  cases P with
  | mk ids rows => rfl

/-- On the accepted generated physical block, the adapted candidate set is
exactly the existing `eligibleSet`. The equality uses the true complete-row
learning component and the accepted equivalence between positive own feedback
and a positive physical observation index. -/
theorem candidateEligibleSetOnActualPhysical_eq_eligibleSet
    (base : FalseFactorBase p) (x : ReferenceInitializationRun.Input p)
    (s : Fin (n_boot p)) (h : GeneratedForwardPrefixTests.processesBlock x s)
    (j : GeneratedForwardPrefixTests.ActiveIncomingFollower x s h)
    (rows : CompleteRows p) (v : Fin (M p))
    (hlearning : base.2.1 = CompletePublicTable.completeRowsLearning p rows) :
    candidateEligibleSetOnPhysical base s
        (GeneratedForwardPrefixTests.actualPhysicalBlock x s h) j.val v =
      GeneratedForwardPrefixTests.eligibleSet x s h j rows v := by
  apply Finset.ext
  intro t
  simp only [candidateEligibleSetOnPhysical, GeneratedForwardPrefixTests.eligibleSet,
    Finset.mem_filter, candidateEligibleOnPhysical,
    GeneratedForwardPrefixTests.candidateEligible]
  have hrow : base.2.1 v = (rows v).2 := congrFun hlearning v
  constructor
  · rintro ⟨ht, ha, hid, hslot, hpos⟩
    refine ⟨ht, ht, ha, hid, ?_, ?_⟩
    · simpa [hrow] using hslot
    · exact (GeneratedForwardPrefixTests.ownEntry_positive_iff_observationIndex
        (GeneratedForwardPrefixTests.actualPhysicalBlock x s h) j.val t).2 hpos
  · rintro ⟨ht, _, ha, hid, hslot, hpos⟩
    refine ⟨ht, ha, hid, ?_, ?_⟩
    · simpa [hrow] using hslot
    · exact (GeneratedForwardPrefixTests.ownEntry_positive_iff_observationIndex
        (GeneratedForwardPrefixTests.actualPhysicalBlock x s h) j.val t).1 hpos

/-- Transporting an already constructed physical input and its incoming
follower along the accepted block-index equality preserves its eligible set. -/
theorem castPhysicalBlock_uninformed
    {s₁ s₂ : Fin (n_boot p)} (e : s₁ = s₂)
    (phys : BootstrapPhysicalBlock.Input p s₁) :
    (e ▸ phys).uninformed = phys.uninformed := by
  cases e
  rfl

/-- Transport an incoming follower along a cast of the physical block index. -/
def castPhysicalFollower
    {s₁ s₂ : Fin (n_boot p)} (e : s₁ = s₂)
    (phys : BootstrapPhysicalBlock.Input p s₁)
    (j : {i // i ∈ phys.uninformed}) :
    {i // i ∈ (e ▸ phys).uninformed} :=
  ⟨j.val, by
    rw [castPhysicalBlock_uninformed e phys]
    exact j.property⟩

theorem castPhysicalFollower_active
    {s₁ s₂ : Fin (n_boot p)} (e : s₁ = s₂)
    (phys : BootstrapPhysicalBlock.Input p s₁)
    (j : {i // i ∈ phys.uninformed}) :
    (e ▸ phys).active (castPhysicalFollower e phys j) = phys.active j := by
  cases e
  rfl

theorem castPhysicalFollower_privateID
    {s₁ s₂ : Fin (n_boot p)} (e : s₁ = s₂)
    (phys : BootstrapPhysicalBlock.Input p s₁)
    (j : {i // i ∈ phys.uninformed}) :
    (e ▸ phys).privateId (castPhysicalFollower e phys j) = phys.privateId j := by
  cases e
  rfl

/-- The eligible set is invariant under the accepted dependent cast of a
physical block and its follower. -/
theorem candidateEligibleSetOnPhysical_transport
    {s₁ s₂ : Fin (n_boot p)} (e : s₁ = s₂)
    (base : FalseFactorBase p) (s : Fin (n_boot p))
    (phys : BootstrapPhysicalBlock.Input p s₁)
    (j : {i // i ∈ phys.uninformed}) (v : Fin (M p)) :
    candidateEligibleSetOnPhysical base s (e ▸ phys)
      (castPhysicalFollower e phys j) v =
      candidateEligibleSetOnPhysical base s phys j v := by
  cases e
  rfl

/-- On a processed block and an active incoming follower, the boundary-padded
choice is the existing generated eligible set. -/
theorem chooseFromBase_eq_eligibleSet
    (C_star C_h : ℝ) (eta : LearningRate)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (J : Fin (M p))
    (s : Fin (n_boot p)) (z : FalseFactorBase p × ExtendedPrivateCoordinates p)
    (h : GeneratedForwardPrefixTests.processesBlock
      (referenceInputOfBase C_star C_h eta rewards J z) s)
    (j : GeneratedForwardPrefixTests.ActiveIncomingFollower
      (referenceInputOfBase C_star C_h eta rewards J z) s h)
    (rows : CompleteRows p) (v : Fin (M p))
    (hlearning : z.1.2.1 = CompletePublicTable.completeRowsLearning p rows) :
    chooseFromBase C_star C_h eta rewards J s j.val.val z v =
      GeneratedForwardPrefixTests.eligibleSet
        (referenceInputOfBase C_star C_h eta rewards J z) s h j rows v := by
  let x := referenceInputOfBase C_star C_h eta rewards J z
  change GeneratedForwardPrefixTests.processesBlock x s at h
  have hrem : (ReferenceInitializationRun.run x s.val).completed < n_boot p := by
    rw [h.2]
    exact s.isLt
  let phys : BootstrapPhysicalBlock.Input p
      (ReferenceInitializationRun.nextBlock
        (ReferenceInitializationRun.run x s.val) hrem) :=
    ReferenceInitializationRun.physical x
      (ReferenceInitializationRun.run x s.val) hrem
  have hindex := GeneratedForwardPrefixTests.actualBlockIndex x s h
  have hcastUninformed :
      (GeneratedForwardPrefixTests.actualPhysicalBlock x s h).uninformed =
        phys.uninformed := by
    change (hindex ▸ phys).uninformed = phys.uninformed
    exact castPhysicalBlock_uninformed hindex phys
  let incoming : {i // i ∈ phys.uninformed} :=
    ⟨j.val.val, hcastUninformed ▸ j.val.property⟩
  have hsourceIn : j.val.val ∈
      ReferenceInitializationRun.uninformed (ReferenceInitializationRun.run x s.val) := by
    have hmem : j.val.val ∈ phys.uninformed := by
      rw [← hcastUninformed]
      exact j.val.property
    simpa [phys, ReferenceInitializationRun.physical,
      BootstrapPhysicalInput.blockInput] using hmem
  have hfollower : castPhysicalFollower hindex phys incoming = j.val := by
    apply Subtype.ext
    rfl
  have hphysicalDef :
      GeneratedForwardPrefixTests.actualPhysicalBlock x s h = hindex ▸ phys := by
    unfold GeneratedForwardPrefixTests.actualPhysicalBlock
      GeneratedForwardPrefixTests.actualBoundary
    rfl
  have htransport := candidateEligibleSetOnPhysical_transport
    hindex z.1 s phys incoming v
  have hchoose : chooseFromBase C_star C_h eta rewards J s j.val.val z v =
      candidateEligibleSetOnPhysical z.1 s
        (GeneratedForwardPrefixTests.actualPhysicalBlock x s h) j.val v := by
    have hchooseCast : chooseFromBase C_star C_h eta rewards J s j.val.val z v =
        candidateEligibleSetOnPhysical z.1 s (hindex ▸ phys)
          (castPhysicalFollower hindex phys incoming) v := by
      unfold x at h hsourceIn
      unfold chooseFromBase
      simp [chooseAtBoundary, h.1, h.2, hsourceIn, phys, incoming]
      exact htransport.symm
    let atPair :
        (Σ q : BootstrapPhysicalBlock.Input p s, {i // i ∈ q.uninformed}) →
          Finset (Fin p.T) :=
      fun q => candidateEligibleSetOnPhysical z.1 s q.1 q.2 v
    have hpair :
        (⟨GeneratedForwardPrefixTests.actualPhysicalBlock x s h, j.val⟩ :
          Σ q : BootstrapPhysicalBlock.Input p s, {i // i ∈ q.uninformed}) =
        ⟨hindex ▸ phys, castPhysicalFollower hindex phys incoming⟩ := by
      apply Sigma.ext hphysicalDef
      exact heq_of_eq hfollower.symm
    have hset := congrArg atPair hpair
    calc
      chooseFromBase C_star C_h eta rewards J s j.val.val z v =
          candidateEligibleSetOnPhysical z.1 s (hindex ▸ phys)
            (castPhysicalFollower hindex phys incoming) v := hchooseCast
      _ = candidateEligibleSetOnPhysical z.1 s
          (GeneratedForwardPrefixTests.actualPhysicalBlock x s h) j.val v := by
        simpa [atPair] using hset.symm
  rw [hchoose]
  exact candidateEligibleSetOnActualPhysical_eq_eligibleSet
    z.1 x s h j rows v hlearning

/-- Producer-to-consumer identity for every published output, hence for every
completion of a fixed false-row base. The label's first coordinate supplies
candidate learning data; its second coordinate does not alter eligibility. -/
theorem choose_eq_generated_eligibleSet
    (C_star C_h : ℝ) (eta : LearningRate)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (J : Fin (M p))
    (P : PublishedOutput p) (rho : ExtendedPrivateCoordinates p)
    (s : Fin (n_boot p))
    (h : GeneratedForwardPrefixTests.processesBlock
      (referenceInputOfPublishedOutput C_star C_h eta rewards J (P, rho)) s)
    (j : GeneratedForwardPrefixTests.ActiveIncomingFollower
      (referenceInputOfPublishedOutput C_star C_h eta rewards J (P, rho)) s h)
    (label : SliceLabel p) :
    (family C_star C_h eta rewards J s j.val.val label).choose
        ((falseRowFactorEquiv p J P).1, rho) =
      GeneratedForwardPrefixTests.eligibleSet
        (referenceInputOfPublishedOutput C_star C_h eta rewards J (P, rho))
        s h j P.2 label.1 := by
  let base := (falseRowFactorEquiv p J P).1
  let x := referenceInputOfPublishedOutput C_star C_h eta rewards J (P, rho)
  have hx : referenceInputOfBase C_star C_h eta rewards J (base, rho) = x := by
    exact referenceInputOfBase_eq_publishedOutput C_star C_h eta rewards J P rho
  have hbase : GeneratedForwardPrefixTests.processesBlock
      (referenceInputOfBase C_star C_h eta rewards J (base, rho)) s := by
    rw [hx]
    exact h
  have hphysEq :
      GeneratedForwardPrefixTests.actualPhysicalBlock
          (referenceInputOfBase C_star C_h eta rewards J (base, rho)) s hbase =
        GeneratedForwardPrefixTests.actualPhysicalBlock x s h := by
    cases hx
    have hproof : hbase = h := Subsingleton.elim _ _
    cases hproof
    rfl
  let incomingBase : {i // i ∈
      (GeneratedForwardPrefixTests.actualPhysicalBlock
        (referenceInputOfBase C_star C_h eta rewards J (base, rho)) s hbase).uninformed} :=
    ⟨j.val.val, by rw [hphysEq]; exact j.val.property⟩
  have hincomingEq : incomingBase = j.val := by
    apply Subtype.ext
    rfl
  let physicalFollower :
      Σ q : BootstrapPhysicalBlock.Input p s, {i // i ∈ q.uninformed} :=
    ⟨GeneratedForwardPrefixTests.actualPhysicalBlock
      (referenceInputOfBase C_star C_h eta rewards J (base, rho)) s hbase,
      incomingBase⟩
  let publishedFollower :
      Σ q : BootstrapPhysicalBlock.Input p s, {i // i ∈ q.uninformed} :=
    ⟨GeneratedForwardPrefixTests.actualPhysicalBlock x s h, j.val⟩
  have hfollowerPair : physicalFollower = publishedFollower := by
    apply Sigma.ext hphysEq
    exact heq_of_eq hincomingEq
  let activeAt :
      (Σ q : BootstrapPhysicalBlock.Input p s, {i // i ∈ q.uninformed}) → Bool :=
    fun q => q.1.active q.2
  have hactiveBase :
      (GeneratedForwardPrefixTests.actualPhysicalBlock
        (referenceInputOfBase C_star C_h eta rewards J (base, rho)) s hbase).active
        incomingBase = true := by
    have hact := congrArg activeAt hfollowerPair
    calc
      (GeneratedForwardPrefixTests.actualPhysicalBlock
        (referenceInputOfBase C_star C_h eta rewards J (base, rho)) s hbase).active
          incomingBase =
        (GeneratedForwardPrefixTests.actualPhysicalBlock x s h).active j.val := by
          simpa [activeAt, physicalFollower, publishedFollower] using hact
      _ = true := j.property
  let jbase : GeneratedForwardPrefixTests.ActiveIncomingFollower
      (referenceInputOfBase C_star C_h eta rewards J (base, rho)) s hbase :=
    ⟨incomingBase, hactiveBase⟩
  have hlearning : base.2.1 = CompletePublicTable.completeRowsLearning p P.2 := by
    simp [base]
  have hchoose := chooseFromBase_eq_eligibleSet C_star C_h eta rewards J s
    (base, rho) hbase jbase P.2 label.1 hlearning
  have hjid : jbase.val.val = j.val.val := by
    change incomingBase.val = j.val.val
    exact congrArg Subtype.val hincomingEq
  have hsetEq :
      GeneratedForwardPrefixTests.eligibleSet
          (referenceInputOfBase C_star C_h eta rewards J (base, rho))
          s hbase jbase P.2 label.1 =
        GeneratedForwardPrefixTests.eligibleSet x s h j P.2 label.1 := by
    have hleft := candidateEligibleSetOnActualPhysical_eq_eligibleSet
      base (referenceInputOfBase C_star C_h eta rewards J (base, rho))
      s hbase jbase P.2 label.1 hlearning
    have hright := candidateEligibleSetOnActualPhysical_eq_eligibleSet
      base x s h j P.2 label.1 hlearning
    let adaptPair :
        (Σ q : BootstrapPhysicalBlock.Input p s, {i // i ∈ q.uninformed}) →
          Finset (Fin p.T) :=
      fun q => candidateEligibleSetOnPhysical base s q.1 q.2 label.1
    have hpairSet := congrArg adaptPair hfollowerPair
    calc
      GeneratedForwardPrefixTests.eligibleSet
          (referenceInputOfBase C_star C_h eta rewards J (base, rho))
          s hbase jbase P.2 label.1 =
        candidateEligibleSetOnPhysical base s
          (GeneratedForwardPrefixTests.actualPhysicalBlock
            (referenceInputOfBase C_star C_h eta rewards J (base, rho)) s hbase)
          jbase.val label.1 := hleft.symm
      _ = candidateEligibleSetOnPhysical base s
          (GeneratedForwardPrefixTests.actualPhysicalBlock x s h) j.val label.1 := by
        simpa [adaptPair, jbase] using hpairSet
      _ = GeneratedForwardPrefixTests.eligibleSet x s h j P.2 label.1 := hright
  change chooseFromBase C_star C_h eta rewards J s j.val.val
      (base, rho) label.1 =
    GeneratedForwardPrefixTests.eligibleSet x s h j P.2 label.1
  rw [← hjid]
  exact hchoose.trans hsetEq

/-- The chronological list is exactly the existing generated list, with the
same original private-coordinate draw retained by the physical calculation. -/
theorem chronologicalList_eq_generated
    (C_star C_h : ℝ) (eta : LearningRate)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (J : Fin (M p))
    (P : PublishedOutput p) (rho : ExtendedPrivateCoordinates p)
    (s : Fin (n_boot p))
    (h : GeneratedForwardPrefixTests.processesBlock
      (referenceInputOfPublishedOutput C_star C_h eta rewards J (P, rho)) s)
    (j : GeneratedForwardPrefixTests.ActiveIncomingFollower
      (referenceInputOfPublishedOutput C_star C_h eta rewards J (P, rho)) s h)
    (label : SliceLabel p) :
    ForwardPrefixSlice.chronologicalEligibleTimes
        (family C_star C_h eta rewards J s j.val.val label)
        ((falseRowFactorEquiv p J P).1, rho) =
      GeneratedForwardPrefixTests.chronologicalEligibleTimes
        (referenceInputOfPublishedOutput C_star C_h eta rewards J (P, rho))
        s h j P.2 label.1 := by
  simp only [ForwardPrefixSlice.chronologicalEligibleTimes,
    GeneratedForwardPrefixTests.chronologicalEligibleTimes]
  rw [choose_eq_generated_eligibleSet C_star C_h eta rewards J P rho s h j label]

/-- Under the explicit identification of the label ID with this follower's
actual private draw, the factorized consumer event is exactly the existing
generated false-candidate pass event. -/
theorem factorPass_iff_generatedFalseCandidatePasses
    (C_star C_h : ℝ) (eta : LearningRate)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (J : Fin (M p))
    (P : PublishedOutput p) (rho : ExtendedPrivateCoordinates p)
    (s : Fin (n_boot p))
    (h : GeneratedForwardPrefixTests.processesBlock
      (referenceInputOfPublishedOutput C_star C_h eta rewards J (P, rho)) s)
    (j : GeneratedForwardPrefixTests.ActiveIncomingFollower
      (referenceInputOfPublishedOutput C_star C_h eta rewards J (P, rho)) s h)
    (label : SliceLabel p) (hfalse : label.1 ≠ J)
    (hid : label.2 =
      (GeneratedForwardPrefixTests.actualPhysicalBlock
        (referenceInputOfPublishedOutput C_star C_h eta rewards J (P, rho)) s h).privateId j.val) :
    (falseRowFactorEquiv p J P, rho) ∈
        FalseForwardBaseTail.factorFalseForwardPassSet
          (family C_star C_h eta rewards J s j.val.val) J label hfalse ↔
      GeneratedForwardPrefixTests.falseCandidatePasses
        (referenceInputOfPublishedOutput C_star C_h eta rewards J (P, rho))
        s h j P.2 J ⟨label.1, hfalse⟩ := by
  let base := (falseRowFactorEquiv p J P).1
  let E := family C_star C_h eta rewards J s j.val.val
  let x := referenceInputOfPublishedOutput C_star C_h eta rewards J (P, rho)
  have htimes := chronologicalList_eq_generated C_star C_h eta rewards J
    P rho s h j label
  have hslice :
      FalseForwardBaseTail.factorFalseForwardSlice p J label hfalse
          (falseRowFactorEquiv p J P) =
        GeneratedForwardPrefixTests.candidateForwardSlice x s h j P.2 label.1 := by
    funext t
    simp [FalseForwardBaseTail.factorFalseForwardSlice,
      FalseRowSliceFactorization.falseRowFactorEquiv_falseForward,
      GeneratedForwardPrefixTests.candidateForwardSlice, x, hid]
  change ForwardPrefixSlice.privatePrefixPasses
      (FalseForwardBaseTail.baseSectionEligibleList E base label) rho
      (FalseForwardBaseTail.factorFalseForwardSlice p J label hfalse
        (falseRowFactorEquiv p J P)) ↔
    GeneratedForwardPrefixTests.falseCandidatePasses x s h j P.2 J
      ⟨label.1, hfalse⟩
  rw [ForwardPrefixSlice.privatePrefixPasses_iff_first_q,
    GeneratedForwardPrefixTests.falseCandidatePasses_iff_first_quota]
  have htimes' :
      ForwardPrefixSlice.chronologicalEligibleTimes
          (FalseForwardBaseTail.baseSectionEligibleList E base label) rho =
        GeneratedForwardPrefixTests.chronologicalEligibleTimes x s h j P.2 label.1 := by
    simpa [E, base, ForwardPrefixSlice.chronologicalEligibleTimes,
      FalseForwardBaseTail.baseSectionEligibleList] using htimes
  rw [htimes', hslice]
  simp [GeneratedForwardPrefixTests.candidateForwardSlice]

/-- At a fixed boundary, expose the actual incoming active follower's private
ID, and return `none` outside that tested context. -/
theorem processedBoundaryRemaining (s : Fin (n_boot p))
    (b : ReferenceInitializationRun.Boundary p)
    (hguard : b.crossing = none ∧ b.completed = s.val) :
    b.completed < n_boot p := by
  omega

def activePrivateIDCodeAtBoundary
    (C_star C_h : ℝ) (eta : LearningRate)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (J : Fin (M p))
    (s : Fin (n_boot p)) (i : Follower p.m)
    (b : ReferenceInitializationRun.Boundary p)
    (z : FalseFactorBase p × ExtendedPrivateCoordinates p) : Option (Fin (A_id p)) :=
  if hguard : b.crossing = none ∧ b.completed = s.val then
    let hrem := processedBoundaryRemaining s b hguard
    let phys := ReferenceInitializationRun.physical
      (referenceInputOfBase C_star C_h eta rewards J z) b hrem
    if hin : i ∈ phys.uninformed then
      let ji : {j // j ∈ phys.uninformed} := ⟨i, hin⟩
      if phys.active ji then some (phys.privateId ji) else none
    else none
  else none

/-- The actual boundary code for block `s`, evaluated on the same false-factor
base and original private coordinates as the eligible-list family. -/
def activePrivateIDCode
    (C_star C_h : ℝ) (eta : LearningRate)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (J : Fin (M p))
    (s : Fin (n_boot p)) (i : Follower p.m)
    (z : FalseFactorBase p × ExtendedPrivateCoordinates p) : Option (Fin (A_id p)) :=
  activePrivateIDCodeAtBoundary C_star C_h eta rewards J s i
    (ReferenceInitializationRun.run
      (referenceInputOfBase C_star C_h eta rewards J z) s.val) z

/-- Fixed-boundary measurability of the active/private-ID guard uses only the
accepted finite block-draw encoding. -/
theorem measurable_activePrivateIDCodeAtBoundary
    (C_star C_h : ℝ) (eta : LearningRate)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (J : Fin (M p))
    (s : Fin (n_boot p)) (i : Follower p.m)
    (b : ReferenceInitializationRun.Boundary p) :
    Measurable (activePrivateIDCodeAtBoundary C_star C_h eta rewards J s i b) := by
  classical
  by_cases hguard : b.crossing = none ∧ b.completed = s.val
  · let hrem := processedBoundaryRemaining s b hguard
    let incoming := ReferenceInitializationRun.uninformed b
    by_cases hin : i ∈ incoming
    · let s' := ReferenceInitializationRun.nextBlock b hrem
      have hnext : ReferenceInitializationRun.nextBlock b
          (processedBoundaryRemaining s b hguard) = s' := rfl
      let coords := inputCoordinatesOfBase J
      have hcoords : Measurable coords := by
        dsimp [coords, inputCoordinatesOfBase]
        have hid : Measurable (fun z : FalseFactorBase p × ExtendedPrivateCoordinates p => z.1.1) :=
          (measurable_fst.comp measurable_fst)
        have hforward : Measurable
            (fun z : FalseFactorBase p × ExtendedPrivateCoordinates p => z.1.2.2) :=
          measurable_snd.comp (measurable_snd.comp measurable_fst)
        have hlearning : Measurable
            (fun z : FalseFactorBase p × ExtendedPrivateCoordinates p => z.1.2.1 J) :=
          (measurable_pi_apply J).comp
            (measurable_fst.comp (measurable_snd.comp measurable_fst))
        exact hid.prodMk ((hforward.prodMk hlearning).prodMk measurable_snd)
      have hdraw : Measurable
          (fun z : FalseFactorBase p × ExtendedPrivateCoordinates p =>
            ReferenceInitializationMeasurability.blockDrawCode p s' incoming
              b.numerators b.weight_ge_one (coords z)) :=
        (ReferenceInitializationMeasurability.measurable_blockDrawCode p s' incoming
          b.numerators b.weight_ge_one).comp hcoords
      let ji : {j // j ∈ incoming} := ⟨i, hin⟩
      let activity := fun z : FalseFactorBase p × ExtendedPrivateCoordinates p =>
        (ReferenceInitializationMeasurability.blockDrawCode p s' incoming
          b.numerators b.weight_ge_one (coords z)).1 ji
      let privateID := fun z : FalseFactorBase p × ExtendedPrivateCoordinates p =>
        (ReferenceInitializationMeasurability.blockDrawCode p s' incoming
          b.numerators b.weight_ge_one (coords z)).2.2.1 ji
      have hactivity : Measurable activity := by
        dsimp [activity]
        exact (measurable_pi_apply ji).comp (measurable_fst.comp hdraw)
      have hprivateID : Measurable privateID := by
        dsimp [privateID]
        exact (measurable_pi_apply ji).comp
          (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp hdraw)))
      let encode : Bool × Fin (A_id p) → Option (Fin (A_id p)) :=
        fun q => if q.1 then some q.2 else none
      have hencode : Measurable encode := measurable_of_finite encode
      have hpair : Measurable (fun z : FalseFactorBase p × ExtendedPrivateCoordinates p =>
          (activity z, privateID z)) := hactivity.prodMk hprivateID
      have hcode : Measurable (fun z : FalseFactorBase p × ExtendedPrivateCoordinates p =>
          encode (activity z, privateID z)) := hencode.comp hpair
      have hmem (z : FalseFactorBase p × ExtendedPrivateCoordinates p) :
          i ∈ (ReferenceInitializationRun.physical
            (referenceInputOfBase C_star C_h eta rewards J z) b hrem).uninformed := by
        simpa [ReferenceInitializationRun.physical,
          BootstrapPhysicalInput.blockInput] using hin
      have heq : activePrivateIDCodeAtBoundary C_star C_h eta rewards J s i b =
          fun z => encode (activity z, privateID z) := by
        funext z
        simp [activePrivateIDCodeAtBoundary, hguard, incoming, hin, s', hnext,
          ReferenceInitializationRun.physical, BootstrapPhysicalInput.blockInput,
          referenceInputOfBase, inputCoordinatesOfBase,
          ReferenceInitializationMeasurability.inputOfCoordinates,
          ReferenceInitializationMeasurability.blockDrawCode,
          coords, ji, activity, privateID, encode]
      rw [heq]
      exact hcode
    · have hnotmem (z : FalseFactorBase p × ExtendedPrivateCoordinates p) :
          ¬ i ∈ (ReferenceInitializationRun.physical
            (referenceInputOfBase C_star C_h eta rewards J z) b hrem).uninformed := by
        simpa [ReferenceInitializationRun.physical,
          BootstrapPhysicalInput.blockInput] using hin
      have heq : activePrivateIDCodeAtBoundary C_star C_h eta rewards J s i b =
          fun _ => (none : Option (Fin (A_id p))) := by
        funext z
        simp [activePrivateIDCodeAtBoundary, hguard, incoming, hin,
          ReferenceInitializationRun.physical, BootstrapPhysicalInput.blockInput]
      rw [heq]
      exact measurable_const
  · have heq : activePrivateIDCodeAtBoundary C_star C_h eta rewards J s i b =
        fun _ => (none : Option (Fin (A_id p))) := by
      funext z
      simp [activePrivateIDCodeAtBoundary, hguard]
    rw [heq]
    exact measurable_const

/-- Measurability of the active/private-ID code over base and original private
coordinates, by the accepted countable generated-boundary split. -/
theorem measurable_activePrivateIDCode
    (C_star C_h : ℝ) (eta : LearningRate)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (J : Fin (M p))
    (s : Fin (n_boot p)) (i : Follower p.m) :
    Measurable (activePrivateIDCode C_star C_h eta rewards J s i) := by
  let coords := inputCoordinatesOfBase J
  let x := fun z : FalseFactorBase p × ExtendedPrivateCoordinates p =>
    ReferenceInitializationMeasurability.inputOfCoordinates p C_star C_h eta rewards
      (coords z)
  have hcoords : Measurable coords := by
    dsimp [coords, inputCoordinatesOfBase]
    have hid : Measurable (fun z : FalseFactorBase p × ExtendedPrivateCoordinates p => z.1.1) :=
      measurable_fst.comp measurable_fst
    have hforward : Measurable
        (fun z : FalseFactorBase p × ExtendedPrivateCoordinates p => z.1.2.2) :=
      measurable_snd.comp (measurable_snd.comp measurable_fst)
    have hlearning : Measurable
        (fun z : FalseFactorBase p × ExtendedPrivateCoordinates p => z.1.2.1 J) :=
      (measurable_pi_apply J).comp
        (measurable_fst.comp (measurable_snd.comp measurable_fst))
    exact hid.prodMk ((hforward.prodMk hlearning).prodMk measurable_snd)
  have hrun : Measurable (fun z : FalseFactorBase p × ExtendedPrivateCoordinates p =>
      ReferenceInitializationRun.run (x z) s.val) :=
    (ReferenceInitializationMeasurability.measurable_run
      p C_star C_h eta rewards s.val).comp hcoords
  have hbranches : ∀ b : ReferenceInitializationRun.Boundary p,
      Measurable (activePrivateIDCodeAtBoundary C_star C_h eta rewards J s i b) := by
    intro b
    exact measurable_activePrivateIDCodeAtBoundary C_star C_h eta rewards J s i b
  have hboundary : Measurable
      (fun z : ReferenceInitializationRun.Boundary p ×
          (FalseFactorBase p × ExtendedPrivateCoordinates p) =>
        activePrivateIDCodeAtBoundary C_star C_h eta rewards J s i z.1 z.2) :=
    measurable_from_prod_countable_right hbranches
  have hpair : Measurable
      (fun z : FalseFactorBase p × ExtendedPrivateCoordinates p =>
        (ReferenceInitializationRun.run (x z) s.val, z)) := hrun.prodMk measurable_id
  change Measurable (fun z : FalseFactorBase p × ExtendedPrivateCoordinates p =>
    activePrivateIDCodeAtBoundary C_star C_h eta rewards J s i
      (ReferenceInitializationRun.run
        (referenceInputOfBase C_star C_h eta rewards J z) s.val) z)
  exact hboundary.comp hpair

/-- When the actual run processes the block and its incoming follower is
active, the boundary code is exactly that same physical block's private ID. -/
theorem activePrivateIDCode_eq_actualPrivateID
    (C_star C_h : ℝ) (eta : LearningRate)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (J : Fin (M p))
    (s : Fin (n_boot p))
    (z : FalseFactorBase p × ExtendedPrivateCoordinates p)
    (h : GeneratedForwardPrefixTests.processesBlock
      (referenceInputOfBase C_star C_h eta rewards J z) s)
    (j : GeneratedForwardPrefixTests.ActiveIncomingFollower
      (referenceInputOfBase C_star C_h eta rewards J z) s h) :
    activePrivateIDCode C_star C_h eta rewards J s j.val.val z =
      some ((GeneratedForwardPrefixTests.actualPhysicalBlock
        (referenceInputOfBase C_star C_h eta rewards J z) s h).privateId j.val) := by
  let x := referenceInputOfBase C_star C_h eta rewards J z
  change GeneratedForwardPrefixTests.processesBlock x s at h
  let b := ReferenceInitializationRun.run x s.val
  let hrem := GeneratedForwardPrefixTests.actualBlockRemaining x s h
  let phys : BootstrapPhysicalBlock.Input p
      (ReferenceInitializationRun.nextBlock b hrem) :=
    ReferenceInitializationRun.physical x b hrem
  have hindex := GeneratedForwardPrefixTests.actualBlockIndex x s h
  have hphysicalDef :
      GeneratedForwardPrefixTests.actualPhysicalBlock x s h = hindex ▸ phys := by
    unfold GeneratedForwardPrefixTests.actualPhysicalBlock
    rfl
  have hcastUninformed :
      (GeneratedForwardPrefixTests.actualPhysicalBlock x s h).uninformed =
        phys.uninformed := by
    change (hindex ▸ phys).uninformed = phys.uninformed
    exact castPhysicalBlock_uninformed hindex phys
  let incoming : {q // q ∈ phys.uninformed} :=
    ⟨j.val.val, hcastUninformed ▸ j.val.property⟩
  have hincomingEq : castPhysicalFollower hindex phys incoming = j.val := by
    apply Subtype.ext
    rfl
  have hsourceIn : j.val.val ∈ ReferenceInitializationRun.uninformed b := by
    have hm : j.val.val ∈ phys.uninformed := incoming.property
    simpa [phys, ReferenceInitializationRun.physical,
      BootstrapPhysicalInput.blockInput] using hm
  let sourcePair :
      Σ q : BootstrapPhysicalBlock.Input p s, {i // i ∈ q.uninformed} :=
    ⟨hindex ▸ phys, castPhysicalFollower hindex phys incoming⟩
  let actualPair :
      Σ q : BootstrapPhysicalBlock.Input p s, {i // i ∈ q.uninformed} :=
    ⟨GeneratedForwardPrefixTests.actualPhysicalBlock x s h, j.val⟩
  have hpair : sourcePair = actualPair := by
    apply Sigma.ext
    · exact hphysicalDef.symm
    · exact heq_of_eq hincomingEq
  let activeAt :
      (Σ q : BootstrapPhysicalBlock.Input p s, {i // i ∈ q.uninformed}) → Bool :=
    fun q => q.1.active q.2
  have hactiveCast :
      (hindex ▸ phys).active (castPhysicalFollower hindex phys incoming) = true := by
    have hact := congrArg activeAt hpair
    change (hindex ▸ phys).active (castPhysicalFollower hindex phys incoming) =
      (GeneratedForwardPrefixTests.actualPhysicalBlock x s h).active j.val at hact
    rw [j.property] at hact
    exact hact
  have hactiveSource : phys.active incoming = true := by
    rw [castPhysicalFollower_active hindex phys incoming] at hactiveCast
    exact hactiveCast
  let privateIDAt :
      (Σ q : BootstrapPhysicalBlock.Input p s, {i // i ∈ q.uninformed}) → Fin (A_id p) :=
    fun q => q.1.privateId q.2
  have hprivateCast :
      (hindex ▸ phys).privateId (castPhysicalFollower hindex phys incoming) =
        (GeneratedForwardPrefixTests.actualPhysicalBlock x s h).privateId j.val := by
    have hid := congrArg privateIDAt hpair
    simpa [privateIDAt, sourcePair, actualPair] using hid
  have hprivateID : phys.privateId incoming =
      (GeneratedForwardPrefixTests.actualPhysicalBlock x s h).privateId j.val := by
    calc
      phys.privateId incoming =
          (hindex ▸ phys).privateId (castPhysicalFollower hindex phys incoming) :=
        (castPhysicalFollower_privateID hindex phys incoming).symm
      _ = (GeneratedForwardPrefixTests.actualPhysicalBlock x s h).privateId j.val :=
        hprivateCast
  let hguard : b.crossing = none ∧ b.completed = s.val := ⟨h.1, h.2⟩
  let hremCode := processedBoundaryRemaining s b hguard
  have hremEq : hremCode = hrem := Subsingleton.elim _ _
  have hphysEq : ReferenceInitializationRun.physical x b hremCode = phys := by
    cases hremEq
    rfl
  have hlocalMem : j.val.val ∈
      (ReferenceInitializationRun.physical x b hremCode).uninformed := by
    rw [hphysEq]
    exact incoming.property
  have hlocalFollower :
      (⟨j.val.val, hlocalMem⟩ :
        {q // q ∈ (ReferenceInitializationRun.physical x b hremCode).uninformed}) =
        incoming := by
    cases hphysEq
    apply Subtype.ext
    rfl
  have hlocalActive :
      (ReferenceInitializationRun.physical x b hremCode).active
        ⟨j.val.val, hlocalMem⟩ = true := by
    cases hphysEq
    rw [hlocalFollower]
    exact hactiveSource
  have hlocalID :
      (ReferenceInitializationRun.physical x b hremCode).privateId
        ⟨j.val.val, hlocalMem⟩ = phys.privateId incoming := by
    cases hphysEq
    rw [hlocalFollower]
  have hcodeAt : activePrivateIDCodeAtBoundary C_star C_h eta rewards J s
      j.val.val b z =
      some (phys.privateId incoming) := by
    simp [activePrivateIDCodeAtBoundary, b, hguard]
    exact ⟨hlocalMem, hlocalActive, hlocalID⟩
  simp [activePrivateIDCode, x, b, hcodeAt, hprivateID]

/-- Pull the actual context code to the published-output carrier. -/
def activePrivateIDCodeOnPublishedOutput
    (C_star C_h : ℝ) (eta : LearningRate)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (J : Fin (M p))
    (s : Fin (n_boot p)) (i : Follower p.m)
    (z : PublishedOutput p × ExtendedPrivateCoordinates p) : Option (Fin (A_id p)) :=
  activePrivateIDCode C_star C_h eta rewards J s i
    ((falseRowFactorEquiv p J z.1).1, z.2)

/-- On a processed, active generated context, the output-side guard code is
the same actual private draw installed by the generated physical block. -/
theorem activePrivateIDCodeOnPublishedOutput_eq_actualPrivateID
    (C_star C_h : ℝ) (eta : LearningRate)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (J : Fin (M p))
    (P : PublishedOutput p) (rho : ExtendedPrivateCoordinates p)
    (s : Fin (n_boot p))
    (h : GeneratedForwardPrefixTests.processesBlock
      (referenceInputOfPublishedOutput C_star C_h eta rewards J (P, rho)) s)
    (j : GeneratedForwardPrefixTests.ActiveIncomingFollower
      (referenceInputOfPublishedOutput C_star C_h eta rewards J (P, rho)) s h) :
    activePrivateIDCodeOnPublishedOutput C_star C_h eta rewards J s j.val.val
      (P, rho) = some ((GeneratedForwardPrefixTests.actualPhysicalBlock
        (referenceInputOfPublishedOutput C_star C_h eta rewards J (P, rho)) s h).privateId j.val) := by
  let base := (falseRowFactorEquiv p J P).1
  let x := referenceInputOfPublishedOutput C_star C_h eta rewards J (P, rho)
  have hx : referenceInputOfBase C_star C_h eta rewards J (base, rho) = x :=
    referenceInputOfBase_eq_publishedOutput C_star C_h eta rewards J P rho
  have hbase : GeneratedForwardPrefixTests.processesBlock
      (referenceInputOfBase C_star C_h eta rewards J (base, rho)) s := by
    rw [hx]
    exact h
  have hphysEq :
      GeneratedForwardPrefixTests.actualPhysicalBlock
          (referenceInputOfBase C_star C_h eta rewards J (base, rho)) s hbase =
        GeneratedForwardPrefixTests.actualPhysicalBlock x s h := by
    cases hx
    have hproof : hbase = h := Subsingleton.elim _ _
    cases hproof
    rfl
  let incomingBase : {q // q ∈
      (GeneratedForwardPrefixTests.actualPhysicalBlock
        (referenceInputOfBase C_star C_h eta rewards J (base, rho)) s hbase).uninformed} :=
    ⟨j.val.val, by rw [hphysEq]; exact j.val.property⟩
  have hincomingEq : incomingBase = j.val := by
    apply Subtype.ext
    rfl
  let pairBase :
      Σ q : BootstrapPhysicalBlock.Input p s, {q' // q' ∈ q.uninformed} :=
    ⟨GeneratedForwardPrefixTests.actualPhysicalBlock
      (referenceInputOfBase C_star C_h eta rewards J (base, rho)) s hbase, incomingBase⟩
  let pairOutput :
      Σ q : BootstrapPhysicalBlock.Input p s, {q' // q' ∈ q.uninformed} :=
    ⟨GeneratedForwardPrefixTests.actualPhysicalBlock x s h, j.val⟩
  have hpair : pairBase = pairOutput := by
    apply Sigma.ext hphysEq
    exact heq_of_eq hincomingEq
  let privateIDAt :
      (Σ q : BootstrapPhysicalBlock.Input p s, {q' // q' ∈ q.uninformed}) → Fin (A_id p) :=
    fun q => q.1.privateId q.2
  have hprivate :
      (GeneratedForwardPrefixTests.actualPhysicalBlock
        (referenceInputOfBase C_star C_h eta rewards J (base, rho)) s hbase).privateId
          incomingBase =
        (GeneratedForwardPrefixTests.actualPhysicalBlock x s h).privateId j.val := by
    have hid := congrArg privateIDAt hpair
    simpa [privateIDAt, pairBase, pairOutput] using hid
  let activeAt :
      (Σ q : BootstrapPhysicalBlock.Input p s, {q' // q' ∈ q.uninformed}) → Bool :=
    fun q => q.1.active q.2
  have hactive :
      (GeneratedForwardPrefixTests.actualPhysicalBlock
        (referenceInputOfBase C_star C_h eta rewards J (base, rho)) s hbase).active
          incomingBase = true := by
    have hact := congrArg activeAt hpair
    calc
      (GeneratedForwardPrefixTests.actualPhysicalBlock
        (referenceInputOfBase C_star C_h eta rewards J (base, rho)) s hbase).active
          incomingBase =
        (GeneratedForwardPrefixTests.actualPhysicalBlock x s h).active j.val := by
          simpa [activeAt, pairBase, pairOutput] using hact
      _ = true := j.property
  let jbase : GeneratedForwardPrefixTests.ActiveIncomingFollower
      (referenceInputOfBase C_star C_h eta rewards J (base, rho)) s hbase :=
    ⟨incomingBase, hactive⟩
  change activePrivateIDCode C_star C_h eta rewards J s j.val.val (base, rho) = _
  rw [activePrivateIDCode_eq_actualPrivateID C_star C_h eta rewards J s
    (base, rho) hbase jbase]
  exact congrArg some hprivate

/-- Measurability of the actual generated context code over published output
and the original private-coordinate product. -/
theorem measurable_activePrivateIDCodeOnPublishedOutput
    (C_star C_h : ℝ) (eta : LearningRate)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (J : Fin (M p))
    (s : Fin (n_boot p)) (i : Follower p.m) :
    Measurable (activePrivateIDCodeOnPublishedOutput C_star C_h eta rewards J s i) := by
  have hbase : Measurable
      (fun z : PublishedOutput p × ExtendedPrivateCoordinates p =>
        (falseRowFactorEquiv p J z.1).1) :=
    (measurable_fst.comp (falseRowFactorEquiv p J).measurable).comp measurable_fst
  have hmap : Measurable
      (fun z : PublishedOutput p × ExtendedPrivateCoordinates p =>
        ((falseRowFactorEquiv p J z.1).1, z.2)) := hbase.prodMk measurable_snd
  exact (measurable_activePrivateIDCode C_star C_h eta rewards J s i).comp hmap

/-- The factorized pass event for one label, intersected with the guard that
its ID coordinate is the actual active incoming private draw. -/
def virtualFalseForwardLabelSet
    (C_star C_h : ℝ) (eta : LearningRate)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (J : Fin (M p))
    (s : Fin (n_boot p)) (i : Follower p.m) (label : SliceLabel p) :
    Set (PublishedOutput p × ExtendedPrivateCoordinates p) :=
  if hfalse : label.1 ≠ J then
    (fun z : PublishedOutput p × ExtendedPrivateCoordinates p =>
      (falseRowFactorEquiv p J z.1, z.2)) ⁻¹'
        FalseForwardBaseTail.factorFalseForwardPassSet
          (family C_star C_h eta rewards J s i) J label hfalse ∩
      {z | activePrivateIDCodeOnPublishedOutput C_star C_h eta rewards J s i z =
        some label.2}
  else ∅

/-- The finite label union of false-forward pass and processed/active-ID guards
on the actual published-output and private-coordinate carrier. -/
def virtualExistsFalseForwardPrefixPassSet
    (C_star C_h : ℝ) (eta : LearningRate)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (J : Fin (M p))
    (s : Fin (n_boot p)) (i : Follower p.m) :
    Set (PublishedOutput p × ExtendedPrivateCoordinates p) :=
  ⋃ label : SliceLabel p,
    virtualFalseForwardLabelSet C_star C_h eta rewards J s i label

/-- Each label term is measurable: the factorized generated pass test is
pulled back through the accepted published-output equivalence, then intersected
with the measurable actual processed/active-ID code guard. -/
theorem measurableSet_virtualFalseForwardLabelSet
    (C_star C_h : ℝ) (eta : LearningRate)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (J : Fin (M p))
    (s : Fin (n_boot p)) (i : Follower p.m) (label : SliceLabel p) :
    MeasurableSet
      (virtualFalseForwardLabelSet C_star C_h eta rewards J s i label) := by
  classical
  let E := family C_star C_h eta rewards J s i
  let map : PublishedOutput p × ExtendedPrivateCoordinates p →
      FalseFactorOutput p J × ExtendedPrivateCoordinates p :=
    fun z => (falseRowFactorEquiv p J z.1, z.2)
  have hmap : Measurable map := by
    dsimp [map]
    exact (falseRowFactorEquiv p J).measurable.comp measurable_fst |>.prodMk
      measurable_snd
  have hcode : Measurable (activePrivateIDCodeOnPublishedOutput C_star C_h eta rewards J s i) :=
    measurable_activePrivateIDCodeOnPublishedOutput C_star C_h eta rewards J s i
  by_cases hfalse : label.1 ≠ J
  · have hpass : MeasurableSet
        (map ⁻¹' FalseForwardBaseTail.factorFalseForwardPassSet E J label hfalse) :=
      (FalseForwardBaseTail.measurableSet_factorFalseForwardPassSet E J label hfalse).preimage hmap
    have hguard : MeasurableSet
        {z : PublishedOutput p × ExtendedPrivateCoordinates p |
          activePrivateIDCodeOnPublishedOutput C_star C_h eta rewards J s i z = some label.2} :=
      hcode (measurableSet_singleton (some label.2))
    simp [virtualFalseForwardLabelSet, hfalse]
    exact hpass.inter hguard
  · simp [virtualFalseForwardLabelSet, hfalse]

/-- Measurability of the actual finite false-forward label union, with both
the processed-block and active-incoming private-ID guards present. -/
theorem measurableSet_virtualExistsFalseForwardPrefixPassSet
    (C_star C_h : ℝ) (eta : LearningRate)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (J : Fin (M p))
    (s : Fin (n_boot p)) (i : Follower p.m) :
    MeasurableSet
      (virtualExistsFalseForwardPrefixPassSet C_star C_h eta rewards J s i) := by
  classical
  rw [virtualExistsFalseForwardPrefixPassSet]
  exact MeasurableSet.iUnion fun label =>
    measurableSet_virtualFalseForwardLabelSet C_star C_h eta rewards J s i label

end Bandits.Support.GeneratedEligibleFamily

end
