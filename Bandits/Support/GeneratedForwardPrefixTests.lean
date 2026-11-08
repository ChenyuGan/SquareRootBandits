/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceInitializationRun
public import Bandits.Support.ForwardPrefixSlice
public import Bandits.Support.FalseRowSliceFactorization

/-!
# Virtual false-forward tests on a generated reference block

Sources: sources/zip4/manuscript/appendix_b_communication.tex:101-126,
294-344,751-790 and sources/zip4/manuscript/07_public_setup.tex:129-144.

This module derives the tested block from ReferenceInitializationRun.run.
Its virtual candidate tests read the actual incoming active follower, its
actual private ID, and its actual physical observation. Candidate DATA
eligibility uses that candidate's existing continuous learning row. Forward
bits are read only after the eligible times have been formed. All tests are
observational: they do not alter the generated run.

The module proves deterministic finite-prefix facts only. It constructs no
eligible-list measurability producer, conditional law, probability bound,
coupling, or manuscript closure.
-/

public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.CompletePublicTable
open Bandits.Support.ActiveRoundActions
open Bandits.Support.PublicDiscreteDraws
open Bandits.Support.ReferenceInitializationRun
open Bandits.Support.BootstrapPhysicalBlock
open Bandits.Support.BootstrapTruePrefixController
open Bandits.Support.ForwardPrefixSlice
open Bandits.Support.FalseRowSliceFactorization
open scoped Classical

namespace Bandits.Support.GeneratedForwardPrefixTests

variable {p : Parameters}

/-- The boundary reached at the opportunity for block s has not crossed
beforehand and has completed exactly the preceding s.val blocks. -/
@[expose] def processesBlock (x : ReferenceInitializationRun.Input p)
    (s : Fin (n_boot p)) : Prop :=
  (ReferenceInitializationRun.run x s.val).crossing = none ∧
    (ReferenceInitializationRun.run x s.val).completed = s.val

/-- A processed block cannot have any earlier crossing in the stopped run. -/
theorem processesBlock_no_prior_crossing
    (x : ReferenceInitializationRun.Input p) (s : Fin (n_boot p))
    (h : processesBlock x s) {r : ℕ} (hr : r ≤ s.val) :
    (ReferenceInitializationRun.run x r).crossing = none := by
  cases hc : (ReferenceInitializationRun.run x r).crossing with
  | none => rfl
  | some c =>
      have hsome : (ReferenceInitializationRun.run x r).crossing.isSome = true := by
        simp [hc]
      have hfreeze := ReferenceInitializationRun.run_stops_at_crossing
        x r (s.val - r) hsome
      have hcross := congrArg ReferenceInitializationRun.Boundary.crossing hfreeze
      rw [Nat.add_sub_of_le hr, h.1, hc] at hcross
      cases hcross

/-- The actual physical input at the generated boundary, available only when
the run really processes this block. -/
@[expose] def actualBoundary (x : ReferenceInitializationRun.Input p)
    (s : Fin (n_boot p)) : ReferenceInitializationRun.Boundary p :=
  ReferenceInitializationRun.run x s.val

/-- The generated boundary has a remaining block under processesBlock. -/
theorem actualBlockRemaining (x : ReferenceInitializationRun.Input p)
    (s : Fin (n_boot p)) (h : processesBlock x s) :
    (actualBoundary x s).completed < n_boot p := by
  exact h.2 ▸ s.isLt

/-- The accepted block index at the generated boundary is exactly s. -/
theorem actualBlockIndex (x : ReferenceInitializationRun.Input p)
    (s : Fin (n_boot p)) (h : processesBlock x s) :
    ReferenceInitializationRun.nextBlock (actualBoundary x s)
      (actualBlockRemaining x s h) = s := by
  apply Fin.ext
  change (ReferenceInitializationRun.run x s.val).completed = s.val
  exact h.2

/-- The actual physical input at the generated boundary, available only when
the run really processes this block. -/
@[expose] def actualPhysicalBlock (x : ReferenceInitializationRun.Input p)
    (s : Fin (n_boot p)) (h : processesBlock x s) :
    BootstrapPhysicalBlock.Input p s :=
  actualBlockIndex x s h ▸ ReferenceInitializationRun.physical x
    (actualBoundary x s) (actualBlockRemaining x s h)

private theorem castPhysicalBlock_row {s₁ s₂ : Fin (n_boot p)}
    (e : s₁ = s₂) (v : BootstrapPhysicalBlock.Input p s₁) :
    (e ▸ v).row = v.row := by
  cases e
  rfl

/-- The actual physical block keeps the selected complete row from its
ReferenceInitializationRun input. -/
theorem actualPhysicalBlock_row (x : ReferenceInitializationRun.Input p)
    (s : Fin (n_boot p)) (h : processesBlock x s) :
    (actualPhysicalBlock x s h).row = x.row := by
  exact castPhysicalBlock_row (actualBlockIndex x s h)
    (ReferenceInitializationRun.physical x (actualBoundary x s)
      (actualBlockRemaining x s h))

/-- A tested follower is selected from the generated incoming uninformed set
and carries its actual current-block activity proof. -/
abbrev ActiveIncomingFollower (x : ReferenceInitializationRun.Input p)
    (s : Fin (n_boot p)) (h : processesBlock x s) :=
  {j : {i // i ∈ (actualPhysicalBlock x s h).uninformed} //
    (actualPhysicalBlock x s h).active j = true}

/-- The candidate-specific, inclusive observation eligibility predicate.
The follower activity is the actual activity carried by the subtype, while
the slot is read from candidate v's own learning row. -/
@[expose] def candidateEligible
    (x : ReferenceInitializationRun.Input p) (s : Fin (n_boot p))
    (h : processesBlock x s) (j : ActiveIncomingFollower x s h)
    (rows : CompleteRows p) (v : Fin (M p)) (t : Fin p.T) : Prop :=
  t ∈ calendarBlock p s ∧
    (actualPhysicalBlock x s h).active j.val = true ∧
    (actualPhysicalBlock x s h).ids
      ((actualPhysicalBlock x s h).privateId j.val) t = false ∧
    slotDraw ((rows v).2 t).1 = dataSlot ∧
    0 < (ReferenceInitializationRun.ownEntry (actualPhysicalBlock x s h)
      (followerPlayer p.two_le_m j.val.val) t).2.val.val

/-- The full eligible finset for a candidate on the generated physical
block. -/
@[expose] def eligibleSet
    (x : ReferenceInitializationRun.Input p) (s : Fin (n_boot p))
    (h : processesBlock x s) (j : ActiveIncomingFollower x s h)
    (rows : CompleteRows p) (v : Fin (M p)) : Finset (Fin p.T) :=
  (calendarBlock p s).filter (candidateEligible x s h j rows v)

theorem mem_eligibleSet_iff
    (x : ReferenceInitializationRun.Input p) (s : Fin (n_boot p))
    (h : processesBlock x s) (j : ActiveIncomingFollower x s h)
    (rows : CompleteRows p) (v : Fin (M p)) (t : Fin p.T) :
    t ∈ eligibleSet x s h j rows v ↔ candidateEligible x s h j rows v t := by
  simp only [eligibleSet, Finset.mem_filter, candidateEligible]
  constructor
  · rintro ⟨_, htest⟩
    exact htest
  · intro htest
    exact ⟨htest.1, htest⟩

/-- Every member of the generated candidate set is a time in the source
calendar block. -/
theorem eligibleSet_subset_calendarBlock
    (x : ReferenceInitializationRun.Input p) (s : Fin (n_boot p))
    (h : processesBlock x s) (j : ActiveIncomingFollower x s h)
    (rows : CompleteRows p) (v : Fin (M p)) :
    eligibleSet x s h j rows v ⊆ calendarBlock p s := by
  intro t ht
  exact (mem_eligibleSet_iff x s h j rows v t).mp ht |>.1

/-- The full eligible set restricted to the inclusive calendar prefix through
offset k - 1. -/
@[expose] def eligiblePrefixSet
    (x : ReferenceInitializationRun.Input p) (s : Fin (n_boot p))
    (h : processesBlock x s) (j : ActiveIncomingFollower x s h)
    (rows : CompleteRows p) (v : Fin (M p)) (k : ℕ) : Finset (Fin p.T) :=
  (eligibleSet x s h j rows v).filter (fun t => t.val < k)

theorem mem_eligiblePrefixSet_iff
    (x : ReferenceInitializationRun.Input p) (s : Fin (n_boot p))
    (h : processesBlock x s) (j : ActiveIncomingFollower x s h)
    (rows : CompleteRows p) (v : Fin (M p)) (k : ℕ) (t : Fin p.T) :
    t ∈ eligiblePrefixSet x s h j rows v k ↔
      t ∈ eligibleSet x s h j rows v ∧ t.val < k := by
  simp only [eligiblePrefixSet, Finset.mem_filter]

/-- Eligibility prefixes are nested in chronological cutoffs. -/
theorem eligiblePrefixSet_mono
    (x : ReferenceInitializationRun.Input p) (s : Fin (n_boot p))
    (h : processesBlock x s) (j : ActiveIncomingFollower x s h)
    (rows : CompleteRows p) (v : Fin (M p)) {k l : ℕ} (hkl : k ≤ l) :
    eligiblePrefixSet x s h j rows v k ⊆ eligiblePrefixSet x s h j rows v l := by
  intro t ht
  rw [mem_eligiblePrefixSet_iff] at ht ⊢
  exact ⟨ht.1, ht.2.trans_le hkl⟩

/-- An eligible current observation is included at prefix length t.val + 1. -/
theorem currentObservation_in_eligiblePrefix
    (x : ReferenceInitializationRun.Input p) (s : Fin (n_boot p))
    (h : processesBlock x s) (j : ActiveIncomingFollower x s h)
    (rows : CompleteRows p) (v : Fin (M p)) (t : Fin p.T)
    (ht : t ∈ eligibleSet x s h j rows v) :
    t ∈ eligiblePrefixSet x s h j rows v (t.val + 1) := by
  rw [mem_eligiblePrefixSet_iff]
  exact ⟨ht, Nat.lt_succ_self _⟩

/-- Chronological list of every eligible time, with no post-save truncation. -/
@[expose] noncomputable def chronologicalEligibleTimes
    (x : ReferenceInitializationRun.Input p) (s : Fin (n_boot p))
    (h : processesBlock x s) (j : ActiveIncomingFollower x s h)
    (rows : CompleteRows p) (v : Fin (M p)) : List (Fin p.T) :=
  (eligibleSet x s h j rows v).sort

theorem mem_chronologicalEligibleTimes_iff
    (x : ReferenceInitializationRun.Input p) (s : Fin (n_boot p))
    (h : processesBlock x s) (j : ActiveIncomingFollower x s h)
    (rows : CompleteRows p) (v : Fin (M p)) (t : Fin p.T) :
    t ∈ chronologicalEligibleTimes x s h j rows v ↔
      t ∈ eligibleSet x s h j rows v := by
  simp only [chronologicalEligibleTimes, Finset.mem_sort]

theorem chronologicalEligibleTimes_nodup
    (x : ReferenceInitializationRun.Input p) (s : Fin (n_boot p))
    (h : processesBlock x s) (j : ActiveIncomingFollower x s h)
    (rows : CompleteRows p) (v : Fin (M p)) :
    (chronologicalEligibleTimes x s h j rows v).Nodup :=
  Finset.sort_nodup _ _

theorem chronologicalEligibleTimes_sorted
    (x : ReferenceInitializationRun.Input p) (s : Fin (n_boot p))
    (h : processesBlock x s) (j : ActiveIncomingFollower x s h)
    (rows : CompleteRows p) (v : Fin (M p)) :
    (chronologicalEligibleTimes x s h j rows v).SortedLT :=
  Finset.sortedLT_sort _

/-- The scanned eligible-list prefixes are nested as the scan length grows. -/
theorem chronologicalEligibleTimes_take_sublist
    (x : ReferenceInitializationRun.Input p) (s : Fin (n_boot p))
    (h : processesBlock x s) (j : ActiveIncomingFollower x s h)
    (rows : CompleteRows p) (v : Fin (M p)) {k l : ℕ} (hkl : k ≤ l) :
    List.Sublist
      ((chronologicalEligibleTimes x s h j rows v).take k)
      ((chronologicalEligibleTimes x s h j rows v).take l) := by
  have ht :
      (chronologicalEligibleTimes x s h j rows v).take k =
        ((chronologicalEligibleTimes x s h j rows v).take l).take k := by
    rw [List.take_take, Nat.min_eq_left hkl]
  rw [ht]
  exact List.take_sublist _ _

/-- The prefix count from the existing literal scan, at an inclusive list
prefix length. -/
@[expose] def candidatePrefixCount
    (x : ReferenceInitializationRun.Input p) (s : Fin (n_boot p))
    (h : processesBlock x s) (j : ActiveIncomingFollower x s h)
    (rows : CompleteRows p) (v : Fin (M p)) (k : ℕ) : ℕ :=
  ForwardPrefixSlice.prefixCount (chronologicalEligibleTimes x s h j rows v) k

/-- Candidate v's forward row at the actual private ID U of this follower in
the generated block. -/
@[expose] def candidateForwardSlice
    (x : ReferenceInitializationRun.Input p) (s : Fin (n_boot p))
    (h : processesBlock x s) (j : ActiveIncomingFollower x s h)
    (rows : CompleteRows p) (v : Fin (M p)) : ForwardPrefixSlice.ForwardSlice p :=
  fun t => (rows v).1 ((actualPhysicalBlock x s h).privateId j.val) t

/-- The permanent dead condition from the existing scan, over the same
inclusive prefix and actual private ID coordinate. -/
@[expose] def candidatePrefixDead
    (x : ReferenceInitializationRun.Input p) (s : Fin (n_boot p))
    (h : processesBlock x s) (j : ActiveIncomingFollower x s h)
    (rows : CompleteRows p) (v : Fin (M p)) (k : ℕ) : Bool :=
  ForwardPrefixSlice.prefixEverMismatch
    (chronologicalEligibleTimes x s h j rows v)
    (candidateForwardSlice x s h j rows v) k

/-- Exact no-mismatch characterization of the literal dead bit. -/
theorem candidatePrefixDead_eq_false_iff
    (x : ReferenceInitializationRun.Input p) (s : Fin (n_boot p))
    (h : processesBlock x s) (j : ActiveIncomingFollower x s h)
    (rows : CompleteRows p) (v : Fin (M p)) (k : ℕ) :
    candidatePrefixDead x s h j rows v k = false ↔
      ∀ t ∈ (chronologicalEligibleTimes x s h j rows v).take k,
        candidateForwardSlice x s h j rows v t = true := by
  exact ForwardPrefixSlice.prefixEverMismatch_eq_false_iff _ _ k

/-- A virtual candidate passes precisely when some inclusive list prefix
reaches quota without a mismatch in its actual-U forward slice. -/
@[expose] def falseCandidatePasses
    (x : ReferenceInitializationRun.Input p) (s : Fin (n_boot p))
    (h : processesBlock x s) (j : ActiveIncomingFollower x s h)
    (rows : CompleteRows p) (J : Fin (M p))
    (v : FalseRowSliceFactorization.FalseRow p J) : Prop :=
  ForwardPrefixSlice.prefixPasses
    (chronologicalEligibleTimes x s h j rows v.1)
    (candidateForwardSlice x s h j rows v.1)
    (q_dec p)

/-- Existing scan theorem specialized to one generated false candidate. -/
theorem falseCandidatePasses_iff_first_quota
    (x : ReferenceInitializationRun.Input p) (s : Fin (n_boot p))
    (h : processesBlock x s) (j : ActiveIncomingFollower x s h)
    (rows : CompleteRows p) (J : Fin (M p))
    (v : FalseRowSliceFactorization.FalseRow p J) :
    falseCandidatePasses x s h j rows J v ↔
      q_dec p ≤ (chronologicalEligibleTimes x s h j rows v.1).length ∧
        ∀ t ∈ (chronologicalEligibleTimes x s h j rows v.1).take (q_dec p),
          (rows v.1).1 ((actualPhysicalBlock x s h).privateId j.val) t = true := by
  exact ForwardPrefixSlice.prefixPasses_iff_first_quota _ _

/-- The selected candidate's pass event is exactly the accepted true-only
controller's eligible-prefix pass condition on this physical block. -/
@[expose] def selectedCandidatePasses
    (x : ReferenceInitializationRun.Input p) (s : Fin (n_boot p))
    (h : processesBlock x s) (j : ActiveIncomingFollower x s h) : Prop :=
  BootstrapTruePrefixController.hasPassingPrefix
    (actualPhysicalBlock x s h) j.val p.T

/-- The selected true candidate pass condition is the pending result of the
accepted true-prefix register recursion; all tested observations are included
through the end of this same physical block. -/
theorem selectedCandidatePasses_iff_controllerPending
    (x : ReferenceInitializationRun.Input p) (s : Fin (n_boot p))
    (h : processesBlock x s) (j : ActiveIncomingFollower x s h) :
    selectedCandidatePasses x s h j ↔
      (BootstrapTruePrefixController.run (actualPhysicalBlock x s h) j.val p.T).pending = true := by
  exact (BootstrapTruePrefixController.pending_iff_passingPrefix
    (actualPhysicalBlock x s h) j.val p.T le_rfl).symm

/-- The actual event that some incorrect candidate passes an exists-prefix
test on this generated block. -/
@[expose] def existsFalseForwardPrefixPass
    (x : ReferenceInitializationRun.Input p) (s : Fin (n_boot p))
    (h : processesBlock x s) (j : ActiveIncomingFollower x s h)
    (rows : CompleteRows p) (J : Fin (M p)) : Prop :=
  ∃ v : FalseRowSliceFactorization.FalseRow p J,
    falseCandidatePasses x s h j rows J v

/-- Changing a candidate's forward bits cannot change its eligible finset:
the finset reads only the candidate's continuous learning row and the actual
generated physical coordinates. -/
theorem eligibleSet_eq_of_learningRows_eq
    (x : ReferenceInitializationRun.Input p) (s : Fin (n_boot p))
    (h : processesBlock x s) (j : ActiveIncomingFollower x s h)
    (rows rows' : CompleteRows p) (v : Fin (M p))
    (hlearning : (rows v).2 = (rows' v).2) :
    eligibleSet x s h j rows v = eligibleSet x s h j rows' v := by
  unfold eligibleSet
  apply Finset.filter_congr
  intro t ht
  simp only [candidateEligible]
  rw [hlearning]

/-- The complete eligible-set family is blind to all forward coordinates
when every candidate learning/control row is fixed. -/
theorem eligibleSetFamily_eq_of_learningFamily_eq
    (x : ReferenceInitializationRun.Input p) (s : Fin (n_boot p))
    (h : processesBlock x s) (j : ActiveIncomingFollower x s h)
    (rows rows' : CompleteRows p)
    (hlearning : CompletePublicTable.completeRowsLearning p rows =
      CompletePublicTable.completeRowsLearning p rows') :
    (fun v => eligibleSet x s h j rows v) =
      fun v => eligibleSet x s h j rows' v := by
  funext v
  exact eligibleSet_eq_of_learningRows_eq x s h j rows rows' v
    (congrFun hlearning v)

/-- Equality of the existing factorization bases is exactly equality of the
shared IDs, the complete candidate learning family, and the selected true
forward row. -/
theorem falseFactorBase_eq_iff_coordinates
    (J : Fin (M p)) (out out' : PublishedOutput p) :
    (FalseRowSliceFactorization.falseRowFactorEquiv p J out).1 =
        (FalseRowSliceFactorization.falseRowFactorEquiv p J out').1 ↔
      out.1 = out'.1 ∧
        CompletePublicTable.completeRowsLearning p out.2 =
          CompletePublicTable.completeRowsLearning p out'.2 ∧
        (out.2 J).1 = (out'.2 J).1 := by
  constructor
  · intro hb
    have hid := congrArg Prod.fst hb
    have hrest := congrArg Prod.snd hb
    have hlearning := congrArg Prod.fst hrest
    have hforward := congrArg Prod.snd hrest
    exact ⟨by simpa only [FalseRowSliceFactorization.falseRowFactorEquiv_id] using hid,
      by simpa only [FalseRowSliceFactorization.falseRowFactorEquiv_learning] using hlearning,
      by simpa only [FalseRowSliceFactorization.falseRowFactorEquiv_trueForward] using hforward⟩
  · rintro ⟨hid, hlearning, hforward⟩
    apply Prod.ext
    · exact hid
    · apply Prod.ext
      · exact hlearning
      · exact hforward

/-- Holding the complete false-row factor base and the selected run input
fixed leaves every candidate's full eligibility unchanged, regardless of all
false forward bits. The input-to-output equation identifies the actual row
and the shared ID array; its rewards, private coordinates and constants are
held by the common input x. -/
theorem eligibleSet_eq_of_same_falseFactorBase
    (x : ReferenceInitializationRun.Input p) (s : Fin (n_boot p))
    (h : processesBlock x s) (j : ActiveIncomingFollower x s h)
    (J v : Fin (M p)) (out out' : PublishedOutput p)
    (hbase : (FalseRowSliceFactorization.falseRowFactorEquiv p J out).1 =
      (FalseRowSliceFactorization.falseRowFactorEquiv p J out').1)
    (hactual : x.ids = out.1 ∧ x.row = out.2 J) :
    x.ids = out'.1 ∧ x.row = out'.2 J ∧
      eligibleSet x s h j out.2 v = eligibleSet x s h j out'.2 v := by
  have hcoords := (falseFactorBase_eq_iff_coordinates J out out').1 hbase
  have hselected : out.2 J = out'.2 J := by
    apply Prod.ext
    · exact hcoords.2.2
    · have hlearn := congrFun hcoords.2.1 J
      simpa only [CompletePublicTable.completeRowsLearning] using hlearn
  have hactual' : x.row = out'.2 J := hactual.2.trans hselected
  have hlearningV : (out.2 v).2 = (out'.2 v).2 := by
    simpa only [CompletePublicTable.completeRowsLearning] using congrFun hcoords.2.1 v
  exact ⟨hactual.1.trans hcoords.1, hactual',
    eligibleSet_eq_of_learningRows_eq x s h j out.2 out'.2 v
      hlearningV⟩

/-- Own-entry positivity is the accepted physical feedback positivity used by
the true-row controller's typed observation index. -/
theorem ownEntry_positive_iff_observationIndex
    {s : Fin (n_boot p)}
    (phys : BootstrapPhysicalBlock.Input p s)
    (j : {i // i ∈ phys.uninformed}) (t : Fin p.T) :
    0 < (ReferenceInitializationRun.ownEntry phys
      (followerPlayer p.two_le_m j.val) t).2.val.val ↔
      0 < (BootstrapPhysicalBlock.observationIndex phys
        (BootstrapPhysicalBlock.run phys t.val) t
        (followerPlayer p.two_le_m j.val)).val := by
  change 0 < BootstrapPhysicalBlock.feedback phys
      (BootstrapPhysicalBlock.run phys t.val) t
      (followerPlayer p.two_le_m j.val) ↔ _
  exact (BootstrapPhysicalBlock.observationIndex_pos_iff phys
    (BootstrapPhysicalBlock.run phys t.val) t
    (followerPlayer p.two_le_m j.val)).symm

/-- On the selected row, candidate eligibility is exactly the accepted true
controller's eligible-prefix predicate on this same physical block. -/
theorem eligibleSet_eq_trueEligiblePrefix
    (x : ReferenceInitializationRun.Input p) (s : Fin (n_boot p))
    (h : processesBlock x s) (j : ActiveIncomingFollower x s h)
    (rows : CompleteRows p) (J : Fin (M p)) (hrow : x.row = rows J) :
    eligibleSet x s h j rows J =
      BootstrapTruePrefixController.eligiblePrefix (actualPhysicalBlock x s h)
        j.val p.T := by
  let phys := actualPhysicalBlock x s h
  have hphysrow : phys.row = rows J :=
    (actualPhysicalBlock_row x s h).trans hrow
  ext t
  rw [mem_eligibleSet_iff,
    BootstrapTruePrefixController.mem_eligiblePrefix_iff]
  constructor
  · rintro ⟨hcal, hactive, hid, hslot, hobs⟩
    refine ⟨hcal, t.isLt, ?_⟩
    change t ∈ calendarBlock p s ∧ phys.active j.val = true ∧
      phys.ids (phys.privateId j.val) t = false ∧
      BootstrapPhysicalBlock.slot phys t = dataSlot ∧
      0 < (BootstrapPhysicalBlock.observationIndex phys
        (BootstrapPhysicalBlock.run phys t.val) t
        (followerPlayer p.two_le_m j.val.val)).val
    refine ⟨hcal, hactive, hid, ?_, ?_⟩
    · simpa only [BootstrapPhysicalBlock.slot, hphysrow] using hslot
    · exact (ownEntry_positive_iff_observationIndex phys j.val t).1 hobs
  · rintro ⟨hcal, _, htrue⟩
    change t ∈ calendarBlock p s ∧ phys.active j.val = true ∧
      phys.ids (phys.privateId j.val) t = false ∧
      BootstrapPhysicalBlock.slot phys t = dataSlot ∧
      0 < (BootstrapPhysicalBlock.observationIndex phys
        (BootstrapPhysicalBlock.run phys t.val) t
        (followerPlayer p.two_le_m j.val.val)).val at htrue
    rcases htrue with ⟨_, hactive, hid, hslot, hobs⟩
    refine ⟨hcal, hactive, hid, ?_, ?_⟩
    · simpa only [BootstrapPhysicalBlock.slot, hphysrow] using hslot
    · exact (ownEntry_positive_iff_observationIndex phys j.val t).2 hobs

/-- Every cutoff of the selected candidate's eligibility agrees with the
accepted true controller's inclusive eligible prefix on this block. -/
theorem eligiblePrefixSet_eq_trueEligiblePrefix
    (x : ReferenceInitializationRun.Input p) (s : Fin (n_boot p))
    (h : processesBlock x s) (j : ActiveIncomingFollower x s h)
    (rows : CompleteRows p) (J : Fin (M p)) (hrow : x.row = rows J)
    (k : ℕ) :
    eligiblePrefixSet x s h j rows J k =
      BootstrapTruePrefixController.eligiblePrefix
        (actualPhysicalBlock x s h) j.val k := by
  let phys := actualPhysicalBlock x s h
  have hphysrow : phys.row = rows J :=
    (actualPhysicalBlock_row x s h).trans hrow
  ext t
  rw [mem_eligiblePrefixSet_iff,
    BootstrapTruePrefixController.mem_eligiblePrefix_iff]
  constructor
  · rintro ⟨hset, hlt⟩
    have he := (mem_eligibleSet_iff x s h j rows J t).mp hset
    refine ⟨he.1, hlt, ?_⟩
    change t ∈ calendarBlock p s ∧
      phys.active j.val = true ∧
      phys.ids (phys.privateId j.val) t = false ∧
      BootstrapPhysicalBlock.slot phys t = dataSlot ∧
      0 < (BootstrapPhysicalBlock.observationIndex phys
        (BootstrapPhysicalBlock.run phys t.val) t
        (followerPlayer p.two_le_m j.val.val)).val
    rcases he with ⟨hcal, hactive, hid, hslot, hobs⟩
    refine ⟨hcal, hactive, hid, ?_, ?_⟩
    · simpa only [BootstrapPhysicalBlock.slot, hphysrow] using hslot
    · exact (ownEntry_positive_iff_observationIndex phys j.val t).1 hobs
  · rintro ⟨hcal, hlt, htrue⟩
    change t ∈ calendarBlock p s ∧
      phys.active j.val = true ∧
      phys.ids (phys.privateId j.val) t = false ∧
      BootstrapPhysicalBlock.slot phys t = dataSlot ∧
      0 < (BootstrapPhysicalBlock.observationIndex phys
        (BootstrapPhysicalBlock.run phys t.val) t
        (followerPlayer p.two_le_m j.val.val)).val at htrue
    rcases htrue with ⟨_, hactive, hid, hslot, hobs⟩
    refine ⟨?_, hlt⟩
    rw [mem_eligibleSet_iff]
    refine ⟨hcal, hactive, hid, ?_, ?_⟩
    · simpa only [BootstrapPhysicalBlock.slot, hphysrow] using hslot
    · exact (ownEntry_positive_iff_observationIndex phys j.val t).2 hobs

/-- On the selected row, the tested forward slice uses the same actual U and
is exactly the accepted true controller's forward-bit function. -/
theorem selectedCandidateForwardSlice_eq_trueForwardBit
    (x : ReferenceInitializationRun.Input p) (s : Fin (n_boot p))
    (h : processesBlock x s) (j : ActiveIncomingFollower x s h)
    (rows : CompleteRows p) (J : Fin (M p)) (hrow : x.row = rows J) :
    candidateForwardSlice x s h j rows J =
      BootstrapTruePrefixController.trueForwardBit (actualPhysicalBlock x s h)
        j.val := by
  funext t
  have hforward := congrArg Prod.fst
    ((actualPhysicalBlock_row x s h).trans hrow)
  simp only [candidateForwardSlice, BootstrapTruePrefixController.trueForwardBit]
  rw [← hforward]

/-- The selected candidate's generated prefix pass is exactly the accepted
true controller's pass condition, expressed using this module's prefix sets
and actual-U forward slice. -/
theorem selectedCandidatePasses_iff_generatedPrefixConditions
    (x : ReferenceInitializationRun.Input p) (s : Fin (n_boot p))
    (h : processesBlock x s) (j : ActiveIncomingFollower x s h)
    (rows : CompleteRows p) (J : Fin (M p)) (hrow : x.row = rows J) :
    selectedCandidatePasses x s h j ↔
      ∃ t : Fin p.T, t.val < p.T ∧
        t ∈ eligibleSet x s h j rows J ∧
        q_dec p ≤ (eligiblePrefixSet x s h j rows J (t.val + 1)).card ∧
        ∀ r ∈ eligiblePrefixSet x s h j rows J (t.val + 1),
          candidateForwardSlice x s h j rows J r = true := by
  let phys := actualPhysicalBlock x s h
  have hfull := eligibleSet_eq_trueEligiblePrefix x s h j rows J hrow
  have hforward := selectedCandidateForwardSlice_eq_trueForwardBit
    x s h j rows J hrow
  constructor
  · intro hp
    rcases hp with ⟨t, ht, hpass⟩
    rcases hpass with ⟨he, hquota, hall⟩
    have htTrue : t ∈ BootstrapTruePrefixController.eligiblePrefix phys j.val p.T := by
      rw [BootstrapTruePrefixController.mem_eligiblePrefix_iff]
      exact ⟨he.1, t.isLt, he⟩
    have htSet : t ∈ eligibleSet x s h j rows J := by
      rw [hfull]
      exact htTrue
    have hprefix := eligiblePrefixSet_eq_trueEligiblePrefix
      x s h j rows J hrow (t.val + 1)
    refine ⟨t, ht, htSet, ?_, ?_⟩
    · rw [hprefix]
      exact hquota
    · intro r hr
      have hrTrue : r ∈ BootstrapTruePrefixController.eligiblePrefix phys j.val
          (t.val + 1) := by
        rw [hprefix] at hr
        exact hr
      have hbit := hall r hrTrue
      rw [hforward]
      exact hbit
  · rintro ⟨t, ht, htSet, hquota, hall⟩
    have htTrue : t ∈ BootstrapTruePrefixController.eligiblePrefix phys j.val p.T := by
      rw [← hfull]
      exact htSet
    have htrueMem :=
      (BootstrapTruePrefixController.mem_eligiblePrefix_iff phys j.val p.T t).mp htTrue
    have he : BootstrapTruePrefixController.eligible phys j.val t := htrueMem.2.2
    have hprefix := eligiblePrefixSet_eq_trueEligiblePrefix
      x s h j rows J hrow (t.val + 1)
    have hquotaTrue : q_dec p ≤
        (BootstrapTruePrefixController.eligiblePrefix phys j.val (t.val + 1)).card := by
      rw [← hprefix]
      exact hquota
    have hallTrue : BootstrapTruePrefixController.allTruePrefix phys j.val
        (t.val + 1) := by
      unfold BootstrapTruePrefixController.allTruePrefix
      intro r hr
      have hrSet : r ∈ eligiblePrefixSet x s h j rows J (t.val + 1) := by
        rw [hprefix]
        exact hr
      have hbit := hall r hrSet
      rw [hforward] at hbit
      exact hbit
    have hpass : BootstrapTruePrefixController.passesAt phys j.val t :=
      ⟨he, hquotaTrue, hallTrue⟩
    exact ⟨t, ht, hpass⟩

/-- The false-row factorization adapter exposes exactly the shared IDs, all
candidate learning rows, and the true forward row. -/
theorem falseFactorBase_coordinates
    (J : Fin (M p)) (out : PublishedOutput p) :
    (FalseRowSliceFactorization.falseRowFactorEquiv p J out).1.1 = out.1 ∧
      (FalseRowSliceFactorization.falseRowFactorEquiv p J out).1.2.1 =
        CompletePublicTable.completeRowsLearning p out.2 ∧
      (FalseRowSliceFactorization.falseRowFactorEquiv p J out).1.2.2 =
        (out.2 J).1 := by
  have h := FalseRowSliceFactorization.falseRowFactorEquiv_coordinates p J out
  exact ⟨h.1, h.2.1, h.2.2.1⟩

/-- If a false candidate's own DATA-slot bit changes at an otherwise eligible
time, membership of that time changes. The shared base and actual physical
observation are held fixed. -/
theorem falseCandidate_dataSlot_change_changes_eligibility
    (x : ReferenceInitializationRun.Input p) (s : Fin (n_boot p))
    (h : processesBlock x s) (j : ActiveIncomingFollower x s h)
    (rows rows' : CompleteRows p) (J : Fin (M p))
    (v : FalseRowSliceFactorization.FalseRow p J)
    (t : Fin p.T) (ht : t ∈ calendarBlock p s)
    (hid : (actualPhysicalBlock x s h).ids
      ((actualPhysicalBlock x s h).privateId j.val) t = false)
    (hobs : 0 < (ReferenceInitializationRun.ownEntry (actualPhysicalBlock x s h)
      (followerPlayer p.two_le_m j.val.val) t).2.val.val)
    (hdata : slotDraw ((rows v.1).2 t).1 = dataSlot)
    (hnotdata : slotDraw ((rows' v.1).2 t).1 ≠ dataSlot) :
    t ∈ eligibleSet x s h j rows v.1 ∧ t ∉ eligibleSet x s h j rows' v.1 := by
  constructor
  · rw [mem_eligibleSet_iff]
    exact ⟨ht, j.property, hid, hdata, hobs⟩
  · intro htmem
    rw [mem_eligibleSet_iff] at htmem
    rcases htmem with ⟨_, _, _, hslot, _⟩
    exact hnotdata hslot

end Bandits.Support.GeneratedForwardPrefixTests

end
