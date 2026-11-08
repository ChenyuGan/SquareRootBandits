/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceInitializationRun

/-!
# Prelaunch reference invariance under DOWN affine resampling

Sources: `sources/zip4/manuscript/appendix_b_communication.tex:724-744`,
`sources/zip4/manuscript/07_public_setup.tex:63-140`, and
`sources/zip4/manuscript/08_main_theorem.tex:29-42`.

The proof compares the existing generated reference execution when only the
DOWN affine samples are resampled. It keeps the complete continuous row and
the original private draw arrays; it creates no second execution model and
does not claim invariance of the ordinary DOWN batch or its parsed decisions.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.PublicDiscreteDraws
open Bandits.Support.CompletePublicTable
open Bandits.Support.ReferenceInitializationRun
open Bandits.Support.ReferencePrelaunchFollower
open Bandits.Support.BootstrapPhysicalBlock hiding Input run
open Bandits.Support.BootstrapPhysicalInput
open scoped Classical BigOperators

namespace Bandits.Support.ReferencePrelaunchDownInvariance

variable {p : Parameters}

def receiverFollower (i : Fin (p.m - 1)) :
    Fin (PublicDiscreteDraws.followerCount p.m) :=
  ⟨i.val, by simpa only [PublicDiscreteDraws.followerCount] using i.isLt⟩

/-- Literal agreement of the three original row coordinates read by the
prelaunch physical execution: all forward bits, the entire continuous slice,
and every UP affine sample. DOWN affine samples are unconstrained. -/
def DownCoordinateAgreement (row row' : CompleteRow p) : Prop :=
  (∀ u : Fin (A_id p), ∀ t : Fin p.T, row.1 u t = row'.1 u t) ∧
  (∀ t : Fin p.T, (row.2 t).1 = (row'.2 t).1) ∧
  (∀ t : Fin p.T, ∀ i : Fin (p.m - 1),
    (row.2 t).2 (1, i) = (row'.2 t).2 (1, i))

private theorem block_slot_eq_of_downAgreement
    {s : Fin (n_boot p)} (v : BootstrapPhysicalBlock.Input p s)
    (row' : CompleteRow p) (hrow : DownCoordinateAgreement v.row row')
    (t : Fin p.T) :
    BootstrapPhysicalBlock.slot v t =
      BootstrapPhysicalBlock.slot
        ({v with row := row'} : BootstrapPhysicalBlock.Input p s) t := by
  change PublicDiscreteDraws.slotDraw (v.row.2 t).1 =
    PublicDiscreteDraws.slotDraw (row'.2 t).1
  rw [hrow.2.1 t]

private theorem block_tuple_eq_of_downAgreement
    {s : Fin (n_boot p)} (v : BootstrapPhysicalBlock.Input p s)
    (row' : CompleteRow p) (hrow : DownCoordinateAgreement v.row row')
    (t : Fin p.T) :
    BootstrapPhysicalBlock.tuple v t =
      BootstrapPhysicalBlock.tuple
        ({v with row := row'} : BootstrapPhysicalBlock.Input p s) t := by
  unfold BootstrapPhysicalBlock.tuple
  rw [hrow.2.1 t]

private theorem block_actions_eq_of_downAgreement
    {s : Fin (n_boot p)} (v : BootstrapPhysicalBlock.Input p s)
    (row' : CompleteRow p) (hrow : DownCoordinateAgreement v.row row')
    (st : BootstrapPhysicalBlock.State p) (t : Fin p.T) :
    BootstrapPhysicalBlock.actions v st t =
      BootstrapPhysicalBlock.actions
        ({v with row := row'} : BootstrapPhysicalBlock.Input p s) st t := by
  have hslot := block_slot_eq_of_downAgreement v row' hrow t
  have hselected : BootstrapPhysicalBlock.selected v t =
      BootstrapPhysicalBlock.selected ({v with row := row'} : BootstrapPhysicalBlock.Input p s) t := by
    change PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
      (v.row.2 t).1 = PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
        (row'.2 t).1
    rw [hrow.2.1 t]
  have htuple := block_tuple_eq_of_downAgreement v row' hrow t
  have hpilot (i : Fin p.m) : BootstrapPhysicalBlock.pilot v t i =
      BootstrapPhysicalBlock.pilot ({v with row := row'} : BootstrapPhysicalBlock.Input p s) t i := by
    unfold BootstrapPhysicalBlock.pilot
    rw [hrow.2.1 t]
  have hup (i : ActiveRoundActions.Follower p.m) :
      BootstrapPhysicalBlock.initialUpBit v t i =
        BootstrapPhysicalBlock.initialUpBit
          ({v with row := row'} : BootstrapPhysicalBlock.Input p s) t i := by
    rw [BootstrapPhysicalBlock.initialUpBit_eq_offset,
      BootstrapPhysicalBlock.initialUpBit_eq_offset]
    have hindex : BootstrapPhysicalInput.sourceFollowerIndex p i = i := by
      apply Fin.ext
      rfl
    have hu := hrow.2.2 t (BootstrapPhysicalInput.sourceFollowerIndex p i)
    have hu' := congrArg Prod.snd hu
    rw [hindex] at hu'
    exact hu'
  have hproduct : BootstrapPhysicalBlock.forwardProduct v st t =
      BootstrapPhysicalBlock.forwardProduct
        ({v with row := row'} : BootstrapPhysicalBlock.Input p s) st t := by
    unfold BootstrapPhysicalBlock.forwardProduct
    apply Finset.prod_congr rfl
    intro u hu
    simp only [hrow.1 u t]
  funext i
  by_cases hi : i = ActiveRoundActions.coordinator p.two_le_m
  · subst i
    rw [BootstrapPhysicalBlock.actions_coordinator,
      BootstrapPhysicalBlock.actions_coordinator]
    simp only [BootstrapPhysicalBlock.coordinatorAction, hslot, htuple, hproduct]
  · have hleft : BootstrapPhysicalBlock.actions v st t i =
        BootstrapPhysicalBlock.followerAction v t
          (ActiveRoundActions.followerIndex p.two_le_m i hi) := by
      simp [BootstrapPhysicalBlock.actions, hi]
    have hright : BootstrapPhysicalBlock.actions
          ({v with row := row'} : BootstrapPhysicalBlock.Input p s) st t i =
        BootstrapPhysicalBlock.followerAction
          ({v with row := row'} : BootstrapPhysicalBlock.Input p s) t
          (ActiveRoundActions.followerIndex p.two_le_m i hi) := by
      simp [BootstrapPhysicalBlock.actions, hi]
    rw [hleft, hright]
    simp [BootstrapPhysicalBlock.followerAction,
      BootstrapPhysicalBlock.uninformedAction,
      BootstrapPhysicalBlock.unoccupiedAction,
      hslot, hselected, htuple, hpilot, hup]

private theorem block_feedback_eq_of_downAgreement
    {s : Fin (n_boot p)} (v : BootstrapPhysicalBlock.Input p s)
    (row' : CompleteRow p) (hrow : DownCoordinateAgreement v.row row')
    (st : BootstrapPhysicalBlock.State p) (t : Fin p.T) (i : Fin p.m) :
    BootstrapPhysicalBlock.feedback v st t i =
      BootstrapPhysicalBlock.feedback
        ({v with row := row'} : BootstrapPhysicalBlock.Input p s) st t i := by
  simp only [BootstrapPhysicalBlock.feedback,
    block_actions_eq_of_downAgreement v row' hrow st t]

private theorem block_observationIndex_eq_of_downAgreement
    {s : Fin (n_boot p)} (v : BootstrapPhysicalBlock.Input p s)
    (row' : CompleteRow p) (hrow : DownCoordinateAgreement v.row row')
    (st : BootstrapPhysicalBlock.State p) (t : Fin p.T) (i : Fin p.m) :
    BootstrapPhysicalBlock.observationIndex v st t i =
      BootstrapPhysicalBlock.observationIndex
        ({v with row := row'} : BootstrapPhysicalBlock.Input p s) st t i := by
  simp only [BootstrapPhysicalBlock.observationIndex,
    block_actions_eq_of_downAgreement v row' hrow st t]

private theorem block_step_eq_of_downAgreement
    {s : Fin (n_boot p)} (v : BootstrapPhysicalBlock.Input p s)
    (row' : CompleteRow p) (hrow : DownCoordinateAgreement v.row row')
    (st : BootstrapPhysicalBlock.State p) (t : Fin p.T) :
    BootstrapPhysicalBlock.step v st t =
      BootstrapPhysicalBlock.step
        ({v with row := row'} : BootstrapPhysicalBlock.Input p s) st t := by
  have hslot : BootstrapPhysicalBlock.slot v t =
      BootstrapPhysicalBlock.slot ({v with row := row'} : BootstrapPhysicalBlock.Input p s) t := by
    change PublicDiscreteDraws.slotDraw (v.row.2 t).1 =
      PublicDiscreteDraws.slotDraw (row'.2 t).1
    rw [hrow.2.1 t]
  have hpositive : BootstrapPhysicalBlock.discoveryPositive v st t ↔
      BootstrapPhysicalBlock.discoveryPositive
        ({v with row := row'} : BootstrapPhysicalBlock.Input p s) st t := by
    unfold BootstrapPhysicalBlock.discoveryPositive
    rw [hslot, block_feedback_eq_of_downAgreement v row' hrow st t
      (ActiveRoundActions.coordinator p.two_le_m)]
  unfold BootstrapPhysicalBlock.step
  rw [propext hpositive]

private theorem block_run_eq_of_downAgreement
    {s : Fin (n_boot p)} (v : BootstrapPhysicalBlock.Input p s)
    (row' : CompleteRow p) (hrow : DownCoordinateAgreement v.row row') (n : ℕ) :
    BootstrapPhysicalBlock.run v n =
      BootstrapPhysicalBlock.run
        ({v with row := row'} : BootstrapPhysicalBlock.Input p s) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      by_cases hn : n < p.T
      · rw [BootstrapPhysicalBlock.run_succ v ⟨n, hn⟩,
          BootstrapPhysicalBlock.run_succ
            ({v with row := row'} : BootstrapPhysicalBlock.Input p s) ⟨n, hn⟩, ih]
        exact block_step_eq_of_downAgreement v row' hrow _ ⟨n, hn⟩
      · simp only [BootstrapPhysicalBlock.run, hn, ↓reduceDIte]
        exact ih

private theorem block_ownObservation_eq_of_downAgreement
    {s : Fin (n_boot p)} (v : BootstrapPhysicalBlock.Input p s)
    (row' : CompleteRow p) (hrow : DownCoordinateAgreement v.row row')
    (i : Fin p.m) (t : Fin p.T) :
    ReferenceInitializationRun.ownObservation v i t =
      ReferenceInitializationRun.ownObservation
        ({v with row := row'} : BootstrapPhysicalBlock.Input p s) i t := by
  unfold ReferenceInitializationRun.ownObservation
  apply Subtype.ext
  apply Subtype.ext
  change BootstrapPhysicalBlock.feedback v (BootstrapPhysicalBlock.run v t.val) t i =
    BootstrapPhysicalBlock.feedback
      ({v with row := row'} : BootstrapPhysicalBlock.Input p s)
      (BootstrapPhysicalBlock.run
        ({v with row := row'} : BootstrapPhysicalBlock.Input p s) t.val) t i
  rw [block_run_eq_of_downAgreement v row' hrow t.val]
  exact block_feedback_eq_of_downAgreement v row' hrow
    (BootstrapPhysicalBlock.run
      ({v with row := row'} : BootstrapPhysicalBlock.Input p s) t.val) t i

private theorem block_ownEntry_eq_of_downAgreement
    {s : Fin (n_boot p)} (v : BootstrapPhysicalBlock.Input p s)
    (row' : CompleteRow p) (hrow : DownCoordinateAgreement v.row row')
    (i : Fin p.m) (t : Fin p.T) :
    ReferenceInitializationRun.ownEntry v i t =
      ReferenceInitializationRun.ownEntry
        ({v with row := row'} : BootstrapPhysicalBlock.Input p s) i t := by
  change (BootstrapPhysicalBlock.actions v (BootstrapPhysicalBlock.run v t.val) t i,
      ReferenceInitializationRun.ownObservation v i t) =
    (BootstrapPhysicalBlock.actions
        ({v with row := row'} : BootstrapPhysicalBlock.Input p s)
        (BootstrapPhysicalBlock.run
          ({v with row := row'} : BootstrapPhysicalBlock.Input p s) t.val) t i,
      ReferenceInitializationRun.ownObservation
        ({v with row := row'} : BootstrapPhysicalBlock.Input p s) i t)
  apply Prod.ext
  · rw [block_run_eq_of_downAgreement v row' hrow t.val]
    exact congrArg (fun a => a i) (block_actions_eq_of_downAgreement v row' hrow
        (BootstrapPhysicalBlock.run
          ({v with row := row'} : BootstrapPhysicalBlock.Input p s) t.val) t)
  · exact block_ownObservation_eq_of_downAgreement v row' hrow i t

private theorem physical_update_row
    (x : ReferenceInitializationRun.Input p) (row' : CompleteRow p)
    (b : ReferenceInitializationRun.Boundary p) (h : b.completed < n_boot p) :
    ReferenceInitializationRun.physical {x with row := row'} b h =
      {ReferenceInitializationRun.physical x b h with row := row'} := rfl

/-- Equality of the existing physical bootstrap recursion throughout one
processed block, after changing only DOWN affine samples. -/
theorem physicalRun_eq (x : ReferenceInitializationRun.Input p)
    (row' : CompleteRow p) (hrow : DownCoordinateAgreement x.row row')
    (b : ReferenceInitializationRun.Boundary p) (h : b.completed < n_boot p)
    (n : ℕ) :
    BootstrapPhysicalBlock.run (ReferenceInitializationRun.physical x b h) n =
      BootstrapPhysicalBlock.run
        (ReferenceInitializationRun.physical {x with row := row'} b h) n := by
  rw [physical_update_row x row' b h]
  exact block_run_eq_of_downAgreement _ row' hrow n

/-- The generated block's simultaneous actions are equal at every round of
the physical recursion; the UP hash uses the fixed UP channel coordinate. -/
theorem physicalActions_eq (x : ReferenceInitializationRun.Input p)
    (row' : CompleteRow p) (hrow : DownCoordinateAgreement x.row row')
    (b : ReferenceInitializationRun.Boundary p) (h : b.completed < n_boot p)
    (st : BootstrapPhysicalBlock.State p) (t : Fin p.T) :
    BootstrapPhysicalBlock.actions (ReferenceInitializationRun.physical x b h) st t =
      BootstrapPhysicalBlock.actions
        (ReferenceInitializationRun.physical {x with row := row'} b h) st t := by
  rw [physical_update_row x row' b h]
  exact block_actions_eq_of_downAgreement _ row' hrow st t

/-- The rounded grid feedback is equal when the simultaneous profiles agree. -/
theorem physicalFeedback_eq (x : ReferenceInitializationRun.Input p)
    (row' : CompleteRow p) (hrow : DownCoordinateAgreement x.row row')
    (b : ReferenceInitializationRun.Boundary p) (h : b.completed < n_boot p)
    (st : BootstrapPhysicalBlock.State p) (t : Fin p.T) (i : Fin p.m) :
    BootstrapPhysicalBlock.feedback (ReferenceInitializationRun.physical x b h) st t i =
      BootstrapPhysicalBlock.feedback
        (ReferenceInitializationRun.physical {x with row := row'} b h) st t i := by
  rw [physical_update_row x row' b h]
  exact block_feedback_eq_of_downAgreement _ row' hrow st t i

private theorem physicalObservationIndex_eq (x : ReferenceInitializationRun.Input p)
    (row' : CompleteRow p) (hrow : DownCoordinateAgreement x.row row')
    (b : ReferenceInitializationRun.Boundary p) (h : b.completed < n_boot p)
    (st : BootstrapPhysicalBlock.State p) (t : Fin p.T) (i : Fin p.m) :
    BootstrapPhysicalBlock.observationIndex (ReferenceInitializationRun.physical x b h)
      st t i =
    BootstrapPhysicalBlock.observationIndex
      (ReferenceInitializationRun.physical {x with row := row'} b h) st t i := by
  rw [physical_update_row x row' b h]
  exact block_observationIndex_eq_of_downAgreement _ row' hrow st t i

private theorem generatedCandidateRun_eq
    (x : ReferenceInitializationRun.Input p) (row' : CompleteRow p)
    (hrow : DownCoordinateAgreement x.row row')
    (b : ReferenceInitializationRun.Boundary p) (h : b.completed < n_boot p)
    (i : {i // i ∈ ReferenceInitializationRun.uninformed b}) (k : ℕ) :
    BootstrapTruePrefixController.run (ReferenceInitializationRun.physical x b h) i k =
      BootstrapTruePrefixController.run
        (ReferenceInitializationRun.physical {x with row := row'} b h) i k := by
  have hactive : (ReferenceInitializationRun.physical x b h).active i =
      (ReferenceInitializationRun.physical {x with row := row'} b h).active i := rfl
  have hid : (ReferenceInitializationRun.physical x b h).privateId i =
      (ReferenceInitializationRun.physical {x with row := row'} b h).privateId i := rfl
  induction k with
  | zero => rfl
  | succ k ih =>
      by_cases hk : k < p.T
      · let t : Fin p.T := ⟨k, hk⟩
        have hregs : BootstrapTruePrefixController.run
              (ReferenceInitializationRun.physical x b h) i t.val =
            BootstrapTruePrefixController.run
              (ReferenceInitializationRun.physical {x with row := row'} b h) i t.val := by
          simpa [t] using ih
        have hstate := physicalRun_eq x row' hrow b h t.val
        have hindex : BootstrapPhysicalBlock.observationIndex
              (ReferenceInitializationRun.physical x b h)
              (BootstrapPhysicalBlock.run (ReferenceInitializationRun.physical x b h) t.val) t
              (PublicDiscreteDraws.followerPlayer p.two_le_m i.val) =
            BootstrapPhysicalBlock.observationIndex
              (ReferenceInitializationRun.physical {x with row := row'} b h)
              (BootstrapPhysicalBlock.run
                (ReferenceInitializationRun.physical {x with row := row'} b h) t.val) t
              (PublicDiscreteDraws.followerPlayer p.two_le_m i.val) := by
          rw [hstate]
          exact physicalObservationIndex_eq x row' hrow b h
            (BootstrapPhysicalBlock.run
              (ReferenceInitializationRun.physical {x with row := row'} b h) t.val) t _
        have hslot : BootstrapPhysicalBlock.slot
              (ReferenceInitializationRun.physical x b h) t =
            BootstrapPhysicalBlock.slot
              (ReferenceInitializationRun.physical {x with row := row'} b h) t := by
          change PublicDiscreteDraws.slotDraw (x.row.2 t).1 =
            PublicDiscreteDraws.slotDraw (row'.2 t).1
          rw [hrow.2.1 t]
        have heligible : BootstrapTruePrefixController.eligible
              (ReferenceInitializationRun.physical x b h) i t ↔
            BootstrapTruePrefixController.eligible
              (ReferenceInitializationRun.physical {x with row := row'} b h) i t := by
          have hids : (ReferenceInitializationRun.physical x b h).ids =
              (ReferenceInitializationRun.physical {x with row := row'} b h).ids := rfl
          simp only [BootstrapTruePrefixController.eligible,
            hactive, hid, hids, hslot, hindex]
        have hforward : BootstrapTruePrefixController.trueForwardBit
              (ReferenceInitializationRun.physical x b h) i t =
            BootstrapTruePrefixController.trueForwardBit
              (ReferenceInitializationRun.physical {x with row := row'} b h) i t := by
          unfold BootstrapTruePrefixController.trueForwardBit
          rw [hid]
          exact hrow.1 ((ReferenceInitializationRun.physical x b h).privateId i) t
        change BootstrapTruePrefixController.run
              (ReferenceInitializationRun.physical x b h) i (t.val + 1) =
            BootstrapTruePrefixController.run
              (ReferenceInitializationRun.physical {x with row := row'} b h) i
              (t.val + 1)
        rw [BootstrapTruePrefixController.run_succ
              (ReferenceInitializationRun.physical x b h) i t,
          BootstrapTruePrefixController.run_succ
              (ReferenceInitializationRun.physical {x with row := row'} b h) i t,
          hregs]
        simp only [BootstrapTruePrefixController.advance,
          BootstrapTruePrefixController.eligibleFlag, propext heligible, hforward]
      · simp only [BootstrapTruePrefixController.run, hk, ↓reduceDIte, ih]

/-- The true-row candidate registers and save events are generated from the
same physical observations and are unchanged by DOWN resampling. -/
theorem trueCandidateRun_eq (x : ReferenceInitializationRun.Input p)
    (row' : CompleteRow p) (hrow : DownCoordinateAgreement x.row row')
    (b : ReferenceInitializationRun.Boundary p) (h : b.completed < n_boot p)
    (i : {i // i ∈ ReferenceInitializationRun.uninformed b}) (k : ℕ) :
    BootstrapTruePrefixController.run (ReferenceInitializationRun.physical x b h) i k =
      BootstrapTruePrefixController.run
        (ReferenceInitializationRun.physical {x with row := row'} b h) i k := by
  exact generatedCandidateRun_eq x row' hrow b h i k

/-- The physical all-slot held-arm gain, including positives after a save,
agrees on both resampled block inputs. -/
theorem physicalStayGain_eq (x : ReferenceInitializationRun.Input p)
    (row' : CompleteRow p) (hrow : DownCoordinateAgreement x.row row')
    (b : ReferenceInitializationRun.Boundary p) (h : b.completed < n_boot p)
    (i : {i // i ∈ ReferenceInitializationRun.uninformed b}) :
    BootstrapPhysicalBlock.physicalStayGain
        (ReferenceInitializationRun.physical x b h) i =
      BootstrapPhysicalBlock.physicalStayGain
        (ReferenceInitializationRun.physical {x with row := row'} b h) i := by
  have hrounds : BootstrapPhysicalBlock.physicalStayRounds
      (ReferenceInitializationRun.physical x b h) i =
    BootstrapPhysicalBlock.physicalStayRounds
      (ReferenceInitializationRun.physical {x with row := row'} b h) i := by
    classical
    apply Finset.ext
    intro t
    simp only [BootstrapPhysicalBlock.physicalStayRounds, Finset.mem_filter]
    constructor
    · rintro ⟨ht, hid, hpos⟩
      refine ⟨ht, hid, ?_⟩
      have hstate := physicalRun_eq x row' hrow b h t.val
      rw [hstate] at hpos
      rw [physicalFeedback_eq x row' hrow b h
        (BootstrapPhysicalBlock.run
          (ReferenceInitializationRun.physical {x with row := row'} b h) t.val) t
        (PublicDiscreteDraws.followerPlayer p.two_le_m i.val)] at hpos
      exact hpos
    · rintro ⟨ht, hid, hpos⟩
      refine ⟨ht, hid, ?_⟩
      have hstate := physicalRun_eq x row' hrow b h t.val
      rw [← hstate] at hpos
      rw [← physicalFeedback_eq x row' hrow b h
        (BootstrapPhysicalBlock.run (ReferenceInitializationRun.physical x b h) t.val) t
        (PublicDiscreteDraws.followerPlayer p.two_le_m i.val)] at hpos
      exact hpos
  have hactive : (ReferenceInitializationRun.physical x b h).active i =
      (ReferenceInitializationRun.physical {x with row := row'} b h).active i := rfl
  simp only [BootstrapPhysicalBlock.physicalStayGain, hrounds, hactive]

private theorem weightInput_eq_of_downAgreement
    (x : ReferenceInitializationRun.Input p) (row' : CompleteRow p)
    (hrow : DownCoordinateAgreement x.row row')
    (b : ReferenceInitializationRun.Boundary p) (h : b.completed < n_boot p)
    (i : {i // i ∈ ReferenceInitializationRun.uninformed b}) :
    ReferenceInitializationRun.weightInput x b h i =
      ReferenceInitializationRun.weightInput {x with row := row'} b h i := by
  have ha : (ReferenceInitializationRun.physical x b h).active i =
      (ReferenceInitializationRun.physical {x with row := row'} b h).active i := rfl
  have hh : (ReferenceInitializationRun.physical x b h).held i =
      (ReferenceInitializationRun.physical {x with row := row'} b h).held i := rfl
  have hid : (ReferenceInitializationRun.physical x b h).privateId i =
      (ReferenceInitializationRun.physical {x with row := row'} b h).privateId i := rfl
  have hids : (ReferenceInitializationRun.physical x b h).ids =
      (ReferenceInitializationRun.physical {x with row := row'} b h).ids := rfl
  have hs : BootstrapTruePrefixController.savedAt
        (ReferenceInitializationRun.physical x b h) i =
      BootstrapTruePrefixController.savedAt
        (ReferenceInitializationRun.physical {x with row := row'} b h) i := by
    funext t
    change decide ((BootstrapTruePrefixController.run
          (ReferenceInitializationRun.physical x b h) i t.val).pending = false ∧
        (BootstrapTruePrefixController.run
          (ReferenceInitializationRun.physical x b h) i (t.val + 1)).pending = true) =
      decide ((BootstrapTruePrefixController.run
          (ReferenceInitializationRun.physical {x with row := row'} b h) i t.val).pending = false ∧
        (BootstrapTruePrefixController.run
          (ReferenceInitializationRun.physical {x with row := row'} b h) i (t.val + 1)).pending = true)
    rw [trueCandidateRun_eq x row' hrow b h i t.val,
      trueCandidateRun_eq x row' hrow b h i (t.val + 1)]
  have ho : (fun t : Fin p.T => if t ∈ calendarBlock p (ReferenceInitializationRun.nextBlock b h) then
        BootstrapPhysicalBlock.observationIndex
          (ReferenceInitializationRun.physical x b h)
          (BootstrapPhysicalBlock.run (ReferenceInitializationRun.physical x b h) t.val) t
          (PublicDiscreteDraws.followerPlayer p.two_le_m i.val)
        else ⟨0, Nat.zero_lt_succ _⟩) =
      (fun t : Fin p.T => if t ∈ calendarBlock p (ReferenceInitializationRun.nextBlock b h) then
        BootstrapPhysicalBlock.observationIndex
          (ReferenceInitializationRun.physical {x with row := row'} b h)
          (BootstrapPhysicalBlock.run
            (ReferenceInitializationRun.physical {x with row := row'} b h) t.val) t
          (PublicDiscreteDraws.followerPlayer p.two_le_m i.val)
        else ⟨0, Nat.zero_lt_succ _⟩) := by
    funext t
    split_ifs with ht
    · have hstate := physicalRun_eq x row' hrow b h t.val
      rw [hstate]
      exact physicalObservationIndex_eq x row' hrow b h
        (BootstrapPhysicalBlock.run
          (ReferenceInitializationRun.physical {x with row := row'} b h) t.val) t _
    · rfl
  unfold ReferenceInitializationRun.weightInput
  congr 1
  simp only [BootstrapTruePrefixController.observationTrace,
    BootstrapPhysicalBlock.observationTrace, ha, hh, hid, hids, hs, ho]

private theorem updatedNumerators_eq_of_downAgreement
    (x : ReferenceInitializationRun.Input p) (row' : CompleteRow p)
    (hrow : DownCoordinateAgreement x.row row')
    (b : ReferenceInitializationRun.Boundary p) (h : b.completed < n_boot p) :
    ReferenceInitializationRun.updatedNumerators x b h =
      ReferenceInitializationRun.updatedNumerators {x with row := row'} b h := by
  funext j
  unfold ReferenceInitializationRun.updatedNumerators
  dsimp only
  split_ifs with hi
  · rw [weightInput_eq_of_downAgreement x row' hrow b h]
  · rfl

private theorem declaredActivation_eq_of_downAgreement
    (x : ReferenceInitializationRun.Input p) (row' : CompleteRow p)
    (hrow : DownCoordinateAgreement x.row row')
    (b : ReferenceInitializationRun.Boundary p) (h : b.completed < n_boot p) :
    ReferenceInitializationRun.declaredActivation x b h =
      ReferenceInitializationRun.declaredActivation {x with row := row'} b h := by
  funext i
  unfold ReferenceInitializationRun.declaredActivation
  by_cases hi : i ∈ ReferenceInitializationRun.uninformed b
  · simp only [dite_eq_left hi]
    have hc := trueCandidateRun_eq x row' hrow b h ⟨i, hi⟩ p.T
    simp only [ReferenceInitializationRun.candidate, hc]
    rfl
  · simp only [dite_eq_right hi]

private theorem updatedCounters_eq_of_downAgreement
    (x : ReferenceInitializationRun.Input p) (row' : CompleteRow p)
    (hrow : DownCoordinateAgreement x.row row')
    (b : ReferenceInitializationRun.Boundary p) (h : b.completed < n_boot p) :
    ReferenceInitializationRun.updatedCounters x b h =
      ReferenceInitializationRun.updatedCounters {x with row := row'} b h := by
  funext a
  unfold ReferenceInitializationRun.updatedCounters
  congr 1
  apply Finset.sum_congr rfl
  intro t ht
  have hstate := physicalRun_eq x row' hrow b h t.val
  have hfeedback : BootstrapPhysicalBlock.feedback
        (ReferenceInitializationRun.physical x b h)
        (BootstrapPhysicalBlock.run (ReferenceInitializationRun.physical x b h) t.val) t
        (ActiveRoundActions.coordinator p.two_le_m) =
      BootstrapPhysicalBlock.feedback
        (ReferenceInitializationRun.physical {x with row := row'} b h)
        (BootstrapPhysicalBlock.run
          (ReferenceInitializationRun.physical {x with row := row'} b h) t.val) t
        (ActiveRoundActions.coordinator p.two_le_m) := by
    rw [hstate]
    exact physicalFeedback_eq x row' hrow b h
      (BootstrapPhysicalBlock.run (ReferenceInitializationRun.physical {x with row := row'} b h) t.val)
      t (ActiveRoundActions.coordinator p.two_le_m)
  have hslot : BootstrapPhysicalBlock.slot (ReferenceInitializationRun.physical x b h) t =
      BootstrapPhysicalBlock.slot
        (ReferenceInitializationRun.physical {x with row := row'} b h) t := by
    rw [physical_update_row x row' b h]
    exact block_slot_eq_of_downAgreement _ row' hrow t
  have htuple : BootstrapPhysicalBlock.tuple (ReferenceInitializationRun.physical x b h) t =
      BootstrapPhysicalBlock.tuple
        (ReferenceInitializationRun.physical {x with row := row'} b h) t := by
    rw [physical_update_row x row' b h]
    exact block_tuple_eq_of_downAgreement _ row' hrow t
  simp only [ReferenceInitializationRun.downArm, hslot, hfeedback, htuple]
  rfl

private theorem crosses_eq_of_downAgreement
    (x : ReferenceInitializationRun.Input p) (row' : CompleteRow p)
    (hrow : DownCoordinateAgreement x.row row')
    (b : ReferenceInitializationRun.Boundary p) (h : b.completed < n_boot p) :
    ReferenceInitializationRun.crosses x b h =
      ReferenceInitializationRun.crosses {x with row := row'} b h := by
  simp only [ReferenceInitializationRun.crosses,
    updatedCounters_eq_of_downAgreement x row' hrow b h]

private theorem forced_eq_of_downAgreement
    (x : ReferenceInitializationRun.Input p) (row' : CompleteRow p)
    (hrow : DownCoordinateAgreement x.row row')
    (b : ReferenceInitializationRun.Boundary p) (h : b.completed < n_boot p) :
    ReferenceInitializationRun.forced x b h =
      ReferenceInitializationRun.forced {x with row := row'} b h := by
  funext i
  simp only [ReferenceInitializationRun.forced,
    crosses_eq_of_downAgreement x row' hrow b h,
    declaredActivation_eq_of_downAgreement x row' hrow b h]

private theorem finishBlock_eq_of_downAgreement
    (x : ReferenceInitializationRun.Input p) (row' : CompleteRow p)
    (hrow : DownCoordinateAgreement x.row row')
    (b : ReferenceInitializationRun.Boundary p) (h : b.completed < n_boot p) :
    ReferenceInitializationRun.finishBlock x b h =
      ReferenceInitializationRun.finishBlock {x with row := row'} b h := by
  have hext : ReferenceInitializationRun.extendedHistory x b h =
      ReferenceInitializationRun.extendedHistory {x with row := row'} b h := by
    funext i t
    unfold ReferenceInitializationRun.extendedHistory
    split_ifs with ht
    · rfl
    · have hrowv : DownCoordinateAgreement
          (ReferenceInitializationRun.physical x b h).row row' := by
        simpa [ReferenceInitializationRun.physical, BootstrapPhysicalInput.blockInput] using hrow
      exact block_ownEntry_eq_of_downAgreement
        (ReferenceInitializationRun.physical x b h) row' hrowv i
        ⟨t.val, Nat.lt_of_lt_of_le t.isLt (ReferenceInitializationRun.elapsed_le_T p _)⟩
  have hnum := updatedNumerators_eq_of_downAgreement x row' hrow b h
  have hdecl := declaredActivation_eq_of_downAgreement x row' hrow b h
  have hcount := updatedCounters_eq_of_downAgreement x row' hrow b h
  have hcross := crosses_eq_of_downAgreement x row' hrow b h
  have hforced := forced_eq_of_downAgreement x row' hrow b h
  have hfinal : ReferenceInitializationRun.finalActivation x b h =
      ReferenceInitializationRun.finalActivation {x with row := row'} b h := by
    funext i
    simp only [ReferenceInitializationRun.finalActivation, hforced,
      hdecl]
  unfold ReferenceInitializationRun.finishBlock
  simp only [hext, hnum, hfinal, hcount, hcross, hforced]

private theorem advance_eq_of_downAgreement
    (x : ReferenceInitializationRun.Input p) (row' : CompleteRow p)
    (hrow : DownCoordinateAgreement x.row row') (b : ReferenceInitializationRun.Boundary p) :
    ReferenceInitializationRun.advance x b =
      ReferenceInitializationRun.advance {x with row := row'} b := by
  unfold ReferenceInitializationRun.advance
  split_ifs with hc hb
  · rfl
  · exact finishBlock_eq_of_downAgreement x row' hrow b hb
  · rfl

/-- Every block boundary in the generated prelaunch execution is invariant
under resampling only the DOWN affine coordinates. This includes the stopped
state after strict launch crossing and the final clipped `T` boundary. -/
theorem run_eq (x : ReferenceInitializationRun.Input p) (row' : CompleteRow p)
    (hrow : DownCoordinateAgreement x.row row') (r : ℕ) :
    ReferenceInitializationRun.run x r =
      ReferenceInitializationRun.run {x with row := row'} r := by
  induction r with
  | zero => rfl
  | succ r ih =>
      rw [ReferenceInitializationRun.run_succ x r,
        ReferenceInitializationRun.run_succ {x with row := row'} r, ih]
      exact advance_eq_of_downAgreement x row' hrow _

/-- The existing generated output boundary is invariant under DOWN resampling. -/
theorem output_eq (x : ReferenceInitializationRun.Input p) (row' : CompleteRow p)
    (hrow : DownCoordinateAgreement x.row row') :
    ReferenceInitializationRun.output x =
      ReferenceInitializationRun.output {x with row := row'} := by
  exact run_eq x row' hrow (n_boot p)

/-- The source launch round, including the `T + 1` no-launch sentinel, is
unchanged by DOWN resampling. -/
theorem launchRound_eq (x : ReferenceInitializationRun.Input p)
    (row' : CompleteRow p) (hrow : DownCoordinateAgreement x.row row') :
    ReferenceInitializationRun.launchRound x =
      ReferenceInitializationRun.launchRound {x with row := row'} := by
  simp only [ReferenceInitializationRun.launchRound,
    output_eq x row' hrow]

/-- The exact original DOWN receiver selection gate reads activation time,
continuous slot and selected-follower coordinates. It is invariant even
though the affine DOWN sample itself may change. -/
theorem downSelected_eq (i : Fin (p.m - 1)) (row row' : CompleteRow p)
    (hrow : DownCoordinateAgreement row row') (alpha : Activation p)
    (t : Fin p.T) (own : Fin p.K × Observation p) :
    (ReferencePrelaunchFollower.downInput i row alpha t own).selected =
      (ReferencePrelaunchFollower.downInput i row' alpha t own).selected := by
  unfold ReferencePrelaunchFollower.downInput
  simp only [hrow.2.1 t]

/-- Original ordinary prelaunch receiver-positive times read from the actual
generated physical history. The filter uses `downInput.selected` and that
receiver's own physically generated positive observation. -/
def selectedPositiveTimes (x : ReferenceInitializationRun.Input p)
    (b : ReferenceInitializationRun.Boundary p) (i : Fin (p.m - 1))
    (alpha : Activation p) : Finset (Fin p.T) :=
  Finset.univ.filter fun t =>
    ∃ ht : t.val < ReferenceInitializationRun.elapsed p b.completed,
      let u : Fin (ReferenceInitializationRun.elapsed p b.completed) := ⟨t.val, ht⟩
      let calendarTime := ReferencePrelaunchFollower.calendar
        (ReferenceInitializationRun.elapsed_le_T p b.completed) u
      (ReferencePrelaunchFollower.downInput i x.row alpha calendarTime
        (b.history (PublicDiscreteDraws.followerPlayer p.two_le_m (receiverFollower i)) u)).selected = true ∧
        0 < ((b.history (PublicDiscreteDraws.followerPlayer p.two_le_m (receiverFollower i)) u).2).val.val

/-- The original receiver's selected, physically positive DOWN tests agree on
the actual generated histories. `halpha` identifies the ordinary receiver's
activation time at the boundary; no positivity policy is supplied externally. -/
private theorem selectedPositiveTimes_sameBoundary_eq
    (x x' : ReferenceInitializationRun.Input p)
    (hrow : DownCoordinateAgreement x.row x'.row)
    (b : ReferenceInitializationRun.Boundary p) (i : Fin (p.m - 1))
    (alpha : Activation p) :
    selectedPositiveTimes x b i alpha = selectedPositiveTimes x' b i alpha := by
  classical
  apply Finset.ext
  intro t
  simp only [selectedPositiveTimes, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨ht, hselected, hpositive⟩
    let u : Fin (ReferenceInitializationRun.elapsed p b.completed) := ⟨t.val, ht⟩
    let calendarTime := ReferencePrelaunchFollower.calendar
      (ReferenceInitializationRun.elapsed_le_T p b.completed) u
    let player := PublicDiscreteDraws.followerPlayer p.two_le_m (receiverFollower i)
    have hs := downSelected_eq i x.row x'.row hrow alpha calendarTime (b.history player u)
    have hselected' : (ReferencePrelaunchFollower.downInput i x'.row alpha calendarTime
        (b.history player u)).selected = true := by
      change (ReferencePrelaunchFollower.downInput i x.row alpha calendarTime
        (b.history player u)).selected = true at hselected
      rw [← hs]
      exact hselected
    refine ⟨ht, ?_⟩
    change (ReferencePrelaunchFollower.downInput i x'.row alpha calendarTime
        (b.history player u)).selected = true ∧
      0 < (b.history player u).2.val.val
    exact ⟨hselected', hpositive⟩
  · rintro ⟨ht, hselected, hpositive⟩
    let u : Fin (ReferenceInitializationRun.elapsed p b.completed) := ⟨t.val, ht⟩
    let calendarTime := ReferencePrelaunchFollower.calendar
      (ReferenceInitializationRun.elapsed_le_T p b.completed) u
    let player := PublicDiscreteDraws.followerPlayer p.two_le_m (receiverFollower i)
    have hs := downSelected_eq i x.row x'.row hrow alpha calendarTime (b.history player u)
    have hselected' : (ReferencePrelaunchFollower.downInput i x.row alpha calendarTime
        (b.history player u)).selected = true := by
      change (ReferencePrelaunchFollower.downInput i x'.row alpha calendarTime
        (b.history player u)).selected = true at hselected
      rw [hs]
      exact hselected
    refine ⟨ht, ?_⟩
    change (ReferencePrelaunchFollower.downInput i x.row alpha calendarTime
        (b.history player u)).selected = true ∧
      0 < (b.history player u).2.val.val
    exact ⟨hselected', hpositive⟩

theorem selectedPositiveTimes_eq (x : ReferenceInitializationRun.Input p)
    (row' : CompleteRow p) (hrow : DownCoordinateAgreement x.row row')
    (r : ℕ) (i : Fin (p.m - 1)) (alpha : Activation p)
    (halpha : (ReferenceInitializationRun.run x r).activation i = some alpha) :
    selectedPositiveTimes x (ReferenceInitializationRun.run x r) i alpha =
      selectedPositiveTimes {x with row := row'}
        (ReferenceInitializationRun.run {x with row := row'} r) i alpha ∧
      (ReferenceInitializationRun.run {x with row := row'} r).activation i = some alpha := by
  have hb := run_eq x row' hrow r
  constructor
  · rw [hb]
    exact selectedPositiveTimes_sameBoundary_eq x {x with row := row'} hrow
      (ReferenceInitializationRun.run {x with row := row'} r) i alpha
  · rw [← hb]
    exact halpha

end Bandits.Support.ReferencePrelaunchDownInvariance

end
