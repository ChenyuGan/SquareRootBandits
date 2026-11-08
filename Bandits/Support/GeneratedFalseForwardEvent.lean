/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.GeneratedEligibleFamily

/-!
# Actual generated false-forward events

The actual event is defined on the published-output and original private-
coordinate carrier. Its reference input is the selected row in that same
output, and a block context exists only when the stopped run processes it and
the incoming follower is active.

Sources: `sources/zip4/manuscript/appendix_b_communication.tex:101-126,294-338`
and `sources/zip4/manuscript/07_public_setup.tex:123-140`.

These are deterministic event-identity and measurability constructions. They
prove no conditional private-ID law, probability bound, or manuscript closure.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.CompletePublicTable
open Bandits.Support.ActiveRoundActions
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.ReferencePrelaunchFollower
open Bandits.Support.ReferenceInitializationRun
open Bandits.Support.GeneratedForwardPrefixTests
open Bandits.Support.ForwardPrefixSlice
open Bandits.Support.FalseForwardBaseTail
open Bandits.Support.FalseRowSliceFactorization
open Bandits.Support.GeneratedEligibleFamily
open scoped Classical

namespace Bandits.Support.GeneratedFalseForwardEvent

variable {p : Parameters}

/-- The literal dependent existential false-forward event on the published
output and original private-coordinate carrier. The reference input is
constructed from the same output `P`; no alternate rows or default block are
introduced. -/
def actualFalseForwardPrefixPassSet
    (C_star C_h : ℝ) (eta : LearningRate)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (J : Fin (M p))
    (s : Fin (n_boot p)) (i : Follower p.m) :
    Set (PublishedOutput p × ExtendedPrivateCoordinates p) :=
  {z | ∃ h : GeneratedForwardPrefixTests.processesBlock
        (referenceInputOfPublishedOutput C_star C_h eta rewards J z) s,
      ∃ j : GeneratedForwardPrefixTests.ActiveIncomingFollower
        (referenceInputOfPublishedOutput C_star C_h eta rewards J z) s h,
        j.val.val = i ∧
          GeneratedForwardPrefixTests.existsFalseForwardPrefixPass
            (referenceInputOfPublishedOutput C_star C_h eta rewards J z)
            s h j (CompletePublicTable.publishedRows p z.1) J}

/-- The output-side active/private-ID code is present exactly when the
generated stopped run processes the block and has an active incoming context
for this follower, with the same actual private ID. -/
theorem activePrivateIDCodeOnPublishedOutput_eq_some_iff_actualContext
    (C_star C_h : ℝ) (eta : LearningRate)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (J : Fin (M p))
    (P : PublishedOutput p) (rho : ExtendedPrivateCoordinates p)
    (s : Fin (n_boot p)) (i : Follower p.m) (u : Fin (A_id p)) :
    activePrivateIDCodeOnPublishedOutput C_star C_h eta rewards J s i (P, rho) = some u ↔
      ∃ h : GeneratedForwardPrefixTests.processesBlock
          (referenceInputOfPublishedOutput C_star C_h eta rewards J (P, rho)) s,
        ∃ j : GeneratedForwardPrefixTests.ActiveIncomingFollower
          (referenceInputOfPublishedOutput C_star C_h eta rewards J (P, rho)) s h,
          j.val.val = i ∧
            (GeneratedForwardPrefixTests.actualPhysicalBlock
              (referenceInputOfPublishedOutput C_star C_h eta rewards J (P, rho)) s h).privateId
              j.val = u := by
  classical
  let base := (FalseRowSliceFactorization.falseRowFactorEquiv p J P).1
  let zbase : FalseFactorBase p × ExtendedPrivateCoordinates p := (base, rho)
  let xBase := referenceInputOfBase C_star C_h eta rewards J zbase
  let x := referenceInputOfPublishedOutput C_star C_h eta rewards J (P, rho)
  have hx : xBase = x :=
    referenceInputOfBase_eq_publishedOutput C_star C_h eta rewards J P rho
  have hbaseContext :
      (activePrivateIDCode C_star C_h eta rewards J s i zbase = some u) ↔
        ∃ h : GeneratedForwardPrefixTests.processesBlock xBase s,
          ∃ j : GeneratedForwardPrefixTests.ActiveIncomingFollower xBase s h,
            j.val.val = i ∧
              (GeneratedForwardPrefixTests.actualPhysicalBlock xBase s h).privateId
                j.val = u := by
    constructor
    · intro hc
      let b := ReferenceInitializationRun.run xBase s.val
      change activePrivateIDCodeAtBoundary C_star C_h eta rewards J s i b zbase = some u at hc
      unfold activePrivateIDCodeAtBoundary at hc
      by_cases hguard : b.crossing = none ∧ b.completed = s.val
      · simp only [dite_eq_left hguard] at hc
        let h : GeneratedForwardPrefixTests.processesBlock xBase s := hguard
        let hremCode := GeneratedEligibleFamily.processedBoundaryRemaining s b hguard
        let physCode : BootstrapPhysicalBlock.Input p
            (ReferenceInitializationRun.nextBlock b hremCode) :=
          ReferenceInitializationRun.physical
            (referenceInputOfBase C_star C_h eta rewards J zbase) b hremCode
        let hrem := GeneratedForwardPrefixTests.actualBlockRemaining xBase s h
        let phys : BootstrapPhysicalBlock.Input p
            (ReferenceInitializationRun.nextBlock
              (GeneratedForwardPrefixTests.actualBoundary xBase s) hrem) :=
          ReferenceInitializationRun.physical xBase
            (GeneratedForwardPrefixTests.actualBoundary xBase s) hrem
        have hremEq : hremCode = hrem := Subsingleton.elim _ _
        have hphysEq : physCode = phys := by
          cases hremEq
          rfl
        have hindex := GeneratedForwardPrefixTests.actualBlockIndex xBase s h
        by_cases hin : i ∈
            (ReferenceInitializationRun.physical
              (referenceInputOfBase C_star C_h eta rewards J zbase) b
              (GeneratedEligibleFamily.processedBoundaryRemaining s b hguard)).uninformed
        · let incoming : {q // q ∈
              (ReferenceInitializationRun.physical
                (referenceInputOfBase C_star C_h eta rewards J zbase) b
                (GeneratedEligibleFamily.processedBoundaryRemaining s b hguard)).uninformed} :=
            ⟨i, hin⟩
          simp [hin] at hc
          rcases hc with ⟨haCode, hidCode⟩
          let incomingAtActualBoundary : {q // q ∈ phys.uninformed} :=
            hphysEq ▸ incoming
          have ha : phys.active incomingAtActualBoundary = true := by
            cases hphysEq
            exact haCode
          have hid : phys.privateId incomingAtActualBoundary = u := by
            cases hphysEq
            exact hidCode
          let incomingActual := GeneratedEligibleFamily.castPhysicalFollower
            hindex phys incomingAtActualBoundary
          have hactiveActual :
              (hindex ▸ phys).active incomingActual = true := by
            rw [GeneratedEligibleFamily.castPhysicalFollower_active]
            exact ha
          let j : GeneratedForwardPrefixTests.ActiveIncomingFollower xBase s h :=
            ⟨incomingActual, by
              change (hindex ▸ phys).active incomingActual = true
              exact hactiveActual⟩
          have hincomingVal : incomingAtActualBoundary.val = i := by
            dsimp [incomingAtActualBoundary]
          have hcastVal : incomingActual.val = incomingAtActualBoundary.val := rfl
          have hji : j.val.val = i := by
            change incomingActual.val = i
            exact hcastVal.trans hincomingVal
          have hidActual :
              (GeneratedForwardPrefixTests.actualPhysicalBlock xBase s h).privateId j.val = u := by
            change (hindex ▸ phys).privateId incomingActual = u
            rw [GeneratedEligibleFamily.castPhysicalFollower_privateID]
            exact hid
          exact ⟨h, j, hji, hidActual⟩
        · simp [hin] at hc
      · simp [hguard] at hc
    · rintro ⟨h, j, hji, hid⟩
      have hc := activePrivateIDCode_eq_actualPrivateID
        C_star C_h eta rewards J s zbase h j
      rw [hji, hid] at hc
      exact hc
  constructor
  · intro hc
    change activePrivateIDCode C_star C_h eta rewards J s i zbase = some u at hc
    rcases hbaseContext.mp hc with ⟨hBase, jBase, hji, hid⟩
    cases hx
    exact ⟨hBase, jBase, hji, hid⟩
  · rintro ⟨h, j, hji, hid⟩
    cases hx
    exact hbaseContext.mpr ⟨h, j, hji, hid⟩

/-- The actual dependent existential event agrees pointwise with the existing
finite union over false-row and private-ID labels. A virtual label is realized
only by the actual active context, and its tests use the same published rows,
observations, private ID, and first-quota prefix. -/
theorem actualFalseForwardPrefixPass_iff_mem_virtualUnion
    (C_star C_h : ℝ) (eta : LearningRate)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (J : Fin (M p))
    (s : Fin (n_boot p)) (i : Follower p.m)
    (P : PublishedOutput p) (rho : ExtendedPrivateCoordinates p) :
    (P, rho) ∈ actualFalseForwardPrefixPassSet C_star C_h eta rewards J s i ↔
      (P, rho) ∈ virtualExistsFalseForwardPrefixPassSet C_star C_h eta rewards J s i := by
  classical
  let x := referenceInputOfPublishedOutput C_star C_h eta rewards J (P, rho)
  change (∃ h : GeneratedForwardPrefixTests.processesBlock x s,
      ∃ j : GeneratedForwardPrefixTests.ActiveIncomingFollower x s h,
        j.val.val = i ∧
          GeneratedForwardPrefixTests.existsFalseForwardPrefixPass x s h j
            (CompletePublicTable.publishedRows p P) J) ↔
    (P, rho) ∈ virtualExistsFalseForwardPrefixPassSet C_star C_h eta rewards J s i
  constructor
  · rintro ⟨h, j, hji, hpass⟩
    rcases hpass with ⟨v, hcandidate⟩
    let u := (GeneratedForwardPrefixTests.actualPhysicalBlock x s h).privateId j.val
    let label : SliceLabel p := (v.1, u)
    have hcode :
        activePrivateIDCodeOnPublishedOutput C_star C_h eta rewards J s i (P, rho) = some u := by
      have hcodeJ := activePrivateIDCodeOnPublishedOutput_eq_actualPrivateID
        C_star C_h eta rewards J P rho s h j
      rw [hji] at hcodeJ
      simpa [u] using hcodeJ
    have hid : label.2 =
        (GeneratedForwardPrefixTests.actualPhysicalBlock x s h).privateId j.val := rfl
    have hfactorAtJ : (FalseRowSliceFactorization.falseRowFactorEquiv p J P, rho) ∈
        FalseForwardBaseTail.factorFalseForwardPassSet
          (family C_star C_h eta rewards J s j.val.val) J label v.2 :=
      (factorPass_iff_generatedFalseCandidatePasses C_star C_h eta rewards J
        P rho s h j label v.2 hid).2 hcandidate
    have hfactor : (FalseRowSliceFactorization.falseRowFactorEquiv p J P, rho) ∈
        FalseForwardBaseTail.factorFalseForwardPassSet
          (family C_star C_h eta rewards J s i) J label v.2 := by
      simpa only [hji] using hfactorAtJ
    have hfalse : label.1 ≠ J := v.2
    rw [virtualExistsFalseForwardPrefixPassSet]
    apply Set.mem_iUnion.mpr
    refine ⟨label, ?_⟩
    simp [virtualFalseForwardLabelSet, label, hfalse, hfactor, hcode]
  · intro hmem
    rw [virtualExistsFalseForwardPrefixPassSet] at hmem
    rcases Set.mem_iUnion.mp hmem with ⟨label, hlabel⟩
    by_cases hfalse : label.1 ≠ J
    · have hparts :
          (FalseRowSliceFactorization.falseRowFactorEquiv p J P, rho) ∈
            FalseForwardBaseTail.factorFalseForwardPassSet
              (family C_star C_h eta rewards J s i) J label hfalse ∧
            activePrivateIDCodeOnPublishedOutput C_star C_h eta rewards J s i
              (P, rho) = some label.2 := by
        simpa [virtualFalseForwardLabelSet, hfalse] using hlabel
      rcases (activePrivateIDCodeOnPublishedOutput_eq_some_iff_actualContext
        C_star C_h eta rewards J P rho s i label.2).mp hparts.2 with
        ⟨h, j, hji, hid⟩
      have hfactorAtJ : (FalseRowSliceFactorization.falseRowFactorEquiv p J P, rho) ∈
          FalseForwardBaseTail.factorFalseForwardPassSet
            (family C_star C_h eta rewards J s j.val.val) J label hfalse := by
        have hsetEq :
            FalseForwardBaseTail.factorFalseForwardPassSet
                (family C_star C_h eta rewards J s j.val.val) J label hfalse =
              FalseForwardBaseTail.factorFalseForwardPassSet
                (family C_star C_h eta rewards J s i) J label hfalse := by
          rw [hji]
        exact hsetEq.symm ▸ hparts.1
      have hcandidate := (factorPass_iff_generatedFalseCandidatePasses
        C_star C_h eta rewards J P rho s h j label hfalse hid.symm).1 hfactorAtJ
      exact ⟨h, j, hji, ⟨⟨label.1, hfalse⟩, hcandidate⟩⟩
    · simp [virtualFalseForwardLabelSet, hfalse] at hlabel

/-- Set equality between the literal actual event and the guarded virtual
label union. -/
theorem actualFalseForwardPrefixPassSet_eq_virtualUnion
    (C_star C_h : ℝ) (eta : LearningRate)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (J : Fin (M p))
    (s : Fin (n_boot p)) (i : Follower p.m) :
    actualFalseForwardPrefixPassSet C_star C_h eta rewards J s i =
      virtualExistsFalseForwardPrefixPassSet C_star C_h eta rewards J s i := by
  ext z
  rcases z with ⟨P, rho⟩
  exact actualFalseForwardPrefixPass_iff_mem_virtualUnion
    C_star C_h eta rewards J s i P rho

/-- Measurability of the actual dependent existential event on the same
published-output and original private-coordinate carrier. -/
theorem measurableSet_actualFalseForwardPrefixPassSet
    (C_star C_h : ℝ) (eta : LearningRate)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (J : Fin (M p))
    (s : Fin (n_boot p)) (i : Follower p.m) :
    MeasurableSet (actualFalseForwardPrefixPassSet C_star C_h eta rewards J s i) := by
  rw [actualFalseForwardPrefixPassSet_eq_virtualUnion]
  exact measurableSet_virtualExistsFalseForwardPrefixPassSet
    C_star C_h eta rewards J s i

/-- The finite union of the same actual dependent existential event over all
source blocks and followers, retaining each selected-output reference run and
its complete observation tests. -/
def actualAnyFalseForwardPrefixPassSet
    (C_star C_h : ℝ) (eta : LearningRate)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (J : Fin (M p)) :
    Set (PublishedOutput p × ExtendedPrivateCoordinates p) :=
  ⋃ s : Fin (n_boot p), ⋃ i : Follower p.m,
    actualFalseForwardPrefixPassSet C_star C_h eta rewards J s i

/-- Measurability of the finite union over all blocks and followers on the
same published-output and private-coordinate carrier. -/
theorem measurableSet_actualAnyFalseForwardPrefixPassSet
    (C_star C_h : ℝ) (eta : LearningRate)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (J : Fin (M p)) :
    MeasurableSet (actualAnyFalseForwardPrefixPassSet C_star C_h eta rewards J) := by
  rw [actualAnyFalseForwardPrefixPassSet]
  exact MeasurableSet.iUnion fun s =>
    MeasurableSet.iUnion fun i =>
      measurableSet_actualFalseForwardPrefixPassSet C_star C_h eta rewards J s i

end Bandits.Support.GeneratedFalseForwardEvent

end
