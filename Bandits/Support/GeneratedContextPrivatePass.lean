/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.GeneratedContextPrivateLaw
public import Bandits.Support.BootstrapContextPrefixOperation
public import Bandits.Support.GeneratedFalseForwardEvent
public import Bandits.Support.GeneratedEligibleFamily
public import Bandits.Support.ReferencePrelaunchFollower

/-!
# Actual fixed-output private false-pass application

For a fixed complete published output, this module disintegrates the actual
generated false-candidate passage on the original private coordinates.  Its
context and ID cells are the existing source context and physical ID, and its
local event is the accepted fixed-base candidate prefix test on the original
round pair.

Sources: `sources/zip4/manuscript/appendix_b_communication.tex:302-338,350-365`
and `sources/zip4/manuscript/08_main_theorem.tex:65-74`.
This is a fixed-output internal application only; it asserts no public event
probability, startup/coupling result, or manuscript closure.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.CompletePublicTable
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.BootstrapPrivateIDFibers
open Bandits.Support.FalseRowSliceFactorization
open Bandits.Support.ForwardPrefixSlice
open Bandits.Support.GeneratedPrivateIDFibers
open Bandits.Support.GeneratedBootstrapSupportContext
open Bandits.Support.GeneratedForwardPrefixTests
open Bandits.Support.GeneratedEligibleFamily
open Bandits.Support.GeneratedContextPrivateLaw
open Bandits.Support.GeneratedFalseForwardEvent
open Bandits.Support.BootstrapContextPrefixOperation
open Bandits.Support.ReferencePrelaunchFollower
open scoped ENNReal Classical BigOperators

namespace Bandits.Support.GeneratedContextPrivatePass

variable {p : Parameters}

/-- A value of the accepted finite context carrier with the block, selected
row, and focal follower fixed.  The arm and mask entries remain ordinary
source-context data. -/
abbrev sourceContextAt
    (s : Fin (n_boot p)) (J : Fin (M p)) (j : Fin (p.m - 1))
    (a z : Fin p.K)
    (x_a x_z : FalseRowSliceFactorization.BlockTime p s → Bool) : SourceContext p :=
  ⟨s, (J, (j, (a, (z, (x_a, x_z)))))⟩

/-- Existing source contexts whose displayed coordinates match this fixed
block, selected row, and focal source follower. -/
abbrev matchingSourceContext (s : Fin (n_boot p)) (J : Fin (M p))
    (j : Fin (p.m - 1)) :=
  {c : SourceContext p // c.1 = s ∧ c.2.1 = J ∧ c.2.2.1 = j}

/-- The actual generated pass of one false row, on the selected output and
the original private-coordinate carrier. -/
def actualGeneratedFalseCandidatePassSet
    (C_star C_h : ℝ) (eta : LearningRate)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (P : PublishedOutput p) (J : Fin (M p))
    (s : Fin (n_boot p)) (j : Fin (p.m - 1))
    (v : FalseRow p J) : Set (ExtendedPrivateCoordinates p) :=
  {rho | ∃ h : GeneratedForwardPrefixTests.processesBlock
        (GeneratedEligibleFamily.referenceInputOfPublishedOutput
          C_star C_h eta rewards J (P, rho)) s,
      ∃ q : GeneratedForwardPrefixTests.ActiveIncomingFollower
        (GeneratedEligibleFamily.referenceInputOfPublishedOutput
          C_star C_h eta rewards J (P, rho)) s h,
        q.val.val = BootstrapPrivateIDFibers.sourceFollower p j ∧
          GeneratedForwardPrefixTests.falseCandidatePasses
            (GeneratedEligibleFamily.referenceInputOfPublishedOutput
              C_star C_h eta rewards J (P, rho)) s h q P.2 J v}

/-- The indexed actual candidate events partition the existing dependent
existential event, without changing its selected output or private trace. -/
theorem actualFalseForwardPrefixPass_iff_exists_candidate
    (C_star C_h : ℝ) (eta : LearningRate)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (P : PublishedOutput p) (J : Fin (M p))
    (s : Fin (n_boot p)) (j : Fin (p.m - 1))
    (rho : ExtendedPrivateCoordinates p) :
    (P, rho) ∈ actualFalseForwardPrefixPassSet C_star C_h eta rewards J s
      (BootstrapPrivateIDFibers.sourceFollower p j) ↔
      ∃ v : FalseRow p J,
        rho ∈ actualGeneratedFalseCandidatePassSet C_star C_h eta rewards
          P J s j v := by
  change (∃ h : GeneratedForwardPrefixTests.processesBlock
      (GeneratedEligibleFamily.referenceInputOfPublishedOutput
        C_star C_h eta rewards J (P, rho)) s,
    ∃ q : GeneratedForwardPrefixTests.ActiveIncomingFollower
      (GeneratedEligibleFamily.referenceInputOfPublishedOutput
        C_star C_h eta rewards J (P, rho)) s h,
      q.val.val = BootstrapPrivateIDFibers.sourceFollower p j ∧
        GeneratedForwardPrefixTests.existsFalseForwardPrefixPass
          (GeneratedEligibleFamily.referenceInputOfPublishedOutput
            C_star C_h eta rewards J (P, rho)) s h q P.2 J) ↔ _
  constructor
  · rintro ⟨h, q, hq, hv⟩
    rcases hv with ⟨v, hpass⟩
    exact ⟨v, h, q, hq, hpass⟩
  · rintro ⟨v, h, q, hq, hpass⟩
    exact ⟨h, q, hq, v, hpass⟩

private theorem focalActiveWitness_eq_of_same_follower
    (x : ReferenceInitializationRun.Input p) (s : Fin (n_boot p))
    (j : Fin (p.m - 1))
    (h : GeneratedForwardPrefixTests.processesBlock x s)
    (q : GeneratedForwardPrefixTests.ActiveIncomingFollower x s h)
    (hqi : q.val.val = BootstrapPrivateIDFibers.sourceFollower p j)
    (w : GeneratedContextPrivateLaw.FocalActiveWitness s j x) :
    w = ⟨h, q, hqi⟩ := by
  rcases w with ⟨hw, qw, hwi⟩
  have hh : hw = h := Subsingleton.elim _ _
  subst hw
  have hqv : qw.val.val = q.val.val := hwi.trans hqi.symm
  have hq : qw = q := by
    apply Subtype.ext
    apply Subtype.ext
    exact hqv
  subst qw
  rfl

/-- A context code is present only at its original block, selected row, and
source follower coordinates. -/
theorem contextCode_some_components
    (C_star C_h : ℝ) (eta : LearningRate)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (P : PublishedOutput p) (J : Fin (M p))
    (s : Fin (n_boot p)) (j : Fin (p.m - 1)) (hj : j.val + 1 < p.m)
    (rho : ExtendedPrivateCoordinates p) (c : SourceContext p)
    (hc : GeneratedContextPrivateLaw.contextCode s j hj P J rewards C_star C_h eta rho = some c) :
    c.1 = s ∧ c.2.1 = J ∧ c.2.2.1 = j := by
  classical
  cases hw : GeneratedContextPrivateLaw.actualFocalActiveWitness
      s j hj P J rewards C_star C_h eta rho with
  | none => simp [GeneratedContextPrivateLaw.contextCode, hw] at hc
  | some w =>
    let localBlock := GeneratedContextPrivateLaw.actualLocalBlockOfWitness
      s j hj P J rewards C_star C_h eta rho w
    have hmap : GeneratedBootstrapSupportContext.actualContextMap P J
        (GeneratedContextPrivateLaw.publishedInput P J rewards C_star C_h eta rho) s
        localBlock = c := by
      simpa [GeneratedContextPrivateLaw.contextCode, hw] using hc
    have hs : c.1 = s := by
      have h := congrArg (fun d : SourceContext p => d.1) hmap
      exact h.symm
    have hJ : c.2.1 = J := by
      have h := congrArg (fun d : SourceContext p => d.2.1) hmap
      simpa only [GeneratedBootstrapSupportContext.actualContextMap] using h.symm
    have hidx : c.2.2.1 = BootstrapPhysicalInput.sourceFollowerIndex p
        localBlock.follower.1 := by
      have h := congrArg (fun d : SourceContext p => d.2.2.1) hmap
      simpa only [GeneratedBootstrapSupportContext.actualContextMap] using h.symm
    have hinput := GeneratedContextPrivateLaw.actualPhysicalInput_eq_actualPhysicalBlock
      s (GeneratedContextPrivateLaw.publishedInput P J rewards C_star C_h eta rho) w.processed
    have hlocalVal : localBlock.follower.1 = w.activeFollower.val.val := by
      change (hinput.symm ▸ w.activeFollower.val).val = _
      exact GeneratedContextPrivateLaw.inputEq_subtype_val _ _ hinput
        w.activeFollower.val
    have hj : c.2.2.1 = j := by
      rw [hidx, hlocalVal, w.focal_eq]
      exact BootstrapPrivateIDFibers.sourceFollowerIndex_eq p j
    exact ⟨hs, hJ, hj⟩

/-- A context code is present exactly on the accepted actual processed,
uninformed, active focal-witness branch. -/
theorem contextCode_ne_none_iff_actualFocalActiveWitness_ne_none
    (C_star C_h : ℝ) (eta : LearningRate)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (P : PublishedOutput p) (J : Fin (M p))
    (s : Fin (n_boot p)) (j : Fin (p.m - 1)) (hj : j.val + 1 < p.m)
    (rho : ExtendedPrivateCoordinates p) :
    GeneratedContextPrivateLaw.contextCode s j hj P J rewards C_star C_h eta rho ≠ none ↔
      GeneratedContextPrivateLaw.actualFocalActiveWitness
        s j hj P J rewards C_star C_h eta rho ≠ none := by
  simp [GeneratedContextPrivateLaw.contextCode]

/-- The finite existing `SourceContext` carrier partitions all actual
processed/uninformed/active focal contexts, with no default context on the
stopped or inactive branch. -/
theorem contextCode_some_partition
    (C_star C_h : ℝ) (eta : LearningRate)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (P : PublishedOutput p) (J : Fin (M p))
    (s : Fin (n_boot p)) (j : Fin (p.m - 1)) (hj : j.val + 1 < p.m) :
    {rho | GeneratedContextPrivateLaw.contextCode s j hj P J rewards C_star C_h eta rho ≠
        none} =
      ⋃ c : SourceContext p,
        {rho | GeneratedContextPrivateLaw.contextCode s j hj P J rewards C_star C_h eta rho =
          some c} := by
  classical
  ext rho
  constructor
  · intro h
    cases hcode : GeneratedContextPrivateLaw.contextCode
        s j hj P J rewards C_star C_h eta rho with
    | none => exact (h hcode).elim
    | some c => exact Set.mem_iUnion.mpr ⟨c, hcode⟩
  · intro h
    rcases Set.mem_iUnion.mp h with ⟨c, hc⟩
    change GeneratedContextPrivateLaw.contextCode s j hj P J rewards C_star C_h eta rho =
      some c at hc
    simp [hc]

/-- A context/W cell inconsistent with the actual block, selected row, or
focal follower is empty. This covers zero and null cells without a positivity
or division premise. -/
theorem contextWCell_zero_of_nonmatching
    (C_star C_h : ℝ) (eta : LearningRate)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (P : PublishedOutput p) (J : Fin (M p))
    (s : Fin (n_boot p)) (j : Fin (p.m - 1)) (hj : j.val + 1 < p.m)
    (H : Set (BootstrapPrivateIDFibers.Complement p s j ⟨j.val + 1, hj⟩))
    (c : SourceContext p)
    (hnot : ¬ (c.1 = s ∧ c.2.1 = J ∧ c.2.2.1 = j)) :
    extendedPrivateLaw p
      {rho | GeneratedContextPrivateLaw.contextCode s j hj P J rewards C_star C_h eta rho =
          some c ∧
        (BootstrapPrivateIDFibers.splitEquiv p s j hj rho).1 ∈ H} = 0 := by
  have hempty : {rho | GeneratedContextPrivateLaw.contextCode s j hj P J rewards C_star C_h eta rho =
      some c ∧
      (BootstrapPrivateIDFibers.splitEquiv p s j hj rho).1 ∈ H} = ∅ := by
    ext rho
    constructor
    · rintro ⟨hc, _⟩
      exact (hnot (contextCode_some_components C_star C_h eta rewards P J s j hj rho c hc)).elim
    · intro h
      cases h
  rw [hempty]
  simp

private theorem actualFocalWitness_privateId_eq_of_activeID
    (C_star C_h : ℝ) (eta : LearningRate)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (P : PublishedOutput p) (J : Fin (M p))
    (s : Fin (n_boot p)) (j : Fin (p.m - 1)) (_hj : j.val + 1 < p.m)
    (rho : ExtendedPrivateCoordinates p) (u : Fin (A_id p))
    (w : GeneratedContextPrivateLaw.FocalActiveWitness s j
      (GeneratedContextPrivateLaw.publishedInput P J rewards C_star C_h eta rho))
    (hid : activePrivateIDCodeOnPublishedOutput C_star C_h eta rewards J s
      (BootstrapPrivateIDFibers.sourceFollower p j) (P, rho) = some u) :
    (GeneratedForwardPrefixTests.actualPhysicalBlock
      (GeneratedContextPrivateLaw.publishedInput P J rewards C_star C_h eta rho)
      s w.processed).privateId w.activeFollower.val = u := by
  rcases (GeneratedFalseForwardEvent.activePrivateIDCodeOnPublishedOutput_eq_some_iff_actualContext
    C_star C_h eta rewards J P rho s (BootstrapPrivateIDFibers.sourceFollower p j) u).mp hid
    with ⟨h, q, hq, hprivate⟩
  have hwEq := focalActiveWitness_eq_of_same_follower
    (GeneratedContextPrivateLaw.publishedInput P J rewards C_star C_h eta rho)
    s j h q hq w
  rw [hwEq]
  exact hprivate

/-- On a context/ID cell, the actual generated false-candidate pass for a
fixed row is exactly the accepted projected candidate pass at the literal
factorized base and false rows, evaluated on the original round pair. -/
theorem actualGeneratedFalseCandidatePass_iff_candidatePasses
    (C_star C_h : ℝ) (eta : LearningRate)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (P : PublishedOutput p) (J : Fin (M p))
    (s : Fin (n_boot p)) (j : Fin (p.m - 1)) (hj : j.val + 1 < p.m)
    (rho : ExtendedPrivateCoordinates p) (u : Fin (A_id p))
    (v : FalseRow p J)
    (c : SourceContext p)
    (hc : GeneratedContextPrivateLaw.contextCode s j hj P J rewards C_star C_h eta rho =
      some c)
    (hid : activePrivateIDCodeOnPublishedOutput C_star C_h eta rewards J s
      (BootstrapPrivateIDFibers.sourceFollower p j) (P, rho) = some u) :
    rho ∈ actualGeneratedFalseCandidatePassSet C_star C_h eta rewards P J s j v ↔
      BootstrapContextPrefixOperation.candidatePasses
        c
        (FalseRowSliceFactorization.falseRowFactorEquiv p J P).1 u
        (Eq.ndrec (motive := fun b => BootstrapContextPrefixOperation.RoundPair b)
          (GeneratedPrivateIDFibers.originalRoundPair p s j hj rho)
          (contextCode_some_components C_star C_h eta rewards P J s j hj rho c hc).1.symm)
        (Eq.ndrec (motive := fun r => FalseRow p r) v
          (contextCode_some_components C_star C_h eta rewards P J s j hj rho c hc).2.1.symm)
        (Eq.ndrec (motive := fun r => FalseForwardRows p r)
          (FalseRowSliceFactorization.falseRowFactorEquiv p J P).2
          (contextCode_some_components C_star C_h eta rewards P J s j hj rho c hc).2.1.symm) := by
  classical
  let x := GeneratedContextPrivateLaw.publishedInput P J rewards C_star C_h eta rho
  have hcomp := contextCode_some_components C_star C_h eta rewards P J s j hj rho c hc
  cases hw : GeneratedContextPrivateLaw.actualFocalActiveWitness
      s j hj P J rewards C_star C_h eta rho with
  | none => simp [GeneratedContextPrivateLaw.contextCode, hw] at hc
  | some w =>
    have hctx : GeneratedBootstrapSupportContext.actualContextMap P J x s
        (GeneratedContextPrivateLaw.actualLocalBlockOfWitness
          s j hj P J rewards C_star C_h eta rho w) = c := by
      simpa [GeneratedContextPrivateLaw.contextCode, hw, x] using hc
    have hprivate := actualFocalWitness_privateId_eq_of_activeID
      C_star C_h eta rewards P J s j hj rho u w hid
    let localBlock := GeneratedContextPrivateLaw.actualLocalBlockOfWitness
      s j hj P J rewards C_star C_h eta rho w
    have hcontextInputEq := GeneratedContextPrivateLaw.actualPhysicalInput_eq_actualPhysicalBlock
      s x w.processed
    have hlocalVal : localBlock.follower.1 = w.activeFollower.val.val := by
      change (hcontextInputEq.symm ▸ w.activeFollower.val).val = _
      exact GeneratedContextPrivateLaw.inputEq_subtype_val _ _ hcontextInputEq
        w.activeFollower.val
    let genFollower := BootstrapContextPrefixOperation.actualGeneratedFollower
      localBlock w.processed
    have hinputEq := BootstrapContextPrefixOperation.actualPhysicalInput_eq_generatedPhysical
      localBlock w.processed
    have hgenFollower : genFollower = w.activeFollower := by
      have hval := BootstrapContextPrefixOperation.followerValue_cast_eq
        hinputEq localBlock.follower
      apply Subtype.ext
      apply Subtype.ext
      exact hval.trans hlocalVal
    have hlocalPrivateId :
        (GeneratedBootstrapSupportContext.actualPhysicalInput x localBlock.incoming s).privateId
          localBlock.follower = u := by
      have hcast := BootstrapContextPrefixOperation.privateId_cast_eq
        hinputEq localBlock.follower
      calc
        _ = (GeneratedForwardPrefixTests.actualPhysicalBlock x s w.processed).privateId
            genFollower.val := hcast.symm
        _ = (GeneratedForwardPrefixTests.actualPhysicalBlock x s w.processed).privateId
            w.activeFollower.val := by rw [hgenFollower]
        _ = u := hprivate
    have hlocalContext :
        GeneratedBootstrapSupportContext.actualContextMap P J x s localBlock = c := by
      simpa [localBlock, x] using hctx
    have hsourceIndex :
        BootstrapPhysicalInput.sourceFollowerIndex p localBlock.follower.1 = j := by
      rw [hlocalVal, w.focal_eq]
      exact BootstrapPrivateIDFibers.sourceFollowerIndex_eq p j
    have htrueRow : BootstrapContextPrefixOperation.trueRowIndex c = J := hcomp.2.1
    have hrounds :
        BootstrapContextPrefixOperation.originalRoundPair s
          (BootstrapPhysicalInput.sourceFollowerIndex p localBlock.follower.1)
          (by
            have hi := (BootstrapPhysicalInput.sourceFollowerIndex p localBlock.follower.1).isLt
            omega) x.coordinates = GeneratedPrivateIDFibers.originalRoundPair p s j hj rho := by
      rw [BootstrapContextPrefixOperation.originalRoundPair_eq_source]
      rw [hsourceIndex]
      rfl
    have hcandidate := BootstrapContextPrefixOperation.candidatePasses_iff_generatedFalseCandidatePasses
      localBlock w.processed v
    have hprivateRewrite :
        (GeneratedBootstrapSupportContext.actualPhysicalInput
          (GeneratedContextPrivateLaw.publishedInput P J rewards C_star C_h eta rho)
          localBlock.incoming s).privateId localBlock.follower = u := by
      simpa only [x] using hlocalPrivateId
    have hroundRewrite :
        BootstrapContextPrefixOperation.originalRoundPair s
          (BootstrapPhysicalInput.sourceFollowerIndex p localBlock.follower.1)
          (by
            have hi := (BootstrapPhysicalInput.sourceFollowerIndex p localBlock.follower.1).isLt
            omega) (GeneratedContextPrivateLaw.publishedInput P J rewards C_star C_h eta rho).coordinates =
          GeneratedPrivateIDFibers.originalRoundPair p s j hj rho := by
      simpa only [x] using hrounds
    have hcandidateLocal :
        BootstrapContextPrefixOperation.candidatePasses c
          (FalseRowSliceFactorization.falseRowFactorEquiv p J P).1 u
          (Eq.ndrec (motive := fun b => BootstrapContextPrefixOperation.RoundPair b)
            (GeneratedPrivateIDFibers.originalRoundPair p s j hj rho) hcomp.1.symm)
          (Eq.ndrec (motive := fun r => FalseRow p r) v hcomp.2.1.symm)
          (Eq.ndrec (motive := fun r => FalseForwardRows p r)
            (FalseRowSliceFactorization.falseRowFactorEquiv p J P).2 hcomp.2.1.symm) ↔
        GeneratedForwardPrefixTests.falseCandidatePasses x s w.processed
          w.activeFollower P.2 J v := by
      have hcandidateMap := hcandidate
      rw [hprivateRewrite] at hcandidateMap
      have hgenFollower' :
          BootstrapContextPrefixOperation.actualGeneratedFollower localBlock w.processed =
            w.activeFollower := hgenFollower
      rw [hgenFollower'] at hcandidateMap
      dsimp only [GeneratedBootstrapSupportContext.actualContextMap] at hcandidateMap
      rw [hroundRewrite] at hcandidateMap
      cases hlocalContext.symm
      simpa [x, GeneratedBootstrapSupportContext.actualContextMap] using hcandidateMap
    have hset :
        rho ∈ actualGeneratedFalseCandidatePassSet C_star C_h eta rewards P J s j v ↔
          GeneratedForwardPrefixTests.falseCandidatePasses x s w.processed
            w.activeFollower P.2 J v := by
      constructor
      · rintro ⟨h, q, hq, hpass⟩
        have hwEq := focalActiveWitness_eq_of_same_follower x s j h q hq w
        cases hwEq
        exact hpass
      · intro hpass
        exact ⟨w.processed, w.activeFollower, w.focal_eq, hpass⟩
    rw [hset]
    exact hcandidateLocal.symm

/-- Measurability of the literal fixed-context, fixed-base candidate pass
set, obtained from the accepted eligible-list measurability and first-quota
prefix test. -/
theorem measurableSet_candidatePasses
    (c : SourceContext p) (base : FalseFactorBase p) (u : Fin (A_id p))
    (v : FalseRow p c.2.1)
    (falseRows : FalseForwardRows p c.2.1) :
    MeasurableSet {rounds : BootstrapContextPrefixOperation.LocalRoundPair c |
      BootstrapContextPrefixOperation.candidatePasses c base u rounds v falseRows} := by
  change MeasurableSet (ForwardPrefixSlice.privatePrefixPassSet
    (BootstrapContextPrefixOperation.candidateEligibleListFunction c base u v.1)
    (fun t => falseRows v u t))
  exact ForwardPrefixSlice.measurableSet_privatePrefixPassSet
    (BootstrapContextPrefixOperation.candidateEligibleListFunction c base u v.1)
    (fun t => falseRows v u t)

/-- The actual fixed-output false-row passage on a reachable context/ID cell
has exactly the unnormalized private-ID and original-round-pair product
measure. `rho₀` witnesses reachability only; no cell mass is divided by or
assumed positive. The local statistic is the literal accepted candidate pass
with the factorized numerical base and false rows. -/
theorem actualGeneratedFalseCandidatePassSet_contextCell_measure
    (C_star C_h : ℝ) (eta : LearningRate)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (P : PublishedOutput p) (J : Fin (M p))
    (s : Fin (n_boot p)) (j : Fin (p.m - 1)) (hj : j.val + 1 < p.m)
    (H : Set (BootstrapPrivateIDFibers.Complement p s j ⟨j.val + 1, hj⟩))
    (hH : MeasurableSet H) (c : SourceContext p)
    (rho₀ : ExtendedPrivateCoordinates p)
    (hc₀ : GeneratedContextPrivateLaw.contextCode s j hj P J rewards C_star C_h eta rho₀ =
      some c)
    (u : Fin (A_id p)) (v : FalseRow p J) :
    extendedPrivateLaw p
      {rho | GeneratedContextPrivateLaw.contextCode s j hj P J rewards C_star C_h eta rho =
          some c ∧
        (BootstrapPrivateIDFibers.splitEquiv p s j hj rho).1 ∈ H ∧
        activePrivateIDCodeOnPublishedOutput C_star C_h eta rewards J s
          (BootstrapPrivateIDFibers.sourceFollower p j) (P, rho) = some u ∧
        rho ∈ actualGeneratedFalseCandidatePassSet C_star C_h eta rewards P J s j v} =
      extendedPrivateLaw p
        {rho | GeneratedContextPrivateLaw.contextCode s j hj P J rewards C_star C_h eta rho =
          some c ∧
          (BootstrapPrivateIDFibers.splitEquiv p s j hj rho).1 ∈ H} *
        ENNReal.ofReal (1 / (A_id p : ℝ)) *
        BootstrapPrivateIDFibers.roundPairLaw p s
          {rounds | BootstrapContextPrefixOperation.candidatePasses c
            (FalseRowSliceFactorization.falseRowFactorEquiv p J P).1 u
            (Eq.ndrec (motive := fun b => BootstrapContextPrefixOperation.RoundPair b)
              rounds
              (contextCode_some_components C_star C_h eta rewards P J s j hj rho₀ c hc₀).1.symm)
            (Eq.ndrec (motive := fun r => FalseRow p r) v
              (contextCode_some_components C_star C_h eta rewards P J s j hj rho₀ c hc₀).2.1.symm)
            (Eq.ndrec (motive := fun r => FalseForwardRows p r)
              (FalseRowSliceFactorization.falseRowFactorEquiv p J P).2
              (contextCode_some_components C_star C_h eta rewards P J s j hj rho₀ c hc₀).2.1.symm)} := by
  classical
  let hcomp := contextCode_some_components C_star C_h eta rewards P J s j hj rho₀ c hc₀
  let D : Set (BootstrapContextPrefixOperation.RoundPair s) :=
    {rounds | BootstrapContextPrefixOperation.candidatePasses c
      (FalseRowSliceFactorization.falseRowFactorEquiv p J P).1 u
      (Eq.ndrec (motive := fun b => BootstrapContextPrefixOperation.RoundPair b)
        rounds hcomp.1.symm)
      (Eq.ndrec (motive := fun r => FalseRow p r) v hcomp.2.1.symm)
      (Eq.ndrec (motive := fun r => FalseForwardRows p r)
        (FalseRowSliceFactorization.falseRowFactorEquiv p J P).2 hcomp.2.1.symm)}
  have hD : MeasurableSet D := by
    dsimp [D]
    cases hcomp.1
    exact measurableSet_candidatePasses c
      (FalseRowSliceFactorization.falseRowFactorEquiv p J P).1 u
      (Eq.ndrec (motive := fun r => FalseRow p r) v hcomp.2.1.symm)
      (Eq.ndrec (motive := fun r => FalseForwardRows p r)
        (FalseRowSliceFactorization.falseRowFactorEquiv p J P).2 hcomp.2.1.symm)
  have hnum :
      {rho | GeneratedContextPrivateLaw.contextCode s j hj P J rewards C_star C_h eta rho =
          some c ∧
        (BootstrapPrivateIDFibers.splitEquiv p s j hj rho).1 ∈ H ∧
        activePrivateIDCodeOnPublishedOutput C_star C_h eta rewards J s
          (BootstrapPrivateIDFibers.sourceFollower p j) (P, rho) = some u ∧
        rho ∈ actualGeneratedFalseCandidatePassSet C_star C_h eta rewards P J s j v} =
      {rho | GeneratedContextPrivateLaw.contextCode s j hj P J rewards C_star C_h eta rho =
          some c ∧
        (BootstrapPrivateIDFibers.splitEquiv p s j hj rho).1 ∈ H ∧
        activePrivateIDCodeOnPublishedOutput C_star C_h eta rewards J s
          (BootstrapPrivateIDFibers.sourceFollower p j) (P, rho) = some u ∧
        GeneratedPrivateIDFibers.originalRoundPair p s j hj rho ∈ D} := by
    ext rho
    constructor
    · rintro ⟨hc, hW, hid, hpass⟩
      refine ⟨hc, hW, hid, ?_⟩
      have hlocal := actualGeneratedFalseCandidatePass_iff_candidatePasses
        C_star C_h eta rewards P J s j hj rho u v c hc hid
      exact (by simpa [D, hcomp] using hlocal.mp hpass)
    · rintro ⟨hc, hW, hid, hpair⟩
      refine ⟨hc, hW, hid, ?_⟩
      have hlocal := actualGeneratedFalseCandidatePass_iff_candidatePasses
        C_star C_h eta rewards P J s j hj rho u v c hc hid
      exact (by simpa [D, hcomp] using hlocal.mpr hpair)
  calc
    extendedPrivateLaw p
        {rho | GeneratedContextPrivateLaw.contextCode s j hj P J rewards C_star C_h eta rho =
            some c ∧
          (BootstrapPrivateIDFibers.splitEquiv p s j hj rho).1 ∈ H ∧
          activePrivateIDCodeOnPublishedOutput C_star C_h eta rewards J s
            (BootstrapPrivateIDFibers.sourceFollower p j) (P, rho) = some u ∧
          rho ∈ actualGeneratedFalseCandidatePassSet C_star C_h eta rewards P J s j v} =
      extendedPrivateLaw p
        {rho | GeneratedContextPrivateLaw.contextCode s j hj P J rewards C_star C_h eta rho =
            some c ∧
          (BootstrapPrivateIDFibers.splitEquiv p s j hj rho).1 ∈ H ∧
          activePrivateIDCodeOnPublishedOutput C_star C_h eta rewards J s
            (BootstrapPrivateIDFibers.sourceFollower p j) (P, rho) = some u ∧
          GeneratedPrivateIDFibers.originalRoundPair p s j hj rho ∈ D} := by
      rw [hnum]
    _ = extendedPrivateLaw p
          {rho | GeneratedContextPrivateLaw.contextCode s j hj P J rewards C_star C_h eta rho =
              some c ∧
            (BootstrapPrivateIDFibers.splitEquiv p s j hj rho).1 ∈ H} *
          ENNReal.ofReal (1 / (A_id p : ℝ)) *
          BootstrapPrivateIDFibers.roundPairLaw p s D :=
      GeneratedContextPrivateLaw.context_id_originalRoundPair_measure
        s j hj P J rewards C_star C_h eta H hH D hD c u
    _ = _ := rfl

private theorem actualFocalActiveWitness_some_of_incoming
    (C_star C_h : ℝ) (eta : LearningRate)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (P : PublishedOutput p) (J : Fin (M p))
    (s : Fin (n_boot p)) (j : Fin (p.m - 1)) (hj : j.val + 1 < p.m)
    (rho : ExtendedPrivateCoordinates p)
    (h : GeneratedForwardPrefixTests.processesBlock
      (GeneratedEligibleFamily.referenceInputOfPublishedOutput
        C_star C_h eta rewards J (P, rho)) s)
    (q : GeneratedForwardPrefixTests.ActiveIncomingFollower
      (GeneratedEligibleFamily.referenceInputOfPublishedOutput
        C_star C_h eta rewards J (P, rho)) s h)
    (hq : q.val.val = BootstrapPrivateIDFibers.sourceFollower p j) :
    ∃ w, GeneratedContextPrivateLaw.actualFocalActiveWitness
      s j hj P J rewards C_star C_h eta rho = some w := by
  let x := GeneratedContextPrivateLaw.publishedInput P J rewards C_star C_h eta rho
  have hx :
      GeneratedEligibleFamily.referenceInputOfPublishedOutput
        C_star C_h eta rewards J (P, rho) = x := by
    rfl
  have h' : GeneratedForwardPrefixTests.processesBlock x s := by
    simpa only [hx] using h
  let phys := GeneratedForwardPrefixTests.actualPhysicalBlock x s h'
  have hmem : BootstrapPrivateIDFibers.sourceFollower p j ∈ phys.uninformed := by
    rw [← hq]
    exact q.val.property
  let f : {i // i ∈ phys.uninformed} :=
    ⟨BootstrapPrivateIDFibers.sourceFollower p j, hmem⟩
  have hf : f = q.val := by
    apply Subtype.ext
    exact hq.symm
  have hactive : phys.active f = true := by
    rw [hf]
    exact q.property
  let w : GeneratedContextPrivateLaw.FocalActiveWitness s j x :=
    ⟨h', ⟨f, hactive⟩, rfl⟩
  refine ⟨w, ?_⟩
  simp [GeneratedContextPrivateLaw.actualFocalActiveWitness, x, w, f]
  refine ⟨?_, ?_, ?_⟩
  · simpa only [x] using h'
  · simpa only [x] using hmem
  · simpa only [x] using hactive

/-- At a fixed complete published output, the actual per-follower/block false
pass event restricted to a retained W-event is the union over existing source
contexts, actual private IDs, and false rows of the actual context cells. -/
theorem actualFalseForwardPrefixPass_fixedOutput_eq_contextIDRowUnion
    (C_star C_h : ℝ) (eta : LearningRate)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (P : PublishedOutput p) (J : Fin (M p))
    (s : Fin (n_boot p)) (j : Fin (p.m - 1)) (hj : j.val + 1 < p.m)
    (H : Set (BootstrapPrivateIDFibers.Complement p s j ⟨j.val + 1, hj⟩)) :
    {rho | (P, rho) ∈ actualFalseForwardPrefixPassSet C_star C_h eta rewards J s
        (BootstrapPrivateIDFibers.sourceFollower p j) ∧
      (BootstrapPrivateIDFibers.splitEquiv p s j hj rho).1 ∈ H} =
      ⋃ mc : matchingSourceContext s J j, ⋃ u : Fin (A_id p), ⋃ v : FalseRow p J,
        {rho | GeneratedContextPrivateLaw.contextCode s j hj P J rewards C_star C_h eta rho =
            some mc.1 ∧
          (BootstrapPrivateIDFibers.splitEquiv p s j hj rho).1 ∈ H ∧
          activePrivateIDCodeOnPublishedOutput C_star C_h eta rewards J s
            (BootstrapPrivateIDFibers.sourceFollower p j) (P, rho) = some u ∧
          rho ∈ actualGeneratedFalseCandidatePassSet C_star C_h eta rewards P J s j v} := by
  classical
  ext rho
  constructor
  · rintro ⟨hpass, hW⟩
    rcases (actualFalseForwardPrefixPass_iff_exists_candidate
      C_star C_h eta rewards P J s j rho).mp hpass with ⟨v, hv⟩
    rcases hv with ⟨h, q, hq, hfalse⟩
    obtain ⟨w, hw⟩ := actualFocalActiveWitness_some_of_incoming
      C_star C_h eta rewards P J s j hj rho h q hq
    let c := GeneratedBootstrapSupportContext.actualContextMap P J
      (GeneratedContextPrivateLaw.publishedInput P J rewards C_star C_h eta rho) s
      (GeneratedContextPrivateLaw.actualLocalBlockOfWitness
        s j hj P J rewards C_star C_h eta rho w)
    have hc : GeneratedContextPrivateLaw.contextCode s j hj P J rewards C_star C_h eta rho =
        some c := by
      simp [GeneratedContextPrivateLaw.contextCode, hw, c]
    let mc : matchingSourceContext s J j :=
      ⟨c, contextCode_some_components C_star C_h eta rewards P J s j hj rho c hc⟩
    let u := (GeneratedForwardPrefixTests.actualPhysicalBlock
      (GeneratedEligibleFamily.referenceInputOfPublishedOutput
        C_star C_h eta rewards J (P, rho)) s h).privateId q.val
    have hid : activePrivateIDCodeOnPublishedOutput C_star C_h eta rewards J s
        (BootstrapPrivateIDFibers.sourceFollower p j) (P, rho) = some u := by
      apply (GeneratedFalseForwardEvent.activePrivateIDCodeOnPublishedOutput_eq_some_iff_actualContext
        C_star C_h eta rewards J P rho s (BootstrapPrivateIDFibers.sourceFollower p j) u).2
      exact ⟨h, q, hq, rfl⟩
    exact Set.mem_iUnion.mpr ⟨mc, Set.mem_iUnion.mpr ⟨u,
      Set.mem_iUnion.mpr ⟨v, ⟨hc, hW, hid, ⟨h, q, hq, hfalse⟩⟩⟩⟩⟩
  · simp only [Set.mem_iUnion]
    rintro ⟨mc, u, v, hc, hW, hid, hv⟩
    refine ⟨?_, hW⟩
    exact (actualFalseForwardPrefixPass_iff_exists_candidate
      C_star C_h eta rewards P J s j rho).mpr ⟨v, hv⟩

/-- Finite context/ID/false-row union bound at one fixed complete public
output. Each summand is the actual context/W-cell mass, the literal inverse-ID
factor, and the accepted local candidate-pass measure on the original pair. -/
theorem actualFalseForwardPrefixPass_fixedOutput_contextWeightedBound
    (C_star C_h : ℝ) (eta : LearningRate)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (P : PublishedOutput p) (J : Fin (M p))
    (s : Fin (n_boot p)) (j : Fin (p.m - 1)) (hj : j.val + 1 < p.m)
    (H : Set (BootstrapPrivateIDFibers.Complement p s j ⟨j.val + 1, hj⟩))
    (hH : MeasurableSet H) :
    extendedPrivateLaw p
      {rho | (P, rho) ∈ actualFalseForwardPrefixPassSet C_star C_h eta rewards J s
          (BootstrapPrivateIDFibers.sourceFollower p j) ∧
        (BootstrapPrivateIDFibers.splitEquiv p s j hj rho).1 ∈ H} ≤
      ∑ mc : matchingSourceContext s J j,
        extendedPrivateLaw p
          {rho | GeneratedContextPrivateLaw.contextCode s j hj P J rewards C_star C_h eta rho =
              some mc.1 ∧
            (BootstrapPrivateIDFibers.splitEquiv p s j hj rho).1 ∈ H} *
        (∑ u : Fin (A_id p), ENNReal.ofReal (1 / (A_id p : ℝ)) *
          ∑ v : FalseRow p J,
            BootstrapPrivateIDFibers.roundPairLaw p s
              {rounds | BootstrapContextPrefixOperation.candidatePasses mc.1
                (FalseRowSliceFactorization.falseRowFactorEquiv p J P).1 u
                (Eq.ndrec (motive := fun b => BootstrapContextPrefixOperation.RoundPair b)
                  rounds mc.2.1.symm)
                (Eq.ndrec (motive := fun r => FalseRow p r) v mc.2.2.1.symm)
                (Eq.ndrec (motive := fun r => FalseForwardRows p r)
                  (FalseRowSliceFactorization.falseRowFactorEquiv p J P).2
                  mc.2.2.1.symm)}) := by
  classical
  let bad (mc : matchingSourceContext s J j) (u : Fin (A_id p))
      (v : FalseRow p J) : Set (ExtendedPrivateCoordinates p) :=
    {rho | GeneratedContextPrivateLaw.contextCode s j hj P J rewards C_star C_h eta rho =
        some mc.1 ∧
      (BootstrapPrivateIDFibers.splitEquiv p s j hj rho).1 ∈ H ∧
      activePrivateIDCodeOnPublishedOutput C_star C_h eta rewards J s
        (BootstrapPrivateIDFibers.sourceFollower p j) (P, rho) = some u ∧
      rho ∈ actualGeneratedFalseCandidatePassSet C_star C_h eta rewards P J s j v}
  have hUnion := actualFalseForwardPrefixPass_fixedOutput_eq_contextIDRowUnion
    C_star C_h eta rewards P J s j hj H
  have hRows (mc : matchingSourceContext s J j) (u : Fin (A_id p)) :
      extendedPrivateLaw p (⋃ v : FalseRow p J, bad mc u v) ≤
        ∑ v : FalseRow p J, extendedPrivateLaw p (bad mc u v) :=
    measure_iUnion_fintype_le _ _
  have hIDs (mc : matchingSourceContext s J j) :
      extendedPrivateLaw p (⋃ u : Fin (A_id p), ⋃ v : FalseRow p J, bad mc u v) ≤
        ∑ u : Fin (A_id p), ∑ v : FalseRow p J,
          extendedPrivateLaw p (bad mc u v) := by
    calc
      _ ≤ ∑ u : Fin (A_id p),
          extendedPrivateLaw p (⋃ v : FalseRow p J, bad mc u v) :=
        measure_iUnion_fintype_le _ _
      _ ≤ _ := Finset.sum_le_sum fun u _ => hRows mc u
  have hAll :
      extendedPrivateLaw p (⋃ mc : matchingSourceContext s J j,
        ⋃ u : Fin (A_id p), ⋃ v : FalseRow p J, bad mc u v) ≤
        ∑ mc : matchingSourceContext s J j,
          ∑ u : Fin (A_id p), ∑ v : FalseRow p J,
            extendedPrivateLaw p (bad mc u v) := by
    calc
      _ ≤ ∑ mc : matchingSourceContext s J j,
          extendedPrivateLaw p (⋃ u : Fin (A_id p),
            ⋃ v : FalseRow p J, bad mc u v) := measure_iUnion_fintype_le _ _
      _ ≤ _ := Finset.sum_le_sum fun mc _ => hIDs mc
  have hcell (mc : matchingSourceContext s J j) (u : Fin (A_id p))
      (v : FalseRow p J) :
      extendedPrivateLaw p (bad mc u v) =
        extendedPrivateLaw p
          {rho | GeneratedContextPrivateLaw.contextCode s j hj P J rewards C_star C_h eta rho =
              some mc.1 ∧
            (BootstrapPrivateIDFibers.splitEquiv p s j hj rho).1 ∈ H} *
          ENNReal.ofReal (1 / (A_id p : ℝ)) *
          BootstrapPrivateIDFibers.roundPairLaw p s
            {rounds | BootstrapContextPrefixOperation.candidatePasses mc.1
              (FalseRowSliceFactorization.falseRowFactorEquiv p J P).1 u
              (Eq.ndrec (motive := fun b => BootstrapContextPrefixOperation.RoundPair b)
                rounds mc.2.1.symm)
              (Eq.ndrec (motive := fun r => FalseRow p r) v mc.2.2.1.symm)
              (Eq.ndrec (motive := fun r => FalseForwardRows p r)
                (FalseRowSliceFactorization.falseRowFactorEquiv p J P).2
                mc.2.2.1.symm)} := by
    by_cases hreach : ∃ rho, GeneratedContextPrivateLaw.contextCode
        s j hj P J rewards C_star C_h eta rho = some mc.1
    · rcases hreach with ⟨rho₀, hc₀⟩
      have hmeasure := actualGeneratedFalseCandidatePassSet_contextCell_measure
        C_star C_h eta rewards P J s j hj H hH mc.1 rho₀ hc₀ u v
      have hcompEq :
          contextCode_some_components C_star C_h eta rewards P J s j hj rho₀ mc.1 hc₀ =
            mc.2 := Subsingleton.elim _ _
      simpa [bad, hcompEq] using hmeasure
    · have hbadEmpty : bad mc u v = ∅ := by
        ext rho
        constructor
        · rintro ⟨hc, _, _, _⟩
          exact hreach ⟨rho, hc⟩
        · intro h
          cases h
      have hctxEmpty :
          {rho | GeneratedContextPrivateLaw.contextCode s j hj P J rewards C_star C_h eta rho =
              some mc.1 ∧
            (BootstrapPrivateIDFibers.splitEquiv p s j hj rho).1 ∈ H} = ∅ := by
        ext rho
        constructor
        · rintro ⟨hc, _⟩
          exact hreach ⟨rho, hc⟩
        · intro h
          cases h
      rw [hbadEmpty, hctxEmpty]
      simp
  have hsum :
      (∑ mc : matchingSourceContext s J j,
        ∑ u : Fin (A_id p), ∑ v : FalseRow p J,
          extendedPrivateLaw p (bad mc u v)) =
      ∑ mc : matchingSourceContext s J j,
        extendedPrivateLaw p
          {rho | GeneratedContextPrivateLaw.contextCode s j hj P J rewards C_star C_h eta rho =
              some mc.1 ∧
            (BootstrapPrivateIDFibers.splitEquiv p s j hj rho).1 ∈ H} *
        (∑ u : Fin (A_id p), ENNReal.ofReal (1 / (A_id p : ℝ)) *
          ∑ v : FalseRow p J,
            BootstrapPrivateIDFibers.roundPairLaw p s
              {rounds | BootstrapContextPrefixOperation.candidatePasses mc.1
                (FalseRowSliceFactorization.falseRowFactorEquiv p J P).1 u
                (Eq.ndrec (motive := fun b => BootstrapContextPrefixOperation.RoundPair b)
                  rounds mc.2.1.symm)
                (Eq.ndrec (motive := fun r => FalseRow p r) v mc.2.2.1.symm)
                (Eq.ndrec (motive := fun r => FalseForwardRows p r)
                  (FalseRowSliceFactorization.falseRowFactorEquiv p J P).2
                  mc.2.2.1.symm)}) := by
    apply Finset.sum_congr rfl
    intro mc _
    calc
      _ = ∑ u : Fin (A_id p), ∑ v : FalseRow p J,
          extendedPrivateLaw p (bad mc u v) := rfl
      _ = ∑ u : Fin (A_id p), ∑ v : FalseRow p J,
          (extendedPrivateLaw p
            {rho | GeneratedContextPrivateLaw.contextCode s j hj P J rewards C_star C_h eta rho =
                some mc.1 ∧
              (BootstrapPrivateIDFibers.splitEquiv p s j hj rho).1 ∈ H} *
            ENNReal.ofReal (1 / (A_id p : ℝ)) *
            BootstrapPrivateIDFibers.roundPairLaw p s
              {rounds | BootstrapContextPrefixOperation.candidatePasses mc.1
                (FalseRowSliceFactorization.falseRowFactorEquiv p J P).1 u
                (Eq.ndrec (motive := fun b => BootstrapContextPrefixOperation.RoundPair b)
                  rounds mc.2.1.symm)
                (Eq.ndrec (motive := fun r => FalseRow p r) v mc.2.2.1.symm)
                (Eq.ndrec (motive := fun r => FalseForwardRows p r)
                  (FalseRowSliceFactorization.falseRowFactorEquiv p J P).2
                  mc.2.2.1.symm)}) := by
          apply Finset.sum_congr rfl
          intro u _
          apply Finset.sum_congr rfl
          intro v _
          exact hcell mc u v
      _ = _ := by
        let cellMass := extendedPrivateLaw p
          {rho | GeneratedContextPrivateLaw.contextCode s j hj P J rewards C_star C_h eta rho =
              some mc.1 ∧
            (BootstrapPrivateIDFibers.splitEquiv p s j hj rho).1 ∈ H}
        let localMass := fun (u : Fin (A_id p)) (v : FalseRow p J) =>
          BootstrapPrivateIDFibers.roundPairLaw p s
            {rounds | BootstrapContextPrefixOperation.candidatePasses mc.1
              (FalseRowSliceFactorization.falseRowFactorEquiv p J P).1 u
              (Eq.ndrec (motive := fun b => BootstrapContextPrefixOperation.RoundPair b)
                rounds mc.2.1.symm)
              (Eq.ndrec (motive := fun r => FalseRow p r) v mc.2.2.1.symm)
              (Eq.ndrec (motive := fun r => FalseForwardRows p r)
                (FalseRowSliceFactorization.falseRowFactorEquiv p J P).2
                mc.2.2.1.symm)}
        calc
          _ = ∑ u : Fin (A_id p), ∑ v : FalseRow p J,
                (cellMass * ENNReal.ofReal (1 / (A_id p : ℝ))) * localMass u v := by
                rfl
          _ = ∑ u : Fin (A_id p),
                cellMass * (ENNReal.ofReal (1 / (A_id p : ℝ)) *
                  ∑ v : FalseRow p J, localMass u v) := by
                apply Finset.sum_congr rfl
                intro u _
                calc
                  _ = ∑ v : FalseRow p J,
                        (cellMass * ENNReal.ofReal (1 / (A_id p : ℝ))) * localMass u v := by
                        rfl
                  _ = (cellMass * ENNReal.ofReal (1 / (A_id p : ℝ))) *
                        ∑ v : FalseRow p J, localMass u v := by
                        rw [Finset.mul_sum]
                  _ = cellMass * (ENNReal.ofReal (1 / (A_id p : ℝ)) *
                        ∑ v : FalseRow p J, localMass u v) := by
                        rw [mul_assoc]
          _ = cellMass * ∑ u : Fin (A_id p),
                ENNReal.ofReal (1 / (A_id p : ℝ)) *
                  ∑ v : FalseRow p J, localMass u v := by
                rw [← Finset.mul_sum]
          _ = _ := rfl
  calc
    _ = extendedPrivateLaw p
        (⋃ mc : matchingSourceContext s J j,
          ⋃ u : Fin (A_id p), ⋃ v : FalseRow p J, bad mc u v) := by
        rw [hUnion]
    _ ≤ ∑ mc : matchingSourceContext s J j,
        ∑ u : Fin (A_id p), ∑ v : FalseRow p J,
          extendedPrivateLaw p (bad mc u v) := hAll
    _ = _ := hsum

/-- The actual processed/uninformed/active focal branch, retained on any
measurable W-event, is partitioned by matching values of the existing finite
source-context carrier. -/
theorem matchingContextW_partition
    (C_star C_h : ℝ) (eta : LearningRate)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (P : PublishedOutput p) (J : Fin (M p))
    (s : Fin (n_boot p)) (j : Fin (p.m - 1)) (hj : j.val + 1 < p.m)
    (H : Set (BootstrapPrivateIDFibers.Complement p s j ⟨j.val + 1, hj⟩)) :
    {rho | GeneratedContextPrivateLaw.contextCode s j hj P J rewards C_star C_h eta rho ≠
        none ∧ (BootstrapPrivateIDFibers.splitEquiv p s j hj rho).1 ∈ H} =
      ⋃ mc : matchingSourceContext s J j,
        {rho | GeneratedContextPrivateLaw.contextCode s j hj P J rewards C_star C_h eta rho =
            some mc.1 ∧ (BootstrapPrivateIDFibers.splitEquiv p s j hj rho).1 ∈ H} := by
  classical
  ext rho
  constructor
  · rintro ⟨hcode, hW⟩
    cases hc : GeneratedContextPrivateLaw.contextCode
        s j hj P J rewards C_star C_h eta rho with
    | none => exact (hcode hc).elim
    | some c =>
      have hcomponents := contextCode_some_components C_star C_h eta rewards P J s j hj rho c hc
      let mc : matchingSourceContext s J j := ⟨c, hcomponents⟩
      exact Set.mem_iUnion.mpr ⟨mc, hc, hW⟩
  · intro h
    rcases Set.mem_iUnion.mp h with ⟨mc, hc, hW⟩
    exact ⟨by simp [hc], hW⟩

/-- The context-cell masses sum to the actual processed/uninformed/active
focal mass on the retained W-event. -/
theorem matchingContextW_mass_eq
    (C_star C_h : ℝ) (eta : LearningRate)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (P : PublishedOutput p) (J : Fin (M p))
    (s : Fin (n_boot p)) (j : Fin (p.m - 1)) (hj : j.val + 1 < p.m)
    (H : Set (BootstrapPrivateIDFibers.Complement p s j ⟨j.val + 1, hj⟩))
    (hH : MeasurableSet H) :
    (∑ mc : matchingSourceContext s J j,
      extendedPrivateLaw p
        {rho | GeneratedContextPrivateLaw.contextCode s j hj P J rewards C_star C_h eta rho =
            some mc.1 ∧ (BootstrapPrivateIDFibers.splitEquiv p s j hj rho).1 ∈ H}) =
      extendedPrivateLaw p
        {rho | GeneratedContextPrivateLaw.contextCode s j hj P J rewards C_star C_h eta rho ≠
            none ∧ (BootstrapPrivateIDFibers.splitEquiv p s j hj rho).1 ∈ H} := by
  classical
  let cell : matchingSourceContext s J j → Set (ExtendedPrivateCoordinates p) := fun mc =>
    {rho | GeneratedContextPrivateLaw.contextCode s j hj P J rewards C_star C_h eta rho =
        some mc.1 ∧ (BootstrapPrivateIDFibers.splitEquiv p s j hj rho).1 ∈ H}
  have hpartition := matchingContextW_partition C_star C_h eta rewards P J s j hj H
  have hdisj : Set.PairwiseDisjoint
      (↑(Finset.univ : Finset (matchingSourceContext s J j))) cell := by
    intro mc _ mc' _ hne
    apply Set.disjoint_left.2
    intro rho hmc hmc'
    apply hne
    apply Subtype.ext
    exact Option.some.inj (hmc.1.symm.trans hmc'.1)
  have hmeas : ∀ mc ∈ (Finset.univ : Finset (matchingSourceContext s J j)),
      MeasurableSet (cell mc) := by
    intro mc _
    let E := GeneratedContextPrivateLaw.contextWCell s j hj P J rewards C_star C_h eta H mc.1
    have hE : MeasurableSet E :=
      GeneratedContextPrivateLaw.measurableSet_contextWCell s j hj P J rewards C_star C_h eta H hH mc.1
    have hden : cell mc =
        (fun rho => (BootstrapPrivateIDFibers.splitEquiv p s j hj rho).1) ⁻¹' E := by
      ext rho
      simp [cell, E, GeneratedContextPrivateLaw.contextWCell,
        GeneratedContextPrivateLaw.contextCode_eq_contextCodeFromW,
        GeneratedContextPrivateLaw.splitW]
    rw [hden]
    exact hE.preimage (measurable_fst.comp
      (BootstrapPrivateIDFibers.splitEquiv p s j hj).measurable)
  have hset : (Set.univ : Set (matchingSourceContext s J j)) =
      ↑(Finset.univ : Finset (matchingSourceContext s J j)) := by
    ext mc
    simp
  have hconv : (⋃ mc : matchingSourceContext s J j, cell mc) =
      ⋃ mc ∈ (Finset.univ : Finset (matchingSourceContext s J j)), cell mc := by
    rw [← Set.biUnion_univ, hset]
    exact Finset.set_biUnion_coe Finset.univ cell
  rw [hpartition, hconv]
  exact (measure_biUnion_finset (μ := extendedPrivateLaw p)
    (s := Finset.univ) (f := cell) hdisj hmeas).symm

/-- If every matching numerical context has the displayed inverse-ID weighted
local round-pair sum at most `epsilon`, the actual fixed-output false-pass
mass on W is at most `epsilon` times the actual processed/uninformed/active
focal mass on W. This is the concrete fixed-public-event application used
next with the accepted public-tail/g event and `GeneratedPrivateActivityBudget`
for an all-block fixed-public `1/B_boot` bound. -/
theorem actualFalseForwardPrefixPass_fixedOutput_epsilonBound
    (C_star C_h : ℝ) (eta : LearningRate)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (P : PublishedOutput p) (J : Fin (M p))
    (s : Fin (n_boot p)) (j : Fin (p.m - 1)) (hj : j.val + 1 < p.m)
    (H : Set (BootstrapPrivateIDFibers.Complement p s j ⟨j.val + 1, hj⟩))
    (hH : MeasurableSet H) (epsilon : ℝ) (_hepsilon : 0 ≤ epsilon)
    (hlocal : ∀ mc : matchingSourceContext s J j,
      (∑ u : Fin (A_id p), ENNReal.ofReal (1 / (A_id p : ℝ)) *
        ∑ v : FalseRow p J,
          BootstrapPrivateIDFibers.roundPairLaw p s
            {rounds | BootstrapContextPrefixOperation.candidatePasses mc.1
              (FalseRowSliceFactorization.falseRowFactorEquiv p J P).1 u
              (Eq.ndrec (motive := fun b => BootstrapContextPrefixOperation.RoundPair b)
                rounds mc.2.1.symm)
              (Eq.ndrec (motive := fun r => FalseRow p r) v mc.2.2.1.symm)
              (Eq.ndrec (motive := fun r => FalseForwardRows p r)
                (FalseRowSliceFactorization.falseRowFactorEquiv p J P).2
                mc.2.2.1.symm)}) ≤ ENNReal.ofReal epsilon) :
    extendedPrivateLaw p
      {rho | (P, rho) ∈ actualFalseForwardPrefixPassSet C_star C_h eta rewards J s
          (BootstrapPrivateIDFibers.sourceFollower p j) ∧
        (BootstrapPrivateIDFibers.splitEquiv p s j hj rho).1 ∈ H} ≤
      ENNReal.ofReal epsilon * extendedPrivateLaw p
        {rho | GeneratedContextPrivateLaw.contextCode s j hj P J rewards C_star C_h eta rho ≠
            none ∧ (BootstrapPrivateIDFibers.splitEquiv p s j hj rho).1 ∈ H} := by
  calc
    _ ≤ ∑ mc : matchingSourceContext s J j,
        extendedPrivateLaw p
          {rho | GeneratedContextPrivateLaw.contextCode s j hj P J rewards C_star C_h eta rho =
              some mc.1 ∧ (BootstrapPrivateIDFibers.splitEquiv p s j hj rho).1 ∈ H} *
        (∑ u : Fin (A_id p), ENNReal.ofReal (1 / (A_id p : ℝ)) *
          ∑ v : FalseRow p J,
            BootstrapPrivateIDFibers.roundPairLaw p s
              {rounds | BootstrapContextPrefixOperation.candidatePasses mc.1
                (FalseRowSliceFactorization.falseRowFactorEquiv p J P).1 u
                (Eq.ndrec (motive := fun b => BootstrapContextPrefixOperation.RoundPair b)
                  rounds mc.2.1.symm)
                (Eq.ndrec (motive := fun r => FalseRow p r) v mc.2.2.1.symm)
                (Eq.ndrec (motive := fun r => FalseForwardRows p r)
                  (FalseRowSliceFactorization.falseRowFactorEquiv p J P).2
                  mc.2.2.1.symm)}) :=
      actualFalseForwardPrefixPass_fixedOutput_contextWeightedBound
        C_star C_h eta rewards P J s j hj H hH
    _ ≤ ∑ mc : matchingSourceContext s J j,
        extendedPrivateLaw p
          {rho | GeneratedContextPrivateLaw.contextCode s j hj P J rewards C_star C_h eta rho =
              some mc.1 ∧ (BootstrapPrivateIDFibers.splitEquiv p s j hj rho).1 ∈ H} *
          ENNReal.ofReal epsilon := by
      apply Finset.sum_le_sum
      intro mc _
      exact mul_le_mul_right (hlocal mc) _
    _ = ENNReal.ofReal epsilon *
        ∑ mc : matchingSourceContext s J j,
          extendedPrivateLaw p
            {rho | GeneratedContextPrivateLaw.contextCode s j hj P J rewards C_star C_h eta rho =
                some mc.1 ∧ (BootstrapPrivateIDFibers.splitEquiv p s j hj rho).1 ∈ H} := by
      calc
        _ = ∑ mc : matchingSourceContext s J j,
              ENNReal.ofReal epsilon *
                extendedPrivateLaw p
                  {rho | GeneratedContextPrivateLaw.contextCode s j hj P J rewards C_star C_h eta rho =
                      some mc.1 ∧ (BootstrapPrivateIDFibers.splitEquiv p s j hj rho).1 ∈ H} := by
              apply Finset.sum_congr rfl
              intro mc _
              exact mul_comm _ _
        _ = _ := by rw [Finset.mul_sum]
    _ = _ := by rw [matchingContextW_mass_eq C_star C_h eta rewards P J s j hj H hH]

end Bandits.Support.GeneratedContextPrivatePass

end
