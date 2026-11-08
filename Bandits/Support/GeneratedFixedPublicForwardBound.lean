/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.BootstrapContextPassingTail
public import Bandits.Support.GeneratedContextPrivatePass
public import Bandits.Support.GeneratedFalseForwardEvent
public import Bandits.Support.GeneratedPrivateActivityBudget
public import Bandits.Support.ReferencePrelaunchFollower
public import Bandits.Support.CompletePublicTable

/-!
# Fixed-public actual false-forward bound

For each output in the existing common numerical public-good set, this file
applies the actual context statistic to the literal candidate prefix event,
disintegrates on the original private coordinates, and sums over the actual
all-block false-forward event.

Sources: `sources/zip4/manuscript/appendix_b_communication.tex:302-365` and
`sources/zip4/manuscript/08_main_theorem.tex:65-74`.
This is an internal conditional application; it is not a source-facing
theorem or manuscript-closure claim.
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
open Bandits.Support.BootstrapContextPrefixOperation
open Bandits.Support.BootstrapContextPassingTail
open Bandits.Support.ForwardPrefixSlice
open Bandits.Support.GeneratedContextPrivateLaw
open Bandits.Support.GeneratedContextPrivatePass
open Bandits.Support.GeneratedFalseForwardEvent
open Bandits.Support.GeneratedPrivateActivityBudget
open Bandits.Support.ReferencePrelaunchFollower
open scoped ENNReal Classical BigOperators

namespace Bandits.Support.GeneratedFixedPublicForwardBound

variable {p : ConstructorDimensions.Parameters}

/-- The context-local round-pair law is the original law from the same source
block. -/
theorem localRoundPairLaw_eq_roundPairLaw
    (c : BootstrapContextPassingTail.Context p) :
    BootstrapContextPassingTail.localRoundPairLaw c =
      BootstrapPrivateIDFibers.roundPairLaw p c.1 := rfl

/-- Transporting the context-local law along its source-block equality gives
the original law on that block's round-pair carrier. -/
theorem localRoundPairLaw_transport_eq_roundPairLaw
    (c : BootstrapContextPassingTail.Context p)
    (s : Fin (n_boot p)) (hs : c.1 = s) :
    hs ▸ BootstrapContextPassingTail.localRoundPairLaw c =
      BootstrapPrivateIDFibers.roundPairLaw p s := by
  cases hs
  rfl

/-- The literal candidate event agrees with the singleton-slice context event:
the accepted `candidatePasses` body reads only the selected false row and ID.
The full factorized false-row family remains the input on the left. -/
theorem candidatePasses_eq_contextPassSet_of_factorFalseForwardSlice
    (c : BootstrapContextPassingTail.Context p)
    (J : Fin (M p)) (hJ : c.2.1 = J)
    (base : FalseFactorBase p) (u : Fin (A_id p))
    (v : FalseRow p J) (rows : FalseForwardRows p J)
    (slice : ForwardSlice p)
    (hslice : ∀ t : Fin p.T,
      slice t = (Eq.ndrec (motive := fun r => FalseForwardRows p r) rows hJ.symm)
        (Eq.ndrec (motive := fun r => FalseRow p r) v hJ.symm) u t) :
    {rounds : BootstrapContextPrefixOperation.LocalRoundPair c |
      BootstrapContextPrefixOperation.candidatePasses c base u rounds
        (Eq.ndrec (motive := fun r => FalseRow p r) v hJ.symm)
        (Eq.ndrec (motive := fun r => FalseForwardRows p r) rows hJ.symm)} =
      BootstrapContextPassingTail.contextPassSet c base (v.1, u)
        (by simpa [BootstrapContextPrefixOperation.trueRowIndex, hJ] using v.property)
        slice := by
  cases hJ
  have hv : (⟨v.1, v.property⟩ : FalseRow p (BootstrapContextPrefixOperation.trueRowIndex c)) = v := by
    apply Subtype.ext
    rfl
  ext rounds
  change ForwardPrefixSlice.privatePrefixPasses
      (BootstrapContextPrefixOperation.candidateEligibleListFunction c base u v.1)
      rounds (fun t => rows v u t) ↔
    ForwardPrefixSlice.privatePrefixPasses
      (BootstrapContextPrefixOperation.candidateEligibleListFunction c base u v.1)
      rounds (fun t => BootstrapContextPassingTail.singletonFalseForwardRows c (v.1, u)
        v.property slice (⟨v.1, v.property⟩) u t)
  have hbits : (fun t => rows v u t) =
      (fun t => BootstrapContextPassingTail.singletonFalseForwardRows c (v.1, u)
        v.property slice (⟨v.1, v.property⟩) u t) := by
    funext t
    simp [BootstrapContextPassingTail.singletonFalseForwardRows, hslice]
  rw [hbits]

/-- Exact bridge from the accepted real context statistic to the `ENNReal`
inverse-ID sum used inline by the accepted fixed-output private disintegration
theorem. Its round-pair events are the full `candidatePasses` tests, identified
with the context statistic through the selected `(v,u)` false slice. -/
theorem actualContextStatistic_eq_inlineLocalSum_toReal
    (c : BootstrapContextPassingTail.Context p)
    (P : CompletePublicTable.PublishedOutput p)
    (s : Fin (n_boot p)) (J : Fin (M p))
    (hs : c.1 = s) (hJ : c.2.1 = J) :
    BootstrapContextPassingTail.actualContextPublishedFalseForwardStatistic c P =
    ENNReal.toReal (∑ u : Fin (A_id p), ENNReal.ofReal (1 / (A_id p : ℝ)) *
        ∑ v : FalseRow p J,
          BootstrapPrivateIDFibers.roundPairLaw p s
            {rounds | BootstrapContextPrefixOperation.candidatePasses c
              (FalseRowSliceFactorization.falseRowFactorEquiv p J P).1 u
              (Eq.ndrec (motive := fun b => BootstrapContextPrefixOperation.RoundPair b)
                rounds hs.symm)
              (Eq.ndrec (motive := fun r => FalseRow p r) v hJ.symm)
              (Eq.ndrec (motive := fun r => FalseForwardRows p r)
                (FalseRowSliceFactorization.falseRowFactorEquiv p J P).2 hJ.symm)}) := by
  classical
  cases hs
  cases hJ
  let Jc := BootstrapContextPrefixOperation.trueRowIndex c
  let z := FalseRowSliceFactorization.falseRowFactorEquiv p Jc P
  let μ := BootstrapPrivateIDFibers.roundPairLaw p c.1
  let candidate (v : FalseRow p Jc) (u : Fin (A_id p)) :
      Set (BootstrapContextPrefixOperation.RoundPair c.1) :=
    {rounds | BootstrapContextPrefixOperation.candidatePasses c z.1 u rounds v z.2}
  have hslice (v : FalseRow p Jc) (u : Fin (A_id p)) :
      BootstrapContextPassingTail.contextPassSet c z.1 (v.1, u) v.property
          (FalseForwardBaseTail.factorFalseForwardSlice p Jc (v.1, u) v.property z) =
        candidate v u := by
    have hv : (⟨v.1, v.property⟩ : FalseRow p Jc) = v := by
      apply Subtype.ext
      rfl
    have hsliceVal (t : Fin p.T) :
        FalseForwardBaseTail.factorFalseForwardSlice p Jc (v.1, u) v.property z t =
          z.2 v u t := by
      change z.2 (⟨v.1, v.property⟩ : FalseRow p Jc) u t = z.2 v u t
      rw [hv]
    exact (candidatePasses_eq_contextPassSet_of_factorFalseForwardSlice
      c Jc rfl z.1 u v z.2
      (FalseForwardBaseTail.factorFalseForwardSlice p Jc (v.1, u) v.property z)
      hsliceVal).symm
  have hprob (v : FalseRow p Jc) (u : Fin (A_id p)) :
      BootstrapContextPassingTail.contextPassingProbability c z.1 (v.1, u)
          v.property
          (FalseForwardBaseTail.factorFalseForwardSlice p Jc (v.1, u) v.property z) =
        μ.real (candidate v u) := by
    change (∫ rounds,
        (BootstrapContextPassingTail.contextPassSet c z.1 (v.1, u) v.property
          (FalseForwardBaseTail.factorFalseForwardSlice p Jc (v.1, u) v.property z)).indicator
            (fun _ => (1 : ℝ)) rounds ∂BootstrapContextPassingTail.localRoundPairLaw c) = _
    calc
      _ = (BootstrapContextPassingTail.localRoundPairLaw c).real
            (BootstrapContextPassingTail.contextPassSet c z.1 (v.1, u) v.property
              (FalseForwardBaseTail.factorFalseForwardSlice p Jc (v.1, u) v.property z)) :=
        integral_indicator_one
          (BootstrapContextPassingTail.measurableSet_contextPassSet c z.1 (v.1, u)
            v.property
            (FalseForwardBaseTail.factorFalseForwardSlice p Jc (v.1, u) v.property z))
      _ = μ.real (candidate v u) := by rw [hslice]; rfl
  have hinvnonneg : 0 ≤ 1 / (A_id p : ℝ) := by positivity
  have htermne (u : Fin (A_id p)) :
      ENNReal.ofReal (1 / (A_id p : ℝ)) * ∑ v : FalseRow p Jc, μ (candidate v u) ≠ ∞ := by
    apply ENNReal.mul_ne_top
    · simp
    · apply ENNReal.sum_ne_top.mpr
      intro v hv
      exact measure_ne_top μ (candidate v u)
  have hsumReal :
      ENNReal.toReal (∑ u : Fin (A_id p), ENNReal.ofReal (1 / (A_id p : ℝ)) *
        ∑ v : FalseRow p Jc, μ (candidate v u)) =
      ∑ u : Fin (A_id p), (1 / (A_id p : ℝ)) *
        ∑ v : FalseRow p Jc, (μ (candidate v u)).toReal := by
    rw [ENNReal.toReal_sum (fun u _ => htermne u)]
    apply Finset.sum_congr rfl
    intro u hu
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hinvnonneg,
      ENNReal.toReal_sum (fun v _ => measure_ne_top μ (candidate v u))]
  have hrows :
      (∑ v : Fin (M p), ∑ u : Fin (A_id p),
        if hfalse : v ≠ Jc then
          BootstrapContextPassingTail.contextPassingProbability c z.1 (v, u) hfalse
            (FalseForwardBaseTail.factorFalseForwardSlice p Jc (v, u) hfalse z)
        else 0) =
      ∑ v : FalseRow p Jc, ∑ u : Fin (A_id p), (μ (candidate v u)).toReal := by
    rw [Fintype.sum_eq_add_sum_subtype_ne
      (fun v : Fin (M p) => ∑ u : Fin (A_id p),
        if hfalse : v ≠ Jc then
          BootstrapContextPassingTail.contextPassingProbability c z.1 (v, u) hfalse
            (FalseForwardBaseTail.factorFalseForwardSlice p Jc (v, u) hfalse z)
        else 0) Jc]
    simp only [ne_eq, not_true_eq_false, dite_false,
      Finset.sum_const_zero, zero_add]
    apply Finset.sum_congr rfl
    intro v hv
    apply Finset.sum_congr rfl
    intro u hu
    have hvfalse : (v : Fin (M p)) ≠ Jc := v.property
    simpa [hvfalse, Measure.real] using hprob v u
  calc
    BootstrapContextPassingTail.actualContextPublishedFalseForwardStatistic c P =
        (1 / (A_id p : ℝ)) *
          ∑ v : Fin (M p), ∑ u : Fin (A_id p),
            if hfalse : v ≠ Jc then
              BootstrapContextPassingTail.contextPassingProbability c z.1 (v, u) hfalse
                (FalseForwardBaseTail.factorFalseForwardSlice p Jc (v, u) hfalse z)
            else 0 := by
      simp [BootstrapContextPassingTail.actualContextPublishedFalseForwardStatistic,
        Jc, z]
    _ = (1 / (A_id p : ℝ)) *
          ∑ v : FalseRow p Jc, ∑ u : Fin (A_id p), (μ (candidate v u)).toReal := by
      rw [hrows]
    _ = (1 / (A_id p : ℝ)) *
          ∑ u : Fin (A_id p), ∑ v : FalseRow p Jc, (μ (candidate v u)).toReal := by
      congr 1
      exact Finset.sum_comm
    _ = ∑ u : Fin (A_id p), (1 / (A_id p : ℝ)) *
          ∑ v : FalseRow p Jc, (μ (candidate v u)).toReal := by
      rw [Finset.mul_sum]
    _ = ENNReal.toReal (∑ u : Fin (A_id p), ENNReal.ofReal (1 / (A_id p : ℝ)) *
          ∑ v : FalseRow p Jc, μ (candidate v u)) := hsumReal.symm

/-- The subtype payload retains the exact source block, selected row, and
source follower indices, while its remaining context components stay in the
same source carrier. -/
theorem matchingSourceContext_indices
    (s : Fin (n_boot p)) (J : Fin (M p)) (j : Fin (p.m - 1))
    (mc : matchingSourceContext s J j) :
    mc.1.1 = s ∧
      BootstrapContextPrefixOperation.trueRowIndex mc.1 = J ∧
      BootstrapContextPrefixOperation.followerIndex mc.1 = j := by
  exact ⟨mc.2.1, mc.2.2.1, mc.2.2.2⟩

/-- On the exact common public-good event, every existing matching source
context supplies the inline `ENNReal` local sum required by the accepted
fixed-output private disintegration theorem. -/
theorem commonGoodSet_matchingContext_inlineSum_le
    (P : CompletePublicTable.PublishedOutput p) (J : Fin (M p))
    (s : Fin (n_boot p)) (j : Fin (p.m - 1))
    (mc : matchingSourceContext s J j)
    (hP : P ∈ BootstrapContextPassingTail.commonNumericPublicGoodSet p) :
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
              mc.2.2.1.symm)}) ≤ ENNReal.ofReal (BootstrapContextPassingTail.localEpsilon p) := by
  have hP' := hP
  rw [BootstrapContextPassingTail.commonNumericPublicGoodSet_eq_forall] at hP'
  have hstat := hP' mc.1
  have hmatch := matchingSourceContext_indices s J j mc
  have hbridge := actualContextStatistic_eq_inlineLocalSum_toReal
    mc.1 P s J hmatch.1 hmatch.2.1
  have hsumne :
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
                mc.2.2.1.symm)}) ≠ ∞ := by
    apply ENNReal.sum_ne_top.mpr
    intro u hu
    apply ENNReal.mul_ne_top
    · simp
    · apply ENNReal.sum_ne_top.mpr
      intro v hv
      exact measure_ne_top (BootstrapPrivateIDFibers.roundPairLaw p s) _
  have hepsilon : 0 ≤ BootstrapContextPassingTail.localEpsilon p := by
    unfold BootstrapContextPassingTail.localEpsilon
    positivity
  apply (ENNReal.le_ofReal_iff_toReal_le hsumne hepsilon).2
  calc
    _ = BootstrapContextPassingTail.actualContextPublishedFalseForwardStatistic mc.1 P :=
      hbridge.symm
    _ ≤ BootstrapContextPassingTail.localEpsilon p := hstat

/-- The nonempty actual context-code event is exactly the accepted original
processed/uninformed/active admission event. -/
theorem contextCode_ne_none_iff_activeProcessedUninformedEvent
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (P : CompletePublicTable.PublishedOutput p) (J : Fin (M p))
    (s : Fin (n_boot p)) (j : Fin (p.m - 1))
    (hj : j.val + 1 < p.m) (rho : ExtendedPrivateCoordinates p) :
    GeneratedContextPrivateLaw.contextCode s j hj P J rewards C_star C_h eta rho ≠ none ↔
      rho ∈ GeneratedPrivateActivityBudget.activeProcessedUninformedEvent
        p P J rewards C_star C_h eta s j := by
  rw [GeneratedContextPrivatePass.contextCode_ne_none_iff_actualFocalActiveWitness_ne_none,
    GeneratedPrivateActivityBudget.mem_activeProcessedUninformedEvent_iff_scalarActivity]
  let x := GeneratedEligibleFamily.referenceInputOfPublishedOutput
    C_star C_h eta rewards J (P, rho)
  constructor
  · intro h
    cases hw : GeneratedContextPrivateLaw.actualFocalActiveWitness
        s j hj P J rewards C_star C_h eta rho with
    | none => exact (h hw).elim
    | some w =>
      have hprocess : GeneratedForwardPrefixTests.processesBlock x s := by
        simpa [x, GeneratedContextPrivateLaw.publishedInput] using w.processed
      have hsame : BootstrapPrivateIDFibers.sourceFollower p j = j := by
        apply Fin.ext
        rfl
      have hinSource : BootstrapPrivateIDFibers.sourceFollower p j ∈
          (GeneratedForwardPrefixTests.actualPhysicalBlock x s hprocess).uninformed := by
        exact w.focal_eq ▸ w.activeFollower.val.property
      have hsub : w.activeFollower.val = ⟨BootstrapPrivateIDFibers.sourceFollower p j,
          hinSource⟩ := by
        apply Subtype.ext
        exact w.focal_eq
      have hactive :
          (GeneratedForwardPrefixTests.actualPhysicalBlock x s hprocess).active
            ⟨BootstrapPrivateIDFibers.sourceFollower p j, hinSource⟩ = true := by
        have hwactive := w.activeFollower.property
        rw [hsub] at hwactive
        exact hwactive
      have hcoin := GeneratedPrivateActivityBudget.actualIncomingActivity_eq_originalScalar
        p P J rewards C_star C_h eta s j hj rho hprocess hinSource
      refine ⟨?_, hcoin.symm.trans hactive⟩
      exact (GeneratedPrivateActivityBudget.mem_processedUninformedEvent_iff_actualIncoming
        p P J rewards C_star C_h eta s j rho).2
          ⟨hprocess, hsame ▸ hinSource⟩
  · rintro ⟨hprocessed, hcoin⟩
    rcases (GeneratedPrivateActivityBudget.mem_processedUninformedEvent_iff_actualIncoming
      p P J rewards C_star C_h eta s j rho).1 hprocessed with ⟨hprocess, hin⟩
    have hactive := GeneratedPrivateActivityBudget.actualIncomingActivity_eq_originalScalar
      p P J rewards C_star C_h eta s j hj rho hprocess hin
    have hsame : BootstrapPrivateIDFibers.sourceFollower p j = j := by
      apply Fin.ext
      rfl
    have hinSource : BootstrapPrivateIDFibers.sourceFollower p j ∈
        (GeneratedForwardPrefixTests.actualPhysicalBlock x s hprocess).uninformed :=
      hsame ▸ hin
    have hsub : (⟨BootstrapPrivateIDFibers.sourceFollower p j, hinSource⟩ :
        {i // i ∈ (GeneratedForwardPrefixTests.actualPhysicalBlock x s hprocess).uninformed}) =
        ⟨j, hin⟩ := by
      apply Subtype.ext
      exact hsame
    have hactiveSource :
        (GeneratedForwardPrefixTests.actualPhysicalBlock x s hprocess).active
          ⟨BootstrapPrivateIDFibers.sourceFollower p j, hinSource⟩ = true := by
      rw [hsub]
      exact hactive.trans hcoin
    have hw : GeneratedContextPrivateLaw.actualFocalActiveWitness
        s j hj P J rewards C_star C_h eta rho ≠ none := by
      simp [GeneratedContextPrivateLaw.actualFocalActiveWitness,
        GeneratedContextPrivateLaw.publishedInput, x, hprocess, hinSource, hactiveSource]
    exact hw

/-- At each fixed output, block, and source follower, the actual false-pass
mass is at most local epsilon times the mass of the matching actual admission
event. The accepted private disintegration is applied with `H = univ`. -/
theorem actualFalsePass_measure_le_localEpsilon_mul_admissionMass
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (P : CompletePublicTable.PublishedOutput p) (J : Fin (M p))
    (s : Fin (n_boot p)) (j : Fin (p.m - 1))
    (hj : j.val + 1 < p.m)
    (hP : P ∈ BootstrapContextPassingTail.commonNumericPublicGoodSet p) :
    (BootstrapPrivateRoundStreams.extendedPrivateLaw p).real
      {rho | (P, rho) ∈ actualFalseForwardPrefixPassSet C_star C_h eta rewards J s
        (BootstrapPrivateIDFibers.sourceFollower p j)} ≤
      BootstrapContextPassingTail.localEpsilon p *
        (BootstrapPrivateRoundStreams.extendedPrivateLaw p).real
          (GeneratedPrivateActivityBudget.activeProcessedUninformedEvent
            p P J rewards C_star C_h eta s j) := by
  have hlocal (mc : matchingSourceContext s J j) :=
    commonGoodSet_matchingContext_inlineSum_le P J s j mc hP
  have hdisintegrated :=
    GeneratedContextPrivatePass.actualFalseForwardPrefixPass_fixedOutput_epsilonBound
      C_star C_h eta rewards P J s j hj Set.univ MeasurableSet.univ
      (BootstrapContextPassingTail.localEpsilon p)
      (by
        unfold BootstrapContextPassingTail.localEpsilon
        positivity)
      hlocal
  have hcodeSet :
      {rho | GeneratedContextPrivateLaw.contextCode s j hj P J rewards C_star C_h eta rho ≠ none} =
        GeneratedPrivateActivityBudget.activeProcessedUninformedEvent
          p P J rewards C_star C_h eta s j := by
    ext rho
    exact contextCode_ne_none_iff_activeProcessedUninformedEvent
      C_star C_h eta rewards P J s j hj rho
  have hENN :
      BootstrapPrivateRoundStreams.extendedPrivateLaw p
        {rho | (P, rho) ∈ actualFalseForwardPrefixPassSet C_star C_h eta rewards J s
          (BootstrapPrivateIDFibers.sourceFollower p j)} ≤
        ENNReal.ofReal (BootstrapContextPassingTail.localEpsilon p) *
          BootstrapPrivateRoundStreams.extendedPrivateLaw p
            (GeneratedPrivateActivityBudget.activeProcessedUninformedEvent
              p P J rewards C_star C_h eta s j) := by
    simpa only [Set.mem_univ, and_true, hcodeSet] using hdisintegrated
  have hepsilon : 0 ≤ BootstrapContextPassingTail.localEpsilon p := by
    unfold BootstrapContextPassingTail.localEpsilon
    positivity
  calc
    _ = (BootstrapPrivateRoundStreams.extendedPrivateLaw p
        {rho | (P, rho) ∈ actualFalseForwardPrefixPassSet C_star C_h eta rewards J s
          (BootstrapPrivateIDFibers.sourceFollower p j)}).toReal := rfl
    _ ≤ (ENNReal.ofReal (BootstrapContextPassingTail.localEpsilon p) *
          BootstrapPrivateRoundStreams.extendedPrivateLaw p
            (GeneratedPrivateActivityBudget.activeProcessedUninformedEvent
              p P J rewards C_star C_h eta s j)).toReal :=
      ENNReal.toReal_mono (by finiteness) hENN
    _ = BootstrapContextPassingTail.localEpsilon p *
        (BootstrapPrivateRoundStreams.extendedPrivateLaw p).real
          (GeneratedPrivateActivityBudget.activeProcessedUninformedEvent
            p P J rewards C_star C_h eta s j) := by
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hepsilon]
      rfl

/-- The complete actual all-block false-forward event has the source
coefficient `n_boot * (m-1)/m`, and hence at most `1/B_boot`, for each fixed
output in the exact common numerical public-good set and every reward/index
choice. -/
theorem fixedOutput_actualAnyFalseForwardPrefixPass_measure_le_inv_Bboot
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (P : CompletePublicTable.PublishedOutput p) (J : Fin (M p))
    (hP : P ∈ BootstrapContextPassingTail.commonNumericPublicGoodSet p) :
    (BootstrapPrivateRoundStreams.extendedPrivateLaw p).real
      {rho | (P, rho) ∈ actualAnyFalseForwardPrefixPassSet C_star C_h eta rewards J} ≤
        1 / (B_boot p : ℝ) := by
  classical
  let μ := BootstrapPrivateRoundStreams.extendedPrivateLaw p
  let event (s : Fin (n_boot p)) (j : Fin (p.m - 1)) :
      Set (ExtendedPrivateCoordinates p) :=
    {rho | (P, rho) ∈ actualFalseForwardPrefixPassSet C_star C_h eta rewards J s
      (BootstrapPrivateIDFibers.sourceFollower p j)}
  have hunion :
      {rho | (P, rho) ∈ actualAnyFalseForwardPrefixPassSet C_star C_h eta rewards J} =
        ⋃ s : Fin (n_boot p), ⋃ j : Fin (p.m - 1), event s j := by
    ext rho
    simp only [GeneratedFalseForwardEvent.actualAnyFalseForwardPrefixPassSet,
      Set.mem_ofPred_eq, Set.mem_iUnion, event]
    constructor
    · rintro ⟨s, i, hpass⟩
      let j : Fin (p.m - 1) := i
      have hi : i = BootstrapPrivateIDFibers.sourceFollower p j := by
        apply Fin.ext
        rfl
      exact ⟨s, j, hi ▸ hpass⟩
    · rintro ⟨s, j, hpass⟩
      exact ⟨s, BootstrapPrivateIDFibers.sourceFollower p j, hpass⟩
  have hunionBound :
      μ.real (⋃ s : Fin (n_boot p), ⋃ j : Fin (p.m - 1), event s j) ≤
        ∑ s : Fin (n_boot p), ∑ j : Fin (p.m - 1), μ.real (event s j) := by
    calc
      _ ≤ ∑ s : Fin (n_boot p), μ.real (⋃ j : Fin (p.m - 1), event s j) :=
        measureReal_iUnion_fintype_le _
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro s hs
        exact measureReal_iUnion_fintype_le _
  have hper (s : Fin (n_boot p)) (j : Fin (p.m - 1)) :
      μ.real (event s j) ≤ BootstrapContextPassingTail.localEpsilon p *
        μ.real (GeneratedPrivateActivityBudget.activeProcessedUninformedEvent
          p P J rewards C_star C_h eta s j) := by
    exact actualFalsePass_measure_le_localEpsilon_mul_admissionMass
      C_star C_h eta rewards P J s j (by
        have hj := j.isLt
        change j.val < p.m - 1 at hj
        omega) hP
  have htotal := GeneratedPrivateActivityBudget.total_activeAdmission_real_mass_le_fraction
    p P J rewards C_star C_h eta
  have hepsilon : 0 ≤ BootstrapContextPassingTail.localEpsilon p := by
    unfold BootstrapContextPassingTail.localEpsilon
    positivity
  have hmpos : 0 < (p.m : ℝ) := Nat.cast_pos.mpr (ConstructorDimensions.m_pos p)
  have hratio : ((p.m - 1 : ℕ) : ℝ) / (p.m : ℝ) ≤ 1 := by
    apply (div_le_iff₀ hmpos).2
    have hnat : p.m - 1 ≤ p.m := Nat.sub_le p.m 1
    have hnatReal : ((p.m - 1 : ℕ) : ℝ) ≤ (p.m : ℝ) := by
      exact_mod_cast hnat
    simpa only [one_mul] using hnatReal
  have hcoeff : (n_boot p : ℝ) *
      (((p.m - 1 : ℕ) : ℝ) / (p.m : ℝ)) ≤ (n_boot p : ℝ) := by
    calc
      (n_boot p : ℝ) * (((p.m - 1 : ℕ) : ℝ) / (p.m : ℝ)) ≤
          (n_boot p : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left hratio (Nat.cast_nonneg _)
      _ = (n_boot p : ℝ) := by ring
  have hscale : BootstrapContextPassingTail.localEpsilon p * (n_boot p : ℝ) =
      1 / (B_boot p : ℝ) := by
    rw [BootstrapContextPassingTail.localEpsilon]
    have hB : (0 : ℝ) < (B_boot p : ℝ) := Nat.cast_pos.mpr (BootstrapDimensions.B_boot_pos p)
    have hn : (0 : ℝ) < (n_boot p : ℝ) := Nat.cast_pos.mpr (BootstrapDimensions.n_boot_pos p)
    field_simp [ne_of_gt hB, ne_of_gt hn]
  calc
    _ = μ.real (⋃ s : Fin (n_boot p), ⋃ j : Fin (p.m - 1), event s j) := by
      rw [hunion]
    _ ≤ ∑ s : Fin (n_boot p), ∑ j : Fin (p.m - 1), μ.real (event s j) := hunionBound
    _ ≤ ∑ s : Fin (n_boot p), ∑ j : Fin (p.m - 1),
          BootstrapContextPassingTail.localEpsilon p *
            μ.real (GeneratedPrivateActivityBudget.activeProcessedUninformedEvent
              p P J rewards C_star C_h eta s j) := by
      apply Finset.sum_le_sum
      intro s hs
      apply Finset.sum_le_sum
      intro j hj
      exact hper s j
    _ = ∑ s : Fin (n_boot p), BootstrapContextPassingTail.localEpsilon p *
          ∑ j : Fin (p.m - 1),
            μ.real (GeneratedPrivateActivityBudget.activeProcessedUninformedEvent
              p P J rewards C_star C_h eta s j) := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [← Finset.mul_sum]
    _ = BootstrapContextPassingTail.localEpsilon p *
          ∑ s : Fin (n_boot p), ∑ j : Fin (p.m - 1),
            μ.real (GeneratedPrivateActivityBudget.activeProcessedUninformedEvent
              p P J rewards C_star C_h eta s j) := by
      rw [← Finset.mul_sum]
    _ ≤ BootstrapContextPassingTail.localEpsilon p *
          ((n_boot p : ℝ) * (((p.m - 1 : ℕ) : ℝ) / (p.m : ℝ))) := by
      apply mul_le_mul_of_nonneg_left _ hepsilon
      calc
        _ ≤ (n_boot p : ℝ) * ((p.m - 1 : ℕ) : ℝ) / (p.m : ℝ) := htotal
        _ = (n_boot p : ℝ) * (((p.m - 1 : ℕ) : ℝ) / (p.m : ℝ)) := by ring
    _ ≤ BootstrapContextPassingTail.localEpsilon p * (n_boot p : ℝ) :=
      mul_le_mul_of_nonneg_left hcoeff hepsilon
    _ = 1 / (B_boot p : ℝ) := hscale

/-- One combined conditional application: the exact existing common numeric
public event is measurable and fails with probability at most `1/N`, and on
that same event every fixed output, denominator-`D` reward matrix, selected
index, shared numeric parameters, and existing learning rate obey the actual
all-block fixed-public false-forward private bound. The witness is the
accepted universal witness; this is an internal application, not source-lemma
closure. -/
theorem exists_universal_N0_commonGoodSet_and_fixedOutput_actualAnyFalseForwardPrefixPass_bound :
    ∃ N₀ : ℕ, ∀ p : ConstructorDimensions.Parameters, N₀ ≤ N p →
      (16 : ℝ) * (p.m : ℝ) * (p.K : ℝ) * (b_N p : ℝ) ^ 2 < (p.T : ℝ) →
      MeasurableSet (BootstrapContextPassingTail.commonNumericPublicGoodSet p) ∧
      (CompletePublicTable.publishedOutputMeasure p).real
        (BootstrapContextPassingTail.commonNumericPublicGoodSet p)ᶜ ≤ 1 / (N p : ℝ) ∧
      ∀ P : CompletePublicTable.PublishedOutput p,
        P ∈ BootstrapContextPassingTail.commonNumericPublicGoodSet p →
        ∀ rewards : Fin p.T → Fin p.K → Fin (D p + 1),
          ∀ J : Fin (M p), ∀ C_star C_h : ℝ,
            ∀ eta : ReferencePrelaunchFollower.LearningRate,
              (BootstrapPrivateRoundStreams.extendedPrivateLaw p).real
                {rho | (P, rho) ∈ actualAnyFalseForwardPrefixPassSet
                  C_star C_h eta rewards J} ≤ 1 / (B_boot p : ℝ) := by
  obtain ⟨N₀, hgood⟩ :=
    BootstrapContextPassingTail.commonNumericPublicGoodSet_failure_probability_le_of_construction_branch
  refine ⟨N₀, ?_⟩
  intro p hN₀ hbranch
  rcases hgood p hN₀ hbranch with ⟨hmeas, hfailure⟩
  refine ⟨hmeas, hfailure, ?_⟩
  intro P hP rewards J C_star C_h eta
  exact fixedOutput_actualAnyFalseForwardPrefixPass_measure_le_inv_Bboot
    C_star C_h eta rewards P J hP

end Bandits.Support.GeneratedFixedPublicForwardBound

end
