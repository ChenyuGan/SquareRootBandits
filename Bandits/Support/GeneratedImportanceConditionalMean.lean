/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.GeneratedBootstrapImportanceMean

import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Actual importance gain on causal prefix cells

Sources: `sources/zip4/manuscript/appendix_b_communication.tex:376-415,485-584`
and `sources/zip4/manuscript/07_public_setup.tex:63-115`.
The incoming numerator vector in every denominator is the one from the actual
original-coordinate run. Physical gains retain the whole clipped block,
including positive stays after a pending declaration and the first crossing.
-/

@[expose] public section

noncomputable section

open MeasureTheory Function
open scoped Classical BigOperators

namespace Bandits.Support.GeneratedImportanceConditionalMean

open ConstructorDimensions BootstrapDimensions ActiveRoundActions CompletePublicTable
open ReferencePrelaunchFollower ReferenceInitializationRun
open GeneratedBootstrapBlockFiltrationRepair GeneratedBootstrapRoundLaw
open GeneratedBlockChoiceAverages GeneratedImportanceGainAdaptedness
open GeneratedBootstrapImportanceMean

variable (p : ConstructorDimensions.Parameters)

/-- The denominator is strictly positive for each actual incoming numerator
vector. No positivity of the probability of a boundary event is required. -/
theorem incoming_probability_pos (b : ReferenceInitializationRun.Boundary p)
    (i : Follower p.m) (a : Fin p.K) :
    0 < BootstrapWeightPotential.probability (b_N p)
      (b.numerators (BootstrapPhysicalInput.sourceFollowerIndex p i)) a :=
  BootstrapWeightPotential.probability_pos (K_pos p) _ a

/-- On the actual active/held start event, importance is the full physical
gain divided by the probability from the same incoming run boundary. -/
theorem actualImportance_eq_full_gain_div_probability_on_blockStartEvent
    (ids : IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : LearningRate) (i : Follower p.m)
    (s : Fin (n_boot p)) (a z : Fin p.K) (u : Fin (A_id p))
    (e : GeneratedBootstrapBlockFiltrationRepair.Coordinates p)
    (he : e ∈ GeneratedStayBlockTower.blockStartEvent ids rewards C_star C_h eta
      (s := s) i a z u) :
    actualImportanceObservable p ids rewards C_star C_h eta i s a e =
      GeneratedStayBlockTower.actualBlockGain ids rewards C_star C_h eta (s := s) i e /
        BootstrapWeightPotential.probability (b_N p)
          ((ReferenceInitializationRun.run
            (referenceInput p ids rewards C_star C_h eta e) s.val).numerators
              (BootstrapPhysicalInput.sourceFollowerIndex p i)) a := by
  let x := GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e
  let b := ReferenceInitializationRun.run x s.val
  change GeneratedStayBlockTower.blockStartGuard ids rewards (s := s) i a z u
    (descriptor p ids rewards C_star C_h eta s
      (GeneratedStayBlockTower.blockStartRound p s) e) at he
  cases hd : descriptor p ids rewards C_star C_h eta s
      (GeneratedStayBlockTower.blockStartRound p s) e with
  | none => simp only [hd, GeneratedStayBlockTower.blockStartGuard] at he
  | some d =>
    have hrec := GeneratedStayConditionalMean.actualDescriptor_reconstructs_source_block
      p ids rewards C_star C_h eta (s := s)
      (GeneratedStayBlockTower.blockStartRound p s) e d hd
    rcases hrec with ⟨hb, hrem, hprofile, _, _, _⟩
    change b = d.1 at hb
    have hc : b.crossing = none := by
      by_contra h
      have hn := (descriptor_eq_none_iff ids rewards C_star C_h eta s
        (GeneratedStayBlockTower.blockStartRound p s) e).2 h
      rw [hd] at hn
      cases hn
    rw [hd] at he
    dsimp only [GeneratedStayBlockTower.blockStartGuard,
      GeneratedStayConditionalMean.inputOfDescriptor] at he
    rcases he with ⟨hi, ha, hh, _, _, _, _⟩
    have hi' : i ∈ ReferenceInitializationRun.uninformed b := by
      rw [hb]
      exact hi
    let j : {j // j ∈ ReferenceInitializationRun.uninformed b} := ⟨i, hi'⟩
    have hactive : (ReferenceInitializationRun.physical x b hrem).active j = true := by
      change (BootstrapPhysicalInput.currentBlockDrawProfile p
        (ReferenceInitializationRun.nextBlock b hrem) b.numerators b.weight_ge_one
        x.coordinates (BootstrapPhysicalInput.sourceFollowerIndex p i)).1 = true
      rw [hprofile]
      exact ha
    have hheld : (ReferenceInitializationRun.physical x b hrem).held j = a := by
      change (BootstrapPhysicalInput.currentBlockDrawProfile p
        (ReferenceInitializationRun.nextBlock b hrem) b.numerators b.weight_ge_one
        x.coordinates (BootstrapPhysicalInput.sourceFollowerIndex p i)).2.1 = a
      rw [hprofile]
      exact hh
    have hfields := ReferenceInitializationMeasurability.weightInput_fields x b hrem j
    have henabled : (ReferenceInitializationRun.weightInput x b hrem j).enabled = true :=
      hfields.1.trans hactive
    have hheld' : (ReferenceInitializationRun.weightInput x b hrem j).held = a :=
      hfields.2.1.trans hheld
    have hgain := GeneratedStayBlockTower.actualBlockGain_eq_referenceEffectiveGain
      ids rewards C_star C_h eta (s := s) i e hc hrem hi'
    change GeneratedBootstrapPotential.actualImportance x i s a = _
    unfold GeneratedBootstrapPotential.actualImportance
    rw [GeneratedBootstrapPotential.actualBlock_eq_weightInput x i s hc hi']
    rw [hgain]
    change BootstrapWeightPotential.importance (b_N p)
      (b.numerators (BootstrapPhysicalInput.sourceFollowerIndex p i))
      (ReferenceInitializationRun.weightInput x b hrem j) a =
        (BootstrapWeightPotential.effectiveGain
          (ReferenceInitializationRun.weightInput x b hrem j) : ℝ) /
            BootstrapWeightPotential.probability (b_N p)
              (b.numerators (BootstrapPhysicalInput.sourceFollowerIndex p i)) a
    simp only [BootstrapWeightPotential.importance, henabled, hheld', and_self,
      ite_true, BootstrapWeightPotential.effectiveGain]

/-- Distinct actual target/private-ID pairs select disjoint physical events.
Both guards inspect the same generated descriptor. -/
theorem blockStartEvent_pairwise_disjoint
    (ids : IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : LearningRate) (i : Follower p.m)
    (s : Fin (n_boot p)) (a : Fin p.K) :
    Pairwise (Disjoint on (fun q : Fin p.K × Fin (A_id p) =>
      GeneratedStayBlockTower.blockStartEvent ids rewards C_star C_h eta
        (s := s) i a q.1 q.2)) := by
  intro q r hqr
  apply Set.disjoint_left.mpr
  intro e hq hr
  change GeneratedStayBlockTower.blockStartGuard ids rewards (s := s) i a q.1 q.2
    (descriptor p ids rewards C_star C_h eta s
      (GeneratedStayBlockTower.blockStartRound p s) e) at hq
  change GeneratedStayBlockTower.blockStartGuard ids rewards (s := s) i a r.1 r.2
    (descriptor p ids rewards C_star C_h eta s
      (GeneratedStayBlockTower.blockStartRound p s) e) at hr
  cases hd : descriptor p ids rewards C_star C_h eta s
      (GeneratedStayBlockTower.blockStartRound p s) e with
  | none => simp only [hd, GeneratedStayBlockTower.blockStartGuard] at hq
  | some d =>
    rw [hd] at hq hr
    rcases hq with ⟨hi, _, _, hu, hz, _, _⟩
    rcases hr with ⟨hi', _, _, hu', hz', _, _⟩
    apply hqr
    exact Prod.ext (hz.symm.trans hz') (hu.symm.trans hu')

/-- The start events are ambient measurable under the original law. -/
theorem measurableSet_blockStartEvent
    (ids : IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : LearningRate) (i : Follower p.m)
    (s : Fin (n_boot p)) (a z : Fin p.K) (u : Fin (A_id p)) :
    MeasurableSet (GeneratedStayBlockTower.blockStartEvent ids rewards C_star C_h eta
      (s := s) i a z u) :=
  (GeneratedBootstrapFiltration.analysisFiltration_le p _) _
    (GeneratedStayBlockTower.blockStartEvent_measurable ids rewards C_star C_h eta
      (s := s) i a z u)

/-- A physical start event localized to an arbitrary causal-prefix cell and
one actual incoming boundary. -/
def prefixStartCell (s : Fin (n_boot p))
    (E : Set (GeneratedBootstrapImportanceMean.SourcePrefix p s))
    (ids : IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : LearningRate) (b : ReferenceInitializationRun.Boundary p)
    (i : Follower p.m) (a z : Fin p.K) (u : Fin (A_id p)) :
    Set (GeneratedBootstrapBlockFiltrationRepair.Coordinates p) :=
  sourcePrefixBoundaryCell p s E ids rewards C_star C_h eta b ∩
    GeneratedStayBlockTower.blockStartEvent ids rewards C_star C_h eta (s := s) i a z u

theorem measurableSet_prefixStartCell (s : Fin (n_boot p))
    (E : Set (GeneratedBootstrapImportanceMean.SourcePrefix p s)) (hE : MeasurableSet E)
    (ids : IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : LearningRate) (b : ReferenceInitializationRun.Boundary p)
    (i : Follower p.m) (a z : Fin p.K) (u : Fin (A_id p)) :
    MeasurableSet (prefixStartCell p s E ids rewards C_star C_h eta b i a z u) :=
  (measurableSet_sourcePrefixBoundaryCell p s E hE ids rewards C_star C_h eta b).inter
    (measurableSet_blockStartEvent p ids rewards C_star C_h eta i s a z u)

/-- On each literal incoming boundary the same positive probability is
constant throughout the integral. -/
theorem actualImportance_setIntegral_prefixStartCell (s : Fin (n_boot p))
    (E : Set (GeneratedBootstrapImportanceMean.SourcePrefix p s)) (hE : MeasurableSet E)
    (ids : IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : LearningRate) (b : ReferenceInitializationRun.Boundary p)
    (i : Follower p.m) (a z : Fin p.K) (u : Fin (A_id p)) :
    (∫ e in prefixStartCell p s E ids rewards C_star C_h eta b i a z u,
      actualImportanceObservable p ids rewards C_star C_h eta i s a e ∂originalLaw p) =
    (∫ e in prefixStartCell p s E ids rewards C_star C_h eta b i a z u,
      GeneratedStayBlockTower.actualBlockGain ids rewards C_star C_h eta (s := s) i e
        ∂originalLaw p) /
      BootstrapWeightPotential.probability (b_N p)
        (b.numerators (BootstrapPhysicalInput.sourceFollowerIndex p i)) a := by
  rw [← integral_div]
  apply setIntegral_congr_fun
    (measurableSet_prefixStartCell p s E hE ids rewards C_star C_h eta b i a z u)
  intro e he
  rw [actualImportance_eq_full_gain_div_probability_on_blockStartEvent
    p ids rewards C_star C_h eta i s a z u e he.2]
  have hb : ReferenceInitializationRun.run
      (referenceInput p ids rewards C_star C_h eta e) s.val = b := he.1.2
  rw [hb]

/-- The parent prefix-cell mass converted to real values and divided by the
actual held probability. This identity includes null and unreachable cells. -/
theorem prefix_choice_mass_div_probability (s : Fin (n_boot p))
    (E : Set (GeneratedBootstrapImportanceMean.SourcePrefix p s)) (hE : MeasurableSet E)
    (ids : IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : LearningRate) (b : ReferenceInitializationRun.Boundary p)
    (hcompleted : b.completed = s.val) (hnotStopped : b.crossing = none)
    (i : GeneratedBlockChoiceAverages.Incoming p b) (a z : Fin p.K) (u : Fin (A_id p)) :
    (originalLaw p).real (supportChoiceTargetCellWithSide p s ids rewards C_star C_h eta
        (sourcePrefixSideCell p s E) b hcompleted hnotStopped i a z u) /
        BootstrapWeightPotential.probability (b_N p)
          (b.numerators (BootstrapPhysicalInput.sourceFollowerIndex p i.1)) a =
      (originalLaw p).real (sourcePrefixBoundaryCell p s E ids rewards C_star C_h eta b) *
        ((1 / (p.m : ℝ)) * (1 / (A_id p : ℝ)) *
          (1 - 1 / (p.m : ℝ)) ^ (incomingCount p b - 1) * (1 / (p.K : ℝ))) := by
  let P := BootstrapWeightPotential.probability (b_N p)
    (b.numerators (BootstrapPhysicalInput.sourceFollowerIndex p i.1)) a
  have hP : 0 < P := incoming_probability_pos p b i.1 a
  have hm : 0 < (p.m : ℝ) := Nat.cast_pos.mpr (m_pos p)
  have hA : 0 < (A_id p : ℝ) := Nat.cast_pos.mpr (A_id_pos p)
  have hK : 0 < (p.K : ℝ) := Nat.cast_pos.mpr (K_pos p)
  have hq : 0 ≤ 1 - 1 / (p.m : ℝ) :=
    BootstrapBlockConstruction.activityProbability_nonneg p false
  have hnonneg : 0 ≤ ((P / (p.m : ℝ)) * (1 / (A_id p : ℝ))) *
      (1 - 1 / (p.m : ℝ)) ^ (incomingCount p b - 1) := by positivity
  have hmass := congrArg ENNReal.toReal
    (supportChoiceTargetCell_prefix_measure p s E hE ids rewards C_star C_h eta b
      hcompleted hnotStopped i a z u)
  simp only [ENNReal.toReal_mul] at hmass
  change (originalLaw p).real _ = (originalLaw p).real _ *
    (ENNReal.ofReal ((P / (p.m : ℝ) * (1 / (A_id p : ℝ))) *
      (1 - 1 / (p.m : ℝ)) ^ (incomingCount p b - 1))).toReal *
      (ENNReal.ofReal (1 / (p.K : ℝ))).toReal at hmass
  rw [ENNReal.toReal_ofReal hnonneg, ENNReal.toReal_ofReal (by positivity)] at hmass
  rw [hmass]
  change (_ * ((P / _ * _) * _) * _) / P = _
  field_simp

/-- A fixed actual target/private-ID cell contributes its supported-zero
count with the held denominator cancelled. Only local branch conditions are
present here; no conditional-law or mean hypothesis is supplied. -/
theorem actualImportance_setIntegral_ge_prefixChoice (s : Fin (n_boot p))
    (E : Set (GeneratedBootstrapImportanceMean.SourcePrefix p s)) (hE : MeasurableSet E)
    (ids : IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : LearningRate) (b : ReferenceInitializationRun.Boundary p)
    (hcompleted : b.completed = s.val) (hnotStopped : b.crossing = none)
    (i : GeneratedBlockChoiceAverages.Incoming p b) (a z : Fin p.K) (u : Fin (A_id p))
    (hza : z ≠ a) :
    (supportedIDZeroCount p s ids rewards a u / 16) *
        (originalLaw p).real (sourcePrefixBoundaryCell p s E ids rewards C_star C_h eta b) *
        ((1 / (p.m : ℝ)) * (1 / (A_id p : ℝ)) *
          (1 - 1 / (p.m : ℝ)) ^ (incomingCount p b - 1) * (1 / (p.K : ℝ))) ≤
      ∫ e in prefixStartCell p s E ids rewards C_star C_h eta b i.1 a z u,
        actualImportanceObservable p ids rewards C_star C_h eta i.1 s a e ∂originalLaw p := by
  rw [actualImportance_setIntegral_prefixStartCell p s E hE ids rewards C_star C_h eta
    b i.1 a z u]
  have hgain := actualBlockGain_setIntegral_ge_prefixCell p s E hE ids rewards
    C_star C_h eta b hcompleted hnotStopped i a z u hza
  have hdiv := div_le_div_of_nonneg_right hgain (incoming_probability_pos p b i.1 a).le
  rw [mul_div_assoc, prefix_choice_mass_div_probability p s E hE ids rewards
    C_star C_h eta b hcompleted hnotStopped i a z u] at hdiv
  simpa only [prefixStartCell, mul_assoc] using hdiv

private theorem isolation_power_ge_quarter (b : ReferenceInitializationRun.Boundary p)
    (i : GeneratedBlockChoiceAverages.Incoming p b) :
    (1 / 4 : ℝ) ≤ (1 - 1 / (p.m : ℝ)) ^ (incomingCount p b - 1) := by
  have hq : 0 ≤ 1 - 1 / (p.m : ℝ) :=
    BootstrapBlockConstruction.activityProbability_nonneg p false
  have hqle : 1 - 1 / (p.m : ℝ) ≤ 1 := sub_le_self _ (by positivity)
  calc
    (1 / 4 : ℝ) ≤ (1 - 1 / (p.m : ℝ)) ^ (p.m - 2) :=
      BootstrapBlockIsolation.inactivity_power_lower_bound p
    _ ≤ (1 - 1 / (p.m : ℝ)) ^ (incomingCount p b - 1) :=
      pow_le_pow_of_le_one hq hqle
        (GeneratedBlockGuardLaw.sourceIncomingFinset_other_count_le p b i)

/-- Summing the disjoint actual target and private-ID cells gives the
support lower bound on every causal-prefix/boundary cell. Good IDs are used
only through their supported-zero average. -/
theorem actualImportance_setIntegral_ge_prefixBoundary (s : Fin (n_boot p))
    (E : Set (GeneratedBootstrapImportanceMean.SourcePrefix p s)) (hE : MeasurableSet E)
    (ids : IDArray p) (hgood : ids ∈ IdentificationGoodEvent.identificationGoodEvent p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : LearningRate) (b : ReferenceInitializationRun.Boundary p)
    (hcompleted : b.completed = s.val) (hnotStopped : b.crossing = none)
    (i : GeneratedBlockChoiceAverages.Incoming p b) (a : Fin p.K) :
    (blockSupportCount p s rewards a / (512 * (p.m : ℝ))) *
        (originalLaw p).real (sourcePrefixBoundaryCell p s E ids rewards C_star C_h eta b) ≤
      ∫ e in sourcePrefixBoundaryCell p s E ids rewards C_star C_h eta b,
        actualImportanceObservable p ids rewards C_star C_h eta i.1 s a e ∂originalLaw p := by
  let M := sourcePrefixBoundaryCell p s E ids rewards C_star C_h eta b
  let Q := {z : Fin p.K // z ≠ a} × Fin (A_id p)
  let cells : Q → Set (GeneratedBootstrapBlockFiltrationRepair.Coordinates p) := fun q =>
    prefixStartCell p s E ids rewards C_star C_h eta b i.1 a q.1.1 q.2
  let mass := (originalLaw p).real M
  let isolate := (1 - 1 / (p.m : ℝ)) ^ (incomingCount p b - 1)
  let factor := mass * ((1 / (p.m : ℝ)) * (1 / (A_id p : ℝ)) * isolate * (1 / (p.K : ℝ)))
  have hmeas : ∀ q, MeasurableSet (cells q) := fun q =>
    measurableSet_prefixStartCell p s E hE ids rewards C_star C_h eta b i.1 a q.1.1 q.2
  have hdisj : Pairwise (Disjoint on cells) := by
    intro q r hqr
    have hne : (q.1.1, q.2) ≠ (r.1.1, r.2) := by
      intro h
      apply hqr
      apply Prod.ext
      · exact Subtype.ext (congrArg Prod.fst h)
      · exact congrArg (fun v : Fin p.K × Fin (A_id p) => v.2) h
    exact (blockStartEvent_pairwise_disjoint p ids rewards C_star C_h eta i.1 s a hne).mono
      Set.inter_subset_right Set.inter_subset_right
  have hint := actualImportance_integrable_originalLaw p ids rewards C_star C_h eta i.1 s a
  have hsum : (∑ q : Q, (supportedIDZeroCount p s ids rewards a q.2 / 16) * factor) ≤
      ∫ e in M, actualImportanceObservable p ids rewards C_star C_h eta i.1 s a e
        ∂originalLaw p := by
    calc
      _ ≤ ∑ q : Q, ∫ e in cells q,
          actualImportanceObservable p ids rewards C_star C_h eta i.1 s a e ∂originalLaw p := by
        apply Finset.sum_le_sum
        intro q _
        simpa only [factor, mass, isolate, M, mul_assoc] using
          actualImportance_setIntegral_ge_prefixChoice p s E hE ids rewards C_star C_h eta b
            hcompleted hnotStopped i a q.1.1 q.2 q.1.2
      _ = ∫ e in ⋃ q : Q, cells q,
          actualImportanceObservable p ids rewards C_star C_h eta i.1 s a e ∂originalLaw p :=
        (integral_iUnion_fintype hmeas hdisj (fun _ => hint.integrableOn)).symm
      _ ≤ ∫ e in M,
          actualImportanceObservable p ids rewards C_star C_h eta i.1 s a e ∂originalLaw p := by
        apply setIntegral_mono_set hint.integrableOn
          (Filter.Eventually.of_forall fun e =>
            actualImportance_nonneg p ids rewards C_star C_h eta i.1 s a e)
        exact Filter.Eventually.of_forall (Set.iUnion_subset fun _ => Set.inter_subset_left)
  have hcard : Fintype.card {z : Fin p.K // z ≠ a} = p.K - 1 := by
    simp [Fintype.card_subtype_compl]
  have hsum_eq : (∑ q : Q, (supportedIDZeroCount p s ids rewards a q.2 / 16) * factor) =
      mass / (p.m : ℝ) * isolate * (((p.K - 1 : ℕ) : ℝ) / (p.K : ℝ)) *
        ((∑ u : Fin (A_id p), supportedIDZeroCount p s ids rewards a u) /
          (16 * (A_id p : ℝ))) := by
    rw [Fintype.sum_prod_type]
    simp only [← Finset.sum_mul, ← Finset.sum_div, Finset.sum_const, Finset.card_univ,
      hcard, nsmul_eq_mul]
    dsimp [factor]
    ring
  have hsupp := blockSupportCount_nonneg p s rewards a
  have hmass : 0 ≤ mass := measureReal_nonneg
  have hm : 0 < (p.m : ℝ) := Nat.cast_pos.mpr (m_pos p)
  have hA : 0 < (A_id p : ℝ) := Nat.cast_pos.mpr (A_id_pos p)
  have hK : 0 < (p.K : ℝ) := Nat.cast_pos.mpr (K_pos p)
  have hratio : blockSupportCount p s rewards a / 48 ≤
      (∑ u : Fin (A_id p), supportedIDZeroCount p s ids rewards a u) /
        (16 * (A_id p : ℝ)) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 48)
      (mul_pos (by norm_num) hA)).mpr
    have havg := sum_supportedIDZeroCount_lower p s ids rewards a hgood
    linarith only [havg]
  have hisolate : (1 / 4 : ℝ) ≤ isolate := isolation_power_ge_quarter p b i
  have htarget : (1 / 2 : ℝ) ≤ ((p.K - 1 : ℕ) : ℝ) / (p.K : ℝ) := by
    have hKtwo : 2 ≤ p.K := p.two_le_m.trans (Nat.le_of_lt p.m_lt_K)
    rw [Nat.cast_sub (by omega : 1 ≤ p.K), Nat.cast_one]
    apply (le_div_iff₀ hK).mpr
    have hcast : (2 : ℝ) ≤ (p.K : ℝ) := by exact_mod_cast hKtwo
    linarith only [hcast]
  have hprod : (1 / 8 : ℝ) ≤ isolate * (((p.K - 1 : ℕ) : ℝ) / (p.K : ℝ)) := by
    calc
      (1 / 8 : ℝ) = (1 / 4 : ℝ) * (1 / 2 : ℝ) := by norm_num
      _ ≤ _ := mul_le_mul hisolate htarget (by norm_num) (by positivity)
  have hsupport : blockSupportCount p s rewards a / 512 ≤
      isolate * (((p.K - 1 : ℕ) : ℝ) / (p.K : ℝ)) *
        ((∑ u : Fin (A_id p), supportedIDZeroCount p s ids rewards a u) /
          (16 * (A_id p : ℝ))) := by
    calc
      _ ≤ blockSupportCount p s rewards a / 384 := by linarith only [hsupp]
      _ = (1 / 8 : ℝ) * (blockSupportCount p s rewards a / 48) := by ring
      _ ≤ _ := mul_le_mul hprod hratio (by positivity) (by positivity)
  rw [hsum_eq] at hsum
  calc
    _ = (mass / (p.m : ℝ)) * (blockSupportCount p s rewards a / 512) := by ring
    _ ≤ (mass / (p.m : ℝ)) *
        (isolate * (((p.K - 1 : ℕ) : ℝ) / (p.K : ℝ)) *
          ((∑ u : Fin (A_id p), supportedIDZeroCount p s ids rewards a u) /
            (16 * (A_id p : ℝ)))) :=
      mul_le_mul_of_nonneg_left hsupport (div_nonneg hmass hm.le)
    _ ≤ _ := by simpa only [mul_assoc] using hsum

/-- Crossed and informed incoming states have the actual zero observable,
as prescribed by the stopped analytical process. -/
theorem actualImportance_eq_zero_of_crossed_or_informed
    (ids : IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : LearningRate) (i : Follower p.m)
    (s : Fin (n_boot p)) (a : Fin p.K)
    (e : GeneratedBootstrapBlockFiltrationRepair.Coordinates p)
    (h : (ReferenceInitializationRun.run
        (referenceInput p ids rewards C_star C_h eta e) s.val).crossing ≠ none ∨
      (ReferenceInitializationRun.run
        (referenceInput p ids rewards C_star C_h eta e) s.val).activation i ≠ none) :
    actualImportanceObservable p ids rewards C_star C_h eta i s a e = 0 := by
  let x := referenceInput p ids rewards C_star C_h eta e
  apply GeneratedBootstrapPotential.actualImportance_eq_zero_of_disabled x i s _ a
  rcases h with hc | hi
  · change (ReferenceInitializationRun.run x s.val).crossing ≠ none at hc
    simp only [GeneratedBootstrapPotential.actualBlock, dite_eq_right hc]
  · exact GeneratedBootstrapPotential.actualBlock_disabled_of_activated x i s hi

/-- Every boundary fiber is covered, including stopped/informed fibers and
unreachable states. No local branch premise remains in this integral order. -/
theorem actualImportanceMeanLower_setIntegral_le_on_boundaryCell (s : Fin (n_boot p))
    (E : Set (GeneratedBootstrapImportanceMean.SourcePrefix p s)) (hE : MeasurableSet E)
    (ids : IDArray p) (hgood : ids ∈ IdentificationGoodEvent.identificationGoodEvent p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : LearningRate) (i : Follower p.m) (a : Fin p.K)
    (b : ReferenceInitializationRun.Boundary p) :
    (∫ e in sourcePrefixBoundaryCell p s E ids rewards C_star C_h eta b,
      actualImportanceMeanLower p ids rewards C_star C_h eta i s a e ∂originalLaw p) ≤
    ∫ e in sourcePrefixBoundaryCell p s E ids rewards C_star C_h eta b,
      actualImportanceObservable p ids rewards C_star C_h eta i s a e ∂originalLaw p := by
  let M := sourcePrefixBoundaryCell p s E ids rewards C_star C_h eta b
  have hM : MeasurableSet M :=
    measurableSet_sourcePrefixBoundaryCell p s E hE ids rewards C_star C_h eta b
  by_cases hguard : b.crossing = none ∧ b.activation i = none
  · by_cases hcompleted : b.completed = s.val
    · have hi : i ∈ ReferenceInitializationRun.uninformed b := (mem_uninformed b i).mpr hguard.2
      have hlower : (∫ e in M,
          actualImportanceMeanLower p ids rewards C_star C_h eta i s a e ∂originalLaw p) =
          (blockSupportCount p s rewards a / (512 * (p.m : ℝ))) *
            (originalLaw p).real M := by
        calc
          _ = ∫ _ in M, blockSupportCount p s rewards a / (512 * (p.m : ℝ))
              ∂originalLaw p := by
            apply setIntegral_congr_fun hM
            intro e he
            have hb : ReferenceInitializationRun.run
                (referenceInput p ids rewards C_star C_h eta e) s.val = b := he.2
            simp only [actualImportanceMeanLower, actualUnlaunchedUninformedGuard, hb,
              hguard, and_self, ite_true, one_mul]
          _ = _ := by rw [setIntegral_const, smul_eq_mul, mul_comm]
      rw [hlower]
      exact actualImportance_setIntegral_ge_prefixBoundary p s E hE ids hgood rewards
        C_star C_h eta b hcompleted hguard.1 ⟨i, hi⟩ a
    · have hempty : M = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro e he
        have hb : ReferenceInitializationRun.run
            (referenceInput p ids rewards C_star C_h eta e) s.val = b := he.2
        have hc : (ReferenceInitializationRun.run
            (referenceInput p ids rewards C_star C_h eta e) s.val).crossing = none := by
          rw [hb]
          exact hguard.1
        have hprogress := GeneratedBootstrapPotential.completed_eq_of_no_crossing
          (referenceInput p ids rewards C_star C_h eta e) s.val s.isLt.le hc
        rw [hb] at hprogress
        exact hcompleted hprogress
      change (∫ e in M, _ ∂originalLaw p) ≤ ∫ e in M, _ ∂originalLaw p
      rw [hempty, setIntegral_empty, setIntegral_empty]
  · have hzero : (∫ e in M,
        actualImportanceMeanLower p ids rewards C_star C_h eta i s a e ∂originalLaw p) = 0 := by
      calc
        _ = ∫ _ in M, (0 : ℝ) ∂originalLaw p := by
          apply setIntegral_congr_fun hM
          intro e he
          have hb : ReferenceInitializationRun.run
              (referenceInput p ids rewards C_star C_h eta e) s.val = b := he.2
          simp only [actualImportanceMeanLower, actualUnlaunchedUninformedGuard,
            hb, hguard, ite_false, zero_mul, zero_div]
        _ = 0 := integral_zero _ _
    have hzeroActual : (∫ e in M,
        actualImportanceObservable p ids rewards C_star C_h eta i s a e ∂originalLaw p) = 0 := by
      calc
        _ = ∫ _ in M, (0 : ℝ) ∂originalLaw p := by
          apply setIntegral_congr_fun hM
          intro e he
          apply actualImportance_eq_zero_of_crossed_or_informed p ids rewards C_star C_h eta
            i s a e
          have hb : ReferenceInitializationRun.run
              (referenceInput p ids rewards C_star C_h eta e) s.val = b := he.2
          rw [hb]
          exact not_and_or.mp hguard
        _ = 0 := integral_zero _ _
    change (∫ e in M, _ ∂originalLaw p) ≤ ∫ e in M, _ ∂originalLaw p
    rw [hzero, hzeroActual]

/-- The actual countable boundary fibers partition every source-prefix cell,
including fibers with zero original probability. -/
theorem sourcePrefixBoundaryCell_iUnion (s : Fin (n_boot p))
    (E : Set (GeneratedBootstrapImportanceMean.SourcePrefix p s))
    (ids : IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : LearningRate) :
    (⋃ b : ReferenceInitializationRun.Boundary p,
      sourcePrefixBoundaryCell p s E ids rewards C_star C_h eta b) =
        (GeneratedBootstrapBlockFiltrationRepair.sourcePrefix p s.val) ⁻¹' E := by
  ext e
  simp only [Set.mem_iUnion, sourcePrefixBoundaryCell, Set.mem_ofPred_eq,
    Set.mem_preimage]
  exact ⟨fun ⟨_, he, _⟩ => he, fun he => ⟨_, he, rfl⟩⟩

/-- Countable disjoint boundary assembly gives integral order on arbitrary
measurable causal-prefix cells, without any state-atom conditioning. -/
theorem actualImportanceMeanLower_setIntegral_le_on_prefix (s : Fin (n_boot p))
    (E : Set (GeneratedBootstrapImportanceMean.SourcePrefix p s)) (hE : MeasurableSet E)
    (ids : IDArray p) (hgood : ids ∈ IdentificationGoodEvent.identificationGoodEvent p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : LearningRate) (i : Follower p.m) (a : Fin p.K) :
    (∫ e in (GeneratedBootstrapBlockFiltrationRepair.sourcePrefix p s.val) ⁻¹' E,
      actualImportanceMeanLower p ids rewards C_star C_h eta i s a e ∂originalLaw p) ≤
    ∫ e in (GeneratedBootstrapBlockFiltrationRepair.sourcePrefix p s.val) ⁻¹' E,
      actualImportanceObservable p ids rewards C_star C_h eta i s a e ∂originalLaw p := by
  let cells := fun b : ReferenceInitializationRun.Boundary p =>
    sourcePrefixBoundaryCell p s E ids rewards C_star C_h eta b
  have hmeas : ∀ b, MeasurableSet (cells b) := fun b =>
    measurableSet_sourcePrefixBoundaryCell p s E hE ids rewards C_star C_h eta b
  have hdisj : Pairwise (Disjoint on cells) := by
    intro b c hbc
    apply Set.disjoint_left.mpr
    intro e hb hc
    exact hbc (hb.2.symm.trans hc.2)
  have hlower := actualImportanceMeanLower_integrable p ids rewards C_star C_h eta i s a
  have hactual := actualImportance_integrable_originalLaw p ids rewards C_star C_h eta i s a
  have hsumLower := hasSum_integral_iUnion hmeas hdisj hlower.integrableOn
  have hsumActual := hasSum_integral_iUnion hmeas hdisj hactual.integrableOn
  have hle := hsumLower.summable.tsum_le_tsum
    (fun b => actualImportanceMeanLower_setIntegral_le_on_boundaryCell p s E hE ids hgood
      rewards C_star C_h eta i a b) hsumActual.summable
  rw [hsumLower.tsum_eq, hsumActual.tsum_eq] at hle
  simpa only [cells, sourcePrefixBoundaryCell_iUnion] using hle

/-- Every measurable cell of the literal causal boundary sigma algebra is a
source-prefix preimage, so the integral comparison applies to all such cells. -/
theorem actualImportanceMeanLower_setIntegral_le (s : Fin (n_boot p))
    (ids : IDArray p) (hgood : ids ∈ IdentificationGoodEvent.identificationGoodEvent p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : LearningRate) (i : Follower p.m) (a : Fin p.K)
    (M : Set (GeneratedBootstrapBlockFiltrationRepair.Coordinates p))
    (hM : MeasurableSet[boundarySigma p s.val] M) :
    (∫ e in M, actualImportanceMeanLower p ids rewards C_star C_h eta i s a e
      ∂originalLaw p) ≤
    ∫ e in M, actualImportanceObservable p ids rewards C_star C_h eta i s a e
      ∂originalLaw p := by
  obtain ⟨E, hE, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hM
  exact actualImportanceMeanLower_setIntegral_le_on_prefix p s E hE ids hgood rewards
    C_star C_h eta i a

/-- The actual source conditional importance lower mean under the original
coordinate law and the causal incoming boundary sigma algebra. All local
boundary, isolation, private-ID and target conditions have been assembled. -/
theorem actualImportanceMeanLower_le_condExp
    (ids : IDArray p) (hgood : ids ∈ IdentificationGoodEvent.identificationGoodEvent p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : LearningRate) (i : Follower p.m)
    (s : Fin (n_boot p)) (a : Fin p.K) :
    ∀ᵐ e ∂originalLaw p,
      actualImportanceMeanLower p ids rewards C_star C_h eta i s a e ≤
        ((originalLaw p)[actualImportanceObservable p ids rewards C_star C_h eta i s a |
          boundarySigma p s.val]) e := by
  have hm : boundarySigma p s.val ≤
      (inferInstance : MeasurableSpace (GeneratedBootstrapBlockFiltrationRepair.Coordinates p)) :=
    boundaryFiltration_le_ambient p s.val
  have hlower : StronglyMeasurable[boundarySigma p s.val]
      (actualImportanceMeanLower p ids rewards C_star C_h eta i s a) :=
    (actualImportanceMeanLower_measurable_boundary p ids rewards C_star C_h eta i s a).stronglyMeasurable
  have hcond : StronglyMeasurable[boundarySigma p s.val]
      ((originalLaw p)[actualImportanceObservable p ids rewards C_star C_h eta i s a |
        boundarySigma p s.val]) := stronglyMeasurable_condExp
  have hlint := actualImportanceMeanLower_integrable p ids rewards C_star C_h eta i s a
  have haint := actualImportance_integrable_originalLaw p ids rewards C_star C_h eta i s a
  have hcint : Integrable
      ((originalLaw p)[actualImportanceObservable p ids rewards C_star C_h eta i s a |
        boundarySigma p s.val]) (originalLaw p) := integrable_condExp
  apply ae_of_ae_trim hm
  apply ae_le_of_forall_setIntegral_le (Integrable.trim hm hlint hlower)
    (Integrable.trim hm hcint hcond)
  intro M hM _
  rw [← setIntegral_trim hm hlower hM, ← setIntegral_trim hm hcond hM,
    setIntegral_condExp hm haint hM]
  exact actualImportanceMeanLower_setIntegral_le p s ids hgood rewards C_star C_h eta i a M hM

/-- The deterministic normalizing bound in the source is strictly positive. -/
theorem importance_scale_pos : (0 : ℝ) < 2 * (p.K : ℝ) * B_boot p := by
  have hK : (0 : ℝ) < (p.K : ℝ) := Nat.cast_pos.mpr (K_pos p)
  have hB : (0 : ℝ) < (B_boot p : ℝ) := Nat.cast_pos.mpr (B_boot_pos p)
  positivity

/-- Dividing by the positive source bound gives the conditional mean needed
by a later bounded-observable consumer. -/
theorem scaledActualImportanceMeanLower_le_condExp
    (ids : IDArray p) (hgood : ids ∈ IdentificationGoodEvent.identificationGoodEvent p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : LearningRate) (i : Follower p.m)
    (s : Fin (n_boot p)) (a : Fin p.K) :
    ∀ᵐ e ∂originalLaw p,
      actualImportanceMeanLower p ids rewards C_star C_h eta i s a e /
          (2 * (p.K : ℝ) * B_boot p) ≤
        ((originalLaw p)[scaledActualImportanceObservable p ids rewards C_star C_h eta i s a |
          boundarySigma p s.val]) e := by
  let U : ℝ := 2 * (p.K : ℝ) * B_boot p
  have hmean := actualImportanceMeanLower_le_condExp p ids hgood rewards C_star C_h eta i s a
  have hscale := condExp_smul (μ := originalLaw p) U⁻¹
    (actualImportanceObservable p ids rewards C_star C_h eta i s a) (boundarySigma p s.val)
  have hfun : scaledActualImportanceObservable p ids rewards C_star C_h eta i s a =
      U⁻¹ • actualImportanceObservable p ids rewards C_star C_h eta i s a := by
    funext e
    change _ / U = U⁻¹ * _
    exact div_eq_inv_mul _ U
  rw [hfun]
  filter_upwards [hmean, hscale] with e he hs
  rw [hs]
  change _ / U ≤ U⁻¹ * _
  rw [← div_eq_inv_mul]
  exact div_le_div_of_nonneg_right he (importance_scale_pos p).le

/-- Literal normalization of the accepted Nat-indexed actual process. -/
def normalizedActualImportanceProcess
    (ids : IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : LearningRate) (i : Follower p.m) (a : Fin p.K)
    (n : ℕ) (e : GeneratedBootstrapBlockFiltrationRepair.Coordinates p) : ℝ :=
  actualImportanceProcess p ids rewards C_star C_h eta i a n e /
    (2 * (p.K : ℝ) * B_boot p)

/-- Exact opportunity alignment uses the accepted process at `s.val + 1`. -/
theorem normalizedActualImportanceProcess_at_opportunity
    (ids : IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : LearningRate) (i : Follower p.m) (a : Fin p.K)
    (s : Fin (n_boot p)) (e : GeneratedBootstrapBlockFiltrationRepair.Coordinates p) :
    normalizedActualImportanceProcess p ids rewards C_star C_h eta i a (s.val + 1) e =
      scaledActualImportanceObservable p ids rewards C_star C_h eta i s a e := by
  unfold normalizedActualImportanceProcess scaledActualImportanceObservable
  rw [actualImportanceProcess_at_opportunity p ids rewards C_star C_h eta i a s e]

/-- The normalized shifted actual process has the same causal conditional
lower mean. This statement makes no support-tail or concentration claim. -/
theorem normalizedActualImportanceProcess_condExp_ge_at_opportunity
    (ids : IDArray p) (hgood : ids ∈ IdentificationGoodEvent.identificationGoodEvent p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : LearningRate) (i : Follower p.m)
    (s : Fin (n_boot p)) (a : Fin p.K) :
    ∀ᵐ e ∂originalLaw p,
      actualImportanceMeanLower p ids rewards C_star C_h eta i s a e /
          (2 * (p.K : ℝ) * B_boot p) ≤
        ((originalLaw p)[normalizedActualImportanceProcess p ids rewards C_star C_h eta
          i a (s.val + 1) | boundarySigma p s.val]) e := by
  have heq : normalizedActualImportanceProcess p ids rewards C_star C_h eta i a (s.val + 1) =
      scaledActualImportanceObservable p ids rewards C_star C_h eta i s a := by
    funext e
    exact normalizedActualImportanceProcess_at_opportunity p ids rewards C_star C_h eta i a s e
  rw [heq]
  exact scaledActualImportanceMeanLower_le_condExp p ids hgood rewards C_star C_h eta i s a

end Bandits.Support.GeneratedImportanceConditionalMean

end
