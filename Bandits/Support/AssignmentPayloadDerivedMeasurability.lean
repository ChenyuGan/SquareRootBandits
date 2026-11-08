/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.LaterAssignmentAnchorMeasurability
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions

import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Group.Arithmetic

/-!
# Measurability of derived assignment payload fields

On the existing observation-comap carrier, the anchor remains an ordinary
product-Borel real vector. The recording rates, natural exponents, and
minimum-label-tiebroken auxiliary arm are the actual fields of
`AssignmentStartPayload.Input`.

Sources: `sources/zip4/manuscript/04_slow_fast_learner.tex:96-138`,
`sources/zip4/manuscript/06_interruptions.tex:46-61`, and
`sources/zip4/manuscript/appendix_b_communication.tex:25-55`.
-/

@[expose] public section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.AssignmentStartPayload
open Bandits.Support.CanonicalFastSampling
open Bandits.Support.CanonicalRecordingRates
open Bandits.Support.LaterAssignmentAnchorMeasurability
open Bandits.Support.LaterAssignmentStartMeasurability
open Bandits.Support.ProductSetLaw

namespace Bandits.Support.AssignmentPayloadDerivedMeasurability

variable {p : ConstructorDimensions.Parameters}
abbrev LearningRate := Bandits.Support.ReferencePrelaunchFollower.LearningRate
variable {eta : LearningRate}

/-- The original anchor field, with no change to its carrier. -/
def inputAnchor (s : AssignmentStartPayload.Input p eta) : Fin p.K → ℝ :=
  s.anchor

/-- The complete vector of the payload's actual canonical recording rates. -/
noncomputable def inputRate (s : AssignmentStartPayload.Input p eta) : Fin p.K → ℝ :=
  fun i => s.rate i

/-- The complete vector of the payload's actual natural exponents. -/
noncomputable def inputExponent (s : AssignmentStartPayload.Input p eta) : Fin p.K → ℕ :=
  fun i => s.exponent i

/-- The payload's actual minimum-anchor fast arm with label tie-breaking. -/
noncomputable def inputAuxiliary (s : AssignmentStartPayload.Input p eta) : Fin p.K :=
  s.assignment.auxiliary

/-- The four literal derived payload fields, retaining both full vectors. -/
noncomputable def inputDerivedFields (s : AssignmentStartPayload.Input p eta) :
    (Fin p.K → ℝ) × ((Fin p.K → ℝ) × ((Fin p.K → ℕ) × Fin p.K)) :=
  (inputAnchor s, (inputRate s, (inputExponent s, inputAuxiliary s)))

private theorem measurable_payloadObservation :
    Measurable (LaterAssignmentStartMeasurability.payloadObservation
      (p := p) (eta := eta)) :=
  comap_measurable _

private theorem measurable_inputAnchor_core :
    Measurable (inputAnchor (p := p) (eta := eta)) := by
  change Measurable (fun s : AssignmentStartPayload.Input p eta =>
    (LaterAssignmentStartMeasurability.payloadObservation s).2.2.2.1)
  exact measurable_fst.comp
    (measurable_snd.comp
      (measurable_snd.comp
        (measurable_snd.comp measurable_payloadObservation)))

private theorem measurable_inputSlowSet :
    Measurable (fun s : AssignmentStartPayload.Input p eta => s.slowSet.1) := by
  change Measurable (fun s : AssignmentStartPayload.Input p eta =>
    (LaterAssignmentStartMeasurability.payloadObservation s).2.2.1)
  exact measurable_fst.comp
    (measurable_snd.comp (measurable_snd.comp measurable_payloadObservation))

/-- Finite anchor products are Borel by the existing finite-product API. -/
private theorem measurable_setWeight (S : Finset (Fin p.K)) :
    Measurable (fun v : Fin p.K → ℝ => ProductSetLaw.setWeight v S) := by
  unfold ProductSetLaw.setWeight
  exact Finset.measurable_fun_prod S fun i _ => measurable_pi_apply i

private theorem measurable_totalMass (support : Finset (Finset (Fin p.K))) :
    Measurable (fun v : Fin p.K → ℝ =>
      FiniteNormalization.totalMass support (ProductSetLaw.setWeight v)) := by
  unfold FiniteNormalization.totalMass
  exact Finset.measurable_fun_sum support fun S _ => measurable_setWeight S

/-- The literal product-set inclusion marginal is Borel in the full anchor. -/
private theorem measurable_theta (m : ℕ) (i : Fin p.K) :
    Measurable (fun v : Fin p.K → ℝ => ProductSetLaw.theta m v i) := by
  unfold ProductSetLaw.theta FiniteNormalization.mass
  apply Finset.measurable_fun_sum
  intro S _
  unfold FiniteNormalization.normalizedWeight
  exact (measurable_setWeight S).div
    (measurable_totalMass (ProductSetLaw.support p.K m))

/-- The literal scalar threshold `f` is Borel by real arithmetic. -/
private theorem measurable_f (i : Fin p.K) :
    Measurable (fun v : Fin p.K → ℝ => CanonicalRecordingRates.f p v i) := by
  have htheta := measurable_theta (p := p) p.m i
  unfold CanonicalRecordingRates.f
  fun_prop

/-- The real log base two is Borel, including its total value at zero. -/
private theorem measurable_logb_two : Measurable (Real.logb 2 : ℝ → ℝ) := by
  change Measurable (fun x : ℝ => Real.log x / Real.log 2)
  exact (Real.measurable_log).div_const (Real.log 2)

/-- The literal dyadic ceiling is Borel by `Int.measurable_ceil` and real
constant-base powers. -/
theorem measurable_dyadicCeiling :
    Measurable Bandits.Support.DyadicEnvelope.dyadicCeiling := by
  unfold Bandits.Support.DyadicEnvelope.dyadicCeiling
  have hceil : Measurable (fun x : ℝ => Int.ceil (Real.logb 2 x)) :=
    Int.measurable_ceil.comp measurable_logb_two
  have hcast : Measurable (fun z : ℤ => (z : ℝ)) :=
    measurable_of_countable (fun z : ℤ => (z : ℝ))
  exact (Real.continuous_const_rpow (by norm_num : (2 : ℝ) ≠ 0)).measurable.comp
    (hcast.comp hceil)

private theorem measurable_rateScalar (i : Fin p.K) :
    Measurable (fun v : Fin p.K → ℝ =>
      CanonicalRecordingRates.xi p eta.val v i) := by
  unfold CanonicalRecordingRates.xi
  exact measurable_dyadicCeiling.comp
    ((measurable_const : Measurable fun _ : Fin p.K → ℝ =>
      CanonicalRecordingRates.beta p eta.val).max
      (measurable_f (p := p) i))

private theorem measurable_exponentScalar (i : Fin p.K) :
    Measurable (fun v : Fin p.K → ℝ =>
      Int.toNat (-Int.ceil (Real.logb 2
        (max (CanonicalRecordingRates.beta p eta.val)
          (CanonicalRecordingRates.f p v i))))) := by
  have hthreshold : Measurable (fun v : Fin p.K → ℝ =>
      max (CanonicalRecordingRates.beta p eta.val)
        (CanonicalRecordingRates.f p v i)) :=
    (measurable_const : Measurable fun _ : Fin p.K → ℝ =>
      CanonicalRecordingRates.beta p eta.val).max (measurable_f (p := p) i)
  have hlog : Measurable (fun v : Fin p.K → ℝ =>
      Real.logb 2 (max (CanonicalRecordingRates.beta p eta.val)
        (CanonicalRecordingRates.f p v i))) := by
    change Measurable (fun v : Fin p.K → ℝ =>
      Real.log (max (CanonicalRecordingRates.beta p eta.val)
        (CanonicalRecordingRates.f p v i)) / Real.log 2)
    exact (Real.measurable_log.comp hthreshold).div_const (Real.log 2)
  have hceil : Measurable (fun v : Fin p.K → ℝ =>
      Int.ceil (Real.logb 2 (max (CanonicalRecordingRates.beta p eta.val)
        (CanonicalRecordingRates.f p v i)))) :=
    Int.measurable_ceil.comp hlog
  have hnegative : Measurable (fun v : Fin p.K → ℝ =>
      -Int.ceil (Real.logb 2 (max (CanonicalRecordingRates.beta p eta.val)
        (CanonicalRecordingRates.f p v i)))) := hceil.neg
  exact (measurable_of_countable Int.toNat).comp hnegative

private theorem exponent_eq_sourceFormula (s : AssignmentStartPayload.Input p eta)
    (i : Fin p.K) :
    s.exponent i = Int.toNat (-Int.ceil (Real.logb 2
      (max (CanonicalRecordingRates.beta p eta.val)
        (CanonicalRecordingRates.f p s.anchor i)))) := by
  have hnonneg : 0 ≤ -Int.ceil (Real.logb 2 (s.rateThreshold i)) := by
    rw [← s.exponent_intCast i]
    exact Int.natCast_nonneg _
  have hcast : (s.exponent i : ℤ) =
      ((Int.toNat (-Int.ceil (Real.logb 2 (s.rateThreshold i))) : ℕ) : ℤ) := by
    rw [Int.toNat_of_nonneg hnonneg]
    exact s.exponent_intCast i
  have hnat : s.exponent i =
      Int.toNat (-Int.ceil (Real.logb 2 (s.rateThreshold i))) := by
    exact_mod_cast hcast
  simpa [AssignmentStartPayload.Input.rateThreshold] using hnat

private theorem measurable_rateOf {α : Type*} [MeasurableSpace α]
    (f : α → AssignmentStartPayload.Input p eta)
    (ha : Measurable fun x => (f x).anchor) :
    Measurable (fun x => inputRate (f x)) := by
  apply measurable_pi_iff.mpr
  intro i
  have hcanonical : Measurable (fun x =>
      CanonicalRecordingRates.xi p eta.val (f x).anchor i) :=
    (measurable_rateScalar (p := p) (eta := eta) i).comp ha
  have heq : (fun x => (f x).rate i) = fun x =>
      CanonicalRecordingRates.xi p eta.val (f x).anchor i := by
    funext x
    exact (f x).rate_eq_canonical i
  change Measurable (fun x => (f x).rate i)
  rw [heq]
  exact hcanonical

private theorem measurable_exponentOf {α : Type*} [MeasurableSpace α]
    (f : α → AssignmentStartPayload.Input p eta)
    (ha : Measurable fun x => (f x).anchor) :
    Measurable (fun x => inputExponent (f x)) := by
  apply measurable_pi_iff.mpr
  intro i
  have hcanonical : Measurable (fun x => Int.toNat (-Int.ceil (Real.logb 2
      (max (CanonicalRecordingRates.beta p eta.val)
        (CanonicalRecordingRates.f p (f x).anchor i))))) :=
    (measurable_exponentScalar (p := p) (eta := eta) i).comp ha
  have heq : (fun x => (f x).exponent i) = fun x =>
      Int.toNat (-Int.ceil (Real.logb 2
        (max (CanonicalRecordingRates.beta p eta.val)
          (CanonicalRecordingRates.f p (f x).anchor i)))) := by
    funext x
    exact exponent_eq_sourceFormula (f x) i
  change Measurable (fun x => (f x).exponent i)
  rw [heq]
  exact hcanonical

private theorem measurable_auxiliaryOf {α : Type*} [MeasurableSpace α]
    (f : α → AssignmentStartPayload.Input p eta)
    (ha : Measurable fun x => (f x).anchor)
    (hs : Measurable fun x => (f x).slowSet.1) :
    Measurable (fun x => inputAuxiliary (f x)) := by
  classical
  apply measurable_to_countable'
  intro j
  have hfast (k : Fin p.K) :
      MeasurableSet {x | k ∈ fastArmFinset (f x).slowSet} := by
    have hset : {x | k ∈ fastArmFinset (f x).slowSet} =
        {x | k ∉ (f x).slowSet.1} := by
      ext x
      simp [CanonicalFastSampling.fastArmFinset]
    rw [hset]
    exact (measurableSet_notMem_finset k).preimage hs
  have hcomparison (k : Fin p.K) : MeasurableSet
      {x | (f x).anchor j < (f x).anchor k ∨
        ((f x).anchor j = (f x).anchor k ∧ j ≤ k)} := by
    have hj : Measurable fun x => (f x).anchor j :=
      (measurable_pi_apply j).comp ha
    have hk : Measurable fun x => (f x).anchor k :=
      (measurable_pi_apply k).comp ha
    have hlt : MeasurableSet {x | (f x).anchor j < (f x).anchor k} :=
      measurableSet_lt hj hk
    have heq : MeasurableSet {x | (f x).anchor j = (f x).anchor k} :=
      measurableSet_eq_fun hj hk
    have htie : MeasurableSet
        {x | (f x).anchor j = (f x).anchor k ∧ j ≤ k} := by
      by_cases hjk : j ≤ k
      · simpa [hjk] using heq
      · simp [hjk]
    exact hlt.union htie
  have hminimum : MeasurableSet {x | ∀ k : Fin p.K,
      k ∈ fastArmFinset (f x).slowSet →
        ((f x).anchor j < (f x).anchor k ∨
          ((f x).anchor j = (f x).anchor k ∧ j ≤ k))} := by
    have hsets : ∀ k : Fin p.K, MeasurableSet
        ({x | k ∈ fastArmFinset (f x).slowSet}ᶜ ∪
          {x | (f x).anchor j < (f x).anchor k ∨
            ((f x).anchor j = (f x).anchor k ∧ j ≤ k)}) := by
      intro k
      exact (hfast k).compl.union (hcomparison k)
    have hInter : MeasurableSet (⋂ k : Fin p.K,
        ({x | k ∈ fastArmFinset (f x).slowSet}ᶜ ∪
          {x | (f x).anchor j < (f x).anchor k ∨
            ((f x).anchor j = (f x).anchor k ∧ j ≤ k)})) :=
      MeasurableSet.iInter hsets
    have hEq : {x | ∀ k : Fin p.K,
        k ∈ fastArmFinset (f x).slowSet →
          ((f x).anchor j < (f x).anchor k ∨
            ((f x).anchor j = (f x).anchor k ∧ j ≤ k))} =
        ⋂ k : Fin p.K,
          ({x | k ∈ fastArmFinset (f x).slowSet}ᶜ ∪
            {x | (f x).anchor j < (f x).anchor k ∨
              ((f x).anchor j = (f x).anchor k ∧ j ≤ k)}) := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_union,
        Set.mem_compl_iff]
      constructor
      · intro h k
        by_cases hk : k ∈ fastArmFinset (f x).slowSet
        · exact Or.inr (h k hk)
        · exact Or.inl hk
      · intro h k hk
        rcases h k with hnot | hcmp
        · exact False.elim (hnot hk)
        · exact hcmp
    rw [hEq]
    exact hInter
  have hfiber : {x | inputAuxiliary (f x) = j} =
      {x | j ∈ fastArmFinset (f x).slowSet} ∩
        {x | ∀ k : Fin p.K,
          k ∈ fastArmFinset (f x).slowSet →
            ((f x).anchor j < (f x).anchor k ∨
              ((f x).anchor j = (f x).anchor k ∧ j ≤ k))} := by
    ext x
    constructor
    · intro haux
      change (f x).auxiliaryArm = j at haux
      have hspec := (f x).auxiliaryArm_spec
      constructor
      · rw [← haux]
        exact hspec.1
      · intro k hk
        have hle : (f x).anchor (f x).auxiliaryArm ≤ (f x).anchor k :=
          hspec.2.1 k hk
        rcases lt_or_eq_of_le hle with hlt | heq
        · exact Or.inl (by simpa [haux] using hlt)
        · have hlabel : (f x).auxiliaryArm ≤ k :=
            hspec.2.2 k hk heq
          exact Or.inr ⟨by simpa [haux] using heq,
            by simpa [haux] using hlabel⟩
    · rintro ⟨hmem, hminimum⟩
      change (f x).auxiliaryArm = j
      have hmin : ∀ k, k ∈ fastArmFinset (f x).slowSet →
          (f x).anchor j ≤ (f x).anchor k := by
        intro k hk
        rcases hminimum k hk with hlt | ⟨heq, _⟩
        · exact hlt.le
        · exact le_of_eq heq
      have htie : ∀ k, k ∈ fastArmFinset (f x).slowSet →
          (f x).anchor j = (f x).anchor k → j ≤ k := by
        intro k hk heq
        rcases hminimum k hk with hlt | ⟨_, hjk⟩
        · exact False.elim ((ne_of_lt hlt) heq)
        · exact hjk
      exact ((f x).auxiliaryArm_characterization hmem hmin htie).symm
  change MeasurableSet {x | inputAuxiliary (f x) = j}
  rw [hfiber]
  exact (hfast j).inter hminimum

/-- The input anchor is measurable on its existing comap carrier. -/
theorem measurable_inputAnchor :
    Measurable (inputAnchor (p := p) (eta := eta)) :=
  measurable_inputAnchor_core (p := p) (eta := eta)

/-- Every coordinate of the literal recording-rate vector is Borel. -/
theorem measurable_inputRate :
    Measurable (inputRate (p := p) (eta := eta)) :=
  measurable_rateOf (p := p) (eta := eta) id measurable_inputAnchor_core

/-- Every coordinate of the actual natural exponent vector is measurable. -/
theorem measurable_inputExponent :
    Measurable (inputExponent (p := p) (eta := eta)) :=
  measurable_exponentOf (p := p) (eta := eta) id measurable_inputAnchor_core

/-- The actual auxiliary projection is measurable by its finite comparison
fibers on each slow-set fiber. -/
theorem measurable_inputAuxiliary :
    Measurable (inputAuxiliary (p := p) (eta := eta)) :=
  measurable_auxiliaryOf (p := p) (eta := eta) id
    measurable_inputAnchor_core measurable_inputSlowSet

/-- The tuple of the original anchor and all actual derived payload fields is
Borel on `payloadInputMeasurableSpace`. -/
theorem measurable_inputDerivedFields :
    Measurable (inputDerivedFields (p := p) (eta := eta)) := by
  exact measurable_inputAnchor_core.prodMk
    (measurable_inputRate.prodMk
      (measurable_inputExponent.prodMk measurable_inputAuxiliary))

/-- The same literal tuple on the varying joint local-start input. -/
noncomputable def jointInputDerivedFields
    (z : LaterAssignmentAnchorMeasurability.JointLocalStartInput p eta) :=
  inputDerivedFields z.1

private theorem measurable_jointOldPayload :
    Measurable (fun z : LaterAssignmentAnchorMeasurability.JointLocalStartInput p eta =>
      z.1) := by
  rw [LaterAssignmentStartMeasurability.payloadInputMeasurableSpace]
  apply measurable_comap_iff.mpr
  simpa only [Function.comp_def] using
    LaterAssignmentAnchorMeasurability.measurable_jointPayloadObservation
      (p := p) (eta := eta)

/-- The original anchor projection on `JointLocalStartInput` is Borel. -/
theorem measurable_jointInputAnchor :
    Measurable (fun z : LaterAssignmentAnchorMeasurability.JointLocalStartInput p eta =>
      (z.1).anchor) :=
  measurable_inputAnchor.comp measurable_jointOldPayload

/-- The actual full rate vector lifted along the existing joint payload
observation is Borel. -/
theorem measurable_jointInputRate :
    Measurable (fun z : LaterAssignmentAnchorMeasurability.JointLocalStartInput p eta =>
      inputRate z.1) :=
  measurable_inputRate.comp measurable_jointOldPayload

/-- The actual full exponent vector lifted along the existing joint payload
observation is Borel. -/
theorem measurable_jointInputExponent :
    Measurable (fun z : LaterAssignmentAnchorMeasurability.JointLocalStartInput p eta =>
      inputExponent z.1) :=
  measurable_inputExponent.comp measurable_jointOldPayload

/-- The actual tie-broken auxiliary arm lifted along the existing joint
payload observation is Borel. -/
theorem measurable_jointInputAuxiliary :
    Measurable (fun z : LaterAssignmentAnchorMeasurability.JointLocalStartInput p eta =>
      inputAuxiliary z.1) :=
  measurable_inputAuxiliary.comp measurable_jointOldPayload

/-- The complete literal derived-field tuple is Borel on the existing joint
local-start carrier. -/
theorem measurable_jointInputDerivedFields :
    Measurable (jointInputDerivedFields (p := p) (eta := eta)) :=
  measurable_inputDerivedFields.comp measurable_jointOldPayload

end Bandits.Support.AssignmentPayloadDerivedMeasurability

end
