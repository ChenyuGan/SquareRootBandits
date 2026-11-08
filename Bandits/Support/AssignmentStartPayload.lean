/-
Copyright (c) 2026 The Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ConstructorDimensions
public import Bandits.Support.CanonicalAssignmentVector
public import Bandits.Support.CanonicalFastSampling
public import Bandits.Support.CanonicalRecordingRates
public import Bandits.Support.DyadicEnvelope
public import Bandits.Support.OrdinaryMessageCodec
public import Bandits.Support.ActiveRoundActions
public import Bandits.Support.FirstAssignmentLaunch
public import Bandits.Support.ReferencePrelaunchFollower
public import Mathlib.Data.Finset.Max
public import Mathlib.Order.Prod.Lex.Basic

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega

/-!
# Canonical DOWN payloads at assignment starts

This module packages one already selected supported slow set, one frozen
positive anchor, and bounded current queues into the source's ordinary DOWN
records. It does not assert how those local inputs were produced.

Sources: `sources/zip4/manuscript/04_slow_fast_learner.tex:96-124`,
`sources/zip4/manuscript/05_binary_transport.tex:62-70`, and
`sources/zip4/manuscript/06_interruptions.tex:46-61,123-189`.

The rates are the literal `CanonicalRecordingRates.xi` values. The selected
auxiliary arm is the lexicographic minimum of `(anchor weight, arm label)` on
the existing slow-set complement. Records and words use the existing codec.
These are internal constructions; they establish no sampling law, physical
provenance, acceptance event, or chronological execution claim.
-/

@[expose] public section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.CanonicalOrientedSetLaw
open Bandits.Support.CanonicalFastSampling
open Bandits.Support.CanonicalAssignmentVector
open Bandits.Support.CanonicalRecordingRates
open Bandits.Support.OrdinaryMessageCodec
open Bandits.Support.ActiveRoundActions
open Bandits.Support.ReferencePrelaunchFollower

namespace Bandits.Support.AssignmentStartPayload

/-- Local source data for packaging one assignment start. The slow set and
queues are supplied snapshots; the fields assert no law or physical
provenance. Rates, exponents, the auxiliary arm, and codec records are derived
inside this module.

Source: `sources/zip4/manuscript/04_slow_fast_learner.tex:96-113` and
`sources/zip4/manuscript/06_interruptions.tex:46-60`. -/
structure Input (p : Parameters) (eta : LearningRate) where
  eta_le_source_cap : eta.val ≤
    1 / (1024 * (p.m : ℝ) * (p.K : ℝ) * (L_stab p : ℝ))
  n : ℕ
  n_eq_eta_mul_D : (n : ℝ) = eta.val * (D p : ℝ)
  sigma : Fin p.T
  slowSet : CanonicalOrientedSetLaw.SlowSet p.K p.m
  anchor : Fin p.K → ℝ
  anchor_pos : ∀ i, 0 < anchor i
  queues : Fin p.K → ℕ
  queues_le_TD : ∀ i, queues i ≤ p.T * D p

namespace Input

variable {p : Parameters} {eta : LearningRate} (s : Input p eta)

/-- The source's rate at any arm, with the supplied frozen anchor. -/
noncomputable def rate (i : Fin p.K) : ℝ :=
  CanonicalRecordingRates.xi p eta.val s.anchor i

/-- The source's literal max-before-dyadic-rounding input. -/
noncomputable def rateThreshold (i : Fin p.K) : ℝ :=
  max (CanonicalRecordingRates.beta p eta.val)
    (CanonicalRecordingRates.f p s.anchor i)

/-- The rate operation is definitionally the source's canonical recording
rate at every arm; callers cannot supply admissible alternatives. -/
theorem rate_eq_canonical (i : Fin p.K) :
    s.rate i = CanonicalRecordingRates.xi p eta.val s.anchor i := rfl

/-- The canonical rate is at least the literal source floor `β`. -/
theorem beta_le_rate (i : Fin p.K) :
    CanonicalRecordingRates.beta p eta.val ≤ s.rate i := by
  rw [rate]
  exact CanonicalRecordingRates.beta_le_xi p eta.property s.anchor i

/-- Each natural-valued queue is in the source's closed interval `[0, TD]`. -/
theorem queue_mem_Icc (i : Fin p.K) :
    s.queues i ∈ Set.Icc (0 : ℕ) (p.T * D p) :=
  ⟨Nat.zero_le _, s.queues_le_TD i⟩

/-- The lexicographically least `(frozen anchor weight, arm label)` key in
the actual complement of the supplied supported slow set. -/
noncomputable def minimumKey : ℝ ×ₗ Fin p.K := by
  classical
  have hnonempty : (fastArmFinset s.slowSet).Nonempty := by
    apply Finset.card_pos.mp
    have h := CanonicalFastSampling.fastArmFinset_card_ge_two s.slowSet
    omega
  exact (fastArmFinset s.slowSet).image
    (fun j => toLex (s.anchor j, j)) |>.min'
      (by
        rcases hnonempty with ⟨j, hj⟩
        exact ⟨toLex (s.anchor j, j),
          Finset.mem_image.mpr ⟨j, hj, rfl⟩⟩)

/-- The complement is nonempty because every supported slow set leaves at
least two fast arms. -/
theorem fastComplement_nonempty : (fastArmFinset s.slowSet).Nonempty := by
  apply Finset.card_pos.mp
  have h := CanonicalFastSampling.fastArmFinset_card_ge_two s.slowSet
  omega

/-- The selected auxiliary arm is the arm component of the finite lexicographic
minimum. -/
noncomputable def auxiliaryArm : Fin p.K :=
  (ofLex s.minimumKey).2

theorem minimumKey_nonempty :
    ((fastArmFinset s.slowSet).image
      (fun j => toLex (s.anchor j, j))).Nonempty := by
  classical
  rcases s.fastComplement_nonempty with ⟨j, hj⟩
  exact ⟨toLex (s.anchor j, j), Finset.mem_image.mpr ⟨j, hj, rfl⟩⟩

/-- The minimum key is represented by its selected arm in the complement. -/
theorem auxiliaryKey_mem :
    s.minimumKey ∈ (fastArmFinset s.slowSet).image
      (fun j => toLex (s.anchor j, j)) :=
  Finset.min'_mem _ s.minimumKey_nonempty

/-- Exact key identity for the selected arm. -/
theorem auxiliaryKey_eq :
    toLex (s.anchor s.auxiliaryArm, s.auxiliaryArm) = s.minimumKey := by
  classical
  rcases Finset.mem_image.mp s.auxiliaryKey_mem with ⟨j, hj, hkey⟩
  have hp : (s.anchor j, j) = ofLex s.minimumKey := by
    simpa only [ofLex_toLex] using congrArg ofLex hkey
  have hj_aux : j = s.auxiliaryArm := congrArg Prod.snd hp
  subst j
  exact hkey

/-- The selected auxiliary arm is in the slow-set complement. -/
theorem auxiliaryArm_mem_complement :
    s.auxiliaryArm ∈ fastArmFinset s.slowSet := by
  classical
  rcases Finset.mem_image.mp s.auxiliaryKey_mem with ⟨j, hj, hkey⟩
  have hp : (s.anchor j, j) = ofLex s.minimumKey := by
    simpa only [ofLex_toLex] using congrArg ofLex hkey
  have hj_aux : j = s.auxiliaryArm := congrArg Prod.snd hp
  simpa [hj_aux] using hj

/-- The chosen arm has minimum frozen anchor weight on the complement. -/
theorem auxiliaryArm_anchor_minimum (j : Fin p.K)
    (hj : j ∈ fastArmFinset s.slowSet) :
    s.anchor s.auxiliaryArm ≤ s.anchor j := by
  have hkey : s.minimumKey ≤ toLex (s.anchor j, j) :=
    Finset.min'_le _ _ (Finset.mem_image.mpr ⟨j, hj, rfl⟩)
  rw [← s.auxiliaryKey_eq] at hkey
  rcases Prod.Lex.toLex_le_toLex.mp hkey with hlt | ⟨heq, _⟩
  · exact hlt.le
  · exact le_of_eq heq

/-- Equal-weight complement arms are ordered by the smallest arm label. -/
theorem auxiliaryArm_label_minimum (j : Fin p.K)
    (hj : j ∈ fastArmFinset s.slowSet)
    (hweight : s.anchor s.auxiliaryArm = s.anchor j) :
    s.auxiliaryArm ≤ j := by
  have hkey : s.minimumKey ≤ toLex (s.anchor j, j) :=
    Finset.min'_le _ _ (Finset.mem_image.mpr ⟨j, hj, rfl⟩)
  rw [← s.auxiliaryKey_eq] at hkey
  rcases Prod.Lex.toLex_le_toLex.mp hkey with hlt | ⟨_, hle⟩
  · exact False.elim ((not_lt_of_ge (le_of_eq hweight.symm)) hlt)
  · exact hle

/-- Full membership, weight-minimum, and label-tie characterization of the
finite minimizer. -/
theorem auxiliaryArm_spec :
    s.auxiliaryArm ∈ fastArmFinset s.slowSet ∧
      (∀ j, j ∈ fastArmFinset s.slowSet →
        s.anchor s.auxiliaryArm ≤ s.anchor j) ∧
      (∀ j, j ∈ fastArmFinset s.slowSet →
        s.anchor s.auxiliaryArm = s.anchor j → s.auxiliaryArm ≤ j) := by
  exact ⟨s.auxiliaryArm_mem_complement,
    s.auxiliaryArm_anchor_minimum, s.auxiliaryArm_label_minimum⟩

/-- Any arm with the full minimum-and-tie characterization is the selected
auxiliary arm. -/
theorem auxiliaryArm_characterization {j : Fin p.K}
    (hj : j ∈ fastArmFinset s.slowSet)
    (hmin : ∀ k, k ∈ fastArmFinset s.slowSet → s.anchor j ≤ s.anchor k)
    (htie : ∀ k, k ∈ fastArmFinset s.slowSet →
      s.anchor j = s.anchor k → j ≤ k) :
    j = s.auxiliaryArm := by
  have hwe : s.anchor j = s.anchor s.auxiliaryArm :=
    le_antisymm (hmin _ s.auxiliaryArm_mem_complement)
      (s.auxiliaryArm_anchor_minimum j hj)
  have hjle : j ≤ s.auxiliaryArm :=
    htie _ s.auxiliaryArm_mem_complement hwe
  have hele : s.auxiliaryArm ≤ j :=
    s.auxiliaryArm_label_minimum j hj hwe.symm
  exact Fin.ext (le_antisymm hjle hele)

/-- Existence and uniqueness of the complement minimizer, with the complete
source tie-breaking characterization. -/
theorem existsUnique_auxiliaryArm :
    ∃! j : Fin p.K,
      j ∈ fastArmFinset s.slowSet ∧
        (∀ k, k ∈ fastArmFinset s.slowSet → s.anchor j ≤ s.anchor k) ∧
        (∀ k, k ∈ fastArmFinset s.slowSet →
          s.anchor j = s.anchor k → j ≤ k) := by
  refine ⟨s.auxiliaryArm, s.auxiliaryArm_spec, ?_⟩
  intro j hj
  exact s.auxiliaryArm_characterization hj.1 hj.2.1 hj.2.2

/-- The canonical sorted follower arm map, with the selected auxiliary arm. -/
noncomputable def assignment : ActiveRoundActions.Assignment p.m p.K where
  assigned := CanonicalAssignmentVector.followerArm p.two_le_m s.slowSet
  injective := CanonicalAssignmentVector.followerArm_injective p.two_le_m s.slowSet
  auxiliary := s.auxiliaryArm
  auxiliary_outside := by
    intro i
    let e : CanonicalFastSampling.FastArm s.slowSet :=
      ⟨s.auxiliaryArm, s.auxiliaryArm_mem_complement⟩
    exact (CanonicalAssignmentVector.followerArm_ne_of_fastCandidate
      p.two_le_m s.slowSet e i).symm

/-- Assignment injectivity is inherited from the existing sorted-set
enumeration. -/
theorem assignment_injective : Function.Injective s.assignment.assigned :=
  CanonicalAssignmentVector.followerArm_injective p.two_le_m s.slowSet

/-- The existing follower-arm enumeration is strictly sorted. -/
theorem assignment_strictMono : StrictMono s.assignment.assigned :=
  CanonicalAssignmentVector.followerArm_strictMono p.two_le_m s.slowSet

/-- The assigned arms have image exactly the supplied supported slow set. -/
theorem assignment_image :
    Finset.univ.image s.assignment.assigned = s.slowSet.1 :=
  CanonicalAssignmentVector.followerArm_image p.two_le_m s.slowSet

/-- Every assigned follower arm differs from the auxiliary arm. -/
theorem assignment_auxiliary_outside (i : ActiveRoundActions.Follower p.m) :
    s.assignment.auxiliary ≠ s.assignment.assigned i :=
  s.assignment.auxiliary_outside i

/-- The canonical rate threshold is positive. -/
theorem rateThreshold_pos (i : Fin p.K) : 0 < s.rateThreshold i := by
  unfold rateThreshold
  exact (CanonicalRecordingRates.beta_pos p eta.property).trans_le
    (le_max_left _ _)

/-- The source cap and canonical threshold bound give a rate threshold at most
one, establishing nonnegativity of the dyadic exponent before casting. -/
theorem rateThreshold_le_one (i : Fin p.K) : s.rateThreshold i ≤ 1 := by
  have hbeta := CanonicalRecordingRates.beta_le_one_div_32mK p
    eta.property s.eta_le_source_cap
  have hf := CanonicalRecordingRates.f_le_one_div_32mK p s.anchor
    s.anchor_pos i
  have hm : (1 : ℝ) ≤ (p.m : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt (ConstructorDimensions.m_pos p))
  have hK : (1 : ℝ) ≤ (p.K : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt (ConstructorDimensions.K_pos p))
  have hden_pos : 0 < 32 * (p.m : ℝ) * (p.K : ℝ) := by positivity
  have hden : 1 ≤ 32 * (p.m : ℝ) * (p.K : ℝ) := by nlinarith
  have hrecip : 1 / (32 * (p.m : ℝ) * (p.K : ℝ)) ≤ 1 := by
    rw [div_le_iff₀ hden_pos]
    simpa only [one_mul] using hden
  unfold rateThreshold
  exact (max_le hbeta hf).trans hrecip

/-- The integer ceiling exponent, with its nonnegativity proved from the
literal max rate threshold. -/
noncomputable def integerExponent (i : Fin p.K) : {h : ℤ // 0 ≤ h} := by
  refine ⟨-Int.ceil (Real.logb 2 (s.rateThreshold i)), ?_⟩
  apply neg_nonneg.mpr
  apply Int.ceil_nonpos.mpr
  exact Real.logb_nonpos one_lt_two
    (le_of_lt (s.rateThreshold_pos i)) (s.rateThreshold_le_one i)

/-- The natural source exponent, obtained only after proving its integer value
is nonnegative. -/
noncomputable def exponent (i : Fin p.K) : ℕ :=
  (s.integerExponent i).val.toNat

theorem exponent_intCast (i : Fin p.K) :
    (s.exponent i : ℤ) = -Int.ceil (Real.logb 2 (s.rateThreshold i)) :=
  Int.toNat_of_nonneg (s.integerExponent i).property

/-- The signed exponent is nonnegative before it is converted to a natural. -/
theorem integerExponent_nonneg (i : Fin p.K) :
    0 ≤ (s.integerExponent i).val :=
  (s.integerExponent i).property

/-- Every derived exponent represents exactly the literal canonical source
recording rate at that arm. -/
theorem dyadicRate_eq_rate (i : Fin p.K) :
    OrdinaryMessageCodec.dyadicRate (s.exponent i) = s.rate i := by
  have hceilInt : Int.ceil (Real.logb 2 (s.rateThreshold i)) =
      -(s.exponent i : ℤ) := by
    have h := s.exponent_intCast i
    omega
  have hceilReal :
      (Int.ceil (Real.logb 2 (s.rateThreshold i)) : ℝ) =
        -(s.exponent i : ℝ) := by
    exact_mod_cast hceilInt
  unfold OrdinaryMessageCodec.dyadicRate rate CanonicalRecordingRates.xi
  change ((2 : ℝ) ^ s.exponent i)⁻¹ =
    (2 : ℝ) ^ (Int.ceil (Real.logb 2 (s.rateThreshold i)) : ℝ)
  rw [hceilReal, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]

/-- The exact integer-rate witness forces `η ≥ 1/D`. -/
theorem eta_ge_one_div_D (s : Input p eta) : 1 / (D p : ℝ) ≤ eta.val := by
  have hreal : 0 < (s.n : ℝ) := by
    rw [s.n_eq_eta_mul_D]
    exact mul_pos eta.property (Nat.cast_pos.mpr (ConstructorDimensions.D_pos p))
  have hnpos : 0 < s.n := by exact_mod_cast hreal
  have hn1 : 1 ≤ (s.n : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hnpos)
  have hD : 0 < (D p : ℝ) := Nat.cast_pos.mpr (ConstructorDimensions.D_pos p)
  rw [s.n_eq_eta_mul_D] at hn1
  exact (div_le_iff₀ hD).2 (by nlinarith [hn1])

/-- `β` dominates `η` because the source stability logarithm is at least one. -/
theorem eta_le_beta : eta.val ≤ CanonicalRecordingRates.beta p eta.val := by
  have hL : (1 : ℝ) ≤ (L_stab p : ℝ) := by
    exact_mod_cast CanonicalRecordingRates.L_stab_ge_one p
  unfold CanonicalRecordingRates.beta
  nlinarith [eta.property]

/-- The derived natural exponent is at most the source codec bound `b_N`.
This uses the positive integer identity, the actual canonical rate, and the
literal source cap; exponent validity is not an input. -/
theorem exponent_le_b_N (i : Fin p.K) : s.exponent i ≤ b_N p := by
  have hrate : 1 / (D p : ℝ) ≤
      OrdinaryMessageCodec.dyadicRate (s.exponent i) := by
    calc
      1 / (D p : ℝ) ≤ eta.val := s.eta_ge_one_div_D
      _ ≤ CanonicalRecordingRates.beta p eta.val := eta_le_beta
      _ ≤ CanonicalRecordingRates.xi p eta.val s.anchor i :=
        CanonicalRecordingRates.beta_le_xi p eta.property s.anchor i
      _ = OrdinaryMessageCodec.dyadicRate (s.exponent i) :=
        (s.dyadicRate_eq_rate i).symm
  have hDpos : 0 < (D p : ℝ) := Nat.cast_pos.mpr (ConstructorDimensions.D_pos p)
  have hpow_le_D : (2 : ℝ) ^ s.exponent i ≤ (D p : ℝ) := by
    apply le_of_one_div_le_one_div hDpos
    simpa only [div_eq_mul_inv, one_mul, OrdinaryMessageCodec.dyadicRate] using hrate
  have hpow_nat : 2 ^ s.exponent i ≤ D p := by exact_mod_cast hpow_le_D
  by_contra hnot
  have hlt : b_N p < s.exponent i := Nat.lt_of_not_ge hnot
  have hpow_lt : 2 ^ b_N p < 2 ^ s.exponent i :=
    Nat.pow_lt_pow_right (by decide : 1 < 2) hlt
  exact (not_lt_of_ge (by
    change 2 ^ s.exponent i ≤ 2 ^ b_N p at hpow_nat
    exact hpow_nat)) hpow_lt

/-- The literal source rate satisfies its upper admissibility bound at every
arm. -/
theorem rate_le_source_bound (i : Fin p.K) :
    s.rate i ≤ 1 / (16 * (p.m : ℝ) * (p.K : ℝ)) := by
  exact CanonicalRecordingRates.xi_le_one_div_16mK p eta.property
    s.eta_le_source_cap s.anchor s.anchor_pos i

/-- The actual admissible DOWN record for follower `i`. Its fields are the
one-based source start and arm labels, the derived rate exponent, and the
supplied current queue of the assigned arm. -/
noncomputable def downRecord (i : ActiveRoundActions.Follower p.m) :
    OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p eta) := by
  let a := s.assignment.assigned i
  let e := s.assignment.auxiliary
  let h := s.exponent a
  let q := s.queues a
  have hae : a ≠ e := (s.assignment_auxiliary_outside i).symm
  have hrate : OrdinaryMessageCodec.dyadicRate h = s.rate a :=
    s.dyadicRate_eq_rate a
  have hbeta : CanonicalRecordingRates.beta p eta.val ≤
      OrdinaryMessageCodec.dyadicRate h := by
    rw [hrate]
    exact s.beta_le_rate a
  have hrateUpper : OrdinaryMessageCodec.dyadicRate h ≤
      1 / (16 * (p.m : ℝ) * (p.K : ℝ)) := by
    rw [hrate]
    exact s.rate_le_source_bound a
  refine ⟨⟨s.sigma.val + 1, a.val + 1, e.val + 1, h, q⟩, ?_⟩
  change
    1 ≤ s.sigma.val + 1 ∧ s.sigma.val + 1 ≤ p.T ∧
    1 ≤ a.val + 1 ∧ a.val + 1 ≤ p.K ∧
    1 ≤ e.val + 1 ∧ e.val + 1 ≤ p.K ∧
    a.val + 1 ≠ e.val + 1 ∧ h ≤ b_N p ∧
    CanonicalRecordingRates.beta p eta.val ≤ OrdinaryMessageCodec.dyadicRate h ∧
    OrdinaryMessageCodec.dyadicRate h ≤
      1 / ((16 : ℝ) * (p.m : ℝ) * (p.K : ℝ)) ∧
    q ≤ p.T * D p
  refine ⟨by omega, ?_, by omega, ?_, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Nat.succ_le_of_lt s.sigma.isLt
  · exact Nat.succ_le_of_lt a.isLt
  · exact Nat.succ_le_of_lt e.isLt
  · intro hab
    apply hae
    apply Fin.ext
    omega
  · exact s.exponent_le_b_N a
  · exact hbeta
  · simpa [ReferencePrelaunchFollower.codecParams] using hrateUpper
  · exact s.queues_le_TD a

/-- The record fields are exactly `(σ+1, aᵢ+1, e+1, h(aᵢ), Bσ(aᵢ))`. -/
theorem downRecord_fields (i : ActiveRoundActions.Follower p.m) :
    (s.downRecord i).val =
      ⟨s.sigma.val + 1, (s.assignment.assigned i).val + 1,
        s.assignment.auxiliary.val + 1,
        s.exponent (s.assignment.assigned i),
        s.queues (s.assignment.assigned i)⟩ := rfl

/-- The record's exponent represents exactly the assigned arm's source rate. -/
theorem downRecord_rate (i : ActiveRoundActions.Follower p.m) :
    OrdinaryMessageCodec.dyadicRate (s.downRecord i).val.h =
      CanonicalRecordingRates.xi p eta.val s.anchor
        (s.assignment.assigned i) := by
  rw [s.downRecord_fields]
  exact s.dyadicRate_eq_rate _

/-- The payload preserves the actual supplied initial queue at its assigned
arm. -/
theorem downRecord_initialQueue (i : ActiveRoundActions.Follower p.m) :
    (s.downRecord i).val.q = s.queues (s.assignment.assigned i) := by
  rw [s.downRecord_fields]

/-- Encode each constructed record with the existing five-field codec. -/
noncomputable def downWord (i : ActiveRoundActions.Follower p.m) :
    OrdinaryMessageCodec.Word (ReferencePrelaunchFollower.codecParams p eta) :=
  OrdinaryMessageCodec.encodeDown (ReferencePrelaunchFollower.codecParams p eta)
    (s.downRecord i)

/-- The existing DOWN parser returns every encoded admissible record. -/
theorem parseDown_downWord (i : ActiveRoundActions.Follower p.m) :
    OrdinaryMessageCodec.parseDown (ReferencePrelaunchFollower.codecParams p eta)
      (some (s.downWord i)) = some (s.downRecord i) :=
  OrdinaryMessageCodec.parseDown_encode _ _

/-- Reuse the first-launch construction as a specialization: its actual
sampled slow set, unit anchor, zero queues, start, and rate witnesses become
the local data for this general deterministic packaging operation. -/
noncomputable def ofFirstAssignment (s : FirstAssignmentLaunch.Input p eta) : Input p eta where
  eta_le_source_cap := s.eta_le_source_cap
  n := s.n
  n_eq_eta_mul_D := s.n_eq_eta_mul_D
  sigma := s.sigma
  slowSet := s.slowSet
  anchor := FirstAssignmentLaunch.Input.anchor p
  anchor_pos := by
    intro i
    norm_num [FirstAssignmentLaunch.Input.anchor]
  queues := FirstAssignmentLaunch.Input.initialQueues p
  queues_le_TD := by
    intro i
    simp [FirstAssignmentLaunch.Input.initialQueues]

theorem slowSet_eq_first_start (s : FirstAssignmentLaunch.Input p eta) :
    (ofFirstAssignment s).slowSet = s.start.slowSet := rfl

theorem anchor_eq_first_start (s : FirstAssignmentLaunch.Input p eta) :
    (ofFirstAssignment s).anchor = s.start.anchor := rfl

theorem queues_eq_first_start (s : FirstAssignmentLaunch.Input p eta) :
    (ofFirstAssignment s).queues = s.start.queues := rfl

theorem rate_eq_first_start (s : FirstAssignmentLaunch.Input p eta)
    (i : Fin p.K) :
    (ofFirstAssignment s).rate i = s.start.recordingRates i := rfl

theorem auxiliaryArm_eq_first (s : FirstAssignmentLaunch.Input p eta) :
    (ofFirstAssignment s).auxiliaryArm =
      FirstAssignmentLaunch.Input.auxiliaryArm s := by
  have h := (ofFirstAssignment s).auxiliaryArm_characterization
    (j := FirstAssignmentLaunch.Input.auxiliaryArm s)
    (FirstAssignmentLaunch.Input.auxiliaryArm_mem_complement s)
    (by
      intro j hj
      simp [ofFirstAssignment, FirstAssignmentLaunch.Input.anchor])
    (by
      intro j hj hweight
      exact FirstAssignmentLaunch.Input.auxiliaryArm_minimum s j hj)
  exact h.symm

theorem assignment_assigned_eq_first (s : FirstAssignmentLaunch.Input p eta)
    (i : ActiveRoundActions.Follower p.m) :
    (ofFirstAssignment s).assignment.assigned i =
      (FirstAssignmentLaunch.Input.assignment s).assigned i := rfl

theorem assignment_auxiliary_eq_first (s : FirstAssignmentLaunch.Input p eta) :
    (ofFirstAssignment s).assignment.auxiliary =
      (FirstAssignmentLaunch.Input.assignment s).auxiliary :=
  auxiliaryArm_eq_first s

/-- The complete assigned-arm functions of the general operation and actual
first launch agree. -/
theorem assignment_map_eq_first (s : FirstAssignmentLaunch.Input p eta) :
    (ofFirstAssignment s).assignment.assigned =
      (FirstAssignmentLaunch.Input.assignment s).assigned := by
  funext i
  exact assignment_assigned_eq_first s i

theorem assignment_map_eq_first_start (s : FirstAssignmentLaunch.Input p eta) :
    (ofFirstAssignment s).assignment.assigned = s.start.assignment.assigned := by
  rw [assignment_map_eq_first]
  rfl

theorem assignment_auxiliary_eq_first_start (s : FirstAssignmentLaunch.Input p eta) :
    (ofFirstAssignment s).assignment.auxiliary = s.start.assignment.auxiliary := by
  rw [assignment_auxiliary_eq_first]
  rfl

theorem exponent_eq_first (s : FirstAssignmentLaunch.Input p eta)
    (i : ActiveRoundActions.Follower p.m) :
    (ofFirstAssignment s).exponent
        ((FirstAssignmentLaunch.Input.assignment s).assigned i) = s.exponent i := by
  rfl

/-- On the first launch's actual sampled set, unit anchor, and zero queues,
the general operation constructs exactly the already existing DOWN record. -/
theorem downRecord_eq_first (s : FirstAssignmentLaunch.Input p eta)
    (i : ActiveRoundActions.Follower p.m) :
    (ofFirstAssignment s).downRecord i = s.downRecord i := by
  apply Subtype.ext
  rw [(ofFirstAssignment s).downRecord_fields i,
    FirstAssignmentLaunch.Input.downRecord_fields s i]
  rw [assignment_assigned_eq_first, assignment_auxiliary_eq_first,
    exponent_eq_first]
  rfl

/-- The general encoded payload also equals the first launch's actual encoded
word, not merely a word satisfying the same format predicate. -/
theorem downWord_eq_first (s : FirstAssignmentLaunch.Input p eta)
    (i : ActiveRoundActions.Follower p.m) :
    (ofFirstAssignment s).downWord i = s.downWord i := by
  unfold downWord FirstAssignmentLaunch.Input.downWord
  rw [downRecord_eq_first]

/-- The specialized record is the actual `Start.outgoing` value. -/
theorem downRecord_eq_first_start (s : FirstAssignmentLaunch.Input p eta)
    (i : ActiveRoundActions.Follower p.m) :
    (ofFirstAssignment s).downRecord i = s.start.outgoing i := by
  rw [downRecord_eq_first]
  rfl

/-- The specialized word is the actual `Start.outgoingWords` value. -/
theorem downWord_eq_first_start (s : FirstAssignmentLaunch.Input p eta)
    (i : ActiveRoundActions.Follower p.m) :
    (ofFirstAssignment s).downWord i = s.start.outgoingWords i := by
  rw [downWord_eq_first, s.start_outgoingWord]
  rfl

end Input

end Bandits.Support.AssignmentStartPayload

end
