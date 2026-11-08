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
public import Bandits.Support.ReferencePrelaunchFollower
public import Mathlib.Data.Finset.Max

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Positivity

/-!
# The literal first assignment and its outgoing DOWN records

The first assignment uses the complete `K + 1` control vector, the canonical
slow sampler, the sorted follower arms, and the minimum-label complement arm.
Its outgoing records use the existing ordinary codec and the frozen unit
weights, anchor, and recording rates.

Sources: `sources/zip4/manuscript/05_binary_transport.tex:62-70`,
`sources/zip4/manuscript/06_interruptions.tex:46-61,179-189`, and
`sources/zip4/manuscript/04_slow_fast_learner.tex:96-125`.

These are fully proved internal constructions and calculations. They do not
claim that this launch occurs in a physical run or close a manuscript lemma.
-/

@[expose] public section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.CanonicalOrientedSetLaw
open Bandits.Support.ContinuousControlSlice
open Bandits.Support.ActiveRoundActions
open Bandits.Support.OrdinaryMessageCodec
open Bandits.Support.ReferencePrelaunchFollower

namespace Bandits.Support.FirstAssignmentLaunch

open Bandits.Support.CanonicalAssignmentVector
open Bandits.Support.CanonicalFastSampling
open Bandits.Support.CanonicalRecordingRates

local instance firstAssignmentSlowSetMeasurableSpace (K m : ℕ) :
    MeasurableSpace (CanonicalOrientedSetLaw.SlowSet K m) := ⊤

/-- The concrete outputs of a first assignment start. Every field is filled
by `Input.start`; no slow set, auxiliary arm, exponent, codec-validity proof,
or sampling law is supplied by a caller. -/
structure Start (p : Parameters) (eta : LearningRate) where
  sigma : Fin p.T
  coordinates : Fin (p.K + 1) → Scalar
  slowSet : CanonicalOrientedSetLaw.SlowSet p.K p.m
  auxiliaryArm : Fin p.K
  assignment : ActiveRoundActions.Assignment p.m p.K
  snapshot : ActiveRoundActions.Snapshot assignment
  baseScores : Fin p.K → ℕ
  queues : Fin p.K → ℕ
  weights : Fin p.K → ℝ
  anchor : Fin p.K → ℝ
  recordingRates : Fin p.K → ℝ
  outgoing : ActiveRoundActions.Follower p.m →
    OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p eta)
  outgoingWords : ActiveRoundActions.Follower p.m →
    OrdinaryMessageCodec.Word (ReferencePrelaunchFollower.codecParams p eta)

/-- Source inputs for one first assignment launch. The vector is the actual
complete `K + 1`-coordinate vector. The only rate assumptions are the literal
source cap and the exact integer identity `n = ηD`.

Sources: `sources/zip4/manuscript/05_binary_transport.tex:62-68`,
`sources/zip4/manuscript/06_interruptions.tex:46-61`, and
`sources/zip4/manuscript/04_slow_fast_learner.tex:96-113`. -/
structure Input (p : Parameters) (eta : LearningRate) where
  eta_le_source_cap : eta.val ≤
    1 / (1024 * (p.m : ℝ) * (p.K : ℝ) * (L_stab p : ℝ))
  n : ℕ
  n_eq_eta_mul_D : (n : ℝ) = eta.val * (D p : ℝ)
  sigma : Fin p.T
  coordinates : Fin (p.K + 1) → Scalar

namespace Input

variable {p : Parameters} {eta : LearningRate} (s : Input p eta)

/-- Replace the entire assignment-coordinate vector while keeping the actual
launch round and its source rate witnesses fixed. -/
def withCoordinates (v : Fin (p.K + 1) → Scalar) : Input p eta :=
  { s with coordinates := v }

/-- The existing canonical sampler applied once to the entire assignment
vector, with both current and anchor weights equal to one. -/
noncomputable def slowSet : SlowSet p.K p.m :=
  CanonicalAssignmentVector.canonicalSlowSampler p.two_le_m p.m_lt_K
    (fun _ => 1) (fun _ => 1) (by intro i; norm_num) (by intro i; norm_num)
    s.coordinates

/-- The complement of the sampled slow set has the canonical cardinal bound. -/
theorem fastComplement_card_ge_two :
    2 ≤ (CanonicalFastSampling.fastArmFinset s.slowSet).card :=
  CanonicalFastSampling.fastArmFinset_card_ge_two s.slowSet

/-- Nonemptiness of the actual complement follows from its cardinal bound. -/
theorem fastComplement_nonempty :
    (CanonicalFastSampling.fastArmFinset s.slowSet).Nonempty := by
  apply Finset.card_pos.mp
  have h := s.fastComplement_card_ge_two
  omega

/-- The auxiliary arm is the smallest label in the actual slow-set
complement. This is the frozen-weight argmin rule because the anchor weights
used at this launch are all one. -/
noncomputable def auxiliaryArm : Fin p.K :=
  (CanonicalFastSampling.fastArmFinset s.slowSet).min' s.fastComplement_nonempty

/-- The selected auxiliary arm lies in the actual complement. -/
theorem auxiliaryArm_mem_complement :
    s.auxiliaryArm ∈ CanonicalFastSampling.fastArmFinset s.slowSet :=
  Finset.min'_mem _ _

/-- Every complement arm has label at least the selected auxiliary label. -/
theorem auxiliaryArm_minimum (j : Fin p.K)
    (hj : j ∈ CanonicalFastSampling.fastArmFinset s.slowSet) :
    s.auxiliaryArm ≤ j := by
  exact Finset.min'_le _ _ hj

/-- The assigned arm at follower rank `i`, using the existing increasing
order isomorphism of the sampled slow set. -/
noncomputable def followerArm (i : Fin (p.m - 1)) : Fin p.K :=
  CanonicalAssignmentVector.followerArm p.two_le_m s.slowSet i

/-- The actual injective slow assignment and minimum-label auxiliary arm. -/
noncomputable def assignment : ActiveRoundActions.Assignment p.m p.K where
  assigned := s.followerArm
  injective := CanonicalAssignmentVector.followerArm_injective p.two_le_m s.slowSet
  auxiliary := s.auxiliaryArm
  auxiliary_outside := by
    intro i
    let j : CanonicalFastSampling.FastArm s.slowSet :=
      ⟨s.auxiliaryArm, s.auxiliaryArm_mem_complement⟩
    exact (CanonicalAssignmentVector.followerArm_ne_of_fastCandidate
      p.two_le_m s.slowSet j i).symm

/-- Sortedness of the actual follower assignment. -/
theorem assignment_strictMono : StrictMono (fun i : Fin (p.m - 1) =>
    s.assignment.assigned i) := by
  exact CanonicalAssignmentVector.followerArm_strictMono p.two_le_m s.slowSet

/-- The follower-arm image is exactly the sampled slow set. -/
theorem assignment_image :
    Finset.univ.image s.assignment.assigned = s.slowSet.1 := by
  exact CanonicalAssignmentVector.followerArm_image p.two_le_m s.slowSet

/-- The actual initial physical snapshot for this assignment. -/
noncomputable def initialSnapshot : ActiveRoundActions.Snapshot s.assignment :=
  ActiveRoundActions.initialSnapshot s.assignment

/-- First-assignment base scores are all zero. -/
def baseScores (p : Parameters) : Fin p.K → ℕ := fun _ => 0

/-- First-assignment queues are all zero. -/
def initialQueues (p : Parameters) : Fin p.K → ℕ := fun _ => 0

/-- Both the current weights and frozen anchor are the source's unit vector. -/
def weights (p : Parameters) : Fin p.K → ℝ := fun _ => 1

/-- Frozen start anchor, equal to one at every arm. -/
def anchor (p : Parameters) : Fin p.K → ℝ := fun _ => 1

/-- The source's dyadic-rounding argument for follower `i`, evaluated at that
follower's actual sorted arm and the actual unit-anchor rates. -/
noncomputable def recordingThreshold (i : Fin (p.m - 1)) : ℝ :=
  max (CanonicalRecordingRates.beta p eta.val)
    (CanonicalRecordingRates.f p (anchor p) (s.followerArm i))

theorem recordingThreshold_pos (i : Fin (p.m - 1)) :
    0 < s.recordingThreshold i := by
  unfold recordingThreshold
  exact (CanonicalRecordingRates.beta_pos p eta.property).trans_le
    (le_max_left _ _)

theorem recordingThreshold_le_one (i : Fin (p.m - 1)) :
    s.recordingThreshold i ≤ 1 := by
  have hbeta := CanonicalRecordingRates.beta_le_one_div_32mK p
    eta.property s.eta_le_source_cap
  have hf := CanonicalRecordingRates.f_le_one_div_32mK p (anchor p)
    (by intro j; norm_num [anchor]) (s.followerArm i)
  have hm : (1 : ℝ) ≤ (p.m : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt (m_pos p))
  have hK : (1 : ℝ) ≤ (p.K : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt (K_pos p))
  have hden_pos : 0 < 32 * (p.m : ℝ) * (p.K : ℝ) := by
    exact mul_pos (mul_pos (by norm_num) (Nat.cast_pos.mpr (m_pos p)))
      (Nat.cast_pos.mpr (K_pos p))
  have hden : 1 ≤ 32 * (p.m : ℝ) * (p.K : ℝ) := by nlinarith
  have hrecip : 1 / (32 * (p.m : ℝ) * (p.K : ℝ)) ≤ 1 := by
    rw [div_le_iff₀ hden_pos]
    simpa only [one_mul] using hden
  unfold recordingThreshold
  exact (max_le hbeta hf).trans hrecip

/-- The integer exponent before conversion to a natural number. Its subtype
proof establishes nonnegativity from the literal rate cap and dyadic envelope.
-/
noncomputable def integerExponent (i : Fin (p.m - 1)) :
    {h : ℤ // 0 ≤ h} := by
  refine ⟨-Int.ceil (Real.logb 2 (s.recordingThreshold i)), ?_⟩
  apply neg_nonneg.mpr
  apply Int.ceil_nonpos.mpr
  exact Real.logb_nonpos one_lt_two
    (le_of_lt (s.recordingThreshold_pos i)) (s.recordingThreshold_le_one i)

/-- The integer source exponent is nonnegative before its conversion to `ℕ`. -/
theorem integerExponent_nonneg (i : Fin (p.m - 1)) :
    0 ≤ (s.integerExponent i).val :=
  (s.integerExponent i).property

/-- The natural recording exponent, obtained only after proving its integer
value nonnegative. -/
noncomputable def exponent (i : Fin (p.m - 1)) : ℕ :=
  (s.integerExponent i).val.toNat

/-- Casting the derived natural exponent back to integers recovers the
negative integer ceiling of the source logarithm. -/
theorem exponent_intCast (i : Fin (p.m - 1)) :
    (s.exponent i : ℤ) = -Int.ceil (Real.logb 2 (s.recordingThreshold i)) := by
  exact Int.toNat_of_nonneg (s.integerExponent i).property

/-- The canonical recording rate is exactly the codec's reciprocal dyadic
rate at the derived exponent. -/
theorem dyadicRate_eq_canonicalRate (i : Fin (p.m - 1)) :
    OrdinaryMessageCodec.dyadicRate (s.exponent i) =
      CanonicalRecordingRates.xi p eta.val (anchor p) (s.followerArm i) := by
  have hceilInt : Int.ceil (Real.logb 2 (s.recordingThreshold i)) =
      -(s.exponent i : ℤ) := by
    have h := s.exponent_intCast i
    omega
  have hceilReal :
      (Int.ceil (Real.logb 2 (s.recordingThreshold i)) : ℝ) =
        -(s.exponent i : ℝ) := by
    exact_mod_cast hceilInt
  unfold OrdinaryMessageCodec.dyadicRate CanonicalRecordingRates.xi anchor
  change ((2 : ℝ) ^ s.exponent i)⁻¹ =
    (2 : ℝ) ^ (Int.ceil (Real.logb 2 (s.recordingThreshold i)) : ℝ)
  rw [hceilReal, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]

/-- The exact integer-rate witness is positive. -/
theorem rateInteger_pos : 0 < s.n := by
  have hn : 0 < (s.n : ℝ) := by
    rw [s.n_eq_eta_mul_D]
    exact mul_pos eta.property (Nat.cast_pos.mpr (D_pos p))
  exact_mod_cast hn

/-- The rate is at least the literal source threshold `β`. -/
theorem beta_le_canonicalRate (i : Fin p.K) :
    CanonicalRecordingRates.beta p eta.val ≤
      CanonicalRecordingRates.xi p eta.val (anchor p) i := by
  exact CanonicalRecordingRates.beta_le_xi p eta.property (anchor p) i

/-- The learning rate is at least `1/D`, derived from the supplied positive
integer identity `n = ηD`. -/
theorem eta_ge_one_div_D (n : ℕ)
    (hn : (n : ℝ) = eta.val * (D p : ℝ)) :
    1 / (D p : ℝ) ≤ eta.val := by
  have hreal : 0 < (n : ℝ) := by
    rw [hn]
    exact mul_pos eta.property (Nat.cast_pos.mpr (D_pos p))
  have hnpos : 0 < n := by exact_mod_cast hreal
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hnpos)
  rw [hn] at hn1
  have hD : 0 < (D p : ℝ) := Nat.cast_pos.mpr (D_pos p)
  exact (div_le_iff₀ hD).2 (by nlinarith [hn1])

/-- `β` dominates the learning rate because `L_stab ≥ 1`. -/
theorem eta_le_beta : eta.val ≤ CanonicalRecordingRates.beta p eta.val := by
  have hL : (1 : ℝ) ≤ (L_stab p : ℝ) := by
    exact_mod_cast CanonicalRecordingRates.L_stab_ge_one p
  unfold CanonicalRecordingRates.beta
  nlinarith [eta.property]

/-- The natural exponent is at most the source codec bound `b_N`. This uses
the actual dyadic rate, `η ≥ 1/D`, and `β ≥ η`; no exponent-validity premise is
supplied. -/
theorem exponent_le_b_N (i : Fin (p.m - 1)) :
    s.exponent i ≤ b_N p := by
  have hrate : 1 / (D p : ℝ) ≤
      OrdinaryMessageCodec.dyadicRate (s.exponent i) := by
    calc
      1 / (D p : ℝ) ≤ eta.val := eta_ge_one_div_D s.n s.n_eq_eta_mul_D
      _ ≤ CanonicalRecordingRates.beta p eta.val := eta_le_beta
      _ ≤ CanonicalRecordingRates.xi p eta.val (anchor p) (s.followerArm i) :=
        beta_le_canonicalRate (p := p) (eta := eta) _
      _ = OrdinaryMessageCodec.dyadicRate (s.exponent i) :=
        (s.dyadicRate_eq_canonicalRate i).symm
  have hDpos : 0 < (D p : ℝ) := Nat.cast_pos.mpr (D_pos p)
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

/-- The existing canonical unit-anchor rate obeys the source upper bound. -/
theorem canonicalRate_le_source_bound
    (heta_le : eta.val ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) * (L_stab p : ℝ)))
    (i : Fin p.K) :
    CanonicalRecordingRates.xi p eta.val (anchor p) i ≤
      1 / (16 * (p.m : ℝ) * (p.K : ℝ)) := by
  exact CanonicalRecordingRates.xi_le_one_div_16mK p eta.property
    heta_le (anchor p) (by intro j; norm_num [anchor]) i

/-- The concrete first DOWN record for follower `i`, with one-based source
labels and zero initial queue. Its admissibility proof is derived entirely
from the supplied source cap, exact integer rate, and actual canonical rates.
-/
noncomputable def downRecord (i : Fin (p.m - 1)) :
    DownRecord (ReferencePrelaunchFollower.codecParams p eta) := by
  let a := s.followerArm i
  let e := s.auxiliaryArm
  let h := s.exponent i
  have he_mem := s.auxiliaryArm_mem_complement
  let ec : CanonicalFastSampling.FastArm s.slowSet := ⟨e, he_mem⟩
  have hae : a ≠ e :=
    CanonicalAssignmentVector.followerArm_ne_of_fastCandidate
      p.two_le_m s.slowSet ec i
  have hh : h ≤ b_N p := s.exponent_le_b_N i
  have hrate : OrdinaryMessageCodec.dyadicRate h =
      CanonicalRecordingRates.xi p eta.val (anchor p) a := by
    exact s.dyadicRate_eq_canonicalRate i
  have hbeta : CanonicalRecordingRates.beta p eta.val ≤
      OrdinaryMessageCodec.dyadicRate h := by
    rw [hrate]
    exact beta_le_canonicalRate (p := p) (eta := eta) a
  have hrateUpper : OrdinaryMessageCodec.dyadicRate h ≤
      1 / (16 * (p.m : ℝ) * (p.K : ℝ)) := by
    rw [hrate]
    exact canonicalRate_le_source_bound s.eta_le_source_cap a
  refine ⟨⟨s.sigma.val + 1, a.val + 1, e.val + 1, h, 0⟩, ?_⟩
  change
    1 ≤ s.sigma.val + 1 ∧ s.sigma.val + 1 ≤ p.T ∧
    1 ≤ a.val + 1 ∧ a.val + 1 ≤ p.K ∧
    1 ≤ e.val + 1 ∧ e.val + 1 ≤ p.K ∧
    a.val + 1 ≠ e.val + 1 ∧ h ≤ b_N p ∧
    CanonicalRecordingRates.beta p eta.val ≤ OrdinaryMessageCodec.dyadicRate h ∧
    OrdinaryMessageCodec.dyadicRate h ≤
      1 / ((16 : ℝ) * (p.m : ℝ) * (p.K : ℝ)) ∧
    0 ≤ p.T * D p
  refine ⟨by omega, ?_, by omega, ?_, by omega, ?_, ?_, ?_, ?_, ?_, by omega⟩
  · exact Nat.succ_le_of_lt s.sigma.isLt
  · exact Nat.succ_le_of_lt a.isLt
  · exact Nat.succ_le_of_lt e.isLt
  · intro hab
    apply hae
    apply Fin.ext
    omega
  · exact hh
  · exact hbeta
  · simpa [ReferencePrelaunchFollower.codecParams] using hrateUpper

/-- The encoded outgoing DOWN word in the existing ordinary message codec. -/
noncomputable def downWord (i : Fin (p.m - 1)) :
    Word (ReferencePrelaunchFollower.codecParams p eta) :=
  OrdinaryMessageCodec.encodeDown (ReferencePrelaunchFollower.codecParams p eta)
    (s.downRecord i)

/-- The existing parser accepts and returns each constructed outgoing record. -/
theorem parseDown_downWord (i : Fin (p.m - 1)) :
    OrdinaryMessageCodec.parseDown (ReferencePrelaunchFollower.codecParams p eta)
      (some (s.downWord i)) = some (s.downRecord i) := by
  exact OrdinaryMessageCodec.parseDown_encode _ _

/-- The literal payload fields are `(σ+1, aᵢ+1, e+1, hᵢ, 0)`. -/
theorem downRecord_fields (i : Fin (p.m - 1)) :
    (s.downRecord i).val =
      ⟨s.sigma.val + 1, (s.followerArm i).val + 1,
        s.auxiliaryArm.val + 1, s.exponent i, 0⟩ := rfl

/-- The first assignment start with its actual assignment, initial snapshot,
zero score/queue state, unit weights and anchor, canonical recording rates,
and all concrete outgoing DOWN records. -/
noncomputable def start :
    FirstAssignmentLaunch.Start p eta where
  sigma := s.sigma
  coordinates := s.coordinates
  slowSet := s.slowSet
  auxiliaryArm := s.auxiliaryArm
  assignment := s.assignment
  snapshot := s.initialSnapshot
  baseScores := baseScores p
  queues := initialQueues p
  weights := weights p
  anchor := anchor p
  recordingRates := fun i => CanonicalRecordingRates.xi p eta.val (anchor p) i
  outgoing := s.downRecord
  outgoingWords := s.downWord

/-- The actual complete-vector pushforward to the canonical slow-set law.
This specializes `assignmentLaw_map_canonicalSlowSampler` to the same entire
`K + 1`-coordinate vector used by the start and payload constructor. -/
theorem slowSet_pushforward :
    (ContinuousControlSlice.assignmentLaw p.K).map
      (fun v => (s.withCoordinates v).slowSet) =
        (CanonicalOrientedSetLaw.slowSetPMF (fun _ => 1) (fun _ => 1)
          p.two_le_m p.m_lt_K (by intro _i; norm_num) (by intro _i; norm_num)).toMeasure := by
  simpa only [withCoordinates, slowSet] using
    CanonicalAssignmentVector.assignmentLaw_map_canonicalSlowSampler
      p.two_le_m p.m_lt_K (fun _ => 1) (fun _ => 1)
      (by intro i; norm_num) (by intro i; norm_num)

/-- The sampled assignment has an injective follower map. -/
theorem assignment_injective : Function.Injective s.assignment.assigned :=
  s.assignment.injective

/-- The chosen auxiliary arm is outside the image of the slow assignment. -/
theorem assignment_auxiliary_outside (i : ActiveRoundActions.Follower p.m) :
    s.assignment.auxiliary ≠ s.assignment.assigned i :=
  s.assignment.auxiliary_outside i

/-- The actual start's slow-set marginal is the full-vector pushforward law.
The measure is on the complete `K + 1`-coordinate assignment vector. -/
theorem start_slowSet_pushforward :
    (ContinuousControlSlice.assignmentLaw p.K).map
      (fun v => (s.withCoordinates v).start.slowSet) =
        (CanonicalOrientedSetLaw.slowSetPMF (fun _ => 1) (fun _ => 1)
          p.two_le_m p.m_lt_K (by intro _i; norm_num) (by intro _i; norm_num)).toMeasure := by
  simpa only [start, withCoordinates] using s.slowSet_pushforward

/-- The actual start retains the complete vector used by the canonical sampler. -/
theorem start_coordinates : s.start.coordinates = s.coordinates := rfl

/-- The actual assignment is strictly sorted by arm label. -/
theorem start_assignment_strictMono :
    StrictMono (fun i : Fin (p.m - 1) => s.start.assignment.assigned i) := by
  exact s.assignment_strictMono

/-- The actual assignment image is exactly its sampled slow set. -/
theorem start_assignment_image :
    Finset.univ.image s.start.assignment.assigned = s.start.slowSet.1 := by
  exact s.assignment_image

/-- The actual assignment map is injective. -/
theorem start_assignment_injective :
    Function.Injective s.start.assignment.assigned :=
  s.assignment_injective

/-- The start's auxiliary arm lies in the sampled slow-set complement. -/
theorem start_auxiliary_mem_complement :
    s.start.auxiliaryArm ∈ CanonicalFastSampling.fastArmFinset s.start.slowSet :=
  s.auxiliaryArm_mem_complement

/-- The start's actual snapshot is the existing empty initial snapshot. -/
theorem start_snapshot_initial :
    s.start.snapshot = ActiveRoundActions.initialSnapshot s.start.assignment := rfl

/-- Every base score in the actual first start is zero. -/
theorem start_baseScores_zero (i : Fin p.K) : s.start.baseScores i = 0 := rfl

/-- Every queue in the actual first start is zero. -/
theorem start_queues_zero (i : Fin p.K) : s.start.queues i = 0 := rfl

/-- Every current weight in the actual first start is one. -/
theorem start_weights_one (i : Fin p.K) : s.start.weights i = 1 := rfl

/-- Every frozen anchor weight in the actual first start is one. -/
theorem start_anchor_one (i : Fin p.K) : s.start.anchor i = 1 := rfl

/-- The actual start's rates are the existing canonical rates at its unit
anchor. -/
theorem start_recordingRates (i : Fin p.K) :
    s.start.recordingRates i = CanonicalRecordingRates.xi p eta.val
      (fun _ => 1) i := rfl

/-- The first start's canonical rates retain both source recording-rate
bounds. -/
theorem start_recordingRates_bounds (i : Fin p.K) :
    CanonicalRecordingRates.beta p eta.val ≤ s.start.recordingRates i ∧
      s.start.recordingRates i ≤ 1 / (16 * (p.m : ℝ) * (p.K : ℝ)) := by
  constructor
  · rw [s.start_recordingRates]
    exact beta_le_canonicalRate (p := p) (eta := eta) i
  · rw [s.start_recordingRates]
    exact canonicalRate_le_source_bound s.eta_le_source_cap i

/-- The actual outgoing word is the existing codec encoding of its record. -/
theorem start_outgoingWord (i : ActiveRoundActions.Follower p.m) :
    s.start.outgoingWords i = OrdinaryMessageCodec.encodeDown
      (ReferencePrelaunchFollower.codecParams p eta) (s.start.outgoing i) := rfl

/-- The existing parser returns the actual outgoing DOWN record. -/
theorem start_parseDown_outgoing (i : ActiveRoundActions.Follower p.m) :
    OrdinaryMessageCodec.parseDown (ReferencePrelaunchFollower.codecParams p eta)
      (some (s.start.outgoingWords i)) = some (s.start.outgoing i) := by
  exact s.parseDown_downWord i

/-- The actual outgoing fields are `(σ+1, aᵢ+1, e+1, hᵢ, 0)`. -/
theorem start_outgoing_fields (i : ActiveRoundActions.Follower p.m) :
    (s.start.outgoing i).val =
      ⟨s.sigma.val + 1, (s.followerArm i).val + 1,
        s.auxiliaryArm.val + 1, s.exponent i, 0⟩ := by
  exact s.downRecord_fields i

/-- The first outgoing DOWN record carries the actual recording rate for its
assigned arm, encoded by its exponent. -/
theorem start_outgoing_rate (i : ActiveRoundActions.Follower p.m) :
    OrdinaryMessageCodec.dyadicRate (s.start.outgoing i).val.h =
      s.start.recordingRates (s.start.assignment.assigned i) := by
  rw [s.start_outgoing_fields, s.start_recordingRates]
  exact s.dyadicRate_eq_canonicalRate i

/-- Every first outgoing DOWN queue field is zero. -/
theorem start_outgoing_queue_zero (i : ActiveRoundActions.Follower p.m) :
    (s.start.outgoing i).val.q = 0 := by
  rw [s.start_outgoing_fields]

end Input

end Bandits.Support.FirstAssignmentLaunch

end
