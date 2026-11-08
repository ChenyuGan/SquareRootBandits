/-
Copyright (c) 2026 Bandits Lean regret formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceOriginalStoppedTransportFixedIDMean
public import Bandits.Support.ReferenceOriginalCalendarFixedIDLearningMean
public import Bandits.Support.TunedNumericalRemainder

import Mathlib.Tactic

/-!
# Uniform domination of the accepted learning and transport budgets

This module bounds the literal accepted source coefficients and combines them
with the already selected dyadic source rate. It proves only a scalar numerical
estimate; it makes no startup, source-law, or regret claim.
-/

@[expose] public section

open Bandits.Support.ConstructorDimensions

namespace Bandits.Support.ReferenceLearningTransportRateDomination

private theorem exp_gap_pos : 0 < 1 - Real.exp (-1) := by
  apply sub_pos.mpr
  exact Real.exp_lt_one_iff.mpr (by norm_num)

/-- The accepted ordinary message quota is at most thirteen source bits. -/
theorem quota_le_thirteen_mul_b_N (p : Parameters) :
    AffineBatchDecoder.quota p ≤ 13 * b_N p := by
  have hfactor : 1 ≤ 2 * p.K * p.m :=
    Nat.succ_le_of_lt (Nat.mul_pos (Nat.mul_pos (by decide) (ConstructorDimensions.K_pos p))
      (ConstructorDimensions.m_pos p))
  have hTplusLeN : p.T + 1 ≤ N p := by
    calc
      p.T + 1 = 1 * (p.T + 1) := by simp
      _ ≤ (2 * p.K * p.m) * (p.T + 1) :=
        Nat.mul_le_mul_right (p.T + 1) hfactor
      _ = N p := by rfl
  have hTltN : p.T < N p := by omega
  have hTltD : p.T < D p :=
    hTltN.trans_le (ConstructorDimensions.N_lt_D p).le
  have hDpos := ConstructorDimensions.D_pos p
  have hDone : 1 ≤ D p := Nat.succ_le_of_lt hDpos
  have hTplus : p.T + 1 ≤ D p := Nat.succ_le_of_lt hTltD
  have hfieldArg : p.T * D p + 1 ≤ (D p) ^ 2 := by
    calc
      p.T * D p + 1 ≤ p.T * D p + D p := Nat.add_le_add_left hDone _
      _ = (p.T + 1) * D p := by ring
      _ ≤ D p * D p := Nat.mul_le_mul_right (D p) hTplus
      _ = (D p) ^ 2 := by ring
  have hDsq : (D p) ^ 2 = 2 ^ (2 * b_N p) := by
    change (2 ^ b_N p) ^ 2 = 2 ^ (2 * b_N p)
    rw [← Nat.pow_mul]
    congr 1
    omega
  have hfield : OrdinaryMessageCodec.fieldWidth p.T (D p) ≤ 2 * b_N p := by
    change Nat.clog 2 (p.T * D p + 1) ≤ 2 * b_N p
    apply Nat.clog_le_of_le_pow
    exact hfieldArg.trans_eq hDsq
  have hwidth : AffineBatchDecoder.width p ≤ 10 * b_N p := by
    change 5 * OrdinaryMessageCodec.fieldWidth p.T (D p) ≤ 10 * b_N p
    calc
      5 * OrdinaryMessageCodec.fieldWidth p.T (D p) ≤
          5 * (2 * b_N p) := Nat.mul_le_mul_left 5 hfield
      _ = 10 * b_N p := by omega
  have h2ltK : 2 < p.K := lt_of_le_of_lt p.two_le_m p.m_lt_K
  have hKge3 : 3 ≤ p.K := Nat.succ_le_of_lt h2ltK
  have hKfour : 4 ≤ 2 * p.K := by
    calc
      4 ≤ 2 * 3 := by norm_num
      _ ≤ 2 * p.K := Nat.mul_le_mul_left 2 hKge3
  have hmSub : p.m - 1 ≤ p.m := Nat.sub_le _ _
  have hprefix : 4 * (p.m - 1) * p.T ≤ 4 * p.m * p.T := by
    exact Nat.mul_le_mul_right p.T (Nat.mul_le_mul_left 4 hmSub)
  have hmt : p.m * p.T ≤ p.m * (p.T + 1) :=
    Nat.mul_le_mul_left p.m (Nat.le_succ p.T)
  have hmain : 4 * p.m * p.T ≤ N p := by
    change 4 * p.m * p.T ≤ 2 * p.K * p.m * (p.T + 1)
    calc
      4 * p.m * p.T = 4 * (p.m * p.T) := by ring
      _ ≤ (2 * p.K) * (p.m * p.T) := Nat.mul_le_mul_right _ hKfour
      _ ≤ (2 * p.K) * (p.m * (p.T + 1)) := Nat.mul_le_mul_left _ hmt
      _ = 2 * p.K * p.m * (p.T + 1) := by ring
  have hquotaArg : 4 * (p.m - 1) * p.T * (N p) ^ 2 ≤ (N p) ^ 3 := by
    calc
      4 * (p.m - 1) * p.T * (N p) ^ 2 ≤ N p * (N p) ^ 2 :=
        Nat.mul_le_mul_right _ (hprefix.trans hmain)
      _ = (N p) ^ 3 := by ring
  have hDcube : (D p) ^ 3 = 2 ^ (3 * b_N p) := by
    change (2 ^ b_N p) ^ 3 = 2 ^ (3 * b_N p)
    rw [← Nat.pow_mul]
    congr 1
    omega
  have hNcube : (N p) ^ 3 ≤ (D p) ^ 3 :=
    Nat.pow_le_pow_left (ConstructorDimensions.N_lt_D p).le 3
  have hsecond : Nat.clog 2
      (4 * (p.m - 1) * p.T * (N p) ^ 2) ≤ 3 * b_N p := by
    apply Nat.clog_le_of_le_pow
    exact hquotaArg.trans (hNcube.trans_eq hDcube)
  calc
    AffineBatchDecoder.quota p = AffineBatchDecoder.width p +
        Nat.clog 2 (4 * (p.m - 1) * p.T * (N p) ^ 2) := rfl
    _ ≤ 10 * b_N p + 3 * b_N p := Nat.add_le_add hwidth hsecond
    _ = 13 * b_N p := by omega

/-- The natural logarithm of the follower count and its additive one have
uniform bounds in the source bit length. -/
theorem log_follower_count_bounds (p : Parameters) :
    Real.log ((p.m - 1 : ℕ) : ℝ) ≤ (b_N p : ℝ) ∧
      Real.log ((p.m - 1 : ℕ) : ℝ) + 1 ≤ 2 * (b_N p : ℝ) := by
  have hmge2 : 2 ≤ p.m := p.two_le_m
  have hmpos : 0 < p.m := ConstructorDimensions.m_pos p
  have hdposNat : 0 < p.m - 1 := by omega
  have hm_le_N : p.m ≤ N p :=
    (Nat.le_of_lt p.m_lt_K).trans (ConstructorDimensions.K_le_N p)
  have hd_le_D : p.m - 1 ≤ D p :=
    (Nat.sub_le _ _).trans (hm_le_N.trans (ConstructorDimensions.N_lt_D p).le)
  have hdpos : (0 : ℝ) < ((p.m - 1 : ℕ) : ℝ) := Nat.cast_pos.mpr hdposNat
  have hDpos : (0 : ℝ) < (D p : ℝ) := Nat.cast_pos.mpr (ConstructorDimensions.D_pos p)
  have hdle : ((p.m - 1 : ℕ) : ℝ) ≤ (D p : ℝ) := by exact_mod_cast hd_le_D
  have hlogd : Real.log ((p.m - 1 : ℕ) : ℝ) ≤ (b_N p : ℝ) := by
    have hmon := Real.log_le_log hdpos hdle
    have hlogD : Real.log (D p : ℝ) = (b_N p : ℝ) * Real.log 2 := by
      rw [ConstructorDimensions.D, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
    have hlog2le : Real.log 2 ≤ 1 := by
      calc
        Real.log 2 ≤ 2 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
        _ = 1 := by norm_num
    have hbnonneg : 0 ≤ (b_N p : ℝ) := by positivity
    calc
      Real.log ((p.m - 1 : ℕ) : ℝ) ≤ Real.log (D p : ℝ) := hmon
      _ = (b_N p : ℝ) * Real.log 2 := hlogD
      _ ≤ (b_N p : ℝ) * 1 := mul_le_mul_of_nonneg_left hlog2le hbnonneg
      _ = (b_N p : ℝ) := by ring
  have hbge1 : 1 ≤ (b_N p : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt (ConstructorDimensions.b_N_pos p)
  constructor
  · exact hlogd
  · calc
      Real.log ((p.m - 1 : ℕ) : ℝ) + 1 ≤ (b_N p : ℝ) + 1 := by
        nlinarith only [hlogd]
      _ ≤ (b_N p : ℝ) + (b_N p : ℝ) := by linarith
      _ = 2 * (b_N p : ℝ) := by ring

/-- The universal transport coefficient from the literal three phase bounds. -/
noncomputable def transportConstant : ℝ :=
  2 + 1000 / (1 - Real.exp (-1))

theorem transportConstant_pos : 0 < transportConstant := by
  unfold transportConstant
  have hc := exp_gap_pos
  exact add_pos (by norm_num) (div_pos (by norm_num) hc)

/-- The actual accepted three-phase source coefficient satisfies the source
order bound with one numerical constant independent of the constructor. -/
theorem C_tr_le_transportConstant_mul_m_mul_K_mul_b_N (p : Parameters) :
    ReferenceOriginalStoppedTransportFixedIDMean.C_tr (p := p) ≤
      transportConstant * (p.m : ℝ) * (p.K : ℝ) * (b_N p : ℝ) := by
  let d : ℝ := ((p.m - 1 : ℕ) : ℝ)
  let q : ℝ := (AffineBatchDecoder.quota p : ℝ)
  let k : ℝ := (p.K : ℝ)
  let b : ℝ := (b_N p : ℝ)
  let c : ℝ := 1 - Real.exp (-1)
  have hc : 0 < c := by
    dsimp [c]
    exact exp_gap_pos
  have hm : 1 ≤ p.m := Nat.succ_le_of_lt (ConstructorDimensions.m_pos p)
  have hd_nonneg : 0 ≤ d := by
    dsimp [d]
    positivity
  have hd_le_m : d ≤ (p.m : ℝ) := by
    dsimp [d]
    exact_mod_cast Nat.sub_le p.m 1
  have hk_nonneg : 0 ≤ k := by positivity
  have hb_ge_one : 1 ≤ b := by
    dsimp [b]
    exact_mod_cast Nat.succ_le_of_lt (ConstructorDimensions.b_N_pos p)
  have hb_nonneg : 0 ≤ b := le_trans (by norm_num) hb_ge_one
  have hq : q ≤ 13 * b := by
    dsimp [q, b]
    exact_mod_cast quota_le_thirteen_mul_b_N p
  have hlog_bounds := log_follower_count_bounds p
  have hlog_add : Real.log d + 1 ≤ 2 * b := by
    dsimp [d, b]
    exact hlog_bounds.2
  have hlog : Real.log d ≤ b := by
    dsimp [d, b]
    exact hlog_bounds.1
  have hfirstBracket : 4 * q + Real.log d ≤ 53 * b := by
    dsimp [q, b] at hq
    nlinarith only [hq, hlog]
  have hsecondBracket : 2 * q + Real.log d + 1 ≤ 28 * b := by
    dsimp [q, b] at hq
    nlinarith only [hq, hlog_add]
  have hform : ReferenceOriginalStoppedTransportFixedIDMean.C_tr (p := p) =
      (8 * d * k / c) * (4 * q + Real.log d) +
      (8 * d * k / c) * (2 * q + Real.log d + 1) +
      2 * d * k + (12 * d * k / c) * (Real.log d + 1) := by
    dsimp [ReferenceOriginalStoppedTransportFixedIDMean.C_tr,
      ReferenceOriginalKthCollectionConditionalWaitingCost.B_col,
      ReferenceOriginalFixedInstallationHandoverWaitingCost.B_hand,
      ReferenceOriginalKthReleaseSignedCost.B_rel, d, q, k, c]
    rw [Nat.cast_sub hm]
    ring_nf
  have hdk : d * k ≤ (p.m : ℝ) * k :=
    mul_le_mul_of_nonneg_right hd_le_m hk_nonneg
  have hFirst : (8 * d * k / c) * (53 * b) ≤
      (424 / c) * ((p.m : ℝ) * k * b) := by
    calc
      (8 * d * k / c) * (53 * b) = (424 / c * b) * (d * k) := by ring
      _ ≤ (424 / c * b) * ((p.m : ℝ) * k) :=
        mul_le_mul_of_nonneg_left hdk (by positivity)
      _ = (424 / c) * ((p.m : ℝ) * k * b) := by ring
  have hSecond : (8 * d * k / c) * (28 * b) ≤
      (224 / c) * ((p.m : ℝ) * k * b) := by
    calc
      (8 * d * k / c) * (28 * b) = (224 / c * b) * (d * k) := by ring
      _ ≤ (224 / c * b) * ((p.m : ℝ) * k) :=
        mul_le_mul_of_nonneg_left hdk (by positivity)
      _ = (224 / c) * ((p.m : ℝ) * k * b) := by ring
  have hBaseTerm : 2 * d * k ≤ 2 * ((p.m : ℝ) * k * b) := by
    calc
      2 * d * k = 2 * (d * k) := by ring
      _ ≤ 2 * ((p.m : ℝ) * k) := mul_le_mul_of_nonneg_left hdk (by norm_num)
      _ = 2 * ((p.m : ℝ) * k) * 1 := by ring
      _ ≤ 2 * ((p.m : ℝ) * k) * b :=
        mul_le_mul_of_nonneg_left hb_ge_one (by positivity)
      _ = 2 * ((p.m : ℝ) * k * b) := by ring
  have hRelease : (12 * d * k / c) * (2 * b) ≤
      (24 / c) * ((p.m : ℝ) * k * b) := by
    calc
      (12 * d * k / c) * (2 * b) = (24 / c * b) * (d * k) := by ring
      _ ≤ (24 / c * b) * ((p.m : ℝ) * k) :=
        mul_le_mul_of_nonneg_left hdk (by positivity)
      _ = (24 / c) * ((p.m : ℝ) * k * b) := by ring
  have hFirstBracketScaled : (8 * d * k / c) * (4 * q + Real.log d) ≤
      (8 * d * k / c) * (53 * b) :=
    mul_le_mul_of_nonneg_left hfirstBracket (by positivity)
  have hSecondBracketScaled : (8 * d * k / c) * (2 * q + Real.log d + 1) ≤
      (8 * d * k / c) * (28 * b) :=
    mul_le_mul_of_nonneg_left hsecondBracket (by positivity)
  have hReleaseScaled : (12 * d * k / c) * (Real.log d + 1) ≤
      (12 * d * k / c) * (2 * b) :=
    mul_le_mul_of_nonneg_left hlog_add (by positivity)
  have h672div : (672 : ℝ) / c ≤ 674 / c :=
    div_le_div_of_nonneg_right (by norm_num) hc.le
  have hsum :
      (424 / c) * ((p.m : ℝ) * k * b) +
          (224 / c) * ((p.m : ℝ) * k * b) +
          2 * ((p.m : ℝ) * k * b) +
          (24 / c) * ((p.m : ℝ) * k * b) ≤
        (674 / c + 2) * ((p.m : ℝ) * k * b) := by
    calc
      _ = (672 / c + 2) * ((p.m : ℝ) * k * b) := by ring
      _ ≤ (674 / c + 2) * ((p.m : ℝ) * k * b) :=
        mul_le_mul_of_nonneg_right (by linarith [h672div]) (by positivity)
  have hcoeff : 674 / c + 2 ≤ 1000 / c + 2 := by
    have h674div : (674 : ℝ) / c ≤ 1000 / c :=
      div_le_div_of_nonneg_right (by norm_num) hc.le
    linarith
  have hmkb : 0 ≤ (p.m : ℝ) * k * b := by positivity
  calc
    ReferenceOriginalStoppedTransportFixedIDMean.C_tr (p := p) ≤
        (8 * d * k / c) * (53 * b) +
          (8 * d * k / c) * (28 * b) +
          2 * d * k + (12 * d * k / c) * (2 * b) := by
      rw [hform]
      exact add_le_add
        (add_le_add
          (add_le_add hFirstBracketScaled hSecondBracketScaled)
          (le_of_eq rfl))
        hReleaseScaled
    _ ≤ (424 / c) * ((p.m : ℝ) * k * b) +
          (224 / c) * ((p.m : ℝ) * k * b) +
          2 * ((p.m : ℝ) * k * b) + (24 / c) * ((p.m : ℝ) * k * b) := by
      exact add_le_add
        (add_le_add (add_le_add hFirst hSecond) hBaseTerm) hRelease
    _ ≤ (674 / c + 2) * ((p.m : ℝ) * k * b) := hsum
    _ ≤ (1000 / c + 2) * ((p.m : ℝ) * k * b) :=
      mul_le_mul_of_nonneg_right hcoeff hmkb
    _ = transportConstant * (p.m : ℝ) * (p.K : ℝ) * (b_N p : ℝ) := by
      dsimp [transportConstant, c, k, b]
      ring

/-- One constructor independent positive coefficient, chosen before all
constructor parameters. -/
noncomputable def universalC1 : ℝ := 1024 + 68 * transportConstant

theorem universalC1_pos : 0 < universalC1 := by
  unfold universalC1
  have hA := transportConstant_pos
  linarith

/-- The full accepted eta-times-T coefficient is bounded by `W` for every
positive learning rate. -/
theorem acceptedLearningTransportCoefficient_le_W (p : Parameters) {eta : ℝ}
    (heta : 0 < eta) :
    16 * (p.m : ℝ) ^ 2 + (16 / 11 : ℝ) * CanonicalRecordingRates.R p +
        32 * (p.m : ℝ) + CanonicalRecordingRates.gamma p eta / eta +
        ReferenceOriginalStoppedTransportFixedIDMean.C_tr (p := p) *
          (4 * (p.m : ℝ) + 128) ≤ TuningSourceDimensions.W universalC1 p := by
  let m : ℝ := p.m
  let k : ℝ := p.K
  let b : ℝ := b_N p
  let x : ℝ := ((p.K - p.m + 1 : ℕ) : ℝ)
  have hm2 : 2 ≤ m := by
    dsimp [m]
    exact_mod_cast p.two_le_m
  have hm0 : 0 ≤ m := by positivity
  have hk1 : 1 ≤ k := by
    dsimp [k]
    exact_mod_cast Nat.succ_le_of_lt (ConstructorDimensions.K_pos p)
  have hk0 : 0 ≤ k := le_trans (by norm_num) hk1
  have hb1 : 1 ≤ b := by
    dsimp [b]
    exact_mod_cast Nat.succ_le_of_lt (ConstructorDimensions.b_N_pos p)
  have hb0 : 0 ≤ b := le_trans (by norm_num) hb1
  have hmk0 : 0 ≤ m ^ 2 * k := by positivity
  have hmSq : 4 ≤ m ^ 2 := by nlinarith [sq_nonneg (m - 2)]
  have hKle2K : p.K ≤ 2 * p.K := by
    calc
      p.K = 1 * p.K := by simp
      _ ≤ 2 * p.K := Nat.mul_le_mul_right p.K (by decide)
  have hmle2K : p.m ≤ 2 * p.K := p.m_lt_K.le.trans hKle2K
  have hmle2Kr : (p.m : ℝ) ≤ 2 * (p.K : ℝ) := by exact_mod_cast hmle2K
  have hRBracket : 0 ≤ 2 * k - m ∧ 2 * k - m ≤ 2 * k := by
    constructor <;> dsimp [m, k]
    · linarith
    · linarith [hm0]
  have hR : CanonicalRecordingRates.R p ≤ 128 * m ^ 2 * k := by
    unfold CanonicalRecordingRates.R
    dsimp [m, k]
    calc
      64 * (p.m : ℝ) ^ 2 * (2 * (p.K : ℝ) - (p.m : ℝ)) ≤
          64 * (p.m : ℝ) ^ 2 * (2 * (p.K : ℝ)) :=
        mul_le_mul_of_nonneg_left hRBracket.2 (by positivity)
      _ = 128 * (p.m : ℝ) ^ 2 * (p.K : ℝ) := by ring
  have hRscaled : (16 / 11 : ℝ) * CanonicalRecordingRates.R p ≤
      200 * m ^ 2 * k := by
    calc
      (16 / 11 : ℝ) * CanonicalRecordingRates.R p ≤
          (16 / 11 : ℝ) * (128 * m ^ 2 * k) :=
        mul_le_mul_of_nonneg_left hR (by norm_num)
      _ ≤ 200 * m ^ 2 * k := by nlinarith only [hmk0]
  have hsmall1 : 16 * m ^ 2 ≤ 16 * m ^ 2 * k := by
    calc
      16 * m ^ 2 = (16 * m ^ 2) * 1 := by ring
      _ ≤ (16 * m ^ 2) * k := mul_le_mul_of_nonneg_left hk1 (by positivity)
  have hsmall2 : 32 * m ≤ 16 * m ^ 2 * k := by
    have hmSq2 : 2 * m ≤ m ^ 2 := by nlinarith [sq_nonneg (m - 1)]
    calc
      32 * m ≤ 16 * m ^ 2 := by nlinarith only [hmSq2]
      _ = (16 * m ^ 2) * 1 := by ring
      _ ≤ (16 * m ^ 2) * k := mul_le_mul_of_nonneg_left hk1 (by positivity)
  have hlearn :
      16 * m ^ 2 + (16 / 11 : ℝ) * CanonicalRecordingRates.R p + 32 * m ≤
        232 * m ^ 2 * k := by
    have hsum := add_le_add (add_le_add hsmall1 hRscaled) hsmall2
    calc
      _ ≤ 16 * m ^ 2 * k + 200 * m ^ 2 * k + 16 * m ^ 2 * k := hsum
      _ = 232 * m ^ 2 * k := by ring
  have hL : (CanonicalRecordingRates.L_stab p : ℝ) ≤ 3 * b := by
    dsimp [b]
    exact_mod_cast TuningSourceDimensions.L_stab_le_three_mul_b_N p
  have hmone : 1 ≤ p.m := Nat.succ_le_of_lt (ConstructorDimensions.m_pos p)
  have hxNat : p.K - p.m + 1 ≤ p.K := by
    have hsub := Nat.sub_add_cancel p.m_lt_K.le
    omega
  have hxk : x ≤ k := by
    dsimp [x, k]
    exact_mod_cast hxNat
  have hL0 : 0 ≤ (CanonicalRecordingRates.L_stab p : ℝ) := by positivity
  have hXL : x * (CanonicalRecordingRates.L_stab p : ℝ) ≤ k * (3 * b) := by
    calc
      x * (CanonicalRecordingRates.L_stab p : ℝ) ≤
          k * (CanonicalRecordingRates.L_stab p : ℝ) :=
        mul_le_mul_of_nonneg_right hxk hL0
      _ ≤ k * (3 * b) := mul_le_mul_of_nonneg_left hL (le_of_lt (by positivity))
  have hGammaEq : CanonicalRecordingRates.gamma p eta / eta =
      1024 * x * (CanonicalRecordingRates.L_stab p : ℝ) := by
    rw [CanonicalRecordingRates.gamma, CanonicalRecordingRates.beta]
    dsimp [x]
    field_simp [ne_of_gt heta]
    ring
  have hGamma : CanonicalRecordingRates.gamma p eta / eta ≤ 768 * m ^ 2 * k * b := by
    rw [hGammaEq]
    calc
      1024 * x * (CanonicalRecordingRates.L_stab p : ℝ) ≤
          1024 * (k * (3 * b)) := by nlinarith only [hXL]
      _ = 3072 * k * b := by ring
      _ = 768 * 4 * k * b := by ring
      _ ≤ 768 * m ^ 2 * k * b := by
        have hmul : 0 ≤ 768 * k * b := by positivity
        calc
          768 * 4 * k * b = (768 * k * b) * 4 := by ring
          _ ≤ (768 * k * b) * (m ^ 2) := mul_le_mul_of_nonneg_left hmSq hmul
          _ = 768 * m ^ 2 * k * b := by ring
  have hcount : 4 * m + 128 ≤ 68 * m := by nlinarith only [hm2]
  have htransport :
      ReferenceOriginalStoppedTransportFixedIDMean.C_tr (p := p) * (4 * m + 128) ≤
        68 * transportConstant * m ^ 2 * k * b := by
    have hscale0 : 0 ≤ transportConstant * m * k * b :=
      mul_nonneg (mul_nonneg (mul_nonneg transportConstant_pos.le hm0) hk0) hb0
    have hcount0 : 0 ≤ 4 * m + 128 := by positivity
    calc
      ReferenceOriginalStoppedTransportFixedIDMean.C_tr (p := p) * (4 * m + 128) ≤
          (transportConstant * m * k * b) * (4 * m + 128) :=
        mul_le_mul_of_nonneg_right
          (by
            have h := C_tr_le_transportConstant_mul_m_mul_K_mul_b_N p
            simpa [m, k, b] using h) hcount0
      _ ≤ (transportConstant * m * k * b) * (68 * m) :=
        mul_le_mul_of_nonneg_left hcount hscale0
      _ = 68 * transportConstant * m ^ 2 * k * b := by ring
  have hwhole :
      16 * m ^ 2 + (16 / 11 : ℝ) * CanonicalRecordingRates.R p + 32 * m +
          CanonicalRecordingRates.gamma p eta / eta +
          ReferenceOriginalStoppedTransportFixedIDMean.C_tr (p := p) *
            (4 * m + 128) ≤ (1000 + 68 * transportConstant) * m ^ 2 * k * b := by
    calc
      _ ≤ 232 * m ^ 2 * k + 768 * m ^ 2 * k * b +
          68 * transportConstant * m ^ 2 * k * b := by
        exact add_le_add (add_le_add hlearn hGamma) htransport
      _ ≤ 1000 * m ^ 2 * k * b +
          68 * transportConstant * m ^ 2 * k * b := by
        have hfirst : 232 * m ^ 2 * k ≤ 232 * m ^ 2 * k * b := by
          calc
            232 * m ^ 2 * k = (232 * m ^ 2 * k) * 1 := by ring
            _ ≤ (232 * m ^ 2 * k) * b :=
              mul_le_mul_of_nonneg_left hb1 (by positivity)
        nlinarith only [hfirst]
      _ = (1000 + 68 * transportConstant) * m ^ 2 * k * b := by ring
  unfold TuningSourceDimensions.W universalC1
  have hcoef : 1000 + 68 * transportConstant ≤ 1024 + 68 * transportConstant := by
    norm_num
  have hscale0 : 0 ≤ (p.m : ℝ) ^ 2 * (p.K : ℝ) * (b_N p : ℝ) := by positivity
  calc
    16 * (p.m : ℝ) ^ 2 + (16 / 11 : ℝ) * CanonicalRecordingRates.R p +
        32 * (p.m : ℝ) + CanonicalRecordingRates.gamma p eta / eta +
        ReferenceOriginalStoppedTransportFixedIDMean.C_tr (p := p) *
          (4 * (p.m : ℝ) + 128) ≤
        (1000 + 68 * transportConstant) *
          ((p.m : ℝ) ^ 2 * (p.K : ℝ) * (b_N p : ℝ)) := by
      simpa [m, k, b, mul_assoc] using hwhole
    _ ≤ (1024 + 68 * transportConstant) *
          ((p.m : ℝ) ^ 2 * (p.K : ℝ) * (b_N p : ℝ)) :=
      mul_le_mul_of_nonneg_right hcoef hscale0
    _ = TuningSourceDimensions.W universalC1 p := by
      simp only [TuningSourceDimensions.W, universalC1]
      ring

/-- The literal scalar budget assembled from the accepted source learning and
transport coefficients. -/
noncomputable def combinedBudget (p : Parameters) (eta : ℝ) : ℝ :=
  (2 * Real.log (Nat.choose p.K p.m : ℝ) + (p.m : ℝ) / 16) / eta +
    (16 * (p.m : ℝ) ^ 2 + (16 / 11 : ℝ) * CanonicalRecordingRates.R p +
      32 * (p.m : ℝ)) * eta * (p.T : ℝ) +
    CanonicalRecordingRates.gamma p eta * (p.T : ℝ) +
    ReferenceOriginalStoppedTransportFixedIDMean.C_tr (p := p) *
      ((4 * (p.m : ℝ) + 128) * eta * (p.T : ℝ) + 2)

/-- At every actual active rate, the scalar budget is exactly the accepted raw
learning budget plus the literal exploration and transport terms. -/
theorem combinedBudget_eq_actualRate_budget (p : Parameters)
    (rate : ReferenceActivePhysicalStep.RateInput p) :
    combinedBudget p rate.eta.val =
      ReferenceOriginalCalendarFixedIDLearningMean.rawLearningBudget rate +
        CanonicalRecordingRates.gamma p rate.eta.val * (p.T : ℝ) +
        ReferenceOriginalStoppedTransportFixedIDMean.C_tr (p := p) *
          ((4 * (p.m : ℝ) + 128) * rate.eta.val * (p.T : ℝ) + 2) := by
  rfl

/-- The scalar budget is bounded by the tuned objective, the accepted `W`
coefficient, and the literal transport constant term. -/
theorem combinedBudget_le_source_envelope (p : Parameters) {eta : ℝ}
    (heta : 0 < eta) :
    combinedBudget p eta ≤
      3 * (TuningSourceDimensions.J p : ℝ) / eta +
        TuningSourceDimensions.W universalC1 p * eta * (p.T : ℝ) +
        2 * transportConstant * (p.m : ℝ) * (p.K : ℝ) * (b_N p : ℝ) := by
  have hchoose := TuningSourceDimensions.log_choose_le_log_two_mul_J p
  have hlog2le : Real.log 2 ≤ 1 := by
    calc
      Real.log 2 ≤ 2 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
      _ = 1 := by norm_num
  have hJnonneg : 0 ≤ (TuningSourceDimensions.J p : ℝ) := by positivity
  have hchooseleJ : Real.log (Nat.choose p.K p.m : ℝ) ≤
      (TuningSourceDimensions.J p : ℝ) := by
    calc
      Real.log (Nat.choose p.K p.m : ℝ) ≤
          Real.log 2 * (TuningSourceDimensions.J p : ℝ) := hchoose
      _ ≤ 1 * (TuningSourceDimensions.J p : ℝ) :=
        mul_le_mul_of_nonneg_right hlog2le hJnonneg
      _ = (TuningSourceDimensions.J p : ℝ) := by ring
  have hmleJ : (p.m : ℝ) ≤ (TuningSourceDimensions.J p : ℝ) := by
    exact_mod_cast TuningSourceDimensions.m_le_J p
  have hnumerator :
      2 * Real.log (Nat.choose p.K p.m : ℝ) + (p.m : ℝ) / 16 ≤
        3 * (TuningSourceDimensions.J p : ℝ) := by
    nlinarith only [hchooseleJ, hmleJ]
  have hdivide :
      (2 * Real.log (Nat.choose p.K p.m : ℝ) + (p.m : ℝ) / 16) / eta ≤
        3 * (TuningSourceDimensions.J p : ℝ) / eta :=
    div_le_div_of_nonneg_right hnumerator (le_of_lt heta)
  have hEtaT : 0 ≤ eta * (p.T : ℝ) := by positivity
  have hCoefficient := acceptedLearningTransportCoefficient_le_W p heta
  have hscale :
      (16 * (p.m : ℝ) ^ 2 + (16 / 11 : ℝ) * CanonicalRecordingRates.R p +
        32 * (p.m : ℝ) + CanonicalRecordingRates.gamma p eta / eta +
        ReferenceOriginalStoppedTransportFixedIDMean.C_tr (p := p) *
          (4 * (p.m : ℝ) + 128)) * eta * (p.T : ℝ) ≤
        TuningSourceDimensions.W universalC1 p * eta * (p.T : ℝ) := by
    calc
      _ = (16 * (p.m : ℝ) ^ 2 + (16 / 11 : ℝ) * CanonicalRecordingRates.R p +
          32 * (p.m : ℝ) + CanonicalRecordingRates.gamma p eta / eta +
          ReferenceOriginalStoppedTransportFixedIDMean.C_tr (p := p) *
            (4 * (p.m : ℝ) + 128)) * (eta * (p.T : ℝ)) := by ring
      _ ≤ (TuningSourceDimensions.W universalC1 p) * (eta * (p.T : ℝ)) :=
        mul_le_mul_of_nonneg_right hCoefficient hEtaT
      _ = TuningSourceDimensions.W universalC1 p * eta * (p.T : ℝ) := by ring
  have hconstant :
      2 * ReferenceOriginalStoppedTransportFixedIDMean.C_tr (p := p) ≤
        2 * transportConstant * (p.m : ℝ) * (p.K : ℝ) * (b_N p : ℝ) := by
    have h := C_tr_le_transportConstant_mul_m_mul_K_mul_b_N p
    nlinarith only [h]
  have hfactor :
      combinedBudget p eta =
        (2 * Real.log (Nat.choose p.K p.m : ℝ) + (p.m : ℝ) / 16) / eta +
          (16 * (p.m : ℝ) ^ 2 + (16 / 11 : ℝ) * CanonicalRecordingRates.R p +
            32 * (p.m : ℝ) + CanonicalRecordingRates.gamma p eta / eta +
            ReferenceOriginalStoppedTransportFixedIDMean.C_tr (p := p) *
              (4 * (p.m : ℝ) + 128)) * eta * (p.T : ℝ) +
          2 * ReferenceOriginalStoppedTransportFixedIDMean.C_tr (p := p) := by
    unfold combinedBudget
    field_simp [ne_of_gt heta]
    ring
  rw [hfactor]
  exact add_le_add (add_le_add hdivide hscale) hconstant

/-- One uniform choice of `C₁` and the accepted branch witnesses bounds the
actual combined source budget and its denominator penalty by startup scale. -/
theorem exists_uniform_tuned_combinedBudget_bound :
    ∃ C1 : ℝ, ∃ hC1 : 0 < C1, ∃ Cb : ℝ, ∃ N0 : ℕ, ∃ C : ℝ,
      16 ≤ Cb ∧ 0 < C ∧
      ∀ p : Parameters,
        Cb * (p.m : ℝ) * (p.K : ℝ) * (b_N p : ℝ) ^ 2 < (p.T : ℝ) →
        N0 ≤ N p →
        combinedBudget p (SourceDyadicTuning.sourceRate C1 hC1 p) +
            (p.m : ℝ) * (p.T : ℝ) /
              (SourceDyadicTuning.sourceRate C1 hC1 p * (D p : ℝ)) ≤
          C * BootstrapStartupCostScale.Q_boot p := by
  let C1 : ℝ := universalC1
  have hC1 : 0 < C1 := by
    dsimp [C1]
    exact universalC1_pos
  obtain ⟨Cb, N0, Crem, _, hCbmax, hCrempos, hRemainder⟩ :=
    TunedNumericalRemainder.exists_uniform_tuned_numerical_remainder_bound C1 hC1
  have hCb16 : 16 ≤ Cb := (le_max_left _ _).trans hCbmax
  refine ⟨C1, hC1, Cb, N0, 4 * Crem + 2 * transportConstant, hCb16, ?_⟩
  constructor
  · have hA := transportConstant_pos
    linarith
  · intro p hbranch hN0
    let eta := SourceDyadicTuning.sourceRate C1 hC1 p
    let objective := (TuningSourceDimensions.J p : ℝ) / eta +
      TuningSourceDimensions.W C1 p * eta * (p.T : ℝ)
    let penalty := (p.m : ℝ) * (p.T : ℝ) /
      (eta * (D p : ℝ))
    have heta : 0 < eta := by
      dsimp [eta]
      exact SourceDyadicTuning.sourceRate_pos C1 hC1 p
    have hDpos : 0 < (D p : ℝ) :=
      Nat.cast_pos.mpr (ConstructorDimensions.D_pos p)
    have hAbsorb :
        (p.m : ℝ) * (p.K : ℝ) * (b_N p : ℝ) ≤ BootstrapStartupCostScale.Q_boot p :=
      (hRemainder p hbranch hN0).1
    have hRemain := (hRemainder p hbranch hN0).2.2.2.2.2
    have hpenalty : 0 ≤ penalty := by
      dsimp [penalty]
      exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
        (le_of_lt (mul_pos heta hDpos))
    have hWpart : 0 ≤ TuningSourceDimensions.W C1 p * eta * (p.T : ℝ) := by
      dsimp [eta]
      exact le_of_lt (mul_pos (mul_pos (TuningSourceDimensions.W_pos C1 p hC1)
        (SourceDyadicTuning.sourceRate_pos C1 hC1 p))
        (Nat.cast_pos.mpr (ConstructorDimensions.T_pos p)))
    have hEnv := combinedBudget_le_source_envelope p heta
    have hEnvC1 : combinedBudget p eta ≤
        3 * (TuningSourceDimensions.J p : ℝ) / eta +
          TuningSourceDimensions.W C1 p * eta * (p.T : ℝ) +
          2 * transportConstant * (p.m : ℝ) * (p.K : ℝ) * (b_N p : ℝ) := by
      simpa [TuningSourceDimensions.W] using hEnv
    have hObjectiveScale :
        3 * (TuningSourceDimensions.J p : ℝ) / eta +
          TuningSourceDimensions.W C1 p * eta * (p.T : ℝ) ≤ 3 * objective := by
      dsimp [objective]
      have hWpart_le_three :
          TuningSourceDimensions.W C1 p * eta * (p.T : ℝ) ≤
            3 * (TuningSourceDimensions.W C1 p * eta * (p.T : ℝ)) := by
        have hmul := mul_le_mul_of_nonneg_right
          (show (1 : ℝ) ≤ 3 by norm_num) hWpart
        simpa using hmul
      calc
        _ = 3 * ((TuningSourceDimensions.J p : ℝ) / eta) +
            TuningSourceDimensions.W C1 p * eta * (p.T : ℝ) := by ring
        _ ≤ 3 * ((TuningSourceDimensions.J p : ℝ) / eta) +
            3 * (TuningSourceDimensions.W C1 p * eta * (p.T : ℝ)) := by
          exact add_le_add (le_of_eq rfl) hWpart_le_three
        _ = 3 * ((TuningSourceDimensions.J p : ℝ) / eta +
            TuningSourceDimensions.W C1 p * eta * (p.T : ℝ)) := by ring
    have hEnv' : combinedBudget p eta ≤ 3 * objective +
        2 * transportConstant * (p.m : ℝ) * (p.K : ℝ) * (b_N p : ℝ) := by
      exact hEnvC1.trans (add_le_add hObjectiveScale (le_of_eq rfl))
    have hNpos : 0 < (N p : ℝ) :=
      Nat.cast_pos.mpr (ConstructorDimensions.N_pos p)
    have hBbootpos : 0 < (BootstrapDimensions.B_boot p : ℝ) :=
      Nat.cast_pos.mpr (BootstrapDimensions.B_boot_pos p)
    have hErrorNonneg : 0 ≤
        (p.m : ℝ) * (p.T : ℝ) *
          (5 / (N p : ℝ) ^ 2 + 2 / (N p : ℝ) ^ 2 +
            1 / (BootstrapDimensions.B_boot p : ℝ)) := by
      positivity [hNpos, hBbootpos]
    have hExtra : 0 ≤
        BootstrapStartupCostScale.Q_boot p +
          (p.m : ℝ) * (p.K : ℝ) * (b_N p : ℝ) +
          PublicGridConcentration.rowConcentrationScale p +
          (p.m : ℝ) * (p.T : ℝ) /
            (SourceDyadicTuning.sourceRate C1 hC1 p * (D p : ℝ)) +
          (p.m : ℝ) * (p.T : ℝ) *
            (5 / (N p : ℝ) ^ 2 + 2 / (N p : ℝ) ^ 2 + 1 / (BootstrapDimensions.B_boot p : ℝ)) := by
      have hQboot : 0 ≤ BootstrapStartupCostScale.Q_boot p := by
        unfold BootstrapStartupCostScale.Q_boot
        positivity
      have hrow := PublicGridConcentration.rowConcentrationScale_nonneg p
      have hmkb : 0 ≤ (p.m : ℝ) * (p.K : ℝ) * (b_N p : ℝ) := by positivity
      exact add_nonneg
        (add_nonneg
          (add_nonneg (add_nonneg hQboot hmkb) hrow)
          (by simpa [penalty, eta] using hpenalty))
        hErrorNonneg
    have hObjectiveLeRemainder : objective ≤
        TunedNumericalRemainder.tunedNumericalRemainder C1 hC1 p := by
      dsimp [objective, eta, TunedNumericalRemainder.tunedNumericalRemainder]
      nlinarith only [hExtra]
    have hOriginalPenalty : 0 ≤ (p.m : ℝ) * (p.T : ℝ) / (D p : ℝ) := by
      positivity
    have hRemainderOnly :
        TunedNumericalRemainder.tunedNumericalRemainder C1 hC1 p ≤
          Crem * BootstrapStartupCostScale.Q_boot p := by
      nlinarith only [hRemain, hOriginalPenalty]
    have hObjectiveBound : objective ≤ Crem * BootstrapStartupCostScale.Q_boot p :=
      hObjectiveLeRemainder.trans hRemainderOnly
    have hPenaltyBound : penalty ≤ (TuningSourceDimensions.J p : ℝ) / eta := by
      dsimp [penalty, eta]
      exact SourceDyadicTuning.sourceRate_penalty_comparison C1 hC1 p
    have hpenaltyLeObjective : penalty ≤ objective := by
      dsimp [objective] at hPenaltyBound hWpart ⊢
      nlinarith only [hPenaltyBound, hWpart]
    have hFourObjectiveBound : 4 * objective ≤
        4 * Crem * BootstrapStartupCostScale.Q_boot p := by
      calc
        4 * objective ≤ 4 * (Crem * BootstrapStartupCostScale.Q_boot p) :=
          mul_le_mul_of_nonneg_left hObjectiveBound (by norm_num)
        _ = 4 * Crem * BootstrapStartupCostScale.Q_boot p := by ring
    have hAbsorbScaled :
        (2 * transportConstant) *
            ((p.m : ℝ) * (p.K : ℝ) * (b_N p : ℝ)) ≤
          2 * transportConstant * BootstrapStartupCostScale.Q_boot p := by
      have hconst : 0 ≤ 2 * transportConstant :=
        mul_nonneg (by norm_num) transportConstant_pos.le
      exact mul_le_mul_of_nonneg_left hAbsorb hconst
    nlinarith only [hEnv', hpenaltyLeObjective, hFourObjectiveBound, hAbsorbScaled]

end Bandits.Support.ReferenceLearningTransportRateDomination

end
