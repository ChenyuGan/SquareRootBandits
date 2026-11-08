module

public import Bandits.Support.ConstructorDimensions
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Fin.Basic

import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Order
import Mathlib.Tactic.Ring

/-!
Literal bootstrap dimensions and the finite calendar partition.  The only
parameters are the accepted constructor parameters.  Source: initialization,
`sources/zip4/manuscript/07_public_setup.tex:5-25`; public table parameters,
`sources/zip4/manuscript/appendix_b_communication.tex:7-23`.
-/

public section

namespace Bandits.Support.BootstrapDimensions

open Bandits.Support.ConstructorDimensions

/-- The source bootstrap block length `ceil(sqrt(T / (m K)))`.
Source: `07_public_setup.tex:13-16` and `appendix_b_communication.tex:10-13`. -/
@[expose] noncomputable def B_boot (p : Parameters) : ℕ :=
  ⌈Real.sqrt ((p.T : ℝ) / ((p.m : ℝ) * (p.K : ℝ)))⌉₊

/-- The source bootstrap block count `ceil(T / B_boot)`.
Source: `07_public_setup.tex:13-16` and `appendix_b_communication.tex:10-13`. -/
@[expose] noncomputable def n_boot (p : Parameters) : ℕ :=
  ⌈(p.T : ℝ) / (B_boot p : ℝ)⌉₊

/-- The source bootstrap identification alphabet, using the actual `b_N`.
Source: `07_public_setup.tex:17-20` and `appendix_b_communication.tex:10-14`. -/
@[expose] noncomputable def A_id (p : Parameters) : ℕ :=
  ⌈(p.T : ℝ) * ((B_boot p : ℝ) + (b_N p : ℝ)) / (b_N p : ℝ)⌉₊

/-- The source dyadic multicast cutoff, using the actual `b_N`.
Source: `07_public_setup.tex:17-20` and `appendix_b_communication.tex:10-14`. -/
@[expose] def L0 (p : Parameters) : ℕ :=
  2 ^ Nat.clog 2 (2 * b_N p)

/-- The source bootstrap decoding quota.
Source: `07_public_setup.tex:21-25`. -/
@[expose] def q_dec (p : Parameters) : ℕ := 8 * L0 p * b_N p

/-- Translate a zero-based `Fin T` offset to the manuscript's one-based round. -/
@[expose] def manuscriptRound (p : Parameters) (t : Fin p.T) : ℕ := t.val + 1

private theorem B_rate_pos (p : Parameters) :
    0 < (p.T : ℝ) / ((p.m : ℝ) * (p.K : ℝ)) := by
  exact div_pos (Nat.cast_pos.mpr (ConstructorDimensions.T_pos p))
    (mul_pos (Nat.cast_pos.mpr (ConstructorDimensions.m_pos p))
      (Nat.cast_pos.mpr (ConstructorDimensions.K_pos p)))

/-- Positivity of the source block length. -/
theorem B_boot_pos (p : Parameters) : 0 < B_boot p := by
  have h : 1 ≤ B_boot p := by
    rw [B_boot, Nat.one_le_ceil_iff]
    exact Real.sqrt_pos.2 (B_rate_pos p)
  omega

/-- The lower real-ceiling bound for `B_boot`. -/
theorem B_boot_real_lower_bound (p : Parameters) :
    Real.sqrt ((p.T : ℝ) / ((p.m : ℝ) * (p.K : ℝ))) ≤ (B_boot p : ℝ) := by
  rw [B_boot]
  exact Nat.le_ceil _

/-- The strict upper real-ceiling bound for `B_boot`. -/
theorem B_boot_real_upper_bound (p : Parameters) :
    (B_boot p : ℝ) <
      Real.sqrt ((p.T : ℝ) / ((p.m : ℝ) * (p.K : ℝ))) + 1 := by
  rw [B_boot]
  exact Nat.ceil_lt_add_one (Real.sqrt_nonneg _)

private theorem real_mK_ge_one (p : Parameters) :
    (1 : ℝ) ≤ (p.m : ℝ) * (p.K : ℝ) := by
  have hm : 1 ≤ p.m := Nat.succ_le_of_lt (ConstructorDimensions.m_pos p)
  have hK : 1 ≤ p.K := Nat.succ_le_of_lt (ConstructorDimensions.K_pos p)
  have hmul : 1 * 1 ≤ p.m * p.K := Nat.mul_le_mul hm hK
  exact_mod_cast hmul

/-- The source ceiling block length never exceeds the horizon. -/
theorem B_boot_le_T (p : Parameters) : B_boot p ≤ p.T := by
  rw [B_boot, Nat.ceil_le]
  have hT : (1 : ℝ) ≤ (p.T : ℝ) := by exact_mod_cast p.one_le_T
  have hTnonneg : (0 : ℝ) ≤ (p.T : ℝ) := by positivity
  have hdenpos : 0 < (p.m : ℝ) * (p.K : ℝ) :=
    mul_pos (Nat.cast_pos.mpr (ConstructorDimensions.m_pos p))
      (Nat.cast_pos.mpr (ConstructorDimensions.K_pos p))
  have hratio :
      (p.T : ℝ) / ((p.m : ℝ) * (p.K : ℝ)) ≤ (p.T : ℝ) := by
    rw [div_le_iff₀ hdenpos]
    calc
      (p.T : ℝ) = (p.T : ℝ) * 1 := by ring
      _ ≤ (p.T : ℝ) * ((p.m : ℝ) * (p.K : ℝ)) :=
        mul_le_mul_of_nonneg_left (real_mK_ge_one p) hTnonneg
  apply Real.sqrt_le_iff.mpr
  constructor
  · exact hTnonneg
  · nlinarith [hratio, hT]

private theorem n_boot_rate_pos (p : Parameters) :
    0 < (p.T : ℝ) / (B_boot p : ℝ) :=
  div_pos (Nat.cast_pos.mpr (ConstructorDimensions.T_pos p))
    (Nat.cast_pos.mpr (B_boot_pos p))

/-- Positivity of the number of calendar blocks. -/
theorem n_boot_pos (p : Parameters) : 0 < n_boot p := by
  have h : 1 ≤ n_boot p := by
    rw [n_boot, Nat.one_le_ceil_iff]
    exact n_boot_rate_pos p
  omega

/-- The lower real-ceiling bound for `n_boot`. -/
theorem n_boot_real_lower_bound (p : Parameters) :
    (p.T : ℝ) / (B_boot p : ℝ) ≤ (n_boot p : ℝ) := by
  rw [n_boot]
  exact Nat.le_ceil _

/-- The strict upper real-ceiling bound for `n_boot`. -/
theorem n_boot_real_upper_bound (p : Parameters) :
    (n_boot p : ℝ) < (p.T : ℝ) / (B_boot p : ℝ) + 1 := by
  rw [n_boot]
  exact Nat.ceil_lt_add_one (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

/-- The source ceiling block count never exceeds the horizon. -/
theorem n_boot_le_T (p : Parameters) : n_boot p ≤ p.T := by
  rw [n_boot, Nat.ceil_le]
  have hTnonneg : (0 : ℝ) ≤ (p.T : ℝ) := by positivity
  have hBge : (1 : ℝ) ≤ (B_boot p : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt (B_boot_pos p)
  have hBpos : 0 < (B_boot p : ℝ) := Nat.cast_pos.mpr (B_boot_pos p)
  rw [div_le_iff₀ hBpos]
  calc
    (p.T : ℝ) = (p.T : ℝ) * 1 := by ring
    _ ≤ (p.T : ℝ) * (B_boot p : ℝ) :=
      mul_le_mul_of_nonneg_left hBge hTnonneg

/-- The natural source size `N` bounds the total bootstrap block volume. -/
theorem K_mul_B_boot_le_N (p : Parameters) : p.K * B_boot p ≤ N p := by
  have hm : 1 ≤ p.m := Nat.succ_le_of_lt (ConstructorDimensions.m_pos p)
  have hKdouble : p.K ≤ 2 * p.K := by
    calc
      p.K = 1 * p.K := by simp
      _ ≤ 2 * p.K := Nat.mul_le_mul_right p.K (by norm_num)
  have hKT : p.K * p.T ≤ N p := by
    change p.K * p.T ≤ 2 * p.K * p.m * (p.T + 1)
    calc
      p.K * p.T ≤ p.K * (p.T + 1) :=
        Nat.mul_le_mul_left p.K (Nat.le_succ p.T)
      _ ≤ (2 * p.K) * (p.T + 1) :=
        Nat.mul_le_mul_right (p.T + 1) hKdouble
      _ ≤ ((2 * p.K) * p.m) * (p.T + 1) :=
        Nat.mul_le_mul_right (p.T + 1) (le_mul_of_one_le_right' hm)
  exact (Nat.mul_le_mul_left p.K (B_boot_le_T p)).trans hKT

/-- The accepted parameter domain makes the source size at least `24`. -/
theorem twentyFour_le_N (p : Parameters) : 24 ≤ N p := by
  have hK : 3 ≤ p.K := Nat.succ_le_of_lt (lt_of_le_of_lt p.two_le_m p.m_lt_K)
  have hT : 2 ≤ p.T + 1 := Nat.succ_le_succ p.one_le_T
  change 24 ≤ 2 * p.K * p.m * (p.T + 1)
  calc
    24 = (2 * 3) * (2 * 2) := by norm_num
    _ ≤ ((2 * p.K) * 2) * 2 := by
      simpa [Nat.mul_assoc] using
        (Nat.mul_le_mul_right (2 * 2) (Nat.mul_le_mul_left 2 hK))
    _ ≤ ((2 * p.K) * p.m) * 2 := by
      simpa [Nat.mul_assoc] using
        (Nat.mul_le_mul_right 2 (Nat.mul_le_mul_left (2 * p.K) p.two_le_m))
    _ ≤ ((2 * p.K) * p.m) * (p.T + 1) :=
      Nat.mul_le_mul_left ((2 * p.K) * p.m) hT

private theorem b_N_real_pos (p : Parameters) : 0 < (b_N p : ℝ) :=
  Nat.cast_pos.mpr (ConstructorDimensions.b_N_pos p)

private theorem A_id_rate_pos (p : Parameters) :
    0 < (p.T : ℝ) * ((B_boot p : ℝ) + (b_N p : ℝ)) / (b_N p : ℝ) := by
  exact div_pos
    (mul_pos (Nat.cast_pos.mpr (ConstructorDimensions.T_pos p))
      (add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) (b_N_real_pos p)))
    (b_N_real_pos p)

/-- Positivity of the source identification alphabet. -/
theorem A_id_pos (p : Parameters) : 0 < A_id p := by
  have h : 1 ≤ A_id p := by
    rw [A_id, Nat.one_le_ceil_iff]
    exact A_id_rate_pos p
  omega

/-- The source alphabet is at least the horizon. -/
theorem T_le_A_id (p : Parameters) : p.T ≤ A_id p := by
  have hTnonneg : (0 : ℝ) ≤ (p.T : ℝ) := Nat.cast_nonneg _
  have hBnonneg : (0 : ℝ) ≤ (B_boot p : ℝ) := Nat.cast_nonneg _
  have hbpos := b_N_real_pos p
  have hrate :
      (p.T : ℝ) ≤
        (p.T : ℝ) * ((B_boot p : ℝ) + (b_N p : ℝ)) / (b_N p : ℝ) := by
    rw [le_div_iff₀ hbpos]
    nlinarith [mul_nonneg hTnonneg hBnonneg]
  have hceil :
      (p.T : ℝ) * ((B_boot p : ℝ) + (b_N p : ℝ)) / (b_N p : ℝ) ≤ (A_id p : ℝ) :=
    Nat.le_ceil _
  exact_mod_cast hrate.trans hceil

/-- The source alphabet times the actual bit length bounds its real numerator. -/
theorem T_mul_boot_plus_b_N_le_A_id_mul_b_N (p : Parameters) :
    p.T * (B_boot p + b_N p) ≤ A_id p * b_N p := by
  have hbpos := b_N_real_pos p
  have hrate :
      (p.T : ℝ) * ((B_boot p : ℝ) + (b_N p : ℝ)) / (b_N p : ℝ) ≤ (A_id p : ℝ) :=
    Nat.le_ceil _
  have hmul :
      (p.T : ℝ) * ((B_boot p : ℝ) + (b_N p : ℝ)) ≤
        (A_id p : ℝ) * (b_N p : ℝ) :=
    (div_le_iff₀ hbpos).1 hrate
  exact_mod_cast hmul

/-- The lower dyadic bound for the source multicast cutoff. -/
theorem two_mul_b_N_le_L0 (p : Parameters) : 2 * b_N p ≤ L0 p := by
  change 2 * b_N p ≤ 2 ^ Nat.clog 2 (2 * b_N p)
  exact Nat.le_pow_clog (by norm_num) _

/-- The strict upper dyadic bound for the source multicast cutoff. -/
theorem L0_lt_four_mul_b_N (p : Parameters) : L0 p < 4 * b_N p := by
  let x := 2 * b_N p
  have hx : 1 < x := by
    dsimp [x]
    have hb := ConstructorDimensions.b_N_pos p
    omega
  have hcpos : 0 < Nat.clog 2 x := Nat.clog_pos (by norm_num) (by omega)
  have hpred : 2 ^ (Nat.clog 2 x).pred < x :=
    Nat.pow_pred_clog_lt_self (by norm_num) (by omega)
  have hpred_add : (Nat.clog 2 x).pred + 1 = Nat.clog 2 x := by
    simpa only [Nat.succ_eq_add_one] using Nat.succ_pred_eq_of_pos hcpos
  change 2 ^ Nat.clog 2 x < 4 * b_N p
  calc
    2 ^ Nat.clog 2 x = 2 ^ ((Nat.clog 2 x).pred + 1) := by
      exact congrArg (fun e : ℕ => 2 ^ e) hpred_add.symm
    _ = 2 ^ (Nat.clog 2 x).pred * 2 := by rw [pow_succ]
    _ = 2 * 2 ^ (Nat.clog 2 x).pred := Nat.mul_comm _ _
    _ < 2 * x := Nat.mul_lt_mul_of_pos_left hpred (by norm_num)
    _ = 4 * b_N p := by dsimp [x]; ring

/-- Every block index has a start strictly before the horizon. -/
private theorem calendar_start_lt_T (p : Parameters) (s : Fin (n_boot p)) :
    s.val * B_boot p < p.T := by
  have hceil := n_boot_real_upper_bound p
  have hsplus : (s.val : ℝ) + 1 ≤ (n_boot p : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt s.isLt
  have hslt : (s.val : ℝ) < (p.T : ℝ) / (B_boot p : ℝ) := by
    have h := hsplus.trans_lt hceil
    linarith
  have hprod :
      (s.val : ℝ) * (B_boot p : ℝ) < (p.T : ℝ) :=
    (lt_div_iff₀ (Nat.cast_pos.mpr (B_boot_pos p))).1 hslt
  exact_mod_cast hprod

/-- The clipped block endpoint is strictly after its start. -/
private theorem calendar_start_lt_stop (p : Parameters) (s : Fin (n_boot p)) :
    s.val * B_boot p < min p.T ((s.val + 1) * B_boot p) := by
  have hT := calendar_start_lt_T p s
  have hnext : s.val * B_boot p < (s.val + 1) * B_boot p := by
    calc
      s.val * B_boot p < s.val * B_boot p + B_boot p :=
        Nat.lt_add_of_pos_right (B_boot_pos p)
      _ = (s.val + 1) * B_boot p := by rw [Nat.add_mul, one_mul]
  exact Nat.lt_min.mpr ⟨hT, hnext⟩

/-- A finite calendar block on zero-based offsets in `Fin T`.
Its points are exactly `s*B_boot ≤ t < min(T,(s+1)*B_boot)`. -/
@[expose] noncomputable def calendarBlock (p : Parameters) (s : Fin (n_boot p)) :
    Finset (Fin p.T) :=
  ((Finset.Ico (s.val * B_boot p) (min p.T ((s.val + 1) * B_boot p))).attach).map
    ⟨(fun x =>
        ⟨x.val, Nat.lt_of_lt_of_le (Finset.mem_Ico.mp x.property).2 (Nat.min_le_left _ _)⟩),
      (by
        intro x y hxy
        apply Subtype.ext
        exact congrArg Fin.val hxy)⟩

/-- Membership in a block is the source half-open interval condition. -/
theorem mem_calendarBlock_iff (p : Parameters) (s : Fin (n_boot p)) (t : Fin p.T) :
    t ∈ calendarBlock p s ↔
      s.val * B_boot p ≤ t.val ∧ t.val < min p.T ((s.val + 1) * B_boot p) := by
  constructor
  · intro ht
    rcases Finset.mem_map.mp ht with ⟨x, _, hxt⟩
    have hx := Finset.mem_Ico.mp x.property
    have hval : x.val = t.val := by simpa using congrArg Fin.val hxt
    simpa [hval] using hx
  · intro ht
    rcases ht with ⟨hlo, hhi⟩
    apply Finset.mem_map.mpr
    refine ⟨⟨t.val, Finset.mem_Ico.mpr ⟨hlo, hhi⟩⟩, Finset.mem_attach _ _, ?_⟩
    apply Fin.ext
    rfl

/-- The exact cardinality of a clipped block. -/
theorem calendarBlock_card (p : Parameters) (s : Fin (n_boot p)) :
    (calendarBlock p s).card = min p.T ((s.val + 1) * B_boot p) - s.val * B_boot p := by
  simp [calendarBlock]

/-- Every calendar block is nonempty. -/
theorem calendarBlock_nonempty (p : Parameters) (s : Fin (n_boot p)) :
    (calendarBlock p s).Nonempty := by
  refine ⟨⟨s.val * B_boot p, calendar_start_lt_T p s⟩, ?_⟩
  rw [mem_calendarBlock_iff]
  exact ⟨Nat.le_refl _, calendar_start_lt_stop p s⟩

/-- Every calendar block has at most `B_boot` rounds. -/
theorem calendarBlock_card_le_B_boot (p : Parameters) (s : Fin (n_boot p)) :
    (calendarBlock p s).card ≤ B_boot p := by
  rw [calendarBlock_card]
  calc
    min p.T ((s.val + 1) * B_boot p) - s.val * B_boot p ≤
        ((s.val + 1) * B_boot p) - s.val * B_boot p :=
      Nat.sub_le_sub_right (Nat.min_le_right _ _) _
    _ = B_boot p := by rw [Nat.add_mul, one_mul, Nat.add_sub_cancel_left]

/-- A nonlast block has its full source length. -/
theorem calendarBlock_card_eq_B_boot_of_nonlast (p : Parameters)
    (s : Fin (n_boot p)) (hlast : s.val + 1 < n_boot p) :
    (calendarBlock p s).card = B_boot p := by
  rw [calendarBlock_card]
  have hceil := n_boot_real_upper_bound p
  have hsplusNat : s.val + 2 ≤ n_boot p := by omega
  have hsplus : (s.val : ℝ) + 2 ≤ (n_boot p : ℝ) := by
    exact_mod_cast hsplusNat
  have hsle : (s.val + 1 : ℝ) ≤ (p.T : ℝ) / (B_boot p : ℝ) := by
    have h := hsplus.trans_lt hceil
    linarith
  have hfullReal :
      (s.val + 1 : ℝ) * (B_boot p : ℝ) ≤ (p.T : ℝ) :=
    (le_div_iff₀ (Nat.cast_pos.mpr (B_boot_pos p))).1 hsle
  have hfull : (s.val + 1) * B_boot p ≤ p.T := by exact_mod_cast hfullReal
  rw [Nat.min_eq_right hfull, Nat.add_mul, one_mul, Nat.add_sub_cancel_left]

/-- The quotient block index for a zero-based round offset. -/
theorem round_quotient_lt_n_boot (p : Parameters) (t : Fin p.T) :
    t.val / B_boot p < n_boot p := by
  have hdiv : (t.val / B_boot p) * B_boot p ≤ t.val :=
    Nat.div_mul_le_self _ _
  have hceil : (p.T : ℝ) ≤ (n_boot p : ℝ) * (B_boot p : ℝ) :=
    (div_le_iff₀ (Nat.cast_pos.mpr (B_boot_pos p))).1 (n_boot_real_lower_bound p)
  have hdivCast :
      ((t.val / B_boot p : ℕ) : ℝ) * (B_boot p : ℝ) ≤ (t.val : ℝ) := by
    exact_mod_cast hdiv
  have ht : (t.val : ℝ) < (p.T : ℝ) := by exact_mod_cast t.isLt
  by_contra hnot
  have hle : n_boot p ≤ t.val / B_boot p := Nat.le_of_not_gt hnot
  have hmul : n_boot p * B_boot p ≤ (t.val / B_boot p) * B_boot p :=
    Nat.mul_le_mul_right (B_boot p) hle
  have hmulCast :
      (n_boot p : ℝ) * (B_boot p : ℝ) ≤
        ((t.val / B_boot p : ℕ) : ℝ) * (B_boot p : ℝ) := by
    exact_mod_cast hmul
  linarith

/-- The unique source block index of a zero-based round offset. -/
@[expose] noncomputable def roundBlockIndex (p : Parameters) (t : Fin p.T) :
    Fin (n_boot p) :=
  ⟨t.val / B_boot p, round_quotient_lt_n_boot p t⟩

/-- Euclidean quotient bounds for the source block length. -/
private theorem round_quotient_bounds (p : Parameters) (t : Fin p.T) :
    (t.val / B_boot p) * B_boot p ≤ t.val ∧
      t.val < (t.val / B_boot p + 1) * B_boot p := by
  have hmod : t.val % B_boot p < B_boot p :=
    Nat.mod_lt _ (Nat.pos_of_ne_zero (Nat.ne_of_gt (B_boot_pos p)))
  have hdecomp :
      (t.val / B_boot p) * B_boot p + t.val % B_boot p = t.val :=
    Nat.div_add_mod' _ _
  constructor
  · exact Nat.div_mul_le_self _ _
  · rw [Nat.add_mul, one_mul]
    omega

/-- A round belongs exactly to the block indexed by its quotient `t / B_boot`.
The quotient is the zero-based block number; `manuscriptRound` translates `t`
to the manuscript's one-based round label `t + 1`. -/
theorem mem_calendarBlock_iff_quotient (p : Parameters) (s : Fin (n_boot p))
    (t : Fin p.T) :
    t ∈ calendarBlock p s ↔ s.val = t.val / B_boot p := by
  rw [mem_calendarBlock_iff]
  constructor
  · rintro ⟨hlo, hhi⟩
    apply le_antisymm
    · exact (Nat.le_div_iff_mul_le
        (Nat.pos_of_ne_zero (Nat.ne_of_gt (B_boot_pos p)))).2 hlo
    · have hup : t.val < (s.val + 1) * B_boot p :=
        lt_of_lt_of_le hhi (Nat.min_le_right _ _)
      have hq : t.val / B_boot p < s.val + 1 :=
        (Nat.div_lt_iff_lt_mul
          (Nat.pos_of_ne_zero (Nat.ne_of_gt (B_boot_pos p)))).2 hup
      omega
  · intro hq
    have hbounds := round_quotient_bounds p t
    rw [← hq] at hbounds
    refine ⟨hbounds.1, Nat.lt_min.mpr ⟨t.isLt, hbounds.2⟩⟩

/-- The quotient block index itself contains the round. -/
theorem round_mem_quotient_block (p : Parameters) (t : Fin p.T) :
    t ∈ calendarBlock p (roundBlockIndex p t) := by
  apply (mem_calendarBlock_iff_quotient p (roundBlockIndex p t) t).2
  rfl

/-- Every calendar round lies in exactly one block, namely its quotient block. -/
theorem round_mem_exactly_one_calendarBlock (p : Parameters) (t : Fin p.T) :
    ∃! s : Fin (n_boot p), t ∈ calendarBlock p s := by
  refine ⟨roundBlockIndex p t, round_mem_quotient_block p t, ?_⟩
  intro s hs
  apply Fin.ext
  exact (mem_calendarBlock_iff_quotient p s t).1 hs

/-- The calendar blocks cover every round in `Fin T`. -/
theorem calendarBlocks_cover (p : Parameters) (t : Fin p.T) :
    ∃ s : Fin (n_boot p), t ∈ calendarBlock p s :=
  ⟨roundBlockIndex p t, round_mem_quotient_block p t⟩

/-- Distinct calendar blocks are disjoint. -/
theorem calendarBlocks_disjoint (p : Parameters) (s r : Fin (n_boot p)) (hne : s ≠ r) :
    Disjoint (calendarBlock p s) (calendarBlock p r) := by
  apply Finset.disjoint_left.mpr
  intro t hst hrt
  apply hne
  apply Fin.ext
  exact ((mem_calendarBlock_iff_quotient p s t).1 hst).trans
    ((mem_calendarBlock_iff_quotient p r t).1 hrt).symm

/-- The half-open zero-based block bounds translated to one-based manuscript rounds. -/
theorem mem_calendarBlock_iff_manuscriptRound (p : Parameters)
    (s : Fin (n_boot p)) (t : Fin p.T) :
    t ∈ calendarBlock p s ↔
      s.val * B_boot p + 1 ≤ manuscriptRound p t ∧
        manuscriptRound p t ≤ min p.T ((s.val + 1) * B_boot p) := by
  rw [mem_calendarBlock_iff]
  change s.val * B_boot p ≤ t.val ∧ t.val < min p.T ((s.val + 1) * B_boot p) ↔
    s.val * B_boot p + 1 ≤ t.val + 1 ∧ t.val + 1 ≤ min p.T ((s.val + 1) * B_boot p)
  omega

/-- Every translated manuscript round lies in `[1,T]`. -/
theorem manuscriptRound_bounds (p : Parameters) (t : Fin p.T) :
    1 ≤ manuscriptRound p t ∧ manuscriptRound p t ≤ p.T := by
  change 1 ≤ t.val + 1 ∧ t.val + 1 ≤ p.T
  omega

end Bandits.Support.BootstrapDimensions
