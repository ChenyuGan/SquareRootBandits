/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.BootstrapDimensions
public import Bandits.Support.BootstrapWeightPotential
public import Bandits.Support.ConstructorDimensions
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Explicit calendar bootstrap blocks

This module builds the calendar-block gain inputs and their stopped finite
weight run from explicit finite traces.  It does not assert that the traces
come from the physical protocol.  Sources:
`sources/zip4/manuscript/07_public_setup.tex:15-38,63-114` and
`sources/zip4/manuscript/appendix_b_communication.tex:524-568`.
-/

public section

namespace Bandits.Support.BootstrapBlockConstruction

open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.BootstrapWeightPotential

/-- Explicit finite inputs for one uninformed follower's calendar-block
analysis.  The observation is the integer index of a bounded rounded value in
`{0, ..., D}`.  The flags are supplied traces, not protocol invariants. -/
structure ExplicitTrace (p : Parameters) where
  idBits : Fin (A_id p) → Fin p.T → Bool
  observation : Fin p.T → Fin (D p + 1)
  active : Fin (n_boot p) → Bool
  heldArm : Fin (n_boot p) → Fin p.K
  privateId : Fin (n_boot p) → Fin (A_id p)
  savedDeclaration : Fin (n_boot p) → Bool
  coordinatorLaunch : Fin (n_boot p) → Bool

/-- Whether this block ends with either stopping event.  The current event is
recorded only for later blocks by `aliveBefore`. -/
@[expose] def stopEvent {p : Parameters} (trace : ExplicitTrace p)
    (s : Fin (n_boot p)) : Bool :=
  trace.savedDeclaration s || trace.coordinatorLaunch s

/-- A literal finite scan of stop events in the blocks strictly before `s`.
The finite universal check is evaluated by `decide`; a declaration or launch
in block `s` is excluded, so it cannot suppress that block's full update. -/
@[expose] noncomputable def aliveBefore {p : Parameters} (trace : ExplicitTrace p)
    (s : Fin (n_boot p)) : Bool :=
  decide (∀ r : Fin (n_boot p), r.val < s.val → stopEvent trace r = false)

/-- All positive stay-observation rounds in the entire calendar block.  The
cutoff for a saved declaration is deliberately absent from this definition. -/
@[expose] noncomputable def positiveStayRounds {p : Parameters} (trace : ExplicitTrace p)
    (s : Fin (n_boot p)) : Finset (Fin p.T) :=
  (calendarBlock p s).filter fun t =>
    trace.idBits (trace.privateId s) t = false ∧ 0 < (trace.observation t).val

/-- The complete source gain for block `s`, counting every positive stay
observation over `calendarBlock p s`. -/
@[expose] noncomputable def calendarBlockGain {p : Parameters} (trace : ExplicitTrace p)
    (s : Fin (n_boot p)) : ℕ :=
  (positiveStayRounds trace s).card

/-- The activity and prior-stop gate for a block.  The event at the end of the
current block is not included. -/
@[expose] noncomputable def blockEnabled {p : Parameters} (trace : ExplicitTrace p)
    (s : Fin (n_boot p)) : Bool :=
  trace.active s && aliveBefore trace s

/-- The effective source gain: the complete calendar gain when the follower is
active and had not stopped earlier, and zero on inactive or later blocks. -/
@[expose] noncomputable def effectiveCalendarBlockGain {p : Parameters}
    (trace : ExplicitTrace p) (s : Fin (n_boot p)) : ℕ :=
  if blockEnabled trace s then calendarBlockGain trace s else 0

/-- Actual `BootstrapWeightPotential.Block` input built from the calendar
partition, common ID table, bounded observation trace, and visible flags.  The
raw gain and held arm may be populated on disabled blocks; the accepted
updater ignores both there. -/
@[expose] noncomputable def blockInput {p : Parameters}
    (trace : ExplicitTrace p) (s : Fin (n_boot p)) :
    BootstrapWeightPotential.Block p.K (B_boot p) where
  enabled := blockEnabled trace s
  held := trace.heldArm s
  gain := calendarBlockGain trace s
  gain_le := (Finset.card_filter_le _ _).trans (calendarBlock_card_le_B_boot p s)

/-- Chronological list of all explicitly constructed calendar-block inputs. -/
@[expose] noncomputable def blockInputs {p : Parameters}
    (trace : ExplicitTrace p) :
    List (BootstrapWeightPotential.Block p.K (B_boot p)) :=
  List.ofFn (blockInput trace)

/-- The actual finite prefix fold of the constructed block list, using the
existing literal `next` update and `listNumerators`. -/
@[expose] noncomputable def blockRun {p : Parameters}
    (trace : ExplicitTrace p) (r : ℕ) : Fin p.K → ℕ :=
  BootstrapWeightPotential.listNumerators (b_N p) (blockInputs trace) r

/-- Recursive view of the same finite run.  The accepted `stoppedInput` tail
is used only beyond the calendar list; all public run theorems restrict to
prefixes within the list. -/
@[expose] noncomputable def recursiveBlockRun {p : Parameters}
    (trace : ExplicitTrace p) (r : ℕ) : Fin p.K → ℕ :=
  BootstrapWeightPotential.numerators (b_N p)
    (BootstrapWeightPotential.stoppedInput (blockInputs trace)
      ⟨0, K_pos p⟩) r

/-- The finite raw gain never exceeds the actual clipped calendar block size. -/
theorem calendarBlockGain_le_card {p : Parameters} (trace : ExplicitTrace p)
    (s : Fin (n_boot p)) :
    calendarBlockGain trace s ≤ (calendarBlock p s).card := by
  classical
  exact Finset.card_filter_le _ _

/-- The source block-length bound discharges the gain field required by the
accepted deterministic update API. -/
theorem calendarBlockGain_le {p : Parameters} (trace : ExplicitTrace p)
    (s : Fin (n_boot p)) : calendarBlockGain trace s ≤ B_boot p := by
  exact (calendarBlockGain_le_card trace s).trans (calendarBlock_card_le_B_boot p s)

/-- Exact decomposition at any saved-declaration round in the block.  The
cutoff round itself belongs to the at-or-after part, so observations after the
declaration is saved remain counted through the block boundary. -/
theorem calendarBlockGain_cutoff_decomposition {p : Parameters}
    (trace : ExplicitTrace p) (s : Fin (n_boot p)) (cutoff : Fin p.T) :
    calendarBlockGain trace s =
      ((positiveStayRounds trace s).filter (fun t => t.val < cutoff.val)).card +
        ((positiveStayRounds trace s).filter (fun t => cutoff.val ≤ t.val)).card := by
  classical
  have h := Finset.card_filter_add_card_filter_not
    (s := positiveStayRounds trace s) (p := fun t => t.val < cutoff.val)
  have h' :
      ((positiveStayRounds trace s).filter (fun t => t.val < cutoff.val)).card +
        ((positiveStayRounds trace s).filter (fun t => cutoff.val ≤ t.val)).card =
          (positiveStayRounds trace s).card := by
    simpa only [not_lt] using h
  simpa [calendarBlockGain] using h'.symm

/-- A declaring/launching block remains enabled whenever it was active and no
earlier block had stopped the scan.  No condition is imposed on its own end
flag: its complete calendar gain is still supplied to the update. -/
theorem current_stop_block_receives_full_gain {p : Parameters}
    (trace : ExplicitTrace p) (s : Fin (n_boot p))
    (hactive : trace.active s = true) (halive : aliveBefore trace s = true) :
    effectiveGain (blockInput trace s) = calendarBlockGain trace s := by
  simp [blockInput, blockEnabled, hactive, halive, effectiveGain]

/-- A declaration or launch at an earlier block boundary makes every later
block disabled by the explicit finite scan. -/
theorem later_block_disabled_of_stop_event {p : Parameters}
    (trace : ExplicitTrace p) (stopped later : Fin (n_boot p))
    (hprior : stopped.val < later.val)
    (hstop : stopEvent trace stopped = true) :
    blockEnabled trace later = false := by
  have hnot : ¬ ∀ r : Fin (n_boot p), r.val < later.val →
      stopEvent trace r = false := by
    intro hall
    have h := hall stopped hprior
    rw [hstop] at h
    cases h
  have halive : aliveBefore trace later = false :=
    decide_eq_false_iff_not.mpr hnot
  simp [blockEnabled, halive]

/-- On an inactive or already-stopped block, the effective gain is zero. -/
theorem effectiveGain_zero_of_disabled {p : Parameters}
    (trace : ExplicitTrace p) (s : Fin (n_boot p))
    (hdisabled : blockEnabled trace s = false) :
    effectiveGain (blockInput trace s) = 0 := by
  simp [blockInput, hdisabled, effectiveGain]

/-- The existing potential input's effective gain is exactly the source gain
with the explicit activity/stop gate applied. -/
theorem effectiveCalendarBlockGain_eq_effectiveGain {p : Parameters}
    (trace : ExplicitTrace p) (s : Fin (n_boot p)) :
    effectiveCalendarBlockGain trace s = effectiveGain (blockInput trace s) := by
  rfl

/-- Disabled block inputs do not change the constructed numerator vector. -/
theorem blockInput_next_eq_of_disabled {p : Parameters}
    (trace : ExplicitTrace p) (s : Fin (n_boot p))
    (n : Fin p.K → ℕ) (hdisabled : blockEnabled trace s = false) :
    next (b_N p) n (blockInput trace s) = n := by
  apply next_disabled
  simp [blockInput, hdisabled]

/-- Any two disabled inputs, including ones with different held arms or raw
gains from different unused private IDs, have identical effective gains and
identical updates. -/
theorem disabled_private_values_irrelevant {p : Parameters}
    (s₁ s₂ : BootstrapWeightPotential.Block p.K (B_boot p))
    (h₁ : s₁.enabled = false) (h₂ : s₂.enabled = false)
    (n : Fin p.K → ℕ) :
    effectiveGain s₁ = effectiveGain s₂ ∧
      next (b_N p) n s₁ = next (b_N p) n s₂ := by
  constructor
  · simp [effectiveGain, h₁, h₂]
  · rw [next_disabled (b := b_N p) n s₁ h₁,
      next_disabled (b := b_N p) n s₂ h₂]

/-- Changing any supplied inactive or stopped private values, including the
unused arm and ID, cannot affect the effective observation gain or updater. -/
theorem disabled_trace_values_irrelevant {p : Parameters}
    (trace₁ trace₂ : ExplicitTrace p) (s : Fin (n_boot p))
    (h₁ : blockEnabled trace₁ s = false)
    (h₂ : blockEnabled trace₂ s = false) (n : Fin p.K → ℕ) :
    effectiveCalendarBlockGain trace₁ s = effectiveCalendarBlockGain trace₂ s ∧
      next (b_N p) n (blockInput trace₁ s) =
        next (b_N p) n (blockInput trace₂ s) := by
  constructor
  · simp [effectiveCalendarBlockGain, h₁, h₂]
  · rw [blockInput_next_eq_of_disabled trace₁ s n h₁,
      blockInput_next_eq_of_disabled trace₂ s n h₂]

/-- Built-list indexing returns the input for the corresponding chronological
calendar index. -/
theorem blockInputs_get {p : Parameters} (trace : ExplicitTrace p)
    (s : Fin (n_boot p)) :
    (blockInputs trace)[s.val]'(by simp [blockInputs]) = blockInput trace s := by
  simp [blockInputs]

/-- The constructed block list has exactly the accepted calendar length. -/
theorem blockInputs_length {p : Parameters} (trace : ExplicitTrace p) :
    (blockInputs trace).length = n_boot p := by
  simp [blockInputs]

/-- The explicitly named run is exactly the existing finite-list fold. -/
theorem blockRun_eq_listNumerators {p : Parameters}
    (trace : ExplicitTrace p) (r : ℕ) :
    blockRun trace r =
      BootstrapWeightPotential.listNumerators (b_N p) (blockInputs trace) r := rfl

/-- The recursive `next` stream agrees with the chronological finite fold on
every prefix through the end of the calendar. -/
theorem recursiveBlockRun_eq_blockRun {p : Parameters}
    (trace : ExplicitTrace p) (r : ℕ) (hr : r ≤ n_boot p) :
    recursiveBlockRun trace r = blockRun trace r := by
  exact BootstrapWeightPotential.numerators_stoppedInput
    (blockInputs trace) ⟨0, K_pos p⟩ r (by
      simpa [blockInputs] using hr)

/-- Every arm weight in every constructed finite prefix remains at least one.
This follows from the accepted numerator update and its all-one initialization. -/
theorem blockRun_weight_ge_one {p : Parameters}
    (trace : ExplicitTrace p) (r : ℕ) (hr : r ≤ n_boot p) (a : Fin p.K) :
    1 ≤ weight (b_N p) (blockRun trace r) a := by
  rw [← recursiveBlockRun_eq_blockRun trace r hr]
  exact BootstrapWeightPotential.weight_ge_one (K_pos p) (B_boot_pos p)
    (BootstrapWeightPotential.stoppedInput (blockInputs trace)
      ⟨0, K_pos p⟩) r a

/-- The deterministic finite potential inequality for the constructed
calendar-block list.  All five numeric side conditions are derived at this
same constructor parameter `p`. -/
theorem constructed_finite_bootstrap_potential_bound {p : Parameters}
    (trace : ExplicitTrace p) (r : ℕ) (hr : r ≤ n_boot p) (a : Fin p.K) :
    (∑ s : Fin r, importance (b_N p) (blockRun trace s.val)
      ((blockInputs trace).get ⟨s.val, lt_of_lt_of_le s.isLt
        (by simpa [blockInputs] using hr)⟩) a) ≤
      4 * (∑ s : Fin r, (effectiveGain
        ((blockInputs trace).get ⟨s.val, lt_of_lt_of_le s.isLt
          (by simpa [blockInputs] using hr)⟩) : ℝ)) +
        8 * p.K * B_boot p * Real.log (p.K : ℝ) := by
  have hNb : N p ≤ 2 ^ b_N p := by
    simpa [ConstructorDimensions.D] using (N_lt_D p).le
  exact BootstrapWeightPotential.finite_bootstrap_potential_bound
    (K_pos p) (B_boot_pos p) (twentyFour_le_N p)
    (K_mul_B_boot_le_N p) hNb (blockInputs trace) r (by
      simpa [blockInputs] using hr) a

/-- The independent activity coin's real atom masses. -/
@[expose] noncomputable def activityProbability (p : Parameters) (active : Bool) : ℝ :=
  if active then 1 / (p.m : ℝ) else 1 - 1 / (p.m : ℝ)

/-- Uniform private-ID atom mass on the source alphabet. -/
@[expose] noncomputable def privateIdProbability (p : Parameters)
    (_u : Fin (A_id p)) : ℝ := 1 / (A_id p : ℝ)

/-- Real atom mass for the fixed-state draw of activity, held arm, and private
ID.  The state is a natural numerator vector on the accepted `b_N` grid. -/
@[expose] noncomputable def privateDrawMass (p : Parameters)
    (n : Fin p.K → ℕ) (outcome : Bool × Fin p.K × Fin (A_id p)) : ℝ :=
  activityProbability p outcome.1 *
    probability (b_N p) n outcome.2.1 * privateIdProbability p outcome.2.2

/-- The private activity probability is nonnegative. -/
theorem activityProbability_nonneg (p : Parameters) (active : Bool) :
    0 ≤ activityProbability p active := by
  have hm : (1 : ℝ) ≤ (p.m : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt (m_pos p))
  have hmpos : 0 < (p.m : ℝ) := Nat.cast_pos.mpr (m_pos p)
  have hinv : 1 / (p.m : ℝ) ≤ 1 := by
    rw [div_le_iff₀ hmpos]
    nlinarith
  cases active with
  | false =>
      simp only [activityProbability, Bool.false_eq_true, ↓reduceIte]
      exact sub_nonneg.mpr hinv
  | true =>
      simp only [activityProbability, ↓reduceIte]
      positivity

/-- Both outcomes of the private activity coin have positive mass in the
accepted constructor domain. -/
theorem activityProbability_pos (p : Parameters) (active : Bool) :
    0 < activityProbability p active := by
  have hmNat : 1 < p.m := lt_of_lt_of_le (by norm_num) p.two_le_m
  have hm : (1 : ℝ) < (p.m : ℝ) := by exact_mod_cast hmNat
  have hmpos : 0 < (p.m : ℝ) := Nat.cast_pos.mpr (m_pos p)
  have hinv : 1 / (p.m : ℝ) < 1 := by
    rw [div_lt_iff₀ hmpos]
    nlinarith
  cases active with
  | false =>
      simp only [activityProbability, Bool.false_eq_true, ↓reduceIte]
      exact sub_pos.mpr hinv
  | true =>
      simp only [activityProbability, ↓reduceIte]
      exact one_div_pos.mpr hmpos

/-- The two activity masses sum to one. -/
theorem activityProbability_sum (p : Parameters) :
    (∑ active : Bool, activityProbability p active) = 1 := by
  rw [Fintype.sum_bool]
  simp [activityProbability]

/-- Uniform private-ID masses sum to one by the accepted positive source
alphabet size. -/
theorem privateIdProbability_sum (p : Parameters) :
    (∑ u : Fin (A_id p), privateIdProbability p u) = 1 := by
  simp only [privateIdProbability, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  field_simp [Nat.cast_ne_zero.mpr (A_id_pos p).ne']

/-- The held-arm mixture is a normalized, strictly positive law from the
accepted bootstrap weight API and the current positive numerator state. -/
theorem heldArmProbability_sum (p : Parameters) (n : Fin p.K → ℕ)
    (hn : ∀ a, 1 ≤ weight (b_N p) n a) :
    (∑ a : Fin p.K, probability (b_N p) n a) = 1 :=
  sum_probability (K_pos p) n hn

/-- Each fixed-state held-arm atom is strictly positive by the accepted
probability lower bound. -/
theorem heldArmProbability_pos (p : Parameters) (n : Fin p.K → ℕ)
    (a : Fin p.K) : 0 < probability (b_N p) n a :=
  probability_pos (b := b_N p) (K_pos p) n a

/-- Every atom of the explicit fixed-state private draw has positive real
mass. -/
theorem privateDrawMass_pos (p : Parameters) (n : Fin p.K → ℕ)
    (outcome : Bool × Fin p.K × Fin (A_id p)) :
    0 < privateDrawMass p n outcome := by
  exact mul_pos (mul_pos (activityProbability_pos p outcome.1)
    (heldArmProbability_pos p n outcome.2.1))
    (one_div_pos.mpr (Nat.cast_pos.mpr (A_id_pos p)))

/-- Every private draw atom is nonnegative. -/
theorem privateDrawMass_nonneg (p : Parameters) (n : Fin p.K → ℕ)
    (outcome : Bool × Fin p.K × Fin (A_id p)) :
    0 ≤ privateDrawMass p n outcome :=
  (privateDrawMass_pos p n outcome).le

/-- Normalization of the complete joint atom law, with each factor derived
from the accepted dimensions and held-arm probability API. -/
theorem privateDrawMass_sum_eq_one (p : Parameters) (n : Fin p.K → ℕ)
    (hn : ∀ a, 1 ≤ weight (b_N p) n a) :
    (∑ outcome : Bool × Fin p.K × Fin (A_id p),
      privateDrawMass p n outcome) = 1 := by
  classical
  simp only [Fintype.sum_prod_type]
  have hinner (active : Bool) (arm : Fin p.K) :
      (∑ u : Fin (A_id p), privateDrawMass p n (active, arm, u)) =
        activityProbability p active * probability (b_N p) n arm := by
    simp only [privateDrawMass]
    rw [← Finset.mul_sum, privateIdProbability_sum, mul_one]
  have hmid (active : Bool) :
      (∑ arm : Fin p.K, ∑ u : Fin (A_id p),
        privateDrawMass p n (active, arm, u)) = activityProbability p active := by
    calc
      _ = ∑ arm : Fin p.K,
          activityProbability p active * probability (b_N p) n arm := by
            apply Finset.sum_congr rfl
            intro arm _
            exact hinner active arm
      _ = activityProbability p active *
          (∑ arm : Fin p.K, probability (b_N p) n arm) := by
            rw [← Finset.mul_sum]
      _ = activityProbability p active := by
            rw [heldArmProbability_sum p n hn, mul_one]
  calc
    _ = ∑ active : Bool, activityProbability p active := by
      apply Finset.sum_congr rfl
      intro active _
      exact hmid active
    _ = 1 := activityProbability_sum p

/-- The finite PMF of the activity coin, held arm, and private ID at a fixed
positive numerator state.  `hn` is the explicit positive-state invariant;
normalization and atom positivity are proved above, not assumed. -/
@[expose] noncomputable def privateBlockDrawLaw (p : Parameters)
    (n : Fin p.K → ℕ) (hn : ∀ a, 1 ≤ weight (b_N p) n a) :
    PMF (Bool × Fin p.K × Fin (A_id p)) :=
  PMF.ofFintype (fun outcome => ENNReal.ofReal (privateDrawMass p n outcome)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg
      (fun outcome _ => privateDrawMass_nonneg p n outcome)]
    rw [privateDrawMass_sum_eq_one p n hn]
    norm_num)

/-- Exact joint atom law of activity, held arm, and private ID. -/
theorem privateBlockDrawLaw_apply (p : Parameters) (n : Fin p.K → ℕ)
    (hn : ∀ a, 1 ≤ weight (b_N p) n a)
    (outcome : Bool × Fin p.K × Fin (A_id p)) :
    privateBlockDrawLaw p n hn outcome =
      ENNReal.ofReal (privateDrawMass p n outcome) := by
  rfl

/-- Every tuple has positive PMF mass; this follows from the three positive
factor laws, not from an assumed support condition. -/
theorem privateBlockDrawLaw_apply_pos (p : Parameters) (n : Fin p.K → ℕ)
    (hn : ∀ a, 1 ≤ weight (b_N p) n a)
    (outcome : Bool × Fin p.K × Fin (A_id p)) :
    0 < privateBlockDrawLaw p n hn outcome := by
  rw [privateBlockDrawLaw_apply]
  exact ENNReal.ofReal_pos.mpr (privateDrawMass_pos p n outcome)

/-- Reading a PMF atom back to `ℝ` recovers its exact explicit joint mass. -/
theorem privateBlockDrawLaw_toReal_apply (p : Parameters) (n : Fin p.K → ℕ)
    (hn : ∀ a, 1 ≤ weight (b_N p) n a)
    (outcome : Bool × Fin p.K × Fin (A_id p)) :
    (privateBlockDrawLaw p n hn outcome).toReal = privateDrawMass p n outcome := by
  rw [privateBlockDrawLaw_apply]
  exact ENNReal.toReal_ofReal (privateDrawMass_nonneg p n outcome)

/-- The arm marginal of the explicit private draw is exactly the accepted
bootstrap held-arm probability. -/
theorem privateBlockDrawLaw_arm_marginal (p : Parameters)
    (n : Fin p.K → ℕ) (hn : ∀ a, 1 ≤ weight (b_N p) n a) (arm : Fin p.K) :
    (∑ active : Bool, ∑ u : Fin (A_id p),
      (privateBlockDrawLaw p n hn (active, arm, u)).toReal) =
        probability (b_N p) n arm := by
  simp_rw [privateBlockDrawLaw_toReal_apply]
  have hinner (active : Bool) :
      (∑ u : Fin (A_id p), privateDrawMass p n (active, arm, u)) =
        activityProbability p active * probability (b_N p) n arm := by
    simp only [privateDrawMass]
    rw [← Finset.mul_sum, privateIdProbability_sum, mul_one]
  calc
    _ = ∑ active : Bool,
        activityProbability p active * probability (b_N p) n arm := by
          apply Finset.sum_congr rfl
          intro active _
          exact hinner active
    _ = (∑ active : Bool, activityProbability p active) *
        probability (b_N p) n arm := by
          rw [Finset.sum_mul]
    _ = probability (b_N p) n arm := by
          rw [activityProbability_sum, one_mul]

/-- The private-ID marginal is uniform on the complete source alphabet. -/
theorem privateBlockDrawLaw_id_marginal (p : Parameters)
    (n : Fin p.K → ℕ) (hn : ∀ a, 1 ≤ weight (b_N p) n a)
    (u : Fin (A_id p)) :
    (∑ active : Bool, ∑ arm : Fin p.K,
      (privateBlockDrawLaw p n hn (active, arm, u)).toReal) =
        privateIdProbability p u := by
  simp_rw [privateBlockDrawLaw_toReal_apply]
  have harm (active : Bool) :
      (∑ arm : Fin p.K, privateDrawMass p n (active, arm, u)) =
        activityProbability p active * privateIdProbability p u := by
    calc
      _ = ∑ arm : Fin p.K,
          activityProbability p active *
            (probability (b_N p) n arm * privateIdProbability p u) := by
              apply Finset.sum_congr rfl
              intro arm _
              simp only [privateDrawMass]
              ring
      _ = activityProbability p active *
          (∑ arm : Fin p.K,
            probability (b_N p) n arm * privateIdProbability p u) := by
              rw [Finset.mul_sum]
      _ = activityProbability p active *
          ((∑ arm : Fin p.K, probability (b_N p) n arm) *
            privateIdProbability p u) := by
              rw [← Finset.sum_mul]
      _ = activityProbability p active * privateIdProbability p u := by
              rw [heldArmProbability_sum p n hn, one_mul]
  calc
    _ = ∑ active : Bool,
        activityProbability p active * privateIdProbability p u := by
          apply Finset.sum_congr rfl
          intro active _
          exact harm active
    _ = (∑ active : Bool, activityProbability p active) *
        privateIdProbability p u := by
          rw [Finset.sum_mul]
    _ = privateIdProbability p u := by
          rw [activityProbability_sum, one_mul]

/-- The activity marginal is Bernoulli with mean `1/m`.  Since the random
variable is the indicator of `true`, this is also its expectation. -/
theorem privateBlockDrawLaw_activity_marginal (p : Parameters)
    (n : Fin p.K → ℕ) (hn : ∀ a, 1 ≤ weight (b_N p) n a) (active : Bool) :
    (∑ arm : Fin p.K, ∑ u : Fin (A_id p),
      (privateBlockDrawLaw p n hn (active, arm, u)).toReal) =
        activityProbability p active := by
  simp_rw [privateBlockDrawLaw_toReal_apply]
  have hinner (active : Bool) (arm : Fin p.K) :
      (∑ u : Fin (A_id p), privateDrawMass p n (active, arm, u)) =
        activityProbability p active * probability (b_N p) n arm := by
    simp only [privateDrawMass]
    rw [← Finset.mul_sum, privateIdProbability_sum, mul_one]
  calc
    _ = ∑ arm : Fin p.K,
        activityProbability p active * probability (b_N p) n arm := by
          apply Finset.sum_congr rfl
          intro arm _
          exact hinner active arm
    _ = activityProbability p active *
        (∑ arm : Fin p.K, probability (b_N p) n arm) := by
          rw [← Finset.mul_sum]
    _ = activityProbability p active := by
          rw [heldArmProbability_sum p n hn, mul_one]

/-- The expectation of the activity indicator under the constructed PMF is
exactly the source mean `1/m`. -/
theorem privateBlockDrawLaw_activity_mean (p : Parameters)
    (n : Fin p.K → ℕ) (hn : ∀ a, 1 ≤ weight (b_N p) n a) :
    (∑ active : Bool, (if active then (1 : ℝ) else 0) *
      (∑ arm : Fin p.K, ∑ u : Fin (A_id p),
        (privateBlockDrawLaw p n hn (active, arm, u)).toReal)) =
          1 / (p.m : ℝ) := by
  rw [Fintype.sum_bool]
  rw [privateBlockDrawLaw_activity_marginal p n hn true,
    privateBlockDrawLaw_activity_marginal p n hn false]
  simp [activityProbability]

/-- Conditional on an active block, the joint held-arm/private-ID atom law is
the product of the accepted bootstrap arm law and the uniform source ID law.
The positive activity mass makes the displayed conditional ratio defined. -/
theorem privateBlockDrawLaw_active_conditional_arm_id (p : Parameters)
    (n : Fin p.K → ℕ) (hn : ∀ a, 1 ≤ weight (b_N p) n a)
    (arm : Fin p.K) (u : Fin (A_id p)) :
    (privateBlockDrawLaw p n hn (true, arm, u)).toReal /
        activityProbability p true =
      probability (b_N p) n arm * privateIdProbability p u := by
  rw [privateBlockDrawLaw_toReal_apply]
  simp only [privateDrawMass, activityProbability, ite_true]
  have hm : (p.m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (m_pos p).ne'
  field_simp [hm]

/-- The private draw law for a constructed prefix uses that prefix's actual
numerator vector.  Its positivity is derived from the accepted finite update,
so callers supply no extra weight-normalization conclusion. -/
@[expose] noncomputable def blockPrivateDrawLaw {p : Parameters}
    (trace : ExplicitTrace p) (r : ℕ) (hr : r ≤ n_boot p) :
    PMF (Bool × Fin p.K × Fin (A_id p)) :=
  privateBlockDrawLaw p (blockRun trace r) (blockRun_weight_ge_one trace r hr)

/-- Exact joint atom law at any actual constructed prefix state. -/
theorem blockPrivateDrawLaw_apply {p : Parameters}
    (trace : ExplicitTrace p) (r : ℕ) (hr : r ≤ n_boot p)
    (outcome : Bool × Fin p.K × Fin (A_id p)) :
    blockPrivateDrawLaw trace r hr outcome =
      ENNReal.ofReal (privateDrawMass p (blockRun trace r) outcome) := by
  exact privateBlockDrawLaw_apply p (blockRun trace r)
    (blockRun_weight_ge_one trace r hr) outcome

end Bandits.Support.BootstrapBlockConstruction

end
