/-
Copyright (c) 2026 The Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.CanonicalEpisodePolicy
public import Bandits.Support.RecordedEpisodeStability
public import Bandits.Support.ReplayWeightStability

import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Counts of accepted causal episode starts

Sources: `sources/zip4/manuscript/04_slow_fast_learner.tex:96-104`,
`sources/zip4/manuscript/06_interruptions.tex:40-56`, and
`sources/zip4/manuscript/06_interruptions.tex:512-520`.

The set counted here consists only of starts accepted by the existing causal
episode clock.  Its proof follows the actual clock recursion and
`episode_persists`; it does not install a time-zero episode or identify logical
starts with assignments, reads, or physical transfers.  The prefix theorem
counts starts on any actual history prefix, including a final shortened grid
bin and starts delayed by idle periods.
-/

@[expose] public section

namespace Bandits.Support.EpisodeStartCount

open ConstructorDimensions CanonicalRecordingRates CanonicalQueueProcess CanonicalEpisodePolicy
open RecordedEpisodeStability ReplayWeightStability

variable {K : ℕ}

/-- Accepted episode starts visible in an actual history prefix of length `n`.
Rounds outside the supplied history are excluded.  At a terminal prefix of
length `p.T`, this is exactly the source-history start set below. -/
def prefixStarts (p : Parameters) (H : ℕ)
    (request : (t : Fin p.T) → History p.K t.val → Bool)
    (n : ℕ) (h : History p.K n) : Finset (Fin p.T) :=
  Finset.univ.filter fun t =>
    if ht : t.val < n then
      starts p H request t (historyPrefix t.val n ht.le h) = true
    else False

/-- The literal finite set of accepted starts in a terminal causal history. -/
def episodeStarts (p : Parameters) (H : ℕ)
    (request : (t : Fin p.T) → History p.K t.val → Bool)
    (h : History p.K p.T) : Finset (Fin p.T) :=
  Finset.univ.filter fun t =>
    starts p H request t (historyPrefix t.val p.T t.isLt.le h) = true

theorem mem_prefixStarts_iff (p : Parameters) (H : ℕ)
    (request : (t : Fin p.T) → History p.K t.val → Bool)
    (n : ℕ) (h : History p.K n) (t : Fin p.T) :
    t ∈ prefixStarts p H request n h ↔
      ∃ ht : t.val < n,
        starts p H request t (historyPrefix t.val n ht.le h) = true := by
  classical
  constructor
  · intro hm
    simp only [prefixStarts, Finset.mem_filter, Finset.mem_univ, true_and] at hm
    by_cases ht : t.val < n
    · exact ⟨ht, by simpa only [dite_eq_left ht] using hm⟩
    · simp only [dite_eq_right ht] at hm
  · rintro ⟨ht, hs⟩
    simp only [prefixStarts, Finset.mem_filter, Finset.mem_univ, true_and]
    simpa only [dite_eq_left ht] using hs

private theorem prefix_start_bin_ne (p : Parameters) (H : ℕ) (hH : 0 < H)
    (request : (t : Fin p.T) → History p.K t.val → Bool)
    (n : ℕ) (hn : n ≤ p.T) (h : History p.K n)
    (t u : Fin p.T)
    (ht : t ∈ prefixStarts p H request n h)
    (hu : u ∈ prefixStarts p H request n h)
    (hlt : t.val < u.val) :
    (t.val + 1) / H ≠ (u.val + 1) / H := by
  rcases (mem_prefixStarts_iff p H request n h t).mp ht with ⟨htn, hstart⟩
  rcases (mem_prefixStarts_iff p H request n h u).mp hu with ⟨hun, hstartu⟩
  intro hbin
  have hq : (u.val + 1) / H = (t.val + 1) / H := hbin.symm
  have hdecomp := Nat.mod_add_div (u.val + 1) H
  have hrem := Nat.mod_lt (u.val + 1) hH
  have hgrid : u.val + 1 < H * ((t.val + 1) / H + 1) := by
    rw [Nat.mul_add, Nat.mul_one]
    rw [hq] at hdecomp
    omega
  have hclip : u.val + 1 < p.T + 1 :=
    Nat.succ_lt_succ (Nat.lt_of_lt_of_le hun hn)
  have hbefore : u.val + 1 < sourceEpisodeEnd p.T H (t.val + 1) := by
    unfold sourceEpisodeEnd
    exact Nat.lt_min.mpr ⟨hclip, hgrid⟩
  have huPos : 0 < u.val := by omega
  rcases u with ⟨uVal, uBound⟩
  have huPos' : 0 < uVal := by simpa using huPos
  obtain ⟨v, huv⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt huPos')
  subst uVal
  have htv : t.val ≤ v := by
    have hlt' : t.val < v + 1 := by simpa only [Fin.val_mk] using hlt
    omega
  have htvSucc : t.val ≤ v + 1 := htv.trans (Nat.le_succ v)
  have hvn : v + 1 < n := by simpa only [Fin.val_mk] using hun
  have hvBound : v < p.T := by omega
  have hbefore' : v + 2 < sourceEpisodeEnd p.T H (t.val + 1) := by
    simpa only [Fin.val_mk] using hbefore
  have hEndPrev : v + 1 < sourceEpisodeEnd p.T H (t.val + 1) := by omega
  let current : History p.K (v + 1) :=
    historyPrefix (v + 1) n hvn.le h
  have hstartPrev : starts p H request t
      (historyPrefix t.val v htv current.1) = true := by
    have htrans := historyPrefix_trans t.val (v + 1) n htvSucc hvn.le h
    have hstep := historyPrefix_succ t.val v htv current
    have hhist : historyPrefix t.val v htv current.1 =
        historyPrefix t.val n htn.le h := by
      calc
        historyPrefix t.val v htv current.1 =
            historyPrefix t.val (v + 1) htvSucc current := hstep.symm
        _ = historyPrefix t.val n htn.le h := htrans
    rw [hhist]
    exact hstart
  have hstartPrev' : starts p H request t
      (historyPrefix t.val (⟨v, hvBound⟩ : Fin p.T).val htv current.1) = true := by
    simpa only [Fin.val_mk] using hstartPrev
  have htvPrev : t.val ≤ (⟨v, hvBound⟩ : Fin p.T).val := by
    simpa only [Fin.val_mk] using htv
  have hpersist := episode_persists p H request ⟨v, hvBound⟩ current.1 t
    htvPrev hstartPrev' hEndPrev
  have hclock :
      (clock p H request (v + 1) (Nat.le_of_lt uBound) current).endpoint =
        sourceEpisodeEnd p.T H (t.val + 1) := by
    rw [← Prod.eta current]
    rw [clock_succ p H request v (Nat.le_of_lt uBound) current.1 current.2]
    exact hpersist.2.1
  have hactive : (v + 1) + 1 <
      (clock p H request (v + 1) (Nat.le_of_lt uBound) current).endpoint := by
    rw [hclock]
    omega
  have hfalse := starts_eq_false_of_active p H request ⟨v + 1, uBound⟩
    current hactive
  have hstartuCurrent : starts p H request ⟨v + 1, uBound⟩ current = true := by
    simpa only [Fin.val_mk] using hstartu
  exact Bool.noConfusion (hfalse.symm.trans hstartuCurrent)

/-- Distinct accepted starts in an actual prefix have distinct one-based
source grid-bin indices.  The provenance is the persisted endpoint of the
earlier accepted start in the actual clock state. -/
theorem prefix_start_bin_injOn (p : Parameters) (H : ℕ) (hH : 0 < H)
    (request : (t : Fin p.T) → History p.K t.val → Bool)
    (n : ℕ) (hn : n ≤ p.T) (h : History p.K n) :
    Set.InjOn (fun t : Fin p.T => (t.val + 1) / H)
      (prefixStarts p H request n h : Set (Fin p.T)) := by
  intro t ht u hu hbin
  by_contra hne
  have hval : t.val ≠ u.val := fun heq => hne (Fin.ext heq)
  rcases lt_or_gt_of_ne hval with hlt | hgt
  · exact (prefix_start_bin_ne p H hH request n hn h t u ht hu hlt) hbin
  · exact (prefix_start_bin_ne p H hH request n hn h u t hu ht hgt) hbin.symm

/-- An injection from accepted prefix starts into the source grid bins proves
the count bound, including the final shortened episode. -/
theorem prefix_start_count_le (p : Parameters) (H : ℕ) (hH : 0 < H)
    (request : (t : Fin p.T) → History p.K t.val → Bool)
    (n : ℕ) (hn : n ≤ p.T) (h : History p.K n) :
    (prefixStarts p H request n h).card ≤ n / H + 1 := by
  classical
  calc
    (prefixStarts p H request n h).card ≤ (Finset.range (n / H + 1)).card :=
      Finset.card_le_card_of_injOn (fun t : Fin p.T => (t.val + 1) / H)
        (s := prefixStarts p H request n h) (t := Finset.range (n / H + 1))
        (by
          intro t ht
          rcases (mem_prefixStarts_iff p H request n h t).mp ht with ⟨htn, _⟩
          apply Finset.mem_range.mpr
          have hdiv : (t.val + 1) / H ≤ n / H :=
            Nat.div_le_div_right (Nat.succ_le_of_lt htn)
          exact Nat.lt_succ_of_le hdiv)
        (prefix_start_bin_injOn p H hH request n hn h)
    _ = n / H + 1 := by simp

/-- The terminal finite set is precisely the actual accepted-start set from
the requested full history, with no synthetic start at round zero. -/
theorem episode_start_count_le (p : Parameters) (H : ℕ) (hH : 0 < H)
    (request : (t : Fin p.T) → History p.K t.val → Bool)
    (h : History p.K p.T) :
    (episodeStarts p H request h).card ≤ p.T / H + 1 := by
  simpa [episodeStarts, prefixStarts] using
    (prefix_start_count_le p H hH request p.T le_rfl h)

/-- The source cap makes the floor horizon positive. -/
theorem episodeHorizon_pos (p : Parameters) {eta : ℝ} (heta : 0 < eta)
    (hcap : eta ≤ 1 / (1024 * (p.m : ℝ) * p.K * L_stab p)) :
    0 < ReplayWeightStability.episodeHorizon eta := by
  have hsmall := CanonicalEpisodePolicy.eta_le_one_div_64 p heta hcap
  have hden : 0 < 64 * eta := mul_pos (by norm_num) heta
  have hone : (1 : ℝ) ≤ 1 / (64 * eta) :=
    (le_div_iff₀ hden).2 (by nlinarith only [hsmall])
  simpa [ReplayWeightStability.episodeHorizon] using Nat.floor_pos.mpr hone

/-- The floor and the source cap give the manuscript's lower horizon bound. -/
theorem episodeHorizon_cast_lower (p : Parameters) {eta : ℝ} (heta : 0 < eta)
    (hcap : eta ≤ 1 / (1024 * (p.m : ℝ) * p.K * L_stab p)) :
    (1 / (128 * eta) : ℝ) ≤ (ReplayWeightStability.episodeHorizon eta : ℝ) := by
  let H := ReplayWeightStability.episodeHorizon eta
  have hHpos : 0 < H := episodeHorizon_pos p heta hcap
  have hHone : (1 : ℝ) ≤ (H : ℝ) := by exact_mod_cast (by omega : 1 ≤ H)
  have hfloor : (1 / (64 * eta) : ℝ) < (H : ℝ) + 1 := by
    simpa [H, ReplayWeightStability.episodeHorizon] using
      (Nat.lt_floor_add_one (1 / (64 * eta)))
  have hxH : (1 / (64 * eta) : ℝ) ≤ 2 * (H : ℝ) := by
    linarith only [hfloor, hHone]
  have hxrel : (1 / (64 * eta) : ℝ) = 2 * (1 / (128 * eta)) := by
    field_simp [ne_of_gt heta]
    norm_num
  change (1 / (128 * eta) : ℝ) ≤ (H : ℝ)
  nlinarith only [hxH, hxrel]

/-- For the source horizon and source cap, the actual accepted causal starts
in a terminal history satisfy the quantitative real count
`startCount ≤ 128 * eta * T + 1`.  This counts logical starts only; read
proposals and physical transfers have separate producers. -/
theorem episode_start_count_real_le (p : Parameters) {eta : ℝ}
    (heta : 0 < eta)
    (hcap : eta ≤ 1 / (1024 * (p.m : ℝ) * p.K * L_stab p))
    (request : (t : Fin p.T) → History p.K t.val → Bool)
    (h : History p.K p.T) :
    ((episodeStarts p (ReplayWeightStability.episodeHorizon eta) request h).card : ℝ) ≤
      128 * eta * (p.T : ℝ) + 1 := by
  let H := ReplayWeightStability.episodeHorizon eta
  have hHpos : 0 < H := episodeHorizon_pos p heta hcap
  have hHlower : (1 / (128 * eta) : ℝ) ≤ (H : ℝ) :=
    episodeHorizon_cast_lower p heta hcap
  have hcount := episode_start_count_le p H hHpos request h
  have hcountReal : ((episodeStarts p H request h).card : ℝ) ≤
      ((p.T / H : ℕ) : ℝ) + 1 := by exact_mod_cast hcount
  have hprod : (1 : ℝ) ≤ (128 * eta) * (H : ℝ) := by
    have h := (div_le_iff₀ (by positivity : (0 : ℝ) < 128 * eta)).mp hHlower
    simpa only [mul_comm] using h
  have hTdiv : (p.T : ℝ) / (H : ℝ) ≤ 128 * eta * (p.T : ℝ) := by
    rw [div_le_iff₀ (Nat.cast_pos.mpr hHpos)]
    calc
      (p.T : ℝ) = (p.T : ℝ) * 1 := by ring
      _ ≤ (p.T : ℝ) * ((128 * eta) * (H : ℝ)) :=
        mul_le_mul_of_nonneg_left hprod (by positivity)
      _ = (128 * eta * (p.T : ℝ)) * (H : ℝ) := by ring
  have hNatDivReal : ((p.T / H : ℕ) : ℝ) ≤ (p.T : ℝ) / (H : ℝ) :=
    Nat.cast_div_le
  change ((episodeStarts p (ReplayWeightStability.episodeHorizon eta) request h).card : ℝ) ≤
      128 * eta * (p.T : ℝ) + 1
  calc
    ((episodeStarts p H request h).card : ℝ) ≤ ((p.T / H : ℕ) : ℝ) + 1 := hcountReal
    _ ≤ 128 * eta * (p.T : ℝ) + 1 := by
      linarith only [hNatDivReal, hTdiv]

end Bandits.Support.EpisodeStartCount
