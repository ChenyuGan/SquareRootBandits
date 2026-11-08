/-
Copyright (c) 2026 The Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.CanonicalQueueProcess
public import Bandits.Support.RecordedEpisodeStability
public import Bandits.Support.RecordedQueueSummation

import Mathlib.Tactic.Linarith

/-!
# Causal logical episodes for the canonical queue process

Sources: `sources/zip4/manuscript/04_slow_fast_learner.tex:96-138,189-215`
and `sources/zip4/manuscript/06_interruptions.tex:9-14,37-71`.
The input request function supplies the logical schedule required by the learner.
Requests during an episode are ignored. An assignment start or collection
cutoff is not an input to this clock. Correspondence with a physical scheduler
and its private recording law remains a separate application obligation.
-/

@[expose] public section

namespace Bandits.Support.CanonicalEpisodePolicy

open ConstructorDimensions CanonicalRecordingRates CanonicalQueueProcess
open RecordedQueueRun RecordedEpisodeStability
open scoped BigOperators

variable {K : ℕ}

/-- Restrict the existing nested outcome history to an earlier prefix. -/
def historyPrefix (a : ℕ) : (t : ℕ) → a ≤ t → History K t → History K a
  | 0, ha, h => by
      have heq : a = 0 := by omega
      subst a
      exact h
  | t + 1, ha, h =>
      if heq : a = t + 1 then heq.symm ▸ h
      else historyPrefix a t (by omega) h.1

theorem historyPrefix_self (t : ℕ) (h : History K t) :
    historyPrefix t t (Nat.le_refl t) h = h := by
  cases t <;> simp only [historyPrefix, ↓reduceDIte]

theorem historyPrefix_succ (a t : ℕ) (ha : a ≤ t) (h : History K (t + 1)) :
    historyPrefix a (t + 1) (by omega) h = historyPrefix a t ha h.1 := by
  simp only [historyPrefix, dite_eq_right (show a ≠ t + 1 by omega)]

theorem historyPrefix_trans (a b t : ℕ) (hab : a ≤ b) (hbt : b ≤ t)
    (h : History K t) :
    historyPrefix a b hab (historyPrefix b t hbt h) =
      historyPrefix a t (hab.trans hbt) h := by
  induction t with
  | zero =>
      have hb : b = 0 := by omega
      have ha : a = 0 := by omega
      subst a
      subst b
      rfl
  | succ t ih =>
      by_cases hb : b = t + 1
      · subst b
        rw [historyPrefix_self]
      · have hbt' : b ≤ t := by omega
        rw [historyPrefix_succ b t hbt', historyPrefix_succ a t (hab.trans hbt')]
        exact ih hbt' h.1

/-- A remembered actual state index and its episode endpoint. Endpoint zero
means no episode has yet started; expired episodes retain their actual anchor. -/
structure ClockState (t : ℕ) where
  anchorIndex : Fin (t + 1)
  endpoint : ℕ

/-- The initial clock has no episode and selects the actual zero state. -/
def initialClock : ClockState 0 := ⟨⟨0, by omega⟩, 0⟩

/-- Passing a calendar round enlarges the valid state-index domain. -/
def liftClock {t : ℕ} (s : ClockState t) : ClockState (t + 1) :=
  ⟨⟨s.anchorIndex.val, by have := s.anchorIndex.isLt; omega⟩, s.endpoint⟩

variable (p : ConstructorDimensions.Parameters)

/-- Requests are used only when the previous episode has reached its endpoint.
The request sees exactly the outcomes before the current round. -/
def acceptStart
    (request : (t : Fin p.T) → History p.K t.val → Bool)
    (t : Fin p.T) (h : History p.K t.val) (s : ClockState t.val) : Bool :=
  decide (s.endpoint ≤ t.val + 1) && request t h

/-- Select the current episode, preserving the remembered index while idle. -/
def chooseClock (H : ℕ)
    (request : (t : Fin p.T) → History p.K t.val → Bool)
    (t : Fin p.T) (h : History p.K t.val) (s : ClockState t.val) : ClockState t.val :=
  if acceptStart p request t h s then
    ⟨⟨t.val, Nat.lt_succ_self _⟩, sourceEpisodeEnd p.T H (t.val + 1)⟩
  else s

/-- Clock after exactly `t` calendar rounds. It changes no queue registers. -/
def clock (H : ℕ)
    (request : (t : Fin p.T) → History p.K t.val → Bool) :
    (t : ℕ) → t ≤ p.T → History p.K t → ClockState t
  | 0, _, _ => initialClock
  | t + 1, ht, h => liftClock (chooseClock p H request ⟨t, by omega⟩ h.1
      (clock H request t (by omega) h.1))

/-- Clock selected before the current update, after considering its request. -/
def roundClock (H : ℕ)
    (request : (t : Fin p.T) → History p.K t.val → Bool)
    (t : Fin p.T) (h : History p.K t.val) : ClockState t.val :=
  chooseClock p H request t h (clock p H request t.val t.isLt.le h)

/-- Whether this round actually starts a logical episode. -/
def starts (H : ℕ)
    (request : (t : Fin p.T) → History p.K t.val → Bool)
    (t : Fin p.T) (h : History p.K t.val) : Bool :=
  acceptStart p request t h (clock p H request t.val t.isLt.le h)

/-- Adapter to the accepted queue process; enablement is logical calendar
enablement, independent of the queue's irreversible overflow flag. -/
def policy (H : ℕ)
    (request : (t : Fin p.T) → History p.K t.val → Bool) : Policy p where
  enabled t h := decide (t.val + 1 < (roundClock p H request t h).endpoint)
  anchorIndex t h := (roundClock p H request t h).anchorIndex

theorem roundClock_of_start (H : ℕ) (request) (t : Fin p.T) (h)
    (hs : starts p H request t h = true) :
    roundClock p H request t h =
      ⟨⟨t.val, Nat.lt_succ_self _⟩, sourceEpisodeEnd p.T H (t.val + 1)⟩ := by
  exact ite_eq_left hs

theorem roundClock_of_no_start (H : ℕ) (request) (t : Fin p.T) (h)
    (hs : starts p H request t h = false) :
    roundClock p H request t h = clock p H request t.val t.isLt.le h := by
  exact ite_eq_right (show starts p H request t h ≠ true from Bool.eq_false_iff.mp hs)

theorem clock_succ (H : ℕ) (request) (t : ℕ) (ht : t + 1 ≤ p.T)
    (h : History p.K t) (o : Option (Fin p.K)) :
    clock p H request (t + 1) ht (h, o) =
      liftClock (roundClock p H request ⟨t, by omega⟩ h) := rfl

/-- Every stored noninitial anchor is a genuine earlier accepted request. -/
theorem clock_origin (H : ℕ) (request) (t : ℕ) (ht : t ≤ p.T)
    (h : History p.K t) :
    ((clock p H request t ht h).endpoint = 0 ∧
      (clock p H request t ht h).anchorIndex.val = 0) ∨
    ∃ (a : Fin p.T) (ha : a.val < t),
      starts p H request a (historyPrefix a.val t ha.le h) = true ∧
      (clock p H request t ht h).anchorIndex.val = a.val ∧
      (clock p H request t ht h).endpoint = sourceEpisodeEnd p.T H (a.val + 1) := by
  induction t with
  | zero => exact Or.inl ⟨rfl, rfl⟩
  | succ t ih =>
      obtain ⟨h, o⟩ := h
      rw [clock_succ]
      by_cases hs : starts p H request ⟨t, by omega⟩ h = true
      · simp only [roundClock_of_start p H request ⟨t, by omega⟩ h hs, liftClock]
        refine Or.inr ⟨⟨t, by omega⟩, Nat.lt_succ_self t, ?_, rfl, rfl⟩
        have hp := historyPrefix_succ (K := p.K) t t le_rfl
          (show History p.K (t + 1) from (h, o))
        have hp' : historyPrefix t (t + 1) (by omega) (h, o) = h :=
          hp.trans (historyPrefix_self t h)
        exact (congrArg (fun h' => starts p H request ⟨t, by omega⟩ h') hp').trans hs
      · have hs' : starts p H request ⟨t, by omega⟩ h = false :=
          Bool.eq_false_iff.mpr hs
        simp only [roundClock_of_no_start p H request ⟨t, by omega⟩ h hs', liftClock]
        rcases ih (by omega) h with hz | ⟨a, ha, hstart, hanchor, hend⟩
        · exact Or.inl hz
        · refine Or.inr ⟨a, by omega, ?_, hanchor, hend⟩
          exact (congrArg (fun h' => starts p H request a h')
            (historyPrefix_succ a.val t ha.le (show History p.K (t + 1) from (h, o)))).trans hstart

/-- Selected anchors also have an actual accepted-start witness. -/
theorem roundClock_origin (H : ℕ) (request) (t : Fin p.T) (h) :
    ((roundClock p H request t h).endpoint = 0 ∧
      (roundClock p H request t h).anchorIndex.val = 0) ∨
    ∃ (a : Fin p.T) (ha : a.val ≤ t.val),
      starts p H request a (historyPrefix a.val t.val ha h) = true ∧
      (roundClock p H request t h).anchorIndex.val = a.val ∧
      (roundClock p H request t h).endpoint = sourceEpisodeEnd p.T H (a.val + 1) := by
  by_cases hs : starts p H request t h = true
  · rw [roundClock_of_start p H request t h hs]
    exact Or.inr ⟨t, le_rfl, by simpa only [historyPrefix_self] using hs, rfl, rfl⟩
  · rw [roundClock_of_no_start p H request t h (Bool.eq_false_iff.mpr hs)]
    rcases clock_origin p H request t.val t.isLt.le h with hz | ⟨a, ha, hs, hi, he⟩
    · exact Or.inl hz
    · exact Or.inr ⟨a, ha.le, hs, hi, he⟩

/-- The cap supplies the small-rate premise used in source calendar stability. -/
theorem eta_le_one_div_64 {eta : ℝ} (heta : 0 < eta)
    (hcap : eta ≤ 1 / (1024 * (p.m : ℝ) * p.K * L_stab p)) : eta ≤ 1 / 64 := by
  have hm : (1 : ℝ) ≤ p.m := by exact_mod_cast (m_pos p)
  have hK : (1 : ℝ) ≤ p.K := by exact_mod_cast (K_pos p)
  have hL : (1 : ℝ) ≤ L_stab p := by exact_mod_cast L_stab_ge_one p
  have hprod := one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le hm hK) hL
  have hd : (64 : ℝ) ≤ 1024 * (p.m : ℝ) * p.K * L_stab p := by
    nlinarith only [hprod]
  have hdpos : 0 < 1024 * (p.m : ℝ) * p.K * L_stab p := lt_of_lt_of_le (by norm_num) hd
  have hmul := (le_div_iff₀ hdpos).mp hcap
  have hsmall := mul_le_mul_of_nonneg_left hd heta.le
  nlinarith only [hmul, hsmall]

/-- The next clipped boundary is strictly after a round inside the horizon. -/
theorem sourceEpisodeEnd_gt (H tau : ℕ) (hH : 0 < H) (htau : tau ≤ p.T) :
    tau < sourceEpisodeEnd p.T H tau := by
  have hmod := Nat.mod_lt tau hH
  have hdiv := Nat.mod_add_div tau H
  apply Nat.lt_min.mpr
  constructor
  · omega
  · rw [Nat.mul_add, Nat.mul_one]
    omega

/-- Exact request acceptance rule, including the boundary round. -/
theorem starts_iff (H : ℕ) (request) (t : Fin p.T) (h) :
    starts p H request t h = true ↔
      (clock p H request t.val t.isLt.le h).endpoint ≤ t.val + 1 ∧ request t h = true := by
  simp only [starts, acceptStart, Bool.and_eq_true, decide_eq_true_eq]

/-- An actual start enables its first update and selects the incoming state. -/
theorem start_enabled (H : ℕ) (hH : 0 < H) (request) (t : Fin p.T) (h)
    (hs : starts p H request t h = true) :
    (policy p H request).enabled t h = true ∧
      ((policy p H request).anchorIndex t h).val = t.val := by
  have hc := roundClock_of_start p H request t h hs
  have hend := congrArg (fun s : ClockState t.val => s.endpoint) hc
  have hindex := congrArg (fun s : ClockState t.val => s.anchorIndex.val) hc
  refine ⟨?_, hindex⟩
  apply decide_eq_true
  exact (sourceEpisodeEnd_gt p H (t.val + 1) hH t.isLt).trans_le (le_of_eq hend.symm)

/-- After an expired episode, absence of a request leaves the clock idle and
retains its most recent actual anchor. -/
theorem idle_without_request (H : ℕ) (request) (t : Fin p.T) (h)
    (hexp : (clock p H request t.val t.isLt.le h).endpoint ≤ t.val + 1)
    (hr : request t h = false) :
    (policy p H request).enabled t h = false ∧
      (policy p H request).anchorIndex t h =
        (clock p H request t.val t.isLt.le h).anchorIndex := by
  have hs : starts p H request t h = false := by
    simp only [starts, acceptStart, hr, Bool.and_false]
  have hc := roundClock_of_no_start p H request t h hs
  constructor
  · change decide (t.val + 1 < (roundClock p H request t h).endpoint) = false
    rw [hc]
    exact decide_eq_false (Nat.not_lt.mpr hexp)
  · exact congrArg (fun s : ClockState t.val => s.anchorIndex) hc

/-- Enabled rounds expose a real episode origin, its fixed index, its exact
boundary, and the derived calendar-age bound. No bounded-age input is used. -/
theorem enabled_episode (H : ℕ) (hH : 0 < H) (request) (t : Fin p.T) (h)
    (he : (policy p H request).enabled t h = true) :
    ∃ (a : Fin p.T) (ha : a.val ≤ t.val),
      starts p H request a (historyPrefix a.val t.val ha h) = true ∧
      ((policy p H request).anchorIndex t h).val = a.val ∧
      (roundClock p H request t h).endpoint = sourceEpisodeEnd p.T H (a.val + 1) ∧
      t.val + 1 < sourceEpisodeEnd p.T H (a.val + 1) ∧
      sourceEpisodeEnd p.T H (a.val + 1) - (a.val + 1) ≤ H ∧
      t.val + 1 - a.val ≤ H := by
  have he' : t.val + 1 < (roundClock p H request t h).endpoint := of_decide_eq_true he
  rcases roundClock_origin p H request t h with hz | ⟨a, ha, hs, hi, hg⟩
  · omega
  · have hb := sourceEpisodeEnd_bounds p.T H (a.val + 1) hH (by omega)
        (by have := a.isLt; omega)
    refine ⟨a, ha, hs, hi, hg, ?_, hb.2.2, ?_⟩ <;> omega

/-- A request made while the stored episode is active is ignored. -/
theorem starts_eq_false_of_active (H : ℕ) (request) (t : Fin p.T) (h)
    (he : t.val + 1 < (clock p H request t.val t.isLt.le h).endpoint) :
    starts p H request t h = false := by
  simp only [starts, acceptStart, Nat.not_le.mpr he, decide_false, Bool.false_and]

/-- Passing a round inside an episode preserves its actual anchor and endpoint,
regardless of the new request or the recording outcome. -/
theorem roundClock_continues (H : ℕ) (request) (t : ℕ) (ht : t + 1 < p.T)
    (h : History p.K t) (o : Option (Fin p.K))
    (he : t + 2 < (roundClock p H request ⟨t, by omega⟩ h).endpoint) :
    roundClock p H request ⟨t + 1, ht⟩ (h, o) =
      liftClock (roundClock p H request ⟨t, by omega⟩ h) := by
  have hactive : t + 1 + 1 <
      (clock p H request (t + 1) ht.le (h, o)).endpoint := by
    simpa only [clock_succ, liftClock] using he
  have hs := starts_eq_false_of_active p H request ⟨t + 1, ht⟩ (h, o) hactive
  simp only [roundClock_of_no_start p H request _ _ hs, clock_succ]

/-- Every round before the boundary of an actual start has that same anchor
and endpoint and is enabled. This includes later assignment-start requests. -/
theorem episode_persists (H : ℕ) (request) (t : Fin p.T) (h : History p.K t.val)
    (a : Fin p.T) (ha : a.val ≤ t.val)
    (hs : starts p H request a (historyPrefix a.val t.val ha h) = true)
    (hg : t.val + 1 < sourceEpisodeEnd p.T H (a.val + 1)) :
    (roundClock p H request t h).anchorIndex.val = a.val ∧
      (roundClock p H request t h).endpoint = sourceEpisodeEnd p.T H (a.val + 1) ∧
      (policy p H request).enabled t h = true := by
  obtain ⟨t, ht⟩ := t
  induction t with
  | zero =>
      dsimp only [Fin.val_mk] at ha hg
      have ha0 : a.val = 0 := by omega
      have hat : a = ⟨0, ht⟩ := Fin.ext ha0
      subst a
      simp only [historyPrefix_self] at hs
      simp only [roundClock_of_start p H request _ _ hs, policy]
      exact ⟨trivial, trivial, decide_eq_true hg⟩
  | succ t ih =>
      dsimp only [Fin.val_mk] at ha hg
      obtain ⟨h, o⟩ := h
      by_cases hat : a.val = t + 1
      · have hat' : a = ⟨t + 1, ht⟩ := Fin.ext hat
        subst a
        have hs0 : starts p H request ⟨t + 1, ht⟩ (h, o) = true :=
          (congrArg (fun h' => starts p H request ⟨t + 1, ht⟩ h')
            (historyPrefix_self (t + 1) (show History p.K (t + 1) from (h, o)))).symm.trans hs
        have hc := roundClock_of_start p H request ⟨t + 1, ht⟩ (h, o) hs0
        have hi := congrArg (fun s : ClockState (t + 1) => s.anchorIndex.val) hc
        have he := congrArg (fun s : ClockState (t + 1) => s.endpoint) hc
        refine ⟨hi, he, ?_⟩
        exact decide_eq_true (hg.trans_le (le_of_eq he.symm))
      · have hat : a.val ≤ t := by omega
        have hs' : starts p H request a (historyPrefix a.val t hat h) = true := by
          exact (congrArg (fun h' => starts p H request a h')
            (historyPrefix_succ a.val t hat (show History p.K (t + 1) from (h, o)))).symm.trans hs
        have hg' : t + 1 < sourceEpisodeEnd p.T H (a.val + 1) := by omega
        obtain ⟨hi, he, _⟩ := ih (by omega) h hat hs' hg'
        have hc : t + 2 < (roundClock p H request ⟨t, by omega⟩ h).endpoint := by
          rw [he]
          exact hg
        have hcontinue := roundClock_continues p H request t ht h o hc
        have hi' : (roundClock p H request ⟨t + 1, ht⟩ (h, o)).anchorIndex.val = a.val := by
          simpa only [hcontinue, liftClock] using hi
        have he' : (roundClock p H request ⟨t + 1, ht⟩ (h, o)).endpoint =
            sourceEpisodeEnd p.T H (a.val + 1) := by
          simpa only [hcontinue, liftClock] using he
        refine ⟨hi', he', ?_⟩
        change decide (t + 1 + 1 < (roundClock p H request ⟨t + 1, ht⟩ (h, o)).endpoint) = true
        rw [he']
        exact decide_eq_true hg

variable (eta : ℝ) (heta : 0 < eta)
  (hcap : eta ≤ 1 / (1024 * (p.m : ℝ) * p.K * L_stab p))
  (n : ℕ) (hn : (n : ℝ) = eta * (D p : ℝ))

local notation "q" => queueParameters p eta heta hcap n hn
local notation "H" => ReplayWeightStability.episodeHorizon eta

include heta hcap in
/-- Positivity of the source floor horizon follows from the cap. -/
theorem horizon_pos : 0 < H := by
  have hsmall := eta_le_one_div_64 p heta hcap
  have hden : 0 < 64 * eta := mul_pos (by norm_num) heta
  apply Nat.floor_pos.mpr
  apply (le_div_iff₀ hden).mpr
  linarith only [hsmall]

/-- Restricting an actual generated list agrees with generating from the
restricted outcome history, for every accepted causal policy. -/
theorem generatedRounds_prefix
    (rewards : FiniteBanditModel.RewardMatrix p.T p.K) (pol : Policy p)
    (t : ℕ) (ht : t ≤ p.T) (h : History p.K t) (a : ℕ) (ha : a ≤ t) :
    (generatedRounds p eta heta hcap n hn rewards pol t ht h).take a =
      generatedRounds p eta heta hcap n hn rewards pol a (ha.trans ht)
        (historyPrefix a t ha h) := by
  induction t with
  | zero =>
      have ha0 : a = 0 := by omega
      subst a
      rfl
  | succ t ih =>
      by_cases hat : a = t + 1
      · subst a
        rw [historyPrefix_self]
        exact List.take_of_length_le (le_of_eq
          (generatedRounds_length p eta heta hcap n hn rewards pol _ ht h))
      · have hat : a ≤ t := by omega
        have hlen : a ≤ (generatedRounds p eta heta hcap n hn rewards pol t
            (by omega) h.1).length := by
          rw [generatedRounds_length]
          exact hat
        simp only [generatedRounds, List.take_append_of_le_length hlen,
          historyPrefix_succ a t hat]
        exact ih (by omega) h.1 hat

/-- Actual selected weights and the canonical input rates remain fixed
throughout an episode, using generated-history prefix consistency. The two
recording outcomes are arbitrary and need not agree. -/
theorem episode_anchor_and_rates_fixed
    (request : (t : Fin p.T) → History p.K t.val → Bool)
    (rewards : FiniteBanditModel.RewardMatrix p.T p.K)
    (t : Fin p.T) (h : History p.K t.val) (a : Fin p.T) (ha : a.val ≤ t.val)
    (hs : starts p H request a (historyPrefix a.val t.val ha h) = true)
    (hg : t.val + 1 < sourceEpisodeEnd p.T H (a.val + 1))
    (o oa : Option (Fin p.K)) :
    let pol := policy p H request
    let past := generatedRounds p eta heta hcap n hn rewards pol t.val t.isLt.le h
    let ah := historyPrefix a.val t.val ha h
    let apast := generatedRounds p eta heta hcap n hn rewards pol a.val a.isLt.le ah
    selectedAnchor p eta heta hcap n hn pol t h past =
      selectedAnchor p eta heta hcap n hn pol a ah apast ∧
    (nextInput p eta heta hcap n hn rewards pol t h past o).rate =
      (nextInput p eta heta hcap n hn rewards pol a ah apast oa).rate := by
  dsimp only
  let pol := policy p H request
  let ah := historyPrefix a.val t.val ha h
  let past := generatedRounds p eta heta hcap n hn rewards pol t.val t.isLt.le h
  let apast := generatedRounds p eta heta hcap n hn rewards pol a.val a.isLt.le ah
  have hi : (pol.anchorIndex t h).val = a.val :=
    (episode_persists p H request t h a ha hs hg).1
  have hia : (pol.anchorIndex a ah).val = a.val :=
    (start_enabled p H (horizon_pos p eta heta hcap) request a ah hs).2
  have hp : past.take a.val = apast :=
    generatedRounds_prefix p eta heta hcap n hn rewards pol t.val t.isLt.le h a.val ha
  have hlen : apast.length = a.val := generatedRounds_length p eta heta hcap n hn _ _ _ _ _
  have hanchor : selectedAnchor p eta heta hcap n hn pol t h past =
      selectedAnchor p eta heta hcap n hn pol a ah apast := by
    unfold selectedAnchor
    rw [hi, hia, hp, List.take_of_length_le (by omega : apast.length ≤ a.val)]
  refine ⟨hanchor, ?_⟩
  funext i
  change xi p eta (selectedAnchor p eta heta hcap n hn pol t h past) i =
    xi p eta (selectedAnchor p eta heta hcap n hn pol a ah apast) i
  rw [hanchor]

/-- The accepted suffix-execution estimate, at two actual list prefixes.
This helper exposes all index and length inputs; the episode theorem below
derives them from the constructed clock. -/
theorem run_take_weight_envelope (rounds : List (RoundInput p.K))
    (a b : ℕ) (hab : a ≤ b) (hb : b ≤ rounds.length) (hgap : b - a ≤ H)
    (i : Fin p.K) :
    scoreWeight q (run q (rounds.take a)) i ≤ scoreWeight q (run q (rounds.take b)) i ∧
      scoreWeight q (run q (rounds.take b)) i < 2 * scoreWeight q (run q (rounds.take a)) i ∧
      Real.log (scoreWeight q (run q (rounds.take b)) i /
        scoreWeight q (run q (rounds.take a)) i) ≤ 4 * eta * ((b - a : ℕ) : ℝ) ∧
      4 * eta * ((b - a : ℕ) : ℝ) ≤ 1 / 16 := by
  have hlen : ((rounds.drop a).take (b - a)).length = b - a := by
    rw [List.length_take, List.length_drop, Nat.min_eq_left (by omega)]
  have hbound : ((rounds.drop a).take (b - a)).length ≤ H := by
    rw [hlen]
    exact hgap
  have hresult := execute_source_weight_envelope q (run q (rounds.take a))
    ((rounds.drop a).take (b - a)) i hbound
  rw [run_take_eq_execute_drop q rounds a b hab]
  simpa only [hlen, queueParameters] using hresult

/-- On every generated enabled prefix the selected anchor is the actual weight
at a genuine earlier start. Both the incoming and completed-update weights
obey the strict factor-two envelope relative to that same anchor. No age,
envelope, physical-scheduling, or no-overflow premise is required. -/
theorem enabled_prefix_weight_envelope
    (request : (t : Fin p.T) → History p.K t.val → Bool)
    (rewards : FiniteBanditModel.RewardMatrix p.T p.K)
    (t : Fin p.T) (h : History p.K t.val) (o : Option (Fin p.K))
    (he : (policy p H request).enabled t h = true) :
    let pol := policy p H request
    let past := generatedRounds p eta heta hcap n hn rewards pol t.val t.isLt.le h
    let anchor := selectedAnchor p eta heta hcap n hn pol t h past
    ∃ (a : Fin p.T) (ha : a.val ≤ t.val),
      starts p H request a (historyPrefix a.val t.val ha h) = true ∧
      (pol.anchorIndex t h).val = a.val ∧
      (roundClock p H request t h).endpoint = sourceEpisodeEnd p.T H (a.val + 1) ∧
      t.val + 1 < sourceEpisodeEnd p.T H (a.val + 1) ∧
      sourceEpisodeEnd p.T H (a.val + 1) - (a.val + 1) ≤ H ∧
      t.val + 1 - a.val ≤ H ∧
      anchor = scoreWeight q (run q (past.take a.val)) ∧
      anchor = scoreWeight q (prefixState p eta heta hcap n hn rewards pol
        a.val (a.isLt.le) (historyPrefix a.val t.val ha h)) ∧
      ∀ i : Fin p.K,
        anchor i ≤ scoreWeight q (prefixState p eta heta hcap n hn rewards pol
          t.val t.isLt.le h) i ∧
        scoreWeight q (prefixState p eta heta hcap n hn rewards pol
          t.val t.isLt.le h) i < 2 * anchor i ∧
        anchor i ≤ scoreWeight q (prefixState p eta heta hcap n hn rewards pol
          (t.val + 1) (by omega) (h, o)) i ∧
        scoreWeight q (prefixState p eta heta hcap n hn rewards pol
          (t.val + 1) (by omega) (h, o)) i < 2 * anchor i := by
  dsimp only
  obtain ⟨a, ha, hs, hi, hg, htg, hgap, hage⟩ :=
    enabled_episode p H (horizon_pos p eta heta hcap) request t h he
  let pol := policy p H request
  let past := generatedRounds p eta heta hcap n hn rewards pol t.val t.isLt.le h
  let full := generatedRounds p eta heta hcap n hn rewards pol (t.val + 1) (by omega) (h, o)
  have hlen : past.length = t.val := generatedRounds_length p eta heta hcap n hn _ _ _ _ _
  have hfull : full = past ++ [nextInput p eta heta hcap n hn rewards pol t h past o] := rfl
  have hfullLen : full.length = t.val + 1 :=
    generatedRounds_length p eta heta hcap n hn _ _ _ _ _
  have hanchor : selectedAnchor p eta heta hcap n hn pol t h past =
      scoreWeight q (run q (past.take a.val)) := by
    unfold selectedAnchor
    rw [hi]
  have hanchorPrefix : selectedAnchor p eta heta hcap n hn pol t h past =
      scoreWeight q (prefixState p eta heta hcap n hn rewards pol
        a.val a.isLt.le (historyPrefix a.val t.val ha h)) := by
    rw [hanchor, generatedRounds_prefix p eta heta hcap n hn rewards pol t.val t.isLt.le h a.val ha]
    rfl
  have htakeA : full.take a.val = past.take a.val := by
    rw [hfull, List.take_append_of_le_length (by omega : a.val ≤ past.length)]
  have htakeT : past.take t.val = past := List.take_of_length_le (by omega)
  have htakeFull : full.take (t.val + 1) = full := List.take_of_length_le (by omega)
  refine ⟨a, ha, hs, hi, hg, htg, hgap, hage, hanchor, hanchorPrefix, ?_⟩
  intro i
  have hpre := run_take_weight_envelope p eta heta hcap n hn past a.val t.val ha
    (by omega) (by omega) i
  have hpost := run_take_weight_envelope p eta heta hcap n hn full a.val (t.val + 1)
    (by omega) (by omega) hage i
  rw [htakeT] at hpre
  rw [htakeA, htakeFull] at hpost
  change selectedAnchor p eta heta hcap n hn pol t h past i ≤ scoreWeight q (run q past) i ∧
    scoreWeight q (run q past) i < 2 * selectedAnchor p eta heta hcap n hn pol t h past i ∧
    selectedAnchor p eta heta hcap n hn pol t h past i ≤ scoreWeight q (run q full) i ∧
    scoreWeight q (run q full) i < 2 * selectedAnchor p eta heta hcap n hn pol t h past i
  rw [hanchor]
  exact ⟨hpre.1, hpre.2.1, hpost.1, hpost.2.1⟩

/-- Actual suffix execution from an earlier generated state, with no score or
backlog reinitialization at a logical episode start. -/
theorem generated_prefix_execution
    (rewards : FiniteBanditModel.RewardMatrix p.T p.K) (pol : Policy p)
    (t : ℕ) (ht : t ≤ p.T) (h : History p.K t) (a : ℕ) (ha : a ≤ t) :
    let past := generatedRounds p eta heta hcap n hn rewards pol t ht h
    prefixState p eta heta hcap n hn rewards pol t ht h =
      execute q (past.drop a)
        (prefixState p eta heta hcap n hn rewards pol a (ha.trans ht)
          (historyPrefix a t ha h)) := by
  dsimp only
  let past := generatedRounds p eta heta hcap n hn rewards pol t ht h
  have hlen : past.length = t := generatedRounds_length p eta heta hcap n hn _ _ _ _ _
  have hfactor := run_take_eq_execute_drop q past a t ha
  have htake : past.take t = past := List.take_of_length_le (by omega)
  have hdrop : (past.drop a).take (t - a) = past.drop a :=
    List.take_of_length_le (by simp only [List.length_drop, hlen]; omega)
  rw [htake, hdrop, generatedRounds_prefix p eta heta hcap n hn rewards pol t ht h a ha]
    at hfactor
  exact hfactor

/-- Starting an episode selects the actual incoming state; the accepted
generator then steps from that same state, preserving all existing queues. -/
theorem start_anchor_eq_incoming_weight
    (request : (t : Fin p.T) → History p.K t.val → Bool)
    (rewards : FiniteBanditModel.RewardMatrix p.T p.K)
    (t : Fin p.T) (h : History p.K t.val)
    (hs : starts p H request t h = true) :
    selectedAnchor p eta heta hcap n hn (policy p H request) t h
      (generatedRounds p eta heta hcap n hn rewards (policy p H request) t.val t.isLt.le h) =
        scoreWeight q (prefixState p eta heta hcap n hn rewards
          (policy p H request) t.val t.isLt.le h) := by
  have hi := (start_enabled p H (horizon_pos p eta heta hcap) request t h hs).2
  unfold selectedAnchor
  rw [hi, List.take_of_length_le (le_of_eq
    (generatedRounds_length p eta heta hcap n hn rewards _ _ _ _))]
  rfl

/-- Pauses and the frozen tail preserve the actual scores and backlogs.
Neither logical starts nor pauses initialize a second queue process. -/
theorem inactive_generated_update_preserves
    (request : (t : Fin p.T) → History p.K t.val → Bool)
    (rewards : FiniteBanditModel.RewardMatrix p.T p.K)
    (t : Fin p.T) (h : History p.K t.val) (o : Option (Fin p.K))
    (hi : (policy p H request).enabled t h = false ∨
      (prefixState p eta heta hcap n hn rewards (policy p H request)
        t.val t.isLt.le h).overflow = true) (i : Fin p.K) :
    (prefixState p eta heta hcap n hn rewards (policy p H request)
      (t.val + 1) (by omega) (h, o)).registers i =
    (prefixState p eta heta hcap n hn rewards (policy p H request)
      t.val t.isLt.le h).registers i := by
  rw [prefixState_succ]
  exact (inactive_input_zero_and_preserves q _ _ _ _ _ hi o).2 i

/-- Every enabled update with a nonfrozen incoming state is retained in full,
including an update whose outgoing state first overflows. No outgoing
no-overflow premise appears. -/
theorem enabled_generated_update_retained
    (request : (t : Fin p.T) → History p.K t.val → Bool)
    (rewards : FiniteBanditModel.RewardMatrix p.T p.K)
    (t : Fin p.T) (h : History p.K t.val) (o : Option (Fin p.K))
    (he : (policy p H request).enabled t h = true)
    (hf : (prefixState p eta heta hcap n hn rewards (policy p H request)
      t.val t.isLt.le h).overflow = false) (i : Fin p.K) :
    let pol := policy p H request
    let past := generatedRounds p eta heta hcap n hn rewards pol t.val t.isLt.le h
    (prefixState p eta heta hcap n hn rewards pol (t.val + 1) (by omega) (h, o)).registers i =
      QueueReplay.transition (4 * n)
        ((prefixState p eta heta hcap n hn rewards pol t.val t.isLt.le h).registers i)
        (true, quantizedArrival q (nextInput p eta heta hcap n hn rewards pol t h past o) i) := by
  dsimp only
  rw [prefixState_succ]
  change QueueReplay.transition (4 * n) _ (acceptedRecord q _ _ i) = _
  have hinput : (nextInput p eta heta hcap n hn rewards (policy p H request) t h
      (generatedRounds p eta heta hcap n hn rewards (policy p H request) t.val t.isLt.le h)
      o).enabled = true := he
  simp only [acceptedRecord, hf, Bool.false_eq_true, ↓reduceIte, hinput]

/-- The accepted terminal correction instantiated on the generated full
horizon. Its rate hypothesis is discharged by the canonical constructor. -/
theorem generated_terminal_backlog_correction_le
    (request : (t : Fin p.T) → History p.K t.val → Bool)
    (rewards : FiniteBanditModel.RewardMatrix p.T p.K)
    (h : History p.K p.T) (S : ProductSetLaw.ProductSet p.K p.m) :
    let pol := policy p H request
    let rounds := generatedRounds p eta heta hcap n hn rewards pol p.T le_rfl h
    let terminal := prefixState p eta heta hcap n hn rewards pol p.T le_rfl h
    (∑ i ∈ S.1, StoppedQueueBound.normalizedBacklog q terminal i) -
      ∑ i : Fin p.K, RecordedQueueSummation.runMarginal q p.m rounds (p.T - 1) i *
        StoppedQueueBound.normalizedBacklog q terminal i ≤ (p.m : ℝ) / (16 * eta) := by
  dsimp only
  let pol := policy p H request
  let rounds := generatedRounds p eta heta hcap n hn rewards pol p.T le_rfl h
  have hlen : rounds.length = p.T := generatedRounds_length p eta heta hcap n hn _ _ _ _ _
  have hrate := generatedRounds_rate_bound p eta heta hcap n hn rewards pol p.T le_rfl h
  have hresult := RecordedQueueSummation.run_terminal_backlog_correction_le q rounds
    p.two_le_m p.m_lt_K S hrate (by rw [hlen]; exact T_pos p)
  simpa only [hlen, List.take_of_length_le (le_of_eq hlen), prefixState, queueParameters] using hresult

end Bandits.Support.CanonicalEpisodePolicy

end
