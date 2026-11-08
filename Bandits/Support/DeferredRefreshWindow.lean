/-
Copyright (c) 2026 The Bandits Lean regret formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.CanonicalOrientedSetLaw
public import Bandits.Support.RecordedQueueRun
public import Bandits.Support.RecordedSlowRefresh
import Bandits.Support.DeferredRecurrence
import Bandits.Support.RecordedEpisodeStability
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Finite collection-window slow-law iteration

This module constructs the slow-set PMF by binding the actual residual refresh
kernels along the finite recorded queue path. Its pointwise calculation is the
finite collection-window step in `sources/zip4/manuscript/06_interruptions.tex:399-408`,
using the residual law from `sources/zip4/manuscript/04_slow_fast_learner.tex:176-187`
and the retained queue update described in
`sources/zip4/manuscript/appendix_a_local_protocol.tex:66-75`.

The hypotheses describe an explicit bounded trace. They do not assert a
physical execution, a conditional law, or a sampler coupling.
-/

public section

open scoped BigOperators

namespace Bandits.Support.DeferredRefreshWindow

open Bandits.Support.CanonicalOrientedSetLaw
open Bandits.Support.ConstructorDimensions
open Bandits.Support.RecordedQueueRun
open Bandits.Support.RecordedSlowRefresh

variable {K : ℕ}

/-- The canonical slow mass at an actual recorded run prefix. This is the
source's `p_r`, with `s_r = run q (rounds.take r)`. -/
@[expose] noncomputable def slowMassAt
    (p : ConstructorDimensions.Parameters) (q : RecordedQueueRun.Parameters)
    (rounds : List (RecordedQueueRun.RoundInput p.K))
    (anchor : Fin p.K → ℝ) (hanchor : ∀ i, 0 < anchor i)
    (r : ℕ) (U : CanonicalOrientedSetLaw.SlowSet p.K p.m) : ℝ :=
  RecordedSlowRefresh.recordedSlowMass p q
    (RecordedQueueRun.run q (rounds.take r)) anchor hanchor U

/-- The actual suffix of inputs at calendar indices in `[u,v)`. Together
with the trigger input at `u - 1`, this contains exactly the active input
indices in the collection-window calculation. -/
@[expose] def refreshWindowRounds
    {K : ℕ} (rounds : List (RecordedQueueRun.RoundInput K)) (u v : ℕ) :
    List (RecordedQueueRun.RoundInput K) :=
  (rounds.drop u).take (v - u)

/-- Chronological finite PMF binding along an actual queue path. At each list
entry, the kernel is formed from the current state and then the state advances
by that same `RecordedQueueRun.step`. -/
@[expose] noncomputable def refreshPathPMF
    (p : ConstructorDimensions.Parameters) (q : RecordedQueueRun.Parameters)
    (anchor : Fin p.K → ℝ) (hanchor : ∀ i, 0 < anchor i)
    (hcap : q.eta ≤ 1 /
      (1024 * (p.m : ℝ) * (p.K : ℝ) *
        (CanonicalRecordingRates.L_stab p : ℝ)))
    (state : RecordedQueueRun.RunState p.K) :
    List (RecordedQueueRun.RoundInput p.K) →
      PMF (CanonicalOrientedSetLaw.SlowSet p.K p.m) →
        PMF (CanonicalOrientedSetLaw.SlowSet p.K p.m)
  | [], μ => μ
  | round :: rounds, μ =>
      refreshPathPMF p q anchor hanchor hcap
        (RecordedQueueRun.step q state round) rounds
        (μ.bind (fun U => RecordedSlowRefresh.recordedRefreshKernel
          p q state round anchor hanchor hcap U))

/-- The PMF after binding the existing refresh kernels through the first `n`
inputs of the actual collection-window suffix. -/
@[expose] noncomputable def windowPrefixPMF
    (p : ConstructorDimensions.Parameters) (q : RecordedQueueRun.Parameters)
    (rounds : List (RecordedQueueRun.RoundInput p.K)) (u v : ℕ)
    (hu : 1 ≤ u) (huv : u ≤ v) (hv : v ≤ rounds.length)
    (anchor : Fin p.K → ℝ) (hanchor : ∀ i, 0 < anchor i)
    (hcap : q.eta ≤ 1 /
      (1024 * (p.m : ℝ) * (p.K : ℝ) *
        (CanonicalRecordingRates.L_stab p : ℝ)))
    (n : ℕ) : PMF (CanonicalOrientedSetLaw.SlowSet p.K p.m) :=
  refreshPathPMF p q anchor hanchor hcap
    (RecordedQueueRun.run q (rounds.take u))
    ((refreshWindowRounds rounds u v).take n)
    (RecordedSlowRefresh.residualPMF p q
      (RecordedQueueRun.run q (rounds.take (u - 1)))
      (rounds[u - 1]'(by omega)) anchor hanchor)

/-- The constructed PMF at the end of the finite collection window. The
trigger residual at `u - 1` is its initial law; the subsequent kernels are
bound at the actual indices in `[u,v)`. -/
@[expose] noncomputable def deferredRefreshWindowPMF
    (p : ConstructorDimensions.Parameters) (q : RecordedQueueRun.Parameters)
    (rounds : List (RecordedQueueRun.RoundInput p.K)) (u v : ℕ)
    (hu : 1 ≤ u) (huv : u ≤ v) (hv : v ≤ rounds.length)
    (anchor : Fin p.K → ℝ) (hanchor : ∀ i, 0 < anchor i)
    (hcap : q.eta ≤ 1 /
      (1024 * (p.m : ℝ) * (p.K : ℝ) *
        (CanonicalRecordingRates.L_stab p : ℝ))) :
    PMF (CanonicalOrientedSetLaw.SlowSet p.K p.m) :=
  windowPrefixPMF p q rounds u v hu huv hv anchor hanchor hcap (v - u)

private theorem refreshPathPMF_append
    (p : ConstructorDimensions.Parameters) (q : RecordedQueueRun.Parameters)
    (anchor : Fin p.K → ℝ) (hanchor : ∀ i, 0 < anchor i)
    (hcap : q.eta ≤ 1 /
      (1024 * (p.m : ℝ) * (p.K : ℝ) *
        (CanonicalRecordingRates.L_stab p : ℝ)))
    (state : RecordedQueueRun.RunState p.K)
    (xs ys : List (RecordedQueueRun.RoundInput p.K))
    (μ : PMF (CanonicalOrientedSetLaw.SlowSet p.K p.m)) :
    refreshPathPMF p q anchor hanchor hcap state (xs ++ ys) μ =
      refreshPathPMF p q anchor hanchor hcap
        (RecordedQueueRun.execute q xs state) ys
        (refreshPathPMF p q anchor hanchor hcap state xs μ) := by
  induction xs generalizing state μ with
  | nil => rfl
  | cons round xs ih =>
      simp only [List.cons_append, refreshPathPMF]
      exact ih (RecordedQueueRun.step q state round)
        (μ.bind (fun U => RecordedSlowRefresh.recordedRefreshKernel
          p q state round anchor hanchor hcap U))

private theorem execute_take_succ_eq_step
    {K : ℕ}
    (q : RecordedQueueRun.Parameters)
    (rounds : List (RecordedQueueRun.RoundInput K))
    (state : RecordedQueueRun.RunState K) (n : ℕ)
    (hn : n < rounds.length) :
    RecordedQueueRun.execute q (rounds.take (n + 1)) state =
      RecordedQueueRun.step q (RecordedQueueRun.execute q (rounds.take n) state)
        rounds[n] := by
  rw [← List.take_concat_get' rounds n hn,
    RecordedSlowRefresh.execute_append]
  rfl

private theorem windowPrefixState_eq_run
    {K : ℕ}
    (q : RecordedQueueRun.Parameters)
    (rounds : List (RecordedQueueRun.RoundInput K)) (u v n : ℕ)
    (huv : u ≤ v) (hv : v ≤ rounds.length) (hn : n ≤ v - u) :
    RecordedQueueRun.execute q ((refreshWindowRounds rounds u v).take n)
        (RecordedQueueRun.run q (rounds.take u)) =
      RecordedQueueRun.run q (rounds.take (u + n)) := by
  have htake : (refreshWindowRounds rounds u v).take n =
      (rounds.drop u).take n := by
    have hNle' : v - u ≤ rounds.length - u := Nat.sub_le_sub_right hv u
    have hndrop' : n ≤ rounds.length - u := by omega
    simp [refreshWindowRounds, List.take_take, List.length_drop,
      Nat.min_eq_left hNle', Nat.min_eq_left hn, Nat.min_eq_left hndrop']
  rw [htake]
  symm
  rw [RecordedEpisodeStability.run_take_eq_execute_drop q rounds u (u + n) (by omega)]
  simp only [Nat.add_sub_cancel_left]

private theorem refreshWindowRounds_length
    {K : ℕ} (rounds : List (RecordedQueueRun.RoundInput K)) (u v : ℕ)
    (hv : v ≤ rounds.length) :
    (refreshWindowRounds rounds u v).length = v - u := by
  have hle : v - u ≤ (rounds.drop u).length := by
    rw [List.length_drop]
    exact Nat.sub_le_sub_right hv u
  change ((rounds.drop u).take (v - u)).length = v - u
  rw [List.length_take, Nat.min_eq_left hle]

private theorem run_prefix_overflow_false
    {K : ℕ}
    (q : RecordedQueueRun.Parameters)
    (rounds : List (RecordedQueueRun.RoundInput K)) (v n : ℕ)
    (hn : n ≤ v)
    (hretain : (RecordedQueueRun.run q (rounds.take v)).overflow = false) :
    (RecordedQueueRun.run q (rounds.take n)).overflow = false := by
  cases hprefix : (RecordedQueueRun.run q (rounds.take n)).overflow with
  | false => rfl
  | true =>
      have hsuffix := RecordedQueueRun.execute_after_overflow_preserves q
        ((rounds.drop n).take (v - n)) (RecordedQueueRun.run q (rounds.take n)) hprefix
      have hterminal :
          (RecordedQueueRun.execute q ((rounds.drop n).take (v - n))
            (RecordedQueueRun.run q (rounds.take n))).overflow = false := by
        rw [← RecordedEpisodeStability.run_take_eq_execute_drop q rounds n v hn]
        exact hretain
      rw [hsuffix.1] at hterminal
      cases hterminal

private theorem refreshKernel_bind_toReal
    (p : ConstructorDimensions.Parameters) (q : RecordedQueueRun.Parameters)
    (state : RecordedQueueRun.RunState p.K)
    (round : RecordedQueueRun.RoundInput p.K)
    (anchor : Fin p.K → ℝ) (hanchor : ∀ i, 0 < anchor i)
    (hcap : q.eta ≤ 1 /
      (1024 * (p.m : ℝ) * (p.K : ℝ) *
        (CanonicalRecordingRates.L_stab p : ℝ)))
    (μ : PMF (CanonicalOrientedSetLaw.SlowSet p.K p.m))
    (hactive : RecordedSlowRefresh.proposalProbability p q state round =
      RecordedSlowRefresh.hazard p q)
    (U : CanonicalOrientedSetLaw.SlowSet p.K p.m) :
    ((μ.bind (fun V => RecordedSlowRefresh.recordedRefreshKernel
      p q state round anchor hanchor hcap V)) U).toReal =
      (1 - RecordedSlowRefresh.hazard p q) * (μ U).toReal +
        RecordedSlowRefresh.hazard p q *
          RecordedSlowRefresh.residualMass p q state round anchor hanchor U := by
  have hkernel :
      (fun V => RecordedSlowRefresh.recordedRefreshKernel
        p q state round anchor hanchor hcap V) =
      (fun V => RecordedSlowRefresh.refreshKernel
        (RecordedSlowRefresh.hazard p q)
        (RecordedSlowRefresh.hazard_pos p q).le
        (le_trans (RecordedSlowRefresh.hazard_le_quarter p q hcap) (by norm_num))
        (RecordedSlowRefresh.residualPMF p q state round anchor hanchor) V) := by
    funext V
    unfold RecordedSlowRefresh.recordedRefreshKernel
    simp only [hactive]
  rw [hkernel, RecordedSlowRefresh.refreshKernel_bind_apply]
  rw [RecordedSlowRefresh.residualPMF_apply]
  conv_lhs =>
    rw [← ENNReal.ofReal_toReal (μ.apply_ne_top U)]
  have hle : 0 ≤ 1 - RecordedSlowRefresh.hazard p q := by
    have hquarter := RecordedSlowRefresh.hazard_le_quarter p q hcap
    linarith
  have hnow : 0 ≤ (μ U).toReal := ENNReal.toReal_nonneg
  have hrho : 0 ≤ RecordedSlowRefresh.residualMass p q state round anchor hanchor U :=
    RecordedSlowRefresh.residualMass_nonneg p q state round anchor hanchor U
  have hleft : 0 ≤
      (1 - RecordedSlowRefresh.hazard p q) * (μ U).toReal :=
    mul_nonneg hle hnow
  have hright : 0 ≤
      RecordedSlowRefresh.hazard p q *
        RecordedSlowRefresh.residualMass p q state round anchor hanchor U :=
    mul_nonneg (RecordedSlowRefresh.hazard_pos p q).le hrho
  rw [← ENNReal.ofReal_mul hle, ← ENNReal.ofReal_mul
    (RecordedSlowRefresh.hazard_pos p q).le,
    ← ENNReal.ofReal_add hleft hright]
  rw [ENNReal.toReal_ofReal (add_nonneg hleft hright)]

private theorem windowPrefixPMF_step
    (p : ConstructorDimensions.Parameters) (q : RecordedQueueRun.Parameters)
    (rounds : List (RecordedQueueRun.RoundInput p.K)) (u v : ℕ)
    (hu : 1 ≤ u) (huv : u ≤ v) (hv : v ≤ rounds.length)
    (anchor : Fin p.K → ℝ) (hanchor : ∀ i, 0 < anchor i)
    (hcap : q.eta ≤ 1 /
      (1024 * (p.m : ℝ) * (p.K : ℝ) *
        (CanonicalRecordingRates.L_stab p : ℝ)))
    (n : ℕ) (hn : n < v - u) :
    windowPrefixPMF p q rounds u v hu huv hv anchor hanchor hcap (n + 1) =
      (windowPrefixPMF p q rounds u v hu huv hv anchor hanchor hcap n).bind
        (fun U => RecordedSlowRefresh.recordedRefreshKernel p q
          (RecordedQueueRun.run q (rounds.take (u + n)))
          ((refreshWindowRounds rounds u v)[n]'(by
            rw [refreshWindowRounds_length rounds u v hv]
            exact hn)) anchor hanchor hcap U) := by
  have hlen := refreshWindowRounds_length rounds u v hv
  have hget : n < (refreshWindowRounds rounds u v).length := by rw [hlen]; exact hn
  have htake := List.take_concat_get' (refreshWindowRounds rounds u v) n hget
  have hpathTake : (refreshWindowRounds rounds u v).take n =
      (rounds.drop u).take n := by
    have hle : v - u ≤ rounds.length - u := Nat.sub_le_sub_right hv u
    have hnle : n ≤ rounds.length - u := by omega
    simp [refreshWindowRounds, List.take_take, List.length_drop,
      Nat.min_eq_left hle, Nat.min_eq_left (by omega : n ≤ v - u),
      Nat.min_eq_left hnle]
  unfold windowPrefixPMF
  rw [← htake, refreshPathPMF_append]
  rw [hpathTake]
  have hrun := RecordedEpisodeStability.run_take_eq_execute_drop q rounds u (u + n) (by omega)
  simp only [Nat.add_sub_cancel_left] at hrun
  rw [← hrun]
  simp [refreshPathPMF]

/-- The actual trigger and all subsequent window inputs are active under the
terminal no-overflow trace restriction. Earlier clear states follow from the
absorbing overflow flag of `RecordedQueueRun`; no prefix-state assumption is
supplied. -/
theorem refreshWindow_trace_active
    (p : ConstructorDimensions.Parameters) (q : RecordedQueueRun.Parameters)
    (rounds : List (RecordedQueueRun.RoundInput p.K)) (u v : ℕ)
    (hu : 1 ≤ u) (huv : u ≤ v) (hv : v ≤ rounds.length)
    (htriggerEnabled : (rounds[u - 1]'(by omega)).enabled = true)
    (hwindowEnabled : ∀ (n : ℕ) (hn : n < (refreshWindowRounds rounds u v).length),
      ((refreshWindowRounds rounds u v)[n]'hn).enabled = true)
    (hretain : (RecordedQueueRun.run q (rounds.take v)).overflow = false) :
    RecordedSlowRefresh.proposalProbability p q
        (RecordedQueueRun.run q (rounds.take (u - 1))) rounds[u - 1] =
      RecordedSlowRefresh.hazard p q ∧
    ∀ (n : ℕ) (hn : n < v - u),
      RecordedSlowRefresh.proposalProbability p q
        (RecordedQueueRun.run q (rounds.take (u + n)))
        ((refreshWindowRounds rounds u v)[n]'(by
          rw [refreshWindowRounds_length rounds u v hv]
          exact hn)) = RecordedSlowRefresh.hazard p q := by
  have htriggerClear := run_prefix_overflow_false q rounds v (u - 1) (by omega) hretain
  have htriggerActive := RecordedSlowRefresh.proposalProbability_active p q
    (RecordedQueueRun.run q (rounds.take (u - 1))) rounds[u - 1]
    htriggerClear htriggerEnabled
  constructor
  · exact htriggerActive
  · intro n hn
    have hclear := run_prefix_overflow_false q rounds v (u + n) (by omega) hretain
    have hflag := hwindowEnabled n (by
      rw [refreshWindowRounds_length rounds u v hv]
      exact hn)
    exact RecordedSlowRefresh.proposalProbability_active p q
      (RecordedQueueRun.run q (rounds.take (u + n)))
      ((refreshWindowRounds rounds u v)[n]'(by
        rw [refreshWindowRounds_length rounds u v hv]
        exact hn)) hclear hflag

/-- The trigger PMF is exactly the existing residual PMF at the actual step
from `s_(u-1)`. In particular this includes `v = u`, when no later kernel is
bound. -/
theorem windowPrefixPMF_zero
    (p : ConstructorDimensions.Parameters) (q : RecordedQueueRun.Parameters)
    (rounds : List (RecordedQueueRun.RoundInput p.K)) (u v : ℕ)
    (hu : 1 ≤ u) (huv : u ≤ v) (hv : v ≤ rounds.length)
    (anchor : Fin p.K → ℝ) (hanchor : ∀ i, 0 < anchor i)
    (hcap : q.eta ≤ 1 /
      (1024 * (p.m : ℝ) * (p.K : ℝ) *
        (CanonicalRecordingRates.L_stab p : ℝ))) :
    windowPrefixPMF p q rounds u v hu huv hv anchor hanchor hcap 0 =
      RecordedSlowRefresh.residualPMF p q
        (RecordedQueueRun.run q (rounds.take (u - 1)))
        (rounds[u - 1]'(by omega)) anchor hanchor := by
  simp [windowPrefixPMF, refreshPathPMF]

/-- The constructed finite-window result is a PMF, so it has unit total mass.
No normalization of a conditional or corrected mass is assumed. -/
theorem deferredRefreshWindowPMF_tsum_eq_one
    (p : ConstructorDimensions.Parameters) (q : RecordedQueueRun.Parameters)
    (rounds : List (RecordedQueueRun.RoundInput p.K)) (u v : ℕ)
    (hu : 1 ≤ u) (huv : u ≤ v) (hv : v ≤ rounds.length)
    (anchor : Fin p.K → ℝ) (hanchor : ∀ i, 0 < anchor i)
    (hcap : q.eta ≤ 1 /
      (1024 * (p.m : ℝ) * (p.K : ℝ) *
        (CanonicalRecordingRates.L_stab p : ℝ))) :
    ∑' U : CanonicalOrientedSetLaw.SlowSet p.K p.m,
      deferredRefreshWindowPMF p q rounds u v hu huv hv anchor hanchor hcap U = 1 := by
  exact (deferredRefreshWindowPMF p q rounds u v hu huv hv anchor hanchor hcap).tsum_coe

/-- Every atom of the constructed PMF is nonnegative, including atoms whose
mass is zero. -/
theorem deferredRefreshWindowPMF_apply_nonneg
    (p : ConstructorDimensions.Parameters) (q : RecordedQueueRun.Parameters)
    (rounds : List (RecordedQueueRun.RoundInput p.K)) (u v : ℕ)
    (hu : 1 ≤ u) (huv : u ≤ v) (hv : v ≤ rounds.length)
    (anchor : Fin p.K → ℝ) (hanchor : ∀ i, 0 < anchor i)
    (hcap : q.eta ≤ 1 /
      (1024 * (p.m : ℝ) * (p.K : ℝ) *
        (CanonicalRecordingRates.L_stab p : ℝ)))
    (U : CanonicalOrientedSetLaw.SlowSet p.K p.m) :
    0 ≤ deferredRefreshWindowPMF p q rounds u v hu huv hv anchor hanchor hcap U :=
  bot_le

/-- Exact pointwise real recurrence obtained from the atoms of the actual
refresh kernel. The equality is stated for every slow set, including zero
atoms. -/
private theorem windowPrefixPMF_active_step_toReal
    (p : ConstructorDimensions.Parameters) (q : RecordedQueueRun.Parameters)
    (state : RecordedQueueRun.RunState p.K)
    (round : RecordedQueueRun.RoundInput p.K)
    (anchor : Fin p.K → ℝ) (hanchor : ∀ i, 0 < anchor i)
    (hcap : q.eta ≤ 1 /
      (1024 * (p.m : ℝ) * (p.K : ℝ) *
        (CanonicalRecordingRates.L_stab p : ℝ)))
    (μ : PMF (CanonicalOrientedSetLaw.SlowSet p.K p.m))
    (hactive : RecordedSlowRefresh.proposalProbability p q state round =
      RecordedSlowRefresh.hazard p q)
    (U : CanonicalOrientedSetLaw.SlowSet p.K p.m) :
    ((μ.bind (fun V => RecordedSlowRefresh.recordedRefreshKernel
      p q state round anchor hanchor hcap V)) U).toReal =
      (1 - RecordedSlowRefresh.hazard p q) * (μ U).toReal +
        RecordedSlowRefresh.hazard p q *
          RecordedSlowRefresh.residualMass p q state round anchor hanchor U :=
  refreshKernel_bind_toReal p q state round anchor hanchor hcap μ hactive U

/-- Finite-window deferred collection formula. The source cap supplies
`h = 4 m eta`; actual enabled flags and the terminal retention test supply
every active/clear premise along the bounded path. -/
theorem deferredRefreshWindowPMF_toReal
    (p : ConstructorDimensions.Parameters) (q : RecordedQueueRun.Parameters)
    (rounds : List (RecordedQueueRun.RoundInput p.K)) (u v : ℕ)
    (hu : 1 ≤ u) (huv : u ≤ v) (hv : v ≤ rounds.length)
    (anchor : Fin p.K → ℝ) (hanchor : ∀ i, 0 < anchor i)
    (hcap : q.eta ≤ 1 /
      (1024 * (p.m : ℝ) * (p.K : ℝ) *
        (CanonicalRecordingRates.L_stab p : ℝ)))
    (htriggerEnabled : (rounds[u - 1]'(by omega)).enabled = true)
    (hwindowEnabled : ∀ (n : ℕ) (hn : n < (refreshWindowRounds rounds u v).length),
      ((refreshWindowRounds rounds u v)[n]'hn).enabled = true)
    (hretain : (RecordedQueueRun.run q (rounds.take v)).overflow = false)
    (U : CanonicalOrientedSetLaw.SlowSet p.K p.m) :
    (deferredRefreshWindowPMF p q rounds u v hu huv hv anchor hanchor hcap U).toReal =
      slowMassAt p q rounds anchor hanchor v U +
        (1 - RecordedSlowRefresh.hazard p q) ^ (v - u + 1) /
          RecordedSlowRefresh.hazard p q *
          (slowMassAt p q rounds anchor hanchor u U -
            slowMassAt p q rounds anchor hanchor (u - 1) U) := by
  classical
  let N := v - u
  let path := refreshWindowRounds rounds u v
  let stateAt := fun n =>
    RecordedQueueRun.execute q (path.take n) (RecordedQueueRun.run q (rounds.take u))
  let μActual := fun n =>
    ((windowPrefixPMF p q rounds u v hu huv hv anchor hanchor hcap n) U).toReal
  let pActual := fun n =>
    RecordedSlowRefresh.recordedSlowMass p q (stateAt n) anchor hanchor U
  let h := RecordedSlowRefresh.hazard p q
  let a := 1 - h
  let μFinal := μActual N
  let pFinal := pActual N
  let μSeq : ℕ → ℝ := fun n =>
    if n ≤ N then μActual n else pFinal + a ^ (n - N) * (μFinal - pFinal)
  let pSeq : ℕ → ℝ := fun n => if n ≤ N then pActual n else pFinal
  let ρSeq : ℕ → ℝ := fun n =>
    if hn : n < N then
      RecordedSlowRefresh.residualMass p q (stateAt n) (path[n]'(by
        have hlen : path.length = N := by
          dsimp [path, N]
          exact refreshWindowRounds_length rounds u v hv
        rw [hlen]
        exact hn)) anchor hanchor U
    else pFinal
  let ρPrev :=
    (RecordedSlowRefresh.residualPMF p q
      (RecordedQueueRun.run q (rounds.take (u - 1)))
      (rounds[u - 1]'(by omega)) anchor hanchor U).toReal
  let pPrev := slowMassAt p q rounds anchor hanchor (u - 1) U
  have hN_nonneg : 0 ≤ N := Nat.zero_le _
  have hpathLen : path.length = N := by
    dsimp [path, N]
    exact refreshWindowRounds_length rounds u v hv
  have hpathState (n : ℕ) (hn : n ≤ N) :
      stateAt n = RecordedQueueRun.run q (rounds.take (u + n)) := by
    dsimp [stateAt, path]
    exact windowPrefixState_eq_run q rounds u v n huv hv hn
  have htrace := refreshWindow_trace_active p q rounds u v hu huv hv
    htriggerEnabled hwindowEnabled hretain
  have hstepTrigger :
      RecordedQueueRun.run q (rounds.take u) =
        RecordedQueueRun.step q (RecordedQueueRun.run q (rounds.take (u - 1)))
          rounds[u - 1] := by
    have hsingle : u - (u - 1) = 1 := by omega
    have hpart :=
      RecordedEpisodeStability.run_take_eq_execute_drop q rounds (u - 1) u (by omega)
    have hget := List.take_one_drop_eq_of_lt_length
      (l := rounds) (n := u - 1) (by omega)
    rw [hpart, hsingle, hget]
    rfl
  have htriggerChar := RecordedSlowRefresh.residualMass_characterization p q
    (RecordedQueueRun.run q (rounds.take (u - 1))) rounds[u - 1] anchor hanchor U
  have hρPrev : ρPrev =
      RecordedSlowRefresh.residualMass p q
        (RecordedQueueRun.run q (rounds.take (u - 1))) rounds[u - 1] anchor hanchor U := by
    dsimp [ρPrev]
    rw [RecordedSlowRefresh.residualPMF_apply,
      ENNReal.toReal_ofReal (RecordedSlowRefresh.residualMass_nonneg p q
        (RecordedQueueRun.run q (rounds.take (u - 1))) rounds[u - 1] anchor hanchor U)]
  have hμ0 : μSeq 0 = ρPrev := by
    dsimp [μSeq, μActual, ρPrev, N]
    simp [windowPrefixPMF, refreshPathPMF, path]
  have hp0 : pSeq 0 = slowMassAt p q rounds anchor hanchor u U := by
    dsimp [pSeq, pActual, stateAt, path, N]
    simp [refreshWindowRounds, RecordedQueueRun.execute]
    rfl
  have hpPrev : pPrev = slowMassAt p q rounds anchor hanchor (u - 1) U := rfl
  have htriggerId : h * ρPrev = pSeq 0 - a * pPrev := by
    rw [hρPrev, hp0, hpPrev]
    simp only [slowMassAt]
    rw [hstepTrigger]
    have hchar := htriggerChar
    dsimp [h, a, RecordedSlowRefresh.hazard] at hchar ⊢
    linear_combination hchar
  have hμrec : ∀ n, μSeq (Nat.succ n) = a * μSeq n + h * ρSeq n := by
    intro n
    by_cases hn : n < N
    · have hstep := windowPrefixPMF_step p q rounds u v hu huv hv
        anchor hanchor hcap n hn
      have hsn : n + 1 ≤ N := by omega
      have hstateEq := hpathState n (by omega)
      have hactive := htrace.2 n hn
      have hactivePath : RecordedSlowRefresh.proposalProbability p q
          (stateAt n) (path[n]'(by rw [hpathLen]; exact hn)) = h := by
        rw [hstateEq]
        exact hactive
      have hreal := windowPrefixPMF_active_step_toReal p q (stateAt n)
        (path[n]'(by rw [hpathLen]; exact hn)) anchor hanchor hcap
        (windowPrefixPMF p q rounds u v hu huv hv anchor hanchor hcap n)
        hactivePath U
      have hρ : ρSeq n = RecordedSlowRefresh.residualMass p q (stateAt n)
          (path[n]'(by rw [hpathLen]; exact hn)) anchor hanchor U := by
        simp [ρSeq, hn]
      have hstepPath :
          windowPrefixPMF p q rounds u v hu huv hv anchor hanchor hcap (n + 1) =
            (windowPrefixPMF p q rounds u v hu huv hv anchor hanchor hcap n).bind
              (fun V => RecordedSlowRefresh.recordedRefreshKernel p q (stateAt n)
                (path[n]'(by rw [hpathLen]; exact hn)) anchor hanchor hcap V) := by
        rw [hstep, ← hstateEq]
      rw [← hstepPath] at hreal
      simpa [μSeq, μActual, ρSeq, N, hn, hn.le, hsn, h, a, hρ] using hreal
    · have hNn : N ≤ n := Nat.le_of_not_gt hn
      by_cases hEq : n = N
      · subst n
        have hμsucc' : μSeq (N + 1) = pFinal + a * (μFinal - pFinal) := by
          simp [μSeq, hN_nonneg, show ¬ N + 1 ≤ N by omega, μFinal]
        have hμN' : μSeq N = μFinal := by simp [μSeq, μFinal]
        have hpN' : pSeq N = pFinal := by simp [pSeq, pFinal]
        have hρN' : ρSeq N = pFinal := by simp [ρSeq, N]
        rw [hμsucc', hμN', hρN']
        dsimp [h, a]
        ring
      · have hgt : N < n := lt_of_le_of_ne hNn (Ne.symm hEq)
        have hmuRhs : μSeq (n + 1) =
            pFinal + a ^ (n + 1 - N) * (μFinal - pFinal) := by
          simp [μSeq, not_le_of_gt hgt, not_le_of_gt (by omega : N < n + 1)]
        have hmuHere : μSeq n = pFinal + a ^ (n - N) * (μFinal - pFinal) := by
          simp [μSeq, not_le_of_gt hgt]
        have hpHere : pSeq n = pFinal := by simp [pSeq, not_le_of_gt hgt]
        have hρHere : ρSeq n = pFinal := by simp [ρSeq, not_lt_of_ge hNn]
        rw [hmuRhs, hmuHere, hρHere]
        have hexp : n + 1 - N = (n - N) + 1 := by omega
        rw [hexp, pow_succ]
        dsimp [h, a]
        ring
  have hpRec : ∀ n, pSeq (Nat.succ n) = a * pSeq n + h * ρSeq n := by
    intro n
    by_cases hn : n < N
    · have hsn : n + 1 ≤ N := by omega
      have hstateStep : stateAt (n + 1) =
          RecordedQueueRun.step q (stateAt n) (path[n]'(by rw [hpathLen]; exact hn)) := by
        dsimp [stateAt]
        rw [execute_take_succ_eq_step q path (RecordedQueueRun.run q (rounds.take u)) n
          (by rw [hpathLen]; exact hn)]
      have hchar := RecordedSlowRefresh.residualMass_characterization p q
        (stateAt n) (path[n]'(by rw [hpathLen]; exact hn)) anchor hanchor U
      have hρ : ρSeq n = RecordedSlowRefresh.residualMass p q (stateAt n)
          (path[n]'(by rw [hpathLen]; exact hn)) anchor hanchor U := by
        simp [ρSeq, hn]
      simp only [pSeq, if_pos hsn, if_pos hn.le, pActual]
      rw [hρ, hstateStep]
      dsimp [h, a]
      rw [← hchar]
      ring
    · have hNn : N ≤ n := Nat.le_of_not_gt hn
      by_cases hEq : n = N
      · subst n
        have hpN' : pSeq N = pFinal := by simp [pSeq, pFinal]
        have hpSucc' : pSeq (N + 1) = pFinal := by
          simp [pSeq, show ¬ N + 1 ≤ N by omega]
        have hρ' : ρSeq N = pFinal := by simp [ρSeq, N]
        rw [hpSucc', hpN', hρ']
        dsimp [h, a]
        ring
      · have hgt : N < n := lt_of_le_of_ne hNn (Ne.symm hEq)
        have hpN' : pSeq n = pFinal := by
          simp [pSeq, not_le_of_gt hgt]
        have hpSucc' : pSeq (n + 1) = pFinal := by
          simp [pSeq, not_le_of_gt (by omega : N < n + 1)]
        have hρ' : ρSeq n = pFinal := by simp [ρSeq, not_lt_of_ge hNn]
        rw [hpSucc', hpN', hρ']
        dsimp [h, a]
        ring
  have hmu0' : μSeq 0 = ρPrev := hμ0
  have hha : a = 1 - h := by rfl
  have hhn : h ≠ 0 := (RecordedSlowRefresh.hazard_pos p q).ne'
  have herror := DeferredRecurrence.initialTriggerError μSeq pSeq ρSeq a h
    ρPrev pPrev hμrec hpRec hha hhn hmu0' htriggerId N
  have hmuFinal : μSeq N =
      (deferredRefreshWindowPMF p q rounds u v hu huv hv anchor hanchor hcap U).toReal := by
    dsimp [μSeq, μActual, μFinal, deferredRefreshWindowPMF, windowPrefixPMF]
    simp [N, hN_nonneg]
  have hpFinal : pSeq N = slowMassAt p q rounds anchor hanchor v U := by
    have hstate := hpathState N (by rfl)
    have huvNat : u + N = v := by dsimp [N]; omega
    simp only [pSeq, if_pos (le_rfl : N ≤ N)]
    dsimp [pSeq, pActual, slowMassAt]
    rw [hstate, huvNat]
  have hpZero : pSeq 0 = slowMassAt p q rounds anchor hanchor u U := by
    rw [hp0]
  have hNexp : Nat.succ N = v - u + 1 := by rfl
  have hresult :
      (deferredRefreshWindowPMF p q rounds u v hu huv hv anchor hanchor hcap U).toReal =
        slowMassAt p q rounds anchor hanchor v U +
          (1 - h) ^ (v - u + 1) / h *
            (slowMassAt p q rounds anchor hanchor u U -
              slowMassAt p q rounds anchor hanchor (u - 1) U) := by
    have herror' := herror
    rw [hmuFinal, hpFinal, hpZero, hpPrev, hNexp] at herror'
    simp [h, a] at herror'
    linarith
  simpa [h] using hresult

end Bandits.Support.DeferredRefreshWindow

end
