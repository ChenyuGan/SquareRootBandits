/-
Copyright (c) 2026 Bandits formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.List.Range
public import Mathlib.Data.List.Nodup
public import Bandits.Support.CappedService
public import Bandits.Support.QueueReplay

import Bandits.Support.QueueDrainReplay
import Bandits.Support.QueueTraceConservation
import Lean.Elab.Tactic.Omega

/-!
# Delayed sparse calendar logging and local queue replay

The logging and saved-contribution formulas are transcribed from
`sources/zip4/manuscript/05_binary_transport.tex:352-393,426-431`. The delayed
local scan and queue reconstruction are from
`sources/zip4/manuscript/06_interruptions.tex:194-232`.

This module proves a deterministic finite-calendar construction from explicit
round snapshots. It does not identify those snapshots with a reference
execution, prove assignment correctness or the physical recording law, or
close the manuscript's sparse-recovery lemma.
-/

public section

namespace Bandits.Support.SparseCalendarReplay

/-- A quantized observation in the source interval `[0,1]`. -/
abbrev SparseCalendarReward := Set.Icc (0 : ℝ) 1

/-- A thinning scalar in the source interval `[0,1)`. -/
abbrev SparseCalendarThinScalar := Set.Ico (0 : ℝ) 1

/-- One explicit local calendar snapshot. The function-valued pilot field has
one entry for each of the `d` other players. The flags and values are input
data; this structure does not assert that they came from a protocol run. -/
structure SparseCalendarRound (K d : ℕ) where
  data : Bool
  selectedSource : Bool
  unoccupied : Bool
  active : Bool
  pilot : Fin K
  otherPlayersPilots : Fin d → Fin K
  observation : SparseCalendarReward
  thinScalar : SparseCalendarThinScalar

/-- A saved candidate record stores its calendar round, pilot, reward and thin
scalar. Logging stores these values before any later thinning test. -/
structure SparseCalendarRecord (K : ℕ) where
  calendarRound : ℕ
  pilot : Fin K
  observation : SparseCalendarReward
  thinScalar : SparseCalendarThinScalar

/-- The source mask requires every other player's pilot to differ from this
player's played pilot. -/
@[expose] def sourceMaskPasses {K d : ℕ} (round : SparseCalendarRound K d) : Prop :=
  ∀ player : Fin d, round.otherPlayersPilots player ≠ round.pilot

/-- The exact logging tests: active, unoccupied, DATA, this selected source,
and the source mask. Neither reward positivity nor thinning occurs here. -/
@[expose] def loggingTestsPass {K d : ℕ} (round : SparseCalendarRound K d) : Prop :=
  round.active = true ∧ round.unoccupied = true ∧ round.data = true ∧
    round.selectedSource = true ∧ sourceMaskPasses round

noncomputable local instance {K d : ℕ} (round : SparseCalendarRound K d) :
    Decidable (loggingTestsPass round) := Classical.propDecidable _

/-- The arm-specific logging event adds only the selected pilot test to the
logging tests. -/
@[expose] def loggingTestsPassForArm {K d : ℕ}
    (round : SparseCalendarRound K d) (arm : Fin K) : Prop :=
  loggingTestsPass round ∧ round.pilot = arm

/-- The mask factor `zeta = (1 - 1/K)^d`. -/
@[expose] noncomputable def sparseMaskProbability (K d : ℕ) : ℝ :=
  (1 - (1 : ℝ) / (K : ℝ)) ^ d

/-- Under positive `K` and `d < K`, the mask factor is positive, including the
`K = 1, d = 0` endpoint. -/
theorem sparseMaskProbability_pos (K d : ℕ) (hK : 0 < K) (hd : d < K) :
    0 < sparseMaskProbability K d := by
  by_cases hd0 : d = 0
  · simp [sparseMaskProbability, hd0]
  have hK1 : 1 < K := by omega
  have hKreal : (1 : ℝ) < (K : ℝ) := by exact_mod_cast hK1
  have hKpos : 0 < (K : ℝ) := Nat.cast_pos.mpr hK
  have hfrac : (1 : ℝ) / (K : ℝ) < 1 := by
    exact (div_lt_one hKpos).2 hKreal
  have hbase : 0 < 1 - (1 : ℝ) / (K : ℝ) := sub_pos.mpr hfrac
  exact pow_pos hbase d

/-- One saved candidate's contribution at exponent `h`. The thinning test is
the source's non-strict `v ≤ 4*d*K*2^(-h)/zeta` test, and the stored value is
the literal natural floor. -/
@[expose] noncomputable def savedContribution (K d : ℕ) (D eta : ℝ)
    (h : ℕ) (y : SparseCalendarReward) (v : SparseCalendarThinScalar) : ℕ :=
  if v.1 ≤ (4 * (d : ℝ) * (K : ℝ) * (((2 : ℝ) ^ h)⁻¹)) /
        sparseMaskProbability K d then
    Nat.floor ((D : ℝ) * eta * (2 : ℝ) ^ h * y.1)
  else 0

/-- When the non-strict thinning condition holds, including at equality, the
saved contribution is the floor term. -/
theorem savedContribution_eq_floor_of_le (K d : ℕ) (D eta : ℝ)
    (h : ℕ) (y : SparseCalendarReward) (v : SparseCalendarThinScalar)
    (hv : v.1 ≤ (4 * (d : ℝ) * (K : ℝ) * (((2 : ℝ) ^ h)⁻¹)) /
      sparseMaskProbability K d) :
    savedContribution K d D eta h y v =
      Nat.floor ((D : ℝ) * eta * (2 : ℝ) ^ h * y.1) := by
  simp [savedContribution, hv]

/-- Copy the fields of an eligible calendar round into its candidate record. -/
@[expose] def recordAt {K d : ℕ} (r : ℕ) (round : SparseCalendarRound K d) :
    SparseCalendarRecord K :=
  ⟨r, round.pilot, round.observation, round.thinScalar⟩

/-- The initially empty chronological candidate buffer, formed by appending
exactly once at each calendar round whose logging tests pass. -/
@[expose] noncomputable def sparseCalendarBuffer {K d : ℕ}
    (trace : ℕ → SparseCalendarRound K d) (horizon : ℕ) :
    List (SparseCalendarRecord K) := by
  classical
  exact Nat.rec [] (fun r earlier =>
    earlier ++ if loggingTestsPass (trace r) then [recordAt r (trace r)] else []) horizon

/-- The buffer's one-round append equation. -/
theorem sparseCalendarBuffer_succ {K d : ℕ}
    (trace : ℕ → SparseCalendarRound K d) (horizon : ℕ) :
    sparseCalendarBuffer trace (horizon + 1) =
      sparseCalendarBuffer trace horizon ++
        (if loggingTestsPass (trace horizon) then [recordAt horizon (trace horizon)] else []) := by
  classical
  rfl

/-- Exact membership in the actually constructed buffer. The characterization
contains only calendar membership and the logging tests; it contains no reward
positivity or thinning premise. -/
theorem sparseCalendarBuffer_mem_iff {K d : ℕ}
    (trace : ℕ → SparseCalendarRound K d) (horizon : ℕ)
    (record : SparseCalendarRecord K) :
    record ∈ sparseCalendarBuffer trace horizon ↔
      ∃ r, r < horizon ∧ loggingTestsPass (trace r) ∧ record = recordAt r (trace r) := by
  classical
  induction horizon with
  | zero => simp [sparseCalendarBuffer]
  | succ horizon ih =>
    rw [sparseCalendarBuffer_succ, List.mem_append]
    constructor
    · rintro (h | h)
      · obtain ⟨r, hr, hlog, hrecord⟩ := ih.mp h
        exact ⟨r, Nat.lt_trans hr (Nat.lt_succ_self _), hlog, hrecord⟩
      · by_cases hlog : loggingTestsPass (trace horizon)
        · have hrecord : record = recordAt horizon (trace horizon) := by
            simpa [hlog] using h
          exact ⟨horizon, Nat.lt_succ_self _, hlog, hrecord⟩
        · simp [hlog] at h
    · rintro ⟨r, hr, hlog, hrecord⟩
      by_cases hlt : r < horizon
      · exact Or.inl (ih.mpr ⟨r, hlt, hlog, hrecord⟩)
      · have hrEq : r = horizon := by omega
        subst r
        exact Or.inr (by simp [hlog, hrecord])

/-- Every shorter-horizon buffer is a list prefix of the longer buffer. -/
theorem sparseCalendarBuffer_prefix {K d : ℕ}
    (trace : ℕ → SparseCalendarRound K d) {shorterHorizon horizon : ℕ}
    (hprefix : shorterHorizon ≤ horizon) :
    ∃ suffix, sparseCalendarBuffer trace horizon =
      sparseCalendarBuffer trace shorterHorizon ++ suffix := by
  classical
  induction horizon generalizing shorterHorizon with
  | zero =>
    have : shorterHorizon = 0 := by omega
    subst shorterHorizon
    exact ⟨[], rfl⟩
  | succ horizon ih =>
    by_cases hsmall : shorterHorizon ≤ horizon
    · obtain ⟨suffix, hs⟩ := ih hsmall
      refine ⟨suffix ++ (if loggingTestsPass (trace horizon) then
        [recordAt horizon (trace horizon)] else []), ?_⟩
      rw [sparseCalendarBuffer_succ, hs, List.append_assoc]
    · have hEq : shorterHorizon = horizon + 1 := by omega
      subst shorterHorizon
      exact ⟨[], by simp⟩

/-- Two records constructed in this buffer cannot have the same calendar
round unless the records are equal. -/
theorem sparseCalendarBuffer_unique_round {K d : ℕ}
    (trace : ℕ → SparseCalendarRound K d) (horizon : ℕ)
    {left right : SparseCalendarRecord K}
    (hleft : left ∈ sparseCalendarBuffer trace horizon)
    (hright : right ∈ sparseCalendarBuffer trace horizon)
    (hround : left.calendarRound = right.calendarRound) :
    left = right := by
  classical
  obtain ⟨r, hr, hlog, hleftEq⟩ :=
    (sparseCalendarBuffer_mem_iff trace horizon left).mp hleft
  obtain ⟨s, hs, hlog', hrightEq⟩ :=
    (sparseCalendarBuffer_mem_iff trace horizon right).mp hright
  have hrs : r = s := by simpa [hleftEq, hrightEq, recordAt] using hround
  subst s
  rw [hleftEq, hrightEq]

/-- The constructed buffer has no duplicate entries, so in particular there is
at most one record occurrence at each calendar round. -/
theorem sparseCalendarBuffer_nodup {K d : ℕ}
    (trace : ℕ → SparseCalendarRound K d) (horizon : ℕ) :
    (sparseCalendarBuffer trace horizon).Nodup := by
  classical
  induction horizon with
  | zero => simp [sparseCalendarBuffer]
  | succ horizon ih =>
    by_cases hlog : loggingTestsPass (trace horizon)
    · have hbuffer : sparseCalendarBuffer trace (horizon + 1) =
          sparseCalendarBuffer trace horizon ++ [recordAt horizon (trace horizon)] := by
        rw [sparseCalendarBuffer_succ]
        simp [hlog]
      rw [hbuffer, List.nodup_append']
      refine ⟨ih, by simp, ?_⟩
      rw [List.disjoint_iff_ne]
      intro old hold fresh hfresh
      simp only [List.mem_singleton] at hfresh
      subst fresh
      intro heq
      obtain ⟨r, hr, hlog', hrecord⟩ :=
        (sparseCalendarBuffer_mem_iff trace horizon old).mp hold
      have heqRecord : recordAt r (trace r) = recordAt horizon (trace horizon) :=
        hrecord.symm.trans heq
      have hrEq : r = horizon := by
        have hround := congrArg
          (fun record : SparseCalendarRecord K => record.calendarRound) heqRecord
        simpa [recordAt] using hround
      omega
    · rw [sparseCalendarBuffer_succ]
      simpa [hlog] using ih

/-- The sum over a candidate buffer restricted to one calendar round and arm.
The fold writes the finite sum with zero contributions outside that restriction. -/
@[expose] noncomputable def sparseBufferContribution {K : ℕ}
    (d : ℕ) (D eta : ℝ) (h : ℕ) (arm : Fin K) (r : ℕ)
    (buffer : List (SparseCalendarRecord K)) : ℕ := by
  classical
  exact buffer.foldr (fun record total =>
    (if record.calendarRound = r ∧ record.pilot = arm then
      savedContribution K d D eta h record.observation record.thinScalar else 0) + total) 0

/-- Splitting the finite sum over a concatenated record list splits the
contribution additively. -/
theorem sparseBufferContribution_append {K : ℕ}
    (d : ℕ) (D eta : ℝ) (h : ℕ) (arm : Fin K) (r : ℕ)
    (left right : List (SparseCalendarRecord K)) :
    sparseBufferContribution d D eta h arm r (left ++ right) =
      sparseBufferContribution d D eta h arm r left +
        sparseBufferContribution d D eta h arm r right := by
  classical
  induction left with
  | nil => simp [sparseBufferContribution]
  | cons record left ih =>
    rw [List.cons_append]
    simp only [sparseBufferContribution, List.foldr_cons] at ih ⊢
    rw [ih]
    omega

/-- Contribution reconstructed from the built sparse buffer. -/
@[expose] noncomputable def sparseCalendarArrival {K d : ℕ}
    (trace : ℕ → SparseCalendarRound K d) (horizon : ℕ)
    (D eta : ℝ) (h : ℕ) (arm : Fin K) (r : ℕ) : ℕ :=
  sparseBufferContribution d D eta h arm r (sparseCalendarBuffer trace horizon)

/-- The literal one-round indicator of the logging tests and pilot-arm match,
multiplied by that saved observation's contribution. -/
@[expose] noncomputable def literalCalendarArrival {K d : ℕ}
    (trace : ℕ → SparseCalendarRound K d) (horizon : ℕ)
    (D eta : ℝ) (h : ℕ) (arm : Fin K) (r : ℕ) : ℕ := by
  classical
  exact if r < horizon then
      if loggingTestsPassForArm (trace r) arm then
        savedContribution K d D eta h (trace r).observation (trace r).thinScalar
      else 0
    else 0

/-- The actual-buffer reconstruction equals the literal one-round logging
indicator on every calendar round. -/
theorem sparseCalendarArrival_eq_literal {K d : ℕ}
    (trace : ℕ → SparseCalendarRound K d) (horizon : ℕ)
    (D eta : ℝ) (h : ℕ) (arm : Fin K) (r : ℕ) :
    sparseCalendarArrival trace horizon D eta h arm r =
      literalCalendarArrival trace horizon D eta h arm r := by
  classical
  induction horizon with
  | zero => simp [sparseCalendarArrival, sparseCalendarBuffer,
      sparseBufferContribution, literalCalendarArrival]
  | succ horizon ih =>
    have hrec : sparseCalendarArrival trace (horizon + 1) D eta h arm r =
        sparseCalendarArrival trace horizon D eta h arm r +
          (if loggingTestsPassForArm (trace horizon) arm ∧ horizon = r then
            savedContribution K d D eta h (trace horizon).observation
              (trace horizon).thinScalar else 0) := by
      unfold sparseCalendarArrival
      rw [sparseCalendarBuffer_succ, sparseBufferContribution_append]
      by_cases hlog : loggingTestsPass (trace horizon)
      · simp [hlog, sparseBufferContribution, loggingTestsPassForArm, recordAt,
          and_comm]
      · simp [hlog, sparseBufferContribution, loggingTestsPassForArm]
    rw [hrec, ih]
    by_cases hlt : r < horizon
    · have hltSucc : r < horizon + 1 := by omega
      have hne : horizon ≠ r := by omega
      simp [literalCalendarArrival, hlt, hltSucc, hne]
    · by_cases heq : r = horizon
      · subst r
        simp [literalCalendarArrival]
      · have hgt : horizon < r := by omega
        have hnot : ¬ r < horizon + 1 := by omega
        have hne : horizon ≠ r := by omega
        simp [literalCalendarArrival, hlt, hnot, hne]

/-- The interval `[sigma, ell)` as a chronological list of calendar rounds. -/
@[expose] def sparseCalendarRounds (sigma ell : ℕ) : List ℕ :=
  (List.range (ell - sigma)).map (sigma + ·)

/-- When the interval is nonempty, its final calendar round is `ell - 1`. -/
theorem sparseCalendarRounds_append_last {sigma ell : ℕ} (h : sigma < ell) :
    sparseCalendarRounds sigma ell =
      sparseCalendarRounds sigma (ell - 1) ++ [ell - 1] := by
  cases ell with
  | zero => omega
  | succ ell =>
    have hsigma : sigma ≤ ell := by omega
    simp [sparseCalendarRounds, Nat.succ_sub hsigma, List.range_succ,
      Nat.add_sub_of_le hsigma]

/-- The interval list contains exactly `ell - sigma` calendar rounds. -/
theorem sparseCalendarRounds_length (sigma ell : ℕ) :
    (sparseCalendarRounds sigma ell).length = ell - sigma := by
  simp [sparseCalendarRounds]

/-- The chronological one-round arrivals scanned directly from the literal
logging tests. -/
@[expose] noncomputable def sparseDirectArrivalScan {K d : ℕ}
    (trace : ℕ → SparseCalendarRound K d) (horizon : ℕ)
    (D eta : ℝ) (h : ℕ) (arm : Fin K) (sigma ell : ℕ) : List ℕ :=
  (sparseCalendarRounds sigma ell).map
    (literalCalendarArrival trace horizon D eta h arm)

/-- The chronological arrivals reconstructed by summing the actually built
buffer at each calendar round. -/
@[expose] noncomputable def sparseBufferedArrivalScan {K d : ℕ}
    (trace : ℕ → SparseCalendarRound K d) (horizon : ℕ)
    (D eta : ℝ) (h : ℕ) (arm : Fin K) (sigma ell : ℕ) : List ℕ :=
  (sparseCalendarRounds sigma ell).map
    (sparseCalendarArrival trace horizon D eta h arm)

/-- The delayed sparse scan equals the directly constructed chronological
one-round scan. -/
theorem sparseBufferedArrivalScan_eq_direct {K d : ℕ}
    (trace : ℕ → SparseCalendarRound K d) (horizon : ℕ)
    (D eta : ℝ) (h : ℕ) (arm : Fin K) (sigma ell : ℕ) :
    sparseBufferedArrivalScan trace horizon D eta h arm sigma ell =
      sparseDirectArrivalScan trace horizon D eta h arm sigma ell := by
  unfold sparseBufferedArrivalScan sparseDirectArrivalScan
  apply List.map_congr_left
  intro r hr
  exact sparseCalendarArrival_eq_literal trace horizon D eta h arm r

/-- Feed every scanned calendar round to the queue as an enabled record. -/
@[expose] noncomputable def sparseCalendarQueueRecords {K d : ℕ}
    (trace : ℕ → SparseCalendarRound K d) (horizon : ℕ)
    (D eta : ℝ) (h : ℕ) (arm : Fin K) (sigma ell : ℕ) :
    List (Bool × ℕ) :=
  (sparseBufferedArrivalScan trace horizon D eta h arm sigma ell).map
    (fun arrival => (true, arrival))

/-- Queue records from the literal direct arrival scan. -/
@[expose] noncomputable def sparseDirectQueueRecords {K d : ℕ}
    (trace : ℕ → SparseCalendarRound K d) (horizon : ℕ)
    (D eta : ℝ) (h : ℕ) (arm : Fin K) (sigma ell : ℕ) :
    List (Bool × ℕ) :=
  (sparseDirectArrivalScan trace horizon D eta h arm sigma ell).map
    (fun arrival => (true, arrival))

/-- Every calendar round, including a round with no saved candidate, remains
as an enabled queue record. -/
theorem sparseCalendarQueueRecords_all_enabled {K d : ℕ}
    (trace : ℕ → SparseCalendarRound K d) (horizon : ℕ)
    (D eta : ℝ) (h : ℕ) (arm : Fin K) (sigma ell : ℕ) :
    ∀ record ∈ sparseCalendarQueueRecords trace horizon D eta h arm sigma ell,
      record.1 = true := by
  intro record hrecord
  rcases List.mem_map.mp hrecord with ⟨arrival, _, rfl⟩
  rfl

/-- The local queue has one enabled record per calendar round in `[sigma,ell)`,
regardless of whether any candidate was logged on that round. -/
theorem sparseCalendarQueueRecords_length {K d : ℕ}
    (trace : ℕ → SparseCalendarRound K d) (horizon : ℕ)
    (D eta : ℝ) (h : ℕ) (arm : Fin K) (sigma ell : ℕ) :
    (sparseCalendarQueueRecords trace horizon D eta h arm sigma ell).length =
      ell - sigma := by
  simp [sparseCalendarQueueRecords, sparseBufferedArrivalScan, sparseCalendarRounds]

/-- The cast of the capacity `4*n` equals `4*eta*D` when the source integer
scale satisfies `eta*D = n`. The product equality stays an explicit input. -/
theorem sparseQueueCapacity_cast_eq_of_product (D eta : ℝ) (n : ℕ)
    (hproduct : eta * (D : ℝ) = (n : ℝ)) :
    ((4 * n : ℕ) : ℝ) = 4 * eta * (D : ℝ) := by
  calc
    ((4 * n : ℕ) : ℝ) = 4 * (n : ℝ) := by simp
    _ = 4 * (eta * (D : ℝ)) := by rw [hproduct]
    _ = 4 * eta * (D : ℝ) := by rw [mul_assoc]

/-- Positive `D` and `eta`, together with the exact product witness, imply the
positive integer scale required by the local queue. -/
theorem sparseQueueScale_pos_of_product (D eta : ℝ) (n : ℕ)
    (hD : 0 < D) (heta : 0 < eta)
    (hproduct : eta * (D : ℝ) = (n : ℝ)) : 0 < n := by
  have hnReal : 0 < (n : ℝ) := by
    rw [← hproduct]
    exact mul_pos heta hD
  exact Nat.cast_pos.mp hnReal

/-- The enabled local replay with capacity `4*n`, score zero and initial
backlog `q`. The replay takes `n` explicitly. The product identity is kept as
the separate application theorem `sparseQueueCapacity_cast_eq_of_product`. -/
@[expose] noncomputable def sparseCalendarQueueReplay {K d : ℕ}
    (trace : ℕ → SparseCalendarRound K d) (horizon : ℕ)
    (D eta : ℝ) (h n : ℕ) (arm : Fin K) (sigma ell q : ℕ) : ℕ × ℕ :=
  Bandits.Support.QueueReplay.replay (4 * n) (0, q)
    (sparseCalendarQueueRecords trace horizon D eta h arm sigma ell)

/-- The sparse-buffer queue and the queue driven by the direct one-round scan
have exactly the same replay state. -/
theorem sparseCalendarQueueReplay_eq_direct {K d : ℕ}
    (trace : ℕ → SparseCalendarRound K d) (horizon : ℕ)
    (D eta : ℝ) (h n : ℕ) (arm : Fin K) (sigma ell q : ℕ) :
    sparseCalendarQueueReplay trace horizon D eta h n arm sigma ell q =
      Bandits.Support.QueueReplay.replay (4 * n) (0, q)
        (sparseDirectQueueRecords trace horizon D eta h arm sigma ell) := by
  unfold sparseCalendarQueueReplay sparseCalendarQueueRecords sparseDirectQueueRecords
  rw [sparseBufferedArrivalScan_eq_direct]

/-- Appending the last live calendar round appends one enabled record, even
when its buffer-derived arrival is zero. -/
theorem sparseCalendarQueueRecords_append_last {K d : ℕ}
    (trace : ℕ → SparseCalendarRound K d) (horizon : ℕ)
    (D eta : ℝ) (h : ℕ) (arm : Fin K) (sigma ell : ℕ)
    (hnonempty : sigma < ell) :
    sparseCalendarQueueRecords trace horizon D eta h arm sigma ell =
      sparseCalendarQueueRecords trace horizon D eta h arm sigma (ell - 1) ++
        [(true, sparseCalendarArrival trace horizon D eta h arm (ell - 1))] := by
  unfold sparseCalendarQueueRecords sparseBufferedArrivalScan
  rw [sparseCalendarRounds_append_last hnonempty]
  simp only [List.map_append, List.map_singleton]

/-- Queue score plus terminal backlog equals the initial queue plus the exact
sum of the directly scanned one-round arrivals. Thus the score coordinate is
the total service accumulated by `QueueReplay`. -/
theorem sparseCalendarQueueReplay_conservation {K d : ℕ}
    (trace : ℕ → SparseCalendarRound K d) (horizon : ℕ)
    (D eta : ℝ) (h n : ℕ) (arm : Fin K) (sigma ell q : ℕ) :
    (sparseCalendarQueueReplay trace horizon D eta h n arm sigma ell q).1 +
        (sparseCalendarQueueReplay trace horizon D eta h n arm sigma ell q).2 =
      q + (sparseDirectArrivalScan trace horizon D eta h arm sigma ell).sum := by
  rw [sparseCalendarQueueReplay_eq_direct]
  have harrival :
      (sparseDirectQueueRecords trace horizon D eta h arm sigma ell |>.map
        Bandits.Support.QueueTraceConservation.acceptedArrival).sum =
      (sparseDirectArrivalScan trace horizon D eta h arm sigma ell).sum := by
    unfold sparseDirectQueueRecords
    rw [List.map_map]
    change ((sparseDirectArrivalScan trace horizon D eta h arm sigma ell).map
      (fun arrival => Bandits.Support.QueueTraceConservation.acceptedArrival
        (true, arrival))).sum = _
    simp [Bandits.Support.QueueTraceConservation.acceptedArrival]
  have hcon := Bandits.Support.QueueTraceConservation.replay_score_add_backlog
    (4 * n) (0, q) (sparseDirectQueueRecords trace horizon D eta h arm sigma ell)
  rw [Nat.zero_add, harrival] at hcon
  exact hcon

/-- The terminal backlog is exactly initial backlog plus scanned arrivals
minus the accumulated service score. -/
theorem sparseCalendarQueueReplay_terminal_backlog {K d : ℕ}
    (trace : ℕ → SparseCalendarRound K d) (horizon : ℕ)
    (D eta : ℝ) (h n : ℕ) (arm : Fin K) (sigma ell q : ℕ) :
    (sparseCalendarQueueReplay trace horizon D eta h n arm sigma ell q).2 =
      q + (sparseDirectArrivalScan trace horizon D eta h arm sigma ell).sum -
        (sparseCalendarQueueReplay trace horizon D eta h n arm sigma ell q).1 := by
  have hcon := sparseCalendarQueueReplay_conservation trace horizon D eta h n
    arm sigma ell q
  omega

/-- Appending a disabled collection round anywhere in a replay preserves the
registers. This remains separate from the all-enabled live local interval. -/
theorem sparseCalendarQueueReplay_disabled_insert (capacity : ℕ)
    (initial : ℕ × ℕ) (before after : List (Bool × ℕ)) (arrival : ℕ) :
    Bandits.Support.QueueReplay.replay capacity initial
        (before ++ (false, arrival) :: after) =
      Bandits.Support.QueueReplay.replay capacity initial (before ++ after) :=
  Bandits.Support.QueueDrainReplay.replay_insert_disabled
    capacity initial before after arrival

/-- A missing local record contributes zero, but its calendar round still
performs the enabled zero-arrival queue update. -/
theorem sparseCalendarQueueReplay_missing_record_step {K d : ℕ}
    (trace : ℕ → SparseCalendarRound K d) (horizon : ℕ)
    (D eta : ℝ) (h n : ℕ) (arm : Fin K) (r score backlog : ℕ)
    (hr : r < horizon) (hmiss : ¬ loggingTestsPassForArm (trace r) arm) :
    Bandits.Support.QueueReplay.transition (4 * n) (score, backlog)
        (true, sparseCalendarArrival trace horizon D eta h arm r) =
      (score + Bandits.Support.CappedService.service (4 * n) backlog 0,
        Bandits.Support.CappedService.residual (4 * n) backlog 0) := by
  classical
  rw [sparseCalendarArrival_eq_literal trace horizon D eta h arm r]
  simp [literalCalendarArrival, hr, hmiss]
  exact Bandits.Support.QueueDrainReplay.transition_zero_arrival_eq_capped
    (4 * n) score backlog

/-- Splitting an enabled local queue interval at its final calendar round
exposes exactly that round's service and residual backlog. -/
theorem sparseCalendarQueueReplay_last_round {K d : ℕ}
    (trace : ℕ → SparseCalendarRound K d) (horizon : ℕ)
    (D eta : ℝ) (h n : ℕ) (arm : Fin K) (sigma ell q : ℕ)
    (hnonempty : sigma < ell) :
    Bandits.Support.QueueReplay.replay (4 * n) (0, q)
        (sparseCalendarQueueRecords trace horizon D eta h arm sigma ell) =
      let before := Bandits.Support.QueueReplay.replay (4 * n) (0, q)
        (sparseCalendarQueueRecords trace horizon D eta h arm sigma (ell - 1))
      (before.1 + Bandits.Support.CappedService.service (4 * n) before.2
          (sparseCalendarArrival trace horizon D eta h arm (ell - 1)),
        Bandits.Support.CappedService.residual (4 * n) before.2
          (sparseCalendarArrival trace horizon D eta h arm (ell - 1))) := by
  dsimp
  rw [sparseCalendarQueueRecords_append_last trace horizon D eta h arm sigma ell hnonempty]
  rw [Bandits.Support.QueueReplay.replay_append]
  rfl

end Bandits.Support.SparseCalendarReplay

end
