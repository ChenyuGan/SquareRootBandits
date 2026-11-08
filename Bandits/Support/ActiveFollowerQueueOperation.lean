/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ActiveRoundActions
public import Bandits.Support.CanonicalRecordingRates
public import Bandits.Support.CanonicalRecordingSlice
public import Bandits.Support.CappedService
public import Bandits.Support.CompletePublicTable
public import Bandits.Support.OrdinaryMessageCodec
public import Bandits.Support.PrelaunchBufferRecovery
public import Bandits.Support.PublicDiscreteDraws
public import Bandits.Support.QueueReplay
public import Bandits.Support.ReferencePrelaunchFollower
public import Bandits.Support.SparseCalendarReplay

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# One local occupied-follower service operation

The local UP offer and the post-feedback queue-service update follow
`sources/zip4/manuscript/06_interruptions.tex:108-114,256-269`,
`sources/zip4/manuscript/05_binary_transport.tex:352-393`,
`sources/zip4/manuscript/04_slow_fast_learner.tex:157-174`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:8-14`.

This module consumes the existing follower registers and row. It does not
log a candidate, decode or accept a DOWN record, recover a queue, release an
assignment, construct a physical history, or certify global reachability.
Every source-local queue-domain check is an explicit branch of the checked
operation. In particular, this operation's failure result is not the existing
initialization-failure monitor.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ActiveFollowerQueueOperation

open Bandits.Support.ConstructorDimensions
open Bandits.Support.CompletePublicTable
open Bandits.Support.ContinuousControlSlice
open Bandits.Support.ActiveRoundActions
open Bandits.Support.OrdinaryMessageCodec
open Bandits.Support.PublicDiscreteDraws
open Bandits.Support.ReferencePrelaunchFollower
open Bandits.Support.SparseCalendarReplay
open Classical

/-- The source cap on the positive learning rate used by local service.
Source: `04_slow_fast_learner.tex:98-101`. -/
def sourceRateCapped (p : Parameters) (eta : LearningRate) : Prop :=
  eta.val ≤ 1 / (1024 * (p.m : ℝ) * (p.K : ℝ) *
    (CanonicalRecordingRates.L_stab p : ℝ))

/-- The source's follower thinning probability when the accepted record's
assigned arm is played with conditional probability one. -/
def thinningProbability {p : Parameters} (eta : LearningRate)
    (M : DownRecord (codecParams p eta)) : ℝ :=
  (4 * ((p.m - 1 : ℕ) : ℝ) * dyadicRate M.val.h) /
    sparseMaskProbability p.K (p.m - 1)

/-- Every occupied record carries an in-domain thinning probability. This
explicitly checks the source's Bernoulli parameter and does not clip it. -/
def thinningProbabilityDomain {p : Parameters} (eta : LearningRate)
    (M : DownRecord (codecParams p eta)) : Prop :=
  0 < sparseMaskProbability p.K (p.m - 1) ∧
  0 < dyadicRate M.val.h ∧
  0 ≤ thinningProbability eta M ∧
  thinningProbability eta M ≤ 1

/-- The exact occupied-follower DATA/source/arm-mask/inclusive-thinning gate.
The mask is evaluated against every other public pilot, while the selected
arm is the accepted DOWN arm. -/
def recorderGate {p : Parameters} (eta : LearningRate)
    (i : Fin (p.m - 1)) (row : CompleteRow p) (t : Fin p.T)
    (M : DownRecord (codecParams p eta)) : Prop :=
  let slice := (row.2 t).1
  slotDraw slice = dataSlot ∧
  recorderSourceDraw p.two_le_m p.m_lt_K slice =
    followerPlayer p.two_le_m i ∧
  CanonicalRecordingSlice.recordingMask (K_pos p)
    (followerPlayer p.two_le_m i) (PrelaunchBufferRecovery.downArm eta M) slice ∧
  (coordinate Label.thin slice).val ≤ thinningProbability eta M

/-- The requested literal integer floor `floor(D eta Y / 2^(-h))`. -/
def sourceArrivalFloor {p : Parameters} (eta : LearningRate)
    (M : DownRecord (codecParams p eta)) (y : Observation p) : ℕ :=
  Nat.floor ((D p : ℝ) * eta.val * y.val.1 / dyadicRate M.val.h)

/-- A passing occupied-follower gate uses the existing sparse saved-contribution
calculation. Its wider pilot gate is shown below to be satisfied by the exact
occupied-follower gate before this value is used. -/
def rawArrival {p : Parameters} (eta : LearningRate)
    (i : Fin (p.m - 1)) (row : CompleteRow p) (t : Fin p.T)
    (M : DownRecord (codecParams p eta)) (y : Observation p) : ℕ := by
  classical
  exact if recorderGate eta i row t M then
    SparseCalendarReplay.savedContribution p.K (p.m - 1) (D p) eta.val M.val.h
      y.val ((coordinate Label.thin (row.2 t).1))
  else 0

/-- A raw follower-buffer key is a one-based calendar round and the pilot arm
recorded on that round. -/
def bufferKey {K : ℕ} (record : SparseCalendarRecord K) : ℕ × Fin K :=
  (record.calendarRound, record.pilot)

/-- The explicit appendix-A input domain for an existing follower state. Typed
records supply their arm/reward/scalar bounds; this checks all natural
register, timestamp, and one-record-per-arm-and-round restrictions. -/
def stateInputDomain {p : Parameters} {eta : LearningRate}
    (s : State p eta) : Prop :=
  s.S ≤ p.T * D p ∧ s.delta ≤ D p ∧ s.backlog ≤ p.T * D p ∧
    (∀ record ∈ s.buffer, 1 ≤ record.calendarRound ∧
      record.calendarRound ≤ p.T) ∧
    (s.buffer.map bufferKey).Nodup

/-- Source queue capacity corresponding to the supplied natural `n = eta D`. -/
def serviceCapacity (n : ℕ) : ℕ := 4 * n

/-- The constructed score/backlog output domain checked before storing it. -/
def outputDomain {p : Parameters} (n : ℕ) {eta : LearningRate}
    (s : State p eta) (arrival service : ℕ) : Prop :=
  arrival ≤ D p ∧ service ≤ D p ∧ s.S + service ≤ p.T * D p ∧
    CappedService.residual (serviceCapacity n) s.backlog arrival ≤ p.T * D p

/-- The capped service amount on one enabled calendar round. -/
def localService (n backlog arrival : ℕ) : ℕ :=
  CappedService.service (serviceCapacity n) backlog arrival

/-- Update only `(S, delta, backlog)` on an occupied service round. -/
def serviceUpdate {p : Parameters} {eta : LearningRate}
    (n : ℕ) (s : State p eta) (arrival : ℕ) : State p eta :=
  let service := localService n s.backlog arrival
  { s with
    S := s.S + service
    delta := service
    backlog := CappedService.residual (serviceCapacity n) s.backlog arrival }

/-- The state returned by an enabled occupied round, or the unchanged state
when local service is disabled for an unoccupied follower. -/
noncomputable def serviceOutput {p : Parameters} {eta : LearningRate}
    (n : ℕ) (s : State p eta) (arrival : ℕ) : State p eta :=
  by
    classical
    exact if s.status.occupied then serviceUpdate n s arrival else s

/-- The successful service result records which local branch ran and the
arrival/service values computed by that branch. -/
def serviceAction {p : Parameters} (eta : LearningRate) (n : ℕ)
    (i : Fin (p.m - 1)) (row : CompleteRow p) (alpha : Activation p)
    (t : Fin p.T) (observation : Observation p) (input : State p eta)
    (arrival service : ℕ) : Prop :=
  match input.status with
  | .unoccupied => arrival = 0 ∧ service = 0
  | .pending =>
      alpha.val ≤ t.val + 1 ∧ ∃ M, input.lastDown = some M ∧
        thinningProbabilityDomain eta M ∧
        arrival = rawArrival eta i row t M observation ∧
        service = localService n input.backlog arrival
  | .released =>
      alpha.val ≤ t.val + 1 ∧ ∃ M, input.lastDown = some M ∧
        thinningProbabilityDomain eta M ∧
        arrival = rawArrival eta i row t M observation ∧
        service = localService n input.backlog arrival

/-- The successful service result carries the checked input and output bounds.
Failure is kept separate from `initializationFailure` in the follower state. -/
structure ServiceSuccess (p : Parameters) (eta : LearningRate) (n : ℕ)
    (i : Fin (p.m - 1)) (row : CompleteRow p) (alpha : Activation p)
    (t : Fin p.T) (observation : Observation p) (input : State p eta) where
  output : State p eta
  arrival : ℕ
  service : ℕ
  inputDomain : stateInputDomain input
  sourceRateCap : sourceRateCapped p eta
  naturalScale : (n : ℝ) = eta.val * (D p : ℝ)
  arrival_le_D : arrival ≤ D p
  service_le_D : service ≤ D p
  score_le_TD : output.S ≤ p.T * D p
  backlog_le_TD : output.backlog ≤ p.T * D p
  queueUpdate : output = serviceOutput n input arrival
  action : serviceAction eta n i row alpha t observation input arrival service

/-- A failed domain check, or a successful checked local queue update. -/
inductive ServiceResult (p : Parameters) (eta : LearningRate) (n : ℕ)
    (i : Fin (p.m - 1)) (row : CompleteRow p) (alpha : Activation p)
    (t : Fin p.T) (observation : Observation p) (input : State p eta) where
  | failure
  | success (result : ServiceSuccess p eta n i row alpha t observation input)

/-- The exact DATA recorder arrival for the current occupied DOWN arm. -/
def checkedService {p : Parameters} (eta : LearningRate)
    (hcap : sourceRateCapped p eta) (n : ℕ)
    (hn : (n : ℝ) = eta.val * (D p : ℝ))
    (i : Fin (p.m - 1)) (row : CompleteRow p) (alpha : Activation p)
    (t : Fin p.T) (observation : Observation p) (s : State p eta) :
    ServiceResult p eta n i row alpha t observation s := by
  classical
  if hdomain : stateInputDomain s then
    match hstatus : s.status with
    | .unoccupied =>
        exact .success ⟨s, 0, 0, hdomain, hcap, hn, by omega, by omega,
          hdomain.1, hdomain.2.2.1,
          by simp [serviceOutput, FollowerStatus.occupied, hstatus],
          by simp [serviceAction, hstatus]⟩
    | .pending =>
        if hactive : alpha.val ≤ t.val + 1 then
          match hlast : s.lastDown with
          | none => exact .failure
          | some M =>
              if hthin : thinningProbabilityDomain eta M then
                let arrival := rawArrival eta i row t M observation
                let service := localService n s.backlog arrival
                let output := serviceOutput n s arrival
                if hout : outputDomain n s arrival service then
                  refine .success ⟨output, arrival, service, hdomain, hcap, hn, hout.1,
                    hout.2.1,
                    ?_, ?_,
                    rfl, ?_⟩
                  · have hscore : output.S = s.S + service := by
                      dsimp [output]
                      simp only [serviceOutput, FollowerStatus.occupied, hstatus]
                      rfl
                    rw [hscore]
                    exact hout.2.2.1
                  · have hbacklog : output.backlog =
                        CappedService.residual (serviceCapacity n) s.backlog arrival := by
                      dsimp [output]
                      simp only [serviceOutput, FollowerStatus.occupied, hstatus]
                      rfl
                    rw [hbacklog]
                    exact hout.2.2.2
                  · unfold serviceAction
                    rw [hstatus]
                    exact ⟨hactive, M, hlast, hthin, rfl, rfl⟩
                else exact .failure
              else exact .failure
        else exact .failure
    | .released =>
        if hactive : alpha.val ≤ t.val + 1 then
          match hlast : s.lastDown with
          | none => exact .failure
          | some M =>
              if hthin : thinningProbabilityDomain eta M then
                let arrival := rawArrival eta i row t M observation
                let service := localService n s.backlog arrival
                let output := serviceOutput n s arrival
                if hout : outputDomain n s arrival service then
                  refine .success ⟨output, arrival, service, hdomain, hcap, hn, hout.1,
                    hout.2.1,
                    ?_, ?_,
                    rfl, ?_⟩
                  · have hscore : output.S = s.S + service := by
                      dsimp [output]
                      simp only [serviceOutput, FollowerStatus.occupied, hstatus]
                      rfl
                    rw [hscore]
                    exact hout.2.2.1
                  · have hbacklog : output.backlog =
                        CappedService.residual (serviceCapacity n) s.backlog arrival := by
                      dsimp [output]
                      simp only [serviceOutput, FollowerStatus.occupied, hstatus]
                      rfl
                    rw [hbacklog]
                    exact hout.2.2.2
                  · unfold serviceAction
                    rw [hstatus]
                    exact ⟨hactive, M, hlast, hthin, rfl, rfl⟩
                else exact .failure
              else exact .failure
        else exact .failure
  else exact .failure

/-- The register tuple offered on an eligible UP round is read from the
incoming follower state, including its existing accepted start. -/
def upOfferFields {p : Parameters} {eta : LearningRate}
    (s : State p eta) : UpFields :=
  ⟨acceptedStart s, s.S, s.delta, s.backlog⟩

/-- The public row selects this active follower for an UP message. -/
def selectedUpRound {p : Parameters} (i : Fin (p.m - 1))
    (row : CompleteRow p) (alpha : Activation p) (t : Fin p.T) : Prop :=
  alpha.val ≤ t.val + 1 ∧
  slotDraw (row.2 t).1 = upSlot ∧
  selectedFollowerDraw p.two_le_m p.m_lt_K (row.2 t).1 = i

/-- A checked offer result distinguishes an ineligible empty offer from a
source-domain failure. -/
inductive UpOfferResult (p : Parameters) (eta : LearningRate) where
  | failure
  | noOffer
  | offer (record : UpRecord (codecParams p eta))

/-- Construct the local offer at arm choice. Its four fields are checked by
the existing UP record predicate; an inadmissible selected offer is failure. -/
def checkedUpOffer {p : Parameters} (eta : LearningRate)
    (i : Fin (p.m - 1)) (row : CompleteRow p) (alpha : Activation p)
    (t : Fin p.T) (s : State p eta) : UpOfferResult p eta := by
  classical
  if hdomain : stateInputDomain s then
    if hselected : selectedUpRound i row alpha t ∧ s.status = .unoccupied then
      if hadm : upAdmissible (codecParams p eta) (upOfferFields s) then
        let record : UpRecord (codecParams p eta) := ⟨upOfferFields s, hadm⟩
        exact .offer record
      else exact .failure
    else exact .noOffer
  else exact .failure

/-- The exact current thinning test is no larger than the existing saved
pilot-contribution test. `K` is at least one and the common mask denominator
is positive. -/
theorem thinningProbability_le_savedThreshold {p : Parameters}
    (eta : LearningRate)
    (M : DownRecord (codecParams p eta)) :
    thinningProbability eta M ≤
      (4 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ) * dyadicRate M.val.h) /
        sparseMaskProbability p.K (p.m - 1) := by
  have hzeta : 0 < sparseMaskProbability p.K (p.m - 1) := by
    have hmk : p.m < p.K := p.m_lt_K
    exact SparseCalendarReplay.sparseMaskProbability_pos p.K (p.m - 1)
      (K_pos p) (by omega)
  have hK : (1 : ℝ) ≤ (p.K : ℝ) := by
    have hm := p.two_le_m
    have hmk := p.m_lt_K
    exact_mod_cast (show 1 ≤ p.K by omega)
  have hrate : 0 < dyadicRate M.val.h := by
    unfold dyadicRate
    positivity
  have hnum : 0 ≤ 4 * ((p.m - 1 : ℕ) : ℝ) * dyadicRate M.val.h := by
    positivity
  rw [thinningProbability, div_le_div_iff₀ hzeta hzeta]
  nlinarith [mul_nonneg hnum (sub_nonneg.mpr hK)]

/-- Any DOWN record's literal thinning probability lies in `[0,1]`; this is
derived from the codec admissibility bound and the canonical mask bound. -/
theorem thinningProbability_domain {p : Parameters}
    (eta : LearningRate) (M : DownRecord (codecParams p eta)) :
    thinningProbabilityDomain eta M := by
  rcases M.property with ⟨_, _, _, _, _, _, _, _, _, hxi, _⟩
  have hzeta : (1 / 4 : ℝ) < sparseMaskProbability p.K (p.m - 1) := by
    calc
      (1 / 4 : ℝ) < CanonicalRecordingSlice.recordingZeta p.m p.K :=
        CanonicalRecordingSlice.recordingZeta_gt_quarter p.two_le_m p.m_lt_K
      _ = sparseMaskProbability p.K (p.m - 1) :=
        CanonicalRecordingSlice.recordingZeta_eq_sparseMaskProbability p.m p.K
  have hzetaPos : 0 < sparseMaskProbability p.K (p.m - 1) :=
    lt_trans (by norm_num) hzeta
  have hxiPos : 0 < dyadicRate M.val.h := by
    unfold dyadicRate
    positivity
  have hd_le : ((p.m - 1 : ℕ) : ℝ) ≤ (p.m : ℝ) := by
    exact_mod_cast Nat.sub_le p.m 1
  have hmK : (p.m : ℝ) ≤ (p.m : ℝ) * (p.K : ℝ) := by
    have hK : (1 : ℝ) ≤ (p.K : ℝ) := by
      have hm := p.two_le_m
      have hmk := p.m_lt_K
      exact_mod_cast (show 1 ≤ p.K by omega)
    nlinarith [mul_nonneg (sub_nonneg.mpr hK) (show 0 ≤ (p.m : ℝ) by positivity)]
  have hnum :
      4 * ((p.m - 1 : ℕ) : ℝ) * dyadicRate M.val.h ≤ 1 / 4 := by
    have hxi' : dyadicRate M.val.h ≤
        1 / (16 * (p.m : ℝ) * (p.K : ℝ)) := by
      simpa [codecParams, D] using hxi
    have hmPos : 0 < (p.m : ℝ) := by exact_mod_cast m_pos p
    have hKPos : 0 < (p.K : ℝ) := by exact_mod_cast K_pos p
    have hden : 0 < 16 * (p.m : ℝ) * (p.K : ℝ) := by positivity
    have hsmall :
        4 * ((p.m - 1 : ℕ) : ℝ) *
            (1 / (16 * (p.m : ℝ) * (p.K : ℝ))) ≤ 1 / 4 := by
      field_simp [ne_of_gt hden]
      nlinarith [hd_le, hmK]
    exact (mul_le_mul_of_nonneg_left hxi' (by positivity)).trans hsmall
  have hthinNonneg : 0 ≤ thinningProbability eta M := by
    unfold thinningProbability
    positivity
  have hthinLe : thinningProbability eta M ≤ 1 := by
    unfold thinningProbability
    exact (div_le_one hzetaPos).2 (hnum.trans hzeta.le)
  exact ⟨hzetaPos, hxiPos, hthinNonneg, hthinLe⟩

/-- The source floor and the saved-contribution floor are the same integer. -/
theorem sourceArrivalFloor_eq_savedFloor {p : Parameters}
    (eta : LearningRate) (M : DownRecord (codecParams p eta))
    (y : Observation p) :
    sourceArrivalFloor eta M y =
      Nat.floor ((D p : ℝ) * eta.val * (2 : ℝ) ^ M.val.h * y.val.1) := by
  unfold sourceArrivalFloor
  congr 1
  unfold dyadicRate
  have hp : (0 : ℝ) < (2 : ℝ) ^ M.val.h := by positivity
  field_simp [ne_of_gt hp]

/-- An occupied-follower DATA gate passes the existing saved-contribution
gate, including at the non-strict thinning endpoint. -/
theorem recorderGate_le_savedGate {p : Parameters}
    (eta : LearningRate) (i : Fin (p.m - 1)) (row : CompleteRow p)
    (t : Fin p.T) (M : DownRecord (codecParams p eta))
    (hgate : recorderGate eta i row t M) :
    (coordinate Label.thin (row.2 t).1).val ≤
      (4 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ) * dyadicRate M.val.h) /
        sparseMaskProbability p.K (p.m - 1) := by
  rcases hgate with ⟨_, _, _, hthin⟩
  exact hthin.trans (thinningProbability_le_savedThreshold eta M)

/-- Exact source equation for the current follower arrival. -/
theorem rawArrival_eq_sourceFormula {p : Parameters}
    (eta : LearningRate) (i : Fin (p.m - 1)) (row : CompleteRow p)
    (t : Fin p.T) (M : DownRecord (codecParams p eta))
    (y : Observation p) :
    rawArrival eta i row t M y =
      if recorderGate eta i row t M then sourceArrivalFloor eta M y else 0 := by
  classical
  unfold rawArrival
  split_ifs with hgate
  · have hsaved := SparseCalendarReplay.savedContribution_eq_floor_of_le
      p.K (p.m - 1) (D p) eta.val M.val.h y.val
      (coordinate Label.thin (row.2 t).1)
      (recorderGate_le_savedGate eta i row t M hgate)
    rw [hsaved]
    exact (sourceArrivalFloor_eq_savedFloor eta M y).symm
  · rfl

/-- The literal threshold itself is inclusive: equality still selects the
source floor, and a failed DATA/source/mask/thinning test gives zero. -/
theorem rawArrival_eq_floor_of_gate {p : Parameters}
    (eta : LearningRate) (i : Fin (p.m - 1)) (row : CompleteRow p)
    (t : Fin p.T) (M : DownRecord (codecParams p eta))
    (y : Observation p) (hgate : recorderGate eta i row t M) :
    rawArrival eta i row t M y = sourceArrivalFloor eta M y := by
  classical
  rw [rawArrival_eq_sourceFormula, if_pos hgate]

/-- The record's admissibility lower bound and positive learning rate keep
the actual raw arrival in `[0,D]`. The upper-bound check remains in
`checkedService` as required by Appendix A. -/
theorem sourceArrivalFloor_le_D {p : Parameters}
    (eta : LearningRate) (M : DownRecord (codecParams p eta))
    (y : Observation p) : sourceArrivalFloor eta M y ≤ D p := by
  rcases M.property with ⟨_, _, _, _, _, _, _, _, hbeta, _, _⟩
  have hxi : 0 < dyadicRate M.val.h := by
    unfold dyadicRate
    positivity
  have hL : (1 : ℝ) ≤ (CanonicalRecordingRates.L_stab p : ℝ) := by
    exact_mod_cast CanonicalRecordingRates.L_stab_ge_one p
  have hbeta' : 32 * eta.val * (CanonicalRecordingRates.L_stab p : ℝ) ≤
      dyadicRate M.val.h := by
    simpa [codecParams, CanonicalRecordingRates.beta] using hbeta
  have hratio : eta.val / dyadicRate M.val.h ≤ 1 / 32 := by
    apply (div_le_iff₀ hxi).2
    nlinarith [hbeta', eta.property]
  have hy : 0 ≤ y.val.1 ∧ y.val.1 ≤ 1 := y.val.2
  have hnum : eta.val * y.val.1 ≤ dyadicRate M.val.h := by
    have hmul : eta.val * y.val.1 ≤ eta.val := by
      nlinarith [eta.property]
    have hdiv := (div_le_iff₀ hxi).1 hratio
    nlinarith
  have hreal :
      (D p : ℝ) * eta.val * y.val.1 / dyadicRate M.val.h ≤ (D p : ℝ) := by
    apply (div_le_iff₀ hxi).2
    calc
      (D p : ℝ) * eta.val * y.val.1 =
          (D p : ℝ) * (eta.val * y.val.1) := by ring
      _ ≤ (D p : ℝ) * dyadicRate M.val.h :=
        mul_le_mul_of_nonneg_left hnum (Nat.cast_nonneg _)
  unfold sourceArrivalFloor
  exact Nat.floor_le_of_le hreal

/-- The source rate cap and `n = eta D` imply the queue's service capacity is
at most `D`. -/
theorem serviceCapacity_le_D {p : Parameters} (eta : LearningRate)
    (hcap : sourceRateCapped p eta) (n : ℕ)
    (hn : (n : ℝ) = eta.val * (D p : ℝ)) :
    serviceCapacity n ≤ D p := by
  have hm : (2 : ℝ) ≤ (p.m : ℝ) := by exact_mod_cast p.two_le_m
  have hKnat : 2 ≤ p.K := by
    have hm := p.two_le_m
    have hmk := p.m_lt_K
    omega
  have hK : (2 : ℝ) ≤ (p.K : ℝ) := by exact_mod_cast hKnat
  have hL : (1 : ℝ) ≤ (CanonicalRecordingRates.L_stab p : ℝ) := by
    exact_mod_cast CanonicalRecordingRates.L_stab_ge_one p
  have hden : 0 < 1024 * (p.m : ℝ) * (p.K : ℝ) *
      (CanonicalRecordingRates.L_stab p : ℝ) := by positivity
  have hm1 : (1 : ℝ) ≤ (p.m : ℝ) := by nlinarith
  have hK1 : (1 : ℝ) ≤ (p.K : ℝ) := by linarith
  have hprod : (1 : ℝ) ≤ (p.m : ℝ) * (p.K : ℝ) *
      (CanonicalRecordingRates.L_stab p : ℝ) := by
    have hmk : (1 : ℝ) ≤ (p.m : ℝ) * (p.K : ℝ) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hm1) (sub_nonneg.mpr hK1)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hmk) (sub_nonneg.mpr hL)]
  have hden4 : 4 ≤ 1024 * (p.m : ℝ) * (p.K : ℝ) *
      (CanonicalRecordingRates.L_stab p : ℝ) := by nlinarith
  have hetaProd : eta.val *
      (1024 * (p.m : ℝ) * (p.K : ℝ) *
        (CanonicalRecordingRates.L_stab p : ℝ)) ≤ 1 :=
    (le_div_iff₀ hden).mp hcap
  have hetaQuarter : eta.val ≤ 1 / 4 := by
    have hmul := mul_le_mul_of_nonneg_right hden4 eta.property.le
    nlinarith
  have hDpos : 0 < (D p : ℝ) := by exact_mod_cast D_pos p
  have hnQuarter : 4 * (n : ℝ) ≤ (D p : ℝ) := by
    rw [hn]
    nlinarith [mul_le_mul_of_nonneg_left hetaQuarter hDpos.le]
  unfold serviceCapacity
  exact_mod_cast hnQuarter

/-- The current follower arrival is bounded by `D` from the admitted DOWN
rate; the checked operation still evaluates this as an output-domain test. -/
theorem rawArrival_le_D {p : Parameters} (eta : LearningRate)
    (i : Fin (p.m - 1)) (row : CompleteRow p) (t : Fin p.T)
    (M : DownRecord (codecParams p eta)) (y : Observation p) :
    rawArrival eta i row t M y ≤ D p := by
  classical
  by_cases hgate : recorderGate eta i row t M
  · rw [rawArrival_eq_floor_of_gate eta i row t M y hgate]
    exact sourceArrivalFloor_le_D eta M y
  · rw [rawArrival_eq_sourceFormula]
    rw [if_neg hgate]
    exact Nat.zero_le _

/-- The capped amount served is at most `D` under the source-capped natural
service scale. -/
theorem localService_le_D {p : Parameters} (eta : LearningRate)
    (hcap : sourceRateCapped p eta) (n : ℕ)
    (hn : (n : ℝ) = eta.val * (D p : ℝ)) (backlog arrival : ℕ) :
    localService n backlog arrival ≤ D p := by
  exact (CappedService.service_le_capacity (serviceCapacity n) backlog arrival).trans
    (serviceCapacity_le_D eta hcap n hn)

/-- The literal state update is the existing enabled queue transition. -/
theorem serviceUpdate_eq_queueTransition {p : Parameters} {eta : LearningRate}
    (n : ℕ) (s : State p eta) (arrival : ℕ) :
    ((serviceUpdate n s arrival).S, (serviceUpdate n s arrival).backlog) =
      QueueReplay.transition (serviceCapacity n) (s.S, s.backlog) (true, arrival) := by
  simp [serviceUpdate, localService, CappedService.service, CappedService.residual,
    QueueReplay.transition, serviceCapacity]

/-- Exact score, delta, and residual equations for the occupied service step. -/
theorem serviceUpdate_register_equations {p : Parameters} {eta : LearningRate}
    (n : ℕ) (s : State p eta) (arrival : ℕ) :
    (serviceUpdate n s arrival).S = s.S + localService n s.backlog arrival ∧
    (serviceUpdate n s arrival).delta = localService n s.backlog arrival ∧
    (serviceUpdate n s arrival).backlog + localService n s.backlog arrival =
      s.backlog + arrival := by
  refine ⟨rfl, rfl, ?_⟩
  exact CappedService.residual_add_service (serviceCapacity n) s.backlog arrival

/-- Enabled zero-arrival service still drains the incoming backlog. -/
theorem serviceUpdate_zero_arrival {p : Parameters} {eta : LearningRate}
    (n : ℕ) (s : State p eta) :
    (serviceUpdate n s 0).S = s.S + min (serviceCapacity n) s.backlog ∧
    (serviceUpdate n s 0).delta = min (serviceCapacity n) s.backlog ∧
    (serviceUpdate n s 0).backlog = s.backlog - min (serviceCapacity n) s.backlog := by
  simp [serviceUpdate, localService, CappedService.service, CappedService.residual]

/-- Every unrelated local register is preserved by service, including the
last DOWN record, partial DOWN batch, candidate buffer, status, and the
separate initialization-failure monitor. -/
theorem serviceUpdate_preserves_other_registers {p : Parameters}
    {eta : LearningRate} (n : ℕ) (s : State p eta) (arrival : ℕ) :
    (serviceUpdate n s arrival).lastDown = s.lastDown ∧
    (serviceUpdate n s arrival).downBatch = s.downBatch ∧
    (serviceUpdate n s arrival).buffer = s.buffer ∧
    (serviceUpdate n s arrival).status = s.status ∧
    (serviceUpdate n s arrival).initializationFailure = s.initializationFailure :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- An unoccupied follower has no online queue service; all reply/service
registers and other local state are preserved. -/
theorem serviceOutput_unoccupied_preserves {p : Parameters}
    {eta : LearningRate} (n : ℕ) (s : State p eta)
    (h : s.status = .unoccupied) (arrival : ℕ) :
    serviceOutput n s arrival = s := by
  classical
  simp [serviceOutput, FollowerStatus.occupied, h]

/-- Service preserves every non-queue local field on both occupied and
unoccupied branches. -/
theorem serviceOutput_preserves_other_registers {p : Parameters}
    {eta : LearningRate} (n : ℕ) (s : State p eta)
    (arrival : ℕ) :
    (serviceOutput n s arrival).lastDown = s.lastDown ∧
    (serviceOutput n s arrival).downBatch = s.downBatch ∧
    (serviceOutput n s arrival).buffer = s.buffer ∧
    (serviceOutput n s arrival).status = s.status ∧
    (serviceOutput n s arrival).initializationFailure =
      s.initializationFailure := by
  classical
  by_cases hoccupied : s.status.occupied
  · simp only [serviceOutput, if_pos hoccupied]
    exact serviceUpdate_preserves_other_registers n s arrival
  · simp [serviceOutput, hoccupied]

/-- A non-DATA slot has zero current recorder arrival, but the enabled queue
still receives its ordinary zero-arrival service transition. -/
theorem rawArrival_zero_of_not_data {p : Parameters}
    (eta : LearningRate) (i : Fin (p.m - 1)) (row : CompleteRow p)
    (t : Fin p.T) (M : DownRecord (codecParams p eta))
    (y : Observation p)
    (hslot : slotDraw (row.2 t).1 ≠ dataSlot) :
    rawArrival eta i row t M y = 0 := by
  classical
  rw [rawArrival_eq_sourceFormula]
  have hgate : ¬ recorderGate eta i row t M := by
    intro h
    exact hslot h.1
  rw [if_neg hgate]

/-- On a successful occupied non-DATA service round the source arrival is
zero, while the queue still serves `min(4n, backlog)`. -/
theorem serviceSuccess_nonData_update {p : Parameters} {eta : LearningRate}
    {n : ℕ} {i : Fin (p.m - 1)} {row : CompleteRow p} {alpha : Activation p}
    {t : Fin p.T} {observation : Observation p} {s : State p eta}
    (result : ServiceSuccess p eta n i row alpha t observation s)
    (hoccupied : s.status.occupied)
    (hslot : slotDraw (row.2 t).1 ≠ dataSlot) :
    result.arrival = 0 ∧
    result.service = min (serviceCapacity n) s.backlog ∧
    result.output.S = s.S + min (serviceCapacity n) s.backlog ∧
    result.output.delta = min (serviceCapacity n) s.backlog ∧
    result.output.backlog = s.backlog - min (serviceCapacity n) s.backlog := by
  cases hstatus : s.status with
  | unoccupied =>
      simp [FollowerStatus.occupied, hstatus] at hoccupied
  | pending =>
      have ha : serviceAction eta n i row alpha t observation s
          result.arrival result.service := result.action
      simp only [serviceAction, hstatus] at ha
      rcases ha with ⟨_, M, _hM, _hthin, harrival, hservice⟩
      have harrivalZero : result.arrival = 0 := by
        rw [harrival]
        exact rawArrival_zero_of_not_data eta i row t M observation hslot
      have hservice' : result.service = min (serviceCapacity n) s.backlog := by
        rw [hservice, harrivalZero]
        simp [localService, CappedService.service, serviceCapacity]
      have hqueue : result.output = serviceUpdate n s 0 := by
        calc
          result.output = serviceOutput n s result.arrival := result.queueUpdate
          _ = serviceOutput n s 0 := by rw [harrivalZero]
          _ = serviceUpdate n s 0 := by
            simp [serviceOutput, FollowerStatus.occupied, hstatus]
      rcases serviceUpdate_zero_arrival n s with ⟨hS, hdelta, hbacklog⟩
      exact ⟨harrivalZero, hservice', by rw [hqueue]; exact hS,
        by rw [hqueue]; exact hdelta, by rw [hqueue]; exact hbacklog⟩
  | released =>
      have ha : serviceAction eta n i row alpha t observation s
          result.arrival result.service := result.action
      simp only [serviceAction, hstatus] at ha
      rcases ha with ⟨_, M, _hM, _hthin, harrival, hservice⟩
      have harrivalZero : result.arrival = 0 := by
        rw [harrival]
        exact rawArrival_zero_of_not_data eta i row t M observation hslot
      have hservice' : result.service = min (serviceCapacity n) s.backlog := by
        rw [hservice, harrivalZero]
        simp [localService, CappedService.service, serviceCapacity]
      have hqueue : result.output = serviceUpdate n s 0 := by
        calc
          result.output = serviceOutput n s result.arrival := result.queueUpdate
          _ = serviceOutput n s 0 := by rw [harrivalZero]
          _ = serviceUpdate n s 0 := by
            simp [serviceOutput, FollowerStatus.occupied, hstatus]
      rcases serviceUpdate_zero_arrival n s with ⟨hS, hdelta, hbacklog⟩
      exact ⟨harrivalZero, hservice', by rw [hqueue]; exact hS,
        by rw [hqueue]; exact hdelta, by rw [hqueue]; exact hbacklog⟩

/-- The four UP fields are copied from the current unoccupied registers. -/
theorem checkedUpOffer_noOffer {p : Parameters} (eta : LearningRate)
    (i : Fin (p.m - 1)) (row : CompleteRow p) (alpha : Activation p)
    (t : Fin p.T) (s : State p eta) (hdomain : stateInputDomain s)
    (hnot : ¬ (selectedUpRound i row alpha t ∧ s.status = .unoccupied)) :
    checkedUpOffer eta i row alpha t s = .noOffer := by
  simp [checkedUpOffer, hdomain, hnot]

/-- If selected UP on an active round while unoccupied, the offer contains
exactly the incoming accepted-start, service, delta, and backlog fields. -/
theorem checkedUpOffer_fields {p : Parameters} (eta : LearningRate)
    (i : Fin (p.m - 1)) (row : CompleteRow p) (alpha : Activation p)
    (t : Fin p.T) (s : State p eta) (M : UpRecord (codecParams p eta))
    (h : checkedUpOffer eta i row alpha t s = .offer M) :
    M.val = upOfferFields s := by
  classical
  unfold checkedUpOffer at h
  by_cases hdomain : stateInputDomain s
  · simp only [dif_pos hdomain] at h
    by_cases hselected : selectedUpRound i row alpha t ∧ s.status = .unoccupied
    · simp only [dif_pos hselected] at h
      by_cases hadm : upAdmissible (codecParams p eta) (upOfferFields s)
      · simp only [dif_pos hadm] at h
        have hrecord := UpOfferResult.offer.inj h
        change (⟨upOfferFields s, hadm⟩ : UpRecord (codecParams p eta)) = M at hrecord
        rw [← hrecord]
      · simp only [dif_neg hadm] at h
        cases h
    · simp only [dif_neg hselected] at h
      cases h
  · simp only [dif_neg hdomain] at h
    cases h

/-- Every successful offer is accepted by the exact ordinary UP parser after
the existing codec encoder; this is a codec check, not a new message model. -/
theorem checkedUpOffer_codec {p : Parameters} (eta : LearningRate)
    (M : UpRecord (codecParams p eta)) :
    parseUp (codecParams p eta)
      (some (encodeUp (codecParams p eta) M)) = some M :=
  parseUp_encode (codecParams p eta) M

/-- Replay's zero placeholder is obtained from the actual replay registers,
not inserted as a default for every unoccupied state. -/
theorem checkedUpOffer_replay_placeholder {p : Parameters} {n : ℕ}
    (eta : LearningRate) (i : Fin (p.m - 1)) (row : CompleteRow p)
    (alpha : Activation p) (history : LocalHistory p n) (hn : n ≤ p.T)
    (t : Fin p.T) (M : UpRecord (codecParams p eta))
    (h : checkedUpOffer eta i row alpha t
      (ReferencePrelaunchFollower.replay eta i row alpha history hn) = .offer M) :
    M.val = upPlaceholder := by
  obtain ⟨_, hstart, hS, hdelta, hbacklog, _⟩ :=
    ReferencePrelaunchFollower.replay_registers eta i row alpha history hn
  have hfields := checkedUpOffer_fields eta i row alpha t _ M h
  rw [hfields]
  simp [upOfferFields, hstart, hS, hdelta, hbacklog, upPlaceholder]

/-- Every successful result carries the exact queue equation and the checked
raw-arrival, served-increment, score, and terminal-backlog domains. -/
theorem serviceSuccess_equations {p : Parameters} {eta : LearningRate} {n : ℕ}
    {i : Fin (p.m - 1)} {row : CompleteRow p} {alpha : Activation p}
    {t : Fin p.T} {observation : Observation p} {s : State p eta}
    (result : ServiceSuccess p eta n i row alpha t observation s) :
    result.output = serviceOutput n s result.arrival ∧
    result.arrival ≤ D p ∧ result.service ≤ D p ∧
      result.output.S ≤ p.T * D p ∧ result.output.backlog ≤ p.T * D p ∧
      serviceAction eta n i row alpha t observation s result.arrival result.service :=
  ⟨result.queueUpdate, result.arrival_le_D, result.service_le_D,
    result.score_le_TD, result.backlog_le_TD, result.action⟩

end Bandits.Support.ActiveFollowerQueueOperation

end
