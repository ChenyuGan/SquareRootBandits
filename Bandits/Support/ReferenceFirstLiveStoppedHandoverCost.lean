/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveHandoverPhysicalQuota
public import Bandits.Support.ReferenceFirstLiveStoppedHandoverSectionService

/-!
# Actual first-handover waiting cost

The physical service count and the stopped-phase waiting process are joined
on the original source execution. The cost uses the same actual handover
observation, pending sets, whole reward rows, and source-prefix start field.

Sources: ZIP4 `05_binary_transport.tex:180-281`,
`06_interruptions.tex:431-490`, and
`appendix_a_local_protocol.tex:100-108,141-157`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceFirstLiveHandoverBoundaryFactorization
open Bandits.Support.ReferenceFirstLiveSourceStoppedHandoverEndpoint
open Bandits.Support.ReferenceFirstLiveStoppedHandoverAdaptation
open Bandits.Support.ReferenceFirstLiveHandoverPhysicalQuota
open Bandits.Support.ReferenceFirstLiveStoppedHandoverSectionService
open Bandits.Support.PhaseServiceWaiting
open scoped BigOperators Classical ENNReal

namespace Bandits.Support.ReferenceFirstLiveStoppedHandoverCost

section Context

variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ)
  (control0 : ContinuousLearningRows.TimeControl p)

local notation "Source" => BootstrapPrivateRoundStreams.SourceInput p
local notation "mu" => BootstrapPrivateRoundStreams.sourceInputLaw p
local notation "F" =>
  ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0
local notation "pending" =>
  ReferenceFirstLiveSourceStoppedHandoverEndpoint.pendingNat rate rewards C_star C_h
local notation "XH" =>
  ReferenceFirstLiveStoppedHandoverAdaptation.X_H rate rewards C_star C_h control0
local notation "gH" =>
  ReferenceFirstLiveStoppedHandoverAdaptation.g_H rate rewards C_star C_h control0
local notation "sigmaH" =>
  ReferenceFirstLiveSourceStoppedHandoverEndpoint.sigma rate rewards C_star C_h
local notation "thetaH" =>
  ReferenceFirstLiveSourceStoppedHandoverEndpoint.theta rate rewards C_star C_h
local notation "phaseField" =>
  PhaseStartConditionalWaiting.phaseStartSigmaAlgebra F sigmaH
    (ReferenceFirstLiveStoppedHandoverAdaptation.sigma_preRound_stopping
      rate rewards C_star C_h control0)
local notation "quotaH" => 2 * AffineBatchDecoder.quota p + 1
local notation "aH" =>
  1 / (8 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ))

/-- On the actual pending support, the literal physical service term is the
same binary observation used by the stopped phase process. -/
theorem physicalServiceTerm_eq_X_H
    (z : Source) (i : Fin (p.m - 1)) (t : Fin p.T) :
    ReferenceFirstLiveHandoverPhysicalQuota.physicalServiceTerm
        rate rewards C_star C_h z
        (ReferenceFirstLiveHandoverPhysicalQuota.actionFollowerIndex i) t =
      if XH i t.val z then 1 else 0 := by
  classical
  let qIndex : Fin (p.m - 1) := i
  have hIndex :
      ReferenceFirstLiveHandoverPhysicalQuota.actionFollowerIndex i = qIndex := by
    apply Fin.ext
    rfl
  cases hrecord : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t z with
  | none =>
      simp [ReferenceFirstLiveHandoverPhysicalQuota.physicalServiceTerm,
        ReferenceFirstLiveStoppedHandoverAdaptation.X_H, hrecord, t.isLt]
  | some r =>
      have hactual :
          ReferenceSourcePrefixHistoryFiltration.actualRecord
            rate rewards C_star C_h t z = some r := hrecord
      by_cases hpending : qIndex ∈ pending t.val z
      · have hiPending : i ∈ pending t.val z := by
          simpa [qIndex, hIndex, ReferenceFirstLiveHandoverPhysicalQuota.actionFollowerIndex,
            PublicDiscreteDraws.followerCount] using hpending
        have hsupport : t.val + 1 ∈
            ReferenceFirstLiveSourceStoppedHandoverEndpoint.supportDates
              rate rewards C_star C_h z := by
          apply (ReferenceFirstLiveSourceStoppedHandoverEndpoint.pendingNat_nonempty_iff
            rate rewards C_star C_h z t.val).mp
          exact ⟨i, hiPending⟩
        obtain ⟨k, hdate, hwindowRecord, selected, hselected, _hpayload,
          _hmissing, _hphase, _hnext, _howned, _hbase, _hnextRecord,
          _hnextPayload, _hupdate⟩ :=
          ReferenceFirstLiveSourceStoppedHandoverEndpoint.supportDates_member_provenance
            rate rewards C_star C_h z (t.val + 1) hsupport
        have hwindowTime :
            ((ReferenceFirstLiveSourceStoppedHandoverEndpoint.window
              rate rewards C_star C_h z).get k).input.time = t := by
          apply Fin.ext
          exact Nat.add_right_cancel hdate
        have hwindowRecord' := hwindowRecord
        rw [hwindowTime] at hwindowRecord'
        have hwindowEq :
            (ReferenceFirstLiveSourceStoppedHandoverEndpoint.window
              rate rewards C_star C_h z).get k = r :=
          Option.some.inj (hwindowRecord'.symm.trans hactual)
        cases hwindowEq
        let r : ReferenceActivePhysicalHorizon.RoundRecord :=
          (ReferenceFirstLiveSourceStoppedHandoverEndpoint.window
            rate rewards C_star C_h z).get k
        have hselectedActual :
            ReferenceFirstLiveSourceStoppedHandoverEndpoint.actualSelection rate r =
              some selected := hselected
        have hBeforeIff :
            ReferenceFirstLiveHandoverPhysicalQuota.beforeDownService
                rate qIndex r ↔
              Before rate r i ∧ V_before rate rewards C_star C_h i t z := by
          constructor
          · rintro ⟨incoming, memory, hstate, hnone, hdown, hpositive⟩
            have hdown' : ActiveFollowerDownAcceptance.downSelected p i
                r.input.row r.input.time := by
              simpa only [hIndex] using hdown
            refine ⟨⟨incoming, memory, hstate, hnone⟩, ?_⟩
            refine ⟨r, hactual, ?_, ?_, ?_⟩
            · exact hdown'.1
            · exact hdown'.2
            · simpa only [ReferenceFollowerDownDecoderReplay.preparedOwnObservation,
                hIndex] using hpositive
          · rintro ⟨⟨incoming, memory, hstate, hnone⟩,
              ⟨record, hrecord', hslot, hdraw, hpositive⟩⟩
            have hrecordEq : record = r :=
              Option.some.inj (hrecord'.symm.trans hactual)
            subst record
            have hdown : ActiveFollowerDownAcceptance.downSelected p i
                r.input.row r.input.time := ⟨hslot, hdraw⟩
            refine ⟨incoming, memory, hstate, hnone, ?_, ?_⟩
            · simpa only [hIndex] using hdown
            · simpa only [ReferenceFollowerDownDecoderReplay.preparedOwnObservation,
                hIndex] using hpositive
        have hAfterIff :
            ReferenceFirstLiveHandoverPhysicalQuota.afterDownService
                rate qIndex r ↔
              ∃ chosen : ReferenceActivePhysicalStep.Selection r.input,
                ReferenceFirstLiveSourceStoppedHandoverEndpoint.actualSelection
                    rate r = some chosen ∧
                After rate r chosen i ∧
                V_after rate rewards C_star C_h i t z := by
          have hnormalized :
              (r.output.preparation.feedback.observations
                (ActiveRoundActions.coordinator p.two_le_m)).val.val =
              CoordinatorLocalArmChoice.ownGridObservationValue
                r.output.preparation.coordinatorObservation :=
            r.output.preparation.feedback.observation_grid_value _
          constructor
          · rintro ⟨chosen, hchosen, ⟨incoming, memory, hstate, hlast⟩,
              hdown, hhash, hpositive⟩
            have hdown' : ActiveFollowerDownAcceptance.downSelected p i
                r.input.row r.input.time := by
              simpa only [hIndex] using hdown
            have hpositive' : 0 <
                (r.output.preparation.feedback.observations
                  (ActiveRoundActions.coordinator p.two_le_m)).val.val := by
              rw [hnormalized]
              exact hpositive
            refine ⟨chosen, ?_, ⟨incoming, memory, hstate, hlast⟩, ?_⟩
            · exact hchosen
            · refine ⟨r, chosen, hactual, ?_, hdown'.1, hdown'.2,
                hhash, hpositive'⟩
              change ReferenceFirstLiveSourceStoppedHandoverEndpoint.actualSelection
                rate r = some chosen at hchosen
              exact hchosen
          · rintro ⟨chosen, hchosen, ⟨incoming, memory, hstate, hlast⟩,
              ⟨record, selected', hrecord', hselection', hslot, hdraw,
                hhash, hpositive⟩⟩
            have hrecordEq : record = r :=
              Option.some.inj (hrecord'.symm.trans hactual)
            subst record
            have hchosen' : r.output.preparation.coordinator.selection =
                some chosen := by
              change ReferenceFirstLiveSourceStoppedHandoverEndpoint.actualSelection
                rate r = some chosen at hchosen
              exact hchosen
            have hchosenEq : chosen = selected' :=
              Option.some.inj (hchosen'.symm.trans hselection')
            subst selected'
            have hdown : ActiveFollowerDownAcceptance.downSelected p i
                r.input.row r.input.time := ⟨hslot, hdraw⟩
            have hpositive' : 0 <
                CoordinatorLocalArmChoice.ownGridObservationValue
                  r.output.preparation.coordinatorObservation := by
              rw [← hnormalized]
              exact hpositive
            refine ⟨chosen, hchosen, ⟨incoming, memory, hstate, hlast⟩,
              ?_, hhash, hpositive'⟩
            simpa only [hIndex] using hdown
        have hServiceIff :
            (qIndex ∈ pending t.val z ∧
              (ReferenceFirstLiveHandoverPhysicalQuota.beforeDownService
                  rate qIndex r ∨
                ReferenceFirstLiveHandoverPhysicalQuota.afterDownService
                  rate qIndex r)) ↔
              XH i t.val z = true := by
          rw [ReferenceFirstLiveStoppedHandoverAdaptation.X_H_eq_decide
            rate rewards C_star C_h control0 i t]
          simp only [decide_eq_true_eq]
          constructor
          · rintro ⟨hpending', hbefore | hafter⟩
            · have hpending'' : i ∈ pending t.val z := by
                simpa [qIndex, hIndex,
                  ReferenceFirstLiveHandoverPhysicalQuota.actionFollowerIndex,
                  PublicDiscreteDraws.followerCount] using hpending'
              refine ⟨hpending'', r, selected, hactual, hselectedActual, ?_⟩
              exact Or.inl (hBeforeIff.mp hbefore)
            · have ⟨chosen, hchosen, hafter', hv⟩ := hAfterIff.mp hafter
              have hpending'' : i ∈ pending t.val z := by
                simpa [qIndex, hIndex,
                  ReferenceFirstLiveHandoverPhysicalQuota.actionFollowerIndex,
                  PublicDiscreteDraws.followerCount] using hpending'
              exact ⟨hpending'', r, chosen, hactual, hchosen,
                Or.inr ⟨hafter', hv⟩⟩
          · rintro ⟨hpending', record, chosen, hrecord', hchosen,
              hbefore | ⟨hafter, hv⟩⟩
            · have hrecordEq : record = r :=
                Option.some.inj (hrecord'.symm.trans hactual)
              subst record
              have hchosenEq : chosen = selected :=
                Option.some.inj (hchosen.symm.trans hselectedActual)
              subst chosen
              have hpending'' : qIndex ∈ pending t.val z := by
                simpa [qIndex, hIndex,
                  ReferenceFirstLiveHandoverPhysicalQuota.actionFollowerIndex,
                  PublicDiscreteDraws.followerCount] using hpending'
              exact ⟨hpending'', Or.inl (hBeforeIff.mpr hbefore)⟩
            · have hrecordEq : record = r :=
                Option.some.inj (hrecord'.symm.trans hactual)
              subst record
              have hchosenEq : chosen = selected :=
                Option.some.inj (hchosen.symm.trans hselectedActual)
              subst chosen
              have hpending'' : qIndex ∈ pending t.val z := by
                simpa [qIndex, hIndex,
                  ReferenceFirstLiveHandoverPhysicalQuota.actionFollowerIndex,
                  PublicDiscreteDraws.followerCount] using hpending'
              exact ⟨hpending'', Or.inr (hAfterIff.mpr
                ⟨selected, hselectedActual, hafter, hv⟩)⟩
        have hServiceIffAction :
            (ReferenceFirstLiveHandoverPhysicalQuota.actionFollowerIndex i ∈
                pending t.val z ∧
              (ReferenceFirstLiveHandoverPhysicalQuota.beforeDownService rate
                  (ReferenceFirstLiveHandoverPhysicalQuota.actionFollowerIndex i)
                  ((ReferenceFirstLiveSourceStoppedHandoverEndpoint.window
                    rate rewards C_star C_h z).get k) ∨
                ReferenceFirstLiveHandoverPhysicalQuota.afterDownService rate
                  (ReferenceFirstLiveHandoverPhysicalQuota.actionFollowerIndex i)
                  ((ReferenceFirstLiveSourceStoppedHandoverEndpoint.window
                    rate rewards C_star C_h z).get k))) ↔
              XH i t.val z = true := by
          change (ReferenceFirstLiveHandoverPhysicalQuota.actionFollowerIndex i ∈
                pending t.val z ∧
              (ReferenceFirstLiveHandoverPhysicalQuota.beforeDownService rate
                  (ReferenceFirstLiveHandoverPhysicalQuota.actionFollowerIndex i) r ∨
                ReferenceFirstLiveHandoverPhysicalQuota.afterDownService rate
                  (ReferenceFirstLiveHandoverPhysicalQuota.actionFollowerIndex i) r)) ↔ _
          rw [hIndex]
          exact hServiceIff
        rw [ReferenceFirstLiveHandoverPhysicalQuota.physicalServiceTerm,
          hrecord]
        dsimp only
        split_ifs <;> simp_all
      · have hnotPending : i ∉ pending t.val z := by
          intro hi
          apply hpending
          simpa [qIndex, hIndex,
            ReferenceFirstLiveHandoverPhysicalQuota.actionFollowerIndex,
            PublicDiscreteDraws.followerCount] using hi
        have hX : XH i t.val z = false :=
          ReferenceFirstLiveStoppedHandoverAdaptation.X_H_false_of_not_pending
            rate rewards C_star C_h control0 i t.val z hnotPending
        have hnotIndex : qIndex ∉ pending t.val z := hpending
        have hserviceFalse :
            ¬ (ReferenceFirstLiveHandoverPhysicalQuota.actionFollowerIndex i ∈
                pending t.val z ∧
              (ReferenceFirstLiveHandoverPhysicalQuota.beforeDownService rate
                  (ReferenceFirstLiveHandoverPhysicalQuota.actionFollowerIndex i) r ∨
                ReferenceFirstLiveHandoverPhysicalQuota.afterDownService rate
                  (ReferenceFirstLiveHandoverPhysicalQuota.actionFollowerIndex i) r)) := by
          intro h
          have hi : i ∈ pending t.val z := by
            have hmem :
                (⟨i.val, by simp⟩ :
                  Fin (p.m - 1)) ∈ pending t.val z := by
              simpa only [ReferenceFirstLiveHandoverPhysicalQuota.actionFollowerIndex,
                ActiveRoundActions.Follower, PublicDiscreteDraws.followerCount] using h.1
            have hindex :
                (⟨i.val, by simp⟩ :
                  Fin (p.m - 1)) = i := by
              apply Fin.ext
              rfl
            simpa [hindex] using hmem
          exact hpending hi
        simp [ReferenceFirstLiveHandoverPhysicalQuota.physicalServiceTerm,
          hrecord, hserviceFalse, hX]

private theorem range_fin_sum (T n : ℕ) (hn : n ≤ T) (f : Fin T → ℕ) :
    (∑ r ∈ Finset.range n, if hr : r < T then f ⟨r, hr⟩ else 0) =
      ∑ t : Fin T, if t.val < n then f t else 0 := by
  classical
  let g : ℕ → ℕ := fun r =>
    if hr : r < T then if r < n then f ⟨r, hr⟩ else 0 else 0
  have hleft :
      (∑ r ∈ Finset.range n, if hr : r < T then f ⟨r, hr⟩ else 0) =
        ∑ r ∈ Finset.range n, g r := by
    apply Finset.sum_congr rfl
    intro r hr
    have hrn : r < n := Finset.mem_range.mp hr
    have hrT : r < T := lt_of_lt_of_le hrn hn
    simp [g, hrn, hrT]
  have hright :
      (∑ t : Fin T, if t.val < n then f t else 0) =
        ∑ r ∈ Finset.range T, g r := by
    calc
      (∑ t : Fin T, if t.val < n then f t else 0) =
          ∑ t : Fin T, g t.val := by
            apply Finset.sum_congr rfl
            intro t ht
            by_cases htn : t.val < n <;> simp [g, t.isLt, htn]
      _ = ∑ r ∈ Finset.range T, g r := Fin.sum_univ_eq_sum_range g T
  have hsub : Finset.range n ⊆ Finset.range T :=
    Finset.range_subset_range.mpr hn
  have hzero : ∀ r ∈ Finset.range T, r ∉ Finset.range n → g r = 0 := by
    intro r hrT hrn
    have hnle : n ≤ r := Nat.le_of_not_gt (fun hlt =>
      hrn (Finset.mem_range.mpr hlt))
    simp [g, not_lt.mpr hnle]
  calc
    (∑ r ∈ Finset.range n, if hr : r < T then f ⟨r, hr⟩ else 0) =
        ∑ r ∈ Finset.range n, g r := hleft
    _ = ∑ r ∈ Finset.range T, g r := Finset.sum_subset hsub hzero
    _ = ∑ t : Fin T, if t.val < n then f t else 0 := hright.symm

/-- The generic service count and the actual physical count use the same
calendar prefix, including all zero terms beyond the stopped support. -/
theorem N_eq_stoppedServiceSum
    (z : Source) (i : Fin (p.m - 1)) (n : ℕ) (hn : n ≤ p.T) :
    PhaseServiceWaiting.N pending XH i n z =
      ReferenceFirstLiveHandoverPhysicalQuota.stoppedServiceSum
        rate rewards C_star C_h z i n := by
  classical
  let f : Fin p.T → ℕ := fun t =>
    if i ∈ pending t.val z ∧ XH i t.val z then 1 else 0
  have hf : ∀ t : Fin p.T,
      f t = ReferenceFirstLiveHandoverPhysicalQuota.physicalServiceTerm
        rate rewards C_star C_h z
        (ReferenceFirstLiveHandoverPhysicalQuota.actionFollowerIndex i) t := by
    intro t
    have hjoin := physicalServiceTerm_eq_X_H rate rewards C_star C_h control0
      z i t
    have hsupport : XH i t.val z = true → i ∈ pending t.val z := by
      intro hx
      by_contra hnot
      have hfalse :=
        ReferenceFirstLiveStoppedHandoverAdaptation.X_H_false_of_not_pending
          rate rewards C_star C_h control0 i t.val z hnot
      rw [hfalse] at hx
      cases hx
    by_cases hx : XH i t.val z = true
    · have hp := hsupport hx
      simp [f, hp, hx, hjoin]
    · simp [f, hx, hjoin]
  have hleft :
      (∑ r ∈ Finset.range n,
        if i ∈ pending r z ∧ XH i r z then 1 else 0) =
      (∑ r ∈ Finset.range n,
        if hr : r < p.T then f ⟨r, hr⟩ else 0) := by
    apply Finset.sum_congr rfl
    intro r hr
    have hrn : r < n := Finset.mem_range.mp hr
    have hrT : r < p.T := lt_of_lt_of_le hrn hn
    simp [f, hrT]
  unfold PhaseServiceWaiting.N
  rw [hleft]
  rw [range_fin_sum p.T n hn f]
  unfold ReferenceFirstLiveHandoverPhysicalQuota.stoppedServiceSum
  apply Finset.sum_congr rfl
  intro t ht
  by_cases htn : t.val < n
  · simp only [ite_eq_left htn]
    rw [hf t]
  · simp only [ite_eq_right htn]

/-- The physical stopped sum is unchanged when truncated at the literal
first-excluded endpoint: every later source-calendar term is zero. -/
theorem stoppedServiceSum_eq_truncated
    (z : Source) (i : Fin (p.m - 1)) (n : ℕ) :
    ReferenceFirstLiveHandoverPhysicalQuota.stoppedServiceSum
        rate rewards C_star C_h z i n =
      ReferenceFirstLiveHandoverPhysicalQuota.stoppedServiceSum
        rate rewards C_star C_h z i
        (min n (ReferenceFirstLiveSourceStoppedHandoverEndpoint.theta
          rate rewards C_star C_h z - 1)) := by
  classical
  unfold ReferenceFirstLiveHandoverPhysicalQuota.stoppedServiceSum
  apply Finset.sum_congr rfl
  intro t ht
  by_cases htn : t.val < n
  · by_cases hcut : t.val < min n
        (ReferenceFirstLiveSourceStoppedHandoverEndpoint.theta
          rate rewards C_star C_h z - 1)
    · simp only [ite_eq_left htn, ite_eq_left hcut]
    · have hafter :
          ReferenceFirstLiveSourceStoppedHandoverEndpoint.theta
            rate rewards C_star C_h z - 1 ≤ t.val := by omega
      have hnotSupport : t.val + 1 ∉
          ReferenceFirstLiveSourceStoppedHandoverEndpoint.supportDates
            rate rewards C_star C_h z := by
        intro hs
        have hinterval :=
          ReferenceFirstLiveSourceStoppedHandoverEndpoint.supportDates_subset_interval
            rate rewards C_star C_h z hs
        have hlt := (Finset.mem_Ico.mp hinterval).2
        omega
      have hpending : pending t.val z = ∅ := by
        ext j
        constructor
        · intro hj
          have hs :=
            (ReferenceFirstLiveSourceStoppedHandoverEndpoint.pendingNat_nonempty_iff
              rate rewards C_star C_h z t.val).mp ⟨j, hj⟩
          exact (hnotSupport hs).elim
        · intro hj
          simp at hj
      have hzero :
          ReferenceFirstLiveHandoverPhysicalQuota.physicalServiceTerm
            rate rewards C_star C_h z
            (ReferenceFirstLiveHandoverPhysicalQuota.actionFollowerIndex i) t = 0 := by
        cases hrecord : ReferenceSourcePrefixHistoryFiltration.actualRecord
            rate rewards C_star C_h t z with
        | none => simp [ReferenceFirstLiveHandoverPhysicalQuota.physicalServiceTerm,
            hrecord]
        | some r =>
            have hserviceFalse :
                ¬ (ReferenceFirstLiveHandoverPhysicalQuota.actionFollowerIndex i ∈
                    pending t.val z ∧
                  (ReferenceFirstLiveHandoverPhysicalQuota.beforeDownService rate
                      (ReferenceFirstLiveHandoverPhysicalQuota.actionFollowerIndex i) r ∨
                    ReferenceFirstLiveHandoverPhysicalQuota.afterDownService rate
                      (ReferenceFirstLiveHandoverPhysicalQuota.actionFollowerIndex i) r)) := by
              intro h
              have hne : (pending t.val z).Nonempty :=
                ⟨ReferenceFirstLiveHandoverPhysicalQuota.actionFollowerIndex i, h.1⟩
              rw [hpending] at hne
              exact Finset.not_nonempty_empty hne
            simp [ReferenceFirstLiveHandoverPhysicalQuota.physicalServiceTerm,
              hrecord, hserviceFalse]
      simp only [ite_eq_left htn, ite_eq_right hcut, hzero]
  · have hcut : ¬ t.val < min n
        (ReferenceFirstLiveSourceStoppedHandoverEndpoint.theta
          rate rewards C_star C_h z - 1) := by omega
    simp only [ite_eq_right htn, ite_eq_right hcut]

/-- The actual physical task count never exceeds its two decoder batches and
one genuine confirmation, including after literal off-support zero terms. -/
theorem stoppedServiceSum_le_twoQ_add_one
    (z : Source) (i : Fin (p.m - 1)) (n : ℕ) :
    ReferenceFirstLiveHandoverPhysicalQuota.stoppedServiceSum
        rate rewards C_star C_h z i n ≤ 2 * AffineBatchDecoder.quota p + 1 := by
  rw [stoppedServiceSum_eq_truncated rate rewards C_star C_h z i n]
  exact ReferenceFirstLiveHandoverPhysicalQuota.actualStoppedServiceSum_le_twoQ_add_one
    rate rewards C_star C_h z i n

/-- Immediately before every actual pending date, the accumulated generic
waiting count is strictly below its incoming quota. -/
theorem incomingQuota_strict
    (z : Source) (k : ℕ) (hk : k < p.T) (i : Fin (p.m - 1))
    (hi : i ∈ pending k z) :
    PhaseServiceWaiting.N pending XH i k z < quotaH := by
  have hsupport :=
    (ReferenceFirstLiveSourceStoppedHandoverEndpoint.pendingNat_nonempty_iff
      rate rewards C_star C_h z k).mp ⟨i, hi⟩
  rw [N_eq_stoppedServiceSum rate rewards C_star C_h control0 z i k hk.le]
  exact ReferenceFirstLiveHandoverPhysicalQuota.actualStoppedServiceSum_lt_twoQ_add_one_before_pending
    rate rewards C_star C_h z i ⟨k, hk⟩ hsupport hi

private theorem waiting_parameter_pos :
    0 < p.m - 1 ∧ 0 < p.T ∧ 0 < p.K ∧ 0 < quotaH ∧ 0 < aH := by
  have hd : 0 < p.m - 1 := Nat.sub_pos_of_lt
    (lt_of_lt_of_le (by decide : 1 < 2) p.two_le_m)
  have hq : 0 < 2 * AffineBatchDecoder.quota p + 1 := by omega
  have ha : 0 <
      (1 / (8 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ))) := by
    have hdR : 0 < ((p.m - 1 : ℕ) : ℝ) := Nat.cast_pos.mpr hd
    have hKR : 0 < (p.K : ℝ) := Nat.cast_pos.mpr (ConstructorDimensions.K_pos p)
    positivity
  exact ⟨hd, ConstructorDimensions.T_pos p, ConstructorDimensions.K_pos p,
    hq, ha⟩

private theorem actual_phase_bounds (t : ℕ) (_ht : t < p.T) (z : Source)
    (hne : (pending t z).Nonempty) :
    sigmaH z ≤ t + 1 ∧ t + 1 < thetaH z := by
  have hs :=
    (ReferenceFirstLiveSourceStoppedHandoverEndpoint.pendingNat_nonempty_iff
      rate rewards C_star C_h z t).mp hne
  have hinterval :=
    ReferenceFirstLiveSourceStoppedHandoverEndpoint.supportDates_subset_interval
      rate rewards C_star C_h z hs
  exact Finset.mem_Ico.mp hinterval

private theorem actual_gH_bounds (t : ℕ) (ht : t < p.T) (z : Source) :
    gH t z ∈ Set.Icc (0 : ℝ) (p.K : ℝ) := by
  let ft : Fin p.T := ⟨t, ht⟩
  rw [ReferenceFirstLiveStoppedHandoverAdaptation.g_H_eq_card
    rate rewards C_star C_h control0 ft z]
  have hcard :
      (Finset.univ.filter fun b : Fin p.K => 0 < (rewards ft b).val).card ≤ p.K := by
    calc
      (Finset.univ.filter fun b : Fin p.K => 0 < (rewards ft b).val).card ≤
          (Finset.univ : Finset (Fin p.K)).card :=
        Finset.card_filter_le Finset.univ _
      _ = p.K := by simp
  exact ⟨Nat.cast_nonneg _, Nat.cast_le.mpr hcard⟩

private theorem actual_waiting_totalCharge_integrable_exp :
    Integrable
        (PhaseServiceWaiting.totalCharge pending sigmaH thetaH gH p.T) mu ∧
      Integrable
        (fun z => Real.exp (PhaseServiceWaiting.kappa * aH *
          PhaseServiceWaiting.totalCharge pending sigmaH thetaH gH p.T z)) mu := by
  have hstopping :=
    ReferenceFirstLiveStoppedHandoverAdaptation.sigma_preRound_stopping
      rate rewards C_star C_h control0
  have htheta :=
    ReferenceFirstLiveStoppedHandoverAdaptation.theta_preRound_stopping
      rate rewards C_star C_h control0
  have hbounds := fun t ht z hne => actual_phase_bounds rate rewards C_star C_h
    t ht z hne
  have hweight := fun t ht z => actual_gH_bounds rate rewards C_star C_h
    control0 t ht z
  obtain ⟨_, _, _, _, ha⟩ := waiting_parameter_pos (p := p)
  exact PhaseServiceWaiting.totalCharge_exp_integrable mu F pending sigmaH thetaH gH aH ha
    hstopping htheta
    (fun i t ht => ReferenceFirstLiveStoppedHandoverAdaptation.pendingNat_preRound_measurableSet
      rate rewards C_star C_h control0 i t ht)
    (fun t ht => ReferenceFirstLiveStoppedHandoverAdaptation.g_H_preRound_stronglyMeasurable
      rate rewards C_star C_h control0 t)
    hbounds hweight

private theorem actual_phase_start_totalCharge_condExp_bound :
    mu[PhaseServiceWaiting.totalCharge pending sigmaH thetaH gH p.T | phaseField]
      ≤ᵐ[mu] fun _ =>
        (((quotaH : ℝ) + Real.log ((p.m - 1 : ℕ) : ℝ)) /
          (PhaseServiceWaiting.kappa * aH)) := by
  obtain ⟨hd, hT, hK, hq, ha⟩ :=
    waiting_parameter_pos (p := p)
  have hstopping :=
    ReferenceFirstLiveStoppedHandoverAdaptation.sigma_preRound_stopping
      rate rewards C_star C_h control0
  have htheta :=
    ReferenceFirstLiveStoppedHandoverAdaptation.theta_preRound_stopping
      rate rewards C_star C_h control0
  have hbounds := fun t ht z hne => actual_phase_bounds rate rewards C_star C_h
    t ht z hne
  have hweight := fun t ht z => actual_gH_bounds rate rewards C_star C_h
    control0 t ht z
  have hgeneric := PhaseStartConditionalWaiting.phase_start_totalCharge_condExp_bound
    (μ := mu) (d := p.m - 1) (T := p.T) (K := p.K) (q := quotaH)
    hd hT hK hq F pending XH gH sigmaH thetaH aH ha hstopping htheta
    (fun z => (ReferenceFirstLiveSourceStoppedHandoverEndpoint.sigma_theta_bounds
      rate rewards C_star C_h z).1)
    (fun z => (ReferenceFirstLiveSourceStoppedHandoverEndpoint.sigma_theta_bounds
      rate rewards C_star C_h z).2.1)
    (fun z => (ReferenceFirstLiveSourceStoppedHandoverEndpoint.sigma_theta_bounds
      rate rewards C_star C_h z).2.2)
    (fun i t ht => ReferenceFirstLiveStoppedHandoverAdaptation.pendingNat_preRound_measurableSet
      rate rewards C_star C_h control0 i t ht)
    hbounds
    (fun s t hst ht z hs he =>
      ReferenceFirstLiveSourceStoppedHandoverEndpoint.pendingNat_antitone
        rate rewards C_star C_h z s t hst ht hs he)
    (fun t ht => ReferenceFirstLiveStoppedHandoverAdaptation.g_H_preRound_stronglyMeasurable
      rate rewards C_star C_h control0 t)
    hweight
    (fun i t ht =>
      ReferenceFirstLiveStoppedHandoverAdaptation.observation_roundEnd_stronglyMeasurable
        rate rewards C_star C_h control0 i t ht)
    (fun i t ht z hi => incomingQuota_strict rate rewards C_star C_h control0 z t ht i hi)
    (fun i t ht => ReferenceFirstLiveStoppedHandoverSectionService.phaseStart_hservice
      rate rewards C_star C_h control0 t ht i)
  push_cast at hgeneric ⊢
  exact hgeneric

private theorem actual_phase_start_totalCharge_exponential_setIntegral_bound
    (B : Set Source)
    (hB : MeasurableSet[phaseField] B) :
    ∫ z in B, Real.exp (PhaseServiceWaiting.kappa * aH *
      PhaseServiceWaiting.totalCharge pending sigmaH thetaH gH p.T z) ∂mu ≤
        ((p.m - 1 : ℕ) : ℝ) * Real.exp (quotaH : ℝ) *
          (BootstrapPrivateRoundStreams.sourceInputLaw p).real B := by
  obtain ⟨hd, hT, hK, hq, ha⟩ :=
    waiting_parameter_pos (p := p)
  have hstopping :=
    ReferenceFirstLiveStoppedHandoverAdaptation.sigma_preRound_stopping
      rate rewards C_star C_h control0
  have htheta :=
    ReferenceFirstLiveStoppedHandoverAdaptation.theta_preRound_stopping
      rate rewards C_star C_h control0
  have hbounds := fun t ht z hne => actual_phase_bounds rate rewards C_star C_h
    t ht z hne
  have hweight := fun t ht z => actual_gH_bounds rate rewards C_star C_h
    control0 t ht z
  have hgeneric := PhaseStartConditionalWaiting.phase_start_totalCharge_exponential_setIntegral_bound
    (μ := mu) (d := p.m - 1) (T := p.T) (K := p.K) (q := quotaH)
    hd hT hK hq F pending XH gH sigmaH thetaH aH ha hstopping htheta
    (fun z => (ReferenceFirstLiveSourceStoppedHandoverEndpoint.sigma_theta_bounds
      rate rewards C_star C_h z).1)
    (fun z => (ReferenceFirstLiveSourceStoppedHandoverEndpoint.sigma_theta_bounds
      rate rewards C_star C_h z).2.1)
    (fun z => (ReferenceFirstLiveSourceStoppedHandoverEndpoint.sigma_theta_bounds
      rate rewards C_star C_h z).2.2)
    (fun i t ht => ReferenceFirstLiveStoppedHandoverAdaptation.pendingNat_preRound_measurableSet
      rate rewards C_star C_h control0 i t ht)
    hbounds
    (fun s t hst ht z hs he =>
      ReferenceFirstLiveSourceStoppedHandoverEndpoint.pendingNat_antitone
        rate rewards C_star C_h z s t hst ht hs he)
    (fun t ht => ReferenceFirstLiveStoppedHandoverAdaptation.g_H_preRound_stronglyMeasurable
      rate rewards C_star C_h control0 t)
    hweight
    (fun i t ht =>
      ReferenceFirstLiveStoppedHandoverAdaptation.observation_roundEnd_stronglyMeasurable
        rate rewards C_star C_h control0 i t ht)
    (fun i t ht z hi => incomingQuota_strict rate rewards C_star C_h control0 z t ht i hi)
    (fun i t ht => ReferenceFirstLiveStoppedHandoverSectionService.phaseStart_hservice
      rate rewards C_star C_h control0 t ht i)
    B hB
  push_cast at hgeneric ⊢
  exact hgeneric

private theorem actual_phase_start_totalCharge_setIntegral_bound
    (B : Set Source)
    (hB : MeasurableSet[phaseField] B) :
    ∫ z in B, PhaseServiceWaiting.totalCharge pending sigmaH thetaH gH p.T z ∂mu ≤
      (((quotaH : ℝ) + Real.log ((p.m - 1 : ℕ) : ℝ)) /
        (PhaseServiceWaiting.kappa * aH)) *
          (BootstrapPrivateRoundStreams.sourceInputLaw p).real B := by
  obtain ⟨hd, hT, hK, hq, ha⟩ :=
    waiting_parameter_pos (p := p)
  have hstopping :=
    ReferenceFirstLiveStoppedHandoverAdaptation.sigma_preRound_stopping
      rate rewards C_star C_h control0
  have htheta :=
    ReferenceFirstLiveStoppedHandoverAdaptation.theta_preRound_stopping
      rate rewards C_star C_h control0
  have hbounds := fun t ht z hne => actual_phase_bounds rate rewards C_star C_h
    t ht z hne
  have hweight := fun t ht z => actual_gH_bounds rate rewards C_star C_h
    control0 t ht z
  have hgeneric := PhaseStartConditionalWaiting.phase_start_totalCharge_setIntegral_bound
    (μ := mu) (d := p.m - 1) (T := p.T) (K := p.K) (q := quotaH)
    hd hT hK hq F pending XH gH sigmaH thetaH aH ha hstopping htheta
    (fun z => (ReferenceFirstLiveSourceStoppedHandoverEndpoint.sigma_theta_bounds
      rate rewards C_star C_h z).1)
    (fun z => (ReferenceFirstLiveSourceStoppedHandoverEndpoint.sigma_theta_bounds
      rate rewards C_star C_h z).2.1)
    (fun z => (ReferenceFirstLiveSourceStoppedHandoverEndpoint.sigma_theta_bounds
      rate rewards C_star C_h z).2.2)
    (fun i t ht => ReferenceFirstLiveStoppedHandoverAdaptation.pendingNat_preRound_measurableSet
      rate rewards C_star C_h control0 i t ht)
    hbounds
    (fun s t hst ht z hs he =>
      ReferenceFirstLiveSourceStoppedHandoverEndpoint.pendingNat_antitone
        rate rewards C_star C_h z s t hst ht hs he)
    (fun t ht => ReferenceFirstLiveStoppedHandoverAdaptation.g_H_preRound_stronglyMeasurable
      rate rewards C_star C_h control0 t)
    hweight
    (fun i t ht =>
      ReferenceFirstLiveStoppedHandoverAdaptation.observation_roundEnd_stronglyMeasurable
        rate rewards C_star C_h control0 i t ht)
    (fun i t ht z hi => incomingQuota_strict rate rewards C_star C_h control0 z t ht i hi)
    (fun i t ht => ReferenceFirstLiveStoppedHandoverSectionService.phaseStart_hservice
      rate rewards C_star C_h control0 t ht i)
    B hB
  push_cast at hgeneric ⊢
  exact hgeneric

private theorem waiting_constant_eq_source_constant :
    (((quotaH : ℝ) + Real.log ((p.m - 1 : ℕ) : ℝ)) /
        (PhaseServiceWaiting.kappa * aH)) =
      (8 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ) /
        PhaseServiceWaiting.kappa) *
        (2 * (AffineBatchDecoder.quota p : ℝ) +
          Real.log ((p.m - 1 : ℕ) : ℝ) + 1) := by
  have hd : 0 < ((p.m - 1 : ℕ) : ℝ) :=
    Nat.cast_pos.mpr (Nat.sub_pos_of_lt
      (lt_of_lt_of_le (by decide : 1 < 2) p.two_le_m))
  have hK : 0 < (p.K : ℝ) := Nat.cast_pos.mpr (ConstructorDimensions.K_pos p)
  have hk : PhaseServiceWaiting.kappa ≠ 0 :=
    ne_of_gt PhaseServiceWaiting.kappa_pos
  have hden :
      (8 : ℝ) * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ) ≠ 0 := by positivity
  field_simp [hk, hden]
  ring

/-- Integrability of the original uncapped handover charge and its waiting
exponential under the source product law. -/
theorem integrable_G_H :
    Integrable
      (ReferenceFirstLiveStoppedHandoverAdaptation.G_H
        rate rewards C_star C_h control0) mu := by
  have hcharge :=
    actual_waiting_totalCharge_integrable_exp rate rewards C_star C_h control0
  exact hcharge.1.congr (Filter.Eventually.of_forall fun z =>
    ReferenceFirstLiveStoppedHandoverAdaptation.totalCharge_eq_G_H
      rate rewards C_star C_h control0 z)

/-- The source exponential of the original uncapped handover charge is
integrable under the same source product law. -/
theorem integrable_exp_G_H :
    Integrable
      (fun z => Real.exp (PhaseServiceWaiting.kappa * aH *
        ReferenceFirstLiveStoppedHandoverAdaptation.G_H
          rate rewards C_star C_h control0 z)) mu := by
  have hcharge :=
    actual_waiting_totalCharge_integrable_exp rate rewards C_star C_h control0
  apply hcharge.2.congr
  filter_upwards [] with z
  rw [← ReferenceFirstLiveStoppedHandoverAdaptation.totalCharge_eq_G_H
    rate rewards C_star C_h control0 z]

/-- Conditional expectation of the actual `G_H` at the original source-prefix
phase-start sigma-algebra, with the manuscript constant. -/
theorem G_H_condExp_bound :
    mu[ReferenceFirstLiveStoppedHandoverAdaptation.G_H
      rate rewards C_star C_h control0 | phaseField] ≤ᵐ[mu] fun _ =>
      (8 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ) /
        PhaseServiceWaiting.kappa) *
        (2 * (AffineBatchDecoder.quota p : ℝ) +
          Real.log ((p.m - 1 : ℕ) : ℝ) + 1) := by
  have hwait :=
    actual_phase_start_totalCharge_condExp_bound rate rewards C_star C_h control0
  have hEq := ReferenceFirstLiveStoppedHandoverAdaptation.totalCharge_eq_G_H
    rate rewards C_star C_h control0
  have hCE := condExp_congr_ae (m := phaseField) (μ := mu)
    (Filter.Eventually.of_forall fun z => hEq z)
  have hconstant := waiting_constant_eq_source_constant (p := p)
  filter_upwards [hCE, hwait] with z hzEq hzBound
  calc
    mu[ReferenceFirstLiveStoppedHandoverAdaptation.G_H
        rate rewards C_star C_h control0 | phaseField] z =
      mu[PhaseServiceWaiting.totalCharge pending sigmaH thetaH gH p.T | phaseField] z :=
        hzEq.symm
    _ ≤ ((quotaH : ℝ) + Real.log ((p.m - 1 : ℕ) : ℝ)) /
        (PhaseServiceWaiting.kappa * aH) := hzBound
    _ = (8 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ) /
          PhaseServiceWaiting.kappa) *
        (2 * (AffineBatchDecoder.quota p : ℝ) +
          Real.log ((p.m - 1 : ℕ) : ℝ) + 1) := hconstant

/-- Localized mean handover cost on every set measurable at the actual
source-prefix phase-start field. -/
theorem G_H_setIntegral_bound
    (B : Set Source)
    (hB : MeasurableSet[phaseField] B) :
    ∫ z in B, ReferenceFirstLiveStoppedHandoverAdaptation.G_H
        rate rewards C_star C_h control0 z ∂mu ≤
      (8 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ) /
        PhaseServiceWaiting.kappa) *
        (2 * (AffineBatchDecoder.quota p : ℝ) +
          Real.log ((p.m - 1 : ℕ) : ℝ) + 1) *
        (BootstrapPrivateRoundStreams.sourceInputLaw p).real B := by
  have hwait := actual_phase_start_totalCharge_setIntegral_bound
    rate rewards C_star C_h control0 B hB
  have hEq := ReferenceFirstLiveStoppedHandoverAdaptation.totalCharge_eq_G_H
    rate rewards C_star C_h control0
  have hIntegralEq :
      ∫ z in B, ReferenceFirstLiveStoppedHandoverAdaptation.G_H
          rate rewards C_star C_h control0 z ∂mu =
        ∫ z in B, PhaseServiceWaiting.totalCharge pending sigmaH thetaH gH p.T z ∂mu := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun z => (hEq z).symm
  have hconstant := waiting_constant_eq_source_constant (p := p)
  calc
    ∫ z in B, ReferenceFirstLiveStoppedHandoverAdaptation.G_H
        rate rewards C_star C_h control0 z ∂mu =
      ∫ z in B, PhaseServiceWaiting.totalCharge pending sigmaH thetaH gH p.T z ∂mu :=
        hIntegralEq
    _ ≤ (((quotaH : ℝ) + Real.log ((p.m - 1 : ℕ) : ℝ)) /
        (PhaseServiceWaiting.kappa * aH)) *
        (BootstrapPrivateRoundStreams.sourceInputLaw p).real B := hwait
    _ = _ := by rw [hconstant]

/-- The original unconditional expected handover cost satisfies the same
source constant. -/
theorem G_H_expectation_bound :
    ∫ z, ReferenceFirstLiveStoppedHandoverAdaptation.G_H
      rate rewards C_star C_h control0 z ∂mu ≤
      (8 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ) /
        PhaseServiceWaiting.kappa) *
        (2 * (AffineBatchDecoder.quota p : ℝ) +
          Real.log ((p.m - 1 : ℕ) : ℝ) + 1) := by
  have h := G_H_setIntegral_bound rate rewards C_star C_h control0
    Set.univ MeasurableSet.univ
  have hmu : (BootstrapPrivateRoundStreams.sourceInputLaw p).real Set.univ = 1 := by
    simp [Measure.real]
  simpa only [MeasureTheory.setIntegral_univ, hmu, mul_one] using h

/-- The localized source exponential moment of the actual handover charge. -/
theorem G_H_exponential_setIntegral_bound
    (B : Set Source)
    (hB : MeasurableSet[phaseField] B) :
    ∫ z in B, Real.exp (PhaseServiceWaiting.kappa * aH *
      ReferenceFirstLiveStoppedHandoverAdaptation.G_H
        rate rewards C_star C_h control0 z) ∂mu ≤
      ((p.m - 1 : ℕ) : ℝ) * Real.exp (quotaH : ℝ) *
        (BootstrapPrivateRoundStreams.sourceInputLaw p).real B := by
  have hwait := actual_phase_start_totalCharge_exponential_setIntegral_bound
    rate rewards C_star C_h control0 B hB
  have hEq := ReferenceFirstLiveStoppedHandoverAdaptation.totalCharge_eq_G_H
    rate rewards C_star C_h control0
  have hIntegralEq :
      ∫ z in B, Real.exp (PhaseServiceWaiting.kappa * aH *
          ReferenceFirstLiveStoppedHandoverAdaptation.G_H
            rate rewards C_star C_h control0 z) ∂mu =
        ∫ z in B, Real.exp (PhaseServiceWaiting.kappa * aH *
          PhaseServiceWaiting.totalCharge pending sigmaH thetaH gH p.T z) ∂mu := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun z => by
      change Real.exp (PhaseServiceWaiting.kappa * aH *
          ReferenceFirstLiveStoppedHandoverAdaptation.G_H
            rate rewards C_star C_h control0 z) =
        Real.exp (PhaseServiceWaiting.kappa * aH *
          PhaseServiceWaiting.totalCharge pending sigmaH thetaH gH p.T z)
      rw [← hEq z]
  calc
    ∫ z in B, Real.exp (PhaseServiceWaiting.kappa * aH *
        ReferenceFirstLiveStoppedHandoverAdaptation.G_H
          rate rewards C_star C_h control0 z) ∂mu =
      ∫ z in B, Real.exp (PhaseServiceWaiting.kappa * aH *
        PhaseServiceWaiting.totalCharge pending sigmaH thetaH gH p.T z) ∂mu :=
        hIntegralEq
    _ ≤ ((p.m - 1 : ℕ) : ℝ) * Real.exp (quotaH : ℝ) *
      (BootstrapPrivateRoundStreams.sourceInputLaw p).real B := hwait

end Context

end Bandits.Support.ReferenceFirstLiveStoppedHandoverCost

end
