/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveHandoverPendingStagePartition
public import Bandits.Support.ReferenceFirstLiveHandoverConfirmationService
public import Bandits.Support.ReferenceFirstLiveStoppedHandoverAdaptation

/-!
# Actual conditional service on stopped first-handover sections

This module assembles the before-acceptance and accepted-but-unconfirmed
section service laws over the literal, uniquely partitioned stopped sections.
The observation and reward support remain those of the original physical run.

Sources: ZIP4 `05_binary_transport.tex:253-281` and
`06_interruptions.tex:431-490`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.ReferenceFirstLiveHandoverBoundaryFactorization
open scoped BigOperators Classical ENNReal

namespace Bandits.Support.ReferenceFirstLiveStoppedHandoverSectionService

section Context

variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)

local notation "Source" => BootstrapPrivateRoundStreams.SourceInput p
local notation "mu" => BootstrapPrivateRoundStreams.sourceInputLaw p
local notation "H" =>
  ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0

/-- The literal before or after source section, restricted by the strict
first-excluded stop mask used in the stopped pending-stage partition. -/
def stoppedSection (t : Fin p.T) (i : Fin (p.m - 1))
    (a : Bool × Fin (M p) × Fin (t.val + 1)) : Set Source :=
  (if a.1 then
      E_after rate rewards C_star C_h a.2.1 a.2.2.val t i
    else
      E_before rate rewards C_star C_h a.2.1 a.2.2.val t i) ∩
    {z | t.val + 1 < ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstExcluded
      rate rewards C_star C_h z}

/-- The actual finite strong-indicator service sum over the same stopped
sections that partition the pending set. -/
def stoppedSectionObservation (t : Fin p.T) (i : Fin (p.m - 1)) (z : Source) : ℝ :=
  ∑ a : Bool × Fin (M p) × Fin (t.val + 1),
    (if z ∈ stoppedSection rate rewards C_star C_h t i a then (1 : ℝ) else 0) *
      (if (if a.1 then V_after rate rewards C_star C_h i t z
        else V_before rate rewards C_star C_h i t z) then (1 : ℝ) else 0)

include control0 in
private theorem stoppedSection_summand_integrable
    (t : Fin p.T) (i : Fin (p.m - 1))
    (a : Bool × Fin (M p) × Fin (t.val + 1)) :
    Integrable (fun z : Source =>
      (if z ∈ stoppedSection rate rewards C_star C_h t i a then (1 : ℝ) else 0) *
        (if (if a.1 then V_after rate rewards C_star C_h i t z
          else V_before rate rewards C_star C_h i t z) then (1 : ℝ) else 0)) mu := by
  classical
  let V : Source → Prop := fun z =>
    if a.1 then V_after rate rewards C_star C_h i t z
    else V_before rate rewards C_star C_h i t z
  let S : Set Source := stoppedSection rate rewards C_star C_h t i a
  let v : Source → ℝ := fun z => if V z then (1 : ℝ) else 0
  have hVset : MeasurableSet {z : Source | V z} := by
    cases htag : a.1
    · simpa [V, htag] using
        (ReferenceFirstLiveHandoverBoundaryFactorization.measurableSet_V_before
          rate rewards C_star C_h i t)
    · simpa [V, htag] using
        (ReferenceFirstLiveHandoverBoundaryFactorization.measurableSet_V_after
          rate rewards C_star C_h i t)
  have hVint : Integrable v mu := by
    convert ((integrable_const (μ := mu) (1 : ℝ)).indicator hVset) using 1
    funext z
    simp [v, Set.indicator_apply]
  have hSset : MeasurableSet[H (t.val + 1)] S := by
    cases htag : a.1
    · have hn := ReferenceFirstLiveHandoverNoGateStopMask.measurableSet_E_before_stopped
        rate rewards C_star C_h control0 a.2.1 a.2.2.val t
        (Nat.le_of_lt_succ a.2.2.isLt) i
      have hEq : ({z : Source | z ∈ E_before rate rewards C_star C_h a.2.1
          a.2.2.val t i ∧ t.val + 1 <
            ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstExcluded
              rate rewards C_star C_h z} : Set Source) = S := by
        ext z
        simp [S, stoppedSection, htag]
      rw [← hEq]
      exact hn
    · have hn := ReferenceFirstLiveHandoverNoGateStopMask.measurableSet_E_after_stopped
        rate rewards C_star C_h control0 a.2.1 a.2.2.val t
        (Nat.le_of_lt_succ a.2.2.isLt) i
      have hEq : ({z : Source | z ∈ E_after rate rewards C_star C_h a.2.1
          a.2.2.val t i ∧ t.val + 1 <
            ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstExcluded
              rate rewards C_star C_h z} : Set Source) = S := by
        ext z
        simp [S, stoppedSection, htag]
      rw [← hEq]
      exact hn
  have hSambient : MeasurableSet S :=
    (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).le
      (t.val + 1) _ hSset
  let f : Source → ℝ := fun z => if z ∈ S then (1 : ℝ) else 0
  have hfint : Integrable (fun z => f z * v z) mu := by
    have h := hVint.indicator hSambient
    convert h using 1
    funext z
    by_cases hz : z ∈ S
    · simp [f, v, hz]
    · simp [f, v, hz]
  convert hfint using 1

/-- Integrability of the literal full finite stopped-section service sum. -/
theorem integrable_stoppedSectionObservation
    (control : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) (i : Fin (p.m - 1)) :
    Integrable (stoppedSectionObservation rate rewards C_star C_h t i) mu := by
  classical
  unfold stoppedSectionObservation
  apply integrable_finsetSum
  intro a ha
  exact stoppedSection_summand_integrable rate rewards C_star C_h control t i a

private theorem stoppedSection_summand_condExp
    (t : Fin p.T) (i : Fin (p.m - 1))
    (a : Bool × Fin (M p) × Fin (t.val + 1)) :
    mu[(fun z : Source =>
      (if z ∈ stoppedSection rate rewards C_star C_h t i a then (1 : ℝ) else 0) *
        (if (if a.1 then V_after rate rewards C_star C_h i t z
          else V_before rate rewards C_star C_h i t z) then (1 : ℝ) else 0)) |
        H (t.val + 1)] =ᵐ[mu] fun z =>
          (if z ∈ stoppedSection rate rewards C_star C_h t i a then (1 : ℝ) else 0) *
            (((Finset.univ.filter fun b : Fin p.K => 0 < (rewards t b).val).card : ℝ) /
              (8 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ))) := by
  classical
  let E : Set Source := if a.1 then
    E_after rate rewards C_star C_h a.2.1 a.2.2.val t i
    else E_before rate rewards C_star C_h a.2.1 a.2.2.val t i
  let V : Source → Prop := fun z =>
    if a.1 then V_after rate rewards C_star C_h i t z
    else V_before rate rewards C_star C_h i t z
  let S : Set Source := stoppedSection rate rewards C_star C_h t i a
  let f : Source → ℝ := fun z => if z ∈ S then (1 : ℝ) else 0
  let e : Source → ℝ := fun z => if z ∈ E then (1 : ℝ) else 0
  let v : Source → ℝ := fun z => if V z then (1 : ℝ) else 0
  let c : ℝ :=
    ((Finset.univ.filter fun b : Fin p.K => 0 < (rewards t b).val).card : ℝ) /
      (8 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ))
  have hSset : MeasurableSet[H (t.val + 1)] S := by
    cases htag : a.1
    · have hn := ReferenceFirstLiveHandoverNoGateStopMask.measurableSet_E_before_stopped
        rate rewards C_star C_h control0 a.2.1 a.2.2.val t
        (Nat.le_of_lt_succ a.2.2.isLt) i
      have hEq : ({z : Source | z ∈ E_before rate rewards C_star C_h a.2.1
          a.2.2.val t i ∧ t.val + 1 <
            ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstExcluded
              rate rewards C_star C_h z} : Set Source) = S := by
        ext z
        simp [S, stoppedSection, htag]
      rw [← hEq]
      exact hn
    · have hn := ReferenceFirstLiveHandoverNoGateStopMask.measurableSet_E_after_stopped
        rate rewards C_star C_h control0 a.2.1 a.2.2.val t
        (Nat.le_of_lt_succ a.2.2.isLt) i
      have hEq : ({z : Source | z ∈ E_after rate rewards C_star C_h a.2.1
          a.2.2.val t i ∧ t.val + 1 <
            ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstExcluded
              rate rewards C_star C_h z} : Set Source) = S := by
        ext z
        simp [S, stoppedSection, htag]
      rw [← hEq]
      exact hn
  have hSambient : MeasurableSet S :=
    (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).le
      (t.val + 1) _ hSset
  have hSE : S ⊆ E := by
    intro z hz
    exact hz.1
  have hVset : MeasurableSet {z : Source | V z} := by
    cases htag : a.1
    · simpa [V, htag] using
        (ReferenceFirstLiveHandoverBoundaryFactorization.measurableSet_V_before
          rate rewards C_star C_h i t)
    · simpa [V, htag] using
        (ReferenceFirstLiveHandoverBoundaryFactorization.measurableSet_V_after
          rate rewards C_star C_h i t)
  have hVint : Integrable v mu := by
    convert ((integrable_const (μ := mu) (1 : ℝ)).indicator hVset) using 1
    funext z
    simp [v, Set.indicator_apply]
  have hEset : MeasurableSet E := by
    cases htag : a.1
    · have hs : a.2.2.val ≤ t.val := Nat.le_of_lt_succ a.2.2.isLt
      exact (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).le
        (t.val + 1) _
        (by simpa [E, htag] using
          (ReferenceFirstLiveHandoverBoundaryFactorization.measurableSet_E_before
            rate rewards C_star C_h control0 a.2.1 a.2.2.val t hs i))
    · have hs : a.2.2.val ≤ t.val := Nat.le_of_lt_succ a.2.2.isLt
      exact (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).le
        (t.val + 1) _
        (by simpa [E, htag] using
          (ReferenceFirstLiveHandoverBoundaryFactorization.measurableSet_E_after
            rate rewards C_star C_h control0 a.2.1 a.2.2.val t hs i))
  have hEVint : Integrable (fun z => e z * v z) mu := by
    have h := hVint.indicator hEset
    convert h using 1
    funext z
    by_cases hz : z ∈ E <;> simp [e, v, hz]
  have hfevint : Integrable (fun z => f z * (e z * v z)) mu := by
    have h := hEVint.indicator hSambient
    convert h using 1
    funext z
    by_cases hz : z ∈ S
    · have hze := hSE hz
      simp [f, e, v, hz, hze]
    · simp [f, e, v, hz]
  have hfStrong : StronglyMeasurable[H (t.val + 1)] f := by
    change StronglyMeasurable[H (t.val + 1)]
      (S.indicator fun _ : Source => (1 : ℝ))
    exact stronglyMeasurable_const.indicator hSset
  have hpull := condExp_mul_of_stronglyMeasurable_left hfStrong hfevint hEVint
  have hraw :
      mu[(fun z => e z * v z) | H (t.val + 1)] =ᵐ[mu] fun z => e z * c := by
    have hs : a.2.2.val ≤ t.val := Nat.le_of_lt_succ a.2.2.isLt
    cases htag : a.1
    · simpa [E, V, e, v, c, htag] using
        (ReferenceFirstLiveHandoverBeforeDownService.before_service_condExp
          rate rewards C_star C_h control0 a.2.1 t a.2.2.val hs i)
    · simpa [E, V, e, v, c, htag] using
        (ReferenceFirstLiveHandoverConfirmationService.after_service_condExp
          rate rewards C_star C_h control0 a.2.1 t a.2.2.val hs i)
  have htermEq :
      (fun z => (if z ∈ S then (1 : ℝ) else 0) *
        (if V z then (1 : ℝ) else 0)) =ᵐ[mu] (fun z => f z * (e z * v z)) :=
    Filter.Eventually.of_forall (fun z => by
      by_cases hz : z ∈ S
      · have hze := hSE hz
        simp [f, e, v, hz, hze]
      · simp [f, e, v, hz])
  have hce := condExp_congr_ae (m := H (t.val + 1)) (μ := mu) htermEq
  filter_upwards [hce, hpull, hraw] with z hcez hpz hrawz
  rw [hcez]
  change mu[(f * fun z => e z * v z) | H (t.val + 1)] z = _
  rw [hpz]
  change f z * mu[fun z => e z * v z | H (t.val + 1)] z = _
  rw [hrawz]
  by_cases hz : z ∈ S
  · have hze := hSE hz
    simp [S, f, e, hz, hze, c]
  · simp [S, f, hz, c]

/-- The finite stopped-section sum has the actual conditional service law.
The coefficient is the positive integer-grid arm count divided by the source
service denominator, with no normalization by section mass. -/
theorem stoppedSectionObservation_condExp
    (t : Fin p.T) (i : Fin (p.m - 1)) :
    mu[stoppedSectionObservation rate rewards C_star C_h t i |
      H (t.val + 1)] =ᵐ[mu] fun z =>
        (if i ∈ ReferenceFirstLiveSourceStoppedHandoverEndpoint.pendingNat
          rate rewards C_star C_h t.val z then (1 : ℝ) else 0) *
          (((Finset.univ.filter fun b : Fin p.K => 0 < (rewards t b).val).card : ℝ) /
            (8 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ))) := by
  classical
  let I := Bool × Fin (M p) × Fin (t.val + 1)
  let f : I → Source → ℝ := fun a z =>
    (if z ∈ stoppedSection rate rewards C_star C_h t i a then (1 : ℝ) else 0) *
      (if (if a.1 then V_after rate rewards C_star C_h i t z
        else V_before rate rewards C_star C_h i t z) then (1 : ℝ) else 0)
  let c : ℝ :=
    ((Finset.univ.filter fun b : Fin p.K => 0 < (rewards t b).val).card : ℝ) /
      (8 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ))
  have hsumCE :
      mu[(fun z => ∑ a : I, f a z) | H (t.val + 1)] =ᵐ[mu] fun z =>
        ∑ a : I, mu[f a | H (t.val + 1)] z := by
    convert (condExp_finsetSum (μ := mu) (s := Finset.univ) (f := f)
      (fun a ha => stoppedSection_summand_integrable
        rate rewards C_star C_h control0 t i a) (H (t.val + 1))) using 1
    · congr 1
      funext z
      simp
    · ext z
      simp
  have hterms : ∀ᵐ z ∂mu, ∀ a : I,
      mu[f a | H (t.val + 1)] z =
        (if z ∈ stoppedSection rate rewards C_star C_h t i a then (1 : ℝ) else 0) * c := by
    apply ae_all_iff.mpr
    intro a
    filter_upwards [stoppedSection_summand_condExp
      rate rewards C_star C_h control0 t i a] with z hz
    simpa [f, c] using hz
  have hL : stoppedSectionObservation rate rewards C_star C_h t i =
      (fun z => ∑ a : I, f a z) := by
    funext z
    rfl
  have hLCE :
      mu[stoppedSectionObservation rate rewards C_star C_h t i | H (t.val + 1)] =ᵐ[mu]
        mu[(fun z => ∑ a : I, f a z) | H (t.val + 1)] :=
    condExp_congr_ae (m := H (t.val + 1)) (μ := mu)
      (Filter.Eventually.of_forall fun z => congrFun hL z)
  have hpartition : ∀ z : Source,
      (if i ∈ ReferenceFirstLiveSourceStoppedHandoverEndpoint.pendingNat
          rate rewards C_star C_h t.val z then (1 : ℝ) else 0) =
        ∑ a : I, if z ∈ stoppedSection rate rewards C_star C_h t i a
          then (1 : ℝ) else 0 := by
    intro z
    simpa [I, stoppedSection] using
      (ReferenceFirstLiveHandoverPendingStagePartition.pending_stopped_section_partition_indicator
        rate rewards C_star C_h t i z)
  filter_upwards [hLCE, hsumCE, hterms] with z hLz hsum hterm
  calc
    mu[stoppedSectionObservation rate rewards C_star C_h t i | H (t.val + 1)] z =
        mu[(fun w => ∑ a : I, f a w) | H (t.val + 1)] z := hLz
    _ = (∑ a : I, mu[f a | H (t.val + 1)] z) := hsum
    _ =
        ∑ a : I, (if z ∈ stoppedSection rate rewards C_star C_h t i a
          then (1 : ℝ) else 0) * c := by
            apply Finset.sum_congr rfl
            intro a ha
            exact hterm a
    _ = (∑ a : I, if z ∈ stoppedSection rate rewards C_star C_h t i a
          then (1 : ℝ) else 0) * c := by rw [Finset.sum_mul]
    _ = (if i ∈ ReferenceFirstLiveSourceStoppedHandoverEndpoint.pendingNat
          rate rewards C_star C_h t.val z then (1 : ℝ) else 0) * c := by
            rw [← hpartition z]
    _ = _ := by rfl

/-- On every original source point, the finite stopped-section sum is the
literal waiting-process observation of the accepted adaptation's same `X_H`. -/
theorem stoppedSectionObservation_eq_X_H_observation
    (t : Fin p.T) (i : Fin (p.m - 1)) (z : Source) :
    stoppedSectionObservation rate rewards C_star C_h t i z =
      PhaseServiceWaiting.observation
        (ReferenceFirstLiveStoppedHandoverAdaptation.X_H rate rewards C_star C_h control0)
        i t.val z := by
  classical
  let I := Bool × Fin (M p) × Fin (t.val + 1)
  let S : I → Set Source := fun a => stoppedSection rate rewards C_star C_h t i a
  let V : I → Source → Prop := fun a z =>
    if a.1 then V_after rate rewards C_star C_h i t z
    else V_before rate rewards C_star C_h i t z
  have hx :
      ReferenceFirstLiveStoppedHandoverAdaptation.X_H rate rewards C_star C_h control0
        i t.val z = true ↔ ∃ a : I, z ∈ S a ∧ V a z := by
    rw [ReferenceFirstLiveStoppedHandoverAdaptation.X_H_true_iff_stopped_sections]
    constructor
    · rintro (⟨⟨q, s, he⟩, hstop, hv⟩ | ⟨⟨q, s, he⟩, hstop, hv⟩)
      · refine ⟨(false, q, s), ?_, ?_⟩
        · simpa [S, stoppedSection] using And.intro he hstop
        · simpa [V] using hv
      · refine ⟨(true, q, s), ?_, ?_⟩
        · simpa [S, stoppedSection] using And.intro he hstop
        · simpa [V] using hv
    · rintro ⟨a, ha, hv⟩
      rcases a with ⟨tag, q, s⟩
      cases tag
      · have hstop : t.val + 1 <
          ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstExcluded
            rate rewards C_star C_h z := by
          simpa [S, stoppedSection] using ha.2
        have hE : z ∈ E_before rate rewards C_star C_h q s.val t i := by
          simpa [S, stoppedSection] using ha.1
        exact Or.inl ⟨⟨q, s, hE⟩, hstop, by simpa [V] using hv⟩
      · have hstop : t.val + 1 <
          ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstExcluded
            rate rewards C_star C_h z := by
          simpa [S, stoppedSection] using ha.2
        have hE : z ∈ E_after rate rewards C_star C_h q s.val t i := by
          simpa [S, stoppedSection] using ha.1
        exact Or.inr ⟨⟨q, s, hE⟩, hstop, by simpa [V] using hv⟩
  have hpartition :
      i ∈ ReferenceFirstLiveSourceStoppedHandoverEndpoint.pendingNat
        rate rewards C_star C_h t.val z ↔ ∃! a : I, z ∈ S a := by
    simpa only [I, S, stoppedSection] using
      (ReferenceFirstLiveHandoverPendingStagePartition.pending_stopped_section_partition
        rate rewards C_star C_h t i z)
  have hsum :
      (∑ a : I, (if z ∈ S a then (1 : ℝ) else 0) *
        (if V a z then (1 : ℝ) else 0)) =
      (if ReferenceFirstLiveStoppedHandoverAdaptation.X_H rate rewards C_star C_h
        control0 i t.val z then (1 : ℝ) else 0) := by
    by_cases hX : ReferenceFirstLiveStoppedHandoverAdaptation.X_H
        rate rewards C_star C_h control0 i t.val z = true
    · obtain ⟨a, haS, haV⟩ := hx.mp hX
      have hXpending := hX
      rw [ReferenceFirstLiveStoppedHandoverAdaptation.X_H_eq_decide
        rate rewards C_star C_h control0 i t z] at hXpending
      simp only [decide_eq_true_eq] at hXpending
      obtain ⟨a0, ha0, huniq⟩ := hpartition.mp hXpending.1
      have haEq : a = a0 := huniq a haS
      subst a
      calc
        (∑ b : I, (if z ∈ S b then (1 : ℝ) else 0) *
            (if V b z then (1 : ℝ) else 0)) =
            (if z ∈ S a0 then (1 : ℝ) else 0) * (if V a0 z then (1 : ℝ) else 0) :=
          Finset.sum_eq_single_of_mem a0 (Finset.mem_univ a0) (by
            intro b _hb hne
            have hnot : z ∉ S b := fun hb => hne (huniq b hb)
            simp [hnot])
        _ = 1 := by simp [ha0, haV]
        _ = (if ReferenceFirstLiveStoppedHandoverAdaptation.X_H
              rate rewards C_star C_h control0 i t.val z then (1 : ℝ) else 0) := by
                simp [hX]
    · rw [ite_eq_right hX]
      apply Finset.sum_eq_zero
      intro a ha
      by_cases hS : z ∈ S a
      · by_cases hV : V a z
        · exact False.elim (hX (hx.mpr ⟨a, hS, hV⟩))
        · simp [hS, hV]
      · simp [hS]
  rw [show stoppedSectionObservation rate rewards C_star C_h t i z =
      ∑ a : I, (if z ∈ S a then (1 : ℝ) else 0) * (if V a z then (1 : ℝ) else 0) by rfl,
    hsum,
    ReferenceFirstLiveStoppedHandoverAdaptation.observation_eq_X_H
      rate rewards C_star C_h control0 i t.val]

/-- Integrability of the actual `X_H` observation on the whole original
source follows from its pointwise finite stopped-section representation. -/
theorem integrable_X_H_observation
    (t : Fin p.T) (i : Fin (p.m - 1)) :
    Integrable
      (PhaseServiceWaiting.observation
        (ReferenceFirstLiveStoppedHandoverAdaptation.X_H rate rewards C_star C_h control0)
        i t.val) mu := by
  have hEq := stoppedSectionObservation_eq_X_H_observation
    rate rewards C_star C_h control0 t i
  exact (integrable_stoppedSectionObservation rate rewards C_star C_h control0 t i).congr
    (Filter.Eventually.of_forall fun z => hEq z)

/-- The actual `X_H` waiting observation has the same exact source-prefix
conditional law, including zero-mass and strict-stop branches. -/
theorem X_H_observation_condExp
    (t : Fin p.T) (i : Fin (p.m - 1)) :
    mu[PhaseServiceWaiting.observation
      (ReferenceFirstLiveStoppedHandoverAdaptation.X_H rate rewards C_star C_h control0)
      i t.val | H (t.val + 1)] =ᵐ[mu] fun z =>
        (if i ∈ ReferenceFirstLiveSourceStoppedHandoverEndpoint.pendingNat
          rate rewards C_star C_h t.val z then (1 : ℝ) else 0) *
          (((Finset.univ.filter fun b : Fin p.K => 0 < (rewards t b).val).card : ℝ) /
            (8 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ))) := by
  have hEq := stoppedSectionObservation_eq_X_H_observation
    rate rewards C_star C_h control0 t i
  have hCE := condExp_congr_ae (m := H (t.val + 1)) (μ := mu)
    (Filter.Eventually.of_forall fun z => hEq z)
  exact hCE.symm.trans (stoppedSectionObservation_condExp
    rate rewards C_star C_h control0 t i)

/-- Direct service input for the phase-start waiting theorem, with the same
actual stopped observation and deterministic original reward support. -/
theorem phaseStart_hservice
    (k : ℕ) (hk : k < p.T) (i : Fin (p.m - 1)) :
    ∀ᵐ z ∂mu,
      i ∈ ReferenceFirstLiveSourceStoppedHandoverEndpoint.pendingNat
        rate rewards C_star C_h k z →
      (1 / (8 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ))) *
          ReferenceFirstLiveStoppedHandoverAdaptation.g_H
            rate rewards C_star C_h control0 k z ≤
        mu[PhaseServiceWaiting.observation
          (ReferenceFirstLiveStoppedHandoverAdaptation.X_H rate rewards C_star C_h control0)
          i k | H (k + 1)] z := by
  let t : Fin p.T := ⟨k, hk⟩
  have hLaw := X_H_observation_condExp rate rewards C_star C_h control0 t i
  have hcard := ReferenceFirstLiveStoppedHandoverAdaptation.g_H_eq_card
    rate rewards C_star C_h control0 t
  have hden : (0 : ℝ) <
      8 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ) := by
    have hm : 0 < p.m - 1 := Nat.sub_pos_of_lt
      (lt_of_lt_of_le (by decide : 1 < 2) p.two_le_m)
    exact mul_pos (mul_pos (by norm_num) (Nat.cast_pos.mpr hm))
      (Nat.cast_pos.mpr (ConstructorDimensions.K_pos p))
  filter_upwards [hLaw] with z hz
  intro hpending
  have hpending' : i ∈ ReferenceFirstLiveSourceStoppedHandoverEndpoint.pendingNat
      rate rewards C_star C_h t.val z := by
    simpa [t] using hpending
  have hIndicator :
      (if i ∈ ReferenceFirstLiveSourceStoppedHandoverEndpoint.pendingNat
        rate rewards C_star C_h t.val z then (1 : ℝ) else 0) = 1 := by
    simp [hpending']
  have hCond := hz
  rw [hIndicator] at hCond
  have hWeight :
      (1 / (8 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ))) *
          ReferenceFirstLiveStoppedHandoverAdaptation.g_H
            rate rewards C_star C_h control0 k z =
        ((Finset.univ.filter fun b : Fin p.K => 0 < (rewards t b).val).card : ℝ) /
          (8 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ)) := by
    rw [show k = t.val by rfl, hcard z]
    field_simp [ne_of_gt hden]
  rw [hWeight]
  have hCondLe :
      ((Finset.univ.filter fun b : Fin p.K => 0 < (rewards t b).val).card : ℝ) /
          (8 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ)) ≤
        mu[PhaseServiceWaiting.observation
          (ReferenceFirstLiveStoppedHandoverAdaptation.X_H rate rewards C_star C_h control0)
          i k | H (k + 1)] z := by
    simpa [t] using hCond.symm.le
  exact hCondLe

end Context

end Bandits.Support.ReferenceFirstLiveStoppedHandoverSectionService

end
