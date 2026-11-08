/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCompleteOrdinaryWrongCompletionCharacterization
public import Bandits.Support.ReferencePrelaunchDecoderIndexLocality

import Lean.Elab.Tactic.Omega

/-!
# Borel and selected-row locality of the actual ordinary wrong-completion event

This module observes the full original-source ordinary unique wrong completed
batch event. Its calendar prefix is untruncated; no physical overflow cutoff
is applied here.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.CompletePublicTable
open Bandits.Support.BootstrapPrivateRoundStreams

namespace Bandits.Support.ReferenceCompleteOrdinaryFalseEventObservableLocality

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev SourceInput (p : Parameters) := BootstrapPrivateRoundStreams.SourceInput p

variable {p : Parameters} (rate : RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ)

local instance : MeasurableSpace (CoordinatorPhaseClock.StartRoundResult p) := ⊤

private abbrev RecordCode (r : RateInput p) :=
  ReferenceActiveHorizonMeasurability.RoundRecordCode (p := p) (rate := r)

/-- The actual prelaunch ordinary wrong-completion bit, formed from the
original per-follower decision bits. -/
def ordinaryPrelaunchWrongCompletionAtBool
    (t : Fin p.T) (z : SourceInput p) : Bool :=
  decide (∃ i : Fin (p.m - 1),
    ReferencePrelaunchDownDecisionReadout.prelaunchDownFailureAt
      rate rewards C_star C_h z i t = true)

/-- The saved wrong-unique diagnostic on the actual optional postlaunch
record at its original calendar date. Absence remains false. -/
def ordinaryPostlaunchWrongCompletionAtBool
    (t : Fin p.T) (z : SourceInput p) : Bool :=
  (ReferenceInspectedPastRoundObservations.pastRoundObservations
    rate rewards C_star C_h p.T (Nat.le_refl p.T) z t).elim false
      ReferenceSavedWrongUniqueMeasurability.savedWrongCode

/-- The Boolean observation of the actual full-source ordinary event. -/
def ordinaryWrongCompletionAtObserved
    (t : Fin p.T) (z : SourceInput p) : Bool :=
  ordinaryPrelaunchWrongCompletionAtBool rate rewards C_star C_h t z ||
    ordinaryPostlaunchWrongCompletionAtBool rate rewards C_star C_h t z

private theorem ordinaryPostlaunchWrongCompletionAtBool_eq_true_iff
    (t : Fin p.T) (z : SourceInput p) :
    ordinaryPostlaunchWrongCompletionAtBool rate rewards C_star C_h t z = true ↔
      ∃ r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate),
        ReferenceSourcePrefixHistoryFiltration.actualRecord
          rate rewards C_star C_h t z = some r ∧
        ReferenceGeneratedSavedWrongEvent.savedWrongRecordFlag r = true := by
  unfold ordinaryPostlaunchWrongCompletionAtBool
  change ((ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t z).map
      ReferenceActiveHorizonMeasurability.roundRecordCode).elim false
        ReferenceSavedWrongUniqueMeasurability.savedWrongCode = true ↔ _
  cases hr : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t z with
  | none => simp
  | some r =>
      simp only [Option.map_some, Option.elim_some,
        ReferenceSavedWrongUniqueMeasurability.savedWrongCode_roundRecord_iff,
        Option.some.injEq]
      simp [ReferenceGeneratedSavedWrongEvent.savedWrongRecordFlag]

/-- The Boolean observer is equivalent to W's actual prelaunch union and
actual completed-record diagnostic characterization. -/
theorem ordinaryWrongCompletionAt_observed_iff
    (t : Fin p.T) (z : SourceInput p) :
    ReferenceCompleteOrdinaryWrongCompletionCharacterization.ordinaryWrongCompletionAt
        rate rewards C_star C_h t z ↔
      ordinaryWrongCompletionAtObserved rate rewards C_star C_h t z = true := by
  rw [ReferenceCompleteOrdinaryWrongCompletionCharacterization.ordinaryWrongCompletionAt_iff]
  simp [ordinaryWrongCompletionAtObserved, ordinaryPrelaunchWrongCompletionAtBool,
    ordinaryPostlaunchWrongCompletionAtBool_eq_true_iff, decide_eq_true_eq]

private theorem measurable_ordinaryPrelaunchWrongCompletionAtBool
    (t : Fin p.T) :
    Measurable (ordinaryPrelaunchWrongCompletionAtBool rate rewards C_star C_h t) := by
  have hbits : Measurable (fun z : SourceInput p => fun i : Fin (p.m - 1) =>
      ReferencePrelaunchDownDecisionReadout.prelaunchDownFailureAt
        rate rewards C_star C_h z i t) := by
    apply measurable_pi_iff.mpr
    intro i
    exact ReferencePrelaunchInspectedDecoderPast.prelaunchDownFailureAt_measurable
      rate rewards C_star C_h p.T (Nat.le_refl p.T) t t.isLt i
  have hfold : Measurable (fun f : Fin (p.m - 1) → Bool =>
      decide (∃ i, f i = true)) := measurable_of_finite _
  exact hfold.comp hbits

private theorem measurable_ordinaryPostlaunchWrongCompletionAtBool
    (t : Fin p.T) :
    Measurable (ordinaryPostlaunchWrongCompletionAtBool rate rewards C_star C_h t) := by
  have hround : Measurable (fun z : SourceInput p =>
      ReferenceInspectedPastRoundObservations.pastRoundObservations
        rate rewards C_star C_h p.T (Nat.le_refl p.T) z) :=
    ReferenceInspectedPastRoundObservations.measurable_pastRoundObservations
      rate rewards C_star C_h p.T (Nat.le_refl p.T)
  have hdate := (measurable_pi_iff.mp hround) t
  have hoption : Measurable (fun code : Option (RecordCode rate) =>
      code.elim false ReferenceSavedWrongUniqueMeasurability.savedWrongCode) := by
    have hsum := (ReferenceSavedWrongUniqueMeasurability.measurable_savedWrongCode
      (p := p) (rate := rate)).sumElim
        (measurable_const : Measurable (fun _ : PUnit => false))
    convert hsum.comp (comap_measurable (Equiv.optionEquivSumPUnit (RecordCode rate))) using 1
    funext code
    cases code <;> rfl
  exact hoption.comp hdate

/-- The date-wise Boolean observer is Borel on the original whole-source
measurable space. -/
theorem ordinaryWrongCompletionAt_observed_measurable
    (t : Fin p.T) :
    Measurable (ordinaryWrongCompletionAtObserved rate rewards C_star C_h t) := by
  have hpre := measurable_ordinaryPrelaunchWrongCompletionAtBool
    (rate := rate) (rewards := rewards) C_star C_h t
  have hpost := measurable_ordinaryPostlaunchWrongCompletionAtBool
    (rate := rate) (rewards := rewards) C_star C_h t
  exact (measurable_of_finite (fun b : Bool × Bool => b.1 || b.2)).comp
    (hpre.prodMk hpost)

/-- The date-wise ordinary event is a Borel set on the original whole-source
space. -/
theorem ordinaryWrongCompletionAt_measurableSet
    (t : Fin p.T) :
    MeasurableSet {z : SourceInput p |
      ReferenceCompleteOrdinaryWrongCompletionCharacterization.ordinaryWrongCompletionAt
        rate rewards C_star C_h t z} := by
  have hobs := ordinaryWrongCompletionAt_observed_measurable
    (rate := rate) (rewards := rewards) C_star C_h t
  have heq : {z : SourceInput p |
      ReferenceCompleteOrdinaryWrongCompletionCharacterization.ordinaryWrongCompletionAt
        rate rewards C_star C_h t z} =
      (ordinaryWrongCompletionAtObserved rate rewards C_star C_h t) ⁻¹' {true} := by
    ext z
    exact ordinaryWrongCompletionAt_observed_iff rate rewards C_star C_h t z
  rw [heq]
  exact measurableSet_preimage hobs (measurableSet_singleton true)

/-- The actual untruncated finite calendar prefix of the full-source event.
There is no overflow or stopping premise in this definition. -/
def ordinaryWrongCompletionPrefix
    (n : ℕ) (z : SourceInput p) : Prop :=
  ∃ t : Fin p.T, t.val < n ∧
    ReferenceCompleteOrdinaryWrongCompletionCharacterization.ordinaryWrongCompletionAt
      rate rewards C_star C_h t z

/-- The Boolean observation of the finite calendar prefix. -/
def ordinaryWrongCompletionPrefixObserved
    (n : ℕ) (z : SourceInput p) : Bool :=
  by
    classical
    exact decide (ordinaryWrongCompletionPrefix rate rewards C_star C_h n z)

theorem ordinaryWrongCompletionPrefixObserved_iff
    (n : ℕ) (z : SourceInput p) :
    ordinaryWrongCompletionPrefixObserved rate rewards C_star C_h n z = true ↔
      ordinaryWrongCompletionPrefix rate rewards C_star C_h n z := by
  classical
  simp [ordinaryWrongCompletionPrefixObserved]

theorem ordinaryWrongCompletionPrefix_zero
    (z : SourceInput p) :
    ordinaryWrongCompletionPrefix rate rewards C_star C_h 0 z ↔ False := by
  simp [ordinaryWrongCompletionPrefix]

/-- The successor scan includes the current update at calendar date `n`. -/
theorem ordinaryWrongCompletionPrefix_succ_iff
    (n : ℕ) (hn : n < p.T) (z : SourceInput p) :
    ordinaryWrongCompletionPrefix rate rewards C_star C_h (n + 1) z ↔
      ordinaryWrongCompletionPrefix rate rewards C_star C_h n z ∨
        ReferenceCompleteOrdinaryWrongCompletionCharacterization.ordinaryWrongCompletionAt
          rate rewards C_star C_h ⟨n, hn⟩ z := by
  constructor
  · rintro ⟨t, ht, hbad⟩
    by_cases hbefore : t.val < n
    · exact Or.inl ⟨t, hbefore, hbad⟩
    · have hval : t.val = n := by omega
      have htime : t = ⟨n, hn⟩ := Fin.ext hval
      subst t
      exact Or.inr hbad
  · rintro (⟨t, ht, hbad⟩ | hbad)
    · exact ⟨t, Nat.lt_trans ht (Nat.lt_succ_self n), hbad⟩
    · refine ⟨⟨n, hn⟩, ?_, hbad⟩
      change n < n + 1
      exact Nat.lt_succ_self n

theorem ordinaryWrongCompletionPrefixObserved_zero
    (z : SourceInput p) :
    ordinaryWrongCompletionPrefixObserved rate rewards C_star C_h 0 z = false := by
  classical
  simp [ordinaryWrongCompletionPrefixObserved,
    ordinaryWrongCompletionPrefix_zero]

theorem ordinaryWrongCompletionPrefixObserved_succ
    (n : ℕ) (hn : n < p.T) (z : SourceInput p) :
    ordinaryWrongCompletionPrefixObserved rate rewards C_star C_h (n + 1) z =
      (ordinaryWrongCompletionPrefixObserved rate rewards C_star C_h n z ||
        ordinaryWrongCompletionAtObserved rate rewards C_star C_h ⟨n, hn⟩ z) := by
  have hscan := ordinaryWrongCompletionPrefix_succ_iff
    (rate := rate) (rewards := rewards) C_star C_h n hn z
  have hdated := ordinaryWrongCompletionAt_observed_iff
    (rate := rate) (rewards := rewards) C_star C_h ⟨n, hn⟩ z
  have hprev : ordinaryWrongCompletionPrefixObserved rate rewards C_star C_h n z =
      true ↔ ordinaryWrongCompletionPrefix rate rewards C_star C_h n z :=
    ordinaryWrongCompletionPrefixObserved_iff rate rewards C_star C_h n z
  have hnext : ordinaryWrongCompletionPrefixObserved rate rewards C_star C_h (n + 1) z =
      true ↔ ordinaryWrongCompletionPrefix rate rewards C_star C_h (n + 1) z :=
    ordinaryWrongCompletionPrefixObserved_iff rate rewards C_star C_h (n + 1) z
  apply Bool.eq_iff_iff.mpr
  rw [hnext, hscan, Bool.or_eq_true, hprev, hdated]

theorem ordinaryWrongCompletionPrefix_observer_measurable
    (n : ℕ) :
    Measurable (ordinaryWrongCompletionPrefixObserved rate rewards C_star C_h n) := by
  have hbits : Measurable (fun z : SourceInput p => fun t : Fin p.T =>
      ordinaryWrongCompletionAtObserved rate rewards C_star C_h t z) := by
    apply measurable_pi_iff.mpr
    intro t
    exact ordinaryWrongCompletionAt_observed_measurable
      (rate := rate) (rewards := rewards) C_star C_h t
  have hscan : Measurable (fun f : Fin p.T → Bool =>
      decide (∃ t : Fin p.T, t.val < n ∧ f t = true)) := measurable_of_finite _
  have hprefix := hscan.comp hbits
  have hpoint (z : SourceInput p) :
      ordinaryWrongCompletionPrefixObserved rate rewards C_star C_h n z =
        decide (∃ t : Fin p.T, t.val < n ∧
          ordinaryWrongCompletionAtObserved rate rewards C_star C_h t z = true) := by
    classical
    unfold ordinaryWrongCompletionPrefixObserved
    apply Bool.decide_congr
    constructor
    · rintro ⟨t, ht, hbad⟩
      exact ⟨t, ht, (ordinaryWrongCompletionAt_observed_iff
        rate rewards C_star C_h t z).mp hbad⟩
    · rintro ⟨t, ht, hbit⟩
      exact ⟨t, ht, (ordinaryWrongCompletionAt_observed_iff
        rate rewards C_star C_h t z).mpr hbit⟩
  have heq : ordinaryWrongCompletionPrefixObserved rate rewards C_star C_h n =
      fun z => decide (∃ t : Fin p.T, t.val < n ∧
        ordinaryWrongCompletionAtObserved rate rewards C_star C_h t z = true) := by
    funext z
    exact hpoint z
  rw [heq]
  exact hprefix

theorem ordinaryWrongCompletionPrefix_measurableSet
    (n : ℕ) :
    MeasurableSet {z : SourceInput p |
      ordinaryWrongCompletionPrefix rate rewards C_star C_h n z} := by
  have hprefix := ordinaryWrongCompletionPrefix_observer_measurable
    (rate := rate) (rewards := rewards) C_star C_h n
  have heq : {z : SourceInput p |
      ordinaryWrongCompletionPrefix rate rewards C_star C_h n z} =
      (ordinaryWrongCompletionPrefixObserved rate rewards C_star C_h n) ⁻¹' {true} := by
    ext z
    exact (ordinaryWrongCompletionPrefixObserved_iff
      rate rewards C_star C_h n z).symm
  rw [heq]
  exact measurableSet_preimage hprefix (measurableSet_singleton true)

private theorem ordinaryPostlaunchWrongCompletionAtBool_eq_of_source_data
    (t : Fin p.T) (z z' : SourceInput p) (j : Fin (M p))
    (hids : z.1.1 = z'.1.1) (hprivate : z.2 = z'.2)
    (hJ : ActualInitializationPhysicalStep.selectedRowIndex p z = j)
    (hrow : z.1.2 j = z'.1.2 j) :
    ordinaryPostlaunchWrongCompletionAtBool rate rewards C_star C_h t z =
      ordinaryPostlaunchWrongCompletionAtBool rate rewards C_star C_h t z' := by
  obtain ⟨_, hboundary, _⟩ :=
    ReferenceCompletePhysicalHistory.generatedInput_and_launch_eq_of_source_data
      rate z z' rewards C_star C_h j hids hprivate hJ hrow
  have hstart : ReferenceCompletePhysicalHistory.physicalStart
      rate z rewards C_star C_h =
        ReferenceCompletePhysicalHistory.physicalStart rate z' rewards C_star C_h := by
    unfold ReferenceCompletePhysicalHistory.physicalStart
    rw [hboundary]
  have hcodes := ReferenceGeneratedCompleteCalendarObservation.completeSuffixCode_eq_of_source_data
    (rate := rate) rewards C_star C_h z z' j hids hprivate hJ hrow
  have hlook (k : ℕ) :
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k]?.map
          (ReferenceActiveHorizonMeasurability.roundRecordCode (p := p) (rate := rate)) =
        (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z' rewards C_star C_h)[k]?.map
          (ReferenceActiveHorizonMeasurability.roundRecordCode (p := p) (rate := rate)) := by
    calc
      _ = (ReferenceGeneratedCompleteCalendarObservation.completeSuffixCode
          (rate := rate) rewards C_star C_h z)[k]? := by
            simp [ReferenceGeneratedCompleteCalendarObservation.completeSuffixCode,
              List.getElem?_map]
      _ = (ReferenceGeneratedCompleteCalendarObservation.completeSuffixCode
          (rate := rate) rewards C_star C_h z')[k]? := congrArg (fun xs => xs[k]?) hcodes
      _ = _ := by
            simp [ReferenceGeneratedCompleteCalendarObservation.completeSuffixCode,
              List.getElem?_map]
  have hactual :
      (ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z).map
          (ReferenceActiveHorizonMeasurability.roundRecordCode (p := p) (rate := rate)) =
        (ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z').map
          (ReferenceActiveHorizonMeasurability.roundRecordCode (p := p) (rate := rate)) := by
    unfold ReferenceSourcePrefixHistoryFiltration.actualRecord
    rw [hstart]
    split_ifs with htime
    · exact hlook (t.val - ReferenceCompletePhysicalHistory.physicalStart
        rate z' rewards C_star C_h)
    · rfl
  unfold ordinaryPostlaunchWrongCompletionAtBool
  exact congrArg (fun code => code.elim false
    ReferenceSavedWrongUniqueMeasurability.savedWrongCode) hactual

private theorem ordinaryPrelaunchWrongCompletionAtBool_eq_of_source_data
    (t : Fin p.T) (z z' : SourceInput p) (j : Fin (M p))
    (hids : z.1.1 = z'.1.1) (hprivate : z.2 = z'.2)
    (hJ : ActualInitializationPhysicalStep.selectedRowIndex p z = j)
    (hrow : z.1.2 j = z'.1.2 j) :
    ordinaryPrelaunchWrongCompletionAtBool rate rewards C_star C_h t z =
      ordinaryPrelaunchWrongCompletionAtBool rate rewards C_star C_h t z' := by
  classical
  have hpre (i : Fin (p.m - 1)) :
      ReferencePrelaunchDownDecisionReadout.prelaunchDownFailureAt
          rate rewards C_star C_h z i t =
        ReferencePrelaunchDownDecisionReadout.prelaunchDownFailureAt
          rate rewards C_star C_h z' i t := by
    let e : ExtendedPrivateCoordinates p := z.2
    let scalar : ContinuousCategorical.Scalar :=
      (ReferenceInitializationIndexMixture.scalarAndResidual e).1
    let residual : ReferenceInitializationIndexMixture.PrivateResidual p :=
      (ReferenceInitializationIndexMixture.scalarAndResidual e).2
    have he : e = ReferenceInitializationIndexMixture.insertScalarResidual (scalar, residual) := by
      simp [e, scalar, residual, ReferenceInitializationIndexMixture.insert_scalarAndResidual]
    have hindex : PrivateSourceStreams.coordinatorIndex p scalar = j := by
      simpa [e, scalar, ReferenceInitializationIndexMixture.scalarAndResidual,
        ActualInitializationPhysicalStep.selectedRowIndex] using hJ
    have hsame : z' = ((z.1.1, z'.1.2), e) := by
      apply Prod.ext
      · apply Prod.ext
        · exact hids.symm
        · rfl
      · exact hprivate.symm
    rw [show z = ((z.1.1, z.1.2), e) by rfl, hsame, he]
    exact ReferencePrelaunchDecoderIndexLocality.prelaunchDownFailureAt_eq_of_selectedRow_and_J_cell
      p rate rewards C_star C_h z.1.1 z.1.2 z'.1.2 residual scalar scalar j
      hindex hindex hrow i t
  unfold ordinaryPrelaunchWrongCompletionAtBool
  have hiff :
      (∃ i, ReferencePrelaunchDownDecisionReadout.prelaunchDownFailureAt
        rate rewards C_star C_h z i t = true) ↔
      ∃ i, ReferencePrelaunchDownDecisionReadout.prelaunchDownFailureAt
        rate rewards C_star C_h z' i t = true := by
    apply exists_congr
    intro i
    rw [hpre i]
  exact Bool.decide_congr hiff

/-- Dated locality for public identifiers, every original private coordinate
and the selected complete row. The full saved code is compared despite unequal
raw records that may retain different nuisance rows. -/
theorem ordinaryWrongCompletionAt_eq_of_source_data
    (t : Fin p.T) (z z' : SourceInput p) (j : Fin (M p))
    (hids : z.1.1 = z'.1.1) (hprivate : z.2 = z'.2)
    (hJ : ActualInitializationPhysicalStep.selectedRowIndex p z = j)
    (hrow : z.1.2 j = z'.1.2 j) :
    ReferenceCompleteOrdinaryWrongCompletionCharacterization.ordinaryWrongCompletionAt
        rate rewards C_star C_h t z ↔
      ReferenceCompleteOrdinaryWrongCompletionCharacterization.ordinaryWrongCompletionAt
        rate rewards C_star C_h t z' := by
  have hpre := ordinaryPrelaunchWrongCompletionAtBool_eq_of_source_data
    (rate := rate) (rewards := rewards) C_star C_h t z z' j hids hprivate hJ hrow
  have hpost := ordinaryPostlaunchWrongCompletionAtBool_eq_of_source_data
    (rate := rate) (rewards := rewards) C_star C_h t z z' j hids hprivate hJ hrow
  have hobs : ordinaryWrongCompletionAtObserved rate rewards C_star C_h t z =
      ordinaryWrongCompletionAtObserved rate rewards C_star C_h t z' := by
    simp [ordinaryWrongCompletionAtObserved, hpre, hpost]
  rw [ordinaryWrongCompletionAt_observed_iff rate rewards C_star C_h t z,
    ordinaryWrongCompletionAt_observed_iff rate rewards C_star C_h t z']
  rw [hobs]

/-- The finite prefix event is unchanged under the same literal source-data
comparison. -/
theorem ordinaryWrongCompletionPrefix_iff_of_source_data
    (n : ℕ) (z z' : SourceInput p) (j : Fin (M p))
    (hids : z.1.1 = z'.1.1) (hprivate : z.2 = z'.2)
    (hJ : ActualInitializationPhysicalStep.selectedRowIndex p z = j)
    (hrow : z.1.2 j = z'.1.2 j) :
    ordinaryWrongCompletionPrefix rate rewards C_star C_h n z ↔
      ordinaryWrongCompletionPrefix rate rewards C_star C_h n z' := by
  constructor
  · rintro ⟨t, ht, hbad⟩
    exact ⟨t, ht, (ordinaryWrongCompletionAt_eq_of_source_data
      (rate := rate) (rewards := rewards) C_star C_h t z z' j hids hprivate hJ hrow).mp hbad⟩
  · rintro ⟨t, ht, hbad⟩
    exact ⟨t, ht, (ordinaryWrongCompletionAt_eq_of_source_data
      (rate := rate) (rewards := rewards) C_star C_h t z z' j hids hprivate hJ hrow).mpr hbad⟩

/-- A selected-row replacement gives identical dated and finite-prefix
observations whenever both original coordinator indices select `j`. -/
theorem selectedRow_update_observation
    (ids : IDArray p) (rows otherRows : CompleteRows p)
    (j : Fin (M p)) (rho : CompleteRow p)
    (e : ExtendedPrivateCoordinates p)
    (hJ : PrivateSourceStreams.coordinatorIndex p e.1.2 = j)
    (t : Fin p.T) (n : ℕ) :
    (ReferenceCompleteOrdinaryWrongCompletionCharacterization.ordinaryWrongCompletionAt
        rate rewards C_star C_h t ((ids, Function.update rows j rho), e) ↔
      ReferenceCompleteOrdinaryWrongCompletionCharacterization.ordinaryWrongCompletionAt
        rate rewards C_star C_h t ((ids, Function.update otherRows j rho), e)) ∧
    (ordinaryWrongCompletionPrefix rate rewards C_star C_h n
        ((ids, Function.update rows j rho), e) ↔
      ordinaryWrongCompletionPrefix rate rewards C_star C_h n
        ((ids, Function.update otherRows j rho), e)) := by
  have hselected : ActualInitializationPhysicalStep.selectedRowIndex p
      ((ids, Function.update rows j rho), e) = j := by
    simpa [ActualInitializationPhysicalStep.selectedRowIndex] using hJ
  have hrow : Function.update rows j rho j = Function.update otherRows j rho j := by
    simp
  refine ⟨?_, ?_⟩
  · exact ordinaryWrongCompletionAt_eq_of_source_data
      (rate := rate) (rewards := rewards) C_star C_h t
      ((ids, Function.update rows j rho), e)
      ((ids, Function.update otherRows j rho), e) j rfl rfl hselected hrow
  · exact ordinaryWrongCompletionPrefix_iff_of_source_data
      (rate := rate) (rewards := rewards) C_star C_h n
      ((ids, Function.update rows j rho), e)
      ((ids, Function.update otherRows j rho), e) j rfl rfl hselected hrow

/-- Measurability of the observer on a fixed public identifier/table section
as the full original private coordinates vary. -/
theorem fixedPublic_dated_observer_measurable
    (ids : IDArray p) (rows : CompleteRows p) (t : Fin p.T) :
    Measurable (fun e : ExtendedPrivateCoordinates p =>
      ordinaryWrongCompletionAtObserved rate rewards C_star C_h t ((ids, rows), e)) := by
  have hsource : Measurable (fun e : ExtendedPrivateCoordinates p => ((ids, rows), e)) :=
    measurable_const.prodMk measurable_id
  exact (ordinaryWrongCompletionAt_observed_measurable
    (rate := rate) (rewards := rewards) C_star C_h t).comp hsource

/-- Measurability of the finite-prefix observer on the same fixed-public
private-coordinate section. -/
theorem fixedPublic_prefix_observer_measurable
    (ids : IDArray p) (rows : CompleteRows p) (n : ℕ) :
    Measurable (fun e : ExtendedPrivateCoordinates p =>
      ordinaryWrongCompletionPrefixObserved rate rewards C_star C_h n ((ids, rows), e)) := by
  have hsource : Measurable (fun e : ExtendedPrivateCoordinates p => ((ids, rows), e)) :=
    measurable_const.prodMk measurable_id
  exact (ordinaryWrongCompletionPrefix_observer_measurable
    (rate := rate) (rewards := rewards) C_star C_h n).comp hsource

/-- The date-wise observer remains measurable as a complete row is replaced
at a fixed coordinate of the original product table. -/
theorem updatedRow_dated_observer_measurable
    (ids : IDArray p) (rows : CompleteRows p) (j : Fin (M p))
    (e : ExtendedPrivateCoordinates p) (t : Fin p.T) :
    Measurable (fun rho : CompleteRow p =>
      ordinaryWrongCompletionAtObserved rate rewards C_star C_h t
        ((ids, Function.update rows j rho), e)) := by
  have hrows : Measurable (fun rho : CompleteRow p => Function.update rows j rho) :=
    measurable_update rows
  have hpublic : Measurable (fun rho : CompleteRow p =>
      (ids, Function.update rows j rho)) := measurable_const.prodMk hrows
  have hsource : Measurable (fun rho : CompleteRow p =>
      ((ids, Function.update rows j rho), e)) := hpublic.prodMk measurable_const
  exact (ordinaryWrongCompletionAt_observed_measurable
    (rate := rate) (rewards := rewards) C_star C_h t).comp hsource

/-- The finite-prefix observer remains measurable on the corresponding
updated complete-row section. -/
theorem updatedRow_prefix_observer_measurable
    (ids : IDArray p) (rows : CompleteRows p) (j : Fin (M p))
    (e : ExtendedPrivateCoordinates p) (n : ℕ) :
    Measurable (fun rho : CompleteRow p =>
      ordinaryWrongCompletionPrefixObserved rate rewards C_star C_h n
        ((ids, Function.update rows j rho), e)) := by
  have hrows : Measurable (fun rho : CompleteRow p => Function.update rows j rho) :=
    measurable_update rows
  have hpublic : Measurable (fun rho : CompleteRow p =>
      (ids, Function.update rows j rho)) := measurable_const.prodMk hrows
  have hsource : Measurable (fun rho : CompleteRow p =>
      ((ids, Function.update rows j rho), e)) := hpublic.prodMk measurable_const
  exact (ordinaryWrongCompletionPrefix_observer_measurable
    (rate := rate) (rewards := rewards) C_star C_h n).comp hsource

end Bandits.Support.ReferenceCompleteOrdinaryFalseEventObservableLocality

end
