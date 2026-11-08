/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.InitializationFailureProvenance
public import Bandits.Support.InitializationRowObservables

/-!
# Operational witnesses for initialization row events

The fixed-row initialization-failure event and its selected-row counterpart
are exactly the union of the existing operational correction and suppressed
ordinary-DOWN witnesses. The selected-row event uses the same private point
and selects its row by the original coordinator index and complete row family.

`actualInitializationFailureEvent` names the selected-row **reference** flag:
it is still formed from `fixedRowInput` and the selected complete row, not from
the actual all-candidate protocol.

These interfaces expose event identity and transport its existing real mass
and indicator integrals. They do not identify the event with manuscript
`E_init` or establish a launch bound, coupling, postlaunch-policy result,
whole-reference cost, or the main regret theorem.

Sources: `sources/zip4/manuscript/07_public_setup.tex:129-140`,
`sources/zip4/manuscript/08_main_theorem.tex:29-42`, and
`sources/zip4/manuscript/appendix_b_communication.tex:724-744`.
-/

public section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.CompletePublicTable
open Bandits.Support.InitializationRowObservables

namespace Bandits.Support.InitializationRowEventProvenance

/-- Fixed-row event membership is the accepted terminal reference flag and,
through the accepted provenance theorem, the existing operational witness. -/
theorem initializationFailureEvent_iff_operationalInitializationFailure
    (p : ConstructorDimensions.Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (row : CompleteRow p)
    (e : PrivateCoordinates p) :
    e ∈ InitializationRowObservables.initializationFailureEvent
        p ids rewards C_star C_h eta row ↔
      InitializationFailureProvenance.operationalInitializationFailure
        (ReferenceInitializationIndexMixture.fixedRowInput
          p ids rewards C_star C_h eta row e) := by
  exact (InitializationRowObservables.initializationFailureEvent_iff_terminalFlag
    p ids rewards C_star C_h eta row e).trans
      (InitializationFailureProvenance.initializationFailure_iff_operational
        (ReferenceInitializationIndexMixture.fixedRowInput
          p ids rewards C_star C_h eta row e))

/-- The selected-row event is the same operational reference flag on the same
private point, using the original coordinator scalar and complete row family. -/
theorem actualInitializationFailureEvent_iff_operationalInitializationFailure
    (p : ConstructorDimensions.Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (rows : CompleteRows p)
    (e : PrivateCoordinates p) :
    e ∈ InitializationRowObservables.actualInitializationFailureEvent
        p ids rewards C_star C_h eta rows ↔
      InitializationFailureProvenance.operationalInitializationFailure
        (ReferenceInitializationIndexMixture.fixedRowInput p ids rewards C_star C_h eta
          (rows (PrivateSourceStreams.coordinatorIndex p e.1.2)) e) := by
  exact (InitializationRowObservables.actualInitializationFailureEvent_iff_terminalFlag
    p ids rewards C_star C_h eta rows e).trans
      (InitializationFailureProvenance.initializationFailure_iff_operational
        (ReferenceInitializationIndexMixture.fixedRowInput p ids rewards C_star C_h eta
          (rows (PrivateSourceStreams.coordinatorIndex p e.1.2)) e))

/-- Exact fixed-row set equality with the existing correction-or-suppressed-
DOWN witness union, at the literal accepted `fixedRowInput`. -/
theorem initializationFailureEvent_eq_operationalWitnessedUnion
    (p : ConstructorDimensions.Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (row : CompleteRow p) :
    InitializationRowObservables.initializationFailureEvent
        p ids rewards C_star C_h eta row =
      {e : PrivateCoordinates p |
        (∃ i : ActiveRoundActions.Follower p.m,
          ∃ s : Fin (BootstrapDimensions.n_boot p),
            InitializationFailureProvenance.forcedCorrectionAt
              (ReferenceInitializationIndexMixture.fixedRowInput
                p ids rewards C_star C_h eta row e) s i) ∨
        (∃ i : ActiveRoundActions.Follower p.m,
          ∃ s : Fin (BootstrapDimensions.n_boot p),
            InitializationFailureProvenance.suppressedDownAt
              (ReferenceInitializationIndexMixture.fixedRowInput
                p ids rewards C_star C_h eta row e) s i)} := by
  ext e
  exact initializationFailureEvent_iff_operationalInitializationFailure
    p ids rewards C_star C_h eta row e

/-- Exact selected-row set equality with the existing correction-or-suppressed-
DOWN witness union, preserving the whole family, scalar, and original private
point used to select the row. -/
theorem actualInitializationFailureEvent_eq_operationalWitnessedUnion
    (p : ConstructorDimensions.Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (rows : CompleteRows p) :
    InitializationRowObservables.actualInitializationFailureEvent
        p ids rewards C_star C_h eta rows =
      {e : PrivateCoordinates p |
        (∃ i : ActiveRoundActions.Follower p.m,
          ∃ s : Fin (BootstrapDimensions.n_boot p),
            InitializationFailureProvenance.forcedCorrectionAt
              (ReferenceInitializationIndexMixture.fixedRowInput p ids rewards C_star C_h eta
                (rows (PrivateSourceStreams.coordinatorIndex p e.1.2)) e) s i) ∨
        (∃ i : ActiveRoundActions.Follower p.m,
          ∃ s : Fin (BootstrapDimensions.n_boot p),
            InitializationFailureProvenance.suppressedDownAt
              (ReferenceInitializationIndexMixture.fixedRowInput p ids rewards C_star C_h eta
                (rows (PrivateSourceStreams.coordinatorIndex p e.1.2)) e) s i)} := by
  ext e
  exact actualInitializationFailureEvent_iff_operationalInitializationFailure
    p ids rewards C_star C_h eta rows e

/-- The real mass of the fixed-row operational witness event is the accepted
per-row failure indicator integral. -/
theorem operationalFixedRowFailure_mass_eq_e_initFlag
    (p : ConstructorDimensions.Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (row : CompleteRow p) :
    (BootstrapPrivateRoundStreams.extendedPrivateLaw p
      {e : PrivateCoordinates p |
        (∃ i : ActiveRoundActions.Follower p.m,
          ∃ s : Fin (BootstrapDimensions.n_boot p),
            InitializationFailureProvenance.forcedCorrectionAt
              (ReferenceInitializationIndexMixture.fixedRowInput
                p ids rewards C_star C_h eta row e) s i) ∨
        (∃ i : ActiveRoundActions.Follower p.m,
          ∃ s : Fin (BootstrapDimensions.n_boot p),
            InitializationFailureProvenance.suppressedDownAt
              (ReferenceInitializationIndexMixture.fixedRowInput
                p ids rewards C_star C_h eta row e) s i)}).toReal =
      InitializationRowObservables.e_initFlag p ids rewards C_star C_h eta row := by
  rw [← initializationFailureEvent_eq_operationalWitnessedUnion
    p ids rewards C_star C_h eta row]
  exact InitializationRowObservables.e_initFlag_eq_real_event_mass
    p ids rewards C_star C_h eta row

/-- The real mass of the selected-row operational witness event is the
accepted integral of the selected-row named-event indicator. -/
theorem operationalSelectedRowFailure_mass_eq_indicator_integral
    (p : ConstructorDimensions.Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (rows : CompleteRows p) :
    (BootstrapPrivateRoundStreams.extendedPrivateLaw p
      {e : PrivateCoordinates p |
        (∃ i : ActiveRoundActions.Follower p.m,
          ∃ s : Fin (BootstrapDimensions.n_boot p),
            InitializationFailureProvenance.forcedCorrectionAt
              (ReferenceInitializationIndexMixture.fixedRowInput p ids rewards C_star C_h eta
                (rows (PrivateSourceStreams.coordinatorIndex p e.1.2)) e) s i) ∨
        (∃ i : ActiveRoundActions.Follower p.m,
          ∃ s : Fin (BootstrapDimensions.n_boot p),
            InitializationFailureProvenance.suppressedDownAt
              (ReferenceInitializationIndexMixture.fixedRowInput p ids rewards C_star C_h eta
                (rows (PrivateSourceStreams.coordinatorIndex p e.1.2)) e) s i)}).toReal =
      ∫ e, InitializationRowObservables.actualInitializationFailureIndicator
        p ids rewards C_star C_h eta rows e
          ∂BootstrapPrivateRoundStreams.extendedPrivateLaw p := by
  rw [← actualInitializationFailureEvent_eq_operationalWitnessedUnion
    p ids rewards C_star C_h eta rows]
  exact InitializationRowObservables.actual_failure_indicator_eq_real_event_mass
    p ids rewards C_star C_h eta rows

/-- The indicator integral of the fixed-row operational witness union is the
accepted per-row failure integral. Measurability is supplied by the existing
operational-event API. -/
theorem operationalFixedRowFailure_indicator_integral_eq_e_initFlag
    (p : ConstructorDimensions.Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (row : CompleteRow p) :
    ∫ e, ({e : PrivateCoordinates p |
        (∃ i : ActiveRoundActions.Follower p.m,
          ∃ s : Fin (BootstrapDimensions.n_boot p),
            InitializationFailureProvenance.forcedCorrectionAt
              (ReferenceInitializationIndexMixture.fixedRowInput
                p ids rewards C_star C_h eta row e) s i) ∨
        (∃ i : ActiveRoundActions.Follower p.m,
          ∃ s : Fin (BootstrapDimensions.n_boot p),
            InitializationFailureProvenance.suppressedDownAt
              (ReferenceInitializationIndexMixture.fixedRowInput
                p ids rewards C_star C_h eta row e) s i)} : Set (PrivateCoordinates p)).indicator
          (fun _ => (1 : ℝ)) e
        ∂BootstrapPrivateRoundStreams.extendedPrivateLaw p =
      InitializationRowObservables.e_initFlag p ids rewards C_star C_h eta row := by
  calc
    _ = (BootstrapPrivateRoundStreams.extendedPrivateLaw p
        {e : PrivateCoordinates p |
          (∃ i : ActiveRoundActions.Follower p.m,
            ∃ s : Fin (BootstrapDimensions.n_boot p),
              InitializationFailureProvenance.forcedCorrectionAt
                (ReferenceInitializationIndexMixture.fixedRowInput
                  p ids rewards C_star C_h eta row e) s i) ∨
          (∃ i : ActiveRoundActions.Follower p.m,
            ∃ s : Fin (BootstrapDimensions.n_boot p),
              InitializationFailureProvenance.suppressedDownAt
                (ReferenceInitializationIndexMixture.fixedRowInput
                  p ids rewards C_star C_h eta row e) s i)}).toReal :=
      integral_indicator_one
        (InitializationFailureProvenance.measurable_fixedRowOperationalInitializationFailure
          p ids rewards C_star C_h eta row)
    _ = InitializationRowObservables.e_initFlag p ids rewards C_star C_h eta row :=
      operationalFixedRowFailure_mass_eq_e_initFlag p ids rewards C_star C_h eta row

/-- The indicator integral of the selected-row operational witness union is
the accepted selected-row named-event indicator integral. Measurability is
supplied by the existing operational-event API. -/
theorem operationalSelectedRowFailure_indicator_integral_eq_namedEvent
    (p : ConstructorDimensions.Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (rows : CompleteRows p) :
    ∫ e, ({e : PrivateCoordinates p |
        (∃ i : ActiveRoundActions.Follower p.m,
          ∃ s : Fin (BootstrapDimensions.n_boot p),
            InitializationFailureProvenance.forcedCorrectionAt
              (ReferenceInitializationIndexMixture.fixedRowInput p ids rewards C_star C_h eta
                (rows (PrivateSourceStreams.coordinatorIndex p e.1.2)) e) s i) ∨
        (∃ i : ActiveRoundActions.Follower p.m,
          ∃ s : Fin (BootstrapDimensions.n_boot p),
            InitializationFailureProvenance.suppressedDownAt
              (ReferenceInitializationIndexMixture.fixedRowInput p ids rewards C_star C_h eta
                (rows (PrivateSourceStreams.coordinatorIndex p e.1.2)) e) s i)} :
          Set (PrivateCoordinates p)).indicator (fun _ => (1 : ℝ)) e
        ∂BootstrapPrivateRoundStreams.extendedPrivateLaw p =
      ∫ e, InitializationRowObservables.actualInitializationFailureIndicator
        p ids rewards C_star C_h eta rows e
          ∂BootstrapPrivateRoundStreams.extendedPrivateLaw p := by
  calc
    _ = (BootstrapPrivateRoundStreams.extendedPrivateLaw p
        {e : PrivateCoordinates p |
          (∃ i : ActiveRoundActions.Follower p.m,
            ∃ s : Fin (BootstrapDimensions.n_boot p),
              InitializationFailureProvenance.forcedCorrectionAt
                (ReferenceInitializationIndexMixture.fixedRowInput p ids rewards C_star C_h eta
                  (rows (PrivateSourceStreams.coordinatorIndex p e.1.2)) e) s i) ∨
          (∃ i : ActiveRoundActions.Follower p.m,
            ∃ s : Fin (BootstrapDimensions.n_boot p),
              InitializationFailureProvenance.suppressedDownAt
                (ReferenceInitializationIndexMixture.fixedRowInput p ids rewards C_star C_h eta
                  (rows (PrivateSourceStreams.coordinatorIndex p e.1.2)) e) s i)}).toReal :=
      integral_indicator_one
        (InitializationFailureProvenance.measurable_actualSelectedRowOperationalInitializationFailure
          p ids rewards C_star C_h eta rows)
    _ = ∫ e, InitializationRowObservables.actualInitializationFailureIndicator
          p ids rewards C_star C_h eta rows e
            ∂BootstrapPrivateRoundStreams.extendedPrivateLaw p :=
      operationalSelectedRowFailure_mass_eq_indicator_integral
        p ids rewards C_star C_h eta rows

end Bandits.Support.InitializationRowEventProvenance

end
