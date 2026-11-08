/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.GeneratedForcedCorrectionTail
public import Bandits.Support.ReferenceSuppressedDownCoverage
public import Bandits.Support.ReferenceSuppressedDownMeasurability
public import Bandits.Support.InitializationRowObservables

import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Combined initialization-failure probability on the original product law

The literal operational failure event is the union of a forced correction at
the strict first monitor crossing and a suppressed accepted ordinary DOWN
decision. Its ambient probability is bounded on the same complete-row and
extended-private product law. The accepted row-observable theorem then turns
this whole-product mass into the actual complete-row integral of `e_initFlag`.

Sources: `sources/zip4/manuscript/07_public_setup.tex:129-164`,
`sources/zip4/manuscript/appendix_b_communication.tex:737-798`, and
`sources/zip4/manuscript/08_main_theorem.tex:29-42`.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace Bandits.Support.GeneratedInitializationFailureTail

abbrev Parameters := ConstructorDimensions.Parameters
abbrev Coordinates (p : Parameters) := GeneratedBootstrapRoundLaw.Coordinates p

variable (p : Parameters)
variable (ids : CompletePublicTable.IDArray p)
variable (rewards : Fin p.T → Fin p.K → Fin (ConstructorDimensions.D p + 1))
variable (C_star C_h : ℝ)
variable (eta : ReferencePrelaunchFollower.LearningRate)

/-- The literal union of operational forced-correction and suppressed-DOWN
causes on the original complete-row/private coordinate carrier. -/
def initializationFailureEvent : Set (Coordinates p) :=
  {e | InitializationFailureProvenance.operationalInitializationFailure
    (GeneratedBootstrapBlockFiltrationRepair.referenceInput
      p ids rewards C_star C_h eta e)}

/-- Reordering the operational witnesses gives exactly the two accepted
literal event components. -/
theorem initializationFailureEvent_eq_forcedCorrectionEvent_union_E_down :
    initializationFailureEvent p ids rewards C_star C_h eta =
      GeneratedForcedCorrectionTail.forcedCorrectionEvent
          p ids rewards C_star C_h eta ∪
        ReferenceSuppressedDownTail.E_down p ids rewards C_star C_h eta := by
  ext e
  change InitializationFailureProvenance.operationalInitializationFailure
      (GeneratedBootstrapBlockFiltrationRepair.referenceInput
        p ids rewards C_star C_h eta e) ↔
    e ∈ GeneratedForcedCorrectionTail.forcedCorrectionEvent
          p ids rewards C_star C_h eta ∪
        ReferenceSuppressedDownTail.E_down p ids rewards C_star C_h eta
  simp only [InitializationFailureProvenance.operationalInitializationFailure,
    Set.mem_union, GeneratedForcedCorrectionTail.forcedCorrectionEvent,
    ReferenceSuppressedDownTail.E_down, Set.mem_ofPred_eq]
  constructor
  · rintro (⟨i, s, hforce⟩ | ⟨i, s, hdown⟩)
    · exact Or.inl ⟨s, i, hforce⟩
    · exact Or.inr ⟨i, s, hdown⟩
  · rintro (⟨s, i, hforce⟩ | ⟨i, s, hdown⟩)
    · exact Or.inl ⟨i, s, hforce⟩
    · exact Or.inr ⟨i, s, hdown⟩

/-- The exact terminal-flag product event, with the adapter equality derived
from the two literal `inputOfCoordinates` applications in this proof. -/
theorem initializationFailureEvent_eq_terminalFlagProduct :
    initializationFailureEvent p ids rewards C_star C_h eta =
      {z : CompletePublicTable.CompleteRow p ×
          BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p |
        z.2 ∈ InitializationRowObservables.initializationFailureEvent
          p ids rewards C_star C_h eta z.1} := by
  ext z
  rcases z with ⟨row, e⟩
  change InitializationFailureProvenance.operationalInitializationFailure
      (GeneratedBootstrapBlockFiltrationRepair.referenceInput
        p ids rewards C_star C_h eta (row, e)) ↔
    e ∈ InitializationRowObservables.initializationFailureEvent
      p ids rewards C_star C_h eta row
  have hinput :
      GeneratedBootstrapBlockFiltrationRepair.referenceInput
          p ids rewards C_star C_h eta (row, e) =
        ReferenceInitializationIndexMixture.fixedRowInput
          p ids rewards C_star C_h eta row e := by
    change ReferenceInitializationMeasurability.inputOfCoordinates
        p C_star C_h eta rewards (ids, (row, e)) =
      ReferenceInitializationMeasurability.inputOfCoordinates
        p C_star C_h eta rewards (ids, (row, e))
    rfl
  rw [hinput,
    ← InitializationFailureProvenance.initializationFailure_iff_operational]
  exact (InitializationRowObservables.initializationFailureEvent_iff_terminalFlag
    p ids rewards C_star C_h eta row e).symm

/-- The exact combined event is ambient Borel measurable, without any
identification-good or scalar-regime hypothesis. -/
theorem measurableSet_initializationFailureEvent :
    MeasurableSet (initializationFailureEvent p ids rewards C_star C_h eta) := by
  rw [initializationFailureEvent_eq_forcedCorrectionEvent_union_E_down]
  exact (GeneratedForcedCorrectionTail.measurableSet_forcedCorrectionEvent
    p ids rewards C_star C_h eta).union
      (ReferenceSuppressedDownMeasurability.measurableSet_E_down
        p ids rewards C_star C_h eta)

/-- The two accepted tail bounds combine on the same original product law by
the ordinary union inequality. The first conjunct retains the exact sum of
the forced-correction and suppressed-DOWN estimates. -/
theorem initializationFailureEvent_real_probability_bounds
    (hgood : ids ∈ IdentificationGoodEvent.identificationGoodEvent p)
    (hC_h : (4096 : ℝ) ≤ C_h)
    (hCstar : (2 : ℝ) ^ 20 ≤ C_star) :
    (GeneratedBootstrapRoundLaw.originalLaw p).real
        (initializationFailureEvent p ids rewards C_star C_h eta) ≤
      1 / (ConstructorDimensions.N p : ℝ) ^ 2 +
        1 / (4 * (ConstructorDimensions.N p : ℝ) ^ 2) ∧
    (GeneratedBootstrapRoundLaw.originalLaw p).real
        (initializationFailureEvent p ids rewards C_star C_h eta) ≤
      5 / (4 * (ConstructorDimensions.N p : ℝ) ^ 2) ∧
    (GeneratedBootstrapRoundLaw.originalLaw p).real
        (initializationFailureEvent p ids rewards C_star C_h eta) ≤
      5 / (ConstructorDimensions.N p : ℝ) ^ 2 := by
  let μ := GeneratedBootstrapRoundLaw.originalLaw p
  have hforce :=
    (GeneratedForcedCorrectionTail.forcedCorrectionEvent_measure_le
      p ids rewards C_star C_h eta hgood hC_h hCstar).2.2
  have hdown :=
    ReferenceSuppressedDownCoverage.E_down_real_outer_probability_le_quarter
      p ids rewards C_star C_h eta
  have hsum :
      1 / (ConstructorDimensions.N p : ℝ) ^ 2 +
        1 / (4 * (ConstructorDimensions.N p : ℝ) ^ 2) =
      5 / (4 * (ConstructorDimensions.N p : ℝ) ^ 2) := by
    have hNpos : 0 < (ConstructorDimensions.N p : ℝ) :=
      Nat.cast_pos.mpr (ConstructorDimensions.N_pos p)
    have hdenpos : 0 < (ConstructorDimensions.N p : ℝ) ^ 2 := pow_pos hNpos 2
    field_simp [ne_of_gt hdenpos]; ring
  have hweak :
      5 / (4 * (ConstructorDimensions.N p : ℝ) ^ 2) ≤
        5 / (ConstructorDimensions.N p : ℝ) ^ 2 := by
    have hNpos : 0 < (ConstructorDimensions.N p : ℝ) :=
      Nat.cast_pos.mpr (ConstructorDimensions.N_pos p)
    have hdenpos : 0 < (ConstructorDimensions.N p : ℝ) ^ 2 := pow_pos hNpos 2
    rw [div_le_div_iff₀ (mul_pos (by norm_num) hdenpos) hdenpos]
    nlinarith
  have hcombined :
      μ.real (initializationFailureEvent p ids rewards C_star C_h eta) ≤
        1 / (ConstructorDimensions.N p : ℝ) ^ 2 +
          1 / (4 * (ConstructorDimensions.N p : ℝ) ^ 2) := by
    calc
      μ.real (initializationFailureEvent p ids rewards C_star C_h eta) =
          μ.real (GeneratedForcedCorrectionTail.forcedCorrectionEvent
            p ids rewards C_star C_h eta ∪
              ReferenceSuppressedDownTail.E_down p ids rewards C_star C_h eta) :=
        congrArg μ.real
          (initializationFailureEvent_eq_forcedCorrectionEvent_union_E_down
            p ids rewards C_star C_h eta)
      _ ≤ μ.real (GeneratedForcedCorrectionTail.forcedCorrectionEvent
            p ids rewards C_star C_h eta) +
          μ.real (ReferenceSuppressedDownTail.E_down p ids rewards C_star C_h eta) :=
        MeasureTheory.measureReal_union_le _ _
      _ ≤ 1 / (ConstructorDimensions.N p : ℝ) ^ 2 +
          1 / (4 * (ConstructorDimensions.N p : ℝ) ^ 2) := add_le_add hforce hdown
  exact ⟨hcombined, hcombined.trans_eq hsum,
    (hcombined.trans_eq hsum).trans hweak⟩

/-- Actual complete-row integral bound for the accepted `e_initFlag` observable.
It is obtained from the exact product-event equality and the accepted
unconditional row/private Fubini theorem. -/
theorem e_initFlag_integral_bounds
    (hgood : ids ∈ IdentificationGoodEvent.identificationGoodEvent p)
    (hC_h : (4096 : ℝ) ≤ C_h)
    (hCstar : (2 : ℝ) ^ 20 ≤ C_star) :
    (∫ row, InitializationRowObservables.e_initFlag
        p ids rewards C_star C_h eta row
        ∂CompletePublicTable.completeRowMeasure p) ≤
      5 / (4 * (ConstructorDimensions.N p : ℝ) ^ 2) ∧
    (∫ row, InitializationRowObservables.e_initFlag
        p ids rewards C_star C_h eta row
        ∂CompletePublicTable.completeRowMeasure p) ≤
      5 / (ConstructorDimensions.N p : ℝ) ^ 2 := by
  have hmass :
      (GeneratedBootstrapRoundLaw.originalLaw p).real
          (initializationFailureEvent p ids rewards C_star C_h eta) =
        ∫ row, InitializationRowObservables.e_initFlag
          p ids rewards C_star C_h eta row
          ∂CompletePublicTable.completeRowMeasure p := by
    calc
      _ = (GeneratedBootstrapRoundLaw.originalLaw p).real
          {z : CompletePublicTable.CompleteRow p ×
              BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p |
            z.2 ∈ InitializationRowObservables.initializationFailureEvent
              p ids rewards C_star C_h eta z.1} :=
        congrArg (GeneratedBootstrapRoundLaw.originalLaw p).real
          (initializationFailureEvent_eq_terminalFlagProduct
            p ids rewards C_star C_h eta)
      _ = ∫ row, InitializationRowObservables.e_initFlag
          p ids rewards C_star C_h eta row
          ∂CompletePublicTable.completeRowMeasure p :=
        InitializationRowObservables.generatedFailureEvent_real_mass
          p ids rewards C_star C_h eta
  have hprob := initializationFailureEvent_real_probability_bounds
    p ids rewards C_star C_h eta hgood hC_h hCstar
  constructor
  · rw [← hmass]
    exact hprob.2.1
  · rw [← hmass]
    exact hprob.2.2

end Bandits.Support.GeneratedInitializationFailureTail

end
