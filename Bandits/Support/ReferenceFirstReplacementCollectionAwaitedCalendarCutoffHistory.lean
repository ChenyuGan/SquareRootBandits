/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstReplacementCollectionAwaitedCalendarWaitingCost
public import Bandits.Support.ReferenceFirstReplacementCollectionAwaitedCutoffHistory

/-!
# New awaited-calendar waiting bounds at the actual replacement issued cutoff

The NEW support is localized to the same actual birth and cutoff used by the
existing issued-command history. Its analytical phase start is later than or
equal to that history, including empty-support and failed-command paths.
The SAME new waiting charge is then bounded at the earlier stopped field under
the original source-input law. Neither stopping time is redefined or identified
with the other; the source-prefix fields are analysis fields, not physical
Gminus/Gplus. This internal result does not cover the whole stopped transfer.

Sources: ZIP4 `06_interruptions.tex:9-14,37-70,246-296,431-437,459-487` and
`appendix_a_local_protocol.tex:28-85`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support ConstructorDimensions BootstrapPrivateRoundStreams
open ReferenceSourcePrefixHistoryFiltration PhaseStartConditionalWaiting
open scoped Classical

namespace Bandits.Support.ReferenceFirstReplacementCollectionAwaitedCalendarCutoffHistory

variable {p : ConstructorDimensions.Parameters}

/-- Nonempty NEW support produces the successful local branch at the SAME
actual replacement cutoff; no containment in the old support is used. -/
theorem S_repl_le_of_Pnew_nonempty
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (n : ℕ)
    (hP : (ReferenceFirstReplacementCollectionAwaitedTaskSupport.Pnew rate rewards C_star C_h control0 n z).Nonempty) :
    ReferenceFirstReplacementCollectionAwaitedCutoffHistory.S_repl rate rewards C_star C_h z ≤ n + 1 := by
  have hloc := ReferenceFirstReplacementCollectionAwaitedTaskSupport.complete_first_replacement_awaited_pending_localization
    rate rewards C_star C_h control0 z n hP
  have hissued := ReferenceFirstReplacementCollectionAwaitedCutoffHistory.replacement_issued_at_same_cut
    rate rewards C_star C_h control0 z
  dsimp only at hloc hissued
  split at hloc
  · exact hloc.elim
  · split at hloc
    · split at hloc
      · exact hloc.elim
      · split at hloc
        · obtain ⟨a, ha, _, _⟩ := hloc
          simp_all only
          have hcutIssued := hissued.2.2
          have hle := ReferenceFirstReplacementCollectionAwaitedCutoffHistory.replacementIssuedAt_implies_S_repl_le
            rate rewards C_star C_h z _ hcutIssued
          omega
        all_goals exact hloc.elim
    all_goals exact hloc.elim

/-- The actual first issued cutoff precedes the EXACT new supported start.
Empty support uses only the horizon bound, retaining failed issued commands. -/
theorem S_repl_le_new_sigma
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (z : BootstrapPrivateRoundStreams.SourceInput p) :
    ReferenceFirstReplacementCollectionAwaitedCutoffHistory.S_repl rate rewards C_star C_h z ≤
      ReferenceFirstReplacementCollectionAwaitedCalendarPhaseSupport.sigma rate rewards C_star C_h control0 z := by
  unfold ReferenceFirstReplacementCollectionAwaitedCalendarPhaseSupport.sigma
  split
  · rename_i hne
    have hm := Finset.min'_mem _ hne
    have hsupport := (ReferenceFirstReplacementCollectionAwaitedCalendarPhaseSupport.mem_supportIndices_iff
      rate rewards C_star C_h control0 z _).1 hm
    exact S_repl_le_of_Pnew_nonempty rate rewards C_star C_h control0 z _ hsupport.2
  · exact (ReferenceFirstReplacementCollectionAwaitedCutoffHistory.S_repl_bounds rate rewards C_star C_h z).2

/-- Literally the stopped field of the NEW supported phase start. -/
@[instance_reducible] def GammaNew
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p) :
    MeasurableSpace (BootstrapPrivateRoundStreams.SourceInput p) :=
  PhaseStartConditionalWaiting.phaseStartSigmaAlgebra
    (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0)
    (ReferenceFirstReplacementCollectionAwaitedCalendarPhaseSupport.sigma rate rewards C_star C_h control0)
    (ReferenceFirstReplacementCollectionAwaitedCalendarPhaseSupport.sigma_is_pre_round_stopping_time
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
      (control0 := control0))

/-- Full literal characterization of the new stopped-field abbreviation. -/
theorem GammaNew_eq_phaseStartSigmaAlgebra
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p) :
    GammaNew rate rewards C_star C_h control0 =
      PhaseStartConditionalWaiting.phaseStartSigmaAlgebra
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0)
        (ReferenceFirstReplacementCollectionAwaitedCalendarPhaseSupport.sigma rate rewards C_star C_h control0)
        (ReferenceFirstReplacementCollectionAwaitedCalendarPhaseSupport.sigma_is_pre_round_stopping_time
          (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
          (control0 := control0)) := rfl

/-- Stopping-space monotonicity for the actual issued history and NEW start. -/
theorem GammaS_repl_le_GammaNew
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p) :
    ReferenceFirstReplacementCollectionAwaitedCutoffHistory.GammaS_repl rate rewards C_star C_h control0 ≤
      GammaNew rate rewards C_star C_h control0 := by
  unfold ReferenceFirstReplacementCollectionAwaitedCutoffHistory.GammaS_repl GammaNew PhaseStartConditionalWaiting.phaseStartSigmaAlgebra
  apply MeasureTheory.IsStoppingTime.measurableSpace_mono
  intro z
  change (ReferenceFirstReplacementCollectionAwaitedCutoffHistory.S_repl rate rewards C_star C_h z : WithTop ℕ) ≤
    (ReferenceFirstReplacementCollectionAwaitedCalendarPhaseSupport.sigma rate rewards C_star C_h control0 z : WithTop ℕ)
  exact WithTop.coe_le_coe.mpr (S_repl_le_new_sigma rate rewards C_star C_h control0 z)

/-- The exact new stopped field lies in the original ambient source space. -/
theorem GammaNew_le_ambient
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p) :
    GammaNew rate rewards C_star C_h control0 ≤
      inferInstanceAs (MeasurableSpace (BootstrapPrivateRoundStreams.SourceInput p)) := by
  exact PhaseStartConditionalWaiting.phaseStartSigmaAlgebra_le _ _ _

/-- The original-law downward tower for the SAME NEW waiting charge. -/
theorem W_downward_tower
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p) :
    (BootstrapPrivateRoundStreams.sourceInputLaw p)[
      (BootstrapPrivateRoundStreams.sourceInputLaw p)[
        ReferenceFirstReplacementCollectionAwaitedCalendarWaitingCost.W rate rewards C_star C_h control0 | GammaNew rate rewards C_star C_h control0] |
        ReferenceFirstReplacementCollectionAwaitedCutoffHistory.GammaS_repl rate rewards C_star C_h control0] =ᵐ[
          BootstrapPrivateRoundStreams.sourceInputLaw p]
      (BootstrapPrivateRoundStreams.sourceInputLaw p)[
        ReferenceFirstReplacementCollectionAwaitedCalendarWaitingCost.W rate rewards C_star C_h control0 |
          ReferenceFirstReplacementCollectionAwaitedCutoffHistory.GammaS_repl rate rewards C_star C_h control0] := by
  exact MeasureTheory.condExp_condExp_of_le
    (GammaS_repl_le_GammaNew rate rewards C_star C_h control0)
    (GammaNew_le_ambient rate rewards C_star C_h control0)

/-- Every event in the existing issued-cutoff history localizes the SAME NEW
waiting bound, with unnormalized original-law mass, including mass zero. -/
theorem W_cutoff_setIntegral_bound
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (B : Set (BootstrapPrivateRoundStreams.SourceInput p))
    (hB : MeasurableSet[ReferenceFirstReplacementCollectionAwaitedCutoffHistory.GammaS_repl rate rewards C_star C_h control0] B) :
    (∫ z in B, ReferenceFirstReplacementCollectionAwaitedCalendarWaitingCost.W rate rewards C_star C_h control0 z
      ∂BootstrapPrivateRoundStreams.sourceInputLaw p) ≤
      ReferenceFirstCollectionAwaitedWaitingCost.Bcol (p := p) *
        (BootstrapPrivateRoundStreams.sourceInputLaw p).real B := by
  exact ReferenceFirstReplacementCollectionAwaitedCalendarWaitingCost.W_setIntegral_bound rate rewards C_star C_h control0 B
    (GammaS_repl_le_GammaNew rate rewards C_star C_h control0 B hB)

/-- The SAME NEW charge is bounded at the actual issued cutoff under the
original source law, using its proved integrability and event-localized bound. -/
theorem W_cutoff_condExp_bound
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p) :
    (BootstrapPrivateRoundStreams.sourceInputLaw p)[
      ReferenceFirstReplacementCollectionAwaitedCalendarWaitingCost.W rate rewards C_star C_h control0 |
        ReferenceFirstReplacementCollectionAwaitedCutoffHistory.GammaS_repl rate rewards C_star C_h control0] ≤ᵐ[
          BootstrapPrivateRoundStreams.sourceInputLaw p]
      fun _ => ReferenceFirstCollectionAwaitedWaitingCost.Bcol (p := p) := by
  apply (PhaseStartConditionalWaiting.setIntegral_iff_condExp_le
    (BootstrapPrivateRoundStreams.sourceInputLaw p)
    (ReferenceFirstReplacementCollectionAwaitedCutoffHistory.GammaS_repl rate rewards C_star C_h control0)
    ((GammaS_repl_le_GammaNew rate rewards C_star C_h control0).trans
      (GammaNew_le_ambient rate rewards C_star C_h control0))
    (ReferenceFirstReplacementCollectionAwaitedCalendarWaitingCost.W rate rewards C_star C_h control0)
    (ReferenceFirstCollectionAwaitedWaitingCost.Bcol (p := p))
    (ReferenceFirstReplacementCollectionAwaitedCalendarWaitingCost.W_integrable rate rewards C_star C_h control0)).1
  exact W_cutoff_setIntegral_bound rate rewards C_star C_h control0

end Bandits.Support.ReferenceFirstReplacementCollectionAwaitedCalendarCutoffHistory

end
