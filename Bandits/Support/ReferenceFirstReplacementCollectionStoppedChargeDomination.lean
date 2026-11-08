/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstReplacementCollectionInclusiveStoppedCharge
public import Bandits.Support.ReferenceFirstReplacementCollectionDecoderSafeWaitingCost

/-!
# Original-law bounds for the inclusive stopped first-replacement charge

The literal inclusive stopped charge is dominated by the decoder-safe charge
on the same original source input. Its original-law integrability and its
event-set and conditional bounds are transferred at the existing new phase
start and issued-cutoff analysis fields.

Sources: ZIP4 `06_interruptions.tex:355-437,459-487`,
`05_binary_transport.tex:354-431`, and `appendix_a_local_protocol.tex:14-64`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support ConstructorDimensions BootstrapPrivateRoundStreams
open scoped Classical

namespace Bandits.Support.ReferenceFirstReplacementCollectionStoppedChargeDomination

variable {p : ConstructorDimensions.Parameters}

/-- The exact inclusive first-replacement stopped charge is bounded by the
decoder-safe charge on the same original source input. -/
theorem Cstop_le_W
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (z : BootstrapPrivateRoundStreams.SourceInput p) :
    ReferenceFirstReplacementCollectionInclusiveStoppedCharge.Cstop
        rate rewards C_star C_h z ≤
      ReferenceFirstReplacementCollectionAwaitedCalendarWaitingCost.W
        rate rewards C_star C_h control0 z := by
  calc
    ReferenceFirstReplacementCollectionInclusiveStoppedCharge.Cstop
        rate rewards C_star C_h z ≤
        ReferenceFirstReplacementCollectionGlobalDecoderCharge.Cdec
          rate rewards C_star C_h z :=
      (ReferenceFirstReplacementCollectionInclusiveStoppedCharge.Cstop_bounds
        rate rewards C_star C_h z).2
    _ ≤ ReferenceFirstReplacementCollectionAwaitedCalendarWaitingCost.W
        rate rewards C_star C_h control0 z :=
      ReferenceFirstReplacementCollectionDecoderSafeWaitingCost.Cdec_le_W
        rate rewards C_star C_h control0 z

/-- Integrability of the literal inclusive stopped charge under the original
private-round source law. -/
theorem Cstop_integrable
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p) :
    Integrable
      (ReferenceFirstReplacementCollectionInclusiveStoppedCharge.Cstop
        rate rewards C_star C_h)
      (BootstrapPrivateRoundStreams.sourceInputLaw p) := by
  have hW := ReferenceFirstReplacementCollectionAwaitedCalendarWaitingCost.W_integrable
    rate rewards C_star C_h control0
  have hmeas := ReferenceFirstReplacementCollectionInclusiveStoppedCharge.Cstop_measurable
    rate rewards C_star C_h control0
  have hnonneg (z : BootstrapPrivateRoundStreams.SourceInput p) :=
    (ReferenceFirstReplacementCollectionInclusiveStoppedCharge.Cstop_bounds
      rate rewards C_star C_h z).1
  have hle (z : BootstrapPrivateRoundStreams.SourceInput p) :=
    Cstop_le_W rate rewards C_star C_h control0 z
  have hnorm : ∀ z : BootstrapPrivateRoundStreams.SourceInput p,
      ‖ReferenceFirstReplacementCollectionInclusiveStoppedCharge.Cstop
        rate rewards C_star C_h z‖ ≤
      ReferenceFirstReplacementCollectionAwaitedCalendarWaitingCost.W
        rate rewards C_star C_h control0 z := by
    intro z
    rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg z)]
    exact hle z
  exact hW.mono' hmeas.aestronglyMeasurable (ae_of_all _ hnorm)

/-- Every event in the exact new phase-start field has the unnormalized
original-law bound for the inclusive stopped charge. -/
theorem Cstop_phaseStart_setIntegral_bound
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (B : Set (BootstrapPrivateRoundStreams.SourceInput p))
    (hB : MeasurableSet[
      ReferenceFirstReplacementCollectionAwaitedCalendarCutoffHistory.GammaNew
        rate rewards C_star C_h control0] B) :
    (∫ z in B,
        ReferenceFirstReplacementCollectionInclusiveStoppedCharge.Cstop
          rate rewards C_star C_h z
      ∂BootstrapPrivateRoundStreams.sourceInputLaw p) ≤
      ReferenceFirstCollectionAwaitedWaitingCost.Bcol (p := p) *
        (BootstrapPrivateRoundStreams.sourceInputLaw p).real B := by
  have hle :
      ReferenceFirstReplacementCollectionInclusiveStoppedCharge.Cstop
        rate rewards C_star C_h ≤ᵐ[BootstrapPrivateRoundStreams.sourceInputLaw p]
      ReferenceFirstReplacementCollectionAwaitedCalendarWaitingCost.W
        rate rewards C_star C_h control0 :=
    ae_of_all _ (fun z => Cstop_le_W rate rewards C_star C_h control0 z)
  have hB' : MeasurableSet[
      PhaseStartConditionalWaiting.phaseStartSigmaAlgebra
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0)
        (ReferenceFirstReplacementCollectionAwaitedCalendarPhaseSupport.sigma
          (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
          (control0 := control0))
        (ReferenceFirstReplacementCollectionAwaitedCalendarPhaseSupport.sigma_is_pre_round_stopping_time
          (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
          (control0 := control0))] B := by
    simpa only [ReferenceFirstReplacementCollectionAwaitedCalendarCutoffHistory.GammaNew_eq_phaseStartSigmaAlgebra]
      using hB
  calc
    (∫ z in B,
        ReferenceFirstReplacementCollectionInclusiveStoppedCharge.Cstop
          rate rewards C_star C_h z
      ∂BootstrapPrivateRoundStreams.sourceInputLaw p) ≤
      ∫ z in B,
        ReferenceFirstReplacementCollectionAwaitedCalendarWaitingCost.W
          rate rewards C_star C_h control0 z
        ∂BootstrapPrivateRoundStreams.sourceInputLaw p :=
      setIntegral_mono_ae
        (Cstop_integrable rate rewards C_star C_h control0).integrableOn
        (ReferenceFirstReplacementCollectionAwaitedCalendarWaitingCost.W_integrable
          rate rewards C_star C_h control0).integrableOn hle
    _ ≤ ReferenceFirstCollectionAwaitedWaitingCost.Bcol (p := p) *
        (BootstrapPrivateRoundStreams.sourceInputLaw p).real B :=
      ReferenceFirstReplacementCollectionAwaitedCalendarWaitingCost.W_setIntegral_bound
        rate rewards C_star C_h control0 B hB'

/-- The conditional expectation of the inclusive stopped charge is bounded
by `Bcol` at the same exact new phase-start field. -/
theorem Cstop_phaseStart_condExp_bound
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p) :
    (BootstrapPrivateRoundStreams.sourceInputLaw p)[
      ReferenceFirstReplacementCollectionInclusiveStoppedCharge.Cstop
        rate rewards C_star C_h |
      ReferenceFirstReplacementCollectionAwaitedCalendarCutoffHistory.GammaNew
        rate rewards C_star C_h control0] ≤ᵐ[
          BootstrapPrivateRoundStreams.sourceInputLaw p]
      fun _ => ReferenceFirstCollectionAwaitedWaitingCost.Bcol (p := p) := by
  have hmono := MeasureTheory.condExp_mono
    (m := ReferenceFirstReplacementCollectionAwaitedCalendarCutoffHistory.GammaNew
      rate rewards C_star C_h control0)
    (Cstop_integrable rate rewards C_star C_h control0)
    (ReferenceFirstReplacementCollectionAwaitedCalendarWaitingCost.W_integrable
      rate rewards C_star C_h control0)
    (ae_of_all _ (fun z => Cstop_le_W rate rewards C_star C_h control0 z))
  exact hmono.trans
    (ReferenceFirstReplacementCollectionAwaitedCalendarWaitingCost.W_condExp_bound
      rate rewards C_star C_h control0)

/-- Every event in the existing issued-cutoff analysis field has the
unnormalized original-law bound for the inclusive stopped charge. -/
theorem Cstop_cutoff_setIntegral_bound
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (B : Set (BootstrapPrivateRoundStreams.SourceInput p))
    (hB : MeasurableSet[
      ReferenceFirstReplacementCollectionAwaitedCutoffHistory.GammaS_repl
        rate rewards C_star C_h control0] B) :
    (∫ z in B,
        ReferenceFirstReplacementCollectionInclusiveStoppedCharge.Cstop
          rate rewards C_star C_h z
      ∂BootstrapPrivateRoundStreams.sourceInputLaw p) ≤
      ReferenceFirstCollectionAwaitedWaitingCost.Bcol (p := p) *
        (BootstrapPrivateRoundStreams.sourceInputLaw p).real B := by
  have hle :
      ReferenceFirstReplacementCollectionInclusiveStoppedCharge.Cstop
        rate rewards C_star C_h ≤ᵐ[BootstrapPrivateRoundStreams.sourceInputLaw p]
      ReferenceFirstReplacementCollectionAwaitedCalendarWaitingCost.W
        rate rewards C_star C_h control0 :=
    ae_of_all _ (fun z => Cstop_le_W rate rewards C_star C_h control0 z)
  calc
    (∫ z in B,
        ReferenceFirstReplacementCollectionInclusiveStoppedCharge.Cstop
          rate rewards C_star C_h z
      ∂BootstrapPrivateRoundStreams.sourceInputLaw p) ≤
      ∫ z in B,
        ReferenceFirstReplacementCollectionAwaitedCalendarWaitingCost.W
          rate rewards C_star C_h control0 z
        ∂BootstrapPrivateRoundStreams.sourceInputLaw p :=
      setIntegral_mono_ae
        (Cstop_integrable rate rewards C_star C_h control0).integrableOn
        (ReferenceFirstReplacementCollectionAwaitedCalendarWaitingCost.W_integrable
          rate rewards C_star C_h control0).integrableOn hle
    _ ≤ ReferenceFirstCollectionAwaitedWaitingCost.Bcol (p := p) *
        (BootstrapPrivateRoundStreams.sourceInputLaw p).real B :=
      ReferenceFirstReplacementCollectionAwaitedCalendarCutoffHistory.W_cutoff_setIntegral_bound
        rate rewards C_star C_h control0 B hB

/-- The conditional expectation of the inclusive stopped charge is bounded
by `Bcol` at the exact existing issued-cutoff analysis field. -/
theorem Cstop_cutoff_condExp_bound
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p) :
    (BootstrapPrivateRoundStreams.sourceInputLaw p)[
      ReferenceFirstReplacementCollectionInclusiveStoppedCharge.Cstop
        rate rewards C_star C_h |
      ReferenceFirstReplacementCollectionAwaitedCutoffHistory.GammaS_repl
        rate rewards C_star C_h control0] ≤ᵐ[
          BootstrapPrivateRoundStreams.sourceInputLaw p]
      fun _ => ReferenceFirstCollectionAwaitedWaitingCost.Bcol (p := p) := by
  have hmono := MeasureTheory.condExp_mono
    (m := ReferenceFirstReplacementCollectionAwaitedCutoffHistory.GammaS_repl
      rate rewards C_star C_h control0)
    (Cstop_integrable rate rewards C_star C_h control0)
    (ReferenceFirstReplacementCollectionAwaitedCalendarWaitingCost.W_integrable
      rate rewards C_star C_h control0)
    (ae_of_all _ (fun z => Cstop_le_W rate rewards C_star C_h control0 z))
  exact hmono.trans
    (ReferenceFirstReplacementCollectionAwaitedCalendarCutoffHistory.W_cutoff_condExp_bound
      rate rewards C_star C_h control0)

end Bandits.Support.ReferenceFirstReplacementCollectionStoppedChargeDomination

end
