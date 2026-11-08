/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstReplacementCollectionGlobalDecoderCharge
public import Bandits.Support.ReferenceFirstReplacementCollectionAwaitedCalendarWaitingCost
public import Bandits.Support.ReferenceFirstReplacementCollectionAwaitedCalendarCutoffHistory

/-!
# Waiting bounds for the globally decoder-safe first replacement collection

The original-law estimates compare the actual globally decoder-safe capped
charge with the supported awaited-calendar charge, at the exact new phase
start and at the existing issued-cutoff analysis field.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support ConstructorDimensions BootstrapPrivateRoundStreams
open ReferenceFirstReplacementCollectionGlobalDecoderCharge
open ReferenceFirstReplacementCollectionAwaitedCalendarWaitingCost
open ReferenceFirstReplacementCollectionAwaitedCalendarCutoffHistory
open scoped Classical

namespace Bandits.Support.ReferenceFirstReplacementCollectionDecoderSafeWaitingCost

variable {p : ConstructorDimensions.Parameters}

/-- The actual decoder-safe collection charge is bounded by the admitted
supported-date waiting charge for the same source and control. -/
theorem Cdec_le_W
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (z : BootstrapPrivateRoundStreams.SourceInput p) :
    ReferenceFirstReplacementCollectionGlobalDecoderCharge.Cdec
        rate rewards C_star C_h z ≤
      ReferenceFirstReplacementCollectionAwaitedCalendarWaitingCost.W
        rate rewards C_star C_h control0 z := by
  change ReferenceFirstReplacementCollectionGlobalDecoderCharge.Cdec
      rate rewards C_star C_h z ≤
    ∑ n ∈ Finset.range p.T,
      if (ReferenceFirstReplacementCollectionAwaitedTaskSupport.Pnew
          rate rewards C_star C_h control0 n z).Nonempty then
        ReferenceFirstCollectionRoundEndObservation.g rewards n z else 0
  exact ReferenceFirstReplacementCollectionGlobalDecoderCharge.Cdec_le_supportedCharge
    rate rewards C_star C_h control0 z

/-- The original-law integrability of the literal global decoder-safe charge.
Measurability and its pointwise comparison are both used. -/
theorem Cdec_integrable
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p) :
    Integrable
      (ReferenceFirstReplacementCollectionGlobalDecoderCharge.Cdec
        rate rewards C_star C_h)
      (BootstrapPrivateRoundStreams.sourceInputLaw p) := by
  have hW := ReferenceFirstReplacementCollectionAwaitedCalendarWaitingCost.W_integrable
    rate rewards C_star C_h control0
  have hmeas := ReferenceFirstReplacementCollectionGlobalDecoderCharge.Cdec_measurable
    rate rewards C_star C_h control0
  have hnonneg (z : BootstrapPrivateRoundStreams.SourceInput p) :=
    (ReferenceFirstReplacementCollectionGlobalDecoderCharge.Cdec_bounds
      rate rewards C_star C_h z).1
  have hle (z : BootstrapPrivateRoundStreams.SourceInput p) :=
    Cdec_le_W rate rewards C_star C_h control0 z
  have hnorm : ∀ z : BootstrapPrivateRoundStreams.SourceInput p,
      ‖ReferenceFirstReplacementCollectionGlobalDecoderCharge.Cdec
        rate rewards C_star C_h z‖ ≤
      ReferenceFirstReplacementCollectionAwaitedCalendarWaitingCost.W
        rate rewards C_star C_h control0 z := by
    intro z
    rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg z)]
    exact hle z
  exact hW.mono' hmeas.aestronglyMeasurable (ae_of_all _ hnorm)

/-- Every event in the exact new supported phase-start field has the
unnormalized original-law bound for the actual decoder-safe charge. -/
theorem Cdec_phaseStart_setIntegral_bound
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (B : Set (BootstrapPrivateRoundStreams.SourceInput p))
    (hB : MeasurableSet[
      ReferenceFirstReplacementCollectionAwaitedCalendarCutoffHistory.GammaNew
        rate rewards C_star C_h control0] B) :
    (∫ z in B,
        ReferenceFirstReplacementCollectionGlobalDecoderCharge.Cdec
          rate rewards C_star C_h z
      ∂BootstrapPrivateRoundStreams.sourceInputLaw p) ≤
      ReferenceFirstCollectionAwaitedWaitingCost.Bcol (p := p) *
        (BootstrapPrivateRoundStreams.sourceInputLaw p).real B := by
  have hle :
      ReferenceFirstReplacementCollectionGlobalDecoderCharge.Cdec
        rate rewards C_star C_h ≤ᵐ[BootstrapPrivateRoundStreams.sourceInputLaw p]
      ReferenceFirstReplacementCollectionAwaitedCalendarWaitingCost.W
        rate rewards C_star C_h control0 :=
    ae_of_all _ (Cdec_le_W rate rewards C_star C_h control0)
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
        ReferenceFirstReplacementCollectionGlobalDecoderCharge.Cdec
          rate rewards C_star C_h z
      ∂BootstrapPrivateRoundStreams.sourceInputLaw p) ≤
      ∫ z in B,
        ReferenceFirstReplacementCollectionAwaitedCalendarWaitingCost.W
          rate rewards C_star C_h control0 z
        ∂BootstrapPrivateRoundStreams.sourceInputLaw p :=
      setIntegral_mono_ae
        (Cdec_integrable rate rewards C_star C_h control0).integrableOn
        (ReferenceFirstReplacementCollectionAwaitedCalendarWaitingCost.W_integrable
          rate rewards C_star C_h control0).integrableOn hle
    _ ≤ ReferenceFirstCollectionAwaitedWaitingCost.Bcol (p := p) *
        (BootstrapPrivateRoundStreams.sourceInputLaw p).real B :=
      ReferenceFirstReplacementCollectionAwaitedCalendarWaitingCost.W_setIntegral_bound
        rate rewards C_star C_h control0 B hB'

/-- The decoder-safe charge has the same conditional `Bcol` bound at the
exact new supported phase-start field. -/
theorem Cdec_phaseStart_condExp_bound
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p) :
    (BootstrapPrivateRoundStreams.sourceInputLaw p)[
      ReferenceFirstReplacementCollectionGlobalDecoderCharge.Cdec
        rate rewards C_star C_h |
      ReferenceFirstReplacementCollectionAwaitedCalendarCutoffHistory.GammaNew
        rate rewards C_star C_h control0] ≤ᵐ[
          BootstrapPrivateRoundStreams.sourceInputLaw p]
      fun _ => ReferenceFirstCollectionAwaitedWaitingCost.Bcol (p := p) := by
  have hmono := MeasureTheory.condExp_mono
    (m := ReferenceFirstReplacementCollectionAwaitedCalendarCutoffHistory.GammaNew
      rate rewards C_star C_h control0)
    (Cdec_integrable rate rewards C_star C_h control0)
    (ReferenceFirstReplacementCollectionAwaitedCalendarWaitingCost.W_integrable
      rate rewards C_star C_h control0)
    (ae_of_all _ (Cdec_le_W rate rewards C_star C_h control0))
  exact hmono.trans
    (ReferenceFirstReplacementCollectionAwaitedCalendarWaitingCost.W_condExp_bound
      rate rewards C_star C_h control0)

/-- Every event in the actual issued-cutoff analysis field has the
unnormalized original-law bound for the actual decoder-safe charge. -/
theorem Cdec_cutoff_setIntegral_bound
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (B : Set (BootstrapPrivateRoundStreams.SourceInput p))
    (hB : MeasurableSet[
      ReferenceFirstReplacementCollectionAwaitedCutoffHistory.GammaS_repl
        rate rewards C_star C_h control0] B) :
    (∫ z in B,
        ReferenceFirstReplacementCollectionGlobalDecoderCharge.Cdec
          rate rewards C_star C_h z
      ∂BootstrapPrivateRoundStreams.sourceInputLaw p) ≤
      ReferenceFirstCollectionAwaitedWaitingCost.Bcol (p := p) *
        (BootstrapPrivateRoundStreams.sourceInputLaw p).real B := by
  have hle :
      ReferenceFirstReplacementCollectionGlobalDecoderCharge.Cdec
        rate rewards C_star C_h ≤ᵐ[BootstrapPrivateRoundStreams.sourceInputLaw p]
      ReferenceFirstReplacementCollectionAwaitedCalendarWaitingCost.W
        rate rewards C_star C_h control0 :=
    ae_of_all _ (Cdec_le_W rate rewards C_star C_h control0)
  calc
    (∫ z in B,
        ReferenceFirstReplacementCollectionGlobalDecoderCharge.Cdec
          rate rewards C_star C_h z
      ∂BootstrapPrivateRoundStreams.sourceInputLaw p) ≤
      ∫ z in B,
        ReferenceFirstReplacementCollectionAwaitedCalendarWaitingCost.W
          rate rewards C_star C_h control0 z
        ∂BootstrapPrivateRoundStreams.sourceInputLaw p :=
      setIntegral_mono_ae
        (Cdec_integrable rate rewards C_star C_h control0).integrableOn
        (ReferenceFirstReplacementCollectionAwaitedCalendarWaitingCost.W_integrable
          rate rewards C_star C_h control0).integrableOn hle
    _ ≤ ReferenceFirstCollectionAwaitedWaitingCost.Bcol (p := p) *
        (BootstrapPrivateRoundStreams.sourceInputLaw p).real B :=
      ReferenceFirstReplacementCollectionAwaitedCalendarCutoffHistory.W_cutoff_setIntegral_bound
        rate rewards C_star C_h control0 B hB

/-- The actual decoder-safe charge has the same conditional `Bcol` bound at
the existing issued-cutoff analysis field. -/
theorem Cdec_cutoff_condExp_bound
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p) :
    (BootstrapPrivateRoundStreams.sourceInputLaw p)[
      ReferenceFirstReplacementCollectionGlobalDecoderCharge.Cdec
        rate rewards C_star C_h |
      ReferenceFirstReplacementCollectionAwaitedCutoffHistory.GammaS_repl
        rate rewards C_star C_h control0] ≤ᵐ[
          BootstrapPrivateRoundStreams.sourceInputLaw p]
      fun _ => ReferenceFirstCollectionAwaitedWaitingCost.Bcol (p := p) := by
  have hmono := MeasureTheory.condExp_mono
    (m := ReferenceFirstReplacementCollectionAwaitedCutoffHistory.GammaS_repl
      rate rewards C_star C_h control0)
    (Cdec_integrable rate rewards C_star C_h control0)
    (ReferenceFirstReplacementCollectionAwaitedCalendarWaitingCost.W_integrable
      rate rewards C_star C_h control0)
    (ae_of_all _ (Cdec_le_W rate rewards C_star C_h control0))
  exact hmono.trans
    (ReferenceFirstReplacementCollectionAwaitedCalendarCutoffHistory.W_cutoff_condExp_bound
      rate rewards C_star C_h control0)

end Bandits.Support.ReferenceFirstReplacementCollectionDecoderSafeWaitingCost

end
