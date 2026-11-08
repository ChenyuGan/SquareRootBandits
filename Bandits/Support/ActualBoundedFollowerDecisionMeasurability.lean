/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ActualBoundedFollowerDecision
public import Bandits.Support.ActualFollowerFiniteHistoryReplayMeasurability

/-!
# Joint Borel measurability of bounded follower decisions and terminal readouts

The maps in this module compose the actual bounded-history follower with the
existing finite-history replay. They retain the complete published output, the
follower's original private block triples and own-round scalars, and every
bounded real local history. No realizability or actual-history premise is
required.

Mathematical evidence: `sources/zip4/manuscript/01_introduction.tex:18-36`,
`sources/zip4/manuscript/07_public_setup.tex:27-38,55-114`,
`sources/zip4/manuscript/06_interruptions.tex:240-296`,
`sources/zip4/manuscript/appendix_a_local_protocol.tex:6-14`, and
`sources/zip4/manuscript/08_main_theorem.tex:163-168`.

The terminal maps retain the existing boundary code and the separate final
bootstrap numerator observable. These internal Borel results do not assert a
law for the whole execution or close a regret theorem.
-/

@[expose] public section

open MeasureTheory
open Bandits.Support.ActualFollowerCalendarContinuity
open Bandits.Support.FiniteBoundedLocalHistoryCode

namespace Bandits.Support.ActualBoundedFollowerDecisionMeasurability

open ActualBoundedFollowerDecision
open ActualFollowerFiniteHistoryReplay

variable {p : ActualBoundedFollowerDecision.Parameters}

private theorem measurable_boundedHistoryCodeInput {n : ℕ} :
    Measurable (fun z : ActualFollowerFiniteHistoryReplay.Published p ×
        (ActualFollowerFiniteHistoryReplay.Own p ×
          ActualBoundedFollowerDecision.BoundedHistory p n) =>
      (z.1, (z.2.1, FiniteBoundedLocalHistoryCode.Q p z.2.2))) := by
  exact measurable_fst.prodMk
    ((measurable_fst.comp measurable_snd).prodMk
      ((FiniteBoundedLocalHistoryCode.Q_measurable p).comp
        (measurable_snd.comp measurable_snd)))

/-- The bounded follower decision is jointly Borel on the full published,
own-coordinate, and bounded-history product. The supplied real history is
quantized by the existing floor code before the existing replay decision. -/
theorem measurable_followerBoundedDecision
    (rate : ActualBoundedFollowerDecision.RateInput p) (a b : ℝ)
    (i : Fin (p.m - 1)) (t : Fin p.T) :
    Measurable (ActualBoundedFollowerDecision.followerBoundedDecision
      rate a b i t) := by
  change Measurable (fun z : ActualBoundedFollowerDecision.DecisionInput p t =>
    ActualFollowerFiniteHistoryReplay.followerGridDecision rate a b i z.1 z.2.1 t
      (FiniteBoundedLocalHistoryCode.Q p z.2.2))
  exact (ActualFollowerFiniteHistoryReplayMeasurability.follower_grid_decision_measurable
    rate a b i t).comp measurable_boundedHistoryCodeInput

/-- The bounded-history before-replay code is exactly the first projection of
the existing dependent replay code after applying `Q`. -/
theorem measurable_followerBoundedReplayCode
    (rate : ActualBoundedFollowerDecision.RateInput p) (a b : ℝ)
    (i : Fin (p.m - 1)) (t : Fin p.T) :
    Measurable (fun z : ActualBoundedFollowerDecision.DecisionInput p t =>
      (ActualFollowerFiniteHistoryReplay.followerReplayCode rate a b i
        z.1 z.2.1 t (FiniteBoundedLocalHistoryCode.Q p z.2.2)).1) := by
  exact (ActualFollowerFiniteHistoryReplayMeasurability.follower_replay_code_measurable
    rate a b i t).comp measurable_boundedHistoryCodeInput

/-- The existing un-coded before-round follower state is definitionally the
decoder applied to that same replay code. This identity makes no claim that
the dependent full-storage state is measurable. -/
theorem followerBoundedReplayBefore_eq_decodedReplayCode
    (rate : ActualBoundedFollowerDecision.RateInput p) (a b : ℝ)
    (i : Fin (p.m - 1)) (t : Fin p.T)
    (z : ActualBoundedFollowerDecision.DecisionInput p t) :
    ActualBoundedFollowerDecision.followerBoundedReplayBefore rate a b i
        z.1 z.2.1 t z.2.2 =
      ActualInitializationRoundMeasurability.followerStateOfCode p rate
        (ActualFollowerCalendarContinuity.calendarBlockIndex t)
        (ActualFollowerFiniteHistoryReplay.followerReplayCode rate a b i
          z.1 z.2.1 t (FiniteBoundedLocalHistoryCode.Q p z.2.2)).1 := by
  rfl

/-- The literal terminal boundary code of the bounded follower is jointly
Borel at horizon `T`, including clipped boundaries and terminal declarations. -/
theorem measurable_followerBoundedTerminalCode
    (rate : ActualBoundedFollowerDecision.RateInput p) (a b : ℝ)
    (i : Fin (p.m - 1)) :
    Measurable (fun z : ActualBoundedFollowerDecision.Published p ×
        (ActualBoundedFollowerDecision.Own p ×
          ActualBoundedFollowerDecision.BoundedHistory p p.T) =>
      ActualBoundedFollowerDecision.followerBoundedTerminalCode rate a b i
        z.1 z.2.1 z.2.2) := by
  change Measurable (fun z : ActualBoundedFollowerDecision.Published p ×
      (ActualBoundedFollowerDecision.Own p ×
        ActualBoundedFollowerDecision.BoundedHistory p p.T) =>
    ActualFollowerFiniteHistoryReplay.followerTerminalCode rate a b i
      z.1 z.2.1 (FiniteBoundedLocalHistoryCode.Q p z.2.2))
  exact (ActualFollowerFiniteHistoryReplayMeasurability.follower_terminal_code_measurable
    rate a b i).comp measurable_boundedHistoryCodeInput

/-- The separate terminal bootstrap numerator update is jointly Borel on the
same full product, even when the terminal boundary conversion drops weights. -/
theorem measurable_followerBoundedTerminalUpdatedNumerators
    (rate : ActualBoundedFollowerDecision.RateInput p) (a b : ℝ)
    (i : Fin (p.m - 1)) :
    Measurable (fun z : ActualBoundedFollowerDecision.Published p ×
        (ActualBoundedFollowerDecision.Own p ×
          ActualBoundedFollowerDecision.BoundedHistory p p.T) =>
      ActualBoundedFollowerDecision.followerBoundedTerminalUpdatedNumerators
        rate a b i z.1 z.2.1 z.2.2) := by
  change Measurable (fun z : ActualBoundedFollowerDecision.Published p ×
      (ActualBoundedFollowerDecision.Own p ×
        ActualBoundedFollowerDecision.BoundedHistory p p.T) =>
    ActualFollowerFiniteHistoryReplay.followerTerminalUpdatedNumerators rate a b i
      z.1 z.2.1 (FiniteBoundedLocalHistoryCode.Q p z.2.2))
  exact (ActualFollowerFiniteHistoryReplayMeasurability.follower_terminal_updated_numerators_measurable
    rate a b i).comp measurable_boundedHistoryCodeInput

end Bandits.Support.ActualBoundedFollowerDecisionMeasurability

end
