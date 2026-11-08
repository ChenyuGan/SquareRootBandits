/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferencePhysicalReleaseObservability
public import Bandits.Support.ReferenceRetainedBoundaryMeasurability

/-!
# Retained assignment release history on an actual generated run

Sources: `sources/zip4/manuscript/05_binary_transport.tex:74-88,297-345`,
`sources/zip4/manuscript/06_interruptions.tex:40-61,435-492`,
`sources/zip4/manuscript/07_public_setup.tex:121-164`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-79`.

The module projects the whole assignment payload actually retained at a
generated launch boundary, its retrospective pending history on the existing
physical horizon fold, and its current UP/DATA flags on the actual next input.
The payload is traced to a unique actual installation in that same run.
These are deterministic and Borel support results. They do not identify a
source stopping time or filtration, prove conditional service, or close a
regret assertion.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalStepMeasurability
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceActiveHorizonMeasurability
open Bandits.Support.ReferenceGeneratedActivePrefixFactor
open Bandits.Support.ReferenceAssignmentPayloadPersistence
open Bandits.Support.ReferenceAssignmentPayloadChronology
open Bandits.Support.ReferenceLaterInstallationProvenance
open Bandits.Support.ReferencePhysicalReleaseQuota
open Bandits.Support.ReferencePhysicalReleaseObservability
open Bandits.Support.ReferenceRetainedBoundaryMeasurability
open Bandits.Support.ReferenceFixedTimeSourceControlCoupling
open Bandits.Support.ReferenceCorrectedInitializationLaunch
open Bandits.Support.ReferenceInitializationRun
open Bandits.Support.ActualReferenceInitializationBlock
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.LaterAssignmentStartMeasurability
open Bandits.Support.ReferenceCollectionInstallOutputMeasurability
open Bandits.Support.LaterAssignmentFullOutputMeasurability
open scoped Classical

namespace Bandits.Support.ReferenceRetainedAssignmentReleaseHistory

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev TimeControl := ContinuousLearningRows.TimeControl
abbrev SourceInput := BootstrapPrivateRoundStreams.SourceInput

variable {p : Parameters} {rate : RateInput p}

abbrev Payload := ReferenceActivePhysicalStep.Payload (p := p) rate
abbrev Record := ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)

abbrev RetainedLaunchStartInput (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ) (hs : s ≤ t.val)
    (control0 : TimeControl p) :=
  ReferenceRetainedBoundaryMeasurability.RetainedLaunchStart
    rate rewards C_star C_h q t s hs control0

def retainedHistoryTime (s : ℕ) (t : Fin p.T) (hs : s ≤ t.val)
    (j : Fin (t.val - s + 1)) : Fin p.T :=
  ⟨s + j.val, by have hj := j.isLt; omega⟩

/-- The actual generated horizon prefix for one removed current control.
This is a direct alias of `generatedActivePrefixFactor`, the existing physical
fold; it defines no second transition or recursive execution. -/
def retainedGeneratedPrefix
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p)
    (x : RetainedLaunchStartInput (p := p) rate rewards C_star C_h q t s hs control0)
    (control : TimeControl p) (count : ℕ) (hcount : s + count ≤ t.val) :=
  let hparts : x.1 ∈ ReferenceFixedTimeSourceControlCoupling.fixedControlRemainderStratum
      p q t ∧ x.1 ∈ ReferenceInitializationControlRemainder.launchStartRemainderEvent
        rate rewards C_star C_h q t s control0 := by
    change x.1 ∈ ReferenceRetainedBoundaryMeasurability.retainedLaunchStartSet
      rate rewards C_star C_h q t s control0
    change x.1 ∈ ReferenceFixedTimeSourceControlCoupling.fixedControlRemainderStratum p q t ∩
      ReferenceInitializationControlRemainder.launchStartRemainderEvent
        rate rewards C_star C_h q t s control0
    exact x.2
  ReferenceGeneratedActivePrefixFactor.generatedActivePrefixFactor
    rate rewards C_star C_h q t control x.1 hparts.1 s count hs
    ((ReferenceInitializationControlRemainder.launchStartRemainderEvent_control_independent
      rate rewards C_star C_h q t s x.1 hparts.1 control0 control).mp hparts.2)
    hcount

/-- The whole payload currently retained by the actual incoming coordinator
configuration. First and dagger give `none`; live and collection retain their
literal whole payload, including its real anchor and queue vector. -/
def retainedAssignmentSelection
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p)
    (x : RetainedLaunchStartInput (p := p) rate rewards C_star C_h q t s hs control0) :
    Option (ℕ × Payload (p := p) (rate := rate)) :=
  (ReferenceAssignmentPayloadPersistence.storedPayload
    (ReferenceRetainedBoundaryMeasurability.retainedIncomingBoundary
      rate rewards C_star C_h q t s hs control0 x).state.coordinator).map
    (fun M => (M.sigma.val, M))

/-- The same retained-payload selector evaluated on the actual generated
prefix for `control`. -/
def retainedAssignmentSelectionAtControl
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p)
    (x : RetainedLaunchStartInput (p := p) rate rewards C_star C_h q t s hs control0)
    (control : TimeControl p) : Option (ℕ × Payload (p := p) (rate := rate)) :=
  (ReferenceAssignmentPayloadPersistence.storedPayload
    (retainedGeneratedPrefix rate rewards C_star C_h q t s hs control0 x control
      (t.val - s) (by omega)).finalState.coordinator).map
    (fun M => (M.sigma.val, M))

/-- The historical pending projection through every prefix endpoint from the
launch round through and including the current incoming boundary. Earlier
coordinates are retrospective relative to the payload selected at `t`. -/
def retainedPendingHistory
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p)
    (x : RetainedLaunchStartInput (p := p) rate rewards C_star C_h q t s hs control0) :
    Option ((ℕ × Payload (p := p) (rate := rate)) ×
      (Fin (t.val - s + 1) → Finset (Fin (p.m - 1)))) :=
  (retainedAssignmentSelection rate rewards C_star C_h q t s hs control0 x).map
    (fun selected =>
      (selected, fun j => ReferencePhysicalReleaseQuota.pendingAtStart selected.2
        (retainedHistoryTime s t hs j)
        (retainedGeneratedPrefix rate rewards C_star C_h q t s hs control0 x control0
          j.val (by have hj := j.isLt; omega)).finalState))

/-- The same pending projection made from the generated run for an arbitrary
current control. Its history remains the actual prefix on that control's
reconstructed original source. -/
def retainedPendingHistoryAtControl
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p)
    (x : RetainedLaunchStartInput (p := p) rate rewards C_star C_h q t s hs control0)
    (control : TimeControl p) :
    Option ((ℕ × Payload (p := p) (rate := rate)) ×
      (Fin (t.val - s + 1) → Finset (Fin (p.m - 1)))) :=
  (retainedAssignmentSelectionAtControl rate rewards C_star C_h q t s hs control0 x control).map
    (fun selected =>
      (selected, fun j => ReferencePhysicalReleaseQuota.pendingAtStart selected.2
        (retainedHistoryTime s t hs j)
        (retainedGeneratedPrefix rate rewards C_star C_h q t s hs control0 x control
          j.val (by have hj := j.isLt; omega)).finalState))

/-- The literal current UP and DATA release tests for the retained payload,
evaluated on the generated actual next input. `none` remains visible. -/
def retainedReleaseFlags
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p)
    (x : RetainedLaunchStartInput (p := p) rate rewards C_star C_h q t s hs control0)
    (control : TimeControl p) (i : Fin (p.m - 1)) : Option (Bool × Bool) :=
  (retainedAssignmentSelection rate rewards C_star C_h q t s hs control0 x).map
    (fun selected =>
      (ReferencePhysicalReleaseQuota.upFlag selected.2
        (ReferencePhysicalReleaseObservability.recordOfInput
          (ReferenceRetainedBoundaryMeasurability.retainedGeneratedNextInput
            rate rewards C_star C_h q t s hs control0 x control)) i,
       ReferencePhysicalReleaseQuota.dataFlag selected.2
        (ReferencePhysicalReleaseObservability.recordOfInput
          (ReferenceRetainedBoundaryMeasurability.retainedGeneratedNextInput
            rate rewards C_star C_h q t s hs control0 x control)) i))

@[simp] theorem retainedAssignmentSelection_none_iff
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p)
    (x : RetainedLaunchStartInput (p := p) rate rewards C_star C_h q t s hs control0) :
    retainedAssignmentSelection rate rewards C_star C_h q t s hs control0 x = none ↔
      (ReferenceRetainedBoundaryMeasurability.retainedIncomingBoundary
        rate rewards C_star C_h q t s hs control0 x).state.coordinator = .first ∨
      (ReferenceRetainedBoundaryMeasurability.retainedIncomingBoundary
        rate rewards C_star C_h q t s hs control0 x).state.coordinator = .dagger := by
  let c := (ReferenceRetainedBoundaryMeasurability.retainedIncomingBoundary
    rate rewards C_star C_h q t s hs control0 x).state.coordinator
  change (ReferenceAssignmentPayloadPersistence.storedPayload c).map
      (fun M => (M.sigma.val, M)) = none ↔ c = .first ∨ c = .dagger
  cases c <;> simp [ReferenceAssignmentPayloadPersistence.storedPayload]

@[simp] theorem retainedAssignmentSelectionAtControl_baseline
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p)
    (x : RetainedLaunchStartInput (p := p) rate rewards C_star C_h q t s hs control0) :
    retainedAssignmentSelectionAtControl rate rewards C_star C_h q t s hs control0 x control0 =
      retainedAssignmentSelection rate rewards C_star C_h q t s hs control0 x := by
  change (ReferenceAssignmentPayloadPersistence.storedPayload
      (retainedGeneratedPrefix rate rewards C_star C_h q t s hs control0 x control0
        (t.val - s) (by omega)).finalState.coordinator).map (fun M => (M.sigma.val, M)) =
    (ReferenceAssignmentPayloadPersistence.storedPayload
      (ReferenceRetainedBoundaryMeasurability.retainedIncomingBoundary
        rate rewards C_star C_h q t s hs control0 x).state.coordinator).map
      (fun M => (M.sigma.val, M))
  exact congrArg
    (fun state : ReferenceActivePhysicalStep.State p rate =>
      (ReferenceAssignmentPayloadPersistence.storedPayload state.coordinator).map
        (fun M => (M.sigma.val, M)))
    (ReferenceRetainedBoundaryMeasurability.retainedIncomingBoundary_state
      rate rewards C_star C_h q t s hs control0 x)

/-- Every removed current-control value gives the same final state and
chronological record evidence on this actual generated prefix. This is the
existing control-independence theorem for the accepted physical fold. -/
theorem retainedGeneratedPrefix_control_independent
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p)
    (x : RetainedLaunchStartInput (p := p) rate rewards C_star C_h q t s hs control0)
    (control control' : TimeControl p) (count : ℕ)
    (hcount : s + count ≤ t.val) :
    (retainedGeneratedPrefix rate rewards C_star C_h q t s hs control0 x control
      count hcount).finalState =
      (retainedGeneratedPrefix rate rewards C_star C_h q t s hs control0 x control'
        count hcount).finalState ∧
    (retainedGeneratedPrefix rate rewards C_star C_h q t s hs control0 x control
      count hcount).records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence =
      (retainedGeneratedPrefix rate rewards C_star C_h q t s hs control0 x control'
        count hcount).records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence := by
  have hfactor := ReferenceGeneratedActivePrefixFactor.generatedActivePrefixFactor_control_independent
    rate rewards C_star C_h q t x.1 x.2.1 control0 s count hs hcount x.2.2 control control'
  rcases hfactor with ⟨active, _, _, _, _, _, hstate, hevidence⟩
  exact ⟨hstate, hevidence⟩

/-- The common corrected-launch seed, final physical state, and chronological
record evidence agree for two current controls on the same original launch
remainder. This keeps the whole seed equality available to consumers. -/
theorem retainedGeneratedPrefix_seed_control_independent
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p)
    (x : RetainedLaunchStartInput (p := p) rate rewards C_star C_h q t s hs control0)
    (control control' : TimeControl p) (count : ℕ)
    (hcount : s + count ≤ t.val) :
    ReferenceGeneratedActivePrefixFactor.generatedActiveSeed rate rewards C_star C_h q t control
      x.1 x.2.1 s hs
        ((ReferenceInitializationControlRemainder.launchStartRemainderEvent_control_independent
          rate rewards C_star C_h q t s x.1 x.2.1 control0 control).mp x.2.2) =
      ReferenceGeneratedActivePrefixFactor.generatedActiveSeed rate rewards C_star C_h q t control'
        x.1 x.2.1 s hs
          ((ReferenceInitializationControlRemainder.launchStartRemainderEvent_control_independent
            rate rewards C_star C_h q t s x.1 x.2.1 control0 control').mp x.2.2) ∧
    (retainedGeneratedPrefix rate rewards C_star C_h q t s hs control0 x control count hcount).finalState =
      (retainedGeneratedPrefix rate rewards C_star C_h q t s hs control0 x control' count hcount).finalState ∧
    (retainedGeneratedPrefix rate rewards C_star C_h q t s hs control0 x control count hcount).records.map
        ReferenceActivePhysicalHorizon.RoundRecord.evidence =
      (retainedGeneratedPrefix rate rewards C_star C_h q t s hs control0 x control' count hcount).records.map
        ReferenceActivePhysicalHorizon.RoundRecord.evidence := by
  let hstart := (ReferenceInitializationControlRemainder.launchStartRemainderEvent_control_independent
    rate rewards C_star C_h q t s x.1 x.2.1 control0 control).mp x.2.2
  let hstart' := (ReferenceInitializationControlRemainder.launchStartRemainderEvent_control_independent
    rate rewards C_star C_h q t s x.1 x.2.1 control0 control').mp x.2.2
  obtain ⟨active, hlaunch0, hlaunch, hlaunch', _, _, _, _⟩ :=
    ReferenceGeneratedActivePrefixFactor.generatedActivePrefixFactor_control_independent
      rate rewards C_star C_h q t x.1 x.2.1 control0 s count hs hcount x.2.2 control control'
  have hseedSpec := ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec
    rate rewards C_star C_h q t control x.1 x.2.1 s hs hstart
  have hseedSpec' := ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec
    rate rewards C_star C_h q t control' x.1 x.2.1 s hs hstart'
  have hseed : ReferenceGeneratedActivePrefixFactor.generatedActiveSeed rate rewards C_star C_h q t
      control x.1 x.2.1 s hs hstart = active :=
    Option.some.inj (hseedSpec.1.symm.trans hlaunch)
  have hseed' : ReferenceGeneratedActivePrefixFactor.generatedActiveSeed rate rewards C_star C_h q t
      control' x.1 x.2.1 s hs hstart' = active :=
    Option.some.inj (hseedSpec'.1.symm.trans hlaunch')
  have hrun := retainedGeneratedPrefix_control_independent rate rewards C_star C_h q t s hs
    control0 x control control' count hcount
  exact ⟨hseed.trans hseed'.symm, hrun.1, hrun.2⟩

/-- The retained selector carries the same whole payload on every generated
control run, including the same `none` branch. No equality of whole rows is
asserted. -/
theorem retainedAssignmentSelectionAtControl_eq
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p)
    (x : RetainedLaunchStartInput (p := p) rate rewards C_star C_h q t s hs control0)
    (control : TimeControl p) :
    retainedAssignmentSelectionAtControl rate rewards C_star C_h q t s hs control0 x control =
      retainedAssignmentSelection rate rewards C_star C_h q t s hs control0 x := by
  have hstate := (retainedGeneratedPrefix_control_independent rate rewards C_star C_h q t s
    hs control0 x control control0 (t.val - s) (by omega)).1
  have hboundary := ReferenceRetainedBoundaryMeasurability.retainedIncomingBoundary_state
    rate rewards C_star C_h q t s hs control0 x
  change (ReferenceAssignmentPayloadPersistence.storedPayload
      (retainedGeneratedPrefix rate rewards C_star C_h q t s hs control0 x control
        (t.val - s) (by omega)).finalState.coordinator).map (fun M => (M.sigma.val, M)) =
    (ReferenceAssignmentPayloadPersistence.storedPayload
      (ReferenceRetainedBoundaryMeasurability.retainedIncomingBoundary
        rate rewards C_star C_h q t s hs control0 x).state.coordinator).map
      (fun M => (M.sigma.val, M))
  exact congrArg (fun state : ReferenceActivePhysicalStep.State p rate =>
    (ReferenceAssignmentPayloadPersistence.storedPayload state.coordinator).map
      (fun M => (M.sigma.val, M))) (hstate.trans hboundary.symm)

/-- The whole retrospective pending history is unchanged when the removed
current control varies. Every coordinate uses the same actual prefix fold. -/
theorem retainedPendingHistoryAtControl_eq
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p)
    (x : RetainedLaunchStartInput (p := p) rate rewards C_star C_h q t s hs control0)
    (control : TimeControl p) :
    retainedPendingHistoryAtControl rate rewards C_star C_h q t s hs control0 x control =
      retainedPendingHistory rate rewards C_star C_h q t s hs control0 x := by
  have hselection := retainedAssignmentSelectionAtControl_eq rate rewards C_star C_h q t s
    hs control0 x control
  cases hbase : retainedAssignmentSelection rate rewards C_star C_h q t s hs control0 x with
  | none =>
      simp [retainedPendingHistoryAtControl, retainedPendingHistory, hselection, hbase]
  | some selected =>
      simp only [retainedPendingHistoryAtControl, retainedPendingHistory, hselection, hbase,
        Option.map_some]
      apply congrArg (fun history : Fin (t.val - s + 1) → Finset (Fin (p.m - 1)) =>
        some (selected, history))
      funext j
      exact congrArg (fun state : ReferenceActivePhysicalStep.State p rate =>
        ReferencePhysicalReleaseQuota.pendingAtStart selected.2
          (retainedHistoryTime s t hs j) state)
        ((retainedGeneratedPrefix_control_independent rate rewards C_star C_h q t s
          hs control0 x control control0 j.val (by have hj := j.isLt; omega)).1)

/-- Whole history factorization together with seed, state, and chronological
evidence equality at every retrospective endpoint, including the current
incoming boundary. -/
theorem retainedPendingHistoryAtControl_eq_withChronology
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p)
    (x : RetainedLaunchStartInput (p := p) rate rewards C_star C_h q t s hs control0)
    (control control' : TimeControl p) :
    retainedPendingHistoryAtControl rate rewards C_star C_h q t s hs control0 x control =
      retainedPendingHistoryAtControl rate rewards C_star C_h q t s hs control0 x control' ∧
    ∀ j : Fin (t.val - s + 1),
      ReferenceGeneratedActivePrefixFactor.generatedActiveSeed rate rewards C_star C_h q t control
        x.1 x.2.1 s hs
          ((ReferenceInitializationControlRemainder.launchStartRemainderEvent_control_independent
            rate rewards C_star C_h q t s x.1 x.2.1 control0 control).mp x.2.2) =
        ReferenceGeneratedActivePrefixFactor.generatedActiveSeed rate rewards C_star C_h q t control'
          x.1 x.2.1 s hs
            ((ReferenceInitializationControlRemainder.launchStartRemainderEvent_control_independent
              rate rewards C_star C_h q t s x.1 x.2.1 control0 control').mp x.2.2) ∧
      (retainedGeneratedPrefix rate rewards C_star C_h q t s hs control0 x control j.val
        (by have hj := j.isLt; omega)).finalState =
      (retainedGeneratedPrefix rate rewards C_star C_h q t s hs control0 x control' j.val
        (by have hj := j.isLt; omega)).finalState ∧
      (retainedGeneratedPrefix rate rewards C_star C_h q t s hs control0 x control j.val
        (by have hj := j.isLt; omega)).records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence =
      (retainedGeneratedPrefix rate rewards C_star C_h q t s hs control0 x control' j.val
        (by have hj := j.isLt; omega)).records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence := by
  refine ⟨?_, ?_⟩
  · exact retainedPendingHistoryAtControl_eq rate rewards C_star C_h q t s hs control0 x control
      |>.trans (retainedPendingHistoryAtControl_eq rate rewards C_star C_h q t s hs control0 x
        control').symm
  · intro j
    exact retainedGeneratedPrefix_seed_control_independent rate rewards C_star C_h q t s hs
      control0 x control control' j.val (by have hj := j.isLt; omega)

/-- The final retrospective coordinate is the pending set on the generated
incoming input, for every control and conditional only on the real selector
branch. -/
theorem retainedPendingHistory_last_eq_generatedNextInput
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p)
    (x : RetainedLaunchStartInput (p := p) rate rewards C_star C_h q t s hs control0)
    (control : TimeControl p) (b : ℕ) (M : Payload (p := p) (rate := rate))
    (hsel : retainedAssignmentSelection rate rewards C_star C_h q t s hs control0 x = some (b, M)) :
    (retainedPendingHistoryAtControl rate rewards C_star C_h q t s hs control0 x control).map
      (fun h => h.2 ⟨t.val - s, by omega⟩) =
      some (ReferencePhysicalReleaseQuota.pendingAtStart M t
        (ReferenceRetainedBoundaryMeasurability.retainedGeneratedNextInput
          rate rewards C_star C_h q t s hs control0 x control).state) := by
  have hhistory := retainedPendingHistoryAtControl_eq rate rewards C_star C_h q t s
    hs control0 x control
  rw [hhistory, retainedPendingHistory, hsel]
  simp only [Option.map_some]
  congr 1
  have htime : retainedHistoryTime s t hs ⟨t.val - s, by omega⟩ = t := by
    apply Fin.ext
    simp only [retainedHistoryTime]
    omega
  rw [htime]
  have hboundary := ReferenceRetainedBoundaryMeasurability.retainedIncomingBoundary_state
    rate rewards C_star C_h q t s hs control0 x
  have hnextInput := ReferenceRetainedBoundaryMeasurability.retainedGeneratedNextInput_eq_roundInputAtSource
    rate rewards C_star C_h q t s hs control0 x control
  have hnextState :
      (ReferenceRetainedBoundaryMeasurability.retainedGeneratedNextInput
        rate rewards C_star C_h q t s hs control0 x control).state =
      (ReferenceRetainedBoundaryMeasurability.retainedIncomingBoundary
        rate rewards C_star C_h q t s hs control0 x).state := by
    have hstate := congrArg ReferenceActivePhysicalStep.RoundInput.state hnextInput
    change (ReferenceRetainedBoundaryMeasurability.retainedGeneratedNextInput
        rate rewards C_star C_h q t s hs control0 x control).state =
      (ReferenceRetainedBoundaryMeasurability.retainedIncomingBoundary
        rate rewards C_star C_h q t s hs control0 x).state at hstate
    exact hstate
  exact congrArg (ReferencePhysicalReleaseQuota.pendingAtStart M t)
    (hboundary.symm.trans hnextState.symm)

/-- A selected whole payload has a unique actual installation in the same
generated run. The record lookup uses the physical calendar coordinate
`b - s`; the only selector premise is the literal retained branch. -/
theorem retainedAssignmentSelection_has_unique_actual_installation
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p)
    (x : RetainedLaunchStartInput (p := p) rate rewards C_star C_h q t s hs control0)
    (b : ℕ) (M : Payload (p := p) (rate := rate))
    (hsel : retainedAssignmentSelection rate rewards C_star C_h q t s hs control0 x = some (b, M)) :
    b = M.sigma.val ∧
      ∃ record : Record (p := p) (rate := rate),
        record ∈ (retainedGeneratedPrefix rate rewards C_star C_h q t s hs control0 x control0
          (t.val - s) (by omega)).records ∧
        ReferenceAssignmentPayloadPersistence.InstallationBirth record M ∧
        record.input.time.val = b ∧ s ≤ b ∧ b < t.val ∧
        (retainedGeneratedPrefix rate rewards C_star C_h q t s hs control0 x control0
          (t.val - s) (by omega)).records[b - s]? = some record ∧
        (∀ other : Record (p := p) (rate := rate),
          other ∈ (retainedGeneratedPrefix rate rewards C_star C_h q t s hs control0 x control0
            (t.val - s) (by omega)).records →
          ReferenceAssignmentPayloadPersistence.InstallationBirth other M → other = record) := by
  let boundary := ReferenceRetainedBoundaryMeasurability.retainedIncomingBoundary
    rate rewards C_star C_h q t s hs control0 x
  let source := ReferenceGeneratedActivePrefixFactor.splitSource q t control0 x.1
  let count := t.val - s
  let seed := ReferenceGeneratedActivePrefixFactor.generatedActiveSeed
    rate rewards C_star C_h q t control0 x.1 x.2.1 s hs x.2.2
  have hselectionFacts : b = M.sigma.val ∧
      ReferenceAssignmentPayloadPersistence.storedPayload boundary.state.coordinator = some M := by
    have hsel' :
        (ReferenceAssignmentPayloadPersistence.storedPayload boundary.state.coordinator).map
          (fun payload => (payload.sigma.val, payload)) = some (b, M) := by
      change retainedAssignmentSelection rate rewards C_star C_h q t s hs control0 x = some (b, M) at hsel
      exact hsel
    cases hp : ReferenceAssignmentPayloadPersistence.storedPayload boundary.state.coordinator with
    | none =>
        rw [hp] at hsel'
        cases hsel'
    | some stored =>
        have hpair : (stored.sigma.val, stored) = (b, M) := by
          apply Option.some.inj
          simpa only [hp, Option.map_some] using hsel'
        rcases Prod.mk.inj hpair with ⟨hb, hM⟩
        have hstored :
            ReferenceAssignmentPayloadPersistence.storedPayload boundary.state.coordinator = some M := by
          rw [hp, hM]
        have hstored' : some stored = some M := congrArg some hM
        have hBM : M.sigma.val = b := by rw [← hM]; exact hb
        exact ⟨hBM.symm, hstored'⟩
  obtain ⟨hB, hstoredBoundary⟩ := hselectionFacts
  have hfacts := ReferenceGeneratedActivePrefixFactor.launchStart_source_facts
    rate rewards C_star C_h q t control0 x.1 x.2.1 s hs x.2.2
  obtain ⟨hcross, helapsed⟩ := hfacts
  obtain ⟨initial, hlaunch, hinitial, _, _, _⟩ :=
    ReferenceCorrectedInitializationLaunch.correctedLaunch_coordinator_provenance
      rate source rewards C_star C_h hcross
  have hseedSpec := ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec
    rate rewards C_star C_h q t control0 x.1 x.2.1 s hs x.2.2
  have hseed : seed = initial :=
    Option.some.inj (hseedSpec.1.symm.trans hlaunch)
  have hinitialSeed : seed.coordinator = .first := by rw [hseed]; exact hinitial
  have hmode : ReferenceActivePhysicalHorizon.allActiveAtStart seed s := hseedSpec.2.1
  have hselected : ActualInitializationPhysicalStep.selectedRowIndex p
      (ReferenceGeneratedActivePrefixFactor.splitSource q t control0 x.1) = q := by
    rw [← ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex]
    exact ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_symm_coordinatorIndex
      p q t control0 x.1 x.2.1
  have hcount : s + count ≤ t.val := by omega
  have hspan : s + count ≤ p.T := by omega
  have hsameRun :
      ReferenceActivePhysicalHorizon.run seed source.1.2 q rewards s count
        (by omega) hmode =
      ReferenceActivePhysicalHorizon.run seed source.1.2 q rewards s count hspan hmode := by
    congr 1
  have hrunEq :
      retainedGeneratedPrefix rate rewards C_star C_h q t s hs control0 x control0 count
        hcount =
      ReferenceActivePhysicalHorizon.run seed source.1.2 q rewards s count hspan hmode := by
    calc
      retainedGeneratedPrefix rate rewards C_star C_h q t s hs control0 x control0 count
          hcount = ReferenceGeneratedActivePrefixFactor.generatedActivePrefixFactor
            rate rewards C_star C_h q t control0 x.1 x.2.1 s count hs x.2.2 hcount := rfl
      _ = ReferenceActivePhysicalHorizon.run seed source.1.2 q rewards s count hspan hmode := by
        unfold ReferenceGeneratedActivePrefixFactor.generatedActivePrefixFactor
        dsimp only [source]
        rw [hselected]
  have hboundaryState : boundary.state =
      (retainedGeneratedPrefix rate rewards C_star C_h q t s hs control0 x control0 count
        (by omega)).finalState := by
    change (ReferenceRetainedBoundaryMeasurability.retainedIncomingBoundary
        rate rewards C_star C_h q t s hs control0 x).state =
      (ReferenceGeneratedActivePrefixFactor.generatedActivePrefixFactor
        rate rewards C_star C_h q t control0 x.1 x.2.1 s count hs x.2.2 (by omega)).finalState
    exact ReferenceRetainedBoundaryMeasurability.retainedIncomingBoundary_state
      rate rewards C_star C_h q t s hs control0 x
  have hstoredRun :
      ReferenceAssignmentPayloadPersistence.storedPayload
        (ReferenceActivePhysicalHorizon.run seed source.1.2 q rewards s count
          hspan hmode).finalState.coordinator = some M := by
    rw [← hrunEq, ← hboundaryState]
    exact hstoredBoundary
  obtain ⟨record, hmem, hbirth, htime, hlower, hupper⟩ :=
    ReferenceAssignmentPayloadChronology.run_prefix_storedPayload_has_birth
      seed source.1.2 q rewards s count hspan hmode hinitialSeed count le_rfl M hstoredRun
  rw [hsameRun] at hmem
  have htimeB : record.input.time.val = b := htime.trans hB.symm
  have hlowerB : s ≤ b := by omega
  have hupperB : b < t.val := by omega
  obtain ⟨index, hindex, hget⟩ := List.mem_iff_getElem.mp hmem
  have htimeValues := ReferenceActivePhysicalHorizon.run_time_values
    seed source.1.2 q rewards s count hspan hmode
  have hrunCount := ReferenceActivePhysicalHorizon.run_record_count
    seed source.1.2 q rewards s count hspan hmode
  have hindexCount : index < count := by rw [hrunCount] at hindex; exact hindex
  have htimeIndex :
      ((ReferenceActivePhysicalHorizon.run seed source.1.2 q rewards s count
        hspan hmode).records[index]).input.time.val = s + index := by
    have hgetTimes := congrArg (fun times : List ℕ => times[index]?) htimeValues
    have hindexRecord :
        (ReferenceActivePhysicalHorizon.run seed source.1.2 q rewards s count
          hspan hmode).records[index]? = some record := by
      rw [List.getElem?_eq_getElem hindex, hget]
    have hrecordTime :
        ((ReferenceActivePhysicalHorizon.run seed source.1.2 q rewards s count
          hspan hmode).records.map (fun r => r.input.time.val))[index]? =
          some ((ReferenceActivePhysicalHorizon.run seed source.1.2 q rewards s count
            hspan hmode).records[index].input.time.val) := by
      rw [List.getElem?_map, hindexRecord]
      rw [Option.map_some, hget]
    have hcalendar :
        (ReferenceActivePhysicalHorizon.calendar s count)[index]? = some (s + index) := by
      have hindexCalendar : index <
          (ReferenceActivePhysicalHorizon.calendar s count).length := by
        simpa only [ReferenceActivePhysicalHorizon.calendar, List.length_range'] using hindexCount
      rw [List.getElem?_eq_getElem hindexCalendar]
      congr 1
      change (List.range' s count)[index] = s + index
      exact List.getElem_range'_1 index hindexCalendar
    rw [hrecordTime, hcalendar] at hgetTimes
    exact Option.some.inj hgetTimes
  have hindexEq : index = b - s := by
    rw [hget] at htimeIndex
    omega
  have hlookup :
      (ReferenceActivePhysicalHorizon.run seed source.1.2 q rewards s count
        hspan hmode).records[b - s]? = some record := by
    have hcount := ReferenceActivePhysicalHorizon.run_record_count
      seed source.1.2 q rewards s count hspan hmode
    rw [List.getElem?_eq_getElem (by rw [hcount]; omega)]
    have hrecordAt :
        (ReferenceActivePhysicalHorizon.run seed source.1.2 q rewards s count
          hspan hmode).records[b - s]'(by rw [hcount]; omega) = record := by
      simpa [hindexEq] using hget
    exact congrArg some hrecordAt
  have hmemActual : record ∈
      (retainedGeneratedPrefix rate rewards C_star C_h q t s hs control0 x control0 count
        hcount).records := by
    rw [hrunEq]
    exact hmem
  have hlookupActual :
      (retainedGeneratedPrefix rate rewards C_star C_h q t s hs control0 x control0 count
        hcount).records[b - s]? = some record := by
    rw [hrunEq]
    exact hlookup
  refine ⟨hB, record, hmemActual, hbirth, htimeB, hlowerB, hupperB, hlookupActual, ?_⟩
  intro other hother hotherBirth
  rw [hrunEq] at hother
  have hsame : record = other :=
    ReferenceAssignmentPayloadChronology.run_records_time_injective
      seed source.1.2 q rewards s count hspan hmode hmem hother
      (htimeB.trans (hB.trans (ReferenceAssignmentPayloadChronology.installationBirth_time_eq
        other M hotherBirth)))
  exact hsame.symm

private theorem measurable_storedPayload
    (rate : RateInput p) :
    Measurable (fun state : ReferenceActivePhysicalStep.State p rate =>
      ReferenceAssignmentPayloadPersistence.storedPayload state.coordinator) := by
  let Code := ReferenceActivePhysicalStepMeasurability.CoordinatorCode p rate
  let storedCode : Code → Option (Payload (p := p) (rate := rate))
    | .inl _ => none
    | .inr (.inl (payload, _)) => some payload
    | .inr (.inr (.inl (payload, _, _))) => some payload
    | .inr (.inr (.inr _)) => none
  have hsome : Measurable (some : Payload (p := p) (rate := rate) →
      Option (Payload (p := p) (rate := rate))) := by
    exact measurable_some_of_measurable id measurable_id
  have hlive : Measurable (fun z : Payload (p := p) (rate := rate) ×
      ReferenceActivePhysicalStepMeasurability.LiveDiscrete p => some z.1) :=
    hsome.comp measurable_fst
  have hcollection : Measurable (fun z : Payload (p := p) (rate := rate) ×
      (ReferenceActivePhysicalStep.Ledger rate × Option (Fin p.T × Bool)) => some z.1) :=
    hsome.comp measurable_fst
  have htail : Measurable (fun z :
      (Payload (p := p) (rate := rate) ×
        (ReferenceActivePhysicalStep.Ledger rate × Option (Fin p.T × Bool))) ⊕ Unit =>
      Sum.elim (fun q => some q.1) (fun _ : Unit => none) z) := by
    exact hcollection.sumElim measurable_const
  have hmid : Measurable (fun z :
      (Payload (p := p) (rate := rate) ×
        ReferenceActivePhysicalStepMeasurability.LiveDiscrete p) ⊕
        ((Payload (p := p) (rate := rate) ×
          (ReferenceActivePhysicalStep.Ledger rate × Option (Fin p.T × Bool))) ⊕ Unit) =>
      Sum.elim (fun q => some q.1)
        (fun q => Sum.elim (fun r => some r.1) (fun _ : Unit => none) q) z) := by
    exact hlive.sumElim htail
  have hcode : Measurable (fun z : Code =>
      Sum.elim (fun _ : Unit => (none : Option (Payload (p := p) (rate := rate))) )
        (fun q => Sum.elim (fun r => some r.1)
          (fun r => Sum.elim (fun v => some v.1) (fun _ : Unit => none) r) q) z) := by
    exact measurable_const.sumElim hmid
  have heq : storedCode = fun z =>
      Sum.elim (fun _ : Unit => (none : Option (Payload (p := p) (rate := rate))))
        (fun q => Sum.elim (fun r => some r.1)
          (fun r => Sum.elim (fun v => some v.1) (fun _ : Unit => none) r) q) z := by
    funext z
    cases z with
    | inl u => cases u; rfl
    | inr z => cases z with
      | inl x => rfl
      | inr z => cases z with
        | inl x => rfl
        | inr u => cases u; rfl
  have hcode' : Measurable storedCode := heq ▸ hcode
  have hencode : Measurable (fun state : ReferenceActivePhysicalStep.State p rate =>
      ReferenceActivePhysicalStepMeasurability.encodeCoordinator state.coordinator) :=
    ReferenceActivePhysicalStepMeasurability.measurable_coordinatorCode
  have hstored : Measurable (fun state : ReferenceActivePhysicalStep.State p rate =>
      storedCode (ReferenceActivePhysicalStepMeasurability.encodeCoordinator state.coordinator)) :=
    hcode'.comp hencode
  have hidentity : (fun state : ReferenceActivePhysicalStep.State p rate =>
      storedCode (ReferenceActivePhysicalStepMeasurability.encodeCoordinator state.coordinator)) =
      fun state => ReferenceAssignmentPayloadPersistence.storedPayload state.coordinator := by
    funext state
    cases state.coordinator <;> rfl
  rw [← hidentity]
  exact hstored

/-- Borel measurability of the retained selector on the original inherited
launch-start space. The whole real payload remains in its existing Borel
carrier. -/
theorem measurable_retainedAssignmentSelection
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p) :
    Measurable (retainedAssignmentSelection rate rewards C_star C_h q t s hs control0) := by
  let x : RetainedLaunchStartInput (p := p) rate rewards C_star C_h q t s hs control0 →
      ReferenceActivePhysicalStep.State p rate := fun x =>
    (ReferenceRetainedBoundaryMeasurability.retainedIncomingBoundary
      rate rewards C_star C_h q t s hs control0 x).state
  have hx : Measurable x :=
    ReferenceActivePhysicalStepMeasurability.measurable_state.comp
      (ReferenceRetainedBoundaryMeasurability.measurable_retainedIncomingBoundary
        rate rewards C_star C_h q t s hs control0)
  have hstored : Measurable (fun z : RetainedLaunchStartInput
      (p := p) rate rewards C_star C_h q t s hs control0 =>
        ReferenceAssignmentPayloadPersistence.storedPayload (x z).coordinator) :=
    (measurable_storedPayload rate).comp hx
  have hobs : Measurable (LaterAssignmentStartMeasurability.payloadObservation
      (p := p) (eta := rate.eta)) := comap_measurable _
  have hsigma : Measurable (fun M : Payload (p := p) (rate := rate) =>
      (LaterAssignmentStartMeasurability.payloadObservation M).2.1) :=
    measurable_fst.comp (measurable_snd.comp hobs)
  have hval : Measurable (fun M : Payload (p := p) (rate := rate) =>
      (LaterAssignmentStartMeasurability.payloadObservation M).2.1.val) :=
    (measurable_of_finite _).comp hsigma
  have hpair : Measurable (fun M : Payload (p := p) (rate := rate) =>
      (M.sigma.val, M)) := by
    have heq : (fun M : Payload (p := p) (rate := rate) =>
        (M.sigma.val, M)) = fun M =>
          ((LaterAssignmentStartMeasurability.payloadObservation M).2.1.val, M) := rfl
    rw [heq]
    exact hval.prodMk measurable_id
  exact LaterAssignmentFullOutputMeasurability.measurable_optionMap
    (fun M : Payload (p := p) (rate := rate) => (M.sigma.val, M)) hpair
    (fun z : RetainedLaunchStartInput (p := p) rate rewards C_star C_h q t s hs control0 =>
      ReferenceAssignmentPayloadPersistence.storedPayload (x z).coordinator)
    hstored

/-- A Borel version of the whole history-valued projection. Every coordinate
uses the actual generated prefix and the joint `(payload,time,state)` Borel
result for `pendingAtStart`; the finite function space is the ordinary finite
pi carrier. -/
theorem measurable_retainedPendingHistory
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p) :
    Measurable (retainedPendingHistory rate rewards C_star C_h q t s hs control0) := by
  let X := RetainedLaunchStartInput (p := p) rate rewards C_star C_h q t s hs control0
  let count := t.val - s
  let source : X → SourceInput p := fun x =>
    ReferenceGeneratedActivePrefixFactor.splitSource q t control0 x.1
  let seed : X → ReferenceActivePhysicalStep.State p rate := fun x =>
    ReferenceRetainedBoundaryMeasurability.retainedGeneratedActiveSeed
      rate rewards C_star C_h q t s hs control0 x
  have hsource : Measurable source := by
    change Measurable (fun x : X =>
      (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t).symm
        (control0, x.1))
    exact (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t).symm.measurable.comp
      (measurable_const.prodMk measurable_subtype_coe)
  have hseed : Measurable seed :=
    ReferenceRetainedBoundaryMeasurability.measurable_retainedGeneratedActiveSeed
      rate rewards C_star C_h q t s hs control0
  have hrows : Measurable (fun x : X => (source x).1.2) :=
    measurable_snd.comp (measurable_fst.comp hsource)
  have hselected : Measurable (fun _ : X => q) := measurable_const
  have hmode : ∀ x : X,
      ReferenceActivePhysicalHorizon.allActiveAtStart (seed x) s := by
    intro x
    exact (ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec
      rate rewards C_star C_h q t control0 x.1 x.2.1 s hs x.2.2).2.1
  have hfinal (k : ℕ) (hk : s + k ≤ t.val) :
      Measurable (fun x : X =>
        (retainedGeneratedPrefix rate rewards C_star C_h q t s hs control0 x control0
          k hk).finalState) := by
    have hdata : Measurable (fun x : X => (seed x, ((source x).1.2, (q, rewards)))) :=
      hseed.prodMk (hrows.prodMk (hselected.prodMk measurable_const))
    let runInput : X →
        ReferenceActiveHorizonMeasurability.ActiveRunInput (p := p) (rate := rate) s :=
      fun x => ⟨(seed x, ((source x).1.2, (q, rewards))), hmode x⟩
    have hrinput : Measurable runInput := hdata.subtype_mk
    have hspan : s + k ≤ p.T := by omega
    have hrun := (ReferenceActiveHorizonMeasurability.measurable_runFinalState
      (p := p) (rate := rate) s k hspan).comp hrinput
    have heq : (fun x : X =>
        (ReferenceActiveHorizonMeasurability.runOfInput (p := p) (rate := rate)
          s k hspan (runInput x)).finalState) = fun x =>
        (retainedGeneratedPrefix rate rewards C_star C_h q t s hs control0 x control0
          k hk).finalState := by
      funext x
      have hselectedAt : ActualInitializationPhysicalStep.selectedRowIndex p
          (ReferenceGeneratedActivePrefixFactor.splitSource q t control0 x.1) = q := by
        calc
          ActualInitializationPhysicalStep.selectedRowIndex p
              (ReferenceGeneratedActivePrefixFactor.splitSource q t control0 x.1) =
              ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p
                (ReferenceGeneratedActivePrefixFactor.splitSource q t control0 x.1) :=
            (ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex
              p (ReferenceGeneratedActivePrefixFactor.splitSource q t control0 x.1)).symm
          _ = q := ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_symm_coordinatorIndex
            p q t control0 x.1 x.2.1
      unfold retainedGeneratedPrefix
      dsimp only [ReferenceActiveHorizonMeasurability.runOfInput, runInput, seed, source]
      dsimp only [ReferenceGeneratedActivePrefixFactor.generatedActivePrefixFactor]
      rw [hselectedAt]
      rfl
    rw [← heq]
    exact hrun
  have hhistory : Measurable (fun z :
      (ℕ × Payload (p := p) (rate := rate)) × X =>
        fun j : Fin (t.val - s + 1) =>
          ReferencePhysicalReleaseQuota.pendingAtStart z.1.2 (retainedHistoryTime s t hs j)
            (retainedGeneratedPrefix rate rewards C_star C_h q t s hs control0 z.2
              control0 j.val (by have hj := j.isLt; omega)).finalState) := by
    rw [measurable_pi_iff]
    intro j
    have hstate : Measurable (fun z :
        (ℕ × Payload (p := p) (rate := rate)) × X =>
          (retainedGeneratedPrefix rate rewards C_star C_h q t s hs control0 z.2
            control0 j.val (by have hj := j.isLt; omega)).finalState) :=
      (hfinal j.val (by have hj := j.isLt; omega)).comp measurable_snd
    have hinput : Measurable (fun z :
        (ℕ × Payload (p := p) (rate := rate)) × X =>
          (z.1.2, (retainedHistoryTime s t hs j,
            (retainedGeneratedPrefix rate rewards C_star C_h q t s hs control0 z.2
              control0 j.val (by have hj := j.isLt; omega)).finalState))) := by
      exact (measurable_snd.comp measurable_fst).prodMk
        (measurable_const.prodMk hstate)
    exact (ReferencePhysicalReleaseObservability.measurable_pendingAtStart).comp hinput
  have hbody : Measurable (fun z :
      ((ℕ × Payload (p := p) (rate := rate)) × X) =>
        (z.1, fun j : Fin (t.val - s + 1) =>
          ReferencePhysicalReleaseQuota.pendingAtStart z.1.2 (retainedHistoryTime s t hs j)
            (retainedGeneratedPrefix rate rewards C_star C_h q t s hs control0 z.2
              control0 j.val (by have hj := j.isLt; omega)).finalState)) :=
    measurable_fst.prodMk hhistory
  exact ReferenceCollectionInstallOutputMeasurability.measurable_optionMapDependent
    (fun z : (ℕ × Payload (p := p) (rate := rate)) × X =>
      (z.1, fun j : Fin (t.val - s + 1) =>
        ReferencePhysicalReleaseQuota.pendingAtStart z.1.2 (retainedHistoryTime s t hs j)
          (retainedGeneratedPrefix rate rewards C_star C_h q t s hs control0 z.2
            control0 j.val (by have hj := j.isLt; omega)).finalState)) hbody
    (retainedAssignmentSelection rate rewards C_star C_h q t s hs control0)
    (measurable_retainedAssignmentSelection rate rewards C_star C_h q t s hs control0)

/-- Joint measurability of the actual next-input producer on the retained
launch space and the full current control, via the original fixed-control
source coordinates and the lossless active-round code. -/
theorem measurable_retainedGeneratedNextInput
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p) :
    Measurable (fun z :
      RetainedLaunchStartInput (p := p) rate rewards C_star C_h q t s hs control0 × TimeControl p =>
        ReferenceRetainedBoundaryMeasurability.retainedGeneratedNextInput
          rate rewards C_star C_h q t s hs control0 z.1 z.2) := by
  let X := RetainedLaunchStartInput (p := p) rate rewards C_star C_h q t s hs control0
  let source : X × TimeControl p → SourceInput p := fun z =>
    ReferenceGeneratedActivePrefixFactor.splitSource q t z.2 z.1.1
  let boundary : X → ReferenceActivePhysicalStep.RoundInput p rate :=
    ReferenceRetainedBoundaryMeasurability.retainedIncomingBoundary
      rate rewards C_star C_h q t s hs control0
  have hsource : Measurable source := by
    change Measurable (fun z : X × TimeControl p =>
      (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t).symm
        (z.2, z.1.1))
    exact (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t).symm.measurable.comp
      (measurable_snd.prodMk (measurable_subtype_coe.comp (measurable_fst.comp measurable_id)))
  have hboundary : Measurable boundary :=
    ReferenceRetainedBoundaryMeasurability.measurable_retainedIncomingBoundary
      rate rewards C_star C_h q t s hs control0
  have hstate : Measurable (fun z : X × TimeControl p => (boundary z.1).state) :=
    ReferenceActivePhysicalStepMeasurability.measurable_state.comp
      (hboundary.comp measurable_fst)
  have hrows : Measurable (fun z : X × TimeControl p => (source z).1.2) :=
    measurable_snd.comp (measurable_fst.comp hsource)
  have hselected : Measurable (fun _ : X × TimeControl p => q) := measurable_const
  have hcoords : Measurable (fun z : X × TimeControl p =>
      ((boundary z.1).state, ((source z).1.2, (q, (t, rewards))))) :=
    hstate.prodMk (hrows.prodMk (hselected.prodMk
      ((measurable_const : Measurable (fun _ : X × TimeControl p => t)).prodMk
        measurable_const)))
  let input := fun z : X × TimeControl p =>
    ReferenceFixedTimeSourceControlCoupling.roundInputAtSource p rate (boundary z.1) (source z)
  have hselectedEq : ∀ z, ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p
      (source z) = q := by
    intro z
    have hparts : z.1.1 ∈
        ReferenceFixedTimeSourceControlCoupling.fixedControlRemainderStratum p q t ∩
          ReferenceInitializationControlRemainder.launchStartRemainderEvent
            rate rewards C_star C_h q t s control0 := by
      change z.1.1 ∈ ReferenceRetainedBoundaryMeasurability.retainedLaunchStartSet
        rate rewards C_star C_h q t s control0
      change z.1.1 ∈ ReferenceFixedTimeSourceControlCoupling.fixedControlRemainderStratum p q t ∩
        ReferenceInitializationControlRemainder.launchStartRemainderEvent
          rate rewards C_star C_h q t s control0
      exact z.1.2
    exact ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_symm_coordinatorIndex
      p q t z.2 z.1.1 hparts.1
  have hencoded : Measurable (fun z =>
      ReferenceActivePhysicalStepMeasurability.encodeRoundInput (input z)) := by
    let codeValue : X × TimeControl p →
        ReferenceActivePhysicalStepMeasurability.RoundCoordinates p rate :=
      fun z => ((boundary z.1).state, ((source z).1.2, (q, (t, rewards))))
    have hcodeValue : Measurable codeValue := hcoords
    let activeCode : X × TimeControl p →
        ReferenceActivePhysicalStepMeasurability.ActiveRoundCoordinates p rate :=
      fun z => ⟨codeValue z, (input z).active⟩
    have hactiveCode : Measurable activeCode :=
      hcodeValue.subtype_mk (h := fun z => (input z).active)
    have heq : (fun z : X × TimeControl p =>
        ReferenceActivePhysicalStepMeasurability.encodeRoundInput (input z)) = activeCode := by
      funext z
      apply Subtype.ext
      change ((boundary z.1).state, ((source z).1.2,
        (ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p (source z),
          (t, rewards)))) =
        ((boundary z.1).state, ((source z).1.2, (q, (t, rewards))))
      rw [hselectedEq z]
    rw [heq]
    exact hactiveCode
  have hin : Measurable input := measurable_comap_iff.mpr hencoded
  have heq : (fun z : X × TimeControl p =>
      ReferenceRetainedBoundaryMeasurability.retainedGeneratedNextInput
        rate rewards C_star C_h q t s hs control0 z.1 z.2) = input := by
    funext z
    rw [ReferenceRetainedBoundaryMeasurability.retainedGeneratedNextInput_eq_roundInputAtSource
      rate rewards C_star C_h q t s hs control0 z.1 z.2]
  rw [heq]
  exact hin

/-- Joint Borel measurability of each current release flag pair, retaining the
actual option-valued assignment branch and the full current input. -/
theorem measurable_retainedReleaseFlags
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p) (i : Fin (p.m - 1)) :
    Measurable (fun z :
      RetainedLaunchStartInput (p := p) rate rewards C_star C_h q t s hs control0 × TimeControl p =>
        retainedReleaseFlags rate rewards C_star C_h q t s hs control0 z.1 z.2 i) := by
  let X := RetainedLaunchStartInput (p := p) rate rewards C_star C_h q t s hs control0
  let f : (ℕ × Payload (p := p) (rate := rate)) × (X × TimeControl p) → Bool × Bool :=
    fun z =>
      (ReferencePhysicalReleaseQuota.upFlag z.1.2
        (ReferencePhysicalReleaseObservability.recordOfInput
          (ReferenceRetainedBoundaryMeasurability.retainedGeneratedNextInput
            rate rewards C_star C_h q t s hs control0 z.2.1 z.2.2)) i,
       ReferencePhysicalReleaseQuota.dataFlag z.1.2
        (ReferencePhysicalReleaseObservability.recordOfInput
          (ReferenceRetainedBoundaryMeasurability.retainedGeneratedNextInput
            rate rewards C_star C_h q t s hs control0 z.2.1 z.2.2)) i)
  have hinput : Measurable (fun z :
      (ℕ × Payload (p := p) (rate := rate)) × (X × TimeControl p) =>
        (z.1.2,
          ReferenceRetainedBoundaryMeasurability.retainedGeneratedNextInput
            rate rewards C_star C_h q t s hs control0 z.2.1 z.2.2)) := by
    exact (measurable_snd.comp measurable_fst).prodMk
      ((measurable_retainedGeneratedNextInput
        rate rewards C_star C_h q t s hs control0).comp
          (measurable_snd.comp measurable_id))
  have hflags : Measurable f := by
    have hup := (ReferencePhysicalReleaseObservability.measurable_upFlag i).comp hinput
    have hdata := (ReferencePhysicalReleaseObservability.measurable_dataFlag i).comp hinput
    exact hup.prodMk hdata
  exact ReferenceCollectionInstallOutputMeasurability.measurable_optionMapDependent
    (fun z : (ℕ × Payload (p := p) (rate := rate)) × (X × TimeControl p) =>
      f z) hflags
    (fun z : X × TimeControl p =>
      retainedAssignmentSelection rate rewards C_star C_h q t s hs control0 z.1)
    ((measurable_retainedAssignmentSelection rate rewards C_star C_h q t s hs control0).comp
      measurable_fst)

private theorem selectionAt_payload_eq
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (payload : Payload (p := p) (rate := rate))
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (time : Fin p.T)
    (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ)
    (choice : CoordinatorRoundDispatch.ArmSelection payload started time weights x.row)
    (selected : ReferenceActivePhysicalStep.Selection x)
    (hselection : ReferenceActivePhysicalStep.selectionAt x payload started time weights choice =
      some selected) :
    selected.view.payload = payload := by
  by_cases htime : time = x.time
  · simp only [ReferenceActivePhysicalStep.selectionAt, dif_pos htime] at hselection
    exact (congrArg (fun value : ReferenceActivePhysicalStep.Selection x => value.view.payload)
      (Option.some.inj hselection)).symm
  · simp only [ReferenceActivePhysicalStep.selectionAt, dif_neg htime] at hselection
    cases hselection

private theorem inputCoordinator_eq_first_of_dispatch_eq_first
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (outcome : CoordinatorRoundDispatch.FirstOutcome (ReferenceActivePhysicalStep.firstInput x))
    (hdispatch : ReferenceActivePhysicalStep.dispatch x = .first outcome) :
    x.state.coordinator = .first := by
  cases hstate : x.state.coordinator with
  | first => rfl
  | live registers owned base =>
      cases hresult : CoordinatorRoundDispatch.dispatch
          (.live (ReferenceActivePhysicalStep.liveInput x registers owned base)) with
      | live actualOutcome =>
          have hcut : ReferenceActivePhysicalStep.dispatch x =
              .live registers owned base actualOutcome := by
            unfold ReferenceActivePhysicalStep.dispatch
            simp only [hstate]
            rw [hresult]
            rfl
          rw [hcut] at hdispatch
          cases hdispatch
  | collection payload ledger savedProposal =>
      by_cases hcutoff : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
      · let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
        let clock := ReferenceActivePhysicalStep.collectionClock payload ledger savedProposal cutoff
        cases hresult : CoordinatorRoundDispatch.dispatch
            (.collection (ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff)) with
        | collection actualOutcome =>
            have hcut : ReferenceActivePhysicalStep.dispatch x =
                .collection payload ledger clock cutoff actualOutcome := by
              unfold ReferenceActivePhysicalStep.dispatch
              simp only [hstate, dif_pos hcutoff]
              rw [hresult]
              rfl
            rw [hcut] at hdispatch
            cases hdispatch
      · have hcut : ReferenceActivePhysicalStep.dispatch x = .invalidCollectionCutoff := by
          unfold ReferenceActivePhysicalStep.dispatch
          simp only [hstate, dif_neg hcutoff]
        rw [hcut] at hdispatch
        cases hdispatch
  | dagger =>
      have hcut : ReferenceActivePhysicalStep.dispatch x = .dagger := by
        simp [ReferenceActivePhysicalStep.dispatch, hstate]
      rw [hcut] at hdispatch
      cases hdispatch

private theorem roundRecordCode_front_of_preparationSelection
    (record : Record (p := p) (rate := rate))
    (selected : ReferenceActivePhysicalStep.Selection record.input)
    (hselected : record.output.preparation.coordinator.selection = some selected) :
    (ReferenceActiveHorizonMeasurability.roundRecordCode record).2.2.1.1 =
      some (ReferenceLiveDispatchOutputMeasurability.encodeSelection selected) := by
  have hactual : record.output.preparation.coordinator =
      ReferenceActivePhysicalStep.dispatch record.input := by
    rw [record.output_eq]
    exact (ReferenceActivePhysicalStep.prepare record.input).coordinator_eq
  have hselectionEq := congrArg
    (fun coordinator => coordinator.selection) hactual
  have hdispatchSelection :
      (ReferenceActivePhysicalStep.dispatch record.input).selection = some selected :=
    hselectionEq.symm.trans hselected
  have hfront := (ReferenceActiveHorizonMeasurability.roundRecordCode_front record).1
  rw [hdispatchSelection, Option.map_some] at hfront
  exact hfront

/-- The record selected from the current retained payload has an actual
preparation selection carrying that whole payload. The front code coordinate
is the same selection from `roundRecordCode_front`; first and later births
are recovered from their checked dispatcher branches. -/
theorem retainedAssignmentSelection_birth_has_actual_preparationView
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p)
    (x : RetainedLaunchStartInput (p := p) rate rewards C_star C_h q t s hs control0)
    (b : ℕ) (M : Payload (p := p) (rate := rate))
    (hsel : retainedAssignmentSelection rate rewards C_star C_h q t s hs control0 x = some (b, M)) :
    ∃ record : Record (p := p) (rate := rate),
      record ∈ (retainedGeneratedPrefix rate rewards C_star C_h q t s hs control0 x control0
        (t.val - s) (by omega)).records ∧
      ReferenceAssignmentPayloadPersistence.InstallationBirth record M ∧
      ∃ selected : ReferenceActivePhysicalStep.Selection record.input,
        record.output.preparation.coordinator.selection = some selected ∧
        selected.view.payload = M ∧
        (ReferenceActiveHorizonMeasurability.roundRecordCode record).2.2.1.1 =
          some (ReferenceLiveDispatchOutputMeasurability.encodeSelection selected) := by
  obtain ⟨_, record, hmem, hbirth, _, _, _, _, _⟩ :=
    retainedAssignmentSelection_has_unique_actual_installation
      rate rewards C_star C_h q t s hs control0 x b M hsel
  have hactual : record.output.preparation.coordinator =
      ReferenceActivePhysicalStep.dispatch record.input := by
    rw [record.output_eq]
    exact (ReferenceActivePhysicalStep.prepare record.input).coordinator_eq
  refine ⟨record, hmem, hbirth, ?_⟩
  cases hcoord : record.output.preparation.coordinator with
  | first outcome =>
      cases outcome with
      | choiceDomainFailure installed => simp [ReferenceAssignmentPayloadPersistence.InstallationBirth,
          hcoord] at hbirth
      | recorderBoundaryFailure installed => simp [ReferenceAssignmentPayloadPersistence.InstallationBirth,
          hcoord] at hbirth
      | choiceRejected installed => simp [ReferenceAssignmentPayloadPersistence.InstallationBirth,
          hcoord] at hbirth
      | chosen installed choice =>
          have hdispatch : ReferenceActivePhysicalStep.dispatch record.input =
              .first (.chosen installed choice) := by
            rw [← hactual, hcoord]
          have hfirst := inputCoordinator_eq_first_of_dispatch_eq_first record.input
            (.chosen installed choice) hdispatch
          have hchosen : CoordinatorRoundDispatch.dispatchFirst
              (ReferenceActivePhysicalStep.firstInput record.input) = .chosen installed choice := by
            rw [ReferenceActivePhysicalStep.dispatch_first record.input hfirst] at hdispatch
            injection hdispatch
          have hpayloadEq : M = installed.registers.payload := by
            have hbirth' : M = installed.registers.payload ∧
                M.sigma.val = record.input.time.val := by
              simpa [ReferenceAssignmentPayloadPersistence.InstallationBirth, hcoord] using hbirth
            exact hbirth'.1
          have htime := ReferenceActivePhysicalStep.dispatchFirst_chosen_time
            record.input installed choice hchosen
          have hsome : (ReferenceActivePhysicalStep.selectionAt record.input
              installed.registers.payload installed.startRoundResult installed.registers.time
              installed.registers.complementWeights choice).isSome := by
            simp [ReferenceActivePhysicalStep.selectionAt, htime]
          obtain ⟨selected, hselectionAt⟩ := Option.isSome_iff_exists.mp hsome
          have hselectedCut :
              (ReferenceActivePhysicalStep.DispatchCut.first (.chosen installed choice)).selection =
                some selected := by
            simpa only [ReferenceActivePhysicalStep.DispatchCut.selection] using hselectionAt
          have hselected : record.output.preparation.coordinator.selection = some selected := by
            rw [hcoord]
            exact hselectedCut
          have hview := selectionAt_payload_eq record.input installed.registers.payload
            installed.startRoundResult installed.registers.time installed.registers.complementWeights
            choice selected hselectionAt
          have hviewM : selected.view.payload = M := hview.trans hpayloadEq.symm
          exact ⟨selected, hselectedCut, hviewM,
            roundRecordCode_front_of_preparationSelection record selected hselected⟩
  | live registers owned base outcome =>
      simp [ReferenceAssignmentPayloadPersistence.InstallationBirth, hcoord] at hbirth
  | collection payload ledger clock cutoff outcome =>
      cases outcome with
      | laterChosen core consistent started hstart instruction hinstruction output
          outputConsistency clockData installed choice =>
          have hdispatch : ReferenceActivePhysicalStep.dispatch record.input =
              .collection payload ledger clock cutoff
                (.laterChosen core consistent started hstart instruction hinstruction output
                  outputConsistency clockData installed choice) := by
            rw [← hactual, hcoord]
          have hprovenance := ReferenceLaterInstallationProvenance.dispatch_laterChosen_provenance
            record.input
          rw [hdispatch] at hprovenance
          have hrecordBirth : ReferenceAssignmentPayloadPersistence.InstallationBirth record
              installed.registers.payload := by
            simpa [hcoord] using ReferenceLaterInstallationProvenance.record_laterChosen_birth record
          have hpayloadEq := ReferenceAssignmentPayloadChronology.installationBirth_payload_unique
            record M installed.registers.payload hbirth hrecordBirth
          have hpayloadOutput : M = output.payload := hpayloadEq.trans hprovenance.2.1
          have htime := ReferenceActivePhysicalStep.later_instruction_time record.input payload
            ledger clock cutoff core started instruction hstart hinstruction
          have hsome : (ReferenceActivePhysicalStep.selectionAt record.input
              installed.registers.payload started instruction.time
              installed.registers.complementWeights choice).isSome := by
            simp [ReferenceActivePhysicalStep.selectionAt, htime]
          obtain ⟨selected, hselectionAt⟩ := Option.isSome_iff_exists.mp hsome
          have hselectedCut :
              (ReferenceActivePhysicalStep.DispatchCut.collection payload ledger clock cutoff
                (.laterChosen core consistent started hstart instruction hinstruction output
                  outputConsistency clockData installed choice)).selection = some selected := by
            simpa only [ReferenceActivePhysicalStep.DispatchCut.selection] using hselectionAt
          have hselected : record.output.preparation.coordinator.selection = some selected := by
            rw [hcoord]
            exact hselectedCut
          have hview := selectionAt_payload_eq record.input installed.registers.payload
            started instruction.time installed.registers.complementWeights choice selected hselectionAt
          have hviewM : selected.view.payload = M :=
            (hview.trans hprovenance.2.1).trans hpayloadOutput.symm
          exact ⟨selected, hselectedCut, hviewM,
            roundRecordCode_front_of_preparationSelection record selected hselected⟩
      | clockFailure failure startRound_eq =>
          simp [ReferenceAssignmentPayloadPersistence.InstallationBirth, hcoord] at hbirth
      | localFailure started startRound_eq core_invalid reason =>
          simp [ReferenceAssignmentPayloadPersistence.InstallationBirth, hcoord] at hbirth
      | coreFailure core started startRound_eq reason =>
          simp [ReferenceAssignmentPayloadPersistence.InstallationBirth, hcoord] at hbirth
      | continuing core prepared boundary checked =>
          simp [ReferenceAssignmentPayloadPersistence.InstallationBirth, hcoord] at hbirth
      | laterReconstructionFailure core consistent started startRound_eq instruction
          assignmentStart_eq reason later_eq =>
          simp [ReferenceAssignmentPayloadPersistence.InstallationBirth, hcoord] at hbirth
      | laterPrefixFailure core consistent started startRound_eq instruction
          assignmentStart_eq arm reason later_eq =>
          simp [ReferenceAssignmentPayloadPersistence.InstallationBirth, hcoord] at hbirth
      | laterOrientationFailure core consistent started startRound_eq instruction
          assignmentStart_eq set later_eq =>
          simp [ReferenceAssignmentPayloadPersistence.InstallationBirth, hcoord] at hbirth
      | laterChoiceFailure core consistent started startRound_eq instruction
          assignmentStart_eq output outputConsistency clockData installed reason =>
          simp [ReferenceAssignmentPayloadPersistence.InstallationBirth, hcoord] at hbirth
  | invalidCollectionCutoff =>
      simp [ReferenceAssignmentPayloadPersistence.InstallationBirth, hcoord] at hbirth
  | dagger => simp [ReferenceAssignmentPayloadPersistence.InstallationBirth, hcoord] at hbirth

/-- At a zero-length prefix the corrected launch seed is still `.first`, so
the producer exposes `none` for the current selector, retrospective history,
and every current flag. The current coordinate remains the supplied `t : Fin T`;
there is no action at a natural time equal to `T`. -/
theorem retainedAssignmentSelection_zeroPrefix_none
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p)
    (x : RetainedLaunchStartInput (p := p) rate rewards C_star C_h q t s hs control0)
    (hzero : s = t.val) :
    retainedAssignmentSelection rate rewards C_star C_h q t s hs control0 x = none ∧
      retainedPendingHistory rate rewards C_star C_h q t s hs control0 x = none ∧
      ∀ control i, retainedReleaseFlags rate rewards C_star C_h q t s hs control0 x control i = none := by
  subst s
  let s : ℕ := t.val
  let source := ReferenceGeneratedActivePrefixFactor.splitSource q t control0 x.1
  let count := t.val - s
  have hcrossElapsed := ReferenceGeneratedActivePrefixFactor.launchStart_source_facts
    rate rewards C_star C_h q t control0 x.1 x.2.1 s hs x.2.2
  obtain ⟨hcross, _helapsed⟩ := hcrossElapsed
  obtain ⟨initial, hlaunch, hinitial, _, _, _⟩ :=
    ReferenceCorrectedInitializationLaunch.correctedLaunch_coordinator_provenance
      rate source rewards C_star C_h hcross
  have hseedSpec := ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec
    rate rewards C_star C_h q t control0 x.1 x.2.1 s hs x.2.2
  let seed := ReferenceGeneratedActivePrefixFactor.generatedActiveSeed
    rate rewards C_star C_h q t control0 x.1 x.2.1 s hs x.2.2
  have hseed : seed = initial := Option.some.inj (hseedSpec.1.symm.trans hlaunch)
  have hmode : ReferenceActivePhysicalHorizon.allActiveAtStart seed s := hseedSpec.2.1
  have hrunZero0 :
      (retainedGeneratedPrefix rate rewards C_star C_h q t s hs control0 x control0
        0 (by omega)).finalState = seed := by
    unfold retainedGeneratedPrefix
    dsimp only
    unfold ReferenceGeneratedActivePrefixFactor.generatedActivePrefixFactor
    rw [ReferenceActivePhysicalHorizon.run_zero_final]
  have hrunZero :
      (retainedGeneratedPrefix rate rewards C_star C_h q t s hs control0 x control0
        count (by omega)).finalState = seed := by
    simpa [count, s] using hrunZero0
  have hboundaryState := ReferenceRetainedBoundaryMeasurability.retainedIncomingBoundary_state
    rate rewards C_star C_h q t s hs control0 x
  have hcoord :
      (ReferenceRetainedBoundaryMeasurability.retainedIncomingBoundary
        rate rewards C_star C_h q t s hs control0 x).state.coordinator = .first := by
    calc
      _ = (retainedGeneratedPrefix rate rewards C_star C_h q t s hs control0 x control0
          count (by omega)).finalState.coordinator :=
        congrArg ReferenceActivePhysicalStep.State.coordinator hboundaryState
      _ = seed.coordinator := congrArg ReferenceActivePhysicalStep.State.coordinator hrunZero
      _ = .first := by rw [hseed]; exact hinitial
  have hnone := (retainedAssignmentSelection_none_iff
    rate rewards C_star C_h q t s hs control0 x).2 (Or.inl hcoord)
  refine ⟨hnone, ?_, ?_⟩
  · unfold retainedPendingHistory
    rw [hnone]
    rfl
  · intro control i
    unfold retainedReleaseFlags
    rw [hnone]
    rfl

/-- Each retained generated successor remains the accepted physical step. The
chronology module supplies both the actual record appended by the finite fold
and its exhaustive drop/retain/fresh-birth interpretation, including failure
and malformed-cutoff branches. -/
theorem retainedGeneratedPrefix_successor_payload_classification
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p)
    (x : RetainedLaunchStartInput (p := p) rate rewards C_star C_h q t s hs control0)
    (control : TimeControl p) (index : ℕ)
    (hnext : s + (index + 1) ≤ t.val) :
    let source := ReferenceGeneratedActivePrefixFactor.splitSource q t control x.1
    let seed := ReferenceGeneratedActivePrefixFactor.generatedActiveSeed rate rewards C_star C_h
      q t control x.1 x.2.1 s hs
      ((ReferenceInitializationControlRemainder.launchStartRemainderEvent_control_independent
        rate rewards C_star C_h q t s x.1 x.2.1 control0 control).mp x.2.2)
    let selected := ActualInitializationPhysicalStep.selectedRowIndex p source
    let hmode := (ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec rate rewards
      C_star C_h q t control x.1 x.2.1 s hs
      ((ReferenceInitializationControlRemainder.launchStartRemainderEvent_control_independent
        rate rewards C_star C_h q t s x.1 x.2.1 control0 control).mp x.2.2)).2.1
    let record := ReferenceAssignmentPayloadChronology.actualRunRecordAt seed source.1.2 selected
      rewards s index (by omega) hmode
    (retainedGeneratedPrefix rate rewards C_star C_h q t s hs control0 x control
        (index + 1) (by omega)).records =
      (retainedGeneratedPrefix rate rewards C_star C_h q t s hs control0 x control
        index (by omega)).records ++ [record] ∧
    (ReferenceAssignmentPayloadPersistence.storedPayload
        (ReferenceActivePhysicalStep.step record.input).next.coordinator = none ∨
      (∃ old : Payload (p := p) (rate := rate),
        ReferenceAssignmentPayloadPersistence.storedPayload record.input.state.coordinator = some old ∧
        ReferenceAssignmentPayloadPersistence.storedPayload
          (ReferenceActivePhysicalStep.step record.input).next.coordinator = some old) ∨
      (∃ fresh : Payload (p := p) (rate := rate),
        ReferenceAssignmentPayloadPersistence.InstallationBirth
          (ReferenceAssignmentPayloadChronology.actualStepRecord record.input) fresh ∧
        ReferenceAssignmentPayloadPersistence.storedPayload
          (ReferenceActivePhysicalStep.step record.input).next.coordinator = some fresh)) := by
  let source := ReferenceGeneratedActivePrefixFactor.splitSource q t control x.1
  let hstart := (ReferenceInitializationControlRemainder.launchStartRemainderEvent_control_independent
    rate rewards C_star C_h q t s x.1 x.2.1 control0 control).mp x.2.2
  let seed := ReferenceGeneratedActivePrefixFactor.generatedActiveSeed
    rate rewards C_star C_h q t control x.1 x.2.1 s hs hstart
  let selected := ActualInitializationPhysicalStep.selectedRowIndex p source
  let hmode := (ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec
    rate rewards C_star C_h q t control x.1 x.2.1 s hs hstart).2.1
  let record := ReferenceAssignmentPayloadChronology.actualRunRecordAt seed source.1.2 selected
    rewards s index (by omega) hmode
  dsimp only
  have hrunEq (count : ℕ) (hcount : s + count ≤ t.val) :
      retainedGeneratedPrefix rate rewards C_star C_h q t s hs control0 x control count hcount =
        ReferenceActivePhysicalHorizon.run seed source.1.2 selected rewards s count
          (by omega) hmode := by
    unfold retainedGeneratedPrefix
    dsimp only [source, seed, hstart, selected, hmode]
    unfold ReferenceGeneratedActivePrefixFactor.generatedActivePrefixFactor
    rfl
  have hspan : s + (index + 1) ≤ p.T := by omega
  have hsucc := ReferenceAssignmentPayloadChronology.run_successor_actualRunRecordAt
    seed source.1.2 selected rewards s index hspan hmode
  have hrecords := hrunEq (index + 1) (by omega)
  have hprior := hrunEq index (by omega)
  constructor
  · rw [hrecords, hprior]
    exact hsucc
  · exact ReferenceAssignmentPayloadChronology.actualStep_payload_classification record.input

/-- Specialize the producer to the exact original source using only the
selected-index, successful-crossing, and elapsed-start equations. The source
round input is reconstructed with all original rows and private coordinates;
the whole `N` input can depend on the current control. -/
theorem retainedAssignmentReleaseHistory_source_specialization
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p)
    (z : SourceInput p)
    (hselected : ActualInitializationPhysicalStep.selectedRowIndex p z = q)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true)
    (helapsed : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed = s) :
    let x := ReferenceRetainedBoundaryMeasurability.retainedLaunchStartInputOfSource
      rate rewards C_star C_h q t s hs control0 z hselected hcross helapsed
    let control := (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t z).1
    retainedAssignmentSelectionAtControl rate rewards C_star C_h q t s hs control0 x control =
      retainedAssignmentSelection rate rewards C_star C_h q t s hs control0 x ∧
    retainedPendingHistoryAtControl rate rewards C_star C_h q t s hs control0 x control =
      retainedPendingHistory rate rewards C_star C_h q t s hs control0 x ∧
    ReferenceRetainedBoundaryMeasurability.retainedGeneratedNextInput
      rate rewards C_star C_h q t s hs control0 x control =
      ReferenceFixedTimeSourceControlCoupling.roundInputAtSource p rate
        (ReferenceRetainedBoundaryMeasurability.retainedIncomingBoundary
          rate rewards C_star C_h q t s hs control0 x) z ∧
    ∀ i : Fin (p.m - 1),
      retainedReleaseFlags rate rewards C_star C_h q t s hs control0 x control i =
        (retainedAssignmentSelection rate rewards C_star C_h q t s hs control0 x).map
          (fun selected =>
            (ReferencePhysicalReleaseQuota.upFlag selected.2
              (ReferencePhysicalReleaseObservability.recordOfInput
                (ReferenceFixedTimeSourceControlCoupling.roundInputAtSource p rate
                  (ReferenceRetainedBoundaryMeasurability.retainedIncomingBoundary
                    rate rewards C_star C_h q t s hs control0 x) z)) i,
             ReferencePhysicalReleaseQuota.dataFlag selected.2
              (ReferencePhysicalReleaseObservability.recordOfInput
                (ReferenceFixedTimeSourceControlCoupling.roundInputAtSource p rate
                  (ReferenceRetainedBoundaryMeasurability.retainedIncomingBoundary
                    rate rewards C_star C_h q t s hs control0 x) z)) i)) := by
  let x := ReferenceRetainedBoundaryMeasurability.retainedLaunchStartInputOfSource
    rate rewards C_star C_h q t s hs control0 z hselected hcross helapsed
  let control := (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t z).1
  have hnext := ReferenceRetainedBoundaryMeasurability.retainedGeneratedNextInput_eq_of_source
    rate rewards C_star C_h q t s hs control0 z hselected hcross helapsed
  refine ⟨retainedAssignmentSelectionAtControl_eq rate rewards C_star C_h q t s hs
      control0 x control,
    retainedPendingHistoryAtControl_eq rate rewards C_star C_h q t s hs control0 x control,
    ?_, ?_⟩
  · exact hnext
  · intro i
    unfold retainedReleaseFlags
    rw [hnext]

end Bandits.Support.ReferenceRetainedAssignmentReleaseHistory
