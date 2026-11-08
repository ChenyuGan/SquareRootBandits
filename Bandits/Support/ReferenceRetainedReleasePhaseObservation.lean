/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceRetainedAssignmentReleaseHistory

/-!
# Local release-phase observations on an actual retained launch run

Sources: `sources/zip4/manuscript/05_binary_transport.tex:74-88,293-348`,
`sources/zip4/manuscript/06_interruptions.tex:435-492`,
`sources/zip4/manuscript/07_public_setup.tex:121-164`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-79`.

This file observes the actual incoming states of the existing retained
generated-prefix fold.  Its state vector is a sufficient local phase
observation; it is not the source's full pre-round history or a filtration.
The computed clock readout keeps non-live branches, errors, cutoff commands,
and assignment-start commands visible.  No stopped source interval or
conditional waiting theorem is established here.
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
open Bandits.Support.ReferenceRetainedBoundaryMeasurability
open Bandits.Support.ReferenceAssignmentPayloadPersistence
open Bandits.Support.ReferenceAssignmentPayloadChronology
open Bandits.Support.ReferencePhysicalReleaseQuota
open Bandits.Support.ReferencePhysicalReleaseObservability
open Bandits.Support.CoordinatorPhaseClock
open Bandits.Support.CoordinatorLiveChoiceRecorderStep
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.ContinuousLearningRows
open scoped Classical

namespace Bandits.Support.ReferenceRetainedReleasePhaseObservation

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev TimeControl := ContinuousLearningRows.TimeControl
abbrev SourceInput := BootstrapPrivateRoundStreams.SourceInput
abbrev Payload (p : Parameters) (rate : RateInput p) :=
  ReferenceActivePhysicalStep.Payload rate

variable {p : Parameters} {rate : RateInput p}

abbrev LaunchStart (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p) :=
  ReferenceRetainedAssignmentReleaseHistory.RetainedLaunchStartInput
    (p := p) rate rewards C_star C_h q t s hs control0

/-- The actual incoming-state code at every retained calendar prefix, including
the prefix immediately before the supplied current round.  Each coordinate is
`encodeState` of H's existing run final state at that prefix length. -/
def generatedPhaseBefore
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p)
    (x : LaunchStart (p := p) rate rewards C_star C_h q t s hs control0)
    (control : TimeControl p) :
    Fin (t.val - s + 1) →
      ReferenceActivePhysicalStepMeasurability.StateCode p rate :=
  fun j => ReferenceActivePhysicalStepMeasurability.encodeState
    ((ReferenceRetainedAssignmentReleaseHistory.retainedGeneratedPrefix
      rate rewards C_star C_h q t s hs control0 x control j.val
      (by have hj := j.isLt; omega)).finalState)

private theorem measurable_retainedPrefixFinalState
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s k : ℕ)
    (hs : s ≤ t.val) (hk : s + k ≤ t.val) (control0 : TimeControl p) :
    Measurable (fun x : LaunchStart (p := p) rate rewards C_star C_h q t s hs control0 =>
      (ReferenceRetainedAssignmentReleaseHistory.retainedGeneratedPrefix
        rate rewards C_star C_h q t s hs control0 x control0 k hk).finalState) := by
  let X := LaunchStart (p := p) rate rewards C_star C_h q t s hs control0
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
  have hselected : ∀ x : X,
      ActualInitializationPhysicalStep.selectedRowIndex p (source x) = q := by
    intro x
    calc
      ActualInitializationPhysicalStep.selectedRowIndex p (source x) =
          ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p (source x) :=
        (ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex
          p (source x)).symm
      _ = q := ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_symm_coordinatorIndex
        p q t control0 x.1 x.2.1
  have hmode (x : X) :
      ReferenceActivePhysicalHorizon.allActiveAtStart (seed x) s :=
    (ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec
      rate rewards C_star C_h q t control0 x.1 x.2.1 s hs x.2.2).2.1
  have hdata : Measurable (fun x : X =>
      (seed x, ((source x).1.2, (q, rewards)))) :=
    hseed.prodMk (hrows.prodMk (measurable_const.prodMk measurable_const))
  let runInput : X →
      ReferenceActiveHorizonMeasurability.ActiveRunInput
        (p := p) (rate := rate) s :=
    fun x => ⟨(seed x, ((source x).1.2, (q, rewards))), hmode x⟩
  have hrinput : Measurable runInput := hdata.subtype_mk
  have hspan : s + k ≤ p.T := by omega
  have hrun := (ReferenceActiveHorizonMeasurability.measurable_runFinalState
    (p := p) (rate := rate) s k hspan).comp hrinput
  have heq : (fun x : X =>
      (ReferenceActiveHorizonMeasurability.runOfInput
        (p := p) (rate := rate) s k hspan (runInput x)).finalState) = fun x =>
      (ReferenceRetainedAssignmentReleaseHistory.retainedGeneratedPrefix
        rate rewards C_star C_h q t s hs control0 x control0 k hk).finalState := by
    funext x
    unfold ReferenceRetainedAssignmentReleaseHistory.retainedGeneratedPrefix
    dsimp only [ReferenceActiveHorizonMeasurability.runOfInput, runInput, seed, source]
    dsimp only [ReferenceGeneratedActivePrefixFactor.generatedActivePrefixFactor]
    rw [hselected x]
    rfl
  rw [← heq]
  exact hrun

/-- The finite actual-state observation is Borel on H's original retained
launch-start subtype with its inherited canonical measurable space. -/
theorem measurable_generatedPhaseBefore
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p) (control : TimeControl p) :
    Measurable (generatedPhaseBefore rate rewards C_star C_h q t s hs control0 · control) := by
  have hbase : Measurable
      (generatedPhaseBefore rate rewards C_star C_h q t s hs control0 · control0) := by
    rw [measurable_pi_iff]
    intro j
    have hstate := measurable_retainedPrefixFinalState rate rewards C_star C_h q t s
      j.val hs (by have hj := j.isLt; omega) control0
    exact ReferenceActivePhysicalStepMeasurability.measurable_encodeState.comp hstate
  have hcontrol :
      (generatedPhaseBefore rate rewards C_star C_h q t s hs control0 · control) =
        (generatedPhaseBefore rate rewards C_star C_h q t s hs control0 · control0) := by
    funext x j
    apply congrArg ReferenceActivePhysicalStepMeasurability.encodeState
    exact (ReferenceRetainedAssignmentReleaseHistory.retainedGeneratedPrefix_seed_control_independent
      rate rewards C_star C_h q t s hs control0 x control control0 j.val
      (by have hj := j.isLt; omega)).2.1
  rw [hcontrol]
  exact hbase

/-- H's joint seed/final-state/record-evidence invariance gives the current
removed-control invariance of every coordinate of the local observation. -/
theorem generatedPhaseBefore_currentControl_invariant
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p)
    (x : LaunchStart (p := p) rate rewards C_star C_h q t s hs control0)
    (control control' : TimeControl p) :
    generatedPhaseBefore rate rewards C_star C_h q t s hs control0 x control =
      generatedPhaseBefore rate rewards C_star C_h q t s hs control0 x control' := by
  funext j
  apply congrArg ReferenceActivePhysicalStepMeasurability.encodeState
  exact (ReferenceRetainedAssignmentReleaseHistory.retainedGeneratedPrefix_seed_control_independent
    rate rewards C_star C_h q t s hs control0 x control control' j.val
    (by have hj := j.isLt; omega)).2.1

/-- The actual readout preserves the entire canonical coordinator code and
adds the computed StartRound result on a live state. Thus first, collection,
and dagger remain distinct, while clock errors, cutoff commands, and
assignment-start commands remain the actual `Except` result. -/
abbrev LocalClockOutput (p : Parameters) :=
  Option (Except CoordinatorPhaseClock.ClockFailure
    (CoordinatorPhaseClock.StartRoundResult p))

abbrev LocalReleaseReadout (p : Parameters) (rate : RateInput p) :=
  ReferenceActivePhysicalStepMeasurability.CoordinatorCode p rate ×
    LocalClockOutput p

local instance : MeasurableSpace CoordinatorPhaseClock.ClockFailure := ⊤
local instance : MeasurableSpace (CoordinatorPhaseClock.StartRoundResult p) := ⊤
local instance : MeasurableSpace (Except CoordinatorPhaseClock.ClockFailure
    (CoordinatorPhaseClock.StartRoundResult p)) := ⊤
local instance : MeasurableSpace (LocalClockOutput p) := ⊤

/-- The actual computed phase-clock call at zero-based physical time `time`.
The live clock registers and pending set are exactly those decoded from the
canonical live-state code. -/
def localReleaseStartResult
    (rate : RateInput p) (time : Fin p.T)
    (live : ReferenceActivePhysicalStepMeasurability.LiveDiscrete p) :
    Except CoordinatorPhaseClock.ClockFailure
      (CoordinatorPhaseClock.StartRoundResult p) :=
  CoordinatorPhaseClock.startRound p rate.eta.val time
    ⟨live.clockSigma, live.clockCutoff, live.clockBoundary, live.clockProposal⟩
    live.pending

/-- The retained `priorClock` and `clockPending` fields reduce to the exact
clock and pending fields used by `localReleaseStartResult`. -/
theorem localReleaseStartResult_eq_decoded
    (rate : RateInput p) (time : Fin p.T)
    (payload : Payload (p := p) (rate := rate))
    (live : ReferenceActivePhysicalStepMeasurability.LiveDiscrete p) :
    localReleaseStartResult rate time live =
      CoordinatorPhaseClock.startRound p rate.eta.val time
        (ReferenceActivePhysicalStepMeasurability.decodeLiveRegisters payload live).priorClock
        (ReferenceActivePhysicalStepMeasurability.decodeLiveRegisters payload live).clockPending := by
  rfl

/-- A literal local readout on the canonical state code. Its first coordinate
retains every coordinator branch and its second coordinate records the
computed clock result only when the incoming branch is live. -/
def localReleaseReadout
    (rate : RateInput p) (time : Fin p.T)
    (code : ReferenceActivePhysicalStepMeasurability.StateCode p rate) :
    LocalReleaseReadout p rate :=
  (code.1, match code.1 with
    | .inl _ => none
    | .inr (.inl (_, live)) => some (localReleaseStartResult rate time live)
    | .inr (.inr _) => none)

/-- The source release gate on one actual incoming state. The timestamp `b` is
zero-based. The caller supplies the physical zero-based round `time`; the
StartRound result is computed here and no success or frame law is an input. -/
def localReleaseGate
    (rate : RateInput p) (b : ℕ) (time : Fin p.T)
    (code : ReferenceActivePhysicalStepMeasurability.StateCode p rate) : Bool :=
  match code.1 with
  | .inl _ => false
  | .inr (.inl (payload, live)) =>
      decide (payload.sigma.val = b) &&
      decide (live.pending = ∅) &&
      decide (live.clockSigma = some payload.sigma) &&
      decide (live.clockCutoff = none) &&
      match localReleaseStartResult rate time live with
      | .error _ => false
      | .ok result => decide (CoordinatorLiveChoiceRecorderStep.unchangedLiveClockFrame
          (ReferenceActivePhysicalStepMeasurability.decodeLiveRegisters payload live) result)
  | .inr (.inr _) => false

/-- The gate's computed frame condition is precisely the clock frame required
by the live choice step. -/
theorem localReleaseGate_startFrame_iff
    (rate : RateInput p) (time : Fin p.T)
    (payload : Payload (p := p) (rate := rate))
    (live : ReferenceActivePhysicalStepMeasurability.LiveDiscrete p)
    (result : CoordinatorPhaseClock.StartRoundResult p) :
    CoordinatorLiveChoiceRecorderStep.unchangedLiveClockFrame
        (ReferenceActivePhysicalStepMeasurability.decodeLiveRegisters payload live) result ↔
      result.clock = ⟨live.clockSigma, live.clockCutoff, live.clockBoundary,
        live.clockProposal⟩ ∧ result.pending = live.pending ∧
        result.ledgerCommand = none ∧ result.assignmentStart = none := by
  rfl

/-- Borel measurability of the locally computed clock result on the
countable/discrete live-clock code. -/
private theorem measurable_localReleaseStartResult
    (rate : RateInput p) (time : Fin p.T) :
    Measurable (localReleaseStartResult rate time) := by
  exact measurable_of_countable (localReleaseStartResult rate time)

/-- The readout is Borel on the canonical inherited state-code space. -/
theorem measurable_localReleaseReadout
    (rate : RateInput p) (time : Fin p.T) :
    Measurable (localReleaseReadout rate time) := by
  let resultCode := fun code : ReferenceActivePhysicalStepMeasurability.CoordinatorCode p rate =>
    match code with
    | .inl _ => (none : Option (Except CoordinatorPhaseClock.ClockFailure
        (CoordinatorPhaseClock.StartRoundResult p)))
    | .inr (.inl (_, live)) => some (localReleaseStartResult rate time live)
    | .inr (.inr _) => none
  have hstart := measurable_localReleaseStartResult rate time
  have hsome : Measurable (fun live : ReferenceActivePhysicalStepMeasurability.LiveDiscrete p =>
      some (localReleaseStartResult rate time live)) := measurable_of_countable _
  have hlive : Measurable (fun z : Payload (p := p) (rate := rate) ×
      ReferenceActivePhysicalStepMeasurability.LiveDiscrete p =>
        some (localReleaseStartResult rate time z.2)) := hsome.comp measurable_snd
  have hcollection : Measurable (fun _ : Payload (p := p) (rate := rate) ×
      (ReferenceActivePhysicalStep.Ledger rate × Option (Fin p.T × Bool)) =>
        (none : Option (Except CoordinatorPhaseClock.ClockFailure
          (CoordinatorPhaseClock.StartRoundResult p)))) := measurable_const
  have hunit : Measurable (fun _ : Unit =>
      (none : Option (Except CoordinatorPhaseClock.ClockFailure
        (CoordinatorPhaseClock.StartRoundResult p)))) := measurable_const
  have htail : Measurable (fun _ : Sum
      (Payload (p := p) (rate := rate) ×
        (ReferenceActivePhysicalStep.Ledger rate × Option (Fin p.T × Bool))) Unit =>
      (none : LocalClockOutput p)) := measurable_const
  have hmid : Measurable (fun z : Sum
      (Payload (p := p) (rate := rate) ×
        ReferenceActivePhysicalStepMeasurability.LiveDiscrete p)
      (Sum (Payload (p := p) (rate := rate) ×
        (ReferenceActivePhysicalStep.Ledger rate × Option (Fin p.T × Bool))) Unit) =>
      Sum.elim (fun live => some (localReleaseStartResult rate time live.2))
        (fun _ => (none : LocalClockOutput p)) z) := by
    exact Measurable.sumElim hlive htail
  have hcode : Measurable resultCode := by
    exact measurable_const.sumElim hmid
  have hpair : Measurable (fun code :
      ReferenceActivePhysicalStepMeasurability.CoordinatorCode p rate =>
        (code, resultCode code)) := measurable_id.prodMk hcode
  have heq : localReleaseReadout rate time =
      fun code : ReferenceActivePhysicalStepMeasurability.StateCode p rate =>
        (code.1, resultCode code.1) := by
    funext code
    rfl
  rw [heq]
  exact hpair.comp measurable_fst

/-- The gate is Borel in the inherited state-code space. The continuous
payload contributes only its finite sigma coordinate; all clock fields and
the computed StartRound result use the existing discrete live code. -/
theorem measurable_localReleaseGate
    (rate : RateInput p) (b : ℕ) (time : Fin p.T) :
    Measurable (fun code : ReferenceActivePhysicalStepMeasurability.StateCode p rate =>
      localReleaseGate rate b time code) := by
  have hobs : Measurable
      (LaterAssignmentStartMeasurability.payloadObservation
        (p := p) (eta := rate.eta)) := comap_measurable _
  have hsigma : Measurable (fun payload : Payload (p := p) (rate := rate) =>
      (LaterAssignmentStartMeasurability.payloadObservation payload).2.1) :=
    measurable_fst.comp (measurable_snd.comp hobs)
  have hlive : Measurable (fun data : Fin p.T ×
      ReferenceActivePhysicalStepMeasurability.LiveDiscrete p =>
        decide (data.1.val = b) && decide (data.2.pending = ∅) &&
        decide (data.2.clockSigma = some data.1) &&
        decide (data.2.clockCutoff = none) &&
        match localReleaseStartResult rate time data.2 with
        | .error _ => false
        | .ok result => decide (result.clock =
            ⟨data.2.clockSigma, data.2.clockCutoff, data.2.clockBoundary,
              data.2.clockProposal⟩ ∧
            result.pending = data.2.pending ∧ result.ledgerCommand = none ∧
            result.assignmentStart = none)) := by
    exact measurable_of_countable _
  have hliveInput : Measurable (fun z : Payload (p := p) (rate := rate) ×
      ReferenceActivePhysicalStepMeasurability.LiveDiscrete p =>
        ((LaterAssignmentStartMeasurability.payloadObservation z.1).2.1, z.2)) :=
    (hsigma.comp measurable_fst).prodMk measurable_snd
  let codeGate := fun code : ReferenceActivePhysicalStepMeasurability.CoordinatorCode p rate =>
    match code with
    | .inl _ => false
    | .inr (.inl (payload, live)) =>
        decide (payload.sigma.val = b) && decide (live.pending = ∅) &&
        decide (live.clockSigma = some payload.sigma) && decide (live.clockCutoff = none) &&
        match localReleaseStartResult rate time live with
        | .error _ => false
        | .ok result => decide (result.clock =
            (⟨live.clockSigma, live.clockCutoff, live.clockBoundary, live.clockProposal⟩ :
              CoordinatorPhaseClock.ClockRegisters p) ∧
            result.pending = live.pending ∧ result.ledgerCommand = none ∧
            result.assignmentStart = none)
    | .inr (.inr _) => false
  have hliveCode : Measurable (fun z : Payload (p := p) (rate := rate) ×
      ReferenceActivePhysicalStepMeasurability.LiveDiscrete p =>
        decide (z.1.sigma.val = b) && decide (z.2.pending = ∅) &&
        decide (z.2.clockSigma = some z.1.sigma) && decide (z.2.clockCutoff = none) &&
        match localReleaseStartResult rate time z.2 with
        | .error _ => false
        | .ok result => decide (result.clock =
            ⟨z.2.clockSigma, z.2.clockCutoff, z.2.clockBoundary, z.2.clockProposal⟩ ∧
            result.pending = z.2.pending ∧ result.ledgerCommand = none ∧
            result.assignmentStart = none)) := by
    exact hlive.comp hliveInput
  have hfalseLive : Measurable (fun _ : Unit => false) := measurable_const
  have hfalseCollection : Measurable (fun _ : Payload (p := p) (rate := rate) ×
      (ReferenceActivePhysicalStep.Ledger rate × Option (Fin p.T × Bool)) => false) :=
    measurable_const
  have htail : Measurable (Sum.elim (fun _ : Payload (p := p) (rate := rate) ×
      (ReferenceActivePhysicalStep.Ledger rate × Option (Fin p.T × Bool)) => false)
      (fun _ : Unit => false)) := Measurable.sumElim hfalseCollection hfalseLive
  have hmid : Measurable (Sum.elim
      (fun z : Payload (p := p) (rate := rate) ×
        ReferenceActivePhysicalStepMeasurability.LiveDiscrete p =>
          decide (z.1.sigma.val = b) && decide (z.2.pending = ∅) &&
          decide (z.2.clockSigma = some z.1.sigma) && decide (z.2.clockCutoff = none) &&
          match localReleaseStartResult rate time z.2 with
          | .error _ => false
          | .ok result => decide (result.clock =
              (⟨z.2.clockSigma, z.2.clockCutoff, z.2.clockBoundary, z.2.clockProposal⟩ :
                CoordinatorPhaseClock.ClockRegisters p) ∧
              result.pending = z.2.pending ∧ result.ledgerCommand = none ∧
              result.assignmentStart = none))
      (fun z => Sum.elim
        (fun _ : Payload (p := p) (rate := rate) ×
          (ReferenceActivePhysicalStep.Ledger rate × Option (Fin p.T × Bool)) => false)
        (fun _ : Unit => false) z)) := Measurable.sumElim hliveCode htail
  have hcode : Measurable codeGate := by
    unfold codeGate
    exact Measurable.sumElim measurable_const hmid
  have heq : localReleaseGate rate b time = fun code => codeGate code.1 := by
    funext code
    cases code with
    | mk coordinator rest =>
      cases coordinator with
      | inl u => cases u; simp [localReleaseGate, codeGate]
      | inr z => cases z with
        | inl pair =>
          simp only [localReleaseGate, codeGate]
          cases hresult : localReleaseStartResult rate time pair.2 with
          | error failure => simp [hresult]
          | ok result =>
            simp only [hresult]
            apply congrArg (fun accepted =>
              decide (pair.1.sigma.val = b) && decide (pair.2.pending = ∅) &&
                decide (pair.2.clockSigma = some pair.1.sigma) &&
                decide (pair.2.clockCutoff = none) && accepted)
            exact Bool.decide_congr
              (localReleaseGate_startFrame_iff rate time pair.1 pair.2 result)
        | inr tail => cases tail with
          | inl data => simp [localReleaseGate, codeGate]
          | inr unit => cases unit; simp [localReleaseGate, codeGate]
  rw [heq]
  exact hcode.comp measurable_fst

/-- The actual payload retained by one canonical incoming-state code.
First and dagger have no stored payload; collection keeps its full old
payload; live keeps its full current payload. -/
def localStoredPayload
    (code : ReferenceActivePhysicalStepMeasurability.StateCode p rate) :
    Option (Payload (p := p) (rate := rate)) :=
  match code.1 with
  | .inl _ => none
  | .inr (.inl (payload, _)) => some payload
  | .inr (.inr (.inl (payload, _, _))) => some payload
  | .inr (.inr (.inr _)) => none

/-- The exact assignment timestamp paired with the locally reselected whole
payload, when the incoming coordinator state retains one. -/
def localStoredAssignment
    (code : ReferenceActivePhysicalStepMeasurability.StateCode p rate) :
    Option (ℕ × Payload (p := p) (rate := rate)) :=
  (localStoredPayload code).map fun payload => (payload.sigma.val, payload)

/-- Local stored-payload selection is the actual source stored-payload
projection after losslessly decoding the state code. -/
theorem localStoredPayload_eq_decoded
    (code : ReferenceActivePhysicalStepMeasurability.StateCode p rate) :
    localStoredPayload code =
      ReferenceAssignmentPayloadPersistence.storedPayload
        (ReferenceActivePhysicalStepMeasurability.decodeState code).coordinator := by
  cases code with
  | mk coordinator rest =>
    cases coordinator with
    | inl unit => cases unit; simp [localStoredPayload,
        ReferenceActivePhysicalStepMeasurability.decodeState,
        ReferenceActivePhysicalStepMeasurability.decodeCoordinator,
        ReferenceAssignmentPayloadPersistence.storedPayload]
    | inr tail => cases tail with
      | inl live => simp [localStoredPayload,
          ReferenceActivePhysicalStepMeasurability.decodeState,
          ReferenceActivePhysicalStepMeasurability.decodeCoordinator,
          ReferenceActivePhysicalStepMeasurability.decodeLiveRegisters,
          ReferenceAssignmentPayloadPersistence.storedPayload]
      | inr tail => cases tail with
        | inl collection => simp [localStoredPayload,
            ReferenceActivePhysicalStepMeasurability.decodeState,
            ReferenceActivePhysicalStepMeasurability.decodeCoordinator,
            ReferenceAssignmentPayloadPersistence.storedPayload]
        | inr unit => cases unit; simp [localStoredPayload,
            ReferenceActivePhysicalStepMeasurability.decodeState,
            ReferenceActivePhysicalStepMeasurability.decodeCoordinator,
            ReferenceAssignmentPayloadPersistence.storedPayload]

private theorem localStoredAssignment_extract
    (code : ReferenceActivePhysicalStepMeasurability.StateCode p rate)
    (b : ℕ) (payload : Payload (p := p) (rate := rate))
    (h : localStoredAssignment code = some (b, payload)) :
    localStoredPayload code = some payload ∧ payload.sigma.val = b := by
  unfold localStoredAssignment at h
  cases hp : localStoredPayload code with
  | none => simp [hp] at h
  | some current =>
      have hpair : (current.sigma.val, current) = (b, payload) := by
        simpa [hp] using h
      have hcurrent : current = payload := congrArg Prod.snd hpair
      constructor
      · simpa [hp, hcurrent]
      · simpa [hcurrent] using congrArg Prod.fst hpair

/-- A local gate-restricted pending projection for an explicitly supplied
whole assignment payload. It returns the actual `pendingAtStart` only when the
computed local release gate is true. -/
def localReleasePending
    (rate : RateInput p) (b : ℕ) (payload : Payload (p := p) (rate := rate))
    (time : Fin p.T) (state : ReferenceActivePhysicalStep.State p rate) :
    Finset (Fin (p.m - 1)) :=
  if localReleaseGate rate b time
      (ReferenceActivePhysicalStepMeasurability.encodeState state) then
    ReferencePhysicalReleaseQuota.pendingAtStart payload time state
  else ∅

/-- The gate-restricted Q projection is Borel on the original payload and
state carriers. -/
theorem measurable_localReleasePending
    (rate : RateInput p) (b : ℕ) (time : Fin p.T) :
    Measurable (fun z : Payload (p := p) (rate := rate) ×
        ReferenceActivePhysicalStep.State p rate =>
      localReleasePending rate b z.1 time z.2) := by
  have hgate : Measurable (fun z : Payload (p := p) (rate := rate) ×
      ReferenceActivePhysicalStep.State p rate =>
        localReleaseGate rate b time
          (ReferenceActivePhysicalStepMeasurability.encodeState z.2)) :=
    (measurable_localReleaseGate rate b time).comp
      (ReferenceActivePhysicalStepMeasurability.measurable_encodeState.comp measurable_snd)
  have hpending : Measurable (fun z : Payload (p := p) (rate := rate) ×
      ReferenceActivePhysicalStep.State p rate =>
        ReferencePhysicalReleaseQuota.pendingAtStart z.1 time z.2) :=
    ReferencePhysicalReleaseObservability.measurable_pendingAtStart.comp
      (measurable_fst.prodMk (measurable_const.prodMk measurable_snd))
  exact Measurable.ite (measurableSet_eq_fun hgate measurable_const)
    hpending measurable_const

/-- Q's gate-restricted pending readout at an actual prefix is recovered
through exactly that coordinate of generatedPhaseBefore. -/
theorem localReleasePending_factors_through_generatedPhaseBefore
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p)
    (x : LaunchStart (p := p) rate rewards C_star C_h q t s hs control0)
    (j : Fin (t.val - s + 1)) (b : ℕ)
    (payload : Payload (p := p) (rate := rate)) :
    let time := ReferenceRetainedAssignmentReleaseHistory.retainedHistoryTime s t hs j
    localReleasePending rate b payload time
        ((ReferenceRetainedAssignmentReleaseHistory.retainedGeneratedPrefix
          rate rewards C_star C_h q t s hs control0 x control0 j.val
          (by have hj := j.isLt; omega)).finalState) =
      localReleasePending rate b payload time
        (ReferenceActivePhysicalStepMeasurability.decodeState
          (generatedPhaseBefore rate rewards C_star C_h q t s hs control0 x control0 j)) := by
  simp [localReleasePending, generatedPhaseBefore,
    ReferenceActivePhysicalStepMeasurability.decodeState_encodeState]

/-- The actual retained current payload selection is recovered from the last
coordinate of `generatedPhaseBefore`. -/
theorem localStoredAssignment_last_eq_retainedSelection
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p)
    (x : LaunchStart (p := p) rate rewards C_star C_h q t s hs control0)
    (control : TimeControl p) :
    localStoredAssignment
        (generatedPhaseBefore rate rewards C_star C_h q t s hs control0 x control
          ⟨t.val - s, by omega⟩) =
      ReferenceRetainedAssignmentReleaseHistory.retainedAssignmentSelection
        rate rewards C_star C_h q t s hs control0 x := by
  calc
    localStoredAssignment
        (generatedPhaseBefore rate rewards C_star C_h q t s hs control0 x control
          ⟨t.val - s, by omega⟩) =
      ReferenceRetainedAssignmentReleaseHistory.retainedAssignmentSelectionAtControl
        rate rewards C_star C_h q t s hs control0 x control := by
          unfold localStoredAssignment
          rw [localStoredPayload_eq_decoded]
          simp [generatedPhaseBefore,
            ReferenceActivePhysicalStepMeasurability.decodeState_encodeState,
            ReferenceRetainedAssignmentReleaseHistory.retainedAssignmentSelectionAtControl,
            ReferenceRetainedAssignmentReleaseHistory.retainedGeneratedPrefix]
    _ = ReferenceRetainedAssignmentReleaseHistory.retainedAssignmentSelection
        rate rewards C_star C_h q t s hs control0 x :=
      ReferenceRetainedAssignmentReleaseHistory.retainedAssignmentSelectionAtControl_eq
        rate rewards C_star C_h q t s hs control0 x control

/-- The current-control value in the actual source can replace the fixed
baseline in every coordinate of the observation. -/
theorem generatedPhaseBefore_source_specialization
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
    let split := ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t z
    let control := split.1
    let remainder := split.2
    let hrem : remainder ∈
        ReferenceFixedTimeSourceControlCoupling.fixedControlRemainderStratum p q t := by
      change PrivateSourceStreams.coordinatorIndex p
        ((ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t z).2.2).1.2 = q
      rw [ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_private p q t z]
      change ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p z = q
      rw [ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex]
      exact hselected
    let hstart : remainder ∈ ReferenceInitializationControlRemainder.launchStartRemainderEvent
        rate rewards C_star C_h q t s control := by
      exact (ReferenceInitializationControlRemainder.launchStartRemainderEvent_iff_source
        rate rewards C_star C_h q t control z hselected s hs).mpr ⟨hcross, helapsed⟩
    let seed := ReferenceGeneratedActivePrefixFactor.generatedActiveSeed
      rate rewards C_star C_h q t control remainder hrem s hs hstart
    let hmode := (ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec
      rate rewards C_star C_h q t control remainder hrem s hs hstart).2.1
    let x := ReferenceRetainedBoundaryMeasurability.retainedLaunchStartInputOfSource
      rate rewards C_star C_h q t s hs control0 z hselected hcross helapsed
    ∀ j : Fin (t.val - s + 1),
      generatedPhaseBefore rate rewards C_star C_h q t s hs control0 x control j =
        ReferenceActivePhysicalStepMeasurability.encodeState
          ((ReferenceActivePhysicalHorizon.run seed z.1.2 q rewards s j.val
            (by have hj := j.isLt; omega) hmode).finalState) := by
  intro split control remainder hrem hstart seed hmode x j
  have hxval := ReferenceRetainedBoundaryMeasurability.retainedLaunchStartInputOfSource_val
    rate rewards C_star C_h q t s hs control0 z hselected hcross helapsed
  have honSource := ReferenceGeneratedActivePrefixFactor.generatedActivePrefixFactor_on_source
    rate rewards C_star C_h q t z hselected s j.val hs
    (by have hj := j.isLt; omega) hcross helapsed
  rcases honSource with ⟨hstate, _hevidence⟩
  have hprefix :
      (ReferenceRetainedAssignmentReleaseHistory.retainedGeneratedPrefix
        rate rewards C_star C_h q t s hs control0 x control j.val
        (by have hj := j.isLt; omega)).finalState =
      (ReferenceGeneratedActivePrefixFactor.generatedActivePrefixFactor
        rate rewards C_star C_h q t control remainder hrem s j.val hs hstart
        (by have hj := j.isLt; omega)).finalState := by
    unfold ReferenceRetainedAssignmentReleaseHistory.retainedGeneratedPrefix
    simp only [hxval]
    rfl
  change ReferenceActivePhysicalStepMeasurability.encodeState
      (ReferenceRetainedAssignmentReleaseHistory.retainedGeneratedPrefix
        rate rewards C_star C_h q t s hs control0 x control j.val
        (by have hj := j.isLt; omega)).finalState = _
  rw [hprefix]
  calc
    ReferenceActivePhysicalStepMeasurability.encodeState
        ((ReferenceGeneratedActivePrefixFactor.generatedActivePrefixFactor
          rate rewards C_star C_h q t control remainder hrem s j.val hs hstart
          (by have hj := j.isLt; omega)).finalState) =
      ReferenceActivePhysicalStepMeasurability.encodeState
        ((ReferenceActivePhysicalHorizon.run seed z.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s j.val
          (by have hj := j.isLt; omega) hmode).finalState) :=
        congrArg ReferenceActivePhysicalStepMeasurability.encodeState hstate
    _ = ReferenceActivePhysicalStepMeasurability.encodeState
        ((ReferenceActivePhysicalHorizon.run seed z.1.2 q rewards s j.val
          (by have hj := j.isLt; omega) hmode).finalState) := by
        rw [hselected]

/-- The local gate at an earlier retained coordinate reselects that
coordinate's actual payload and timestamp. -/
theorem localReleaseGate_reselects_actualAssignment
    (rate : RateInput p) (b : ℕ) (time : Fin p.T)
    (code : ReferenceActivePhysicalStepMeasurability.StateCode p rate)
    (hgate : localReleaseGate rate b time code = true) :
    ∃ payload, localStoredAssignment code = some (b, payload) := by
  cases hcoord : code.1 with
  | inl unit => cases unit; simp [localReleaseGate, hcoord] at hgate
  | inr tail => cases tail with
    | inl pair =>
        rcases pair with ⟨payload, live⟩
        refine ⟨payload, ?_⟩
        simp only [localStoredAssignment, localStoredPayload, hcoord, Option.map_some]
        have hb : payload.sigma.val = b := by
          simp [localReleaseGate, hcoord] at hgate
          exact hgate.1.1.1.1
        simp [hb]
    | inr tail => cases tail with
      | inl collection => simp [localReleaseGate, hcoord] at hgate
      | inr unit => cases unit; simp [localReleaseGate, hcoord] at hgate

/-- If an earlier local gate and the current retained selector carry the same
zero-based timestamp on this one actual run, payload chronology proves whole
payload identity. No assignment history is assumed. -/
theorem localReleaseGate_sameRun_payload_identity
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p)
    (x : LaunchStart (p := p) rate rewards C_star C_h q t s hs control0)
    (j : Fin (t.val - s + 1)) (b : ℕ)
    (payload : Payload (p := p) (rate := rate))
    (hselected :
      ReferenceRetainedAssignmentReleaseHistory.retainedAssignmentSelection
        rate rewards C_star C_h q t s hs control0 x = some (b, payload))
    (hgate : localReleaseGate rate b (ReferenceRetainedAssignmentReleaseHistory.retainedHistoryTime
      s t hs j) (generatedPhaseBefore rate rewards C_star C_h q t s hs control0 x control0 j) = true) :
    ∃ earlierPayload,
      localStoredAssignment (generatedPhaseBefore rate rewards C_star C_h q t s hs control0 x
        control0 j) = some (b, earlierPayload) ∧ earlierPayload = payload := by
  obtain ⟨earlierPayload, hearlier⟩ := localReleaseGate_reselects_actualAssignment rate b
    (ReferenceRetainedAssignmentReleaseHistory.retainedHistoryTime s t hs j)
    (generatedPhaseBefore rate rewards C_star C_h q t s hs control0 x control0 j) hgate
  have hcurrent := localStoredAssignment_last_eq_retainedSelection rate rewards C_star C_h q t s
    hs control0 x control0
  have hcurrentStored :
      ReferenceAssignmentPayloadPersistence.storedPayload
        ((ReferenceRetainedAssignmentReleaseHistory.retainedGeneratedPrefix
          rate rewards C_star C_h q t s hs control0 x control0 (t.val - s)
          (by omega)).finalState).coordinator = some payload := by
    let code := generatedPhaseBefore rate rewards C_star C_h q t s hs control0 x control0
      ⟨t.val - s, by omega⟩
    have hassign : localStoredAssignment code = some (b, payload) := hcurrent.trans hselected
    have hpayload := (localStoredAssignment_extract code b payload hassign).1
    have hdecoded := localStoredPayload_eq_decoded code
    rw [hdecoded] at hpayload
    simpa [code, generatedPhaseBefore,
      ReferenceActivePhysicalStepMeasurability.decodeState_encodeState,
      ReferenceRetainedBoundaryMeasurability.retainedIncomingBoundary_state,
      ReferenceRetainedAssignmentReleaseHistory.retainedGeneratedPrefix] using hpayload
  have hEarlierSigma : earlierPayload.sigma.val = b := by
    let code := generatedPhaseBefore rate rewards C_star C_h q t s hs control0 x control0 j
    have hlocal : localStoredAssignment code = some (b, earlierPayload) := hearlier
    exact (localStoredAssignment_extract code b earlierPayload hlocal).2
  have hCurrentSigma : payload.sigma.val = b := by
    let code := generatedPhaseBefore rate rewards C_star C_h q t s hs control0 x control0
      ⟨t.val - s, by omega⟩
    have hlocal : localStoredAssignment code = some (b, payload) := hcurrent.trans hselected
    exact (localStoredAssignment_extract code b payload hlocal).2
  have htime : earlierPayload.sigma.val = payload.sigma.val :=
    hEarlierSigma.trans hCurrentSigma.symm
  let source := ReferenceGeneratedActivePrefixFactor.splitSource q t control0 x.1
  let seed := ReferenceRetainedBoundaryMeasurability.retainedGeneratedActiveSeed
    rate rewards C_star C_h q t s hs control0 x
  have hmode := (ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec
    rate rewards C_star C_h q t control0 x.1 x.2.1 s hs x.2.2).2.1
  have hinitial : seed.coordinator = .first := by
    rcases ReferenceRetainedBoundaryMeasurability.retainedLaunchStart_source_facts
      rate rewards C_star C_h q t s hs control0 x.1 x.2.1 x.2.2 with
      ⟨hcross, _helapsed⟩
    obtain ⟨initial, hlaunch, hinitial, _, _, _⟩ :=
      ReferenceCorrectedInitializationLaunch.correctedLaunch_coordinator_provenance
        rate source rewards C_star C_h hcross
    have hseed : seed = initial :=
      Option.some.inj ((ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec
        rate rewards C_star C_h q t control0 x.1 x.2.1 s hs x.2.2).1.symm.trans hlaunch)
    rw [hseed]
    exact hinitial
  have hrun (count : ℕ) (hcount : s + count ≤ t.val) :
      ReferenceRetainedAssignmentReleaseHistory.retainedGeneratedPrefix
        rate rewards C_star C_h q t s hs control0 x control0 count hcount =
      ReferenceActivePhysicalHorizon.run seed source.1.2 q rewards s count
        (by omega) hmode := by
    unfold ReferenceRetainedAssignmentReleaseHistory.retainedGeneratedPrefix
    dsimp only [seed, source, ReferenceRetainedBoundaryMeasurability.retainedGeneratedActiveSeed]
    unfold ReferenceGeneratedActivePrefixFactor.generatedActivePrefixFactor
    have hindex : ActualInitializationPhysicalStep.selectedRowIndex p source = q := by
      calc
        ActualInitializationPhysicalStep.selectedRowIndex p source =
            ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p source :=
          (ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex
            p source).symm
        _ = q := ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_symm_coordinatorIndex
          p q t control0 x.1 x.2.1
    change ReferenceActivePhysicalHorizon.run seed source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s count
        (by omega) hmode =
      ReferenceActivePhysicalHorizon.run seed source.1.2 q rewards s count (by omega) hmode
    rw [hindex]

  have hj : j.val ≤ t.val - s := by have hj' := j.isLt; omega
  have hleft : storedPayload
      (ReferenceActivePhysicalHorizon.run seed source.1.2 q rewards s j.val
        (by omega) hmode).finalState.coordinator = some earlierPayload := by
    let code := generatedPhaseBefore rate rewards C_star C_h q t s hs control0 x control0 j
    have hlocalPayload :=
      (localStoredAssignment_extract code b earlierPayload hearlier).1
    have hdecoded := localStoredPayload_eq_decoded code
    rw [hdecoded] at hlocalPayload
    have hprefix : storedPayload
        ((ReferenceRetainedAssignmentReleaseHistory.retainedGeneratedPrefix
          rate rewards C_star C_h q t s hs control0 x control0 j.val
          (by have hj' := j.isLt; omega)).finalState).coordinator = some earlierPayload := by
      simpa [code, generatedPhaseBefore,
        ReferenceActivePhysicalStepMeasurability.decodeState_encodeState] using hlocalPayload
    rw [hrun j.val (by omega)] at hprefix
    exact hprefix
  have hright : storedPayload
      (ReferenceActivePhysicalHorizon.run seed source.1.2 q rewards s (t.val - s)
        (by omega) hmode).finalState.coordinator = some payload := by
    rw [← hrun (t.val - s) (by omega)]
    exact hcurrentStored
  have hsame := ReferenceAssignmentPayloadChronology.run_prefix_storedPayload_eq_of_equal_sigma
    seed source.1.2 q rewards s (t.val - s) (by omega) hmode hinitial j.val
    (t.val - s) hj (by omega) earlierPayload payload hleft hright htime
  exact ⟨earlierPayload, hearlier, hsame⟩

/-- A gate is counted even when the actual pending-at-start set is empty.
This local entry stores the gate separately from its pending set. -/
def localReleaseEntry
    (rate : RateInput p) (b : ℕ) (time : Fin p.T)
    (code : ReferenceActivePhysicalStepMeasurability.StateCode p rate) :
    Bool × Option (Finset (Fin (p.m - 1))) :=
  (localReleaseGate rate b time code,
    if localReleaseGate rate b time code then
      match localStoredPayload code with
      | none => none
      | some payload => some (localReleasePending rate b payload time
          (ReferenceActivePhysicalStepMeasurability.decodeState code))
    else none)

/-- The first local gate among the finite retained physical coordinates,
converted to one-based source-round indexing. The empty value is `T + 1`;
the assignment timestamp `b` remains zero-based. -/
def firstLocalReleaseGateRound
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p)
    (x : LaunchStart (p := p) rate rewards C_star C_h q t s hs control0)
    (b : ℕ) : ℕ :=
  let gates := Finset.univ.filter fun j : Fin (t.val - s + 1) =>
    localReleaseGate rate b (ReferenceRetainedAssignmentReleaseHistory.retainedHistoryTime s t hs j)
      (generatedPhaseBefore rate rewards C_star C_h q t s hs control0 x control0 j) = true
  if h : gates.Nonempty then s + (gates.min' h).val + 1 else p.T + 1

/-- Before the empty sentinel, a sublevel of the first local gate is exactly a
finite union of earlier local gate events. -/
theorem firstLocalReleaseGateRound_le_iff
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p)
    (x : LaunchStart (p := p) rate rewards C_star C_h q t s hs control0)
    (b n : ℕ) (hn : n < p.T + 1) :
    firstLocalReleaseGateRound rate rewards C_star C_h q t s hs control0 x b ≤ n ↔
      ∃ j : Fin (t.val - s + 1),
        localReleaseGate rate b (ReferenceRetainedAssignmentReleaseHistory.retainedHistoryTime s t hs j)
          (generatedPhaseBefore rate rewards C_star C_h q t s hs control0 x control0 j) = true ∧
        s + j.val + 1 ≤ n := by
  classical
  unfold firstLocalReleaseGateRound
  dsimp only
  let gates : Finset (Fin (t.val - s + 1)) := Finset.univ.filter fun j =>
    localReleaseGate rate b (ReferenceRetainedAssignmentReleaseHistory.retainedHistoryTime s t hs j)
      (generatedPhaseBefore rate rewards C_star C_h q t s hs control0 x control0 j) = true
  change (if h : gates.Nonempty then s + (gates.min' h).val + 1 else p.T + 1) ≤ n ↔ _
  by_cases hne : gates.Nonempty
  · have hmem : gates.min' hne ∈ gates := gates.min'_mem hne
    have hgate : localReleaseGate rate b
        (ReferenceRetainedAssignmentReleaseHistory.retainedHistoryTime s t hs (gates.min' hne))
        (generatedPhaseBefore rate rewards C_star C_h q t s hs control0 x control0
          (gates.min' hne)) = true := (Finset.mem_filter.mp hmem).2
    constructor
    · intro hle
      rw [dif_pos hne] at hle
      refine ⟨gates.min' hne, hgate, ?_⟩
      exact hle
    · rintro ⟨j, hj, hround⟩
      have hjmem : j ∈ gates := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩
      have hmin : gates.min' hne ≤ j := gates.min'_le j hjmem
      have hminval : (gates.min' hne).val ≤ j.val := Fin.le_iff_val_le_val.mp hmin
      have hshift : s + (gates.min' hne).val + 1 ≤ s + j.val + 1 := by omega
      have htarget := Nat.le_trans hshift hround
      rw [dif_pos hne]
      exact htarget
  · rw [dif_neg hne]
    constructor
    · intro hle
      omega
    · rintro ⟨j, hj, _⟩
      exact False.elim (hne ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩)

/-- Every finite sublevel of the first local gate is Borel on the original
retained launch domain. For `n ≥ T + 1`, the empty sentinel makes the sublevel
the whole domain; below it, the event is the finite union above. -/
theorem firstLocalReleaseGateRound_le_horizon
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p)
    (x : LaunchStart (p := p) rate rewards C_star C_h q t s hs control0)
    (b : ℕ) :
    firstLocalReleaseGateRound rate rewards C_star C_h q t s hs control0 x b ≤ p.T + 1 := by
  classical
  by_cases hne : (Finset.univ.filter fun j : Fin (t.val - s + 1) =>
      localReleaseGate rate b (ReferenceRetainedAssignmentReleaseHistory.retainedHistoryTime s t hs j)
        (generatedPhaseBefore rate rewards C_star C_h q t s hs control0 x control0 j) = true).Nonempty
  · let gates := Finset.univ.filter fun j : Fin (t.val - s + 1) =>
      localReleaseGate rate b (ReferenceRetainedAssignmentReleaseHistory.retainedHistoryTime s t hs j)
        (generatedPhaseBefore rate rewards C_star C_h q t s hs control0 x control0 j) = true
    have hj : (gates.min' hne).val < t.val - s + 1 := (gates.min' hne).isLt
    simp [firstLocalReleaseGateRound, gates, hne]
    have ht := t.isLt
    omega
  · simp [firstLocalReleaseGateRound, hne]

theorem measurableSet_firstLocalReleaseGateRound_le
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p) (b n : ℕ) :
    MeasurableSet {x : LaunchStart (p := p) rate rewards C_star C_h q t s hs control0 |
      firstLocalReleaseGateRound rate rewards C_star C_h q t s hs control0 x b ≤ n} := by
  classical
  by_cases hn : n < p.T + 1
  · have hgate (j : Fin (t.val - s + 1)) : MeasurableSet
        {x : LaunchStart (p := p) rate rewards C_star C_h q t s hs control0 |
          localReleaseGate rate b (ReferenceRetainedAssignmentReleaseHistory.retainedHistoryTime s t hs j)
            (generatedPhaseBefore rate rewards C_star C_h q t s hs control0 x control0 j) = true} := by
      exact measurableSet_eq_fun
        ((measurable_localReleaseGate rate b
          (ReferenceRetainedAssignmentReleaseHistory.retainedHistoryTime s t hs j)).comp
            ((measurable_pi_iff.mp
              (measurable_generatedPhaseBefore rate rewards C_star C_h q t s hs control0
                control0)) j)) measurable_const
    have hterm (j : Fin (t.val - s + 1)) : MeasurableSet
        {x : LaunchStart (p := p) rate rewards C_star C_h q t s hs control0 |
          localReleaseGate rate b (ReferenceRetainedAssignmentReleaseHistory.retainedHistoryTime s t hs j)
            (generatedPhaseBefore rate rewards C_star C_h q t s hs control0 x control0 j) = true ∧
          s + j.val + 1 ≤ n} := by
      have hround : MeasurableSet
          {x : LaunchStart (p := p) rate rewards C_star C_h q t s hs control0 |
            s + j.val + 1 ≤ n} := by
        by_cases h : s + j.val + 1 ≤ n
        · simpa [h] using (MeasurableSet.univ : MeasurableSet
            (Set.univ : Set (LaunchStart (p := p) rate rewards C_star C_h q t s hs control0)))
        · simpa [h] using (MeasurableSet.empty : MeasurableSet
            (∅ : Set (LaunchStart (p := p) rate rewards C_star C_h q t s hs control0)))
      exact MeasurableSet.inter (hgate j) hround
    have heq : {x : LaunchStart (p := p) rate rewards C_star C_h q t s hs control0 |
        firstLocalReleaseGateRound rate rewards C_star C_h q t s hs control0 x b ≤ n} =
        ⋃ j : Fin (t.val - s + 1), {x : LaunchStart
          (p := p) rate rewards C_star C_h q t s hs control0 |
          localReleaseGate rate b (ReferenceRetainedAssignmentReleaseHistory.retainedHistoryTime s t hs j)
            (generatedPhaseBefore rate rewards C_star C_h q t s hs control0 x control0 j) = true ∧
          s + j.val + 1 ≤ n} := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_iUnion]
      exact firstLocalReleaseGateRound_le_iff rate rewards C_star C_h q t s hs
        control0 x b n hn
    rw [heq]
    exact MeasurableSet.iUnion hterm
  · have heq : {x : LaunchStart (p := p) rate rewards C_star C_h q t s hs control0 |
        firstLocalReleaseGateRound rate rewards C_star C_h q t s hs control0 x b ≤ n} =
      Set.univ := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      have hbound := firstLocalReleaseGateRound_le_horizon rate rewards C_star C_h q t s
        hs control0 x b
      omega
    rw [heq]
    exact MeasurableSet.univ

/-- Initialization: when the retained launch starts at the current coordinate,
H's corrected zero-prefix result leaves no stored assignment and hence no
local release gate can be reported from the first-state branch. -/
theorem retainedLaunch_zeroPrefix_no_selection
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T)
    (control0 : TimeControl p)
    (hs : t.val ≤ t.val)
    (x : LaunchStart (p := p) rate rewards C_star C_h q t t.val hs control0)
    : ReferenceRetainedAssignmentReleaseHistory.retainedAssignmentSelection
        rate rewards C_star C_h q t t.val hs control0 x = none :=
  (ReferenceRetainedAssignmentReleaseHistory.retainedAssignmentSelection_zeroPrefix_none
    rate rewards C_star C_h q t t.val hs control0 x rfl).1

/-- One generated successor still has the exact actual drop, retain, or
fresh-birth classification from H's payload chronology. -/
theorem retainedPayload_successor_classification
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p)
    (x : LaunchStart (p := p) rate rewards C_star C_h q t s hs control0)
    (control : TimeControl p) (index : ℕ)
    (hnext : s + (index + 1) ≤ t.val) :
    let source := ReferenceGeneratedActivePrefixFactor.splitSource q t control x.1
    let seed := ReferenceGeneratedActivePrefixFactor.generatedActiveSeed rate rewards C_star C_h
      q t control x.1 x.2.1 s hs
      ((ReferenceInitializationControlRemainder.launchStartRemainderEvent_control_independent
        rate rewards C_star C_h q t s x.1 x.2.1 control0 control).mp x.2.2)
    let selected := ActualInitializationPhysicalStep.selectedRowIndex p source
    let hmode := (ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec
      rate rewards C_star C_h q t control x.1 x.2.1 s hs
      ((ReferenceInitializationControlRemainder.launchStartRemainderEvent_control_independent
        rate rewards C_star C_h q t s x.1 x.2.1 control0 control).mp x.2.2)).2.1
    let record := ReferenceAssignmentPayloadChronology.actualRunRecordAt seed source.1.2 selected
      rewards s index (by omega) hmode
    (ReferenceRetainedAssignmentReleaseHistory.retainedGeneratedPrefix
        rate rewards C_star C_h q t s hs control0 x control (index + 1) (by omega)).records =
      (ReferenceRetainedAssignmentReleaseHistory.retainedGeneratedPrefix
        rate rewards C_star C_h q t s hs control0 x control index (by omega)).records ++ [record] ∧
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
          (ReferenceActivePhysicalStep.step record.input).next.coordinator = some fresh)) :=
  ReferenceRetainedAssignmentReleaseHistory.retainedGeneratedPrefix_successor_payload_classification
    rate rewards C_star C_h q t s hs control0 x control index hnext

end Bandits.Support.ReferenceRetainedReleasePhaseObservation
