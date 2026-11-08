/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ActualInitializationHorizonObservation

/-!
# The source-initialized actual initialization observation

This module starts the accepted horizon observation at the original source and
the exact initial carry, then records focused consequences of the accepted
same-run reconstruction.  It uses the actual whole published table, every
original private coordinate, the whole fixed reward table, and the same two
fixed constants throughout.

Mathematical evidence: `sources/zip4/manuscript/07_public_setup.tex:55-114,144-164`,
`sources/zip4/manuscript/appendix_b_communication.tex:94-131,160-165`, and
`sources/zip4/manuscript/08_main_theorem.tex:30-75`.

These are deterministic internal observation and Borel-section results.  They
make no product-law, probability, integrability, selected-row locality, or
regret claim.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.CompletePublicTable
open Bandits.Support.ActualInitializationRun
open Bandits.Support.ActualInitializationHorizon
open Bandits.Support.ActualInitializationHorizonMeasurability
open Bandits.Support.ActualInitializationHorizonObservation
open Bandits.Support.ActualInitializationBlockMeasurability
open Bandits.Support.ActualInitializationBlockFoldExact
open Bandits.Support.ActualInitializationBlockFoldMeasurability
open Bandits.Support.ActualInitializationCombinedBoundaryMeasurability
open Bandits.Support.BootstrapCoordinatorRoundMeasurability
open Bandits.Support.BootstrapObservedFollower

namespace Bandits.Support.ActualInitializationSourceObservation

abbrev Parameters := ActualInitializationHorizon.Parameters
abbrev RateInput := ActualInitializationHorizonMeasurability.RateInput
abbrev GridRewardTable := ActualInitializationHorizonMeasurability.GridRewardTable

variable {p : Parameters} {rate : RateInput p}
  {C_star C_h : ℝ} {rewards : GridRewardTable p}

/-- The actual horizon observation at the original source and exact
`ActualInitializationRun.initialCarry`. -/
def sourceInitializedRunObservation
    (source : BootstrapPrivateRoundStreams.SourceInput p) :
    RunFromObservation (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
      (ActualInitializationRun.firstBlock p) :=
  ActualInitializationHorizonObservation.runFromObservation
    (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
    (rewards := rewards) (ActualInitializationRun.firstBlock p)
    (source, ⟨ActualInitializationRun.initialCarry p rate C_star C_h, rfl, rfl⟩)

/-- The observation retains the complete original source and the exact
fixed-constant initial carry, including both constant equalities. -/
theorem sourceInitializedRunObservation_input_coordinates
    (source : BootstrapPrivateRoundStreams.SourceInput p) :
    let observation := sourceInitializedRunObservation (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) (rewards := rewards) source
    observation.originalSource = source ∧
      observation.initialCarry =
        ⟨ActualInitializationRun.initialCarry p rate C_star C_h, rfl, rfl⟩ := by
  constructor <;> rfl

/-- Full terminal reconstruction for H's source-initialized run.  This keeps
the reached carry, both constants, the whole terminal fold, the entire
combined-boundary handoff, and its disposition. -/
theorem sourceInitializedRunObservation_terminal_reconstruction
    (source : BootstrapPrivateRoundStreams.SourceInput p) :
    let observation := sourceInitializedRunObservation (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) (rewards := rewards) source
    let run := ActualInitializationHorizon.sourceInitializedRun p rate source
      rewards C_star C_h
    ∃ (terminal : Fin (n_boot p))
      (carry : FixedConstantsBlockCarry p rate terminal C_star C_h),
      let trace := terminalBlockTraceOfInput (rewards := rewards) terminal
        (source, carry)
      observation.suffix.terminalBlock = terminal ∧
      observation.suffix.terminalEntries =
        (terminalRunTailObservation terminal trace).terminalEntries ∧
      finalCarriedInput ⟨ActualInitializationRun.firstBlock p,
        ActualInitializationRun.initialCarry p rate C_star C_h⟩ run.continuedBlocks =
          ⟨terminal, carry.1⟩ ∧
      trace.carry = carry ∧ trace.terminalC_star = run.terminalC_star ∧
      trace.terminalC_h = run.terminalC_h ∧
      trace.consumed =
        (foldBlock p rate terminal source rewards carry.1).consumed ∧
      decodeBlockFoldCodeOfInput rewards (source, carry) trace.blockCode.1 =
        some (foldBlock p rate terminal source rewards carry.1) ∧
      terminalData run =
        ⟨terminal, carry.1.C_star, carry.1.C_h,
          foldBlock p rate terminal source rewards carry.1,
          combinedBoundaryHandoffOfObservation trace.blockCode.2,
          (combinedBoundaryHandoffOfObservation trace.blockCode.2).disposition⟩ := by
  simpa only [sourceInitializedRunObservation,
      ActualInitializationHorizon.sourceInitializedRun] using
    (runFrom_terminal_reconstruction (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) (rewards := rewards)
      (ActualInitializationRun.firstBlock p)
      (source, ⟨ActualInitializationRun.initialCarry p rate C_star C_h, rfl, rfl⟩))

/-- Every H continuation is reconstructed in its original order with its
actual next carry, full handoff code, fold code, and `branch_eq` certificate. -/
theorem sourceInitializedRunObservation_continued_reconstruction
    (source : BootstrapPrivateRoundStreams.SourceInput p) :
    let observation := sourceInitializedRunObservation (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) (rewards := rewards) source
    let run := ActualInitializationHorizon.sourceInitializedRun p rate source
      rewards C_star C_h
    ∀ execution ∈ run.continuedBlocks,
      ∃ (tag : Fin (n_boot p))
        (trace : ContinuedBlockTrace (p := p) (rate := rate)
          (C_star := C_star) (C_h := C_h) tag),
        observation.suffix.continuedEntries execution.block = .inr ⟨tag, trace⟩ ∧
        continuedTracePayload trace = executionPayload execution ∧
        trace.blockCode =
          (terminalBlockTraceOfInput (rewards := rewards) tag (source, trace.carry)).blockCode ∧
        decodeBlockFoldCodeOfInput rewards (source, trace.carry) trace.blockCode.1 =
          some (foldBlock p rate tag source rewards trace.carry.1) ∧
        HEq (combinedBoundaryHandoffOfObservation trace.blockCode.2)
          (combinedBoundaryHandoff p rate tag source rewards
            trace.carry.1.C_star trace.carry.1.C_h
            (foldBlock p rate tag source rewards trace.carry.1)) ∧
        (combinedBoundaryHandoff p rate execution.block source rewards
          execution.carry.C_star execution.carry.C_h
          (foldBlock p rate execution.block source rewards execution.carry)).disposition =
            .continueNext execution.next execution.nextCarry := by
  simpa only [sourceInitializedRunObservation,
      ActualInitializationHorizon.sourceInitializedRun] using
    (runFrom_continued_reconstruction (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) (rewards := rewards)
      (ActualInitializationRun.firstBlock p)
      (source, ⟨ActualInitializationRun.initialCarry p rate C_star C_h, rfl, rfl⟩))

/-- The full continued execution payloads appear in the original H order. -/
theorem sourceInitializedRunObservation_continued_order
    (source : BootstrapPrivateRoundStreams.SourceInput p) :
    let observation := sourceInitializedRunObservation (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) (rewards := rewards) source
    let run := ActualInitializationHorizon.sourceInitializedRun p rate source
      rewards C_star C_h
    run.continuedBlocks.map (fun execution =>
      continuedEntryPayload observation.suffix execution.block) =
        run.continuedBlocks.map (fun execution => Sum.inr (executionPayload execution)) := by
  simpa only [sourceInitializedRunObservation,
      ActualInitializationHorizon.sourceInitializedRun] using
    (runFrom_continued_order (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) (rewards := rewards)
      (ActualInitializationRun.firstBlock p)
      (source, ⟨ActualInitializationRun.initialCarry p rate C_star C_h, rfl, rfl⟩))

/-- An absent observed continuation slot is exactly an absent actual H entry. -/
theorem sourceInitializedRunObservation_continued_absent
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (other : Fin (n_boot p)) :
    (sourceInitializedRunObservation (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) (rewards := rewards) source).suffix.continuedEntries
        other = .inl () ↔
      ∀ execution ∈
        (ActualInitializationHorizon.sourceInitializedRun p rate source rewards
          C_star C_h).continuedBlocks, execution.block ≠ other := by
  simpa only [sourceInitializedRunObservation,
      ActualInitializationHorizon.sourceInitializedRun] using
    (runFrom_continued_absent (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) (rewards := rewards)
      (ActualInitializationRun.firstBlock p)
      (source, ⟨ActualInitializationRun.initialCarry p rate C_star C_h, rfl, rfl⟩) other)

/-- The complete chronological code list is H's original full physical-record
list, preserving the outer absence tag and inner physical success/error code. -/
theorem sourceInitializedRunObservation_chronologicalRoundCodes
    (source : BootstrapPrivateRoundStreams.SourceInput p) :
    chronologicalRoundCodes (ActualInitializationRun.firstBlock p)
        (sourceInitializedRunObservation (p := p) (rate := rate)
          (C_star := C_star) (C_h := C_h) (rewards := rewards) source).suffix =
      (ActualInitializationHorizon.sourceInitializedRun p rate source rewards
        C_star C_h).records.map (fullRecordCode (C_star := C_star) (C_h := C_h)) := by
  simpa only [sourceInitializedRunObservation,
      ActualInitializationHorizon.sourceInitializedRun] using
    (runFrom_chronologicalRoundCodes (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) (rewards := rewards)
      (ActualInitializationRun.firstBlock p)
      (source, ⟨ActualInitializationRun.initialCarry p rate C_star C_h, rfl, rfl⟩))

/-- The same chronological observation reconstructs all simultaneous actions
and rounded feedback in H's physical order. -/
theorem sourceInitializedRunObservation_actionFeedbackHistory
    (source : BootstrapPrivateRoundStreams.SourceInput p) :
    chronologicalActionFeedbackHistory (ActualInitializationRun.firstBlock p)
        (sourceInitializedRunObservation (p := p) (rate := rate)
          (C_star := C_star) (C_h := C_h) (rewards := rewards) source).suffix =
      (((ActualInitializationHorizon.sourceInitializedRun p rate source rewards
          C_star C_h).records.map (fun record => Sum.inr record.result.actions)),
        ((ActualInitializationHorizon.sourceInitializedRun p rate source rewards
          C_star C_h).records.map (fun record => Sum.inr record.result.feedback))) := by
  simpa only [sourceInitializedRunObservation,
      ActualInitializationHorizon.sourceInitializedRun] using
    (runFrom_actionFeedbackHistory (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) (rewards := rewards)
      (ActualInitializationRun.firstBlock p)
      (source, ⟨ActualInitializationRun.initialCarry p rate C_star C_h, rfl, rfl⟩))

/-- Each player's full own action-feedback history is the projection of the
same chronological actual codes. -/
theorem sourceInitializedRunObservation_ownHistory
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (player : Fin p.m) :
    chronologicalOwnHistory (ActualInitializationRun.firstBlock p)
        (sourceInitializedRunObservation (p := p) (rate := rate)
          (C_star := C_star) (C_h := C_h) (rewards := rewards) source).suffix player =
      (ActualInitializationHorizon.sourceInitializedRun p rate source rewards
        C_star C_h).records.map
          (fun record => Sum.inr (record.result.actions player, record.result.feedback player)) := by
  simpa only [sourceInitializedRunObservation,
      ActualInitializationHorizon.sourceInitializedRun] using
    (runFrom_ownHistory (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) (rewards := rewards)
      (ActualInitializationRun.firstBlock p)
      (source, ⟨ActualInitializationRun.initialCarry p rate C_star C_h, rfl, rfl⟩) player)

/-- Borel measurability on the whole original source, by fixing exactly
`ActualInitializationRun.initialCarry` in O's joint source-and-carry theorem. -/
theorem measurable_sourceInitializedRunObservation :
    Measurable (sourceInitializedRunObservation (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) (rewards := rewards)) := by
  let initial : FixedConstantsBlockCarry p rate (ActualInitializationRun.firstBlock p)
      C_star C_h :=
    ⟨ActualInitializationRun.initialCarry p rate C_star C_h, rfl, rfl⟩
  have hinput : Measurable (fun source : BootstrapPrivateRoundStreams.SourceInput p =>
      (source, initial)) := measurable_id.prodMk measurable_const
  change Measurable (fun source =>
    ActualInitializationHorizonObservation.runFromObservation
      (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
      (rewards := rewards) (ActualInitializationRun.firstBlock p) (source, initial))
  exact (ActualInitializationHorizonObservation.measurable_runFromObservation
    (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
    (rewards := rewards) (ActualInitializationRun.firstBlock p)).comp hinput

/-- Fixing a published output leaves the complete `ExtendedPrivateCoordinates`
as the section variable, including the private coordinator `J` coordinate. -/
def fixedPublicPrivateSourceInitializedRunObservation
    (published : CompletePublicTable.PublishedOutput p)
    (privateCoordinates : BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p) :=
  sourceInitializedRunObservation (p := p) (rate := rate) (C_star := C_star)
    (C_h := C_h) (rewards := rewards) (published, privateCoordinates)

/-- The actual source-initialized observation is Borel on every full private
section at a fixed published output. -/
theorem measurable_fixedPublicPrivateSourceInitializedRunObservation
    (published : CompletePublicTable.PublishedOutput p) :
    Measurable (fixedPublicPrivateSourceInitializedRunObservation (p := p)
      (rate := rate) (C_star := C_star) (C_h := C_h) (rewards := rewards) published) :=
  (measurable_sourceInitializedRunObservation (p := p) (rate := rate)
    (C_star := C_star) (C_h := C_h) (rewards := rewards)).comp
      (measurable_const.prodMk measurable_id)

/-- Replace exactly one complete published row while retaining the fixed ID
array and every other row. -/
def variableRowPublishedOutput
    (ids : CompletePublicTable.IDArray p)
    (rows : CompletePublicTable.CompleteRows p)
    (j0 : Fin (M p))
    (row : CompletePublicTable.CompleteRow p) : CompletePublicTable.PublishedOutput p :=
  (ids, fun j => if j = j0 then row else rows j)

/-- Joint section in one whole continuous row and all original private
coordinates.  The private `J` coordinate remains variable and unchanged. -/
def variableRowPrivateSourceInitializedRunObservation
    (ids : CompletePublicTable.IDArray p)
    (rows : CompletePublicTable.CompleteRows p)
    (j0 : Fin (M p))
    (pair : CompletePublicTable.CompleteRow p ×
      BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p) :=
  sourceInitializedRunObservation (p := p) (rate := rate) (C_star := C_star)
    (C_h := C_h) (rewards := rewards)
    (variableRowPublishedOutput (p := p) ids rows j0 pair.1, pair.2)

/-- The one-row/full-private-coordinate section is jointly Borel with fixed
IDs, fixed other rows, a fixed replacement index, rewards, and constants. -/
theorem measurable_variableRowPrivateSourceInitializedRunObservation
    (ids : CompletePublicTable.IDArray p)
    (rows : CompletePublicTable.CompleteRows p)
    (j0 : Fin (M p)) :
    Measurable (fun pair : CompletePublicTable.CompleteRow p ×
        BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p =>
      variableRowPrivateSourceInitializedRunObservation (p := p) (rate := rate)
        (C_star := C_star) (C_h := C_h) (rewards := rewards) ids rows j0 pair) := by
  have hrows : Measurable (fun pair : CompletePublicTable.CompleteRow p ×
      BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p =>
        fun j : Fin (M p) => if j = j0 then pair.1 else rows j) := by
    apply measurable_pi_iff.mpr
    intro j
    by_cases h : j = j0
    · subst j
      simpa using (measurable_fst : Measurable
        (fun pair : CompletePublicTable.CompleteRow p ×
          BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p => pair.1))
    · simp [h]
  have hpublished : Measurable (fun pair : CompletePublicTable.CompleteRow p ×
      BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p =>
        variableRowPublishedOutput (p := p) ids rows j0 pair.1) := by
    change Measurable (fun pair : CompletePublicTable.CompleteRow p ×
      BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p =>
        (ids, fun j : Fin (M p) => if j = j0 then pair.1 else rows j))
    exact measurable_const.prodMk hrows
  have hsource : Measurable (fun pair : CompletePublicTable.CompleteRow p ×
      BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p =>
        (variableRowPublishedOutput (p := p) ids rows j0 pair.1, pair.2)) :=
    hpublished.prodMk measurable_snd
  exact (measurable_sourceInitializedRunObservation (p := p) (rate := rate)
    (C_star := C_star) (C_h := C_h) (rewards := rewards)).comp hsource

/-- The terminal block of H's actual source-initialized run is Borel on the
whole original source. -/
theorem measurable_sourceInitializedRun_terminalBlock :
    Measurable (fun source : BootstrapPrivateRoundStreams.SourceInput p =>
      (ActualInitializationHorizon.sourceInitializedRun p rate source rewards
        C_star C_h).terminalBlock) := by
  let initial : FixedConstantsBlockCarry p rate (ActualInitializationRun.firstBlock p)
      C_star C_h :=
    ⟨ActualInitializationRun.initialCarry p rate C_star C_h, rfl, rfl⟩
  have hinput : Measurable (fun source : BootstrapPrivateRoundStreams.SourceInput p =>
      (source, initial)) := measurable_id.prodMk measurable_const
  exact (ActualInitializationHorizonObservation.measurable_actual_terminalBlock
    (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
    (rewards := rewards) (ActualInitializationRun.firstBlock p)).comp hinput

/-- Every indexed full physical-round code in H's actual record stream is
Borel on the whole original source, retaining all same-round outcomes. -/
theorem measurable_sourceInitializedRun_round_stream
    (other : Fin (n_boot p)) (cursor : ℕ) :
    Measurable (fun source : BootstrapPrivateRoundStreams.SourceInput p =>
      (roundCodeListCoordinates
        (((ActualInitializationHorizon.sourceInitializedRun p rate source rewards
          C_star C_h).records.filter (fun record => record.block == other)).map
            (fullRecordCode (C_star := C_star) (C_h := C_h)))).2 cursor) := by
  let initial : FixedConstantsBlockCarry p rate (ActualInitializationRun.firstBlock p)
      C_star C_h :=
    ⟨ActualInitializationRun.initialCarry p rate C_star C_h, rfl, rfl⟩
  have hinput : Measurable (fun source : BootstrapPrivateRoundStreams.SourceInput p =>
      (source, initial)) := measurable_id.prodMk measurable_const
  exact (ActualInitializationHorizonObservation.measurable_actual_round_stream
    (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
    (rewards := rewards) (ActualInitializationRun.firstBlock p) other cursor).comp hinput

/-- Read the actual terminal trigger from the stored combined-boundary phase
code. `none` is the no-crossing phase; `some trigger` is the launch phase. -/
def terminalTraceTrigger
    {block : Fin (n_boot p)}
    (trace : TerminalBlockTrace (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) block) : Option (Fin p.T) :=
  trace.blockCode.2.phaseCode.2.2.2.2

/-- The elapsed launch boundary retained in the same combined-boundary monitor
coordinate. Its successor is the numerical launch round, including the `T+1`
sentinel and a launch after the final boundary. -/
def terminalTraceLaunchPosition
    {block : Fin (n_boot p)}
    (trace : TerminalBlockTrace (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) block) : ℕ :=
  trace.blockCode.2.phaseCode.2.2.2.1.launchPosition

/-- A terminal launch entry is present only at its own block fibre and only
when that actual combined-boundary phase stores a trigger. -/
def terminalEntryLaunchPredicate (block : Fin (n_boot p)) :
    (Unit ⊕ (Σ traceBlock : Fin (n_boot p),
      TerminalBlockTrace (p := p) (rate := rate) (C_star := C_star)
        (C_h := C_h) traceBlock)) → Prop
  | .inl _ => False
  | .inr ⟨traceBlock, trace⟩ =>
      traceBlock = block ∧ terminalTraceTrigger trace ≠ none

/-- A terminal exhaustion entry is present only at its own block fibre and
keeps the no-crossing phase tag. -/
def terminalEntryExhaustionPredicate (block : Fin (n_boot p)) :
    (Unit ⊕ (Σ traceBlock : Fin (n_boot p),
      TerminalBlockTrace (p := p) (rate := rate) (C_star := C_star)
        (C_h := C_h) traceBlock)) → Prop
  | .inl _ => False
  | .inr ⟨traceBlock, trace⟩ =>
      traceBlock = block ∧ terminalTraceTrigger trace = none

/-- Elapsed boundary position on one terminal block fibre. Zero records an
absent entry; a present entry keeps its actual block boundary. -/
def terminalEntryElapsedBoundary (block : Fin (n_boot p)) :
    (Unit ⊕ (Σ traceBlock : Fin (n_boot p),
      TerminalBlockTrace (p := p) (rate := rate) (C_star := C_star)
        (C_h := C_h) traceBlock)) → ℕ
  | .inl _ => 0
  | .inr ⟨traceBlock, _⟩ =>
      if traceBlock = block then BootstrapObservedFollower.blockStop p block else 0

/-- Numerical launch round on one terminal block fibre, read from the retained
combined-boundary monitor coordinate. Zero records an absent entry. -/
def terminalEntryLaunchRound (block : Fin (n_boot p)) :
    (Unit ⊕ (Σ traceBlock : Fin (n_boot p),
      TerminalBlockTrace (p := p) (rate := rate) (C_star := C_star)
        (C_h := C_h) traceBlock)) → ℕ
  | .inl _ => 0
  | .inr ⟨traceBlock, trace⟩ =>
      if traceBlock = block then terminalTraceLaunchPosition trace + 1 else 0

private theorem measurable_combinedBoundary_phaseCode (block : Fin (n_boot p)) :
    Measurable (fun observation : CombinedBoundaryObservation p rate block C_star C_h =>
      observation.phaseCode) := by
  apply Measurable.of_comap_le
  rw [combinedBoundaryObservationMeasurableSpace]
  exact le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left
    (le_sup_of_le_left (le_sup_of_le_left
      (le_sup_of_le_right le_rfl)))))

private theorem measurable_terminalTraceTrigger
    (block : Fin (n_boot p)) :
    Measurable (terminalTraceTrigger (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) (block := block)) := by
  have hphase : Measurable (fun trace : TerminalBlockTrace (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) block => trace.blockCode.2.phaseCode) :=
    (measurable_combinedBoundary_phaseCode (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) block).comp
      (measurable_snd.comp (measurable_terminalBlockTrace_code (p := p) (rate := rate)
        (C_star := C_star) (C_h := C_h) block))
  change Measurable (fun trace : TerminalBlockTrace (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) block => trace.blockCode.2.phaseCode.2.2.2.2)
  exact measurable_snd.comp (measurable_snd.comp (measurable_snd.comp
    (measurable_snd.comp hphase)))

private theorem measurable_terminalTraceLaunchPosition
    (block : Fin (n_boot p)) :
    Measurable (terminalTraceLaunchPosition (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) (block := block)) := by
  have hphase : Measurable (fun trace : TerminalBlockTrace (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) block => trace.blockCode.2.phaseCode) :=
    (measurable_combinedBoundary_phaseCode (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) block).comp
      (measurable_snd.comp (measurable_terminalBlockTrace_code (p := p) (rate := rate)
        (C_star := C_star) (C_h := C_h) block))
  have hmonitor : Measurable (fun trace : TerminalBlockTrace (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) block =>
        trace.blockCode.2.phaseCode.2.2.2.1) :=
    measurable_fst.comp (measurable_snd.comp (measurable_snd.comp
      (measurable_snd.comp hphase)))
  change Measurable (fun trace : TerminalBlockTrace (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) block =>
        trace.blockCode.2.phaseCode.2.2.2.1.launchPosition)
  exact (measurable_of_countable
    (fun monitor : BootstrapCoordinatorRoundMeasurability.MonitorCode p =>
      monitor.launchPosition)).comp hmonitor

private theorem measurable_sigma_elim {α : Type*} {β : α → Type*}
    [∀ a, MeasurableSpace (β a)] {γ : Type*} [MeasurableSpace γ]
    (f : Sigma β → γ)
    (hf : ∀ a, Measurable (fun x : β a => f ⟨a, x⟩)) : Measurable f := by
  intro s hs
  change MeasurableSet[
      (⨅ a, (inferInstance : MeasurableSpace (β a)).map (Sigma.mk a))]
    {x | f x ∈ s}
  rw [MeasurableSpace.measurableSet_iInf]
  intro a
  rw [MeasurableSpace.map_def]
  exact hf a hs

private theorem measurable_terminalEntryLaunchPredicate
    (block : Fin (n_boot p)) :
    Measurable (terminalEntryLaunchPredicate (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) block) := by
  apply Measurable.sumElim
  · exact measurable_const
  · apply measurable_sigma_elim
    intro traceBlock
    by_cases hblock : traceBlock = block
    · subst traceBlock
      have htrigger := measurable_terminalTraceTrigger (p := p) (rate := rate)
        (C_star := C_star) (C_h := C_h) block
      have hpred : Measurable (fun trace : TerminalBlockTrace (p := p) (rate := rate)
          (C_star := C_star) (C_h := C_h) block => terminalTraceTrigger trace ≠ none) :=
        measurableSet_setOfPred.mp
          ((measurableSet_singleton none).compl.preimage htrigger)
      simpa [terminalEntryLaunchPredicate] using hpred
    · simp [hblock]

private theorem measurable_terminalEntryExhaustionPredicate
    (block : Fin (n_boot p)) :
    Measurable (terminalEntryExhaustionPredicate (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) block) := by
  apply Measurable.sumElim
  · exact measurable_const
  · apply measurable_sigma_elim
    intro traceBlock
    by_cases hblock : traceBlock = block
    · subst traceBlock
      have htrigger := measurable_terminalTraceTrigger (p := p) (rate := rate)
        (C_star := C_star) (C_h := C_h) block
      have hpred : Measurable (fun trace : TerminalBlockTrace (p := p) (rate := rate)
          (C_star := C_star) (C_h := C_h) block => terminalTraceTrigger trace = none) :=
        measurableSet_setOfPred.mp
          ((measurableSet_singleton none).preimage htrigger)
      simpa [terminalEntryExhaustionPredicate] using hpred
    · simp [hblock]

private theorem measurable_terminalEntryElapsedBoundary
    (block : Fin (n_boot p)) :
    Measurable (terminalEntryElapsedBoundary (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) block) := by
  apply Measurable.sumElim
  · exact measurable_const
  · apply measurable_sigma_elim
    intro traceBlock
    by_cases hblock : traceBlock = block
    · subst traceBlock
      simp
    · simp [hblock]

private theorem measurable_terminalEntryLaunchRound
    (block : Fin (n_boot p)) :
    Measurable (terminalEntryLaunchRound (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) block) := by
  apply Measurable.sumElim
  · exact measurable_const
  · apply measurable_sigma_elim
    intro traceBlock
    by_cases hblock : traceBlock = block
    · subst traceBlock
      have hround := (measurable_of_countable (fun n : ℕ => n + 1)).comp
        (measurable_terminalTraceLaunchPosition (p := p) (rate := rate)
          (C_star := C_star) (C_h := C_h) block)
      convert hround using 1
      funext trace
      simp
    · simp [hblock]

private theorem measurable_sourceInitializedRunObservation_suffix :
    Measurable (fun source : BootstrapPrivateRoundStreams.SourceInput p =>
      (sourceInitializedRunObservation (p := p) (rate := rate)
        (C_star := C_star) (C_h := C_h) (rewards := rewards) source).suffix) := by
  have hcoordinates := (comap_measurable
    (ActualInitializationHorizonMeasurability.runFromObservationCoordinates
      (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
      (block := ActualInitializationRun.firstBlock p))).comp
        (measurable_sourceInitializedRunObservation (p := p) (rate := rate)
          (C_star := C_star) (C_h := C_h) (rewards := rewards))
  exact measurable_snd.comp (measurable_snd.comp hcoordinates)

private theorem measurable_sourceInitializedRunObservation_terminalEntry
    (block : Fin (n_boot p)) :
    Measurable (fun source : BootstrapPrivateRoundStreams.SourceInput p =>
      (sourceInitializedRunObservation (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) (rewards := rewards) source).suffix.terminalEntries block) :=
  (measurable_pi_apply block).comp
    ((ActualInitializationHorizonMeasurability.measurable_runTail_terminalEntries
      (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)).comp
      (measurable_sourceInitializedRunObservation_suffix (p := p) (rate := rate)
        (C_star := C_star) (C_h := C_h) (rewards := rewards)))

/-- The observer's terminal boundary index agrees with H's actual terminal
boundary; this is a projection of the same reconstructed run. -/
theorem sourceInitializedRunObservation_terminalBlock_eq_actual
    (source : BootstrapPrivateRoundStreams.SourceInput p) :
    (sourceInitializedRunObservation (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) (rewards := rewards) source).suffix.terminalBlock =
      (ActualInitializationHorizon.sourceInitializedRun p rate source rewards
        C_star C_h).terminalBlock := by
  simpa only [sourceInitializedRunObservation,
      ActualInitializationHorizon.sourceInitializedRun] using
    (runFrom_terminalBlock_eq (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) (rewards := rewards)
      (ActualInitializationRun.firstBlock p)
      (source, ⟨ActualInitializationRun.initialCarry p rate C_star C_h, rfl, rfl⟩))

/-- Actual terminal launch on a fixed terminal-block fibre. -/
def sourceInitializedRunTerminalLaunchAtBlock (block : Fin (n_boot p)) :
    Set (BootstrapPrivateRoundStreams.SourceInput p) :=
  {source | (sourceInitializedRunObservation (p := p) (rate := rate)
        (C_star := C_star) (C_h := C_h) (rewards := rewards) source).suffix.terminalBlock = block ∧
      terminalEntryLaunchPredicate (p := p) (rate := rate) (C_star := C_star)
        (C_h := C_h) block
        ((sourceInitializedRunObservation (p := p) (rate := rate)
          (C_star := C_star) (C_h := C_h) (rewards := rewards) source).suffix.terminalEntries block)}

/-- Actual terminal exhaustion on a fixed terminal-block fibre, preserving
the distinct no-crossing tag. -/
def sourceInitializedRunTerminalExhaustionAtBlock (block : Fin (n_boot p)) :
    Set (BootstrapPrivateRoundStreams.SourceInput p) :=
  {source | (sourceInitializedRunObservation (p := p) (rate := rate)
        (C_star := C_star) (C_h := C_h) (rewards := rewards) source).suffix.terminalBlock = block ∧
      terminalEntryExhaustionPredicate (p := p) (rate := rate) (C_star := C_star)
        (C_h := C_h) block
        ((sourceInitializedRunObservation (p := p) (rate := rate)
          (C_star := C_star) (C_h := C_h) (rewards := rewards) source).suffix.terminalEntries block)}

/-- The actual source-run terminal LAUNCH event, read on the finite family of
terminal block fibres. -/
def sourceInitializedRunTerminalLaunchEvent : Set (BootstrapPrivateRoundStreams.SourceInput p) :=
  ⋃ block : Fin (n_boot p), sourceInitializedRunTerminalLaunchAtBlock
    (p := p) (rate := rate) (C_star := C_star) (C_h := C_h) (rewards := rewards) block

/-- The actual source-run exhaustion event, retaining the no-crossing phase
separately from a launch at elapsed time `T`. -/
def sourceInitializedRunTerminalExhaustionEvent :
    Set (BootstrapPrivateRoundStreams.SourceInput p) :=
  ⋃ block : Fin (n_boot p), sourceInitializedRunTerminalExhaustionAtBlock
    (p := p) (rate := rate) (C_star := C_star) (C_h := C_h) (rewards := rewards) block

/-- Elapsed terminal boundary position, measured from H's actual terminal
block and therefore finite on the original horizon. -/
def sourceInitializedRunTerminalBoundaryPosition
    (source : BootstrapPrivateRoundStreams.SourceInput p) : ℕ :=
  BootstrapObservedFollower.blockStop p
    (ActualInitializationHorizon.sourceInitializedRun p rate source rewards
      C_star C_h).terminalBlock

/-- The launch-round observable on one terminal block fibre. Zero is the
absent-entry sentinel; exhaustion and a final-boundary launch retain their
actual monitor values even when both give the numerical sentinel `T+1`. -/
def sourceInitializedRunTerminalLaunchRoundAtBlock (block : Fin (n_boot p))
    (source : BootstrapPrivateRoundStreams.SourceInput p) : ℕ :=
  terminalEntryLaunchRound (p := p) (rate := rate) (C_star := C_star)
    (C_h := C_h) block
    ((sourceInitializedRunObservation (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) (rewards := rewards) source).suffix.terminalEntries block)

/-- The elapsed terminal boundary on one block fibre, read from the same
terminal handoff entry. -/
def sourceInitializedRunTerminalElapsedBoundaryAtBlock (block : Fin (n_boot p))
    (source : BootstrapPrivateRoundStreams.SourceInput p) : ℕ :=
  terminalEntryElapsedBoundary (p := p) (rate := rate) (C_star := C_star)
    (C_h := C_h) block
    ((sourceInitializedRunObservation (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) (rewards := rewards) source).suffix.terminalEntries block)

/-- Every fixed terminal-block launch fibre is Borel on the whole original
source. The phase tag is read from the reconstructed combined-boundary code. -/
theorem measurable_sourceInitializedRunTerminalLaunchAtBlock
    (block : Fin (n_boot p)) :
    MeasurableSet (sourceInitializedRunTerminalLaunchAtBlock (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) (rewards := rewards) block) := by
  have hterminal : Measurable (fun source : BootstrapPrivateRoundStreams.SourceInput p =>
      (sourceInitializedRunObservation (p := p) (rate := rate)
        (C_star := C_star) (C_h := C_h) (rewards := rewards) source).suffix.terminalBlock) :=
    (ActualInitializationHorizonMeasurability.measurable_runTail_terminalBlock).comp
      (measurable_sourceInitializedRunObservation_suffix
        (p := p) (rate := rate) (C_star := C_star) (C_h := C_h) (rewards := rewards))
  have hentry := measurable_sourceInitializedRunObservation_terminalEntry
    (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
    (rewards := rewards) block
  have hlaunch := (measurable_terminalEntryLaunchPredicate block).comp hentry
  change MeasurableSet {source | _ = block ∧ _}
  exact ((measurableSet_singleton block).preimage hterminal).inter
    (measurableSet_setOfPred.mpr hlaunch)

/-- Every fixed terminal-block exhaustion fibre is Borel and retains the
actual no-crossing phase separately from a launch at the final boundary. -/
theorem measurable_sourceInitializedRunTerminalExhaustionAtBlock
    (block : Fin (n_boot p)) :
    MeasurableSet (sourceInitializedRunTerminalExhaustionAtBlock (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) (rewards := rewards) block) := by
  have hterminal : Measurable (fun source : BootstrapPrivateRoundStreams.SourceInput p =>
      (sourceInitializedRunObservation (p := p) (rate := rate)
        (C_star := C_star) (C_h := C_h) (rewards := rewards) source).suffix.terminalBlock) :=
    (ActualInitializationHorizonMeasurability.measurable_runTail_terminalBlock).comp
      (measurable_sourceInitializedRunObservation_suffix
        (p := p) (rate := rate) (C_star := C_star) (C_h := C_h) (rewards := rewards))
  have hentry := measurable_sourceInitializedRunObservation_terminalEntry
    (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
    (rewards := rewards) block
  have hexhausted := (measurable_terminalEntryExhaustionPredicate block).comp hentry
  change MeasurableSet {source | _ = block ∧ _}
  exact ((measurableSet_singleton block).preimage hterminal).inter
    (measurableSet_setOfPred.mpr hexhausted)

/-- The source-run terminal launch event is the finite union of its actual
terminal-block fibres, each read from that fibre's reconstructed handoff. -/
theorem measurable_sourceInitializedRunTerminalLaunchEvent :
    MeasurableSet (sourceInitializedRunTerminalLaunchEvent (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) (rewards := rewards)) := by
  exact MeasurableSet.iUnion fun block =>
    measurable_sourceInitializedRunTerminalLaunchAtBlock (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) (rewards := rewards) block

/-- The source-run exhaustion event is the finite union of actual terminal
block fibres and remains disjoint in meaning from final-boundary launch. -/
theorem measurable_sourceInitializedRunTerminalExhaustionEvent :
    MeasurableSet (sourceInitializedRunTerminalExhaustionEvent (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) (rewards := rewards)) := by
  exact MeasurableSet.iUnion fun block =>
    measurable_sourceInitializedRunTerminalExhaustionAtBlock (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) (rewards := rewards) block

/-- The launch-round observable is Borel on each terminal-block fibre. Its
`T+1` value is preserved for both final-boundary launch and no-crossing
exhaustion; the separate event tag distinguishes those cases. -/
theorem measurable_sourceInitializedRunTerminalLaunchRoundAtBlock
    (block : Fin (n_boot p)) :
    Measurable (sourceInitializedRunTerminalLaunchRoundAtBlock (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) (rewards := rewards) block) := by
  exact (measurable_terminalEntryLaunchRound block).comp
      (measurable_sourceInitializedRunObservation_terminalEntry
        (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
        (rewards := rewards) block)

/-- The elapsed-boundary observable is Borel on each terminal-block fibre and
uses zero at the observer's explicit absent-entry tag. -/
theorem measurable_sourceInitializedRunTerminalElapsedBoundaryAtBlock
    (block : Fin (n_boot p)) :
    Measurable (sourceInitializedRunTerminalElapsedBoundaryAtBlock
      (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
      (rewards := rewards) block) := by
  exact (measurable_terminalEntryElapsedBoundary block).comp
      (measurable_sourceInitializedRunObservation_terminalEntry
        (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
        (rewards := rewards) block)

/-- H's actual elapsed terminal boundary is Borel by its finite terminal
block projection. -/
theorem measurable_sourceInitializedRunTerminalBoundaryPosition :
    Measurable (sourceInitializedRunTerminalBoundaryPosition (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) (rewards := rewards)) := by
  exact (measurable_of_countable
    (fun block : Fin (n_boot p) => BootstrapObservedFollower.blockStop p block)).comp
    (measurable_sourceInitializedRun_terminalBlock (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) (rewards := rewards))

end Bandits.Support.ActualInitializationSourceObservation

end
