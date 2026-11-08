/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ActualPostlaunchStepMeasurability
public import Bandits.Support.ActualCompletePhysicalHistory

/-!
# The actual initialization terminal storage readout

The readout below evaluates the source-initialized run's stored terminal slot
at its own stored terminal block and extracts the present trace.  The source,
whole reward table, fixed constants, and private streams remain the original
ones.  The same extracted trace retains the actual fold and combined-boundary
coordinates, including every follower code, checked and unchecked output,
updated numerator, and tagged next carry.

Mathematical evidence: `sources/zip4/manuscript/07_public_setup.tex:55-114`,
`sources/zip4/manuscript/appendix_b_communication.tex:94-131`,
`sources/zip4/manuscript/06_interruptions.tex:240-296`,
`sources/zip4/manuscript/appendix_a_local_protocol.tex:6-14`, and
`sources/zip4/manuscript/08_main_theorem.tex:67-75`.

This module proves only internal readout and terminal-event facts.  It makes
no source-law, local-information, postlaunch-composition, or regret claim.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.BootstrapObservedFollower
open Bandits.Support.ActiveFollowerDownAcceptance
open Bandits.Support.ActualInitializationRun
open Bandits.Support.ActualInitializationHorizon
open Bandits.Support.ActualInitializationHorizonMeasurability
open Bandits.Support.ActualInitializationHorizonObservation
open Bandits.Support.ActualInitializationBlockMeasurability
open Bandits.Support.ActualInitializationBlockFoldExact
open Bandits.Support.ActualInitializationCombinedBoundaryMeasurability
open Bandits.Support.ActualInitializationSourceObservation

namespace Bandits.Support.ActualInitializationTerminalReadout

abbrev Parameters := ActualInitializationHorizon.Parameters
abbrev RateInput := ActualInitializationHorizonMeasurability.RateInput
abbrev GridRewardTable := ActualInitializationPhysicalStep.GridRewardTable
abbrev SourceInput (p : Parameters) := BootstrapPrivateRoundStreams.SourceInput p
abbrev TraceFamily (p : Parameters) (rate : RateInput p) (C_star C_h : ℝ) :=
  fun block : Fin (n_boot p) =>
    ActualInitializationHorizonMeasurability.TerminalBlockTrace
      (p := p) (rate := rate) (C_star := C_star) (C_h := C_h) block
abbrev StoredTrace (p : Parameters) (rate : RateInput p) (C_star C_h : ℝ) :=
  Sigma (TraceFamily p rate C_star C_h)
abbrev StoredEntry (p : Parameters) (rate : RateInput p) (C_star C_h : ℝ) :=
  Unit ⊕ StoredTrace p rate C_star C_h
abbrev CombinedBoundaryFamily (p : Parameters) (rate : RateInput p) (C_star C_h : ℝ) :=
  fun block : Fin (n_boot p) =>
    ActualInitializationCombinedBoundaryMeasurability.CombinedBoundaryObservation
      p rate block C_star C_h

variable {p : Parameters} {rate : RateInput p} {C_star C_h : ℝ}
  {rewards : GridRewardTable p}

private theorem measurable_of_sigma_sections {α : Type*} {β : α → Type*}
    [∀ a, MeasurableSpace (β a)] {γ : Type*} [MeasurableSpace γ]
    (f : Sigma β → γ)
    (hf : ∀ a, Measurable (fun x : β a => f ⟨a, x⟩)) : Measurable f := by
  intro s hs
  change MeasurableSet[(⨅ a, (inferInstance : MeasurableSpace (β a)).map (Sigma.mk a))]
    {x | f x ∈ s}
  rw [MeasurableSpace.measurableSet_iInf]
  intro a
  rw [MeasurableSpace.map_def]
  exact hf a hs

private theorem measurable_finiteIndexEvaluation {n : ℕ} {β : Type*}
    [MeasurableSpace β] :
    Measurable (fun pair : Fin n × (Fin n → β) => pair.2 pair.1) := by
  intro s hs
  have hpre :
      {pair : Fin n × (Fin n → β) | pair.2 pair.1 ∈ s} =
        ⋃ i : Fin n, {pair | pair.1 = i ∧ pair.2 i ∈ s} := by
    ext pair
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · intro h
      exact ⟨pair.1, rfl, h⟩
    · rintro ⟨i, hi, h⟩
      simpa [hi] using h
  change MeasurableSet {pair : Fin n × (Fin n → β) | pair.2 pair.1 ∈ s}
  rw [hpre]
  exact MeasurableSet.iUnion fun i =>
    ((measurableSet_singleton i).preimage measurable_fst).inter
      ((measurable_pi_apply i).comp measurable_snd hs)

/-- The literal selected terminal entry in O's existing run-tail storage. -/
def sourceInitializedTerminalStoredEntry (source : SourceInput p) :
    StoredEntry p rate C_star C_h :=
  let observation := ActualInitializationSourceObservation.sourceInitializedRunObservation
    (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
      (rewards := rewards) source
  observation.suffix.terminalEntries observation.suffix.terminalBlock

/-- The stored entry is measurable by evaluating the public measurable entry
family at its public measurable terminal-block coordinate. -/
theorem measurable_sourceInitializedTerminalStoredEntry :
    Measurable (sourceInitializedTerminalStoredEntry (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) (rewards := rewards)) := by
  let observation := fun source : SourceInput p =>
    ActualInitializationSourceObservation.sourceInitializedRunObservation
      (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
        (rewards := rewards) source
  have hobs : Measurable observation :=
    ActualInitializationSourceObservation.measurable_sourceInitializedRunObservation
      (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
        (rewards := rewards)
  have hcoordinates := (comap_measurable
      (ActualInitializationHorizonMeasurability.runFromObservationCoordinates
        (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
        (block := ActualInitializationRun.firstBlock p))).comp hobs
  have hsuffix : Measurable (fun source : SourceInput p => (observation source).suffix) :=
    measurable_snd.comp (measurable_snd.comp hcoordinates)
  have hblock := ActualInitializationHorizonMeasurability.measurable_runTail_terminalBlock
    (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
  have hentries := ActualInitializationHorizonMeasurability.measurable_runTail_terminalEntries
    (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
  have hpair : Measurable (fun source : SourceInput p =>
      ((observation source).suffix.terminalBlock,
        (observation source).suffix.terminalEntries)) :=
    (hblock.comp hsuffix).prodMk (hentries.comp hsuffix)
  change Measurable (fun source : SourceInput p =>
    ((observation source).suffix.terminalEntries)
      ((observation source).suffix.terminalBlock))
  exact measurable_finiteIndexEvaluation.comp hpair

/-- Public same-run reconstruction proves the exact stored terminal slot is
present and names the original B trace stored in that slot. -/
theorem sourceInitializedTerminalStoredEntry_reconstruction
    (source : SourceInput p) :
    let observation := ActualInitializationSourceObservation.sourceInitializedRunObservation
      (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
        (rewards := rewards) source
    ∃ (terminal : Fin (n_boot p))
      (carry : FixedConstantsBlockCarry p rate terminal C_star C_h),
      let trace := ActualInitializationHorizonMeasurability.terminalBlockTraceOfInput
        (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
        (rewards := rewards) terminal (source, carry)
      observation.suffix.terminalBlock = terminal ∧
        sourceInitializedTerminalStoredEntry (p := p) (rate := rate)
          (C_star := C_star) (C_h := C_h) (rewards := rewards) source =
            Sum.inr ⟨terminal, trace⟩ := by
  rcases ActualInitializationSourceObservation.sourceInitializedRunObservation_terminal_reconstruction
      (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
      (rewards := rewards) source with
    ⟨terminal, carry, hterminal, hentries, _hfinal, _hcarry, _hstar, _hh,
      _hconsumed, _hfold, _hdata⟩
  let observation := ActualInitializationSourceObservation.sourceInitializedRunObservation
    (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
      (rewards := rewards) source
  let trace := ActualInitializationHorizonMeasurability.terminalBlockTraceOfInput
    (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
    (rewards := rewards) terminal (source, carry)
  have hslot : observation.suffix.terminalEntries terminal = Sum.inr ⟨terminal, trace⟩ := by
    have hslot := congrFun hentries terminal
    simpa [ActualInitializationHorizonMeasurability.terminalRunTailObservation]
      using hslot
  refine ⟨terminal, carry, ?_, ?_⟩
  · exact hterminal
  · dsimp [sourceInitializedTerminalStoredEntry, observation]
    rw [hterminal]
    exact hslot

/-- The selected entry is in the original measurable range of `Sum.inr`; its
absent branch is impossible by the preceding actual reconstruction. -/
theorem sourceInitializedTerminalStoredEntry_mem_range (source : SourceInput p) :
    sourceInitializedTerminalStoredEntry (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) (rewards := rewards) source ∈
        Set.range (Sum.inr : StoredTrace p rate C_star C_h → StoredEntry p rate C_star C_h) := by
  rcases sourceInitializedTerminalStoredEntry_reconstruction (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) (rewards := rewards) source with
    ⟨terminal, carry, _hterminal, hentry⟩
  exact ⟨⟨terminal, ActualInitializationHorizonMeasurability.terminalBlockTraceOfInput
      (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
      (rewards := rewards) terminal (source, carry)⟩, hentry.symm⟩

def sourceInitializedTerminalStoredRangeValue (source : SourceInput p) :
    {entry : StoredEntry p rate C_star C_h | entry ∈ Set.range
      (Sum.inr : StoredTrace p rate C_star C_h → StoredEntry p rate C_star C_h)} :=
  ⟨sourceInitializedTerminalStoredEntry (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) (rewards := rewards) source,
    sourceInitializedTerminalStoredEntry_mem_range (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) (rewards := rewards) source⟩

/-- Extract the actual Sigma payload from the present stored terminal entry
using the existing measurable inverse of `Sum.inr`. -/
def sourceInitializedTerminalTrace (rewards : GridRewardTable p) (source : SourceInput p) :
    StoredTrace p rate C_star C_h :=
  MeasurableEquiv.Set.rangeInr (sourceInitializedTerminalStoredRangeValue
    (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
    (rewards := rewards) source)

/-- Matching O's selected terminal entry eliminates its absent branch and
returns precisely the Sigma trace stored in that slot. -/
theorem sourceInitializedTerminalTrace_matches_storedEntry (source : SourceInput p) :
    match sourceInitializedTerminalStoredEntry (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) (rewards := rewards) source with
    | .inl _ => False
    | .inr trace => sourceInitializedTerminalTrace (p := p) (rate := rate)
        (C_star := C_star) (C_h := C_h) (rewards := rewards) source = trace := by
  cases hentry : sourceInitializedTerminalStoredEntry (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) (rewards := rewards) source with
  | inl absent =>
      have hmem := sourceInitializedTerminalStoredEntry_mem_range (p := p) (rate := rate)
        (C_star := C_star) (C_h := C_h) (rewards := rewards) source
      rw [hentry] at hmem
      rcases hmem with ⟨trace, h⟩
      cases h
  | inr trace =>
      simp [sourceInitializedTerminalTrace, sourceInitializedTerminalStoredRangeValue,
        hentry, MeasurableEquiv.Set.rangeInr, Equiv.Set.rangeInr]

/-- The extracted trace is measurable in B's existing Sigma and dependent
trace spaces.  This factors through the measurable range of the actual `inr`
injection, not through a discrete replacement carrier. -/
theorem measurable_sourceInitializedTerminalTrace :
    Measurable (sourceInitializedTerminalTrace (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) (rewards := rewards)) := by
  have hentry := measurable_sourceInitializedTerminalStoredEntry
    (p := p) (rate := rate) (C_star := C_star) (C_h := C_h) (rewards := rewards)
  have hrange : Measurable (sourceInitializedTerminalStoredRangeValue
      (p := p) (rate := rate) (C_star := C_star) (C_h := C_h) (rewards := rewards)) :=
    hentry.subtype_mk
  exact (MeasurableEquiv.Set.rangeInr.measurable_toFun).comp hrange

/-- The Sigma index is the very terminal block index stored in the selected
entry. -/
theorem sourceInitializedTerminalTrace_index (source : SourceInput p) :
    (sourceInitializedTerminalTrace (p := p) (rate := rate) (C_star := C_star)
      (C_h := C_h) (rewards := rewards) source).1 =
      (ActualInitializationSourceObservation.sourceInitializedRunObservation
        (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
        (rewards := rewards) source).suffix.terminalBlock := by
  rcases sourceInitializedTerminalStoredEntry_reconstruction (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) (rewards := rewards) source with
    ⟨terminal, carry, hterminal, hentry⟩
  have hmatch := sourceInitializedTerminalTrace_matches_storedEntry
    (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
    (rewards := rewards) source
  rw [hentry] at hmatch
  have htrace : sourceInitializedTerminalTrace (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) (rewards := rewards) source =
        ⟨terminal, ActualInitializationHorizonMeasurability.terminalBlockTraceOfInput
          (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
          (rewards := rewards) terminal (source, carry)⟩ := by
    simpa using hmatch
  rw [htrace]
  exact hterminal.symm

/-- The extracted Sigma payload is exactly B's stored trace for the terminal
block and the same original source and reached carry. -/
theorem sourceInitializedTerminalTrace_reconstruction (source : SourceInput p) :
    ∃ (terminal : Fin (n_boot p))
      (carry : FixedConstantsBlockCarry p rate terminal C_star C_h),
      (sourceInitializedTerminalTrace (p := p) (rate := rate) (C_star := C_star)
        (C_h := C_h) (rewards := rewards) source : StoredTrace p rate C_star C_h) =
        ⟨terminal, ActualInitializationHorizonMeasurability.terminalBlockTraceOfInput
          (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
          (rewards := rewards) terminal (source, carry)⟩ := by
  rcases sourceInitializedTerminalStoredEntry_reconstruction (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) (rewards := rewards) source with
    ⟨terminal, carry, _hterminal, hentry⟩
  refine ⟨terminal, carry, ?_⟩
  have hmatch := sourceInitializedTerminalTrace_matches_storedEntry
    (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
    (rewards := rewards) source
  rw [hentry] at hmatch
  simpa using hmatch

/-- The actual trace keeps the initial-carry lineage, both common constants,
the consumed count, the actual fold decoder result, the combined handoff, and
the actual terminal disposition. -/
theorem sourceInitializedTerminalTrace_full_reconstruction (source : SourceInput p) :
    let run := ActualInitializationHorizon.sourceInitializedRun p rate source rewards C_star C_h
    ∃ (terminal : Fin (n_boot p))
      (carry : FixedConstantsBlockCarry p rate terminal C_star C_h),
      (sourceInitializedTerminalTrace (p := p) (rate := rate) (C_star := C_star)
        (C_h := C_h) (rewards := rewards) source : StoredTrace p rate C_star C_h) =
          ⟨terminal, ActualInitializationHorizonMeasurability.terminalBlockTraceOfInput
            (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
            (rewards := rewards) terminal (source, carry)⟩ ∧
      (ActualInitializationSourceObservation.sourceInitializedRunObservation
        (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
        (rewards := rewards) source).originalSource = source ∧
      (ActualInitializationSourceObservation.sourceInitializedRunObservation
        (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
        (rewards := rewards) source).initialCarry =
          ⟨ActualInitializationRun.initialCarry p rate C_star C_h, rfl, rfl⟩ ∧
      (ActualInitializationSourceObservation.sourceInitializedRunObservation
        (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
        (rewards := rewards) source).suffix.terminalBlock = terminal ∧
      carry.1.C_star = C_star ∧ carry.1.C_h = C_h ∧
      (ActualInitializationHorizonMeasurability.terminalBlockTraceOfInput
        (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
        (rewards := rewards) terminal (source, carry)).consumed =
        (ActualInitializationRun.foldBlock p rate terminal source rewards carry.1).consumed ∧
      ActualInitializationBlockFoldExact.decodeBlockFoldCodeOfInput
        (p := p) (rate := rate) (block := terminal) (C_star := C_star) (C_h := C_h)
        rewards (source, carry)
        (ActualInitializationHorizonMeasurability.terminalBlockTraceOfInput
          (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
          (rewards := rewards) terminal (source, carry)).blockCode.1 =
        some (ActualInitializationRun.foldBlock p rate terminal source rewards carry.1) ∧
      ActualInitializationHorizonObservation.terminalData run =
        ⟨terminal, carry.1.C_star, carry.1.C_h,
          ActualInitializationRun.foldBlock p rate terminal source rewards carry.1,
          ActualInitializationCombinedBoundaryMeasurability.combinedBoundaryHandoffOfObservation
            (ActualInitializationHorizonMeasurability.terminalBlockTraceOfInput
              (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
              (rewards := rewards) terminal (source, carry)).blockCode.2,
          (ActualInitializationCombinedBoundaryMeasurability.combinedBoundaryHandoffOfObservation
            (ActualInitializationHorizonMeasurability.terminalBlockTraceOfInput
              (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
              (rewards := rewards) terminal (source, carry)).blockCode.2).disposition⟩ := by
  let observation := ActualInitializationSourceObservation.sourceInitializedRunObservation
    (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
      (rewards := rewards) source
  rcases ActualInitializationSourceObservation.sourceInitializedRunObservation_terminal_reconstruction
      (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
      (rewards := rewards) source with
    ⟨terminal, carry, hterminal, hentries, _hfinal, _hcarry, _hstar, _hh,
      hconsumed, hfold, hdata⟩
  let trace := ActualInitializationHorizonMeasurability.terminalBlockTraceOfInput
    (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
    (rewards := rewards) terminal (source, carry)
  have hslot : observation.suffix.terminalEntries terminal = Sum.inr ⟨terminal, trace⟩ := by
    have hslot := congrFun hentries terminal
    simpa [ActualInitializationHorizonMeasurability.terminalRunTailObservation]
      using hslot
  have hentry : sourceInitializedTerminalStoredEntry (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) (rewards := rewards) source =
        Sum.inr ⟨terminal, trace⟩ := by
    dsimp [sourceInitializedTerminalStoredEntry, observation]
    rw [hterminal]
    exact hslot
  have htrace : sourceInitializedTerminalTrace (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) (rewards := rewards) source =
        ⟨terminal, trace⟩ := by
    have hmatch := sourceInitializedTerminalTrace_matches_storedEntry
      (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
      (rewards := rewards) source
    rw [hentry] at hmatch
    simpa using hmatch
  refine ⟨terminal, carry, htrace, ?_, ?_, hterminal, carry.2.1, carry.2.2,
    hconsumed, hfold, hdata⟩
  · exact (ActualInitializationSourceObservation.sourceInitializedRunObservation_input_coordinates
      (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
      (rewards := rewards) source).1
  · exact (ActualInitializationSourceObservation.sourceInitializedRunObservation_input_coordinates
      (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
      (rewards := rewards) source).2

private def terminalDataDisposition {source : SourceInput p}
    (data : Sigma (fun terminal : Fin (n_boot p) =>
      Sigma (fun star : ℝ => Sigma (fun ch : ℝ =>
        ActualInitializationRun.BlockFoldOutput p rate terminal source rewards star ch 0 ×
          ActualInitializationRun.CombinedBoundaryHandoff p rate terminal source ×
            ActualInitializationRun.BoundaryDisposition p rate terminal)))) :
    Sigma (fun terminal : Fin (n_boot p) =>
      ActualInitializationRun.BoundaryDisposition p rate terminal) :=
  ⟨data.1, data.2.2.2.2.2⟩

/-- O's same-run `terminalData` reconstruction preserves both the actual
terminal index and the disposition decoded from the stored C observation. -/
theorem sourceInitializedTerminalTrace_actualDispositionSigma (source : SourceInput p) :
    (⟨(ActualInitializationHorizon.sourceInitializedRun p rate source rewards C_star C_h).terminalBlock,
      (ActualInitializationHorizon.sourceInitializedRun p rate source rewards C_star C_h).terminalDisposition⟩ :
        Sigma (fun terminal : Fin (n_boot p) =>
          ActualInitializationRun.BoundaryDisposition p rate terminal)) =
      ⟨(sourceInitializedTerminalTrace (p := p) (rate := rate) (C_star := C_star)
          (C_h := C_h) (rewards := rewards) source).1,
        (ActualInitializationCombinedBoundaryMeasurability.combinedBoundaryHandoffOfObservation
          (sourceInitializedTerminalTrace (p := p) (rate := rate) (C_star := C_star)
            (C_h := C_h) (rewards := rewards) source).2.blockCode.2).disposition⟩ := by
  let observation := ActualInitializationSourceObservation.sourceInitializedRunObservation
    (p := p) (rate := rate) (C_star := C_star) (C_h := C_h) (rewards := rewards) source
  let run := ActualInitializationHorizon.sourceInitializedRun p rate source rewards C_star C_h
  rcases ActualInitializationSourceObservation.sourceInitializedRunObservation_terminal_reconstruction
      (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
      (rewards := rewards) source with
    ⟨terminal, carry, hterminal, hentries, _hfinal, _hcarry, _hstar, _hh,
      _hconsumed, _hfold, hdata⟩
  let trace := ActualInitializationHorizonMeasurability.terminalBlockTraceOfInput
    (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
    (rewards := rewards) terminal (source, carry)
  have hslot : observation.suffix.terminalEntries terminal = Sum.inr ⟨terminal, trace⟩ := by
    have hslot := congrFun hentries terminal
    simpa [ActualInitializationHorizonMeasurability.terminalRunTailObservation]
      using hslot
  have hentry : sourceInitializedTerminalStoredEntry (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) (rewards := rewards) source =
        Sum.inr ⟨terminal, trace⟩ := by
    dsimp [sourceInitializedTerminalStoredEntry, observation]
    rw [hterminal]
    exact hslot
  have htrace : sourceInitializedTerminalTrace (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) (rewards := rewards) source =
        ⟨terminal, trace⟩ := by
    have hmatch := sourceInitializedTerminalTrace_matches_storedEntry
      (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
      (rewards := rewards) source
    rw [hentry] at hmatch
    simpa using hmatch
  have hdisposition := congrArg terminalDataDisposition hdata
  simp only [terminalDataDisposition, ActualInitializationHorizonObservation.terminalData]
    at hdisposition
  rw [htrace]
  exact hdisposition

private def continuationLaunchFlag {p : Parameters}
    (phase : BootstrapCoordinatorLocalRound.Continuation p) : Bool :=
  match phase with
  | .prelaunch _ => false
  | .launched _ => true

private theorem continuationOfEndpointCode_launchFlag
    (block : Fin (n_boot p)) (source : SourceInput p)
    (code : ActualInitializationCombinedBoundaryMeasurability.PhaseCode p)
    (hvalid : ActualInitializationCombinedBoundaryMeasurability.endpointPhaseValid
      p block C_star C_h source code) :
    continuationLaunchFlag
      (ActualInitializationCombinedBoundaryMeasurability.continuationOfEndpointCode
        p block C_star C_h source code hvalid) =
      code.2.2.2.2.isSome := by
  rcases code with ⟨phaseBlock, target, coordinator, monitor, trigger⟩
  cases trigger <;>
    simp [continuationLaunchFlag,
      ActualInitializationCombinedBoundaryMeasurability.continuationOfEndpointCode]

private def dispositionLaunchFlag {block : Fin (n_boot p)}
    (disposition : ActualInitializationRun.BoundaryDisposition p rate block) : Bool :=
  match disposition with
  | .launched _ _ => true
  | .continueNext _ _ => false
  | .exhausted _ => false

private theorem endpointDisposition_launchFlag
    {block : Fin (n_boot p)}
    (observation : ActualInitializationCombinedBoundaryMeasurability.CombinedBoundaryObservation
      p rate block C_star C_h) :
    dispositionLaunchFlag
      (ActualInitializationCombinedBoundaryMeasurability.endpointDispositionOfObservation
        observation) =
      continuationLaunchFlag
        (ActualInitializationCombinedBoundaryMeasurability.continuationOfEndpointCode
          p block C_star C_h observation.originalSource observation.phaseCode
          observation.phaseValid) := by
  unfold ActualInitializationCombinedBoundaryMeasurability.endpointDispositionOfObservation
  cases hphase : ActualInitializationCombinedBoundaryMeasurability.continuationOfEndpointCode
      p block C_star C_h observation.originalSource observation.phaseCode observation.phaseValid with
  | prelaunch live =>
      cases observation.nextCarry <;>
        simp [dispositionLaunchFlag, continuationLaunchFlag,
          ActualInitializationCombinedBoundaryMeasurability.endpointDispositionOfObservation,
          ActualInitializationCombinedBoundaryMeasurability.endpointDispositionFromData]
  | launched launch =>
      simp [dispositionLaunchFlag, continuationLaunchFlag,
        ActualInitializationCombinedBoundaryMeasurability.endpointDispositionOfObservation,
        ActualInitializationCombinedBoundaryMeasurability.endpointDispositionFromData]

private theorem terminalTraceTrigger_ne_none_iff_dispositionLaunchFlag
    {block : Fin (n_boot p)}
    (trace : ActualInitializationHorizonMeasurability.TerminalBlockTrace
      (p := p) (rate := rate) (C_star := C_star) (C_h := C_h) block) :
    ActualInitializationSourceObservation.terminalTraceTrigger trace ≠ none ↔
      dispositionLaunchFlag
        (ActualInitializationCombinedBoundaryMeasurability.endpointDispositionOfObservation
          trace.blockCode.2) = true := by
  let observation := trace.blockCode.2
  have hflag := (endpointDisposition_launchFlag (p := p) (rate := rate)
    (C_star := C_star) (C_h := C_h) observation).trans
      (continuationOfEndpointCode_launchFlag (p := p)
        (C_star := C_star) (C_h := C_h) block observation.originalSource
        observation.phaseCode observation.phaseValid)
  change observation.phaseCode.2.2.2.2 ≠ none ↔ _
  have htag : observation.phaseCode.2.2.2.2 ≠ none ↔
      observation.phaseCode.2.2.2.2.isSome = true := by
    cases observation.phaseCode.2.2.2.2 <;> simp
  rw [htag, ← hflag]

private theorem sourceInitializedTerminalTrace_actualLaunchFlag (source : SourceInput p) :
    dispositionLaunchFlag
      (ActualInitializationHorizon.sourceInitializedRun p rate source rewards C_star C_h).terminalDisposition =
    dispositionLaunchFlag
      (ActualInitializationCombinedBoundaryMeasurability.endpointDispositionOfObservation
        (sourceInitializedTerminalTrace (p := p) (rate := rate) (C_star := C_star)
          (C_h := C_h) (rewards := rewards) source).2.blockCode.2) := by
  have hpair := sourceInitializedTerminalTrace_actualDispositionSigma
    (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
    (rewards := rewards) source
  exact congrArg (fun (pair : Sigma (fun terminal : Fin (n_boot p) =>
      ActualInitializationRun.BoundaryDisposition p rate terminal)) =>
    dispositionLaunchFlag pair.2) hpair

/-- The full combined-boundary observation from the extracted trace, carried
in the same dependent Sigma family indexed by B's original block calendar.
Its measurable structure is C's existing ten-coordinate join. -/
def sourceInitializedTerminalCombinedBoundaryReadout (source : SourceInput p) :
    Sigma (CombinedBoundaryFamily p rate C_star C_h) :=
  let trace := sourceInitializedTerminalTrace (p := p) (rate := rate)
    (C_star := C_star) (C_h := C_h) (rewards := rewards) source
  ⟨trace.1, trace.2.blockCode.2⟩

/-- Measurability of the combined observation is checked on each original
block fiber, then assembled in the standard dependent Sigma space. -/
theorem measurable_sourceInitializedTerminalCombinedBoundaryReadout :
    Measurable (sourceInitializedTerminalCombinedBoundaryReadout
      (p := p) (rate := rate) (C_star := C_star) (C_h := C_h) (rewards := rewards)) := by
  let fiberMap := fun trace : StoredTrace p rate C_star C_h =>
    (⟨trace.1, trace.2.blockCode.2⟩ : Sigma (CombinedBoundaryFamily p rate C_star C_h))
  have hfiber (block : Fin (n_boot p)) :
      Measurable (fun trace : TraceFamily p rate C_star C_h block =>
        fiberMap ⟨block, trace⟩) := by
    have hcode := Bandits.Support.ActualInitializationHorizonMeasurability.measurable_terminalBlockTrace_code
      (p := p) (rate := rate)
        (C_star := C_star) (C_h := C_h) block
    have hobservation : Measurable (fun trace : TraceFamily p rate C_star C_h block =>
        trace.blockCode.2) := measurable_snd.comp hcode
    have hmk : Measurable (fun observation : CombinedBoundaryFamily
        p rate C_star C_h block =>
        (⟨block, observation⟩ : Sigma (CombinedBoundaryFamily p rate C_star C_h))) := by
      apply Measurable.of_le_map
      exact iInf_le _ block
    exact hmk.comp hobservation
  have hsigma := measurable_of_sigma_sections fiberMap hfiber
  change Measurable (fiberMap ∘
    sourceInitializedTerminalTrace (p := p) (rate := rate) (C_star := C_star)
      (C_h := C_h) (rewards := rewards) )
  exact hsigma.comp (measurable_sourceInitializedTerminalTrace
    (p := p) (rate := rate) (C_star := C_star) (C_h := C_h) (rewards := rewards))

private theorem measurable_combinedBoundaryFollowerCodes
    (block : Fin (n_boot p)) :
    Measurable (fun observation : CombinedBoundaryFamily p rate C_star C_h block =>
      observation.followerCodes) := by
  apply Measurable.of_comap_le
  rw [ActualInitializationCombinedBoundaryMeasurability.combinedBoundaryObservationMeasurableSpace]
  exact le_sup_of_le_left <| le_sup_of_le_left <|
    le_sup_of_le_left <| le_sup_of_le_left <| le_sup_of_le_right le_rfl

abbrev TerminalBoundaryFollowerCarryCodeFamily (p : Parameters) (rate : RateInput p) :=
  fun block : Fin (n_boot p) =>
    Fin (p.m - 1) → ActualInitializationBlockMeasurability.FollowerCarryCode p rate

/-- The canonical C follower-carry codes read only the retained terminal
follower codes. Their original bootstrap/declared tags and all saved-real
configuration coordinates remain in C's accepted carry-code carrier. -/
def sourceInitializedTerminalBoundaryFollowerCarryCodes (source : SourceInput p) :
    Sigma (TerminalBoundaryFollowerCarryCodeFamily p rate) :=
  let trace := sourceInitializedTerminalTrace (p := p) (rate := rate)
    (C_star := C_star) (C_h := C_h) (rewards := rewards) source
  ⟨trace.1, fun i => ActualInitializationCombinedBoundaryMeasurability.boundaryFollowerCarryCode
    rate trace.1 (trace.2.blockCode.2.followerCodes i)⟩

/-- The carry-code family is measurable from C's retained original
follower-code coordinate and is assembled in the original dependent block
sum. -/
theorem measurable_sourceInitializedTerminalBoundaryFollowerCarryCodes :
    Measurable (sourceInitializedTerminalBoundaryFollowerCarryCodes
      (p := p) (rate := rate) (C_star := C_star) (C_h := C_h) (rewards := rewards)) := by
  let fiberMap := fun trace : StoredTrace p rate C_star C_h =>
    (⟨trace.1, fun i => ActualInitializationCombinedBoundaryMeasurability.boundaryFollowerCarryCode
      rate trace.1 (trace.2.blockCode.2.followerCodes i)⟩ :
        Sigma (TerminalBoundaryFollowerCarryCodeFamily p rate))
  have hfiber (block : Fin (n_boot p)) :
      Measurable (fun trace : TraceFamily p rate C_star C_h block => fiberMap ⟨block, trace⟩) := by
    have hcode := ActualInitializationHorizonMeasurability.measurable_terminalBlockTrace_code
      (p := p) (rate := rate) (C_star := C_star) (C_h := C_h) block
    have hobservation : Measurable (fun trace : TraceFamily p rate C_star C_h block =>
        trace.blockCode.2) := measurable_snd.comp hcode
    have hcarry : Measurable (fun observation : CombinedBoundaryFamily
        p rate C_star C_h block => fun i =>
          ActualInitializationCombinedBoundaryMeasurability.boundaryFollowerCarryCode
            rate block (observation.followerCodes i)) := by
      apply measurable_pi_iff.mpr
      intro i
      exact (ActualInitializationCombinedBoundaryMeasurability.measurable_boundaryFollowerCarryCode
        rate block).comp
          ((measurable_pi_apply i).comp
            (measurable_combinedBoundaryFollowerCodes (p := p) (rate := rate)
              (C_star := C_star) (C_h := C_h) block))
    have hmk : Measurable (fun codes :
        Fin (p.m - 1) → ActualInitializationBlockMeasurability.FollowerCarryCode p rate =>
        (⟨block, codes⟩ : Sigma (TerminalBoundaryFollowerCarryCodeFamily p rate))) := by
      apply Measurable.of_le_map
      exact iInf_le _ block
    have hfiberCode : Measurable (fun trace : TraceFamily p rate C_star C_h block =>
        fun i => ActualInitializationCombinedBoundaryMeasurability.boundaryFollowerCarryCode
          rate block (trace.blockCode.2.followerCodes i)) := hcarry.comp hobservation
    exact hmk.comp hfiberCode
  have hsigma := measurable_of_sigma_sections fiberMap hfiber
  change Measurable (fiberMap ∘
    sourceInitializedTerminalTrace (p := p) (rate := rate) (C_star := C_star)
      (C_h := C_h) (rewards := rewards))
  exact hsigma.comp (measurable_sourceInitializedTerminalTrace
    (p := p) (rate := rate) (C_star := C_star) (C_h := C_h) (rewards := rewards))

/-- Each retained carry code decodes, by C's accepted adapter, to the actual
follower carry represented by that terminal follower code. -/
theorem sourceInitializedTerminalBoundaryFollowerCarryCodes_reconstruction
    (source : SourceInput p) :
    ∀ i : Fin (p.m - 1),
      ActualInitializationBlockMeasurability.followerCarryOfCode
        ((sourceInitializedTerminalBoundaryFollowerCarryCodes (p := p) (rate := rate)
          (C_star := C_star) (C_h := C_h) (rewards := rewards) source).2 i) =
      ActualInitializationRun.followerCarryOfBoundaryOutput rate
        (ActualInitializationFollowerBoundaryMeasurability.decodeBoundaryOutputCode
          p rate
            (ActualInitializationFollowerBoundaryMeasurability.boundaryOutputFromFollowerCode
              p rate (sourceInitializedTerminalBoundaryFollowerCarryCodes
                (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
                (rewards := rewards) source).1
              ((sourceInitializedTerminalTrace (p := p) (rate := rate)
                (C_star := C_star) (C_h := C_h) (rewards := rewards)
                source).2.blockCode.2.followerCodes i))) := by
  let trace := sourceInitializedTerminalTrace (p := p) (rate := rate)
    (C_star := C_star) (C_h := C_h) (rewards := rewards) source
  intro i
  change ActualInitializationBlockMeasurability.followerCarryOfCode
      (ActualInitializationCombinedBoundaryMeasurability.boundaryFollowerCarryCode
        rate trace.1 (trace.2.blockCode.2.followerCodes i)) = _
  exact ActualInitializationCombinedBoundaryMeasurability.boundaryFollowerCarryCode_reconstruction
    rate trace.1 (trace.2.blockCode.2.followerCodes i)

/-- O's finite union event reads the trigger from the same actual selected
terminal slot represented by the extracted Sigma trace. -/
theorem sourceInitializedRunTerminalLaunchEvent_iff_trace_trigger (source : SourceInput p) :
    source ∈ ActualInitializationSourceObservation.sourceInitializedRunTerminalLaunchEvent
      (p := p) (rate := rate) (C_star := C_star) (C_h := C_h) (rewards := rewards) ↔
    ((sourceInitializedTerminalTrace (p := p) (rate := rate) (C_star := C_star)
      (C_h := C_h) (rewards := rewards) source).2.blockCode.2.phaseCode.2.2.2.2 ≠ none) := by
  let observation := ActualInitializationSourceObservation.sourceInitializedRunObservation
    (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
      (rewards := rewards) source
  rcases ActualInitializationSourceObservation.sourceInitializedRunObservation_terminal_reconstruction
      (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
      (rewards := rewards) source with
    ⟨terminal, carry, hterminal, hentries, _hfinal, _hcarry, _hstar, _hh,
      _hconsumed, _hfold, _hdata⟩
  let storedTrace := ActualInitializationHorizonMeasurability.terminalBlockTraceOfInput
    (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
    (rewards := rewards) terminal (source, carry)
  have hslot : observation.suffix.terminalEntries terminal = Sum.inr ⟨terminal, storedTrace⟩ := by
    have hslot := congrFun hentries terminal
    simpa [ActualInitializationHorizonMeasurability.terminalRunTailObservation]
      using hslot
  have htrace : sourceInitializedTerminalTrace (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) (rewards := rewards) source =
        ⟨terminal, storedTrace⟩ := by
    rcases sourceInitializedTerminalStoredEntry_reconstruction (p := p) (rate := rate)
        (C_star := C_star) (C_h := C_h) (rewards := rewards) source with
      ⟨terminal', carry', hterminal', hentry⟩
    have hsame : terminal' = terminal := hterminal'.symm.trans hterminal
    subst terminal'
    have hslot' : sourceInitializedTerminalStoredEntry (p := p) (rate := rate)
        (C_star := C_star) (C_h := C_h) (rewards := rewards) source =
          Sum.inr ⟨terminal, storedTrace⟩ := by
      change observation.suffix.terminalEntries observation.suffix.terminalBlock = _
      rw [hterminal]
      exact hslot
    have hmatch := sourceInitializedTerminalTrace_matches_storedEntry (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) (rewards := rewards) source
    rw [hslot'] at hmatch
    simpa using hmatch
  have hevent : source ∈
      ActualInitializationSourceObservation.sourceInitializedRunTerminalLaunchEvent
        (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
          (rewards := rewards) ↔
      ActualInitializationSourceObservation.terminalEntryLaunchPredicate
        (p := p) (rate := rate) (C_star := C_star) (C_h := C_h) terminal
        (observation.suffix.terminalEntries terminal) := by
    simp only [ActualInitializationSourceObservation.sourceInitializedRunTerminalLaunchEvent,
      Set.mem_iUnion,
      ActualInitializationSourceObservation.sourceInitializedRunTerminalLaunchAtBlock,
      Set.mem_setOf_eq]
    constructor
    · rintro ⟨block, hblock, hpred⟩
      have hblock' : block = terminal := by
        calc
          block = observation.suffix.terminalBlock := hblock.symm
          _ = terminal := hterminal
      subst block
      simpa [hterminal] using hpred
    · intro hpred
      exact ⟨terminal, hterminal, hpred⟩
  rw [hevent, hslot, htrace]
  simp [ActualInitializationSourceObservation.terminalEntryLaunchPredicate,
    ActualInitializationSourceObservation.terminalTraceTrigger]

/-- The existing O launch union is exactly the actual run's launched terminal
constructor, with its original launch and learner-seed witnesses. -/
theorem sourceInitializedRunTerminalLaunchEvent_iff_actual_constructor
    (source : SourceInput p) :
    source ∈ ActualInitializationSourceObservation.sourceInitializedRunTerminalLaunchEvent
      (p := p) (rate := rate) (C_star := C_star) (C_h := C_h) (rewards := rewards) ↔
    ∃ launch : BootstrapCoordinatorLocalRound.LaunchedBlock p,
      ∃ seed : ActualInitializationRun.CoordinatorLearnerZeroSeed p,
        (ActualInitializationHorizon.sourceInitializedRun p rate source rewards C_star C_h).terminalDisposition =
          .launched launch seed := by
  rw [sourceInitializedRunTerminalLaunchEvent_iff_trace_trigger
    (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
    (rewards := rewards) source]
  have htag := terminalTraceTrigger_ne_none_iff_dispositionLaunchFlag
    (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
    (trace := (sourceInitializedTerminalTrace (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) (rewards := rewards) source).2)
  have htag' :
      (sourceInitializedTerminalTrace (p := p) (rate := rate) (C_star := C_star)
        (C_h := C_h) (rewards := rewards) source).2.blockCode.2.phaseCode.2.2.2.2 ≠ none ↔
      dispositionLaunchFlag
        (ActualInitializationCombinedBoundaryMeasurability.endpointDispositionOfObservation
          (sourceInitializedTerminalTrace (p := p) (rate := rate) (C_star := C_star)
            (C_h := C_h) (rewards := rewards) source).2.blockCode.2) = true := by
    simpa only [ActualInitializationSourceObservation.terminalTraceTrigger] using htag
  rw [htag']
  rw [← sourceInitializedTerminalTrace_actualLaunchFlag
    (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
    (rewards := rewards) source]
  cases (ActualInitializationHorizon.sourceInitializedRun p rate source rewards C_star C_h).terminalDisposition
    <;> simp [dispositionLaunchFlag]

/-- The fixed-block O launch fibre selects the actual terminal block and the
same actual launched constructor. -/
theorem sourceInitializedRunTerminalLaunchAtBlock_iff_actual_constructor
    (source : SourceInput p) (block : Fin (n_boot p)) :
    source ∈ ActualInitializationSourceObservation.sourceInitializedRunTerminalLaunchAtBlock
      (p := p) (rate := rate) (C_star := C_star) (C_h := C_h) (rewards := rewards) block ↔
    (ActualInitializationHorizon.sourceInitializedRun p rate source rewards C_star C_h).terminalBlock =
        block ∧
      ∃ launch : BootstrapCoordinatorLocalRound.LaunchedBlock p,
        ∃ seed : ActualInitializationRun.CoordinatorLearnerZeroSeed p,
          (ActualInitializationHorizon.sourceInitializedRun p rate source rewards C_star C_h).terminalDisposition =
            .launched launch seed := by
  let observation := ActualInitializationSourceObservation.sourceInitializedRunObservation
    (p := p) (rate := rate) (C_star := C_star) (C_h := C_h) (rewards := rewards) source
  let run := ActualInitializationHorizon.sourceInitializedRun p rate source rewards C_star C_h
  constructor
  · intro hblockEvent
    change observation.suffix.terminalBlock = block ∧ _ at hblockEvent
    rcases hblockEvent with ⟨hblock, hpredicate⟩
    have hlaunchEvent : source ∈
        ActualInitializationSourceObservation.sourceInitializedRunTerminalLaunchEvent
          (p := p) (rate := rate) (C_star := C_star) (C_h := C_h) (rewards := rewards) := by
      simp only [ActualInitializationSourceObservation.sourceInitializedRunTerminalLaunchEvent,
        Set.mem_iUnion]
      refine ⟨block, ?_⟩
      change observation.suffix.terminalBlock = block ∧ _
      exact ⟨hblock, hpredicate⟩
    have hlaunch := (sourceInitializedRunTerminalLaunchEvent_iff_actual_constructor
      (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
      (rewards := rewards) source).1 hlaunchEvent
    have hterminal := ActualInitializationSourceObservation.sourceInitializedRunObservation_terminalBlock_eq_actual
        (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
        (rewards := rewards) source
    exact ⟨hterminal.symm.trans hblock, hlaunch⟩
  · rintro ⟨hblock, hlaunch⟩
    have hlaunchEvent := (sourceInitializedRunTerminalLaunchEvent_iff_actual_constructor
      (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
      (rewards := rewards) source).2 hlaunch
    simp only [ActualInitializationSourceObservation.sourceInitializedRunTerminalLaunchEvent,
      Set.mem_iUnion] at hlaunchEvent
    rcases hlaunchEvent with ⟨tag, htag⟩
    change observation.suffix.terminalBlock = tag ∧ _ at htag
    have htagEq : tag = block := by
      calc
        tag = observation.suffix.terminalBlock := htag.1.symm
        _ = run.terminalBlock :=
          ActualInitializationSourceObservation.sourceInitializedRunObservation_terminalBlock_eq_actual
            (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
            (rewards := rewards) source
        _ = block := hblock
    subst tag
    exact htag

/-- The finite terminal-launch successor-index union read on O's original
block fibres. -/
def sourceInitializedTerminalSuccessorIndexUnion (next : Fin (n_boot p)) :
    Set (SourceInput p) :=
  ⋃ block : Fin (n_boot p),
    {source | block.val + 1 = next.val ∧
      source ∈ ActualInitializationSourceObservation.sourceInitializedRunTerminalLaunchAtBlock
        (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
        (rewards := rewards) block ∧
      BootstrapObservedFollower.blockStop p block < p.T}

/-- The output-index graph of M's actual postlaunch successor-block adapter.
Launch and learner-seed records are existential operational outputs of the
same source run; no successor index is selected as an independent input. -/
def sourceInitializedActualSuccessorIndexGraph (next : Fin (n_boot p)) :
    Set (SourceInput p) :=
  {source | ∃ launch : BootstrapCoordinatorLocalRound.LaunchedBlock p,
    ∃ seed : ActualInitializationRun.CoordinatorLearnerZeroSeed p,
    ∃ hlaunch : (ActualInitializationHorizon.sourceInitializedRun p rate source rewards
      C_star C_h).terminalDisposition = .launched launch seed,
    ∃ hbefore : launch.monitor.launchPosition < p.T,
      ActualPostlaunchPhysicalStep.sourceInitializedLaunchSuccessorBlock p rate source
        rewards C_star C_h launch seed hlaunch hbefore = next}

/-- The actual O terminal-launch union with the prescribed finite successor
index condition equals the output graph of M's actual successor adapter. -/
theorem sourceInitializedTerminalSuccessorIndexUnion_eq_actualGraph
    (next : Fin (n_boot p)) :
    sourceInitializedTerminalSuccessorIndexUnion (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) (rewards := rewards) next =
    sourceInitializedActualSuccessorIndexGraph (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) (rewards := rewards) next := by
  ext source
  simp only [sourceInitializedTerminalSuccessorIndexUnion, Set.mem_iUnion,
    Set.mem_setOf_eq, sourceInitializedActualSuccessorIndexGraph]
  constructor
  · rintro ⟨block, hindex, hblockEvent, hbeforeBlock⟩
    rcases (sourceInitializedRunTerminalLaunchAtBlock_iff_actual_constructor
      (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
      (rewards := rewards) source block).1 hblockEvent with
      ⟨hterminal, launch, seed, hlaunch⟩
    have hstrict := ActualInitializationHorizon.sourceInitializedRun_terminal_launch_strict
      p rate source rewards C_star C_h launch seed hlaunch
    have hbefore : launch.monitor.launchPosition < p.T := by
      change BootstrapObservedFollower.blockStop p block < p.T at hbeforeBlock
      rw [← hterminal] at hbeforeBlock
      rw [← hstrict.2.2.2] at hbeforeBlock
      exact hbeforeBlock
    refine ⟨launch, seed, hlaunch, hbefore, ?_⟩
    apply Fin.ext
    simpa [ActualPostlaunchPhysicalStep.sourceInitializedLaunchSuccessorBlock,
      ActualInitializationRun.successorBlock, hterminal] using hindex
  · rintro ⟨launch, seed, hlaunch, hbefore, hsuccessor⟩
    let run := ActualInitializationHorizon.sourceInitializedRun p rate source rewards C_star C_h
    have hstrict := ActualInitializationHorizon.sourceInitializedRun_terminal_launch_strict
      p rate source rewards C_star C_h launch seed hlaunch
    have hblockEvent := (sourceInitializedRunTerminalLaunchAtBlock_iff_actual_constructor
      (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
      (rewards := rewards) source run.terminalBlock).2 ⟨rfl, launch, seed, hlaunch⟩
    have hindex : run.terminalBlock.val + 1 = next.val := by
      have hvalues := congrArg Fin.val hsuccessor
      simpa [ActualPostlaunchPhysicalStep.sourceInitializedLaunchSuccessorBlock,
        ActualInitializationRun.successorBlock] using hvalues
    refine ⟨run.terminalBlock, hindex, hblockEvent, ?_⟩
    change BootstrapObservedFollower.blockStop p run.terminalBlock < p.T
    rw [← hstrict.2.2.2]
    exact hbefore

/-- The exhaustion union event is exactly the no-crossing tag in the actual
selected terminal trace.  This remains distinct from a launch at boundary T. -/
theorem sourceInitializedRunTerminalExhaustionEvent_iff_trace_no_trigger
    (source : SourceInput p) :
    source ∈ ActualInitializationSourceObservation.sourceInitializedRunTerminalExhaustionEvent
      (p := p) (rate := rate) (C_star := C_star) (C_h := C_h) (rewards := rewards) ↔
    ((sourceInitializedTerminalTrace (p := p) (rate := rate) (C_star := C_star)
      (C_h := C_h) (rewards := rewards) source).2.blockCode.2.phaseCode.2.2.2.2 = none) := by
  let observation := ActualInitializationSourceObservation.sourceInitializedRunObservation
    (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
      (rewards := rewards) source
  rcases ActualInitializationSourceObservation.sourceInitializedRunObservation_terminal_reconstruction
      (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
      (rewards := rewards) source with
    ⟨terminal, carry, hterminal, hentries, _hfinal, _hcarry, _hstar, _hh,
      _hconsumed, _hfold, _hdata⟩
  let storedTrace := ActualInitializationHorizonMeasurability.terminalBlockTraceOfInput
    (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
    (rewards := rewards) terminal (source, carry)
  have hslot : observation.suffix.terminalEntries terminal = Sum.inr ⟨terminal, storedTrace⟩ := by
    have hslot := congrFun hentries terminal
    simpa [ActualInitializationHorizonMeasurability.terminalRunTailObservation]
      using hslot
  have htrace : sourceInitializedTerminalTrace (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) (rewards := rewards) source =
        ⟨terminal, storedTrace⟩ := by
    rcases sourceInitializedTerminalStoredEntry_reconstruction (p := p) (rate := rate)
        (C_star := C_star) (C_h := C_h) (rewards := rewards) source with
      ⟨terminal', _carry', hterminal', _hentry⟩
    have hsame : terminal' = terminal := hterminal'.symm.trans hterminal
    subst terminal'
    have hentry' : sourceInitializedTerminalStoredEntry (p := p) (rate := rate)
        (C_star := C_star) (C_h := C_h) (rewards := rewards) source =
          Sum.inr ⟨terminal, storedTrace⟩ := by
      change observation.suffix.terminalEntries observation.suffix.terminalBlock = _
      rw [hterminal]
      exact hslot
    have hmatch := sourceInitializedTerminalTrace_matches_storedEntry (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) (rewards := rewards) source
    rw [hentry'] at hmatch
    simpa using hmatch
  have hevent : source ∈
      ActualInitializationSourceObservation.sourceInitializedRunTerminalExhaustionEvent
        (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
          (rewards := rewards) ↔
      ActualInitializationSourceObservation.terminalEntryExhaustionPredicate
        (p := p) (rate := rate) (C_star := C_star) (C_h := C_h) terminal
        (observation.suffix.terminalEntries terminal) := by
    simp only [ActualInitializationSourceObservation.sourceInitializedRunTerminalExhaustionEvent,
      Set.mem_iUnion,
      ActualInitializationSourceObservation.sourceInitializedRunTerminalExhaustionAtBlock,
      Set.mem_setOf_eq]
    constructor
    · rintro ⟨block, hblock, hpred⟩
      have hblock' : block = terminal := by
        calc
          block = observation.suffix.terminalBlock := hblock.symm
          _ = terminal := hterminal
      subst block
      simpa [hterminal] using hpred
    · intro hpred
      exact ⟨terminal, hterminal, hpred⟩
  rw [hevent, hslot, htrace]
  simp [ActualInitializationSourceObservation.terminalEntryExhaustionPredicate,
    ActualInitializationSourceObservation.terminalTraceTrigger]

/-- Launch and exhaustion partition the actual terminal slot by its original
trigger tag. -/
theorem sourceInitializedTerminalEvents_partition (source : SourceInput p) :
    (source ∈ ActualInitializationSourceObservation.sourceInitializedRunTerminalLaunchEvent
        (p := p) (rate := rate) (C_star := C_star) (C_h := C_h) (rewards := rewards)) ∨
    (source ∈ ActualInitializationSourceObservation.sourceInitializedRunTerminalExhaustionEvent
        (p := p) (rate := rate) (C_star := C_star) (C_h := C_h) (rewards := rewards)) := by
  by_cases htrigger :
      (sourceInitializedTerminalTrace (p := p) (rate := rate) (C_star := C_star)
        (C_h := C_h) (rewards := rewards) source).2.blockCode.2.phaseCode.2.2.2.2 = none
  · exact Or.inr ((sourceInitializedRunTerminalExhaustionEvent_iff_trace_no_trigger
      (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
      (rewards := rewards) source).2 htrigger)
  · exact Or.inl ((sourceInitializedRunTerminalLaunchEvent_iff_trace_trigger
      (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
      (rewards := rewards) source).2 htrigger)

/-- The launch and exhaustion tags cannot both occupy O's same selected
terminal entry. -/
theorem sourceInitializedTerminalEvents_disjoint (source : SourceInput p) :
    source ∈ ActualInitializationSourceObservation.sourceInitializedRunTerminalLaunchEvent
      (p := p) (rate := rate) (C_star := C_star) (C_h := C_h) (rewards := rewards) →
    source ∉ ActualInitializationSourceObservation.sourceInitializedRunTerminalExhaustionEvent
      (p := p) (rate := rate) (C_star := C_star) (C_h := C_h) (rewards := rewards) := by
  intro hlaunch hexhaust
  have htrigger := (sourceInitializedRunTerminalLaunchEvent_iff_trace_trigger
    (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
    (rewards := rewards) source).1 hlaunch
  have hnone := (sourceInitializedRunTerminalExhaustionEvent_iff_trace_no_trigger
    (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
    (rewards := rewards) source).1 hexhaust
  exact htrigger hnone

/-- O's exhaustion union is exactly the actual run's exhausted terminal
constructor.  The stopped-run proof excludes `continueNext`; launch and
exhaustion remain distinct at the final boundary. -/
theorem sourceInitializedRunTerminalExhaustionEvent_iff_actual_constructor
    (source : SourceInput p) :
    source ∈ ActualInitializationSourceObservation.sourceInitializedRunTerminalExhaustionEvent
      (p := p) (rate := rate) (C_star := C_star) (C_h := C_h) (rewards := rewards) ↔
    ∃ live : BootstrapCoordinatorLocalRound.PrelaunchBlock p,
      (ActualInitializationHorizon.sourceInitializedRun p rate source rewards C_star C_h).terminalDisposition =
        .exhausted live := by
  let run := ActualInitializationHorizon.sourceInitializedRun p rate source rewards C_star C_h
  constructor
  · intro hexhaust
    cases hdisposition : run.terminalDisposition with
    | launched launch seed =>
        have hlaunch := (sourceInitializedRunTerminalLaunchEvent_iff_actual_constructor
          (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
          (rewards := rewards) source).2 ⟨launch, seed, hdisposition⟩
        exact False.elim
          ((sourceInitializedTerminalEvents_disjoint (p := p) (rate := rate)
            (C_star := C_star) (C_h := C_h) (rewards := rewards) source hlaunch) hexhaust)
    | exhausted live => exact ⟨live, rfl⟩
    | continueNext next carry =>
        exact False.elim (ActualCompletePhysicalHistory.sourceRun_not_continueNext
          p rate source rewards C_star C_h run next carry hdisposition)
  · rintro ⟨live, hdisposition⟩
    rcases sourceInitializedTerminalEvents_partition (p := p) (rate := rate)
        (C_star := C_star) (C_h := C_h) (rewards := rewards) source with hlaunch | hexhaust
    · rcases (sourceInitializedRunTerminalLaunchEvent_iff_actual_constructor
        (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
        (rewards := rewards) source).1 hlaunch with ⟨launch, seed, hlaunch⟩
      rw [hdisposition] at hlaunch
      cases hlaunch
    · exact hexhaust

/-- The fixed-block O exhaustion fibre is the actual terminal block paired
with H's no-crossing exhausted constructor. -/
theorem sourceInitializedRunTerminalExhaustionAtBlock_iff_actual_constructor
    (source : SourceInput p) (block : Fin (n_boot p)) :
    source ∈ ActualInitializationSourceObservation.sourceInitializedRunTerminalExhaustionAtBlock
      (p := p) (rate := rate) (C_star := C_star) (C_h := C_h) (rewards := rewards) block ↔
    (ActualInitializationHorizon.sourceInitializedRun p rate source rewards C_star C_h).terminalBlock =
        block ∧
      ∃ live : BootstrapCoordinatorLocalRound.PrelaunchBlock p,
        (ActualInitializationHorizon.sourceInitializedRun p rate source rewards C_star C_h).terminalDisposition =
          .exhausted live := by
  let observation := ActualInitializationSourceObservation.sourceInitializedRunObservation
    (p := p) (rate := rate) (C_star := C_star) (C_h := C_h) (rewards := rewards) source
  let run := ActualInitializationHorizon.sourceInitializedRun p rate source rewards C_star C_h
  constructor
  · intro hblockEvent
    change observation.suffix.terminalBlock = block ∧ _ at hblockEvent
    rcases hblockEvent with ⟨hblock, hpredicate⟩
    have hexhaustEvent : source ∈
        ActualInitializationSourceObservation.sourceInitializedRunTerminalExhaustionEvent
          (p := p) (rate := rate) (C_star := C_star) (C_h := C_h) (rewards := rewards) := by
      simp only [ActualInitializationSourceObservation.sourceInitializedRunTerminalExhaustionEvent,
        Set.mem_iUnion]
      refine ⟨block, ?_⟩
      change observation.suffix.terminalBlock = block ∧ _
      exact ⟨hblock, hpredicate⟩
    have hexhaust := (sourceInitializedRunTerminalExhaustionEvent_iff_actual_constructor
      (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
      (rewards := rewards) source).1 hexhaustEvent
    have hterminal := ActualInitializationSourceObservation.sourceInitializedRunObservation_terminalBlock_eq_actual
      (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
      (rewards := rewards) source
    exact ⟨hterminal.symm.trans hblock, hexhaust⟩
  · rintro ⟨hblock, hexhaust⟩
    have hexhaustEvent := (sourceInitializedRunTerminalExhaustionEvent_iff_actual_constructor
      (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
      (rewards := rewards) source).2 hexhaust
    simp only [ActualInitializationSourceObservation.sourceInitializedRunTerminalExhaustionEvent,
      Set.mem_iUnion] at hexhaustEvent
    rcases hexhaustEvent with ⟨tag, htag⟩
    change observation.suffix.terminalBlock = tag ∧ _ at htag
    have htagEq : tag = block := by
      calc
        tag = observation.suffix.terminalBlock := htag.1.symm
        _ = run.terminalBlock :=
          ActualInitializationSourceObservation.sourceInitializedRunObservation_terminalBlock_eq_actual
            (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
            (rewards := rewards) source
        _ = block := hblock
    subst tag
    exact htag

/-- The literal strict pre-horizon launch event required for the actual
source-initialized run. -/
def sourceInitializedPreHorizonTerminalLaunchEvent : Set (SourceInput p) :=
  ActualInitializationSourceObservation.sourceInitializedRunTerminalLaunchEvent
      (p := p) (rate := rate) (C_star := C_star) (C_h := C_h) (rewards := rewards) ∩
    {source | ActualInitializationSourceObservation.sourceInitializedRunTerminalBoundaryPosition
      (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
      (rewards := rewards) source < p.T}

/-- The strict pre-horizon launch event is Borel on the whole original
private source space. -/
theorem measurable_sourceInitializedPreHorizonTerminalLaunchEvent :
    MeasurableSet (sourceInitializedPreHorizonTerminalLaunchEvent
      (p := p) (rate := rate) (C_star := C_star) (C_h := C_h) (rewards := rewards)) := by
  change MeasurableSet (ActualInitializationSourceObservation.sourceInitializedRunTerminalLaunchEvent
      (p := p) (rate := rate) (C_star := C_star) (C_h := C_h) (rewards := rewards) ∩ _)
  exact ActualInitializationSourceObservation.measurable_sourceInitializedRunTerminalLaunchEvent
      (p := p) (rate := rate) (C_star := C_star) (C_h := C_h) (rewards := rewards) |>.inter
    (measurableSet_lt
      (ActualInitializationSourceObservation.measurable_sourceInitializedRunTerminalBoundaryPosition
        (p := p) (rate := rate) (C_star := C_star) (C_h := C_h) (rewards := rewards))
      measurable_const)

/-- The literal pre-horizon event is equivalent to a present trigger in the
extracted actual terminal trace and the actual terminal boundary being
strictly before T. -/
theorem sourceInitializedPreHorizonTerminalLaunchEvent_iff_trace_trigger
    (source : SourceInput p) :
    source ∈ sourceInitializedPreHorizonTerminalLaunchEvent
      (p := p) (rate := rate) (C_star := C_star) (C_h := C_h) (rewards := rewards) ↔
      (sourceInitializedTerminalTrace (p := p) (rate := rate) (C_star := C_star)
        (C_h := C_h) (rewards := rewards) source).2.blockCode.2.phaseCode.2.2.2.2 ≠ none ∧
      ActualInitializationSourceObservation.sourceInitializedRunTerminalBoundaryPosition
        (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
        (rewards := rewards) source < p.T := by
  simp only [sourceInitializedPreHorizonTerminalLaunchEvent, Set.mem_inter_iff,
    Set.mem_setOf_eq]
  rw [sourceInitializedRunTerminalLaunchEvent_iff_trace_trigger]

/-- The strict pre-horizon event is the actual launched constructor together
with its actual launch position strictly below T. -/
theorem sourceInitializedPreHorizonTerminalLaunchEvent_iff_actual_constructor
    (source : SourceInput p) :
    source ∈ sourceInitializedPreHorizonTerminalLaunchEvent
      (p := p) (rate := rate) (C_star := C_star) (C_h := C_h) (rewards := rewards) ↔
    ∃ launch : BootstrapCoordinatorLocalRound.LaunchedBlock p,
      ∃ seed : ActualInitializationRun.CoordinatorLearnerZeroSeed p,
        (ActualInitializationHorizon.sourceInitializedRun p rate source rewards C_star C_h).terminalDisposition =
          .launched launch seed ∧ launch.monitor.launchPosition < p.T := by
  simp only [sourceInitializedPreHorizonTerminalLaunchEvent, Set.mem_inter_iff,
    Set.mem_setOf_eq]
  rw [sourceInitializedRunTerminalLaunchEvent_iff_actual_constructor]
  constructor
  · rintro ⟨⟨launch, seed, hlaunch⟩, hboundary⟩
    have hstrict := ActualInitializationHorizon.sourceInitializedRun_terminal_launch_strict
      p rate source rewards C_star C_h launch seed hlaunch
    refine ⟨launch, seed, hlaunch, ?_⟩
    change BootstrapObservedFollower.blockStop p
      (ActualInitializationHorizon.sourceInitializedRun p rate source rewards C_star C_h).terminalBlock <
        p.T at hboundary
    rw [← hstrict.2.2.2] at hboundary
    exact hboundary
  · rintro ⟨launch, seed, hlaunch, hbefore⟩
    have hstrict := ActualInitializationHorizon.sourceInitializedRun_terminal_launch_strict
      p rate source rewards C_star C_h launch seed hlaunch
    refine ⟨⟨launch, seed, hlaunch⟩, ?_⟩
    change BootstrapObservedFollower.blockStop p
      (ActualInitializationHorizon.sourceInitializedRun p rate source rewards C_star C_h).terminalBlock <
        p.T
    rw [← hstrict.2.2.2]
    exact hbefore


end Bandits.Support.ActualInitializationTerminalReadout

end
