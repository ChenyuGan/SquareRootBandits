/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ActualInitializationBlockHandoffMeasurability
public import Bandits.Support.ActualInitializationHorizon

/-!
# Joint source-and-carry Borel observation of actual initialization

The recursive code uses P's accepted actual clipped-block fold, complete
combined-boundary observation, no-launch subtype, and next-carry producer.
Each stored block entry is proved to reconstruct that exact block fold and
handoff.  The source-level equality of the recursive terminal trace with
H's dependent `RunSuffix` result is not certified in this module, so the
horizon-level maps remain file-private.

The source inputs are the pinned manuscript ranges
`sources/zip4/manuscript/07_public_setup.tex:55-114,144-164`,
`sources/zip4/manuscript/appendix_b_communication.tex:94-131,160-165`, and
`sources/zip4/manuscript/06_interruptions.tex:235-297`.

This module proves internal measurability of the literal finite recursion
code and its block producers.  It makes no probability, locality, coupling,
or regret claim.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.ActualInitializationRun
open Bandits.Support.ActualInitializationBlockMeasurability
open Bandits.Support.ActualInitializationBlockFoldExact
open Bandits.Support.ActualInitializationCombinedBoundaryMeasurability
open Bandits.Support.ActualInitializationBlockHandoffMeasurability
open Bandits.Support.ActualInitializationHorizon
open Bandits.Support.ActualInitializationStepMeasurability
open Bandits.Support.ActualInitializationBlockFoldMeasurability

namespace Bandits.Support.ActualInitializationHorizonMeasurability

abbrev Parameters := ActualInitializationHorizon.Parameters
abbrev RateInput := ActualInitializationBlockHandoffMeasurability.RateInput
abbrev GridRewardTable := ActualInitializationPhysicalStep.GridRewardTable

variable {p : Parameters} {rate : RateInput p}
  {C_star C_h : ℝ} {rewards : GridRewardTable p}

/-- The full, admitted data emitted by the actual one-block producer. -/
abbrev BlockObservationCode (block : Fin (n_boot p)) :=
  BlockFoldCode p rate block C_star C_h ×
    CombinedBoundaryObservation p rate block C_star C_h

/-- The complete full-input round code, with the block index retained in its
dependent tag.  The inner `Unit` branch remains the physical input-not-ready
code; the outer `Unit` branch below means that a list position is absent. -/
abbrev FullPhysicalRoundCode :=
  Σ block : Fin (n_boot p), ActualRoundOutputCode p rate block

instance fullPhysicalRoundCodeMeasurableSpace :
    MeasurableSpace (FullPhysicalRoundCode (p := p) (rate := rate)) :=
  Sigma.instMeasurableSpace

/-- The standard measurable structure on a finite dependent round-code sum
makes each original block-indexed fibre a measurable injection. -/
theorem measurable_sigma_mk (block : Fin (n_boot p)) :
    Measurable (fun code : ActualRoundOutputCode p rate block =>
      (⟨block, code⟩ : FullPhysicalRoundCode (p := p) (rate := rate))) := by
  apply Measurable.of_le_map
  exact iInf_le _ block

theorem measurable_fixedConstantsCarry_sigmaMk (block : Fin (n_boot p)) :
    Measurable (fun carry : FixedConstantsBlockCarry p rate block C_star C_h =>
      (⟨block, carry⟩ : Σ next : Fin (n_boot p),
        FixedConstantsBlockCarry p rate next C_star C_h)) := by
  apply Measurable.of_le_map
  exact iInf_le _ block

/-- A terminal block keeps the existing input carry, the two shared constants,
the consumed cursor count, E's full fold code, and C's full handoff
observation.  The disposition is decoded from the retained C observation. -/
structure TerminalBlockTrace (block : Fin (n_boot p)) where
  carry : FixedConstantsBlockCarry p rate block C_star C_h
  terminalC_star : ℝ
  terminalC_h : ℝ
  consumed : ℕ
  blockCode : BlockObservationCode (p := p) (rate := rate)
    (C_star := C_star) (C_h := C_h) block

def terminalBlockTraceCoordinates {block : Fin (n_boot p)}
    (trace : TerminalBlockTrace (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) block) :=
  (trace.carry, (trace.terminalC_star,
    (trace.terminalC_h, (trace.consumed, trace.blockCode))))

instance terminalBlockTraceMeasurableSpace (block : Fin (n_boot p)) :
    MeasurableSpace (TerminalBlockTrace (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) block) :=
  MeasurableSpace.comap terminalBlockTraceCoordinates inferInstance

/-- A continuing block retains its original input carry, the actual next
index, the actual successor carry in B's same fixed-constant coordinates,
and the complete physical/handoff code for this block. -/
structure ContinuedBlockTrace (block : Fin (n_boot p)) where
  carry : FixedConstantsBlockCarry p rate block C_star C_h
  nextBlock : Fin (n_boot p)
  nextCarry : Σ next : Fin (n_boot p),
    FixedConstantsBlockCarry p rate next C_star C_h
  blockCode : BlockObservationCode (p := p) (rate := rate)
    (C_star := C_star) (C_h := C_h) block

def continuedBlockTraceCoordinates {block : Fin (n_boot p)}
    (trace : ContinuedBlockTrace (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) block) :=
  (trace.carry, (trace.nextBlock, (trace.nextCarry, trace.blockCode)))

instance continuedBlockTraceMeasurableSpace (block : Fin (n_boot p)) :
    MeasurableSpace (ContinuedBlockTrace (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) block) :=
  MeasurableSpace.comap continuedBlockTraceCoordinates inferInstance

theorem measurable_terminalBlockTrace_sigmaMk (block : Fin (n_boot p)) :
    Measurable (fun trace : TerminalBlockTrace (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) block =>
      (⟨block, trace⟩ : Σ traceBlock : Fin (n_boot p),
        TerminalBlockTrace (p := p) (rate := rate)
          (C_star := C_star) (C_h := C_h) traceBlock)) := by
  apply Measurable.of_le_map
  exact iInf_le _ block

theorem measurable_continuedBlockTrace_sigmaMk (block : Fin (n_boot p)) :
    Measurable (fun trace : ContinuedBlockTrace (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) block =>
      (⟨block, trace⟩ : Σ traceBlock : Fin (n_boot p),
        ContinuedBlockTrace (p := p) (rate := rate)
          (C_star := C_star) (C_h := C_h) traceBlock)) := by
  apply Measurable.of_le_map
  exact iInf_le _ block

/-- The horizon observation is indexed by the original block calendar.  A
`Sum.inl ()` in a block slot means no such initialization block occurred.
Round positions use E's independent outer sum tag for absence, retaining the
inner physical error/success tag from the actual round encoder. -/
structure RunTailObservation where
  terminalBlock : Fin (n_boot p)
  terminalEntries : ∀ block : Fin (n_boot p),
    Unit ⊕ (Σ traceBlock : Fin (n_boot p),
      TerminalBlockTrace (p := p) (rate := rate)
        (C_star := C_star) (C_h := C_h) traceBlock)
  continuedEntries : ∀ block : Fin (n_boot p),
    Unit ⊕ (Σ traceBlock : Fin (n_boot p),
      ContinuedBlockTrace (p := p) (rate := rate)
        (C_star := C_star) (C_h := C_h) traceBlock)
  physicalRoundCodes : ∀ block : Fin (n_boot p), ℕ →
    Unit ⊕ FullPhysicalRoundCode (p := p) (rate := rate)

instance runTailTerminalEntriesMeasurableSpace :
    MeasurableSpace (∀ block : Fin (n_boot p),
      Unit ⊕ (Σ traceBlock : Fin (n_boot p),
        TerminalBlockTrace (p := p) (rate := rate)
          (C_star := C_star) (C_h := C_h) traceBlock)) := by
  infer_instance

instance runTailContinuedEntriesMeasurableSpace :
    MeasurableSpace (∀ block : Fin (n_boot p),
      Unit ⊕ (Σ traceBlock : Fin (n_boot p),
        ContinuedBlockTrace (p := p) (rate := rate)
          (C_star := C_star) (C_h := C_h) traceBlock)) := by
  infer_instance

instance runTailRoundPositionsMeasurableSpace :
    MeasurableSpace (ℕ → Unit ⊕ FullPhysicalRoundCode (p := p) (rate := rate)) := by
  infer_instance

instance runTailPhysicalRoundCodesMeasurableSpace :
    MeasurableSpace (∀ block : Fin (n_boot p),
      ℕ → Unit ⊕ FullPhysicalRoundCode (p := p) (rate := rate)) :=
  by infer_instance

def runTailObservationCoordinates (observation : RunTailObservation
    (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)) :=
  (observation.terminalBlock,
    (observation.terminalEntries,
      (observation.continuedEntries, observation.physicalRoundCodes)))

instance runTailObservationMeasurableSpace :
    MeasurableSpace (RunTailObservation (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h)) :=
  MeasurableSpace.comap runTailObservationCoordinates inferInstance

/-- The public observation also retains the original whole source and the
starting carry, before the recursively observed suffix. -/
structure RunFromObservation (block : Fin (n_boot p)) where
  originalSource : BootstrapPrivateRoundStreams.SourceInput p
  initialCarry : FixedConstantsBlockCarry p rate block C_star C_h
  suffix : RunTailObservation (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)

def runFromObservationCoordinates {block : Fin (n_boot p)}
    (observation : RunFromObservation (p := p) (rate := rate) (C_star := C_star)
      (C_h := C_h) block) :=
  (observation.originalSource, (observation.initialCarry, observation.suffix))

instance runFromObservationMeasurableSpace (block : Fin (n_boot p)) :
    MeasurableSpace (RunFromObservation (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) block) :=
  MeasurableSpace.comap runFromObservationCoordinates inferInstance

/-- The existing block-fold code exposes a list through its admitted
length-indexed stream coordinates. -/
theorem measurable_blockFoldCode_roundCount (block : Fin (n_boot p)) :
    Measurable (fun code : BlockFoldCode p rate block C_star C_h => code.rounds.length) := by
  have hcoordinates := measurable_blockFoldCodeCoordinates
    (p := p) (rate := rate) (block := block) (C_star := C_star) (C_h := C_h)
  exact measurable_fst.comp
    (measurable_snd.comp (measurable_snd.comp hcoordinates))

/-- Read one position from E's original stored list code.  The outer sum is
the list-position tag; the complete original round code is retained inside. -/
def blockPhysicalRoundCodeAt (block : Fin (n_boot p))
    (code : BlockFoldCode p rate block C_star C_h) (cursor : ℕ) :
    Unit ⊕ FullPhysicalRoundCode (p := p) (rate := rate) :=
  Sum.map id (fun round => (⟨block, round⟩ : FullPhysicalRoundCode (p := p) (rate := rate)))
    ((roundCodeListCoordinates code.rounds).2 cursor)

theorem measurable_blockPhysicalRoundCodeAt (block : Fin (n_boot p)) (cursor : ℕ) :
    Measurable (fun code : BlockFoldCode p rate block C_star C_h =>
      blockPhysicalRoundCodeAt (p := p) (rate := rate) (C_star := C_star)
        (C_h := C_h) block code cursor) := by
  have hcoordinates := measurable_blockFoldCodeCoordinates
    (p := p) (rate := rate) (block := block) (C_star := C_star) (C_h := C_h)
  have hstream : Measurable (fun code : BlockFoldCode p rate block C_star C_h =>
      (blockFoldCodeCoordinates code).2.2.2 cursor) := by
    exact (measurable_pi_apply cursor).comp
      (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp hcoordinates)))
  exact (Measurable.sumMap measurable_id
    (measurable_sigma_mk (p := p) (rate := rate) block)).comp hstream

theorem measurable_terminalBlockTraceCoordinates (block : Fin (n_boot p)) :
    Measurable (terminalBlockTraceCoordinates (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) (block := block)) :=
  comap_measurable _

theorem measurable_terminalBlockTrace_carry (block : Fin (n_boot p)) :
    Measurable (fun trace : TerminalBlockTrace (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) block => trace.carry) :=
  measurable_fst.comp
    (measurable_terminalBlockTraceCoordinates (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) block)

theorem measurable_terminalBlockTrace_code (block : Fin (n_boot p)) :
    Measurable (fun trace : TerminalBlockTrace (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) block => trace.blockCode) := by
  exact measurable_snd.comp
    (measurable_snd.comp (measurable_snd.comp
      (measurable_snd.comp
        (measurable_terminalBlockTraceCoordinates (p := p) (rate := rate)
          (C_star := C_star) (C_h := C_h) block))))

theorem measurable_continuedBlockTraceCoordinates (block : Fin (n_boot p)) :
    Measurable (continuedBlockTraceCoordinates (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) (block := block)) :=
  comap_measurable _

theorem measurable_continuedBlockTrace_blockCode (block : Fin (n_boot p)) :
    Measurable (fun trace : ContinuedBlockTrace (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) block => trace.blockCode) :=
  measurable_snd.comp
    (measurable_snd.comp (measurable_snd.comp
      (measurable_continuedBlockTraceCoordinates (p := p) (rate := rate)
        (C_star := C_star) (C_h := C_h) block)))

theorem measurable_continuedBlockTrace_nextCarry (block : Fin (n_boot p)) :
    Measurable (fun trace : ContinuedBlockTrace (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) block => trace.nextCarry) :=
  measurable_fst.comp (measurable_snd.comp
    (measurable_snd.comp
      (measurable_continuedBlockTraceCoordinates (p := p) (rate := rate)
        (C_star := C_star) (C_h := C_h) block)))

theorem measurable_runTailObservationCoordinates :
    Measurable (runTailObservationCoordinates (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h)) :=
  comap_measurable _

theorem measurable_runTail_terminalBlock :
    Measurable (fun observation : RunTailObservation (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) => observation.terminalBlock) :=
  measurable_fst.comp
    measurable_runTailObservationCoordinates

theorem measurable_runTail_terminalEntries :
    Measurable (fun observation : RunTailObservation (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) => observation.terminalEntries) :=
  measurable_fst.comp
    (measurable_snd.comp
      measurable_runTailObservationCoordinates)

theorem measurable_runTail_continuedEntries :
    Measurable (fun observation : RunTailObservation (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) => observation.continuedEntries) :=
  measurable_fst.comp
    (measurable_snd.comp (measurable_snd.comp
      measurable_runTailObservationCoordinates))

theorem measurable_runTail_physicalRoundCodes :
    Measurable (fun observation : RunTailObservation (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) => observation.physicalRoundCodes) :=
  measurable_snd.comp (measurable_snd.comp (measurable_snd.comp
    measurable_runTailObservationCoordinates))

def terminalBlockTraceOfInput (block : Fin (n_boot p))
    (input : BlockInput p rate block C_star C_h) :
    TerminalBlockTrace (p := p) (rate := rate) (C_star := C_star)
      (C_h := C_h) block := by
  let code := actualBlockHandoffCompositionOfInput
    (p := p) (rate := rate) (block := block) (C_star := C_star) (C_h := C_h)
    rewards input
  exact ⟨input.2, C_star, C_h, code.1.rounds.length, code⟩

theorem measurable_terminalBlockTraceOfInput (block : Fin (n_boot p)) :
    Measurable (terminalBlockTraceOfInput (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) (rewards := rewards) block) := by
  apply measurable_comap_iff.mpr
  have hcode := measurable_actualBlockHandoffCompositionOfInput
    (p := p) (rate := rate) (block := block) (C_star := C_star)
    (C_h := C_h) rewards
  have hfold := measurable_fst.comp hcode
  have hcount := (measurable_blockFoldCode_roundCount (p := p) (rate := rate)
    (C_star := C_star) (C_h := C_h) block).comp hfold
  change Measurable (fun input : BlockInput p rate block C_star C_h =>
    (input.2, (C_star, (C_h,
      ((actualBlockHandoffCompositionOfInput rewards input).1.rounds.length,
        actualBlockHandoffCompositionOfInput rewards input)))))
  exact measurable_snd.prodMk
    (measurable_const.prodMk (measurable_const.prodMk (hcount.prodMk hcode)))

def actualSuccessorBlockInput (block : Fin (n_boot p))
    (hnext : block.val + 1 < n_boot p)
    (rewards : GridRewardTable p)
    (input : ActualBlockPrelaunchInput (p := p) (rate := rate) (block := block)
      (C_star := C_star) (C_h := C_h) rewards) :
    BlockInput p rate (successorBlock p block hnext) C_star C_h :=
  (input.1.1, actualEndpointNextCarryOfInput (p := p) (rate := rate)
    (block := block) (C_star := C_star) (C_h := C_h) rewards hnext input)

theorem measurable_actualSuccessorBlockInput (block : Fin (n_boot p))
    (hnext : block.val + 1 < n_boot p) :
    Measurable (actualSuccessorBlockInput (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) block hnext rewards) := by
  exact (measurable_fst.comp measurable_subtype_coe).prodMk
    (measurable_actualEndpointNextCarryOfInput (p := p) (rate := rate)
      (block := block) (C_star := C_star) (C_h := C_h) rewards hnext)

def continuedBlockTraceOfPrelaunch (block : Fin (n_boot p))
    (hnext : block.val + 1 < n_boot p)
    (rewards : GridRewardTable p)
    (input : ActualBlockPrelaunchInput (p := p) (rate := rate) (block := block)
      (C_star := C_star) (C_h := C_h) rewards) :
    ContinuedBlockTrace (p := p) (rate := rate) (C_star := C_star)
      (C_h := C_h) block := by
  let nextBlock := successorBlock p block hnext
  let nextCarry := actualEndpointNextCarryOfInput (p := p) (rate := rate)
    (block := block) (C_star := C_star) (C_h := C_h) rewards hnext input
  let code := actualBlockHandoffCompositionOfInput (p := p) (rate := rate)
    (block := block) (C_star := C_star) (C_h := C_h) rewards input.1
  exact ⟨input.1.2, nextBlock, ⟨nextBlock, nextCarry⟩, code⟩

theorem measurable_continuedBlockTraceOfPrelaunch (block : Fin (n_boot p))
    (hnext : block.val + 1 < n_boot p) :
    Measurable (continuedBlockTraceOfPrelaunch (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) block hnext rewards) := by
  apply measurable_comap_iff.mpr
  have hcoerce : Measurable (fun input : ActualBlockPrelaunchInput
      (p := p) (rate := rate) (block := block) (C_star := C_star)
      (C_h := C_h) rewards => (input : BlockInput p rate block C_star C_h)) :=
    measurable_subtype_coe
  have hcarry : Measurable (fun input : ActualBlockPrelaunchInput
      (p := p) (rate := rate) (block := block) (C_star := C_star)
      (C_h := C_h) rewards => input.1.2) :=
    measurable_snd.comp hcoerce
  have hnextCarry := measurable_actualEndpointNextCarryOfInput
    (p := p) (rate := rate) (block := block) (C_star := C_star)
    (C_h := C_h) rewards hnext
  have hnextCode : Measurable (fun input : ActualBlockPrelaunchInput
      (p := p) (rate := rate) (block := block) (C_star := C_star)
      (C_h := C_h) rewards =>
        (⟨successorBlock p block hnext,
          actualEndpointNextCarryOfInput (p := p) (rate := rate)
            (block := block) (C_star := C_star) (C_h := C_h) rewards hnext input⟩ :
          Σ next : Fin (n_boot p), FixedConstantsBlockCarry p rate next C_star C_h)) := by
    simpa [Function.comp_def] using
      ((measurable_fixedConstantsCarry_sigmaMk (p := p) (rate := rate)
        (C_star := C_star) (C_h := C_h) (successorBlock p block hnext)).comp
          hnextCarry)
  have hblockCode := (measurable_actualBlockHandoffCompositionOfInput
    (p := p) (rate := rate) (block := block) (C_star := C_star)
    (C_h := C_h) rewards).comp hcoerce
  change Measurable (fun input : ActualBlockPrelaunchInput
      (p := p) (rate := rate) (block := block) (C_star := C_star)
      (C_h := C_h) rewards =>
    (input.1.2, (successorBlock p block hnext,
      ((⟨successorBlock p block hnext,
        actualEndpointNextCarryOfInput (p := p) (rate := rate)
          (block := block) (C_star := C_star) (C_h := C_h) rewards hnext input⟩ :
        Σ next : Fin (n_boot p), FixedConstantsBlockCarry p rate next C_star C_h),
        actualBlockHandoffCompositionOfInput rewards input.1))))
  exact hcarry.prodMk (measurable_const.prodMk (hnextCode.prodMk hblockCode))

def terminalRunTailObservation (block : Fin (n_boot p))
    (trace : TerminalBlockTrace (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) block) :
    RunTailObservation (p := p) (rate := rate) (C_star := C_star) (C_h := C_h) :=
  { terminalBlock := block
    terminalEntries := fun other =>
      if h : other = block then Sum.inr (⟨block, trace⟩) else Sum.inl ()
    continuedEntries := fun _ => Sum.inl ()
    physicalRoundCodes := fun other cursor =>
      if other = block then blockPhysicalRoundCodeAt (p := p) (rate := rate)
        (C_star := C_star) (C_h := C_h) block trace.blockCode.1 cursor
      else Sum.inl () }

theorem measurable_terminalRunTailObservation (block : Fin (n_boot p)) :
    Measurable (terminalRunTailObservation (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) block) := by
  apply measurable_comap_iff.mpr
  have hterminal : Measurable (fun trace : TerminalBlockTrace
      (p := p) (rate := rate) (C_star := C_star) (C_h := C_h) block =>
        (terminalRunTailObservation (p := p) (rate := rate)
          (C_star := C_star) (C_h := C_h) block trace).terminalEntries) := by
    apply measurable_pi_iff.mpr
    intro other
    by_cases h : other = block
    · subst other
      simpa [terminalRunTailObservation, Function.comp_def] using
        (measurable_inr.comp
          (measurable_terminalBlockTrace_sigmaMk (p := p) (rate := rate)
            (C_star := C_star) (C_h := C_h) block))
    · simp [terminalRunTailObservation, h]
  have hcontinued : Measurable (fun trace : TerminalBlockTrace
      (p := p) (rate := rate) (C_star := C_star) (C_h := C_h) block =>
        (terminalRunTailObservation (p := p) (rate := rate)
          (C_star := C_star) (C_h := C_h) block trace).continuedEntries) :=
    measurable_const
  have hrounds : Measurable (fun trace : TerminalBlockTrace
      (p := p) (rate := rate) (C_star := C_star) (C_h := C_h) block =>
        (terminalRunTailObservation (p := p) (rate := rate)
          (C_star := C_star) (C_h := C_h) block trace).physicalRoundCodes) := by
    have hfoldCode : Measurable (fun trace : TerminalBlockTrace
        (p := p) (rate := rate) (C_star := C_star) (C_h := C_h) block =>
          trace.blockCode.1) :=
      measurable_fst.comp
        (measurable_terminalBlockTrace_code (p := p) (rate := rate)
          (C_star := C_star) (C_h := C_h) block)
    apply measurable_pi_iff.mpr
    intro other
    apply measurable_pi_iff.mpr
    intro cursor
    by_cases h : other = block
    · subst other
      simpa [terminalRunTailObservation, Function.comp_def] using
        (measurable_blockPhysicalRoundCodeAt (p := p) (rate := rate)
          (C_star := C_star) (C_h := C_h) block cursor).comp hfoldCode
    · simp [terminalRunTailObservation, h]
  change Measurable (fun trace =>
    ((terminalRunTailObservation (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) block trace).terminalBlock,
      ((terminalRunTailObservation (p := p) (rate := rate)
        (C_star := C_star) (C_h := C_h) block trace).terminalEntries,
        ((terminalRunTailObservation (p := p) (rate := rate)
          (C_star := C_star) (C_h := C_h) block trace).continuedEntries,
          (terminalRunTailObservation (p := p) (rate := rate)
            (C_star := C_star) (C_h := C_h) block trace).physicalRoundCodes))))
  exact measurable_const.prodMk (hterminal.prodMk (hcontinued.prodMk hrounds))

def continuedRunTailObservation (block : Fin (n_boot p))
    (trace : ContinuedBlockTrace (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) block)
    (tail : RunTailObservation (p := p) (rate := rate) (C_star := C_star)
      (C_h := C_h)) : RunTailObservation (p := p) (rate := rate)
        (C_star := C_star) (C_h := C_h) :=
  { terminalBlock := tail.terminalBlock
    terminalEntries := tail.terminalEntries
    continuedEntries := fun other =>
      if h : other = block then Sum.inr (⟨block, trace⟩) else tail.continuedEntries other
    physicalRoundCodes := fun other cursor =>
      if other = block then blockPhysicalRoundCodeAt (p := p) (rate := rate)
        (C_star := C_star) (C_h := C_h) block trace.blockCode.1 cursor
      else tail.physicalRoundCodes other cursor }

theorem measurable_continuedRunTailObservation (block : Fin (n_boot p)) :
    Measurable (fun pair :
      ContinuedBlockTrace (p := p) (rate := rate) (C_star := C_star)
        (C_h := C_h) block ×
      RunTailObservation (p := p) (rate := rate) (C_star := C_star)
        (C_h := C_h) =>
      continuedRunTailObservation (p := p) (rate := rate) (C_star := C_star)
        (C_h := C_h) block pair.1 pair.2) := by
  apply measurable_comap_iff.mpr
  have hterminalBlock : Measurable (fun pair :
      ContinuedBlockTrace (p := p) (rate := rate) (C_star := C_star)
        (C_h := C_h) block ×
      RunTailObservation (p := p) (rate := rate) (C_star := C_star)
        (C_h := C_h) => pair.2.terminalBlock) :=
    measurable_runTail_terminalBlock.comp measurable_snd
  have hterminalEntries : Measurable (fun pair :
      ContinuedBlockTrace (p := p) (rate := rate) (C_star := C_star)
        (C_h := C_h) block ×
      RunTailObservation (p := p) (rate := rate) (C_star := C_star)
        (C_h := C_h) => pair.2.terminalEntries) :=
    measurable_runTail_terminalEntries.comp measurable_snd
  have hcontinuedEntries : Measurable (fun pair :
      ContinuedBlockTrace (p := p) (rate := rate) (C_star := C_star)
        (C_h := C_h) block ×
      RunTailObservation (p := p) (rate := rate) (C_star := C_star)
        (C_h := C_h) =>
      (continuedRunTailObservation (p := p) (rate := rate) (C_star := C_star)
        (C_h := C_h) block pair.1 pair.2).continuedEntries) := by
    apply measurable_pi_iff.mpr
    intro other
    by_cases h : other = block
    · subst other
      simpa [continuedRunTailObservation, Function.comp_def] using
        ((measurable_inr.comp
          (measurable_continuedBlockTrace_sigmaMk (p := p) (rate := rate)
            (C_star := C_star) (C_h := C_h) block)).comp measurable_fst)
    · simp only [continuedRunTailObservation, dite_eq_right h]
      convert ((measurable_pi_apply other).comp
        (measurable_runTail_continuedEntries.comp measurable_snd)) using 1
      funext pair
      simp [Function.comp_apply]
  have hrounds : Measurable (fun pair :
      ContinuedBlockTrace (p := p) (rate := rate) (C_star := C_star)
        (C_h := C_h) block ×
      RunTailObservation (p := p) (rate := rate) (C_star := C_star)
        (C_h := C_h) =>
      (continuedRunTailObservation (p := p) (rate := rate) (C_star := C_star)
        (C_h := C_h) block pair.1 pair.2).physicalRoundCodes) := by
    apply measurable_pi_iff.mpr
    intro other
    apply measurable_pi_iff.mpr
    intro cursor
    by_cases h : other = block
    · subst other
      simpa [continuedRunTailObservation, Function.comp_def] using
        (measurable_blockPhysicalRoundCodeAt (p := p) (rate := rate)
          (C_star := C_star) (C_h := C_h) block cursor).comp
          (measurable_fst.comp
            ((measurable_continuedBlockTrace_blockCode (p := p) (rate := rate)
              (C_star := C_star) (C_h := C_h) block).comp measurable_fst))
    · simp only [continuedRunTailObservation, ite_eq_right h]
      convert ((measurable_pi_apply cursor).comp
        ((measurable_pi_apply other).comp
          (measurable_runTail_physicalRoundCodes.comp measurable_snd))) using 1
      funext pair
      simp [Function.comp_apply]
  change Measurable (fun pair :
    ContinuedBlockTrace (p := p) (rate := rate) (C_star := C_star)
      (C_h := C_h) block ×
    RunTailObservation (p := p) (rate := rate) (C_star := C_star)
      (C_h := C_h) =>
    ((continuedRunTailObservation (p := p) (rate := rate) (C_star := C_star)
      (C_h := C_h) block pair.1 pair.2).terminalBlock,
      ((continuedRunTailObservation (p := p) (rate := rate) (C_star := C_star)
        (C_h := C_h) block pair.1 pair.2).terminalEntries,
        ((continuedRunTailObservation (p := p) (rate := rate) (C_star := C_star)
          (C_h := C_h) block pair.1 pair.2).continuedEntries,
          (continuedRunTailObservation (p := p) (rate := rate) (C_star := C_star)
            (C_h := C_h) block pair.1 pair.2).physicalRoundCodes))))
  exact hterminalBlock.prodMk (hterminalEntries.prodMk (hcontinuedEntries.prodMk hrounds))

/-- The actual recursion follows the original remaining-block measure
`n_boot p - block.val`.  The zero case cannot occur for an original `Fin`
block; every positive step either stores the actual terminal block or uses
P's real no-launch successor subtype. -/
private noncomputable def actualRunTailObservationAux :
    (fuel : ℕ) → (block : Fin (n_boot p)) →
      n_boot p - block.val = fuel →
      BlockInput p rate block C_star C_h →
        RunTailObservation (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
  | 0, block, hmeasure, _input => by
      have hblock := block.isLt
      omega
  | fuel + 1, block, hmeasure, input => by
      by_cases hnext : block.val + 1 < n_boot p
      · let next := successorBlock p block hnext
        have hmeasureNext : n_boot p - next.val = fuel := by
          simp [next, successorBlock]
          omega
        by_cases hpre : input ∈ actualBlockPrelaunchSet
            (p := p) (rate := rate) (block := block) (C_star := C_star)
            (C_h := C_h) rewards
        · let preinput : ActualBlockPrelaunchInput (p := p) (rate := rate)
              (block := block) (C_star := C_star) (C_h := C_h) rewards :=
              ⟨input, hpre⟩
          exact continuedRunTailObservation (p := p) (rate := rate)
            (C_star := C_star) (C_h := C_h) block
            (continuedBlockTraceOfPrelaunch (p := p) (rate := rate)
              (C_star := C_star) (C_h := C_h) block hnext rewards preinput)
            (actualRunTailObservationAux fuel next hmeasureNext
              (actualSuccessorBlockInput (p := p) (rate := rate)
                (C_star := C_star) (C_h := C_h) block hnext rewards preinput))
        · exact terminalRunTailObservation (p := p) (rate := rate)
            (C_star := C_star) (C_h := C_h) block
            (terminalBlockTraceOfInput (p := p) (rate := rate)
              (C_star := C_star) (C_h := C_h) (rewards := rewards) block input)
      · exact terminalRunTailObservation (p := p) (rate := rate)
          (C_star := C_star) (C_h := C_h) block
          (terminalBlockTraceOfInput (p := p) (rate := rate)
            (C_star := C_star) (C_h := C_h) (rewards := rewards) block input)
termination_by fuel block hmeasure input => n_boot p - block.val
decreasing_by omega

private theorem measurable_actualRunTailObservationAux (fuel : ℕ) :
    ∀ (block : Fin (n_boot p)) (hmeasure : n_boot p - block.val = fuel),
      Measurable (fun input : BlockInput p rate block C_star C_h =>
        actualRunTailObservationAux (p := p) (rate := rate) (C_star := C_star)
          (C_h := C_h) (rewards := rewards) fuel block hmeasure input) := by
  classical
  induction fuel with
  | zero =>
      intro block hmeasure
      have hblock := block.isLt
      omega
  | succ fuel ih =>
      intro block hmeasure
      by_cases hnext : block.val + 1 < n_boot p
      · let next := successorBlock p block hnext
        have hmeasureNext : n_boot p - next.val = fuel := by
          simp [next, successorBlock]
          omega
        let preSet := actualBlockPrelaunchSet (p := p) (rate := rate)
          (block := block) (C_star := C_star) (C_h := C_h) rewards
        have hpreSet : MeasurableSet preSet := by
          exact measurableSet_actualBlockPrelaunchSet (p := p) (rate := rate)
            (block := block) (C_star := C_star) (C_h := C_h) rewards
        have hcontinueTrace : Measurable (continuedBlockTraceOfPrelaunch
            (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
            block hnext rewards) :=
          measurable_continuedBlockTraceOfPrelaunch (p := p) (rate := rate)
            (C_star := C_star) (C_h := C_h) block hnext
        have hnextInput : Measurable (actualSuccessorBlockInput
            (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
            block hnext rewards) :=
          measurable_actualSuccessorBlockInput (p := p) (rate := rate)
            (C_star := C_star) (C_h := C_h) block hnext
        have htail : Measurable (fun input : ActualBlockPrelaunchInput
            (p := p) (rate := rate) (block := block) (C_star := C_star)
            (C_h := C_h) rewards =>
              actualRunTailObservationAux (p := p) (rate := rate)
                (C_star := C_star) (C_h := C_h) (rewards := rewards)
                fuel next hmeasureNext
                (actualSuccessorBlockInput (p := p) (rate := rate)
                  (C_star := C_star) (C_h := C_h) block hnext rewards input)) :=
          (ih next hmeasureNext).comp hnextInput
        have hcontinue : Measurable (fun input : ActualBlockPrelaunchInput
            (p := p) (rate := rate) (block := block) (C_star := C_star)
            (C_h := C_h) rewards =>
              continuedRunTailObservation (p := p) (rate := rate)
                (C_star := C_star) (C_h := C_h) block
                (continuedBlockTraceOfPrelaunch (p := p) (rate := rate)
                  (C_star := C_star) (C_h := C_h) block hnext rewards input)
                (actualRunTailObservationAux (p := p) (rate := rate)
                  (C_star := C_star) (C_h := C_h) (rewards := rewards)
                  fuel next hmeasureNext
                  (actualSuccessorBlockInput (p := p) (rate := rate)
                    (C_star := C_star) (C_h := C_h) block hnext rewards input))) :=
          (measurable_continuedRunTailObservation (p := p) (rate := rate)
            (C_star := C_star) (C_h := C_h) block).comp
              (hcontinueTrace.prodMk htail)
        have hstop : Measurable (fun input : ({x : BlockInput p rate block C_star C_h //
            x ∉ preSet}) =>
              terminalRunTailObservation (p := p) (rate := rate)
                (C_star := C_star) (C_h := C_h) block
                (terminalBlockTraceOfInput (p := p) (rate := rate)
                  (C_star := C_star) (C_h := C_h) (rewards := rewards) block input.1)) :=
          (measurable_terminalRunTailObservation (p := p) (rate := rate)
            (C_star := C_star) (C_h := C_h) block).comp
              ((measurable_terminalBlockTraceOfInput (p := p) (rate := rate)
                (C_star := C_star) (C_h := C_h) (rewards := rewards) block).comp
                  measurable_subtype_coe)
        simp only [actualRunTailObservationAux, dif_pos hnext]
        exact Measurable.dite hcontinue hstop hpreSet
      · simp only [actualRunTailObservationAux, dif_neg hnext]
        convert (measurable_terminalRunTailObservation (p := p) (rate := rate)
          (C_star := C_star) (C_h := C_h) block).comp
            (measurable_terminalBlockTraceOfInput (p := p) (rate := rate)
              (C_star := C_star) (C_h := C_h) (rewards := rewards) block) using 1
        funext input
        rfl

/-- The actual `H.runFrom` input is observed jointly in the whole original
source and the existing fixed-constant continuous carry. -/
private def runFromObservation (block : Fin (n_boot p))
    (input : BlockInput p rate block C_star C_h) :
    RunFromObservation (p := p) (rate := rate) (C_star := C_star)
      (C_h := C_h) block :=
  ⟨input.1, input.2,
    actualRunTailObservationAux (p := p) (rate := rate) (C_star := C_star)
      (C_h := C_h) (rewards := rewards) (n_boot p - block.val) block rfl input⟩

/-- Joint Borel measurability of the literal finite-block observation. -/
private theorem runFrom_observation_measurable (block : Fin (n_boot p)) :
    Measurable (fun input : BlockInput p rate block C_star C_h =>
      runFromObservation (p := p) (rate := rate) (C_star := C_star)
        (C_h := C_h) (rewards := rewards) block input) := by
  apply measurable_comap_iff.mpr
  have htail := measurable_actualRunTailObservationAux (p := p) (rate := rate)
    (C_star := C_star) (C_h := C_h) (rewards := rewards)
    (n_boot p - block.val) block rfl
  change Measurable (fun input : BlockInput p rate block C_star C_h =>
    (input.1, (input.2,
      actualRunTailObservationAux (p := p) (rate := rate) (C_star := C_star)
        (C_h := C_h) (rewards := rewards) (n_boot p - block.val) block rfl input)))
  simpa [Function.comp_def] using
    (measurable_fst.prodMk (measurable_snd.prodMk htail))

/-- The source-initialized observation starts with the exact `R.initialCarry`
in the existing fixed-constant carry subtype. -/
private def sourceInitializedRunObservation
    (source : BootstrapPrivateRoundStreams.SourceInput p) :
    RunFromObservation (p := p) (rate := rate) (C_star := C_star)
      (C_h := C_h) (ActualInitializationRun.firstBlock p) :=
  runFromObservation (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
    (rewards := rewards) (ActualInitializationRun.firstBlock p)
    (source, ⟨ActualInitializationRun.initialCarry p rate C_star C_h, rfl, rfl⟩)

/-- The initialized observation stores the same original source and exact
initial carry consumed by `H.sourceInitializedRun`. -/
private theorem sourceInitializedRunObservation_input_coordinates
    (source : BootstrapPrivateRoundStreams.SourceInput p) :
    let observation := sourceInitializedRunObservation (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) (rewards := rewards) source
    observation.originalSource = source ∧
      observation.initialCarry.1 = ActualInitializationRun.initialCarry p rate C_star C_h := by
  simp [sourceInitializedRunObservation, runFromObservation]

/-- The source-initialized finite-block observation is Borel in the whole
original source, from the constant `R.initialCarry`. -/
private theorem sourceInitializedRun_observation_measurable :
    Measurable (sourceInitializedRunObservation (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) (rewards := rewards)) := by
  let initial : FixedConstantsBlockCarry p rate (ActualInitializationRun.firstBlock p)
      C_star C_h :=
    ⟨ActualInitializationRun.initialCarry p rate C_star C_h, rfl, rfl⟩
  have hinput : Measurable (fun source : BootstrapPrivateRoundStreams.SourceInput p =>
      (source, initial)) := measurable_id.prodMk measurable_const
  change Measurable (fun source => runFromObservation (p := p) (rate := rate)
    (C_star := C_star) (C_h := C_h) (rewards := rewards)
    (ActualInitializationRun.firstBlock p) (source, initial))
  exact (runFrom_observation_measurable (p := p) (rate := rate) (C_star := C_star)
    (C_h := C_h) (rewards := rewards) (ActualInitializationRun.firstBlock p)).comp hinput

/-- Fixing a published output leaves the complete original extended private
coordinate, including the accepted private arrays and coordinator `J`, as the
section variable. -/
private def fixedPublicPrivateSourceInitializedRunObservation
    (published : CompletePublicTable.PublishedOutput p)
    (privateCoordinates : BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p) :=
  sourceInitializedRunObservation (p := p) (rate := rate) (C_star := C_star)
    (C_h := C_h) (rewards := rewards) (published, privateCoordinates)

/-- The fixed-public section remains Borel in the full original extended
private coordinate. This is a section result and asserts no selected-row
factorization of actual outputs. -/
private theorem fixedPublicPrivateSourceInitializedRunObservation_measurable
    (published : CompletePublicTable.PublishedOutput p) :
    Measurable (fixedPublicPrivateSourceInitializedRunObservation (p := p)
      (rate := rate) (C_star := C_star) (C_h := C_h) (rewards := rewards) published) := by
  exact (sourceInitializedRun_observation_measurable (p := p) (rate := rate)
    (C_star := C_star) (C_h := C_h) (rewards := rewards)).comp
      (measurable_const.prodMk measurable_id)

/-- Assemble one varying selected complete row with fixed IDs and all other
row coordinates. The full published output remains the input to actual play. -/
private def variableSelectedPublishedOutput
    (ids : CompletePublicTable.IDArray p)
    (rows : CompletePublicTable.CompleteRows p)
    (selectedIndex : Fin (M p))
    (selectedRow : CompletePublicTable.CompleteRow p) :
    CompletePublicTable.PublishedOutput p :=
  (ids, fun i => if i = selectedIndex then selectedRow else rows i)

/-- Joint Borel section in the selected complete row and the full extended
private array/J coordinate, with IDs, other rows, and index fixed. The actual
tests may still read any of the fixed other rows. -/
private theorem variableSelectedRowPrivateSourceInitializedRunObservation_measurable
    (ids : CompletePublicTable.IDArray p)
    (rows : CompletePublicTable.CompleteRows p)
    (selectedIndex : Fin (M p)) :
    Measurable (fun pair : CompletePublicTable.CompleteRow p ×
        BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p =>
      sourceInitializedRunObservation (p := p) (rate := rate) (C_star := C_star)
        (C_h := C_h) (rewards := rewards)
        (variableSelectedPublishedOutput (p := p) ids rows selectedIndex pair.1, pair.2)) := by
  have hrows : Measurable (fun pair : CompletePublicTable.CompleteRow p ×
      BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p =>
        fun i : Fin (M p) =>
          if i = selectedIndex then pair.1 else rows i) := by
    apply measurable_pi_iff.mpr
    intro i
    by_cases h : i = selectedIndex
    · subst i
      simpa using (measurable_fst : Measurable
        (fun pair : CompletePublicTable.CompleteRow p ×
          BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p => pair.1))
    · simpa [h] using (measurable_const : Measurable
        (fun _ : CompletePublicTable.CompleteRow p ×
          BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p => rows i))
  have hpublished : Measurable (fun pair : CompletePublicTable.CompleteRow p ×
      BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p =>
        variableSelectedPublishedOutput (p := p) ids rows selectedIndex pair.1) := by
    change Measurable (fun pair : CompletePublicTable.CompleteRow p ×
        BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p =>
      (ids, fun i : Fin (M p) =>
        if i = selectedIndex then pair.1 else rows i))
    exact measurable_const.prodMk hrows
  have hsource : Measurable (fun pair : CompletePublicTable.CompleteRow p ×
      BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p =>
        (variableSelectedPublishedOutput (p := p) ids rows selectedIndex pair.1, pair.2)) :=
    hpublished.prodMk measurable_snd
  exact (sourceInitializedRun_observation_measurable (p := p) (rate := rate)
    (C_star := C_star) (C_h := C_h) (rewards := rewards)).comp hsource

/-- The stored block code decodes, through E's accepted stored-round
restoration, to the very `R.foldBlock` represented by the same input. -/
theorem terminalBlockTraceOfInput_reconstructs_fold (rewards : GridRewardTable p)
    (block : Fin (n_boot p))
    (input : BlockInput p rate block C_star C_h) :
    decodeBlockFoldCodeOfInput (p := p) (rate := rate) (block := block)
      (C_star := C_star) (C_h := C_h) rewards input
        (terminalBlockTraceOfInput (p := p) (rate := rate) (C_star := C_star)
          (C_h := C_h) (rewards := rewards) block input).blockCode.1 =
      some (ActualInitializationRun.foldBlock p rate block input.1 rewards input.2.1) := by
  change decodeBlockFoldCodeOfInput (p := p) (rate := rate) (block := block)
      (C_star := C_star) (C_h := C_h) rewards input
        (physicalBlockFoldCodeOfInput rewards input) =
      some (ActualInitializationRun.foldBlock p rate block input.1 rewards input.2.1)
  rw [physicalBlockFoldCodeOfInput_eq_actualBlockFoldCodeOfInput]
  exact decodeBlockFoldCodeOfInput_actual rewards input

/-- The stored C observation reconstructs the actual combined handoff on the
same source, carry, reward grid, and physical fold.  Its phase and successor
payload therefore retain the real launch/continue/exhaustion disposition. -/
theorem terminalBlockTraceOfInput_reconstructs_handoff (rewards : GridRewardTable p)
    (block : Fin (n_boot p))
    (input : BlockInput p rate block C_star C_h) :
    combinedBoundaryHandoffOfObservation
        (terminalBlockTraceOfInput (p := p) (rate := rate) (C_star := C_star)
          (C_h := C_h) (rewards := rewards) block input).blockCode.2 =
      combinedBoundaryHandoff p rate block input.1 rewards C_star C_h
        (actualBlockFoldOfInput (p := p) (rate := rate) (block := block)
          (C_star := C_star) (C_h := C_h) rewards input) := by
  change combinedBoundaryHandoffOfObservation
      (actualBlockHandoffCompositionOfInput (p := p) (rate := rate)
        (block := block) (C_star := C_star) (C_h := C_h) rewards input).2 = _
  exact actualBlockHandoffComposition_reconstructs_actual rewards input

/-- The full chronological physical-round codes retained for one actual
block.  Each element is E's complete same-input preparation, observation,
and `RoundResult` code, including its original error/success tag. -/
def terminalBlockChronologicalRoundCodes {block : Fin (n_boot p)}
    (trace : TerminalBlockTrace (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) block) :=
  trace.blockCode.1.rounds

/-- The named chronological action projection of the retained full round
codes. -/
def terminalBlockActionFeedbackHistory {block : Fin (n_boot p)}
    (trace : TerminalBlockTrace
    (p := p) (rate := rate) (C_star := C_star) (C_h := C_h) block) :=
  (trace.blockCode.1.actions, trace.blockCode.1.feedback)

/-- A player's own action/feedback history projected from those same full
round codes. -/
def terminalBlockOwnHistory {block : Fin (n_boot p)}
    (trace : TerminalBlockTrace
    (p := p) (rate := rate) (C_star := C_star) (C_h := C_h) block)
    (player : Fin p.m) :=
  trace.blockCode.1.rounds.map fun code =>
    ActualInitializationStepMeasurability.physicalOwnEntryFromActualRoundOutput
      rate block code player

/-- The terminal trace's retained code is the ordered physical encoding of
the exact records returned by this block's `R.foldBlock`. -/
theorem terminalBlockChronologicalRoundCodes_eq_physicalRecords
    {block : Fin (n_boot p)}
    (trace : TerminalBlockTrace (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) block)
    (rewards : GridRewardTable p)
    (input : BlockInput p rate block C_star C_h)
    (htrace : trace = terminalBlockTraceOfInput (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) (rewards := rewards) block input) :
    terminalBlockChronologicalRoundCodes (p := p) (rate := rate)
        (C_star := C_star) (C_h := C_h) trace =
      ActualInitializationBlockFoldExact.physicalRoundCodes C_star C_h
        (ActualInitializationRun.foldBlock p rate block input.1 rewards input.2.1).records
        (ActualInitializationBlockFoldExact.foldBlock_records_block
          input.1 rewards input.2.1) := by
  subst trace
  exact actualBlockHandoffComposition_rounds_eq_physicalRoundCodes rewards input

/-- The complete action and denominator-`D` feedback histories are projected
from the same stored physical records, preserving each per-round tag. -/
theorem terminalBlockActionFeedbackHistory_eq_physicalRecords
    {block : Fin (n_boot p)}
    (rewards : GridRewardTable p)
    (input : BlockInput p rate block C_star C_h) :
    terminalBlockActionFeedbackHistory (p := p) (rate := rate)
        (C_star := C_star) (C_h := C_h)
        (terminalBlockTraceOfInput (p := p) (rate := rate)
          (C_star := C_star) (C_h := C_h) (rewards := rewards) block input) =
      ((PhysicalRoundRecord.actions
          (ActualInitializationRun.foldBlock p rate block input.1 rewards input.2.1).records).map
          Sum.inr,
        (PhysicalRoundRecord.feedback
          (ActualInitializationRun.foldBlock p rate block input.1 rewards input.2.1).records).map
          Sum.inr) := by
  change ((actualBlockHandoffCompositionOfInput rewards input).1.actions,
      (actualBlockHandoffCompositionOfInput rewards input).1.feedback) = _
  rcases actualBlockHandoffComposition_actions_feedback rewards input with ⟨ha, hf⟩
  exact Prod.ext ha hf

/-- Each named per-player history is the exact action/feedback projection of
the same actual chronological `R.foldBlock` records. -/
theorem terminalBlockOwnHistory_eq_physicalRecords
    {block : Fin (n_boot p)}
    (rewards : GridRewardTable p)
    (input : BlockInput p rate block C_star C_h) (player : Fin p.m) :
    terminalBlockOwnHistory (p := p) (rate := rate) (C_star := C_star)
        (C_h := C_h)
        (terminalBlockTraceOfInput (p := p) (rate := rate)
          (C_star := C_star) (C_h := C_h) (rewards := rewards) block input) player =
      (ActualInitializationRun.foldBlock p rate block input.1 rewards input.2.1).records.map
        (fun record => Sum.inr
          (record.result.actions player, record.result.feedback player)) := by
  exact actualBlockHandoffComposition_own_entries rewards input player

/-- The consumed cursor in the terminal trace is exactly the existing fold's
consumed count and hence the actual clipped block length. -/
theorem terminalBlockTraceOfInput_consumed_eq_fold (rewards : GridRewardTable p)
    {block : Fin (n_boot p)}
    (input : BlockInput p rate block C_star C_h) :
    (terminalBlockTraceOfInput (p := p) (rate := rate) (C_star := C_star)
      (C_h := C_h) (rewards := rewards) block input).consumed =
        (ActualInitializationRun.foldBlock p rate block input.1 rewards input.2.1).consumed := by
  let folded := ActualInitializationRun.foldBlock p rate block input.1 rewards input.2.1
  have hlen : folded.records.length = folded.consumed := by
    simpa using folded.record_count
  change (physicalBlockFoldCodeOfInput rewards input).rounds.length = folded.consumed
  rw [physicalBlockFoldCodeOfInput_eq_actualBlockFoldCodeOfInput,
    actualBlockFoldCodeOfInput_rounds_eq_physicalRoundCodes]
  simpa [ActualInitializationBlockFoldExact.physicalRoundCodes] using hlen

/-- Both constants and the incoming carry stored in a terminal trace are the
same coordinates supplied to the original actual block input. -/
theorem terminalBlockTraceOfInput_input_coordinates (rewards : GridRewardTable p)
    {block : Fin (n_boot p)}
    (input : BlockInput p rate block C_star C_h) :
    let trace := terminalBlockTraceOfInput (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) (rewards := rewards) block input
    trace.carry = input.2 ∧ trace.terminalC_star = C_star ∧ trace.terminalC_h = C_h := by
  simp [terminalBlockTraceOfInput]

/-- On the accepted no-launch subtype and with a real successor, P's carried
coordinate is exactly H's `continueNext` branch, including both constants. -/
theorem actualPrelaunchInput_handoff_continueNext
    {block : Fin (n_boot p)}
    (hnext : block.val + 1 < n_boot p)
    (input : ActualBlockPrelaunchInput (p := p) (rate := rate) (block := block)
      (C_star := C_star) (C_h := C_h) rewards) :
    ∃ next carry,
      (ActualInitializationRun.combinedBoundaryHandoff p rate block input.1.1 rewards
        C_star C_h (actualBlockFoldOfInput rewards input.1)).disposition =
          .continueNext next carry ∧
      next = successorBlock p block hnext ∧
      HEq carry (actualEndpointNextCarryOfInput rewards hnext input).1 ∧
      carry.C_star = C_star ∧ carry.C_h = C_h := by
  let handoff := ActualInitializationRun.combinedBoundaryHandoff p rate block input.1.1
    rewards C_star C_h (actualBlockFoldOfInput rewards input.1)
  cases hdisp : handoff.disposition with
  | continueNext next carry =>
      have h := actualEndpointNextCarryOfInput_eq_actual_continueNext rewards hnext input
      simp only [handoff, hdisp] at h
      exact ⟨next, carry, by simpa [handoff] using hdisp,
        h.1, h.2.1, h.2.2.1, h.2.2.2⟩
  | launched launch seed =>
      have h := actualEndpointNextCarryOfInput_eq_actual_continueNext rewards hnext input
      simp only [handoff, hdisp] at h
  | exhausted live =>
      have h := actualEndpointNextCarryOfInput_eq_actual_continueNext rewards hnext input
      simp only [handoff, hdisp] at h

/-- The accepted no-launch slice is exactly the `continueNext` branch of the
same actual combined handoff whenever a real successor block exists. -/
theorem actualBlockPrelaunchSet_iff_handoff_continueNext
    {block : Fin (n_boot p)}
    (hnext : block.val + 1 < n_boot p)
    (input : BlockInput p rate block C_star C_h) :
    input ∈ actualBlockPrelaunchSet (p := p) (rate := rate) (block := block)
        (C_star := C_star) (C_h := C_h) rewards ↔
      ∃ next carry,
        (combinedBoundaryHandoff p rate block input.1 rewards C_star C_h
          (actualBlockFoldOfInput rewards input)).disposition = .continueNext next carry := by
  constructor
  · intro hpre
    let preinput : ActualBlockPrelaunchInput (p := p) (rate := rate)
        (block := block) (C_star := C_star) (C_h := C_h) rewards := ⟨input, hpre⟩
    obtain ⟨next, carry, hdisp, _, _, _, _⟩ :=
      actualPrelaunchInput_handoff_continueNext (p := p) (rate := rate)
        (C_star := C_star) (C_h := C_h) (rewards := rewards) hnext preinput
    exact ⟨next, carry, hdisp⟩
  · rintro ⟨next, carry, hdisp⟩
    have hfacts := combinedBoundaryHandoff_continueNext_facts
      (actualBlockFoldOfInput rewards input) next carry hdisp
    rcases hfacts.2.2.2 with ⟨live, hphase, _, _, _⟩
    change physicalBlockEndpointInputOfInput rewards input ∈
      ActualInitializationCombinedBoundaryMeasurability.endpointPrelaunchSet
        p rate block C_star C_h
    rw [physicalBlockEndpointInputOfInput_eq_endpointInputOfBlockFold rewards input]
    simp [ActualInitializationCombinedBoundaryMeasurability.endpointPrelaunchSet,
      ActualInitializationCombinedBoundaryMeasurability.endpointInputOfBlockFold,
      ActualInitializationBlockMeasurability.continuationCodeOf, hphase]

/-- The source-and-carry handoff used by P is H's exact original handoff,
after the two equalities in B's existing fixed-constant carry subtype. -/
theorem actualBlockHandoffOfInput_eq_runFromInput
    {block : Fin (n_boot p)}
    (input : BlockInput p rate block C_star C_h) :
    combinedBoundaryHandoff p rate block input.1 rewards C_star C_h
        (actualBlockFoldOfInput rewards input) =
      ActualInitializationRun.combinedBoundaryHandoff p rate block input.1 rewards
        input.2.1.C_star input.2.1.C_h
        (ActualInitializationRun.foldBlock p rate block input.1 rewards input.2.1) := by
  rcases input with ⟨source, ⟨carry, hC_star, hC_h⟩⟩
  cases hC_star
  cases hC_h
  rfl

/-- The accepted no-launch slice is exactly the prelaunch constructor of
E's continuation code for the same source-and-carry fold. -/
theorem actualBlockPrelaunchSet_iff_foldPhasePrelaunch
    {block : Fin (n_boot p)}
    (input : BlockInput p rate block C_star C_h) :
    input ∈ actualBlockPrelaunchSet (p := p) (rate := rate) (block := block)
        (C_star := C_star) (C_h := C_h) rewards ↔
      ∃ live : BootstrapCoordinatorLocalRound.PrelaunchBlock p,
        (actualBlockFoldOfInput rewards input).phase = .prelaunch live := by
  constructor
  · intro hpre
    have hendpointTag := hpre
    change (physicalBlockEndpointInputOfInput rewards input).1.2.1.2.2.2.2 = none
      at hendpointTag
    rw [physicalBlockEndpointInputOfInput_eq_endpointInputOfBlockFold rewards input]
      at hendpointTag
    have hphaseTag :
        (ActualInitializationBlockMeasurability.continuationCodeOf
          (actualBlockFoldOfInput rewards input).phase).2.2.2.2 = none := by
      simpa [ActualInitializationCombinedBoundaryMeasurability.endpointInputOfBlockFold]
        using hendpointTag
    cases hphase : (actualBlockFoldOfInput rewards input).phase with
    | launched launch =>
        simp [ActualInitializationBlockMeasurability.continuationCodeOf, hphase] at hphaseTag
    | prelaunch live => exact ⟨live, rfl⟩
  · rintro ⟨live, hphase⟩
    change physicalBlockEndpointInputOfInput rewards input ∈
      ActualInitializationCombinedBoundaryMeasurability.endpointPrelaunchSet
        p rate block C_star C_h
    rw [physicalBlockEndpointInputOfInput_eq_endpointInputOfBlockFold rewards input]
    simp [ActualInitializationCombinedBoundaryMeasurability.endpointPrelaunchSet,
      ActualInitializationCombinedBoundaryMeasurability.endpointInputOfBlockFold,
      ActualInitializationBlockMeasurability.continuationCodeOf, hphase]

/-- The continuation phase of P's reindexed fold is the phase of the exact
original `R.foldBlock` input supplied to H. -/
theorem actualBlockFoldOfInput_phase_eq_runFromInput
    {block : Fin (n_boot p)}
    (input : BlockInput p rate block C_star C_h) :
    (actualBlockFoldOfInput rewards input).phase =
      (ActualInitializationRun.foldBlock p rate block input.1 rewards input.2.1).phase := by
  rcases input with ⟨source, ⟨carry, hC_star, hC_h⟩⟩
  cases hC_star
  cases hC_h
  rfl


end Bandits.Support.ActualInitializationHorizonMeasurability
