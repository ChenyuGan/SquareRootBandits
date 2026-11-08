/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ActualInitializationTerminalReadout

/-!
# Actual terminal follower carry codes

The terminal readout retains the follower codes and the unchecked boundary
outputs in the full combined observation.  On an arbitrary value of that raw
observation, those coordinates are independent apart from the checked to
unchecked output agreement.  This module proves their additional relation on
the actual terminal image, then transports the retained carry codes to the
followers of the same source-initialized run.

The code measurability theorem uses the existing dependent terminal block
sum and the existing product of follower carry code spaces.  The source,
whole reward table, common real constants, private coordinates, saved-real
fibres, and ordinary/dagger configurations are unchanged.

Mathematical evidence: `sources/zip4/manuscript/07_public_setup.tex:55-114`,
`sources/zip4/manuscript/appendix_b_communication.tex:94-131`,
`sources/zip4/manuscript/06_interruptions.tex:240-296`,
`sources/zip4/manuscript/appendix_a_local_protocol.tex:6-14`, and
`sources/zip4/manuscript/08_main_theorem.tex:67-75`.

These are internal actual-producer identities and a readout measurability
result.  They do not establish the next-block launch input, suffix iteration,
whole-history measurability, source laws, safety, or regret comparison.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.ActiveFollowerDownAcceptance
open Bandits.Support.ActualInitializationRun
open Bandits.Support.ActualInitializationHorizon
open Bandits.Support.ActualInitializationHorizonMeasurability
open Bandits.Support.ActualInitializationHorizonObservation
open Bandits.Support.ActualInitializationCombinedBoundaryMeasurability
open Bandits.Support.ActualInitializationBlockMeasurability
open Bandits.Support.ActualInitializationFollowerBoundaryMeasurability
open Bandits.Support.ActualInitializationTerminalReadout

namespace Bandits.Support.ActualInitializationTerminalCarryHandoff

abbrev Parameters := ActualInitializationTerminalReadout.Parameters
abbrev RateInput := ActualInitializationTerminalReadout.RateInput
abbrev GridRewardTable := ActualInitializationTerminalReadout.GridRewardTable
abbrev SourceInput (p : Parameters) := ActualInitializationTerminalReadout.SourceInput p

variable {p : Parameters} {rate : RateInput p} {C_star C_h : ℝ}
  {rewards : GridRewardTable p}

private def terminalDataFollowerOutputs
    {source : SourceInput p}
    (data : Sigma (fun terminal : Fin (n_boot p) =>
      Sigma (fun star : ℝ => Sigma (fun ch : ℝ =>
        ActualInitializationRun.BlockFoldOutput p rate terminal source rewards star ch 0 ×
          ActualInitializationRun.CombinedBoundaryHandoff p rate terminal source ×
            ActualInitializationRun.BoundaryDisposition p rate terminal)))) :
    Fin (p.m - 1) → ActualInitializationPhysicalStep.BoundaryFollowerOutput p rate :=
  fun i => data.2.2.2.2.1.followers i

/-- On the terminal trace actually extracted from the initialized run, the
unchecked output is the output constructed from that observation's retained
follower code.  This is an image identity: it is not asserted for arbitrary
raw combined observations. -/
theorem sourceInitializedTerminalTrace_uncheckedOutput_eq_codeOutput
    (source : SourceInput p) :
    let trace := ActualInitializationTerminalReadout.sourceInitializedTerminalTrace
      (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
      (rewards := rewards) source
    let observation := trace.2.blockCode.2
    ∀ i : Fin (p.m - 1),
      observation.uncheckedBoundaryOutputs i =
        ActualInitializationFollowerBoundaryMeasurability.boundaryOutputFromFollowerCode
          p rate trace.1 (observation.followerCodes i) := by
  dsimp only
  rcases ActualInitializationTerminalReadout.sourceInitializedTerminalTrace_reconstruction
      (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
      (rewards := rewards) source with ⟨terminal, carry, htrace⟩
  intro i
  rw [htrace]
  rfl

/-- The handoff decoded from the retained terminal combined observation is
the terminal handoff of the same actual source-initialized run.  The terminal
index, reached carry, original source, and common constants come from T's full
terminal reconstruction and terminal-data equality. -/
theorem sourceInitializedTerminalObservation_handoff_eq_actual
    (source : SourceInput p) :
    ∀ i : Fin (p.m - 1),
      (ActualInitializationCombinedBoundaryMeasurability.combinedBoundaryHandoffOfObservation
        ((ActualInitializationTerminalReadout.sourceInitializedTerminalTrace
        (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
        (rewards := rewards) source).2.blockCode.2)).followers i =
        (ActualInitializationHorizon.sourceInitializedRun p rate source rewards C_star C_h).terminalHandoff.followers i := by
  let run := ActualInitializationHorizon.sourceInitializedRun p rate source rewards C_star C_h
  let trace := ActualInitializationTerminalReadout.sourceInitializedTerminalTrace
    (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
    (rewards := rewards) source
  let observation := trace.2.blockCode.2
  rcases ActualInitializationTerminalReadout.sourceInitializedTerminalTrace_full_reconstruction
      (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
      (rewards := rewards) source with
    ⟨terminal, carry, htrace, _horiginalSource, _hinitialCarry, _hterminal,
      _hstar, _hch, _hconsumed, _hfold, hdata⟩
  have hdataFollowers := congrArg
    (terminalDataFollowerOutputs (p := p) (rate := rate) (source := source)
      (rewards := rewards)) hdata
  have htraceFollowers := congrArg
    (fun entry : ActualInitializationTerminalReadout.StoredTrace p rate C_star C_h =>
      fun i => (combinedBoundaryHandoffOfObservation entry.2.blockCode.2).followers i) htrace
  have htraceFollowers' :
      (fun i => (combinedBoundaryHandoffOfObservation observation).followers i) =
        fun i => (combinedBoundaryHandoffOfObservation
          (ActualInitializationHorizonMeasurability.terminalBlockTraceOfInput
            (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
            (rewards := rewards) terminal (source, carry)).blockCode.2).followers i := by
    simpa [trace, observation] using htraceFollowers
  have hdataFollowers' :
      (fun i => run.terminalHandoff.followers i) =
        fun i => (combinedBoundaryHandoffOfObservation
          (ActualInitializationHorizonMeasurability.terminalBlockTraceOfInput
            (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
            (rewards := rewards) terminal (source, carry)).blockCode.2).followers i := by
    funext i
    simpa [terminalDataFollowerOutputs, run,
      ActualInitializationHorizonObservation.terminalData] using congrFun hdataFollowers i
  have htransport := htraceFollowers'.trans hdataFollowers'.symm
  intro i
  exact congrFun htransport i

/-- The retained terminal carry code decodes to the follower carry in the
same actual terminal handoff.  The terminal trace is reconstructed from the
actual reached carry; its C observation is the literal producer image. -/
theorem sourceInitializedTerminalBoundaryFollowerCarryCodes_actual
    (source : SourceInput p) :
    ∀ i : Fin (p.m - 1),
      ActualInitializationBlockMeasurability.followerCarryOfCode
        ((ActualInitializationTerminalReadout.sourceInitializedTerminalBoundaryFollowerCarryCodes
          (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
          (rewards := rewards) source).2 i) =
      ActualInitializationRun.followerCarryOfBoundaryOutput rate
        ((ActualInitializationHorizon.sourceInitializedRun p rate source rewards C_star C_h).terminalHandoff.followers i) := by
  let trace := ActualInitializationTerminalReadout.sourceInitializedTerminalTrace
    (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
    (rewards := rewards) source
  let observation := trace.2.blockCode.2
  have himage := sourceInitializedTerminalTrace_uncheckedOutput_eq_codeOutput
    (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
    (rewards := rewards) source
  have hhandoff := sourceInitializedTerminalObservation_handoff_eq_actual
    (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
    (rewards := rewards) source
  intro i
  have hcode := ActualInitializationTerminalReadout.sourceInitializedTerminalBoundaryFollowerCarryCodes_reconstruction
      (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
      (rewards := rewards) source i
  calc
    ActualInitializationBlockMeasurability.followerCarryOfCode
        ((ActualInitializationTerminalReadout.sourceInitializedTerminalBoundaryFollowerCarryCodes
          (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
          (rewards := rewards) source).2 i) =
      ActualInitializationRun.followerCarryOfBoundaryOutput rate
        (ActualInitializationFollowerBoundaryMeasurability.decodeBoundaryOutputCode
          p rate
          (ActualInitializationFollowerBoundaryMeasurability.boundaryOutputFromFollowerCode
            p rate trace.1 (observation.followerCodes i))) := hcode
    _ = ActualInitializationRun.followerCarryOfBoundaryOutput rate
        (ActualInitializationFollowerBoundaryMeasurability.decodeBoundaryOutputCode
          p rate (observation.uncheckedBoundaryOutputs i)) := by
      rw [← himage i]
    _ = ActualInitializationRun.followerCarryOfBoundaryOutput rate
        ((ActualInitializationCombinedBoundaryMeasurability.combinedBoundaryHandoffOfObservation
          observation).followers i) := rfl
    _ = ActualInitializationRun.followerCarryOfBoundaryOutput rate
        ((ActualInitializationHorizon.sourceInitializedRun p rate source rewards C_star C_h).terminalHandoff.followers i) := by
      rw [hhandoff i]

/-- Re-encoding the actual terminal handoff carry recovers the exact stored
terminal follower carry code, including its existing ordinary/dagger
configuration coordinates. -/
theorem sourceInitializedTerminalBoundaryFollowerCarryCodes_actual_code
    (source : SourceInput p) :
    ∀ i : Fin (p.m - 1),
      ActualInitializationBlockMeasurability.followerCarryCodeOf
        (ActualInitializationRun.followerCarryOfBoundaryOutput rate
          ((ActualInitializationHorizon.sourceInitializedRun p rate source rewards C_star C_h).terminalHandoff.followers i)) =
        (ActualInitializationTerminalReadout.sourceInitializedTerminalBoundaryFollowerCarryCodes
          (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
          (rewards := rewards) source).2 i := by
  intro i
  rw [← sourceInitializedTerminalBoundaryFollowerCarryCodes_actual
    (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
    (rewards := rewards) source i]
  exact ActualInitializationCombinedBoundaryMeasurability.followerCarryCodeOf_decode _

/-- The actual terminal-handoff follower code readout, in the same product
space of `D.FollowerCarryCode` values used by the terminal code family. -/
def sourceInitializedTerminalHandoffFollowerCarryCodes
    {C_star C_h : ℝ} {rewards : GridRewardTable p} (source : SourceInput p) :
    Fin (p.m - 1) → ActualInitializationBlockMeasurability.FollowerCarryCode p rate :=
  fun i => ActualInitializationBlockMeasurability.followerCarryCodeOf
    (ActualInitializationRun.followerCarryOfBoundaryOutput rate
      ((ActualInitializationHorizon.sourceInitializedRun p rate source rewards C_star C_h).terminalHandoff.followers i))

private theorem measurable_sigma_snd_constant_fiber
    {ι β : Type*} [MeasurableSpace β] :
    Measurable (fun entry : Sigma (fun _ : ι => β) => entry.2) := by
  intro s hs
  change MeasurableSet[
    (⨅ i, (inferInstance : MeasurableSpace β).map (Sigma.mk i))]
      {entry : Sigma (fun _ : ι => β) | entry.2 ∈ s}
  rw [MeasurableSpace.measurableSet_iInf]
  intro i
  rw [MeasurableSpace.map_def]
  simpa using hs

/-- The actual terminal-handoff code readout is jointly measurable into the
existing product of D's follower carry code spaces.  It is obtained by
projecting T's measurable dependent terminal readout and transporting along
the actual carry-code identity above. -/
theorem measurable_sourceInitializedTerminalHandoffFollowerCarryCodes :
    Measurable (sourceInitializedTerminalHandoffFollowerCarryCodes
      (p := p) (rate := rate) (C_star := C_star) (C_h := C_h) (rewards := rewards)) := by
  let terminalCodes := ActualInitializationTerminalReadout.sourceInitializedTerminalBoundaryFollowerCarryCodes
      (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
      (rewards := rewards)
  have hprojection : Measurable (fun entry :
      Sigma (ActualInitializationTerminalReadout.TerminalBoundaryFollowerCarryCodeFamily
        p rate) => entry.2) := by
    change Measurable (fun entry :
      Sigma (fun _ : Fin (n_boot p) =>
        Fin (p.m - 1) → ActualInitializationBlockMeasurability.FollowerCarryCode p rate) =>
          entry.2)
    exact measurable_sigma_snd_constant_fiber
  have hterminalCodes : Measurable (fun source : SourceInput p =>
      (terminalCodes (source := source)).2) :=
    hprojection.comp (ActualInitializationTerminalReadout.measurable_sourceInitializedTerminalBoundaryFollowerCarryCodes
        (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
        (rewards := rewards))
  have hactual :
      sourceInitializedTerminalHandoffFollowerCarryCodes
          (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
          (rewards := rewards) =
        fun source : SourceInput p => (terminalCodes (source := source)).2 := by
    funext source
    funext i
    exact sourceInitializedTerminalBoundaryFollowerCarryCodes_actual_code
      (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
      (rewards := rewards) source i
  change Measurable (sourceInitializedTerminalHandoffFollowerCarryCodes
    (p := p) (rate := rate) (C_star := C_star) (C_h := C_h) (rewards := rewards))
  rw [hactual]
  exact hterminalCodes

end Bandits.Support.ActualInitializationTerminalCarryHandoff

end
