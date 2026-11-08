/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ActualReferenceInitializationHorizon
public import Bandits.Support.ReferenceActiveStoppedPrefixCoupling

/-!
# Actual initialization to active stopped-prefix splice

Sources: `sources/zip4/manuscript/07_public_setup.tex:106-156`,
`sources/zip4/manuscript/08_main_theorem.tex:29-42,67-83`, and
`sources/zip4/manuscript/06_interruptions.tex:235-296`.

The launched result consumes the actual source-initialized terminal handoff
and its existential canonical all-active state, then starts the accepted
ordinary/reference folds at the actual zero-based launch boundary. The
initialized records remain an immutable prefix. Local saved-reference
diagnostic exclusions are conditions on each requested stopped prefix and
on each first-bad candidate; they are not identified here with the two global
event complements. The exhausted disposition is retained as a separate
result with the full horizon initialization history and no suffix rounds.

This is deterministic internal mathematics. It does not identify source
false, ambiguous, queue, or initialization events with saved diagnostics, and
does not prove a probability, expectation, local validity, or regret theorem.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.ActualReferenceInitializationBlock
open Bandits.Support.ReferenceActiveStoppedPrefixCoupling
open scoped Classical

namespace Bandits.Support.ActualReferenceStoppedPrefixSplice

/-- The literal physical projection of one actual initialization record.
Every field is read from its stored, successfully executed physical result. -/
def initializationPhysicalProjection {p : Parameters}
    {rate : ActualReferenceInitializationHorizon.RateInput p}
    {source : Bandits.Support.BootstrapPrivateRoundStreams.SourceInput p}
    {rewards : ActualInitializationPhysicalStep.GridRewardTable p}
    (record : ActualInitializationRun.PhysicalRoundRecord p rate source rewards) :
    ReferenceActiveStoppedPrefixCoupling.PhysicalRound p :=
  ⟨record.time, record.result.actions, record.result.feedback,
    fun i => ActualReferenceInitializationBlock.recordEntry record i⟩

/-- A real launched initialization is spliced to the accepted finite
all-active suffix. The two and only two global event conditions are the
literal complements used by the source-initialized construction. The returned
state, carry, handoff, initialization history, and suffix folds are all
existential outputs of the accepted computations.

For every requested suffix prefix, the local antecedent is precisely absence
of a wrong unique acceptance on those saved reference records. Since the
quantifier ranges over all \(k \leq T-start\), it includes both the empty
prefix \(k=0\) and the full safe suffix. The separate first-bad implication
retains equality only through the bad record's physical round and only through
the predecessor boundary for canonical states. -/
theorem sourceInitializedRun_launched_suffix_splice
    (p : Parameters) (rate : ActualReferenceInitializationHorizon.RateInput p)
    (source : Bandits.Support.BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (hinit : ¬ InitializationFailureProvenance.operationalInitializationFailure
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate))
    (hfalse : source ∉ GeneratedFalseForwardEvent.actualAnyFalseForwardPrefixPassSet
      C_star C_h rate.eta rewards (ActualInitializationPhysicalStep.selectedRowIndex p source))
    (launch : BootstrapCoordinatorLocalRound.LaunchedBlock p)
    (seed : ActualInitializationRun.CoordinatorLearnerZeroSeed p)
    (hlaunched : (ActualInitializationHorizon.sourceInitializedRun p rate source rewards
      C_star C_h).terminalDisposition = .launched launch seed) :
    let x := ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate
    let result := ActualInitializationHorizon.sourceInitializedRun p rate source rewards C_star C_h
    let J := ActualInitializationPhysicalStep.selectedRowIndex p source
    let initializedTrace := result.records.map initializationPhysicalProjection
    let start := launch.monitor.launchPosition
    let count := p.T - start
    ∃ actual : ActualInitializationRun.BlockCarry p rate result.terminalBlock,
      ∃ active : ReferenceActivePhysicalStep.State p rate,
        ActualReferenceInitializationBlock.BlockStartRelated source rewards C_star C_h rate
          result.terminalBlock actual
          (ReferenceInitializationRun.run x result.terminalBlock.val)
          (result.records.take (BootstrapObservedFollower.blockStart p result.terminalBlock)) ∧
        HEq result.terminalFold
          (ActualInitializationRun.foldBlock p rate result.terminalBlock source rewards actual) ∧
        actual.C_star = C_star ∧ actual.C_h = C_h ∧
        active.coordinator = .first ∧
        active.upDecoderBank = CoordinatorUpReception.initialUpDecoderBank p ∧
        (∀ i, ActualInitializationRun.followerCarryOfBoundaryOutput rate
          (result.terminalHandoff.followers i) = .declared J (active.activations i)
            (active.followers i)) ∧
        (∀ i, ActualReferenceInitializationBlock.follower_start_related x source rate rfl
          (ReferenceInitializationRun.output x) i
          (.declared J (active.activations i) (active.followers i))) ∧
        (∀ i, ∃ state memory,
          active.followers i = .ordinary state memory ∧
          state = ReferenceInitializationRun.ordinary x (ReferenceInitializationRun.output x)
            (refFollower i) ∧
          state.lastDown = none ∧ ReferencePrelaunchFollower.acceptedStart state = 0 ∧
          state.S = 0 ∧ state.delta = 0 ∧ state.backlog = 0 ∧
          state.status = .unoccupied ∧ state.initializationFailure = false) ∧
        (∀ i, (active.activations i).val ≤ start + 1) ∧
        (∀ time : Fin p.T, start ≤ time.val →
          ∀ i, (active.activations i).val ≤ time.val + 1) ∧
        (∀ i row activation state memory,
          actual.followers i = .declared row activation (.ordinary state memory) →
          result.terminalHandoff.followers i = .preserveDeclared J activation
            (.ordinary (ReferenceInitializationRun.ordinary x (ReferenceInitializationRun.output x)
              (refFollower i)) memory) ∧
          active.followers i = .ordinary
            (ReferenceInitializationRun.ordinary x (ReferenceInitializationRun.output x)
              (refFollower i)) memory) ∧
        (∀ i row activation state memory,
          result.terminalHandoff.followers i =
            .firstDeclaration row activation state memory →
          state = ReferencePrelaunchFollower.initial p rate.eta ∧
            memory = ActiveFollowerLifecycle.initialMemory p) ∧
        ∃ hstart : start ≤ p.T,
          ∃ hspan : start + count ≤ p.T,
            ∃ hmode : ReferenceActivePhysicalHorizon.allActiveAtStart active start,
            (ReferenceInitializationRun.output x).crossing = some result.terminalBlock ∧
            ReferenceInitializationRun.launchRound x = start + 1 ∧
            result.records.length = start ∧
            (ActualInitializationRun.PhysicalRoundRecord.actions result.records).length = start ∧
            (ActualInitializationRun.PhysicalRoundRecord.feedback result.records).length = start ∧
            ActualReferenceInitializationBlock.past_related result.records
              (ReferenceInitializationRun.output x) ∧
            ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.output x).completed =
              start ∧
            (ActualInitializationRun.PhysicalRoundRecord.times result.records).map Fin.val =
              ActualInitializationHorizon.consecutiveNat 0 start ∧
            ∃ suffix : ReferenceActiveStoppedPrefixCoupling.Run active,
              suffix = ReferenceActiveStoppedPrefixCoupling.run active source.1.2 J rewards
                start count hspan
                hmode ∧
              ∃ referenceSuffix : ReferenceActivePhysicalHorizon.Run active,
                referenceSuffix = ReferenceActivePhysicalHorizon.run active source.1.2 J rewards
                  start count hspan
                  hmode ∧
                (initializedTrace ++ suffix.physicalTrace).length = p.T ∧
                ((initializedTrace ++ suffix.physicalTrace).map
                  ReferenceActiveStoppedPrefixCoupling.PhysicalRound.actions).length = p.T ∧
                ((initializedTrace ++ suffix.physicalTrace).map
                  ReferenceActiveStoppedPrefixCoupling.PhysicalRound.gridFeedback).length = p.T ∧
                ((initializedTrace ++ suffix.physicalTrace).map
                  ReferenceActiveStoppedPrefixCoupling.PhysicalRound.ownEntries).length = p.T ∧
                ((initializedTrace ++ suffix.physicalTrace).map
                  ReferenceActiveStoppedPrefixCoupling.PhysicalRound.totalReward).length = p.T ∧
                (initializedTrace ++
                  (referenceSuffix.records.map
                    ReferenceActiveStoppedPrefixCoupling.referencePhysical)).length = p.T ∧
                ((initializedTrace ++
                  (referenceSuffix.records.map
                    ReferenceActiveStoppedPrefixCoupling.referencePhysical)).map
                    ReferenceActiveStoppedPrefixCoupling.PhysicalRound.actions).length = p.T ∧
                ((initializedTrace ++
                  (referenceSuffix.records.map
                    ReferenceActiveStoppedPrefixCoupling.referencePhysical)).map
                    ReferenceActiveStoppedPrefixCoupling.PhysicalRound.gridFeedback).length = p.T ∧
                ((initializedTrace ++
                  (referenceSuffix.records.map
                    ReferenceActiveStoppedPrefixCoupling.referencePhysical)).map
                    ReferenceActiveStoppedPrefixCoupling.PhysicalRound.ownEntries).length = p.T ∧
                ((initializedTrace ++
                  (referenceSuffix.records.map
                    ReferenceActiveStoppedPrefixCoupling.referencePhysical)).map
                    ReferenceActiveStoppedPrefixCoupling.PhysicalRound.totalReward).length = p.T ∧
                (suffix.records.map fun record => record.input.time.val) =
                  ReferenceActivePhysicalHorizon.calendar start count ∧
                (referenceSuffix.records.map fun record => record.input.time.val) =
                  ReferenceActivePhysicalHorizon.calendar start count ∧
                (∀ record ∈ suffix.records,
                  record.input.rows = source.1.2 ∧ record.input.selected = J ∧
                    record.input.rewards = rewards) ∧
                (∀ record ∈ referenceSuffix.records,
                  record.input.rows = source.1.2 ∧ record.input.selected = J ∧
                    record.input.rewards = rewards) ∧
                (start = p.T →
                  count = 0 ∧ suffix.records = [] ∧ suffix.finalState = active ∧
                    suffix.totalReward = 0 ∧
                    ReferenceInitializationRun.launchRound x = p.T + 1 ∧
                    (ReferenceInitializationRun.output x).crossing =
                      some result.terminalBlock) ∧
                (∀ k (hk : k ≤ count)
                    (hgood : ∀ record ∈
                      (ReferenceActivePhysicalHorizon.run active source.1.2 J rewards
                        start count hspan hmode).records.take k,
                      ReferenceActiveStoppedPrefixCoupling.no_wrong_unique_accepted record),
                  ((ReferenceActiveStoppedPrefixCoupling.run active source.1.2 J rewards
                    start k (by omega) hmode).finalState =
                    (ReferenceActivePhysicalHorizon.run active source.1.2 J rewards
                      start k (by omega) hmode).finalState ∧
                  (ReferenceActiveStoppedPrefixCoupling.run active source.1.2 J rewards
                    start count hspan hmode).physicalTrace.take k =
                    (((ReferenceActivePhysicalHorizon.run active source.1.2 J rewards
                      start count hspan hmode).records.map
                      ReferenceActiveStoppedPrefixCoupling.referencePhysical).take k) ∧
                  (ReferenceActiveStoppedPrefixCoupling.run active source.1.2 J rewards
                    start k (by omega) hmode).totalReward =
                    (ReferenceActivePhysicalHorizon.run active source.1.2 J rewards
                      start k (by omega) hmode).totalReward) ∧
                  (initializedTrace ++
                    (ReferenceActiveStoppedPrefixCoupling.run active source.1.2 J rewards
                      start count hspan hmode).physicalTrace.take k) =
                    (initializedTrace ++
                    (((ReferenceActivePhysicalHorizon.run active source.1.2 J rewards
                      start count hspan hmode).records.map
                      ReferenceActiveStoppedPrefixCoupling.referencePhysical).take k)) ∧
                  ((((ReferenceActiveStoppedPrefixCoupling.run active source.1.2 J rewards
                    start count hspan hmode).physicalTrace.take k).map
                      ReferenceActiveStoppedPrefixCoupling.PhysicalRound.actions) =
                    ((((ReferenceActivePhysicalHorizon.run active source.1.2 J rewards
                      start count hspan hmode).records.map
                      ReferenceActiveStoppedPrefixCoupling.referencePhysical).take k).map
                      ReferenceActiveStoppedPrefixCoupling.PhysicalRound.actions) ∧
                  (((ReferenceActiveStoppedPrefixCoupling.run active source.1.2 J rewards
                    start count hspan hmode).physicalTrace.take k).map
                      ReferenceActiveStoppedPrefixCoupling.PhysicalRound.gridFeedback) =
                    ((((ReferenceActivePhysicalHorizon.run active source.1.2 J rewards
                      start count hspan hmode).records.map
                      ReferenceActiveStoppedPrefixCoupling.referencePhysical).take k).map
                      ReferenceActiveStoppedPrefixCoupling.PhysicalRound.gridFeedback) ∧
                  (((ReferenceActiveStoppedPrefixCoupling.run active source.1.2 J rewards
                    start count hspan hmode).physicalTrace.take k).map
                      ReferenceActiveStoppedPrefixCoupling.PhysicalRound.ownEntries) =
                    ((((ReferenceActivePhysicalHorizon.run active source.1.2 J rewards
                      start count hspan hmode).records.map
                      ReferenceActiveStoppedPrefixCoupling.referencePhysical).take k).map
                      ReferenceActiveStoppedPrefixCoupling.PhysicalRound.ownEntries)) ∧
                  ((initializedTrace ++
                    (ReferenceActiveStoppedPrefixCoupling.run active source.1.2 J rewards
                      start count hspan
                      hmode).physicalTrace.take k).map
                      ReferenceActiveStoppedPrefixCoupling.PhysicalRound.actions) =
                    ((initializedTrace ++
                    (((ReferenceActivePhysicalHorizon.run active source.1.2 J rewards
                      start count hspan
                      hmode).records.map
                      ReferenceActiveStoppedPrefixCoupling.referencePhysical).take k)).map
                      ReferenceActiveStoppedPrefixCoupling.PhysicalRound.actions) ∧
                  ((initializedTrace ++
                    (ReferenceActiveStoppedPrefixCoupling.run active source.1.2 J rewards
                      start count hspan
                      hmode).physicalTrace.take k).map
                      ReferenceActiveStoppedPrefixCoupling.PhysicalRound.gridFeedback) =
                    ((initializedTrace ++
                    (((ReferenceActivePhysicalHorizon.run active source.1.2 J rewards
                      start count hspan
                      hmode).records.map
                      ReferenceActiveStoppedPrefixCoupling.referencePhysical).take k)).map
                      ReferenceActiveStoppedPrefixCoupling.PhysicalRound.gridFeedback) ∧
                  ((initializedTrace ++
                    (ReferenceActiveStoppedPrefixCoupling.run active source.1.2 J rewards
                      start count hspan
                      hmode).physicalTrace.take k).map
                      ReferenceActiveStoppedPrefixCoupling.PhysicalRound.ownEntries) =
                    ((initializedTrace ++
                    (((ReferenceActivePhysicalHorizon.run active source.1.2 J rewards
                      start count hspan
                      hmode).records.map
                      ReferenceActiveStoppedPrefixCoupling.referencePhysical).take k)).map
                      ReferenceActiveStoppedPrefixCoupling.PhysicalRound.ownEntries) ∧
                  ((initializedTrace ++
                    (ReferenceActiveStoppedPrefixCoupling.run active source.1.2 J rewards
                      start count hspan
                      hmode).physicalTrace.take k).map
                      ReferenceActiveStoppedPrefixCoupling.PhysicalRound.totalReward) =
                    ((initializedTrace ++
                    (((ReferenceActivePhysicalHorizon.run active source.1.2 J rewards
                      start count hspan
                      hmode).records.map
                      ReferenceActiveStoppedPrefixCoupling.referencePhysical).take k)).map
                      ReferenceActiveStoppedPrefixCoupling.PhysicalRound.totalReward) ∧
                  (((initializedTrace ++
                    (ReferenceActiveStoppedPrefixCoupling.run active source.1.2 J rewards
                      start count hspan
                      hmode).physicalTrace.take k).map
                      ReferenceActiveStoppedPrefixCoupling.PhysicalRound.totalReward).sum =
                    (((initializedTrace ++
                    (((ReferenceActivePhysicalHorizon.run active source.1.2 J rewards
                      start count hspan
                      hmode).records.map
                      ReferenceActiveStoppedPrefixCoupling.referencePhysical).take k)).map
                      ReferenceActiveStoppedPrefixCoupling.PhysicalRound.totalReward).sum))) ∧
                (∀ index (hindex : index < count)
                    (hearlier : ∀ record ∈
                      (ReferenceActivePhysicalHorizon.run active source.1.2 J rewards
                        start count hspan hmode).records.take index,
                      ReferenceActiveStoppedPrefixCoupling.no_wrong_unique_accepted record)
                    (hbad : ReferenceActiveStoppedPrefixCoupling.saved_wrong_unique_accepted
                      (ReferenceActiveStoppedPrefixCoupling.referenceRecordAt active source.1.2 J
                        rewards start index (by omega) hmode)),
                  ((∃ record ∈
                    (ReferenceActivePhysicalHorizon.run active source.1.2 J rewards
                      start count hspan hmode).records,
                    record.input.time.val = start + index ∧
                      ReferenceActiveStoppedPrefixCoupling.saved_wrong_unique_accepted record) ∧
                  (∀ k (_hk : k ≤ index),
                    (ReferenceActiveStoppedPrefixCoupling.run active source.1.2 J rewards
                      start k (by omega) hmode).finalState =
                    (ReferenceActivePhysicalHorizon.run active source.1.2 J rewards
                      start k (by omega) hmode).finalState) ∧
                  (∀ k, k ≤ index + 1 →
                    (ReferenceActiveStoppedPrefixCoupling.run active source.1.2 J rewards
                      start count hspan hmode).physicalTrace.take k =
                    (((ReferenceActivePhysicalHorizon.run active source.1.2 J rewards
                      start count hspan hmode).records.map
                      ReferenceActiveStoppedPrefixCoupling.referencePhysical).take k)) ∧
                  (ReferenceActiveStoppedPrefixCoupling.run active source.1.2 J rewards
                    start (index + 1) (by omega) hmode).totalReward =
                    (ReferenceActivePhysicalHorizon.run active source.1.2 J rewards
                      start (index + 1) (by omega) hmode).totalReward) ∧
                  (∀ k, k ≤ index + 1 →
                    (initializedTrace ++
                      (ReferenceActiveStoppedPrefixCoupling.run active source.1.2 J rewards
                        start count hspan hmode).physicalTrace.take k) =
                    (initializedTrace ++
                      (((ReferenceActivePhysicalHorizon.run active source.1.2 J rewards
                        start count hspan hmode).records.map
                        ReferenceActiveStoppedPrefixCoupling.referencePhysical).take k))) ∧
                  (∀ k, k ≤ index + 1 →
                    ((initializedTrace ++
                      (ReferenceActiveStoppedPrefixCoupling.run active source.1.2 J rewards
                        start count hspan
                        hmode).physicalTrace.take k).map
                        ReferenceActiveStoppedPrefixCoupling.PhysicalRound.actions) =
                      ((initializedTrace ++
                      (((ReferenceActivePhysicalHorizon.run active source.1.2 J rewards
                        start count hspan
                        hmode).records.map
                        ReferenceActiveStoppedPrefixCoupling.referencePhysical).take k)).map
                        ReferenceActiveStoppedPrefixCoupling.PhysicalRound.actions) ∧
                    ((initializedTrace ++
                      (ReferenceActiveStoppedPrefixCoupling.run active source.1.2 J rewards
                        start count hspan
                        hmode).physicalTrace.take k).map
                        ReferenceActiveStoppedPrefixCoupling.PhysicalRound.gridFeedback) =
                      ((initializedTrace ++
                      (((ReferenceActivePhysicalHorizon.run active source.1.2 J rewards
                        start count hspan
                        hmode).records.map
                        ReferenceActiveStoppedPrefixCoupling.referencePhysical).take k)).map
                        ReferenceActiveStoppedPrefixCoupling.PhysicalRound.gridFeedback) ∧
                    ((initializedTrace ++
                      (ReferenceActiveStoppedPrefixCoupling.run active source.1.2 J rewards
                        start count hspan
                        hmode).physicalTrace.take k).map
                        ReferenceActiveStoppedPrefixCoupling.PhysicalRound.ownEntries) =
                      ((initializedTrace ++
                      (((ReferenceActivePhysicalHorizon.run active source.1.2 J rewards
                        start count hspan
                        hmode).records.map
                        ReferenceActiveStoppedPrefixCoupling.referencePhysical).take k)).map
                        ReferenceActiveStoppedPrefixCoupling.PhysicalRound.ownEntries)) ∧
                  (∀ k, k ≤ index + 1 →
                    List.sum ((initializedTrace ++
                      (ReferenceActiveStoppedPrefixCoupling.run active source.1.2 J rewards
                        start count hspan hmode).physicalTrace.take k).map
                      ReferenceActiveStoppedPrefixCoupling.PhysicalRound.totalReward) =
                    List.sum ((initializedTrace ++
                      (((ReferenceActivePhysicalHorizon.run active source.1.2 J rewards
                        start count hspan hmode).records.map
                        ReferenceActiveStoppedPrefixCoupling.referencePhysical).take k)).map
                      ReferenceActiveStoppedPrefixCoupling.PhysicalRound.totalReward)))
      := by
  dsimp only
  let x := ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate
  let result := ActualInitializationHorizon.sourceInitializedRun p rate source rewards C_star C_h
  let J := ActualInitializationPhysicalStep.selectedRowIndex p source
  let initializedTrace := result.records.map initializationPhysicalProjection
  let start := launch.monitor.launchPosition
  let count := p.T - start
  obtain ⟨actual, hrelated, hfold, active, hfirst, hup, hhandoff, hstartRelated,
    hordinary, hactiveStart, hactiveTime, hpreserve⟩ :=
    ActualReferenceInitializationHorizon.sourceInitializedRun_launched_state
      p rate source rewards C_star C_h hinit hfalse launch seed hlaunched
  obtain ⟨hcross, hlaunchRound, _, _, hposition, _, _, _, _, _⟩ :=
    ActualReferenceInitializationHorizon.sourceInitializedRun_launched_endpoint
      p rate source rewards C_star C_h hinit hfalse launch seed hlaunched
  obtain ⟨_, hpast, _, _, _⟩ :=
    ActualReferenceInitializationHorizon.sourceInitializedRun_output_related
      p rate source rewards C_star C_h hinit hfalse
  have hactualCStar : actual.C_star = C_star := hrelated.2.2.2.2.1
  have hactualCh : actual.C_h = C_h := hrelated.2.2.2.2.2.1
  have hblockStop : BootstrapObservedFollower.blockStop p result.terminalBlock ≤ p.T := by
    unfold BootstrapObservedFollower.blockStop
    exact Nat.min_le_left _ _
  have hstart : start ≤ p.T := by
    dsimp only [start]
    rw [hposition]
    exact hblockStop
  have hspan : start + count ≤ p.T := by
    dsimp only [count]
    omega
  have hmode : ReferenceActivePhysicalHorizon.allActiveAtStart active start := by
    intro i
    simpa only [start] using hactiveStart i
  have hlengths := ActualInitializationHorizon.sourceInitializedRun_history_lengths
    p rate source rewards C_star C_h
  have hrecordLength : result.records.length =
      BootstrapObservedFollower.blockStop p result.terminalBlock := by
    simpa only [ActualInitializationRun.PhysicalRoundRecord.actions, List.length_map]
      using hlengths.1
  have hinitLength : result.records.length = start := by
    rw [← hposition] at hrecordLength
    exact hrecordLength
  have hactionsLength :
      (ActualInitializationRun.PhysicalRoundRecord.actions result.records).length = start := by
    calc
      _ = BootstrapObservedFollower.blockStop p result.terminalBlock := hlengths.1
      _ = start := hposition.symm
  have hfeedbackLength :
      (ActualInitializationRun.PhysicalRoundRecord.feedback result.records).length = start := by
    calc
      _ = BootstrapObservedFollower.blockStop p result.terminalBlock := hlengths.2
      _ = start := hposition.symm
  have hinitCalendar :=
    ActualInitializationHorizon.sourceInitializedRun_chronological p rate source rewards C_star C_h
  rw [← hposition] at hinitCalendar
  have hinitCalendar' :
      (ActualInitializationRun.PhysicalRoundRecord.times result.records).map Fin.val =
        ActualInitializationHorizon.consecutiveNat 0 start := by
    simpa only [start] using hinitCalendar
  have hsourceBoundaryElapsed :
      ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.output x).completed = start := by
    have hlaunchElapsed :
        ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.output x).completed + 1 =
          start + 1 := by
      simpa [ReferenceInitializationRun.launchRound, hcross] using hlaunchRound
    omega
  let suffix := ReferenceActiveStoppedPrefixCoupling.run active source.1.2 J rewards
    start count hspan hmode
  let referenceSuffix := ReferenceActivePhysicalHorizon.run active source.1.2 J rewards
    start count hspan hmode
  have hrecordsCount :
      (ReferenceActiveStoppedPrefixCoupling.run active source.1.2 J rewards
        start count hspan hmode).records.length = count :=
    ReferenceActiveStoppedPrefixCoupling.run_record_count active source.1.2 J rewards
      start count hspan hmode
  have htraceCount : suffix.physicalTrace.length = count := by
    simp only [suffix, ReferenceActiveStoppedPrefixCoupling.Run.physicalTrace,
      List.length_map]
    exact hrecordsCount
  have hinitTraceLength : initializedTrace.length = start := by
    simp only [initializedTrace, List.length_map]
    exact hinitLength
  have htotalTraceLength : (initializedTrace ++ suffix.physicalTrace).length = p.T := by
    rw [List.length_append, hinitTraceLength, htraceCount]
    dsimp only [count]
    omega
  have hreferenceCount := ReferenceActivePhysicalHorizon.run_record_count
    active source.1.2 J rewards start count hspan hmode
  have hreferenceTraceLength :
      (referenceSuffix.records.map
        ReferenceActiveStoppedPrefixCoupling.referencePhysical).length = count := by
    simp only [referenceSuffix, List.length_map]
    exact hreferenceCount
  have htotalReferenceTraceLength :
      (initializedTrace ++ (referenceSuffix.records.map
        ReferenceActiveStoppedPrefixCoupling.referencePhysical)).length = p.T := by
    rw [List.length_append, hinitTraceLength, hreferenceTraceLength]
    dsimp only [count]
    omega
  have hordinaryCalendar :=
    ReferenceActiveStoppedPrefixCoupling.run_time_values active source.1.2 J rewards
      start count hspan hmode
  have hreferenceCalendar :=
    ReferenceActivePhysicalHorizon.run_time_values active source.1.2 J rewards
      start count hspan hmode
  have hrecordInputs :=
    ReferenceActiveStoppedPrefixCoupling.run_record_inputs active source.1.2 J rewards
      start count hspan hmode
  have hfirstDeclaration :=
    ActualReferenceInitializationHorizon.sourceInitializedRun_firstDeclaration_initial
      p rate source rewards C_star C_h
  refine ⟨actual, active, hrelated, hfold, hactualCStar, hactualCh,
    hfirst, hup, hhandoff, hstartRelated,
    hordinary, hmode, hactiveTime, hpreserve, ?_, hstart, hspan, hmode, hcross,
    hlaunchRound, hinitLength, hactionsLength, hfeedbackLength, hpast,
    hsourceBoundaryElapsed, hinitCalendar', suffix, rfl, referenceSuffix, rfl,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i row activation state memory hfirst
    exact hfirstDeclaration i row activation state memory hfirst
  · exact htotalTraceLength
  · simp only [List.length_map]
    exact htotalTraceLength
  · simp only [List.length_map]
    exact htotalTraceLength
  · simp only [List.length_map]
    exact htotalTraceLength
  · simp only [List.length_map]
    exact htotalTraceLength
  · exact htotalReferenceTraceLength
  · simp only [List.length_map]
    exact htotalReferenceTraceLength
  · simp only [List.length_map]
    exact htotalReferenceTraceLength
  · simp only [List.length_map]
    exact htotalReferenceTraceLength
  · simp only [List.length_map]
    exact htotalReferenceTraceLength
  · simpa only [suffix] using hordinaryCalendar
  · simpa only [referenceSuffix] using hreferenceCalendar
  · intro record hmem
    exact (hrecordInputs.1 record (by simpa only [suffix] using hmem))
  · intro record hmem
    exact (hrecordInputs.2 record (by simpa only [referenceSuffix] using hmem))
  · intro hstartT
    have hcount : count = 0 := by
      dsimp only [count]
      omega
    have hzero :=
      ReferenceActiveStoppedPrefixCoupling.run_zero active source.1.2 J rewards
        start (by omega) hmode
    have hrecords : suffix.records = [] := by
      simpa only [suffix, hcount] using hzero.2
    have hfinal : suffix.finalState = active := by
      simpa only [suffix, hcount] using hzero.1
    have hreward : suffix.totalReward = 0 := by
      simp [ReferenceActiveStoppedPrefixCoupling.Run.totalReward,
        ReferenceActiveStoppedPrefixCoupling.Run.physicalTrace, hrecords]
    exact ⟨hcount, hrecords, hfinal, hreward, by omega, hcross⟩
  · intro k hk hgood
    have hstopped := ReferenceActiveStoppedPrefixCoupling.stopped_prefix_eq
      active source.1.2 J rewards start count hspan hmode k hk hgood
    have hprojections := ReferenceActiveStoppedPrefixCoupling.stopped_prefix_projections_eq
      active source.1.2 J rewards start count hspan hmode k hk hgood
    have htrace := hstopped.2.1
    have hactions := congrArg
      (List.map ReferenceActiveStoppedPrefixCoupling.PhysicalRound.actions) htrace
    have hfeedback := congrArg
      (List.map ReferenceActiveStoppedPrefixCoupling.PhysicalRound.gridFeedback) htrace
    have hentries := congrArg
      (List.map ReferenceActiveStoppedPrefixCoupling.PhysicalRound.ownEntries) htrace
    have hrewardSeq := congrArg
      (List.map ReferenceActiveStoppedPrefixCoupling.PhysicalRound.totalReward) htrace
    have hcombinedActions :
        ((initializedTrace ++
          (ReferenceActiveStoppedPrefixCoupling.run active source.1.2 J rewards
            start count hspan hmode).physicalTrace.take k).map
          ReferenceActiveStoppedPrefixCoupling.PhysicalRound.actions) =
        ((initializedTrace ++
          (((ReferenceActivePhysicalHorizon.run active source.1.2 J rewards
            start count hspan hmode).records.map
            ReferenceActiveStoppedPrefixCoupling.referencePhysical).take k)).map
          ReferenceActiveStoppedPrefixCoupling.PhysicalRound.actions) := by
      simp only [List.map_append]
      exact congrArg
        (fun tail => (initializedTrace.map
          ReferenceActiveStoppedPrefixCoupling.PhysicalRound.actions) ++ tail) hactions
    have hcombinedFeedback :
        ((initializedTrace ++
          (ReferenceActiveStoppedPrefixCoupling.run active source.1.2 J rewards
            start count hspan hmode).physicalTrace.take k).map
          ReferenceActiveStoppedPrefixCoupling.PhysicalRound.gridFeedback) =
        ((initializedTrace ++
          (((ReferenceActivePhysicalHorizon.run active source.1.2 J rewards
            start count hspan hmode).records.map
            ReferenceActiveStoppedPrefixCoupling.referencePhysical).take k)).map
          ReferenceActiveStoppedPrefixCoupling.PhysicalRound.gridFeedback) := by
      simp only [List.map_append]
      exact congrArg
        (fun tail => (initializedTrace.map
          ReferenceActiveStoppedPrefixCoupling.PhysicalRound.gridFeedback) ++ tail) hfeedback
    have hcombinedEntries :
        ((initializedTrace ++
          (ReferenceActiveStoppedPrefixCoupling.run active source.1.2 J rewards
            start count hspan hmode).physicalTrace.take k).map
          ReferenceActiveStoppedPrefixCoupling.PhysicalRound.ownEntries) =
        ((initializedTrace ++
          (((ReferenceActivePhysicalHorizon.run active source.1.2 J rewards
            start count hspan hmode).records.map
            ReferenceActiveStoppedPrefixCoupling.referencePhysical).take k)).map
          ReferenceActiveStoppedPrefixCoupling.PhysicalRound.ownEntries) := by
      simp only [List.map_append]
      exact congrArg
        (fun tail => (initializedTrace.map
          ReferenceActiveStoppedPrefixCoupling.PhysicalRound.ownEntries) ++ tail) hentries
    have hcombinedRewardSeq :
        ((initializedTrace ++
          (ReferenceActiveStoppedPrefixCoupling.run active source.1.2 J rewards
            start count hspan hmode).physicalTrace.take k).map
          ReferenceActiveStoppedPrefixCoupling.PhysicalRound.totalReward) =
        ((initializedTrace ++
          (((ReferenceActivePhysicalHorizon.run active source.1.2 J rewards
            start count hspan hmode).records.map
            ReferenceActiveStoppedPrefixCoupling.referencePhysical).take k)).map
          ReferenceActiveStoppedPrefixCoupling.PhysicalRound.totalReward) := by
      simp only [List.map_append]
      exact congrArg
        (fun tail => (initializedTrace.map
          ReferenceActiveStoppedPrefixCoupling.PhysicalRound.totalReward) ++ tail) hrewardSeq
    have hcombinedTrace := congrArg (List.append initializedTrace) htrace
    have hcombinedReward := congrArg List.sum hcombinedRewardSeq
    exact ⟨hstopped, hcombinedTrace, hprojections, hcombinedActions, hcombinedFeedback,
      hcombinedEntries, hcombinedRewardSeq, hcombinedReward⟩
  · intro index hindex hearlier hbad
    have hbadBoundary := ReferenceActiveStoppedPrefixCoupling.first_bad_boundary
      active source.1.2 J rewards start count index hspan hmode hindex
      hearlier hbad
    have hprojectionAtBad :
        ∀ k, k ≤ index + 1 →
          ((initializedTrace ++
            (ReferenceActiveStoppedPrefixCoupling.run active source.1.2 J rewards
              start count hspan hmode).physicalTrace.take k).map
            ReferenceActiveStoppedPrefixCoupling.PhysicalRound.actions) =
          ((initializedTrace ++
            (((ReferenceActivePhysicalHorizon.run active source.1.2 J rewards
              start count hspan hmode).records.map
              ReferenceActiveStoppedPrefixCoupling.referencePhysical).take k)).map
            ReferenceActiveStoppedPrefixCoupling.PhysicalRound.actions) ∧
          ((initializedTrace ++
            (ReferenceActiveStoppedPrefixCoupling.run active source.1.2 J rewards
              start count hspan hmode).physicalTrace.take k).map
            ReferenceActiveStoppedPrefixCoupling.PhysicalRound.gridFeedback) =
          ((initializedTrace ++
            (((ReferenceActivePhysicalHorizon.run active source.1.2 J rewards
              start count hspan hmode).records.map
              ReferenceActiveStoppedPrefixCoupling.referencePhysical).take k)).map
            ReferenceActiveStoppedPrefixCoupling.PhysicalRound.gridFeedback) ∧
          ((initializedTrace ++
            (ReferenceActiveStoppedPrefixCoupling.run active source.1.2 J rewards
              start count hspan hmode).physicalTrace.take k).map
            ReferenceActiveStoppedPrefixCoupling.PhysicalRound.ownEntries) =
          ((initializedTrace ++
            (((ReferenceActivePhysicalHorizon.run active source.1.2 J rewards
              start count hspan hmode).records.map
              ReferenceActiveStoppedPrefixCoupling.referencePhysical).take k)).map
            ReferenceActiveStoppedPrefixCoupling.PhysicalRound.ownEntries) := by
      intro k hk
      have htraceBad := hbadBoundary.2.2.1 k hk
      have hactions := congrArg
        (List.map ReferenceActiveStoppedPrefixCoupling.PhysicalRound.actions) htraceBad
      have hfeedback := congrArg
        (List.map ReferenceActiveStoppedPrefixCoupling.PhysicalRound.gridFeedback) htraceBad
      have hentries := congrArg
        (List.map ReferenceActiveStoppedPrefixCoupling.PhysicalRound.ownEntries) htraceBad
      simp only [List.map_append]
      exact ⟨
        congrArg (fun tail => (initializedTrace.map
          ReferenceActiveStoppedPrefixCoupling.PhysicalRound.actions) ++ tail) hactions,
        congrArg (fun tail => (initializedTrace.map
          ReferenceActiveStoppedPrefixCoupling.PhysicalRound.gridFeedback) ++ tail) hfeedback,
        congrArg (fun tail => (initializedTrace.map
          ReferenceActiveStoppedPrefixCoupling.PhysicalRound.ownEntries) ++ tail) hentries⟩
    have hcombinedTraceAtBad :
        ∀ k, k ≤ index + 1 →
          (initializedTrace ++
            (ReferenceActiveStoppedPrefixCoupling.run active source.1.2 J rewards
              start count hspan hmode).physicalTrace.take k) =
          (initializedTrace ++
            (((ReferenceActivePhysicalHorizon.run active source.1.2 J rewards
              start count hspan hmode).records.map
              ReferenceActiveStoppedPrefixCoupling.referencePhysical).take k)) := by
      intro k hk
      exact congrArg (List.append initializedTrace) (hbadBoundary.2.2.1 k hk)
    have hrewardAtBad :
        ∀ k, k ≤ index + 1 →
          List.sum ((initializedTrace ++
            (ReferenceActiveStoppedPrefixCoupling.run active source.1.2 J rewards
              start count hspan hmode).physicalTrace.take k).map
            ReferenceActiveStoppedPrefixCoupling.PhysicalRound.totalReward) =
          List.sum ((initializedTrace ++
            (((ReferenceActivePhysicalHorizon.run active source.1.2 J rewards
              start count hspan hmode).records.map
              ReferenceActiveStoppedPrefixCoupling.referencePhysical).take k)).map
            ReferenceActiveStoppedPrefixCoupling.PhysicalRound.totalReward) := by
      intro k hk
      exact congrArg (fun trace =>
        List.sum (trace.map ReferenceActiveStoppedPrefixCoupling.PhysicalRound.totalReward))
        (hcombinedTraceAtBad k hk)
    exact ⟨hbadBoundary, hcombinedTraceAtBad, hprojectionAtBad, hrewardAtBad⟩

/-- Horizon exhaustion keeps the complete actual initialization history,
the no-crossing sentinel and a zero-length post-initialization suffix. This
branch is distinct from a launch at the final boundary, whose crossing remains
present even though its reference launch round is also T+1. -/
theorem sourceInitializedRun_exhausted_splice
    (p : Parameters) (rate : ActualReferenceInitializationHorizon.RateInput p)
    (source : Bandits.Support.BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (hinit : ¬ InitializationFailureProvenance.operationalInitializationFailure
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate))
    (hfalse : source ∉ GeneratedFalseForwardEvent.actualAnyFalseForwardPrefixPassSet
      C_star C_h rate.eta rewards (ActualInitializationPhysicalStep.selectedRowIndex p source))
    (live : BootstrapCoordinatorLocalRound.PrelaunchBlock p)
    (hexhausted : (ActualInitializationHorizon.sourceInitializedRun p rate source rewards
      C_star C_h).terminalDisposition = .exhausted live) :
    let x := ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate
    let result := ActualInitializationHorizon.sourceInitializedRun p rate source rewards C_star C_h
    (ReferenceInitializationRun.output x).crossing = none ∧
    ReferenceInitializationRun.launchRound x = p.T + 1 ∧
    result.terminalBlock.val + 1 = n_boot p ∧
    BootstrapObservedFollower.blockStop p result.terminalBlock = p.T ∧
    result.records.length = p.T ∧
    (ActualInitializationRun.PhysicalRoundRecord.actions result.records).length = p.T ∧
    (ActualInitializationRun.PhysicalRoundRecord.feedback result.records).length = p.T ∧
    ActualReferenceInitializationBlock.past_related result.records
      (ReferenceInitializationRun.output x) ∧
    result.terminalFold.phase.monitorState.counters =
      (ReferenceInitializationRun.output x).counters ∧
    (∀ i, ActualReferenceInitializationBlock.follower_start_related x source rate rfl
      (ReferenceInitializationRun.output x) i
      (ActualInitializationRun.followerCarryOfBoundaryOutput rate
        (result.terminalHandoff.followers i))) ∧
    (ReferenceInitializationRun.boundaryActivation
      (ReferenceInitializationRun.run x result.terminalBlock.val)).val = p.T + 1 ∧
    (∀ i, match result.terminalHandoff.followers i with
      | .continueBootstrap _ _ activation => activation.val = p.T + 1
      | .firstDeclaration _ activation _ _ => activation.val = p.T + 1
      | .preserveDeclared _ _ _ => True) ∧
    (∀ record ∈ result.records, record.time.val < p.T) ∧
    (∃ actual : ActualInitializationRun.BlockCarry p rate result.terminalBlock,
      ActualReferenceInitializationBlock.BlockStartRelated source rewards C_star C_h rate
        result.terminalBlock actual (ReferenceInitializationRun.run x result.terminalBlock.val)
        (result.records.take (BootstrapObservedFollower.blockStart p result.terminalBlock)) ∧
      HEq result.terminalFold
        (ActualInitializationRun.foldBlock p rate result.terminalBlock source rewards actual) ∧
      ∀ i row activation state memory,
        actual.followers i = .declared row activation (.ordinary state memory) →
        result.terminalHandoff.followers i = .preserveDeclared
          (ActualInitializationPhysicalStep.selectedRowIndex p source) activation
          (.ordinary (ReferenceInitializationRun.ordinary x (ReferenceInitializationRun.output x)
            (refFollower i)) memory)) ∧
    (ActualInitializationRun.PhysicalRoundRecord.times result.records).map Fin.val =
      ActualInitializationHorizon.consecutiveNat 0 p.T ∧
    (result.records.map initializationPhysicalProjection).length = p.T ∧
    ((result.records.map initializationPhysicalProjection).map
      ReferenceActiveStoppedPrefixCoupling.PhysicalRound.totalReward).length = p.T ∧
    p.T - result.records.length = 0 := by
  dsimp only
  let x := ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate
  let result := ActualInitializationHorizon.sourceInitializedRun p rate source rewards C_star C_h
  have hrelated :=
    ActualReferenceInitializationHorizon.sourceInitializedRun_exhausted_related
      p rate source rewards C_star C_h hinit hfalse live hexhausted
  obtain ⟨hcross, hlaunchRound, hterminalBlock, hstop, hlength, hactions, hfeedback,
    hpast, hcounters, hfollowers, hactivation, hhandoff, hrecordTime, hexists⟩ := hrelated
  have hchron :=
    ActualInitializationHorizon.sourceInitializedRun_chronological p rate source rewards C_star C_h
  rw [hstop] at hchron
  refine ⟨hcross, hlaunchRound, hterminalBlock, hstop, hlength, hactions, hfeedback,
    hpast, hcounters, hfollowers, hactivation, hhandoff, hrecordTime, hexists,
    hchron, ?_, ?_, ?_⟩
  · simp only [List.length_map]
    exact hlength
  · simp only [List.length_map, List.length_map]
    exact hlength
  · omega

end Bandits.Support.ActualReferenceStoppedPrefixSplice

end
