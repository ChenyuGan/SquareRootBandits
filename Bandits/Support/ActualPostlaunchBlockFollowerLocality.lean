/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ActualPostlaunchFollowerObservationLocality

/-!
# Own-history locality within one actual postlaunch block

This module iterates the admitted actual one-round follower congruence along
the existing mixed physical trace. It compares complete follower storage and
the actual played-arm list from equal boundary storage, equal literal public
output, equal own private round scalars, and equal own feedback history.
Both executions retain their original sources, reward tables, and all other
private coordinates.

The final action consumer uses only the strict-past trace feedback and the
current own scalar; it does not require current feedback equality. Initial
storage equality and own coordinate provenance remain inputs for a later
complete-history producer, including its block-boundary and launch-cut cases.
This is neither source-initialized whole-horizon locality nor a source,
probability, section, or regret result.

Mathematical evidence: `sources/zip4/manuscript/01_introduction.tex:20-28`,
`sources/zip4/manuscript/07_public_setup.tex:28-38,55-114`,
`sources/zip4/manuscript/appendix_b_communication.tex:94-131`,
`sources/zip4/manuscript/06_interruptions.tex:240-296`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:6-14`.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.BootstrapObservedFollower
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.ActualPostlaunchFollowerMeasurability
open Bandits.Support.ActualPostlaunchPhysicalStep
open Bandits.Support.ActualPostlaunchStepMeasurability
open Bandits.Support.ActualCompletePhysicalHistory

namespace Bandits.Support.ActualPostlaunchBlockFollowerLocality

private theorem local_read_envelopes_eq_of_own_coordinates
    {p : ActualPostlaunchFollowerObservationLocality.Parameters}
    {rate : ActualPostlaunchFollowerObservationLocality.RateInput p}
    {block : Fin (n_boot p)} {cursor : Nat}
    (hcursor : cursor < BootstrapObservedFollower.blockLength p block)
    (i : Fin (p.m - 1))
    (x x' : ActualPostlaunchFollowerMeasurability.LocalInput
      (rate := rate) block cursor)
    (hf : ActualPostlaunchFollowerMeasurability.localFollower x =
      ActualPostlaunchFollowerMeasurability.localFollower x')
    (hpublic : (ActualPostlaunchFollowerMeasurability.localSource x).1 =
      (ActualPostlaunchFollowerMeasurability.localSource x').1)
    (hscalar : BootstrapPhysicalInput.playerRoundScalarAt p
        (ActualPostlaunchFollowerMeasurability.localSource x).2
        (PublicDiscreteDraws.followerPlayer p.two_le_m i)
        (ActualPostlaunchFollowerMeasurability.localTime block cursor hcursor) =
      BootstrapPhysicalInput.playerRoundScalarAt p
        (ActualPostlaunchFollowerMeasurability.localSource x').2
        (PublicDiscreteDraws.followerPlayer p.two_le_m i)
        (ActualPostlaunchFollowerMeasurability.localTime block cursor hcursor)) :
    ActualPostlaunchFollowerPreparationLocality.preparationSourceCoordinates
        (rate := rate) hcursor i x =
      ActualPostlaunchFollowerPreparationLocality.preparationSourceCoordinates
        (rate := rate) hcursor i x' ∧
    ActualPostlaunchFollowerObservationLocality.observationSourceCoordinates
        (rate := rate) hcursor i x =
      ActualPostlaunchFollowerObservationLocality.observationSourceCoordinates
        (rate := rate) hcursor i x' := by
  classical
  have hpublicRaw : x.1.1 = x'.1.1 := by
    simpa [ActualPostlaunchFollowerMeasurability.localSource] using hpublic
  have hids : x.1.1.1 = x'.1.1.1 := congrArg Prod.fst hpublicRaw
  have hrows : x.1.1.2 = x'.1.1.2 := congrArg Prod.snd hpublicRaw
  have hscalarRaw : BootstrapPhysicalInput.playerRoundScalarAt p x.1.2
        (PublicDiscreteDraws.followerPlayer p.two_le_m i)
        (ActualInitializationRun.blockTime p block cursor hcursor) =
      BootstrapPhysicalInput.playerRoundScalarAt p x'.1.2
        (PublicDiscreteDraws.followerPlayer p.two_le_m i)
        (ActualInitializationRun.blockTime p block cursor hcursor) := by
    simpa [ActualPostlaunchFollowerMeasurability.localSource,
      ActualPostlaunchFollowerMeasurability.localTime] using hscalar
  constructor
  · cases hlocal : ActualPostlaunchFollowerMeasurability.localFollower x with
    | bootstrap startup =>
        have hlocal' : ActualPostlaunchFollowerMeasurability.localFollower x' =
            .bootstrap startup := hf.symm.trans hlocal
        change (x.2.1).1 = .bootstrap startup at hlocal
        change (x'.2.1).1 = .bootstrap startup at hlocal'
        cases hcase : startup.blockCase with
        | inactive =>
            simp [ActualPostlaunchFollowerPreparationLocality.preparationSourceCoordinates,
              ActualPostlaunchFollowerMeasurability.localFollower,
              ActualPostlaunchFollowerMeasurability.localSource,
              ActualBootstrapObservationCode.sourcePrivate,
              ActualPostlaunchFollowerMeasurability.localTime,
              hlocal, hlocal', hcase, hscalarRaw]
        | active held privateID gain registers =>
            simp [ActualPostlaunchFollowerPreparationLocality.preparationSourceCoordinates,
              ActualPostlaunchFollowerMeasurability.localFollower,
              ActualPostlaunchFollowerMeasurability.localSource,
              ActualBootstrapObservationCode.sourcePrivate,
              ActualBootstrapObservationCode.sourceIDs,
              ActualPostlaunchFollowerMeasurability.localTime,
              hlocal, hlocal', hcase, hids, hscalarRaw]
    | declared row activation configuration =>
        have hlocal' : ActualPostlaunchFollowerMeasurability.localFollower x' =
            .declared row activation configuration := hf.symm.trans hlocal
        change (x.2.1).1 = .declared row activation configuration at hlocal
        change (x'.2.1).1 = .declared row activation configuration at hlocal'
        cases configuration with
        | dagger =>
            simp [ActualPostlaunchFollowerPreparationLocality.preparationSourceCoordinates,
              ActualPostlaunchFollowerMeasurability.localFollower,
              hlocal, hlocal']
        | ordinary state memory =>
            simp [ActualPostlaunchFollowerPreparationLocality.preparationSourceCoordinates,
              ActualPostlaunchFollowerMeasurability.localFollower,
              ActualPostlaunchFollowerMeasurability.localSource,
              ActualBootstrapObservationCode.sourceRows,
              hlocal, hlocal', hrows]
  · cases hlocal : ActualPostlaunchFollowerMeasurability.localFollower x with
    | bootstrap startup =>
        have hlocal' : ActualPostlaunchFollowerMeasurability.localFollower x' =
            .bootstrap startup := hf.symm.trans hlocal
        change (x.2.1).1 = .bootstrap startup at hlocal
        change (x'.2.1).1 = .bootstrap startup at hlocal'
        cases hcase : startup.blockCase with
        | inactive =>
            simp [ActualPostlaunchFollowerObservationLocality.observationSourceCoordinates,
              ActualPostlaunchFollowerMeasurability.localFollower,
              ActualPostlaunchFollowerMeasurability.localTime,
              hlocal, hlocal', hcase]
        | active held privateID gain registers =>
            simp [ActualPostlaunchFollowerObservationLocality.observationSourceCoordinates,
              ActualPostlaunchFollowerMeasurability.localFollower,
              ActualPostlaunchFollowerMeasurability.localSource,
              ActualBootstrapObservationCode.sourceIDs,
              ActualBootstrapObservationCode.sourceRows,
              ActualPostlaunchFollowerMeasurability.localTime,
              hlocal, hlocal', hcase, hids, hrows]
    | declared row activation configuration =>
        have hlocal' : ActualPostlaunchFollowerMeasurability.localFollower x' =
            .declared row activation configuration := hf.symm.trans hlocal
        change (x.2.1).1 = .declared row activation configuration at hlocal
        change (x'.2.1).1 = .declared row activation configuration at hlocal'
        cases configuration with
        | dagger =>
            simp [ActualPostlaunchFollowerObservationLocality.observationSourceCoordinates,
              ActualPostlaunchFollowerMeasurability.localFollower,
              hlocal, hlocal']
        | ordinary state memory =>
            simp [ActualPostlaunchFollowerObservationLocality.observationSourceCoordinates,
              ActualPostlaunchFollowerMeasurability.localFollower,
              ActualPostlaunchFollowerMeasurability.localSource,
              ActualBootstrapObservationCode.sourceRows,
              hlocal, hlocal', hrows]

/-- Equal whole incoming storage, literal public output, and this follower's
current private scalar yield the actual preparation and observation read
envelopes on the two physical inputs. Each input retains its original source. -/
theorem physical_follower_read_envelopes_eq_of_own_coordinates
    {p : ActualPostlaunchFollowerObservationLocality.Parameters}
    {rate : ActualPostlaunchFollowerObservationLocality.RateInput p}
    {block : Fin (n_boot p)} {cursor : Nat}
    (i : Fin (p.m - 1))
    (a b : ActualPostlaunchPhysicalStep.PhysicalInput
      (p := p) (rate := rate) block cursor)
    (hstorage : a.state.followers i = b.state.followers i)
    (hpublic : a.source.1 = b.source.1)
    (hscalar : BootstrapPhysicalInput.playerRoundScalarAt p a.source.2
        (PublicDiscreteDraws.followerPlayer p.two_le_m i) a.time =
      BootstrapPhysicalInput.playerRoundScalarAt p b.source.2
        (PublicDiscreteDraws.followerPlayer p.two_le_m i) b.time) :
    ActualPostlaunchFollowerMeasurability.localFollower
        (ActualPostlaunchStepMeasurability.followerInput i a) =
      ActualPostlaunchFollowerMeasurability.localFollower
        (ActualPostlaunchStepMeasurability.followerInput i b) ∧
    ActualPostlaunchFollowerPreparationLocality.preparationSourceCoordinates
        (rate := rate) a.cursor_lt i
        (ActualPostlaunchStepMeasurability.followerInput i a) =
      ActualPostlaunchFollowerPreparationLocality.preparationSourceCoordinates
        (rate := rate) a.cursor_lt i
        (ActualPostlaunchStepMeasurability.followerInput i b) ∧
    ActualPostlaunchFollowerObservationLocality.observationSourceCoordinates
        (rate := rate) a.cursor_lt i
        (ActualPostlaunchStepMeasurability.followerInput i a) =
      ActualPostlaunchFollowerObservationLocality.observationSourceCoordinates
        (rate := rate) a.cursor_lt i
        (ActualPostlaunchStepMeasurability.followerInput i b) := by
  let x := ActualPostlaunchStepMeasurability.followerInput i a
  let x' := ActualPostlaunchStepMeasurability.followerInput i b
  have hf : ActualPostlaunchFollowerMeasurability.localFollower x =
      ActualPostlaunchFollowerMeasurability.localFollower x' := by
    change a.state.followers i = b.state.followers i
    exact hstorage
  have hsource : (ActualPostlaunchFollowerMeasurability.localSource x).1 =
      (ActualPostlaunchFollowerMeasurability.localSource x').1 := by
    change a.source.1 = b.source.1
    exact hpublic
  have hscalar' : BootstrapPhysicalInput.playerRoundScalarAt p
        (ActualPostlaunchFollowerMeasurability.localSource x).2
        (PublicDiscreteDraws.followerPlayer p.two_le_m i)
        (ActualPostlaunchFollowerMeasurability.localTime block cursor a.cursor_lt) =
      BootstrapPhysicalInput.playerRoundScalarAt p
        (ActualPostlaunchFollowerMeasurability.localSource x').2
        (PublicDiscreteDraws.followerPlayer p.two_le_m i)
        (ActualPostlaunchFollowerMeasurability.localTime block cursor a.cursor_lt) := by
    simpa [x, x', ActualPostlaunchStepMeasurability.followerInput,
      ActualPostlaunchPreparationMeasurability.cursorFollower,
      ActualPostlaunchFollowerMeasurability.localSource,
      ActualPostlaunchFollowerMeasurability.localTime,
      ActualPostlaunchPhysicalStep.PhysicalInput.time,
      ActualInitializationRun.blockTime] using hscalar
  have hcoords := local_read_envelopes_eq_of_own_coordinates
    (rate := rate) a.cursor_lt i x x' hf hsource hscalar'
  exact ⟨hf, hcoords.1, hcoords.2⟩

private theorem mixed_trace_time_bounds
    {p : ActualPostlaunchFollowerObservationLocality.Parameters}
    {rate : ActualPostlaunchFollowerObservationLocality.RateInput p}
    {block : Fin (n_boot p)} {cursor stop : Nat}
    (input : ActualPostlaunchPhysicalStep.PhysicalInput
      (p := p) (rate := rate) block cursor)
    (hlt : cursor < stop) :
    BootstrapObservedFollower.blockStart p block + cursor ≤ input.time.val ∧
      input.time.val < BootstrapObservedFollower.blockStart p block + stop := by
  have htime : input.time.val = BootstrapObservedFollower.blockStart p block + cursor := rfl
  rw [htime]
  exact ⟨le_rfl, by omega⟩

/-- Equal initial own storage, literal public output, own scalar history, and
own finite-grid feedback history imply equality of the entire final follower
state and of its actual played-arm list on the two original mixed traces. -/
theorem follower_state_and_actions_eq_of_own_history
    {p : ActualPostlaunchFollowerObservationLocality.Parameters}
    {rate : ActualPostlaunchFollowerObservationLocality.RateInput p}
    {block : Fin (n_boot p)}
    (i : Fin (p.m - 1))
    {source source' : BootstrapPrivateRoundStreams.SourceInput p}
    {rewards rewards' : ActualPostlaunchPhysicalStep.GridRewardTable p}
    {cursor stop : Nat}
    {s s' : ActualPostlaunchPhysicalStep.PostlaunchState
      (p := p) (rate := rate) block cursor}
    (trace : ActualCompletePhysicalHistory.MixedBlockTrace p rate source rewards
      block cursor s stop)
    (trace' : ActualCompletePhysicalHistory.MixedBlockTrace p rate source' rewards'
      block cursor s' stop)
    (hinitial : s.followers i = s'.followers i)
    (hpublic : source.1 = source'.1)
    (hround : ∀ t : Fin p.T,
      (BootstrapObservedFollower.blockStart p block + cursor ≤ t.val ∧
        t.val < BootstrapObservedFollower.blockStart p block + stop) →
        BootstrapPhysicalInput.playerRoundScalarAt p source.2
            (PublicDiscreteDraws.followerPlayer p.two_le_m i) t =
          BootstrapPhysicalInput.playerRoundScalarAt p source'.2
            (PublicDiscreteDraws.followerPlayer p.two_le_m i) t)
    (hy : trace.records.map (fun r =>
      ActualCompletePhysicalHistory.MixedRoundRecord.feedback r
        (PublicDiscreteDraws.followerPlayer p.two_le_m i)) =
      trace'.records.map (fun r =>
        ActualCompletePhysicalHistory.MixedRoundRecord.feedback r
          (PublicDiscreteDraws.followerPlayer p.two_le_m i))) :
    trace.finalState.followers i = trace'.finalState.followers i ∧
      trace.records.map (fun r =>
        ActualCompletePhysicalHistory.MixedRoundRecord.actions r
          (PublicDiscreteDraws.followerPlayer p.two_le_m i)) =
      trace'.records.map (fun r =>
        ActualCompletePhysicalHistory.MixedRoundRecord.actions r
          (PublicDiscreteDraws.followerPlayer p.two_le_m i)) := by
  induction trace generalizing source' hpublic with
  | done state =>
      cases trace' with
      | done state' =>
          constructor
          · simpa [ActualCompletePhysicalHistory.MixedBlockTrace.finalState] using hinitial
          · simp [ActualCompletePhysicalHistory.MixedBlockTrace.records]
      | @step cursor stop state' input' inputState' inputSource' inputRewards'
          result' resultEq' tail' hlt' =>
          omega
  | @step cursor stop state input inputState inputSource inputRewards
      result resultEq tail hlt ih =>
      cases trace' with
      | done state' =>
          omega
      | @step cursor' stop' state' input' inputState' inputSource' inputRewards'
          result' resultEq' tail' hlt' =>
          have hstorage : input.state.followers i = input'.state.followers i := by
            rw [inputState, inputState']
            exact hinitial
          have hpublicInputs : input.source.1 = input'.source.1 := calc
            input.source.1 = source.1 := congrArg Prod.fst inputSource
            _ = source'.1 := hpublic
            _ = input'.source.1 := (congrArg Prod.fst inputSource').symm
          have hbounds := mixed_trace_time_bounds input hlt
          have hscalar := hround input.time hbounds
          have htime : input.time = input'.time := rfl
          have hscalarInputs : BootstrapPhysicalInput.playerRoundScalarAt p
                input.source.2 (PublicDiscreteDraws.followerPlayer p.two_le_m i) input.time =
              BootstrapPhysicalInput.playerRoundScalarAt p input'.source.2
                (PublicDiscreteDraws.followerPlayer p.two_le_m i) input'.time := by
            simpa [inputSource, inputSource', htime] using hscalar
          have henvelopes := physical_follower_read_envelopes_eq_of_own_coordinates
            (rate := rate) i input input' hstorage hpublicInputs hscalarInputs
          have hheadAction :
              ActualCompletePhysicalHistory.MixedRoundRecord.actions
                  ⟨block, cursor, input, inputSource, inputRewards, result, resultEq⟩
                  (PublicDiscreteDraws.followerPlayer p.two_le_m i) =
                ActualCompletePhysicalHistory.MixedRoundRecord.actions
                  ⟨block, cursor, input', inputSource', inputRewards', result', resultEq'⟩
                  (PublicDiscreteDraws.followerPlayer p.two_le_m i) := by
            have haction :=
              ActualPostlaunchFollowerPreparationLocality.physical_follower_action_eq_of_own_coordinates
                (rate := rate) i input input' henvelopes.1 henvelopes.2.1
            change ActualPostlaunchPhysicalStep.actionProfile result.prepared _ =
              ActualPostlaunchPhysicalStep.actionProfile result'.prepared _
            rw [resultEq, resultEq']
            change ActualPostlaunchPhysicalStep.actionProfile
                (ActualPostlaunchPhysicalStep.prepare input) _ =
              ActualPostlaunchPhysicalStep.actionProfile
                (ActualPostlaunchPhysicalStep.prepare input') _
            exact haction
          have hyCons :
              ActualCompletePhysicalHistory.MixedRoundRecord.feedback
                  ⟨block, cursor, input, inputSource, inputRewards, result, resultEq⟩
                  (PublicDiscreteDraws.followerPlayer p.two_le_m i) ::
                tail.records.map (fun r =>
                  ActualCompletePhysicalHistory.MixedRoundRecord.feedback r
                    (PublicDiscreteDraws.followerPlayer p.two_le_m i)) =
              ActualCompletePhysicalHistory.MixedRoundRecord.feedback
                  ⟨block, cursor, input', inputSource', inputRewards', result', resultEq'⟩
                  (PublicDiscreteDraws.followerPlayer p.two_le_m i) ::
                tail'.records.map (fun r =>
                  ActualCompletePhysicalHistory.MixedRoundRecord.feedback r
                    (PublicDiscreteDraws.followerPlayer p.two_le_m i)) := by
            simpa only [ActualCompletePhysicalHistory.MixedBlockTrace.records,
              List.map_cons] using hy
          obtain ⟨hyHead, hyTail⟩ := List.cons.inj hyCons
          have hfeedback :
              ActualPostlaunchFollowerMeasurability.localFeedback
                  (ActualPostlaunchStepMeasurability.followerInput i input) =
                ActualPostlaunchFollowerMeasurability.localFeedback
                  (ActualPostlaunchStepMeasurability.followerInput i input') := by
            change ActualPostlaunchPhysicalStep.physicalFeedback
                  (ActualPostlaunchPhysicalStep.prepare input)
                  (PublicDiscreteDraws.followerPlayer p.two_le_m i) =
                ActualPostlaunchPhysicalStep.physicalFeedback
                  (ActualPostlaunchPhysicalStep.prepare input')
                  (PublicDiscreteDraws.followerPlayer p.two_le_m i)
            change ActualPostlaunchPhysicalStep.physicalFeedback result.prepared _ =
              ActualPostlaunchPhysicalStep.physicalFeedback result'.prepared _ at hyHead
            rw [resultEq, resultEq'] at hyHead
            change ActualPostlaunchPhysicalStep.physicalFeedback
                (ActualPostlaunchPhysicalStep.prepare input) _ =
              ActualPostlaunchPhysicalStep.physicalFeedback
                (ActualPostlaunchPhysicalStep.prepare input') _ at hyHead
            exact hyHead
          have hnext :=
            ActualPostlaunchFollowerObservationLocality.physical_follower_next_eq_of_own_coordinates
              (rate := rate) i input input' henvelopes.1 henvelopes.2.1
              henvelopes.2.2 hfeedback
          have hstorageNext : result.nextState.followers i = result'.nextState.followers i := by
            rw [resultEq, resultEq']
            exact hnext
          have hroundTail : ∀ t : Fin p.T,
              (BootstrapObservedFollower.blockStart p block + (cursor + 1) ≤ t.val ∧
                t.val < BootstrapObservedFollower.blockStart p block + stop) →
                BootstrapPhysicalInput.playerRoundScalarAt p source.2
                    (PublicDiscreteDraws.followerPlayer p.two_le_m i) t =
                  BootstrapPhysicalInput.playerRoundScalarAt p source'.2
                    (PublicDiscreteDraws.followerPlayer p.two_le_m i) t := by
            intro t ht
            apply hround t
            exact ⟨by omega, ht.2⟩
          have htail := ih tail' hstorageNext
            hpublic hroundTail hyTail
          constructor
          · simpa [ActualCompletePhysicalHistory.MixedBlockTrace.finalState] using htail.1
          · change
              ActualCompletePhysicalHistory.MixedRoundRecord.actions
                  ⟨block, cursor, input, inputSource, inputRewards, result, resultEq⟩
                  (PublicDiscreteDraws.followerPlayer p.two_le_m i) ::
                tail.records.map (fun r =>
                  ActualCompletePhysicalHistory.MixedRoundRecord.actions r
                    (PublicDiscreteDraws.followerPlayer p.two_le_m i)) =
              ActualCompletePhysicalHistory.MixedRoundRecord.actions
                  ⟨block, cursor, input', inputSource', inputRewards', result', resultEq'⟩
                  (PublicDiscreteDraws.followerPlayer p.two_le_m i) ::
                tail'.records.map (fun r =>
                  ActualCompletePhysicalHistory.MixedRoundRecord.actions r
                    (PublicDiscreteDraws.followerPlayer p.two_le_m i))
            exact congrArg₂ List.cons hheadAction htail.2

/-- At the cursor immediately after an actual trace, equal own history and
the current own scalar determine the next played arm. The trace supplies only
strictly earlier feedback; current feedback is not required. -/
theorem physical_follower_action_eq_after_own_history
    {p : ActualPostlaunchFollowerObservationLocality.Parameters}
    {rate : ActualPostlaunchFollowerObservationLocality.RateInput p}
    {block : Fin (n_boot p)}
    (i : Fin (p.m - 1))
    {source source' : BootstrapPrivateRoundStreams.SourceInput p}
    {rewards rewards' : ActualPostlaunchPhysicalStep.GridRewardTable p}
    {cursor stop : Nat}
    {s s' : ActualPostlaunchPhysicalStep.PostlaunchState
      (p := p) (rate := rate) block cursor}
    (trace : ActualCompletePhysicalHistory.MixedBlockTrace p rate source rewards
      block cursor s stop)
    (trace' : ActualCompletePhysicalHistory.MixedBlockTrace p rate source' rewards'
      block cursor s' stop)
    (hinitial : s.followers i = s'.followers i)
    (hpublic : source.1 = source'.1)
    (hround : ∀ t : Fin p.T,
      (BootstrapObservedFollower.blockStart p block + cursor ≤ t.val ∧
        t.val < BootstrapObservedFollower.blockStart p block + stop) →
        BootstrapPhysicalInput.playerRoundScalarAt p source.2
            (PublicDiscreteDraws.followerPlayer p.two_le_m i) t =
          BootstrapPhysicalInput.playerRoundScalarAt p source'.2
            (PublicDiscreteDraws.followerPlayer p.two_le_m i) t)
    (hy : trace.records.map (fun r =>
      ActualCompletePhysicalHistory.MixedRoundRecord.feedback r
        (PublicDiscreteDraws.followerPlayer p.two_le_m i)) =
      trace'.records.map (fun r =>
        ActualCompletePhysicalHistory.MixedRoundRecord.feedback r
          (PublicDiscreteDraws.followerPlayer p.two_le_m i)))
    (a b : ActualPostlaunchPhysicalStep.PhysicalInput
      (p := p) (rate := rate) block stop)
    (hstate : a.state = trace.finalState)
    (hstate' : b.state = trace'.finalState)
    (hsource : a.source = source)
    (hsource' : b.source = source')
    (hcurrent : BootstrapPhysicalInput.playerRoundScalarAt p source.2
        (PublicDiscreteDraws.followerPlayer p.two_le_m i) a.time =
      BootstrapPhysicalInput.playerRoundScalarAt p source'.2
        (PublicDiscreteDraws.followerPlayer p.two_le_m i) b.time) :
    ActualPostlaunchPhysicalStep.actionProfile (ActualPostlaunchPhysicalStep.prepare a)
        (PublicDiscreteDraws.followerPlayer p.two_le_m i) =
      ActualPostlaunchPhysicalStep.actionProfile (ActualPostlaunchPhysicalStep.prepare b)
        (PublicDiscreteDraws.followerPlayer p.two_le_m i) := by
  have hfinal := follower_state_and_actions_eq_of_own_history i trace trace'
    hinitial hpublic hround hy
  have hstorage : a.state.followers i = b.state.followers i := by
    rw [hstate, hstate']
    exact hfinal.1
  have hpublicInputs : a.source.1 = b.source.1 := calc
    a.source.1 = source.1 := congrArg Prod.fst hsource
    _ = source'.1 := hpublic
    _ = b.source.1 := (congrArg Prod.fst hsource').symm
  have hscalar : BootstrapPhysicalInput.playerRoundScalarAt p a.source.2
        (PublicDiscreteDraws.followerPlayer p.two_le_m i) a.time =
      BootstrapPhysicalInput.playerRoundScalarAt p b.source.2
        (PublicDiscreteDraws.followerPlayer p.two_le_m i) b.time := by
    simpa [hsource, hsource'] using hcurrent
  have henvelopes := physical_follower_read_envelopes_eq_of_own_coordinates
    (rate := rate) i a b hstorage hpublicInputs hscalar
  exact ActualPostlaunchFollowerPreparationLocality.physical_follower_action_eq_of_own_coordinates
      (rate := rate) i a b henvelopes.1 henvelopes.2.1

end Bandits.Support.ActualPostlaunchBlockFollowerLocality

end
