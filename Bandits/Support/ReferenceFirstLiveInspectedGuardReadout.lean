/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveGuardedConditionalService
public import Bandits.Support.ReferenceSourceOwnHistoryContainment

/-!
# Inspecting the literal first-live guard

Sources: `sources/zip4/manuscript/05_binary_transport.tex:74-124,293-348`,
`sources/zip4/manuscript/06_interruptions.tex:391-426`,
`sources/zip4/manuscript/07_public_setup.tex:127-164`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-79`.

The observations use the existing lossless state code and the explicitly enlarged
analysis field. They do not define an operational policy or identify a logical
filtration. Whole rewards, continuous payloads, and original private arrays are
retained. All results in this file are internal deterministic statements.

The next consumer is `ReferenceFirstLiveInspectedCoefficients`, followed by
`ReferenceFirstLiveInspectedConditionalService` and the finite-support waiting
join. Coefficient adaptation, inspected conditional expectations, stopping laws,
numerical replay, and manuscript closure are outside this module.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open scoped Classical

namespace Bandits.Support.ReferenceFirstLiveInspectedGuardReadout


abbrev SourceInput := BootstrapPrivateRoundStreams.SourceInput

variable {p : Parameters} {rate : ReferenceActivePhysicalStep.RateInput p}

/-- FIRST is the literal left constructor of the existing coordinator code.
An absent incoming observation fails this test. -/
def incomingFirst (code : Option (ReferenceActivePhysicalStepMeasurability.StateCode p rate)) : Bool :=
  match code with
  | some (.inl _, _) => true
  | _ => false

/-- LIVE is the literal middle-left constructor, including its entire payload
and live registers. An absent incoming observation fails this test. -/
def incomingLive (code : Option (ReferenceActivePhysicalStepMeasurability.StateCode p rate)) : Bool :=
  match code with
  | some (.inr (.inl _), _) => true
  | _ => false

private theorem measurable_incomingFirst :
    Measurable (incomingFirst (p := p) (rate := rate)) := by
  have htag : Measurable (fun c : ReferenceActivePhysicalStepMeasurability.StateCode p rate =>
      Sum.elim (fun _ : Unit => true) (fun _ => false) c.1) :=
    (measurable_const.sumElim measurable_const).comp measurable_fst
  have hm := ReferenceCollectionInstallOutputMeasurability.measurable_optionMapDependent
    (fun v : ReferenceActivePhysicalStepMeasurability.StateCode p rate × Option (ReferenceActivePhysicalStepMeasurability.StateCode p rate) =>
      Sum.elim (fun _ : Unit => true) (fun _ => false) v.1.1)
    (htag.comp measurable_fst) id measurable_id
  have h := (show Measurable (fun b : Option Bool => b.getD false) from by
    have h := (show Measurable (Sum.elim id (fun _ : PUnit => false) : Bool ⊕ PUnit → Bool) from
      measurable_id.sumElim measurable_const).comp
      (comap_measurable (Equiv.optionEquivSumPUnit Bool))
    convert h using 1
    funext b
    cases b <;> rfl).comp hm
  convert h using 1
  funext c
  cases c with
  | none => rfl
  | some c => rcases c with ⟨coord, rest⟩; cases coord <;> rfl

private theorem measurable_incomingLive :
    Measurable (incomingLive (p := p) (rate := rate)) := by
  have htag : Measurable (fun c : ReferenceActivePhysicalStepMeasurability.StateCode p rate =>
      Sum.elim (fun _ : Unit => false)
        (Sum.elim (fun _ => true) (fun _ => false)) c.1) :=
    (measurable_const.sumElim
      (measurable_const.sumElim measurable_const)).comp measurable_fst
  have hm := ReferenceCollectionInstallOutputMeasurability.measurable_optionMapDependent
    (fun v : ReferenceActivePhysicalStepMeasurability.StateCode p rate × Option (ReferenceActivePhysicalStepMeasurability.StateCode p rate) =>
      Sum.elim (fun _ : Unit => false)
        (Sum.elim (fun _ => true) (fun _ => false)) v.1.1)
    (htag.comp measurable_fst) id measurable_id
  have h := (show Measurable (fun b : Option Bool => b.getD false) from by
    have h := (show Measurable (Sum.elim id (fun _ : PUnit => false) : Bool ⊕ PUnit → Bool) from
      measurable_id.sumElim measurable_const).comp
      (comap_measurable (Equiv.optionEquivSumPUnit Bool))
    convert h using 1
    funext b
    cases b <;> rfl).comp hm
  convert h using 1
  funext c
  cases c with
  | none => rfl
  | some c =>
      rcases c with ⟨coord, rest⟩
      cases coord with
      | inl u => rfl
      | inr tail => cases tail <;> rfl

/-- The first test reads exactly the original coordinator constructor. -/
theorem incomingFirst_encode (state : ReferenceActivePhysicalStep.State p rate) :
    incomingFirst (some (ReferenceActivePhysicalStepMeasurability.encodeState state)) = true ↔ state.coordinator = .first := by
  cases hc : state.coordinator <;> simp [incomingFirst, ReferenceActivePhysicalStepMeasurability.encodeState,
    ReferenceActivePhysicalStepMeasurability.encodeCoordinator, hc]

/-- The live test reads exactly the original coordinator constructor. -/
theorem incomingLive_encode (state : ReferenceActivePhysicalStep.State p rate) :
    incomingLive (some (ReferenceActivePhysicalStepMeasurability.encodeState state)) = true ↔
      ∃ r owned base, state.coordinator = .live r owned base := by
  cases hc : state.coordinator <;> simp [incomingLive, ReferenceActivePhysicalStepMeasurability.encodeState,
    ReferenceActivePhysicalStepMeasurability.encodeCoordinator, hc]

variable (rate) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)

/-- Entry adaptation follows from the actual incoming observation and the
existing local decoder, with absence and false gates kept distinct. -/
theorem entry_measurable_in_inspectedHistorySpace
    (n : ℕ) (hn : n ≤ p.T) (t : Fin p.T) (ht : t.val ≤ n) (b : ℕ) :
    Measurable[ReferenceSourceOwnHistoryContainment.inspectedHistorySpace rate rewards C_star C_h n hn]
      (ReferenceSourcePrefixHistoryFiltration.entry rate rewards C_star C_h b t) := by
  let : MeasurableSpace (SourceInput p) :=
    ReferenceSourceOwnHistoryContainment.inspectedHistorySpace rate rewards C_star C_h n hn
  exact ReferenceCollectionInstallOutputMeasurability.measurable_optionMapDependent
    (fun v : ReferenceActivePhysicalStepMeasurability.StateCode p rate × SourceInput p =>
      ReferenceRetainedReleasePhaseObservation.localReleaseEntry rate b t v.1)
    ((ReferenceReleaseStrictPastFactor.measurable_localReleaseEntry rate b t).comp
      measurable_fst) _
    (ReferenceSourceOwnHistoryContainment.incoming_measurable_in_inspectedHistorySpace rate rewards C_star C_h n hn t ht)

/-- The finite pending set is the literal optional-entry projection. -/
theorem pending_measurable_in_inspectedHistorySpace
    (n : ℕ) (hn : n ≤ p.T) (t : Fin p.T) (ht : t.val ≤ n) (b : ℕ) :
    Measurable[ReferenceSourceOwnHistoryContainment.inspectedHistorySpace rate rewards C_star C_h n hn]
      (ReferenceSourcePrefixHistoryFiltration.pending rate rewards C_star C_h b t) := by
  have hget : Measurable (fun e : Option (Finset (Fin (p.m - 1))) => e.getD ∅) := by
    have h := (Measurable.sumElim measurable_id measurable_const :
      Measurable (Sum.elim id (fun _ : PUnit => (∅ : Finset (Fin (p.m - 1)))))).comp
        (comap_measurable (Equiv.optionEquivSumPUnit (Finset (Fin (p.m - 1)))))
    convert h using 1
    funext e
    cases e <;> rfl
  have hread : Measurable (fun e : Option (Bool × Option (Finset (Fin (p.m - 1)))) =>
      (e.bind Prod.snd).getD ∅) := by
    have hsum : Measurable (Sum.elim
        (fun e : Bool × Option (Finset (Fin (p.m - 1))) => e.2.getD ∅)
        (fun _ : PUnit => (∅ : Finset (Fin (p.m - 1))))) :=
      (hget.comp measurable_snd).sumElim measurable_const
    have h := hsum.comp (comap_measurable (Equiv.optionEquivSumPUnit
      (Bool × Option (Finset (Fin (p.m - 1))))))
    convert h using 1
    funext e
    cases e <;> rfl
  exact hread.comp
    (entry_measurable_in_inspectedHistorySpace rate rewards C_star C_h n hn t ht b)

/-- The actual release support is measurable from its entry and pending
observations alone. This does not assert first-live support coverage. -/
theorem releaseSupport_measurable_in_inspectedHistorySpace
    (n : ℕ) (hn : n ≤ p.T) (t : Fin p.T) (ht : t.val ≤ n)
    (i : Fin (p.m - 1)) (b : ℕ) :
    MeasurableSet[ReferenceSourceOwnHistoryContainment.inspectedHistorySpace rate rewards C_star C_h n hn]
      (ReferenceSourcePhysicalFlagConditionalLaw.actualReleaseSupport
        rate rewards C_star C_h b t i) := by
  let : MeasurableSpace (SourceInput p) :=
    ReferenceSourceOwnHistoryContainment.inspectedHistorySpace rate rewards C_star C_h n hn
  have he := entry_measurable_in_inspectedHistorySpace rate rewards C_star C_h n hn t ht b
  have hp := pending_measurable_in_inspectedHistorySpace rate rewards C_star C_h n hn t ht b
  have hg : Measurable (fun e : Option (Bool × Option (Finset (Fin (p.m - 1)))) =>
      e.map Prod.fst) :=
    ReferenceCollectionInstallOutputMeasurability.measurable_optionMapDependent
      (fun v : (Bool × Option (Finset (Fin (p.m - 1)))) ×
          Option (Bool × Option (Finset (Fin (p.m - 1)))) => v.1.1)
      (measurable_fst.comp measurable_fst) _ measurable_id
  have hd : Measurable (fun v : Option Bool => v.getD false) := by
    have h := (show Measurable (Sum.elim id (fun _ : PUnit => false) : Bool ⊕ PUnit → Bool)
        from measurable_id.sumElim measurable_const).comp
      (comap_measurable (Equiv.optionEquivSumPUnit Bool))
    convert h using 1
    funext v
    cases v <;> rfl
  have heq : {z : SourceInput p | (ReferenceSourcePrefixHistoryFiltration.entry
      rate rewards C_star C_h b t z).map Prod.fst = some true} =
      {z | ((ReferenceSourcePrefixHistoryFiltration.entry
        rate rewards C_star C_h b t z).map Prod.fst).getD false = true} := by
    ext z
    cases he : ReferenceSourcePrefixHistoryFiltration.entry rate rewards C_star C_h b t z with
    | none => simp [he]
    | some pair => rcases pair with ⟨flag, pending⟩; cases flag <;> simp [he]
  have hset : MeasurableSet {z : SourceInput p |
      ((ReferenceSourcePrefixHistoryFiltration.entry
        rate rewards C_star C_h b t z).map Prod.fst).getD false = true} :=
    (hd.comp (hg.comp he)) (MeasurableSet.singleton true)
  rw [← heq] at hset
  exact hset.inter (hp (measurableSet_mem_finset i))

variable {rate}

private theorem livePostChoice_configuration_ne_first
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
    (base : Fin (p.m - 1) → ℕ) (started : CoordinatorPhaseClock.StartRoundResult p) :
    (ReferenceActivePhysicalStep.livePostChoice prepared registers owned base started).configuration ≠
      .first := by
  unfold ReferenceActivePhysicalStep.livePostChoice
  cases hrecord : CoordinatorRecorderComplementBridge.run
      (ReferenceActivePhysicalStep.liveRecordingInput prepared registers started) with
  | none => simp [ReferenceActivePhysicalStep.coordinatorFailure]
  | some recording =>
      cases hservice : CoordinatorLiveServiceFinish.servicePass registers owned recording with
      | error reason => simp [hservice, ReferenceActivePhysicalStep.coordinatorFailure]
      | ok serviced =>
          cases hconfirmation : CoordinatorLocalArmChoice.confirmationUpdate registers.payload
              started.pending (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
              x.time x.row prepared.coordinatorObservation with
          | none => simp [hservice, ReferenceActivePhysicalStep.coordinatorFailure]
          | some pending =>
              cases hfinish : CoordinatorPhaseClock.finishRound p rate.eta.val x.time
                  started.clock pending x.row with
              | error reason => simp [hservice, hfinish,
                  ReferenceActivePhysicalStep.coordinatorFailure]
              | ok finished => simp [hservice, hfinish]

private theorem collectionFinish_configuration_ne_first
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (recording : CoordinatorRecordingOperation.Output p)
    (cut : ReferenceActivePhysicalStep.UpCut p rate) :
    (ReferenceActivePhysicalStep.collectionFinish (x := x) payload started recording cut).configuration ≠
      .first := by
  unfold ReferenceActivePhysicalStep.collectionFinish
  cases hresult : cut.result with
  | invalid => simp [ReferenceActivePhysicalStep.coordinatorFailure]
  | success pair =>
      rcases pair with ⟨ledger, bank⟩
      cases hledger : CoordinatorCollectionLedger.finishRound ledger with
      | invalid => simp [hledger, ReferenceActivePhysicalStep.coordinatorFailure]
      | rejected rejected => simp [hledger, ReferenceActivePhysicalStep.coordinatorFailure]
      | success finishedLedger =>
          cases hclock : CoordinatorPhaseClock.finishRound p rate.eta.val x.time
              started.clock finishedLedger.pending x.row with
          | error reason => simp [hledger, hclock,
              ReferenceActivePhysicalStep.coordinatorFailure]
          | ok finishedClock => simp [hledger, hclock]
  | rejected pair =>
      rcases pair with ⟨ledger, bank⟩
      cases hledger : CoordinatorCollectionLedger.finishRound ledger with
      | invalid => simp [hledger, ReferenceActivePhysicalStep.coordinatorFailure]
      | rejected rejected => simp [hledger, ReferenceActivePhysicalStep.coordinatorFailure]
      | success finishedLedger =>
          cases hclock : CoordinatorPhaseClock.finishRound p rate.eta.val x.time
              started.clock finishedLedger.pending x.row with
          | error reason => simp [hledger, hclock,
              ReferenceActivePhysicalStep.coordinatorFailure]
          | ok finishedClock => simp [hledger, hclock]

private theorem collectionPostChoice_configuration_ne_first
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ) :
    (ReferenceActivePhysicalStep.collectionPostChoice prepared payload ledger started weights).configuration ≠
      .first := by
  unfold ReferenceActivePhysicalStep.collectionPostChoice
  cases hrecord : CoordinatorRecorderComplementBridge.run
      (ReferenceActivePhysicalStep.collectionRecordingInput prepared payload started weights) with
  | none => simp [ReferenceActivePhysicalStep.coordinatorFailure]
  | some recording =>
      cases hstart : CoordinatorCollectionLedger.startRound ledger (x.time.val + 1)
          (ReferenceActivePhysicalStep.collectionEnabled ledger x.time)
          (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) with
      | invalid => simp [hstart, ReferenceActivePhysicalStep.coordinatorFailure]
      | rejected rejected => simp [hstart, ReferenceActivePhysicalStep.coordinatorFailure]
      | success startedLedger =>
          simpa [hrecord, hstart] using
            (collectionFinish_configuration_ne_first (x := x) payload started recording
              (ReferenceActivePhysicalStep.receiveUp prepared startedLedger))

private theorem step_coordinator_ne_first (x : ReferenceActivePhysicalStep.RoundInput p rate) :
    (ReferenceActivePhysicalStep.step x).next.coordinator ≠ .first := by
  rw [(ReferenceActivePhysicalStep.step_next_fields x).1]
  cases hcoord : (ReferenceActivePhysicalStep.prepare x).coordinator with
  | dagger =>
      simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
        ReferenceActivePhysicalStep.DispatchCut.selection, hcoord]
  | first outcome =>
      have hobserve := ReferenceActivePhysicalStep.observeCoordinator_first_equation
        (ReferenceActivePhysicalStep.prepare x) outcome hcoord
      by_cases hnone : (ReferenceActivePhysicalStep.DispatchCut.first outcome).selection = none
      · rw [hobserve, ite_eq_left hnone]
        simp [ReferenceActivePhysicalStep.coordinatorFailure]
      · rw [hobserve, ite_eq_right hnone]
        cases outcome with
        | chosen installed choice =>
            exact livePostChoice_configuration_ne_first
              (ReferenceActivePhysicalStep.prepare x) installed.registers installed.ownedRegisters
              installed.followerBaseScore installed.startRoundResult
        | _ => simp [ReferenceActivePhysicalStep.DispatchCut.selection] at hnone
  | live registers owned base outcome =>
      have hobserve := ReferenceActivePhysicalStep.observeCoordinator_live_equation
        (ReferenceActivePhysicalStep.prepare x) registers owned base outcome hcoord
      by_cases hnone : (ReferenceActivePhysicalStep.DispatchCut.live registers owned base outcome).selection = none
      · rw [hobserve, ite_eq_left hnone]
        simp [ReferenceActivePhysicalStep.coordinatorFailure]
      · rw [hobserve, ite_eq_right hnone]
        cases outcome with
        | continuingChosen dispatched startRound continuation choice =>
            exact livePostChoice_configuration_ne_first
              (ReferenceActivePhysicalStep.prepare x) (ReferenceActivePhysicalStep.liveRegistersAt registers x.time)
              (ReferenceActivePhysicalStep.liveOwnedAt registers owned x.time) base dispatched.startResult
        | cutoffChosen dispatched startRound ledger initialization ledgerCandidate domain clock pending noAssignment choice =>
            exact collectionPostChoice_configuration_ne_first
              (ReferenceActivePhysicalStep.prepare x) registers.payload
              (ReferenceActivePhysicalStep.sharedLedger ledger) dispatched.startResult
              (ReferenceActivePhysicalStep.liveRegistersAt registers x.time).complementWeights
        | _ => simp [ReferenceActivePhysicalStep.DispatchCut.selection] at hnone
  | collection payload ledger clock cutoff outcome =>
      have hobserve := ReferenceActivePhysicalStep.observeCoordinator_collection_equation
        (ReferenceActivePhysicalStep.prepare x) payload ledger clock cutoff outcome hcoord
      by_cases hnone : (ReferenceActivePhysicalStep.DispatchCut.collection payload ledger clock cutoff outcome).selection = none
      · rw [hobserve, ite_eq_left hnone]
        simp [ReferenceActivePhysicalStep.coordinatorFailure]
      · rw [hobserve, ite_eq_right hnone]
        cases outcome with
        | continuing core prepared boundary currentScores =>
            exact collectionPostChoice_configuration_ne_first
              (ReferenceActivePhysicalStep.prepare x) payload ledger prepared.clockStarted
              (CoordinatorCollectionInteractive.PreObservationInputs.weights
                (ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff)
                prepared.inputsValid.ledger_valid prepared.inputsValid.assignment_eq)
        | laterChosen core consistent started startRound instruction assignmentStart output consistency clockData installed choice =>
            exact livePostChoice_configuration_ne_first
              (ReferenceActivePhysicalStep.prepare x) installed.registers installed.ownedRegisters
              installed.retainedBaseScore started
        | _ => simp [ReferenceActivePhysicalStep.DispatchCut.selection] at hnone
  | invalidCollectionCutoff =>
      simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
        ReferenceActivePhysicalStep.DispatchCut.selection, hcoord,
        ReferenceActivePhysicalStep.coordinatorFailure]

private theorem run_prefix_final_coordinator_first_only
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start totalCount : ℕ) (hspan : start + totalCount ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (prefixLength : ℕ) (hprefix : prefixLength ≤ totalCount)
    (hcoord : (ReferenceActivePhysicalHorizon.run initial rows J rewards start prefixLength
      (by omega) active).finalState.coordinator = .first) :
    prefixLength = 0 := by
  cases prefixLength with
  | zero => rfl
  | succ prefixLength =>
      have hfinal := ReferenceAssignmentPayloadChronology.run_successor_finalState_eq_actualRunRecordAt
        initial rows J rewards start prefixLength (by omega) active
      have hrecord : ReferenceAssignmentPayloadChronology.actualRunRecordAt initial rows J rewards
          start prefixLength (by omega) active =
            ReferenceAssignmentPayloadChronology.actualStepRecord
              (ReferenceCollectionPhaseHistory.nextInput initial rows J rewards start prefixLength
                (by omega) active) := rfl
      rw [hfinal, hrecord] at hcoord
      exact (step_coordinator_ne_first _ hcoord).elim

/-- FIRST at an actual incoming calendar coordinate is the corrected launch
itself. Every physical successor constructor has been excluded, including
failure, collection, and later-installation branches. -/
theorem incomingFirst_actual_launch
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (time : Fin p.T) (z : SourceInput p)
    (hfirst : incomingFirst
      (ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h time z) = true) :
    (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true ∧
      ReferenceInitializationRun.elapsed p
        (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed =
        time.val := by
  have hby : ReferenceSourcePrefixHistoryFiltration.actualLaunchBy
      rate rewards C_star C_h time.val z := by
    by_contra hnot
    rw [ReferenceSourcePrefixHistoryFiltration.incoming,
      ReferenceSourcePrefixHistoryFiltration.actualRecord_eq_none_of_not_launchBy
        rate rewards C_star C_h time z hnot] at hfirst
    cases hfirst
  let seed := ReferenceLocalReleaseGateChronology.sourceSeed rate z rewards C_star C_h hby.1
  have hlaunch := ReferenceLocalReleaseGateChronology.sourceSeed_launch
    rate z rewards C_star C_h hby.1
  rw [ReferenceSourcePrefixHistoryFiltration.incoming,
    ReferenceSourcePrefixHistoryFiltration.actualRecord_on_launch
      rate rewards C_star C_h time z seed hlaunch hby.2,
    Option.map_some] at hfirst
  have hcoord := (incomingFirst_encode _).mp hfirst
  have hzero := run_prefix_final_coordinator_first_only seed z.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards
    (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
    (time.val - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
    (by have ht := time.isLt; have hs := hby.2; omega)
    (ReferenceCompletePhysicalHistory.activeMode_of_launch_eq_some
      rate z rewards C_star C_h seed hlaunch)
    (time.val - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
    le_rfl hcoord
  exact ⟨hby.1, Nat.le_antisymm hby.2 (Nat.sub_eq_zero_iff_le.mp hzero)⟩

open ReferenceActivePhysicalStep

private theorem collection_finish_not_live (x : RoundInput p rate) (payload : Payload rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (recording : CoordinatorRecordingOperation.Output p) (cut : UpCut p rate)
    (next : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters next) (base : Fin (p.m - 1) → ℕ) :
    (collectionFinish (x := x) payload started recording cut).configuration ≠ .live next owned base := by
  unfold collectionFinish
  split
  · simp only [coordinatorFailure, ne_eq, reduceCtorEq, not_false_eq_true]
  all_goals dsimp only
  all_goals repeat' split
  all_goals simp only [coordinatorFailure, ne_eq, reduceCtorEq, not_false_eq_true]

private theorem collection_tail_not_live (x : RoundInput p rate) (prepared : PreparedRound x)
    (payload : Payload rate) (ledger : Ledger rate) (started : CoordinatorPhaseClock.StartRoundResult p)
    (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ)
    (next : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters next) (base : Fin (p.m - 1) → ℕ) :
    (collectionPostChoice prepared payload ledger started weights).configuration ≠ .live next owned base := by
  unfold collectionPostChoice
  split
  · simp only [coordinatorFailure, ne_eq, reduceCtorEq, not_false_eq_true]
  · dsimp only
    split
    · simp only [coordinatorFailure, ne_eq, reduceCtorEq, not_false_eq_true]
    · simp only [coordinatorFailure, ne_eq, reduceCtorEq, not_false_eq_true]
    · exact collection_finish_not_live x payload started _ _ next owned base

private theorem cutoff_next_not_live (x : RoundInput p rate)
    (hcut : ReferenceCollectionPhaseHistory.cutoffChosen x = true)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters r) (base : Fin (p.m - 1) → ℕ) :
    (step x).next.coordinator ≠ .live r owned base := by
  rw [(step_next_fields x).1]
  cases hd : (prepare x).coordinator with
  | live old oldOwned oldBase outcome =>
      cases outcome with
      | cutoffChosen d hstart ledger hi he hv hc hp ha arm =>
          rw [observeCoordinator_live_equation (prepare x) old oldOwned oldBase _ hd]
          split
          · simp only [coordinatorFailure, ne_eq, reduceCtorEq, not_false_eq_true]
          · exact collection_tail_not_live x (prepare x) old.payload (sharedLedger ledger)
              d.startResult (liveRegistersAt old x.time).complementWeights r owned base
      | _ => simp only [ReferenceCollectionPhaseHistory.cutoffChosen, hd] at hcut; cases hcut
  | _ => simp only [ReferenceCollectionPhaseHistory.cutoffChosen, hd] at hcut; cases hcut

private theorem gate_no_cutoff (x : RoundInput p rate) (b : ℕ)
    (hg : ReferenceRetainedReleasePhaseObservation.localReleaseGate rate b x.time
      (ReferenceActivePhysicalStepMeasurability.encodeState x.state) = true) :
    ReferenceCollectionPhaseHistory.cutoffChosen x = false := by
  obtain ⟨r, owned, base, hc, _, _, _, hu⟩ :=
    ReferenceLocalReleaseGateChronology.gate_live b x.time x.state hg
  have hd : (prepare x).coordinator = .live r owned base
      (CoordinatorRoundDispatch.dispatchLive (liveInput x r owned base)) := by
    simp only [prepare, dispatch, hc, CoordinatorRoundDispatch.dispatch]
    rfl
  cases ho : CoordinatorRoundDispatch.dispatchLive (liveInput x r owned base) with
  | cutoffChosen d hstart ledger hi he hv hclock hp ha arm =>
      have hstart' : CoordinatorPhaseClock.startRound p rate.eta.val x.time
          r.priorClock r.clockPending = .ok d.startResult := hstart
      have hdecode := ReferenceActivePhysicalStepMeasurability.decodeCoordinator_encodeCoordinator
        (.live r owned base : CoordinatorConfiguration p rate)
      have hframe : CoordinatorLiveChoiceRecorderStep.unchangedLiveClockFrame
          (liveRegistersAt r x.time) d.startResult := by
        have hrec : ReferenceActivePhysicalStepMeasurability.decodeLiveRegisters r.payload
            (ReferenceActivePhysicalStepMeasurability.encodeLive r owned base) = r := by
          have h := congrArg (fun c : CoordinatorConfiguration p rate =>
            match c with | .live rr _ _ => some rr | _ => none) hdecode
          exact Option.some.inj h
        have hstartCode : ReferenceRetainedReleasePhaseObservation.localReleaseStartResult
            rate x.time (ReferenceActivePhysicalStepMeasurability.encodeLive r owned base) =
              .ok d.startResult := by
          rw [ReferenceRetainedReleasePhaseObservation.localReleaseStartResult_eq_decoded
            rate x.time r.payload _, hrec]
          exact hstart'
        simp only [ReferenceRetainedReleasePhaseObservation.localReleaseGate,
          ReferenceActivePhysicalStepMeasurability.encodeState, hc,
          ReferenceActivePhysicalStepMeasurability.encodeCoordinator, hstartCode,
          Bool.and_eq_true, decide_eq_true_eq] at hg
        have hf := hg.2
        rw [hrec] at hf
        exact hf
      have hnone : d.startResult.clock.u = none := hframe.1 ▸ hu
      have hsome : d.startResult.clock.u = some x.time :=
        congrArg CoordinatorPhaseClock.ClockRegisters.u hclock
      rw [hnone] at hsome
      cases hsome
  | _ => simp only [ReferenceCollectionPhaseHistory.cutoffChosen, hd, ho]

private theorem window_index_of_live_prefix
    (initial : State p rate) (rows : CompletePublicTable.CompleteRows p)
    (J : Fin (M p)) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start n : ℕ) (hspan : start + (n + 1) ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hfirst : initial.coordinator = .first)
    (hlive : ∀ k (_hpos : 0 < k) (hk : k ≤ n),
      ∃ r owned base, (ReferenceActivePhysicalHorizon.run initial rows J rewards
        start k (by omega) active).finalState.coordinator = .live r owned base)
    (b : ℕ)
    (hg : ReferenceRetainedReleasePhaseObservation.localReleaseGate rate b
      ⟨start + n, by omega⟩ (ReferenceActivePhysicalStepMeasurability.encodeState
        (ReferenceActivePhysicalHorizon.run initial rows J rewards start n
          (by omega) active).finalState) = true) :
    n < (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceActivePhysicalHorizon.run initial rows J rewards start (n + 1)
        hspan active).records).length := by
  let E := ReferenceActivePhysicalHorizon.run initial rows J rewards start (n + 1) hspan active
  let W := ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records
  have hlength : W.length ≤ n + 1 := by
    calc
      W.length ≤ E.records.length := (List.takeWhile_prefix _).length_le
      _ = n + 1 := ReferenceActivePhysicalHorizon.run_record_count _ _ _ _ _ _ _ _
  by_contra hnot
  have hle : W.length ≤ n := Nat.le_of_not_gt hnot
  obtain ⟨hidx, hcut, _⟩ :=
    (ReferenceFirstLiveCoordinatorSafety.run_first_live_coordinator_safety
      initial rows J rewards start (n + 1) hspan active hfirst).2.2 (by omega)
  let boundary := E.records[W.length]'hidx
  have hrecord : boundary = ReferenceAssignmentPayloadChronology.actualRunRecordAt
      initial rows J rewards start W.length (by omega) active :=
    ReferenceLocalReleaseGateChronology.run_record_at initial rows J rewards start active
      (n + 1) hspan ⟨W.length, by omega⟩
  have hcut' : ReferenceCollectionPhaseHistory.cutoffChosen boundary.input = true := hcut
  by_cases heq : W.length = n
  · have hstate : boundary.input.state =
        (ReferenceActivePhysicalHorizon.run initial rows J rewards start n (by omega) active).finalState := by
      rw [hrecord]
      change (ReferenceActivePhysicalHorizon.run initial rows J rewards
        start W.length (by omega) active).finalState = _
      simp only [heq]
    have htime : boundary.input.time = ⟨start + n, by omega⟩ := by
      rw [hrecord]
      apply Fin.ext
      exact congrArg (start + ·) heq
    have hgate : ReferenceRetainedReleasePhaseObservation.localReleaseGate rate b
        boundary.input.time (ReferenceActivePhysicalStepMeasurability.encodeState
          boundary.input.state) = true := by rw [hstate, htime]; exact hg
    have hfalse := gate_no_cutoff boundary.input b hgate
    rw [hfalse] at hcut'
    cases hcut'
  · obtain ⟨r, owned, base, hnext⟩ := hlive (W.length + 1) (by omega) (by omega)
    rw [ReferenceAssignmentPayloadChronology.run_successor_finalState_eq_actualRunRecordAt]
      at hnext
    rw [← hrecord] at hnext
    have hstep : (step boundary.input).next.coordinator = .live r owned base := by
      rw [← boundary.output_eq]
      exact hnext
    exact cutoff_next_not_live boundary.input hcut' r owned base hstep

private theorem incoming_of_launch
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (z : SourceInput p) (initial : State p rate) (start : ℕ)
    (hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch rate z rewards C_star C_h =
      some initial)
    (hstart : ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h = start)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (v : Fin p.T) (hv : start ≤ v.val) :
    ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h v z =
      some (ReferenceActivePhysicalStepMeasurability.encodeState
        (ReferenceActivePhysicalHorizon.run initial z.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards start
          (v.val - start) (by have _ht := v.isLt; omega) active).finalState) := by
  subst start
  rw [ReferenceSourcePrefixHistoryFiltration.incoming,
    ReferenceSourcePrefixHistoryFiltration.actualRecord_on_launch
      rate rewards C_star C_h v z initial hlaunch hv]
  rfl

private theorem incoming_prefix_le
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (control0 : ContinuousLearningRows.TimeControl p) (n : ℕ)
    (z : SourceInput p) (v : Fin p.T) (hv : v.val ≤ n) :
    ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h v z =
      ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h v
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n z) := by
  rw [ReferenceSourcePrefixHistoryFiltration.incoming_factor
    rate rewards C_star C_h control0 v z,
    ReferenceSourcePrefixHistoryFiltration.incoming_factor rate rewards C_star C_h control0 v
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n z),
    ReferenceSourcePrefixHistoryFiltration.sourcePrefix_sourcePrefix control0 v.val n hv]

private theorem first_live_branch_incoming
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (control0 : ContinuousLearningRows.TimeControl p) (i : Fin (p.m - 1))
    (t : Fin p.T) (q : Fin (M p)) (s : ℕ) (hs : s ≤ t.val)
    (z : SourceInput p)
    (hz : z ∈ ReferenceFirstLiveActualFlagSections.firstLiveSourceBranch
      rate rewards C_star C_h control0 i t q s hs) :
    incomingFirst (ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h
      ⟨s, hs.trans_lt t.isLt⟩ z) = true ∧
      ∀ v : Fin p.T, s < v.val → v.val ≤ t.val →
        incomingLive (ReferenceSourcePrefixHistoryFiltration.incoming
          rate rewards C_star C_h v z) = true := by
  obtain ⟨hj, hc, he, hx⟩ := hz
  let seed := ReferenceFirstLiveReleaseCylinderIntegral.originalSeed rate rewards C_star C_h z hc
  have hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate z rewards C_star C_h = some seed := (Option.some_get _).symm
  have hmode := ReferenceFirstLiveReleaseCylinderIntegral.originalSeed_active
    rate rewards C_star C_h s z hc he
  have hfirst : seed.coordinator = .first :=
    (ReferenceLocalReleaseGateChronology.canonical_seed_release_inputs
      rate z rewards C_star C_h hc).1
  obtain ⟨hn, _⟩ := ReferenceFirstLiveReleaseCylinderIntegral.source_current_record
    rate rewards C_star C_h q t s hs control0 i z hj hc he hx
  have hsafe := ReferenceFirstLiveCoordinatorSafety.run_first_live_coordinator_safety
    seed z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s (p.T - s)
    (by omega) hmode hfirst
  constructor
  · rw [incoming_of_launch rate rewards C_star C_h z seed s hlaunch he hmode
      ⟨s, hs.trans_lt t.isLt⟩ le_rfl]
    apply (incomingFirst_encode _).mpr
    simpa only [Nat.sub_self, ReferenceActivePhysicalHorizon.run_zero_final] using hfirst
  · intro v hsv hvt
    have hk : v.val - s ≤
        (ReferenceFirstLiveReleaseCylinderIntegral.originalWindow
          rate rewards C_star C_h s (by omega) z hc he).length := by omega
    obtain ⟨r, owned, base, hcoord⟩ := (hsafe.2.1 (v.val - s) hk).2 (by omega)
    rw [incoming_of_launch rate rewards C_star C_h z seed s hlaunch he hmode v (by omega)]
    exact (incomingLive_encode _).mpr ⟨r, owned, base, hcoord⟩

private theorem first_live_branch_of_fixed_observations
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (control0 : ContinuousLearningRows.TimeControl p) (i : Fin (p.m - 1))
    (t : Fin p.T) (q : Fin (M p)) (s : ℕ) (hs : s ≤ t.val) (b : ℕ)
    (z : SourceInput p)
    (hj : ActualInitializationPhysicalStep.selectedRowIndex p z = q)
    (hcontrol : (z.1.2 q).2 t = control0)
    (hfirstCode : incomingFirst (ReferenceSourcePrefixHistoryFiltration.incoming
      rate rewards C_star C_h ⟨s, hs.trans_lt t.isLt⟩ z) = true)
    (hliveCode : ∀ v : Fin p.T, s < v.val → v.val ≤ t.val →
      incomingLive (ReferenceSourcePrefixHistoryFiltration.incoming
        rate rewards C_star C_h v z) = true)
    (hentry : (ReferenceSourcePrefixHistoryFiltration.entry rate rewards C_star C_h b t z).map
      Prod.fst = some true)
    (hi : i ∈ ReferenceSourcePrefixHistoryFiltration.pending rate rewards C_star C_h b t z) :
    z ∈ ReferenceFirstLiveActualFlagSections.firstLiveSourceBranch
      rate rewards C_star C_h control0 i t q s hs := by
  obtain ⟨hc, he⟩ := incomingFirst_actual_launch rate rewards C_star C_h
    ⟨s, hs.trans_lt t.isLt⟩ z hfirstCode
  let x := ReferenceRetainedBoundaryMeasurability.retainedLaunchStartInputOfSource
    rate rewards C_star C_h q t s hs control0 z hj hc he
  let source := ReferenceGeneratedActivePrefixFactor.splitSource q t control0 x.val
  have hsource : source = z := by
    have hcurrent : (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t z).1 =
        control0 := by
      rw [ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_control]
      exact hcontrol
    change (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t).symm
      (control0, (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t z).2) = z
    rw [← hcurrent, (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t).symm_apply_apply]
  let seed := ReferenceGeneratedActivePrefixFactor.generatedActiveSeed
    rate rewards C_star C_h q t control0 x.val x.property.1 s hs x.property.2
  have hseedSpec := ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec
    rate rewards C_star C_h q t control0 x.val x.property.1 s hs x.property.2
  have hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch rate z rewards C_star C_h =
      some seed := hsource ▸ hseedSpec.1
  have hmode : ReferenceActivePhysicalHorizon.allActiveAtStart seed s := hseedSpec.2.1
  have hseedEq : seed = ReferenceLocalReleaseGateChronology.sourceSeed
      rate z rewards C_star C_h hc :=
    Option.some.inj (hlaunch.symm.trans
      (ReferenceLocalReleaseGateChronology.sourceSeed_launch rate z rewards C_star C_h hc))
  have hfirst : seed.coordinator = .first := by
    rw [hseedEq]
    exact (ReferenceLocalReleaseGateChronology.canonical_seed_release_inputs
      rate z rewards C_star C_h hc).1
  let n := t.val - s
  let E := ReferenceActivePhysicalHorizon.run seed z.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s (n + 1) (by dsimp [n]; omega) hmode
  let W := ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records
  let current := ReferenceAssignmentPayloadChronology.actualRunRecordAt seed z.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s n (by dsimp [n]; omega) hmode
  have hin : ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t z =
      some (ReferenceActivePhysicalStepMeasurability.encodeState current.input.state) :=
    incoming_of_launch rate rewards C_star C_h z seed s hlaunch he hmode t hs
  have hg : ReferenceRetainedReleasePhaseObservation.localReleaseGate rate b t
      (ReferenceActivePhysicalStepMeasurability.encodeState current.input.state) = true := by
    rw [ReferenceSourcePrefixHistoryFiltration.entry, hin] at hentry
    exact Option.some.inj hentry
  have hlive : ∀ k (_hpos : 0 < k) (hk : k ≤ n),
      ∃ r owned base, (ReferenceActivePhysicalHorizon.run seed z.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s k
        (by dsimp [n] at hk; omega) hmode).finalState.coordinator = .live r owned base := by
    intro k hkpos hk
    let v : Fin p.T := ⟨s + k, by dsimp [n] at hk; omega⟩
    have hcode := hliveCode v (by dsimp [v]; omega) (by dsimp [v, n] at *; omega)
    rw [incoming_of_launch rate rewards C_star C_h z seed s hlaunch he hmode v (by dsimp [v]; omega)] at hcode
    have hcoord := (incomingLive_encode _).mp hcode
    simpa only [v, Nat.add_sub_cancel_left] using hcoord
  have hn : n < W.length := by
    apply window_index_of_live_prefix seed z.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s n
      (by dsimp [n]; omega) hmode hfirst hlive b
    have htime : (⟨s + n, by dsimp [n]; omega⟩ : Fin p.T) = t := Fin.ext (by dsimp [n]; omega)
    rw [htime]
    exact hg
  have hpref := List.takeWhile_prefix (l := E.records)
    (fun record => !ReferenceCollectionPhaseHistory.cutoffChosen record.input)
  have hrecord : W[n] = current :=
    (hpref.getElem hn).trans (ReferenceLocalReleaseGateChronology.run_record_at
      seed z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s hmode
      (n + 1) (by dsimp [n]; omega) ⟨n, by omega⟩)
  obtain ⟨r, owned, base, hcoord, _, hempty, _, _⟩ :=
    ReferenceLocalReleaseGateChronology.gate_live b t current.input.state hg
  have hentryEq : ReferenceSourcePrefixHistoryFiltration.entry rate rewards C_star C_h b t z =
      some (true, some (ReferencePhysicalReleaseQuota.pendingAtStart r.payload t current.input.state)) := by
    rw [ReferenceSourcePrefixHistoryFiltration.entry, hin, Option.map_some]
    simp only [ReferenceRetainedReleasePhaseObservation.localReleaseEntry, hg,
      ite_true,
      ReferenceRetainedReleasePhaseObservation.localStoredPayload_eq_decoded,
      ReferenceActivePhysicalStepMeasurability.decodeState_encodeState, hcoord,
      ReferenceAssignmentPayloadPersistence.storedPayload_live,
      ReferenceRetainedReleasePhaseObservation.localReleasePending]
  have hip : i ∈ ReferencePhysicalReleaseQuota.pendingAtStart r.payload t current.input.state := by
    simpa only [ReferenceSourcePrefixHistoryFiltration.pending, hentryEq, Option.bind_some,
      Option.getD_some] using hi
  have hretained : ReferenceFirstLiveReleaseControlTransport.retainedWindow
      rewards C_star C_h q t s hs control0 x control0 = W := by
    change ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceActivePhysicalHorizon.run seed source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s (n + 1) _ _).records = W
    rw [hsource]
  have hbetaState : (ReferenceRetainedBoundaryMeasurability.retainedIncomingBoundary
      rate rewards C_star C_h q t s hs control0 x).state = current.input.state := by
    change (ReferenceActivePhysicalHorizon.run seed source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s n _ _).finalState = _
    rw [hsource]
    rfl
  have hprov := ReferenceFirstLiveMissingSetProvenance.run_first_live_missing_set_provenance
    seed z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s (n + 1)
    (by dsimp [n]; omega) hmode hfirst
  rcases hprov with hzero | ⟨_hW, _firstSelected, _installed, _arm, _hf, _hd, _hi,
      _hu, _hsu, _hsel, _hpay, _hpen, _hstarted, hall⟩
  · change W.length = 0 at hzero
    omega
  · obtain ⟨record, hrec, selected, hselected, _hpayload, hframe, _next⟩ := hall ⟨n, hn⟩
    subst record
    have hcW : W[n].input.state.coordinator = .live r owned base := by
      rw [hrecord]
      exact hcoord
    rw [hcW] at hframe
    refine ⟨hj, hc, he, ?_⟩
    change x ∈ ReferenceFirstLiveReleaseSourceCylinder.selectedEmptyPendingRemainder
      rewards C_star C_h q t s hs control0 i
    change ∃ hn : n < (ReferenceFirstLiveReleaseControlTransport.retainedWindow
        rewards C_star C_h q t s hs control0 x control0).length,
      ∃ selected : Selection ((ReferenceFirstLiveReleaseControlTransport.retainedWindow
          rewards C_star C_h q t s hs control0 x control0)[n]'hn).input,
        ((ReferenceFirstLiveReleaseControlTransport.retainedWindow
          rewards C_star C_h q t s hs control0 x control0)[n]'hn).output.preparation.coordinator.selection =
            some selected ∧ selected.view.pendingAtChoice = ∅ ∧
          i ∈ ReferencePhysicalReleaseQuota.pendingAtStart selected.view.payload
            (ReferenceRetainedBoundaryMeasurability.retainedIncomingBoundary
              rate rewards C_star C_h q t s hs control0 x).time
            (ReferenceRetainedBoundaryMeasurability.retainedIncomingBoundary
              rate rewards C_star C_h q t s hs control0 x).state
    rw [hretained]
    refine ⟨hn, selected, hselected, hframe.2.1.trans hempty, ?_⟩
    rw [hframe.1,
      ReferenceRetainedBoundaryMeasurability.retainedIncomingBoundary_time, hbetaState]
    exact hip

/-- The literal first-live guard is reconstructed from included incoming
constructors and the actual local release entry. No selector, launch event,
history law, successful trace, or measurability premise is supplied. -/
theorem inspected_guard_iff
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (control0 : ContinuousLearningRows.TimeControl p) (i : Fin (p.m - 1))
    (t : Fin p.T) (q : Fin (M p)) (s : ℕ) (hs : s ≤ t.val) (b : ℕ)
    (z : SourceInput p) :
    z ∈ ReferenceFirstLiveGuardedConditionalService.firstLiveGuardedEvent
      rate rewards C_star C_h control0 i t q s hs b ↔
      ActualInitializationPhysicalStep.selectedRowIndex p z = q ∧
      incomingFirst (ReferenceSourcePrefixHistoryFiltration.incoming
        rate rewards C_star C_h ⟨s, hs.trans_lt t.isLt⟩ z) = true ∧
      (∀ v : Fin p.T, s < v.val → v.val ≤ t.val →
        incomingLive (ReferenceSourcePrefixHistoryFiltration.incoming
          rate rewards C_star C_h v z) = true) ∧
      (ReferenceSourcePrefixHistoryFiltration.entry rate rewards C_star C_h b t z).map
        Prod.fst = some true ∧
      i ∈ ReferenceSourcePrefixHistoryFiltration.pending rate rewards C_star C_h b t z := by
  constructor
  · intro hz
    have hcodes := first_live_branch_incoming
      rate rewards C_star C_h control0 i t q s hs z hz.1
    exact ⟨hz.1.choose, hcodes.1, hcodes.2, hz.2.1, hz.2.2⟩
  · rintro ⟨hj, hfirst, hlive, he, hi⟩
    refine ⟨?_, he, hi⟩
    apply (ReferenceFirstLiveActualFlagSections.firstLiveSourceBranch_factor
      rate rewards C_star C_h control0 i t q s hs z).mpr
    let c := ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z
    apply first_live_branch_of_fixed_observations
      rate rewards C_star C_h control0 i t q s hs b c hj
    · dsimp only [c]
      rw [← hj, ReferenceSourcePrefixHistoryFiltration.sourcePrefix_control,
        ite_eq_right (lt_irrefl _)]
    · rw [← incoming_prefix_le rate rewards C_star C_h control0 t.val z
        ⟨s, hs.trans_lt t.isLt⟩ hs]
      exact hfirst
    · intro v hsv hvt
      rw [← incoming_prefix_le rate rewards C_star C_h control0 t.val z v hvt]
      exact hlive v hsv hvt
    · rw [← ReferenceSourcePrefixHistoryFiltration.entry_factor
        rate rewards C_star C_h control0 b t z]
      exact he
    · rw [← ReferenceSourcePrefixHistoryFiltration.pending_factor
        rate rewards C_star C_h control0 b t z]
      exact hi

/-- The original row index is observable because the enlarged field retains
all original private arrays, including the distinct private J coordinate. -/
private theorem selected_measurable_in_inspectedHistorySpace
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (n : ℕ) (hn : n ≤ p.T) :
    Measurable[ReferenceSourceOwnHistoryContainment.inspectedHistorySpace
      rate rewards C_star C_h n hn] (ActualInitializationPhysicalStep.selectedRowIndex p) := by
  have hprivate : Measurable[ReferenceSourceOwnHistoryContainment.inspectedHistorySpace
      rate rewards C_star C_h n hn]
      (Prod.snd : SourceInput p → BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p) := by
    apply (comap_measurable Prod.snd).mono _ le_rfl
    dsimp only [ReferenceSourceOwnHistoryContainment.inspectedHistorySpace]
    exact le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left
      (le_sup_of_le_right le_rfl)))
  exact (PrivateSourceStreams.measurable_coordinatorIndex p).comp
    (measurable_snd.comp (measurable_fst.comp hprivate))

/-- Measurability in the inspected analysis field follows from the proved
literal reconstruction and its defining incoming observations. It is not
inferred from containment in a larger source-prefix field. -/
theorem measurableSet_inspected_guard
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (control0 : ContinuousLearningRows.TimeControl p) (i : Fin (p.m - 1))
    (t : Fin p.T) (q : Fin (M p)) (s : ℕ) (hs : s ≤ t.val) (b : ℕ) :
    MeasurableSet[ReferenceSourceOwnHistoryContainment.inspectedHistorySpace
      rate rewards C_star C_h t.val (le_of_lt t.isLt)]
      (ReferenceFirstLiveGuardedConditionalService.firstLiveGuardedEvent
        rate rewards C_star C_h control0 i t q s hs b) := by
  let : MeasurableSpace (SourceInput p) :=
    ReferenceSourceOwnHistoryContainment.inspectedHistorySpace
      rate rewards C_star C_h t.val (le_of_lt t.isLt)
  have hj := (selected_measurable_in_inspectedHistorySpace
    rate rewards C_star C_h t.val (le_of_lt t.isLt)) (MeasurableSet.singleton q)
  have hfirst := (measurable_incomingFirst.comp
    (ReferenceSourceOwnHistoryContainment.incoming_measurable_in_inspectedHistorySpace
      rate rewards C_star C_h t.val (le_of_lt t.isLt) ⟨s, hs.trans_lt t.isLt⟩ hs))
        (MeasurableSet.singleton true)
  have hlive : MeasurableSet {z : SourceInput p | ∀ v : Fin p.T,
      s < v.val → v.val ≤ t.val → incomingLive
        (ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h v z) = true} := by
    simp only [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro v
    apply MeasurableSet.iInter
    intro _hsv
    apply MeasurableSet.iInter
    intro hvt
    exact (measurable_incomingLive.comp
      (ReferenceSourceOwnHistoryContainment.incoming_measurable_in_inspectedHistorySpace
        rate rewards C_star C_h t.val (le_of_lt t.isLt) v hvt))
          (MeasurableSet.singleton true)
  have hsupport := releaseSupport_measurable_in_inspectedHistorySpace
    rate rewards C_star C_h t.val (le_of_lt t.isLt) t le_rfl i b
  have heq : ReferenceFirstLiveGuardedConditionalService.firstLiveGuardedEvent
      rate rewards C_star C_h control0 i t q s hs b =
      {z | ActualInitializationPhysicalStep.selectedRowIndex p z = q} ∩
      ({z | incomingFirst (ReferenceSourcePrefixHistoryFiltration.incoming
        rate rewards C_star C_h ⟨s, hs.trans_lt t.isLt⟩ z) = true} ∩
      ({z | ∀ v : Fin p.T, s < v.val → v.val ≤ t.val →
        incomingLive (ReferenceSourcePrefixHistoryFiltration.incoming
          rate rewards C_star C_h v z) = true} ∩
        ReferenceSourcePhysicalFlagConditionalLaw.actualReleaseSupport
          rate rewards C_star C_h b t i)) := by
    ext z
    exact inspected_guard_iff rate rewards C_star C_h control0 i t q s hs b z
  rw [heq]
  exact hj.inter (hfirst.inter (hlive.inter hsupport))

/-- On the actual guarded branch, the baseline selector's WHOLE fields
are those in the very same incoming LIVE code. Registers are reindexed only
by `liveRegistersAt`; all complement weights are retained. No frame, validity,
selector, or weight agreement is a caller premise. -/
private theorem baseline_fields_eq_incoming_registers
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (control0 : ContinuousLearningRows.TimeControl p) (i : Fin (p.m - 1))
    (t : Fin p.T) (q : Fin (M p)) (s : ℕ) (hs : s ≤ t.val) (b : ℕ)
    (z : SourceInput p)
    (hz : z ∈ ReferenceFirstLiveGuardedConditionalService.firstLiveGuardedEvent
      rate rewards C_star C_h control0 i t q s hs b) :
    let x := ReferenceFirstLiveActualFlagSections.firstLiveRemainder
      rate rewards C_star C_h control0 i t q s hs z hz.1
    let hx := ReferenceFirstLiveActualFlagSections.firstLiveRemainder_mem
      rate rewards C_star C_h control0 i t q s hs z hz.1
    let selected0 := ReferenceFirstLiveReleaseCylinderIntegral.baselineSelection
      rate rewards C_star C_h q t s hs control0 i x hx
    ∃ (code : ReferenceActivePhysicalStepMeasurability.StateCode p rate)
      (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
      (owned : CoordinatorLiveServiceFinish.OwnedRegisters r) (base : Fin (p.m - 1) → ℕ),
      ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t z = some code ∧
      code.1 = .inr (.inl (r.payload,
        ReferenceActivePhysicalStepMeasurability.encodeLive r owned base)) ∧
      (ReferenceActivePhysicalStepMeasurability.decodeState code).coordinator = .live r owned base ∧
      r.time.val + 1 = t.val ∧
      selected0.view.payload = (ReferenceActivePhysicalStep.liveRegistersAt r t).payload ∧
      HEq selected0.view.complementWeights
        (ReferenceActivePhysicalStep.liveRegistersAt r t).complementWeights ∧
      (ReferenceActivePhysicalStep.liveRegistersAt r t).time = t ∧
      (ReferenceActivePhysicalStep.liveRegistersAt r t).pendingAtChoice = ∅ ∧
      (ReferenceActivePhysicalStep.liveRegistersAt r t).priorClock.u = none ∧
      selected0.view.cutoff = none ∧
      CoordinatorLocalArmChoice.ChoiceInputsValid selected0.view.payload
        selected0.view.cutoff t selected0.view.complementWeights := by
  intro x hx selected0
  let beta := ReferenceRetainedBoundaryMeasurability.retainedIncomingBoundary
    rate rewards C_star C_h q t s hs control0 x
  have hn := ReferenceFirstLiveReleaseCylinderIntegral.baseline_index_lt
    rate rewards C_star C_h q t s hs control0 i x hx
  have hspec := ReferenceFirstLiveReleaseCylinderIntegral.baselineSelection_spec
    rate rewards C_star C_h q t s hs control0 i x hx
  obtain ⟨r, owned, base, hbeta, hstate, htime, hprior, hpending,
      _hnoCut, hpayload, hcutoff, hweights, _htail⟩ :=
    ReferenceFirstLiveReleaseControlTransport.retained_first_live_control_transport
      rewards C_star C_h q t s hs control0 x hn selected0 hspec.1 hspec.2.1
  have hbstate : beta.state.coordinator = .live r owned base := by
    rw [show beta = _ from hbeta]
    exact hstate
  have hbtime : beta.time = t :=
    ReferenceRetainedBoundaryMeasurability.retainedIncomingBoundary_time
      rate rewards C_star C_h q t s hs control0 x
  have hwtime : _ = t := (congrArg ReferenceActivePhysicalStep.RoundInput.time hbeta).symm.trans hbtime
  have hincoming : ReferenceSourcePrefixHistoryFiltration.incoming
      rate rewards C_star C_h t z =
        some (ReferenceActivePhysicalStepMeasurability.encodeState beta.state) := by
    rw [ReferenceSourcePrefixHistoryFiltration.incoming,
      ReferenceFirstLiveActualFlagSections.actualRecord_eq_current
        rate rewards C_star C_h control0 i t q s hs z hz.1]
    rfl
  have hstored := ReferenceFirstLiveActualFlagSections.actual_storedPayload_eq_baseline
    rate rewards C_star C_h control0 i t q s hs z hz.1 control0
  change ReferenceAssignmentPayloadPersistence.storedPayload beta.state.coordinator =
    some selected0.view.payload at hstored
  rw [hbstate] at hstored
  have hpwhole : selected0.view.payload = r.payload := (Option.some.inj hstored).symm
  have hvalid := ReferenceFirstLiveReleaseCylinderIntegral.baselineSelection_valid
    rate rewards C_star C_h q t s hs control0 i x hx
  dsimp only at hvalid
  have hwtime' : (ReferenceFirstLiveReleaseControlTransport.retainedWindow
      rewards C_star C_h q t s hs control0 x control0)[t.val - s].input.time = t := hwtime
  rw [hwtime'] at hvalid
  refine ⟨ReferenceActivePhysicalStepMeasurability.encodeState beta.state,
    r, owned, base, hincoming, ?_, ?_, ?_, hpwhole, hweights,
    rfl, hpending, hprior, hcutoff, hvalid⟩
  · simp only [ReferenceActivePhysicalStepMeasurability.encodeState, hbstate,
      ReferenceActivePhysicalStepMeasurability.encodeCoordinator]
  · rw [ReferenceActivePhysicalStepMeasurability.decodeState_encodeState]
    exact hbstate
  · simpa only [hwtime] using htime

/-- The actual incoming LIVE code supplies the whole payload and the full
complement weights of the uniquely computed baseline selection. The registers
on the right are decoded from that SAME code, then reindexed to the actual
current time. The empty confirmation set, absent cutoff, unchanged StartRound
frame, and choice validity are conclusions on the guarded branch. -/
theorem baseline_fields_eq_incoming
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (control0 : ContinuousLearningRows.TimeControl p) (i : Fin (p.m - 1))
    (t : Fin p.T) (q : Fin (M p)) (s : ℕ) (hs : s ≤ t.val) (b : ℕ)
    (z : SourceInput p)
    (hz : z ∈ ReferenceFirstLiveGuardedConditionalService.firstLiveGuardedEvent
      rate rewards C_star C_h control0 i t q s hs b) :
    let x := ReferenceFirstLiveActualFlagSections.firstLiveRemainder
      rate rewards C_star C_h control0 i t q s hs z hz.1
    let hx := ReferenceFirstLiveActualFlagSections.firstLiveRemainder_mem
      rate rewards C_star C_h control0 i t q s hs z hz.1
    let selected0 := ReferenceFirstLiveReleaseCylinderIntegral.baselineSelection
      rate rewards C_star C_h q t s hs control0 i x hx
    ∃ (code : ReferenceActivePhysicalStepMeasurability.StateCode p rate)
      (payload : Payload rate) (live : ReferenceActivePhysicalStepMeasurability.LiveDiscrete p),
      ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t z = some code ∧
      code.1 = .inr (.inl (payload, live)) ∧
      (ReferenceActivePhysicalStepMeasurability.decodeState code).coordinator =
        .live (ReferenceActivePhysicalStepMeasurability.decodeLiveRegisters payload live)
          (ReferenceActivePhysicalStepMeasurability.decodeLiveOwned payload live) live.baseScores ∧
      let decoded := ReferenceActivePhysicalStepMeasurability.decodeLiveRegisters payload live
      let registers := liveRegistersAt decoded t
      decoded.time.val + 1 = t.val ∧
      selected0.view.payload = payload ∧
      HEq selected0.view.complementWeights registers.complementWeights ∧
      registers.time = t ∧ registers.pendingAtChoice = ∅ ∧
      registers.priorClock.u = none ∧ selected0.view.cutoff = none ∧
      CoordinatorLocalArmChoice.ChoiceInputsValid selected0.view.payload
        selected0.view.cutoff t selected0.view.complementWeights ∧
      ∃ started, CoordinatorPhaseClock.startRound p rate.eta.val t
          registers.priorClock registers.clockPending = .ok started ∧
        CoordinatorLiveChoiceRecorderStep.unchangedLiveClockFrame registers started := by
  intro x hx selected0
  obtain ⟨code, r, owned, base, hin, hcode, _hdecodedState, htime, hpayload,
      hweights, htimeAt, hempty, hprior, hcutoff, hvalid⟩ :=
    baseline_fields_eq_incoming_registers
      rate rewards C_star C_h control0 i t q s hs b z hz
  have hdecode : ReferenceActivePhysicalStepMeasurability.decodeLiveRegisters r.payload
      (ReferenceActivePhysicalStepMeasurability.encodeLive r owned base) = r := by
    have h := congrArg (fun c : CoordinatorConfiguration p rate =>
      match c with | .live rr _ _ => some rr | _ => none)
      (ReferenceActivePhysicalStepMeasurability.decodeCoordinator_encodeCoordinator
        (.live r owned base))
    exact Option.some.inj h
  have hg : ReferenceRetainedReleasePhaseObservation.localReleaseGate rate b t code = true := by
    have he := hz.2.1
    rw [ReferenceSourcePrefixHistoryFiltration.entry, hin] at he
    exact Option.some.inj he
  have hframe : ∃ started, CoordinatorPhaseClock.startRound p rate.eta.val t
      (liveRegistersAt r t).priorClock (liveRegistersAt r t).clockPending = .ok started ∧
      CoordinatorLiveChoiceRecorderStep.unchangedLiveClockFrame (liveRegistersAt r t) started := by
    have hstartCode : ReferenceRetainedReleasePhaseObservation.localReleaseStartResult rate t
        (ReferenceActivePhysicalStepMeasurability.encodeLive r owned base) =
        CoordinatorPhaseClock.startRound p rate.eta.val t r.priorClock r.clockPending := by
      rw [ReferenceRetainedReleasePhaseObservation.localReleaseStartResult_eq_decoded
        rate t r.payload _, hdecode]
    simp only [ReferenceRetainedReleasePhaseObservation.localReleaseGate, hcode,
      hstartCode, Bool.and_eq_true, decide_eq_true_eq] at hg
    cases hsStart : CoordinatorPhaseClock.startRound p rate.eta.val t r.priorClock r.clockPending with
    | error failure => simp only [hsStart, Bool.false_eq_true, and_false] at hg
    | ok started =>
        simp only [hsStart, decide_eq_true_eq] at hg
        have hf := hg.2
        rw [hdecode] at hf
        exact ⟨started, hsStart, hf⟩
  refine ⟨code, r.payload, ReferenceActivePhysicalStepMeasurability.encodeLive r owned base,
    hin, hcode, ?_, ?_⟩
  · change ReferenceActivePhysicalStepMeasurability.decodeCoordinator code.1 = _
    rw [hcode]
    rfl
  · dsimp only
    rw [hdecode]
    exact ⟨htime, hpayload, hweights, htimeAt, hempty, hprior, hcutoff, hvalid, hframe⟩

/-- An absent actual current record never belongs to the guarded support.
This is an observation of absence, not an invented ordinary state. -/
theorem not_mem_guard_of_no_record
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (control0 : ContinuousLearningRows.TimeControl p) (i : Fin (p.m - 1))
    (t : Fin p.T) (q : Fin (M p)) (s : ℕ) (hs : s ≤ t.val) (b : ℕ)
    (z : SourceInput p)
    (hnone : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = none) :
    z ∉ ReferenceFirstLiveGuardedConditionalService.firstLiveGuardedEvent
      rate rewards C_star C_h control0 i t q s hs b := by
  intro hz
  have he := hz.2.1
  rw [ReferenceSourcePrefixHistoryFiltration.entry,
    ReferenceSourcePrefixHistoryFiltration.incoming, hnone] at he
  cases he

/-- No crossing, including all original initialization paths, gives no guard. -/
theorem not_mem_guard_of_no_crossing
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (control0 : ContinuousLearningRows.TimeControl p) (i : Fin (p.m - 1))
    (t : Fin p.T) (q : Fin (M p)) (s : ℕ) (hs : s ≤ t.val) (b : ℕ)
    (z : SourceInput p)
    (hnone : (ReferenceCompletePhysicalHistory.generatedBoundary rate z rewards C_star C_h).crossing = none) :
    z ∉ ReferenceFirstLiveGuardedConditionalService.firstLiveGuardedEvent
      rate rewards C_star C_h control0 i t q s hs b :=
  not_mem_guard_of_no_record rate rewards C_star C_h control0 i t q s hs b z
    (ReferenceSourcePrefixHistoryFiltration.actualRecord_eq_none_of_no_crossing
      rate rewards C_star C_h t z hnone)

/-- A future launch has no current guarded observation. Terminal launch is
included since every `Fin T` coordinate is strictly before `T`. -/
theorem not_mem_guard_of_future_start
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (control0 : ContinuousLearningRows.TimeControl p) (i : Fin (p.m - 1))
    (t : Fin p.T) (q : Fin (M p)) (s : ℕ) (hs : s ≤ t.val) (b : ℕ)
    (z : SourceInput p)
    (hfuture : t.val < ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h) :
    z ∉ ReferenceFirstLiveGuardedConditionalService.firstLiveGuardedEvent
      rate rewards C_star C_h control0 i t q s hs b :=
  not_mem_guard_of_no_record rate rewards C_star C_h control0 i t q s hs b z
    (ReferenceSourcePrefixHistoryFiltration.actualRecord_eq_none_of_future_start
      rate rewards C_star C_h t z hfuture)

/-- A launch at the terminal source boundary has no physical query record. -/
theorem not_mem_guard_of_terminal_start
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (control0 : ContinuousLearningRows.TimeControl p) (i : Fin (p.m - 1))
    (t : Fin p.T) (q : Fin (M p)) (s : ℕ) (hs : s ≤ t.val) (b : ℕ)
    (z : SourceInput p)
    (hterminal : ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h = p.T) :
    z ∉ ReferenceFirstLiveGuardedConditionalService.firstLiveGuardedEvent
      rate rewards C_star C_h control0 i t q s hs b :=
  not_mem_guard_of_no_record rate rewards C_star C_h control0 i t q s hs b z
    (ReferenceSourcePrefixHistoryFiltration.actualRecord_eq_none_of_terminal_start
      rate rewards C_star C_h t z hterminal)

/-- The zero-length incoming prefix (`s=t`, hence `t-s=0`) cannot be a
release round: FIRST and the true live entry are disjoint constructor tests. -/
theorem not_mem_guard_at_launch
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (control0 : ContinuousLearningRows.TimeControl p) (i : Fin (p.m - 1))
    (t : Fin p.T) (q : Fin (M p)) (b : ℕ) (z : SourceInput p) :
    z ∉ ReferenceFirstLiveGuardedConditionalService.firstLiveGuardedEvent
      rate rewards C_star C_h control0 i t q t.val le_rfl b := by
  intro hz
  have hf := ((inspected_guard_iff rate rewards C_star C_h control0 i t q
    t.val le_rfl b z).mp hz).2.1
  have he := hz.2.1
  change incomingFirst (ReferenceSourcePrefixHistoryFiltration.incoming
    rate rewards C_star C_h t z) = true at hf
  cases hin : ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t z with
  | none => simp only [hin, incomingFirst, Bool.false_eq_true] at hf
  | some code =>
      rcases code with ⟨coord, rest⟩
      cases coord with
      | inl u =>
          simp only [ReferenceSourcePrefixHistoryFiltration.entry, hin, Option.map_some,
            ReferenceRetainedReleasePhaseObservation.localReleaseEntry,
            ReferenceRetainedReleasePhaseObservation.localReleaseGate] at he
          cases he
      | inr tail => simp only [hin, incomingFirst, Bool.false_eq_true] at hf

end Bandits.Support.ReferenceFirstLiveInspectedGuardReadout

end
