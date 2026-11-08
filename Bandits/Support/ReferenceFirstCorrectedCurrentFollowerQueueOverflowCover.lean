/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCorrectedCurrentFollowerLiveQueue
public import Bandits.Support.ReferenceFirstCorrectedCurrentFollowerCollectionQueue
public import Bandits.Support.ReferenceFirstCollectionCorrectedAssignedOverflowCover

import Mathlib.Tactic

/-!
# Current follower-register overflow on the first corrected assignment

This event observes only actual current follower registers and an actually
reached occupied service residual on the original physical source execution.
The separate attributed-calendar event remains the target of its cover.

Sources: `appendix_a_local_protocol.tex:28-64`,
`06_interruptions.tex:40-100,192-233,246-299`, and
`04_slow_fast_learner.tex:157-174` under `sources/zip4/manuscript/`.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions
open scoped Classical

namespace Bandits.Support.ReferenceFirstCorrectedCurrentFollowerQueueOverflowCover

variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)

local notation "X" => BootstrapPrivateRoundStreams.SourceInput p
local notation "Record" => ReferenceActivePhysicalHorizon.RoundRecord
  (p := p) (rate := rate)
local notation "Register" => Option (Option (OrdinaryMessageCodec.DownRecord
  (ReferencePrelaunchFollower.codecParams p rate.eta)) × ℕ)

/-- A typed local-register observation. Missing configurations and `dagger`
have no queue; an ordinary configuration reads its actual registers. -/
def followerRegisterObserver? (configuration : Option
    (DeclaredFollowerLocalRound.LocalConfiguration p rate)) : Register :=
  match configuration with
  | none => none
  | some .dagger => none
  | some (.ordinary state _) => some (state.lastDown, state.backlog)

/-- Read the actual incoming follower configuration of an optional physical
record. -/
def followerInputRegister? (record : Option Record)
    (i : Fin (p.m - 1)) : Register :=
  record.bind fun r =>
    followerRegisterObserver? (rate := rate) (some (r.input.state.followers i))

/-- Read the configuration after the actual beginning-of-round
`startRound` choice. -/
def followerChoiceRegister? (record : Option Record)
    (i : Fin (p.m - 1)) : Register :=
  record.bind fun r =>
    followerRegisterObserver? (rate := rate) (some
      (ReferenceFollowerFixedReply.actualChoice r i).configuration)

/-- Read the actual ordinary follower configuration returned by the physical
round. -/
def followerOutputRegister? (record : Option Record)
    (i : Fin (p.m - 1)) : Register :=
  record.bind fun r =>
    followerRegisterObserver? (rate := rate) (some (r.output.followers i).configuration)

/-- The computed occupied service residual at the actual CHOICE. The value is
present only for a current accepted DOWN register, an occupied CHOICE, and an
actual successful follower output. Its raw arrival is the literal local
recorder calculation from that CHOICE and its actual observation. -/
def actualOccupiedServiceResidual? (record : Option Record)
    (i : Fin (p.m - 1)) : Register := by
  classical
  exact record.bind fun r =>
    match (ReferenceFollowerFixedReply.actualChoice r i).configuration with
    | .dagger => none
    | .ordinary state _ =>
        if hstatus : state.status = .unoccupied then none
        else match hlast : state.lastDown with
          | none => none
          | some M =>
              if (r.output.followers i).failure = none then
                some (some M, CappedService.residual (4 * rate.n) state.backlog
                  (ActiveFollowerQueueOperation.rawArrival rate.eta i r.input.row
                    r.input.time M
                    ((ReferenceActivePhysicalStep.prepare r.input).feedback.observations
                      (PublicDiscreteDraws.followerPlayer p.two_le_m i))))
              else none

/-! The site types retain the source index of every observed configuration.
The optional remaining-suffix output constructor carries the actual
`laterChosen = false` fact as part of its availability condition. -/

inductive LiveFollowerRegisterSite (V : List Record) where
  | input (j : Fin V.length)
  | choice (j : Fin V.length)
  | output (j : Fin V.length)
  | serviceResidual (j : Fin V.length)

def observeLiveFollowerRegister (V : List Record) (i : Fin (p.m - 1)) :
    LiveFollowerRegisterSite (rate := rate) V → Register
  | .input j => followerInputRegister? (rate := rate) (some (V.get j)) i
  | .choice j => followerChoiceRegister? (rate := rate) (some (V.get j)) i
  | .output j => followerOutputRegister? (rate := rate) (some (V.get j)) i
  | .serviceResidual j => actualOccupiedServiceResidual? (rate := rate)
      (some (V.get j)) i

inductive CollectionFollowerRegisterSite
    (seg : ReferenceCollectionSegmentExtraction.Segment rate) where
  | cutoffInput
  | cutoffChoice
  | recordInput (j : Fin seg.records.length)
  | recordChoice (j : Fin seg.records.length)
  | recordOutput (j : Fin seg.records.length)
  | remainingInput (r : Record) (h : seg.remaining.head? = some r)
  | remainingChoice (r : Record) (h : seg.remaining.head? = some r)
  | remainingOutput (r : Record) (h : seg.remaining.head? = some r)
      (hnotLater : ReferenceCollectionPhaseHistory.laterChosen r.input = false)

def observeCollectionFollowerRegister
    (seg : ReferenceCollectionSegmentExtraction.Segment rate)
    (i : Fin (p.m - 1)) : CollectionFollowerRegisterSite (rate := rate) seg → Register
  | .cutoffInput => followerInputRegister? (rate := rate) (some seg.entry) i
  | .cutoffChoice => followerChoiceRegister? (rate := rate) (some seg.entry) i
  | .recordInput j => followerInputRegister? (rate := rate) (some (seg.records.get j)) i
  | .recordChoice j => followerChoiceRegister? (rate := rate) (some (seg.records.get j)) i
  | .recordOutput j => followerOutputRegister? (rate := rate) (some (seg.records.get j)) i
  | .remainingInput r _ => followerInputRegister? (rate := rate) (some r) i
  | .remainingChoice r _ => followerChoiceRegister? (rate := rate) (some r) i
  | .remainingOutput r _ _ => followerOutputRegister? (rate := rate) (some r) i

/-- The literal current follower register and computed-service overflow event
on the first corrected assignment. `V` is the complete actual birth-plus-LIVE
slice. The first collection is queried only through its actual extracted
segment, and the remaining suffix contributes only its optional first record.
The numerical threshold is tested on the observed current register value,
not defined as a union of independently chosen threshold events. -/
def currentFollowerRegisterOverflowEvent
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T) : Set X := by
  classical
  exact {z | z ∈ ReferenceFirstCollectionCorrectedSliceNumericalPrefix.correctedCell
      rate rewards C_star C_h u t ∧
    ∃ (birth : Record) (P : ReferenceActivePhysicalStep.Payload rate),
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[ReferenceFirstCollectionCorrectedSliceNumericalPrefix.birthIndex
          rate rewards C_star C_h z]? = some birth ∧
      ReferenceAssignmentPayloadPersistence.InstallationBirth birth P ∧ P.sigma = t ∧
      let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
      let b := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.birthIndex rate rewards C_star C_h z
      let W := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.liveTail rate rewards C_star C_h z
      let V := (R.drop b).take (1 + W.length)
      let e := b + (1 + W.length)
      ((∃ (i : Fin (p.m - 1)) (site : LiveFollowerRegisterSite (rate := rate) V)
          (q : ℕ),
          observeLiveFollowerRegister (rate := rate) V i site =
            some (some (P.downRecord i), q) ∧
          (q : ℝ) / (rate.n : ℝ) > 1 / (32 * rate.eta.val)) ∨
        (∃ (seg : ReferenceCollectionSegmentExtraction.Segment rate),
          ReferenceCollectionSegmentExtraction.segmentAt R e = some seg ∧
          ∃ (i : Fin (p.m - 1))
            (site : CollectionFollowerRegisterSite (rate := rate) seg) (q : ℕ),
            observeCollectionFollowerRegister (rate := rate) seg i site =
              some (some (P.downRecord i), q) ∧
            (q : ℝ) / (rate.n : ℝ) > 1 / (32 * rate.eta.val)))}

/-- A reached occupied residual is the backlog in the actual OUTPUT. The
observer computes the queue residual from CHOICE's accepted DOWN and actual
feedback; the no-failure guard and actual record equation identify it with
the returned ordinary configuration. -/
theorem actualOccupiedServiceResidual_is_output
    (r : Record) (i : Fin (p.m - 1))
    (M : OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta)) (q : ℕ)
    (hread : actualOccupiedServiceResidual? (rate := rate) (some r) i =
      some (some M, q)) :
    ∃ next nextMemory,
      (r.output.followers i).configuration = .ordinary next nextMemory ∧
      (r.output.followers i).failure = none ∧ next.backlog = q := by
  classical
  unfold actualOccupiedServiceResidual? at hread
  simp only [Option.bind_some] at hread
  cases hchoice : (ReferenceFollowerFixedReply.actualChoice r i).configuration with
  | dagger => simp [hchoice] at hread
  | ordinary state memory =>
      simp only [hchoice] at hread
      by_cases hu : state.status = .unoccupied
      · simp [hu] at hread
      · simp [hu] at hread
        cases hLastEq : state.lastDown with
        | none =>
            rw [hLastEq] at hread
            cases hread
        | some old =>
            rw [hLastEq] at hread
            by_cases hf : (r.output.followers i).failure = none
            · simp [hf] at hread
              rcases hread with ⟨_hM, hq'⟩
              have hq : q = CappedService.residual (4 * rate.n) state.backlog
                  (ActiveFollowerQueueOperation.rawArrival rate.eta i r.input.row
                    r.input.time old
                    ((ReferenceActivePhysicalStep.prepare r.input).feedback.observations
                      (PublicDiscreteDraws.followerPlayer p.two_le_m i))) := hq'.symm
              have hprepared : r.output.preparation =
                  ReferenceActivePhysicalStep.prepare r.input := by
                rw [r.output_eq]
                rfl
              have hstate : (r.output.preparation.followers.followers i).configuration =
                  .ordinary state memory := by
                simpa only [ReferenceFollowerFixedReply.actualChoice] using hchoice
              let follower := r.output.preparation.followers.followers i
              let observation := r.output.preparation.feedback.observations
                (PublicDiscreteDraws.followerPlayer p.two_le_m i)
              have hfinishFollower : r.output.followers i =
                  ReferenceActivePhysicalStep.finishFollower
                    r.output.preparation.coordinator.downView follower observation := by
                calc
                  r.output.followers i = (ReferenceActivePhysicalStep.step r.input).followers i := by
                    rw [r.output_eq]
                  _ = ReferenceActivePhysicalStep.finishFollower
                      (ReferenceActivePhysicalStep.prepare r.input).coordinator.downView
                      ((ReferenceActivePhysicalStep.prepare r.input).followers.followers i)
                      ((ReferenceActivePhysicalStep.prepare r.input).feedback.observations
                        (PublicDiscreteDraws.followerPlayer p.two_le_m i)) := by
                    simp only [ReferenceActivePhysicalStep.step,
                      ReferenceActivePhysicalStep.PreparedRound.observeFollower]
                  _ = ReferenceActivePhysicalStep.finishFollower
                      r.output.preparation.coordinator.downView follower observation := by
                    rw [← hprepared]
              have hfailure :
                  (ReferenceActivePhysicalStep.finishFollower
                    r.output.preparation.coordinator.downView follower observation).failure = none := by
                rw [← hfinishFollower]
                exact hf
              let recorded := ReferenceActivePhysicalStep.recordFollower
                r.output.preparation.coordinator.downView follower.follower follower.row
                follower.activation follower.time follower.active follower.arm observation state
              cases hr : recorded.result with
              | error reason =>
                  simp [ReferenceActivePhysicalStep.finishFollower, recorded, follower,
                    observation, hstate, hr] at hfailure
              | ok post =>
                  cases hrelease : DeclaredFollowerLocalRound.releaseAndFinish rate
                      follower.follower follower.row follower.time observation state memory post with
                  | error reason =>
                      simp [ReferenceActivePhysicalStep.finishFollower, recorded, follower,
                        observation, hstate, hr, hrelease] at hfailure
                  | ok pair =>
                      rcases pair with ⟨next, nextMemory⟩
                      have hsuccess := ReferenceActivePhysicalStep.finishFollower_success
                        r.output.preparation.coordinator.downView follower observation
                        state post next memory nextMemory hstate hr hrelease
                      have hactual : (r.output.followers i).configuration =
                          .ordinary next nextMemory := by
                        rw [hfinishFollower]
                        exact hsuccess.1
                      have hframe := ReferenceFollowerReplyChronology.releaseAndFinish_frame
                        follower.follower follower.row follower.time observation state post
                        next memory nextMemory hrelease
                      have hpost : post.backlog =
                          CappedService.residual (4 * rate.n) state.backlog
                            (ActiveFollowerQueueOperation.rawArrival rate.eta i r.input.row
                              r.input.time old observation) := by
                        have hrecorded : recorded.result =
                            DeclaredFollowerLocalRound.recordOrServiceThenDown rate
                              follower.follower follower.row follower.activation follower.time
                              follower.active follower.arm observation state := by
                          simp [recorded, ReferenceActivePhysicalStep.recordFollower, hu]
                        have hoccupied : state.status ≠ .unoccupied := hu
                        have hraw : ActiveFollowerQueueOperation.rawArrival rate.eta
                              follower.follower follower.row follower.time old observation =
                            ActiveFollowerQueueOperation.rawArrival rate.eta i r.input.row
                              r.input.time old observation := by
                          have halign := ReferenceActivePhysicalStep.PreparedRound.follower_alignment
                            r.output.preparation i
                          rw [halign.2.1, halign.1, halign.2.2.1]
                        have hrd := DeclaredFollowerLocalRound.recordOrServiceThenDown_occupied
                          rate follower.follower follower.row follower.activation follower.time
                          follower.active follower.arm observation state hu
                        have hchecked : ∃ result, ActiveFollowerQueueOperation.checkedService rate.eta
                              rate.sourceCap rate.n rate.n_scale follower.follower follower.row
                              follower.activation follower.time observation state = .success result := by
                          rw [hrd] at hrecorded
                          cases hh : ActiveFollowerQueueOperation.checkedService rate.eta
                              rate.sourceCap rate.n rate.n_scale follower.follower follower.row
                              follower.activation follower.time observation state with
                          | failure =>
                              have h := hr
                              rw [hrecorded] at h
                              simp [hh] at h
                          | success result => exact ⟨result, rfl⟩
                        rcases hchecked with ⟨result, hchecked⟩
                        have hpostEq : post = result.output := by
                          have h : result.output = post := by
                            have h' := hr
                            rw [hrecorded] at h'
                            rw [hrd, hchecked] at h'
                            exact Except.ok.inj h'
                          exact h.symm
                        have hresult := ActiveFollowerQueueOperation.serviceSuccess_equations result
                        have hocc : state.status.occupied := by
                          cases hs : state.status with
                          | unoccupied => exact (hu hs).elim
                          | pending => exact Or.inl rfl
                          | released => exact Or.inr rfl
                        have hupdate : result.output =
                            ActiveFollowerQueueOperation.serviceUpdate rate.n state
                              result.arrival := by
                          calc
                            result.output = ActiveFollowerQueueOperation.serviceOutput rate.n
                                state result.arrival := hresult.1
                            _ = ActiveFollowerQueueOperation.serviceUpdate rate.n state
                                result.arrival := by
                                  simp [ActiveFollowerQueueOperation.serviceOutput, hocc]
                        rw [hpostEq, hupdate]
                        simp [ActiveFollowerQueueOperation.serviceUpdate,
                          ActiveFollowerQueueOperation.serviceCapacity]
                        have harrival : result.arrival =
                            ActiveFollowerQueueOperation.rawArrival rate.eta i r.input.row
                              r.input.time old observation := by
                          have haction := hresult.2.2.2.2.2
                          rcases hocc with hpending | hreleased
                          · simp only [ActiveFollowerQueueOperation.serviceAction, hpending] at haction
                            rcases haction with ⟨_, ⟨M0, hM0, _, hraw0, _⟩⟩
                            have hM0eq : M0 = old := Option.some.inj (hM0.symm.trans hLastEq)
                            rw [hM0eq, hraw] at hraw0
                            exact hraw0
                          · simp only [ActiveFollowerQueueOperation.serviceAction, hreleased] at haction
                            rcases haction with ⟨_, ⟨M0, hM0, _, hraw0, _⟩⟩
                            have hM0eq : M0 = old := Option.some.inj (hM0.symm.trans hLastEq)
                            rw [hM0eq, hraw] at hraw0
                            exact hraw0
                        rw [harrival]
                      have hback := congrArg (fun x => x.2.2.2) hframe.1
                      have hnextPost : next.backlog = post.backlog := by
                        simpa only [ReferenceFollowerReplyChronology.reply] using hback
                      refine ⟨next, nextMemory, hactual, hf, ?_⟩
                      rw [hnextPost, hpost, hq]
                      rw [← hprepared]
            · simp [hf] at hread

private theorem observer_eq_fields
    (configuration : DeclaredFollowerLocalRound.LocalConfiguration p rate)
    (M : OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta)) (q : ℕ)
    (hobs : followerRegisterObserver? (rate := rate) (some configuration) =
      some (some M, q)) :
    ∃ state memory,
      configuration = .ordinary state memory ∧
      state.lastDown = some M ∧ state.backlog = q := by
  cases configuration with
  | dagger => simp [followerRegisterObserver?] at hobs
  | ordinary state memory =>
      have hfields : state.lastDown = some M ∧ state.backlog = q := by
        simpa [followerRegisterObserver?] using hobs
      exact ⟨state, memory, rfl, hfields.1, hfields.2⟩

private theorem inputRegister_eq_fields
    (r : Record) (i : Fin (p.m - 1))
    (M : OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta)) (q : ℕ)
    (hobs : followerInputRegister? (rate := rate) (some r) i =
      some (some M, q)) :
    ∃ state memory,
      r.input.state.followers i = .ordinary state memory ∧
      state.lastDown = some M ∧ state.backlog = q := by
  apply observer_eq_fields rate
  simpa [followerInputRegister?] using hobs

private theorem choiceRegister_eq_fields
    (r : Record) (i : Fin (p.m - 1))
    (M : OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta)) (q : ℕ)
    (hobs : followerChoiceRegister? (rate := rate) (some r) i =
      some (some M, q)) :
    ∃ state memory,
      (ReferenceFollowerFixedReply.actualChoice r i).configuration =
        .ordinary state memory ∧
      state.lastDown = some M ∧ state.backlog = q := by
  apply observer_eq_fields rate
  simpa [followerChoiceRegister?] using hobs

private theorem outputRegister_eq_fields
    (r : Record) (i : Fin (p.m - 1))
    (M : OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta)) (q : ℕ)
    (hobs : followerOutputRegister? (rate := rate) (some r) i =
      some (some M, q)) :
    ∃ state memory,
      (r.output.followers i).configuration = .ordinary state memory ∧
      state.lastDown = some M ∧ state.backlog = q := by
  apply observer_eq_fields rate
  simpa [followerOutputRegister?] using hobs

/-- Every literal current follower register in the event is covered by the
same attributed replay word from the first corrected assignment. -/
theorem currentFollowerRegisterOverflowEvent_subset_assignedAttributedOverflowEvent
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T) :
    currentFollowerRegisterOverflowEvent rate rewards C_star C_h u t ⊆
      ReferenceFirstCollectionCorrectedAssignedOverflowCover.assignedAttributedOverflowEvent
        rate rewards C_star C_h u t := by
  classical
  intro z hzEvent
  change z ∈ ReferenceFirstCollectionCorrectedSliceNumericalPrefix.correctedCell
      rate rewards C_star C_h u t ∧ _ at hzEvent
  rcases hzEvent with ⟨hz, birth, P, hb, hborn, hsigma, hsite⟩
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let b := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.birthIndex
    rate rewards C_star C_h z
  let W := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.liveTail
    rate rewards C_star C_h z
  let V := (R.drop b).take (1 + W.length)
  have hLive := ReferenceFirstCorrectedCurrentFollowerLiveQueue.actual_first_corrected_current_live_queues
    rate rewards C_star C_h u t z hz
  rcases hLive with ⟨birthL, PL, A, hbL, hbornL, hsigmaL, hV, hbound,
      _hterminal, hword, hAlength, htake, hsites⟩
  have hbirthEq : birthL = birth := Option.some.inj (hbL.symm.trans hb)
  subst birthL
  have hpayloadEq : PL = P :=
    ReferenceAssignmentPayloadChronology.installationBirth_payload_unique
      birth PL P hbornL hborn
  subst PL
  have hseed (i : Fin (p.m - 1)) :
      (P.downRecord i).val.q = P.queues (P.assignment.assigned i) :=
    P.downRecord_initialQueue i
  have hV' : V = birth :: W := by
    simpa [R, b, V] using hV
  have hVlen : V.length = 1 + W.length := by
    rw [hV']
    simp
    omega
  have hAssignedBirth :
      (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords
        rate rewards C_star C_h z)[ReferenceFirstCollectionCorrectedSliceNumericalPrefix.birthIndex
          rate rewards C_star C_h z]? = some birth := by
    simpa [R, b, ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords] using hb
  refine ⟨hz, birth, P, hAssignedBirth, hborn, hsigma, ?_⟩
  rcases hsite with hLiveSite | hCollectionSite
  · rcases hLiveSite with ⟨i, site, q, hobs, hcross⟩
    have hqReplay : ∃ v : ℕ, 1 ≤ v ∧ v ≤ V.length ∧
        (V.take v).mapM
          (ReferenceFirstCorrectedAssignedArrivalPrefix.attributedArrival? P i) =
            some ((A i).take v) ∧
        q = (QueueReplay.replay (4 * rate.n)
          (0, (P.downRecord i).val.q) ((A i).take v)).2 := by
        cases site with
        | input j =>
            obtain ⟨input, memory, choice, next, nextMemory, _hrecord, hinput,
              _hstart, _hchoice, _houtput, _hfailure, _hnext, hbirthInput,
              hinputReplay, _hchoiceReplay, _houtputReplay, _hframe⟩ := hsites i j
            have hobs' : followerInputRegister? (rate := rate) (some (V.get j)) i =
                some (some (P.downRecord i), q) := by
              simpa only [observeLiveFollowerRegister] using hobs
            have hfields := inputRegister_eq_fields rate (V.get j) i
              (P.downRecord i) q hobs'
            rcases hfields with ⟨input', memory', hinput', hlast, hbacklog⟩
            have hinputEq : input' = input := by
              have hget : V.get j = V[j.val] := rfl
              rw [hget, hinput] at hinput'
              exact ((DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
                hinput').1).symm
            subst input'
            have hjpos : 1 ≤ j.val := by
              by_contra hnot
              have hjzero : j.val = 0 := by omega
              exact (hbirthInput hjzero).1 hlast
            have hqueue := congrArg Prod.snd (hinputReplay hlast).2
            exact ⟨j.val, hjpos, Nat.le_of_lt j.isLt, htake i j.val,
              hbacklog.symm.trans hqueue⟩
        | choice j =>
            obtain ⟨input, memory, choice, next, nextMemory, _hrecord, _hinput,
              _hstart, hchoice, _houtput, _hfailure, _hnext, _hbirthInput,
              _hinputReplay, hchoiceReplay, _houtputReplay, _hframe⟩ := hsites i j
            have hobs' : followerChoiceRegister? (rate := rate) (some (V.get j)) i =
                some (some (P.downRecord i), q) := by
              simpa only [observeLiveFollowerRegister] using hobs
            have hfields := choiceRegister_eq_fields rate (V.get j) i
              (P.downRecord i) q hobs'
            rcases hfields with ⟨choice', memory', hchoice', hlast, hbacklog⟩
            have hchoiceEq : choice' = choice := by
              have hget : V.get j = V[j.val] := rfl
              rw [hget, hchoice] at hchoice'
              exact ((DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
                hchoice').1).symm
            subst choice'
            have hjpos : 1 ≤ j.val := by
              by_contra hnot
              have hjzero : j.val = 0 := by omega
              exact (_hbirthInput hjzero).2 hlast
            have hqueue := congrArg Prod.snd (hchoiceReplay hlast).2
            exact ⟨j.val, hjpos, Nat.le_of_lt j.isLt, htake i j.val,
              hbacklog.symm.trans hqueue⟩
        | output j =>
            obtain ⟨_input, _memory, _choice, next, nextMemory, _hrecord,
              _hinput, _hstart, _hchoice, houtput, _hfailure, _hnext,
              _hbirthInput, _hinputReplay, _hchoiceReplay, houtputReplay, _hframe⟩ :=
              hsites i j
            have hobs' : followerOutputRegister? (rate := rate) (some (V.get j)) i =
                some (some (P.downRecord i), q) := by
              simpa only [observeLiveFollowerRegister] using hobs
            have hfields := outputRegister_eq_fields rate (V.get j) i
              (P.downRecord i) q hobs'
            rcases hfields with ⟨next', nextMemory', houtput', hlast, hbacklog⟩
            have hnextEq : next' = next := by
              have hget : V.get j = V[j.val] := rfl
              rw [hget, houtput] at houtput'
              exact ((DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
                houtput').1).symm
            subst next'
            have hqueue := congrArg Prod.snd (houtputReplay hlast).2
            exact ⟨j.val + 1, by omega, Nat.succ_le_iff.mpr j.isLt,
              htake i (j.val + 1),
              hbacklog.symm.trans hqueue⟩
        | serviceResidual j =>
            obtain ⟨_input, _memory, choice, next, nextMemory, _hrecord,
              _hinput, _hstart, hchoice, houtput, _hfailure, _hnext,
              _hbirthInput, _hinputReplay, hchoiceReplay, houtputReplay, hframe⟩ :=
              hsites i j
            have hobs' : actualOccupiedServiceResidual? (rate := rate)
                (some (V.get j)) i = some (some (P.downRecord i), q) := by
              simpa only [observeLiveFollowerRegister] using hobs
            have hget : V.get j = V[j.val] := rfl
            have hchoiceGet :
                (ReferenceFollowerFixedReply.actualChoice (V.get j) i).configuration =
                  .ordinary choice _memory := by
              rw [hget]
              exact hchoice
            have hoccupied : choice.status ≠ .unoccupied := by
              intro hu
              have hraw := hobs'
              unfold actualOccupiedServiceResidual? at hraw
              simp only [Option.bind_some, hchoiceGet] at hraw
              simp [hu] at hraw
            have hchoiceCurrent : choice.lastDown = some (P.downRecord i) := by
              have hraw := hobs'
              unfold actualOccupiedServiceResidual? at hraw
              simp only [Option.bind_some, hchoiceGet] at hraw
              generalize hlast : choice.lastDown = current at hraw
              cases current with
              | none => simp at hraw
              | some M =>
                  have hlast' : choice.lastDown = some M := hlast
                  by_cases hf : (V[j.val].output.followers i).failure = none
                  · have hfields := by simpa [hlast', hf, hget] using hraw
                    have hM : M = P.downRecord i := hfields.2.1
                    simp [hM]
                  · simp [hf] at hraw
            have houtputCurrent : next.lastDown = some (P.downRecord i) :=
              (hframe hoccupied).2.trans hchoiceCurrent
            have hqueueOutput := congrArg Prod.snd (houtputReplay houtputCurrent).2
            have hres := actualOccupiedServiceResidual_is_output rate (V.get j) i
              (P.downRecord i) q hobs'
            rcases hres with ⟨next', nextMemory', hnext', _hfailure, hbacklog⟩
            have hnextEq : next' = next := by
              have hget : V.get j = V[j.val] := rfl
              rw [hget, houtput] at hnext'
              exact ((DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
                hnext').1).symm
            subst next'
            have hqueue : q =
                (QueueReplay.replay (4 * rate.n)
                  (0, (P.downRecord i).val.q) ((A i).take (j.val + 1))).2 :=
              hbacklog.symm.trans hqueueOutput
            exact ⟨j.val + 1, by omega, Nat.succ_le_iff.mpr j.isLt,
              htake i (j.val + 1), hqueue⟩
    rcases hqReplay with ⟨v, hv, hvle, hmap, hq⟩
    have hcrossReplay :
        ((QueueReplay.replay (4 * rate.n)
          (0, P.queues (P.assignment.assigned i)) ((A i).take v)).2 : ℝ) /
          (rate.n : ℝ) > 1 / (32 * rate.eta.val) := by
      simpa only [hq, hseed i] using hcross
    apply Or.inl
    refine ⟨i, v, (A i).take v, hv, ?_, ?_, hcrossReplay⟩
    · simpa [hVlen] using hvle
    · have hvN : v ≤ 1 + W.length := by simpa [hVlen] using hvle
      have hprefixEq : V.take v = (R.drop b).take v := by
        change ((R.drop b).take (1 + W.length)).take v = (R.drop b).take v
        rw [List.take_take, Nat.min_eq_left hvN]
      rw [hprefixEq] at hmap
      simpa [R, b, ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords] using hmap
  · rcases hCollectionSite with ⟨seg, hseg, i, site, q, hobs, hcross⟩
    have hCollection := ReferenceFirstCorrectedCurrentFollowerCollectionQueue.actual_first_corrected_current_follower_collection_queues
      rate rewards C_star C_h u t z hz birth P hb hborn hsigma
    dsimp only [R, b, W, V] at hCollection
    obtain ⟨hpayload, hqueues⟩ := hCollection seg (by simpa only [R, b, W, V] using hseg)
    obtain ⟨collectionWord, hcollectionWord, hentryInput, hentryChoice,
        hrecords, hremaining⟩ := hqueues i
    have hwordEq : collectionWord = A i :=
      Option.some.inj (hcollectionWord.symm.trans (hword i))
    have hqReplay : q =
        (QueueReplay.replay (4 * rate.n)
          (0, (P.downRecord i).val.q) (A i)).2 := by
      have hqword : q =
          (QueueReplay.replay (4 * rate.n)
            (0, (P.downRecord i).val.q) collectionWord).2 := by
          cases site with
          | cutoffInput =>
              have hobs' : followerInputRegister? (rate := rate) (some seg.entry) i =
                  some (some (P.downRecord i), q) := by
                simpa only [observeCollectionFollowerRegister] using hobs
              obtain ⟨state, memory, hconfig, hlast, hbacklog⟩ :=
                inputRegister_eq_fields rate seg.entry i (P.downRecord i) q hobs'
              exact hbacklog.symm.trans (hentryInput state memory hconfig hlast)
          | cutoffChoice =>
              have hobs' : followerChoiceRegister? (rate := rate) (some seg.entry) i =
                  some (some (P.downRecord i), q) := by
                simpa only [observeCollectionFollowerRegister] using hobs
              obtain ⟨state, memory, hconfig, hlast, hbacklog⟩ :=
                choiceRegister_eq_fields rate seg.entry i (P.downRecord i) q hobs'
              exact hbacklog.symm.trans (hentryChoice state memory hconfig hlast)
          | recordInput j =>
              let r := seg.records.get j
              have hobs' : followerInputRegister? (rate := rate) (some r) i =
                  some (some (P.downRecord i), q) := by
                simpa [observeCollectionFollowerRegister, r] using hobs
              obtain ⟨state, memory, hconfig, hlast, hbacklog⟩ :=
                inputRegister_eq_fields rate r i (P.downRecord i) q hobs'
              have hmem : r ∈ seg.records := by
                exact List.get_mem seg.records j
              exact hbacklog.symm.trans ((hrecords r hmem).1 state memory hconfig hlast)
          | recordChoice j =>
              let r := seg.records.get j
              have hobs' : followerChoiceRegister? (rate := rate) (some r) i =
                  some (some (P.downRecord i), q) := by
                simpa [observeCollectionFollowerRegister, r] using hobs
              obtain ⟨state, memory, hconfig, hlast, hbacklog⟩ :=
                choiceRegister_eq_fields rate r i (P.downRecord i) q hobs'
              have hmem : r ∈ seg.records := by
                exact List.get_mem seg.records j
              exact hbacklog.symm.trans ((hrecords r hmem).2.1 state memory hconfig hlast)
          | recordOutput j =>
              let r := seg.records.get j
              have hobs' : followerOutputRegister? (rate := rate) (some r) i =
                  some (some (P.downRecord i), q) := by
                simpa [observeCollectionFollowerRegister, r] using hobs
              obtain ⟨state, memory, hconfig, hlast, hbacklog⟩ :=
                outputRegister_eq_fields rate r i (P.downRecord i) q hobs'
              have hmem : r ∈ seg.records := by
                exact List.get_mem seg.records j
              exact hbacklog.symm.trans ((hrecords r hmem).2.2 state memory hconfig hlast)
          | remainingInput r hhead =>
              have hobs' : followerInputRegister? (rate := rate) (some r) i =
                  some (some (P.downRecord i), q) := by
                simpa only [observeCollectionFollowerRegister] using hobs
              obtain ⟨state, memory, hconfig, hlast, hbacklog⟩ :=
                inputRegister_eq_fields rate r i (P.downRecord i) q hobs'
              exact hbacklog.symm.trans ((hremaining r hhead).1 state memory hconfig hlast)
          | remainingChoice r hhead =>
              have hobs' : followerChoiceRegister? (rate := rate) (some r) i =
                  some (some (P.downRecord i), q) := by
                simpa only [observeCollectionFollowerRegister] using hobs
              obtain ⟨state, memory, hconfig, hlast, hbacklog⟩ :=
                choiceRegister_eq_fields rate r i (P.downRecord i) q hobs'
              exact hbacklog.symm.trans ((hremaining r hhead).2.1 state memory hconfig hlast)
          | remainingOutput r hhead hnotLater =>
              have hobs' : followerOutputRegister? (rate := rate) (some r) i =
                  some (some (P.downRecord i), q) := by
                simpa only [observeCollectionFollowerRegister] using hobs
              obtain ⟨state, memory, hconfig, hlast, hbacklog⟩ :=
                outputRegister_eq_fields rate r i (P.downRecord i) q hobs'
              exact hbacklog.symm.trans
                ((hremaining r hhead).2.2 hnotLater state memory hconfig hlast)
      simpa [hwordEq] using hqword
    have hcrossReplay :
        ((QueueReplay.replay (4 * rate.n)
          (0, P.queues (P.assignment.assigned i)) (A i)).2 : ℝ) /
          (rate.n : ℝ) > 1 / (32 * rate.eta.val) := by
      simpa only [hqReplay, hseed i] using hcross
    have hmap :
        (((ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h).drop
            (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.birthIndex
              rate rewards C_star C_h z)).take V.length).mapM
          (ReferenceFirstCorrectedAssignedArrivalPrefix.attributedArrival? P i) =
            some (A i) := by
      rw [hVlen]
      have h := htake i (1 + W.length)
      have hfullV : V.take (1 + W.length) = V :=
        List.take_of_length_le (by rw [hVlen])
      have hfullA : (A i).take (1 + W.length) = A i :=
        List.take_of_length_le (by rw [hAlength i, hVlen])
      rw [hfullV, hfullA] at h
      simpa [V, R, b] using h
    apply Or.inl
    refine ⟨i, V.length, A i, ?_, ?_, ?_, hcrossReplay⟩
    · rw [hVlen]
      exact Nat.le_add_right 1 W.length
    · exact le_of_eq hVlen
    · simpa [ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords] using hmap

end Bandits.Support.ReferenceFirstCorrectedCurrentFollowerQueueOverflowCover

end
