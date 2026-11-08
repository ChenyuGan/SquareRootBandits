/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ActualInitializationBlockMeasurability

/-!
# One actual initialization cursor transition

This internal adapter uses exactly the local induction tuple of
`ActualInitializationRun.foldBlockAux`. It keeps the whole original source,
the existing coordinator continuation, and all existing heterogeneous follower
states. The measurable structure is pulled back from their literal accepted
codes, with the original continuous saved-real fibers. Readiness and the next
cursor invariant are conclusions, not inputs.

Sources: `sources/zip4/manuscript/07_public_setup.tex:55-114`,
`sources/zip4/manuscript/appendix_b_communication.tex:94-165`, and
`sources/zip4/manuscript/06_interruptions.tex:235-297`.
The next consumer is the recursive within-block fold on the original decreasing
cursor/fuel, after independent acceptance of this module and
`init-begin-joint-borel`. This module does not construct that recursion.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions

namespace Bandits.Support.ActualInitializationCursorMeasurability

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ActiveFollowerDownAcceptance.RateInput

/-- The original local tuple, with no new execution state. -/
abbrev CursorTuple (p : Parameters) (rate : RateInput p) (block : Fin (n_boot p)) :=
  BootstrapPrivateRoundStreams.SourceInput p ×
    (BootstrapCoordinatorLocalRound.Continuation p × (Fin (p.m - 1) → ActualInitializationPhysicalStep.FollowerState p rate block))

/-- Literal coordinates: the entire source, the accepted continuation code,
and all accepted follower codes. -/
def cursorTupleCoordinates {p : Parameters} {rate : RateInput p}
    {block : Fin (n_boot p)} (input : CursorTuple p rate block) :=
  (input.1, (ActualInitializationBlockMeasurability.continuationCodeOf input.2.1,
    fun i => ActualInitializationRoundMeasurability.followerCodeOfState p rate block (input.2.2 i)))

instance cursorTupleMeasurableSpace (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) : MeasurableSpace (CursorTuple p rate block) :=
  MeasurableSpace.comap cursorTupleCoordinates inferInstance

/-- Exactly the existing `foldBlockAux` invariant at this cursor. Its expansion
is source alignment of block/IDs/whole selected row/target/shared constants,
cursor at most block length, each bootstrap processed cursor equal to cursor
or each declared activation at most block start + cursor + 1, and launch only
at the clipped endpoint. No successful trace or no-dagger premise is added. -/
abbrev CursorInput (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) (C_star C_h : ℝ) (cursor : ℕ) :=
  {input : CursorTuple p rate block //
    ActualInitializationRun.BlockInvariant p rate block input.1 C_star C_h cursor input.2.1 input.2.2}

variable {p : Parameters} {rate : RateInput p} {block : Fin (n_boot p)}
  {C_star C_h : ℝ} {cursor : ℕ}

theorem measurable_cursorInputCoordinates :
    Measurable (fun input : CursorInput p rate block C_star C_h cursor =>
      cursorTupleCoordinates input.1) :=
  (comap_measurable _).comp measurable_subtype_coe

/-- A launched continuation contradicts the genuine nonterminal invariant. -/
theorem phase_is_prelaunch (hcursor : cursor < BootstrapObservedFollower.blockLength p block)
    (input : CursorInput p rate block C_star C_h cursor) :
    ∃ live, input.1.2.1 = BootstrapCoordinatorLocalRound.Continuation.prelaunch live := by
  cases hphase : input.1.2.1 with
  | prelaunch live => exact ⟨live, rfl⟩
  | launched launch =>
      have hdone := input.2.2.2.2
      rw [hphase] at hdone
      exact False.elim (Nat.ne_of_lt hcursor hdone)

/-- Extract the actual existing prelaunch constructor, with no fallback. -/
def prelaunchAtCursor (hcursor : cursor < BootstrapObservedFollower.blockLength p block)
    (input : CursorInput p rate block C_star C_h cursor) : BootstrapCoordinatorLocalRound.PrelaunchBlock p :=
  match hphase : input.1.2.1 with
  | .prelaunch live => live
  | .launched launch => False.elim (by
      have hdone := input.2.2.2.2
      rw [hphase] at hdone
      exact Nat.ne_of_lt hcursor hdone)

theorem prelaunchAtCursor_eq (hcursor : cursor < BootstrapObservedFollower.blockLength p block)
    (input : CursorInput p rate block C_star C_h cursor) :
    BootstrapCoordinatorLocalRound.Continuation.prelaunch (prelaunchAtCursor hcursor input) = input.1.2.1 := by
  unfold prelaunchAtCursor
  split
  · rename_i live hphase
    exact hphase.symm
  · rename_i launch hphase
    have hdone := input.2.2.2.2
    rw [hphase] at hdone
    exact False.elim (Nat.ne_of_lt hcursor hdone)

theorem prelaunchAtCursor_aligned (hcursor : cursor < BootstrapObservedFollower.blockLength p block)
    (input : CursorInput p rate block C_star C_h cursor) :
    ActualInitializationRun.continuationAligned p block input.1.1 C_star C_h
      (.prelaunch (prelaunchAtCursor hcursor input)) := by
  rw [prelaunchAtCursor_eq]
  exact input.2.1

/-- The canonical local code of the actual prelaunch constructor. -/
def coordinatorCodeAtCursor (hcursor : cursor < BootstrapObservedFollower.blockLength p block)
    (input : CursorInput p rate block C_star C_h cursor) : BootstrapCoordinatorRoundMeasurability.CoordinatorLocalCode p :=
  (BootstrapCoordinatorRoundMeasurability.prelaunchCoordinates p (prelaunchAtCursor hcursor input)).2

theorem measurable_coordinatorCodeAtCursor (hcursor : cursor < BootstrapObservedFollower.blockLength p block) :
    Measurable (coordinatorCodeAtCursor (rate := rate) (C_star := C_star)
      (C_h := C_h) hcursor) := by
  have hphase := measurable_fst.comp (measurable_snd.comp
    (measurable_cursorInputCoordinates (rate := rate) (block := block) (C_star := C_star)
      (C_h := C_h) (cursor := cursor)))
  have hcode : Measurable (fun input : CursorInput p rate block C_star C_h cursor =>
      ((ActualInitializationBlockMeasurability.continuationCodeOf input.1.2.1).1,
        ((ActualInitializationBlockMeasurability.continuationCodeOf input.1.2.1).2.1,
          ((ActualInitializationBlockMeasurability.continuationCodeOf input.1.2.1).2.2.1,
            (ActualInitializationBlockMeasurability.continuationCodeOf input.1.2.1).2.2.2.1)))) :=
    (measurable_fst.comp hphase).prodMk
      ((measurable_fst.comp (measurable_snd.comp hphase)).prodMk
        ((measurable_fst.comp (measurable_snd.comp (measurable_snd.comp hphase))).prodMk
          (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp
            (measurable_snd.comp hphase))))))
  let codeFields : BootstrapCoordinatorRoundMeasurability.CoordinatorLocalCode p →
      Fin (n_boot p) × (Fin p.K × (BootstrapCoordinatorRoundMeasurability.CoordinatorStateCode p × BootstrapCoordinatorRoundMeasurability.MonitorCode p)) :=
    fun c => (c.block, (c.target, (c.coordinator, c.monitor.1)))
  have hinj : Function.Injective codeFields := by
    intro a b hab
    apply BootstrapCoordinatorRoundMeasurability.coordinatorLocalCodeFields_injective p
    change (a.block, (a.target, (a.coordinator, a.monitor.1))) =
      (b.block, (b.target, (b.coordinator, b.monitor.1))) at hab
    simp only [Prod.mk.injEq] at hab
    obtain ⟨hb, ht, hc, hm⟩ := hab
    exact Prod.ext hb (Prod.ext ht (Prod.ext hc (Subtype.ext hm)))
  have hmeas : MeasurableEmbedding codeFields :=
    ⟨hinj, measurable_of_countable _, fun _ _ => Set.to_countable _ |>.measurableSet⟩
  apply hmeas.measurable_comp_iff.mp
  convert hcode using 1
  funext input
  change codeFields (coordinatorCodeAtCursor hcursor input) = _
  rw [← prelaunchAtCursor_eq hcursor input]
  rfl

/-- The literal accepted round input at the original block time, with the
original selected whole row, IDs, source, fixed whole reward grid, and codes. -/
def roundInputAtCursor (hcursor : cursor < BootstrapObservedFollower.blockLength p block)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (input : CursorInput p rate block C_star C_h cursor) :
    ActualInitializationStepMeasurability.RoundInput p rate block C_star C_h :=
  ⟨ActualInitializationRun.blockTime p block cursor hcursor,
    input.1.1.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p input.1.1), input.1.1.1.1,
    coordinatorCodeAtCursor hcursor input,
    fun i => ActualInitializationRoundMeasurability.followerCodeOfState p rate block (input.1.2.2 i), input.1.1, rewards⟩

theorem measurable_roundInputAtCursor (hcursor : cursor < BootstrapObservedFollower.blockLength p block)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) :
    Measurable (roundInputAtCursor (rate := rate) (C_star := C_star)
      (C_h := C_h) hcursor rewards) := by
  have hcoords := measurable_cursorInputCoordinates (rate := rate) (block := block)
    (C_star := C_star) (C_h := C_h) (cursor := cursor)
  have hsource := measurable_fst.comp hcoords
  have hbase := (BootstrapCoordinatorRoundMeasurability.measurable_selectedCoordinatorBase p C_star C_h).comp hsource
  have hrow := measurable_fst.comp (measurable_fst.comp hbase)
  have hids := measurable_snd.comp (measurable_fst.comp hbase)
  have hfollowers := measurable_snd.comp (measurable_snd.comp hcoords)
  apply measurable_comap_iff.mpr
  exact measurable_const.prodMk (hrow.prodMk (hids.prodMk
    ((measurable_coordinatorCodeAtCursor hcursor).prodMk
      (hfollowers.prodMk (hsource.prodMk measurable_const)))))

theorem roundInputAtCursor_coordinator (hcursor : cursor < BootstrapObservedFollower.blockLength p block)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (input : CursorInput p rate block C_star C_h cursor) :
    ActualInitializationRoundMeasurability.coordinatorOfInput p rate block C_star C_h (roundInputAtCursor hcursor rewards input) =
      prelaunchAtCursor hcursor input := by
  have ha := prelaunchAtCursor_aligned hcursor input
  have hbase : ActualInitializationRoundMeasurability.coordinatorBaseOfInput p rate block C_star C_h
      (roundInputAtCursor hcursor rewards input) =
      (BootstrapCoordinatorRoundMeasurability.prelaunchCoordinates p (prelaunchAtCursor hcursor input)).1 := by
    simp only [ActualInitializationRun.continuationAligned, ActualInitializationRun.continuationData] at ha
    simp only [ActualInitializationRoundMeasurability.coordinatorBaseOfInput, roundInputAtCursor, BootstrapCoordinatorRoundMeasurability.prelaunchCoordinates,
      ha.2.1, ha.2.2.1, ha.2.2.2.2.1, ha.2.2.2.2.2]
  unfold ActualInitializationRoundMeasurability.coordinatorOfInput
  rw [hbase]
  exact BootstrapCoordinatorRoundMeasurability.reconstructPrelaunch p _

theorem roundInputAtCursor_followers (hcursor : cursor < BootstrapObservedFollower.blockLength p block)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (input : CursorInput p rate block C_star C_h cursor) :
    ActualInitializationRoundMeasurability.followersOfInput p rate block (roundInputAtCursor hcursor rewards input).followers =
      input.1.2.2 := by
  funext i
  exact ActualInitializationRoundMeasurability.followerStateOfCode_encode p rate block _

/-- Decoding the literal input fields recovers the entire original local
induction tuple, with the whole source kept as the continuous relative base. -/
theorem roundInputAtCursor_reconstructs
    (hcursor : cursor < BootstrapObservedFollower.blockLength p block)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (input : CursorInput p rate block C_star C_h cursor) :
    ((roundInputAtCursor hcursor rewards input).source,
      (BootstrapCoordinatorLocalRound.Continuation.prelaunch
        (ActualInitializationRoundMeasurability.coordinatorOfInput p rate block C_star C_h
          (roundInputAtCursor hcursor rewards input)),
        ActualInitializationRoundMeasurability.followersOfInput p rate block
          (roundInputAtCursor hcursor rewards input).followers)) = input.1 := by
  rw [roundInputAtCursor_coordinator, roundInputAtCursor_followers, prelaunchAtCursor_eq]
  rfl

/-- Readiness is derived as in `ActualInitializationRun.foldBlockAux:389-426`; only the genuine local
induction invariant and the nonterminal cursor are consumed. -/
theorem roundInputAtCursor_ready (hcursor : cursor < BootstrapObservedFollower.blockLength p block)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (input : CursorInput p rate block C_star C_h cursor) :
    ActualInitializationRoundMeasurability.roundInputReady p rate block C_star C_h (roundInputAtCursor hcursor rewards input) := by
  unfold ActualInitializationRoundMeasurability.roundInputReady
  rw [roundInputAtCursor_coordinator, roundInputAtCursor_followers]
  have ha := prelaunchAtCursor_aligned hcursor input
  have ht := ActualInitializationRun.blockTime_mem p block cursor hcursor
  refine ⟨ha.1, ht, ha.2.1, ha.2.2.1, ha.2.2.2.1, ?_⟩
  intro i
  cases hf : input.1.2.2 i with
  | bootstrap state =>
      have hc := input.2.2.2.1 i
      simp only [ActualInitializationRun.followerAtCursor, hf] at hc
      refine ⟨ht, ?_, ?_⟩
      · rw [hc]
        exact hcursor
      · rw [hc]
        rfl
  | declared row activation configuration =>
      have hc := input.2.2.2.1 i
      simp only [ActualInitializationRun.followerAtCursor, hf] at hc
      change activation.val ≤ (ActualInitializationRun.blockTime p block cursor hcursor).val + 1
      simpa only [ActualInitializationRun.blockTime] using hc

/-- The accepted ready subtype is constructed from the proved invariant adapter. -/
def readyInputAtCursor (hcursor : cursor < BootstrapObservedFollower.blockLength p block)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (input : CursorInput p rate block C_star C_h cursor) :
    ActualInitializationStepMeasurability.ReadyInput p rate block C_star C_h :=
  ⟨roundInputAtCursor hcursor rewards input, roundInputAtCursor_ready hcursor rewards input⟩

/-- The actual successful result used by the original first physical step. -/
def actualCursorResult (hcursor : cursor < BootstrapObservedFollower.blockLength p block)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (input : CursorInput p rate block C_star C_h cursor) : ActualInitializationPhysicalStep.RoundResult p rate block :=
  ActualInitializationStepMeasurability.actualRoundResultOnReady rate block C_star C_h (readyInputAtCursor hcursor rewards input)

theorem actualCursorResult_step (hcursor : cursor < BootstrapObservedFollower.blockLength p block)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (input : CursorInput p rate block C_star C_h cursor) :
    ActualInitializationPhysicalStep.step rate block (ActualInitializationRun.blockTime p block cursor hcursor) (prelaunchAtCursor hcursor input)
      input.1.2.2 input.1.1 rewards = .ok (actualCursorResult hcursor rewards input) := by
  have h := ActualInitializationStepMeasurability.actualPhysicalStepOnRoundInput_eq_ok_onReady rate block C_star C_h
    (readyInputAtCursor hcursor rewards input)
  change ActualInitializationPhysicalStep.step rate block _ _ _ _ _ = _ at h
  change ActualInitializationPhysicalStep.step rate block
    (roundInputAtCursor hcursor rewards input).time
    (ActualInitializationRoundMeasurability.coordinatorOfInput p rate block C_star C_h
      (roundInputAtCursor hcursor rewards input))
    (ActualInitializationRoundMeasurability.followersOfInput p rate block
      (roundInputAtCursor hcursor rewards input).followers)
    (roundInputAtCursor hcursor rewards input).source rewards =
      .ok (actualCursorResult hcursor rewards input) at h
  rw [roundInputAtCursor_coordinator, roundInputAtCursor_followers] at h
  exact h

private theorem bufferCodes_ofFn {n : ℕ}
    (skeleton : FollowerDownJointMeasurability.BufferSkeletonCode p n)
    (values : FollowerDownMeasurability.SavedScalarFamily n) :
    let buffer := FollowerDownJointMeasurability.bufferFromSkeletonAndScalars skeleton values
    HEq (FollowerDownJointMeasurability.bufferSkeletonCode buffer) skeleton ∧
      HEq (FollowerDownJointMeasurability.bufferScalarsCode buffer) values := by
  dsimp only
  have hlen : (FollowerDownJointMeasurability.bufferFromSkeletonAndScalars
      skeleton values).length = n := List.length_ofFn
  constructor
  · apply (Fin.heq_fun_iff hlen).mpr
    intro i
    change ((List.ofFn fun j : Fin n =>
      (⟨(skeleton j).1, (skeleton j).2, (values j).1, (values j).2⟩ :
        SparseCalendarReplay.SparseCalendarRecord p.K))[i.val].calendarRound,
      (List.ofFn fun j : Fin n =>
      (⟨(skeleton j).1, (skeleton j).2, (values j).1, (values j).2⟩ :
        SparseCalendarReplay.SparseCalendarRecord p.K))[i.val].pilot) = _
    simp only [List.getElem_ofFn]
  · apply (Fin.heq_fun_iff hlen).mpr
    intro i
    change ((List.ofFn fun j : Fin n =>
      (⟨(skeleton j).1, (skeleton j).2, (values j).1, (values j).2⟩ :
        SparseCalendarReplay.SparseCalendarRecord p.K))[i.val].observation,
      (List.ofFn fun j : Fin n =>
      (⟨(skeleton j).1, (skeleton j).2, (values j).1, (values j).2⟩ :
        SparseCalendarReplay.SparseCalendarRecord p.K))[i.val].thinScalar) = _
    simp only [List.getElem_ofFn]

/-- Re-encoding a literal follower code preserves every coordinate. This is
a codec identity, including all original saved-real fibers, not a transition. -/
theorem followerCodeOfState_decode
    (code : ActualInitializationRoundMeasurability.FollowerCode p rate block) :
    ActualInitializationRoundMeasurability.followerCodeOfState p rate block
      (ActualInitializationRoundMeasurability.followerStateOfCode p rate block code) = code := by
  cases code with
  | inl startup => rfl
  | inr fields =>
      rcases fields with ⟨row, activation, configuration⟩
      cases configuration with
      | none => rfl
      | some data =>
          rcases data with ⟨⟨⟨registers, ⟨n, skeleton⟩⟩, values⟩, memory⟩
          cases registers with
          | mk lastDown score delta backlog status batch failure =>
              fin_cases status <;>
                simp [ActualInitializationRoundMeasurability.followerCodeOfState,
                  ActualInitializationRoundMeasurability.followerStateOfCode,
                  FollowerPrepareJointMeasurability.incomingOfLocalConfiguration,
                  FollowerPrepareJointMeasurability.localConfigurationOfIncoming,
                  FollowerObservationStageMeasurabilityRepair.carriedStateOfState,
                  FollowerObservationStageMeasurabilityRepair.reconstructCarriedState,
                  FollowerDownMeasurability.followerStateCode,
                  FollowerDownMeasurability.followerStateOfCode,
                  FollowerDownMeasurability.followerStatusCode,
                  FollowerDownMeasurability.followerStatusOfCode,
                  FollowerDownMeasurability.decoderBatchCode,
                  FollowerDownMeasurability.decoderBatchOfCode,
                  FollowerDownMeasurability.decoderEntryCode,
                  FollowerDownMeasurability.decoderEntryOfCode,
                  FollowerDownJointMeasurability.bufferFromSkeletonAndScalars,
                  FollowerLifecycleMeasurability.localMemoryCodeOfCode,
                  List.map_map, Function.comp_def]
              all_goals exact bufferCodes_ofFn skeleton values

open BootstrapCoordinatorLocalRound BootstrapPhysicalInput ActiveRoundActions
open ActualInitializationPhysicalStep ActualInitializationRun

/-- Preservation mined from the original `foldBlockAux`, for an actual round
result at the current source time. The visible metadata input identifies its
time; the other input is precisely the old local induction invariant on its
prepared original source/coordinator/followers. No successor law is assumed. -/
theorem blockInvariant_after_round
    (result : ActualInitializationPhysicalStep.RoundResult p rate block)
    (hcursor : cursor < BootstrapObservedFollower.blockLength p block)
    (htimeval : result.prepared.time.val =
      BootstrapObservedFollower.blockStart p block + cursor)
    (hinvariant : ActualInitializationRun.BlockInvariant p rate block
      result.prepared.source C_star C_h cursor
      (.prelaunch result.prepared.coordinatorInput) result.prepared.followerInputs) :
    ActualInitializationRun.BlockInvariant p rate block result.prepared.source C_star C_h
      (cursor + 1) result.coordinator.next (fun i => (result.followers i).next) := by
  let source := result.prepared.source
  let coordinator := result.prepared.coordinatorInput
  let followers := result.prepared.followerInputs
  let followers' := fun i => (result.followers i).next
  have hready := result.prepared.readiness
  have htime := hready.2.1
  have hcoordinatorTime : result.prepared.time ∈ calendarBlock p coordinator.data.block := by
    rw [hready.1]
    exact htime
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hnextEq := roundResult_next_eq result
    have hdata : continuationData p result.coordinator.next =
        updateLocalCoordinatorState p coordinator.data
          (BootstrapCoordinatorLocalRound.observationUpdate p coordinator.data.row
            coordinator.data.ids coordinator.data.coordinator
            result.prepared.time
            (result.feedback (ActiveRoundActions.coordinator p.two_le_m))) := by
      rw [hnextEq]
      exact
        continuationAfterObservation_data p coordinator.data coordinator.monitor
          coordinator.data.coordinator result.prepared.time
          hcoordinatorTime
          (result.feedback (ActiveRoundActions.coordinator p.two_le_m))
    change
      (continuationData p result.coordinator.next).block = block ∧
        (continuationData p result.coordinator.next).ids = source.1.1 ∧
        (continuationData p result.coordinator.next).row =
          source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) ∧
        (continuationData p result.coordinator.next).target =
          BootstrapPhysicalInput.targetArmMap p block source.2 ∧
        (continuationData p result.coordinator.next).C_star = C_star ∧
        (continuationData p result.coordinator.next).C_h = C_h
    have hAligned : coordinator.data.block = block ∧
        coordinator.data.ids = source.1.1 ∧
        coordinator.data.row = source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source) ∧
        coordinator.data.target = BootstrapPhysicalInput.targetArmMap p block source.2 ∧
        coordinator.data.C_star = C_star ∧ coordinator.data.C_h = C_h := by
      simpa [continuationAligned, continuationData] using hinvariant.1
    have hAligned' :
        (continuationData p result.coordinator.next).block = block ∧
          (continuationData p result.coordinator.next).ids = source.1.1 ∧
          (continuationData p result.coordinator.next).row = source.1.2
            (ActualInitializationPhysicalStep.selectedRowIndex p source) ∧
          (continuationData p result.coordinator.next).target =
            BootstrapPhysicalInput.targetArmMap p block source.2 ∧
          (continuationData p result.coordinator.next).C_star = C_star ∧
          (continuationData p result.coordinator.next).C_h = C_h := by
      rw [hdata]
      simpa [updateLocalCoordinatorState] using hAligned
    exact hAligned'
  · omega
  · intro i
    cases hf : result.prepared.followerInputs i with
    | bootstrap state =>
        have hc := hinvariant.2.2.1 i
        simp only [followerAtCursor, hf] at hc
        have hnext := result.followerTransition i
        let arm := BootstrapObservedFollower.localArm p block state source.1.1
          result.prepared.time
          (fun t => BootstrapPhysicalInput.playerRoundScalarAt p source.2
            (PublicDiscreteDraws.followerPlayer p.two_le_m i) t)
        have hprepared' : result.prepared.followers i = .bootstrap state arm := by
          have hreadyI := hready.2.2.2.2.2 i
          have hreadyState : ActualInitializationPhysicalStep.followerAtNextCursor
              result.prepared.time
              (.bootstrap state : ActualInitializationPhysicalStep.FollowerState p rate block) := by
            simpa [hf] using hreadyI
          have hfield : result.prepared.followers i =
              ActualInitializationPhysicalStep.prepareFollowerValid rate block
                result.prepared.time source i (followers i) hreadyI := by
            exact result.prepared.followers_eq i
          have hcongr := prepareFollowerValid_congr
            result.prepared.time source i (followers i)
            (.bootstrap state : ActualInitializationPhysicalStep.FollowerState p rate block)
            hf hreadyI hreadyState
          have hbranch :
              ActualInitializationPhysicalStep.prepareFollowerValid rate block
                result.prepared.time source i
                (.bootstrap state : ActualInitializationPhysicalStep.FollowerState p rate block)
                hreadyState =
                  .bootstrap state arm := by
            rfl
          exact hfield.trans (hcongr.trans hbranch)
        have hopen : state.processed.val < BootstrapObservedFollower.blockLength p block := by
          rw [hc]
          exact hcursor
        have hcurrent : result.prepared.time.val =
            BootstrapObservedFollower.blockStart p block + state.processed.val := by
          rw [hc]
          exact htimeval
        let ownFeedback := result.feedback
          (PublicDiscreteDraws.followerPlayer p.two_le_m i)
        let next := BootstrapObservedFollower.observeOne p block state source.1.1
          source.1.2 result.prepared.time
          (ActualInitializationPhysicalStep.observationOfGrid p ownFeedback)
          htime hopen hcurrent
        have hobs := BootstrapObservedFollower.observe_accepted_processed p block state
          source.1.1 source.1.2 result.prepared.time
          (ActualInitializationPhysicalStep.observationOfGrid p ownFeedback)
          htime hopen hcurrent
        have hstartup :=
          ActualInitializationPhysicalStep.observeFollower_bootstrap_next_is_startup
            rate block result.prepared.time source i state next arm
            ownFeedback hobs
        have hstate : (result.followers i).next = .bootstrap next := by
          rw [hprepared'] at hnext
          have hnext' : observeFollower rate block
              result.prepared.time source i
              (.bootstrap state arm) ownFeedback = .ok (result.followers i) := by
            simpa only [ownFeedback,
              ActualInitializationPhysicalStep.RoundResult.feedback] using hnext
          rw [hstartup] at hnext'
          exact congrArg FollowerOutcome.next (Except.ok.inj hnext').symm
        change followerAtCursor p rate block (cursor + 1)
          ((result.followers i).next)
        rw [hstate]
        change next.processed.val = cursor + 1
        have hprocessed := BootstrapObservedFollower.observe_accepted_cursor p block
          state source.1.1 source.1.2 result.prepared.time
          (ActualInitializationPhysicalStep.observationOfGrid p ownFeedback)
          htime hopen hcurrent
        rw [hprocessed, hc]
    | declared row activation configuration =>
        have hc := hinvariant.2.2.1 i
        simp only [followerAtCursor, hf] at hc
        have hactive : activation.val ≤ result.prepared.time.val + 1 := by
          simpa only [htimeval] using hc
        have hprepared' : result.prepared.followers i =
            .declared row activation
              (DeclaredFollowerLocalRound.prepare rate i (source.1.2 row) activation
                result.prepared.time hactive configuration) := by
          have hreadyI := hready.2.2.2.2.2 i
          have hreadyState : ActualInitializationPhysicalStep.followerAtNextCursor
              result.prepared.time
              (.declared row activation configuration :
                ActualInitializationPhysicalStep.FollowerState p rate block) := by
            simpa [hf] using hreadyI
          have hfield : result.prepared.followers i =
              ActualInitializationPhysicalStep.prepareFollowerValid rate block
                result.prepared.time source i (followers i) hreadyI := by
            exact result.prepared.followers_eq i
          have hcongr := prepareFollowerValid_congr
            result.prepared.time source i (followers i)
            (.declared row activation configuration :
              ActualInitializationPhysicalStep.FollowerState p rate block)
            hf hreadyI hreadyState
          have hbranch :
              ActualInitializationPhysicalStep.prepareFollowerValid rate block
                result.prepared.time source i
                (.declared row activation configuration :
                  ActualInitializationPhysicalStep.FollowerState p rate block) hreadyState =
                  .declared row activation
                    (DeclaredFollowerLocalRound.prepare rate i (source.1.2 row)
                      activation result.prepared.time hactive configuration) := by
            rfl
          exact hfield.trans (hcongr.trans hbranch)
        have hnext := result.followerTransition i
        rw [hprepared'] at hnext
        let round := DeclaredFollowerLocalRound.prepare rate i
          (source.1.2 row) activation result.prepared.time
          hactive configuration
        have hdeclared :=
          ActualInitializationPhysicalStep.observeFollower_declared_eq
            rate block result.prepared.time source i row activation
            round (result.feedback
              (PublicDiscreteDraws.followerPlayer p.two_le_m i))
        have hnext' : observeFollower rate block
            result.prepared.time source i (.declared row activation round)
            (result.feedback (PublicDiscreteDraws.followerPlayer p.two_le_m i)) =
              .ok (result.followers i) := by
          simpa only [
            ActualInitializationPhysicalStep.RoundResult.feedback] using hnext
        have hstate := congrArg FollowerOutcome.next
          (Except.ok.inj (hdeclared.symm.trans hnext'))
        change followerAtCursor p rate block (cursor + 1)
          ((result.followers i).next)
        rw [← hstate]
        simp only [followerAtCursor]
        omega
  · cases hphase : result.coordinator.next with
    | prelaunch live => trivial
    | launched launch =>
        have hnextEq := roundResult_next_eq result
        have hphaseObs : BootstrapCoordinatorLocalRound.continuationAfterObservation p
            coordinator.data coordinator.monitor coordinator.data.coordinator
            result.prepared.time hcoordinatorTime
            (result.feedback (ActiveRoundActions.coordinator p.two_le_m)) =
              .launched launch := by
          exact hnextEq.symm.trans hphase
        have hlaunchData : launch.data =
            updateLocalCoordinatorState p coordinator.data
              (BootstrapCoordinatorLocalRound.observationUpdate p
                coordinator.data.row coordinator.data.ids coordinator.data.coordinator
                result.prepared.time
                (result.feedback (ActiveRoundActions.coordinator p.two_le_m))) := by
          have hdata := continuationAfterObservation_data p coordinator.data
            coordinator.monitor coordinator.data.coordinator
            result.prepared.time hcoordinatorTime
            (result.feedback (ActiveRoundActions.coordinator p.two_le_m))
          rw [hphaseObs] at hdata
          simpa [continuationData] using hdata
        have hlaunchBlock : launch.data.block = block := by
          have hblock := congrArg
            (fun data : BootstrapCoordinatorLocalRound.LocalData p => data.block)
            hlaunchData
          simpa [updateLocalCoordinatorState] using hblock.trans hinvariant.1.1
        have htrigger := continuationAfterObservation_launched_trigger
          coordinator.data coordinator.monitor coordinator.data.coordinator
          result.prepared.time hcoordinatorTime
          (result.feedback (ActiveRoundActions.coordinator p.two_le_m)) launch hphaseObs
        have hlaunchInBlock : launch.triggerRound ∈
            BootstrapDimensions.calendarBlock p block := by
          rw [← hlaunchBlock]
          exact launch.triggerInBlock
        have hquot := (BootstrapDimensions.mem_calendarBlock_iff_quotient p block
          launch.triggerRound).1 hlaunchInBlock
        have hindex : BootstrapDimensions.roundBlockIndex p
            result.prepared.time = block := by
          apply Fin.ext
          change result.prepared.time.val / B_boot p = block.val
          rw [← htrigger]
          exact hquot.symm
        have hendpoint := launch.triggerAtBlockEnd
        unfold BootstrapLaunchMonitor.calendarBlockEnd at hendpoint
        rw [htrigger, hindex, BootstrapDimensions.manuscriptRound] at hendpoint
        have hend : launch.triggerRound.val + 1 =
            BootstrapObservedFollower.blockStop p block := by
          rw [htrigger, BootstrapObservedFollower.blockStop]
          exact hendpoint
        have htriggerVal := congrArg Fin.val htrigger
        rw [htimeval] at htriggerVal
        have hstartstop : BootstrapObservedFollower.blockStart p block +
            BootstrapObservedFollower.blockLength p block =
              BootstrapObservedFollower.blockStop p block := by
          have hle := Nat.le_of_lt
            (BootstrapObservedFollower.blockStart_lt_blockStop p block)
          unfold BootstrapObservedFollower.blockLength
          omega
        rw [htriggerVal, ← hstartstop] at hend
        omega

/-- The actual one-cursor output satisfies the original next induction state. -/
theorem actualCursorResult_invariant
    (hcursor : cursor < BootstrapObservedFollower.blockLength p block)
    (rewards : GridRewardTable p)
    (input : CursorInput p rate block C_star C_h cursor) :
    BlockInvariant p rate block input.1.1 C_star C_h (cursor + 1)
      (actualCursorResult hcursor rewards input).coordinator.next
      (fun i => ((actualCursorResult hcursor rewards input).followers i).next) := by
  apply blockInvariant_after_round (actualCursorResult hcursor rewards input) hcursor
  · rfl
  · change BlockInvariant p rate block input.1.1 C_star C_h cursor
      (.prelaunch (ActualInitializationRoundMeasurability.coordinatorOfInput p rate block
        C_star C_h (roundInputAtCursor hcursor rewards input)))
      (ActualInitializationRoundMeasurability.followersOfInput p rate block
        (roundInputAtCursor hcursor rewards input).followers)
    rw [roundInputAtCursor_coordinator, roundInputAtCursor_followers, prelaunchAtCursor_eq]
    exact input.2

/-- Canonical successor coordinates of every actual heterogeneous follower. -/
def followerSuccessorCodeAtCursor
    (hcursor : cursor < BootstrapObservedFollower.blockLength p block)
    (rewards : GridRewardTable p)
    (input : CursorInput p rate block C_star C_h cursor) (i : Fin (p.m - 1)) :
    ActualInitializationRoundMeasurability.FollowerCode p rate block :=
  ActualInitializationRoundMeasurability.followerCodeOfState p rate block
    ((actualCursorResult hcursor rewards input).followers i).next

/-- The accepted successor projection equals the canonical code of this same
actual result. It is not an independent successor field supplied as input. -/
theorem actualFollowerSuccessorCode_eq
    (hcursor : cursor < BootstrapObservedFollower.blockLength p block)
    (rewards : GridRewardTable p)
    (input : CursorInput p rate block C_star C_h cursor) (i : Fin (p.m - 1)) :
    ActualInitializationStepMeasurability.actualFollowerSuccessorCodeOnRoundInput
      rate block C_star C_h (roundInputAtCursor hcursor rewards input) i =
      .inr (followerSuccessorCodeAtCursor hcursor rewards input i) := by
  have h := ActualInitializationStepMeasurability.actualFollowerSuccessorCodeOnRoundInput_reconstructs_onReady rate block C_star C_h
      (readyInputAtCursor hcursor rewards input) i
  change Sum.map id (ActualInitializationRoundMeasurability.followerStateOfCode p rate block)
    (ActualInitializationStepMeasurability.actualFollowerSuccessorCodeOnRoundInput
      rate block C_star C_h (roundInputAtCursor hcursor rewards input) i) =
      .inr ((actualCursorResult hcursor rewards input).followers i).next at h
  cases hc : ActualInitializationStepMeasurability.actualFollowerSuccessorCodeOnRoundInput
      rate block C_star C_h (roundInputAtCursor hcursor rewards input) i with
  | inl error => simp only [hc, Sum.map_inl, Sum.inl_ne_inr] at h
  | inr code =>
      simp only [hc, Sum.map_inr, Sum.inr.injEq] at h
      unfold followerSuccessorCodeAtCursor
      rw [← h, followerCodeOfState_decode]

theorem measurable_followerSuccessorCodeAtCursor
    (hcursor : cursor < BootstrapObservedFollower.blockLength p block)
    (rewards : GridRewardTable p) (i : Fin (p.m - 1)) :
    Measurable (fun input : CursorInput p rate block C_star C_h cursor =>
      followerSuccessorCodeAtCursor hcursor rewards input i) := by
  have h := (ActualInitializationStepMeasurability.measurable_actualFollowerSuccessorCodeOnRoundInput rate block C_star C_h i).comp
      (measurable_roundInputAtCursor hcursor rewards)
  have heq := funext (fun input : CursorInput p rate block C_star C_h cursor =>
    actualFollowerSuccessorCode_eq hcursor rewards input i)
  dsimp only [Function.comp_def] at h
  rw [heq] at h
  intro t ht
  convert h (ht.inr_image (α := Unit)) using 1
  ext input
  simp only [Set.mem_preimage, Sum.inr_injective.mem_set_image]

/-- The coordinator successor projection identifies all actual registers,
monitor fields and the legitimate continue/launch tag of this same result. -/
theorem actualCoordinatorSuccessorCode_eq
    (hcursor : cursor < BootstrapObservedFollower.blockLength p block)
    (rewards : GridRewardTable p)
    (input : CursorInput p rate block C_star C_h cursor) :
    ActualInitializationStepMeasurability.actualCoordinatorSuccessorCodeOnRoundInput
      rate block C_star C_h (roundInputAtCursor hcursor rewards input) =
      .inr (ActualInitializationStepMeasurability.coordinatorSuccessorCodeOfObservation
        (actualCursorResult hcursor rewards input).coordinator) :=
  ActualInitializationStepMeasurability.actualCoordinatorSuccessorCodeOnRoundInput_eq_onReady
    rate block C_star C_h (readyInputAtCursor hcursor rewards input)

theorem measurable_coordinatorSuccessorCodeAtCursor
    (hcursor : cursor < BootstrapObservedFollower.blockLength p block)
    (rewards : GridRewardTable p) :
    Measurable (fun input : CursorInput p rate block C_star C_h cursor =>
      ActualInitializationStepMeasurability.coordinatorSuccessorCodeOfObservation
        (actualCursorResult hcursor rewards input).coordinator) := by
  have h := (ActualInitializationStepMeasurability.measurable_actualCoordinatorSuccessorCodeOnRoundInput rate block C_star C_h).comp
      (measurable_roundInputAtCursor hcursor rewards)
  have heq := funext (fun input : CursorInput p rate block C_star C_h cursor =>
    actualCoordinatorSuccessorCode_eq hcursor rewards input)
  dsimp only [Function.comp_def] at h
  rw [heq] at h
  intro t ht
  convert h (ht.inr_image (α := Unit)) using 1
  ext input
  simp only [Set.mem_preimage, Sum.inr_injective.mem_set_image]

/-- The canonical continuation code keeps block and target as well as the
actual successor counters, monitor/crossing and optional launch trigger. -/
def continuationSuccessorCodeAtCursor
    (hcursor : cursor < BootstrapObservedFollower.blockLength p block)
    (rewards : GridRewardTable p)
    (input : CursorInput p rate block C_star C_h cursor) :
    ActualInitializationBlockMeasurability.ContinuationCode p :=
  ActualInitializationBlockMeasurability.continuationCodeOf
    (actualCursorResult hcursor rewards input).coordinator.next

theorem continuationSuccessorCodeAtCursor_eq
    (hcursor : cursor < BootstrapObservedFollower.blockLength p block)
    (rewards : GridRewardTable p)
    (input : CursorInput p rate block C_star C_h cursor) :
    continuationSuccessorCodeAtCursor hcursor rewards input =
      (block, (BootstrapPhysicalInput.targetArmMap p block input.1.1.2,
        (ActualInitializationStepMeasurability.coordinatorSuccessorCodeOfObservation
          (actualCursorResult hcursor rewards input).coordinator).2)) := by
  have ha := (actualCursorResult_invariant hcursor rewards input).1
  unfold continuationSuccessorCodeAtCursor
    ActualInitializationBlockMeasurability.continuationCodeOf
  rw [ha.1, ha.2.2.2.1]
  rfl

theorem measurable_continuationSuccessorCodeAtCursor
    (hcursor : cursor < BootstrapObservedFollower.blockLength p block)
    (rewards : GridRewardTable p) :
    Measurable (continuationSuccessorCodeAtCursor (rate := rate)
      (C_star := C_star) (C_h := C_h) hcursor rewards) := by
  have hsource := measurable_fst.comp (measurable_cursorInputCoordinates
    (rate := rate) (block := block) (C_star := C_star) (C_h := C_h) (cursor := cursor))
  have htarget := (BootstrapPhysicalInput.measurable_targetArmMap p block).comp
    (measurable_snd.comp hsource)
  have hsucc := measurable_coordinatorSuccessorCodeAtCursor (rate := rate)
    (C_star := C_star) (C_h := C_h) hcursor rewards
  have heq := funext (fun input : CursorInput p rate block C_star C_h cursor =>
    continuationSuccessorCodeAtCursor_eq hcursor rewards input)
  rw [heq]
  exact measurable_const.prodMk (htarget.prodMk (measurable_snd.comp hsucc))

/-- One joint output: the complete accepted same-step round code, the actual
continuation code, and every complete heterogeneous follower successor code. -/
abbrev ActualCursorOutputCode (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) :=
  ActualInitializationStepMeasurability.ActualRoundOutputCode p rate block ×
    (ActualInitializationBlockMeasurability.ContinuationCode p ×
      (Fin (p.m - 1) → ActualInitializationRoundMeasurability.FollowerCode p rate block))

/-- The actual joint producer at one cursor. Its continuous buffers and decoder
banks use the accepted literal fibers; no discrete structure is imposed on them. -/
def actualCursorOutputCode
    (hcursor : cursor < BootstrapObservedFollower.blockLength p block)
    (rewards : GridRewardTable p)
    (input : CursorInput p rate block C_star C_h cursor) : ActualCursorOutputCode p rate block :=
  (ActualInitializationStepMeasurability.actualRoundOutputCode rate block C_star C_h
      (roundInputAtCursor hcursor rewards input),
    (continuationSuccessorCodeAtCursor hcursor rewards input,
      fun i => followerSuccessorCodeAtCursor hcursor rewards input i))

/-- Joint Borel measurability on the genuine local induction domain. -/
theorem measurable_actualCursorOutputCode
    (hcursor : cursor < BootstrapObservedFollower.blockLength p block)
    (rewards : GridRewardTable p) :
    Measurable (actualCursorOutputCode (rate := rate) (C_star := C_star)
      (C_h := C_h) hcursor rewards) := by
  have hround := (ActualInitializationStepMeasurability.measurable_actualRoundOutputCode
    rate block C_star C_h).comp (measurable_roundInputAtCursor hcursor rewards)
  have hfollowers := measurable_pi_iff.mpr (fun i =>
    measurable_followerSuccessorCodeAtCursor (rate := rate) (C_star := C_star)
      (C_h := C_h) hcursor rewards i)
  exact hround.prodMk ((measurable_continuationSuccessorCodeAtCursor hcursor rewards).prodMk
    hfollowers)

/-- Relative reconstruction uses the original input explicitly. The stored
complete round code is decoded by the accepted decoder; the two successor
coordinate families are checked against that reconstruction. This decoder
does not execute `step` or use `actualCursorResult` as its output. -/
def decodeCursorOutputCode
    (hcursor : cursor < BootstrapObservedFollower.blockLength p block)
    (rewards : GridRewardTable p)
    (input : CursorInput p rate block C_star C_h cursor)
    (code : ActualCursorOutputCode p rate block) : Option (RoundResult p rate block) := by
  classical
  match ActualInitializationStepMeasurability.decodeActualRoundOutputCode
      rate block C_star C_h (roundInputAtCursor hcursor rewards input) code.1 with
  | some (.ok result) =>
      exact if code.2.1 = ActualInitializationBlockMeasurability.continuationCodeOf
          result.coordinator.next ∧ code.2.2 =
            (fun i => ActualInitializationRoundMeasurability.followerCodeOfState p rate block
              (result.followers i).next) then some result else none
  | _ => exact none

/-- The complete stored round code reconstructs the exact original successful
physical step, including all preparation and observation metadata. -/
theorem actualCursorOutputCode_round_reconstructs
    (hcursor : cursor < BootstrapObservedFollower.blockLength p block)
    (rewards : GridRewardTable p)
    (input : CursorInput p rate block C_star C_h cursor) :
    ActualInitializationStepMeasurability.decodeActualRoundOutputCode rate block C_star C_h
      (roundInputAtCursor hcursor rewards input)
      (actualCursorOutputCode hcursor rewards input).1 =
        some (.ok (actualCursorResult hcursor rewards input)) := by
  change ActualInitializationStepMeasurability.decodeActualRoundOutputCode rate block C_star C_h
    (roundInputAtCursor hcursor rewards input)
    (ActualInitializationStepMeasurability.actualRoundOutputCode rate block C_star C_h
      (roundInputAtCursor hcursor rewards input)) = _
  rw [ActualInitializationStepMeasurability.decodeActualRoundOutputCode_eq_actualPhysicalStep]
  congr 1
  exact ActualInitializationStepMeasurability.actualPhysicalStepOnRoundInput_eq_ok_onReady
    rate block C_star C_h (readyInputAtCursor hcursor rewards input)

/-- Exact decoding of the joint output on the same original input. -/
theorem decodeCursorOutputCode_actual
    (hcursor : cursor < BootstrapObservedFollower.blockLength p block)
    (rewards : GridRewardTable p)
    (input : CursorInput p rate block C_star C_h cursor) :
    decodeCursorOutputCode hcursor rewards input (actualCursorOutputCode hcursor rewards input) =
      some (actualCursorResult hcursor rewards input) := by
  have hr := actualCursorOutputCode_round_reconstructs hcursor rewards input
  unfold decodeCursorOutputCode
  rw [hr]
  simp only [actualCursorOutputCode, continuationSuccessorCodeAtCursor,
    followerSuccessorCodeAtCursor, and_self, ite_true]

/-- The joint code retains exactly the continuation and each actual follower
successor of this same physical result, not a branchwise replacement. -/
theorem actualCursorOutputCode_successors
    (hcursor : cursor < BootstrapObservedFollower.blockLength p block)
    (rewards : GridRewardTable p)
    (input : CursorInput p rate block C_star C_h cursor) :
    (actualCursorOutputCode hcursor rewards input).2.1 =
        ActualInitializationBlockMeasurability.continuationCodeOf
          (actualCursorResult hcursor rewards input).coordinator.next ∧
      ∀ i, ActualInitializationRoundMeasurability.followerStateOfCode p rate block
        ((actualCursorOutputCode hcursor rewards input).2.2 i) =
          ((actualCursorResult hcursor rewards input).followers i).next :=
  ⟨rfl, fun _ => ActualInitializationRoundMeasurability.followerStateOfCode_encode
    p rate block _⟩

/-- Every player's own action and grid observation are the corresponding
entries in the full actual result consumed by the first step of the fold. -/
theorem actualCursorOutputCode_own_entry
    (hcursor : cursor < BootstrapObservedFollower.blockLength p block)
    (rewards : GridRewardTable p)
    (input : CursorInput p rate block C_star C_h cursor) (player : Fin p.m) :
    ActualInitializationStepMeasurability.physicalOwnEntryFromActualRoundOutput rate block
      (actualCursorOutputCode hcursor rewards input).1 player =
      .inr ((actualCursorResult hcursor rewards input).actions player,
        (actualCursorResult hcursor rewards input).feedback player) :=
  ActualInitializationStepMeasurability.actualPhysicalOwnEntryOnRoundInput_eq_onReady
    rate block C_star C_h (readyInputAtCursor hcursor rewards input) player

/-- Identification with any result of the exact original first physical step
in `foldBlockAux`; determinism makes the identification independent of how
that result's proof witnesses were assembled. -/
theorem actualCursorResult_eq_of_step
    (hcursor : cursor < BootstrapObservedFollower.blockLength p block)
    (rewards : GridRewardTable p)
    (input : CursorInput p rate block C_star C_h cursor) (result : RoundResult p rate block)
    (hstep : step rate block (blockTime p block cursor hcursor)
      (prelaunchAtCursor hcursor input) input.1.2.2 input.1.1 rewards = .ok result) :
    actualCursorResult hcursor rewards input = result :=
  Except.ok.inj ((actualCursorResult_step hcursor rewards input).symm.trans hstep)

/-- An actual launch is retained on the last physical step, including a launch
whose following round is beyond the horizon. No global no-launch assumption
is used to obtain the next induction state. -/
theorem actualCursorResult_launched
    (hcursor : cursor < BootstrapObservedFollower.blockLength p block)
    (rewards : GridRewardTable p)
    (input : CursorInput p rate block C_star C_h cursor) (launch : LaunchedBlock p)
    (hlaunch : (actualCursorResult hcursor rewards input).coordinator.next = .launched launch) :
    cursor + 1 = BootstrapObservedFollower.blockLength p block ∧
      launch.triggerRound = blockTime p block cursor hcursor ∧
      (actualCursorOutputCode hcursor rewards input).2.1.2.2.2.2 =
        some (blockTime p block cursor hcursor) := by
  have hi := (actualCursorResult_invariant hcursor rewards input).2.2.2
  rw [hlaunch] at hi
  let result := actualCursorResult hcursor rewards input
  have ht : result.prepared.time ∈ calendarBlock p result.prepared.coordinatorInput.data.block := by
    rw [result.prepared.readiness.1]
    exact result.prepared.readiness.2.1
  have ho := (roundResult_next_eq result).symm.trans hlaunch
  have htrigger := continuationAfterObservation_launched_trigger
    result.prepared.coordinatorInput.data result.prepared.coordinatorInput.monitor
    result.prepared.coordinatorInput.data.coordinator result.prepared.time ht
    (result.feedback (coordinator p.two_le_m)) launch ho
  have htrigger' : launch.triggerRound = blockTime p block cursor hcursor := htrigger
  refine ⟨hi, htrigger', ?_⟩
  change (match (actualCursorResult hcursor rewards input).coordinator.next with
    | .prelaunch _ => none
    | .launched launch => some launch.triggerRound) = _
  rw [hlaunch]
  exact congrArg some htrigger'

/-- The exact next local induction tuple. This is the original tuple at the
next cursor, not a second state or a recursive run. -/
def cursorSuccessorInput
    (hcursor : cursor < BootstrapObservedFollower.blockLength p block)
    (rewards : GridRewardTable p)
    (input : CursorInput p rate block C_star C_h cursor) :
    CursorInput p rate block C_star C_h (cursor + 1) :=
  ⟨(input.1.1, ((actualCursorResult hcursor rewards input).coordinator.next,
      fun i => ((actualCursorResult hcursor rewards input).followers i).next)),
    actualCursorResult_invariant hcursor rewards input⟩

/-- Every successor coordinate needed by the later decreasing cursor/fuel
recursion is measurable, with the entire original source retained. -/
theorem measurable_cursorSuccessorInput
    (hcursor : cursor < BootstrapObservedFollower.blockLength p block)
    (rewards : GridRewardTable p) :
    Measurable (cursorSuccessorInput (rate := rate) (C_star := C_star)
      (C_h := C_h) hcursor rewards) := by
  apply Measurable.subtype_mk
  apply measurable_comap_iff.mpr
  have hsource := measurable_fst.comp (measurable_cursorInputCoordinates
    (rate := rate) (block := block) (C_star := C_star) (C_h := C_h) (cursor := cursor))
  have hout := measurable_actualCursorOutputCode (rate := rate)
    (C_star := C_star) (C_h := C_h) hcursor rewards
  exact hsource.prodMk (measurable_snd.comp hout)

end Bandits.Support.ActualInitializationCursorMeasurability

end
