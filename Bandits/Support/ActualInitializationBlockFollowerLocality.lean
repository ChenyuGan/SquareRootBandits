/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ActualPostlaunchFollowerObservationLocality
public import Bandits.Support.ActualSourceCompleteSuffixObservation

import Lean.Elab.Tactic.Omega

/-!
# Own-history locality inside actual initialization blocks

The original initialization physical records are decoded at their genuine
cursor inputs.  Locality is then proved by following the accepted cursor fold
and the follower's own physical feedback.  The result is internal to one
initialization block and makes no whole-horizon or regret claim. Each side
retains its complete original source and reward grid; only the stated public
and own coordinates are equated. The actual cursor fold supplies chaining.
Its input invariant does not assert a common coordinator history or launch cut.

The boundary formulas below characterize the literal accepted map. For actual
fold outputs its application is at the completed cursor, as certified by
`ActualInitializationRun.blockFold_follower_complete`.

Mathematical evidence: `sources/zip4/manuscript/01_introduction.tex:20-28`,
`sources/zip4/manuscript/07_public_setup.tex:28-38,55-114`,
`sources/zip4/manuscript/appendix_b_communication.tex:94-131`,
`sources/zip4/manuscript/06_interruptions.tex:240-296`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:6-14`.
-/

@[expose] public section

noncomputable section

open scoped Classical

open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.BootstrapObservedFollower
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.BootstrapPhysicalInput
open Bandits.Support.PublicDiscreteDraws
open Bandits.Support.ActualInitializationPhysicalStep
open Bandits.Support.ActualInitializationRun
open Bandits.Support.ActualPostlaunchFollowerMeasurability
open Bandits.Support.ActualPostlaunchFollowerPreparationLocality
open Bandits.Support.ActualPostlaunchFollowerObservationLocality

namespace Bandits.Support.ActualInitializationBlockFollowerLocality

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ActiveFollowerDownAcceptance.RateInput

/-- Every actual initialization record is the follower's original cursor-local
code on that same source, time, incoming state, and physically derived own
feedback.  Readiness is recovered from the executed physical step. -/
theorem initialization_record_localCode {p : Parameters} {rate : RateInput p}
    {source : BootstrapPrivateRoundStreams.SourceInput p}
    {rewards : ActualInitializationPhysicalStep.GridRewardTable p}
    (r : ActualInitializationRun.PhysicalRoundRecord p rate source rewards)
    (i : Fin (p.m - 1)) :
    let b := r.block
    let c := r.time.val - BootstrapObservedFollower.blockStart p b
    let player := PublicDiscreteDraws.followerPlayer p.two_le_m i
    let y := r.result.feedback player
    ∃ hc : c < BootstrapObservedFollower.blockLength p b,
      ∃ hs : ActualInitializationRun.followerAtCursor p rate b c
          (r.followersBefore i),
        ActualPostlaunchFollowerMeasurability.localTime b c hc = r.time ∧
        ActualPostlaunchFollowerMeasurability.decodeLocalCode
          (rate := rate) source r.time i
          (ActualPostlaunchFollowerMeasurability.localCodeOnCursor
            (rate := rate) hc i
            (ActualPostlaunchFollowerMeasurability.localInputOfComponents
              (rate := rate) source (r.followersBefore i) hs y)) =
          some (r.result.followers i) := by
  dsimp only
  let b := r.block
  let c := r.time.val - BootstrapObservedFollower.blockStart p b
  let player := PublicDiscreteDraws.followerPlayer p.two_le_m i
  let y := r.result.feedback player
  have hready :=
    (ActualInitializationPhysicalStep.step_succeeds_iff_ready rate b r.time
      r.coordinatorBefore r.followersBefore source rewards).mp
      ⟨r.result, r.executed⟩
  have htimeBlock := hready.2.1
  have hstartle : BootstrapObservedFollower.blockStart p b ≤ r.time.val :=
    ((BootstrapDimensions.mem_calendarBlock_iff p b r.time).mp htimeBlock).1
  dsimp [BootstrapObservedFollower.blockStart] at hstartle
  have hc : c < BootstrapObservedFollower.blockLength p b := by
    have hinterval :=
      (BootstrapDimensions.mem_calendarBlock_iff p b r.time).mp htimeBlock
    dsimp [c, BootstrapObservedFollower.blockStart,
      BootstrapObservedFollower.blockStop, BootstrapObservedFollower.blockLength]
    omega
  have hs : ActualInitializationRun.followerAtCursor p rate b c
      (r.followersBefore i) := by
    have hreadyI := hready.2.2.2.2.2 i
    cases hf : r.followersBefore i with
    | bootstrap state =>
        simp only [ActualInitializationPhysicalStep.followerAtNextCursor, hf] at hreadyI
        simp only [ActualInitializationRun.followerAtCursor]
        dsimp [c, BootstrapObservedFollower.blockStart] at *
        omega
    | declared row activation configuration =>
        simp only [ActualInitializationPhysicalStep.followerAtNextCursor, hf] at hreadyI
        simp only [ActualInitializationRun.followerAtCursor]
        dsimp [c, BootstrapObservedFollower.blockStart] at *
        omega
  have hlocalTime :
      ActualPostlaunchFollowerMeasurability.localTime b c hc = r.time := by
    apply Fin.ext
    simp [ActualPostlaunchFollowerMeasurability.localTime,
      ActualInitializationRun.blockTime, c,
      BootstrapObservedFollower.blockStart]
    omega
  have hactual := Bandits.Support.ActualInitializationHorizon.physicalRoundRecord_actual r
  have hstep := hactual.1
  obtain ⟨prepared, hprepare⟩ :=
    (ActualInitializationPhysicalStep.prepare_eq_ok_iff_ready rate b r.time
      r.coordinatorBefore r.followersBefore source rewards).mpr hready
  have hobserved : ActualInitializationPhysicalStep.observePrepared prepared =
      .ok r.result := by
    have hstepB : ActualInitializationPhysicalStep.step rate b r.time
        r.coordinatorBefore r.followersBefore source rewards = .ok r.result := by
      simpa [b] using hstep
    simpa [ActualInitializationPhysicalStep.step, hprepare] using hstepB
  have hresultPrepared : r.result.prepared = prepared := by
    have hround : r.result =
        ⟨prepared,
          (ActualInitializationPhysicalStep.observeFollowers prepared).val,
          (ActualInitializationPhysicalStep.observeFollowers prepared).property⟩ := by
      simpa [ActualInitializationPhysicalStep.observePrepared] using hobserved.symm
    rw [hround]
  have hreadyI := hready.2.2.2.2.2 i
  have hprepFollower : r.result.prepared.followers i =
      ActualInitializationPhysicalStep.prepareFollowerValid rate b r.time source i
        (r.followersBefore i) hreadyI := by
    rw [hresultPrepared]
    have h := hprepare
    simp [ActualInitializationPhysicalStep.prepare, hready] at h
    cases h
    rfl
  have hlocalOutcome :
      ActualInitializationPhysicalStep.observeFollower rate b r.time source i
          (ActualInitializationPhysicalStep.prepareFollowerValid rate b r.time source i
            (r.followersBefore i) hreadyI) y = .ok
        (ActualPostlaunchFollowerMeasurability.localOutcomeOnCursor
          (rate := rate) hc i source (r.followersBefore i) hs y) := by
    simpa [hlocalTime, ActualPostlaunchFollowerMeasurability.localOutcomeOnCursor,
      ActualPostlaunchFollowerMeasurability.localInputOfComponents] using
      ActualPostlaunchFollowerMeasurability.observeFollower_eq_localOutcomeOnCursor
        (rate := rate) hc i source (r.followersBefore i) hs y
  have htransition := r.result.followerTransition i
  rw [r.result_time, hactual.2.1, hprepFollower,
    ← hactual.2.2.2.2] at htransition
  have houtcome : ActualPostlaunchFollowerMeasurability.localOutcomeOnCursor
      (rate := rate) hc i source (r.followersBefore i) hs y = r.result.followers i :=
    Except.ok.inj (hlocalOutcome.symm.trans htransition)
  refine ⟨hc, hs, hlocalTime, ?_⟩
  have hdecode := ActualPostlaunchFollowerMeasurability.decode_localCodeOnComponents
    (rate := rate) hc i source (r.followersBefore i) hs y
  have hdecode' :
      ActualPostlaunchFollowerMeasurability.decodeLocalCode (rate := rate) source
          (ActualPostlaunchFollowerMeasurability.localTime b c hc) i
          (ActualPostlaunchFollowerMeasurability.localCodeOnCursor
            (rate := rate) hc i
            (ActualPostlaunchFollowerMeasurability.localInputOfComponents
              (rate := rate) source (r.followersBefore i) hs y)) =
        some (ActualPostlaunchFollowerMeasurability.localOutcomeOnCursor
          (rate := rate) hc i source (r.followersBefore i) hs y) := by
    simpa [ActualPostlaunchFollowerMeasurability.localOutcomeOnCursor] using hdecode
  have htimeDecode := congrArg
      (fun time => ActualPostlaunchFollowerMeasurability.decodeLocalCode
        (rate := rate) source time i
        (ActualPostlaunchFollowerMeasurability.localCodeOnCursor
          (rate := rate) hc i
          (ActualPostlaunchFollowerMeasurability.localInputOfComponents
            (rate := rate) source (r.followersBefore i) hs y))) hlocalTime
  exact htimeDecode.symm.trans (hdecode'.trans (congrArg some houtcome))

private theorem record_localCode_projections {p : Parameters} {rate : RateInput p}
    {source : BootstrapPrivateRoundStreams.SourceInput p}
    {rewards : ActualInitializationPhysicalStep.GridRewardTable p}
    (r : ActualInitializationRun.PhysicalRoundRecord p rate source rewards)
    (i : Fin (p.m - 1)) :
    let b := r.block
    let c := r.time.val - BootstrapObservedFollower.blockStart p b
    let player := PublicDiscreteDraws.followerPlayer p.two_le_m i
    ∃ hc : c < BootstrapObservedFollower.blockLength p b,
      ∃ hs : ActualInitializationRun.followerAtCursor p rate b c
          (r.followersBefore i),
        ActualPostlaunchFollowerMeasurability.localTime b c hc = r.time ∧
        let code := ActualPostlaunchFollowerMeasurability.localCodeOnCursor
          (rate := rate) hc i
          (ActualPostlaunchFollowerMeasurability.localInputOfComponents
            (rate := rate) source (r.followersBefore i) hs
            (r.result.feedback player))
        (r.result.followers i).next =
            ActualInitializationRoundMeasurability.followerStateOfCode p rate b
              code.2.2 ∧
          r.result.actions player =
            ActualInitializationPreparationMeasurability.preparedFollowerCodeArm code.1 := by
  dsimp only
  obtain ⟨hc, hs, htime, hdecode⟩ := initialization_record_localCode r i
  let code := ActualPostlaunchFollowerMeasurability.localCodeOnCursor
    (rate := rate) hc i
    (ActualPostlaunchFollowerMeasurability.localInputOfComponents
      (rate := rate) source (r.followersBefore i) hs
      (r.result.feedback (PublicDiscreteDraws.followerPlayer p.two_le_m i)))
  change Option.map
      (fun prepared => (⟨prepared,
        ActualInitializationRoundMeasurability.followerStateOfCode p rate r.block
          code.2.2⟩ : ActualInitializationPhysicalStep.FollowerOutcome p rate r.block))
      (ActualInitializationPreparationMeasurability.decodePreparedFollowerCode
        (rate := rate) (block := r.block) i source r.time code.1) =
    some (r.result.followers i) at hdecode
  rcases Option.map_eq_some_iff.mp hdecode with
    ⟨prepared, hdecodePrepared, hfields⟩
  have hnext : (r.result.followers i).next =
      ActualInitializationRoundMeasurability.followerStateOfCode p rate r.block
        code.2.2 := by
    exact (congrArg ActualInitializationPhysicalStep.FollowerOutcome.next hfields).symm
  have hprepared : prepared = (r.result.followers i).prepared :=
    congrArg ActualInitializationPhysicalStep.FollowerOutcome.prepared hfields
  have hpreparedArm :
      ActualInitializationPreparationMeasurability.preparedFollowerCodeArm code.1 =
        prepared.arm := by
    cases hcode : code.1 with
    | inl fields =>
        rcases fields with ⟨state, arm⟩
        simp [ActualInitializationPreparationMeasurability.decodePreparedFollowerCode,
          hcode] at hdecodePrepared
        cases hdecodePrepared
        rfl
    | inr fields =>
        rcases fields with ⟨row, activation, arm, incoming⟩
        by_cases hvalid : activation.val ≤ r.time.val + 1
        · simp [ActualInitializationPreparationMeasurability.decodePreparedFollowerCode,
            hcode, hvalid] at hdecodePrepared
          cases hdecodePrepared
          rfl
        · simp [ActualInitializationPreparationMeasurability.decodePreparedFollowerCode,
            hcode, hvalid] at hdecodePrepared
  have harm := ActualInitializationPhysicalStep.roundResult_follower_arm_preserved
    r.result i
  have ha : r.result.actions (PublicDiscreteDraws.followerPlayer p.two_le_m i) =
      (r.result.prepared.followers i).arm :=
    ActualInitializationPhysicalStep.actionProfile_follower r.result.prepared i
  have hownArm : r.result.actions (PublicDiscreteDraws.followerPlayer p.two_le_m i) =
      (r.result.followers i).prepared.arm := ha.trans harm.symm
  refine ⟨hc, hs, htime, ?_⟩
  exact ⟨hnext,
    hownArm.trans (hpreparedArm.trans (congrArg
      ActualInitializationPhysicalStep.PreparedFollower.arm hprepared)).symm⟩

private theorem initialization_localCode_eq_of_own_coordinates
    {p : Parameters} {rate : RateInput p} {block : Fin (n_boot p)}
    {cursor : Nat} (hcursor : cursor < BootstrapObservedFollower.blockLength p block)
    (i : Fin (p.m - 1)) (source source' : BootstrapPrivateRoundStreams.SourceInput p)
    (follower follower' : ActualInitializationPhysicalStep.FollowerState p rate block)
    (hstate : ActualInitializationRun.followerAtCursor p rate block cursor follower)
    (hstate' : ActualInitializationRun.followerAtCursor p rate block cursor follower')
    (hfollowers : follower = follower') (hpublic : source.1 = source'.1)
    (hround : BootstrapPhysicalInput.playerRoundScalarAt p source.2
        (PublicDiscreteDraws.followerPlayer p.two_le_m i)
        (ActualPostlaunchFollowerMeasurability.localTime block cursor hcursor) =
      BootstrapPhysicalInput.playerRoundScalarAt p source'.2
        (PublicDiscreteDraws.followerPlayer p.two_le_m i)
        (ActualPostlaunchFollowerMeasurability.localTime block cursor hcursor))
    (y y' : Fin (D p + 1)) (hy : y = y') :
    ActualPostlaunchFollowerMeasurability.localCodeOnCursor
        (rate := rate) hcursor i
        (ActualPostlaunchFollowerMeasurability.localInputOfComponents
          (rate := rate) source follower hstate y) =
      ActualPostlaunchFollowerMeasurability.localCodeOnCursor
        (rate := rate) hcursor i
        (ActualPostlaunchFollowerMeasurability.localInputOfComponents
          (rate := rate) source' follower' hstate' y') := by
  let x := ActualPostlaunchFollowerMeasurability.localInputOfComponents
    (rate := rate) source follower hstate y
  let x' := ActualPostlaunchFollowerMeasurability.localInputOfComponents
    (rate := rate) source' follower' hstate' y'
  have hf : ActualPostlaunchFollowerMeasurability.localFollower x =
      ActualPostlaunchFollowerMeasurability.localFollower x' := by
    simp [x, x', ActualPostlaunchFollowerMeasurability.localInputOfComponents,
      ActualPostlaunchFollowerMeasurability.localFollower, hfollowers]
  have hp : ActualPostlaunchFollowerPreparationLocality.preparationSourceCoordinates
      (rate := rate) hcursor i x =
      ActualPostlaunchFollowerPreparationLocality.preparationSourceCoordinates
        (rate := rate) hcursor i x' := by
    simp [ActualPostlaunchFollowerPreparationLocality.preparationSourceCoordinates,
      x, x', ActualPostlaunchFollowerMeasurability.localInputOfComponents,
      ActualPostlaunchFollowerMeasurability.localSource,
      ActualPostlaunchFollowerMeasurability.localFollower,
      ActualBootstrapObservationCode.sourcePrivate,
      ActualBootstrapObservationCode.sourceIDs,
      ActualBootstrapObservationCode.sourceRows,
      hpublic, hfollowers, hround]
  have ho : ActualPostlaunchFollowerObservationLocality.observationSourceCoordinates
      (rate := rate) hcursor i x =
      ActualPostlaunchFollowerObservationLocality.observationSourceCoordinates
        (rate := rate) hcursor i x' := by
    simp [ActualPostlaunchFollowerObservationLocality.observationSourceCoordinates,
      x, x', ActualPostlaunchFollowerMeasurability.localInputOfComponents,
      ActualPostlaunchFollowerMeasurability.localSource,
      ActualPostlaunchFollowerMeasurability.localFollower,
      ActualBootstrapObservationCode.sourceIDs,
      ActualBootstrapObservationCode.sourceRows,
      hpublic, hfollowers]
  exact ActualPostlaunchFollowerObservationLocality.localCodeOnCursor_eq_of_own_coordinates
    (rate := rate) hcursor i x x' hf hp ho (by simp [x, x',
      ActualPostlaunchFollowerMeasurability.localInputOfComponents,
      ActualPostlaunchFollowerMeasurability.localFeedback, hy])

/-- Preparation compares the original local input before its current feedback
is read. -/
private theorem initialization_preparedCode_eq_of_own_coordinates
    {p : Parameters} {rate : RateInput p} {block : Fin (n_boot p)}
    {cursor : Nat} (hcursor : cursor < BootstrapObservedFollower.blockLength p block)
    (i : Fin (p.m - 1)) (source source' : BootstrapPrivateRoundStreams.SourceInput p)
    (follower follower' : ActualInitializationPhysicalStep.FollowerState p rate block)
    (hstate : ActualInitializationRun.followerAtCursor p rate block cursor follower)
    (hstate' : ActualInitializationRun.followerAtCursor p rate block cursor follower')
    (hfollowers : follower = follower') (hpublic : source.1 = source'.1)
    (hround : BootstrapPhysicalInput.playerRoundScalarAt p source.2
        (PublicDiscreteDraws.followerPlayer p.two_le_m i)
        (ActualPostlaunchFollowerMeasurability.localTime block cursor hcursor) =
      BootstrapPhysicalInput.playerRoundScalarAt p source'.2
        (PublicDiscreteDraws.followerPlayer p.two_le_m i)
        (ActualPostlaunchFollowerMeasurability.localTime block cursor hcursor))
    (y y' : Fin (D p + 1)) :
    ActualPostlaunchFollowerMeasurability.preparedCodeOnCursor
        (rate := rate) hcursor i
        (ActualPostlaunchFollowerMeasurability.localInputOfComponents
          (rate := rate) source follower hstate y) =
      ActualPostlaunchFollowerMeasurability.preparedCodeOnCursor
        (rate := rate) hcursor i
        (ActualPostlaunchFollowerMeasurability.localInputOfComponents
          (rate := rate) source' follower' hstate' y') := by
  let x := ActualPostlaunchFollowerMeasurability.localInputOfComponents
    (rate := rate) source follower hstate y
  let x' := ActualPostlaunchFollowerMeasurability.localInputOfComponents
    (rate := rate) source' follower' hstate' y'
  have hf : ActualPostlaunchFollowerMeasurability.localFollower x =
      ActualPostlaunchFollowerMeasurability.localFollower x' := by
    simp [x, x', ActualPostlaunchFollowerMeasurability.localInputOfComponents,
      ActualPostlaunchFollowerMeasurability.localFollower, hfollowers]
  have hp : ActualPostlaunchFollowerPreparationLocality.preparationSourceCoordinates
      (rate := rate) hcursor i x =
      ActualPostlaunchFollowerPreparationLocality.preparationSourceCoordinates
        (rate := rate) hcursor i x' := by
    simp [ActualPostlaunchFollowerPreparationLocality.preparationSourceCoordinates,
      x, x', ActualPostlaunchFollowerMeasurability.localInputOfComponents,
      ActualPostlaunchFollowerMeasurability.localSource,
      ActualPostlaunchFollowerMeasurability.localFollower,
      ActualBootstrapObservationCode.sourcePrivate,
      ActualBootstrapObservationCode.sourceIDs,
      ActualBootstrapObservationCode.sourceRows,
      hpublic, hfollowers, hround]
  exact ActualPostlaunchFollowerPreparationLocality.preparedCodeOnCursor_eq_of_own_coordinates
    (rate := rate) hcursor i x x' hf hp

private theorem initialization_cursor_step_locality
    {p : Parameters} {rate : RateInput p} {block : Fin (n_boot p)}
    {C_star C_h : ℝ} {cursor : Nat}
    (hcursor : cursor < BootstrapObservedFollower.blockLength p block)
    (rewards rewards' : ActualInitializationPhysicalStep.GridRewardTable p)
    (x x' : ActualInitializationCursorMeasurability.CursorInput
      p rate block C_star C_h cursor) (i : Fin (p.m - 1))
    (hfollowers : x.1.2.2 i = x'.1.2.2 i)
    (hpublic : x.1.1.1 = x'.1.1.1)
    (hround : ∀ t : Fin p.T,
      BootstrapObservedFollower.blockStart p block + cursor ≤ t.val →
      t.val < BootstrapObservedFollower.blockStop p block →
      BootstrapPhysicalInput.playerRoundScalarAt p x.1.1.2
          (PublicDiscreteDraws.followerPlayer p.two_le_m i) t =
        BootstrapPhysicalInput.playerRoundScalarAt p x'.1.1.2
          (PublicDiscreteDraws.followerPlayer p.two_le_m i) t) :
    (ActualInitializationCursorMeasurability.actualCursorResult
        hcursor rewards x).actions (PublicDiscreteDraws.followerPlayer p.two_le_m i) =
      (ActualInitializationCursorMeasurability.actualCursorResult
        hcursor rewards' x').actions (PublicDiscreteDraws.followerPlayer p.two_le_m i) ∧
    ((ActualInitializationCursorMeasurability.actualCursorResult
        hcursor rewards x).feedback (PublicDiscreteDraws.followerPlayer p.two_le_m i) =
      (ActualInitializationCursorMeasurability.actualCursorResult
        hcursor rewards' x').feedback (PublicDiscreteDraws.followerPlayer p.two_le_m i) →
      ((ActualInitializationCursorMeasurability.cursorSuccessorInput
        hcursor rewards x).1.2.2 i) =
          ((ActualInitializationCursorMeasurability.cursorSuccessorInput
            hcursor rewards' x').1.2.2 i)) := by
  have hc := hcursor
  let leftRecord := ActualInitializationBlockFoldExact.cursorRecord hc rewards x
  let rightRecord := ActualInitializationBlockFoldExact.cursorRecord hc rewards' x'
  obtain ⟨hcLeft, hsLeft, htimeLeft, hleftFacts⟩ :=
    record_localCode_projections leftRecord i
  obtain ⟨hcRight, hsRight, htimeRight, hrightFacts⟩ :=
    record_localCode_projections rightRecord i
  have hrecordTime : leftRecord.time = rightRecord.time := rfl
  have hleftBlock : leftRecord.block = block := rfl
  have hrightBlock : rightRecord.block = block := rfl
  have hcRightAtLeft :
      leftRecord.time.val - BootstrapObservedFollower.blockStart p block <
        BootstrapObservedFollower.blockLength p block := by
    change (ActualInitializationRun.blockTime p block cursor hc).val -
        BootstrapObservedFollower.blockStart p block <
          BootstrapObservedFollower.blockLength p block
    simpa [rightRecord, ActualInitializationBlockFoldExact.cursorRecord] using hcRight
  have hsRightAtLeft :
      ActualInitializationRun.followerAtCursor p rate block
        (leftRecord.time.val - BootstrapObservedFollower.blockStart p block)
        (rightRecord.followersBefore i) := by
    change ActualInitializationRun.followerAtCursor p rate block
      ((ActualInitializationRun.blockTime p block cursor hc).val -
        BootstrapObservedFollower.blockStart p block) ((x'.1.2.2) i)
    simpa [rightRecord, ActualInitializationBlockFoldExact.cursorRecord] using hsRight
  let rightCodeOriginal := ActualPostlaunchFollowerMeasurability.localCodeOnCursor
    (rate := rate) hcRight i
    (ActualPostlaunchFollowerMeasurability.localInputOfComponents
      (rate := rate) x'.1.1 (rightRecord.followersBefore i) hsRight
      (rightRecord.result.feedback (PublicDiscreteDraws.followerPlayer p.two_le_m i)))
  have hrightFactsOriginal : (rightRecord.result.followers i).next =
      ActualInitializationRoundMeasurability.followerStateOfCode p rate block
        rightCodeOriginal.2.2 ∧
      rightRecord.result.actions (PublicDiscreteDraws.followerPlayer p.two_le_m i) =
        ActualInitializationPreparationMeasurability.preparedFollowerCodeArm rightCodeOriginal.1 := by
    simpa [rightCodeOriginal, rightRecord,
      ActualInitializationBlockFoldExact.cursorRecord] using hrightFacts
  have hcursorProof : hcLeft = hcRightAtLeft := Subsingleton.elim _ _
  subst hcRightAtLeft
  have htimeMem : leftRecord.time ∈ BootstrapDimensions.calendarBlock p block := by
    simpa [leftRecord, ActualInitializationBlockFoldExact.cursorRecord,
      ActualInitializationRun.blockTime] using
      ActualInitializationRun.blockTime_mem p block cursor hc
  have htimeLeftAtBlock :
      ActualPostlaunchFollowerMeasurability.localTime block
        (leftRecord.time.val - BootstrapObservedFollower.blockStart p block) hcLeft =
          leftRecord.time := by
    simpa [leftRecord, ActualInitializationBlockFoldExact.cursorRecord] using htimeLeft
  have htimeLower : BootstrapObservedFollower.blockStart p block + cursor ≤
      (ActualPostlaunchFollowerMeasurability.localTime block
        (leftRecord.time.val - BootstrapObservedFollower.blockStart p block) hcLeft).val := by
    rw [htimeLeftAtBlock]
    simp [leftRecord, ActualInitializationBlockFoldExact.cursorRecord,
      ActualInitializationRun.blockTime, BootstrapObservedFollower.blockStart]
  have htimeUpper :
      (ActualPostlaunchFollowerMeasurability.localTime block
        (leftRecord.time.val - BootstrapObservedFollower.blockStart p block) hcLeft).val <
        BootstrapObservedFollower.blockStop p block := by
    rw [htimeLeftAtBlock]
    have hinterval :=
      (BootstrapDimensions.mem_calendarBlock_iff p block leftRecord.time).mp htimeMem
    simpa [BootstrapObservedFollower.blockStop] using hinterval.2
  have hscalar := hround
    (ActualPostlaunchFollowerMeasurability.localTime block
      (leftRecord.time.val - BootstrapObservedFollower.blockStart p block) hcLeft)
    htimeLower htimeUpper
  have hstorage : leftRecord.followersBefore i = rightRecord.followersBefore i := by
    simpa [leftRecord, rightRecord, ActualInitializationBlockFoldExact.cursorRecord] using
      hfollowers
  let leftInput := ActualPostlaunchFollowerMeasurability.localInputOfComponents
    (rate := rate) x.1.1 (leftRecord.followersBefore i) hsLeft
    (leftRecord.result.feedback (PublicDiscreteDraws.followerPlayer p.two_le_m i))
  let rightInput := ActualPostlaunchFollowerMeasurability.localInputOfComponents
    (rate := rate) x'.1.1 (rightRecord.followersBefore i) hsRightAtLeft
    (rightRecord.result.feedback (PublicDiscreteDraws.followerPlayer p.two_le_m i))
  let leftCode := ActualPostlaunchFollowerMeasurability.localCodeOnCursor
    (rate := rate) hcLeft i leftInput
  let rightCode := ActualPostlaunchFollowerMeasurability.localCodeOnCursor
    (rate := rate) hcLeft i rightInput
  have hprepared := initialization_preparedCode_eq_of_own_coordinates
    (rate := rate) hcLeft i x.1.1 x'.1.1 (leftRecord.followersBefore i)
    (rightRecord.followersBefore i) hsLeft hsRightAtLeft hstorage hpublic hscalar
    (leftRecord.result.feedback (PublicDiscreteDraws.followerPlayer p.two_le_m i))
    (rightRecord.result.feedback (PublicDiscreteDraws.followerPlayer p.two_le_m i))
  have hpreparedArm :
      ActualInitializationPreparationMeasurability.preparedFollowerCodeArm leftCode.1 =
        ActualInitializationPreparationMeasurability.preparedFollowerCodeArm rightCode.1 := by
    exact congrArg ActualInitializationPreparationMeasurability.preparedFollowerCodeArm hprepared
  have hrightCodeEq : rightCodeOriginal = rightCode := by
    rfl
  let leftCodeAtBlock : ActualPostlaunchFollowerMeasurability.LocalCode
      (rate := rate) block := leftCode
  let rightCodeAtBlock : ActualPostlaunchFollowerMeasurability.LocalCode
      (rate := rate) block := rightCode
  have hleftFactsAtBlock : (leftRecord.result.followers i).next =
      ActualInitializationRoundMeasurability.followerStateOfCode p rate block leftCodeAtBlock.2.2 ∧
      leftRecord.result.actions (PublicDiscreteDraws.followerPlayer p.two_le_m i) =
        ActualInitializationPreparationMeasurability.preparedFollowerCodeArm leftCodeAtBlock.1 := by
    simpa [leftCodeAtBlock, leftCode, leftRecord,
      leftInput,
      ActualInitializationBlockFoldExact.cursorRecord] using hleftFacts
  have hleftNext : (leftRecord.result.followers i).next =
      ActualInitializationRoundMeasurability.followerStateOfCode p rate block leftCodeAtBlock.2.2 := by
    exact hleftFactsAtBlock.1
  have hrightNext : (rightRecord.result.followers i).next =
      ActualInitializationRoundMeasurability.followerStateOfCode p rate block rightCodeAtBlock.2.2 := by
    simpa [rightCodeAtBlock, rightCodeOriginal, rightCode, hrightCodeEq,
      rightInput,
      leftRecord, rightRecord, ActualInitializationBlockFoldExact.cursorRecord] using
      hrightFactsOriginal.1
  have hleftAction : leftRecord.result.actions
        (PublicDiscreteDraws.followerPlayer p.two_le_m i) =
      ActualInitializationPreparationMeasurability.preparedFollowerCodeArm leftCodeAtBlock.1 := by
    exact hleftFactsAtBlock.2
  have hrightAction : rightRecord.result.actions
        (PublicDiscreteDraws.followerPlayer p.two_le_m i) =
      ActualInitializationPreparationMeasurability.preparedFollowerCodeArm rightCodeAtBlock.1 := by
    simpa [rightCodeAtBlock, rightCodeOriginal, rightCode, hrightCodeEq,
      rightInput,
      leftRecord, rightRecord, ActualInitializationBlockFoldExact.cursorRecord] using
      hrightFactsOriginal.2
  have hmiddleAction :
      ActualInitializationPreparationMeasurability.preparedFollowerCodeArm leftCodeAtBlock.1 =
        ActualInitializationPreparationMeasurability.preparedFollowerCodeArm rightCodeAtBlock.1 := by
    exact hpreparedArm
  have hactions : leftRecord.result.actions (PublicDiscreteDraws.followerPlayer p.two_le_m i) =
      rightRecord.result.actions (PublicDiscreteDraws.followerPlayer p.two_le_m i) :=
    hleftAction.trans (hmiddleAction.trans hrightAction.symm)
  constructor
  · simpa [leftRecord, rightRecord, ActualInitializationBlockFoldExact.cursorRecord] using hactions
  · intro hfeedback
    have hfeedbackRecord : leftRecord.result.feedback
          (PublicDiscreteDraws.followerPlayer p.two_le_m i) =
        rightRecord.result.feedback (PublicDiscreteDraws.followerPlayer p.two_le_m i) := by
      simpa [leftRecord, rightRecord, ActualInitializationBlockFoldExact.cursorRecord] using
        hfeedback
    have hcode := initialization_localCode_eq_of_own_coordinates (rate := rate) hcLeft i
      x.1.1 x'.1.1 (leftRecord.followersBefore i) (rightRecord.followersBefore i)
      hsLeft hsRightAtLeft hstorage hpublic hscalar
      (leftRecord.result.feedback (PublicDiscreteDraws.followerPlayer p.two_le_m i))
      (rightRecord.result.feedback (PublicDiscreteDraws.followerPlayer p.two_le_m i))
      hfeedbackRecord
    have hcodeAtBlock : leftCodeAtBlock = rightCodeAtBlock := by
      simpa [leftCodeAtBlock, rightCodeAtBlock, leftCode, rightCode,
        leftInput, rightInput, leftRecord, rightRecord,
        ActualInitializationBlockFoldExact.cursorRecord] using hcode
    have hmiddleNext :
        ActualInitializationRoundMeasurability.followerStateOfCode p rate block leftCodeAtBlock.2.2 =
          ActualInitializationRoundMeasurability.followerStateOfCode p rate block rightCodeAtBlock.2.2 := by
      rw [hcodeAtBlock]
    have hnext : (leftRecord.result.followers i).next = (rightRecord.result.followers i).next :=
      hleftNext.trans (hmiddleNext.trans hrightNext.symm)
    simpa [ActualInitializationCursorMeasurability.cursorSuccessorInput,
      leftRecord, rightRecord, ActualInitializationBlockFoldExact.cursorRecord] using hnext

/-- The accepted initialization cursor fold preserves one follower's whole
post-round storage and actual own-action history from own coordinates and own
feedback alone. -/
theorem foldBlockAux_follower_locality {p : Parameters} {rate : RateInput p}
    {block : Fin (n_boot p)} {C_star C_h : ℝ} {cursor fuel : ℕ}
    (hbudget : cursor + fuel = BootstrapObservedFollower.blockLength p block)
    (x x' : ActualInitializationCursorMeasurability.CursorInput
      p rate block C_star C_h cursor)
    (rewards rewards' : ActualInitializationPhysicalStep.GridRewardTable p)
    (i : Fin (p.m - 1))
    (hstorage : x.1.2.2 i = x'.1.2.2 i)
    (hpublic : x.1.1.1 = x'.1.1.1)
    (hround : ∀ t : Fin p.T,
      BootstrapObservedFollower.blockStart p block + cursor ≤ t.val →
      t.val < BootstrapObservedFollower.blockStop p block →
      BootstrapPhysicalInput.playerRoundScalarAt p x.1.1.2
          (PublicDiscreteDraws.followerPlayer p.two_le_m i) t =
        BootstrapPhysicalInput.playerRoundScalarAt p x'.1.1.2
          (PublicDiscreteDraws.followerPlayer p.two_le_m i) t)
    (hfeedback :
      (ActualInitializationRun.foldBlockAux p rate block x.1.1 rewards C_star C_h
        cursor fuel hbudget x.1.2.1 x.1.2.2 x.2).records.map
          (fun r => r.result.feedback
            (PublicDiscreteDraws.followerPlayer p.two_le_m i)) =
      (ActualInitializationRun.foldBlockAux p rate block x'.1.1 rewards' C_star C_h
        cursor fuel hbudget x'.1.2.1 x'.1.2.2 x'.2).records.map
          (fun r => r.result.feedback
            (PublicDiscreteDraws.followerPlayer p.two_le_m i))) :
    let V := ActualInitializationRun.foldBlockAux p rate block x.1.1 rewards C_star C_h
      cursor fuel hbudget x.1.2.1 x.1.2.2 x.2
    let V' := ActualInitializationRun.foldBlockAux p rate block x'.1.1 rewards' C_star C_h
      cursor fuel hbudget x'.1.2.1 x'.1.2.2 x'.2
    V.followers i = V'.followers i ∧
      V.records.map (fun r => r.result.actions
        (PublicDiscreteDraws.followerPlayer p.two_le_m i)) =
      V'.records.map (fun r => r.result.actions
        (PublicDiscreteDraws.followerPlayer p.two_le_m i)) := by
  let player : Fin p.m := PublicDiscreteDraws.followerPlayer p.two_le_m i
  change (ActualInitializationRun.foldBlockAux p rate block x.1.1 rewards C_star C_h
        cursor fuel hbudget x.1.2.1 x.1.2.2 x.2).records.map
          (fun r => r.result.feedback
            (PublicDiscreteDraws.followerPlayer p.two_le_m i)) =
      (ActualInitializationRun.foldBlockAux p rate block x'.1.1 rewards' C_star C_h
        cursor fuel hbudget x'.1.2.1 x'.1.2.2 x'.2).records.map
          (fun r => r.result.feedback
            (PublicDiscreteDraws.followerPlayer p.two_le_m i)) at hfeedback
  change (ActualInitializationRun.foldBlockAux p rate block x.1.1 rewards C_star C_h
      cursor fuel hbudget x.1.2.1 x.1.2.2 x.2).records.map
        (fun r => r.result.feedback player) =
    (ActualInitializationRun.foldBlockAux p rate block x'.1.1 rewards' C_star C_h
      cursor fuel hbudget x'.1.2.1 x'.1.2.2 x'.2).records.map
        (fun r => r.result.feedback player) at hfeedback
  change
    (let V := ActualInitializationRun.foldBlockAux p rate block x.1.1 rewards C_star C_h
      cursor fuel hbudget x.1.2.1 x.1.2.2 x.2
     let V' := ActualInitializationRun.foldBlockAux p rate block x'.1.1 rewards' C_star C_h
      cursor fuel hbudget x'.1.2.1 x'.1.2.2 x'.2
     V.followers i = V'.followers i ∧
       V.records.map (fun r => r.result.actions player) =
         V'.records.map (fun r => r.result.actions player))
  induction fuel generalizing cursor with
  | zero =>
      have hd := ActualInitializationBlockFoldExact.foldBlockAux_zero_data
        hbudget rewards x
      have hd' := ActualInitializationBlockFoldExact.foldBlockAux_zero_data
        hbudget rewards' x'
      have hf := congrArg (fun data => data.2.1) hd
      have hf' := congrArg (fun data => data.2.1) hd'
      have hr := congrArg (fun data => data.2.2) hd
      have hr' := congrArg (fun data => data.2.2) hd'
      dsimp only at hf hf' hr hr'
      dsimp only
      rw [hf, hf']
      constructor
      · exact hstorage
      · simp [hr, hr']
  | succ fuel ih =>
      have hc : cursor < BootstrapObservedFollower.blockLength p block := by omega
      have hd := ActualInitializationBlockFoldExact.foldBlockAux_succ_data
        hbudget hc rewards x
      have hd' := ActualInitializationBlockFoldExact.foldBlockAux_succ_data
        hbudget hc rewards' x'
      have hf := congrArg (fun data => data.2.1) hd
      have hf' := congrArg (fun data => data.2.1) hd'
      have hr := congrArg (fun data => data.2.2) hd
      have hr' := congrArg (fun data => data.2.2) hd'
      dsimp only at hf hf' hr hr'
      let next := ActualInitializationCursorMeasurability.cursorSuccessorInput hc rewards x
      let next' := ActualInitializationCursorMeasurability.cursorSuccessorInput hc rewards' x'
      have hfeedbackCons := hfeedback
      rw [hr, hr'] at hfeedbackCons
      have hfeedbackPair := List.cons.inj hfeedbackCons
      have hheadFeedback := hfeedbackPair.1
      have htailFeedback := hfeedbackPair.2
      have hstep := initialization_cursor_step_locality hc
        rewards rewards' x x' i hstorage hpublic hround
      have htailStorage := hstep.2 hheadFeedback
      have hroundNext : ∀ t : Fin p.T,
          BootstrapObservedFollower.blockStart p block + (cursor + 1) ≤ t.val →
          t.val < BootstrapObservedFollower.blockStop p block →
          BootstrapPhysicalInput.playerRoundScalarAt p next.1.1.2
              (PublicDiscreteDraws.followerPlayer p.two_le_m i) t =
            BootstrapPhysicalInput.playerRoundScalarAt p next'.1.1.2
              (PublicDiscreteDraws.followerPlayer p.two_le_m i) t := by
        intro t hlow hhigh
        exact hround t (by omega) hhigh
      have hpublicNext : next.1.1.1 = next'.1.1.1 := by
        simpa [next, next',
          ActualInitializationCursorMeasurability.cursorSuccessorInput] using hpublic
      have htail := by
        apply ih (hbudget := by omega) (x := next) (x' := next')
          (hstorage := htailStorage) (hpublic := hpublicNext) (hround := hroundNext)
        simpa [next, next', player,
          ActualInitializationCursorMeasurability.cursorSuccessorInput] using htailFeedback
      dsimp only
      rw [hf, hf', hr, hr']
      constructor
      · exact htail.1
      · exact congrArg₂ List.cons hstep.1 htail.2

/-- Every remaining actual calendar position contributes exactly one record. -/
theorem foldBlockAux_records_length
    {p : Parameters} {rate : RateInput p} {block : Fin (n_boot p)}
    {C_star C_h : ℝ} {cursor fuel : ℕ}
    (hbudget : cursor + fuel = BootstrapObservedFollower.blockLength p block)
    (x : ActualInitializationCursorMeasurability.CursorInput
      p rate block C_star C_h cursor)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) :
    (ActualInitializationRun.foldBlockAux p rate block x.1.1 rewards C_star C_h
      cursor fuel hbudget x.1.2.1 x.1.2.2 x.2).records.length = fuel := by
  have h := (ActualInitializationRun.foldBlockAux p rate block x.1.1 rewards C_star C_h
    cursor fuel hbudget x.1.2.1 x.1.2.2 x.2).record_count
  rw [(ActualInitializationRun.foldBlockAux p rate block x.1.1 rewards C_star C_h
    cursor fuel hbudget x.1.2.1 x.1.2.2 x.2).consumed_eq_blockLength] at h
  omega

/-- The literal zero-cursor input from the original source and block carry. -/
def beginBlockCursorInput {p : Parameters} {rate : RateInput p}
    {block : Fin (n_boot p)} {source : BootstrapPrivateRoundStreams.SourceInput p}
    {C_star C_h : ℝ} (carry : ActualInitializationRun.BlockCarry p rate block)
    (hCstar : carry.C_star = C_star) (hCh : carry.C_h = C_h) :
    ActualInitializationCursorMeasurability.CursorInput p rate block C_star C_h 0 := by
  let started := ActualInitializationRun.beginBlock p rate block source carry
  exact ⟨(source, (.prelaunch started.coordinator, started.followers)),
    by simpa [hCstar, hCh] using started.invariant⟩

/-- At cursor zero the exact accepted block fold starts from each original
source and carried state. Equal own carry storage and original own block
coordinates produce equal incoming own storage; equal own round scalars and
own feedback histories then determine the final storage and actual own-arm
record list. The boundary maps remain the literal active, inactive, pending,
ordinary, and dagger transitions. -/
private theorem foldBlockCursor_follower_locality {p : Parameters} {rate : RateInput p}
    {block : Fin (n_boot p)}
    (source source' : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards rewards' : ActualInitializationPhysicalStep.GridRewardTable p)
    (carry carry' : ActualInitializationRun.BlockCarry p rate block)
    (i : Fin (p.m - 1))
    (hCstar : carry.C_star = carry'.C_star)
    (hCh : carry.C_h = carry'.C_h)
    (hcarry : carry.followers i = carry'.followers i)
    (hpublic : source.1 = source'.1)
    (hblock : source.2.1.1 block i = source'.2.1.1 block i)
    (hround : ∀ t : Fin p.T,
      BootstrapObservedFollower.blockStart p block ≤ t.val →
      t.val < BootstrapObservedFollower.blockStop p block →
      BootstrapPhysicalInput.playerRoundScalarAt p source.2
          (PublicDiscreteDraws.followerPlayer p.two_le_m i) t =
        BootstrapPhysicalInput.playerRoundScalarAt p source'.2
          (PublicDiscreteDraws.followerPlayer p.two_le_m i) t)
    (hfeedback :
      let x := beginBlockCursorInput (source := source) carry rfl rfl
      let x' := beginBlockCursorInput (source := source') carry' hCstar.symm hCh.symm
      (ActualInitializationRun.foldBlockAux p rate block x.1.1 rewards carry.C_star carry.C_h
        0 (BootstrapObservedFollower.blockLength p block) (by omega)
        x.1.2.1 x.1.2.2 x.2).records.map
          (fun r => r.result.feedback (PublicDiscreteDraws.followerPlayer p.two_le_m i)) =
      (ActualInitializationRun.foldBlockAux p rate block x'.1.1 rewards' carry.C_star carry.C_h
        0 (BootstrapObservedFollower.blockLength p block) (by omega)
        x'.1.2.1 x'.1.2.2 x'.2).records.map
          (fun r => r.result.feedback (PublicDiscreteDraws.followerPlayer p.two_le_m i))) :
    let x := beginBlockCursorInput (source := source) carry rfl rfl
    let x' := beginBlockCursorInput (source := source') carry' hCstar.symm hCh.symm
    let V := ActualInitializationRun.foldBlockAux p rate block x.1.1 rewards carry.C_star carry.C_h
      0 (BootstrapObservedFollower.blockLength p block) (by omega)
      x.1.2.1 x.1.2.2 x.2
    let V' := ActualInitializationRun.foldBlockAux p rate block x'.1.1 rewards' carry.C_star carry.C_h
      0 (BootstrapObservedFollower.blockLength p block) (by omega)
      x'.1.2.1 x'.1.2.2 x'.2
    ActualInitializationRun.beginFollowerBlock p rate block source i (carry.followers i) =
        ActualInitializationRun.beginFollowerBlock p rate block source' i (carry'.followers i) ∧
      V.followers i = V'.followers i ∧
      V.records.map (fun r => r.result.actions
        (PublicDiscreteDraws.followerPlayer p.two_le_m i)) =
      V'.records.map (fun r => r.result.actions
        (PublicDiscreteDraws.followerPlayer p.two_le_m i)) ∧
      V.records.length = BootstrapObservedFollower.blockLength p block ∧
      ActualInitializationRun.boundaryOutputFromFollower p rate block (V.followers i) =
        ActualInitializationRun.boundaryOutputFromFollower p rate block (V'.followers i) ∧
      ActualInitializationRun.followerCarryAtBlockBoundary p rate block (V.followers i) =
        ActualInitializationRun.followerCarryAtBlockBoundary p rate block (V'.followers i) := by
  let started := ActualInitializationRun.beginBlock p rate block source carry
  let started' := ActualInitializationRun.beginBlock p rate block source' carry'
  let x := beginBlockCursorInput (source := source) carry rfl rfl
  let x' := beginBlockCursorInput (source := source') carry' hCstar.symm hCh.symm
  have hstart : started.followers i = started'.followers i := by
    change ActualInitializationRun.beginFollowerBlock p rate block source i (carry.followers i) =
      ActualInitializationRun.beginFollowerBlock p rate block source' i (carry'.followers i)
    rw [hcarry]
    cases h : carry'.followers i with
    | bootstrap numerators lowerBound =>
        simp [ActualInitializationRun.beginFollowerBlock, hblock]
    | declared row activation configuration =>
        simp [ActualInitializationRun.beginFollowerBlock]
  have hstartCore : x.1.2.2 i = x'.1.2.2 i := by
    simpa [x, x', beginBlockCursorInput, started, started'] using hstart
  have hpublicCore : x.1.1.1 = x'.1.1.1 := by
    change source.1 = source'.1
    exact hpublic
  have hroundCore : ∀ t : Fin p.T,
      BootstrapObservedFollower.blockStart p block ≤ t.val →
      t.val < BootstrapObservedFollower.blockStop p block →
      BootstrapPhysicalInput.playerRoundScalarAt p x.1.1.2
          (PublicDiscreteDraws.followerPlayer p.two_le_m i) t =
        BootstrapPhysicalInput.playerRoundScalarAt p x'.1.1.2
          (PublicDiscreteDraws.followerPlayer p.two_le_m i) t := by
    intro t hlow hhigh
    exact hround t hlow hhigh
  have hfeedbackCore :
      (ActualInitializationRun.foldBlockAux p rate block x.1.1 rewards carry.C_star carry.C_h
        0 (BootstrapObservedFollower.blockLength p block) (by omega)
        x.1.2.1 x.1.2.2 x.2).records.map
          (fun r => r.result.feedback (PublicDiscreteDraws.followerPlayer p.two_le_m i)) =
      (ActualInitializationRun.foldBlockAux p rate block x'.1.1 rewards' carry.C_star carry.C_h
        0 (BootstrapObservedFollower.blockLength p block) (by omega)
        x'.1.2.1 x'.1.2.2 x'.2).records.map
          (fun r => r.result.feedback (PublicDiscreteDraws.followerPlayer p.two_le_m i)) := by
    simpa [x, x', beginBlockCursorInput, started, started'] using hfeedback
  have hlocal := foldBlockAux_follower_locality
    (cursor := 0) (fuel := BootstrapObservedFollower.blockLength p block)
    (hbudget := by omega) x x' rewards rewards' i hstartCore hpublicCore hroundCore
    hfeedbackCore
  have hrecordsLength := foldBlockAux_records_length
    (cursor := 0) (fuel := BootstrapObservedFollower.blockLength p block)
    (hbudget := by omega) x rewards
  have hboundary := congrArg
    (ActualInitializationRun.boundaryOutputFromFollower p rate block) hlocal.1
  have hcarryOut := congrArg
    (ActualInitializationRun.followerCarryAtBlockBoundary p rate block) hlocal.1
  refine ⟨hstart, hlocal.1, hlocal.2, hrecordsLength, hboundary, hcarryOut⟩

/-- Specialization to the actual `foldBlock` on each original source. Only
this follower's incoming carry, block triple, public output, remaining own
round scalars and actual own feedback are compared. -/
theorem foldBlock_follower_locality {p : Parameters} {rate : RateInput p}
    {block : Fin (n_boot p)}
    (source source' : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards rewards' : ActualInitializationPhysicalStep.GridRewardTable p)
    (carry carry' : ActualInitializationRun.BlockCarry p rate block)
    (i : Fin (p.m - 1))
    (hCstar : carry.C_star = carry'.C_star) (hCh : carry.C_h = carry'.C_h)
    (hcarry : carry.followers i = carry'.followers i)
    (hpublic : source.1 = source'.1)
    (hblock : source.2.1.1 block i = source'.2.1.1 block i)
    (hround : ∀ t : Fin p.T,
      BootstrapObservedFollower.blockStart p block ≤ t.val →
      t.val < BootstrapObservedFollower.blockStop p block →
      BootstrapPhysicalInput.playerRoundScalarAt p source.2
          (PublicDiscreteDraws.followerPlayer p.two_le_m i) t =
        BootstrapPhysicalInput.playerRoundScalarAt p source'.2
          (PublicDiscreteDraws.followerPlayer p.two_le_m i) t)
    (hfeedback :
      (ActualInitializationRun.foldBlock p rate block source rewards carry).records.map
          (fun r => r.result.feedback (PublicDiscreteDraws.followerPlayer p.two_le_m i)) =
      (ActualInitializationRun.foldBlock p rate block source' rewards' carry').records.map
          (fun r => r.result.feedback (PublicDiscreteDraws.followerPlayer p.two_le_m i))) :
    let V := ActualInitializationRun.foldBlock p rate block source rewards carry
    let V' := ActualInitializationRun.foldBlock p rate block source' rewards' carry'
    ActualInitializationRun.beginFollowerBlock p rate block source i (carry.followers i) =
        ActualInitializationRun.beginFollowerBlock p rate block source' i (carry'.followers i) ∧
      V.followers i = V'.followers i ∧
      V.records.map (fun r => r.result.actions
        (PublicDiscreteDraws.followerPlayer p.two_le_m i)) =
      V'.records.map (fun r => r.result.actions
        (PublicDiscreteDraws.followerPlayer p.two_le_m i)) ∧
      V.records.length = BootstrapObservedFollower.blockLength p block ∧
      ActualInitializationRun.boundaryOutputFromFollower p rate block (V.followers i) =
        ActualInitializationRun.boundaryOutputFromFollower p rate block (V'.followers i) ∧
      ActualInitializationRun.followerCarryAtBlockBoundary p rate block (V.followers i) =
        ActualInitializationRun.followerCarryAtBlockBoundary p rate block (V'.followers i) := by
  let input : ActualInitializationBlockMeasurability.BlockInput
      p rate block carry.C_star carry.C_h := ⟨source, carry, rfl, rfl⟩
  let input' : ActualInitializationBlockMeasurability.BlockInput
      p rate block carry.C_star carry.C_h := ⟨source', carry', hCstar.symm, hCh.symm⟩
  have hd := ActualInitializationBlockFoldExact.foldBlock_zero_input_data rewards input
  have hd' := ActualInitializationBlockFoldExact.foldBlock_zero_input_data rewards' input'
  have hf := congrArg (fun data => data.2.1) hd
  have hf' := congrArg (fun data => data.2.1) hd'
  have hr := congrArg (fun data => data.2.2) hd
  have hr' := congrArg (fun data => data.2.2) hd'
  dsimp only [input, input'] at hf hf' hr hr'
  have hlocal := foldBlockCursor_follower_locality source source' rewards rewards'
    carry carry' i hCstar hCh hcarry hpublic hblock hround
    (by simpa only [hr, hr', beginBlockCursorInput,
      ActualInitializationBlockFoldMeasurability.actualCursorZeroInput] using hfeedback)
  dsimp only
  rw [hf, hf', hr, hr']
  simpa only [beginBlockCursorInput,
    ActualInitializationBlockFoldMeasurability.actualCursorZeroInput] using hlocal

/-- The genuine first block uses `initialCarry` and its own source triple.
All-one means that the accepted initial numerators have weight one in every
arm; their integer entries are not replaced by literal ones. -/
theorem foldInitialBlock_follower_locality {p : Parameters} {rate : RateInput p}
    {C_star C_h : ℝ}
    (source source' : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards rewards' : ActualInitializationPhysicalStep.GridRewardTable p)
    (i : Fin (p.m - 1))
    (hpublic : source.1 = source'.1)
    (hblock : source.2.1.1 (ActualInitializationRun.firstBlock p) i =
      source'.2.1.1 (ActualInitializationRun.firstBlock p) i)
    (hround : ∀ t : Fin p.T,
      BootstrapObservedFollower.blockStart p (ActualInitializationRun.firstBlock p) ≤ t.val →
      t.val < BootstrapObservedFollower.blockStop p (ActualInitializationRun.firstBlock p) →
      BootstrapPhysicalInput.playerRoundScalarAt p source.2
          (PublicDiscreteDraws.followerPlayer p.two_le_m i) t =
        BootstrapPhysicalInput.playerRoundScalarAt p source'.2
          (PublicDiscreteDraws.followerPlayer p.two_le_m i) t)
    (hfeedback :
      (ActualInitializationRun.foldInitialBlock p rate source rewards C_star C_h).records.map
        (fun r => r.result.feedback (PublicDiscreteDraws.followerPlayer p.two_le_m i)) =
      (ActualInitializationRun.foldInitialBlock p rate source' rewards' C_star C_h).records.map
        (fun r => r.result.feedback (PublicDiscreteDraws.followerPlayer p.two_le_m i))) :
    (∀ a : Fin p.K,
      BootstrapWeightPotential.weight (b_N p)
        (BootstrapObservedFollower.initialNumerators p) a = 1) ∧
    let V := ActualInitializationRun.foldInitialBlock p rate source rewards C_star C_h
    let V' := ActualInitializationRun.foldInitialBlock p rate source' rewards' C_star C_h
    ActualInitializationRun.beginFollowerBlock p rate (ActualInitializationRun.firstBlock p)
        source i ((ActualInitializationRun.initialCarry p rate C_star C_h).followers i) =
      ActualInitializationRun.beginFollowerBlock p rate (ActualInitializationRun.firstBlock p)
        source' i ((ActualInitializationRun.initialCarry p rate C_star C_h).followers i) ∧
      V.followers i = V'.followers i ∧
      V.records.map (fun r => r.result.actions
        (PublicDiscreteDraws.followerPlayer p.two_le_m i)) =
      V'.records.map (fun r => r.result.actions
        (PublicDiscreteDraws.followerPlayer p.two_le_m i)) ∧
      V.records.length = BootstrapObservedFollower.blockLength p (ActualInitializationRun.firstBlock p) ∧
      ActualInitializationRun.boundaryOutputFromFollower p rate (ActualInitializationRun.firstBlock p)
          (V.followers i) =
        ActualInitializationRun.boundaryOutputFromFollower p rate (ActualInitializationRun.firstBlock p)
          (V'.followers i) ∧
      ActualInitializationRun.followerCarryAtBlockBoundary p rate
          (ActualInitializationRun.firstBlock p) (V.followers i) =
        ActualInitializationRun.followerCarryAtBlockBoundary p rate
          (ActualInitializationRun.firstBlock p) (V'.followers i) := by
  have hlocal := foldBlock_follower_locality
    (source := source) (source' := source') (rewards := rewards) (rewards' := rewards')
    (carry := ActualInitializationRun.initialCarry p rate C_star C_h)
    (carry' := ActualInitializationRun.initialCarry p rate C_star C_h)
    (i := i) rfl rfl rfl hpublic hblock hround hfeedback
  have hweight : ∀ a : Fin p.K,
      BootstrapWeightPotential.weight (b_N p)
        (BootstrapObservedFollower.initialNumerators p) a = 1 := by
    intro a
    exact BootstrapObservedFollower.initialNumerators_weight_eq_one p a
  constructor
  · exact hweight
  · simpa [ActualInitializationRun.foldInitialBlock, ActualInitializationRun.foldBlock,
      ActualInitializationRun.initialCarry, beginBlockCursorInput] using hlocal

/-- Transport a physical record's incoming follower storage to the accepted
block index using the exact block-membership theorem for the actual fold. -/
def transportedIncomingFollower {p : Parameters} {rate : RateInput p}
    {block : Fin (n_boot p)} {source : BootstrapPrivateRoundStreams.SourceInput p}
    {rewards : ActualInitializationPhysicalStep.GridRewardTable p}
    (record : ActualInitializationRun.PhysicalRoundRecord p rate source rewards)
    (hblock : record.block = block) (i : Fin (p.m - 1)) :
    ActualInitializationPhysicalStep.FollowerState p rate block :=
  Eq.mp (congrArg (ActualInitializationPhysicalStep.FollowerState p rate) hblock)
    (record.followersBefore i)

/-- Strict-past locality at a physical record: an explicit prefix of length
`n` precedes records with equal incoming own storage and action. Thus those
records are precisely the zero-based nth records. The current record's
feedback is not compared. -/
theorem foldBlockAux_strict_past_follower_locality
    {p : Parameters} {rate : RateInput p} {block : Fin (n_boot p)}
    {C_star C_h : ℝ} {cursor fuel n : ℕ}
    (hbudget : cursor + fuel = BootstrapObservedFollower.blockLength p block)
    (x x' : ActualInitializationCursorMeasurability.CursorInput
      p rate block C_star C_h cursor)
    (rewards rewards' : ActualInitializationPhysicalStep.GridRewardTable p)
    (i : Fin (p.m - 1)) (hn : n < fuel)
    (hstorage : x.1.2.2 i = x'.1.2.2 i)
    (hpublic : x.1.1.1 = x'.1.1.1)
    (hround : ∀ t : Fin p.T,
      BootstrapObservedFollower.blockStart p block + cursor ≤ t.val →
      t.val < BootstrapObservedFollower.blockStop p block →
      BootstrapPhysicalInput.playerRoundScalarAt p x.1.1.2
          (PublicDiscreteDraws.followerPlayer p.two_le_m i) t =
        BootstrapPhysicalInput.playerRoundScalarAt p x'.1.1.2
          (PublicDiscreteDraws.followerPlayer p.two_le_m i) t)
    (hfeedback :
      ((ActualInitializationRun.foldBlockAux p rate block x.1.1 rewards C_star C_h
          cursor fuel hbudget x.1.2.1 x.1.2.2 x.2).records.map
          (fun r => r.result.feedback (PublicDiscreteDraws.followerPlayer p.two_le_m i))).take n =
      ((ActualInitializationRun.foldBlockAux p rate block x'.1.1 rewards' C_star C_h
          cursor fuel hbudget x'.1.2.1 x'.1.2.2 x'.2).records.map
          (fun r => r.result.feedback (PublicDiscreteDraws.followerPlayer p.two_le_m i))).take n) :
    let V := ActualInitializationRun.foldBlockAux p rate block x.1.1 rewards C_star C_h
      cursor fuel hbudget x.1.2.1 x.1.2.2 x.2
    let V' := ActualInitializationRun.foldBlockAux p rate block x'.1.1 rewards' C_star C_h
      cursor fuel hbudget x'.1.2.1 x'.1.2.2 x'.2
    ∃ (pre post : List (ActualInitializationRun.PhysicalRoundRecord p rate x.1.1 rewards))
      (pre' post' : List (ActualInitializationRun.PhysicalRoundRecord p rate x'.1.1 rewards'))
      (r : ActualInitializationRun.PhysicalRoundRecord p rate x.1.1 rewards)
      (r' : ActualInitializationRun.PhysicalRoundRecord p rate x'.1.1 rewards'),
      V.records = pre ++ r :: post ∧ V'.records = pre' ++ r' :: post' ∧
      pre.length = n ∧ pre'.length = n ∧
      V.records.length = fuel ∧ V'.records.length = fuel ∧
      (∃ hb : r.block = block, ∃ hb' : r'.block = block,
        transportedIncomingFollower r hb i = transportedIncomingFollower r' hb' i ∧
          r.result.actions (PublicDiscreteDraws.followerPlayer p.two_le_m i) =
            r'.result.actions (PublicDiscreteDraws.followerPlayer p.two_le_m i)) := by
  let player : Fin p.m := PublicDiscreteDraws.followerPlayer p.two_le_m i
  change ((ActualInitializationRun.foldBlockAux p rate block x.1.1 rewards C_star C_h
      cursor fuel hbudget x.1.2.1 x.1.2.2 x.2).records.map
      (fun r => r.result.feedback player)).take n =
    ((ActualInitializationRun.foldBlockAux p rate block x'.1.1 rewards' C_star C_h
      cursor fuel hbudget x'.1.2.1 x'.1.2.2 x'.2).records.map
      (fun r => r.result.feedback player)).take n at hfeedback
  induction n generalizing cursor fuel with
  | zero =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          have hlength := foldBlockAux_records_length hbudget x rewards
          have hlength' := foldBlockAux_records_length hbudget x' rewards'
          have hc : cursor < BootstrapObservedFollower.blockLength p block := by omega
          have hd := ActualInitializationBlockFoldExact.foldBlockAux_succ_data
            hbudget hc rewards x
          have hd' := ActualInitializationBlockFoldExact.foldBlockAux_succ_data
            hbudget hc rewards' x'
          have hr := congrArg (fun data => data.2.2) hd
          have hr' := congrArg (fun data => data.2.2) hd'
          dsimp only at hr hr'
          dsimp only [ActualInitializationCursorMeasurability.cursorSuccessorInput] at hr hr'
          have hstep := initialization_cursor_step_locality hc
            rewards rewards' x x' i hstorage hpublic hround
          refine ⟨[], (ActualInitializationRun.foldBlockAux p rate block
            (ActualInitializationCursorMeasurability.cursorSuccessorInput hc rewards x).1.1
              rewards C_star C_h (cursor + 1) fuel (by omega)
              (ActualInitializationCursorMeasurability.cursorSuccessorInput hc rewards x).1.2.1
              (ActualInitializationCursorMeasurability.cursorSuccessorInput hc rewards x).1.2.2
              (ActualInitializationCursorMeasurability.cursorSuccessorInput hc rewards x).2).records,
            [], (ActualInitializationRun.foldBlockAux p rate block
            (ActualInitializationCursorMeasurability.cursorSuccessorInput hc rewards' x').1.1
              rewards' C_star C_h (cursor + 1) fuel (by omega)
              (ActualInitializationCursorMeasurability.cursorSuccessorInput hc rewards' x').1.2.1
              (ActualInitializationCursorMeasurability.cursorSuccessorInput hc rewards' x').1.2.2
              (ActualInitializationCursorMeasurability.cursorSuccessorInput hc rewards' x').2).records,
            ActualInitializationBlockFoldExact.cursorRecord hc rewards x,
            ActualInitializationBlockFoldExact.cursorRecord hc rewards' x', ?_⟩
          refine ⟨hr, hr', rfl, rfl, ?_, ?_, ?_⟩
          · simpa using hlength
          · simpa using hlength'
          · have hmem : ActualInitializationBlockFoldExact.cursorRecord hc rewards x ∈
                (ActualInitializationRun.foldBlockAux p rate block x.1.1 rewards C_star C_h
                  cursor (fuel + 1) hbudget x.1.2.1 x.1.2.2 x.2).records := by
              rw [hr]
              simp
            have hmem' : ActualInitializationBlockFoldExact.cursorRecord hc rewards' x' ∈
                (ActualInitializationRun.foldBlockAux p rate block x'.1.1 rewards' C_star C_h
                  cursor (fuel + 1) hbudget x'.1.2.1 x'.1.2.2 x'.2).records := by
              rw [hr']
              simp
            have hb := ActualInitializationBlockFoldExact.foldBlockAux_records_block
              hbudget rewards x (ActualInitializationBlockFoldExact.cursorRecord hc rewards x)
              hmem
            have hb' := ActualInitializationBlockFoldExact.foldBlockAux_records_block
              hbudget rewards' x' (ActualInitializationBlockFoldExact.cursorRecord hc rewards' x')
              hmem'
            refine ⟨hb, ⟨hb', ?_⟩⟩
            refine ⟨?_, ?_⟩
            · cases hb
              cases hb'
              change x.1.2.2 i = x'.1.2.2 i
              exact hstorage
            · simpa [ActualInitializationBlockFoldExact.cursorRecord] using hstep.1
  | succ n ih =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          have hlength := foldBlockAux_records_length hbudget x rewards
          have hlength' := foldBlockAux_records_length hbudget x' rewards'
          have hc : cursor < BootstrapObservedFollower.blockLength p block := by omega
          have hd := ActualInitializationBlockFoldExact.foldBlockAux_succ_data
            hbudget hc rewards x
          have hd' := ActualInitializationBlockFoldExact.foldBlockAux_succ_data
            hbudget hc rewards' x'
          have hf := congrArg (fun data => data.2.1) hd
          have hf' := congrArg (fun data => data.2.1) hd'
          have hr := congrArg (fun data => data.2.2) hd
          have hr' := congrArg (fun data => data.2.2) hd'
          dsimp only at hf hf' hr hr'
          dsimp only [ActualInitializationCursorMeasurability.cursorSuccessorInput] at hr hr'
          let next := ActualInitializationCursorMeasurability.cursorSuccessorInput hc rewards x
          let next' := ActualInitializationCursorMeasurability.cursorSuccessorInput hc rewards' x'
          have hfeedbackCons := hfeedback
          rw [hr, hr'] at hfeedbackCons
          have hfeedbackPair := List.cons.inj hfeedbackCons
          have hstep := initialization_cursor_step_locality hc
            rewards rewards' x x' i hstorage hpublic hround
          have htailStorage := hstep.2 hfeedbackPair.1
          have hroundNext : ∀ t : Fin p.T,
              BootstrapObservedFollower.blockStart p block + (cursor + 1) ≤ t.val →
              t.val < BootstrapObservedFollower.blockStop p block →
              BootstrapPhysicalInput.playerRoundScalarAt p next.1.1.2
                  (PublicDiscreteDraws.followerPlayer p.two_le_m i) t =
                BootstrapPhysicalInput.playerRoundScalarAt p next'.1.1.2
                  (PublicDiscreteDraws.followerPlayer p.two_le_m i) t := by
            intro t hlow hhigh
            exact hround t (by omega) hhigh
          have hpublicNext : next.1.1.1 = next'.1.1.1 := by
            simpa [next, next',
              ActualInitializationCursorMeasurability.cursorSuccessorInput] using hpublic
          have htail := ih (hbudget := by omega) (x := next) (x' := next')
            (hn := by omega) (hstorage := htailStorage) (hpublic := hpublicNext)
            (hround := hroundNext) (hfeedback := hfeedbackPair.2)
          have htailNorm := by
            simpa only [next, next', ActualInitializationCursorMeasurability.cursorSuccessorInput]
              using htail
          rcases htailNorm with ⟨pre, post, pre', post', r, r', htailRecords,
            htailRecords', hpreLen, hpreLen', htailLen, htailLen',
            ⟨hb, ⟨hb', ⟨hstorageTail, hactionTail⟩⟩⟩⟩
          refine ⟨ActualInitializationBlockFoldExact.cursorRecord hc rewards x :: pre,
            post, ActualInitializationBlockFoldExact.cursorRecord hc rewards' x' :: pre',
            post', r, r', ?_⟩
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · calc
              _ = ActualInitializationBlockFoldExact.cursorRecord hc rewards x ::
                    (ActualInitializationRun.foldBlockAux p rate block
                      (ActualInitializationCursorMeasurability.cursorSuccessorInput hc rewards x).1.1
                      rewards C_star C_h (cursor + 1) fuel (by omega)
                      (ActualInitializationCursorMeasurability.cursorSuccessorInput hc rewards x).1.2.1
                      (ActualInitializationCursorMeasurability.cursorSuccessorInput hc rewards x).1.2.2
                      (ActualInitializationCursorMeasurability.cursorSuccessorInput hc rewards x).2).records := hr
              _ = ActualInitializationBlockFoldExact.cursorRecord hc rewards x ::
                    (pre ++ r :: post) := congrArg (List.cons _) htailRecords
              _ = (ActualInitializationBlockFoldExact.cursorRecord hc rewards x :: pre) ++
                    r :: post := by simp
          · calc
              _ = ActualInitializationBlockFoldExact.cursorRecord hc rewards' x' ::
                    (ActualInitializationRun.foldBlockAux p rate block
                      (ActualInitializationCursorMeasurability.cursorSuccessorInput hc rewards' x').1.1
                      rewards' C_star C_h (cursor + 1) fuel (by omega)
                      (ActualInitializationCursorMeasurability.cursorSuccessorInput hc rewards' x').1.2.1
                      (ActualInitializationCursorMeasurability.cursorSuccessorInput hc rewards' x').1.2.2
                      (ActualInitializationCursorMeasurability.cursorSuccessorInput hc rewards' x').2).records := hr'
              _ = ActualInitializationBlockFoldExact.cursorRecord hc rewards' x' ::
                    (pre' ++ r' :: post') := congrArg (List.cons _) htailRecords'
              _ = (ActualInitializationBlockFoldExact.cursorRecord hc rewards' x' :: pre') ++
                    r' :: post' := by simp
          · simp [hpreLen]
          · simp [hpreLen']
          · exact hlength
          · exact hlength'
          · exact ⟨hb, ⟨hb', ⟨hstorageTail, hactionTail⟩⟩⟩

/-- Indexed strict-past consequence. Both indices are proved in range, and
block transports come from membership in the actual fold. No current own
feedback equality is required. -/
theorem foldBlockAux_action_eq_of_past_feedback
    {p : Parameters} {rate : RateInput p} {block : Fin (n_boot p)}
    {C_star C_h : ℝ} {cursor fuel n : ℕ}
    (hbudget : cursor + fuel = BootstrapObservedFollower.blockLength p block)
    (x x' : ActualInitializationCursorMeasurability.CursorInput
      p rate block C_star C_h cursor)
    (rewards rewards' : ActualInitializationPhysicalStep.GridRewardTable p)
    (i : Fin (p.m - 1)) (hn : n < fuel)
    (hstorage : x.1.2.2 i = x'.1.2.2 i)
    (hpublic : x.1.1.1 = x'.1.1.1)
    (hround : ∀ t : Fin p.T,
      BootstrapObservedFollower.blockStart p block + cursor ≤ t.val →
      t.val < BootstrapObservedFollower.blockStop p block →
      BootstrapPhysicalInput.playerRoundScalarAt p x.1.1.2
          (PublicDiscreteDraws.followerPlayer p.two_le_m i) t =
        BootstrapPhysicalInput.playerRoundScalarAt p x'.1.1.2
          (PublicDiscreteDraws.followerPlayer p.two_le_m i) t)
    (hfeedback :
      ((ActualInitializationRun.foldBlockAux p rate block x.1.1 rewards C_star C_h
          cursor fuel hbudget x.1.2.1 x.1.2.2 x.2).records.map
          (fun r => r.result.feedback (PublicDiscreteDraws.followerPlayer p.two_le_m i))).take n =
      ((ActualInitializationRun.foldBlockAux p rate block x'.1.1 rewards' C_star C_h
          cursor fuel hbudget x'.1.2.1 x'.1.2.2 x'.2).records.map
          (fun r => r.result.feedback (PublicDiscreteDraws.followerPlayer p.two_le_m i))).take n) :
    let V := ActualInitializationRun.foldBlockAux p rate block x.1.1 rewards C_star C_h
      cursor fuel hbudget x.1.2.1 x.1.2.2 x.2
    let V' := ActualInitializationRun.foldBlockAux p rate block x'.1.1 rewards' C_star C_h
      cursor fuel hbudget x'.1.2.1 x'.1.2.2 x'.2
    V.records.length = fuel ∧ V'.records.length = fuel ∧
      ∃ (hindex : n < V.records.length) (hindex' : n < V'.records.length),
        ∃ hb : (V.records[n]'hindex).block = block,
          ∃ hb' : (V'.records[n]'hindex').block = block,
            transportedIncomingFollower (V.records[n]'hindex) hb i =
                transportedIncomingFollower (V'.records[n]'hindex') hb' i ∧
              (V.records[n]'hindex).result.actions
                  (PublicDiscreteDraws.followerPlayer p.two_le_m i) =
                (V'.records[n]'hindex').result.actions
                  (PublicDiscreteDraws.followerPlayer p.two_le_m i) := by
  obtain ⟨pre, post, pre', post', r, r', hr, hr', hpre, hpre', hlength, hlength',
      hb, hb', hstate, haction⟩ :=
    foldBlockAux_strict_past_follower_locality hbudget x x' rewards rewards' i hn
      hstorage hpublic hround hfeedback
  let V := ActualInitializationRun.foldBlockAux p rate block x.1.1 rewards C_star C_h
    cursor fuel hbudget x.1.2.1 x.1.2.2 x.2
  let V' := ActualInitializationRun.foldBlockAux p rate block x'.1.1 rewards' C_star C_h
    cursor fuel hbudget x'.1.2.1 x'.1.2.2 x'.2
  have hnV : n < V.records.length := by rw [hlength]; exact hn
  have hnV' : n < V'.records.length := by rw [hlength']; exact hn
  have hget : V.records[n]'hnV = r := by
    simp only [V, hr, List.getElem_append, hpre, Nat.lt_irrefl, dite_false,
      Nat.sub_self, List.getElem_cons_zero]
  have hget' : V'.records[n]'hnV' = r' := by
    simp only [V', hr', List.getElem_append, hpre', Nat.lt_irrefl, dite_false,
      Nat.sub_self, List.getElem_cons_zero]
  refine ⟨hlength, hlength', hnV, hnV', ?_⟩
  rw [hget, hget']
  exact ⟨hb, hb', hstate, haction⟩

/-- The actual own-action and own-feedback lists both have exactly the
remaining clipped-block length. -/
theorem foldBlockAux_own_history_lengths
    {p : Parameters} {rate : RateInput p} {block : Fin (n_boot p)}
    {C_star C_h : ℝ} {cursor fuel : ℕ}
    (hbudget : cursor + fuel = BootstrapObservedFollower.blockLength p block)
    (x : ActualInitializationCursorMeasurability.CursorInput
      p rate block C_star C_h cursor)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (i : Fin (p.m - 1)) :
    let V := ActualInitializationRun.foldBlockAux p rate block x.1.1 rewards C_star C_h
      cursor fuel hbudget x.1.2.1 x.1.2.2 x.2
    (V.records.map (fun r => r.result.actions
      (PublicDiscreteDraws.followerPlayer p.two_le_m i))).length = fuel ∧
      (V.records.map (fun r => r.result.feedback
        (PublicDiscreteDraws.followerPlayer p.two_le_m i))).length = fuel := by
  simp only [List.length_map, foldBlockAux_records_length hbudget x rewards, and_self]

/-- An actual bootstrap record retains bootstrap storage and applies the
accepted one-observation operation on its original public arrays and its own
physical feedback. Readiness and the prepared incoming storage are recovered
from this record's executed step. -/
theorem initialization_record_bootstrap_next
    {p : Parameters} {rate : RateInput p}
    {source : BootstrapPrivateRoundStreams.SourceInput p}
    {rewards : ActualInitializationPhysicalStep.GridRewardTable p}
    (r : ActualInitializationRun.PhysicalRoundRecord p rate source rewards)
    (i : Fin (p.m - 1)) (state : BootstrapObservedFollower.StartupState p r.block)
    (hstate : r.followersBefore i = .bootstrap state) :
    ∃ hready : ActualInitializationPhysicalStep.followerAtNextCursor
        (p := p) (rate := rate) r.time (.bootstrap state),
      (r.result.followers i).next = .bootstrap
        (BootstrapObservedFollower.observeOne p r.block state source.1.1 source.1.2
          r.time (ActualInitializationPhysicalStep.observationOfGrid p
            (r.result.feedback (PublicDiscreteDraws.followerPlayer p.two_le_m i)))
          hready.1 hready.2.1 hready.2.2) := by
  have hready := (ActualInitializationPhysicalStep.step_succeeds_iff_ready rate
    r.block r.time r.coordinatorBefore r.followersBefore source rewards).mp
      ⟨r.result, r.executed⟩
  have hreadyState : ActualInitializationPhysicalStep.followerAtNextCursor
      (p := p) (rate := rate) r.time (.bootstrap state) := by
    simpa only [hstate] using hready.2.2.2.2.2 i
  obtain ⟨prepared, hprepare⟩ :=
    (ActualInitializationPhysicalStep.prepare_eq_ok_iff_ready rate r.block r.time
      r.coordinatorBefore r.followersBefore source rewards).mpr hready
  have hobserved : ActualInitializationPhysicalStep.observePrepared prepared =
      .ok r.result := by
    simpa only [ActualInitializationPhysicalStep.step, hprepare] using r.executed
  have hresultPrepared : r.result.prepared = prepared := by
    have hround : r.result =
        ⟨prepared, (ActualInitializationPhysicalStep.observeFollowers prepared).val,
          (ActualInitializationPhysicalStep.observeFollowers prepared).property⟩ := by
      simpa [ActualInitializationPhysicalStep.observePrepared] using hobserved.symm
    rw [hround]
  have hprepared : r.result.prepared.followers i =
      ActualInitializationPhysicalStep.prepareFollowerValid rate r.block r.time source i
        (r.followersBefore i) (hready.2.2.2.2.2 i) := by
    rw [hresultPrepared]
    have h := hprepare
    simp [ActualInitializationPhysicalStep.prepare, hready] at h
    cases h
    rfl
  have hactual := ActualInitializationHorizon.physicalRoundRecord_actual r
  have htransition := r.result.followerTransition i
  rw [r.result_time, hactual.2.1, hprepared, ← hactual.2.2.2.2] at htransition
  have hobs := BootstrapObservedFollower.observe_accepted_processed p r.block state
    source.1.1 source.1.2 r.time
    (ActualInitializationPhysicalStep.observationOfGrid p
      (r.result.feedback (PublicDiscreteDraws.followerPlayer p.two_le_m i)))
    hreadyState.1 hreadyState.2.1 hreadyState.2.2
  -- Substitute incoming storage on this same original source only. The
  -- two-source locality proofs above instead use the public local codecs.
  have hpreparedState : ActualInitializationPhysicalStep.prepareFollowerValid rate
      r.block r.time source i (r.followersBefore i) (hready.2.2.2.2.2 i) =
        ActualInitializationPhysicalStep.prepareFollowerValid rate r.block r.time source i
          (.bootstrap state) hreadyState :=
    ActualInitializationRun.prepareFollowerValid_congr r.time source i
      (r.followersBefore i) (.bootstrap state) hstate (hready.2.2.2.2.2 i) hreadyState
  rw [hpreparedState] at htransition
  simp only [ActualInitializationPhysicalStep.prepareFollowerValid,
    ActualInitializationPhysicalStep.observeFollower, hobs] at htransition
  exact ⟨hreadyState, (congrArg ActualInitializationPhysicalStep.FollowerOutcome.next
    (Except.ok.inj htransition)).symm⟩

/-- At every genuine active bootstrap record the gain includes this positive
stay even when a declaration is already pending. Pending freezes the candidate
registers, not gain counting or physical play. -/
theorem initialization_record_active_gain
    {p : Parameters} {rate : RateInput p}
    {source : BootstrapPrivateRoundStreams.SourceInput p}
    {rewards : ActualInitializationPhysicalStep.GridRewardTable p}
    (r : ActualInitializationRun.PhysicalRoundRecord p rate source rewards)
    (i : Fin (p.m - 1)) (state : BootstrapObservedFollower.StartupState p r.block)
    (hstate : r.followersBefore i = .bootstrap state)
    (held : Fin p.K) (privateID : Fin (A_id p)) (gain : ℕ)
    (registers : BootstrapAllCandidateController.Registers p)
    (hactive : state.blockCase = .active held privateID gain registers) :
    let observation := ActualInitializationPhysicalStep.observationOfGrid p
      (r.result.feedback (PublicDiscreteDraws.followerPlayer p.two_le_m i))
    let nextGain := if BootstrapObservedFollower.positiveStay
      source.1.1 privateID r.time observation then gain + 1 else gain
    ∃ next : BootstrapObservedFollower.StartupState p r.block,
      (r.result.followers i).next = .bootstrap next ∧
        next.blockCase.gain = nextGain ∧
        (registers.pending.isSome = true →
          next.blockCase = .active held privateID nextGain registers) := by
  obtain ⟨hready, hnext⟩ := initialization_record_bootstrap_next r i state hstate
  refine ⟨_, hnext, ?_, ?_⟩
  · exact BootstrapObservedFollower.observeOne_active_gain_eq p r.block state
      source.1.1 source.1.2 r.time _ hready.1 hready.2.1 hready.2.2
      held privateID gain registers hactive
  · intro hpending
    exact BootstrapObservedFollower.observeOne_pending_persists p r.block state
      source.1.1 source.1.2 r.time _ hready.1 hready.2.1 hready.2.2
      held privateID gain registers hactive hpending

/-- Once a declaration is pending, the genuine remaining cursor fold retains
the candidate registers and original numerators, while counting every positive
stay through the clipped block endpoint. The count uses actual physical records,
including their own feedback; no hypothetical trace or gain law is supplied. -/
theorem foldBlockAux_pending_gain
    {p : Parameters} {rate : RateInput p} {block : Fin (n_boot p)}
    {C_star C_h : ℝ} {cursor fuel : ℕ}
    (hbudget : cursor + fuel = BootstrapObservedFollower.blockLength p block)
    (x : ActualInitializationCursorMeasurability.CursorInput
      p rate block C_star C_h cursor)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (i : Fin (p.m - 1))
    (state : BootstrapObservedFollower.StartupState p block)
    (hstate : x.1.2.2 i = .bootstrap state)
    (held : Fin p.K) (privateID : Fin (A_id p)) (gain : ℕ)
    (registers : BootstrapAllCandidateController.Registers p)
    (hactive : state.blockCase = .active held privateID gain registers)
    (hpending : registers.pending.isSome = true) :
    let V := ActualInitializationRun.foldBlockAux p rate block x.1.1 rewards C_star C_h
      cursor fuel hbudget x.1.2.1 x.1.2.2 x.2
    ∃ final : BootstrapObservedFollower.StartupState p block,
      V.followers i = .bootstrap final ∧ final.numerators = state.numerators ∧
        final.blockCase = .active held privateID
          (gain + V.records.countP (fun r => decide
            (BootstrapObservedFollower.positiveStay x.1.1.1.1 privateID r.time
              (ActualInitializationPhysicalStep.observationOfGrid p
                (r.result.feedback (PublicDiscreteDraws.followerPlayer p.two_le_m i))))))
          registers := by
  induction fuel generalizing cursor state gain with
  | zero =>
      have hd := ActualInitializationBlockFoldExact.foldBlockAux_zero_data
        hbudget rewards x
      have hf := congrArg (fun data => data.2.1) hd
      have hr := congrArg (fun data => data.2.2) hd
      dsimp only at hf hr ⊢
      refine ⟨state, ?_, rfl, ?_⟩
      · rw [hf]; exact hstate
      · simpa only [hr, List.countP_nil, Nat.add_zero] using hactive
  | succ fuel ih =>
      have hc : cursor < BootstrapObservedFollower.blockLength p block := by omega
      have hd := ActualInitializationBlockFoldExact.foldBlockAux_succ_data
        hbudget hc rewards x
      have hf := congrArg (fun data => data.2.1) hd
      have hr := congrArg (fun data => data.2.2) hd
      dsimp only at hf hr
      let r := ActualInitializationBlockFoldExact.cursorRecord hc rewards x
      let next := ActualInitializationCursorMeasurability.cursorSuccessorInput hc rewards x
      obtain ⟨hready, hnext⟩ := initialization_record_bootstrap_next r i state hstate
      let observation := ActualInitializationPhysicalStep.observationOfGrid p
        (r.result.feedback (PublicDiscreteDraws.followerPlayer p.two_le_m i))
      let nextGain := if BootstrapObservedFollower.positiveStay
        x.1.1.1.1 privateID r.time observation then gain + 1 else gain
      let stateNext := BootstrapObservedFollower.observeOne p block state
        x.1.1.1.1 x.1.1.1.2 r.time observation hready.1 hready.2.1 hready.2.2
      have hnextState : next.1.2.2 i = .bootstrap stateNext := hnext
      have hnextCase : stateNext.blockCase = .active held privateID nextGain registers :=
        BootstrapObservedFollower.observeOne_pending_persists p block state
          x.1.1.1.1 x.1.1.1.2 r.time observation hready.1 hready.2.1 hready.2.2
          held privateID gain registers hactive hpending
      obtain ⟨final, hfinal, hnumerators, hcase⟩ :=
        ih (hbudget := by omega) next stateNext hnextState nextGain hnextCase
      dsimp only
      refine ⟨final, ?_, ?_, ?_⟩
      · rw [hf]; exact hfinal
      · exact hnumerators.trans (BootstrapObservedFollower.observeOne_numerators
          p block state x.1.1.1.1 x.1.1.1.2 r.time observation
          hready.1 hready.2.1 hready.2.2)
      · rw [hr]
        let positive : ActualInitializationRun.PhysicalRoundRecord p rate x.1.1 rewards → Bool :=
          fun record => decide (BootstrapObservedFollower.positiveStay
            x.1.1.1.1 privateID record.time
            (ActualInitializationPhysicalStep.observationOfGrid p
              (record.result.feedback (PublicDiscreteDraws.followerPlayer p.two_le_m i))))
        let tail := ActualInitializationRun.foldBlockAux p rate block next.1.1 rewards
          C_star C_h (cursor + 1) fuel (by omega) next.1.2.1 next.1.2.2 next.2
        have hcount : nextGain + tail.records.countP positive =
            gain + (r :: tail.records).countP positive := by
          rw [List.countP_cons (p := positive) (a := r) (l := tail.records)]
          by_cases hstay : BootstrapObservedFollower.positiveStay
            x.1.1.1.1 privateID r.time observation
          · simp [nextGain, positive, observation, hstay, Nat.add_assoc, Nat.add_comm 1]
          · simp [nextGain, positive, observation, hstay]
        exact hcase.trans (congrArg (fun g =>
          BootstrapObservedFollower.StartupBlockCase.active held privateID g registers) hcount)

/-- The active boundary formula uses the retained held arm, original numerator
vector and accumulated gain. On completed actual folds this includes every
round, including those after a pending declaration. -/
theorem bootstrap_active_boundary_update {p : Parameters} {block : Fin (n_boot p)}
    (state : BootstrapObservedFollower.StartupState p block)
    (held : Fin p.K) (privateID : Fin (A_id p)) (gain : ℕ)
    (registers : BootstrapAllCandidateController.Registers p)
    (hactive : state.blockCase = .active held privateID gain registers) :
    BootstrapObservedFollower.updatedNumerators p block state =
      BootstrapWeightPotential.next (b_N p) state.numerators
        (BootstrapObservedFollower.activeWeightBlock p held gain
          (BootstrapObservedFollower.activeGain_le_B_boot p block state
            held privateID gain registers hactive)) ∧
      BootstrapObservedFollower.pendingDeclaration state.blockCase = registers.pending := by
  exact ⟨BootstrapObservedFollower.updatedNumerators_active_eq_next p block state
    held privateID gain registers hactive,
    by simp only [hactive, BootstrapObservedFollower.pendingDeclaration]⟩

/-- Inactive bootstrap boundaries retain the entire original numerator vector. -/
theorem bootstrap_inactive_boundary {p : Parameters} {rate : RateInput p}
    {block : Fin (n_boot p)} (state : BootstrapObservedFollower.StartupState p block)
    (hinactive : state.blockCase = .inactive) :
    ActualInitializationRun.boundaryOutputFromFollower p rate block (.bootstrap state) =
        .continueBootstrap state.numerators state.numerators_lower_bound
          (BootstrapObservedFollower.nextActivationRound p block) ∧
      ActualInitializationRun.followerCarryAtBlockBoundary p rate block (.bootstrap state) =
        .bootstrap state.numerators state.numerators_lower_bound := by
  have hupdate := BootstrapObservedFollower.updatedNumerators_inactive p block state hinactive
  simp only [ActualInitializationRun.followerCarryAtBlockBoundary,
    ActualInitializationRun.boundaryOutputFromFollower, hinactive,
    BootstrapObservedFollower.pendingDeclaration, Option.elim_none, hupdate,
    ActualInitializationRun.followerCarryOfBoundaryOutput, and_self]

/-- A first declaration installs only the initial ordinary state and memory
at the actual next activation round, including `T + 1` for the clipped final
block. Declared ordinary and dagger storage is handled by the separate copied
branch of the same literal boundary operation. -/
theorem bootstrap_first_declaration_boundary {p : Parameters} {rate : RateInput p}
    {block : Fin (n_boot p)} (state : BootstrapObservedFollower.StartupState p block)
    (row : Fin (M p))
    (hpending : BootstrapObservedFollower.pendingDeclaration state.blockCase = some row) :
    ActualInitializationRun.boundaryOutputFromFollower p rate block (.bootstrap state) =
        .firstDeclaration row (BootstrapObservedFollower.nextActivationRound p block)
          (ReferencePrelaunchFollower.initial p rate.eta)
          (ActiveFollowerLifecycle.initialMemory p) ∧
      ActualInitializationRun.followerCarryAtBlockBoundary p rate block (.bootstrap state) =
        .declared row (BootstrapObservedFollower.nextActivationRound p block)
          (.ordinary (ReferencePrelaunchFollower.initial p rate.eta)
            (ActiveFollowerLifecycle.initialMemory p)) := by
  simp only [ActualInitializationRun.followerCarryAtBlockBoundary,
    ActualInitializationRun.boundaryOutputFromFollower, hpending, Option.elim_some,
    ActualInitializationRun.followerCarryOfBoundaryOutput, and_self]

/-- Retained declared storage is copied whole across the boundary, including
ordinary buffers, saved real values and the dagger configuration. -/
theorem declared_boundary_preserves {p : Parameters} {rate : RateInput p}
    (block : Fin (n_boot p)) (row : Fin (M p))
    (activation : ReferencePrelaunchFollower.Activation p)
    (configuration : DeclaredFollowerLocalRound.LocalConfiguration p rate) :
    ActualInitializationRun.boundaryOutputFromFollower p rate block
        (.declared row activation configuration) = .preserveDeclared row activation configuration ∧
      ActualInitializationRun.followerCarryAtBlockBoundary p rate block
        (.declared row activation configuration) = .declared row activation configuration :=
  ⟨rfl, rfl⟩

end Bandits.Support.ActualInitializationBlockFollowerLocality

end
