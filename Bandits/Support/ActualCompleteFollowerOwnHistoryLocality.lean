/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ActualFollowerCalendarContinuity

import Lean.Elab.Tactic.Omega

/-!
# Actual complete-history locality for one follower

Equal public output, the selected follower's original block triples, its own
round scalars, and its strict-past actual feedback determine its complete
pre-round storage and current arm on the full calendar. The two executions
retain their own rewards, private coordinates, initialization paths, and
launch times.

Mathematical evidence: sources/zip4/manuscript/01_introduction.tex:20-36,
sources/zip4/manuscript/07_public_setup.tex:28-38,55-114,
sources/zip4/manuscript/appendix_b_communication.tex:94-131,
sources/zip4/manuscript/06_interruptions.tex:240-296, and
sources/zip4/manuscript/appendix_a_local_protocol.tex:6-14.
-/

@[expose] public section

noncomputable section

open Bandits.Support.BootstrapDimensions
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.PublicDiscreteDraws
open Bandits.Support.ActualInitializationPhysicalStep
open Bandits.Support.ActualInitializationRun
open Bandits.Support.ActualPostlaunchFollowerMeasurability
open Bandits.Support.ActualPostlaunchFollowerPreparationLocality
open Bandits.Support.ActualPostlaunchFollowerObservationLocality
open Bandits.Support.ActualCompletePhysicalHistory

namespace Bandits.Support.ActualCompleteFollowerOwnHistoryLocality

variable {p : Bandits.Support.ActualFollowerCalendarContinuity.Parameters}
  (rate : Bandits.Support.ActualFollowerCalendarContinuity.RateInput p)
  (source other : BootstrapPrivateRoundStreams.SourceInput p)
  (rewards otherRewards : ActualCompletePhysicalHistory.GridRewardTable p)
  (C_star C_h : ℝ) (i : Fin (p.m - 1)) (t : Fin p.T)

private theorem actualPlayerFeedbackHistory_length
    (worldSource : BootstrapPrivateRoundStreams.SourceInput p)
    (worldRewards : ActualCompletePhysicalHistory.GridRewardTable p)
    (follower : Fin (p.m - 1)) :
    (ActualCompletePhysicalHistory.playerGridFeedbackHistory
      (Bandits.Support.ActualFollowerCalendarContinuity.actualHistory
        rate worldSource worldRewards C_star C_h)
      (PublicDiscreteDraws.followerPlayer p.two_le_m follower)).length = p.T := by
  have h := ActualCompletePhysicalHistory.sourceInitializedActualCompleteHistory_lengths
    p rate worldSource worldRewards C_star C_h
  simpa [ActualCompletePhysicalHistory.playerGridFeedbackHistory,
    ActualCompletePhysicalHistory.feedbackHistory,
    Bandits.Support.ActualFollowerCalendarContinuity.actualHistory] using h.1

private theorem actualPlayerArmHistory_length
    (worldSource : BootstrapPrivateRoundStreams.SourceInput p)
    (worldRewards : ActualCompletePhysicalHistory.GridRewardTable p)
    (follower : Fin (p.m - 1)) :
    (ActualCompletePhysicalHistory.playerArmHistory
      (Bandits.Support.ActualFollowerCalendarContinuity.actualHistory
        rate worldSource worldRewards C_star C_h)
      (PublicDiscreteDraws.followerPlayer p.two_le_m follower)).length = p.T := by
  have h := ActualCompletePhysicalHistory.sourceInitializedActualCompleteHistory_lengths
    p rate worldSource worldRewards C_star C_h
  simpa [ActualCompletePhysicalHistory.playerArmHistory,
    ActualCompletePhysicalHistory.actionHistory,
    Bandits.Support.ActualFollowerCalendarContinuity.actualHistory] using h.1

private def actualPlayerFeedback
    (worldSource : BootstrapPrivateRoundStreams.SourceInput p)
    (worldRewards : ActualCompletePhysicalHistory.GridRewardTable p)
    (follower : Fin (p.m - 1)) (u : Fin p.T) : Fin (D p + 1) :=
  (ActualCompletePhysicalHistory.playerGridFeedbackHistory
    (Bandits.Support.ActualFollowerCalendarContinuity.actualHistory
      rate worldSource worldRewards C_star C_h)
    (PublicDiscreteDraws.followerPlayer p.two_le_m follower))[u.val]'(by
      rw [actualPlayerFeedbackHistory_length
        (rate := rate) (C_star := C_star) (C_h := C_h)
        (worldSource := worldSource) (worldRewards := worldRewards)
        (follower := follower)]
      exact u.isLt)

private def actualPlayerArm
    (worldSource : BootstrapPrivateRoundStreams.SourceInput p)
    (worldRewards : ActualCompletePhysicalHistory.GridRewardTable p)
    (follower : Fin (p.m - 1)) (u : Fin p.T) : Fin p.K :=
  (ActualCompletePhysicalHistory.playerArmHistory
    (Bandits.Support.ActualFollowerCalendarContinuity.actualHistory
      rate worldSource worldRewards C_star C_h)
    (PublicDiscreteDraws.followerPlayer p.two_le_m follower))[u.val]'(by
      rw [actualPlayerArmHistory_length
        (rate := rate) (C_star := C_star) (C_h := C_h)
        (worldSource := worldSource) (worldRewards := worldRewards)
        (follower := follower)]
      exact u.isLt)

private theorem actualPlayerFeedback_eq_of_strict_past
    (hfeedback :
      (ActualCompletePhysicalHistory.playerGridFeedbackHistory
        (Bandits.Support.ActualFollowerCalendarContinuity.actualHistory
          rate source rewards C_star C_h)
        (PublicDiscreteDraws.followerPlayer p.two_le_m i)).take t.val =
      (ActualCompletePhysicalHistory.playerGridFeedbackHistory
        (Bandits.Support.ActualFollowerCalendarContinuity.actualHistory
          rate other otherRewards C_star C_h)
        (PublicDiscreteDraws.followerPlayer p.two_le_m i)).take t.val)
    (u : Fin p.T) (hu : u.val < t.val) :
    actualPlayerFeedback (rate := rate) (C_star := C_star) (C_h := C_h)
        (worldSource := source) (worldRewards := rewards) (follower := i) (u := u) =
      actualPlayerFeedback (rate := rate) (C_star := C_star) (C_h := C_h)
        (worldSource := other) (worldRewards := otherRewards) (follower := i) (u := u) := by
  let left := ActualCompletePhysicalHistory.playerGridFeedbackHistory
    (Bandits.Support.ActualFollowerCalendarContinuity.actualHistory
      rate source rewards C_star C_h)
    (PublicDiscreteDraws.followerPlayer p.two_le_m i)
  let right := ActualCompletePhysicalHistory.playerGridFeedbackHistory
    (Bandits.Support.ActualFollowerCalendarContinuity.actualHistory
      rate other otherRewards C_star C_h)
    (PublicDiscreteDraws.followerPlayer p.two_le_m i)
  have hprefix : left.take t.val = right.take t.val := hfeedback
  have hget := congrArg (fun xs : List (Fin (D p + 1)) => xs[u.val]?) hprefix
  have hopt : left[u.val]? = right[u.val]? := by
    simp only [List.getElem?_take_of_lt hu] at hget
    exact hget
  have hleft : u.val < left.length := by
    change u.val <
      (ActualCompletePhysicalHistory.playerGridFeedbackHistory
        (Bandits.Support.ActualFollowerCalendarContinuity.actualHistory
          rate source rewards C_star C_h)
        (PublicDiscreteDraws.followerPlayer p.two_le_m i)).length
    rw [actualPlayerFeedbackHistory_length
      (rate := rate) (C_star := C_star) (C_h := C_h)
      (worldSource := source) (worldRewards := rewards) (follower := i)]
    exact u.isLt
  have hright : u.val < right.length := by
    change u.val <
      (ActualCompletePhysicalHistory.playerGridFeedbackHistory
        (Bandits.Support.ActualFollowerCalendarContinuity.actualHistory
          rate other otherRewards C_star C_h)
        (PublicDiscreteDraws.followerPlayer p.two_le_m i)).length
    rw [actualPlayerFeedbackHistory_length
      (rate := rate) (C_star := C_star) (C_h := C_h)
      (worldSource := other) (worldRewards := otherRewards) (follower := i)]
    exact u.isLt
  have hsome : some (left[u.val]'hleft) = some (right[u.val]'hright) := by
    rw [← List.getElem?_eq_getElem hleft, ← List.getElem?_eq_getElem hright]
    exact hopt
  change left[u.val]'_ = right[u.val]'_
  exact Option.some.inj hsome

private def actualCalendarLocalInput
    (worldSource : BootstrapPrivateRoundStreams.SourceInput p)
    (worldRewards : ActualCompletePhysicalHistory.GridRewardTable p)
    (follower : Fin (p.m - 1)) (u : Fin p.T)
    (hstate : ActualInitializationRun.followerAtCursor p rate
      (Bandits.Support.ActualFollowerCalendarContinuity.calendarBlockIndex u)
      (Bandits.Support.ActualFollowerCalendarContinuity.calendarCursor u)
      (Bandits.Support.ActualFollowerCalendarContinuity.calendarFollowerBefore
        rate worldSource worldRewards C_star C_h follower u)) :
    ActualPostlaunchFollowerMeasurability.LocalInput (rate := rate)
      (Bandits.Support.ActualFollowerCalendarContinuity.calendarBlockIndex u)
      (Bandits.Support.ActualFollowerCalendarContinuity.calendarCursor u) :=
  ActualPostlaunchFollowerMeasurability.localInputOfComponents worldSource
    (Bandits.Support.ActualFollowerCalendarContinuity.calendarFollowerBefore
      rate worldSource worldRewards C_star C_h follower u)
    hstate (actualPlayerFeedback (rate := rate) (C_star := C_star) (C_h := C_h)
      (worldSource := worldSource) (worldRewards := worldRewards)
      (follower := follower) (u := u))

private theorem preparationCoordinates_eq_of_public_and_round
    {block : Fin (n_boot p)} {cursor : Nat}
    (hcursor : cursor < BootstrapObservedFollower.blockLength p block)
    (follower : Fin (p.m - 1))
    (worldSource worldOther : BootstrapPrivateRoundStreams.SourceInput p)
    (x x' : ActualPostlaunchFollowerMeasurability.LocalInput
      (rate := rate) block cursor)
    (hx : ActualPostlaunchFollowerMeasurability.localSource x = worldSource)
    (hx' : ActualPostlaunchFollowerMeasurability.localSource x' = worldOther)
    (hfollower : ActualPostlaunchFollowerMeasurability.localFollower x =
      ActualPostlaunchFollowerMeasurability.localFollower x')
    (hpublic : worldSource.1 = worldOther.1)
    (hround : BootstrapPhysicalInput.playerRoundScalarAt p worldSource.2
        (PublicDiscreteDraws.followerPlayer p.two_le_m follower)
        (ActualPostlaunchFollowerMeasurability.localTime block cursor hcursor) =
      BootstrapPhysicalInput.playerRoundScalarAt p worldOther.2
        (PublicDiscreteDraws.followerPlayer p.two_le_m follower)
        (ActualPostlaunchFollowerMeasurability.localTime block cursor hcursor)) :
    ActualPostlaunchFollowerPreparationLocality.preparationSourceCoordinates
        (rate := rate) hcursor follower x =
      ActualPostlaunchFollowerPreparationLocality.preparationSourceCoordinates
        (rate := rate) hcursor follower x' := by
  cases hlocal : ActualPostlaunchFollowerMeasurability.localFollower x with
  | bootstrap startup =>
      have hlocal' : ActualPostlaunchFollowerMeasurability.localFollower x' =
          .bootstrap startup := hfollower.symm.trans hlocal
      cases hcase : startup.blockCase with
      | inactive =>
          simp [ActualPostlaunchFollowerPreparationLocality.preparationSourceCoordinates,
            hx, hx', hlocal, hlocal', hcase,
            ActualBootstrapObservationCode.sourcePrivate,
            hround]
      | active held privateID gain registers =>
          simp [ActualPostlaunchFollowerPreparationLocality.preparationSourceCoordinates,
            hx, hx', hlocal, hlocal', hcase,
            ActualBootstrapObservationCode.sourcePrivate,
            ActualBootstrapObservationCode.sourceIDs,
            hpublic, hround]
  | declared row activation configuration =>
      have hlocal' : ActualPostlaunchFollowerMeasurability.localFollower x' =
          .declared row activation configuration := hfollower.symm.trans hlocal
      cases hconfiguration : configuration with
      | dagger =>
          simp [ActualPostlaunchFollowerPreparationLocality.preparationSourceCoordinates,
            hlocal, hlocal', hconfiguration]
      | ordinary state memory =>
          simp [ActualPostlaunchFollowerPreparationLocality.preparationSourceCoordinates,
            hx, hx', hlocal, hlocal', hconfiguration,
            ActualBootstrapObservationCode.sourceRows,
            hpublic]

private theorem observationCoordinates_eq_of_public
    {block : Fin (n_boot p)} {cursor : Nat}
    (hcursor : cursor < BootstrapObservedFollower.blockLength p block)
    (follower : Fin (p.m - 1))
    (worldSource worldOther : BootstrapPrivateRoundStreams.SourceInput p)
    (x x' : ActualPostlaunchFollowerMeasurability.LocalInput
      (rate := rate) block cursor)
    (hx : ActualPostlaunchFollowerMeasurability.localSource x = worldSource)
    (hx' : ActualPostlaunchFollowerMeasurability.localSource x' = worldOther)
    (hfollower : ActualPostlaunchFollowerMeasurability.localFollower x =
      ActualPostlaunchFollowerMeasurability.localFollower x')
    (hpublic : worldSource.1 = worldOther.1) :
    ActualPostlaunchFollowerObservationLocality.observationSourceCoordinates
        (rate := rate) hcursor follower x =
      ActualPostlaunchFollowerObservationLocality.observationSourceCoordinates
        (rate := rate) hcursor follower x' := by
  cases hlocal : ActualPostlaunchFollowerMeasurability.localFollower x with
  | bootstrap startup =>
      have hlocal' : ActualPostlaunchFollowerMeasurability.localFollower x' =
          .bootstrap startup := hfollower.symm.trans hlocal
      cases hcase : startup.blockCase with
      | inactive =>
          simp [ActualPostlaunchFollowerObservationLocality.observationSourceCoordinates,
            hlocal, hlocal', hcase]
      | active held privateID gain registers =>
          simp [ActualPostlaunchFollowerObservationLocality.observationSourceCoordinates,
            hx, hx', hlocal, hlocal', hcase,
            ActualBootstrapObservationCode.sourceIDs,
            ActualBootstrapObservationCode.sourceRows, hpublic]
  | declared row activation configuration =>
      have hlocal' : ActualPostlaunchFollowerMeasurability.localFollower x' =
          .declared row activation configuration := hfollower.symm.trans hlocal
      cases hconfiguration : configuration with
      | dagger =>
          simp [ActualPostlaunchFollowerObservationLocality.observationSourceCoordinates,
            hlocal, hlocal', hconfiguration]
      | ordinary state memory =>
          simp [ActualPostlaunchFollowerObservationLocality.observationSourceCoordinates,
            hx, hx', hlocal, hlocal', hconfiguration,
            ActualBootstrapObservationCode.sourceRows, hpublic]

private theorem decodedFollowerNext_eq
    {block : Fin (n_boot p)} {time : Fin p.T}
    (worldSource worldOther : BootstrapPrivateRoundStreams.SourceInput p)
    (follower : Fin (p.m - 1))
    (code code' : ActualPostlaunchFollowerMeasurability.LocalCode
      (rate := rate) block)
    (outcome outcome' : ActualInitializationPhysicalStep.FollowerOutcome p rate block)
    (hcode : code = code')
    (hdecode : ActualPostlaunchFollowerMeasurability.decodeLocalCode
      worldSource time follower code = some outcome)
    (hdecode' : ActualPostlaunchFollowerMeasurability.decodeLocalCode
      worldOther time follower code' = some outcome') :
    outcome.next = outcome'.next := by
  have hnext (worldSource : BootstrapPrivateRoundStreams.SourceInput p)
      (code : ActualPostlaunchFollowerMeasurability.LocalCode
        (rate := rate) block)
      (outcome : ActualInitializationPhysicalStep.FollowerOutcome p rate block)
      (hdecode : ActualPostlaunchFollowerMeasurability.decodeLocalCode
        worldSource time follower code = some outcome) :
      outcome.next = ActualInitializationRoundMeasurability.followerStateOfCode
        p rate block code.2.2 := by
    unfold ActualPostlaunchFollowerMeasurability.decodeLocalCode at hdecode
    cases hprepared : ActualInitializationPreparationMeasurability.decodePreparedFollowerCode
        (rate := rate) (block := block) follower worldSource time code.1 with
    | none =>
        simp [hprepared] at hdecode
    | some prepared =>
        have hdecoded :
            some (⟨prepared,
              ActualInitializationRoundMeasurability.followerStateOfCode
                p rate block code.2.2⟩ : ActualInitializationPhysicalStep.FollowerOutcome
                p rate block) = some outcome := by
          simpa [hprepared] using hdecode
        have houtcome :
            (⟨prepared,
              ActualInitializationRoundMeasurability.followerStateOfCode
                p rate block code.2.2⟩ :
              ActualInitializationPhysicalStep.FollowerOutcome p rate block) = outcome := by
          exact Option.some.inj hdecoded
        cases houtcome
        rfl
  calc
    outcome.next = ActualInitializationRoundMeasurability.followerStateOfCode
        p rate block code.2.2 := hnext worldSource code outcome hdecode
    _ = ActualInitializationRoundMeasurability.followerStateOfCode
        p rate block code'.2.2 := by rw [hcode]
    _ = outcome'.next := (hnext worldOther code' outcome' hdecode').symm

private theorem beginFollowerBlock_eq_of_own_triple
    (block : Fin (n_boot p))
    (carry : ActualInitializationRun.FollowerCarry p rate)
    (htriple : source.2.1.1 block i = other.2.1.1 block i) :
    ActualInitializationRun.beginFollowerBlock p rate block source i carry =
      ActualInitializationRun.beginFollowerBlock p rate block other i carry := by
  cases carry with
  | bootstrap numerators lowerBound =>
      simp [ActualInitializationRun.beginFollowerBlock, htriple]
  | declared row activation configuration =>
      rfl

theorem sourceInitialized_follower_action_eq_of_own_history
    (hpublic : source.1 = other.1)
    (hblock : (fun b => source.2.1.1 b i) = (fun b => other.2.1.1 b i))
    (hround : (fun v => BootstrapPhysicalInput.playerRoundScalarAt p source.2
        (PublicDiscreteDraws.followerPlayer p.two_le_m i) v) =
      (fun v => BootstrapPhysicalInput.playerRoundScalarAt p other.2
        (PublicDiscreteDraws.followerPlayer p.two_le_m i) v))
    (hy : (ActualCompletePhysicalHistory.playerGridFeedbackHistory
        (Bandits.Support.ActualFollowerCalendarContinuity.actualHistory
          rate source rewards C_star C_h)
        (PublicDiscreteDraws.followerPlayer p.two_le_m i)).take t.val =
      (ActualCompletePhysicalHistory.playerGridFeedbackHistory
        (Bandits.Support.ActualFollowerCalendarContinuity.actualHistory
          rate other otherRewards C_star C_h)
        (PublicDiscreteDraws.followerPlayer p.two_le_m i)).take t.val) :
    Bandits.Support.ActualFollowerCalendarContinuity.calendarFollowerBefore
        rate source rewards C_star C_h i t =
      Bandits.Support.ActualFollowerCalendarContinuity.calendarFollowerBefore
        rate other otherRewards C_star C_h i t ∧
      (ActualCompletePhysicalHistory.playerArmHistory
        (Bandits.Support.ActualFollowerCalendarContinuity.actualHistory
          rate source rewards C_star C_h)
        (PublicDiscreteDraws.followerPlayer p.two_le_m i))[t.val]'(by
          have h := ActualCompletePhysicalHistory.sourceInitializedActualCompleteHistory_lengths
            p rate source rewards C_star C_h
          have hlen : (ActualCompletePhysicalHistory.playerArmHistory
              (Bandits.Support.ActualFollowerCalendarContinuity.actualHistory
                rate source rewards C_star C_h)
              (PublicDiscreteDraws.followerPlayer p.two_le_m i)).length = p.T := by
            simpa [ActualCompletePhysicalHistory.playerArmHistory,
              ActualCompletePhysicalHistory.actionHistory,
              Bandits.Support.ActualFollowerCalendarContinuity.actualHistory] using h.1
          rw [hlen]
          exact t.isLt) =
      (ActualCompletePhysicalHistory.playerArmHistory
        (Bandits.Support.ActualFollowerCalendarContinuity.actualHistory
          rate other otherRewards C_star C_h)
        (PublicDiscreteDraws.followerPlayer p.two_le_m i))[t.val]'(by
          have h := ActualCompletePhysicalHistory.sourceInitializedActualCompleteHistory_lengths
            p rate other otherRewards C_star C_h
          have hlen : (ActualCompletePhysicalHistory.playerArmHistory
              (Bandits.Support.ActualFollowerCalendarContinuity.actualHistory
                rate other otherRewards C_star C_h)
              (PublicDiscreteDraws.followerPlayer p.two_le_m i)).length = p.T := by
            simpa [ActualCompletePhysicalHistory.playerArmHistory,
              ActualCompletePhysicalHistory.actionHistory,
              Bandits.Support.ActualFollowerCalendarContinuity.actualHistory] using h.1
          rw [hlen]
          exact t.isLt) := by
  have hbeforePrefix : ∀ (n : Nat) (hn : n ≤ t.val),
      Bandits.Support.ActualFollowerCalendarContinuity.calendarFollowerBefore
          rate source rewards C_star C_h i
          ⟨n, Nat.lt_of_le_of_lt hn t.isLt⟩ =
        Bandits.Support.ActualFollowerCalendarContinuity.calendarFollowerBefore
          rate other otherRewards C_star C_h i
          ⟨n, Nat.lt_of_le_of_lt hn t.isLt⟩ := by
    intro n
    induction n with
    | zero =>
        intro hn
        have hinitialLeft :=
          Bandits.Support.ActualFollowerCalendarContinuity.calendar_follower_initial
            rate source rewards C_star C_h i
        have hinitialRight :=
          Bandits.Support.ActualFollowerCalendarContinuity.calendar_follower_initial
            rate other otherRewards C_star C_h i
        dsimp only at hinitialLeft hinitialRight
        have htriple := congrFun hblock (ActualInitializationRun.firstBlock p)
        have hbegin := beginFollowerBlock_eq_of_own_triple
          (rate := rate) (source := source) (other := other) (i := i)
          (ActualInitializationRun.firstBlock p)
          ((ActualInitializationRun.initialCarry p rate C_star C_h).followers i)
          htriple
        have hz :
            Bandits.Support.ActualFollowerCalendarContinuity.calendarFollowerBefore
                rate source rewards C_star C_h i
                ⟨0, Nat.lt_of_le_of_lt hn t.isLt⟩ =
              Bandits.Support.ActualFollowerCalendarContinuity.calendarFollowerBefore
                rate other otherRewards C_star C_h i
                ⟨0, Nat.lt_of_le_of_lt hn t.isLt⟩ := by
          rw [hinitialLeft, hinitialRight, hbegin]
        simpa using hz
    | succ n ih =>
        intro hn
        have hnle : n ≤ t.val := by omega
        have hbefore := ih hnle
        let u : Fin p.T := ⟨n, Nat.lt_of_le_of_lt hnle t.isLt⟩
        have hnext : u.val + 1 < p.T := by
          dsimp [u]
          omega
        let uNext : Fin p.T := ⟨u.val + 1, hnext⟩
        have hpast : n < t.val := by omega
        have hfeedback := actualPlayerFeedback_eq_of_strict_past
          (rate := rate) (source := source) (other := other)
          (rewards := rewards) (otherRewards := otherRewards)
          (C_star := C_star) (C_h := C_h) (i := i) (t := t)
          (hfeedback := hy) (u := u)
          (hu := by simpa [u] using hpast)
        obtain ⟨hstateLeft, _, hdecodeLeft, _⟩ :=
          Bandits.Support.ActualFollowerCalendarContinuity.calendar_record_localCode
            rate source rewards C_star C_h i u
        obtain ⟨hstateRight, _, hdecodeRight, _⟩ :=
          Bandits.Support.ActualFollowerCalendarContinuity.calendar_record_localCode
            rate other otherRewards C_star C_h i u
        let x := actualCalendarLocalInput
          (rate := rate) (C_star := C_star) (C_h := C_h)
          (worldSource := source) (worldRewards := rewards)
          (follower := i) (u := u) (hstate := hstateLeft)
        let x' := actualCalendarLocalInput
          (rate := rate) (C_star := C_star) (C_h := C_h)
          (worldSource := other) (worldRewards := otherRewards)
          (follower := i) (u := u) (hstate := hstateRight)
        have hdecodeLeft' :
            ActualPostlaunchFollowerMeasurability.decodeLocalCode source u i
              (ActualPostlaunchFollowerMeasurability.localCodeOnCursor
                (Bandits.Support.ActualFollowerCalendarContinuity.calendarCursor_lt_blockLength u)
                i x) =
              some (Bandits.Support.ActualFollowerCalendarContinuity.calendarFollowerOutcome
                rate source rewards C_star C_h i u) := by
          simpa [x, actualCalendarLocalInput, actualPlayerFeedback] using hdecodeLeft
        have hdecodeRight' :
            ActualPostlaunchFollowerMeasurability.decodeLocalCode other u i
              (ActualPostlaunchFollowerMeasurability.localCodeOnCursor
                (Bandits.Support.ActualFollowerCalendarContinuity.calendarCursor_lt_blockLength u)
                i x') =
              some (Bandits.Support.ActualFollowerCalendarContinuity.calendarFollowerOutcome
                rate other otherRewards C_star C_h i u) := by
          simpa [x', actualCalendarLocalInput, actualPlayerFeedback] using hdecodeRight
        have hlocal : ActualPostlaunchFollowerMeasurability.localFollower x =
            ActualPostlaunchFollowerMeasurability.localFollower x' := by
          change Bandits.Support.ActualFollowerCalendarContinuity.calendarFollowerBefore
              rate source rewards C_star C_h i u =
            Bandits.Support.ActualFollowerCalendarContinuity.calendarFollowerBefore
              rate other otherRewards C_star C_h i u
          exact hbefore
        have hx : ActualPostlaunchFollowerMeasurability.localSource x = source := by
          simp [x, actualCalendarLocalInput,
            ActualPostlaunchFollowerMeasurability.localInputOfComponents,
            ActualPostlaunchFollowerMeasurability.localSource]
        have hx' : ActualPostlaunchFollowerMeasurability.localSource x' = other := by
          simp [x', actualCalendarLocalInput,
            ActualPostlaunchFollowerMeasurability.localInputOfComponents,
            ActualPostlaunchFollowerMeasurability.localSource]
        have hscalarAtTime := congrFun hround u
        have hscalar : BootstrapPhysicalInput.playerRoundScalarAt p source.2
            (PublicDiscreteDraws.followerPlayer p.two_le_m i)
            (ActualPostlaunchFollowerMeasurability.localTime
              (Bandits.Support.ActualFollowerCalendarContinuity.calendarBlockIndex u)
              (Bandits.Support.ActualFollowerCalendarContinuity.calendarCursor u)
              (Bandits.Support.ActualFollowerCalendarContinuity.calendarCursor_lt_blockLength u)) =
          BootstrapPhysicalInput.playerRoundScalarAt p other.2
            (PublicDiscreteDraws.followerPlayer p.two_le_m i)
            (ActualPostlaunchFollowerMeasurability.localTime
              (Bandits.Support.ActualFollowerCalendarContinuity.calendarBlockIndex u)
              (Bandits.Support.ActualFollowerCalendarContinuity.calendarCursor u)
              (Bandits.Support.ActualFollowerCalendarContinuity.calendarCursor_lt_blockLength u)) := by
          rw [Bandits.Support.ActualFollowerCalendarContinuity.calendarLocalTime_eq_time u]
          exact hscalarAtTime
        have hprepCoordinates := preparationCoordinates_eq_of_public_and_round
          (rate := rate)
          (hcursor := Bandits.Support.ActualFollowerCalendarContinuity.calendarCursor_lt_blockLength u)
          (follower := i) (worldSource := source) (worldOther := other)
          (x := x) (x' := x') (hx := hx) (hx' := hx')
          (hfollower := hlocal) (hpublic := hpublic) (hround := hscalar)
        have hobsCoordinates := observationCoordinates_eq_of_public
          (rate := rate)
          (hcursor := Bandits.Support.ActualFollowerCalendarContinuity.calendarCursor_lt_blockLength u)
          (follower := i) (worldSource := source) (worldOther := other)
          (x := x) (x' := x') (hx := hx) (hx' := hx')
          (hfollower := hlocal) (hpublic := hpublic)
        have hfeedbackLocal :
            ActualPostlaunchFollowerMeasurability.localFeedback x =
              ActualPostlaunchFollowerMeasurability.localFeedback x' := by
          simpa [x, x', actualCalendarLocalInput,
            ActualPostlaunchFollowerMeasurability.localInputOfComponents,
            ActualPostlaunchFollowerMeasurability.localFeedback,
            actualPlayerFeedback] using hfeedback
        have hcode :=
          ActualPostlaunchFollowerObservationLocality.localCodeOnCursor_eq_of_own_coordinates
            (Bandits.Support.ActualFollowerCalendarContinuity.calendarCursor_lt_blockLength u)
            i x x' hlocal hprepCoordinates hobsCoordinates hfeedbackLocal
        have hafter := decodedFollowerNext_eq
          (rate := rate)
          (worldSource := source) (worldOther := other) (follower := i)
          (time := u)
          (code := ActualPostlaunchFollowerMeasurability.localCodeOnCursor
            (Bandits.Support.ActualFollowerCalendarContinuity.calendarCursor_lt_blockLength u)
            i x)
          (code' := ActualPostlaunchFollowerMeasurability.localCodeOnCursor
            (Bandits.Support.ActualFollowerCalendarContinuity.calendarCursor_lt_blockLength u)
            i x')
          (outcome := Bandits.Support.ActualFollowerCalendarContinuity.calendarFollowerOutcome
            rate source rewards C_star C_h i u)
          (outcome' := Bandits.Support.ActualFollowerCalendarContinuity.calendarFollowerOutcome
            rate other otherRewards C_star C_h i u)
          hcode hdecodeLeft' hdecodeRight'
        have hafter' :
            Bandits.Support.ActualFollowerCalendarContinuity.calendarFollowerAfter
                rate source rewards C_star C_h i u =
              Bandits.Support.ActualFollowerCalendarContinuity.calendarFollowerAfter
                rate other otherRewards C_star C_h i u := by
          simpa [Bandits.Support.ActualFollowerCalendarContinuity.calendarFollowerAfter]
            using hafter
        have hsuccessorLeft :=
          Bandits.Support.ActualFollowerCalendarContinuity.calendar_follower_successor
            rate source rewards C_star C_h i u hnext
        have hsuccessorRight :=
          Bandits.Support.ActualFollowerCalendarContinuity.calendar_follower_successor
            rate other otherRewards C_star C_h i u hnext
        by_cases hsameBlock :
            Bandits.Support.ActualFollowerCalendarContinuity.calendarBlockIndex u =
              Bandits.Support.ActualFollowerCalendarContinuity.calendarBlockIndex uNext
        · have hleft :
              Bandits.Support.ActualFollowerCalendarContinuity.calendarFollowerBefore
                  rate source rewards C_star C_h i uNext =
                cast (congrArg (ActualInitializationPhysicalStep.FollowerState p rate)
                  hsameBlock)
                  (Bandits.Support.ActualFollowerCalendarContinuity.calendarFollowerAfter
                    rate source rewards C_star C_h i u) := by
            simpa only [uNext, dite_eq_left hsameBlock] using hsuccessorLeft
          have hright :
              Bandits.Support.ActualFollowerCalendarContinuity.calendarFollowerBefore
                  rate other otherRewards C_star C_h i uNext =
                cast (congrArg (ActualInitializationPhysicalStep.FollowerState p rate)
                  hsameBlock)
                  (Bandits.Support.ActualFollowerCalendarContinuity.calendarFollowerAfter
                    rate other otherRewards C_star C_h i u) := by
            simpa only [uNext, dite_eq_left hsameBlock] using hsuccessorRight
          have hcast :
              cast (congrArg (ActualInitializationPhysicalStep.FollowerState p rate)
                  hsameBlock)
                  (Bandits.Support.ActualFollowerCalendarContinuity.calendarFollowerAfter
                    rate source rewards C_star C_h i u) =
                cast (congrArg (ActualInitializationPhysicalStep.FollowerState p rate)
                  hsameBlock)
                  (Bandits.Support.ActualFollowerCalendarContinuity.calendarFollowerAfter
                    rate other otherRewards C_star C_h i u) :=
            congrArg (fun state => cast
              (congrArg (ActualInitializationPhysicalStep.FollowerState p rate)
                hsameBlock) state) hafter'
          exact hleft.trans (hcast.trans hright.symm)
        · have hleft :
              Bandits.Support.ActualFollowerCalendarContinuity.calendarFollowerBefore
                  rate source rewards C_star C_h i uNext =
                ActualInitializationRun.beginFollowerBlock p rate
                  (Bandits.Support.ActualFollowerCalendarContinuity.calendarBlockIndex uNext)
                  source i
                  (ActualInitializationRun.followerCarryAtBlockBoundary p rate
                    (Bandits.Support.ActualFollowerCalendarContinuity.calendarBlockIndex u)
                    (Bandits.Support.ActualFollowerCalendarContinuity.calendarFollowerAfter
                      rate source rewards C_star C_h i u)) := by
            have hleft' :
                (Bandits.Support.ActualFollowerCalendarContinuity.calendarBlockIndex u).val + 1 =
                  (Bandits.Support.ActualFollowerCalendarContinuity.calendarBlockIndex uNext).val ∧
                u.val + 1 =
                  BootstrapObservedFollower.blockStop p
                    (Bandits.Support.ActualFollowerCalendarContinuity.calendarBlockIndex u) ∧
                uNext.val =
                  BootstrapObservedFollower.blockStart p
                    (Bandits.Support.ActualFollowerCalendarContinuity.calendarBlockIndex uNext) ∧
                Bandits.Support.ActualFollowerCalendarContinuity.calendarFollowerBefore
                    rate source rewards C_star C_h i uNext =
                  ActualInitializationRun.beginFollowerBlock p rate
                    (Bandits.Support.ActualFollowerCalendarContinuity.calendarBlockIndex uNext)
                    source i
                    (ActualInitializationRun.followerCarryAtBlockBoundary p rate
                      (Bandits.Support.ActualFollowerCalendarContinuity.calendarBlockIndex u)
                      (Bandits.Support.ActualFollowerCalendarContinuity.calendarFollowerAfter
                        rate source rewards C_star C_h i u)) := by
              simpa only [uNext, dite_eq_right hsameBlock] using hsuccessorLeft
            exact hleft'.2.2.2
          have hright :
              Bandits.Support.ActualFollowerCalendarContinuity.calendarFollowerBefore
                  rate other otherRewards C_star C_h i uNext =
                ActualInitializationRun.beginFollowerBlock p rate
                  (Bandits.Support.ActualFollowerCalendarContinuity.calendarBlockIndex uNext)
                  other i
                  (ActualInitializationRun.followerCarryAtBlockBoundary p rate
                    (Bandits.Support.ActualFollowerCalendarContinuity.calendarBlockIndex u)
                    (Bandits.Support.ActualFollowerCalendarContinuity.calendarFollowerAfter
                      rate other otherRewards C_star C_h i u)) := by
            have hright' :
                (Bandits.Support.ActualFollowerCalendarContinuity.calendarBlockIndex u).val + 1 =
                  (Bandits.Support.ActualFollowerCalendarContinuity.calendarBlockIndex uNext).val ∧
                u.val + 1 =
                  BootstrapObservedFollower.blockStop p
                    (Bandits.Support.ActualFollowerCalendarContinuity.calendarBlockIndex u) ∧
                uNext.val =
                  BootstrapObservedFollower.blockStart p
                    (Bandits.Support.ActualFollowerCalendarContinuity.calendarBlockIndex uNext) ∧
                Bandits.Support.ActualFollowerCalendarContinuity.calendarFollowerBefore
                    rate other otherRewards C_star C_h i uNext =
                  ActualInitializationRun.beginFollowerBlock p rate
                    (Bandits.Support.ActualFollowerCalendarContinuity.calendarBlockIndex uNext)
                    other i
                    (ActualInitializationRun.followerCarryAtBlockBoundary p rate
                      (Bandits.Support.ActualFollowerCalendarContinuity.calendarBlockIndex u)
                      (Bandits.Support.ActualFollowerCalendarContinuity.calendarFollowerAfter
                        rate other otherRewards C_star C_h i u)) := by
              simpa only [uNext, dite_eq_right hsameBlock] using hsuccessorRight
            exact hright'.2.2.2
          have hcarry :
              ActualInitializationRun.followerCarryAtBlockBoundary p rate
                  (Bandits.Support.ActualFollowerCalendarContinuity.calendarBlockIndex u)
                  (Bandits.Support.ActualFollowerCalendarContinuity.calendarFollowerAfter
                    rate source rewards C_star C_h i u) =
                ActualInitializationRun.followerCarryAtBlockBoundary p rate
                  (Bandits.Support.ActualFollowerCalendarContinuity.calendarBlockIndex u)
                  (Bandits.Support.ActualFollowerCalendarContinuity.calendarFollowerAfter
                    rate other otherRewards C_star C_h i u) :=
            congrArg (ActualInitializationRun.followerCarryAtBlockBoundary p rate
              (Bandits.Support.ActualFollowerCalendarContinuity.calendarBlockIndex u)) hafter'
          have htriple := congrFun hblock
            (Bandits.Support.ActualFollowerCalendarContinuity.calendarBlockIndex uNext)
          have hbegin := beginFollowerBlock_eq_of_own_triple
            (rate := rate) (source := source) (other := other) (i := i)
            (Bandits.Support.ActualFollowerCalendarContinuity.calendarBlockIndex uNext)
            (ActualInitializationRun.followerCarryAtBlockBoundary p rate
              (Bandits.Support.ActualFollowerCalendarContinuity.calendarBlockIndex u)
              (Bandits.Support.ActualFollowerCalendarContinuity.calendarFollowerAfter
                rate source rewards C_star C_h i u))
            htriple
          have hbeginRight :
              ActualInitializationRun.beginFollowerBlock p rate
                  (Bandits.Support.ActualFollowerCalendarContinuity.calendarBlockIndex uNext)
                  source i
                  (ActualInitializationRun.followerCarryAtBlockBoundary p rate
                    (Bandits.Support.ActualFollowerCalendarContinuity.calendarBlockIndex u)
                    (Bandits.Support.ActualFollowerCalendarContinuity.calendarFollowerAfter
                      rate source rewards C_star C_h i u)) =
                ActualInitializationRun.beginFollowerBlock p rate
                  (Bandits.Support.ActualFollowerCalendarContinuity.calendarBlockIndex uNext)
                  other i
                  (ActualInitializationRun.followerCarryAtBlockBoundary p rate
                    (Bandits.Support.ActualFollowerCalendarContinuity.calendarBlockIndex u)
                    (Bandits.Support.ActualFollowerCalendarContinuity.calendarFollowerAfter
                      rate other otherRewards C_star C_h i u)) := by
            calc
              _ = ActualInitializationRun.beginFollowerBlock p rate
                  (Bandits.Support.ActualFollowerCalendarContinuity.calendarBlockIndex uNext)
                  other i
                  (ActualInitializationRun.followerCarryAtBlockBoundary p rate
                    (Bandits.Support.ActualFollowerCalendarContinuity.calendarBlockIndex u)
                    (Bandits.Support.ActualFollowerCalendarContinuity.calendarFollowerAfter
                      rate source rewards C_star C_h i u)) := hbegin
              _ = _ := congrArg
                (ActualInitializationRun.beginFollowerBlock p rate
                  (Bandits.Support.ActualFollowerCalendarContinuity.calendarBlockIndex uNext)
                  other i) hcarry
          exact hleft.trans (hbeginRight.trans hright.symm)

  have hbefore := hbeforePrefix t.val le_rfl
  obtain ⟨hstateLeft, _, _, harmLeft⟩ :=
    Bandits.Support.ActualFollowerCalendarContinuity.calendar_record_localCode
      rate source rewards C_star C_h i t
  obtain ⟨hstateRight, _, _, harmRight⟩ :=
    Bandits.Support.ActualFollowerCalendarContinuity.calendar_record_localCode
      rate other otherRewards C_star C_h i t
  let x := actualCalendarLocalInput
    (rate := rate) (C_star := C_star) (C_h := C_h)
    (worldSource := source) (worldRewards := rewards)
    (follower := i) (u := t) (hstate := hstateLeft)
  let x' := actualCalendarLocalInput
    (rate := rate) (C_star := C_star) (C_h := C_h)
    (worldSource := other) (worldRewards := otherRewards)
    (follower := i) (u := t) (hstate := hstateRight)
  have hlocal : ActualPostlaunchFollowerMeasurability.localFollower x =
      ActualPostlaunchFollowerMeasurability.localFollower x' := by
    simp [x, x', actualCalendarLocalInput,
      ActualPostlaunchFollowerMeasurability.localInputOfComponents,
      ActualPostlaunchFollowerMeasurability.localFollower, hbefore]
  have hx : ActualPostlaunchFollowerMeasurability.localSource x = source := by
    simp [x, actualCalendarLocalInput,
      ActualPostlaunchFollowerMeasurability.localInputOfComponents,
      ActualPostlaunchFollowerMeasurability.localSource]
  have hx' : ActualPostlaunchFollowerMeasurability.localSource x' = other := by
    simp [x', actualCalendarLocalInput,
      ActualPostlaunchFollowerMeasurability.localInputOfComponents,
      ActualPostlaunchFollowerMeasurability.localSource]
  have hscalarAtTime := congrFun hround t
  have hscalar : BootstrapPhysicalInput.playerRoundScalarAt p source.2
      (PublicDiscreteDraws.followerPlayer p.two_le_m i)
      (ActualPostlaunchFollowerMeasurability.localTime
        (Bandits.Support.ActualFollowerCalendarContinuity.calendarBlockIndex t)
        (Bandits.Support.ActualFollowerCalendarContinuity.calendarCursor t)
        (Bandits.Support.ActualFollowerCalendarContinuity.calendarCursor_lt_blockLength t)) =
    BootstrapPhysicalInput.playerRoundScalarAt p other.2
      (PublicDiscreteDraws.followerPlayer p.two_le_m i)
      (ActualPostlaunchFollowerMeasurability.localTime
        (Bandits.Support.ActualFollowerCalendarContinuity.calendarBlockIndex t)
        (Bandits.Support.ActualFollowerCalendarContinuity.calendarCursor t)
        (Bandits.Support.ActualFollowerCalendarContinuity.calendarCursor_lt_blockLength t)) := by
    rw [Bandits.Support.ActualFollowerCalendarContinuity.calendarLocalTime_eq_time t]
    exact hscalarAtTime
  have hprepCoordinates := preparationCoordinates_eq_of_public_and_round
    (rate := rate)
    (hcursor := Bandits.Support.ActualFollowerCalendarContinuity.calendarCursor_lt_blockLength t)
    (follower := i) (worldSource := source) (worldOther := other)
    (x := x) (x' := x') (hx := hx) (hx' := hx')
    (hfollower := hlocal) (hpublic := hpublic) (hround := hscalar)
  have hprepared :=
    ActualPostlaunchFollowerPreparationLocality.preparedCodeOnCursor_eq_of_own_coordinates
      (Bandits.Support.ActualFollowerCalendarContinuity.calendarCursor_lt_blockLength t)
      i x x' hlocal hprepCoordinates
  have harmLeft' : actualPlayerArm
      (rate := rate) (C_star := C_star) (C_h := C_h)
      (worldSource := source) (worldRewards := rewards) (follower := i) (u := t) =
      ActualInitializationPreparationMeasurability.preparedFollowerCodeArm
        (ActualPostlaunchFollowerMeasurability.preparedCodeOnCursor
          (Bandits.Support.ActualFollowerCalendarContinuity.calendarCursor_lt_blockLength t)
          i x) := by
    simpa [actualPlayerArm, actualPlayerFeedback, x, actualCalendarLocalInput] using harmLeft
  have harmRight' : actualPlayerArm
      (rate := rate) (C_star := C_star) (C_h := C_h)
      (worldSource := other) (worldRewards := otherRewards) (follower := i) (u := t) =
      ActualInitializationPreparationMeasurability.preparedFollowerCodeArm
        (ActualPostlaunchFollowerMeasurability.preparedCodeOnCursor
          (Bandits.Support.ActualFollowerCalendarContinuity.calendarCursor_lt_blockLength t)
          i x') := by
    simpa [actualPlayerArm, actualPlayerFeedback, x', actualCalendarLocalInput] using harmRight
  refine ⟨hbefore, ?_⟩
  change actualPlayerArm
      (rate := rate) (C_star := C_star) (C_h := C_h)
      (worldSource := source) (worldRewards := rewards) (follower := i) (u := t) =
    actualPlayerArm
      (rate := rate) (C_star := C_star) (C_h := C_h)
      (worldSource := other) (worldRewards := otherRewards) (follower := i) (u := t)
  exact harmLeft'.trans
    ((congrArg ActualInitializationPreparationMeasurability.preparedFollowerCodeArm
      hprepared).trans harmRight'.symm)

end Bandits.Support.ActualCompleteFollowerOwnHistoryLocality

end
