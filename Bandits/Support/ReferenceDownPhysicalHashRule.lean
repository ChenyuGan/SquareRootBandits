/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceAffineDispatchPairInvariance

/-!
# Actual DOWN physical affine hash rule

Sources: sources/zip4/manuscript/05_binary_transport.tex:7-42,74-124 and
sources/zip4/manuscript/appendix_a_local_protocol.tex:112-137.

This module proves the DOWN rule from the actual accepted dispatcher, checked
coordinator choice, follower PREPARE, and finite collision feedback. It keeps
the original complete round input and changes only its selected DOWN affine
pair. No statement here supplies a fresh conditional law on a physical run or
proves pre-pair measurability, chronology, freshness, or decoder-tail claims.
-/

@[expose] public section

open scoped BigOperators ENNReal Classical

namespace Bandits.Support.ReferenceDownPhysicalHashRule

open ConstructorDimensions
open AffineChannelLaw
open ReferenceActiveAffinePositiveTest
open ReferenceActivePhysicalStep
open ReferenceAffineDispatchPairInvariance
open AdaptiveAffineBatchTail

variable {p : Parameters} {rate : ReferenceActivePhysicalStep.RateInput p}

/-- The actual current DOWN pair in the original selected row. -/
noncomputable def originalDownSample (x : ReferenceActivePhysicalStep.RoundInput p rate) :
    Sample (AffineBatchDecoder.width p) :=
  (x.row.2 x.time).2 (0, ReferenceActivePhysicalStep.upSenderIndex x)

/-- The genuine zero coefficient word in the existing binary word carrier. -/
def zeroCoefficient : Word (AffineBatchDecoder.width p) := fun _ => 0

theorem affineHash_zeroCoefficient (s : Sample (AffineBatchDecoder.width p)) :
    affineHash s zeroCoefficient = s.2 := by
  simp [zeroCoefficient, AffineChannelLaw.affineHash, AffineChannelLaw.dotProduct]

/-- With the genuine zero coefficient vector as the sample coefficient, the
offset bit is the affine hash for every word. -/
theorem affineHash_zeroCoefficientSample (bit : Bit)
    (word : Word (AffineBatchDecoder.width p)) :
    affineHash (zeroCoefficient, bit) word = bit := by
  simp [zeroCoefficient, AffineChannelLaw.affineHash,
    AffineChannelLaw.dotProduct]

/-- The literal selected-DOWN hash argument, with a constant zero branch when
the actual checked dispatcher sends no DOWN word. -/
noncomputable def downHashBit (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (s : Sample (AffineBatchDecoder.width p)) : Bit :=
  match ReferenceActiveAffinePositiveTest.downSent x with
  | none => 0
  | some w => affineHash s w

/-- The actual positive test at the concrete zero-coefficient pair with offset
bit; this definition is used to encode the rule itself. -/
noncomputable def downRule (x : ReferenceActivePhysicalStep.RoundInput p rate) (bit : Bit) : Bool :=
  ReferenceActiveAffinePositiveTest.downPositive
    (ReferenceActiveAffinePositiveTest.replaceCurrentPair x 0 (zeroCoefficient, bit))

private theorem coordinatorArmChoiceCore_eq_of_no_selected_down
    (payload : AssignmentStartPayload.Input p rate.eta)
    (pending : Finset (ActiveRoundActions.Follower p.m))
    (cutoff : Option (CoordinatorLocalArmChoice.Cutoff p)) (time : Fin p.T)
    (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ)
    (control otherControl : ContinuousLearningRows.TimeControl p)
    (hscalar : control.1 = otherControl.1)
    (hno : ¬ (PublicDiscreteDraws.slotDraw control.1 = PublicDiscreteDraws.downSlot ∧
      PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K control.1 ∈ pending)) :
    CoordinatorLocalArmChoice.coordinatorArmChoiceCore payload pending cutoff time weights control =
      CoordinatorLocalArmChoice.coordinatorArmChoiceCore payload pending cutoff time weights otherControl := by
  rcases control with ⟨scalars, samples⟩
  rcases otherControl with ⟨otherScalars, otherSamples⟩
  change scalars = otherScalars at hscalar
  subst otherScalars
  unfold CoordinatorLocalArmChoice.coordinatorArmChoiceCore
  dsimp only
  split
  · split
    · rfl
    · split
      · rfl
      · by_cases hbranch : PublicDiscreteDraws.slotDraw scalars = PublicDiscreteDraws.downSlot ∧
          PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K scalars ∈ pending
        · exact False.elim (hno hbranch)
        · rfl
  · rfl

/-- On a real selected DOWN word, the checked selected choice is exactly its
literal SendArm output, with the current affine hash as its only varying input.
-/
theorem coordinatorAction_eq_sendArm_of_downSent
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (word : Word (AffineBatchDecoder.width p))
    (hsent : ReferenceActiveAffinePositiveTest.downSent x = some word) :
    (ReferenceActivePhysicalStep.prepare x).arms.actions
        (ActiveRoundActions.coordinator p.two_le_m) =
      ActiveRoundActions.sendArm
        (affineHash ((x.row.2 x.time).2
          (0, ReferenceActivePhysicalStep.upSenderIndex x)) word)
        ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K (x.row.2 x.time).1).val
          (ActiveRoundActions.coordinator p.two_le_m))
        ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K (x.row.2 x.time).1).val
          (PublicDiscreteDraws.followerPlayer p.two_le_m
            (ReferenceActivePhysicalStep.upSenderIndex x))) := by
  let i := ReferenceActivePhysicalStep.upSenderIndex x
  let dispatched := ReferenceActivePhysicalStep.dispatch x
  have hsent' : ReferenceDownReception.expectedDownFlatWord dispatched.downView i x.row x.time =
      some word := by
    simpa only [ReferenceActiveAffinePositiveTest.downSent, dispatched, i] using hsent
  cases hselection : dispatched.selection with
  | none =>
      simp only [ReferenceActivePhysicalStep.DispatchCut.downView, hselection,
        Option.map_none] at hsent'
      cases hsent'
  | some selected =>
      have hdecoded :
          CoordinatorLocalArmChoice.coordinatorArmChoice selected.view.payload
              selected.view.pendingAtChoice selected.view.cutoff x.time
              selected.view.complementWeights x.row ≠ none ∧
            ReferenceDownReception.selectedDownSenderBranch selected.view i x.row x.time ∧
            CoordinatorLocalArmChoice.storedDownFlatWord selected.view.payload i = word := by
        have hsentView : ReferenceDownReception.expectedDownFlatWord
            (some selected.view) i x.row x.time = some word := by
          simpa only [ReferenceActiveAffinePositiveTest.downSent, dispatched,
            ReferenceActivePhysicalStep.DispatchCut.downView, hselection, i,
            Option.map_some] using hsent
        unfold ReferenceDownReception.expectedDownFlatWord at hsentView
        dsimp only at hsentView
        split_ifs at hsentView with hcondition
        · have hword : CoordinatorLocalArmChoice.storedDownFlatWord
              selected.view.payload i = word := by
            simpa only [AffineBatchDecoder.width, ContinuousLearningRows.B] using
              Option.some.inj hsentView
          exact ⟨hcondition.1, hcondition.2, hword⟩
      have hbranch := hdecoded.2.1
      have hselected : dispatched.selection = some selected := hselection
      have hword := hdecoded.2.2
      have harm := ReferenceActivePhysicalStep.action_eq_down_sendArm
        (ReferenceActivePhysicalStep.prepare x) selected hselected i hbranch
      rw [harm]
      dsimp only [CoordinatorLocalArmChoice.currentDownHash,
        CoordinatorLocalArmChoice.downChannel]
      rw [hword]

private theorem coordinatorAction_replace_none
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (s : Sample (AffineBatchDecoder.width p))
    (hnone : ReferenceActiveAffinePositiveTest.downSent x = none) :
    (ReferenceActivePhysicalStep.prepare
        (ReferenceActiveAffinePositiveTest.replaceCurrentPair x 0 s)).arms.actions
        (ActiveRoundActions.coordinator p.two_le_m) =
      (ReferenceActivePhysicalStep.prepare x).arms.actions
        (ActiveRoundActions.coordinator p.two_le_m) := by
  let y := ReferenceActiveAffinePositiveTest.replaceCurrentPair x 0 s
  let original := ReferenceActivePhysicalStep.dispatch x
  let changed := ReferenceActivePhysicalStep.dispatch y
  have hview := ReferenceAffineDispatchPairInvariance.downView_replace x 0 s
  cases hselection : original.selection with
  | none =>
      have hchanged : changed.selection = none := by
        have hpresent : changed.selection.isSome = false := by
          rw [ReferenceAffineDispatchPairInvariance.selection_isSome_replace]
          simp [original, hselection]
        cases hchanged : changed.selection with
        | none => rfl
        | some selected =>
            simp [hchanged] at hpresent
      change changed.arm = original.arm
      simp only [ReferenceActivePhysicalStep.DispatchCut.arm, hchanged, hselection]
  | some originalSelection =>
      have hnoBranch : ¬ ReferenceDownReception.selectedDownSenderBranch
          originalSelection.view (ReferenceActivePhysicalStep.upSenderIndex x) x.row x.time := by
        have hwordNone : ReferenceDownReception.expectedDownFlatWord
            (some originalSelection.view) (ReferenceActivePhysicalStep.upSenderIndex x)
            x.row x.time = none := by
          simpa [ReferenceActiveAffinePositiveTest.downSent, original,
            ReferenceActivePhysicalStep.DispatchCut.downView, hselection] using hnone
        intro hbranch
        have hword := ReferenceActivePhysicalStep.Selection.expected_down_word
          originalSelection (ReferenceActivePhysicalStep.upSenderIndex x) hbranch
        rw [hwordNone] at hword
        cases hword
      have hchangedSome : ∃ selected, changed.selection = some selected := by
        have hpresent : changed.selection.isSome = true := by
          rw [ReferenceAffineDispatchPairInvariance.selection_isSome_replace]
          simp [original, hselection]
        cases hchanged : changed.selection with
        | none => simp [hchanged] at hpresent
        | some selected => exact ⟨selected, rfl⟩
      rcases hchangedSome with ⟨changedSelection, hchanged⟩
      have hselectionView : changedSelection.view = originalSelection.view := by
        change changed.selection.map ReferenceActivePhysicalStep.Selection.view =
          original.selection.map ReferenceActivePhysicalStep.Selection.view at hview
        rw [hchanged, hselection] at hview
        have hview' : some changedSelection.view = some originalSelection.view := hview
        exact Option.some.inj hview'
      have htime : y.time = x.time :=
        (ReferenceActiveAffinePositiveTest.replaceCurrentPair_fields x 0 s).2.2.1
      have hchoiceChanged := changedSelection.choice_eq
      rw [htime, hselectionView] at hchoiceChanged
      have hchoiceOriginal := originalSelection.choice_eq
      change CoordinatorLocalArmChoice.coordinatorArmChoiceCore
          originalSelection.view.payload originalSelection.view.pendingAtChoice
          originalSelection.view.cutoff x.time originalSelection.view.complementWeights
          (y.row.2 y.time) = some changedSelection.arm at hchoiceChanged
      change CoordinatorLocalArmChoice.coordinatorArmChoiceCore
          originalSelection.view.payload originalSelection.view.pendingAtChoice
          originalSelection.view.cutoff x.time originalSelection.view.complementWeights
          (x.row.2 x.time) = some originalSelection.arm at hchoiceOriginal
      have hnoCore : ¬ (PublicDiscreteDraws.slotDraw (x.row.2 x.time).1 =
          PublicDiscreteDraws.downSlot ∧
          PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
            (x.row.2 x.time).1 ∈ originalSelection.view.pendingAtChoice) := by
        intro hcoreBranch
        apply hnoBranch
        exact ⟨hcoreBranch.1, (ReferenceActiveAffinePositiveTest.upSenderIndex_eq_draw x).symm,
          hcoreBranch.2⟩
      have hslice : (y.row.2 y.time).1 = (x.row.2 x.time).1 := by
        rw [htime]
        exact ReferenceActiveAffinePositiveTest.replaceCurrentPair_current_slice x 0 s
      have hnoChanged : ¬ (PublicDiscreteDraws.slotDraw (y.row.2 y.time).1 =
          PublicDiscreteDraws.downSlot ∧
          PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
            (y.row.2 y.time).1 ∈ originalSelection.view.pendingAtChoice) := by
        intro h
        rw [hslice] at h
        exact hnoCore h
      have hcore := coordinatorArmChoiceCore_eq_of_no_selected_down
        originalSelection.view.payload originalSelection.view.pendingAtChoice
        originalSelection.view.cutoff x.time originalSelection.view.complementWeights
        (y.row.2 y.time) (x.row.2 x.time)
        hslice hnoChanged
      rw [hcore, hchoiceOriginal] at hchoiceChanged
      have harm : changedSelection.arm = originalSelection.arm :=
        (Option.some.inj hchoiceChanged).symm
      change changed.arm = original.arm
      simpa only [ReferenceActivePhysicalStep.DispatchCut.arm, changed, original,
        hchanged, hselection] using harm

private theorem coordinatorAction_replace_eq_of_hash_eq
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (s t : Sample (AffineBatchDecoder.width p))
    (hhash : downHashBit x s = downHashBit x t) :
    (ReferenceActivePhysicalStep.prepare
        (ReferenceActiveAffinePositiveTest.replaceCurrentPair x 0 s)).arms.actions
        (ActiveRoundActions.coordinator p.two_le_m) =
      (ReferenceActivePhysicalStep.prepare
        (ReferenceActiveAffinePositiveTest.replaceCurrentPair x 0 t)).arms.actions
        (ActiveRoundActions.coordinator p.two_le_m) := by
  cases hsent : ReferenceActiveAffinePositiveTest.downSent x with
  | none =>
      have hs := coordinatorAction_replace_none x s hsent
      have ht := coordinatorAction_replace_none x t hsent
      exact hs.trans ht.symm
  | some word =>
      have hsentS : ReferenceActiveAffinePositiveTest.downSent
          (ReferenceActiveAffinePositiveTest.replaceCurrentPair x 0 s) = some word := by
        calc
          _ = ReferenceActiveAffinePositiveTest.downSent x :=
            ReferenceAffineDispatchPairInvariance.downSent_replace x 0 s
          _ = some word := hsent
      have hsentT : ReferenceActiveAffinePositiveTest.downSent
          (ReferenceActiveAffinePositiveTest.replaceCurrentPair x 0 t) = some word := by
        calc
          _ = ReferenceActiveAffinePositiveTest.downSent x :=
            ReferenceAffineDispatchPairInvariance.downSent_replace x 0 t
          _ = some word := hsent
      have hhash' : affineHash s word = affineHash t word := by
        simpa only [downHashBit, hsent] using hhash
      have hcoordS := coordinatorAction_eq_sendArm_of_downSent
        (ReferenceActiveAffinePositiveTest.replaceCurrentPair x 0 s) word hsentS
      have hcoordT := coordinatorAction_eq_sendArm_of_downSent
        (ReferenceActiveAffinePositiveTest.replaceCurrentPair x 0 t) word hsentT
      rw [(ReferenceActiveAffinePositiveTest.replaceCurrentPair_fields x 0 s).2.2.1,
        ReferenceActiveAffinePositiveTest.upSenderIndex_replace x 0 s,
        ReferenceActiveAffinePositiveTest.replaceCurrentPair_sample x 0 s] at hcoordS
      rw [ReferenceActiveAffinePositiveTest.replaceCurrentPair_current_slice x 0 s] at hcoordS
      rw [(ReferenceActiveAffinePositiveTest.replaceCurrentPair_fields x 0 t).2.2.1,
        ReferenceActiveAffinePositiveTest.upSenderIndex_replace x 0 t,
        ReferenceActiveAffinePositiveTest.replaceCurrentPair_sample x 0 t] at hcoordT
      rw [ReferenceActiveAffinePositiveTest.replaceCurrentPair_current_slice x 0 t] at hcoordT
      rw [hcoordS, hcoordT]
      exact congrArg (fun bit : Bit => ActiveRoundActions.sendArm bit
        ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K (x.row.2 x.time).1).val
          (ActiveRoundActions.coordinator p.two_le_m))
        ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K (x.row.2 x.time).1).val
          (PublicDiscreteDraws.followerPlayer p.two_le_m
            (ReferenceActivePhysicalStep.upSenderIndex x))))
        (by simpa only [AffineBatchDecoder.width, ContinuousLearningRows.B] using hhash')

/-- For a fixed original round, the whole actual PREPARE action profile after
replacing its DOWN pair depends on the replacement only through the sent-word
hash. -/
theorem prepareActions_replace_down_eq_of_same_hash
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (s t : Sample (AffineBatchDecoder.width p))
    (hhash : downHashBit x s = downHashBit x t) :
    (ReferenceActivePhysicalStep.prepare
        (ReferenceActiveAffinePositiveTest.replaceCurrentPair x 0 s)).arms.actions =
      (ReferenceActivePhysicalStep.prepare
        (ReferenceActiveAffinePositiveTest.replaceCurrentPair x 0 t)).arms.actions := by
  funext player
  rcases ActiveRoundActions.player_cases p.two_le_m player with hcoord | ⟨i, hplayer⟩
  · simpa only [hcoord] using coordinatorAction_replace_eq_of_hash_eq x s t hhash
  · calc
      (ReferenceActivePhysicalStep.prepare
          (ReferenceActiveAffinePositiveTest.replaceCurrentPair x 0 s)).arms.actions player =
          (ReferenceActivePhysicalStep.prepare x).arms.actions
            (PublicDiscreteDraws.followerPlayer p.two_le_m i) := by
            simpa only [hplayer] using
              ReferenceActiveAffinePositiveTest.follower_arm_replace_down x s i
      _ = (ReferenceActivePhysicalStep.prepare
          (ReferenceActiveAffinePositiveTest.replaceCurrentPair x 0 t)).arms.actions player := by
            simpa only [hplayer] using
              (ReferenceActiveAffinePositiveTest.follower_arm_replace_down x t i).symm

/-- With no actual DOWN word, the entire PREPARE profile is independent of the
whole replacement pair, including live-empty priority and all rejection paths.
-/
theorem prepareActions_replace_down_eq_of_no_word
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (s t : Sample (AffineBatchDecoder.width p))
    (hnone : ReferenceActiveAffinePositiveTest.downSent x = none) :
    (ReferenceActivePhysicalStep.prepare
        (ReferenceActiveAffinePositiveTest.replaceCurrentPair x 0 s)).arms.actions =
      (ReferenceActivePhysicalStep.prepare
        (ReferenceActiveAffinePositiveTest.replaceCurrentPair x 0 t)).arms.actions := by
  apply prepareActions_replace_down_eq_of_same_hash
  simp [downHashBit, hnone]

private theorem downPositive_replace_eq_of_same_hash
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (s t : Sample (AffineBatchDecoder.width p))
    (hhash : downHashBit x s = downHashBit x t) :
    ReferenceActiveAffinePositiveTest.downPositive
        (ReferenceActiveAffinePositiveTest.replaceCurrentPair x 0 s) =
      ReferenceActiveAffinePositiveTest.downPositive
        (ReferenceActiveAffinePositiveTest.replaceCurrentPair x 0 t) := by
  let ys := ReferenceActiveAffinePositiveTest.replaceCurrentPair x 0 s
  let yt := ReferenceActiveAffinePositiveTest.replaceCurrentPair x 0 t
  have hactions := prepareActions_replace_down_eq_of_same_hash x s t hhash
  have htimeS : ys.time = x.time := (ReferenceActiveAffinePositiveTest.replaceCurrentPair_fields x 0 s).2.2.1
  have htimeT : yt.time = x.time := (ReferenceActiveAffinePositiveTest.replaceCurrentPair_fields x 0 t).2.2.1
  have hrewardsS : ys.rewards = x.rewards := (ReferenceActiveAffinePositiveTest.replaceCurrentPair_fields x 0 s).2.2.2
  have hrewardsT : yt.rewards = x.rewards := (ReferenceActiveAffinePositiveTest.replaceCurrentPair_fields x 0 t).2.2.2
  have hfeedback :
      ReferenceActiveFeedbackCut.collisionFeedbackVector
        (ReferenceActivePhysicalStep.prepare ys).arms.actions ys.time ys.rewards
        (PublicDiscreteDraws.followerPlayer p.two_le_m
          (ReferenceActivePhysicalStep.upSenderIndex ys)) =
      ReferenceActiveFeedbackCut.collisionFeedbackVector
        (ReferenceActivePhysicalStep.prepare yt).arms.actions yt.time yt.rewards
        (PublicDiscreteDraws.followerPlayer p.two_le_m
          (ReferenceActivePhysicalStep.upSenderIndex yt)) := by
    rw [ReferenceActiveAffinePositiveTest.upSenderIndex_replace x 0 s,
      ReferenceActiveAffinePositiveTest.upSenderIndex_replace x 0 t,
      htimeS, htimeT, hrewardsS, hrewardsT]
    exact congrArg (fun actions : FiniteBanditModel.ActionProfile p.m p.K =>
      ReferenceActiveFeedbackCut.collisionFeedbackVector actions x.time x.rewards
        (PublicDiscreteDraws.followerPlayer p.two_le_m
          (ReferenceActivePhysicalStep.upSenderIndex x))) hactions
  have hfeedback' :
      ReferenceActiveFeedbackCut.collisionFeedbackVector
        (ReferenceActivePhysicalStep.prepare
          (ReferenceActiveAffinePositiveTest.replaceCurrentPair x 0 s)).arms.actions x.time x.rewards
        (PublicDiscreteDraws.followerPlayer p.two_le_m
          (ReferenceActivePhysicalStep.upSenderIndex x)) =
      ReferenceActiveFeedbackCut.collisionFeedbackVector
        (ReferenceActivePhysicalStep.prepare
          (ReferenceActiveAffinePositiveTest.replaceCurrentPair x 0 t)).arms.actions x.time x.rewards
        (PublicDiscreteDraws.followerPlayer p.two_le_m
          (ReferenceActivePhysicalStep.upSenderIndex x)) := by
    simpa only [ys, yt,
      ReferenceActiveAffinePositiveTest.upSenderIndex_replace,
      htimeS, htimeT, hrewardsS, hrewardsT,
      PublicDiscreteDraws.followerCount] using hfeedback
  rw [ReferenceActiveAffinePositiveTest.downPositive_eq_gate_feedback,
    ReferenceActiveAffinePositiveTest.downPositive_eq_gate_feedback,
    ReferenceActiveAffinePositiveTest.downGate_replace x 0 s,
    ReferenceActiveAffinePositiveTest.downGate_replace x 0 t,
    ReferenceActiveAffinePositiveTest.upSenderIndex_replace x 0 s,
    ReferenceActiveAffinePositiveTest.upSenderIndex_replace x 0 t,
    htimeS, htimeT, hrewardsS, hrewardsT]
  rw [hfeedback']

/-- The literal positive-test rule factors through the actual sent DOWN word
and its affine hash, with an honest zero-word encoding for the no-send branch.
-/
theorem downPositive_replace_eq_downRule
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (s : Sample (AffineBatchDecoder.width p)) :
    ReferenceActiveAffinePositiveTest.downPositive
        (ReferenceActiveAffinePositiveTest.replaceCurrentPair x 0 s) =
      downRule x (downHashBit x s) := by
  cases hsent : ReferenceActiveAffinePositiveTest.downSent x with
  | none =>
      have hhash : downHashBit x s = downHashBit x (zeroCoefficient, 0) := by
        simp [downHashBit, hsent]
      rw [downPositive_replace_eq_of_same_hash x s (zeroCoefficient, 0) hhash]
      simp [downRule, downHashBit, hsent]
  | some word =>
      have hhash : downHashBit x s =
          downHashBit x (zeroCoefficient, affineHash s word) := by
        simp [downHashBit, hsent, affineHash_zeroCoefficientSample]
      rw [downPositive_replace_eq_of_same_hash x s
        (zeroCoefficient, affineHash s word) hhash]
      simp [downRule, downHashBit, hsent]

/-- Replacing the actual DOWN coordinate by its own original pair recovers the
entire round input, not just its selected row projection. -/
theorem replaceCurrentPair_originalDownSample
    (x : ReferenceActivePhysicalStep.RoundInput p rate) :
    ReferenceActiveAffinePositiveTest.replaceCurrentPair x 0 (originalDownSample x) = x := by
  cases x with
  | mk state rows selected time active rewards =>
      apply congrArg (fun rows' : CompletePublicTable.CompleteRows p =>
        ReferenceActivePhysicalStep.RoundInput.mk state rows' selected time active rewards)
      funext rowIndex
      by_cases hrow : rowIndex = selected
      · subst rowIndex
        apply Prod.ext
        · simp [ReferenceActivePhysicalStep.RoundInput.row]
        · funext calendarTime
          by_cases htime : calendarTime = time
          · subst calendarTime
            apply Prod.ext
            · simp [ReferenceActivePhysicalStep.RoundInput.row]
            · funext channel
              by_cases hchannel : channel = (0, ReferenceActivePhysicalStep.upSenderIndex
                  (ReferenceActivePhysicalStep.RoundInput.mk state rows selected time active rewards))
              · subst channel
                simp [originalDownSample, ReferenceActivePhysicalStep.RoundInput.row]
              · simp [originalDownSample, ReferenceActivePhysicalStep.RoundInput.row]
          · simp [ReferenceActivePhysicalStep.RoundInput.row,
              Function.update_of_ne htime]
      · simp [ReferenceActivePhysicalStep.RoundInput.row,
          Function.update_of_ne hrow]

/-- The actual input is recovered at its own pair, and its positive test is the
literal DOWN rule evaluated at that pair's actual affine hash. -/
theorem downPositive_eq_downRule_at_original_pair
    (x : ReferenceActivePhysicalStep.RoundInput p rate) :
    ReferenceActiveAffinePositiveTest.downPositive x =
      downRule x (downHashBit x (originalDownSample x)) := by
  calc
    ReferenceActiveAffinePositiveTest.downPositive x =
        ReferenceActiveAffinePositiveTest.downPositive
          (ReferenceActiveAffinePositiveTest.replaceCurrentPair x 0 (originalDownSample x)) :=
      congrArg ReferenceActiveAffinePositiveTest.downPositive
        (replaceCurrentPair_originalDownSample x).symm
    _ = downRule x (downHashBit x (originalDownSample x)) :=
      downPositive_replace_eq_downRule x (originalDownSample x)

private theorem declaredPrepare_arm_eq_tuple_of_ordinary_unoccupied_down
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (activation : ReferencePrelaunchFollower.Activation p) (time : Fin p.T)
    (active : activation.val ≤ time.val + 1)
    (input : DeclaredFollowerLocalRound.LocalConfiguration p rate)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hconfiguration : (DeclaredFollowerLocalRound.prepare rate i row activation time active input).configuration =
      .ordinary state memory)
    (hunoccupied : state.status = .unoccupied)
    (hdown : PublicDiscreteDraws.slotDraw (row.2 time).1 = PublicDiscreteDraws.downSlot) :
    (DeclaredFollowerLocalRound.prepare rate i row activation time active input).arm =
      (OrderedTupleSampler.sample p.two_le_m p.m_lt_K (row.2 time).1).val
        (PublicDiscreteDraws.followerPlayer p.two_le_m i) := by
  cases hinput : input with
  | dagger =>
      simp [DeclaredFollowerLocalRound.prepare, hinput] at hconfiguration
  | ordinary oldState oldMemory =>
      cases hstart : ActiveFollowerLifecycle.startRound rate.eta time oldState oldMemory with
      | error reason =>
          simp [DeclaredFollowerLocalRound.prepare, hinput, hstart] at hconfiguration
      | ok result =>
          rcases result with ⟨choiceState, choiceMemory⟩
          cases hoff : ActiveFollowerQueueOperation.checkedUpOffer rate.eta i row activation time
              choiceState with
          | failure =>
              simp [DeclaredFollowerLocalRound.prepare, hinput, hstart, hoff] at hconfiguration
          | noOffer =>
              cases hchoice : ActiveFollowerArmChoice.followerArmChoice choiceState row time i none with
              | none =>
                  simp [DeclaredFollowerLocalRound.prepare, hinput, hstart, hoff,
                    hchoice] at hconfiguration
              | some arm =>
                  have hstates : choiceState = state ∧ choiceMemory = memory := by
                    simp [DeclaredFollowerLocalRound.prepare, hinput, hstart, hoff,
                      hchoice] at hconfiguration
                    exact ⟨hconfiguration.1, hconfiguration.2⟩
                  have hchoiceUnoccupied : choiceState.status = .unoccupied := by
                    rw [hstates.1]
                    exact hunoccupied
                  have hnotdata : PublicDiscreteDraws.slotDraw (row.2 time).1 ≠
                      PublicDiscreteDraws.dataSlot := by rw [hdown]; decide
                  have hnotselected : ¬ (PublicDiscreteDraws.slotDraw (row.2 time).1 =
                      PublicDiscreteDraws.upSlot ∧
                      PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
                        (row.2 time).1 = i) := by
                    rintro ⟨hslot, _⟩
                    rw [hdown] at hslot
                    exact (by decide : PublicDiscreteDraws.downSlot ≠
                      PublicDiscreteDraws.upSlot) hslot
                  have htuple := ActiveFollowerArmChoice.followerArmChoiceCore_unoccupied_other
                    choiceState (row.2 time) i none hchoiceUnoccupied hnotdata hnotselected
                  have htuple' : ActiveFollowerArmChoice.followerArmChoice
                      choiceState row time i none =
                      some ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K
                        (row.2 time).1).val (PublicDiscreteDraws.followerPlayer p.two_le_m i)) := by
                    simpa only [ActiveFollowerArmChoice.followerArmChoice] using htuple
                  rw [hchoice] at htuple'
                  have hprepare := (DeclaredFollowerLocalRound.prepare_no_offer_arm_equation
                    rate i row activation time active oldState choiceState
                    oldMemory choiceMemory hstart hoff).2
                    arm hchoice
                  rw [hprepare.1]
                  exact (by
                    simpa only [PublicDiscreteDraws.followerCount] using
                      Option.some.inj htuple')
          | offer offered =>
              cases hchoice : ActiveFollowerArmChoice.followerArmChoice choiceState row time i
                  (some offered) with
              | none =>
                  simp [DeclaredFollowerLocalRound.prepare, hinput, hstart, hoff,
                    hchoice] at hconfiguration
              | some arm =>
                  have hstates : choiceState = state ∧ choiceMemory = memory := by
                    simp [DeclaredFollowerLocalRound.prepare, hinput, hstart, hoff,
                      hchoice] at hconfiguration
                    exact ⟨hconfiguration.1, hconfiguration.2⟩
                  have hchoiceUnoccupied : choiceState.status = .unoccupied := by
                    rw [hstates.1]
                    exact hunoccupied
                  have hnotdata : PublicDiscreteDraws.slotDraw (row.2 time).1 ≠
                      PublicDiscreteDraws.dataSlot := by rw [hdown]; decide
                  have hnotselected : ¬ (PublicDiscreteDraws.slotDraw (row.2 time).1 =
                      PublicDiscreteDraws.upSlot ∧
                      PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
                        (row.2 time).1 = i) := by
                    rintro ⟨hslot, _⟩
                    rw [hdown] at hslot
                    exact (by decide : PublicDiscreteDraws.downSlot ≠
                      PublicDiscreteDraws.upSlot) hslot
                  have htuple := ActiveFollowerArmChoice.followerArmChoiceCore_unoccupied_other
                    choiceState (row.2 time) i (some offered) hchoiceUnoccupied hnotdata hnotselected
                  have htuple' : ActiveFollowerArmChoice.followerArmChoice
                      choiceState row time i (some offered) =
                      some ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K
                        (row.2 time).1).val (PublicDiscreteDraws.followerPlayer p.two_le_m i)) := by
                    simpa only [ActiveFollowerArmChoice.followerArmChoice] using htuple
                  rw [hchoice] at htuple'
                  have hprepare := (DeclaredFollowerLocalRound.prepare_offer_arm_equation
                    rate i row activation time active oldState choiceState
                    oldMemory choiceMemory hstart offered hoff).2
                    arm hchoice
                  rw [hprepare.1]
                  exact (by
                    simpa only [PublicDiscreteDraws.followerCount] using
                      Option.some.inj htuple')

/-- A true actual DOWN gate exposes the checked ordinary receiver PREPARE and
its unoccupied, selected-DOWN receiver conditions. -/
theorem downGate_true_receiver_prepared
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (hgate : ReferenceActiveAffinePositiveTest.downGate x = true) :
    ∃ state memory,
      ((ReferenceActivePhysicalStep.prepare x).followers.followers
        (ReferenceActivePhysicalStep.upSenderIndex x)).configuration = .ordinary state memory ∧
      state.status = .unoccupied ∧
      ActiveFollowerDownAcceptance.downSelected p
        (ReferenceActivePhysicalStep.upSenderIndex x) x.row x.time := by
  let i := ReferenceActivePhysicalStep.upSenderIndex x
  let prepared := ReferenceActivePhysicalStep.prepare x
  unfold ReferenceActiveAffinePositiveTest.downGate at hgate
  dsimp only [i, prepared] at hgate
  cases hconfiguration : ((ReferenceActivePhysicalStep.prepare x).followers.followers
      (ReferenceActivePhysicalStep.upSenderIndex x)).configuration with
  | dagger =>
      simp [ReferenceActiveAffinePositiveTest.downPrefixGate, hconfiguration] at hgate
  | ordinary state memory =>
      have hprefix : ActiveFollowerLifecycle.localBufferValid state ∧
          ReferenceActiveAffinePositiveTest.downReceiverGate i x.row x.time state := by
        simpa [ReferenceActiveAffinePositiveTest.downPrefixGate, hconfiguration] using hgate
      exact ⟨state, memory, rfl, hprefix.2.2.1, hprefix.2.1⟩

private theorem prepared_receiver_arm_eq_tuple
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (i : Fin (p.m - 1)) (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hconfiguration : (prepared.followers.followers i).configuration = .ordinary state memory)
    (hunoccupied : state.status = .unoccupied)
    (hdown : PublicDiscreteDraws.slotDraw (x.row.2 x.time).1 = PublicDiscreteDraws.downSlot) :
    prepared.arms.actions (PublicDiscreteDraws.followerPlayer p.two_le_m i) =
      (OrderedTupleSampler.sample p.two_le_m p.m_lt_K (x.row.2 x.time).1).val
        (PublicDiscreteDraws.followerPlayer p.two_le_m i) := by
  rw [prepared.action_follower]
  have hlocal' := hconfiguration
  rw [prepared.followers.followers_eq i,
    ReferenceActiveFeedbackCut.prepareFollowers_apply] at hlocal'
  have hlocal :
      (DeclaredFollowerLocalRound.prepare rate i x.row (x.state.activations i) x.time
        (x.active i) (x.state.followers i)).configuration = .ordinary state memory := by
    simpa [ReferenceActivePhysicalStep.followerInput,
      ReferenceActivePhysicalStep.RoundInput.row] using hlocal'
  exact declaredPrepare_arm_eq_tuple_of_ordinary_unoccupied_down i x.row
    (x.state.activations i) x.time (x.active i) (x.state.followers i)
    state memory hlocal hunoccupied hdown

/-- A zero DOWN hash collides in the real finite feedback cut whenever the
actual gate is enabled: the checked coordinator SendArm and actual unoccupied
receiver PREPARE select the same tuple arm. -/
theorem downFeedback_eq_zero_of_sent_hash_zero
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (s : Sample (AffineBatchDecoder.width p))
    (word : Word (AffineBatchDecoder.width p))
    (hsent : ReferenceActiveAffinePositiveTest.downSent x = some word)
    (hhash : affineHash s word = 0)
    (hgate : ReferenceActiveAffinePositiveTest.downGate
      (ReferenceActiveAffinePositiveTest.replaceCurrentPair x 0 s) = true) :
    (ReferenceActiveFeedbackCut.collisionFeedbackVector
      (ReferenceActivePhysicalStep.prepare
        (ReferenceActiveAffinePositiveTest.replaceCurrentPair x 0 s)).arms.actions
      (ReferenceActiveAffinePositiveTest.replaceCurrentPair x 0 s).time
      (ReferenceActiveAffinePositiveTest.replaceCurrentPair x 0 s).rewards
      (PublicDiscreteDraws.followerPlayer p.two_le_m
        (ReferenceActivePhysicalStep.upSenderIndex
          (ReferenceActiveAffinePositiveTest.replaceCurrentPair x 0 s)))).val = 0 := by
  let y := ReferenceActiveAffinePositiveTest.replaceCurrentPair x 0 s
  have hsentY : ReferenceActiveAffinePositiveTest.downSent y = some word := by
    calc
      _ = ReferenceActiveAffinePositiveTest.downSent x :=
        ReferenceAffineDispatchPairInvariance.downSent_replace x 0 s
      _ = some word := hsent
  obtain ⟨state, memory, hconfiguration, hunoccupied, hselected⟩ :=
    downGate_true_receiver_prepared y hgate
  have hdown : PublicDiscreteDraws.slotDraw (y.row.2 y.time).1 = PublicDiscreteDraws.downSlot :=
    hselected.1
  have hreceiver := prepared_receiver_arm_eq_tuple y
    (ReferenceActivePhysicalStep.prepare y)
    (ReferenceActivePhysicalStep.upSenderIndex y) state memory
    hconfiguration hunoccupied hdown
  have hcoordinator := coordinatorAction_eq_sendArm_of_downSent y word hsentY
  have hhash' : affineHash (B := ContinuousLearningRows.B p) s word = 0 := by
    simpa only [AffineBatchDecoder.width, ContinuousLearningRows.B] using hhash
  have hpairY : (y.row.2 y.time).2
      (0, ReferenceActivePhysicalStep.upSenderIndex y) = s := by
    rw [(ReferenceActiveAffinePositiveTest.replaceCurrentPair_fields x 0 s).2.2.1]
    simpa only [y, ReferenceActiveAffinePositiveTest.upSenderIndex_replace,
      ContinuousLearningRows.d] using
      ReferenceActiveAffinePositiveTest.replaceCurrentPair_sample x 0 s
  rw [hpairY, hhash', ActiveRoundActions.sendArm_zero] at hcoordinator
  have hcollision : ¬ FiniteBanditModel.collisionFreeFor
      (ReferenceActivePhysicalStep.prepare y).arms.actions
      (PublicDiscreteDraws.followerPlayer p.two_le_m
        (ReferenceActivePhysicalStep.upSenderIndex y)) := by
    intro hfree
    have hneq : ActiveRoundActions.coordinator p.two_le_m ≠
        PublicDiscreteDraws.followerPlayer p.two_le_m
          (ReferenceActivePhysicalStep.upSenderIndex y) :=
      (ActiveRoundActions.followerPlayer_ne_coordinator p.two_le_m
        (ReferenceActivePhysicalStep.upSenderIndex y)).symm
    have hdistinct := hfree (ActiveRoundActions.coordinator p.two_le_m) hneq
    rw [hcoordinator, hreceiver] at hdistinct
    exact hdistinct rfl
  rw [ReferenceActiveFeedbackCut.collisionFeedbackVector_apply]
  simp [y, hcollision]

/-- A sent-word zero hash cannot pass the actual positive DOWN test. -/
theorem downPositive_false_of_sent_hash_zero
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (s : Sample (AffineBatchDecoder.width p))
    (word : Word (AffineBatchDecoder.width p))
    (hsent : ReferenceActiveAffinePositiveTest.downSent x = some word)
    (hhash : affineHash s word = 0) :
    ReferenceActiveAffinePositiveTest.downPositive
      (ReferenceActiveAffinePositiveTest.replaceCurrentPair x 0 s) = false := by
  rw [ReferenceActiveAffinePositiveTest.downPositive_eq_gate_feedback]
  rw [ReferenceActiveAffinePositiveTest.downGate_replace x 0 s]
  by_cases hgate : ReferenceActiveAffinePositiveTest.downGate x = true
  · have hfeedback := downFeedback_eq_zero_of_sent_hash_zero x s word hsent hhash
      (by simpa only [ReferenceActiveAffinePositiveTest.downGate_replace x 0 s] using hgate)
    simp [hgate, hfeedback]
  · have hgate' : ReferenceActiveAffinePositiveTest.downGate x = false := by
      cases h : ReferenceActiveAffinePositiveTest.downGate x <;> simp_all
    simp [hgate']

/-- A positive actual DOWN test with a sent word forces its affine hash to one.
The implication follows from the actual zero-hash collision branch. -/
theorem downPositive_sent_hash_one
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (word : Word (AffineBatchDecoder.width p))
    (hsent : ReferenceActiveAffinePositiveTest.downSent x = some word)
    (hpositive : ReferenceActiveAffinePositiveTest.downPositive x = true) :
    affineHash (originalDownSample x) word = 1 := by
  have hnotzero : affineHash (originalDownSample x) word ≠ 0 := by
    intro hzero
    have hfalse := downPositive_false_of_sent_hash_zero x (originalDownSample x)
      word hsent hzero
    rw [replaceCurrentPair_originalDownSample] at hfalse
    rw [hfalse] at hpositive
    cases hpositive
  have hval : (affineHash (originalDownSample x) word).val ≠ 0 :=
    (ZMod.val_ne_zero _).2 hnotzero
  have hval_lt : (affineHash (originalDownSample x) word).val < 2 :=
    ZMod.val_lt _
  have hval_eq : (affineHash (originalDownSample x) word).val = 1 := by omega
  have hone : (1 : Bit).val = 1 := by simpa using (ZMod.val_one 2)
  apply ZMod.val_injective 2
  rw [hval_eq, hone]

/-- In the actual finite affine-pair sum, the positive DOWN test and stale-word
exclusion have exactly a one-half candidate-hash factor. This is fixed-input
integration; it is not a conditional law on an original physical run. -/
theorem down_jointLaw_hash_half
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (candidate : Word (AffineBatchDecoder.width p)) :
    (∑ s : Sample (AffineBatchDecoder.width p), AffineChannelLaw.jointLaw
        (AffineBatchDecoder.width p) s * AdaptiveAffineBatchTail.indicator
          (ReferenceActiveAffinePositiveTest.downPositive
              (ReferenceActiveAffinePositiveTest.replaceCurrentPair x 0 s) = true ∧
            ReferenceActiveAffinePositiveTest.downSent x ≠ some candidate ∧
            affineHash s candidate = 1)) =
      ((1 : ℝ≥0∞) / 2) * ∑ s : Sample (AffineBatchDecoder.width p),
        AffineChannelLaw.jointLaw (AffineBatchDecoder.width p) s *
          AdaptiveAffineBatchTail.indicator
            (ReferenceActiveAffinePositiveTest.downPositive
                (ReferenceActiveAffinePositiveTest.replaceCurrentPair x 0 s) = true ∧
              ReferenceActiveAffinePositiveTest.downSent x ≠ some candidate) := by
  let decision : AdaptiveAffineBatchTail.Decision (AffineBatchDecoder.width p) Unit := {
    sent := ReferenceActiveAffinePositiveTest.downSent x
    active := true
    positive := fun _ bit => downRule x bit
  }
  have h := AdaptiveAffineBatchTail.one_step_half decision candidate ()
  have hpositive (s : Sample (AffineBatchDecoder.width p)) :
      ReferenceActiveAffinePositiveTest.downPositive
          (ReferenceActiveAffinePositiveTest.replaceCurrentPair x 0 s) =
        AdaptiveAffineBatchTail.positiveTest decision s () := by
    cases hsent : ReferenceActiveAffinePositiveTest.downSent x
    · rw [downPositive_replace_eq_downRule]
      simp [AdaptiveAffineBatchTail.positiveTest, decision, downHashBit, hsent]
    · rw [downPositive_replace_eq_downRule]
      simp [AdaptiveAffineBatchTail.positiveTest, decision, downHashBit, hsent]
  have hleft :
      (∑ s : Sample (AffineBatchDecoder.width p), AffineChannelLaw.jointLaw
          (AffineBatchDecoder.width p) s * AdaptiveAffineBatchTail.indicator
            (AdaptiveAffineBatchTail.positiveTest decision s () = true ∧
              decision.sent ≠ some candidate ∧ affineHash s candidate = 1)) =
        (∑ s : Sample (AffineBatchDecoder.width p), AffineChannelLaw.jointLaw
          (AffineBatchDecoder.width p) s * AdaptiveAffineBatchTail.indicator
            (ReferenceActiveAffinePositiveTest.downPositive
                (ReferenceActiveAffinePositiveTest.replaceCurrentPair x 0 s) = true ∧
              ReferenceActiveAffinePositiveTest.downSent x ≠ some candidate ∧
              affineHash s candidate = 1)) := by
    apply Finset.sum_congr rfl
    intro s hs
    rw [hpositive s]
  have hright :
      (∑ s : Sample (AffineBatchDecoder.width p), AffineChannelLaw.jointLaw
          (AffineBatchDecoder.width p) s * AdaptiveAffineBatchTail.indicator
            (AdaptiveAffineBatchTail.positiveTest decision s () = true ∧
              decision.sent ≠ some candidate)) =
        (∑ s : Sample (AffineBatchDecoder.width p), AffineChannelLaw.jointLaw
          (AffineBatchDecoder.width p) s * AdaptiveAffineBatchTail.indicator
            (ReferenceActiveAffinePositiveTest.downPositive
                (ReferenceActiveAffinePositiveTest.replaceCurrentPair x 0 s) = true ∧
              ReferenceActiveAffinePositiveTest.downSent x ≠ some candidate)) := by
    apply Finset.sum_congr rfl
    intro s hs
    rw [hpositive s]
  rw [← hleft, ← hright]
  exact h

/-- The fixed-input half identity at a same-record physical round. -/
theorem roundRecord_down_jointLaw_hash_half
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (candidate : Word (AffineBatchDecoder.width p)) :
    (∑ s : Sample (AffineBatchDecoder.width p), AffineChannelLaw.jointLaw
        (AffineBatchDecoder.width p) s * AdaptiveAffineBatchTail.indicator
          (ReferenceActiveAffinePositiveTest.downPositive
              (ReferenceActiveAffinePositiveTest.replaceCurrentPair record.input 0 s) = true ∧
            ReferenceActiveAffinePositiveTest.downSent record.input ≠ some candidate ∧
            affineHash s candidate = 1)) =
      ((1 : ℝ≥0∞) / 2) * ∑ s : Sample (AffineBatchDecoder.width p),
        AffineChannelLaw.jointLaw (AffineBatchDecoder.width p) s *
          AdaptiveAffineBatchTail.indicator
            (ReferenceActiveAffinePositiveTest.downPositive
                (ReferenceActiveAffinePositiveTest.replaceCurrentPair record.input 0 s) = true ∧
              ReferenceActiveAffinePositiveTest.downSent record.input ≠ some candidate) :=
  down_jointLaw_hash_half record.input candidate

/-- The same fixed-input identity for any record selected from an actual run;
membership is visible, and no prefix induction or run-level conditional law is
asserted. -/
theorem runRecord_down_jointLaw_hash_half
    {initial : ReferenceActivePhysicalHorizon.State p rate}
    (execution : ReferenceActivePhysicalHorizon.Run initial)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (_hrecord : record ∈ execution.records)
    (candidate : Word (AffineBatchDecoder.width p)) :
    (∑ s : Sample (AffineBatchDecoder.width p), AffineChannelLaw.jointLaw
        (AffineBatchDecoder.width p) s * AdaptiveAffineBatchTail.indicator
          (ReferenceActiveAffinePositiveTest.downPositive
              (ReferenceActiveAffinePositiveTest.replaceCurrentPair record.input 0 s) = true ∧
            ReferenceActiveAffinePositiveTest.downSent record.input ≠ some candidate ∧
            affineHash s candidate = 1)) =
      ((1 : ℝ≥0∞) / 2) * ∑ s : Sample (AffineBatchDecoder.width p),
        AffineChannelLaw.jointLaw (AffineBatchDecoder.width p) s *
          AdaptiveAffineBatchTail.indicator
            (ReferenceActiveAffinePositiveTest.downPositive
                (ReferenceActiveAffinePositiveTest.replaceCurrentPair record.input 0 s) = true ∧
              ReferenceActiveAffinePositiveTest.downSent record.input ≠ some candidate) :=
  roundRecord_down_jointLaw_hash_half record candidate

end Bandits.Support.ReferenceDownPhysicalHashRule

end
