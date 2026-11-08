/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferencePrelaunchInspectedPrefixCode
public import Bandits.Support.ReferencePrelaunchDownDecisionReadout

import Lean.Elab.Tactic.Omega

/-!
# Strict-past prelaunch DOWN decoder readout in the inspected source history

Sources: `07_public_setup.tex:127-164`, `05_binary_transport.tex:7-55`, and
`appendix_a_local_protocol.tex:92-157`.

The event is the existing finite strict-past `prelaunchPastDecoderFlag` from
the admitted source readout.  Its per-round factor uses the original three
branch prefix code, its retained real buffer fibres, the actual current
control and own entry, and the countable ordinary decoder/parser projection.
The finite date remains explicit, so the current decision enters at the
successor field and is excluded only at the next strict-past date.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.ReferenceInitializationRun
open Bandits.Support.ReferencePrelaunchFollower
open Bandits.Support.ReferenceGeneratedPrelaunchDownPastFactor
open Bandits.Support.ReferencePrelaunchPhysicalReplay
open Bandits.Support.BootstrapDimensions
open scoped Classical

namespace Bandits.Support.ReferencePrelaunchInspectedDecoderPast

local instance sumMeasurableSingletonClass (α β : Type*) [MeasurableSpace α]
    [MeasurableSpace β] [MeasurableSingletonClass α] [MeasurableSingletonClass β] :
    MeasurableSingletonClass (α ⊕ β) where
  measurableSet_singleton x := by
    cases x with
    | inl x =>
        simpa only [Set.image_singleton] using
          (measurableSet_singleton x).inl_image (β := β)
    | inr x =>
        simpa only [Set.image_singleton] using
          (measurableSet_singleton x).inr_image (α := α)

variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ)

private abbrev K (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (n : ℕ) (hn : n ≤ p.T) : MeasurableSpace (SourceInput p) :=
  ReferenceSourceOwnHistoryContainment.inspectedHistorySpace
    rate rewards C_star C_h n hn

private theorem advance_completed_ge (x : ReferenceInitializationRun.Input p)
    (b : ReferenceInitializationRun.Boundary p) :
    b.completed ≤ (ReferenceInitializationRun.advance x b).completed := by
  unfold ReferenceInitializationRun.advance
  split_ifs with hc h
  · exact le_rfl
  · simp [ReferenceInitializationRun.finishBlock]
  · exact le_rfl

private theorem run_completed_mono (x : ReferenceInitializationRun.Input p)
    {a b : ℕ} (hab : a ≤ b) :
    (ReferenceInitializationRun.run x a).completed ≤
      (ReferenceInitializationRun.run x b).completed := by
  induction hab with
  | refl => exact le_rfl
  | @step b hab ih =>
      rw [ReferenceInitializationRun.run_succ]
      exact ih.trans (advance_completed_ge x (ReferenceInitializationRun.run x b))

private theorem advance_history_at (x : ReferenceInitializationRun.Input p)
    (b : ReferenceInitializationRun.Boundary p) (player : Fin p.m) (t : Fin p.T)
    (ht : t.val < ReferenceInitializationRun.elapsed p b.completed)
    (ht' : t.val < ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.advance x b).completed) :
    (ReferenceInitializationRun.advance x b).history player ⟨t.val, ht'⟩ =
      b.history player ⟨t.val, ht⟩ := by
  classical
  generalize heq : ReferenceInitializationRun.advance x b = c at ht' ⊢
  unfold ReferenceInitializationRun.advance at heq
  split at heq
  · cases heq
    rfl
  · split at heq
    · cases heq
      exact ReferenceInitializationRun.extendedHistory_prefix x b _ player ⟨t.val, ht⟩
    · cases heq
      rfl

private theorem run_history_eq_after (x : ReferenceInitializationRun.Input p)
    (player : Fin p.m) (t : Fin p.T) {a b : ℕ} (hab : a ≤ b)
    (ht : t.val < ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.run x a).completed) :
    (ReferenceInitializationRun.run x b).history player
        ⟨t.val, lt_of_lt_of_le ht
          (ReferenceInitializationRun.elapsed_mono p (run_completed_mono x hab))⟩ =
      (ReferenceInitializationRun.run x a).history player ⟨t.val, ht⟩ := by
  induction hab with
  | refl => rfl
  | @step b hab ih =>
      have hmid : t.val < ReferenceInitializationRun.elapsed p
          (ReferenceInitializationRun.run x b).completed :=
        lt_of_lt_of_le ht (ReferenceInitializationRun.elapsed_mono p
          (run_completed_mono x hab))
      have hsucc : t.val < ReferenceInitializationRun.elapsed p
          (ReferenceInitializationRun.run x b.succ).completed :=
        lt_of_lt_of_le ht (ReferenceInitializationRun.elapsed_mono p
          (run_completed_mono x (Nat.le.step hab)))
      change (ReferenceInitializationRun.advance x (ReferenceInitializationRun.run x b)).history
          player ⟨t.val, hsucc⟩ = _
      exact (advance_history_at x (ReferenceInitializationRun.run x b)
        player t hmid hsucc).trans ih

private def controlCurrentCode (i : Fin (p.m - 1))
    (control : ContinuousLearningRows.TimeControl p) :
    PublicDiscreteDraws.Slot × Fin (p.m - 1) ×
      AffineChannelLaw.Sample (AffineBatchDecoder.width p) :=
  (PublicDiscreteDraws.slotDraw control.1,
    PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K control.1,
    control.2 (0, i))

private instance observationCountable :
    Countable (ReferencePrelaunchFollower.Observation p) :=
  (ReferenceInitializationMeasurability.observationGridIndex_injective p).countable

private def ownEntryCode (entry : ReferenceSourceOwnHistoryContainment.OwnEntry p) :=
  (entry.1, ReferenceInitializationMeasurability.observationGridIndex p entry.2)

private theorem measurable_ownEntryCode :
    Measurable (ownEntryCode (p := p)) := measurable_of_countable _

private def passingAtCode (rate : ReferenceActivePhysicalStep.RateInput p)
    (i : Fin (p.m - 1)) (r : Fin p.T)
    (rowCode : PublicDiscreteDraws.Slot × Fin (p.m - 1) ×
      AffineChannelLaw.Sample (AffineBatchDecoder.width p))
    (own : Fin p.K × Fin (ConstructorDimensions.D p + 1))
    (alpha : ReferencePrelaunchFollower.Activation p)
    (batch : AffineBatchDecoder.State p.T (AffineBatchDecoder.width p)) : Prop := by
  classical
  let current : AffineBatchDecoder.RoundInput (AffineBatchDecoder.width p) := {
    selected := decide (alpha.val ≤ r.val + 1 ∧
      rowCode.1 = PublicDiscreteDraws.downSlot ∧ rowCode.2.1 = i)
    receiverEnabled := true
    sample := rowCode.2.2
    roundedReward := (ActualInitializationPhysicalStep.observationOfGrid p own.2).val.val
  }
  let trace : AffineBatchDecoder.Trace p := fun _ => current
  let output := if current.selected = true then
      AffineBatchDecoder.decodeStep p trace batch r
    else (batch, none)
  exact ∃ M : OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta), OrdinaryMessageCodec.parseDown
      (ReferencePrelaunchFollower.codecParams p rate.eta)
      (output.2.map (OrdinaryMessageCodec.wordEquivFlat
        (ReferencePrelaunchFollower.codecParams p rate.eta)).symm) = some M ∧
    OrdinaryMessageCodec.acceptDown (ReferencePrelaunchFollower.codecParams p rate.eta)
      0 (r.val + 1) M

private def decisionFromPrefixRegisters (rate : ReferenceActivePhysicalStep.RateInput p)
    (i : Fin (p.m - 1)) (r : Fin p.T)
    (rowCode : PublicDiscreteDraws.Slot × Fin (p.m - 1) ×
      AffineChannelLaw.Sample (AffineBatchDecoder.width p))
    (own : Fin p.K × Fin (ConstructorDimensions.D p + 1))
    (registers : ReferenceGeneratedPrelaunchDownPastFactor.PrefixRegisters p rate r.val) : Bool :=
  match registers with
  | .inl (.inl (_, alpha, _, stateCode)) =>
      decide (passingAtCode rate i r rowCode own alpha
        (FollowerDownMeasurability.decoderBatchOfCode stateCode.downBatch)
      )
  | .inl (.inr _) => false
  | .inr _ => false

private theorem passingAtCode_eq (i : Fin (p.m - 1)) (r : Fin p.T)
    (row : CompletePublicTable.CompleteRow p)
    (rowCode : PublicDiscreteDraws.Slot × Fin (p.m - 1) ×
      AffineChannelLaw.Sample (AffineBatchDecoder.width p))
    (own : Fin p.K × Fin (ConstructorDimensions.D p + 1))
    (actualOwn : ReferenceSourceOwnHistoryContainment.OwnEntry p)
    (hown : own = ownEntryCode actualOwn)
    (alpha : ReferencePrelaunchFollower.Activation p)
    (batch : AffineBatchDecoder.State p.T (AffineBatchDecoder.width p))
    (hrow : (ReferenceInitializationMeasurability.ordinaryRowCode p i row) r = rowCode) :
    decide (passingAtCode rate i r rowCode own alpha batch) =
      decide (ReferencePrelaunchFollower.passing_at rate.eta i row alpha r actualOwn batch) := by
  classical
  let expected : AffineBatchDecoder.RoundInput (AffineBatchDecoder.width p) := {
    selected := decide (alpha.val ≤ r.val + 1 ∧
      rowCode.1 = PublicDiscreteDraws.downSlot ∧ rowCode.2.1 = i)
    receiverEnabled := true
    sample := rowCode.2.2
    roundedReward := (ActualInitializationPhysicalStep.observationOfGrid p own.2).val.val
  }
  have hinput :
      ReferencePrelaunchFollower.downInput i row alpha r actualOwn = expected := by
    have hs := congrArg Prod.fst hrow
    have hi := congrArg (fun v => v.2.1) hrow
    have ha := congrArg (fun v => v.2.2) hrow
    dsimp only [ReferenceInitializationMeasurability.ordinaryRowCode] at hs hi ha
    have hreward :
        (ActualInitializationPhysicalStep.observationOfGrid p own.2).val.val =
          actualOwn.2.val.val := by
      have hgrid := congrArg Prod.snd hown
      dsimp [ownEntryCode] at hgrid
      rw [hgrid, ActualInitializationPhysicalStep.observationOfGrid_value,
        ReferenceInitializationMeasurability.observationGridIndex_value]
    dsimp only [ReferencePrelaunchFollower.downInput, expected]
    congr 1
    all_goals
      first
      | exact Bool.decide_congr (by simp [hs, hi, PublicDiscreteDraws.followerCount])
      | exact hreward.symm
  let current : AffineBatchDecoder.RoundInput (AffineBatchDecoder.width p) := expected
  let trace : AffineBatchDecoder.Trace p := fun _ => current
  let output := if current.selected = true then
      AffineBatchDecoder.decodeStep p trace batch r
    else (batch, none)
  have htrace : ReferencePrelaunchFollower.traceAt i row alpha r actualOwn =
      fun _ => expected := by
    funext t
    simp [ReferencePrelaunchFollower.traceAt, hinput]
  have houtput : output = ReferencePrelaunchFollower.decodeAt i row alpha r actualOwn batch := by
    dsimp only [output, current, trace, ReferencePrelaunchFollower.decodeAt]
    rw [htrace, hinput]
  have hprop : passingAtCode rate i r rowCode own alpha batch ↔
      ReferencePrelaunchFollower.passing_at rate.eta i row alpha r actualOwn batch := by
    change (∃ M : OrdinaryMessageCodec.DownRecord
        (ReferencePrelaunchFollower.codecParams p rate.eta),
          OrdinaryMessageCodec.parseDown
            (ReferencePrelaunchFollower.codecParams p rate.eta)
            (output.2.map (OrdinaryMessageCodec.wordEquivFlat
              (ReferencePrelaunchFollower.codecParams p rate.eta)).symm) = some M ∧
          OrdinaryMessageCodec.acceptDown (ReferencePrelaunchFollower.codecParams p rate.eta)
            0 (r.val + 1) M) ↔
      ∃ M : OrdinaryMessageCodec.DownRecord
          (ReferencePrelaunchFollower.codecParams p rate.eta),
        OrdinaryMessageCodec.parseDown
          (ReferencePrelaunchFollower.codecParams p rate.eta)
          ((ReferencePrelaunchFollower.decodeAt i row alpha r actualOwn batch).2.map
            (OrdinaryMessageCodec.wordEquivFlat
              (ReferencePrelaunchFollower.codecParams p rate.eta)).symm) = some M ∧
        OrdinaryMessageCodec.acceptDown (ReferencePrelaunchFollower.codecParams p rate.eta)
          0 (r.val + 1) M
    rw [houtput]
  exact Bool.decide_congr hprop

private theorem decisionFromPrefixRegisters_measurable (i : Fin (p.m - 1))
    (r : Fin p.T) :
    Measurable (fun v : (ReferenceGeneratedPrelaunchDownPastFactor.PrefixRegisters p rate r.val) ×
      ((PublicDiscreteDraws.Slot × Fin (p.m - 1) ×
        AffineChannelLaw.Sample (AffineBatchDecoder.width p)) ×
        (Fin p.K × Fin (ConstructorDimensions.D p + 1))) =>
      decisionFromPrefixRegisters rate i r v.2.1 v.2.2 v.1) := by
  exact measurable_of_countable _

private theorem currentOwnEntry_eq_recorded (n : ℕ) (hn : n ≤ p.T)
    (i : Fin (p.m - 1)) (r : Fin p.T) (hr : r.val < n) (z : SourceInput p)
    (active : ReferenceGeneratedPrelaunchDownPrefix.ActiveProjection p i r.val
      (ReferenceGeneratedPrelaunchDownPrefix.sourceReferenceInput
        rate rewards C_star C_h z).row (Nat.le_of_lt r.isLt)
      (ReferenceGeneratedPrelaunchDownPrefix.sourceReferenceInput
        rate rewards C_star C_h z) (BootstrapDimensions.roundBlockIndex p r)) :
    ReferenceSourceOwnHistoryContainment.ownBefore rate rewards C_star C_h
        n hn z
        (PublicDiscreteDraws.followerPlayer p.two_le_m
          (ActualReferenceInitializationBlock.refFollower i))
        ⟨r.val, hr⟩ =
      ReferenceInitializationRun.ownEntry
        (ReferenceInitializationRun.physical
          (ReferenceGeneratedPrelaunchDownPrefix.sourceReferenceInput
            rate rewards C_star C_h z)
          active.val.1.val active.val.1.property.1)
        (PublicDiscreteDraws.followerPlayer p.two_le_m
          (ActualReferenceInitializationBlock.refFollower i)) r := by
  classical
  let x := ReferenceGeneratedPrelaunchDownPrefix.sourceReferenceInput
    rate rewards C_star C_h z
  let s := BootstrapDimensions.roundBlockIndex p r
  let b := active.val.1.val
  let h := active.val.1.property.1
  have hboundary : b = ReferenceInitializationRun.run x s.val :=
    active.val.1.property.2.2
  have hcross : b.crossing = none := active.val.1.property.2.1
  have hcrossRun : (ReferenceInitializationRun.run x s.val).crossing = none := by
    rw [← hboundary]
    exact hcross
  have hcompleted : b.completed = s.val := by
    have hp := ReferenceInitializationRun.run_progress x s.val s.isLt.le
    rcases hp with hc | he
    · rw [← hboundary, hcross] at hc
      cases hc
    · exact (congrArg Boundary.completed hboundary).trans he
  have hproc : s.val + 1 ≤ n_boot p := Nat.succ_le_of_lt s.isLt
  have hrunNext : ReferenceInitializationRun.run x (s.val + 1) =
      ReferenceInitializationRun.finishBlock x b h := by
    rw [ReferenceInitializationRun.run_succ, ← hboundary,
      ReferenceInitializationRun.advance_of_no_crossing x b hcross h]
  have hnextCompleted :
      (ReferenceInitializationRun.run x (s.val + 1)).completed = s.val + 1 := by
    rw [hrunNext, (ReferenceInitializationRun.finishBlock_equations x b h).1,
      hcompleted]
  have hcalendar : r ∈ BootstrapDimensions.calendarBlock p s :=
    BootstrapDimensions.round_mem_quotient_block p r
  obtain ⟨u, hu⟩ := ReferencePrelaunchPhysicalReplay.exists_blockRound p s r hcalendar
  have htime : ReferencePrelaunchPhysicalReplay.blockRound
      (p := p) s u = r := hu
  have hblock := (BootstrapDimensions.mem_calendarBlock_iff p s r).mp hcalendar
  have hwithin : r.val < ReferenceInitializationRun.elapsed p (s.val + 1) := by
    simpa only [ReferenceInitializationRun.elapsed] using hblock.2
  have hmono := run_completed_mono x hproc
  have hstart : r.val <
      ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.output x).completed := by
    have hElapsed : ReferenceInitializationRun.elapsed p (s.val + 1) ≤
        ReferenceInitializationRun.elapsed p
          (ReferenceInitializationRun.run x (n_boot p)).completed := by
      rw [← hnextCompleted]
      exact ReferenceInitializationRun.elapsed_mono p hmono
    simpa only [ReferenceInitializationRun.output] using
      lt_of_lt_of_le hwithin hElapsed
  have hstartNext : r.val < ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.run x (s.val + 1)).completed := by
    rw [hnextCompleted]
    exact hwithin
  have hhistoryBlock :
      (ReferenceInitializationRun.run x (s.val + 1)).history
          (PublicDiscreteDraws.followerPlayer p.two_le_m
            (ActualReferenceInitializationBlock.refFollower i))
          ⟨r.val, hstartNext⟩ =
        ReferenceInitializationRun.ownEntry (ReferenceInitializationRun.physical x b h)
          (PublicDiscreteDraws.followerPlayer p.two_le_m
            (ActualReferenceInitializationBlock.refFollower i)) r := by
    have hnext : ReferenceInitializationRun.nextBlock b h = s := by
      apply Fin.ext
      simp only [ReferenceInitializationRun.nextBlock, hcompleted]
    have hcalendar' : r ∈ BootstrapDimensions.calendarBlock p
        (ReferenceInitializationRun.nextBlock b h) := by
      simpa only [hnext] using hcalendar
    obtain ⟨v, hv⟩ := ReferencePrelaunchPhysicalReplay.exists_blockRound p
      (ReferenceInitializationRun.nextBlock b h) r hcalendar'
    have htime : ReferencePrelaunchPhysicalReplay.blockRound
        (p := p) (ReferenceInitializationRun.nextBlock b h) v = r := hv
    have hblockEntry := ReferenceInitializationRun.extendedHistory_block x b h
      (PublicDiscreteDraws.followerPlayer p.two_le_m
        (ActualReferenceInitializationBlock.refFollower i)) v
    have hwithin' : r.val < ReferenceInitializationRun.elapsed p (b.completed + 1) := by
      simpa only [hcompleted] using hwithin
    have hfinishTime : r.val < ReferenceInitializationRun.elapsed p
        (ReferenceInitializationRun.finishBlock x b h).completed := by
      rw [(ReferenceInitializationRun.finishBlock_equations x b h).1]
      exact hwithin'
    have hfinishTime' : r.val < ReferenceInitializationRun.elapsed p (b.completed + 1) := by
      exact hwithin'
    have hblockIndex : ReferencePrelaunchPhysicalReplay.blockEmbed v =
        (⟨r.val, hfinishTime'⟩ : Fin (ReferenceInitializationRun.elapsed p
          (b.completed + 1))) := by
      apply Fin.ext
      have hv' := congrArg Fin.val htime
      rw [ReferencePrelaunchPhysicalReplay.blockRound_val] at hv'
      simpa only [ReferencePrelaunchPhysicalReplay.blockEmbed] using hv'
    have hfinishEntry :
        ReferenceInitializationRun.extendedHistory x b h
          (PublicDiscreteDraws.followerPlayer p.two_le_m
            (ActualReferenceInitializationBlock.refFollower i))
          ⟨r.val, hfinishTime'⟩ =
        ReferenceInitializationRun.ownEntry (ReferenceInitializationRun.physical x b h)
          (PublicDiscreteDraws.followerPlayer p.two_le_m
            (ActualReferenceInitializationBlock.refFollower i)) r := by
      calc
        _ = ReferenceInitializationRun.extendedHistory x b h
            (PublicDiscreteDraws.followerPlayer p.two_le_m
              (ActualReferenceInitializationBlock.refFollower i))
            (ReferencePrelaunchPhysicalReplay.blockEmbed v) := by rw [hblockIndex]
        _ = ReferenceInitializationRun.ownEntry (ReferenceInitializationRun.physical x b h)
            (PublicDiscreteDraws.followerPlayer p.two_le_m
              (ActualReferenceInitializationBlock.refFollower i)) r := by
              simpa only [htime] using hblockEntry
    have hfinishHistory :
        (ReferenceInitializationRun.finishBlock x b h).history
          (PublicDiscreteDraws.followerPlayer p.two_le_m
            (ActualReferenceInitializationBlock.refFollower i))
          ⟨r.val, hfinishTime⟩ =
          ReferenceInitializationRun.ownEntry (ReferenceInitializationRun.physical x b h)
            (PublicDiscreteDraws.followerPlayer p.two_le_m
              (ActualReferenceInitializationBlock.refFollower i)) r := by
      change ReferenceInitializationRun.extendedHistory x b h
        (PublicDiscreteDraws.followerPlayer p.two_le_m
          (ActualReferenceInitializationBlock.refFollower i))
        ⟨r.val, hfinishTime'⟩ = _
      exact hfinishEntry
    have hrunHistory :
        (ReferenceInitializationRun.run x (s.val + 1)).history
          (PublicDiscreteDraws.followerPlayer p.two_le_m
            (ActualReferenceInitializationBlock.refFollower i))
          ⟨r.val, hstartNext⟩ =
        (ReferenceInitializationRun.finishBlock x b h).history
          (PublicDiscreteDraws.followerPlayer p.two_le_m
            (ActualReferenceInitializationBlock.refFollower i))
          ⟨r.val, hfinishTime⟩ := by
      let observe := fun state : ReferenceInitializationRun.Boundary p =>
        if ht : r.val < ReferenceInitializationRun.elapsed p state.completed then
          some (state.history
            (PublicDiscreteDraws.followerPlayer p.two_le_m
              (ActualReferenceInitializationBlock.refFollower i)) ⟨r.val, ht⟩)
        else none
      have hobserve := congrArg observe hrunNext
      simp only [observe, dite_eq_left hstartNext, dite_eq_left hfinishTime] at hobserve
      exact Option.some.inj hobserve
    exact hrunHistory.trans hfinishHistory
  have hstable := run_history_eq_after x
    (PublicDiscreteDraws.followerPlayer p.two_le_m
      (ActualReferenceInitializationBlock.refFollower i)) r (hab := hproc) hstartNext
  have hstartOutput : r.val < ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output x).completed := by
    simpa only [ReferenceInitializationRun.output] using
      lt_of_lt_of_le hstartNext (ReferenceInitializationRun.elapsed_mono p hmono)
  change ReferenceCompletePhysicalHistory.completeOwnHistory rate z rewards C_star C_h
      (PublicDiscreteDraws.followerPlayer p.two_le_m
        (ActualReferenceInitializationBlock.refFollower i))
      (Fin.castLE hn ⟨r.val, hr⟩) = _
  have hstartPhysical : r.val < ReferenceCompletePhysicalHistory.physicalStart
      rate z rewards C_star C_h := by
    simpa [x, ReferenceCompletePhysicalHistory.physicalStart,
      ReferenceCompletePhysicalHistory.generatedBoundary,
      ReferenceCompletePhysicalHistory.generatedInput,
      ReferenceGeneratedPrelaunchDownPrefix.sourceReferenceInput] using hstart
  rw [ReferenceCompletePhysicalHistory.completeOwnHistory_prefix]
  · change (ReferenceInitializationRun.output x).history
      (PublicDiscreteDraws.followerPlayer p.two_le_m
        (ActualReferenceInitializationBlock.refFollower i))
      (⟨r.val, hstartPhysical⟩ : Fin (ReferenceInitializationRun.elapsed p
        (ReferenceInitializationRun.output x).completed)) = _
    have hindex :
        (⟨r.val, hstartPhysical⟩ : Fin (ReferenceInitializationRun.elapsed p
          (ReferenceInitializationRun.output x).completed)) = ⟨r.val, hstartOutput⟩ := by
      apply Fin.ext
      rfl
    rw [hindex]
    change (ReferenceInitializationRun.run x (n_boot p)).history
      (PublicDiscreteDraws.followerPlayer p.two_le_m
        (ActualReferenceInitializationBlock.refFollower i))
      ⟨r.val, hstartOutput⟩ = _
    exact hstable.trans hhistoryBlock

private theorem decisionFromPrefixRegisters_eq_actual (n : ℕ) (hn : n ≤ p.T)
    (r : Fin p.T) (hr : r.val < n) (i : Fin (p.m - 1)) (z : SourceInput p) :
    decisionFromPrefixRegisters rate i r
        (ReferenceInitializationMeasurability.ordinaryRowCode p i
          (ReferenceGeneratedPrelaunchDownPrefix.sourceReferenceInput
            rate rewards C_star C_h z).row r)
        (ownEntryCode ((ReferenceSourceOwnHistoryContainment.ownBefore rate rewards C_star C_h
          n hn z)
          (PublicDiscreteDraws.followerPlayer p.two_le_m
            (ActualReferenceInitializationBlock.refFollower i))
          ⟨r.val, hr⟩))
        (sourcePrefixRegisters rate rewards C_star C_h z i r) =
      ReferencePrelaunchDownDecisionReadout.prelaunchDownFailureAt
        rate rewards C_star C_h z i r := by
  classical
  let x := ReferenceGeneratedPrelaunchDownPrefix.sourceReferenceInput
    rate rewards C_star C_h z
  let f := ActualReferenceInitializationBlock.refFollower i
  let player := PublicDiscreteDraws.followerPlayer p.two_le_m f
  cases hp : ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix
      rate rewards C_star C_h z i r with
  | inl branch =>
      cases branch with
      | inl active =>
          have hbatch := FollowerDownMeasurability.decoderBatchOfCode_code
            active.val.2.2.2.downBatch
          have hown := currentOwnEntry_eq_recorded rate rewards C_star C_h n hn i r hr z active
          have hownCode := congrArg ownEntryCode hown
          simp only [sourcePrefixRegisters, sourcePrefixCode, hp,
            ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix_observation,
            ReferenceGeneratedPrelaunchDownPrefix.forgetPrefixProofs,
            ReferenceGeneratedPrelaunchDownPastFactor.encodePrefix,
            ReferenceGeneratedPrelaunchDownPastFactor.prefixRegisters,
            FollowerObservationStageMeasurabilityRepair.carriedStateOfState,
            FollowerDownMeasurability.followerStateCode] at hbatch ⊢
          simp only [decisionFromPrefixRegisters, hp,
            FollowerDownMeasurability.decoderBatchOfCode_code, hownCode,
            ReferencePrelaunchDownDecisionReadout.prelaunchDownFailureAt,
            ReferencePrelaunchFollower.passing_at]
          exact passingAtCode_eq rate i r x.row
            (controlCurrentCode i ((x.row.2 r)))
            (ownEntryCode (ReferenceInitializationRun.ownEntry
              (ReferenceInitializationRun.physical x active.val.1.val
                active.val.1.property.1) player r))
            (ReferenceInitializationRun.ownEntry
              (ReferenceInitializationRun.physical x active.val.1.val
                active.val.1.property.1) player r) rfl
            active.val.2.1 active.val.2.2.2.downBatch rfl
      | inr inactive =>
          simp [decisionFromPrefixRegisters, sourcePrefixRegisters, sourcePrefixCode, hp,
            ReferencePrelaunchDownDecisionReadout.prelaunchDownFailureAt,
            ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix_observation,
            ReferenceGeneratedPrelaunchDownPrefix.forgetPrefixProofs,
            ReferenceGeneratedPrelaunchDownPastFactor.encodePrefix,
            ReferenceGeneratedPrelaunchDownPastFactor.prefixRegisters]
  | inr stopped =>
      simp [decisionFromPrefixRegisters, sourcePrefixRegisters, sourcePrefixCode, hp,
        ReferencePrelaunchDownDecisionReadout.prelaunchDownFailureAt,
        ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix_observation,
        ReferenceGeneratedPrelaunchDownPrefix.forgetPrefixProofs,
        ReferenceGeneratedPrelaunchDownPastFactor.encodePrefix,
        ReferenceGeneratedPrelaunchDownPastFactor.prefixRegisters]

local instance prefixCodesAtEachIndexMeasurableSpace (n : ℕ) (j : Fin n) :
    MeasurableSpace
      (Fin (p.m - 1) →
        ReferenceGeneratedPrelaunchDownPastFactor.PrefixCode p rate j.val) :=
  MeasurableSpace.pi

local instance prefixCodeFamilyMeasurableSpace (n : ℕ) :
    MeasurableSpace
      ((j : Fin n) → Fin (p.m - 1) →
        ReferenceGeneratedPrelaunchDownPastFactor.PrefixCode p rate j.val) :=
  MeasurableSpace.pi

private theorem measurable_controlCurrentCode (i : Fin (p.m - 1)) :
    Measurable (fun control : ContinuousLearningRows.TimeControl p =>
      controlCurrentCode i control) := by
  have hslot : Measurable (fun control : ContinuousLearningRows.TimeControl p =>
      PublicDiscreteDraws.slotDraw control.1) :=
    PublicDiscreteDraws.measurable_slotDraw.comp measurable_fst
  have hselected : Measurable (fun control : ContinuousLearningRows.TimeControl p =>
      PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K control.1) :=
    (PublicDiscreteDraws.measurable_selectedFollowerDraw p.two_le_m p.m_lt_K).comp
      measurable_fst
  have hsample : Measurable (fun control : ContinuousLearningRows.TimeControl p =>
      control.2 (0, i)) :=
    (measurable_pi_apply (0, i)).comp measurable_snd
  exact hslot.prodMk (hselected.prodMk hsample)

private def factorDecision (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (n : ℕ) (hn : n ≤ p.T)
    (z : SourceInput p) (j : Fin n) (i : Fin (p.m - 1)) : Bool :=
  decisionFromPrefixRegisters rate i (Fin.castLE hn j)
    (controlCurrentCode i
      ((ReferenceSourceOwnHistoryContainment.selectedControlPrefix n hn z) j))
    (ownEntryCode ((ReferenceSourceOwnHistoryContainment.ownBefore rate rewards C_star C_h n hn z)
      (PublicDiscreteDraws.followerPlayer p.two_le_m
        (ActualReferenceInitializationBlock.refFollower i)) j))
    (ReferenceGeneratedPrelaunchDownPastFactor.prefixRegisters
      (ReferencePrelaunchInspectedPrefixCode.sourcePrefixCodeFamily
        rate rewards C_star C_h n hn z j i))

/-- The factor rebuilds each prefix observation through the lossless decoder,
then projects its countable active registers and the actual dated controls. -/
private theorem factorDecision_eq_actual (n : ℕ) (hn : n ≤ p.T)
    (z : SourceInput p) (j : Fin n) (i : Fin (p.m - 1)) :
    factorDecision rate rewards C_star C_h n hn z j i =
      ReferencePrelaunchDownDecisionReadout.prelaunchDownFailureAt
        rate rewards C_star C_h z i (Fin.castLE hn j) := by
  classical
  let r : Fin p.T := Fin.castLE hn j
  let codes := ReferencePrelaunchInspectedPrefixCode.sourcePrefixCodeFamily
    rate rewards C_star C_h n hn z
  let controls := ReferenceSourceOwnHistoryContainment.selectedControlPrefix n hn z
  let own := ReferenceSourceOwnHistoryContainment.ownBefore rate rewards C_star C_h n hn z
  let player := PublicDiscreteDraws.followerPlayer p.two_le_m
    (ActualReferenceInitializationBlock.refFollower i)
  have hdecode := ReferencePrelaunchInspectedPrefixCode.decode_sourcePrefixCodeFamily
    rate rewards C_star C_h n hn z j i
  have hfamilyCode : codes j i =
      ReferenceGeneratedPrelaunchDownPastFactor.sourcePrefixCode
        rate rewards C_star C_h z i r := by
    change ReferenceGeneratedPrelaunchDownPastFactor.sourcePrefixCode rate rewards
      C_star C_h z i ⟨j.val, Nat.lt_of_lt_of_le j.isLt hn⟩ = _
    congr 1
  have hroundtrip :
      ReferenceGeneratedPrelaunchDownPastFactor.encodePrefix rate
        (ReferenceGeneratedPrelaunchDownPastFactor.decodePrefixCode rate i (codes j i)) =
      codes j i := by
    rw [hdecode, hfamilyCode]
    rfl
  have hcode : codes j i =
      ReferenceGeneratedPrelaunchDownPastFactor.sourcePrefixCode
        rate rewards C_star C_h z i r := by
    calc
      codes j i = ReferenceGeneratedPrelaunchDownPastFactor.encodePrefix rate
          (ReferenceGeneratedPrelaunchDownPastFactor.decodePrefixCode rate i (codes j i)) :=
        hroundtrip.symm
      _ = ReferenceGeneratedPrelaunchDownPastFactor.sourcePrefixCode
          rate rewards C_star C_h z i r := by rw [hdecode]; rfl
  have hcontrolAt : controls j =
      (ReferenceGeneratedPrelaunchDownPrefix.sourceReferenceInput
        rate rewards C_star C_h z).row.2 r := by
    change (ReferenceSourceOwnHistoryContainment.selectedControlPrefix n hn z) j = _
    simp only [ReferenceSourceOwnHistoryContainment.selectedControlPrefix]
    congr 1
  have hrj : r.val < n := by simp [r]
  have hownIndex : j = (⟨r.val, hrj⟩ : Fin n) := by
    apply Fin.ext
    rfl
  change decisionFromPrefixRegisters rate i r (controlCurrentCode i (controls j))
      (ownEntryCode (own player j))
      (ReferenceGeneratedPrelaunchDownPastFactor.prefixRegisters (codes j i)) = _
  rw [hcode, hcontrolAt]
  rw [hownIndex]
  change decisionFromPrefixRegisters rate i r
      (ReferenceInitializationMeasurability.ordinaryRowCode p i
        (ReferenceGeneratedPrelaunchDownPrefix.sourceReferenceInput
          rate rewards C_star C_h z).row r)
      (ownEntryCode (ReferenceSourceOwnHistoryContainment.ownBefore
        rate rewards C_star C_h n hn z player ⟨r.val, hrj⟩))
      (sourcePrefixRegisters rate rewards C_star C_h z i r) = _
  exact decisionFromPrefixRegisters_eq_actual rate rewards C_star C_h n hn r
    hrj i z

/-- Every current prelaunch DOWN failure bit is adapted to the exact strict-past
inspected field.  Its inputs are the dated lossless prefix code, the actual
selected control at that date, and the corresponding original own-history
entry. -/
private def fixedControl (p : ConstructorDimensions.Parameters) :
    ContinuousLearningRows.TimeControl p :=
  (fun _ => ⟨0, le_rfl, zero_lt_one⟩, fun _ => (fun _ => 0, 0))

theorem prelaunchDownFailureAt_measurable_in_inspectedHistorySpace
    (n : ℕ) (hn : n ≤ p.T) (r : Fin p.T) (hr : r.val < n)
    (i : Fin (p.m - 1)) :
    Measurable[ReferenceSourceOwnHistoryContainment.inspectedHistorySpace rate rewards C_star C_h n hn]
      (fun z : SourceInput p =>
        ReferencePrelaunchDownDecisionReadout.prelaunchDownFailureAt
          rate rewards C_star C_h z i r) := by
  let K := K rate rewards C_star C_h n hn
  let j : Fin n := ⟨r.val, hr⟩
  let codes := ReferencePrelaunchInspectedPrefixCode.sourcePrefixCodeFamily
    rate rewards C_star C_h n hn
  let controls := ReferenceSourceOwnHistoryContainment.selectedControlPrefix n hn
  let own := ReferenceSourceOwnHistoryContainment.ownBefore rate rewards C_star C_h n hn
  let player := PublicDiscreteDraws.followerPlayer p.two_le_m
    (ActualReferenceInitializationBlock.refFollower i)
  have hcodes : Measurable[K] codes :=
    ReferencePrelaunchInspectedPrefixCode.sourcePrefixCodeFamily_measurable_in_inspectedHistorySpace
      rate rewards C_star C_h n hn
  have hcode : Measurable[K] (fun z : SourceInput p => codes z j i) :=
    (measurable_pi_apply i).comp ((measurable_pi_apply j).comp hcodes)
  have hcontrols : Measurable[K] controls :=
    ReferenceInspectedPastRoundObservations.selectedControlPrefix_measurable_in_inspectedHistorySpace
      rate rewards C_star C_h n hn
  have hcontrol : Measurable[K] (fun z : SourceInput p => controls z j) :=
    (measurable_pi_apply j).comp hcontrols
  have hrowCode : Measurable[K] (fun z : SourceInput p =>
      controlCurrentCode i (controls z j)) :=
    (measurable_controlCurrentCode i).comp hcontrol
  have hownAll : Measurable[K] own :=
    ReferenceSourceOwnHistoryContainment.ownBefore_measurable_in_inspectedHistorySpace
      rate rewards C_star C_h n hn
  have hownPlayer : Measurable[K] (fun z : SourceInput p => own z player) :=
    (measurable_pi_apply player).comp hownAll
  have hown : Measurable[K] (fun z : SourceInput p => own z player j) :=
    (measurable_pi_apply j).comp hownPlayer
  have hownCode : Measurable[K] (fun z : SourceInput p =>
      ownEntryCode (own z player j)) := (measurable_ownEntryCode).comp hown
  have hregisters : Measurable[K] (fun z : SourceInput p =>
      ReferenceGeneratedPrelaunchDownPastFactor.prefixRegisters (codes z j i)) :=
    (ReferenceGeneratedPrelaunchDownPastFactor.measurable_prefixRegisters rate j.val).comp hcode
  have hdecision := decisionFromPrefixRegisters_measurable rate i
    (Fin.castLE hn j)
  have hfactor : Measurable[K] (fun z : SourceInput p =>
      factorDecision rate rewards C_star C_h n hn z j i) := by
    dsimp [factorDecision]
    exact hdecision.comp (hregisters.prodMk (hrowCode.prodMk hownCode))
  have hdate : Fin.castLE hn j = r := by
    apply Fin.ext
    rfl
  have heq : (fun z : SourceInput p => factorDecision rate rewards C_star C_h n hn z j i) =
      (fun z => ReferencePrelaunchDownDecisionReadout.prelaunchDownFailureAt
        rate rewards C_star C_h z i r) := by
    funext z
    rw [factorDecision_eq_actual rate rewards C_star C_h n hn z j i, hdate]
  rw [← heq]
  exact hfactor

/-- The finite strict-past detector is adapted to the same inspected field.
The Boolean family is assembled only after the prefix, control, and feedback
coordinates at every included original date have been adapted. -/
theorem prelaunchPastDecoderFlag_measurable_in_inspectedHistorySpace
    (n : ℕ) (hn : n ≤ p.T) :
    Measurable[ReferenceSourceOwnHistoryContainment.inspectedHistorySpace rate rewards C_star C_h n hn]
      (fun z : SourceInput p => ReferencePrelaunchDownDecisionReadout.prelaunchPastDecoderFlag
        rate rewards C_star C_h z n hn) := by
  let K := K rate rewards C_star C_h n hn
  let codes := ReferencePrelaunchInspectedPrefixCode.sourcePrefixCodeFamily
    rate rewards C_star C_h n hn
  let controls := ReferenceSourceOwnHistoryContainment.selectedControlPrefix n hn
  let own := ReferenceSourceOwnHistoryContainment.ownBefore rate rewards C_star C_h n hn
  let bits : SourceInput p → ((j : Fin n) → Fin (p.m - 1) → Bool) := fun z j i =>
    factorDecision rate rewards C_star C_h n hn z j i
  let containsTrue : ((j : Fin n) → Fin (p.m - 1) → Bool) → Bool := fun b =>
    decide (∃ j, ∃ i, b j i = true)
  have hcodes : Measurable[K] codes :=
    ReferencePrelaunchInspectedPrefixCode.sourcePrefixCodeFamily_measurable_in_inspectedHistorySpace
      rate rewards C_star C_h n hn
  have hcontrols : Measurable[K] controls :=
    ReferenceInspectedPastRoundObservations.selectedControlPrefix_measurable_in_inspectedHistorySpace
      rate rewards C_star C_h n hn
  have hown : Measurable[K] own :=
    ReferenceSourceOwnHistoryContainment.ownBefore_measurable_in_inspectedHistorySpace
      rate rewards C_star C_h n hn
  have hbits : Measurable[K] bits := by
    apply measurable_pi_iff.mpr
    intro j
    apply measurable_pi_iff.mpr
    intro i
    have hcode : Measurable[K] (fun z : SourceInput p => codes z j i) :=
      (measurable_pi_apply i).comp ((measurable_pi_apply j).comp hcodes)
    have hcontrol : Measurable[K] (fun z : SourceInput p => controls z j) :=
      (measurable_pi_apply j).comp hcontrols
    have hrowCode : Measurable[K] (fun z : SourceInput p =>
        controlCurrentCode i (controls z j)) :=
      (measurable_controlCurrentCode i).comp hcontrol
    have hownPlayer : Measurable[K] (fun z : SourceInput p => own z
        (PublicDiscreteDraws.followerPlayer p.two_le_m
          (ActualReferenceInitializationBlock.refFollower i))) :=
      (measurable_pi_apply (PublicDiscreteDraws.followerPlayer p.two_le_m
        (ActualReferenceInitializationBlock.refFollower i))).comp hown
    have hownAt : Measurable[K] (fun z : SourceInput p => own z
        (PublicDiscreteDraws.followerPlayer p.two_le_m
          (ActualReferenceInitializationBlock.refFollower i)) j) :=
      (measurable_pi_apply j).comp hownPlayer
    have hownCode : Measurable[K] (fun z : SourceInput p => ownEntryCode (own z
        (PublicDiscreteDraws.followerPlayer p.two_le_m
          (ActualReferenceInitializationBlock.refFollower i)) j)) :=
      (measurable_ownEntryCode).comp hownAt
    have hregisters : Measurable[K] (fun z : SourceInput p =>
        ReferenceGeneratedPrelaunchDownPastFactor.prefixRegisters (codes z j i)) :=
      (ReferenceGeneratedPrelaunchDownPastFactor.measurable_prefixRegisters rate j.val).comp hcode
    have hdecision := decisionFromPrefixRegisters_measurable rate i
      (Fin.castLE hn j)
    have hfactor : Measurable[K] (fun z : SourceInput p =>
        factorDecision rate rewards C_star C_h n hn z j i) := by
      dsimp [factorDecision]
      exact hdecision.comp (hregisters.prodMk (hrowCode.prodMk hownCode))
    exact hfactor
  have hcontains : Measurable containsTrue := measurable_of_countable _
  have hfactor : Measurable[K] (fun z : SourceInput p => containsTrue (bits z)) :=
    hcontains.comp hbits
  have hEq : (fun z : SourceInput p => containsTrue (bits z)) =
      fun z : SourceInput p => ReferencePrelaunchDownDecisionReadout.prelaunchPastDecoderFlag
        rate rewards C_star C_h z n hn := by
    funext z
    apply Bool.eq_iff_iff.mpr
    simp only [containsTrue, bits,
      ReferencePrelaunchDownDecisionReadout.prelaunchPastDecoderFlag,
      decide_eq_true_eq]
    constructor
    · rintro ⟨j, i, hbit⟩
      refine ⟨j, i, ?_⟩
      rw [← factorDecision_eq_actual rate rewards C_star C_h n hn z j i]
      exact hbit
    · rintro ⟨j, i, hreadout⟩
      refine ⟨j, i, ?_⟩
      rw [factorDecision_eq_actual rate rewards C_star C_h n hn z j i]
      exact hreadout
  rw [← hEq]
  exact hfactor

/-- Each current-date failure bit is also Borel on the unchanged original
source space, by the same inspected-field containment. -/
theorem prelaunchDownFailureAt_measurable
    (n : ℕ) (hn : n ≤ p.T) (r : Fin p.T) (hr : r.val < n)
    (i : Fin (p.m - 1)) :
    Measurable (fun z : SourceInput p =>
      ReferencePrelaunchDownDecisionReadout.prelaunchDownFailureAt
        rate rewards C_star C_h z i r) :=
  (prelaunchDownFailureAt_measurable_in_inspectedHistorySpace
    rate rewards C_star C_h n hn r hr i).mono
    (ReferenceSourceOwnHistoryContainment.inspectedHistorySpace_le_original
      rate rewards C_star C_h (fixedControl p) n hn) le_rfl

theorem prelaunchPastDecoderFlag_true_measurableSet_in_inspectedHistorySpace
    (n : ℕ) (hn : n ≤ p.T) :
    MeasurableSet[ReferenceSourceOwnHistoryContainment.inspectedHistorySpace rate rewards C_star C_h n hn]
      {z : SourceInput p | ReferencePrelaunchDownDecisionReadout.prelaunchPastDecoderFlag
        rate rewards C_star C_h z n hn = true} :=
  measurableSet_preimage
    (prelaunchPastDecoderFlag_measurable_in_inspectedHistorySpace
      rate rewards C_star C_h n hn) (measurableSet_singleton true)

theorem prelaunchPastDecoderFlag_false_measurableSet_in_inspectedHistorySpace
    (n : ℕ) (hn : n ≤ p.T) :
    MeasurableSet[ReferenceSourceOwnHistoryContainment.inspectedHistorySpace rate rewards C_star C_h n hn]
      {z : SourceInput p | ReferencePrelaunchDownDecisionReadout.prelaunchPastDecoderFlag
        rate rewards C_star C_h z n hn = false} :=
  measurableSet_preimage
    (prelaunchPastDecoderFlag_measurable_in_inspectedHistorySpace
      rate rewards C_star C_h n hn) (measurableSet_singleton false)

/-- The whole dated strict-past flag is measurable on the original source
Borel space, using containment in that direction. -/
theorem prelaunchPastDecoderFlag_measurable
    (n : ℕ) (hn : n ≤ p.T) :
    Measurable (fun z : SourceInput p => ReferencePrelaunchDownDecisionReadout.prelaunchPastDecoderFlag
      rate rewards C_star C_h z n hn) :=
  (prelaunchPastDecoderFlag_measurable_in_inspectedHistorySpace
    rate rewards C_star C_h n hn).mono
    (ReferenceSourceOwnHistoryContainment.inspectedHistorySpace_le_original
      rate rewards C_star C_h (fixedControl p) n hn) le_rfl

theorem prelaunchPastDecoderFlag_true_measurableSet
    (n : ℕ) (hn : n ≤ p.T) :
    MeasurableSet {z : SourceInput p |
      ReferencePrelaunchDownDecisionReadout.prelaunchPastDecoderFlag
        rate rewards C_star C_h z n hn = true} :=
  measurableSet_preimage (prelaunchPastDecoderFlag_measurable
    rate rewards C_star C_h n hn) (measurableSet_singleton true)

theorem prelaunchPastDecoderFlag_false_measurableSet
    (n : ℕ) (hn : n ≤ p.T) :
    MeasurableSet {z : SourceInput p |
      ReferencePrelaunchDownDecisionReadout.prelaunchPastDecoderFlag
        rate rewards C_star C_h z n hn = false} :=
  measurableSet_preimage (prelaunchPastDecoderFlag_measurable
    rate rewards C_star C_h n hn) (measurableSet_singleton false)

/-- The false event excludes every follower's DOWN readout at every original
strict-past date. -/
theorem prelaunchPastDecoderFlag_eq_false_iff_no_dated_readout
    (n : ℕ) (hn : n ≤ p.T) (z : SourceInput p) :
    ReferencePrelaunchDownDecisionReadout.prelaunchPastDecoderFlag
        rate rewards C_star C_h z n hn = false ↔
      ∀ j : Fin n, ∀ i : Fin (p.m - 1),
        ReferencePrelaunchDownDecisionReadout.prelaunchDownFailureAt
          rate rewards C_star C_h z i (Fin.castLE hn j) = false := by
  constructor
  · intro h j i
    by_contra hfalse
    have htrue : ReferencePrelaunchDownDecisionReadout.prelaunchDownFailureAt
        rate rewards C_star C_h z i (Fin.castLE hn j) = true := by
      cases hv : ReferencePrelaunchDownDecisionReadout.prelaunchDownFailureAt
          rate rewards C_star C_h z i (Fin.castLE hn j) <;> simp_all
    have hflag : ReferencePrelaunchDownDecisionReadout.prelaunchPastDecoderFlag
        rate rewards C_star C_h z n hn = true := by
      change decide (∃ j' : Fin n, ∃ i' : Fin (p.m - 1),
        ReferencePrelaunchDownDecisionReadout.prelaunchDownFailureAt
          rate rewards C_star C_h z i' (Fin.castLE hn j') = true) = true
      exact decide_eq_true_eq.mpr ⟨j, i, htrue⟩
    rw [h] at hflag
    cases hflag
  · intro h
    by_contra hfalse
    have htrue : ReferencePrelaunchDownDecisionReadout.prelaunchPastDecoderFlag
        rate rewards C_star C_h z n hn = true := by
      cases hv : ReferencePrelaunchDownDecisionReadout.prelaunchPastDecoderFlag
          rate rewards C_star C_h z n hn <;> simp_all
    have hex : ∃ j : Fin n, ∃ i : Fin (p.m - 1),
        ReferencePrelaunchDownDecisionReadout.prelaunchDownFailureAt
          rate rewards C_star C_h z i (Fin.castLE hn j) = true := by
      simpa [ReferencePrelaunchDownDecisionReadout.prelaunchPastDecoderFlag] using htrue
    obtain ⟨j, i, hj⟩ := hex
    have hf := h j i
    rw [hj] at hf
    cases hf

/-- The exact current-date source readout is the admitted same-date ordinary
block decision. This public copy keeps the dated replay interface available to
consumers of the strict-past exclusion theorem. -/
abbrev prelaunchDownFailureAt_sameDateBlockDecisions
    (z : SourceInput p) (i : Fin (p.m - 1)) (r : Fin p.T) :=
  ReferencePrelaunchDownDecisionReadout.prelaunchDownFailureAt_sameDateBlockDecisions
    rate rewards C_star C_h z i r

/-- The strict-past false event is equivalently the absence of every dated
same-date source readout. The preceding theorem identifies each readout with
the current ordinary accepted DOWN decision in its actual calendar block. -/
theorem prelaunchPastDecoderFlag_eq_false_iff_no_dated_sameDateReadout
    (n : ℕ) (hn : n ≤ p.T) (z : SourceInput p) :
    ReferencePrelaunchDownDecisionReadout.prelaunchPastDecoderFlag
        rate rewards C_star C_h z n hn = false ↔
      ∀ j : Fin n, ∀ i : Fin (p.m - 1),
        ¬ (ReferencePrelaunchDownDecisionReadout.prelaunchDownFailureAt
          rate rewards C_star C_h z i (Fin.castLE hn j) = true) := by
  rw [prelaunchPastDecoderFlag_eq_false_iff_no_dated_readout
    rate rewards C_star C_h n hn z]
  constructor
  · intro h j i htrue
    have hfalse := h j i
    rw [htrue] at hfalse
    cases hfalse
  · intro h j i
    by_contra hfalse
    have htrue : ReferencePrelaunchDownDecisionReadout.prelaunchDownFailureAt
        rate rewards C_star C_h z i (Fin.castLE hn j) = true := by
      cases hv : ReferencePrelaunchDownDecisionReadout.prelaunchDownFailureAt
          rate rewards C_star C_h z i (Fin.castLE hn j) <;> simp_all
    exact h j i htrue

/-- The existing empty-prefix and successor identities are exposed verbatim.
A decision at round `n` first enters the flag at `n + 1`; the next strict-past
date is the first one that excludes it. -/
theorem prelaunchPastDecoderFlag_zero (z : SourceInput p) :
    ReferencePrelaunchDownDecisionReadout.prelaunchPastDecoderFlag
      rate rewards C_star C_h z 0 (Nat.zero_le p.T) = false :=
  ReferencePrelaunchDownDecisionReadout.prelaunchPastDecoderFlag_zero
    rate rewards C_star C_h z

theorem prelaunchPastDecoderFlag_succ (z : SourceInput p) (n : ℕ)
    (hn : n + 1 ≤ p.T) :
    ReferencePrelaunchDownDecisionReadout.prelaunchPastDecoderFlag
        rate rewards C_star C_h z (n + 1) hn =
      (ReferencePrelaunchDownDecisionReadout.prelaunchPastDecoderFlag
          rate rewards C_star C_h z n (Nat.le_of_succ_le hn) ||
        decide (∃ i : Fin (p.m - 1),
          ReferencePrelaunchDownDecisionReadout.prelaunchDownFailureAt
            rate rewards C_star C_h z i ⟨n, hn⟩ = true)) :=
  ReferencePrelaunchDownDecisionReadout.prelaunchPastDecoderFlag_succ
    rate rewards C_star C_h z n hn

end Bandits.Support.ReferencePrelaunchInspectedDecoderPast

end
