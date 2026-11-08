/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionUpConditionalService
public import Bandits.Support.ReferenceFirstCollectionStreamEmptyDispatch

import Lean.Elab.Tactic.Omega

/-!
# First cutoff fresh control and old DOWN geometry

Sources: `sources/zip4/manuscript/06_interruptions.tex:477-481`,
`sources/zip4/manuscript/05_binary_transport.tex:33-48,72-78,94-124`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:44-60,100-106`.

This module proves root-driven geometry for the actual first cutoff, including
its live coordinator and prepared ordinary followers. It also proves the local
ordinary OLD DOWN event equivalence from explicit gate, domain, and physical
action facts. Those local facts are not yet derived uniformly for every fresh
control here. The module proves no DOWN probability, service interval, or
regret conclusion.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions
open ActiveRoundActions
open PublicDiscreteDraws
open OrderedTupleSampler
open AffineChannelLaw

namespace Bandits.Support.ReferenceFirstCutoffDownControlGeometry

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev SourceInput := BootstrapPrivateRoundStreams.SourceInput
abbrev RewardTable := ActualInitializationPhysicalStep.GridRewardTable

variable {p : Parameters} {rate : RateInput p}

local instance propDecidable (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition

private theorem bit_eq_zero_or_one (a : AffineChannelLaw.Bit) : a = 0 ∨ a = 1 := by
  have ha : a.val < 2 := ZMod.val_lt a
  interval_cases hval : a.val
  · left
    calc
      a = (a.val : AffineChannelLaw.Bit) := (ZMod.natCast_zmod_val a).symm
      _ = 0 := by rw [hval]; rfl
  · right
    calc
      a = (a.val : AffineChannelLaw.Bit) := (ZMod.natCast_zmod_val a).symm
      _ = 1 := by rw [hval]; rfl

/-- Physical DOWN positivity from the literal affine sender and prepared
tuple actions. The gate and both action equations are explicit hypotheses;
this helper does not claim that they hold for a particular cutoff. -/
theorem old_down_positive_eq_decide_of_prepared_actions
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (i : Fin (p.m - 1))
    (hindex : ReferenceActivePhysicalStep.upSenderIndex x = i)
    (word : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (hgate : ReferenceActiveAffinePositiveTest.downGate x = true)
    (hcoordinator : (ReferenceActivePhysicalStep.prepare x).arms.actions
        (ActiveRoundActions.coordinator p.two_le_m) =
      ActiveRoundActions.sendArm
        (AffineChannelLaw.affineHash ((x.row.2 x.time).2 (0, i)) word)
        ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K (x.row.2 x.time).1).val
          (ActiveRoundActions.coordinator p.two_le_m))
        ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K (x.row.2 x.time).1).val
          (PublicDiscreteDraws.followerPlayer p.two_le_m i)))
    (hfollower : ∀ j : Fin (p.m - 1),
      (ReferenceActivePhysicalStep.prepare x).arms.actions
          (PublicDiscreteDraws.followerPlayer p.two_le_m j) =
        (OrderedTupleSampler.sample p.two_le_m p.m_lt_K (x.row.2 x.time).1).val
          (PublicDiscreteDraws.followerPlayer p.two_le_m j)) :
    ReferenceActiveAffinePositiveTest.downPositive x =
      decide (AffineChannelLaw.affineHash ((x.row.2 x.time).2 (0, i)) word = 1 ∧
        0 < x.rewards x.time
          ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K (x.row.2 x.time).1).val
            (PublicDiscreteDraws.followerPlayer p.two_le_m i))) := by
  let tuple := OrderedTupleSampler.sample p.two_le_m p.m_lt_K (x.row.2 x.time).1
  let focal := PublicDiscreteDraws.followerPlayer p.two_le_m i
  let coord := ActiveRoundActions.coordinator p.two_le_m
  let hash := AffineChannelLaw.affineHash ((x.row.2 x.time).2 (0, i)) word
  let actions := (ReferenceActivePhysicalStep.prepare x).arms.actions
  change actions coord = ActiveRoundActions.sendArm hash (tuple.val coord) (tuple.val focal)
    at hcoordinator
  change ∀ j : Fin (p.m - 1),
      actions (PublicDiscreteDraws.followerPlayer p.two_le_m j) =
        tuple.val (PublicDiscreteDraws.followerPlayer p.two_le_m j) at hfollower
  have hcoordNe : coord ≠ focal := ActiveRoundActions.followerPlayer_ne_coordinator
    p.two_le_m i |>.symm
  have hcollision : FiniteBanditModel.collisionFreeFor actions focal ↔ hash = 1 := by
    constructor
    · intro hfree
      by_contra hnotOne
      have hzero : hash = 0 := by
        have hcase := bit_eq_zero_or_one hash
        rcases hcase with hz | ho
        · exact hz
        · exact (hnotOne ho).elim
      have hsame : actions coord = actions focal := by
        rw [hcoordinator, hfollower i]
        simp [ActiveRoundActions.sendArm, hash, hzero, tuple, focal]
      exact (hfree coord hcoordNe) hsame
    · intro hone player hplayerNe
      rcases ActiveRoundActions.player_cases p.two_le_m player with hcoordPlayer | ⟨j, hplayer⟩
      · subst player
        rw [hcoordinator, hfollower i]
        have hneq : tuple.val coord ≠ tuple.val focal := by
          intro heq
          exact ActiveRoundActions.followerPlayer_ne_coordinator p.two_le_m i
            (tuple.property heq).symm
        simpa [ActiveRoundActions.sendArm, hone] using hneq
      · subst player
        have hji : j ≠ i := by
          intro heq
          apply hplayerNe
          exact congrArg (PublicDiscreteDraws.followerPlayer p.two_le_m) heq
        rw [hfollower j, hfollower i]
        exact fun heq => hji (ActiveRoundActions.followerPlayer_injective p.two_le_m
          ((tuple.property heq)))
  have hfeedback :
      (ReferenceActiveFeedbackCut.collisionFeedbackVector actions x.time x.rewards focal) =
        if hash = 1 then x.rewards x.time (tuple.val focal) else 0 := by
    rw [ReferenceActiveFeedbackCut.collisionFeedbackVector_apply]
    rw [hcollision]
    have hact : actions focal = tuple.val focal := by simpa [focal] using hfollower i
    by_cases hh : hash = 1 <;> simp [hh, hact]
  rw [ReferenceActiveAffinePositiveTest.downPositive_eq_gate_feedback, hgate, hindex]
  rw [hfeedback]
  by_cases hh : hash = 1 <;> simp [hh, hash, tuple, focal]

/-- The physical DOWN gate is exactly its selected local draw when PREPARE
retains the ordinary unoccupied receiver and its actual carried-field domain.
The two domain inputs are discharged from the lifecycle validator, including
the existing equivalence for the sparse buffer checker. -/
theorem down_gate_eq_decide_downSelected_of_prepared_unoccupied
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (i : Fin (p.m - 1))
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hindex : ReferenceActivePhysicalStep.upSenderIndex x = i)
    (hconfiguration :
      ((ReferenceActivePhysicalStep.prepare x).followers.followers i).configuration =
        .ordinary state memory)
    (hstatus : state.status = .unoccupied)
    (hvalid : ActiveFollowerLifecycle.localStateDomainValid state) :
    ReferenceActiveAffinePositiveTest.downGate x = decide
      (ActiveFollowerDownAcceptance.downSelected p i x.row x.time) := by
  classical
  have hregisters : ActiveFollowerDownAcceptance.registerInputDomain p rate state := by
    simpa [ActiveFollowerDownAcceptance.registerInputDomain,
      ActiveFollowerLifecycle.serviceRegistersValid] using hvalid.1
  have hdecoder : ActiveFollowerDownAcceptance.decoderInputDomain p state.downBatch := by
    simpa [ActiveFollowerDownAcceptance.decoderInputDomain,
      ActiveFollowerLifecycle.downDecoderStateValid] using hvalid.2.2
  have hbuffer : ActiveFollowerDownAcceptance.bufferInputDomain p state.buffer :=
    (FollowerLifecycleMeasurability.localBufferValid_iff_bufferInputDomain state).mp hvalid.2.1
  have hreceiver : ReferenceActiveAffinePositiveTest.downReceiverGate i x.row x.time state ↔
      ActiveFollowerDownAcceptance.downSelected p i x.row x.time := by
    unfold ReferenceActiveAffinePositiveTest.downReceiverGate
    constructor
    · intro h
      exact h.1
    · intro hselected
      exact ⟨hselected, hstatus, hregisters, hdecoder, hbuffer⟩
  have hgate :
      (ActiveFollowerLifecycle.localBufferValid state ∧
        ReferenceActiveAffinePositiveTest.downReceiverGate i x.row x.time state) ↔
      ActiveFollowerDownAcceptance.downSelected p i x.row x.time := by
    constructor
    · intro h
      exact hreceiver.mp h.2
    · intro hselected
      exact ⟨hvalid.2.1, hreceiver.mpr hselected⟩
  dsimp only [ReferenceActiveAffinePositiveTest.downGate]
  rw [hindex, hconfiguration]
  change decide (ActiveFollowerLifecycle.localBufferValid state ∧
      ReferenceActiveAffinePositiveTest.downReceiverGate i x.row x.time state) = _
  by_cases hselected : ActiveFollowerDownAcceptance.downSelected p i x.row x.time
  · have hleft : ActiveFollowerLifecycle.localBufferValid state ∧
        ReferenceActiveAffinePositiveTest.downReceiverGate i x.row x.time state :=
      ⟨hvalid.2.1, hreceiver.mpr hselected⟩
    simp [hleft, hselected]
  · have hleft : ¬ (ActiveFollowerLifecycle.localBufferValid state ∧
        ReferenceActiveAffinePositiveTest.downReceiverGate i x.row x.time state) := by
      intro h
      exact hselected (hreceiver.mp h.2)
    simp [hleft, hselected]

/-- Exact old-DOWN event geometry once the actual unoccupied PREPARE,
receiver-domain checks, and the two physical tuple-action equations are
available. A source-root theorem must produce these conditional inputs for
each fresh control; this lemma itself introduces no probability or protocol
assumptions. -/
theorem old_down_event_iff_prepared_unoccupied
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (i : Fin (p.m - 1))
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (word : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (hindex : ReferenceActivePhysicalStep.upSenderIndex x = i)
    (hconfiguration :
      ((ReferenceActivePhysicalStep.prepare x).followers.followers i).configuration =
        .ordinary state memory)
    (hstatus : state.status = .unoccupied)
    (hvalid : ActiveFollowerLifecycle.localStateDomainValid state)
    (hcoordinator : (ReferenceActivePhysicalStep.prepare x).arms.actions
        (ActiveRoundActions.coordinator p.two_le_m) =
      ActiveRoundActions.sendArm
        (AffineChannelLaw.affineHash ((x.row.2 x.time).2 (0, i)) word)
        ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K (x.row.2 x.time).1).val
          (ActiveRoundActions.coordinator p.two_le_m))
        ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K (x.row.2 x.time).1).val
          (PublicDiscreteDraws.followerPlayer p.two_le_m i)))
    (hfollower : ∀ j : Fin (p.m - 1),
      (ReferenceActivePhysicalStep.prepare x).arms.actions
          (PublicDiscreteDraws.followerPlayer p.two_le_m j) =
        (OrderedTupleSampler.sample p.two_le_m p.m_lt_K (x.row.2 x.time).1).val
          (PublicDiscreteDraws.followerPlayer p.two_le_m j)) :
    (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
        (x.row.2 x.time).1 = i ∧
      ReferenceActiveAffinePositiveTest.downPositive x = true) ↔
    (PublicDiscreteDraws.slotDraw (x.row.2 x.time).1 = PublicDiscreteDraws.downSlot ∧
      PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
        (x.row.2 x.time).1 = i ∧
      AffineChannelLaw.affineHash ((x.row.2 x.time).2 (0, i)) word = 1 ∧
      0 < x.rewards x.time
        ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K (x.row.2 x.time).1).val
          (PublicDiscreteDraws.followerPlayer p.two_le_m i))) := by
  have hgate := down_gate_eq_decide_downSelected_of_prepared_unoccupied
    x i state memory hindex hconfiguration hstatus hvalid
  constructor
  · rintro ⟨hdraw, hpositive⟩
    have hbits : ReferenceActiveAffinePositiveTest.downGate x = true ∧
        decide (0 < (ReferenceActiveFeedbackCut.collisionFeedbackVector
          (ReferenceActivePhysicalStep.prepare x).arms.actions x.time x.rewards
          (PublicDiscreteDraws.followerPlayer p.two_le_m
            (ReferenceActivePhysicalStep.upSenderIndex x))).val) = true := by
      have hprod := hpositive
      rw [ReferenceActiveAffinePositiveTest.downPositive_eq_gate_feedback x] at hprod
      exact Bool.and_eq_true_iff.mp hprod
    have hselected : ActiveFollowerDownAcceptance.downSelected p i x.row x.time := by
      rw [hgate] at hbits
      exact of_decide_eq_true hbits.1
    have hgeometry := old_down_positive_eq_decide_of_prepared_actions
      x i hindex word hbits.1 hcoordinator hfollower
    rw [hgeometry] at hpositive
    have hhashReward := of_decide_eq_true hpositive
    exact ⟨hselected.1, hdraw, hhashReward.1, hhashReward.2⟩
  · rintro ⟨hslot, hdraw, hhash, hreward⟩
    have hselected : ActiveFollowerDownAcceptance.downSelected p i x.row x.time :=
      ⟨hslot, hdraw⟩
    have hgateTrue : ReferenceActiveAffinePositiveTest.downGate x = true := by
      rw [hgate]
      exact decide_eq_true hselected
    have hgeometry := old_down_positive_eq_decide_of_prepared_actions
      x i hindex word hgateTrue hcoordinator hfollower
    refine ⟨hdraw, ?_⟩
    rw [hgeometry]
    exact decide_eq_true ⟨hhash, hreward⟩

/-- The stream root and follower-preparation producer expose the actual
first-cutoff input, its live coordinator, and every incoming follower together
with the literal status reset performed before local CHOICE. -/
theorem actual_first_cutoff_source_geometry
    (rate : RateInput p) (source : SourceInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (count : ℕ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hspan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed +
          count ≤ p.T)
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
        rate source rewards C_star C_h hcross count hspan).records).length < count) :
    let E := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
      rate source rewards C_star C_h hcross count hspan
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records).length
    let B := ReferenceCollectionPhaseHistory.collectionWindow E.records w
    ∃ d : ReferenceFirstCollectionStreamEmptyDispatch.ActualInitializedStreamDispatch
        source rewards C_star C_h count hcross hspan hshort,
      let out := d.stream
      out.window = B ∧
      out.window[0]'(by exact out.windowNonempty) = out.cutoff.cut ∧
      out.cutoff.cut.input.time.val =
        ReferenceInitializationRun.elapsed p
          (ReferenceInitializationRun.output
            (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed + w ∧
      out.cutoff.cut.input.rows = source.1.2 ∧
      out.cutoff.cut.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p source ∧
      out.cutoff.cut.input.rewards = rewards ∧
      ∃ r q base,
        out.cutoff.cut.input.state.coordinator = .live r q base ∧
        out.payload = r.payload ∧
        (∀ i : Fin (p.m - 1),
          ∃ s_i memory_i,
            out.cutoff.cut.input.state.followers i = .ordinary s_i memory_i ∧
            let c_i : ReferencePrelaunchFollower.State p rate.eta :=
              { s_i with status := .unoccupied }
            c_i.status = .unoccupied ∧
            c_i.lastDown = s_i.lastDown ∧ c_i.S = s_i.S ∧
            c_i.delta = s_i.delta ∧ c_i.backlog = s_i.backlog ∧
            c_i.buffer = s_i.buffer ∧ c_i.downBatch = s_i.downBatch ∧
            c_i.initializationFailure = s_i.initializationFailure ∧
            ActiveFollowerLifecycle.localStateDomainValid c_i ∧
            ActiveFollowerLifecycle.startRound rate.eta out.cutoff.cut.input.time
              s_i memory_i = .ok (c_i, memory_i)) := by
  classical
  let E := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
    rate source rewards C_star C_h hcross count hspan
  let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records).length
  let B := ReferenceCollectionPhaseHistory.collectionWindow E.records w
  have hspanStream : ReferenceFirstCollectionReadyStream.startTime
      (rate := rate) source rewards C_star C_h + count ≤ p.T := by
    exact hspan
  have hshortOriginal : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
        source rewards C_star C_h hcross count hspanStream).records).length < count := by
    simpa [ReferenceFirstCollectionReadyStream.actualEpoch] using hshort
  have hshortGenerated := ReferenceFirstCollectionReadyStream.generatedFirstCutoffRun_short
    source rewards C_star C_h hcross count hspanStream hshortOriginal
  obtain ⟨d⟩ := ReferenceFirstCollectionStreamEmptyDispatch.actual_initialized_first_collection_stream_empty_dispatch
    rate source rewards C_star C_h count hcross hspan hshort
  let out := d.stream
  have hwindow : out.window = B := by
    rw [out.windowIsActual]
    rfl
  let hheadFin : Fin out.window.length := ⟨0, by have hn := out.windowNonempty; omega⟩
  have hhead := out.alignment hheadFin
  have hcutHead : out.window[0]'(by have hn := out.windowNonempty; omega) = out.cutoff.cut := out.cutoffIsHead
  have htimeWindow : (out.window[0]'(by have hn := out.windowNonempty; omega)).input.time.val + 1 =
      ReferenceInitializationRun.elapsed p
        (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed + w + 1 := by
    simpa [ReferenceFirstCollectionReadyStream.actualEpoch,
      ReferenceFirstCollectionReadyStream.startTime, E, hheadFin, w] using hhead.2
  have htimeCut : out.cutoff.cut.input.time.val =
      ReferenceInitializationRun.elapsed p
        (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed + w := by
    rw [← hcutHead]
    omega
  have hsourceWindowInputs := out.originalInputs hheadFin
  have hsourceHeadRows : (out.window[0]'(by have hn := out.windowNonempty; omega)).input.rows = source.1.2 := by
    simpa [hheadFin] using hsourceWindowInputs.1
  have hsourceHeadSelected : (out.window[0]'(by have hn := out.windowNonempty; omega)).input.selected =
      ActualInitializationPhysicalStep.selectedRowIndex p source := by
    simpa [hheadFin] using hsourceWindowInputs.2.1
  have hsourceHeadRewards : (out.window[0]'(by have hn := out.windowNonempty; omega)).input.rewards = rewards := by
    simpa [hheadFin] using hsourceWindowInputs.2.2
  have hcutRows : out.cutoff.cut.input.rows = source.1.2 := by
    rw [← hcutHead]
    exact hsourceHeadRows
  have hcutSelected : out.cutoff.cut.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p source := by
    rw [← hcutHead]
    exact hsourceHeadSelected
  have hcutRewards : out.cutoff.cut.input.rewards = rewards := by
    rw [← hcutHead]
    exact hsourceHeadRewards
  let initial := ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hcross
  let seed := ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffSeed
    rate source rewards C_star C_h
  let memory := ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffMemory (p := p)
  let active := ReferenceGeneratedFirstCutoffSurvival.generatedLaunchActive
    rate source rewards C_star C_h hcross
      (ReferenceInitializationRun.elapsed p
        (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed)
      rfl
  have hgenerated := ReferenceGeneratedFirstCutoffSurvival.run_generated_first_cutoff_survival
    rate source rewards C_star C_h hcross
    (ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed)
    rfl count hspan hshortGenerated
  dsimp only [initial, active] at hgenerated
  rcases hgenerated with ⟨hactive, hfirst, _hbank, _hlearner, _hqueue, hseed, hcutoff⟩
  have hseedOrd : ∀ i, initial.followers i = .ordinary (seed i) (memory i) := by
    intro i
    exact (hseed i).1
  have hseedS : ∀ i, (seed i).S = 0 := by
    intro i
    exact (hseed i).2.2.1
  have hseedDelta : ∀ i, (seed i).delta = 0 := by
    intro i
    exact (hseed i).2.2.2.1
  have hseedBacklog : ∀ i, (seed i).backlog = 0 := by
    intro i
    exact (hseed i).2.2.2.2.1
  have hseedNone : ∀ i, (seed i).lastDown = none := by
    intro i
    exact (hseed i).2.1
  have hseedUnoccupied : ∀ i, (seed i).status = .unoccupied := by
    intro i
    exact (hseed i).2.2.2.2.2.1
  have hseedBuffer : ∀ i, ActiveFollowerLifecycle.localBufferValid (seed i) := by
    intro i
    exact (hseed i).2.2.2.2.2.2.2.1
  have hseedPair : ∀ i, (seed i).buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound) := by
    intro i
    exact (hseed i).2.2.2.2.2.2.2.2.1
  have hseedTime : ∀ i saved, saved ∈ (seed i).buffer → saved.calendarRound ≤
      ReferenceInitializationRun.elapsed p
        (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed := by
    intro i saved hs
    exact (hseed i).2.2.2.2.2.2.2.2.2.1 saved hs
  have hseedBatch : ∀ i, ActiveFollowerLifecycle.downDecoderStateValid (seed i) := by
    intro i
    exact (hseed i).2.2.2.2.2.2.2.2.2.2
  have hprepared := ReferenceFirstCutoffFollowerPreparation.run_first_cutoff_follower_preparation
    initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
    (ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed)
    count hspanStream hactive hfirst seed memory hseedOrd hseedS hseedDelta hseedBacklog
    hseedNone hseedUnoccupied hseedBuffer hseedPair hseedTime hseedBatch hshortGenerated
  dsimp only [E, w, B, initial, seed, memory, active,
    ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun] at hprepared
  rcases hprepared with ⟨cut, suffix, _hsplit, hcutIndex, _htime, hstate,
    _hrows, _hselected, _hrewards, hfollowers, _hfeedback, _hentries⟩
  have hrecords :
      (ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun rate source rewards
        C_star C_h hcross
    (ReferenceInitializationRun.elapsed p
          (ReferenceInitializationRun.output
            (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed)
        rfl count hspanStream).records = E.records := by
    exact ReferenceFirstCollectionReadyStream.generatedFirstCutoffRun_records_eq
      source rewards C_star C_h hcross count hspanStream
  have hcutGetGenerated :
      (ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun rate source rewards
        C_star C_h hcross
        (ReferenceInitializationRun.elapsed p
          (ReferenceInitializationRun.output
            (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed)
        rfl count hspanStream).records[w]? = some cut := by
    rw [hcutIndex]
    exact List.getElem?_eq_getElem _
  have hcutGetEpoch : E.records[w]? = some cut := by
    rw [← hrecords]
    exact hcutGetGenerated
  have hrootCut : E.records[w]? = some out.cutoff.cut := out.cutoff.cutIndex
  have hcutEq : cut = out.cutoff.cut := Option.some.inj (hcutGetEpoch.symm.trans hrootCut)
  have hfollowersOut : ∀ i : Fin (p.m - 1),
      ∃ s_i memory_i,
        out.cutoff.cut.input.state.followers i = .ordinary s_i memory_i ∧
        let c_i : ReferencePrelaunchFollower.State p rate.eta :=
          { s_i with status := .unoccupied }
        c_i.status = .unoccupied ∧
        c_i.lastDown = s_i.lastDown ∧ c_i.S = s_i.S ∧ c_i.delta = s_i.delta ∧
        c_i.backlog = s_i.backlog ∧ c_i.buffer = s_i.buffer ∧
        c_i.downBatch = s_i.downBatch ∧ c_i.initializationFailure = s_i.initializationFailure ∧
        ActiveFollowerLifecycle.localStateDomainValid c_i ∧
        ActiveFollowerLifecycle.startRound rate.eta out.cutoff.cut.input.time
          s_i memory_i = .ok (c_i, memory_i) := by
    intro i
    obtain ⟨s_i, memory_i, hstateFollower, _hunoccupied, _hoccupied, hstart,
      _hconfiguration, hlocal, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ :=
        hfollowers i
    have hstateOut : out.cutoff.cut.input.state.followers i = .ordinary s_i memory_i := by
      rw [← hcutEq, hstate]
      exact hstateFollower
    exact ⟨s_i, memory_i, hstateOut,
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hlocal, by simpa [hcutEq] using hstart⟩⟩
  obtain ⟨ce⟩ := out.cutoffExecution
  refine ⟨d, ?_⟩
  refine ⟨hwindow, hcutHead, htimeCut, hcutRows, hcutSelected, hcutRewards,
    ce.live, ce.owned, ce.base, ce.actualLive, ?_, hfollowersOut⟩
  exact out.payloadMatchesCutoff.trans ce.payloadIsLive

end Bandits.Support.ReferenceFirstCutoffDownControlGeometry

end
