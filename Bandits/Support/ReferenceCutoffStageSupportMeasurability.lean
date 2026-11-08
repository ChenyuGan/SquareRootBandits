/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCutoffUpConditionalService

import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Lean.Elab.Tactic.Omega

/-!
# Actual cutoff old and formed-UP stage support

Literal before-current support at the actual first cutoff, on the original
source and the canonical lossless state code. Incoming ordinary followers may
be occupied; the UP branch is selected only after its reply has been formed.

Sources: `sources/zip4/manuscript/06_interruptions.tex:425-426,477-481`,
`sources/zip4/manuscript/05_binary_transport.tex:70-124`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:44-64,100-108`.
No waiting quota, current-row service, global truth, stopped coverage, or
manuscript-filtration equality is asserted. The next consumer is the actual
cutoff OLD/formed stage-service adapter after the separately owned cutoff DOWN
fresh service, followed by stopped collection.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support
open ConstructorDimensions
open scoped Classical

namespace Bandits.Support.ReferenceCutoffStageSupportMeasurability

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev SourceInput := BootstrapPrivateRoundStreams.SourceInput
abbrev RewardTable := ActualInitializationPhysicalStep.GridRewardTable
abbrev TimeControl := ContinuousLearningRows.TimeControl
abbrev RoundRecord (p : Parameters) (rate : RateInput p) :=
  ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)
abbrev StateCode (p : Parameters) (rate : RateInput p) :=
  ReferenceActivePhysicalStepMeasurability.StateCode p rate

variable {p : Parameters} {rate : RateInput p}

local instance downRecordMeasurableSpace : MeasurableSpace
    (OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta)) := ⊤
local instance downRecordDiscreteMeasurableSpace : DiscreteMeasurableSpace
    (OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta)) :=
  ⟨fun _ => trivial⟩

local instance sourceInputMeasurableSpace (p : Parameters) :
    MeasurableSpace (SourceInput p) := by
  change MeasurableSpace
    (CompletePublicTable.PublishedOutput p ×
      BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

/-- Literal OLD-DOWN support at the actual cutoff input. The all-ordinary
condition does not impose an unoccupied status. -/
def cutoffDownStageSupport
    (rewards : RewardTable p) (C_star C_h : ℝ)
    (i : Fin (p.m - 1)) (t : Fin p.T)
    (wD : AffineChannelLaw.Word (AffineBatchDecoder.width p)) :
    Set (SourceInput p) :=
  {z | ∃ r : RoundRecord p rate,
      ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some r ∧
      ∃ (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
        (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
        (base : Fin (p.m - 1) → ℕ),
        r.input.state.coordinator = .live registers owned base ∧
        ReferenceCollectionPhaseHistory.cutoffChosen r.input = true ∧
        (∀ j : Fin (p.m - 1), ∃ old memory,
          r.input.state.followers j = .ordinary old memory) ∧
        ∃ old memory,
          r.input.state.followers i = .ordinary old memory ∧
          old.lastDown = none ∧
          CoordinatorLocalArmChoice.storedDownFlatWord registers.payload i = wD}

/-- Literal formed-UP support at the actual cutoff input. -/
def cutoffUpStageSupport
    (rewards : RewardTable p) (C_star C_h : ℝ)
    (i : Fin (p.m - 1)) (t : Fin p.T)
    (reply : OrdinaryMessageCodec.UpRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta)) :
    Set (SourceInput p) :=
  {z | ∃ r : RoundRecord p rate,
      ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some r ∧
      ∃ (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
        (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
        (base : Fin (p.m - 1) → ℕ),
        r.input.state.coordinator = .live registers owned base ∧
        ReferenceCollectionPhaseHistory.cutoffChosen r.input = true ∧
        (∀ j : Fin (p.m - 1), ∃ old memory,
          r.input.state.followers j = .ordinary old memory) ∧
        ∃ old memory,
          r.input.state.followers i = .ordinary old memory ∧
          1 ≤ ReferencePrelaunchFollower.acceptedStart old ∧
          ActiveFollowerQueueOperation.upOfferFields old = reply.val}

/-- The pre-choice ordinary/dagger tag, keeping the whole original scalar
fibre in the canonical incoming carrier. -/
abbrev FollowerTag (p : Parameters) (rate : RateInput p) :=
  Unit ⊕ FollowerDownMeasurability.FollowerStateCode p rate
abbrev FollowerTags (p : Parameters) (rate : RateInput p) :=
  Fin (p.m - 1) → FollowerTag p rate

/-- The finite payload coordinates used only as a countable dispatch key. The
real anchor is kept separately on its original positive Borel carrier. -/
abbrev QueueCode (p : Parameters) :=
  {q : Fin p.K → ℕ // ∀ a, q a ≤ p.T * D p}
abbrev PayloadDiscreteCode (p : Parameters) :=
  ℕ × (Fin p.T ×
    (CanonicalOrientedSetLaw.SlowSet p.K p.m × QueueCode p))
abbrev StageCodeKey (p : Parameters) (rate : RateInput p) :=
  PayloadDiscreteCode p ×
    (ReferenceActivePhysicalStepMeasurability.LiveDiscrete p ×
      (Fin p.T × FollowerTags p rate))
abbrev StageCodeView (p : Parameters) (rate : RateInput p) :=
  Unit ⊕ (LaterAssignmentAnchorMeasurability.PositiveAnchor p × StageCodeKey p rate)

def followerStateTag (x : FollowerPrepareJointMeasurability.IncomingConfiguration p rate) :
    FollowerTag p rate :=
  match x with
  | none => Sum.inl ()
  | some (carried, _) => Sum.inr carried.1.1

def followerStateCodeTags (c : StateCode p rate) : FollowerTags p rate :=
  fun j => followerStateTag (c.2.2.2 j)

def payloadDiscreteCode (payload : ReferenceActivePhysicalStep.Payload rate) :
    PayloadDiscreteCode p :=
  (payload.n, (payload.sigma,
    (payload.slowSet, ⟨payload.queues, payload.queues_le_TD⟩)))

def payloadWithUnitAnchor (sigma : Fin p.T)
    (slowSet : CanonicalOrientedSetLaw.SlowSet p.K p.m) (queues : QueueCode p) :
    ReferenceActivePhysicalStep.Payload rate := {
  eta_le_source_cap := rate.sourceCap
  n := rate.n
  n_eq_eta_mul_D := rate.n_scale
  sigma := sigma
  slowSet := slowSet
  anchor := fun _ => 1
  anchor_pos := by intro; norm_num
  queues := queues.1
  queues_le_TD := queues.2
}

def payloadFromStageCodeKey (anchor : LaterAssignmentAnchorMeasurability.PositiveAnchor p)
    (key : StageCodeKey p rate) : ReferenceActivePhysicalStep.Payload rate :=
  LaterAssignmentAnchorMeasurability.payloadWithAnchor
    (payloadWithUnitAnchor (p := p) (rate := rate)
      key.1.2.1 key.1.2.2.1 key.1.2.2.2) anchor

private def positiveUnitAnchor : LaterAssignmentAnchorMeasurability.PositiveAnchor p :=
  ⟨fun _ => 1, by intro; norm_num⟩

private theorem payloadFromStageCodeKey_reanchor
    (anchor : LaterAssignmentAnchorMeasurability.PositiveAnchor p)
    (key : StageCodeKey p rate) :
    payloadFromStageCodeKey (p := p) (rate := rate) anchor key =
      LaterAssignmentAnchorMeasurability.payloadWithAnchor
        (payloadFromStageCodeKey (p := p) (rate := rate) positiveUnitAnchor key) anchor := by
  rcases key with ⟨⟨n, ⟨sigma, ⟨slow, queues⟩⟩⟩, ⟨live, ⟨time, tags⟩⟩⟩
  rfl

/-- Project the canonical state code to its actual live payload anchor and
countable discrete inputs; non-LIVE coordinator summands collapse to `none`.
The real anchor and follower saved-real fibres are not discretized. -/
def cutoffStageCodeView (t : Fin p.T) (c : StateCode p rate) : StageCodeView p rate :=
  let tags := followerStateCodeTags (p := p) (rate := rate) c
  match c.1 with
  | .inr (.inl (payload, live)) =>
      .inr (⟨payload.anchor, payload.anchor_pos⟩,
        (payloadDiscreteCode (p := p) (rate := rate) payload, (live, (t, tags))))
  | _ => .inl ()

/-- A successful, row-free cutoff test on the original LIVE code. The
dispatcher is the actual one-call StartRound dispatch. The selected arm is
not stored in this tag; `ChoiceInputsValid` is retained so its existence is a
theorem about the actual input, not a default or fallback. -/
def cutoffStageDispatchCheck
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (live : ReferenceActivePhysicalStepMeasurability.LiveDiscrete p)
    (t : Fin p.T) : Prop :=
  let registers := ReferenceActivePhysicalStep.liveRegistersAt
    (ReferenceActivePhysicalStepMeasurability.decodeLiveRegisters payload live) t
  let owned := ReferenceActivePhysicalStep.liveOwnedAt
    (ReferenceActivePhysicalStepMeasurability.decodeLiveRegisters payload live)
    (ReferenceActivePhysicalStepMeasurability.decodeLiveOwned payload live) t
  ∃ out : CoordinatorStartRoundCutoffDispatch.Output registers owned live.baseScores,
    CoordinatorStartRoundCutoffDispatch.dispatch registers owned live.baseScores = .ok out ∧
    (∃ ledger, out.collectionInitialization = .success (some ledger)) ∧
    CoordinatorLocalArmChoice.ChoiceInputsValid payload
      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p out.startResult.clock.u)
      t registers.complementWeights ∧
    out.startResult.clock.g ≤ p.T + 1 ∧ registers.complementEnvelopeValid

/-- Countable-register part of the code support. Every incoming follower tag
is ordinary, and the focal code is either the old-DOWN or formed-UP branch. -/
def cutoffStageDiscreteCheck
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (_i : Fin (p.m - 1)) (t : Fin p.T) (key : StageCodeKey p rate) : Prop :=
  let live := key.2.1
  let tags := key.2.2.2
  cutoffStageDispatchCheck payload live t ∧
  (∀ j : Fin (p.m - 1), ∃ follower, tags j = Sum.inr follower)

/-- The focal old-DOWN code check uses the payload's actual canonical encoding
and the FollowerStateCode registers. -/
def cutoffDownStageCodeCheck
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (i : Fin (p.m - 1)) (t : Fin p.T)
    (wD : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (key : StageCodeKey p rate) : Prop :=
  cutoffStageDiscreteCheck payload i t key ∧
    ∃ follower, key.2.2.2 i = Sum.inr follower ∧
      follower.lastDown = none ∧
      CoordinatorLocalArmChoice.storedDownFlatWord payload i = wD

/-- The focal formed-UP code check reads exactly the four encoded reply
registers. No acceptance date or successful solver is included. -/
def cutoffUpStageCodeCheck
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (i : Fin (p.m - 1)) (t : Fin p.T)
    (reply : OrdinaryMessageCodec.UpRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))
    (key : StageCodeKey p rate) : Prop :=
  cutoffStageDiscreteCheck payload i t key ∧
    ∃ follower, key.2.2.2 i = Sum.inr follower ∧
      1 ≤ follower.lastDown.elim 0 (fun d => d.val.sigma) ∧
      ({ sigma := follower.lastDown.elim 0 (fun d => d.val.sigma),
         S := follower.S, delta := follower.delta, q := follower.backlog } :
        OrdinaryMessageCodec.UpFields) = reply.val

def cutoffDownStageCodeViewSet
    (i : Fin (p.m - 1)) (t : Fin p.T)
    (wD : AffineChannelLaw.Word (AffineBatchDecoder.width p)) :
    Set (StageCodeView p rate) :=
  {view | ∃ anchor key, view = Sum.inr (anchor, key) ∧
    cutoffDownStageCodeCheck (payloadFromStageCodeKey (p := p) (rate := rate) anchor key)
      i t wD key}

def cutoffUpStageCodeViewSet
    (i : Fin (p.m - 1)) (t : Fin p.T)
    (reply : OrdinaryMessageCodec.UpRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta)) :
    Set (StageCodeView p rate) :=
  {view | ∃ anchor key, view = Sum.inr (anchor, key) ∧
    cutoffUpStageCodeCheck (payloadFromStageCodeKey (p := p) (rate := rate) anchor key)
      i t reply key}

def cutoffDownStageSupportCodeSet
    (i : Fin (p.m - 1)) (t : Fin p.T)
    (wD : AffineChannelLaw.Word (AffineBatchDecoder.width p)) :
    Set (Option (StateCode p rate)) :=
  {c | ∃ code, c = some code ∧
    cutoffStageCodeView t code ∈ cutoffDownStageCodeViewSet (p := p) (rate := rate) i t wD}

def cutoffUpStageSupportCodeSet
    (i : Fin (p.m - 1)) (t : Fin p.T)
    (reply : OrdinaryMessageCodec.UpRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta)) :
    Set (Option (StateCode p rate)) :=
  {c | ∃ code, c = some code ∧
    cutoffStageCodeView t code ∈ cutoffUpStageCodeViewSet (p := p) (rate := rate) i t reply}

private theorem sourcePrefix_replaceSourceControl
    (control0 : TimeControl p) (t : Fin p.T) (z : SourceInput p)
    (c : TimeControl p) :
    ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z c) =
      ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z := by
  apply Prod.ext
  · refine Prod.ext rfl ?_
    funext q
    have hselected : ActualInitializationPhysicalStep.selectedRowIndex p
          (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z c) =
        ActualInitializationPhysicalStep.selectedRowIndex p z := by
      rw [← ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex,
        ← ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex]
      rfl
    by_cases hq : q = ActualInitializationPhysicalStep.selectedRowIndex p z
    · subst q
      have hrow := ReferenceFixedTimeSourceControlCoupling.replaceSourceControl_forward p t z c
      apply Prod.ext
      · rw [ReferenceSourcePrefixHistoryFiltration.sourcePrefix_forward control0 t.val
          (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z c)
          (ActualInitializationPhysicalStep.selectedRowIndex p z),
          ReferenceSourcePrefixHistoryFiltration.sourcePrefix_forward control0 t.val z
          (ActualInitializationPhysicalStep.selectedRowIndex p z)]
        simpa [ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex]
          using hrow
      · funext v
        have hleft := ReferenceSourcePrefixHistoryFiltration.sourcePrefix_control control0 t.val
          (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z c) v
        rw [hselected] at hleft
        have hright := ReferenceSourcePrefixHistoryFiltration.sourcePrefix_control control0 t.val z v
        rw [hleft, hright]
        by_cases hv : v.val < t.val
        · have hvt : v ≠ t := by
            intro h
            subst v
            omega
          simp only [ite_eq_left hv]
          simp only [ReferenceFixedTimeSourceControlCoupling.replaceSourceControl,
            ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex p z,
            Function.update_self]
          exact Function.update_of_ne hvt c
            (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)).2
        · simp [hv]
    · have hq' : q ≠ ActualInitializationPhysicalStep.selectedRowIndex p
          (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z c) := by
        intro h
        apply hq
        exact h.trans hselected
      rw [ReferenceSourcePrefixHistoryFiltration.sourcePrefix_otherRow control0 t.val
          (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z c) q hq',
        ReferenceSourcePrefixHistoryFiltration.sourcePrefix_otherRow control0 t.val z q hq]
      simp only [ReferenceFixedTimeSourceControlCoupling.replaceSourceControl]
      rw [ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex p z]
      exact Function.update_of_ne hq
        (((z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)).1,
          Function.update (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)).2 t c))
        z.1.2
  · rfl

private abbrev DownStageCodeBranch (p : Parameters) (rate : RateInput p) :=
  LaterAssignmentAnchorMeasurability.PositiveAnchor p × StageCodeKey p rate

private def cutoffDownStageCodeBranchSet
    (i : Fin (p.m - 1)) (t : Fin p.T)
    (wD : AffineChannelLaw.Word (AffineBatchDecoder.width p)) :
    Set (DownStageCodeBranch p rate) :=
  {b | cutoffDownStageCodeCheck
    (payloadFromStageCodeKey (p := p) (rate := rate) b.1 b.2) i t wD b.2}

private def cutoffUpStageCodeBranchSet
    (i : Fin (p.m - 1)) (t : Fin p.T)
    (reply : OrdinaryMessageCodec.UpRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta)) :
    Set (DownStageCodeBranch p rate) :=
  {b | cutoffUpStageCodeCheck
    (payloadFromStageCodeKey (p := p) (rate := rate) b.1 b.2) i t reply b.2}

private def cutoffDownStageKeyCheck
    (i : Fin (p.m - 1)) (key : StageCodeKey p rate) : Prop :=
  (∀ j : Fin (p.m - 1), ∃ follower, key.2.2.2 j = Sum.inr follower) ∧
  ∃ follower, key.2.2.2 i = Sum.inr follower ∧ follower.lastDown = none

private def cutoffUpStageKeyCheck
    (i : Fin (p.m - 1))
    (reply : OrdinaryMessageCodec.UpRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))
    (key : StageCodeKey p rate) : Prop :=
  (∀ j : Fin (p.m - 1), ∃ follower, key.2.2.2 j = Sum.inr follower) ∧
  ∃ follower, key.2.2.2 i = Sum.inr follower ∧
    1 ≤ follower.lastDown.elim 0 (fun d => d.val.sigma) ∧
    ({ sigma := follower.lastDown.elim 0 (fun d => d.val.sigma),
       S := follower.S, delta := follower.delta, q := follower.backlog } :
      OrdinaryMessageCodec.UpFields) = reply.val

private theorem cutoffDownStageCodeViewSet_eq_image
    (i : Fin (p.m - 1)) (t : Fin p.T)
    (wD : AffineChannelLaw.Word (AffineBatchDecoder.width p)) :
    cutoffDownStageCodeViewSet (p := p) (rate := rate) i t wD =
      Sum.inr '' cutoffDownStageCodeBranchSet (p := p) (rate := rate) i t wD := by
  ext view
  constructor
  · rintro ⟨anchor, key, rfl, hcheck⟩
    exact ⟨(anchor, key), hcheck, rfl⟩
  · rintro ⟨⟨anchor, key⟩, hcheck, rfl⟩
    exact ⟨anchor, key, rfl, hcheck⟩

private theorem cutoffUpStageCodeViewSet_eq_image
    (i : Fin (p.m - 1)) (t : Fin p.T)
    (reply : OrdinaryMessageCodec.UpRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta)) :
    cutoffUpStageCodeViewSet (p := p) (rate := rate) i t reply =
      Sum.inr '' cutoffUpStageCodeBranchSet (p := p) (rate := rate) i t reply := by
  ext view
  constructor
  · rintro ⟨anchor, key, rfl, hcheck⟩
    exact ⟨(anchor, key), hcheck, rfl⟩
  · rintro ⟨⟨anchor, key⟩, hcheck, rfl⟩
    exact ⟨anchor, key, rfl, hcheck⟩

private theorem measurable_of_sigma_sections {α : Type*} {β : α → Type*}
    [∀ a, MeasurableSpace (β a)] {γ : Type*} [MeasurableSpace γ]
    (f : Sigma β → γ)
    (hf : ∀ a, Measurable (fun x : β a => f ⟨a, x⟩)) : Measurable f := by
  intro s hs
  change MeasurableSet[(⨅ a, (inferInstance : MeasurableSpace (β a)).map (Sigma.mk a))]
    {x | f x ∈ s}
  rw [MeasurableSpace.measurableSet_iInf]
  intro a
  rw [MeasurableSpace.map_def]
  exact hf a hs

private theorem measurable_carriedFollowerStateCode :
    Measurable (fun x : FollowerPrepareJointMeasurability.CarriedState p rate => x.1.1) := by
  apply measurable_of_sigma_sections
  intro index
  simp

private theorem measurable_followerStateTag : Measurable
    (followerStateTag (p := p) (rate := rate)) := by
  have hordinary : Measurable (fun x :
      FollowerPrepareJointMeasurability.CarriedState p rate ×
        FollowerPrepareJointMeasurability.LocalMemoryCode p =>
      (Sum.inr x.1.1.1 : FollowerTag p rate)) := by
    exact measurable_inr.comp
      ((measurable_carriedFollowerStateCode (p := p) (rate := rate)).comp measurable_fst)
  have hsum : Measurable (fun x : Unit ⊕
      (FollowerPrepareJointMeasurability.CarriedState p rate ×
        FollowerPrepareJointMeasurability.LocalMemoryCode p) =>
      Sum.elim (fun _ => (Sum.inl () : FollowerTag p rate))
        (fun y => Sum.inr y.1.1.1) x) :=
    Measurable.sumElim measurable_const hordinary
  have hview := FollowerPrepareJointMeasurability.measurable_incomingConfigurationToSum
    (p := p) rate
  convert hsum.comp hview using 1
  funext x
  cases x <;> rfl

private theorem measurable_followerStateCodeTags :
    Measurable (followerStateCodeTags (p := p) (rate := rate)) := by
  have hfollowers : Measurable (fun c : StateCode p rate => c.2.2.2) :=
    measurable_snd.comp (measurable_snd.comp measurable_snd)
  apply measurable_pi_iff.mpr
  intro j
  exact (measurable_followerStateTag (p := p) (rate := rate)).comp
    ((measurable_pi_apply j).comp hfollowers)

private theorem measurable_payloadDiscreteCode :
    Measurable (payloadDiscreteCode (p := p) (rate := rate)) := by
  have hobs : Measurable
      (LaterAssignmentStartMeasurability.payloadObservation
        (p := p) (eta := rate.eta)) := comap_measurable _
  have hn : Measurable (fun x : ReferenceActivePhysicalStep.Payload rate => x.n) :=
    measurable_fst.comp hobs
  have hsigma : Measurable (fun x : ReferenceActivePhysicalStep.Payload rate => x.sigma) :=
    measurable_fst.comp (measurable_snd.comp hobs)
  have hslow : Measurable (fun x : ReferenceActivePhysicalStep.Payload rate => x.slowSet) :=
    (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp hobs))).subtype_mk
  have hqueue : Measurable (fun x : ReferenceActivePhysicalStep.Payload rate =>
      (⟨x.queues, x.queues_le_TD⟩ : QueueCode p)) :=
    (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp
      (measurable_snd.comp hobs)))).subtype_mk
  exact hn.prodMk (hsigma.prodMk (hslow.prodMk hqueue))

abbrev StageCoordinatorView (p : Parameters) (rate : RateInput p) :=
  Unit ⊕ (ReferenceActivePhysicalStep.Payload rate ×
    ReferenceActivePhysicalStepMeasurability.LiveDiscrete p)

private def cutoffStageCoordinatorView (c :
    ReferenceActivePhysicalStepMeasurability.CoordinatorCode p rate) :
    StageCoordinatorView p rate :=
  match c with
  | .inl _ => .inl ()
  | .inr (.inl live) => .inr live
  | .inr (.inr _) => .inl ()

private theorem measurable_cutoffStageCoordinatorView :
    Measurable (cutoffStageCoordinatorView (p := p) (rate := rate)) := by
  unfold cutoffStageCoordinatorView
  apply Measurable.sumElim
  · exact measurable_const
  · apply Measurable.sumElim
    · exact measurable_inr.comp measurable_id
    · apply Measurable.sumElim <;> exact measurable_const

private theorem measurable_cutoffStageCodeView (t : Fin p.T) :
    Measurable (cutoffStageCodeView (p := p) (rate := rate) t) := by
  let Live := ReferenceActivePhysicalStep.Payload rate ×
    ReferenceActivePhysicalStepMeasurability.LiveDiscrete p
  let Tags := FollowerTags p rate
  have hanchor : Measurable (fun x : Live × Tags =>
      (⟨x.1.1.anchor, x.1.1.anchor_pos⟩ :
        LaterAssignmentAnchorMeasurability.PositiveAnchor p)) :=
    (AssignmentPayloadDerivedMeasurability.measurable_inputAnchor.comp
      (measurable_fst.comp measurable_fst)).subtype_mk
  have hkey : Measurable (fun x : Live × Tags =>
      (payloadDiscreteCode (p := p) (rate := rate) x.1.1, (x.1.2, (t, x.2)))) :=
    (measurable_payloadDiscreteCode.comp (measurable_fst.comp measurable_fst)).prodMk
      ((measurable_snd.comp measurable_fst).prodMk
        (measurable_const.prodMk measurable_snd))
  let branch := fun x : Live × Tags =>
    (Sum.inr (⟨x.1.1.anchor, x.1.1.anchor_pos⟩,
      (payloadDiscreteCode (p := p) (rate := rate) x.1.1, (x.1.2, (t, x.2)))) :
      StageCodeView p rate)
  have hb : Measurable branch := measurable_inr.comp (hanchor.prodMk hkey)
  have hs : Measurable (fun c : StateCode p rate =>
      (cutoffStageCoordinatorView (p := p) (rate := rate) c.1,
        followerStateCodeTags (p := p) (rate := rate) c)) :=
    (measurable_cutoffStageCoordinatorView.comp measurable_fst).prodMk
      measurable_followerStateCodeTags
  have hm := ((Measurable.sumElim
    (measurable_const : Measurable (fun _ : Unit × Tags =>
      (Sum.inl () : StageCodeView p rate))) hb).comp
        (MeasurableEquiv.sumProdDistrib Unit Live Tags).measurable_toFun).comp hs
  convert hm using 1
  funext c
  rcases c with ⟨coord, rest⟩
  rcases coord with first | liveOrOther
  · rfl
  · rcases liveOrOther with live | collectionOrDagger
    · rfl
    · cases collectionOrDagger <;> rfl

private theorem measurable_reanchoredPayload
    (old : ReferenceActivePhysicalStep.Payload rate) :
    Measurable (fun a : LaterAssignmentAnchorMeasurability.PositiveAnchor p =>
      LaterAssignmentAnchorMeasurability.payloadWithAnchor old a) := by
  apply measurable_comap_iff.mpr
  change Measurable (fun a : LaterAssignmentAnchorMeasurability.PositiveAnchor p =>
    (old.n, old.sigma, old.slowSet.1, a.1, old.queues))
  exact measurable_const.prodMk (measurable_const.prodMk
    (measurable_const.prodMk
      ((measurable_subtype_coe.comp measurable_id).prodMk measurable_const)))

private def downCoordinates (r : OrdinaryMessageCodec.DownFields) :=
  (r.sigma, r.a, r.e, r.h, r.q)

private theorem downCoordinates_injective :
    Function.Injective downCoordinates := by
  rintro ⟨a, b, c, d, e⟩ ⟨f, g, h, i, j⟩ heq
  simpa only [downCoordinates, Prod.mk.injEq,
    OrdinaryMessageCodec.DownFields.mk.injEq] using heq

private theorem measurable_reanchoredDownRecord
    (old : ReferenceActivePhysicalStep.Payload rate) (i : Fin (p.m - 1)) :
    Measurable (fun a : LaterAssignmentAnchorMeasurability.PositiveAnchor p =>
      (LaterAssignmentAnchorMeasurability.payloadWithAnchor old a).downRecord i) := by
  have hp := measurable_reanchoredPayload (p := p) (rate := rate) old
  have he := AssignmentPayloadDerivedMeasurability.measurable_inputExponent.comp hp
  have ha := AssignmentPayloadDerivedMeasurability.measurable_inputAuxiliary.comp hp
  have haux : Measurable (fun a : LaterAssignmentAnchorMeasurability.PositiveAnchor p =>
      (LaterAssignmentAnchorMeasurability.payloadWithAnchor old a).assignment.auxiliary.val + 1) :=
    (measurable_of_countable (fun a : Fin p.K => a.val + 1)).comp ha
  have hexp : Measurable (fun a : LaterAssignmentAnchorMeasurability.PositiveAnchor p =>
      (LaterAssignmentAnchorMeasurability.payloadWithAnchor old a).exponent
        (old.assignment.assigned i)) :=
    (measurable_pi_apply (old.assignment.assigned i)).comp he
  have hcoordinates : Measurable (fun a : LaterAssignmentAnchorMeasurability.PositiveAnchor p =>
      downCoordinates
        ((LaterAssignmentAnchorMeasurability.payloadWithAnchor old a).downRecord i).val) := by
    change Measurable (fun a : LaterAssignmentAnchorMeasurability.PositiveAnchor p =>
      (old.sigma.val + 1, (old.assignment.assigned i).val + 1,
        (LaterAssignmentAnchorMeasurability.payloadWithAnchor old a).assignment.auxiliary.val + 1,
        (LaterAssignmentAnchorMeasurability.payloadWithAnchor old a).exponent
          (old.assignment.assigned i),
        old.queues (old.assignment.assigned i)))
    exact measurable_const.prodMk (measurable_const.prodMk
      (haux.prodMk (hexp.prodMk measurable_const)))
  have hrecord : Measurable (fun a : LaterAssignmentAnchorMeasurability.PositiveAnchor p =>
      (LaterAssignmentAnchorMeasurability.payloadWithAnchor old a).downRecord i) := by
    apply measurable_to_countable'
    intro record
    have hfiber : {a : LaterAssignmentAnchorMeasurability.PositiveAnchor p |
        (LaterAssignmentAnchorMeasurability.payloadWithAnchor old a).downRecord i = record} =
        (fun a => downCoordinates
          ((LaterAssignmentAnchorMeasurability.payloadWithAnchor old a).downRecord i).val) ⁻¹'
          {downCoordinates record.val} := by
      ext a
      constructor
      · intro h
        exact congrArg (fun r => downCoordinates r.val) h
      · intro h
        exact Subtype.ext (downCoordinates_injective h)
    change MeasurableSet {a : LaterAssignmentAnchorMeasurability.PositiveAnchor p |
      (LaterAssignmentAnchorMeasurability.payloadWithAnchor old a).downRecord i = record}
    rw [hfiber]
    exact hcoordinates (measurableSet_singleton _)
  exact hrecord

private theorem measurable_reanchoredDownFlatWord
    (old : ReferenceActivePhysicalStep.Payload rate) (i : Fin (p.m - 1)) :
    Measurable (fun a : LaterAssignmentAnchorMeasurability.PositiveAnchor p =>
      CoordinatorLocalArmChoice.storedDownFlatWord
        (LaterAssignmentAnchorMeasurability.payloadWithAnchor old a) i) := by
  have hencode : Measurable (fun record : OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta) =>
      OrdinaryMessageCodec.wordEquivFlat
        (ReferencePrelaunchFollower.codecParams p rate.eta)
        (OrdinaryMessageCodec.encodeDown
          (ReferencePrelaunchFollower.codecParams p rate.eta) record)) :=
    measurable_of_countable _
  change Measurable ((fun record => OrdinaryMessageCodec.wordEquivFlat
      (ReferencePrelaunchFollower.codecParams p rate.eta)
      (OrdinaryMessageCodec.encodeDown
        (ReferencePrelaunchFollower.codecParams p rate.eta) record)) ∘
      (fun a => (LaterAssignmentAnchorMeasurability.payloadWithAnchor old a).downRecord i))
  exact hencode.comp (measurable_reanchoredDownRecord (p := p) (rate := rate) old i)

private def outcomeIsCutoff :
    ReferenceLiveDispatchOutputMeasurability.OutcomeData p → Bool
  | .cutoffChosen _ _ _ => true
  | _ => false

private theorem outcomeIsCutoff_choiceData_cont
    (x : CoordinatorRoundDispatch.LiveInput p)
    (out : CoordinatorStartRoundCutoffDispatch.Output
      x.registers x.ownedRegisters x.followerBaseScore) :
    outcomeIsCutoff (ReferenceLiveDispatchOutputMeasurability.choiceData x out
      (ReferenceLiveDispatchOutputMeasurability.OutcomeData.continuingChosen
        (ReferenceLiveDispatchOutputMeasurability.dispatchData out) out.startResult)) = false := by
  unfold ReferenceLiveDispatchOutputMeasurability.choiceData
  split_ifs <;> rfl

private def stageDispatchOutcomeData
    (old : ReferenceActivePhysicalStep.Payload rate)
    (live : ReferenceActivePhysicalStepMeasurability.LiveDiscrete p)
    (t : Fin p.T)
    (anchor : LaterAssignmentAnchorMeasurability.PositiveAnchor p)
    (row : CompletePublicTable.CompleteRow p) :
    ReferenceLiveDispatchOutputMeasurability.OutcomeData p :=
  ReferenceLiveDispatchOutputMeasurability.outcomeData
    (CoordinatorRoundDispatch.dispatchLive
      (ReferenceLiveDispatchOutputMeasurability.sliceInput old live t (anchor, row)))

private def cutoffStageDispatchCheckOnInput
    (x : CoordinatorRoundDispatch.LiveInput p) : Prop :=
  ∃ out : CoordinatorStartRoundCutoffDispatch.Output
      x.registers x.ownedRegisters x.followerBaseScore,
    CoordinatorStartRoundCutoffDispatch.dispatch x.registers x.ownedRegisters
      x.followerBaseScore = .ok out ∧
    (∃ ledger, out.collectionInitialization = .success (some ledger)) ∧
    CoordinatorLocalArmChoice.ChoiceInputsValid x.registers.payload
      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p out.startResult.clock.u)
      x.registers.time x.registers.complementWeights ∧
    out.startResult.clock.g ≤ p.T + 1 ∧ x.registers.complementEnvelopeValid

private theorem measurable_stageDispatchOutcomeData
    (old : ReferenceActivePhysicalStep.Payload rate)
    (live : ReferenceActivePhysicalStepMeasurability.LiveDiscrete p)
    (t : Fin p.T) (row : CompletePublicTable.CompleteRow p) :
    Measurable (stageDispatchOutcomeData (p := p) (rate := rate) old live t · row) := by
  exact (ReferenceLiveDispatchOutputMeasurability.measurable_outcomeData_slice
    (p := p) (rate := rate) old live t).comp
      (measurable_id.prodMk measurable_const)

private theorem stageDispatchCheck_iff_outcomeIsCutoff
    (old : ReferenceActivePhysicalStep.Payload rate)
    (live : ReferenceActivePhysicalStepMeasurability.LiveDiscrete p)
    (t : Fin p.T) (anchor : LaterAssignmentAnchorMeasurability.PositiveAnchor p)
    (row : CompletePublicTable.CompleteRow p) :
    cutoffStageDispatchCheck (p := p) (rate := rate)
        (LaterAssignmentAnchorMeasurability.payloadWithAnchor old anchor) live t ↔
      outcomeIsCutoff (stageDispatchOutcomeData (p := p) (rate := rate)
        old live t anchor row) = true := by
  classical
  let payload := LaterAssignmentAnchorMeasurability.payloadWithAnchor old anchor
  let x := ReferenceLiveDispatchOutputMeasurability.sliceInput old live t (anchor, row)
  have hcheck : cutoffStageDispatchCheck (p := p) (rate := rate) payload live t ↔
      cutoffStageDispatchCheckOnInput x := by
    simp [cutoffStageDispatchCheck, cutoffStageDispatchCheckOnInput, x,
      ReferenceLiveDispatchOutputMeasurability.sliceInput,
      ReferenceLiveDispatchMeasurability.liveInputOfCoordinates,
      ReferenceActivePhysicalStepMeasurability.decodeLiveRegisters,
      ReferenceActivePhysicalStepMeasurability.decodeLiveOwned,
      ReferenceActivePhysicalStep.liveRegistersAt,
      ReferenceActivePhysicalStep.liveOwnedAt, payload]
  rw [hcheck]
  change cutoffStageDispatchCheckOnInput x ↔
    outcomeIsCutoff (ReferenceLiveDispatchOutputMeasurability.outcomeData
      (CoordinatorRoundDispatch.dispatchLive x)) = true
  rw [ReferenceLiveDispatchOutputMeasurability.outcomeData_dispatchLive]
  dsimp only [outcomeIsCutoff]
  unfold ReferenceLiveDispatchOutputMeasurability.dataFormula
  let dispatch := CoordinatorStartRoundCutoffDispatch.dispatch x.registers
    x.ownedRegisters x.followerBaseScore
  cases hd : dispatch with
  | error failure =>
      simp [cutoffStageDispatchCheckOnInput, dispatch, hd]
  | ok out =>
      cases hi : out.collectionInitialization with
      | invalid =>
          simp [cutoffStageDispatchCheckOnInput, dispatch, hd, hi]
      | rejected rejected =>
          simp [cutoffStageDispatchCheckOnInput, dispatch, hd, hi]
      | success value =>
          cases value with
          | none =>
              have hleft : ¬ cutoffStageDispatchCheckOnInput x := by
                simp [cutoffStageDispatchCheckOnInput, dispatch, hd, hi]
              have hright : outcomeIsCutoff
                  (ReferenceLiveDispatchOutputMeasurability.dataFormula x) = false := by
                simp only [ReferenceLiveDispatchOutputMeasurability.dataFormula,
                  dispatch, hd, hi]
                split_ifs
                all_goals
                  first
                  | rfl
                  | exact outcomeIsCutoff_choiceData_cont x out
              change cutoffStageDispatchCheckOnInput x ↔
                outcomeIsCutoff (ReferenceLiveDispatchOutputMeasurability.dataFormula x) = true
              simp [hleft, hright]
          | some ledger =>
              have hledger := CoordinatorRoundDispatch.cutoffDispatch_ledger_eq_candidate
                x.registers x.ownedRegisters x.followerBaseScore out ledger hd hi
              simp only [dispatch, hd, hi]
              change cutoffStageDispatchCheckOnInput x ↔
                outcomeIsCutoff (ReferenceLiveDispatchOutputMeasurability.choiceData x out
                  (ReferenceLiveDispatchOutputMeasurability.OutcomeData.cutoffChosen
                    (ReferenceLiveDispatchOutputMeasurability.dispatchData out)
                    (ReferenceLiveDispatchOutputMeasurability.ledgerData ledger))) = true
              rw [hledger.2.2]
              unfold ReferenceLiveDispatchOutputMeasurability.choiceData
              by_cases hchoice : CoordinatorLocalArmChoice.ChoiceInputsValid
                  x.registers.payload (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
                    out.startResult.clock.u) x.registers.time x.registers.complementWeights
              · by_cases hclock : out.startResult.clock.g ≤ p.T + 1
                · by_cases henvelope : x.registers.complementEnvelopeValid
                  · have hselected :=
                      CoordinatorLiveChoiceRecorderStep.coordinatorArmChoice_ne_none
                        x.registers.payload out.startResult.pending
                        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
                          out.startResult.clock.u) x.registers.time x.registers.complementWeights row hchoice
                    have hnotnone : CoordinatorLocalArmChoice.coordinatorArmChoice
                        x.registers.payload out.startResult.pending
                        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
                          out.startResult.clock.u) x.registers.time x.registers.complementWeights row ≠ none :=
                      hselected
                    have hexists := Option.ne_none_iff_exists.mp hnotnone
                    rcases hexists with ⟨arm, harm⟩
                    simp only [ite_eq_left hchoice, ite_eq_left hclock, ite_eq_left henvelope]
                    rw [show CoordinatorLocalArmChoice.coordinatorArmChoice
                      x.registers.payload out.startResult.pending
                      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p out.startResult.clock.u)
                      x.registers.time x.registers.complementWeights x.row = some arm from harm.symm]
                    simp [hchoice, hclock, henvelope,
                      cutoffStageDispatchCheckOnInput, dispatch, hd, hi]
                    rfl
                  · simp [hchoice, hclock, henvelope, cutoffStageDispatchCheckOnInput,
                      dispatch, hd]
                    rfl
                · simp [hchoice, hclock, cutoffStageDispatchCheckOnInput,
                    dispatch, hd, hi]
                  rfl
              · simp [hchoice, cutoffStageDispatchCheckOnInput, dispatch,
                  hd, hi]
                rfl

private theorem measurableSet_stageDispatchCheck
    (old : ReferenceActivePhysicalStep.Payload rate)
    (live : ReferenceActivePhysicalStepMeasurability.LiveDiscrete p)
    (t : Fin p.T) :
    MeasurableSet {anchor : LaterAssignmentAnchorMeasurability.PositiveAnchor p |
      cutoffStageDispatchCheck (p := p) (rate := rate)
        (LaterAssignmentAnchorMeasurability.payloadWithAnchor old anchor) live t} := by
  let row := CoordinatorLiveChoiceRecorderStep.dummyCompleteRow p
  have hm := measurable_stageDispatchOutcomeData (p := p) (rate := rate) old live t row
  have hs : MeasurableSet {o : ReferenceLiveDispatchOutputMeasurability.OutcomeData p |
      outcomeIsCutoff o = true} := MeasurableSpace.measurableSet_top
  convert hm hs using 1
  ext anchor
  exact stageDispatchCheck_iff_outcomeIsCutoff (p := p) (rate := rate) old live t anchor row

private def cutoffDownStageAnchorSection
    (i : Fin (p.m - 1)) (t : Fin p.T)
    (wD : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (key : StageCodeKey p rate) :
    Set (LaterAssignmentAnchorMeasurability.PositiveAnchor p) :=
  {anchor | cutoffStageDispatchCheck (p := p) (rate := rate)
      (payloadFromStageCodeKey (p := p) (rate := rate) anchor key) key.2.1 t ∧
    CoordinatorLocalArmChoice.storedDownFlatWord
      (payloadFromStageCodeKey (p := p) (rate := rate) anchor key) i = wD}

private theorem measurableSet_cutoffDownStageAnchorSection
    (i : Fin (p.m - 1)) (t : Fin p.T)
    (wD : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (key : StageCodeKey p rate) :
    MeasurableSet (cutoffDownStageAnchorSection (p := p) (rate := rate) i t wD key) := by
  let old := payloadFromStageCodeKey (p := p) (rate := rate) positiveUnitAnchor key
  have hd := measurableSet_stageDispatchCheck (p := p) (rate := rate) old key.2.1 t
  have hw := (measurableSet_singleton wD).preimage
    (measurable_reanchoredDownFlatWord (p := p) (rate := rate) old i)
  convert hd.inter hw using 1
  ext anchor
  simp only [cutoffDownStageAnchorSection, Set.mem_ofPred_eq, Set.mem_inter_iff]
  rw [payloadFromStageCodeKey_reanchor (p := p) (rate := rate) anchor key]
  rfl

local instance followerTagMeasurableSingletonClass :
    MeasurableSingletonClass (FollowerTag p rate) := ⟨by
  intro tag
  cases tag with
  | inl u => simpa only [Set.image_singleton] using
      (measurableSet_singleton u).inl_image (β := FollowerDownMeasurability.FollowerStateCode p rate)
  | inr code => simpa only [Set.image_singleton] using
      (measurableSet_singleton code).inr_image (α := Unit)⟩

private theorem measurableSet_cutoffDownStageCodeBranchSet
    (i : Fin (p.m - 1)) (t : Fin p.T)
    (wD : AffineChannelLaw.Word (AffineBatchDecoder.width p)) :
    MeasurableSet (cutoffDownStageCodeBranchSet (p := p) (rate := rate) i t wD) := by
  have hm : Measurable (fun b : DownStageCodeBranch p rate =>
      decide (b ∈ cutoffDownStageCodeBranchSet (p := p) (rate := rate) i t wD)) := by
    apply measurable_from_prod_countable_left
    intro key
    apply measurable_to_bool
    simp only [Set.preimage, Set.mem_singleton_iff, decide_eq_true_eq]
    have heq : {a | (a, key) ∈ cutoffDownStageCodeBranchSet (p := p) (rate := rate) i t wD} =
        if cutoffDownStageKeyCheck (p := p) (rate := rate) i key then
          cutoffDownStageAnchorSection (p := p) (rate := rate) i t wD key else ∅ := by
      ext anchor
      by_cases hkey : cutoffDownStageKeyCheck (p := p) (rate := rate) i key
      · simp only [hkey, ite_true]
        rcases hkey with ⟨hordinary, follower, htag, hnone⟩
        simp only [cutoffDownStageCodeBranchSet, cutoffDownStageCodeCheck,
          cutoffStageDiscreteCheck, cutoffDownStageAnchorSection, Set.mem_ofPred_eq]
        constructor
        · rintro ⟨⟨hd, _⟩, f, hf, _, hw⟩
          exact ⟨hd, hw⟩
        · rintro ⟨hd, hw⟩
          exact ⟨⟨hd, hordinary⟩, follower, htag, hnone, hw⟩
      · simp only [hkey, ite_false, Set.mem_empty_iff_false, iff_false]
        rintro ⟨⟨_, ho⟩, f, hf, hn, _⟩
        exact hkey ⟨ho, f, hf, hn⟩
    rw [heq]
    split_ifs
    · exact measurableSet_cutoffDownStageAnchorSection (p := p) (rate := rate) i t wD key
    · exact MeasurableSet.empty
  simpa only [Set.preimage, Set.mem_singleton_iff, decide_eq_true_eq, Set.ofPred_mem_eq] using
    hm (measurableSet_singleton true)

private def cutoffUpStageAnchorSection
    (_i : Fin (p.m - 1)) (t : Fin p.T)
    (_reply : OrdinaryMessageCodec.UpRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))
    (key : StageCodeKey p rate) :
    Set (LaterAssignmentAnchorMeasurability.PositiveAnchor p) :=
  {anchor | cutoffStageDispatchCheck (p := p) (rate := rate)
      (payloadFromStageCodeKey (p := p) (rate := rate) anchor key) key.2.1 t}

private theorem measurableSet_cutoffUpStageAnchorSection
    (i : Fin (p.m - 1)) (t : Fin p.T)
    (reply : OrdinaryMessageCodec.UpRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))
    (key : StageCodeKey p rate) :
    MeasurableSet (cutoffUpStageAnchorSection (p := p) (rate := rate) i t reply key) := by
  convert measurableSet_stageDispatchCheck (p := p) (rate := rate)
    (payloadFromStageCodeKey (p := p) (rate := rate) positiveUnitAnchor key) key.2.1 t using 1
  ext anchor
  simp only [cutoffUpStageAnchorSection, Set.mem_ofPred_eq]
  rw [payloadFromStageCodeKey_reanchor (p := p) (rate := rate) anchor key]

private theorem measurableSet_cutoffUpStageCodeBranchSet
    (i : Fin (p.m - 1)) (t : Fin p.T)
    (reply : OrdinaryMessageCodec.UpRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta)) :
    MeasurableSet (cutoffUpStageCodeBranchSet (p := p) (rate := rate) i t reply) := by
  have hm : Measurable (fun b : DownStageCodeBranch p rate =>
      decide (b ∈ cutoffUpStageCodeBranchSet (p := p) (rate := rate) i t reply)) := by
    apply measurable_from_prod_countable_left
    intro key
    apply measurable_to_bool
    simp only [Set.preimage, Set.mem_singleton_iff, decide_eq_true_eq]
    have heq : {a | (a, key) ∈ cutoffUpStageCodeBranchSet (p := p) (rate := rate) i t reply} =
        if cutoffUpStageKeyCheck (p := p) (rate := rate) i reply key then
          cutoffUpStageAnchorSection (p := p) (rate := rate) i t reply key else ∅ := by
      ext anchor
      by_cases hkey : cutoffUpStageKeyCheck (p := p) (rate := rate) i reply key
      · simp only [hkey, ite_true]
        rcases hkey with ⟨hordinary, follower, htag, hpositive, hfields⟩
        simp only [cutoffUpStageCodeBranchSet, cutoffUpStageCodeCheck,
          cutoffStageDiscreteCheck, cutoffUpStageAnchorSection, Set.mem_ofPred_eq]
        constructor
        · exact fun h => h.1.1
        · intro hd
          exact ⟨⟨hd, hordinary⟩, follower, htag, hpositive, hfields⟩
      · simp only [hkey, ite_false, Set.mem_empty_iff_false, iff_false]
        rintro ⟨⟨_, ho⟩, f, hf, hp, hv⟩
        exact hkey ⟨ho, f, hf, hp, hv⟩
    rw [heq]
    split_ifs
    · exact measurableSet_cutoffUpStageAnchorSection (p := p) (rate := rate) i t reply key
    · exact MeasurableSet.empty
  simpa only [Set.preimage, Set.mem_singleton_iff, decide_eq_true_eq, Set.ofPred_mem_eq] using
    hm (measurableSet_singleton true)

private theorem measurableSet_optionSomeSet {α : Type*} [MeasurableSpace α]
    (s : Set α) (hs : MeasurableSet s) :
    MeasurableSet {o : Option α | ∃ x, o = some x ∧ x ∈ s} := by
  let e := Equiv.optionEquivSumPUnit α
  have hsum : MeasurableSet {v : α ⊕ PUnit | v.elim (fun x => x ∈ s) (fun _ => False)} := by
    rw [measurableSet_sum_iff]
    exact ⟨hs, MeasurableSet.empty⟩
  have hpre : {o : Option α | ∃ x, o = some x ∧ x ∈ s} =
      e ⁻¹' {v : α ⊕ PUnit | v.elim (fun x => x ∈ s) (fun _ => False)} := by
    ext o
    cases o with
    | none => simp [e]
    | some x => simp [e]
  rw [hpre]
  exact hsum.preimage (comap_measurable e)

private theorem measurableSet_cutoffDownStageCodeViewSet
    (i : Fin (p.m - 1)) (t : Fin p.T)
    (wD : AffineChannelLaw.Word (AffineBatchDecoder.width p)) :
    MeasurableSet (cutoffDownStageCodeViewSet (p := p) (rate := rate) i t wD) := by
  rw [cutoffDownStageCodeViewSet_eq_image]
  exact (measurableSet_cutoffDownStageCodeBranchSet (p := p) (rate := rate) i t wD).inr_image

private theorem measurableSet_cutoffUpStageCodeViewSet
    (i : Fin (p.m - 1)) (t : Fin p.T)
    (reply : OrdinaryMessageCodec.UpRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta)) :
    MeasurableSet (cutoffUpStageCodeViewSet (p := p) (rate := rate) i t reply) := by
  rw [cutoffUpStageCodeViewSet_eq_image]
  exact (measurableSet_cutoffUpStageCodeBranchSet (p := p) (rate := rate) i t reply).inr_image

/-- The old-DOWN code event is Borel on the canonical `Option StateCode`
carrier; absence of an actual incoming code is excluded. -/
theorem cutoffDownStageSupportCodeSet_measurableSet
    (i : Fin (p.m - 1)) (t : Fin p.T)
    (wD : AffineChannelLaw.Word (AffineBatchDecoder.width p)) :
    MeasurableSet (cutoffDownStageSupportCodeSet (p := p) (rate := rate) i t wD) := by
  unfold cutoffDownStageSupportCodeSet
  exact measurableSet_optionSomeSet
    {code : StateCode p rate |
      cutoffStageCodeView (p := p) (rate := rate) t code ∈
        cutoffDownStageCodeViewSet (p := p) (rate := rate) i t wD}
    ((measurableSet_cutoffDownStageCodeViewSet (p := p) (rate := rate) i t wD).preimage
      (measurable_cutoffStageCodeView (p := p) (rate := rate) t))

/-- The formed-UP code event is Borel on the canonical `Option StateCode`
carrier; absence of an actual incoming code is excluded. -/
theorem cutoffUpStageSupportCodeSet_measurableSet
    (i : Fin (p.m - 1)) (t : Fin p.T)
    (reply : OrdinaryMessageCodec.UpRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta)) :
    MeasurableSet (cutoffUpStageSupportCodeSet (p := p) (rate := rate) i t reply) := by
  unfold cutoffUpStageSupportCodeSet
  exact measurableSet_optionSomeSet
    {code : StateCode p rate |
      cutoffStageCodeView (p := p) (rate := rate) t code ∈
        cutoffUpStageCodeViewSet (p := p) (rate := rate) i t reply}
    ((measurableSet_cutoffUpStageCodeViewSet (p := p) (rate := rate) i t reply).preimage
      (measurable_cutoffStageCodeView (p := p) (rate := rate) t))

/-- Direct characterization of membership for a present canonical state
code. -/
theorem some_mem_cutoffDownStageSupportCodeSet_iff
    (i : Fin (p.m - 1)) (t : Fin p.T)
    (wD : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (code : StateCode p rate) :
    some code ∈ cutoffDownStageSupportCodeSet (p := p) (rate := rate) i t wD ↔
      cutoffStageCodeView (p := p) (rate := rate) t code ∈
        cutoffDownStageCodeViewSet (p := p) (rate := rate) i t wD := by
  simp only [cutoffDownStageSupportCodeSet, Set.mem_ofPred_eq, Option.some.injEq, exists_eq_left']

/-- Direct characterization of membership for a present canonical state
code. -/
theorem some_mem_cutoffUpStageSupportCodeSet_iff
    (i : Fin (p.m - 1)) (t : Fin p.T)
    (reply : OrdinaryMessageCodec.UpRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))
    (code : StateCode p rate) :
    some code ∈ cutoffUpStageSupportCodeSet (p := p) (rate := rate) i t reply ↔
      cutoffStageCodeView (p := p) (rate := rate) t code ∈
        cutoffUpStageCodeViewSet (p := p) (rate := rate) i t reply := by
  simp only [cutoffUpStageSupportCodeSet, Set.mem_ofPred_eq, Option.some.injEq, exists_eq_left']

/-- The canonical code events exclude absence. -/
theorem none_not_mem_cutoffDownStageSupportCodeSet (i : Fin (p.m - 1)) (t : Fin p.T)
    (wD : AffineChannelLaw.Word (AffineBatchDecoder.width p)) :
    none ∉ cutoffDownStageSupportCodeSet (rate := rate) i t wD := by
  simp only [cutoffDownStageSupportCodeSet, Set.mem_ofPred_eq, reduceCtorEq,
    false_and, exists_false, not_false_eq_true]

theorem none_not_mem_cutoffUpStageSupportCodeSet (i : Fin (p.m - 1)) (t : Fin p.T)
    (reply : OrdinaryMessageCodec.UpRecord (ReferencePrelaunchFollower.codecParams p rate.eta)) :
    none ∉ cutoffUpStageSupportCodeSet (rate := rate) i t reply := by
  simp only [cutoffUpStageSupportCodeSet, Set.mem_ofPred_eq, reduceCtorEq,
    false_and, exists_false, not_false_eq_true]

private theorem payloadFromStageCodeKey_original
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (live : ReferenceActivePhysicalStepMeasurability.LiveDiscrete p)
    (t : Fin p.T) (tags : FollowerTags p rate) :
    payloadFromStageCodeKey (p := p) (rate := rate) ⟨payload.anchor, payload.anchor_pos⟩
      (payloadDiscreteCode payload, (live, (t, tags))) = payload := by
  have hn := ReferenceActivePhysicalStep.payload_n_eq payload
  cases payload
  dsimp only at hn
  cases hn
  rfl

private theorem followerTag_exists_iff
    (config : DeclaredFollowerLocalRound.LocalConfiguration p rate)
    (P : FollowerDownMeasurability.FollowerStateCode p rate → Prop) :
    (∃ f, followerStateTag (FollowerPrepareJointMeasurability.incomingOfLocalConfiguration
      rate config) = Sum.inr f ∧ P f) ↔
      ∃ old memory, config = .ordinary old memory ∧
        P (FollowerDownMeasurability.followerStateCode rate old) := by
  cases config <;> simp [followerStateTag,
    FollowerPrepareJointMeasurability.incomingOfLocalConfiguration,
    FollowerObservationStageMeasurabilityRepair.carriedStateOfState]

private theorem followerTag_ordinary_iff
    (config : DeclaredFollowerLocalRound.LocalConfiguration p rate) :
    (∃ f, followerStateTag (FollowerPrepareJointMeasurability.incomingOfLocalConfiguration
      rate config) = Sum.inr f) ↔ ∃ old memory, config = .ordinary old memory := by
  simpa only [and_true] using followerTag_exists_iff (rate := rate) config (fun _ => True)

private theorem dispatchCheck_encodeLive_iff
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r) (base : Fin (p.m - 1) → ℕ)
    (hc : x.state.coordinator = .live r q base) :
    cutoffStageDispatchCheck r.payload
        (ReferenceActivePhysicalStepMeasurability.encodeLive r q base) x.time ↔
      ReferenceCollectionPhaseHistory.cutoffChosen x = true := by
  have hp : LaterAssignmentAnchorMeasurability.payloadWithAnchor r.payload
      ⟨r.payload.anchor, r.payload.anchor_pos⟩ = r.payload := by cases r.payload; rfl
  have h := stageDispatchCheck_iff_outcomeIsCutoff r.payload
    (ReferenceActivePhysicalStepMeasurability.encodeLive r q base) x.time
    ⟨r.payload.anchor, r.payload.anchor_pos⟩ x.row
  rw [hp] at h
  rw [h]
  have hi : ReferenceLiveDispatchOutputMeasurability.sliceInput r.payload
      (ReferenceActivePhysicalStepMeasurability.encodeLive r q base) x.time
      (⟨r.payload.anchor, r.payload.anchor_pos⟩, x.row) =
      ReferenceActivePhysicalStep.liveInput x r q base := by
    exact ReferenceLiveDispatchMeasurability.liveInputOfCoordinates_liveDispatchCoordinatesOfRound
      x r q base
  dsimp only [stageDispatchOutcomeData]
  rw [hi]
  dsimp only [ReferenceCollectionPhaseHistory.cutoffChosen, ReferenceActivePhysicalStep.prepare,
    ReferenceActivePhysicalStep.dispatch]
  simp only [hc, CoordinatorRoundDispatch.dispatch]
  cases CoordinatorRoundDispatch.dispatchLive (ReferenceActivePhysicalStep.liveInput x r q base) <;> rfl

private theorem down_code_round_iff (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (i : Fin (p.m - 1)) (wD : AffineChannelLaw.Word (AffineBatchDecoder.width p)) :
    some (ReferenceActivePhysicalStepMeasurability.encodeState x.state) ∈
        cutoffDownStageSupportCodeSet (rate := rate) i x.time wD ↔
      ∃ (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
        (q : CoordinatorLiveServiceFinish.OwnedRegisters r) (base : Fin (p.m - 1) → ℕ),
        x.state.coordinator = .live r q base ∧
        ReferenceCollectionPhaseHistory.cutoffChosen x = true ∧
        (∀ j, ∃ old memory, x.state.followers j = .ordinary old memory) ∧
        ∃ old memory, x.state.followers i = .ordinary old memory ∧ old.lastDown = none ∧
          CoordinatorLocalArmChoice.storedDownFlatWord r.payload i = wD := by
  cases hc : x.state.coordinator with
  | first => simp [some_mem_cutoffDownStageSupportCodeSet_iff, cutoffStageCodeView,
      ReferenceActivePhysicalStepMeasurability.encodeState,
      ReferenceActivePhysicalStepMeasurability.encodeCoordinator, hc, cutoffDownStageCodeViewSet]
  | dagger => simp [some_mem_cutoffDownStageSupportCodeSet_iff, cutoffStageCodeView,
      ReferenceActivePhysicalStepMeasurability.encodeState,
      ReferenceActivePhysicalStepMeasurability.encodeCoordinator, hc, cutoffDownStageCodeViewSet]
  | collection payload ledger proposal =>
      simp [some_mem_cutoffDownStageSupportCodeSet_iff, cutoffStageCodeView,
        ReferenceActivePhysicalStepMeasurability.encodeState,
        ReferenceActivePhysicalStepMeasurability.encodeCoordinator, hc, cutoffDownStageCodeViewSet]
  | live r q base =>
      simp only [some_mem_cutoffDownStageSupportCodeSet_iff, cutoffStageCodeView,
        ReferenceActivePhysicalStepMeasurability.encodeState,
        ReferenceActivePhysicalStepMeasurability.encodeCoordinator, hc,
        cutoffDownStageCodeViewSet, Set.mem_ofPred_eq, Sum.inr.injEq, Prod.mk.injEq,
        and_assoc]
      simp [payloadFromStageCodeKey_original, cutoffDownStageCodeCheck, cutoffStageDiscreteCheck,
        followerStateCodeTags, followerTag_exists_iff, followerTag_ordinary_iff,
        FollowerDownMeasurability.followerStateCode, dispatchCheck_encodeLive_iff x r q base hc, and_assoc]

private theorem up_code_round_iff (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (i : Fin (p.m - 1)) (reply : OrdinaryMessageCodec.UpRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta)) :
    some (ReferenceActivePhysicalStepMeasurability.encodeState x.state) ∈
        cutoffUpStageSupportCodeSet (rate := rate) i x.time reply ↔
      ∃ (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
        (q : CoordinatorLiveServiceFinish.OwnedRegisters r) (base : Fin (p.m - 1) → ℕ),
        x.state.coordinator = .live r q base ∧
        ReferenceCollectionPhaseHistory.cutoffChosen x = true ∧
        (∀ j, ∃ old memory, x.state.followers j = .ordinary old memory) ∧
        ∃ old memory, x.state.followers i = .ordinary old memory ∧
          1 ≤ ReferencePrelaunchFollower.acceptedStart old ∧
          ActiveFollowerQueueOperation.upOfferFields old = reply.val := by
  cases hc : x.state.coordinator with
  | first => simp [some_mem_cutoffUpStageSupportCodeSet_iff, cutoffStageCodeView,
      ReferenceActivePhysicalStepMeasurability.encodeState,
      ReferenceActivePhysicalStepMeasurability.encodeCoordinator, hc, cutoffUpStageCodeViewSet]
  | dagger => simp [some_mem_cutoffUpStageSupportCodeSet_iff, cutoffStageCodeView,
      ReferenceActivePhysicalStepMeasurability.encodeState,
      ReferenceActivePhysicalStepMeasurability.encodeCoordinator, hc, cutoffUpStageCodeViewSet]
  | collection payload ledger proposal =>
      simp [some_mem_cutoffUpStageSupportCodeSet_iff, cutoffStageCodeView,
        ReferenceActivePhysicalStepMeasurability.encodeState,
        ReferenceActivePhysicalStepMeasurability.encodeCoordinator, hc, cutoffUpStageCodeViewSet]
  | live r q base =>
      simp only [some_mem_cutoffUpStageSupportCodeSet_iff, cutoffStageCodeView,
        ReferenceActivePhysicalStepMeasurability.encodeState,
        ReferenceActivePhysicalStepMeasurability.encodeCoordinator, hc,
        cutoffUpStageCodeViewSet, Set.mem_ofPred_eq, Sum.inr.injEq, Prod.mk.injEq,
        and_assoc]
      simp [payloadFromStageCodeKey_original, cutoffUpStageCodeCheck, cutoffStageDiscreteCheck,
        followerStateCodeTags, followerTag_exists_iff, followerTag_ordinary_iff,
        FollowerDownMeasurability.followerStateCode, ReferencePrelaunchFollower.acceptedStart,
        ActiveFollowerQueueOperation.upOfferFields, dispatchCheck_encodeLive_iff x r q base hc,
        Option.elim, and_assoc]
      intro _ _
      apply exists_congr
      intro old
      cases old.lastDown <;> rfl

private theorem actualRecord_time (rewards : RewardTable p) (C_star C_h : ℝ)
    (t : Fin p.T) (z : SourceInput p) (r : RoundRecord p rate)
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some r) :
    r.input.time = t := by
  by_cases hz : ReferenceSourcePrefixHistoryFiltration.actualLaunchBy rate rewards C_star C_h t.val z
  · have hl := ReferenceLocalReleaseGateChronology.sourceSeed_launch rate z rewards C_star C_h hz.1
    have heq := Option.some.inj (hr.symm.trans
      (ReferenceSourcePrefixHistoryFiltration.actualRecord_on_launch rate rewards C_star C_h t z _ hl hz.2))
    subst r
    apply Fin.ext
    dsimp only [ReferenceAssignmentPayloadChronology.actualRunRecordAt,
      ReferenceActivePhysicalHorizon.roundInputAt]
    have hs := hz.2
    omega
  · rw [ReferenceSourcePrefixHistoryFiltration.actualRecord_eq_none_of_not_launchBy
      rate rewards C_star C_h t z hz] at hr
    cases hr

/-- Exact original-source characterization, with absence, FIRST, COLLECTION and
incoming dagger excluded by the literal event. -/
theorem cutoffDownStageSupport_iff_code (rewards : RewardTable p) (C_star C_h : ℝ)
    (i : Fin (p.m - 1)) (t : Fin p.T)
    (wD : AffineChannelLaw.Word (AffineBatchDecoder.width p)) (z : SourceInput p) :
    z ∈ cutoffDownStageSupport (rate := rate) rewards C_star C_h i t wD ↔
      ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t z ∈
        cutoffDownStageSupportCodeSet (rate := rate) i t wD := by
  cases hr : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z with
  | none => simp [cutoffDownStageSupport, ReferenceSourcePrefixHistoryFiltration.incoming, hr,
      cutoffDownStageSupportCodeSet]
  | some r =>
      have ht := actualRecord_time rewards C_star C_h t z r hr
      simpa only [cutoffDownStageSupport, Set.mem_ofPred_eq, hr, Option.some.injEq,
        exists_eq_left', ReferenceSourcePrefixHistoryFiltration.incoming, Option.map_some, ht] using
        (down_code_round_iff r.input i wD).symm

/-- Exact formed-UP characterization on the same original incoming code. -/
theorem cutoffUpStageSupport_iff_code (rewards : RewardTable p) (C_star C_h : ℝ)
    (i : Fin (p.m - 1)) (t : Fin p.T) (reply : OrdinaryMessageCodec.UpRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta)) (z : SourceInput p) :
    z ∈ cutoffUpStageSupport (rate := rate) rewards C_star C_h i t reply ↔
      ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t z ∈
        cutoffUpStageSupportCodeSet (rate := rate) i t reply := by
  cases hr : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z with
  | none => simp [cutoffUpStageSupport, ReferenceSourcePrefixHistoryFiltration.incoming, hr,
      cutoffUpStageSupportCodeSet]
  | some r =>
      have ht := actualRecord_time rewards C_star C_h t z r hr
      simpa only [cutoffUpStageSupport, Set.mem_ofPred_eq, hr, Option.some.injEq,
        exists_eq_left', ReferenceSourcePrefixHistoryFiltration.incoming, Option.map_some, ht] using
        (up_code_round_iff r.input i reply).symm

/-- The literal OLD support is measurable in the exact strict-prefix field. -/
theorem cutoffDownStageSupport_measurableSet (rewards : RewardTable p) (C_star C_h : ℝ)
    (control0 : TimeControl p) (i : Fin (p.m - 1)) (t : Fin p.T)
    (wD : AffineChannelLaw.Word (AffineBatchDecoder.width p)) :
    MeasurableSet[ReferenceSourceCurrentControlFreshness.m_t p control0 t]
      (cutoffDownStageSupport (rate := rate) rewards C_star C_h i t wD) := by
  rw [← ReferenceSourcePhysicalFlagConditionalLaw.sourcePrefixField_eq_m_t control0 t]
  convert (cutoffDownStageSupportCodeSet_measurableSet (rate := rate) i t wD).preimage
    (ReferenceSourcePrefixHistoryFiltration.incoming_measurable rate rewards C_star C_h control0 t) using 1
  ext z
  exact cutoffDownStageSupport_iff_code rewards C_star C_h i t wD z

/-- The literal formed-UP support is measurable in that same field. -/
theorem cutoffUpStageSupport_measurableSet (rewards : RewardTable p) (C_star C_h : ℝ)
    (control0 : TimeControl p) (i : Fin (p.m - 1)) (t : Fin p.T)
    (reply : OrdinaryMessageCodec.UpRecord (ReferencePrelaunchFollower.codecParams p rate.eta)) :
    MeasurableSet[ReferenceSourceCurrentControlFreshness.m_t p control0 t]
      (cutoffUpStageSupport (rate := rate) rewards C_star C_h i t reply) := by
  rw [← ReferenceSourcePhysicalFlagConditionalLaw.sourcePrefixField_eq_m_t control0 t]
  convert (cutoffUpStageSupportCodeSet_measurableSet (rate := rate) i t reply).preimage
    (ReferenceSourcePrefixHistoryFiltration.incoming_measurable rate rewards C_star C_h control0 t) using 1
  ext z
  exact cutoffUpStageSupport_iff_code rewards C_star C_h i t reply z

/-- Explicit factor through `sourcePrefix control0 t.val` and the canonical
Borel incoming map; it retains every other row and every original private array. -/
theorem cutoffDownStageSupport_factor (rewards : RewardTable p) (C_star C_h : ℝ)
    (control0 : TimeControl p) (i : Fin (p.m - 1)) (t : Fin p.T)
    (wD : AffineChannelLaw.Word (AffineBatchDecoder.width p)) :
    cutoffDownStageSupport (rate := rate) rewards C_star C_h i t wD =
      ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val ⁻¹'
        (ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t ⁻¹'
          cutoffDownStageSupportCodeSet (rate := rate) i t wD) := by
  ext z
  rw [cutoffDownStageSupport_iff_code,
    ReferenceSourcePrefixHistoryFiltration.incoming_factor rate rewards C_star C_h control0 t z]
  rfl

/-- The formed-UP event has the same explicit strict-prefix factorization. -/
theorem cutoffUpStageSupport_factor (rewards : RewardTable p) (C_star C_h : ℝ)
    (control0 : TimeControl p) (i : Fin (p.m - 1)) (t : Fin p.T)
    (reply : OrdinaryMessageCodec.UpRecord (ReferencePrelaunchFollower.codecParams p rate.eta)) :
    cutoffUpStageSupport (rate := rate) rewards C_star C_h i t reply =
      ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val ⁻¹'
        (ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t ⁻¹'
          cutoffUpStageSupportCodeSet (rate := rate) i t reply) := by
  ext z
  rw [cutoffUpStageSupport_iff_code,
    ReferenceSourcePrefixHistoryFiltration.incoming_factor rate rewards C_star C_h control0 t z]
  rfl

/-- OLD support is invariant under replacing the complete current control,
for every original source, including every absent and exceptional path. -/
theorem cutoffDownStageSupport_replaceSourceControl_iff
    (rewards : RewardTable p) (C_star C_h : ℝ) (i : Fin (p.m - 1)) (t : Fin p.T)
    (wD : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (z : SourceInput p) (c : TimeControl p) :
    ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z c ∈
        cutoffDownStageSupport (rate := rate) rewards C_star C_h i t wD ↔
      z ∈ cutoffDownStageSupport (rate := rate) rewards C_star C_h i t wD := by
  rw [cutoffDownStageSupport_factor rewards C_star C_h c i t wD]
  simp only [Set.mem_preimage]
  rw [sourcePrefix_replaceSourceControl]

/-- The same invariance for the exact typed formed reply. -/
theorem cutoffUpStageSupport_replaceSourceControl_iff
    (rewards : RewardTable p) (C_star C_h : ℝ) (i : Fin (p.m - 1)) (t : Fin p.T)
    (reply : OrdinaryMessageCodec.UpRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (z : SourceInput p) (c : TimeControl p) :
    ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z c ∈
        cutoffUpStageSupport (rate := rate) rewards C_star C_h i t reply ↔
      z ∈ cutoffUpStageSupport (rate := rate) rewards C_star C_h i t reply := by
  rw [cutoffUpStageSupport_factor rewards C_star C_h c i t reply]
  simp only [Set.mem_preimage]
  rw [sourcePrefix_replaceSourceControl]

private theorem actualRecord_at_cutoff
    (rate : RateInput p) (source : SourceInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (count : ℕ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hspan : ReferenceFirstCollectionReadyStream.startTime (rate := rate)
      source rewards C_star C_h + count ≤ p.T)
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
        source rewards C_star C_h hcross count hspan).records).length < count)
    (d : ReferenceFirstCollectionStreamEmptyDispatch.ActualInitializedStreamDispatch
      source rewards C_star C_h count hcross hspan hshort) :
    ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
      d.stream.cutoff.cut.input.time source = some d.stream.cutoff.cut := by
  let initial := ReferenceFirstCollectionEpochAlignment.actualLaunchState
    rate source rewards C_star C_h hcross
  let s := ReferenceFirstCollectionReadyStream.startTime (rate := rate) source rewards C_star C_h
  let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
    (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
      source rewards C_star C_h hcross count hspan).records).length
  have active := (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
    rate source rewards C_star C_h hcross).1
  have hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h = some initial :=
    Option.eq_some_of_isSome ((ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
      rate source rewards C_star C_h).2 hcross)
  have htime : d.stream.cutoff.cut.input.time.val = s + w := d.stream.cutoff.cutTime
  have hat := ReferenceLocalReleaseGateChronology.run_record_at initial source.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s active count hspan
    ⟨w, hshort⟩
  have hrecordAt : d.stream.cutoff.cut =
      ReferenceAssignmentPayloadChronology.actualRunRecordAt initial source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s w
        (by omega) active := by
    apply Option.some.inj
    calc
      some d.stream.cutoff.cut = _ := d.stream.cutoff.cutIndex.symm
      _ = _ := by
        rw [List.getElem?_eq_getElem (by
          change w < (ReferenceActivePhysicalHorizon.run initial source.1.2
            (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s count hspan active).records.length
          rw [ReferenceActivePhysicalHorizon.run_record_count]
          exact hshort)]
        exact congrArg some hat
  have hsource := ReferenceSourcePrefixHistoryFiltration.actualRecord_on_launch
    rate rewards C_star C_h d.stream.cutoff.cut.input.time source initial hlaunch
    (by change s ≤ d.stream.cutoff.cut.input.time.val; omega)
  have hsource' : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
      d.stream.cutoff.cut.input.time source = some
        (ReferenceAssignmentPayloadChronology.actualRunRecordAt initial source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s w
          (by omega) active) := by
    simpa only [show ReferenceCompletePhysicalHistory.physicalStart rate source rewards
      C_star C_h = s from rfl, htime, Nat.add_sub_cancel_left] using hsource
  exact hsource'.trans (congrArg some hrecordAt.symm)

/-- Actual old-or-formed support at the cutoff which starts the stopped
collection stream. This uses the whole reward table and unrestricted thresholds;
the same actual live payload fixes every DOWN word before follower branches.
Sources: `06_interruptions.tex:425-426,477-481`,
`05_binary_transport.tex:70-124`, `appendix_a_local_protocol.tex:44-64,100-108`. -/
theorem actual_first_cutoff_stage_support
    (rate : RateInput p) (source : SourceInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (count : ℕ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hspan : ReferenceFirstCollectionReadyStream.startTime (rate := rate)
      source rewards C_star C_h + count ≤ p.T)
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
        source rewards C_star C_h hcross count hspan).records).length < count) :
    ∃ d : ReferenceFirstCollectionStreamEmptyDispatch.ActualInitializedStreamDispatch
        source rewards C_star C_h count hcross hspan hshort,
    ∃ (old : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
      (memory : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p),
    let x := d.stream.cutoff.cut.input
    (∀ j, x.state.followers j = .ordinary (old j) (memory j) ∧
      ActiveFollowerLifecycle.startRound rate.eta x.time (old j) (memory j) =
        .ok ({ old j with status := ActiveRoundActions.FollowerStatus.unoccupied }, memory j) ∧
      ((ReferenceActivePhysicalStep.prepare x).followers.followers j).configuration =
        .ordinary ({ old j with status := ActiveRoundActions.FollowerStatus.unoccupied }) (memory j) ∧
      ActiveFollowerLifecycle.localStateDomainValid
        ({ old j with status := ActiveRoundActions.FollowerStatus.unoccupied })) ∧
    ∃ cut : RoundRecord p rate, cut = d.stream.cutoff.cut ∧
    ∃ (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
      (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
      (base : Fin (p.m - 1) → ℕ),
    ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
      cut.input.time source = some cut ∧
    cut.input.state.coordinator = .live registers owned base ∧
    ReferenceCollectionPhaseHistory.cutoffChosen cut.input = true ∧
    (∃ dispatched : CoordinatorStartRoundCutoffDispatch.Output
        (ReferenceActivePhysicalStep.liveRegistersAt registers cut.input.time)
        (ReferenceActivePhysicalStep.liveOwnedAt registers owned cut.input.time) base,
      (∃ ledger, dispatched.collectionInitialization = .success (some ledger)) ∧
      dispatched.startResult.pending = Finset.univ ∧
      ∃ selection : ReferenceActivePhysicalStep.Selection cut.input,
        (ReferenceActivePhysicalStep.prepare cut.input).coordinator.selection = some selection ∧
        selection.view.payload = registers.payload ∧
        selection.started = dispatched.startResult ∧
        selection.view.pendingAtChoice = Finset.univ) ∧
    let wD := fun i => CoordinatorLocalArmChoice.storedDownFlatWord registers.payload i
    (∀ i, (old i).lastDown = none →
      source ∈ cutoffDownStageSupport (p := p) (rate := rate) rewards C_star C_h
        i cut.input.time (wD i)) ∧
    (∀ i, (old i).lastDown ≠ none →
      ∃ reply : OrdinaryMessageCodec.UpRecord
        (ReferencePrelaunchFollower.codecParams p rate.eta),
        1 ≤ ReferencePrelaunchFollower.acceptedStart (old i) ∧
        reply.val = ActiveFollowerQueueOperation.upOfferFields (old i) ∧
        reply.val = ActiveFollowerQueueOperation.upOfferFields
          ({ old i with status := ActiveRoundActions.FollowerStatus.unoccupied }) ∧
        reply.val.sigma = ReferenceFirstCollectionReadyStream.startTime (rate := rate)
          source rewards C_star C_h + 1 ∧
        source ∈ cutoffUpStageSupport (p := p) (rate := rate) rewards C_star C_h
          i cut.input.time reply) := by
  classical
  obtain ⟨d, old, memory, hfollowers, hbranch⟩ :=
    ReferenceFirstCutoffUpConditionalService.actual_first_cutoff_up_service_coefficient
      rate source rewards C_star C_h count hcross hspan hshort
  let x := d.stream.cutoff.cut.input
  have hrecord := actualRecord_at_cutoff rate source rewards C_star C_h count
    hcross hspan hshort d
  have hcutoff := ReferenceFirstCutoffRecordedService.run_first_cutoff_recorded_service
    (ReferenceFirstCollectionEpochAlignment.actualLaunchState rate source rewards C_star C_h hcross)
    source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
    (ReferenceFirstCollectionReadyStream.startTime (rate := rate) source rewards C_star C_h)
    count hspan
    (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
      rate source rewards C_star C_h hcross).1
    (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
      rate source rewards C_star C_h hcross).2 hshort
  rcases hcutoff with ⟨cut, _suffix, _split, hindex, _htime, r0, q0, base0,
    hstateEq, hliveEq, dispatched, _start, ledger, hinit, _ledger, _domain, _clock,
    hpending, _assignment, selected, hchosen, _recorder⟩
  have hget : (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
      source rewards C_star C_h hcross count hspan).records[
        (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
          (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
            source rewards C_star C_h hcross count hspan).records).length]? = some cut := by
    rw [hindex]
    exact List.getElem?_eq_getElem _
  have hcutEq : cut = d.stream.cutoff.cut :=
    Option.some.inj (hget.symm.trans d.stream.cutoff.cutIndex)
  have hrecordCut := hrecord
  rw [← hcutEq] at hrecordCut
  have hprep : cut.output.preparation = ReferenceActivePhysicalStep.prepare cut.input :=
    congrArg ReferenceActivePhysicalStep.RoundOutput.preparation cut.output_eq
  have hcutCut : ReferenceCollectionPhaseHistory.cutoffChosen cut.input = true := by
    unfold ReferenceCollectionPhaseHistory.cutoffChosen
    rw [← hprep, hchosen]
  have hcoordCut : cut.input.state.coordinator = .live r0 q0 base0 := by
    rw [hstateEq, hliveEq]
  have hfollowersCut : ∀ j : Fin (p.m - 1),
      cut.input.state.followers j = .ordinary (old j) (memory j) := by
    intro j
    rw [hcutEq]
    exact (hfollowers j).1
  refine ⟨d, old, memory, ?_⟩
  dsimp only [x]
  constructor
  · exact hfollowers
  · refine ⟨cut, hcutEq, r0, q0, base0, hrecordCut, hcoordCut, hcutCut, ?_, ?_⟩
    · refine ⟨dispatched, ⟨ledger, hinit⟩, hpending, ?_⟩
      rw [← hprep, hchosen]
      simp only [ReferenceActivePhysicalStep.DispatchCut.selection,
        ReferenceActivePhysicalStep.selectionAt]
      exact ⟨_, rfl, rfl, rfl, hpending⟩
    · dsimp
      constructor
      · intro i hnone
        exact ⟨cut,
          ⟨hrecordCut, r0, q0, base0, hcoordCut, hcutCut,
            fun j => ⟨old j, memory j, hfollowersCut j⟩,
            old i, memory i, hfollowersCut i, hnone, rfl⟩⟩
      · intro i hsome
        have hpositive : 1 ≤ ReferencePrelaunchFollower.acceptedStart (old i) := by
          cases hlast : (old i).lastDown with
          | none => exact (hsome hlast).elim
          | some last =>
              have hdown := last.property
              unfold OrdinaryMessageCodec.downAdmissible at hdown
              simpa [ReferencePrelaunchFollower.acceptedStart, hlast] using hdown.1
        rcases hbranch i hpositive with ⟨reply, hprepared, hreply, hsigma, _positive,
          _supportEq, _measure, _record, _sections, _controls⟩
        exact ⟨reply, hpositive, hreply, hprepared, hsigma,
          cut,
          ⟨hrecordCut, r0, q0, base0, hcoordCut, hcutCut,
            (fun j => ⟨old j, memory j, hfollowersCut j⟩),
            old i, memory i, hfollowersCut i, hpositive, hreply.symm⟩⟩

end Bandits.Support.ReferenceCutoffStageSupportMeasurability
