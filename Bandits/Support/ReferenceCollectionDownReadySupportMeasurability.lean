/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionUpConditionalService

import Lean.Elab.Tactic.Omega

/-!
# Literal first-collection DOWN-ready support

This module defines the before-current continuing-collection old-DOWN event on
the original source space. It characterizes the event through the canonical
incoming state code, proves strict-prefix dependence and current-control
invariance, and applies the generated all-ordinary follower boundary to an
actual first-collection window record. It asserts no service law.

Sources: `sources/zip4/manuscript/06_interruptions.tex:459-490`,
`sources/zip4/manuscript/05_binary_transport.tex:20-53,70-124`,
`sources/zip4/manuscript/07_public_setup.tex:127-164`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-79,92-157`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support
open ConstructorDimensions
open scoped Classical

namespace Bandits.Support.ReferenceCollectionDownReadySupportMeasurability

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev SourceInput := BootstrapPrivateRoundStreams.SourceInput
abbrev RewardTable := ActualInitializationPhysicalStep.GridRewardTable
abbrev TimeControl := ContinuousLearningRows.TimeControl
abbrev RoundRecord (p : Parameters) (rate : RateInput p) :=
  ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)
abbrev Payload {p : Parameters} (rate : RateInput p) :=
  ReferenceActivePhysicalStep.Payload rate
abbrev Ledger {p : Parameters} (rate : RateInput p) :=
  ReferenceActivePhysicalStep.Ledger rate

local instance sourceInputMeasurableSpace (p : Parameters) :
    MeasurableSpace (SourceInput p) := by
  change MeasurableSpace
    (CompletePublicTable.PublishedOutput p ×
      (BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p))
  infer_instance

variable {p : Parameters} {rate : RateInput p}

/-- The literal old-DOWN branch before the current whole control. Its
witnesses are the actual calendar record, the continuing-ready domain, the
pending focal follower with no accepted DOWN word, the stored outgoing word,
and the all-ordinary follower clause. -/
def collectionDownReadySupport
    (rewards : RewardTable p) (C_star C_h : ℝ)
    (i : Fin (p.m - 1)) (t : Fin p.T)
    (wD : AffineChannelLaw.Word (AffineBatchDecoder.width p)) :
    Set (SourceInput p) :=
  {z | ∃ r : RoundRecord p rate,
      ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some r ∧
      ∃ (payload : Payload rate) (l : Ledger rate)
        (saved : Option (Fin p.T × Bool))
        (old : ReferencePrelaunchFollower.State p rate.eta)
        (memory : ActiveFollowerLifecycle.LocalMemory p),
        ReferenceContinuingCollectionStartDomains.continuingCollectionReadyDomain
          r.input payload l saved ∧
        i ∈ l.pending ∧
        r.input.state.followers i = .ordinary old memory ∧
        old.lastDown = none ∧
        CoordinatorLocalArmChoice.storedDownFlatWord payload i = wD ∧
        ∀ j : Fin (p.m - 1), r.input.state.followers j ≠ .dagger}

/-- The original real-valued payload anchor fibre. -/
abbrev AnchorCoordinates (p : Parameters) := Fin p.K → ℝ

/-- A follower tag distinguishes the dagger state from its canonical state code. -/
abbrev FollowerTag (p : Parameters) (rate : RateInput p) :=
  Unit ⊕ FollowerDownMeasurability.FollowerStateCode p rate

/-- The follower tags carried by one canonical incoming state code. -/
abbrev FollowerTags (p : Parameters) (rate : RateInput p) :=
  Fin (p.m - 1) → FollowerTag p rate

/-- A queue together with its original horizon bound, retaining its discrete fibre. -/
abbrev QueueCode (p : Parameters) :=
  {q : Fin p.K → ℕ // ∀ a, q a ≤ p.T * D p}

/-- The countable payload coordinates used by the collection ready code. -/
abbrev PayloadDiscreteCode (p : Parameters) :=
  ℕ × (Fin p.T × (CanonicalOrientedSetLaw.SlowSet p.K p.m × QueueCode p))

/- The key is countable. The anchor vector is kept as its original real-valued
factor in `CodeBranch`; it is never given a discrete measurable structure.
Queues are included as countable original payload coordinates because the
stored DOWN word contains the corresponding initial queue. -/
/-- The countable ready-state key, retaining the saved record and all followers. -/
abbrev ReadyCodeKey (p : Parameters) (rate : RateInput p) :=
  PayloadDiscreteCode p ×
    (ReferenceActivePhysicalStep.Ledger rate ×
      (Option (Fin p.T × Bool) ×
        (CoordinatorUpReception.UpDecoderBank p ×
          (Fin p.T × FollowerTags p rate))))

/-- The real anchor fibre paired with its countable ready-state key. -/
abbrev CodeBranch (p : Parameters) (rate : RateInput p) :=
  AnchorCoordinates p × ReadyCodeKey p rate

/-- The collection branch or the collapsed non-collection coordinator code. -/
abbrev CodeView (p : Parameters) (rate : RateInput p) :=
  Unit ⊕ CodeBranch p rate

/-- The canonical state code supplied by the physical-step measurability API. -/
abbrev StateCode (p : Parameters) (rate : RateInput p) :=
  ReferenceActivePhysicalStepMeasurability.StateCode p rate

/-- Encode dagger versus the canonical follower state in an incoming tag. -/
def followerStateTag (x : FollowerPrepareJointMeasurability.IncomingConfiguration p rate) :
    FollowerTag p rate :=
  match x with
  | none => Sum.inl ()
  | some (carried, _) => Sum.inr carried.1.1

/-- Read all follower tags from one canonical incoming state code. -/
def followerStateCodeTags : StateCode p rate → FollowerTags p rate :=
  fun c j => followerStateTag (c.2.2.2 j)

/-- Retain the collection coordinator branch and collapse the other branches. -/
def collectionCoordinatorCodeView
    (code : ReferenceActivePhysicalStepMeasurability.CoordinatorCode p rate) :
    Unit ⊕ (Payload rate × (Ledger rate × Option (Fin p.T × Bool))) :=
  match code with
  | .inl _ => .inl ()
  | .inr (.inl _) => .inl ()
  | .inr (.inr (.inl data)) => .inr data
  | .inr (.inr (.inr _)) => .inl ()

/-- Retain the discrete payload coordinates, including the bounded queues. -/
def payloadDiscreteCode (payload : Payload rate) : PayloadDiscreteCode p :=
  (payload.n, (payload.sigma,
    (payload.slowSet, ⟨payload.queues, payload.queues_le_TD⟩)))

/-- Assemble the ready-state key from one decoded collection branch. -/
def readyCodeKeyOfBranch
    (data : (Payload rate × (Ledger rate × Option (Fin p.T × Bool))) ×
      (CoordinatorUpReception.UpDecoderBank p × (Fin p.T × FollowerTags p rate))) :
    ReadyCodeKey p rate :=
  let payload := data.1.1
  let l := data.1.2.1
  let saved := data.1.2.2
  let bank := data.2.1
  (payloadDiscreteCode (p := p) (rate := rate) payload,
    (l, (saved, (bank, data.2.2))))

/-- Project one canonical state code to its real anchor and countable key. -/
def collectionDownReadyCodeView (t : Fin p.T) (c : StateCode p rate) :
    CodeView p rate :=
  let followers := followerStateCodeTags (p := p) (rate := rate) c
  let aux := (c.2.1, (t, followers))
  match collectionCoordinatorCodeView (p := p) (rate := rate) c.1 with
  | .inl _ => .inl ()
  | .inr branch =>
      .inr (branch.1.anchor,
        readyCodeKeyOfBranch (p := p) (rate := rate) (branch, aux))

/-- Rebuild the original payload fibre with anchor coordinates fixed to one. -/
def payloadWithUnitAnchor (sigma : Fin p.T)
    (slowSet : CanonicalOrientedSetLaw.SlowSet p.K p.m) (queues : QueueCode p) :
    Payload rate := {
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

/-- The Ready-domain conditions expressed on the countable key coordinates. -/
def readyDomainCodeKeyCheck (key : ReadyCodeKey p rate) : Prop :=
  let payloadN := key.1.1
  let payloadSigma := key.1.2.1
  let slowSet := key.1.2.2.1
  let l := key.2.1
  let bank := key.2.2.2.1
  let time := key.2.2.2.2.1
  payloadN = rate.n ∧
  l.phase = CoordinatorCollectionLedger.Phase.ready ∧
  1 ≤ l.sigma ∧ l.sigma ≤ p.T ∧ l.sigma < l.cutoff ∧
  l.sigma = payloadSigma.val + 1 ∧
  1 ≤ l.cutoff ∧ l.cutoff ≤ p.T ∧
  l.cutoff ≤ l.freezeAt ∧ l.freezeAt ≤ p.T + 1 ∧
  l.freezeAt = FollowerCutoffScan.gridBoundary p rate.eta.val payloadSigma ∧
  l.cursor = time.val + 1 ∧ l.cutoff < l.cursor ∧ l.cursor ≤ p.T + 1 ∧
  l.assignment.arm = CanonicalAssignmentVector.followerArm p.two_le_m slowSet ∧
  l.baseScore = (fun _ : Fin (p.m - 1) => (0 : ℕ)) ∧
  l.pending.Nonempty ∧
  (∀ a : Fin p.K,
    (l.currentRegisters a = none ↔ CoordinatorCollectionLedger.armPending l a) ∧
    (l.cutoffRegisters a = none ↔ CoordinatorCollectionLedger.armPending l a)) ∧
  (∀ a : Fin p.K,
    l.gammaLoc a = 0 ∧
    (CoordinatorCollectionLedger.armPending l a → l.increment a = 0)) ∧
  (∀ a c, l.cutoffRegisters a = some c →
    c.score + c.queue ≤ (l.cutoff - l.sigma) * D p ∧ c.lastService ≤ D p) ∧
  (∀ a c q, l.cutoffRegisters a = some c → l.currentRegisters a = some q →
    q.lastService ≤ D p ∧
    c.score + l.increment a + q.queue ≤ (l.cursor - l.sigma) * D p) ∧
  (∀ a c q, l.cutoffRegisters a = some c → l.currentRegisters a = some q →
    c.score + l.increment a ≤
      4 * rate.n * (min l.cursor l.freezeAt - l.sigma)) ∧
  (∀ a r amount, l.rawBuffer a r = some amount →
    0 < amount ∧ amount ≤ D p ∧
    l.cutoff ≤ r.val + 1 ∧ r.val + 1 < min l.cursor l.freezeAt ∧
    CoordinatorCollectionLedger.armPending l a) ∧
  (∀ r, l.enabledHistory r =
    if l.cutoff ≤ r.val + 1 ∧ r.val + 1 < l.cursor then
      some (decide (r.val + 1 < l.freezeAt)) else none) ∧
  (∀ j : Fin (p.m - 1),
    (bank j).pending.length < AffineBatchDecoder.quota p ∧
    (∀ batch, batch ∈ (bank j).completed →
      batch.length = AffineBatchDecoder.quota p) ∧
    (j ∉ l.pending → (bank j).pending = []))

/-- The focal old-DOWN branch check on a countable ready-state key. -/
def readyCodeKeyCheck (i : Fin (p.m - 1))
    (wD : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (key : ReadyCodeKey p rate) : Prop :=
  let l := key.2.1
  let followers := key.2.2.2.2.2
  readyDomainCodeKeyCheck (p := p) (rate := rate) key ∧
  (∀ j : Fin (p.m - 1), ∃ code, followers j = Sum.inr code) ∧
  i ∈ l.pending ∧
  (∃ code, followers i = Sum.inr code ∧
    code.lastDown = none) ∧
  CoordinatorLocalArmChoice.storedDownFlatWord
    (payloadWithUnitAnchor (p := p) (rate := rate)
      key.1.2.1 key.1.2.2.1 key.1.2.2.2) i = wD

/-- The code branches whose original anchor vector is identically one. -/
def readyCodeBranchSet
    (i : Fin (p.m - 1))
    (wD : AffineChannelLaw.Word (AffineBatchDecoder.width p)) :
    Set (CodeBranch p rate) :=
  {b | (∀ a : Fin p.K, b.1 a = 1) ∧ readyCodeKeyCheck (p := p) (rate := rate) i wD b.2}

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
    Measurable (fun x : FollowerPrepareJointMeasurability.CarriedState p rate =>
      x.1.1) := by
  apply measurable_of_sigma_sections
  intro index
  simp

private theorem measurable_followerStateTag :
    Measurable (followerStateTag (p := p) (rate := rate)) := by
  have hordinary : Measurable (fun x :
      FollowerPrepareJointMeasurability.CarriedState p rate ×
        FollowerPrepareJointMeasurability.LocalMemoryCode p =>
      (Sum.inr (x.1.1.1) : Unit ⊕ FollowerDownMeasurability.FollowerStateCode p rate)) := by
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
  have hfollowers : Measurable
      (fun c : StateCode p rate => c.2.2.2) :=
    measurable_snd.comp (measurable_snd.comp measurable_snd)
  apply measurable_pi_iff.mpr
  intro j
  exact (measurable_followerStateTag (p := p) (rate := rate)).comp
    ((measurable_pi_apply j).comp hfollowers)

private theorem measurable_collectionCoordinatorCodeView :
    Measurable (collectionCoordinatorCodeView (p := p) (rate := rate)) := by
  unfold collectionCoordinatorCodeView
  apply Measurable.sumElim
  · exact measurable_const
  · apply Measurable.sumElim
    · exact measurable_const
    · apply Measurable.sumElim
      · exact measurable_inr.comp measurable_id
      · exact measurable_const

private theorem measurable_payloadN : Measurable (fun x : Payload rate => x.n) := by
  exact measurable_fst.comp
    (ReferenceCollectionDispatchMeasurability.measurable_payloadObservation
      (p := p) (rate := rate))

private theorem measurable_payloadAnchor :
    Measurable (fun x : Payload rate => x.anchor) := by
  have hobs := ReferenceCollectionDispatchMeasurability.measurable_payloadObservation
    (p := p) (rate := rate)
  exact measurable_fst.comp
    (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp hobs)))

private theorem measurable_payloadQueueCode :
    Measurable (fun x : Payload rate =>
      (⟨x.queues, x.queues_le_TD⟩ : QueueCode p)) := by
  have hobs := ReferenceCollectionDispatchMeasurability.measurable_payloadObservation
    (p := p) (rate := rate)
  have hqueues : Measurable (fun x : Payload rate =>
      (LaterAssignmentStartMeasurability.payloadObservation x).2.2.2.2) := by
    exact measurable_snd.comp
      (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp hobs)))
  exact hqueues.subtype_mk

private theorem measurable_payloadDiscreteCode :
    Measurable (payloadDiscreteCode (p := p) (rate := rate)) := by
  have hn := measurable_payloadN (p := p) (rate := rate)
  have hsigma := ReferenceCollectionDispatchMeasurability.measurable_payloadSigma
    (p := p) (rate := rate)
  have hslow := ReferenceCollectionDispatchMeasurability.measurable_payloadSlowSet
    (p := p) (rate := rate)
  have hqueues := measurable_payloadQueueCode (p := p) (rate := rate)
  exact hn.prodMk (hsigma.prodMk (hslow.prodMk hqueues))

private theorem measurable_readyCodeKeyOfBranch :
    Measurable (readyCodeKeyOfBranch (p := p) (rate := rate)) := by
  let payloadMap :
      (Payload rate × (Ledger rate × Option (Fin p.T × Bool))) ×
        (CoordinatorUpReception.UpDecoderBank p × (Fin p.T × FollowerTags p rate)) →
        Payload rate := fun d => d.1.1
  let Domain := (Payload rate × (Ledger rate × Option (Fin p.T × Bool))) ×
    (CoordinatorUpReception.UpDecoderBank p × (Fin p.T × FollowerTags p rate))
  have hp : Measurable payloadMap := measurable_fst.comp measurable_fst
  have hpayloadCode : Measurable (fun d : Domain =>
      payloadDiscreteCode (p := p) (rate := rate) (payloadMap d)) :=
    (measurable_payloadDiscreteCode (p := p) (rate := rate)).comp hp
  have hl : Measurable (fun d : Domain => d.1.2.1) :=
    measurable_fst.comp (measurable_snd.comp measurable_fst)
  have hsaved : Measurable (fun d : Domain => d.1.2.2) :=
    measurable_snd.comp (measurable_snd.comp measurable_fst)
  have hbank : Measurable (fun d : Domain => d.2.1) := measurable_fst.comp measurable_snd
  have htime : Measurable (fun d : Domain => d.2.2.1) :=
    measurable_fst.comp (measurable_snd.comp measurable_snd)
  have hfollowers : Measurable (fun d : Domain => d.2.2.2) :=
    measurable_snd.comp (measurable_snd.comp measurable_snd)
  have hright : Measurable (fun d : Domain =>
      (d.1.2.1, (d.1.2.2, (d.2.1, (d.2.2.1, d.2.2.2))))) :=
    hl.prodMk (hsaved.prodMk (hbank.prodMk (htime.prodMk hfollowers)))
  convert hpayloadCode.prodMk hright using 1
  rfl

private abbrev CoordinatorCollectionView (p : Parameters) (rate : RateInput p) :=
  Unit ⊕ (Payload rate × (Ledger rate × Option (Fin p.T × Bool)))

private abbrev CodeAux (p : Parameters) (rate : RateInput p) :=
  CoordinatorUpReception.UpDecoderBank p × (Fin p.T × FollowerTags p rate)

private def attachCodeAux (x : CoordinatorCollectionView p rate × CodeAux p rate) :
    CodeView p rate :=
  match x.1 with
  | .inl _ => .inl ()
  | .inr branch =>
      .inr (branch.1.anchor,
        readyCodeKeyOfBranch (p := p) (rate := rate) (branch, x.2))

private theorem measurable_attachCodeAux :
    Measurable (attachCodeAux (p := p) (rate := rate)) := by
  let B := Payload rate × (Ledger rate × Option (Fin p.T × Bool))
  have hleft : Measurable (fun x : Unit × CodeAux p rate =>
      (Sum.inl () : CodeView p rate)) := measurable_const
  have hrData : Measurable (fun x : B × CodeAux p rate =>
      (x.1.1.anchor, readyCodeKeyOfBranch (p := p) (rate := rate) x)) := by
    exact (measurable_payloadAnchor.comp (measurable_fst.comp measurable_fst)).prodMk
      (measurable_readyCodeKeyOfBranch (p := p) (rate := rate))
  have hright : Measurable (fun x : B × CodeAux p rate =>
      (Sum.inr (x.1.1.anchor, readyCodeKeyOfBranch (p := p) (rate := rate) x) :
        CodeView p rate)) := measurable_inr.comp hrData
  have hsum := (hleft.sumElim hright).comp
    (MeasurableEquiv.sumProdDistrib Unit B (CodeAux p rate)).measurable_toFun
  convert hsum using 1
  funext x
  rcases x with ⟨tag, aux⟩
  cases tag with
  | inl u =>
      change attachCodeAux (Sum.inl u, aux) =
        Sum.elim (fun _ => (Sum.inl () : CodeView p rate))
          (fun x => Sum.inr (x.1.1.anchor, readyCodeKeyOfBranch x))
          (Equiv.sumProdDistrib Unit B (CodeAux p rate) (Sum.inl u, aux))
      simp [attachCodeAux, Equiv.sumProdDistrib_apply_left]
  | inr b =>
      change attachCodeAux (Sum.inr b, aux) =
        Sum.elim (fun _ => (Sum.inl () : CodeView p rate))
          (fun x => Sum.inr (x.1.1.anchor, readyCodeKeyOfBranch x))
          (Equiv.sumProdDistrib Unit B (CodeAux p rate) (Sum.inr b, aux))
      simp [attachCodeAux, Equiv.sumProdDistrib_apply_right]

private theorem measurable_collectionDownReadyCodeView (t : Fin p.T) :
    Measurable (collectionDownReadyCodeView (p := p) (rate := rate) t) := by
  have hcoord := measurable_collectionCoordinatorCodeView (p := p) (rate := rate)
  have htags := measurable_followerStateCodeTags (p := p) (rate := rate)
  have hbank : Measurable (fun c : StateCode p rate => c.2.1) :=
    measurable_fst.comp measurable_snd
  have haux : Measurable (fun c : StateCode p rate =>
      (c.2.1, (t, followerStateCodeTags (p := p) (rate := rate) c))) :=
    hbank.prodMk (measurable_const.prodMk htags)
  have hsplit : Measurable (fun c : StateCode p rate =>
      (collectionCoordinatorCodeView (p := p) (rate := rate) c.1,
        (c.2.1, (t, followerStateCodeTags (p := p) (rate := rate) c)))) :=
    (hcoord.comp measurable_fst).prodMk haux
  have h := (measurable_attachCodeAux (p := p) (rate := rate)).comp hsplit
  convert h using 1
  funext c
  rcases c with ⟨coord, rest⟩
  cases coord <;> simp [collectionDownReadyCodeView, collectionCoordinatorCodeView,
    readyCodeKeyOfBranch, attachCodeAux]
  all_goals rfl

private theorem countable_readyCodeKey : Countable (ReadyCodeKey p rate) := inferInstance

private theorem measurableSet_singleton_prod {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (a : α) (b : β) (ha : MeasurableSet ({a} : Set α))
    (hb : MeasurableSet ({b} : Set β)) :
    MeasurableSet ({(a, b)} : Set (α × β)) := by
  have hset : ({(a, b)} : Set (α × β)) = {a} ×ˢ {b} := by
    ext ⟨x, y⟩
    simp [eq_comm]
  rw [hset]
  exact ha.prod hb

private theorem measurableSet_singleton_readyCodeKey (key : ReadyCodeKey p rate) :
    MeasurableSet ({key} : Set (ReadyCodeKey p rate)) := by
  rcases key with ⟨left, right⟩
  rcases left with ⟨n, payloadData⟩
  rcases payloadData with ⟨sigma, slowQueue⟩
  rcases slowQueue with ⟨slow, queues⟩
  rcases right with ⟨ledger, right⟩
  rcases right with ⟨saved, right⟩
  rcases right with ⟨bank, timeTags⟩
  rcases timeTags with ⟨time, tags⟩
  have htag : ∀ tag : FollowerTag p rate,
      MeasurableSet ({tag} : Set (FollowerTag p rate)) := by
    intro tag
    cases tag with
    | inl u =>
        rw [measurableSet_sum_iff]
        constructor
        · have hpre : Sum.inl ⁻¹' ({Sum.inl u} : Set
              (Unit ⊕ FollowerDownMeasurability.FollowerStateCode p rate)) = {u} := by
            ext x
            simp
          rw [hpre]
          exact measurableSet_singleton u
        · have hpre : Sum.inr ⁻¹' ({Sum.inl u} : Set
              (Unit ⊕ FollowerDownMeasurability.FollowerStateCode p rate)) = ∅ := by
            ext x
            simp
          rw [hpre]
          exact MeasurableSet.empty
    | inr code =>
        rw [measurableSet_sum_iff]
        constructor
        · have hpre : Sum.inl ⁻¹' ({Sum.inr code} : Set
              (Unit ⊕ FollowerDownMeasurability.FollowerStateCode p rate)) = ∅ := by
            ext x
            simp
          rw [hpre]
          exact MeasurableSet.empty
        · have hpre : Sum.inr ⁻¹' ({Sum.inr code} : Set
              (Unit ⊕ FollowerDownMeasurability.FollowerStateCode p rate)) = {code} := by
            ext x
            simp
          rw [hpre]
          exact measurableSet_singleton code
  have htags : MeasurableSet ({tags} : Set (FollowerTags p rate)) := by
    rw [show ({tags} : Set (FollowerTags p rate)) =
        ⋂ j : Fin (p.m - 1), {f : FollowerTags p rate | f j = tags j} by
          ext f
          simp only [Set.mem_singleton_iff, Set.mem_iInter, Set.mem_ofPred_eq]
          constructor
          · intro hf j
            simp [hf]
          · intro hf
            funext j
            exact hf j]
    apply MeasurableSet.iInter
    intro j
    exact (htag (tags j)).preimage (measurable_pi_apply j)
  have htagsingle := measurableSet_singleton_prod time tags
    (measurableSet_singleton time) htags
  have hbanktags := measurableSet_singleton_prod bank (time, tags)
    (measurableSet_singleton bank) htagsingle
  have hsavedbanktags := measurableSet_singleton_prod saved (bank, (time, tags))
    (measurableSet_singleton saved) hbanktags
  have hright := measurableSet_singleton_prod ledger (saved, (bank, (time, tags)))
    (measurableSet_singleton ledger) hsavedbanktags
  have hslowQueue := measurableSet_singleton_prod slow queues
    (measurableSet_singleton slow) (measurableSet_singleton queues)
  have hsigmaslowQueue := measurableSet_singleton_prod sigma (slow, queues)
    (measurableSet_singleton sigma) hslowQueue
  have hleft := measurableSet_singleton_prod n (sigma, (slow, queues))
    (measurableSet_singleton n) hsigmaslowQueue
  exact measurableSet_singleton_prod (n, (sigma, (slow, queues)))
    (ledger, (saved, (bank, (time, tags)))) hleft hright

private theorem measurableSet_anchorOne :
    MeasurableSet {a : AnchorCoordinates p | ∀ j : Fin p.K, a j = (1 : ℝ)} := by
  rw [show {a : AnchorCoordinates p | ∀ j : Fin p.K, a j = (1 : ℝ)} =
      ⋂ j : Fin p.K, {a : AnchorCoordinates p | a j = (1 : ℝ)} by
        ext a
        simp]
  apply MeasurableSet.iInter
  intro j
  exact (measurableSet_singleton (1 : ℝ)).preimage (measurable_pi_apply j)

private theorem measurableSet_readyCodeBranchSet
    (i : Fin (p.m - 1))
    (wD : AffineChannelLaw.Word (AffineBatchDecoder.width p)) :
    MeasurableSet (readyCodeBranchSet (p := p) (rate := rate) i wD) := by
  let goodKeys : Set (ReadyCodeKey p rate) :=
    {key | readyCodeKeyCheck (p := p) (rate := rate) i wD key}
  have hgoodKeys : MeasurableSet goodKeys := by
    rw [show goodKeys = ⋃ key : ReadyCodeKey p rate,
        if key ∈ goodKeys then ({key} : Set (ReadyCodeKey p rate)) else ∅ by
          ext key
          simp]
    apply MeasurableSet.iUnion
    intro key
    by_cases hk : key ∈ goodKeys
    · simp [hk]
      exact measurableSet_singleton_readyCodeKey (p := p) (rate := rate) key
    · simp [hk]
  have hEq : readyCodeBranchSet (p := p) (rate := rate) i wD =
      Set.prod {a : AnchorCoordinates p | ∀ j : Fin p.K, a j = (1 : ℝ)} goodKeys := by
    ext b
    rcases b with ⟨a, key⟩
    change ((∀ j : Fin p.K, a j = (1 : ℝ)) ∧
        readyCodeKeyCheck (p := p) (rate := rate) i wD key) ↔
      a ∈ {a : AnchorCoordinates p | ∀ j : Fin p.K, a j = (1 : ℝ)} ∧ key ∈ goodKeys
    rfl
  rw [hEq]
  exact measurableSet_anchorOne.prod hgoodKeys

/-- The ready-support set on the real-anchor/countable-key code view. -/
def collectionDownReadySupportViewSet
    (i : Fin (p.m - 1))
    (wD : AffineChannelLaw.Word (AffineBatchDecoder.width p)) :
    Set (CodeView p rate) :=
  Sum.inr '' readyCodeBranchSet (p := p) (rate := rate) i wD

/-- Pull the ready-support view set back to the canonical physical state code. -/
def collectionDownReadySupportCodeSet
    (i : Fin (p.m - 1))
    (t : Fin p.T)
    (wD : AffineChannelLaw.Word (AffineBatchDecoder.width p)) :
    Set (StateCode p rate) :=
  (collectionDownReadyCodeView (p := p) (rate := rate) t) ⁻¹'
    collectionDownReadySupportViewSet (p := p) (rate := rate) i wD

/-- Literal support on the incoming optional code, with absence kept false. -/
def collectionDownReadySupportIncomingSet
    (i : Fin (p.m - 1))
    (t : Fin p.T)
    (wD : AffineChannelLaw.Word (AffineBatchDecoder.width p)) :
    Set (Option (StateCode p rate)) :=
  {c | ∃ code, c = some code ∧ code ∈
    collectionDownReadySupportCodeSet (p := p) (rate := rate) i t wD}

private theorem measurableSet_collectionDownReadySupportViewSet
    (i : Fin (p.m - 1))
    (wD : AffineChannelLaw.Word (AffineBatchDecoder.width p)) :
    MeasurableSet (collectionDownReadySupportViewSet (p := p) (rate := rate) i wD) := by
  rw [measurableSet_sum_iff]
  constructor
  · have hpre : Sum.inl ⁻¹' collectionDownReadySupportViewSet
        (p := p) (rate := rate) i wD = ∅ := by
      ext u
      simp [collectionDownReadySupportViewSet]
    rw [hpre]
    exact MeasurableSet.empty
  · have hpre : Sum.inr ⁻¹' collectionDownReadySupportViewSet
        (p := p) (rate := rate) i wD = readyCodeBranchSet (p := p) (rate := rate) i wD := by
      ext b
      simp [collectionDownReadySupportViewSet]
    rw [hpre]
    exact measurableSet_readyCodeBranchSet (p := p) (rate := rate) i wD

private theorem measurableSet_collectionDownReadySupportCodeSet
    (i : Fin (p.m - 1)) (t : Fin p.T)
    (wD : AffineChannelLaw.Word (AffineBatchDecoder.width p)) :
    MeasurableSet (collectionDownReadySupportCodeSet (p := p) (rate := rate) i t wD) := by
  unfold collectionDownReadySupportCodeSet
  exact (measurableSet_collectionDownReadySupportViewSet
    (p := p) (rate := rate) i wD).preimage
      (measurable_collectionDownReadyCodeView (p := p) (rate := rate) t)

private theorem measurableSet_collectionDownReadySupportIncomingSet
    (i : Fin (p.m - 1)) (t : Fin p.T)
    (wD : AffineChannelLaw.Word (AffineBatchDecoder.width p)) :
    MeasurableSet (collectionDownReadySupportIncomingSet (p := p) (rate := rate) i t wD) := by
  let e := Equiv.optionEquivSumPUnit (StateCode p rate)
  have hsum : MeasurableSet
      {v : StateCode p rate ⊕ PUnit | v.elim
        (fun c => c ∈ collectionDownReadySupportCodeSet (p := p) (rate := rate) i t wD)
        (fun _ => False)} := by
    rw [measurableSet_sum_iff]
    constructor
    · exact measurableSet_collectionDownReadySupportCodeSet (p := p) (rate := rate) i t wD
    · exact MeasurableSet.empty
  have hpre : collectionDownReadySupportIncomingSet (p := p) (rate := rate) i t wD =
      e ⁻¹' {v : StateCode p rate ⊕ PUnit | v.elim
        (fun c => c ∈ collectionDownReadySupportCodeSet (p := p) (rate := rate) i t wD)
        (fun _ => False)} := by
    ext c
    cases c with
    | none =>
        change (∃ code, none = some code ∧
            code ∈ collectionDownReadySupportCodeSet (p := p) (rate := rate) i t wD) ↔
          e none ∈ {v : StateCode p rate ⊕ PUnit | v.elim
            (fun c => c ∈ collectionDownReadySupportCodeSet
              (p := p) (rate := rate) i t wD) (fun _ => False)}
        rw [Equiv.optionEquivSumPUnit_none]
        simp
    | some code =>
        change (∃ code', some code = some code' ∧
            code' ∈ collectionDownReadySupportCodeSet (p := p) (rate := rate) i t wD) ↔
          e (some code) ∈ {v : StateCode p rate ⊕ PUnit | v.elim
            (fun c => c ∈ collectionDownReadySupportCodeSet
              (p := p) (rate := rate) i t wD) (fun _ => False)}
        rw [Equiv.optionEquivSumPUnit_some]
        simp
  rw [hpre]
  exact hsum.preimage (comap_measurable e)

private def readyCodeKeyOfInput (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (payload : Payload rate) (l : Ledger rate)
    (saved : Option (Fin p.T × Bool)) : ReadyCodeKey p rate :=
  let followers := fun j => followerStateTag
    (FollowerPrepareJointMeasurability.incomingOfLocalConfiguration rate
      (x.state.followers j))
  (payloadDiscreteCode (p := p) (rate := rate) payload,
    (l, (saved, (x.state.upDecoderBank, (x.time, followers)))))

private theorem payload_eq_unitAnchor (payload : Payload rate)
    (hn : payload.n = rate.n)
    (hanchor : ∀ a : Fin p.K, payload.anchor a = (1 : ℝ)) :
    payload = payloadWithUnitAnchor (p := p) (rate := rate) payload.sigma
      payload.slowSet ⟨payload.queues, payload.queues_le_TD⟩ := by
  rcases payload with ⟨cap, n, nScale, sigma, slowSet, anchor, anchorPos, queues, queuesBound⟩
  dsimp only at hn hanchor ⊢
  subst n
  have hanchorEq : anchor = fun _ => (1 : ℝ) := funext hanchor
  subst anchor
  rfl

private theorem readyDomain_expand
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (payload : Payload rate) (l : Ledger rate)
    (saved : Option (Fin p.T × Bool)) :
    ReferenceContinuingCollectionStartDomains.continuingCollectionReadyDomain
        x payload l saved ↔
      x.state.coordinator = .collection payload l saved ∧
      (∀ a : Fin p.K, payload.anchor a = (1 : ℝ)) ∧
      readyDomainCodeKeyCheck (p := p) (rate := rate)
        (readyCodeKeyOfInput (p := p) (rate := rate) x payload l saved) := by
  simp [ReferenceContinuingCollectionStartDomains.continuingCollectionReadyDomain,
    readyDomainCodeKeyCheck, readyCodeKeyOfInput,
    AssignmentStartPayload.Input.assignment]
  tauto

private theorem followerStateTag_encode_configuration
    (configuration : DeclaredFollowerLocalRound.LocalConfiguration p rate) :
    followerStateTag (p := p) (rate := rate)
        (FollowerPrepareJointMeasurability.incomingOfLocalConfiguration rate configuration) =
      match configuration with
      | .dagger => Sum.inl ()
      | .ordinary state _ => Sum.inr (FollowerDownMeasurability.followerStateCode rate state) := by
  cases configuration <;> rfl

private theorem collectionDownReadyCodeView_encodeState_collection
    (x : ReferenceActivePhysicalStep.RoundInput p rate) (t : Fin p.T)
    (payload : Payload rate) (l : Ledger rate) (saved : Option (Fin p.T × Bool))
    (hcoord : x.state.coordinator = .collection payload l saved) :
    collectionDownReadyCodeView (p := p) (rate := rate) t
        (ReferenceActivePhysicalStepMeasurability.encodeState x.state) =
      Sum.inr (payload.anchor,
        readyCodeKeyOfBranch (p := p) (rate := rate)
          ((payload, (l, saved)),
            (x.state.upDecoderBank, (t, fun j => followerStateTag
              (FollowerPrepareJointMeasurability.incomingOfLocalConfiguration rate
                (x.state.followers j)))))) := by
  simp only [collectionDownReadyCodeView, collectionCoordinatorCodeView,
    ReferenceActivePhysicalStepMeasurability.encodeState,
    ReferenceActivePhysicalStepMeasurability.encodeCoordinator, hcoord]
  congr 1

private theorem recordReadySupport_iff_code
    (x : ReferenceActivePhysicalStep.RoundInput p rate) (t : Fin p.T)
    (htime : x.time = t)
    (i : Fin (p.m - 1))
    (wD : AffineChannelLaw.Word (AffineBatchDecoder.width p)) :
    (∃ (payload : Payload rate) (l : Ledger rate)
        (saved : Option (Fin p.T × Bool))
        (old : ReferencePrelaunchFollower.State p rate.eta)
        (memory : ActiveFollowerLifecycle.LocalMemory p),
        ReferenceContinuingCollectionStartDomains.continuingCollectionReadyDomain
          x payload l saved ∧
        i ∈ l.pending ∧
        x.state.followers i = .ordinary old memory ∧
        old.lastDown = none ∧
        CoordinatorLocalArmChoice.storedDownFlatWord payload i = wD ∧
        ∀ j : Fin (p.m - 1), x.state.followers j ≠ .dagger) ↔
      ReferenceActivePhysicalStepMeasurability.encodeState x.state ∈
        collectionDownReadySupportCodeSet (p := p) (rate := rate) i t wD := by
  have hdecode := congrArg ReferenceActivePhysicalStep.State.coordinator
    (ReferenceActivePhysicalStepMeasurability.decodeState_encodeState x.state)
  cases hcoord : (ReferenceActivePhysicalStepMeasurability.decodeState
      (ReferenceActivePhysicalStepMeasurability.encodeState x.state)).coordinator with
  | first =>
      rw [hdecode] at hcoord
      simp [collectionDownReadySupportCodeSet, collectionDownReadyCodeView,
        collectionCoordinatorCodeView, hcoord,
        ReferenceActivePhysicalStepMeasurability.encodeState,
        ReferenceActivePhysicalStepMeasurability.encodeCoordinator,
        ReferenceContinuingCollectionStartDomains.continuingCollectionReadyDomain,
        collectionDownReadySupportViewSet]
  | dagger =>
      rw [hdecode] at hcoord
      simp [collectionDownReadySupportCodeSet, collectionDownReadyCodeView,
        collectionCoordinatorCodeView, hcoord,
        ReferenceActivePhysicalStepMeasurability.encodeState,
        ReferenceActivePhysicalStepMeasurability.encodeCoordinator,
        ReferenceContinuingCollectionStartDomains.continuingCollectionReadyDomain,
        collectionDownReadySupportViewSet]
  | live registers owned base =>
      rw [hdecode] at hcoord
      simp [collectionDownReadySupportCodeSet, collectionDownReadyCodeView,
        collectionCoordinatorCodeView, hcoord,
        ReferenceActivePhysicalStepMeasurability.encodeState,
        ReferenceActivePhysicalStepMeasurability.encodeCoordinator,
        ReferenceContinuingCollectionStartDomains.continuingCollectionReadyDomain,
        collectionDownReadySupportViewSet]
  | collection payload0 l0 saved0 =>
      rw [hdecode] at hcoord
      have hview := collectionDownReadyCodeView_encodeState_collection
        (p := p) (rate := rate) x t payload0 l0 saved0 hcoord
      rw [collectionDownReadySupportCodeSet, Set.mem_preimage, hview,
        collectionDownReadySupportViewSet]
      change (∃ (payload : Payload rate) (l : Ledger rate)
          (saved : Option (Fin p.T × Bool))
          (old : ReferencePrelaunchFollower.State p rate.eta)
          (memory : ActiveFollowerLifecycle.LocalMemory p),
          ReferenceContinuingCollectionStartDomains.continuingCollectionReadyDomain
              x payload l saved ∧
            i ∈ l.pending ∧ x.state.followers i = .ordinary old memory ∧
              old.lastDown = none ∧
              CoordinatorLocalArmChoice.storedDownFlatWord payload i = wD ∧
              ∀ j : Fin (p.m - 1), x.state.followers j ≠ .dagger) ↔
        Sum.inr (payload0.anchor,
          readyCodeKeyOfBranch (p := p) (rate := rate)
            ((payload0, (l0, saved0)),
              (x.state.upDecoderBank, (t, fun j => followerStateTag
                (FollowerPrepareJointMeasurability.incomingOfLocalConfiguration rate
                  (x.state.followers j)))))) ∈
          Sum.inr '' readyCodeBranchSet (p := p) (rate := rate) i wD
      simp only [Set.mem_image, Sum.inr.injEq, exists_eq_right]
      rw [readyCodeBranchSet]
      dsimp [readyCodeKeyOfBranch]
      constructor
      · rintro ⟨payload, l, saved, old, memory, hReady, hip, hfi, hnone, hword,
          hordinary⟩
        have hshape := (readyDomain_expand (p := p) (rate := rate) x payload l saved).mp hReady
        have hsame : ReferenceActivePhysicalStep.CoordinatorConfiguration.collection
            payload l saved = .collection payload0 l0 saved0 := by
          calc
            _ = x.state.coordinator := hshape.1.symm
            _ = _ := hcoord
        injection hsame with hp hl hs
        subst payload
        subst l
        subst saved
        let branchKey := readyCodeKeyOfBranch (p := p) (rate := rate)
          ((payload0, (l0, saved0)),
            (x.state.upDecoderBank, (t, fun j => followerStateTag
              (FollowerPrepareJointMeasurability.incomingOfLocalConfiguration rate
                (x.state.followers j)))))
        have hkeyEq : readyCodeKeyOfInput (p := p) (rate := rate) x payload0 l0 saved0 =
            branchKey := by
          simp [branchKey, readyCodeKeyOfInput, readyCodeKeyOfBranch, htime]
        have hreadyKey : readyDomainCodeKeyCheck (p := p) (rate := rate) branchKey := by
          rw [← hkeyEq]
          exact hshape.2.2
        have hpayloadN : payload0.n = rate.n := by
          simpa [branchKey, readyCodeKeyOfBranch, payloadDiscreteCode] using hreadyKey.1
        have hunit := payload_eq_unitAnchor (p := p) (rate := rate)
          payload0 hpayloadN hshape.2.1
        have hwordUnit : CoordinatorLocalArmChoice.storedDownFlatWord
            (payloadWithUnitAnchor (p := p) (rate := rate) payload0.sigma
              payload0.slowSet ⟨payload0.queues, payload0.queues_le_TD⟩) i = wD := by
          rw [← hunit]
          exact hword
        have htags : ∀ j : Fin (p.m - 1), ∃ code,
            followerStateTag (p := p) (rate := rate)
              (FollowerPrepareJointMeasurability.incomingOfLocalConfiguration rate
                (x.state.followers j)) = Sum.inr code := by
          intro j
          cases hconfig : x.state.followers j with
          | dagger => exact (hordinary j hconfig).elim
          | ordinary state mem =>
              exact ⟨FollowerDownMeasurability.followerStateCode rate state, by
                simp [followerStateTag_encode_configuration]⟩
        have htagI : followerStateTag (p := p) (rate := rate)
            (FollowerPrepareJointMeasurability.incomingOfLocalConfiguration rate
              (x.state.followers i)) =
              Sum.inr (FollowerDownMeasurability.followerStateCode rate old) := by
          rw [hfi]
          simp [followerStateTag_encode_configuration]
        have hcodeNone :
            (FollowerDownMeasurability.followerStateCode rate old).lastDown = none := by
          simpa [FollowerDownMeasurability.followerStateCode] using hnone
        refine ⟨hshape.2.1, ?_⟩
        exact ⟨hreadyKey, htags, hip,
          ⟨FollowerDownMeasurability.followerStateCode rate old, htagI, hcodeNone⟩,
          by simpa [branchKey, readyCodeKeyOfBranch, payloadDiscreteCode] using hwordUnit⟩
      · rintro ⟨hanchor, hreadyKey, htags, hip, ⟨code, htag, hcodeNone⟩, hwordCode⟩
        let branchKey := readyCodeKeyOfBranch (p := p) (rate := rate)
          ((payload0, (l0, saved0)),
            (x.state.upDecoderBank, (t, fun j => followerStateTag
              (FollowerPrepareJointMeasurability.incomingOfLocalConfiguration rate
                (x.state.followers j)))))
        have hdomain : readyDomainCodeKeyCheck (p := p) (rate := rate) branchKey := by
          exact hreadyKey
        have hReady := (readyDomain_expand (p := p) (rate := rate) x payload0 l0 saved0).mpr
          ⟨hcoord, hanchor, ?_⟩
        · have hordinary : ∀ j : Fin (p.m - 1), x.state.followers j ≠ .dagger := by
            intro j hdagger
            have htagj : ∃ code, followerStateTag (p := p) (rate := rate)
                (FollowerPrepareJointMeasurability.incomingOfLocalConfiguration rate
                  (x.state.followers j)) = Sum.inr code := by
              exact htags j
            rw [hdagger, followerStateTag_encode_configuration] at htagj
            rcases htagj with ⟨codeJ, hcodeJ⟩
            exact Sum.inl_ne_inr hcodeJ
          cases hconfig : x.state.followers i with
          | dagger =>
              have hi : ∃ code, followerStateTag (p := p) (rate := rate)
                  (FollowerPrepareJointMeasurability.incomingOfLocalConfiguration rate
                    (x.state.followers i)) = Sum.inr code := by
                exact htags i
              rw [hconfig, followerStateTag_encode_configuration] at hi
              rcases hi with ⟨codeI, hcodeI⟩
              exact (Sum.inl_ne_inr hcodeI).elim
          | ordinary old memory =>
              have htagI : followerStateTag (p := p) (rate := rate)
                  (FollowerPrepareJointMeasurability.incomingOfLocalConfiguration rate
                    (x.state.followers i)) =
                    Sum.inr (FollowerDownMeasurability.followerStateCode rate old) := by
                rw [hconfig]
                simp [followerStateTag_encode_configuration]
              have hcodeEq : code = FollowerDownMeasurability.followerStateCode rate old :=
                Sum.inr.inj (htag.symm.trans htagI)
              subst code
              have hpayloadN : payload0.n = rate.n := by
                simpa [branchKey, readyCodeKeyOfBranch, payloadDiscreteCode] using hdomain.1
              have hunit := payload_eq_unitAnchor (p := p) (rate := rate)
                payload0 hpayloadN hanchor
              have hword : CoordinatorLocalArmChoice.storedDownFlatWord payload0 i = wD := by
                rw [hunit]
                simpa [readyCodeKeyOfBranch, payloadDiscreteCode] using hwordCode
              have hnone : old.lastDown = none := by
                simpa [FollowerDownMeasurability.followerStateCode] using hcodeNone
              exact ⟨payload0, l0, saved0, old, memory, hReady, hip, rfl,
                hnone, hword, hordinary⟩
        · have hkeyEq : readyCodeKeyOfInput (p := p) (rate := rate)
              x payload0 l0 saved0 = readyCodeKeyOfBranch (p := p) (rate := rate)
                ((payload0, (l0, saved0)),
                  (x.state.upDecoderBank, (t, fun j => followerStateTag
                    (FollowerPrepareJointMeasurability.incomingOfLocalConfiguration rate
                      (x.state.followers j))))) := by
            simp [readyCodeKeyOfInput, readyCodeKeyOfBranch, payloadDiscreteCode, htime]
          rw [hkeyEq]
          exact hdomain


private theorem actualRecord_input_time_eq
    (rewards : RewardTable p) (C_star C_h : ℝ) (t : Fin p.T) (z : SourceInput p)
    (r : RoundRecord p rate)
    (hrecord : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z =
      some r) : r.input.time = t := by
  classical
  unfold ReferenceSourcePrefixHistoryFiltration.actualRecord at hrecord
  by_cases hstart : ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h ≤ t.val
  · rw [ite_eq_left hstart] at hrecord
    let records := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let index := t.val - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
    have hget : records[index]? = some r := hrecord
    have hidx : index < p.T -
        ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h := by
      have hlen := (List.getElem?_eq_some_iff.mp hget).1
      simpa [records, ReferenceCompletePhysicalHistory.completeSuffixRecords_length] using hlen
    have htimeAt := congrArg (fun xs : List ℕ => xs[index]?)
      (ReferenceCompletePhysicalHistory.completeSuffixRecords_time_values
        rate z rewards C_star C_h)
    rw [List.getElem?_map, hget] at htimeAt
    simp only [Option.map_some, ReferenceActivePhysicalHorizon.calendar,
      List.getElem?_range' hidx, Nat.one_mul] at htimeAt
    have hval : r.input.time.val = t.val := by
      have hEq : r.input.time.val =
          ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + index :=
        Option.some.inj htimeAt
      dsimp [index] at hEq
      omega
    exact Fin.ext hval
  · rw [ite_eq_right hstart] at hrecord
    simp at hrecord

private theorem incomingSupportSet_some_iff
    (i : Fin (p.m - 1)) (t : Fin p.T)
    (wD : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (code : StateCode p rate) :
    some code ∈ collectionDownReadySupportIncomingSet (p := p) (rate := rate) i t wD ↔
      code ∈ collectionDownReadySupportCodeSet (p := p) (rate := rate) i t wD := by
  simp only [collectionDownReadySupportIncomingSet, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨code', hcode, hmem⟩
    exact Option.some.inj hcode ▸ hmem
  · intro hmem
    exact ⟨code, rfl, hmem⟩

/-- The literal source event is exactly the accepted incoming optional
canonical state code; absence of an actual record maps to `none` and is false. -/
theorem collectionDownReadySupport_iff_incoming
    (rewards : RewardTable p) (C_star C_h : ℝ)
    (i : Fin (p.m - 1)) (t : Fin p.T)
    (wD : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (z : SourceInput p) :
    z ∈ collectionDownReadySupport (p := p) (rate := rate) rewards C_star C_h i t wD ↔
      ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t z ∈
        collectionDownReadySupportIncomingSet (p := p) (rate := rate) i t wD := by
  classical
  unfold collectionDownReadySupport
  cases hrecord : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t z with
  | none =>
      simp [ReferenceSourcePrefixHistoryFiltration.incoming, hrecord,
        collectionDownReadySupportIncomingSet]
  | some r =>
      have htime := actualRecord_input_time_eq (p := p) (rate := rate)
        rewards C_star C_h t z r hrecord
      have hcode := recordReadySupport_iff_code (p := p) (rate := rate)
        r.input t htime i wD
      have hleft :
          (∃ r' : RoundRecord p rate,
            ReferenceSourcePrefixHistoryFiltration.actualRecord
              rate rewards C_star C_h t z = some r' ∧
            ∃ (payload : Payload rate) (l : Ledger rate)
              (saved : Option (Fin p.T × Bool))
              (old : ReferencePrelaunchFollower.State p rate.eta)
              (memory : ActiveFollowerLifecycle.LocalMemory p),
              ReferenceContinuingCollectionStartDomains.continuingCollectionReadyDomain
                r'.input payload l saved ∧
              i ∈ l.pending ∧
              r'.input.state.followers i = .ordinary old memory ∧
              old.lastDown = none ∧
              CoordinatorLocalArmChoice.storedDownFlatWord payload i = wD ∧
              ∀ j : Fin (p.m - 1), r'.input.state.followers j ≠ .dagger) ↔
          (∃ (payload : Payload rate) (l : Ledger rate)
            (saved : Option (Fin p.T × Bool))
            (old : ReferencePrelaunchFollower.State p rate.eta)
            (memory : ActiveFollowerLifecycle.LocalMemory p),
            ReferenceContinuingCollectionStartDomains.continuingCollectionReadyDomain
              r.input payload l saved ∧
            i ∈ l.pending ∧
            r.input.state.followers i = .ordinary old memory ∧
            old.lastDown = none ∧
            CoordinatorLocalArmChoice.storedDownFlatWord payload i = wD ∧
            ∀ j : Fin (p.m - 1), r.input.state.followers j ≠ .dagger) := by
        constructor
        · rintro ⟨r', heq, hready⟩
          have hrsame : r' = r := Option.some.inj (heq.symm.trans hrecord)
          subst r'
          exact hready
        · intro hready
          exact ⟨r, hrecord, hready⟩
      have hincoming : ReferenceSourcePrefixHistoryFiltration.incoming
          rate rewards C_star C_h t z =
          some (ReferenceActivePhysicalStepMeasurability.encodeState r.input.state) := by
        simp [ReferenceSourcePrefixHistoryFiltration.incoming, hrecord]
      change (∃ r' : RoundRecord p rate,
        ReferenceSourcePrefixHistoryFiltration.actualRecord
          rate rewards C_star C_h t z = some r' ∧
        ∃ (payload : Payload rate) (l : Ledger rate)
          (saved : Option (Fin p.T × Bool))
          (old : ReferencePrelaunchFollower.State p rate.eta)
          (memory : ActiveFollowerLifecycle.LocalMemory p),
          ReferenceContinuingCollectionStartDomains.continuingCollectionReadyDomain
            r'.input payload l saved ∧
          i ∈ l.pending ∧
          r'.input.state.followers i = .ordinary old memory ∧
          old.lastDown = none ∧
          CoordinatorLocalArmChoice.storedDownFlatWord payload i = wD ∧
          ∀ j : Fin (p.m - 1), r'.input.state.followers j ≠ .dagger) ↔
        ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t z ∈
          collectionDownReadySupportIncomingSet (p := p) (rate := rate) i t wD
      rw [hincoming, incomingSupportSet_some_iff (p := p) (rate := rate) i t wD]
      exact hleft.trans hcode

/-- Measurability in the source current-control field, on the original source
space and its original law. -/
theorem collectionDownReadySupport_measurableSet
    (rewards : RewardTable p) (C_star C_h : ℝ)
    (control0 : TimeControl p) (i : Fin (p.m - 1)) (t : Fin p.T)
    (wD : AffineChannelLaw.Word (AffineBatchDecoder.width p)) :
    MeasurableSet[ReferenceSourceCurrentControlFreshness.m_t p control0 t]
      (collectionDownReadySupport (p := p) (rate := rate) rewards C_star C_h i t wD) := by
  have heq : collectionDownReadySupport (p := p) (rate := rate)
      rewards C_star C_h i t wD =
      (ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t) ⁻¹'
        collectionDownReadySupportIncomingSet (p := p) (rate := rate) i t wD := by
    ext z
    exact collectionDownReadySupport_iff_incoming (p := p) (rate := rate)
      rewards C_star C_h i t wD z
  rw [heq]
  have hincoming : Measurable[ReferenceSourceCurrentControlFreshness.m_t p control0 t]
      (ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t) := by
    rw [← ReferenceSourcePhysicalFlagConditionalLaw.sourcePrefixField_eq_m_t control0 t]
    exact ReferenceSourcePrefixHistoryFiltration.incoming_measurable
      rate rewards C_star C_h control0 t
  have hset := (measurableSet_collectionDownReadySupportIncomingSet
    (p := p) (rate := rate) i t wD).preimage hincoming
  exact hset

/-- The event is a function only of the strict source prefix at `t`. -/
theorem collectionDownReadySupport_factor
    (rewards : RewardTable p) (C_star C_h : ℝ)
    (control0 : TimeControl p) (i : Fin (p.m - 1)) (t : Fin p.T)
    (wD : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (z : SourceInput p) :
    z ∈ collectionDownReadySupport (p := p) (rate := rate) rewards C_star C_h i t wD ↔
      ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z ∈
        collectionDownReadySupport (p := p) (rate := rate) rewards C_star C_h i t wD := by
  rw [collectionDownReadySupport_iff_incoming (p := p) (rate := rate)
      rewards C_star C_h i t wD z,
    collectionDownReadySupport_iff_incoming (p := p) (rate := rate)
      rewards C_star C_h i t wD (ReferenceSourcePrefixHistoryFiltration.sourcePrefix
        control0 t.val z)]
  exact Iff.of_eq (congrArg
    (fun x => x ∈ collectionDownReadySupportIncomingSet (p := p) (rate := rate) i t wD)
    (ReferenceSourcePrefixHistoryFiltration.incoming_factor
      rate rewards C_star C_h control0 t z))

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
        simpa [ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex] using hrow
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

/-- Literal replacement of the current control leaves the event unchanged for
every replacement control. -/
theorem collectionDownReadySupport_replaceSourceControl
    (rewards : RewardTable p) (C_star C_h : ℝ)
    (control0 : TimeControl p) (i : Fin (p.m - 1)) (t : Fin p.T)
    (wD : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (z : SourceInput p) (c : TimeControl p) :
    z ∈ collectionDownReadySupport (p := p) (rate := rate) rewards C_star C_h i t wD ↔
      ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z c ∈
        collectionDownReadySupport (p := p) (rate := rate) rewards C_star C_h i t wD := by
  have hz := collectionDownReadySupport_factor (p := p) (rate := rate)
    rewards C_star C_h control0 i t wD z
  have hr := collectionDownReadySupport_factor (p := p) (rate := rate)
    rewards C_star C_h control0 i t wD
    (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z c)
  have hprefix := sourcePrefix_replaceSourceControl (p := p) control0 t z c
  calc
    z ∈ collectionDownReadySupport (p := p) (rate := rate) rewards C_star C_h i t wD
        ↔ ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z ∈
          collectionDownReadySupport (p := p) (rate := rate) rewards C_star C_h i t wD := hz
    _ ↔ ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val
          (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z c) ∈
          collectionDownReadySupport (p := p) (rate := rate) rewards C_star C_h i t wD :=
      iff_of_eq (congrArg (fun x => x ∈ collectionDownReadySupport
        (p := p) (rate := rate) rewards C_star C_h i t wD) hprefix.symm)
    _ ↔ ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z c ∈
          collectionDownReadySupport (p := p) (rate := rate) rewards C_star C_h i t wD := hr.symm

/-- At an actual first-collection record strictly after the cutoff, the literal
old-DOWN ready/pending branch belongs to the before-current support. The
all-ordinary clause, original full-calendar lookup, and canonical record
alignment are produced here.

The collection window includes the cutoff at index zero. Thus G's boundary is
`n.val - 1`, including its final boundary, rather than `n.val`. Sources:
`06_interruptions.tex:246-296,327-348,459-490`, `05_binary_transport.tex:70-124`,
and `07_public_setup.tex:127-164`. -/
theorem actual_first_collection_mem_collectionDownReadySupport
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (count : ℕ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hspan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed + count ≤ p.T)
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
        rate source rewards C_star C_h hcross count hspan).records).length < count) :
    let E := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
      rate source rewards C_star C_h hcross count hspan
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records).length
    let B := ReferenceCollectionPhaseHistory.collectionWindow E.records w
    ∀ (n : Fin B.length), 0 < n.val →
      ∀ (payload : ReferenceActivePhysicalStep.Payload rate)
        (l : ReferenceActivePhysicalStep.Ledger rate) (saved : Option (Fin p.T × Bool)),
      ReferenceContinuingCollectionStartDomains.continuingCollectionReadyDomain
        B[n.val].input payload l saved →
      ∀ (i : Fin (p.m - 1)) (old : ReferencePrelaunchFollower.State p rate.eta)
        (memory : ActiveFollowerLifecycle.LocalMemory p),
      B[n.val].input.state.followers i = .ordinary old memory →
      i ∈ l.pending → old.lastDown = none →
      source ∈ collectionDownReadySupport (rate := rate) rewards C_star C_h i
        B[n.val].input.time
        (CoordinatorLocalArmChoice.storedDownFlatWord payload i) := by
  classical
  dsimp only
  let s := ReferenceInitializationRun.elapsed p
    (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
  let initial := ReferenceFirstCollectionEpochAlignment.actualLaunchState
    rate source rewards C_star C_h hcross
  have hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h = some initial :=
    Option.eq_some_of_isSome
      ((ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
        rate source rewards C_star C_h).2 hcross)
  have hinitial : initial = ReferenceFirstLaunchNumericalCell.launchState
      rate source rewards C_star C_h hcross :=
    Option.some.inj (hlaunch.symm.trans
      (ReferenceFirstLaunchNumericalCell.correctedLaunch_eq_some_launchState
        rate source rewards C_star C_h hcross))
  let active := (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
    rate source rewards C_star C_h hcross).1
  let E := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
    rate source rewards C_star C_h hcross count hspan
  let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records).length
  let B := ReferenceCollectionPhaseHistory.collectionWindow E.records w
  let W := (E.records.drop (w + 1)).takeWhile
    (fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input)
  have hrecords : E.records =
      (ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun
        rate source rewards C_star C_h hcross s rfl count hspan).records := by
    change (ReferenceActivePhysicalHorizon.run initial source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s count
      hspan active).records = _
    dsimp only [ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun]
    cases hinitial
    rfl
  have hGshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun
        rate source rewards C_star C_h hcross s rfl count hspan).records).length < count := by
    rw [← hrecords]
    exact hshort
  obtain ⟨_r, _q, _base, _, _, _, _dispatched, _hstart, _ledger, _hinit,
      _hledger, _hdomain, _hclock, _hpending, _hnoAssignment, _selected,
      _, _, _, _, _, _, _, _, _, hboundary, _⟩ :=
    ReferenceGeneratedFirstCollectionFollowerPrefix.actual_first_collection_follower_prefix_boundary
      rate source rewards C_star C_h hcross s rfl count hspan hGshort
  have hcount : E.records.length = count :=
    ReferenceActivePhysicalHorizon.run_record_count initial source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s count hspan active
  have hfirstLength : ((E.records.drop w).take 1).length = 1 := by
    have hw : w < count := hshort
    simp only [List.length_take, List.length_drop, hcount]
    omega
  have hBLength : B.length = 1 + W.length := by
    change (((E.records.drop w).take 1) ++ W).length = _
    rw [List.length_append, hfirstLength]
  intro n hn payload l saved hReady i old memory hfi hip hnone
  have hwindow := ReferenceFirstCollectionEpochAlignment.actual_first_collection_window_time
    rate source rewards C_star C_h count hcross hspan hshort n
  have hlookup : E.records[w + n.val]? = some B[n.val] := hwindow.1
  have htime : B[n.val].input.time.val = s + (w + n.val) := by
    have ht : B[n.val].input.time.val + 1 = s + w + 1 + n.val := hwindow.2
    omega
  have hindex : w + n.val < count := by
    have hb := (List.getElem?_eq_some_iff.mp hlookup).1
    simpa only [hcount] using hb
  have hrecordAt : B[n.val] = ReferenceAssignmentPayloadChronology.actualRunRecordAt
      initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
      rewards s (w + n.val) (by omega) active := by
    have hat := ReferenceLocalReleaseGateChronology.run_record_at initial source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s active
      count hspan ⟨w + n.val, hindex⟩
    have hget : E.records[w + n.val]? = some
        (ReferenceAssignmentPayloadChronology.actualRunRecordAt initial source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s
          (w + n.val) (by omega) active) := by
      rw [List.getElem?_eq_getElem (by rw [hcount]; exact hindex)]
      exact congrArg some hat
    exact Option.some.inj (hlookup.symm.trans hget)
  have hj : n.val - 1 ≤ W.length := by
    have hnB : n.val < B.length := n.isLt
    omega
  have hGindex : n.val - 1 ≤
      (((ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun
        rate source rewards C_star C_h hcross s rfl count hspan).records.drop
          ((ReferenceFirstLiveConfirmationHistory.firstLiveWindow
            (ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun
              rate source rewards C_star C_h hcross s rfl count hspan).records).length + 1)).takeWhile
            (fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input)).length := by
    simpa only [← hrecords] using hj
  have hordinary : ∀ j : Fin (p.m - 1), B[n.val].input.state.followers j ≠ .dagger := by
    intro j hdagger
    obtain ⟨post, μ, hpost, _⟩ := (hboundary (n.val - 1) hGindex).2 j
    simp only [← hrecords] at hpost
    have hshift : w + 1 + (n.val - 1) = w + n.val := by omega
    have hpost' : (ReferenceActivePhysicalHorizon.run initial source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s
        (w + n.val) (by omega) active).finalState.followers j = .ordinary post μ := by
      change (ReferenceActivePhysicalHorizon.run
        (ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hcross)
        source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s
        (w + 1 + (n.val - 1)) _ _).finalState.followers j = .ordinary post μ at hpost
      simp only [hshift] at hpost
      cases hinitial
      exact hpost
    have hstate : B[n.val].input.state.followers j = .ordinary post μ := by
      rw [hrecordAt]
      exact hpost'
    rw [hstate] at hdagger
    cases hdagger
  have hsourceRecord : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h B[n.val].input.time source = some B[n.val] := by
    have hstart : ReferenceCompletePhysicalHistory.physicalStart
        rate source rewards C_star C_h = s := rfl
    have hsource := ReferenceSourcePrefixHistoryFiltration.actualRecord_on_launch
      rate rewards C_star C_h B[n.val].input.time source initial hlaunch
      (by rw [hstart, htime]; omega)
    have hsource' : ReferenceSourcePrefixHistoryFiltration.actualRecord
        rate rewards C_star C_h B[n.val].input.time source = some
          (ReferenceAssignmentPayloadChronology.actualRunRecordAt initial source.1.2
            (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s
            (w + n.val) (by omega) active) := by
      simpa only [hstart, htime, Nat.add_sub_cancel_left] using hsource
    exact hsource'.trans (congrArg some hrecordAt.symm)
  exact ⟨B[n.val], hsourceRecord, payload, l, saved, old, memory,
    hReady, hip, hfi, hnone, rfl, hordinary⟩

end Bandits.Support.ReferenceCollectionDownReadySupportMeasurability

end
