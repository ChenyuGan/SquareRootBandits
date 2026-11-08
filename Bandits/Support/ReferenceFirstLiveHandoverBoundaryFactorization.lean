/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveStoppedReleaseSignedCost

/-!
# Raw first-handover boundary events on the original source

This module records the two physical confirmation observations and their
choice-time source sets on the existing complete physical run.  It does not
introduce a stopped trace, a local-information identification, or a service
probability.

Sources: `05_binary_transport.tex:253-275`,
`06_interruptions.tex:246-299,431-490`, and
`appendix_a_local_protocol.tex:100-108,141-157` in the pinned ZIP4 manuscript.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.ContinuousLearningRows
open Bandits.Support.ReferenceFixedTimeSourceControlCoupling
open scoped Classical

namespace Bandits.Support.ReferenceFirstLiveHandoverBoundaryFactorization

variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)

abbrev Source := BootstrapPrivateRoundStreams.SourceInput
abbrev Record := ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)
abbrev Selection (r : Record (p := p) (rate := rate)) :=
  ReferenceActivePhysicalStep.Selection r.input

local notation "μ" => BootstrapPrivateRoundStreams.sourceInputLaw p
local notation "H" => ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0

/-- The actual incoming ordinary state has not yet accepted a DOWN record. -/
def Before (r : Record (p := p) (rate := rate)) (i : Fin (p.m - 1)) : Prop :=
  ∃ state memory,
    r.input.state.followers i = .ordinary state memory ∧ state.lastDown = none

/-- The actual incoming ordinary state has accepted this choice's DOWN word. -/
def After (r : Record (p := p) (rate := rate))
    (selected : Selection (p := p) (rate := rate) r) (i : Fin (p.m - 1)) : Prop :=
  ∃ state memory,
    r.input.state.followers i = .ordinary state memory ∧
      state.lastDown = some (selected.view.payload.downRecord i)

/-- The raw positive follower observation when the incoming DOWN word is not
yet accepted.  This is a physical event, with no live-window or support gate. -/
def V_before (i : Fin (p.m - 1)) (t : Fin p.T) (z : Source p) : Prop :=
  ∃ r : Record (p := p) (rate := rate),
    ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some r ∧
      PublicDiscreteDraws.slotDraw (r.input.row.2 r.input.time).1 = PublicDiscreteDraws.downSlot ∧
      PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
        (r.input.row.2 r.input.time).1 = i ∧
      0 < (r.output.preparation.feedback.observations
        (PublicDiscreteDraws.followerPlayer p.two_le_m i)).val.val

/-- The raw positive coordinator observation on a zero-hash DOWN slot after
the incoming word has been accepted.  Absence and failure tags remain in the
actual record option; this definition supplies no support premise. -/
def V_after (i : Fin (p.m - 1)) (t : Fin p.T) (z : Source p) : Prop :=
  ∃ r : Record (p := p) (rate := rate),
    ∃ selected : Selection (p := p) (rate := rate) r,
      ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some r ∧
      r.output.preparation.coordinator.selection = some selected ∧
      PublicDiscreteDraws.slotDraw (r.input.row.2 r.input.time).1 = PublicDiscreteDraws.downSlot ∧
      PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
        (r.input.row.2 r.input.time).1 = i ∧
      CoordinatorLocalArmChoice.currentDownHash selected.view.payload
        (r.input.row.2 r.input.time) i = 0 ∧
      0 < (r.output.preparation.feedback.observations
        (ActiveRoundActions.coordinator p.two_le_m)).val.val

def crossed (z : Source p) : Prop :=
  (ReferenceCompletePhysicalHistory.generatedBoundary rate z rewards C_star C_h).crossing.isSome = true

def firstWindow (z : Source p) :=
  ReferenceFirstLiveConfirmationHistory.firstLiveWindow
    (ReferenceFirstLiveSourceStoppedReleaseEndpoint.completeRecords
      rate rewards C_star C_h z)

/-- The literal pre-acceptance original-source section. -/
def E_before (q : Fin (M p)) (s : ℕ) (t : Fin p.T)
    (i : Fin (p.m - 1)) : Set (Source p) :=
  {z | ActualInitializationPhysicalStep.selectedRowIndex p z = q ∧ crossed rate rewards C_star C_h z ∧
    ReferenceFirstLiveSourceStoppedReleaseEndpoint.physicalStart rate rewards C_star C_h z = s ∧
    s ≤ t.val ∧
    ∃ r : Record (p := p) (rate := rate),
      ∃ selected : Selection (p := p) (rate := rate) r,
        ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some r ∧
        r ∈ firstWindow rate rewards C_star C_h z ∧
        r.output.preparation.coordinator.selection = some selected ∧
        i ∈ selected.view.pendingAtChoice ∧ Before (p := p) (rate := rate) r i}

/-- The literal accepted-but-unconfirmed original-source section. -/
def E_after (q : Fin (M p)) (s : ℕ) (t : Fin p.T)
    (i : Fin (p.m - 1)) : Set (Source p) :=
  {z | ActualInitializationPhysicalStep.selectedRowIndex p z = q ∧ crossed rate rewards C_star C_h z ∧
    ReferenceFirstLiveSourceStoppedReleaseEndpoint.physicalStart rate rewards C_star C_h z = s ∧
    s ≤ t.val ∧
    ∃ r : Record (p := p) (rate := rate),
      ∃ selected : Selection (p := p) (rate := rate) r,
        ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some r ∧
        r ∈ firstWindow rate rewards C_star C_h z ∧
        r.output.preparation.coordinator.selection = some selected ∧
        i ∈ selected.view.pendingAtChoice ∧ After (p := p) (rate := rate) r selected i}

/-- The actual Borel test used to resample the complete current TimeControl. -/
def B_before (i : Fin (p.m - 1)) (t : Fin p.T) :
    Set (Source p × ContinuousLearningRows.TimeControl p) :=
  {x | V_before rate rewards C_star C_h i t
    (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t x.1 x.2)}

/-- The actual Borel test used to resample the complete current TimeControl. -/
def B_after (i : Fin (p.m - 1)) (t : Fin p.T) :
    Set (Source p × ContinuousLearningRows.TimeControl p) :=
  {x | V_after rate rewards C_star C_h i t
    (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t x.1 x.2)}

private abbrev RoundCode :=
  ReferenceActiveHorizonMeasurability.RoundRecordCode (p := p) (rate := rate)

private theorem actualRecord_sourceFields (t : Fin p.T) (z : Source p)
    (r : Record (p := p) (rate := rate))
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t z = some r) :
    r.input.rows = z.1.2 ∧
      r.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p z ∧
      r.input.time = t ∧ r.input.rewards = rewards := by
  by_cases hz : ReferenceSourcePrefixHistoryFiltration.actualLaunchBy
      rate rewards C_star C_h t.val z
  · have hl := ReferenceLocalReleaseGateChronology.sourceSeed_launch
      rate z rewards C_star C_h hz.1
    have hrec := ReferenceSourcePrefixHistoryFiltration.actualRecord_on_launch
      rate rewards C_star C_h t z _ hl hz.2
    have heq := Option.some.inj (hr.symm.trans hrec)
    subst r
    refine ⟨rfl, rfl, ?_, rfl⟩
    apply Fin.ext
    dsimp only [ReferenceAssignmentPayloadChronology.actualRunRecordAt,
      ReferenceActivePhysicalHorizon.roundInputAt]
    have hs := hz.2
    omega
  · rw [ReferenceSourcePrefixHistoryFiltration.actualRecord_eq_none_of_not_launchBy
      rate rewards C_star C_h t z hz] at hr
    cases hr

private def beforeCodeEvent (i : Fin (p.m - 1)) :
    Set (RoundCode (p := p) (rate := rate) × TimeControl p) :=
  {x | PublicDiscreteDraws.slotDraw x.2.1 = PublicDiscreteDraws.downSlot ∧
    PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K x.2.1 = i ∧
    0 < (ActualInitializationPhysicalStep.observationOfGrid p
      (ReferenceActiveHorizonMeasurability.roundRecordCodeFeedback x.1
        (PublicDiscreteDraws.followerPlayer p.two_le_m i))).val.val}

private theorem measurableSet_beforeCodeEvent (i : Fin (p.m - 1)) :
    MeasurableSet (beforeCodeEvent (p := p) (rate := rate) i) := by
  have hslot : Measurable (fun x : RoundCode (p := p) (rate := rate) × TimeControl p =>
      PublicDiscreteDraws.slotDraw x.2.1) := by
    exact (PublicDiscreteDraws.measurable_slotDraw.comp measurable_fst).comp measurable_snd
  have hdraw : Measurable (fun x : RoundCode (p := p) (rate := rate) × TimeControl p =>
      PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K x.2.1) := by
    exact (PublicDiscreteDraws.measurable_selectedFollowerDraw p.two_le_m p.m_lt_K |>.comp
      measurable_fst).comp measurable_snd
  let player := PublicDiscreteDraws.followerPlayer p.two_le_m i
  have hentry : Measurable (fun code : RoundCode (p := p) (rate := rate) =>
      ReferenceActiveHorizonMeasurability.roundRecordCodeOwnEntry code player) :=
    ReferenceActiveHorizonMeasurability.measurable_roundRecordCodeOwnEntry player
  have hobsCode : Measurable (fun code : RoundCode (p := p) (rate := rate) =>
      (ReferenceActiveHorizonMeasurability.roundRecordCodeOwnEntry code player).2) :=
    measurable_snd.comp hentry
  have hscalar : Measurable (fun obs : ReferencePrelaunchFollower.Observation p =>
      obs.val.val) := by fun_prop
  have hvalue : Measurable (fun x : RoundCode (p := p) (rate := rate) × TimeControl p =>
      (ActualInitializationPhysicalStep.observationOfGrid p
        (ReferenceActiveHorizonMeasurability.roundRecordCodeFeedback x.1 player)).val.val) := by
    exact hscalar.comp (hobsCode.comp measurable_fst)
  exact (hslot (measurableSet_singleton PublicDiscreteDraws.downSlot)).inter
    ((hdraw (measurableSet_singleton i)).inter (hvalue measurableSet_Ioi))

private theorem measurable_optionElim {α β X : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace X]
    (f : α × X → β) (hf : Measurable f) (g : X → β) (hg : Measurable g)
    (v : X → Option α) (hv : Measurable v) :
    Measurable (fun x => match v x with | none => g x | some a => f (a, x)) := by
  have h := (hf.sumElim (hg.comp measurable_snd)).comp
    (MeasurableEquiv.sumProdDistrib α PUnit X).measurable_toFun
  have hpair := h.comp
    (((comap_measurable (Equiv.optionEquivSumPUnit α)).comp hv).prodMk measurable_id)
  convert hpair using 1
  funext x
  change (match v x with | none => g x | some a => f (a, x)) =
    Sum.elim f (g ∘ Prod.snd) ((Equiv.sumProdDistrib α PUnit X)
      ((Equiv.optionEquivSumPUnit α) (v x), x))
  cases v x <;> rfl

private theorem actualRecord_current (t : Fin p.T) (z : Source p)
    (r : Record (p := p) (rate := rate))
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some r) :
    r.input.row.2 r.input.time = ReferenceSourceCurrentControlFreshness.u_t p t z := by
  obtain ⟨hrows, hselected, htime, _⟩ := actualRecord_sourceFields rate rewards C_star C_h t z r hr
  dsimp only [ReferenceActivePhysicalStep.RoundInput.row, ReferenceSourceCurrentControlFreshness.u_t]
  rw [hrows, hselected, htime]

private theorem record_code_observation (r : Record (p := p) (rate := rate)) (player : Fin p.m) :
    r.output.preparation.feedback.observations player =
      ActualInitializationPhysicalStep.observationOfGrid p
        (ReferenceActiveHorizonMeasurability.roundRecordCodeFeedback
          (ReferenceActiveHorizonMeasurability.roundRecordCode r) player) := by
  rw [(ReferenceActiveHorizonMeasurability.roundRecordCode_front r).2.2.2]
  exact r.output.preparation.feedback.observations_eq player

private theorem measurableSet_actualRecordEvent (t : Fin p.T) (V : Source p → Prop)
    (B : Set (RoundCode (p := p) (rate := rate) × TimeControl p)) (hB : MeasurableSet B)
    (hnone : ∀ z, ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t z = none → ¬ V z)
    (hsome : ∀ z r, ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t z = some r →
      (V z ↔ (ReferenceActiveHorizonMeasurability.roundRecordCode r,
        ReferenceSourceCurrentControlFreshness.u_t p t z) ∈ B)) :
    MeasurableSet {z | V z} := by
  let code := ReferenceFirstLiveInspectedFastCollision.actualRecordCode rate rewards C_star C_h t
  have hcode : Measurable code :=
    ReferenceFirstLiveInspectedFastCollision.measurable_actualRecordCode rate rewards C_star C_h t
  have hbranch : Measurable (fun x : RoundCode (p := p) (rate := rate) × Source p =>
      if (x.1, ReferenceSourceCurrentControlFreshness.u_t p t x.2) ∈ B then (1 : ℝ) else 0) :=
    measurable_const.indicator (hB.preimage (measurable_fst.prodMk
      ((ReferenceSourceCurrentControlFreshness.measurable_u_t t).comp measurable_snd)))
  have hm := measurable_optionElim _ hbranch (fun _ => (0 : ℝ)) measurable_const code hcode
  let f := fun z => match code z with
    | none => (0 : ℝ)
    | some c => if (c, ReferenceSourceCurrentControlFreshness.u_t p t z) ∈ B then 1 else 0
  have hf : Measurable f := by
    convert hm using 1
    funext z
    cases hc : code z <;> simp only [f, hc]
  have heq : {z | V z} = f ⁻¹' {1} := by
    ext z
    cases hr : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z with
    | none => simp [f, code, ReferenceFirstLiveInspectedFastCollision.actualRecordCode, hr, hnone z hr]
    | some r => simp [f, code, ReferenceFirstLiveInspectedFastCollision.actualRecordCode, hr, hsome z r hr]
  rw [heq]
  exact hf (measurableSet_singleton 1)

/-- Borel measurability of the literal physical follower observation. -/
theorem measurableSet_V_before (i : Fin (p.m - 1)) (t : Fin p.T) :
    MeasurableSet {z : Source p | V_before rate rewards C_star C_h i t z} := by
  apply measurableSet_actualRecordEvent rate rewards C_star C_h t
    (V_before rate rewards C_star C_h i t) (beforeCodeEvent (rate := rate) i)
    (measurableSet_beforeCodeEvent (rate := rate) i)
  · intro z hr
    simp [V_before, hr]
  · intro z r hr
    have hcontrol := actualRecord_current rate rewards C_star C_h t z r hr
    have hobs := record_code_observation (rate := rate) r
      (PublicDiscreteDraws.followerPlayer p.two_le_m i)
    constructor
    · rintro ⟨r', hr', hs, hd, hp⟩
      have heq : r' = r := Option.some.inj (hr'.symm.trans hr)
      subst r'
      exact ⟨by simpa only [hcontrol] using hs,
        by simpa only [hcontrol] using hd, by simpa only [hobs] using hp⟩
    · rintro ⟨hs, hd, hp⟩
      exact ⟨r, hr, by simpa only [hcontrol] using hs,
        by simpa only [hcontrol] using hd, by simpa only [hobs] using hp⟩

/-- The actual raw test for the before-acceptance branch is Borel. -/
theorem measurableSet_B_before (i : Fin (p.m - 1)) (t : Fin p.T) :
    MeasurableSet (B_before rate rewards C_star C_h i t) := by
  exact (measurableSet_V_before rate rewards C_star C_h i t).preimage
    (ReferenceSourcePhysicalFlagConditionalLaw.measurable_replaceSourceControl p t)

private def payloadTailDiscreteCode (payload : ReferenceActivePhysicalStep.Payload rate) :=
  (payload.n, (payload.sigma, (payload.slowSet.1,
    (payload.queues,
      (AssignmentPayloadDerivedMeasurability.inputExponent payload,
        AssignmentPayloadDerivedMeasurability.inputAuxiliary payload)))))

private theorem measurable_payloadTailDiscreteCode :
    Measurable (payloadTailDiscreteCode (p := p) (rate := rate)) := by
  have hobs : Measurable (LaterAssignmentStartMeasurability.payloadObservation
      (p := p) (eta := rate.eta)) := comap_measurable _
  have hfields := AssignmentPayloadDerivedMeasurability.measurable_inputDerivedFields
    (p := p) (eta := rate.eta)
  have hderived : Measurable (fun payload : ReferenceActivePhysicalStep.Payload rate =>
      (AssignmentPayloadDerivedMeasurability.inputExponent payload,
        AssignmentPayloadDerivedMeasurability.inputAuxiliary payload)) :=
    measurable_snd.comp (measurable_snd.comp hfields)
  change Measurable (fun payload : ReferenceActivePhysicalStep.Payload rate =>
    (payload.n, payload.sigma, payload.slowSet.1, payload.queues,
      AssignmentPayloadDerivedMeasurability.inputExponent payload,
      AssignmentPayloadDerivedMeasurability.inputAuxiliary payload))
  simpa only [LaterAssignmentStartMeasurability.payloadObservation] using
    hobs.fst.prodMk (hobs.snd.fst.prodMk
      (hobs.snd.snd.fst.prodMk (hobs.snd.snd.snd.snd.prodMk hderived)))

private theorem payload_downRecord_eq_of_code_eq
    {payload₁ payload₂ : ReferenceActivePhysicalStep.Payload rate}
    (hcode : payloadTailDiscreteCode (rate := rate) payload₁ =
      payloadTailDiscreteCode (rate := rate) payload₂)
    (i : ActiveRoundActions.Follower p.m) : payload₁.downRecord i = payload₂.downRecord i := by
  simp only [payloadTailDiscreteCode, Prod.mk.injEq] at hcode
  rcases hcode with ⟨_, h⟩
  rcases h with ⟨hsigma, h⟩
  rcases h with ⟨hslow, h⟩
  rcases h with ⟨hqueues, h⟩
  rcases h with ⟨hexponent, haux⟩
  have hslowSet : payload₁.slowSet = payload₂.slowSet := Subtype.ext hslow
  have hassigned : payload₁.assignment.assigned i = payload₂.assignment.assigned i := by
    change CanonicalAssignmentVector.followerArm p.two_le_m payload₁.slowSet i =
      CanonicalAssignmentVector.followerArm p.two_le_m payload₂.slowSet i
    exact congrArg (fun slowSet : CanonicalOrientedSetLaw.SlowSet p.K p.m =>
      CanonicalAssignmentVector.followerArm p.two_le_m slowSet i) hslowSet
  have hauxiliary : payload₁.assignment.auxiliary = payload₂.assignment.auxiliary := by
    simpa [AssignmentPayloadDerivedMeasurability.inputAuxiliary] using haux
  have hfields : (payload₁.downRecord i).val = (payload₂.downRecord i).val := by
    rw [payload₁.downRecord_fields, payload₂.downRecord_fields]
    ext
    · simp [hsigma]
    · simp [hassigned]
    · simp [hauxiliary]
    · rw [hassigned]
      exact congrFun hexponent (payload₂.assignment.assigned i)
    · rw [hassigned]
      exact congrFun hqueues (payload₂.assignment.assigned i)
  exact Subtype.ext hfields

private theorem measurable_of_countable_control
    {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] [Countable β] [MeasurableSingletonClass β]
    (control : α → β) (output : α → γ) (hc : Measurable control)
    (hf : ∀ x y, control x = control y → output x = output y) : Measurable output := by
  classical
  intro s _
  have heq : output ⁻¹' s =
      ⋃ b : {b : β // ∃ x, control x = b ∧ output x ∈ s}, control ⁻¹' {b.val} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_singleton_iff]
    constructor
    · intro hx
      exact ⟨⟨control x, x, rfl, hx⟩, rfl⟩
    · rintro ⟨b, hb⟩
      obtain ⟨y, hy, hys⟩ := b.property
      rw [hf x y (hb.trans hy.symm)]
      exact hys
  rw [heq]
  exact MeasurableSet.iUnion fun b => hc (measurableSet_singleton b.val)

private def followerIndex (i : Fin (p.m - 1)) : ActiveRoundActions.Follower p.m :=
  ⟨i.val, by simp [PublicDiscreteDraws.followerCount]⟩

private theorem measurable_payloadCurrentDownHash (i : Fin (p.m - 1)) :
    Measurable (fun x : ReferenceActivePhysicalStep.Payload rate × TimeControl p =>
      CoordinatorLocalArmChoice.currentDownHash x.1 x.2 i) := by
  apply measurable_of_countable_control
    (fun x : ReferenceActivePhysicalStep.Payload rate × TimeControl p =>
      (payloadTailDiscreteCode (rate := rate) x.1,
        x.2.2 (CoordinatorLocalArmChoice.downChannel i)))
    _ (((measurable_payloadTailDiscreteCode (rate := rate)).comp measurable_fst).prodMk
      ((measurable_pi_apply (CoordinatorLocalArmChoice.downChannel i)).comp
        (measurable_snd.comp measurable_snd)))
  intro x y h
  obtain ⟨hp, hs⟩ := Prod.mk.inj h
  have hw := payload_downRecord_eq_of_code_eq (rate := rate) hp (followerIndex i)
  have hidx : followerIndex i = i := by
    apply Fin.ext
    rfl
  rw [hidx] at hw
  simp only [CoordinatorLocalArmChoice.currentDownHash,
    CoordinatorLocalArmChoice.storedDownFlatWord, AssignmentStartPayload.Input.downWord, hs, hw]

private abbrev SelectionData :=
  ReferenceLiveDispatchOutputMeasurability.SelectionData p rate

private def afterSelectionCode (code : RoundCode (p := p) (rate := rate)) :
    Option (SelectionData (p := p) (rate := rate)) := code.2.2.1.1

private def afterCodeBranch (i : Fin (p.m - 1)) :
    Set (SelectionData (p := p) (rate := rate) ×
      (RoundCode (p := p) (rate := rate) × TimeControl p)) :=
  {x | PublicDiscreteDraws.slotDraw x.2.2.1 = PublicDiscreteDraws.downSlot ∧
    PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K x.2.2.1 = i ∧
    CoordinatorLocalArmChoice.currentDownHash x.1.1.payload x.2.2 i = 0 ∧
    0 < (ActualInitializationPhysicalStep.observationOfGrid p
      (ReferenceActiveHorizonMeasurability.roundRecordCodeFeedback x.2.1
        (ActiveRoundActions.coordinator p.two_le_m))).val.val}

private def afterCodeReadout (i : Fin (p.m - 1))
    (x : RoundCode (p := p) (rate := rate) × TimeControl p) : ℝ :=
  match afterSelectionCode (p := p) (rate := rate) x.1 with
  | none => 0
  | some selected => if (selected, x) ∈ afterCodeBranch (p := p) (rate := rate) i then 1 else 0

private def afterCodeEvent (i : Fin (p.m - 1)) (_t : Fin p.T) :
    Set (RoundCode (p := p) (rate := rate) × TimeControl p) :=
  (afterCodeReadout (p := p) (rate := rate) i) ⁻¹' {1}

private theorem measurableSet_afterCodeBranch (i : Fin (p.m - 1)) :
    MeasurableSet (afterCodeBranch (p := p) (rate := rate) i) := by
  have hslice : Measurable (fun x : SelectionData (p := p) (rate := rate) ×
      (RoundCode (p := p) (rate := rate) × TimeControl p) => x.2.2.1) := by fun_prop
  have hslot : Measurable (fun x : SelectionData (p := p) (rate := rate) ×
      (RoundCode (p := p) (rate := rate) × TimeControl p) =>
        PublicDiscreteDraws.slotDraw x.2.2.1) :=
    PublicDiscreteDraws.measurable_slotDraw.comp hslice
  have hdraw : Measurable (fun x : SelectionData (p := p) (rate := rate) ×
      (RoundCode (p := p) (rate := rate) × TimeControl p) =>
        PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K x.2.2.1) :=
    (PublicDiscreteDraws.measurable_selectedFollowerDraw p.two_le_m p.m_lt_K).comp hslice
  have hviewPayload : Measurable
      (fun view : ReferenceDownReception.ChoiceTimeView p rate.eta => view.payload) := by
    exact measurable_fst.comp (comap_measurable _)
  have hpayload : Measurable (fun x : SelectionData (p := p) (rate := rate) ×
      (RoundCode (p := p) (rate := rate) × TimeControl p) => x.1.1.payload) :=
    hviewPayload.comp (measurable_fst.comp measurable_fst)
  have hcontrol : Measurable (fun x : SelectionData (p := p) (rate := rate) ×
      (RoundCode (p := p) (rate := rate) × TimeControl p) => x.2.2) :=
    measurable_snd.comp measurable_snd
  have hhash := (measurable_payloadCurrentDownHash (p := p) (rate := rate) i).comp
    (hpayload.prodMk hcontrol)
  let coordinator := ActiveRoundActions.coordinator p.two_le_m
  have hentry := ReferenceActiveHorizonMeasurability.measurable_roundRecordCodeOwnEntry
    (p := p) (rate := rate) coordinator
  have hobs : Measurable (fun code : RoundCode (p := p) (rate := rate) =>
      (ReferenceActiveHorizonMeasurability.roundRecordCodeOwnEntry code coordinator).2) :=
    measurable_snd.comp hentry
  have hscalar : Measurable (fun obs : ReferencePrelaunchFollower.Observation p => obs.val.val) := by
    fun_prop
  have hcoordValue : Measurable (fun x : SelectionData (p := p) (rate := rate) ×
      (RoundCode (p := p) (rate := rate) × TimeControl p) =>
        (ActualInitializationPhysicalStep.observationOfGrid p
          (ReferenceActiveHorizonMeasurability.roundRecordCodeFeedback x.2.1 coordinator)).val.val) := by
    exact hscalar.comp (hobs.comp
      (measurable_fst.comp (measurable_snd.comp measurable_id)))
  exact (hslot (measurableSet_singleton PublicDiscreteDraws.downSlot)).inter
    ((hdraw (measurableSet_singleton i)).inter
      ((hhash (measurableSet_singleton 0)).inter (hcoordValue measurableSet_Ioi)))

private theorem measurable_afterCodeReadout (i : Fin (p.m - 1)) :
    Measurable (afterCodeReadout (p := p) (rate := rate) i) := by
  have hbranch : Measurable (fun x : SelectionData (p := p) (rate := rate) ×
      (RoundCode (p := p) (rate := rate) × TimeControl p) =>
        if x ∈ afterCodeBranch (p := p) (rate := rate) i then (1 : ℝ) else 0) :=
    measurable_const.indicator (measurableSet_afterCodeBranch (p := p) (rate := rate) i)
  have hselection : Measurable (fun x : RoundCode (p := p) (rate := rate) × TimeControl p =>
      afterSelectionCode (p := p) (rate := rate) x.1) := by
    have hcode : Measurable (afterSelectionCode (p := p) (rate := rate)) := by
      exact measurable_fst.comp (measurable_fst.comp
        (measurable_snd.comp (measurable_snd.comp measurable_id)))
    exact hcode.comp measurable_fst
  have h := measurable_optionElim
    (f := fun x : SelectionData (p := p) (rate := rate) ×
      (RoundCode (p := p) (rate := rate) × TimeControl p) =>
        if x ∈ afterCodeBranch (p := p) (rate := rate) i then (1 : ℝ) else 0)
    hbranch (fun _ => (0 : ℝ)) measurable_const
    (afterSelectionCode (p := p) (rate := rate) ∘ Prod.fst)
    hselection
  unfold afterCodeReadout
  convert h using 1
  funext x
  cases hselection' : afterSelectionCode (p := p) (rate := rate) x.1 <;>
    simp [hselection', Function.comp_apply]

private theorem measurableSet_afterCodeEvent (i : Fin (p.m - 1)) (t : Fin p.T) :
    MeasurableSet (afterCodeEvent (p := p) (rate := rate) i t) :=
  measurable_afterCodeReadout (p := p) (rate := rate) i (measurableSet_singleton 1)

private theorem record_outputSelection_eq_dispatch
    (r : Record (p := p) (rate := rate)) :
    r.output.preparation.coordinator.selection =
      (ReferenceActivePhysicalStep.dispatch r.input).selection := by
  calc
    r.output.preparation.coordinator.selection =
        (ReferenceActivePhysicalStep.step r.input).preparation.coordinator.selection :=
      congrArg (fun output : ReferenceActivePhysicalStep.RoundOutput r.input =>
        output.preparation.coordinator.selection) r.output_eq
    _ = (ReferenceActivePhysicalStep.prepare r.input).coordinator.selection := rfl
    _ = (ReferenceActivePhysicalStep.dispatch r.input).selection :=
      congrArg (fun cut : ReferenceActivePhysicalStep.DispatchCut r.input => cut.selection)
        (ReferenceActivePhysicalStep.prepare r.input).coordinator_eq

private theorem afterSelectionCode_roundRecord
    (r : Record (p := p) (rate := rate)) :
    afterSelectionCode (p := p) (rate := rate)
        (ReferenceActiveHorizonMeasurability.roundRecordCode r) =
      r.output.preparation.coordinator.selection.map
        ReferenceLiveDispatchOutputMeasurability.encodeSelection := by
  calc
    _ = (ReferenceActivePhysicalStep.dispatch r.input).selection.map
        ReferenceLiveDispatchOutputMeasurability.encodeSelection :=
      ReferenceActiveHorizonMeasurability.roundRecordCode_front r |>.1
    _ = _ := congrArg (fun selected : Option (Selection (p := p) (rate := rate) r) =>
      selected.map ReferenceLiveDispatchOutputMeasurability.encodeSelection)
        (record_outputSelection_eq_dispatch (rate := rate) r).symm

private theorem sparseReward_pos_iff_ne_zero
    (reward : SparseCalendarReplay.SparseCalendarReward) :
    0 < reward ↔ reward ≠ 0 := by
  constructor
  · exact ne_of_gt
  · intro hne
    exact lt_of_le_of_ne reward.property.1 (Ne.symm hne)

/-- Borel measurability retains the actual selected payload and coordinator observation. -/
theorem measurableSet_V_after (i : Fin (p.m - 1)) (t : Fin p.T) :
    MeasurableSet {z : Source p | V_after rate rewards C_star C_h i t z} := by
  apply measurableSet_actualRecordEvent rate rewards C_star C_h t
    (V_after rate rewards C_star C_h i t) (afterCodeEvent (rate := rate) i t)
    (measurableSet_afterCodeEvent (rate := rate) i t)
  · intro z hr
    simp [V_after, hr]
  · intro z r hr
    have hcontrol := actualRecord_current rate rewards C_star C_h t z r hr
    let coordinator := ActiveRoundActions.coordinator p.two_le_m
    have hobsReward := congrArg (fun obs : ReferencePrelaunchFollower.Observation p => obs.val)
      (record_code_observation (rate := rate) r coordinator)
    cases hsel : r.output.preparation.coordinator.selection with
    | none =>
        simp [V_after, hr, hsel, afterCodeEvent, afterCodeReadout,
          afterSelectionCode_roundRecord (rate := rate) r]
    | some selected =>
        simp [afterCodeEvent, afterCodeReadout, V_after, hr, hsel,
          afterSelectionCode_roundRecord (rate := rate) r, afterCodeBranch,
          ReferenceLiveDispatchOutputMeasurability.encodeSelection, hcontrol]
        intro _ _ _
        rw [hobsReward]
        exact sparseReward_pos_iff_ne_zero
          (ActualInitializationPhysicalStep.observationOfGrid p
            (ReferenceActiveHorizonMeasurability.roundRecordCodeFeedback
              (ReferenceActiveHorizonMeasurability.roundRecordCode r) coordinator)).val

/-- The actual raw test for the accepted-word branch is Borel. -/
theorem measurableSet_B_after (i : Fin (p.m - 1)) (t : Fin p.T) :
    MeasurableSet (B_after rate rewards C_star C_h i t) := by
  exact (measurableSet_V_after rate rewards C_star C_h i t).preimage
    (ReferenceSourcePhysicalFlagConditionalLaw.measurable_replaceSourceControl p t)

private def recordReads (r : Record (p := p) (rate := rate)) :=
  (r.input.row.2 r.input.time,
    (r.output.preparation.coordinator.selection.map (fun selected => selected.view),
      r.gridFeedback))

private theorem recordReads_eq_of_temporal_reads
    (r r' : Record (p := p) (rate := rate))
    (hstate : r.input.state = r'.input.state)
    (hselected : r.input.selected = r'.input.selected)
    (htime : r.input.time = r'.input.time)
    (hrewards : r.input.rewards = r'.input.rewards)
    (hcurrent : r.input.row.2 r.input.time = r'.input.row.2 r'.input.time)
    (hpast : ∀ v : Fin p.T, v.val < r.input.time.val →
      (r.input.row.2 v).1 ContinuousControlSlice.Label.prop =
        (r'.input.row.2 v).1 ContinuousControlSlice.Label.prop) :
    recordReads (rate := rate) r = recordReads (rate := rate) r' := by
  have hselection := record_outputSelection_eq_dispatch (rate := rate) r
  have hselection' := record_outputSelection_eq_dispatch (rate := rate) r'
  unfold recordReads
  rw [hselection, hselection']
  rcases r with ⟨x, output, hout⟩
  rcases r' with ⟨y, output', hout'⟩
  subst output
  subst output'
  rcases x with ⟨state, rows, selected, time, active, rewards⟩
  rcases y with ⟨state', rows', selected', time', active', rewards'⟩
  dsimp only at hstate hselected htime hrewards hcurrent hpast
  subst state'
  subst selected'
  subst time'
  subst rewards'
  change (rows selected).2 time = (rows' selected).2 time at hcurrent
  have hevidence := ReferenceActiveTemporalAssembly.computedEvidence_eq_of_temporal_reads
    state rows rows' selected time active rewards rewards hcurrent hpast rfl
  have hgrid := congrArg ReferenceActivePhysicalHorizon.RoundEvidence.gridFeedback hevidence
  have hview : (ReferenceActivePhysicalStep.dispatch
        ⟨state, rows, selected, time, active, rewards⟩).downView =
      (ReferenceActivePhysicalStep.dispatch
        ⟨state, rows', selected, time, active, rewards⟩).downView := by
    cases hphase : state.coordinator with
    | first =>
        exact congrArg Prod.snd
          (ReferenceActiveTemporalCausality.first_dispatch_projections_eq_of_current
            state rows rows' selected active rewards rewards hphase hcurrent)
    | live registers owned base =>
        exact congrArg (fun data => data.2.1)
          (ReferenceActiveDispatchTemporal.live_dispatch_data_eq_of_current
            state rows rows' selected time active rewards rewards
            registers owned base hphase hcurrent)
    | collection payload ledger proposal =>
        exact congrArg (fun data => data.2.1)
          (ReferenceActiveDispatchTemporal.collection_dispatch_data_eq_of_current
            state rows rows' selected time active rewards rewards
            payload ledger proposal hphase hcurrent)
    | dagger =>
        rw [ReferenceActivePhysicalStep.dispatch_dagger _ hphase,
          ReferenceActivePhysicalStep.dispatch_dagger _ hphase]
        rfl
  exact Prod.ext hcurrent (Prod.ext hview hgrid)

private theorem actualRecord_reads_prefix (t : Fin p.T) (z : Source p) :
    (ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z).map
        (recordReads (rate := rate)) =
      (ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 (t.val + 1) z)).map
          (recordReads (rate := rate)) := by
  let z' := ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 (t.val + 1) z
  have hprefixEq : ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z' =
      ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z :=
    ReferenceSourcePrefixHistoryFiltration.sourcePrefix_sourcePrefix
      control0 t.val (t.val + 1) (by omega) z
  have hin : ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t z =
      ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t z' := by
    rw [ReferenceSourcePrefixHistoryFiltration.incoming_factor
      rate rewards C_star C_h control0 t z,
      ReferenceSourcePrefixHistoryFiltration.incoming_factor
      rate rewards C_star C_h control0 t z', hprefixEq]
  unfold ReferenceSourcePrefixHistoryFiltration.incoming at hin
  cases hr : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z <;>
    cases hr' : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z' <;>
    simp only [hr, hr', Option.map_none, Option.map_some] at hin ⊢
  · contradiction
  · contradiction
  rename_i r r'
  have hstate := ReferenceActivePhysicalStepMeasurability.encodeState_injective
    (Option.some.inj hin)
  obtain ⟨hrows, hselected, htime, hrewards⟩ :=
    actualRecord_sourceFields rate rewards C_star C_h t z r hr
  obtain ⟨hrows', hselected', htime', hrewards'⟩ :=
    actualRecord_sourceFields rate rewards C_star C_h t z' r' hr'
  have hselectedEq : r.input.selected = r'.input.selected := by
    rw [hselected, hselected', ReferenceSourcePrefixHistoryFiltration.sourcePrefix_selected]
  have hcurrent : r.input.row.2 r.input.time = r'.input.row.2 r'.input.time := by
    change (r.input.rows r.input.selected).2 r.input.time =
      (r'.input.rows r'.input.selected).2 r'.input.time
    rw [hrows, hselected, htime, hrows', hselected', htime',
      ReferenceSourcePrefixHistoryFiltration.sourcePrefix_selected,
      ReferenceSourcePrefixHistoryFiltration.sourcePrefix_control]
    simp
  have hpast : ∀ v : Fin p.T, v.val < r.input.time.val →
      (r.input.row.2 v).1 ContinuousControlSlice.Label.prop =
        (r'.input.row.2 v).1 ContinuousControlSlice.Label.prop := by
    intro v hv
    have hv' : v.val < t.val := by simpa [htime] using hv
    dsimp only [ReferenceActivePhysicalStep.RoundInput.row]
    rw [hrows, hselected, hrows', hselected',
      ReferenceSourcePrefixHistoryFiltration.sourcePrefix_selected,
      ReferenceSourcePrefixHistoryFiltration.sourcePrefix_control]
    simp [show v.val < t.val + 1 by omega]
  exact congrArg some (recordReads_eq_of_temporal_reads (rate := rate) r r'
    hstate hselectedEq (htime.trans htime'.symm) (hrewards.trans hrewards'.symm)
    hcurrent hpast)

private theorem V_before_reads (i : Fin (p.m - 1)) (t : Fin p.T) (z : Source p) :
    V_before rate rewards C_star C_h i t z ↔
      ∃ reads ∈ (ReferenceSourcePrefixHistoryFiltration.actualRecord
        rate rewards C_star C_h t z).map (recordReads (rate := rate)),
        PublicDiscreteDraws.slotDraw reads.1.1 = PublicDiscreteDraws.downSlot ∧
        PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K reads.1.1 = i ∧
        0 < (ActualInitializationPhysicalStep.observationOfGrid p
          (reads.2.2 (PublicDiscreteDraws.followerPlayer p.two_le_m i))).val.val := by
  constructor
  · rintro ⟨r, hr, hs, hi, ho⟩
    refine ⟨recordReads (rate := rate) r, by simp [hr], hs, hi, ?_⟩
    rw [r.output.preparation.feedback.observations_eq] at ho
    exact ho
  · rintro ⟨reads, hreads, hs, hi, ho⟩
    cases hr : ReferenceSourcePrefixHistoryFiltration.actualRecord
        rate rewards C_star C_h t z with
    | none => simp [hr] at hreads
    | some r =>
        have heq : recordReads (rate := rate) r = reads := by simpa [hr] using hreads
        subst reads
        refine ⟨r, hr, hs, hi, ?_⟩
        rw [r.output.preparation.feedback.observations_eq]
        exact ho

private theorem V_after_reads (i : Fin (p.m - 1)) (t : Fin p.T) (z : Source p) :
    V_after rate rewards C_star C_h i t z ↔
      ∃ reads ∈ (ReferenceSourcePrefixHistoryFiltration.actualRecord
        rate rewards C_star C_h t z).map (recordReads (rate := rate)),
        ∃ view ∈ reads.2.1,
          PublicDiscreteDraws.slotDraw reads.1.1 = PublicDiscreteDraws.downSlot ∧
          PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K reads.1.1 = i ∧
          CoordinatorLocalArmChoice.currentDownHash view.payload reads.1 i = 0 ∧
          0 < (ActualInitializationPhysicalStep.observationOfGrid p
            (reads.2.2 (ActiveRoundActions.coordinator p.two_le_m))).val.val := by
  constructor
  · rintro ⟨r, selected, hr, hsel, hs, hi, hh, ho⟩
    refine ⟨recordReads (rate := rate) r, by simp [hr], selected.view,
      by simp [recordReads, hsel], hs, hi, hh, ?_⟩
    rw [r.output.preparation.feedback.observations_eq] at ho
    exact ho
  · rintro ⟨reads, hreads, view, hview, hs, hi, hh, ho⟩
    cases hr : ReferenceSourcePrefixHistoryFiltration.actualRecord
        rate rewards C_star C_h t z with
    | none => simp [hr] at hreads
    | some r =>
        have heq : recordReads (rate := rate) r = reads := by simpa [hr] using hreads
        subst reads
        cases hsel : r.output.preparation.coordinator.selection with
        | none => simp [recordReads, hsel] at hview
        | some selected =>
            have heq : selected.view = view := by simpa [recordReads, hsel] using hview
            subst view
            refine ⟨r, selected, hr, hsel, hs, hi, hh, ?_⟩
            rw [r.output.preparation.feedback.observations_eq]
            exact ho

/-- Actual future-prefix invariance, using only incoming state, current
control, past proposal scalars, the selected view and physical feedback. -/
theorem V_before_sourcePrefix_successor (i : Fin (p.m - 1)) (t : Fin p.T)
    (z : Source p) :
    V_before rate rewards C_star C_h i t z =
      V_before rate rewards C_star C_h i t
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 (t.val + 1) z) := by
  apply propext
  rw [V_before_reads, V_before_reads,
    actualRecord_reads_prefix rate rewards C_star C_h control0 t z]

theorem V_after_sourcePrefix_successor (i : Fin (p.m - 1)) (t : Fin p.T)
    (z : Source p) :
    V_after rate rewards C_star C_h i t z =
      V_after rate rewards C_star C_h i t
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 (t.val + 1) z) := by
  apply propext
  rw [V_after_reads, V_after_reads,
    actualRecord_reads_prefix rate rewards C_star C_h control0 t z]

private theorem raw_roundEnd (V : Source p → Prop) (t : Fin p.T)
    (hV : MeasurableSet {z | V z})
    (hfactor : ∀ z, V z = V
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 (t.val + 1) z)) :
    StronglyMeasurable[H (t.val + 2)] (fun z => if V z then (1 : ℝ) else 0) := by
  rw [show t.val + 2 = (t.val + 1) + 1 by omega,
    ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration_succ]
  have hm : Measurable (fun z => if V z then (1 : ℝ) else 0) :=
    measurable_const.indicator hV
  have hf := hm.comp (comap_measurable
    (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 (t.val + 1)))
  convert hf.stronglyMeasurable using 1
  funext z
  exact congrArg (fun b : Prop => if b then (1 : ℝ) else 0) (hfactor z)

/-- The raw pre-acceptance zero/one observation is strongly measurable at
the end of its actual physical round. -/
theorem V_before_roundEnd_stronglyMeasurable (i : Fin (p.m - 1)) (t : Fin p.T) :
    StronglyMeasurable[H (t.val + 2)]
      (fun z : Source p => if V_before rate rewards C_star C_h i t z then (1 : ℝ) else 0) := by
  exact raw_roundEnd control0 _ t (measurableSet_V_before rate rewards C_star C_h i t)
    (V_before_sourcePrefix_successor rate rewards C_star C_h control0 i t)

/-- Restoring the original current whole control to the strict prefix gives
the original source through the end of this physical round. -/
theorem before_current_restoration (t : Fin p.T) (z : Source p) :
    ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z)
        (ReferenceSourceCurrentControlFreshness.u_t p t z) =
      ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 (t.val + 1) z := by
  rw [← ReferenceSourcePhysicalFlagConditionalLaw.c_t_eq_sourcePrefix control0 t z]
  exact (ReferenceSourcePrefixHistoryFiltration.prefix_successor_restore control0 t z).symm

/-- The admitted whole-control integration theorem specialized to the actual
pre-acceptance replacement test. -/
theorem before_control_test_condExp (i : Fin (p.m - 1)) (t : Fin p.T) :
    μ[ReferenceSourceCurrentControlFreshness.sourceControlTest p control0 t
        (B_before rate rewards C_star C_h i t) |
      ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0
        (t.val + 1)] =ᵐ[μ] fun source =>
      ∫ control, (B_before rate rewards C_star C_h i t).indicator
        (fun _ => (1 : ℝ))
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val source, control)
        ∂ContinuousLearningRows.timeControlLaw p := by
  simpa only [ReferenceSourcePhysicalFlagConditionalLaw.sourcePrefixField_eq_m_t
      control0 t, ReferenceSourcePhysicalFlagConditionalLaw.c_t_eq_sourcePrefix
      control0 t] using
    ReferenceSourceCurrentControlFreshness.source_control_test_condExp
      control0 t (B_before rate rewards C_star C_h i t)
      (measurableSet_B_before rate rewards C_star C_h i t)

private theorem raw_event_condExp (V : Source p → Prop) (t : Fin p.T)
    (hB : MeasurableSet {x : Source p × TimeControl p |
      V (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t x.1 x.2)})
    (hfactor : ∀ z, V z = V
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 (t.val + 1) z)) :
    μ[(fun z => if V z then (1 : ℝ) else 0) | H (t.val + 1)] =ᵐ[μ]
      fun z => ∫ u, (if V (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z) u)
        then (1 : ℝ) else 0) ∂timeControlLaw p := by
  let B := {x : Source p × TimeControl p |
    V (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t x.1 x.2)}
  have htest := ReferenceSourceCurrentControlFreshness.source_control_test_condExp control0 t B hB
  have heq : ReferenceSourceCurrentControlFreshness.sourceControlTest p control0 t B =
      fun z => if V z then (1 : ℝ) else 0 := by
    funext z
    rw [ReferenceSourceCurrentControlFreshness.sourceControlTest,
      ReferenceSourcePhysicalFlagConditionalLaw.c_t_eq_sourcePrefix]
    change (if V (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z)
      (ReferenceSourceCurrentControlFreshness.u_t p t z)) then (1 : ℝ) else 0) = _
    rw [before_current_restoration, ← hfactor z]
  rw [heq] at htest
  simpa only [ReferenceSourcePhysicalFlagConditionalLaw.sourcePrefixField_eq_m_t control0 t,
    ReferenceSourcePhysicalFlagConditionalLaw.c_t_eq_sourcePrefix control0 t,
    B, Set.indicator_apply, Set.mem_ofPred_eq] using htest

/-- Conditional expectation of the raw pre-acceptance physical event over the
complete original current-control law. The event-to-test equality uses both
the actual prefix-restoration identity and the temporal-read factorization. -/
theorem V_before_condExp (i : Fin (p.m - 1)) (t : Fin p.T) :
    μ[(fun source => if V_before rate rewards C_star C_h i t source then (1 : ℝ) else 0) |
      H (t.val + 1)] =ᵐ[μ] fun source =>
      ∫ control, (if V_before rate rewards C_star C_h i t
          (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
            (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val source)
            control)
        then (1 : ℝ) else 0) ∂ContinuousLearningRows.timeControlLaw p := by
  exact raw_event_condExp control0 (V_before rate rewards C_star C_h i t) t
    (measurableSet_B_before rate rewards C_star C_h i t)
    (V_before_sourcePrefix_successor rate rewards C_star C_h control0 i t)

/-- The raw accepted-word zero/one observation is strongly measurable at
the end of its actual physical round. -/
theorem V_after_roundEnd_stronglyMeasurable (i : Fin (p.m - 1)) (t : Fin p.T) :
    StronglyMeasurable[H (t.val + 2)]
      (fun z : Source p => if V_after rate rewards C_star C_h i t z then (1 : ℝ) else 0) := by
  exact raw_roundEnd control0 _ t (measurableSet_V_after rate rewards C_star C_h i t)
    (V_after_sourcePrefix_successor rate rewards C_star C_h control0 i t)

/-- The admitted whole-control integration theorem specialized to the actual
accepted-word replacement test. -/
theorem after_control_test_condExp (i : Fin (p.m - 1)) (t : Fin p.T) :
    μ[ReferenceSourceCurrentControlFreshness.sourceControlTest p control0 t
        (B_after rate rewards C_star C_h i t) |
      ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0
        (t.val + 1)] =ᵐ[μ] fun source =>
      ∫ control, (B_after rate rewards C_star C_h i t).indicator
        (fun _ => (1 : ℝ))
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val source, control)
        ∂ContinuousLearningRows.timeControlLaw p := by
  simpa only [ReferenceSourcePhysicalFlagConditionalLaw.sourcePrefixField_eq_m_t
      control0 t, ReferenceSourcePhysicalFlagConditionalLaw.c_t_eq_sourcePrefix
      control0 t] using
    ReferenceSourceCurrentControlFreshness.source_control_test_condExp
      control0 t (B_after rate rewards C_star C_h i t)
      (measurableSet_B_after rate rewards C_star C_h i t)

/-- Conditional expectation of the raw accepted-word physical event over the
complete original current-control law. The event-to-test equality uses both
the actual prefix-restoration identity and the temporal-read factorization. -/
theorem V_after_condExp (i : Fin (p.m - 1)) (t : Fin p.T) :
    μ[(fun source => if V_after rate rewards C_star C_h i t source then (1 : ℝ) else 0) |
      H (t.val + 1)] =ᵐ[μ] fun source =>
      ∫ control, (if V_after rate rewards C_star C_h i t
          (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
            (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val source)
            control)
        then (1 : ℝ) else 0) ∂ContinuousLearningRows.timeControlLaw p := by
  exact raw_event_condExp control0 (V_after rate rewards C_star C_h i t) t
    (measurableSet_B_after rate rewards C_star C_h i t)
    (V_after_sourcePrefix_successor rate rewards C_star C_h control0 i t)

private def incomingFollowerCode (i : Fin (p.m - 1))
    (code : ReferenceActivePhysicalStepMeasurability.StateCode p rate) :
    Option (FollowerDownMeasurability.FollowerStateCode p rate) :=
  (code.2.2.2 i).map (fun data => data.1.1.1)

private theorem measurable_incomingFollowerCode (i : Fin (p.m - 1)) :
    Measurable (incomingFollowerCode (rate := rate) i) := by
  have hf : Measurable (fun code : ReferenceActivePhysicalStepMeasurability.StateCode p rate =>
      code.2.2.2 i) :=
    (measurable_pi_apply i).comp
      (measurable_snd.comp (measurable_snd.comp measurable_snd))
  have hindex : Measurable (fun data :
      FollowerObservationStageMeasurabilityRepair.CarriedState p rate => data.1.1) := by
    intro u _
    change MeasurableSet[(⨅ index : FollowerObservationStageMeasurabilityRepair.FollowerCarryIndex p rate,
      (inferInstance : MeasurableSpace
      (FollowerDownMeasurability.SavedScalarFamily index.2.1)).map
        (Sigma.mk index))] {data | data.1.1 ∈ u}
    rw [MeasurableSpace.measurableSet_iInf]
    intro index
    rw [MeasurableSpace.map_def]
    by_cases hmem : index.1 ∈ u <;> simp [hmem]
  have hm : Measurable (fun data :
      FollowerObservationStageMeasurabilityRepair.CarriedState p rate ×
        FollowerPrepareJointMeasurability.LocalMemoryCode p =>
      some data.1.1.1) :=
    (measurable_of_countable (fun c : FollowerDownMeasurability.FollowerStateCode p rate =>
      some c)).comp (hindex.comp measurable_fst)
  have hnone : Measurable (fun _ : Unit =>
      (none : Option (FollowerDownMeasurability.FollowerStateCode p rate))) := measurable_const
  have h := (hnone.sumElim hm).comp
    ((FollowerPrepareJointMeasurability.measurable_incomingConfigurationToSum rate).comp hf)
  convert h using 1
  funext code
  dsimp only [incomingFollowerCode, Function.comp_def]
  cases code.2.2.2 i <;> rfl

private def stageCode (after : Bool) (i : Fin (p.m - 1))
    (x : SelectionData (p := p) (rate := rate) × RoundCode (p := p) (rate := rate)) : Bool :=
  decide (i ∈ x.1.1.pendingAtChoice ∧
    ∃ f ∈ incomingFollowerCode (rate := rate) i x.2.2.1,
      f.lastDown = if after then some (x.1.1.payload.downRecord i) else none)

private theorem measurable_stageCode (after : Bool) (i : Fin (p.m - 1)) :
    Measurable (stageCode (rate := rate) after i) := by
  have hview : Measurable (fun x : SelectionData (p := p) (rate := rate) ×
      RoundCode (p := p) (rate := rate) =>
      ReferenceDownReceptionMeasurability.choiceTimeViewObservation x.1.1) :=
    (comap_measurable _).comp (measurable_fst.comp measurable_fst)
  have hpend := measurable_fst.comp (measurable_snd.comp hview)
  have hf : Measurable (fun x : SelectionData (p := p) (rate := rate) ×
      RoundCode (p := p) (rate := rate) => incomingFollowerCode (rate := rate) i x.2.2.1) :=
    (measurable_incomingFollowerCode (rate := rate) i).comp
      (measurable_fst.comp (measurable_snd.comp measurable_snd))
  have hp := (measurable_payloadTailDiscreteCode (rate := rate)).comp
    (measurable_fst.comp hview)
  apply measurable_of_countable_control
    (fun x => (x.1.1.pendingAtChoice,
      incomingFollowerCode (rate := rate) i x.2.2.1,
      payloadTailDiscreteCode (rate := rate) x.1.1.payload)) _
    (hpend.prodMk (hf.prodMk hp))
  intro x y h
  obtain ⟨hpend, hrest⟩ := Prod.mk.inj h
  obtain ⟨hf, hp⟩ := Prod.mk.inj hrest
  have hrecord := payload_downRecord_eq_of_code_eq (rate := rate) hp (followerIndex i)
  have hi : followerIndex i = i := Fin.ext rfl
  rw [hi] at hrecord
  simp only [stageCode, hpend, hf, hrecord]

private def choiceStageCode (after : Bool) (i : Fin (p.m - 1))
    (code : RoundCode (p := p) (rate := rate)) : Bool :=
  match afterSelectionCode (rate := rate) code with
  | none => false
  | some selected => stageCode (rate := rate) after i (selected, code)

private theorem measurable_choiceStageCode (after : Bool) (i : Fin (p.m - 1)) :
    Measurable (choiceStageCode (rate := rate) after i) := by
  have h := measurable_optionElim (stageCode (rate := rate) after i)
    (measurable_stageCode (rate := rate) after i) (fun _ => false) measurable_const
    (afterSelectionCode (rate := rate)) (measurable_fst.comp (measurable_fst.comp
      (measurable_snd.comp (measurable_snd.comp measurable_id))))
  convert h using 1
  funext code
  cases hselection : afterSelectionCode (rate := rate) code <;>
    simp only [choiceStageCode, hselection]

private theorem choiceStageCode_record (after : Bool) (i : Fin (p.m - 1))
    (r : Record (p := p) (rate := rate)) :
    choiceStageCode (rate := rate) after i
        (ReferenceActiveHorizonMeasurability.roundRecordCode r) = true ↔
      ∃ selected, r.output.preparation.coordinator.selection = some selected ∧
        i ∈ selected.view.pendingAtChoice ∧
        (if after then After (rate := rate) r selected i else Before (rate := rate) r i) := by
  unfold choiceStageCode
  rw [afterSelectionCode_roundRecord]
  cases hs : r.output.preparation.coordinator.selection with
  | none => simp
  | some selected =>
      simp only [Option.map_some, stageCode, decide_eq_true_eq,
        ReferenceLiveDispatchOutputMeasurability.encodeSelection]
      cases hf : r.input.state.followers i <;>
        cases after <;>
        simp [Before, After, incomingFollowerCode,
          ReferenceActiveHorizonMeasurability.roundRecordCode,
          ReferenceActivePhysicalStepMeasurability.encodeState,
          FollowerPrepareJointMeasurability.incomingOfLocalConfiguration,
          FollowerObservationStageMeasurabilityRepair.carriedStateOfState,
          FollowerDownMeasurability.followerStateCode, hf]

private theorem actualRecord_of_member (t : Fin p.T) (z : Source p)
    (r : Record (p := p) (rate := rate))
    (hr : r ∈ ReferenceFirstLiveSourceStoppedReleaseEndpoint.completeRecords
      rate rewards C_star C_h z) (ht : r.input.time = t) :
    ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some r := by
  obtain ⟨k, hk, heq⟩ := List.mem_iff_getElem.mp hr
  change r ∈ ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h at hr
  change k < (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).length at hk
  change (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k] = r at heq
  have htimes := ReferenceCompletePhysicalHistory.completeSuffixRecords_time_values
    rate z rewards C_star C_h
  have htime := congrArg (fun ts : List ℕ => ts[k]?) htimes
  rw [List.getElem?_map, List.getElem?_eq_getElem hk, Option.map_some] at htime
  rw [heq, ht] at htime
  have hk' : k < p.T - ReferenceCompletePhysicalHistory.physicalStart
      rate z rewards C_star C_h := by
    simpa only [ReferenceFirstLiveSourceStoppedReleaseEndpoint.completeRecords,
      ReferenceCompletePhysicalHistory.completeSuffixRecords_length] using hk
  have hdate : t.val = ReferenceCompletePhysicalHistory.physicalStart
      rate z rewards C_star C_h + k := by
    simpa [ReferenceActivePhysicalHorizon.calendar, List.getElem?_range', hk'] using htime
  unfold ReferenceSourcePrefixHistoryFiltration.actualRecord
  rw [ite_eq_left (by omega), show t.val - ReferenceCompletePhysicalHistory.physicalStart
    rate z rewards C_star C_h = k by omega, List.getElem?_eq_getElem hk, heq]

private def sectionCodeEvent (after : Bool) (t : Fin p.T) (i : Fin (p.m - 1)) :
    Set (Source p) :=
  {z | ∃ code ∈ (firstWindow rate rewards C_star C_h z).map
      ReferenceActiveHorizonMeasurability.roundRecordCode,
    code.1 = t.val ∧ choiceStageCode (rate := rate) after i code = true}

private theorem measurableSet_sectionCodeEvent (after : Bool) (t : Fin p.T)
    (i : Fin (p.m - 1)) :
    MeasurableSet (sectionCodeEvent rate rewards C_star C_h after t i) := by
  let codes := fun z => (firstWindow rate rewards C_star C_h z).map
    ReferenceActiveHorizonMeasurability.roundRecordCode
  have hc : Measurable codes :=
    ReferenceFirstLiveOverflowReadout.measurable_wholeFirstLiveWindowCensus
      rate rewards C_star C_h
  have htest : Measurable (fun code : RoundCode (p := p) (rate := rate) =>
      decide (code.1 = t.val ∧ choiceStageCode (rate := rate) after i code = true)) :=
    (measurable_of_countable (fun x : ℕ × Bool => decide (x.1 = t.val ∧ x.2 = true))).comp
      (measurable_fst.prodMk (measurable_choiceStageCode (rate := rate) after i))
  have hj (j : ℕ) : Measurable (fun z =>
      (ReferenceActiveHorizonMeasurability.listObservationAt (codes z) j).elim
        (fun _ => false) (fun code => decide
          (code.1 = t.val ∧ choiceStageCode (rate := rate) after i code = true))) :=
    (measurable_const.sumElim htest).comp ((measurable_pi_apply j).comp
      (measurable_snd.comp
        (ReferenceActiveHorizonMeasurability.measurable_listObservationCoordinates.comp hc)))
  have heq : sectionCodeEvent rate rewards C_star C_h after t i =
      ⋃ j : ℕ, {z | (ReferenceActiveHorizonMeasurability.listObservationAt (codes z) j).elim
        (fun _ => false) (fun code => decide
          (code.1 = t.val ∧ choiceStageCode (rate := rate) after i code = true)) = true} := by
    ext z
    simp only [sectionCodeEvent, Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨code, hcode, ht, hs⟩
      obtain ⟨j, hj, heq⟩ := List.mem_iff_getElem.mp hcode
      exact ⟨j, by simp [ReferenceActiveHorizonMeasurability.listObservationAt,
        List.getElem?_eq_getElem hj, heq, ht, hs, codes]⟩
    · rintro ⟨j, hj⟩
      cases heq : (codes z)[j]? with
      | none => simp [ReferenceActiveHorizonMeasurability.listObservationAt, heq] at hj
      | some code =>
          have hp : code.1 = t.val ∧ choiceStageCode (rate := rate) after i code = true := by
            simpa [ReferenceActiveHorizonMeasurability.listObservationAt, heq] using hj
          exact ⟨code, List.mem_of_getElem? heq, hp⟩
  rw [heq]
  exact MeasurableSet.iUnion fun j => hj j (measurableSet_singleton true)

private theorem sectionCodeEvent_iff (after : Bool) (t : Fin p.T)
    (i : Fin (p.m - 1)) (z : Source p) :
      z ∈ sectionCodeEvent rate rewards C_star C_h after t i ↔
    ∃ r : Record (p := p) (rate := rate), ∃ selected : Selection (rate := rate) r,
      ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some r ∧
      r ∈ firstWindow rate rewards C_star C_h z ∧
      r.output.preparation.coordinator.selection = some selected ∧
      i ∈ selected.view.pendingAtChoice ∧
      (if after then After (rate := rate) r selected i else Before (rate := rate) r i) := by
  constructor
  · rintro ⟨code, hc, ht, hstage⟩
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hc
    obtain ⟨selected, hsel, hi, hb⟩ := (choiceStageCode_record (rate := rate) after i r).mp hstage
    have ht' : r.input.time = t := Fin.ext ht
    exact ⟨r, selected, actualRecord_of_member rate rewards C_star C_h t z r
      ((List.takeWhile_prefix _).subset hr) ht', hr, hsel, hi, hb⟩
  · rintro ⟨r, selected, hr, hW, hsel, hi, hb⟩
    refine ⟨ReferenceActiveHorizonMeasurability.roundRecordCode r,
      List.mem_map.mpr ⟨r, hW, rfl⟩, ?_, (choiceStageCode_record (rate := rate) after i r).mpr
        ⟨selected, hsel, hi, hb⟩⟩
    exact congrArg Fin.val (actualRecord_sourceFields rate rewards C_star C_h t z r hr).2.2.1

private theorem E_eq_code (after : Bool) (q : Fin (M p)) (s : ℕ) (t : Fin p.T)
    (hs : s ≤ t.val) (i : Fin (p.m - 1)) :
    (if after then E_after rate rewards C_star C_h q s t i
      else E_before rate rewards C_star C_h q s t i) =
      ReferenceTotalSourcePairCoupling.sourceStratumEvent rate rewards C_star C_h t
        (ReferenceFirstLiveRecordingSourceCylinder.stratumIndex q t s hs) ∩
      sectionCodeEvent rate rewards C_star C_h after t i := by
  ext z
  have hsource : z ∈ ReferenceTotalSourcePairCoupling.sourceStratumEvent
      rate rewards C_star C_h t
      (ReferenceFirstLiveRecordingSourceCylinder.stratumIndex q t s hs) ↔
      ActualInitializationPhysicalStep.selectedRowIndex p z = q ∧
        crossed rate rewards C_star C_h z ∧
        ReferenceFirstLiveSourceStoppedReleaseEndpoint.physicalStart
          rate rewards C_star C_h z = s := by
    rw [← ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex]
    rfl
  rw [Set.mem_inter_iff, hsource]
  have hcode := sectionCodeEvent_iff rate rewards C_star C_h after t i z
  cases after <;> simp only [Bool.false_eq_true, ite_false, ite_true]
      at hcode ⊢
  all_goals
    rw [hcode]
    simp only [E_before, E_after, Set.mem_ofPred_eq, hs, true_and]
    constructor
    · rintro ⟨hq, hc, hstart, r, selected, hr, hW, hsel, hi, hb⟩
      exact ⟨⟨hq, hc, hstart⟩, r, selected, hr, hW, hsel, hi, hb⟩
    · rintro ⟨⟨hq, hc, hstart⟩, r, selected, hr, hW, hsel, hi, hb⟩
      exact ⟨hq, hc, hstart, r, selected, hr, hW, hsel, hi, hb⟩

private theorem choiceStage_control (after : Bool) (i : Fin (p.m - 1))
    (r : Record (p := p) (rate := rate))
    (hphase : ReferenceFirstLiveConfirmationHistory.FirstLiveState r.input.state)
    (hno : ReferenceCollectionPhaseHistory.cutoffChosen r.input = false)
    (hstage : choiceStageCode (rate := rate) after i
      (ReferenceActiveHorizonMeasurability.roundRecordCode r) = true)
    (u : TimeControl p) :
    let r_u := ReferencePhysicalReleaseObservability.recordOfInput
      (ReferenceContinuingLiveSlicePreparation.inputAtControl r.input u)
    ReferenceCollectionPhaseHistory.cutoffChosen r_u.input = false ∧
      choiceStageCode (rate := rate) after i
        (ReferenceActiveHorizonMeasurability.roundRecordCode r_u) = true := by
  intro r_u
  obtain ⟨selected, hsel, hi, hb⟩ := (choiceStageCode_record (rate := rate) after i r).mp hstage
  have hsel' : (ReferenceActivePhysicalStep.prepare r.input).coordinator.selection = some selected := by
    rw [record_outputSelection_eq_dispatch] at hsel
    exact hsel
  let x := ReferenceContinuingLiveSlicePreparation.inputAtControl r.input u
  have hstage_u (selected_u : ReferenceActivePhysicalStep.Selection x)
      (hsel_u : (ReferenceActivePhysicalStep.prepare x).coordinator.selection = some selected_u)
      (hi_u : i ∈ selected_u.view.pendingAtChoice)
      (hb_u : if after then After (rate := rate) r_u selected_u i else Before (rate := rate) r_u i) :
      choiceStageCode (rate := rate) after i
        (ReferenceActiveHorizonMeasurability.roundRecordCode r_u) = true := by
    apply (choiceStageCode_record (rate := rate) after i r_u).mpr
    exact ⟨selected_u, hsel_u, hi_u, hb_u⟩
  cases hc : r.input.state.coordinator with
  | first =>
      have hf : x.state.coordinator = .first := hc
      have hn : ReferenceCollectionPhaseHistory.cutoffChosen x = false := by
        simp only [ReferenceCollectionPhaseHistory.cutoffChosen,
          ReferenceActivePhysicalStep.prepare, ReferenceActivePhysicalStep.dispatch,
          hf, CoordinatorRoundDispatch.dispatch]
        rfl
      refine ⟨hn, ?_⟩
      obtain ⟨installed, arm, hchosen⟩ := ReferenceFirstAssignmentFibreStep.dispatchFirst_chosen_exists
        (ReferenceActivePhysicalStep.firstInput x)
      have htime := ReferenceActivePhysicalStep.dispatchFirst_chosen_time x installed arm hchosen
      let selected_u := ReferenceCoordinatorRecorderCallCorrespondence.selectionOfArm x
        installed.registers.payload installed.startRoundResult installed.registers.time
        installed.registers.complementWeights arm htime
      apply hstage_u selected_u
      · change (ReferenceActivePhysicalStep.dispatch x).selection = some selected_u
        rw [ReferenceActivePhysicalStep.dispatch_first x hf, hchosen]
        exact ReferenceCoordinatorRecorderCallCorrespondence.selectionAt_eq _ _ _ _ _ _ _
      · have hinst := ReferenceActivePhysicalStep.dispatchFirst_chosen_installation x installed arm hchosen
        simp [selected_u, ReferenceCoordinatorRecorderCallCorrespondence.selectionOfArm,
          hinst, CoordinatorAssignmentRegisterInstall.installFirst,
          CoordinatorAssignmentRegisterInstall.firstStartRoundResult]
        exact Finset.mem_univ i
      · cases after with
        | false => exact hb
        | true =>
            obtain ⟨state, memory, hordinary, hlast⟩ := hb
            have hnone := hphase
            simp only [ReferenceFirstLiveConfirmationHistory.FirstLiveState, hc] at hnone
            have hlastNone := (hnone i state memory hordinary).2
            rw [hlastNone] at hlast
            cases hlast
  | live registers owned base =>
      have hd : (ReferenceActivePhysicalStep.prepare r.input).coordinator =
          .live registers owned base (CoordinatorRoundDispatch.dispatchLive
            (ReferenceActivePhysicalStep.liveInput r.input registers owned base)) := by
        change ReferenceActivePhysicalStep.dispatch r.input = _
        simp only [ReferenceActivePhysicalStep.dispatch, hc, CoordinatorRoundDispatch.dispatch]
        rfl
      cases hout : CoordinatorRoundDispatch.dispatchLive
          (ReferenceActivePhysicalStep.liveInput r.input registers owned base) with
      | clockFailure failure hfailure => simp [hd, hout, ReferenceActivePhysicalStep.DispatchCut.selection] at hsel'
      | initializerFailure d hs checked hchecked => simp [hd, hout, ReferenceActivePhysicalStep.DispatchCut.selection] at hsel'
      | localFailure d hs failure => simp [hd, hout, ReferenceActivePhysicalStep.DispatchCut.selection] at hsel'
      | cutoffChosen d hs ledger hinitial hledger hvalid hclock hpending hnone arm =>
          simp [ReferenceCollectionPhaseHistory.cutoffChosen, hd, hout] at hno
      | continuingChosen d hs c arm =>
          have hp := hd.trans (congrArg (fun out => ReferenceActivePhysicalStep.DispatchCut.live
            registers owned base out) hout)
          obtain ⟨c_u, arm_u, hp_u⟩ := ReferenceContinuingLiveSlicePreparation.continuing_cut_at_control
            r.input registers owned base d hs c arm hp u
          refine ⟨?_, ?_⟩
          · change ReferenceCollectionPhaseHistory.cutoffChosen x = false
            dsimp only [x]
            simp only [ReferenceCollectionPhaseHistory.cutoffChosen, hp_u]
          · let selected_u := ReferenceContinuingLiveSlicePreparation.continuingSelection
              x registers owned base d hs c_u arm_u
            have hs_u := ReferenceContinuingLiveSlicePreparation.continuingSelection_eq_actual
              x registers owned base d hs c_u arm_u hp_u
            have hs_old := ReferenceContinuingLiveSlicePreparation.continuingSelection_eq_actual
              r.input registers owned base d hs c arm hp
            have heq := Option.some.inj (hsel'.symm.trans hs_old)
            subst selected
            apply hstage_u selected_u hs_u hi
            cases after <;> exact hb
  | collection payload ledger proposal =>
      simp only [ReferenceFirstLiveConfirmationHistory.FirstLiveState, hc] at hphase
  | dagger =>
      simp [ReferenceActivePhysicalStep.prepare, ReferenceActivePhysicalStep.dispatch,
        hc, ReferenceActivePhysicalStep.DispatchCut.selection] at hsel'

private theorem same_current_cutoff (x y : ReferenceActivePhysicalStep.RoundInput p rate)
    (hstate : x.state = y.state) (htime : x.time = y.time)
    (hcurrent : x.row.2 x.time = y.row.2 y.time) :
    ReferenceCollectionPhaseHistory.cutoffChosen x =
      ReferenceCollectionPhaseHistory.cutoffChosen y := by
  rcases x with ⟨state, rows, J, time, active, rewards⟩
  rcases y with ⟨state', rows', J', time', active', rewards'⟩
  dsimp only at hstate htime hcurrent
  subst state'
  subst time'
  cases hc : state.coordinator with
  | live registers owned base =>
      let R := ReferenceActivePhysicalStep.liveRegistersAt registers time
      let Q := ReferenceActivePhysicalStep.liveOwnedAt registers owned time
      have hdata := ReferenceActiveDispatchTemporal.liveOutcomeData_eq_of_current
        R Q base (rows J) (rows' J') hcurrent
      let tag := fun data : Fin p.K × Option (ReferenceDownReception.ChoiceTimeView p rate.eta) ×
          (Unit ⊕ (Unit ⊕ (ReferenceActiveDispatchTemporal.LiveArgs p rate ⊕
            ReferenceActiveDispatchTemporal.CollectionArgs p rate))) =>
        match data.2.2 with | .inr (.inr (.inr _)) => true | _ => false
      have hx : tag (ReferenceActiveDispatchTemporal.liveOutcomeData R Q base (rows J)
          (CoordinatorRoundDispatch.dispatchLive ⟨rate.eta, R, Q, base, rows J⟩)) =
          ReferenceCollectionPhaseHistory.cutoffChosen
            ⟨state, rows, J, time, active, rewards⟩ := by
        simp only [ReferenceCollectionPhaseHistory.cutoffChosen, ReferenceActivePhysicalStep.prepare,
          ReferenceActivePhysicalStep.dispatch, hc, CoordinatorRoundDispatch.dispatch]
        dsimp only [R, Q, ReferenceActivePhysicalStep.liveInput, ReferenceActivePhysicalStep.RoundInput.row]
        cases CoordinatorRoundDispatch.dispatchLive
          ⟨rate.eta, ReferenceActivePhysicalStep.liveRegistersAt registers time,
            ReferenceActivePhysicalStep.liveOwnedAt registers owned time, base, rows J⟩ <;> rfl
      have hy : tag (ReferenceActiveDispatchTemporal.liveOutcomeData R Q base (rows' J')
          (CoordinatorRoundDispatch.dispatchLive ⟨rate.eta, R, Q, base, rows' J'⟩)) =
          ReferenceCollectionPhaseHistory.cutoffChosen
            ⟨state, rows', J', time, active', rewards'⟩ := by
        simp only [ReferenceCollectionPhaseHistory.cutoffChosen, ReferenceActivePhysicalStep.prepare,
          ReferenceActivePhysicalStep.dispatch, hc, CoordinatorRoundDispatch.dispatch]
        dsimp only [R, Q, ReferenceActivePhysicalStep.liveInput, ReferenceActivePhysicalStep.RoundInput.row]
        cases CoordinatorRoundDispatch.dispatchLive
          ⟨rate.eta, ReferenceActivePhysicalStep.liveRegistersAt registers time,
            ReferenceActivePhysicalStep.liveOwnedAt registers owned time, base, rows' J'⟩ <;> rfl
      exact hx.symm.trans ((congrArg tag hdata).trans hy)
  | first =>
      simp only [ReferenceCollectionPhaseHistory.cutoffChosen, ReferenceActivePhysicalStep.prepare,
        ReferenceActivePhysicalStep.dispatch, hc, CoordinatorRoundDispatch.dispatch]
      rfl
  | collection payload ledger proposal =>
      simp only [ReferenceCollectionPhaseHistory.cutoffChosen, ReferenceActivePhysicalStep.prepare,
        ReferenceActivePhysicalStep.dispatch, hc]
      by_cases hbound : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
      · simp only [dite_eq_left hbound, CoordinatorRoundDispatch.dispatch]
        rfl
      · simp only [dite_eq_right hbound]
  | dagger =>
      simp only [ReferenceCollectionPhaseHistory.cutoffChosen, ReferenceActivePhysicalStep.prepare,
        ReferenceActivePhysicalStep.dispatch, hc]

private theorem takeWhile_at_iff {α : Type*} (test : α → Bool) (l : List α)
    (n : ℕ) (r : α) (hnodup : l.Nodup) (hr : l[n]? = some r) :
    r ∈ l.takeWhile test ↔ (∀ a ∈ l.take n, test a = true) ∧ test r = true := by
  induction l generalizing n with
  | nil => simp at hr
  | cons a l ih =>
      obtain ⟨ha, hl⟩ := List.nodup_cons.mp hnodup
      cases n with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hr
          subst r
          cases ht : test a <;> simp [ht]
      | succ n =>
          change l[n]? = some r at hr
          have hne : a ≠ r := fun h => ha (h ▸ List.mem_of_getElem? hr)
          cases ht : test a <;>
            simp [ht, Ne.symm hne, ih n hl hr]

private theorem choiceStage_eq (after : Bool) (i : Fin (p.m - 1))
    (r r' : Record (p := p) (rate := rate)) (hstate : r.input.state = r'.input.state)
    (hview : r.output.preparation.coordinator.selection.map (fun s => s.view) =
      r'.output.preparation.coordinator.selection.map (fun s => s.view)) :
    choiceStageCode (rate := rate) after i (ReferenceActiveHorizonMeasurability.roundRecordCode r) =
      choiceStageCode (rate := rate) after i (ReferenceActiveHorizonMeasurability.roundRecordCode r') := by
  apply Bool.eq_iff_iff.mpr
  rw [choiceStageCode_record, choiceStageCode_record]
  cases hs : r.output.preparation.coordinator.selection <;>
    cases hs' : r'.output.preparation.coordinator.selection <;>
    simp only [hs, hs', Option.map_none, Option.map_some, Option.some.injEq] at hview
  · simp
  · contradiction
  · contradiction
  rename_i selected selected'
  cases after <;> simp [Before, After, hstate, hview]

private def pastTags (s : ℕ) (t : Fin p.T) (z : Source p) :=
  ((ReferenceFirstLiveSourceStoppedReleaseEndpoint.completeRecords
    rate rewards C_star C_h z).take (t.val - s)).map
      (fun r => ReferenceCollectionPhaseHistory.cutoffChosen r.input)

private theorem pastTags_prefix (q : Fin (M p)) (s : ℕ) (t : Fin p.T) (hs : s ≤ t.val)
    (z : ReferenceTotalSourceDisintegration.SourceStratum rate rewards C_star C_h t
      (ReferenceFirstLiveRecordingSourceCylinder.stratumIndex q t s hs)) :
    pastTags rate rewards C_star C_h s t z.val =
      pastTags rate rewards C_star C_h s t
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z.val) := by
  let w := (⟨_, ReferenceFirstLiveNumericalPrefixTemporal.actualSourcePrefix_mem
    rate rewards C_star C_h q t s hs control0 z⟩ :
    ReferenceTotalSourceDisintegration.SourceStratum rate rewards C_star C_h t
      (ReferenceFirstLiveRecordingSourceCylinder.stratumIndex q t s hs))
  have htake (a : ReferenceTotalSourceDisintegration.SourceStratum rate rewards C_star C_h t
      (ReferenceFirstLiveRecordingSourceCylinder.stratumIndex q t s hs)) :=
    ReferenceGeneratedDownAmbiguityMeasurability.generatedRun_records_eq_completeSuffixRecords_take
      (rate := rate) rewards C_star C_h s (t.val - s) (by omega)
      ⟨a.val, (ReferenceFirstLiveNumericalPrefixTemporal.sourceStratum_facts
        rate rewards C_star C_h q t s hs a).2⟩
  have h := ReferenceFirstLiveNumericalPrefixTemporal.actualSourcePrefix_cutoffTags_eq
    rate rewards C_star C_h q t s hs control0 z w rfl
  have hrun (a : ReferenceTotalSourceDisintegration.SourceStratum rate rewards C_star C_h t
      (ReferenceFirstLiveRecordingSourceCylinder.stratumIndex q t s hs)) :=
    congrArg (fun R => R.records) (ReferenceFirstLiveOverflowReadout.actualFirstLiveRun_eq_generated
      rate rewards C_star C_h s (t.val - s) (by omega)
      ⟨a.val, (ReferenceFirstLiveNumericalPrefixTemporal.sourceStratum_facts
        rate rewards C_star C_h q t s hs a).2⟩)
  rw [hrun z, hrun w, htake z, htake w] at h
  exact h

section Sections

variable (q : Fin (M p)) (s : ℕ) (t : Fin p.T) (hs : s ≤ t.val)
local notation "Z" => ReferenceTotalSourceDisintegration.SourceStratum rate rewards C_star C_h t
  (ReferenceFirstLiveRecordingSourceCylinder.stratumIndex q t s hs)
local notation "R" => ReferenceFirstLiveSourceStoppedReleaseEndpoint.completeRecords rate rewards C_star C_h
local notation "prefix" => ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val

private theorem source_section_transfer (after : Bool) (i : Fin (p.m - 1))
    (z w : Z) (hprefix : prefix z.val = prefix w.val)
    (hz : z.val ∈ sectionCodeEvent rate rewards C_star C_h after t i) :
    w.val ∈ sectionCodeEvent rate rewards C_star C_h after t i := by
  obtain ⟨r, selected, hr, hW, hsel, hi, hb⟩ :=
    (sectionCodeEvent_iff rate rewards C_star C_h after t i z.val).mp hz
  have hzF := ReferenceFirstLiveNumericalPrefixTemporal.sourceStratum_facts rate rewards C_star C_h q t s hs z
  have hwF := ReferenceFirstLiveNumericalPrefixTemporal.sourceStratum_facts rate rewards C_star C_h q t s hs w
  have hin : ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t z.val =
      ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t w.val := by
    rw [ReferenceSourcePrefixHistoryFiltration.incoming_factor rate rewards C_star C_h control0 t z.val,
      ReferenceSourcePrefixHistoryFiltration.incoming_factor rate rewards C_star C_h control0 t w.val, hprefix]
  unfold ReferenceSourcePrefixHistoryFiltration.incoming at hin
  rw [hr] at hin
  cases hr' : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t w.val with
  | none => simp [hr'] at hin
  | some r' =>
      rw [hr'] at hin
      have hstate := ReferenceActivePhysicalStepMeasurability.encodeState_injective (Option.some.inj hin)
      obtain ⟨hrows, hJ, ht, hrew⟩ := actualRecord_sourceFields rate rewards C_star C_h t z.val r hr
      obtain ⟨hrows', hJ', ht', hrew'⟩ := actualRecord_sourceFields rate rewards C_star C_h t w.val r' hr'
      have hzS : ReferenceCompletePhysicalHistory.physicalStart rate z.val rewards C_star C_h = s := hzF.2.2
      have hwS : ReferenceCompletePhysicalHistory.physicalStart rate w.val rewards C_star C_h = s := hwF.2.2
      have hlookup : (R z.val)[t.val - s]? = some r := by
        simpa only [ReferenceSourcePrefixHistoryFiltration.actualRecord,
          ReferenceFirstLiveSourceStoppedReleaseEndpoint.completeRecords, hzS, ite_eq_left hs] using hr
      have hlookup' : (R w.val)[t.val - s]? = some r' := by
        simpa only [ReferenceSourcePrefixHistoryFiltration.actualRecord,
          ReferenceFirstLiveSourceStoppedReleaseEndpoint.completeRecords, hwS, ite_eq_left hs] using hr'
      have hnodup (a : Source p) : (R a).Nodup := by
        apply List.Nodup.of_map (fun r => r.input.time.val)
        change ((ReferenceCompletePhysicalHistory.completeSuffixRecords rate a rewards C_star C_h).map
          (fun r => r.input.time.val)).Nodup
        rw [ReferenceCompletePhysicalHistory.completeSuffixRecords_time_values]
        unfold ReferenceActivePhysicalHorizon.calendar
        exact List.nodup_range'
      have hcut := (takeWhile_at_iff (fun r : Record (rate := rate) => !ReferenceCollectionPhaseHistory.cutoffChosen r.input) (R z.val)
        (t.val - s) r (hnodup z.val) hlookup).mp hW
      have hphase : ReferenceFirstLiveConfirmationHistory.FirstLiveState r.input.state := by
        let seed := ReferenceLocalReleaseGateChronology.sourceSeed rate z.val rewards C_star C_h hzF.2.1
        have hseed := ReferenceLocalReleaseGateChronology.canonical_seed_release_inputs
          rate z.val rewards C_star C_h hzF.2.1
        have hlaunch := ReferenceLocalReleaseGateChronology.sourceSeed_launch rate z.val rewards C_star C_h hzF.2.1
        have hfull := ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
          rate z.val rewards C_star C_h seed hlaunch
        have hW' := hW
        change r ∈ ReferenceFirstLiveConfirmationHistory.firstLiveWindow
          (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z.val rewards C_star C_h) at hW'
        rw [hfull] at hW'
        obtain ⟨k, hk, heq⟩ := List.mem_iff_getElem.mp hW'
        have h := ReferenceFirstLiveConfirmationHistory.run_firstLive_carried seed z.val.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p z.val) rewards _ _ _ _
          hseed.1 hseed.2.2 ⟨k, hk⟩
        simpa only [heq] using h
      let r_u := ReferencePhysicalReleaseObservability.recordOfInput
        (ReferenceContinuingLiveSlicePreparation.inputAtControl r.input (r'.input.row.2 r'.input.time))
      obtain ⟨hno_u, hstage_u⟩ := choiceStage_control (rate := rate) after i r hphase
        (by simpa only [Bool.not_eq_true'] using hcut.2)
        ((choiceStageCode_record (rate := rate) after i r).mpr ⟨selected, hsel, hi, hb⟩)
        (r'.input.row.2 r'.input.time)
      have hcurrent : r_u.input.row.2 r_u.input.time = r'.input.row.2 r'.input.time := by
        simp [r_u, ReferencePhysicalReleaseObservability.recordOfInput]
      have hpast : ∀ v : Fin p.T, v.val < r_u.input.time.val →
          (r_u.input.row.2 v).1 ContinuousControlSlice.Label.prop =
            (r'.input.row.2 v).1 ContinuousControlSlice.Label.prop := by
        intro v hv
        have hv' : v.val < t.val := by simpa [r_u, ReferencePhysicalReleaseObservability.recordOfInput, ht] using hv
        have hc := congrArg (fun a : Source p => (a.1.2 q).2 v) hprefix
        have hzC := ReferenceSourcePrefixHistoryFiltration.sourcePrefix_control control0 t.val z.val v
        have hwC := ReferenceSourcePrefixHistoryFiltration.sourcePrefix_control control0 t.val w.val v
        rw [hzF.1] at hzC
        rw [hwF.1] at hwC
        simp only [hzC, hwC, ite_eq_left hv'] at hc
        dsimp only [r_u, ReferencePhysicalReleaseObservability.recordOfInput]
        rw [ReferenceContinuingLiveSlicePreparation.inputAtControl_row,
          ReferenceContinuingLiveSlicePreparation.rowAtControl_other_time _ _ v (by rw [ht]; exact Fin.ne_of_val_ne (by omega))]
        simpa only [ReferenceActivePhysicalStep.RoundInput.row, hrows, hJ, hzF.1,
          hrows', hJ', hwF.1] using congrArg (fun u : TimeControl p => u.1 ContinuousControlSlice.Label.prop) hc
      have hread := recordReads_eq_of_temporal_reads (rate := rate) r_u r' hstate
        (hJ.trans (hzF.1.trans (hwF.1.symm.trans hJ'.symm))) (ht.trans ht'.symm)
        (hrew.trans hrew'.symm) hcurrent hpast
      have hstage' := (choiceStage_eq (rate := rate) after i r_u r' hstate
        (congrArg (fun reads => reads.2.1) hread)).symm.trans hstage_u
      have hno' := (same_current_cutoff (rate := rate) r_u.input r'.input hstate
        (ht.trans ht'.symm) hcurrent).symm.trans hno_u
      have htags : pastTags rate rewards C_star C_h s t z.val =
          pastTags rate rewards C_star C_h s t w.val :=
        (pastTags_prefix rate rewards C_star C_h control0 q s t hs z).trans
          ((congrArg (pastTags rate rewards C_star C_h s t) hprefix).trans
            (pastTags_prefix rate rewards C_star C_h control0 q s t hs w).symm)
      have hpastAll : (pastTags rate rewards C_star C_h s t w.val).all Bool.not = true := by
        rw [← htags]
        simpa only [pastTags, List.all_map, List.all_eq_true, Function.comp_def] using hcut.1
      have hW' : r' ∈ firstWindow rate rewards C_star C_h w.val := by
        apply (takeWhile_at_iff (fun r : Record (rate := rate) => !ReferenceCollectionPhaseHistory.cutoffChosen r.input) (R w.val) (t.val - s) r' (hnodup w.val) hlookup').mpr
        exact ⟨by simpa only [pastTags, List.all_map, List.all_eq_true, Function.comp_def] using hpastAll,
          by simpa only [Bool.not_eq_true'] using hno'⟩
      obtain ⟨selected', hsel', hi', hb'⟩ := (choiceStageCode_record (rate := rate) after i r').mp hstage'
      exact (sectionCodeEvent_iff rate rewards C_star C_h after t i w.val).mpr
        ⟨r', selected', hr', hW', hsel', hi', hb'⟩

include hs

private theorem E_prefix (after : Bool) (i : Fin (p.m - 1)) (z : Source p) :
    z ∈ (if after then E_after rate rewards C_star C_h q s t i else E_before rate rewards C_star C_h q s t i) ↔
      prefix z ∈ (if after then E_after rate rewards C_star C_h q s t i else E_before rate rewards C_star C_h q s t i) := by
  rw [E_eq_code rate rewards C_star C_h after q s t hs i]
  have hf : z ∈ ReferenceTotalSourcePairCoupling.sourceStratumEvent rate rewards C_star C_h t
      (ReferenceFirstLiveRecordingSourceCylinder.stratumIndex q t s hs) ↔
      prefix z ∈ ReferenceTotalSourcePairCoupling.sourceStratumEvent rate rewards C_star C_h t
        (ReferenceFirstLiveRecordingSourceCylinder.stratumIndex q t s hs) := by
    change (ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p z = q ∧ _) ↔
      (ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p (prefix z) = q ∧ _)
    rw [ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex,
      ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex,
      ReferenceSourcePrefixHistoryFiltration.sourcePrefix_selected]
    exact and_congr_right' (ReferenceSourcePrefixHistoryFiltration.actualLaunchStratum_factor
      rate rewards C_star C_h control0 t.val (by omega) s hs z)
  by_cases hz : z ∈ ReferenceTotalSourcePairCoupling.sourceStratumEvent rate rewards C_star C_h t
      (ReferenceFirstLiveRecordingSourceCylinder.stratumIndex q t s hs)
  · have hw := hf.mp hz
    simp only [Set.mem_inter_iff, hz, hw, true_and]
    let zz : Z := ⟨z, hz⟩
    let ww : Z := ⟨prefix z, hw⟩
    have hpp : prefix zz.val = prefix ww.val :=
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefix_sourcePrefix control0 t.val t.val le_rfl z).symm
    exact ⟨source_section_transfer rate rewards C_star C_h control0 q s t hs after i zz ww hpp,
      source_section_transfer rate rewards C_star C_h control0 q s t hs after i ww zz hpp.symm⟩
  · simp only [Set.mem_inter_iff, hz, false_and, false_iff]
    exact fun h => hz (hf.mpr h.1)

private theorem E_measurable (after : Bool) (i : Fin (p.m - 1)) :
    MeasurableSet[H (t.val + 1)]
      (if after then E_after rate rewards C_star C_h q s t i else E_before rate rewards C_star C_h q s t i) := by
  rw [ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration_succ,
    MeasurableSpace.measurableSet_comap]
  refine ⟨(if after then E_after rate rewards C_star C_h q s t i
    else E_before rate rewards C_star C_h q s t i), ?_, ?_⟩
  · rw [E_eq_code rate rewards C_star C_h after q s t hs i]
    exact (ReferenceTotalSourcePairCoupling.measurableSet_sourceStratumEvent
      rate rewards C_star C_h t control0 _).inter
        (measurableSet_sectionCodeEvent rate rewards C_star C_h after t i)
  · ext z
    exact (E_prefix rate rewards C_star C_h control0 q s t hs after i z).symm

theorem E_before_sourcePrefix (i : Fin (p.m - 1)) (z : Source p) :
    z ∈ E_before rate rewards C_star C_h q s t i ↔ prefix z ∈ E_before rate rewards C_star C_h q s t i :=
  E_prefix rate rewards C_star C_h control0 q s t hs false i z

theorem E_after_sourcePrefix (i : Fin (p.m - 1)) (z : Source p) :
    z ∈ E_after rate rewards C_star C_h q s t i ↔ prefix z ∈ E_after rate rewards C_star C_h q s t i :=
  E_prefix rate rewards C_star C_h control0 q s t hs true i z

theorem measurableSet_E_before (i : Fin (p.m - 1)) :
    MeasurableSet[H (t.val + 1)] (E_before rate rewards C_star C_h q s t i) :=
  E_measurable rate rewards C_star C_h control0 q s t hs false i

theorem measurableSet_E_after (i : Fin (p.m - 1)) :
    MeasurableSet[H (t.val + 1)] (E_after rate rewards C_star C_h q s t i) :=
  E_measurable rate rewards C_star C_h control0 q s t hs true i

end Sections

end Bandits.Support.ReferenceFirstLiveHandoverBoundaryFactorization

end
