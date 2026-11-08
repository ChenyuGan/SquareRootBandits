/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceOriginalStoppedPhysicalTransferStarts
public import Bandits.Support.ReferenceOriginalCalendarTransferPhaseCover
public import Bandits.Support.ReferencePostReplacementCollectionHandoverSourcePrefix

import Mathlib.Tactic

/-!
# Original kth collection source sections

The prechoice observer below reads the incoming encoded coordinator at the
current original-source round. Its collection ledger is the literal retained
ledger, or the exact ledger initialized by the live `initializeAt` command.
No phase-membership scan is used to construct this pre-round data.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support
open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceSourcePrefixHistoryFiltration (sourcePrefix sourcePrefixFiltration)
open scoped Classical

namespace Bandits.Support.ReferenceOriginalKthCollectionSourceSections

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceOriginalStoppedPhysicalTransferStarts.RateInput
abbrev SourceInput (p : Parameters) :=
  ReferenceOriginalStoppedPhysicalTransferStarts.SourceInput p
abbrev GridRewardTable (p : Parameters) :=
  ReferenceOriginalStoppedPhysicalTransferStarts.GridRewardTable p

variable {p : Parameters}
variable (rate : RateInput p) (rewards : GridRewardTable p)
  (C_star C_h : ℝ)

/-- A source prechoice keeps the complete old payload, its actual pending and
cutoff fields, and the exact incoming coordinator code.  That code retains the
whole stored collection ledger or all live queue/register fields. -/
abbrev KthCPrechoiceData :=
  ReferenceActivePhysicalStep.Payload rate ×
    (Finset (Fin (p.m - 1)) ×
      (ℕ × ReferenceActivePhysicalStepMeasurability.CoordinatorCode p rate))

abbrev KthCDownWord :=
  OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta)
abbrev KthCStartCode :=
  Unit ⊕ FollowerLifecycleMeasurability.StartRoundResultCode p rate

local instance kthCDownWordMeasurableSpace : MeasurableSpace (KthCDownWord rate) := ⊤
local instance kthCPendingMeasurableSpace :
    MeasurableSpace (Finset (Fin (p.m - 1))) := ⊤
local instance kthCDownWordSingleton : MeasurableSingletonClass (KthCDownWord rate) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩
local instance kthCPendingSingleton :
    MeasurableSingletonClass (Finset (Fin (p.m - 1))) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩
local instance kthCStartCodeSingleton : MeasurableSingletonClass (KthCStartCode rate) := by
  constructor
  intro code
  cases code with
  | inl unitCode =>
      rw [measurableSet_sum_iff]
      exact ⟨MeasurableSpace.measurableSet_top, MeasurableSpace.measurableSet_top⟩
  | inr startCode =>
      rw [measurableSet_sum_iff]
      exact ⟨MeasurableSpace.measurableSet_top, MeasurableSpace.measurableSet_top⟩

/-- The source's `Fin (m - 1)` follower index in the accepted protocol
carrier `Follower m`. -/
def kthFollowerIndex (i : Fin (p.m - 1)) : ActiveRoundActions.Follower p.m :=
  ⟨i.val, by simp [PublicDiscreteDraws.followerCount]⟩

/-- The checked LIVE start command depends only on the incoming encoded clock
and pending set.  The current row and all future phase membership are absent. -/
def liveIssuesInitializeAt (t : Fin p.T)
    (live : ReferenceActivePhysicalStepMeasurability.LiveDiscrete p) : Bool :=
  match CoordinatorPhaseClock.startRound p rate.eta.val t
      ⟨live.clockSigma, live.clockCutoff, live.clockBoundary, live.clockProposal⟩
      live.pending with
  | .error _ => false
  | .ok started => decide (started.ledgerCommand = some (.initializeAt t))

/-- Lossless tagged code for the same incoming LIVE coordinator registers. -/
def kthLiveCoordinatorCode
    (pair : ReferenceActivePhysicalStep.Payload rate ×
      ReferenceActivePhysicalStepMeasurability.LiveDiscrete p) :
    ReferenceActivePhysicalStepMeasurability.CoordinatorCode p rate :=
  Sum.inr (Sum.inl pair :
    (ReferenceActivePhysicalStep.Payload rate ×
      ReferenceActivePhysicalStepMeasurability.LiveDiscrete p) ⊕
    ((ReferenceActivePhysicalStep.Payload rate ×
      (ReferenceActivePhysicalStep.Ledger rate × Option (Fin p.T × Bool))) ⊕ Unit))

private theorem measurable_kthLiveCoordinatorCode :
    Measurable (kthLiveCoordinatorCode (p := p) (rate := rate)) := by
  change Measurable (fun pair : ReferenceActivePhysicalStep.Payload rate ×
    ReferenceActivePhysicalStepMeasurability.LiveDiscrete p =>
      (Sum.inr (Sum.inl pair :
        (ReferenceActivePhysicalStep.Payload rate ×
          ReferenceActivePhysicalStepMeasurability.LiveDiscrete p) ⊕
        ((ReferenceActivePhysicalStep.Payload rate ×
          (ReferenceActivePhysicalStep.Ledger rate × Option (Fin p.T × Bool))) ⊕ Unit)) :
        ReferenceActivePhysicalStepMeasurability.CoordinatorCode p rate))
  exact measurable_inr.comp measurable_inl

/-- Lossless tagged code for the same incoming COLLECTION coordinator state. -/
def kthCollectionCoordinatorCode
    (pair : ReferenceActivePhysicalStep.Payload rate ×
      (ReferenceActivePhysicalStep.Ledger rate × Option (Fin p.T × Bool))) :
    ReferenceActivePhysicalStepMeasurability.CoordinatorCode p rate :=
  Sum.inr (Sum.inr (Sum.inl pair :
    (ReferenceActivePhysicalStep.Payload rate ×
      (ReferenceActivePhysicalStep.Ledger rate × Option (Fin p.T × Bool))) ⊕ Unit) :
    (ReferenceActivePhysicalStep.Payload rate ×
      ReferenceActivePhysicalStepMeasurability.LiveDiscrete p) ⊕
    ((ReferenceActivePhysicalStep.Payload rate ×
      (ReferenceActivePhysicalStep.Ledger rate × Option (Fin p.T × Bool))) ⊕ Unit))

private theorem measurable_kthCollectionCoordinatorCode :
    Measurable (kthCollectionCoordinatorCode (p := p) (rate := rate)) := by
  change Measurable (fun pair : ReferenceActivePhysicalStep.Payload rate ×
    (ReferenceActivePhysicalStep.Ledger rate × Option (Fin p.T × Bool)) =>
      (Sum.inr (Sum.inr (Sum.inl pair :
        (ReferenceActivePhysicalStep.Payload rate ×
          (ReferenceActivePhysicalStep.Ledger rate × Option (Fin p.T × Bool))) ⊕ Unit) :
        (ReferenceActivePhysicalStep.Payload rate ×
          ReferenceActivePhysicalStepMeasurability.LiveDiscrete p) ⊕
        ((ReferenceActivePhysicalStep.Payload rate ×
          (ReferenceActivePhysicalStep.Ledger rate × Option (Fin p.T × Bool))) ⊕ Unit)) :
        ReferenceActivePhysicalStepMeasurability.CoordinatorCode p rate))
  exact measurable_inr.comp (measurable_inr.comp measurable_inl)

/-- Read optional C prechoice data from the incoming coordinator encoding.
LIVE initialization keeps the old payload with the actual universal initial
pending set; COLLECTION keeps its stored payload and nonempty ledger fields.
Empty pending, first, dagger, and absent records have literal absence. -/
def kthCPrechoiceDataFromCoordinatorCode (t : Fin p.T) :
    ReferenceActivePhysicalStepMeasurability.CoordinatorCode p rate →
      Option (KthCPrechoiceData rate)
  | .inl _ => none
  | .inr (.inl (payload, live)) =>
      if liveIssuesInitializeAt rate t live then
        some (payload, (Finset.univ,
          (t.val + 1, kthLiveCoordinatorCode rate (payload, live))))
      else none
  | .inr (.inr (.inl (payload, ledger, savedProposal))) =>
      if decide ledger.pending.Nonempty then
        some (payload, (ledger.pending,
          (ledger.cutoff, kthCollectionCoordinatorCode rate (payload, ledger, savedProposal))))
      else none
  | .inr (.inr (.inr _)) => none

/-- Project the prechoice only from the coordinator component of the
lossless incoming state code. -/
def kthCPrechoiceDataFromIncomingCode (t : Fin p.T)
    (code : ReferenceActivePhysicalStepMeasurability.StateCode p rate) :
    Option (KthCPrechoiceData rate) :=
  kthCPrechoiceDataFromCoordinatorCode rate t code.1

/-- The optional C prechoice read from the same incoming actual state used by
the original source observer. -/
noncomputable def kthCPrechoiceData (t : Fin p.T) (z : SourceInput p) :
    Option (KthCPrechoiceData rate) :=
  (ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t z).bind
    (kthCPrechoiceDataFromIncomingCode rate t)

private theorem measurable_optionBind {X Y W : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace W]
    (f : Y → Option W) (hf : Measurable f) (g : X → Option Y)
    (hg : Measurable g) : Measurable (fun x => (g x).bind f) := by
  have hbind : Measurable (fun o : Option Y => o.bind f) := by
    apply measurable_comap_iff.mpr
    have hsum : Measurable (Sum.elim
        (fun y => Equiv.optionEquivSumPUnit W (f y))
        (fun _ : PUnit => Equiv.optionEquivSumPUnit W none)) :=
      (measurable_comap_iff.mp hf).sumElim measurable_const
    convert hsum.comp (comap_measurable (Equiv.optionEquivSumPUnit Y)) using 1
    funext o
    cases o <;> rfl
  exact hbind.comp hg

/-- Borel measurability of the incoming-code projection retains the payload's
continuous product structure, pending/cutoff coordinates, and exact
coordinator code. -/
theorem kthCPrechoiceDataFromIncomingCode_measurable (t : Fin p.T) :
    Measurable (kthCPrechoiceDataFromIncomingCode rate t) := by
  classical
  have hLive : Measurable (fun pair :
      ReferenceActivePhysicalStep.Payload rate ×
        ReferenceActivePhysicalStepMeasurability.LiveDiscrete p =>
      if liveIssuesInitializeAt rate t pair.2 then
        some (pair.1, ((Finset.univ : Finset (Fin (p.m - 1))),
          (t.val + 1, kthLiveCoordinatorCode rate pair))) else none) := by
    have hinit : Measurable (fun pair :
        ReferenceActivePhysicalStep.Payload rate ×
          ReferenceActivePhysicalStepMeasurability.LiveDiscrete p =>
        liveIssuesInitializeAt rate t pair.2) :=
      (measurable_of_countable (liveIssuesInitializeAt rate t)).comp measurable_snd
    have hsome : Measurable (fun pair :
        ReferenceActivePhysicalStep.Payload rate ×
          ReferenceActivePhysicalStepMeasurability.LiveDiscrete p =>
        some (pair.1, ((Finset.univ : Finset (Fin (p.m - 1))),
          (t.val + 1, kthLiveCoordinatorCode rate pair)))) := by
      have htuple : Measurable (fun pair :
          ReferenceActivePhysicalStep.Payload rate ×
            ReferenceActivePhysicalStepMeasurability.LiveDiscrete p =>
          (pair.1, ((Finset.univ : Finset (Fin (p.m - 1))),
            (t.val + 1, kthLiveCoordinatorCode rate pair)))) := by
        exact measurable_fst.prodMk (measurable_const.prodMk
          (measurable_const.prodMk
            (measurable_kthLiveCoordinatorCode (p := p) (rate := rate))))
      apply measurable_comap_iff.mpr
      convert (measurable_inl.comp htuple) using 1
      funext pair
      rfl
    exact Measurable.ite (hinit (measurableSet_singleton true)) hsome measurable_const
  have hCollection : Measurable (fun pair :
      ReferenceActivePhysicalStep.Payload rate ×
        (ReferenceActivePhysicalStep.Ledger rate × Option (Fin p.T × Bool)) =>
      if decide pair.2.1.pending.Nonempty then
        some (pair.1, (pair.2.1.pending,
          (pair.2.1.cutoff, kthCollectionCoordinatorCode rate pair))) else none) := by
    have hpending : Measurable (fun pair :
        ReferenceActivePhysicalStep.Payload rate ×
          (ReferenceActivePhysicalStep.Ledger rate × Option (Fin p.T × Bool)) =>
        decide pair.2.1.pending.Nonempty) :=
      (measurable_of_countable
        (fun ledger : ReferenceActivePhysicalStep.Ledger rate =>
          decide ledger.pending.Nonempty)).comp
        (measurable_fst.comp measurable_snd)
    have hsome : Measurable (fun pair :
        ReferenceActivePhysicalStep.Payload rate ×
          (ReferenceActivePhysicalStep.Ledger rate × Option (Fin p.T × Bool)) =>
        some (pair.1, (pair.2.1.pending,
          (pair.2.1.cutoff, kthCollectionCoordinatorCode rate pair)))) := by
      have htuple : Measurable (fun pair :
          ReferenceActivePhysicalStep.Payload rate ×
            (ReferenceActivePhysicalStep.Ledger rate × Option (Fin p.T × Bool)) =>
          (pair.1, (pair.2.1.pending,
            (pair.2.1.cutoff, kthCollectionCoordinatorCode rate pair)))) := by
        have hPending : Measurable (fun ledger : ReferenceActivePhysicalStep.Ledger rate =>
            ledger.pending) := measurable_of_countable
              (fun ledger : ReferenceActivePhysicalStep.Ledger rate => ledger.pending)
        have hCutoff : Measurable (fun ledger : ReferenceActivePhysicalStep.Ledger rate =>
            ledger.cutoff) := measurable_of_countable
              (fun ledger : ReferenceActivePhysicalStep.Ledger rate => ledger.cutoff)
        exact measurable_fst.prodMk
          ((hPending.comp (measurable_fst.comp measurable_snd)).prodMk
            ((hCutoff.comp (measurable_fst.comp measurable_snd)).prodMk
              (measurable_kthCollectionCoordinatorCode (p := p) (rate := rate))))
      apply measurable_comap_iff.mpr
      convert (measurable_inl.comp htuple) using 1
      funext pair
      rfl
    exact Measurable.ite (hpending (measurableSet_singleton true)) hsome measurable_const
  have hcoord : Measurable (kthCPrechoiceDataFromCoordinatorCode rate t) := by
    exact measurable_const.sumElim
      (hLive.sumElim (hCollection.sumElim measurable_const))
  exact hcoord.comp measurable_fst

/-- The full original-source prechoice datum is Borel in the same pre-round
field as the encoded incoming state. -/
theorem kthCPrechoiceData_preRound_measurable
    (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T) :
    Measurable[sourcePrefixFiltration control0 (t.val + 1)]
      (kthCPrechoiceData rate rewards C_star C_h t) := by
  let : MeasurableSpace (SourceInput p) :=
    sourcePrefixFiltration control0 (t.val + 1)
  exact measurable_optionBind _
    (kthCPrechoiceDataFromIncomingCode_measurable rate t)
    (ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t)
    (ReferenceSourcePrefixHistoryFiltration.incoming_measurable
      rate rewards C_star C_h control0 t)

/-- The prechoice data factors through the original strict source prefix.
The whole source, including private arrays and all public rows, remains the
input to the accepted incoming-state factorization. -/
theorem kthCPrechoiceData_factor (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) (z : SourceInput p) :
    kthCPrechoiceData rate rewards C_star C_h t z =
      kthCPrechoiceData rate rewards C_star C_h t (sourcePrefix control0 t.val z) := by
  unfold kthCPrechoiceData
  rw [ReferenceSourcePrefixHistoryFiltration.incoming_factor
    rate rewards C_star C_h control0 t z]

/-- The pre-round follower stage retains the literal pending set from the
incoming C ledger.  The old/formed distinction is decided against the same
payload's actual DOWN word; every other start result remains nonordinary. -/
def kthCPrechoiceStage (t : Fin p.T) (i : Fin (p.m - 1)) (z : SourceInput p) :
    Option (Finset (Fin (p.m - 1)) ×
      ReferenceFirstReplacementCollectionPredictableStages.TaskStage) :=
  (kthCPrechoiceData rate rewards C_star C_h t z).map fun data =>
    (data.2.1,
      ReferenceFirstReplacementCollectionPredictableStages.startStage rate
        (data.1.downRecord (kthFollowerIndex (p := p) i))
        (ReferenceFirstReplacementCollectionPredictableStages.preRoundStart
          rate rewards C_star C_h t i z))

/-- The actual old DOWN word and pending set carried by the incoming
prechoice, before applying the checked follower START result. -/
def kthCPrechoiceWord (t : Fin p.T) (i : Fin (p.m - 1)) (z : SourceInput p) :
    Option (KthCDownWord rate × Finset (Fin (p.m - 1))) :=
  (kthCPrechoiceData rate rewards C_star C_h t z).map fun data =>
    (data.1.downRecord (kthFollowerIndex (p := p) i), data.2.1)

/-- Apply the accepted exact `startStage` test to the same optional incoming
word and incoming follower preparation code. -/
def kthCPrechoiceStageFromWordStart
    (q : Option (KthCDownWord rate × Finset (Fin (p.m - 1))) × KthCStartCode rate) :
    Option (Finset (Fin (p.m - 1)) ×
      ReferenceFirstReplacementCollectionPredictableStages.TaskStage) :=
  q.1.map fun word =>
    (word.2, ReferenceFirstReplacementCollectionPredictableStages.startStage rate
      word.1 q.2)

/-- The source-facing stage uses the same incoming state and strict prefix as
the prechoice payload. -/
theorem kthCPrechoiceStage_factor (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) (i : Fin (p.m - 1)) (z : SourceInput p) :
    kthCPrechoiceStage rate rewards C_star C_h t i z =
      kthCPrechoiceStage rate rewards C_star C_h t i (sourcePrefix control0 t.val z) := by
  unfold kthCPrechoiceStage
  rw [kthCPrechoiceData_factor rate rewards C_star C_h control0 t z,
    ReferenceFirstReplacementCollectionPredictableStages.preRoundStart_factor
      rate rewards C_star C_h control0 t i z]

private theorem measurable_optionSome {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] {f : X → Y}
    (hf : Measurable f) : Measurable (fun x => some (f x)) := by
  apply measurable_comap_iff.mpr
  convert (measurable_inl.comp hf) using 1
  funext x
  rfl

private theorem kthOptionBorel_eq_top (A : Type*) [MeasurableSpace A]
    [Countable A] [MeasurableSingletonClass A] :
    @LaterAssignmentStartMeasurability.optionMeasurableSpace A inferInstance = ⊤ := by
  apply MeasurableSpace.ext
  intro U
  constructor
  · intro _
    trivial
  · intro _
    rw [LaterAssignmentStartMeasurability.optionMeasurableSpace,
      MeasurableSpace.measurableSet_comap]
    let e := Equiv.optionEquivSumPUnit A
    have hU : MeasurableSet (e '' U) := by
      rw [measurableSet_sum_iff]
      exact ⟨(Set.to_countable _).measurableSet,
        (Set.to_countable _).measurableSet⟩
    exact ⟨e '' U, hU, e.injective.preimage_image U⟩

/-- The actual incoming payload DOWN word and pending set are Borel in the
same source-prefix field. -/
theorem kthCPrechoiceWord_preRound_measurable
    (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T)
    (i : Fin (p.m - 1)) :
    Measurable[sourcePrefixFiltration control0 (t.val + 1)]
      (kthCPrechoiceWord rate rewards C_star C_h t i) := by
  let : MeasurableSpace (SourceInput p) := sourcePrefixFiltration control0 (t.val + 1)
  have hData := kthCPrechoiceData_preRound_measurable rate rewards C_star C_h control0 t
  have hDown := ReferenceFirstReplacementCollectionPredictableStages.measurable_payloadDown
    (p := p) (rate := rate) i
  have hDown' : Measurable (fun payload : ReferenceActivePhysicalStep.Payload rate =>
      payload.downRecord (kthFollowerIndex (p := p) i)) := by
    simpa [kthFollowerIndex, ActiveRoundActions.Follower,
      PublicDiscreteDraws.followerCount] using hDown
  have hProjection : Measurable (fun data : KthCPrechoiceData rate =>
      (data.1.downRecord (kthFollowerIndex (p := p) i), data.2.1)) :=
    (hDown'.comp measurable_fst).prodMk (measurable_fst.comp measurable_snd)
  have hSome := measurable_optionSome hProjection
  have h := measurable_optionBind _ hSome
    (kthCPrechoiceData rate rewards C_star C_h t) hData
  have hspace := kthOptionBorel_eq_top
    (KthCDownWord rate × Finset (Fin (p.m - 1)))
  have hspace' :
      LaterAssignmentStartMeasurability.optionMeasurableSpace
          (α := KthCDownWord rate × Finset (Fin (p.m - 1))) =
        ReferenceInitializationMeasurability.optionCountableMeasurableSpace
          (KthCDownWord rate × Finset (Fin (p.m - 1))) := by
    simpa [ReferenceInitializationMeasurability.optionCountableMeasurableSpace] using hspace
  have heq : kthCPrechoiceWord rate rewards C_star C_h t i =
      fun z => (kthCPrechoiceData rate rewards C_star C_h t z).bind
        (fun data => some
          (data.1.downRecord (kthFollowerIndex (p := p) i), data.2.1)) := by
    funext z
    cases hk : kthCPrechoiceData rate rewards C_star C_h t z <;>
      simp [kthCPrechoiceWord, hk]
  rw [heq]
  rw [← hspace']
  exact h

/-- The optional OLD/FORMED/nonordinary task-stage view is Borel before the
same original round. Its pending coordinate is the literal incoming set. -/
theorem kthCPrechoiceStage_preRound_measurable
    (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T)
    (i : Fin (p.m - 1)) :
    Measurable[sourcePrefixFiltration control0 (t.val + 1)]
      (kthCPrechoiceStage rate rewards C_star C_h t i) := by
  let F := sourcePrefixFiltration control0 (t.val + 1)
  let : MeasurableSpace (SourceInput p) := F
  have hword := kthCPrechoiceWord_preRound_measurable
    rate rewards C_star C_h control0 t i
  have hstart := ReferenceFirstReplacementCollectionPredictableStages.preRoundStart_measurable
    rate rewards C_star C_h control0 t i
  have hpair : Measurable[F] (fun z : SourceInput p =>
      (kthCPrechoiceWord rate rewards C_star C_h t i z,
        ReferenceFirstReplacementCollectionPredictableStages.preRoundStart
          rate rewards C_star C_h t i z)) := hword.prodMk hstart
  have hcode : Measurable (kthCPrechoiceStageFromWordStart (rate := rate)) := by
    apply measurable_from_prod_countable_right
    intro word
    cases word with
    | none => exact measurable_const
    | some word =>
        exact measurable_of_countable (fun start : KthCStartCode rate =>
          (some (word.2,
            ReferenceFirstReplacementCollectionPredictableStages.startStage rate
              word.1 start) : Option (Finset (Fin (p.m - 1)) ×
                ReferenceFirstReplacementCollectionPredictableStages.TaskStage)))
  have heq : kthCPrechoiceStage rate rewards C_star C_h t i =
      fun z => kthCPrechoiceStageFromWordStart (rate := rate)
        (kthCPrechoiceWord rate rewards C_star C_h t i z,
          ReferenceFirstReplacementCollectionPredictableStages.preRoundStart
            rate rewards C_star C_h t i z) := by
    funext z
    cases hk : kthCPrechoiceData rate rewards C_star C_h t z <;>
      simp [kthCPrechoiceStage, kthCPrechoiceWord,
        kthCPrechoiceStageFromWordStart, hk]
  rw [heq]
  exact hcode.comp hpair

/-- The next ranked start, with the same `T + 1` sentinel used by the
accepted stopped-start enumeration. -/
def kthNextStoppedStartDate (k : Fin (p.T + 1)) (z : SourceInput p) : ℕ :=
  if hk : k.val + 1 ≤ p.T then
    ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
      rate rewards C_star C_h ⟨k.val + 1, by omega⟩ z
  else p.T + 1

/-- The kth collection interval at original date `t`: its ranked start has
occurred, its next original start has not occurred, and the inclusive first
bad-date gate still includes `t + 1`. -/
def kthCStratum (k : Fin (p.T + 1)) (t : Fin p.T) (z : SourceInput p) : Prop :=
  ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
      rate rewards C_star C_h k z ≤ t.val + 1 ∧
    t.val + 1 < kthNextStoppedStartDate rate rewards C_star C_h k z ∧
    t.val + 1 ≤ ReferenceCompleteSignedFirstBadCalendar.firstBadDate
      rate rewards C_star C_h z

/-- Each actual stopped-start test through the current date factors through
the same source prefix, by composing the accepted prefix test with the
source-prefix composition law. -/
private theorem stoppedStartAt_prefixExtension
    (control0 : ContinuousLearningRows.TimeControl p) (q t : Fin p.T)
    (hqt : q.val ≤ t.val) (z : SourceInput p) :
    ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartAt
        rate rewards C_star C_h q z ↔
      ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartAt
        rate rewards C_star C_h q (sourcePrefix control0 t.val z) := by
  have hq := ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartAt_prefix_factor
    rate rewards C_star C_h control0 q z
  have hqt' := ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartAt_prefix_factor
      rate rewards C_star C_h control0 q (sourcePrefix control0 t.val z)
  rw [ReferenceSourcePrefixHistoryFiltration.sourcePrefix_sourcePrefix
    control0 q.val t.val hqt z] at hqt'
  exact hq.trans hqt'.symm

/-- The count through an in-scope round is unchanged on its original strict
source prefix. -/
private theorem stoppedStartCountThrough_prefix_factor
    (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T)
    (n : ℕ) (hn : n ≤ t.val + 1) (z : SourceInput p) :
    ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartCountThrough
        rate rewards C_star C_h n z =
      ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartCountThrough
        rate rewards C_star C_h n (sourcePrefix control0 t.val z) := by
  classical
  have hfilter :
      (ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartRounds
        rate rewards C_star C_h z).filter (fun q => q.val + 1 ≤ n) =
      (ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartRounds
        rate rewards C_star C_h (sourcePrefix control0 t.val z)).filter
          (fun q => q.val + 1 ≤ n) := by
    ext q
    simp only [Finset.mem_filter,
      ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartRounds,
      Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hq, hqn⟩
      have hqt : q.val ≤ t.val := by omega
      exact ⟨(stoppedStartAt_prefixExtension
        rate rewards C_star C_h control0 q t hqt z).mp hq, hqn⟩
    · rintro ⟨hq, hqn⟩
      have hqt : q.val ≤ t.val := by omega
      exact ⟨(stoppedStartAt_prefixExtension
        rate rewards C_star C_h control0 q t hqt z).mpr hq, hqn⟩
  unfold ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartCountThrough
  rw [hfilter]

/-- The ranked date comparison through the current round factors through the
same original strict prefix; future ranked dates themselves are not replaced. -/
private theorem stoppedPhysicalTransferStartDate_le_prefix_factor
    (control0 : ContinuousLearningRows.TimeControl p) (k : Fin (p.T + 1))
    (t : Fin p.T) (z : SourceInput p) :
    ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
        rate rewards C_star C_h k z ≤ t.val + 1 ↔
      ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
        rate rewards C_star C_h k (sourcePrefix control0 t.val z) ≤ t.val + 1 := by
  rw [ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate_le_iff_count_gt
      rate rewards C_star C_h k (t.val + 1) (by omega) z,
    ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate_le_iff_count_gt
      rate rewards C_star C_h k (t.val + 1) (by omega) (sourcePrefix control0 t.val z),
    stoppedStartCountThrough_prefix_factor rate rewards C_star C_h control0 t
      (t.val + 1) (by omega) z]

/-- The same kth C interval factors through the source history before the
current original control. The stop comparison is the accepted strict-prefix
first-bad test. -/
theorem kthCStratum_factor (control0 : ContinuousLearningRows.TimeControl p)
    (k : Fin (p.T + 1)) (t : Fin p.T) (z : SourceInput p) :
    kthCStratum rate rewards C_star C_h k t z =
      kthCStratum rate rewards C_star C_h k t (sourcePrefix control0 t.val z) := by
  unfold kthCStratum
  have hfirst := stoppedPhysicalTransferStartDate_le_prefix_factor
    rate rewards C_star C_h control0 k t z
  have hnext : t.val + 1 < kthNextStoppedStartDate rate rewards C_star C_h k z ↔
      t.val + 1 < kthNextStoppedStartDate rate rewards C_star C_h k
        (sourcePrefix control0 t.val z) := by
    unfold kthNextStoppedStartDate
    by_cases hk : k.val + 1 ≤ p.T
    · have hdate := stoppedPhysicalTransferStartDate_le_prefix_factor
        rate rewards C_star C_h control0 ⟨k.val + 1, by omega⟩ t z
      simpa [hk, not_le] using not_congr hdate
    · simp [hk]
  have hbad := ReferenceOriginalFirstBadStrictPrefix.firstBadDate_inclusive_prefix_factor
    rate rewards C_star C_h control0 t z
  simp only [hfirst, hnext, hbad]

/-- The literal kth stratum is measurable in the accepted original
pre-round filtration. The first-bad condition uses
`OriginalFirstBadStrictPrefix`, not a post-round overflow surrogate. -/
theorem kthCStratum_preRound_measurable
    (control0 : ContinuousLearningRows.TimeControl p) (k : Fin (p.T + 1))
    (t : Fin p.T) :
    MeasurableSet[sourcePrefixFiltration control0 (t.val + 1)]
      {z : SourceInput p | kthCStratum rate rewards C_star C_h k t z} := by
  let n := t.val + 1
  have hn : n ≤ p.T := by dsimp [n]; omega
  have hstart0 := ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate_isPreRoundStoppingTime
      rate rewards C_star C_h control0 k
  have hstart : MeasurableSet[sourcePrefixFiltration control0 n]
      {z : SourceInput p |
        ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
          rate rewards C_star C_h k z ≤ n} := by
    exact hstart0 n
  have hnext : MeasurableSet[sourcePrefixFiltration control0 n]
      {z : SourceInput p | n < kthNextStoppedStartDate rate rewards C_star C_h k z} := by
    by_cases hk : k.val + 1 ≤ p.T
    · have hnext0 := ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate_isPreRoundStoppingTime
          rate rewards C_star C_h control0 ⟨k.val + 1, by omega⟩
      have hle : MeasurableSet[sourcePrefixFiltration control0 n]
          {z : SourceInput p |
            ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
              rate rewards C_star C_h ⟨k.val + 1, by omega⟩ z ≤ n} := by
        exact hnext0 n
      have hevent : {z : SourceInput p | n <
          kthNextStoppedStartDate rate rewards C_star C_h k z} =
          {z | ¬ ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
          rate rewards C_star C_h ⟨k.val + 1, by omega⟩ z ≤ n} := by
        ext z
        simp [kthNextStoppedStartDate, hk, not_le]
      rw [hevent]
      exact hle.compl
    · have hset : {z : SourceInput p | n <
          kthNextStoppedStartDate rate rewards C_star C_h k z} = Set.univ := by
        ext z
        simp [kthNextStoppedStartDate, hk, hn]
      rw [hset]
      exact MeasurableSet.univ
  have hbad0 := ReferenceOriginalFirstBadStrictPrefix.noBadEventStrictlyBefore_strictPrefix_measurable
      rate rewards C_star C_h control0 t
  have hbad : MeasurableSet[sourcePrefixFiltration control0 n]
      {z : SourceInput p | n ≤
        ReferenceCompleteSignedFirstBadCalendar.firstBadDate rate rewards C_star C_h z} := by
    have hevent : {z : SourceInput p | n ≤
        ReferenceCompleteSignedFirstBadCalendar.firstBadDate rate rewards C_star C_h z} =
        {z | ReferenceOriginalFirstBadStrictPrefix.noBadEventStrictlyBefore
          rate rewards C_star C_h z t} := by
      ext z
      simpa [n] using
        (ReferenceOriginalFirstBadStrictPrefix.firstBadDate_prefix_iff
          rate rewards C_star C_h z t)
    rw [hevent]
    simpa [n] using hbad0
  have hevent : {z : SourceInput p | kthCStratum rate rewards C_star C_h k t z} =
      {z | ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
          rate rewards C_star C_h k z ≤ n} ∩
        {z | n < kthNextStoppedStartDate rate rewards C_star C_h k z} ∩
        {z | n ≤ ReferenceCompleteSignedFirstBadCalendar.firstBadDate
          rate rewards C_star C_h z} := by
    ext z
    simp [kthCStratum, n, and_assoc]
  rw [hevent]
  exact (hstart.inter hnext).inter hbad

/-- The kth-local OLD mask uses the incoming pending membership and the
checked OLD stage, and is zero outside the same stopped-start stratum. -/
def kthCOLDSet (k : Fin (p.T + 1)) (t : Fin p.T)
    (i : Fin (p.m - 1)) : Set (SourceInput p) :=
  {z | kthCStratum rate rewards C_star C_h k t z ∧
    ∃ pending, i ∈ pending ∧
      kthCPrechoiceStage rate rewards C_star C_h t i z =
        some (pending, .old)}

/-- The kth-local FORMED mask tests the same incoming pending set and requires
the actual current DOWN word in the checked stage. -/
def kthCFORMEDSet (k : Fin (p.T + 1)) (t : Fin p.T)
    (i : Fin (p.m - 1)) : Set (SourceInput p) :=
  {z | kthCStratum rate rewards C_star C_h k t z ∧
    ∃ pending, i ∈ pending ∧
      kthCPrechoiceStage rate rewards C_star C_h t i z =
        some (pending, .formed)}

private theorem kthCStagePendingSet_preRound_measurable
    (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T)
    (i : Fin (p.m - 1)) (stage : ReferenceFirstReplacementCollectionPredictableStages.TaskStage) :
    MeasurableSet[sourcePrefixFiltration control0 (t.val + 1)]
      {z : SourceInput p | ∃ pending, i ∈ pending ∧
        kthCPrechoiceStage rate rewards C_star C_h t i z = some (pending, stage)} := by
  classical
  let F := sourcePrefixFiltration control0 (t.val + 1)
  let : MeasurableSpace (SourceInput p) := F
  have hstage := kthCPrechoiceStage_preRound_measurable
    rate rewards C_star C_h control0 t i
  have hfiber (pending : Finset (Fin (p.m - 1))) :
      MeasurableSet[F]
        {z : SourceInput p | kthCPrechoiceStage rate rewards C_star C_h t i z =
          some (pending, stage)} := by
    change MeasurableSet[F]
      (kthCPrechoiceStage rate rewards C_star C_h t i ⁻¹' {some (pending, stage)})
    exact hstage (measurableSet_singleton (some (pending, stage)))
  have hevent : {z : SourceInput p | ∃ pending, i ∈ pending ∧
        kthCPrechoiceStage rate rewards C_star C_h t i z = some (pending, stage)} =
      ⋃ pending : Finset (Fin (p.m - 1)),
        {z : SourceInput p | i ∈ pending ∧
          kthCPrechoiceStage rate rewards C_star C_h t i z = some (pending, stage)} := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
  rw [hevent]
  exact MeasurableSet.iUnion fun pending => by
    by_cases hi : i ∈ pending
    · simpa [hi] using hfiber pending
    · simp [hi]

/-- The OLD mask is measurable in the accepted pre-round field. -/
theorem kthCOLDSet_preRound_measurable
    (control0 : ContinuousLearningRows.TimeControl p) (k : Fin (p.T + 1))
    (t : Fin p.T) (i : Fin (p.m - 1)) :
    MeasurableSet[sourcePrefixFiltration control0 (t.val + 1)]
      (kthCOLDSet rate rewards C_star C_h k t i) := by
  change MeasurableSet[sourcePrefixFiltration control0 (t.val + 1)]
    ({z | kthCStratum rate rewards C_star C_h k t z} ∩
      {z | ∃ pending, i ∈ pending ∧
        kthCPrechoiceStage rate rewards C_star C_h t i z = some (pending, .old)})
  exact (kthCStratum_preRound_measurable rate rewards C_star C_h control0 k t).inter
    (kthCStagePendingSet_preRound_measurable rate rewards C_star C_h control0 t i .old)

/-- The FORMED mask is measurable in the same accepted pre-round field. -/
theorem kthCFORMEDSet_preRound_measurable
    (control0 : ContinuousLearningRows.TimeControl p) (k : Fin (p.T + 1))
    (t : Fin p.T) (i : Fin (p.m - 1)) :
    MeasurableSet[sourcePrefixFiltration control0 (t.val + 1)]
      (kthCFORMEDSet rate rewards C_star C_h k t i) := by
  change MeasurableSet[sourcePrefixFiltration control0 (t.val + 1)]
    ({z | kthCStratum rate rewards C_star C_h k t z} ∩
      {z | ∃ pending, i ∈ pending ∧
        kthCPrechoiceStage rate rewards C_star C_h t i z = some (pending, .formed)})
  exact (kthCStratum_preRound_measurable rate rewards C_star C_h control0 k t).inter
    (kthCStagePendingSet_preRound_measurable rate rewards C_star C_h control0 t i .formed)

/-- The whole-original-source positive DOWN readout restricted to the kth
OLD/pending mask. -/
def kthCOLDReadout (k : Fin (p.T + 1)) (t : Fin p.T)
    (i : Fin (p.m - 1)) (z : SourceInput p) : ℝ :=
  (kthCOLDSet rate rewards C_star C_h k t i).indicator
    (ReferenceFirstCollectionDownConditionalService.actualFirstCollectionDownReadout
      (rate := rate) rewards C_star C_h i t) z

/-- The whole-original-source positive UP readout restricted to the kth
FORMED/pending mask. -/
def kthCFORMEDReadout (k : Fin (p.T + 1)) (t : Fin p.T)
    (i : Fin (p.m - 1)) (z : SourceInput p) : ℝ :=
  (kthCFORMEDSet rate rewards C_star C_h k t i).indicator
    (ReferenceFirstCollectionUpConditionalService.actualFirstCollectionUpReadout
      (rate := rate) rewards C_star C_h i t) z

/-- The masked actual kth-C service readout on the unchanged original-source
law. -/
def kthCSourceReadout (k : Fin (p.T + 1)) (t : Fin p.T)
    (i : Fin (p.m - 1)) (z : SourceInput p) : ℝ :=
  kthCOLDReadout rate rewards C_star C_h k t i z +
    kthCFORMEDReadout rate rewards C_star C_h k t i z

/-- Fresh whole-control sections of the same actual DOWN/UP readouts, with
the literal kth stratum and incoming pending masks. -/
def kthCSourceFreshSection (k : Fin (p.T + 1)) (t : Fin p.T)
    (i : Fin (p.m - 1)) (control0 : ContinuousLearningRows.TimeControl p)
    (z : SourceInput p) : ℝ :=
  (kthCOLDSet rate rewards C_star C_h k t i).indicator
      (ReferenceFirstCollectionDownConditionalService.actualFirstCollectionDownFreshSection
        (rate := rate) rewards C_star C_h control0 i t) z +
    (kthCFORMEDSet rate rewards C_star C_h k t i).indicator
      (ReferenceFirstCollectionUpConditionalService.actualFirstCollectionUpFreshSection
        (rate := rate) rewards C_star C_h control0 i t) z

/-- Integrability of the masked kth OLD/FORMED readouts under the original
private source law. -/
theorem integrable_kthCSourceReadout
    (control0 : ContinuousLearningRows.TimeControl p) (k : Fin (p.T + 1))
    (t : Fin p.T) (i : Fin (p.m - 1)) :
    Integrable (kthCSourceReadout rate rewards C_star C_h k t i)
      (BootstrapPrivateRoundStreams.sourceInputLaw p) := by
  let μ := BootstrapPrivateRoundStreams.sourceInputLaw p
  let oldSet := kthCOLDSet rate rewards C_star C_h k t i
  let formedSet := kthCFORMEDSet rate rewards C_star C_h k t i
  let downReadout :=
    ReferenceFirstCollectionDownConditionalService.actualFirstCollectionDownReadout
      (rate := rate) rewards C_star C_h i t
  let upReadout :=
    ReferenceFirstCollectionUpConditionalService.actualFirstCollectionUpReadout
      (rate := rate) rewards C_star C_h i t
  have hF := kthCOLDSet_preRound_measurable rate rewards C_star C_h control0 k t i
  have hG := kthCFORMEDSet_preRound_measurable rate rewards C_star C_h control0 k t i
  have hle : sourcePrefixFiltration control0 (t.val + 1) ≤
      (inferInstance : MeasurableSpace (SourceInput p)) := by
    rw [ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration_round]
    exact (ReferenceSourceCurrentControlFreshness.measurable_c_t control0 t).comap_le
  have hOldAmbient := hle oldSet hF
  have hFormedAmbient := hle formedSet hG
  have hDown : Integrable downReadout μ :=
    ReferenceFirstCollectionDownConditionalService.integrable_actualFirstCollectionDownReadout
      (rate := rate) rewards C_star C_h i t
  have hUp : Integrable upReadout μ :=
    ReferenceFirstCollectionUpConditionalService.integrable_actualFirstCollectionUpReadout
      (rate := rate) rewards C_star C_h i t
  change Integrable (oldSet.indicator downReadout + formedSet.indicator upReadout) μ
  exact (hDown.indicator hOldAmbient).add (hUp.indicator hFormedAmbient)

/-- Integrability of the masked fresh sections follows from the accepted
whole-control DOWN/UP section bounds. -/
theorem integrable_kthCSourceFreshSection
    (control0 : ContinuousLearningRows.TimeControl p) (k : Fin (p.T + 1))
    (t : Fin p.T) (i : Fin (p.m - 1)) :
    Integrable (kthCSourceFreshSection rate rewards C_star C_h k t i control0)
      (BootstrapPrivateRoundStreams.sourceInputLaw p) := by
  let μ := BootstrapPrivateRoundStreams.sourceInputLaw p
  let oldSet := kthCOLDSet rate rewards C_star C_h k t i
  let formedSet := kthCFORMEDSet rate rewards C_star C_h k t i
  let downSection :=
    ReferenceFirstCollectionDownConditionalService.actualFirstCollectionDownFreshSection
      (rate := rate) rewards C_star C_h control0 i t
  let upSection :=
    ReferenceFirstCollectionUpConditionalService.actualFirstCollectionUpFreshSection
      (rate := rate) rewards C_star C_h control0 i t
  have hF := kthCOLDSet_preRound_measurable rate rewards C_star C_h control0 k t i
  have hG := kthCFORMEDSet_preRound_measurable rate rewards C_star C_h control0 k t i
  have hle : sourcePrefixFiltration control0 (t.val + 1) ≤
      (inferInstance : MeasurableSpace (SourceInput p)) := by
    rw [ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration_round]
    exact (ReferenceSourceCurrentControlFreshness.measurable_c_t control0 t).comap_le
  have hOldAmbient := hle oldSet hF
  have hFormedAmbient := hle formedSet hG
  have hDown : Integrable downSection μ :=
    ReferenceFirstCollectionDownConditionalService.integrable_actualFirstCollectionDownFreshSection
      (rate := rate) rewards C_star C_h control0 i t
  have hUp : Integrable upSection μ :=
    ReferenceFirstCollectionUpConditionalService.integrable_actualFirstCollectionUpFreshSection
      (rate := rate) rewards C_star C_h control0 i t
  change Integrable (oldSet.indicator downSection + formedSet.indicator upSection) μ
  exact (hDown.indicator hOldAmbient).add (hUp.indicator hFormedAmbient)

/-- Under the unchanged original source law, the kth-local masked actual
readout has conditional expectation at the exact pre-round source field given
by the corresponding masked whole-current-control fresh sections. -/
theorem kthCSourceReadout_condExp
    (control0 : ContinuousLearningRows.TimeControl p) (k : Fin (p.T + 1))
    (t : Fin p.T) (i : Fin (p.m - 1)) :
    (BootstrapPrivateRoundStreams.sourceInputLaw p)[
      kthCSourceReadout rate rewards C_star C_h k t i |
        sourcePrefixFiltration control0 (t.val + 1)] =ᵐ[
          BootstrapPrivateRoundStreams.sourceInputLaw p]
      kthCSourceFreshSection rate rewards C_star C_h k t i control0 := by
  let μ := BootstrapPrivateRoundStreams.sourceInputLaw p
  let F := sourcePrefixFiltration control0 (t.val + 1)
  let m := ReferenceSourceCurrentControlFreshness.m_t p control0 t
  let oldSet := kthCOLDSet rate rewards C_star C_h k t i
  let formedSet := kthCFORMEDSet rate rewards C_star C_h k t i
  let downReadout :=
    ReferenceFirstCollectionDownConditionalService.actualFirstCollectionDownReadout
      (rate := rate) rewards C_star C_h i t
  let upReadout :=
    ReferenceFirstCollectionUpConditionalService.actualFirstCollectionUpReadout
      (rate := rate) rewards C_star C_h i t
  let downSection :=
    ReferenceFirstCollectionDownConditionalService.actualFirstCollectionDownFreshSection
      (rate := rate) rewards C_star C_h control0 i t
  let upSection :=
    ReferenceFirstCollectionUpConditionalService.actualFirstCollectionUpFreshSection
      (rate := rate) rewards C_star C_h control0 i t
  have hF : F = m := by
    dsimp [F, ReferenceSourceCurrentControlFreshness.m_t,
      ReferenceSourceCurrentControlFreshness.c_t]
    rw [ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration_round]
    rfl
  have hOld : MeasurableSet[m] oldSet := by
    rw [← hF]
    exact kthCOLDSet_preRound_measurable rate rewards C_star C_h control0 k t i
  have hFormed : MeasurableSet[m] formedSet := by
    rw [← hF]
    exact kthCFORMEDSet_preRound_measurable rate rewards C_star C_h control0 k t i
  have hleF : F ≤ (Prod.instMeasurableSpace : MeasurableSpace (SourceInput p)) :=
    (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).le'
      (t.val + 1)
  have hle : m ≤ (Prod.instMeasurableSpace : MeasurableSpace (SourceInput p)) := hF ▸ hleF
  have hOldAmbient := hle oldSet hOld
  have hFormedAmbient := hle formedSet hFormed
  have hDownInt : Integrable downReadout μ :=
    ReferenceFirstCollectionDownConditionalService.integrable_actualFirstCollectionDownReadout
      (rate := rate) rewards C_star C_h i t
  have hUpInt : Integrable upReadout μ :=
    ReferenceFirstCollectionUpConditionalService.integrable_actualFirstCollectionUpReadout
      (rate := rate) rewards C_star C_h i t
  have hOldInt : Integrable (oldSet.indicator downReadout) μ :=
    hDownInt.indicator hOldAmbient
  have hFormedInt : Integrable (formedSet.indicator upReadout) μ :=
    hUpInt.indicator hFormedAmbient
  have hAdd : μ[kthCSourceReadout rate rewards C_star C_h k t i | m] =ᵐ[μ]
      μ[oldSet.indicator downReadout | m] + μ[formedSet.indicator upReadout | m] := by
    change μ[(oldSet.indicator downReadout) +
      (formedSet.indicator upReadout) | m] =ᵐ[μ] _
    exact MeasureTheory.condExp_add hOldInt hFormedInt m
  have hOldInd := MeasureTheory.condExp_indicator hDownInt hOld
  have hFormedInd := MeasureTheory.condExp_indicator hUpInt hFormed
  have hDownCE :=
    ReferenceFirstCollectionDownConditionalService.actual_first_collection_down_condExp
      (rate := rate) rewards C_star C_h control0 i t
  have hUpCE :=
    ReferenceFirstCollectionUpConditionalService.actual_first_collection_up_condExp
      (rate := rate) rewards C_star C_h control0 i t
  filter_upwards [hAdd, hOldInd, hFormedInd, hDownCE, hUpCE]
    with z hAdd hOldInd hFormedInd hDownCE hUpCE
  have hOldSection : oldSet.indicator (μ[downReadout | m]) z =
      oldSet.indicator downSection z := by
    by_cases hz : z ∈ oldSet
    · simpa only [Set.indicator_of_mem hz] using hDownCE
    · simp [Set.indicator_of_notMem hz]
  have hFormedSection : formedSet.indicator (μ[upReadout | m]) z =
      formedSet.indicator upSection z := by
    by_cases hz : z ∈ formedSet
    · simpa only [Set.indicator_of_mem hz] using hUpCE
    · simp [Set.indicator_of_notMem hz]
  calc
    μ[kthCSourceReadout rate rewards C_star C_h k t i | m] z =
        (μ[oldSet.indicator downReadout | m] +
          μ[formedSet.indicator upReadout | m]) z := hAdd
    _ = oldSet.indicator (μ[downReadout | m]) z +
        formedSet.indicator (μ[upReadout | m]) z := by
      change μ[oldSet.indicator downReadout | m] z +
        μ[formedSet.indicator upReadout | m] z = _
      rw [hOldInd, hFormedInd]
    _ = oldSet.indicator downSection z + formedSet.indicator upSection z := by
      rw [hOldSection, hFormedSection]

/-- On a present actual source record, the optional prechoice is projected
from that record's lossless incoming coordinator code. -/
theorem kthCPrechoiceData_actualRecord
    (t : Fin p.T) (z : SourceInput p)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t z = some r) :
    kthCPrechoiceData rate rewards C_star C_h t z =
      kthCPrechoiceDataFromCoordinatorCode rate t
        (ReferenceActivePhysicalStepMeasurability.encodeCoordinator
          r.input.state.coordinator) := by
  rw [kthCPrechoiceData, ReferenceSourcePrefixHistoryFiltration.incoming, hr]
  simp [kthCPrechoiceDataFromIncomingCode,
    ReferenceActivePhysicalStepMeasurability.encodeState]

private theorem completeSuffix_get_time_nat
    (z : SourceInput p) (n : ℕ)
    (hn : n < (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length) :
    ((ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).get ⟨n, hn⟩).input.time.val =
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + n := by
  have htimes := ReferenceCompletePhysicalHistory.completeSuffixRecords_time_values
    rate z rewards C_star C_h
  have hget := congrArg (fun xs : List ℕ => xs[n]?) htimes
  have hn' : n < p.T - ReferenceCompletePhysicalHistory.physicalStart
      rate z rewards C_star C_h := by
    simpa only [ReferenceCompletePhysicalHistory.completeSuffixRecords_length] using hn
  have hrange := List.getElem?_range'
    (s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
    (step := 1) hn'
  simpa [ReferenceActivePhysicalHorizon.calendar, List.getElem?_map,
    List.getElem?_eq_getElem hn, hrange] using hget

private theorem actualRecord_suffixIndex
    (t : Fin p.T) (z : SourceInput p)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t z = some r) :
    ∃ k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h).length,
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[k.val]'k.isLt = r ∧ r.input.time = t := by
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  unfold ReferenceSourcePrefixHistoryFiltration.actualRecord at hr
  split at hr
  · obtain ⟨hk, he⟩ := List.getElem?_eq_some_iff.mp hr
    let k : Fin R.length := ⟨t.val - s, hk⟩
    have hget : R[k.val]'k.isLt = r := he
    have htime := completeSuffix_get_time_nat rate rewards C_star C_h z k.val k.isLt
    change (R[k.val]'k.isLt).input.time.val = s + k.val at htime
    rw [hget] at htime
    have htimeFin : r.input.time = t := by
      apply Fin.ext
      dsimp [k, s] at htime
      omega
    exact ⟨k, by simpa [R] using hget, htimeFin⟩
  · cases hr

/-- A present record whose incoming collection ledger has pending followers
has the same literal collection choice as the accepted complete-suffix
choice-domain producer. The stored payload, pending set, cutoff, and actual
prechoice fields agree in that record. -/
theorem kthCPrechoiceData_actualCollectionChoice_nonempty
    (t : Fin p.T) (z : SourceInput p)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t z = some r)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (saved : Option (Fin p.T × Bool))
    (hstate : r.input.state.coordinator = .collection payload ledger saved)
    (hpending : ledger.pending.Nonempty) :
    ∃ c : ReferenceCollectionSegmentExtraction.Choice rate,
      ReferenceCollectionSegmentExtraction.choice r.input = some c ∧
      c.payload = payload ∧ c.preLedger.pending = ledger.pending ∧
      c.preLedger.cutoff = ledger.cutoff ∧ c.initializer = none ∧
      ∃ data : KthCPrechoiceData rate,
        kthCPrechoiceData rate rewards C_star C_h t z = some data ∧
        data.1 = c.payload ∧ data.2.1 = c.preLedger.pending ∧
        data.2.2.1 = c.preLedger.cutoff := by
  obtain ⟨k, hget, _htime⟩ := actualRecord_suffixIndex rate rewards C_star C_h t z r hr
  have hstate' :
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[k.val]'k.isLt).input.state.coordinator =
        .collection payload ledger saved := by
    rw [hget]
    exact hstate
  obtain ⟨u, hu, core, scores, started, hstart, hframe, choiceInputs,
    snapshot, boundary, hdispatch, hchoiceInputs, hclockStarted, harm,
    c, hchoice, hc, hvalid, hchoiceArm, o, startedLedger, finished, bank,
    clockFinished, hobserve, hfinish⟩ :=
    ReferenceCompleteContinuingCollectionChoiceDomains.complete_nonempty_continuing_collection_choice_domains
      rate rewards C_star C_h z k payload ledger saved hstate' hpending
  have hdata : kthCPrechoiceData rate rewards C_star C_h t z =
      some (payload, (ledger.pending,
        (ledger.cutoff, kthCollectionCoordinatorCode rate
          (payload, ledger, saved)))) := by
    rw [kthCPrechoiceData_actualRecord rate rewards C_star C_h t z r hr]
    simp [kthCPrechoiceDataFromCoordinatorCode,
      ReferenceActivePhysicalStepMeasurability.encodeCoordinator, hstate, hpending,
      kthCollectionCoordinatorCode]
  have hpayload : c.payload = payload := by rw [hc]
  have hledger : c.preLedger = ledger := by rw [hc]
  have hinitializer : c.initializer = none := by rw [hc]
  have hchoiceR : ReferenceCollectionSegmentExtraction.choice r.input = some c := by
    simpa only [hget] using hchoice
  refine ⟨c, hchoiceR, hpayload, ?_, ?_, hinitializer, ?_⟩
  · rw [hledger]
  · rw [hledger]
  · refine ⟨(payload, (ledger.pending,
      (ledger.cutoff, kthCollectionCoordinatorCode rate (payload, ledger, saved)))),
      hdata, ?_, ?_, ?_⟩
    · rw [hpayload]
    · rw [hledger]
    · rw [hledger]

/-- When a present incoming LIVE coordinator actually makes a collection
choice, the accepted complete-suffix cutoff theorem identifies that choice
with the same payload and universal initialization pending set read here. -/
theorem kthCPrechoiceData_actualLiveCollectionChoice
    (t : Fin p.T) (z : SourceInput p)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t z = some r)
    (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
    (base : Fin (p.m - 1) → ℕ)
    (hstate : r.input.state.coordinator = .live registers owned base)
    (c : ReferenceCollectionSegmentExtraction.Choice rate)
    (hchoice : ReferenceCollectionSegmentExtraction.choice r.input = some c) :
    ∃ data : KthCPrechoiceData rate,
      kthCPrechoiceData rate rewards C_star C_h t z = some data ∧
      data.1 = c.payload ∧ data.2.1 = c.preLedger.pending ∧
      data.2.2.1 = c.preLedger.cutoff ∧
      ∃ initializer, c.initializer = some initializer := by
  obtain ⟨k, hget, htime⟩ := actualRecord_suffixIndex rate rewards C_star C_h t z r hr
  have hstate' :
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[k.val]'k.isLt).input.state.coordinator =
        .live registers owned base := by
    rw [hget]
    exact hstate
  let x := (ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate z rewards C_star C_h)[k.val]'k.isLt |>.input
  let live := ReferenceActivePhysicalStepMeasurability.encodeLive registers owned base
  let current := ReferenceActivePhysicalStep.liveInput x registers owned base
  have hcutoff := Bandits.Support.complete_live_cutoff_post_choice
    rate rewards C_star C_h z k registers owned base hstate'
  dsimp only at hcutoff
  rcases hcutoff with ⟨hprepared, hbranch⟩
  have hchoiceX : ReferenceCollectionSegmentExtraction.choice x = some c := by
    simpa [x, hget] using hchoice
  have hselection :
      (ReferenceActivePhysicalStep.prepare x).coordinator.selection ≠ none := by
    intro hnone
    simp [ReferenceCollectionSegmentExtraction.choice, hnone] at hchoiceX
  have hchoiceCut :
      ReferenceCollectionSegmentExtraction.choiceOfCut
        (ReferenceActivePhysicalStep.prepare x).coordinator = some c := by
    simpa [ReferenceCollectionSegmentExtraction.choice, hselection] using hchoiceX
  rw [hprepared] at hchoiceCut
  change ReferenceCollectionSegmentExtraction.choiceOfCut
      (.live registers owned base (CoordinatorRoundDispatch.dispatchLive current)) = some c
    at hchoiceCut
  cases hd : CoordinatorRoundDispatch.dispatchLive current with
  | cutoffChosen dispatched hstart ledger hinitialization hledger hdomains
      hclock hpending hassignment selection =>
      have hfacts := by simpa [current, x, hd] using hbranch
      rcases hfacts with ⟨hcommand, _, _, _, _, _, _, hledgerCutoff, _,
        hledgerPending, _, _, _, _, _, _⟩
      have hc : c =
          ⟨registers.payload,
            ReferenceActivePhysicalStep.sharedLedger ledger,
            dispatched.startResult,
            (ReferenceActivePhysicalStep.liveRegistersAt registers x.time).complementWeights,
            some (ReferenceCollectionSegmentExtraction.cutoffInitializer
              (ReferenceActivePhysicalStep.liveRegistersAt registers x.time)
              (ReferenceActivePhysicalStep.liveOwnedAt registers owned x.time) base x.time)⟩ := by
        have heq : some
            ⟨registers.payload,
              ReferenceActivePhysicalStep.sharedLedger ledger,
              dispatched.startResult,
              (ReferenceActivePhysicalStep.liveRegistersAt registers x.time).complementWeights,
              some (ReferenceCollectionSegmentExtraction.cutoffInitializer
                (ReferenceActivePhysicalStep.liveRegistersAt registers x.time)
                (ReferenceActivePhysicalStep.liveOwnedAt registers owned x.time) base x.time)⟩ =
              some c := by
          simpa [ReferenceCollectionSegmentExtraction.choiceOfCut, hd] using hchoiceCut
        exact Option.some.inj heq.symm
      have hcommand' : dispatched.startResult.ledgerCommand = some (.initializeAt t) := by
        simpa [x, hget, htime] using hcommand
      have hledgerCutoff' : ledger.cutoff = t.val + 1 := by
        simpa [x, hget, htime] using hledgerCutoff
      have hstartCode :
          CoordinatorPhaseClock.startRound p rate.eta.val t
            ⟨live.clockSigma, live.clockCutoff, live.clockBoundary, live.clockProposal⟩
            live.pending = .ok dispatched.startResult := by
        simpa [current, x, live, ReferenceActivePhysicalStep.liveInput,
          ReferenceActivePhysicalStep.liveRegistersAt,
          ReferenceActivePhysicalStepMeasurability.encodeLive,
          CoordinatorLiveChoiceRecorderStep.Registers.clockPending, hget, htime] using hstart
      have hissues : liveIssuesInitializeAt rate t live = true := by
        unfold liveIssuesInitializeAt
        rw [hstartCode]
        simp [hcommand']
      have hdata : kthCPrechoiceData rate rewards C_star C_h t z =
          some (registers.payload,
            ((Finset.univ : Finset (Fin (p.m - 1))),
              (t.val + 1,
                kthLiveCoordinatorCode rate (registers.payload, live)))) := by
        rw [kthCPrechoiceData_actualRecord rate rewards C_star C_h t z r hr]
        simp [kthCPrechoiceDataFromCoordinatorCode,
          ReferenceActivePhysicalStepMeasurability.encodeCoordinator, hstate, live,
          hissues, kthLiveCoordinatorCode]
      refine ⟨(registers.payload,
        ((Finset.univ : Finset (Fin (p.m - 1))),
          (t.val + 1, kthLiveCoordinatorCode rate (registers.payload, live)))),
        hdata, ?_, ?_, ?_, ?_⟩
      · rw [hc]
      · rw [hc]
        simp [ReferenceActivePhysicalStep.sharedLedger, hledgerPending]
      · rw [hc]
        simp [ReferenceActivePhysicalStep.sharedLedger, hledgerCutoff']
      · refine ⟨ReferenceCollectionSegmentExtraction.cutoffInitializer
          (ReferenceActivePhysicalStep.liveRegistersAt registers x.time)
          (ReferenceActivePhysicalStep.liveOwnedAt registers owned x.time) base x.time, ?_⟩
        rw [hc]
  | continuingChosen _ _ _ _ =>
      simp [ReferenceCollectionSegmentExtraction.choiceOfCut, current, x, hd] at hchoiceCut
  | clockFailure _ _ =>
      simp [ReferenceCollectionSegmentExtraction.choiceOfCut, current, x, hd] at hchoiceCut
  | initializerFailure _ _ _ _ =>
      simp [ReferenceCollectionSegmentExtraction.choiceOfCut, current, x, hd] at hchoiceCut
  | localFailure _ _ _ =>
      simp [ReferenceCollectionSegmentExtraction.choiceOfCut, current, x, hd] at hchoiceCut

/-- On an actual incoming LIVE record with no collection choice, the accepted
phase-exhaustion and live-dispatch results force the unchanged live START
branch, whose command is not `initializeAt`; hence the optional C data is
literally absent. -/
theorem kthCPrechoiceData_liveNoCollectionChoice
    (t : Fin p.T) (z : SourceInput p)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t z = some r)
    (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
    (base : Fin (p.m - 1) → ℕ)
    (hstate : r.input.state.coordinator = .live registers owned base)
    (hchoice : ReferenceCollectionSegmentExtraction.choice r.input = none) :
    kthCPrechoiceData rate rewards C_star C_h t z = none := by
  obtain ⟨k, hget, htime⟩ := actualRecord_suffixIndex rate rewards C_star C_h t z r hr
  have hstate' :
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[k.val]'k.isLt).input.state.coordinator =
        .live registers owned base := by
    rw [hget]
    exact hstate
  let x := (ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate z rewards C_star C_h)[k.val]'k.isLt |>.input
  let live := ReferenceActivePhysicalStepMeasurability.encodeLive registers owned base
  let current := ReferenceActivePhysicalStep.liveInput x registers owned base
  have hcutoff := Bandits.Support.complete_live_cutoff_post_choice
    rate rewards C_star C_h z k registers owned base hstate'
  dsimp only at hcutoff
  rcases hcutoff with ⟨hprepared, _⟩
  have hexhaustion :=
    (ReferenceCompleteCoordinatorPhaseExhaustion.complete_coordinator_phase_exhaustion
      rate rewards C_star C_h z).1 k
  have hout :
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[k.val]'k.isLt).output.preparation =
        ReferenceActivePhysicalStep.prepare x := by
    rw [((ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[k.val]'k.isLt).output_eq]
    rfl
  have hselection : (ReferenceActivePhysicalStep.prepare x).coordinator.selection ≠ none := by
    rw [← hout]
    exact hexhaustion.2.1
  have hchoiceX : ReferenceCollectionSegmentExtraction.choice x = none := by
    simpa [x, hget] using hchoice
  have hchoiceCut :
      ReferenceCollectionSegmentExtraction.choiceOfCut
        (ReferenceActivePhysicalStep.prepare x).coordinator = none := by
    by_cases hs : (ReferenceActivePhysicalStep.prepare x).coordinator.selection = none
    · exact False.elim (hselection hs)
    · simpa [ReferenceCollectionSegmentExtraction.choice, hs] using hchoiceX
  rw [hprepared] at hchoiceCut
  change ReferenceCollectionSegmentExtraction.choiceOfCut
      (.live registers owned base (CoordinatorRoundDispatch.dispatchLive current)) = none
    at hchoiceCut
  cases hd : CoordinatorRoundDispatch.dispatchLive current with
  | cutoffChosen dispatched hstart ledger hinitialization hledger hdomains
      hclock hpending hassignment selection =>
      have hfalse : False := by
        simp [ReferenceCollectionSegmentExtraction.choiceOfCut, hd] at hchoiceCut
      exact hfalse.elim
  | continuingChosen dispatched hstart continuation selection =>
      have hliveDomains :=
        ReferenceCompleteLiveChoiceDomains.complete_live_dispatch_choice_exists
          rate rewards C_star C_h z k registers owned base hstate'
      dsimp only at hliveDomains
      rcases hliveDomains with ⟨_, hdomain⟩
      have hdomain' := by simpa [current, x, hd] using hdomain
      have hclockU : dispatched.startResult.clock.u = none := hdomain'.2.1
      have hnoInitialize :
          dispatched.startResult.ledgerCommand ≠ some (.initializeAt x.time) := by
        intro hcommand
        have hclockShape :=
          CoordinatorStartRoundCutoffDispatch.startRound_initializeAt_shape
            (ReferenceActivePhysicalStep.liveRegistersAt registers x.time)
            dispatched.startResult
            (by simpa [current, x, ReferenceActivePhysicalStep.liveInput,
              ReferenceActivePhysicalStep.liveRegistersAt] using hstart)
            hcommand
        have hsome : dispatched.startResult.clock.u = some x.time := by
          rw [hclockShape.1]
          rfl
        rw [hclockU] at hsome
        cases hsome
      have hstartCode :
          CoordinatorPhaseClock.startRound p rate.eta.val t
            ⟨live.clockSigma, live.clockCutoff, live.clockBoundary, live.clockProposal⟩
            live.pending = .ok dispatched.startResult := by
        simpa [current, x, live, ReferenceActivePhysicalStep.liveInput,
          ReferenceActivePhysicalStep.liveRegistersAt,
          ReferenceActivePhysicalStepMeasurability.encodeLive,
          CoordinatorLiveChoiceRecorderStep.Registers.clockPending, hget, htime] using hstart
      have hissues : liveIssuesInitializeAt rate t live = false := by
        unfold liveIssuesInitializeAt
        rw [hstartCode]
        have hnoInitializeAtT :
            dispatched.startResult.ledgerCommand ≠ some (.initializeAt t) := by
          simpa [x, hget, htime] using hnoInitialize
        simp [hnoInitializeAtT]
      rw [kthCPrechoiceData_actualRecord rate rewards C_star C_h t z r hr]
      simp [kthCPrechoiceDataFromCoordinatorCode,
        ReferenceActivePhysicalStepMeasurability.encodeCoordinator, hstate, live,
        hissues]
  | clockFailure _ _ =>
      simp [ReferenceActivePhysicalStep.DispatchCut.selection, current, x, hprepared, hd]
        at hselection
  | initializerFailure _ _ _ _ =>
      simp [ReferenceActivePhysicalStep.DispatchCut.selection, current, x, hprepared, hd]
        at hselection
  | localFailure _ _ _ =>
      simp [ReferenceActivePhysicalStep.DispatchCut.selection, current, x, hprepared, hd]
        at hselection

/-- A later-installation dispatch is not a collection choice at this record. -/
private theorem collectionChoice_none_of_laterChosen
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (hlater : ReferenceCollectionPhaseHistory.laterChosen x = true) :
    ReferenceCollectionSegmentExtraction.choice x = none := by
  classical
  unfold ReferenceCollectionPhaseHistory.laterChosen at hlater
  by_cases hselection : (ReferenceActivePhysicalStep.prepare x).coordinator.selection = none
  · simp [ReferenceCollectionSegmentExtraction.choice, hselection]
  · cases hcoord : (ReferenceActivePhysicalStep.prepare x).coordinator with
    | first outcome => simp [hcoord] at hlater
    | live registers owned base outcome => simp [hcoord] at hlater
    | collection payload ledger clock cutoff outcome =>
        cases outcome <;>
          simp [ReferenceCollectionSegmentExtraction.choice, hcoord,
            ReferenceCollectionSegmentExtraction.choiceOfCut] at hlater ⊢
    | invalidCollectionCutoff => simp [hcoord] at hlater
    | dagger => simp [hcoord] at hlater

/-- An empty incoming collection set carries no C prechoice data. The
accepted actual-index equivalence identifies this exact empty-pending branch
with the later installation. -/
theorem kthCPrechoiceData_emptyCollection_laterChosen
    (t : Fin p.T) (z : SourceInput p)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t z = some r)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (saved : Option (Fin p.T × Bool))
    (hstate : r.input.state.coordinator = .collection payload ledger saved)
    (hempty : ledger.pending = ∅) :
    kthCPrechoiceData rate rewards C_star C_h t z = none ∧
      ReferenceCollectionSegmentExtraction.choice r.input = none ∧
      ReferenceCollectionPhaseHistory.laterChosen r.input = true := by
  obtain ⟨k, hget, _htime⟩ := actualRecord_suffixIndex rate rewards C_star C_h t z r hr
  have hstate' :
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[k.val]'k.isLt).input.state.coordinator =
        .collection payload ledger saved := by
    rw [hget]
    exact hstate
  have hdata : kthCPrechoiceData rate rewards C_star C_h t z = none := by
    rw [kthCPrechoiceData_actualRecord rate rewards C_star C_h t z r hr]
    simp [kthCPrechoiceDataFromCoordinatorCode,
      ReferenceActivePhysicalStepMeasurability.encodeCoordinator, hstate, hempty]
  have hlater :=
    (ReferencePostReplacementCollectionHandoverSourcePrefix.actual_collection_laterChosen_iff_pending_empty
      rate rewards C_star C_h z k payload ledger saved hstate').2 hempty
  have hlaterR : ReferenceCollectionPhaseHistory.laterChosen r.input = true := by
    simpa [hget] using hlater
  exact ⟨hdata, collectionChoice_none_of_laterChosen rate r.input hlaterR, hlaterR⟩

end Bandits.Support.ReferenceOriginalKthCollectionSourceSections

end
