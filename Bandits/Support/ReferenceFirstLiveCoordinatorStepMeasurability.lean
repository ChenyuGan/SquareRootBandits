/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstDispatchMeasurability
public import Bandits.Support.ReferenceLiveDispatchOutputMeasurability
public import Bandits.Support.ReferenceCollectionTailComposition
public import Bandits.Support.ReferenceActiveLiveTailMeasurability
public import Bandits.Support.ReferenceActivePhysicalStepMeasurability

/-!
# The FIRST/LIVE physical choice cut and coordinator continuation

Sources: `sources/zip4/manuscript/06_interruptions.tex:40-69,235-296`,
`sources/zip4/manuscript/appendix_a_local_protocol.tex:6-14,28-64`, and
`sources/zip4/manuscript/08_main_theorem.tex:29-42`.

The domain consists of original active round inputs, restricted only by the
incoming coordinator tag. Whole public rows, the original selected index,
the entire reward table, and all follower stores remain present. The only common parameters are `p : ConstructorDimensions.Parameters` and the
existing `rate : ReferenceActivePhysicalStep.RateInput p`. The original round
contains the entire state, `Fin (M p) → CompleteRow p`, selected `Fin (M p)`,
`Fin p.T`, the entire `GridRewardTable p`, and its original proof
`∀ i, (state.activations i).val ≤ time.val + 1`. Final measurable exports add
only the indicated incoming-tag subtype; they have no supplied output, domain,
success, reachability, score-truth, or measurable-tail premise. The sole generic
private helpers `measurable_actions` and `measurable_feedback` explicitly take
a measurable original-round map and, respectively, a measurable coordinator
arm or actual profile. All these inputs are produced on each tag fiber.

This is internal deterministic infrastructure, not a manuscript theorem or a full
successor/follower STEP measurability result.

Admission records are absolute files in
`private-audit-archive/`:
`turn-00144-dependency-evidence.json`, `turn-00144-publication.json`, and
`delta-verified-dependencies.json`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions

namespace Bandits.Support.ReferenceFirstLiveCoordinatorStepMeasurability


variable {p : Parameters} {rate : ReferenceActivePhysicalStep.RateInput p}

/-- The original incoming FIRST tag fiber. -/
def firstSet : Set (ReferenceActivePhysicalStep.RoundInput p rate) :=
  {x | (ReferenceActivePhysicalStepMeasurability.encodeState x.state).1 = .inl ()}

/-- The original incoming LIVE tag fiber, with no runtime-domain restriction. -/
def liveSet : Set (ReferenceActivePhysicalStep.RoundInput p rate) :=
  {x | ∃ v : ReferenceActivePhysicalStep.Payload rate × ReferenceActivePhysicalStepMeasurability.LiveDiscrete p,
    (ReferenceActivePhysicalStepMeasurability.encodeState x.state).1 = .inr (.inl v)}

/-- The original incoming absorbing coordinator tag fiber. -/
def daggerSet : Set (ReferenceActivePhysicalStep.RoundInput p rate) :=
  {x | (ReferenceActivePhysicalStepMeasurability.encodeState x.state).1 = .inr (.inr (.inr ()))}

abbrev FirstInput (p : Parameters) (rate : ReferenceActivePhysicalStep.RateInput p) :=
  ↥(firstSet (p := p) (rate := rate))
abbrev LiveInput (p : Parameters) (rate : ReferenceActivePhysicalStep.RateInput p) :=
  ↥(liveSet (p := p) (rate := rate))
abbrev DaggerInput (p : Parameters) (rate : ReferenceActivePhysicalStep.RateInput p) :=
  ↥(daggerSet (p := p) (rate := rate))

theorem measurableSet_firstSet : MeasurableSet (firstSet (p := p) (rate := rate)) := by
  have h : MeasurableSet ({()} : Set Unit) := measurableSet_singleton _
  simpa only [firstSet, daggerSet, Set.image_singleton, Set.preimage,
    ReferenceActivePhysicalStepMeasurability.encodeState, Function.comp_def, Set.mem_singleton_iff] using
    (h.inl_image.preimage (ReferenceActivePhysicalStepMeasurability.measurable_coordinatorCode.comp
      ReferenceActivePhysicalStepMeasurability.measurable_state))

theorem measurableSet_liveSet : MeasurableSet (liveSet (p := p) (rate := rate)) := by
  have h : MeasurableSet (Set.univ : Set (ReferenceActivePhysicalStep.Payload rate × ReferenceActivePhysicalStepMeasurability.LiveDiscrete p)) :=
    MeasurableSet.univ
  convert (h.inl_image.inr_image.preimage
    (ReferenceActivePhysicalStepMeasurability.measurable_coordinatorCode.comp ReferenceActivePhysicalStepMeasurability.measurable_state)) using 1
  ext x
  simp only [liveSet, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_image,
    Set.mem_univ, true_and]
  constructor
  · rintro ⟨v, hv⟩
    exact ⟨.inl v, ⟨v, rfl⟩, hv.symm⟩
  · rintro ⟨_, ⟨v, rfl⟩, hv⟩
    exact ⟨v, hv.symm⟩

theorem measurableSet_daggerSet : MeasurableSet (daggerSet (p := p) (rate := rate)) := by
  have h : MeasurableSet ({()} : Set Unit) := measurableSet_singleton _
  simpa only [firstSet, daggerSet, Set.image_singleton, Set.preimage,
    ReferenceActivePhysicalStepMeasurability.encodeState, Function.comp_def, Set.mem_singleton_iff] using
    (h.inr_image.inr_image.inr_image.preimage
      (ReferenceActivePhysicalStepMeasurability.measurable_coordinatorCode.comp
        ReferenceActivePhysicalStepMeasurability.measurable_state))

theorem first_state (x : FirstInput p rate) : x.val.state.coordinator = .first :=
  ReferenceActivePhysicalStepMeasurability.encodeCoordinator_injective x.property

theorem dagger_state (x : DaggerInput p rate) : x.val.state.coordinator = .dagger :=
  ReferenceActivePhysicalStepMeasurability.encodeCoordinator_injective x.property

/-- Extract the actual LIVE payload and discrete store by sum elimination.
The other tags are impossible on this subtype; no dummy payload is installed. -/
def livePair (x : LiveInput p rate) :
    ReferenceActivePhysicalStep.Payload rate × ReferenceActivePhysicalStepMeasurability.LiveDiscrete p :=
  match h : (ReferenceActivePhysicalStepMeasurability.encodeState x.val.state).1 with
  | .inr (.inl v) => v
  | .inl _ => False.elim (by
      obtain ⟨v, hv⟩ := x.property
      rw [h] at hv
      contradiction)
  | .inr (.inr _) => False.elim (by
      obtain ⟨v, hv⟩ := x.property
      rw [h] at hv
      simp only [Sum.inr.injEq, reduceCtorEq] at hv)

theorem livePair_spec (x : LiveInput p rate) :
    (ReferenceActivePhysicalStepMeasurability.encodeState x.val.state).1 = .inr (.inl (livePair x)) := by
  unfold livePair
  split
  · assumption
  · contradiction
  · contradiction

theorem measurable_livePair : Measurable (livePair (p := p) (rate := rate)) := by
  intro s hs
  have heq : livePair ⁻¹' s = (fun x : LiveInput p rate =>
      (ReferenceActivePhysicalStepMeasurability.encodeState x.val.state).1) ⁻¹' (Sum.inr '' (Sum.inl '' s)) := by
    ext x
    rw [Set.mem_preimage, Set.mem_preimage, livePair_spec]
    simp only [Set.mem_image, Sum.inr.injEq, Sum.inl.injEq, exists_eq_right]
  rw [heq]
  exact hs.inl_image.inr_image.preimage
    ((ReferenceActivePhysicalStepMeasurability.measurable_coordinatorCode.comp ReferenceActivePhysicalStepMeasurability.measurable_state).comp measurable_subtype_coe)

def liveRegisters (x : LiveInput p rate) :=
  ReferenceActivePhysicalStepMeasurability.decodeLiveRegisters (livePair x).1 (livePair x).2
def liveOwned (x : LiveInput p rate) :
    CoordinatorLiveServiceFinish.OwnedRegisters (liveRegisters x) :=
  ReferenceActivePhysicalStepMeasurability.decodeLiveOwned (livePair x).1 (livePair x).2
def liveBase (x : LiveInput p rate) := (livePair x).2.baseScores

theorem live_state (x : LiveInput p rate) :
    x.val.state.coordinator = .live (liveRegisters x) (liveOwned x) (liveBase x) := by
  have h := congrArg ReferenceActivePhysicalStepMeasurability.decodeCoordinator (livePair_spec x)
  exact (ReferenceActivePhysicalStepMeasurability.decodeCoordinator_encodeCoordinator x.val.state.coordinator).symm.trans h

theorem livePair_eq_actual (x : LiveInput p rate) :
    livePair x = ((liveRegisters x).payload,
      ReferenceActivePhysicalStepMeasurability.encodeLive (liveRegisters x) (liveOwned x) (liveBase x)) := by
  have h := congrArg ReferenceActivePhysicalStepMeasurability.encodeCoordinator (live_state x)
  change (ReferenceActivePhysicalStepMeasurability.encodeState x.val.state).1 = .inr (.inl _) at h
  rw [livePair_spec] at h
  exact Sum.inl.inj (Sum.inr.inj h)

theorem measurable_livePayload : Measurable
    (fun x : LiveInput p rate => (liveRegisters x).payload) :=
  measurable_fst.comp measurable_livePair

theorem measurable_liveCode : Measurable
    (fun x : LiveInput p rate => ReferenceActivePhysicalStepMeasurability.encodeLive (liveRegisters x) (liveOwned x) (liveBase x)) := by
  have h : (fun x : LiveInput p rate =>
      ReferenceActivePhysicalStepMeasurability.encodeLive (liveRegisters x) (liveOwned x) (liveBase x)) =
      fun x => (livePair x).2 :=
    funext fun x => (congrArg Prod.snd (livePair_eq_actual x)).symm
  rw [h]
  exact measurable_snd.comp measurable_livePair

/-- Both FIRST and LIVE retain the entire original continuous row. -/
def firstCoordinates (x : ReferenceActivePhysicalStep.RoundInput p rate) : ReferenceFirstDispatchMeasurability.FirstDomain p := (x.time, x.row)

theorem measurable_firstCoordinates : Measurable (firstCoordinates (p := p) (rate := rate)) :=
  ReferenceActivePhysicalStepMeasurability.measurable_time.prodMk ReferenceActivePhysicalStepMeasurability.measurable_row

def liveCoordinates (x : LiveInput p rate) : ReferenceLiveDispatchMeasurability.LiveDispatchCoordinates p rate :=
  ReferenceLiveDispatchMeasurability.liveDispatchCoordinatesOfRound x.val (liveRegisters x) (liveOwned x) (liveBase x)

theorem measurable_liveCoordinates : Measurable (liveCoordinates (p := p) (rate := rate)) :=
  measurable_livePayload.prodMk (measurable_liveCode.prodMk
    ((ReferenceActivePhysicalStepMeasurability.measurable_time.comp measurable_subtype_coe).prodMk
      (ReferenceActivePhysicalStepMeasurability.measurable_row.comp measurable_subtype_coe)))

/-- Raw FIRST diagnostics retain the full assignment vector and installation. -/
theorem measurable_firstDispatchObservation : Measurable
    (fun x : FirstInput p rate => ReferenceFirstDispatchMeasurability.firstDispatchObservationAt rate (firstCoordinates x.val)) :=
  ReferenceFirstDispatchMeasurability.measurable_firstDispatchObservationAt.comp
    (measurable_firstCoordinates.comp measurable_subtype_coe)

/-- Raw LIVE diagnostics retain every dispatch failure and the cutoff ledger. -/
theorem measurable_liveDispatchObservation : Measurable
    (fun x : LiveInput p rate => ReferenceLiveDispatchOutputMeasurability.dispatchObservation (liveCoordinates x)) :=
  ReferenceLiveDispatchOutputMeasurability.measurable_dispatchObservation.comp measurable_liveCoordinates

private theorem measurable_firstSelection : Measurable
    (fun x : FirstInput p rate => (ReferenceActivePhysicalStep.dispatch x.val).selection.map ReferenceLiveDispatchOutputMeasurability.encodeSelection) := by
  have hv : Measurable (fun x : FirstInput p rate =>
      ReferenceFirstDispatchMeasurability.firstChoiceViewAt rate (firstCoordinates x.val)) :=
    (ReferenceFirstDispatchMeasurability.measurable_firstChoiceViewAt (rate := rate)).comp
    (measurable_firstCoordinates.comp measurable_subtype_coe)
  have hs : Measurable (fun x : FirstInput p rate =>
      ReferenceFirstDispatchMeasurability.firstStartResultAt rate (firstCoordinates x.val)) :=
    (ReferenceFirstDispatchMeasurability.measurable_firstStartResultAt (rate := rate)).comp
    (measurable_firstCoordinates.comp measurable_subtype_coe)
  have ha : Measurable (fun x : FirstInput p rate =>
      ReferenceFirstDispatchMeasurability.firstOutcomeArmAt rate (firstCoordinates x.val)) :=
    (ReferenceFirstDispatchMeasurability.measurable_firstOutcomeArmAt (rate := rate)).comp
    (measurable_firstCoordinates.comp measurable_subtype_coe)
  have hsome : Measurable (some : ReferenceLiveDispatchOutputMeasurability.SelectionData p rate → Option (ReferenceLiveDispatchOutputMeasurability.SelectionData p rate)) := by
    apply measurable_comap_iff.mpr
    exact measurable_inl
  convert hsome.comp (hv.prodMk (hs.prodMk ha)) using 1
  funext x
  rw [ReferenceFirstDispatchMeasurability.dispatch_first_selection x.val (first_state x)]
  rfl

private theorem measurable_firstDownView : Measurable
    (fun x : FirstInput p rate => (ReferenceActivePhysicalStep.dispatch x.val).downView) := by
  have h : Measurable (fun x : FirstInput p rate =>
      ReferenceFirstDispatchMeasurability.firstOutcomeViewAt rate (firstCoordinates x.val)) :=
    ReferenceFirstDispatchMeasurability.measurable_firstOutcomeViewAt.comp
      (measurable_firstCoordinates.comp measurable_subtype_coe)
  convert h using 1
  funext x
  exact ReferenceFirstDispatchMeasurability.dispatch_first_downView x.val (first_state x)

private theorem measurable_firstArm : Measurable
    (fun x : FirstInput p rate => (ReferenceActivePhysicalStep.dispatch x.val).arm) := by
  have h : Measurable (fun x : FirstInput p rate =>
      ReferenceFirstDispatchMeasurability.firstOutcomeArmAt rate (firstCoordinates x.val)) :=
    ReferenceFirstDispatchMeasurability.measurable_firstOutcomeArmAt.comp
      (measurable_firstCoordinates.comp measurable_subtype_coe)
  convert h using 1
  funext x
  exact ReferenceFirstDispatchMeasurability.dispatch_first_arm x.val (first_state x)

private theorem measurable_liveProjections : Measurable
    (fun x : LiveInput p rate =>
      ((ReferenceActivePhysicalStep.dispatch x.val).selection.map ReferenceLiveDispatchOutputMeasurability.encodeSelection,
        (ReferenceActivePhysicalStep.dispatch x.val).downView, (ReferenceActivePhysicalStep.dispatch x.val).arm)) :=
  ReferenceLiveDispatchOutputMeasurability.measurable_canonical_live_projections_comp Subtype.val liveRegisters liveOwned liveBase
    live_state measurable_livePayload measurable_liveCode
    (ReferenceActivePhysicalStepMeasurability.measurable_time.comp measurable_subtype_coe)
    (ReferenceActivePhysicalStepMeasurability.measurable_row.comp measurable_subtype_coe)

/-- Assemble the actual simultaneous profile, including all follower
PREPARE failures and active dagger play. The arm premise is explicit here
and discharged by each actual coordinator dispatcher below. -/
private theorem measurable_actions {Ω : Type*} [MeasurableSpace Ω]
    (round : Ω → ReferenceActivePhysicalStep.RoundInput p rate) (hr : Measurable round)
    (ha : Measurable (fun ω => (ReferenceActivePhysicalStep.dispatch (round ω)).arm)) :
    Measurable (fun ω => (ReferenceActivePhysicalStep.prepare (round ω)).arms.actions) := by
  apply measurable_pi_iff.mpr
  intro player
  rcases ActiveRoundActions.player_cases p.two_le_m player with h | ⟨i, h⟩
  · subst player
    convert ha using 1
    funext ω
    exact (ReferenceActivePhysicalStep.prepare (round ω)).action_coordinator
  · subst player
    exact (ReferenceActivePhysicalStepMeasurability.measurable_followerArm i).comp hr

/-- Feedback is computed from the original complete grid reward table and
the actual simultaneous profile, rather than supplied as a helper premise. -/
private theorem measurable_feedback {Ω : Type*} [MeasurableSpace Ω]
    (round : Ω → ReferenceActivePhysicalStep.RoundInput p rate) (hr : Measurable round)
    (ha : Measurable (fun ω => (ReferenceActivePhysicalStep.prepare (round ω)).arms.actions)) :
    Measurable (fun ω => (ReferenceActivePhysicalStep.prepare (round ω)).feedback.feedback) := by
  have h := ReferenceActivePhysicalStepMeasurability.measurable_gridFeedback.comp
    ((ReferenceActivePhysicalStepMeasurability.measurable_rewards.comp hr).prodMk ((ReferenceActivePhysicalStepMeasurability.measurable_time.comp hr).prodMk ha))
  convert h using 1
  funext ω player
  exact (ReferenceActivePhysicalStepMeasurability.gridFeedback_eq_actual (round ω) player).symm

/-- Time reindexing preserves every other original live coordinate. -/
theorem encodeLive_at (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r) (base : Fin (p.m - 1) → ℕ)
    (time : Fin p.T) :
    ReferenceActivePhysicalStepMeasurability.encodeLive (ReferenceActivePhysicalStep.liveRegistersAt r time) (ReferenceActivePhysicalStep.liveOwnedAt r q time) base =
      { ReferenceActivePhysicalStepMeasurability.encodeLive r q base with time := time } := rfl

/-- Embed the live suffix's actual whole observation into the existing
collection-tail code. Recording is decoded with its existing finite decoder. -/
def liftLiveCode (c : ReferenceLiveServiceTailMeasurability.LiveServiceTailWholeCode p rate) : ReferenceCollectionServiceTailMeasurability.CollectionTailCode p rate :=
  (c.1, c.2.1, c.2.2.1, CoordinatorRecordingMeasurability.decodeResult c.2.2.2, none)

private theorem measurable_liftLiveCode : Measurable (liftLiveCode (p := p) (rate := rate)) :=
  measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk
    ((measurable_fst.comp (measurable_snd.comp measurable_snd)).prodMk
      (((measurable_of_countable CoordinatorRecordingMeasurability.decodeResult).comp
        (measurable_snd.comp (measurable_snd.comp measurable_snd))).prodMk measurable_const)))

private theorem liftLiveCode_eq_observation (z : ReferenceActiveLiveTailMeasurability.LivePostChoiceCoordinates p rate) :
    liftLiveCode (ReferenceActiveLiveTailMeasurability.livePostChoiceWholeCode z) =
      ReferenceCollectionServiceTailMeasurability.encodeCollectionObservation (ReferenceActiveLiveTailMeasurability.livePostChoiceObservation z) := by
  have hup := ReferenceLiveServiceTailMeasurability.liveServiceTailObservation_up_none (ReferenceActiveLiveTailMeasurability.liveServiceTailCoordinates z)
  change (ReferenceActivePhysicalStepMeasurability.encodeCoordinator (ReferenceActiveLiveTailMeasurability.livePostChoiceObservation z).configuration,
      (ReferenceActiveLiveTailMeasurability.livePostChoiceObservation z).upDecoderBank,
      (ReferenceActiveLiveTailMeasurability.livePostChoiceObservation z).failure,
      CoordinatorRecordingMeasurability.decodeResult
        (CoordinatorRecordingMeasurability.encodeResult (ReferenceActiveLiveTailMeasurability.livePostChoiceObservation z).recording),
      none) = _
  rw [CoordinatorRecordingMeasurability.decodeResult_encodeResult]
  unfold ReferenceCollectionServiceTailMeasurability.encodeCollectionObservation
  change (ReferenceActiveLiveTailMeasurability.livePostChoiceObservation z).up = none at hup
  rw [hup]
  rfl

/-- This equality uses the actual reconstruction theorem and absent-UP proof;
it does not assert a right inverse for arbitrary canonical codes. -/
theorem liftLiveCode_eq_actual {x : ReferenceActivePhysicalStep.RoundInput p rate} (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r) (base : Fin (p.m - 1) → ℕ)
    (started : CoordinatorPhaseClock.StartRoundResult p) :
    liftLiveCode (ReferenceActiveLiveTailMeasurability.livePostChoiceWholeCode (ReferenceActiveLiveTailMeasurability.coordinatesOf prepared r q base started)) =
      ReferenceCollectionServiceTailMeasurability.encodeCollectionObservation (ReferenceActivePhysicalStep.livePostChoice prepared r q base started) := by
  rw [liftLiveCode_eq_observation]
  have h := (ReferenceActiveLiveTailMeasurability.decode_livePostChoiceWholeCode (ReferenceActiveLiveTailMeasurability.coordinatesOf prepared r q base started)).symm.trans
    (ReferenceActiveLiveTailMeasurability.livePostChoiceWholeCode_reconstructs_actual prepared r q base started)
  exact congrArg ReferenceCollectionServiceTailMeasurability.encodeCollectionObservation h

/-- All fourteen ledger coordinates are restored literally, with the existing
shared rate indices. No initializer is called by this data decoder. -/
def ledgerOfData (c : ReferenceLiveDispatchOutputMeasurability.LedgerData p) : ReferenceActivePhysicalStep.Ledger rate := {
  assignment := c.1
  sigma := c.2.1
  cutoff := c.2.2.1
  freezeAt := c.2.2.2.1
  baseScore := c.2.2.2.2.1
  pending := c.2.2.2.2.2.1
  cutoffRegisters := c.2.2.2.2.2.2.1
  currentRegisters := c.2.2.2.2.2.2.2.1
  increment := c.2.2.2.2.2.2.2.2.1
  gammaLoc := c.2.2.2.2.2.2.2.2.2.1
  rawBuffer := c.2.2.2.2.2.2.2.2.2.2.1
  enabledHistory := c.2.2.2.2.2.2.2.2.2.2.2.1
  cursor := c.2.2.2.2.2.2.2.2.2.2.2.2.1
  phase := c.2.2.2.2.2.2.2.2.2.2.2.2.2 }

theorem ledgerOfData_eq_sharedLedger
    {r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta}
    (ledger : CoordinatorStartRoundCutoffDispatch.NewLedger r) :
    ledgerOfData (rate := rate) (ReferenceLiveDispatchOutputMeasurability.ledgerData ledger) = ReferenceActivePhysicalStep.sharedLedger ledger := rfl

/-- The full real vector agrees at every actual fast coordinate; zero fills
only the unused slow coordinates. -/
theorem weightVector_eq_extension (x : LiveInput p rate) :
    ReferenceLiveDispatchOutputMeasurability.weightVector (liveCoordinates x) =
      ReferenceCollectionTailComposition.extendComplementWeights (liveRegisters x).payload (fun _ => 0)
        (ReferenceActivePhysicalStep.liveRegistersAt (liveRegisters x) x.val.time).complementWeights := by
  classical
  change ReferenceLiveDispatchOutputMeasurability.weightVector
    ((liveRegisters x).payload,
      ReferenceActivePhysicalStepMeasurability.encodeLive (liveRegisters x) (liveOwned x) (liveBase x),
      x.val.time, x.val.row) = _
  funext a
  unfold ReferenceLiveDispatchOutputMeasurability.weightVector ReferenceCollectionTailComposition.extendComplementWeights
  by_cases ha : a ∈ (liveRegisters x).payload.slowSet.val
  · have hn : a ∉ CanonicalFastSampling.fastArmFinset (liveRegisters x).payload.slowSet :=
      fun hf => (Finset.mem_sdiff.mp hf).2 ha
    rw [dite_eq_right hn, dite_eq_left ha]
  · have hf : a ∈ CanonicalFastSampling.fastArmFinset (liveRegisters x).payload.slowSet :=
      Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ha⟩
    rw [dite_eq_left hf, dite_eq_right ha]
    exact congrArg (ScoreWeights.scoreWeight (AssignmentScoreReconstruction.sourceWeightBase p))
      (ReferenceActivePhysicalStepMeasurability.extendComplement_apply (liveRegisters x).payload
        (liveRegisters x).complementScores ⟨a, hf⟩)

private theorem measurable_liveActions : Measurable
    (fun x : LiveInput p rate => (ReferenceActivePhysicalStep.prepare x.val).arms.actions) :=
  measurable_actions Subtype.val measurable_subtype_coe
    (measurable_snd.comp (measurable_snd.comp measurable_liveProjections))

private theorem measurable_liveFeedback : Measurable
    (fun x : LiveInput p rate => (ReferenceActivePhysicalStep.prepare x.val).feedback.feedback) :=
  measurable_feedback Subtype.val measurable_subtype_coe measurable_liveActions

private theorem measurable_firstActions : Measurable
    (fun x : FirstInput p rate => (ReferenceActivePhysicalStep.prepare x.val).arms.actions) :=
  measurable_actions Subtype.val measurable_subtype_coe measurable_firstArm

private theorem measurable_firstFeedback : Measurable
    (fun x : FirstInput p rate => (ReferenceActivePhysicalStep.prepare x.val).feedback.feedback) :=
  measurable_feedback Subtype.val measurable_subtype_coe measurable_firstActions

/-- The literal installed FIRST runtime. Its zero stores are the initialization
formulas in `installFirst`, not values filled outside the source carrier. -/
def firstInstalled (x : ReferenceActivePhysicalStep.RoundInput p rate) :=
  CoordinatorAssignmentRegisterInstall.installFirst (ReferenceFirstDispatchMeasurability.firstLaunchInputAt rate (firstCoordinates x))

/-- Explicit initialization identities, on every original input. -/
theorem firstInstalled_zero (x : ReferenceActivePhysicalStep.RoundInput p rate) :
    (∀ a, (firstInstalled x).registers.complementScores a = 0) ∧
    (∀ a, (firstInstalled x).ownedRegisters.queue a = 0) ∧
    (∀ a, (firstInstalled x).ownedRegisters.previousService a = 0) ∧
    (∀ i, (firstInstalled x).followerBaseScore i = 0) :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

private theorem measurable_firstPayload : Measurable
    (fun x : FirstInput p rate => (firstInstalled x.val).registers.payload) := by
  let : MeasurableSpace (ReferenceFirstDispatchMeasurability.FirstChoiceKey p) := ⊤
  have h := (measurable_of_countable (fun key : ReferenceFirstDispatchMeasurability.FirstChoiceKey p =>
      ReferenceFirstDispatchMeasurability.firstPayloadAt rate key.1 key.2)).comp
    ((ReferenceFirstDispatchMeasurability.measurable_firstChoiceKeyAt (rate := rate)).comp
      (measurable_firstCoordinates.comp (measurable_subtype_coe (p := firstSet (rate := rate)))))
  exact h

private theorem measurable_firstCode : Measurable
    (fun x : FirstInput p rate => ReferenceActivePhysicalStepMeasurability.encodeLive (firstInstalled x.val).registers
      (firstInstalled x.val).ownedRegisters (firstInstalled x.val).followerBaseScore) := by
  let : MeasurableSpace (ReferenceFirstDispatchMeasurability.FirstChoiceKey p) := ⊤
  have h := (measurable_of_countable (fun key : ReferenceFirstDispatchMeasurability.FirstChoiceKey p =>
      ReferenceActivePhysicalStepMeasurability.encodeLive (ReferenceFirstDispatchMeasurability.firstRegistersForKey rate key)
        { queue := fun _ => 0, previousService := fun _ => 0 } (fun _ => 0))).comp
    ((ReferenceFirstDispatchMeasurability.measurable_firstChoiceKeyAt (rate := rate)).comp
      (measurable_firstCoordinates.comp (measurable_subtype_coe (p := firstSet (rate := rate)))))
  exact h

/-- The local composed live tail in the existing collection observation code. -/
def liveTailCode {x : ReferenceActivePhysicalStep.RoundInput p rate} (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r) (base : Fin (p.m - 1) → ℕ)
    (started : CoordinatorPhaseClock.StartRoundResult p) : ReferenceCollectionServiceTailMeasurability.CollectionTailCode p rate :=
  liftLiveCode (ReferenceActiveLiveTailMeasurability.livePostChoiceWholeCode (ReferenceActiveLiveTailMeasurability.coordinatesOf prepared r q base started))

private theorem measurable_firstTail : Measurable (fun x : FirstInput p rate =>
    liveTailCode (ReferenceActivePhysicalStep.prepare x.val) (firstInstalled x.val).registers
      (firstInstalled x.val).ownedRegisters (firstInstalled x.val).followerBaseScore
      (firstInstalled x.val).startRoundResult) := by
  have hs : Measurable (fun x : FirstInput p rate => (firstInstalled x.val).startRoundResult) :=
    ReferenceFirstDispatchMeasurability.measurable_firstStartResultAt.comp (measurable_firstCoordinates.comp measurable_subtype_coe)
  have hb : Measurable (fun x : FirstInput p rate => x.val.state.upDecoderBank) :=
    (ReferenceActivePhysicalStepMeasurability.measurable_upDecoderBank.comp ReferenceActivePhysicalStepMeasurability.measurable_state).comp measurable_subtype_coe
  have ha : Measurable (fun x : FirstInput p rate => (ReferenceActivePhysicalStep.prepare x.val).coordinator.arm) :=
    measurable_firstArm
  have ho : Measurable (fun x : FirstInput p rate => (ReferenceActivePhysicalStep.prepare x.val).coordinatorObservation) :=
    (measurable_pi_apply (ActiveRoundActions.coordinator p.two_le_m)).comp measurable_firstFeedback
  change Measurable (fun x : FirstInput p rate => liftLiveCode
    (ReferenceActiveLiveTailMeasurability.livePostChoiceWholeCode
      ((firstInstalled x.val).registers.payload,
        ReferenceActivePhysicalStepMeasurability.encodeLive (firstInstalled x.val).registers
          (firstInstalled x.val).ownedRegisters (firstInstalled x.val).followerBaseScore,
        (firstInstalled x.val).startRoundResult, x.val.state.upDecoderBank,
        x.val.time, x.val.row, (ReferenceActivePhysicalStep.prepare x.val).coordinator.arm,
        (ReferenceActivePhysicalStep.prepare x.val).coordinatorObservation)))
  exact measurable_liftLiveCode.comp
    (ReferenceActiveLiveTailMeasurability.measurable_livePostChoiceWholeCode_comp _ _ _ _ _ _ _ _
      measurable_firstPayload measurable_firstCode hs hb
      (ReferenceActivePhysicalStepMeasurability.measurable_time.comp measurable_subtype_coe)
      (ReferenceActivePhysicalStepMeasurability.measurable_row.comp measurable_subtype_coe) ha ho)

/-- The actual first dispatcher always chooses, by the admitted full-domain
proof. The chosen installation is the one used by the physical continuation. -/
theorem first_observation_eq (x : FirstInput p rate) :
    ReferenceCollectionServiceTailMeasurability.encodeCollectionObservation (ReferenceActivePhysicalStep.prepare x.val).observeCoordinator =
      liveTailCode (ReferenceActivePhysicalStep.prepare x.val) (firstInstalled x.val).registers
        (firstInstalled x.val).ownedRegisters (firstInstalled x.val).followerBaseScore
        (firstInstalled x.val).startRoundResult := by
  obtain ⟨installed, selected, hchosen⟩ := ReferenceFirstDispatchMeasurability.firstOutcomeAt_chosen (rate := rate) (firstCoordinates x.val)
  have hi := ReferenceFirstDispatchMeasurability.firstOutcomeAt_chosen_installation (firstCoordinates x.val) installed selected hchosen
  have hc : (ReferenceActivePhysicalStep.prepare x.val).coordinator = .first (.chosen installed selected) := by
    change ReferenceActivePhysicalStep.dispatch x.val = _
    rw [ReferenceActivePhysicalStep.dispatch_first x.val (first_state x)]
    exact congrArg ReferenceActivePhysicalStep.DispatchCut.first hchosen
  have hn : (ReferenceActivePhysicalStep.prepare x.val).coordinator.selection ≠ none := by
    rw [show (ReferenceActivePhysicalStep.prepare x.val).coordinator = ReferenceActivePhysicalStep.dispatch x.val from rfl,
      ReferenceFirstDispatchMeasurability.dispatch_first_selection x.val (first_state x)]
    exact Option.some_ne_none _
  have heq := ReferenceActivePhysicalStep.observeCoordinator_first_equation (ReferenceActivePhysicalStep.prepare x.val) (.chosen installed selected) hc
  have hn' : (ReferenceActivePhysicalStep.DispatchCut.first (.chosen installed selected)).selection ≠ none := by
    rw [← hc]
    exact hn
  rw [ite_eq_right hn'] at heq
  dsimp only at heq
  rw [heq]
  change _ = liftLiveCode (ReferenceActiveLiveTailMeasurability.livePostChoiceWholeCode _)
  rw [hi]
  exact (liftLiveCode_eq_actual _ _ _ _ _).symm

private theorem measurable_firstObservation : Measurable (fun x : FirstInput p rate =>
    ReferenceCollectionServiceTailMeasurability.encodeCollectionObservation (ReferenceActivePhysicalStep.prepare x.val).observeCoordinator) := by
  simp_rw [first_observation_eq]
  exact measurable_firstTail

/-- The full data decoder restores the actual installation and actual arm. -/
theorem first_dispatch_data_reconstruction (x : FirstInput p rate) :
    ReferenceFirstDispatchMeasurability.decodeFirstDispatchObservation (ReferenceFirstDispatchMeasurability.firstDispatchObservationAt rate (firstCoordinates x.val)) =
      (ReferenceFirstDispatchMeasurability.FirstInstallationData.ofInstallation (firstInstalled x.val),
        some (ReferenceFirstDispatchMeasurability.firstOutcomeArmAt rate (firstCoordinates x.val))) :=
  ReferenceFirstDispatchMeasurability.decode_firstDispatchObservationAt (firstCoordinates x.val)

/-- The two omitted installation proof fields are produced by the admitted
initial-clock theorem; no successful start is assumed by this reconstruction. -/
theorem first_dispatch_restore (x : FirstInput p rate) :
    let d := (ReferenceFirstDispatchMeasurability.decodeFirstDispatchObservation
      (ReferenceFirstDispatchMeasurability.firstDispatchObservationAt rate (firstCoordinates x.val))).1
    ∃ (hstart : d.start = (ReferenceFirstDispatchMeasurability.firstLaunchInputAt rate (firstCoordinates x.val)).start)
      (hclock : CoordinatorPhaseClock.startRound p rate.eta.val x.val.time
        (CoordinatorPhaseClock.initialClock p) Finset.univ = .ok d.startRoundResult),
      d.restore (ReferenceFirstDispatchMeasurability.firstLaunchInputAt rate (firstCoordinates x.val)) hstart hclock =
        firstInstalled x.val :=
  ReferenceFirstDispatchMeasurability.restore_firstDispatchObservationAt (firstCoordinates x.val)

/-- All assignment-vector coordinates survive in the FIRST raw diagnostic. -/
theorem first_assignmentVector (x : FirstInput p rate) :
    (ReferenceFirstDispatchMeasurability.firstDispatchObservationAt rate (firstCoordinates x.val)).start.coordinates =
      LaterAssignmentStartOperation.ownAssignmentVector x.val.row x.val.time :=
  ReferenceFirstDispatchMeasurability.firstDispatchObservationAt_coordinates (firstCoordinates x.val)

/-- The canonical LIVE cut is the one actual dispatch on this original input. -/
theorem live_dispatch_eq (x : LiveInput p rate) :
    ReferenceActivePhysicalStep.dispatch x.val = .live (liveRegisters x) (liveOwned x) (liveBase x)
      (CoordinatorRoundDispatch.dispatchLive
        (ReferenceActivePhysicalStep.liveInput x.val (liveRegisters x) (liveOwned x) (liveBase x))) :=
  ReferenceLiveDispatchMeasurability.canonicalDispatch_live_reconstruction x.val _ _ _ (live_state x)

/-- The raw LIVE decoder reconstructs the entire original dependent outcome,
including every failure and initializer diagnostic, at the same runtime. -/
theorem live_dispatch_reconstruction (x : LiveInput p rate) :
    (ReferenceLiveDispatchMeasurability.liveInputOfCoordinates_liveDispatchCoordinatesOfRound x.val
      (liveRegisters x) (liveOwned x) (liveBase x)) ▸
      ReferenceLiveDispatchOutputMeasurability.decodeOutcome (ReferenceLiveDispatchMeasurability.liveInputOfCoordinates (liveCoordinates x))
        ⟨(ReferenceLiveDispatchOutputMeasurability.dispatchObservation (liveCoordinates x)).2,
          CoordinatorRoundDispatch.dispatchLive (ReferenceLiveDispatchMeasurability.liveInputOfCoordinates (liveCoordinates x)), rfl⟩ =
      CoordinatorRoundDispatch.dispatchLive
        (ReferenceActivePhysicalStep.liveInput x.val (liveRegisters x) (liveOwned x) (liveBase x)) :=
  ReferenceLiveDispatchOutputMeasurability.canonical_decodeOutcome_reconstruction x.val _ _ _

/-- The actual reindexed runtime code used by the continuing LIVE tail. -/
private theorem measurable_liveCodeAt : Measurable (fun x : LiveInput p rate =>
    ReferenceActivePhysicalStepMeasurability.encodeLive (ReferenceActivePhysicalStep.liveRegistersAt (liveRegisters x) x.val.time)
      (ReferenceActivePhysicalStep.liveOwnedAt (liveRegisters x) (liveOwned x) x.val.time) (liveBase x)) := by
  simp_rw [encodeLive_at]
  exact (measurable_of_countable (fun z : ReferenceActivePhysicalStepMeasurability.LiveDiscrete p × Fin p.T =>
    { z.1 with time := z.2 })).comp
      (measurable_liveCode.prodMk (ReferenceActivePhysicalStepMeasurability.measurable_time.comp measurable_subtype_coe))

private theorem measurable_liveTail (started : CoordinatorPhaseClock.StartRoundResult p) :
    Measurable (fun x : LiveInput p rate => liveTailCode (ReferenceActivePhysicalStep.prepare x.val)
      (ReferenceActivePhysicalStep.liveRegistersAt (liveRegisters x) x.val.time)
      (ReferenceActivePhysicalStep.liveOwnedAt (liveRegisters x) (liveOwned x) x.val.time) (liveBase x) started) := by
  change Measurable (fun x : LiveInput p rate => liftLiveCode
    (ReferenceActiveLiveTailMeasurability.livePostChoiceWholeCode
      ((liveRegisters x).payload,
        ReferenceActivePhysicalStepMeasurability.encodeLive (ReferenceActivePhysicalStep.liveRegistersAt (liveRegisters x) x.val.time)
          (ReferenceActivePhysicalStep.liveOwnedAt (liveRegisters x) (liveOwned x) x.val.time) (liveBase x),
        started, x.val.state.upDecoderBank, x.val.time, x.val.row,
        (ReferenceActivePhysicalStep.prepare x.val).coordinator.arm, (ReferenceActivePhysicalStep.prepare x.val).coordinatorObservation)))
  exact measurable_liftLiveCode.comp
    (ReferenceActiveLiveTailMeasurability.measurable_livePostChoiceWholeCode_comp _ _ _ _ _ _ _ _
      measurable_livePayload measurable_liveCodeAt measurable_const
      ((ReferenceActivePhysicalStepMeasurability.measurable_upDecoderBank.comp ReferenceActivePhysicalStepMeasurability.measurable_state).comp measurable_subtype_coe)
      (ReferenceActivePhysicalStepMeasurability.measurable_time.comp measurable_subtype_coe)
      (ReferenceActivePhysicalStepMeasurability.measurable_row.comp measurable_subtype_coe)
      (measurable_snd.comp (measurable_snd.comp measurable_liveProjections))
      ((measurable_pi_apply (ActiveRoundActions.coordinator p.two_le_m)).comp measurable_liveFeedback))

/-- The literal observation code for failed dispatch, preserving the original
bank. Distinct raw dispatch failures are retained by dispatchObservation. -/
def rejectedCode (x : ReferenceActivePhysicalStep.RoundInput p rate) : ReferenceCollectionServiceTailMeasurability.CollectionTailCode p rate :=
  ReferenceCollectionServiceTailMeasurability.encodeCollectionObservation
    (ReferenceActivePhysicalStep.coordinatorFailure x.state.upDecoderBank .dispatchRejected none none)

private theorem measurable_rejectedCode : Measurable (rejectedCode (p := p) (rate := rate)) :=
  measurable_const.prodMk ((ReferenceActivePhysicalStepMeasurability.measurable_upDecoderBank.comp ReferenceActivePhysicalStepMeasurability.measurable_state).prodMk
    (measurable_const.prodMk (measurable_const.prodMk measurable_const)))

/-- Glue by the lossless original dispatch outcome. Cutoff uses the collection
suffix and its original fourteen-coordinate initialized ledger. -/
def liveObservationFormula (x : LiveInput p rate) : ReferenceLiveDispatchOutputMeasurability.OutcomeData p → ReferenceCollectionServiceTailMeasurability.CollectionTailCode p rate
  | .clockFailure _ => rejectedCode x.val
  | .initializerFailure _ _ => rejectedCode x.val
  | .localFailure _ _ => rejectedCode x.val
  | .continuingChosen dispatched _ _ => liveTailCode (ReferenceActivePhysicalStep.prepare x.val)
      (ReferenceActivePhysicalStep.liveRegistersAt (liveRegisters x) x.val.time)
      (ReferenceActivePhysicalStep.liveOwnedAt (liveRegisters x) (liveOwned x) x.val.time)
      (liveBase x) dispatched.1
  | .cutoffChosen dispatched ledger _ =>
      ReferenceCollectionTailComposition.collectionPostChoiceTailCode x.val (liveRegisters x).payload
        (ledgerOfData ledger) dispatched.1 (ReferenceLiveDispatchOutputMeasurability.weightVector (liveCoordinates x))
        (ReferenceActivePhysicalStep.prepare x.val).coordinator.arm (ReferenceActivePhysicalStep.prepare x.val).coordinatorObservation

private theorem measurable_liveObservationFormula : Measurable
    (fun z : LiveInput p rate × ReferenceLiveDispatchOutputMeasurability.OutcomeData p => liveObservationFormula z.1 z.2) := by
  apply measurable_from_prod_countable_left
  intro outcome
  cases outcome with
  | clockFailure reason => exact measurable_rejectedCode.comp measurable_subtype_coe
  | initializerFailure dispatched checked => exact measurable_rejectedCode.comp measurable_subtype_coe
  | localFailure dispatched reason => exact measurable_rejectedCode.comp measurable_subtype_coe
  | continuingChosen dispatched continuation arm => exact measurable_liveTail dispatched.1
  | cutoffChosen dispatched ledger arm =>
      exact ReferenceCollectionTailComposition.measurable_collectionPostChoiceTailCode_comp
        Subtype.val (fun x => (liveRegisters x).payload)
        (fun _ => ledgerOfData ledger) (fun _ => dispatched.1)
        (fun x => ReferenceLiveDispatchOutputMeasurability.weightVector (liveCoordinates x))
        (fun x => (ReferenceActivePhysicalStep.prepare x.val).coordinator.arm)
        (fun x => (ReferenceActivePhysicalStep.prepare x.val).coordinatorObservation)
        measurable_subtype_coe measurable_livePayload measurable_const measurable_const
        (ReferenceLiveDispatchOutputMeasurability.measurable_weightVector.comp measurable_liveCoordinates)
        (measurable_snd.comp (measurable_snd.comp measurable_liveProjections))
        ((measurable_pi_apply (ActiveRoundActions.coordinator p.two_le_m)).comp measurable_liveFeedback)

/-- Same-input equality to the literal coordinator observation, including
clock/initializer/local rejection, continuing LIVE, and first cutoff. -/
theorem live_observation_eq (x : LiveInput p rate) :
    ReferenceCollectionServiceTailMeasurability.encodeCollectionObservation (ReferenceActivePhysicalStep.prepare x.val).observeCoordinator =
      liveObservationFormula x (ReferenceLiveDispatchOutputMeasurability.dispatchObservation (liveCoordinates x)).2 := by
  have hc : (ReferenceActivePhysicalStep.prepare x.val).coordinator = .live (liveRegisters x) (liveOwned x) (liveBase x)
      (CoordinatorRoundDispatch.dispatchLive
        (ReferenceActivePhysicalStep.liveInput x.val (liveRegisters x) (liveOwned x) (liveBase x))) :=
    ReferenceLiveDispatchMeasurability.canonicalDispatch_live_reconstruction x.val _ _ _ (live_state x)
  rw [ReferenceActivePhysicalStep.observeCoordinator_live_equation (ReferenceActivePhysicalStep.prepare x.val) _ _ _ _ hc]
  change _ = liveObservationFormula x (ReferenceLiveDispatchOutputMeasurability.outcomeData
    (CoordinatorRoundDispatch.dispatchLive (ReferenceLiveDispatchMeasurability.liveInputOfCoordinates
      (ReferenceLiveDispatchMeasurability.liveDispatchCoordinatesOfRound x.val
        (liveRegisters x) (liveOwned x) (liveBase x)))))
  rw [ReferenceLiveDispatchOutputMeasurability.outcomeData_originalInput x.val
    (liveRegisters x) (liveOwned x) (liveBase x)]
  cases outcome : CoordinatorRoundDispatch.dispatchLive
      (ReferenceActivePhysicalStep.liveInput x.val (liveRegisters x) (liveOwned x) (liveBase x)) with
  | clockFailure reason hclock => rfl
  | initializerFailure dispatched hdispatch checked hchecked => rfl
  | localFailure dispatched hdispatch reason => rfl
  | continuingChosen dispatched hdispatch continuation selected =>
      simp only [ReferenceActivePhysicalStep.DispatchCut.selection, ReferenceActivePhysicalStep.selectionAt, dite_true,
        Option.some_ne_none, ReferenceLiveDispatchOutputMeasurability.outcomeData, liveObservationFormula,
        ReferenceLiveDispatchOutputMeasurability.dispatchData]
      exact (liftLiveCode_eq_actual _ _ _ _ _).symm
  | cutoffChosen dispatched hdispatch ledger hinitial hcutoff hvalid hpayload hweights hchoice selected =>
      simp only [ReferenceActivePhysicalStep.DispatchCut.selection, ReferenceActivePhysicalStep.selectionAt, dite_true,
        Option.some_ne_none, ReferenceLiveDispatchOutputMeasurability.outcomeData, liveObservationFormula,
        ReferenceLiveDispatchOutputMeasurability.dispatchData, weightVector_eq_extension]
      exact (ReferenceCollectionTailComposition.collectionPostChoiceTailCode_eq_existing (ReferenceActivePhysicalStep.prepare x.val)
        (liveRegisters x).payload (ReferenceActivePhysicalStep.sharedLedger ledger) dispatched.startResult
        (fun _ => 0) (ReferenceActivePhysicalStep.liveRegistersAt (liveRegisters x) x.val.time).complementWeights).symm

private theorem measurable_liveObservation : Measurable (fun x : LiveInput p rate =>
    ReferenceCollectionServiceTailMeasurability.encodeCollectionObservation (ReferenceActivePhysicalStep.prepare x.val).observeCoordinator) := by
  simp_rw [live_observation_eq]
  exact measurable_liveObservationFormula.comp
    (measurable_id.prodMk (measurable_snd.comp measurable_liveDispatchObservation))

/-- The exact tuple consumed by follower FINISH and the later canonical STEP
composer. It uses only existing operations and existing observation codes. -/
def physicalCode (x : ReferenceActivePhysicalStep.RoundInput p rate) :=
  ((ReferenceActivePhysicalStep.dispatch x).selection.map ReferenceLiveDispatchOutputMeasurability.encodeSelection,
    (ReferenceActivePhysicalStep.dispatch x).downView, (ReferenceActivePhysicalStep.prepare x).arms.actions,
    (ReferenceActivePhysicalStep.prepare x).feedback.feedback,
    ReferenceCollectionServiceTailMeasurability.encodeCollectionObservation (ReferenceActivePhysicalStep.prepare x).observeCoordinator)

/-- Unconditional FIRST physical front and whole coordinator observation. -/
theorem measurable_firstPhysicalCode : Measurable
    (fun x : FirstInput p rate => physicalCode x.val) :=
  measurable_firstSelection.prodMk (measurable_firstDownView.prodMk
    (measurable_firstActions.prodMk (measurable_firstFeedback.prodMk measurable_firstObservation)))

/-- Unconditional LIVE physical front and whole coordinator observation. -/
theorem measurable_livePhysicalCode : Measurable
    (fun x : LiveInput p rate => physicalCode x.val) :=
  (measurable_fst.comp measurable_liveProjections).prodMk
    ((measurable_fst.comp (measurable_snd.comp measurable_liveProjections)).prodMk
      (measurable_liveActions.prodMk (measurable_liveFeedback.prodMk measurable_liveObservation)))

/-- Absorbing coordinator play preserves its bank without introducing a
failure flag, recorder result, or UP cut. Followers still prepare and play. -/
theorem dagger_observation_eq (x : DaggerInput p rate) :
    (ReferenceActivePhysicalStep.prepare x.val).observeCoordinator =
      ⟨.dagger, x.val.state.upDecoderBank, none, none, none⟩ :=
  ReferenceActivePhysicalStep.observeCoordinator_dagger (ReferenceActivePhysicalStep.prepare x.val) (ReferenceActivePhysicalStep.dispatch_dagger x.val (dagger_state x))

/-- Unconditional dagger physical front, including every actual follower arm
and the resulting simultaneous feedback. -/
theorem measurable_daggerPhysicalCode : Measurable
    (fun x : DaggerInput p rate => physicalCode x.val) := by
  have hd (x : DaggerInput p rate) : ReferenceActivePhysicalStep.dispatch x.val = .dagger :=
    ReferenceActivePhysicalStep.dispatch_dagger x.val (dagger_state x)
  have hselection : Measurable (fun x : DaggerInput p rate =>
      (ReferenceActivePhysicalStep.dispatch x.val).selection.map ReferenceLiveDispatchOutputMeasurability.encodeSelection) := by
    simp_rw [hd]
    exact measurable_const
  have hview : Measurable (fun x : DaggerInput p rate => (ReferenceActivePhysicalStep.dispatch x.val).downView) := by
    simp_rw [hd]
    exact measurable_const
  have harm : Measurable (fun x : DaggerInput p rate => (ReferenceActivePhysicalStep.dispatch x.val).arm) := by
    simp_rw [hd]
    exact measurable_const
  have hactions := measurable_actions Subtype.val measurable_subtype_coe harm
  have hfeedback := measurable_feedback Subtype.val measurable_subtype_coe hactions
  have hobservation : Measurable (fun x : DaggerInput p rate =>
      ReferenceCollectionServiceTailMeasurability.encodeCollectionObservation (ReferenceActivePhysicalStep.prepare x.val).observeCoordinator) := by
    simp_rw [dagger_observation_eq]
    exact measurable_const.prodMk
      (((ReferenceActivePhysicalStepMeasurability.measurable_upDecoderBank.comp ReferenceActivePhysicalStepMeasurability.measurable_state).comp measurable_subtype_coe).prodMk
        (measurable_const.prodMk (measurable_const.prodMk measurable_const)))
  exact hselection.prodMk (hview.prodMk (hactions.prodMk (hfeedback.prodMk hobservation)))

/-- The three incoming canonical tag fibers; only incoming COLLECTION is omitted. -/
def firstLiveSet : Set (ReferenceActivePhysicalStep.RoundInput p rate) := firstSet ∪ liveSet ∪ daggerSet

abbrev FirstLiveInput (p : Parameters) (rate : ReferenceActivePhysicalStep.RateInput p) :=
  ↥(firstLiveSet (p := p) (rate := rate))

theorem measurableSet_firstLiveSet : MeasurableSet (firstLiveSet (p := p) (rate := rate)) :=
  (measurableSet_firstSet.union measurableSet_liveSet).union measurableSet_daggerSet

/-- There are no reachability, domain, success, score, queue or decoder
restrictions hidden in the union's domain. -/
theorem mem_firstLiveSet_iff (x : ReferenceActivePhysicalStep.RoundInput p rate) :
    x ∈ firstLiveSet ↔ ¬ ∃ payload ledger proposal,
      x.state.coordinator = .collection payload ledger proposal := by
  cases h : x.state.coordinator <;>
    simp [firstLiveSet, firstSet, liveSet, daggerSet, ReferenceActivePhysicalStepMeasurability.encodeState, ReferenceActivePhysicalStepMeasurability.encodeCoordinator, h]

/-- Glue the actual maps on the three measured incoming-tag fibers.
The conclusion has no conditional producer measurability inputs. -/
theorem measurable_physicalCode : Measurable
    (fun x : FirstLiveInput p rate => physicalCode x.val) := by
  intro u hu
  have hfirst := (measurableSet_firstSet (rate := rate)).subtype_image
    ((measurable_firstPhysicalCode (rate := rate)) hu)
  have hlive := (measurableSet_liveSet (rate := rate)).subtype_image
    ((measurable_livePhysicalCode (rate := rate)) hu)
  have hdagger := (measurableSet_daggerSet (rate := rate)).subtype_image
    ((measurable_daggerPhysicalCode (rate := rate)) hu)
  have h : MeasurableSet
      ((Subtype.val : FirstLiveInput p rate → ReferenceActivePhysicalStep.RoundInput p rate) ⁻¹'
        ((Subtype.val : FirstInput p rate → ReferenceActivePhysicalStep.RoundInput p rate) ''
          ((fun x : FirstInput p rate => physicalCode x.val) ⁻¹' u) ∪
        (Subtype.val : LiveInput p rate → ReferenceActivePhysicalStep.RoundInput p rate) ''
          ((fun x : LiveInput p rate => physicalCode x.val) ⁻¹' u) ∪
        (Subtype.val : DaggerInput p rate → ReferenceActivePhysicalStep.RoundInput p rate) ''
          ((fun x : DaggerInput p rate => physicalCode x.val) ⁻¹' u))) :=
    ((hfirst.union hlive).union hdagger).preimage measurable_subtype_coe
  convert h using 1
  ext x
  simp only [Set.mem_preimage, Set.mem_union, Set.mem_image]
  constructor
  · intro hx
    rcases x.property with (hf | hl) | hd
    · exact Or.inl (Or.inl ⟨⟨x.val, hf⟩, hx, rfl⟩)
    · exact Or.inl (Or.inr ⟨⟨x.val, hl⟩, hx, rfl⟩)
    · exact Or.inr ⟨⟨x.val, hd⟩, hx, rfl⟩
  · rintro ((⟨y, hy, heq⟩ | ⟨y, hy, heq⟩) | ⟨y, hy, heq⟩) <;>
      simpa only [heq] using hy

/-- The existing decoder recovers the literal entire actual observation. -/
theorem physicalCode_observation_reconstructs (x : FirstLiveInput p rate) :
    ReferenceCollectionServiceTailMeasurability.decodeCollectionObservation (physicalCode x.val).2.2.2.2 =
      (ReferenceActivePhysicalStep.prepare x.val).observeCoordinator :=
  ReferenceCollectionServiceTailMeasurability.decodeCollectionObservation_encodeCollectionObservation _

/-- Canonical successor fields are exactly the observation's configuration
and persistent UP bank, by the existing physical STEP field identities. -/
theorem coordinatorBank_eq_successor (x : ReferenceActivePhysicalStep.RoundInput p rate) :
    ((physicalCode x).2.2.2.2.1, (physicalCode x).2.2.2.2.2.1) =
      ((ReferenceActivePhysicalStepMeasurability.successorCode x).1, (ReferenceActivePhysicalStepMeasurability.successorCode x).2.1) := by
  change (ReferenceActivePhysicalStepMeasurability.encodeCoordinator (ReferenceActivePhysicalStep.prepare x).observeCoordinator.configuration,
      (ReferenceActivePhysicalStep.prepare x).observeCoordinator.upDecoderBank) =
    (ReferenceActivePhysicalStepMeasurability.encodeCoordinator (ReferenceActivePhysicalStep.step x).next.coordinator, (ReferenceActivePhysicalStep.step x).next.upDecoderBank)
  rw [(ReferenceActivePhysicalStep.step_next_fields x).1, (ReferenceActivePhysicalStep.step_next_fields x).2.1]

/-- The exact coordinator/bank successor projection is measured independently
of follower FINISH and of incoming COLLECTION dispatch. -/
theorem measurable_coordinatorBankSuccessor : Measurable (fun x : FirstLiveInput p rate =>
    ((ReferenceActivePhysicalStepMeasurability.successorCode x.val).1, (ReferenceActivePhysicalStepMeasurability.successorCode x.val).2.1)) := by
  simp_rw [← coordinatorBank_eq_successor]
  have h : Measurable (fun x : FirstLiveInput p rate => (physicalCode x.val).2.2.2.2) :=
    measurable_snd.comp (measurable_snd.comp
      (measurable_snd.comp (measurable_snd.comp measurable_physicalCode)))
  exact (measurable_fst.comp h).prodMk (measurable_fst.comp (measurable_snd.comp h))

/-- The named follower-tail consumer receives the actual measured DOWN view. -/
theorem measurable_downView : Measurable
    (fun x : FirstLiveInput p rate => (ReferenceActivePhysicalStep.dispatch x.val).downView) :=
  measurable_fst.comp (measurable_snd.comp measurable_physicalCode)

/-- The named follower-tail consumer receives each player's actual own grid
feedback, with no collision-freedom or physical-history assumption. -/
theorem measurable_playerFeedback (player : Fin p.m) : Measurable
    (fun x : FirstLiveInput p rate => (ReferenceActivePhysicalStep.prepare x.val).feedback.feedback player) :=
  (measurable_pi_apply player).comp
    (measurable_fst.comp (measurable_snd.comp
      (measurable_snd.comp (measurable_snd.comp measurable_physicalCode))))

end Bandits.Support.ReferenceFirstLiveCoordinatorStepMeasurability

end
