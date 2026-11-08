/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionUpDetectedWaitingCost

/-!
# Actual finite-calendar awaited DOWN failure readout

Sources: `sources/zip4/manuscript/05_binary_transport.tex:33-55`,
`sources/zip4/manuscript/06_interruptions.tex:246-282,459-481`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:92-108,141-157`.

This module reads the actual finite-calendar DOWN diagnostics and source
controls. Its fixed-word ambiguity predicate requires the ordinary receiver
acceptance test at every selected DOWN round, including zero-feedback rounds.
It is an internal reference-calendar event readout, not source-law coverage.
The intended consumer after acceptance is
`ReferenceFirstCollectionAwaitedTaskSupport`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support
open ConstructorDimensions
open BootstrapPrivateRoundStreams
open scoped Classical

namespace Bandits.Support.ReferenceFirstCollectionAwaitedDownFailureReadout

variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
variable (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
variable (C_star C_h : ℝ)

/-- The common original source carrier used by the finite-calendar readouts. -/
abbrev Z := BootstrapPrivateRoundStreams.SourceInput p

/-- The actual stored physical record and its original stamped decoder entries. -/
abbrev Record := ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)
abbrev Batch := List (AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p))
abbrev Word := AffineChannelLaw.Word (AffineBatchDecoder.width p)
abbrev I := Fin (p.m - 1)

/-- The literal actual postlaunch record lookup on the original source input. -/
abbrev actualRecord (t : Fin p.T) (z : Z (p := p)) :=
  ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z

/-- A word is awaited at this actual DOWN record precisely when the retained
call, completed receiver cut, expected sender word, and ordinary local
acceptance test all agree. The expected word remains an explicit `Word`. -/
def awaitedDownAt (r : Record (rate := rate)) (i : I (p := p))
    (M : Word (p := p)) : Prop :=
  ∃ logged cut,
    (r.output.followers i).downInput = some logged ∧
    (r.output.followers i).down = some cut ∧
    cut.rawComparison.isSome = true ∧
    cut.expectedWord = some M ∧
    ReferenceDownReception.ordinaryLocalAcceptanceTest p rate r.input.time logged
      (ReferenceDownReception.ordinaryParse p rate (some M))

/-- A completed ambiguous DOWN batch whose every equation and every selected
DOWN calendar point belongs to one fixed, locally accepted awaited word. -/
def fixedAwaitedDownFailureAt (z : Z (p := p)) (t : Fin p.T) : Prop :=
  ∃ (r : Record (rate := rate)) (i : I (p := p)) (M : Word (p := p))
      (W : Batch (p := p)) (a : Fin p.T),
    actualRecord rate rewards C_star C_h t z = some r ∧
    ReferenceFirstLiveDownCompletionReadout.completedDownBatch r i = some W ∧
    a.val ≤ t.val ∧
    ReferenceFirstLiveDownCompletionReadout.multipleSolutions W ∧
    (∀ e ∈ W, a.val ≤ e.time.val ∧ e.time.val ≤ t.val ∧
      AffineBatchDecoder.equation e.sample M ∧
      ∃ re : Record (rate := rate),
        actualRecord rate rewards C_star C_h e.time z = some re ∧
        e ∈ ReferenceFollowerDownDecoderReplay.actualDownPositives i [re] ∧
        awaitedDownAt rate re i M) ∧
    (∀ v : Fin p.T, a.val ≤ v.val → v.val ≤ t.val →
      ReferenceSelectedAffinePairLaw.selectedChannel p
        ((z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)).2 v).1 =
          some (0, i) →
      ∃ rv : Record (rate := rate),
        actualRecord rate rewards C_star C_h v z = some rv ∧
        awaitedDownAt rate rv i M)

/-- The strict-past failure readout combines the retained saved-wrong
diagnostic, the new fixed awaited DOWN event, and the existing fixed awaited
UP event without changing the latter's body. -/
def failureAt (z : Z (p := p)) (t : Fin p.T) : Prop :=
  (∃ r : Record (rate := rate),
      actualRecord rate rewards C_star C_h t z = some r ∧
        ReferenceActiveStoppedPrefixCoupling.saved_wrong_unique_accepted r) ∨
    fixedAwaitedDownFailureAt rate rewards C_star C_h z t ∨
    ReferenceCollectionUpFailureReadoutV2.fixedAwaitedUpFailureAt
      rate rewards C_star C_h z t

/-- Scan only earlier physical calendar coordinates. The detecting update is
included at the next scan index by this strict-past endpoint convention. -/
def pastFailureFlag (n : ℕ) (z : Z (p := p)) : Bool :=
  decide (∃ t : Fin p.T, t.val < n ∧ failureAt rate rewards C_star C_h z t)

private abbrev RoundCode :=
  ReferenceActiveHorizonMeasurability.RoundRecordCode (p := p) (rate := rate)
private abbrev DownCode :=
  ReferenceDownCompletedAmbiguityMeasurability.DownRoundCode p rate
private abbrev Channel := ContinuousLearningRows.Channel p

/-- The retained original whole-round codes, projected to the existing DOWN
call and diagnostic code at each actual calendar time. -/
private def downObservationFromRecordCode (i : I (p := p))
    (z : Z (p := p)) (v : Fin p.T) (code : RoundCode (p := p) (rate := rate)) :
    Option (DownCode (p := p) (rate := rate)) := by
  classical
  let state := ReferenceActivePhysicalStepMeasurability.decodeState code.2.1
  exact if hactive : ∀ j : Fin (p.m - 1), (state.activations j).val ≤ v.val + 1 then
    some (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation
      ⟨state, z.1.2, ActualInitializationPhysicalStep.selectedRowIndex p z, v,
        hactive, rewards⟩ i)
  else none

private def downObservationHistory (i : I (p := p)) (z : Z (p := p)) :
    Fin p.T → Option (DownCode (p := p) (rate := rate)) :=
  fun v => (ReferenceInspectedPastRoundObservations.pastRoundObservations
      rate rewards C_star C_h p.T (Nat.le_refl p.T) z v).bind
    (downObservationFromRecordCode rate rewards i z v)

/-- The source's selected channel is read from its original selected row at
every finite-calendar point, including zero-feedback points. -/
private def selectedChannelHistory (z : Z (p := p)) : Fin p.T → Option (Channel (p := p)) :=
  fun v => (ReferenceSelectedAffinePairLaw.selector p v z).2

/-- Countable-code form of the local ordinary awaited receiver test. -/
private def awaitedDownAtCode (round : DownCode (p := p) (rate := rate))
    (_i : I (p := p)) (M : Word (p := p)) : Prop :=
  ∃ logged cut,
    round.2.2.2.1 = some logged ∧
    round.2.2.2.2.2 = some cut ∧
    cut.2.2.1.isSome = true ∧ cut.2.1 = some M ∧
    ReferenceDownReception.ordinaryLocalAcceptanceTest p rate round.1
      (FollowerDownMeasurability.followerStateOfCode rate logged [])
      (ReferenceDownReception.ordinaryParse p rate (some M))

/-- Positive entries carried by the existing DOWN call code. -/
private def positiveEntriesFromDownCode (round : DownCode (p := p) (rate := rate)) :
    Batch (p := p) :=
  match round.2.2.1 with
  | none => []
  | some call => AffineBatchDecoder.positiveAt p
      (ActiveFollowerDownAcceptance.currentInputExtension p
        (ReferenceDownCompletedAmbiguityMeasurability.decodeCall call).2) call.1

/-- Exact code-level fixed awaited DOWN event on the retained actual calendar,
including zero selected arrivals in its interval clause. -/
private def fixedAwaitedDownFailureCodeAt
    (history : I (p := p) → Fin p.T → Option (DownCode (p := p) (rate := rate)))
    (channels : Fin p.T → Option (Channel (p := p))) (t : Fin p.T) : Prop :=
  ∃ (i : I (p := p)) (M : Word (p := p)) (W : Batch (p := p)) (a : Fin p.T),
    (history i t).bind (ReferenceFirstLiveDownCompletionReadout.completedBatchCode
      (p := p) (rate := rate)) = some W ∧
    a.val ≤ t.val ∧ ReferenceFirstLiveDownCompletionReadout.multipleSolutions W ∧
    (∀ e ∈ W, a.val ≤ e.time.val ∧ e.time.val ≤ t.val ∧
      AffineBatchDecoder.equation e.sample M ∧
      ∃ round, history i e.time = some round ∧
        e ∈ positiveEntriesFromDownCode rate round ∧ awaitedDownAtCode rate round i M) ∧
    (∀ v : Fin p.T, a.val ≤ v.val → v.val ≤ t.val → channels v = some (0, i) →
      ∃ round, history i v = some round ∧ awaitedDownAtCode rate round i M)

private theorem measurableSet_option_singleton {α : Type*}
    [MeasurableSpace α] [MeasurableSingletonClass α] (a : Option α) :
    MeasurableSet[LaterAssignmentStartMeasurability.optionMeasurableSpace] {a} := by
  let e := Equiv.optionEquivSumPUnit α
  have he : @Measurable (Option α) (α ⊕ PUnit)
      LaterAssignmentStartMeasurability.optionMeasurableSpace inferInstance e :=
    comap_measurable _
  have hset : ({a} : Set (Option α)) = e ⁻¹' {e a} := by
    ext x
    exact ⟨fun h => congrArg e h, fun h => e.injective h⟩
  rw [hset]
  apply he
  cases h : e a with
  | inl value =>
      simpa only [Set.image_singleton] using
        (measurableSet_singleton value).inl_image (β := PUnit)
  | inr value =>
      simpa only [Set.image_singleton] using
        (measurableSet_singleton value).inr_image (α := α)

local instance {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] :
    @MeasurableSingletonClass (Option α)
      LaterAssignmentStartMeasurability.optionMeasurableSpace :=
  ⟨measurableSet_option_singleton⟩

local instance : MeasurableSingletonClass
    (FollowerDownMeasurability.FollowerStateCode p rate) := ⟨fun _ => trivial⟩

local instance : MeasurableSingletonClass DeclaredFollowerLocalRound.RoundFailure :=
  ⟨fun _ => trivial⟩

private theorem measurable_downObservationFromRecordCode (i : I (p := p)) (v : Fin p.T) :
    Measurable (fun x : RoundCode (p := p) (rate := rate) × Z (p := p) =>
      downObservationFromRecordCode rate rewards i x.2 v x.1) := by
  let active : Set (RoundCode (p := p) (rate := rate) × Z (p := p)) :=
    {x | ∀ j : I (p := p),
      ((ReferenceActivePhysicalStepMeasurability.decodeState x.1.2.1).activations j).val ≤
        v.val + 1}
  have hstate : Measurable (fun x : RoundCode (p := p) (rate := rate) × Z (p := p) =>
      ReferenceActivePhysicalStepMeasurability.decodeState x.1.2.1) :=
    (ReferenceReleaseStrictPastFactor.measurable_decodeState rate).comp
      (measurable_fst.comp (measurable_snd.comp measurable_fst))
  have hactivations := ReferenceActivePhysicalStepMeasurability.measurable_activations.comp hstate
  have hs : MeasurableSet active := by
    exact hactivations (Set.to_countable
      {a : I (p := p) → ReferencePrelaunchFollower.Activation p |
        ∀ j, (a j).val ≤ v.val + 1}).measurableSet
  apply measurable_of_restrict_of_restrict_compl hs
  · let input (x : active) : ReferenceActivePhysicalStep.RoundInput p rate :=
      ⟨ReferenceActivePhysicalStepMeasurability.decodeState x.val.1.2.1,
        x.val.2.1.2, ActualInitializationPhysicalStep.selectedRowIndex p x.val.2,
        v, x.property, rewards⟩
    have hrows : Measurable (fun x : active => x.val.2.1.2) :=
      measurable_snd.comp (measurable_fst.comp
        (measurable_snd.comp measurable_subtype_coe))
    have hselected : Measurable (fun x : active =>
        ActualInitializationPhysicalStep.selectedRowIndex p x.val.2) :=
      (PrivateSourceStreams.measurable_coordinatorIndex p).comp
        (measurable_snd.comp (measurable_fst.comp
          (measurable_snd.comp (measurable_snd.comp measurable_subtype_coe))))
    have hi : Measurable input := by
      apply measurable_comap_iff.mpr
      apply Measurable.subtype_mk
      exact (hstate.comp measurable_subtype_coe).prodMk
        (hrows.prodMk (hselected.prodMk (measurable_const.prodMk measurable_const)))
    have hobs := (ReferenceDownCompletedAmbiguityMeasurability.measurable_roundDownObservation i).comp hi
    have hsome : Measurable (some : DownCode (p := p) (rate := rate) → Option _) :=
      measurable_comap_iff.mpr measurable_inl
    convert hsome.comp hobs using 1
    funext x
    change downObservationFromRecordCode rate rewards i x.val.2 v x.val.1 = _
    have hx : ∀ j : I (p := p),
        ((ReferenceActivePhysicalStepMeasurability.decodeState x.val.1.2.1).activations j).val ≤
          v.val + 1 := x.property
    rw [downObservationFromRecordCode, dite_eq_left hx]
    rfl
  · have heq : (fun x : (activeᶜ : Set _) =>
        downObservationFromRecordCode rate rewards i x.val.2 v x.val.1) =
          fun _ => none := by
      funext x
      exact dite_eq_right x.property
    change Measurable (fun x : (activeᶜ : Set _) =>
      downObservationFromRecordCode rate rewards i x.val.2 v x.val.1)
    rw [heq]
    exact measurable_const

private theorem measurable_downObservationHistory (i : I (p := p)) :
    Measurable (downObservationHistory rate rewards C_star C_h i) := by
  apply measurable_pi_iff.mpr
  intro v
  have hobs := (measurable_pi_iff.mp
    (ReferenceInspectedPastRoundObservations.measurable_pastRoundObservations
      rate rewards C_star C_h p.T (Nat.le_refl p.T))) v
  have hm := ReferenceCollectionInstallOutputMeasurability.measurable_optionMapDependent
    (fun x : RoundCode (p := p) (rate := rate) × Z (p := p) =>
      downObservationFromRecordCode rate rewards i x.2 v x.1)
    (measurable_downObservationFromRecordCode rate rewards i v)
    (fun z => ReferenceInspectedPastRoundObservations.pastRoundObservations
      rate rewards C_star C_h p.T (Nat.le_refl p.T) z v) hobs
  have hflatten : Measurable (fun x : Option (Option (DownCode (p := p) (rate := rate))) =>
      x.bind id) := measurable_of_countable _
  convert hflatten.comp hm using 1
  funext z
  simp only [Function.comp_def, downObservationHistory, Option.bind_map, id_eq]

private theorem actualRecord_input_fields (t : Fin p.T) (z : Z (p := p))
    (r : Record (rate := rate))
    (hr : actualRecord rate rewards C_star C_h t z = some r) :
    r.input.rows = z.1.2 ∧ r.input.selected =
      ActualInitializationPhysicalStep.selectedRowIndex p z ∧
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
  · change ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t z = some r at hr
    rw [ReferenceSourcePrefixHistoryFiltration.actualRecord_eq_none_of_not_launchBy
      rate rewards C_star C_h t z hz] at hr
    cases hr

private theorem roundInput_ext
    {left right : ReferenceActivePhysicalStep.RoundInput p rate}
    (hstate : left.state = right.state) (hrows : left.rows = right.rows)
    (hselected : left.selected = right.selected) (htime : left.time = right.time)
    (hrewards : left.rewards = right.rewards) : left = right := by
  cases left
  cases right
  simp_all

private theorem downObservationFromRecordCode_actual
    (i : I (p := p)) (z : Z (p := p)) (t : Fin p.T)
    (r : Record (rate := rate))
    (hr : actualRecord rate rewards C_star C_h t z = some r) :
    downObservationFromRecordCode rate rewards i z t
        (ReferenceActiveHorizonMeasurability.roundRecordCode r) =
      some (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation r.input i) := by
  obtain ⟨hrows, hselected, htime, hrewards⟩ :=
    actualRecord_input_fields rate rewards C_star C_h t z r hr
  have hstate :=
    (ReferenceActiveHorizonMeasurability.roundRecordCode_reconstructs r).1
  have hactive : ∀ j : Fin (p.m - 1), ((ReferenceActivePhysicalStepMeasurability.decodeState
      (ReferenceActiveHorizonMeasurability.roundRecordCode r).2.1).activations j).val ≤
        t.val + 1 := by
    intro j
    rw [hstate, ← htime]
    exact r.input.active j
  let input : ReferenceActivePhysicalStep.RoundInput p rate :=
    ⟨ReferenceActivePhysicalStepMeasurability.decodeState
        (ReferenceActiveHorizonMeasurability.roundRecordCode r).2.1,
      z.1.2, ActualInitializationPhysicalStep.selectedRowIndex p z, t, hactive, rewards⟩
  have hinput : input = r.input := by
    apply roundInput_ext
    · exact hstate
    · exact hrows.symm
    · exact hselected.symm
    · exact htime.symm
    · exact hrewards.symm
  simp [downObservationFromRecordCode, hactive, input, hinput]

private theorem downObservationHistory_some_iff
    (i : I (p := p)) (z : Z (p := p)) (t : Fin p.T)
    (round : DownCode (p := p) (rate := rate)) :
    downObservationHistory rate rewards C_star C_h i z t = some round ↔
      ∃ r : Record (rate := rate),
        actualRecord rate rewards C_star C_h t z = some r ∧
        ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation r.input i = round := by
  unfold downObservationHistory
  rw [Option.bind_eq_some_iff]
  constructor
  · rintro ⟨code, hcode, hround⟩
    rcases (ReferenceInspectedPastRoundObservations.pastRoundObservations_some_iff
      rate rewards C_star C_h p.T (Nat.le_refl p.T) z t code).mp hcode with
      ⟨r, hr, hrecordCode⟩
    have hmap := downObservationFromRecordCode_actual rate rewards C_star C_h i z t r hr
    rw [hrecordCode] at hmap
    simp only [hmap, Option.some.injEq] at hround
    exact ⟨r, hr, hround⟩
  · rintro ⟨r, hr, hround⟩
    refine ⟨ReferenceActiveHorizonMeasurability.roundRecordCode r, ?_, ?_⟩
    · exact ReferenceInspectedPastRoundObservations.pastRoundObservations_some
        rate rewards C_star C_h p.T (Nat.le_refl p.T) z t r hr
    · rw [downObservationFromRecordCode_actual rate rewards C_star C_h i z t r hr]
      simp [hround]

private theorem awaitedDownAtCode_actual
    (r : Record (rate := rate)) (i : I (p := p)) (M : Word (p := p)) :
    awaitedDownAtCode rate
        (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation r.input i) i M ↔
      awaitedDownAt rate r i M := by
  have hdiag := ReferenceFirstLiveDownCompletionReadout.retained_diagnostics_reconstruct r i
  unfold awaitedDownAtCode awaitedDownAt
  rw [hdiag]
  constructor
  · rintro ⟨loggedCode, cutCode, hlogged, hcut, hcompare, hexpected, haccept⟩
    cases hinput : (r.output.followers i).downInput with
    | none => simp [hinput] at hlogged
    | some logged =>
      cases hcutActual : (r.output.followers i).down with
      | none => simp [hcutActual] at hcut
      | some cut =>
        have hloggedEq : FollowerDownMeasurability.followerStateCode rate logged = loggedCode := by
          simpa [hinput] using hlogged
        have hcutEq : ReferenceDownCompletedAmbiguityMeasurability.cutFields cut = cutCode := by
          simpa [hinput, hcutActual] using hcut
        subst loggedCode
        subst cutCode
        refine ⟨logged, cut, rfl, rfl, ?_, ?_, ?_⟩
        · simpa [ReferenceDownCompletedAmbiguityMeasurability.cutFields] using hcompare
        · simpa [ReferenceDownCompletedAmbiguityMeasurability.cutFields] using hexpected
        · change ReferenceDownReception.ordinaryLocalAcceptanceTest p rate r.input.time
            (FollowerDownMeasurability.followerStateOfCode rate
              (FollowerDownMeasurability.followerStateCode rate logged) [])
            (ReferenceDownReception.ordinaryParse p rate (some M)) at haccept
          simpa [ReferenceDownReception.ordinaryLocalAcceptanceTest,
            ReferencePrelaunchFollower.acceptedStart,
            FollowerDownMeasurability.followerStateOfCode,
            FollowerDownMeasurability.followerStateCode] using haccept
  · rintro ⟨logged, cut, hinput, hcutActual, hcompare, hexpected, haccept⟩
    refine ⟨FollowerDownMeasurability.followerStateCode rate logged,
      ReferenceDownCompletedAmbiguityMeasurability.cutFields cut, ?_, ?_, ?_, ?_, ?_⟩
    · simp [hinput]
    · simp [hcutActual]
    · simpa [ReferenceDownCompletedAmbiguityMeasurability.cutFields] using hcompare
    · simpa [ReferenceDownCompletedAmbiguityMeasurability.cutFields] using hexpected
    · change ReferenceDownReception.ordinaryLocalAcceptanceTest p rate r.input.time
        (FollowerDownMeasurability.followerStateOfCode rate
          (FollowerDownMeasurability.followerStateCode rate logged) [])
        (ReferenceDownReception.ordinaryParse p rate (some M)) at haccept
      change ReferenceDownReception.ordinaryLocalAcceptanceTest p rate r.input.time
        logged (ReferenceDownReception.ordinaryParse p rate (some M))
      simpa [ReferenceDownReception.ordinaryLocalAcceptanceTest,
        ReferencePrelaunchFollower.acceptedStart,
        FollowerDownMeasurability.followerStateOfCode,
        FollowerDownMeasurability.followerStateCode] using haccept

private theorem positiveEntriesFromDownCode_actual
    (r : Record (rate := rate)) (i : I (p := p)) :
    positiveEntriesFromDownCode rate
        (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation r.input i) =
      ReferenceFollowerDownDecoderReplay.actualDownPositives i [r] := by
  have hcall :
      (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation r.input i).2.2.1.map
          ReferenceDownCompletedAmbiguityMeasurability.decodeCall =
        ReferenceFollowerDownDecoderReplay.actualDownCall i r := by
    simpa only [ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation,
      ReferenceDownCompletedAmbiguityMeasurability.downCallObservation] using
      ReferenceDownCompletedAmbiguityMeasurability.downCallObservation_reconstructs i r
  unfold positiveEntriesFromDownCode
  cases hcode : ReferenceDownCompletedAmbiguityMeasurability.roundCallObservation r.input i with
  | none =>
      have hactual : ReferenceFollowerDownDecoderReplay.actualDownCall i r = none := by
        have htmp : none = ReferenceFollowerDownDecoderReplay.actualDownCall i r := by
          simpa [ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation, hcode]
            using hcall
        exact htmp.symm
      simp [ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation, hcode,
        ReferenceFollowerDownDecoderReplay.actualDownPositives,
        ReferenceFollowerDownDecoderReplay.actualDownCalls,
        ReferenceFollowerDownDecoderReplay.positiveCallEntries, hactual]
  | some callCode =>
      have hactual : ReferenceFollowerDownDecoderReplay.actualDownCall i r =
          some (ReferenceDownCompletedAmbiguityMeasurability.decodeCall callCode) := by
        have htmp : some (ReferenceDownCompletedAmbiguityMeasurability.decodeCall callCode) =
            ReferenceFollowerDownDecoderReplay.actualDownCall i r := by
          simpa [ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation, hcode]
            using hcall
        exact htmp.symm
      simp [ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation, hcode,
        ReferenceFollowerDownDecoderReplay.actualDownPositives,
        ReferenceFollowerDownDecoderReplay.actualDownCalls,
        ReferenceFollowerDownDecoderReplay.positiveCallEntries,
        ReferenceDownCompletedAmbiguityMeasurability.decodeCall, hactual]

private theorem fixedAwaitedDownFailureAt_iff_code
    (z : Z (p := p)) (t : Fin p.T) :
    fixedAwaitedDownFailureAt rate rewards C_star C_h z t ↔
      fixedAwaitedDownFailureCodeAt rate
        (fun i => downObservationHistory rate rewards C_star C_h i z)
        (selectedChannelHistory z) t := by
  constructor
  · rintro ⟨r, i, M, W, a, hrt, hbatch, hat, hmulti, hentries, hchannels⟩
    have hroundT := (downObservationHistory_some_iff rate rewards C_star C_h i z t
      (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation r.input i)).2
      ⟨r, hrt, rfl⟩
    refine ⟨i, M, W, a, ?_, hat, hmulti, ?_, ?_⟩
    · change (downObservationHistory rate rewards C_star C_h i z t).bind
        ReferenceFirstLiveDownCompletionReadout.completedBatchCode = some W
      simpa [hroundT, ReferenceFirstLiveDownCompletionReadout.completedBatchCode_actual]
        using hbatch
    · intro e he
      rcases hentries e he with ⟨hb, ht, heq, re, hre, hpos, haw⟩
      have hroundE := (downObservationHistory_some_iff rate rewards C_star C_h i z e.time
        (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation re.input i)).2
          ⟨re, hre, rfl⟩
      refine ⟨hb, ht, heq, ?_⟩
      refine ⟨ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation re.input i,
        ?_, ?_, ?_⟩
      · change downObservationHistory rate rewards C_star C_h i z e.time = _
        exact hroundE
      · rw [positiveEntriesFromDownCode_actual rate re i]
        exact hpos
      · exact (awaitedDownAtCode_actual rate re i M).mpr haw
    · intro v hb hv hchannel
      have hchannelActual :
          ReferenceSelectedAffinePairLaw.selectedChannel p
            ((z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)).2 v).1 =
              some (0, i) := by
        simpa [selectedChannelHistory, ReferenceSelectedAffinePairLaw.selector] using hchannel
      rcases hchannels v hb hv hchannelActual with ⟨rv, hrv, haw⟩
      have hroundV := (downObservationHistory_some_iff rate rewards C_star C_h i z v
        (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation rv.input i)).2
          ⟨rv, hrv, rfl⟩
      refine ⟨ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation rv.input i,
        ?_, ?_⟩
      · change downObservationHistory rate rewards C_star C_h i z v = _
        exact hroundV
      · exact (awaitedDownAtCode_actual rate rv i M).mpr haw
  · rintro ⟨i, M, W, a, hbatch, hat, hmulti, hentries, hchannels⟩
    rcases Option.bind_eq_some_iff.mp hbatch with ⟨roundT, hroundT, hbatchCode⟩
    change downObservationHistory rate rewards C_star C_h i z t = some roundT at hroundT
    rcases (downObservationHistory_some_iff rate rewards C_star C_h i z t roundT).mp
      hroundT with ⟨r, hrt, hroundTActual⟩
    have hbatchActual :
        ReferenceFirstLiveDownCompletionReadout.completedDownBatch r i = some W := by
      rw [← hroundTActual] at hbatchCode
      rw [ReferenceFirstLiveDownCompletionReadout.completedBatchCode_actual] at hbatchCode
      exact hbatchCode
    refine ⟨r, i, M, W, a, hrt, hbatchActual, hat, hmulti, ?_, ?_⟩
    · intro e he
      rcases hentries e he with ⟨hb, ht, heq, roundE, hroundE, hpos, haw⟩
      change downObservationHistory rate rewards C_star C_h i z e.time = some roundE at hroundE
      rcases (downObservationHistory_some_iff rate rewards C_star C_h i z e.time roundE).mp
        hroundE with ⟨re, hre, hroundEActual⟩
      refine ⟨hb, ht, heq, re, hre, ?_, ?_⟩
      · rw [← hroundEActual, positiveEntriesFromDownCode_actual] at hpos
        exact hpos
      · rw [← hroundEActual] at haw
        exact (awaitedDownAtCode_actual rate re i M).mp haw
    · intro v hb hv hchannel
      rcases hchannels v hb hv hchannel with ⟨roundV, hroundV, haw⟩
      change downObservationHistory rate rewards C_star C_h i z v = some roundV at hroundV
      rcases (downObservationHistory_some_iff rate rewards C_star C_h i z v roundV).mp
        hroundV with ⟨rv, hrv, hroundVActual⟩
      refine ⟨rv, hrv, ?_⟩
      rw [← hroundVActual] at haw
      exact (awaitedDownAtCode_actual rate rv i M).mp haw

private theorem measurable_selectedChannelHistory (v : Fin p.T) :
    @Measurable (Z (p := p)) (Option (Channel (p := p)))
      (inferInstance : MeasurableSpace (Z (p := p)))
      (ReferenceInitializationMeasurability.optionCountableMeasurableSpace
        (Channel (p := p)))
      (fun z => selectedChannelHistory z v) := by
  let : MeasurableSpace (Option (Channel (p := p))) :=
    ReferenceInitializationMeasurability.optionCountableMeasurableSpace (Channel (p := p))
  let index : Z (p := p) → Fin (ConstructorDimensions.M p) :=
    fun z => ActualInitializationPhysicalStep.selectedRowIndex p z
  have hindex : Measurable index := by
    exact (PrivateSourceStreams.measurable_coordinatorIndex p).comp
      (measurable_snd.comp (measurable_fst.comp measurable_snd))
  let rows : Z (p := p) → CompletePublicTable.CompleteRows p := fun z => z.1.2
  have hrows : Measurable rows := measurable_snd.comp measurable_fst
  have hrowEval : Measurable (fun z : Z (p := p) => rows z (index z)) := by
    have heval : Measurable
        (fun x : CompletePublicTable.CompleteRows p × Fin (ConstructorDimensions.M p) => x.1 x.2) := by
      apply measurable_from_prod_countable_left
      intro j
      exact measurable_pi_apply j
    exact heval.comp (hrows.prodMk hindex)
  let learningRow : Z (p := p) → ContinuousLearningRows.LearningRow p :=
    fun z => (rows z (index z)).2
  have hlearning : Measurable learningRow :=
    measurable_snd.comp hrowEval
  have htimeEval : Measurable (fun z : Z (p := p) => learningRow z v) := by
    have heval : Measurable
        (fun x : ContinuousLearningRows.LearningRow p × Fin p.T => x.1 x.2) := by
      apply measurable_from_prod_countable_left
      intro t
      exact measurable_pi_apply t
    exact heval.comp (hlearning.prodMk measurable_const)
  have hslice : Measurable (fun z : Z (p := p) => (learningRow z v).1) :=
    measurable_fst.comp htimeEval
  have hselected := (ReferenceSelectedAffinePairLaw.measurable_selectedChannel p).comp hslice
  change @Measurable (Z (p := p)) (Option (Channel (p := p)))
    (inferInstance : MeasurableSpace (Z (p := p)))
    (ReferenceInitializationMeasurability.optionCountableMeasurableSpace
      (Channel (p := p)))
    (fun z : Z (p := p) =>
      ReferenceSelectedAffinePairLaw.selectedChannel p (learningRow z v).1)
  exact hselected

private abbrev ReadoutCodeData :=
  (I (p := p) → Fin p.T → Option (DownCode (p := p) (rate := rate))) ×
    (Fin p.T → Option (Channel (p := p)))

private theorem measurableSet_pi_singleton {ι A : Type*} [Finite ι]
    [MeasurableSpace A] [MeasurableSingletonClass A] (x : ι → A) :
    MeasurableSet {x} := by
  have heq : Set.univ.pi (fun v => {x v}) = {x} := by
    ext y
    simp only [Set.mem_pi, Set.mem_univ, Set.mem_singleton_iff]
    constructor
    · intro hy
      funext v
      exact hy v trivial
    · intro h v _
      exact congrFun h v
  rw [← heq]
  exact MeasurableSet.univ_pi (fun v => measurableSet_singleton (x v))

local instance {ι A : Type*} [Finite ι] [MeasurableSpace A]
    [MeasurableSingletonClass A] : MeasurableSingletonClass (ι → A) :=
  ⟨measurableSet_pi_singleton⟩

/-- Borel measurability of the exact fixed awaited DOWN event on the original
source carrier, via its countable diagnostic and selected-channel code. -/
theorem fixedAwaitedDownFailureAt_borel (t : Fin p.T) :
    MeasurableSet {z : Z (p := p) |
      fixedAwaitedDownFailureAt rate rewards C_star C_h z t} := by
  let : MeasurableSpace (Option (Channel (p := p))) :=
    ReferenceInitializationMeasurability.optionCountableMeasurableSpace (Channel (p := p))
  let codeMap : Z (p := p) → ReadoutCodeData (p := p) (rate := rate) :=
    fun z => ((fun i => downObservationHistory rate rewards C_star C_h i z),
      selectedChannelHistory z)
  have hh : Measurable (fun z : Z (p := p) =>
      fun i => downObservationHistory rate rewards C_star C_h i z) := by
    apply measurable_pi_iff.mpr
    intro i
    exact measurable_downObservationHistory rate rewards C_star C_h i
  have hc : Measurable (selectedChannelHistory (p := p)) := by
    apply measurable_pi_iff.mpr
    intro v
    exact measurable_selectedChannelHistory v
  let event : Set (ReadoutCodeData (p := p) (rate := rate)) :=
    {x | fixedAwaitedDownFailureCodeAt rate x.1 x.2 t}
  let : Countable (Fin p.T → Option (DownCode (p := p) (rate := rate))) := inferInstance
  let : Countable (I (p := p) → Fin p.T → Option (DownCode (p := p) (rate := rate))) :=
    inferInstance
  let : Countable (Fin p.T → Option (Channel (p := p))) := inferInstance
  have hevent : MeasurableSet event := event.to_countable.measurableSet
  have heq : {z : Z (p := p) |
      fixedAwaitedDownFailureAt rate rewards C_star C_h z t} = codeMap ⁻¹' event := by
    ext z
    exact fixedAwaitedDownFailureAt_iff_code rate rewards C_star C_h z t
  rw [heq]
  exact hevent.preimage (hh.prodMk hc)

private def savedWrongAtFlag (t : Fin p.T) (z : Z (p := p)) : Bool :=
  (ReferenceInspectedPastRoundObservations.pastRoundObservations rate rewards C_star C_h
    p.T (Nat.le_refl p.T) z t).elim false
      ReferenceSavedWrongUniqueMeasurability.savedWrongCode

private theorem savedWrongAtFlag_iff (t : Fin p.T) (z : Z (p := p)) :
    savedWrongAtFlag rate rewards C_star C_h t z = true ↔
      ∃ r : Record (rate := rate), actualRecord rate rewards C_star C_h t z = some r ∧
        ReferenceActiveStoppedPrefixCoupling.saved_wrong_unique_accepted r := by
  change ((actualRecord rate rewards C_star C_h t z).map
    ReferenceActiveHorizonMeasurability.roundRecordCode).elim false
      ReferenceSavedWrongUniqueMeasurability.savedWrongCode = true ↔ _
  cases hr : actualRecord rate rewards C_star C_h t z with
  | none => simp
  | some r =>
    simp only [Option.map_some, Option.elim_some,
      ReferenceSavedWrongUniqueMeasurability.savedWrongCode_roundRecord_iff,
      Option.some.injEq]
    exact ⟨fun h => ⟨r, rfl, h⟩, fun ⟨_, h, hw⟩ => h.symm ▸ hw⟩

private theorem measurable_savedWrongAtFlag (t : Fin p.T) :
    Measurable (savedWrongAtFlag rate rewards C_star C_h t) := by
  have h : Measurable (fun code : Option (RoundCode (p := p) (rate := rate)) =>
      code.elim false ReferenceSavedWrongUniqueMeasurability.savedWrongCode) := by
    have hsum := (ReferenceSavedWrongUniqueMeasurability.measurable_savedWrongCode
      (p := p) (rate := rate)).sumElim
        (measurable_const : Measurable (fun _ : PUnit => false))
    convert hsum.comp (comap_measurable (Equiv.optionEquivSumPUnit
      (RoundCode (p := p) (rate := rate)))) using 1
    funext code
    cases code <;> rfl
  exact h.comp ((measurable_pi_iff.mp
    (ReferenceInspectedPastRoundObservations.measurable_pastRoundObservations
      rate rewards C_star C_h p.T (Nat.le_refl p.T))) t)

/-- The three literal failure branches are Borel on the original data. The UP
branch is exactly the existing V2 predicate. -/
theorem failureAt_borel (t : Fin p.T) :
    MeasurableSet {z : Z (p := p) | failureAt rate rewards C_star C_h z t} := by
  have hs : MeasurableSet {z : Z (p := p) |
      ∃ r : Record (rate := rate), actualRecord rate rewards C_star C_h t z = some r ∧
        ReferenceActiveStoppedPrefixCoupling.saved_wrong_unique_accepted r} := by
    have h := (measurable_savedWrongAtFlag rate rewards C_star C_h t)
      (measurableSet_singleton true)
    simpa only [Set.preimage, Set.mem_singleton_iff,
      savedWrongAtFlag_iff] using h
  exact hs.union ((fixedAwaitedDownFailureAt_borel rate rewards C_star C_h t).union
    (ReferenceCollectionUpFailureReadoutV2.fixedAwaitedUpFailureAt_borel
      rate rewards C_star C_h t))

private theorem preparedOutput_tail_eq_of_current
    (i : Fin (p.m - 1)) (activation : ReferencePrelaunchFollower.Activation p)
    (incoming : FollowerPrepareJointMeasurability.IncomingConfiguration p rate)
    (row row' : CompletePublicTable.CompleteRow p)
    (time : FollowerPrepareJointMeasurability.ActiveCalendarTime p activation)
    (hc : row.2 time.val = row'.2 time.val) :
    (FollowerPrepareJointMeasurability.prepareOutputOnInput rate i activation
      (FollowerPrepareJointMeasurability.assemblePrepareInput incoming row time)).2 =
    (FollowerPrepareJointMeasurability.prepareOutputOnInput rate i activation
      (FollowerPrepareJointMeasurability.assemblePrepareInput incoming row' time)).2 := by
  cases incoming with
  | none => rfl
  | some data =>
    rcases data with ⟨⟨index, values⟩, memory⟩
    have hp := ReferenceActiveTemporalCausality.prepare_projections_eq_of_current
      i activation time.property
      (FollowerLifecycleMeasurability.localConfigurationOfCode rate
        (some (index.1, memory))
        (FollowerDownJointMeasurability.bufferFromSkeletonAndScalars index.2.2 values)) hc
    have hcode := congrArg (fun pair =>
      FollowerLifecycleMeasurability.PreparedRoundCode.mk pair.1
        (FollowerLifecycleMeasurability.localConfigurationCode pair.2)) hp
    change FollowerLifecycleMeasurability.prepareRoundCodeAt rate i activation
        (some (index.1, memory)) index.2.2 row time values =
      FollowerLifecycleMeasurability.prepareRoundCodeAt rate i activation
        (some (index.1, memory)) index.2.2 row' time values at hcode
    simp only [FollowerPrepareJointMeasurability.prepareOutputOnInput,
      FollowerPrepareJointMeasurability.assemblePrepareInput,
      FollowerPrepareJointMeasurability.prepareRoundCodeOnInput,
      FollowerPrepareJointMeasurability.prepareOutputConfiguration, hcode]

private theorem preparedRegisters_eq_of_current
    (x y : ReferenceActivePhysicalStep.RoundInput p rate) (i : I (p := p))
    (hstate : x.state = y.state) (htime : x.time = y.time)
    (hcurrent : x.row.2 x.time = y.row.2 y.time) :
    ReferenceDownCompletedAmbiguityMeasurability.preparedRegisters x i =
      ReferenceDownCompletedAmbiguityMeasurability.preparedRegisters y i := by
  rcases x with ⟨sx, rx, jx, tx, ax, wx⟩
  rcases y with ⟨sy, ry, jy, ty, ay, wy⟩
  dsimp only at hstate htime
  cases hstate
  cases htime
  have htail := preparedOutput_tail_eq_of_current (p := p) (rate := rate)
    i (sx.activations i)
    (FollowerPrepareJointMeasurability.incomingOfLocalConfiguration rate (sx.followers i))
    (rx jx) (ry jy) ⟨tx, ax i⟩ hcurrent
  exact congrArg (fun output =>
    ReferenceDownCompletedAmbiguityMeasurability.incomingRegisters output.2) htail

private theorem roundDownObservation_eq_of_temporal_reads
    (x y : ReferenceActivePhysicalStep.RoundInput p rate) (i : Fin (p.m - 1))
    (hstate : x.state = y.state) (htime : x.time = y.time)
    (hcurrent : x.row.2 x.time = y.row.2 y.time)
    (hwhole : ReferenceActiveStepCompositionMeasurability.wholeStepCode x =
      ReferenceActiveStepCompositionMeasurability.wholeStepCode y) :
    ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation x i =
      ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation y i := by
  have hprepared := preparedRegisters_eq_of_current rate x y i hstate htime hcurrent
  have hown : ReferenceDownCompletedAmbiguityMeasurability.ownGrid x i =
      ReferenceDownCompletedAmbiguityMeasurability.ownGrid y i := by
    unfold ReferenceDownCompletedAmbiguityMeasurability.ownGrid
    rw [hwhole]
  have hcurrent' : x.row.2 y.time = y.row.2 y.time := by
    calc
      x.row.2 y.time = x.row.2 x.time := congrArg (fun time => x.row.2 time) htime.symm
      _ = y.row.2 y.time := hcurrent
  have hdownSelected' : ActiveFollowerDownAcceptance.downSelected p i x.row y.time =
      ActiveFollowerDownAcceptance.downSelected p i y.row y.time := by
    unfold ActiveFollowerDownAcceptance.downSelected
    rw [hcurrent']
  have hcall : ReferenceDownCompletedAmbiguityMeasurability.roundCallObservation x i =
      ReferenceDownCompletedAmbiguityMeasurability.roundCallObservation y i := by
    unfold ReferenceDownCompletedAmbiguityMeasurability.roundCallObservation
    rw [htime, hprepared, hdownSelected', hcurrent', hown]
  have hdiagnostic : ReferenceDownCompletedAmbiguityMeasurability.diagnosticProjection
      ((ReferenceActiveStepCompositionMeasurability.wholeStepCode x).2.1 i) =
      ReferenceDownCompletedAmbiguityMeasurability.diagnosticProjection
        ((ReferenceActiveStepCompositionMeasurability.wholeStepCode y).2.1 i) := by
    rw [hwhole]
  unfold ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation
  rw [htime, hown, hcall, hdiagnostic]

private def actualReadoutCode (r : Record (rate := rate)) :=
  (ReferenceActiveHorizonMeasurability.roundRecordCode r,
    fun i : I (p := p) =>
      ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation r.input i)

private theorem actualReadoutCode_map_eq_of_prefix
    (control0 : ContinuousLearningRows.TimeControl p) (n : ℕ)
    (v : Fin p.T) (hvn : v.val < n) (z : Z (p := p)) :
    (actualRecord rate rewards C_star C_h v z).map
        (actualReadoutCode rate) =
      (actualRecord rate rewards C_star C_h v (ReferenceSourcePrefixHistoryFiltration.sourcePrefix
        control0 n z)).map
        (actualReadoutCode rate) := by
  have hin : ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h v z =
      ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h v
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n z) := by
    calc
      _ = ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h v
          (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 v.val z) :=
            ReferenceSourcePrefixHistoryFiltration.incoming_factor rate rewards C_star C_h
              control0 v z
      _ = ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h v
          (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 v.val
            (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n z)) := by
              rw [ReferenceSourcePrefixHistoryFiltration.sourcePrefix_sourcePrefix
                control0 v.val n (by omega)]
      _ = _ := (ReferenceSourcePrefixHistoryFiltration.incoming_factor
          rate rewards C_star C_h control0 v
          (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n z)).symm
  cases hr : actualRecord rate rewards C_star C_h v z with
  | none =>
      cases hr' : actualRecord rate rewards C_star C_h v
          (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n z) with
      | none => rfl
      | some r' =>
          have : False := by
            simp [ReferenceSourcePrefixHistoryFiltration.incoming, hr, hr'] at hin
          exact this.elim
  | some r =>
      cases hr' : actualRecord rate rewards C_star C_h v
          (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n z) with
      | none =>
          have : False := by
            simp [ReferenceSourcePrefixHistoryFiltration.incoming, hr, hr'] at hin
          exact this.elim
      | some r' =>
          have henc : ReferenceActivePhysicalStepMeasurability.encodeState r.input.state =
              ReferenceActivePhysicalStepMeasurability.encodeState r'.input.state := by
            simpa [ReferenceSourcePrefixHistoryFiltration.incoming, hr, hr'] using hin
          have hstate : r.input.state = r'.input.state := by
            have h := congrArg ReferenceActivePhysicalStepMeasurability.decodeState henc
            simpa only [ReferenceActivePhysicalStepMeasurability.decodeState_encodeState] using h
          obtain ⟨hrows, hselected, htime, hrewards⟩ :=
            actualRecord_input_fields rate rewards C_star C_h v z r hr
          obtain ⟨hrows', hselected', htime', hrewards'⟩ :=
            actualRecord_input_fields rate rewards C_star C_h v
              (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n z) r' hr'
          have hselectedEq : r.input.selected = r'.input.selected := by
            rw [hselected, hselected',
              ReferenceSourcePrefixHistoryFiltration.sourcePrefix_selected]
          have hcurrent : r.input.row.2 r.input.time = r'.input.row.2 r'.input.time := by
            simp [ReferenceActivePhysicalStep.RoundInput.row, hrows, hrows', hselected,
              hselected', htime, htime', ReferenceSourcePrefixHistoryFiltration.sourcePrefix_selected,
              ReferenceSourcePrefixHistoryFiltration.sourcePrefix_control, hvn]
          have hpast : ∀ u : Fin p.T, u.val < r.input.time.val →
              (r.input.row.2 u).1 ContinuousControlSlice.Label.prop =
                (r'.input.row.2 u).1 ContinuousControlSlice.Label.prop := by
            intro u hu
            have hu' : u.val < n := by rw [htime] at hu; omega
            simp [ReferenceActivePhysicalStep.RoundInput.row, hrows, hrows', hselected,
              hselected', ReferenceSourcePrefixHistoryFiltration.sourcePrefix_selected,
              ReferenceSourcePrefixHistoryFiltration.sourcePrefix_control, hu']
          have hcode := ReferenceInspectedPastRoundObservations.roundRecordCode_eq_of_temporal_reads
            (rate := rate) r.input r'.input hstate hselectedEq (htime.trans htime'.symm)
            (hrewards.trans hrewards'.symm) hcurrent hpast
          have hrecordCode :
              ReferenceActiveHorizonMeasurability.roundRecordCode r =
                ReferenceActiveHorizonMeasurability.roundRecordCode r' := by
            rcases r with ⟨inputL, outputL, houtL⟩
            rcases r' with ⟨inputR, outputR, houtR⟩
            have houtputL : outputL = ReferenceActivePhysicalStep.step inputL := houtL
            have houtputR : outputR = ReferenceActivePhysicalStep.step inputR := houtR
            subst outputL
            subst outputR
            simpa using hcode
          have hwhole := congrArg (fun code => code.2.2) hrecordCode
          have hdown := funext fun i : I (p := p) =>
            roundDownObservation_eq_of_temporal_reads rate r.input r'.input i hstate
              (htime.trans htime'.symm) hcurrent hwhole
          simp only [Option.map_some, actualReadoutCode, Option.some.injEq,
            Prod.mk.injEq]
          exact ⟨hrecordCode, hdown⟩

private theorem downObservationHistory_eq_map
    (i : I (p := p)) (z : Z (p := p)) (t : Fin p.T) :
    downObservationHistory rate rewards C_star C_h i z t =
      (actualRecord rate rewards C_star C_h t z).map
        (fun r => ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation r.input i) := by
  change ((actualRecord rate rewards C_star C_h t z).map
    ReferenceActiveHorizonMeasurability.roundRecordCode).bind
      (downObservationFromRecordCode rate rewards i z t) = _
  cases hr : actualRecord rate rewards C_star C_h t z with
  | none => rfl
  | some r =>
    exact downObservationFromRecordCode_actual rate rewards C_star C_h i z t r hr

private theorem downObservationHistory_eq_of_prefix
    (control0 : ContinuousLearningRows.TimeControl p) (n : ℕ)
    (v : Fin p.T) (hvn : v.val < n) (z : Z (p := p)) (i : I (p := p)) :
    downObservationHistory rate rewards C_star C_h i z v =
      downObservationHistory rate rewards C_star C_h i
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n z) v := by
  have h := actualReadoutCode_map_eq_of_prefix rate rewards C_star C_h control0 n v hvn z
  rw [downObservationHistory_eq_map, downObservationHistory_eq_map]
  simpa only [Option.map_map, actualReadoutCode, Function.comp_def] using
    congrArg (fun o => o.map (fun code => code.2 i)) h

private theorem savedWrongAtFlag_eq_of_prefix
    (control0 : ContinuousLearningRows.TimeControl p) (n : ℕ)
    (v : Fin p.T) (hvn : v.val < n) (z : Z (p := p)) :
    savedWrongAtFlag rate rewards C_star C_h v z =
      savedWrongAtFlag rate rewards C_star C_h v
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n z) := by
  have h := actualReadoutCode_map_eq_of_prefix rate rewards C_star C_h control0 n v hvn z
  have hcodes := congrArg (fun o => o.map Prod.fst) h
  change ((actualRecord rate rewards C_star C_h v z).map
    ReferenceActiveHorizonMeasurability.roundRecordCode).elim false
      ReferenceSavedWrongUniqueMeasurability.savedWrongCode =
    ((actualRecord rate rewards C_star C_h v
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n z)).map
        ReferenceActiveHorizonMeasurability.roundRecordCode).elim false
          ReferenceSavedWrongUniqueMeasurability.savedWrongCode
  simpa only [Option.map_map, actualReadoutCode, Function.comp_def] using
    congrArg (fun o => o.elim false ReferenceSavedWrongUniqueMeasurability.savedWrongCode) hcodes

private theorem selectedChannelHistory_eq_of_prefix
    (control0 : ContinuousLearningRows.TimeControl p) (n : ℕ)
    (v : Fin p.T) (hvn : v.val < n) (z : Z (p := p)) :
    selectedChannelHistory (p := p) z v = selectedChannelHistory (p := p)
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n z) v := by
  simp [selectedChannelHistory, ReferenceSelectedAffinePairLaw.selector,
    ReferenceSourcePrefixHistoryFiltration.sourcePrefix_selected,
    ReferenceSourcePrefixHistoryFiltration.sourcePrefix_control, hvn]

private theorem fixedAwaitedDownFailureCodeAt_congr_on_past
    (history history' : I (p := p) → Fin p.T → Option (DownCode (p := p) (rate := rate)))
    (channels channels' : Fin p.T → Option (Channel (p := p))) (t : Fin p.T)
    (hcode : ∀ i v, v.val ≤ t.val → history i v = history' i v)
    (hchannel : ∀ v : Fin p.T, v.val ≤ t.val → channels v = channels' v) :
    fixedAwaitedDownFailureCodeAt rate history channels t ↔
      fixedAwaitedDownFailureCodeAt rate history' channels' t := by
  have forward : ∀
      (h h' : I (p := p) → Fin p.T → Option (DownCode (p := p) (rate := rate)))
      (c c' : Fin p.T → Option (Channel (p := p))),
      (∀ i v, v.val ≤ t.val → h i v = h' i v) →
      (∀ v, v.val ≤ t.val → c v = c' v) →
      fixedAwaitedDownFailureCodeAt rate h c t →
        fixedAwaitedDownFailureCodeAt rate h' c' t := by
    intro h h' c c' hh hc
    rintro ⟨i, M, W, a, hbatch, ha, hmulti, hentries, hinterval⟩
    refine ⟨i, M, W, a, ?_, ha, hmulti, ?_, ?_⟩
    · simpa only [hh i t (Nat.le_refl _)] using hbatch
    · intro e he
      rcases hentries e he with ⟨hb, ht, heq, round, hr, hpos, haw⟩
      exact ⟨hb, ht, heq, round, (hh i e.time ht).symm.trans hr, hpos, haw⟩
    · intro v hb ht hselected
      rcases hinterval v hb ht ((hc v ht).trans hselected) with ⟨round, hr, haw⟩
      exact ⟨round, (hh i v ht).symm.trans hr, haw⟩
  exact ⟨forward history history' channels channels' hcode hchannel,
    forward history' history channels' channels
      (fun i v hv => (hcode i v hv).symm) (fun v hv => (hchannel v hv).symm)⟩

private theorem fixedAwaitedDownFailureAt_factor_on_past
    (control0 : ContinuousLearningRows.TimeControl p) (n : ℕ)
    (t : Fin p.T) (htn : t.val < n) (z : Z (p := p)) :
    fixedAwaitedDownFailureAt rate rewards C_star C_h z t ↔
      fixedAwaitedDownFailureAt rate rewards C_star C_h
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n z) t := by
  rw [fixedAwaitedDownFailureAt_iff_code, fixedAwaitedDownFailureAt_iff_code]
  exact fixedAwaitedDownFailureCodeAt_congr_on_past rate _ _ _ _ t
    (fun i v hv => downObservationHistory_eq_of_prefix rate rewards C_star C_h
      control0 n v (by omega) z i)
    (fun v hv => selectedChannelHistory_eq_of_prefix control0 n v (by omega) z)

private theorem pastFailureFlag_eq_or (n : ℕ) (z : Z (p := p)) :
    pastFailureFlag rate rewards C_star C_h n z =
      (decide (∃ t : Fin p.T, t.val < n ∧
        (savedWrongAtFlag rate rewards C_star C_h t z = true ∨
          fixedAwaitedDownFailureAt rate rewards C_star C_h z t)) ||
        ReferenceCollectionUpFailureReadoutV2.pastUpFailureFlag rate rewards C_star C_h n z) := by
  apply Bool.eq_iff_iff.mpr
  simp only [pastFailureFlag, failureAt, Bool.or_eq_true, decide_eq_true_eq,
    ReferenceCollectionUpFailureReadoutV2.pastUpFailureFlag,
    savedWrongAtFlag_iff, and_or_left, exists_or]
  exact or_assoc.symm

/-- The flag factors through the original whole-source prefix, retaining every
selected zero-feedback point at offsets strictly less than the scan index. -/
theorem pastFailureFlag_factor (control0 : ContinuousLearningRows.TimeControl p)
    (n : ℕ) (z : Z (p := p)) :
    pastFailureFlag rate rewards C_star C_h n z =
      pastFailureFlag rate rewards C_star C_h n
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n z) := by
  rw [pastFailureFlag_eq_or, pastFailureFlag_eq_or,
    ReferenceCollectionUpFailureReadoutV2.pastUpFailureFlag_factor
      rate rewards C_star C_h control0 n z]
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  apply exists_congr
  intro t
  apply and_congr_right
  intro ht
  rw [savedWrongAtFlag_eq_of_prefix rate rewards C_star C_h control0 n t ht z]
  exact or_congr Iff.rfl
    (fixedAwaitedDownFailureAt_factor_on_past rate rewards C_star C_h control0 n t ht z)

private theorem measurable_pastFailureFlag (n : ℕ) :
    Measurable (pastFailureFlag rate rewards C_star C_h n) := by
  apply measurable_to_bool
  change MeasurableSet {z : Z (p := p) | pastFailureFlag rate rewards C_star C_h n z = true}
  simp only [pastFailureFlag, decide_eq_true_eq]
  have heq : {z : Z (p := p) | ∃ t : Fin p.T, t.val < n ∧
      failureAt rate rewards C_star C_h z t} =
      ⋃ t : Fin p.T, {z : Z (p := p) | t.val < n ∧
        failureAt rate rewards C_star C_h z t} := by
    ext z
    simp
  rw [heq]
  exact MeasurableSet.iUnion fun t => by
    by_cases ht : t.val < n
    · simpa only [ht, true_and] using failureAt_borel rate rewards C_star C_h t
    · simp [ht]

/-- Predictability in the unchanged original source-prefix filtration. No
history, trace, success, law, or measurability premise is supplied. -/
theorem pastFailureFlag_adapted (control0 : ContinuousLearningRows.TimeControl p)
    (n : ℕ) :
    Measurable[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (n + 1)]
      (pastFailureFlag rate rewards C_star C_h n) := by
  have hambient := measurable_pastFailureFlag rate rewards C_star C_h n
  have hfactor : pastFailureFlag rate rewards C_star C_h n =
      pastFailureFlag rate rewards C_star C_h n ∘
        ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n := by
    funext z
    exact pastFailureFlag_factor rate rewards C_star C_h control0 n z
  rw [hfactor, ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration_succ,
    measurable_iff_comap_le, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono hambient.comap_le

/-- The executed actual DOWN call fields underlying every awaited diagnostic,
including the zero-feedback branch, are the ones from the retained receiver
transition. -/
theorem awaitedDownAt_retained_call_fields
    (r : Record (rate := rate)) (i : I (p := p)) (M : Word (p := p))
    (hawait : awaitedDownAt rate r i M) :
    ∃ logged cut,
      (r.output.followers i).downInput = some logged ∧
      (r.output.followers i).down = some cut ∧
      ActiveFollowerDownAcceptance.downSelected p i r.input.row r.input.time ∧
      logged.status = .unoccupied ∧
      ActiveFollowerDownAcceptance.registerInputDomain p rate logged ∧
      ActiveFollowerDownAcceptance.decoderInputDomain p logged.downBatch ∧
      ActiveFollowerDownAcceptance.bufferInputDomain p logged.buffer ∧
      cut.raw = (ActiveFollowerDownAcceptance.currentDecodeStep p i r.input.row
        r.input.time (ReferenceFollowerDownDecoderReplay.preparedOwnObservation r i)
        rate logged).2 ∧
      cut.expectedWord = ReferenceDownReception.expectedDownFlatWord
        r.output.preparation.coordinator.downView i r.input.row r.input.time ∧
      cut.ordinaryParse = ReferenceDownReception.ordinaryParse p rate cut.raw ∧
      cut.ordinaryAcceptance = ReferenceDownReception.ordinaryLocalAcceptanceTest
        p rate r.input.time logged
        (ReferenceDownReception.ordinaryParse p rate cut.raw) ∧
      cut.rawComparison = some (decide (cut.raw = cut.expectedWord)) := by
  rcases hawait with ⟨logged, cut, hinput, hcut, hcompare, _, _⟩
  exact ⟨logged, cut, hinput, hcut,
    ReferenceFirstLiveDownCompletionReadout.retained_call_fields
      r i logged cut hinput hcut hcompare⟩

/-- The awaited `Word` is exactly the sender's retained expected word. This
uses the executed branch and does not require positive feedback. -/
theorem awaitedDownAt_expected_sender_word
    (r : Record (rate := rate)) (i : I (p := p)) (M : Word (p := p))
    (hawait : awaitedDownAt rate r i M) :
    ReferenceDownReception.expectedDownFlatWord
      r.output.preparation.coordinator.downView i r.input.row r.input.time = some M := by
  rcases hawait with ⟨logged, cut, hinput, hcut, hcompare, hexpected, _⟩
  have hfields := ReferenceFirstLiveDownCompletionReadout.retained_call_fields
    r i logged cut hinput hcut hcompare
  exact hfields.2.2.2.2.2.2.1.symm.trans hexpected

/-- Every awaited word parses and strictly exceeds the actual receiver's last
accepted DOWN start at this very deciding call. -/
theorem awaitedDownAt_strict_accepted_start
    (r : Record (rate := rate)) (i : I (p := p)) (M : Word (p := p))
    (hawait : awaitedDownAt rate r i M) :
    ∃ (logged : ReferencePrelaunchFollower.State p rate.eta)
      (D : OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta)),
      (r.output.followers i).downInput = some logged ∧
      ReferenceDownReception.ordinaryParse p rate (some M) = some D ∧
      ReferencePrelaunchFollower.acceptedStart logged < D.val.sigma ∧
      D.val.sigma ≤ r.input.time.val + 1 := by
  rcases hawait with ⟨logged, cut, hinput, hcut, hcompare, hexpected, haccept⟩
  cases hp : ReferenceDownReception.ordinaryParse p rate (some M) with
  | none => simp only [ReferenceDownReception.ordinaryLocalAcceptanceTest, hp] at haccept
  | some D =>
    exact ⟨logged, D, hinput, rfl, by
      simpa only [ReferenceDownReception.ordinaryLocalAcceptanceTest, hp,
        OrdinaryMessageCodec.acceptDown] using haccept⟩

/-- A repeated old accepted DOWN word cannot satisfy the awaited test at the
current receiver call, even when the channel is selected again. -/
theorem not_awaitedDownAt_of_old_accepted_start
    (r : Record (rate := rate)) (i : I (p := p)) (M : Word (p := p))
    (logged : ReferencePrelaunchFollower.State p rate.eta)
    (D : OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (hinput : (r.output.followers i).downInput = some logged)
    (hparse : ReferenceDownReception.ordinaryParse p rate (some M) = some D)
    (hold : D.val.sigma ≤ ReferencePrelaunchFollower.acceptedStart logged) :
    ¬ awaitedDownAt rate r i M := by
  intro haw
  rcases awaitedDownAt_strict_accepted_start rate r i M haw with
    ⟨logged', D', hinput', hparse', hstrict, _⟩
  have hl : logged' = logged := Option.some.inj (hinput'.symm.trans hinput)
  have hd : D' = D := Option.some.inj (hparse'.symm.trans hparse)
  subst logged'
  subst D'
  exact (not_lt_of_ge hold) hstrict

/-- The empty calendar scan has no strict-past failure. -/
theorem pastFailureFlag_zero (z : Z (p := p)) :
    pastFailureFlag rate rewards C_star C_h 0 z = false := by
  simp [pastFailureFlag]

/-- Once detected, a strict-past failure remains in every longer scan. -/
theorem pastFailureFlag_mono (z : Z (p := p)) (a b : ℕ) (hab : a ≤ b) :
    pastFailureFlag rate rewards C_star C_h a z = true →
      pastFailureFlag rate rewards C_star C_h b z = true := by
  simp only [pastFailureFlag, decide_eq_true_eq]
  rintro ⟨t, hta, hf⟩
  exact ⟨t, lt_of_lt_of_le hta hab, hf⟩

/-- Exact complement characterization: a false flag means no earlier failure
at any actual calendar coordinate. -/
theorem pastFailureFlag_false_iff_no_earlier_failure
    (z : Z (p := p)) (n : ℕ) :
    pastFailureFlag rate rewards C_star C_h n z = false ↔
      ∀ t : Fin p.T, t.val < n → ¬ failureAt rate rewards C_star C_h z t := by
  simp only [pastFailureFlag, decide_eq_false_iff_not, not_exists, not_and]

/-- A false scan excludes every actual saved-wrong diagnostic in its strict
past; absent records do not create a witness. -/
theorem pastFailureFlag_false_no_saved_wrong
    (z : Z (p := p)) (n : ℕ) (t : Fin p.T) (ht : t.val < n)
    (hflag : pastFailureFlag rate rewards C_star C_h n z = false)
    (r : Record (rate := rate))
    (hr : actualRecord rate rewards C_star C_h t z = some r) :
    ¬ ReferenceActiveStoppedPrefixCoupling.saved_wrong_unique_accepted r := by
  intro hw
  exact ((pastFailureFlag_false_iff_no_earlier_failure
    rate rewards C_star C_h z n).mp hflag t ht) (Or.inl ⟨r, hr, hw⟩)

/-- Before the first detected update, the strict-past flag is false. -/
theorem pastFailureFlag_false_before_first_detection
    (z : Z (p := p)) (t : Fin p.T)
    (hnoEarlier : ∀ u : Fin p.T, u.val < t.val →
      ¬ failureAt rate rewards C_star C_h z u) :
    pastFailureFlag rate rewards C_star C_h t.val z = false := by
  apply (pastFailureFlag_false_iff_no_earlier_failure
    rate rewards C_star C_h z t.val).2
  exact hnoEarlier

/-- The detecting update, including its own physical round, appears at the
next strict-past endpoint. -/
theorem pastFailureFlag_true_after_detection
    (z : Z (p := p)) (t : Fin p.T)
    (hf : failureAt rate rewards C_star C_h z t) :
    pastFailureFlag rate rewards C_star C_h (t.val + 1) z = true := by
  simp only [pastFailureFlag, decide_eq_true_eq]
  exact ⟨t, by omega, hf⟩

end Bandits.Support.ReferenceFirstCollectionAwaitedDownFailureReadout

end
