/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceAffineDispatchPairInvariance

/-!
# The actual UP physical hash rule

Sources: `sources/zip4/manuscript/05_binary_transport.tex:7-42,74-124`,
`sources/zip4/manuscript/06_interruptions.tex:235-296`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:112-137`.

Internal deterministic results on the original round input and continuous rows.
The reward table, selected row, private arrays, and incoming state stay fixed.
Executed positives include tests preceding decoder rejection or later failure.
Freshness, pre-pair measurability, bank chronology, conditional expectation,
and the batch tail require separate producers. No manuscript closure is asserted.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ReferenceUpPhysicalHashRule

open ConstructorDimensions AffineChannelLaw
open scoped BigOperators ENNReal


local instance propDecidable (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition

variable {p : Parameters} {rate : ReferenceActivePhysicalStep.RateInput p}

/-- The actual local PREPARE either falls back or retains the successful arm
operation on its actual checked offer. No ordinary-sender premise is imposed. -/
theorem prepare_arm_spec (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (alpha : ReferencePrelaunchFollower.Activation p) (t : Fin p.T)
    (active : alpha.val ≤ t.val + 1) (input : DeclaredFollowerLocalRound.LocalConfiguration p rate) :
    let prepared := DeclaredFollowerLocalRound.prepare rate i row alpha t active input
    match prepared.configuration with
    | .dagger => prepared.arm = DeclaredFollowerLocalRound.fallbackArm p i
    | .ordinary state _ =>
      match ActiveFollowerQueueOperation.checkedUpOffer rate.eta i row alpha t state with
      | .failure => False
      | .noOffer => ActiveFollowerArmChoice.followerArmChoice state row t i none = some prepared.arm
      | .offer record =>
        ActiveFollowerArmChoice.followerArmChoice state row t i (some record) = some prepared.arm := by
  cases input with
  | dagger => rfl
  | ordinary state memory =>
    cases hs : ActiveFollowerLifecycle.startRound rate.eta t state memory with
    | error reason => simp only [DeclaredFollowerLocalRound.prepare, hs]
    | ok pair =>
      rcases pair with ⟨choice, mem⟩
      cases ho : ActiveFollowerQueueOperation.checkedUpOffer rate.eta i row alpha t choice with
      | failure => simp only [DeclaredFollowerLocalRound.prepare, hs, ho]
      | noOffer =>
        cases ha : ActiveFollowerArmChoice.followerArmChoice choice row t i none <;>
          simp only [DeclaredFollowerLocalRound.prepare, hs, ho, ha]
      | offer record =>
        cases ha : ActiveFollowerArmChoice.followerArmChoice choice row t i (some record) <;>
          simp only [DeclaredFollowerLocalRound.prepare, hs, ho, ha]

/-- A supplied local offer affects arm choice through its own encoded hash only.
The scalar-slice equality and the offered-word hash equality are explicit inputs. -/
theorem armChoice_eq_of_slice_hash (state : ReferencePrelaunchFollower.State p rate.eta)
    (c c' : ContinuousLearningRows.TimeControl p) (i : Fin (p.m - 1))
    (offer : Option (OrdinaryMessageCodec.UpRecord (ReferencePrelaunchFollower.codecParams p rate.eta)))
    (hc : c.1 = c'.1)
    (hh : ∀ record, offer = some record →
      affineHash (c.2 (1, i)) (ActiveFollowerArmChoice.offeredUpWord rate.eta record) =
        affineHash (c'.2 (1, i)) (ActiveFollowerArmChoice.offeredUpWord rate.eta record)) :
    ActiveFollowerArmChoice.followerArmChoiceCore state c i offer =
      ActiveFollowerArmChoice.followerArmChoiceCore state c' i offer := by
  rcases c with ⟨scalars, samples⟩
  rcases c' with ⟨scalars', samples'⟩
  change scalars = scalars' at hc
  subst scalars'
  unfold ActiveFollowerArmChoice.followerArmChoiceCore
  dsimp only
  split
  · split
    · rfl
    · split
      · cases offer with
        | none => rfl
        | some record =>
          dsimp only
          split
          · rw [show ActiveFollowerArmChoice.offeredUpBit rate.eta (scalars, samples) i record =
                ActiveFollowerArmChoice.offeredUpBit rate.eta (scalars, samples') i record from
              hh record rfl]
          · rfl
      · rfl
  · cases state.lastDown <;> rfl

/-- The full selected-follower action comparison uses the actual checked word.
The sole conditional input is equality of that word's hash when it exists. -/
theorem selected_action_eq_of_hash (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (s t : Sample (AffineBatchDecoder.width p))
    (hh : ∀ w, ReferenceActiveAffinePositiveTest.upSent x = some w → affineHash s w = affineHash t w) :
    (ReferenceActivePhysicalStep.prepare (ReferenceActiveAffinePositiveTest.replaceCurrentPair x 1 s)).arms.actions
        (PublicDiscreteDraws.followerPlayer p.two_le_m (ReferenceActivePhysicalStep.upSenderIndex x)) =
      (ReferenceActivePhysicalStep.prepare (ReferenceActiveAffinePositiveTest.replaceCurrentPair x 1 t)).arms.actions
        (PublicDiscreteDraws.followerPlayer p.two_le_m (ReferenceActivePhysicalStep.upSenderIndex x)) := by
  let i := ReferenceActivePhysicalStep.upSenderIndex x
  let xs := ReferenceActiveAffinePositiveTest.replaceCurrentPair x 1 s
  let xt := ReferenceActiveAffinePositiveTest.replaceCurrentPair x 1 t
  let ps := (ReferenceActivePhysicalStep.prepare xs).followers.followers i
  let pt := (ReferenceActivePhysicalStep.prepare xt).followers.followers i
  have hs := prepare_arm_spec (rate := rate) i xs.row (x.state.activations i) x.time
    (x.active i) (x.state.followers i)
  have ht := prepare_arm_spec (rate := rate) i xt.row (x.state.activations i) x.time
    (x.active i) (x.state.followers i)
  change (match ps.configuration with
    | .dagger => ps.arm = _
    | .ordinary state _ => match ActiveFollowerQueueOperation.checkedUpOffer rate.eta i xs.row
        (x.state.activations i) x.time state with
      | .failure => False
      | .noOffer => ActiveFollowerArmChoice.followerArmChoice state xs.row x.time i none = some ps.arm
      | .offer record => ActiveFollowerArmChoice.followerArmChoice state xs.row x.time i
          (some record) = some ps.arm) at hs
  change (match pt.configuration with
    | .dagger => pt.arm = _
    | .ordinary state _ => match ActiveFollowerQueueOperation.checkedUpOffer rate.eta i xt.row
        (x.state.activations i) x.time state with
      | .failure => False
      | .noOffer => ActiveFollowerArmChoice.followerArmChoice state xt.row x.time i none = some pt.arm
      | .offer record => ActiveFollowerArmChoice.followerArmChoice state xt.row x.time i
          (some record) = some pt.arm) at ht
  have hconfig : ps.configuration = pt.configuration :=
    (ReferenceActiveAffinePositiveTest.follower_configuration_replace x 1 s i).trans (ReferenceActiveAffinePositiveTest.follower_configuration_replace x 1 t i).symm
  have hc : (xs.row.2 x.time).1 = (xt.row.2 x.time).1 :=
    (ReferenceActiveAffinePositiveTest.replaceCurrentPair_current_slice x 1 s).trans (ReferenceActiveAffinePositiveTest.replaceCurrentPair_current_slice x 1 t).symm
  change ps.arm = pt.arm
  cases hps : ps.configuration with
  | dagger =>
    rw [hps] at hs
    rw [← hconfig, hps] at ht
    exact hs.trans ht.symm
  | ordinary state memory =>
    rw [hps] at hs
    rw [← hconfig, hps] at ht
    dsimp only at hs ht
    have ho := ReferenceActiveAffinePositiveTest.checkedUpOffer_eq_of_slice (rate := rate) i xs.row xt.row
      (x.state.activations i) x.time state hc
    rw [← ho] at ht
    cases hoff : ActiveFollowerQueueOperation.checkedUpOffer rate.eta i xs.row
        (x.state.activations i) x.time state with
    | failure => simp only [hoff] at hs
    | noOffer =>
      rw [hoff] at hs ht
      have he := armChoice_eq_of_slice_hash (rate := rate) state (xs.row.2 x.time)
        (xt.row.2 x.time) i none hc (by intro record h; cases h)
      exact Option.some.inj (hs.symm.trans (he.trans ht))
    | offer record =>
      rw [hoff] at hs ht
      have hw : ReferenceActiveAffinePositiveTest.upSent x = some (ActiveFollowerArmChoice.offeredUpWord rate.eta record) := by
        rw [← ReferenceActiveAffinePositiveTest.upSent_replace x 1 s]
        unfold ReferenceActiveAffinePositiveTest.upSent ReferenceActivePhysicalStep.upExpected ReferenceUpReception.currentOfferWord
        rw [ReferenceActiveAffinePositiveTest.upSenderIndex_replace]
        rw [hps]
        have halign := (ReferenceActivePhysicalStep.prepare xs).follower_alignment i
        rw [halign.1, halign.2.1, halign.2.2.1, halign.2.2.2]
        change (match ActiveFollowerQueueOperation.checkedUpOffer rate.eta i xs.row
            (x.state.activations i) x.time state with
            | .failure => none
            | .noOffer => none
            | .offer record => some (ActiveFollowerArmChoice.offeredUpWord rate.eta record)) = _
        rw [hoff]
      have he := armChoice_eq_of_slice_hash (rate := rate) state (xs.row.2 x.time)
        (xt.row.2 x.time) i (some record) hc (by
          intro record' hr
          cases Option.some.inj hr
          rw [show (xs.row.2 x.time).2 (1, i) = s from ReferenceActiveAffinePositiveTest.replaceCurrentPair_sample x 1 s,
            show (xt.row.2 x.time).2 (1, i) = t from ReferenceActiveAffinePositiveTest.replaceCurrentPair_sample x 1 t]
          exact hh _ hw)
      exact Option.some.inj (hs.symm.trans (he.trans ht))

/-- Equality of the sent-word hash fixes the complete simultaneous physical profile. -/
theorem actions_eq_of_hash (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (s t : Sample (AffineBatchDecoder.width p))
    (hh : ∀ w, ReferenceActiveAffinePositiveTest.upSent x = some w → affineHash s w = affineHash t w) :
    (ReferenceActivePhysicalStep.prepare (ReferenceActiveAffinePositiveTest.replaceCurrentPair x 1 s)).arms.actions =
      (ReferenceActivePhysicalStep.prepare (ReferenceActiveAffinePositiveTest.replaceCurrentPair x 1 t)).arms.actions := by
  funext player
  by_cases hzero : player = ActiveRoundActions.coordinator p.two_le_m
  · subst player
    exact (ReferenceAffineDispatchPairInvariance.coordinator_action_replace_up x s).trans (ReferenceAffineDispatchPairInvariance.coordinator_action_replace_up x t).symm
  · let i := ActiveRoundActions.followerIndex p.two_le_m player hzero
    rw [← ActiveRoundActions.followerPlayer_followerIndex p.two_le_m player hzero]
    by_cases hi : i = ReferenceActivePhysicalStep.upSenderIndex x
    · change (ReferenceActivePhysicalStep.prepare (ReferenceActiveAffinePositiveTest.replaceCurrentPair x 1 s)).arms.actions
        (PublicDiscreteDraws.followerPlayer p.two_le_m i) =
        (ReferenceActivePhysicalStep.prepare (ReferenceActiveAffinePositiveTest.replaceCurrentPair x 1 t)).arms.actions
        (PublicDiscreteDraws.followerPlayer p.two_le_m i)
      rw [hi]
      exact selected_action_eq_of_hash x s t hh
    · exact (ReferenceActiveAffinePositiveTest.follower_arm_replace_up_of_ne x s i hi).trans
        (ReferenceActiveAffinePositiveTest.follower_arm_replace_up_of_ne x t i hi).symm

/-- Live continuations never invoke the UP decoder, including every failure. -/
theorem livePostChoice_up_none {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r) (base : Fin (p.m - 1) → ℕ)
    (started : CoordinatorPhaseClock.StartRoundResult p) :
    (ReferenceActivePhysicalStep.livePostChoice prepared r q base started).up = none := by
  unfold ReferenceActivePhysicalStep.livePostChoice
  split
  · rfl
  · split
    · rfl
    · split
      · rfl
      · split <;> rfl

/-- Project the existing dispatcher's exact continuation arguments onto the
executed UP test; this introduces no new dispatcher, state, or success input. -/
def tailPositive {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (args : Unit ⊕ (Unit ⊕ (ReferenceActiveDispatchTemporal.LiveArgs p rate ⊕
      ReferenceActiveDispatchTemporal.CollectionArgs p rate))) : Bool :=
  match args with
  | .inr (.inr (.inr ⟨payload, ledger, started, weights⟩)) =>
    ReferenceActiveAffinePositiveTest.upDiagnosticPositive
      (ReferenceActivePhysicalStep.collectionPostChoice prepared payload ledger started weights).up
  | _ => false

/-- Actual diagnostics follow the actual dispatcher. First/later live choices,
selection-none, dagger, and dispatch failure all give the real no-call branch. -/
theorem observeCoordinator_positive_eq_tail {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (prepared : ReferenceActivePhysicalStep.PreparedRound x) :
    ReferenceActiveAffinePositiveTest.upDiagnosticPositive prepared.observeCoordinator.up =
      tailPositive prepared (ReferenceActiveDispatchTemporal.tailArgs prepared.coordinator) := by
  rcases prepared with ⟨cut, hcut, followers⟩
  cases cut with
  | dagger => rfl
  | invalidCollectionCutoff => rfl
  | first outcome =>
    cases outcome <;>
      (unfold ReferenceActivePhysicalStep.PreparedRound.observeCoordinator
        ReferenceActiveDispatchTemporal.tailArgs
       split <;> first
       | rfl
       | (simp only [tailPositive]
          change ReferenceActiveAffinePositiveTest.upDiagnosticPositive _ =
            ReferenceActiveAffinePositiveTest.upDiagnosticPositive (none : Option (ReferenceActivePhysicalStep.UpDiagnostic p rate))
          apply congrArg ReferenceActiveAffinePositiveTest.upDiagnosticPositive
          exact livePostChoice_up_none _ _ _ _ _))
  | live r q base outcome =>
    cases outcome <;>
      (unfold ReferenceActivePhysicalStep.PreparedRound.observeCoordinator
        ReferenceActiveDispatchTemporal.tailArgs
       split <;> first
       | rfl
       | (simp only [tailPositive]
          change ReferenceActiveAffinePositiveTest.upDiagnosticPositive _ =
            ReferenceActiveAffinePositiveTest.upDiagnosticPositive (none : Option (ReferenceActivePhysicalStep.UpDiagnostic p rate))
          apply congrArg ReferenceActiveAffinePositiveTest.upDiagnosticPositive
          exact livePostChoice_up_none _ _ _ _ _))
  | collection payload ledger clock cutoff outcome =>
    cases outcome <;>
      (unfold ReferenceActivePhysicalStep.PreparedRound.observeCoordinator
        ReferenceActiveDispatchTemporal.tailArgs
       split <;> first
       | rfl
       | (simp only [tailPositive]
          change ReferenceActiveAffinePositiveTest.upDiagnosticPositive _ =
            ReferenceActiveAffinePositiveTest.upDiagnosticPositive (none : Option (ReferenceActivePhysicalStep.UpDiagnostic p rate))
          apply congrArg ReferenceActiveAffinePositiveTest.upDiagnosticPositive
          exact livePostChoice_up_none _ _ _ _ _))

/-- Reception eligibility reads its selection gate and the actual scalar;
the decoder sample itself is irrelevant to whether a test executes. -/
theorem eligible_eq_of_slice_observation (row row' : CompletePublicTable.CompleteRow p)
    (ledger : ReferenceActivePhysicalStep.Ledger rate) (bank : CoordinatorUpReception.UpDecoderBank p)
    (time : Fin p.T) (y : Fin (D p + 1)) (hc : (row.2 time).1 = (row'.2 time).1) :
    let input := ReferenceUpReception.receptionInputAtRow rate row (ledger, bank, time, y) time
    let input' := ReferenceUpReception.receptionInputAtRow rate row' (ledger, bank, time, y) time
    (AffineBatchDecoder.eligible (CoordinatorUpReception.roundInput input) ↔
      AffineBatchDecoder.eligible (CoordinatorUpReception.roundInput input')) := by
  dsimp only
  have hg := (ReferenceActiveAffinePositiveTest.up_checks_eq_of_slice row row' ledger bank time y y hc).2
  simp only [AffineBatchDecoder.eligible, CoordinatorUpReception.roundInput,
    decide_eq_true_eq]
  exact and_congr hg Iff.rfl

/-- Non-UP slots cannot execute an UP test, even when earlier recorder and
ledger operations succeed. This does not compare their outputs. -/
theorem collection_positive_non_up {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (payload : ReferenceActivePhysicalStep.Payload rate) (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ)
    (hu : PublicDiscreteDraws.slotDraw (x.row.2 x.time).1 ≠ PublicDiscreteDraws.upSlot) :
    ReferenceActiveAffinePositiveTest.upDiagnosticPositive
      (ReferenceActivePhysicalStep.collectionPostChoice prepared payload ledger started weights).up = false := by
  rw [ReferenceActiveAffinePositiveTest.collectionPostChoice_positive_prefix]
  split
  · rfl
  · split
    · rfl
    · rfl
    · simp [AffineBatchDecoder.eligible, CoordinatorUpReception.roundInput,
        CoordinatorUpReception.receptionGate, ReferenceUpReception.receptionInputAtRow,
        CoordinatorUpMeasurability.receptionInputAtRow,
        CoordinatorUpMeasurability.receptionInputAtControl, hu]

/-- The physical receiver keeps the original ledger inputs except for its
actual collision-filtered observation. -/
theorem upInputs_replace (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (s : Sample (AffineBatchDecoder.width p)) (ledger : ReferenceActivePhysicalStep.Ledger rate) :
    ReferenceActivePhysicalStep.upInputs
      (ReferenceActivePhysicalStep.prepare (ReferenceActiveAffinePositiveTest.replaceCurrentPair x 1 s)) ledger =
      (ledger, x.state.upDecoderBank, x.time,
        (ReferenceActivePhysicalStep.prepare (ReferenceActiveAffinePositiveTest.replaceCurrentPair x 1 s)).coordinatorObservation) := rfl

/-- Actual collection positives agree at equal sent-word hashes. On UP the
real recorder output is fixed before startRound, including enabled zero
arrivals; all invalid/rejected start results remain in their source order. -/
theorem collection_positive_eq_of_hash (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (s t : Sample (AffineBatchDecoder.width p))
    (payload : ReferenceActivePhysicalStep.Payload rate) (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ)
    (hh : ∀ w, ReferenceActiveAffinePositiveTest.upSent x = some w → affineHash s w = affineHash t w) :
    ReferenceActiveAffinePositiveTest.upDiagnosticPositive
      (ReferenceActivePhysicalStep.collectionPostChoice
        (ReferenceActivePhysicalStep.prepare (ReferenceActiveAffinePositiveTest.replaceCurrentPair x 1 s))
        payload ledger started weights).up =
    ReferenceActiveAffinePositiveTest.upDiagnosticPositive
      (ReferenceActivePhysicalStep.collectionPostChoice
        (ReferenceActivePhysicalStep.prepare (ReferenceActiveAffinePositiveTest.replaceCurrentPair x 1 t))
        payload ledger started weights).up := by
  by_cases hu : PublicDiscreteDraws.slotDraw (x.row.2 x.time).1 = PublicDiscreteDraws.upSlot
  · rw [ReferenceActiveAffinePositiveTest.collectionPostChoice_positive_prefix,
      ReferenceActiveAffinePositiveTest.collectionPostChoice_positive_prefix,
      ReferenceActiveAffinePositiveTest.collectionRecording_replace_up x s payload started weights hu,
      ReferenceActiveAffinePositiveTest.collectionRecording_replace_up x t payload started weights hu]
    simp only [(ReferenceActiveAffinePositiveTest.replaceCurrentPair_fields x 1 s).2.2.1,
      (ReferenceActiveAffinePositiveTest.replaceCurrentPair_fields x 1 t).2.2.1]
    split
    · rfl
    · split
      · rfl
      · rfl
      · rename_i ledgerStarted hstart
        have ha := actions_eq_of_hash x s t hh
        have hy : (ReferenceActivePhysicalStep.prepare
            (ReferenceActiveAffinePositiveTest.replaceCurrentPair x 1 s)).coordinatorObservation =
            (ReferenceActivePhysicalStep.prepare
            (ReferenceActiveAffinePositiveTest.replaceCurrentPair x 1 t)).coordinatorObservation := by
          unfold ReferenceActivePhysicalStep.PreparedRound.coordinatorObservation
          rw [ReferenceActivePhysicalStep.PreparedRound.feedback_rule,
            ReferenceActivePhysicalStep.PreparedRound.feedback_rule, ha]
          rfl
        have hc := (ReferenceActiveAffinePositiveTest.replaceCurrentPair_current_slice x 1 s).trans
          (ReferenceActiveAffinePositiveTest.replaceCurrentPair_current_slice x 1 t).symm
        have hcheck := (ReferenceActiveAffinePositiveTest.up_checks_eq_of_slice
          (ReferenceActiveAffinePositiveTest.replaceCurrentPair x 1 s).row
          (ReferenceActiveAffinePositiveTest.replaceCurrentPair x 1 t).row ledgerStarted
          x.state.upDecoderBank x.time
          (ReferenceActivePhysicalStep.prepare (ReferenceActiveAffinePositiveTest.replaceCurrentPair x 1 s)).coordinatorObservation
          (ReferenceActivePhysicalStep.prepare (ReferenceActiveAffinePositiveTest.replaceCurrentPair x 1 t)).coordinatorObservation hc).1
        rw [upInputs_replace, upInputs_replace, hcheck, hy]
        rw [propext (eligible_eq_of_slice_observation _ _ _ _ _ _ hc)]
  · rw [collection_positive_non_up, collection_positive_non_up]
    all_goals
      change PublicDiscreteDraws.slotDraw ((ReferenceActiveAffinePositiveTest.replaceCurrentPair x 1 _).row.2 x.time).1 ≠ _
      rw [ReferenceActiveAffinePositiveTest.replaceCurrentPair_current_slice]
      exact hu

/-- The complete actual UP executed-test Boolean depends on the current pair
only through the actual offered word's hash, with no word imposing no condition. -/
theorem upPositive_eq_of_hash (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (s t : Sample (AffineBatchDecoder.width p))
    (hh : ∀ w, ReferenceActiveAffinePositiveTest.upSent x = some w → affineHash s w = affineHash t w) :
    ReferenceActiveAffinePositiveTest.upPositive (ReferenceActiveAffinePositiveTest.replaceCurrentPair x 1 s) =
      ReferenceActiveAffinePositiveTest.upPositive (ReferenceActiveAffinePositiveTest.replaceCurrentPair x 1 t) := by
  unfold ReferenceActiveAffinePositiveTest.upPositive
  rw [observeCoordinator_positive_eq_tail, observeCoordinator_positive_eq_tail]
  change tailPositive _ (ReferenceActiveDispatchTemporal.tailArgs
      (ReferenceActivePhysicalStep.dispatch (ReferenceActiveAffinePositiveTest.replaceCurrentPair x 1 s))) =
    tailPositive _ (ReferenceActiveDispatchTemporal.tailArgs
      (ReferenceActivePhysicalStep.dispatch (ReferenceActiveAffinePositiveTest.replaceCurrentPair x 1 t)))
  rw [ReferenceAffineDispatchPairInvariance.tailArgs_replace,
    ReferenceAffineDispatchPairInvariance.tailArgs_replace]
  cases ReferenceActiveDispatchTemporal.tailArgs (ReferenceActivePhysicalStep.dispatch x) with
  | inl ignored => rfl
  | inr next =>
    cases next with
    | inl ignored => rfl
    | inr next =>
      cases next with
      | inl ignored => rfl
      | inr args =>
        rcases args with ⟨payload, ledger, started, weights⟩
        exact collection_positive_eq_of_hash x s t payload ledger started weights hh

/-- Literal Boolean rule: run the actual test with zero coefficients and the
supplied offset. This definition includes the real receiver prefix. -/
def upRule (x : ReferenceActivePhysicalStep.RoundInput p rate) (bit : Bit) : Bool :=
  ReferenceActiveAffinePositiveTest.upPositive
    (ReferenceActiveAffinePositiveTest.replaceCurrentPair x 1 (0, bit))

theorem affineHash_zero_coefficient (bit : Bit) (w : Word (AffineBatchDecoder.width p)) :
    affineHash (0, bit) w = bit := by
  simp only [affineHash, AffineChannelLaw.dotProduct, Pi.zero_apply, zero_mul, Finset.sum_const_zero, zero_add]

/-- Literal simultaneous-profile rule, evaluated at zero coefficients and the
supplied offset. Every coordinator and follower action is retained. -/
def upActionRule (x : ReferenceActivePhysicalStep.RoundInput p rate) (bit : Bit) : Fin p.m → Fin p.K :=
  (ReferenceActivePhysicalStep.prepare
    (ReferenceActiveAffinePositiveTest.replaceCurrentPair x 1 (0, bit))).arms.actions

/-- The complete PREPARE profile has exactly the same one-bit dependence as
the actual positive test, including every no-offer and dagger branch. -/
theorem actions_eq_rule (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (s : Sample (AffineBatchDecoder.width p)) :
    (ReferenceActivePhysicalStep.prepare (ReferenceActiveAffinePositiveTest.replaceCurrentPair x 1 s)).arms.actions =
      upActionRule x (match ReferenceActiveAffinePositiveTest.upSent x with
        | none => 0
        | some w => affineHash s w) := by
  apply actions_eq_of_hash
  intro w hw
  rw [hw, affineHash_zero_coefficient]

/-- In the actual absent-offer branch the entire profile ignores both current
affine coordinates, even if the coordinator still executes a positive test. -/
theorem actions_none (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (h : ReferenceActiveAffinePositiveTest.upSent x = none)
    (s t : Sample (AffineBatchDecoder.width p)) :
    (ReferenceActivePhysicalStep.prepare (ReferenceActiveAffinePositiveTest.replaceCurrentPair x 1 s)).arms.actions =
      (ReferenceActivePhysicalStep.prepare (ReferenceActiveAffinePositiveTest.replaceCurrentPair x 1 t)).arms.actions := by
  apply actions_eq_of_hash
  intro w hw
  rw [h] at hw
  cases hw

/-- The actual full UP enabling Boolean factors through the actual sent hash.
No-offer rounds ignore the entire pair, including when a positive is collected. -/
theorem upPositive_eq_rule (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (s : Sample (AffineBatchDecoder.width p)) :
    ReferenceActiveAffinePositiveTest.upPositive (ReferenceActiveAffinePositiveTest.replaceCurrentPair x 1 s) =
      upRule x (match ReferenceActiveAffinePositiveTest.upSent x with
        | none => 0
        | some w => affineHash s w) := by
  apply upPositive_eq_of_hash
  intro w hw
  rw [hw, affineHash_zero_coefficient]

/-- Absent actual offers impose no restriction on either replacement sample. -/
theorem upPositive_none (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (h : ReferenceActiveAffinePositiveTest.upSent x = none)
    (s t : Sample (AffineBatchDecoder.width p)) :
    ReferenceActiveAffinePositiveTest.upPositive (ReferenceActiveAffinePositiveTest.replaceCurrentPair x 1 s) =
      ReferenceActiveAffinePositiveTest.upPositive (ReferenceActiveAffinePositiveTest.replaceCurrentPair x 1 t) := by
  apply upPositive_eq_of_hash
  intro w hw
  rw [h] at hw
  cases hw

/-- Replacing the current pair by its original value preserves the complete
input, including the original private arrays and selected row index. -/
theorem replaceCurrentPair_original (x : ReferenceActivePhysicalStep.RoundInput p rate) :
    ReferenceActiveAffinePositiveTest.replaceCurrentPair x 1
      ((x.row.2 x.time).2 (1, ReferenceActivePhysicalStep.upSenderIndex x)) = x := by
  unfold ReferenceActiveAffinePositiveTest.replaceCurrentPair
  simp only [Function.update_eq_self, Prod.eta]
  change { x with rows := Function.update x.rows x.selected (x.rows x.selected) } = x
  rw [Function.update_eq_self]

/-- The original, unmodified physical round uses its own affine pair. -/
theorem upPositive_original_eq_rule (x : ReferenceActivePhysicalStep.RoundInput p rate) :
    ReferenceActiveAffinePositiveTest.upPositive x =
      upRule x (match ReferenceActiveAffinePositiveTest.upSent x with
        | none => 0
        | some w => affineHash ((x.row.2 x.time).2 (1, ReferenceActivePhysicalStep.upSenderIndex x)) w) := by
  have h := upPositive_eq_rule x ((x.row.2 x.time).2 (1, ReferenceActivePhysicalStep.upSenderIndex x))
  rw [replaceCurrentPair_original] at h
  exact h

/-- A fixed-input decision for the existing finite affine law. It supplies
neither an adapted history nor a conditional fresh-pair law. -/
def upDecision (x : ReferenceActivePhysicalStep.RoundInput p rate) :
    AdaptiveAffineBatchTail.Decision (AffineBatchDecoder.width p) Unit :=
  { sent := ReferenceActiveAffinePositiveTest.upSent x
    active := true
    positive := fun _ bit => upRule x bit }

theorem upDecision_positiveTest (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (s : Sample (AffineBatchDecoder.width p)) :
    AdaptiveAffineBatchTail.positiveTest (upDecision x) s () =
      ReferenceActiveAffinePositiveTest.upPositive (ReferenceActiveAffinePositiveTest.replaceCurrentPair x 1 s) := by
  have h := (upPositive_eq_rule x s).symm
  unfold AdaptiveAffineBatchTail.positiveTest upDecision
  cases hw : ReferenceActiveAffinePositiveTest.upSent x <;>
    simpa only [hw, Bool.true_and] using h

/-- The fixed-input finite jointLaw half identity for the actual UP positive.
The candidate exclusion occurs on both sides; its hash-one test only on the left.
The next consumer is the original-coordinate hash-half/batch construction after
active-prefix exposure and actual bank chronology producers have landed. -/
theorem upPositive_one_step_half (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (M : Word (AffineBatchDecoder.width p)) :
    (∑ s : Sample (AffineBatchDecoder.width p), jointLaw (AffineBatchDecoder.width p) s *
      AdaptiveAffineBatchTail.indicator
        (ReferenceActiveAffinePositiveTest.upPositive (ReferenceActiveAffinePositiveTest.replaceCurrentPair x 1 s) = true ∧
          ReferenceActiveAffinePositiveTest.upSent x ≠ some M ∧ affineHash s M = 1)) =
    ((1 : ℝ≥0∞) / 2) * ∑ s : Sample (AffineBatchDecoder.width p), jointLaw (AffineBatchDecoder.width p) s *
      AdaptiveAffineBatchTail.indicator
        (ReferenceActiveAffinePositiveTest.upPositive (ReferenceActiveAffinePositiveTest.replaceCurrentPair x 1 s) = true ∧
          ReferenceActiveAffinePositiveTest.upSent x ≠ some M) := by
  have h := AdaptiveAffineBatchTail.one_step_half (upDecision x) M ()
  simp_rw [upDecision_positiveTest] at h
  exact h

/-- A real checked offer derives the selected, unoccupied branch and all arm
checks from its literal construction, without assuming a correct reply. -/
theorem checked_offer_facts (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (alpha : ReferencePrelaunchFollower.Activation p) (time : Fin p.T)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (record : OrdinaryMessageCodec.UpRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (ho : ActiveFollowerQueueOperation.checkedUpOffer rate.eta i row alpha time state = .offer record) :
    ActiveFollowerQueueOperation.selectedUpRound i row alpha time ∧ state.status = .unoccupied ∧
      ActiveFollowerArmChoice.upStateDomain state ∧
      ActiveFollowerArmChoice.offeredUpMatchesState state record := by
  unfold ActiveFollowerQueueOperation.checkedUpOffer at ho
  split at ho
  · rename_i hdomain
    split at ho
    · rename_i hselected
      split at ho
      · cases ho
        exact ⟨hselected.1, hselected.2, ⟨hdomain.1, hdomain.2.1, hdomain.2.2.1⟩,
          rfl, rfl, rfl, rfl⟩
      · cases ho
    · cases ho
  · cases ho

/-- Expand the actual selected-word projection using derived PREPARE alignment. -/
theorem upSent_eq_configuration (x : ReferenceActivePhysicalStep.RoundInput p rate) :
    ReferenceActiveAffinePositiveTest.upSent x =
      match ((ReferenceActivePhysicalStep.prepare x).followers.followers
          (ReferenceActivePhysicalStep.upSenderIndex x)).configuration with
      | .dagger => none
      | .ordinary state _ =>
        match ActiveFollowerQueueOperation.checkedUpOffer rate.eta
            (ReferenceActivePhysicalStep.upSenderIndex x) x.row
            (x.state.activations (ReferenceActivePhysicalStep.upSenderIndex x)) x.time state with
        | .failure => none
        | .noOffer => none
        | .offer record => some (ActiveFollowerArmChoice.offeredUpWord rate.eta record) := by
  unfold ReferenceActiveAffinePositiveTest.upSent ReferenceActivePhysicalStep.upExpected
    ReferenceUpReception.currentOfferWord
  cases ((ReferenceActivePhysicalStep.prepare x).followers.followers
      (ReferenceActivePhysicalStep.upSenderIndex x)).configuration with
  | dagger => rfl
  | ordinary state memory =>
    have h := (ReferenceActivePhysicalStep.prepare x).follower_alignment
      (ReferenceActivePhysicalStep.upSenderIndex x)
    rw [h.1, h.2.1, h.2.2.1, h.2.2.2]
    rfl

/-- A present actual UP word forces the real selected unoccupied sender's
SendArm action and the UP slot. All local branches are derived from the offer. -/
theorem selected_action_of_upSent (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (w : Word (AffineBatchDecoder.width p))
    (hw : ReferenceActiveAffinePositiveTest.upSent x = some w) :
    PublicDiscreteDraws.slotDraw (x.row.2 x.time).1 = PublicDiscreteDraws.upSlot ∧
      (ReferenceActivePhysicalStep.prepare x).arms.actions
          (PublicDiscreteDraws.followerPlayer p.two_le_m (ReferenceActivePhysicalStep.upSenderIndex x)) =
        ActiveRoundActions.sendArm
          (affineHash ((x.row.2 x.time).2 (1, ReferenceActivePhysicalStep.upSenderIndex x)) w)
          ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K (x.row.2 x.time).1).val
            (PublicDiscreteDraws.followerPlayer p.two_le_m (ReferenceActivePhysicalStep.upSenderIndex x)))
          ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K (x.row.2 x.time).1).val
            (ActiveRoundActions.coordinator p.two_le_m)) := by
  let i := ReferenceActivePhysicalStep.upSenderIndex x
  let prepared := (ReferenceActivePhysicalStep.prepare x).followers.followers i
  have hs := prepare_arm_spec (rate := rate) i x.row (x.state.activations i) x.time
    (x.active i) (x.state.followers i)
  change (match prepared.configuration with
    | .dagger => prepared.arm = _
    | .ordinary state _ => match ActiveFollowerQueueOperation.checkedUpOffer rate.eta i x.row
        (x.state.activations i) x.time state with
      | .failure => False
      | .noOffer => ActiveFollowerArmChoice.followerArmChoice state x.row x.time i none = some prepared.arm
      | .offer record => ActiveFollowerArmChoice.followerArmChoice state x.row x.time i
          (some record) = some prepared.arm) at hs
  rw [upSent_eq_configuration] at hw
  change (match prepared.configuration with
    | .dagger => none
    | .ordinary state _ =>
      match ActiveFollowerQueueOperation.checkedUpOffer rate.eta i x.row (x.state.activations i) x.time state with
      | .failure => none
      | .noOffer => none
      | .offer record => some (ActiveFollowerArmChoice.offeredUpWord rate.eta record)) = some w at hw
  cases hc : prepared.configuration with
  | dagger => simp only [hc] at hw; cases hw
  | ordinary state memory =>
    rw [hc] at hs hw
    dsimp only at hs hw
    cases ho : ActiveFollowerQueueOperation.checkedUpOffer rate.eta i x.row
        (x.state.activations i) x.time state with
    | failure => simp only [ho] at hw; cases hw
    | noOffer => simp only [ho] at hw; cases hw
    | offer record =>
      rw [ho] at hs hw
      have hf := checked_offer_facts i x.row (x.state.activations i) x.time state record ho
      have hword : ActiveFollowerArmChoice.offeredUpWord rate.eta record = w := Option.some.inj hw
      refine ⟨hf.1.2.1, ?_⟩
      have ha := ActiveFollowerArmChoice.followerArmChoiceCore_unoccupied_selected_up state
        (x.row.2 x.time) i record hf.2.1 hf.1.2.1 hf.1.2.2 hf.2.2
      change ActiveFollowerArmChoice.followerArmChoiceCore state (x.row.2 x.time) i (some record) =
        some prepared.arm at hs
      have he := Option.some.inj (hs.symm.trans ha)
      change prepared.arm = _
      simpa only [ActiveFollowerArmChoice.offeredUpBit, hword] using he

/-- Replacement-pair form of the literal selected sender formula. Ordinary
status, selected UP, offer fields, and physical arm success are all derived. -/
theorem selected_action_replace_of_upSent (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (s : Sample (AffineBatchDecoder.width p)) (w : Word (AffineBatchDecoder.width p))
    (hw : ReferenceActiveAffinePositiveTest.upSent x = some w) :
    (ReferenceActivePhysicalStep.prepare (ReferenceActiveAffinePositiveTest.replaceCurrentPair x 1 s)).arms.actions
        (PublicDiscreteDraws.followerPlayer p.two_le_m (ReferenceActivePhysicalStep.upSenderIndex x)) =
      ActiveRoundActions.sendArm (affineHash s w)
        ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K (x.row.2 x.time).1).val
          (PublicDiscreteDraws.followerPlayer p.two_le_m (ReferenceActivePhysicalStep.upSenderIndex x)))
        ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K (x.row.2 x.time).1).val
          (ActiveRoundActions.coordinator p.two_le_m)) := by
  have h := (selected_action_of_upSent (ReferenceActiveAffinePositiveTest.replaceCurrentPair x 1 s) w
    ((ReferenceActiveAffinePositiveTest.upSent_replace x 1 s).trans hw)).2
  rw [ReferenceActiveAffinePositiveTest.upSenderIndex_replace,
    (ReferenceActiveAffinePositiveTest.replaceCurrentPair_fields x 1 s).2.2.1,
    ReferenceActiveAffinePositiveTest.replaceCurrentPair_current_slice,
    ReferenceActiveAffinePositiveTest.replaceCurrentPair_sample] at h
  exact h

/-- A successful literal UP choice outside the fast-confirmed branch uses
the receiver tuple arm. The local branch and success inputs are explicit. -/
theorem coordinator_choice_up (payload : ReferenceActivePhysicalStep.Payload rate)
    (pending : Finset (ActiveRoundActions.Follower p.m))
    (cutoff : Option (CoordinatorLocalArmChoice.Cutoff p)) (time : Fin p.T)
    (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ)
    (row : CompletePublicTable.CompleteRow p) (arm : Fin p.K)
    (hchoice : CoordinatorLocalArmChoice.coordinatorArmChoice payload pending cutoff time weights row = some arm)
    (hnotfast : ¬ (CoordinatorLocalArmChoice.assignmentIsLive payload cutoff time ∧ pending = ∅))
    (hu : PublicDiscreteDraws.slotDraw (row.2 time).1 = PublicDiscreteDraws.upSlot) :
    arm = (OrderedTupleSampler.sample p.two_le_m p.m_lt_K (row.2 time).1).val
      (ActiveRoundActions.coordinator p.two_le_m) := by
  unfold CoordinatorLocalArmChoice.coordinatorArmChoice
    CoordinatorLocalArmChoice.coordinatorArmChoiceCore at hchoice
  split at hchoice
  · have hd : PublicDiscreteDraws.upSlot ≠ PublicDiscreteDraws.dataSlot := by decide
    have hn : PublicDiscreteDraws.upSlot ≠ PublicDiscreteDraws.downSlot := by decide
    simp only [hu, hd, hn, false_and, ite_false] at hchoice
    exact (Option.some.inj hchoice).symm
  · cases hchoice

/-- In either actual collection continuation, UP uses the actual coordinator
receiver tuple arm. All remaining tails have no assertion to discharge. -/
theorem collection_tail_arm {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (cut : ReferenceActivePhysicalStep.DispatchCut x)
    (hu : PublicDiscreteDraws.slotDraw (x.row.2 x.time).1 = PublicDiscreteDraws.upSlot) :
    match ReferenceActiveDispatchTemporal.tailArgs cut with
    | .inr (.inr (.inr _)) => cut.arm =
      (OrderedTupleSampler.sample p.two_le_m p.m_lt_K (x.row.2 x.time).1).val
        (ActiveRoundActions.coordinator p.two_le_m)
    | _ => True := by
  cases cut with
  | dagger => trivial
  | invalidCollectionCutoff => trivial
  | first outcome =>
    cases outcome <;> (unfold ReferenceActiveDispatchTemporal.tailArgs; split_ifs <;> trivial)
  | live r q base outcome =>
    cases outcome
    case cutoffChosen dispatched hstart ledger hinitial hcand hdom hclock hpending hno selected =>
      have hc := selected.armChoice_eq
      change CoordinatorLocalArmChoice.coordinatorArmChoice r.payload dispatched.startResult.pending
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p dispatched.startResult.clock.u)
        x.time (ReferenceActivePhysicalStep.liveRegistersAt r x.time).complementWeights x.row =
        some selected.arm at hc
      have hnotfast : ¬ (CoordinatorLocalArmChoice.assignmentIsLive r.payload
          (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p dispatched.startResult.clock.u) x.time ∧
          dispatched.startResult.pending = ∅) := by
        rw [hclock]
        intro h
        have ht := h.1.2
        change x.time.val + 1 < x.time.val + 1 at ht
        exact (Nat.lt_irrefl _) ht
      have ha := coordinator_choice_up r.payload dispatched.startResult.pending _ x.time _
        x.row selected.arm hc hnotfast hu
      unfold ReferenceActiveDispatchTemporal.tailArgs
      split_ifs
      · trivial
      · rw [ReferenceActivePhysicalStep.live_arm_equation]
        exact ha
    all_goals (unfold ReferenceActiveDispatchTemporal.tailArgs; split_ifs <;> trivial)
  | collection payload ledger clock cutoff outcome =>
    cases outcome
    case continuing core snapshot boundary scores =>
      have hc := snapshot.armChoice_eq
      change CoordinatorLocalArmChoice.coordinatorArmChoice payload snapshot.clockStarted.pending
        (some (CoordinatorCollectionUpRoundStep.localCutoff cutoff)) x.time _ x.row =
        some snapshot.arm at hc
      have hnotfast : ¬ (CoordinatorLocalArmChoice.assignmentIsLive payload
          (some (CoordinatorCollectionUpRoundStep.localCutoff cutoff)) x.time ∧
          snapshot.clockStarted.pending = ∅) := by
        intro h
        have he : ledger.pending = ∅ := snapshot.clockStarted_frame.2.1.symm.trans h.2
        exact snapshot.inputsValid.pending_nonempty.ne_empty he
      have ha := coordinator_choice_up payload snapshot.clockStarted.pending _ x.time _
        x.row snapshot.arm hc hnotfast hu
      unfold ReferenceActiveDispatchTemporal.tailArgs
      split_ifs
      · trivial
      · rw [ReferenceActivePhysicalStep.collection_arm_equation]
        exact ha
    all_goals (unfold ReferenceActiveDispatchTemporal.tailArgs; split_ifs <;> trivial)

/-- Eligible actual receiver input implies the UP slot and a positive actual
collision-filtered coordinator grid observation. -/
theorem receiver_eligible_observation {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (he : AffineBatchDecoder.eligible (CoordinatorUpReception.roundInput
      (ReferenceUpReception.receptionInputAtRow rate x.row
        (ReferenceActivePhysicalStep.upInputs prepared ledger) x.time))) :
    PublicDiscreteDraws.slotDraw (x.row.2 x.time).1 = PublicDiscreteDraws.upSlot ∧
      0 < CoordinatorUpReception.roundedObservationValue p prepared.coordinatorObservation := by
  have hg := of_decide_eq_true he.1
  exact ⟨hg.2.1, he.2.2⟩

/-- Read the positive before any later UP rejection or collection finish
failure, retaining all preceding recorder and startRound failures. -/
theorem collection_positive_observation {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (payload : ReferenceActivePhysicalStep.Payload rate) (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ)
    (hp : ReferenceActiveAffinePositiveTest.upDiagnosticPositive
      (ReferenceActivePhysicalStep.collectionPostChoice prepared payload ledger started weights).up = true) :
    PublicDiscreteDraws.slotDraw (x.row.2 x.time).1 = PublicDiscreteDraws.upSlot ∧
      0 < CoordinatorUpReception.roundedObservationValue p prepared.coordinatorObservation := by
  rw [ReferenceActiveAffinePositiveTest.collectionPostChoice_positive_prefix] at hp
  split at hp
  · cases hp
  · split at hp
    · cases hp
    · cases hp
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
      exact receiver_eligible_observation prepared _ hp.2

/-- A positive actual UP test forces the real coordinator receiver arm, not
a supplied call, observation, or collision-free profile. -/
theorem upPositive_receiver (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (hp : ReferenceActiveAffinePositiveTest.upPositive x = true) :
    0 < CoordinatorUpReception.roundedObservationValue p (ReferenceActivePhysicalStep.prepare x).coordinatorObservation ∧
      (ReferenceActivePhysicalStep.prepare x).arms.actions (ActiveRoundActions.coordinator p.two_le_m) =
        (OrderedTupleSampler.sample p.two_le_m p.m_lt_K (x.row.2 x.time).1).val
          (ActiveRoundActions.coordinator p.two_le_m) := by
  have ht : tailPositive (ReferenceActivePhysicalStep.prepare x)
      (ReferenceActiveDispatchTemporal.tailArgs (ReferenceActivePhysicalStep.dispatch x)) = true :=
    (observeCoordinator_positive_eq_tail (ReferenceActivePhysicalStep.prepare x)).symm.trans hp
  cases ha : ReferenceActiveDispatchTemporal.tailArgs (ReferenceActivePhysicalStep.dispatch x) with
  | inl ignored => simp only [ha, tailPositive] at ht; cases ht
  | inr next =>
    cases next with
    | inl ignored => simp only [ha, tailPositive] at ht; cases ht
    | inr next =>
      cases next with
      | inl ignored => simp only [ha, tailPositive] at ht; cases ht
      | inr args =>
        rcases args with ⟨payload, ledger, started, weights⟩
        rw [ha] at ht
        have ho := collection_positive_observation (ReferenceActivePhysicalStep.prepare x)
          payload ledger started weights ht
        have harm := collection_tail_arm (ReferenceActivePhysicalStep.dispatch x) ho.1
        rw [ha] at harm
        exact ⟨ho.2, harm⟩

/-- A present offered word and a positive actual test force its actual hash
to be one. Hash zero makes the selected sender collide at the receiver arm. -/
theorem upPositive_hash_one (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (w : Word (AffineBatchDecoder.width p))
    (hw : ReferenceActiveAffinePositiveTest.upSent x = some w)
    (hp : ReferenceActiveAffinePositiveTest.upPositive x = true) :
    affineHash ((x.row.2 x.time).2 (1, ReferenceActivePhysicalStep.upSenderIndex x)) w = 1 := by
  have hs := selected_action_of_upSent x w hw
  have hr := upPositive_receiver x hp
  have hnonzero : affineHash ((x.row.2 x.time).2 (1, ReferenceActivePhysicalStep.upSenderIndex x)) w ≠ 0 := by
    intro hz
    have hcollision : ¬ FiniteBanditModel.collisionFreeFor
        (ReferenceActivePhysicalStep.prepare x).arms.actions (ActiveRoundActions.coordinator p.two_le_m) := by
      intro hfree
      apply hfree (PublicDiscreteDraws.followerPlayer p.two_le_m (ReferenceActivePhysicalStep.upSenderIndex x))
        (ActiveRoundActions.followerPlayer_ne_coordinator p.two_le_m _)
      rw [hs.2, hz, ActiveRoundActions.sendArm, hr.2]
      rfl
    have hy : (ReferenceActivePhysicalStep.prepare x).coordinatorObservation = 0 := by
      unfold ReferenceActivePhysicalStep.PreparedRound.coordinatorObservation
      rw [ReferenceActivePhysicalStep.PreparedRound.feedback_rule, ite_eq_right hcollision]
    have hzero := CoordinatorUpReception.roundedObservationValue_zero p
      (ReferenceActivePhysicalStep.prepare x).coordinatorObservation (congrArg Fin.val hy)
    rw [hzero] at hr
    exact (lt_irrefl 0) hr.1
  have hb := ZMod.val_lt (affineHash ((x.row.2 x.time).2 (1, ReferenceActivePhysicalStep.upSenderIndex x)) w)
  have hz : (affineHash ((x.row.2 x.time).2 (1, ReferenceActivePhysicalStep.upSenderIndex x)) w).val ≠ 0 := by
    intro h
    apply hnonzero
    calc
      affineHash ((x.row.2 x.time).2 (1, ReferenceActivePhysicalStep.upSenderIndex x)) w =
        ((affineHash ((x.row.2 x.time).2 (1, ReferenceActivePhysicalStep.upSenderIndex x)) w).val : Bit) :=
          (ZMod.natCast_zmod_val _).symm
      _ = 0 := by rw [h]; rfl
  have hv : (affineHash ((x.row.2 x.time).2 (1, ReferenceActivePhysicalStep.upSenderIndex x)) w).val = 1 := by omega
  calc
    affineHash ((x.row.2 x.time).2 (1, ReferenceActivePhysicalStep.upSenderIndex x)) w =
      ((affineHash ((x.row.2 x.time).2 (1, ReferenceActivePhysicalStep.upSenderIndex x)) w).val : Bit) :=
        (ZMod.natCast_zmod_val _).symm
    _ = 1 := by rw [hv]; rfl

/-- Replacement specialization: every positive with a present original word
has hash one under the replacement pair, with all other input data fixed. -/
theorem upPositive_replace_hash_one (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (s : Sample (AffineBatchDecoder.width p)) (w : Word (AffineBatchDecoder.width p))
    (hw : ReferenceActiveAffinePositiveTest.upSent x = some w)
    (hp : ReferenceActiveAffinePositiveTest.upPositive (ReferenceActiveAffinePositiveTest.replaceCurrentPair x 1 s) = true) :
    affineHash s w = 1 := by
  have h := upPositive_hash_one (ReferenceActiveAffinePositiveTest.replaceCurrentPair x 1 s) w
    ((ReferenceActiveAffinePositiveTest.upSent_replace x 1 s).trans hw) hp
  rw [ReferenceActiveAffinePositiveTest.upSenderIndex_replace,
    (ReferenceActiveAffinePositiveTest.replaceCurrentPair_fields x 1 s).2.2.1,
    ReferenceActiveAffinePositiveTest.replaceCurrentPair_sample] at h
  exact h

end Bandits.Support.ReferenceUpPhysicalHashRule
