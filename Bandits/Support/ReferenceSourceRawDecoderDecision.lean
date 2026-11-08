/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionInclusiveDecoderStop

/-!
# Literal ordinary wrong-unique physical decoder decisions

Sources: `05_binary_transport.tex:23-55`, `06_interruptions.tex:140-177,425-431`,
`appendix_a_local_protocol.tex:92-108,141-157`, and
`appendix_b_communication.tex:94-99,725-751` in the pinned ZIP4 manuscript.

These internal dictionaries identify one raw ordinary decision, before reference
filtering and checked recovery or finish. A completed bank is not a successful
protocol output. Sent words are options, so an absent current offer is retained.
The prelaunch dictionary uses its own actual prefix, without inventing a
postlaunch record. No fixed-awaited ambiguity, exhaustive source partition,
probability bound, stopping theorem, or manuscript closure is asserted.
The next consumer is `ReferenceLiteralSourceDecoderCoverage`.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ReferenceSourceRawDecoderDecision

open ConstructorDimensions AffineBatchDecoder
open ReferenceFollowerDownDecoderReplay
open scoped Classical

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

abbrev Record := ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)
abbrev Batch := List (AffineBatchDecoder.Entry p.T (width p))
abbrev Word := AffineChannelLaw.Word (width p)
abbrev Down := OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta)
abbrev Up := OrdinaryMessageCodec.UpRecord (ReferencePrelaunchFollower.codecParams p rate.eta)
abbrev UpInput := CoordinatorUpReception.ReceptionInput p rate.eta.val rate.eta.property
  (ReferenceUpReception.sourceCap_forLedger rate) rate.n rate.n_scale

/-- The ordinary UP parse and acceptance test on a raw word and a current
option-valued offer. This body contains no saved decision flag or filter. -/
def ordinary_up_wrong (input : UpInput (rate := rate))
    (raw sent : Option (Word (p := p))) : Prop :=
  ∃ (w : Word (p := p)) (M : Up (rate := rate)),
    raw = some w ∧ some w ≠ sent ∧
    CoordinatorUpReception.parseDecoderOutput (p := p) (eta := rate.eta.val)
      (some w) = some M ∧
    CoordinatorCollectionLedger.acceptUpCheck input.ledger input.selectedFollower M = true

/-- A literal DOWN decision on the retained physical receiver bank. The bank
keeps its original pending entries and the actual current positive append.
The comparison uses the actual sender, including encoded absence. -/
def down_wrong_decision (r : Record (rate := rate)) (i : Fin (p.m - 1)) : Prop :=
  ∃ (logged : ReferencePrelaunchFollower.State p rate.eta)
      (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
      (W : Batch (p := p)) (w : Word (p := p)) (M : Down (rate := rate)),
    (r.output.followers i).downInput = some logged ∧
    (r.output.followers i).down = some cut ∧
    ReferenceFirstLiveDownCompletionReadout.completedDownBatch r i = some W ∧
    W = logged.downBatch.pending ++ positiveAt p
      (ActiveFollowerDownAcceptance.currentInputExtension p
        (ActiveFollowerDownAcceptance.currentRoundInput p i r.input.row r.input.time
          (preparedOwnObservation r i) rate logged)) r.input.time ∧
    W.length = quota p ∧ cut.raw = batchOutput W ∧ cut.raw = some w ∧
    satisfies (samples W) w ∧ (∀ v, satisfies (samples W) v → v = w) ∧
    some w ≠ ReferenceActiveAffinePositiveTest.downSent r.input ∧
    ReferenceDownReception.ordinaryParse p rate (some w) = some M ∧
    OrdinaryMessageCodec.acceptDown (ReferencePrelaunchFollower.codecParams p rate.eta)
      (ReferencePrelaunchFollower.acceptedStart logged) (r.input.time.val + 1) M

/-- The passed physical DOWN call selects this same sender and derives its
expected option from the actual coordinator dispatch. -/
theorem retained_down_sent (r : Record (rate := rate)) (i : Fin (p.m - 1))
    (logged : ReferencePrelaunchFollower.State p rate.eta)
    (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
    (hi : (r.output.followers i).downInput = some logged)
    (hd : (r.output.followers i).down = some cut)
    (hc : cut.rawComparison.isSome = true) :
    cut.expectedWord = ReferenceActiveAffinePositiveTest.downSent r.input := by
  have hf := ReferenceFirstLiveDownCompletionReadout.retained_call_fields r i logged cut hi hd hc
  have hsender : ReferenceActivePhysicalStep.upSenderIndex r.input = i := by
    rw [ReferenceActiveAffinePositiveTest.upSenderIndex_eq_draw]
    exact hf.1.2
  rw [hf.2.2.2.2.2.2.1]
  unfold ReferenceActiveAffinePositiveTest.downSent
  rw [hsender, ← r.output.preparation.coordinator_eq]

/-- A retained DOWN cut carries its actual logged input even on a later
failed follower output. This uses the real tail, not a successful configuration. -/
theorem retained_down_input (r : Record (rate := rate)) (i : Fin (p.m - 1))
    (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
    (hd : (r.output.followers i).down = some cut) :
    ∃ logged, (r.output.followers i).downInput = some logged := by
  have hp := ReferenceDownCompletedAmbiguityMeasurability.record_preparationDiagnostics r i
  have hpair (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
      (prepared : DeclaredFollowerLocalRound.PreparedRound p rate)
      (own : ReferencePrelaunchFollower.Observation p) :
      ((ReferenceActivePhysicalStep.finishFollower view prepared own).downInput,
        (ReferenceActivePhysicalStep.finishFollower view prepared own).down) =
      match prepared.configuration with
      | .dagger => (none, none)
      | .ordinary state _ =>
        let recorded := ReferenceActivePhysicalStep.recordFollower view prepared.follower
          prepared.row prepared.activation prepared.time prepared.active prepared.arm own state
        (recorded.downInput, recorded.down) := by
    cases hcfg : prepared.configuration with
    | dagger => simp only [ReferenceActivePhysicalStep.finishFollower, hcfg]
    | ordinary state memory =>
      simp only [ReferenceActivePhysicalStep.finishFollower, hcfg]
      cases hr : (ReferenceActivePhysicalStep.recordFollower view prepared.follower prepared.row
          prepared.activation prepared.time prepared.active prepared.arm own state).result with
      | error failure => rfl
      | ok post =>
        dsimp only
        cases hf : DeclaredFollowerLocalRound.releaseAndFinish rate prepared.follower prepared.row
            prepared.time own state memory post with
        | error failure => rfl
        | ok next => cases next; rfl
  have hdiag := hpair r.output.preparation.coordinator.downView
    (r.output.preparation.followers.followers i) (preparedOwnObservation r i)
  change ((r.output.preparation.observeFollower i).downInput,
    (r.output.preparation.observeFollower i).down) = _ at hdiag
  rw [hp] at hdiag
  cases hcfg : (r.output.preparation.followers.followers i).configuration with
  | dagger =>
    rw [hcfg] at hdiag
    have hn := congrArg Prod.snd hdiag
    rw [hd] at hn
    cases hn
  | ordinary state memory =>
    rw [hcfg] at hdiag
    dsimp only at hdiag
    by_cases hs : state.status = .unoccupied
    · simp only [ReferenceActivePhysicalStep.recordFollower, dite_eq_left hs] at hdiag
      split at hdiag
      · have hn := congrArg Prod.snd hdiag
        rw [hd] at hn
        cases hn
      · exact ⟨_, congrArg Prod.fst hdiag⟩
    · simp only [ReferenceActivePhysicalStep.recordFollower, dite_eq_right hs] at hdiag
      have hn := congrArg Prod.snd hdiag
      rw [hd] at hn
      cases hn

/-- No call/domain/success premise is needed: a saved wrong DOWN diagnostic
itself produces the reached call and exact completed physical bank. -/
theorem down_wrong_decision_iff (r : Record (rate := rate)) (i : Fin (p.m - 1)) :
    down_wrong_decision r i ↔
      ∃ cut, (r.output.followers i).down = some cut ∧
        ReferenceDownReception.wrongUniqueAccepted cut := by
  constructor
  · rintro ⟨logged, cut, W, w, M, hi, hd, hW, _, _, _, _, hs, hu, hne, hm, ha⟩
    obtain ⟨l, c, hl, hd', hc, _, _⟩ :=
      (ReferenceFirstLiveDownCompletionReadout.completedDownBatch_eq_some_iff r i W).mp hW
    cases hi.symm.trans hl
    cases hd.symm.trans hd'
    refine ⟨cut, hd, (ReferenceFirstLiveDownCompletionReadout.retained_wrongUniqueAccepted_iff
      r i logged cut hi hd).mpr ⟨W, w, hW, hs, hu, ?_, ?_⟩⟩
    · rw [retained_down_sent r i logged cut hi hd hc]
      exact hne
    · rw [hm]
      exact ha
  · rintro ⟨cut, hd, hwrong⟩
    have hc : cut.rawComparison.isSome = true := by rw [hwrong.1]; rfl
    obtain ⟨logged, hi⟩ := retained_down_input r i cut hd
    obtain ⟨W, w, hW, hs, hu, hne, ha⟩ :=
      (ReferenceFirstLiveDownCompletionReadout.retained_wrongUniqueAccepted_iff
        r i logged cut hi hd).mp hwrong
    obtain ⟨hlen, l, c, hl, hd', _, hbank, _, hraw⟩ :=
      ReferenceFirstLiveDownCompletionReadout.completedDownBatch_spec r i W hW
    cases hi.symm.trans hl
    cases hd.symm.trans hd'
    have hw := (ReferenceFirstLiveDownCompletionReadout.completed_raw_some_iff
      r i W hW cut hd w).mpr ⟨hs, hu⟩
    cases hm : ReferenceDownReception.ordinaryParse p rate (some w) with
    | none => rw [hm] at ha; exact ha.elim
    | some M =>
      refine ⟨logged, cut, W, w, M, hi, hd, hW, hbank, hlen, hraw, hw,
        hs, hu, ?_, hm, ?_⟩
      · rw [← retained_down_sent r i logged cut hi hd hc]
        exact hne
      · rw [hm] at ha
        exact ha

/-- A literal UP decision retains the original selected receiver bank and
its current positive append. The ordinary parser runs on the unique raw
solver, before reference mismatch filtering and collection finish. -/
def up_wrong_decision (r : Record (rate := rate)) (i : Fin (p.m - 1)) : Prop :=
  ∃ (d : ReferenceActivePhysicalStep.UpDiagnostic p rate)
      (W : Batch (p := p)) (w : Word (p := p)),
    r.output.coordinator.up = some d ∧ d.input.selectedFollower = i ∧
    ReferenceCollectionUpFailureReadoutV2.completedUpBatch rate r i = some W ∧
    W = (d.input.upDecoderBank i).pending ++
      positiveAt p (CoordinatorUpReception.traceAt d.input) d.input.time ∧
    W.length = quota p ∧ d.raw = batchOutput W ∧ d.raw = some w ∧
    satisfies (samples W) w ∧ (∀ v, satisfies (samples W) v → v = w) ∧
    ordinary_up_wrong d.input (some w) (ReferenceActiveAffinePositiveTest.upSent r.input)

/-- The saved UP flag is the ordinary raw decision, independent of the
reference-filtered reception result. This is a property of any actual call. -/
private theorem receive_up_flag {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (d : ReferenceActivePhysicalStep.UpDiagnostic p rate)
    (hd : (ReferenceActivePhysicalStep.receiveUp prepared ledger).diagnostic = some d) :
    d.wrongUniqueAccepted = true ↔ ordinary_up_wrong d.input d.raw d.expected := by
  unfold ReferenceActivePhysicalStep.receiveUp at hd
  dsimp only at hd
  split at hd
  · simp only [Option.some.injEq] at hd
    subst d
    dsimp only
    have hflag := ReferenceUpReception.wrongUniqueAndLocalAcceptanceAtRow_eq_true_iff
      rate x.row (ReferenceActivePhysicalStep.upInputs prepared ledger) x.time
      (prepared.followers.followers (ReferenceActivePhysicalStep.upSenderIndex x))
      (prepared.follower_alignment _).1 (prepared.follower_alignment _).2.1
      (prepared.follower_alignment _).2.2.1 rfl
    constructor
    · intro h
      obtain ⟨w, M, hw, hm, ha, hn⟩ := hflag.mp h
      exact ⟨w, M, hw, hn, hm, ha⟩
    · rintro ⟨w, M, hw, hn, hm, ha⟩
      exact hflag.mpr ⟨w, M, hw, hm, ha, hn⟩
  · cases hd

private theorem collection_up_flag {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ)
    (d : ReferenceActivePhysicalStep.UpDiagnostic p rate)
    (hd : (ReferenceActivePhysicalStep.collectionPostChoice prepared payload ledger started weights).up = some d) :
    d.wrongUniqueAccepted = true ↔ ordinary_up_wrong d.input d.raw d.expected := by
  unfold ReferenceActivePhysicalStep.collectionPostChoice at hd
  split at hd
  · cases hd
  · dsimp only at hd
    split at hd
    · cases hd
    · cases hd
    · rw [ReferenceActiveAffinePositiveTest.collectionFinish_up] at hd
      exact receive_up_flag prepared _ d hd

/-- The complete actual dispatch preserves the flag law even when later
reception, reconstruction, ledger finish, or clock finish fails. -/
theorem retained_up_flag (r : Record (rate := rate))
    (d : ReferenceActivePhysicalStep.UpDiagnostic p rate)
    (hd : r.output.coordinator.up = some d) :
    d.wrongUniqueAccepted = true ↔ ordinary_up_wrong d.input d.raw d.expected := by
  have hout : r.output.coordinator.up =
      (ReferenceActivePhysicalStep.prepare r.input).observeCoordinator.up := by
    rw [r.output_eq]
    rfl
  rw [hout] at hd
  generalize hp : ReferenceActivePhysicalStep.prepare r.input = prepared at hd
  rcases prepared with ⟨cut, hcut, followers⟩
  cases cut with
  | dagger => cases hd
  | invalidCollectionCutoff => cases hd
  | first outcome =>
    cases outcome <;>
      (unfold ReferenceActivePhysicalStep.PreparedRound.observeCoordinator at hd
       split at hd <;> first
       | cases hd
       | have hn := (ReferenceUpPhysicalHashRule.livePostChoice_up_none _ _ _ _ _).symm.trans hd
         cases hn)
  | live registers owned base outcome =>
    cases outcome <;>
      (unfold ReferenceActivePhysicalStep.PreparedRound.observeCoordinator at hd
       split at hd <;> first
       | cases hd
       | exact collection_up_flag _ _ _ _ _ d hd
       | have hn := (ReferenceUpPhysicalHashRule.livePostChoice_up_none _ _ _ _ _).symm.trans hd
         cases hn)
  | collection payload ledger clock cutoff outcome =>
    cases outcome <;>
      (unfold ReferenceActivePhysicalStep.PreparedRound.observeCoordinator at hd
       split at hd <;> first
       | cases hd
       | exact collection_up_flag _ _ _ _ _ d hd
       | have hn := (ReferenceUpPhysicalHashRule.livePostChoice_up_none _ _ _ _ _).symm.trans hd
         cases hn)

/-- The retained expected UP option is the actual prepared follower offer,
including failed/non-offers and dagger senders. -/
theorem retained_up_sent (r : Record (rate := rate))
    (d : ReferenceActivePhysicalStep.UpDiagnostic p rate)
    (hd : r.output.coordinator.up = some d) :
    d.expected = ReferenceActiveAffinePositiveTest.upSent r.input := by
  obtain ⟨ledger, _, _, _, _, _, _, _, _, he, _⟩ :=
    ReferenceGeneratedUpBatchCalendar.record_up_executed_fields r d hd
  simpa only [ReferenceGeneratedAffineHashHalf.directionSent, show (1 : Fin 2) ≠ 0 from by decide,
    ite_false] using he

/-- A returned raw UP word produces a completed actual physical bank. The
input check and eligibility are derived from the reached call and bank domain. -/
theorem retained_up_raw_completion (r : Record (rate := rate))
    (d : ReferenceActivePhysicalStep.UpDiagnostic p rate)
    (hd : r.output.coordinator.up = some d) (w : Word (p := p))
    (hw : d.raw = some w) :
    ReferenceCollectionUpFailureReadoutV2.completedUpBatch rate r d.input.selectedFollower =
      some (ReferenceCollectionUpFailureReadoutV2.appendedUp rate d) := by
  obtain ⟨ledger, _, hcheck, hinput, _, hraw, _⟩ :=
    ReferenceGeneratedUpBatchCalendar.record_up_executed_fields r d hd
  have hc : CoordinatorUpReception.receptionInputCheck d.input = true := by
    rw [hinput]
    exact hcheck
  have hdom := (CoordinatorUpReception.receptionInputCheck_eq_true_iff d.input).mp hc
  obtain ⟨_, _, _, _, _, _, _, hbank⟩ :=
    CoordinatorUpReception.receptionInputDomain_parts d.input hdom
  have hs : stepOutput p (CoordinatorUpReception.traceAt d.input)
      (d.input.upDecoderBank d.input.selectedFollower) d.input.time = some w :=
    hraw.symm.trans hw
  have hquota := (stepOutput_eq_some_iff p _ _ _ w).mp hs |>.1
  have hel : eligible (CoordinatorUpReception.roundInput d.input) := by
    by_contra hn
    have hnil : positiveAt p (CoordinatorUpReception.traceAt d.input) d.input.time = [] := by
      simp only [positiveAt, CoordinatorUpReception.traceAt, hn, ite_false]
    rw [hnil, List.append_nil] at hquota
    exact (Nat.not_le_of_lt (hbank d.input.selectedFollower).1) hquota
  exact (ReferenceCollectionUpFailureReadoutV2.completedUpBatch_eq_some_iff rate r _ _).mpr
    ⟨d, hd, rfl, hc, hel, hquota, rfl⟩

/-- Direction-specific equivalence with the actual saved UP diagnostic.
No pre-call guard, positive feedback, solver, or successful finish is assumed. -/
theorem up_wrong_decision_iff (r : Record (rate := rate)) (i : Fin (p.m - 1)) :
    up_wrong_decision r i ↔
      ∃ d, r.output.coordinator.up = some d ∧ d.input.selectedFollower = i ∧
        d.wrongUniqueAccepted = true := by
  constructor
  · rintro ⟨d, W, w, hd, hi, _, _, _, _, hw, _, _, ha⟩
    refine ⟨d, hd, hi, (retained_up_flag r d hd).mpr ?_⟩
    rw [hw, retained_up_sent r d hd]
    exact ha
  · rintro ⟨d, hd, hi, hwrong⟩
    have ha := (retained_up_flag r d hd).mp hwrong
    obtain ⟨w, M, hw, hn, hm, hacc⟩ := ha
    have hW := retained_up_raw_completion r d hd w hw
    rw [hi] at hW
    let W := ReferenceCollectionUpFailureReadoutV2.appendedUp rate d
    obtain ⟨hlen, d', hd', hi', _, hraw⟩ :=
      ReferenceCollectionUpFailureReadoutV2.completedUpBatch_spec rate r i W hW
    cases hd.symm.trans hd'
    have hsol : satisfies (samples W) w ∧ ∀ v, satisfies (samples W) v → v = w :=
      (solve_eq_some_iff (samples W) w).mp (hraw.symm.trans hw)
    refine ⟨d, W, w, hd, hi, hW, ?_, hlen, hraw, hw, hsol.1, hsol.2, ?_⟩
    · simp only [W, ReferenceCollectionUpFailureReadoutV2.appendedUp, hi]
    · exact ⟨w, M, rfl, (retained_up_sent r d hd) ▸ hn, hm, hacc⟩

/-- A completed literal UP decision retains the original time, whole bank,
affine sample, and executed coordinator observation, even on later failure. -/
theorem up_wrong_decision_original_fields (r : Record (rate := rate))
    (i : Fin (p.m - 1)) (h : up_wrong_decision r i) :
    ∃ d, r.output.coordinator.up = some d ∧ d.input.selectedFollower = i ∧
      d.input.time = r.input.time ∧
      d.input.upDecoderBank = r.input.state.upDecoderBank ∧
      d.input.affineSample = ((r.input.rows r.input.selected).2 r.input.time).2
        (1, CoordinatorUpMeasurability.selectedChannelFollower
          ((r.input.rows r.input.selected).2 r.input.time)) ∧
      d.input.ownObservation =
        (ReferenceActivePhysicalStep.prepare r.input).feedback.feedback
          (ActiveRoundActions.coordinator p.two_le_m) ∧
      d.expected = ReferenceActiveAffinePositiveTest.upSent r.input := by
  obtain ⟨d, hd, hi, _⟩ := (up_wrong_decision_iff r i).mp h
  obtain ⟨ledger, _, _, _, _, _, _, _, _, _, ht, hb, hs, ho⟩ :=
    ReferenceGeneratedUpBatchCalendar.record_up_executed_fields r d hd
  exact ⟨d, hd, hi, ht, hb, hs, ho, retained_up_sent r d hd⟩

/-- No completion is no literal DOWN wrong-unique decision. -/
theorem down_wrong_absent_of_no_completion (r : Record (rate := rate))
    (i : Fin (p.m - 1))
    (h : ReferenceFirstLiveDownCompletionReadout.completedDownBatch r i = none) :
    ¬ down_wrong_decision r i := by
  rintro ⟨_, _, W, _, _, _, _, hW, _⟩
  rw [h] at hW
  cases hW

/-- Missing logged input or missing cut cannot produce a physical decision. -/
theorem down_wrong_absent_of_missing_call (r : Record (rate := rate))
    (i : Fin (p.m - 1))
    (h : (r.output.followers i).downInput = none ∨ (r.output.followers i).down = none) :
    ¬ down_wrong_decision r i := by
  apply down_wrong_absent_of_no_completion r i
  rcases h with hi | hd
  · exact ReferenceFirstLiveDownCompletionReadout.completedDownBatch_eq_none_of_no_input r i hi
  · exact ReferenceFirstLiveDownCompletionReadout.completedDownBatch_eq_none_of_no_cut r i hd

/-- A skipped or failed pre-call DOWN operation is not a completion. -/
theorem down_wrong_absent_of_not_called (r : Record (rate := rate))
    (i : Fin (p.m - 1)) (logged : ReferencePrelaunchFollower.State p rate.eta)
    (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
    (hi : (r.output.followers i).downInput = some logged)
    (hd : (r.output.followers i).down = some cut) (hc : cut.rawComparison = none) :
    ¬ down_wrong_decision r i :=
  down_wrong_absent_of_no_completion r i
    (ReferenceFirstLiveDownCompletionReadout.completedDownBatch_eq_none_of_not_called
      r i logged cut hi hd hc)

/-- Failure of any actual DOWN pre-call check suppresses the call, rather
than being a wrong unique ordinary decision. -/
theorem down_wrong_absent_of_failed_precheck (r : Record (rate := rate))
    (i : Fin (p.m - 1)) (logged : ReferencePrelaunchFollower.State p rate.eta)
    (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
    (hi : (r.output.followers i).downInput = some logged)
    (hd : (r.output.followers i).down = some cut)
    (hfail : ¬ ActiveFollowerDownAcceptance.downSelected p i r.input.row r.input.time ∨
      logged.status ≠ .unoccupied ∨
      ¬ ActiveFollowerDownAcceptance.registerInputDomain p rate logged ∨
      ¬ ActiveFollowerDownAcceptance.decoderInputDomain p logged.downBatch ∨
      ¬ ActiveFollowerDownAcceptance.bufferInputDomain p logged.buffer) :
    ¬ down_wrong_decision r i := by
  apply down_wrong_absent_of_not_called r i logged cut hi hd
  have he := ReferenceDownCompletedAmbiguityMeasurability.record_downCut_eq_actual
    r i logged cut hi hd
  rw [he]
  rcases hfail with h | h | h | h | h <;>
    (unfold ReferenceDownReception.referenceDownCut
     split_ifs <;> simp_all only)

/-- A passed incomplete DOWN bank is neither ambiguous nor wrong unique. -/
theorem down_wrong_absent_of_incomplete (r : Record (rate := rate))
    (i : Fin (p.m - 1)) (logged : ReferencePrelaunchFollower.State p rate.eta)
    (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
    (hi : (r.output.followers i).downInput = some logged)
    (hd : (r.output.followers i).down = some cut) (hc : cut.rawComparison.isSome = true)
    (hsmall : (ReferenceFirstLiveDownCompletionReadout.appendedDownBatch r i logged).length < quota p) :
    ¬ down_wrong_decision r i :=
  down_wrong_absent_of_no_completion r i
    (ReferenceFirstLiveDownCompletionReadout.retained_incomplete_raw_none
      r i logged cut hi hd hc hsmall).1

/-- Raw absence, whether inconsistency or ambiguity, is not a wrong unique
DOWN decision. -/
theorem down_wrong_absent_of_raw_none (r : Record (rate := rate))
    (i : Fin (p.m - 1)) (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
    (hd : (r.output.followers i).down = some cut) (hn : cut.raw = none) :
    ¬ down_wrong_decision r i := by
  rintro ⟨_, c, _, w, _, _, hd', _, _, _, _, hw, _⟩
  cases hd.symm.trans hd'
  rw [hn] at hw
  cases hw

/-- Ordinary parse or local acceptance rejection cannot set this DOWN event. -/
theorem down_wrong_absent_of_local_rejection (r : Record (rate := rate))
    (i : Fin (p.m - 1)) (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
    (hd : (r.output.followers i).down = some cut) (ha : ¬ cut.ordinaryAcceptance) :
    ¬ down_wrong_decision r i := by
  intro h
  obtain ⟨c, hd', hw⟩ := (down_wrong_decision_iff r i).mp h
  cases hd.symm.trans hd'
  exact ha hw.2.2

/-- A wrong raw DOWN decision survives reference suppression as an ordinary
raw/parse/acceptance diagnostic; its reference-filtered raw is absent. -/
theorem down_wrong_filtered_none (r : Record (rate := rate))
    (i : Fin (p.m - 1)) (h : down_wrong_decision r i) :
    ∃ (logged : ReferencePrelaunchFollower.State p rate.eta)
        (cut : ReferenceDownReception.ReferenceDownCutOutput p rate),
      (r.output.followers i).downInput = some logged ∧
      (r.output.followers i).down = some cut ∧ cut.filteredRaw = none ∧
      cut.ordinaryAcceptance ∧
      cut.ordinaryParse = ReferenceDownReception.ordinaryParse p rate cut.raw := by
  obtain ⟨cut, hd, hw⟩ := (down_wrong_decision_iff r i).mp h
  obtain ⟨logged, hi⟩ := retained_down_input r i cut hd
  have hc : cut.rawComparison.isSome = true := by rw [hw.1]; rfl
  obtain ⟨hsel, hstatus, hreg, hbank, hbuffer, _, _, hparse, _⟩ :=
    ReferenceFirstLiveDownCompletionReadout.retained_call_fields r i logged cut hi hd hc
  have he := ReferenceDownCompletedAmbiguityMeasurability.record_downCut_eq_actual r i logged cut hi hd
  have hpres := ReferenceDownReception.referenceDownCut_raw_mismatch_preserves
    r.output.preparation.coordinator.downView i r.input.row r.input.time
    (preparedOwnObservation r i) rate logged hsel hstatus hreg hbank hbuffer
    (show ReferenceDownReception.rawMismatch
      (ReferenceDownReception.referenceDownCut p r.output.preparation.coordinator.downView
        i r.input.row r.input.time (preparedOwnObservation r i) rate logged) from he ▸ hw.1)
  rw [← he] at hpres
  exact ⟨logged, cut, hi, hd, hpres.2.2.1, hw.2.2, hparse⟩

/-- Missing/incomplete physical UP completion has no literal wrong decision. -/
theorem up_wrong_absent_of_no_completion (r : Record (rate := rate))
    (i : Fin (p.m - 1))
    (h : ReferenceCollectionUpFailureReadoutV2.completedUpBatch rate r i = none) :
    ¬ up_wrong_decision r i := by
  rintro ⟨_, W, _, _, _, hW, _⟩
  rw [h] at hW
  cases hW

/-- Missing UP calls stay absent. -/
theorem up_wrong_absent_of_missing_call (r : Record (rate := rate))
    (i : Fin (p.m - 1)) (h : r.output.coordinator.up = none) :
    ¬ up_wrong_decision r i :=
  up_wrong_absent_of_no_completion r i
    (ReferenceCollectionUpFailureReadoutV2.completedUpBatch_eq_none_of_no_up rate r i h)

/-- Failed input checks, ineligibility, and incomplete banks are separate
non-decisions; none is classified as wrong unique. -/
theorem up_wrong_absent_of_failed_or_incomplete_call (r : Record (rate := rate))
    (i : Fin (p.m - 1)) (d : ReferenceActivePhysicalStep.UpDiagnostic p rate)
    (hd : r.output.coordinator.up = some d)
    (h : CoordinatorUpReception.receptionInputCheck d.input = false ∨
      ¬ eligible (CoordinatorUpReception.roundInput d.input) ∨
      (ReferenceCollectionUpFailureReadoutV2.appendedUp rate d).length < quota p) :
    ¬ up_wrong_decision r i := by
  apply up_wrong_absent_of_no_completion r i
  rcases h with hc | hn | hs
  · exact ReferenceCollectionUpFailureReadoutV2.completedUpBatch_eq_none_of_input_check_false
      rate r i d hd hc
  · exact ReferenceCollectionUpFailureReadoutV2.completedUpBatch_eq_none_of_ineligible
      rate r i d hd hn
  · obtain ⟨ledger, _, hc, he, _⟩ :=
      ReferenceGeneratedUpBatchCalendar.record_up_executed_fields r d hd
    have hcheck : CoordinatorUpReception.receptionInputCheck d.input = true := by
      rw [he]
      exact hc
    by_cases hel : eligible (CoordinatorUpReception.roundInput d.input)
    · exact ReferenceCollectionUpFailureReadoutV2.completedUpBatch_eq_none_of_incomplete
        rate r i d hd hcheck hel hs
    · exact ReferenceCollectionUpFailureReadoutV2.completedUpBatch_eq_none_of_ineligible
        rate r i d hd hel

/-- A completed raw `none` has two solver explanations, independent of parsing
or acceptance. Neither is a wrong unique output. -/
theorem batch_raw_none_iff (W : Batch (p := p)) :
    batchOutput W = none ↔ (∀ w, ¬ satisfies (samples W) w) ∨
      ∃ w v, satisfies (samples W) w ∧ satisfies (samples W) v ∧ w ≠ v :=
  solve_eq_none_iff_empty_or_ambiguous (samples W)

/-- Raw absence, ordinary parse rejection, or failed ordinary Acc excludes a
literal UP wrong decision. These tests precede filtered reconstruction. -/
theorem up_wrong_absent_of_raw_or_local_rejection (r : Record (rate := rate))
    (i : Fin (p.m - 1)) (d : ReferenceActivePhysicalStep.UpDiagnostic p rate)
    (hd : r.output.coordinator.up = some d)
    (h : d.raw = none ∨
      CoordinatorUpReception.parseDecoderOutput (p := p) (eta := rate.eta.val) d.raw = none ∨
      (∀ M, CoordinatorUpReception.parseDecoderOutput (p := p) (eta := rate.eta.val) d.raw = some M →
        CoordinatorCollectionLedger.acceptUpCheck d.input.ledger d.input.selectedFollower M = false)) :
    ¬ up_wrong_decision r i := by
  intro hwrong
  obtain ⟨d', hd', _, hflag⟩ := (up_wrong_decision_iff r i).mp hwrong
  cases hd.symm.trans hd'
  obtain ⟨w, M, hw, _, hm, ha⟩ := (retained_up_flag r d hd).mp hflag
  rcases h with hn | hp | hr
  · rw [hn] at hw
    cases hw
  · rw [hw, hm] at hp
    cases hp
  · have hf := hr M (hw ▸ hm)
    rw [ha] at hf
    cases hf

/-- The actual initial UP placeholder is unaccepted on every retained input,
even if it is the unique raw solution. This is not an ambiguity claim. -/
theorem up_wrong_absent_of_placeholder (r : Record (rate := rate))
    (i : Fin (p.m - 1)) (d : ReferenceActivePhysicalStep.UpDiagnostic p rate)
    (hd : r.output.coordinator.up = some d)
    (hp : CoordinatorUpReception.parseDecoderOutput (p := p) (eta := rate.eta.val) d.raw =
      some (CoordinatorUpReception.placeholderUpRecord p rate.eta.val)) :
    ¬ up_wrong_decision r i := by
  apply up_wrong_absent_of_raw_or_local_rejection r i d hd
  right
  right
  intro M hm
  cases hp.symm.trans hm
  obtain ⟨ledger, _, hc, he, _⟩ :=
    ReferenceGeneratedUpBatchCalendar.record_up_executed_fields r d hd
  have hcheck : CoordinatorUpReception.receptionInputCheck d.input = true := by
    rw [he]
    exact hc
  have hdom := (CoordinatorUpReception.receptionInputCheck_eq_true_iff d.input).mp hcheck
  apply Bool.eq_false_iff.mpr
  intro ha
  exact CoordinatorUpReception.placeholder_not_literal_acceptUp d.input hdom
    ((CoordinatorCollectionLedger.acceptUpCheck_iff _ _ _).mp ha)

section WholeSource

variable (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)

open ReferenceGeneratedPrelaunchDownPrefix ReferencePrelaunchFollower
open ReferenceInitializationRun BootstrapDimensions

/-- One actual postlaunch DOWN raw decision at its original source date.
The absent-record branch stays absent. -/
def source_down_wrong (z : BootstrapPrivateRoundStreams.SourceInput p)
    (t : Fin p.T) (i : Fin (p.m - 1)) : Prop :=
  ∃ r : Record (rate := rate),
    ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some r ∧
    down_wrong_decision r i

/-- One actual postlaunch UP raw decision, on the original whole source. -/
def source_up_wrong (z : BootstrapPrivateRoundStreams.SourceInput p)
    (t : Fin p.T) (i : Fin (p.m - 1)) : Prop :=
  ∃ r : Record (rate := rate),
    ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some r ∧
    up_wrong_decision r i

/-- Full-source DOWN dictionary, without a launch, domain, or success input. -/
theorem source_down_wrong_iff (z : BootstrapPrivateRoundStreams.SourceInput p)
    (t : Fin p.T) (i : Fin (p.m - 1)) :
    source_down_wrong rate rewards C_star C_h z t i ↔
      ∃ (r : Record (rate := rate)) (cut : ReferenceDownReception.ReferenceDownCutOutput p rate),
        ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some r ∧
        (r.output.followers i).down = some cut ∧ ReferenceDownReception.wrongUniqueAccepted cut := by
  constructor
  · rintro ⟨r, hr, h⟩
    obtain ⟨cut, hd, hw⟩ := (down_wrong_decision_iff r i).mp h
    exact ⟨r, cut, hr, hd, hw⟩
  · rintro ⟨r, cut, hr, hd, hw⟩
    exact ⟨r, hr, (down_wrong_decision_iff r i).mpr ⟨cut, hd, hw⟩⟩

/-- Full-source UP dictionary on the original selected receiver channel. -/
theorem source_up_wrong_iff (z : BootstrapPrivateRoundStreams.SourceInput p)
    (t : Fin p.T) (i : Fin (p.m - 1)) :
    source_up_wrong rate rewards C_star C_h z t i ↔
      ∃ (r : Record (rate := rate)) (d : ReferenceActivePhysicalStep.UpDiagnostic p rate),
        ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some r ∧
        r.output.coordinator.up = some d ∧ d.input.selectedFollower = i ∧
        d.wrongUniqueAccepted = true := by
  constructor
  · rintro ⟨r, hr, h⟩
    obtain ⟨d, hd, hi, hw⟩ := (up_wrong_decision_iff r i).mp h
    exact ⟨r, d, hr, hd, hi, hw⟩
  · rintro ⟨r, d, hr, hd, hi, hw⟩
    exact ⟨r, hr, (up_wrong_decision_iff r i).mpr ⟨d, hd, hi, hw⟩⟩

/-- Both ordinary raw directions identify the saved wrong-unique diagnostic
on the actual source record. This contains no ambiguity or source-stop claim. -/
theorem actual_raw_wrong_decision_iff_saved_diagnostic
    (z : BootstrapPrivateRoundStreams.SourceInput p) (t : Fin p.T) :
    ((∃ i, source_down_wrong rate rewards C_star C_h z t i) ∨
      (∃ i, source_up_wrong rate rewards C_star C_h z t i)) ↔
      ∃ r : Record (rate := rate),
        ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some r ∧
        ReferenceActiveStoppedPrefixCoupling.saved_wrong_unique_accepted r := by
  constructor
  · rintro (⟨i, hi⟩ | ⟨i, hi⟩)
    · obtain ⟨r, cut, hr, hd, hw⟩ := (source_down_wrong_iff rate rewards C_star C_h z t i).mp hi
      exact ⟨r, hr, Or.inr ⟨i, cut, hd, hw⟩⟩
    · obtain ⟨r, d, hr, hd, _, hw⟩ := (source_up_wrong_iff rate rewards C_star C_h z t i).mp hi
      exact ⟨r, hr, Or.inl ⟨d, hd, hw⟩⟩
  · rintro ⟨r, hr, hwrong⟩
    rcases hwrong with ⟨d, hd, hw⟩ | ⟨i, cut, hd, hw⟩
    · exact Or.inr ⟨d.input.selectedFollower,
        (source_up_wrong_iff rate rewards C_star C_h z t _).mpr ⟨r, d, hr, hd, rfl, hw⟩⟩
    · exact Or.inl ⟨i,
        (source_down_wrong_iff rate rewards C_star C_h z t i).mpr ⟨r, cut, hr, hd, hw⟩⟩

/-- The independent literal prelaunch ordinary decision. It retains the exact
strict-prefix test census, the pending suffix, current append, unique solver,
ordinary DOWN parser/Acc, actual absent sent word, and suppressed registers. -/
def prelaunch_down_wrong (z : BootstrapPrivateRoundStreams.SourceInput p)
    (t : Fin p.T) (i : Fin (p.m - 1)) : Prop :=
  let x := sourceReferenceInput rate rewards C_star C_h z
  ∃ active : ActiveProjection p i t.val x.row (Nat.le_of_lt t.isLt) x (roundBlockIndex p t),
    source_prelaunch_down_prefix rate rewards C_star C_h z i t = .inl (.inl active) ∧
    ∃ (W : Batch (p := p)) (w : Word (p := p)) (M : Down (rate := rate))
        (test : ReferenceGeneratedDownBatchCalendar.ExecutedTest p),
      let own := ownEntry (physical x active.val.1.val active.val.1.property.1)
        (PublicDiscreteDraws.followerPlayer p.two_le_m
          (ActualReferenceInitializationBlock.refFollower i)) t
      let bank := active.val.2.2.2.downBatch
      let tests := source_prelaunch_down_prefix_tests rate rewards C_star C_h z i t
      W = bank.pending ++ positiveAt p (traceAt i x.row active.val.2.1 t own) t ∧
      W.length = quota p ∧
      (decodeAt i x.row active.val.2.1 t own bank).2 = batchOutput W ∧
      batchOutput W = some w ∧
      satisfies (samples W) w ∧ (∀ v, satisfies (samples W) v → v = w) ∧
      ReferenceDownReception.ordinaryParse p rate (some w) = some M ∧
      (OrdinaryMessageCodec.wordEquivFlat (ReferencePrelaunchFollower.codecParams p rate.eta)).symm w =
        OrdinaryMessageCodec.encodeDown (ReferencePrelaunchFollower.codecParams p rate.eta) M ∧
      OrdinaryMessageCodec.acceptDown (ReferencePrelaunchFollower.codecParams p rate.eta)
        0 (t.val + 1) M ∧
      tests.map ReferenceGeneratedPrelaunchDownCohort.testEntry = collected bank ∧
      bank.pending = (tests.map ReferenceGeneratedPrelaunchDownCohort.testEntry).drop
        (quota p * bank.completed.length) ∧
      test = ⟨t, (x.row.2 t).2 (0, i), none⟩ ∧ test.sent = none ∧ some w ≠ test.sent ∧
      ReferenceGeneratedPrelaunchDownCohort.prelaunchTest i x.row active.val.2.1 t own = some test ∧
      source_prelaunch_down_current_test rate rewards C_star C_h z i t = some test ∧
      coordinatorLearner active.val.1.val = none ∧
      active.val.2.2.2.lastDown = none ∧ acceptedStart active.val.2.2.2 = 0 ∧
      active.val.2.2.2.S = 0 ∧ active.val.2.2.2.delta = 0 ∧
      active.val.2.2.2.backlog = 0 ∧ active.val.2.2.2.status = .unoccupied ∧
      let after := ReferencePrelaunchFollower.step i x.row active.val.2.1 t own active.val.2.2.2
      after.lastDown = none ∧ after.S = 0 ∧ after.delta = 0 ∧
        after.backlog = 0 ∧ after.status = .unoccupied

/-- Prelaunch uses the actual selector and ordinary call; the current word
is absent and a passing decision has no assignment effects. No postlaunch
record, fixed awaited word, or successful output is postulated. -/
theorem prelaunch_down_wrong_iff (z : BootstrapPrivateRoundStreams.SourceInput p)
    (t : Fin p.T) (i : Fin (p.m - 1)) :
    prelaunch_down_wrong rate rewards C_star C_h z t i ↔
      ReferencePrelaunchDownDecisionReadout.prelaunchDownFailureAt
        rate rewards C_star C_h z i t = true := by
  constructor
  · rintro ⟨active, hpref, W, w, M, test, hW, hlen, hraw, hw, hs, hu, hm, he, ha, _⟩
    apply (ReferencePrelaunchDownDecisionReadout.prelaunchDownFailureAt_completedBatch_iff
      rate rewards C_star C_h z i t).mpr
    subst W
    exact ⟨active, hpref, w, M, hraw.trans hw, hlen, hw, hs, hu, hm, he, ha⟩
  · intro hfail
    obtain ⟨active, hpref, w, M, hraw, hlen, hw, hs, hu, hm, he, ha⟩ :=
      (ReferencePrelaunchDownDecisionReadout.prelaunchDownFailureAt_completedBatch_iff
        rate rewards C_star C_h z i t).mp hfail
    obtain ⟨active', hpref', test, ht, hn, _, htest, hcurrent, hlearner, _⟩ :=
      ReferencePrelaunchDownDecisionReadout.prelaunchDownFailureAt_currentAbsentWord
        rate rewards C_star C_h z i t hfail
    have heq : active' = active := Sum.inl.inj (Sum.inl.inj (hpref'.symm.trans hpref))
    subst active'
    have hcensus := source_prelaunch_down_prefix_census rate rewards C_star C_h z i t
    rw [hpref] at hcensus
    have hregisters := ReferencePrelaunchDownDecisionReadout.prelaunch_active_registers
      rate rewards C_star C_h z i t active
    refine ⟨active, hpref, _, w, M, test, rfl, hlen, hraw.trans hw.symm,
      hw, hs, hu, hm, he, ha, hcensus.1, hcensus.2.1, ht, hn, ?_,
      htest, hcurrent, hlearner, hregisters.1, hregisters.2.1,
      hregisters.2.2.1, hregisters.2.2.2.1, hregisters.2.2.2.2.1,
      hregisters.2.2.2.2.2, ?_⟩
    · rw [hn]
      exact Option.some_ne_none w
    · have hframe := ReferencePrelaunchFollower.step_registers i
        (sourceReferenceInput rate rewards C_star C_h z).row active.val.2.1 t
        (ownEntry (physical (sourceReferenceInput rate rewards C_star C_h z)
          active.val.1.val active.val.1.property.1)
          (PublicDiscreteDraws.followerPlayer p.two_le_m
            (ActualReferenceInitializationBlock.refFollower i)) t) active.val.2.2.2
      exact ⟨hframe.1.trans hregisters.1,
        hframe.2.1.trans hregisters.2.2.1,
        hframe.2.2.1.trans hregisters.2.2.2.1,
        hframe.2.2.2.1.trans hregisters.2.2.2.2.1,
        hframe.2.2.2.2.trans hregisters.2.2.2.2.2⟩

/-- Missing actual postlaunch records cannot manufacture either direction's
raw decision. This covers future/terminal/no-launch suffix absence. -/
theorem source_wrong_absent_of_no_record
    (z : BootstrapPrivateRoundStreams.SourceInput p) (t : Fin p.T)
    (h : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = none) :
    (∀ i, ¬ source_down_wrong rate rewards C_star C_h z t i) ∧
      (∀ i, ¬ source_up_wrong rate rewards C_star C_h z t i) := by
  constructor
  · rintro i ⟨r, hr, _⟩
    rw [h] at hr
    cases hr
  · rintro i ⟨r, hr, _⟩
    rw [h] at hr
    cases hr

end WholeSource

end Bandits.Support.ReferenceSourceRawDecoderDecision

end
