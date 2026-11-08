/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveStepMeasurability
public import Bandits.Support.ReferenceCollectionOutcomeMeasurability

/-!
# Composition of one canonical active physical step

Sources: `sources/zip4/manuscript/06_interruptions.tex:30-70,235-296`,
`sources/zip4/manuscript/appendix_a_local_protocol.tex:6-14,28-64`, and
`sources/zip4/manuscript/08_main_theorem.tex:29-42`.

The input and all observation/state codes are the existing canonical ones.
Only the incoming tag is used for branch decomposition. Continuous rows,
anchors, complement weights and saved observations retain their original
Borel spaces. This is internal deterministic mathematics, with no horizon,
execution invariant, sampling law or manuscript/regret closure assertion.

The unrestricted measurability exports have only the existing parameters:
`p` contains `K,m,T`, `2 ≤ m`, `m < K`, and `1 ≤ T`; `rate` contains positive
`eta`, its source cap, `n : ℕ`, and `(n : ℝ) = eta * D p`. `RoundInput` contains
the original state, ALL complete rows, selected `J`, time, full grid rewards,
and the original active-time typing proof for every follower. No runtime
validity, truth, success, law or producer-measurability premise is added.

The two conditional public bridges expose their entire extra input:
`collection_installed_observation` takes a local product `z`, a numerical
installation/clock pair and equality to the actual dispatch's data projection;
`collection_observation_eq` takes the original round, payload, ledger,
proposal, cutoff and equality to the literal prepared dispatch. Both premises
are discharged inside the canonical proof. The private substitution lemma
lists six primitive maps and their six measurability proofs. The private
sum/Option lemmas list each branch, selector and measurability proof. These
are internal composition lemmas, not source-facing statements.

Direct dependency hashes: FIRST/LIVE STEP
`56b8caa3116ebcbb8ed7c9c78527c6ded992870527cc43520ef9265fb1de4628`;
repaired COLLECTION outcome
`3a0ca1bf00338774710aeee67af26aa13b74314ed504e07f627e59d7c1f3b22b`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalStepMeasurability

namespace Bandits.Support.ReferenceActiveStepCompositionMeasurability

variable {p : Parameters} {rate : RateInput p}

-- These are the existing countable clock skeletons; no continuous fiber is changed.
local instance : MeasurableSpace (CoordinatorPhaseClock.StartRoundResult p) := ⊤
local instance : MeasurableSpace (ReferenceCollectionDispatchMeasurability.ClockObservation p) := ⊤

/-- Exactly the incoming COLLECTION tag, with no successful-domain restriction. -/
def collectionSet : Set (RoundInput p rate) := ReferenceFirstLiveCoordinatorStepMeasurability.firstLiveSetᶜ

abbrev CollectionInput (p : Parameters) (rate : RateInput p) :=
  ↥(collectionSet (p := p) (rate := rate))

theorem measurableSet_collectionSet :
    MeasurableSet (collectionSet (p := p) (rate := rate)) :=
  ReferenceFirstLiveCoordinatorStepMeasurability.measurableSet_firstLiveSet.compl

theorem mem_collectionSet_iff (x : RoundInput p rate) :
    x ∈ collectionSet ↔ ∃ payload ledger proposal,
      x.state.coordinator = .collection payload ledger proposal := by
  classical
  rw [collectionSet, Set.mem_compl_iff, ReferenceFirstLiveCoordinatorStepMeasurability.mem_firstLiveSet_iff, not_not]

/-- The existing optional collection-coordinate projection is present here. -/
def collectionCoordinates (x : CollectionInput p rate) :
    ReferenceCollectionDispatchMeasurability.CollectionCoordinates p rate :=
  (ReferenceCollectionDispatchMeasurability.collectionCoordinates?
    (encodeCoordinator x.val.state.coordinator)).get
    (by
      obtain ⟨payload, ledger, proposal, hs⟩ := (mem_collectionSet_iff x.val).mp x.property
      simp only [hs, encodeCoordinator, ReferenceCollectionDispatchMeasurability.collectionCoordinates?, Option.isSome_some])

theorem collection_state (x : CollectionInput p rate) :
    x.val.state.coordinator = .collection (collectionCoordinates x).1
      (collectionCoordinates x).2.1 (collectionCoordinates x).2.2 := by
  obtain ⟨payload, ledger, proposal, hs⟩ := (mem_collectionSet_iff x.val).mp x.property
  simp only [collectionCoordinates, hs, encodeCoordinator,
    ReferenceCollectionDispatchMeasurability.collectionCoordinates?, Option.get_some]

theorem measurable_collectionCoordinates :
    Measurable (collectionCoordinates (p := p) (rate := rate)) := by
  intro s hs
  have heq : collectionCoordinates ⁻¹' s = (fun x : CollectionInput p rate =>
      ReferenceCollectionDispatchMeasurability.collectionCoordinates?
        (encodeCoordinator x.val.state.coordinator)) ⁻¹' (some '' s) := by
    ext x
    rw [Set.mem_preimage, Set.mem_preimage, collection_state x]
    simp only [collectionCoordinates, encodeCoordinator,
      ReferenceCollectionDispatchMeasurability.collectionCoordinates?,
      Set.mem_image, Option.some.injEq, exists_eq_right]
  rw [heq]
  have hs' : MeasurableSet (some '' s :
      Set (Option (ReferenceCollectionDispatchMeasurability.CollectionCoordinates p rate))) := by
    change MeasurableSet[(inferInstance : MeasurableSpace
      (ReferenceCollectionDispatchMeasurability.CollectionCoordinates p rate ⊕ PUnit)).comap
        (Equiv.optionEquivSumPUnit _)] (some '' s)
    rw [MeasurableSpace.measurableSet_comap]
    refine ⟨Sum.inl '' s, measurableSet_inl_image.mpr hs, ?_⟩
    ext value
    cases value <;> simp
  exact hs'.preimage
    (ReferenceCollectionDispatchMeasurability.measurable_collectionCoordinates?.comp
      ((measurable_coordinatorCode.comp measurable_state).comp measurable_subtype_coe))

theorem measurable_collectionSelection : Measurable (fun x : CollectionInput p rate =>
    (dispatch x.val).selection.map ReferenceLiveDispatchOutputMeasurability.encodeSelection) := by
  have heq (x : CollectionInput p rate) : ReferenceCollectionOutcomeMeasurability.canonicalCollectionSelectionCode x.val =
      (dispatch x.val).selection.map ReferenceLiveDispatchOutputMeasurability.encodeSelection :=
    ReferenceCollectionOutcomeMeasurability.canonicalCollectionSelectionCode_eq_dispatch x.val _ _ _ (collection_state x)
  simp_rw [← heq]
  exact ReferenceCollectionOutcomeMeasurability.measurable_canonicalCollectionSelectionCode.comp measurable_subtype_coe

theorem measurable_collectionDownView : Measurable (fun x : CollectionInput p rate =>
    (dispatch x.val).downView) := by
  simp_rw [← ReferenceCollectionOutcomeMeasurability.canonicalCollectionDownView_eq_dispatch _ _ _ _ (collection_state _)]
  exact ReferenceCollectionOutcomeMeasurability.measurable_canonicalCollectionDownView.comp measurable_subtype_coe

theorem measurable_collectionArm : Measurable (fun x : CollectionInput p rate =>
    (dispatch x.val).arm) := by
  have h := ReferenceCollectionOutcomeMeasurability.measurable_canonicalCollectionArm.comp
    (measurable_subtype_coe : Measurable (Subtype.val : CollectionInput p rate → _))
  have heq (x : CollectionInput p rate) : ReferenceCollectionOutcomeMeasurability.canonicalCollectionArm x.val =
      some (dispatch x.val).arm :=
    ReferenceCollectionOutcomeMeasurability.canonicalCollectionArm_eq_dispatch x.val _ _ _ (collection_state x)
  change Measurable (fun x : CollectionInput p rate =>
    ReferenceCollectionOutcomeMeasurability.canonicalCollectionArm x.val) at h
  simp_rw [heq] at h
  exact (measurable_of_countable (fun a : Option (Fin p.K) =>
    a.getD (coordinatorFallback p))).comp h

/-- Actions use original follower PREPARE, including its failures and dagger
play, together with the actual dispatched coordinator arm. -/
theorem measurable_collectionActions : Measurable (fun x : CollectionInput p rate =>
    (prepare x.val).arms.actions) := by
  apply measurable_pi_iff.mpr
  intro player
  rcases ActiveRoundActions.player_cases p.two_le_m player with h | ⟨i, h⟩
  · subst player
    convert measurable_collectionArm using 1
    funext x
    exact (prepare x.val).action_coordinator
  · subst player
    exact (measurable_followerArm i).comp measurable_subtype_coe

/-- Simultaneous collisions and quantized feedback use the same action
profile and the original entire grid reward table. -/
theorem measurable_collectionFeedback : Measurable (fun x : CollectionInput p rate =>
    (prepare x.val).feedback.feedback) := by
  have h := (measurable_gridFeedback (p := p)).comp
    (((measurable_rewards (p := p) (rate := rate)).comp measurable_subtype_coe).prodMk
      ((measurable_time.comp measurable_subtype_coe).prodMk measurable_collectionActions))
  convert h using 1
  funext x player
  exact (gridFeedback_eq_actual x.val player).symm

private theorem measurable_liftLiveCode :
    Measurable (ReferenceFirstLiveCoordinatorStepMeasurability.liftLiveCode (p := p) (rate := rate)) :=
  measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk
    ((measurable_fst.comp (measurable_snd.comp measurable_snd)).prodMk
      (((measurable_of_countable CoordinatorRecordingMeasurability.decodeResult).comp
        (measurable_snd.comp (measurable_snd.comp measurable_snd))).prodMk measurable_const)))

/-- The accepted choice-view space exposes the whole continuous weight vector. -/
theorem measurable_viewWeights : Measurable
    (ReferenceDownReceptionMeasurability.choiceTimeViewWeightVector
      (p := p) (rate := rate)) :=
  measurable_snd.comp (measurable_snd.comp (measurable_snd.comp
    (comap_measurable ReferenceDownReceptionMeasurability.choiceTimeViewObservation)))

theorem viewWeights_eq_extension (view : ReferenceDownReception.ChoiceTimeView p rate.eta) :
    ReferenceDownReceptionMeasurability.choiceTimeViewWeightVector view =
      ReferenceCollectionTailComposition.extendComplementWeights view.payload (fun _ => 0) view.complementWeights := by
  classical
  funext a
  unfold ReferenceDownReceptionMeasurability.choiceTimeViewWeightVector ReferenceCollectionTailComposition.extendComplementWeights
  by_cases ha : a ∈ view.payload.slowSet.val
  · have hn : a ∉ CanonicalFastSampling.fastArmFinset view.payload.slowSet :=
      fun hf => (Finset.mem_sdiff.mp hf).2 ha
    rw [dite_eq_right hn, dite_eq_left ha]
  · have hf : a ∈ CanonicalFastSampling.fastArmFinset view.payload.slowSet :=
      Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ha⟩
    rw [dite_eq_left hf, dite_eq_right ha]

/-- Continuing collection consumes the old payload/ledger and retained
selection view. Later choice consumes stored installation coordinates and the
original started result. All rejected dispatch branches preserve the bank. -/
def collectionObservationFormula (x : RoundInput p rate) (payload : Payload rate)
    (ledger : Ledger rate) (ownArm : Fin p.K) (feedback : Fin (D p + 1))
    (obs : ReferenceCollectionOutcomeMeasurability.FullObservation p rate) :
    ReferenceCollectionServiceTailMeasurability.CollectionTailCode p rate :=
  if obs.2.2.1 = .continuing then
    ReferenceCollectionOutcomeMeasurability.optionalElim
      (ReferenceFirstLiveCoordinatorStepMeasurability.rejectedCode x)
      (fun selected : ReferenceCollectionDispatchMeasurability.SelectionCoordinates p rate =>
      ReferenceCollectionTailComposition.collectionPostChoiceTailCode x payload ledger selected.2.1
        (ReferenceDownReceptionMeasurability.choiceTimeViewWeightVector selected.1)
        ownArm feedback) obs.2.2.2.1
  else if obs.2.2.1 = .laterChosen then
    ReferenceCollectionOutcomeMeasurability.optionalElim
      (ReferenceFirstLiveCoordinatorStepMeasurability.rejectedCode x)
      (fun c : ReferenceCollectionInstallOutputMeasurability.InstalledObservation p rate =>
      ReferenceFirstLiveCoordinatorStepMeasurability.liftLiveCode (ReferenceActiveLiveTailMeasurability.livePostChoiceWholeCode
        (c.1.1, c.1.2, c.2.2.1, x.state.upDecoderBank, x.time, x.row, ownArm, feedback))) obs.2.1
  else ReferenceFirstLiveCoordinatorStepMeasurability.rejectedCode x

/-- Every primitive assumption of this generic substitution lemma is explicit.
The canonical theorem below supplies them from the original round. -/
private theorem measurable_collectionObservationFormula_comp {X : Type*} [MeasurableSpace X]
    (input : X → RoundInput p rate) (payload : X → Payload rate) (ledger : X → Ledger rate)
    (arm : X → Fin p.K) (feedback : X → Fin (D p + 1))
    (obs : X → ReferenceCollectionOutcomeMeasurability.FullObservation p rate)
    (hx : Measurable input) (hp : Measurable payload) (hl : Measurable ledger)
    (ha : Measurable arm) (hf : Measurable feedback) (ho : Measurable obs) :
    Measurable (fun x => collectionObservationFormula (input x) (payload x) (ledger x)
      (arm x) (feedback x) (obs x)) := by
  classical
  have hreject : Measurable (fun x => ReferenceFirstLiveCoordinatorStepMeasurability.rejectedCode (input x)) :=
    measurable_const.prodMk ((measurable_upDecoderBank.comp (measurable_state.comp hx)).prodMk
      (measurable_const.prodMk (measurable_const.prodMk measurable_const)))
  have hcontinuing : Measurable (fun z : ReferenceCollectionDispatchMeasurability.SelectionCoordinates p rate × X =>
      ReferenceCollectionTailComposition.collectionPostChoiceTailCode (input z.2) (payload z.2) (ledger z.2) z.1.2.1
        (ReferenceDownReceptionMeasurability.choiceTimeViewWeightVector z.1.1)
        (arm z.2) (feedback z.2)) :=
    ReferenceCollectionTailComposition.measurable_collectionPostChoiceTailCode_comp _ _ _ _ _ _ _
      (hx.comp measurable_snd) (hp.comp measurable_snd) (hl.comp measurable_snd)
      (measurable_fst.comp (measurable_snd.comp measurable_fst))
      (measurable_viewWeights.comp (measurable_fst.comp measurable_fst))
      (ha.comp measurable_snd) (hf.comp measurable_snd)
  have hlater : Measurable (fun z : ReferenceCollectionInstallOutputMeasurability.InstalledObservation p rate × X =>
      ReferenceFirstLiveCoordinatorStepMeasurability.liftLiveCode (ReferenceActiveLiveTailMeasurability.livePostChoiceWholeCode
        (z.1.1.1, z.1.1.2, z.1.2.2.1, (input z.2).state.upDecoderBank,
          (input z.2).time, (input z.2).row, arm z.2, feedback z.2))) :=
    measurable_liftLiveCode.comp
      (ReferenceActiveLiveTailMeasurability.measurable_livePostChoiceWholeCode_comp _ _ _ _ _ _ _ _
        (measurable_fst.comp (measurable_fst.comp measurable_fst))
        (measurable_snd.comp (measurable_fst.comp measurable_fst))
        (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_fst)))
        (measurable_upDecoderBank.comp (measurable_state.comp (hx.comp measurable_snd)))
        (measurable_time.comp (hx.comp measurable_snd))
        (measurable_row.comp (hx.comp measurable_snd))
        (ha.comp measurable_snd) (hf.comp measurable_snd))
  have hoptional {A : Type} [MeasurableSpace A]
      (f : A × X → ReferenceCollectionServiceTailMeasurability.CollectionTailCode p rate) (h : Measurable f)
      (a : X → Option A) (hm : Measurable a) :
      Measurable (fun x => ReferenceCollectionOutcomeMeasurability.optionalElim
        (ReferenceFirstLiveCoordinatorStepMeasurability.rejectedCode (input x))
        (fun v => f (v, x)) (a x)) := by
    have hmap := ReferenceCollectionInstallOutputMeasurability.measurable_optionMapDependent
      (fun q : A × X => f q) h a hm
    have helim : Measurable (fun z : Option (ReferenceCollectionServiceTailMeasurability.CollectionTailCode p rate) ×
        CoordinatorUpReception.UpDecoderBank p => z.1.getD
          (ReferenceCollectionServiceTailMeasurability.encodeCollectionObservation
            (coordinatorFailure z.2 .dispatchRejected none none))) := by
      apply measurable_from_prod_countable_left
      intro b
      convert ReferenceCollectionOutcomeMeasurability.measurable_optionalElim
        (ReferenceCollectionServiceTailMeasurability.encodeCollectionObservation
          (coordinatorFailure b .dispatchRejected none none)) id measurable_id using 1
      funext a
      cases a <;> rfl
    convert helim.comp (hmap.prodMk
      (measurable_upDecoderBank.comp (measurable_state.comp hx))) using 1
    funext x
    change ReferenceCollectionOutcomeMeasurability.optionalElim _ _ (a x) =
      ((a x).map (fun v => f (v, x))).getD _
    cases a x <;> rfl
  exact Measurable.ite
    (measurableSet_eq_fun
      ((measurable_fst.comp (measurable_snd.comp measurable_snd)).comp ho) measurable_const)
    (hoptional _ hcontinuing _
      ((measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))).comp ho))
    (Measurable.ite
      (measurableSet_eq_fun
        ((measurable_fst.comp (measurable_snd.comp measurable_snd)).comp ho) measurable_const)
      (hoptional _ hlater _ ((measurable_fst.comp measurable_snd).comp ho)) hreject)

open ReferenceCollectionDispatchMeasurability
open ReferenceCollectionInstallOutputMeasurability
open ReferenceCollectionOutcomeMeasurability

/-- Data projection from the existing outcome; no second installation is run. -/
def outcomeInstallationCoordinates {p : ConstructorDimensions.Parameters}
    {rate : ReferenceActivePhysicalStep.RateInput p} (z : LocalInput p rate) :
    CoordinatorRoundDispatch.CollectionOutcome (assemble z) →
      Option (InstallationCoordinates p rate × CoordinatorPhaseClock.StartRoundResult p)
  | .laterChosen _ _ started _ _ _ _ _ _ installed _ =>
      some ((installed.registers.payload,
        encodeLive (rate := rate) installed.registers installed.ownedRegisters installed.retainedBaseScore), started)
  | _ => none

/-- Actual later choices expose the retained numerical installation and clock.
The premise selects a data projection of the original dispatch; it supplies no
successful operation or installation to the unrestricted step theorem. -/
theorem collection_installed_observation {p : ConstructorDimensions.Parameters}
    {rate : ReferenceActivePhysicalStep.RateInput p} (z : LocalInput p rate)
    (installed : InstallationCoordinates p rate × CoordinatorPhaseClock.StartRoundResult p)
    (hchosen : outcomeInstallationCoordinates z
      (CoordinatorRoundDispatch.dispatchCollection (assemble z)) = some installed) :
    ∃ c : InstalledObservation p rate,
      laterInstalledObservation? z = some c ∧ (c.1, c.2.2.1) = installed := by
  classical
  generalize hout : CoordinatorRoundDispatch.dispatchCollection (assemble z) = outcome at hchosen
  unfold CoordinatorRoundDispatch.dispatchCollection at hout
  split at hout
  next failure hstart => cases hout; cases hchosen
  next started hstart =>
    split at hout
    next hcore =>
      dsimp only at hout
      split at hout
      next hpending =>
        split at hout
        next hscores =>
          split at hout
          next hchoice =>
            split at hout
            next hnone =>
              have he := Except.ok.inj (hstart.symm.trans
                (carriedStart_eq_actual ⟨⟨z, hcore⟩, hpending⟩))
              have hc : CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u =
                  some (CoordinatorCollectionUpRoundStep.localCutoff (assemble z).cutoffIndex) := by
                rw [he]
                change CoordinatorLiveChoiceRecorderStep.cutoffFromClock p (assemble z).clock.u = _
                rw [hcore.clock_cutoff_eq]
                rfl
              have hv : CoordinatorLocalArmChoice.ChoiceInputsValid (assemble z).payload
                  (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
                  (assemble z).time (CoordinatorCollectionInteractive.PreObservationInputs.weights
                    (assemble z) hcore.ledger_valid hcore.assignment_eq) := by
                rw [hc]
                exact hchoice
              exact False.elim ((CoordinatorLiveChoiceRecorderStep.coordinatorArmChoice_ne_none
                _ _ _ _ _ _ hv) hnone)
            next arm ha => cases hout; cases hchosen
          next hchoice => cases hout; cases hchosen
        next hscores => cases hout; cases hchosen
      next hpending =>
        split at hout
        next hi => cases hout; cases hchosen
        next instruction hi =>
          split at hout
          next reason hr => cases hout; cases hchosen
          next arm reason hr => cases hout; cases hchosen
          next set hr => cases hout; cases hchosen
          next output hlocal hr =>
            let core : CoreInput p rate := ⟨z, hcore⟩
            change @LaterAssignmentStartOperation.SuccessfulStart p rate.eta z.1.1
              (operationLedger core) instruction z.1.2 at output
            change LaterAssignmentStartOperation.laterAssignmentStart z.1.1
              (operationLedger core) instruction z.1.2 (localConsistency core) = _ at hr
            have hobs := laterInstalledObservation?_of_actual_success core started hstart
              hpending instruction hi output hlocal hr
            split at hout
            next hbase =>
              split at hout
              next hchoice =>
                split at hout
                next henvelope =>
                  split at hout
                  next hnone =>
                    exact False.elim
                      ((CoordinatorLiveChoiceRecorderStep.coordinatorArmChoice_ne_none
                        _ _ _ _ _ _ hchoice) hnone)
                  next arm ha =>
                    cases hout
                    have heq := Option.some.inj hchosen
                    refine ⟨_, hobs, ?_⟩
                    apply Eq.trans _ heq
                    exact Prod.ext (installationCoordinates_eq_actual core instruction output
                      (restoreClockData core started hstart instruction hi output hlocal)) rfl
                next henvelope => cases hout; cases hchosen
              next hchoice => cases hout; cases hchosen
            next hbase => cases hout; cases hchosen
    next hcore => cases hout; cases hchosen

/-- Same-input coordinator observation on a valid outer cutoff. All internal
failures remain in the full observation. The only premise identifies the
literal collection dispatch of this very preparation. -/
theorem collection_observation_eq {p : ConstructorDimensions.Parameters}
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (x : RoundInput p rate) (payload : Payload rate) (ledger : Ledger rate)
    (proposal : Option (Fin p.T × Bool)) (cutoff : Fin p.T)
    (hdispatch : (prepare x).coordinator = .collection payload ledger
      (collectionClock payload ledger proposal cutoff) cutoff
      (CoordinatorRoundDispatch.dispatchCollection (assemble
        ((payload, x.row), ledger, proposal, x.state.upDecoderBank, x.time, cutoff)))) :
    ReferenceCollectionServiceTailMeasurability.encodeCollectionObservation
        (prepare x).observeCoordinator =
      collectionObservationFormula x payload ledger (prepare x).coordinator.arm
        (prepare x).coordinatorObservation (collectionFullObservation
          ((payload, x.row), ledger, proposal, x.state.upDecoderBank, x.time, cutoff)) := by
  classical
  let z : LocalInput p rate :=
    ((payload, x.row), ledger, proposal, x.state.upDecoderBank, x.time, cutoff)
  have htag := collectionTag_eq_actual z
  have hselection := collectionSelectionCode_eq_actual z
  have hinstalled := collection_installed_observation z
  dsimp only [z] at htag hselection hinstalled
  rw [observeCoordinator_collection_equation (prepare x) payload ledger
    (collectionClock payload ledger proposal cutoff) cutoff _ hdispatch]
  generalize hout : CoordinatorRoundDispatch.dispatchCollection
    (assemble ((payload, x.row), ledger, proposal, x.state.upDecoderBank, x.time, cutoff)) = outcome
    at htag hselection hinstalled ⊢
  cases outcome with
  | continuing core snapshot boundary hscores =>
      simp only [DispatchCut.selection, Option.some_ne_none, ite_false,
        collectionObservationFormula, collectionFullObservation, htag, outcomeTag,
        ite_true, hselection, outcomeSelectionCode, optionalElim]
      rw [viewWeights_eq_extension]
      exact (ReferenceCollectionTailComposition.collectionPostChoiceTailCode_eq_existing
        (prepare x) payload ledger snapshot.clockStarted (fun _ => 0)
        (CoordinatorCollectionInteractive.PreObservationInputs.weights
          (assemble z) snapshot.inputsValid.ledger_valid snapshot.inputsValid.assignment_eq)).symm
  | laterChosen core consistent started hstart instruction hi output hlocal clockData installed selected =>
      have ht := later_instruction_time x payload ledger
        (collectionClock payload ledger proposal cutoff) cutoff core started instruction hstart hi
      obtain ⟨c, hc, hcoords⟩ := hinstalled
        ((installed.registers.payload,
          encodeLive (rate := rate) installed.registers installed.ownedRegisters installed.retainedBaseScore),
          started) rfl
      simp only [DispatchCut.selection, selectionAt, dite_eq_left ht, Option.some_ne_none,
        ite_false, collectionObservationFormula, collectionFullObservation, htag, outcomeTag,
        reduceCtorEq, ite_true, hc, optionalElim]
      have hs : c.2.2.1 = started := congrArg Prod.snd hcoords
      rw [congrArg Prod.fst hcoords, hs]
      exact (ReferenceFirstLiveCoordinatorStepMeasurability.liftLiveCode_eq_actual
        (prepare x) installed.registers installed.ownedRegisters installed.retainedBaseScore started).symm
  | clockFailure reason hstart =>
      simp only [DispatchCut.selection, ite_true, collectionObservationFormula,
        collectionFullObservation, htag, outcomeTag, reduceCtorEq, ite_false,
        ReferenceFirstLiveCoordinatorStepMeasurability.rejectedCode]
  | localFailure started hstart hcore reason =>
      simp only [DispatchCut.selection, ite_true, collectionObservationFormula,
        collectionFullObservation, htag, outcomeTag, reduceCtorEq, ite_false,
        ReferenceFirstLiveCoordinatorStepMeasurability.rejectedCode]
  | coreFailure core started hstart reason =>
      simp only [DispatchCut.selection, ite_true, collectionObservationFormula,
        collectionFullObservation, htag, outcomeTag, reduceCtorEq, ite_false,
        ReferenceFirstLiveCoordinatorStepMeasurability.rejectedCode]
  | laterReconstructionFailure core consistent started hstart instruction hi reason hr =>
      simp only [DispatchCut.selection, ite_true, collectionObservationFormula,
        collectionFullObservation, htag, outcomeTag, reduceCtorEq, ite_false,
        ReferenceFirstLiveCoordinatorStepMeasurability.rejectedCode]
  | laterPrefixFailure core consistent started hstart instruction hi arm reason hr =>
      simp only [DispatchCut.selection, ite_true, collectionObservationFormula,
        collectionFullObservation, htag, outcomeTag, reduceCtorEq, ite_false,
        ReferenceFirstLiveCoordinatorStepMeasurability.rejectedCode]
  | laterOrientationFailure core consistent started hstart instruction hi set hr =>
      simp only [DispatchCut.selection, ite_true, collectionObservationFormula,
        collectionFullObservation, htag, outcomeTag, reduceCtorEq, ite_false,
        ReferenceFirstLiveCoordinatorStepMeasurability.rejectedCode]
  | laterChoiceFailure core consistent started hstart instruction hi output hlocal clockData installed reason =>
      simp only [DispatchCut.selection, ite_true, collectionObservationFormula,
        collectionFullObservation, htag, outcomeTag, reduceCtorEq, ite_false,
        ReferenceFirstLiveCoordinatorStepMeasurability.rejectedCode]

/-- Ordinary sum elimination with both independently measurable branches. -/
private theorem measurable_sumElim_comp {X A B Y : Type*}
    [MeasurableSpace X] [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace Y]
    (f : A × X → Y) (g : B × X → Y) (hf : Measurable f) (hg : Measurable g)
    (a : X → A ⊕ B) (ha : Measurable a) :
    Measurable (fun x => Sum.elim (fun v => f (v, x)) (fun v => g (v, x)) (a x)) := by
  have h := (hf.sumElim hg).comp (MeasurableEquiv.sumProdDistrib A B X).measurable_toFun
  convert h.comp (ha.prodMk measurable_id) using 1
  funext x
  change Sum.elim _ _ (a x) = Sum.elim f g ((Equiv.sumProdDistrib A B X) (a x, x))
  cases a x <;> rfl

/-- Optional elimination keeps the absent branch explicit and measurable. -/
private theorem measurable_optionalElim_comp {X A Y : Type*}
    [MeasurableSpace X] [MeasurableSpace A] [MeasurableSpace Y]
    (fallback : X → Y) (f : A × X → Y) (hb : Measurable fallback) (hf : Measurable f)
    (a : X → Option A) (ha : Measurable a) :
    Measurable (fun x => optionalElim (fallback x) (fun v => f (v, x)) (a x)) := by
  have h := measurable_sumElim_comp f (fun z : PUnit × X => fallback z.2)
    hf (hb.comp measurable_snd) (fun x => (Equiv.optionEquivSumPUnit A) (a x))
    ((comap_measurable (Equiv.optionEquivSumPUnit A)).comp ha)
  convert h using 1
  funext x
  cases a x <;> rfl

variable {p : ConstructorDimensions.Parameters} {rate : ReferenceActivePhysicalStep.RateInput p}

/-- The actual post-choice code assembled from the canonical full collection
observation. Outer invalid cutoff, absence and every failed dispatch use the
original bank-preserving rejection; only the two chosen tags run a tail. -/
def collectionObservationCode (x : CollectionInput p rate) :
    ReferenceCollectionServiceTailMeasurability.CollectionTailCode p rate :=
  optionalElim (ReferenceFirstLiveCoordinatorStepMeasurability.rejectedCode x.val)
    (Sum.elim (fun _ : Unit => ReferenceFirstLiveCoordinatorStepMeasurability.rejectedCode x.val)
      (collectionObservationFormula x.val (collectionCoordinates x).1
        (collectionCoordinates x).2.1 (prepare x.val).coordinator.arm
        (prepare x.val).coordinatorObservation))
    (canonicalCollectionFullObservation x.val)

private theorem measurable_collectionRejected : Measurable
    (fun x : CollectionInput p rate => ReferenceFirstLiveCoordinatorStepMeasurability.rejectedCode x.val) :=
  measurable_const.prodMk
    (((measurable_upDecoderBank.comp measurable_state).comp measurable_subtype_coe).prodMk
      (measurable_const.prodMk (measurable_const.prodMk measurable_const)))

/-- The observation formula uses retained continuous components, never the
certificate tests in the full-outcome decoder. -/
theorem measurable_collectionObservationCode :
    Measurable (collectionObservationCode (p := p) (rate := rate)) := by
  have hformula : Measurable (fun z : FullObservation p rate × CollectionInput p rate =>
      collectionObservationFormula z.2.val (collectionCoordinates z.2).1
        (collectionCoordinates z.2).2.1 (prepare z.2.val).coordinator.arm
        (prepare z.2.val).coordinatorObservation z.1) :=
    measurable_collectionObservationFormula_comp _ _ _ _ _ _
      (measurable_subtype_coe.comp measurable_snd)
      ((measurable_fst.comp measurable_collectionCoordinates).comp measurable_snd)
      ((measurable_fst.comp (measurable_snd.comp measurable_collectionCoordinates)).comp measurable_snd)
      (measurable_collectionArm.comp measurable_snd)
      (((measurable_pi_apply (ActiveRoundActions.coordinator p.two_le_m)).comp
        measurable_collectionFeedback).comp measurable_snd) measurable_fst
  have hsum : Measurable (fun z : (Unit ⊕ FullObservation p rate) × CollectionInput p rate =>
      Sum.elim (fun _ : Unit => ReferenceFirstLiveCoordinatorStepMeasurability.rejectedCode z.2.val)
        (fun o => collectionObservationFormula z.2.val (collectionCoordinates z.2).1
          (collectionCoordinates z.2).2.1 (prepare z.2.val).coordinator.arm
          (prepare z.2.val).coordinatorObservation o) z.1) :=
    measurable_sumElim_comp _ _ (measurable_collectionRejected.comp
      (measurable_snd.comp measurable_snd))
      (hformula.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))
      Prod.fst measurable_fst
  exact measurable_optionalElim_comp _ _ measurable_collectionRejected hsum _
    (measurable_canonicalCollectionFullObservation.comp measurable_subtype_coe)

/-- Exact whole coordinator observation, including outer cutoff rejection and
all post-choice recording, service, UP filtering and finish failures. -/
theorem collectionObservationCode_eq_actual (x : CollectionInput p rate) :
    collectionObservationCode x =
      ReferenceCollectionServiceTailMeasurability.encodeCollectionObservation
        (prepare x.val).observeCoordinator := by
  classical
  let c := collectionCoordinates x
  have hs := collection_state x
  unfold collectionObservationCode
  rw [canonicalCollectionFullObservation_collection x.val c.1 c.2.1 c.2.2 hs]
  simp only [optionalElim]
  let b : BoundaryInput p rate := ((c.1, x.val.row), c.2.1, c.2.2,
    x.val.state.upDecoderBank, x.val.time)
  by_cases hc : cutoffValid b
  · change Sum.elim _ _ (boundaryFullObservation b) = _
    rw [boundaryFullObservation, dite_eq_left hc]
    dsimp only [Sum.elim_inr]
    have hd := dispatch_collection x.val c.1 c.2.1 c.2.2 hs hc
    exact (collection_observation_eq x.val c.1 c.2.1 c.2.2
      (boundaryLocal ⟨b, hc⟩).2.2.2.2.2 hd).symm
  · have hd := (dispatch_collection_invalid x.val c.1 c.2.1 c.2.2 hs hc).1
    change Sum.elim _ _ (boundaryFullObservation b) = _
    rw [boundaryFullObservation, dite_eq_right hc]
    change ReferenceFirstLiveCoordinatorStepMeasurability.rejectedCode x.val = _
    simp only [PreparedRound.observeCoordinator, show (prepare x.val).coordinator =
      .invalidCollectionCutoff from hd, DispatchCut.selection, dite_true,
      ReferenceFirstLiveCoordinatorStepMeasurability.rejectedCode]

/-- The existing physical tuple is jointly Borel on ALL incoming collection
states; the subtype is only the canonical incoming tag. -/
theorem measurable_collectionPhysicalCode : Measurable (fun x : CollectionInput p rate =>
    ReferenceFirstLiveCoordinatorStepMeasurability.physicalCode x.val) := by
  have ho : Measurable (fun x : CollectionInput p rate =>
      ReferenceCollectionServiceTailMeasurability.encodeCollectionObservation
        (prepare x.val).observeCoordinator) := by
    simp_rw [← collectionObservationCode_eq_actual]
    exact measurable_collectionObservationCode
  exact measurable_collectionSelection.prodMk (measurable_collectionDownView.prodMk
    (measurable_collectionActions.prodMk (measurable_collectionFeedback.prodMk ho)))

/-- Full incoming-tag gluing of the SAME physical tuple. No validity,
reachability, successful-choice or measurable-producer premise is added. -/
theorem measurable_physicalCode : Measurable
    (ReferenceFirstLiveCoordinatorStepMeasurability.physicalCode (p := p) (rate := rate)) :=
  measurable_of_restrict_of_restrict_compl
    ReferenceFirstLiveCoordinatorStepMeasurability.measurableSet_firstLiveSet
    ReferenceFirstLiveCoordinatorStepMeasurability.measurable_physicalCode
    measurable_collectionPhysicalCode

/-- Actual DOWN projection produced by the full physical tuple. -/
theorem measurable_downView : Measurable (fun x : RoundInput p rate => (dispatch x).downView) :=
  measurable_fst.comp (measurable_snd.comp measurable_physicalCode)

/-- Each player's actual feedback includes simultaneous collisions. -/
theorem measurable_playerFeedback (player : Fin p.m) : Measurable
    (fun x : RoundInput p rate => (prepare x).feedback.feedback player) :=
  (measurable_pi_apply player).comp
    (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp
      (measurable_snd.comp measurable_physicalCode))))

/-- Decode every field of the original whole coordinator observation. -/
theorem physicalCode_observation_reconstructs (x : RoundInput p rate) :
    ReferenceCollectionServiceTailMeasurability.decodeCollectionObservation
      (ReferenceFirstLiveCoordinatorStepMeasurability.physicalCode x).2.2.2.2 =
        (prepare x).observeCoordinator :=
  ReferenceCollectionServiceTailMeasurability.decodeCollectionObservation_encodeCollectionObservation _

/-- The measured coordinator/bank coordinates are the literal successor fields. -/
theorem measurable_coordinatorBankSuccessor : Measurable (fun x : RoundInput p rate =>
    ((successorCode x).1, (successorCode x).2.1)) := by
  simp_rw [← ReferenceFirstLiveCoordinatorStepMeasurability.coordinatorBank_eq_successor]
  have h : Measurable (fun x : RoundInput p rate =>
      (ReferenceFirstLiveCoordinatorStepMeasurability.physicalCode x).2.2.2.2) :=
    measurable_snd.comp (measurable_snd.comp (measurable_snd.comp
      (measurable_snd.comp measurable_physicalCode)))
  exact (measurable_fst.comp h).prodMk (measurable_fst.comp (measurable_snd.comp h))

/-- The existing whole follower observable from this same canonical
preparation, including its configuration, failure, logged DOWN input, and
complete DOWN cut. -/
def followerObservable (x : RoundInput p rate) (i : Fin (p.m - 1)) :=
  ReferenceFollowerTailComposition.observeFollowerObservable
    (ReferenceActivePhysicalStep.prepare x) i

/-- PREPARE retains exactly the dispatcher DOWN view used by the existing
whole-observation physical code. -/
theorem preparedDownView_eq_dispatch
    (x : ReferenceActivePhysicalStep.RoundInput p rate) :
    (ReferenceActivePhysicalStep.prepare x).coordinator.downView =
      (ReferenceActivePhysicalStep.dispatch x).downView := rfl

private theorem measurable_preparedDownView : Measurable
    (fun x : RoundInput p rate =>
      (ReferenceActivePhysicalStep.prepare x).coordinator.downView) := by
  have heq : (fun x : RoundInput p rate =>
      (ReferenceActivePhysicalStep.prepare x).coordinator.downView) =
      fun x => (ReferenceActivePhysicalStep.dispatch x).downView := by
    funext x
    exact preparedDownView_eq_dispatch x
  rw [heq]
  exact measurable_downView

/-- The actual follower observation is measurable on the original
unrestricted active-round domain, with both whole-step producers discharged. -/
theorem measurable_followerObservable (i : Fin (p.m - 1)) :
    Measurable (fun x : RoundInput p rate => followerObservable x i) := by
  exact ReferenceFollowerVaryingFinishMeasurability.measurable_observeFollowerObservable_comp
    (p := p) (rate := rate)
    (input := id) measurable_id i measurable_preparedDownView
    (measurable_playerFeedback
      (PublicDiscreteDraws.followerPlayer p.two_le_m i))

/-- The existing observable decoder reconstructs the follower result of this
very preparation; no second follower run is introduced. -/
theorem followerObservable_reconstruct (x : RoundInput p rate)
    (i : Fin (p.m - 1)) :
    ReferenceFollowerTailComposition.reconstructFollowerObservable
        (followerObservable x i) =
      (ReferenceActivePhysicalStep.prepare x).observeFollower i := by
  exact ReferenceFollowerTailComposition.observeFollowerObservable_reconstruct
    (ReferenceActivePhysicalStep.prepare x) i

/-- Assemble all actual successor follower configuration codes by finite pi. -/
theorem measurable_successorFollowerCodes :
    Measurable (fun x : RoundInput p rate =>
      fun i => ReferenceFollowerVaryingFinishMeasurability.successorFollowerConfigurationCode
        x i) := by
  apply measurable_pi_iff.mpr
  intro i
  exact ReferenceFollowerVaryingFinishMeasurability.measurable_successorFollowerConfigurationCode_comp
    (p := p) (rate := rate)
    (input := id) measurable_id i measurable_preparedDownView
    (measurable_playerFeedback
      (PublicDiscreteDraws.followerPlayer p.two_le_m i))

private theorem measurable_successorActivations : Measurable
    (fun x : RoundInput p rate =>
      (ReferenceActivePhysicalStepMeasurability.successorCode x).2.2.1) := by
  have hsource : Measurable (fun x : RoundInput p rate => x.state.activations) :=
    (ReferenceActivePhysicalStepMeasurability.measurable_activations.comp
      ReferenceActivePhysicalStepMeasurability.measurable_state)
  have heq : (fun x : RoundInput p rate =>
      (ReferenceActivePhysicalStepMeasurability.successorCode x).2.2.1) =
      fun x => x.state.activations := by
    funext x
    change (ReferenceActivePhysicalStep.step x).next.activations = x.state.activations
    exact (ReferenceActivePhysicalStep.step_next_fields x).2.2.1
  rw [heq]
  exact hsource

/-- The exact original `successorCode` is measurable. Its follower coordinates
come from the whole observable, its coordinator/bank from the physical code,
and its activations are the unchanged actual state fields. -/
theorem measurable_successorCode :
    Measurable (fun x : RoundInput p rate =>
      ReferenceActivePhysicalStepMeasurability.successorCode x) := by
  have hcoordinatorBank :=
    measurable_coordinatorBankSuccessor
      (p := p) (rate := rate)
  have hcoordinatorProjection : Measurable
      (fun z : ReferenceActivePhysicalStepMeasurability.CoordinatorCode p rate ×
        CoordinatorUpReception.UpDecoderBank p => z.1) := measurable_fst
  have hbankProjection : Measurable
      (fun z : ReferenceActivePhysicalStepMeasurability.CoordinatorCode p rate ×
        CoordinatorUpReception.UpDecoderBank p => z.2) := measurable_snd
  have hcoordinator : Measurable (fun x : RoundInput p rate =>
      (ReferenceActivePhysicalStepMeasurability.successorCode x).1) :=
    hcoordinatorProjection.comp hcoordinatorBank
  have hbank : Measurable (fun x : RoundInput p rate =>
      (ReferenceActivePhysicalStepMeasurability.successorCode x).2.1) :=
    hbankProjection.comp hcoordinatorBank
  have hfollower : Measurable (fun x : RoundInput p rate =>
      (ReferenceActivePhysicalStepMeasurability.successorCode x).2.2.2) := by
    have heq : (fun x : RoundInput p rate =>
        (ReferenceActivePhysicalStepMeasurability.successorCode x).2.2.2) =
        fun x i => ReferenceFollowerVaryingFinishMeasurability.successorFollowerConfigurationCode
          (p := p) (rate := rate) x i := by
      funext x i
      rfl
    rw [heq]
    exact measurable_successorFollowerCodes
  exact hcoordinator.prodMk (hbank.prodMk
    (measurable_successorActivations.prodMk hfollower))

/-- The literal next state is measurable in its existing STORE space, whose
measurable structure is the comap along the proved lossless `encodeState`. -/
theorem measurable_stepNext :
    Measurable (fun x : RoundInput p rate =>
      (ReferenceActivePhysicalStep.step x).next) := by
  apply measurable_comap_iff.mpr
  convert measurable_successorCode using 1
  funext x
  rfl

/-- The actual original own-entry code is measurable from the action and
feedback profiles already present in the physical code. -/
theorem measurable_ownEntryCode (player : Fin p.m) :
    Measurable (fun x : RoundInput p rate =>
      ReferenceActivePhysicalStepMeasurability.ownEntryCode x player) := by
  have hactions : Measurable (fun x : RoundInput p rate =>
      (ReferenceActivePhysicalStep.prepare x).arms.actions) := by
    convert measurable_fst.comp (measurable_snd.comp
      (measurable_snd.comp
        measurable_physicalCode)) using 1
    funext x
    rfl
  exact ((measurable_pi_apply player).comp hactions).prodMk
    (measurable_playerFeedback player)

/-- The deterministic grid conversion is measurable, so the original step's
own entry in its existing typed observation space is measurable as well. -/
theorem measurable_stepOwnEntry (player : Fin p.m) :
    Measurable (fun x : RoundInput p rate =>
      (ReferenceActivePhysicalStep.step x).ownEntries player) := by
  have hcode := measurable_ownEntryCode (p := p) (rate := rate) player
  have hgrid : Measurable (fun x : RoundInput p rate =>
      (ReferenceActivePhysicalStepMeasurability.ownEntryCode x player).2) :=
    measurable_snd.comp hcode
  have hobservation : Measurable (fun x : RoundInput p rate =>
      ActualInitializationPhysicalStep.observationOfGrid p
        (ReferenceActivePhysicalStepMeasurability.ownEntryCode x player).2) :=
    (measurable_of_countable (fun y : Fin (D p + 1) =>
      ActualInitializationPhysicalStep.observationOfGrid p y)).comp hgrid
  have hpair : Measurable (fun x : RoundInput p rate =>
      ((ReferenceActivePhysicalStepMeasurability.ownEntryCode x player).1,
        ActualInitializationPhysicalStep.observationOfGrid p
          (ReferenceActivePhysicalStepMeasurability.ownEntryCode x player).2)) :=
    (measurable_fst.comp hcode).prodMk hobservation
  have heq : (fun x : RoundInput p rate =>
      (ReferenceActivePhysicalStep.step x).ownEntries player) = fun x =>
        ((ReferenceActivePhysicalStepMeasurability.ownEntryCode x player).1,
          ActualInitializationPhysicalStep.observationOfGrid p
            (ReferenceActivePhysicalStepMeasurability.ownEntryCode x player).2) := by
    funext x
    exact (ReferenceActivePhysicalStepMeasurability.ownEntryCode_reconstruct
      x player).symm
  rw [heq]
  exact hpair

/-- The complete profile of entries appended to the players' own histories. -/
theorem measurable_stepOwnEntries : Measurable
    (fun x : RoundInput p rate => (step x).ownEntries) :=
  measurable_pi_iff.mpr measurable_stepOwnEntry

/-- Actual arm projection of a player's own history entry. -/
theorem measurable_stepOwnArm (player : Fin p.m) : Measurable
    (fun x : RoundInput p rate => ((step x).ownEntries player).1) :=
  measurable_fst.comp (measurable_stepOwnEntry player)

/-- Actual reward-observation projection of a player's own history entry. -/
theorem measurable_stepOwnObservation (player : Fin p.m) : Measurable
    (fun x : RoundInput p rate => ((step x).ownEntries player).2) :=
  measurable_snd.comp (measurable_stepOwnEntry player)

/-- Exact action and collision-sensitive feedback reconstruction for the
same original STEP entry. -/
theorem ownEntryCode_reconstruct (x : RoundInput p rate)
    (player : Fin p.m) :
    ((ReferenceActivePhysicalStepMeasurability.ownEntryCode x player).1,
      ActualInitializationPhysicalStep.observationOfGrid p
        (ReferenceActivePhysicalStepMeasurability.ownEntryCode x player).2) =
      (ReferenceActivePhysicalStep.step x).ownEntries player :=
  ReferenceActivePhysicalStepMeasurability.ownEntryCode_reconstruct x player

/-- The joint code retains the admitted physical code, every whole follower
observable, and the exact canonical successor code from the same input. -/
def wholeStepCode (x : RoundInput p rate) :=
  (ReferenceFirstLiveCoordinatorStepMeasurability.physicalCode x,
    (fun i => followerObservable x i,
      ReferenceActivePhysicalStepMeasurability.successorCode x))

/-- The complete actual physical-to-successor composition
is measurable. -/
theorem measurable_wholeStepCode : Measurable (wholeStepCode (p := p) (rate := rate)) := by
  have hfollowers : Measurable (fun x : RoundInput p rate =>
      fun i => followerObservable x i) := by
    apply measurable_pi_iff.mpr
    intro i
    exact measurable_followerObservable i
  exact measurable_physicalCode.prodMk
    (hfollowers.prodMk measurable_successorCode)

/-- Every component of the joint code reconstructs the original prepared
coordinator observation, all original follower observations, and literal
successor from this same preparation and step. -/
theorem wholeStepCode_reconstructs (x : RoundInput p rate) :
    ReferenceCollectionServiceTailMeasurability.decodeCollectionObservation
        (wholeStepCode x).1.2.2.2.2 =
        (ReferenceActivePhysicalStep.prepare x).observeCoordinator ∧
      (∀ i, ReferenceFollowerTailComposition.reconstructFollowerObservable
        ((wholeStepCode x).2.1 i) =
          (ReferenceActivePhysicalStep.prepare x).observeFollower i) ∧
      ReferenceActivePhysicalStepMeasurability.decodeState
        ((wholeStepCode x).2.2) = (ReferenceActivePhysicalStep.step x).next := by
  constructor
  · exact physicalCode_observation_reconstructs x
  constructor
  · intro i
    exact followerObservable_reconstruct x i
  · exact ReferenceActivePhysicalStepMeasurability.successorCode_reconstruct x

/-- Every physical-front coordinate comes from the same original preparation. -/
theorem wholeStepCode_front (x : RoundInput p rate) :
    (wholeStepCode x).1.1 =
        (dispatch x).selection.map ReferenceLiveDispatchOutputMeasurability.encodeSelection ∧
      (wholeStepCode x).1.2.1 = (dispatch x).downView ∧
      (wholeStepCode x).1.2.2.1 = (prepare x).arms.actions ∧
      (wholeStepCode x).1.2.2.2.1 = (prepare x).feedback.feedback :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Own entries are reconstructed directly from the retained physical front. -/
theorem wholeStepCode_ownEntry (x : RoundInput p rate) (player : Fin p.m) :
    ((wholeStepCode x).1.2.2.1 player,
      ActualInitializationPhysicalStep.observationOfGrid p
        ((wholeStepCode x).1.2.2.2.1 player)) = (step x).ownEntries player :=
  ownEntryCode_reconstruct x player

/-- On the existing incoming FIRST/LIVE/dagger fiber this is literally its
accepted whole-step code, including transitions that enter collection. -/
theorem wholeStepCode_firstLive (x : ReferenceFirstLiveStepMeasurability.FirstLiveInput p rate) :
    wholeStepCode x.val = ReferenceFirstLiveStepMeasurability.wholeStepCode x := rfl

end Bandits.Support.ReferenceActiveStepCompositionMeasurability

end
