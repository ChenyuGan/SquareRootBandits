/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCompleteInstallationCollectionPrefixNumericalTruth

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.Tactic

/-!
# Original arbitrary-date collection recorder and retained queue observers

The original optional collection recorder and inherited numerical prefix are retained at every date.
Sources: ZIP4 `04_slow_fast_learner.tex:157-188,245-288`,
`06_interruptions.tex:192-233,246-299,355-426`, and
`appendix_a_local_protocol.tex:28-64`, under `sources/zip4/manuscript/`.
-/

public section

noncomputable section

open MeasureTheory
open scoped Classical BigOperators

namespace Bandits.Support.ReferenceOriginalCalendarCollectionRetainedEnergyStep
open ConstructorDimensions (Parameters)
open ReferenceActivePhysicalStep (RateInput)
open ActualInitializationPhysicalStep (GridRewardTable)
open BootstrapPrivateRoundStreams (SourceInput sourceInputLaw)
open ContinuousLearningRows (TimeControl)
open ReferenceSourcePrefixHistoryFiltration (actualRecord sourcePrefixFiltration)
variable {p : Parameters}
  (rate : RateInput p) (rewards : GridRewardTable p)
  (C_star C_h : ℝ) (control0 : TimeControl p)
  (q : Fin p.T) (a : Fin p.K)
local notation "S" => SourceInput p
local notation "mu" => sourceInputLaw p
local notation "F" => sourcePrefixFiltration control0 (q.val + 1)
local notation "beta" => CanonicalRecordingRates.beta p rate.eta.val
local notation "Q" => ReferenceFirstLaunchNumericalCell.queueParameters rate
private theorem prepare_input_domain
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (activation : ReferencePrelaunchFollower.Activation p) (t : Fin p.T)
    (active : activation.val ≤ t.val + 1)
    (input : DeclaredFollowerLocalRound.LocalConfiguration p rate)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hprep : (DeclaredFollowerLocalRound.prepare rate i row activation t active input).configuration =
      .ordinary state memory) : ActiveFollowerQueueOperation.stateInputDomain state := by
  obtain ⟨before, beforeMemory, hi, hstart, _hreply, _hunoccupied⟩ :=
    ReferenceFollowerReplyChronology.prepare_ordinary_inversion
      i row activation t active input state memory hprep
  by_contra hdomain
  have hoff : ActiveFollowerQueueOperation.checkedUpOffer
      rate.eta i row activation t state = .failure := by
    simp only [ActiveFollowerQueueOperation.checkedUpOffer, dite_eq_right hdomain]
  rw [hi] at hprep
  simp only [DeclaredFollowerLocalRound.prepare, hstart, hoff] at hprep
  cases hprep
private theorem prepare_unoccupied_otherRow
    (i : Fin (p.m - 1)) (row row' : CompletePublicTable.CompleteRow p)
    (activation : ReferencePrelaunchFollower.Activation p) (t : Fin p.T)
    (active : activation.val ≤ t.val + 1)
    (input : DeclaredFollowerLocalRound.LocalConfiguration p rate)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hprep : (DeclaredFollowerLocalRound.prepare rate i row activation t active input).configuration =
      .ordinary state memory)
    (hunoccupied : state.status = .unoccupied)
    (hadmissible : OrdinaryMessageCodec.upAdmissible
      (ReferencePrelaunchFollower.codecParams p rate.eta)
      (ActiveFollowerQueueOperation.upOfferFields state)) :
    (DeclaredFollowerLocalRound.prepare rate i row' activation t active input).configuration =
      .ordinary state memory := by
  obtain ⟨before, beforeMemory, hi, hstart, _hreply, _hunocc⟩ :=
    ReferenceFollowerReplyChronology.prepare_ordinary_inversion
      i row activation t active input state memory hprep
  have hdomain := prepare_input_domain rate i row activation t active input state memory hprep
  let offered : OrdinaryMessageCodec.UpRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta) :=
    ⟨ActiveFollowerQueueOperation.upOfferFields state, hadmissible⟩
  by_cases hselected : ActiveFollowerQueueOperation.selectedUpRound i row' activation t
  · have hoff : ActiveFollowerQueueOperation.checkedUpOffer rate.eta i row' activation t state =
        .offer offered := by
      have hselected' : ActiveFollowerQueueOperation.selectedUpRound i row' activation t ∧
          state.status = .unoccupied := ⟨hselected, hunoccupied⟩
      simp only [ActiveFollowerQueueOperation.checkedUpOffer, dite_eq_left hdomain,
        dite_eq_left hselected', dite_eq_left hadmissible]
      rfl
    have hvalid : ActiveFollowerArmChoice.upStateDomain state ∧
        ActiveFollowerArmChoice.offeredUpMatchesState state offered :=
      ⟨⟨hdomain.1, hdomain.2.1, hdomain.2.2.1⟩, rfl, rfl, rfl, rfl⟩
    have hchoice := ActiveFollowerArmChoice.followerArmChoiceCore_unoccupied_selected_up
      state (row'.2 t) i offered hunoccupied hselected.2.1 hselected.2.2 hvalid
    rw [← ActiveFollowerArmChoice.followerArmChoice_eq_core] at hchoice
    rw [hi]
    simp only [DeclaredFollowerLocalRound.prepare, hstart, hoff, hchoice]
  · have hoff := ActiveFollowerQueueOperation.checkedUpOffer_noOffer rate.eta i row'
      activation t state hdomain (fun h => hselected h.1)
    by_cases hdata : PublicDiscreteDraws.slotDraw (row'.2 t).1 = PublicDiscreteDraws.dataSlot
    · have hchoice := ActiveFollowerArmChoice.followerArmChoiceCore_unoccupied_data
        state (row'.2 t) i none hunoccupied hdata
      rw [← ActiveFollowerArmChoice.followerArmChoice_eq_core] at hchoice
      rw [hi]
      simp only [DeclaredFollowerLocalRound.prepare, hstart, hoff, hchoice]
    · have hnot : ¬ (PublicDiscreteDraws.slotDraw (row'.2 t).1 = PublicDiscreteDraws.upSlot ∧
          PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K (row'.2 t).1 = i) :=
        fun h => hselected ⟨active, h⟩
      have hchoice := ActiveFollowerArmChoice.followerArmChoiceCore_unoccupied_other
        state (row'.2 t) i none hunoccupied hdata hnot
      rw [← ActiveFollowerArmChoice.followerArmChoice_eq_core] at hchoice
      rw [hi]
      simp only [DeclaredFollowerLocalRound.prepare, hstart, hoff, hchoice]
private theorem prepare_otherInput
    (x y : ReferenceActivePhysicalStep.RoundInput p rate)
    (hstate : x.state = y.state) (htime : x.time = y.time)
    (i : Fin (p.m - 1)) (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hprep : ((ReferenceActivePhysicalStep.prepare x).followers.followers i).configuration =
      .ordinary state memory)
    (hunoccupied : state.status = .unoccupied)
    (hadmissible : OrdinaryMessageCodec.upAdmissible
      (ReferencePrelaunchFollower.codecParams p rate.eta)
      (ActiveFollowerQueueOperation.upOfferFields state)) :
    ((ReferenceActivePhysicalStep.prepare y).followers.followers i).configuration =
      .ordinary state memory := by
  rcases x with ⟨state0, rows, selected, time, active, rewards⟩
  rcases y with ⟨state1, rows', selected', time', active', rewards'⟩
  dsimp only at hstate htime
  subst state1
  subst time'
  exact prepare_unoccupied_otherRow rate i (rows selected) (rows' selected')
    (state0.activations i) time (active i) (state0.followers i) state memory hprep
    hunoccupied hadmissible
private theorem collection_continuing_otherRow
    (x : CoordinatorRoundDispatch.CollectionInput p)
    (core : CoordinatorRoundDispatch.CollectionCoreValid x)
    (snapshot : CoordinatorCollectionInteractive.PreparedSnapshot x)
    (hscores : CoordinatorRoundDispatch.collectionCurrentScoresCheck x = true)
    (row : CompletePublicTable.CompleteRow p) :
    ∃ (core' : CoordinatorRoundDispatch.CollectionCoreValid {x with row := row})
      (snapshot' : CoordinatorCollectionInteractive.PreparedSnapshot {x with row := row})
      (boundary : snapshot'.clockStarted.clock.g ≤ p.T + 1)
      (scores : CoordinatorRoundDispatch.collectionCurrentScoresCheck {x with row := row} = true),
      CoordinatorRoundDispatch.dispatchCollection {x with row := row} =
        .continuing core' snapshot' boundary scores ∧
      snapshot'.clockStarted = snapshot.clockStarted := by
  let y : CoordinatorRoundDispatch.CollectionInput p := {x with row := row}
  have hc : CoordinatorRoundDispatch.CollectionCoreValid y :=
    (ReferenceActiveDispatchTemporal.collectionCoreValid_row_iff x row).mp core
  have hp : y.ledger.pending.Nonempty := snapshot.inputsValid.pending_nonempty
  have hs : CoordinatorRoundDispatch.collectionCurrentScoresCheck y = true := hscores
  have hstart : CoordinatorPhaseClock.startRound p y.etaReal y.time y.clock y.ledger.pending =
      .ok snapshot.clockStarted := snapshot.clockStarted_eq
  let weights := CoordinatorCollectionInteractive.PreObservationInputs.weights
    y hc.ledger_valid hc.assignment_eq
  have hchoice : CoordinatorLocalArmChoice.ChoiceInputsValid y.payload
      (some (CoordinatorCollectionUpRoundStep.localCutoff y.cutoffIndex)) y.time weights :=
    snapshot.inputsValid.choice_valid
  have hcutoff : CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
      snapshot.clockStarted.clock.u =
        some (CoordinatorCollectionUpRoundStep.localCutoff y.cutoffIndex) := by
    rw [snapshot.clockStarted_frame.1, core.clock_cutoff_eq]
    rfl
  have hchoice' : CoordinatorLocalArmChoice.ChoiceInputsValid y.payload
      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p snapshot.clockStarted.clock.u)
      y.time weights := by rw [hcutoff]; exact hchoice
  have hnonempty := CoordinatorLiveChoiceRecorderStep.coordinatorArmChoice_ne_none
    y.payload snapshot.clockStarted.pending
    (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p snapshot.clockStarted.clock.u)
    y.time weights y.row hchoice'
  change ∃ core' snapshot' boundary scores,
    CoordinatorRoundDispatch.dispatchCollection y =
      .continuing core' snapshot' boundary scores ∧
      snapshot'.clockStarted = snapshot.clockStarted
  unfold CoordinatorRoundDispatch.dispatchCollection
  split
  · rename_i failure hfailure
    have hbad := hstart.symm.trans hfailure
    cases hbad
  · rename_i started hclock
    have heq : started = snapshot.clockStarted := Except.ok.inj (hclock.symm.trans hstart)
    subst started
    simp only [dite_eq_left hc, dite_eq_left hp, dite_eq_left hs]
    split
    · split
      · rename_i hnone
        exact False.elim (hnonempty hnone)
      · rename_i arm hselected
        let snap : CoordinatorCollectionInteractive.PreparedSnapshot y := {
          inputsValid := { snapshot.inputsValid with }
          clockStarted := snapshot.clockStarted
          clockStarted_eq := hstart
          clockStarted_frame := snapshot.clockStarted_frame
          arm := arm
          armChoice_eq := by simpa only [hcutoff] using hselected }
        have hgrid := CoordinatorPhaseClock.clockRegistersValid_gridDomain
          p y.etaReal y.clock hc.clock_registers_valid
        simp only [CoordinatorPhaseClock.clockGridDomain, hc.clock_sigma_eq] at hgrid
        have hb : snap.clockStarted.clock.g ≤ p.T + 1 := by
          rw [snap.clockStarted_frame.1]
          exact hgrid.2
        exact ⟨hc, snap, hb, hs, rfl, rfl⟩
    · rename_i hbad
      exact False.elim (hbad hchoice)
private def dispatch_collection_domain
    (x : ReferenceActivePhysicalStep.RoundInput p rate) : Prop :=
  match ReferenceActivePhysicalStep.dispatch x with
  | .collection _ _ _ _ (.continuing _ _ _ _) => True
  | .live registers _ _ (.cutoffChosen _ _ _ _ _ _ _ _ _ _) =>
      0 < registers.payload.sigma.val
  | _ => False
private theorem dispatch_collection_domain_freshRow
    (x y : ReferenceActivePhysicalStep.RoundInput p rate)
    (hstate : x.state = y.state) (htime : x.time = y.time)
    (hx : dispatch_collection_domain rate x) :
    dispatch_collection_domain rate y := by
  unfold dispatch_collection_domain at hx ⊢
  cases hs : x.state.coordinator with
  | first =>
      simp only [ReferenceActivePhysicalStep.dispatch, hs,
        CoordinatorRoundDispatch.dispatch] at hx
      cases CoordinatorRoundDispatch.dispatchFirst (ReferenceActivePhysicalStep.firstInput x) <;>
        contradiction
  | dagger =>
      simp only [ReferenceActivePhysicalStep.dispatch, hs] at hx
  | live registers owned base =>
      have hs' : y.state.coordinator = .live registers owned base := by rw [← hstate]; exact hs
      have hdx := ReferenceLiveDispatchMeasurability.canonicalDispatch_live_reconstruction
        x registers owned base hs
      have hdy := ReferenceLiveDispatchMeasurability.canonicalDispatch_live_reconstruction
        y registers owned base hs'
      rw [hdx] at hx
      rw [hdy]
      have hinput : ReferenceActivePhysicalStep.liveInput y registers owned base =
          {ReferenceActivePhysicalStep.liveInput x registers owned base with row := y.row} := by
        dsimp only [ReferenceActivePhysicalStep.liveInput]
        rw [htime]
      have htag := ReferenceFirstCollectionOldRecorderFoundation.liveCutoffTag_otherRow
        (ReferenceActivePhysicalStep.liveInput x registers owned base) y.row
      rw [← hinput] at htag
      cases ho : CoordinatorRoundDispatch.dispatchLive
          (ReferenceActivePhysicalStep.liveInput x registers owned base) <;>
        simp only [ho] at hx
      all_goals
        cases ho' : CoordinatorRoundDispatch.dispatchLive
            (ReferenceActivePhysicalStep.liveInput y registers owned base) <;>
          simp only [ho, ho', ReferenceLiveDispatchOutputMeasurability.outcomeData,
            ReferenceFirstCollectionOldRecorderFoundation.cutoffDataTag,
            Bool.false_eq_true] at htag
      all_goals simpa only [ho'] using hx
  | collection payload ledger proposal =>
      have hs' : y.state.coordinator = .collection payload ledger proposal := by rw [← hstate]; exact hs
      by_cases hcut : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
      · let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
        let clock := ReferenceActivePhysicalStep.collectionClock payload ledger proposal cutoff
        have hdx : ReferenceActivePhysicalStep.dispatch x =
            .collection payload ledger clock cutoff
              (CoordinatorRoundDispatch.dispatchCollection
                (ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff)) := by
          simp only [ReferenceActivePhysicalStep.dispatch, hs, dite_eq_left hcut,
            CoordinatorRoundDispatch.dispatch]
          rfl
        have hdy : ReferenceActivePhysicalStep.dispatch y =
            .collection payload ledger clock cutoff
              (CoordinatorRoundDispatch.dispatchCollection
                (ReferenceActivePhysicalStep.collectionInput y payload ledger clock cutoff)) := by
          simp only [ReferenceActivePhysicalStep.dispatch, hs', dite_eq_left hcut,
            CoordinatorRoundDispatch.dispatch]
          rfl
        rw [hdx] at hx
        rw [hdy]
        have hinput : ReferenceActivePhysicalStep.collectionInput y payload ledger clock cutoff =
            {ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff with
              row := y.row} := by
          simp only [ReferenceActivePhysicalStep.collectionInput, ← hstate, ← htime]
        cases ho : CoordinatorRoundDispatch.dispatchCollection
            (ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff) <;>
          simp only [ho] at hx
        rename_i core snapshot boundary scores
        have hother := collection_continuing_otherRow _ core snapshot scores y.row
        rw [← hinput] at hother
        obtain ⟨core', snapshot', boundary', scores', heq, _hclock⟩ := hother
        rw [heq]
        trivial
      · simp only [ReferenceActivePhysicalStep.dispatch, hs, dite_eq_right hcut] at hx
private theorem presentCell_upAdmissible
    (z : S) (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hrecord : actualRecord rate rewards C_star C_h q z = some record)
    (hunoccupied : ReferenceLaterCollectionArrivalReadout.preparedFollowersUnoccupied record)
    (i : Fin (p.m - 1)) :
    OrdinaryMessageCodec.upAdmissible (ReferencePrelaunchFollower.codecParams p rate.eta)
      (ActiveFollowerQueueOperation.upOfferFields
        (ReferenceLaterCollectionArrivalReadout.actualFollowerParts record hunoccupied i).1) := by
  exact ReferenceFirstCollectionOldRecorderFoundation.actualPrepared_upAdmissible
    rate rewards C_star C_h q z record hrecord i
    (ReferenceLaterCollectionArrivalReadout.actualFollowerParts record hunoccupied i).1
    (ReferenceLaterCollectionArrivalReadout.actualFollowerParts record hunoccupied i).2
    (ReferenceLaterCollectionArrivalReadout.actualFollowerParts_spec record hunoccupied i).1
private theorem presentCell_record_of_incoming
    (z z' : S)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hrecord : actualRecord rate rewards C_star C_h q z = some record)
    (hin : ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h q z' =
      ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h q z) :
    ∃ replacement : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate),
      actualRecord rate rewards C_star C_h q z' = some replacement ∧
        record.input.state = replacement.input.state := by
  cases hrecord' : actualRecord rate rewards C_star C_h q z' with
  | none =>
      simp only [ReferenceSourcePrefixHistoryFiltration.incoming, hrecord', hrecord,
        Option.map_none, Option.map_some] at hin
      cases hin
  | some replacement =>
      have hcode : ReferenceActivePhysicalStepMeasurability.encodeState replacement.input.state =
          ReferenceActivePhysicalStepMeasurability.encodeState record.input.state := by
        exact Option.some.inj (by
          simpa only [ReferenceSourcePrefixHistoryFiltration.incoming, hrecord', hrecord,
            Option.map_some] using hin)
      exact ⟨replacement, rfl,
        (ReferenceActivePhysicalStepMeasurability.encodeState_injective hcode).symm⟩
@[expose] public def C : S → Option (RecordedQueueRun.RoundInput p.K) :=
  ReferenceFirstCollectionOldRecorderFoundation.oldCell? rate rewards C_star C_h q
@[expose] public def physicalMarker? : S → Option (Option (Fin p.K)) := fun z =>
  (actualRecord rate rewards C_star C_h q z).bind fun record =>
    record.coordinatorDiagnostics.recording.map (fun out => out.gateArm)
@[expose] public def P (n : ℕ) : S →
    Option (ReferenceFirstCollectionCurrentQueueReadout.QueueReadout p.K) :=
  ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout
    rate rewards C_star C_h n
@[expose] public def D : Set S := {z | (C rate rewards C_star C_h q z).isSome = true}
@[expose] public def V : Set S := {z | (P rate rewards C_star C_h q.val z).isSome = true}
@[expose] public def B : Set S := D rate rewards C_star C_h q ∩ V rate rewards C_star C_h q
@[expose] public def H : Set S :=
  ReferenceFirstCollectionCurrentRetainedGate.H rate rewards C_star C_h q
@[expose] public def E : Set S :=
  D rate rewards C_star C_h q ∩ {z | ReferenceFirstCollectionOldRecorderFoundation.incomingEnabled?
    rate rewards C_star C_h q z = some true}
@[expose] public def G : Set S :=
  B rate rewards C_star C_h q ∩ H rate rewards C_star C_h q ∩ E rate rewards C_star C_h q
@[expose] public def queueExp (n : ℕ) : S → ℝ := fun z =>
  (P rate rewards C_star C_h n z).elim 0
    (fun readout => Real.exp (beta * (((readout.1 a).2 : ℝ) / ((Q).n : ℝ))))
@[expose] public def W : S → ℝ :=
  (B rate rewards C_star C_h q).indicator (queueExp rate rewards C_star C_h a q.val)
@[expose] public def Xplus : S → ℝ :=
  (B rate rewards C_star C_h q).indicator (queueExp rate rewards C_star C_h a (q.val + 1))
@[expose] public def x : S → ℝ :=
  (G rate rewards C_star C_h q).indicator (fun z =>
    ReferenceFirstCollectionOldRecorderFoundation.oldRaw rate rewards C_star C_h q a z - 4)
@[expose] public def expX : S → ℝ := fun z => Real.exp (beta * x rate rewards C_star C_h q a z)
private theorem presentCell_incoming_forward
    (z z' : S) (hz : z ∈ D rate rewards C_star C_h q)
    (hin : ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h q z' =
      ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h q z) :
    z' ∈ D rate rewards C_star C_h q := by
  obtain ⟨cell, hcell⟩ := Option.isSome_iff_exists.mp hz
  obtain ⟨record, hrecord, hread⟩ := Option.bind_eq_some_iff.mp hcell
  have hsome : (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 record).isSome = true := by
    rw [hread]
    rfl
  obtain ⟨hunoccupied, hbranch⟩ :=
    (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout_domain 0 record).mp hsome
  obtain ⟨replacement, hrecord', hstate⟩ :=
    presentCell_record_of_incoming rate rewards C_star C_h q z z' record hrecord hin
  have hf := ReferenceCalendarLaterSamplerOutputSections.actualRecord_fields
    rate rewards C_star C_h q z record hrecord
  have hf' := ReferenceCalendarLaterSamplerOutputSections.actualRecord_fields
    rate rewards C_star C_h q
      z'
      replacement hrecord'
  have htime : record.input.time = replacement.input.time := hf.2.2.1.trans hf'.2.2.1.symm
  have hfollowers : ReferenceLaterCollectionArrivalReadout.preparedFollowersUnoccupied replacement := by
    intro i
    change (match (replacement.output.preparation.followers.followers i).configuration with
      | .ordinary state _ => state.status = .unoccupied
      | .dagger => False)
    let parts := ReferenceLaterCollectionArrivalReadout.actualFollowerParts record hunoccupied i
    obtain ⟨hconfig, hstatus⟩ := ReferenceLaterCollectionArrivalReadout.actualFollowerParts_spec record hunoccupied i
    have hprep : record.output.preparation = ReferenceActivePhysicalStep.prepare record.input := by
      rw [record.output_eq]
      rfl
    have hprep' : replacement.output.preparation =
        ReferenceActivePhysicalStep.prepare replacement.input := by
      rw [replacement.output_eq]
      rfl
    have hother := prepare_otherInput rate record.input replacement.input hstate htime i
      parts.1 parts.2 (hprep ▸ hconfig) hstatus
      (presentCell_upAdmissible rate rewards C_star C_h q z record hrecord hunoccupied i)
    rw [hprep', hother]
    exact hstatus
  have hdispatch : dispatch_collection_domain rate record.input := by
    unfold dispatch_collection_domain
    rw [← record.output.preparation.coordinator_eq]
    cases hcoord : record.output.preparation.coordinator with
    | first outcome => cases outcome <;> simp_all
    | live registers owned base outcome => cases outcome <;> simp_all
    | collection payload ledger clock cutoff outcome => cases outcome <;> simp_all
    | invalidCollectionCutoff => simp [hcoord] at hbranch ⊢
    | dagger => simp [hcoord] at hbranch ⊢
  have hdispatch' := dispatch_collection_domain_freshRow rate record.input replacement.input hstate htime hdispatch
  have hread' : (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 replacement).isSome = true :=
    (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout_domain 0 replacement).mpr
      ⟨hfollowers, by
        unfold dispatch_collection_domain at hdispatch'
        rw [← replacement.output.preparation.coordinator_eq] at hdispatch'
        cases hcoord : replacement.output.preparation.coordinator with
        | first outcome => cases outcome <;> simp_all
        | live registers owned base outcome => cases outcome <;> simp_all
        | collection payload ledger clock cutoff outcome => cases outcome <;> simp_all
        | invalidCollectionCutoff => simp [hcoord] at hdispatch' ⊢
        | dagger => simp [hcoord] at hdispatch' ⊢⟩
  change (C rate rewards C_star C_h q
    z').isSome = true
  rw [C, ReferenceFirstCollectionOldRecorderFoundation.oldCell?, hrecord', Option.bind_some]
  exact hread'
public theorem presentCell_replaceCurrent_forward
    (control0 : TimeControl p) (z : S)
    (hz : z ∈ D rate rewards C_star C_h q) (fresh : TimeControl p) :
    ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p q z fresh ∈
      D rate rewards C_star C_h q := by
  apply presentCell_incoming_forward rate rewards C_star C_h q z _ hz
  rw [ReferenceSourcePrefixHistoryFiltration.incoming_factor rate rewards C_star C_h
    control0 q]
  rw [ReferenceFirstCollectionOldRecorderFoundation.sourcePrefix_replaceCurrent
    control0 q q.val le_rfl z fresh]
  exact (ReferenceSourcePrefixHistoryFiltration.incoming_factor rate rewards C_star C_h
    control0 q z).symm
public theorem D_factor (control0 : TimeControl p) (z : S) :
    z ∈ D rate rewards C_star C_h q ↔
      ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 q.val z ∈
        D rate rewards C_star C_h q := by
  have hin := ReferenceSourcePrefixHistoryFiltration.incoming_factor
    rate rewards C_star C_h control0 q z
  exact ⟨fun hz => presentCell_incoming_forward rate rewards C_star C_h q _ _ hz hin.symm,
    fun hz => presentCell_incoming_forward rate rewards C_star C_h q _ _ hz hin⟩
public theorem D_replaceCurrent (control0 : TimeControl p) (z : S) (fresh : TimeControl p) :
    ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p q z fresh ∈
      D rate rewards C_star C_h q ↔ z ∈ D rate rewards C_star C_h q := by
  rw [D_factor rate rewards C_star C_h q control0,
    ReferenceFirstCollectionOldRecorderFoundation.sourcePrefix_replaceCurrent
      control0 q q.val le_rfl, ← D_factor rate rewards C_star C_h q control0]
local instance optionMeasurableSpace {A : Type*} [MeasurableSpace A] :
    MeasurableSpace (Option A) := LaterAssignmentStartMeasurability.optionMeasurableSpace
private instance sumMeasurableSingleton {A B : Type*} [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSingletonClass A] [MeasurableSingletonClass B] :
    MeasurableSingletonClass (A ⊕ B) where
  measurableSet_singleton x := by
    cases x with
    | inl a => simpa only [Set.image_singleton] using (MeasurableSet.singleton a).inl_image
    | inr b => simpa only [Set.image_singleton] using (MeasurableSet.singleton b).inr_image
private instance optionMeasurableSingleton {A : Type*} [MeasurableSpace A]
    [MeasurableSingletonClass A] : MeasurableSingletonClass (Option A) where
  measurableSet_singleton x := by
    have h := (comap_measurable (Equiv.optionEquivSumPUnit A))
      (MeasurableSet.singleton (Equiv.optionEquivSumPUnit A x))
    convert h using 1
    ext y
    simp only [Set.mem_singleton_iff, Set.mem_preimage,
      (Equiv.optionEquivSumPUnit A).injective.eq_iff]
private theorem measurableSet_optionNone {A : Type*} [MeasurableSpace A] :
    MeasurableSet ({none} : Set (Option A)) := by
  change MeasurableSet[(inferInstance : MeasurableSpace (A ⊕ PUnit)).comap
    (Equiv.optionEquivSumPUnit A)] {none}
  rw [MeasurableSpace.measurableSet_comap]
  refine ⟨Set.range (Sum.inr : PUnit → A ⊕ PUnit), measurableSet_range_inr, ?_⟩
  ext value
  cases value <;> simp
public theorem measurableSet_D : MeasurableSet[F]
    (D rate rewards C_star C_h q) := by
  have hambient : MeasurableSet (D rate rewards C_star C_h q) := by
    have hm := ReferenceFirstCollectionOldRecorderFoundation.oldMarker_measurable rate rewards C_star C_h q
    have he : D rate rewards C_star C_h q =
        {z | ReferenceFirstCollectionOldRecorderFoundation.oldMarker? rate rewards C_star C_h q z ≠ none} := by
      ext z
      cases hc : ReferenceFirstCollectionOldRecorderFoundation.oldCell? rate rewards C_star C_h q z <;>
        simp [D, C, ReferenceFirstCollectionOldRecorderFoundation.oldMarker?, hc]
    rw [he]
    exact (hm.eq_const none).setOf.compl
  rw [ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration_succ]
  have hm := (comap_measurable
    (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 q.val)) hambient
  have he : ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 q.val ⁻¹'
      D rate rewards C_star C_h q = D rate rewards C_star C_h q := by
    ext z
    exact (D_factor rate rewards C_star C_h q control0 z).symm
  rwa [he] at hm
public theorem P_eq_current (z : S) : P rate rewards C_star C_h q.val z =
    ReferenceFirstCollectionCurrentRetainedGate.prefixReadout? rate rewards C_star C_h q z :=
  ReferenceFirstCollectionCorrectedFutureRetainedMoment.prefixReadout_eq_current
    rate rewards C_star C_h q z
public theorem P_measurable :
    Measurable[F] (P rate rewards C_star C_h q.val) := by
  have he : P rate rewards C_star C_h q.val =
      ReferenceFirstCollectionCurrentRetainedGate.prefixReadout? rate rewards C_star C_h q :=
    funext (P_eq_current rate rewards C_star C_h q)
  rw [he]
  exact ReferenceFirstCollectionCurrentRetainedGate.prefixReadout_measurable
    rate rewards C_star C_h control0 q
public theorem measurableSet_V :
    MeasurableSet[F] (V rate rewards C_star C_h q) := by
  have he : V rate rewards C_star C_h q =
      {z | P rate rewards C_star C_h q.val z ≠ none} := by
    ext z
    simp only [V, Set.mem_ofPred_eq, Option.isSome_iff_ne_none]
  rw [he]
  exact ((measurableSet_optionNone).preimage
    (P_measurable rate rewards C_star C_h control0 q)).compl
public theorem measurableSet_B :
    MeasurableSet[F] (B rate rewards C_star C_h q) :=
  (measurableSet_D rate rewards C_star C_h control0 q).inter
    (measurableSet_V rate rewards C_star C_h control0 q)
public theorem measurableSet_E :
    MeasurableSet[F] (E rate rewards C_star C_h q) :=
  (measurableSet_D rate rewards C_star C_h control0 q).inter
    ((measurableSet_singleton (some true)).preimage
      (ReferenceFirstCollectionOldRecorderFoundation.incomingEnabled_measurable
        rate rewards C_star C_h control0 q))
public theorem measurableSet_G :
    MeasurableSet[F] (G rate rewards C_star C_h q) :=
  ((measurableSet_B rate rewards C_star C_h control0 q).inter
    (ReferenceFirstCollectionCurrentRetainedGate.measurableSet_H
      rate rewards C_star C_h control0 q)).inter
        (measurableSet_E rate rewards C_star C_h control0 q)
private theorem presentCell_call_congr
    (record replacement : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (cell cell' : RecordedQueueRun.RoundInput p.K)
    (hread : ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 record = some cell)
    (hread' : ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 replacement = some cell')
    (hstate : record.input.state = replacement.input.state)
    (htime : record.input.time = replacement.input.time) :
    ReferenceLaterCollectionArrivalReadout.laterCollectionCall 0 record =
      ReferenceLaterCollectionArrivalReadout.laterCollectionCall 0 replacement := by
  have hd := (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout_domain 0 record).mp
    (by rw [hread]; rfl)
  have hd' := (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout_domain 0 replacement).mp
    (by rw [hread']; rfl)
  obtain ⟨hf, hb⟩ := hd
  obtain ⟨hf', hb'⟩ := hd'
  rw [record.output.preparation.coordinator_eq] at hb
  rw [replacement.output.preparation.coordinator_eq] at hb'
  unfold ReferenceLaterCollectionArrivalReadout.laterCollectionCall
  rw [ite_eq_left hf, ite_eq_left hf', record.output.preparation.coordinator_eq,
    replacement.output.preparation.coordinator_eq]
  cases hs : record.input.state.coordinator with
  | first =>
      simp only [ReferenceActivePhysicalStep.dispatch, hs, CoordinatorRoundDispatch.dispatch] at hb
      cases CoordinatorRoundDispatch.dispatchFirst
        (ReferenceActivePhysicalStep.firstInput record.input) <;> contradiction
  | dagger => simp only [ReferenceActivePhysicalStep.dispatch, hs] at hb
  | live registers owned base =>
      have hs' : replacement.input.state.coordinator = .live registers owned base := by
        rw [← hstate]; exact hs
      have hdx := ReferenceLiveDispatchMeasurability.canonicalDispatch_live_reconstruction
        record.input registers owned base hs
      have hdy := ReferenceLiveDispatchMeasurability.canonicalDispatch_live_reconstruction
        replacement.input registers owned base hs'
      rw [hdx] at hb ⊢
      rw [hdy] at hb' ⊢
      cases ho : CoordinatorRoundDispatch.dispatchLive
          (ReferenceActivePhysicalStep.liveInput record.input registers owned base) with
      | cutoffChosen dispatched hstart ledger hinit hcand hdomain hclock hpending hnone selected =>
          cases ho' : CoordinatorRoundDispatch.dispatchLive
              (ReferenceActivePhysicalStep.liveInput replacement.input registers owned base) with
          | cutoffChosen dispatched' hstart' ledger' hinit' hcand' hdomain' hclock' hpending' hnone' selected' =>
              have hstartEq : dispatched.startResult = dispatched'.startResult := by
                apply Except.ok.inj
                exact hstart.symm.trans (by
                  simpa only [ReferenceActivePhysicalStep.liveInput, ← htime] using hstart')
              simp only [ho] at hb
              simp only [ho'] at hb'
              simp only [ite_eq_left hb]
              have hledgerEq : ReferenceActivePhysicalStep.sharedLedger ledger =
                  ReferenceActivePhysicalStep.sharedLedger ledger' := by
                simp only [hcand, hcand', ReferenceActivePhysicalStep.liveInput]
                exact congrArg (fun t : Fin p.T => ReferenceActivePhysicalStep.sharedLedger
                  (CoordinatorStartRoundCutoffDispatch.collectionStartLedger
                    (ReferenceActivePhysicalStep.liveRegistersAt registers t)
                    (ReferenceActivePhysicalStep.liveOwnedAt registers owned t) base t)) htime
              rw [hledgerEq, hstartEq]
              rfl
          | _ => simp only [ho'] at hb'
      | _ => simp only [ho] at hb
  | collection payload ledger saved =>
      have hs' : replacement.input.state.coordinator = .collection payload ledger saved := by
        rw [← hstate]; exact hs
      by_cases hcut : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
      · let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
        let clock := ReferenceActivePhysicalStep.collectionClock payload ledger saved cutoff
        have hdx : ReferenceActivePhysicalStep.dispatch record.input = .collection payload ledger clock cutoff
            (CoordinatorRoundDispatch.dispatchCollection
              (ReferenceActivePhysicalStep.collectionInput record.input payload ledger clock cutoff)) := by
          simp only [ReferenceActivePhysicalStep.dispatch, hs, dite_eq_left hcut,
            CoordinatorRoundDispatch.dispatch]; rfl
        have hdy : ReferenceActivePhysicalStep.dispatch replacement.input = .collection payload ledger clock cutoff
            (CoordinatorRoundDispatch.dispatchCollection
              (ReferenceActivePhysicalStep.collectionInput replacement.input payload ledger clock cutoff)) := by
          simp only [ReferenceActivePhysicalStep.dispatch, hs', dite_eq_left hcut,
            CoordinatorRoundDispatch.dispatch]; rfl
        rw [hdx] at hb ⊢
        rw [hdy] at hb' ⊢
        cases ho : CoordinatorRoundDispatch.dispatchCollection
            (ReferenceActivePhysicalStep.collectionInput record.input payload ledger clock cutoff) <;>
          simp only [ho] at hb
        rename_i core snapshot boundary scores
        have hinput : ReferenceActivePhysicalStep.collectionInput replacement.input payload ledger clock cutoff =
            {ReferenceActivePhysicalStep.collectionInput record.input payload ledger clock cutoff with
              row := replacement.input.row} := by
          simp only [ReferenceActivePhysicalStep.collectionInput, ← hstate, ← htime]
        have hother := collection_continuing_otherRow _ core snapshot scores replacement.input.row
        rw [← hinput] at hother
        obtain ⟨core', snapshot', boundary', scores', heq, hclock⟩ := hother
        simp only [heq, hclock]
        rfl
      · simp only [ReferenceActivePhysicalStep.dispatch, hs, dite_eq_right hcut] at hb
private theorem presentCell_dispatch_payload
    (x : ReferenceActivePhysicalStep.RoundInput p rate) :
    match ReferenceActivePhysicalStep.dispatch x with
    | .live registers _ _ _ =>
        ReferenceAssignmentPayloadPersistence.storedPayload x.state.coordinator =
          some registers.payload
    | .collection payload _ _ _ _ =>
        ReferenceAssignmentPayloadPersistence.storedPayload x.state.coordinator = some payload
    | _ => True := by
  cases hs : x.state.coordinator with
  | first =>
      simp only [ReferenceActivePhysicalStep.dispatch, hs, CoordinatorRoundDispatch.dispatch]
      trivial
  | live registers owned base =>
      simp only [ReferenceActivePhysicalStep.dispatch, hs, CoordinatorRoundDispatch.dispatch]
      rfl
  | collection payload ledger saved =>
      simp only [ReferenceActivePhysicalStep.dispatch, hs]
      by_cases hcut : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
      · simp only [dite_eq_left hcut, CoordinatorRoundDispatch.dispatch]
        rfl
      · simp only [dite_eq_right hcut]
  | dagger => simp only [ReferenceActivePhysicalStep.dispatch, hs]

/-- The actual recorder run and diagnostics, including failed later tails.
All arms of the physical raw input coincide with the witnessed numerical cell. -/
public theorem presentCell_physicalRecorder
    (z : S) (hz : z ∈ D rate rewards C_star C_h q) :
    ∃ (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
      (cell : RecordedQueueRun.RoundInput p.K) (payload : ReferenceActivePhysicalStep.Payload rate) (ledger : ReferenceActivePhysicalStep.Ledger rate)
      (started : CoordinatorPhaseClock.StartRoundResult p)
      (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ)
      (out : CoordinatorRecordingOperation.Output p),
      actualRecord rate rewards C_star C_h q z = some record ∧
      C rate rewards C_star C_h q z = some cell ∧
      ReferenceLaterCollectionArrivalReadout.laterCollectionCall 0 record = some ⟨payload, ledger, started, weights⟩ ∧
      record.coordinatorDiagnostics = ReferenceActivePhysicalStep.collectionPostChoice
        record.output.preparation payload ledger started weights ∧
      CoordinatorRecorderComplementBridge.run (ReferenceActivePhysicalStep.collectionRecordingInput
        record.output.preparation payload started weights) = some out ∧
      cell.enabled = ReferenceActivePhysicalStep.collectionEnabled ledger record.input.time ∧
      cell.rate = payload.rate ∧
      cell.enabled = decide (record.input.time.val + 1 < started.clock.g) ∧
      record.coordinatorDiagnostics.recording = some out ∧ out.gateArm = cell.recordedArm ∧
      (∀ a, CoordinatorCollectionLedger.localArrival
        (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder out) a =
          RecordedQueueRun.quantizedArrival Q cell a) := by
  obtain ⟨cell, hc⟩ := Option.isSome_iff_exists.mp hz
  obtain ⟨record, hr, hread⟩ := Option.bind_eq_some_iff.mp hc
  obtain ⟨payload, ledger, started, weights, out, hcall, hdiag, hrun, henabled, hclock,
    hrate, _hreward, hrecording, hgate, hraw⟩ :=
    ReferenceLaterCollectionArrivalReadout.laterCollectionReadout_call 0 record cell hread
  exact ⟨record, cell, payload, ledger, started, weights, out, hr, hc, hcall, hdiag, hrun, henabled, hrate, hclock, hrecording, hgate, hraw⟩
public theorem presentCell_physicalMarker_eq (z : S) (hz : z ∈ D rate rewards C_star C_h q) :
    physicalMarker? rate rewards C_star C_h q z =
      (C rate rewards C_star C_h q z).map (fun cell => cell.recordedArm) := by
  obtain ⟨record, cell, payload, ledger, started, weights, out, hr, hc, _hcall, _hdiag,
    _hrun, _henabled, _hrate, _hclock, hrecording, hgate, _hraw⟩ :=
    presentCell_physicalRecorder rate rewards C_star C_h q z hz
  simp only [physicalMarker?, hr, Option.bind_some, hrecording, Option.map_some, hc, hgate]
private theorem presentCell_readout_snapshot
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (cell : RecordedQueueRun.RoundInput p.K)
    (hread : ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 record = some cell) :
    ∃ payload : ReferenceActivePhysicalStep.Payload rate,
      ReferenceAssignmentPayloadPersistence.storedPayload record.input.state.coordinator =
        some payload ∧
      cell.rate = payload.rate ∧
      cell.recordedArm = SnapshotRecordingKernel.recordingMap p .collection cell.enabled
        rate.eta.val rate.eta.property rate.sourceCap payload.anchor payload.anchor
        payload.anchor_pos payload.anchor_pos (fun _ => le_rfl)
        (fun a => by linarith [payload.anchor_pos a])
        (ContinuousLearningRows.sliceAt record.input.time record.input.row.2) := by
  obtain ⟨physicalPayload, physicalLedger, started, weights, out, _hcall, _hdiag, _hrun,
    _henabled, _hclock, _hrate, _hreward, _hrecording, hgate, _hraw⟩ :=
    ReferenceLaterCollectionArrivalReadout.laterCollectionReadout_call 0 record cell hread
  have hp : (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 record).isSome =
      true := by rw [hread]; rfl
  obtain ⟨hf, hb⟩ :=
    (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout_domain 0 record).mp hp
  have hframe := presentCell_dispatch_payload rate record.input
  rw [← record.output.preparation.coordinator_eq] at hframe
  cases he : record.output.preparation.coordinator with
  | first outcome => simp only [he] at hb
  | invalidCollectionCutoff => simp only [he] at hb
  | dagger => simp only [he] at hb
  | collection payload ledger clock cutoff outcome =>
      cases outcome with
      | continuing core snapshot boundary scores =>
          have hc : ReferenceLaterCollectionArrivalReadout.continuingCollectionInput
              record payload ledger clock cutoff snapshot = cell := by
            simpa only [ReferenceLaterCollectionArrivalReadout.laterCollectionReadout,
              dite_eq_left hf, he, Option.some.injEq] using hread
          subst cell
          refine ⟨payload, ?_, rfl, ?_⟩
          · simpa only [he] using hframe
          · have hphysical := hgate
            unfold ReferenceLaterCollectionArrivalReadout.continuingCollectionInput at hphysical ⊢
            exact hgate.symm.trans (hphysical.trans
              (ReferenceFirstCollectionOldRecorderFoundation.collectionMap_independent_currentWeights
                rate _ _ _ _ _ _ _ _))
      | _ => simp only [he] at hb
  | live registers owned base outcome =>
      cases outcome with
      | cutoffChosen dispatched hstart ledger hinit hcand hdomain hclock hpending hnone selected =>
          have hpos : 0 < registers.payload.sigma.val := by simpa only [he] using hb
          have hc : ReferenceLaterCollectionArrivalReadout.laterCutoffCollectionInput
              record registers owned base dispatched selected = cell := by
            simpa only [ReferenceLaterCollectionArrivalReadout.laterCollectionReadout,
              dite_eq_left hf, he, dite_eq_left hpos, Option.some.injEq] using hread
          subst cell
          refine ⟨registers.payload, ?_, rfl, ?_⟩
          · simpa only [he] using hframe
          · have hphysical := hgate
            unfold ReferenceLaterCollectionArrivalReadout.laterCutoffCollectionInput at hphysical ⊢
            exact hgate.symm.trans (hphysical.trans
              (ReferenceFirstCollectionOldRecorderFoundation.collectionMap_independent_currentWeights
                rate _ _ _ _ _ _ _ _))
      | _ => simp only [he] at hb
public theorem presentPrefix_append (z : S) (hz : z ∈ B rate rewards C_star C_h q) :
    ∃ (L : List (RecordedQueueRun.RoundInput p.K)) (cell : RecordedQueueRun.RoundInput p.K),
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
        rate rewards C_star C_h q.val z = some L ∧
      C rate rewards C_star C_h q z = some cell ∧
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
        rate rewards C_star C_h (q.val + 1) z = some (L ++ [cell]) ∧
      P rate rewards C_star C_h q.val z = some
        (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
          (RecordedQueueRun.run Q L)) ∧
      P rate rewards C_star C_h (q.val + 1) z = some
        (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
          (RecordedQueueRun.step Q (RecordedQueueRun.run Q L) cell)) := by
  obtain ⟨o, ho⟩ := Option.isSome_iff_exists.mp hz.2
  obtain ⟨L, hL, _⟩ := Option.map_eq_some_iff.mp ho
  obtain ⟨cell, hcell⟩ := Option.isSome_iff_exists.mp hz.1
  obtain ⟨record, hr, hread⟩ := Option.bind_eq_some_iff.mp hcell
  have hlaunch := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs_launch
    rate rewards C_star C_h q.val z L hL
  have hslot : (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords
      rate rewards C_star C_h z)[q.val -
        ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart
          rate rewards C_star C_h z]? = some record := by
    simpa only [ReferenceSourcePrefixHistoryFiltration.actualRecord,
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords,
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart,
      ite_eq_left hlaunch.2] using hr
  have hlive : ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 record = none := by
    cases hc : ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 record with
    | none => rfl
    | some other =>
        exact False.elim (ReferenceCompleteNumericalBranchObservation.readouts_disjoint
          rate 0 record ⟨by rw [hc]; rfl, by rw [hread]; rfl⟩)
  have hcell0 : ReferenceFirstCollectionCurrentRetainedGate.cell0 rate record = some cell := by
    simp only [ReferenceFirstCollectionCurrentRetainedGate.cell0, hlive, Option.none_or, hread]
  have hnext := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs_append_one
    rate rewards C_star C_h q.val z L hL record cell hslot hcell0
  refine ⟨L, cell, hL, hcell, hnext, ?_, ?_⟩
  · simp only [P, ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout,
      hL, Option.map_some]
  · simp only [P, ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout,
      hnext, Option.map_some,
      ReferenceFirstCollectionRenewalFutureNumericalPrefix.run_append_one]

/-- The SAME original successor queue obeys the stopped recurrence. The
incoming overflow test retains the first detecting update and disabled
or already stopped queues persist. The incoming queue is never reset. -/
public theorem presentPrefix_queue_step (z : S) (hz : z ∈ B rate rewards C_star C_h q) :
    ∃ before after : ReferenceFirstCollectionCurrentQueueReadout.QueueReadout p.K,
      P rate rewards C_star C_h q.val z = some before ∧
      P rate rewards C_star C_h (q.val + 1) z = some after ∧
      ((after.1 a).2 : ℝ) / ((Q).n : ℝ) =
        if z ∈ G rate rewards C_star C_h q then
          max (((before.1 a).2 : ℝ) / ((Q).n : ℝ) +
            x rate rewards C_star C_h q a z) 0
        else ((before.1 a).2 : ℝ) / ((Q).n : ℝ) := by
  obtain ⟨L, cell, _hL, hcell, _hnext, hbefore, hafter⟩ :=
    presentPrefix_append rate rewards C_star C_h q z hz
  refine ⟨_, _, hbefore, hafter, ?_⟩
  have hH : z ∈ H rate rewards C_star C_h q ↔
      (RecordedQueueRun.run Q L).overflow = false := by
    have hp := (P_eq_current rate rewards C_star C_h q z).symm.trans hbefore
    simp only [H, ReferenceFirstCollectionCurrentRetainedGate.H,
      Set.mem_ofPred_eq, hp, Option.some.injEq, exists_eq_left',
      ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout]
  have hE : z ∈ E rate rewards C_star C_h q ↔ cell.enabled = true := by
    have he := ReferenceFirstCollectionOldRecorderFoundation.oldCell_enabled_eq_incoming
      rate rewards C_star C_h q z cell hcell
    change (z ∈ D rate rewards C_star C_h q ∧
      ReferenceFirstCollectionOldRecorderFoundation.incomingEnabled?
        rate rewards C_star C_h q z = some true) ↔ _
    rw [he]
    simp only [hz.1, true_and, Option.some.injEq]
  have hG : z ∈ G rate rewards C_star C_h q ↔
      (RecordedQueueRun.run Q L).overflow = false ∧ cell.enabled = true := by
    change (z ∈ B rate rewards C_star C_h q ∧ z ∈ H rate rewards C_star C_h q) ∧
      z ∈ E rate rewards C_star C_h q ↔ _
    simp only [hz, true_and, hH, hE]
  by_cases hg : z ∈ G rate rewards C_star C_h q
  · obtain ⟨hf, he⟩ := hG.mp hg
    have hraw : RecordedRoundMoments.rawEstimate Q (RecordedQueueRun.run Q L) cell a =
        ReferenceFirstCollectionOldRecorderFoundation.oldRaw rate rewards C_star C_h q a z := by
      change ReferenceFirstCollectionOldRecorderFoundation.oldCell?
        rate rewards C_star C_h q z = some cell at hcell
      simp only [ReferenceFirstCollectionOldRecorderFoundation.oldRaw, hcell,
        RecordedRoundMoments.rawEstimate, RecordedQueueRun.acceptedRecord,
        hf, Bool.false_eq_true, ite_false, he, ite_true,
        RecordedQueueRun.acceptedArrival, RecordedRoundMoments.normalizedQuantizedArrival]
    simpa only [ite_eq_left hg, x, Set.indicator_of_mem hg, hraw,
      ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout,
      StoppedQueueBound.normalizedBacklog, add_sub_assoc] using
      CanonicalQueueProcess.normalizedBacklog_step_of_retained
        Q (RecordedQueueRun.run Q L) cell a hf he
  · have hinactive : (RecordedQueueRun.run Q L).overflow = true ∨ cell.enabled = false := by
      have hn := mt hG.mpr hg
      cases hf : (RecordedQueueRun.run Q L).overflow <;> cases he : cell.enabled <;>
        simp_all
    simpa only [ite_eq_right hg,
      ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout,
      StoppedQueueBound.normalizedBacklog] using
      CanonicalQueueProcess.normalizedBacklog_step_of_inactive
        Q (RecordedQueueRun.run Q L) cell a hinactive.symm
public theorem presentCell_recordingMap
    (z : S) (hz : z ∈ D rate rewards C_star C_h q) :
    ∃ (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
      (cell : RecordedQueueRun.RoundInput p.K)
      (payload : ReferenceActivePhysicalStep.Payload rate),
      actualRecord rate rewards C_star C_h q z = some record ∧
      C rate rewards C_star C_h q z = some cell ∧
      ReferenceFirstCollectionOldRecorderFoundation.incomingPayload?
        rate rewards C_star C_h q z = some payload ∧
      cell.rate = payload.rate ∧
      cell.recordedArm = SnapshotRecordingKernel.recordingMap p .collection cell.enabled
        rate.eta.val rate.eta.property rate.sourceCap payload.anchor payload.anchor
        payload.anchor_pos payload.anchor_pos (fun _ => le_rfl)
        (fun a => by linarith [payload.anchor_pos a])
        (ContinuousLearningRows.sliceAt record.input.time record.input.row.2) := by
  obtain ⟨cell, hcell⟩ := Option.isSome_iff_exists.mp hz
  obtain ⟨record, hrecord, hread⟩ := Option.bind_eq_some_iff.mp hcell
  obtain ⟨payload, hstored, hrate, hmap⟩ := presentCell_readout_snapshot rate record cell hread
  refine ⟨record, cell, payload, hrecord, hcell, ?_, hrate, hmap⟩
  simp only [ReferenceFirstCollectionOldRecorderFoundation.incomingPayload?, hrecord,
    Option.bind_some, hstored]

/-- Every fresh complete current control preserves the unrestricted present
cell, its inherited payload and rates, and its enabled bit. Its recorded option
is the actual snapshot map evaluated at that fresh row. -/
public theorem presentCell_replaceCurrent_snapshot
    (control0 : TimeControl p) (z : S)
    (hz : z ∈ D rate rewards C_star C_h q) (fresh : TimeControl p) :
    ∃ (record replacement : ReferenceActivePhysicalHorizon.RoundRecord
        (p := p) (rate := rate))
      (cell cell' : RecordedQueueRun.RoundInput p.K)
      (payload : ReferenceActivePhysicalStep.Payload rate),
      actualRecord rate rewards C_star C_h q z = some record ∧
      actualRecord rate rewards C_star C_h q
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p q z fresh) =
          some replacement ∧
      C rate rewards C_star C_h q z = some cell ∧
      C rate rewards C_star C_h q
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p q z fresh) =
          some cell' ∧
      ReferenceFirstCollectionOldRecorderFoundation.incomingPayload?
        rate rewards C_star C_h q z = some payload ∧
      ReferenceFirstCollectionOldRecorderFoundation.incomingPayload?
        rate rewards C_star C_h q
          (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p q z fresh) =
            some payload ∧
      cell.enabled = cell'.enabled ∧
      ReferenceLaterCollectionArrivalReadout.laterCollectionCall 0 record =
        ReferenceLaterCollectionArrivalReadout.laterCollectionCall 0 replacement ∧
      cell.rate = payload.rate ∧ cell'.rate = payload.rate ∧
      cell.recordedArm = SnapshotRecordingKernel.recordingMap p .collection cell.enabled
        rate.eta.val rate.eta.property rate.sourceCap payload.anchor payload.anchor
        payload.anchor_pos payload.anchor_pos (fun _ => le_rfl)
        (fun a => by linarith [payload.anchor_pos a])
        (ContinuousLearningRows.sliceAt record.input.time record.input.row.2) ∧
      cell'.recordedArm = SnapshotRecordingKernel.recordingMap p .collection cell'.enabled
        rate.eta.val rate.eta.property rate.sourceCap payload.anchor payload.anchor
        payload.anchor_pos payload.anchor_pos (fun _ => le_rfl)
        (fun a => by linarith [payload.anchor_pos a])
        (ContinuousLearningRows.sliceAt replacement.input.time replacement.input.row.2) := by
  have hz' := presentCell_replaceCurrent_forward rate rewards C_star C_h q control0 z hz fresh
  obtain ⟨record, cell, payload, hrecord, hcell, hpayload, hrate, hmap⟩ :=
    presentCell_recordingMap rate rewards C_star C_h q z hz
  obtain ⟨replacement, cell', payload', hreplacement, hcell', hpayload', hrate', hmap'⟩ :=
    presentCell_recordingMap rate rewards C_star C_h q
      (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p q z fresh) hz'
  have hpayloadEq : payload' = payload := Option.some.inj
    (hpayload'.symm.trans
      ((ReferenceFirstCollectionOldRecorderFoundation.incomingPayload_replaceCurrent
        rate rewards C_star C_h control0 q z fresh).trans hpayload))
  subst payload'
  have hinc := ReferenceFirstCollectionOldRecorderFoundation.incomingEnabled_replaceCurrent
    rate rewards C_star C_h control0 q z fresh
  have he := ReferenceFirstCollectionOldRecorderFoundation.oldCell_enabled_eq_incoming
    rate rewards C_star C_h q z cell hcell
  have he' := ReferenceFirstCollectionOldRecorderFoundation.oldCell_enabled_eq_incoming
    rate rewards C_star C_h q
      (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p q z fresh) cell' hcell'
  have henabled : cell.enabled = cell'.enabled := (Option.some.inj
    (he'.symm.trans (hinc.trans he))).symm
  have hin : ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h q
      (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p q z fresh) =
        ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h q z := by
    rw [ReferenceSourcePrefixHistoryFiltration.incoming_factor rate rewards C_star C_h control0 q,
      ReferenceFirstCollectionOldRecorderFoundation.sourcePrefix_replaceCurrent control0 q q.val le_rfl,
      ← ReferenceSourcePrefixHistoryFiltration.incoming_factor rate rewards C_star C_h control0 q]
  have hstate : record.input.state = replacement.input.state :=
    ReferenceActivePhysicalStepMeasurability.encodeState_injective (Option.some.inj (by
      simpa only [ReferenceSourcePrefixHistoryFiltration.incoming, hrecord, hreplacement,
        Option.map_some] using hin.symm))
  have hf := ReferenceCalendarLaterSamplerOutputSections.actualRecord_fields
    rate rewards C_star C_h q z record hrecord
  have hf' := ReferenceCalendarLaterSamplerOutputSections.actualRecord_fields
    rate rewards C_star C_h q _ replacement hreplacement
  have hread : ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 record = some cell := by
    simpa only [C, ReferenceFirstCollectionOldRecorderFoundation.oldCell?, hrecord, Option.bind_some] using hcell
  have hread' : ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 replacement = some cell' := by
    simpa only [C, ReferenceFirstCollectionOldRecorderFoundation.oldCell?, hreplacement, Option.bind_some] using hcell'
  exact ⟨record, replacement, cell, cell', payload, hrecord, hreplacement, hcell, hcell',
    hpayload, hpayload', henabled, presentCell_call_congr rate record replacement cell cell'
      hread hread' hstate (hf.2.2.1.trans hf'.2.2.1.symm), hrate, hrate', hmap, hmap'⟩
public theorem presentCell_marker_control_integral
    (control0 : TimeControl p) (z : S)
    (hz : z ∈ D rate rewards C_star C_h q) (o : Option (Fin p.K)) :
    ∃ (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
      (cell : RecordedQueueRun.RoundInput p.K)
      (payload : ReferenceActivePhysicalStep.Payload rate),
      actualRecord rate rewards C_star C_h q z = some record ∧
      C rate rewards C_star C_h q z = some cell ∧
      ReferenceFirstCollectionOldRecorderFoundation.incomingPayload?
        rate rewards C_star C_h q z = some payload ∧
      (∫ fresh : TimeControl p,
        (if physicalMarker? rate rewards C_star C_h q
          (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p q z fresh) = some o then (1 : ℝ) else 0)
          ∂ContinuousLearningRows.timeControlLaw p) =
        if cell.enabled = true then
          match o with
          | some a => payload.rate a
          | none => 1 - ∑ a, payload.rate a
        else if o = none then 1 else 0 := by
  obtain ⟨record, cell, payload, hrecord, hcell, hpayload, _hrate, _hmap⟩ :=
    presentCell_recordingMap rate rewards C_star C_h q z hz
  have hmarkers (fresh : TimeControl p) :
      physicalMarker? rate rewards C_star C_h q
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p q z fresh) = some (SnapshotRecordingKernel.recordingMap p .collection
            cell.enabled rate.eta.val rate.eta.property rate.sourceCap payload.anchor payload.anchor
            payload.anchor_pos payload.anchor_pos (fun _ => le_rfl)
            (fun a => by linarith [payload.anchor_pos a]) fresh.1) := by
    obtain ⟨record₀, replacement, cell₀, cell', payload', _hr₀, hreplacement,
      hcell₀, hcell', _hpay₀, hpay', henabled, _hcall, _hrate₀, _hrate', _hmap₀, hmap'⟩ :=
      presentCell_replaceCurrent_snapshot rate rewards C_star C_h q control0 z hz fresh
    have hcellEq : cell₀ = cell := Option.some.inj (hcell₀.symm.trans hcell)
    subst cell₀
    have hpayEq : payload' = payload := Option.some.inj
      (hpay'.symm.trans
        ((ReferenceFirstCollectionOldRecorderFoundation.incomingPayload_replaceCurrent
          rate rewards C_star C_h control0 q z fresh).trans hpayload))
    subst payload'
    have hf := ReferenceCalendarLaterSamplerOutputSections.actualRecord_fields
      rate rewards C_star C_h q
      (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p q z fresh)
      replacement hreplacement
    have hslice : ContinuousLearningRows.sliceAt replacement.input.time
        replacement.input.row.2 = fresh.1 := by
      rw [hf.2.2.1]
      change ((replacement.input.rows replacement.input.selected).2 q).1 = fresh.1
      rw [hf.1, hf.2.1]
      simp [ReferenceFixedTimeSourceControlCoupling.replaceSourceControl,
        ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex,
        ActualInitializationPhysicalStep.selectedRowIndex, Function.update_self]
    rw [presentCell_physicalMarker_eq rate rewards C_star C_h q _
      (presentCell_replaceCurrent_forward rate rewards C_star C_h q control0 z hz fresh),
      hcell', Option.map_some, hmap', henabled, hslice]
  have htest :
      (fun fresh : TimeControl p =>
        if physicalMarker? rate rewards C_star C_h q
          (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p q z fresh) = some o then (1 : ℝ) else 0) =
      (fun fresh : TimeControl p =>
        if SnapshotRecordingKernel.recordingMap p .collection cell.enabled
        rate.eta.val rate.eta.property rate.sourceCap payload.anchor payload.anchor
        payload.anchor_pos payload.anchor_pos (fun _ => le_rfl)
        (fun a => by linarith [payload.anchor_pos a]) fresh.1 = o then (1 : ℝ) else 0) := by
    funext fresh
    rw [hmarkers fresh]
    simp only [Option.some.injEq]
  refine ⟨record, cell, payload, hrecord, hcell, hpayload, ?_⟩
  rw [htest]
  cases he : cell.enabled with
  | true => cases o <;> simpa using
      (ReferenceFirstCollectionOldSelectorRecordingLaw.collection_recordingMap_control_integral rate payload _)
  | false =>
      have hzero (fresh : TimeControl p) :
          SnapshotRecordingKernel.recordingMap p .collection false
        rate.eta.val rate.eta.property rate.sourceCap payload.anchor payload.anchor
        payload.anchor_pos payload.anchor_pos (fun _ => le_rfl)
        (fun a => by linarith [payload.anchor_pos a]) fresh.1 = none :=
        SnapshotRecordingKernel.recordingMap_disabled p .collection rate.eta.val
          rate.eta.property rate.sourceCap payload.anchor payload.anchor payload.anchor_pos
          payload.anchor_pos (fun _ => le_rfl)
          (fun j => by linarith [payload.anchor_pos j]) fresh.1
      simp only [Bool.false_eq_true, ite_false]
      simp_rw [hzero]
      cases o <;> simp [integral_const, probReal_univ]
open ReferenceFirstCollectionOldRecorderFoundation
  (oldMarker? incomingPayload? incomingPayload_eq_code incomingPayload_factor
    incomingEnabled? incomingEnabled_eq_code incomingRates? sourcePrefix_replaceCurrent
    oldCell_enabled_eq_incoming oldMarker_measurable)
open ReferenceSourcePrefixHistoryFiltration (incoming sourcePrefix)
private theorem marker_snapshot (z : S) (hz : z ∈ D rate rewards C_star C_h q) :
    ∃ (payload : ReferenceActivePhysicalStep.Payload rate) (c : RecordedQueueRun.RoundInput p.K),
      incomingPayload? rate rewards C_star C_h q z = some payload ∧
      C rate rewards C_star C_h q z = some c ∧ c.rate = payload.rate ∧
      oldMarker? rate rewards C_star C_h q z =
        some (SnapshotRecordingKernel.recordingMap p .collection c.enabled
        rate.eta.val rate.eta.property rate.sourceCap payload.anchor payload.anchor
        payload.anchor_pos payload.anchor_pos (fun _ => le_rfl)
        (fun a => by linarith [payload.anchor_pos a])
          (ReferenceSourceCurrentControlFreshness.u_t p q z).1) := by
  obtain ⟨record, c, payload, hr, hc, hp, hrate, hmap⟩ :=
    presentCell_recordingMap rate rewards C_star C_h q z hz
  have hf := ReferenceCalendarLaterSamplerOutputSections.actualRecord_fields
    rate rewards C_star C_h q z record hr
  refine ⟨payload, c, hp, hc, hrate, ?_⟩
  change (C rate rewards C_star C_h q z).map _ = _
  rw [hc, Option.map_some, hmap]
  simp only [ContinuousLearningRows.sliceAt, ReferenceActivePhysicalStep.RoundInput.row,
    hf.1, hf.2.1, hf.2.2.1, ReferenceSourceCurrentControlFreshness.u_t]
private theorem marker_eq_of_incoming_current (r : Fin p.T) (z z' : SourceInput p)
    (hz : z ∈ D rate rewards C_star C_h r)
    (hz' : z' ∈ D rate rewards C_star C_h r)
    (hin : incoming rate rewards C_star C_h r z = incoming rate rewards C_star C_h r z')
    (hu : ReferenceSourceCurrentControlFreshness.u_t p r z =
      ReferenceSourceCurrentControlFreshness.u_t p r z') :
    oldMarker? rate rewards C_star C_h r z = oldMarker? rate rewards C_star C_h r z' := by
  obtain ⟨payload, c, hp, hc, _hrate, hm⟩ :=
    marker_snapshot rate rewards C_star C_h r z hz
  obtain ⟨payload', c', hp', hc', _hrate', hm'⟩ :=
    marker_snapshot rate rewards C_star C_h r z' hz'
  have hpay : incomingPayload? rate rewards C_star C_h r z =
      incomingPayload? rate rewards C_star C_h r z' := by
    rw [incomingPayload_eq_code, incomingPayload_eq_code, hin]
  have he : incomingEnabled? rate rewards C_star C_h r z =
      incomingEnabled? rate rewards C_star C_h r z' := by
    rw [incomingEnabled_eq_code, incomingEnabled_eq_code, hin]
  have hpayload : payload' = payload := Option.some.inj (hp'.symm.trans (hpay.symm.trans hp))
  subst payload'
  have henabled : c'.enabled = c.enabled := Option.some.inj
    ((oldCell_enabled_eq_incoming rate rewards C_star C_h r z' c' hc').symm.trans
      (he.symm.trans (oldCell_enabled_eq_incoming rate rewards C_star C_h r z c hc)))
  rw [hm, hm', henabled, hu]
private theorem marker_control_integral (control0 : TimeControl p) (r : Fin p.T)
    (z : S) (hz : z ∈ D rate rewards C_star C_h r) (o : Option (Fin p.K)) :
    (∫ fresh : TimeControl p,
      (if oldMarker? rate rewards C_star C_h r
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p r z fresh) = some o
        then (1 : ℝ) else 0) ∂ContinuousLearningRows.timeControlLaw p) =
      if incomingEnabled? rate rewards C_star C_h r z = some true then
        match o with
        | some a => (incomingRates? rate rewards C_star C_h r z).getD (fun _ => 0) a
        | none => 1 - ∑ a, (incomingRates? rate rewards C_star C_h r z).getD (fun _ => 0) a
      else if o = none then 1 else 0 := by
  obtain ⟨record, cell, payload, _hr, hc, hp, hi⟩ :=
    presentCell_marker_control_integral rate rewards C_star C_h r control0 z hz o
  have he := oldCell_enabled_eq_incoming rate rewards C_star C_h r z cell hc
  have hrates : incomingRates? rate rewards C_star C_h r z = some payload.rate := by
    simp only [incomingRates?, hp, Option.map_some]
  rw [he, hrates]
  simp only [Option.some.injEq, Option.getD_some]
  convert hi using 1
  apply integral_congr_ae
  filter_upwards [] with fresh
  rw [presentCell_physicalMarker_eq rate rewards C_star C_h r _
    (presentCell_replaceCurrent_forward rate rewards C_star C_h r control0 z hz fresh)]
  rfl
public theorem presentCell_marker_condExp (control0 : TimeControl p) (r : Fin p.T)
    (o : Option (Fin p.K)) :
    (sourceInputLaw p)[(D rate rewards C_star C_h r).indicator
      (fun z => if oldMarker? rate rewards C_star C_h r z = some o then (1 : ℝ) else 0) |
      sourcePrefixFiltration control0 (r.val + 1)] =ᵐ[sourceInputLaw p]
      (D rate rewards C_star C_h r).indicator (fun z =>
        if incomingEnabled? rate rewards C_star C_h r z = some true then
          match o with
          | some a => (incomingRates? rate rewards C_star C_h r z).getD (fun _ => 0) a
          | none => 1 - ∑ a, (incomingRates? rate rewards C_star C_h r z).getD (fun _ => 0) a
        else if o = none then 1 else 0) := by
  let E := D rate rewards C_star C_h r
  let test := fun z => if oldMarker? rate rewards C_star C_h r z = some o then (1 : ℝ) else 0
  let coefficient := fun z =>
    if incomingEnabled? rate rewards C_star C_h r z = some true then
      match o with
      | some a => (incomingRates? rate rewards C_star C_h r z).getD (fun _ => 0) a
      | none => 1 - ∑ a, (incomingRates? rate rewards C_star C_h r z).getD (fun _ => 0) a
    else if o = none then (1 : ℝ) else 0
  let B : Set (SourceInput p × TimeControl p) := {x |
    ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p r x.1 x.2 ∈ E ∧
      oldMarker? rate rewards C_star C_h r
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p r x.1 x.2) = some o}
  have hB : MeasurableSet B :=
    ((((sourcePrefixFiltration control0).le' (r.val + 1) _
      (measurableSet_D rate rewards C_star C_h control0 r))).inter
      ((oldMarker_measurable rate rewards C_star C_h r) (measurableSet_singleton (some o)))).preimage
        (ReferenceSourcePhysicalFlagConditionalLaw.measurable_replaceSourceControl p r)
  have hBtest (seed : SourceInput p) (fresh : TimeControl p) :
      B.indicator (fun _ => (1 : ℝ)) (seed, fresh) =
        E.indicator test
          (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p r seed fresh) := by
    by_cases he : ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p r seed fresh ∈ E <;>
      simp [B, test, Set.indicator, he]
  have hrestore (z : SourceInput p) :
      E.indicator test
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p r
          (ReferenceSourceCurrentControlFreshness.c_t p control0 r z)
          (ReferenceSourceCurrentControlFreshness.u_t p r z)) = E.indicator test z := by
    rw [ReferenceSourcePhysicalFlagConditionalLaw.c_t_eq_sourcePrefix]
    let seed := sourcePrefix control0 r.val z
    let fresh := ReferenceSourceCurrentControlFreshness.u_t p r z
    let restored := ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p r seed fresh
    have hE : restored ∈ E ↔ z ∈ E :=
      (D_replaceCurrent rate rewards C_star C_h r control0 seed fresh).trans
        (D_factor rate rewards C_star C_h r control0 z).symm
    by_cases hz : z ∈ E
    · have hz' := hE.mpr hz
      have hin : incoming rate rewards C_star C_h r restored =
          incoming rate rewards C_star C_h r z := by
        rw [ReferenceSourcePrefixHistoryFiltration.incoming_factor
          rate rewards C_star C_h control0 r restored]
        dsimp only [restored, seed]
        rw [sourcePrefix_replaceCurrent control0 r r.val le_rfl,
          ReferenceSourcePrefixHistoryFiltration.sourcePrefix_sourcePrefix control0 r.val r.val le_rfl,
          ← ReferenceSourcePrefixHistoryFiltration.incoming_factor rate rewards C_star C_h control0 r z]
      have hu : ReferenceSourceCurrentControlFreshness.u_t p r restored =
          ReferenceSourceCurrentControlFreshness.u_t p r z := by
        simp only [restored, fresh, ReferenceSourceCurrentControlFreshness.u_t,
          ReferenceFixedTimeSourceControlCoupling.replaceSourceControl,
          ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex,
          ActualInitializationPhysicalStep.selectedRowIndex, Function.update_self]
      have hm := marker_eq_of_incoming_current rate rewards C_star C_h r restored z hz' hz hin hu
      change E.indicator test restored = E.indicator test z
      simp only [Set.indicator_of_mem hz', Set.indicator_of_mem hz, test, hm]
    · have hz' := mt hE.mp hz
      exact (Set.indicator_of_notMem hz' test).trans (Set.indicator_of_notMem hz test).symm
  have htest : ReferenceSourceCurrentControlFreshness.sourceControlTest p control0 r B =
      E.indicator test := by
    funext z
    exact (hBtest _ _).trans (hrestore z)
  have hsection (z : SourceInput p) :
      (∫ fresh, B.indicator (fun _ => (1 : ℝ))
        (ReferenceSourceCurrentControlFreshness.c_t p control0 r z, fresh)
        ∂ContinuousLearningRows.timeControlLaw p) = E.indicator coefficient z := by
    rw [ReferenceSourcePhysicalFlagConditionalLaw.c_t_eq_sourcePrefix]
    let seed := sourcePrefix control0 r.val z
    by_cases hz : z ∈ E
    · have hs : seed ∈ E := (D_factor rate rewards C_star C_h r control0 z).mp hz
      have heq : (fun fresh => B.indicator (fun _ => (1 : ℝ)) (seed, fresh)) =
          fun fresh => test (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p r seed fresh) := by
        funext fresh
        rw [hBtest, Set.indicator_of_mem
          (presentCell_replaceCurrent_forward rate rewards C_star C_h r control0 seed hs fresh)]
      change (∫ fresh, B.indicator (fun _ => (1 : ℝ)) (seed, fresh)
        ∂ContinuousLearningRows.timeControlLaw p) = _
      rw [heq, Set.indicator_of_mem hz]
      have hi := marker_control_integral rate rewards C_star C_h control0 r seed hs o
      have hrates : incomingRates? rate rewards C_star C_h r seed =
          incomingRates? rate rewards C_star C_h r z := by
        unfold incomingRates?
        rw [← incomingPayload_factor rate rewards C_star C_h control0 r z]
      have henabled : incomingEnabled? rate rewards C_star C_h r seed =
          incomingEnabled? rate rewards C_star C_h r z := by
        rw [incomingEnabled_eq_code, incomingEnabled_eq_code,
          ← ReferenceSourcePrefixHistoryFiltration.incoming_factor rate rewards C_star C_h control0 r z]
      simpa only [test, coefficient, hrates, henabled] using hi
    · have hs : seed ∉ E := mt (D_factor rate rewards C_star C_h r control0 z).mpr hz
      have heq : (fun fresh => B.indicator (fun _ => (1 : ℝ)) (seed, fresh)) = fun _ => 0 := by
        funext fresh
        rw [hBtest, Set.indicator_of_notMem
          (mt (D_replaceCurrent rate rewards C_star C_h r control0 seed fresh).mp hs)]
      change (∫ fresh, B.indicator (fun _ => (1 : ℝ)) (seed, fresh)
        ∂ContinuousLearningRows.timeControlLaw p) = _
      rw [heq, integral_zero, Set.indicator_of_notMem hz]
  have hce := ReferenceSourceCurrentControlFreshness.source_control_test_condExp control0 r B hB
  rw [htest] at hce
  simpa only [ReferenceSourcePhysicalFlagConditionalLaw.sourcePrefixField_eq_m_t, hsection] using hce
private theorem raw_amplitude_identity (r : Fin p.T) (a : Fin p.K) (z : SourceInput p)
    (hz : z ∈ D rate rewards C_star C_h r) :
    ReferenceFirstCollectionOldRecorderFoundation.oldRaw rate rewards C_star C_h r a z =
      (if oldMarker? rate rewards C_star C_h r z = some (some a) then 1 else 0) *
        (ReferenceFirstCollectionOldRecorderFoundation.incomingAmplitude? rate rewards C_star C_h r a z).getD 0 := by
  obtain ⟨_record, c, payload, _hr, hc, hp, hrate, _hm⟩ :=
    presentCell_recordingMap rate rewards C_star C_h r z hz
  change ReferenceFirstCollectionOldRecorderFoundation.oldCell?
    rate rewards C_star C_h r z = some c at hc
  have hreward := ReferenceFirstCollectionOldRecorderFoundation.oldCell_reward rate rewards C_star C_h r z c hc
  by_cases ha : c.recordedArm = some a
  · simp only [ReferenceFirstCollectionOldRecorderFoundation.oldRaw, hc]
    rw [RecordedRoundMoments.normalizedQuantizedArrival_eq_quantizedValue_of_recorded
      _ c a ha]
    simp only [oldMarker?, hc, Option.map_some, ha, ↓reduceIte,
      ReferenceFirstCollectionOldRecorderFoundation.incomingAmplitude?, hp, Option.getD_some, one_mul, hrate, hreward]
    rfl
  · simp only [ReferenceFirstCollectionOldRecorderFoundation.oldRaw, hc, RecordedRoundMoments.normalizedQuantizedArrival,
      RecordedQueueRun.quantizedArrival, ha, ite_false, Nat.cast_zero, zero_div]
    simp only [oldMarker?, hc, Option.map_some, Option.some.injEq, ha, ite_false, zero_mul]
private theorem integrable_bounded {f : S → ℝ} (hf : Measurable f) (c : ℝ)
    (hb : ∀ z, ‖f z‖ ≤ c) : Integrable f mu :=
  (integrable_const c).mono' hf.aestronglyMeasurable (Filter.Eventually.of_forall hb)
private theorem measurable_queueExp_projection : Measurable
    (fun o : Option (ReferenceFirstCollectionCurrentQueueReadout.QueueReadout p.K) =>
      o.elim (0 : ℝ) (fun r => Real.exp (beta * (((r.1 a).2 : ℝ) / ((Q).n : ℝ))))) := by
  have hr : Measurable (fun r : ReferenceFirstCollectionCurrentQueueReadout.QueueReadout p.K =>
      Real.exp (beta * (((r.1 a).2 : ℝ) / ((Q).n : ℝ)))) := by fun_prop
  convert (hr.sumElim measurable_const).comp
    (comap_measurable (Equiv.optionEquivSumPUnit
      (ReferenceFirstCollectionCurrentQueueReadout.QueueReadout p.K))) using 1
  funext o
  cases o <;> rfl
public theorem queueExp_bounds (n : ℕ) (z : S) :
    0 ≤ queueExp rate rewards C_star C_h a n z ∧
      queueExp rate rewards C_star C_h a n z ≤
        Real.exp (beta * (2 * (1 / (32 * rate.eta.val)))) := by
  cases hp : P rate rewards C_star C_h n z with
  | none => simp only [queueExp, hp]; exact ⟨le_rfl, Real.exp_nonneg _⟩
  | some r =>
      simp only [queueExp, hp]
      have hb := ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.prefixReadout_backlog_bounds
        rate rewards C_star C_h n z r hp a
      exact ⟨Real.exp_nonneg _, Real.exp_le_exp_of_le (mul_le_mul_of_nonneg_left hb.2
        (CanonicalRecordingRates.beta_pos p rate.eta.property).le)⟩
public theorem W_measurable : Measurable[F] (W rate rewards C_star C_h q a) := by
  have hm := (measurable_queueExp_projection rate a).comp
    (P_measurable rate rewards C_star C_h control0 q)
  exact hm.indicator (measurableSet_B rate rewards C_star C_h control0 q)
public theorem energy_integrable (control0 : TimeControl p) :
    Integrable (W rate rewards C_star C_h q a) mu ∧
      Integrable (Xplus rate rewards C_star C_h q a) mu := by
  have hB := (sourcePrefixFiltration control0).le' (q.val + 1) _
    (measurableSet_B rate rewards C_star C_h control0 q)
  have hi (n : ℕ) : Integrable (queueExp rate rewards C_star C_h a n) mu := by
    have hP := ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.measurable_prefixReadout
      rate rewards C_star C_h n
    have hm := (measurable_queueExp_projection rate a).comp
      (hP.mono le_rfl (show optionMeasurableSpace ≤ ⊤ from le_top))
    apply integrable_bounded (f := queueExp rate rewards C_star C_h a n)
      hm
      (Real.exp (beta * (2 * (1 / (32 * rate.eta.val)))))
    intro z
    rw [Real.norm_eq_abs, abs_of_nonneg (queueExp_bounds rate rewards C_star C_h a n z).1]
    exact (queueExp_bounds rate rewards C_star C_h a n z).2
  exact ⟨(hi q.val).indicator hB, (hi (q.val + 1)).indicator hB⟩
public theorem Xplus_le_W_mul_expX_add_gate (z : S) :
    Xplus rate rewards C_star C_h q a z ≤ W rate rewards C_star C_h q a z *
      expX rate rewards C_star C_h q a z +
        (G rate rewards C_star C_h q).indicator (fun _ => (1 : ℝ)) z := by
  by_cases hb : z ∈ B rate rewards C_star C_h q
  · obtain ⟨before, after, hbefore, hafter, hstep⟩ :=
      presentPrefix_queue_step rate rewards C_star C_h q a z hb
    by_cases hg : z ∈ G rate rewards C_star C_h q
    · simp only [ite_eq_left hg] at hstep
      simpa only [Xplus, W, queueExp, expX, Set.indicator_of_mem hb,
        Set.indicator_of_mem hg, hbefore, hafter, Option.elim_some, hstep, add_comm] using
        CanonicalQueueProcess.exp_mul_max_le
          (((before.1 a).2 : ℝ) / ((Q).n : ℝ)) (x rate rewards C_star C_h q a z) beta
    · simp only [ite_eq_right hg] at hstep
      simp only [Xplus, W, queueExp, expX, x, Set.indicator_of_mem hb,
        Set.indicator_of_notMem hg, hbefore, hafter, Option.elim_some, hstep, mul_zero,
        Real.exp_zero, mul_one, add_zero, le_refl]
  · have hg : z ∉ G rate rewards C_star C_h q := fun h => hb h.1.1
    simp only [Xplus, W, Set.indicator_of_notMem hb, Set.indicator_of_notMem hg,
      zero_mul, add_zero, le_refl]
private theorem payload_exponential_bound
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (state : RecordedQueueRun.RunState p.K) (hclear : state.overflow = false) :
    let A := QuantizedRecordingMoments.quantizedValue (ConstructorDimensions.D p)
      rate.eta.val (payload.rate a)
      (ReferenceFirstCollectionOldRecorderFoundation.roundedReward rewards q a)
    Real.exp (beta * (A - 4)) * payload.rate a +
      Real.exp (beta * (-4)) * (1 - payload.rate a) ≤ 1 := by
  let rates := SnapshotRecordingKernel.recordingRates p rate.eta.val rate.eta.property
    rate.sourceCap payload.anchor payload.anchor_pos
  let reward := ReferenceFirstCollectionOldRecorderFoundation.roundedReward rewards q
  have hr := ReferenceFirstCollectionOldRecorderFoundation.roundedReward_bounds rewards q
  have hmgf := RecordedRoundMoments.rawEstimate_exponentialMoment_le_one Q state rates
    reward hr a hclear beta (CanonicalRecordingRates.beta_pos p rate.eta.property)
    (payload.beta_le_rate a)
  have hraw (o : Option (Fin p.K)) :=
    RecordedRoundMoments.rawEstimate_eq_quantizedValue_of_enabled
      Q state rates reward hr o a hclear
  simp_rw [hraw] at hmgf
  rw [PMF.integral_eq_sum] at hmgf
  simp only [RecordedRoundMoments.recordingOutcomePMF, PMF.ofFintype_apply,
    RecordedRoundMoments.outcomeMass, Fintype.sum_option, smul_eq_mul] at hmgf
  simp only [ENNReal.toReal_ofReal (rates.none_mass_nonneg),
    ENNReal.toReal_ofReal (rates.rate_nonneg _)] at hmgf
  let A := QuantizedRecordingMoments.quantizedValue (ConstructorDimensions.D p)
    rate.eta.val (payload.rate a) (reward a)
  let d := Real.exp (beta * (-4))
  let e := Real.exp (beta * (A - 4))
  simp only [reduceCtorEq, ite_false, zero_sub] at hmgf
  change (1 - ∑ j, payload.rate j) * d +
    ∑ j, payload.rate j * Real.exp (beta * ((if some j = some a then A else 0) - 4)) ≤ 1 at hmgf
  have hs : (∑ j, payload.rate j * Real.exp (beta * ((if some j = some a then A else 0) - 4))) =
      d * (∑ j, payload.rate j) + (e - d) * payload.rate a := by
    calc
      _ = ∑ j, (d * payload.rate j + if j = a then (e - d) * payload.rate j else 0) := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases hj : j = a <;> simp [hj, d, e] <;> ring
      _ = _ := by rw [Finset.sum_add_distrib]; simp [Finset.mul_sum]
  rw [hs] at hmgf
  dsimp only
  change e * payload.rate a + d * (1 - payload.rate a) ≤ 1
  linarith only [hmgf]
private theorem expX_bounds (z : S) : 0 ≤ expX rate rewards C_star C_h q a z ∧
    expX rate rewards C_star C_h q a z ≤ Real.exp 1 := by
  refine ⟨Real.exp_nonneg _, ?_⟩
  apply Real.exp_le_exp_of_le
  by_cases hg : z ∈ G rate rewards C_star C_h q
  · have hr := ReferenceFirstCollectionOldRecorderFoundation.oldRaw_bounds
      rate rewards C_star C_h q a z
    have hb := CanonicalRecordingRates.beta_pos p rate.eta.property
    have hm := mul_le_mul_of_nonneg_left hr.2 hb.le
    have hh : beta * (1 / beta) = 1 := by field_simp [ne_of_gt hb]
    simp only [x, Set.indicator_of_mem hg]
    nlinarith only [hm, hh, hb]
  · simp only [x, Set.indicator_of_notMem hg, mul_zero]; norm_num
public theorem expX_integrable (control0 : TimeControl p) :
    Integrable (expX rate rewards C_star C_h q a) mu := by
  have hGa := (sourcePrefixFiltration control0).le' (q.val + 1) _
    (measurableSet_G rate rewards C_star C_h control0 q)
  have hm : Measurable (expX rate rewards C_star C_h q a) :=
    (measurable_const.mul (((ReferenceFirstCollectionOldRecorderFoundation.oldRaw_measurable
      rate rewards C_star C_h q a).sub_const 4).indicator hGa)).exp
  apply integrable_bounded hm (Real.exp 1)
  intro z
  rw [Real.norm_eq_abs, abs_of_nonneg (expX_bounds rate rewards C_star C_h q a z).1]
  exact (expX_bounds rate rewards C_star C_h q a z).2
public theorem condExp_expX_le_one :
    mu[expX rate rewards C_star C_h q a | F] ≤ᵐ[mu] (fun _ => (1 : ℝ))  := by
  let penalty := Real.exp (beta * (-4))
  let A := fun z => (ReferenceFirstCollectionOldRecorderFoundation.incomingAmplitude?
    rate rewards C_star C_h q a z).getD 0
  let jump := fun z => Real.exp (beta * (A z - 4)) - penalty
  let test := (D rate rewards C_star C_h q).indicator (fun z =>
    if oldMarker? rate rewards C_star C_h q z = some (some a) then (1 : ℝ) else 0)
  let gt := (G rate rewards C_star C_h q).indicator test
  let base := (G rate rewards C_star C_h q).indicator (fun _ => penalty) +
    (G rate rewards C_star C_h q)ᶜ.indicator (fun _ => (1 : ℝ))
  have hle := (sourcePrefixFiltration control0).le' (q.val + 1)
  have hG := measurableSet_G rate rewards C_star C_h control0 q
  have hGa := hle _ hG
  have hDa := hle _ (measurableSet_D rate rewards C_star C_h control0 q)
  have htestMeas : Measurable test :=
    (Measurable.ite ((measurableSet_singleton (some (some a))).preimage
      (oldMarker_measurable rate rewards C_star C_h q))
      measurable_const measurable_const).indicator hDa
  have htestInt : Integrable test mu := by
    apply integrable_bounded htestMeas 1
    intro z
    by_cases hd : z ∈ D rate rewards C_star C_h q <;>
      by_cases hm : oldMarker? rate rewards C_star C_h q z = some (some a) <;>
        simp [test, hd, hm]
  have hgtInt : Integrable gt mu := htestInt.indicator hGa
  have hbaseInt : Integrable base mu :=
    ((integrable_const penalty).indicator hGa).add ((integrable_const 1).indicator hGa.compl)
  have hbaseMeas : Measurable[F] base :=
    (measurable_const.indicator hG).add (measurable_const.indicator hG.compl)
  have hjump : Measurable[F] jump :=
    (((ReferenceFirstCollectionOldRecorderFoundation.incomingAmplitudeValue_measurable
      rate rewards C_star C_h control0 q a).sub_const 4).const_mul beta).exp.sub_const penalty
  have hexpInt := expX_integrable rate rewards C_star C_h q a control0
  have hdecomp : expX rate rewards C_star C_h q a = jump * gt + base := by
    funext z
    by_cases hg : z ∈ G rate rewards C_star C_h q
    · have hd := hg.1.1.1
      have hr := raw_amplitude_identity rate rewards C_star C_h q a z hd
      by_cases hm : oldMarker? rate rewards C_star C_h q z = some (some a) <;>
        simp [expX, x, jump, gt, test, base, A, hg, hd, hr, hm, penalty]
    · simp [expX, x, gt, base, hg]
  have hprodInt : Integrable (jump * gt) mu := by
    have heq : jump * gt = expX rate rewards C_star C_h q a - base := by
      rw [hdecomp]; exact (add_sub_cancel_right _ _).symm
    rw [heq]
    exact hexpInt.sub hbaseInt
  have hgtCE : mu[gt | F] =ᵐ[mu] (G rate rewards C_star C_h q).indicator
      (fun z => (incomingRates? rate rewards C_star C_h q z).getD (fun _ => 0) a) := by
    have hm := condExp_indicator (μ := mu) htestInt hG
    have hlaw := presentCell_marker_condExp rate rewards C_star C_h control0 q (some a)
    filter_upwards [hm, hlaw] with z hm hlaw
    by_cases hg : z ∈ G rate rewards C_star C_h q
    · have hd := hg.1.1.1
      have he := hg.2.2
      change incomingEnabled? rate rewards C_star C_h q z = some true at he
      have hh : mu[gt | F] z = mu[test | F] z := by simpa [gt, hg] using hm
      simpa [test, hg, hd, he] using hh.trans hlaw
    · simpa [gt, hg] using hm
  have hsum := condExp_add hprodInt hbaseInt F
  have hpull := condExp_mul_of_aestronglyMeasurable_left hjump.aestronglyMeasurable hprodInt hgtInt
  have hbaseCE := condExp_of_stronglyMeasurable hle hbaseMeas.stronglyMeasurable hbaseInt
  have hExp : mu[expX rate rewards C_star C_h q a | F] ≤ᵐ[mu] (fun _ => (1 : ℝ)) := by
    rw [hdecomp]
    filter_upwards [hsum, hpull, hgtCE] with z hs hp ht
    rw [hs]
    simp only [Pi.add_apply]
    rw [hp, hbaseCE]
    simp only [Pi.mul_apply]
    rw [ht]
    by_cases hg : z ∈ G rate rewards C_star C_h q
    · obtain ⟨L, cell, _hL, _hc, _hn, hbefore, _ha⟩ :=
        presentPrefix_append rate rewards C_star C_h q z hg.1.1
      obtain ⟨payload, c, hpay, _hc, _hr, _hm⟩ :=
        marker_snapshot rate rewards C_star C_h q z hg.1.1.1
      have hclear : (RecordedQueueRun.run Q L).overflow = false := by
        obtain ⟨o, ho, hf⟩ := hg.1.2
        rw [← P_eq_current rate rewards C_star C_h q z, hbefore] at ho
        exact (congrArg (fun r => r.2.1) (Option.some.inj ho)).trans hf
      have hb := payload_exponential_bound rate rewards q a payload (RecordedQueueRun.run Q L) hclear
      simp only [Set.indicator_of_mem hg, base, Pi.add_apply,
        Set.indicator_of_notMem (Set.notMem_compl_iff.mpr hg)]
      dsimp only [jump, A]
      simp only [ReferenceFirstCollectionOldRecorderFoundation.incomingAmplitude?,
        incomingRates?, hpay, Option.map_some, Option.getD_some]
      dsimp only at hb
      dsimp only [penalty]
      nlinarith only [hb]
    · simp [base, hg]
  exact hExp
public theorem x_off_gate (z : S) (hz : z ∉ G rate rewards C_star C_h q) :
    x rate rewards C_star C_h q a z = 0 := Set.indicator_of_notMem hz _
public theorem x_retained_zero_arrival (z : S) (hz : z ∈ G rate rewards C_star C_h q)
    (hzero : ReferenceFirstCollectionOldRecorderFoundation.oldRaw rate rewards C_star C_h q a z = 0) :
    x rate rewards C_star C_h q a z = -4 := by simp only [x, Set.indicator_of_mem hz, hzero, zero_sub]

/-- Weighted retained energy at an arbitrary original collection date. The
incoming factor is its inherited queue energy, including later installations. -/
public theorem retained_energy_step :
    mu[Xplus rate rewards C_star C_h q a | F] ≤ᵐ[mu]
      (fun z => W rate rewards C_star C_h q a z +
        (G rate rewards C_star C_h q).indicator (fun _ => (1 : ℝ)) z) ∧
    (∫ z, Xplus rate rewards C_star C_h q a z ∂mu) ≤
      (∫ z, W rate rewards C_star C_h q a z ∂mu) +
        ∫ z, (G rate rewards C_star C_h q).indicator (fun _ => (1 : ℝ)) z ∂mu := by
  let gate := (G rate rewards C_star C_h q).indicator (fun _ => (1 : ℝ))
  have hle := (sourcePrefixFiltration control0).le' (q.val + 1)
  have hG := measurableSet_G rate rewards C_star C_h control0 q
  obtain ⟨hWi, hXi⟩ := energy_integrable rate rewards C_star C_h q a control0
  have hEi := expX_integrable rate rewards C_star C_h q a control0
  have hgi : Integrable gate mu := (integrable_const 1).indicator (hle _ hG)
  have hpi : Integrable (W rate rewards C_star C_h q a * expX rate rewards C_star C_h q a) mu := by
    apply hWi.mul_bdd hEi.aestronglyMeasurable
    filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_of_nonneg (expX_bounds rate rewards C_star C_h q a z).1]
    exact (expX_bounds rate rewards C_star C_h q a z).2
  have hm := condExp_mono (m := F) hXi (hpi.add hgi)
    (Filter.Eventually.of_forall (Xplus_le_W_mul_expX_add_gate rate rewards C_star C_h q a))
  have hs := condExp_add hpi hgi F
  have hp := condExp_mul_of_aestronglyMeasurable_left
    (W_measurable rate rewards C_star C_h control0 q a).aestronglyMeasurable hpi hEi
  have hgCE : mu[gate | F] = gate := condExp_of_stronglyMeasurable hle
    (measurable_const.indicator hG).stronglyMeasurable hgi
  have hCE : mu[Xplus rate rewards C_star C_h q a | F] ≤ᵐ[mu]
      (fun z => W rate rewards C_star C_h q a z + gate z) := by
    filter_upwards [hm, hs, hp, condExp_expX_le_one rate rewards C_star C_h control0 q a]
      with z hm hs hp he
    simp only [Pi.add_apply, Pi.mul_apply] at hm hs hp
    rw [hs, hp, hgCE] at hm
    have hw : 0 ≤ W rate rewards C_star C_h q a z := by
      by_cases hz : z ∈ B rate rewards C_star C_h q
      · simpa only [W, Set.indicator_of_mem hz] using
          (queueExp_bounds rate rewards C_star C_h a q.val z).1
      · simp only [W, Set.indicator_of_notMem hz, le_refl]
    exact hm.trans (add_le_add (by simpa using mul_le_mul_of_nonneg_left he hw) le_rfl)
  refine ⟨hCE, ?_⟩
  have hi := integral_mono_ae integrable_condExp (hWi.add hgi) hCE
  rw [integral_condExp hle] at hi
  calc
    _ ≤ ∫ z, W rate rewards C_star C_h q a z + gate z ∂mu := hi
    _ = _ := integral_add hWi hgi
end Bandits.Support.ReferenceOriginalCalendarCollectionRetainedEnergyStep
end
