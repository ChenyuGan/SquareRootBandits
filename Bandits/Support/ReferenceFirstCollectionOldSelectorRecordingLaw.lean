/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionOldRecorderFoundation

/-!
# Original OLD selector and local recording laws

Sources: `sources/zip4/manuscript/04_slow_fast_learner.tex:140-188,245-284`,
`05_binary_transport.tex:352-431`, and `06_interruptions.tex:35-100,355-426`.
All readouts are the accepted foundation's literal original-source readouts.
The complete selector is stable under every fresh whole control and factors
through the strict prefix. The same incoming snapshot gives exact arm/bottom
control integrals and original-source conditional expectations, including
disabled present bottom and separate outer absence. The localized raw CE uses
the same predictable floor amplitude and actual incoming rate.
The consumer is OldCalendarExponentialStep after PrecallCalendarSupport.
These internal laws assert no calendar coverage or manuscript closure.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped Classical BigOperators

namespace Bandits.Support.ReferenceFirstCollectionOldSelectorRecordingLaw

open ConstructorDimensions (Parameters D D_pos)
open ReferenceActivePhysicalStep (RateInput Payload)
open ActualInitializationPhysicalStep (GridRewardTable)
open BootstrapPrivateRoundStreams (SourceInput sourceInputLaw)
open ContinuousLearningRows (TimeControl)
open ReferenceSourcePrefixHistoryFiltration
  (actualRecord incoming sourcePrefix sourcePrefixFiltration)
open ReferenceFirstCollectionOldRecorderFoundation

variable {p : Parameters}

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
          armChoice_eq := by
            simpa only [hcutoff] using hselected }
        have hgrid := CoordinatorPhaseClock.clockRegistersValid_gridDomain
          p y.etaReal y.clock hc.clock_registers_valid
        simp only [CoordinatorPhaseClock.clockGridDomain, hc.clock_sigma_eq] at hgrid
        have hb : snap.clockStarted.clock.g ≤ p.T + 1 := by
          rw [snap.clockStarted_frame.1]
          exact hgrid.2
        exact ⟨hc, snap, hb, hs, rfl, rfl⟩
    · rename_i hbad
      exact False.elim (hbad hchoice)

private theorem dispatch_domain_otherInput
    (rate : RateInput p) (x y : ReferenceActivePhysicalStep.RoundInput p rate)
    (hstate : x.state = y.state) (htime : x.time = y.time)
    (hx : match ReferenceActivePhysicalStep.dispatch x with
      | .collection _ _ _ _ (.continuing _ _ _ _) => True
      | .live registers _ _ (.cutoffChosen _ _ _ _ _ _ _ _ _ _) =>
          0 < registers.payload.sigma.val
      | _ => False) :
    match ReferenceActivePhysicalStep.dispatch y with
      | .collection _ _ _ _ (.continuing _ _ _ _) => True
      | .live registers _ _ (.cutoffChosen _ _ _ _ _ _ _ _ _ _) =>
          0 < registers.payload.sigma.val
      | _ => False := by
  rcases x with ⟨state, rows, selected, time, active, rewards⟩
  rcases y with ⟨otherState, otherRows, otherSelected, otherTime, otherActive, otherRewards⟩
  dsimp only at hstate htime
  cases hstate
  cases htime
  let x : ReferenceActivePhysicalStep.RoundInput p rate :=
    ⟨state, rows, selected, time, active, rewards⟩
  let y : ReferenceActivePhysicalStep.RoundInput p rate :=
    ⟨state, otherRows, otherSelected, time, active, otherRewards⟩
  change (match ReferenceActivePhysicalStep.dispatch x with
    | .collection _ _ _ _ (.continuing _ _ _ _) => True
    | .live registers _ _ (.cutoffChosen _ _ _ _ _ _ _ _ _ _) =>
        0 < registers.payload.sigma.val
    | _ => False) at hx
  change (match ReferenceActivePhysicalStep.dispatch y with
    | .collection _ _ _ _ (.continuing _ _ _ _) => True
    | .live registers _ _ (.cutoffChosen _ _ _ _ _ _ _ _ _ _) =>
        0 < registers.payload.sigma.val
    | _ => False)
  cases hs : x.state.coordinator with
  | first =>
      simp only [ReferenceActivePhysicalStep.dispatch, hs,
        CoordinatorRoundDispatch.dispatch] at hx
      cases CoordinatorRoundDispatch.dispatchFirst (ReferenceActivePhysicalStep.firstInput x) <;>
        contradiction
  | dagger =>
      simp only [ReferenceActivePhysicalStep.dispatch, hs] at hx
  | live registers owned base =>
      have hs' : y.state.coordinator = .live registers owned base := hs
      have hdx : ReferenceActivePhysicalStep.dispatch x = .live registers owned base
          (CoordinatorRoundDispatch.dispatchLive
            (ReferenceActivePhysicalStep.liveInput x registers owned base)) := by
        simp only [ReferenceActivePhysicalStep.dispatch, hs, CoordinatorRoundDispatch.dispatch]
        rfl
      have hdy : ReferenceActivePhysicalStep.dispatch y = .live registers owned base
          (CoordinatorRoundDispatch.dispatchLive
            (ReferenceActivePhysicalStep.liveInput y registers owned base)) := by
        simp only [ReferenceActivePhysicalStep.dispatch, hs', CoordinatorRoundDispatch.dispatch]
        rfl
      rw [hdx] at hx
      rw [hdy]
      have hinput : ReferenceActivePhysicalStep.liveInput y registers owned base =
          {ReferenceActivePhysicalStep.liveInput x registers owned base with row := y.row} := rfl
      have htag := liveCutoffTag_otherRow
        (ReferenceActivePhysicalStep.liveInput x registers owned base) y.row
      rw [← hinput] at htag
      cases ho : CoordinatorRoundDispatch.dispatchLive
          (ReferenceActivePhysicalStep.liveInput x registers owned base) <;>
        simp only [ho] at hx
      all_goals
        cases ho' : CoordinatorRoundDispatch.dispatchLive
            (ReferenceActivePhysicalStep.liveInput y registers owned base) <;>
          simp only [ho, ho', ReferenceLiveDispatchOutputMeasurability.outcomeData,
            cutoffDataTag, Bool.false_eq_true] at htag
      all_goals simpa only [ho'] using hx
  | collection payload ledger proposal =>
      have hs' : y.state.coordinator = .collection payload ledger proposal := hs
      by_cases hcut : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
      · let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
        let clock := ReferenceActivePhysicalStep.collectionClock payload ledger proposal cutoff
        have hdx : ReferenceActivePhysicalStep.dispatch x = .collection payload ledger clock cutoff
            (CoordinatorRoundDispatch.dispatchCollection
              (ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff)) := by
          simp only [ReferenceActivePhysicalStep.dispatch, hs, dite_eq_left hcut,
            CoordinatorRoundDispatch.dispatch]
          rfl
        have hdy : ReferenceActivePhysicalStep.dispatch y = .collection payload ledger clock cutoff
            (CoordinatorRoundDispatch.dispatchCollection
              (ReferenceActivePhysicalStep.collectionInput y payload ledger clock cutoff)) := by
          simp only [ReferenceActivePhysicalStep.dispatch, hs', dite_eq_left hcut,
            CoordinatorRoundDispatch.dispatch]
          rfl
        rw [hdx] at hx
        rw [hdy]
        have hinput : ReferenceActivePhysicalStep.collectionInput y payload ledger clock cutoff =
            {ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff with
              row := y.row} := rfl
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

variable (rate : RateInput p) (rewards : GridRewardTable p) (C_star C_h : ℝ)

/-- Every whole fresh control preserves presence on the original OLD selector.
No success, future endpoint, or almost-everywhere restriction is imposed. -/
theorem oldSelector_replaceCurrent_forward (control0 : TimeControl p)
    (r : Fin p.T) (z : SourceInput p)
    (hz : z ∈ oldSelector rate rewards C_star C_h r) (fresh : TimeControl p) :
    ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p r z fresh ∈
      oldSelector rate rewards C_star C_h r := by
  obtain ⟨record, replacement, hr, hr', hstate, hfollowers⟩ :=
    oldSelector_followers_replaceCurrent rate rewards C_star C_h control0 r z hz fresh
  have hread : (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 record).isSome =
      true := by
    have h := hz.2
    change (oldCell? rate rewards C_star C_h r z).isSome = true at h
    simpa only [oldCell?, hr, Option.bind_some] using h
  obtain ⟨hunoccupied, hcoord⟩ :=
    (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout_domain 0 record).mp hread
  have hunoccupied' :
      ReferenceLaterCollectionArrivalReadout.preparedFollowersUnoccupied replacement := by
    intro i
    change (match (replacement.output.preparation.followers.followers i).configuration with
      | .ordinary state _ => state.status = .unoccupied
      | .dagger => False)
    rw [hfollowers]
    exact hunoccupied i
  have hf := ReferenceCalendarLaterSamplerOutputSections.actualRecord_fields
    rate rewards C_star C_h r z record hr
  have hf' := ReferenceCalendarLaterSamplerOutputSections.actualRecord_fields
    rate rewards C_star C_h r _ replacement hr'
  have hcoord' := dispatch_domain_otherInput rate record.input replacement.input hstate
    (hf.2.2.1.trans hf'.2.2.1.symm)
    (by
      rw [record.output.preparation.coordinator_eq] at hcoord
      cases hd : ReferenceActivePhysicalStep.dispatch record.input with
      | first out => cases out <;> simp_all only
      | live registers owned base out => cases out <;> simp_all only
      | collection payload ledger clock cutoff out => cases out <;> simp_all only
      | dagger => simp_all only
      | invalidCollectionCutoff => simp_all only)
  refine ⟨(beforeCall_replaceCurrent rate rewards C_star C_h control0 r z fresh).mpr hz.1, ?_⟩
  change (oldCell? rate rewards C_star C_h r _).isSome = true
  simp only [oldCell?, hr', Option.bind_some]
  apply (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout_domain 0 replacement).mpr
  exact ⟨hunoccupied', by
    rw [replacement.output.preparation.coordinator_eq]
    cases hd : ReferenceActivePhysicalStep.dispatch replacement.input with
    | first out => cases out <;> simp_all only
    | live registers owned base out => cases out <;> simp_all only
    | collection payload ledger clock cutoff out => cases out <;> simp_all only
    | dagger => simp_all only
    | invalidCollectionCutoff => simp_all only⟩

/-- Whole-control replacement preserves the complete selector in both directions. -/
theorem oldSelector_replaceCurrent (control0 : TimeControl p) (r : Fin p.T)
    (z : SourceInput p) (fresh : TimeControl p) :
    ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p r z fresh ∈
        oldSelector rate rewards C_star C_h r ↔
      z ∈ oldSelector rate rewards C_star C_h r := by
  constructor
  · intro hz
    have h := oldSelector_replaceCurrent_forward rate rewards C_star C_h control0 r
      _ hz (ReferenceSourceCurrentControlFreshness.u_t p r z)
    have hrestore : ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p r
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p r z fresh)
        (ReferenceSourceCurrentControlFreshness.u_t p r z) = z := by
      simp only [ReferenceFixedTimeSourceControlCoupling.replaceSourceControl,
        ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex,
        ReferenceSourceCurrentControlFreshness.u_t,
        ActualInitializationPhysicalStep.selectedRowIndex, Function.update_self,
        Function.update_idem, Function.update_eq_self]
    rwa [hrestore] at h
  · exact fun hz => oldSelector_replaceCurrent_forward rate rewards C_star C_h control0 r z hz fresh

private theorem prepare_configuration_eq_of_current
    (x y : ReferenceActivePhysicalStep.RoundInput p rate)
    (hstate : x.state = y.state) (htime : x.time = y.time)
    (hcurrent : x.row.2 x.time = y.row.2 y.time) (i : Fin (p.m - 1)) :
    ((ReferenceActivePhysicalStep.prepare x).followers.followers i).configuration =
      ((ReferenceActivePhysicalStep.prepare y).followers.followers i).configuration := by
  rcases x with ⟨state, rows, selected, time, active, rewards⟩
  rcases y with ⟨otherState, otherRows, otherSelected, otherTime, otherActive, otherRewards⟩
  dsimp only at hstate htime
  cases hstate
  cases htime
  exact congrArg Prod.snd
    (ReferenceActiveTemporalCausality.prepare_projections_eq_of_current
      i (state.activations i) (active i) (state.followers i) hcurrent)

private theorem oldSelector_transport_current (r : Fin p.T) (z z' : SourceInput p)
    (hz : z ∈ oldSelector rate rewards C_star C_h r)
    (hin : incoming rate rewards C_star C_h r z = incoming rate rewards C_star C_h r z')
    (hcurrent : ReferenceSourceCurrentControlFreshness.u_t p r z =
      ReferenceSourceCurrentControlFreshness.u_t p r z')
    (hbefore : z' ∈ beforeCall rate rewards C_star C_h r) :
    z' ∈ oldSelector rate rewards C_star C_h r := by
  obtain ⟨cell, hcell⟩ := Option.isSome_iff_exists.mp hz.2
  obtain ⟨record, hr, hread⟩ := Option.bind_eq_some_iff.mp hcell
  cases hr' : actualRecord rate rewards C_star C_h r z' with
  | none =>
      simp only [incoming, hr, hr', Option.map_some, Option.map_none] at hin
      cases hin
  | some replacement =>
      have hstate : record.input.state = replacement.input.state :=
        ReferenceActivePhysicalStepMeasurability.encodeState_injective
          (Option.some.inj (by simpa only [incoming, hr, hr', Option.map_some] using hin))
      have hf := ReferenceCalendarLaterSamplerOutputSections.actualRecord_fields
        rate rewards C_star C_h r z record hr
      have hf' := ReferenceCalendarLaterSamplerOutputSections.actualRecord_fields
        rate rewards C_star C_h r z' replacement hr'
      have htime := hf.2.2.1.trans hf'.2.2.1.symm
      have hc : record.input.row.2 record.input.time =
          replacement.input.row.2 replacement.input.time := by
        simpa only [ReferenceActivePhysicalStep.RoundInput.row, hf.1, hf.2.1, hf.2.2.1,
          hf'.1, hf'.2.1, hf'.2.2.1, ReferenceSourceCurrentControlFreshness.u_t] using hcurrent
      have hconfig (i : Fin (p.m - 1)) :
          (record.output.preparation.followers.followers i).configuration =
            (replacement.output.preparation.followers.followers i).configuration := by
        have hprep : record.output.preparation = ReferenceActivePhysicalStep.prepare record.input := by
          rw [record.output_eq]; rfl
        have hprep' : replacement.output.preparation =
            ReferenceActivePhysicalStep.prepare replacement.input := by
          rw [replacement.output_eq]; rfl
        rw [hprep, hprep']
        exact prepare_configuration_eq_of_current rate record.input replacement.input
          hstate htime hc i
      have hsome : (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 record).isSome =
          true := by rw [hread]; rfl
      obtain ⟨hfollowers, hcoord⟩ :=
        (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout_domain 0 record).mp hsome
      have hfollowers' :
          ReferenceLaterCollectionArrivalReadout.preparedFollowersUnoccupied replacement := by
        intro i
        change (match (replacement.output.preparation.followers.followers i).configuration with
          | .ordinary state _ => state.status = .unoccupied
          | .dagger => False)
        rw [← hconfig]
        exact hfollowers i
      have hdispatch := dispatch_domain_otherInput rate record.input replacement.input hstate htime
        (by
          rw [record.output.preparation.coordinator_eq] at hcoord
          cases hd : ReferenceActivePhysicalStep.dispatch record.input with
          | first out => cases out <;> simp_all only
          | live registers owned base out => cases out <;> simp_all only
          | collection payload ledger clock cutoff out => cases out <;> simp_all only
          | dagger => simp_all only
          | invalidCollectionCutoff => simp_all only)
      refine ⟨hbefore, ?_⟩
      change (oldCell? rate rewards C_star C_h r z').isSome = true
      simp only [oldCell?, hr', Option.bind_some]
      apply (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout_domain 0 replacement).mpr
      refine ⟨hfollowers', ?_⟩
      rw [replacement.output.preparation.coordinator_eq]
      cases hd : ReferenceActivePhysicalStep.dispatch replacement.input with
      | first out => cases out <;> simp_all only
      | live registers owned base out => cases out <;> simp_all only
      | collection payload ledger clock cutoff out => cases out <;> simp_all only
      | dagger => simp_all only
      | invalidCollectionCutoff => simp_all only

/-- The no-invocation test factors through the same strict source prefix. -/
theorem beforeCall_factor (control0 : TimeControl p) (r : Fin p.T) (z : SourceInput p) :
    z ∈ beforeCall rate rewards C_star C_h r ↔
      sourcePrefix control0 r.val z ∈ beforeCall rate rewards C_star C_h r := by
  have hcall (v : Fin p.T) (hv : v.val ≤ r.val) :
      ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h v z =
        ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h v
          (sourcePrefix control0 r.val z) := by
    rw [ReferenceCalendarCollectionCallControlLaw.callAt_factor
      rate rewards C_star C_h control0 v z,
      ReferenceCalendarCollectionCallControlLaw.callAt_factor
        rate rewards C_star C_h control0 v (sourcePrefix control0 r.val z),
      ReferenceSourcePrefixHistoryFiltration.sourcePrefix_sourcePrefix control0 v.val r.val hv]
  constructor <;> intro hz v hv
  · rw [← hcall v hv]; exact hz v hv
  · rw [hcall v hv]; exact hz v hv

/-- The complete original OLD selector uses no current control or future endpoint. -/
theorem oldSelector_factor (control0 : TimeControl p) (r : Fin p.T) (z : SourceInput p) :
    z ∈ oldSelector rate rewards C_star C_h r ↔
      sourcePrefix control0 r.val z ∈ oldSelector rate rewards C_star C_h r := by
  let z0 := ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p r z control0
  let zp := sourcePrefix control0 r.val z
  have hin : incoming rate rewards C_star C_h r z0 = incoming rate rewards C_star C_h r zp := by
    rw [ReferenceSourcePrefixHistoryFiltration.incoming_factor rate rewards C_star C_h control0 r z0]
    dsimp only [z0, zp]
    rw [sourcePrefix_replaceCurrent control0 r r.val le_rfl]
  have hc : ReferenceSourceCurrentControlFreshness.u_t p r z0 =
      ReferenceSourceCurrentControlFreshness.u_t p r zp := by
    simp only [z0, zp, ReferenceSourceCurrentControlFreshness.u_t,
      ReferenceFixedTimeSourceControlCoupling.replaceSourceControl,
      ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex,
      ActualInitializationPhysicalStep.selectedRowIndex, sourcePrefix,
      Function.update_self, lt_self_iff_false, ite_false]
  constructor
  · intro hz
    have hz0 := (oldSelector_replaceCurrent rate rewards C_star C_h control0 r z control0).mpr hz
    exact oldSelector_transport_current rate rewards C_star C_h r z0 zp hz0 hin hc
      ((beforeCall_factor rate rewards C_star C_h control0 r z).mp hz.1)
  · intro hz
    have hbefore : z0 ∈ beforeCall rate rewards C_star C_h r :=
      (beforeCall_replaceCurrent rate rewards C_star C_h control0 r z control0).mpr
        ((beforeCall_factor rate rewards C_star C_h control0 r z).mpr hz.1)
    exact (oldSelector_replaceCurrent rate rewards C_star C_h control0 r z control0).mp
      (oldSelector_transport_current rate rewards C_star C_h r zp z0 hz hin.symm hc.symm hbefore)

/-- Predictability in the original pre-choice filtration, with no supplied law. -/
theorem oldSelector_measurable (control0 : TimeControl p) (r : Fin p.T) :
    MeasurableSet[sourcePrefixFiltration control0 (r.val + 1)]
      (oldSelector rate rewards C_star C_h r) := by
  rw [ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration_succ]
  have hm := (comap_measurable (sourcePrefix control0 r.val))
    (oldSelector_measurable_ambient rate rewards C_star C_h control0 r)
  have heq : sourcePrefix control0 r.val ⁻¹' oldSelector rate rewards C_star C_h r =
      oldSelector rate rewards C_star C_h r := by
    ext z
    exact (oldSelector_factor rate rewards C_star C_h control0 r z).symm
  rwa [heq] at hm

/-- The SAME incoming snapshot describes the marker under every complete fresh
control, including disabled snapshots and every zero floor. -/
theorem oldMarker_fresh_recordingMap (control0 : TimeControl p) (r : Fin p.T)
    (z : SourceInput p) (hz : z ∈ oldSelector rate rewards C_star C_h r) :
    ∃ (payload : Payload rate) (c : RecordedQueueRun.RoundInput p.K),
      incomingPayload? rate rewards C_star C_h r z = some payload ∧
      oldCell? rate rewards C_star C_h r z = some c ∧
      c.rate = payload.rate ∧
      ∀ fresh : TimeControl p,
        oldMarker? rate rewards C_star C_h r
            (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p r z fresh) =
          some (SnapshotRecordingKernel.recordingMap p .collection c.enabled
            rate.eta.val rate.eta.property rate.sourceCap payload.anchor payload.anchor
            payload.anchor_pos payload.anchor_pos (fun _ => le_rfl)
            (fun a => by linarith [payload.anchor_pos a]) fresh.1) := by
  obtain ⟨payload, c, hp, hc, hrate, _hm⟩ :=
    oldCell_recordingMap rate rewards C_star C_h r z hz
  refine ⟨payload, c, hp, hc, hrate, ?_⟩
  intro fresh
  have hz' := oldSelector_replaceCurrent_forward rate rewards C_star C_h control0 r z hz fresh
  obtain ⟨payload', c', hp', hc', _hrate', hm'⟩ :=
    oldCell_recordingMap rate rewards C_star C_h r _ hz'
  have hpay : payload' = payload := Option.some.inj
    (hp'.symm.trans ((incomingPayload_replaceCurrent
      rate rewards C_star C_h control0 r z fresh).trans hp))
  subst payload'
  have he : c'.enabled = c.enabled := Option.some.inj
    ((oldCell_enabled_eq_incoming rate rewards C_star C_h r _ c' hc').symm.trans
      ((incomingEnabled_replaceCurrent rate rewards C_star C_h control0 r z fresh).trans
        (oldCell_enabled_eq_incoming rate rewards C_star C_h r z c hc)))
  rw [he] at hm'
  simpa only [ReferenceSourceCurrentControlFreshness.u_t,
    ReferenceFixedTimeSourceControlCoupling.replaceSourceControl,
    ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex,
    ActualInitializationPhysicalStep.selectedRowIndex, Function.update_self] using hm'

/-- The enabled snapshot's complete-control pushforward is the accepted
recording PMF. This includes the bottom atom without event normalization. -/
theorem collection_recordingMap_control_law (payload : Payload rate) :
    (ContinuousLearningRows.timeControlLaw p).map
      (fun fresh : TimeControl p => SnapshotRecordingKernel.recordingMap p .collection true
        rate.eta.val rate.eta.property rate.sourceCap payload.anchor payload.anchor
        payload.anchor_pos payload.anchor_pos (fun _ => le_rfl)
        (fun a => by linarith [payload.anchor_pos a]) fresh.1) =
      (RecordedRoundMoments.recordingOutcomePMF
        (SnapshotRecordingKernel.recordingRates p rate.eta.val rate.eta.property
          rate.sourceCap payload.anchor payload.anchor_pos)).toMeasure := by
  let f := SnapshotRecordingKernel.recordingMap p .collection true rate.eta.val
    rate.eta.property rate.sourceCap payload.anchor payload.anchor payload.anchor_pos
    payload.anchor_pos (fun _ => le_rfl) (fun a => by linarith [payload.anchor_pos a])
  have hf : Measurable f := SnapshotRecordingKernel.measurable_recordingMap p .collection
    rate.eta.val rate.eta.property rate.sourceCap payload.anchor payload.anchor
    payload.anchor_pos payload.anchor_pos (fun _ => le_rfl)
    (fun a => by linarith [payload.anchor_pos a]) true
  calc
    _ = ((ContinuousLearningRows.timeControlLaw p).map
        (Prod.fst : TimeControl p → ContinuousLearningRows.Slice p)).map f :=
      (Measure.map_map hf measurable_fst).symm
    _ = _ := by
      rw [ContinuousLearningRows.map_slice p]
      exact SnapshotRecordingKernel.map_recordingMap p .collection rate.eta.val
        rate.eta.property rate.sourceCap payload.anchor payload.anchor payload.anchor_pos
        payload.anchor_pos (fun _ => le_rfl) (fun a => by linarith [payload.anchor_pos a])


/-- Every enabled arm and bottom indicator has its exact whole-control integral. -/
theorem collection_recordingMap_control_integral (payload : Payload rate)
    (o : Option (Fin p.K)) :
    (∫ fresh : TimeControl p,
      (if SnapshotRecordingKernel.recordingMap p .collection true
        rate.eta.val rate.eta.property rate.sourceCap payload.anchor payload.anchor
        payload.anchor_pos payload.anchor_pos (fun _ => le_rfl)
        (fun a => by linarith [payload.anchor_pos a]) fresh.1 = o
        then (1 : ℝ) else 0) ∂ContinuousLearningRows.timeControlLaw p) =
      match o with
      | some a => payload.rate a
      | none => 1 - ∑ a, payload.rate a := by
  let f := fun fresh : TimeControl p => SnapshotRecordingKernel.recordingMap p .collection true
    rate.eta.val rate.eta.property rate.sourceCap payload.anchor payload.anchor
    payload.anchor_pos payload.anchor_pos (fun _ => le_rfl)
    (fun a => by linarith [payload.anchor_pos a]) fresh.1
  have hf : Measurable f :=
    (SnapshotRecordingKernel.measurable_recordingMap p .collection rate.eta.val
      rate.eta.property rate.sourceCap payload.anchor payload.anchor payload.anchor_pos
      payload.anchor_pos (fun _ => le_rfl)
      (fun a => by linarith [payload.anchor_pos a]) true).comp measurable_fst
  let rates := SnapshotRecordingKernel.recordingRates p rate.eta.val rate.eta.property
    rate.sourceCap payload.anchor payload.anchor_pos
  have hmass : (ContinuousLearningRows.timeControlLaw p) {fresh | f fresh = o} =
      RecordedRoundMoments.recordingOutcomePMF rates o := by
    have h := congrArg (fun ν : Measure (Option (Fin p.K)) => ν {o})
      (collection_recordingMap_control_law rate payload)
    rw [Measure.map_apply hf (measurableSet_singleton o),
      PMF.toMeasure_apply_singleton _ o (measurableSet_singleton o)] at h
    exact h
  have hs : MeasurableSet {fresh | f fresh = o} := hf (measurableSet_singleton o)
  have hi : (∫ fresh, (if f fresh = o then (1 : ℝ) else 0)
      ∂ContinuousLearningRows.timeControlLaw p) =
      (ContinuousLearningRows.timeControlLaw p).real {fresh | f fresh = o} := by
    simpa only [Set.indicator_apply, Set.mem_ofPred_eq, smul_eq_mul, mul_one] using
      integral_indicator_const (μ := ContinuousLearningRows.timeControlLaw p) (1 : ℝ) hs
  change (∫ fresh, (if f fresh = o then (1 : ℝ) else 0)
    ∂ContinuousLearningRows.timeControlLaw p) = _
  rw [hi, measureReal_def, hmass]
  cases o with
  | some a =>
      rw [RecordedRoundMoments.recordingOutcomePMF_some,
        ENNReal.toReal_ofReal (rates.rate_pos a).le]
      rfl
  | none =>
      rw [RecordedRoundMoments.recordingOutcomePMF_none,
        ENNReal.toReal_ofReal (sub_nonneg.mpr rates.rate_sum_le_one)]
      rfl

/-- Original localized arm/bottom mass under arbitrary fresh complete controls.
The disabled present cell is bottom with mass one; outer absence stays separate. -/
theorem oldMarker_control_integral (control0 : TimeControl p) (r : Fin p.T)
    (z : SourceInput p) (hz : z ∈ oldSelector rate rewards C_star C_h r)
    (o : Option (Fin p.K)) :
    (∫ fresh : TimeControl p,
      (if oldMarker? rate rewards C_star C_h r
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p r z fresh) = some o
        then (1 : ℝ) else 0) ∂ContinuousLearningRows.timeControlLaw p) =
      if incomingEnabled? rate rewards C_star C_h r z = some true then
        match o with
        | some a => (incomingRates? rate rewards C_star C_h r z).getD (fun _ => 0) a
        | none => 1 - ∑ a, (incomingRates? rate rewards C_star C_h r z).getD (fun _ => 0) a
      else if o = none then 1 else 0 := by
  obtain ⟨payload, c, hp, hc, _hrate, hm⟩ :=
    oldMarker_fresh_recordingMap rate rewards C_star C_h control0 r z hz
  have he := oldCell_enabled_eq_incoming rate rewards C_star C_h r z c hc
  have hrates : incomingRates? rate rewards C_star C_h r z = some payload.rate := by
    simp only [incomingRates?, hp, Option.map_some]
  rw [he, hrates]
  have hi : (fun fresh : TimeControl p =>
      if oldMarker? rate rewards C_star C_h r
          (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p r z fresh) = some o
        then (1 : ℝ) else 0) =
      fun fresh => if SnapshotRecordingKernel.recordingMap p .collection c.enabled
        rate.eta.val rate.eta.property rate.sourceCap payload.anchor payload.anchor
        payload.anchor_pos payload.anchor_pos (fun _ => le_rfl)
        (fun a => by linarith [payload.anchor_pos a]) fresh.1 = o
        then (1 : ℝ) else 0 := by
    funext fresh
    simp only [hm fresh, Option.some.injEq]
  rw [hi]
  cases henabled : c.enabled with
  | true =>
      simpa only [henabled, Option.some.injEq, ite_true, Option.getD_some] using
        collection_recordingMap_control_integral rate payload o
  | false =>
      cases o <;> simp [SnapshotRecordingKernel.recordingMap_disabled]


private theorem oldMarker_eq_of_incoming_current (r : Fin p.T) (z z' : SourceInput p)
    (hz : z ∈ oldSelector rate rewards C_star C_h r)
    (hz' : z' ∈ oldSelector rate rewards C_star C_h r)
    (hin : incoming rate rewards C_star C_h r z = incoming rate rewards C_star C_h r z')
    (hu : ReferenceSourceCurrentControlFreshness.u_t p r z =
      ReferenceSourceCurrentControlFreshness.u_t p r z') :
    oldMarker? rate rewards C_star C_h r z = oldMarker? rate rewards C_star C_h r z' := by
  obtain ⟨payload, c, hp, hc, _hrate, hm⟩ :=
    oldCell_recordingMap rate rewards C_star C_h r z hz
  obtain ⟨payload', c', hp', hc', _hrate', hm'⟩ :=
    oldCell_recordingMap rate rewards C_star C_h r z' hz'
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

local instance optionMeasurableSpace {A : Type*} [MeasurableSpace A] :
    MeasurableSpace (Option A) := LaterAssignmentStartMeasurability.optionMeasurableSpace

private theorem measurableSet_some_singleton (o : Option (Fin p.K)) :
    MeasurableSet ({some o} : Set (Option (Option (Fin p.K)))) := by
  change MeasurableSet[(inferInstance : MeasurableSpace (Option (Fin p.K) ⊕ PUnit)).comap
    (Equiv.optionEquivSumPUnit (Option (Fin p.K)))] {some o}
  rw [MeasurableSpace.measurableSet_comap]
  refine ⟨Sum.inl '' {o}, measurableSet_inl_image.mpr (measurableSet_singleton o), ?_⟩
  ext value
  cases value <;> simp

/-- The local marker CE under the original source law and pre-choice field.
Enabled arm and bottom coefficients, disabled present bottom, and outer
absence are kept distinct. There is no supplied recording or predictability law. -/
theorem oldMarker_condExp (control0 : TimeControl p) (r : Fin p.T)
    (o : Option (Fin p.K)) :
    (sourceInputLaw p)[(oldSelector rate rewards C_star C_h r).indicator
      (fun z => if oldMarker? rate rewards C_star C_h r z = some o then (1 : ℝ) else 0) |
      sourcePrefixFiltration control0 (r.val + 1)] =ᵐ[sourceInputLaw p]
      (oldSelector rate rewards C_star C_h r).indicator (fun z =>
        if incomingEnabled? rate rewards C_star C_h r z = some true then
          match o with
          | some a => (incomingRates? rate rewards C_star C_h r z).getD (fun _ => 0) a
          | none => 1 - ∑ a, (incomingRates? rate rewards C_star C_h r z).getD (fun _ => 0) a
        else if o = none then 1 else 0) := by
  let E := oldSelector rate rewards C_star C_h r
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
    ((oldSelector_measurable_ambient rate rewards C_star C_h control0 r).inter
      ((oldMarker_measurable rate rewards C_star C_h r) (measurableSet_some_singleton o))).preimage
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
      (oldSelector_replaceCurrent rate rewards C_star C_h control0 r seed fresh).trans
        (oldSelector_factor rate rewards C_star C_h control0 r z).symm
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
      have hm := oldMarker_eq_of_incoming_current rate rewards C_star C_h r restored z hz' hz hin hu
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
    · have hs : seed ∈ E := (oldSelector_factor rate rewards C_star C_h control0 r z).mp hz
      have heq : (fun fresh => B.indicator (fun _ => (1 : ℝ)) (seed, fresh)) =
          fun fresh => test (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p r seed fresh) := by
        funext fresh
        rw [hBtest, Set.indicator_of_mem
          (oldSelector_replaceCurrent_forward rate rewards C_star C_h control0 r seed hs fresh)]
      change (∫ fresh, B.indicator (fun _ => (1 : ℝ)) (seed, fresh)
        ∂ContinuousLearningRows.timeControlLaw p) = _
      rw [heq, Set.indicator_of_mem hz]
      have hi := oldMarker_control_integral rate rewards C_star C_h control0 r seed hs o
      have hrates : incomingRates? rate rewards C_star C_h r seed =
          incomingRates? rate rewards C_star C_h r z := by
        unfold incomingRates?
        rw [← incomingPayload_factor rate rewards C_star C_h control0 r z]
      have henabled : incomingEnabled? rate rewards C_star C_h r seed =
          incomingEnabled? rate rewards C_star C_h r z := by
        rw [incomingEnabled_eq_code, incomingEnabled_eq_code,
          ← ReferenceSourcePrefixHistoryFiltration.incoming_factor rate rewards C_star C_h control0 r z]
      simpa only [test, coefficient, hrates, henabled] using hi
    · have hs : seed ∉ E := mt (oldSelector_factor rate rewards C_star C_h control0 r z).mpr hz
      have heq : (fun fresh => B.indicator (fun _ => (1 : ℝ)) (seed, fresh)) = fun _ => 0 := by
        funext fresh
        rw [hBtest, Set.indicator_of_notMem
          (mt (oldSelector_replaceCurrent rate rewards C_star C_h control0 r seed fresh).mp hs)]
      change (∫ fresh, B.indicator (fun _ => (1 : ℝ)) (seed, fresh)
        ∂ContinuousLearningRows.timeControlLaw p) = _
      rw [heq, integral_zero, Set.indicator_of_notMem hz]
  have hce := ReferenceSourceCurrentControlFreshness.source_control_test_condExp control0 r B hB
  rw [htest] at hce
  simpa only [ReferenceSourcePhysicalFlagConditionalLaw.sourcePrefixField_eq_m_t, hsection] using hce

/-- Evaluated enabled-arm CE at the actual incoming rate. -/
theorem oldMarker_arm_condExp (control0 : TimeControl p) (r : Fin p.T) (a : Fin p.K) :
    (sourceInputLaw p)[(oldSelector rate rewards C_star C_h r).indicator
      (fun z => if oldMarker? rate rewards C_star C_h r z = some (some a) then (1 : ℝ) else 0) |
      sourcePrefixFiltration control0 (r.val + 1)] =ᵐ[sourceInputLaw p]
      (oldSelector rate rewards C_star C_h r).indicator (fun z =>
        if incomingEnabled? rate rewards C_star C_h r z = some true then
          (incomingRates? rate rewards C_star C_h r z).getD (fun _ => 0) a else 0) := by
  simpa only [reduceCtorEq, ite_false] using
    oldMarker_condExp rate rewards C_star C_h control0 r (some a)

/-- Enabled present bottom has the complementary rate mass; disabled present
bottom has mass one, under the same unnormalized original source law. -/
theorem oldMarker_bottom_condExp (control0 : TimeControl p) (r : Fin p.T) :
    (sourceInputLaw p)[(oldSelector rate rewards C_star C_h r).indicator
      (fun z => if oldMarker? rate rewards C_star C_h r z = some none then (1 : ℝ) else 0) |
      sourcePrefixFiltration control0 (r.val + 1)] =ᵐ[sourceInputLaw p]
      (oldSelector rate rewards C_star C_h r).indicator (fun z =>
        if incomingEnabled? rate rewards C_star C_h r z = some true then
          1 - ∑ a, (incomingRates? rate rewards C_star C_h r z).getD (fun _ => 0) a else 1) := by
  simpa only [ite_true] using oldMarker_condExp rate rewards C_star C_h control0 r none

/-- A disabled present cell is bottom, and all its raw arrivals vanish. -/
theorem oldMarker_disabled_present (r : Fin p.T) (z : SourceInput p)
    (hz : z ∈ oldSelector rate rewards C_star C_h r)
    (he : incomingEnabled? rate rewards C_star C_h r z = some false) :
    oldMarker? rate rewards C_star C_h r z = some none ∧
      ∀ a, oldRaw rate rewards C_star C_h r a z = 0 := by
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hz.2
  have he' : c.enabled = false := Option.some.inj
    ((oldCell_enabled_eq_incoming rate rewards C_star C_h r z c hc).symm.trans he)
  exact oldCell_disabled rate rewards C_star C_h r z hz c hc he'

/-- Outer absence has zero localized mass; it is distinct from present bottom. -/
theorem oldMarker_absent_condExp (control0 : TimeControl p) (r : Fin p.T) :
    (sourceInputLaw p)[(oldSelector rate rewards C_star C_h r).indicator
      (fun z => if oldMarker? rate rewards C_star C_h r z = none then (1 : ℝ) else 0) |
      sourcePrefixFiltration control0 (r.val + 1)] =ᵐ[sourceInputLaw p] 0 := by
  have hzero : (oldSelector rate rewards C_star C_h r).indicator
      (fun z => if oldMarker? rate rewards C_star C_h r z = none then (1 : ℝ) else 0) = 0 := by
    funext z
    by_cases hz : z ∈ oldSelector rate rewards C_star C_h r
    · obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hz.2
      simp only [Set.indicator_of_mem hz, oldMarker?, hc, Option.map_some,
        reduceCtorEq, ite_false, Pi.zero_apply]
    · exact Set.indicator_of_notMem hz _
  rw [hzero, condExp_zero]

/-- Evaluated original localized raw CE: branch indicator, enabled indicator,
actual incoming rate, and the SAME predictable floor amplitude. -/
theorem oldRaw_condExp (control0 : TimeControl p) (r : Fin p.T) (a : Fin p.K) :
    (sourceInputLaw p)[(oldSelector rate rewards C_star C_h r).indicator
      (oldRaw rate rewards C_star C_h r a) |
      sourcePrefixFiltration control0 (r.val + 1)] =ᵐ[sourceInputLaw p]
      fun z => (oldSelector rate rewards C_star C_h r).indicator (fun _ => (1 : ℝ)) z *
        (if incomingEnabled? rate rewards C_star C_h r z = some true then (1 : ℝ) else 0) *
        (incomingRates? rate rewards C_star C_h r z).getD (fun _ => 0) a *
        (incomingAmplitude? rate rewards C_star C_h r a z).getD 0 := by
  filter_upwards [oldRaw_condExp_factor rate rewards C_star C_h control0 r a,
    oldMarker_arm_condExp rate rewards C_star C_h control0 r a] with z hraw harm
  rw [hraw, Pi.mul_apply, harm]
  by_cases hz : z ∈ oldSelector rate rewards C_star C_h r <;>
    by_cases he : incomingEnabled? rate rewards C_star C_h r z = some true <;>
    simp [Set.indicator, hz, he, mul_comm]

/-- The literal integer floor over the SAME numerator `n` satisfies the
original first-mean upper bound, with the full rounded reward table retained. -/
theorem oldRaw_floor_firstMean_bounds (r : Fin p.T) (a : Fin p.K) (z : SourceInput p)
    (hz : z ∈ oldSelector rate rewards C_star C_h r) :
    ∃ payload : Payload rate,
      incomingPayload? rate rewards C_star C_h r z = some payload ∧
      (incomingAmplitude? rate rewards C_star C_h r a z).getD 0 =
        (Nat.floor (((D p : ℝ) * rate.eta.val * roundedReward rewards r a) /
          payload.rate a) : ℝ) / (rate.n : ℝ) ∧
      0 ≤ payload.rate a *
        ((Nat.floor (((D p : ℝ) * rate.eta.val * roundedReward rewards r a) /
          payload.rate a) : ℝ) / (rate.n : ℝ)) ∧
      payload.rate a *
        ((Nat.floor (((D p : ℝ) * rate.eta.val * roundedReward rewards r a) /
          payload.rate a) : ℝ) / (rate.n : ℝ)) ≤ roundedReward rewards r a ∧
      roundedReward rewards r a ≤ 1 := by
  obtain ⟨payload, hp, hnonneg, hbound, hreward⟩ :=
    oldCell_firstMean_le_reward rate rewards C_star C_h r a z hz
  have hamp : (incomingAmplitude? rate rewards C_star C_h r a z).getD 0 =
      (Nat.floor (((D p : ℝ) * rate.eta.val * roundedReward rewards r a) /
        payload.rate a) : ℝ) / (rate.n : ℝ) := by
    simp only [incomingAmplitude?, hp, Option.map_some, Option.getD_some,
      QuantizedRecordingMoments.quantizedValue, QuantizedRecordingMoments.quantizedIndex,
      rate.n_scale]
  exact ⟨payload, hp, hamp, hamp ▸ hnonneg, hamp ▸ hbound, hreward⟩

/-- Original-law raw integral, without conditioning on any future call. -/
theorem oldRaw_integral (control0 : TimeControl p) (r : Fin p.T) (a : Fin p.K) :
    (∫ z, (oldSelector rate rewards C_star C_h r).indicator
      (oldRaw rate rewards C_star C_h r a) z ∂sourceInputLaw p) =
    ∫ z, (oldSelector rate rewards C_star C_h r).indicator (fun _ => (1 : ℝ)) z *
      (if incomingEnabled? rate rewards C_star C_h r z = some true then (1 : ℝ) else 0) *
      (incomingRates? rate rewards C_star C_h r z).getD (fun _ => 0) a *
      (incomingAmplitude? rate rewards C_star C_h r a z).getD 0 ∂sourceInputLaw p := by
  exact (integral_condExp ((sourcePrefixFiltration control0).le' (r.val + 1))).symm.trans
    (integral_congr_ae (oldRaw_condExp rate rewards C_star C_h control0 r a))

/-- Original-law integral of every arm or present-bottom test. -/
theorem oldMarker_integral (control0 : TimeControl p) (r : Fin p.T)
    (o : Option (Fin p.K)) :
    (∫ z, (oldSelector rate rewards C_star C_h r).indicator
      (fun z => if oldMarker? rate rewards C_star C_h r z = some o then (1 : ℝ) else 0) z
      ∂sourceInputLaw p) =
    ∫ z, (oldSelector rate rewards C_star C_h r).indicator (fun z =>
      if incomingEnabled? rate rewards C_star C_h r z = some true then
        match o with
        | some a => (incomingRates? rate rewards C_star C_h r z).getD (fun _ => 0) a
        | none => 1 - ∑ a, (incomingRates? rate rewards C_star C_h r z).getD (fun _ => 0) a
      else if o = none then 1 else 0) z ∂sourceInputLaw p := by
  exact (integral_condExp ((sourcePrefixFiltration control0).le' (r.val + 1))).symm.trans
    (integral_congr_ae (oldMarker_condExp rate rewards C_star C_h control0 r o))

end Bandits.Support.ReferenceFirstCollectionOldSelectorRecordingLaw
