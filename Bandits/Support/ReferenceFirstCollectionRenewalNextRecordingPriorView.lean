/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionRenewalNextControlLaw
public import Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix

/-!
# Recording inputs before the first next control

Sources: `sources/zip4/manuscript/04_slow_fast_learner.tex:140-188`,
`sources/zip4/manuscript/05_binary_transport.tex:354-431`,
`sources/zip4/manuscript/06_interruptions.tex:391-426`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-79`.

All observations below concern the original renewal subtype and its actual
first next calendar record. No marker probability or moment law is asserted.
-/

@[expose] public section
noncomputable section

open MeasureTheory
open Bandits.Support ConstructorDimensions
open scoped Classical

namespace Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingPriorView

open ReferenceActivePhysicalStep
open ReferenceActivePhysicalStepMeasurability
open ReferenceLiveDispatchMeasurability
open ReferenceLiveDispatchOutputMeasurability
open ReferenceFirstCollectionRenewalIncomingQueuePrefix
open ReferenceSourcePrefixHistoryFiltration

open _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix

variable {p : ConstructorDimensions.Parameters}

/-- Exact live constructor tags, with the initializer's checked value and
each local failure reason retained. The successful tag omits only the arm. -/
abbrev LiveTag (p : ConstructorDimensions.Parameters) :=
  CoordinatorPhaseClock.ClockFailure ⊕
    ((DispatchData p × Option (Bool × Option (LedgerData p))) ⊕
      ((DispatchData p × CoordinatorRoundDispatch.LiveFailure) ⊕ (DispatchData p × Bool)))

instance liveTagCountable : Countable (LiveTag p) := by
  let encode : LiveTag p → OutcomeData p × Bool := fun tag => match tag with
    | .inl reason => (.clockFailure reason, false)
    | .inr (.inl (dispatched, checked)) => (.initializerFailure dispatched checked, false)
    | .inr (.inr (.inl (dispatched, reason))) => (.localFailure dispatched reason, false)
    | .inr (.inr (.inr (dispatched, cutoff))) =>
        (.continuingChosen dispatched dispatched.1 ⟨0, K_pos p⟩, cutoff)
  have hinj : Function.Injective encode := by
    intro a b h
    rcases a with a | a | a | ⟨ad, ac⟩ <;>
      rcases b with b | b | b | ⟨bd, bc⟩ <;>
      simp_all [encode, Prod.mk.injEq]
    all_goals exact Prod.ext h.1 h.2
  exact hinj.countable

instance liveTagMeasurableSpace : MeasurableSpace (LiveTag p) := ⊤
instance liveTagDiscrete : DiscreteMeasurableSpace (LiveTag p) := ⟨fun _ => trivial⟩

instance liveTagOptionMeasurableSpace : MeasurableSpace (Option (LiveTag p)) := ⊤
instance liveTagOptionDiscrete : DiscreteMeasurableSpace (Option (LiveTag p)) := ⟨fun _ => trivial⟩

/-- A literal projection of the accepted lossless outcome code. -/
def eraseArm : OutcomeData p → LiveTag p
  | .clockFailure reason => .inl reason
  | .initializerFailure dispatched checked => .inr (.inl (dispatched, checked))
  | .localFailure dispatched reason => .inr (.inr (.inl (dispatched, reason)))
  | .cutoffChosen dispatched _ _ => .inr (.inr (.inr (dispatched, true)))
  | .continuingChosen dispatched _ _ => .inr (.inr (.inr (dispatched, false)))

/-- The actual successful StartRound, when there is a chosen branch. -/
def tagStarted : LiveTag p → Option (CoordinatorPhaseClock.StartRoundResult p)
  | .inr (.inr (.inr (dispatched, _))) => some dispatched.1
  | _ => none

theorem selectedData_started (out : OutcomeData p) :
    (selectedData out).map Prod.fst = tagStarted (eraseArm out) := by
  cases out <;> rfl

/-- All branch checks preceding the nonempty chosen arm use carried inputs.
The accepted output formula already accounts for actual choice nonemptiness. -/
theorem liveTag_row_invariant
    (x : CoordinatorRoundDispatch.LiveInput p) (row : CompletePublicTable.CompleteRow p) :
    eraseArm (outcomeData (CoordinatorRoundDispatch.dispatchLive x)) =
      eraseArm (outcomeData (CoordinatorRoundDispatch.dispatchLive { x with row := row })) := by
  rw [outcomeData_dispatchLive, outcomeData_dispatchLive]
  unfold dataFormula
  dsimp only
  split
  · rfl
  · split
    · rfl
    · rfl
    · unfold choiceData
      dsimp only
      simp only [apply_ite eraseArm]
      rfl
    · unfold choiceData
      dsimp only
      simp only [apply_ite eraseArm]
      rfl

/-- Outer absence is retained for non-live dispatches. On our source it can
only be dagger; the impossible phases are excluded separately. -/
def dispatchTag {rate : RateInput p} (x : RoundInput p rate) : Option (LiveTag p) :=
  match dispatch x with
  | .live _ _ _ out => some (eraseArm (outcomeData out))
  | _ => none

theorem dispatchTag_live {rate : RateInput p} (x : RoundInput p rate)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ) (h : x.state.coordinator = .live r owned base) :
    dispatchTag x = some (eraseArm (outcomeData
      (CoordinatorRoundDispatch.dispatchLive (liveInput x r owned base)))) := by
  rw [dispatchTag, canonicalDispatch_live_reconstruction x r owned base h]

theorem dispatchTag_congr {rate : RateInput p} (left right : RoundInput p rate)
    (hstate : left.state = right.state) (htime : left.time = right.time)
    (hphase : match left.state.coordinator with | .live .. => True | .dagger => True | _ => False) :
    dispatchTag left = dispatchTag right := by
  cases hs : left.state.coordinator with
  | first => simp only [hs] at hphase
  | collection payload ledger saved => simp only [hs] at hphase
  | dagger => simp only [dispatchTag, dispatch, hs, ← hstate]
  | live r owned base =>
    rw [dispatchTag_live left r owned base hs,
      dispatchTag_live right r owned base (by rw [← hstate]; exact hs)]
    have h := liveTag_row_invariant (liveInput left r owned base) right.row
    have hi : { liveInput left r owned base with row := right.row } =
        liveInput right r owned base := by
      dsimp only [liveInput]
      rw [htime]
    rw [hi] at h
    exact congrArg some h

/-- The actual sender view, including payload, anchor, pending set, cutoff,
and complement weights, omits the current chosen arm. -/
theorem downView_congr {rate : RateInput p} (left right : RoundInput p rate)
    (hstate : left.state = right.state) (htime : left.time = right.time)
    (hphase : match left.state.coordinator with | .live .. => True | .dagger => True | _ => False) :
    (dispatch left).downView = (dispatch right).downView := by
  cases hs : left.state.coordinator with
  | first => simp only [hs] at hphase
  | collection payload ledger saved => simp only [hs] at hphase
  | dagger => simp only [dispatch, hs, ← hstate, DispatchCut.downView, DispatchCut.selection, Option.map_none]
  | live r owned base =>
    rw [canonical_downViewObservation left r owned base hs,
      canonical_downViewObservation right r owned base (by rw [← hstate]; exact hs)]
    have he := liveTag_row_invariant (liveInput left r owned base) right.row
    have hi : { liveInput left r owned base with row := right.row } =
        liveInput right r owned base := by
      dsimp only [liveInput]
      rw [htime]
    rw [hi] at he
    have hstart := congrArg tagStarted he
    rw [← selectedData_started, ← selectedData_started] at hstart
    rw [← outcomeData_originalInput left r owned base,
      ← outcomeData_originalInput right r owned base] at hstart
    have hv : ∀ started, viewAtStart (liveDispatchCoordinatesOfRound left r owned base) started =
        viewAtStart (liveDispatchCoordinatesOfRound right r owned base) started := by
      intro started
      rw [viewAtStart_originalInput, viewAtStart_originalInput, htime]
    have heq (x : RoundInput p rate) :
        downViewObservation (liveDispatchCoordinatesOfRound x r owned base) =
          ((selectedData (outcomeData (CoordinatorRoundDispatch.dispatchLive
            (liveInputOfCoordinates (liveDispatchCoordinatesOfRound x r owned base))))).map
              Prod.fst).map (viewAtStart (liveDispatchCoordinatesOfRound x r owned base)) := by
      unfold downViewObservation selectionObservation
      cases selectedData (outcomeData (CoordinatorRoundDispatch.dispatchLive
        (liveInputOfCoordinates (liveDispatchCoordinatesOfRound x r owned base)))) <;> rfl
    change downViewObservation (liveDispatchCoordinatesOfRound left r owned base) =
      downViewObservation (liveDispatchCoordinatesOfRound right r owned base)
    rw [heq, heq, hstart]
    exact congrArg (fun f => Option.map f _) (funext hv)

/-- The actual coarse tag is Borel, on the original continuous input space. -/
theorem measurable_dispatchTag {rate : RateInput p} :
    Measurable (dispatchTag (p := p) (rate := rate)) := by
  apply measurable_of_restrict_of_restrict_compl
    ReferenceFirstLiveCoordinatorStepMeasurability.measurableSet_liveSet
  · have h := (measurable_of_countable (fun out : OutcomeData p => some (eraseArm out))).comp
      (measurable_dispatchLive_outcomeData.comp
        (ReferenceFirstLiveCoordinatorStepMeasurability.measurable_liveCoordinates
          (p := p) (rate := rate)))
    convert h using 1
    funext x
    dsimp only [Function.comp_def, Set.domRestrict,
      ReferenceFirstLiveCoordinatorStepMeasurability.liveCoordinates]
    rw [outcomeData_originalInput]
    exact dispatchTag_live x.val _ _ _
      (ReferenceFirstLiveCoordinatorStepMeasurability.live_state x)
  · have heq : (fun x : ↥((ReferenceFirstLiveCoordinatorStepMeasurability.liveSet
        (p := p) (rate := rate))ᶜ) => dispatchTag x.val) = fun _ => none := by
      funext x
      cases hc : x.val.state.coordinator with
      | first =>
        simp only [dispatchTag, dispatch, hc, CoordinatorRoundDispatch.dispatch]
        cases CoordinatorRoundDispatch.dispatchFirst _ <;> rfl
      | live r owned base =>
        exact False.elim (x.property ⟨(r.payload, encodeLive r owned base), by
          simp only [encodeState, hc, encodeCoordinator]⟩)
      | collection payload ledger saved =>
        by_cases hcut : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
        · simp only [dispatchTag, dispatch, hc, dite_eq_left hcut,
            CoordinatorRoundDispatch.dispatch]
          cases CoordinatorRoundDispatch.dispatchCollection _ <;> rfl
        · simp only [dispatchTag, dispatch, hc, dite_eq_right hcut]
      | dagger => simp only [dispatchTag, dispatch, hc]
    change Measurable (fun x : ↥((ReferenceFirstLiveCoordinatorStepMeasurability.liveSet
      (p := p) (rate := rate))ᶜ) => dispatchTag x.val)
    rw [heq]
    exact measurable_const

/-- Successful ordinary preparations with the same incoming state have the
same complete follower states and memories. Their UP checks and arm choices
may differ; their common StartRound computation cannot differ. -/
theorem ordinary_preparation_congr {rate : RateInput p}
    (left right : RoundInput p rate)
    (hstate : left.state = right.state) (htime : left.time = right.time)
    (i : Fin (p.m - 1))
    (sl sr : ReferencePrelaunchFollower.State p rate.eta)
    (ml mr : ActiveFollowerLifecycle.LocalMemory p)
    (hl : ((prepare left).followers.followers i).configuration = .ordinary sl ml)
    (hr : ((prepare right).followers.followers i).configuration = .ordinary sr mr) :
    sl = sr ∧ ml = mr := by
  obtain ⟨beforeL, memoryL, _, hinputL, hstartL, _⟩ :=
    ReferenceActiveDataOwnership.prepare_ordinary_choice i left.row
      (left.state.activations i) left.time (left.active i) (left.state.followers i) sl ml hl
  obtain ⟨beforeR, memoryR, _, hinputR, hstartR, _⟩ :=
    ReferenceActiveDataOwnership.prepare_ordinary_choice i right.row
      (right.state.activations i) right.time (right.active i) (right.state.followers i) sr mr hr
  have hinput : DeclaredFollowerLocalRound.LocalConfiguration.ordinary beforeL memoryL =
      .ordinary beforeR memoryR :=
    hinputL.symm.trans ((congrArg (fun state => state.followers i) hstate).trans hinputR)
  obtain ⟨hbefore, hmemory⟩ := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj hinput
  rw [← hbefore, ← hmemory, ← htime] at hstartR
  exact Prod.mk.inj (Except.ok.inj (hstartL.symm.trans hstartR))

private theorem measurable_of_some {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]
    (f : X → A) (hf : Measurable (fun x => some (f x))) : Measurable f := by
  let e : Option A ≃ A ⊕ PUnit := Equiv.optionEquivSumPUnit A
  have hs : Measurable (fun x => e (some (f x))) := measurable_comap_iff.mp hf
  intro v hv
  convert hs hv.inl_image using 1
  ext x
  change f x ∈ v ↔ (Sum.inl (f x) : A ⊕ PUnit) ∈ Sum.inl '' v
  simp only [Set.mem_image, Sum.inl.injEq, exists_eq_right]

variable (rate : RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ) (u t : Fin p.T)

local notation "Z" => ReferenceFirstCollectionRenewalNextControlLaw.Source rate rewards C_star C_h u t

/-- The calendar lookup is the actual next record, including failed records. -/
theorem actualRecord_next (z : Z) (hq : t.val + 1 < p.T) :
    actualRecord rate rewards C_star C_h ⟨t.val + 1, hq⟩ z.val =
      some (nextRecord rate rewards C_star C_h u t z hq) := by
  have hb := actual_boundaries rate rewards C_star C_h u t z
  have hs : ReferenceCompletePhysicalHistory.physicalStart rate z.val rewards C_star C_h ≤
      t.val + 1 := by change start rate rewards C_star C_h u t z ≤ _; omega
  rw [actualRecord, ite_eq_left hs]
  have he : t.val + 1 - start rate rewards C_star C_h u t z =
      t.val - start rate rewards C_star C_h u t z + 1 := by omega
  change (sourceRecords rate rewards C_star C_h u t z)[
    t.val + 1 - start rate rewards C_star C_h u t z]? = _
  rw [he]
  exact nextRecord_lookup rate rewards C_star C_h u t z hq

theorem incoming_next (z : Z) (hq : t.val + 1 < p.T) :
    incoming rate rewards C_star C_h ⟨t.val + 1, hq⟩ z.val =
      some (encodeState (nextRecord rate rewards C_star C_h u t z hq).input.state) := by
  rw [ReferenceSourcePrefixHistoryFiltration.incoming, actualRecord_next]
  rfl

/-- Same strict prefix fixes the original next incoming state. No ordinary
or successful-dispatch premise occurs here. -/
theorem nextState_congr (control0 : ContinuousLearningRows.TimeControl p)
    (hq : t.val + 1 < p.T) (z z' : Z)
    (hprefix : sourcePrefix control0 (t.val + 1) z.val =
      sourcePrefix control0 (t.val + 1) z'.val) :
    (nextRecord rate rewards C_star C_h u t z hq).input.state =
      (nextRecord rate rewards C_star C_h u t z' hq).input.state := by
  apply encodeState_injective
  apply Option.some.inj
  rw [← incoming_next rate rewards C_star C_h u t z hq,
    ← incoming_next rate rewards C_star C_h u t z' hq,
    incoming_factor rate rewards C_star C_h control0 ⟨t.val + 1, hq⟩ z.val,
    incoming_factor rate rewards C_star C_h control0 ⟨t.val + 1, hq⟩ z'.val]
  rw [hprefix]

theorem nextState_factor (control0 : ContinuousLearningRows.TimeControl p)
    (z : Z) (hq : t.val + 1 < p.T) :
    (nextRecord rate rewards C_star C_h u t z hq).input.state =
      (nextRecord rate rewards C_star C_h u t
        (ReferenceFirstCollectionRenewalNextPriorReadout.nextPriorObserver rate rewards C_star C_h u t control0 z) hq).input.state := by
  apply nextState_congr rate rewards C_star C_h u t control0 hq
  rw [ReferenceFirstCollectionRenewalNextPriorReadout.nextPriorObserver_val, sourcePrefix_sourcePrefix control0 _ _ le_rfl]

/-- The exact next coarse dispatch observation. -/
def nextTag (z : Z) (hq : t.val + 1 < p.T) :=
  dispatchTag (nextRecord rate rewards C_star C_h u t z hq).input

/-- The actual optional sender view; no view is supplied on absence. -/
def nextDownView (z : Z) (hq : t.val + 1 < p.T) :=
  (nextRecord rate rewards C_star C_h u t z hq).output.preparation.coordinator.downView

theorem nextTag_factor (control0 : ContinuousLearningRows.TimeControl p)
    (z : Z) (hq : t.val + 1 < p.T) :
    nextTag rate rewards C_star C_h u t z hq =
      nextTag rate rewards C_star C_h u t
        (ReferenceFirstCollectionRenewalNextPriorReadout.nextPriorObserver rate rewards C_star C_h u t control0 z) hq := by
  apply dispatchTag_congr
  · exact nextState_factor rate rewards C_star C_h u t control0 z hq
  · exact (nextRecord_fields rate rewards C_star C_h u t z hq).1.trans
      (nextRecord_fields rate rewards C_star C_h u t _ hq).1.symm
  · exact nextRecord_input_phase rate rewards C_star C_h u t z hq

theorem nextDownView_factor (control0 : ContinuousLearningRows.TimeControl p)
    (z : Z) (hq : t.val + 1 < p.T) :
    nextDownView rate rewards C_star C_h u t z hq =
      nextDownView rate rewards C_star C_h u t
        (ReferenceFirstCollectionRenewalNextPriorReadout.nextPriorObserver rate rewards C_star C_h u t control0 z) hq := by
  unfold nextDownView
  rw [(nextRecord rate rewards C_star C_h u t z hq).output_eq,
    (nextRecord rate rewards C_star C_h u t
      (ReferenceFirstCollectionRenewalNextPriorReadout.nextPriorObserver rate rewards C_star C_h u t control0 z) hq).output_eq]
  apply downView_congr
  · exact nextState_factor rate rewards C_star C_h u t control0 z hq
  · exact (nextRecord_fields rate rewards C_star C_h u t z hq).1.trans
      (nextRecord_fields rate rewards C_star C_h u t _ hq).1.symm
  · exact nextRecord_input_phase rate rewards C_star C_h u t z hq

/-- Joint Borel measurability of the genuine first next round input. -/
theorem measurable_nextInput (hq : t.val + 1 < p.T) :
    Measurable (fun z : Z =>
      (nextRecord
        rate rewards C_star C_h u t z hq).input) := by
  have hc : Measurable (fun z : Z => encodeState
      (nextRecord
        rate rewards C_star C_h u t z hq).input.state) := by
    apply measurable_of_some
    have h : Measurable (fun z : Z => ReferenceSourcePrefixHistoryFiltration.incoming
        rate rewards C_star C_h ⟨t.val + 1, hq⟩ z.val) :=
      (measurable_incoming rate rewards C_star C_h ⟨t.val + 1, hq⟩).comp measurable_subtype_coe
    convert h using 1
    funext z
    exact (incoming_next rate rewards C_star C_h u t z hq).symm
  have hs : Measurable (fun z : Z =>
      (nextRecord
        rate rewards C_star C_h u t z hq).input.state) := measurable_comap_iff.mpr hc
  have hr : Measurable (fun z : Z => z.val.1.2) :=
    measurable_snd.comp (measurable_fst.comp measurable_subtype_coe)
  have hj : Measurable (fun z : Z => ActualInitializationPhysicalStep.selectedRowIndex p z.val) :=
    (BootstrapPrivateRoundStreams.measurable_sourceCoordinatorIndex p).comp measurable_subtype_coe
  apply measurable_comap_iff.mpr
  apply Measurable.subtype_mk
  have heq : (fun z : Z => ((encodeRoundInput
      (nextRecord
        rate rewards C_star C_h u t z hq).input)).val) =
      fun z => ((nextRecord
        rate rewards C_star C_h u t z hq).input.state,
          z.val.1.2, ActualInitializationPhysicalStep.selectedRowIndex p z.val,
            (⟨t.val + 1, hq⟩ : Fin p.T), rewards) := by
    funext z
    have hf := nextRecord_fields
      rate rewards C_star C_h u t z hq
    simp only [encodeRoundInput, hf.1, hf.2.1, hf.2.2.1, hf.2.2.2]
  change Measurable (fun z : Z => (encodeRoundInput
    (nextRecord
      rate rewards C_star C_h u t z hq).input).val)
  rw [heq]
  exact hs.prodMk (hr.prodMk (hj.prodMk (measurable_const.prodMk measurable_const)))

/-- The exact dispatch tag is measurable in the original next-prior field. -/
theorem measurable_nextTag (control0 : ContinuousLearningRows.TimeControl p)
    (hq : t.val + 1 < p.T) :
    Measurable[ReferenceFirstCollectionRenewalNextControlLaw.nextPriorField
      rate rewards C_star C_h u t control0]
      (fun z : Z => nextTag rate rewards C_star C_h u t z hq) := by
  have h : Measurable (fun z : Z => nextTag rate rewards C_star C_h u t z hq) :=
    measurable_dispatchTag.comp (measurable_nextInput rate rewards C_star C_h u t hq)
  have heq : (fun z : Z => nextTag rate rewards C_star C_h u t z hq) =
      fun z => nextTag rate rewards C_star C_h u t
        (ReferenceFirstCollectionRenewalNextPriorReadout.nextPriorObserver
          rate rewards C_star C_h u t control0 z) hq := by
    funext z
    exact nextTag_factor rate rewards C_star C_h u t control0 z hq
  rw [heq]
  exact h.comp (ReferenceFirstCollectionRenewalNextControlLaw.measurable_nextPriorObserver_field
    rate rewards C_star C_h u t control0)

/-- The whole actual sender view is Borel in the same prior field. -/
theorem measurable_nextDownView (control0 : ContinuousLearningRows.TimeControl p)
    (hq : t.val + 1 < p.T) :
    Measurable[ReferenceFirstCollectionRenewalNextControlLaw.nextPriorField
      rate rewards C_star C_h u t control0]
      (fun z : Z => nextDownView rate rewards C_star C_h u t z hq) := by
  have h : Measurable (fun z : Z => nextDownView rate rewards C_star C_h u t z hq) := by
    have hm := ReferenceActiveStepCompositionMeasurability.measurable_downView.comp
      (measurable_nextInput rate rewards C_star C_h u t hq)
    convert hm using 1
    funext z
    unfold nextDownView
    rw [(nextRecord
      rate rewards C_star C_h u t z hq).output_eq]
    rfl
  have heq : (fun z : Z => nextDownView rate rewards C_star C_h u t z hq) =
      fun z => nextDownView rate rewards C_star C_h u t
        (ReferenceFirstCollectionRenewalNextPriorReadout.nextPriorObserver
          rate rewards C_star C_h u t control0 z) hq := by
    funext z
    exact nextDownView_factor rate rewards C_star C_h u t control0 z hq
  rw [heq]
  exact h.comp (ReferenceFirstCollectionRenewalNextControlLaw.measurable_nextPriorObserver_field
    rate rewards C_star C_h u t control0)

/-- The tag is literally the actual recorded dispatch projection. -/
theorem nextTag_eq (z : Z) (hq : t.val + 1 < p.T) :
    nextTag rate rewards C_star C_h u t z hq =
      match (nextRecord rate rewards C_star C_h u t z hq).output.preparation.coordinator with
      | .live _ _ _ out => some (eraseArm (outcomeData out))
      | _ => none := by
  unfold nextTag dispatchTag
  have hd : dispatch (nextRecord rate rewards C_star C_h u t z hq).input =
      (nextRecord rate rewards C_star C_h u t z hq).output.preparation.coordinator := by
    rw [(nextRecord rate rewards C_star C_h u t z hq).output_eq]
    rfl
  rw [hd]
  cases (nextRecord rate rewards C_star C_h u t z hq).output.preparation.coordinator <;> rfl

/-- The literal numerical presence, enabled bit, and complete rate vector. -/
def nextParameters (z : Z) (hq : t.val + 1 < p.T) : Option (Bool × (Fin p.K → ℝ)) :=
  (nextCell rate rewards C_star C_h u t z hq).map (fun c => (c.enabled, c.rate))

/-- Read the numerical parameters from the actual successful tag and sender
view. Failure stays absent; cutoff's disabled cell is still present. -/
def parametersOfTag (q : Fin p.T) (tag : Option (LiveTag p))
    (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta)) :
    Option (Bool × (Fin p.K → ℝ)) :=
  tag.bind fun tag => match tag with
  | .inr (.inr (.inr (dispatched, cutoff))) =>
      view.map fun v => (if cutoff then decide (q.val + 1 < dispatched.1.clock.g) else true,
        v.payload.rate)
  | _ => none

/-- Actual source roots supply the ordinary recording domain separately on
both successful constructors. No no-failure or ordinary premise is assumed. -/
theorem nextParameters_eq (z : Z) (hq : t.val + 1 < p.T) :
    nextParameters rate rewards C_star C_h u t z hq =
      parametersOfTag rate ⟨t.val + 1, hq⟩
        (nextTag rate rewards C_star C_h u t z hq)
        (nextDownView rate rewards C_star C_h u t z hq) := by
  have hr := nextDate_readouts rate rewards C_star C_h u t z hq
  have hl := next_continuing_physical rate rewards C_star C_h u t z hq
  have hc := next_cutoff_physical rate rewards C_star C_h u t z hq
  rw [nextTag_eq]
  unfold nextDownView
  dsimp only at hr hl hc
  cases hd : (nextRecord rate rewards C_star C_h u t z hq).output.preparation.coordinator
    <;> simp only [hd] at hr hl hc ⊢
  all_goals try
    obtain ⟨hL, _, hC, _⟩ := hr
    simp only [nextParameters, nextCell, hL, hC, Option.none_or, Option.map_none,
      parametersOfTag, Option.bind_none]
  rename_i r owned base out
  cases out <;> simp only at hr hl hc ⊢
  all_goals try
    obtain ⟨hL, _, hC, _⟩ := hr
    simp only [nextParameters, nextCell, hL, hC, Option.none_or, Option.map_none,
      parametersOfTag, Option.bind_some, eraseArm, outcomeData]
  · rename_i dispatched hs ledger hi hledger hdomain hclock hpending hstart arm
    obtain ⟨c, payload, ledger', started, weights, recording, hC, hL, hcall,
      henabled, hrate, _⟩ := hc
    have hdom := (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout_domain
      (start rate rewards C_star C_h u t z) (nextRecord rate rewards C_star C_h u t z hq)).mp
      (by change (nextCollection rate rewards C_star C_h u t z hq).isSome = true; rw [hC]; rfl)
    have hcall' : ReferenceLaterCollectionArrivalReadout.laterCollectionCall
        (start rate rewards C_star C_h u t z) (nextRecord rate rewards C_star C_h u t z hq) =
        some ⟨r.payload, sharedLedger ledger, dispatched.startResult,
          (liveRegistersAt r (nextRecord rate rewards C_star C_h u t z hq).input.time).complementWeights⟩ := by
      have hsig : start rate rewards C_star C_h u t z < r.payload.sigma.val := by
        simpa only [hd] using hdom.2
      simp only [ReferenceLaterCollectionArrivalReadout.laterCollectionCall, hdom.1,
        ite_true, hd, hsig]
    have hargs := Option.some.inj (hcall'.symm.trans hcall)
    have hp : r.payload = payload := congrArg (fun args => args.1) hargs
    have ht : dispatched.startResult = started := congrArg (fun args => args.2.2.1) hargs
    simp only [nextParameters, nextCell, hL, hC, Option.none_or, Option.map_some,
      parametersOfTag, Option.bind_some, eraseArm, outcomeData,
      DispatchCut.downView, DispatchCut.selection, selectionAt, dite_true,
      Option.map_some, henabled, hrate, ← hp, ← ht]
    rfl
  · obtain ⟨cell, hL, hC, henabled, _hreward, hrate, _⟩ := hl
    have hsel := cell.selection_actual
    rw [hd] at hsel
    simp only [DispatchCut.selection, selectionAt, dite_true, Option.some.injEq] at hsel
    have hp := congrArg (fun selected => selected.view.payload) hsel
    simp only [nextParameters, nextCell, hL, Option.some_or, Option.map_some,
      parametersOfTag, Option.bind_some, eraseArm, outcomeData,
      DispatchCut.downView, DispatchCut.selection, selectionAt, dite_true,
      Option.map_some, henabled, hrate, ← hp]
    rfl

/-- Numerical presence and parameters factor through the same strict prior
observer, without losing disabled cutoff cells. -/
theorem nextParameters_factor (control0 : ContinuousLearningRows.TimeControl p)
    (z : Z) (hq : t.val + 1 < p.T) :
    nextParameters rate rewards C_star C_h u t z hq =
      nextParameters rate rewards C_star C_h u t
        (ReferenceFirstCollectionRenewalNextPriorReadout.nextPriorObserver
          rate rewards C_star C_h u t control0 z) hq := by
  rw [nextParameters_eq, nextParameters_eq,
    nextTag_factor rate rewards C_star C_h u t control0 z hq,
    nextDownView_factor rate rewards C_star C_h u t control0 z hq]

/-- The SAME renewal subtype at every changed suffix. Membership is produced
from the original event, with no successful-dispatch restriction. -/
def withNextSuffix (z : Z) (hq : t.val + 1 < p.T)
    (suffix : Fin p.T → ContinuousLearningRows.TimeControl p) : Z :=
  ⟨ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix
      z.val ⟨t.val + 1, hq⟩ suffix,
    (ReferenceFirstCollectionRenewalNextControlLaw.renewalCallEvent_iff_nextSuffix
      rate rewards C_star C_h u t hq z.val suffix).mp z.property⟩

/-- The SAME renewal subtype at each arbitrary next whole control. -/
def withNextControl (z : Z) (hq : t.val + 1 < p.T)
    (control : ContinuousLearningRows.TimeControl p) : Z :=
  ⟨ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p ⟨t.val + 1, hq⟩ z.val control,
    (ReferenceFirstCollectionRenewalNextControlLaw.renewalCallEvent_iff_replaceNextControl
      rate rewards C_star C_h u t hq z.val control).mp z.property⟩

/-- The original selected strict prefix is unchanged by every suffix change. -/
theorem withNextSuffix_prefix (control0 : ContinuousLearningRows.TimeControl p)
    (z : Z) (hq : t.val + 1 < p.T)
    (suffix : Fin p.T → ContinuousLearningRows.TimeControl p) :
    sourcePrefix control0 (t.val + 1)
        (withNextSuffix rate rewards C_star C_h u t z hq suffix).val =
      sourcePrefix control0 (t.val + 1) z.val := by
  apply Prod.ext
  · refine Prod.ext rfl ?_
    funext row
    by_cases hr : row = ActualInitializationPhysicalStep.selectedRowIndex p z.val
    · subst row
      simp only [sourcePrefix, withNextSuffix,
        ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix,
        ActualInitializationPhysicalStep.selectedRowIndex, Function.update_self]
      refine Prod.ext rfl ?_
      funext v
      by_cases hv : v.val < t.val + 1 <;> simp only [hv, ite_true, ite_false]
    · have hr' : row ≠ PrivateSourceStreams.coordinatorIndex p z.val.2.1.2 := hr
      simp only [sourcePrefix, withNextSuffix,
        ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix,
        ActualInitializationPhysicalStep.selectedRowIndex, Function.update_of_ne hr']
  · rfl

/-- Equality of strict prefixes gives all three actual prior projections. -/
theorem nextPrior_congr (control0 : ContinuousLearningRows.TimeControl p)
    (z z' : Z) (hq : t.val + 1 < p.T)
    (hprefix : sourcePrefix control0 (t.val + 1) z.val =
      sourcePrefix control0 (t.val + 1) z'.val) :
    nextTag rate rewards C_star C_h u t z hq = nextTag rate rewards C_star C_h u t z' hq ∧
    nextDownView rate rewards C_star C_h u t z hq = nextDownView rate rewards C_star C_h u t z' hq ∧
    nextParameters rate rewards C_star C_h u t z hq = nextParameters rate rewards C_star C_h u t z' hq := by
  have he : ReferenceFirstCollectionRenewalNextPriorReadout.nextPriorObserver
        rate rewards C_star C_h u t control0 z =
      ReferenceFirstCollectionRenewalNextPriorReadout.nextPriorObserver
        rate rewards C_star C_h u t control0 z' := by
    apply Subtype.ext
    simpa only [ReferenceFirstCollectionRenewalNextPriorReadout.nextPriorObserver_val] using hprefix
  exact ⟨(nextTag_factor rate rewards C_star C_h u t control0 z hq).trans
      (he ▸ (nextTag_factor rate rewards C_star C_h u t control0 z' hq).symm),
    (nextDownView_factor rate rewards C_star C_h u t control0 z hq).trans
      (he ▸ (nextDownView_factor rate rewards C_star C_h u t control0 z' hq).symm),
    (nextParameters_factor rate rewards C_star C_h u t control0 z hq).trans
      (he ▸ (nextParameters_factor rate rewards C_star C_h u t control0 z' hq).symm)⟩

/-- The parameter formula is Borel in the ordinary product/Option spaces. -/
theorem measurable_parametersOfTag (q : Fin p.T) :
    Measurable (fun z : Option (LiveTag p) ×
      Option (ReferenceDownReception.ChoiceTimeView p rate.eta) => parametersOfTag rate q z.1 z.2) := by
  apply measurable_from_prod_countable_right
  intro tag
  cases tag with
  | none => exact measurable_const
  | some tag =>
    cases tag with
    | inl reason => exact measurable_const
    | inr tag =>
      cases tag with
      | inl failure => exact measurable_const
      | inr tag =>
        cases tag with
        | inl failure => exact measurable_const
        | inr chosen =>
          have hp : Measurable (fun v : ReferenceDownReception.ChoiceTimeView p rate.eta => v.payload) :=
            measurable_fst.comp (comap_measurable
              (ReferenceDownReceptionMeasurability.choiceTimeViewObservation (p := p) (rate := rate)))
          exact LaterAssignmentFullOutputMeasurability.measurable_optionMap _
            (measurable_const.prodMk (AssignmentPayloadDerivedMeasurability.measurable_inputRate.comp hp))
            _ measurable_id

/-- Numerical presence, disabled/enabled distinction, and all rates are
measurable before the first next control on the original source. -/
theorem measurable_nextParameters (control0 : ContinuousLearningRows.TimeControl p)
    (hq : t.val + 1 < p.T) :
    Measurable[ReferenceFirstCollectionRenewalNextControlLaw.nextPriorField
      rate rewards C_star C_h u t control0]
      (fun z : Z => nextParameters rate rewards C_star C_h u t z hq) := by
  have h := (measurable_parametersOfTag rate ⟨t.val + 1, hq⟩).comp
    ((measurable_nextTag rate rewards C_star C_h u t control0 hq).prodMk
      (measurable_nextDownView rate rewards C_star C_h u t control0 hq))
  convert h using 1
  funext z
  exact nextParameters_eq rate rewards C_star C_h u t z hq

/-- The actual successful constructors produce ordinary follower families.
Cutoff additionally produces every unoccupied status. -/
theorem next_prepared_ordinary (z : Z) (hq : t.val + 1 < p.T) :
    let record := nextRecord rate rewards C_star C_h u t z hq
    match record.output.preparation.coordinator with
    | .live _ _ _ (.continuingChosen ..) =>
      ∃ states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta,
      ∃ memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p,
        ∀ i, (record.output.preparation.followers.followers i).configuration =
          .ordinary (states i) (memories i)
    | .live _ _ _ (.cutoffChosen ..) =>
      ∃ states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta,
      ∃ memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p,
        ∀ i, (record.output.preparation.followers.followers i).configuration =
          .ordinary (states i) (memories i) ∧ (states i).status = .unoccupied
    | _ => True := by
  dsimp only
  have hl := next_continuing_physical rate rewards C_star C_h u t z hq
  have hc := next_cutoff_physical rate rewards C_star C_h u t z hq
  dsimp only at hl hc
  cases hd : (nextRecord rate rewards C_star C_h u t z hq).output.preparation.coordinator
    <;> try trivial
  rename_i out
  cases out <;> try trivial
  · simp only [hd] at hc
    obtain ⟨c, _, _, _, _, _, hC, _⟩ := hc
    have hunoccupied := ((ReferenceLaterCollectionArrivalReadout.laterCollectionReadout_domain
      (start rate rewards C_star C_h u t z) (nextRecord rate rewards C_star C_h u t z hq)).mp
      (by change (nextCollection rate rewards C_star C_h u t z hq).isSome = true; rw [hC]; rfl)).1
    exact ⟨fun i => (ReferenceLaterCollectionArrivalReadout.actualFollowerParts _ hunoccupied i).1,
      fun i => (ReferenceLaterCollectionArrivalReadout.actualFollowerParts _ hunoccupied i).2,
      fun i => ReferenceLaterCollectionArrivalReadout.actualFollowerParts_spec _ hunoccupied i⟩
  · simp only [hd] at hl
    obtain ⟨cell, _⟩ := hl
    exact ⟨cell.states, cell.memories, cell.ordinary⟩

/-- Every ordinary next preparation exposes the original carried input and
its successful lifecycle output, including unchanged lastDown. -/
theorem next_ordinary_startRound (z : Z) (hq : t.val + 1 < p.T)
    (i : Fin (p.m - 1)) (s : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (h : ((nextRecord rate rewards C_star C_h u t z hq).output.preparation.followers.followers i).configuration =
      .ordinary s memory) :
    ∃ before beforeMemory,
      (nextRecord rate rewards C_star C_h u t z hq).input.state.followers i = .ordinary before beforeMemory ∧
      ActiveFollowerLifecycle.startRound rate.eta
        (nextRecord rate rewards C_star C_h u t z hq).input.time before beforeMemory = .ok (s, memory) ∧
      s.lastDown = before.lastDown ∧
      (s.status = .unoccupied ∨ s.status = before.status) := by
  rw [(nextRecord rate rewards C_star C_h u t z hq).output_eq] at h
  obtain ⟨before, beforeMemory, _, hin, hstart, _⟩ :=
    ReferenceActiveDataOwnership.prepare_ordinary_choice i
      (nextRecord rate rewards C_star C_h u t z hq).input.row
      ((nextRecord rate rewards C_star C_h u t z hq).input.state.activations i)
      (nextRecord rate rewards C_star C_h u t z hq).input.time
      ((nextRecord rate rewards C_star C_h u t z hq).input.active i)
      ((nextRecord rate rewards C_star C_h u t z hq).input.state.followers i) s memory h
  exact ⟨before, beforeMemory, hin, hstart,
    (ActiveFollowerLifecycle.startRound_frame rate.eta _ before s beforeMemory memory hstart).1,
    ReferenceActiveDataOwnership.startRound_status _ before s beforeMemory memory hstart⟩

/-- The normal finite status code of an actual prepared configuration.
Dagger remains outer absence, distinct from all three ordinary statuses. -/
def configurationStatus (config : DeclaredFollowerLocalRound.LocalConfiguration p rate) :
    Option (Fin 3) :=
  match config with
  | .dagger => none
  | .ordinary state _ => some (FollowerDownMeasurability.followerStatusCode state.status)

/-- Literal projection of the sole canonical prepared-output code. -/
def preparedStatusCode
    (z : FollowerVaryingActivationMeasurability.VaryingPreparedOutput p rate) : Option (Fin 3) :=
  z.2.2.2.map fun data => FollowerDownMeasurability.followerStatusCode
    (FollowerDownMeasurability.followerStatusOfCode data.1.1.1.status)

private theorem measurable_sigma_sections {I : Type*} {F : I → Type*}
    [∀ i, MeasurableSpace (F i)] {Y : Type*} [MeasurableSpace Y]
    (f : Sigma F → Y) (hf : ∀ i, Measurable (fun x : F i => f ⟨i, x⟩)) : Measurable f := by
  intro v hv
  change MeasurableSet[(⨅ i, (inferInstance : MeasurableSpace (F i)).map (Sigma.mk i))]
    {x | f x ∈ v}
  rw [MeasurableSpace.measurableSet_iInf]
  intro i
  rw [MeasurableSpace.map_def]
  exact hf i hv

theorem measurable_preparedStatusCode : Measurable (preparedStatusCode rate) := by
  have hs : Measurable (fun z : FollowerObservationStageMeasurabilityRepair.CarriedState p rate =>
      FollowerDownMeasurability.followerStatusCode
        (FollowerDownMeasurability.followerStatusOfCode z.1.1.status)) := by
    apply measurable_sigma_sections
    intro index
    change Measurable (fun _ => FollowerDownMeasurability.followerStatusCode
      (FollowerDownMeasurability.followerStatusOfCode index.1.status))
    exact measurable_const
  have ht : Measurable (fun z : Unit ⊕
      (FollowerPrepareJointMeasurability.CarriedState p rate ×
        FollowerPrepareJointMeasurability.LocalMemoryCode p) =>
      z.elim (fun _ => (none : Option (Fin 3)))
        (fun data => some (FollowerDownMeasurability.followerStatusCode
          (FollowerDownMeasurability.followerStatusOfCode data.1.1.1.status)))) :=
    Measurable.sumElim measurable_const
      ((measurable_of_countable (some : Fin 3 → Option (Fin 3))).comp (hs.comp measurable_fst))
  apply measurable_sigma_sections
  intro activation
  convert ht.comp ((FollowerPrepareJointMeasurability.measurable_incomingConfigurationToSum rate).comp
    (measurable_snd.comp measurable_snd)) using 1
  funext z
  cases hi : z.2.2 <;>
    simp only [preparedStatusCode, Function.comp_def,
      FollowerPrepareJointMeasurability.incomingConfigurationToSum, hi,
      Option.map_none, Option.map_some, Sum.elim_inl, Sum.elim_inr]

theorem preparedStatusCode_eq (x : RoundInput p rate) (i : Fin (p.m - 1)) :
    preparedStatusCode rate (preparedFollowerCode x i) =
      configurationStatus rate ((prepare x).followers.followers i).configuration := by
  have h := congrArg (fun prepared => configurationStatus rate prepared.configuration)
    (preparedFollowerCode_reconstruct x i)
  convert h using 1
  generalize hz : preparedFollowerCode x i = z
  cases hi : z.2.2.2 <;>
    simp only [preparedStatusCode, FollowerPrepareJointMeasurability.preparedRoundOfOutput,
      FollowerPrepareJointMeasurability.localConfigurationOfIncoming, hi,
      Option.map_none, Option.map_some, configurationStatus,
      FollowerObservationStageMeasurabilityRepair.reconstructCarriedState,
      FollowerDownMeasurability.followerStateOfCode]

/-- The complete actual prepared status vector, with no collapsed busy tag. -/
def nextStatuses (z : Z) (hq : t.val + 1 < p.T) (i : Fin (p.m - 1)) : Option (Fin 3) :=
  configurationStatus rate
    ((nextRecord rate rewards C_star C_h u t z hq).output.preparation.followers.followers i).configuration

/-- Ambient measurability is only used as Borel evidence; prior equality
below is supplied separately by actual ordinary lifecycle producers. -/
theorem measurable_nextStatuses (hq : t.val + 1 < p.T) :
    Measurable (fun z : Z => nextStatuses rate rewards C_star C_h u t z hq) := by
  apply measurable_pi_iff.mpr
  intro i
  have h := (measurable_preparedStatusCode rate).comp
    ((measurable_preparedFollowerCode i).comp
      (measurable_nextInput rate rewards C_star C_h u t hq))
  convert h using 1
  funext z
  dsimp only [Function.comp_def]
  rw [preparedStatusCode_eq]
  unfold nextStatuses
  rw [(nextRecord rate rewards C_star C_h u t z hq).output_eq]
  rfl

/-- Reformulate the actual ordinary boundary with the exact observed tag. -/
theorem nextTag_ordinary (z : Z) (hq : t.val + 1 < p.T) :
    match nextTag rate rewards C_star C_h u t z hq with
    | some (.inr (.inr (.inr (_, cutoff)))) =>
      ∃ states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta,
      ∃ memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p,
        (∀ i, ((nextRecord rate rewards C_star C_h u t z hq).output.preparation.followers.followers i).configuration =
          .ordinary (states i) (memories i)) ∧
        (cutoff = true → ∀ i, (states i).status = .unoccupied)
    | _ => True := by
  have h := next_prepared_ordinary rate rewards C_star C_h u t z hq
  rw [nextTag_eq]
  dsimp only at h
  cases hd : (nextRecord rate rewards C_star C_h u t z hq).output.preparation.coordinator
    <;> try trivial
  rename_i out
  cases out <;> try trivial
  · simp only [hd] at h
    obtain ⟨states, memories, ho⟩ := h
    exact ⟨states, memories, fun i => (ho i).1, fun _ i => (ho i).2⟩
  · simp only [hd] at h
    obtain ⟨states, memories, ho⟩ := h
    exact ⟨states, memories, ho, by intro hfalse; cases hfalse⟩

/-- Actual preparations at every equal-prefix source share the SAME
successful lifecycle output, including lastDown and complete proposal memory.
Each ordinary family is produced anew from its own genuine source member. -/
theorem next_followers_prior (control0 : ContinuousLearningRows.TimeControl p)
    (z z' : Z) (hq : t.val + 1 < p.T)
    (hprefix : sourcePrefix control0 (t.val + 1) z.val =
      sourcePrefix control0 (t.val + 1) z'.val) :
    match nextTag rate rewards C_star C_h u t z hq with
    | some (.inr (.inr (.inr (_, cutoff)))) =>
      ∃ states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta,
      ∃ memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p,
        (∀ i, ((nextRecord rate rewards C_star C_h u t z hq).output.preparation.followers.followers i).configuration =
          .ordinary (states i) (memories i)) ∧
        (∀ i, ((nextRecord rate rewards C_star C_h u t z' hq).output.preparation.followers.followers i).configuration =
          .ordinary (states i) (memories i)) ∧
        (cutoff = true → ∀ i, (states i).status = .unoccupied) ∧
        ∀ i, ∃ before beforeMemory,
          (nextRecord rate rewards C_star C_h u t z hq).input.state.followers i = .ordinary before beforeMemory ∧
          (nextRecord rate rewards C_star C_h u t z' hq).input.state.followers i = .ordinary before beforeMemory ∧
          ActiveFollowerLifecycle.startRound rate.eta ⟨t.val + 1, hq⟩ before beforeMemory =
            .ok (states i, memories i) ∧
          (states i).lastDown = before.lastDown
    | _ => True := by
  have he := nextPrior_congr rate rewards C_star C_h u t control0 z z' hq hprefix
  have h0 := nextTag_ordinary rate rewards C_star C_h u t z hq
  have h1 := nextTag_ordinary rate rewards C_star C_h u t z' hq
  rw [← he.1] at h1
  cases ht : nextTag rate rewards C_star C_h u t z hq with
  | none => trivial
  | some tag =>
    cases tag with
    | inl failure => trivial
    | inr tag =>
      cases tag with
      | inl failure => trivial
      | inr tag =>
        cases tag with
        | inl failure => trivial
        | inr chosen =>
          simp only [ht] at h0 h1
          obtain ⟨states, memories, ho, hu⟩ := h0
          obtain ⟨states', memories', ho', _⟩ := h1
          have hs := nextState_congr rate rewards C_star C_h u t control0 hq z z' hprefix
          have htime := (nextRecord_fields rate rewards C_star C_h u t z hq).1.trans
            (nextRecord_fields rate rewards C_star C_h u t z' hq).1.symm
          have hp : ∀ i, states i = states' i ∧ memories i = memories' i := by
            intro i
            have hL := ho i
            have hR := ho' i
            rw [(nextRecord rate rewards C_star C_h u t z hq).output_eq] at hL
            rw [(nextRecord rate rewards C_star C_h u t z' hq).output_eq] at hR
            exact ordinary_preparation_congr _ _ hs htime i _ _ _ _ hL hR
          refine ⟨states, memories, ho, ?_, hu, ?_⟩
          · intro i
            rw [(hp i).1, (hp i).2]
            exact ho' i
          · intro i
            obtain ⟨before, beforeMemory, hin, hstart, hdown, _⟩ :=
              next_ordinary_startRound rate rewards C_star C_h u t z hq i _ _ (ho i)
            rw [(nextRecord_fields rate rewards C_star C_h u t z hq).1] at hstart
            exact ⟨before, beforeMemory, hin, by rw [← hs]; exact hin, hstart, hdown⟩

/-- Replacing one next control also keeps the exact strict prefix. -/
theorem withNextControl_prefix (control0 : ContinuousLearningRows.TimeControl p)
    (z : Z) (hq : t.val + 1 < p.T) (control : ContinuousLearningRows.TimeControl p) :
    sourcePrefix control0 (t.val + 1)
        (withNextControl rate rewards C_star C_h u t z hq control).val =
      sourcePrefix control0 (t.val + 1) z.val := by
  apply Prod.ext
  · refine Prod.ext rfl ?_
    funext row
    by_cases hr : row = ActualInitializationPhysicalStep.selectedRowIndex p z.val
    · subst row
      simp only [sourcePrefix, withNextControl,
        ReferenceFixedTimeSourceControlCoupling.replaceSourceControl,
        ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex,
        ActualInitializationPhysicalStep.selectedRowIndex, Function.update_self]
      refine Prod.ext rfl ?_
      funext v
      by_cases hv : v.val < t.val + 1
      · have hne : v ≠ (⟨t.val + 1, hq⟩ : Fin p.T) := by
          intro h
          exact (Nat.ne_of_lt hv) (congrArg Fin.val h)
        simp only [hv, ite_true, Function.update_of_ne hne]
      · simp only [hv, ite_false]
    · have hr' : row ≠ PrivateSourceStreams.coordinatorIndex p z.val.2.1.2 := hr
      simp only [sourcePrefix, withNextControl,
        ReferenceFixedTimeSourceControlCoupling.replaceSourceControl,
        ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex,
        ActualInitializationPhysicalStep.selectedRowIndex, Function.update_of_ne hr']
  · rfl

/-- The coarse tag and literal numerical parameters are invariant under all
selected suffix coordinates, including the next control itself. -/
theorem nextPrior_replaceSuffix (control0 : ContinuousLearningRows.TimeControl p)
    (z : Z) (hq : t.val + 1 < p.T)
    (suffix : Fin p.T → ContinuousLearningRows.TimeControl p) :
    nextTag rate rewards C_star C_h u t z hq =
        nextTag rate rewards C_star C_h u t (withNextSuffix rate rewards C_star C_h u t z hq suffix) hq ∧
    nextDownView rate rewards C_star C_h u t z hq =
        nextDownView rate rewards C_star C_h u t (withNextSuffix rate rewards C_star C_h u t z hq suffix) hq ∧
    nextParameters rate rewards C_star C_h u t z hq =
        nextParameters rate rewards C_star C_h u t (withNextSuffix rate rewards C_star C_h u t z hq suffix) hq :=
  nextPrior_congr rate rewards C_star C_h u t control0 z _ hq
    (withNextSuffix_prefix rate rewards C_star C_h u t control0 z hq suffix).symm

/-- The same statement for every arbitrary replacement of the whole q control. -/
theorem nextPrior_replaceControl (control0 : ContinuousLearningRows.TimeControl p)
    (z : Z) (hq : t.val + 1 < p.T) (control : ContinuousLearningRows.TimeControl p) :
    nextTag rate rewards C_star C_h u t z hq =
        nextTag rate rewards C_star C_h u t (withNextControl rate rewards C_star C_h u t z hq control) hq ∧
    nextDownView rate rewards C_star C_h u t z hq =
        nextDownView rate rewards C_star C_h u t (withNextControl rate rewards C_star C_h u t z hq control) hq ∧
    nextParameters rate rewards C_star C_h u t z hq =
        nextParameters rate rewards C_star C_h u t (withNextControl rate rewards C_star C_h u t z hq control) hq :=
  nextPrior_congr rate rewards C_star C_h u t control0 z _ hq
    (withNextControl_prefix rate rewards C_star C_h u t control0 z hq control).symm

/-- A literal observed cutoff/collection tag; it is never inferred from
current arm choice, feedback, or the marker. -/
def isCutoffTag : Option (LiveTag p) → Bool
  | some (.inr (.inr (.inr (_, cutoff)))) => cutoff
  | _ => false

/-- Chosen presence is an observation of the exact coarse tag. -/
def isChosenTag : Option (LiveTag p) → Bool
  | some (.inr (.inr (.inr _))) => true
  | _ => false

private theorem chosenCase {A : Prop} (tag : Option (LiveTag p))
    (h : match tag with | some (.inr (.inr (.inr _))) => A | _ => True)
    (hc : isChosenTag tag = true) : A := by
  rcases tag with _ | tag
  · cases hc
  rcases tag with _ | tag
  · cases hc
  rcases tag with _ | tag
  · cases hc
  rcases tag with _ | chosen
  · cases hc
  exact h

private theorem absentCase {A : Prop} (tag : Option (LiveTag p))
    (h : match tag with | some (.inr (.inr (.inr _))) => True | _ => A)
    (hc : isChosenTag tag ≠ true) : A := by
  rcases tag with _ | tag
  · exact h
  rcases tag with _ | tag
  · exact h
  rcases tag with _ | tag
  · exact h
  rcases tag with _ | chosen
  · exact h
  exact False.elim (hc rfl)

/-- Optional recording view: exact numerical presence and parameters,
actual sender payload/anchor/rate/current weights, and the actual pending and
complete status snapshot on continuing. A cutoff has collection regime
(`none` in the snapshot coordinate). Outer absence has no fallback view. -/
def nextRecordingView (z : Z) (hq : t.val + 1 < p.T) :=
  (nextDownView rate rewards C_star C_h u t z hq).map fun view =>
    (nextParameters rate rewards C_star C_h u t z hq, view,
      if isCutoffTag (nextTag rate rewards C_star C_h u t z hq) then
        (none : Option (Finset (Fin (p.m - 1)) × (Fin (p.m - 1) → Option (Fin 3))))
      else some (view.pendingAtChoice, nextStatuses rate rewards C_star C_h u t z hq))

/-- A successful observed view has a chosen coarse tag. This retains every
failed/rejected constructor on the complement. -/
theorem nextDownView_chosen (z : Z) (hq : t.val + 1 < p.T) :
    match nextTag rate rewards C_star C_h u t z hq with
    | some (.inr (.inr (.inr _))) => True
    | _ => nextDownView rate rewards C_star C_h u t z hq = none := by
  rw [nextTag_eq]
  have hp := nextRecord_dispatch_phase rate rewards C_star C_h u t z hq
  unfold nextDownView
  cases hd : (nextRecord rate rewards C_star C_h u t z hq).output.preparation.coordinator
    <;> simp only [hd] at hp
  · rename_i out
    cases out <;> simp only [outcomeData, eraseArm, DispatchCut.downView, DispatchCut.selection,
      Option.map_none]
  · rfl


/-- Prior equality of the complete actual status vector on chosen branches. -/
theorem nextStatuses_prior (control0 : ContinuousLearningRows.TimeControl p)
    (z z' : Z) (hq : t.val + 1 < p.T)
    (hprefix : sourcePrefix control0 (t.val + 1) z.val =
      sourcePrefix control0 (t.val + 1) z'.val) :
    match nextTag rate rewards C_star C_h u t z hq with
    | some (.inr (.inr (.inr _))) =>
      nextStatuses rate rewards C_star C_h u t z hq = nextStatuses rate rewards C_star C_h u t z' hq
    | _ => True := by
  have hf := next_followers_prior rate rewards C_star C_h u t control0 z z' hq hprefix
  generalize ht : nextTag rate rewards C_star C_h u t z hq = tag at hf ⊢
  rcases tag with _ | tag
  · trivial
  rcases tag with _ | tag
  · trivial
  rcases tag with _ | tag
  · trivial
  rcases tag with _ | chosen
  · trivial
  obtain ⟨states, memories, ho, ho', _⟩ := hf
  funext i
  simp only [nextStatuses, ho i, ho' i]

private theorem optionalView_congr
    (tag : Option (LiveTag p)) (parameters : Option (Bool × (Fin p.K → ℝ)))
    (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (statuses statuses' : Fin (p.m - 1) → Option (Fin 3))
    (hfail : isChosenTag tag ≠ true → view = none)
    (hs : isChosenTag tag = true → statuses = statuses') :
    view.map (fun v => (parameters, v, if isCutoffTag tag then
      (none : Option (Finset (Fin (p.m - 1)) × (Fin (p.m - 1) → Option (Fin 3))))
      else some (v.pendingAtChoice, statuses))) =
    view.map (fun v => (parameters, v, if isCutoffTag tag then
      (none : Option (Finset (Fin (p.m - 1)) × (Fin (p.m - 1) → Option (Fin 3))))
      else some (v.pendingAtChoice, statuses'))) := by
  by_cases hc : isChosenTag tag = true
  · rw [hs hc]
  · rw [hfail hc]
    rfl

/-- The literal optional recording view is equal at equal strict prefixes.
Actual ordinary inputs are produced and discharged inside the proof. -/
theorem nextRecordingView_congr (control0 : ContinuousLearningRows.TimeControl p)
    (z z' : Z) (hq : t.val + 1 < p.T)
    (hprefix : sourcePrefix control0 (t.val + 1) z.val =
      sourcePrefix control0 (t.val + 1) z'.val) :
    nextRecordingView rate rewards C_star C_h u t z hq =
      nextRecordingView rate rewards C_star C_h u t z' hq := by
  have he := nextPrior_congr rate rewards C_star C_h u t control0 z z' hq hprefix
  have hs := nextStatuses_prior rate rewards C_star C_h u t control0 z z' hq hprefix
  have hv := nextDownView_chosen rate rewards C_star C_h u t z hq
  unfold nextRecordingView
  rw [← he.1, ← he.2.1, ← he.2.2]
  exact optionalView_congr rate _ _ _ _ _
    (fun hc => absentCase _ hv hc) (fun hc => chosenCase _ hs hc)

/-- Factorization through the existing next-prior observer on original Z. -/
theorem nextRecordingView_factor (control0 : ContinuousLearningRows.TimeControl p)
    (z : Z) (hq : t.val + 1 < p.T) :
    nextRecordingView rate rewards C_star C_h u t z hq =
      nextRecordingView rate rewards C_star C_h u t
        (ReferenceFirstCollectionRenewalNextPriorReadout.nextPriorObserver
          rate rewards C_star C_h u t control0 z) hq := by
  apply nextRecordingView_congr rate rewards C_star C_h u t control0
  rw [ReferenceFirstCollectionRenewalNextPriorReadout.nextPriorObserver_val,
    sourcePrefix_sourcePrefix control0 _ _ le_rfl]

/-- Ambient Borel evidence uses the sole canonical sender and follower codes;
continuous payloads, anchors, and weight vectors retain their original spaces. -/
theorem measurable_nextRecordingView_ambient (control0 : ContinuousLearningRows.TimeControl p)
    (hq : t.val + 1 < p.T) :
    Measurable (fun z : Z => nextRecordingView rate rewards C_star C_h u t z hq) := by
  have hle := ReferenceFirstCollectionRenewalNextControlLaw.nextPriorField_le
    rate rewards C_star C_h u t control0
  have hp : Measurable (fun z : Z => nextParameters rate rewards C_star C_h u t z hq) :=
    (measurable_nextParameters rate rewards C_star C_h u t control0 hq).mono hle le_rfl
  have hv : Measurable (fun z : Z => nextDownView rate rewards C_star C_h u t z hq) :=
    (measurable_nextDownView rate rewards C_star C_h u t control0 hq).mono hle le_rfl
  have ht : Measurable (fun z : Z => nextTag rate rewards C_star C_h u t z hq) :=
    (measurable_nextTag rate rewards C_star C_h u t control0 hq).mono hle le_rfl
  have hm : Measurable (fun view : ReferenceDownReception.ChoiceTimeView p rate.eta =>
      view.pendingAtChoice) :=
    measurable_fst.comp (measurable_snd.comp (comap_measurable
      (ReferenceDownReceptionMeasurability.choiceTimeViewObservation (p := p) (rate := rate))))
  have hs := measurable_nextStatuses rate rewards C_star C_h u t hq
  have hcut : Measurable (fun v : ReferenceDownReception.ChoiceTimeView p rate.eta × Z =>
      isCutoffTag (nextTag rate rewards C_star C_h u t v.2 hq)) :=
    ((measurable_of_countable isCutoffTag).comp ht).comp measurable_snd
  have hsnap : Measurable (fun v : ReferenceDownReception.ChoiceTimeView p rate.eta × Z =>
      if isCutoffTag (nextTag rate rewards C_star C_h u t v.2 hq) then
        (none : Option (Finset (Fin (p.m - 1)) × (Fin (p.m - 1) → Option (Fin 3))))
      else some (v.1.pendingAtChoice, nextStatuses rate rewards C_star C_h u t v.2 hq)) :=
    (measurable_of_countable (fun key : Bool ×
      (Finset (Fin (p.m - 1)) × (Fin (p.m - 1) → Option (Fin 3))) =>
        if key.1 then none else some key.2)).comp
      (hcut.prodMk ((hm.comp measurable_fst).prodMk (hs.comp measurable_snd)))
  have hformula : Measurable (fun v : ReferenceDownReception.ChoiceTimeView p rate.eta × Z =>
      (nextParameters rate rewards C_star C_h u t v.2 hq, v.1,
        if isCutoffTag (nextTag rate rewards C_star C_h u t v.2 hq) then
          (none : Option (Finset (Fin (p.m - 1)) × (Fin (p.m - 1) → Option (Fin 3))))
        else some (v.1.pendingAtChoice, nextStatuses rate rewards C_star C_h u t v.2 hq))) :=
    (hp.comp measurable_snd).prodMk (measurable_fst.prodMk hsnap)
  exact ReferenceCollectionInstallOutputMeasurability.measurable_optionMapDependent _ hformula _ hv

/-- Borel measurability in Fq follows from the actual source equality, rather
than from an ambient PREPARE measurability assertion alone. -/
theorem measurable_nextRecordingView (control0 : ContinuousLearningRows.TimeControl p)
    (hq : t.val + 1 < p.T) :
    Measurable[ReferenceFirstCollectionRenewalNextControlLaw.nextPriorField
      rate rewards C_star C_h u t control0]
      (fun z : Z => nextRecordingView rate rewards C_star C_h u t z hq) := by
  have heq : (fun z : Z => nextRecordingView rate rewards C_star C_h u t z hq) =
      fun z => nextRecordingView rate rewards C_star C_h u t
        (ReferenceFirstCollectionRenewalNextPriorReadout.nextPriorObserver
          rate rewards C_star C_h u t control0 z) hq := by
    funext z
    exact nextRecordingView_factor rate rewards C_star C_h u t control0 z hq
  rw [heq]
  exact (measurable_nextRecordingView_ambient rate rewards C_star C_h u t control0 hq).comp
    (ReferenceFirstCollectionRenewalNextControlLaw.measurable_nextPriorObserver_field
      rate rewards C_star C_h u t control0)

/-- Actual first-next views are invariant under every selected suffix change. -/
theorem nextRecordingView_replaceSuffix (control0 : ContinuousLearningRows.TimeControl p)
    (z : Z) (hq : t.val + 1 < p.T)
    (suffix : Fin p.T → ContinuousLearningRows.TimeControl p) :
    nextRecordingView rate rewards C_star C_h u t z hq =
      nextRecordingView rate rewards C_star C_h u t
        (withNextSuffix rate rewards C_star C_h u t z hq suffix) hq :=
  nextRecordingView_congr rate rewards C_star C_h u t control0 z _ hq
    (withNextSuffix_prefix rate rewards C_star C_h u t control0 z hq suffix).symm

/-- Actual first-next views are invariant under every whole next-control change. -/
theorem nextRecordingView_replaceControl (control0 : ContinuousLearningRows.TimeControl p)
    (z : Z) (hq : t.val + 1 < p.T) (control : ContinuousLearningRows.TimeControl p) :
    nextRecordingView rate rewards C_star C_h u t z hq =
      nextRecordingView rate rewards C_star C_h u t
        (withNextControl rate rewards C_star C_h u t z hq control) hq :=
  nextRecordingView_congr rate rewards C_star C_h u t control0 z _ hq
    (withNextControl_prefix rate rewards C_star C_h u t control0 z hq control).symm

/-- Joint factorization of the actual replaced-source observation through e;
the whole replacement control remains a separate current coordinate. -/
theorem nextRecordingView_joint_factor (control0 : ContinuousLearningRows.TimeControl p)
    (z : Z) (hq : t.val + 1 < p.T) (control : ContinuousLearningRows.TimeControl p) :
    nextRecordingView rate rewards C_star C_h u t
        (withNextControl rate rewards C_star C_h u t z hq control) hq =
      nextRecordingView rate rewards C_star C_h u t
        (ReferenceFirstCollectionRenewalNextPriorReadout.nextPriorObserver
          rate rewards C_star C_h u t control0 z) hq :=
  (nextRecordingView_replaceControl rate rewards C_star C_h u t control0 z hq control).symm.trans
    (nextRecordingView_factor rate rewards C_star C_h u t control0 z hq)

/-- JOINT measurability on the original next-prior field times the entire
continuous control carrier, with every replaced source admitted separately. -/
theorem measurable_nextRecordingView_joint (control0 : ContinuousLearningRows.TimeControl p)
    (hq : t.val + 1 < p.T) :
    Measurable[(ReferenceFirstCollectionRenewalNextControlLaw.nextPriorField
      rate rewards C_star C_h u t control0).prod
        (inferInstance : MeasurableSpace (ContinuousLearningRows.TimeControl p))]
      (fun v : Z × ContinuousLearningRows.TimeControl p => nextRecordingView
        rate rewards C_star C_h u t (withNextControl rate rewards C_star C_h u t v.1 hq v.2) hq) := by
  have heq : (fun v : Z × ContinuousLearningRows.TimeControl p => nextRecordingView
      rate rewards C_star C_h u t (withNextControl rate rewards C_star C_h u t v.1 hq v.2) hq) =
      fun v => nextRecordingView rate rewards C_star C_h u t v.1 hq := by
    funext v
    exact (nextRecordingView_replaceControl rate rewards C_star C_h u t control0 v.1 hq v.2).symm
  rw [heq]
  exact (measurable_nextRecordingView rate rewards C_star C_h u t control0 hq).comp measurable_fst

private theorem parametersOfTag_isSome (q : Fin p.T) (tag : Option (LiveTag p))
    (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (hfail : isChosenTag tag ≠ true → view = none) :
    (parametersOfTag rate q tag view).isSome = view.isSome := by
  rcases tag with _ | tag
  · rw [hfail (by intro h; cases h)]; rfl
  rcases tag with _ | tag
  · rw [hfail (by intro h; cases h)]; rfl
  rcases tag with _ | tag
  · rw [hfail (by intro h; cases h)]; rfl
  rcases tag with _ | chosen
  · rw [hfail (by intro h; cases h)]; rfl
  cases view <;> rfl

/-- The optional view has EXACTLY the numerical readout's outer presence.
This includes a present disabled cutoff and excludes every failed constructor. -/
theorem nextRecordingView_presence (z : Z) (hq : t.val + 1 < p.T) :
    (nextRecordingView rate rewards C_star C_h u t z hq).isSome =
      (nextCell rate rewards C_star C_h u t z hq).isSome := by
  have he := parametersOfTag_isSome rate ⟨t.val + 1, hq⟩
    (nextTag rate rewards C_star C_h u t z hq) (nextDownView rate rewards C_star C_h u t z hq)
    (fun hc => absentCase _ (nextDownView_chosen rate rewards C_star C_h u t z hq) hc)
  rw [← nextParameters_eq rate rewards C_star C_h u t z hq] at he
  simpa only [nextRecordingView, nextParameters, Option.isSome_map] using he.symm

/-- The sender payload is the very installation in the original renewal
record, on every surviving chosen branch, without any tail-success premise. -/
theorem nextDownView_installed_payload (z : Z) (hq : t.val + 1 < p.T) :
    match (callRecord rate rewards C_star C_h u t z).output.preparation.coordinator with
    | .collection _ _ _ _ (.laterChosen _ _ _ _ _ _ _ _ _ installed _) =>
      match nextDownView rate rewards C_star C_h u t z hq with
      | none => True
      | some view => view.payload = installed.registers.payload
    | _ => False := by
  have hi := nextRecord_installed_payload rate rewards C_star C_h u t z hq
  have hp := nextRecord_dispatch_phase rate rewards C_star C_h u t z hq
  cases hb : (callRecord rate rewards C_star C_h u t z).output.preparation.coordinator
    <;> simp only [hb] at hi ⊢
  rename_i out
  cases out <;> try contradiction
  unfold nextDownView
  cases hd : (nextRecord rate rewards C_star C_h u t z hq).output.preparation.coordinator
    <;> simp only [hd] at hp hi
  · rename_i out
    cases out <;> simp only [DispatchCut.downView, DispatchCut.selection, selectionAt,
      dite_true, Option.map_some, Option.map_none]
    all_goals trivial
  · trivial

/-- Canonical rates, anchor, current weights, pending set and original payload
are all present in the actual view; this rate equality is not an assumption. -/
theorem nextView_rate_canonical (z : Z) (hq : t.val + 1 < p.T)
    (view : ReferenceDownReception.ChoiceTimeView p rate.eta)
    (_hview : nextDownView rate rewards C_star C_h u t z hq = some view) (a : Fin p.K) :
    view.payload.rate a = CanonicalRecordingRates.xi p rate.eta.val view.payload.anchor a :=
  view.payload.rate_eq_canonical a

/-- Every present numerical cell's actual rate is the sender payload's
canonical rate. This does not assert a physical queue/analytical queue identity. -/
theorem nextCell_rate_canonical (z : Z) (hq : t.val + 1 < p.T) :
    match nextCell rate rewards C_star C_h u t z hq with
    | none => True
    | some c => ∃ view : ReferenceDownReception.ChoiceTimeView p rate.eta,
      nextDownView rate rewards C_star C_h u t z hq = some view ∧
      c.rate = view.payload.rate ∧
      ∀ a, c.rate a = CanonicalRecordingRates.xi p rate.eta.val view.payload.anchor a := by
  cases hc : nextCell rate rewards C_star C_h u t z hq with
  | none => trivial
  | some c =>
    have he : nextParameters rate rewards C_star C_h u t z hq = some (c.enabled, c.rate) := by
      simp only [nextParameters, hc, Option.map_some]
    rw [nextParameters_eq] at he
    generalize ht : nextTag rate rewards C_star C_h u t z hq = tag at he
    rcases tag with _ | tag
    · cases he
    rcases tag with _ | tag
    · cases he
    rcases tag with _ | tag
    · cases he
    rcases tag with _ | chosen
    · cases he
    cases hv : nextDownView rate rewards C_star C_h u t z hq with
    | none => simp only [parametersOfTag, Option.bind_some, hv, Option.map_none, reduceCtorEq] at he
    | some view =>
      simp only [parametersOfTag, Option.bind_some, hv, Option.map_some, Option.some.injEq] at he
      have hr : c.rate = view.payload.rate := (Prod.mk.inj he).2.symm
      exact ⟨view, rfl, hr, fun a => (congrFun hr a).trans (view.payload.rate_eq_canonical a)⟩

/-- Only the impossible clock-failure constructor is removed. Initializer
and local failures, their exact reasons, and dagger absence remain tagged. -/
theorem nextTag_no_clockFailure (z : Z) (hq : t.val + 1 < p.T) :
    match nextTag rate rewards C_star C_h u t z hq with
    | some (.inl _) => False
    | _ => True := by
  have h := nextRecord_no_clockFailure rate rewards C_star C_h u t z hq
  rw [nextTag_eq]
  cases hd : (nextRecord rate rewards C_star C_h u t z hq).output.preparation.coordinator
    <;> try trivial
  rename_i out
  cases out <;> try trivial
  simp only [hd] at h

/-- Actual continuing source cells identify this observation with the
complete ownership snapshot consumed by SnapshotRecordingKernel. -/
theorem next_continuing_snapshot (z : Z) (hq : t.val + 1 < p.T) :
    let r := nextRecord rate rewards C_star C_h u t z hq
    match r.output.preparation.coordinator with
    | .live _ _ _ (.continuingChosen ..) =>
      ∃ cell : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell r,
        nextLive rate rewards C_star C_h u t z hq = some cell.input ∧
        nextDownView rate rewards C_star C_h u t z hq = some cell.selected.view ∧
        cell.selected.view.pendingAtChoice =
          (ReferenceActiveDataOwnership.choiceSnapshot cell.selected cell.states).missing ∧
        (∀ i, nextStatuses rate rewards C_star C_h u t z hq i = some
          (FollowerDownMeasurability.followerStatusCode
            ((ReferenceActiveDataOwnership.choiceSnapshot cell.selected cell.states).status i))) ∧
        cell.input.rate = cell.selected.view.payload.rate
    | _ => True := by
  have h := next_continuing_physical rate rewards C_star C_h u t z hq
  dsimp only at h ⊢
  cases hd : (nextRecord rate rewards C_star C_h u t z hq).output.preparation.coordinator
    <;> try trivial
  rename_i out
  cases out <;> try trivial
  simp only [hd] at h
  obtain ⟨cell, hL, _, _, _, hr, _⟩ := h
  refine ⟨cell, hL, ?_, cell.selected.pending_eq, ?_, hr⟩
  · simp only [nextDownView, DispatchCut.downView, cell.selection_actual, Option.map_some]
  · intro i
    simp only [nextStatuses, cell.ordinary i, configurationStatus,
      ReferenceActiveDataOwnership.choiceSnapshot]

/-- Literal canonical payload code together with the existing pending,
cutoff, and full weight coordinates. Every real coordinate has its product
Borel space; only finite/discrete observations have discrete spaces. -/
def recordingViewCode (view : ReferenceDownReception.ChoiceTimeView p rate.eta) :=
  (LaterAssignmentStartMeasurability.payloadObservation view.payload,
    (ReferenceDownReceptionMeasurability.choiceTimeViewObservation view).2)

theorem measurable_recordingViewCode : Measurable (recordingViewCode rate) := by
  have hobs : Measurable (ReferenceDownReceptionMeasurability.choiceTimeViewObservation
      (p := p) (rate := rate)) := comap_measurable _
  exact ((comap_measurable (LaterAssignmentStartMeasurability.payloadObservation
    (p := p) (eta := rate.eta))).comp (measurable_fst.comp hobs)).prodMk
      (measurable_snd.comp hobs)

/-- The same optional recording observation in the established canonical
payload coordinates, normal real products, and finite snapshot coordinates. -/
def nextRecordingCode (z : Z) (hq : t.val + 1 < p.T) :=
  (nextRecordingView rate rewards C_star C_h u t z hq).map fun observed =>
    (observed.1, recordingViewCode rate observed.2.1, observed.2.2)

theorem nextRecordingCode_factor (control0 : ContinuousLearningRows.TimeControl p)
    (z : Z) (hq : t.val + 1 < p.T) :
    nextRecordingCode rate rewards C_star C_h u t z hq =
      nextRecordingCode rate rewards C_star C_h u t
        (ReferenceFirstCollectionRenewalNextPriorReadout.nextPriorObserver
          rate rewards C_star C_h u t control0 z) hq := by
  unfold nextRecordingCode
  rw [nextRecordingView_factor rate rewards C_star C_h u t control0 z hq]

theorem measurable_nextRecordingCode (control0 : ContinuousLearningRows.TimeControl p)
    (hq : t.val + 1 < p.T) :
    Measurable[ReferenceFirstCollectionRenewalNextControlLaw.nextPriorField
      rate rewards C_star C_h u t control0]
      (fun z : Z => nextRecordingCode rate rewards C_star C_h u t z hq) := by
  let : MeasurableSpace Z := ReferenceFirstCollectionRenewalNextControlLaw.nextPriorField
    rate rewards C_star C_h u t control0
  exact LaterAssignmentFullOutputMeasurability.measurable_optionMap _
    (measurable_fst.prodMk
      (((measurable_recordingViewCode rate).comp (measurable_fst.comp measurable_snd)).prodMk
        (measurable_snd.comp measurable_snd))) _
    (measurable_nextRecordingView rate rewards C_star C_h u t control0 hq)

theorem nextRecordingCode_replaceControl (control0 : ContinuousLearningRows.TimeControl p)
    (z : Z) (hq : t.val + 1 < p.T) (control : ContinuousLearningRows.TimeControl p) :
    nextRecordingCode rate rewards C_star C_h u t
        (withNextControl rate rewards C_star C_h u t z hq control) hq =
      nextRecordingCode rate rewards C_star C_h u t z hq := by
  unfold nextRecordingCode
  rw [← nextRecordingView_replaceControl rate rewards C_star C_h u t control0 z hq control]

theorem measurable_nextRecordingCode_joint (control0 : ContinuousLearningRows.TimeControl p)
    (hq : t.val + 1 < p.T) :
    Measurable[(ReferenceFirstCollectionRenewalNextControlLaw.nextPriorField
      rate rewards C_star C_h u t control0).prod
        (inferInstance : MeasurableSpace (ContinuousLearningRows.TimeControl p))]
      (fun v : Z × ContinuousLearningRows.TimeControl p => nextRecordingCode
        rate rewards C_star C_h u t (withNextControl rate rewards C_star C_h u t v.1 hq v.2) hq) := by
  have heq : (fun v : Z × ContinuousLearningRows.TimeControl p => nextRecordingCode
      rate rewards C_star C_h u t (withNextControl rate rewards C_star C_h u t v.1 hq v.2) hq) =
      fun v => nextRecordingCode rate rewards C_star C_h u t v.1 hq := by
    funext v
    exact nextRecordingCode_replaceControl rate rewards C_star C_h u t control0 v.1 hq v.2
  rw [heq]
  exact (measurable_nextRecordingCode rate rewards C_star C_h u t control0 hq).comp measurable_fst

end Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingPriorView

end
