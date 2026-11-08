/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionUpConditionalService
public import Bandits.Support.ReferenceFirstCollectionStreamEmptyDispatch

/-!
# Formed UP service at the actual first cutoff

Internal first-cutoff results on the original complete source and whole reward
table. Incoming LIVE followers may be occupied. PREPARE resets their status,
retaining their fields; only a reply already formed before this choice counts.

Sources: `sources/zip4/manuscript/06_interruptions.tex:477-481`,
`05_binary_transport.tex:27-53,70-88,94-124`, and
`appendix_a_local_protocol.tex:54-64,108,151-157`.
No quota, decoder-error estimate, or manuscript-filtration claim is made here.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions
open MeasureTheory
open scoped ENNReal Classical

namespace Bandits.Support.ReferenceFirstCutoffUpConditionalService


abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev SourceInput := BootstrapPrivateRoundStreams.SourceInput
abbrev RewardTable := ActualInitializationPhysicalStep.GridRewardTable
abbrev TimeControl := ContinuousLearningRows.TimeControl

variable {p : Parameters} {rate : RateInput p}

private def liveCutoffTag
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ) (row : CompletePublicTable.CompleteRow p)
    (out : CoordinatorRoundDispatch.LiveOutcome
      { eta := rate.eta, registers := r, ownedRegisters := q,
        followerBaseScore := base, row := row }) : Bool :=
  match out with
  | .cutoffChosen _ _ _ _ _ _ _ _ _ _ => true
  | _ => false

private theorem liveCutoffTag_projection
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ) (row : CompletePublicTable.CompleteRow p)
    (out : CoordinatorRoundDispatch.LiveOutcome
      { eta := rate.eta, registers := r, ownedRegisters := q,
        followerBaseScore := base, row := row }) :
    liveCutoffTag r q base row out =
      (match (ReferenceActiveDispatchTemporal.liveOutcomeData r q base row out).2.2 with
      | .inr (.inr (.inr _)) => true
      | _ => false) := by
  cases out <;> rfl

private theorem cutoffChosen_live
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ)
    (hphase : x.state.coordinator = .live r q base) :
    ReferenceCollectionPhaseHistory.cutoffChosen x =
      liveCutoffTag (ReferenceActivePhysicalStep.liveRegistersAt r x.time) (ReferenceActivePhysicalStep.liveOwnedAt r q x.time)
        base x.row (CoordinatorRoundDispatch.dispatchLive (ReferenceActivePhysicalStep.liveInput x r q base)) := by
  dsimp only [ReferenceCollectionPhaseHistory.cutoffChosen, ReferenceActivePhysicalStep.prepare, ReferenceActivePhysicalStep.dispatch]
  simp only [hphase, CoordinatorRoundDispatch.dispatch]
  cases CoordinatorRoundDispatch.dispatchLive (ReferenceActivePhysicalStep.liveInput x r q base) <;> rfl

/-- The cutoff tag depends on clock and domain checks, whereas the successful
CHOICE is recomputed on each current row. -/
private theorem liveCutoffTag_row_independent
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ) (row row' : CompletePublicTable.CompleteRow p) :
    liveCutoffTag r q base row (CoordinatorRoundDispatch.dispatchLive
      { eta := rate.eta, registers := r, ownedRegisters := q,
        followerBaseScore := base, row := row }) =
    liveCutoffTag r q base row' (CoordinatorRoundDispatch.dispatchLive
      { eta := rate.eta, registers := r, ownedRegisters := q,
        followerBaseScore := base, row := row' }) := by
  classical
  unfold CoordinatorRoundDispatch.dispatchLive
  dsimp only
  split
  · rfl
  · rename_i dispatched hdispatch
    split
    · rfl
    · rfl
    · rename_i hinit
      conv_lhs => rw [apply_dite (liveCutoffTag r q base row)]
      conv_rhs => rw [apply_dite (liveCutoffTag r q base row')]
      congr 1
      funext h11
      conv_lhs => rw [apply_dite (liveCutoffTag r q base row)]
      conv_rhs => rw [apply_dite (liveCutoffTag r q base row')]
      congr 1
      funext h10
      conv_lhs => rw [apply_dite (liveCutoffTag r q base row)]
      conv_rhs => rw [apply_dite (liveCutoffTag r q base row')]
      congr 1
      funext h9
      conv_lhs => rw [apply_dite (liveCutoffTag r q base row)]
      conv_rhs => rw [apply_dite (liveCutoffTag r q base row')]
      congr 1
      funext h8
      conv_lhs => rw [apply_dite (liveCutoffTag r q base row)]
      conv_rhs => rw [apply_dite (liveCutoffTag r q base row')]
      congr 1
      funext h7
      conv_lhs => rw [apply_dite (liveCutoffTag r q base row)]
      conv_rhs => rw [apply_dite (liveCutoffTag r q base row')]
      congr 1
      funext h6
      conv_lhs => rw [apply_dite (liveCutoffTag r q base row)]
      conv_rhs => rw [apply_dite (liveCutoffTag r q base row')]
      congr 1
      funext h5
      conv_lhs => rw [apply_dite (liveCutoffTag r q base row)]
      conv_rhs => rw [apply_dite (liveCutoffTag r q base row')]
      congr 1
      funext h4
      conv_lhs => rw [apply_dite (liveCutoffTag r q base row)]
      conv_rhs => rw [apply_dite (liveCutoffTag r q base row')]
      congr 1
      funext h3
      conv_lhs => rw [apply_dite (liveCutoffTag r q base row)]
      conv_rhs => rw [apply_dite (liveCutoffTag r q base row')]
      congr 1
      funext h2
      conv_lhs => rw [apply_dite (liveCutoffTag r q base row)]
      conv_rhs => rw [apply_dite (liveCutoffTag r q base row')]
      congr 1
      funext h1
      split
      · rename_i hselected
        exact False.elim (CoordinatorLiveChoiceRecorderStep.coordinatorArmChoice_ne_none
          r.payload dispatched.startResult.pending
          (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p dispatched.startResult.clock.u)
          r.time r.complementWeights row (by assumption) hselected)
      · split
        · rename_i hselected
          exact False.elim (CoordinatorLiveChoiceRecorderStep.coordinatorArmChoice_ne_none
            r.payload dispatched.startResult.pending
            (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p dispatched.startResult.clock.u)
            r.time r.complementWeights row' (by assumption) hselected)
        · rfl
    · rename_i ledger hinit
      conv_lhs => rw [apply_dite (liveCutoffTag r q base row)]
      conv_rhs => rw [apply_dite (liveCutoffTag r q base row')]
      congr 1
      funext h3
      conv_lhs => rw [apply_dite (liveCutoffTag r q base row)]
      conv_rhs => rw [apply_dite (liveCutoffTag r q base row')]
      congr 1
      funext h2
      conv_lhs => rw [apply_dite (liveCutoffTag r q base row)]
      conv_rhs => rw [apply_dite (liveCutoffTag r q base row')]
      congr 1
      funext h1
      split
      · rename_i hselected
        exact False.elim (CoordinatorLiveChoiceRecorderStep.coordinatorArmChoice_ne_none
          r.payload dispatched.startResult.pending
          (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p dispatched.startResult.clock.u)
          r.time r.complementWeights row (by assumption) hselected)
      · split
        · rename_i hselected
          exact False.elim (CoordinatorLiveChoiceRecorderStep.coordinatorArmChoice_ne_none
            r.payload dispatched.startResult.pending
            (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p dispatched.startResult.clock.u)
            r.time r.complementWeights row' (by assumption) hselected)
        · rfl

private theorem cutoffChosen_withControl (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ)
    (hphase : x.state.coordinator = .live r q base) (c : TimeControl p) :
    ReferenceCollectionPhaseHistory.cutoffChosen
        (ReferenceLaterOptionalControlResampling.withControl x c) =
      ReferenceCollectionPhaseHistory.cutoffChosen x := by
  calc
    _ = _ := cutoffChosen_live (ReferenceLaterOptionalControlResampling.withControl x c)
      r q base hphase
    _ = _ := liveCutoffTag_row_independent (ReferenceActivePhysicalStep.liveRegistersAt r x.time)
      (ReferenceActivePhysicalStep.liveOwnedAt r q x.time) base
      (ReferenceLaterOptionalControlResampling.withControl x c).row x.row
    _ = _ := (cutoffChosen_live x r q base hphase).symm

/-- Equal actual incoming states and equal current slices give equal cutoff
tags. Complete records and future row-table entries need not agree. -/
private theorem cutoffChosen_congr (x y : ReferenceActivePhysicalStep.RoundInput p rate)
    (hstate : x.state = y.state) (htime : x.time = y.time)
    (hcurrent : x.row.2 x.time = y.row.2 y.time) :
    ReferenceCollectionPhaseHistory.cutoffChosen x =
      ReferenceCollectionPhaseHistory.cutoffChosen y := by
  cases x with | mk state rows selected time active rewards =>
  cases y with | mk state' rows' selected' time' active' rewards' =>
  dsimp only at hstate htime hcurrent
  cases hstate
  cases htime
  cases hphase : state.coordinator with
  | first =>
      dsimp only [ReferenceCollectionPhaseHistory.cutoffChosen, ReferenceActivePhysicalStep.prepare, ReferenceActivePhysicalStep.dispatch]
      simp only [hphase, CoordinatorRoundDispatch.dispatch]
      rfl
  | live r q base =>
      have hd := ReferenceActiveDispatchTemporal.liveOutcomeData_eq_of_current
        (ReferenceActivePhysicalStep.liveRegistersAt r time) (ReferenceActivePhysicalStep.liveOwnedAt r q time) base
        (rows selected) (rows' selected') hcurrent
      have ht := congrArg (fun data => match data.2.2 with
        | .inr (.inr (.inr _)) => true | _ => false) hd
      rw [← liveCutoffTag_projection, ← liveCutoffTag_projection] at ht
      rw [cutoffChosen_live _ r q base hphase, cutoffChosen_live _ r q base hphase]
      exact ht
  | collection payload ledger proposal =>
      dsimp only [ReferenceCollectionPhaseHistory.cutoffChosen, ReferenceActivePhysicalStep.prepare, ReferenceActivePhysicalStep.dispatch]
      simp only [hphase]
      by_cases hc : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
      · simp only [dite_eq_left hc, CoordinatorRoundDispatch.dispatch]
        rfl
      · simp only [dite_eq_right hc]
  | dagger =>
      dsimp only [ReferenceCollectionPhaseHistory.cutoffChosen, ReferenceActivePhysicalStep.prepare, ReferenceActivePhysicalStep.dispatch]
      simp only [hphase]

private theorem run_cutoffTags_eq
    (initial : ReferenceActivePhysicalStep.State p rate) (rows otherRows : CompletePublicTable.CompleteRows p)
    (selected : Fin (M p)) (rewards : RewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hcontrols : ∀ j : Fin p.T, start ≤ j.val → j.val < start + count →
      (rows selected).2 j = (otherRows selected).2 j)
    (hbefore : ∀ j : Fin p.T, j.val < start →
      ((rows selected).2 j).1 ContinuousControlSlice.Label.prop =
        ((otherRows selected).2 j).1 ContinuousControlSlice.Label.prop) :
    (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count hspan active).records.map
        (fun record => ReferenceCollectionPhaseHistory.cutoffChosen record.input) =
      (ReferenceActivePhysicalHorizon.run initial otherRows selected rewards start count hspan active).records.map
        (fun record => ReferenceCollectionPhaseHistory.cutoffChosen record.input) := by
  induction count with
  | zero => rw [ReferenceActivePhysicalHorizon.run_zero_records, ReferenceActivePhysicalHorizon.run_zero_records]
  | succ count ih =>
      have hprefix : start + count ≤ p.T := by omega
      have hc : ∀ j : Fin p.T, start ≤ j.val → j.val < start + count →
          (rows selected).2 j = (otherRows selected).2 j :=
        fun j hj hk => hcontrols j hj (by omega)
      have htags := ih hprefix hc
      have hstate := (ReferenceActiveTemporalAssembly.run_eq_of_temporal_reads initial
        rows otherRows selected rewards rewards start count hprefix active
        hc (fun _ _ _ => rfl) (fun _ => hbefore)).1
      rw [ReferenceActivePhysicalHorizon.run_successor_step, ReferenceActivePhysicalHorizon.run_successor_step]
      simp only [ReferenceActivePhysicalHorizon.foldRound, List.map_append, List.map_singleton]
      rw [htags]
      congr 1
      apply congrArg List.singleton
      apply cutoffChosen_congr
      · exact hstate
      · rfl
      · exact hcontrols ⟨start + count, by omega⟩ (by dsimp; omega) (by dsimp; omega)

/-- The incoming state is retained in the actual prefix lookup. -/
private theorem actualRecord_at_cutoff
    (source : SourceInput p) (rewards : RewardTable p) (C_star C_h : ℝ)
    (count : ℕ)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hspan : ReferenceFirstCollectionReadyStream.startTime (rate := rate) source rewards C_star C_h + count ≤ p.T)
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate) source rewards C_star C_h hc count hspan).records).length < count)
    (d : ReferenceFirstCollectionStreamEmptyDispatch.ActualInitializedStreamDispatch source rewards C_star C_h count hc hspan hshort) :
    ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
      d.stream.cutoff.cut.input.time source = some d.stream.cutoff.cut := by
  let initial := ReferenceFirstCollectionEpochAlignment.actualLaunchState
    rate source rewards C_star C_h hc
  let s := ReferenceFirstCollectionReadyStream.startTime (rate := rate) source rewards C_star C_h
  let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
    (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate) source rewards C_star C_h hc count hspan).records).length
  have active := (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
    rate source rewards C_star C_h hc).1
  have hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h = some initial :=
    Option.eq_some_of_isSome ((ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
      rate source rewards C_star C_h).2 hc)
  have htime : d.stream.cutoff.cut.input.time.val = s + w := d.stream.cutoff.cutTime
  have hat := ReferenceLocalReleaseGateChronology.run_record_at initial source.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s active count hspan
    ⟨w, hshort⟩
  have hrecordAt : d.stream.cutoff.cut =
      ReferenceAssignmentPayloadChronology.actualRunRecordAt initial source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s w
        (by omega) active := by
    apply Option.some.inj
    calc
      some d.stream.cutoff.cut = _ := d.stream.cutoff.cutIndex.symm
      _ = _ := by
        rw [List.getElem?_eq_getElem (by
          change w < (ReferenceActivePhysicalHorizon.run initial source.1.2
            (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s count hspan active).records.length
          rw [ReferenceActivePhysicalHorizon.run_record_count]
          exact hshort)]
        exact congrArg some hat
  have hsource := ReferenceSourcePrefixHistoryFiltration.actualRecord_on_launch
    rate rewards C_star C_h d.stream.cutoff.cut.input.time source initial hlaunch
    (by change s ≤ d.stream.cutoff.cut.input.time.val; omega)
  have hsource' : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
      d.stream.cutoff.cut.input.time source = some
        (ReferenceAssignmentPayloadChronology.actualRunRecordAt initial source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s w
          (by omega) active) := by
    simpa only [show ReferenceCompletePhysicalHistory.physicalStart rate source rewards
      C_star C_h = s from rfl, htime, Nat.add_sub_cancel_left] using hsource
  exact hsource'.trans (congrArg some hrecordAt.symm)

/-- All actual incoming followers and their cutoff preparation are produced
before inspecting a formed-reply branch. No incoming collection readiness is used. -/
private theorem actual_cutoff_followers
    (source : SourceInput p) (rewards : RewardTable p) (C_star C_h : ℝ)
    (count : ℕ)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hspan : ReferenceFirstCollectionReadyStream.startTime (rate := rate)
      source rewards C_star C_h + count ≤ p.T)
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
        source rewards C_star C_h hc count hspan).records).length < count)
    (d : ReferenceFirstCollectionStreamEmptyDispatch.ActualInitializedStreamDispatch
      source rewards C_star C_h count hc hspan hshort) :
    let x := d.stream.cutoff.cut.input
    ∀ i : Fin (p.m - 1), ∃ old memory,
      x.state.followers i = .ordinary old memory ∧
      let prepared : ReferencePrelaunchFollower.State p rate.eta :=
        { old with status := .unoccupied }
      ActiveFollowerLifecycle.startRound rate.eta x.time old memory = .ok (prepared, memory) ∧
      (d.stream.cutoff.cut.output.preparation.followers.followers i).configuration =
        .ordinary prepared memory ∧
      ActiveFollowerLifecycle.localStateDomainValid prepared ∧
      prepared.S + prepared.backlog ≤
        (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
          (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
            source rewards C_star C_h hc count hspan).records).length * D p ∧
      (old.lastDown = none ∧ old.S = 0 ∧ old.delta = 0 ∧ old.backlog = 0 ∨
        ∃ M, old.lastDown = some M ∧ M.val.sigma =
          ReferenceFirstCollectionReadyStream.startTime (rate := rate) source rewards C_star C_h + 1) ∧
      (ActiveFollowerQueueOperation.selectedUpRound i x.row (x.state.activations i) x.time →
        ∃ offered : OrdinaryMessageCodec.UpRecord (ReferencePrelaunchFollower.codecParams p rate.eta),
          ActiveFollowerQueueOperation.checkedUpOffer rate.eta i x.row
            (x.state.activations i) x.time prepared = .offer offered ∧
          offered.val = ActiveFollowerQueueOperation.upOfferFields prepared ∧
          (d.stream.cutoff.cut.output.preparation.followers.followers i).arm =
            ActiveRoundActions.sendArm
              (ActiveFollowerArmChoice.offeredUpBit rate.eta (x.row.2 x.time) i offered)
              ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K (x.row.2 x.time).1).val
                (PublicDiscreteDraws.followerPlayer p.two_le_m i))
              ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K (x.row.2 x.time).1).val
                (ActiveRoundActions.coordinator p.two_le_m))) ∧
      (PublicDiscreteDraws.slotDraw (x.row.2 x.time).1 ≠ PublicDiscreteDraws.dataSlot →
        ¬ ActiveFollowerQueueOperation.selectedUpRound i x.row (x.state.activations i) x.time →
        (d.stream.cutoff.cut.output.preparation.followers.followers i).arm =
          (OrderedTupleSampler.sample p.two_le_m p.m_lt_K (x.row.2 x.time).1).val
            (PublicDiscreteDraws.followerPlayer p.two_le_m i)) := by
  classical
  let s := ReferenceFirstCollectionReadyStream.startTime (rate := rate)
    source rewards C_star C_h
  let initial := ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hc
  have hsurvival := ReferenceGeneratedFirstCutoffSurvival.run_generated_first_cutoff_survival
    rate source rewards C_star C_h hc s rfl count hspan hshort
  rcases hsurvival with ⟨active, hfirst, _hbank, _hlearner, _hzero, hseed, _hcutoff⟩
  have hlaunch := ReferenceFirstLaunchNumericalCell.actual_launch_seed
    rate source rewards C_star C_h hc
  have hp := ReferenceFirstCutoffFollowerPreparation.run_first_cutoff_follower_preparation
    initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
    rewards s count hspan hlaunch.2.1 hfirst
    (ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffSeed
      rate source rewards C_star C_h)
    ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffMemory
    (fun i => (hseed i).1)
    (by intro i; rcases hseed i with ⟨_, _, h, _⟩; exact h)
    (by intro i; rcases hseed i with ⟨_, _, _, h, _⟩; exact h)
    (by intro i; rcases hseed i with ⟨_, _, _, _, h, _⟩; exact h)
    (by intro i; rcases hseed i with ⟨_, h, _⟩; exact h)
    (by intro i; rcases hseed i with ⟨_, _, _, _, _, h, _⟩; exact h)
    (by intro i; rcases hseed i with ⟨_, _, _, _, _, _, _, h, _⟩; exact h)
    (by intro i; rcases hseed i with ⟨_, _, _, _, _, _, _, _, h, _⟩; exact h)
    (by intro i; rcases hseed i with ⟨_, _, _, _, _, _, _, _, _, h, _⟩; exact h)
    (by intro i; rcases hseed i with ⟨_, _, _, _, _, _, _, _, _, _, h⟩; exact h)
    hshort
  rcases hp with ⟨cut, _suffix, _hsplit, hindex, _htime, hstate, _hrows,
    _hselected, _hrewards, hfollowers, _hfeedback, _hentries⟩
  have hget : (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
      source rewards C_star C_h hc count hspan).records[
      (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
          source rewards C_star C_h hc count hspan).records).length]? = some cut := by
    rw [hindex]
    exact List.getElem?_eq_getElem _
  have hid : cut = d.stream.cutoff.cut :=
    Option.some.inj (hget.symm.trans d.stream.cutoff.cutIndex)
  clear hindex
  subst cut
  dsimp only
  intro i
  rcases hfollowers i with ⟨old, memory, hold, hunoccupied, hoccupied,
    hstart, hconfiguration, hdomain, hmass, _hS, _hdelta, _hbacklog, _hpair,
    _hchron, _hSsame, _hdeltasame, _hbacklogsame, _hlastsame, _hbuffersame,
    _hbatchsame, _hfailuresame, _hzeroOffer, hselectedOffer, _hnoOffer, _hdataArm, hotherArm⟩
  refine ⟨old, memory, ?_, hstart, hconfiguration, hdomain, hmass, ?_, ?_, ?_⟩
  · rw [hstate]
    exact hold
  · by_cases hu : old.status = .unoccupied
    · exact Or.inl (hunoccupied hu)
    · obtain ⟨_, M, _token, hlast, hsigma, _⟩ := hoccupied hu
      exact Or.inr ⟨M, hlast, hsigma⟩

  · intro hselected
    obtain ⟨offered, hchecked, hfields, _hadmissible, _hrange, harm⟩ := hselectedOffer hselected
    have hfollower := d.stream.cutoff.cut.output.preparation.arms.actions_follower i
    exact ⟨offered, hchecked, hfields, hfollower.symm.trans harm⟩
  · intro hnotData hnotSelected
    exact (d.stream.cutoff.cut.output.preparation.arms.actions_follower i).symm.trans
      (hotherArm hnotData hnotSelected)

/-- Whole-control replacement reaches the same first-cutoff incoming state.
Only the strict past is compared; no future window is asserted invariant. -/
private theorem fresh_cutoff_dispatch
    (source : SourceInput p) (rewards : RewardTable p) (C_star C_h : ℝ)
    (count : ℕ)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hspan : ReferenceFirstCollectionReadyStream.startTime (rate := rate)
      source rewards C_star C_h + count ≤ p.T)
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
        source rewards C_star C_h hc count hspan).records).length < count)
    (d : ReferenceFirstCollectionStreamEmptyDispatch.ActualInitializedStreamDispatch
      source rewards C_star C_h count hc hspan hshort) (c : TimeControl p) :
    let x := d.stream.cutoff.cut.input
    let z := ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p x.time source c
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
        source rewards C_star C_h hc count hspan).records).length
    ∃ (hc' : (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true)
      (_hs : ReferenceFirstCollectionReadyStream.startTime (rate := rate) z rewards C_star C_h =
        ReferenceFirstCollectionReadyStream.startTime (rate := rate) source rewards C_star C_h)
      (hspan' : ReferenceFirstCollectionReadyStream.startTime (rate := rate)
        z rewards C_star C_h + (w + 1) ≤ p.T)
      (hshort' : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
          z rewards C_star C_h hc' (w + 1) hspan').records).length < w + 1)
      (d' : ReferenceFirstCollectionStreamEmptyDispatch.ActualInitializedStreamDispatch
        z rewards C_star C_h (w + 1) hc' hspan' hshort'),
      d'.stream.cutoff.cut.input = ReferenceLaterOptionalControlResampling.withControl x c := by
  classical
  intro x z w
  let s := ReferenceFirstCollectionReadyStream.startTime (rate := rate) source rewards C_star C_h
  let J := ActualInitializationPhysicalStep.selectedRowIndex p source
  let split := ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p J x.time source
  have hrem : split.2 ∈ ReferenceFixedTimeSourceControlCoupling.fixedControlRemainderStratum
      p J x.time := by
    change PrivateSourceStreams.coordinatorIndex p
      ((ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p J x.time source).2.2).1.2 = J
    rw [ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_private]
    rfl
  have htime : x.time.val = s + w := d.stream.cutoff.cutTime
  have hs : s ≤ x.time.val := by omega
  have hevent : split.2 ∈ ReferenceInitializationControlRemainder.launchStartRemainderEvent
      rate rewards C_star C_h J x.time s split.1 :=
    (ReferenceInitializationControlRemainder.launchStartRemainderEvent_iff_source
      rate rewards C_star C_h J x.time split.1 source rfl s hs).mpr ⟨hc, rfl⟩
  have hsource : ReferenceGeneratedActivePrefixFactor.splitSource J x.time split.1 split.2 = source :=
    (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p J x.time).symm_apply_apply source
  have hz : ReferenceGeneratedActivePrefixFactor.splitSource J x.time c split.2 = z :=
    ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_replaceSourceControl
      p J x.time source c rfl
  have hevent' := (ReferenceInitializationControlRemainder.launchStartRemainderEvent_control_independent
    rate rewards C_star C_h J x.time s split.2 hrem split.1 c).mp hevent
  have hfacts := ReferenceGeneratedActivePrefixFactor.launchStart_source_facts
    rate rewards C_star C_h J x.time c split.2 hrem s hs hevent'
  rw [hz] at hfacts
  rcases hfacts with ⟨hc', helapsed⟩
  have hselected : ActualInitializationPhysicalStep.selectedRowIndex p z = J := rfl
  obtain ⟨initial, hlaunch0, hlaunch1, _hlaunch2, active, _hbatch, _hstates, _hevidence⟩ :=
    ReferenceGeneratedActivePrefixFactor.generatedActivePrefixFactor_control_independent
      rate rewards C_star C_h J x.time split.2 hrem split.1 s w hs
      (by omega) hevent split.1 c
  rw [hsource] at hlaunch0
  rw [hsource] at hlaunch1
  have hlaunchZ : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate z rewards C_star C_h = some initial := by
    simpa only [hz] using _hlaunch2
  have hinit : initial = ReferenceFirstCollectionEpochAlignment.actualLaunchState
      rate source rewards C_star C_h hc :=
    Option.some.inj (hlaunch0.symm.trans (Option.eq_some_of_isSome
      ((ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
        rate source rewards C_star C_h).2 hc)))
  have hinitZ : initial = ReferenceFirstCollectionEpochAlignment.actualLaunchState
      rate z rewards C_star C_h hc' :=
    Option.some.inj (hlaunchZ.symm.trans (Option.eq_some_of_isSome
      ((ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
        rate z rewards C_star C_h).2 hc')))
  have hspanW : s + w ≤ p.T := by omega
  let pref := ReferenceActivePhysicalHorizon.run initial source.1.2 J rewards s w hspanW active
  let prefZ := ReferenceActivePhysicalHorizon.run initial z.1.2 J rewards s w hspanW active
  have hcontrols : ∀ v : Fin p.T, v.val < x.time.val →
      (source.1.2 J).2 v = (z.1.2 J).2 v := by
    intro v hv
    have hne : v ≠ x.time := by intro heq; subst v; omega
    simp only [z, ReferenceFixedTimeSourceControlCoupling.replaceSourceControl,
      ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex,
      J, Function.update_self, Function.update_of_ne hne]
  have htags := run_cutoffTags_eq initial source.1.2 z.1.2 J rewards s w hspanW active
    (fun v _ hv => hcontrols v (by omega))
    (fun v hv => congrArg (fun u : TimeControl p => u.1 ContinuousControlSlice.Label.prop)
      (hcontrols v (by omega)))
  have hprefix : pref.records.IsPrefix
      (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
        source rewards C_star C_h hc count hspan).records := by
    obtain ⟨suffix, heq⟩ := ReferenceCollectionPhaseHistory.run_records_prefix
      initial source.1.2 J rewards s w (count - w) (by omega) active
    refine ⟨suffix, ?_⟩
    have hw : w ≤ count := Nat.le_of_lt hshort
    have heq' : (ReferenceActivePhysicalHorizon.run initial source.1.2 J rewards s count
        hspan active).records = pref.records ++ suffix := by
      simpa only [Nat.add_sub_of_le hw] using heq
    have hcanon : (ReferenceActivePhysicalHorizon.run initial source.1.2 J rewards s count
        hspan active).records = (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
          source rewards C_star C_h hc count hspan).records := by
      cases hinit
      rfl
    exact heq'.symm.trans hcanon
  have hwindow := List.takeWhile_prefix
    (p := fun r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) =>
      !ReferenceCollectionPhaseHistory.cutoffChosen r.input)
    (l := (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
      source rewards C_star C_h hc count hspan).records)
  have hlen : pref.records.length = w := ReferenceActivePhysicalHorizon.run_record_count _ _ _ _ _ _ _ _
  have hpast : ∀ record ∈ pref.records,
      ReferenceCollectionPhaseHistory.cutoffChosen record.input = false := by
    intro record hrecord
    obtain ⟨j, hj, heq⟩ := List.mem_iff_getElem.mp hrecord
    have hjw : j < w := by omega
    have hsame := (hprefix.getElem hj).trans (hwindow.getElem hjw).symm
    have hmem : record ∈ ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
          source rewards C_star C_h hc count hspan).records := by
      rw [← heq, hsame]
      exact List.getElem_mem hjw
    have hpred := List.all_eq_true.mp (List.all_takeWhile
      (l := (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
        source rewards C_star C_h hc count hspan).records)) record hmem
    cases hb : ReferenceCollectionPhaseHistory.cutoffChosen record.input <;> simp_all only [Bool.not_false, Bool.not_true, Bool.false_eq_true]
  have hpastZ : ∀ record ∈ prefZ.records,
      ReferenceCollectionPhaseHistory.cutoffChosen record.input = false := by
    intro record hrecord
    have hmem := List.mem_map_of_mem
      (f := fun r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) =>
        ReferenceCollectionPhaseHistory.cutoffChosen r.input) hrecord
    rw [← htags] at hmem
    obtain ⟨r, hr, heq⟩ := List.mem_map.mp hmem
    exact heq.symm.trans (hpast r hr)
  have hrec := actualRecord_at_cutoff source rewards C_star C_h count hc hspan hshort d
  obtain ⟨record, hrecord, hinput⟩ :=
    ReferenceFirstCollectionUpConditionalService.actualFirstCollectionUp_actualRecord_replace
      rewards C_star C_h split.1 x.time source d.stream.cutoff.cut hrec c
  have hspan' : ReferenceFirstCollectionReadyStream.startTime (rate := rate)
      z rewards C_star C_h + (w + 1) ≤ p.T := by
    change ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed +
      (w + 1) ≤ p.T
    rw [helapsed]
    omega
  let E := ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
    z rewards C_star C_h hc' (w + 1) hspan'
  have hrecordAt : record = ReferenceAssignmentPayloadChronology.actualRunRecordAt
      initial z.1.2 J rewards s w (by omega) active := by
    have ha := ReferenceSourcePrefixHistoryFiltration.actualRecord_on_launch
      rate rewards C_star C_h x.time z initial hlaunchZ
      (by
        change ReferenceInitializationRun.elapsed p
          (ReferenceInitializationRun.output
            (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed ≤ x.time.val
        rw [helapsed]
        omega)
    have ha' : ReferenceSourcePrefixHistoryFiltration.actualRecord
        rate rewards C_star C_h x.time z = some
          (ReferenceAssignmentPayloadChronology.actualRunRecordAt initial z.1.2 J rewards s w
            (by omega) active) := by
      have hstartZ : ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h = s := helapsed
      simpa only [hstartZ, htime, Nat.add_sub_cancel_left, hselected] using ha
    exact Option.some.inj (hrecord.symm.trans ha')
  have hrecords : E.records = prefZ.records ++ [record] := by
    have hrunEq : E.records = (ReferenceActivePhysicalHorizon.run initial z.1.2 J rewards
        s (w + 1) (by omega) active).records := by
      cases hinitZ
      simp only [E, ReferenceFirstCollectionReadyStream.actualEpoch,
        ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun, helapsed, hselected]
    rw [hrunEq, ReferenceAssignmentPayloadChronology.run_successor_actualRunRecordAt]
    rw [hrecordAt]
  have hcut : ReferenceCollectionPhaseHistory.cutoffChosen record.input = true := by
    obtain ⟨execution⟩ := d.stream.cutoffExecution
    have hcutoff := ReferenceFirstCutoffRecordedService.run_first_cutoff_recorded_service
      (ReferenceFirstCollectionEpochAlignment.actualLaunchState rate source rewards C_star C_h hc)
      source.1.2 J rewards s count hspan
      (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
        rate source rewards C_star C_h hc).1
      (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
        rate source rewards C_star C_h hc).2 hshort
    rcases hcutoff with ⟨cut, _suffix, _hsplit, hi, _ht, r, q, base, _hs, _hp,
      dispatched, hstart, ledger, hinit, hledger, hdomain, hclock, hpending, hnone, selected,
      hchosen, _⟩
    have hget : (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
        source rewards C_star C_h hc count hspan).records[w]? = some cut := by
      rw [hi]
      exact List.getElem?_eq_getElem _
    have heq : cut = d.stream.cutoff.cut := Option.some.inj (hget.symm.trans d.stream.cutoff.cutIndex)
    clear hi
    subst cut
    have horiginal : ReferenceCollectionPhaseHistory.cutoffChosen x = true := by
      unfold ReferenceCollectionPhaseHistory.cutoffChosen
      have hprep : d.stream.cutoff.cut.output.preparation = ReferenceActivePhysicalStep.prepare x :=
        congrArg ReferenceActivePhysicalStep.RoundOutput.preparation d.stream.cutoff.cut.output_eq
      rw [← hprep, hchosen]
    rw [hinput, cutoffChosen_withControl x execution.live execution.owned execution.base execution.actualLive c]
    exact horiginal
  have hwindowZ : ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records = prefZ.records := by
    unfold ReferenceFirstLiveConfirmationHistory.firstLiveWindow
    rw [hrecords, List.takeWhile_append_of_pos (fun r hr => by rw [hpastZ r hr]; rfl)]
    simp only [hcut, Bool.not_true, Bool.false_eq_true, not_false_eq_true,
      List.takeWhile_cons_of_neg, List.append_nil]
  have hshort' : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records).length < w + 1 := by
    rw [hwindowZ, ReferenceActivePhysicalHorizon.run_record_count]
    omega
  obtain ⟨d'⟩ := ReferenceFirstCollectionStreamEmptyDispatch.actual_initialized_first_collection_stream_empty_dispatch
    rate z rewards C_star C_h (w + 1) hc' hspan' hshort'
  have hrec' := actualRecord_at_cutoff z rewards C_star C_h (w + 1) hc' hspan' hshort' d'
  have htime' : d'.stream.cutoff.cut.input.time = x.time := by
    apply Fin.ext
    have ht := d'.stream.cutoff.cutTime
    change _ = _ at ht
    rw [hwindowZ, ReferenceActivePhysicalHorizon.run_record_count] at ht
    calc
      _ = ReferenceFirstCollectionReadyStream.startTime (rate := rate) z rewards C_star C_h + w := ht
      _ = s + w := congrArg (fun n => n + w) helapsed
      _ = x.time.val := htime.symm
  rw [htime'] at hrec'
  have heq : d'.stream.cutoff.cut = record := Option.some.inj (hrec'.symm.trans hrecord)
  refine ⟨hc', helapsed, hspan', hshort', d', ?_⟩
  rw [heq]
  exact hinput

/-- Actual checked receiver and diagnostics at cutoff, including zero feedback.
The generated receiver's finite launch coordinate is the elapsed start. -/
private theorem actual_cutoff_receiver
    (source : SourceInput p) (rewards : RewardTable p) (C_star C_h : ℝ)
    (count : ℕ)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hspan : ReferenceFirstCollectionReadyStream.startTime (rate := rate)
      source rewards C_star C_h + count ≤ p.T)
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
        source rewards C_star C_h hc count hspan).records).length < count)
    (d : ReferenceFirstCollectionStreamEmptyDispatch.ActualInitializedStreamDispatch
      source rewards C_star C_h count hc hspan hshort) :
    let x := d.stream.cutoff.cut.input
    let prepared := ReferenceActivePhysicalStep.prepare x
    (PublicDiscreteDraws.slotDraw (x.row.2 x.time).1 = PublicDiscreteDraws.upSlot →
      prepared.coordinator.arm = (OrderedTupleSampler.sample p.two_le_m p.m_lt_K
        (x.row.2 x.time).1).val (ActiveRoundActions.coordinator p.two_le_m)) ∧
    ∃ ledger : ReferenceActivePhysicalStep.Ledger rate,
      ledger.pending = Finset.univ ∧
      CoordinatorUpReception.receptionInputDomain
        (ReferenceCoordinatorUpPhysicalCall.actualUpInput x ledger) ∧
      CoordinatorUpReception.receptionInputCheck
        (ReferenceCoordinatorUpPhysicalCall.actualUpInput x ledger) = true ∧
      ReferenceCoordinatorUpPhysicalCall.siteLedger? (x := x) = some ledger ∧
      prepared.observeCoordinator.up = (ReferenceActivePhysicalStep.receiveUp prepared ledger).diagnostic ∧
      1 < AffineBatchDecoder.quota p ∧
      ∃ diagnostic : ReferenceActivePhysicalStep.UpDiagnostic p rate,
        prepared.observeCoordinator.up = some diagnostic ∧
        diagnostic.input = ReferenceCoordinatorUpPhysicalCall.actualUpInput x ledger ∧
        diagnostic.expected = ReferenceActivePhysicalStep.upExpected prepared ∧
        diagnostic.decoderAfter = (CoordinatorUpReception.decoderTransition diagnostic.input).1 ∧
        diagnostic.raw = none ∧ diagnostic.parsed = none ∧
        diagnostic.locallyAccepted = false ∧
        diagnostic.rawMatches = decide (none = ReferenceActivePhysicalStep.upExpected prepared) ∧
        diagnostic.wrongUniqueAccepted = false ∧
        (CoordinatorUpReception.decoderTransition diagnostic.input).1.completed = [] ∧
        (CoordinatorUpReception.decoderTransition diagnostic.input).1.pending =
          (if CoordinatorUpReception.receptionGate diagnostic.input ∧
              0 < diagnostic.input.ownObservation.val then
            [AffineBatchDecoder.entry p (CoordinatorUpReception.traceAt diagnostic.input)
              diagnostic.input.time] else []) ∧
        (ReferenceActivePhysicalStep.receiveUp prepared ledger).result =
          .rejected ({ diagnostic.input.ledger with phase := CoordinatorCollectionLedger.Phase.decoded },
            CoordinatorUpReception.decoderBankAfter diagnostic.input) ∧
        (diagnostic.input.ownObservation.val = 0 →
          CoordinatorUpReception.decoderBankAfter diagnostic.input = diagnostic.input.upDecoderBank) := by
  classical
  intro x prepared
  let s := ReferenceFirstCollectionReadyStream.startTime (rate := rate) source rewards C_star C_h
  have hsT : s < p.T := by
    have ht := d.stream.cutoff.cutTime
    have hx := x.time.isLt
    change x.time.val = s + _ at ht
    omega
  have hraw := ReferenceFirstCutoffReceiverDomain.run_generated_first_cutoff_receiver_domain
    rate source rewards C_star C_h hc s rfl hsT count hspan ⟨s, hsT⟩ rfl
  extract_lets J split hrem hlaunchEvent seed active execution window at hraw
  have hseedEq : seed = ReferenceFirstCollectionEpochAlignment.actualLaunchState
      rate source rewards C_star C_h hc :=
    ReferenceGeneratedFirstCutoffSurvival.generatedLaunchSeed_eq_launchState
      rate source rewards C_star C_h hc s rfl hsT
  have hrecordsEq : execution.records =
      (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
        source rewards C_star C_h hc count hspan).records := by
    have hcongr (left right : ReferenceActivePhysicalStep.State p rate)
        (heq : left = right)
        (hl : ReferenceActivePhysicalHorizon.allActiveAtStart left s)
        (hr : ReferenceActivePhysicalHorizon.allActiveAtStart right s) :
        (ReferenceActivePhysicalHorizon.run left source.1.2 J rewards s count hspan hl).records =
          (ReferenceActivePhysicalHorizon.run right source.1.2 J rewards s count hspan hr).records := by
      cases heq
      rfl
    exact hcongr seed _ hseedEq active _
  rcases hraw with ⟨_hrem, _hevent, _hsT, _hfirst, _hbank, hreceive⟩
  have hshortSeed : window.length < count := by
    simpa only [window, hrecordsEq] using hshort
  obtain ⟨cut, suffix, hsplit, htime, r, q, base, hphase,
    dispatched, hstartClock, initial, hinit, hledger, hdomain, hclock, hpending, hnone,
    selected, hchosen, recording, _hbranch, _htrace, _hrecorded, hrecording,
    ledger, hstart, hcandidate, input, hinput, hreceiver, hcheck, _htransition, _hquota,
    _hrawParsed, _hfiltered, _hparsed, _hrejected, _hbankAfter, _hcompleted, hpendingDecoder,
    diagnostic, hdiagnostic, hdiagnosticInput, hdiagnosticExpected, hdiagnosticDecoder,
    hrawNone, hparsedNone, hlocalFalse, _hrawMatches, hwrongFalse, _hother, _hfreeze⟩ :=
      hreceive hshortSeed
  have hsplitCanon : (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
      source rewards C_star C_h hc count hspan).records =
      ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
          source rewards C_star C_h hc count hspan).records ++ cut :: suffix := by
    simpa only [hrecordsEq, window] using hsplit
  have hget : (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
      source rewards C_star C_h hc count hspan).records[
      (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
          source rewards C_star C_h hc count hspan).records).length]? = some cut := by
    have heq := congrArg (fun records : List (ReferenceActivePhysicalHorizon.RoundRecord
      (p := p) (rate := rate)) => records[
        (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
          (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
            source rewards C_star C_h hc count hspan).records).length]?) hsplitCanon
    exact heq.trans (by
      rw [List.getElem?_append_right (Nat.le_refl _)]
      simp only [Nat.sub_self, List.getElem?_cons_zero])
  have hid : cut = d.stream.cutoff.cut := Option.some.inj (hget.symm.trans d.stream.cutoff.cutIndex)
  subst cut
  have hprep : d.stream.cutoff.cut.output.preparation = prepared :=
    congrArg ReferenceActivePhysicalStep.RoundOutput.preparation d.stream.cutoff.cut.output_eq
  simp only [hprep] at hchosen hrecording hinput hdiagnostic hdiagnosticExpected _hrawMatches _hrejected
  have hbridge : CoordinatorRecorderComplementBridge.run
      (ReferenceActivePhysicalStep.collectionRecordingInput prepared r.payload
        dispatched.startResult (ReferenceActivePhysicalStep.liveRegistersAt r x.time).complementWeights) =
      some recording := hrecording
  have hselection : prepared.coordinator.selection ≠ none := by
    rw [hchosen]
    simp [ReferenceActivePhysicalStep.DispatchCut.selection, ReferenceActivePhysicalStep.selectionAt]
  have hobserve : prepared.observeCoordinator.up =
      (ReferenceActivePhysicalStep.receiveUp prepared ledger).diagnostic := by
    rw [ReferenceActivePhysicalStep.observeCoordinator_live_equation prepared r q base _ hchosen]
    have hsel := hselection
    rw [hchosen] at hsel
    rw [ite_eq_right hsel]
    dsimp only
    unfold ReferenceActivePhysicalStep.collectionPostChoice
    rw [hbridge]
    dsimp only
    rw [hstart]
    exact ReferenceActiveAffinePositiveTest.collectionFinish_up x r.payload
      dispatched.startResult recording (ReferenceActivePhysicalStep.receiveUp prepared ledger)
  constructor
  · intro hslot
    have hnotFast : ¬ (CoordinatorLocalArmChoice.assignmentIsLive r.payload
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p dispatched.startResult.clock.u) x.time ∧
        dispatched.startResult.pending = ∅) := by
      rintro ⟨_, hempty⟩
      rw [hpending] at hempty
      have hmem : (⟨0, by have hm := p.two_le_m; omega⟩ : Fin (p.m - 1)) ∈
          (Finset.univ : Finset (Fin (p.m - 1))) := Finset.mem_univ _
      rw [hempty] at hmem
      exact Finset.notMem_empty _ hmem
    have hnotData : PublicDiscreteDraws.slotDraw (x.row.2 x.time).1 ≠ PublicDiscreteDraws.dataSlot :=
      fun heq => (by decide : PublicDiscreteDraws.upSlot ≠ PublicDiscreteDraws.dataSlot)
        (hslot.symm.trans heq)
    have hnotDown : ¬ (PublicDiscreteDraws.slotDraw (x.row.2 x.time).1 = PublicDiscreteDraws.downSlot ∧
        PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K (x.row.2 x.time).1 ∈
          dispatched.startResult.pending) :=
      fun h => (by decide : PublicDiscreteDraws.upSlot ≠ PublicDiscreteDraws.downSlot)
        (hslot.symm.trans h.1)
    have harm := CoordinatorLocalArmChoice.coordinatorArmChoiceCore_other
      r.payload dispatched.startResult.pending
      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p dispatched.startResult.clock.u)
      x.time (ReferenceActivePhysicalStep.liveRegistersAt r x.time).complementWeights
      (x.row.2 x.time) selected.choiceInputsValid hnotFast hnotData hnotDown
    have hselected : CoordinatorLocalArmChoice.coordinatorArmChoice r.payload
        dispatched.startResult.pending
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p dispatched.startResult.clock.u)
        x.time (ReferenceActivePhysicalStep.liveRegistersAt r x.time).complementWeights x.row =
        some selected.arm := selected.armChoice_eq
    change CoordinatorLocalArmChoice.coordinatorArmChoiceCore _ _ _ _ _ _ = _ at hselected
    rw [harm] at hselected
    rw [hchosen, ReferenceActivePhysicalStep.live_arm_equation]
    exact (Option.some.inj hselected).symm
  · refine ⟨ledger, ?_, ?_, ?_, ?_, hobserve, _hquota, diagnostic, hobserve.trans hdiagnostic,
      ?_, hdiagnosticExpected, ?_, hrawNone, hparsedNone, hlocalFalse, _hrawMatches,
      hwrongFalse, ?_, ?_, ?_, ?_⟩
    · rw [hcandidate, hledger]
      rfl
    · simpa only [hinput, ReferenceCoordinatorUpPhysicalCall.actualUpInput, prepared] using hreceiver
    · simpa only [hinput, ReferenceCoordinatorUpPhysicalCall.actualUpInput, prepared] using hcheck
    · dsimp only [prepared] at hchosen hselection hbridge
      unfold ReferenceCoordinatorUpPhysicalCall.siteLedger?
      simp only [hchosen]
      have hsel := hselection
      rw [hchosen] at hsel
      rw [dite_eq_right hsel]
      change ReferenceCoordinatorUpPhysicalCall.tailLedger? prepared r.payload
        (ReferenceActivePhysicalStep.sharedLedger initial) dispatched.startResult
        (ReferenceActivePhysicalStep.liveRegistersAt r x.time).complementWeights = some ledger
      unfold ReferenceCoordinatorUpPhysicalCall.tailLedger?
      rw [hbridge]
      dsimp only
      rw [hstart]
    · exact hdiagnosticInput.trans hinput
    · simpa only [hdiagnosticInput] using hdiagnosticDecoder
    · simpa only [hdiagnosticInput] using _hcompleted
    · rw [hdiagnosticInput]
      exact hpendingDecoder
    · simpa only [hdiagnosticInput] using _hrejected
    · intro hzero
      have hnot : ¬ AffineBatchDecoder.eligible
          ((CoordinatorUpReception.traceAt diagnostic.input) diagnostic.input.time) := by
        intro he
        have hpositive := he.2.2
        change 0 < CoordinatorUpReception.roundedObservationValue p diagnostic.input.ownObservation at hpositive
        rw [CoordinatorUpReception.roundedObservationValue_zero p diagnostic.input.ownObservation hzero] at hpositive
        exact (lt_irrefl 0) hpositive
      have hdom : CoordinatorUpReception.receptionInputDomain diagnostic.input := by
        rw [hdiagnosticInput]
        exact hreceiver
      have htransition := CoordinatorUpReception.decoderTransition_ineligible diagnostic.input hdom hnot
      simp only [CoordinatorUpReception.decoderBankAfter, htransition, Function.update_eq_self]

private theorem upSent_of_checked_offer
    (x : ReferenceActivePhysicalStep.RoundInput p rate) (i : Fin (p.m - 1))
    (old : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (U : OrdinaryMessageCodec.UpRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (hselected : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
      (x.row.2 x.time).1 = i)
    (hconfig : ((ReferenceActivePhysicalStep.prepare x).followers.followers i).configuration =
      .ordinary old memory)
    (hchecked : ActiveFollowerQueueOperation.checkedUpOffer rate.eta i x.row
      (x.state.activations i) x.time old = .offer U) :
    ReferenceActiveAffinePositiveTest.upSent x =
      some (ActiveFollowerArmChoice.offeredUpWord rate.eta U) := by
  let prepared := ReferenceActivePhysicalStep.prepare x
  have halign := prepared.follower_alignment i
  have hlocal : ActiveFollowerQueueOperation.checkedUpOffer rate.eta
      (prepared.followers.followers i).follower (prepared.followers.followers i).row
      (prepared.followers.followers i).activation (prepared.followers.followers i).time
      old = .offer U := by
    rw [halign.1, halign.2.1, halign.2.2.1, halign.2.2.2]
    exact hchecked
  have hw := ReferenceUpReception.currentOfferWord_eq_encoded_offer rate
    x.row i x.time (prepared.followers.followers i)
    halign.1 halign.2.1 halign.2.2.1 old memory hconfig U hlocal
  have hi : ReferenceActivePhysicalStep.upSenderIndex x = i :=
    (ReferenceActiveAffinePositiveTest.upSenderIndex_eq_draw x).trans hselected
  cases hi
  exact hw

private theorem coordinator_observation_positive_iff
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (arm : Fin p.K)
    (ha : prepared.arms.actions (ActiveRoundActions.coordinator p.two_le_m) = arm) :
    (0 < CoordinatorUpReception.roundedObservationValue p prepared.coordinatorObservation) ↔
      FiniteBanditModel.collisionFreeFor prepared.arms.actions
        (ActiveRoundActions.coordinator p.two_le_m) ∧ 0 < x.rewards x.time arm := by
  classical
  have hD : (0 : ℝ) < (D p : ℝ) := by exact_mod_cast D_pos p
  have hpos : (0 < CoordinatorUpReception.roundedObservationValue p
      prepared.coordinatorObservation) ↔
      0 < (prepared.feedback.feedback (ActiveRoundActions.coordinator p.two_le_m)).val := by
    rw [CoordinatorUpReception.roundedObservationValue,
      ReferenceActivePhysicalStep.PreparedRound.coordinatorObservation,
      div_pos_iff_of_pos_right hD]
    exact Nat.cast_pos
  rw [hpos, prepared.feedback_rule]
  by_cases hfree : FiniteBanditModel.collisionFreeFor prepared.arms.actions
      (ActiveRoundActions.coordinator p.two_le_m)
  · rw [ite_eq_left hfree, ha]
    simp only [hfree, true_and]
    rfl
  · rw [ite_eq_right hfree]
    simp only [Fin.val_zero, Nat.lt_irrefl, hfree, false_and]


/-- Exact formed-UP service at date zero of the actual collection window.
All cutoff and follower witnesses are produced from the displayed selectors.
The named consumer is the early-formed (`f = 0`) UP waiting task. -/
theorem actual_first_cutoff_up_service_coefficient
    (rate : RateInput p) (source : SourceInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (count : ℕ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hspan : ReferenceFirstCollectionReadyStream.startTime (rate := rate)
      source rewards C_star C_h + count ≤ p.T)
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
        source rewards C_star C_h hcross count hspan).records).length < count) :
    ∃ d : ReferenceFirstCollectionStreamEmptyDispatch.ActualInitializedStreamDispatch
        source rewards C_star C_h count hcross hspan hshort,
    ∃ (old : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
      (memory : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p),
    let x := d.stream.cutoff.cut.input
    let preparedFollower := fun j => { old j with status := ActiveRoundActions.FollowerStatus.unoccupied }
    (∀ j, x.state.followers j = .ordinary (old j) (memory j) ∧
      ActiveFollowerLifecycle.startRound rate.eta x.time (old j) (memory j) =
        .ok (preparedFollower j, memory j) ∧
      ((ReferenceActivePhysicalStep.prepare x).followers.followers j).configuration =
        .ordinary (preparedFollower j) (memory j) ∧
      ActiveFollowerLifecycle.localStateDomainValid (preparedFollower j)) ∧
    ∀ i : Fin (p.m - 1), 1 ≤ ReferencePrelaunchFollower.acceptedStart (old i) →
    ∃ U : OrdinaryMessageCodec.UpRecord (ReferencePrelaunchFollower.codecParams p rate.eta),
      U.val = ActiveFollowerQueueOperation.upOfferFields (preparedFollower i) ∧
      U.val = ActiveFollowerQueueOperation.upOfferFields (old i) ∧
      U.val.sigma = ReferenceFirstCollectionReadyStream.startTime (rate := rate)
        source rewards C_star C_h + 1 ∧ 1 ≤ U.val.sigma ∧
      ReferenceFirstCollectionUpConditionalService.freshCoordinatorUpServiceSet x i =
        ReferenceFirstCollectionUpConditionalService.coordinatorUpServiceFormulaSet rewards x.time i U ∧
      (ContinuousLearningRows.timeControlLaw p)
          (ReferenceFirstCollectionUpConditionalService.freshCoordinatorUpServiceSet x i) =
        ENNReal.ofReal ((ReferenceFirstCollectionUpConditionalService.positiveRewardCount rewards x.time : ℝ) /
          (8 * (p.m - 1 : ℝ) * p.K)) ∧
      ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h x.time source =
        some d.stream.cutoff.cut ∧
      (∀ control0 : TimeControl p,
        ReferenceFirstCollectionUpConditionalService.actualFirstCollectionUpFreshSection (rate := rate)
          rewards C_star C_h control0 i x.time source =
          (ReferenceFirstCollectionUpConditionalService.positiveRewardCount rewards x.time : ℝ) /
            (8 * (p.m - 1 : ℝ) * p.K)) ∧
      ∀ c : TimeControl p,
        let xc := ReferenceLaterOptionalControlResampling.withControl x c
        let prepared := ReferenceActivePhysicalStep.prepare xc
        let tuple := OrderedTupleSampler.sample p.two_le_m p.m_lt_K c.1
        (∀ j, (prepared.followers.followers j).configuration =
          .ordinary (preparedFollower j) (memory j)) ∧
        (PublicDiscreteDraws.slotDraw c.1 = PublicDiscreteDraws.upSlot ∧
            PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K c.1 = i →
          prepared.coordinator.arm = tuple.val (ActiveRoundActions.coordinator p.two_le_m) ∧
          ActiveFollowerQueueOperation.checkedUpOffer rate.eta i xc.row
            (xc.state.activations i) xc.time (preparedFollower i) = .offer U ∧
          (prepared.followers.followers i).arm = ActiveRoundActions.sendArm
            (ActiveFollowerArmChoice.offeredUpBit rate.eta c i U)
            (tuple.val (PublicDiscreteDraws.followerPlayer p.two_le_m i))
            (tuple.val (ActiveRoundActions.coordinator p.two_le_m)) ∧
          ∀ j, j ≠ i → (prepared.followers.followers j).arm =
            tuple.val (PublicDiscreteDraws.followerPlayer p.two_le_m j)) ∧
        ∃ ledger : ReferenceActivePhysicalStep.Ledger rate,
          ledger.pending = Finset.univ ∧
          CoordinatorUpReception.receptionInputDomain
            (ReferenceCoordinatorUpPhysicalCall.actualUpInput xc ledger) ∧
          CoordinatorUpReception.receptionInputCheck
            (ReferenceCoordinatorUpPhysicalCall.actualUpInput xc ledger) = true ∧
          ReferenceCoordinatorUpPhysicalCall.siteLedger? (x := xc) = some ledger ∧
          prepared.observeCoordinator.up = (ReferenceActivePhysicalStep.receiveUp prepared ledger).diagnostic ∧
          1 < AffineBatchDecoder.quota p ∧
          ∃ diagnostic : ReferenceActivePhysicalStep.UpDiagnostic p rate,
            prepared.observeCoordinator.up = some diagnostic ∧
            diagnostic.input = ReferenceCoordinatorUpPhysicalCall.actualUpInput xc ledger ∧
            diagnostic.expected = ReferenceActivePhysicalStep.upExpected prepared ∧
            diagnostic.decoderAfter = (CoordinatorUpReception.decoderTransition diagnostic.input).1 ∧
            diagnostic.raw = none ∧ diagnostic.parsed = none ∧
            diagnostic.locallyAccepted = false ∧
            diagnostic.rawMatches = decide (none = ReferenceActivePhysicalStep.upExpected prepared) ∧
            diagnostic.wrongUniqueAccepted = false ∧
            (CoordinatorUpReception.decoderTransition diagnostic.input).1.completed = [] ∧
            (CoordinatorUpReception.decoderTransition diagnostic.input).1.pending =
              (if CoordinatorUpReception.receptionGate diagnostic.input ∧
                  0 < diagnostic.input.ownObservation.val then
                [AffineBatchDecoder.entry p (CoordinatorUpReception.traceAt diagnostic.input)
                  diagnostic.input.time] else []) ∧
            (ReferenceActivePhysicalStep.receiveUp prepared ledger).result =
              .rejected ({ diagnostic.input.ledger with phase := CoordinatorCollectionLedger.Phase.decoded },
                CoordinatorUpReception.decoderBankAfter diagnostic.input) ∧
            (diagnostic.input.ownObservation.val = 0 →
              CoordinatorUpReception.decoderBankAfter diagnostic.input = diagnostic.input.upDecoderBank) := by
  classical
  obtain ⟨d⟩ := ReferenceFirstCollectionStreamEmptyDispatch.actual_initialized_first_collection_stream_empty_dispatch
    rate source rewards C_star C_h count hcross hspan hshort
  let x := d.stream.cutoff.cut.input
  have hfollowers := actual_cutoff_followers source rewards C_star C_h count hcross hspan hshort d
  dsimp only at hfollowers
  have hprep : d.stream.cutoff.cut.output.preparation = ReferenceActivePhysicalStep.prepare x :=
    congrArg ReferenceActivePhysicalStep.RoundOutput.preparation d.stream.cutoff.cut.output_eq
  simp only [hprep] at hfollowers
  choose old memory hstate hstart hconfig hdomain hmass hlast hselected hother using hfollowers
  let preparedFollower := fun j => { old j with status := ActiveRoundActions.FollowerStatus.unoccupied }
  refine ⟨d, old, memory, fun j => ⟨hstate j, hstart j, hconfig j, hdomain j⟩, ?_⟩
  intro i hpositive
  obtain ⟨M, hdown, hsigma⟩ : ∃ M, (old i).lastDown = some M ∧ M.val.sigma =
      ReferenceFirstCollectionReadyStream.startTime (rate := rate) source rewards C_star C_h + 1 := by
    rcases hlast i with hnone | hsome
    · have hzero : ReferencePrelaunchFollower.acceptedStart (old i) = 0 := by
        simp only [ReferencePrelaunchFollower.acceptedStart, hnone.1]
      omega
    · exact hsome
  have hM := M.property
  unfold OrdinaryMessageCodec.downAdmissible at hM
  have hadmissible : OrdinaryMessageCodec.upAdmissible
      (ReferencePrelaunchFollower.codecParams p rate.eta)
      (ActiveFollowerQueueOperation.upOfferFields (preparedFollower i)) := by
    right
    simpa only [ActiveFollowerQueueOperation.upOfferFields, preparedFollower,
      ReferencePrelaunchFollower.acceptedStart, ReferencePrelaunchFollower.codecParams, hdown] using
      And.intro hM.1 (And.intro hM.2.1
        (show (old i).S ≤ p.T * D p ∧ (old i).delta ≤ D p ∧ (old i).backlog ≤ p.T * D p
          from (hdomain i).1))
  let U : OrdinaryMessageCodec.UpRecord (ReferencePrelaunchFollower.codecParams p rate.eta) :=
    ⟨ActiveFollowerQueueOperation.upOfferFields (preparedFollower i), hadmissible⟩
  have hU : U.val = ActiveFollowerQueueOperation.upOfferFields (preparedFollower i) := rfl
  have hUsigma : U.val.sigma = ReferenceFirstCollectionReadyStream.startTime (rate := rate)
      source rewards C_star C_h + 1 := by
    simpa only [U, ActiveFollowerQueueOperation.upOfferFields, preparedFollower,
      ReferencePrelaunchFollower.acceptedStart, hdown] using hsigma
  have hforall (c : TimeControl p) :
      let xc := ReferenceLaterOptionalControlResampling.withControl x c
      let prepared := ReferenceActivePhysicalStep.prepare xc
      let tuple := OrderedTupleSampler.sample p.two_le_m p.m_lt_K c.1
      ((PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K c.1 = i ∧
          ReferenceActiveAffinePositiveTest.upPositive xc = true) ↔
        c ∈ ReferenceFirstCollectionUpConditionalService.coordinatorUpServiceFormulaSet rewards x.time i U) ∧
      (∀ j, (prepared.followers.followers j).configuration =
        .ordinary (preparedFollower j) (memory j)) ∧
      (PublicDiscreteDraws.slotDraw c.1 = PublicDiscreteDraws.upSlot ∧
          PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K c.1 = i →
        prepared.coordinator.arm = tuple.val (ActiveRoundActions.coordinator p.two_le_m) ∧
        ActiveFollowerQueueOperation.checkedUpOffer rate.eta i xc.row
          (xc.state.activations i) xc.time (preparedFollower i) = .offer U ∧
        (prepared.followers.followers i).arm = ActiveRoundActions.sendArm
          (ActiveFollowerArmChoice.offeredUpBit rate.eta c i U)
          (tuple.val (PublicDiscreteDraws.followerPlayer p.two_le_m i))
          (tuple.val (ActiveRoundActions.coordinator p.two_le_m)) ∧
        ∀ j, j ≠ i → (prepared.followers.followers j).arm =
          tuple.val (PublicDiscreteDraws.followerPlayer p.two_le_m j)) ∧
      ∃ ledger : ReferenceActivePhysicalStep.Ledger rate,
        ledger.pending = Finset.univ ∧
        CoordinatorUpReception.receptionInputDomain
          (ReferenceCoordinatorUpPhysicalCall.actualUpInput xc ledger) ∧
        CoordinatorUpReception.receptionInputCheck
          (ReferenceCoordinatorUpPhysicalCall.actualUpInput xc ledger) = true ∧
        ReferenceCoordinatorUpPhysicalCall.siteLedger? (x := xc) = some ledger ∧
        prepared.observeCoordinator.up = (ReferenceActivePhysicalStep.receiveUp prepared ledger).diagnostic ∧
        1 < AffineBatchDecoder.quota p ∧
        ∃ diagnostic : ReferenceActivePhysicalStep.UpDiagnostic p rate,
          prepared.observeCoordinator.up = some diagnostic ∧
          diagnostic.input = ReferenceCoordinatorUpPhysicalCall.actualUpInput xc ledger ∧
          diagnostic.expected = ReferenceActivePhysicalStep.upExpected prepared ∧
          diagnostic.decoderAfter = (CoordinatorUpReception.decoderTransition diagnostic.input).1 ∧
          diagnostic.raw = none ∧ diagnostic.parsed = none ∧
          diagnostic.locallyAccepted = false ∧
          diagnostic.rawMatches = decide (none = ReferenceActivePhysicalStep.upExpected prepared) ∧
          diagnostic.wrongUniqueAccepted = false ∧
          (CoordinatorUpReception.decoderTransition diagnostic.input).1.completed = [] ∧
          (CoordinatorUpReception.decoderTransition diagnostic.input).1.pending =
            (if CoordinatorUpReception.receptionGate diagnostic.input ∧
                0 < diagnostic.input.ownObservation.val then
              [AffineBatchDecoder.entry p (CoordinatorUpReception.traceAt diagnostic.input)
                diagnostic.input.time] else []) ∧
          (ReferenceActivePhysicalStep.receiveUp prepared ledger).result =
            .rejected ({ diagnostic.input.ledger with phase := CoordinatorCollectionLedger.Phase.decoded },
              CoordinatorUpReception.decoderBankAfter diagnostic.input) ∧
          (diagnostic.input.ownObservation.val = 0 →
            CoordinatorUpReception.decoderBankAfter diagnostic.input = diagnostic.input.upDecoderBank) := by
    intro xc prepared tuple
    let z := ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p x.time source c
    obtain ⟨hc', _hs', hspan', hshort', d', hinput⟩ :=
      fresh_cutoff_dispatch source rewards C_star C_h count hcross hspan hshort d c
    have hfresh := actual_cutoff_followers z rewards C_star C_h _ hc' hspan' hshort' d'
    dsimp only at hfresh
    have hprep' : d'.stream.cutoff.cut.output.preparation =
        ReferenceActivePhysicalStep.prepare d'.stream.cutoff.cut.input :=
      congrArg ReferenceActivePhysicalStep.RoundOutput.preparation d'.stream.cutoff.cut.output_eq
    simp only [hprep', hinput] at hfresh
    have hfreshSame (j : Fin (p.m - 1)) :
        (prepared.followers.followers j).configuration = .ordinary (preparedFollower j) (memory j) ∧
        (ActiveFollowerQueueOperation.selectedUpRound j xc.row (xc.state.activations j) xc.time →
          ∃ offered, ActiveFollowerQueueOperation.checkedUpOffer rate.eta j xc.row
              (xc.state.activations j) xc.time (preparedFollower j) = .offer offered ∧
            offered.val = ActiveFollowerQueueOperation.upOfferFields (preparedFollower j) ∧
            (prepared.followers.followers j).arm = ActiveRoundActions.sendArm
              (ActiveFollowerArmChoice.offeredUpBit rate.eta (xc.row.2 xc.time) j offered)
              ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K (xc.row.2 xc.time).1).val
                (PublicDiscreteDraws.followerPlayer p.two_le_m j))
              ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K (xc.row.2 xc.time).1).val
                (ActiveRoundActions.coordinator p.two_le_m))) ∧
        (PublicDiscreteDraws.slotDraw (xc.row.2 xc.time).1 ≠ PublicDiscreteDraws.dataSlot →
          ¬ ActiveFollowerQueueOperation.selectedUpRound j xc.row (xc.state.activations j) xc.time →
          (prepared.followers.followers j).arm =
            (OrderedTupleSampler.sample p.two_le_m p.m_lt_K (xc.row.2 xc.time).1).val
              (PublicDiscreteDraws.followerPlayer p.two_le_m j)) := by
      obtain ⟨before, μ, hbefore, _hstart', hconfiguration, _hvalid, _hmass, _hlast, hsend, hother'⟩ := hfresh j
      have hid : DeclaredFollowerLocalRound.LocalConfiguration.ordinary before μ =
          .ordinary (old j) (memory j) := hbefore.symm.trans (hstate j)
      injection hid with hbeforeEq hmemoryEq
      subst before
      subst μ
      have hconfigEq := congrArg (fun v : ReferenceActivePhysicalStep.RoundInput p rate =>
        ((ReferenceActivePhysicalStep.prepare v).followers.followers j).configuration) hinput
      have harmEq := congrArg (fun v : ReferenceActivePhysicalStep.RoundInput p rate =>
        ((ReferenceActivePhysicalStep.prepare v).followers.followers j).arm) hinput
      rw [hconfigEq] at hconfiguration
      rw [harmEq] at hsend hother'
      exact ⟨hconfiguration, hsend, hother'⟩
    have hreceiver := actual_cutoff_receiver z rewards C_star C_h _ hc' hspan' hshort' d'
    dsimp only at hreceiver
    simp only [hinput] at hreceiver
    obtain ⟨hcoordinator, ledger, hpending, hreceiverDomain, hcheck, hsite, hdiagnostic, hquota, hdiagdata⟩ := hreceiver
    have hcoordEq := congrArg (fun v : ReferenceActivePhysicalStep.RoundInput p rate =>
      (ReferenceActivePhysicalStep.prepare v).coordinator.arm) hinput
    rw [hcoordEq] at hcoordinator
    change (PublicDiscreteDraws.slotDraw (xc.row.2 xc.time).1 = PublicDiscreteDraws.upSlot →
      prepared.coordinator.arm = (OrderedTupleSampler.sample p.two_le_m p.m_lt_K
        (xc.row.2 xc.time).1).val (ActiveRoundActions.coordinator p.two_le_m)) at hcoordinator
    have hdiagEq := congrArg (fun v : ReferenceActivePhysicalStep.RoundInput p rate =>
      (ReferenceActivePhysicalStep.prepare v).observeCoordinator.up) hinput
    have hreceiveEq := congrArg (fun v : ReferenceActivePhysicalStep.RoundInput p rate =>
      (ReferenceActivePhysicalStep.receiveUp (ReferenceActivePhysicalStep.prepare v) ledger).diagnostic) hinput
    rw [hdiagEq, hreceiveEq] at hdiagnostic
    have hexpectedEq := congrArg (fun v : ReferenceActivePhysicalStep.RoundInput p rate =>
      ReferenceActivePhysicalStep.upExpected (ReferenceActivePhysicalStep.prepare v)) hinput
    have hresultEq := congrArg (fun v : ReferenceActivePhysicalStep.RoundInput p rate =>
      (ReferenceActivePhysicalStep.receiveUp (ReferenceActivePhysicalStep.prepare v) ledger).result) hinput
    rw [hdiagEq, hexpectedEq, hresultEq] at hdiagdata
    let input := ReferenceCoordinatorUpPhysicalCall.actualUpInput xc ledger
    have hcurrent : xc.row.2 xc.time = c :=
      ReferenceLaterOptionalControlResampling.withControl_currentControl x c
    have hUpFormula : ReferenceActiveAffinePositiveTest.upPositive xc =
        (CoordinatorUpReception.receptionInputCheck input &&
          decide (AffineBatchDecoder.eligible (CoordinatorUpReception.roundInput input))) := by
      unfold ReferenceActiveAffinePositiveTest.upPositive
      rw [hdiagnostic]
      exact ReferenceActiveAffinePositiveTest.receiveUp_positive prepared ledger
    have harms (hslot : PublicDiscreteDraws.slotDraw c.1 = PublicDiscreteDraws.upSlot)
        (hdraw : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K c.1 = i) :
        prepared.coordinator.arm = tuple.val (ActiveRoundActions.coordinator p.two_le_m) ∧
        ActiveFollowerQueueOperation.checkedUpOffer rate.eta i xc.row
          (xc.state.activations i) xc.time (preparedFollower i) = .offer U ∧
        (prepared.followers.followers i).arm = ActiveRoundActions.sendArm
          (ActiveFollowerArmChoice.offeredUpBit rate.eta c i U)
          (tuple.val (PublicDiscreteDraws.followerPlayer p.two_le_m i))
          (tuple.val (ActiveRoundActions.coordinator p.two_le_m)) ∧
        ∀ j, j ≠ i → (prepared.followers.followers j).arm =
          tuple.val (PublicDiscreteDraws.followerPlayer p.two_le_m j) := by
      obtain ⟨offered, hchecked, hfields, harm⟩ := (hfreshSame i).2.1
        ⟨xc.active i, by rw [hcurrent]; exact hslot, by rw [hcurrent]; exact hdraw⟩
      have heq : offered = U := Subtype.ext (hfields.trans hU.symm)
      subst offered
      refine ⟨?_, hchecked, ?_, ?_⟩
      · simpa only [hcurrent] using hcoordinator (by rw [hcurrent]; exact hslot)
      · simpa only [hcurrent] using harm
      · intro j hji
        have hnotData : PublicDiscreteDraws.slotDraw (xc.row.2 xc.time).1 ≠ PublicDiscreteDraws.dataSlot := by
          rw [hcurrent, hslot]
          decide
        have hnotSelected : ¬ ActiveFollowerQueueOperation.selectedUpRound j xc.row
            (xc.state.activations j) xc.time := by
          rintro ⟨_, _, hj⟩
          rw [hcurrent, hdraw] at hj
          exact hji hj.symm
        simpa only [hcurrent] using (hfreshSame j).2.2 hnotData hnotSelected
    have hevent : (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K c.1 = i ∧
        ReferenceActiveAffinePositiveTest.upPositive xc = true) ↔
        c ∈ ReferenceFirstCollectionUpConditionalService.coordinatorUpServiceFormulaSet rewards x.time i U := by
      constructor
      · rintro ⟨hdraw, hpositive⟩
        have heligible : AffineBatchDecoder.eligible (CoordinatorUpReception.roundInput input) := by
          rw [hUpFormula, hcheck] at hpositive
          exact of_decide_eq_true (by simpa only [Bool.true_and] using hpositive)
        obtain ⟨hslotActual, hobs⟩ := ReferenceUpPhysicalHashRule.receiver_eligible_observation prepared ledger heligible
        have hslot : PublicDiscreteDraws.slotDraw c.1 = PublicDiscreteDraws.upSlot := by
          simpa only [hcurrent] using hslotActual
        have hsent := upSent_of_checked_offer xc i (preparedFollower i) (memory i) U
          (by rw [hcurrent]; exact hdraw) (hfreshSame i).1 (harms hslot hdraw).2.1
        have hhash := ReferenceUpPhysicalHashRule.upPositive_hash_one xc
          (ActiveFollowerArmChoice.offeredUpWord rate.eta U) hsent hpositive
        rw [ReferenceActiveAffinePositiveTest.upSenderIndex_eq_draw, hcurrent, hdraw] at hhash
        have ha := prepared.action_coordinator.trans (harms hslot hdraw).1
        have hr := (coordinator_observation_positive_iff xc prepared _ ha).mp hobs |>.2
        have hrTable : x.rewards = rewards := by
          have hmem := List.mem_of_getElem? d.stream.cutoff.cutIndex
          exact (ReferenceActivePhysicalHorizon.run_record_inputs _ _ _ _ _ _ _ _ _ hmem).2.2
        exact ⟨hslot, hdraw, hhash, by simpa only [xc, ReferenceLaterOptionalControlResampling.withControl, hrTable] using hr⟩
      · rintro ⟨hslot, hdraw, hhash, hreward⟩
        obtain ⟨hcoordArm, _hchecked, hsenderArm, hotherArms⟩ := harms hslot hdraw
        have hcollisionFree : FiniteBanditModel.collisionFreeFor prepared.arms.actions
            (ActiveRoundActions.coordinator p.two_le_m) := by
          intro player hne
          rcases ActiveRoundActions.player_cases p.two_le_m player with hcoord | ⟨j, hplayer⟩
          · exact (hne hcoord).elim
          · have hact : prepared.arms.actions player = (prepared.followers.followers j).arm := by
              rw [hplayer]
              exact prepared.arms.actions_follower j
            rw [hact]
            by_cases hji : j = i
            · subst j
              rw [hsenderArm, prepared.action_coordinator, hcoordArm,
                ActiveFollowerArmChoice.offeredUpBit, hhash, ActiveRoundActions.sendArm_one]
              exact fun heq => ActiveRoundActions.followerPlayer_ne_coordinator p.two_le_m i (tuple.property heq)
            · rw [hotherArms j hji, prepared.action_coordinator, hcoordArm]
              exact fun heq => ActiveRoundActions.followerPlayer_ne_coordinator p.two_le_m j (tuple.property heq)
        have hrTable : x.rewards = rewards := by
          have hmem := List.mem_of_getElem? d.stream.cutoff.cutIndex
          exact (ReferenceActivePhysicalHorizon.run_record_inputs _ _ _ _ _ _ _ _ _ hmem).2.2
        have hobs := (coordinator_observation_positive_iff xc prepared _
          (prepared.action_coordinator.trans hcoordArm)).mpr
          ⟨hcollisionFree, by simpa only [xc, ReferenceLaterOptionalControlResampling.withControl, hrTable] using hreward⟩
        have hgate : CoordinatorUpReception.receptionGate input := by
          refine ⟨?_, ?_, ?_⟩
          · exact hreceiverDomain.2.2.2.2.1.trans hreceiverDomain.2.2.2.2.2.2.1.le
          · change PublicDiscreteDraws.slotDraw (xc.row.2 xc.time).1 = PublicDiscreteDraws.upSlot
            rw [hcurrent]
            exact hslot
          · change _ ∈ ledger.pending
            rw [hpending]
            exact Finset.mem_univ _
        have hselectedRound := (CoordinatorUpReception.roundInput_selected_iff_gate input).2 hgate
        have heligible : AffineBatchDecoder.eligible (CoordinatorUpReception.roundInput input) :=
          ⟨hselectedRound, rfl, hobs⟩
        refine ⟨hdraw, ?_⟩
        rw [hUpFormula, hcheck]
        simp only [heligible, decide_true, Bool.and_self]
    exact ⟨hevent, fun j => (hfreshSame j).1,
      fun h => harms h.1 h.2, ledger, hpending, hreceiverDomain, hcheck, hsite,
      hdiagnostic, hquota, hdiagdata⟩
  have hset : ReferenceFirstCollectionUpConditionalService.freshCoordinatorUpServiceSet x i =
      ReferenceFirstCollectionUpConditionalService.coordinatorUpServiceFormulaSet rewards x.time i U := by
    ext c
    exact (hforall c).1
  have hmeasure := ReferenceFirstCollectionUpConditionalService.coordinatorUpServiceFormulaSet_probability
    rewards x.time i U
  rw [← hset] at hmeasure
  have hrec := actualRecord_at_cutoff source rewards C_star C_h count hcross hspan hshort d
  refine ⟨U, hU, rfl, hUsigma, by omega, hset, hmeasure, hrec, ?_, fun c => (hforall c).2⟩
  intro control0
  have hm : (2 : ℝ) ≤ p.m := by exact_mod_cast p.two_le_m
  have hmpos : 0 < (p.m : ℝ) - 1 := by linarith
  rw [ReferenceFirstCollectionUpConditionalService.actualFirstCollectionUpFreshSection_eq_measure
    rewards C_star C_h control0 i x.time source d.stream.cutoff.cut hrec,
    measureReal_def, hmeasure, ENNReal.toReal_ofReal (by positivity)]

/-- A single null set is removed before all finite first-cutoff selectors and
formed-reply witnesses. The conditioning sigma-algebra is the existing `m_t`. -/
theorem actual_first_cutoff_up_condExp_service
    (rate : RateInput p) (rewards : RewardTable p) (C_star C_h : ℝ)
    (control0 : TimeControl p) :
    ∀ᵐ source ∂BootstrapPrivateRoundStreams.sourceInputLaw p,
    ∀ (count : ℕ)
      (hcross : (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
      (hspan : ReferenceFirstCollectionReadyStream.startTime (rate := rate)
        source rewards C_star C_h + count ≤ p.T)
      (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
          source rewards C_star C_h hcross count hspan).records).length < count),
    ∃ d : ReferenceFirstCollectionStreamEmptyDispatch.ActualInitializedStreamDispatch
        source rewards C_star C_h count hcross hspan hshort,
    ∃ (old : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
      (memory : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p),
    let x := d.stream.cutoff.cut.input
    let preparedFollower := fun j => { old j with status := ActiveRoundActions.FollowerStatus.unoccupied }
    (∀ j, x.state.followers j = .ordinary (old j) (memory j) ∧
      ActiveFollowerLifecycle.startRound rate.eta x.time (old j) (memory j) =
        .ok (preparedFollower j, memory j) ∧
      ((ReferenceActivePhysicalStep.prepare x).followers.followers j).configuration =
        .ordinary (preparedFollower j) (memory j) ∧
      ActiveFollowerLifecycle.localStateDomainValid (preparedFollower j)) ∧
    ∀ i : Fin (p.m - 1), 1 ≤ ReferencePrelaunchFollower.acceptedStart (old i) →
    ∃ U : OrdinaryMessageCodec.UpRecord (ReferencePrelaunchFollower.codecParams p rate.eta),
      U.val = ActiveFollowerQueueOperation.upOfferFields (preparedFollower i) ∧
      U.val = ActiveFollowerQueueOperation.upOfferFields (old i) ∧
      U.val.sigma = ReferenceFirstCollectionReadyStream.startTime (rate := rate)
        source rewards C_star C_h + 1 ∧ 1 ≤ U.val.sigma ∧
      (BootstrapPrivateRoundStreams.sourceInputLaw p)[
        ReferenceFirstCollectionUpConditionalService.actualFirstCollectionUpReadout (rate := rate)
          rewards C_star C_h i x.time |
          ReferenceSourceCurrentControlFreshness.m_t p control0 x.time] source =
        (ReferenceFirstCollectionUpConditionalService.positiveRewardCount rewards x.time : ℝ) /
          (8 * (p.m - 1 : ℝ) * p.K) := by
  have hce : ∀ᵐ source ∂BootstrapPrivateRoundStreams.sourceInputLaw p,
      ∀ i : Fin (p.m - 1), ∀ t : Fin p.T,
      (BootstrapPrivateRoundStreams.sourceInputLaw p)[
        ReferenceFirstCollectionUpConditionalService.actualFirstCollectionUpReadout (rate := rate)
          rewards C_star C_h i t | ReferenceSourceCurrentControlFreshness.m_t p control0 t] source =
        ReferenceFirstCollectionUpConditionalService.actualFirstCollectionUpFreshSection (rate := rate)
          rewards C_star C_h control0 i t source :=
    ae_all_iff.mpr fun i => ae_all_iff.mpr fun t =>
      ReferenceFirstCollectionUpConditionalService.actual_first_collection_up_condExp
        rewards C_star C_h control0 i t
  filter_upwards [hce] with source hce
  intro count hcross hspan hshort
  obtain ⟨d, old, memory, hfollowers, hbranch⟩ := actual_first_cutoff_up_service_coefficient
    rate source rewards C_star C_h count hcross hspan hshort
  refine ⟨d, old, memory, hfollowers, ?_⟩
  intro i hpositive
  obtain ⟨U, hU, hUold, hsigma, hpos, _hset, _hprobability, _hrecord, hsection, _hlocal⟩ :=
    hbranch i hpositive
  exact ⟨U, hU, hUold, hsigma, hpos,
    (hce i d.stream.cutoff.cut.input.time).trans (hsection control0)⟩

end Bandits.Support.ReferenceFirstCutoffUpConditionalService

end
