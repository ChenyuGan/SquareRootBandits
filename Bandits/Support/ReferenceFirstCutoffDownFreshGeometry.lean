/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCutoffDownControlGeometry

/-!
# Actual first-cutoff OLD DOWN fresh-control geometry

Sources: `sources/zip4/manuscript/06_interruptions.tex:477-481`,
`sources/zip4/manuscript/05_binary_transport.tex:33-48,72-78,94-124`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:44-60,100-106`.

The cutoff boundary is produced on the original complete source. Replacing
current control preserves the incoming state and saved previous proposal;
CHOICE is recomputed on the new current control. No probability, allowance,
decoder success, or manuscript closure is asserted.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions
open scoped Classical

namespace Bandits.Support.ReferenceFirstCutoffDownFreshGeometry

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
      liveCutoffTag (ReferenceActivePhysicalStep.liveRegistersAt r x.time)
        (ReferenceActivePhysicalStep.liveOwnedAt r q x.time) base x.row
        (CoordinatorRoundDispatch.dispatchLive (ReferenceActivePhysicalStep.liveInput x r q base)) := by
  dsimp only [ReferenceCollectionPhaseHistory.cutoffChosen,
    ReferenceActivePhysicalStep.prepare, ReferenceActivePhysicalStep.dispatch]
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
      dsimp only [ReferenceCollectionPhaseHistory.cutoffChosen,
        ReferenceActivePhysicalStep.prepare, ReferenceActivePhysicalStep.dispatch]
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
      dsimp only [ReferenceCollectionPhaseHistory.cutoffChosen,
        ReferenceActivePhysicalStep.prepare, ReferenceActivePhysicalStep.dispatch]
      simp only [hphase]
      by_cases hc : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
      · simp only [dite_eq_left hc, CoordinatorRoundDispatch.dispatch]
        rfl
      · simp only [dite_eq_right hc]
  | dagger =>
      dsimp only [ReferenceCollectionPhaseHistory.cutoffChosen,
        ReferenceActivePhysicalStep.prepare, ReferenceActivePhysicalStep.dispatch]
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
    (hspan : ReferenceFirstCollectionReadyStream.startTime (rate := rate)
      source rewards C_star C_h + count ≤ p.T)
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
        source rewards C_star C_h hc count hspan).records).length < count)
    (d : ReferenceFirstCollectionStreamEmptyDispatch.ActualInitializedStreamDispatch
      source rewards C_star C_h count hc hspan hshort) :
    ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
      d.stream.cutoff.cut.input.time source = some d.stream.cutoff.cut := by
  let initial := ReferenceFirstCollectionEpochAlignment.actualLaunchState
    rate source rewards C_star C_h hc
  let s := ReferenceFirstCollectionReadyStream.startTime (rate := rate) source rewards C_star C_h
  let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
    (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
      source rewards C_star C_h hc count hspan).records).length
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
    cases hb : ReferenceCollectionPhaseHistory.cutoffChosen record.input <;>
      simp_all only [Bool.not_false, Bool.not_true, Bool.false_eq_true]
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

/-- Actual receiver domain and call site at cutoff. The finite coordinate
supplied to the generated receiver producer is the elapsed launch start. -/
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
    ∃ ledger : ReferenceActivePhysicalStep.Ledger rate,
      ledger.pending = Finset.univ ∧
      CoordinatorUpReception.receptionInputDomain
        (ReferenceCoordinatorUpPhysicalCall.actualUpInput x ledger) ∧
      CoordinatorUpReception.receptionInputCheck
        (ReferenceCoordinatorUpPhysicalCall.actualUpInput x ledger) = true ∧
      ReferenceCoordinatorUpPhysicalCall.siteLedger? (x := x) = some ledger := by
  classical
  intro x
  let prepared := ReferenceActivePhysicalStep.prepare x
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
    ledger, hstart, hcandidate, input, hinput, hreceiver, hcheck, _⟩ :=
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
  simp only [hprep] at hchosen hrecording hinput
  have hbridge : CoordinatorRecorderComplementBridge.run
      (ReferenceActivePhysicalStep.collectionRecordingInput prepared r.payload
        dispatched.startResult (ReferenceActivePhysicalStep.liveRegistersAt r x.time).complementWeights) =
      some recording := hrecording
  have hselection : prepared.coordinator.selection ≠ none := by
    rw [hchosen]
    simp [ReferenceActivePhysicalStep.DispatchCut.selection, ReferenceActivePhysicalStep.selectionAt]
  refine ⟨ledger, ?_, ?_, ?_, ?_⟩
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

/-- Literal initializer and newly checked CHOICE at an actual cutoff. The
row is the current source row; no old arm choice is transported. -/
theorem actual_cutoff_initializer_and_choice
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
    ∃ selected : ReferenceActivePhysicalStep.Selection x,
      (ReferenceActivePhysicalStep.prepare x).coordinator.selection = some selected ∧
      selected.view.payload = d.stream.payload ∧
      selected.view.pendingAtChoice = Finset.univ ∧
      CoordinatorLocalArmChoice.ChoiceInputsValid selected.view.payload
        selected.view.cutoff x.time selected.view.complementWeights ∧
      selected.started.clock.g ≤ p.T + 1 ∧
      ∃ (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
        (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
        (base : Fin (p.m - 1) → ℕ)
        (dispatched : CoordinatorStartRoundCutoffDispatch.Output
          (ReferenceActivePhysicalStep.liveRegistersAt r x.time)
          (ReferenceActivePhysicalStep.liveOwnedAt r q x.time) base)
        (ledger : CoordinatorStartRoundCutoffDispatch.NewLedger
          (ReferenceActivePhysicalStep.liveRegistersAt r x.time))
        (hstart : CoordinatorPhaseClock.startRound p rate.eta.val x.time r.priorClock
          r.clockPending = .ok dispatched.startResult)
        (hinit : dispatched.collectionInitialization = .success (some ledger))
        (hledger : ledger = CoordinatorStartRoundCutoffDispatch.collectionStartLedger
          (ReferenceActivePhysicalStep.liveRegistersAt r x.time)
          (ReferenceActivePhysicalStep.liveOwnedAt r q x.time) base x.time)
        (hdomain : CoordinatorStartRoundCutoffDispatch.initializationDomainValid
          (ReferenceActivePhysicalStep.liveRegistersAt r x.time)
          (ReferenceActivePhysicalStep.liveOwnedAt r q x.time) base x.time)
        (hclock : dispatched.startResult.clock = { r.priorClock with u := some x.time })
        (hpending : dispatched.startResult.pending = Finset.univ)
        (hnone : dispatched.startResult.assignmentStart = none)
        (choice : CoordinatorRoundDispatch.ArmSelection r.payload dispatched.startResult
          x.time (ReferenceActivePhysicalStep.liveRegistersAt r x.time).complementWeights x.row),
        x.state.coordinator = .live r q base ∧
        selected.view.payload = r.payload ∧ selected.started = dispatched.startResult ∧
        (ReferenceActivePhysicalStep.liveRegistersAt r x.time).complementEnvelopeValid ∧
        (ReferenceActivePhysicalStep.prepare x).coordinator = .live r q base
          (.cutoffChosen dispatched hstart ledger hinit hledger hdomain hclock hpending hnone choice) := by
  classical
  intro x
  let initial := ReferenceFirstCollectionEpochAlignment.actualLaunchState
    rate source rewards C_star C_h hc
  have hraw := ReferenceFirstCutoffRecordedService.run_first_cutoff_recorded_service
    initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
    rewards _ count hspan
    (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
      rate source rewards C_star C_h hc).1
    (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
      rate source rewards C_star C_h hc).2 hshort
  rcases hraw with ⟨cut, suffix, hsplit, hi, ht, r, q, base, hs, hp,
    dispatched, hstart, ledger, hinit, hledger, hdomain, hclock, hpending,
    hnone, selected, hchosen, _⟩
  have hget : (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
      source rewards C_star C_h hc count hspan).records[
      (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
          source rewards C_star C_h hc count hspan).records).length]? = some cut := by
    rw [hi]
    exact List.getElem?_eq_getElem _
  have heq : cut = d.stream.cutoff.cut := Option.some.inj (hget.symm.trans d.stream.cutoff.cutIndex)
  clear hi
  subst cut
  have hphase : x.state.coordinator = .live r q base := hs ▸ hp
  have hprep : d.stream.cutoff.cut.output.preparation = ReferenceActivePhysicalStep.prepare x :=
    congrArg ReferenceActivePhysicalStep.RoundOutput.preparation d.stream.cutoff.cut.output_eq
  rw [hprep] at hchosen
  let sel : ReferenceActivePhysicalStep.Selection x := {
    view := {
      payload := r.payload
      pendingAtChoice := dispatched.startResult.pending
      cutoff := CoordinatorLiveChoiceRecorderStep.cutoffFromClock p dispatched.startResult.clock.u
      complementWeights := (ReferenceActivePhysicalStep.liveRegistersAt r x.time).complementWeights }
    started := dispatched.startResult
    pending_eq := rfl
    cutoff_eq := rfl
    arm := selected.arm
    choice_eq := selected.armChoice_eq }
  have hsel : (ReferenceActivePhysicalStep.prepare x).coordinator.selection = some sel := by
    rw [hchosen]
    change ReferenceActivePhysicalStep.selectionAt x r.payload dispatched.startResult x.time
      (ReferenceActivePhysicalStep.liveRegistersAt r x.time).complementWeights selected = some sel
    unfold ReferenceActivePhysicalStep.selectionAt
    rw [dite_eq_left rfl]
  have hpay : r.payload = d.stream.payload := by
    obtain ⟨ce⟩ := d.stream.cutoffExecution
    have he : ReferenceActivePhysicalStep.CoordinatorConfiguration.live r q base = .live ce.live ce.owned ce.base :=
      hphase.symm.trans ce.actualLive
    cases he
    exact (d.stream.payloadMatchesCutoff.trans ce.payloadIsLive).symm
  exact ⟨sel, hsel, hpay, hpending, selected.choiceInputsValid,
    selected.recorderBoundaryValid, r, q, base, dispatched, ledger,
    hstart, hinit, hledger, hdomain, hclock, hpending, hnone, selected,
    hphase, rfl, rfl, (fun j => ⟨selected.choiceInputsValid.anchor_le_current j,
      selected.choiceInputsValid.current_le_twice_anchor j⟩), hchosen⟩

/-- The actual observation continuation retains receiver diagnostics even
when a later local operation fails. -/
private theorem finishFollower_diagnostics
    (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (prepared : DeclaredFollowerLocalRound.PreparedRound p rate)
    (observation : ReferencePrelaunchFollower.Observation p)
    (choice : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hc : prepared.configuration = .ordinary choice memory) :
    let recorded := ReferenceActivePhysicalStep.recordFollower view prepared.follower
      prepared.row prepared.activation prepared.time prepared.active prepared.arm observation choice
    (ReferenceActivePhysicalStep.finishFollower view prepared observation).downInput = recorded.downInput ∧
    (ReferenceActivePhysicalStep.finishFollower view prepared observation).down = recorded.down := by
  dsimp only
  unfold ReferenceActivePhysicalStep.finishFollower
  rw [hc]
  dsimp only
  cases hr : (ReferenceActivePhysicalStep.recordFollower view prepared.follower prepared.row
      prepared.activation prepared.time prepared.active prepared.arm observation choice).result with
  | error failure => exact ⟨rfl, rfl⟩
  | ok post =>
    simp only
    cases hf : DeclaredFollowerLocalRound.releaseAndFinish rate prepared.follower prepared.row
        prepared.time observation choice memory post with
    | error failure => exact ⟨rfl, rfl⟩
    | ok pair => cases pair; exact ⟨rfl, rfl⟩

/-- OLD DOWN geometry on the actual first cutoff. The fixed stored word is
bound before all fresh controls. The next consumer is the actual cutoff OLD
DOWN fresh section/coefficient, followed by stopped collection allowance. -/
theorem actual_first_cutoff_down_control_geometry
    (rate : RateInput p) (source : SourceInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (count : ℕ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hspan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed +
          count ≤ p.T)
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
        rate source rewards C_star C_h hcross count hspan).records).length < count) :
    let E := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
      rate source rewards C_star C_h hcross count hspan
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records).length
    let B := ReferenceCollectionPhaseHistory.collectionWindow E.records w
    ∃ d : ReferenceFirstCollectionStreamEmptyDispatch.ActualInitializedStreamDispatch
        source rewards C_star C_h count hcross hspan hshort,
      let x := d.stream.cutoff.cut.input
      d.stream.window = B ∧
      d.stream.window[0]'d.stream.windowNonempty = d.stream.cutoff.cut ∧
      x.time.val = ReferenceFirstCollectionReadyStream.startTime (rate := rate)
        source rewards C_star C_h + w ∧
      x.rows = source.1.2 ∧
      x.selected = ActualInitializationPhysicalStep.selectedRowIndex p source ∧
      x.rewards = rewards ∧
      ∃ (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
        (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
        (base : Fin (p.m - 1) → ℕ)
        (old : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
        (memory : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p),
      x.state.coordinator = .live r q base ∧ d.stream.payload = r.payload ∧
      (∀ j, x.state.followers j = .ordinary (old j) (memory j) ∧
        let cj : ReferencePrelaunchFollower.State p rate.eta := { old j with status := .unoccupied }
        cj.lastDown = (old j).lastDown ∧ cj.S = (old j).S ∧
        cj.delta = (old j).delta ∧ cj.backlog = (old j).backlog ∧
        cj.buffer = (old j).buffer ∧ cj.downBatch = (old j).downBatch ∧
        cj.initializationFailure = (old j).initializationFailure ∧
        ActiveFollowerLifecycle.localStateDomainValid cj ∧
        ActiveFollowerLifecycle.startRound rate.eta x.time (old j) (memory j) = .ok (cj, memory j)) ∧
      ∀ i : Fin (p.m - 1), (old i).lastDown = none →
      let wD := CoordinatorLocalArmChoice.storedDownFlatWord r.payload i
      wD = OrdinaryMessageCodec.wordEquivFlat (ReferencePrelaunchFollower.codecParams p rate.eta)
        (OrdinaryMessageCodec.encodeDown (ReferencePrelaunchFollower.codecParams p rate.eta)
          (r.payload.downRecord i)) ∧
      ReferenceDownReception.ordinaryParse p rate (some wD) = some (r.payload.downRecord i) ∧
      ∀ c : TimeControl p,
      let xc := ReferenceLaterOptionalControlResampling.withControl x c
      let prepared := ReferenceActivePhysicalStep.prepare xc
      let tuple := OrderedTupleSampler.sample p.two_le_m p.m_lt_K c.1
      ∃ selected : ReferenceActivePhysicalStep.Selection xc,
        prepared.coordinator.selection = some selected ∧
        selected.view.payload = r.payload ∧ selected.view.pendingAtChoice = Finset.univ ∧
        CoordinatorLocalArmChoice.ChoiceInputsValid selected.view.payload
          selected.view.cutoff xc.time selected.view.complementWeights ∧
        selected.started.clock.g ≤ p.T + 1 ∧
        (∃ (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
          (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
          (base : Fin (p.m - 1) → ℕ)
          (dispatched : CoordinatorStartRoundCutoffDispatch.Output
            (ReferenceActivePhysicalStep.liveRegistersAt r xc.time)
            (ReferenceActivePhysicalStep.liveOwnedAt r q xc.time) base)
          (ledger : CoordinatorStartRoundCutoffDispatch.NewLedger
            (ReferenceActivePhysicalStep.liveRegistersAt r xc.time))
          (hstart : CoordinatorPhaseClock.startRound p rate.eta.val xc.time r.priorClock
            r.clockPending = .ok dispatched.startResult)
          (hinit : dispatched.collectionInitialization = .success (some ledger))
          (hledger : ledger = CoordinatorStartRoundCutoffDispatch.collectionStartLedger
            (ReferenceActivePhysicalStep.liveRegistersAt r xc.time)
            (ReferenceActivePhysicalStep.liveOwnedAt r q xc.time) base xc.time)
          (hdomain : CoordinatorStartRoundCutoffDispatch.initializationDomainValid
            (ReferenceActivePhysicalStep.liveRegistersAt r xc.time)
            (ReferenceActivePhysicalStep.liveOwnedAt r q xc.time) base xc.time)
          (hclock : dispatched.startResult.clock = { r.priorClock with u := some xc.time })
          (hpending : dispatched.startResult.pending = Finset.univ)
          (hnone : dispatched.startResult.assignmentStart = none)
          (choice : CoordinatorRoundDispatch.ArmSelection r.payload dispatched.startResult
            xc.time (ReferenceActivePhysicalStep.liveRegistersAt r xc.time).complementWeights xc.row),
          xc.state.coordinator = .live r q base ∧
          selected.view.payload = r.payload ∧ selected.started = dispatched.startResult ∧
          (ReferenceActivePhysicalStep.liveRegistersAt r xc.time).complementEnvelopeValid ∧
          (ReferenceActivePhysicalStep.prepare xc).coordinator = .live r q base
            (.cutoffChosen dispatched hstart ledger hinit hledger hdomain hclock hpending hnone choice)) ∧
        (∀ j, (prepared.followers.followers j).configuration =
          .ordinary { old j with status := .unoccupied } (memory j)) ∧
        Function.Injective tuple.val ∧
        ((PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K c.1 = i ∧
            ReferenceActiveAffinePositiveTest.downPositive xc = true) ↔
          PublicDiscreteDraws.slotDraw c.1 = PublicDiscreteDraws.downSlot ∧
          PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K c.1 = i ∧
          AffineChannelLaw.affineHash (c.2 (0, i)) wD = 1 ∧
          0 < rewards x.time (tuple.val (PublicDiscreteDraws.followerPlayer p.two_le_m i))) ∧
        (∃ ledger : ReferenceActivePhysicalStep.Ledger rate,
          CoordinatorUpReception.receptionInputDomain
            (ReferenceCoordinatorUpPhysicalCall.actualUpInput xc ledger) ∧
          CoordinatorUpReception.receptionInputCheck
            (ReferenceCoordinatorUpPhysicalCall.actualUpInput xc ledger) = true ∧
          ReferenceCoordinatorUpPhysicalCall.siteLedger? (x := xc) = some ledger) ∧
        (PublicDiscreteDraws.slotDraw c.1 = PublicDiscreteDraws.downSlot ∧
            PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K c.1 = i →
          prepared.arms.actions (ActiveRoundActions.coordinator p.two_le_m) =
            ActiveRoundActions.sendArm (AffineChannelLaw.affineHash (c.2 (0, i)) wD)
              (tuple.val (ActiveRoundActions.coordinator p.two_le_m))
              (tuple.val (PublicDiscreteDraws.followerPlayer p.two_le_m i)) ∧
          (∀ j, prepared.arms.actions (PublicDiscreteDraws.followerPlayer p.two_le_m j) =
            tuple.val (PublicDiscreteDraws.followerPlayer p.two_le_m j)) ∧
          let ci : ReferencePrelaunchFollower.State p rate.eta := { old i with status := .unoccupied }
          let own := prepared.feedback.observations (PublicDiscreteDraws.followerPlayer p.two_le_m i)
          let cut := ReferenceDownReception.referenceDownCut p prepared.coordinator.downView
            i xc.row xc.time own rate ci
          ci.lastDown = none ∧
          OrdinaryMessageCodec.acceptDown (ReferencePrelaunchFollower.codecParams p rate.eta)
            (ReferencePrelaunchFollower.acceptedStart ci) (xc.time.val + 1) (r.payload.downRecord i) ∧
          ActiveFollowerDownAcceptance.operationInputDomain p rate ci ∧
          ActiveFollowerLogging.checkedLogging i xc.row (xc.state.activations i) xc.time
            ((prepared.followers.followers i).arm, own) ci = .ok ci ∧
          (ReferenceActivePhysicalStep.recordFollower prepared.coordinator.downView i xc.row
            (xc.state.activations i) xc.time (xc.active i)
            (prepared.followers.followers i).arm own ci).downInput = some ci ∧
          (ReferenceActivePhysicalStep.recordFollower prepared.coordinator.downView i xc.row
            (xc.state.activations i) xc.time (xc.active i)
            (prepared.followers.followers i).arm own ci).down = some cut ∧
          (prepared.observeFollower i).downInput = some ci ∧
          (prepared.observeFollower i).down = some cut ∧
          cut.expectedWord = some wD ∧ cut.rawComparison.isSome = true ∧
          cut.raw = (ActiveFollowerDownAcceptance.currentDecodeStep p i xc.row xc.time own rate ci).2 ∧
          (own.val = 0 → ActiveFollowerDownAcceptance.currentDecodeStep
            p i xc.row xc.time own rate ci = (ci.downBatch, none))) := by
  classical
  intro E w B
  obtain ⟨d, hwindow, hhead, htime, hrows, hJ, hreward, r, q, base, hphase, hpay, hf⟩ :=
    ReferenceFirstCutoffDownControlGeometry.actual_first_cutoff_source_geometry
      rate source rewards C_star C_h count hcross hspan hshort
  let x := d.stream.cutoff.cut.input
  dsimp only at hf
  choose old memory hstate hstatus hlast hS hdelta hbacklog hbuffer hbatch hfailure hvalid hstart using hf
  refine ⟨d, hwindow, hhead, htime, hrows, hJ, hreward, r, q, base,
    old, memory, hphase, hpay, ?_, ?_⟩
  · intro j
    exact ⟨hstate j, hlast j, hS j, hdelta j, hbacklog j, hbuffer j,
      hbatch j, hfailure j, hvalid j, hstart j⟩
  · intro i hnone wD
    refine ⟨rfl, ?_, ?_⟩
    · unfold ReferenceDownReception.ordinaryParse
      change OrdinaryMessageCodec.parseDown (ReferencePrelaunchFollower.codecParams p rate.eta)
        (some ((OrdinaryMessageCodec.wordEquivFlat
          (ReferencePrelaunchFollower.codecParams p rate.eta)).symm
          ((OrdinaryMessageCodec.wordEquivFlat
            (ReferencePrelaunchFollower.codecParams p rate.eta)) (r.payload.downWord i)))) = _
      rw [Equiv.symm_apply_apply]
      exact r.payload.parseDown_downWord i
    · intro c xc prepared tuple
      let z := ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p x.time source c
      obtain ⟨hc', _hs', hspan', hshort', d', hinput⟩ :=
        fresh_cutoff_dispatch source rewards C_star C_h count hcross hspan hshort d c
      change d'.stream.cutoff.cut.input = xc at hinput
      obtain ⟨sel, hsel, hselPay, hselPending, hchoice, hboundary, hinit⟩ :=
        actual_cutoff_initializer_and_choice z rewards C_star C_h _ hc' hspan' hshort' d'
      have hpay' : d'.stream.payload = r.payload := by
        obtain ⟨ce⟩ := d'.stream.cutoffExecution
        have hlive : ReferenceActivePhysicalStep.CoordinatorConfiguration.live ce.live ce.owned ce.base =
            .live r q base := ce.actualLive.symm.trans (by rw [hinput]; exact hphase)
        cases hlive
        exact d'.stream.payloadMatchesCutoff.trans ce.payloadIsLive
      have hselection : ∃ selected : ReferenceActivePhysicalStep.Selection xc,
          prepared.coordinator.selection = some selected ∧
          selected.view.payload = r.payload ∧ selected.view.pendingAtChoice = Finset.univ ∧
          CoordinatorLocalArmChoice.ChoiceInputsValid selected.view.payload
            selected.view.cutoff xc.time selected.view.complementWeights ∧
          selected.started.clock.g ≤ p.T + 1 ∧
          (∃ (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
            (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
            (base : Fin (p.m - 1) → ℕ)
            (dispatched : CoordinatorStartRoundCutoffDispatch.Output
              (ReferenceActivePhysicalStep.liveRegistersAt r xc.time)
              (ReferenceActivePhysicalStep.liveOwnedAt r q xc.time) base)
            (ledger : CoordinatorStartRoundCutoffDispatch.NewLedger
              (ReferenceActivePhysicalStep.liveRegistersAt r xc.time))
            (hstart : CoordinatorPhaseClock.startRound p rate.eta.val xc.time r.priorClock
              r.clockPending = .ok dispatched.startResult)
            (hinit : dispatched.collectionInitialization = .success (some ledger))
            (hledger : ledger = CoordinatorStartRoundCutoffDispatch.collectionStartLedger
              (ReferenceActivePhysicalStep.liveRegistersAt r xc.time)
              (ReferenceActivePhysicalStep.liveOwnedAt r q xc.time) base xc.time)
            (hdomain : CoordinatorStartRoundCutoffDispatch.initializationDomainValid
              (ReferenceActivePhysicalStep.liveRegistersAt r xc.time)
              (ReferenceActivePhysicalStep.liveOwnedAt r q xc.time) base xc.time)
            (hclock : dispatched.startResult.clock = { r.priorClock with u := some xc.time })
            (hpending : dispatched.startResult.pending = Finset.univ)
            (hnone : dispatched.startResult.assignmentStart = none)
            (choice : CoordinatorRoundDispatch.ArmSelection r.payload dispatched.startResult
              xc.time (ReferenceActivePhysicalStep.liveRegistersAt r xc.time).complementWeights xc.row),
            xc.state.coordinator = .live r q base ∧
            selected.view.payload = r.payload ∧ selected.started = dispatched.startResult ∧
            (ReferenceActivePhysicalStep.liveRegistersAt r xc.time).complementEnvelopeValid ∧
            (ReferenceActivePhysicalStep.prepare xc).coordinator = .live r q base
              (.cutoffChosen dispatched hstart ledger hinit hledger hdomain hclock hpending hnone choice)) := by
        have hdata := And.intro hsel (And.intro (hselPay.trans hpay')
          (And.intro hselPending (And.intro hchoice (And.intro hboundary hinit))))
        dsimp only [prepared]
        rw [← hinput]
        exact ⟨sel, hdata⟩
      obtain ⟨selected, hselected, hpayload, hpending, hchoice, hboundary, hinit⟩ := hselection
      have hcurrent : xc.row.2 xc.time = c :=
        ReferenceLaterOptionalControlResampling.withControl_currentControl x c
      have hfresh := actual_cutoff_followers z rewards C_star C_h _ hc' hspan' hshort' d'
      dsimp only at hfresh
      have hprep' : d'.stream.cutoff.cut.output.preparation =
          ReferenceActivePhysicalStep.prepare d'.stream.cutoff.cut.input :=
        congrArg ReferenceActivePhysicalStep.RoundOutput.preparation d'.stream.cutoff.cut.output_eq
      simp only [hprep', hinput] at hfresh
      have hfamily (j : Fin (p.m - 1)) :
          (prepared.followers.followers j).configuration =
            .ordinary { old j with status := .unoccupied } (memory j) ∧
          (PublicDiscreteDraws.slotDraw c.1 = PublicDiscreteDraws.downSlot →
            prepared.arms.actions (PublicDiscreteDraws.followerPlayer p.two_le_m j) =
              tuple.val (PublicDiscreteDraws.followerPlayer p.two_le_m j)) := by
        obtain ⟨before, μ, hbefore, _hstart', hconfig, _hdomain, _hmass, _hlast, _hup, hother⟩ := hfresh j
        have hid : DeclaredFollowerLocalRound.LocalConfiguration.ordinary before μ =
            .ordinary (old j) (memory j) := hbefore.symm.trans (hstate j)
        injection hid with he hm
        subst before
        subst μ
        have hconfigEq := congrArg (fun v : ReferenceActivePhysicalStep.RoundInput p rate =>
          ((ReferenceActivePhysicalStep.prepare v).followers.followers j).configuration) hinput
        have harmEq := congrArg (fun v : ReferenceActivePhysicalStep.RoundInput p rate =>
          ((ReferenceActivePhysicalStep.prepare v).followers.followers j).arm) hinput
        rw [hconfigEq] at hconfig
        rw [harmEq] at hother
        refine ⟨hconfig, ?_⟩
        intro hslot
        have hnotData : PublicDiscreteDraws.slotDraw (xc.row.2 xc.time).1 ≠ PublicDiscreteDraws.dataSlot := by
          rw [hcurrent, hslot]
          decide
        have hnotUp : ¬ ActiveFollowerQueueOperation.selectedUpRound j xc.row
            (xc.state.activations j) xc.time := by
          rintro ⟨_, hu, _⟩
          rw [hcurrent, hslot] at hu
          exact (by decide : PublicDiscreteDraws.downSlot ≠ PublicDiscreteDraws.upSlot) hu
        have ho : (prepared.followers.followers j).arm =
            (OrderedTupleSampler.sample p.two_le_m p.m_lt_K (xc.row.2 xc.time).1).val
              (PublicDiscreteDraws.followerPlayer p.two_le_m j) := hother hnotData hnotUp
        rw [hcurrent] at ho
        exact (prepared.arms.actions_follower j).trans ho
      have harms (hs : PublicDiscreteDraws.slotDraw c.1 = PublicDiscreteDraws.downSlot)
          (hi : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K c.1 = i) :
          prepared.arms.actions (ActiveRoundActions.coordinator p.two_le_m) =
            ActiveRoundActions.sendArm (AffineChannelLaw.affineHash (c.2 (0, i)) wD)
              (tuple.val (ActiveRoundActions.coordinator p.two_le_m))
              (tuple.val (PublicDiscreteDraws.followerPlayer p.two_le_m i)) := by
        have hb : ReferenceDownReception.selectedDownSenderBranch selected.view i xc.row xc.time :=
          ⟨by rw [hcurrent]; exact hs, by rw [hcurrent]; exact hi, by rw [hpending]; exact Finset.mem_univ i⟩
        simpa only [CoordinatorLocalArmChoice.currentDownHash, CoordinatorLocalArmChoice.downChannel,
          hpayload, hcurrent] using
            ReferenceActivePhysicalStep.action_eq_down_sendArm prepared selected hselected i hb
      have hevent : (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K c.1 = i ∧
          ReferenceActiveAffinePositiveTest.downPositive xc = true) ↔
          PublicDiscreteDraws.slotDraw c.1 = PublicDiscreteDraws.downSlot ∧
          PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K c.1 = i ∧
          AffineChannelLaw.affineHash (c.2 (0, i)) wD = 1 ∧
          0 < rewards x.time (tuple.val (PublicDiscreteDraws.followerPlayer p.two_le_m i)) := by
        by_cases hi : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K c.1 = i
        · have hindex : ReferenceActivePhysicalStep.upSenderIndex xc = i := by
            rw [ReferenceActiveAffinePositiveTest.upSenderIndex_eq_draw, hcurrent]
            exact hi
          have hg := ReferenceFirstCutoffDownControlGeometry.down_gate_eq_decide_downSelected_of_prepared_unoccupied
            xc i _ (memory i) hindex (hfamily i).1 rfl (hvalid i)
          by_cases hs : PublicDiscreteDraws.slotDraw c.1 = PublicDiscreteDraws.downSlot
          · have he := ReferenceFirstCutoffDownControlGeometry.old_down_event_iff_prepared_unoccupied
              xc i _ (memory i) wD hindex (hfamily i).1 rfl (hvalid i)
              (by simpa only [hcurrent] using harms hs hi)
              (fun j => by simpa only [hcurrent] using (hfamily j).2 hs)
            rw [hcurrent] at he
            simpa only [show xc.rewards = rewards from hreward,
              show xc.time = x.time from rfl, tuple] using he
          · have hn : ¬ ActiveFollowerDownAcceptance.downSelected p i xc.row xc.time := by
              rintro ⟨hd, _⟩
              rw [hcurrent] at hd
              exact hs hd
            have hp : ReferenceActiveAffinePositiveTest.downPositive xc = false := by
              rw [ReferenceActiveAffinePositiveTest.downPositive_eq_gate_feedback, hg]
              simp only [decide_eq_false hn, Bool.false_and]
            simp only [hp, Bool.false_eq_true, and_false, hs, false_and]
        · simp only [hi, false_and, and_false]
      have hreceiver := actual_cutoff_receiver z rewards C_star C_h _ hc' hspan' hshort' d'
      dsimp only at hreceiver
      obtain ⟨ledger, _hpending, hdom, hcheck, hsite⟩ := hreceiver
      have hreceiverOut : ∃ ledger : ReferenceActivePhysicalStep.Ledger rate,
          CoordinatorUpReception.receptionInputDomain (ReferenceCoordinatorUpPhysicalCall.actualUpInput xc ledger) ∧
          CoordinatorUpReception.receptionInputCheck
            (ReferenceCoordinatorUpPhysicalCall.actualUpInput xc ledger) = true ∧
          ReferenceCoordinatorUpPhysicalCall.siteLedger? (x := xc) = some ledger := by
        rw [← hinput]
        exact ⟨ledger, hdom, hcheck, hsite⟩
      refine ⟨selected, hselected, hpayload, hpending, hchoice, hboundary, hinit,
        fun j => (hfamily j).1, tuple.property, hevent, hreceiverOut, ?_⟩
      rintro ⟨hs, hi⟩
      refine ⟨harms hs hi, fun j => (hfamily j).2 hs, ?_⟩
      dsimp only
      let ci : ReferencePrelaunchFollower.State p rate.eta := { old i with status := .unoccupied }
      let own := prepared.feedback.observations (PublicDiscreteDraws.followerPlayer p.two_le_m i)
      have hregisters : ActiveFollowerDownAcceptance.registerInputDomain p rate ci := (hvalid i).1
      have hdecoder : ActiveFollowerDownAcceptance.decoderInputDomain p ci.downBatch := (hvalid i).2.2
      have hbuf : ActiveFollowerDownAcceptance.bufferInputDomain p ci.buffer :=
        (FollowerLifecycleMeasurability.localBufferValid_iff_bufferInputDomain ci).mp (hvalid i).2.1
      have hlogging : ActiveFollowerLogging.checkedLogging i xc.row (xc.state.activations i) xc.time
          ((prepared.followers.followers i).arm, own) ci = .ok ci := by
        rw [ReferenceActiveAffinePositiveTest.checkedLogging_eq_of_down _ _ _ _ _ _
          (by rw [hcurrent]; exact hs), ite_eq_left (hvalid i).2.1]
      have hrecord := ReferenceActivePhysicalStep.recordFollower_logged prepared.coordinator.downView
        i xc.row (xc.state.activations i) xc.time (xc.active i)
        (prepared.followers.followers i).arm own ci ci rfl hlogging
      have hobserve := finishFollower_diagnostics prepared.coordinator.downView
        (prepared.followers.followers i) own ci (memory i) (hfamily i).1
      dsimp only at hobserve
      have halign := prepared.follower_alignment i
      simp only [halign.1, halign.2.1, halign.2.2.1, halign.2.2.2] at hobserve
      have haccept : OrdinaryMessageCodec.acceptDown
          (ReferencePrelaunchFollower.codecParams p rate.eta)
          (ReferencePrelaunchFollower.acceptedStart ci) (xc.time.val + 1) (r.payload.downRecord i) := by
        have ht := hchoice.time.assignment_started
        rw [hpayload] at ht
        have hsigma : (r.payload.downRecord i).val.sigma = r.payload.sigma.val + 1 := by
          exact congrArg OrdinaryMessageCodec.DownFields.sigma (r.payload.downRecord_fields i)
        unfold OrdinaryMessageCodec.acceptDown
        simp only [ReferencePrelaunchFollower.acceptedStart, ci, hnone, hsigma]
        exact ⟨Nat.zero_lt_succ _, ht⟩
      have hview : prepared.coordinator.downView = some selected.view := by
        unfold ReferenceActivePhysicalStep.DispatchCut.downView
        rw [hselected]
        rfl
      have hb : ReferenceDownReception.selectedDownSenderBranch selected.view i xc.row xc.time :=
        ⟨by rw [hcurrent]; exact hs, by rw [hcurrent]; exact hi, by rw [hpending]; exact Finset.mem_univ i⟩
      have hexpected : ReferenceDownReception.expectedDownFlatWord prepared.coordinator.downView i xc.row xc.time =
          some wD := by
        rw [hview]
        simpa only [hpayload] using selected.expected_down_word i hb
      have hcall := ReferenceActiveAffinePositiveTest.referenceDownCut_has_call
        prepared.coordinator.downView i xc.row xc.time own ci
      have hgate : ReferenceActiveAffinePositiveTest.downReceiverGate i xc.row xc.time ci :=
        ⟨⟨by rw [hcurrent]; exact hs, by rw [hcurrent]; exact hi⟩, rfl, hregisters, hdecoder, hbuf⟩
      rw [decide_eq_true hgate] at hcall
      have hcomp : (ReferenceDownReception.referenceDownCut p prepared.coordinator.downView
          i xc.row xc.time own rate ci).rawComparison ≠ none := by
        intro hn
        rw [hn] at hcall
        cases hcall
      refine ⟨hnone, haccept, ⟨hregisters, hdecoder, hbuf⟩, hlogging, hrecord.1, hrecord.2,
        hobserve.1.trans hrecord.1, hobserve.2.trans hrecord.2, ?_, hcall, ?_, ?_⟩
      · rw [ReferenceDownReceptionMeasurability.referenceDownCut_expectedWord_eq]
        exact hexpected
      · exact ReferenceDownReception.referenceDownCut_raw_eq_currentDecodeStep_of_compared
          prepared.coordinator.downView i xc.row xc.time own rate ci hcomp
      · intro hz
        apply AffineBatchDecoder.decodeStep_ineligible
        · exact hdecoder.1
        · intro he
          have hpos := (ActiveFollowerDownAcceptance.currentRoundInput_eligible_iff
            p i xc.row xc.time own rate ci).mp he
          rw [hz] at hpos
          exact (lt_irrefl 0) hpos.2.2

end Bandits.Support.ReferenceFirstCutoffDownFreshGeometry

end
