/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstReplacementCollectionCommonStopObservation
public import Bandits.Support.ReferenceCompleteCoordinatorDiagnosticSupport

/-!
# Whole-control follower geometry in the first replacement collection

Sources: `sources/zip4/manuscript/05_binary_transport.tex:70-125,180-240`,
`sources/zip4/manuscript/06_interruptions.tex:110-190,246-349,425-431,459-487`,
and `sources/zip4/manuscript/appendix_a_local_protocol.tex:92-157`.

The actual cutoff reset and collection prefix supply the full ordinary local
states. Replacing the current whole control preserves their start-round inputs.
Each offered word is fixed before that replacement; it can be a placeholder,
an older reply, or a current reply. This is an internal preparation result.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ReferenceFirstReplacementCollectionFreshFollowerGeometry

open ConstructorDimensions ReferenceActivePhysicalStep PublicDiscreteDraws

variable {p : ConstructorDimensions.Parameters}

private theorem offer_admissible
    {rate : RateInput p} (state : ReferencePrelaunchFollower.State p rate.eta)
    (hdomain : ActiveFollowerLifecycle.localStateDomainValid state)
    (hzero : state.lastDown = none → state.S = 0 ∧ state.delta = 0 ∧ state.backlog = 0) :
    OrdinaryMessageCodec.upAdmissible (ReferencePrelaunchFollower.codecParams p rate.eta)
      (ActiveFollowerQueueOperation.upOfferFields state) := by
  cases hlast : state.lastDown with
  | none =>
    obtain ⟨hS, hd, hb⟩ := hzero hlast
    simp [OrdinaryMessageCodec.upAdmissible, ActiveFollowerQueueOperation.upOfferFields,
      ReferencePrelaunchFollower.acceptedStart, hlast, hS, hd, hb,
      OrdinaryMessageCodec.upPlaceholder]
  | some M =>
    simp only [OrdinaryMessageCodec.upAdmissible, ActiveFollowerQueueOperation.upOfferFields,
      ReferencePrelaunchFollower.acceptedStart, hlast]
    exact Or.inr ⟨M.property.1, M.property.2.1,
      hdomain.1.1, hdomain.1.2.1, hdomain.1.2.2⟩

/-- A successful start-round call with an ordinary unoccupied result produces
all three actual arm branches, retaining that result's entire configuration. -/
private theorem prepare_geometry
    (rate : RateInput p) (x : RoundInput p rate) (i : Fin (p.m - 1))
    (old choice : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hinput : x.state.followers i = .ordinary old memory)
    (hstart : ActiveFollowerLifecycle.startRound rate.eta x.time old memory =
      .ok (choice, memory))
    (hstatus : choice.status = .unoccupied)
    (hdomain : ActiveFollowerLifecycle.localStateDomainValid choice)
    (U : OrdinaryMessageCodec.UpRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (hU : U.val = ActiveFollowerQueueOperation.upOfferFields choice) :
    let h := x.row.2 x.time
    let prep := prepare x
    (prep.followers.followers i).configuration = .ordinary choice memory ∧
    (slotDraw h.1 = upSlot ∧ selectedFollowerDraw p.two_le_m p.m_lt_K h.1 = i →
      ActiveFollowerQueueOperation.checkedUpOffer rate.eta i x.row
        (x.state.activations i) x.time choice = .offer U ∧
      (prep.followers.followers i).arm = ActiveRoundActions.sendArm
        (ActiveFollowerArmChoice.offeredUpBit rate.eta h i U)
        ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K h.1).val
          (followerPlayer p.two_le_m i))
        ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K h.1).val
          (ActiveRoundActions.coordinator p.two_le_m))) ∧
    (slotDraw h.1 = dataSlot → (prep.followers.followers i).arm =
      pilotDraw (K_pos p) (followerPlayer p.two_le_m i) h.1) ∧
    (slotDraw h.1 ≠ dataSlot ∧
        ¬ (slotDraw h.1 = upSlot ∧ selectedFollowerDraw p.two_le_m p.m_lt_K h.1 = i) →
      (prep.followers.followers i).arm =
        (OrderedTupleSampler.sample p.two_le_m p.m_lt_K h.1).val
          (followerPlayer p.two_le_m i)) := by
  classical
  dsimp only
  have hqueue : ActiveFollowerQueueOperation.stateInputDomain choice :=
    ⟨hdomain.1.1, hdomain.1.2.1, hdomain.1.2.2, hdomain.2.1.1, hdomain.2.1.2.1⟩
  have hadm : OrdinaryMessageCodec.upAdmissible
      (ReferencePrelaunchFollower.codecParams p rate.eta)
      (ActiveFollowerQueueOperation.upOfferFields choice) := hU ▸ U.property
  have hprep : (prepare x).followers.followers i =
      DeclaredFollowerLocalRound.prepare rate i x.row (x.state.activations i)
        x.time (x.active i) (.ordinary old memory) := by
    change DeclaredFollowerLocalRound.prepare rate i x.row (x.state.activations i)
      x.time (x.active i) (x.state.followers i) = _
    rw [hinput]
  have hne : upSlot ≠ dataSlot := by decide
  by_cases hs : slotDraw (x.row.2 x.time).1 = upSlot ∧
      selectedFollowerDraw p.two_le_m p.m_lt_K (x.row.2 x.time).1 = i
  · have hselected : ActiveFollowerQueueOperation.selectedUpRound i x.row
        (x.state.activations i) x.time := ⟨x.active i, hs⟩
    have hoff : ActiveFollowerQueueOperation.checkedUpOffer rate.eta i x.row
        (x.state.activations i) x.time choice = .offer U := by
      unfold ActiveFollowerQueueOperation.checkedUpOffer
      rw [dite_eq_left hqueue, dite_eq_left ⟨hselected, hstatus⟩, dite_eq_left hadm]
      have hrecord : (⟨ActiveFollowerQueueOperation.upOfferFields choice, hadm⟩ :
          OrdinaryMessageCodec.UpRecord (ReferencePrelaunchFollower.codecParams p rate.eta)) =
          U := Subtype.ext hU.symm
      exact congrArg ActiveFollowerQueueOperation.UpOfferResult.offer hrecord
    have hvalid : ActiveFollowerArmChoice.upStateDomain choice ∧
        ActiveFollowerArmChoice.offeredUpMatchesState choice U := by
      refine ⟨⟨hdomain.1.1, hdomain.1.2.1, hdomain.1.2.2⟩, ?_⟩
      simp [ActiveFollowerArmChoice.offeredUpMatchesState, hU,
        ActiveFollowerQueueOperation.upOfferFields]
    have hcore := ActiveFollowerArmChoice.followerArmChoiceCore_unoccupied_selected_up
      choice (x.row.2 x.time) i U hstatus hs.1 hs.2 hvalid
    have hchoice := hcore
    rw [← ActiveFollowerArmChoice.followerArmChoice_eq_core choice x.row x.time i (some U)]
      at hchoice
    have hp := (DeclaredFollowerLocalRound.prepare_offer_arm_equation rate i x.row
      (x.state.activations i) x.time (x.active i) old choice memory memory hstart U hoff).2
      _ hchoice
    rw [hprep]
    refine ⟨hp.2, fun _ => ⟨hoff, hp.1⟩, ?_, ?_⟩
    · intro hd
      exact False.elim (hne (hs.1.symm.trans hd))
    · intro ho
      exact False.elim (ho.2 hs)
  · have hnot : ¬ (ActiveFollowerQueueOperation.selectedUpRound i x.row
        (x.state.activations i) x.time ∧ choice.status = .unoccupied) :=
      fun h => hs h.1.2
    have hoff := ActiveFollowerQueueOperation.checkedUpOffer_noOffer rate.eta i x.row
      (x.state.activations i) x.time choice hqueue hnot
    by_cases hd : slotDraw (x.row.2 x.time).1 = dataSlot
    · have hcore := ActiveFollowerArmChoice.followerArmChoiceCore_unoccupied_data
        choice (x.row.2 x.time) i none hstatus hd
      have hchoice := hcore
      rw [← ActiveFollowerArmChoice.followerArmChoice_eq_core choice x.row x.time i none]
        at hchoice
      have hp := (DeclaredFollowerLocalRound.prepare_no_offer_arm_equation rate i x.row
        (x.state.activations i) x.time (x.active i) old choice memory memory hstart hoff).2
        _ hchoice
      rw [hprep]
      exact ⟨hp.2, fun h => False.elim (hs h), fun _ => hp.1,
        fun h => False.elim (h.1 hd)⟩
    · have hcore := ActiveFollowerArmChoice.followerArmChoiceCore_unoccupied_other
        choice (x.row.2 x.time) i none hstatus hd hs
      have hchoice := hcore
      rw [← ActiveFollowerArmChoice.followerArmChoice_eq_core choice x.row x.time i none]
        at hchoice
      have hp := (DeclaredFollowerLocalRound.prepare_no_offer_arm_equation rate i x.row
        (x.state.activations i) x.time (x.active i) old choice memory memory hstart hoff).2
        _ hchoice
      rw [hprep]
      exact ⟨hp.2, fun h => False.elim (hs h), fun h => False.elim (hd h), fun _ => hp.1⟩

/-- The word depends only on the actual choice registers. Start-round reads no
current control, so the same full choice and memory work under every replacement. -/
private theorem record_control_geometry
    (rate : RateInput p) (r : ReferenceCompletePhysicalHistory.RoundRecord p rate)
    (i : Fin (p.m - 1)) (old choice : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hinput : r.input.state.followers i = .ordinary old memory)
    (hstart : ActiveFollowerLifecycle.startRound rate.eta r.input.time old memory =
      .ok (choice, memory))
    (hstatus : choice.status = .unoccupied)
    (hdomain : ActiveFollowerLifecycle.localStateDomainValid choice)
    (hadm : OrdinaryMessageCodec.upAdmissible
      (ReferencePrelaunchFollower.codecParams p rate.eta)
      (ActiveFollowerQueueOperation.upOfferFields choice)) :
    ∃ U : OrdinaryMessageCodec.UpRecord (ReferencePrelaunchFollower.codecParams p rate.eta),
      (ReferenceFollowerFixedReply.actualChoice r i).configuration = .ordinary choice memory ∧
      U.val = ActiveFollowerQueueOperation.upOfferFields choice ∧
      ∀ h : ContinuousLearningRows.TimeControl p,
        let xh := ReferenceLaterOptionalControlResampling.withControl r.input h
        let prep := prepare xh
        (prep.followers.followers i).configuration = .ordinary choice memory ∧
        (slotDraw h.1 = upSlot ∧ selectedFollowerDraw p.two_le_m p.m_lt_K h.1 = i →
          ActiveFollowerQueueOperation.checkedUpOffer rate.eta i xh.row
            (xh.state.activations i) xh.time choice = .offer U ∧
          (prep.followers.followers i).arm = ActiveRoundActions.sendArm
            (ActiveFollowerArmChoice.offeredUpBit rate.eta h i U)
            ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K h.1).val
              (followerPlayer p.two_le_m i))
            ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K h.1).val
              (ActiveRoundActions.coordinator p.two_le_m))) ∧
        (slotDraw h.1 = dataSlot → (prep.followers.followers i).arm =
          pilotDraw (K_pos p) (followerPlayer p.two_le_m i) h.1) ∧
        (slotDraw h.1 ≠ dataSlot ∧
            ¬ (slotDraw h.1 = upSlot ∧ selectedFollowerDraw p.two_le_m p.m_lt_K h.1 = i) →
          (prep.followers.followers i).arm =
            (OrderedTupleSampler.sample p.two_le_m p.m_lt_K h.1).val
              (followerPlayer p.two_le_m i)) := by
  let U : OrdinaryMessageCodec.UpRecord (ReferencePrelaunchFollower.codecParams p rate.eta) :=
    ⟨ActiveFollowerQueueOperation.upOfferFields choice, hadm⟩
  refine ⟨U, ?_, rfl, ?_⟩
  · have hp := (prepare_geometry rate r.input i old choice memory hinput hstart
      hstatus hdomain U rfl).1
    change (r.output.preparation.followers.followers i).configuration = _
    rw [r.output_eq]
    exact hp
  · intro h
    have hp := prepare_geometry rate
      (ReferenceLaterOptionalControlResampling.withControl r.input h)
      i old choice memory hinput hstart hstatus hdomain U rfl
    simpa only [ReferenceLaterOptionalControlResampling.withControl_time,
      ReferenceLaterOptionalControlResampling.withControl_currentControl] using hp

/-- In every present row of the actual first replacement collection, including
its cutoff row, all followers prepare ordinarily for every current whole
control, with one fixed admissible offer and the literal source arm equations. -/
theorem complete_first_replacement_collection_follower_control_geometry
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let _s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
    let _J := ActualInitializationPhysicalStep.selectedRowIndex p z
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
    let v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
    let tail := ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v
    let c := v + 1 + tail.length
    match R[v]? with
    | none => True
    | some birth =>
      match birth.output.preparation.coordinator with
      | .collection _ _ _ _ (.laterChosen _ _ _ _ _ _ _ _ _ installed _) =>
        let P := installed.registers.payload
        match R[c]? with
        | none => True
        | some cut =>
          match cut.output.preparation.coordinator with
          | .live _ _ _ (.cutoffChosen _ _ _ _ _ _ _ _ _ _) =>
            let _u := cut.input.time.val + 1
            let W := (R.drop (c + 1)).takeWhile
              (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
            let K := cut :: W
            let M := fun i => P.downRecord i
            ∀ a : Fin K.length, ∀ j : Fin (p.m - 1),
              let r := K.get a
              ∃ choice : ReferencePrelaunchFollower.State p rate.eta,
                ∃ memory : ActiveFollowerLifecycle.LocalMemory p,
                ∃ U : OrdinaryMessageCodec.UpRecord
                    (ReferencePrelaunchFollower.codecParams p rate.eta),
                  (ReferenceFollowerFixedReply.actualChoice r j).configuration =
                    .ordinary choice memory ∧
                  choice.status = .unoccupied ∧
                  ActiveFollowerLifecycle.localStateDomainValid choice ∧
                  (choice.lastDown = none →
                    choice.S = 0 ∧ choice.delta = 0 ∧ choice.backlog = 0) ∧
                  (ReferencePrelaunchFollower.acceptedStart choice < (M j).val.sigma ∨
                    choice.lastDown = some (M j)) ∧
                  U.val = ActiveFollowerQueueOperation.upOfferFields choice ∧
                  ∀ h : ContinuousLearningRows.TimeControl p,
                    let xh := ReferenceLaterOptionalControlResampling.withControl r.input h
                    let prep := prepare xh
                    (prep.followers.followers j).configuration = .ordinary choice memory ∧
                    (slotDraw h.1 = upSlot ∧
                        selectedFollowerDraw p.two_le_m p.m_lt_K h.1 = j →
                      ActiveFollowerQueueOperation.checkedUpOffer rate.eta j xh.row
                        (xh.state.activations j) xh.time choice = .offer U ∧
                      (prep.followers.followers j).arm = ActiveRoundActions.sendArm
                        (ActiveFollowerArmChoice.offeredUpBit rate.eta h j U)
                        ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K h.1).val
                          (followerPlayer p.two_le_m j))
                        ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K h.1).val
                          (ActiveRoundActions.coordinator p.two_le_m))) ∧
                    (slotDraw h.1 = dataSlot → (prep.followers.followers j).arm =
                      pilotDraw (K_pos p) (followerPlayer p.two_le_m j) h.1) ∧
                    (slotDraw h.1 ≠ dataSlot ∧
                        ¬ (slotDraw h.1 = upSlot ∧
                          selectedFollowerDraw p.two_le_m p.m_lt_K h.1 = j) →
                      (prep.followers.followers j).arm =
                        (OrderedTupleSampler.sample p.two_le_m p.m_lt_K h.1).val
                          (followerPlayer p.two_le_m j))
          | _ => True
      | _ => True := by
  classical
  have hF := ReferenceFirstReplacementCollectionPrefix.complete_first_replacement_collection_follower_prefix
    rate z rewards C_star C_h
  have hB := ReferenceFirstReplacementCutoffPreparedBoundary.complete_first_replacement_cutoff_follower_boundary
    rate z rewards C_star C_h
  dsimp only at hF hB ⊢
  set R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  set w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
  set v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
  set tail := ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v
  set c := v + 1 + tail.length
  cases hb : R[v]? with
  | none => trivial
  | some birth =>
    simp only [hb] at hF hB ⊢
    cases hbirth : birth.output.preparation.coordinator with
    | first _ => trivial
    | live _ _ _ _ => trivial
    | dagger => trivial
    | invalidCollectionCutoff => trivial
    | collection _ _ _ _ outcome =>
      simp only [hbirth] at hF hB ⊢
      cases outcome <;> try trivial
      rename_i core consistent started hstart instruction hinstruction output hconsistent
        clockData installed selectedBirth
      dsimp only [ReferenceActivePhysicalStep.collectionInput] at hF hB ⊢
      let P := installed.registers.payload
      cases hc : R[c]? with
      | none => trivial
      | some cut =>
        simp only [tail, c, hc] at hF hB ⊢
        rcases hB with ⟨_, hB⟩
        cases hcut : cut.output.preparation.coordinator with
        | first _ => trivial
        | collection _ _ _ _ _ => trivial
        | dagger => trivial
        | invalidCollectionCutoff => trivial
        | live registers owned base outcome =>
          simp only [hcut] at hF hB ⊢
          cases outcome <;> try trivial
          rename_i dispatched hs ledger hi hledger hdata hclock hpending hnone selectedCut
          dsimp only at hF hB ⊢
          let W := (R.drop (c + 1)).takeWhile
            (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
          rcases hF with ⟨_, _, _, _, _, _, hfollowers⟩
          rcases hB with ⟨_, _, _, _, _, _, _, _, _, _, _,
            selectedB, _, _, _, _, hboundary⟩
          intro ⟨a, ha⟩ j
          cases a with
          | zero =>
            rcases hboundary j with
              ⟨old, memory, hinput, _, _, hzero, hold, hoccupied, _, hstart,
                _, hdomain, _, _, _, hadm, _⟩
            let choice : ReferencePrelaunchFollower.State p rate.eta :=
              { old with status := .unoccupied }
            have horigin : ReferencePrelaunchFollower.acceptedStart choice <
                  (P.downRecord j).val.sigma ∨ choice.lastDown = some (P.downRecord j) := by
              by_cases hu : old.status = .unoccupied
              · exact Or.inl (hold hu)
              · exact Or.inr (hoccupied hu).1
            obtain ⟨U, hactual, hU, hall⟩ := record_control_geometry rate cut j old choice
              memory hinput hstart rfl hdomain hadm
            exact ⟨choice, memory, U, hactual, rfl, hdomain, hzero, horigin, hU, hall⟩
          | succ a =>
            have haW : a < W.length := Nat.lt_of_succ_lt_succ ha
            rcases hfollowers j with
              ⟨_, _, old, initial, memory, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hsteps, _⟩
            rcases hsteps a haW with
              ⟨_, state, logged, post, hinput, hstatus, hdomain, _, _, _, hzero,
                horigin, _, _, hstart, _⟩
            have hadm := offer_admissible state hdomain hzero
            obtain ⟨U, hactual, hU, hall⟩ := record_control_geometry rate
              (W.get ⟨a, haW⟩) j state state memory hinput hstart hstatus hdomain hadm
            exact ⟨state, memory, U, hactual, hstatus, hdomain, hzero, horigin, hU, hall⟩

end Bandits.Support.ReferenceFirstReplacementCollectionFreshFollowerGeometry
