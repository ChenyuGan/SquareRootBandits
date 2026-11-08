/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceOriginalKthCollectionSourceSections

/-!
# Original kth collection awaited service

This module joins the actual original-source prechoice and checked follower
START to the arbitrary-k OLD/FORMED service coefficient. The same whole-control
section and original-source conditional expectation retain the literal masks.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support
open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceSourcePrefixHistoryFiltration
open scoped Classical

namespace Bandits.Support.ReferenceOriginalKthCollectionAwaitedService

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceOriginalKthCollectionSourceSections.RateInput
abbrev SourceInput (p : Parameters) :=
  ReferenceOriginalKthCollectionSourceSections.SourceInput p
abbrev GridRewardTable (p : Parameters) :=
  ReferenceOriginalKthCollectionSourceSections.GridRewardTable p

variable {p : Parameters}
variable (rate : RateInput p) (rewards : GridRewardTable p)
  (C_star C_h : ℝ)

private theorem actualRecord_of_prechoiceData
    (t : Fin p.T) (z : SourceInput p)
    (data : ReferenceOriginalKthCollectionSourceSections.KthCPrechoiceData rate)
    (hdata : ReferenceOriginalKthCollectionSourceSections.kthCPrechoiceData
      rate rewards C_star C_h t z = some data) :
    ∃ r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate),
      ReferenceSourcePrefixHistoryFiltration.actualRecord
        rate rewards C_star C_h t z = some r := by
  unfold ReferenceOriginalKthCollectionSourceSections.kthCPrechoiceData at hdata
  simp only [ReferenceSourcePrefixHistoryFiltration.incoming] at hdata
  cases hrecord : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t z with
  | none => simp [hrecord] at hdata
  | some r => exact ⟨r, rfl⟩

/-- On a present actual record, the prechoice stage is the checked START stage
of that same record and the very same incoming payload. -/
theorem kthCPrechoiceStage_eq_actual_choiceStage
    (t : Fin p.T) (i : Fin (p.m - 1)) (z : SourceInput p)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t z = some r)
    (data : ReferenceOriginalKthCollectionSourceSections.KthCPrechoiceData rate)
    (hdata : ReferenceOriginalKthCollectionSourceSections.kthCPrechoiceData
      rate rewards C_star C_h t z = some data) :
    ReferenceOriginalKthCollectionSourceSections.kthCPrechoiceStage
        rate rewards C_star C_h t i z =
      some (data.2.1,
        ReferenceFirstReplacementCollectionPredictableStages.choiceStage
          r data.1 i) := by
  unfold ReferenceOriginalKthCollectionSourceSections.kthCPrechoiceStage
  rw [hdata]
  simp only [Option.map_some]
  congr 1
  simpa [ReferenceOriginalKthCollectionSourceSections.kthFollowerIndex,
    ActiveRoundActions.Follower, PublicDiscreteDraws.followerCount] using
    (ReferenceFirstReplacementCollectionPredictableStages.preRoundStart_choiceStage
      rate rewards C_star C_h t i z r data.1 hr)

/-- OLD-mask membership exposes the actual same-record OLD START branch.
Older accepted DOWN words remain OLD because the comparison is with this
prechoice payload's word. -/
theorem kthCOLDSet_actual_choiceStage
    (k : Fin (p.T + 1)) (t : Fin p.T) (i : Fin (p.m - 1)) (z : SourceInput p)
    (hz : z ∈ ReferenceOriginalKthCollectionSourceSections.kthCOLDSet
      rate rewards C_star C_h k t i) :
    ∃ r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate),
      ∃ data : ReferenceOriginalKthCollectionSourceSections.KthCPrechoiceData rate,
        ReferenceOriginalKthCollectionSourceSections.kthCStratum
          rate rewards C_star C_h k t z ∧
        ReferenceSourcePrefixHistoryFiltration.actualRecord
          rate rewards C_star C_h t z = some r ∧
        ReferenceOriginalKthCollectionSourceSections.kthCPrechoiceData
          rate rewards C_star C_h t z = some data ∧
        i ∈ data.2.1 ∧
    ReferenceFirstReplacementCollectionPredictableStages.choiceStage
          r data.1 i = .old := by
  rcases hz with ⟨hstratum, pending, hip, hstage⟩
  have hmap := hstage
  unfold ReferenceOriginalKthCollectionSourceSections.kthCPrechoiceStage at hmap
  obtain ⟨data, hdata, _⟩ := Option.map_eq_some_iff.mp hmap
  obtain ⟨r, hr⟩ := actualRecord_of_prechoiceData rate rewards C_star C_h t z data hdata
  have hactual := kthCPrechoiceStage_eq_actual_choiceStage
    rate rewards C_star C_h t i z r hr data hdata
  have heq := Prod.mk.inj (Option.some.inj (hactual.symm.trans hstage))
  refine ⟨r, data, hstratum, hr, hdata, ?_, heq.2⟩
  rw [heq.1]
  exact hip

/-- FORMED-mask membership exposes the actual same-record accepted-word START
branch. Its state fields are retained for the service proof, rather than
replaced by an assumed UP offer. -/
theorem kthCFORMEDSet_actual_choiceStage
    (k : Fin (p.T + 1)) (t : Fin p.T) (i : Fin (p.m - 1)) (z : SourceInput p)
    (hz : z ∈ ReferenceOriginalKthCollectionSourceSections.kthCFORMEDSet
      rate rewards C_star C_h k t i) :
    ∃ r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate),
      ∃ data : ReferenceOriginalKthCollectionSourceSections.KthCPrechoiceData rate,
      ReferenceSourcePrefixHistoryFiltration.actualRecord
        rate rewards C_star C_h t z = some r ∧
      ReferenceOriginalKthCollectionSourceSections.kthCPrechoiceData
        rate rewards C_star C_h t z = some data ∧
      i ∈ data.2.1 ∧
      ReferenceFirstReplacementCollectionPredictableStages.choiceStage
        r data.1 i = .formed := by
  rcases hz with ⟨_hstratum, pending, hip, hstage⟩
  have hmap := hstage
  unfold ReferenceOriginalKthCollectionSourceSections.kthCPrechoiceStage at hmap
  obtain ⟨data, hdata, _⟩ := Option.map_eq_some_iff.mp hmap
  obtain ⟨r, hr⟩ := actualRecord_of_prechoiceData rate rewards C_star C_h t z data hdata
  have hactual := kthCPrechoiceStage_eq_actual_choiceStage
    rate rewards C_star C_h t i z r hr data hdata
  have heq := Prod.mk.inj (Option.some.inj (hactual.symm.trans hstage))
  refine ⟨r, data, hr, hdata, ?_, heq.2⟩
  rw [heq.1]
  exact hip

/-- OLD membership exposes the actual unoccupied follower configuration and
the fact that its remembered DOWN word differs from this payload's word. -/
theorem kthCOLDSet_actual_followerStart
    (k : Fin (p.T + 1)) (t : Fin p.T) (i : Fin (p.m - 1)) (z : SourceInput p)
    (hz : z ∈ ReferenceOriginalKthCollectionSourceSections.kthCOLDSet
      rate rewards C_star C_h k t i) :
    ∃ r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate),
      ∃ data : ReferenceOriginalKthCollectionSourceSections.KthCPrechoiceData rate,
      ∃ state : ReferencePrelaunchFollower.State p rate.eta,
      ∃ memory : ActiveFollowerLifecycle.LocalMemory p,
      ReferenceSourcePrefixHistoryFiltration.actualRecord
        rate rewards C_star C_h t z = some r ∧
      ReferenceOriginalKthCollectionSourceSections.kthCPrechoiceData
        rate rewards C_star C_h t z = some data ∧
      i ∈ data.2.1 ∧
      (ReferenceFollowerFixedReply.actualChoice r i).configuration =
        .ordinary state memory ∧
      state.status = .unoccupied ∧
      state.lastDown ≠ some (data.1.downRecord
        (ReferenceOriginalKthCollectionSourceSections.kthFollowerIndex (p := p) i)) := by
  obtain ⟨r, data, _hstratum, hr, hdata, hip, hchoice⟩ :=
    kthCOLDSet_actual_choiceStage rate rewards C_star C_h k t i z hz
  have hold :=
    ReferenceFirstReplacementCollectionPredictableStages.choiceStage_old_iff
      r data.1 i |>.mp hchoice
  rcases hold with ⟨state, memory, hconfig, hstatus, hlast⟩
  exact ⟨r, data, state, memory, hr, hdata, hip, hconfig, hstatus, hlast⟩

/-- FORMED membership exposes the actual ordinary unoccupied follower start
and equality of its remembered DOWN word with this exact incoming payload. -/
theorem kthCFORMEDSet_actual_followerStart
    (k : Fin (p.T + 1)) (t : Fin p.T) (i : Fin (p.m - 1)) (z : SourceInput p)
    (hz : z ∈ ReferenceOriginalKthCollectionSourceSections.kthCFORMEDSet
      rate rewards C_star C_h k t i) :
    ∃ r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate),
      ∃ data : ReferenceOriginalKthCollectionSourceSections.KthCPrechoiceData rate,
      ∃ state : ReferencePrelaunchFollower.State p rate.eta,
      ∃ memory : ActiveFollowerLifecycle.LocalMemory p,
      ReferenceSourcePrefixHistoryFiltration.actualRecord
        rate rewards C_star C_h t z = some r ∧
      ReferenceOriginalKthCollectionSourceSections.kthCPrechoiceData
        rate rewards C_star C_h t z = some data ∧
      i ∈ data.2.1 ∧
      (ReferenceFollowerFixedReply.actualChoice r i).configuration =
        .ordinary state memory ∧
      state.status = .unoccupied ∧
      state.lastDown = some (data.1.downRecord
        (ReferenceOriginalKthCollectionSourceSections.kthFollowerIndex (p := p) i)) := by
  obtain ⟨r, data, hr, hdata, hip, hchoice⟩ :=
    kthCFORMEDSet_actual_choiceStage rate rewards C_star C_h k t i z hz
  have hformed :=
    ReferenceFirstReplacementCollectionPredictableStages.choiceStage_formed_iff
      r data.1 i |>.mp hchoice
  rcases hformed with ⟨state, memory, hconfig, hstatus, hlast⟩
  exact ⟨r, data, state, memory, hr, hdata, hip, hconfig, hstatus, hlast⟩

/-- The two literal kth-C masks cannot hold at once. -/
theorem kthCOLDSet_disjoint_kthCFORMEDSet
    (k : Fin (p.T + 1)) (t : Fin p.T) (i : Fin (p.m - 1)) :
    Disjoint
      (ReferenceOriginalKthCollectionSourceSections.kthCOLDSet
        rate rewards C_star C_h k t i)
      (ReferenceOriginalKthCollectionSourceSections.kthCFORMEDSet
        rate rewards C_star C_h k t i) := by
  apply Set.disjoint_left.mpr
  rintro z ⟨_, pendingOld, _, hOld⟩ ⟨_, pendingFormed, _, hFormed⟩
  have heq := Option.some.inj (hOld.symm.trans hFormed)
  have hstage := congrArg Prod.snd heq
  cases hstage

/-- The fresh whole-control section is zero away from both literal pending
masks, including the no-record, absent-C, and off-stratum cases. -/
theorem kthCSourceFreshSection_eq_zero_of_not_mem
    (control0 : ContinuousLearningRows.TimeControl p) (k : Fin (p.T + 1))
    (t : Fin p.T) (i : Fin (p.m - 1)) (z : SourceInput p)
    (hOld : z ∉ ReferenceOriginalKthCollectionSourceSections.kthCOLDSet
      rate rewards C_star C_h k t i)
    (hFormed : z ∉ ReferenceOriginalKthCollectionSourceSections.kthCFORMEDSet
      rate rewards C_star C_h k t i) :
    ReferenceOriginalKthCollectionSourceSections.kthCSourceFreshSection
      rate rewards C_star C_h k t i control0 z = 0 := by
  simp [ReferenceOriginalKthCollectionSourceSections.kthCSourceFreshSection,
    hOld, hFormed]

/-- On every original-source input, the fresh section is exactly the OLD/FORMED
masked sum, with the absent, nonpending, and off-stratum cases equal to zero. -/
theorem kthCSourceFreshSection_eq_masked_cases
    (control0 : ContinuousLearningRows.TimeControl p) (k : Fin (p.T + 1))
    (t : Fin p.T) (i : Fin (p.m - 1)) (z : SourceInput p) :
    ReferenceOriginalKthCollectionSourceSections.kthCSourceFreshSection
        rate rewards C_star C_h k t i control0 z =
      if z ∈ ReferenceOriginalKthCollectionSourceSections.kthCOLDSet
          rate rewards C_star C_h k t i then
        ReferenceFirstCollectionDownConditionalService.actualFirstCollectionDownFreshSection
          (rate := rate) rewards C_star C_h control0 i t z
      else if z ∈ ReferenceOriginalKthCollectionSourceSections.kthCFORMEDSet
          rate rewards C_star C_h k t i then
        ReferenceFirstCollectionUpConditionalService.actualFirstCollectionUpFreshSection
          (rate := rate) rewards C_star C_h control0 i t z
      else 0 := by
  have hdisjoint := Set.disjoint_left.mp
    (kthCOLDSet_disjoint_kthCFORMEDSet rate rewards C_star C_h k t i)
  by_cases hOld : z ∈ ReferenceOriginalKthCollectionSourceSections.kthCOLDSet
      rate rewards C_star C_h k t i
  · have hFormed : z ∉ ReferenceOriginalKthCollectionSourceSections.kthCFORMEDSet
        rate rewards C_star C_h k t i := hdisjoint hOld
    simp [ReferenceOriginalKthCollectionSourceSections.kthCSourceFreshSection, hOld, hFormed]
  · by_cases hFormed : z ∈ ReferenceOriginalKthCollectionSourceSections.kthCFORMEDSet
        rate rewards C_star C_h k t i
    all_goals simp [ReferenceOriginalKthCollectionSourceSections.kthCSourceFreshSection, hOld, hFormed]

/-- The accepted source conditional-expectation consequence, with its exact
whole-source law and pre-round field. The fresh section is still the literal
masked section defined by the source module. -/
theorem kthCSourceReadout_condExp
    (control0 : ContinuousLearningRows.TimeControl p) (k : Fin (p.T + 1))
    (t : Fin p.T) (i : Fin (p.m - 1)) :
    (BootstrapPrivateRoundStreams.sourceInputLaw p)[
      ReferenceOriginalKthCollectionSourceSections.kthCSourceReadout
        rate rewards C_star C_h k t i |
        sourcePrefixFiltration control0 (t.val + 1)] =ᵐ[
          BootstrapPrivateRoundStreams.sourceInputLaw p]
      ReferenceOriginalKthCollectionSourceSections.kthCSourceFreshSection
        rate rewards C_star C_h k t i control0 :=
  ReferenceOriginalKthCollectionSourceSections.kthCSourceReadout_condExp
    rate rewards C_star C_h control0 k t i

/-! The following local proofs retain the actual original suffix index. -/

private theorem actualRecord_suffixIndex
    (t : Fin p.T) (z : SourceInput p)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t z = some r) :
    ∃ a : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h).length,
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[a.val] = r := by
  unfold ReferenceSourcePrefixHistoryFiltration.actualRecord at hr
  split at hr
  · obtain ⟨ha, he⟩ := List.getElem?_eq_some_iff.mp hr
    exact ⟨⟨_, ha⟩, he⟩
  · cases hr

private theorem actual_choice_domains
    (t : Fin p.T) (z : SourceInput p)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t z = some r)
    (i : Fin (p.m - 1))
    (choice : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hchoice : (ReferenceFollowerFixedReply.actualChoice r i).configuration =
      .ordinary choice memory) :
    ∃ old : ReferencePrelaunchFollower.State p rate.eta,
      r.input.state.followers i = .ordinary old memory ∧
      ActiveFollowerLifecycle.startRound rate.eta r.input.time old memory =
        .ok (choice, memory) ∧
      ActiveFollowerLifecycle.localStateDomainValid choice ∧
      OrdinaryMessageCodec.upAdmissible
        (ReferencePrelaunchFollower.codecParams p rate.eta)
        (ActiveFollowerQueueOperation.upOfferFields choice) := by
  obtain ⟨a, ha⟩ := actualRecord_suffixIndex rate rewards C_star C_h t z r hr
  obtain ⟨old, oldMemory, actual, hinput, _, hstart, hactual, hdomain, _⟩ :=
    ReferenceCompleteSuffixFollowerPreservation.complete_suffix_follower_choice
      (rate := rate) rewards C_star C_h z a i
  rw [ha] at hinput hstart hactual
  have heq := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
    (hactual.symm.trans hchoice)
  rcases heq with ⟨heqState, heqMemory⟩
  subst actual
  subst oldMemory
  refine ⟨old, hinput, hstart, hdomain, ?_⟩
  cases hlast : choice.lastDown with
  | some M =>
      simp only [OrdinaryMessageCodec.upAdmissible,
        ActiveFollowerQueueOperation.upOfferFields,
        ReferencePrelaunchFollower.acceptedStart, hlast]
      exact Or.inr ⟨M.property.1, M.property.2.1,
        hdomain.1.1, hdomain.1.2.1, hdomain.1.2.2⟩
  | none =>
      have hframe := ActiveFollowerLifecycle.startRound_frame rate.eta
        r.input.time old choice memory memory hstart
      have hnone : old.lastDown = none := hframe.1.symm.trans hlast
      have hinputAt : (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h)[a.val].input.state.followers i =
          .ordinary old memory := by rw [ha]; exact hinput
      have hzero := ReferenceAssignmentFollowerMassSteps.complete_no_down_input
        rate rewards C_star C_h z a i old memory hinputAt hnone
      have hS : choice.S = 0 := hframe.2.1.trans hzero.1
      have hd : choice.delta = 0 := hframe.2.2.1.trans hzero.2.1
      have hb : choice.backlog = 0 := hframe.2.2.2.1.trans hzero.2.2.1
      simp [OrdinaryMessageCodec.upAdmissible,
        ActiveFollowerQueueOperation.upOfferFields,
        ReferencePrelaunchFollower.acceptedStart, hlast, hS, hd, hb,
        OrdinaryMessageCodec.upPlaceholder]

open ReferenceActivePhysicalStep PublicDiscreteDraws

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

/-- FORMED fixes the actual current reply, its positive accepted start and
current payload sigma before any fresh control is sampled. The same checked
START produces the sender and all its tuple-arm branches for every complete
control; no future decode or successful current observation is assumed. -/
theorem kthCFORMEDSet_actual_currentReply_control_geometry
    (k : Fin (p.T + 1)) (t : Fin p.T) (i : Fin (p.m - 1)) (z : SourceInput p)
    (hz : z ∈ ReferenceOriginalKthCollectionSourceSections.kthCFORMEDSet
      rate rewards C_star C_h k t i) :
    ∃ r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate),
      ∃ data : ReferenceOriginalKthCollectionSourceSections.KthCPrechoiceData rate,
      ∃ old choice : ReferencePrelaunchFollower.State p rate.eta,
      ∃ memory : ActiveFollowerLifecycle.LocalMemory p,
      ∃ U : OrdinaryMessageCodec.UpRecord (ReferencePrelaunchFollower.codecParams p rate.eta),
      ReferenceSourcePrefixHistoryFiltration.actualRecord
        rate rewards C_star C_h t z = some r ∧
      ReferenceOriginalKthCollectionSourceSections.kthCPrechoiceData
        rate rewards C_star C_h t z = some data ∧
      i ∈ data.2.1 ∧
      r.input.state.followers i = .ordinary old memory ∧
      ActiveFollowerLifecycle.startRound rate.eta r.input.time old memory =
        .ok (choice, memory) ∧
      (ReferenceFollowerFixedReply.actualChoice r i).configuration =
        .ordinary choice memory ∧
      choice.status = .unoccupied ∧
      choice.lastDown = some (data.1.downRecord i) ∧
      U.val = ActiveFollowerQueueOperation.upOfferFields choice ∧
      U.val.sigma = (data.1.downRecord i).val.sigma ∧ 0 < U.val.sigma ∧
      ∀ c : ContinuousLearningRows.TimeControl p,
        let x := ReferenceLaterOptionalControlResampling.withControl r.input c
        ((prepare x).followers.followers i).configuration = .ordinary choice memory ∧
        (slotDraw c.1 = upSlot ∧ selectedFollowerDraw p.two_le_m p.m_lt_K c.1 = i →
          ActiveFollowerQueueOperation.checkedUpOffer rate.eta i x.row
            (x.state.activations i) x.time choice = .offer U ∧
          ((prepare x).followers.followers i).arm = ActiveRoundActions.sendArm
            (ActiveFollowerArmChoice.offeredUpBit rate.eta c i U)
            ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K c.1).val
              (followerPlayer p.two_le_m i))
            ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K c.1).val
              (ActiveRoundActions.coordinator p.two_le_m))) ∧
        (slotDraw c.1 = dataSlot → ((prepare x).followers.followers i).arm =
          pilotDraw (K_pos p) (followerPlayer p.two_le_m i) c.1) ∧
        (slotDraw c.1 ≠ dataSlot ∧
            ¬ (slotDraw c.1 = upSlot ∧
              selectedFollowerDraw p.two_le_m p.m_lt_K c.1 = i) →
          ((prepare x).followers.followers i).arm =
            (OrderedTupleSampler.sample p.two_le_m p.m_lt_K c.1).val
              (followerPlayer p.two_le_m i)) := by
  obtain ⟨r, data, choice, memory, hr, hdata, hip, hchoice, hstatus, hlast⟩ :=
    kthCFORMEDSet_actual_followerStart rate rewards C_star C_h k t i z hz
  obtain ⟨old, hinput, hstart, hdomain, hadmissible⟩ :=
    actual_choice_domains rate rewards C_star C_h t z r hr i choice memory hchoice
  let U : OrdinaryMessageCodec.UpRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta) :=
    ⟨ActiveFollowerQueueOperation.upOfferFields choice, hadmissible⟩
  have hsigma : U.val.sigma = (data.1.downRecord i).val.sigma := by
    change ReferencePrelaunchFollower.acceptedStart choice = _
    simp only [ReferencePrelaunchFollower.acceptedStart,
      ReferenceOriginalKthCollectionSourceSections.kthFollowerIndex] at hlast ⊢
    rw [hlast]
    rfl
  have hpositive : 0 < U.val.sigma := by
    rw [hsigma, data.1.downRecord_fields i]
    exact Nat.succ_pos _
  refine ⟨r, data, old, choice, memory, U, hr, hdata, hip, hinput,
    hstart, hchoice, hstatus, hlast, rfl, hsigma, hpositive, ?_⟩
  intro c
  have hgeometry := prepare_geometry rate
    (ReferenceLaterOptionalControlResampling.withControl r.input c)
    i old choice memory hinput hstart hstatus hdomain U rfl
  simpa only [ReferenceLaterOptionalControlResampling.withControl_time,
    ReferenceLaterOptionalControlResampling.withControl_currentControl] using hgeometry

/-- Every present literal C prechoice is an actual collection choice on the
same record. The payload and pending set are inherited, including at a live
cutoff; this does not restart the physical run or initialize a new payload. -/
theorem kthCPrechoiceData_actual_collectionChoice
    (t : Fin p.T) (z : SourceInput p)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t z = some r)
    (data : ReferenceOriginalKthCollectionSourceSections.KthCPrechoiceData rate)
    (hdata : ReferenceOriginalKthCollectionSourceSections.kthCPrechoiceData
      rate rewards C_star C_h t z = some data) :
    ∃ c : ReferenceCollectionSegmentExtraction.Choice rate,
      ReferenceCollectionSegmentExtraction.choice r.input = some c ∧
      data.1 = c.payload ∧ data.2.1 = c.preLedger.pending ∧
      data.2.2.1 = c.preLedger.cutoff := by
  have hread := hdata
  rw [ReferenceOriginalKthCollectionSourceSections.kthCPrechoiceData_actualRecord
    rate rewards C_star C_h t z r hr] at hread
  cases hstate : r.input.state.coordinator with
  | first =>
      simp [ReferenceOriginalKthCollectionSourceSections.kthCPrechoiceDataFromCoordinatorCode,
        ReferenceActivePhysicalStepMeasurability.encodeCoordinator, hstate] at hread
  | dagger =>
      simp [ReferenceOriginalKthCollectionSourceSections.kthCPrechoiceDataFromCoordinatorCode,
        ReferenceActivePhysicalStepMeasurability.encodeCoordinator, hstate] at hread
  | live registers owned base =>
      cases hchoice : ReferenceCollectionSegmentExtraction.choice r.input with
      | none =>
          have hnone := ReferenceOriginalKthCollectionSourceSections.kthCPrechoiceData_liveNoCollectionChoice
            rate rewards C_star C_h t z r hr registers owned base hstate hchoice
          rw [hnone] at hdata
          cases hdata
      | some c =>
          obtain ⟨data', hdata', hpay, hpend, hcut, _⟩ :=
            ReferenceOriginalKthCollectionSourceSections.kthCPrechoiceData_actualLiveCollectionChoice
              rate rewards C_star C_h t z r hr registers owned base hstate c hchoice
          have heq : data' = data := Option.some.inj (hdata'.symm.trans hdata)
          subst data'
          exact ⟨c, rfl, hpay, hpend, hcut⟩
  | collection payload ledger saved =>
      by_cases hpending : ledger.pending.Nonempty
      · obtain ⟨c, hc, _, _, _, _, data', hdata', hpay, hpend, hcut⟩ :=
          ReferenceOriginalKthCollectionSourceSections.kthCPrechoiceData_actualCollectionChoice_nonempty
            rate rewards C_star C_h t z r hr payload ledger saved hstate hpending
        have heq : data' = data := Option.some.inj (hdata'.symm.trans hdata)
        subst data'
        exact ⟨c, hc, hpay, hpend, hcut⟩
      · simp [ReferenceOriginalKthCollectionSourceSections.kthCPrechoiceDataFromCoordinatorCode,
          ReferenceActivePhysicalStepMeasurability.encodeCoordinator, hstate, hpending] at hread

private theorem collectionChoice_selection
    (x : RoundInput p rate) (c : ReferenceCollectionSegmentExtraction.Choice rate)
    (hc : ReferenceCollectionSegmentExtraction.choice x = some c) :
    ∃ v : Selection x,
      (prepare x).coordinator.selection = some v ∧
      v.view.payload = c.payload ∧ v.view.pendingAtChoice = c.preLedger.pending := by
  unfold ReferenceCollectionSegmentExtraction.choice at hc
  split at hc
  · cases hc
  next hn =>
    obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp hn
    refine ⟨v, hv, ?_⟩
    cases hd : (prepare x).coordinator with
    | first outcome => cases outcome <;>
        simp [hd, ReferenceCollectionSegmentExtraction.choiceOfCut] at hc
    | dagger => simp [hd, ReferenceCollectionSegmentExtraction.choiceOfCut] at hc
    | invalidCollectionCutoff =>
        simp [hd, ReferenceCollectionSegmentExtraction.choiceOfCut] at hc
    | live registers owned base outcome =>
        cases outcome <;> simp only [hd, ReferenceCollectionSegmentExtraction.choiceOfCut] at hc
        all_goals try contradiction
        next dispatched hs ledger hi he hdomain hclock hpending hnone selected =>
          cases Option.some.inj hc
          simp only [hd, DispatchCut.selection, selectionAt] at hv
          cases Option.some.inj hv
          refine ⟨rfl, ?_⟩
          change dispatched.startResult.pending = (sharedLedger ledger).pending
          rw [he, hpending]
          rfl
    | collection payload ledger clock cutoff outcome =>
        cases outcome <;> simp only [hd, ReferenceCollectionSegmentExtraction.choiceOfCut] at hc
        all_goals try contradiction
        next core snapshot boundary scores =>
          cases Option.some.inj hc
          simp only [hd, DispatchCut.selection] at hv
          cases Option.some.inj hv
          exact ⟨rfl, snapshot.clockStarted_frame.2.1⟩

private theorem actual_index_clock
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length) :
    ReferenceCoordinatorClockDomains.clockAt
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val]'k.isLt).input.rows
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val]'k.isLt).input.selected
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val]'k.isLt).input.time.val
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val]'k.isLt).input.state := by
  obtain ⟨hc, hspan, hrecord⟩ := ReferenceLaterLiveNumericalReadout.source_record_prefix
    rate rewards C_star C_h source k
  let initial := ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hc
  let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed rate source rewards C_star C_h hc
  let start := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
  have hseed : ReferenceCoordinatorClockDomains.clockAt source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) start initial := by
    simp [ReferenceCoordinatorClockDomains.clockAt, initial, seed.coordinatorFirst]
  let execution := ReferenceActivePhysicalHorizon.run initial source.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
    start (k.val + 1) hspan seed.activeAtStart
  have hget := ReferenceLocalReleaseGateChronology.run_record_at initial source.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start seed.activeAtStart
    (k.val + 1) hspan ⟨k.val, by omega⟩
  have hmem : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).get k ∈ execution.records := by
    rw [hrecord, ← hget]
    exact List.getElem_mem _
  have hclock := ReferenceRunClockPreservation.run_clockAt initial source.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
    start (k.val + 1) hspan seed.activeAtStart hseed
  have hat := hclock.2.2.2 _ hmem
  dsimp only [List.get_eq_getElem] at hat
  rw [hat.2.2.1, hat.2.2.2.1]
  exact hat.1

private theorem actualRecord_fields (t : Fin p.T) (z : SourceInput p)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : actualRecord rate rewards C_star C_h t z = some r) :
    r.input.rows = z.1.2 ∧
      r.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p z ∧
      r.input.time = t ∧ r.input.rewards = rewards := by
  by_cases hz : ReferenceSourcePrefixHistoryFiltration.actualLaunchBy rate rewards C_star C_h t.val z
  · have hl := ReferenceLocalReleaseGateChronology.sourceSeed_launch rate z rewards C_star C_h hz.1
    have hrec := ReferenceSourcePrefixHistoryFiltration.actualRecord_on_launch rate rewards C_star C_h t z _ hl hz.2
    have heq := Option.some.inj (hr.symm.trans hrec)
    subst r
    refine ⟨rfl, rfl, ?_, rfl⟩
    apply Fin.ext
    dsimp only [ReferenceAssignmentPayloadChronology.actualRunRecordAt,
      ReferenceActivePhysicalHorizon.roundInputAt]
    have hs := hz.2
    omega
  · rw [ReferenceSourcePrefixHistoryFiltration.actualRecord_eq_none_of_not_launchBy rate rewards C_star C_h t z hz] at hr
    cases hr

private theorem startRound_initializeAt_detectCutoff
    (eta : ℝ) (time : Fin p.T) (clock : CoordinatorPhaseClock.ClockRegisters p)
    (pending : Finset (Fin (p.m - 1))) (result : CoordinatorPhaseClock.StartRoundResult p)
    (hparam : CoordinatorPhaseClock.proposalParameterValid p eta)
    (hclock : CoordinatorPhaseClock.clockRegistersValid p eta clock)
    (htime : CoordinatorPhaseClock.startRoundTimeValid p time clock)
    (hstart : CoordinatorPhaseClock.startRound p eta time clock pending = .ok result)
    (hcommand : result.ledgerCommand = some (.initializeAt time)) :
    ∃ sigma : Fin p.T, ∃ hsigma : clock.sigma = some sigma,
      CoordinatorPhaseClock.detectCutoff clock time = .ok (.cutoff sigma hsigma) := by
  classical
  cases hdetect : CoordinatorPhaseClock.detectCutoff clock time with
  | error failure =>
      simp [CoordinatorPhaseClock.startRound, hparam, hclock, htime, hdetect] at hstart
  | ok decision =>
      cases decision with
      | cutoff sigma hsigma => exact ⟨sigma, hsigma, rfl⟩
      | noCutoff =>
          by_cases hsource : CoordinatorPhaseClock.sourceStartTest
              clock.sigma clock.u time pending
          · by_cases hgrid : CoordinatorPhaseClock.newGridBoundaryValid p time
                (FollowerCutoffScan.gridBoundary p eta time)
            · simp only [CoordinatorPhaseClock.startRound, hparam, hclock, htime,
                hdetect, hsource, hgrid] at hstart
              have hcmd := congrArg CoordinatorPhaseClock.StartRoundResult.ledgerCommand
                (Except.ok.inj hstart)
              simp [hcommand] at hcmd
            · simp [CoordinatorPhaseClock.startRound, hparam, hclock, htime,
                hdetect, hsource, hgrid] at hstart
          · simp only [CoordinatorPhaseClock.startRound, hparam, hclock, htime,
              hdetect, hsource] at hstart
            have hcmd := congrArg CoordinatorPhaseClock.StartRoundResult.ledgerCommand
              (Except.ok.inj hstart)
            simp [hcommand] at hcmd

private theorem live_initialize_cutoff_bound
    (t : Fin p.T) (z : SourceInput p)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t z = some r)
    (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
    (base : Fin (p.m - 1) → ℕ)
    (hstate : r.input.state.coordinator = .live registers owned base)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (hstart : CoordinatorPhaseClock.startRound p rate.eta.val r.input.time
      registers.priorClock registers.clockPending = .ok started)
    (hcommand : started.ledgerCommand = some (.initializeAt r.input.time)) :
    FollowerCutoffScan.firstCutoff p rate.eta.val registers.payload.sigma
      (FollowerCutoffScan.completeRowProposalBit p rate.eta.val r.input.row) ≤
      r.input.time.val + 1 := by
  obtain ⟨a, ha⟩ := actualRecord_suffixIndex rate rewards C_star C_h t z r hr
  have hclock := actual_index_clock rate rewards C_star C_h z a
  rw [ha] at hclock
  simp only [ReferenceCoordinatorClockDomains.clockAt, hstate] at hclock
  rcases hclock with ⟨hstamp, hvalid, hsigma, hu, hgrid, hbefore, _, hproposal⟩
  have htime : CoordinatorPhaseClock.startRoundTimeValid p r.input.time
      registers.priorClock := by
    simp [CoordinatorPhaseClock.startRoundTimeValid, hsigma, hu,
      FollowerCutoffScan.calendarRound]
    omega
  obtain ⟨sigma, hsigma', hdetect⟩ := startRound_initializeAt_detectCutoff
    rate.eta.val r.input.time registers.priorClock registers.clockPending started
    (ReferenceCoordinatorClockDomains.proposalParameterValid_of_rate rate)
    hvalid htime hstart hcommand
  have heq : sigma = registers.payload.sigma :=
    Option.some.inj (hsigma'.symm.trans hsigma)
  subst sigma
  have hboundary : registers.priorClock.g =
      FollowerCutoffScan.gridBoundary p rate.eta.val registers.payload.sigma := by
    simpa [CoordinatorPhaseClock.clockRegistersValid,
      CoordinatorPhaseClock.boundaryFromSigma, hsigma] using hvalid.1
  by_cases hgridNow : FollowerCutoffScan.calendarRound r.input.time = registers.priorClock.g
  · have hbound := (FollowerCutoffScan.firstCutoff_bounds p rate.eta.val
      rate.eta.property rate.sourceCap registers.payload.sigma
      (FollowerCutoffScan.completeRowProposalBit p rate.eta.val r.input.row)).2
    rw [← hboundary, ← hgridNow] at hbound
    exact hbound
  · have hread := CoordinatorPhaseClock.savedPriorProposal_correct
      registers.priorClock r.input.time registers.time
      (FollowerCutoffScan.completeRowProposalBit p rate.eta.val r.input.row registers.time)
      hproposal hstamp
    have hbit : FollowerCutoffScan.completeRowProposalBit p rate.eta.val
        r.input.row registers.time = true := by
      by_contra hn
      have hf := Bool.eq_false_iff.mpr hn
      simp only [CoordinatorPhaseClock.detectCutoff, hgridNow, ite_false, hread,
        hf, Bind.bind, Except.bind, Bool.false_eq_true] at hdetect
      split at hdetect <;> cases hdetect
    have hmem : registers.time ∈ FollowerCutoffScan.proposalCoordinates p
        registers.payload.sigma := by
      simp only [FollowerCutoffScan.proposalCoordinates, Finset.mem_filter,
        Finset.mem_univ, true_and]
      have ht := r.input.time.isLt
      exact ⟨by omega, by omega⟩
    have hendpoint : FollowerCutoffScan.proposalEndpoint registers.time ∈
        FollowerCutoffScan.firstCutoffCarrier p rate.eta.val registers.payload.sigma
          (FollowerCutoffScan.completeRowProposalBit p rate.eta.val r.input.row) := by
      apply Finset.mem_insert_of_mem
      apply Finset.mem_image.mpr
      exact ⟨registers.time, Finset.mem_filter.mpr ⟨hmem, hbit⟩, rfl⟩
    have hbound := Finset.min'_le
      (FollowerCutoffScan.firstCutoffCarrier p rate.eta.val registers.payload.sigma
        (FollowerCutoffScan.completeRowProposalBit p rate.eta.val r.input.row))
      (FollowerCutoffScan.proposalEndpoint registers.time) hendpoint
    change FollowerCutoffScan.firstCutoff p rate.eta.val registers.payload.sigma
      (FollowerCutoffScan.completeRowProposalBit p rate.eta.val r.input.row) ≤
      registers.time.val + 2 at hbound
    omega

private theorem live_input_of_prepare
    {rate : RateInput p} (x : RoundInput p rate)
    (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
    (base : Fin (p.m - 1) → ℕ)
    (outcome : CoordinatorRoundDispatch.LiveOutcome (liveInput x registers owned base))
    (hprepare : (prepare x).coordinator = .live registers owned base outcome) :
    x.state.coordinator = .live registers owned base := by
  cases hc : x.state.coordinator with
  | first =>
    simp only [prepare, dispatch, hc, CoordinatorRoundDispatch.dispatch] at hprepare
    contradiction
  | dagger =>
    simp only [prepare, dispatch, hc] at hprepare
    contradiction
  | collection P ledger saved =>
    simp only [prepare, dispatch, hc] at hprepare
    split at hprepare <;>
      (try simp only [CoordinatorRoundDispatch.dispatch] at hprepare) <;> contradiction
  | live registers' owned' base' =>
    have hp : (prepare x).coordinator = .live registers' owned' base'
        (CoordinatorRoundDispatch.dispatchLive (liveInput x registers' owned' base')) := by
      simp only [prepare, dispatch, hc, CoordinatorRoundDispatch.dispatch]
      rfl
    have he := hp.symm.trans hprepare
    cases he
    rfl

private theorem actual_collectionChoice_cutoff_bound
    (t : Fin p.T) (z : SourceInput p)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t z = some r)
    (c : ReferenceCollectionSegmentExtraction.Choice rate)
    (hc : ReferenceCollectionSegmentExtraction.choice r.input = some c) :
    FollowerCutoffScan.firstCutoff p rate.eta.val c.payload.sigma
      (FollowerCutoffScan.completeRowProposalBit p rate.eta.val r.input.row) ≤
      r.input.time.val + 1 := by
  obtain ⟨a, ha⟩ := actualRecord_suffixIndex rate rewards C_star C_h t z r hr
  have hout : r.output.preparation.coordinator = (prepare r.input).coordinator := by
    rw [r.output_eq]
    rfl
  unfold ReferenceCollectionSegmentExtraction.choice at hc
  split at hc
  · cases hc
  · cases hd : (prepare r.input).coordinator with
    | first outcome => cases outcome <;>
        simp [hd, ReferenceCollectionSegmentExtraction.choiceOfCut] at hc
    | dagger => simp [hd, ReferenceCollectionSegmentExtraction.choiceOfCut] at hc
    | invalidCollectionCutoff =>
        simp [hd, ReferenceCollectionSegmentExtraction.choiceOfCut] at hc
    | collection payload ledger clock cutoff outcome =>
        cases outcome <;> simp only [hd, ReferenceCollectionSegmentExtraction.choiceOfCut] at hc
        all_goals try contradiction
        next core snapshot boundary scores =>
          cases Option.some.inj hc
          have hbound := ReferenceCollectionCutoffSourceHistory.complete_continuing_collection_cutoff_source_bound
            rate z rewards C_star C_h a
          dsimp only [List.get_eq_getElem] at hbound
          rw [ha, hout, hd] at hbound
          exact hbound.1.trans (by omega)
    | live registers owned base outcome =>
        cases outcome <;> simp only [hd, ReferenceCollectionSegmentExtraction.choiceOfCut] at hc
        all_goals try contradiction
        next dispatched hs ledger hi he hdomain hclock hpending hnone selected =>
          cases Option.some.inj hc
          have hstate := live_input_of_prepare r.input registers owned base _ hd
          have hstateAt : (ReferenceCompletePhysicalHistory.completeSuffixRecords
              rate z rewards C_star C_h)[a.val].input.state.coordinator =
              .live registers owned base := by rw [ha]; exact hstate
          have hpost := complete_live_cutoff_post_choice
            rate rewards C_star C_h z a registers owned base hstateAt
          dsimp only at hpost
          rw [ha] at hpost
          have hdispatch : CoordinatorRoundDispatch.dispatchLive
              (liveInput r.input registers owned base) =
              .cutoffChosen dispatched hs ledger hi he hdomain hclock hpending hnone selected := by
            have heq := hpost.1.symm.trans hd
            injection heq
          rw [hdispatch] at hpost
          apply live_initialize_cutoff_bound rate rewards C_star C_h t z r hr
            registers owned base hstate dispatched.startResult
          · simpa only [liveInput, liveRegistersAt,
              CoordinatorLiveChoiceRecorderStep.Registers.clockPending_eq] using hs
          · exact hpost.2.1

private theorem selected_unoccupied
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (selected : ReferenceActivePhysicalStep.Selection
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val]'k.isLt).input)
    (hselection : ((ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[k.val]'k.isLt).output.preparation.coordinator.selection =
        some selected)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (hpayload : selected.view.payload = payload)
    (hcut : FollowerCutoffScan.firstCutoff p rate.eta.val payload.sigma
      (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
        ((ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h)[k.val]'k.isLt).input.row) ≤
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val]'k.isLt).input.time.val + 1) :
    ReferenceLaterCollectionArrivalReadout.preparedFollowersUnoccupied
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val]'k.isLt) := by
  classical
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate source rewards C_star C_h
  let record := R[k.val]'k.isLt
  obtain ⟨states, memories, hstates, hdown, _hinputFields, _houtputFields⟩ :=
    ReferenceCompletePayloadChoiceChronology.complete_selected_payload_choice_fields
      (rate := rate) rewards C_star C_h source k selected hselection
  intro i
  change match (ReferenceFollowerFixedReply.actualChoice record i).configuration with
    | .ordinary state _ => state.status = .unoccupied
    | .dagger => False
  rw [hstates i]
  by_contra hbusy
  have hcurrent := hdown i hbusy
  rw [hpayload] at hcurrent
  obtain ⟨before, memory, choice, hbefore, _hdomain, hstart, hchoice,
      _hchoiceDomain, _hoperationDomain⟩ :=
    ReferenceCompleteSuffixFollowerPreservation.complete_suffix_follower_choice
      (rate := rate) rewards C_star C_h source k i
  have hchoiceEq := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
    (hchoice.symm.trans (hstates i))
  have hchoiceDown : choice.lastDown = some (payload.downRecord i) := by
    rw [hchoiceEq.1]
    exact hcurrent
  have hbeforeDown : before.lastDown = some (payload.downRecord i) :=
    (ActiveFollowerLifecycle.startRound_frame rate.eta record.input.time before
      choice memory memory hstart).1.symm.trans hchoiceDown
  have hphase := ReferenceCompleteFollowerCutoffPhase.complete_ordinary_follower_phase
    rate rewards C_star C_h source k i before memory hbefore
      (payload.downRecord i) hbeforeDown
  have htoken : before.status ≠ .unoccupied → ∃ stamp : Fin p.T,
      stamp.val + 1 = record.input.time.val ∧
        memory.lastProposalRead = some ⟨stamp,
          FollowerCutoffScan.completeRowProposalBit p rate.eta.val record.input.row stamp⟩ := by
    intro hoccupied
    exact ReferenceCompleteFollowerCutoffPhase.complete_ordinary_follower_token
      rate rewards C_star C_h source k i before memory hbefore hoccupied
  have hstatus := ReferenceAssignmentFollowerMassSteps.start_round_cutoff_status
    (rate := rate) record.input.time record.input.row before choice memory memory
      (payload.downRecord i) hbeforeDown hphase htoken hstart
  have hstartPayload : ActiveFollowerDownAcceptance.downStart p rate
      (payload.downRecord i) = payload.sigma := by
    apply Fin.ext
    have hval := ActiveFollowerDownAcceptance.downStart_val_add_one p rate
      (payload.downRecord i)
    rw [payload.downRecord_fields i] at hval
    exact Nat.add_right_cancel hval
  have hchoiceUnoccupied : choice.status = .unoccupied :=
    hstatus.mpr (by rw [hstartPayload]; exact hcut)
  exact hbusy (hchoiceEq.1 ▸ hchoiceUnoccupied)

/-- Actual pending prechoice data has an ordinary unoccupied checked START
for every follower. This includes the live cutoff round itself and continuing
collection, with the complete original payload and retained state. -/
theorem kthCPrechoiceData_actual_unoccupied
    (t : Fin p.T) (z : SourceInput p)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t z = some r)
    (data : ReferenceOriginalKthCollectionSourceSections.KthCPrechoiceData rate)
    (hdata : ReferenceOriginalKthCollectionSourceSections.kthCPrechoiceData
      rate rewards C_star C_h t z = some data) :
    ∀ i : Fin (p.m - 1), ∃ state memory,
      (ReferenceFollowerFixedReply.actualChoice r i).configuration = .ordinary state memory ∧
      state.status = .unoccupied := by
  obtain ⟨a, ha⟩ := actualRecord_suffixIndex rate rewards C_star C_h t z r hr
  subst r
  let r := (ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate z rewards C_star C_h)[a.val]
  obtain ⟨c, hc, _, _, _⟩ := kthCPrechoiceData_actual_collectionChoice
    rate rewards C_star C_h t z r hr data hdata
  obtain ⟨v, hv, hpay, _⟩ := collectionChoice_selection rate r.input c hc
  have hselected : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[a.val].output.preparation.coordinator.selection = some v := by
    change r.output.preparation.coordinator.selection = some v
    rw [r.output_eq]
    exact hv
  have hbound := actual_collectionChoice_cutoff_bound rate rewards C_star C_h t z r hr c hc
  have hboundAt : FollowerCutoffScan.firstCutoff p rate.eta.val c.payload.sigma
      (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
        (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h)[a.val].input.row) ≤
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[a.val].input.time.val + 1 := by
    exact hbound
  have hunoccupied := selected_unoccupied rate rewards C_star C_h z a v
    hselected c.payload hpay hboundAt
  intro i
  obtain ⟨state, memory, choice, _, _, _, hchoice, _, _⟩ :=
    ReferenceCompleteSuffixFollowerPreservation.complete_suffix_follower_choice
      (rate := rate) rewards C_star C_h z a i
  have hstatus := hunoccupied i
  change match (ReferenceFollowerFixedReply.actualChoice
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[a.val] i).configuration with
    | .ordinary state _ => state.status = .unoccupied
    | .dagger => False at hstatus
  rw [hchoice] at hstatus
  exact ⟨choice, memory, hchoice, hstatus⟩

/-- The literal OLD and FORMED masks exhaust the actual pending kth-C
stratum. No ordinary-state or current-reply premise is added to this root. -/
theorem kthC_pending_mem_OLD_or_FORMED
    (k : Fin (p.T + 1)) (t : Fin p.T) (i : Fin (p.m - 1)) (z : SourceInput p)
    (hstratum : ReferenceOriginalKthCollectionSourceSections.kthCStratum
      rate rewards C_star C_h k t z)
    (data : ReferenceOriginalKthCollectionSourceSections.KthCPrechoiceData rate)
    (hdata : ReferenceOriginalKthCollectionSourceSections.kthCPrechoiceData
      rate rewards C_star C_h t z = some data)
    (hip : i ∈ data.2.1) :
    z ∈ ReferenceOriginalKthCollectionSourceSections.kthCOLDSet
      rate rewards C_star C_h k t i ∨
    z ∈ ReferenceOriginalKthCollectionSourceSections.kthCFORMEDSet
      rate rewards C_star C_h k t i := by
  obtain ⟨r, hr⟩ := actualRecord_of_prechoiceData rate rewards C_star C_h t z data hdata
  have hordinary := kthCPrechoiceData_actual_unoccupied
    rate rewards C_star C_h t z r hr data hdata i
  have hstages := (ReferenceFirstReplacementCollectionPredictableStages.choiceStage_old_or_formed
    r data.1 i).mpr hordinary
  have hstage := kthCPrechoiceStage_eq_actual_choiceStage
    rate rewards C_star C_h t i z r hr data hdata
  rcases hstages with hold | hformed
  · left
    exact ⟨hstratum, data.2.1, hip, by rw [hstage, hold]⟩
  · right
    exact ⟨hstratum, data.2.1, hip, by rw [hstage, hformed]⟩

private theorem down_event
    {rate : RateInput p} (r : ReferenceCompletePhysicalHistory.RoundRecord p rate)
    (P : Payload rate) (i : Fin (p.m - 1)) (v : Selection r.input)
    (hselected : r.output.preparation.coordinator.selection = some v)
    (hpayload : v.view.payload = P) (hpending : i ∈ v.view.pendingAtChoice)
    (choice : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hconfiguration : ((prepare r.input).followers.followers i).configuration =
      .ordinary choice memory)
    (hstatus : choice.status = .unoccupied)
    (hdomain : ActiveFollowerLifecycle.localStateDomainValid choice)
    (hfollowers : slotDraw (r.input.row.2 r.input.time).1 = downSlot →
      ∀ j : Fin (p.m - 1), (prepare r.input).arms.actions (followerPlayer p.two_le_m j) =
        (OrderedTupleSampler.sample p.two_le_m p.m_lt_K (r.input.row.2 r.input.time).1).val
          (followerPlayer p.two_le_m j)) :
    (selectedFollowerDraw p.two_le_m p.m_lt_K (r.input.row.2 r.input.time).1 = i ∧
      ReferenceActiveAffinePositiveTest.downPositive r.input = true) ↔
    (slotDraw (r.input.row.2 r.input.time).1 = downSlot ∧
      selectedFollowerDraw p.two_le_m p.m_lt_K (r.input.row.2 r.input.time).1 = i ∧
      AffineChannelLaw.affineHash ((r.input.row.2 r.input.time).2 (0, i))
        (CoordinatorLocalArmChoice.storedDownFlatWord P i) = 1 ∧
      0 < r.input.rewards r.input.time
        ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K (r.input.row.2 r.input.time).1).val
          (followerPlayer p.two_le_m i))) := by
  have atDown (hdown : ActiveFollowerDownAcceptance.downSelected p i r.input.row r.input.time) :
      (selectedFollowerDraw p.two_le_m p.m_lt_K (r.input.row.2 r.input.time).1 = i ∧
        ReferenceActiveAffinePositiveTest.downPositive r.input = true) ↔
      (slotDraw (r.input.row.2 r.input.time).1 = downSlot ∧
        selectedFollowerDraw p.two_le_m p.m_lt_K (r.input.row.2 r.input.time).1 = i ∧
        AffineChannelLaw.affineHash ((r.input.row.2 r.input.time).2 (0, i))
          (CoordinatorLocalArmChoice.storedDownFlatWord P i) = 1 ∧
        0 < r.input.rewards r.input.time
          ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K (r.input.row.2 r.input.time).1).val
            (followerPlayer p.two_le_m i))) := by
    have hsender := ReferenceFirstReplacementCollectionOldDownSenderReadiness.selected_sender
      r P i v hselected hpayload hdown hpending
    have hcoord := hsender.2.2.2.1
    rw [r.output_eq] at hcoord
    exact ReferenceFirstCutoffDownControlGeometry.old_down_event_iff_prepared_unoccupied
      r.input i choice memory (CoordinatorLocalArmChoice.storedDownFlatWord P i)
      ((ReferenceActiveAffinePositiveTest.upSenderIndex_eq_draw r.input).trans hdown.2)
      hconfiguration hstatus hdomain hcoord (hfollowers hdown.1)
  constructor
  · rintro ⟨hdraw, hpositive⟩
    have hindex := (ReferenceActiveAffinePositiveTest.upSenderIndex_eq_draw r.input).trans hdraw
    have hgate := ReferenceFirstCutoffDownControlGeometry.down_gate_eq_decide_downSelected_of_prepared_unoccupied
      r.input i choice memory hindex hconfiguration hstatus hdomain
    have hp := hpositive
    rw [ReferenceActiveAffinePositiveTest.downPositive_eq_gate_feedback] at hp
    have hdown : ActiveFollowerDownAcceptance.downSelected p i r.input.row r.input.time := by
      rw [hgate] at hp
      exact of_decide_eq_true (Bool.and_eq_true_iff.mp hp).1
    exact (atDown hdown).mp ⟨hdraw, hpositive⟩
  · intro h
    exact (atDown ⟨h.1, h.2.1⟩).mpr h

private theorem actual_prechoice_down_event
    (t : Fin p.T) (z : SourceInput p)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t z = some r)
    (data : ReferenceOriginalKthCollectionSourceSections.KthCPrechoiceData rate)
    (hdata : ReferenceOriginalKthCollectionSourceSections.kthCPrechoiceData
      rate rewards C_star C_h t z = some data)
    (i : Fin (p.m - 1)) (hip : i ∈ data.2.1) :
    (selectedFollowerDraw p.two_le_m p.m_lt_K (r.input.row.2 r.input.time).1 = i ∧
      ReferenceActiveAffinePositiveTest.downPositive r.input = true) ↔
    (slotDraw (r.input.row.2 r.input.time).1 = downSlot ∧
      selectedFollowerDraw p.two_le_m p.m_lt_K (r.input.row.2 r.input.time).1 = i ∧
      AffineChannelLaw.affineHash ((r.input.row.2 r.input.time).2 (0, i))
        (CoordinatorLocalArmChoice.storedDownFlatWord data.1 i) = 1 ∧
      0 < r.input.rewards r.input.time
        ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K
          (r.input.row.2 r.input.time).1).val (followerPlayer p.two_le_m i))) := by
  obtain ⟨c, hc, hpay, hpend, _⟩ := kthCPrechoiceData_actual_collectionChoice
    rate rewards C_star C_h t z r hr data hdata
  obtain ⟨v, hv, hvpay, hvpend⟩ := collectionChoice_selection rate r.input c hc
  have hselected : r.output.preparation.coordinator.selection = some v := by
    rw [r.output_eq]
    exact hv
  have hfollowers := kthCPrechoiceData_actual_unoccupied rate rewards C_star C_h t z r hr data hdata
  obtain ⟨choice, memory, hchoice, hstatus⟩ := hfollowers i
  obtain ⟨old, _, _, hdomain, _⟩ :=
    actual_choice_domains rate rewards C_star C_h t z r hr i choice memory hchoice
  apply down_event r data.1 i v hselected (hvpay.trans hpay.symm)
    (by rw [hvpend, ← hpend]; exact hip) choice memory
    (by
      have hconfig := hchoice
      change (r.output.preparation.followers.followers i).configuration = _ at hconfig
      rw [r.output_eq] at hconfig
      exact hconfig) hstatus hdomain
  intro hdown j
  obtain ⟨state, mem, hconfig, hstatusJ⟩ := hfollowers j
  obtain ⟨before, hinput, hstart, hvalid, hadm⟩ :=
    actual_choice_domains rate rewards C_star C_h t z r hr j state mem hconfig
  let U : OrdinaryMessageCodec.UpRecord (ReferencePrelaunchFollower.codecParams p rate.eta) :=
    ⟨ActiveFollowerQueueOperation.upOfferFields state, hadm⟩
  have hgeometry := prepare_geometry rate r.input j before state mem
    hinput hstart hstatusJ hvalid U rfl
  apply ((prepare r.input).arms.actions_follower j).trans
  apply hgeometry.2.2.2
  constructor
  · rw [hdown]
    decide
  · rintro ⟨hup, _⟩
    have hne : downSlot ≠ upSlot := by decide
    exact hne (hdown.symm.trans hup)

/-- On an actual OLD pending kth-C branch, every fresh COMPLETE control has
exactly the DOWN-slot/current-word/receiver-arm event. All other slow players'
tuple actions and collision exclusion are derived from the same physical run. -/
theorem kthCOLDSet_actual_down_control_geometry
    (control0 : ContinuousLearningRows.TimeControl p)
    (k : Fin (p.T + 1)) (t : Fin p.T) (i : Fin (p.m - 1)) (z : SourceInput p)
    (hz : z ∈ ReferenceOriginalKthCollectionSourceSections.kthCOLDSet
      rate rewards C_star C_h k t i) :
    ∃ r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate),
      ∃ data : ReferenceOriginalKthCollectionSourceSections.KthCPrechoiceData rate,
      ReferenceSourcePrefixHistoryFiltration.actualRecord
        rate rewards C_star C_h t z = some r ∧
      ReferenceOriginalKthCollectionSourceSections.kthCPrechoiceData
        rate rewards C_star C_h t z = some data ∧
      i ∈ data.2.1 ∧
      ∀ c : ContinuousLearningRows.TimeControl p,
        c ∈ ReferenceFirstCollectionDownConditionalService.freshCoordinatorDownServiceSet r.input i ↔
        c ∈ ReferenceFirstCollectionDownConditionalService.downServiceFormulaSet
          rewards t i (CoordinatorLocalArmChoice.storedDownFlatWord data.1 i) := by
  obtain ⟨r, data, _, hr, hdata, hip, _⟩ :=
    kthCOLDSet_actual_choiceStage rate rewards C_star C_h k t i z hz
  refine ⟨r, data, hr, hdata, hip, ?_⟩
  intro c
  obtain ⟨rh, hrh, hinput⟩ :=
    ReferenceFirstCollectionUpConditionalService.actualFirstCollectionUp_actualRecord_replace
      (rate := rate) rewards C_star C_h control0 t z r hr c
  have hdatah : ReferenceOriginalKthCollectionSourceSections.kthCPrechoiceData
      rate rewards C_star C_h t
      (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z c) = some data := by
    rw [ReferenceOriginalKthCollectionSourceSections.kthCPrechoiceData_actualRecord
      rate rewards C_star C_h t _ rh hrh, hinput]
    change ReferenceOriginalKthCollectionSourceSections.kthCPrechoiceDataFromCoordinatorCode
      rate t (ReferenceActivePhysicalStepMeasurability.encodeCoordinator
        r.input.state.coordinator) = some data
    rw [← ReferenceOriginalKthCollectionSourceSections.kthCPrechoiceData_actualRecord
      rate rewards C_star C_h t z r hr]
    exact hdata
  have hevent := actual_prechoice_down_event rate rewards C_star C_h t _ rh hrh data hdatah i hip
  have hfields := actualRecord_fields rate rewards C_star C_h t z r hr
  rw [hinput] at hevent
  have hcurrent : (ReferenceLaterOptionalControlResampling.withControl r.input c).row.2 t = c := by
    rw [← hfields.2.2.1]
    exact ReferenceLaterOptionalControlResampling.withControl_currentControl r.input c
  have hplayer : ReferenceFirstCollectionDownControlGeometry.followerPlayerAt i =
      followerPlayer p.two_le_m i := by
    apply Fin.ext
    rfl
  simpa only [ReferenceFirstCollectionDownConditionalService.freshCoordinatorDownServiceSet,
    ReferenceFirstCollectionDownConditionalService.downServiceFormulaSet, Set.mem_ofPred_eq,
    ReferenceLaterOptionalControlResampling.withControl_currentControl,
    ReferenceLaterOptionalControlResampling.withControl_time,
    ReferenceLaterOptionalControlResampling.withControl_rewards,
    hfields.2.2.1, hfields.2.2.2, hcurrent,
    hplayer] using hevent

/-- Arbitrary-k OLD service has the literal source coefficient, using the
all-date measure identity and formula probability rather than the
first-collection epoch coefficient. -/
theorem kthCOLDSet_downFreshSection_eq_coefficient
    (control0 : ContinuousLearningRows.TimeControl p)
    (k : Fin (p.T + 1)) (t : Fin p.T) (i : Fin (p.m - 1)) (z : SourceInput p)
    (hz : z ∈ ReferenceOriginalKthCollectionSourceSections.kthCOLDSet
      rate rewards C_star C_h k t i) :
    ReferenceFirstCollectionDownConditionalService.actualFirstCollectionDownFreshSection
        (rate := rate) rewards C_star C_h control0 i t z =
      (ReferenceFirstCollectionUpConditionalService.positiveRewardCount rewards t : ℝ) /
        (8 * (p.m - 1 : ℝ) * p.K) := by
  obtain ⟨r, data, hr, _, _, hgeometry⟩ := kthCOLDSet_actual_down_control_geometry
    rate rewards C_star C_h control0 k t i z hz
  have hset : ReferenceFirstCollectionDownConditionalService.freshCoordinatorDownServiceSet r.input i =
      ReferenceFirstCollectionDownConditionalService.downServiceFormulaSet rewards t i
        (CoordinatorLocalArmChoice.storedDownFlatWord data.1 i) := Set.ext hgeometry
  have hnonneg : 0 ≤ (ReferenceFirstCollectionUpConditionalService.positiveRewardCount rewards t : ℝ) /
      (8 * (p.m - 1 : ℝ) * p.K) := by
    have hm : (1 : ℝ) ≤ p.m := by exact_mod_cast (Nat.le_trans (by decide : 1 ≤ 2) p.two_le_m)
    exact div_nonneg (Nat.cast_nonneg _)
      (mul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hm)) (Nat.cast_nonneg _))
  rw [ReferenceFirstCollectionDownConditionalService.actualFirstCollectionDownFreshSection_eq_measure
    rewards C_star C_h control0 i t z r hr, hset, measureReal_def,
    ReferenceFirstCollectionDownConditionalService.downServiceFormulaSet_probability
      rewards t i (CoordinatorLocalArmChoice.storedDownFlatWord data.1 i),
    ENNReal.toReal_ofReal hnonneg]

private theorem actual_collection_up_site
    (t : Fin p.T) (z : SourceInput p)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t z = some r)
    (c : ReferenceCollectionSegmentExtraction.Choice rate)
    (hc : ReferenceCollectionSegmentExtraction.choice r.input = some c) :
    ∃ (o : CoordinatorRecordingOperation.Output p) (started : Ledger rate),
      CoordinatorRecorderComplementBridge.run
        (collectionRecordingInput (prepare r.input) c.payload c.started c.weights) = some o ∧
      CoordinatorCollectionLedger.startRound c.preLedger (r.input.time.val + 1)
        (collectionEnabled c.preLedger r.input.time)
        (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder o) = .success started ∧
      started.pending = c.preLedger.pending ∧
      CoordinatorUpReception.receptionInputCheck
        (ReferenceCoordinatorUpPhysicalCall.actualUpInput r.input started) = true ∧
      ReferenceActiveAffinePositiveTest.upPositive r.input =
        decide (AffineBatchDecoder.eligible (CoordinatorUpReception.roundInput
          (ReferenceCoordinatorUpPhysicalCall.actualUpInput r.input started))) := by
  obtain ⟨a, ha⟩ := actualRecord_suffixIndex rate rewards C_star C_h t z r hr
  have hfailure := (ReferenceCompleteCoordinatorPhaseExhaustion.complete_coordinator_phase_exhaustion
    rate rewards C_star C_h z).1 a |>.2.2.1
  rw [ha, r.output_eq] at hfailure
  change (prepare r.input).observeCoordinator.failure = none at hfailure
  have htail := ReferenceCollectionSegmentExtraction.choice_tail r.input c hc
  rw [htail] at hfailure
  unfold collectionPostChoice at hfailure
  cases hrec : CoordinatorRecorderComplementBridge.run
      (collectionRecordingInput (prepare r.input) c.payload c.started c.weights) with
  | none => simp only [hrec, coordinatorFailure, reduceCtorEq] at hfailure
  | some o =>
    simp only [hrec] at hfailure
    cases hs : CoordinatorCollectionLedger.startRound c.preLedger (r.input.time.val + 1)
        (collectionEnabled c.preLedger r.input.time)
        (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder o) with
    | invalid => simp only [hs, coordinatorFailure, reduceCtorEq] at hfailure
    | rejected bad => simp only [hs, coordinatorFailure, reduceCtorEq] at hfailure
    | success started =>
      simp only [hs] at hfailure
      have hnotInvalid : (receiveUp (prepare r.input) started).result ≠ .invalid := by
        intro hinvalid
        simp only [collectionFinish, hinvalid, coordinatorFailure, reduceCtorEq] at hfailure
      have hcheck := ReferenceCollectionSegmentExtraction.receiveUp_input_check r.input started hnotInvalid
      change CoordinatorUpReception.receptionInputCheck
        (ReferenceCoordinatorUpPhysicalCall.actualUpInput r.input started) = true at hcheck
      have hpend : started.pending = c.preLedger.pending := by
        unfold CoordinatorCollectionLedger.startRound at hs
        split at hs <;> try contradiction
        dsimp only at hs
        split at hs <;> try contradiction
        split at hs <;> try contradiction
        cases hs
        rfl
      refine ⟨o, started, rfl, hs, hpend, hcheck, ?_⟩
      unfold ReferenceActiveAffinePositiveTest.upPositive
      rw [htail, ReferenceActiveAffinePositiveTest.collectionPostChoice_positive_prefix, hrec]
      dsimp only
      rw [hs]
      change (CoordinatorUpReception.receptionInputCheck
        (ReferenceCoordinatorUpPhysicalCall.actualUpInput r.input started) && _) = _
      rw [hcheck, Bool.true_and]
      rfl

private theorem coordinator_observation_positive_iff
    {rate : RateInput p} (x : RoundInput p rate) (arm : Fin p.K)
    (ha : (prepare x).arms.actions (ActiveRoundActions.coordinator p.two_le_m) = arm) :
    (0 < CoordinatorUpReception.roundedObservationValue p (prepare x).coordinatorObservation) ↔
      FiniteBanditModel.collisionFreeFor (prepare x).arms.actions
        (ActiveRoundActions.coordinator p.two_le_m) ∧ 0 < x.rewards x.time arm := by
  classical
  have hD : (0 : ℝ) < (D p : ℝ) := by exact_mod_cast D_pos p
  have hpos : (0 < CoordinatorUpReception.roundedObservationValue p
      (prepare x).coordinatorObservation) ↔
      0 < ((prepare x).feedback.feedback (ActiveRoundActions.coordinator p.two_le_m)).val := by
    rw [CoordinatorUpReception.roundedObservationValue,
      PreparedRound.coordinatorObservation, div_pos_iff_of_pos_right hD]
    exact Nat.cast_pos
  rw [hpos, (prepare x).feedback_rule]
  by_cases hfree : FiniteBanditModel.collisionFreeFor (prepare x).arms.actions
      (ActiveRoundActions.coordinator p.two_le_m)
  · rw [ite_eq_left hfree, ha]
    simp only [hfree, true_and]
    rfl
  · rw [ite_eq_right hfree]
    simp only [Fin.val_zero, Nat.lt_irrefl, hfree, false_and]

/-- The arbitrary-k FORMED service coefficient uses the fixed actual
current reply and the actual started coordinator ledger, for each complete
fresh control, without conditioning on a later successful decode. -/
theorem kthCFORMEDSet_upFreshSection_eq_coefficient
    (control0 : ContinuousLearningRows.TimeControl p)
    (k : Fin (p.T + 1)) (t : Fin p.T) (i : Fin (p.m - 1)) (z : SourceInput p)
    (hz : z ∈ ReferenceOriginalKthCollectionSourceSections.kthCFORMEDSet
      rate rewards C_star C_h k t i) :
    ReferenceFirstCollectionUpConditionalService.actualFirstCollectionUpFreshSection
        (rate := rate) rewards C_star C_h control0 i t z =
      (ReferenceFirstCollectionUpConditionalService.positiveRewardCount rewards t : ℝ) /
        (8 * (p.m - 1 : ℝ) * p.K) := by
  obtain ⟨r, data, old, choice, memory, U, hr, hdata, hip, _, _, _, _, _, _, _, _, hcontrols⟩ :=
    kthCFORMEDSet_actual_currentReply_control_geometry rate rewards C_star C_h k t i z hz
  have hset : ReferenceFirstCollectionUpConditionalService.freshCoordinatorUpServiceSet r.input i =
      ReferenceFirstCollectionUpConditionalService.coordinatorUpServiceFormulaSet rewards t i U := by
    ext c
    obtain ⟨rh, hrh, hinput⟩ :=
      ReferenceFirstCollectionUpConditionalService.actualFirstCollectionUp_actualRecord_replace
        (rate := rate) rewards C_star C_h control0 t z r hr c
    have hdatah : ReferenceOriginalKthCollectionSourceSections.kthCPrechoiceData
        rate rewards C_star C_h t
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z c) = some data := by
      rw [ReferenceOriginalKthCollectionSourceSections.kthCPrechoiceData_actualRecord
        rate rewards C_star C_h t _ rh hrh, hinput]
      change ReferenceOriginalKthCollectionSourceSections.kthCPrechoiceDataFromCoordinatorCode
        rate t (ReferenceActivePhysicalStepMeasurability.encodeCoordinator
          r.input.state.coordinator) = some data
      rw [← ReferenceOriginalKthCollectionSourceSections.kthCPrechoiceData_actualRecord
        rate rewards C_star C_h t z r hr]
      exact hdata
    obtain ⟨cc, hcc, _, hpend, _⟩ := kthCPrechoiceData_actual_collectionChoice
      rate rewards C_star C_h t _ rh hrh data hdatah
    obtain ⟨v, hv, _, hvpend⟩ := collectionChoice_selection rate rh.input cc hcc
    obtain ⟨o, started, _, _, hstartedPending, hcheck, hpositive⟩ :=
      actual_collection_up_site rate rewards C_star C_h t _ rh hrh cc hcc
    have hipv : i ∈ v.view.pendingAtChoice := by rw [hvpend, ← hpend]; exact hip
    have hpendV : started.pending = v.view.pendingAtChoice := hstartedPending.trans hvpend.symm
    have hgeometry := hcontrols c
    dsimp only at hgeometry
    rw [← hinput] at hgeometry
    have hcurrent : rh.input.row.2 rh.input.time = c := by
      rw [hinput]
      exact ReferenceLaterOptionalControlResampling.withControl_currentControl r.input c
    have hfields := actualRecord_fields rate rewards C_star C_h t _ rh hrh
    have hcoord (hup : slotDraw (rh.input.row.2 rh.input.time).1 = upSlot) :
        (prepare rh.input).arms.actions (ActiveRoundActions.coordinator p.two_le_m) =
        (OrderedTupleSampler.sample p.two_le_m p.m_lt_K
          (rh.input.row.2 rh.input.time).1).val (ActiveRoundActions.coordinator p.two_le_m) := by
      have hnotfast : ¬ (CoordinatorLocalArmChoice.assignmentIsLive v.view.payload
          v.view.cutoff rh.input.time ∧ v.view.pendingAtChoice = ∅) := by
        rintro ⟨_, hempty⟩
        exact Finset.notMem_empty i (hempty ▸ hipv)
      have harm : (prepare rh.input).coordinator.arm = v.arm := by
        unfold DispatchCut.arm
        rw [hv]
      exact (prepare rh.input).action_coordinator.trans (harm.trans
        (ReferenceUpPhysicalHashRule.coordinator_choice_up v.view.payload v.view.pendingAtChoice
          v.view.cutoff rh.input.time v.view.complementWeights rh.input.row v.arm
          v.choice_eq hnotfast hup))
    change (selectedFollowerDraw p.two_le_m p.m_lt_K c.1 = i ∧
      ReferenceActiveAffinePositiveTest.upPositive
        (ReferenceLaterOptionalControlResampling.withControl r.input c) = true) ↔ _
    rw [← hinput]
    change _ ↔ (slotDraw c.1 = upSlot ∧ selectedFollowerDraw p.two_le_m p.m_lt_K c.1 = i ∧
      AffineChannelLaw.affineHash (c.2 (1, i)) (ActiveFollowerArmChoice.offeredUpWord rate.eta U) = 1 ∧
      0 < rewards t ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K c.1).val
        (ActiveRoundActions.coordinator p.two_le_m)))
    rw [← hcurrent, ← hfields.2.2.1, ← hfields.2.2.2]
    constructor
    · rintro ⟨hdraw, hp⟩
      have heligible := of_decide_eq_true (hpositive.symm.trans hp)
      obtain ⟨hup, hobs⟩ := ReferenceUpPhysicalHashRule.receiver_eligible_observation
        (prepare rh.input) started heligible
      have hreward := (coordinator_observation_positive_iff rh.input _ (hcoord hup)).mp hobs
      have hw : ReferenceActiveAffinePositiveTest.upSent rh.input =
          some (ActiveFollowerArmChoice.offeredUpWord rate.eta U) := by
        rw [ReferenceUpPhysicalHashRule.upSent_eq_configuration,
          ReferenceActiveAffinePositiveTest.upSenderIndex_eq_draw, hdraw, hgeometry.1]
        simp only [(hgeometry.2.1 (by rw [← hcurrent]; exact ⟨hup, hdraw⟩)).1]
        rfl
      have hhash := ReferenceUpPhysicalHashRule.upPositive_hash_one rh.input
        (ActiveFollowerArmChoice.offeredUpWord rate.eta U) hw hp
      rw [ReferenceActiveAffinePositiveTest.upSenderIndex_eq_draw, hdraw] at hhash
      exact ⟨hup, hdraw, hhash, hreward.2⟩
    · rintro ⟨hup, hdraw, hhash, hreward⟩
      have hfree : FiniteBanditModel.collisionFreeFor (prepare rh.input).arms.actions
          (ActiveRoundActions.coordinator p.two_le_m) := by
        intro player hne
        rcases ActiveRoundActions.player_cases p.two_le_m player with ho | ⟨j, hj⟩
        · exact (hne ho).elim
        · rw [hj, (prepare rh.input).arms.actions_follower j, hcoord hup]
          change ((prepare rh.input).followers.followers j).arm ≠
            (OrderedTupleSampler.sample p.two_le_m p.m_lt_K
              (rh.input.row.2 rh.input.time).1).val (ActiveRoundActions.coordinator p.two_le_m)
          by_cases hji : j = i
          · subst j
            rw [(hgeometry.2.1 (by rw [← hcurrent]; exact ⟨hup, hdraw⟩)).2]
            rw [← hcurrent, ActiveFollowerArmChoice.offeredUpBit, hhash, ActiveRoundActions.sendArm_one]
            exact fun he => ActiveRoundActions.followerPlayer_ne_coordinator p.two_le_m i
              ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K
                (rh.input.row.2 rh.input.time).1).property he)
          · obtain ⟨state, mem, hconfig, hstatus⟩ := kthCPrechoiceData_actual_unoccupied
              rate rewards C_star C_h t _ rh hrh data hdatah j
            obtain ⟨before, hstate, hstart, hdomain, hadm⟩ :=
              actual_choice_domains rate rewards C_star C_h t _ rh hrh j state mem hconfig
            let Uj : OrdinaryMessageCodec.UpRecord (ReferencePrelaunchFollower.codecParams p rate.eta) :=
              ⟨ActiveFollowerQueueOperation.upOfferFields state, hadm⟩
            have hg := prepare_geometry rate rh.input j before state mem
              hstate hstart hstatus hdomain Uj rfl
            have hother : slotDraw (rh.input.row.2 rh.input.time).1 ≠ dataSlot ∧
                ¬ (slotDraw (rh.input.row.2 rh.input.time).1 = upSlot ∧
                  selectedFollowerDraw p.two_le_m p.m_lt_K (rh.input.row.2 rh.input.time).1 = j) := by
              refine ⟨by rw [hup]; decide, ?_⟩
              rintro ⟨_, hjdraw⟩
              exact hji (hjdraw.symm.trans hdraw)
            rw [hg.2.2.2 hother]
            exact fun he => ActiveRoundActions.followerPlayer_ne_coordinator p.two_le_m j
              ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K
                (rh.input.row.2 rh.input.time).1).property he)
      have hobs := (coordinator_observation_positive_iff rh.input _ (hcoord hup)).mpr ⟨hfree, hreward⟩
      have hdomain := (CoordinatorUpReception.receptionInputCheck_eq_true_iff _).mp hcheck
      have hgate : CoordinatorUpReception.receptionGate
          (ReferenceCoordinatorUpPhysicalCall.actualUpInput rh.input started) := by
        refine ⟨hdomain.2.2.2.2.1.trans hdomain.2.2.2.2.2.2.1.le, hup, ?_⟩
        change selectedFollowerDraw p.two_le_m p.m_lt_K (rh.input.row.2 rh.input.time).1 ∈ started.pending
        rw [hdraw, hpendV]
        exact hipv
      have he := (CoordinatorUpReception.roundInput_selected_iff_gate _).mpr hgate
      exact ⟨hdraw, hpositive.trans (decide_eq_true ⟨he, rfl, hobs⟩)⟩
  have hnonneg : 0 ≤ (ReferenceFirstCollectionUpConditionalService.positiveRewardCount rewards t : ℝ) /
      (8 * (p.m - 1 : ℝ) * p.K) := by
    have hm : (1 : ℝ) ≤ p.m := by exact_mod_cast (Nat.le_trans (by decide : 1 ≤ 2) p.two_le_m)
    exact div_nonneg (Nat.cast_nonneg _)
      (mul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hm)) (Nat.cast_nonneg _))
  rw [ReferenceFirstCollectionUpConditionalService.actualFirstCollectionUpFreshSection_eq_measure
    rewards C_star C_h control0 i t z r hr, hset, measureReal_def,
    ReferenceFirstCollectionUpConditionalService.coordinatorUpServiceFormulaSet_probability rewards t i U,
    ENNReal.toReal_ofReal hnonneg]

/-- Global service identity on the two literal masks. All absent,
nonpending, terminal and off-stratum inputs have value zero. -/
theorem kthCSourceFreshSection_eq_masked_coefficient
    (control0 : ContinuousLearningRows.TimeControl p)
    (k : Fin (p.T + 1)) (t : Fin p.T) (i : Fin (p.m - 1)) (z : SourceInput p) :
    ReferenceOriginalKthCollectionSourceSections.kthCSourceFreshSection
        rate rewards C_star C_h k t i control0 z =
      (ReferenceOriginalKthCollectionSourceSections.kthCOLDSet rate rewards C_star C_h k t i ∪
        ReferenceOriginalKthCollectionSourceSections.kthCFORMEDSet rate rewards C_star C_h k t i).indicator
        (fun _ => (ReferenceFirstCollectionUpConditionalService.positiveRewardCount rewards t : ℝ) /
          (8 * (p.m - 1 : ℝ) * p.K)) z := by
  rw [kthCSourceFreshSection_eq_masked_cases]
  by_cases hOld : z ∈ ReferenceOriginalKthCollectionSourceSections.kthCOLDSet rate rewards C_star C_h k t i
  · rw [ite_eq_left hOld, Set.indicator_of_mem (Set.mem_union_left _ hOld)]
    exact kthCOLDSet_downFreshSection_eq_coefficient rate rewards C_star C_h control0 k t i z hOld
  · rw [ite_eq_right hOld]
    by_cases hFormed : z ∈ ReferenceOriginalKthCollectionSourceSections.kthCFORMEDSet rate rewards C_star C_h k t i
    · rw [ite_eq_left hFormed, Set.indicator_of_mem (Set.mem_union_right _ hFormed)]
      exact kthCFORMEDSet_upFreshSection_eq_coefficient rate rewards C_star C_h control0 k t i z hFormed
    · rw [ite_eq_right hFormed, Set.indicator_of_notMem (by
        rintro (h | h)
        · exact hOld h
        · exact hFormed h)]

/-- Actual pending kth-C inputs have the unmasked coefficient. -/
theorem kthC_pending_freshSection_eq_coefficient
    (control0 : ContinuousLearningRows.TimeControl p)
    (k : Fin (p.T + 1)) (t : Fin p.T) (i : Fin (p.m - 1)) (z : SourceInput p)
    (hstratum : ReferenceOriginalKthCollectionSourceSections.kthCStratum rate rewards C_star C_h k t z)
    (data : ReferenceOriginalKthCollectionSourceSections.KthCPrechoiceData rate)
    (hdata : ReferenceOriginalKthCollectionSourceSections.kthCPrechoiceData
      rate rewards C_star C_h t z = some data) (hip : i ∈ data.2.1) :
    ReferenceOriginalKthCollectionSourceSections.kthCSourceFreshSection rate rewards C_star C_h k t i control0 z =
      (ReferenceFirstCollectionUpConditionalService.positiveRewardCount rewards t : ℝ) /
        (8 * (p.m - 1 : ℝ) * p.K) := by
  have hmask : z ∈ ReferenceOriginalKthCollectionSourceSections.kthCOLDSet rate rewards C_star C_h k t i ∪
      ReferenceOriginalKthCollectionSourceSections.kthCFORMEDSet rate rewards C_star C_h k t i :=
    kthC_pending_mem_OLD_or_FORMED rate rewards C_star C_h k t i z hstratum data hdata hip
  rw [kthCSourceFreshSection_eq_masked_coefficient, Set.indicator_of_mem hmask]

/-- The original-source conditional expectation has the actual masked service
coefficient. Integrability is retained for both sides of the service identity. -/
theorem kthCSourceReadout_condExp_service
    (control0 : ContinuousLearningRows.TimeControl p)
    (k : Fin (p.T + 1)) (t : Fin p.T) (i : Fin (p.m - 1)) :
    let service := (ReferenceOriginalKthCollectionSourceSections.kthCOLDSet rate rewards C_star C_h k t i ∪
      ReferenceOriginalKthCollectionSourceSections.kthCFORMEDSet rate rewards C_star C_h k t i).indicator
      (fun _ => (ReferenceFirstCollectionUpConditionalService.positiveRewardCount rewards t : ℝ) /
        (8 * (p.m - 1 : ℝ) * p.K))
    Integrable (ReferenceOriginalKthCollectionSourceSections.kthCSourceReadout
      rate rewards C_star C_h k t i) (BootstrapPrivateRoundStreams.sourceInputLaw p) ∧
    Integrable service (BootstrapPrivateRoundStreams.sourceInputLaw p) ∧
    (BootstrapPrivateRoundStreams.sourceInputLaw p)[
      ReferenceOriginalKthCollectionSourceSections.kthCSourceReadout rate rewards C_star C_h k t i |
        sourcePrefixFiltration control0 (t.val + 1)] =ᵐ[BootstrapPrivateRoundStreams.sourceInputLaw p] service := by
  intro service
  have hservice : ReferenceOriginalKthCollectionSourceSections.kthCSourceFreshSection
      rate rewards C_star C_h k t i control0 = service := by
    funext z
    exact kthCSourceFreshSection_eq_masked_coefficient rate rewards C_star C_h control0 k t i z
  refine ⟨ReferenceOriginalKthCollectionSourceSections.integrable_kthCSourceReadout
    rate rewards C_star C_h control0 k t i, ?_, ?_⟩
  · rw [← hservice]
    exact ReferenceOriginalKthCollectionSourceSections.integrable_kthCSourceFreshSection
      rate rewards C_star C_h control0 k t i
  · rw [← hservice]
    exact kthCSourceReadout_condExp rate rewards C_star C_h control0 k t i

end Bandits.Support.ReferenceOriginalKthCollectionAwaitedService

end
