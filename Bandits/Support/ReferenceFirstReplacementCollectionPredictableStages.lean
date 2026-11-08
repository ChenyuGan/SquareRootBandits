/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstReplacementCollectionPendingFoundation

/-!
# Actual pre-round stages of first replacement collection tasks

Sources: `06_interruptions.tex:180-239,246-349,459-487`,
`05_binary_transport.tex:20-55,180-240`, and
`appendix_a_local_protocol.tex:92-157` in `sources/zip4/manuscript/`.
The observer uses the unchanged actual pending scan and physical records.
Ordinary unoccupied choices alone are OLD or FORMED; no service probability,
global ordinariness, or manuscript closure is asserted.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support ConstructorDimensions
open scoped Classical

namespace Bandits.Support.ReferenceFirstReplacementCollectionPredictableStages

variable {p : Parameters} {rate : ReferenceActivePhysicalStep.RateInput p}

abbrev Record := ReferenceFirstReplacementCollectionPendingFoundation.Record (rate := rate)
abbrev Payload := ReferenceFirstReplacementCollectionPendingFoundation.Payload (rate := rate)
abbrev Source := ReferenceFirstReplacementCollectionPendingFoundation.Source (p := p)
abbrev Down := OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta)

variable (rate)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)

variable {rate}

open ReferenceFirstReplacementCollectionPendingFoundation

/-- Only actual finite DOWN words are given a discrete observation space. -/
local instance downMeasurableSpace : MeasurableSpace (Down (rate := rate)) := ⊤

private def downCoordinates (fields : OrdinaryMessageCodec.DownFields) :=
  (fields.sigma, (fields.a, (fields.e, (fields.h, fields.q))))

private theorem downCoordinates_injective : Function.Injective downCoordinates := by
  intro x y h
  cases x
  cases y
  simp only [downCoordinates, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl, rfl, rfl, rfl⟩
  rfl

private theorem measurable_eval_fin {X A : Type*} [MeasurableSpace X]
    [MeasurableSpace A] {k : ℕ} (f : X → Fin k → A) (j : X → Fin k)
    (hf : Measurable f) (hj : Measurable j) : Measurable (fun x => f x (j x)) := by
  intro U hU
  have he : (fun x => f x (j x)) ⁻¹' U =
      ⋃ a : Fin k, {x | j x = a} ∩ (fun x => f x a) ⁻¹' U := by
    ext x
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
    exact ⟨fun h => ⟨j x, rfl, h⟩, fun ⟨a, ha, h⟩ => ha ▸ h⟩
  rw [he]
  exact MeasurableSet.iUnion fun a =>
    (hj (measurableSet_singleton a)).inter (((measurable_pi_apply a).comp hf) hU)

/-- Borel projection from the existing continuous payload, with its original
product/comap structure, to this follower's actual finite DOWN word. -/
theorem measurable_payloadDown (i : Fin (p.m - 1)) :
    Measurable (fun payload : Payload (rate := rate) => payload.downRecord i) := by
  have hobs := ReferenceCollectionDispatchMeasurability.measurable_payloadObservation
    (p := p) (rate := rate)
  have hS := ReferenceCollectionDispatchMeasurability.measurable_payloadSlowSet
    (p := p) (rate := rate)
  have ha : Measurable (fun payload : Payload (rate := rate) =>
      payload.assignment.assigned i) :=
    (measurable_of_countable (fun S : CanonicalOrientedSetLaw.SlowSet p.K p.m =>
      CanonicalAssignmentVector.followerArm p.two_le_m S i)).comp hS
  have he := AssignmentPayloadDerivedMeasurability.measurable_inputAuxiliary
    (p := p) (eta := rate.eta)
  have hh := AssignmentPayloadDerivedMeasurability.measurable_inputExponent
    (p := p) (eta := rate.eta)
  have hq : Measurable (fun payload : Payload (rate := rate) =>
      (LaterAssignmentStartMeasurability.payloadObservation payload).2.2.2.2) :=
    measurable_snd.comp (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp hobs)))
  have hhat := measurable_eval_fin _ _ hh ha
  have hqat := measurable_eval_fin _ _ hq ha
  have hsucc : Measurable (fun x : Fin p.K => x.val + 1) := measurable_of_countable _
  have hsig : Measurable (fun payload : Payload (rate := rate) => payload.sigma.val + 1) :=
    (measurable_of_countable (fun t : Fin p.T => t.val + 1)).comp
      ReferenceCollectionDispatchMeasurability.measurable_payloadSigma
  have hcoords : Measurable (fun payload : Payload (rate := rate) =>
      downCoordinates (payload.downRecord i).val) :=
    hsig.prodMk ((hsucc.comp ha).prodMk ((hsucc.comp he).prodMk (hhat.prodMk hqat)))
  apply FollowerDownMeasurability.measurable_of_countable_fibers
  intro M
  have hset : {payload : Payload (rate := rate) | payload.downRecord i = M} =
      (fun payload : Payload (rate := rate) => downCoordinates (payload.downRecord i).val) ⁻¹'
        {downCoordinates M.val} := by
    ext payload
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff]
    exact ⟨fun h => congrArg (fun w : Down (rate := rate) => downCoordinates w.val) h,
      fun h => Subtype.ext (downCoordinates_injective h)⟩
  rw [hset]
  exact hcoords (measurableSet_singleton _)

/-- Countable projection of the SAME carried payload and onset. No payload
is reconstructed, and all real-valued payload coordinates stay in `pastPhase`. -/
def wordSummary (i : Fin (p.m - 1)) : PastPhase rate → ℕ × Option (Down (rate := rate) × ℕ)
  | .firstLive => (0, none)
  | .firstCollection => (1, none)
  | .replacementLive payload => (2, some (payload.downRecord i, 0))
  | .replacementCollection payload u => (3, some (payload.downRecord i, u))
  | .closed => (4, none)

abbrev WordInput := Bool × (Bool × (Option (Down (rate := rate)) × ℕ))

/-- The transition induced by `advance` on the literal finite-word projection. -/
def wordAdvance (state : ℕ × Option (Down (rate := rate) × ℕ))
    (input : WordInput (rate := rate)) : ℕ × Option (Down (rate := rate) × ℕ) :=
  match state.1 with
  | 0 => if input.1 then (1, none) else state
  | 1 => match input.2.2.1 with
    | none => state
    | some M => (2, some (M, 0))
  | 2 => if input.2.1 then state else if input.1 then
      (3, state.2.map fun q => (q.1, input.2.2.2 + 1)) else (4, none)
  | 3 => if input.2.2.1.isSome then (4, none) else state
  | _ => (4, none)

private theorem wordSummary_advance (i : Fin (p.m - 1))
    (phase : PastPhase rate) (r : Record (rate := rate)) :
    wordSummary i (advance phase r) = wordAdvance (wordSummary i phase)
      (isCutoff r, ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen r,
        (birthPayload r).map (fun payload => payload.downRecord i), r.input.time.val) := by
  cases phase with
  | firstLive => cases hc : isCutoff r <;> simp [advance, hc, wordSummary, wordAdvance]
  | firstCollection => cases hb : birthPayload r <;> simp [advance, hb, wordSummary, wordAdvance]
  | replacementLive payload =>
      cases ht : ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen r <;>
        cases hc : isCutoff r <;> simp [advance, ht, hc, wordSummary, wordAdvance]
  | replacementCollection payload u =>
      have hsome : ((birthPayload r).map (fun payload => payload.downRecord i)).isSome =
          ReferenceCollectionPhaseHistory.laterChosen r.input := by
        rw [Option.isSome_map, birthPayload_isSome]
      simp only [advance, wordSummary, wordAdvance, hsome]
      cases ReferenceCollectionPhaseHistory.laterChosen r.input <;> rfl
  | closed => rfl

private theorem measurable_optionBind {X Y W : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace W]
    (f : Y → Option W) (hf : Measurable f) (g : X → Option Y) (hg : Measurable g) :
    Measurable (fun x => (g x).bind f) := by
  have hbind : Measurable (fun o : Option Y => o.bind f) := by
    apply measurable_comap_iff.mpr
    have hsum : Measurable (Sum.elim
        (fun y => Equiv.optionEquivSumPUnit W (f y))
        (fun _ : PUnit => Equiv.optionEquivSumPUnit W none)) :=
      (measurable_comap_iff.mp hf).sumElim measurable_const
    convert hsum.comp (comap_measurable (Equiv.optionEquivSumPUnit Y)) using 1
    funext o
    cases o <;> rfl
  exact hbind.comp hg

private theorem measurable_birthFromSelection : Measurable
    (fun q : ReferenceActivePhysicalStepMeasurability.CoordinatorCode p rate ×
      Option (ReferenceLiveDispatchOutputMeasurability.SelectionData p rate) =>
        birthFromSelection q.1 q.2) := by
  let isCollection : ReferenceActivePhysicalStepMeasurability.CoordinatorCode p rate → Bool :=
    fun c => match c with | .inr (.inr (.inl _)) => true | _ => false
  have hcol : Measurable isCollection :=
    measurable_const.sumElim (measurable_const.sumElim
      (measurable_const.sumElim measurable_const))
  have hv : Measurable (ReferenceDownReceptionMeasurability.choiceTimeViewObservation
      (p := p) (rate := rate)) := comap_measurable _
  have hp := (measurable_fst.comp hv).comp
    (measurable_fst : Measurable (Prod.fst : ReferenceLiveDispatchOutputMeasurability.SelectionData p rate → _))
  have hc := (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp hv))).comp
    (measurable_fst : Measurable (Prod.fst : ReferenceLiveDispatchOutputMeasurability.SelectionData p rate → _))
  have hs : Measurable (some : Payload (rate := rate) → Option (Payload (rate := rate))) :=
    measurable_comap_iff.mpr measurable_inl
  have hchoice : Measurable (fun choice : ReferenceLiveDispatchOutputMeasurability.SelectionData p rate =>
      if choice.1.cutoff = none then some choice.1.payload else none) :=
    Measurable.ite (measurableSet_eq_fun hc measurable_const) (hs.comp hp) measurable_const
  have hbind := measurable_optionBind _ hchoice
    (Prod.snd : ReferenceActivePhysicalStepMeasurability.CoordinatorCode p rate ×
      Option (ReferenceLiveDispatchOutputMeasurability.SelectionData p rate) → _) measurable_snd
  have h : Measurable (fun q : ReferenceActivePhysicalStepMeasurability.CoordinatorCode p rate ×
      Option (ReferenceLiveDispatchOutputMeasurability.SelectionData p rate) =>
        if isCollection q.1 = true then q.2.bind
          (fun choice => if choice.1.cutoff = none then some choice.1.payload else none) else none) :=
    Measurable.ite ((hcol.comp measurable_fst) (measurableSet_singleton true)) hbind measurable_const
  convert h using 1
  funext q
  rcases q with ⟨c, selected⟩
  cases c with
  | inl _ => rfl
  | inr c => cases c with
    | inl _ => rfl
    | inr c => cases c <;> rfl

/-- Only completed physical record codes are read by this projection. -/
def wordInput (i : Fin (p.m - 1)) (code : ReferenceActiveHorizonMeasurability.RoundRecordCode
    (p := p) (rate := rate)) (cut : Bool) : WordInput (rate := rate) :=
  (cut, liveSelection code && !cut,
    (birthFromSelection code.2.1.1 code.2.2.1.1).map (fun payload => payload.downRecord i), code.1)

private theorem measurable_wordInput (i : Fin (p.m - 1)) : Measurable
    (fun q : ReferenceActiveHorizonMeasurability.RoundRecordCode
      (p := p) (rate := rate) × Bool => wordInput i q.1 q.2) := by
  have hsome : Measurable (fun c : Option (ReferenceLiveDispatchOutputMeasurability.SelectionData p rate) =>
      c.isSome) := by
    convert ReferenceCollectionOutcomeMeasurability.measurable_optionalElim false
      (fun _ : ReferenceLiveDispatchOutputMeasurability.SelectionData p rate => true) measurable_const using 1
    funext c
    cases c <;> rfl
  have hfront : Measurable (fun code : ReferenceActiveHorizonMeasurability.RoundRecordCode
      (p := p) (rate := rate) => code.2.2.1.1) :=
    measurable_fst.comp (measurable_fst.comp (measurable_snd.comp measurable_snd))
  have hcoord : Measurable (fun code : ReferenceActiveHorizonMeasurability.RoundRecordCode
      (p := p) (rate := rate) => code.2.1.1) :=
    measurable_fst.comp (measurable_fst.comp measurable_snd)
  have hincoming : Measurable (incomingLive (p := p) (rate := rate)) :=
    measurable_const.sumElim (measurable_const.sumElim measurable_const)
  have hlive : Measurable (liveSelection (p := p) (rate := rate)) :=
    (measurable_of_countable (fun q : Bool × Bool => q.1 && q.2)).comp
      ((hincoming.comp hcoord).prodMk (hsome.comp hfront))
  have hb := measurable_birthFromSelection (rate := rate) |>.comp (hcoord.prodMk hfront)
  have hd : Measurable (fun payload : Payload (rate := rate) =>
      (some (payload.downRecord i) : Option (Down (rate := rate)))) :=
    (measurable_of_countable (some : Down (rate := rate) → Option (Down (rate := rate)))).comp
      (measurable_payloadDown i)
  have hmap := (ReferenceCollectionOutcomeMeasurability.measurable_optionalElim
    (none : Option (Down (rate := rate))) _ hd).comp hb
  have hmap' : Measurable (fun code : ReferenceActiveHorizonMeasurability.RoundRecordCode
      (p := p) (rate := rate) =>
        (birthFromSelection code.2.1.1 code.2.2.1.1).map (fun payload => payload.downRecord i)) := by
    convert hmap using 1
    funext code
    dsimp only [Function.comp_apply]
    cases birthFromSelection code.2.1.1 code.2.2.1.1 <;> rfl
  exact measurable_snd.prodMk
    (((measurable_of_countable (fun q : Bool × Bool => q.1 && !q.2)).comp
      ((hlive.comp measurable_fst).prodMk measurable_snd)).prodMk
      ((hmap'.comp measurable_fst).prodMk (measurable_fst.comp measurable_fst)))

variable (rate)

private theorem sourceCode_borel (t : Fin p.T) :
    Measurable (sourceCode rate rewards C_star C_h t) := by
  exact (measurable_pi_apply (⟨t.val, by omega⟩ : Fin (t.val + 1))).comp
    (ReferenceInspectedPastRoundObservations.measurable_pastRoundObservations
      rate rewards C_star C_h (t.val + 1) (by omega))

private theorem sourceCode_measurable (n : ℕ) (t : Fin p.T) (ht : t.val < n) :
    Measurable[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (n + 1)]
      (sourceCode rate rewards C_star C_h t) := by
  rw [ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration_succ]
  have h := (sourceCode_borel rate rewards C_star C_h t).comp
    (comap_measurable (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n))
  convert h using 1
  funext z
  exact ReferenceFirstReplacementCollectionCommonStopObservation.actualRecordCode_factor
    rate rewards C_star C_h control0 n t ht z

private theorem wordSummary_next (n : ℕ) (hn : n < p.T) (i : Fin (p.m - 1)) (z : Source (p := p)) :
    wordSummary i (pastPhase rate rewards C_star C_h (n + 1) z) =
      match sourceCode rate rewards C_star C_h ⟨n, hn⟩ z with
      | none => wordSummary i (pastPhase rate rewards C_star C_h n z)
      | some code => wordAdvance (wordSummary i (pastPhase rate rewards C_star C_h n z))
          (wordInput i code (cutoffFlag rate rewards C_star C_h ⟨n, hn⟩ z)) := by
  rw [pastPhase, dite_eq_left hn]
  unfold sourceCode
  rw [cutoffFlag_eq]
  cases hr : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h ⟨n, hn⟩ z with
  | none => rfl
  | some r =>
      simp only [Option.map_some, Option.getD_some]
      rw [wordSummary_advance, continuing_eq_code, birthPayload_eq_code]
      rfl

private theorem laterOptionSpace_countable {A : Type*} [MeasurableSpace A]
    [Countable A] [MeasurableSingletonClass A] :
    @LaterAssignmentStartMeasurability.optionMeasurableSpace A inferInstance = ⊤ := by
  apply MeasurableSpace.ext
  intro U
  constructor
  · intro _; trivial
  · intro _
    rw [LaterAssignmentStartMeasurability.optionMeasurableSpace,
      MeasurableSpace.measurableSet_comap]
    let e := Equiv.optionEquivSumPUnit A
    have hU : MeasurableSet (e '' U) := by
      rw [measurableSet_sum_iff]
      exact ⟨(Set.to_countable _).measurableSet, (Set.to_countable _).measurableSet⟩
    exact ⟨e '' U, hU, e.injective.preimage_image U⟩

/-- The finite DOWN word and onset projected from the original scan are
measurable strictly before the original round's current fresh controls. -/
theorem wordSummary_measurable (n : ℕ) (i : Fin (p.m - 1)) :
    Measurable[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (n + 1)]
      (fun z : Source (p := p) => wordSummary i (pastPhase rate rewards C_star C_h n z)) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
      let F := ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0
      let : MeasurableSpace (Source (p := p)) := F (n + 1 + 1)
      have hprev : Measurable (fun z : Source (p := p) =>
          wordSummary i (pastPhase rate rewards C_star C_h n z)) :=
        ih.mono (F.mono (show n + 1 ≤ n + 1 + 1 by omega)) le_rfl
      by_cases hn : n < p.T
      · have hcode := sourceCode_measurable rate rewards C_star C_h control0 (n + 1) ⟨n, hn⟩ (Nat.lt_succ_self n)
        have hcut : Measurable (cutoffFlag rate rewards C_star C_h ⟨n, hn⟩) :=
          (cutoffFlag_measurable rate rewards C_star C_h control0 ⟨n, hn⟩).mono
            (F.mono (show n + 1 ≤ n + 1 + 1 by omega)) le_rfl
        have hinput := (ReferenceCollectionOutcomeMeasurability.measurable_mapOptional _
          (measurable_wordInput (rate := rate) i)).comp (hcode.prodMk hcut)
        rw [laterOptionSpace_countable (A := WordInput (rate := rate))] at hinput
        have hstep := (measurable_of_countable
          (fun q : (ℕ × Option (Down (rate := rate) × ℕ)) × Option (WordInput (rate := rate)) =>
            match q.2 with | none => q.1 | some input => wordAdvance q.1 input)).comp
          (hprev.prodMk hinput)
        convert hstep using 1
        funext z
        rw [wordSummary_next rate rewards C_star C_h n hn i z]
        dsimp only [Function.comp_apply, ReferenceCollectionOutcomeMeasurability.mapOptional]
        cases sourceCode rate rewards C_star C_h ⟨n, hn⟩ z <;> rfl
      · convert hprev using 1
        funext z
        simp only [pastPhase, dite_eq_right hn]

/-- Exact DOWN/onset projection of the unchanged `payloadOnset`. -/
def wordOnset (n : ℕ) (i : Fin (p.m - 1)) (z : Source (p := p)) :
    Option (Down (rate := rate) × ℕ) :=
  (payloadOnset rate rewards C_star C_h n z).map (fun q => (q.1.downRecord i, q.2))

/-- The measurable summary observes exactly the original payload, not just
its assignment start or a rival reconstruction. -/
theorem wordOnset_eq (n : ℕ) (i : Fin (p.m - 1)) (z : Source (p := p)) :
    wordOnset rate rewards C_star C_h n i z =
      let q := wordSummary i (pastPhase rate rewards C_star C_h n z)
      if q.1 = 2 then q.2.map (fun pair => (pair.1, n + 1))
      else if q.1 = 3 then q.2 else none := by
  unfold wordOnset payloadOnset
  cases pastPhase rate rewards C_star C_h n z <;> rfl

theorem wordOnset_measurable (n : ℕ) (i : Fin (p.m - 1)) :
    Measurable[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (n + 1)]
      (wordOnset rate rewards C_star C_h n i) := by
  have h := (measurable_of_countable
    (fun q : ℕ × Option (Down (rate := rate) × ℕ) =>
      if q.1 = 2 then q.2.map (fun pair => (pair.1, n + 1))
      else if q.1 = 3 then q.2 else none)).comp
    (wordSummary_measurable rate rewards C_star C_h control0 n i)
  convert h using 1
  funext z
  exact wordOnset_eq rate rewards C_star C_h n i z

variable {rate}

inductive TaskStage where
  | old
  | formed
  | nonordinary
  deriving DecidableEq, Countable

instance taskStageMeasurableSpace : MeasurableSpace TaskStage := ⊤

instance taskStageDiscreteMeasurableSpace : DiscreteMeasurableSpace TaskStage :=
  ⟨fun _ => trivial⟩

private instance startCodeDiscreteMeasurableSpace :
    DiscreteMeasurableSpace (FollowerLifecycleMeasurability.StartRoundResultCode p rate) :=
  ⟨fun _ => trivial⟩

private instance startSumMeasurableSingletonClass :
    MeasurableSingletonClass (Unit ⊕ FollowerLifecycleMeasurability.StartRoundResultCode p rate) where
  measurableSet_singleton q := by
    rw [measurableSet_sum_iff]
    cases q <;> constructor <;> simp

/-- Compare the actual ordinary unoccupied choice with this SAME payload's
current DOWN record. An older accepted DOWN is OLD as well. -/
def choiceStage (r : Record (rate := rate)) (payload : Payload (rate := rate))
    (i : Fin (p.m - 1)) : TaskStage :=
  match (ReferenceFollowerFixedReply.actualChoice r i).configuration with
  | .dagger => .nonordinary
  | .ordinary state _ =>
      if state.status = .unoccupied then
        if state.lastDown = some (payload.downRecord i) then .formed else .old
      else .nonordinary

/-- OLD is exactly the actual ordinary unoccupied old-word condition. -/
theorem choiceStage_old_iff (r : Record (rate := rate)) (payload : Payload (rate := rate))
    (i : Fin (p.m - 1)) :
    choiceStage r payload i = .old ↔
      ReferenceFirstReplacementCollectionOldDownCallDates.actualOldAt r i (payload.downRecord i) := by
  cases hc : (ReferenceFollowerFixedReply.actualChoice r i).configuration with
  | dagger => simp [choiceStage, hc, ReferenceFirstReplacementCollectionOldDownCallDates.actualOldAt]
  | ordinary state memory =>
      by_cases hu : state.status = .unoccupied <;>
        by_cases hw : state.lastDown = some (payload.downRecord i) <;>
        simp [choiceStage, hc, hu, hw, ReferenceFirstReplacementCollectionOldDownCallDates.actualOldAt]

/-- FORMED keeps exactly the current DOWN word, rather than merely a nonempty
last-DOWN register or the initial collection's special case. -/
theorem choiceStage_formed_iff (r : Record (rate := rate)) (payload : Payload (rate := rate))
    (i : Fin (p.m - 1)) :
    choiceStage r payload i = .formed ↔
      ∃ state memory,
        (ReferenceFollowerFixedReply.actualChoice r i).configuration = .ordinary state memory ∧
        state.status = .unoccupied ∧ state.lastDown = some (payload.downRecord i) := by
  cases hc : (ReferenceFollowerFixedReply.actualChoice r i).configuration with
  | dagger => simp [choiceStage, hc]
  | ordinary state memory =>
      by_cases hu : state.status = .unoccupied <;>
        by_cases hw : state.lastDown = some (payload.downRecord i) <;>
        simp [choiceStage, hc, hu, hw]

/-- The two stages exhaust precisely the ordinary unoccupied configurations.
This theorem does not infer ordinary preparation from fixed words. -/
theorem choiceStage_old_or_formed (r : Record (rate := rate)) (payload : Payload (rate := rate))
    (i : Fin (p.m - 1)) :
    (choiceStage r payload i = .old ∨ choiceStage r payload i = .formed) ↔
      ∃ state memory,
        (ReferenceFollowerFixedReply.actualChoice r i).configuration = .ordinary state memory ∧
        state.status = .unoccupied := by
  cases hc : (ReferenceFollowerFixedReply.actualChoice r i).configuration with
  | dagger => simp [choiceStage, hc]
  | ordinary state memory =>
      by_cases hu : state.status = .unoccupied <;>
        by_cases hw : state.lastDown = some (payload.downRecord i) <;>
        simp [choiceStage, hc, hu, hw]

variable (rate)

/-- A row-free local StartRound readout. Dagger and a checked lifecycle
failure have distinct tags; the original scalar family is passed unchanged. -/
def localStartCode (t : Fin p.T)
    (c : FollowerPrepareJointMeasurability.IncomingConfiguration p rate) :
    Unit ⊕ FollowerLifecycleMeasurability.StartRoundResultCode p rate :=
  (FollowerPrepareJointMeasurability.incomingConfigurationToSum c).elim
    (fun _ => .inl ()) (fun q => .inr
      (FollowerPrepareJointMeasurability.startRoundResultCode rate
        (FollowerPrepareJointMeasurability.assembleStartInput q.1 q.2 t)))

private theorem localStartCode_measurable (t : Fin p.T) :
    Measurable (localStartCode (rate := rate) t) := by
  have hstart := FollowerPrepareJointMeasurability.measurable_startRoundResultCode_atComponents
    rate (Prod.fst : FollowerObservationStageMeasurabilityRepair.CarriedState p rate ×
      FollowerLifecycleMeasurability.LocalMemoryCode p → _)
    Prod.snd (fun _ => t) measurable_fst measurable_snd measurable_const
  exact (measurable_const.sumElim (measurable_inr.comp hstart)).comp
    (FollowerPrepareJointMeasurability.measurable_incomingConfigurationToSum rate)

private theorem localStartCode_encode (t : Fin p.T)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p) :
    localStartCode (rate := rate) t
      (FollowerPrepareJointMeasurability.incomingOfLocalConfiguration rate (.ordinary state memory)) =
      .inr (FollowerLifecycleMeasurability.startRoundResultCode rate
        (ActiveFollowerLifecycle.startRound rate.eta t state memory)) := by
  unfold localStartCode FollowerPrepareJointMeasurability.incomingOfLocalConfiguration
    FollowerPrepareJointMeasurability.incomingConfigurationToSum
  dsimp only [Sum.elim_inr, FollowerPrepareJointMeasurability.startRoundResultCode,
    FollowerPrepareJointMeasurability.assembleStartInput,
    FollowerLifecycleMeasurability.startRoundResultCodeAt]
  have hs := FollowerObservationStageMeasurabilityRepair.carriedStateOfState_reconstruct rate state
  dsimp only [FollowerObservationStageMeasurabilityRepair.carriedStateBuffer] at hs
  rw [hs, FollowerLifecycleMeasurability.localMemoryOfCode_code]

/-- Original-source pre-round follower preparation input. This readout uses
no current arm, feedback, selected channel or fresh current control. -/
def preRoundStart (t : Fin p.T) (i : Fin (p.m - 1)) (z : Source (p := p)) :
    Unit ⊕ FollowerLifecycleMeasurability.StartRoundResultCode p rate :=
  ReferenceCollectionOutcomeMeasurability.optionalElim (.inl ())
    (fun c => localStartCode (rate := rate) t (c.2.2.2 i))
    (ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t z)

/-- Full Borel preparation code in the incoming source field. Continuous
saved buffers keep the admitted product Borel structure. -/
theorem preRoundStart_measurable (t : Fin p.T) (i : Fin (p.m - 1)) :
    Measurable[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (t.val + 1)]
      (preRoundStart rate rewards C_star C_h t i) := by
  have hc : Measurable (fun c : ReferenceActivePhysicalStepMeasurability.StateCode p rate => c.2.2.2 i) :=
    (measurable_pi_apply i).comp (measurable_snd.comp (measurable_snd.comp measurable_snd))
  exact (ReferenceCollectionOutcomeMeasurability.measurable_optionalElim (.inl ())
    _ ((localStartCode_measurable (rate := rate) t).comp hc)).comp
      (ReferenceSourcePrefixHistoryFiltration.incoming_measurable rate rewards C_star C_h control0 t)

/-- The actual original-source prefix preserves the whole local preparation
code, including absent and lifecycle-failure branches. -/
theorem preRoundStart_factor (t : Fin p.T) (i : Fin (p.m - 1)) (z : Source (p := p)) :
    preRoundStart rate rewards C_star C_h t i z =
      preRoundStart rate rewards C_star C_h t i
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z) := by
  unfold preRoundStart
  rw [ReferenceSourcePrefixHistoryFiltration.incoming_factor rate rewards C_star C_h control0 t z]

/-- Exact local register readout at a present incoming ordinary record. This
is an equation of the original checked StartRound, without a domain law. -/
theorem preRoundStart_at_ordinary (t : Fin p.T) (i : Fin (p.m - 1)) (z : Source (p := p))
    (r : Record (rate := rate)) (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some r)
    (hc : r.input.state.followers i = .ordinary state memory) :
    preRoundStart rate rewards C_star C_h t i z =
      .inr (FollowerLifecycleMeasurability.startRoundResultCode rate
        (ActiveFollowerLifecycle.startRound rate.eta t state memory)) := by
  simp only [preRoundStart, ReferenceSourcePrefixHistoryFiltration.incoming, hr,
    Option.map_some, ReferenceCollectionOutcomeMeasurability.optionalElim,
    ReferenceActivePhysicalStepMeasurability.encodeState, hc]
  exact localStartCode_encode (rate := rate) t state memory

/-- On an actual incoming ordinary branch, the admitted full-history
preparation producer identifies this row-free code with the actual CHOICE.
Ordinariness is derived from that producer, not from word agreement. -/
theorem preRoundStart_actual_choice (t : Fin p.T) (i : Fin (p.m - 1)) (z : Source (p := p))
    (r : Record (rate := rate)) (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some r)
    (hc : r.input.state.followers i = .ordinary state memory) :
    ∃ choice : ReferencePrelaunchFollower.State p rate.eta,
      (ReferenceFollowerFixedReply.actualChoice r i).configuration = .ordinary choice memory ∧
      preRoundStart rate rewards C_star C_h t i z =
        .inr (.success (FollowerDownMeasurability.followerStateCode rate choice)
          (FollowerLifecycleMeasurability.localMemoryCode memory)) := by
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  unfold ReferenceSourcePrefixHistoryFiltration.actualRecord at hr
  split at hr
  · rename_i hs
    obtain ⟨hk, he⟩ := List.getElem?_eq_some_iff.mp hr
    let k : Fin R.length := ⟨t.val - s, hk⟩
    have hget : R[k.val] = r := he
    obtain ⟨hcross, hspan, hrecord⟩ :=
      ReferenceLaterLiveNumericalReadout.source_record_prefix rate rewards C_star C_h z k
    have htime : r.input.time = t := by
      apply Fin.ext
      have hcalendar : (R.get k).input.time.val = s + k.val := by rw [hrecord]; rfl
      change (R[k.val]).input.time.val = s + k.val at hcalendar
      rw [hget] at hcalendar
      have hkval : k.val = t.val - s := rfl
      dsimp only [s] at hkval
      omega
    have hinput : (R[k.val]).input.state.followers i = .ordinary state memory := hget ▸ hc
    obtain ⟨choice, _hvalid, hstart, hchoice, _hchoiceValid, _hoperation⟩ :=
      ReferenceCompleteFollowerPreparation.complete_ordinary_input_prepare
        (rate := rate) rewards C_star C_h z k i state memory hinput
    rw [hget] at hstart hchoice
    rw [htime] at hstart
    refine ⟨choice, hchoice, ?_⟩
    have hlookup : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some r := by
      rw [ReferenceSourcePrefixHistoryFiltration.actualRecord, ite_eq_left hs]
      exact hr
    rw [preRoundStart_at_ordinary rate rewards C_star C_h t i z r state memory hlookup hc, hstart]
    rfl
  · cases hr

/-- Read precisely the unoccupied/last-DOWN fields of the checked start code.
Dagger and checked lifecycle failure remain nonordinary. -/
def startStage (M : Down (rate := rate)) :
    Unit ⊕ FollowerLifecycleMeasurability.StartRoundResultCode p rate → TaskStage
  | .inr (.success state _) =>
      if state.status = 0 then
        if state.lastDown = some M then .formed else .old
      else .nonordinary
  | _ => .nonordinary

private theorem actualChoice_dagger (r : Record (rate := rate)) (i : Fin (p.m - 1))
    (hc : r.input.state.followers i = .dagger) :
    (ReferenceFollowerFixedReply.actualChoice r i).configuration = .dagger := by
  unfold ReferenceFollowerFixedReply.actualChoice
  rw [preparation_eq]
  rw [(ReferenceActivePhysicalStep.prepare r.input).followers.followers_eq i,
    ReferenceActiveFeedbackCut.prepareFollowers_apply]
  change (DeclaredFollowerLocalRound.prepare rate i r.input.row (r.input.state.activations i)
    r.input.time (r.input.active i) (r.input.state.followers i)).configuration = .dagger
  rw [hc]
  exact (DeclaredFollowerLocalRound.prepare_dagger rate i r.input.row (r.input.state.activations i)
    r.input.time (r.input.active i)).2

/-- Original-history preparation supplies the exact actual choice stage.
The dagger branch is explicit; no stage-domain or ordinary-choice law is assumed. -/
theorem preRoundStart_choiceStage (t : Fin p.T) (i : Fin (p.m - 1)) (z : Source (p := p))
    (r : Record (rate := rate)) (payload : Payload (rate := rate))
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some r) :
    startStage rate (payload.downRecord i) (preRoundStart rate rewards C_star C_h t i z) =
      choiceStage r payload i := by
  cases hc : r.input.state.followers i with
  | dagger =>
      have hd := actualChoice_dagger rate r i hc
      simp only [preRoundStart, ReferenceSourcePrefixHistoryFiltration.incoming, hr,
        Option.map_some, ReferenceCollectionOutcomeMeasurability.optionalElim,
        ReferenceActivePhysicalStepMeasurability.encodeState, hc,
        FollowerPrepareJointMeasurability.incomingOfLocalConfiguration, localStartCode,
        FollowerPrepareJointMeasurability.incomingConfigurationToSum, Sum.elim_inl,
        startStage, choiceStage, hd]
  | ordinary state memory =>
      obtain ⟨choice, hchoice, hstart⟩ :=
        preRoundStart_actual_choice rate rewards C_star C_h t i z r state memory hr hc
      rw [hstart]
      cases hs : choice.status <;>
        simp [startStage, choiceStage, hchoice, FollowerDownMeasurability.followerStateCode,
          FollowerDownMeasurability.followerStatusCode, hs]

/-- The actual optional stage, supported by the actual masked pending set.
Neither a missing payload nor a missing physical record is reconstructed. -/
def taskStage (n : ℕ) (i : Fin (p.m - 1)) (z : Source (p := p)) : Option TaskStage :=
  if i ∈ ReferenceFirstReplacementCollectionPendingFoundation.P_repl rate rewards C_star C_h control0 n z then
    if hn : n < p.T then
      (ReferenceFirstReplacementCollectionPendingFoundation.payloadOnset rate rewards C_star C_h n z).bind fun pair =>
        (ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h ⟨n, hn⟩ z).map
          (fun r => choiceStage r pair.1 i)
    else none
  else none

def OLD (n : ℕ) (i : Fin (p.m - 1)) (z : Source (p := p)) : Prop :=
  taskStage rate rewards C_star C_h control0 n i z = some .old

def FORMED (n : ℕ) (i : Fin (p.m - 1)) (z : Source (p := p)) : Prop :=
  taskStage rate rewards C_star C_h control0 n i z = some .formed

/-- Disjointness requires no trajectory, stage-domain or service premise. -/
theorem OLD_FORMED_disjoint (n : ℕ) (i : Fin (p.m - 1)) (z : Source (p := p)) :
    ¬ (OLD rate rewards C_star C_h control0 n i z ∧
      FORMED rate rewards C_star C_h control0 n i z) := by
  rintro ⟨hOld, hFormed⟩
  have h : (some TaskStage.old : Option TaskStage) = some .formed := hOld.symm.trans hFormed
  cases h

/-- Exact pointwise readout on a present actual record and its retained
payload. These are local lookup equations, not supplied phase or stage laws. -/
theorem taskStage_at_record (t : Fin p.T) (i : Fin (p.m - 1)) (z : Source (p := p))
    (r : Record (rate := rate)) (payload : Payload (rate := rate)) (u : ℕ)
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some r)
    (hp : ReferenceFirstReplacementCollectionPendingFoundation.payloadOnset rate rewards C_star C_h t.val z = some (payload, u)) :
    taskStage rate rewards C_star C_h control0 t.val i z =
      if i ∈ ReferenceFirstReplacementCollectionPendingFoundation.P_repl rate rewards C_star C_h control0 t.val z
      then some (choiceStage r payload i) else none := by
  simp only [taskStage, dite_eq_left t.isLt, hp, hr, Option.bind_some, Option.map_some]


/-- Unsupported labels have no stage, including nonordinary choices. -/
theorem taskStage_of_not_pending (n : ℕ) (i : Fin (p.m - 1)) (z : Source (p := p))
    (hi : i ∉ P_repl rate rewards C_star C_h control0 n z) :
    taskStage rate rewards C_star C_h control0 n i z = none := by
  simp only [taskStage, ite_eq_right hi]

/-- The observer is absent from the horizon onward. -/
theorem taskStage_of_horizon_le (n : ℕ) (i : Fin (p.m - 1)) (z : Source (p := p))
    (hn : p.T ≤ n) : taskStage rate rewards C_star C_h control0 n i z = none := by
  simp only [taskStage, dite_eq_right (Nat.not_lt.mpr hn), ite_self]

/-- Exact row-free expression of the literal stage observer. The incoming
option preserves missing records rather than inventing a local configuration. -/
theorem taskStage_eq_preRound (t : Fin p.T) (i : Fin (p.m - 1)) (z : Source (p := p)) :
    taskStage rate rewards C_star C_h control0 t.val i z =
      if i ∈ P_repl rate rewards C_star C_h control0 t.val z then
        (wordOnset rate rewards C_star C_h t.val i z).bind fun q =>
          (ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t z).map
            (fun _ => startStage rate q.1 (preRoundStart rate rewards C_star C_h t i z))
      else none := by
  unfold taskStage wordOnset
  rw [dite_eq_left t.isLt]
  split_ifs
  · cases hp : payloadOnset rate rewards C_star C_h t.val z with
    | none => rfl
    | some pair =>
      rcases pair with ⟨payload, u⟩
      cases hr : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z with
      | none => simp only [ReferenceSourcePrefixHistoryFiltration.incoming, hr,
          Option.map_none, Option.map_some, Option.bind_some]
      | some r =>
        simp only [Option.map_some, Option.bind_some, ReferenceSourcePrefixHistoryFiltration.incoming,
          hr, Option.map_some]
        exact congrArg some (preRoundStart_choiceStage rate rewards C_star C_h t i z r payload hr).symm
  · rfl

/-- Strict-past measurability of the entire actual optional stage, on every
original source with whole rewards and unrestricted constants. -/
theorem taskStage_measurable (n : ℕ) (i : Fin (p.m - 1)) :
    Measurable[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (n + 1)]
      (taskStage rate rewards C_star C_h control0 n i) := by
  let F := ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0
  let : MeasurableSpace (Source (p := p)) := F (n + 1)
  by_cases hn : n < p.T
  · let t : Fin p.T := ⟨n, hn⟩
    have hw := wordOnset_measurable rate rewards C_star C_h control0 n i
    have hs := preRoundStart_measurable rate rewards C_star C_h control0 t i
    have hin := ReferenceSourcePrefixHistoryFiltration.incoming_measurable
      rate rewards C_star C_h control0 t
    have hread : Measurable (fun q :
        Option (Down (rate := rate) × ℕ) ×
          ((Unit ⊕ FollowerLifecycleMeasurability.StartRoundResultCode p rate) ×
            Option (ReferenceActivePhysicalStepMeasurability.StateCode p rate)) =>
        q.1.bind fun w => q.2.2.map (fun _ => startStage rate w.1 q.2.1)) := by
      apply measurable_from_prod_countable_right
      intro word
      apply measurable_from_prod_countable_right
      intro start
      cases word with
      | none => exact measurable_const
      | some w =>
          convert ReferenceCollectionOutcomeMeasurability.measurable_optionalElim
            (none : Option TaskStage)
            (fun _ : ReferenceActivePhysicalStepMeasurability.StateCode p rate =>
              some (startStage rate w.1 start)) measurable_const using 1
          funext code
          cases code <;> rfl
    have h : Measurable (fun z : Source (p := p) =>
        if i ∈ P_repl rate rewards C_star C_h control0 n z then
          (wordOnset rate rewards C_star C_h n i z).bind fun w =>
            (ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t z).map
              (fun _ => startStage rate w.1 (preRoundStart rate rewards C_star C_h t i z))
        else none) :=
      Measurable.ite (P_repl_mem_measurable rate rewards C_star C_h control0 n i)
        (hread.comp (hw.prodMk (hs.prodMk hin))) measurable_const
    convert h using 1
    funext z
    exact taskStage_eq_preRound rate rewards C_star C_h control0 t i z
  · convert (measurable_const : Measurable (fun _ : Source (p := p) =>
      (none : Option TaskStage))) using 1
    funext z
    exact taskStage_of_horizon_le rate rewards C_star C_h control0 n i z (Nat.le_of_not_lt hn)

/-- OLD is an event in the pre-round original-source field. -/
theorem OLD_measurable (n : ℕ) (i : Fin (p.m - 1)) :
    MeasurableSet[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (n + 1)]
      {z : Source (p := p) | OLD rate rewards C_star C_h control0 n i z} :=
  (taskStage_measurable rate rewards C_star C_h control0 n i) (measurableSet_singleton _)

/-- FORMED uses exactly the same predictable observer as OLD. -/
theorem FORMED_measurable (n : ℕ) (i : Fin (p.m - 1)) :
    MeasurableSet[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (n + 1)]
      {z : Source (p := p) | FORMED rate rewards C_star C_h control0 n i z} :=
  (taskStage_measurable rate rewards C_star C_h control0 n i) (measurableSet_singleton _)

theorem OLD_borel (n : ℕ) (i : Fin (p.m - 1)) :
    MeasurableSet {z : Source (p := p) | OLD rate rewards C_star C_h control0 n i z} :=
  (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).le (n + 1)
    _ (OLD_measurable rate rewards C_star C_h control0 n i)

theorem FORMED_borel (n : ℕ) (i : Fin (p.m - 1)) :
    MeasurableSet {z : Source (p := p) | FORMED rate rewards C_star C_h control0 n i z} :=
  (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).le (n + 1)
    _ (FORMED_measurable rate rewards C_star C_h control0 n i)

/-- Pointwise prefix factorization, not just an almost-everywhere version. -/
theorem taskStage_factor (n : ℕ) (i : Fin (p.m - 1)) (z : Source (p := p)) :
    taskStage rate rewards C_star C_h control0 n i z =
      taskStage rate rewards C_star C_h control0 n i
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n z) := by
  have h := (taskStage_measurable rate rewards C_star C_h control0 n i)
    (measurableSet_singleton (taskStage rate rewards C_star C_h control0 n i z))
  rw [ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration_succ] at h
  obtain ⟨B, _hB, he⟩ := h
  have hmem : z ∈ {x | taskStage rate rewards C_star C_h control0 n i x =
      taskStage rate rewards C_star C_h control0 n i z} := rfl
  change z ∈ taskStage rate rewards C_star C_h control0 n i ⁻¹'
    {taskStage rate rewards C_star C_h control0 n i z} at hmem
  rw [← he] at hmem
  have hmem' : ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n z ∈
      {x | taskStage rate rewards C_star C_h control0 n i x =
        taskStage rate rewards C_star C_h control0 n i z} := by
    change ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n z ∈
      taskStage rate rewards C_star C_h control0 n i ⁻¹'
        {taskStage rate rewards C_star C_h control0 n i z}
    rw [← he]
    change ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n z) ∈ B
    rw [ReferenceSourcePrefixHistoryFiltration.sourcePrefix_sourcePrefix control0 n n le_rfl]
    exact hmem
  exact hmem'.symm

/-- The finite DOWN/onset projection itself factors through the strict past. -/
theorem wordOnset_factor (n : ℕ) (i : Fin (p.m - 1)) (z : Source (p := p)) :
    wordOnset rate rewards C_star C_h n i z =
      wordOnset rate rewards C_star C_h n i
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n z) := by
  have h := (wordOnset_measurable rate rewards C_star C_h control0 n i)
    (measurableSet_singleton (wordOnset rate rewards C_star C_h n i z))
  rw [ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration_succ] at h
  obtain ⟨B, _hB, he⟩ := h
  have hmem : z ∈ wordOnset rate rewards C_star C_h n i ⁻¹'
      {wordOnset rate rewards C_star C_h n i z} := rfl
  rw [← he] at hmem
  have hmem' : ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n z ∈
      wordOnset rate rewards C_star C_h n i ⁻¹'
        {wordOnset rate rewards C_star C_h n i z} := by
    rw [← he]
    change ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n z) ∈ B
    rw [ReferenceSourcePrefixHistoryFiltration.sourcePrefix_sourcePrefix control0 n n le_rfl]
    exact hmem
  exact hmem'.symm

theorem not_OLD_of_not_pending (n : ℕ) (i : Fin (p.m - 1)) (z : Source (p := p))
    (hi : i ∉ P_repl rate rewards C_star C_h control0 n z) :
    ¬ OLD rate rewards C_star C_h control0 n i z := by
  unfold OLD
  rw [taskStage_of_not_pending rate rewards C_star C_h control0 n i z hi]
  intro h
  cases h

theorem not_FORMED_of_not_pending (n : ℕ) (i : Fin (p.m - 1)) (z : Source (p := p))
    (hi : i ∉ P_repl rate rewards C_star C_h control0 n z) :
    ¬ FORMED rate rewards C_star C_h control0 n i z := by
  unfold FORMED
  rw [taskStage_of_not_pending rate rewards C_star C_h control0 n i z hi]
  intro h
  cases h

theorem not_OLD_of_horizon_le (n : ℕ) (i : Fin (p.m - 1)) (z : Source (p := p))
    (hn : p.T ≤ n) : ¬ OLD rate rewards C_star C_h control0 n i z := by
  unfold OLD
  rw [taskStage_of_horizon_le rate rewards C_star C_h control0 n i z hn]
  intro h
  cases h

theorem not_FORMED_of_horizon_le (n : ℕ) (i : Fin (p.m - 1)) (z : Source (p := p))
    (hn : p.T ≤ n) : ¬ FORMED rate rewards C_star C_h control0 n i z := by
  unfold FORMED
  rw [taskStage_of_horizon_le rate rewards C_star C_h control0 n i z hn]
  intro h
  cases h

theorem disjoint_OLD_FORMED (n : ℕ) (i : Fin (p.m - 1)) :
    Disjoint {z : Source (p := p) | OLD rate rewards C_star C_h control0 n i z}
      {z : Source (p := p) | FORMED rate rewards C_star C_h control0 n i z} := by
  exact Set.disjoint_left.mpr fun z ho hf =>
    OLD_FORMED_disjoint rate rewards C_star C_h control0 n i z ⟨ho, hf⟩

/-- The unchanged original-source root, including every birth/cutoff failure
constructor, yields the literal optional stage at every collection coordinate.
There is no supplied launch, payload agreement, stage law, or ordinary premise. -/
theorem complete_first_replacement_predictable_stages :
    ∀ z : Source (p := p),
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
    let v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
    let tail := ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v
    let c := v + 1 + tail.length
    match R[v]? with
    | none => True
    | some birth =>
      match birth.output.preparation.coordinator with
      | .collection _ _ _ _ (.laterChosen _ _ _ _ _ _ _ _ _ installed _) =>
        let payload := installed.registers.payload
        match R[c]? with
        | none => True
        | some cut =>
          match cut.output.preparation.coordinator with
          | .live _ _ _ (.cutoffChosen _ _ _ _ _ _ _ _ _ _) =>
            let u := cut.input.time.val + 1
            let K := cut :: (R.drop (c + 1)).takeWhile
              (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
            ∀ a : Fin K.length,
              let n := u - 1 + a.val
              ∀ i : Fin (p.m - 1),
                (i ∈ P_repl rate rewards C_star C_h control0 n z ↔
                  i ∈ ReferenceFirstCollectionPendingObservation.Q rate rewards C_star C_h
                    payload.sigma.val (K.get a).input.time z ∧
                  a.val ≤ ReferenceFirstReplacementCollectionStoppedCompositeQuota.commonStopIndex
                    s K z rewards C_star C_h control0 i) ∧
                taskStage rate rewards C_star C_h control0 n i z =
                  if i ∈ P_repl rate rewards C_star C_h control0 n z
                  then some (choiceStage (K.get a) payload i) else none
          | _ => True
      | _ => True := by
  intro z
  have hP := complete_first_replacement_pending_coordinates rate rewards C_star C_h control0 z
  have hQ :=
    ReferenceFirstReplacementCollectionStoppedCompositeQuota.complete_first_replacement_collection_stopped_composite_quota
      rate z rewards C_star C_h control0
  dsimp only at hP hQ ⊢
  set R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  set s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  set w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
  set v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
  set tail := ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v
  set c := v + 1 + tail.length
  cases hb : R[v]? with
  | none => trivial
  | some birth =>
    rw [hb] at hP hQ
    dsimp only at hP hQ ⊢
    cases hbirth : birth.output.preparation.coordinator with
    | first _ => trivial
    | live _ _ _ _ => trivial
    | dagger => trivial
    | invalidCollectionCutoff => trivial
    | collection _ _ _ _ outcome =>
      rw [hbirth] at hP hQ
      cases outcome <;> try trivial
      rename_i core consistent started hstart instruction hinstruction output hconsistent
        clockData installed selectedBirth
      dsimp only [ReferenceActivePhysicalStep.collectionInput] at hP hQ ⊢
      cases hc : R[c]? with
      | none => trivial
      | some cut =>
        rw [hc] at hP hQ
        dsimp only at hP hQ ⊢
        cases hcut : cut.output.preparation.coordinator with
        | first _ => trivial
        | collection _ _ _ _ _ => trivial
        | dagger => trivial
        | invalidCollectionCutoff => trivial
        | live registers owned base outcome =>
          rw [hcut] at hP hQ
          cases outcome <;> try trivial
          dsimp only at hP hQ ⊢
          obtain ⟨_hcuttime, hcalendar, _hinjective, _hquota⟩ := hQ
          intro a i
          obtain ⟨hp, hr, _hraw, hmem⟩ := hP a
          have ht := hcalendar a
          let K := cut :: (R.drop (c + 1)).takeWhile
            (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
          have htime : (K.get a).input.time.val = cut.input.time.val + 1 - 1 + a.val := by
            change (K.get a).input.time.val + 1 = cut.input.time.val + 1 + a.val at ht
            omega
          refine ⟨hmem i, ?_⟩
          have hstage := taskStage_at_record rate rewards C_star C_h control0
            (K.get a).input.time i z (K.get a) installed.registers.payload
            (cut.input.time.val + 1) hr (by rw [htime]; exact hp)
          simpa only [htime] using hstage

end Bandits.Support.ReferenceFirstReplacementCollectionPredictableStages

end
