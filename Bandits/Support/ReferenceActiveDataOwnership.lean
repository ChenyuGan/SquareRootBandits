/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceActivePhysicalHorizon
public import Bandits.Support.ActualInitializationLaunchState

/-!
# Actual local DATA ownership geometry

Sources: `sources/zip4/manuscript/05_binary_transport.tex:64-88,94-124,354-363,396-409`
and `sources/zip4/manuscript/06_interruptions.tex:246-260,270-295`.

The induction datum here is only occupied-register agreement with the current
payload. The DATA geometry additionally requires actual ordinary preparations
for every follower and an actual successful coordinator selection. Dagger has
no register assertion and cannot establish those ordinary branch equations.
No global absence of failure, assignment-replacement invariant, queue/score
history equality, probability law, or manuscript closure is asserted.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ReferenceActiveDataOwnership

open ConstructorDimensions
open ActiveRoundActions PublicDiscreteDraws

local instance propDecidable (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition

variable {p : Parameters} {rate : ReferenceActivePhysicalStep.RateInput p}

/-- Literal per-follower register agreement. Unoccupied and dagger branches
assert no occupied field; this predicate alone says nothing about actions. -/
def occupiedFields (P : ReferenceActivePhysicalStep.Payload rate) (i : Fin (p.m - 1))
    (configuration : DeclaredFollowerLocalRound.LocalConfiguration p rate) : Prop :=
  match configuration with
  | .ordinary s _ => s.status ≠ .unoccupied → s.lastDown = some (P.downRecord i)
  | .dagger => True

/-- The same field datum on the original carried configurations. -/
def carriedOccupiedFields (P : ReferenceActivePhysicalStep.Payload rate) (state : ReferenceActivePhysicalStep.State p rate) : Prop :=
  ∀ i, occupiedFields P i (state.followers i)

/-- The actual choice statuses, with the actual dispatched pending set.
The states are supplied together with ordinary-preparation equations at uses. -/
def choiceSnapshot {x : ReferenceActivePhysicalStep.RoundInput p rate} (selected : ReferenceActivePhysicalStep.Selection x)
    (states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta) :
    Snapshot selected.view.payload.assignment :=
  { missing := selected.started.pending, status := fun i => (states i).status }

/-- A successful StartRound only retains the status or interrupts to unoccupied. -/
theorem startRound_status (t : Fin p.T)
    (s out : ReferencePrelaunchFollower.State p rate.eta)
    (memory nextMemory : ActiveFollowerLifecycle.LocalMemory p)
    (h : ActiveFollowerLifecycle.startRound rate.eta t s memory = .ok (out, nextMemory)) :
    out.status = .unoccupied ∨ out.status = s.status := by
  unfold ActiveFollowerLifecycle.startRound at h
  cases hd : ActiveFollowerLifecycle.interruptionDecision rate.eta t s memory with
  | error reason => simp [hd] at h
  | ok interrupted =>
      simp only [hd] at h
      rcases h with ⟨rfl, _⟩
      cases interrupted <;> simp

/-- The ordinary output of PREPARE exposes the successful local choice and
the original successful StartRound, including its original input state. -/
theorem prepare_ordinary_choice (i : Fin (p.m - 1))
    (row : CompletePublicTable.CompleteRow p)
    (activation : ReferencePrelaunchFollower.Activation p) (t : Fin p.T)
    (active : activation.val ≤ t.val + 1) (input : DeclaredFollowerLocalRound.LocalConfiguration p rate)
    (s : ReferencePrelaunchFollower.State p rate.eta) (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hordinary : (DeclaredFollowerLocalRound.prepare rate i row activation t active input).configuration =
      .ordinary s memory) :
    ∃ before beforeMemory offered,
      input = .ordinary before beforeMemory ∧
      ActiveFollowerLifecycle.startRound rate.eta t before beforeMemory = .ok (s, memory) ∧
      ActiveFollowerArmChoice.followerArmChoice s row t i offered =
        some (DeclaredFollowerLocalRound.prepare rate i row activation t active input).arm := by
  cases input with
  | dagger => simp [DeclaredFollowerLocalRound.prepare] at hordinary
  | ordinary before beforeMemory =>
      cases hs : ActiveFollowerLifecycle.startRound rate.eta t before beforeMemory with
      | error reason => simp [DeclaredFollowerLocalRound.prepare, hs] at hordinary
      | ok pair =>
          rcases pair with ⟨choice, choiceMemory⟩
          cases ho : ActiveFollowerQueueOperation.checkedUpOffer rate.eta i row activation t choice with
          | failure => simp [DeclaredFollowerLocalRound.prepare, hs, ho] at hordinary
          | noOffer =>
              cases hc : ActiveFollowerArmChoice.followerArmChoice choice row t i none with
              | none => simp [DeclaredFollowerLocalRound.prepare, hs, ho, hc] at hordinary
              | some arm =>
                  simp only [DeclaredFollowerLocalRound.prepare, hs, ho, hc, DeclaredFollowerLocalRound.LocalConfiguration.ordinary.injEq]
                    at hordinary
                  rcases hordinary with ⟨rfl, rfl⟩
                  exact ⟨before, beforeMemory, none, rfl, hs, by
                    simp only [DeclaredFollowerLocalRound.prepare, hs, ho, hc]⟩
          | offer offered =>
              cases hc : ActiveFollowerArmChoice.followerArmChoice choice row t i
                  (some offered) with
              | none => simp [DeclaredFollowerLocalRound.prepare, hs, ho, hc] at hordinary
              | some arm =>
                  simp only [DeclaredFollowerLocalRound.prepare, hs, ho, hc, DeclaredFollowerLocalRound.LocalConfiguration.ordinary.injEq]
                    at hordinary
                  rcases hordinary with ⟨rfl, rfl⟩
                  exact ⟨before, beforeMemory, some offered, rfl, hs, by
                    simp only [DeclaredFollowerLocalRound.prepare, hs, ho, hc]⟩

/-- PREPARE preserves occupied-field agreement, including its dagger failures.
It does not infer a successful branch from field agreement. -/
theorem choice_occupied_fields_preserved (P : ReferenceActivePhysicalStep.Payload rate) (i : Fin (p.m - 1))
    (row : CompletePublicTable.CompleteRow p)
    (activation : ReferencePrelaunchFollower.Activation p) (t : Fin p.T)
    (active : activation.val ≤ t.val + 1) (input : DeclaredFollowerLocalRound.LocalConfiguration p rate)
    (hfields : occupiedFields P i input) :
    occupiedFields P i (DeclaredFollowerLocalRound.prepare rate i row activation t active input).configuration := by
  cases hconfig : (DeclaredFollowerLocalRound.prepare rate i row activation t active input).configuration with
  | dagger => trivial
  | ordinary s memory =>
      obtain ⟨before, beforeMemory, offered, hinput, hstart, _⟩ :=
        prepare_ordinary_choice i row activation t active input s memory hconfig
      intro hoccupied
      have hbefore : before.status ≠ .unoccupied := by
        intro hu
        rcases startRound_status t before s beforeMemory memory hstart with h | h
        · exact hoccupied h
        · exact hoccupied (h.trans hu)
      rw [hinput] at hfields
      exact (ActiveFollowerLifecycle.startRound_frame rate.eta t before s beforeMemory memory hstart).1.trans
        (hfields hbefore)

/-- An ordinary choice after an unoccupied carried state is still unoccupied.
Failure branches are not removed by this assertion. -/
theorem first_choice_unoccupied (i : Fin (p.m - 1))
    (row : CompletePublicTable.CompleteRow p)
    (activation : ReferencePrelaunchFollower.Activation p) (t : Fin p.T)
    (active : activation.val ≤ t.val + 1)
    (before s : ReferencePrelaunchFollower.State p rate.eta)
    (beforeMemory memory : ActiveFollowerLifecycle.LocalMemory p)
    (hunoccupied : before.status = .unoccupied)
    (hordinary : (DeclaredFollowerLocalRound.prepare rate i row activation t active
      (.ordinary before beforeMemory)).configuration = .ordinary s memory) :
    s.status = .unoccupied := by
  obtain ⟨initial, initialMemory, _, hinput, hstart, _⟩ :=
    prepare_ordinary_choice i row activation t active (.ordinary before beforeMemory)
      s memory hordinary
  cases hinput
  exact (startRound_status t before s beforeMemory memory hstart).elim id
    (fun h => h.trans hunoccupied)

/-- First choice agreement is vacuous for every payload, including the payload
actually installed by the coordinator's first chosen branch. -/
theorem first_choice_occupied_fields (P : ReferenceActivePhysicalStep.Payload rate) (i : Fin (p.m - 1))
    (row : CompletePublicTable.CompleteRow p)
    (activation : ReferencePrelaunchFollower.Activation p) (t : Fin p.T)
    (active : activation.val ≤ t.val + 1)
    (before : ReferencePrelaunchFollower.State p rate.eta) (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hunoccupied : before.status = .unoccupied) :
    occupiedFields P i (DeclaredFollowerLocalRound.prepare rate i row activation t active
      (.ordinary before memory)).configuration := by
  apply choice_occupied_fields_preserved
  intro h
  exact False.elim (h hunoccupied)

/-- The encoded payload arm converts back to the original assigned arm. -/
theorem downRecord_arm (P : ReferenceActivePhysicalStep.Payload rate) (i : Fin (p.m - 1)) :
    PrelaunchBufferRecovery.downArm rate.eta (P.downRecord i) = P.assignment.assigned i := by
  apply Fin.ext
  have h := PrelaunchBufferRecovery.down_arm_one_based rate.eta (P.downRecord i)
  change _ = (P.assignment.assigned i).val + 1 at h
  omega

/-- DATA arm computation on an actual ordinary preparation. No action-profile
equation is supplied: it is derived from the accepted local choice. -/
theorem ordinary_data_arm (P : ReferenceActivePhysicalStep.Payload rate) (i : Fin (p.m - 1))
    (row : CompletePublicTable.CompleteRow p)
    (activation : ReferencePrelaunchFollower.Activation p) (t : Fin p.T)
    (active : activation.val ≤ t.val + 1) (input : DeclaredFollowerLocalRound.LocalConfiguration p rate)
    (s : ReferencePrelaunchFollower.State p rate.eta) (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hordinary : (DeclaredFollowerLocalRound.prepare rate i row activation t active input).configuration =
      .ordinary s memory)
    (hfields : s.status ≠ .unoccupied → s.lastDown = some (P.downRecord i))
    (hdata : slotDraw (row.2 t).1 = dataSlot) :
    (DeclaredFollowerLocalRound.prepare rate i row activation t active input).arm =
      if s.status = .unoccupied then
        pilotDraw (K_pos p) (followerPlayer p.two_le_m i) (row.2 t).1
      else P.assignment.assigned i := by
  obtain ⟨_, _, offered, _, _, hchoice⟩ :=
    prepare_ordinary_choice i row activation t active input s memory hordinary
  by_cases hu : s.status = .unoccupied
  · rw [ite_eq_left hu]
    exact Option.some.inj (hchoice.symm.trans
      (ActiveFollowerArmChoice.followerArmChoiceCore_unoccupied_data s (row.2 t)
        i offered hu hdata))
  · rw [ite_eq_right hu]
    have hc : ActiveFollowerArmChoice.followerArmChoice s row t i offered =
        some (P.assignment.assigned i) := by
      simp only [ActiveFollowerArmChoice.followerArmChoice,
        ActiveFollowerArmChoice.followerArmChoiceCore, hu, ite_false, hfields hu,
        hdata, or_true, ite_true]
      rw [downRecord_arm]
    exact Option.some.inj (hchoice.symm.trans hc)

/-- The actual selected coordinator arm on DATA either is its pilot or lies
outside the entire assigned image. The fast subtype supplies the latter fact. -/
theorem selected_data_coordinator {x : ReferenceActivePhysicalStep.RoundInput p rate} (selected : ReferenceActivePhysicalStep.Selection x)
    (hlive : CoordinatorLocalArmChoice.assignmentIsLive selected.view.payload selected.view.cutoff x.time)
    (hdata : slotDraw (x.row.2 x.time).1 = dataSlot) :
    (selected.started.pending ≠ ∅ → selected.arm =
      pilotDraw (K_pos p) (coordinator p.two_le_m) (x.row.2 x.time).1) ∧
    (selected.started.pending = ∅ →
      selected.arm ∉ Finset.univ.image selected.view.payload.assignment.assigned) := by
  have hv : CoordinatorLocalArmChoice.ChoiceInputsValid selected.view.payload selected.view.cutoff x.time
      selected.view.complementWeights := by
    by_contra hn
    exact selected.choice_ne_none
      (CoordinatorLocalArmChoice.coordinatorArmChoiceCore_none_of_invalid _ _ _ _ _ _ hn)
  constructor
  · intro hmissing
    have hn : ¬ (CoordinatorLocalArmChoice.assignmentIsLive selected.view.payload selected.view.cutoff x.time ∧
        selected.view.pendingAtChoice = ∅) := by
      rintro ⟨_, he⟩
      exact hmissing (selected.pending_eq.symm.trans he)
    exact Option.some.inj (selected.choice_eq.symm.trans
      (CoordinatorLocalArmChoice.coordinatorArmChoiceCore_data _ _ _ _ _ _ hv hn hdata))
  · intro hempty
    have he : selected.view.pendingAtChoice = ∅ := selected.pending_eq.trans hempty
    have hc := Option.some.inj (selected.choice_eq.symm.trans
      (CoordinatorLocalArmChoice.coordinatorArmChoiceCore_live_empty _ _ _ _ _ _ hv hlive he))
    rw [hc, selected.view.payload.assignment_image]
    exact (Finset.mem_sdiff.mp (CoordinatorLocalArmChoice.localFastDraw _ _ _ _ hv (x.row.2 x.time)).property).2

/-- Physical DATA geometry for any owner. Every ordinary choice configuration
is an explicit equation on the actual preparation; the sole field input is
occupied `lastDown` agreement with this selected payload. -/
theorem actual_data_owner_collisionFree (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (selected : ReferenceActivePhysicalStep.Selection x)
    (hselected : (ReferenceActivePhysicalStep.prepare x).coordinator.selection = some selected)
    (states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
    (memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p)
    (hordinary : ∀ i, ((ReferenceActivePhysicalStep.prepare x).followers.followers i).configuration =
      .ordinary (states i) (memories i))
    (hfields : ∀ i, (states i).status ≠ .unoccupied →
      (states i).lastDown = some (selected.view.payload.downRecord i))
    (hlive : CoordinatorLocalArmChoice.assignmentIsLive selected.view.payload selected.view.cutoff x.time)
    (hdata : slotDraw (x.row.2 x.time).1 = dataSlot)
    (owner : Fin p.m) (j : Fin p.K)
    (haction : (ReferenceActivePhysicalStep.prepare x).arms.actions owner = j)
    (howns : SnapshotRecordingKernel.owns p
      (.live selected.view.payload.assignment (choiceSnapshot selected states)) owner j)
    (hmask : CanonicalRecordingSlice.recordingMask (K_pos p) owner j
      (x.row.2 x.time).1) :
    FiniteBanditModel.collisionFreeFor (ReferenceActivePhysicalStep.prepare x).arms.actions owner := by
  have hc : (ReferenceActivePhysicalStep.prepare x).arms.actions (coordinator p.two_le_m) = selected.arm := by
    rw [ReferenceActivePhysicalStep.PreparedRound.action_coordinator, ReferenceActivePhysicalStep.DispatchCut.arm, hselected]
  have hf (i : Fin (p.m - 1)) :
      (ReferenceActivePhysicalStep.prepare x).arms.actions (followerPlayer p.two_le_m i) =
        if (states i).status = .unoccupied then
          pilotDraw (K_pos p) (followerPlayer p.two_le_m i) (x.row.2 x.time).1
        else selected.view.payload.assignment.assigned i := by
    rw [ReferenceActivePhysicalStep.PreparedRound.action_follower]
    exact ordinary_data_arm _ i x.row (x.state.activations i) x.time (x.active i)
      (x.state.followers i) (states i) (memories i) (hordinary i) (hfields i) hdata
  intro other hne hsame
  have hother : (ReferenceActivePhysicalStep.prepare x).arms.actions other = j := hsame.trans haction
  by_cases ho : other = coordinator p.two_le_m
  · subst other
    have howner : owner ≠ coordinator p.two_le_m := Ne.symm hne
    have hj : j = selected.view.payload.assignment.assigned
        (followerIndex p.two_le_m owner howner) := by
      simpa only [SnapshotRecordingKernel.owns, dite_eq_right howner] using howns
    rcases selected_data_coordinator selected hlive hdata with ⟨hpilot, houtside⟩
    by_cases hempty : selected.started.pending = ∅
    · exact houtside hempty (Finset.mem_image.mpr
        ⟨_, Finset.mem_univ _, hj.symm.trans (hc.symm.trans hother).symm⟩)
    · exact hmask _ hne ((hpilot hempty).symm.trans (hc.symm.trans hother))
  · let i := followerIndex p.two_le_m other ho
    have hi : followerPlayer p.two_le_m i = other :=
      followerPlayer_followerIndex p.two_le_m other ho
    rw [← hi] at hother
    rw [hf i] at hother
    by_cases hu : (states i).status = .unoccupied
    · exact hmask _ (hi ▸ hne) (by simpa only [ite_eq_left hu] using hother)
    · have hj : selected.view.payload.assignment.assigned i = j := by
        simpa only [ite_eq_right hu] using hother
      by_cases howner : owner = coordinator p.two_le_m
      · have houtside : j ∉ Finset.univ.image selected.view.payload.assignment.assigned := by
          simpa only [SnapshotRecordingKernel.owns, dite_eq_left howner] using howns
        exact houtside (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hj⟩)
      · have hownj : j = selected.view.payload.assignment.assigned
            (followerIndex p.two_le_m owner howner) := by
          simpa only [SnapshotRecordingKernel.owns, dite_eq_right howner] using howns
        have heq := selected.view.payload.assignment.injective (hj.trans hownj)
        apply hne
        rw [← hi, heq]
        exact followerPlayer_followerIndex p.two_le_m owner howner

/-- The owner's grid feedback and numerical typed observation equal the
entire reward table's selected entry. Zero rewards need no special case. -/
theorem actual_data_owner_feedback (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (selected : ReferenceActivePhysicalStep.Selection x)
    (hselected : (ReferenceActivePhysicalStep.prepare x).coordinator.selection = some selected)
    (states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
    (memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p)
    (hordinary : ∀ i, ((ReferenceActivePhysicalStep.prepare x).followers.followers i).configuration =
      .ordinary (states i) (memories i))
    (hfields : ∀ i, (states i).status ≠ .unoccupied →
      (states i).lastDown = some (selected.view.payload.downRecord i))
    (hlive : CoordinatorLocalArmChoice.assignmentIsLive selected.view.payload selected.view.cutoff x.time)
    (hdata : slotDraw (x.row.2 x.time).1 = dataSlot)
    (owner : Fin p.m) (j : Fin p.K)
    (haction : (ReferenceActivePhysicalStep.prepare x).arms.actions owner = j)
    (howns : SnapshotRecordingKernel.owns p
      (.live selected.view.payload.assignment (choiceSnapshot selected states)) owner j)
    (hmask : CanonicalRecordingSlice.recordingMask (K_pos p) owner j
      (x.row.2 x.time).1) :
    (ReferenceActivePhysicalStep.prepare x).feedback.feedback owner = x.rewards x.time j ∧
    ((ReferenceActivePhysicalStep.prepare x).feedback.observations owner).val.val =
      ((x.rewards x.time j).val : ℝ) / (D p : ℝ) := by
  have hfree := actual_data_owner_collisionFree x selected hselected states memories
    hordinary hfields hlive hdata owner j haction howns hmask
  have hfeedback : (ReferenceActivePhysicalStep.prepare x).feedback.feedback owner = x.rewards x.time j := by
    rw [ReferenceActivePhysicalStep.PreparedRound.feedback_rule, ite_eq_left hfree, haction]
  exact ⟨hfeedback, by rw [ReferenceActiveFeedbackCut.FeedbackCut.observation_grid_value,
    hfeedback]⟩

/-- Parsing a present expected word returns this current payload's exact
record. No constancy of earlier sender payloads is required. -/
theorem parse_expectedDown (view : ReferenceDownReception.ChoiceTimeView p rate.eta)
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p) (t : Fin p.T)
    (M : OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (hparse : ReferenceDownReception.ordinaryParse p rate
      (ReferenceDownReception.expectedDownFlatWord (some view) i row t) = some M) :
    M = view.payload.downRecord i := by
  simp only [ReferenceDownReception.expectedDownFlatWord] at hparse
  split at hparse
  · change OrdinaryMessageCodec.parseDown (ReferencePrelaunchFollower.codecParams p rate.eta)
      (some ((OrdinaryMessageCodec.wordEquivFlat
        (ReferencePrelaunchFollower.codecParams p rate.eta)).symm
          ((OrdinaryMessageCodec.wordEquivFlat
            (ReferencePrelaunchFollower.codecParams p rate.eta)) (view.payload.downWord i)))) =
        some M at hparse
    rw [Equiv.symm_apply_apply, view.payload.parseDown_downWord i] at hparse
    exact (Option.some.inj hparse).symm
  · change (none : Option (OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))) = some M at hparse
    cases hparse

/-- The pre-effect filter permits an accepted ordinary output only with the
current expected record. The conclusion also identifies the actual installed
register; it assumes only the computed accepted-constructor equation. -/
theorem referenceDown_accepted_fields
    (view : ReferenceDownReception.ChoiceTimeView p rate.eta)
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p) (t : Fin p.T)
    (observation : ReferencePrelaunchFollower.Observation p)
    (state before after : ReferencePrelaunchFollower.State p rate.eta)
    (raw : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p)))
    (M : OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (scan : FollowerCutoffScan.ScanResult p.T) (registers : ℕ × ℕ) (lastService : ℕ)
    (haccepted : (ReferenceDownReception.referenceDownCut p (some view) i row t
      observation rate state).outcome =
        .accepted before after raw M scan registers lastService) :
    M = view.payload.downRecord i ∧ after.lastDown = some (view.payload.downRecord i) := by
  simp only [ReferenceDownReception.referenceDownCut] at haccepted
  split at haccepted
  · split at haccepted
    · split at haccepted
      · split at haccepted
        · split at haccepted
          · split at haccepted
            · rename_i hmatches
              dsimp only at haccepted
              split at haccepted
              · cases haccepted
              · rename_i parsed hparse
                have hrecord : parsed = view.payload.downRecord i :=
                  parse_expectedDown view i row t parsed (hmatches ▸ hparse)
                split at haccepted
                · split at haccepted
                  · cases haccepted
                  · cases haccepted
                    exact ⟨hrecord, congrArg some hrecord⟩
                · cases haccepted
            · cases haccepted
          · cases haccepted
        · cases haccepted
      · cases haccepted
    · cases haccepted
  · cases haccepted

/-- All successful reference-DOWN branches preserve occupied-field agreement.
Rejection retains the old fields; acceptance installs the authenticated current
record. Input/output failures remain errors. -/
theorem referenceDown_occupied_fields
    (view : ReferenceDownReception.ChoiceTimeView p rate.eta)
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p) (t : Fin p.T)
    (observation : ReferencePrelaunchFollower.Observation p)
    (state out : ReferencePrelaunchFollower.State p rate.eta)
    (hfields : state.status ≠ .unoccupied → state.lastDown = some (view.payload.downRecord i))
    (hresult : DeclaredFollowerLocalRound.consumeDownResult rate
      (ReferenceDownReception.referenceDownCut p (some view) i row t observation rate state).outcome =
        .ok out) :
    out.status ≠ .unoccupied → out.lastDown = some (view.payload.downRecord i) := by
  simp only [ReferenceDownReception.referenceDownCut] at hresult
  split at hresult
  · split at hresult
    · split at hresult
      · split at hresult
        · split at hresult
          · split at hresult
            · rename_i hmatches
              split at hresult
              · cases hresult; exact hfields
              · rename_i parsed hparse
                have hrecord := parse_expectedDown view i row t parsed (hmatches ▸ hparse)
                split at hresult
                · split at hresult
                  · cases hresult
                  · cases hresult
                    intro _
                    exact congrArg some hrecord
                · cases hresult; exact hfields
            · cases hresult; exact hfields
          · cases hresult
        · cases hresult
      · cases hresult
    · cases hresult; exact hfields
  · cases hresult; exact hfields

/-- The lastDown field is framed by every successful release operation,
including a failed release test. -/
theorem release_lastDown (i : Fin (p.m - 1)) (t : Fin p.T)
    (row : ActiveFollowerLifecycle.FollowerPublicRow p.m p.K)
    (observation : ReferencePrelaunchFollower.Observation p)
    (before post out : ReferencePrelaunchFollower.State p rate.eta)
    (h : ActiveFollowerLifecycle.releaseAfterService rate.eta i t row observation
      before post = .ok out) : out.lastDown = post.lastDown := by
  simp only [ActiveFollowerLifecycle.releaseAfterService] at h
  split at h
  · split at h
    · split at h
      · cases h
      · split at h
        · split at h
          · split at h
            · split at h
              · cases h; rfl
              · cases h
            · split at h
              · cases h; rfl
              · cases h
          · cases h
        · cases h
    · cases h
  · exact congrArg ReferencePrelaunchFollower.State.lastDown (Except.ok.inj h).symm

/-- Successful release/finish frames lastDown. When choice was unoccupied,
release cannot change the post-record status, either. -/
theorem releaseAndFinish_fields (i : Fin (p.m - 1))
    (row : CompletePublicTable.CompleteRow p) (t : Fin p.T)
    (observation : ReferencePrelaunchFollower.Observation p)
    (before post out : ReferencePrelaunchFollower.State p rate.eta)
    (memory nextMemory : ActiveFollowerLifecycle.LocalMemory p)
    (h : DeclaredFollowerLocalRound.releaseAndFinish rate i row t observation before
      memory post = .ok (out, nextMemory)) :
    out.lastDown = post.lastDown ∧
      (before.status = .unoccupied → out.status = post.status) := by
  unfold DeclaredFollowerLocalRound.releaseAndFinish at h
  cases hr : ActiveFollowerLifecycle.releaseAfterService rate.eta i t
      (ActiveFollowerLifecycle.publicRowOfCompleteRow row t) observation before post with
  | error reason => simp only [hr] at h; cases h
  | ok released =>
      rw [hr] at h
      cases hf : ActiveFollowerLifecycle.finishRound rate.eta t row released memory with
      | error reason => simp only [hf] at h; cases h
      | ok pair =>
          rcases pair with ⟨finished, finishedMemory⟩
          simp only [hf, Except.ok.injEq, Prod.mk.injEq] at h
          rcases h with ⟨hstate, hmemory⟩
          subst finished
          subst finishedMemory
          have heq := ActiveFollowerLifecycle.finishRound_frame rate.eta t row
            released out memory nextMemory hf
          subst out
          refine ⟨release_lastDown i t _ observation before post released hr, ?_⟩
          intro hu
          have hn : before.status ≠ .pending := by rw [hu]; decide
          have hr' := ActiveFollowerLifecycle.releaseAfterService_not_pending rate.eta
            i t (ActiveFollowerLifecycle.publicRowOfCompleteRow row t) observation before post hn
          rw [hr'] at hr
          cases hr
          rfl

/-- The actual record/service operation produces the field datum, and on
occupied choices frames the entire accepted record. Every error is retained. -/
theorem recordFollower_occupied_fields
    (view : ReferenceDownReception.ChoiceTimeView p rate.eta)
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (activation : ReferencePrelaunchFollower.Activation p) (t : Fin p.T)
    (active : activation.val ≤ t.val + 1) (arm : Fin p.K)
    (observation : ReferencePrelaunchFollower.Observation p)
    (state out : ReferencePrelaunchFollower.State p rate.eta)
    (hfields : state.status ≠ .unoccupied → state.lastDown = some (view.payload.downRecord i))
    (hrecord : (ReferenceActivePhysicalStep.recordFollower (some view) i row activation t
      active arm observation state).result = .ok out) :
    (out.status ≠ .unoccupied → out.lastDown = some (view.payload.downRecord i)) ∧
      (state.status ≠ .unoccupied → out.lastDown = state.lastDown) := by
  unfold ReferenceActivePhysicalStep.recordFollower at hrecord
  by_cases hu : state.status = .unoccupied
  · rw [dite_eq_left hu] at hrecord
    cases hl : ActiveFollowerLogging.checkedLogging i row activation t
        (arm, observation) state with
    | error reason => simp only [hl] at hrecord; cases hrecord
    | ok logged =>
        simp only [hl] at hrecord
        have hframe := ActiveFollowerLogging.checkedLogging_success_frame i row activation
          t (arm, observation) state logged hl
        have hg : logged.status ≠ .unoccupied →
            logged.lastDown = some (view.payload.downRecord i) := by
          intro hn
          exact False.elim (hn (hframe.2.2.2.2.1.trans hu))
        have hdown := referenceDown_occupied_fields view i row t observation logged out hg hrecord
        exact ⟨hdown, fun hn => False.elim (hn hu)⟩
  · rw [dite_eq_right hu] at hrecord
    simp only [DeclaredFollowerLocalRound.recordOrServiceThenDown, dite_eq_right hu] at hrecord
    cases hs : ActiveFollowerQueueOperation.checkedService rate.eta rate.sourceCap rate.n
        rate.n_scale i row activation t observation state with
    | failure => simp only [hs] at hrecord; cases hrecord
    | success result =>
        simp only [hs, Except.ok.injEq] at hrecord
        subst out
        have hf : result.output.lastDown = state.lastDown := by
          rw [result.queueUpdate]
          exact (ActiveFollowerQueueOperation.serviceOutput_preserves_other_registers
            rate.n state result.arrival).1
        exact ⟨fun _ => hf.trans (hfields hu), fun _ => hf⟩

/-- Preservation through the actual reference follower tail for the SAME
payload. Failure remains dagger and contributes no field assertion. -/
theorem finishFollower_occupied_fields
    (view : ReferenceDownReception.ChoiceTimeView p rate.eta)
    (prepared : DeclaredFollowerLocalRound.PreparedRound p rate)
    (observation : ReferencePrelaunchFollower.Observation p)
    (hfields : occupiedFields view.payload prepared.follower prepared.configuration) :
    occupiedFields view.payload prepared.follower
      (ReferenceActivePhysicalStep.finishFollower (some view) prepared observation).configuration := by
  unfold ReferenceActivePhysicalStep.finishFollower
  cases hc : prepared.configuration with
  | dagger => trivial
  | ordinary state memory =>
      rw [hc] at hfields
      dsimp only
      cases hr : (ReferenceActivePhysicalStep.recordFollower (some view) prepared.follower
          prepared.row prepared.activation prepared.time prepared.active prepared.arm observation
          state).result with
      | error reason => trivial
      | ok post =>
          dsimp only
          cases hf : DeclaredFollowerLocalRound.releaseAndFinish rate prepared.follower
              prepared.row prepared.time observation state memory post with
          | error reason => trivial
          | ok pair =>
              rcases pair with ⟨out, nextMemory⟩
              dsimp only
              have hp := recordFollower_occupied_fields view prepared.follower prepared.row
                prepared.activation prepared.time prepared.active prepared.arm observation state
                post hfields hr
              have hfinish := releaseAndFinish_fields prepared.follower prepared.row prepared.time
                observation state post out memory nextMemory hf
              intro hoccupied
              rw [hfinish.1]
              by_cases hu : state.status = .unoccupied
              · exact hp.1 (fun h => hoccupied ((hfinish.2 hu).trans h))
              · exact (hp.2 hu).trans (hfields hu)

/-- Same-payload preservation in the literal physical step. The coordinator's
next payload is not asserted to be this payload: replacement is a separate
physical phase/barrier obligation. -/
theorem step_occupied_fields (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (selected : ReferenceActivePhysicalStep.Selection x)
    (hselected : (ReferenceActivePhysicalStep.prepare x).coordinator.selection = some selected)
    (hfields : carriedOccupiedFields selected.view.payload x.state) :
    carriedOccupiedFields selected.view.payload (ReferenceActivePhysicalStep.step x).next := by
  intro i
  rw [(ReferenceActivePhysicalStep.step_next_fields x).2.2.2 i]
  unfold ReferenceActivePhysicalStep.PreparedRound.observeFollower
  have hv : (ReferenceActivePhysicalStep.prepare x).coordinator.downView = some selected.view := by
    simp only [ReferenceActivePhysicalStep.DispatchCut.downView, hselected, Option.map_some]
  rw [hv]
  have hi := ((ReferenceActivePhysicalStep.prepare x).follower_alignment i).2.1
  have hp : occupiedFields selected.view.payload
      ((ReferenceActivePhysicalStep.prepare x).followers.followers i).follower
      ((ReferenceActivePhysicalStep.prepare x).followers.followers i).configuration := by
    rw [hi]
    exact choice_occupied_fields_preserved selected.view.payload i x.row
      (x.state.activations i) x.time (x.active i) (x.state.followers i) (hfields i)
  have hout := finishFollower_occupied_fields selected.view
    ((ReferenceActivePhysicalStep.prepare x).followers.followers i)
    ((ReferenceActivePhysicalStep.prepare x).feedback.observations
      (followerPlayer p.two_le_m i)) hp
  rw [hi] at hout
  exact hout

/-- The typed follower floor can use the reward entry after the actual local
geometry proof. There is no positivity test or gate/amount conflation. -/
theorem actual_follower_sourceArrivalFloor (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (selected : ReferenceActivePhysicalStep.Selection x)
    (hselected : (ReferenceActivePhysicalStep.prepare x).coordinator.selection = some selected)
    (states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
    (memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p)
    (hordinary : ∀ i, ((ReferenceActivePhysicalStep.prepare x).followers.followers i).configuration =
      .ordinary (states i) (memories i))
    (hfields : ∀ i, (states i).status ≠ .unoccupied →
      (states i).lastDown = some (selected.view.payload.downRecord i))
    (hlive : CoordinatorLocalArmChoice.assignmentIsLive selected.view.payload selected.view.cutoff x.time)
    (hdata : slotDraw (x.row.2 x.time).1 = dataSlot) (i : Fin (p.m - 1))
    (haction : (ReferenceActivePhysicalStep.prepare x).arms.actions (followerPlayer p.two_le_m i) =
      selected.view.payload.assignment.assigned i)
    (hmask : CanonicalRecordingSlice.recordingMask (K_pos p) (followerPlayer p.two_le_m i)
      (selected.view.payload.assignment.assigned i) (x.row.2 x.time).1) :
    ActiveFollowerQueueOperation.sourceArrivalFloor rate.eta (selected.view.payload.downRecord i)
      ((ReferenceActivePhysicalStep.prepare x).feedback.observations (followerPlayer p.two_le_m i)) =
    Nat.floor ((D p : ℝ) * rate.eta.val *
      (((x.rewards x.time (selected.view.payload.assignment.assigned i)).val : ℝ) / (D p : ℝ)) /
      OrdinaryMessageCodec.dyadicRate (selected.view.payload.downRecord i).val.h) := by
  have hne := followerPlayer_ne_coordinator p.two_le_m i
  have howns : SnapshotRecordingKernel.owns p
      (.live selected.view.payload.assignment (choiceSnapshot selected states))
      (followerPlayer p.two_le_m i) (selected.view.payload.assignment.assigned i) := by
    simp only [SnapshotRecordingKernel.owns, dite_eq_right hne,
      followerIndex_followerPlayer p.two_le_m i hne]
  have hfeedback := actual_data_owner_feedback x selected hselected states memories hordinary
    hfields hlive hdata (followerPlayer p.two_le_m i) _ haction howns hmask
  unfold ActiveFollowerQueueOperation.sourceArrivalFloor
  rw [hfeedback.2]

/-- A consumer on the ORIGINAL full-table finite horizon. Membership supplies
the original rewards, while `output_eq` supplies the literal step output.
No execution-wide branch or field invariant is assumed or concluded. -/
theorem run_record_owner_feedback (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hrecord : record ∈ (ReferenceActivePhysicalHorizon.run initial rows J rewards
      start count hspan hmode).records)
    (selected : ReferenceActivePhysicalStep.Selection record.input)
    (hselected : (ReferenceActivePhysicalStep.prepare record.input).coordinator.selection = some selected)
    (states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
    (memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p)
    (hordinary : ∀ i, ((ReferenceActivePhysicalStep.prepare record.input).followers.followers i).configuration =
      .ordinary (states i) (memories i))
    (hfields : ∀ i, (states i).status ≠ .unoccupied →
      (states i).lastDown = some (selected.view.payload.downRecord i))
    (hlive : CoordinatorLocalArmChoice.assignmentIsLive selected.view.payload selected.view.cutoff record.input.time)
    (hdata : slotDraw (record.input.row.2 record.input.time).1 = dataSlot)
    (owner : Fin p.m) (j : Fin p.K)
    (haction : (ReferenceActivePhysicalStep.prepare record.input).arms.actions owner = j)
    (howns : SnapshotRecordingKernel.owns p
      (.live selected.view.payload.assignment (choiceSnapshot selected states)) owner j)
    (hmask : CanonicalRecordingSlice.recordingMask (K_pos p) owner j
      (record.input.row.2 record.input.time).1) :
    record.gridFeedback owner = rewards record.input.time j ∧
      ReferenceActivePhysicalHorizon.observationValue (record.ownEntries owner).2 =
        ((rewards record.input.time j).val : ℝ) / (D p : ℝ) := by
  have hinput := ReferenceActivePhysicalHorizon.run_record_inputs initial rows J rewards
    start count hspan hmode record hrecord
  have hf := actual_data_owner_feedback record.input selected hselected states memories
    hordinary hfields hlive hdata owner j haction howns hmask
  have hentry : record.input.rewards record.input.time j = rewards record.input.time j :=
    congrArg (fun table : ActualInitializationPhysicalStep.GridRewardTable p =>
      table record.input.time j) hinput.2.2
  have hgrid := hf.1.trans hentry
  constructor
  · unfold ReferenceActivePhysicalHorizon.RoundRecord.gridFeedback
    rw [record.output_eq]
    exact hgrid
  · unfold ReferenceActivePhysicalHorizon.RoundRecord.ownEntries
      ReferenceActivePhysicalHorizon.observationValue
    rw [record.output_eq, ReferenceActivePhysicalStep.step_own_entry]
    change (ActualInitializationPhysicalStep.observationOfGrid p
      ((ReferenceActivePhysicalStep.prepare record.input).feedback.feedback owner)).val.val = _
    rw [ActualInitializationPhysicalStep.observationOfGrid_value, hgrid]

/-- All common carried domains hold for the source initialization's literal
ordinary state, including replay's full buffer and decoder batch. -/
theorem initialization_ordinary_domain (x : ReferenceInitializationRun.Input p)
    (b : ReferenceInitializationRun.Boundary p) (i : Follower p.m) :
    ActiveFollowerLifecycle.localStateDomainValid (ReferenceInitializationRun.ordinary x b i) := by
  have hinitial : ActiveFollowerLifecycle.localStateDomainValid
      (ReferencePrelaunchFollower.initial p x.eta) := by
    simp only [ActiveFollowerLifecycle.localStateDomainValid,
      ActiveFollowerLifecycle.serviceRegistersValid, ActiveFollowerLifecycle.localBufferValid,
      ActiveFollowerLifecycle.downDecoderStateValid, ReferencePrelaunchFollower.initial,
      AffineBatchDecoder.initial, List.map_nil, List.nodup_nil, List.length_nil,
      List.not_mem_nil, false_implies, implies_true, and_true, true_and, Nat.zero_le]
    exact AffineBatchDecoder.quota_pos p
  unfold ReferenceInitializationRun.ordinary
  split
  · exact hinitial
  · split
    · exact hinitial
    · exact ActualReferenceInitializationBlock.replay_domain_valid _ _ _ _ _ _

/-- Zero-field unoccupied initialization passes the actual local preparation
on every slot, with no checked success supplied as an assumption. -/
theorem prepare_initial_unoccupied (i : Fin (p.m - 1))
    (row : CompletePublicTable.CompleteRow p)
    (activation : ReferencePrelaunchFollower.Activation p) (t : Fin p.T)
    (active : activation.val ≤ t.val + 1)
    (state : ReferencePrelaunchFollower.State p rate.eta) (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hdomain : ActiveFollowerLifecycle.localStateDomainValid state)
    (hu : state.status = .unoccupied) (hs : ReferencePrelaunchFollower.acceptedStart state = 0)
    (hS : state.S = 0) (hd : state.delta = 0) (hb : state.backlog = 0) :
    (DeclaredFollowerLocalRound.prepare rate i row activation t active
      (.ordinary state memory)).configuration = .ordinary state memory := by
  have hstart := ActiveFollowerLifecycle.startRound_unoccupied rate.eta t state memory hdomain hu
  by_cases hdata : slotDraw (row.2 t).1 = dataSlot
  · have hnot : ¬ (ActiveFollowerQueueOperation.selectedUpRound i row activation t ∧
        state.status = .unoccupied) := by
      rintro ⟨⟨_, hup, _⟩, _⟩
      rw [hdata] at hup
      exact (by decide : dataSlot ≠ upSlot) hup
    have hoff := ActiveFollowerQueueOperation.checkedUpOffer_noOffer rate.eta i row
      activation t state (ActualReferenceInitializationBlock.up_domain_of_local_domain state hdomain) hnot
    have harm := ActiveFollowerArmChoice.followerArmChoiceCore_unoccupied_data state
      (row.2 t) i none hu hdata
    simp only [DeclaredFollowerLocalRound.prepare, hstart, hoff,
      ActiveFollowerArmChoice.followerArmChoice, harm]
  · by_cases hselected : slotDraw (row.2 t).1 = upSlot ∧
        selectedFollowerDraw p.two_le_m p.m_lt_K (row.2 t).1 = i
    · have hoff := ActualReferenceInitializationBlock.checked_up_zero rate.eta i row activation t
        state hdomain hu hs hS hd hb ⟨active, hselected⟩
      have hvalid : ActiveFollowerArmChoice.upStateDomain state ∧
          ActiveFollowerArmChoice.offeredUpMatchesState state
            (⟨OrdinaryMessageCodec.upPlaceholder, Or.inl rfl⟩ :
              OrdinaryMessageCodec.UpRecord (ReferencePrelaunchFollower.codecParams p rate.eta)) :=
        ⟨hdomain.1, hs.symm, hS.symm, hd.symm, hb.symm⟩
      have harm := ActiveFollowerArmChoice.followerArmChoiceCore_unoccupied_selected_up
        state (row.2 t) i ⟨OrdinaryMessageCodec.upPlaceholder, Or.inl rfl⟩ hu
        hselected.1 hselected.2 hvalid
      simp only [DeclaredFollowerLocalRound.prepare, hstart, hoff,
        ActiveFollowerArmChoice.followerArmChoice, harm]
    · have hnot : ¬ (ActiveFollowerQueueOperation.selectedUpRound i row activation t ∧
          state.status = .unoccupied) := fun h => hselected h.1.2
      have hoff := ActiveFollowerQueueOperation.checkedUpOffer_noOffer rate.eta i row
        activation t state (ActualReferenceInitializationBlock.up_domain_of_local_domain state hdomain) hnot
      have harm := ActiveFollowerArmChoice.followerArmChoiceCore_unoccupied_other
        state (row.2 t) i none hu hdata hselected
      simp only [DeclaredFollowerLocalRound.prepare, hstart, hoff,
        ActiveFollowerArmChoice.followerArmChoice, harm]

section ActualLaunch

variable
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (rate : ReferenceActivePhysicalStep.RateInput p) (C_star C_h : ℝ)
    (b : ReferenceInitializationRun.Boundary p)
    (h : b.completed < BootstrapDimensions.n_boot p)
    (actual : ActualInitializationRun.BlockCarry p rate (ReferenceInitializationRun.nextBlock b h))
    (past : List (ActualInitializationRun.PhysicalRoundRecord p rate source rewards))
    (hr : ActualReferenceInitializationBlock.BlockStartRelated source rewards
      C_star C_h rate (ReferenceInitializationRun.nextBlock b h) actual b past)
    (hdown : ∀ i, ¬ InitializationFailureProvenance.generatedBlockDown
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate) b h i)
    (hclean : ∀ (i : Fin (p.m - 1))
      (hi : ActualReferenceInitializationBlock.refFollower i ∈
        (ReferenceInitializationRun.physical
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate) b h).uninformed),
      BootstrapAllCandidateController.cleanPrefix
        (ReferenceInitializationRun.physical
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate) b h)
        source.1.2 ⟨ActualReferenceInitializationBlock.refFollower i, hi⟩
        (ActualInitializationPhysicalStep.selectedRowIndex p source) p.T)
    (hforce : ∀ i, ReferenceInitializationRun.forced
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate) b h i = false)
    (launch : BootstrapCoordinatorLocalRound.LaunchedBlock p)
    (learnerSeed : ActualInitializationRun.CoordinatorLearnerZeroSeed p)
    (hlaunched : (ActualInitializationRun.combinedBoundaryHandoff p rate
      (ReferenceInitializationRun.nextBlock b h) source rewards actual.C_star actual.C_h
      (ActualInitializationRun.foldBlock p rate (ReferenceInitializationRun.nextBlock b h)
        source rewards actual)).disposition = .launched launch learnerSeed)

/-- Actual-launch constructor: all followers are ordinary and unoccupied, and
their first PREPARE succeeds on every slot using their original carried fields.
All original launch hypotheses remain explicit in the section parameters. -/
theorem actual_launch_first_choice (i : Fin (p.m - 1))
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p)) (t : Fin p.T)
    (active : ((ActualInitializationLaunchState.ofActualLaunchedBoundary source rewards rate
      C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed hlaunched).activations i).val ≤
        t.val + 1) :
    ∃ state memory,
      (ActualInitializationLaunchState.ofActualLaunchedBoundary source rewards rate C_star C_h b h
        actual past hr hdown hclean hforce launch learnerSeed hlaunched).followers i = .ordinary state memory ∧
      state.status = .unoccupied ∧
      (DeclaredFollowerLocalRound.prepare rate i (rows J)
        ((ActualInitializationLaunchState.ofActualLaunchedBoundary source rewards rate C_star C_h b h
          actual past hr hdown hclean hforce launch learnerSeed hlaunched).activations i)
        t active (.ordinary state memory)).configuration = .ordinary state memory := by
  obtain ⟨state, memory, hconfig, hstate, _, hs, hS, hd, hb, hu, _⟩ :=
    ActualInitializationLaunchState.ofActualLaunchedBoundary_follower_replay source rewards rate
      C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed hlaunched i
  have hdomain : ActiveFollowerLifecycle.localStateDomainValid state := by
    rw [hstate]
    exact initialization_ordinary_domain _ _ _
  exact ⟨state, memory, hconfig, hu,
    prepare_initial_unoccupied i (rows J) _ t active state memory hdomain hu hs hS hd hb⟩

/-- The actual launch supplies the carried induction base for EVERY payload.
In particular the payload in the first actual successful selection is used
without choosing an alternative assignment. -/
theorem actual_launch_carried_fields (P : ReferenceActivePhysicalStep.Payload rate) :
    carriedOccupiedFields P
      (ActualInitializationLaunchState.ofActualLaunchedBoundary source rewards rate C_star C_h b h
        actual past hr hdown hclean hforce launch learnerSeed hlaunched) := by
  intro i
  obtain ⟨state, memory, hconfig, _, _, _, _, _, hu, _⟩ :=
    ActualInitializationLaunchState.ofActualLaunchedBoundary_follower_registers source rewards rate
      C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed hlaunched i
  rw [hconfig]
  intro hoccupied
  exact False.elim (hoccupied hu)

end ActualLaunch

end Bandits.Support.ReferenceActiveDataOwnership

end
