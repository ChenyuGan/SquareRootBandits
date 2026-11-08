/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceActivePhysicalHorizon
public import Bandits.Support.AdaptiveAffineBatchTail

/-!
# Current affine-coordinate perturbations of an actual physical round

Sources: `sources/zip4/manuscript/appendix_a_local_protocol.tex:112-137` and
`sources/zip4/manuscript/05_binary_transport.tex:7-42,74-124`.

These are internal deterministic results on the existing continuous row carrier.
The original selected row, entire reward table, state, forward arrays, and every
scalar label are retained. Executed-test projections retain tests before later
decoder, parser, recovery, or finishing failures. They assert neither a committed
bank update nor a conditional probability law on the generated private run.

The proved cut consists of full coordinate preservation, all follower
configuration comparisons, checked UP-word invariance, unaffected follower
actions, the complete DOWN enabling gate, and the collection recorder/receiver
prefix. The dispatcher choice-data comparison under changed affine coordinates
remains open. Consequently this module supplies no full physical Boolean-rule
factorization, bottom-test invariance, positive-current-hash implication, or
physical specialization of `AdaptiveAffineBatchTail.one_step_half`.

In `collectionRecording_replace_up`, payload, start result, and weights are
explicit fixed local selector inputs. Their invariance for the actual dispatcher
is part of the remaining comparison. The original continuous/private pre-pair
history, conditional fresh-pair law, reset/stopping history, and batch tail are
separate later producers. No manuscript result is certified by this module.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ReferenceActiveAffinePositiveTest

open ConstructorDimensions
open AffineChannelLaw

local instance propDecidable (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition


variable {p : Parameters} {rate : ReferenceActivePhysicalStep.RateInput p}

/-- Change only the selected row's current directed affine coordinate. -/
def replaceCurrentPair (x : ReferenceActivePhysicalStep.RoundInput p rate) (dir : Fin 2)
    (s : Sample (AffineBatchDecoder.width p)) : ReferenceActivePhysicalStep.RoundInput p rate :=
  { x with rows := (Function.update x.rows x.selected
      (x.row.1, Function.update x.row.2 x.time
        ((x.row.2 x.time).1,
          Function.update (x.row.2 x.time).2 (dir, ReferenceActivePhysicalStep.upSenderIndex x) s))) }

theorem replaceCurrentPair_fields (x : ReferenceActivePhysicalStep.RoundInput p rate) (dir : Fin 2)
    (s : Sample (AffineBatchDecoder.width p)) :
    (replaceCurrentPair x dir s).state = x.state ∧
    (replaceCurrentPair x dir s).selected = x.selected ∧
    (replaceCurrentPair x dir s).time = x.time ∧
    (replaceCurrentPair x dir s).rewards = x.rewards := ⟨rfl, rfl, rfl, rfl⟩

theorem replaceCurrentPair_row (x : ReferenceActivePhysicalStep.RoundInput p rate) (dir : Fin 2)
    (s : Sample (AffineBatchDecoder.width p)) :
    (replaceCurrentPair x dir s).row =
      (x.row.1, Function.update x.row.2 x.time
        ((x.row.2 x.time).1,
          Function.update (x.row.2 x.time).2 (dir, ReferenceActivePhysicalStep.upSenderIndex x) s)) := by
  simp only [ReferenceActivePhysicalStep.RoundInput.row, replaceCurrentPair, Function.update_self]

/-- Every forward array, including arrays in unselected rows, is preserved. -/
theorem replaceCurrentPair_forward (x : ReferenceActivePhysicalStep.RoundInput p rate) (dir : Fin 2)
    (s : Sample (AffineBatchDecoder.width p)) (j : Fin (M p)) :
    ((replaceCurrentPair x dir s).rows j).1 = (x.rows j).1 := by
  by_cases hj : j = x.selected
  · subst j
    simp only [replaceCurrentPair, Function.update_self, ReferenceActivePhysicalStep.RoundInput.row]
  · simp only [replaceCurrentPair, Function.update_of_ne hj]

/-- This preserves the whole scalar slice, at every row and calendar time. -/
theorem replaceCurrentPair_slice (x : ReferenceActivePhysicalStep.RoundInput p rate) (dir : Fin 2)
    (s : Sample (AffineBatchDecoder.width p)) (j : Fin (M p)) (t : Fin p.T) :
    (((replaceCurrentPair x dir s).rows j).2 t).1 = ((x.rows j).2 t).1 := by
  by_cases hj : j = x.selected
  · subst j
    by_cases ht : t = x.time
    · subst t
      simp only [replaceCurrentPair, Function.update_self, ReferenceActivePhysicalStep.RoundInput.row]
    · simp only [replaceCurrentPair, Function.update_self, Function.update_of_ne ht,
        ReferenceActivePhysicalStep.RoundInput.row]
  · simp only [replaceCurrentPair, Function.update_of_ne hj]

theorem replaceCurrentPair_scalar (x : ReferenceActivePhysicalStep.RoundInput p rate) (dir : Fin 2)
    (s : Sample (AffineBatchDecoder.width p)) (j : Fin (M p)) (t : Fin p.T)
    (label : ContinuousLearningRows.Label p) :
    (((replaceCurrentPair x dir s).rows j).2 t).1 label =
      ((x.rows j).2 t).1 label :=
  congrFun (replaceCurrentPair_slice x dir s j t) label

/-- In particular all `K+1` assignment coordinates survive, at arbitrary times. -/
theorem replaceCurrentPair_assignment (x : ReferenceActivePhysicalStep.RoundInput p rate) (dir : Fin 2)
    (s : Sample (AffineBatchDecoder.width p)) (j : Fin (M p)) (t : Fin p.T)
    (k : Fin (p.K + 1)) :
    (((replaceCurrentPair x dir s).rows j).2 t).1
        (ContinuousControlSlice.Label.assign k) =
      ((x.rows j).2 t).1 (ContinuousControlSlice.Label.assign k) :=
  replaceCurrentPair_scalar x dir s j t _

theorem replaceCurrentPair_other_row (x : ReferenceActivePhysicalStep.RoundInput p rate) (dir : Fin 2)
    (s : Sample (AffineBatchDecoder.width p)) (j : Fin (M p))
    (hj : j ≠ x.selected) : (replaceCurrentPair x dir s).rows j = x.rows j := by
  exact Function.update_of_ne hj _ _

theorem replaceCurrentPair_other_time (x : ReferenceActivePhysicalStep.RoundInput p rate) (dir : Fin 2)
    (s : Sample (AffineBatchDecoder.width p)) (t : Fin p.T) (ht : t ≠ x.time) :
    ((replaceCurrentPair x dir s).row.2 t) = x.row.2 t := by
  rw [replaceCurrentPair_row]
  exact Function.update_of_ne ht _ _

theorem replaceCurrentPair_sample (x : ReferenceActivePhysicalStep.RoundInput p rate) (dir : Fin 2)
    (s : Sample (AffineBatchDecoder.width p)) :
    ((replaceCurrentPair x dir s).row.2 x.time).2 (dir, ReferenceActivePhysicalStep.upSenderIndex x) = s := by
  rw [replaceCurrentPair_row]
  dsimp only
  rw [Function.update_self]
  exact Function.update_self _ _ _

theorem replaceCurrentPair_other_sample (x : ReferenceActivePhysicalStep.RoundInput p rate) (dir : Fin 2)
    (s : Sample (AffineBatchDecoder.width p)) (channel : ContinuousLearningRows.Channel p)
    (hc : channel ≠ (dir, ReferenceActivePhysicalStep.upSenderIndex x)) :
    ((replaceCurrentPair x dir s).row.2 x.time).2 channel =
      (x.row.2 x.time).2 channel := by
  rw [replaceCurrentPair_row]
  dsimp only
  rw [Function.update_self]
  exact Function.update_of_ne hc _ _

theorem replaceCurrentPair_current_slice (x : ReferenceActivePhysicalStep.RoundInput p rate) (dir : Fin 2)
    (s : Sample (AffineBatchDecoder.width p)) :
    ((replaceCurrentPair x dir s).row.2 x.time).1 = (x.row.2 x.time).1 := by
  simp only [replaceCurrentPair_row, Function.update_self]

theorem upSenderIndex_eq_draw (x : ReferenceActivePhysicalStep.RoundInput p rate) :
    ReferenceActivePhysicalStep.upSenderIndex x = PublicDiscreteDraws.selectedFollowerDraw
      p.two_le_m p.m_lt_K (x.row.2 x.time).1 :=
  CoordinatorUpMeasurability.selectedFollowerIndex_eq_draw _

theorem upSenderIndex_replace (x : ReferenceActivePhysicalStep.RoundInput p rate) (dir : Fin 2)
    (s : Sample (AffineBatchDecoder.width p)) :
    ReferenceActivePhysicalStep.upSenderIndex (replaceCurrentPair x dir s) = ReferenceActivePhysicalStep.upSenderIndex x := by
  rw [upSenderIndex_eq_draw, upSenderIndex_eq_draw]
  exact congrArg (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K)
    (replaceCurrentPair_current_slice x dir s)

/-- This is the actual option-valued DOWN word, including all dispatch failures. -/
def downSent (x : ReferenceActivePhysicalStep.RoundInput p rate) : Option (Word (AffineBatchDecoder.width p)) :=
  ReferenceDownReception.expectedDownFlatWord (ReferenceActivePhysicalStep.dispatch x).downView
    (ReferenceActivePhysicalStep.upSenderIndex x) x.row x.time

/-- This is the actual checked selected-follower offer after PREPARE. -/
def upSent (x : ReferenceActivePhysicalStep.RoundInput p rate) : Option (Word (AffineBatchDecoder.width p)) :=
  ReferenceActivePhysicalStep.upExpected (ReferenceActivePhysicalStep.prepare x)

/-- Checked offer construction reads the scalar slice and no affine sample. -/
theorem checkedUpOffer_eq_of_slice (i : Fin (p.m - 1))
    (row row' : CompletePublicTable.CompleteRow p) (alpha : ReferencePrelaunchFollower.Activation p)
    (t : Fin p.T) (state : ReferencePrelaunchFollower.State p rate.eta)
    (hc : (row.2 t).1 = (row'.2 t).1) :
    ActiveFollowerQueueOperation.checkedUpOffer rate.eta i row alpha t state =
      ActiveFollowerQueueOperation.checkedUpOffer rate.eta i row' alpha t state := by
  unfold ActiveFollowerQueueOperation.checkedUpOffer ActiveFollowerQueueOperation.selectedUpRound
  rw [hc]

/-- Arm rejection is independent of the affine samples, even for malformed offers. -/
theorem followerArmChoice_none_iff_of_slice (state : ReferencePrelaunchFollower.State p rate.eta)
    (c c' : ContinuousLearningRows.TimeControl p) (i : Fin (p.m - 1))
    (offer : Option (OrdinaryMessageCodec.UpRecord (ReferencePrelaunchFollower.codecParams p rate.eta)))
    (hc : c.1 = c'.1) :
    ActiveFollowerArmChoice.followerArmChoiceCore state c i offer = none ↔
      ActiveFollowerArmChoice.followerArmChoiceCore state c' i offer = none := by
  rcases c with ⟨control, samples⟩
  rcases c' with ⟨control', samples'⟩
  change control = control' at hc
  subst control'
  unfold ActiveFollowerArmChoice.followerArmChoiceCore
  dsimp only
  split
  · split
    · constructor <;> intro h <;> cases h
    · split
      · cases offer with
        | none => rfl
        | some offered =>
          dsimp only
          split
          · constructor <;> intro h <;> cases h
          · rfl
      · constructor <;> intro h <;> cases h
  · cases state.lastDown with
    | none => rfl
    | some last => rfl

/-- Compare only the actual continuation configuration, never the retained row. -/
theorem prepare_configuration_eq_of_slice (i : Fin (p.m - 1))
    (row row' : CompletePublicTable.CompleteRow p) (alpha : ReferencePrelaunchFollower.Activation p)
    (t : Fin p.T) (active : alpha.val ≤ t.val + 1)
    (input : DeclaredFollowerLocalRound.LocalConfiguration p rate) (hc : (row.2 t).1 = (row'.2 t).1) :
    (DeclaredFollowerLocalRound.prepare rate i row alpha t active input).configuration =
      (DeclaredFollowerLocalRound.prepare rate i row' alpha t active input).configuration := by
  cases input with
  | dagger => rfl
  | ordinary state memory =>
    cases hstart : ActiveFollowerLifecycle.startRound rate.eta t state memory with
    | error reason => simp only [DeclaredFollowerLocalRound.prepare, hstart]
    | ok pair =>
      rcases pair with ⟨choice, mem⟩
      have hoff := checkedUpOffer_eq_of_slice (rate := rate) i row row' alpha t choice hc
      have hn (offer) := followerArmChoice_none_iff_of_slice (rate := rate)
        choice (row.2 t) (row'.2 t) i offer hc
      simp only [DeclaredFollowerLocalRound.prepare, hstart, ← hoff]
      cases ActiveFollowerQueueOperation.checkedUpOffer rate.eta i row alpha t choice with
      | failure => rfl
      | noOffer =>
        dsimp only
        cases ha : ActiveFollowerArmChoice.followerArmChoice choice row t i none with
        | none =>
          have ha' : ActiveFollowerArmChoice.followerArmChoice choice row' t i none = none :=
            (hn none).mp ha
          simp only [ha']
        | some arm =>
          cases ha' : ActiveFollowerArmChoice.followerArmChoice choice row' t i none with
          | none =>
            have h := (hn none).mpr ha'
            rw [show ActiveFollowerArmChoice.followerArmChoiceCore choice (row.2 t) i none =
              some arm from ha] at h
            cases h
          | some arm' => rfl
      | offer offered =>
        dsimp only
        cases ha : ActiveFollowerArmChoice.followerArmChoice choice row t i (some offered) with
        | none =>
          have ha' : ActiveFollowerArmChoice.followerArmChoice choice row' t i
              (some offered) = none := (hn (some offered)).mp ha
          simp only [ha']
        | some arm =>
          cases ha' : ActiveFollowerArmChoice.followerArmChoice choice row' t i (some offered) with
          | none =>
            have h := (hn (some offered)).mpr ha'
            rw [show ActiveFollowerArmChoice.followerArmChoiceCore choice (row.2 t) i
              (some offered) = some arm from ha] at h
            cases h
          | some arm' => rfl

theorem follower_configuration_replace (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (dir : Fin 2) (s : Sample (AffineBatchDecoder.width p)) (i : Fin (p.m - 1)) :
    ((ReferenceActivePhysicalStep.prepare (replaceCurrentPair x dir s)).followers.followers i).configuration =
      ((ReferenceActivePhysicalStep.prepare x).followers.followers i).configuration := by
  exact prepare_configuration_eq_of_slice i _ _ _ _ _ _
    (replaceCurrentPair_current_slice x dir s)

/-- The selected sender's option-valued checked word is fixed, in either direction. -/
theorem upSent_replace (x : ReferenceActivePhysicalStep.RoundInput p rate) (dir : Fin 2)
    (s : Sample (AffineBatchDecoder.width p)) :
    upSent (replaceCurrentPair x dir s) = upSent x := by
  unfold upSent ReferenceActivePhysicalStep.upExpected ReferenceUpReception.currentOfferWord
  rw [upSenderIndex_replace, follower_configuration_replace]
  cases ((ReferenceActivePhysicalStep.prepare x).followers.followers
      (ReferenceActivePhysicalStep.upSenderIndex x)).configuration with
  | dagger => rfl
  | ordinary state memory =>
    have hn := (ReferenceActivePhysicalStep.prepare (replaceCurrentPair x dir s)).follower_alignment
      (ReferenceActivePhysicalStep.upSenderIndex x)
    have ho := (ReferenceActivePhysicalStep.prepare x).follower_alignment
      (ReferenceActivePhysicalStep.upSenderIndex x)
    have hc := checkedUpOffer_eq_of_slice (rate := rate)
      (ReferenceActivePhysicalStep.upSenderIndex x) (replaceCurrentPair x dir s).row
      x.row (x.state.activations (ReferenceActivePhysicalStep.upSenderIndex x)) x.time state
      (replaceCurrentPair_current_slice x dir s)
    rw [hn.1, hn.2.1, hn.2.2.1, hn.2.2.2, ho.1, ho.2.1, ho.2.2.1, ho.2.2.2]
    exact congrArg (fun offer : ActiveFollowerQueueOperation.UpOfferResult p rate.eta =>
      match offer with
      | .failure => none
      | .noOffer => none
      | .offer record => some ((OrdinaryMessageCodec.wordEquivFlat
          (ReferencePrelaunchFollower.codecParams p rate.eta))
          (OrdinaryMessageCodec.encodeUp (ReferencePrelaunchFollower.codecParams p rate.eta) record))) hc

/-- Arm equality needs only the scalar slice and this follower's own UP pair. -/
theorem prepare_arm_eq_of_slice_sample (i : Fin (p.m - 1))
    (row row' : CompletePublicTable.CompleteRow p) (alpha : ReferencePrelaunchFollower.Activation p)
    (t : Fin p.T) (active : alpha.val ≤ t.val + 1)
    (input : DeclaredFollowerLocalRound.LocalConfiguration p rate)
    (hc : (row.2 t).1 = (row'.2 t).1)
    (hs : (row.2 t).2 (1, i) = (row'.2 t).2 (1, i)) :
    (DeclaredFollowerLocalRound.prepare rate i row alpha t active input).arm =
      (DeclaredFollowerLocalRound.prepare rate i row' alpha t active input).arm := by
  have ha (state : ReferencePrelaunchFollower.State p rate.eta) (offer) :
      ActiveFollowerArmChoice.followerArmChoice state row t i offer =
        ActiveFollowerArmChoice.followerArmChoice state row' t i offer :=
    ActiveFollowerArmChoice.followerArmChoiceCore_eq_of_same_control_and_up_sample
      state _ _ i offer hc hs
  cases input with
  | dagger => rfl
  | ordinary state memory =>
    cases hstart : ActiveFollowerLifecycle.startRound rate.eta t state memory with
    | error reason => simp only [DeclaredFollowerLocalRound.prepare, hstart]
    | ok pair =>
      rcases pair with ⟨choice, mem⟩
      have hoff := checkedUpOffer_eq_of_slice (rate := rate) i row row' alpha t choice hc
      simp only [DeclaredFollowerLocalRound.prepare, hstart, ← hoff, ← ha]
      cases ActiveFollowerQueueOperation.checkedUpOffer rate.eta i row alpha t choice with
      | failure => rfl
      | noOffer =>
        dsimp only
        cases ActiveFollowerArmChoice.followerArmChoice choice row t i none <;> rfl
      | offer offered =>
        dsimp only
        cases ActiveFollowerArmChoice.followerArmChoice choice row t i (some offered) <;> rfl

theorem follower_arm_replace_of_other_channel
    (x : ReferenceActivePhysicalStep.RoundInput p rate) (dir : Fin 2)
    (s : Sample (AffineBatchDecoder.width p)) (i : Fin (p.m - 1))
    (hi : (1, i) ≠ (dir, ReferenceActivePhysicalStep.upSenderIndex x)) :
    (ReferenceActivePhysicalStep.prepare (replaceCurrentPair x dir s)).arms.actions
        (PublicDiscreteDraws.followerPlayer p.two_le_m i) =
      (ReferenceActivePhysicalStep.prepare x).arms.actions
        (PublicDiscreteDraws.followerPlayer p.two_le_m i) := by
  rw [ReferenceActivePhysicalStep.PreparedRound.action_follower,
    ReferenceActivePhysicalStep.PreparedRound.action_follower]
  exact prepare_arm_eq_of_slice_sample i _ _ _ _ _ _
    (replaceCurrentPair_current_slice x dir s) (replaceCurrentPair_other_sample x dir s _ hi)

/-- Every follower action is fixed by a DOWN-pair perturbation. -/
theorem follower_arm_replace_down (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (s : Sample (AffineBatchDecoder.width p)) (i : Fin (p.m - 1)) :
    (ReferenceActivePhysicalStep.prepare (replaceCurrentPair x 0 s)).arms.actions
        (PublicDiscreteDraws.followerPlayer p.two_le_m i) =
      (ReferenceActivePhysicalStep.prepare x).arms.actions
        (PublicDiscreteDraws.followerPlayer p.two_le_m i) := by
  apply follower_arm_replace_of_other_channel
  intro h
  have hdir := congrArg Prod.fst h
  exact (by decide : (1 : Fin 2) ≠ 0) hdir

/-- Unselected follower actions are fixed by an UP-pair perturbation. -/
theorem follower_arm_replace_up_of_ne (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (s : Sample (AffineBatchDecoder.width p)) (i : Fin (p.m - 1))
    (hi : i ≠ ReferenceActivePhysicalStep.upSenderIndex x) :
    (ReferenceActivePhysicalStep.prepare (replaceCurrentPair x 1 s)).arms.actions
        (PublicDiscreteDraws.followerPlayer p.two_le_m i) =
      (ReferenceActivePhysicalStep.prepare x).arms.actions
        (PublicDiscreteDraws.followerPlayer p.two_le_m i) :=
  follower_arm_replace_of_other_channel x 1 s i (fun h => hi (congrArg Prod.snd h))

/-- DOWN performs no sparse append, independently of its observation and arm. -/
theorem logAt_eq_nil_of_down (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (alpha : ReferencePrelaunchFollower.Activation p) (t : Fin p.T)
    (own : Fin p.K × ReferencePrelaunchFollower.Observation p)
    (hd : PublicDiscreteDraws.slotDraw (row.2 t).1 = PublicDiscreteDraws.downSlot) :
    ReferencePrelaunchFollower.logAt i row alpha t own = [] := by
  apply ActiveFollowerLogging.logAt_eq_nil_of_not_tests
  intro h
  have hdata := ((ReferencePrelaunchFollower.loggingTestsPass_iff i row alpha t own).mp h).2.1
  rw [hd] at hdata
  exact (by decide : PublicDiscreteDraws.downSlot ≠ PublicDiscreteDraws.dataSlot) hdata

theorem checkedLogging_eq_of_down (i : Fin (p.m - 1))
    (row : CompletePublicTable.CompleteRow p) (alpha : ReferencePrelaunchFollower.Activation p)
    (t : Fin p.T) (own : Fin p.K × ReferencePrelaunchFollower.Observation p)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (hd : PublicDiscreteDraws.slotDraw (row.2 t).1 = PublicDiscreteDraws.downSlot) :
    ActiveFollowerLogging.checkedLogging i row alpha t own state =
      if ActiveFollowerLifecycle.localBufferValid state then .ok state
      else .error .invalidInputBuffer := by
  classical
  have hupdate : ActiveFollowerLogging.loggingUpdate i row alpha t own state = state := by
    unfold ActiveFollowerLogging.loggingUpdate
    rw [logAt_eq_nil_of_down i row alpha t own hd, List.append_nil]
    split <;> rfl
  simp only [ActiveFollowerLogging.checkedLogging, hupdate, dite_eq_ite]
  split
  · simp_all only
  · simp_all only

/-- Exact pair-independent DOWN logging, including an invalid carried buffer. -/
theorem checkedLogging_replace_down (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (s : Sample (AffineBatchDecoder.width p)) (i : Fin (p.m - 1))
    (alpha : ReferencePrelaunchFollower.Activation p)
    (own own' : Fin p.K × ReferencePrelaunchFollower.Observation p)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (hd : PublicDiscreteDraws.slotDraw (x.row.2 x.time).1 = PublicDiscreteDraws.downSlot) :
    ActiveFollowerLogging.checkedLogging i (replaceCurrentPair x 0 s).row alpha x.time own state =
      ActiveFollowerLogging.checkedLogging i x.row alpha x.time own' state := by
  have hd' : PublicDiscreteDraws.slotDraw ((replaceCurrentPair x 0 s).row.2 x.time).1 =
      PublicDiscreteDraws.downSlot := by rw [replaceCurrentPair_current_slice, hd]
  rw [checkedLogging_eq_of_down i _ alpha _ own state hd',
    checkedLogging_eq_of_down i _ alpha _ own' state hd]

/-- Precisely the five checks before the actual DOWN decoder invocation. -/
def downReceiverGate (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (t : Fin p.T) (state : ReferencePrelaunchFollower.State p rate.eta) : Prop :=
  ActiveFollowerDownAcceptance.downSelected p i row t ∧
    state.status = .unoccupied ∧
    ActiveFollowerDownAcceptance.registerInputDomain p rate state ∧
    ActiveFollowerDownAcceptance.decoderInputDomain p state.downBatch ∧
    ActiveFollowerDownAcceptance.bufferInputDomain p state.buffer

/-- Both raw-match values count as an executed call; subsequent results are irrelevant. -/
theorem referenceDownCut_has_call
    (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p) (t : Fin p.T)
    (observation : ReferencePrelaunchFollower.Observation p)
    (state : ReferencePrelaunchFollower.State p rate.eta) :
    (ReferenceDownReception.referenceDownCut p view i row t observation rate state).rawComparison.isSome =
      decide (downReceiverGate i row t state) := by
  unfold ReferenceDownReception.referenceDownCut downReceiverGate
  dsimp only
  split
  · split
    · split
      · split
        · split
          · split <;> simp_all only [and_self, decide_true, Option.isSome_some]
          · simp_all only [and_false, decide_false, Option.isSome_none]
        · simp_all only [and_false, false_and, decide_false, Option.isSome_none]
      · simp_all only [and_false, false_and, decide_false, Option.isSome_none]
    · simp_all only [and_false, false_and, decide_false, Option.isSome_none]
  · simp_all only [false_and, decide_false, Option.isSome_none]

/-- The actual follower prefix: ordinary preparation, unoccupied status,
checked logging, and the original receiver checks. -/
def downCallGate (prepared : DeclaredFollowerLocalRound.PreparedRound p rate)
    (observation : ReferencePrelaunchFollower.Observation p) : Bool :=
  match prepared.configuration with
  | .dagger => false
  | .ordinary state _ =>
    if state.status = .unoccupied then
      match ActiveFollowerLogging.checkedLogging prepared.follower prepared.row
          prepared.activation prepared.time (prepared.arm, observation) state with
      | .error _ => false
      | .ok logged => decide (downReceiverGate prepared.follower prepared.row prepared.time logged)
    else false

/-- Observe whether the retained diagnostics record any actual DOWN call. -/
def downDiagnosticCall (observation : ReferenceActivePhysicalStep.FollowerObservation p rate) : Bool :=
  match observation.down with
  | none => false
  | some cut => cut.rawComparison.isSome

theorem finishFollower_down_call
    (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (prepared : DeclaredFollowerLocalRound.PreparedRound p rate)
    (observation : ReferencePrelaunchFollower.Observation p) :
    downDiagnosticCall (ReferenceActivePhysicalStep.finishFollower view prepared observation) =
      downCallGate prepared observation := by
  cases hc : prepared.configuration with
  | dagger => simp only [ReferenceActivePhysicalStep.finishFollower, hc, downCallGate, downDiagnosticCall]
  | ordinary state memory =>
    by_cases hs : state.status = .unoccupied
    · cases hl : ActiveFollowerLogging.checkedLogging prepared.follower prepared.row
          prepared.activation prepared.time (prepared.arm, observation) state with
      | error reason =>
        simp only [ReferenceActivePhysicalStep.finishFollower, hc,
          ReferenceActivePhysicalStep.recordFollower, hs, dite_true, hl, downCallGate,
          ite_true, downDiagnosticCall]
      | ok logged =>
        simp only [ReferenceActivePhysicalStep.finishFollower, hc,
          ReferenceActivePhysicalStep.recordFollower, hs, dite_true, hl, downCallGate, ite_true]
        cases DeclaredFollowerLocalRound.consumeDownResult rate
            (ReferenceDownReception.referenceDownCut p view prepared.follower prepared.row
              prepared.time observation rate logged).outcome with
        | error reason => exact referenceDownCut_has_call view _ _ _ _ _
        | ok postRecord =>
          dsimp only
          cases DeclaredFollowerLocalRound.releaseAndFinish rate prepared.follower prepared.row
              prepared.time observation state memory postRecord with
          | error reason => exact referenceDownCut_has_call view _ _ _ _ _
          | ok pair => exact referenceDownCut_has_call view _ _ _ _ _
    · simp only [ReferenceActivePhysicalStep.finishFollower, hc,
        ReferenceActivePhysicalStep.recordFollower, hs, dite_false, downCallGate, ite_false]
      cases DeclaredFollowerLocalRound.recordOrServiceThenDown rate prepared.follower
          prepared.row prepared.activation prepared.time prepared.active prepared.arm observation state with
      | error reason => rfl
      | ok postRecord =>
        dsimp only
        cases DeclaredFollowerLocalRound.releaseAndFinish rate prepared.follower prepared.row
            prepared.time observation state memory postRecord with
        | error reason => rfl
        | ok pair => rfl

/-- Literal executed positive test. Later mismatch, parsing and recovery failures count. -/
def downPositive (x : ReferenceActivePhysicalStep.RoundInput p rate) : Bool :=
  let prepared := ReferenceActivePhysicalStep.prepare x
  let i := ReferenceActivePhysicalStep.upSenderIndex x
  let own := prepared.feedback.observations (PublicDiscreteDraws.followerPlayer p.two_le_m i)
  downCallGate (prepared.followers.followers i) own && decide (0 < own.val.val)

theorem downPositive_eq_diagnostic (x : ReferenceActivePhysicalStep.RoundInput p rate) :
    downPositive x =
      (downDiagnosticCall ((ReferenceActivePhysicalStep.prepare x).observeFollower
        (ReferenceActivePhysicalStep.upSenderIndex x)) &&
      decide (0 < ((ReferenceActivePhysicalStep.prepare x).feedback.observations
        (PublicDiscreteDraws.followerPlayer p.two_le_m
          (ReferenceActivePhysicalStep.upSenderIndex x))).val.val)) := by
  rw [ReferenceActivePhysicalStep.PreparedRound.observeFollower, finishFollower_down_call]
  rfl

/-- Literal UP eligibility at retained actual receiver diagnostics. No diagnostic means no call. -/
def upDiagnosticPositive (diagnostic : Option (ReferenceActivePhysicalStep.UpDiagnostic p rate)) : Bool :=
  match diagnostic with
  | none => false
  | some d => decide (AffineBatchDecoder.eligible (CoordinatorUpReception.roundInput d.input))

def upPositive (x : ReferenceActivePhysicalStep.RoundInput p rate) : Bool :=
  upDiagnosticPositive (ReferenceActivePhysicalStep.prepare x).observeCoordinator.up

/-- Input checks precede UP eligibility; the original ledger gate and own reward are used. -/
theorem receiveUp_positive {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (ledger : ReferenceActivePhysicalStep.Ledger rate) :
    upDiagnosticPositive (ReferenceActivePhysicalStep.receiveUp prepared ledger).diagnostic =
      (CoordinatorUpReception.receptionInputCheck
        (ReferenceUpReception.receptionInputAtRow rate x.row
          (ReferenceActivePhysicalStep.upInputs prepared ledger) x.time) &&
      decide (AffineBatchDecoder.eligible (CoordinatorUpReception.roundInput
        (ReferenceUpReception.receptionInputAtRow rate x.row
          (ReferenceActivePhysicalStep.upInputs prepared ledger) x.time)))) := by
  unfold ReferenceActivePhysicalStep.receiveUp
  dsimp only
  split
  · simp_all only [upDiagnosticPositive, Bool.true_and]
  · rename_i hn
    have hf := Bool.eq_false_iff.mpr hn
    simp only [hf, Bool.false_and, upDiagnosticPositive]

/-- All post-reception result and finish failures preserve the executed-test diagnostic. -/
theorem collectionFinish_up (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (recording : CoordinatorRecordingOperation.Output p)
    (cut : ReferenceActivePhysicalStep.UpCut p rate) :
    (ReferenceActivePhysicalStep.collectionFinish (x := x) payload started recording cut).up =
      cut.diagnostic := by
  unfold ReferenceActivePhysicalStep.collectionFinish
  cases cut.result with
  | invalid => rfl
  | success pair | rejected pair =>
    rcases pair with ⟨ledger, bank⟩
    dsimp only
    cases CoordinatorCollectionLedger.finishRound ledger with
    | invalid => rfl
    | rejected ignored => rfl
    | success ledgerFinished =>
      dsimp only
      cases CoordinatorPhaseClock.finishRound p rate.eta.val x.time started.clock
          ledgerFinished.pending x.row <;> rfl

/-- Actual round records specialize through `output_eq`, without any trace input. -/
theorem record_downPositive (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) :
    downPositive r.input =
      (downDiagnosticCall (r.output.followers (ReferenceActivePhysicalStep.upSenderIndex r.input)) &&
      decide (0 < (r.output.preparation.feedback.observations
        (PublicDiscreteDraws.followerPlayer p.two_le_m
          (ReferenceActivePhysicalStep.upSenderIndex r.input))).val.val)) := by
  rw [r.output_eq]
  exact downPositive_eq_diagnostic r.input

theorem record_upPositive (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) :
    upPositive r.input = upDiagnosticPositive r.output.coordinator.up := by
  rw [r.output_eq]
  rfl

/-- The same DOWN prefix after deriving that logging appends nothing on DOWN. -/
def downPrefixGate (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (t : Fin p.T) (configuration : DeclaredFollowerLocalRound.LocalConfiguration p rate) : Bool :=
  match configuration with
  | .dagger => false
  | .ordinary state _ => decide (ActiveFollowerLifecycle.localBufferValid state ∧
      downReceiverGate i row t state)

/-- The actual executed DOWN prefix ignores the arm and observation in every branch. -/
theorem downCallGate_eq_prefix (prepared : DeclaredFollowerLocalRound.PreparedRound p rate)
    (observation : ReferencePrelaunchFollower.Observation p) :
    downCallGate prepared observation = downPrefixGate prepared.follower prepared.row
      prepared.time prepared.configuration := by
  cases hc : prepared.configuration with
  | dagger => simp only [downCallGate, hc, downPrefixGate]
  | ordinary state memory =>
    by_cases hd : ActiveFollowerDownAcceptance.downSelected p prepared.follower
        prepared.row prepared.time
    · by_cases hs : state.status = .unoccupied
      · simp only [downCallGate, hc, hs, ite_true]
        rw [checkedLogging_eq_of_down _ _ _ _ _ _ hd.1]
        by_cases hb : ActiveFollowerLifecycle.localBufferValid state
        · simp only [hb, ite_true, downPrefixGate, true_and]
        · simp only [hb, ite_false, downPrefixGate, false_and, decide_false]
      · simp only [downCallGate, hc, hs, ite_false, downPrefixGate, downReceiverGate,
          hd, false_and, and_false, decide_false]
    · simp only [downCallGate, hc, downPrefixGate, downReceiverGate, hd, false_and,
        and_false, decide_false]
      split
      · cases ActiveFollowerLogging.checkedLogging prepared.follower prepared.row
          prepared.activation prepared.time (prepared.arm, observation) state <;> rfl
      · rfl

theorem downPrefixGate_eq_of_slice (i : Fin (p.m - 1))
    (row row' : CompletePublicTable.CompleteRow p) (t : Fin p.T)
    (configuration : DeclaredFollowerLocalRound.LocalConfiguration p rate)
    (hc : (row.2 t).1 = (row'.2 t).1) :
    downPrefixGate i row t configuration = downPrefixGate i row' t configuration := by
  cases configuration with
  | dagger => rfl
  | ordinary state memory =>
    unfold downPrefixGate downReceiverGate ActiveFollowerDownAcceptance.downSelected
    rw [hc]

/-- Exact pair-independent enabling guard for the actual DOWN opportunity. -/
def downGate (x : ReferenceActivePhysicalStep.RoundInput p rate) : Bool :=
  let prepared := ReferenceActivePhysicalStep.prepare x
  downPrefixGate (ReferenceActivePhysicalStep.upSenderIndex x) x.row x.time
    (prepared.followers.followers (ReferenceActivePhysicalStep.upSenderIndex x)).configuration

theorem downGate_replace (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (dir : Fin 2) (s : Sample (AffineBatchDecoder.width p)) :
    downGate (replaceCurrentPair x dir s) = downGate x := by
  unfold downGate
  dsimp only
  rw [upSenderIndex_replace, follower_configuration_replace]
  exact downPrefixGate_eq_of_slice _ _ _ _ _ (replaceCurrentPair_current_slice x dir s)

theorem downPositive_eq_gate_feedback (x : ReferenceActivePhysicalStep.RoundInput p rate) :
    downPositive x = (downGate x && decide (0 <
      (ReferenceActiveFeedbackCut.collisionFeedbackVector
        (ReferenceActivePhysicalStep.prepare x).arms.actions x.time x.rewards
        (PublicDiscreteDraws.followerPlayer p.two_le_m
          (ReferenceActivePhysicalStep.upSenderIndex x))).val)) := by
  unfold downPositive
  dsimp only [PublicDiscreteDraws.followerCount]
  rw [downCallGate_eq_prefix]
  have h := (ReferenceActivePhysicalStep.prepare x).follower_alignment
    (ReferenceActivePhysicalStep.upSenderIndex x)
  rw [h.1, h.2.1, h.2.2.1]
  change (downGate x && decide (0 <
      (ActualInitializationPhysicalStep.observationOfGrid p
        (ReferenceActiveFeedbackCut.collisionFeedbackVector
          (ReferenceActivePhysicalStep.prepare x).arms.actions x.time x.rewards
          (PublicDiscreteDraws.followerPlayer p.two_le_m
            (ReferenceActivePhysicalStep.upSenderIndex x)))).val.val)) = _
  rw [ActualInitializationPhysicalStep.observationOfGrid_value]
  have hD : (0 : ℝ) < (D p : ℝ) := Nat.cast_pos.mpr (D_pos p)
  simp only [div_pos_iff_of_pos_right hD, Nat.cast_pos]

/-- The complete assignment-vector read is fixed at every time, including later instructions. -/
theorem ownAssignmentVector_replace (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (dir : Fin 2) (s : Sample (AffineBatchDecoder.width p)) (t : Fin p.T) :
    LaterAssignmentStartOperation.ownAssignmentVector (replaceCurrentPair x dir s).row t =
      LaterAssignmentStartOperation.ownAssignmentVector x.row t := by
  funext k
  exact replaceCurrentPair_assignment x dir s x.selected t k

/-- The first launch reads its actual full scalar assignment vector. -/
theorem firstLaunchInput_coordinates_replace (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (dir : Fin 2) (s : Sample (AffineBatchDecoder.width p)) :
    (CoordinatorRoundDispatch.firstLaunchInput
      (ReferenceActivePhysicalStep.firstInput (replaceCurrentPair x dir s))).coordinates =
      (CoordinatorRoundDispatch.firstLaunchInput (ReferenceActivePhysicalStep.firstInput x)).coordinates :=
  ownAssignmentVector_replace x dir s x.time

/-- The actual collection recorder returns checked zero on non-DATA, or its domain failure. -/
theorem collectionRecording_nonData {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ)
    (hd : PublicDiscreteDraws.slotDraw (x.row.2 x.time).1 ≠ PublicDiscreteDraws.dataSlot) :
    CoordinatorRecorderComplementBridge.run
        (ReferenceActivePhysicalStep.collectionRecordingInput prepared payload started weights) =
      if CoordinatorRecorderComplementBridge.LocalInputsValid
          (ReferenceActivePhysicalStep.collectionRecordingInput prepared payload started weights) then
        some (CoordinatorRecordingOperation.zeroOutput p) else none := by
  let input := ReferenceActivePhysicalStep.collectionRecordingInput prepared payload started weights
  by_cases hv : CoordinatorRecorderComplementBridge.LocalInputsValid input
  · rw [ite_eq_left hv, CoordinatorRecorderComplementBridge.run_eq_executeValid input hv]
    exact CoordinatorRecordingOperation.executeValid_zero_of_not_data _ _ hd
  · rw [ite_eq_right hv]
    apply CoordinatorRecordingOperation.run_none_of_invalid
    exact fun h => hv ((CoordinatorRecorderComplementBridge.recorderInput_inputsValid_iff input).mp h)

/-- The collection recorder prefix on UP is independent of the changed pair and feedback. -/
theorem collectionRecording_replace_up (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (s : Sample (AffineBatchDecoder.width p)) (payload : ReferenceActivePhysicalStep.Payload rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ)
    (hu : PublicDiscreteDraws.slotDraw (x.row.2 x.time).1 = PublicDiscreteDraws.upSlot) :
    CoordinatorRecorderComplementBridge.run
        (ReferenceActivePhysicalStep.collectionRecordingInput
          (ReferenceActivePhysicalStep.prepare (replaceCurrentPair x 1 s)) payload started weights) =
      CoordinatorRecorderComplementBridge.run
        (ReferenceActivePhysicalStep.collectionRecordingInput
          (ReferenceActivePhysicalStep.prepare x) payload started weights) := by
  have hd : PublicDiscreteDraws.slotDraw (x.row.2 x.time).1 ≠ PublicDiscreteDraws.dataSlot := by
    rw [hu]
    decide
  have hd' : PublicDiscreteDraws.slotDraw ((replaceCurrentPair x 1 s).row.2 x.time).1 ≠
      PublicDiscreteDraws.dataSlot := by rw [replaceCurrentPair_current_slice]; exact hd
  rw [collectionRecording_nonData _ _ _ _ hd', collectionRecording_nonData _ _ _ _ hd]
  rfl

/-- The collection prefix keeps enabled zero-arrival service and all start failures. -/
theorem collectionPostChoice_positive_prefix
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (payload : ReferenceActivePhysicalStep.Payload rate) (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ) :
    upDiagnosticPositive
        (ReferenceActivePhysicalStep.collectionPostChoice prepared payload ledger started weights).up =
      match CoordinatorRecorderComplementBridge.run
          (ReferenceActivePhysicalStep.collectionRecordingInput prepared payload started weights) with
      | none => false
      | some recording =>
        match CoordinatorCollectionLedger.startRound ledger (x.time.val + 1)
            (ReferenceActivePhysicalStep.collectionEnabled ledger x.time)
            (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) with
        | .invalid => false
        | .rejected _ => false
        | .success ledgerStarted =>
          let input := ReferenceUpReception.receptionInputAtRow rate x.row
            (ReferenceActivePhysicalStep.upInputs prepared ledgerStarted) x.time
          CoordinatorUpReception.receptionInputCheck input &&
            decide (AffineBatchDecoder.eligible (CoordinatorUpReception.roundInput input)) := by
  unfold ReferenceActivePhysicalStep.collectionPostChoice
  cases CoordinatorRecorderComplementBridge.run
      (ReferenceActivePhysicalStep.collectionRecordingInput prepared payload started weights) with
  | none => rfl
  | some recording =>
    dsimp only
    cases CoordinatorCollectionLedger.startRound ledger (x.time.val + 1)
        (ReferenceActivePhysicalStep.collectionEnabled ledger x.time)
        (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) with
    | invalid => rfl
    | rejected ignored => rfl
    | success ledgerStarted =>
      rw [collectionFinish_up]
      exact receiveUp_positive prepared ledgerStarted

/-- The receiver's input checks and selection gate read neither hash nor observation. -/
theorem up_checks_eq_of_slice (row row' : CompletePublicTable.CompleteRow p)
    (ledger : ReferenceActivePhysicalStep.Ledger rate) (bank : CoordinatorUpReception.UpDecoderBank p)
    (t : Fin p.T) (y y' : Fin (D p + 1)) (hc : (row.2 t).1 = (row'.2 t).1) :
    let input := ReferenceUpReception.receptionInputAtRow rate row (ledger, bank, t, y) t
    let input' := ReferenceUpReception.receptionInputAtRow rate row' (ledger, bank, t, y') t
    CoordinatorUpReception.receptionInputCheck input = CoordinatorUpReception.receptionInputCheck input' ∧
      (CoordinatorUpReception.receptionGate input ↔ CoordinatorUpReception.receptionGate input') := by
  dsimp only
  constructor
  · rfl
  · unfold CoordinatorUpReception.receptionGate ReferenceUpReception.receptionInputAtRow
      CoordinatorUpMeasurability.receptionInputAtRow CoordinatorUpMeasurability.receptionInputAtControl
    dsimp only
    rw [CoordinatorUpMeasurability.selectedFollowerIndex_eq_draw,
      CoordinatorUpMeasurability.selectedFollowerIndex_eq_draw, hc]

end Bandits.Support.ReferenceActiveAffinePositiveTest
