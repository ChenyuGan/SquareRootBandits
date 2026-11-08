/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCorrectedCurrentCutoffReplyRetention

import Mathlib.Tactic

/-!
# Current follower queues on the first corrected LIVE assignment

Sources: `appendix_a_local_protocol.tex:28-64`,
`06_interruptions.tex:40-100,192-233,246-299`, and
`04_slow_fast_learner.tex:157-174` under `sources/zip4/manuscript/`.

The full birth-plus-LIVE slice has one attributed replay word per follower.
Actual cutoff phase excludes unoccupied CURRENT queries; literal service,
release and FINISH provide the final-record CHOICE-to-OUTPUT frame.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions

namespace Bandits.Support.ReferenceFirstCorrectedCurrentFollowerLiveQueue

variable {p : ConstructorDimensions.Parameters}

private theorem mapM_length_of_some {α β : Type*} (f : α → Option β) :
    ∀ (xs : List α) (ys : List β), xs.mapM f = some ys → xs.length = ys.length := by
  intro xs
  induction xs with
  | nil =>
      intro ys h
      have hy : ys = [] := by simpa using h.symm
      simp [hy]
  | cons x xs ih =>
      intro ys h
      simp only [List.mapM_cons] at h
      cases hf : f x with
      | none => simp [hf] at h
      | some y =>
          cases ht : xs.mapM f with
          | none => simp [hf, ht] at h
          | some ys0 =>
              have hys : ys = y :: ys0 := by
                have heq : some (y :: ys0) = some ys := by
                  simpa [List.mapM_cons, hf, ht] using h
                exact (Option.some.inj heq).symm
              subst ys
              simp only [List.length_cons, ih ys0 ht]

private theorem mapM_take_of_some {α β : Type*} (f : α → Option β)
    (xs : List α) (ys : List β) (h : xs.mapM f = some ys) (n : ℕ) :
    (xs.take n).mapM f = some (ys.take n) := by
  induction xs generalizing ys n with
  | nil =>
      have hy : [] = ys := Option.some.inj h
      subst ys
      simp only [List.take_nil, List.mapM_nil, Option.pure_def]
  | cons x xs ih =>
      cases hx : f x with
      | none => simp only [List.mapM_cons, hx, Option.bind_eq_bind, Option.bind_none] at h; cases h
      | some y =>
          cases hs : xs.mapM f with
          | none =>
              simp only [List.mapM_cons, hx, hs, Option.bind_eq_bind,
                Option.bind_some, Option.bind_none] at h
              cases h
          | some rest =>
              have hy : y :: rest = ys := by
                simpa only [List.mapM_cons, hx, hs, Option.bind_eq_bind,
                  Option.bind_some, Option.pure_def, Option.some.injEq] using h
              subst ys
              cases n with
              | zero => simp only [List.take_zero, List.mapM_nil, Option.pure_def]
              | succ n =>
                  simp only [List.take_succ_cons, List.mapM_cons, hx, ih rest hs n,
                    Option.bind_eq_bind, Option.bind_some, Option.pure_def]

/-- A current DOWN retained by an actual ordinary CHOICE has an earlier
source record retaining that same installed payload's DOWN.  The birth
selector is identified by its actual installation constructor and original
record time; no queue, status, or applied-DOWN premise is supplied. -/
theorem actual_current_choice_down_source
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (_hz : z ∈ ReferenceFirstCollectionCorrectedSliceNumericalPrefix.correctedCell
      rate rewards C_star C_h u t)
    (b : ℕ)
    (birth : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (P : ReferenceActivePhysicalStep.Payload rate)
    (hb : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[b]? = some birth)
    (hborn : ReferenceAssignmentPayloadPersistence.InstallationBirth birth P)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (i : Fin (p.m - 1))
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hchoice : (ReferenceFollowerFixedReply.actualChoice
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[k.val] i).configuration = .ordinary state memory)
    (hcurrent : state.lastDown = some (P.downRecord i)) :
    ∃ a : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h).length,
      b ≤ a.val ∧ a.val < k.val ∧
      ReferenceAcceptedUpFollowerHistory.RetainedDown
        (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h)[a.val] i (P.downRecord i) := by
  classical
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  have hbLt : b < R.length := (List.getElem?_eq_some_iff.mp hb).1
  have hbGet : R[b] = birth := (List.getElem?_eq_some_iff.mp hb).2
  let bFin : Fin R.length := ⟨b, hbLt⟩
  have hbornAt : ReferenceAssignmentPayloadPersistence.InstallationBirth R[b] P := by
    rw [hbGet]
    exact hborn
  obtain ⟨b', a, P', beta, hba, hak, hborn', _hbase, hretained, hmessage,
      _hmass, _hdelta⟩ :=
    ReferenceCompleteOrdinaryFollowerMass.complete_ordinary_follower_choice_mass
      rewards C_star C_h z k i state memory hchoice (P.downRecord i) hcurrent
  have hPStart : P'.sigma.val + 1 = P.sigma.val + 1 := by
    calc
      P'.sigma.val + 1 = (P'.downRecord i).val.sigma := by
        rw [P'.downRecord_fields i]
      _ = (P.downRecord i).val.sigma := by
        rw [← hmessage]
      _ = P.sigma.val + 1 := by rw [P.downRecord_fields i]
  have htimeP' : P'.sigma.val =
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + b'.val := by
    calc
      P'.sigma.val = R[b'.val].input.time.val :=
        ReferenceAssignmentPayloadChronology.installationBirth_time_eq
          R[b'.val] P' hborn'
      _ = ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + b'.val :=
        ReferenceAssignmentFollowerMassSteps.complete_record_time
          rate rewards C_star C_h z b'
  have htimeP : P.sigma.val =
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + b := by
    calc
      P.sigma.val = R[b].input.time.val :=
        ReferenceAssignmentPayloadChronology.installationBirth_time_eq R[b] P hbornAt
      _ = ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + b := by
        simpa only [bFin] using
          (ReferenceAssignmentFollowerMassSteps.complete_record_time
            rate rewards C_star C_h z bFin)
  have hindex : b'.val = b := by omega
  have hretainedCurrent : ReferenceAcceptedUpFollowerHistory.RetainedDown
      R[a.val] i (P.downRecord i) := by
    simpa only [hmessage] using hretained
  exact ⟨a, by omega, hak, hretainedCurrent⟩

/-- Every ordinary LIVE CHOICE that already retains the installed current DOWN
has an actual earlier accepted-DOWN source in the same original suffix.  This
source statement also applies when the queried CHOICE is unoccupied. -/
theorem actual_first_corrected_live_choice_current_source
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hz : z ∈ ReferenceFirstCollectionCorrectedSliceNumericalPrefix.correctedCell
      rate rewards C_star C_h u t) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let b := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.birthIndex
      rate rewards C_star C_h z
    let W := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.liveTail
      rate rewards C_star C_h z
    let V := (R.drop b).take (1 + W.length)
    ∃ birth P,
      R[b]? = some birth ∧
      ReferenceAssignmentPayloadPersistence.InstallationBirth birth P ∧
      P.sigma = t ∧
      ∀ (i : Fin (p.m - 1)) (j : ℕ) (hj : j < V.length)
        (state : ReferencePrelaunchFollower.State p rate.eta)
        (memory : ActiveFollowerLifecycle.LocalMemory p),
        (ReferenceFollowerFixedReply.actualChoice V[j] i).configuration =
          .ordinary state memory →
        state.lastDown = some (P.downRecord i) →
        ∃ a : Fin R.length,
          b ≤ a.val ∧ a.val < b + j ∧
          ReferenceAcceptedUpFollowerHistory.RetainedDown R[a.val] i
            (P.downRecord i) := by
  classical
  intro R b W V
  obtain ⟨_L, _c, birth, P, _base, _hL, _hc, _hprefix, _hlen, hb, hborn,
      hSigma, _hqueues, _hbase, _hV, hbound, _hterminal, hqueries,
      _hcutoff, _hwords, _hcurrentEnd⟩ :=
    ReferenceFirstCorrectedCurrentCutoffReplyRetention.actual_first_corrected_current_cutoff_reply_retention
      rate rewards C_star C_h u t z hz
  have hbLt : b < R.length := (List.getElem?_eq_some_iff.mp hb).1
  refine ⟨birth, P, hb, hborn, hSigma, ?_⟩
  intro i j hj state memory hchoice hcurrent
  have hlen : V.length = 1 + W.length := by
    dsimp only [V]
    rw [List.length_take, List.length_drop, Nat.min_eq_left]
    change b + (1 + W.length) ≤ R.length at hbound
    omega
  have hbound' : b + (1 + W.length) ≤ R.length := by
    change b + (1 + W.length) ≤ R.length at hbound
    exact hbound
  have hjW : j < 1 + W.length := by
    rw [← hlen]
    exact hj
  have hindex : b + j < R.length := by omega
  have hslice : V[j] = R[b + j] := by
    dsimp only [V]
    rw [List.getElem_take]
    simp only [List.getElem_drop]
  have hchoice' : (ReferenceFollowerFixedReply.actualChoice R[b + j] i).configuration =
      .ordinary state memory := by
    simpa only [hslice] using hchoice
  obtain ⟨a, hba, hak, hretained⟩ := actual_current_choice_down_source
    rate rewards C_star C_h u t z hz b birth P hb hborn
      ⟨b + j, hindex⟩ i state memory hchoice' hcurrent
  exact ⟨a, hba, hak, hretained⟩

/-- An ordinary LIVE INPUT that retains the installed current DOWN inherits
the same actual source through the physical INPUT-to-CHOICE reply frame,
including when the INPUT is unoccupied. -/
theorem actual_first_corrected_live_input_current_source
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hz : z ∈ ReferenceFirstCollectionCorrectedSliceNumericalPrefix.correctedCell
      rate rewards C_star C_h u t) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let b := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.birthIndex
      rate rewards C_star C_h z
    let W := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.liveTail
      rate rewards C_star C_h z
    let V := (R.drop b).take (1 + W.length)
    ∃ birth P,
      R[b]? = some birth ∧
      ReferenceAssignmentPayloadPersistence.InstallationBirth birth P ∧
      P.sigma = t ∧
      ∀ (i : Fin (p.m - 1)) (j : ℕ) (hj : j < V.length)
        (input : ReferencePrelaunchFollower.State p rate.eta)
        (inputMemory : ActiveFollowerLifecycle.LocalMemory p)
        (choice : ReferencePrelaunchFollower.State p rate.eta)
        (choiceMemory : ActiveFollowerLifecycle.LocalMemory p),
        V[j].input.state.followers i = .ordinary input inputMemory →
        (ReferenceFollowerFixedReply.actualChoice V[j] i).configuration =
          .ordinary choice choiceMemory →
        input.lastDown = some (P.downRecord i) →
        ∃ a : Fin R.length,
          b ≤ a.val ∧ a.val < b + j ∧
          ReferenceAcceptedUpFollowerHistory.RetainedDown R[a.val] i
            (P.downRecord i) := by
  classical
  intro R b W V
  obtain ⟨birth, P, hb, hborn, hSigma, hsource⟩ :=
    actual_first_corrected_live_choice_current_source
      rate rewards C_star C_h u t z hz
  refine ⟨birth, P, hb, hborn, hSigma, ?_⟩
  intro i j hj input inputMemory choice choiceMemory hinput hchoice hcurrent
  obtain ⟨before, beforeMemory, hbefore, hframe, _hunoccupied⟩ :=
    ReferenceFollowerReplyChronology.record_input_to_choice
      V[j] i choice choiceMemory hchoice
  have hbeforeEq : before = input :=
    (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
      (hbefore.symm.trans hinput)).1
  have hlast : choice.lastDown = input.lastDown := by
    have h := congrArg Prod.fst hframe
    simpa only [ReferenceFollowerReplyChronology.reply] using h.trans
      (congrArg (fun state : ReferencePrelaunchFollower.State p rate.eta => state.lastDown)
        hbeforeEq)
  exact hsource i j hj choice choiceMemory hchoice
    (hlast.trans hcurrent)

/-- At an ordinary actual OUTPUT retaining a given DOWN, either this record's
own diagnostic accepted that DOWN, or the same DOWN was already present at
its actual CHOICE.  The split follows the literal output/CHOICE constructors. -/
theorem actual_record_output_current_down_source
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1))
    (next : ReferencePrelaunchFollower.State p rate.eta)
    (nextMemory : ActiveFollowerLifecycle.LocalMemory p)
    (houtput : (record.output.followers i).configuration = .ordinary next nextMemory)
    (M : OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))
    (hcurrent : next.lastDown = some M) :
    ReferenceAcceptedUpFollowerHistory.RetainedDown record i M ∨
      ∃ choice choiceMemory,
        (ReferenceFollowerFixedReply.actualChoice record i).configuration =
          .ordinary choice choiceMemory ∧ choice.lastDown = some M := by
  classical
  let prepared := record.output.preparation.followers.followers i
  let view := record.output.preparation.coordinator.downView
  let observation := record.output.preparation.feedback.observations
    (PublicDiscreteDraws.followerPlayer p.two_le_m i)
  have hfinish : (ReferenceActivePhysicalStep.finishFollower view prepared observation).configuration =
      .ordinary next nextMemory := by
    have hout : record.output.followers i = record.output.preparation.observeFollower i := by
      rw [record.output_eq]
      rfl
    rw [hout] at houtput
    change (ReferenceActivePhysicalStep.finishFollower view prepared observation).configuration =
      .ordinary next nextMemory at houtput
    exact houtput
  obtain ⟨choice, choiceMemory, post, hchoice, hrecord, hrelease,
      hfinishInput, hfinishDown⟩ :=
    ReferenceFollowerReplyChronology.finishFollower_ordinary_inversion
      view prepared observation next nextMemory hfinish
  have hframe := ReferenceFollowerReplyChronology.releaseAndFinish_frame
    prepared.follower prepared.row prepared.time observation choice post next
    choiceMemory nextMemory hrelease
  have hnextPost : next.lastDown = post.lastDown := by
    have hreply := hframe.1
    have h := congrArg Prod.fst hreply
    simpa only [ReferenceFollowerReplyChronology.reply] using h
  rcases ReferenceFollowerReplyChronology.recordFollower_ordinary_inversion
      view prepared.follower prepared.row prepared.activation prepared.time prepared.active
      prepared.arm observation choice post hrecord with
    ⟨hpostDownChoice, _hkeep⟩ |
    ⟨logged, cut, raw, down, scan, registers, lastService,
      hlogged, hcut, _hcutEq, haccepted, _hstrict, hpostDown⟩
  · right
    refine ⟨choice, choiceMemory, hchoice, ?_⟩
    exact hpostDownChoice.symm.trans (hnextPost.symm.trans hcurrent)
  · have hdownEq : down = M := Option.some.inj (hpostDown.symm.trans
      (hnextPost.symm.trans hcurrent))
    subst down
    have hout : record.output.followers i = record.output.preparation.observeFollower i := by
      rw [record.output_eq]
      rfl
    left
    refine ⟨logged, cut, post, raw, scan, registers, lastService, ?_, ?_, haccepted⟩
    · rw [hout]
      unfold ReferenceActivePhysicalStep.PreparedRound.observeFollower
      exact hfinishInput.trans hlogged
    · rw [hout]
      unfold ReferenceActivePhysicalStep.PreparedRound.observeFollower
      exact hfinishDown.trans hcut

/-- Every ordinary LIVE OUTPUT that retains the installed current DOWN has
an actual accepted-DOWN source no later than that output: either its own
diagnostic accepted the record or the actual CHOICE already retained it. -/
theorem actual_first_corrected_live_output_current_source
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hz : z ∈ ReferenceFirstCollectionCorrectedSliceNumericalPrefix.correctedCell
      rate rewards C_star C_h u t) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let b := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.birthIndex
      rate rewards C_star C_h z
    let W := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.liveTail
      rate rewards C_star C_h z
    let V := (R.drop b).take (1 + W.length)
    ∃ birth P,
      R[b]? = some birth ∧
      ReferenceAssignmentPayloadPersistence.InstallationBirth birth P ∧
      P.sigma = t ∧
      ∀ (i : Fin (p.m - 1)) (j : ℕ) (hj : j < V.length)
        (next : ReferencePrelaunchFollower.State p rate.eta)
        (nextMemory : ActiveFollowerLifecycle.LocalMemory p),
        (V[j].output.followers i).configuration = .ordinary next nextMemory →
        next.lastDown = some (P.downRecord i) →
        ∃ a : Fin R.length,
          b ≤ a.val ∧ a.val ≤ b + j ∧
          ReferenceAcceptedUpFollowerHistory.RetainedDown R[a.val] i
            (P.downRecord i) := by
  classical
  intro R b W V
  obtain ⟨birth, P, hb, hborn, hSigma, hchoiceSource⟩ :=
    actual_first_corrected_live_choice_current_source
      rate rewards C_star C_h u t z hz
  have hroot :=
    ReferenceFirstCorrectedCurrentCutoffReplyRetention.actual_first_corrected_current_cutoff_reply_retention
      rate rewards C_star C_h u t z hz
  obtain ⟨_L, _c, _birth, _P, _base, _hL, _hc, _hprefix, _hlen, _hb, _hborn,
      _hSigma, _hqueues, _hbase, _hV, hbound, _hterminal, hqueries,
      _hcutoff, _hwords, _hcurrentEnd⟩ := hroot
  have hlen : V.length = 1 + W.length := by
    dsimp only [V]
    rw [List.length_take, List.length_drop, Nat.min_eq_left]
    change b + (1 + W.length) ≤ R.length at hbound
    omega
  have hbound' : b + (1 + W.length) ≤ R.length := by
    change b + (1 + W.length) ≤ R.length at hbound
    exact hbound
  refine ⟨birth, P, hb, hborn, hSigma, ?_⟩
  intro i j hj next nextMemory houtput hcurrent
  have hjW : j < 1 + W.length := by rw [← hlen]; exact hj
  have hindex : b + j < R.length := by omega
  have hslice : V[j] = R[b + j] := by
    dsimp only [V]
    rw [List.getElem_take]
    simp only [List.getElem_drop]
  obtain hretained |
      ⟨choice, choiceMemory, hchoice, hchoiceCurrent⟩ :=
      actual_record_output_current_down_source rate V[j] i next
        nextMemory houtput (P.downRecord i) hcurrent
  · exact ⟨⟨b + j, hindex⟩, Nat.le_add_right b j, Nat.le_refl _, by
      simpa only [hslice] using hretained⟩
  · obtain ⟨a, hba, hak, hsource⟩ :=
      hchoiceSource i j hj choice choiceMemory hchoice hchoiceCurrent
    exact ⟨a, hba, Nat.le_of_lt hak, hsource⟩

/-- On an occupied ordinary INPUT, the same replay word and numerical reply
registers pass through the actual INPUT-to-CHOICE preparation frame. The
occupied-INPUT case is taken from the public source producer; the CHOICE
state is not reseeded or given a second word. -/
theorem actual_first_corrected_live_choice_replay
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hz : z ∈ ReferenceFirstCollectionCorrectedSliceNumericalPrefix.correctedCell
      rate rewards C_star C_h u t) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let b := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.birthIndex
      rate rewards C_star C_h z
    let W := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.liveTail
      rate rewards C_star C_h z
    let V := (R.drop b).take (1 + W.length)
    ∃ (birth : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
      (P : ReferenceActivePhysicalStep.Payload rate)
      (A : Fin (p.m - 1) → List (Bool × ℕ)),
      R[b]? = some birth ∧
      ReferenceAssignmentPayloadPersistence.InstallationBirth birth P ∧
      P.sigma = t ∧
      (∀ i, V.mapM
        (ReferenceFirstCorrectedAssignedArrivalPrefix.attributedArrival? P i) = some (A i)) ∧
      (∀ i, (A i).length = V.length) ∧
      (∀ i v, v ≤ V.length →
        (V.take v).mapM
          (ReferenceFirstCorrectedAssignedArrivalPrefix.attributedArrival? P i) =
            some ((A i).take v)) ∧
      (∀ (i : Fin (p.m - 1)) (j : ℕ) (hj : j < V.length),
        ∃ next nextMemory,
          (V[j]).output.next.followers i = .ordinary next nextMemory ∧
          (next.status ≠ .unoccupied →
            ∃ word,
              word = (A i).take (j + 1) ∧
              (V.take (j + 1)).mapM
                (ReferenceFirstCorrectedAssignedArrivalPrefix.attributedArrival? P i) = some word ∧
              next.lastDown = some (P.downRecord i) ∧
              (next.S, next.backlog) =
                QueueReplay.replay (4 * rate.n) (0, (P.downRecord i).val.q) word ∧
              next.delta =
                (QueueReplay.replay (4 * rate.n) (0, (P.downRecord i).val.q) word).1 -
                  (QueueReplay.replay (4 * rate.n) (0, (P.downRecord i).val.q)
                    (word.take j)).1)) ∧
      ∀ (i : Fin (p.m - 1)) (j : ℕ) (hj : j < V.length)
        (input : ReferencePrelaunchFollower.State p rate.eta)
        (inputMemory : ActiveFollowerLifecycle.LocalMemory p)
        (choice : ReferencePrelaunchFollower.State p rate.eta)
        (choiceMemory : ActiveFollowerLifecycle.LocalMemory p),
        V[j].input.state.followers i = .ordinary input inputMemory →
        (ReferenceFollowerFixedReply.actualChoice V[j] i).configuration =
          .ordinary choice choiceMemory →
        input.status ≠ .unoccupied →
        ∃ word,
          word = (A i).take j ∧
          (V.take j).mapM
            (ReferenceFirstCorrectedAssignedArrivalPrefix.attributedArrival? P i) = some word ∧
          choice.lastDown = some (P.downRecord i) ∧
          (choice.S, choice.backlog) =
            QueueReplay.replay (4 * rate.n) (0, (P.downRecord i).val.q) word := by
  classical
  intro R b W V
  obtain ⟨_L, _c, birth, P, _base, _hL, _hc, _hprefix, _hlen, hb, hborn,
      hSigma, _hqueues, _hbase, _hV, _hbound, _hterminal, hqueries,
      _hcutoff, hwords, _hcurrentEnd⟩ :=
    ReferenceFirstCorrectedCurrentCutoffReplyRetention.actual_first_corrected_current_cutoff_reply_retention
      rate rewards C_star C_h u t z hz
  have hVlen : V.length = 1 + W.length := by
    dsimp only [V]
    have hdrop : 1 + W.length ≤ (R.drop b).length := by
      rw [List.length_drop]
      have hbound : b + (1 + W.length) ≤ R.length := _hbound
      omega
    rw [List.length_take, Nat.min_eq_left hdrop]
  have hW : W = ReferenceFirstCollectionCorrectedSliceNumericalPrefix.liveTail
      rate rewards C_star C_h z := rfl
  have hVlenRoot : V.length = 1 +
      (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.liveTail
        rate rewards C_star C_h z).length := by
    calc
      V.length = 1 + W.length := hVlen
      _ = 1 + (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.liveTail
          rate rewards C_star C_h z).length := by rw [hW]
  have htakeAll : V.take (1 +
      (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.liveTail
        rate rewards C_star C_h z).length) = V :=
    List.take_of_length_le (by rw [hVlenRoot])
  have hfull : ∀ i : Fin (p.m - 1),
      ∃ A : List (Bool × ℕ),
        V.mapM (ReferenceFirstCorrectedAssignedArrivalPrefix.attributedArrival? P i) = some A := by
    intro i
    obtain ⟨A, hA, _hunique⟩ := hwords i (1 +
      (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.liveTail
        rate rewards C_star C_h z).length) (le_rfl)
    have hAfull : V.mapM
        (ReferenceFirstCorrectedAssignedArrivalPrefix.attributedArrival? P i) = some A := by
      rw [← htakeAll]
      exact hA
    exact ⟨A, hAfull⟩
  choose A hA using hfull
  have hAlength : ∀ i, (A i).length = V.length := by
    intro i
    exact (mapM_length_of_some _ _ _ (hA i)).symm
  have hAtake : ∀ i v, v ≤ V.length →
      (V.take v).mapM
        (ReferenceFirstCorrectedAssignedArrivalPrefix.attributedArrival? P i) =
          some ((A i).take v) := by
    intro i v hv
    exact mapM_take_of_some _ V (A i) (hA i) v
  refine ⟨birth, P, A, hb, hborn, hSigma, hA, hAlength, hAtake, ?_⟩
  constructor
  · intro i j hj
    obtain ⟨input0, inputMemory0, choice0, next, nextMemory, _hrecord, _hinput,
        _hstart, _hchoice, _houtput, _hfailure, hnext, _hbirthInput, _hinputNumeric,
        houtputNumeric, _hadj⟩ := hqueries i j hj
    refine ⟨next, nextMemory, hnext, ?_⟩
    intro hnextOccupied
    obtain ⟨word, hword, hlast, hreplay, hdelta⟩ := houtputNumeric hnextOccupied
    have hjBoundSucc : j + 1 ≤ 1 +
        (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.liveTail
          rate rewards C_star C_h z).length := by
      rw [← hW, ← hVlen]
      exact Nat.succ_le_of_lt hj
    obtain ⟨uniqueWord, _huniqueWord, hunique⟩ := hwords i (j + 1) hjBoundSucc
    have hwordA : (V.take (j + 1)).mapM
        (ReferenceFirstCorrectedAssignedArrivalPrefix.attributedArrival? P i) =
          some ((A i).take (j + 1)) :=
      hAtake i (j + 1) (Nat.succ_le_of_lt hj)
    have hwordEq : word = (A i).take (j + 1) := by
      exact (hunique word hword).trans
        (hunique ((A i).take (j + 1)) hwordA).symm
    exact ⟨word, hwordEq, hword, hlast, hreplay, hdelta⟩
  · intro i j hj input inputMemory choice choiceMemory hinputExternal hchoiceExternal hinputOccupied
    obtain ⟨input0, inputMemory0, choice0, next, nextMemory, _hrecord, hinput,
        _hstart, hchoice, _houtput, _hfailure, _hnext, hbirthInput,
        hinputNumeric, _houtputNumeric, _hadj⟩ := hqueries i j hj
    have hinputEq : input0 = input :=
      (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
        (hinput.symm.trans hinputExternal)).1
    have hchoiceEq : choice0 = choice := by
      change (ReferenceFollowerFixedReply.actualChoice V[j] i).configuration = _ at hchoice
      exact (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
        (hchoice.symm.trans hchoiceExternal)).1
    subst input0
    subst choice0
    have hpos : 1 ≤ j := by
      by_contra hnot
      have hjzero : j = 0 := by omega
      exact hinputOccupied (hbirthInput hjzero)
    obtain ⟨word, hword, hlast, hreplay⟩ := hinputNumeric hpos hinputOccupied
    have hjBound : j ≤ 1 + W.length := by
      rw [← hVlen]
      exact Nat.le_of_lt hj
    have hjBoundRoot : j ≤ 1 +
        (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.liveTail
          rate rewards C_star C_h z).length := by
      rw [← hW]
      exact hjBound
    obtain ⟨uniqueWord, _huniqueWord, hunique⟩ := hwords i j hjBoundRoot
    have hwordA : (V.take j).mapM
        (ReferenceFirstCorrectedAssignedArrivalPrefix.attributedArrival? P i) =
          some ((A i).take j) := hAtake i j (by omega)
    have hwordEq : word = (A i).take j := by
      exact (hunique word hword).trans (hunique ((A i).take j) hwordA).symm
    obtain ⟨before, beforeMemory, hbefore, hframe, _hunoccupied⟩ :=
      ReferenceFollowerReplyChronology.record_input_to_choice
        V[j] i choice choiceMemory hchoiceExternal
    have hbeforeEq : before = input :=
      (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
        (hbefore.symm.trans hinputExternal)).1
    have hframe' : ReferenceFollowerReplyChronology.reply choice =
        ReferenceFollowerReplyChronology.reply input := by
      rw [hbeforeEq] at hframe
      exact hframe
    have hlastChoice : choice.lastDown = some (P.downRecord i) := by
      have h := congrArg Prod.fst hframe'
      simpa only [ReferenceFollowerReplyChronology.reply] using h.trans hlast
    have hregisters : (choice.S, choice.backlog) = (input.S, input.backlog) := by
      apply Prod.ext
      · exact congrArg (fun r => r.2.1) hframe'
      · exact congrArg (fun r => r.2.2.2) hframe'
    exact ⟨word, hwordEq, hword, hlastChoice, hregisters.trans hreplay⟩

/-- At the actual installation BIRTH, INPUT and CHOICE have not yet retained
the new payload's DOWN.  The INPUT claim uses the actual PREPARE frame; CHOICE
is refuted by the source-origin theorem above at the birth index itself. -/
theorem actual_first_corrected_birth_no_current_down
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hz : z ∈ ReferenceFirstCollectionCorrectedSliceNumericalPrefix.correctedCell
      rate rewards C_star C_h u t) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let b := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.birthIndex
      rate rewards C_star C_h z
    ∃ birth P,
      R[b]? = some birth ∧
      ReferenceAssignmentPayloadPersistence.InstallationBirth birth P ∧
      P.sigma = t ∧
      ∀ i : Fin (p.m - 1),
        ∃ input inputMemory choice choiceMemory,
          birth.input.state.followers i = .ordinary input inputMemory ∧
          (ReferenceFollowerFixedReply.actualChoice birth i).configuration =
            .ordinary choice choiceMemory ∧
          input.lastDown ≠ some (P.downRecord i) ∧
          choice.lastDown ≠ some (P.downRecord i) := by
  classical
  intro R b
  let W := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.liveTail
    rate rewards C_star C_h z
  let V := (R.drop b).take (1 + W.length)
  obtain ⟨_L, _c, birth, P, _base, _hL, _hc, _hprefix, _hlen, hb, hborn,
      hSigma, _hqueues, _hbase, _hV, _hbound, _hterminal, hqueries,
      _hcutoff, _hwords⟩ :=
    ReferenceFirstCorrectedCurrentCutoffReplyRetention.actual_first_corrected_current_cutoff_reply_retention
      rate rewards C_star C_h u t z hz
  have hbLt : b < R.length := (List.getElem?_eq_some_iff.mp hb).1
  let bFin : Fin R.length := ⟨b, hbLt⟩
  refine ⟨birth, P, hb, hborn, hSigma, ?_⟩
  intro i
  have hj : 0 < V.length := by
    change 0 < ((R.drop b).take (1 + W.length)).length
    simp only [List.length_take, List.length_drop]
    omega
  obtain ⟨input, inputMemory, choice, next, nextMemory, hrecord, hinput,
      _hstart, hchoice, _houtput, _hfailure, _hnext, _hbInput, _hinputQueue,
      _houtputQueue, _hadj⟩ := hqueries i 0 (by omega)
  have hsliceBirth : R[b]? = some V[0] := by
    simpa only [Nat.add_zero] using hrecord
  have hV0 : V[0] = birth := Option.some.inj (hsliceBirth.symm.trans hb)
  have hbGet : R[b] = birth := (List.getElem?_eq_some_iff.mp hb).2
  have hinputAtZero : V[0].input.state.followers i = .ordinary input inputMemory := by
    change V[0].input.state.followers i = .ordinary input inputMemory at hinput
    exact hinput
  have hinputBirth : birth.input.state.followers i = .ordinary input inputMemory := by
    rw [← hV0]
    exact hinputAtZero
  have hchoiceAtZero : (ReferenceFollowerFixedReply.actualChoice (V[0]) i).configuration =
      .ordinary choice inputMemory := by
    change (ReferenceFollowerFixedReply.actualChoice (V[0]) i).configuration =
      .ordinary choice inputMemory at hchoice
    exact hchoice
  have hchoiceBirth : (ReferenceFollowerFixedReply.actualChoice birth i).configuration =
      .ordinary choice inputMemory := by
    rw [← hV0]
    exact hchoiceAtZero
  have hchoiceAtIndex : (ReferenceFollowerFixedReply.actualChoice R[bFin.val] i).configuration =
      .ordinary choice inputMemory := by
    simpa only [bFin, hbGet] using hchoiceBirth
  have hchoiceAbs : choice.lastDown ≠ some (P.downRecord i) := by
    intro hcurrent
    obtain ⟨a, hba, hak, _hretained⟩ := actual_current_choice_down_source
      rate rewards C_star C_h u t z hz b birth P hb hborn bFin i choice
      inputMemory hchoiceAtIndex hcurrent
    have hak' : a.val < b := by simpa only [bFin] using hak
    omega
  have hinputAbs : input.lastDown ≠ some (P.downRecord i) := by
    intro hcurrent
    obtain ⟨before, beforeMemory, hbefore, hreply, _hunoccupied⟩ :=
      ReferenceFollowerReplyChronology.record_input_to_choice
        birth i choice inputMemory hchoiceBirth
    have hbeforeEq : before = input :=
      (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
        (hbefore.symm.trans hinputBirth)).1
    subst before
    have hlast : choice.lastDown = input.lastDown := by
      have h := congrArg Prod.fst hreply
      simpa only [ReferenceFollowerReplyChronology.reply] using h
    exact hchoiceAbs (hlast.trans hcurrent)
  exact ⟨input, inputMemory, choice, inputMemory, hinputBirth, hchoiceBirth,
    hinputAbs, hchoiceAbs⟩

private theorem release_finish_occupied
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (t : Fin p.T) (observation : ReferencePrelaunchFollower.Observation p)
    (before post next : ReferencePrelaunchFollower.State p rate.eta)
    (memory nextMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hpost : post.status ≠ .unoccupied)
    (h : DeclaredFollowerLocalRound.releaseAndFinish rate i row t observation
      before memory post = .ok (next, nextMemory)) :
    next.status ≠ .unoccupied := by
  unfold DeclaredFollowerLocalRound.releaseAndFinish at h
  cases hr : ActiveFollowerLifecycle.releaseAfterService rate.eta i t
      (ActiveFollowerLifecycle.publicRowOfCompleteRow row t) observation before post with
  | error reason => rw [hr] at h; cases h
  | ok released =>
    simp only [hr] at h
    cases hf : ActiveFollowerLifecycle.finishRound rate.eta t row released memory with
    | error reason => rw [hf] at h; cases h
    | ok result =>
      have heq : result = (next, nextMemory) :=
        Except.ok.inj (by simpa only [hf] using h)
      rw [heq] at hf
      have hframe := ActiveFollowerLifecycle.finishRound_frame rate.eta t row released
        next memory nextMemory hf
      rw [hframe]
      unfold ActiveFollowerLifecycle.releaseAfterService at hr
      split at hr
      · split at hr
        · split at hr
          · cases hr
          · split at hr
            · split at hr
              · split at hr
                · dsimp only at hr
                  split at hr
                  · cases hr; intro hbad; cases hbad
                  · cases hr
                · dsimp only at hr
                  split at hr
                  · cases hr; exact hpost
                  · cases hr
              · cases hr
            · cases hr
        · cases hr
      · cases hr; exact hpost

private theorem occupied_record_status
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (activation : ReferencePrelaunchFollower.Activation p) (t : Fin p.T)
    (active : activation.val ≤ t.val + 1) (arm : Fin p.K)
    (observation : ReferencePrelaunchFollower.Observation p)
    (choice post : ReferencePrelaunchFollower.State p rate.eta)
    (hoccupied : choice.status ≠ .unoccupied)
    (hrecord : (ReferenceActivePhysicalStep.recordFollower
      view i row activation t active arm
      observation choice).result = .ok post) :
    post.status = choice.status := by
  have hlogged := hrecord
  rw [ReferenceActivePhysicalStep.recordFollower_result] at hlogged
  unfold ReferenceDownReception.loggingThenReferenceDown at hlogged
  simp only [dite_eq_right hoccupied] at hlogged
  unfold DeclaredFollowerLocalRound.recordOrServiceThenDown at hlogged
  simp only [dite_eq_right hoccupied] at hlogged
  cases hservice : ActiveFollowerQueueOperation.checkedService rate.eta rate.sourceCap
      rate.n rate.n_scale i row activation t observation choice with
  | failure => simp only [hservice] at hlogged; cases hlogged
  | success result =>
    simp only [hservice] at hlogged
    have hstate : result.output = post := Except.ok.inj hlogged
    subst post
    rw [result.queueUpdate]
    exact (ActiveFollowerQueueOperation.serviceOutput_preserves_other_registers
      rate.n choice result.arrival).2.2.2.1

private theorem downStart_current (rate : ReferenceActivePhysicalStep.RateInput p)
    (P : ReferenceActivePhysicalStep.Payload rate) (i : Fin (p.m - 1)) :
    ActiveFollowerDownAcceptance.downStart p rate (P.downRecord i) = P.sigma := by
  apply Fin.ext
  have h := ActiveFollowerDownAcceptance.downStart_val_add_one p rate (P.downRecord i)
  rw [P.downRecord_fields i] at h
  dsimp only at h
  omega

private theorem cutoff_after_live_date
    (rate : ReferenceActivePhysicalStep.RateInput p) (sigma date : Fin p.T)
    (bits : Fin p.T → Bool)
    (hgrid : date.val + 2 ≤ FollowerCutoffScan.gridBoundary p rate.eta.val sigma)
    (hbits : ∀ v : Fin p.T, sigma.val ≤ v.val → v.val < date.val → bits v = false) :
    date.val + 1 < FollowerCutoffScan.firstCutoff p rate.eta.val sigma bits := by
  have hmem := Finset.min'_mem (FollowerCutoffScan.firstCutoffCarrier p rate.eta.val sigma bits)
    (FollowerCutoffScan.firstCutoffCarrier_nonempty p rate.eta.val sigma bits)
  rcases Finset.mem_insert.mp hmem with hg | hb
  · change FollowerCutoffScan.firstCutoff p rate.eta.val sigma bits = _ at hg
    omega
  · obtain ⟨v, hv, heq⟩ := Finset.mem_image.mp hb
    have hbit := (Finset.mem_filter.mp hv).2
    have hcoord := (Finset.mem_filter.mp hv).1
    simp only [FollowerCutoffScan.proposalCoordinates, Finset.mem_filter,
      Finset.mem_univ, true_and] at hcoord
    have hdate : date.val ≤ v.val := by
      by_contra hnot
      rw [hbits v hcoord.1 (by omega)] at hbit
      cases hbit
    change v.val + 2 = FollowerCutoffScan.firstCutoff p rate.eta.val sigma bits at heq
    omega

/-- Strict LIVE cutoff geometry, including the birth and terminal record. -/
private theorem actual_live_cutoff_bound
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hz : z ∈ ReferenceFirstCollectionCorrectedSliceNumericalPrefix.correctedCell
      rate rewards C_star C_h u t)
    (birth : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (P : ReferenceActivePhysicalStep.Payload rate)
    (hb : (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.birthIndex rate rewards C_star C_h z]? =
      some birth)
    (hborn : ReferenceAssignmentPayloadPersistence.InstallationBirth birth P) :
    let V := birth :: ReferenceFirstCollectionCorrectedSliceNumericalPrefix.liveTail rate rewards C_star C_h z
    ∀ (j : ℕ) (hj : j < V.length),
      V[j].input.time.val + 1 < FollowerCutoffScan.firstCutoff p rate.eta.val P.sigma
        (FollowerCutoffScan.completeRowProposalBit p rate.eta.val V[j].input.row) := by
  intro V j hj
  cases j with
  | zero =>
    have ht := ReferenceAssignmentPayloadChronology.installationBirth_time_eq birth P hborn
    simpa only [V, List.getElem_cons_zero, ht] using
      (FollowerCutoffScan.firstCutoff_bounds p rate.eta.val rate.eta.property rate.sourceCap
        P.sigma (FollowerCutoffScan.completeRowProposalBit p rate.eta.val birth.input.row)).1
  | succ k =>
    obtain ⟨birth0, hb0, _ha, _ht, hchosen⟩ :=
      ReferenceFirstCollectionCorrectedNextPhysicalReadout.firstCell_firstReplacement_record
        rate rewards C_star C_h u t z hz.1
    have heq : birth0 = birth := Option.some.inj (hb0.symm.trans hb)
    subst birth0
    have hgeo := ReferenceFirstReplacementLiveFollowerPrefix.complete_first_replacement_continuing_geometry
      rate z rewards C_star C_h
    dsimp only at hgeo
    have hb' := hb
    simp only [ReferenceFirstCollectionCorrectedSliceNumericalPrefix.birthIndex,
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords] at hb'
    rw [hb'] at hgeo
    dsimp only at hgeo
    have hprep : birth.output.preparation = ReferenceActivePhysicalStep.prepare birth.input := by
      rw [birth.output_eq]; rfl
    unfold ReferenceCollectionPhaseHistory.laterChosen at hchosen
    rw [← hprep] at hchosen
    cases hc : birth.output.preparation.coordinator <;>
      simp only [hc, Bool.false_eq_true] at hchosen
    rename_i outcome
    cases outcome <;> simp only at hchosen <;> try contradiction
    rename_i installed arm
    rw [hc] at hgeo
    have hp : P = installed.registers.payload := by
      exact (show P = installed.registers.payload ∧ _ from by
        simpa only [ReferenceAssignmentPayloadPersistence.InstallationBirth, hc] using hborn).1
    subst P
    have hk : k < (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.liveTail
        rate rewards C_star C_h z).length := by
      change k + 1 < _ + 1 at hj
      omega
    obtain ⟨_hr, _htime, _hrows, _hselected, _hrewards, selected, _hs, _hp,
      _hlive, hgrid, hbits⟩ := hgeo.2 ⟨k, hk⟩
    exact cutoff_after_live_date rate installed.registers.payload.sigma _ _ hgrid hbits

/-- Literal occupied service, release and FINISH preserve the current DOWN
and occupation through the actual OUTPUT. FINISH only reads the current bit. -/
theorem actual_record_occupied_choice_output_frame
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1))
    (choice next : ReferencePrelaunchFollower.State p rate.eta)
    (memory nextMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hc : (ReferenceFollowerFixedReply.actualChoice record i).configuration = .ordinary choice memory)
    (ho : (record.output.followers i).configuration = .ordinary next nextMemory)
    (hoccupied : choice.status ≠ .unoccupied) :
    next.status ≠ .unoccupied ∧ next.lastDown = choice.lastDown := by
  let prepared := record.output.preparation.followers.followers i
  let view := record.output.preparation.coordinator.downView
  let observation := record.output.preparation.feedback.observations
    (PublicDiscreteDraws.followerPlayer p.two_le_m i)
  have hout : record.output.followers i = record.output.preparation.observeFollower i := by
    rw [record.output_eq]; rfl
  rw [hout] at ho
  obtain ⟨choice0, memory0, post, hc0, hrecord, hrelease, _hi, _hd⟩ :=
    ReferenceFollowerReplyChronology.finishFollower_ordinary_inversion
      view prepared observation next nextMemory ho
  have heq := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj (hc0.symm.trans hc)
  rw [heq.1] at hrecord hrelease
  rw [heq.2] at hrelease
  have hstatus := occupied_record_status view prepared.follower prepared.row prepared.activation
    prepared.time prepared.active prepared.arm observation choice post hoccupied hrecord
  have hpostOccupied : post.status ≠ .unoccupied := by rw [hstatus]; exact hoccupied
  have hnextOccupied := release_finish_occupied prepared.follower prepared.row prepared.time
    observation choice post next memory nextMemory hpostOccupied hrelease
  have hframe := ReferenceFollowerReplyChronology.releaseAndFinish_frame prepared.follower
    prepared.row prepared.time observation choice post next memory nextMemory hrelease
  have hpostLast : post.lastDown = choice.lastDown := by
    have hlogged := hrecord
    rw [ReferenceActivePhysicalStep.recordFollower_result] at hlogged
    unfold ReferenceDownReception.loggingThenReferenceDown at hlogged
    simp only [dite_eq_right hoccupied] at hlogged
    unfold DeclaredFollowerLocalRound.recordOrServiceThenDown at hlogged
    simp only [dite_eq_right hoccupied] at hlogged
    cases hs : ActiveFollowerQueueOperation.checkedService rate.eta rate.sourceCap rate.n
        rate.n_scale prepared.follower prepared.row prepared.activation prepared.time observation choice with
    | failure => simp only [hs] at hlogged; cases hlogged
    | success result =>
      simp only [hs] at hlogged
      have heq : result.output = post := Except.ok.inj hlogged
      subst post
      rw [result.queueUpdate]
      exact (ActiveFollowerQueueOperation.serviceOutput_preserves_other_registers
        rate.n choice result.arrival).1
  exact ⟨hnextOccupied, (congrArg Prod.fst hframe.1).trans hpostLast⟩

private theorem actual_retained_down_live_output
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length) (i : Fin (p.m - 1))
    (M : OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (hretained : ReferenceAcceptedUpFollowerHistory.RetainedDown
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val] i M)
    (hbound : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[k.val].input.time.val + 1 <
      FollowerCutoffScan.firstCutoff p rate.eta.val (ActiveFollowerDownAcceptance.downStart p rate M)
        (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
          (ReferenceCompletePhysicalHistory.completeSuffixRecords
            rate z rewards C_star C_h)[k.val].input.row)) :
    ∃ after memory,
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[k.val].output.next.followers i = .ordinary after memory ∧
      after.status ≠ .unoccupied := by
  let r := (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val]
  obtain ⟨logged, cut, after, raw, scan, registers, lastService, hinput, hdown, haccepted⟩ := hretained
  have htransition := ReferenceFollowerSparseEmissionRecovery.actualAcceptedCut_downTransition
    r i logged cut after raw M scan registers lastService hinput hdown haccepted
  have hscan := ReferenceAssignmentFollowerMassSteps.accepted_down_scan_endpoint
    (r.output.preparation.followers.followers i).follower
    (r.output.preparation.followers.followers i).row
    (r.output.preparation.followers.followers i).time _ logged after raw M scan
    registers lastService htransition
  have halign := r.output.preparation.follower_alignment i
  rw [halign.1, halign.2.2.1] at hscan
  have hendpoint : scan.endpoint = r.input.time.val + 2 := by
    rw [hscan, Nat.min_eq_right (by exact Nat.succ_le_of_lt hbound)]
  obtain ⟨hstatus, memory, hnext, _htoken⟩ :=
    ReferenceCompleteFollowerContinuationKernel.accepted_down_successor_token (rate := rate)
      rewards C_star C_h z k i logged after cut raw M scan registers lastService hinput hdown haccepted
  refine ⟨after, memory, hnext, ?_⟩
  rw [hstatus, ite_eq_left hendpoint]
  exact ActiveRoundActions.FollowerStatus.noConfusion

private theorem actual_complete_current_live_phase
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length) (i : Fin (p.m - 1))
    (P : ReferenceActivePhysicalStep.Payload rate)
    (input choice : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hi : (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val].input.state.followers i =
      .ordinary input memory)
    (hs : ActiveFollowerLifecycle.startRound rate.eta
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val].input.time
      input memory = .ok (choice, memory))
    (hbound : (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val].input.time.val + 1 <
      FollowerCutoffScan.firstCutoff p rate.eta.val P.sigma
        (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
          (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val].input.row))
    (hcurrent : input.lastDown = some (P.downRecord i)) :
    input.status ≠ .unoccupied ∧ choice.status ≠ .unoccupied := by
  let r := (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val]
  have hphase := ReferenceCompleteFollowerCutoffPhase.complete_ordinary_follower_phase
    rate rewards C_star C_h z k i input memory hi (P.downRecord i) hcurrent
  have htoken := ReferenceCompleteFollowerCutoffPhase.complete_ordinary_follower_token
    rate rewards C_star C_h z k i input memory hi
  have hchoicePhase := ReferenceAssignmentFollowerMassSteps.start_round_cutoff_status
    r.input.time r.input.row input choice memory memory (P.downRecord i)
    hcurrent hphase htoken hs
  rw [downStart_current rate P i] at hphase hchoicePhase
  exact ⟨fun hu => (Nat.not_le_of_lt (lt_trans (Nat.lt_succ_self _) hbound)) (hphase.mp hu),
    fun hu => (Nat.not_le_of_lt hbound) (hchoicePhase.mp hu)⟩

private theorem actual_complete_current_live_output_occupied
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length) (i : Fin (p.m - 1))
    (P : ReferenceActivePhysicalStep.Payload rate)
    (choice next : ReferencePrelaunchFollower.State p rate.eta)
    (memory nextMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hc : (ReferenceFollowerFixedReply.actualChoice
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val] i).configuration =
        .ordinary choice memory)
    (ho : ((ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val].output.followers i).configuration =
      .ordinary next nextMemory)
    (hn : (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val].output.next.followers i =
      .ordinary next nextMemory)
    (hbound : (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val].input.time.val + 1 <
      FollowerCutoffScan.firstCutoff p rate.eta.val P.sigma
        (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
          (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val].input.row))
    (hchoiceCurrent : choice.lastDown = some (P.downRecord i) → choice.status ≠ .unoccupied)
    (hcurrent : next.lastDown = some (P.downRecord i)) :
    next.status ≠ .unoccupied := by
  let r := (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val]
  rcases actual_record_output_current_down_source rate r i next nextMemory
      ho (P.downRecord i) hcurrent with hretained | ⟨choice0, memory0, hc0, hld0⟩
  · have hcut := hbound
    rw [← downStart_current rate P i] at hcut
    obtain ⟨after, afterMemory, hafter, hafterOccupied⟩ := actual_retained_down_live_output
      rate rewards C_star C_h z k i (P.downRecord i) hretained hcut
    have heq := (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj (hafter.symm.trans hn)).1
    simpa only [heq] using hafterOccupied
  · have heq := (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj (hc0.symm.trans hc)).1
    rw [heq] at hld0
    exact (actual_record_occupied_choice_output_frame rate r i choice next memory nextMemory hc ho
      (hchoiceCurrent hld0)).1

/-- All ordinary CURRENT follower queues on the first corrected birth-plus-LIVE
slice use one actual full attributed word per follower. CURRENT is impossible
at birth INPUT/CHOICE and at every unoccupied LIVE query. The actual occupied
CHOICE-to-OUTPUT frame is retained even on the final physical record. -/
theorem actual_first_corrected_current_live_queues
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hz : z ∈ ReferenceFirstCollectionCorrectedSliceNumericalPrefix.correctedCell
      rate rewards C_star C_h u t) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let b := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.birthIndex rate rewards C_star C_h z
    let W := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.liveTail rate rewards C_star C_h z
    let V := (R.drop b).take (1 + W.length)
    ∃ (birth : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
      (P : ReferenceActivePhysicalStep.Payload rate) (A : Fin (p.m - 1) → List (Bool × ℕ)),
      R[b]? = some birth ∧
      ReferenceAssignmentPayloadPersistence.InstallationBirth birth P ∧ P.sigma = t ∧
      V = birth :: W ∧ b + V.length ≤ R.length ∧
      (t.val + 1 = p.T → b + 1 = R.length ∧ W = [] ∧ V.length = 1) ∧
      (∀ i, V.mapM (ReferenceFirstCorrectedAssignedArrivalPrefix.attributedArrival? P i) = some (A i)) ∧
      (∀ i, (A i).length = V.length) ∧
      (∀ i v, (V.take v).mapM
        (ReferenceFirstCorrectedAssignedArrivalPrefix.attributedArrival? P i) = some ((A i).take v)) ∧
      ∀ (i : Fin (p.m - 1)) (j : Fin V.length),
        ∃ input memory choice next nextMemory,
          R[b + j.val]? = some V[j.val] ∧
          V[j.val].input.state.followers i = .ordinary input memory ∧
          ActiveFollowerLifecycle.startRound rate.eta V[j.val].input.time input memory =
            .ok (choice, memory) ∧
          (ReferenceFollowerFixedReply.actualChoice V[j.val] i).configuration = .ordinary choice memory ∧
          (V[j.val].output.followers i).configuration = .ordinary next nextMemory ∧
          (V[j.val].output.followers i).failure = none ∧
          V[j.val].output.next.followers i = .ordinary next nextMemory ∧
          (j.val = 0 → input.lastDown ≠ some (P.downRecord i) ∧
            choice.lastDown ≠ some (P.downRecord i)) ∧
          (input.lastDown = some (P.downRecord i) →
            input.status ≠ .unoccupied ∧
            (input.S, input.backlog) = QueueReplay.replay (4 * rate.n)
              (0, (P.downRecord i).val.q) ((A i).take j.val)) ∧
          (choice.lastDown = some (P.downRecord i) →
            choice.status ≠ .unoccupied ∧
            (choice.S, choice.backlog) = QueueReplay.replay (4 * rate.n)
              (0, (P.downRecord i).val.q) ((A i).take j.val)) ∧
          (next.lastDown = some (P.downRecord i) →
            next.status ≠ .unoccupied ∧
            (next.S, next.backlog) = QueueReplay.replay (4 * rate.n)
              (0, (P.downRecord i).val.q) ((A i).take (j.val + 1))) ∧
          (choice.status ≠ .unoccupied →
            next.status ≠ .unoccupied ∧ next.lastDown = choice.lastDown) := by
  classical
  intro R b W V
  obtain ⟨_L, _c, birth, P, _base, _hL, _hc, _hpref, _hlen, hb, hborn,
      hsigma, _hqueues, _hbase, hV, hbound, hterminal, hqueries,
      _hcutoff, hwords, _hcurrentEnd⟩ :=
    ReferenceFirstCorrectedCurrentCutoffReplyRetention.actual_first_corrected_current_cutoff_reply_retention
      rate rewards C_star C_h u t z hz
  change V = birth :: W at hV
  change b + (1 + W.length) ≤ R.length at hbound
  change ∀ i : Fin (p.m - 1), ∀ v, v ≤ 1 + W.length → ∃! word,
    (V.take v).mapM (ReferenceFirstCorrectedAssignedArrivalPrefix.attributedArrival? P i) = some word at hwords
  clear _hL _hc _hpref _hlen _hqueues _hbase _hcutoff _hcurrentEnd _base _L _c
  have hVlen : V.length = 1 + W.length := by
    rw [hV, List.length_cons]
    omega
  have hfull : ∀ i : Fin (p.m - 1), ∃ word,
      V.mapM (ReferenceFirstCorrectedAssignedArrivalPrefix.attributedArrival? P i) = some word := by
    intro i
    obtain ⟨word, hw, _hunique⟩ := hwords i (1 + W.length) (le_rfl)
    rw [← hVlen, List.take_length] at hw
    exact ⟨word, hw⟩
  choose A hA using hfull
  have hAtake : ∀ i v, (V.take v).mapM
      (ReferenceFirstCorrectedAssignedArrivalPrefix.attributedArrival? P i) = some ((A i).take v) := by
    intro i v
    exact mapM_take_of_some _ V (A i) (hA i) v
  have hcutoff := actual_live_cutoff_bound rate rewards C_star C_h u t z hz birth P hb hborn
  rw [← hV] at hcutoff
  refine ⟨birth, P, A, hb, hborn, hsigma, hV, by omega, hterminal, hA,
    (fun i => (mapM_length_of_some _ V (A i) (hA i)).symm), hAtake, ?_⟩
  intro i j
  obtain ⟨input, memory, choice, next, nextMemory, hrecord, hinput, hstart,
    hchoice, houtput, hfailure, hnext, hbirthInput, hinputNumeric,
    houtputNumeric, _hadj⟩ := hqueries i j.val j.isLt
  have hindex : b + j.val < R.length := (List.getElem?_eq_some_iff.mp hrecord).1
  have hslice : R[b + j.val] = V[j.val] := (List.getElem?_eq_some_iff.mp hrecord).2
  let k : Fin R.length := ⟨b + j.val, hindex⟩
  have hinputR : R[k.val].input.state.followers i = .ordinary input memory := by
    simpa only [k, hslice] using hinput
  obtain ⟨before, beforeMemory, hbefore, hreply, hunoccupied⟩ :=
    ReferenceFollowerReplyChronology.record_input_to_choice V[j.val] i choice memory hchoice
  have heq := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj (hbefore.symm.trans hinput)
  rw [heq.1] at hreply hunoccupied
  have hlast : choice.lastDown = input.lastDown := congrArg Prod.fst hreply
  have hregisters : (choice.S, choice.backlog) = (input.S, input.backlog) :=
    Prod.ext (congrArg (fun r => r.2.1) hreply) (congrArg (fun r => r.2.2.2) hreply)
  have hcutR : R[k.val].input.time.val + 1 < FollowerCutoffScan.firstCutoff p rate.eta.val P.sigma
      (FollowerCutoffScan.completeRowProposalBit p rate.eta.val R[k.val].input.row) := by
    dsimp only [k]
    rw [hslice]
    exact hcutoff j.val j.isLt
  have hstartR : ActiveFollowerLifecycle.startRound rate.eta R[k.val].input.time input memory =
      .ok (choice, memory) := by
    dsimp only [k]
    rw [hslice]
    exact hstart
  have hphase := actual_complete_current_live_phase rate rewards C_star C_h z k i P input choice
    memory hinputR hstartR hcutR
  have hinputReplay : input.lastDown = some (P.downRecord i) →
      input.status ≠ .unoccupied ∧ (input.S, input.backlog) =
        QueueReplay.replay (4 * rate.n) (0, (P.downRecord i).val.q) ((A i).take j.val) := by
    intro hcurrent
    have hoccupied := (hphase hcurrent).1
    have hpos : 1 ≤ j.val := by
      by_contra hnot
      exact hoccupied (hbirthInput (by omega))
    obtain ⟨word, hw, _hdown, hreplay⟩ := hinputNumeric hpos hoccupied
    have heq : word = (A i).take j.val := Option.some.inj (hw.symm.trans (hAtake i j.val))
    exact ⟨hoccupied, by simpa only [heq] using hreplay⟩
  have hchoiceReplay : choice.lastDown = some (P.downRecord i) →
      choice.status ≠ .unoccupied ∧ (choice.S, choice.backlog) =
        QueueReplay.replay (4 * rate.n) (0, (P.downRecord i).val.q) ((A i).take j.val) := by
    intro hcurrent
    have hinputCurrent := hlast.symm.trans hcurrent
    exact ⟨(hphase hinputCurrent).2, hregisters.trans (hinputReplay hinputCurrent).2⟩
  have hframe := actual_record_occupied_choice_output_frame rate V[j.val] i choice next
    memory nextMemory hchoice houtput
  have houtputReplay : next.lastDown = some (P.downRecord i) →
      next.status ≠ .unoccupied ∧ (next.S, next.backlog) =
        QueueReplay.replay (4 * rate.n) (0, (P.downRecord i).val.q) ((A i).take (j.val + 1)) := by
    intro hcurrent
    have hcR : (ReferenceFollowerFixedReply.actualChoice R[k.val] i).configuration =
        .ordinary choice memory := by
      dsimp only [k]
      rw [hslice]
      exact hchoice
    have hoR : (R[k.val].output.followers i).configuration = .ordinary next nextMemory := by
      dsimp only [k]
      rw [hslice]
      exact houtput
    have hnR : R[k.val].output.next.followers i = .ordinary next nextMemory := by
      dsimp only [k]
      rw [hslice]
      exact hnext
    have hoccupied := actual_complete_current_live_output_occupied rate rewards C_star C_h z k i P
      choice next memory nextMemory hcR hoR hnR hcutR (fun h => (hchoiceReplay h).1) hcurrent
    obtain ⟨word, hw, _hdown, hreplay, _hdelta⟩ := houtputNumeric hoccupied
    have heq : word = (A i).take (j.val + 1) :=
      Option.some.inj (hw.symm.trans (hAtake i (j.val + 1)))
    exact ⟨hoccupied, by simpa only [heq] using hreplay⟩
  refine ⟨input, memory, choice, next, nextMemory, hrecord, hinput, hstart, hchoice,
    houtput, hfailure, hnext, ?_, hinputReplay, hchoiceReplay, houtputReplay, hframe⟩
  intro hj0
  have hcAbs : choice.lastDown ≠ some (P.downRecord i) := by
    intro hcurrent
    have hcR : (ReferenceFollowerFixedReply.actualChoice R[k.val] i).configuration =
        .ordinary choice memory := by
      dsimp only [k]
      rw [hslice]
      exact hchoice
    obtain ⟨a, hba, hak, _ha⟩ := actual_current_choice_down_source
      rate rewards C_star C_h u t z hz b birth P hb hborn k i choice memory hcR hcurrent
    change a.val < b + j.val at hak
    omega
  exact ⟨fun h => hcAbs (hlast.trans h), hcAbs⟩

end Bandits.Support.ReferenceFirstCorrectedCurrentFollowerLiveQueue

end
