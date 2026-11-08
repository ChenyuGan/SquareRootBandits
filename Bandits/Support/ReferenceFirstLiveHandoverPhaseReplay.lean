/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveHandoverSnapshotPrefix

/-!
# Actual first-handover incoming decoder observations

Sources: ZIP4 `05_binary_transport.tex:244-281`,
`06_interruptions.tex:246-299,431-440`, and
`appendix_a_local_protocol.tex:100-108,141-157`.

The calendar is exactly the snapshot-prefix auxiliary continuation. These
internal producers do not define another physical run or a service count.
Incoming correspondence includes a detecting update; it must not be extended
to outgoing physical registers after a false accepted decision.

The results connect the actual incoming phase and full awaiting bank to the
same stopped replay and identify its per-date service. They retain detecting
updates and do not assert a physical total, quota, waiting cost or manuscript
handover theorem.
-/

@[expose] public section

noncomputable section

open Bandits.Support ConstructorDimensions
open ReferenceFirstLiveHandoverSnapshotPrefix
open ReferenceFirstLiveSourceStoppedHandoverEndpoint HandoverStoppedDecoderReplay
open ReferenceFollowerDownDecoderReplay ReferenceFirstLiveDownCompletionReadout
open ActiveFollowerDownAcceptance ReferenceDownReception
open ReferencePrelaunchFollower (State acceptedStart codecParams)
open OrdinaryMessageCodec (acceptDown)
open ReferenceSourcePrefixHistoryFiltration (actualRecord)
open ReferenceFirstWindowNumericalStream (actualFirstLiveSeed)
open ReferenceActivePhysicalHorizon (RoundRecord)
open scoped Classical

namespace Bandits.Support.ReferenceFirstLiveHandoverPhaseReplay

variable {p : ConstructorDimensions.Parameters}

private theorem decoderInput_ext {B : ℕ} (left right : AffineBatchDecoder.RoundInput B)
    (hs : left.selected = right.selected) (he : left.receiverEnabled = right.receiverEnabled)
    (ha : left.sample = right.sample) (hr : left.roundedReward = right.roundedReward) : left = right := by
  cases left
  cases right
  congr 1

/-- All strictly pre-fixation dates are inert, for every initial bank and
every supplied calendar, including calendars with external stop flags. -/
theorem snapshotBefore_at_or_before_fixing (beta : ℝ) (a : ActiveRoundActions.Assignment p.m p.K)
    (data : Fin p.T → RoundData p a) (i : ActiveRoundActions.Follower p.m) (fixing : Fin p.T)
    (M : Down p beta) (initial : LocalState p) (n : ℕ) (hn : n ≤ fixing.val) :
    snapshotBefore p beta a data i fixing M initial n = initial := by
  have inert : ∀ (ts : List (Fin p.T)), (∀ t ∈ ts, t.val < fixing.val) →
      run p beta a data i fixing M ts initial = initial := by
    intro ts
    induction ts with
    | nil => intro _; rfl
    | cons t ts ih =>
        intro ht
        have hstep : roundStep p beta a data i fixing M initial t = initial :=
          ite_eq_left (Or.inl (ht t (by simp only [List.mem_cons, true_or])))
        rw [run, hstep]
        exact ih (fun u hu => ht u (List.mem_cons_of_mem t hu))
  exact inert _ (fun t ht => lt_of_lt_of_le ((AffineBatchDecoder.mem_roundPrefix p n t).mp ht) hn)

/-- The next chronological replay snapshot performs exactly the current update. -/
theorem snapshotBefore_succ
    (beta : ℝ) (a : ActiveRoundActions.Assignment p.m p.K) (calendar : Fin p.T → RoundData p a)
    (i : ActiveRoundActions.Follower p.m) (fixing : Fin p.T) (M : Down p beta)
    (seed : LocalState p) (t : Fin p.T) : snapshotBefore p beta a calendar i fixing M seed (t.val + 1) =
      roundStep p beta a calendar i fixing M (snapshotBefore p beta a calendar i fixing M seed t.val) t := by
  have hp : AffineBatchDecoder.roundPrefix p (t.val + 1) =
      AffineBatchDecoder.roundPrefix p t.val ++ [t] := by
    apply List.Pairwise.eq_of_mem_iff (r := (· < ·)) (AffineBatchDecoder.roundPrefix_pairwise p (t.val + 1))
    · rw [List.pairwise_append]
      refine ⟨AffineBatchDecoder.roundPrefix_pairwise p t.val, by simp only [List.pairwise_singleton], ?_⟩
      intro u hu v hv
      rw [List.mem_singleton] at hv
      subst v
      exact (AffineBatchDecoder.mem_roundPrefix p t.val u).mp hu
    · intro u
      simp only [AffineBatchDecoder.mem_roundPrefix, List.mem_append, List.mem_singleton]
      constructor
      · intro hu
        by_cases he : u.val = t.val
        · exact Or.inr (Fin.ext he)
        · exact Or.inl (by omega)
      · rintro (hu | rfl) <;> omega
  rw [snapshotBefore, hp, run_append]
  rfl

private theorem finish_missing_iff
    {a : ActiveRoundActions.Assignment p.m p.K} (A : ActiveRoundActions.Snapshot a)
    (input : ActiveRoundActions.RoundInput a (AffineBatchDecoder.width p))
    (row : ActiveRoundActions.RewardRow p.K) (flags : ActiveRoundActions.Follower p.m → Bool)
    (i : ActiveRoundActions.Follower p.m) :
    i ∈ (ActiveRoundActions.finishLiveRound p.two_le_m A input row flags).missing ↔
      i ∈ A.missing ∧ ¬ ActiveRoundActions.confirmation p.two_le_m A input row i := by
  change i ∈ (if ActiveRoundActions.confirmation p.two_le_m A input row input.selected then
    A.missing.erase input.selected else A.missing) ↔ _
  by_cases hc : ActiveRoundActions.confirmation p.two_le_m A input row input.selected
  · have hi : ActiveRoundActions.confirmation p.two_le_m A input row i ↔ input.selected = i :=
      ⟨fun h => h.2.1, fun h => h ▸ hc⟩
    simp only [hc, ite_true, Finset.mem_erase, hi]; tauto
  · have hi : ¬ ActiveRoundActions.confirmation p.two_le_m A input row i := fun h => hc (h.2.1.symm ▸ h)
    simp only [hc, ite_false, hi, not_false_eq_true, and_true]

/-- The existing DOWN parser checks exact re-encoding, so even a successful
parse to the SAME record cannot hide a different returned raw word. -/
theorem parseOutput_eq_some_iff (beta : ℝ) (M : Down p beta)
    (raw : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p))) :
    parseOutput p beta raw = some M ↔ raw = some (currentWord p beta M) := by
  constructor
  · intro h
    cases raw with
    | none => rw [parseOutput_none] at h; cases h
    | some w =>
        have hparse : OrdinaryMessageCodec.parseDown (AffineBatchDecoder.codecParams p beta)
            (some ((OrdinaryMessageCodec.wordEquivFlat (AffineBatchDecoder.codecParams p beta)).symm w)) = some M := h
        have hword := OrdinaryMessageCodec.parseDown_some_sound _ hparse
        simpa only [currentWord, Equiv.apply_symm_apply] using congrArg some
          (congrArg (OrdinaryMessageCodec.wordEquivFlat (AffineBatchDecoder.codecParams p beta)) hword)
  · intro h
    rw [h]
    exact parseOutput_currentWord p beta M

section ActualSource

variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p) (n : ℕ)
  (payload : ReferenceActivePhysicalStep.Payload rate)
  (hp : payload0 rate rewards C_star C_h z = some payload)

local notation "W" => window rate rewards C_star C_h z
local notation "s₀" => start rate rewards C_star C_h z
local notation "m₀" => stop rate rewards C_star C_h z n
local notation "supportedDates" => supportDates rate rewards C_star C_h z
local notation "pendingAt(" t ")" => pendingNat rate rewards C_star C_h t z

/-- Original controls on the actual first-live window. -/
theorem actual_auxiliary_row (k : Fin (W).length) (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true) :
    ((W).get k).input.row = z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) := by
  obtain ⟨_, _, _, _, _, _, hrows, hJ, _⟩ := actual_window_frame rate rewards C_star C_h z hc k
  simp only [ReferenceActivePhysicalStep.RoundInput.row, hrows, hJ]

/-- On padding, both branches of the SAME replay service variable vanish,
irrespective of its incoming phase. No physical statistic is introduced. -/
theorem padding_X_zero (overflowAfter : Fin p.T → Bool) (i : ActiveRoundActions.Follower p.m)
    (incoming : LocalState p) (t : Fin p.T) (hout : t.val < s₀ ∨ m₀ ≤ t.val) :
    let data := fromLive p payload.assignment
      (auxiliaryLive rate rewards C_star C_h z n payload hp) (fun _ => false) overflowAfter
    X p payload.assignment data i incoming t = 0 := by
  dsimp only
  have hrow := (auxiliaryLive_padding rate rewards C_star C_h z n payload hp t hout).1
  have hz : ∀ player, ActiveRoundActions.feedback p.two_le_m
      (ActiveObservationBridge.liveSnapshotBefore p payload.assignment
        (auxiliaryLive rate rewards C_star C_h z n payload hp) t)
      (auxiliaryLive rate rewards C_star C_h z n payload hp t).input
      (auxiliaryLive rate rewards C_star C_h z n payload hp t).rewards player = 0 := by
    intro player
    rw [hrow, feedback_zero]
  have hel : ¬ AffineBatchDecoder.eligible (observationTrace p payload.assignment
      (fromLive p payload.assignment (auxiliaryLive rate rewards C_star C_h z n payload hp)
        (fun _ => false) overflowAfter) i t) := by
    rintro ⟨_, _, hpos⟩
    exact (not_lt_of_ge (le_of_eq (hz _))) hpos
  have hc : ¬ physicalConfirmation p payload.assignment
      (fromLive p payload.assignment (auxiliaryLive rate rewards C_star C_h z n payload hp)
        (fun _ => false) overflowAfter) i t := by
    rintro ⟨_, _, _, _, hpos⟩
    exact (not_lt_of_ge (le_of_eq (hz _))) hpos
  cases hphase : incoming.phase <;>
    simp only [X, hphase, hel, hc, ite_false]

/-- The entire current decoder input agrees on an actual selected awaiting
receiver. This does not identify inputs at other retained timestamps. -/
theorem actual_selected_decoder_input (overflowAfter : Fin p.T → Bool) (k : Fin (W).length)
    (hd : ((W).get k).input.time.val + 1 ∈ supportedDates) (ht : ((W).get k).input.time.val < m₀)
    (i : ActiveRoundActions.Follower p.m) (hi : i ∈ pendingAt(((W).get k).input.time.val))
    (hdown : (auxiliaryInput payload z ((W).get k).input.time).slot = PublicDiscreteDraws.downSlot)
    (hdraw : (auxiliaryInput payload z ((W).get k).input.time).selected = i) (incoming : State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hin : ((W).get k).input.state.followers i = .ordinary incoming memory)
    (hnone : incoming.lastDown = none) :
    let r := (W).get k
    let data := fromLive p payload.assignment
      (auxiliaryLive rate rewards C_star C_h z n payload hp) (fun _ => false) overflowAfter
    observationTrace p payload.assignment data i r.input.time =
      currentRoundInput p i r.input.row r.input.time (preparedOwnObservation r i) rate incoming := by
  dsimp only
  let r := (W).get k
  have hc := crossing_of_support rate rewards C_star C_h z (r.input.time.val + 1) hd
  obtain ⟨selected, states, memories, hsel, _, hpselected, _, _, _, hstates, _, hnoneIff, _⟩ :=
    actual_window_frame rate rewards C_star C_h z hc k
  have hrow := actual_auxiliary_row rate rewards C_star C_h z k hc
  have hstateEq : states i = incoming :=
    (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj ((hstates i).symm.trans hin)).1
  have hu : incoming.status = .unoccupied := by
    rw [← hstateEq]
    exact (hnoneIff i).mpr (hstateEq.symm ▸ hnone)
  have hproj := window_snapshot_projection rate rewards C_star C_h z n hc payload hp k hd ht
  have hmissing : i ∈ (ActiveObservationBridge.liveSnapshotBefore p payload.assignment
      (auxiliaryLive rate rewards C_star C_h z n payload hp) r.input.time).missing := by
    rw [hproj.1]
    have hm := pendingNat_eq_window_missing rate rewards C_star C_h z k hd
    exact hm ▸ hi
  have hstatus : (ActiveObservationBridge.liveSnapshotBefore p payload.assignment
      (auxiliaryLive rate rewards C_star C_h z n payload hp) r.input.time).status i = .unoccupied :=
    (hproj.2 i incoming memory hin).trans hu
  have hdown' : PublicDiscreteDraws.slotDraw (r.input.row.2 r.input.time).1 = PublicDiscreteDraws.downSlot := by
    rw [hrow]
    exact hdown
  have hdraw' : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
      (r.input.row.2 r.input.time).1 = i := by
    rw [hrow]
    exact hdraw
  have hpay : selected.view.payload = payload := Option.some.inj (hpselected.symm.trans hp)
  have hmissingPhysical : missing rate r = selected.view.pendingAtChoice := by
    unfold missing actualSelection
    rw [hsel]
    rfl
  have hpend : i ∈ selected.view.pendingAtChoice := by
    rw [← hmissingPhysical]
    exact (pendingNat_eq_window_missing rate rewards C_star C_h z k hd) ▸ hi
  apply decoderInput_ext
  · calc
      _ = true := @decide_eq_true _ _ ⟨hdown, hdraw, hmissing⟩
      _ = _ := (@decide_eq_true _
        (@instDecidableAnd _ _ inferInstance (Classical.propDecidable _)) ⟨hdown', hdraw'⟩).symm
  · calc
      _ = true := @decide_eq_true _ _ hstatus
      _ = _ := (@decide_eq_true _ _ hu).symm
  · change ((z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)).2 r.input.time).2
      (0, (auxiliaryInput payload z r.input.time).selected) = (r.input.row.2 r.input.time).2 (0, i)
    rw [hdraw, hrow]
  · have hs : s₀ ≤ r.input.time.val := by
      have hh := (source_window_record_calendar rate rewards C_star C_h z k).1
      change r.input.time.val = s₀ + k.val at hh
      omega
    have hentry := auxiliaryLive_on_prefix rate rewards C_star C_h z n payload hp r.input.time hs ht r
      (source_window_record_calendar rate rewards C_star C_h z k).2
    have hphysical := ReferenceFirstLiveHandoverDownFeedback.actual_first_live_before_down_feedback
      rate rewards C_star C_h z r.input.time r (source_window_record_calendar rate rewards C_star C_h z k).2
      (List.get_mem _ _) selected hsel i hpend hdown' hdraw' ⟨incoming, memory, hin, hnone⟩
    have hmodel := ActiveRoundActions.unoccupied_down_feedback p.two_le_m
      (ActiveObservationBridge.liveSnapshotBefore p payload.assignment
        (auxiliaryLive rate rewards C_star C_h z n payload hp) r.input.time)
      (auxiliaryInput payload z r.input.time)
      (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards r.input.time) hdown
      (by rw [hdraw]; exact hmissing)
      (ActiveRoundActions.liveSegment_no_released p.two_le_m _) (by rw [hdraw]; exact hstatus)
    change ActiveRoundActions.feedback p.two_le_m
      (ActiveObservationBridge.liveSnapshotBefore p payload.assignment
        (auxiliaryLive rate rewards C_star C_h z n payload hp) r.input.time)
      (auxiliaryLive rate rewards C_star C_h z n payload hp r.input.time).input
      (auxiliaryLive rate rewards C_star C_h z n payload hp r.input.time).rewards
      (PublicDiscreteDraws.followerPlayer p.two_le_m i) = _
    rw [hentry.1]
    change ActiveRoundActions.feedback _ _ (auxiliaryInput payload z r.input.time) _ _ = _
    rw [← hdraw, hmodel]
    rw [hdraw]
    change _ = (r.output.preparation.feedback.observations
      (PublicDiscreteDraws.followerPlayer p.two_le_m i)).val.val
    rw [hphysical, hpay, hrow]
    rw [auxiliaryInput_down_bit, hdraw]
    rfl

/-- Safety of every normal induction predecessor is a CONSEQUENCE of the
later supported date. The current detecting update is deliberately excluded
from this strict predecessor statement. -/
theorem supported_strict_predecessor_safe (k j : Fin (W).length) (hjk : j.val < k.val)
    (hk : ((W).get k).input.time.val + 1 ∈ supportedDates) :
    let r := (W).get j
    ReferenceFirstLiveDecoderPastMeasurability.retainedDecoderRecordFlag (s₀) r = false ∧
    (∀ (i : Fin (p.m - 1)) (cut : ReferenceDownCutOutput p rate),
      (r.output.followers i).down = some cut → ¬ wrongUniqueAccepted cut) ∧
    (∀ i : Fin (p.m - 1), ¬ completedAmbiguousAfterStart (s₀) r i) ∧
    ReferenceFirstLiveOverflowReadout.wholeFirstLiveOverflowRound rate rewards C_star C_h z ≠
      some (r.input.time.val + 1) := by
  dsimp only
  let r := (W).get j
  have hj := supported_predecessors rate rewards C_star C_h z k j hjk.le hk
  have htj := (source_window_record_calendar rate rewards C_star C_h z j).1
  have htk := (source_window_record_calendar rate rewards C_star C_h z k).1
  have htimes : r.input.time.val < ((W).get k).input.time.val := by
    change r.input.time.val = s₀ + j.val at htj
    change ((W).get k).input.time.val = s₀ + k.val at htk
    omega
  have hflag : ReferenceFirstLiveDecoderPastMeasurability.retainedDecoderRecordFlag (s₀) r = false := by
    apply Bool.eq_false_iff.mpr
    intro hf
    have hend := source_window_decoder_detection_endpoint rate rewards C_star C_h z j hj hf
    have hupper : ((W).get k).input.time.val + 1 < theta rate rewards C_star C_h z :=
      (Finset.mem_Ico.mp (supportDates_subset_interval rate rewards C_star C_h z hk)).2
    change theta rate rewards C_star C_h z = r.input.time.val + 2 at hend
    omega
  have hnot := Bool.eq_false_iff.mp hflag
  have hbad := ReferenceFirstLiveDecoderPastMeasurability.retainedDecoderRecordFlag_eq_true_iff (s₀) r
  refine ⟨hflag, ?_, ?_, ?_⟩
  · intro i cut hcut hwrong
    apply hnot
    apply hbad.mpr
    left
    exact of_decide_eq_true (show decide
      (ReferenceActiveStoppedPrefixCoupling.saved_wrong_unique_accepted r) = true from
        decide_eq_true (Or.inr ⟨i, cut, hcut, hwrong⟩))
  · intro i hamb
    exact hnot (hbad.mpr (Or.inr ⟨i, hamb⟩))
  · intro hover
    have hend := overflow_detection_endpoint rate rewards C_star C_h z (r.input.time.val + 1) hover hj
    have hupper : ((W).get k).input.time.val + 1 < theta rate rewards C_star C_h z :=
      (Finset.mem_Ico.mp (supportDates_subset_interval rate rewards C_star C_h z hk)).2
    omega

private theorem positiveEntry_origin {rate : ReferenceActivePhysicalStep.RateInput p} (i : Fin (p.m - 1))
    (records : List (RoundRecord (p := p) (rate := rate))) (e : DecoderEntry p)
    (he : e ∈ actualDownPositives i records) : ∃ (r : RoundRecord (p := p) (rate := rate)) (call : Call p),
      r ∈ records ∧ actualDownCall i r = some call ∧
      AffineBatchDecoder.eligible call.2 ∧ e = ⟨call.1, call.2.sample⟩ := by
  obtain ⟨call, hcall, hentry⟩ := List.mem_flatMap.mp he
  obtain ⟨r, hr, hcall⟩ := List.mem_filterMap.mp hcall
  by_cases hel : AffineBatchDecoder.eligible call.2
  · have heq : e = ⟨call.1, call.2.sample⟩ := by
      simpa only [AffineBatchDecoder.positiveAt, currentInputExtension,
        hel, ite_true, List.mem_singleton, AffineBatchDecoder.entry] using hentry
    exact ⟨r, call, hr, hcall, hel, heq⟩
  · simp only [AffineBatchDecoder.positiveAt, currentInputExtension, hel, ite_false, List.not_mem_nil] at hentry

local notation "β" => CanonicalRecordingRates.beta p rate.eta.val
local notation "L" => auxiliaryLive rate rewards C_star C_h z n payload hp
local notation "actualOverflowAfter" => (fun t : Fin p.T =>
  decide (ReferenceFirstLiveOverflowReadout.wholeFirstLiveOverflowRound
    rate rewards C_star C_h z = some (Fin.val t + 1)))
local notation "data" => fromLive p payload.assignment L (fun _ => false) actualOverflowAfter
local notation "replay[" i "," f "]" => snapshotBefore p β payload.assignment data i f (payload.downRecord i)
local notation "serve[" i "," f "]" => serviceStep p β payload.assignment data i f (payload.downRecord i)
local notation "advance[" i "," f "]" => roundStep p β payload.assignment data i f (payload.downRecord i)

/-- Each retained postlaunch positive equation is checked at ITS OWN time.
Earlier pending membership and support are derived from the actual current
task. This statement includes the current detecting observation. -/
theorem actual_positive_entry_correspondence (k : Fin (W).length)
    (hd : ((W).get k).input.time.val + 1 ∈ supportedDates) (ht : ((W).get k).input.time.val < m₀)
    (i : ActiveRoundActions.Follower p.m) (hi : i ∈ pendingAt(((W).get k).input.time.val))
    (e : DecoderEntry p) (he : e ∈ actualDownPositives i ((W).take (k.val + 1))) :
    s₀ ≤ e.time.val ∧ e.time.val ≤ ((W).get k).input.time.val ∧
      AffineBatchDecoder.eligible (observationTrace p payload.assignment data i e.time) ∧
      e.sample = (data e.time).input.down.sample ∧ (data e.time).input.down.word = currentWord p
        β (payload.downRecord i) := by
  obtain ⟨r, call, hr, hcall, hel, heq⟩ := positiveEntry_origin i _ e he
  obtain ⟨j, hj, hrj⟩ := List.mem_take_iff_getElem.mp hr
  have hjW : j < (W).length := lt_of_lt_of_le hj (min_le_right _ _)
  have hjk : j ≤ k.val := by have := (lt_of_lt_of_le hj (min_le_left _ _)); omega
  let jf : Fin (W).length := ⟨j, hjW⟩
  have hrj' : r = (W).get jf := hrj.symm
  subst r
  let r := (W).get jf
  have hds := supported_predecessors rate rewards C_star C_h z k jf hjk hd
  have htk := (source_window_record_calendar rate rewards C_star C_h z k).1
  have htj := (source_window_record_calendar rate rewards C_star C_h z jf).1
  change ((W).get k).input.time.val = s₀ + k.val at htk
  change r.input.time.val = s₀ + j at htj
  have hle : r.input.time.val ≤ ((W).get k).input.time.val := by omega
  have hts : r.input.time.val < m₀ := hle.trans_lt ht
  have hc := crossing_of_support rate rewards C_star C_h z (r.input.time.val + 1) hds
  obtain ⟨_, states, memories, _, _, _, _, _, _, hin, hchoice, hnoneIff, _⟩ :=
    actual_window_frame rate rewards C_star C_h z hc jf
  have hcall' := actualDownCall_ordinary r i (states i) (memories i) (hchoice i)
  have hcallEq := Option.some.inj (hcall.symm.trans hcall')
  have hinput : call.2 = currentRoundInput p i r.input.row r.input.time
      (preparedOwnObservation r i) rate (states i) := by
    have h := congrArg Prod.snd hcallEq
    change call.2 = currentRoundInput p i (r.output.preparation.followers.followers i).row
      (r.output.preparation.followers.followers i).time (preparedOwnObservation r i) rate (states i) at h
    rw [(r.output.preparation.follower_alignment i).1,
      (r.output.preparation.follower_alignment i).2.2.1] at h
    exact h
  have hel' := hinput ▸ hel
  obtain ⟨hdown, hu, _⟩ := (currentRoundInput_eligible_iff
    p i r.input.row r.input.time (preparedOwnObservation r i) rate (states i)).mp hel'
  have hnone := (hnoneIff i).mp hu
  have hfields := ReferenceDownCompletedAmbiguityMeasurability.actualDownCall_fields r i call hcall
  have hetime : e.time = r.input.time := (congrArg AffineBatchDecoder.Entry.time heq).trans hfields.1
  have hip := pendingNat_antitone
    rate rewards C_star C_h z r.input.time.val ((W).get k).input.time.val hle ((W).get k).input.time.isLt
    (Finset.mem_Ico.mp (supportDates_subset_interval rate rewards C_star C_h z hds)).1
    (Finset.mem_Ico.mp (supportDates_subset_interval rate rewards C_star C_h z hd)).2 hi
  have hrows := (actual_window_frame rate rewards C_star C_h z hc jf)
  obtain ⟨_, _, _, _, _, _, hrows, hJ, _⟩ := hrows
  have hrow := actual_auxiliary_row rate rewards C_star C_h z jf hc
  rw [hrow] at hdown
  have hdraw : (auxiliaryInput payload z r.input.time).selected = i := hdown.2
  have hactual := actual_selected_decoder_input rate rewards C_star C_h z n payload hp actualOverflowAfter
    jf hds hts i hip hdown.1 hdraw (states i) (memories i) (hin i) hnone
  rw [hetime]
  refine ⟨by omega, hle, ?_, ?_, ?_⟩
  · rw [hactual]
    exact hel'
  · have hs : e.sample = call.2.sample := congrArg AffineBatchDecoder.Entry.sample heq
    rw [hs, hfields.2.1]
    change (r.input.row.2 r.input.time).2 (0, i) =
      ((z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)).2 r.input.time).2
        (0, (auxiliaryInput payload z r.input.time).selected)
    rw [hrow, hdraw]
  · change (auxiliaryInput payload z r.input.time).down.word = _
    rw [auxiliaryInput_decoder_word, hdraw]

private theorem actual_completed_entry_origin_iff (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true)
    (k : Fin (W).length) (i : Fin (p.m - 1)) (B : List (DecoderEntry p))
    (hB : completedDownBatch ((W).get k) i = some B) :
    ∀ e ∈ B, s₀ ≤ e.time.val ↔ e ∈ actualDownPositives i ((W).take (k.val + 1)) := by
  let s := s₀
  let count := p.T - s
  have hs : s ≤ p.T := ReferenceCompletePhysicalHistory.physicalStart_le_T rate z rewards C_star C_h
  have hspan : s + count ≤ p.T := by dsimp only [count]; omega
  let physicalSeed := ReferenceLocalReleaseGateChronology.sourceSeed rate z rewards C_star C_h hc
  let R := ReferenceLocalReleaseGateChronology.sourceRun rate z rewards C_star C_h hc s count rfl hspan
  have hcomplete : R.records = completeRecords rate rewards C_star C_h z :=
    (ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch rate z rewards C_star C_h physicalSeed
      (ReferenceLocalReleaseGateChronology.sourceSeed_launch rate z rewards C_star C_h hc)).symm
  have hwindow : ReferenceFirstLiveConfirmationHistory.firstLiveWindow R.records = W := by
    rw [hcomplete]
    rfl
  have hprefix : (W).IsPrefix R.records := by
    rw [← hwindow]
    exact List.takeWhile_prefix _
  have htake : (W).take (k.val + 1) = R.records.take (k.val + 1) := by
    obtain ⟨tail, htail⟩ := hprefix
    rw [← htail, List.take_append_of_le_length (by have := k.isLt; omega)]
  have horig := actual_first_live_batch_origins rate z rewards C_star C_h count hc hspan
  change ∀ (j : Fin (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R.records).length)
    (i : Fin (p.m - 1)) (B : Batch p),
    completedDownBatch (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R.records)[j.val] i = some B →
    ∀ e ∈ B, s ≤ e.time.val ↔ e ∈ actualDownPositives i (R.records.take (j.val + 1)) at horig
  have hk : k.val < (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R.records).length := by
    rw [hwindow]
    exact k.isLt
  have hrecord : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R.records)[k.val] = (W).get k := by
    apply Option.some.inj
    calc _ = (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R.records)[k.val]? :=
        (List.getElem?_eq_getElem hk).symm
      _ = (W)[k.val]? := congrArg (fun records => records[k.val]?) hwindow
      _ = _ := List.getElem?_eq_getElem k.isLt
  have hB' : completedDownBatch
      (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R.records)[k.val] i = some B := by
    rw [hrecord]
    exact hB
  rw [htake]
  exact horig ⟨k.val, hk⟩ i B hB'

/-- Exact WHOLE-batch agreement on an actual completion. Every inherited
entry is retained in `B`; the equivalence discards none of its timestamps. -/
theorem actual_completed_wholeCurrentBatch_iff (k : Fin (W).length)
    (hd : ((W).get k).input.time.val + 1 ∈ supportedDates) (ht : ((W).get k).input.time.val < m₀)
    (i : ActiveRoundActions.Follower p.m) (hi : i ∈ pendingAt(((W).get k).input.time.val))
    (fixing : Fin p.T) (hfixing : fixing.val = s₀) (B : List (DecoderEntry p))
    (hB : completedDownBatch ((W).get k) i = some B) :
    wholeCurrentBatch p β payload.assignment data i fixing (payload.downRecord i) B ↔
      ∀ e ∈ B, s₀ ≤ e.time.val := by
  constructor
  · intro h e he
    rw [← hfixing]
    exact (h e he).1
  · intro h e he
    have hc := crossing_of_support rate rewards C_star C_h z (((W).get k).input.time.val + 1) hd
    have hpos := (actual_completed_entry_origin_iff rate rewards C_star C_h z hc k i B hB e he).mp (h e he)
    obtain ⟨hs, _, hel, hsample, hword⟩ := actual_positive_entry_correspondence
      rate rewards C_star C_h z n payload hp k hd ht i hi e hpos
    exact ⟨hfixing.symm ▸ hs, hel, hsample, hword⟩

/-- On the actual completed bank, the replay's ambiguity decision is exactly
the retained all-postlaunch ambiguity readout. Raw absence and the ordinary
acceptance test remain explicit separate conditions. -/
theorem actual_completed_ambiguityDecision_iff (k : Fin (W).length)
    (hd : ((W).get k).input.time.val + 1 ∈ supportedDates) (ht : ((W).get k).input.time.val < m₀)
    (i : ActiveRoundActions.Follower p.m) (hi : i ∈ pendingAt(((W).get k).input.time.val))
    (fixing : Fin p.T) (hfixing : fixing.val = s₀) (olderStart : ℕ) (B : List (DecoderEntry p))
    (hB : completedDownBatch ((W).get k) i = some B)
    (raw : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p))) : ambiguityDecision p β
      payload.assignment data i fixing (payload.downRecord i) olderStart ((W).get k).input.time B raw ↔
      raw = none ∧ acceptDown (AffineBatchDecoder.codecParams p β) olderStart
        (WaitedWordWindow.sourceRound ((W).get k).input.time) (payload.downRecord i) ∧
      completedAmbiguousAfterStart (s₀) ((W).get k) i := by
  have hwhole := actual_completed_wholeCurrentBatch_iff
    rate rewards C_star C_h z n payload hp k hd ht i hi fixing hfixing B hB
  have hamb : completedAmbiguousAfterStart (s₀) ((W).get k) i ↔
      (∀ e ∈ B, s₀ ≤ e.time.val) ∧ multipleSolutions p B := by
    constructor
    · rintro ⟨B', hB', htimes, hmulti⟩
      have he : B' = B := Option.some.inj (hB'.symm.trans hB)
      subst B'
      exact ⟨htimes, (multipleSolutions_iff B).mp hmulti⟩
    · rintro ⟨htimes, hmulti⟩
      exact ⟨B, hB, htimes, (multipleSolutions_iff B).mpr hmulti⟩
  unfold ambiguityDecision
  rw [hwhole, hamb]
  tauto

/-- Actual confirmation feedback uses the original coordinator preparation
observation. The selected receiver and its full current DOWN hash are kept. -/
theorem actual_confirmation_iff (k : Fin (W).length) (hd : ((W).get k).input.time.val + 1 ∈ supportedDates)
    (ht : ((W).get k).input.time.val < m₀) (i : ActiveRoundActions.Follower p.m) :
    let r := (W).get k
    physicalConfirmation p payload.assignment data i r.input.time ↔
      downSelected p i r.input.row r.input.time ∧ i ∈ pendingAt(r.input.time.val) ∧
      CoordinatorLocalArmChoice.currentDownHash payload (r.input.row.2 r.input.time) i = 0 ∧
      0 < CoordinatorLocalArmChoice.ownGridObservationValue r.output.preparation.coordinatorObservation := by
  dsimp only
  let r := (W).get k
  have hc := crossing_of_support rate rewards C_star C_h z (r.input.time.val + 1) hd
  obtain ⟨selected, states, memories, hsel, hlive, hpselected, hrows, hJ, _, hin, hchoice,
      _, hfields, hnoReleased, _⟩ := actual_window_frame rate rewards C_star C_h z hc k
  change r.output.preparation.coordinator.selection = some selected at hsel
  have hrow := actual_auxiliary_row rate rewards C_star C_h z k hc
  have hpay : selected.view.payload = payload := Option.some.inj (hpselected.symm.trans hp)
  subst payload
  let live := auxiliaryLive rate rewards C_star C_h z n selected.view.payload hp
  have hproj := window_snapshot_projection rate rewards C_star C_h z n hc selected.view.payload hp k hd ht
  have hmissing : missing rate r = selected.view.pendingAtChoice := by
    unfold missing actualSelection
    rw [hsel]
    rfl
  have hne : selected.view.pendingAtChoice.Nonempty := by
    rw [← hmissing]
    exact ((source_window_date_mem_support_iff rate rewards C_star C_h z k).mp hd).1
  have hsnap : ActiveObservationBridge.liveSnapshotBefore p selected.view.payload.assignment live r.input.time =
      (⟨selected.view.pendingAtChoice, fun j => (states j).status⟩ : ActiveRoundActions.Snapshot _) := by
    apply congrArg₂ ActiveRoundActions.Snapshot.mk (hproj.1.trans hmissing)
    funext j
    exact hproj.2 j (states j) (memories j) (hin j)
  have hs : s₀ ≤ r.input.time.val := by
    have hh := (source_window_record_calendar rate rewards C_star C_h z k).1
    change r.input.time.val = s₀ + k.val at hh
    omega
  have hentry := auxiliaryLive_on_prefix rate rewards C_star C_h z n selected.view.payload hp
    r.input.time hs ht r (source_window_record_calendar rate rewards C_star C_h z k).2
  have hconfirm := physical_confirmation_iff rate rewards C_star C_h z r
    (source_window_record_calendar rate rewards C_star C_h z k).2
    (List.get_mem _ _) selected hsel hlive hrow states memories hin hchoice hfields (hnoReleased hne) hne
  have hpending := pendingNat_eq_window_missing rate rewards C_star C_h z k hd
  change pendingAt(r.input.time.val) = missing rate r at hpending
  change ActiveRoundActions.confirmation p.two_le_m
    (ActiveObservationBridge.liveSnapshotBefore p selected.view.payload.assignment live r.input.time)
    (auxiliaryInput selected.view.payload z r.input.time) (live r.input.time).rewards i ↔ _
  rw [hsnap, hentry.1, hpending, hmissing]
  have hslot : (auxiliaryInput selected.view.payload z r.input.time).slot =
      PublicDiscreteDraws.slotDraw (r.input.row.2 r.input.time).1 := by rw [hrow]; rfl
  have hdraw : (auxiliaryInput selected.view.payload z r.input.time).selected =
      PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K (r.input.row.2 r.input.time).1 := by rw [hrow]; rfl
  by_cases hselected : (auxiliaryInput selected.view.payload z r.input.time).selected = i
  · rw [← hselected]
    rw [← hconfirm]
    change CoordinatorLocalArmChoice.downConfirmationEvent _ _ _ _ _ _ ↔ _
    simp only [CoordinatorLocalArmChoice.downConfirmationEvent, CoordinatorLocalArmChoice.confirmationLive,
      hlive, hne, true_and, downSelected, hdraw, r, and_true]
    rfl
  · constructor
    · intro h
      exact (hselected h.2.1).elim
    · rintro ⟨hdown, _⟩
      exact (hselected (hdraw.trans hdown.2)).elim

/-- An actual compared call uses the SAME auxiliary current input and the
entire actual replay bank, with both completed history and pending entries.
The false-word cause is read before reference suppression. -/
theorem actual_called_auxiliary_decoder (k : Fin (W).length)
    (hd : ((W).get k).input.time.val + 1 ∈ supportedDates) (ht : ((W).get k).input.time.val < m₀)
    (i : ActiveRoundActions.Follower p.m) (hi : i ∈ pendingAt(((W).get k).input.time.val))
    (logged : State p rate.eta) (cut : ReferenceDownCutOutput p rate)
    (hlogged : (((W).get k).output.followers i).downInput = some logged)
    (hcut : (((W).get k).output.followers i).down = some cut)
    (hcompared : cut.rawComparison.isSome = true) :
    cut.raw = (AffineBatchDecoder.decodeStep p (observationTrace p payload.assignment data i)
      logged.downBatch ((W).get k).input.time).2 ∧
    (falseDecision p β (payload.downRecord i) 0 ((W).get k).input.time cut.raw ↔ wrongUniqueAccepted cut) := by
  have hc := crossing_of_support rate rewards C_star C_h z (((W).get k).input.time.val + 1) hd
  let r := (W).get k
  obtain ⟨selected, hsel, hpselected, _, _, _, _, _, hbank, hstart, hcollected, _, _, hraw,
      hupdated, _, hexpected, hparse, hfalse⟩ :=
    ReferenceFirstLiveHandoverRawPrefix.actual_called_prefix_bank_counts_and_raw_false
      rate rewards C_star C_h z hc k i logged cut hlogged hcut hcompared
  have hpay : selected.view.payload = payload := Option.some.inj (hpselected.symm.trans hp)
  obtain ⟨_, states, memories, _, _, _, hrows, hJ, _, hin, hchoice, hnoneIff, _⟩ :=
    actual_window_frame rate rewards C_star C_h z hc k
  obtain ⟨choice, memory, hcfg, hu, _, hstatus, _⟩ :=
    retained_input_origin r i logged hlogged
  have hstates : states i = choice :=
    (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj ((hchoice i).symm.trans hcfg)).1
  have hnone : (states i).lastDown = none := (hnoneIff i).mp (hstates.symm ▸ hu)
  have hrow := actual_auxiliary_row rate rewards C_star C_h z k hc
  have hfields := retained_call_fields r i logged cut hlogged hcut hcompared
  have hcontrol := hfields.1
  rw [hrow] at hcontrol
  have hinput := actual_selected_decoder_input rate rewards C_star C_h z n payload hp actualOverflowAfter
    k hd ht i hi hcontrol.1 hcontrol.2 (states i) (memories i) (hin i) hnone
  have hinput' : observationTrace p payload.assignment data i r.input.time =
      currentRoundInput p i r.input.row r.input.time (preparedOwnObservation r i) rate logged := by
    exact hinput.trans (by simp only [r, currentRoundInput, hstatus, ← hstates])
  have hdecode := decodeStep_depends_on_current_input p (observationTrace p payload.assignment data i)
    (currentInputExtension p (currentRoundInput p i r.input.row r.input.time
      (preparedOwnObservation r i) rate logged)) logged.downBatch r.input.time hinput'
  rw [← hbank] at hraw
  exact ⟨hraw.trans (congrArg Prod.snd hdecode).symm, by simpa only [hpay] using hfalse⟩

include hp

/-- A current-word return installs exactly on this actual first-live call.
Successful recovery is obtained from the source's ordinary outgoing record;
it is not a premise. False accepted words remain a separate diagnostic. -/
theorem actual_compared_installation_iff (k : Fin (W).length)
    (hd : ((W).get k).input.time.val + 1 ∈ supportedDates) (i : ActiveRoundActions.Follower p.m)
    (logged : State p rate.eta) (cut : ReferenceDownCutOutput p rate)
    (hlogged : (((W).get k).output.followers i).downInput = some logged)
    (hcut : (((W).get k).output.followers i).down = some cut)
    (hcompared : cut.rawComparison.isSome = true) :
    installationFlag payload ((W).get k) i = true ↔ cut.raw = some
      (currentWord p β (payload.downRecord i)) := by
  let r := (W).get k
  have hc := crossing_of_support rate rewards C_star C_h z (r.input.time.val + 1) hd
  rw [actual_installation_flag_iff rate rewards C_star C_h z hc k payload i]
  obtain ⟨selected, _, hpselected, _, htime, hstamp, _, _, _, hstart, _, _, _, _, _, _, hexpected, _, _⟩ :=
    ReferenceFirstLiveHandoverRawPrefix.actual_called_prefix_bank_counts_and_raw_false
      rate rewards C_star C_h z hc k i logged cut hlogged hcut hcompared
  have hpay : selected.view.payload = payload := Option.some.inj (hpselected.symm.trans hp)
  rw [hpay] at hstamp hexpected
  change r.input.time.val = s₀ + k.val at htime
  change (payload.downRecord i).val.sigma = s₀ + 1 at hstamp
  have hfields := retained_call_fields r i logged cut hlogged hcut hcompared
  have ha : acceptDown (codecParams p rate.eta)
      (acceptedStart logged) (r.input.time.val + 1) (payload.downRecord i) := by
    rw [hstart]
    constructor <;> rw [hstamp] <;> omega
  obtain ⟨choice, memory, actualLogged, hcfg, hu, hlogging, hlogged', hcutdef⟩ :=
    ReferenceFollowerSparseEmissionRecovery.actualDownDiagnostic_choice r i cut hcut
  have hlogeq : actualLogged = logged := Option.some.inj (hlogged'.symm.trans hlogged)
  subst actualLogged
  change cut = referenceDownCut p r.output.preparation.coordinator.downView
    (r.output.preparation.followers.followers i).follower (r.output.preparation.followers.followers i).row
    (r.output.preparation.followers.followers i).time (preparedOwnObservation r i) rate logged at hcutdef
  change ActiveFollowerLogging.checkedLogging (r.output.preparation.followers.followers i).follower
    (r.output.preparation.followers.followers i).row (r.output.preparation.followers.followers i).activation
    (r.output.preparation.followers.followers i).time ((r.output.preparation.followers.followers i).arm,
      preparedOwnObservation r i) choice = .ok logged at hlogging
  constructor
  · rintro ⟨l, c, after, raw, scan, registers, lastService, hl, hc', haccepted⟩
    have hlEq : l = logged := Option.some.inj (hl.symm.trans hlogged)
    have hcEq : c = cut := Option.some.inj (hc'.symm.trans hcut)
    subst l
    subst c
    have hn := ReferenceFollowerSparseEmissionRecovery.actualAcceptedCut_no_rawMismatch
      r i logged cut after raw (payload.downRecord i) scan registers lastService hlogged hcut haccepted
    have hn' : ¬ rawMismatch cut := by rw [hcutdef]; exact hn
    have hraw : cut.raw = cut.expectedWord := by
      by_contra hnot
      apply hn'
      exact hfields.2.2.2.2.2.2.2.2.2.trans (congrArg some (decide_eq_false hnot))
    exact hraw.trans hexpected
  · intro hraw
    have hprov := source_window_provenance rate rewards C_star C_h z hc
    dsimp only at hprov
    rcases hprov with hzero | ⟨_, _, _, _, _, _, _, _, hrows⟩
    · have hk := k.isLt
      omega
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hfollowers⟩ := hrows k
    obtain ⟨_, _, next, nextMemory, _, hnext, _⟩ := hfollowers i
    have hfinish := ReferenceFollowerBufferProvenance.roundRecord_follower_eq_finishFollower i r
    have hn : (ReferenceActivePhysicalStep.finishFollower r.output.preparation.coordinator.downView
        (r.output.preparation.followers.followers i)
        (preparedOwnObservation r i)).configuration = .ordinary next nextMemory := by
      change (ReferenceActivePhysicalStep.finishFollower r.output.preparation.coordinator.downView
        (r.output.preparation.followers.followers i)
        (r.output.preparation.feedback.observations (PublicDiscreteDraws.followerPlayer p.two_le_m i))).configuration = _
      rw [← hfinish]
      exact hnext
    obtain ⟨choice', memory', post, hcfg', hrecord, _, _, _⟩ :=
      ReferenceFollowerReplyChronology.finishFollower_ordinary_inversion _ _ _ next nextMemory hn
    obtain ⟨hchoice, hmemory⟩ := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj (hcfg'.symm.trans hcfg)
    subst choice'
    subst memory'
    simp only [ReferenceActivePhysicalStep.recordFollower, dite_eq_left hu, hlogging] at hrecord
    change DeclaredFollowerLocalRound.consumeDownResult rate
      (referenceDownCut p r.output.preparation.coordinator.downView
        (r.output.preparation.followers.followers i).follower
        (r.output.preparation.followers.followers i).row (r.output.preparation.followers.followers i).time
        (preparedOwnObservation r i) rate logged).outcome = .ok post at hrecord
    rw [← hcutdef] at hrecord
    have halign := r.output.preparation.follower_alignment i
    have hcutdef' := hcutdef
    rw [halign.1, halign.2.1, halign.2.2.1] at hcutdef'
    let decoded := currentDecodeStep p i r.input.row r.input.time (preparedOwnObservation r i) rate logged
    have hmatch : decoded.2 = expectedDownFlatWord
        r.output.preparation.coordinator.downView i r.input.row r.input.time :=
      hfields.2.2.2.2.2.1.symm.trans (hraw.trans (hexpected.symm.trans hfields.2.2.2.2.2.2.1))
    have hparse : ordinaryParse p rate decoded.2 = some (payload.downRecord i) := by
      rw [← hfields.2.2.2.2.2.1, hraw]
      exact parseOutput_currentWord p _ _
    have hparseExpected : ordinaryParse p rate
        (expectedDownFlatWord r.output.preparation.coordinator.downView
          i r.input.row r.input.time) = some (payload.downRecord i) := by
      rw [← hmatch]
      exact hparse
    let scan := acceptedCutoffScan p rate (payload.downRecord i) r.input.time
      (acceptedDownStartLE p rate (payload.downRecord i) r.input.time logged ha) r.input.row
    cases hchecked : checkedRecovery p rate (payload.downRecord i) logged scan.endpoint with
    | error failure =>
        have hout : cut.outcome = .outputFailure logged (.replay failure) := by
          rw [hcutdef']
          simp only [referenceDownCut, hfields.1, hfields.2.1,
            hfields.2.2.1, hfields.2.2.2.1, hfields.2.2.2.2.1, dite_true,
            hmatch, hparseExpected, ha, scan, decoded, hchecked]
        rw [hout] at hrecord
        cases hrecord
    | ok recovered =>
        have hout : cut.outcome = .accepted logged { logged with
              downBatch := decoded.1
              lastDown := some (payload.downRecord i)
              S := recovered.registers.1
              delta := recovered.lastService
              backlog := recovered.registers.2
              status := if scan.endpoint = r.input.time.val + 2 then .pending else .unoccupied
              buffer := [] }
            decoded.2 (payload.downRecord i) scan recovered.registers recovered.lastService := by
          rw [hcutdef']
          simp only [referenceDownCut, hfields.1, hfields.2.1,
            hfields.2.2.1, hfields.2.2.2.1, hfields.2.2.2.2.1, dite_true,
            hmatch, hparseExpected, ha, scan, decoded, hchecked]
        exact ⟨logged, cut, _, decoded.2, scan, recovered.registers, recovered.lastService, hlogged, hcut, hout⟩


omit hp

/-- An actual awaiting incoming follower has retained logging and DOWN
diagnostics. Comparison is called exactly on selected DOWN, including a
zero observation. Input checks follow from the actual ordinary source tail. -/
theorem actual_awaiting_diagnostics (k : Fin (W).length)
    (hd : ((W).get k).input.time.val + 1 ∈ supportedDates) (i : Fin (p.m - 1)) (incoming : State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hin : ((W).get k).input.state.followers i = .ordinary incoming memory)
    (hnone : incoming.lastDown = none) :
    ∃ (logged : State p rate.eta) (cut : ReferenceDownCutOutput p rate),
      (((W).get k).output.followers i).downInput = some logged ∧
      (((W).get k).output.followers i).down = some cut ∧
      logged.lastDown = none ∧ logged.downBatch = incoming.downBatch ∧ logged.status = incoming.status ∧
      acceptedStart logged = 0 ∧
      (cut.rawComparison.isSome = true ↔ downSelected p i
        ((W).get k).input.row ((W).get k).input.time) := by
  let r := (W).get k
  have hc := crossing_of_support rate rewards C_star C_h z (r.input.time.val + 1) hd
  obtain ⟨_, states, memories, _, _, _, _, _, _, hstates, hchoices, hnoneIff, _⟩ :=
    actual_window_frame rate rewards C_star C_h z hc k
  obtain ⟨hstate, hmemory⟩ := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj ((hstates i).symm.trans hin)
  have hu : incoming.status = .unoccupied := by
    rw [← hstate]
    exact (hnoneIff i).mpr (hstate.symm ▸ hnone)
  have hcfg : (r.output.preparation.followers.followers i).configuration = .ordinary incoming memory := by
    rw [← hstate, ← hmemory]
    exact hchoices i
  have hprov := source_window_provenance rate rewards C_star C_h z hc
  dsimp only at hprov
  rcases hprov with hzero | ⟨_, _, _, _, _, _, _, _, hrows⟩
  · have hk := k.isLt
    omega
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hfollowers⟩ := hrows k
  obtain ⟨_, _, next, nextMemory, _, hnext, _⟩ := hfollowers i
  have hfinish := ReferenceFollowerBufferProvenance.roundRecord_follower_eq_finishFollower i r
  change r.output.followers i = ReferenceActivePhysicalStep.finishFollower
    r.output.preparation.coordinator.downView (r.output.preparation.followers.followers i)
    (preparedOwnObservation r i) at hfinish
  have hn : (ReferenceActivePhysicalStep.finishFollower r.output.preparation.coordinator.downView
      (r.output.preparation.followers.followers i)
      (preparedOwnObservation r i)).configuration = .ordinary next nextMemory := by
    rw [← hfinish]
    exact hnext
  obtain ⟨choice, cm, post, hcfg', hrecord, _, hdiagInput, hdiagDown⟩ :=
    ReferenceFollowerReplyChronology.finishFollower_ordinary_inversion _ _ _ next nextMemory hn
  obtain ⟨hchoice, hcm⟩ := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj (hcfg'.symm.trans hcfg)
  subst choice
  subst cm
  cases hlogging : ActiveFollowerLogging.checkedLogging
      (r.output.preparation.followers.followers i).follower (r.output.preparation.followers.followers i).row
      (r.output.preparation.followers.followers i).activation
      (r.output.preparation.followers.followers i).time
      ((r.output.preparation.followers.followers i).arm, preparedOwnObservation r i) incoming with
  | error failure =>
      simp only [ReferenceActivePhysicalStep.recordFollower, dite_eq_left hu, hlogging] at hrecord
      cases hrecord
  | ok logged =>
      let cut := referenceDownCut p r.output.preparation.coordinator.downView
        (r.output.preparation.followers.followers i).follower
        (r.output.preparation.followers.followers i).row (r.output.preparation.followers.followers i).time
        (preparedOwnObservation r i) rate logged
      simp only [ReferenceActivePhysicalStep.recordFollower, dite_eq_left hu, hlogging] at hrecord
      change DeclaredFollowerLocalRound.consumeDownResult rate cut.outcome = .ok post at hrecord
      have hlog := ReferenceActivePhysicalStep.recordFollower_logged r.output.preparation.coordinator.downView
        (r.output.preparation.followers.followers i).follower
        (r.output.preparation.followers.followers i).row
        (r.output.preparation.followers.followers i).activation
        (r.output.preparation.followers.followers i).time
        (r.output.preparation.followers.followers i).active (r.output.preparation.followers.followers i).arm
        (preparedOwnObservation r i) incoming logged hu hlogging
      have hl : (r.output.followers i).downInput = some logged := by
        rw [hfinish]
        exact hdiagInput.trans hlog.1
      have hdcut : (r.output.followers i).down = some cut := by
        rw [hfinish]
        exact hdiagDown.trans hlog.2
      obtain ⟨ch, mem, hch, _, hlast, hstatus, hbank⟩ :=
        retained_input_origin r i logged hl
      have hchEq : ch = incoming := (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj (hch.symm.trans hcfg)).1
      subst ch
      have hln : logged.lastDown = none := hlast.trans hnone
      refine ⟨logged, cut, hl, hdcut, hln, hbank, hstatus, ?_, ?_⟩
      · simp only [acceptedStart, hln]
      · constructor
        · intro hcomp
          exact (retained_call_fields r i logged cut hl hdcut hcomp).1
        · intro hdown
          change downSelected p i r.input.row r.input.time at hdown
          have hcutdef : cut = referenceDownCut p r.output.preparation.coordinator.downView
              i r.input.row r.input.time (preparedOwnObservation r i) rate logged := by
            dsimp only [cut]
            rw [(r.output.preparation.follower_alignment i).1,
              (r.output.preparation.follower_alignment i).2.1,
              (r.output.preparation.follower_alignment i).2.2.1]
          have hul : logged.status = .unoccupied := hstatus.trans hu
          rw [hcutdef] at hrecord ⊢
          simp only [referenceDownCut, hdown, hul, dite_true] at hrecord ⊢
          split <;> rename_i hreg
          · rw [dite_eq_left hreg] at hrecord
            split <;> rename_i hdec
            · rw [dite_eq_left hdec] at hrecord
              split <;> rename_i hbuf
              · split <;> rfl
              · rw [dite_eq_right hbuf] at hrecord
                cases hrecord
            · rw [dite_eq_right hdec] at hrecord
              cases hrecord
          · rw [dite_eq_right hreg] at hrecord
            cases hrecord

omit hp

/-- The full physical bank at every actual incoming ordinary record is the
public replay of its original calls, including completed histories. -/
theorem actual_window_bank (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true)
    (k : Fin (W).length) (i : Fin (p.m - 1))
    (state : State p rate.eta) (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hin : ((W).get k).input.state.followers i = .ordinary state memory) :
    let d0 := ((actualFirstLiveSeed rate z rewards C_star C_h hc).followers i).downBatch
    state.downBatch = replayDownCalls i ((W).take k.val) d0 ∧
      state.downBatch.pending.length < AffineBatchDecoder.quota p := by
  dsimp only
  let s := s₀
  let physicalSeed := ReferenceLocalReleaseGateChronology.sourceSeed rate z rewards C_star C_h hc
  let seed := actualFirstLiveSeed rate z rewards C_star C_h hc
  let count := p.T - s
  have hs : s ≤ p.T := ReferenceCompletePhysicalHistory.physicalStart_le_T rate z rewards C_star C_h
  have hspan : s + count ≤ p.T := by dsimp only [count]; omega
  let R := ReferenceLocalReleaseGateChronology.sourceRun rate z rewards C_star C_h hc s count rfl hspan
  have hlaunch := ReferenceLocalReleaseGateChronology.sourceSeed_launch rate z rewards C_star C_h hc
  have hcomplete : R.records = completeRecords rate rewards C_star C_h z :=
    (ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
      rate z rewards C_star C_h physicalSeed hlaunch).symm
  have hwindow : ReferenceFirstLiveConfirmationHistory.firstLiveWindow R.records = W := by
    rw [hcomplete]; rfl
  have hcand := ReferenceFirstLiveUnoccupiedEmission.window_record_eq_candidate
    physicalSeed z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s count hspan seed.activeAtStart
  let kR : Fin (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R.records).length :=
    ⟨k.val, by rw [hwindow]; exact k.isLt⟩
  obtain ⟨hstep, hrecord, _⟩ := hcand kR
  change s + (k.val + 1) ≤ p.T at hstep
  have helem := congrArg (fun records => records[k.val]?) hwindow
  rw [List.getElem?_eq_getElem kR.isLt, List.getElem?_eq_getElem k.isLt] at helem
  have hrecord' : (W).get k = ReferenceAssignmentPayloadChronology.actualRunRecordAt physicalSeed z.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s k.val hstep seed.activeAtStart :=
    (Option.some.inj helem).symm.trans hrecord
  have hbefore : (ReferenceActivePhysicalHorizon.run physicalSeed z.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s k.val (by omega) seed.activeAtStart
      ).finalState.followers i = .ordinary state memory := by
    rw [hrecord'] at hin
    exact hin
  obtain ⟨active, hactive, hseed⟩ :=
    ReferenceCorrectedInitializationLaunch.correctedLaunch_downBatchSeed rate z rewards C_star C_h hc
  have he : active = physicalSeed := Option.some.inj (hactive.symm.trans hlaunch)
  subst active
  have hreplay := run_downBatch_replay
    physicalSeed z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s k.val (by omega)
    seed.activeAtStart hseed i (seed.followers i) (seed.memory i) (seed.configuration i) state memory hbefore
  have hspec := ReferenceFollowerDecoderChronology.run_downBatch_spec
    physicalSeed z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s k.val (by omega)
    seed.activeAtStart hseed i state memory hbefore
  have hk : k.val ≤ count := by dsimp only [count]; omega
  obtain ⟨suffix, hprefix⟩ := ReferenceCollectionPhaseHistory.run_records_prefix
    physicalSeed z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s k.val (count - k.val)
    (by omega) seed.activeAtStart
  have hprefix' : (ReferenceActivePhysicalHorizon.run physicalSeed z.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s k.val (by omega)
      seed.activeAtStart).records.IsPrefix R.records :=
    ⟨suffix, by simpa only [Nat.add_sub_of_le hk, R, ReferenceLocalReleaseGateChronology.sourceRun] using hprefix.symm⟩
  have htake : R.records.take k.val = (ReferenceActivePhysicalHorizon.run physicalSeed z.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s k.val (by omega)
      seed.activeAtStart).records := by
    have hlen := ReferenceActivePhysicalHorizon.run_record_count physicalSeed z.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s k.val (by omega) seed.activeAtStart
    exact (congrArg (fun j => R.records.take j) hlen).symm.trans (List.prefix_iff_eq_take.mp hprefix').symm
  have hWprefix : (W).IsPrefix R.records := by rw [← hwindow]; exact List.takeWhile_prefix _
  have htakeW : (W).take k.val = R.records.take k.val := by
    obtain ⟨tail, htail⟩ := hWprefix
    rw [← htail, List.take_append_of_le_length k.isLt.le]
  rw [← htakeW] at htake
  exact ⟨hreplay.1.trans (congrArg (fun records => replayDownCalls i
    records (seed.followers i).downBatch) htake.symm), hspec.1.1.1⟩

include hp

/-- One normal awaiting service transition, including unselected calls and
zero feedback. The later supported date supplies both decoder exclusions. -/
theorem actual_awaiting_normal_service (k j : Fin (W).length) (hkj : k.val < j.val)
    (hj : ((W).get j).input.time.val + 1 ∈ supportedDates) (ht : ((W).get k).input.time.val < m₀)
    (i : ActiveRoundActions.Follower p.m) (hi : i ∈ pendingAt(((W).get k).input.time.val))
    (fixing : Fin p.T) (hfixing : fixing.val = s₀) (incoming : State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hin : ((W).get k).input.state.followers i = .ordinary incoming memory)
    (hnone : incoming.lastDown = none)
    (hsmall : incoming.downBatch.pending.length < AffineBatchDecoder.quota p) :
    let r := (W).get k
    let tr := observationTrace p payload.assignment data i
    let updated := initial p (AffineBatchDecoder.decodeStep p tr incoming.downBatch r.input.time).1 0
    serve[i,fixing] (initial p incoming.downBatch 0) r.input.time =
      if installationFlag payload r i = true then
        { updated with acceptedStart := (payload.downRecord i).val.sigma, phase := .acceptedUnconfirmed }
      else updated := by
  dsimp only
  let r := (W).get k
  let tr := observationTrace p payload.assignment data i
  change (if AffineBatchDecoder.eligible (tr r.input.time) then
      receiverStep p β payload.assignment data i fixing
        (payload.downRecord i) (initial p incoming.downBatch 0) r.input.time
    else initial p incoming.downBatch 0) = _
  have hd := supported_predecessors rate rewards C_star C_h z j k hkj.le hj
  have hc := crossing_of_support rate rewards C_star C_h z (r.input.time.val + 1) hd
  have hrow := actual_auxiliary_row rate rewards C_star C_h z k hc
  obtain ⟨logged, cut, hl, hcut, _, hbank, hlogstatus, _, hcalled⟩ :=
    actual_awaiting_diagnostics rate rewards C_star C_h z k hd i incoming memory hin hnone
  by_cases hel : AffineBatchDecoder.eligible (tr r.input.time)
  · obtain ⟨hdaux, hidaux, _⟩ := (eligible_iff p payload.assignment data i r.input.time).mp hel
    have hdown : downSelected p i r.input.row r.input.time := by
      rw [hrow]; exact ⟨hdaux, hidaux⟩
    have hcomp := hcalled.mpr hdown
    have hinput := actual_selected_decoder_input rate rewards C_star C_h z n payload hp actualOverflowAfter
      k hd ht i hi hdaux hidaux incoming memory hin hnone
    obtain ⟨hraw, hfalse⟩ := actual_called_auxiliary_decoder
      rate rewards C_star C_h z n payload hp k hd ht i hi logged cut hl hcut hcomp
    rw [hbank] at hraw
    have hflag := actual_compared_installation_iff rate rewards C_star C_h z payload hp
      k hd i logged cut hl hcut hcomp
    have hinputLog : tr r.input.time = currentRoundInput p i
        r.input.row r.input.time (preparedOwnObservation r i) rate logged := by
      exact hinput.trans (by simp only [r, currentRoundInput, hlogstatus])
    have happ : appendedDownBatch r i logged =
        incoming.downBatch.pending ++ [AffineBatchDecoder.entry p tr r.input.time] := by
      unfold appendedDownBatch
      rw [hbank]
      have hpos : AffineBatchDecoder.positiveAt p (currentInputExtension p
            (currentRoundInput p i r.input.row r.input.time
              (preparedOwnObservation r i) rate logged)) r.input.time =
          [AffineBatchDecoder.entry p tr r.input.time] := by
        simp only [AffineBatchDecoder.positiveAt, currentInputExtension,
          ← hinputLog, hel, ite_true, AffineBatchDecoder.entry]
      rw [hpos]
    by_cases hshort : incoming.downBatch.pending.length + 1 < AffineBatchDecoder.quota p
    · have hrawNone := (retained_incomplete_raw_none r i logged cut hl hcut hcomp
        (by rw [happ, List.length_append, List.length_singleton]; exact hshort)).2
      have hnf : installationFlag payload r i ≠ true := by
        intro hf
        rw [hrawNone] at hflag
        cases hflag.mp hf
      rw [ite_eq_left hel]
      dsimp only [receiverStep, initial]
      change (if incoming.downBatch.pending.length + 1 < AffineBatchDecoder.quota p then
        initial p (AffineBatchDecoder.decodeStep p tr incoming.downBatch r.input.time).1 0
        else _) = _
      rw [ite_eq_left hshort, ite_eq_right hnf]
      rfl
    · have hB : completedDownBatch r i =
          some (incoming.downBatch.pending ++ [AffineBatchDecoder.entry p tr r.input.time]) := by
        apply (completedDownBatch_eq_some_iff r i _).mpr
        refine ⟨logged, cut, hl, hcut, hcomp, ?_, happ⟩
        rw [happ, List.length_append, List.length_singleton]
        omega
      let B := incoming.downBatch.pending ++ [AffineBatchDecoder.entry p tr r.input.time]
      let updated := initial p (AffineBatchDecoder.decodeStep p tr logged.downBatch r.input.time).1 0
      have hn : afterDecision p β payload.assignment data i fixing (payload.downRecord i)
          updated r.input.time B cut.raw = if installationFlag payload r i = true then
            { updated with acceptedStart := (payload.downRecord i).val.sigma, phase := .acceptedUnconfirmed }
          else updated := by
        have hsafe := supported_strict_predecessor_safe rate rewards C_star C_h z j k hkj hj
        have hnf : ¬ falseDecision p β (payload.downRecord i) 0 r.input.time cut.raw := by
          intro h
          exact hsafe.2.1 i cut hcut (hfalse.mp h)
        have hna : ¬ ambiguityDecision p β payload.assignment data i fixing
            (payload.downRecord i) 0 r.input.time B cut.raw := by
          intro h
          have hamb := (actual_completed_ambiguityDecision_iff rate rewards C_star C_h z n payload hp
            k hd ht i hi fixing hfixing 0 B hB cut.raw).mp h
          exact hsafe.2.2.1 i hamb.2.2
        obtain ⟨selected, _, hpselected, _, htime, hstamp, _⟩ :=
          ReferenceFirstLiveHandoverRawPrefix.actual_called_prefix_bank_counts_and_raw_false
            rate rewards C_star C_h z hc k i logged cut hl hcut hcomp
        have hpay : selected.view.payload = payload := Option.some.inj (hpselected.symm.trans hp)
        rw [hpay] at hstamp
        change r.input.time.val = s₀ + k.val at htime
        change (payload.downRecord i).val.sigma = s₀ + 1 at hstamp
        have haM : acceptDown (AffineBatchDecoder.codecParams p β) 0
            (WaitedWordWindow.sourceRound r.input.time) (payload.downRecord i) := by
          change 0 < (payload.downRecord i).val.sigma ∧ (payload.downRecord i).val.sigma ≤ r.input.time.val + 1
          constructor <;> rw [hstamp] <;> omega
        by_cases hf : installationFlag payload r i = true
        · have hpM := (parseOutput_eq_some_iff β (payload.downRecord i) cut.raw).mpr (hflag.mp hf)
          simp only [afterDecision, hpM, updated, initial, haM, hf, ite_true]
          split
          · rfl
          · rename_i hne
            exact (hne rfl).elim
        · rw [ite_eq_right hf]
          cases hparse : parseOutput p β cut.raw with
          | none =>
              simp only [afterDecision, hparse, updated, initial, hna, ite_false]
          | some other =>
              have hreject : ¬ acceptDown (AffineBatchDecoder.codecParams p β) 0
                  (WaitedWordWindow.sourceRound r.input.time) other := by
                intro ha
                by_cases he : other = payload.downRecord i
                · subst other
                  exact hf (hflag.mpr ((parseOutput_eq_some_iff β (payload.downRecord i) cut.raw).mp hparse))
                · exact hnf ⟨other, hparse, he, ha⟩
              simp only [afterDecision, hparse, updated, initial, hreject, ite_false]
      dsimp only [updated, B] at hn
      rw [hbank, hraw] at hn
      rw [ite_eq_left hel]
      dsimp only [receiverStep, initial]
      rw [ite_eq_right hshort]
      exact hn
  · have hdecode := AffineBatchDecoder.decodeStep_ineligible p tr incoming.downBatch r.input.time hsmall hel
    have hnf : installationFlag payload r i ≠ true := by
      intro hf
      have hdown := acceptedDown_selected r i (payload.downRecord i)
        ((actual_installation_flag_iff rate rewards C_star C_h z hc k payload i).mp hf)
      have hcomp := hcalled.mpr hdown
      have hraw := (actual_called_auxiliary_decoder rate rewards C_star C_h z n payload hp
        k hd ht i hi logged cut hl hcut hcomp).1
      rw [hbank] at hraw
      have hrawNone : cut.raw = none := hraw.trans (congrArg Prod.snd hdecode)
      have hflag := (actual_compared_installation_iff rate rewards C_star C_h z payload hp
        k hd i logged cut hl hcut hcomp).mp hf
      rw [hrawNone] at hflag
      cases hflag
    rw [ite_eq_right hel, ite_eq_right hnf, hdecode]

/-- The auxiliary decoder step is the actual next full bank on an awaiting
normal predecessor. No pending or completed history is discarded. -/
theorem actual_awaiting_bank_step (k j : Fin (W).length) (hsucc : j.val = k.val + 1)
    (hj : ((W).get j).input.time.val + 1 ∈ supportedDates) (ht : ((W).get k).input.time.val < m₀)
    (i : Fin (p.m - 1)) (hi : i ∈ pendingAt(((W).get k).input.time.val)) (before after : State p rate.eta)
    (memory nextMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hin : ((W).get k).input.state.followers i = .ordinary before memory)
    (hnext : ((W).get j).input.state.followers i = .ordinary after nextMemory)
    (hnone : before.lastDown = none) :
    after.downBatch = (AffineBatchDecoder.decodeStep p (observationTrace p payload.assignment data i)
      before.downBatch ((W).get k).input.time).1 := by
  have hd := supported_predecessors rate rewards C_star C_h z j k (by omega) hj
  have hc := crossing_of_support rate rewards C_star C_h z _ hd
  obtain ⟨hbank, hsmall⟩ := actual_window_bank rate rewards C_star C_h z hc k i before memory hin
  have hnextBank := (actual_window_bank rate rewards C_star C_h z hc j i after nextMemory hnext).1
  have hchoice' : (((W).get k).output.preparation.followers.followers i).configuration =
      .ordinary before memory := by
    obtain ⟨_, st, mem, _, _, _, _, _, _, hst, hch, _⟩ := actual_window_frame rate rewards C_star C_h z hc k
    obtain ⟨hstate, hmem⟩ := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj ((hst i).symm.trans hin)
    simpa only [hstate, hmem] using hch i
  have hcall := actualDownCall_ordinary ((W).get k) i before memory hchoice'
  dsimp only [preparedChoiceTime, preparedChoiceRow] at hcall
  rw [(((W).get k).output.preparation.follower_alignment i).1,
    (((W).get k).output.preparation.follower_alignment i).2.2.1] at hcall
  have hrow := actual_auxiliary_row rate rewards C_star C_h z k hc
  let actual := currentRoundInput p i ((W).get k).input.row
    ((W).get k).input.time (preparedOwnObservation ((W).get k) i) rate before
  have hstep : (AffineBatchDecoder.decodeStep p
      (currentInputExtension p actual) before.downBatch ((W).get k).input.time).1 =
      (AffineBatchDecoder.decodeStep p (observationTrace p payload.assignment data i)
        before.downBatch ((W).get k).input.time).1 := by
    by_cases hdown : downSelected p i ((W).get k).input.row ((W).get k).input.time
    · have hinput := actual_selected_decoder_input rate rewards C_star C_h z n payload hp actualOverflowAfter
        k hd ht i hi (by rw [hrow] at hdown; exact hdown.1)
        (by rw [hrow] at hdown; exact hdown.2) before memory hin hnone
      exact (congrArg Prod.fst (decodeStep_depends_on_current_input p _ _
        before.downBatch ((W).get k).input.time hinput)).symm
    · have ha : ¬ AffineBatchDecoder.eligible actual := fun h => hdown
        ((currentRoundInput_eligible_iff p i _ _ _ rate before).mp h).1
      have hb : ¬ AffineBatchDecoder.eligible (observationTrace p payload.assignment data i ((W).get k).input.time) := by
        rintro h
        obtain ⟨hdaux, hidaux, _⟩ := (eligible_iff p payload.assignment data i _).mp h
        exact hdown (by rw [hrow]; exact ⟨hdaux, hidaux⟩)
      rw [AffineBatchDecoder.decodeStep_ineligible p _ _ _ hsmall ha,
        AffineBatchDecoder.decodeStep_ineligible p _ _ _ hsmall hb]
  simp only [List.get_eq_getElem] at hcall
  rw [hnextBank, hsucc, List.take_succ_eq_append_getElem k.isLt]
  simp only [replayDownCalls, actualDownCalls, foldDownCalls, List.filterMap_append, List.filterMap_cons,
    List.filterMap_nil, hcall, List.foldl_append, List.foldl_cons, List.foldl_nil]
  change (AffineBatchDecoder.decodeStep p (currentInputExtension p actual)
    (replayDownCalls i ((W).take k.val) _) ((W).get k).input.time).1 = _
  rw [← hbank]
  exact hstep

/-- Incoming phase and full awaiting bank on the actual chronological
calendar. Only strict predecessors are simulated; the queried update may detect
failure or overflow. Confirmed followers are included in the same induction. -/
theorem actual_incoming_correspondence (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true)
    (fixing : Fin p.T) (hfixing : fixing.val = s₀) : ∀ (k : Fin (W).length),
    ((W).get k).input.time.val + 1 ∈ supportedDates → ((W).get k).input.time.val < m₀ →
    ∀ (i : ActiveRoundActions.Follower p.m) (incoming : State p rate.eta)
      (memory : ActiveFollowerLifecycle.LocalMemory p),
    ((W).get k).input.state.followers i = .ordinary incoming memory →
    let d0 := ((actualFirstLiveSeed rate z rewards C_star C_h hc).followers i).downBatch
    let q := replay[i,fixing] (initial p d0 0) ((W).get k).input.time.val
    if i ∈ pendingAt(((W).get k).input.time.val) then
      if incoming.lastDown = none then q = initial p incoming.downBatch 0
      else q.phase = .acceptedUnconfirmed ∧ q.acceptedStart = (payload.downRecord i).val.sigma
    else q.phase = .confirmed := by
  dsimp only
  intro k
  generalize hkval : k.val = l
  induction l generalizing k with
  | zero =>
      intro hd _ i incoming memory hin
      obtain ⟨_, states, memories, _, _, _, _, _, _, hstates, _, hnoneIff, _, _, hinit⟩ :=
        actual_window_frame rate rewards C_star C_h z hc k
      have he := (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj ((hstates i).symm.trans hin)).1
      have hnone : incoming.lastDown = none := he ▸ (hnoneIff i).mp (hinit hkval i)
      have hbank := (actual_window_bank rate rewards C_star C_h z hc k i incoming memory hin).1
      rw [hkval, List.take_zero] at hbank
      change incoming.downBatch = _ at hbank
      have hm := source_window_initial_missing rate rewards C_star C_h z (by have := k.isLt; omega)
      have hk0 : k = ⟨0, by have := k.isLt; omega⟩ := Fin.ext hkval
      have hi : i ∈ pendingAt(((W).get k).input.time.val) := by
        have hmissing := pendingNat_eq_window_missing rate rewards C_star C_h z k hd
        change pendingAt(((W).get k).input.time.val) = _ at hmissing
        have hm' : missing rate ((W).get k) = Finset.univ := by
          simpa only [hk0, List.get_eq_getElem] using hm
        rw [hmissing]
        exact hm'.symm ▸ Finset.mem_univ i
      rw [ite_eq_left hi, ite_eq_left hnone, hbank]
      have ht := (source_window_record_calendar rate rewards C_star C_h z k).1
      change ((W).get k).input.time.val = s₀ + k.val at ht
      have htfix : ((W).get k).input.time.val = fixing.val := by omega
      rw [htfix]
      exact snapshotBefore_at_or_before_fixing _ _ _ _ _ _ _ _ le_rfl
  | succ l ih =>
      intro hd ht i incoming memory hin
      let prev : Fin (W).length := ⟨l, by have := k.isLt; omega⟩
      let a := (W).get prev
      let b := (W).get k
      have haTime := (source_window_record_calendar rate rewards C_star C_h z prev).1
      have hbTime := (source_window_record_calendar rate rewards C_star C_h z k).1
      change a.input.time.val = s₀ + l at haTime
      change b.input.time.val = s₀ + k.val at hbTime
      have hsucc : b.input.time.val = a.input.time.val + 1 := by omega
      have hprev : prev.val < k.val := by dsimp only [prev]; omega
      have had := supported_predecessors rate rewards C_star C_h z k prev hprev.le hd
      have hat : a.input.time.val < m₀ := by change b.input.time.val < _ at ht; omega
      obtain ⟨_, states, memories, _, _, _, _, _, _, hstates, _, hanone, _⟩ :=
        actual_window_frame rate rewards C_star C_h z hc prev
      obtain ⟨_, next, nextMemory, _, _, _, _, _, _, hnext, _, hbnone, _⟩ :=
        actual_window_frame rate rewards C_star C_h z hc k
      have he := (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj ((hnext i).symm.trans hin)).1
      have hpb := window_snapshot_projection rate rewards C_star C_h z n hc payload hp k hd ht
      have hpa := window_snapshot_projection rate rewards C_star C_h z n hc payload hp prev had hat
      let qa := replay[i,fixing] (initial p
          ((actualFirstLiveSeed rate z rewards C_star C_h hc).followers i).downBatch 0)
        a.input.time.val
      let qb := replay[i,fixing] (initial p
          ((actualFirstLiveSeed rate z rewards C_star C_h hc).followers i).downBatch 0)
        b.input.time.val
      let A := (data a.input.time).snapshot
      let B := (data b.input.time).snapshot
      have hAm : A.missing = pendingAt(a.input.time.val) :=
        hpa.1.trans (pendingNat_eq_window_missing rate rewards C_star C_h z prev had).symm
      have hBm : B.missing = pendingAt(b.input.time.val) :=
        hpb.1.trans (pendingNat_eq_window_missing rate rewards C_star C_h z k hd).symm
      have hAs : A.status i = (states i).status := hpa.2 i _ _ (hstates i)
      have hBs : B.status i = incoming.status := hpb.2 i _ _ hin
      have hBn : incoming.lastDown = none ↔ B.status i = .unoccupied := by
        rw [hBs, ← he]; exact (hbnone i).symm
      have hentry := auxiliaryLive_on_prefix rate rewards C_star C_h z n payload hp a.input.time
        (by omega) hat a (source_window_record_calendar rate rewards C_star C_h z prev).2
      have hAB : B = ActiveRoundActions.finishLiveRound p.two_le_m A (L a.input.time).input
          (L a.input.time).rewards (installationFlag payload a) := by
        exact (snapshot_successor L a.input.time b.input.time hsucc).trans
          (congrArg (fun flags => ActiveRoundActions.finishLiveRound p.two_le_m A (L a.input.time).input
            (L a.input.time).rewards flags) hentry.2)
      have hne : A.missing.Nonempty := by
        rw [hAm]; exact (pendingNat_nonempty_iff rate rewards C_star C_h z _).mpr had
      have hstatus : B.status i = ActiveRoundActions.statusAfterAcceptance A (L a.input.time).input
          (installationFlag payload a) i := by
        rw [hAB]; exact finish_status_while_missing A _ _ _ hne i
      have hmem : i ∈ B.missing ↔ i ∈ A.missing ∧ ¬ physicalConfirmation p payload.assignment data i a.input.time := by
        rw [hAB]
        exact finish_missing_iff A _ _ _ i
      have hsafe := supported_strict_predecessor_safe rate rewards C_star C_h z k prev hprev hd
      have hround : advance[i,fixing] qa a.input.time = serve[i,fixing] qa a.input.time := by
        have hbound : ¬ a.input.time.val < fixing.val := by omega
        have ho : (data a.input.time).overflowAfter ≠ true := by
          change decide (_ = _) ≠ true
          exact fun h => hsafe.2.2.2 (of_decide_eq_true h)
        have hcutoff : (data a.input.time).cutoffBefore ≠ true := Bool.false_ne_true
        by_cases hu : qa.phase.unresolved
        · unfold roundStep
          rw [ite_eq_right (not_or.mpr ⟨hbound, not_not.mpr hu⟩), ite_eq_right hcutoff]
          exact ite_eq_right (fun h => ho h.1)
        · have hservice : serve[i,fixing] qa a.input.time = qa := by
            cases hph : qa.phase <;> simp only [serviceStep, hph]
            · exact (hu (Or.inl hph)).elim
            · exact (hu (Or.inr hph)).elim
          exact (roundStep_terminal p β payload.assignment data i fixing
            (payload.downRecord i) qa a.input.time hu).trans hservice.symm
      have hq : qb = serve[i,fixing] qa a.input.time := by
        change snapshotBefore _ _ _ _ _ _ _ _ b.input.time.val = _
        rw [hsucc]
        exact (snapshotBefore_succ β payload.assignment data i fixing
          (payload.downRecord i) _ a.input.time).trans hround
      have ih' := ih prev rfl had hat i (states i) (memories i) (hstates i)
      change (if i ∈ pendingAt(a.input.time.val) then
        if (states i).lastDown = none then qa = initial p (states i).downBatch 0
        else qa.phase = .acceptedUnconfirmed ∧ qa.acceptedStart = (payload.downRecord i).val.sigma
        else qa.phase = .confirmed) at ih'
      change (if i ∈ pendingAt(b.input.time.val) then
        if incoming.lastDown = none then qb = initial p incoming.downBatch 0
        else qb.phase = .acceptedUnconfirmed ∧ qb.acceptedStart = (payload.downRecord i).val.sigma
        else qb.phase = .confirmed)
      have hAmem : i ∈ A.missing ↔ i ∈ pendingAt(a.input.time.val) :=
        ⟨fun h => hAm ▸ h, fun h => hAm.symm ▸ h⟩
      have hBmem : i ∈ B.missing ↔ i ∈ pendingAt(b.input.time.val) :=
        ⟨fun h => hBm ▸ h, fun h => hBm.symm ▸ h⟩
      have hmemNat : i ∈ pendingAt(b.input.time.val) ↔ i ∈ pendingAt(a.input.time.val) ∧
            ¬ physicalConfirmation p payload.assignment data i a.input.time :=
        hBmem.symm.trans (hmem.trans (and_congr_left (fun _ => hAmem)))
      by_cases hi : i ∈ pendingAt(a.input.time.val)
      · rw [ite_eq_left hi] at ih'
        by_cases hn : (states i).lastDown = none
        · rw [ite_eq_left hn] at ih'
          have hu : A.status i = .unoccupied := hAs.trans ((hanone i).mpr hn)
          have hnc : ¬ physicalConfirmation p payload.assignment data i a.input.time := by
            intro h
            rcases ActiveRoundActions.confirmation_implies_occupied p.two_le_m A _ _ i h with h | h <;>
              rw [hu] at h <;> cases h
          have hib : i ∈ pendingAt(b.input.time.val) := hmemNat.mpr ⟨hi, hnc⟩
          rw [ite_eq_left hib]
          have hnservice := actual_awaiting_normal_service rate rewards C_star C_h z n payload hp prev k hprev hd hat
            i hi fixing hfixing (states i) (memories i) (hstates i) hn
            (actual_window_bank rate rewards C_star C_h z hc prev i _ _ (hstates i)).2
          have hbank := actual_awaiting_bank_step rate rewards C_star C_h z n payload hp prev k (by omega) hd hat
            i hi (states i) incoming (memories i) memory (hstates i) hin hn
          rw [hq, ih']
          rw [hnservice]
          rw [← hbank]
          by_cases hf : installationFlag payload a i = true
          · have hs := (acceptedDown_selected a i (payload.downRecord i)
              ((actual_installation_flag_iff rate rewards C_star C_h z hc prev payload i).mp hf))
            have hrow := actual_auxiliary_row rate rewards C_star C_h z prev hc
            have hsel : (L a.input.time).input.slot = PublicDiscreteDraws.downSlot ∧
                (L a.input.time).input.selected = i := by rw [hrow] at hs; exact hs
            have hb : B.status i = .pending := by
              rw [hstatus]; simp only [ActiveRoundActions.statusAfterAcceptance, hu, hsel.1, hsel.2, hf,
                true_and, ite_true]
            have hnb : incoming.lastDown ≠ none := fun h => by have := hBn.mp h; rw [hb] at this; cases this
            rw [ite_eq_right hnb, ite_eq_left hf]
            exact ⟨rfl, rfl⟩
          · have hb : B.status i = .unoccupied := by
              rw [hstatus]; simp only [ActiveRoundActions.statusAfterAcceptance, hf, Bool.false_eq_true, and_false, ite_false, hu]
            rw [ite_eq_left (hBn.mpr hb), ite_eq_right hf]
        · rw [ite_eq_right hn] at ih'
          have hu : A.status i ≠ .unoccupied := fun h => hn ((hanone i).mp (hAs.symm ▸ h))
          have hnb : incoming.lastDown ≠ none := fun h => hu
            ((hstatus.trans (ite_eq_right (fun h => hu h.1))).symm.trans (hBn.mp h))
          by_cases hconf : physicalConfirmation p payload.assignment data i a.input.time
          · rw [ite_eq_right (fun h => (hmemNat.mp h).2 hconf)]
            rw [hq]; simp only [serviceStep, ih'.1, hconf, ite_true]
          · rw [ite_eq_left (hmemNat.mpr ⟨hi, hconf⟩), ite_eq_right hnb, hq]
            simpa only [serviceStep, ih'.1, hconf, ite_false] using ih'
      · rw [ite_eq_right hi] at ih'
        rw [ite_eq_right (fun h => hi (hmemNat.mp h).1), hq]
        simp only [serviceStep, ih']

/-- Outside the actual supported source dates, the same replay service
vanishes by the ORIGINAL continuation's zero padding. This does not assert
that a still-unresolved padded task has `J = 0`. -/
theorem off_support_X_zero (hS : (supportedDates).Nonempty)
    (i : ActiveRoundActions.Follower p.m) (incoming : LocalState p) (t : Fin p.T)
    (hd : t.val + 1 ∉ supportedDates) : X p payload.assignment data i incoming t = 0 := by
  have hsigma := sigma_eq_physicalStart_succ rate rewards C_star C_h z hS
  change sigma rate rewards C_star C_h z = s₀ + 1 at hsigma
  have hout : t.val < s₀ ∨ theta rate rewards C_star C_h z - 1 ≤ t.val := by
    by_contra hn
    apply hd
    rw [supportDates_eq_interval]
    apply Finset.mem_Ico.mpr
    rw [hsigma]
    omega
  apply padding_X_zero rate rewards C_star C_h z n payload hp actualOverflowAfter i incoming t
  rcases hout with hs | he
  · exact Or.inl hs
  · exact Or.inr ((min_le_right _ _).trans he)

/-- An absent actual record gives zero service, without choosing another
record, state or payload for that date. -/
theorem absent_record_X_zero (hS : (supportedDates).Nonempty)
    (i : ActiveRoundActions.Follower p.m) (incoming : LocalState p) (t : Fin p.T)
    (hr : actualRecord rate rewards C_star C_h t z = none) :
    X p payload.assignment data i incoming t = 0 := by
  apply off_support_X_zero rate rewards C_star C_h z n payload hp hS i incoming t
  intro hd
  obtain ⟨k, hdate, _⟩ := (supportDates_mem_iff rate rewards C_star C_h z (t.val + 1)).mp hd
  change ((W).get k).input.time.val + 1 = t.val + 1 at hdate
  have htime : ((W).get k).input.time = t := Fin.ext (Nat.add_right_cancel hdate)
  have hlookup := (source_window_record_calendar rate rewards C_star C_h z k).2
  change actualRecord rate rewards C_star C_h ((W).get k).input.time z = some ((W).get k) at hlookup
  rw [htime, hr] at hlookup
  cases hlookup

end ActualSource

/-- Nonempty original prefixes produce one actual payload and launch for all
queried dates. The same auxiliary snapshot and stopped replay supply both
incoming correspondence and the physical service summand. -/
theorem actual_prefix_correspondence
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (n : ℕ) :
    prefixDates rate rewards C_star C_h z n = ∅ ∨
    ∃ (payload : ReferenceActivePhysicalStep.Payload rate)
      (hp : payload0 rate rewards C_star C_h z = some payload)
      (hc : (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true),
    let live := auxiliaryLive rate rewards C_star C_h z n payload hp
    let calendar := fromLive p payload.assignment live (fun _ => false)
      (fun t => decide (ReferenceFirstLiveOverflowReadout.wholeFirstLiveOverflowRound rate rewards C_star C_h z = some (t.val + 1)))
    payload.sigma.val = start rate rewards C_star C_h z ∧
    (∀ i, (payload.downRecord i).val.sigma = start rate rewards C_star C_h z + 1) ∧
    ∀ t ∈ prefixDates rate rewards C_star C_h z n,
    ∃ (r : RoundRecord (p := p) (rate := rate))
      (states : Fin (p.m - 1) → State p rate.eta)
      (memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p),
    actualRecord rate rewards C_star C_h t z = some r ∧ r.input.time = t ∧
    (calendar t).snapshot.missing = pendingNat rate rewards C_star C_h t.val z ∧
    ∀ i : ActiveRoundActions.Follower p.m,
    r.input.state.followers i = .ordinary (states i) (memories i) ∧
    (r.output.preparation.followers.followers i).configuration = .ordinary (states i) (memories i) ∧
    (calendar t).snapshot.status i = (states i).status ∧
    let q := snapshotBefore p (CanonicalRecordingRates.beta p rate.eta.val) payload.assignment calendar i
      payload.sigma (payload.downRecord i)
      (initial p ((actualFirstLiveSeed rate z rewards C_star C_h hc).followers i).downBatch 0) t.val
    (if i ∈ pendingNat rate rewards C_star C_h t.val z then
      if (states i).lastDown = none then q = initial p (states i).downBatch 0
      else q.phase = .acceptedUnconfirmed ∧ q.acceptedStart = (payload.downRecord i).val.sigma
    else q.phase = .confirmed) ∧
    (i ∈ pendingNat rate rewards C_star C_h t.val z →
      (q.phase = .awaitingDown ↔ (states i).lastDown = none) ∧
      (q.phase = .acceptedUnconfirmed ↔ (states i).lastDown = some (payload.downRecord i))) ∧
    J p payload.assignment calendar payload.sigma q t = (if i ∈ pendingNat rate rewards C_star C_h t.val z then 1 else 0) ∧
    J p payload.assignment calendar payload.sigma q t * X p payload.assignment calendar i q t =
      if i ∈ pendingNat rate rewards C_star C_h t.val z ∧ downSelected p i r.input.row t ∧
        (((states i).lastDown = none ∧ 0 < (preparedOwnObservation r i).val.val) ∨
          ((states i).lastDown = some (payload.downRecord i) ∧
            CoordinatorLocalArmChoice.currentDownHash payload (r.input.row.2 t) i = 0 ∧
            0 < CoordinatorLocalArmChoice.ownGridObservationValue r.output.preparation.coordinatorObservation))
      then 1 else 0 := by
  rcases actual_prefix_projection rate rewards C_star C_h z n with hempty | ⟨payload, hp, hprojection⟩
  · exact Or.inl hempty
  by_cases hempty : prefixDates rate rewards C_star C_h z n = ∅
  · exact Or.inl hempty
  obtain ⟨u, hu⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
  obtain ⟨_, _, hud⟩ := (Finset.mem_filter.mp hu).2
  have hc := crossing_of_support rate rewards C_star C_h z (u.val + 1) hud
  have hprov := source_window_provenance rate rewards C_star C_h z hc
  dsimp only at hprov
  rcases hprov with hzero | ⟨hW, installed, selected, _, hinstalled, _, _, hp0, _⟩
  · obtain ⟨k, _, _⟩ := (supportDates_mem_iff rate rewards C_star C_h z (u.val + 1)).mp hud
    have := k.isLt
    omega
  have hpay : payload = installed.registers.payload := Option.some.inj (hp.symm.trans hp0)
  have hstamp : payload.sigma.val = start rate rewards C_star C_h z := by
    rw [hpay, hinstalled]
    exact (source_window_record_calendar rate rewards C_star C_h z ⟨0, hW⟩).1.trans (Nat.add_zero _)
  refine Or.inr ⟨payload, hp, hc, hstamp, ?_, ?_⟩
  · intro i
    exact (congrArg OrdinaryMessageCodec.DownFields.sigma (payload.downRecord_fields i)).trans
      (congrArg (· + 1) hstamp)
  intro t ht
  obtain ⟨hs, hstop, hd⟩ := (Finset.mem_filter.mp ht).2
  obtain ⟨r, selected, states, memories, hr, hrt, _, _, hin, hchoice, _, _, _, hmissing, hstatus⟩ :=
    hprojection t hs hstop hd
  refine ⟨r, states, memories, hr, hrt, hmissing, ?_⟩
  obtain ⟨k, hdate, _⟩ := (supportDates_mem_iff rate rewards C_star C_h z (t.val + 1)).mp hd
  change ((window rate rewards C_star C_h z).get k).input.time.val + 1 = t.val + 1 at hdate
  have htime : ((window rate rewards C_star C_h z).get k).input.time = t := Fin.ext (Nat.add_right_cancel hdate)
  have hlookup := (source_window_record_calendar rate rewards C_star C_h z k).2
  change actualRecord rate rewards C_star C_h ((window rate rewards C_star C_h z).get k).input.time z =
    some ((window rate rewards C_star C_h z).get k) at hlookup
  rw [htime] at hlookup
  have hrecord : r = (window rate rewards C_star C_h z).get k := Option.some.inj (hr.symm.trans hlookup)
  subst r
  intro i
  refine ⟨hin i, hchoice i, hstatus i, ?_⟩
  have hd' : ((window rate rewards C_star C_h z).get k).input.time.val + 1 ∈ supportDates rate rewards C_star C_h z := htime.symm ▸ hd
  have ht' : ((window rate rewards C_star C_h z).get k).input.time.val < stop rate rewards C_star C_h z n := htime.symm ▸ hstop
  have hcorris := actual_incoming_correspondence rate rewards C_star C_h z n payload hp hc payload.sigma hstamp
    k hd' ht' i (states i) (memories i) (hin i)
  rw [← htime]
  refine ⟨hcorris, ?_⟩
  let live := auxiliaryLive rate rewards C_star C_h z n payload hp
  let calendar := fromLive p payload.assignment live (fun _ => false)
    (fun t => decide (ReferenceFirstLiveOverflowReadout.wholeFirstLiveOverflowRound rate rewards C_star C_h z = some (t.val + 1)))
  have hcorr := hcorris
  have hbound : payload.sigma.val ≤ ((window rate rewards C_star C_h z).get k).input.time.val := by
    rw [htime, hstamp]; exact hs
  have hcutoff : (calendar ((window rate rewards C_star C_h z).get k).input.time).cutoffBefore = false := rfl
  dsimp only [calendar, live] at hcutoff
  obtain ⟨selected, frameStates, frameMemories, _, _, hpselected, _, _, _, hframeStates, _, hnoneIff, hfields, _⟩ :=
    actual_window_frame rate rewards C_star C_h z hc k
  have he := (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj ((hframeStates i).symm.trans (hin i))).1
  have hpay : selected.view.payload = payload := Option.some.inj (hpselected.symm.trans hp)
  by_cases hi : i ∈ pendingNat rate rewards C_star C_h ((window rate rewards C_star C_h z).get k).input.time.val z
  · rw [ite_eq_left hi] at hcorr
    by_cases hn : (states i).lastDown = none
    · rw [ite_eq_left hn] at hcorr
      rw [hcorr]
      have hu : (states i).status = .unoccupied := he ▸ (hnoneIff i).mpr (he.symm ▸ hn)
      refine ⟨?_, ?_, ?_⟩
      · intro _
        simp only [initial, hn, reduceCtorEq, and_self]
      · simp only [J, initial, Phase.unresolved, hbound, hcutoff, true_or, true_and, ite_true, hi]
      · have hJ : J p payload.assignment calendar payload.sigma (initial p (states i).downBatch 0) ((window rate rewards C_star C_h z).get k).input.time = 1 := by
          simp only [calendar, live, J, initial, Phase.unresolved, hbound, hcutoff, true_or, true_and, ite_true]
        rw [hJ, one_mul]
        by_cases hdown : downSelected p i ((window rate rewards C_star C_h z).get k).input.row ((window rate rewards C_star C_h z).get k).input.time
        · have hrow := actual_auxiliary_row rate rewards C_star C_h z k hc
          have hinput := actual_selected_decoder_input rate rewards C_star C_h z n payload hp (fun t => decide (ReferenceFirstLiveOverflowReadout.wholeFirstLiveOverflowRound rate rewards C_star C_h z = some (t.val + 1)))
            k hd' ht' i hi (by rw [hrow] at hdown; exact hdown.1)
            (by rw [hrow] at hdown; exact hdown.2) (states i) (memories i) (hin i) hn
          simp only [X, initial, hinput, hdown, hn, hi, reduceCtorEq, false_and, or_false, true_and]
          have hel := currentRoundInput_eligible_iff p i ((window rate rewards C_star C_h z).get k).input.row ((window rate rewards C_star C_h z).get k).input.time
            (preparedOwnObservation ((window rate rewards C_star C_h z).get k) i) rate (states i)
          exact congrArg (fun P : Prop => if P then (1 : ℕ) else 0)
            (propext (hel.trans (by simp only [hdown, hu, true_and])))
        · have hel : ¬ AffineBatchDecoder.eligible (observationTrace p payload.assignment calendar i ((window rate rewards C_star C_h z).get k).input.time) := by
            rintro h
            obtain ⟨hslot, hdraw, _⟩ := (eligible_iff p payload.assignment calendar i ((window rate rewards C_star C_h z).get k).input.time).mp h
            have hrow := actual_auxiliary_row rate rewards C_star C_h z k hc
            exact hdown (by rw [hrow]; exact ⟨hslot, hdraw⟩)
          dsimp only [calendar, live] at hel
          simp only [X, initial, hel, hi, hdown, false_and, and_false, ite_false]
    · rw [ite_eq_right hn] at hcorr
      have hrecord : (states i).lastDown = some (payload.downRecord i) := by
        have h := hfields i (fun hu => hn (he ▸ (hnoneIff i).mp hu))
        simpa only [he, hpay] using h
      have hJ : J p payload.assignment calendar payload.sigma
          (snapshotBefore p (CanonicalRecordingRates.beta p rate.eta.val) payload.assignment calendar i payload.sigma (payload.downRecord i) (initial p ((actualFirstLiveSeed rate z rewards C_star C_h hc).followers i).downBatch 0)
            ((window rate rewards C_star C_h z).get k).input.time.val) ((window rate rewards C_star C_h z).get k).input.time = 1 := by
        simp only [calendar, live, J, Phase.unresolved, hcorr.1, hbound, hcutoff, or_true, true_and, ite_true]
      refine ⟨?_, ?_, ?_⟩
      · intro _
        simp only [hcorr.1, hrecord, reduceCtorEq, eq_self, and_self]
      · rw [hJ, ite_eq_left hi]
      · rw [hJ, one_mul]
        have hconf := actual_confirmation_iff rate rewards C_star C_h z n payload hp k hd' ht' i
        simp only [X, hcorr.1, hconf, hi, hrecord, reduceCtorEq, false_and, true_and, false_or]
  · rw [ite_eq_right hi] at hcorr
    refine ⟨fun h => (hi h).elim, ?_, ?_⟩
    · simp only [J, Phase.unresolved, hcorr, reduceCtorEq, or_self, false_and, and_false, hi, ite_false]
    · simp only [J, Phase.unresolved, hcorr, reduceCtorEq, or_self, false_and, and_false, hi, ite_false, zero_mul]

end Bandits.Support.ReferenceFirstLiveHandoverPhaseReplay

end
