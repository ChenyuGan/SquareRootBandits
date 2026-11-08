/-
Copyright (c) 2026 The Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.WaitedWordWindow
import Mathlib.Data.List.TakeDrop
import Lean.Elab.Tactic.Omega

/-!
# Chronological stopped replay of one DOWN handover channel

Internal deterministic mathematics for
`sources/zip4/manuscript/05_binary_transport.tex:30-53,244-281`,
`sources/zip4/manuscript/06_interruptions.tex:164-175`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:141-157`.

The local state below is analysis bookkeeping, not a physical protocol state.
Every physical snapshot, action input, reward row and external endpoint is
visible input data. Acceptance is computed from the returned `decodeStep`
output, the real parser and the strict-old/non-strict-current acceptance test.
Confirmation uses the incoming phase and actual selected-DOWN/hash-zero/
coordinator-positive feedback. Neither acceptance flags nor a quota-capped
counter are inputs. Failure and overflow retain their terminating update.

The public results give a genuine transition, its still-awaiting decoder-prefix
identity, and a two-batch decision progress seam with uniqueness derived in the
nonambiguity branch. They do not yet prove the arbitrary-horizon stopped
receiver quota or its calendar-count correspondence. Physical reachability,
snapshot/local-register consistency, fixed-awaited persistence, global failure
event inclusion, earlier-other-channel failure endpoints, and conditional laws
remain application obligations. No source-facing statement is certified here.
-/

@[expose] public section

namespace Bandits.Support.HandoverStoppedDecoderReplay

open ConstructorDimensions AffineChannelLaw OrdinaryMessageCodec
open ActiveRoundActions PublicDiscreteDraws

abbrev DecoderState (p : Parameters) :=
  AffineBatchDecoder.State p.T (AffineBatchDecoder.width p)

abbrev DecoderEntry (p : Parameters) :=
  AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p)

noncomputable abbrev Down (p : Parameters) (beta : ℝ) :=
  DownRecord (AffineBatchDecoder.codecParams p beta)

/-- The current valid record's actual flat binary encoding. -/
noncomputable def currentWord (p : Parameters) (beta : ℝ) (M : Down p beta) :
    AffineChannelLaw.Word (AffineBatchDecoder.width p) :=
  wordEquivFlat (AffineBatchDecoder.codecParams p beta)
    (encodeDown (AffineBatchDecoder.codecParams p beta) M)

/-- These are local analysis phases; failures and overflow stop only the analysis. -/
inductive Phase where
  | awaitingDown
  | acceptedUnconfirmed
  | confirmed
  | failedFalse
  | failedAmbiguous
  | cutoffOrHorizon
  | overflow
  deriving DecidableEq

def Phase.unresolved (ph : Phase) : Prop :=
  ph = .awaitingDown ∨ ph = .acceptedUnconfirmed

/-- The receiver's decoder, accepted-start register and local analysis phase. -/
structure LocalState (p : Parameters) where
  decoder : DecoderState p
  acceptedStart : ℕ
  phase : Phase

def initial (p : Parameters) (decoder : DecoderState p) (olderStart : ℕ) : LocalState p :=
  ⟨decoder, olderStart, .awaitingDown⟩

/-- Literal supplied physical data and endpoint markers for a calendar round.
`cutoffBefore` means the source cutoff/horizon already holds before observation;
`overflowAfter` means the first overflow update has occurred in this round.
No queue or global physical history is reconstructed from these markers. -/
structure RoundData (p : Parameters) (a : Assignment p.m p.K) where
  snapshot : Snapshot a
  input : ActiveRoundActions.RoundInput a (AffineBatchDecoder.width p)
  rewards : RewardRow p.K
  cutoffBefore : Bool
  overflowAfter : Bool

/-- Decoder input from the supplied snapshot and actual follower feedback. -/
noncomputable def observationTrace (p : Parameters) (a : Assignment p.m p.K)
    (data : Fin p.T → RoundData p a) (i : Follower p.m) : AffineBatchDecoder.Trace p :=
  fun t =>
    let r := data t
    { selected := decide (r.input.slot = downSlot ∧ r.input.selected = i ∧
        i ∈ r.snapshot.missing)
      receiverEnabled := decide (r.snapshot.status i = .unoccupied)
      sample := r.input.down.sample
      roundedReward := feedback p.two_le_m r.snapshot r.input r.rewards
        (followerPlayer p.two_le_m i) }

/-- Actual feedback confirmation; service additionally requires the incoming
`acceptedUnconfirmed` phase. -/
def physicalConfirmation (p : Parameters) (a : Assignment p.m p.K)
    (data : Fin p.T → RoundData p a) (i : Follower p.m) (t : Fin p.T) : Prop :=
  confirmation p.two_le_m (data t).snapshot (data t).input (data t).rewards i

/-- This adapter supplies snapshots from the accepted physical live fold.
Its acceptance flags are physical input data, not this replay's acceptance.
Agreement with local phases/registers requires a separate reachability proof. -/
noncomputable def fromLive (p : Parameters) (a : Assignment p.m p.K)
    (live : Fin p.T → LiveRoundData a (AffineBatchDecoder.width p))
    (cutoffBefore overflowAfter : Fin p.T → Bool) (t : Fin p.T) : RoundData p a :=
  ⟨ActiveObservationBridge.liveSnapshotBefore p a live t,
    (live t).input, (live t).rewards, cutoffBefore t, overflowAfter t⟩

theorem observationTrace_fromLive (p : Parameters) (a : Assignment p.m p.K)
    (live : Fin p.T → LiveRoundData a (AffineBatchDecoder.width p))
    (cutoffBefore overflowAfter : Fin p.T → Bool) (i : Follower p.m) :
    observationTrace p a (fromLive p a live cutoffBefore overflowAfter) i =
      ActiveObservationBridge.downObservationTrace p a live i := rfl

/-- Expand every physical gate, with no acceptance assumption. -/
theorem eligible_iff (p : Parameters) (a : Assignment p.m p.K)
    (data : Fin p.T → RoundData p a) (i : Follower p.m) (t : Fin p.T) :
    AffineBatchDecoder.eligible (observationTrace p a data i t) ↔
      (data t).input.slot = downSlot ∧ (data t).input.selected = i ∧
      i ∈ (data t).snapshot.missing ∧ (data t).snapshot.status i = .unoccupied ∧
      0 < feedback p.two_le_m (data t).snapshot (data t).input (data t).rewards
        (followerPlayer p.two_le_m i) := by
  simp only [AffineBatchDecoder.eligible, observationTrace, decide_eq_true_eq]
  tauto

/-- Use the accepted bridge, rather than postulate an affine equation, when
the physical live-prefix data are supplied. -/
theorem live_positive_equation (p : Parameters) (a : Assignment p.m p.K)
    (live : Fin p.T → LiveRoundData a (AffineBatchDecoder.width p))
    (cutoffBefore overflowAfter : Fin p.T → Bool) (i : Follower p.m) (t : Fin p.T)
    (hpos : AffineBatchDecoder.eligible
      (observationTrace p a (fromLive p a live cutoffBefore overflowAfter) i t)) :
    AffineBatchDecoder.equation (live t).input.down.sample (live t).input.down.word := by
  obtain ⟨hslot, hselected, hmissing, hstatus, hy⟩ :=
    (eligible_iff p a _ i t).mp hpos
  exact ActiveObservationBridge.live_unoccupied_down_positive_equation p a live t i
    hslot hselected hmissing hstatus hy

/-- Parse the actual returned raw word, not a separately chosen batch output. -/
noncomputable def parseOutput (p : Parameters) (beta : ℝ)
    (raw : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p))) :
    Option (Down p beta) :=
  parseDown (AffineBatchDecoder.codecParams p beta)
    (raw.map (wordEquivFlat (AffineBatchDecoder.codecParams p beta)).symm)

theorem parseOutput_currentWord (p : Parameters) (beta : ℝ) (M : Down p beta) :
    parseOutput p beta (some (currentWord p beta M)) = some M := by
  simp only [parseOutput, Option.map_some, currentWord, Equiv.symm_apply_apply]
  exact parseDown_encode _ M

/-- The two distinct solutions in the actual retained equations. -/
def multipleSolutions (p : Parameters) (batch : List (DecoderEntry p)) : Prop :=
  ∃ u v, AffineBatchDecoder.satisfies (AffineBatchDecoder.samples batch) u ∧
    AffineBatchDecoder.satisfies (AffineBatchDecoder.samples batch) v ∧ u ≠ v

/-- A whole batch of actual positive tests of this fixed current word, after
fixation. This checks sample provenance, positivity and the sent word at every
retained timestamp, including any pending entries. It does not assume solutions. -/
def wholeCurrentBatch (p : Parameters) (beta : ℝ) (a : Assignment p.m p.K)
    (data : Fin p.T → RoundData p a) (i : Follower p.m) (fixing : Fin p.T)
    (M : Down p beta) (batch : List (DecoderEntry p)) : Prop :=
  ∀ e ∈ batch, fixing.val ≤ e.time.val ∧
    AffineBatchDecoder.eligible (observationTrace p a data i e.time) ∧
    e.sample = (data e.time).input.down.sample ∧
    (data e.time).input.down.word = currentWord p beta M

/-- First local failure cause, from the returned raw decision and real local
acceptance test. Completion is checked by the calling transition. -/
def falseDecision (p : Parameters) (beta : ℝ) (M : Down p beta)
    (olderStart : ℕ) (t : Fin p.T)
    (raw : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p))) : Prop :=
  ∃ other, parseOutput p beta raw = some other ∧ other ≠ M ∧
    acceptDown (AffineBatchDecoder.codecParams p beta) olderStart
      (WaitedWordWindow.sourceRound t) other

/-- Second local failure cause. The whole batch is tested against one fixed
awaited word and has multiple solutions. The acceptance window is explicit. -/
def ambiguityDecision (p : Parameters) (beta : ℝ) (a : Assignment p.m p.K)
    (data : Fin p.T → RoundData p a) (i : Follower p.m) (fixing : Fin p.T)
    (M : Down p beta) (olderStart : ℕ) (t : Fin p.T)
    (batch : List (DecoderEntry p))
    (raw : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p))) : Prop :=
  raw = none ∧ wholeCurrentBatch p beta a data i fixing M batch ∧
    acceptDown (AffineBatchDecoder.codecParams p beta) olderStart
      (WaitedWordWindow.sourceRound t) M ∧ multipleSolutions p batch

/-- Resolve one genuine completed decision, retaining the decoder's new state.
A false accepted word really updates the accepted-start register before stopping.
A mixed failed solve or rejected parse clears without acceptance or failure. -/
noncomputable def afterDecision (p : Parameters) (beta : ℝ) (a : Assignment p.m p.K)
    (data : Fin p.T → RoundData p a) (i : Follower p.m) (fixing : Fin p.T)
    (M : Down p beta) (s : LocalState p) (t : Fin p.T)
    (batch : List (DecoderEntry p))
    (raw : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p))) : LocalState p := by
  classical
  exact match parseOutput p beta raw with
  | some other =>
      if acceptDown (AffineBatchDecoder.codecParams p beta) s.acceptedStart
          (WaitedWordWindow.sourceRound t) other then
        { s with acceptedStart := other.val.sigma
                 phase := if other = M then .acceptedUnconfirmed else .failedFalse }
      else s
  | none =>
      if ambiguityDecision p beta a data i fixing M s.acceptedStart t batch raw then
        { s with phase := .failedAmbiguous }
      else s

/-- One positive receiver observation, using exactly the existing `decodeStep`.
Only the caller's awaiting branch can invoke this function. -/
noncomputable def receiverStep (p : Parameters) (beta : ℝ) (a : Assignment p.m p.K)
    (data : Fin p.T → RoundData p a) (i : Follower p.m) (fixing : Fin p.T)
    (M : Down p beta) (s : LocalState p) (t : Fin p.T) : LocalState p :=
  let tr := observationTrace p a data i
  let out := AffineBatchDecoder.decodeStep p tr s.decoder t
  let updated := { s with decoder := out.1 }
  if s.decoder.pending.length + 1 < AffineBatchDecoder.quota p then updated
  else afterDecision p beta a data i fixing M updated t
    (s.decoder.pending ++ [AffineBatchDecoder.entry p tr t]) out.2

/-- Incoming phase controls both decoding and confirmation; a new acceptance
cannot confirm until a later calendar round. -/
noncomputable def serviceStep (p : Parameters) (beta : ℝ) (a : Assignment p.m p.K)
    (data : Fin p.T → RoundData p a) (i : Follower p.m) (fixing : Fin p.T)
    (M : Down p beta) (s : LocalState p) (t : Fin p.T) : LocalState p := by
  classical
  exact match s.phase with
  | .awaitingDown =>
      if AffineBatchDecoder.eligible (observationTrace p a data i t) then
        receiverStep p beta a data i fixing M s t else s
  | .acceptedUnconfirmed =>
      if physicalConfirmation p a data i t then { s with phase := .confirmed } else s
  | _ => s

/-- Chronological round update. The first failure/overflow observation is
retained. Before-round cutoff does no service. All terminal phases absorb. -/
noncomputable def roundStep (p : Parameters) (beta : ℝ) (a : Assignment p.m p.K)
    (data : Fin p.T → RoundData p a) (i : Follower p.m) (fixing : Fin p.T)
    (M : Down p beta) (s : LocalState p) (t : Fin p.T) : LocalState p := by
  classical
  exact if t.val < fixing.val ∨ ¬ s.phase.unresolved then s
    else if (data t).cutoffBefore = true then { s with phase := .cutoffOrHorizon }
    else
      let updated := serviceStep p beta a data i fixing M s t
      if (data t).overflowAfter = true ∧ updated.phase.unresolved then
        { updated with phase := .overflow }
      else updated

/-- Finite per-calendar-round replay, without a quota cap. Chronology is a
property of the supplied round list, not an assumption about hidden ranks. -/
noncomputable def run (p : Parameters) (beta : ℝ) (a : Assignment p.m p.K)
    (data : Fin p.T → RoundData p a) (i : Follower p.m) (fixing : Fin p.T)
    (M : Down p beta) : List (Fin p.T) → LocalState p → LocalState p
  | [], s => s
  | t :: ts, s => run p beta a data i fixing M ts
      (roundStep p beta a data i fixing M s t)

/-- Literal state before a source calendar index. Pre-fixation rounds are inert. -/
noncomputable def snapshotBefore (p : Parameters) (beta : ℝ) (a : Assignment p.m p.K)
    (data : Fin p.T → RoundData p a) (i : Follower p.m) (fixing : Fin p.T)
    (M : Down p beta) (s : LocalState p) (n : ℕ) : LocalState p :=
  run p beta a data i fixing M (AffineBatchDecoder.roundPrefix p n) s

/-- Incoming unresolved task, after fixation and before any external cutoff. -/
noncomputable def J (p : Parameters) (a : Assignment p.m p.K)
    (data : Fin p.T → RoundData p a) (fixing : Fin p.T)
    (s : LocalState p) (t : Fin p.T) : ℕ := by
  classical
  exact if fixing.val ≤ t.val ∧ s.phase.unresolved ∧ (data t).cutoffBefore = false
    then 1 else 0

/-- Source service event from the incoming phase and actual physical feedback. -/
noncomputable def X (p : Parameters) (a : Assignment p.m p.K)
    (data : Fin p.T → RoundData p a) (i : Follower p.m)
    (s : LocalState p) (t : Fin p.T) : ℕ := by
  classical
  exact match s.phase with
  | .awaitingDown => if AffineBatchDecoder.eligible (observationTrace p a data i t) then 1 else 0
  | .acceptedUnconfirmed => if physicalConfirmation p a data i t then 1 else 0
  | _ => 0

/-- The literal calendar sum over source indices strictly before `n`.
This definition has no `min`, imposed receiver length or terminal rank. -/
noncomputable def N_before (p : Parameters) (beta : ℝ) (a : Assignment p.m p.K)
    (data : Fin p.T → RoundData p a) (i : Follower p.m) (fixing : Fin p.T)
    (M : Down p beta) (s : LocalState p) (n : ℕ) : ℕ :=
  ∑ t : Fin p.T, if t.val < n then
    let incoming := snapshotBefore p beta a data i fixing M s t.val
    J p a data fixing incoming t * X p a data i incoming t else 0

theorem roundStep_terminal (p : Parameters) (beta : ℝ) (a : Assignment p.m p.K)
    (data : Fin p.T → RoundData p a) (i : Follower p.m) (fixing : Fin p.T)
    (M : Down p beta) (s : LocalState p) (t : Fin p.T) (h : ¬ s.phase.unresolved) :
    roundStep p beta a data i fixing M s t = s := by
  unfold roundStep
  exact ite_eq_left (Or.inr h)

theorem run_terminal (p : Parameters) (beta : ℝ) (a : Assignment p.m p.K)
    (data : Fin p.T → RoundData p a) (i : Follower p.m) (fixing : Fin p.T)
    (M : Down p beta) (s : LocalState p) (ts : List (Fin p.T))
    (h : ¬ s.phase.unresolved) : run p beta a data i fixing M ts s = s := by
  induction ts with
  | nil => rfl
  | cons t ts ih => rw [run, roundStep_terminal p beta a data i fixing M s t h, ih]

theorem roundStep_cutoff (p : Parameters) (beta : ℝ) (a : Assignment p.m p.K)
    (data : Fin p.T → RoundData p a) (i : Follower p.m) (fixing : Fin p.T)
    (M : Down p beta) (s : LocalState p) (t : Fin p.T)
    (ht : fixing.val ≤ t.val) (hu : s.phase.unresolved)
    (hc : (data t).cutoffBefore = true) :
    roundStep p beta a data i fixing M s t = { s with phase := .cutoffOrHorizon } := by
  simp only [roundStep, Nat.not_lt.mpr ht, hu, not_true_eq_false, or_self,
    ite_false, hc, ite_true]

theorem afterDecision_decoder (p : Parameters) (beta : ℝ) (a : Assignment p.m p.K)
    (data : Fin p.T → RoundData p a) (i : Follower p.m) (fixing : Fin p.T)
    (M : Down p beta) (s : LocalState p) (t : Fin p.T) (batch : List (DecoderEntry p))
    (raw : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p))) :
    (afterDecision p beta a data i fixing M s t batch raw).decoder = s.decoder := by
  classical
  unfold afterDecision
  split
  · split <;> rfl
  · split <;> rfl

theorem afterDecision_awaiting (p : Parameters) (beta : ℝ) (a : Assignment p.m p.K)
    (data : Fin p.T → RoundData p a) (i : Follower p.m) (fixing : Fin p.T)
    (M : Down p beta) (s : LocalState p) (t : Fin p.T) (batch : List (DecoderEntry p))
    (raw : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p)))
    (h : (afterDecision p beta a data i fixing M s t batch raw).phase = .awaitingDown) :
    afterDecision p beta a data i fixing M s t batch raw = s := by
  classical
  cases hp : parseOutput p beta raw with
  | none =>
      by_cases ha : ambiguityDecision p beta a data i fixing M s.acceptedStart t batch raw
      · simp only [afterDecision, hp, ha, ite_true] at h
        cases h
      · simp only [afterDecision, hp, ha, ite_false]
  | some other =>
      by_cases ha : acceptDown (AffineBatchDecoder.codecParams p beta) s.acceptedStart
          (WaitedWordWindow.sourceRound t) other
      · simp only [afterDecision, hp, ha, ite_true] at h
        split at h <;> cases h
      · simp only [afterDecision, hp, ha, ite_false]

theorem receiverStep_decoder (p : Parameters) (beta : ℝ) (a : Assignment p.m p.K)
    (data : Fin p.T → RoundData p a) (i : Follower p.m) (fixing : Fin p.T)
    (M : Down p beta) (s : LocalState p) (t : Fin p.T) :
    (receiverStep p beta a data i fixing M s t).decoder =
      AffineBatchDecoder.step p (observationTrace p a data i) s.decoder t := by
  unfold receiverStep
  split
  · rfl
  · exact afterDecision_decoder p beta a data i fixing M _ t _ _

/-- Newly accepted receivers do not confirm during this receiver call. -/
theorem receiverStep_not_confirmed (p : Parameters) (beta : ℝ) (a : Assignment p.m p.K)
    (data : Fin p.T → RoundData p a) (i : Follower p.m) (fixing : Fin p.T)
    (M : Down p beta) (s : LocalState p) (t : Fin p.T)
    (hs : s.phase = .awaitingDown) :
    (receiverStep p beta a data i fixing M s t).phase ≠ .confirmed := by
  classical
  unfold receiverStep
  split
  · simpa only using (show s.phase ≠ .confirmed by rw [hs]; exact Phase.noConfusion)
  · unfold afterDecision
    dsimp only
    split
    · split
      · split <;> simp only [ne_eq, reduceCtorEq, not_false_eq_true]
      · simp only [hs, ne_eq, reduceCtorEq, not_false_eq_true]
    · split <;> simp only [hs, ne_eq, reduceCtorEq, not_false_eq_true]

/-- A genuine confirmation removes the unresolved local task exactly once;
all later rounds leave its decoder and accepted-start register untouched. -/
theorem serviceStep_confirmation (p : Parameters) (beta : ℝ) (a : Assignment p.m p.K)
    (data : Fin p.T → RoundData p a) (i : Follower p.m) (fixing : Fin p.T)
    (M : Down p beta) (s : LocalState p) (t : Fin p.T)
    (hs : s.phase = .acceptedUnconfirmed) (hc : physicalConfirmation p a data i t) :
    serviceStep p beta a data i fixing M s t = { s with phase := .confirmed } := by
  simp only [serviceStep, hs, hc, ite_true]

theorem run_append (p : Parameters) (beta : ℝ) (a : Assignment p.m p.K)
    (data : Fin p.T → RoundData p a) (i : Follower p.m) (fixing : Fin p.T)
    (M : Down p beta) (xs ys : List (Fin p.T)) (s : LocalState p) :
    run p beta a data i fixing M (xs ++ ys) s =
      run p beta a data i fixing M ys (run p beta a data i fixing M xs s) := by
  induction xs generalizing s with
  | nil => rfl
  | cons t ts ih => exact ih (roundStep p beta a data i fixing M s t)

private theorem step_pending_lt (p : Parameters) (tr : AffineBatchDecoder.Trace p)
    (s : DecoderState p) (t : Fin p.T) :
    (AffineBatchDecoder.step p tr s t).pending.length < AffineBatchDecoder.quota p := by
  unfold AffineBatchDecoder.step
  dsimp only
  split
  · assumption
  · exact AffineBatchDecoder.quota_pos p

theorem roundStep_pending_lt (p : Parameters) (beta : ℝ) (a : Assignment p.m p.K)
    (data : Fin p.T → RoundData p a) (i : Follower p.m) (fixing : Fin p.T)
    (M : Down p beta) (s : LocalState p) (t : Fin p.T)
    (hk : s.decoder.pending.length < AffineBatchDecoder.quota p) :
    (roundStep p beta a data i fixing M s t).decoder.pending.length <
      AffineBatchDecoder.quota p := by
  have hservice : (serviceStep p beta a data i fixing M s t).decoder.pending.length <
      AffineBatchDecoder.quota p := by
    cases hs : s.phase <;> simp only [serviceStep, hs]
    · split
      · rw [receiverStep_decoder]
        exact step_pending_lt p _ _ t
      · exact hk
    · split <;> exact hk
    all_goals exact hk
  unfold roundStep
  split
  · exact hk
  · split
    · exact hk
    · dsimp only
      split <;> exact hservice

private theorem receiverStep_awaiting_start (p : Parameters) (beta : ℝ)
    (a : Assignment p.m p.K) (data : Fin p.T → RoundData p a)
    (i : Follower p.m) (fixing : Fin p.T) (M : Down p beta) (s : LocalState p)
    (t : Fin p.T)
    (h : (receiverStep p beta a data i fixing M s t).phase = .awaitingDown) :
    (receiverStep p beta a data i fixing M s t).acceptedStart = s.acceptedStart := by
  by_cases hk : s.decoder.pending.length + 1 < AffineBatchDecoder.quota p
  · simp only [receiverStep, hk, ite_true]
  · simp only [receiverStep, hk, ite_false] at h ⊢
    have heq := afterDecision_awaiting p beta a data i fixing M _ t _ _ h
    have hstart := congrArg (fun u : LocalState p => u.acceptedStart) heq
    exact hstart

private theorem serviceStep_awaiting (p : Parameters) (beta : ℝ)
    (a : Assignment p.m p.K) (data : Fin p.T → RoundData p a)
    (i : Follower p.m) (fixing : Fin p.T) (M : Down p beta) (s : LocalState p)
    (t : Fin p.T) (hk : s.decoder.pending.length < AffineBatchDecoder.quota p)
    (h : (serviceStep p beta a data i fixing M s t).phase = .awaitingDown) :
    s.phase = .awaitingDown ∧
      (serviceStep p beta a data i fixing M s t).acceptedStart = s.acceptedStart ∧
      (serviceStep p beta a data i fixing M s t).decoder =
        AffineBatchDecoder.step p (observationTrace p a data i) s.decoder t := by
  classical
  cases hs : s.phase <;> simp only [serviceStep, hs] at h ⊢
  · by_cases he : AffineBatchDecoder.eligible (observationTrace p a data i t)
    · simp only [he, ite_true] at h ⊢
      exact ⟨trivial, receiverStep_awaiting_start p beta a data i fixing M s t h,
        receiverStep_decoder p beta a data i fixing M s t⟩
    · simp only [he, ite_false]
      exact ⟨trivial, trivial, (AffineBatchDecoder.step_ineligible p _ s.decoder t hk he).symm⟩
  · by_cases hc : physicalConfirmation p a data i t
    · rw [ite_eq_left hc] at h
      cases h
    · rw [ite_eq_right hc, hs] at h
      cases h
  all_goals cases h

/-- If the outgoing round is still awaiting, its register did not change and
its decoder performed precisely the ordinary trace step (also on zero service).
No terminal predicate is supplied to this theorem. -/
theorem roundStep_awaiting (p : Parameters) (beta : ℝ) (a : Assignment p.m p.K)
    (data : Fin p.T → RoundData p a) (i : Follower p.m) (fixing : Fin p.T)
    (M : Down p beta) (s : LocalState p) (t : Fin p.T)
    (ht : fixing.val ≤ t.val) (hk : s.decoder.pending.length < AffineBatchDecoder.quota p)
    (h : (roundStep p beta a data i fixing M s t).phase = .awaitingDown) :
    s.phase = .awaitingDown ∧
      (roundStep p beta a data i fixing M s t).acceptedStart = s.acceptedStart ∧
      (roundStep p beta a data i fixing M s t).decoder =
        AffineBatchDecoder.step p (observationTrace p a data i) s.decoder t := by
  classical
  by_cases hu : s.phase.unresolved
  · have hguard : ¬ (t.val < fixing.val ∨ ¬ s.phase.unresolved) :=
      not_or.mpr ⟨Nat.not_lt.mpr ht, not_not.mpr hu⟩
    by_cases hc : (data t).cutoffBefore = true
    · rw [roundStep_cutoff p beta a data i fixing M s t ht hu hc] at h
      cases h
    · by_cases ho : (data t).overflowAfter = true ∧
          (serviceStep p beta a data i fixing M s t).phase.unresolved
      · rw [roundStep, ite_eq_right hguard, ite_eq_right hc] at h
        dsimp only at h
        rw [ite_eq_left ho] at h
        cases h
      · have heq : roundStep p beta a data i fixing M s t =
            serviceStep p beta a data i fixing M s t := by
          rw [roundStep, ite_eq_right hguard, ite_eq_right hc]
          exact ite_eq_right ho
        rw [heq] at h ⊢
        exact serviceStep_awaiting p beta a data i fixing M s t hk h
  · rw [roundStep_terminal p beta a data i fixing M s t hu] at h
    exact (hu (Or.inl h)).elim

/-- Genuine decoder-prefix identity. A still-awaiting replay has not silently
accepted, failed, confirmed or truncated. Its decoder is the existing decoder
run on exactly the supplied calendar prefix, and its accepted-start is unchanged.
This is an implication proved from transitions, not a supplied progress law. -/
theorem run_awaiting_prefix (p : Parameters) (beta : ℝ) (a : Assignment p.m p.K)
    (data : Fin p.T → RoundData p a) (i : Follower p.m) (fixing : Fin p.T)
    (M : Down p beta) (ts : List (Fin p.T)) (s : LocalState p)
    (ht : ∀ t ∈ ts, fixing.val ≤ t.val)
    (hk : s.decoder.pending.length < AffineBatchDecoder.quota p)
    (h : (run p beta a data i fixing M ts s).phase = .awaitingDown) :
    s.phase = .awaitingDown ∧
      (run p beta a data i fixing M ts s).acceptedStart = s.acceptedStart ∧
      (run p beta a data i fixing M ts s).decoder =
        AffineBatchDecoder.run p (observationTrace p a data i) ts s.decoder := by
  induction ts generalizing s with
  | nil => exact ⟨h, rfl, rfl⟩
  | cons t ts ih =>
      obtain ⟨hnext, hstart, hdecoder⟩ := ih
        (roundStep p beta a data i fixing M s t)
        (fun u hu => ht u (List.mem_cons_of_mem t hu))
        (roundStep_pending_lt p beta a data i fixing M s t hk) h
      obtain ⟨hprev, hstartStep, hdecoderStep⟩ :=
        roundStep_awaiting p beta a data i fixing M s t (ht t (List.mem_cons_self)) hk hnext
      refine ⟨hprev, hstart.trans hstartStep, ?_⟩
      simpa only [run, AffineBatchDecoder.run, hdecoderStep] using hdecoder

theorem parseOutput_none (p : Parameters) (beta : ℝ) :
    parseOutput p beta none = none := rfl

/-- A successful parsed batch is the unique solution of its retained equations.
This is what justifies the first local failure's unique-noncurrent wording. -/
theorem parsed_batch_unique (p : Parameters) (beta : ℝ)
    (batch : List (DecoderEntry p)) (other : Down p beta)
    (h : parseOutput p beta (AffineBatchDecoder.batchOutput batch) = some other) :
    AffineBatchDecoder.satisfies (AffineBatchDecoder.samples batch)
        (currentWord p beta other) ∧
      ∀ v, AffineBatchDecoder.satisfies (AffineBatchDecoder.samples batch) v →
        v = currentWord p beta other := by
  have hp : AffineBatchDecoder.parseBatch p beta .DOWN
      (AffineBatchDecoder.samples batch) = some other := h
  exact (AffineBatchDecoder.parseBatch_eq_some_iff_unique p beta .DOWN
    (AffineBatchDecoder.samples batch) other).mp hp

theorem afterDecision_false_cause (p : Parameters) (beta : ℝ)
    (a : Assignment p.m p.K) (data : Fin p.T → RoundData p a)
    (i : Follower p.m) (fixing : Fin p.T) (M : Down p beta)
    (s : LocalState p) (t : Fin p.T) (batch : List (DecoderEntry p))
    (raw : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p)))
    (hs : s.phase = .awaitingDown)
    (h : (afterDecision p beta a data i fixing M s t batch raw).phase = .failedFalse) :
    falseDecision p beta M s.acceptedStart t raw := by
  classical
  cases hp : parseOutput p beta raw with
  | none =>
      simp only [afterDecision, hp] at h
      split at h
      · cases h
      · rw [hs] at h
        cases h
  | some other =>
      by_cases ha : acceptDown (AffineBatchDecoder.codecParams p beta) s.acceptedStart
          (WaitedWordWindow.sourceRound t) other
      · simp only [afterDecision, hp, ha, ite_true] at h
        by_cases he : other = M
        · simp only [he, ite_true] at h
          cases h
        · exact ⟨other, hp, he, ha⟩
      · simp only [afterDecision, hp, ha, ite_false, hs] at h
        cases h

theorem afterDecision_ambiguity_cause (p : Parameters) (beta : ℝ)
    (a : Assignment p.m p.K) (data : Fin p.T → RoundData p a)
    (i : Follower p.m) (fixing : Fin p.T) (M : Down p beta)
    (s : LocalState p) (t : Fin p.T) (batch : List (DecoderEntry p))
    (raw : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p)))
    (hs : s.phase = .awaitingDown)
    (h : (afterDecision p beta a data i fixing M s t batch raw).phase = .failedAmbiguous) :
    ambiguityDecision p beta a data i fixing M s.acceptedStart t batch raw := by
  classical
  cases hp : parseOutput p beta raw with
  | none =>
      by_cases ha : ambiguityDecision p beta a data i fixing M s.acceptedStart t batch raw
      · exact ha
      · simp only [afterDecision, hp, ha, ite_false, hs] at h
        cases h
  | some other =>
      simp only [afterDecision, hp] at h
      split at h
      · split at h <;> cases h
      · rw [hs] at h
        cases h

/-- On a batch of real current-word positive tests, the current word solves
every equation. The accepted physical bridge supplies each equation. -/
theorem wholeCurrentBatch_live_satisfies (p : Parameters) (beta : ℝ)
    (a : Assignment p.m p.K)
    (live : Fin p.T → LiveRoundData a (AffineBatchDecoder.width p))
    (cutoffBefore overflowAfter : Fin p.T → Bool) (i : Follower p.m)
    (fixing : Fin p.T) (M : Down p beta) (batch : List (DecoderEntry p))
    (hw : wholeCurrentBatch p beta a (fromLive p a live cutoffBefore overflowAfter)
      i fixing M batch) :
    AffineBatchDecoder.satisfies (AffineBatchDecoder.samples batch) (currentWord p beta M) := by
  apply (AffineBatchDecoder.satisfies_samples_iff _ _).mpr
  intro e he
  obtain ⟨_, hepos, hsample, hword⟩ := hw e he
  have heq := live_positive_equation p a live cutoffBefore overflowAfter i e.time hepos
  dsimp only [fromLive] at hsample hword
  rw [← hsample, hword] at heq
  exact heq

/-- Uniqueness is derived here: with a known current solution, excluding two
distinct solutions makes the solver return exactly that current word. -/
theorem current_solution_decision (p : Parameters) (beta : ℝ)
    (M : Down p beta) (batch : List (DecoderEntry p))
    (hsat : AffineBatchDecoder.satisfies (AffineBatchDecoder.samples batch)
      (currentWord p beta M)) :
    (AffineBatchDecoder.batchOutput batch = some (currentWord p beta M) ∧
      parseOutput p beta (AffineBatchDecoder.batchOutput batch) = some M) ∨
    (AffineBatchDecoder.batchOutput batch = none ∧ multipleSolutions p batch) := by
  classical
  by_cases hm : multipleSolutions p batch
  · right
    exact ⟨(AffineBatchDecoder.solve_eq_none_iff_empty_or_ambiguous _).mpr (Or.inr hm), hm⟩
  · left
    have hraw : AffineBatchDecoder.batchOutput batch = some (currentWord p beta M) := by
      apply (AffineBatchDecoder.solve_eq_some_iff _ _).mpr
      refine ⟨hsat, fun v hv => ?_⟩
      by_contra hne
      exact hm ⟨currentWord p beta M, v, hsat, hv, Ne.symm hne⟩
    exact ⟨hraw, by rw [hraw]; exact parseOutput_currentWord p beta M⟩

/-- A concrete full current batch either accepts the current record or stops
for genuine ambiguity. No uniqueness or parsed-current output is assumed. -/
theorem afterDecision_current_progress (p : Parameters) (beta : ℝ)
    (a : Assignment p.m p.K) (data : Fin p.T → RoundData p a)
    (i : Follower p.m) (fixing : Fin p.T) (M : Down p beta)
    (s : LocalState p) (t : Fin p.T) (batch : List (DecoderEntry p))
    (hw : wholeCurrentBatch p beta a data i fixing M batch)
    (hlocal : acceptDown (AffineBatchDecoder.codecParams p beta) s.acceptedStart
      (WaitedWordWindow.sourceRound t) M)
    (hsat : AffineBatchDecoder.satisfies (AffineBatchDecoder.samples batch)
      (currentWord p beta M)) :
    ((afterDecision p beta a data i fixing M s t batch
        (AffineBatchDecoder.batchOutput batch)).phase = .acceptedUnconfirmed ∧
      (afterDecision p beta a data i fixing M s t batch
        (AffineBatchDecoder.batchOutput batch)).acceptedStart = M.val.sigma) ∨
    ((afterDecision p beta a data i fixing M s t batch
        (AffineBatchDecoder.batchOutput batch)).phase = .failedAmbiguous ∧
      ambiguityDecision p beta a data i fixing M s.acceptedStart t batch
        (AffineBatchDecoder.batchOutput batch)) := by
  classical
  rcases current_solution_decision p beta M batch hsat with ⟨_, hp⟩ | ⟨hr, hm⟩
  · left
    simp only [afterDecision, hp, hlocal, ite_true, and_self]
  · right
    have ha : ambiguityDecision p beta a data i fixing M s.acceptedStart t batch
        (AffineBatchDecoder.batchOutput batch) := ⟨hr, hw, hlocal, hm⟩
    have hp : parseOutput p beta (AffineBatchDecoder.batchOutput batch) = none := by
      rw [hr, parseOutput_none]
    exact ⟨by simp only [afterDecision, hp, ha, ite_true], ha⟩

/-- The preceding progress statement consumes the raw output actually returned
by `decodeStep` at this receiver's full-batch transition. Its decoder clears
even in the ambiguity branch. -/
theorem receiverStep_current_progress (p : Parameters) (beta : ℝ)
    (a : Assignment p.m p.K) (data : Fin p.T → RoundData p a)
    (i : Follower p.m) (fixing : Fin p.T) (M : Down p beta)
    (s : LocalState p) (t : Fin p.T)
    (hpos : AffineBatchDecoder.eligible (observationTrace p a data i t))
    (hboundary : s.decoder.pending.length + 1 = AffineBatchDecoder.quota p)
    (hw : wholeCurrentBatch p beta a data i fixing M
      (s.decoder.pending ++ [AffineBatchDecoder.entry p (observationTrace p a data i) t]))
    (hlocal : acceptDown (AffineBatchDecoder.codecParams p beta) s.acceptedStart
      (WaitedWordWindow.sourceRound t) M)
    (hsat : AffineBatchDecoder.satisfies (AffineBatchDecoder.samples
      (s.decoder.pending ++ [AffineBatchDecoder.entry p (observationTrace p a data i) t]))
      (currentWord p beta M)) :
    (receiverStep p beta a data i fixing M s t).decoder.pending = [] ∧
      ((receiverStep p beta a data i fixing M s t).phase = .acceptedUnconfirmed ∨
        (receiverStep p beta a data i fixing M s t).phase = .failedAmbiguous) := by
  have hout := AffineBatchDecoder.decodeStep_complete p (observationTrace p a data i)
    s.decoder t hpos hboundary
  have hn : ¬ s.decoder.pending.length + 1 < AffineBatchDecoder.quota p := by omega
  have hprogress := afterDecision_current_progress p beta a data i fixing M
    { s with decoder := (AffineBatchDecoder.decodeStep p (observationTrace p a data i)
      s.decoder t).1 } t _ hw hlocal hsat
  constructor
  · rw [receiverStep_decoder, AffineBatchDecoder.step_complete p _ _ t hpos hboundary]
  · simp only [receiverStep, ite_eq_right hn]
    rw [hout]
    rw [hout] at hprogress
    exact hprogress.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)

private theorem mem_second_window (p : Parameters) (tr : AffineBatchDecoder.Trace p)
    (ts : List (Fin p.T)) (pending : List (DecoderEntry p))
    (hk : pending.length < AffineBatchDecoder.quota p) (e : DecoderEntry p)
    (he : e ∈ WaitedWordWindow.secondPositiveWindow p tr ts pending hk) :
    e ∈ AffineBatchDecoder.positives p tr ts :=
  List.mem_of_mem_drop he

/-- A continued-service two-batch probe, not a stopped task quota. The first
batch has the arbitrary actual older pending entries and is cleared; the next
whole batch tests the current word, which either is uniquely decoded or causes
the explicit ambiguity failure. Every premise concerns raw trace/provenance,
chronology, source time, or the exact available test-prefix length. -/
theorem two_batch_decoder_progress (p : Parameters) (beta : ℝ)
    (a : Assignment p.m p.K)
    (live : Fin p.T → LiveRoundData a (AffineBatchDecoder.width p))
    (cutoffBefore overflowAfter : Fin p.T → Bool) (i : Follower p.m)
    (fixing : Fin p.T) (M : Down p beta) (olderStart : ℕ)
    (hsource : WaitedWordWindow.sourceRound fixing = M.val.sigma)
    (holder : olderStart < M.val.sigma)
    (ts : List (Fin p.T)) (s : DecoderState p)
    (hk : s.pending.length < AffineBatchDecoder.quota p)
    (hbefore : ∀ e ∈ s.pending, e.time.val < fixing.val)
    (hafter : ∀ t ∈ ts, fixing.val ≤ t.val)
    (hchron : ts.Pairwise (fun t u => t.val < u.val))
    (hfixed : ∀ t ∈ ts, AffineBatchDecoder.eligible
        (ActiveObservationBridge.downObservationTrace p a live i t) →
      (live t).input.down.word = currentWord p beta M)
    (hcount : (AffineBatchDecoder.positives p
      (ActiveObservationBridge.downObservationTrace p a live i) ts).length =
        AffineBatchDecoder.quota p - s.pending.length + AffineBatchDecoder.quota p) :
    let data := fromLive p a live cutoffBefore overflowAfter
    let tr := observationTrace p a data i
    let window := WaitedWordWindow.secondPositiveWindow p tr ts s.pending hk
    ∃ first t,
      AffineBatchDecoder.run p tr ts s = ⟨[], s.completed ++ [first, window]⟩ ∧
      first = s.pending ++ (AffineBatchDecoder.positives p tr ts).take
        (AffineBatchDecoder.quota p - s.pending.length) ∧
      first.length = AffineBatchDecoder.quota p ∧
      window.length = AffineBatchDecoder.quota p ∧
      AffineBatchDecoder.decisionTime window = some t ∧
      wholeCurrentBatch p beta a data i fixing M window ∧
      AffineBatchDecoder.satisfies (AffineBatchDecoder.samples window) (currentWord p beta M) ∧
      ((afterDecision p beta a data i fixing M
          ⟨⟨[], s.completed ++ [first, window]⟩, olderStart, .awaitingDown⟩ t window
          (AffineBatchDecoder.batchOutput window)).phase = .acceptedUnconfirmed ∨
        (afterDecision p beta a data i fixing M
          ⟨⟨[], s.completed ++ [first, window]⟩, olderStart, .awaitingDown⟩ t window
          (AffineBatchDecoder.batchOutput window)).phase = .failedAmbiguous) ∧
      AffineBatchDecoder.quota p - s.pending.length + AffineBatchDecoder.quota p ≤
        2 * AffineBatchDecoder.quota p := by
  dsimp only
  let data := fromLive p a live cutoffBefore overflowAfter
  let tr := observationTrace p a data i
  let window := WaitedWordWindow.secondPositiveWindow p tr ts s.pending hk
  have hcount' : (AffineBatchDecoder.positives p tr ts).length =
      AffineBatchDecoder.quota p - s.pending.length + AffineBatchDecoder.quota p := hcount
  obtain ⟨first, hrun, hfirst, hfirstLen, hlen, _, _, hle⟩ :=
    WaitedWordWindow.run_two_batch_window p tr ts s hk hcount' hchron
      (fun e he t ht => Nat.lt_of_lt_of_le (hbefore e he) (hafter t ht))
  have hw : wholeCurrentBatch p beta a data i fixing M window := by
    intro e he
    have hepos := mem_second_window p tr ts s.pending hk e he
    obtain ⟨ht, hel, hsamp⟩ := (AffineBatchDecoder.mem_positives_iff p tr ts e).mp hepos
    exact ⟨hafter e.time ht, hel, hsamp, hfixed e.time ht hel⟩
  have hsat := wholeCurrentBatch_live_satisfies p beta a live cutoffBefore overflowAfter
    i fixing M window hw
  have hne : window ≠ [] := by
    intro he
    have hlen' : window.length = AffineBatchDecoder.quota p := hlen
    rw [he] at hlen'
    simp only [List.length_nil] at hlen'
    have hq := AffineBatchDecoder.quota_pos p
    omega
  let last := window.getLast hne
  have hlast : AffineBatchDecoder.decisionTime window = some last.time := by
    simp only [AffineBatchDecoder.decisionTime, List.getLast?_map,
      List.getLast?_eq_some_getLast hne, Option.map_some, last]
  have hlocal : acceptDown (AffineBatchDecoder.codecParams p beta) olderStart
      (WaitedWordWindow.sourceRound last.time) M := by
    refine ⟨holder, ?_⟩
    have ht := (hw last (List.getLast_mem hne)).1
    rw [← hsource]
    exact Nat.add_le_add_right ht 1
  have hprogress := afterDecision_current_progress p beta a data i fixing M
    ⟨⟨[], s.completed ++ [first, window]⟩, olderStart, .awaitingDown⟩ last.time window
    hw hlocal hsat
  rw [hcount'] at hle
  exact ⟨first, last.time, hrun, hfirst, hfirstLen, hlen, hlast, hw, hsat,
    hprogress.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1), hle⟩

/-- A selected positive is counted from the incoming awaiting phase, including
when that very observation causes a local failure or the first overflow. -/
theorem receiver_tick_counted (p : Parameters) (a : Assignment p.m p.K)
    (data : Fin p.T → RoundData p a) (i : Follower p.m) (fixing : Fin p.T)
    (s : LocalState p) (t : Fin p.T) (ht : fixing.val ≤ t.val)
    (hs : s.phase = .awaitingDown) (hc : (data t).cutoffBefore = false)
    (hy : AffineBatchDecoder.eligible (observationTrace p a data i t)) :
    J p a data fixing s t * X p a data i s t = 1 := by
  have hu : s.phase.unresolved := Or.inl hs
  have hj : J p a data fixing s t = 1 := by
    unfold J
    exact ite_eq_left ⟨ht, hu, hc⟩
  rw [hj]
  simp only [X, hs, hy, ite_true, Nat.one_mul]

/-- Actual confirmation at an eligible calendar round is terminal even when
an overflow marker is also present after that round's update. -/
theorem roundStep_confirmation (p : Parameters) (beta : ℝ)
    (a : Assignment p.m p.K) (data : Fin p.T → RoundData p a)
    (i : Follower p.m) (fixing : Fin p.T) (M : Down p beta)
    (s : LocalState p) (t : Fin p.T) (ht : fixing.val ≤ t.val)
    (hs : s.phase = .acceptedUnconfirmed) (hc : (data t).cutoffBefore = false)
    (hy : physicalConfirmation p a data i t) :
    roundStep p beta a data i fixing M s t = { s with phase := .confirmed } := by
  have hu : s.phase.unresolved := Or.inr hs
  have hguard : ¬ (t.val < fixing.val ∨ ¬ s.phase.unresolved) :=
    not_or.mpr ⟨Nat.not_lt.mpr ht, not_not.mpr hu⟩
  have hcut : ¬ (data t).cutoffBefore = true := by rw [hc]; exact Bool.noConfusion
  rw [roundStep, ite_eq_right hguard, ite_eq_right hcut]
  dsimp only
  rw [serviceStep_confirmation p beta a data i fixing M s t hs hy]
  simp only [Phase.unresolved, reduceCtorEq, or_self, and_false, ite_false]

/-- The true confirmation indicator. This is a physical event in the incoming
accepted-unconfirmed phase; its value is unrelated to an imposed task length. -/
noncomputable def confirmationTick (p : Parameters) (a : Assignment p.m p.K)
    (data : Fin p.T → RoundData p a) (i : Follower p.m) (fixing : Fin p.T)
    (s : LocalState p) (t : Fin p.T) : ℕ := by
  classical
  exact if fixing.val ≤ t.val ∧ (data t).cutoffBefore = false ∧
    s.phase = .acceptedUnconfirmed ∧ physicalConfirmation p a data i t then 1 else 0

/-- The genuine confirmation count, folding the actual stopped transitions. -/
noncomputable def confirmationCount (p : Parameters) (beta : ℝ)
    (a : Assignment p.m p.K) (data : Fin p.T → RoundData p a)
    (i : Follower p.m) (fixing : Fin p.T) (M : Down p beta) :
    List (Fin p.T) → LocalState p → ℕ
  | [], _ => 0
  | t :: ts, s => confirmationTick p a data i fixing s t +
      confirmationCount p beta a data i fixing M ts
        (roundStep p beta a data i fixing M s t)

theorem confirmationCount_terminal (p : Parameters) (beta : ℝ)
    (a : Assignment p.m p.K) (data : Fin p.T → RoundData p a)
    (i : Follower p.m) (fixing : Fin p.T) (M : Down p beta)
    (ts : List (Fin p.T)) (s : LocalState p) (hu : ¬ s.phase.unresolved) :
    confirmationCount p beta a data i fixing M ts s = 0 := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
      have hg : ¬ (fixing.val ≤ t.val ∧ (data t).cutoffBefore = false ∧
          s.phase = .acceptedUnconfirmed ∧ physicalConfirmation p a data i t) :=
        fun h => hu (Or.inr h.2.2.1)
      rw [confirmationCount, roundStep_terminal p beta a data i fixing M s t hu,
        confirmationTick, ite_eq_right hg, Nat.zero_add, ih]

/-- At most one genuine confirmation on every finite replay, with no receiver
count premise, uniqueness premise, or terminal-rank premise. -/
theorem confirmationCount_le_one (p : Parameters) (beta : ℝ)
    (a : Assignment p.m p.K) (data : Fin p.T → RoundData p a)
    (i : Follower p.m) (fixing : Fin p.T) (M : Down p beta)
    (ts : List (Fin p.T)) (s : LocalState p) :
    confirmationCount p beta a data i fixing M ts s ≤ 1 := by
  classical
  induction ts generalizing s with
  | nil => exact Nat.zero_le 1
  | cons t ts ih =>
      by_cases hg : fixing.val ≤ t.val ∧ (data t).cutoffBefore = false ∧
          s.phase = .acceptedUnconfirmed ∧ physicalConfirmation p a data i t
      · have hstep := roundStep_confirmation p beta a data i fixing M s t
          hg.1 hg.2.2.1 hg.2.1 hg.2.2.2
        rw [confirmationCount, confirmationTick, ite_eq_left hg, hstep,
          confirmationCount_terminal p beta a data i fixing M ts _ (by
            simp only [Phase.unresolved, reduceCtorEq, or_self, not_false_eq_true]),
          Nat.add_zero]
      · rw [confirmationCount, confirmationTick, ite_eq_right hg, Nat.zero_add]
        exact ih _

/-- Earlier external truncation can only shorten this literal calendar sum.
Interpreting such an endpoint as an earlier ordinary decoder failure requires
an external witness of that failure and its source round; none is fabricated. -/
theorem N_before_mono (p : Parameters) (beta : ℝ) (a : Assignment p.m p.K)
    (data : Fin p.T → RoundData p a) (i : Follower p.m) (fixing : Fin p.T)
    (M : Down p beta) (s : LocalState p) (n k : ℕ) (hnk : n ≤ k) :
    N_before p beta a data i fixing M s n ≤ N_before p beta a data i fixing M s k := by
  apply Finset.sum_le_sum
  intro t _
  by_cases hn : t.val < n
  · have hk : t.val < k := Nat.lt_of_lt_of_le hn hnk
    simp only [ite_eq_left hn, ite_eq_left hk, le_refl]
  · rw [ite_eq_right hn]
    exact Nat.zero_le _

private theorem decoder_run_history (p : Parameters) (tr : AffineBatchDecoder.Trace p)
    (ts : List (Fin p.T)) (pending : List (DecoderEntry p))
    (history : List (List (DecoderEntry p))) :
    AffineBatchDecoder.run p tr ts ⟨pending, history⟩ =
      let base := AffineBatchDecoder.run p tr ts ⟨pending, []⟩
      ⟨base.pending, history ++ base.completed⟩ := by
  induction ts generalizing pending history with
  | nil => simp only [AffineBatchDecoder.run, List.append_nil]
  | cons t ts ih =>
      simp only [AffineBatchDecoder.run]
      let added := pending ++ AffineBatchDecoder.positiveAt p tr t
      by_cases hk : added.length < AffineBatchDecoder.quota p
      · have hstep₁ : AffineBatchDecoder.step p tr ⟨pending, history⟩ t =
            ⟨added, history⟩ := ite_eq_left hk
        have hstep₂ : AffineBatchDecoder.step p tr ⟨pending, []⟩ t =
            ⟨added, []⟩ := ite_eq_left hk
        rw [hstep₁, hstep₂]
        exact ih added history
      · have hstep₁ : AffineBatchDecoder.step p tr ⟨pending, history⟩ t =
            ⟨[], history ++ [added]⟩ := ite_eq_right hk
        have hstep₂ : AffineBatchDecoder.step p tr ⟨pending, []⟩ t =
            ⟨[], [added]⟩ := ite_eq_right hk
        rw [hstep₁, hstep₂]
        have hleft := ih [] (history ++ [added])
        have hright := ih [] [added]
        rw [hright]
        simpa only [List.append_assoc] using hleft

/-- Exactly `Q - oldLength` positives clear the first actual decoder batch,
including arbitrary older equations and completed-history audit data.
There is no successful-parse or no-failure premise. -/
theorem first_batch_clears (p : Parameters) (tr : AffineBatchDecoder.Trace p)
    (ts : List (Fin p.T)) (s : DecoderState p)
    (hk : s.pending.length < AffineBatchDecoder.quota p)
    (hcount : (AffineBatchDecoder.positives p tr ts).length =
      AffineBatchDecoder.quota p - s.pending.length) :
    AffineBatchDecoder.run p tr ts s =
      ⟨[], s.completed ++ [s.pending ++ AffineBatchDecoder.positives p tr ts]⟩ := by
  have hdec := AffineBatchDecoder.first_decision p tr ts s.pending hk hcount
  have hspec := AffineBatchDecoder.run_spec p tr ts ⟨s.pending, []⟩ hk (by
    simp only [List.not_mem_nil, false_implies, implies_true])
  have hbase : AffineBatchDecoder.run p tr ts ⟨s.pending, []⟩ =
      ⟨[], [s.pending ++ AffineBatchDecoder.positives p tr ts]⟩ := by
    cases hr : AffineBatchDecoder.run p tr ts ⟨s.pending, []⟩ with
    | mk pending completed =>
        have hp : pending = [] := by simpa only [hr] using hdec.2
        have hl : completed.length = 1 := by simpa only [hr] using hdec.1
        cases completed with
        | nil => simp only [List.length_nil] at hl; omega
        | cons batch tail =>
            have ht : tail = [] := by
              apply List.length_eq_zero_iff.mp
              simp only [List.length_cons] at hl
              omega
            have hb : batch = s.pending ++ AffineBatchDecoder.positives p tr ts := by
              simpa only [hr, hp, ht, AffineBatchDecoder.collected,
                List.flatten_cons, List.flatten_nil, List.append_nil, List.nil_append]
                using hspec.2.2
            rw [hp, ht, hb]
  have hh := decoder_run_history p tr ts s.pending s.completed
  rw [hbase] at hh
  exact hh

/-- Composition with the real still-awaiting replay, at the first threshold.
If it already stopped or accepted, `run_awaiting_prefix` deliberately does not
identify its later decoder with an unstopped decoder probe. -/
theorem awaiting_first_batch_clears (p : Parameters) (beta : ℝ)
    (a : Assignment p.m p.K) (data : Fin p.T → RoundData p a)
    (i : Follower p.m) (fixing : Fin p.T) (M : Down p beta)
    (ts : List (Fin p.T)) (s : LocalState p)
    (ht : ∀ t ∈ ts, fixing.val ≤ t.val)
    (hk : s.decoder.pending.length < AffineBatchDecoder.quota p)
    (hcount : (AffineBatchDecoder.positives p (observationTrace p a data i) ts).length =
      AffineBatchDecoder.quota p - s.decoder.pending.length)
    (h : (run p beta a data i fixing M ts s).phase = .awaitingDown) :
    (run p beta a data i fixing M ts s).decoder =
      ⟨[], s.decoder.completed ++ [s.decoder.pending ++
        AffineBatchDecoder.positives p (observationTrace p a data i) ts]⟩ := by
  rw [(run_awaiting_prefix p beta a data i fixing M ts s ht hk h).2.2]
  exact first_batch_clears p _ ts s.decoder hk hcount

end Bandits.Support.HandoverStoppedDecoderReplay

end
