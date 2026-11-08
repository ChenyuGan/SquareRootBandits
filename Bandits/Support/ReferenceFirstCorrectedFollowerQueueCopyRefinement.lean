/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCorrectedCoordinatorQueueOverflowCover
public import Bandits.Support.ReferenceFirstCorrectedFollowerRegisterOverflowCover

import Mathlib.Tactic

/-!
# Literal follower register copies and reached-service refinement

This module refines actual follower logging, offer, stored-seed, and pre-output
service observations to the accepted coordinator and follower register sites.
All records and optional collection segments are taken from the original
first-corrected source execution.

Sources: ZIP4 `appendix_a_local_protocol.tex:8-64`,
`06_interruptions.tex:40-100,192-233,246-299,355-361,391-408,425-426`,
`04_slow_fast_learner.tex:157-187,256-290`, and
`05_binary_transport.tex:7-43,60-114` under `sources/zip4/manuscript/`.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions
open BootstrapPrivateRoundStreams (SourceInput)
open ReferenceFirstCollectionCorrectedSliceNumericalPrefix
  (correctedCell sourceRecords birthIndex liveTail)
open ReferenceCollectionSegmentExtraction
open ReferenceFirstCorrectedCoordinatorQueueOverflowCover
  (CoordinatorQueueSite)
open ReferenceFirstCorrectedFollowerRegisterOverflowCover
  (CollectionFollowerRegisterSiteOf observeCollectionFollowerRegister?)
open ReferenceFirstCorrectedCurrentFollowerQueueOverflowCover
  (LiveFollowerRegisterSite observeLiveFollowerRegister)

namespace Bandits.Support.ReferenceFirstCorrectedFollowerQueueCopyRefinement

variable {p : Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ)

local notation "X" => SourceInput p
local notation "Record" => ReferenceActivePhysicalHorizon.RoundRecord
  (p := p) (rate := rate)
local notation "Segment" => ReferenceCollectionSegmentExtraction.Segment rate
local notation "Payload" => ReferenceActivePhysicalStep.Payload rate
local notation "Register" => Option (Option (OrdinaryMessageCodec.DownRecord
  (ReferencePrelaunchFollower.codecParams p rate.eta)) × ℕ)

/-! ## Logged and offered copies -/

/-- The actual logged last accepted DOWN register and its saved backlog.
Both DOWN diagnostics must be present in the record. -/
def recordLoggedRegister? (r : Record) (i : Fin (p.m - 1)) : Register :=
  (r.output.followers i).down.bind fun _ =>
    (r.output.followers i).downInput.map fun logged => (logged.lastDown, logged.backlog)

/-- The checked logging operation changes only the buffer, so the actual logged
pair equals the already observed CHOICE pair, including `lastDown`. -/
theorem recordLoggedRegister?_eq_choice_of_some (r : Record) (i : Fin (p.m - 1))
    (last : Option (OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))) (q : ℕ)
    (hread : recordLoggedRegister? rate r i = some (last, q)) :
    ReferenceFirstCorrectedCurrentFollowerQueueOverflowCover.followerChoiceRegister?
      (rate := rate) (some r) i = some (last, q) := by
  simp only [recordLoggedRegister?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hread
  obtain ⟨cut, hdown, logged, hlogged, heq⟩ := hread
  obtain ⟨choice, memory, logged0, hchoice, _hstatus, hlogging, hinput, _hcut⟩ :=
    ReferenceFollowerSparseEmissionRecovery.actualDownDiagnostic_choice r i cut hdown
  have hlog : logged0 = logged := Option.some.inj (hinput.symm.trans hlogged)
  subst logged0
  have hframe := ActiveFollowerLogging.checkedLogging_success_frame _ _ _ _ _ _ _ hlogging
  have hpair : (logged.lastDown, logged.backlog) = (choice.lastDown, choice.backlog) :=
    Prod.ext hframe.1 hframe.2.2.2.1
  simpa only [ReferenceFirstCorrectedCurrentFollowerQueueOverflowCover.followerChoiceRegister?,
    Option.bind_some, ReferenceFirstCorrectedCurrentFollowerQueueOverflowCover.followerRegisterObserver?,
    ReferenceFollowerFixedReply.actualChoice, hchoice] using congrArg some (hpair.symm.trans heq)

/-- The actual checked local UP offer before arm choice. Missing, invalid, or
nonselected offers remain absent. -/
def recordOfferedQueue? (r : Record) (i : Fin (p.m - 1)) : Option ℕ :=
  let prepared := ReferenceFollowerFixedReply.actualChoice r i
  match prepared.configuration with
  | .dagger => none
  | .ordinary state _ =>
      match ActiveFollowerQueueOperation.checkedUpOffer rate.eta prepared.follower prepared.row
          prepared.activation prepared.time state with
      | .offer M => some M.val.q
      | .noOffer | .failure => none

/-- An actual offered q is the current CHOICE backlog; its accepted
`lastDown` word is retained in the register observer. -/
theorem recordOfferedQueue?_eq_choice_of_some (r : Record) (i : Fin (p.m - 1))
    (q : ℕ) (hread : recordOfferedQueue? rate r i = some q) :
    ∃ last, ReferenceFirstCorrectedCurrentFollowerQueueOverflowCover.followerChoiceRegister?
      (rate := rate) (some r) i = some (last, q) := by
  unfold recordOfferedQueue? at hread
  cases hc : (ReferenceFollowerFixedReply.actualChoice r i).configuration with
  | dagger => simp only [hc, reduceCtorEq] at hread
  | ordinary state memory =>
      simp only [hc] at hread
      cases ho : ActiveFollowerQueueOperation.checkedUpOffer rate.eta
          (ReferenceFollowerFixedReply.actualChoice r i).follower
          (ReferenceFollowerFixedReply.actualChoice r i).row
          (ReferenceFollowerFixedReply.actualChoice r i).activation
          (ReferenceFollowerFixedReply.actualChoice r i).time state with
      | failure => simp only [ho, reduceCtorEq] at hread
      | noOffer => simp only [ho, reduceCtorEq] at hread
      | offer M =>
          have hfields := ActiveFollowerQueueOperation.checkedUpOffer_fields _ _ _ _ _ _ _ ho
          have hq : M.val.q = state.backlog := congrArg OrdinaryMessageCodec.UpFields.q hfields
          have hq' : state.backlog = q := hq.symm.trans
            (Option.some.inj (by simpa only [ho] using hread))
          refine ⟨state.lastDown, ?_⟩
          simp only [ReferenceFirstCorrectedCurrentFollowerQueueOverflowCover.followerChoiceRegister?,
            Option.bind_some, ReferenceFirstCorrectedCurrentFollowerQueueOverflowCover.followerRegisterObserver?,
            hc, hq']

/-! ## Immutable stored seeds -/

inductive StoredFollowerField where
  | input
  | choice
  | output
  | logged
  deriving DecidableEq, Repr

/-- The immutable initial queue is absent when no DOWN was accepted. -/
def storedDownSeed? (configuration : DeclaredFollowerLocalRound.LocalConfiguration p rate) :
    Option ℕ :=
  match configuration with
  | .dagger => none
  | .ordinary state _ => state.lastDown.map fun M => M.val.q

/-- The output follower configuration is exactly the successor configuration. -/
theorem followerOutput_eq_next (r : Record) (i : Fin (p.m - 1)) :
    (r.output.followers i).configuration = r.output.next.followers i := by
  rw [r.output_eq]
  rfl

/-- Read the stored initial queue at an actual follower field. For `.logged`
the read is specifically the original accepted DOWN q field, distinct from the
moving backlog. -/
def recordSeed? (r : Record) (i : Fin (p.m - 1)) : StoredFollowerField → Option ℕ
  | .input => storedDownSeed? rate (r.input.state.followers i)
  | .choice => storedDownSeed? rate (ReferenceFollowerFixedReply.actualChoice r i).configuration
  | .output => storedDownSeed? rate (r.output.followers i).configuration
  | .logged => (recordLoggedRegister? rate r i).bind fun register =>
      register.1.map fun M => M.val.q

/-- Any present seed is backed by an actual ordinary configuration and its
actual accepted DOWN word. -/
theorem recordSeed?_physical (r : Record) (i : Fin (p.m - 1))
    (field : StoredFollowerField) (q : ℕ) (hread : recordSeed? rate r i field = some q) :
    ∃ state memory M,
      (r.input.state.followers i = .ordinary state memory ∨
        (ReferenceFollowerFixedReply.actualChoice r i).configuration = .ordinary state memory ∨
        r.output.next.followers i = .ordinary state memory) ∧
      state.lastDown = some M ∧ M.val.q = q := by
  have stored (configuration : DeclaredFollowerLocalRound.LocalConfiguration p rate)
      (h : storedDownSeed? rate configuration = some q) :
      ∃ state memory M, configuration = .ordinary state memory ∧
        state.lastDown = some M ∧ M.val.q = q := by
    cases configuration with
    | dagger => cases h
    | ordinary state memory =>
        obtain ⟨M, hM, hq⟩ := Option.map_eq_some_iff.mp h
        exact ⟨state, memory, M, rfl, hM, hq⟩
  cases field with
  | input =>
      obtain ⟨state, memory, M, hc, hM, hq⟩ := stored _ hread
      exact ⟨state, memory, M, Or.inl hc, hM, hq⟩
  | choice =>
      obtain ⟨state, memory, M, hc, hM, hq⟩ := stored _ hread
      exact ⟨state, memory, M, Or.inr (Or.inl hc), hM, hq⟩
  | output =>
      obtain ⟨state, memory, M, hc, hM, hq⟩ := stored _ hread
      exact ⟨state, memory, M, Or.inr (Or.inr
        ((followerOutput_eq_next rate r i).symm.trans hc)), hM, hq⟩
  | logged =>
      obtain ⟨⟨last, backlog⟩, hcopy, hseed⟩ := Option.bind_eq_some_iff.mp hread
      obtain ⟨M, hlast, hq⟩ := Option.map_eq_some_iff.mp hseed
      have hchoice := recordLoggedRegister?_eq_choice_of_some rate r i last backlog hcopy
      cases hc : (ReferenceFollowerFixedReply.actualChoice r i).configuration with
      | dagger =>
          simp [ReferenceFirstCorrectedCurrentFollowerQueueOverflowCover.followerChoiceRegister?,
            ReferenceFirstCorrectedCurrentFollowerQueueOverflowCover.followerRegisterObserver?, hc]
            at hchoice
      | ordinary state memory =>
          have hfields : state.lastDown = last ∧ state.backlog = backlog := by
            simpa [ReferenceFirstCorrectedCurrentFollowerQueueOverflowCover.followerChoiceRegister?,
              ReferenceFirstCorrectedCurrentFollowerQueueOverflowCover.followerRegisterObserver?, hc]
              using hchoice
          exact ⟨state, memory, M, Or.inr (Or.inl rfl), hfields.1.trans hlast, hq⟩

/-- The value returned by any stored-field seed query is the q field of that
same actual accepted DOWN word. -/
theorem recordSeed?_read_eq_storedWord_q (r : Record) (i : Fin (p.m - 1))
    (field : StoredFollowerField) (q : ℕ)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (M : OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (hconfiguration : match field with
      | .input => r.input.state.followers i = .ordinary state memory
      | .choice =>
          (ReferenceFollowerFixedReply.actualChoice r i).configuration = .ordinary state memory
      | .output => r.output.next.followers i = .ordinary state memory
      | .logged =>
          (ReferenceFollowerFixedReply.actualChoice r i).configuration = .ordinary state memory)
    (hlast : state.lastDown = some M)
    (hread : recordSeed? rate r i field = some q) : M.val.q = q := by
  cases field with
  | input =>
      simp only [recordSeed?, storedDownSeed?, hconfiguration] at hread
      obtain ⟨M0, hM0, hq⟩ := Option.map_eq_some_iff.mp hread
      have hM : M0 = M := Option.some.inj (hM0.symm.trans hlast)
      subst M0
      exact hq
  | choice =>
      simp only [recordSeed?, storedDownSeed?, hconfiguration] at hread
      obtain ⟨M0, hM0, hq⟩ := Option.map_eq_some_iff.mp hread
      have hM : M0 = M := Option.some.inj (hM0.symm.trans hlast)
      subst M0
      exact hq
  | output =>
      have hconfig : (r.output.followers i).configuration = .ordinary state memory :=
        (followerOutput_eq_next rate r i).trans hconfiguration
      simp only [recordSeed?, storedDownSeed?, hconfig] at hread
      obtain ⟨M0, hM0, hq⟩ := Option.map_eq_some_iff.mp hread
      have hM : M0 = M := Option.some.inj (hM0.symm.trans hlast)
      subst M0
      exact hq
  | logged =>
      simp only [recordSeed?] at hread
      obtain ⟨⟨last, backlog⟩, hcopy, hseed⟩ := Option.bind_eq_some_iff.mp hread
      obtain ⟨M0, hM0, hq⟩ := Option.map_eq_some_iff.mp hseed
      have hchoice := recordLoggedRegister?_eq_choice_of_some rate r i last backlog hcopy
      have hfields : state.lastDown = last ∧ state.backlog = backlog := by
        simpa [ReferenceFirstCorrectedCurrentFollowerQueueOverflowCover.followerChoiceRegister?,
          ReferenceFirstCorrectedCurrentFollowerQueueOverflowCover.followerRegisterObserver?,
          hconfiguration] using hchoice
      have hlast0 : last = some M := hfields.1.symm.trans hlast
      have hM0' : some M0 = some M := hM0.symm.trans hlast0
      have hM : M0 = M := Option.some.inj hM0'
      subst M0
      exact hq

/-- A boundary query is limited to its actual INPUT or CHOICE field. -/
def boundarySeed? (r : Record) (i : Fin (p.m - 1)) (choice : Bool) : Option ℕ :=
  if choice then recordSeed? rate r i .choice else recordSeed? rate r i .input

theorem boundarySeed?_physical (r : Record) (i : Fin (p.m - 1)) (choice : Bool)
    (q : ℕ) (hread : boundarySeed? rate r i choice = some q) :
    ∃ state memory M,
      (r.input.state.followers i = .ordinary state memory ∨
        (ReferenceFollowerFixedReply.actualChoice r i).configuration = .ordinary state memory) ∧
      state.lastDown = some M ∧ M.val.q = q := by
  have stored (configuration : DeclaredFollowerLocalRound.LocalConfiguration p rate)
      (h : storedDownSeed? rate configuration = some q) :
      ∃ state memory M, configuration = .ordinary state memory ∧
        state.lastDown = some M ∧ M.val.q = q := by
    cases configuration with
    | dagger => cases h
    | ordinary state memory =>
        obtain ⟨M, hM, hq⟩ := Option.map_eq_some_iff.mp h
        exact ⟨state, memory, M, rfl, hM, hq⟩
  cases choice with
  | false =>
      obtain ⟨state, memory, M, hc, hM, hq⟩ := stored _ hread
      exact ⟨state, memory, M, Or.inl hc, hM, hq⟩
  | true =>
      obtain ⟨state, memory, M, hc, hM, hq⟩ := stored _ hread
      exact ⟨state, memory, M, Or.inr hc, hM, hq⟩

/-! ## Original-index collection observations -/

/-- The actual optional segment's entry is the source record at its boundary. -/
theorem collectionEntry_lookup (R : List Record) (e : ℕ) (seg : Segment)
    (hseg : segmentAt R e = some seg) : R[e]? = some seg.entry := by
  classical
  have hbranch := (segmentAt_branch R e seg hseg).1
  cases hdrop : R.drop e with
  | nil => simp [hdrop, ReferenceCollectionSegmentExtraction.segment] at hbranch
  | cons first rest =>
      have hs : ReferenceCollectionSegmentExtraction.segment (first :: rest) = some seg := by
        simpa only [hdrop] using hbranch
      unfold ReferenceCollectionSegmentExtraction.segment at hs
      cases hc : ReferenceCollectionSegmentExtraction.choice first.input with
      | none => simp [hc] at hs
      | some context =>
          simp only [hc, Option.map_some] at hs
          have hlookup : R[e]? = some first := by
            have h := congrArg (fun records : List Record => records[0]?) hdrop
            simpa only [List.getElem?_drop, Nat.add_zero, List.getElem?_cons_zero] using h
          split at hs <;>
            have hentry : seg.entry = first := by
              have h := congrArg ReferenceCollectionSegmentExtraction.Segment.entry
                (Option.some.inj hs)
              exact h.symm
          all_goals rw [hentry]; exact hlookup

/-- A retained record in the optional segment keeps its original complete-
suffix index. -/
theorem collectionRecord_lookup (R : List Record) (e : ℕ) (seg : Segment)
    (hseg : segmentAt R e = some seg) (j : Fin seg.records.length) :
    R[e + j.val]? = some (seg.records.get j) := by
  have hpart := segmentAt_partition R e seg hseg
  have hindex := congrArg (fun records : List Record => records[j.val]?) hpart
  have hleft : (seg.records ++ seg.remaining)[j.val]? = some (seg.records.get j) := by
    rw [List.getElem?_append_left j.isLt]
    simp [j.isLt]
  rw [hleft, List.getElem?_drop] at hindex
  exact hindex.symm

/-- The first excluded record is the next original source-suffix record. -/
theorem collectionRemainingHead_lookup (R : List Record) (e : ℕ) (seg : Segment)
    (hseg : segmentAt R e = some seg) (r : Record) (hhead : seg.remaining.head? = some r) :
    R[e + seg.records.length]? = some r := by
  have hpart := segmentAt_partition R e seg hseg
  have hindex := congrArg (fun records : List Record => records[seg.records.length]?) hpart
  rw [List.getElem?_append_right (by omega), Nat.sub_self, List.getElem?_drop] at hindex
  simpa only [← List.head?_eq_getElem?, hhead] using hindex.symm

/-! ## Seed source cases -/

/-- A particular stored follower configuration is located at an actual LIVE
input/CHOICE/output site or at its actual first collection entry, retained
record, or first-excluded INPUT/CHOICE boundary. This is a source-indexed
observer witness, not a coverage or queue-truth premise. -/
def localizedFollowerSeedSourceSite (z : X) (i : Fin (p.m - 1))
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p) : Prop :=
  (∃ j : Fin (((sourceRecords rate rewards C_star C_h z).drop
      (birthIndex rate rewards C_star C_h z)).take
      (1 + (liveTail rate rewards C_star C_h z).length)).length,
    let r := (((sourceRecords rate rewards C_star C_h z).drop
      (birthIndex rate rewards C_star C_h z)).take
      (1 + (liveTail rate rewards C_star C_h z).length)).get j
    r.input.state.followers i = .ordinary state memory ∨
      (ReferenceFollowerFixedReply.actualChoice r i).configuration = .ordinary state memory ∨
      r.output.next.followers i = .ordinary state memory) ∨
  (∃ (seg : Segment) (j : Fin (sourceRecords rate rewards C_star C_h z).length),
    segmentAt (sourceRecords rate rewards C_star C_h z)
      (birthIndex rate rewards C_star C_h z + 1 + (liveTail rate rewards C_star C_h z).length) =
        some seg ∧
    birthIndex rate rewards C_star C_h z + 1 + (liveTail rate rewards C_star C_h z).length ≤
      j.val ∧
    j.val ≤ birthIndex rate rewards C_star C_h z + 1 + (liveTail rate rewards C_star C_h z).length +
      seg.records.length ∧
    (let r := (sourceRecords rate rewards C_star C_h z)[j.val]
     r.input.state.followers i = .ordinary state memory ∨
      (ReferenceFollowerFixedReply.actualChoice r i).configuration = .ordinary state memory ∨
      (j.val < birthIndex rate rewards C_star C_h z + 1 +
          (liveTail rate rewards C_star C_h z).length + seg.records.length ∧
        r.output.next.followers i = .ordinary state memory)))

/-- An old stored DOWN seed in an actual first-corrected localized
configuration is the original first-assignment zero seed. The canonical-reply
history is produced internally from the accepted source theorem. -/
theorem oldStoredDown_initialQueue_zero (u t : Fin p.T) (z : X)
    (hz : z ∈ correctedCell rate rewards C_star C_h u t)
    (birth : Record)
    (hb : (sourceRecords rate rewards C_star C_h z)[birthIndex rate rewards C_star C_h z]? =
      some birth)
    (P : Payload) (hborn : ReferenceAssignmentPayloadPersistence.InstallationBirth birth P)
    (i : Fin (p.m - 1)) (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (M : OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (hlast : state.lastDown = some M) (hold : state.lastDown ≠ some (P.downRecord i))
    (hsite : localizedFollowerSeedSourceSite rate rewards C_star C_h z i state memory) :
    M.val.q = 0 := by
  classical
  unfold localizedFollowerSeedSourceSite at hsite
  obtain ⟨_hc, _hspan, _hshort, _hsource, birth0, originalBirth, P', P0,
    hb0, hborn0, _hsigma, _horiginal, _hbornOriginal, _htime, _hP0time,
    _hfirst, _hzeros, hreplies⟩ :=
    ReferenceFirstCorrectedInheritedFollowerCutoffQueue.actual_prior_first_collection_canonical_replies
      rate rewards C_star C_h u t z hz
  have hbirth : birth0 = birth := Option.some.inj (hb0.symm.trans hb)
  subst birth0
  have hP : P' = P := ReferenceAssignmentPayloadChronology.installationBirth_payload_unique
    birth P' P hborn0 hborn
  subst P'
  obtain ⟨_k, _accepted, _reply, _seed, _seedMemory,
    _hlower, _hupper, _hlookup, _haccepted, _hchoice, _hunoccupied, _hdown,
    _hreplySigma, _hS, _hdelta, _hq, hzero, _hreplayS, _hreplayQ, _hreplayDelta,
    _input, _inputMemory, _choice, _hinput, _hu, _hlastInput, _hinputReply,
    _hstart, _hchoiceBirth, _hchoiceU, _hchoiceReply, _hnoDown,
    hlive, _hcutoff, hcollection⟩ := hreplies i
  have hcanonical : state.lastDown = some (P0.downRecord i) := by
    rcases hsite with ⟨j, hj⟩ | ⟨seg, j, hseg, hle, hupper, hj⟩
    · exact (hlive j.val j.isLt state memory hj hold).2.1
    · simp only [Nat.add_assoc] at hseg hle hupper hj
      rcases hcollection with hend | ⟨_he, actual, hactual, _hentry, _hpayload, _hpart, hattribute⟩
      · have hjbound := j.isLt
        change birthIndex rate rewards C_star C_h z +
          (1 + (liveTail rate rewards C_star C_h z).length) =
            (sourceRecords rate rewards C_star C_h z).length at hend
        omega
      · have hsame : actual = seg := Option.some.inj (hactual.symm.trans hseg)
        subst actual
        rcases hj with hi | hc | ⟨hoBound, ho⟩
        · exact (hattribute j hle (by omega) state memory (Or.inl hi) hold).2.1
        · exact (hattribute j hle (by omega) state memory (Or.inr (Or.inl hc)) hold).2.1
        · exact (hattribute j hle (by omega) state memory
            (Or.inr (Or.inr ⟨by omega, ho⟩)) hold).2.1
  have hM : M = P0.downRecord i := Option.some.inj (hlast.symm.trans hcanonical)
  rw [hM]
  exact hzero

/-- A current immutable seed crossing is the already observed installed
payload's original DOWN queue. -/
theorem currentDownSeed_mem_coordinator (u t : Fin p.T) (z : X)
    (hz : z ∈ correctedCell rate rewards C_star C_h u t)
    (birth : Record)
    (hb : (sourceRecords rate rewards C_star C_h z)[birthIndex rate rewards C_star C_h z]? =
      some birth)
    (P : Payload) (hborn : ReferenceAssignmentPayloadPersistence.InstallationBirth birth P)
    (hsigma : P.sigma = t) (i : Fin (p.m - 1))
    (hlarge : ((P.downRecord i).val.q : ℝ) / (rate.n : ℝ) >
      1 / (32 * rate.eta.val)) :
    z ∈ ReferenceFirstCorrectedCoordinatorQueueOverflowCover.coordinatorQueueOverflowEvent
      rate rewards C_star C_h u t := by
  obtain ⟨_L, _c, actualBirth, _hL, _hc, _hprefix, _hlen, _hb, _hs,
    _henabled, hbirth, _hactual, _htime, _hrows, _hselected, _hrewards, hseed, _hnext⟩ :=
    ReferenceFirstCollectionCorrectedCurrentNumericalOutput.firstCell_current_output
      rate rewards C_star C_h u t z hz
  have heq : actualBirth = birth := Option.some.inj (hbirth.symm.trans hb)
  subst actualBirth
  refine ⟨hz, birth, hb, P, hborn, hsigma,
    .birthInstalledPayload (P.assignment.assigned i), (P.downRecord i).val.q, ?_, hlarge⟩
  cases hcoord : birth.output.preparation.coordinator <;> simp only [hcoord] at hseed
  rename_i old ledger clock cutoff outcome
  cases outcome <;> simp only at hseed
  rename_i core consistent started startResult instruction inputInfo output localFrame
    clockData installed selection
  have hP : P = installed.registers.payload := by
    have hborn' := hborn
    simp only [ReferenceAssignmentPayloadPersistence.InstallationBirth, hcoord] at hborn'
    exact hborn'.1
  simp only [ReferenceFirstCorrectedCoordinatorQueueOverflowCover.physicalQueueAt?,
    hb, Option.bind_some, hcoord, ← hP]
  exact congrArg some (P.downRecord_initialQueue i).symm

/-- Any crossing of an actual stored-seed query is the current installed
payload's initial queue. If the observed DOWN word is older, the accepted
canonical-reply history proves its seed is zero, so it cannot cross. -/
theorem recordSeed_crossing_mem_coordinator (u t : Fin p.T) (z : X)
    (hz : z ∈ correctedCell rate rewards C_star C_h u t)
    (birth : Record)
    (hb : (sourceRecords rate rewards C_star C_h z)[birthIndex rate rewards C_star C_h z]? =
      some birth)
    (P : Payload) (hborn : ReferenceAssignmentPayloadPersistence.InstallationBirth birth P)
    (hsigma : P.sigma = t) (i : Fin (p.m - 1))
    (r : Record) (field : StoredFollowerField) (q : ℕ)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (M : OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (hconfiguration : match field with
      | .input => r.input.state.followers i = .ordinary state memory
      | .choice =>
          (ReferenceFollowerFixedReply.actualChoice r i).configuration = .ordinary state memory
      | .output => r.output.next.followers i = .ordinary state memory
      | .logged =>
          (ReferenceFollowerFixedReply.actualChoice r i).configuration = .ordinary state memory)
    (hlast : state.lastDown = some M)
    (hsite : localizedFollowerSeedSourceSite rate rewards C_star C_h z i state memory)
    (hread : recordSeed? rate r i field = some q)
    (hlarge : (q : ℝ) / (rate.n : ℝ) > 1 / (32 * rate.eta.val)) :
    z ∈ ReferenceFirstCorrectedCoordinatorQueueOverflowCover.coordinatorQueueOverflowEvent
      rate rewards C_star C_h u t := by
  have hq := recordSeed?_read_eq_storedWord_q rate r i field q state memory M
    hconfiguration hlast hread
  by_cases hcurrent : state.lastDown = some (P.downRecord i)
  · have hM : M = P.downRecord i := Option.some.inj (hlast.symm.trans hcurrent)
    have hlargeM : (M.val.q : ℝ) / (rate.n : ℝ) > 1 / (32 * rate.eta.val) := by
      rw [hq]
      exact hlarge
    have hlargeP : ((P.downRecord i).val.q : ℝ) / (rate.n : ℝ) >
        1 / (32 * rate.eta.val) := by
      simpa only [hM] using hlargeM
    exact currentDownSeed_mem_coordinator rate rewards C_star C_h u t z hz birth hb P
      hborn hsigma i hlargeP
  · have hzero := oldStoredDown_initialQueue_zero rate rewards C_star C_h u t z hz
      birth hb P hborn i state memory M hlast hcurrent hsite
    have hqzero : q = 0 := hq.symm.trans hzero
    have hpositive : 0 < 1 / (32 * rate.eta.val) :=
      one_div_pos.mpr (mul_pos (by norm_num) rate.eta.property)
    rw [hqzero, Nat.cast_zero, zero_div] at hlarge
    exact False.elim ((not_lt_of_ge (le_of_lt hpositive)) hlarge)

/-- INPUT/CHOICE boundary-seed crossings use the same current/old attribution;
the Boolean selects only the literal pre-output field. -/
theorem boundarySeed_crossing_mem_coordinator (u t : Fin p.T) (z : X)
    (hz : z ∈ correctedCell rate rewards C_star C_h u t)
    (birth : Record)
    (hb : (sourceRecords rate rewards C_star C_h z)[birthIndex rate rewards C_star C_h z]? =
      some birth)
    (P : Payload) (hborn : ReferenceAssignmentPayloadPersistence.InstallationBirth birth P)
    (hsigma : P.sigma = t) (i : Fin (p.m - 1))
    (r : Record) (choice : Bool) (q : ℕ)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (M : OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (hconfiguration : if choice then
      (ReferenceFollowerFixedReply.actualChoice r i).configuration = .ordinary state memory
      else r.input.state.followers i = .ordinary state memory)
    (hlast : state.lastDown = some M)
    (hsite : localizedFollowerSeedSourceSite rate rewards C_star C_h z i state memory)
    (hread : boundarySeed? rate r i choice = some q)
    (hlarge : (q : ℝ) / (rate.n : ℝ) > 1 / (32 * rate.eta.val)) :
    z ∈ ReferenceFirstCorrectedCoordinatorQueueOverflowCover.coordinatorQueueOverflowEvent
      rate rewards C_star C_h u t := by
  cases choice with
  | false =>
      exact recordSeed_crossing_mem_coordinator rate rewards C_star C_h u t z hz birth hb P hborn
        hsigma i r .input q state memory M hconfiguration hlast hsite
        (by simpa [boundarySeed?] using hread) hlarge
  | true =>
      exact recordSeed_crossing_mem_coordinator rate rewards C_star C_h u t z hz birth hb P hborn
        hsigma i r .choice q state memory M hconfiguration hlast hsite
        (by simpa [boundarySeed?] using hread) hlarge

/-! ## Reached service before output validation -/

/-- The occupied service candidate after its actual input guards, before any
follower output validation. Failed candidates on arbitrary local inputs are
retained by this query. -/
def reachedFollowerService? (r : Record) (i : Fin (p.m - 1)) : Register := by
  classical
  exact match (ReferenceFollowerFixedReply.actualChoice r i).configuration with
  | .dagger => none
  | .ordinary state _ =>
      if ActiveFollowerQueueOperation.stateInputDomain state ∧
          state.status ≠ .unoccupied ∧
          (ReferenceFollowerFixedReply.actualChoice r i).activation.val ≤ r.input.time.val + 1 then
        state.lastDown.bind fun M =>
          if ActiveFollowerQueueOperation.thinningProbabilityDomain rate.eta M then
            some (some M, CappedService.residual (4 * rate.n) state.backlog
              (ActiveFollowerQueueOperation.rawArrival rate.eta i r.input.row r.input.time M
                ((ReferenceActivePhysicalStep.prepare r.input).feedback.observations
                  (PublicDiscreteDraws.followerPlayer p.two_le_m i))))
          else none
      else none

/-- The reached candidate refines the accepted service observer when the
actual record's follower has no local failure. -/
theorem reachedFollowerService?_eq_accepted_of_some (r : Record) (i : Fin (p.m - 1))
    (hf : (r.output.followers i).failure = none)
    (last : Option (OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))) (q : ℕ)
    (hread : reachedFollowerService? rate r i = some (last, q)) :
    ReferenceFirstCorrectedCurrentFollowerQueueOverflowCover.actualOccupiedServiceResidual?
      (rate := rate) (some r) i = some (last, q) := by
  classical
  unfold reachedFollowerService? at hread
  cases hc : (ReferenceFollowerFixedReply.actualChoice r i).configuration with
  | dagger => simp only [hc, reduceCtorEq] at hread
  | ordinary state memory =>
      simp only [hc] at hread
      split at hread
      next hguards =>
        obtain ⟨M, hlast, hread⟩ := Option.bind_eq_some_iff.mp hread
        split at hread
        next _hthin =>
          unfold ReferenceFirstCorrectedCurrentFollowerQueueOverflowCover.actualOccupiedServiceResidual?
          simp only [Option.bind_some, hc]
          rw [dite_eq_right hguards.2.1, hlast]
          simp only [ite_eq_left hf]
          exact hread
        next => cases hread
      next => cases hread

/-- Every existing source record has the actual ordinary no-failure output,
proved from complete-suffix preservation. -/
theorem sourceRecord_follower_noFailure (z : X) (r : Record)
    (hr : r ∈ sourceRecords rate rewards C_star C_h z) (i : Fin (p.m - 1)) :
    (r.output.followers i).failure = none := by
  obtain ⟨k, hk, hget⟩ := List.mem_iff_getElem.mp hr
  obtain ⟨_s, _m, _c, _n, _nm, _hi, _hc, _hd, _hnd, _ho, hf, _hn⟩ :=
    ReferenceCompleteSuffixFollowerPreservation.complete_suffix_follower_output
      (rate := rate) rewards C_star C_h z ⟨k, hk⟩ i
  change (((sourceRecords rate rewards C_star C_h z)[k]).output.followers i).failure = none at hf
  rw [hget] at hf
  exact hf

/-- Source-record wrapper: later consumers need not assume no failure. -/
theorem reachedFollowerService?_eq_accepted_of_source (z : X) (r : Record)
    (hr : r ∈ sourceRecords rate rewards C_star C_h z) (i : Fin (p.m - 1))
    (last : Option (OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))) (q : ℕ)
    (hread : reachedFollowerService? rate r i = some (last, q)) :
    ReferenceFirstCorrectedCurrentFollowerQueueOverflowCover.actualOccupiedServiceResidual?
      (rate := rate) (some r) i = some (last, q) :=
  reachedFollowerService?_eq_accepted_of_some rate r i
    (sourceRecord_follower_noFailure rate rewards C_star C_h z r hr i) last q hread

/-- Live observer refinement: ordinary fields use the accepted register
observer, while reached service is refined using an explicit local output
failure premise. -/
def observeLiteralLiveFollower (V : List Record) (i : Fin (p.m - 1)) :
    LiveFollowerRegisterSite (rate := rate) V → Register
  | .serviceResidual j => reachedFollowerService? rate (V.get j) i
  | site => observeLiveFollowerRegister (rate := rate) V i site

/-- Collection service is observed before output validation. The accepted
site family intentionally leaves OUTPUT and service unavailable on the first
excluded record. -/
def observeLiteralCollectionFollower (R : List Record) (e : ℕ) (i : Fin (p.m - 1))
    (site : CollectionFollowerRegisterSiteOf rate R e) : Register :=
  match site.site with
  | .serviceResidual j => reachedFollowerService? rate (site.segment.records.get j) i
  | _ => observeCollectionFollowerRegister? (rate := rate) R e i site

/-! ## Actual source membership and event attribution -/

private theorem mem_of_getElem?_eq_some {α : Type} (R : List α) (j : ℕ) (r : α)
    (h : R[j]? = some r) : r ∈ R := by
  obtain ⟨hj, hget⟩ := List.getElem?_eq_some_iff.mp h
  exact List.mem_iff_getElem.mpr ⟨j, hj, hget⟩

/-- Every record in the actual birth-plus-LIVE slice is an original source
record at its retained source index. -/
theorem liveSlice_get_mem_source (z : X)
    (j : Fin (((sourceRecords rate rewards C_star C_h z).drop
      (birthIndex rate rewards C_star C_h z)).take
        (1 + (liveTail rate rewards C_star C_h z).length)).length) :
    (((sourceRecords rate rewards C_star C_h z).drop
      (birthIndex rate rewards C_star C_h z)).take
        (1 + (liveTail rate rewards C_star C_h z).length)).get j ∈
      sourceRecords rate rewards C_star C_h z := by
  apply List.mem_of_mem_drop
  exact List.mem_of_mem_take (List.get_mem _ j)

/-- A collection copy site names exactly the locations whose follower
register is in the accepted collection carrier. Its first-excluded variant
has no OUTPUT or service site. -/
inductive CollectionFollowerCopySite (R : List Record) (e : ℕ) where
  | entry (seg : Segment) (available : segmentAt R e = some seg)
  | retained (seg : Segment) (available : segmentAt R e = some seg)
      (j : Fin seg.records.length)
  | firstExcluded (seg : Segment) (available : segmentAt R e = some seg)
      (r : Record) (head : seg.remaining.head? = some r)

/-- The actual record selected by a collection copy site. -/
def CollectionFollowerCopySite.record {R : List Record} {e : ℕ}
    (site : CollectionFollowerCopySite rate R e) : Record :=
  match site with
  | .entry seg _ => seg.entry
  | .retained seg _ j => seg.records.get j
  | .firstExcluded _ _ r _ => r

/-- The accepted CHOICE site corresponding to a collection copied-register
query. This maps entry and first-excluded records to CHOICE only. -/
def CollectionFollowerCopySite.acceptedSite {R : List Record} {e : ℕ}
    (site : CollectionFollowerCopySite rate R e) :
      CollectionFollowerRegisterSiteOf rate R e :=
  match site with
  | .entry seg available => ⟨seg, available, .cutoffChoice⟩
  | .retained seg available j => ⟨seg, available, .recordChoice j⟩
  | .firstExcluded seg available r head => ⟨seg, available, .remainingChoice r head⟩

/-- The corresponding accepted observer reads the actual CHOICE register of
the record selected by a collection copy site. -/
theorem collectionCopySite_observer_eq_choice {R : List Record} {e : ℕ}
    (site : CollectionFollowerCopySite rate R e) (i : Fin (p.m - 1)) :
    observeCollectionFollowerRegister? (rate := rate) R e i site.acceptedSite =
      ReferenceFirstCorrectedCurrentFollowerQueueOverflowCover.followerChoiceRegister?
        (rate := rate) (some site.record) i := by
  cases site with
  | entry seg available => rfl
  | retained seg available j => rfl
  | firstExcluded seg available r head => rfl


/-- Every collection logged-register crossing is attributed at the same actual
segment and source boundary. The site family includes entry and first-excluded
CHOICE reads, and keeps OUTPUT/service restricted to retained records. -/
theorem collectionLoggedRegister_crossing_mem_followerRegisterOverflowEventAt
    (u t : Fin p.T) (z : X)
    (hz : z ∈ correctedCell rate rewards C_star C_h u t)
    (i : Fin (p.m - 1))
    (site : CollectionFollowerCopySite rate
      (sourceRecords rate rewards C_star C_h z)
      (birthIndex rate rewards C_star C_h z + 1 +
        (liveTail rate rewards C_star C_h z).length))
    (last : Option (OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))) (q : ℕ)
    (hread : recordLoggedRegister? rate site.record i = some (last, q))
    (hlarge : (q : ℝ) / (rate.n : ℝ) > 1 / (32 * rate.eta.val)) :
    z ∈ ReferenceFirstCorrectedFollowerRegisterOverflowCover.followerRegisterOverflowEventAt
      (rate := rate) rewards C_star C_h u t := by
  have hchoice := recordLoggedRegister?_eq_choice_of_some rate site.record i last q hread
  have hobs : observeCollectionFollowerRegister? (rate := rate)
      (sourceRecords rate rewards C_star C_h z)
      (birthIndex rate rewards C_star C_h z + 1 +
        (liveTail rate rewards C_star C_h z).length) i site.acceptedSite = some (last, q) := by
    rw [collectionCopySite_observer_eq_choice]
    exact hchoice
  exact ⟨hz, Or.inr ⟨i, site.acceptedSite, last, q, hobs, hlarge⟩⟩

/-- Every checked UP-offer crossing at the collection entry, a retained
record, or the first excluded INPUT/CHOICE boundary is attributed to that
record's actual CHOICE register. -/
theorem collectionOfferedQueue_crossing_mem_followerRegisterOverflowEventAt
    (u t : Fin p.T) (z : X)
    (hz : z ∈ correctedCell rate rewards C_star C_h u t)
    (i : Fin (p.m - 1))
    (site : CollectionFollowerCopySite rate
      (sourceRecords rate rewards C_star C_h z)
      (birthIndex rate rewards C_star C_h z + 1 +
        (liveTail rate rewards C_star C_h z).length))
    (q : ℕ)
    (hread : recordOfferedQueue? rate site.record i = some q)
    (hlarge : (q : ℝ) / (rate.n : ℝ) > 1 / (32 * rate.eta.val)) :
    z ∈ ReferenceFirstCorrectedFollowerRegisterOverflowCover.followerRegisterOverflowEventAt
      (rate := rate) rewards C_star C_h u t := by
  obtain ⟨last, hchoice⟩ := recordOfferedQueue?_eq_choice_of_some rate site.record i q hread
  have hobs : observeCollectionFollowerRegister? (rate := rate)
      (sourceRecords rate rewards C_star C_h z)
      (birthIndex rate rewards C_star C_h z + 1 +
        (liveTail rate rewards C_star C_h z).length) i site.acceptedSite = some (last, q) := by
    rw [collectionCopySite_observer_eq_choice]
    exact hchoice
  exact ⟨hz, Or.inr ⟨i, site.acceptedSite, last, q, hobs, hlarge⟩⟩

/-- A live literal observer read refines its accepted site observer. The
service case discharges its local failure premise from actual source
membership. -/
theorem observeLiteralLiveFollower_refines_source (z : X) (i : Fin (p.m - 1))
    (V : List Record) (site : LiveFollowerRegisterSite (rate := rate) V)
    (last : Option (OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))) (q : ℕ)
    (hsource : ∀ j : Fin V.length, V.get j ∈ sourceRecords rate rewards C_star C_h z)
    (hread : observeLiteralLiveFollower rate V i site = some (last, q)) :
    observeLiveFollowerRegister (rate := rate) V i site = some (last, q) := by
  cases site with
  | input j => exact hread
  | choice j => exact hread
  | output j => exact hread
  | serviceResidual j =>
      exact reachedFollowerService?_eq_accepted_of_source rate rewards C_star C_h z (V.get j)
        (hsource j) i last q hread

/-- The collection site query's service branch refines the accepted guarded
service observer using its actual retained-record index. Other branches are
the accepted INPUT/CHOICE/OUTPUT projections themselves. -/
theorem observeLiteralCollectionFollower_refines_source (z : X) (i : Fin (p.m - 1))
    (site : CollectionFollowerRegisterSiteOf rate
      (sourceRecords rate rewards C_star C_h z)
      (birthIndex rate rewards C_star C_h z + 1 +
        (liveTail rate rewards C_star C_h z).length))
    (last : Option (OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))) (q : ℕ)
    (hread : observeLiteralCollectionFollower rate
      (sourceRecords rate rewards C_star C_h z)
      (birthIndex rate rewards C_star C_h z + 1 +
        (liveTail rate rewards C_star C_h z).length) i site = some (last, q)) :
    observeCollectionFollowerRegister? (rate := rate)
      (sourceRecords rate rewards C_star C_h z)
      (birthIndex rate rewards C_star C_h z + 1 +
        (liveTail rate rewards C_star C_h z).length) i site = some (last, q) := by
  rcases site with ⟨seg, hseg, selected⟩
  cases selected with
  | cutoffInput => exact hread
  | cutoffChoice => exact hread
  | recordInput j => exact hread
  | recordChoice j => exact hread
  | recordOutput j => exact hread
  | serviceResidual j =>
      have hlookup := collectionRecord_lookup rate
        (sourceRecords rate rewards C_star C_h z)
        (birthIndex rate rewards C_star C_h z + 1 +
          (liveTail rate rewards C_star C_h z).length)
        seg hseg j
      have hsource := mem_of_getElem?_eq_some _ _ _ hlookup
      exact reachedFollowerService?_eq_accepted_of_source rate rewards C_star C_h z
        (seg.records.get j)
        hsource i last q hread
  | remainingInput r hhead => exact hread
  | remainingChoice r hhead => exact hread

/-- A query at any actual LIVE site, including the pre-output service query,
crosses only if the accepted follower-register event crosses at the same site. -/
theorem liveLiteralSite_crossing_mem_followerRegisterOverflowEventAt
    (u t : Fin p.T) (z : X)
    (hz : z ∈ correctedCell rate rewards C_star C_h u t)
    (i : Fin (p.m - 1))
    (site : LiveFollowerRegisterSite (rate := rate)
      (((sourceRecords rate rewards C_star C_h z).drop
        (birthIndex rate rewards C_star C_h z)).take
          (1 + (liveTail rate rewards C_star C_h z).length)))
    (last : Option (OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))) (q : ℕ)
    (hread : observeLiteralLiveFollower rate
      (((sourceRecords rate rewards C_star C_h z).drop
        (birthIndex rate rewards C_star C_h z)).take
          (1 + (liveTail rate rewards C_star C_h z).length)) i site = some (last, q))
    (hlarge : (q : ℝ) / (rate.n : ℝ) > 1 / (32 * rate.eta.val)) :
    z ∈ ReferenceFirstCorrectedFollowerRegisterOverflowCover.followerRegisterOverflowEventAt
      (rate := rate) rewards C_star C_h u t := by
  let V := ((sourceRecords rate rewards C_star C_h z).drop
      (birthIndex rate rewards C_star C_h z)).take
        (1 + (liveTail rate rewards C_star C_h z).length)
  have hsource : ∀ k : Fin V.length, V.get k ∈ sourceRecords rate rewards C_star C_h z := by
    intro k
    exact liveSlice_get_mem_source rate rewards C_star C_h z k
  have hobs := observeLiteralLiveFollower_refines_source rate rewards C_star C_h z i V
    site last q hsource hread
  exact ⟨hz, Or.inl ⟨i, site, last, q, hobs, hlarge⟩⟩

/-- Every logged or offered LIVE crossing is attributed to the accepted
follower-register event at the same original source cell and threshold. The
source membership premise is the actual slice lookup, not a coverage claim. -/
theorem liveLoggedRegister_crossing_mem_followerRegisterOverflowEventAt
    (u t : Fin p.T) (z : X)
    (hz : z ∈ correctedCell rate rewards C_star C_h u t)
    (i : Fin (p.m - 1))
    (V : List Record)
    (hV : V = ((sourceRecords rate rewards C_star C_h z).drop
      (birthIndex rate rewards C_star C_h z)).take
        (1 + (liveTail rate rewards C_star C_h z).length))
    (j : Fin V.length)
    (last : Option (OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))) (q : ℕ)
    (hread : recordLoggedRegister? rate (V.get j) i = some (last, q))
    (hlarge : (q : ℝ) / (rate.n : ℝ) > 1 / (32 * rate.eta.val)) :
    z ∈ ReferenceFirstCorrectedFollowerRegisterOverflowCover.followerRegisterOverflowEventAt
      (rate := rate) rewards C_star C_h u t := by
  subst V
  let V := ((sourceRecords rate rewards C_star C_h z).drop
      (birthIndex rate rewards C_star C_h z)).take
        (1 + (liveTail rate rewards C_star C_h z).length)
  have hsource : ∀ k : Fin V.length, V.get k ∈ sourceRecords rate rewards C_star C_h z := by
    intro k
    exact liveSlice_get_mem_source rate rewards C_star C_h z k
  have hchoice := recordLoggedRegister?_eq_choice_of_some rate (V.get j) i last q hread
  have hliteral : observeLiteralLiveFollower rate V i
      (.choice j) = some (last, q) := by
    simpa [observeLiteralLiveFollower, observeLiveFollowerRegister,
      ReferenceFirstCorrectedCurrentFollowerQueueOverflowCover.followerChoiceRegister?]
      using hchoice
  have hobs := observeLiteralLiveFollower_refines_source rate rewards C_star C_h z i V (.choice j)
    last q hsource hliteral
  exact ⟨hz, Or.inl ⟨i, .choice j, last, q, hobs, hlarge⟩⟩

/-- Every offered-UP LIVE crossing is attributed to the actual CHOICE site,
retaining its last accepted DOWN word. -/
theorem liveOfferedQueue_crossing_mem_followerRegisterOverflowEventAt
    (u t : Fin p.T) (z : X)
    (hz : z ∈ correctedCell rate rewards C_star C_h u t)
    (i : Fin (p.m - 1))
    (V : List Record)
    (hV : V = ((sourceRecords rate rewards C_star C_h z).drop
      (birthIndex rate rewards C_star C_h z)).take
        (1 + (liveTail rate rewards C_star C_h z).length))
    (j : Fin V.length)
    (q : ℕ)
    (hread : recordOfferedQueue? rate (V.get j) i = some q)
    (hlarge : (q : ℝ) / (rate.n : ℝ) > 1 / (32 * rate.eta.val)) :
    z ∈ ReferenceFirstCorrectedFollowerRegisterOverflowCover.followerRegisterOverflowEventAt
      (rate := rate) rewards C_star C_h u t := by
  subst V
  let V := ((sourceRecords rate rewards C_star C_h z).drop
      (birthIndex rate rewards C_star C_h z)).take
        (1 + (liveTail rate rewards C_star C_h z).length)
  have hsource : ∀ k : Fin V.length, V.get k ∈ sourceRecords rate rewards C_star C_h z := by
    intro k
    exact liveSlice_get_mem_source rate rewards C_star C_h z k
  obtain ⟨last, hchoice⟩ := recordOfferedQueue?_eq_choice_of_some
    rate (V.get j) i q hread
  have hliteral : observeLiteralLiveFollower rate V i (.choice j) = some (last, q) := by
    simpa [observeLiteralLiveFollower, observeLiveFollowerRegister,
      ReferenceFirstCorrectedCurrentFollowerQueueOverflowCover.followerChoiceRegister?]
      using hchoice
  have hobs := observeLiteralLiveFollower_refines_source rate rewards C_star C_h z i V (.choice j)
    last q hsource hliteral
  exact ⟨hz, Or.inl ⟨i, .choice j, last, q, hobs, hlarge⟩⟩

/-- The same literal collection observer attributes a reached retained-service
crossing to the accepted collection service site. The first excluded record
cannot be passed here because it has no OUTPUT or service constructor. -/
theorem collectionLiteralSite_crossing_mem_followerRegisterOverflowEventAt
    (u t : Fin p.T) (z : X)
    (hz : z ∈ correctedCell rate rewards C_star C_h u t)
    (i : Fin (p.m - 1))
    (site : CollectionFollowerRegisterSiteOf rate
      (sourceRecords rate rewards C_star C_h z)
      (birthIndex rate rewards C_star C_h z + 1 +
        (liveTail rate rewards C_star C_h z).length))
    (last : Option (OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))) (q : ℕ)
    (hread : observeLiteralCollectionFollower rate
      (sourceRecords rate rewards C_star C_h z)
      (birthIndex rate rewards C_star C_h z + 1 +
        (liveTail rate rewards C_star C_h z).length) i site = some (last, q))
    (hlarge : (q : ℝ) / (rate.n : ℝ) > 1 / (32 * rate.eta.val)) :
    z ∈ ReferenceFirstCorrectedFollowerRegisterOverflowCover.followerRegisterOverflowEventAt
      (rate := rate) rewards C_star C_h u t := by
  have hobs := observeLiteralCollectionFollower_refines_source rate rewards C_star C_h z
    i site last q hread
  exact ⟨hz, Or.inr ⟨i, site, last, q, hobs, hlarge⟩⟩

end Bandits.Support.ReferenceFirstCorrectedFollowerQueueCopyRefinement
