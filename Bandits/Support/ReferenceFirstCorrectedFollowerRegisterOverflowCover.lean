/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCorrectedCurrentFollowerQueueOverflowCover
public import Bandits.Support.ReferenceFirstCorrectedInheritedQueueOverflowCover
public import Bandits.Support.ReferenceFirstCorrectedCollectionBoundaryExclusion

import Mathlib.Tactic

/-!
# First corrected physical follower-register overflow partition

The event in this module reads the original follower configurations and the
actual occupied-service residual. It uses the accepted current and inherited
queue covers to attribute every observed overflow. It is only the follower
register component of the later physical-site partition.

Sources: `appendix_a_local_protocol.tex:28-64`,
`06_interruptions.tex:192-233,246-299,391-408,425-426`,
`04_slow_fast_learner.tex:157-187,256-290`, and
`08_main_theorem.tex:111-128` under `sources/zip4/manuscript/`.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions
open scoped Classical

namespace Bandits.Support.ReferenceFirstCorrectedFollowerRegisterOverflowCover

variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)

local notation "X" => BootstrapPrivateRoundStreams.SourceInput p
local notation "Record" => ReferenceActivePhysicalHorizon.RoundRecord
  (p := p) (rate := rate)
local notation "Register" => Option (Option (OrdinaryMessageCodec.DownRecord
  (ReferencePrelaunchFollower.codecParams p rate.eta)) × ℕ)

/-- Collection query sites keep the actual segment list index. The excluded
boundary has INPUT and CHOICE only; its OUTPUT belongs to the next assignment.
Occupied service is a separate site and is observed by the actual guarded
service query. -/
inductive CollectionFollowerRegisterSite
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (seg : ReferenceCollectionSegmentExtraction.Segment rate) where
  | cutoffInput
  | cutoffChoice
  | recordInput (j : Fin seg.records.length)
  | recordChoice (j : Fin seg.records.length)
  | recordOutput (j : Fin seg.records.length)
  | serviceResidual (j : Fin seg.records.length)
  | remainingInput
      (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
      (h : seg.remaining.head? = some r)
  | remainingChoice
      (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
      (h : seg.remaining.head? = some r)

/-- If the actual optional segment query is absent, there is no collection
site. This keeps segment success inside the observer rather than as a root
premise of the event. -/
structure CollectionFollowerRegisterSiteOf
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (R : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (e : ℕ) where
  segment : ReferenceCollectionSegmentExtraction.Segment rate
  available : ReferenceCollectionSegmentExtraction.segmentAt R e = some segment
  site : CollectionFollowerRegisterSite rate segment

/-- Read a collection site only from the actual optional segment extraction.
All configurations are the original record projections; no fallback record
or queue is supplied. -/
def observeCollectionFollowerRegister?
    (R : List Record) (e : ℕ) (i : Fin (p.m - 1))
    (site : CollectionFollowerRegisterSiteOf rate R e) : Register := by
  classical
  cases site with
  | mk seg _havailable site =>
      cases site with
      | cutoffInput =>
          exact ReferenceFirstCorrectedCurrentFollowerQueueOverflowCover.followerInputRegister?
            (rate := rate) (some seg.entry) i
      | cutoffChoice =>
          exact ReferenceFirstCorrectedCurrentFollowerQueueOverflowCover.followerChoiceRegister?
            (rate := rate) (some seg.entry) i
      | recordInput j =>
          exact ReferenceFirstCorrectedCurrentFollowerQueueOverflowCover.followerInputRegister?
            (rate := rate) (some (seg.records.get j)) i
      | recordChoice j =>
          exact ReferenceFirstCorrectedCurrentFollowerQueueOverflowCover.followerChoiceRegister?
            (rate := rate) (some (seg.records.get j)) i
      | recordOutput j =>
          exact ReferenceFirstCorrectedCurrentFollowerQueueOverflowCover.followerOutputRegister?
            (rate := rate) (some (seg.records.get j)) i
      | serviceResidual j =>
          exact ReferenceFirstCorrectedCurrentFollowerQueueOverflowCover.actualOccupiedServiceResidual?
            (rate := rate) (some (seg.records.get j)) i
      | remainingInput r _ =>
          exact ReferenceFirstCorrectedCurrentFollowerQueueOverflowCover.followerInputRegister?
            (rate := rate) (some r) i
      | remainingChoice r _ =>
          exact ReferenceFirstCorrectedCurrentFollowerQueueOverflowCover.followerChoiceRegister?
            (rate := rate) (some r) i

/-- A literal observer event on the actual birth-plus-LIVE V and the actual
optional first collection segment. Each observed register retains its real
DOWN option and natural backlog, so `none`, inherited words, and the current
word remain in the carrier. Occupied residuals use the actual checked
service operation and its failure guard. -/
def followerRegisterOverflowEventAt
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T) : Set X := by
  classical
  exact {z | z ∈ ReferenceFirstCollectionCorrectedSliceNumericalPrefix.correctedCell
      rate rewards C_star C_h u t ∧
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let b := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.birthIndex
      rate rewards C_star C_h z
    let W := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.liveTail
      rate rewards C_star C_h z
    let V := (R.drop b).take (1 + W.length)
    let e := b + 1 + W.length
    ((∃ (i : Fin (p.m - 1)) (site : ReferenceFirstCorrectedCurrentFollowerQueueOverflowCover.LiveFollowerRegisterSite
          (rate := rate) V) (last : Option (OrdinaryMessageCodec.DownRecord
          (ReferencePrelaunchFollower.codecParams p rate.eta))) (q : ℕ),
        ReferenceFirstCorrectedCurrentFollowerQueueOverflowCover.observeLiveFollowerRegister
          (rate := rate) V i site = some (last, q) ∧
          (q : ℝ) / (rate.n : ℝ) > 1 / (32 * rate.eta.val)) ∨
      (∃ (i : Fin (p.m - 1))
        (site : CollectionFollowerRegisterSiteOf rate R e)
        (last : Option (OrdinaryMessageCodec.DownRecord
          (ReferencePrelaunchFollower.codecParams p rate.eta))) (q : ℕ),
        observeCollectionFollowerRegister? (rate := rate) R e i site = some (last, q) ∧
          (q : ℝ) / (rate.n : ℝ) > 1 / (32 * rate.eta.val)))}

/-- The union of the actual physical follower-register observations over all
corrected source cells. -/
def followerRegisterOverflowEvent
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) : Set X :=
  ⋃ u : Fin p.T, ⋃ t : Fin p.T,
    followerRegisterOverflowEventAt (rate := rate) rewards C_star C_h u t

/-- The LIVE projection of the literal follower-register event. The full event
also includes the first actual collection segment and its excluded input / choice. -/
def liveFollowerRegisterOverflowEventAt
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T) : Set X := by
  classical
  exact {z | z ∈ ReferenceFirstCollectionCorrectedSliceNumericalPrefix.correctedCell
      rate rewards C_star C_h u t ∧
    ∃ (i : Fin (p.m - 1))
      (site : ReferenceFirstCorrectedCurrentFollowerQueueOverflowCover.LiveFollowerRegisterSite
        (rate := rate)
        (List.take (1 + (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.liveTail
          rate rewards C_star C_h z).length)
          ((ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).drop
            (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.birthIndex
              rate rewards C_star C_h z))))
      (last : Option (OrdinaryMessageCodec.DownRecord
        (ReferencePrelaunchFollower.codecParams p rate.eta))) (q : ℕ),
      ReferenceFirstCorrectedCurrentFollowerQueueOverflowCover.observeLiveFollowerRegister
        (rate := rate)
        (List.take (1 + (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.liveTail
          rate rewards C_star C_h z).length)
          ((ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).drop
            (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.birthIndex
              rate rewards C_star C_h z))) i site = some (last, q) ∧
      (q : ℝ) / (rate.n : ℝ) > 1 / (32 * rate.eta.val)}

/-- Union of the source-cell LIVE observations; the collection suffix remains
inside the full literal event and is handled separately. -/
def liveFollowerRegisterOverflowEvent
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) : Set X :=
  ⋃ u : Fin p.T, ⋃ t : Fin p.T,
    liveFollowerRegisterOverflowEventAt (rate := rate) rewards C_star C_h u t

/-- A reached occupied service residual is the backlog of the actual ordinary
OUTPUT, with the actual failure guard discharged by the observer itself. -/
theorem occupiedServiceResidual_output
    (r : Record) (i : Fin (p.m - 1))
    (M : OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta)) (q : ℕ)
    (hread : ReferenceFirstCorrectedCurrentFollowerQueueOverflowCover.actualOccupiedServiceResidual?
      (rate := rate) (some r) i = some (some M, q)) :
    ∃ next nextMemory,
      (r.output.followers i).configuration = .ordinary next nextMemory ∧
      (r.output.followers i).failure = none ∧ next.backlog = q :=
  ReferenceFirstCorrectedCurrentFollowerQueueOverflowCover.actualOccupiedServiceResidual_is_output
    rate r i M q hread

private theorem occupiedServiceObserver_available
    (r : Record) (i : Fin (p.m - 1))
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (next : ReferencePrelaunchFollower.State p rate.eta)
    (nextMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hchoice : (ReferenceFollowerFixedReply.actualChoice r i).configuration =
      .ordinary state memory)
    (houtput : (r.output.followers i).configuration = .ordinary next nextMemory)
    (hoccupied : state.status ≠ .unoccupied)
    (hfailure : (r.output.followers i).failure = none) :
    ∃ M q, ReferenceFirstCorrectedCurrentFollowerQueueOverflowCover.actualOccupiedServiceResidual?
      (rate := rate) (some r) i = some (some M, q) := by
  classical
  let follower := r.output.preparation.followers.followers i
  let observation := r.output.preparation.feedback.observations
    (PublicDiscreteDraws.followerPlayer p.two_le_m i)
  have hprepared : r.output.preparation = ReferenceActivePhysicalStep.prepare r.input := by
    rw [r.output_eq]
    rfl
  have hstate : follower.configuration = .ordinary state memory := by
    simpa only [ReferenceFollowerFixedReply.actualChoice, follower] using hchoice
  have hfinish : r.output.followers i =
      ReferenceActivePhysicalStep.finishFollower
        r.output.preparation.coordinator.downView follower observation := by
    calc
      r.output.followers i = (ReferenceActivePhysicalStep.step r.input).followers i := by
        rw [r.output_eq]
      _ = ReferenceActivePhysicalStep.finishFollower
          (ReferenceActivePhysicalStep.prepare r.input).coordinator.downView
          ((ReferenceActivePhysicalStep.prepare r.input).followers.followers i)
          ((ReferenceActivePhysicalStep.prepare r.input).feedback.observations
            (PublicDiscreteDraws.followerPlayer p.two_le_m i)) := by
              simp only [ReferenceActivePhysicalStep.step,
                ReferenceActivePhysicalStep.PreparedRound.observeFollower]
      _ = ReferenceActivePhysicalStep.finishFollower
          r.output.preparation.coordinator.downView follower observation := by
            rw [← hprepared]
  have hfinishConfig :
      (ReferenceActivePhysicalStep.finishFollower
        r.output.preparation.coordinator.downView follower observation).configuration =
          .ordinary next nextMemory := by
    rw [← hfinish]
    exact houtput
  obtain ⟨choice, choiceMemory, post, hconfig, hrecord, _hrelease, _hdownInput,
      _hdown⟩ := ReferenceFollowerReplyChronology.finishFollower_ordinary_inversion
        r.output.preparation.coordinator.downView follower observation
        next nextMemory hfinishConfig
  have hchoicePair := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
    (hconfig.symm.trans hstate)
  have hchoiceState : choice = state := hchoicePair.1
  have hchoiceMemory : choiceMemory = memory := hchoicePair.2
  subst choice
  subst choiceMemory
  let recorded := ReferenceActivePhysicalStep.recordFollower
    r.output.preparation.coordinator.downView follower.follower follower.row
    follower.activation follower.time follower.active follower.arm observation state
  have hrecorded : recorded.result =
      DeclaredFollowerLocalRound.recordOrServiceThenDown rate follower.follower
        follower.row follower.activation follower.time follower.active follower.arm
        observation state := by
    simp [recorded, ReferenceActivePhysicalStep.recordFollower, hoccupied]
  have hrecordOk : recorded.result = .ok post := by
    simpa only [recorded, ReferenceActivePhysicalStep.recordFollower] using hrecord
  have hchecked : ∃ result,
      ActiveFollowerQueueOperation.checkedService rate.eta rate.sourceCap rate.n
        rate.n_scale follower.follower follower.row follower.activation follower.time
        observation state = .success result := by
    rw [hrecorded,
      DeclaredFollowerLocalRound.recordOrServiceThenDown_occupied rate follower.follower
        follower.row follower.activation follower.time follower.active follower.arm
        observation state hoccupied] at hrecordOk
    cases hservice : ActiveFollowerQueueOperation.checkedService rate.eta rate.sourceCap
        rate.n rate.n_scale follower.follower follower.row follower.activation
        follower.time observation state with
    | failure => simp [hservice] at hrecordOk
    | success result => exact ⟨result, rfl⟩
  rcases hchecked with ⟨result, hservice⟩
  have haction := result.action
  have hlast : ∃ M, state.lastDown = some M := by
    cases hstatus : state.status with
    | unoccupied => exact (hoccupied hstatus).elim
    | pending =>
        simp only [ActiveFollowerQueueOperation.serviceAction, hstatus] at haction
        rcases haction with ⟨_, M, hlast, _⟩
        exact ⟨M, hlast⟩
    | released =>
        simp only [ActiveFollowerQueueOperation.serviceAction, hstatus] at haction
        rcases haction with ⟨_, M, hlast, _⟩
        exact ⟨M, hlast⟩
  rcases hlast with ⟨M, hlast⟩
  refine ⟨M, CappedService.residual (4 * rate.n) state.backlog
      (ActiveFollowerQueueOperation.rawArrival rate.eta i r.input.row r.input.time M
        ((ReferenceActivePhysicalStep.prepare r.input).feedback.observations
          (PublicDiscreteDraws.followerPlayer p.two_le_m i))), ?_⟩
  unfold ReferenceFirstCorrectedCurrentFollowerQueueOverflowCover.actualOccupiedServiceResidual?
  simp only [Option.bind_some, hchoice]
  rw [hlast]
  simp [hoccupied, hfailure]

/-- On every actual complete-suffix record, the source API supplies ordinary
INPUT, CHOICE, and OUTPUT configurations and failure-free output. Whenever
the actual CHOICE is occupied, its checked service necessarily has a saved
DOWN and is present in the guarded residual observer. This is the source-level
availability fact used for birth, LIVE, and retained collection indices. -/
theorem completeSuffixFollowerRegisterObservers_available
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length) (i : Fin (p.m - 1)) :
    ∃ input inputMemory choice choiceMemory next nextMemory,
      (((ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val]).input.state.followers i) =
        .ordinary input inputMemory ∧
      (ReferenceFollowerFixedReply.actualChoice
        (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val]
        i).configuration = .ordinary choice choiceMemory ∧
      (((ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val]).output.followers i).configuration =
        .ordinary next nextMemory ∧
      (((ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val]).output.followers i).failure =
        none ∧
      (((ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val]).output.next.followers i) =
        .ordinary next nextMemory ∧
      ((∃ M q, ReferenceFirstCorrectedCurrentFollowerQueueOverflowCover.actualOccupiedServiceResidual?
        (rate := rate)
        (some (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val])
        i = some (some M, q)) ∨ choice.status = .unoccupied) := by
  obtain ⟨input, inputMemory, choice, next, nextMemory, hinput, hchoice, _hchoiceDomain,
      _hnextDomain, houtput, hfailure, hnext⟩ :=
    ReferenceCompleteSuffixFollowerPreservation.complete_suffix_follower_output
      (rate := rate) rewards C_star C_h z k i
  refine ⟨input, inputMemory, choice, inputMemory, next, nextMemory, hinput, hchoice,
    houtput, hfailure, hnext, ?_⟩
  by_cases hoccupied : choice.status ≠ .unoccupied
  · rcases occupiedServiceObserver_available rate
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val]
      i choice inputMemory next nextMemory hchoice houtput hoccupied hfailure with
      ⟨M, q, hread⟩
    exact Or.inl ⟨M, q, hread⟩
  · exact Or.inr (Classical.not_not.mp hoccupied)

private theorem liveTail_eq_continuingPrefix
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p) :
    ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
      rate rewards C_star C_h z
        (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.birthIndex
          rate rewards C_star C_h z + 1) =
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.liveTail
        rate rewards C_star C_h z := by
  simp only [ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix,
    ReferenceFirstCollectionCorrectedSliceNumericalPrefix.liveTail,
    ReferenceFirstReplacementLiveFollowerPrefix.continuingTail,
    ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords]
  congr 2
  funext r
  unfold ReferenceCompleteLaterLiveComplementPrefixReplay.continuingTest
    ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen
  cases hcoord : r.output.preparation.coordinator with
  | first outcome => rfl
  | live registers owned base outcome => cases outcome <;> rfl
  | collection payload ledger clock cutoff outcome => rfl
  | invalidCollectionCutoff => rfl
  | dagger => rfl

/-- The actual boundary query is source-derived: at the horizon the LIVE
terminal theorem gives `e = R.length`; otherwise the accepted boundary
exclusion producer yields a nonempty segment and its first excluded record,
or exact horizon exhaustion. -/
theorem actualFirstCollectionBoundaryAvailable
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hz : z ∈ ReferenceFirstCollectionCorrectedSliceNumericalPrefix.correctedCell
      rate rewards C_star C_h u t) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let b := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.birthIndex rate rewards C_star C_h z
    let W := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.liveTail rate rewards C_star C_h z
    let e := b + 1 + W.length
    e ≤ R.length ∧
      (e = R.length ∨ ∃ seg : ReferenceCollectionSegmentExtraction.Segment rate,
        ReferenceCollectionSegmentExtraction.segmentAt R e = some seg ∧
        seg.records ≠ [] ∧
        ReferenceFirstCorrectedCollectionBoundaryExclusion.firstCellCollectionBoundaryExclusionResult
          rate rewards C_star C_h z e seg) := by
  classical
  intro R b W e
  by_cases hterminal : t.val + 1 = p.T
  · obtain ⟨_birth, _P, _A, hb, hborn, _hsigma, _hV, _hbound, hLiveTerminal,
        _hwords, _hA_length, _hprefix, _hsites⟩ :=
      ReferenceFirstCorrectedCurrentFollowerLiveQueue.actual_first_corrected_current_live_queues
        rate rewards C_star C_h u t z hz
    have hterm := hLiveTerminal hterminal
    rcases hterm with ⟨hbend, hWnil, _hVlen⟩
    have hbend' : b + 1 = R.length := by simpa only [b, R] using hbend
    have hWnil' : W = [] := by simpa only [W] using hWnil
    have he : e = R.length := by
      dsimp only [e]
      rw [hWnil']
      exact hbend'
    exact ⟨by omega, Or.inl he⟩
  · have hq : t.val + 1 < p.T := by omega
    have hboundary :=
      ReferenceFirstCorrectedCollectionBoundaryExclusion.firstCell_actual_collection_boundary_exclusion
        rate rewards C_star C_h u t z hz hq
    have hwindow :
        ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
          rate rewards C_star C_h z (b + 1) = W := by
      simpa only [b, W] using liveTail_eq_continuingPrefix rate rewards C_star C_h z
    have hboundary' :
        b + 1 + W.length ≤ R.length ∧
          (b + 1 + W.length = R.length ∨
            ∃ seg : ReferenceCollectionSegmentExtraction.Segment rate,
              ReferenceFirstCorrectedCollectionBoundaryExclusion.firstCellCollectionBoundaryExclusionResult
                rate rewards C_star C_h z (b + 1 + W.length) seg) := by
      simpa only [R, b, ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords,
        hwindow] using hboundary
    rcases hboundary' with ⟨hbound, hcase⟩
    have hcase' : e = R.length ∨
        ∃ seg : ReferenceCollectionSegmentExtraction.Segment rate,
          ReferenceCollectionSegmentExtraction.segmentAt R e = some seg ∧
          seg.records ≠ [] ∧
          ReferenceFirstCorrectedCollectionBoundaryExclusion.firstCellCollectionBoundaryExclusionResult
            rate rewards C_star C_h z e seg := by
      rcases hcase with hend | ⟨seg, hresult⟩
      · exact Or.inl (by simpa only [e] using hend)
      · have hseg : ReferenceCollectionSegmentExtraction.segmentAt R
            (b + 1 + W.length) = some seg := hresult.1
        have hnonempty : seg.records ≠ [] := hresult.2.1
        exact Or.inr ⟨seg, by simpa only [e] using hseg,
          hnonempty, by simpa only [e] using hresult⟩
    exact ⟨by simpa only [e] using hbound, hcase'⟩

private theorem collectionEntry_lookup
    (R : List Record) (e : ℕ)
    (seg : ReferenceCollectionSegmentExtraction.Segment rate)
    (hseg : ReferenceCollectionSegmentExtraction.segmentAt R e = some seg) :
    R[e]? = some seg.entry := by
  classical
  have hbranch :=
    (ReferenceCollectionSegmentExtraction.segmentAt_branch R e seg hseg).1
  cases hdrop : R.drop e with
  | nil => simp [hdrop, ReferenceCollectionSegmentExtraction.segment] at hbranch
  | cons first rest =>
      have hseg' : ReferenceCollectionSegmentExtraction.segment (first :: rest) = some seg := by
        simpa only [hdrop] using hbranch
      unfold ReferenceCollectionSegmentExtraction.segment at hseg'
      cases hc : ReferenceCollectionSegmentExtraction.choice first.input with
      | none => simp [hc] at hseg'
      | some context =>
          simp only [hc, Option.map_some] at hseg'
          split at hseg'
          · have hfields := Option.some.inj hseg'
            have hentry : seg.entry = first := by
              have := congrArg ReferenceCollectionSegmentExtraction.Segment.entry hfields
              simpa using this.symm
            have hlookup : R[e]? = some first := by
              have h := congrArg (fun records : List Record => records[0]?) hdrop
              simp only [List.getElem?_drop, Nat.add_zero] at h
              simpa [hdrop] using h
            rw [hentry]
            exact hlookup
          · have hfields := Option.some.inj hseg'
            have hentry : seg.entry = first := by
              have := congrArg ReferenceCollectionSegmentExtraction.Segment.entry hfields
              simpa using this.symm
            have hlookup : R[e]? = some first := by
              have h := congrArg (fun records : List Record => records[0]?) hdrop
              simp only [List.getElem?_drop, Nat.add_zero] at h
              simpa [hdrop] using h
            rw [hentry]
            exact hlookup

private theorem collectionRecord_lookup
    (R : List Record) (e : ℕ)
    (seg : ReferenceCollectionSegmentExtraction.Segment rate)
    (hseg : ReferenceCollectionSegmentExtraction.segmentAt R e = some seg)
    (j : Fin seg.records.length) :
    R[e + j.val]? = some (seg.records.get j) := by
  have hpart := ReferenceCollectionSegmentExtraction.segmentAt_partition R e seg hseg
  have hindex := congrArg (fun records : List Record => records[j.val]?) hpart
  have hleft : (seg.records ++ seg.remaining)[j.val]? = some (seg.records.get j) := by
    rw [List.getElem?_append_left j.isLt]
    simp
  rw [hleft, List.getElem?_drop] at hindex
  exact hindex.symm

private theorem collectionRemainingHead_lookup
    (R : List Record) (e : ℕ)
    (seg : ReferenceCollectionSegmentExtraction.Segment rate)
    (hseg : ReferenceCollectionSegmentExtraction.segmentAt R e = some seg)
    (r : Record) (hhead : seg.remaining.head? = some r) :
    R[e + seg.records.length]? = some r := by
  have hpart := ReferenceCollectionSegmentExtraction.segmentAt_partition R e seg hseg
  have hleft : (seg.records ++ seg.remaining)[seg.records.length]? = some r := by
    rw [List.getElem?_append_right (l₁ := seg.records) (l₂ := seg.remaining) le_rfl]
    simpa only [List.head?_eq_getElem?, Nat.sub_self] using hhead
  have hindex := congrArg
    (fun records : List Record => records[seg.records.length]?) hpart
  rw [hleft, List.getElem?_drop] at hindex
  exact hindex.symm

private theorem followerRegisterObserver_read_fields
    (configuration : Option (DeclaredFollowerLocalRound.LocalConfiguration p rate))
    (last : Option (OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta)))
    (q : ℕ)
    (hread : ReferenceFirstCorrectedCurrentFollowerQueueOverflowCover.followerRegisterObserver?
      (rate := rate) configuration = some (last, q)) :
    ∃ state memory,
      configuration = some (.ordinary state memory) ∧
      state.lastDown = last ∧ state.backlog = q := by
  classical
  cases configuration with
  | none => simp [ReferenceFirstCorrectedCurrentFollowerQueueOverflowCover.followerRegisterObserver?] at hread
  | some configuration =>
      cases configuration with
      | dagger =>
          simp [ReferenceFirstCorrectedCurrentFollowerQueueOverflowCover.followerRegisterObserver?] at hread
      | ordinary state memory =>
          simp only [ReferenceFirstCorrectedCurrentFollowerQueueOverflowCover.followerRegisterObserver?]
            at hread
          have hpair := Option.some.inj hread
          rcases Prod.mk.inj hpair with ⟨hlast, hbacklog⟩
          exact ⟨state, memory, rfl, hlast, hbacklog⟩

private def liveFollowerRegisterSiteIndex (V : List Record) :
    ReferenceFirstCorrectedCurrentFollowerQueueOverflowCover.LiveFollowerRegisterSite
      (rate := rate) V → Fin V.length
  | .input j => j
  | .choice j => j
  | .output j => j
  | .serviceResidual j => j

private theorem actualOccupiedServiceResidual_ne_some_none
    (r : Record) (i : Fin (p.m - 1)) (q : ℕ) :
    ReferenceFirstCorrectedCurrentFollowerQueueOverflowCover.actualOccupiedServiceResidual?
      (rate := rate) (some r) i ≠ some (none, q) := by
  classical
  intro hEq
  unfold ReferenceFirstCorrectedCurrentFollowerQueueOverflowCover.actualOccupiedServiceResidual?
    at hEq
  simp only [Option.bind_some] at hEq
  cases hchoice : (ReferenceFollowerFixedReply.actualChoice r i).configuration with
  | dagger => simp [hchoice] at hEq
  | ordinary state memory =>
      by_cases hu : state.status = .unoccupied
      · simp [hchoice, hu] at hEq
      · simp only [hchoice, hu] at hEq
        split at hEq
        · simp at hEq
        · split at hEq <;> simp at hEq

private theorem liveObservedSite_attributed
    (V : List Record) (P : ReferenceActivePhysicalStep.Payload rate)
    (i : Fin (p.m - 1))
    (site : ReferenceFirstCorrectedCurrentFollowerQueueOverflowCover.LiveFollowerRegisterSite
      (rate := rate) V)
    (last : Option (OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta)))
    (q : ℕ)
    (hread : ReferenceFirstCorrectedCurrentFollowerQueueOverflowCover.observeLiveFollowerRegister
      (rate := rate) V i site = some (last, q))
    (hlarge : (q : ℝ) / (rate.n : ℝ) > 1 / (32 * rate.eta.val))
    (hsource : ∀ (j : Fin V.length), ∃ input inputMemory choice next nextMemory,
      V[j.val].input.state.followers i = .ordinary input inputMemory ∧
      ActiveFollowerLifecycle.startRound rate.eta V[j.val].input.time input inputMemory =
        .ok (choice, inputMemory) ∧
      (ReferenceFollowerFixedReply.actualChoice V[j.val] i).configuration =
        .ordinary choice inputMemory ∧
      (V[j.val].output.followers i).configuration = .ordinary next nextMemory ∧
      (V[j.val].output.followers i).failure = none ∧
      V[j.val].output.next.followers i = .ordinary next nextMemory ∧
      (j.val = 0 → input.lastDown ≠ some (P.downRecord i) ∧
        choice.lastDown ≠ some (P.downRecord i)) ∧
      (input.lastDown = some (P.downRecord i) → input.status ≠ .unoccupied) ∧
      (choice.lastDown = some (P.downRecord i) → choice.status ≠ .unoccupied) ∧
      (next.lastDown = some (P.downRecord i) → next.status ≠ .unoccupied) ∧
      (choice.status ≠ .unoccupied → next.status ≠ .unoccupied ∧
        next.lastDown = choice.lastDown)) :
    (∃ site' q',
      ReferenceFirstCorrectedCurrentFollowerQueueOverflowCover.observeLiveFollowerRegister
        (rate := rate) V i site' = some (some (P.downRecord i), q') ∧
      (q' : ℝ) / (rate.n : ℝ) > 1 / (32 * rate.eta.val)) ∨
    ReferenceFirstCorrectedInheritedQueueOverflowCover.ordinaryRecordStoredBacklogOverflow
      rate P i (V.get (liveFollowerRegisterSiteIndex rate V site)) true := by
  classical
  cases site with
  | input j =>
      rcases hsource j with ⟨input, inputMemory, choice, next, nextMemory,
        hinput, _hstart, hchoice, houtput, _hfailure, hnext, _hbirthWords,
        _hinputCurrent, _hchoiceCurrent, _hnextCurrent, hframe⟩
      have hget : V.get j = V[j.val] := rfl
      have hfields : input.lastDown = last ∧ input.backlog = q := by
        have h := hread
        simpa [ReferenceFirstCorrectedCurrentFollowerQueueOverflowCover.observeLiveFollowerRegister,
          ReferenceFirstCorrectedCurrentFollowerQueueOverflowCover.followerInputRegister?,
          ReferenceFirstCorrectedCurrentFollowerQueueOverflowCover.followerRegisterObserver?,
          hget, hinput] using h
      rcases hfields with ⟨hlast, hbacklog⟩
      by_cases hcurrent : last = some (P.downRecord i)
      · left
        refine ⟨.input j, q, ?_, hlarge⟩
        simpa [hlast, hcurrent] using hread
      · right
        refine ⟨input, inputMemory, Or.inl ?_, ?_, ?_⟩
        · simpa [liveFollowerRegisterSiteIndex, hget] using hinput
        · intro heq
          exact hcurrent (hlast.symm.trans heq)
        · simpa [hbacklog] using hlarge
  | choice j =>
      rcases hsource j with ⟨input, inputMemory, choice, next, nextMemory,
        hinput, _hstart, hchoice, houtput, _hfailure, hnext, _hbirthWords,
        _hinputCurrent, _hchoiceCurrent, _hnextCurrent, hframe⟩
      have hget : V.get j = V[j.val] := rfl
      have hfields : choice.lastDown = last ∧ choice.backlog = q := by
        have h := hread
        simpa [ReferenceFirstCorrectedCurrentFollowerQueueOverflowCover.observeLiveFollowerRegister,
          ReferenceFirstCorrectedCurrentFollowerQueueOverflowCover.followerChoiceRegister?,
          ReferenceFirstCorrectedCurrentFollowerQueueOverflowCover.followerRegisterObserver?,
          hget, hchoice] using h
      rcases hfields with ⟨hlast, hbacklog⟩
      by_cases hcurrent : last = some (P.downRecord i)
      · left
        refine ⟨.choice j, q, ?_, hlarge⟩
        simpa [hlast, hcurrent] using hread
      · right
        refine ⟨choice, inputMemory, Or.inr (Or.inl ?_), ?_, ?_⟩
        · simpa [liveFollowerRegisterSiteIndex, hget] using hchoice
        · intro heq
          exact hcurrent (hlast.symm.trans heq)
        · simpa [hbacklog] using hlarge
  | output j =>
      rcases hsource j with ⟨input, inputMemory, choice, next, nextMemory,
        hinput, _hstart, hchoice, houtput, _hfailure, hnext, _hbirthWords,
        _hinputCurrent, _hchoiceCurrent, _hnextCurrent, hframe⟩
      have hget : V.get j = V[j.val] := rfl
      have hfields : next.lastDown = last ∧ next.backlog = q := by
        have h := hread
        simpa [ReferenceFirstCorrectedCurrentFollowerQueueOverflowCover.observeLiveFollowerRegister,
          ReferenceFirstCorrectedCurrentFollowerQueueOverflowCover.followerOutputRegister?,
          ReferenceFirstCorrectedCurrentFollowerQueueOverflowCover.followerRegisterObserver?,
          hget, houtput] using h
      rcases hfields with ⟨hlast, hbacklog⟩
      by_cases hcurrent : last = some (P.downRecord i)
      · left
        refine ⟨.output j, q, ?_, hlarge⟩
        simpa [hlast, hcurrent] using hread
      · right
        refine ⟨next, nextMemory, Or.inr (Or.inr ⟨rfl, ?_⟩), ?_, ?_⟩
        · simpa [liveFollowerRegisterSiteIndex, hget] using hnext
        · intro heq
          exact hcurrent (hlast.symm.trans heq)
        · simpa [hbacklog] using hlarge
  | serviceResidual j =>
      rcases hsource j with ⟨input, inputMemory, choice, next, nextMemory,
        hinput, _hstart, hchoice, houtput, _hfailure, hnext, _hbirthWords,
        _hinputCurrent, _hchoiceCurrent, _hnextCurrent, hframe⟩
      have hget : V.get j = V[j.val] := rfl
      have hres : ReferenceFirstCorrectedCurrentFollowerQueueOverflowCover.actualOccupiedServiceResidual?
          (rate := rate) (some (V.get j)) i = some (last, q) := by
        simpa only [ReferenceFirstCorrectedCurrentFollowerQueueOverflowCover.observeLiveFollowerRegister]
          using hread
      cases last with
      | none =>
          exact False.elim
            ((actualOccupiedServiceResidual_ne_some_none rate (V.get j) i q) hres)
      | some M =>
          have hservice := occupiedServiceResidual_output rate (V.get j) i M q hres
          rcases hservice with ⟨next', nextMemory', hnext', _hfailure, hbacklog⟩
          have hnextEq : next' = next := by
            rw [hget, houtput] at hnext'
            exact ((DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
              hnext').1).symm
          subst next'
          by_cases hcurrent : next.lastDown = some (P.downRecord i)
          · left
            refine ⟨.output j, q, ?_, hlarge⟩
            simp [ReferenceFirstCorrectedCurrentFollowerQueueOverflowCover.observeLiveFollowerRegister,
              ReferenceFirstCorrectedCurrentFollowerQueueOverflowCover.followerOutputRegister?,
              ReferenceFirstCorrectedCurrentFollowerQueueOverflowCover.followerRegisterObserver?,
              houtput, hcurrent, hbacklog]
          · right
            refine ⟨next, nextMemory, Or.inr (Or.inr ⟨rfl, ?_⟩), hcurrent, ?_⟩
            · simpa [liveFollowerRegisterSiteIndex, hget] using hnext
            · rw [hbacklog]
              exact hlarge

private theorem output_followers_eq_next (r : Record) (i : Fin (p.m - 1)) :
    (r.output.followers i).configuration = r.output.next.followers i := by
  rw [r.output_eq]
  rfl

private theorem collectionObservedSite_attributed
    (R : List Record) (e : ℕ)
    (seg : ReferenceCollectionSegmentExtraction.Segment rate)
    (hseg : ReferenceCollectionSegmentExtraction.segmentAt R e = some seg)
    (P : ReferenceActivePhysicalStep.Payload rate) (i : Fin (p.m - 1))
    (site : CollectionFollowerRegisterSite rate seg)
    (last : Option (OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))) (q : ℕ)
    (hread : observeCollectionFollowerRegister? (rate := rate) R e i
      ⟨seg, hseg, site⟩ = some (last, q))
    (hlarge : (q : ℝ) / (rate.n : ℝ) > 1 / (32 * rate.eta.val)) :
    (∃ site' q',
      ReferenceFirstCorrectedCurrentFollowerQueueOverflowCover.observeCollectionFollowerRegister
        (rate := rate) seg i site' = some (some (P.downRecord i), q') ∧
      (q' : ℝ) / (rate.n : ℝ) > 1 / (32 * rate.eta.val)) ∨
    (∃ k : Fin R.length, e ≤ k.val ∧ k.val ≤ e + seg.records.length ∧
      ReferenceFirstCorrectedInheritedQueueOverflowCover.ordinaryRecordStoredBacklogOverflow
        rate P i R[k.val] (decide (k.val < e + seg.records.length))) := by
  classical
  have classify (r : Record) (k : ℕ)
      (hlookup : R[k]? = some r) (hlower : e ≤ k)
      (hupper : k ≤ e + seg.records.length)
      (configuration : DeclaredFollowerLocalRound.LocalConfiguration p rate)
      (hphysical : configuration = r.input.state.followers i ∨
        configuration = (ReferenceFollowerFixedReply.actualChoice r i).configuration ∨
        (k < e + seg.records.length ∧ configuration = r.output.next.followers i))
      (currentSite : ReferenceFirstCorrectedCurrentFollowerQueueOverflowCover.CollectionFollowerRegisterSite
        (rate := rate) seg)
      (hcurrentRead : ReferenceFirstCorrectedCurrentFollowerQueueOverflowCover.observeCollectionFollowerRegister
        (rate := rate) seg i currentSite =
        ReferenceFirstCorrectedCurrentFollowerQueueOverflowCover.followerRegisterObserver?
          (rate := rate) (some configuration))
      (observedLast : Option (OrdinaryMessageCodec.DownRecord
        (ReferencePrelaunchFollower.codecParams p rate.eta)))
      (hobserved : ReferenceFirstCorrectedCurrentFollowerQueueOverflowCover.followerRegisterObserver?
        (rate := rate) (some configuration) = some (observedLast, q)) :
      (∃ site' q',
        ReferenceFirstCorrectedCurrentFollowerQueueOverflowCover.observeCollectionFollowerRegister
          (rate := rate) seg i site' = some (some (P.downRecord i), q') ∧
        (q' : ℝ) / (rate.n : ℝ) > 1 / (32 * rate.eta.val)) ∨
      (∃ k : Fin R.length, e ≤ k.val ∧ k.val ≤ e + seg.records.length ∧
        ReferenceFirstCorrectedInheritedQueueOverflowCover.ordinaryRecordStoredBacklogOverflow
          rate P i R[k.val] (decide (k.val < e + seg.records.length))) := by
    by_cases hcurrent : observedLast = some (P.downRecord i)
    · exact Or.inl ⟨currentSite, q, hcurrentRead.trans (hcurrent ▸ hobserved), hlarge⟩
    · obtain ⟨state, memory, hconfiguration, hlast, hbacklog⟩ :=
        followerRegisterObserver_read_fields rate (some configuration) observedLast q hobserved
      have hconfiguration' : configuration = .ordinary state memory :=
        Option.some.inj hconfiguration
      obtain ⟨hk, hr⟩ := List.getElem?_eq_some_iff.mp hlookup
      refine Or.inr ⟨⟨k, hk⟩, hlower, hupper, state, memory, ?_, ?_, ?_⟩
      · rw [hr]
        rcases hphysical with hin | hchoice | ⟨houtput, heq⟩
        · exact Or.inl (hin.symm.trans hconfiguration')
        · exact Or.inr (Or.inl (hchoice.symm.trans hconfiguration'))
        · exact Or.inr (Or.inr ⟨by simp only [decide_eq_true_eq]; exact houtput,
            heq.symm.trans hconfiguration'⟩)
      · intro heq
        exact hcurrent (hlast.symm.trans heq)
      · simpa only [hbacklog] using hlarge
  cases site with
  | cutoffInput =>
      exact classify seg.entry e (collectionEntry_lookup rate R e seg hseg)
        le_rfl (by omega) (seg.entry.input.state.followers i) (Or.inl rfl)
        .cutoffInput rfl last hread
  | cutoffChoice =>
      exact classify seg.entry e (collectionEntry_lookup rate R e seg hseg)
        le_rfl (by omega) (ReferenceFollowerFixedReply.actualChoice seg.entry i).configuration
        (Or.inr (Or.inl rfl)) .cutoffChoice rfl last hread
  | recordInput j =>
      exact classify (seg.records.get j) (e + j.val)
        (collectionRecord_lookup rate R e seg hseg j) (by omega) (by omega)
        ((seg.records.get j).input.state.followers i) (Or.inl rfl)
        (.recordInput j) rfl last hread
  | recordChoice j =>
      exact classify (seg.records.get j) (e + j.val)
        (collectionRecord_lookup rate R e seg hseg j) (by omega) (by omega)
        (ReferenceFollowerFixedReply.actualChoice (seg.records.get j) i).configuration
        (Or.inr (Or.inl rfl)) (.recordChoice j) rfl last hread
  | recordOutput j =>
      exact classify (seg.records.get j) (e + j.val)
        (collectionRecord_lookup rate R e seg hseg j) (by omega) (by omega)
        ((seg.records.get j).output.followers i).configuration
        (Or.inr (Or.inr ⟨by omega, output_followers_eq_next rate _ i⟩))
        (.recordOutput j) rfl last hread
  | serviceResidual j =>
      have hres : ReferenceFirstCorrectedCurrentFollowerQueueOverflowCover.actualOccupiedServiceResidual?
          (rate := rate) (some (seg.records.get j)) i = some (last, q) := hread
      cases last with
      | none =>
          exact False.elim ((actualOccupiedServiceResidual_ne_some_none rate _ i q) hres)
      | some M =>
          obtain ⟨next, nextMemory, houtput, _hfailure, hbacklog⟩ :=
            occupiedServiceResidual_output rate _ i M q hres
          apply classify (seg.records.get j) (e + j.val)
            (collectionRecord_lookup rate R e seg hseg j) (by omega) (by omega)
            ((seg.records.get j).output.followers i).configuration
            (Or.inr (Or.inr ⟨by omega, output_followers_eq_next rate _ i⟩))
            (.recordOutput j) rfl next.lastDown
          simp only [ReferenceFirstCorrectedCurrentFollowerQueueOverflowCover.followerRegisterObserver?,
            houtput, hbacklog]
  | remainingInput r hhead =>
      exact classify r (e + seg.records.length)
        (collectionRemainingHead_lookup rate R e seg hseg r hhead) (by omega) le_rfl
        (r.input.state.followers i) (Or.inl rfl)
        (.remainingInput r hhead) rfl last hread
  | remainingChoice r hhead =>
      exact classify r (e + seg.records.length)
        (collectionRemainingHead_lookup rate R e seg hseg r hhead) (by omega) le_rfl
        (ReferenceFollowerFixedReply.actualChoice r i).configuration
        (Or.inr (Or.inl rfl)) (.remainingChoice r hhead) rfl last hread

/-- Every physical LIVE follower-register site is attributable using the
actual birth payload recovered from the accepted corrected-source theorem.
The occupied-service case is classified by the actual OUTPUT word, after the
accepted residual-to-output identity. -/
theorem liveFollowerRegisterObserver_attributed
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hz : z ∈ ReferenceFirstCollectionCorrectedSliceNumericalPrefix.correctedCell
      rate rewards C_star C_h u t)
    (i : Fin (p.m - 1))
    (site : ReferenceFirstCorrectedCurrentFollowerQueueOverflowCover.LiveFollowerRegisterSite
      (rate := rate)
      (List.take (1 + (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.liveTail
          rate rewards C_star C_h z).length)
        ((ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).drop
          (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.birthIndex rate rewards C_star C_h z))))
    (last : Option (OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta)))
    (q : ℕ)
    (hread : ReferenceFirstCorrectedCurrentFollowerQueueOverflowCover.observeLiveFollowerRegister
      (rate := rate)
      (List.take (1 + (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.liveTail
          rate rewards C_star C_h z).length)
        ((ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).drop
          (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.birthIndex rate rewards C_star C_h z)))
      i site = some (last, q))
    (hlarge : (q : ℝ) / (rate.n : ℝ) > 1 / (32 * rate.eta.val)) :
    ReferenceFirstCorrectedInheritedQueueOverflowCover.literalOldInheritedFollowerStoredBacklogOverflowAt
        rate rewards C_star C_h u t z ∨
      z ∈ ReferenceFirstCorrectedCurrentFollowerQueueOverflowCover.currentFollowerRegisterOverflowEvent
        rate rewards C_star C_h u t := by
  classical
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let b := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.birthIndex rate rewards C_star C_h z
  let W := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.liveTail rate rewards C_star C_h z
  let V := (R.drop b).take (1 + W.length)
  have hLive := ReferenceFirstCorrectedCurrentFollowerLiveQueue.actual_first_corrected_current_live_queues
    rate rewards C_star C_h u t z hz
  rcases hLive with ⟨birth, P, A, hb, hborn, hsigma, hV, _hbound,
    _hterminal, _hword, _hAlength, _htake, hsites⟩
  have hsites' : ∀ (j : Fin V.length), ∃ input inputMemory choice next nextMemory,
      V[j.val].input.state.followers i = .ordinary input inputMemory ∧
      ActiveFollowerLifecycle.startRound rate.eta V[j.val].input.time input inputMemory =
        .ok (choice, inputMemory) ∧
      (ReferenceFollowerFixedReply.actualChoice V[j.val] i).configuration =
        .ordinary choice inputMemory ∧
      (V[j.val].output.followers i).configuration = .ordinary next nextMemory ∧
      (V[j.val].output.followers i).failure = none ∧
      V[j.val].output.next.followers i = .ordinary next nextMemory ∧
      (j.val = 0 → input.lastDown ≠ some (P.downRecord i) ∧
        choice.lastDown ≠ some (P.downRecord i)) ∧
      (input.lastDown = some (P.downRecord i) → input.status ≠ .unoccupied) ∧
      (choice.lastDown = some (P.downRecord i) → choice.status ≠ .unoccupied) ∧
      (next.lastDown = some (P.downRecord i) → next.status ≠ .unoccupied) ∧
      (choice.status ≠ .unoccupied → next.status ≠ .unoccupied ∧
        next.lastDown = choice.lastDown) := by
    intro j
    obtain ⟨input, inputMemory, choice, next, nextMemory, _hrecord,
      hinput, hstart, hchoice, houtput, hfailure, hnext, hbirthWords,
      hinputCurrent, hchoiceCurrent, hnextCurrent, hframe⟩ := hsites i j
    exact ⟨input, inputMemory, choice, next, nextMemory,
      by simpa [V] using hinput, by simpa [V] using hstart,
      by simpa [V] using hchoice, by simpa [V] using houtput,
      by simpa [V] using hfailure, by simpa [V] using hnext,
      by simpa [V] using hbirthWords,
      fun h => (hinputCurrent h).1,
      fun h => (hchoiceCurrent h).1,
      fun h => (hnextCurrent h).1,
      by simpa [V] using hframe⟩
  have hsiteAt := liveObservedSite_attributed rate V P i
    site last q hread hlarge hsites'
  rcases hsiteAt with hcurrent | hold
  · right
    change z ∈ ReferenceFirstCollectionCorrectedSliceNumericalPrefix.correctedCell
        rate rewards C_star C_h u t ∧ _
    refine ⟨hz, birth, P, ?_, hborn, hsigma, ?_⟩
    · simpa only [R, b, ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords] using hb
    · exact Or.inl ⟨i, hcurrent⟩
  · left
    change z ∈ ReferenceFirstCollectionCorrectedSliceNumericalPrefix.correctedCell
        rate rewards C_star C_h u t ∧ _
    refine ⟨hz, birth, P, ?_, hborn, hsigma, i, ?_⟩
    · simpa only [R, b, ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords] using hb
    · let j := liveFollowerRegisterSiteIndex rate V site
      have hget : V.get j = V[j.val] := rfl
      rw [hget] at hold
      exact Or.inl ⟨j, hold⟩

/-- A successful actual collection query is the same nonempty segment
produced by the source boundary theorem. A terminal LIVE window cannot supply
such a query. No segment-success or nonterminal premise is imposed on the
physical overflow event. -/
theorem actualCollectionFollowerRegisterBoundary
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T) (z : X)
    (hz : z ∈ ReferenceFirstCollectionCorrectedSliceNumericalPrefix.correctedCell
      rate rewards C_star C_h u t)
    (seg : ReferenceCollectionSegmentExtraction.Segment rate)
    (hseg : ReferenceCollectionSegmentExtraction.segmentAt
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)
      (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.birthIndex rate rewards C_star C_h z + 1 +
        (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.liveTail rate rewards C_star C_h z).length) =
      some seg) :
    ReferenceFirstCorrectedCollectionBoundaryExclusion.firstCellCollectionBoundaryExclusionResult
      rate rewards C_star C_h z
      (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.birthIndex rate rewards C_star C_h z + 1 +
        (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.liveTail rate rewards C_star C_h z).length)
      seg := by
  obtain ⟨_hbound, hboundary⟩ := actualFirstCollectionBoundaryAvailable
    rate rewards C_star C_h u t z hz
  rcases hboundary with hend | ⟨actual, hactual, _hne, hresult⟩
  · have hlookup := collectionEntry_lookup rate _ _ seg hseg
    rw [hend, List.getElem?_length] at hlookup
    cases hlookup
  · have heq : actual = seg := Option.some.inj (hactual.symm.trans hseg)
    subst actual
    exact hresult

/-- At a present first excluded record, the actual coordinator has chosen the
next assignment and the old pending set is empty. In particular no old
collection CHOICE exists there. Only INPUT and CHOICE follower registers from
this record occur in our old slice; its OUTPUT and service are not sites of
`CollectionFollowerRegisterSite`. -/
theorem actualExcludedCollectionFollowerBoundary
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T) (z : X)
    (hz : z ∈ ReferenceFirstCollectionCorrectedSliceNumericalPrefix.correctedCell
      rate rewards C_star C_h u t)
    (site : CollectionFollowerRegisterSiteOf rate
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)
      (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.birthIndex rate rewards C_star C_h z + 1 +
        (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.liveTail rate rewards C_star C_h z).length))
    (r : Record) (hhead : site.segment.remaining.head? = some r) :
    ReferenceCollectionPhaseHistory.laterChosen r.input = true ∧
      site.segment.final.pending = ∅ ∧
      ∀ c : ReferenceCollectionSegmentExtraction.Choice rate,
        ReferenceCollectionSegmentExtraction.choice r.input ≠ some c := by
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let e := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.birthIndex rate rewards C_star C_h z + 1 +
    (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.liveTail rate rewards C_star C_h z).length
  have hresult := actualCollectionFollowerRegisterBoundary rate rewards C_star C_h
    u t z hz site.segment site.available
  obtain ⟨_hseg, _hne, _hcut, saved, _hstate, _hcursor, hboundary⟩ := hresult
  have hlookup : R[e + site.segment.records.length]? = some r :=
    collectionRemainingHead_lookup rate R e site.segment site.available r hhead
  obtain ⟨hk, hr⟩ := List.getElem?_eq_some_iff.mp hlookup
  rcases hboundary with hend | ⟨hv, _hstate, _hcoord, _htime, _hdrop,
      hlater, hpending, _hreplies, hchoice⟩
  · change e + site.segment.records.length = R.length at hend
    exact False.elim (by omega)
  · rw [hr] at hlater hchoice
    exact ⟨hlater, hpending, hchoice⟩

/-- Exhaustive attribution of every literal physical follower-register site
at the same original corrected cell. Service is attributed by the actual
OUTPUT word, and the excluded collection boundary contributes INPUT/CHOICE
only. Birth and payload evidence are constructed from the accepted source API. -/
theorem followerRegisterOverflowEventAt_subset_old_union_current
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T) :
    followerRegisterOverflowEventAt rate rewards C_star C_h u t ⊆
      {z | ReferenceFirstCorrectedInheritedQueueOverflowCover.literalOldInheritedFollowerStoredBacklogOverflowAt
          rate rewards C_star C_h u t z} ∪
        ReferenceFirstCorrectedCurrentFollowerQueueOverflowCover.currentFollowerRegisterOverflowEvent
          rate rewards C_star C_h u t := by
  classical
  intro z hz
  change z ∈ ReferenceFirstCollectionCorrectedSliceNumericalPrefix.correctedCell
      rate rewards C_star C_h u t ∧ _ at hz
  obtain ⟨hz, hsites⟩ := hz
  rcases hsites with ⟨i, site, last, q, hread, hlarge⟩ | ⟨i, site, last, q, hread, hlarge⟩
  · exact liveFollowerRegisterObserver_attributed rate rewards C_star C_h
      u t z hz i site last q hread hlarge
  · let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let b := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.birthIndex rate rewards C_star C_h z
    let W := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.liveTail rate rewards C_star C_h z
    let e := b + 1 + W.length
    obtain ⟨seg, hseg, site⟩ := site
    have hboundary := actualCollectionFollowerRegisterBoundary rate rewards C_star C_h
      u t z hz seg hseg
    have hsameSegment : ReferenceCollectionSegmentExtraction.segmentAt R e = some seg := hboundary.1
    obtain ⟨birth, P, _A, hb, hborn, hsigma, _hV, _hbound,
      _hterminal, _hword, _hAlength, _htake, _hsites⟩ :=
      ReferenceFirstCorrectedCurrentFollowerLiveQueue.actual_first_corrected_current_live_queues
        rate rewards C_star C_h u t z hz
    have hb' : R[b]? = some birth := by
      simpa only [R, b, ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords] using hb
    have hattributed := collectionObservedSite_attributed rate R e seg hsameSegment
      P i site last q hread hlarge
    rcases hattributed with hcurrent | ⟨k, hlower, hupper, hold⟩
    · right
      change z ∈ ReferenceFirstCollectionCorrectedSliceNumericalPrefix.correctedCell
          rate rewards C_star C_h u t ∧ _
      refine ⟨hz, birth, P, hb', hborn, hsigma, Or.inr ?_⟩
      refine ⟨seg, ?_, i, hcurrent⟩
      simpa only [e, Nat.add_assoc] using hsameSegment
    · left
      change z ∈ ReferenceFirstCollectionCorrectedSliceNumericalPrefix.correctedCell
          rate rewards C_star C_h u t ∧ _
      refine ⟨hz, birth, P, hb', hborn, hsigma, i, Or.inr (Or.inr ?_)⟩
      refine ⟨seg, k, ?_, ?_, ?_, ?_⟩
      · simpa only [e, Nat.add_assoc] using hsameSegment
      · simpa only [e, Nat.add_assoc] using hlower
      · simpa only [e, Nat.add_assoc] using hupper
      · simpa only [e, Nat.add_assoc] using hold

/-- One inclusion over all source cells into the two shared overflow events.
No per-cell probability sum or additional time factor is introduced. -/
theorem followerRegisterOverflowEvent_subset_firstWindow_union_allArm
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) :
    followerRegisterOverflowEvent rate rewards C_star C_h ⊆
      ReferenceFirstLiveOriginalSourceOverflowBound.firstWindowOverflow
          rate rewards C_star C_h ∪
        ReferenceFirstCollectionCorrectedNumericalOverflowSum.allArmOverflowEvent
          rate rewards C_star C_h := by
  classical
  intro z hz
  simp only [followerRegisterOverflowEvent, Set.mem_iUnion] at hz
  obtain ⟨u, t, hz⟩ := hz
  rcases followerRegisterOverflowEventAt_subset_old_union_current
      rate rewards C_star C_h u t hz with hold | hcurrent
  · exact Or.inl
      (ReferenceFirstCorrectedInheritedQueueOverflowCover.literalOldInheritedFollowerStoredBacklogOverflow_subset_firstWindowOverflow
        rate rewards C_star C_h ⟨u, t, hold⟩)
  · apply Or.inr
    apply ReferenceFirstCollectionCorrectedAssignedOverflowCover.assignedAttributedOverflowUnion_subset_allArmOverflowEvent
      rate rewards C_star C_h
    simp only [Set.mem_iUnion]
    exact ⟨u, t,
      ReferenceFirstCorrectedCurrentFollowerQueueOverflowCover.currentFollowerRegisterOverflowEvent_subset_assignedAttributedOverflowEvent
        rate rewards C_star C_h u t hcurrent⟩

/-- The common source-law bound for the full literal follower-register event.
This is an outer-measure bound; inclusion alone supplies no Borel claim. -/
theorem followerRegisterOverflowEvent_measureReal_le
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (control0 : ReferenceFirstCorrectedInheritedQueueOverflowCover.TimeControl p) :
    (BootstrapPrivateRoundStreams.sourceInputLaw p).real
        (followerRegisterOverflowEvent rate rewards C_star C_h) ≤
      1 / (ConstructorDimensions.N p : ℝ) ^ 2 +
        2 * (p.K : ℝ) * ((p.T : ℝ) + 1) *
          Real.exp (-(CanonicalRecordingRates.beta p rate.eta.val) /
            (32 * rate.eta.val)) := by
  let μ := BootstrapPrivateRoundStreams.sourceInputLaw p
  calc
    μ.real (followerRegisterOverflowEvent rate rewards C_star C_h) ≤
        μ.real
          (ReferenceFirstLiveOriginalSourceOverflowBound.firstWindowOverflow
              rate rewards C_star C_h ∪
            ReferenceFirstCollectionCorrectedNumericalOverflowSum.allArmOverflowEvent
              rate rewards C_star C_h) :=
      MeasureTheory.measureReal_mono
        (followerRegisterOverflowEvent_subset_firstWindow_union_allArm
          rate rewards C_star C_h) (by finiteness)
    _ ≤ μ.real (ReferenceFirstLiveOriginalSourceOverflowBound.firstWindowOverflow
          rate rewards C_star C_h) +
        μ.real (ReferenceFirstCollectionCorrectedNumericalOverflowSum.allArmOverflowEvent
          rate rewards C_star C_h) := MeasureTheory.measureReal_union_le _ _
    _ ≤ _ := add_le_add
      (ReferenceFirstLiveOriginalSourceOverflowBound.firstWindowOverflow_measureReal_le_inv_N_sq
        rate rewards C_star C_h control0)
      (ReferenceFirstCollectionCorrectedNumericalOverflowSum.allArmOverflowEvent_measure_le
        rate rewards C_star C_h control0)

/-- The union of the physical LIVE register observations is contained in the
accepted old first-window event or the accepted current all-arm event. This
uses a single union inclusion over the original source cells. -/
theorem liveFollowerRegisterOverflowEvent_subset_firstWindow_union_allArm
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) :
    liveFollowerRegisterOverflowEvent rate rewards C_star C_h ⊆
      ReferenceFirstLiveOriginalSourceOverflowBound.firstWindowOverflow
          rate rewards C_star C_h ∪
        ReferenceFirstCollectionCorrectedNumericalOverflowSum.allArmOverflowEvent
          rate rewards C_star C_h := by
  classical
  intro z hz
  simp only [liveFollowerRegisterOverflowEvent, Set.mem_iUnion] at hz
  rcases hz with ⟨u, t, hz⟩
  change z ∈ ReferenceFirstCollectionCorrectedSliceNumericalPrefix.correctedCell
      rate rewards C_star C_h u t ∧ _ at hz
  rcases hz with ⟨hz, i, site, last, q, hread, hlarge⟩
  have hattributed := liveFollowerRegisterObserver_attributed rate rewards C_star C_h
    u t z hz i site last q hread hlarge
  rcases hattributed with hold | hcurrent
  · apply Or.inl
    apply ReferenceFirstCorrectedInheritedQueueOverflowCover.literalOldInheritedFollowerStoredBacklogOverflow_subset_firstWindowOverflow
      rate rewards C_star C_h
    exact ⟨u, t, hold⟩
  · apply Or.inr
    apply ReferenceFirstCollectionCorrectedAssignedOverflowCover.assignedAttributedOverflowUnion_subset_allArmOverflowEvent
      rate rewards C_star C_h
    simp only [Set.mem_iUnion]
    exact ⟨u, t,
      ReferenceFirstCorrectedCurrentFollowerQueueOverflowCover.currentFollowerRegisterOverflowEvent_subset_assignedAttributedOverflowEvent
        rate rewards C_star C_h u t hcurrent⟩

/-- The LIVE component inherits the common source-law bound from the two
accepted global events; no per-cell estimates are summed. -/
theorem liveFollowerRegisterOverflowEvent_measureReal_le
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (control0 : ReferenceFirstCorrectedInheritedQueueOverflowCover.TimeControl p) :
    (BootstrapPrivateRoundStreams.sourceInputLaw p).real
        (liveFollowerRegisterOverflowEvent rate rewards C_star C_h) ≤
      1 / (ConstructorDimensions.N p : ℝ) ^ 2 +
        2 * (p.K : ℝ) * ((p.T : ℝ) + 1) *
          Real.exp (-(CanonicalRecordingRates.beta p rate.eta.val) /
            (32 * rate.eta.val)) := by
  let μ := BootstrapPrivateRoundStreams.sourceInputLaw p
  calc
    μ.real (liveFollowerRegisterOverflowEvent rate rewards C_star C_h) ≤
        μ.real
          (ReferenceFirstLiveOriginalSourceOverflowBound.firstWindowOverflow
              rate rewards C_star C_h ∪
            ReferenceFirstCollectionCorrectedNumericalOverflowSum.allArmOverflowEvent
              rate rewards C_star C_h) :=
      MeasureTheory.measureReal_mono
        (liveFollowerRegisterOverflowEvent_subset_firstWindow_union_allArm
          rate rewards C_star C_h)
        (by finiteness)
    _ ≤
        μ.real (ReferenceFirstLiveOriginalSourceOverflowBound.firstWindowOverflow
          rate rewards C_star C_h) +
        μ.real (ReferenceFirstCollectionCorrectedNumericalOverflowSum.allArmOverflowEvent
          rate rewards C_star C_h) :=
      MeasureTheory.measureReal_union_le _ _
    _ ≤ 1 / (ConstructorDimensions.N p : ℝ) ^ 2 +
        2 * (p.K : ℝ) * ((p.T : ℝ) + 1) *
          Real.exp (-(CanonicalRecordingRates.beta p rate.eta.val) /
            (32 * rate.eta.val)) := by
      apply add_le_add
      · exact ReferenceFirstLiveOriginalSourceOverflowBound.firstWindowOverflow_measureReal_le_inv_N_sq
          rate rewards C_star C_h control0
      · exact ReferenceFirstCollectionCorrectedNumericalOverflowSum.allArmOverflowEvent_measure_le
          rate rewards C_star C_h control0

end Bandits.Support.ReferenceFirstCorrectedFollowerRegisterOverflowCover

end
