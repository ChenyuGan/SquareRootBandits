/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCorrectedFollowerQueueCopyRefinement
public import Bandits.Support.ReferenceFirstCorrectedReachedDownQueueOverflowCover
public import Bandits.Support.ReferenceFirstCorrectedNativeUpOverflowCover
public import Bandits.Support.ReferenceFirstCorrectedOldInheritedPrecallOverflowCover
public import Mathlib.MeasureTheory.Measure.Real

import Mathlib.Tactic

/-!
# Literal first-corrected physical queue-site attribution

This module defines the literal queue observer on one original complete
source execution and attributes every observed crossing to the accepted
coordinator, follower, native DOWN, or native UP event at the same cell. The
single all-cell event is covered by the existing common precall/collection
union and its numerical bound. The literal event's Borelness and manuscript
closure are not claimed here.

Sources: ZIP4 `appendix_a_local_protocol.tex:8-64`,
`04_slow_fast_learner.tex:157-187,256-290`,
`06_interruptions.tex:40-100,192-233,246-299,355-361,391-408,425-426`, and
`05_binary_transport.tex:7-43,60-114` under `sources/zip4/manuscript/`.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions MeasureTheory
open BootstrapPrivateRoundStreams (SourceInput sourceInputLaw)
open ContinuousLearningRows (TimeControl)
open ReferenceFirstCollectionCorrectedSliceNumericalPrefix
  (correctedCell sourceRecords birthIndex liveTail)
open ReferenceCollectionSegmentExtraction
open ReferenceFirstCorrectedCoordinatorQueueOverflowCover (CoordinatorQueueSite)
open ReferenceFirstCorrectedFollowerRegisterOverflowCover
  (CollectionFollowerRegisterSiteOf observeCollectionFollowerRegister?)
open ReferenceFirstCorrectedCurrentFollowerQueueOverflowCover
  (LiveFollowerRegisterSite observeLiveFollowerRegister)
open ReferenceFirstCorrectedFollowerQueueCopyRefinement
open ReferenceFirstCorrectedReachedDownQueueOverflowCover (DownQueueSite)
open ReferenceFirstCorrectedNativeUpComputedPrefixObservation (firstPrefixQueueAt)
open scoped Classical

namespace Bandits.Support.ReferenceFirstCorrectedPhysicalQueueSiteAttribution

variable {p : Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ)

local notation "X" => SourceInput p
local notation "Record" => ReferenceActivePhysicalHorizon.RoundRecord
  (p := p) (rate := rate)
local notation "Segment" => ReferenceCollectionSegmentExtraction.Segment rate
local notation "Payload" => ReferenceActivePhysicalStep.Payload rate


/-- A tagged query at an actual first-corrected source site. DOWN sites keep
absolute source indices and the current-payload guard in the evaluator.
Collection logged/offered tags use `CollectionFollowerCopySite`, covering its
entry, retained, and first-excluded CHOICE reads. Seed tags separately retain
the boundary INPUT/CHOICE reads; no first-excluded OUTPUT/service is added.
An absent or empty segment supplies no fabricated site. -/
inductive PhysicalQueueSite
    (R : List Record) (b : ℕ) (W : List Record) (P : Payload)
    (segment : Option Segment) (z : X) where
  | coordinator (site : CoordinatorQueueSite rate R b W P segment)
  | liveFollower (i : Fin (p.m - 1))
      (site : LiveFollowerRegisterSite (rate := rate)
        ((R.drop b).take (1 + W.length)))
  | collectionFollower (i : Fin (p.m - 1))
      (site : CollectionFollowerRegisterSiteOf rate R (b + 1 + W.length))
  | nativeDown (j : Fin R.length) (i : Fin (p.m - 1)) (site : DownQueueSite)
  | nativeUpPrefix (j k : ℕ)
  | loggedLive (i : Fin (p.m - 1))
      (j : Fin ((R.drop b).take (1 + W.length)).length)
  | loggedCollection (i : Fin (p.m - 1))
      (site : CollectionFollowerCopySite rate R (b + 1 + W.length))
  | offeredLive (i : Fin (p.m - 1))
      (j : Fin ((R.drop b).take (1 + W.length)).length)
  | offeredCollection (i : Fin (p.m - 1))
      (site : CollectionFollowerCopySite rate R (b + 1 + W.length))
  | liveSeed (i : Fin (p.m - 1))
      (j : Fin ((R.drop b).take (1 + W.length)).length) (field : StoredFollowerField)
  | collectionSeed (i : Fin (p.m - 1)) (seg : Segment)
      (available : segmentAt R (b + 1 + W.length) = some seg)
      (j : Fin seg.records.length) (field : StoredFollowerField)
  | cutoffSeed (i : Fin (p.m - 1)) (seg : Segment)
      (available : segmentAt R (b + 1 + W.length) = some seg) (choice : Bool)
  | excludedSeed (i : Fin (p.m - 1)) (seg : Segment)
      (available : segmentAt R (b + 1 + W.length) = some seg)
      (r : Record) (remaining : seg.remaining.head? = some r) (choice : Bool)

/-- Evaluate a tagged site by the actual optional source query. Native DOWN
stops before the first excluded record; native UP uses its accepted literal
expected-filtered observer, whose endpoint remains optional. -/
def physicalQueueAt? (R : List Record) (b : ℕ) (W : List Record)
    (P : Payload) (segment : Option Segment) (z : X)
    (site : PhysicalQueueSite rate R b W P segment z) : Option ℕ := by
  classical
  cases site with
  | coordinator site =>
      exact ReferenceFirstCorrectedCoordinatorQueueOverflowCover.physicalQueueAt?
        rate R b W P segment site
  | liveFollower i site =>
      exact (observeLiteralLiveFollower rate
        ((R.drop b).take (1 + W.length)) i site).map Prod.snd
  | collectionFollower i site =>
      exact (observeLiteralCollectionFollower rate
        R (b + 1 + W.length) i site).map Prod.snd
  | nativeDown j i site =>
      exact if b ≤ j.val ∧ j.val < b + 1 + W.length +
          (segment.map (fun seg => seg.records.length)).getD 0 then
        (R[j.val].output.preparation.coordinator.selection).bind fun current =>
          if current.view.payload = P then
            ReferenceFirstCorrectedReachedDownQueueOverflowCover.recordDownQueue?
              rate R[j.val] i site
          else none
      else none
  | nativeUpPrefix j k =>
      exact (firstPrefixQueueAt rate rewards C_star C_h z j k).map Prod.snd
  | loggedLive i j =>
      exact (recordLoggedRegister? rate (((R.drop b).take (1 + W.length)).get j) i).map Prod.snd
  | loggedCollection i site =>
      exact (recordLoggedRegister? rate site.record i).map Prod.snd
  | offeredLive i j =>
      exact recordOfferedQueue? rate (((R.drop b).take (1 + W.length)).get j) i
  | offeredCollection i site =>
      exact recordOfferedQueue? rate site.record i
  | liveSeed i j field =>
      exact recordSeed? rate (((R.drop b).take (1 + W.length)).get j) i field
  | collectionSeed i seg _available j field =>
      exact recordSeed? rate (seg.records.get j) i field
  | cutoffSeed i seg _available choice =>
      exact boundarySeed? rate seg.entry i choice
  | excludedSeed i _seg _available r _remaining choice =>
      exact boundarySeed? rate r i choice

/-- A stored-seed read retains the exact actual configuration field that
supplied its immutable DOWN word. The logged case is the accepted CHOICE
configuration; its q field is kept distinct from the moving backlog. -/
theorem recordSeed?_configuration (r : Record) (i : Fin (p.m - 1))
    (field : StoredFollowerField) (q : ℕ)
    (hread : recordSeed? rate r i field = some q) :
    ∃ state memory M,
      (match field with
        | .input => r.input.state.followers i = .ordinary state memory
        | .choice =>
            (ReferenceFollowerFixedReply.actualChoice r i).configuration =
              .ordinary state memory
        | .output => r.output.next.followers i = .ordinary state memory
        | .logged =>
            (ReferenceFollowerFixedReply.actualChoice r i).configuration =
              .ordinary state memory) ∧
      state.lastDown = some M ∧ M.val.q = q := by
  classical
  cases field with
  | input =>
      cases hconfig : r.input.state.followers i with
      | dagger => simp [recordSeed?, storedDownSeed?, hconfig] at hread
      | ordinary state memory =>
          obtain ⟨M, hM, hq⟩ := Option.map_eq_some_iff.mp
            (by simpa [recordSeed?, storedDownSeed?, hconfig] using hread)
          exact ⟨state, memory, M, rfl, hM, hq⟩
  | choice =>
      cases hconfig : (ReferenceFollowerFixedReply.actualChoice r i).configuration with
      | dagger => simp [recordSeed?, storedDownSeed?, hconfig] at hread
      | ordinary state memory =>
          obtain ⟨M, hM, hq⟩ := Option.map_eq_some_iff.mp
            (by simpa [recordSeed?, storedDownSeed?, hconfig] using hread)
          exact ⟨state, memory, M, rfl, hM, hq⟩
  | output =>
      cases hconfig : (r.output.followers i).configuration with
      | dagger => simp [recordSeed?, storedDownSeed?, hconfig] at hread
      | ordinary state memory =>
          obtain ⟨M, hM, hq⟩ := Option.map_eq_some_iff.mp
            (by simpa [recordSeed?, storedDownSeed?, hconfig] using hread)
          have hnext : r.output.next.followers i = .ordinary state memory :=
            (ReferenceFirstCorrectedFollowerQueueCopyRefinement.followerOutput_eq_next
              rate r i).symm.trans hconfig
          exact ⟨state, memory, M, hnext, hM, hq⟩
  | logged =>
      obtain ⟨register, hregister, hseed⟩ := Option.bind_eq_some_iff.mp hread
      obtain ⟨M, hM, hq⟩ := Option.map_eq_some_iff.mp hseed
      have hchoice :=
        ReferenceFirstCorrectedFollowerQueueCopyRefinement.recordLoggedRegister?_eq_choice_of_some
          rate r i register.1 register.2 hregister
      cases hconfig : (ReferenceFollowerFixedReply.actualChoice r i).configuration with
      | dagger =>
          simp [ReferenceFirstCorrectedCurrentFollowerQueueOverflowCover.followerChoiceRegister?,
            ReferenceFirstCorrectedCurrentFollowerQueueOverflowCover.followerRegisterObserver?,
            hconfig] at hchoice
      | ordinary state memory =>
          have hfields : state.lastDown = register.1 ∧ state.backlog = register.2 := by
            have hpair : (state.lastDown, state.backlog) = register := by
              simpa [ReferenceFirstCorrectedCurrentFollowerQueueOverflowCover.followerChoiceRegister?,
                ReferenceFirstCorrectedCurrentFollowerQueueOverflowCover.followerRegisterObserver?,
                hconfig]
                using hchoice
            exact ⟨by simpa using congrArg Prod.fst hpair,
              by simpa using congrArg Prod.snd hpair⟩
          exact ⟨state, memory, M, rfl, hfields.1.trans hM, hq⟩

/-- INPUT and CHOICE boundary seed reads preserve the exact side of the
boundary that supplied the immutable DOWN q field. -/
theorem boundarySeed?_configuration (r : Record) (i : Fin (p.m - 1))
    (choice : Bool) (q : ℕ)
    (hread : boundarySeed? rate r i choice = some q) :
    ∃ state memory M,
      (if choice then
        (ReferenceFollowerFixedReply.actualChoice r i).configuration = .ordinary state memory
      else r.input.state.followers i = .ordinary state memory) ∧
      state.lastDown = some M ∧ M.val.q = q := by
  cases choice with
  | false =>
      obtain ⟨state, memory, M, hconfig, hlast, hq⟩ :=
        recordSeed?_configuration rate r i .input q (by simpa [boundarySeed?] using hread)
      exact ⟨state, memory, M, by simpa using hconfig, hlast, hq⟩
  | true =>
      obtain ⟨state, memory, M, hconfig, hlast, hq⟩ :=
        recordSeed?_configuration rate r i .choice q (by simpa [boundarySeed?] using hread)
      exact ⟨state, memory, M, by simpa using hconfig, hlast, hq⟩

/-- Literal threshold event on the original birth, LIVE tail, and first
collection segment. All witnesses are read from the same source execution. -/
def literalPhysicalQueueOverflowEvent (u t : Fin p.T) : Set X :=
  {z | z ∈ correctedCell rate rewards C_star C_h u t ∧
    let R := sourceRecords rate rewards C_star C_h z
    let b := birthIndex rate rewards C_star C_h z
    let W := liveTail rate rewards C_star C_h z
    let segment := ReferenceCollectionSegmentExtraction.segmentAt R (b + 1 + W.length)
    ∃ birth : Record, R[b]? = some birth ∧
    ∃ P : Payload, ReferenceAssignmentPayloadPersistence.InstallationBirth birth P ∧
      P.sigma = t ∧
      ∃ site : PhysicalQueueSite rate R b W P segment z,
        ∃ q : ℕ, physicalQueueAt? rate rewards C_star C_h R b W P segment z site = some q ∧
          (q : ℝ) / (rate.n : ℝ) > 1 / (32 * rate.eta.val)}

/-- Exhaustive attribution of the literal operational observations to the
four accepted source components. Copy equalities are established above before
any analytical overflow cover is applied. -/
theorem literalPhysicalQueueOverflowEvent_subset_sourceEvents (u t : Fin p.T) :
    literalPhysicalQueueOverflowEvent rate rewards C_star C_h u t ⊆
      ReferenceFirstCorrectedCoordinatorQueueOverflowCover.coordinatorQueueOverflowEvent
        rate rewards C_star C_h u t ∪
      (ReferenceFirstCorrectedFollowerRegisterOverflowCover.followerRegisterOverflowEventAt
        rate rewards C_star C_h u t ∪
      (ReferenceFirstCorrectedNativeDownOverflowCover.nativeDownComputedOverflowEvent
        rate rewards C_star C_h u t ∪
        ReferenceFirstCorrectedNativeUpComputedPrefixObservation.firstNativeUpPrefixEvent
          rate rewards C_star C_h u t)) := by
  classical
  intro z hzEvent
  obtain ⟨hz, birth, hbirth, P, hborn, hsigma, site, q, hread, hlarge⟩ := hzEvent
  let R := sourceRecords rate rewards C_star C_h z
  let b := birthIndex rate rewards C_star C_h z
  let W := liveTail rate rewards C_star C_h z
  let e := b + 1 + W.length
  let V := (R.drop b).take (1 + W.length)
  have seedCover (i : Fin (p.m - 1)) (state : ReferencePrelaunchFollower.State p rate.eta)
      (memory : ActiveFollowerLifecycle.LocalMemory p)
      (r : Record)
      (M : OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
      (field : StoredFollowerField)
      (hconfiguration : match field with
        | .input => r.input.state.followers i = .ordinary state memory
        | .choice =>
            (ReferenceFollowerFixedReply.actualChoice r i).configuration =
              .ordinary state memory
        | .output => r.output.next.followers i = .ordinary state memory
        | .logged =>
            (ReferenceFollowerFixedReply.actualChoice r i).configuration =
              .ordinary state memory)
      (hlast : state.lastDown = some M)
      (hsite : ReferenceFirstCorrectedFollowerQueueCopyRefinement.localizedFollowerSeedSourceSite
        rate rewards C_star C_h z i state memory)
      (hread : recordSeed? rate r i field = some q) :
      z ∈ ReferenceFirstCorrectedCoordinatorQueueOverflowCover.coordinatorQueueOverflowEvent
        rate rewards C_star C_h u t := by
    exact ReferenceFirstCorrectedFollowerQueueCopyRefinement.recordSeed_crossing_mem_coordinator
      rate rewards C_star C_h u t z hz birth hbirth P hborn hsigma i r field q
      state memory M hconfiguration hlast hsite hread hlarge
  have boundarySeedCover (i : Fin (p.m - 1)) (r : Record) (choice : Bool)
      (state : ReferencePrelaunchFollower.State p rate.eta)
      (memory : ActiveFollowerLifecycle.LocalMemory p)
      (M : OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
      (hconfiguration : if choice then
        (ReferenceFollowerFixedReply.actualChoice r i).configuration = .ordinary state memory
        else r.input.state.followers i = .ordinary state memory)
      (hlast : state.lastDown = some M)
      (hsite : ReferenceFirstCorrectedFollowerQueueCopyRefinement.localizedFollowerSeedSourceSite
        rate rewards C_star C_h z i state memory)
      (hread : boundarySeed? rate r i choice = some q) :
      z ∈ ReferenceFirstCorrectedCoordinatorQueueOverflowCover.coordinatorQueueOverflowEvent
        rate rewards C_star C_h u t := by
    exact ReferenceFirstCorrectedFollowerQueueCopyRefinement.boundarySeed_crossing_mem_coordinator
      rate rewards C_star C_h u t z hz birth hbirth P hborn hsigma i r choice q
      state memory M hconfiguration hlast hsite hread hlarge
  cases site with
  | coordinator site =>
      exact Or.inl ⟨hz, birth, hbirth, P, hborn, hsigma, site, q, hread, hlarge⟩
  | liveFollower i site =>
      right; left
      change (observeLiteralLiveFollower rate V i site).map Prod.snd = some q at hread
      obtain ⟨⟨last, value⟩, hreg, hq⟩ := Option.map_eq_some_iff.mp hread
      have hvalue : value = q := hq
      subst value
      exact ReferenceFirstCorrectedFollowerQueueCopyRefinement.liveLiteralSite_crossing_mem_followerRegisterOverflowEventAt
        rate rewards C_star C_h u t z hz i site last q hreg hlarge
  | collectionFollower i site =>
      right; left
      change (observeLiteralCollectionFollower rate R e i site).map Prod.snd = some q at hread
      obtain ⟨⟨last, value⟩, hreg, hq⟩ := Option.map_eq_some_iff.mp hread
      have hvalue : value = q := hq
      subst value
      exact ReferenceFirstCorrectedFollowerQueueCopyRefinement.collectionLiteralSite_crossing_mem_followerRegisterOverflowEventAt
        rate rewards C_star C_h u t z hz i site last q hreg hlarge
  | nativeDown j i site =>
      right; right; left
      simp only [physicalQueueAt?] at hread
      split at hread
      next hbounds =>
        obtain ⟨current, hselection, hcurrent⟩ := Option.bind_eq_some_iff.mp hread
        split at hcurrent
        next hpayload =>
          exact ReferenceFirstCorrectedReachedDownQueueOverflowCover.recordDownQueue?_mem_nativeDownComputedOverflowEvent
            rate rewards C_star C_h u t z hz birth hbirth P hborn hsigma
            j hbounds.1 current hselection hpayload i site q hcurrent hlarge
        next => cases hcurrent
      next => cases hread
  | nativeUpPrefix j k =>
      right; right; right
      obtain ⟨⟨a, value⟩, hqueue, hq⟩ := Option.map_eq_some_iff.mp hread
      have hvalue : value = q := hq
      subst value
      exact ⟨hz, j, k, a, q, hqueue, hlarge⟩
  | loggedLive i j =>
      right; left
      change (recordLoggedRegister? rate (V.get j) i).map Prod.snd = some q at hread
      obtain ⟨⟨last, value⟩, hcopy, hq⟩ := Option.map_eq_some_iff.mp hread
      have hvalue : value = q := hq
      subst value
      exact ReferenceFirstCorrectedFollowerQueueCopyRefinement.liveLoggedRegister_crossing_mem_followerRegisterOverflowEventAt
        rate rewards C_star C_h u t z hz i V rfl j last q hcopy hlarge
  | loggedCollection i copySite =>
      right; left
      change (recordLoggedRegister? rate copySite.record i).map Prod.snd = some q at hread
      obtain ⟨⟨last, value⟩, hcopy, hq⟩ := Option.map_eq_some_iff.mp hread
      have hvalue : value = q := hq
      subst value
      exact ReferenceFirstCorrectedFollowerQueueCopyRefinement.collectionLoggedRegister_crossing_mem_followerRegisterOverflowEventAt
        rate rewards C_star C_h u t z hz i copySite last q hcopy hlarge
  | offeredLive i j =>
      right; left
      change recordOfferedQueue? rate (V.get j) i = some q at hread
      exact ReferenceFirstCorrectedFollowerQueueCopyRefinement.liveOfferedQueue_crossing_mem_followerRegisterOverflowEventAt
        rate rewards C_star C_h u t z hz i V rfl j q hread hlarge
  | offeredCollection i copySite =>
      right; left
      change recordOfferedQueue? rate copySite.record i = some q at hread
      exact ReferenceFirstCorrectedFollowerQueueCopyRefinement.collectionOfferedQueue_crossing_mem_followerRegisterOverflowEventAt
        rate rewards C_star C_h u t z hz i copySite q hread hlarge
  | liveSeed i j field =>
      left
      let r := V.get j
      change recordSeed? rate r i field = some q at hread
      obtain ⟨state, memory, M, hconfiguration, hlast, _hq⟩ :=
        recordSeed?_configuration rate r i field q hread
      have hphysical : r.input.state.followers i = .ordinary state memory ∨
          (ReferenceFollowerFixedReply.actualChoice r i).configuration = .ordinary state memory ∨
          r.output.next.followers i = .ordinary state memory := by
        cases field with
        | input => exact Or.inl hconfiguration
        | choice => exact Or.inr (Or.inl hconfiguration)
        | output => exact Or.inr (Or.inr hconfiguration)
        | logged => exact Or.inr (Or.inl hconfiguration)
      have hsite :
          ReferenceFirstCorrectedFollowerQueueCopyRefinement.localizedFollowerSeedSourceSite
            rate rewards C_star C_h z i state memory :=
        Or.inl ⟨j, hphysical⟩
      exact seedCover i state memory r M field hconfiguration hlast hsite hread
  | collectionSeed i seg available j field =>
      left
      let r := seg.records.get j
      change recordSeed? rate r i field = some q at hread
      obtain ⟨state, memory, M, hconfiguration, hlast, _hq⟩ :=
        recordSeed?_configuration rate r i field q hread
      have hphysical : r.input.state.followers i = .ordinary state memory ∨
          (ReferenceFollowerFixedReply.actualChoice r i).configuration = .ordinary state memory ∨
          r.output.next.followers i = .ordinary state memory := by
        cases field with
        | input => exact Or.inl hconfiguration
        | choice => exact Or.inr (Or.inl hconfiguration)
        | output => exact Or.inr (Or.inr hconfiguration)
        | logged => exact Or.inr (Or.inl hconfiguration)
      have hlookup := collectionRecord_lookup rate R e seg available j
      obtain ⟨hk, hget⟩ := List.getElem?_eq_some_iff.mp hlookup
      have hsite :
          ReferenceFirstCorrectedFollowerQueueCopyRefinement.localizedFollowerSeedSourceSite
            rate rewards C_star C_h z i state memory := by
        right
        refine ⟨seg, ⟨e + j.val, hk⟩, available, ?_, ?_, ?_⟩
        · dsimp only [e, b, W]; omega
        · dsimp only [e, b, W]; have := j.isLt; omega
        change R[e + j.val].input.state.followers i = _ ∨ _
        rw [hget]
        rcases hphysical with hi | hc | ho
        · exact Or.inl hi
        · exact Or.inr (Or.inl hc)
        · exact Or.inr (Or.inr ⟨by dsimp only [e, b, W]; have := j.isLt; omega, ho⟩)
      exact seedCover i state memory r M field hconfiguration hlast hsite hread
  | cutoffSeed i seg available choice =>
      left
      change boundarySeed? rate seg.entry i choice = some q at hread
      obtain ⟨state, memory, M, hconfiguration, hlast, _hq⟩ :=
        boundarySeed?_configuration rate seg.entry i choice q hread
      have hphysical : seg.entry.input.state.followers i = .ordinary state memory ∨
          (ReferenceFollowerFixedReply.actualChoice seg.entry i).configuration =
            .ordinary state memory := by
        by_cases hc : choice
        · simp only [hc] at hconfiguration
          exact Or.inr hconfiguration
        · simp only [hc] at hconfiguration
          exact Or.inl hconfiguration
      have hlookup := collectionEntry_lookup rate R e seg available
      obtain ⟨hk, hget⟩ := List.getElem?_eq_some_iff.mp hlookup
      have hsite :
          ReferenceFirstCorrectedFollowerQueueCopyRefinement.localizedFollowerSeedSourceSite
            rate rewards C_star C_h z i state memory := by
        right
        refine ⟨seg, ⟨e, hk⟩, available, le_rfl, ?_, ?_⟩
        · dsimp only [e, b, W]; omega
        change R[e].input.state.followers i = _ ∨ _
        rw [hget]
        exact hphysical.imp_right Or.inl
      exact boundarySeedCover i seg.entry choice state memory M hconfiguration hlast hsite hread
  | excludedSeed i seg available r remaining choice =>
      left
      change boundarySeed? rate r i choice = some q at hread
      obtain ⟨state, memory, M, hconfiguration, hlast, _hq⟩ :=
        boundarySeed?_configuration rate r i choice q hread
      have hphysical : r.input.state.followers i = .ordinary state memory ∨
          (ReferenceFollowerFixedReply.actualChoice r i).configuration =
            .ordinary state memory := by
        by_cases hc : choice
        · simp only [hc] at hconfiguration
          exact Or.inr hconfiguration
        · simp only [hc] at hconfiguration
          exact Or.inl hconfiguration
      have hlookup := collectionRemainingHead_lookup rate R e seg available r remaining
      obtain ⟨hk, hget⟩ := List.getElem?_eq_some_iff.mp hlookup
      have hsite :
          ReferenceFirstCorrectedFollowerQueueCopyRefinement.localizedFollowerSeedSourceSite
            rate rewards C_star C_h z i state memory := by
        right
        refine ⟨seg, ⟨e + seg.records.length, hk⟩, available, ?_, ?_, ?_⟩
        · dsimp only [e, b, W]; omega
        · rfl
        change R[e + seg.records.length].input.state.followers i = _ ∨ _
        rw [hget]
        exact hphysical.imp_right Or.inl
      exact boundarySeedCover i r choice state memory M hconfiguration hlast hsite hread

/-- The old all-arm event is extended to the same first-collection endpoint.
This is one inclusion, not a new probability charge. -/
theorem allArmOverflowEvent_subset_allArmCollectionOverflowEvent :
    ReferenceFirstCollectionCorrectedNumericalOverflowSum.allArmOverflowEvent
      rate rewards C_star C_h ⊆
    ReferenceFirstCorrectedCollectionPostCutoffNumericalOverflow.allArmCollectionOverflowEvent
      rate rewards C_star C_h := by
  intro z hz
  obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hz
  obtain ⟨u, hu⟩ := Set.mem_iUnion.mp ha
  obtain ⟨t, ht⟩ := Set.mem_iUnion.mp hu
  exact Set.mem_iUnion.mpr ⟨a, Set.mem_iUnion.mpr ⟨u, Set.mem_iUnion.mpr ⟨t,
    ReferenceFirstCorrectedCollectionPostCutoffNumericalOverflow.oldOverflowEvent_subset_collectionOverflowEvent
      rate rewards C_star C_h u t a ht⟩⟩⟩

/-- Every literal physical queue observation in a corrected cell lies in the
same precall/collection union. The old inherited case consumes the accepted
strict-precall transfer on this very cell. -/
theorem literalPhysicalQueueOverflowEvent_subset_precall_union_collection
    (u t : Fin p.T) :
    literalPhysicalQueueOverflowEvent rate rewards C_star C_h u t ⊆
      (ReferenceFirstCollectionPrecallOverflowBound.precallOverflow rate rewards C_star C_h ∪
        ReferenceFirstCorrectedCollectionPostCutoffNumericalOverflow.allArmCollectionOverflowEvent
          rate rewards C_star C_h) := by
  intro z hz
  have hparts := literalPhysicalQueueOverflowEvent_subset_sourceEvents
    rate rewards C_star C_h u t hz
  rcases hparts with hcoord | hfollower | hdown | hup
  · exact ReferenceFirstCorrectedCoordinatorQueueOverflowCover.coordinatorQueueOverflowEvent_subset_precall_union_collection
      rate rewards C_star C_h u t hcoord
  · rcases ReferenceFirstCorrectedFollowerRegisterOverflowCover.followerRegisterOverflowEventAt_subset_old_union_current
      rate rewards C_star C_h u t hfollower with hold | hcurrent
    · left
      exact ReferenceFirstCorrectedOldInheritedPrecallOverflowCover.literalOldInheritedFollowerStoredBacklogOverflowAt_subset_precallOverflow
        rate rewards C_star C_h u t hold
    · right
      apply allArmOverflowEvent_subset_allArmCollectionOverflowEvent rate rewards C_star C_h
      apply ReferenceFirstCollectionCorrectedAssignedOverflowCover.assignedAttributedOverflowEvent_subset_allArmOverflowEvent
        rate rewards C_star C_h u t
      exact ReferenceFirstCorrectedCurrentFollowerQueueOverflowCover.currentFollowerRegisterOverflowEvent_subset_assignedAttributedOverflowEvent
        rate rewards C_star C_h u t hcurrent
  · right
    exact allArmOverflowEvent_subset_allArmCollectionOverflowEvent rate rewards C_star C_h
      (ReferenceFirstCorrectedNativeDownOverflowCover.nativeDownComputedOverflowEvent_subset_allArmOverflowEvent
        rate rewards C_star C_h u t hdown)
  · right
    exact ReferenceFirstCorrectedNativeUpOverflowCover.firstNativeUpPrefixEvent_subset_allArmCollectionOverflowEvent
      rate rewards C_star C_h u t hup

/-- All corrected cells use one common precall/collection union, with no
additional physical truth or time-control premise. -/
theorem allLiteralPhysicalQueueOverflowEvent_subset_precall_union_collection :
    (⋃ u : Fin p.T, ⋃ t : Fin p.T,
      literalPhysicalQueueOverflowEvent rate rewards C_star C_h u t) ⊆
      (ReferenceFirstCollectionPrecallOverflowBound.precallOverflow rate rewards C_star C_h ∪
        ReferenceFirstCorrectedCollectionPostCutoffNumericalOverflow.allArmCollectionOverflowEvent
          rate rewards C_star C_h) := by
  intro z hz
  obtain ⟨u, hu⟩ := Set.mem_iUnion.mp hz
  obtain ⟨t, ht⟩ := Set.mem_iUnion.mp hu
  exact literalPhysicalQueueOverflowEvent_subset_precall_union_collection
    rate rewards C_star C_h u t ht

/-- The single common numerical budget, on the original source law. -/
theorem precall_union_collection_measureReal_le
    (control0 : ContinuousLearningRows.TimeControl p) :
    (BootstrapPrivateRoundStreams.sourceInputLaw p).real
      (ReferenceFirstCollectionPrecallOverflowBound.precallOverflow rate rewards C_star C_h ∪
        ReferenceFirstCorrectedCollectionPostCutoffNumericalOverflow.allArmCollectionOverflowEvent
          rate rewards C_star C_h) ≤
      3 * (p.K : ℝ) * ((p.T : ℝ) + 1) *
        Real.exp (-CanonicalRecordingRates.beta p rate.eta.val / (32 * rate.eta.val)) := by
  have hscale := ReferenceFirstCollectionPrecallOverflowBound.beta_mul_cap_eq_Lstab rate
  have hexp : Real.exp (-(CanonicalRecordingRates.L_stab p : ℝ)) =
      Real.exp (-CanonicalRecordingRates.beta p rate.eta.val / (32 * rate.eta.val)) := by
    rw [← hscale]
    congr 1
    ring
  have hpre := ReferenceFirstCollectionPrecallOverflowBound.precallOverflow_measureReal_le_exp
    rate rewards C_star C_h control0
  rw [hexp] at hpre
  have hcol := ReferenceFirstCorrectedCollectionPostCutoffNumericalOverflow.allArmCollectionOverflowEvent_measure_le
    rate rewards C_star C_h control0
  calc
    _ ≤ (BootstrapPrivateRoundStreams.sourceInputLaw p).real
          (ReferenceFirstCollectionPrecallOverflowBound.precallOverflow rate rewards C_star C_h) +
        (BootstrapPrivateRoundStreams.sourceInputLaw p).real
          (ReferenceFirstCorrectedCollectionPostCutoffNumericalOverflow.allArmCollectionOverflowEvent
            rate rewards C_star C_h) := MeasureTheory.measureReal_union_le _ _
    _ ≤ (p.K : ℝ) * ((p.T : ℝ) + 1) *
          Real.exp (-CanonicalRecordingRates.beta p rate.eta.val / (32 * rate.eta.val)) +
        2 * (p.K : ℝ) * ((p.T : ℝ) + 1) *
          Real.exp (-CanonicalRecordingRates.beta p rate.eta.val / (32 * rate.eta.val)) :=
      add_le_add hpre hcol
    _ = _ := by ring

/-- The full literal physical all-cell event has the common numerical budget.
Monotonicity under the finite source law needs no measurability premise on the
literal event. No per-site or per-cell probability summation is used. -/
theorem allLiteralPhysicalQueueOverflowEvent_measureReal_le
    (control0 : ContinuousLearningRows.TimeControl p) :
    (BootstrapPrivateRoundStreams.sourceInputLaw p).real
      (⋃ u : Fin p.T, ⋃ t : Fin p.T,
        literalPhysicalQueueOverflowEvent rate rewards C_star C_h u t) ≤
      3 * (p.K : ℝ) * ((p.T : ℝ) + 1) *
        Real.exp (-CanonicalRecordingRates.beta p rate.eta.val / (32 * rate.eta.val)) := by
  calc
    _ ≤ (BootstrapPrivateRoundStreams.sourceInputLaw p).real
        (ReferenceFirstCollectionPrecallOverflowBound.precallOverflow rate rewards C_star C_h ∪
          ReferenceFirstCorrectedCollectionPostCutoffNumericalOverflow.allArmCollectionOverflowEvent
            rate rewards C_star C_h) :=
      MeasureTheory.measureReal_mono
        (allLiteralPhysicalQueueOverflowEvent_subset_precall_union_collection
          rate rewards C_star C_h)
    _ ≤ _ := precall_union_collection_measureReal_le rate rewards C_star C_h control0

end Bandits.Support.ReferenceFirstCorrectedPhysicalQueueSiteAttribution
