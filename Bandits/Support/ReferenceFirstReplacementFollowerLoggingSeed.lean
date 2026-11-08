/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstReplacementInstalledCredit
import Lean.Elab.Tactic.Omega

/-!
# The actual first replacement's follower logging seed

Sources: `sources/zip4/manuscript/06_interruptions.tex:9-70,193-233,246-295`,
`sources/zip4/manuscript/05_binary_transport.tex:70-124,354-431`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-64`.

This internal result stops immediately after logging on the first reached
replacement round. The original complete source, whole grid reward table,
selected row index, and unrestricted shared constants remain the inputs.
The absent-record and other-dispatch branches have the explicit conclusion
`True`; no replacement existence or success of its observation tail follows.

The execution producer supplies a nonempty first collection. Writing its
raw window as `cut :: W` identifies the incoming replacement with the
original prefix after `w + 1 + W.length` physical steps. The admitted follower
prefix producer is applied at exactly `W.length`. Its ordinary follower,
retained OLD assignment reply, complete buffer, and partial decoder are
kept, rather than replaced by a newly initialized local state.

The common local domain and the unoccupied status make START an identity.
PREPARE still validates a selected UP offer and computes the actual arm from
that original state. Logging then appends the original row's `logAt` using
that prepared arm and its actual grid feedback. Source/mask success retains
the current record even when its observation is zero; no positivity or
thinning comparison is added. Successful logging frames every nonbuffer
field, including the original decoder bank and initialization-failure flag.
The actual diagnostic wrapper consequently receives this same logged state.

Immutable NEW DOWN credit is consumed from the admitted installation-credit
theorem. It is kept separate from the retained OLD reply in the incoming
follower. Neither NEW DOWN acceptance, checked recovery, release, FINISH,
ordinary output, coordinator-tail success, nor a manuscript claim is proved.
The next consumer is actual first-new-DOWN nonzero-queue recovery from this
original buffer and decoder with the installed base-plus-queue credit.
-/

@[expose] public section
noncomputable section

namespace Bandits.Support.ReferenceFirstReplacementFollowerLoggingSeed

open ConstructorDimensions
open ReferenceActivePhysicalHorizon
open ReferencePrelaunchFollower
open ActiveFollowerLifecycle

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

/-- The supplied index is in the literal original run. This helper produces
its record constructor, so the later join supplies no matching-trace premise. -/
private theorem record_at
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (span : start + count ≤ p.T)
    (active : allActiveAtStart initial start) (index : ℕ) (hi : index < count) :
    (run initial rows J rewards start count span active).records[index]? =
      some (ReferenceAssignmentPayloadChronology.actualRunRecordAt
        initial rows J rewards start index (by omega) active) := by
  induction count generalizing index with
  | zero => omega
  | succ count ih =>
      have hlen := run_record_count initial rows J rewards start count (by omega) active
      rw [ReferenceAssignmentPayloadChronology.run_successor_actualRunRecordAt
        initial rows J rewards start count span active]
      by_cases hlt : index < count
      · rw [List.getElem?_append_left (by simpa only [hlen] using hlt)]
        exact ih (by omega) index hlt
      · have heq : index = count := by omega
        subst index
        simp [hlen]

/-- The actual collection dispatch retains its incoming payload. The helper
inspects only the original dispatcher, including its invalid-cutoff branch. -/
private theorem collection_origin (x : ReferenceActivePhysicalStep.RoundInput p rate) :
    match ReferenceActivePhysicalStep.dispatch x with
    | .collection payload ledger _ _ _ =>
        ∃ saved, x.state.coordinator = .collection payload ledger saved
    | _ => True := by
  unfold ReferenceActivePhysicalStep.dispatch
  cases hs : x.state.coordinator with
  | first => simp only [CoordinatorRoundDispatch.dispatch]; trivial
  | live r q base => simp only [CoordinatorRoundDispatch.dispatch]; trivial
  | collection payload ledger saved =>
      simp only [CoordinatorRoundDispatch.dispatch]
      by_cases hcut : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
      · simp only [dite_eq_left hcut]
        exact ⟨saved, rfl⟩
      · simp only [dite_eq_right hcut]
  | dagger => trivial

/-- Conditional local PREPARE calculation. Its inputs are the actual carried
state's domain, unoccupied status, and old reply alternative. The root below
produces all three at the original collection endpoint. -/
private theorem prepare_configuration
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (activation : Activation p) (t : Fin p.T) (active : activation.val ≤ t.val + 1)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (old : ReferencePrelaunchFollower.State p rate.eta) (memory : LocalMemory p)
    (hdomain : localStateDomainValid old) (hstatus : old.status = .unoccupied)
    (halt : (old.lastDown = none ∧ old.S = 0 ∧ old.delta = 0 ∧ old.backlog = 0) ∨
      old.lastDown = some (payload.downRecord i)) :
    (DeclaredFollowerLocalRound.prepare rate i row activation t active
      (.ordinary old memory)).configuration = .ordinary old memory := by
  classical
  have hparts := hdomain
  obtain ⟨⟨hS, hdelta, hbacklog⟩, hbuffer, _hdecoder⟩ := hparts
  have hinput : ActiveFollowerQueueOperation.stateInputDomain old :=
    ⟨hS, hdelta, hbacklog, hbuffer.1, hbuffer.2.1⟩
  have hadmissible : OrdinaryMessageCodec.upAdmissible
      (ReferencePrelaunchFollower.codecParams p rate.eta)
      (ActiveFollowerQueueOperation.upOfferFields old) := by
    rcases halt with ⟨hnone, hSzero, hdeltaZero, hbacklogZero⟩ | hsome
    · simp [OrdinaryMessageCodec.upAdmissible, OrdinaryMessageCodec.upPlaceholder,
        ActiveFollowerQueueOperation.upOfferFields, ReferencePrelaunchFollower.acceptedStart,
        hnone, hSzero, hdeltaZero, hbacklogZero]
    · right
      have hstart : ReferencePrelaunchFollower.acceptedStart old = payload.sigma.val + 1 := by
        simp only [ReferencePrelaunchFollower.acceptedStart, hsome]
        rfl
      rw [ActiveFollowerQueueOperation.upOfferFields, hstart]
      change 1 ≤ payload.sigma.val + 1 ∧ payload.sigma.val + 1 ≤ p.T ∧
        old.S ≤ p.T * D p ∧ old.delta ≤ D p ∧ old.backlog ≤ p.T * D p
      exact ⟨by omega, by have := payload.sigma.isLt; omega, hS, hdelta, hbacklog⟩
  have hstart := ActiveFollowerLifecycle.startRound_unoccupied
    rate.eta t old memory hdomain hstatus
  let offered : OrdinaryMessageCodec.UpRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta) :=
    ⟨ActiveFollowerQueueOperation.upOfferFields old, hadmissible⟩
  by_cases hselected : ActiveFollowerQueueOperation.selectedUpRound i row activation t
  · have hoff : ActiveFollowerQueueOperation.checkedUpOffer rate.eta i row activation t old =
        .offer offered := by
      unfold ActiveFollowerQueueOperation.checkedUpOffer
      rw [dite_eq_left hinput, dite_eq_left (show
        ActiveFollowerQueueOperation.selectedUpRound i row activation t ∧
          old.status = .unoccupied from ⟨hselected, hstatus⟩), dite_eq_left hadmissible]
    have hvalid : ActiveFollowerArmChoice.upStateDomain old ∧
        ActiveFollowerArmChoice.offeredUpMatchesState old offered :=
      ⟨⟨hS, hdelta, hbacklog⟩, by
        simp only [ActiveFollowerArmChoice.offeredUpMatchesState, offered,
          ActiveFollowerQueueOperation.upOfferFields, and_self]⟩
    have hchoice := ActiveFollowerArmChoice.followerArmChoiceCore_unoccupied_selected_up
      old (row.2 t) i offered hstatus hselected.2.1 hselected.2.2 hvalid
    rw [← ActiveFollowerArmChoice.followerArmChoice_eq_core old row t i (some offered)]
      at hchoice
    simp only [DeclaredFollowerLocalRound.prepare, hstart, hoff, hchoice]
  · have hoff := ActiveFollowerQueueOperation.checkedUpOffer_noOffer
      rate.eta i row activation t old hinput (fun h => hselected h.1)
    by_cases hdata : PublicDiscreteDraws.slotDraw (row.2 t).1 = PublicDiscreteDraws.dataSlot
    · have hchoice := ActiveFollowerArmChoice.followerArmChoiceCore_unoccupied_data
        old (row.2 t) i none hstatus hdata
      rw [← ActiveFollowerArmChoice.followerArmChoice_eq_core old row t i none] at hchoice
      simp only [DeclaredFollowerLocalRound.prepare, hstart, hoff, hchoice]
    · have hup : ¬ (PublicDiscreteDraws.slotDraw (row.2 t).1 = PublicDiscreteDraws.upSlot ∧
          PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K (row.2 t).1 = i) :=
        fun h => hselected ⟨active, h⟩
      have hchoice := ActiveFollowerArmChoice.followerArmChoiceCore_unoccupied_other
        old (row.2 t) i none hstatus hdata hup
      rw [← ActiveFollowerArmChoice.followerArmChoice_eq_core old row t i none] at hchoice
      simp only [DeclaredFollowerLocalRound.prepare, hstart, hoff, hchoice]

/-- On the complete original source, produce the actual incoming ordinary
followers, unchanged PREPARE configurations and successful logging at the
first reached replacement. All other record/dispatch cases state `True`.

There are no reachability, crossing, domain, success, trace, current-word,
overflow, or numerical-credit premises in this telescope. The retained
`oldPayload.downRecord` alternative concerns the OLD assignment; the final
three inequalities concern the NEW installed immutable DOWN record. -/
theorem complete_first_replacement_follower_logging_seed
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
    let s := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
    let Cwin := ReferenceCollectionPhaseHistory.collectionWindow R w
    let v := w + Cwin.length
    match R[v]? with
    | none => True
    | some record => match record.output.preparation.coordinator with
      | .collection oldPayload _ledger _ _
          (.laterChosen _ _ _ _ _ _ output _ clockData installed _) =>
          let x := record.input
          installed = CoordinatorAssignmentRegisterInstall.installLater output clockData ∧
          oldPayload.sigma.val = s ∧ x.time.val = s + v ∧
          x.rows = source.1.2 ∧
          x.selected = ActualInitializationPhysicalStep.selectedRowIndex p source ∧
          x.rewards = rewards ∧ installed.registers.payload.sigma.val = x.time.val ∧
          ∀ i : Fin (p.m - 1),
            let prepared := record.output.preparation.followers.followers i
            let actualOwn := (prepared.arm, record.output.preparation.feedback.observations
              (PublicDiscreteDraws.followerPlayer p.two_le_m i))
            ∃ old memory logged,
              x.state.followers i = .ordinary old memory ∧
              old.status = .unoccupied ∧ localStateDomainValid old ∧ localBufferValid old ∧
              downDecoderStateValid old ∧
              ReferenceFollowerDecoderChronology.downBatchEndpoint old x.time.val ∧
              old.S + old.backlog ≤ w * D p ∧
              (∀ saved ∈ old.buffer, 1 ≤ saved.calendarRound ∧ saved.calendarRound ≤ p.T) ∧
              (old.buffer.map (fun saved => (saved.calendarRound, saved.pilot))).Nodup ∧
              (∀ saved ∈ old.buffer, ∃ q : ℕ, q ≤ D p ∧
                saved.observation.val = (q : ℝ) / (D p : ℝ)) ∧
              old.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound) ∧
              (∀ saved ∈ old.buffer, saved.calendarRound < x.time.val + 1) ∧
              ((old.lastDown = none ∧ old.S = 0 ∧ old.delta = 0 ∧ old.backlog = 0) ∨
                old.lastDown = some (oldPayload.downRecord i)) ∧
              ActiveFollowerLifecycle.startRound rate.eta x.time old memory = .ok (old, memory) ∧
              prepared = DeclaredFollowerLocalRound.prepare rate i x.row
                (x.state.activations i) x.time (x.active i) (.ordinary old memory) ∧
              prepared.configuration = .ordinary old memory ∧
              prepared.row = x.row ∧ prepared.follower = i ∧
              prepared.time = x.time ∧ prepared.activation = x.state.activations i ∧
              record.output.preparation.arms.actions
                (PublicDiscreteDraws.followerPlayer p.two_le_m i) = prepared.arm ∧
              ActiveFollowerLogging.checkedLogging i x.row (x.state.activations i)
                x.time actualOwn old = .ok logged ∧
              logged.buffer = old.buffer ++ logAt i x.row (x.state.activations i) x.time actualOwn ∧
              localBufferValid logged ∧ localStateDomainValid logged ∧
              logged.status = .unoccupied ∧ logged.lastDown = old.lastDown ∧
              logged.S = old.S ∧ logged.delta = old.delta ∧ logged.backlog = old.backlog ∧
              logged.downBatch = old.downBatch ∧
              logged.initializationFailure = old.initializationFailure ∧
              ReferenceFollowerDecoderChronology.downBatchEndpoint logged x.time.val ∧
              (∀ saved ∈ logged.buffer, 1 ≤ saved.calendarRound ∧ saved.calendarRound ≤ p.T) ∧
              (logged.buffer.map (fun saved => (saved.calendarRound, saved.pilot))).Nodup ∧
              (∀ saved ∈ logged.buffer, ∃ q : ℕ, q ≤ D p ∧
                saved.observation.val = (q : ℝ) / (D p : ℝ)) ∧
              logged.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound) ∧
              (∀ saved ∈ logged.buffer,
                saved.calendarRound ≤ x.time.val + 1 ∧ saved.calendarRound < x.time.val + 2) ∧
              logged.S + logged.backlog ≤ w * D p ∧
              (ReferenceActivePhysicalStep.recordFollower
                record.output.preparation.coordinator.downView i x.row
                (x.state.activations i) x.time (x.active i) actualOwn.1 actualOwn.2 old).downInput =
                  some logged ∧
              (record.output.followers i).downInput = some logged ∧
              (SparseCalendarReplay.loggingTestsPass
                  (loggingRound i x.row (x.state.activations i) x.time actualOwn) →
                logged.buffer = old.buffer ++
                  [SparseCalendarReplay.recordAt (x.time.val + 1)
                    (loggingRound i x.row (x.state.activations i) x.time actualOwn)]) ∧
              (¬ SparseCalendarReplay.loggingTestsPass
                  (loggingRound i x.row (x.state.activations i) x.time actualOwn) →
                logged.buffer = old.buffer) ∧
              (SparseCalendarReplay.loggingTestsPass
                  (loggingRound i x.row (x.state.activations i) x.time actualOwn) ↔
                (x.state.activations i).val ≤ x.time.val + 1 ∧
                PublicDiscreteDraws.slotDraw (x.row.2 x.time).1 = PublicDiscreteDraws.dataSlot ∧
                PublicDiscreteDraws.recorderSourceDraw p.two_le_m p.m_lt_K
                    (x.row.2 x.time).1 = PublicDiscreteDraws.followerPlayer p.two_le_m i ∧
                ∀ j : Fin p.m, j ≠ PublicDiscreteDraws.followerPlayer p.two_le_m i →
                  PublicDiscreteDraws.pilotDraw (K_pos p) j (x.row.2 x.time).1 ≠ actualOwn.1) ∧
              (installed.registers.payload.downRecord i).val.sigma = x.time.val + 1 ∧
              (installed.registers.payload.downRecord i).val.q ≤ x.time.val * D p ∧
              installed.retainedBaseScore i +
                (installed.registers.payload.downRecord i).val.q ≤ v * D p
      | _ => True := by
  classical
  have execution :=
    ReferenceFirstReplacementCollectionExecution.complete_first_replacement_collection_execution
      rate source rewards C_star C_h
  have credit := ReferenceFirstReplacementInstalledCredit.complete_first_replacement_installed_credit
    rate source rewards C_star C_h
  dsimp only at execution credit ⊢
  set R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
  set s := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
  set w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
  set Cwin := ReferenceCollectionPhaseHistory.collectionWindow R w
  set v := w + Cwin.length
  cases hget : R[v]? with
  | none => trivial
  | some record =>
    simp only [hget] at execution credit
    dsimp only
    cases hcut : record.output.preparation.coordinator with
    | first outcome => trivial
    | live registers owned base outcome => trivial
    | invalidCollectionCutoff => trivial
    | dagger => trivial
    | collection oldPayload ledger clock cutoff outcome =>
      rw [hcut] at execution credit
      cases outcome <;> dsimp only at execution credit ⊢
      rename_i core consistent started hs instruction hi output hl clockData installed selected
      obtain ⟨hwR, holdSigma, htime, _⟩ := execution
      obtain ⟨hinstalled, _, _, hnewTime, _, _, _, hnewDown⟩ := credit
      -- A reached record rules out absent launch. The canonical launch is
      -- identified by the actual option equation, with the original inputs.
      cases hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
          rate source rewards C_star C_h with
      | none =>
        have hemptyR : R = [] := by
          simp only [R, ReferenceCompletePhysicalHistory.completeSuffixRecords,
            hlaunch, ↓reduceDIte]
        rw [hemptyR, List.getElem?_nil] at hget
        contradiction
      | some launched =>
        have hc := (ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
          rate source rewards C_star C_h).mp (by rw [hlaunch]; rfl)
        let initial := ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hc
        let active := ReferenceGeneratedFirstCutoffSurvival.generatedLaunchActive
          rate source rewards C_star C_h hc s rfl
        let J := ActualInitializationPhysicalStep.selectedRowIndex p source
        let count := p.T - s
        have span : s + count ≤ p.T := by
          have hbound := ReferenceCompletePhysicalHistory.physicalStart_le_T
            rate source rewards C_star C_h
          dsimp only [s, count]
          omega
        have hactual := ReferenceFirstLaunchNumericalCell.correctedLaunch_eq_some_launchState
          rate source rewards C_star C_h hc
        have hrun : R = (run initial source.1.2 J rewards s count span active).records :=
          ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
            rate source rewards C_star C_h initial hactual
        have hcount : R.length = count := by rw [hrun, run_record_count]
        have hvR : v < R.length := List.getElem?_eq_some_iff.mp hget |>.1
        have hvcount : v < count := by omega
        have hrecord := record_at initial source.1.2 J rewards s count span active v hvcount
        rw [← hrun, hget] at hrecord
        have hvSpan : s + v ≤ p.T :=
          le_trans (Nat.add_le_add_left (Nat.le_of_lt hvcount) s) span
        have hvSuccSpan : s + (v + 1) ≤ p.T :=
          le_trans (Nat.add_le_add_left (Nat.succ_le_of_lt hvcount) s) span
        have hrecordEq : record = ReferenceAssignmentPayloadChronology.actualRunRecordAt
            initial source.1.2 J rewards s v hvSuccSpan active := Option.some.inj hrecord
        have hinput : record.input.state =
            (run initial source.1.2 J rewards s v hvSpan active).finalState :=
          congrArg (fun value => value.input.state) hrecordEq
        have hrows : record.input.rows = source.1.2 :=
          congrArg (fun value => value.input.rows) hrecordEq
        have hselected : record.input.selected = J :=
          congrArg (fun value => value.input.selected) hrecordEq
        have hrewards : record.input.rewards = rewards :=
          congrArg (fun value => value.input.rewards) hrecordEq
        -- The collection window includes the cutoff and excludes this
        -- replacement. F's endpoint j=W.length is therefore exactly v.
        let b := w + 1
        let W := (R.drop b).takeWhile
          (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
        have hdrop : R.drop w = R[w]'hwR :: R.drop b := List.drop_eq_getElem_cons hwR
        have hCwin : Cwin = R[w]'hwR :: W := by
          dsimp only [Cwin, ReferenceCollectionPhaseHistory.collectionWindow]
          rw [hdrop]
          rfl
        have hvEq : v = b + W.length := by
          dsimp only [v]
          rw [hCwin, List.length_cons]
          dsimp only [b]
          omega
        have hgenerated :
            (ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun
              rate source rewards C_star C_h hc s rfl count span).records = R := by
          change (run initial source.1.2 J rewards s count span active).records = R
          exact hrun.symm
        have hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
            (ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun
              rate source rewards C_star C_h hc s rfl count span).records).length < count := by
          rw [hgenerated, ← hcount]
          exact hwR
        have hF :=
          ReferenceGeneratedFirstCollectionFollowerPrefix.actual_first_collection_follower_prefix_boundary
            rate source rewards C_star C_h hc s rfl count span hshort
        obtain ⟨r0, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
          _, hboundaries, _⟩ := hF
        have hboundary := hboundaries W.length
          (by simpa only [hgenerated] using (Nat.le_refl W.length))
        simp only [hgenerated] at hboundary
        have hboundaryCoord :
            (run initial source.1.2 J rewards s v hvSpan active).finalState.coordinator = .dagger ∨
            ∃ movingLedger movingSaved,
              (run initial source.1.2 J rewards s v hvSpan active).finalState.coordinator =
                .collection r0.payload movingLedger movingSaved := by
          have hb := hboundary.1
          change (run initial source.1.2 J rewards s (b + W.length)
            (by omega) active).finalState.coordinator = .dagger ∨
              ∃ movingLedger movingSaved,
                (run initial source.1.2 J rewards s (b + W.length)
                  (by omega) active).finalState.coordinator =
                    .collection r0.payload movingLedger movingSaved at hb
          simpa only [← hvEq] using hb
        have horigin := collection_origin record.input
        rw [← record.output.preparation.coordinator_eq, hcut] at horigin
        obtain ⟨saved, hincoming⟩ := horigin
        have hsamePayload : r0.payload = oldPayload := by
          rw [← hinput, hincoming] at hboundaryCoord
          rcases hboundaryCoord with hd | ⟨movingLedger, movingSaved, hsame⟩
          · cases hd
          · exact (ReferenceActivePhysicalStep.CoordinatorConfiguration.collection.inj hsame).1.symm
        -- The decoder chronology theorem starts at this same canonical
        -- launch, so its strict endpoint bound includes inherited batches.
        obtain ⟨downInitial, hdownLaunch, hdownSeed⟩ :=
          ReferenceCorrectedInitializationLaunch.correctedLaunch_downBatchSeed
            rate source rewards C_star C_h hc
        have hdownInitial : downInitial = initial :=
          Option.some.inj (hdownLaunch.symm.trans hactual)
        subst downInitial
        refine ⟨hinstalled, holdSigma, htime, hrows, hselected, hrewards, hnewTime, ?_⟩
        intro i
        obtain ⟨old, memory, hstate, hstatus, hdomain, hbuffer, hdecoder,
          _hS, _hdelta, _hbacklog, hmass, hcalendar, hkeys, hquant,
          hpair, hbefore, _hpending, _hcompleted, halt⟩ := hboundary.2 i
        have hstatePrefix : (run initial source.1.2 J rewards s v
            hvSpan active).finalState.followers i = .ordinary old memory := by
          change (run initial source.1.2 J rewards s (b + W.length)
            (by omega) active).finalState.followers i = .ordinary old memory at hstate
          simpa only [← hvEq] using hstate
        have hstateInput : record.input.state.followers i = .ordinary old memory := by
          rw [hinput]
          exact hstatePrefix
        have hbeforeInput : ∀ saved ∈ old.buffer,
            saved.calendarRound < record.input.time.val + 1 := by
          intro saved hmem
          have hb := hbefore saved hmem
          rw [htime, hvEq]
          simpa only [b, w, Nat.add_assoc] using hb
        have hmassInput : old.S + old.backlog ≤ w * D p := by
          exact hmass
        have haltInput : (old.lastDown = none ∧ old.S = 0 ∧ old.delta = 0 ∧ old.backlog = 0) ∨
            old.lastDown = some (oldPayload.downRecord i) := by
          simpa only [hsamePayload] using halt
        have hdown := ReferenceFollowerDecoderChronology.run_downBatch_spec
          initial source.1.2 J rewards s v (by omega) active hdownSeed i old memory hstatePrefix
        have hdownInput : ReferenceFollowerDecoderChronology.downBatchEndpoint
            old record.input.time.val := by rw [htime]; exact hdown.1
        have hstart := ActiveFollowerLifecycle.startRound_unoccupied
          rate.eta record.input.time old memory hdomain hstatus
        have hprepared : record.output.preparation.followers.followers i =
            DeclaredFollowerLocalRound.prepare rate i record.input.row
              (record.input.state.activations i) record.input.time (record.input.active i)
              (.ordinary old memory) := by
          rw [record.output.preparation.followers.followers_eq i]
          change DeclaredFollowerLocalRound.prepare rate i record.input.row
            (record.input.state.activations i) record.input.time (record.input.active i)
            (record.input.state.followers i) = _
          rw [hstateInput]
        have hconfiguration : (record.output.preparation.followers.followers i).configuration =
            .ordinary old memory := by
          rw [hprepared]
          exact prepare_configuration i record.input.row (record.input.state.activations i)
            record.input.time (record.input.active i) oldPayload old memory hdomain hstatus haltInput
        let actualOwn := ((record.output.preparation.followers.followers i).arm,
          record.output.preparation.feedback.observations
            (PublicDiscreteDraws.followerPlayer p.two_le_m i))
        obtain ⟨logged, hlogging, hlogBuffer, hlogStatus, hlogFailure, hlogValid⟩ :=
          ActiveFollowerLogging.checkedLogging_success_of_chronological
            i record.input.row (record.input.state.activations i) record.input.time
            actualOwn old hbuffer hbeforeInput hstatus
        have hframe := ActiveFollowerLogging.checkedLogging_success_frame
          i record.input.row (record.input.state.activations i) record.input.time
          actualOwn old logged hlogging
        obtain ⟨hlast, hS, hdelta, hbacklog, _hstatus, hbatch, _hfailure⟩ := hframe
        have hlogDomain : localStateDomainValid logged := by
          refine ⟨?_, hlogValid, ?_⟩
          · simpa only [ActiveFollowerLifecycle.serviceRegistersValid, hS, hdelta, hbacklog]
              using hdomain.1
          · simpa only [downDecoderStateValid, hbatch] using hdecoder
        have hlogEndpoint : ReferenceFollowerDecoderChronology.downBatchEndpoint
            logged record.input.time.val := by
          simpa only [ReferenceFollowerDecoderChronology.downBatchEndpoint, hbatch] using hdownInput
        have hlogBefore : ∀ saved ∈ logged.buffer,
            saved.calendarRound ≤ record.input.time.val + 1 ∧
              saved.calendarRound < record.input.time.val + 2 := by
          intro saved hmem
          rw [hlogBuffer] at hmem
          rcases List.mem_append.mp hmem with hOld | hNew
          · have hb := hbeforeInput saved hOld
            omega
          · have hb := (ActiveFollowerLogging.logAt_member_fields i record.input.row
              (record.input.state.activations i) record.input.time actualOwn saved hNew).1
            omega
        have hlogPair : logged.buffer.Pairwise
            (fun a b => a.calendarRound < b.calendarRound) := by
          rw [hlogBuffer, List.pairwise_append]
          refine ⟨hpair, ?_, ?_⟩
          · unfold logAt
            split <;> simp only [List.pairwise_singleton, List.Pairwise.nil]
          · intro a ha z hz
            have hb := hbeforeInput a ha
            have hzTime := (ActiveFollowerLogging.logAt_member_fields i record.input.row
              (record.input.state.activations i) record.input.time actualOwn z hz).1
            omega
        have hactualLogging := ReferenceActivePhysicalStep.recordFollower_logged
          record.output.preparation.coordinator.downView i record.input.row
          (record.input.state.activations i) record.input.time (record.input.active i)
          actualOwn.1 actualOwn.2 old logged hstatus hlogging
        have halign := record.output.preparation.follower_alignment i
        -- Diagnostic fields survive every subsequent tail constructor,
        -- including an error in DOWN, release, or FINISH. This projection
        -- does not require an ordinary output or any tail-success premise.
        have htail : record.output.followers i =
            record.output.preparation.observeFollower i := by
          rw [record.output_eq]
          rfl
        have hdiagnostic : (record.output.followers i).downInput = some logged := by
          rw [htail]
          unfold ReferenceActivePhysicalStep.PreparedRound.observeFollower
            ReferenceActivePhysicalStep.finishFollower
          simp only [hconfiguration]
          have hloggedCall : (ReferenceActivePhysicalStep.recordFollower
              record.output.preparation.coordinator.downView
              (record.output.preparation.followers.followers i).follower
              (record.output.preparation.followers.followers i).row
              (record.output.preparation.followers.followers i).activation
              (record.output.preparation.followers.followers i).time
              (record.output.preparation.followers.followers i).active
              (record.output.preparation.followers.followers i).arm actualOwn.2 old).downInput =
                some logged := by
            simpa only [halign.1, halign.2.1, halign.2.2.1, halign.2.2.2]
              using hactualLogging.1
          split
          · exact hloggedCall
          · split <;> exact hloggedCall
        rw [hcut] at hactualLogging
        have harm : record.output.preparation.arms.actions
            (PublicDiscreteDraws.followerPlayer p.two_le_m i) =
              (record.output.preparation.followers.followers i).arm := by
          rw [record.output.preparation.action_follower i, hstateInput, ← hprepared]
        obtain ⟨hnewSigma, _hnewQueue, hnewMass, hnewBound⟩ := hnewDown i
        have hnewSigmaInput : (installed.registers.payload.downRecord i).val.sigma =
            record.input.time.val + 1 := by rw [htime]; exact hnewSigma
        have hnewBoundInput : (installed.registers.payload.downRecord i).val.q ≤
            record.input.time.val * D p := by
          simpa only [hnewSigmaInput, Nat.add_sub_cancel] using hnewBound
        refine ⟨old, memory, logged,
          hstateInput,
          hstatus,
          hdomain,
          hbuffer,
          hdecoder,
          hdownInput,
          hmassInput,
          hcalendar,
          hkeys,
          hquant,
          hpair,
          hbeforeInput,
          haltInput,
          hstart,
          hprepared,
          hconfiguration,
          halign.1,
          halign.2.1,
          halign.2.2.1,
          halign.2.2.2,
          harm,
          hlogging,
          hlogBuffer,
          hlogValid,
          hlogDomain,
          hlogStatus.trans hstatus,
          hlast,
          hS,
          hdelta,
          hbacklog,
          hbatch,
          hlogFailure,
          hlogEndpoint,
          hlogValid.1,
          hlogValid.2.1,
          hlogValid.2.2,
          hlogPair,
          hlogBefore,
          ?_,
          hactualLogging.1,
          hdiagnostic,
          ?_,
          ?_,
          ActiveFollowerLogging.loggingTestsPass_iff_source_mask
            i record.input.row (record.input.state.activations i) record.input.time actualOwn,
          hnewSigmaInput,
          hnewBoundInput,
          hnewMass⟩
        · simpa only [hS, hbacklog] using hmassInput
        · intro htests
          rw [hlogBuffer, ActiveFollowerLogging.logAt_eq_singleton_of_tests
            i record.input.row (record.input.state.activations i) record.input.time actualOwn htests]
        · intro htests
          rw [hlogBuffer, ActiveFollowerLogging.logAt_eq_nil_of_not_tests
            i record.input.row (record.input.state.activations i) record.input.time actualOwn htests,
            List.append_nil]

end Bandits.Support.ReferenceFirstReplacementFollowerLoggingSeed
end
