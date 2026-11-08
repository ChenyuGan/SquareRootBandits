/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCompleteInstallationCalendarInitializationInduction

import Lean.Elab.Tactic.Omega

/-!
# Assigned-arm replay from an actual later installation

For an actual later installation selected by an accepted UP, initialize the
assigned arm from its original-index calendar prefix and apply the accepted-UP
continuation at that same literal raw calendar word. This retains the native
DOWN replay and the actual collection continuation without asserting a common
calendar alignment after the installation.

Source evidence: `appendix_a_local_protocol.tex:28-64`,
`06_interruptions.tex:40-100,192-233,246-299`, and
`04_slow_fast_learner.tex:157-188`, under `sources/zip4/manuscript/`.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ReferenceCompleteInstallationAssignedOriginReplay

open Bandits.Support
open ConstructorDimensions ReferenceActivePhysicalStep ReferenceActivePhysicalHorizon
open ReferenceCollectionSegmentExtraction

variable {p : ConstructorDimensions.Parameters}

/-- Apply the original-prefix replay to the actual assigned arm of an actual
later installation selected by this accepted UP. The original-index calendar
initialization supplies both numerical inputs; the returned assigned replay
retains its native DOWN word, accepted reply, and every known collection
continuation prefix. The result makes no whole-calendar alignment claim. -/
theorem internal_complete_later_installation_assigned_origin_replay
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (i : Fin (p.m - 1)) (reply : ReferenceCollectionPhaseHistory.UpRecord p rate)
    (hacc : ReferenceCollectionPhaseHistory.AcceptedUp
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val].input i reply)
    (b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (hb : ReferenceCollectionPhaseHistory.laterChosen
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[b.val].input = true)
    (hselector : reply.val.sigma =
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[b.val].input.time.val + 1) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
    ∃ P0 : List (RecordedQueueRun.RoundInput p.K),
      P0.length = b.val ∧
      (R.take b.val).map (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate) =
        P0.map some ∧
      (∀ h : ℕ, h ≤ b.val →
        ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
          rate rewards C_star C_h
          (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h + h)
          source = some (P0.take h)) ∧
      ReferenceFirstReplacementCalendarInitialization.initializes_calendar rate P0 R[b.val] ∧
      ∃ (payload : AssignmentStartPayload.Input p rate.eta)
        (base : Fin (p.m - 1) → ℕ) (E : List (Bool × ℕ)),
        ReferenceAssignmentPayloadPersistence.InstallationBirth R[b.val] payload ∧
        (match (R[b.val]'b.isLt).output.preparation.coordinator with
        | .first (.chosen installed _) => some installed.followerBaseScore
        | .collection _ _ _ _ (.laterChosen _ _ _ _ _ _ _ _ _ installed _) =>
            some installed.retainedBaseScore
        | _ => none) = some base ∧
        E = ReferenceFirstCorrectedNextCalendarWordJoin.rawCalendar rate
          (payload.assignment.assigned i) P0 ∧
        (∀ arm : Fin p.K,
          payload.queues arm =
            (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay
              rate P0 arm P0.length).2) ∧
        (∀ follower : Fin (p.m - 1),
          base follower =
            (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate
              P0 (payload.assignment.assigned follower) P0.length).1 ∧
          (payload.downRecord follower).val.q =
            (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate
              P0 (payload.assignment.assigned follower) P0.length).2) ∧
        ReferenceFirstCorrectedNextAssignedCalendarReplay.initialized_assigned_replay
          rewards C_star C_h source k i reply b payload E := by
  classical
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
  obtain ⟨P0, hP0len, hP0slots, hP0prefix, hinit⟩ :=
    Bandits.Support.ReferenceCompleteInstallationCalendarInitializationInduction.internal_complete_later_installation_calendar_initialization
      rate rewards C_star C_h source b hb
  have hinitProof := hinit
  rcases hinit with ⟨initPayload, ledger, saved, cutoff, hstate, hpending,
    hcutoff, core, startedInit, hstartInit, instruction, hassignmentInit,
    hinstructionTime, consistent, output, hlocal, clockData, installation,
    selected, hinstallation, hsuccess, hdispatch, hprepared, hpayloadEq,
    hsigmaInit, hassignmentVector, hreconstruction, hallArms, hretained,
    hcomplement, hcorrected, hrenewal⟩
  let payload := installation.registers.payload
  let base := installation.retainedBaseScore
  let E := ReferenceFirstCorrectedNextCalendarWordJoin.rawCalendar rate
    (payload.assignment.assigned i) P0
  have hpayloadTime : payload.sigma = (R[b.val]'b.isLt).input.time := by
    change installation.registers.payload.sigma = (R[b.val]'b.isLt).input.time
    exact hsigmaInit
  have hinstalledBirth :
      ReferenceAssignmentPayloadPersistence.InstallationBirth
        (R[b.val]'b.isLt) payload := by
    unfold ReferenceAssignmentPayloadPersistence.InstallationBirth
    rw [hprepared]
    exact ⟨rfl, congrArg Fin.val hpayloadTime⟩
  have hbase :
      (match (R[b.val]'b.isLt).output.preparation.coordinator with
      | .first (.chosen installed _) => some installed.followerBaseScore
      | .collection _ _ _ _ (.laterChosen _ _ _ _ _ _ _ _ _ installed _) =>
          some installed.retainedBaseScore
      | _ => none) = some base := by
    rw [hprepared]
  have hcalendar (arm : Fin p.K) :
      ReferenceFirstReplacementCalendarInitialization.calendarReplay
          rate arm P0 P0.length =
        ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay
          rate P0 arm P0.length := by
    simp [ReferenceFirstReplacementCalendarInitialization.calendarReplay,
      ReferenceFirstReplacementCalendarInitialization.rawCalendar,
      ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay,
      ReferenceFirstCorrectedNextCalendarWordJoin.rawCalendar]
  have hselectorPayload : reply.val.sigma = payload.sigma.val + 1 := by
    rw [hpayloadTime]
    exact hselector
  have hqueue : (payload.downRecord i).val.q =
      (QueueReplay.replay (4 * rate.n) (0, 0) E).2 := by
    have hq := (hretained i).2.2
    change (installation.registers.payload.downRecord i).val.q =
      (ReferenceFirstReplacementCalendarInitialization.calendarReplay
        rate (payload.assignment.assigned i) P0 P0.length).2 at hq
    calc
      (payload.downRecord i).val.q =
          (ReferenceFirstReplacementCalendarInitialization.calendarReplay
            rate (payload.assignment.assigned i) P0 P0.length).2 := hq
      _ = (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay
          rate P0 (payload.assignment.assigned i) P0.length).2 :=
        congrArg Prod.snd (hcalendar (payload.assignment.assigned i))
      _ = (QueueReplay.replay (4 * rate.n) (0, 0) E).2 := by
        simp [E, ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay,
          List.take_length]
  have hscore : base i =
      (QueueReplay.replay (4 * rate.n) (0, 0) E).1 := by
    have hs := (hretained i).2.1
    change installation.retainedBaseScore i =
      (ReferenceFirstReplacementCalendarInitialization.calendarReplay
        rate (payload.assignment.assigned i) P0 P0.length).1 at hs
    calc
      base i =
          (ReferenceFirstReplacementCalendarInitialization.calendarReplay
            rate (payload.assignment.assigned i) P0 P0.length).1 := hs
      _ = (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay
          rate P0 (payload.assignment.assigned i) P0.length).1 :=
        congrArg Prod.fst (hcalendar (payload.assignment.assigned i))
      _ = (QueueReplay.replay (4 * rate.n) (0, 0) E).1 := by
        simp [E, ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay,
          List.take_length]
  have hqueues : ∀ arm : Fin p.K,
      payload.queues arm =
        (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay
          rate P0 arm P0.length).2 := by
    intro arm
    exact ((hallArms arm).2.2.2.1).trans
      (congrArg Prod.snd (hcalendar arm))
  have hretainedOutput : ∀ follower : Fin (p.m - 1),
      base follower =
        (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate
          P0 (payload.assignment.assigned follower) P0.length).1 ∧
      (payload.downRecord follower).val.q =
        (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate
          P0 (payload.assignment.assigned follower) P0.length).2 := by
    intro follower
    refine ⟨?_, ?_⟩
    · exact ((hretained follower).2.1).trans
        (congrArg Prod.fst (hcalendar (payload.assignment.assigned follower)))
    · exact ((hretained follower).2.2).trans
        (congrArg Prod.snd (hcalendar (payload.assignment.assigned follower)))

  have happlication :
      ReferenceFirstCorrectedNextAssignedCalendarReplay.initialized_assigned_replay
        rewards C_star C_h source k i reply b payload E := by
    unfold ReferenceFirstCorrectedNextAssignedCalendarReplay.initialized_assigned_replay
    intro R'
    have hR' : R' = R := rfl
    subst R'
    obtain ⟨c, bN, j, logged, after, cut, raw, scan, registers, lastService,
      hc, hbj, hjk, hbirth, hretainedDown, hlogged, hdown, houtcome,
      hscan, hchecked, hq, hUsigma, hdpos, hdle, htimes, hLlen, v, ho,
      hselected, hpreparedLive, hQ, hEd, hAlen, hAenabled, hregisters,
      hlastService, seg, done, c0, I, hok, hoR, hn, hsegment, hentry,
      hsegContext, hc0, hP0, hI, hIchecked, hIarm, hIsigma, hIcutoff, hIbase,
      hbaseProv, hrecord, hdone, hcontext, haccepted, hparsed, hsender,
      hacceptedEndpoint, recording, started, decoded, bank, hrecording,
      hstart, hreceive, hdecode, hfinish, hassignment, hunknownStarted,
      hgammaStarted, hgammaDecoded, hfinishIncrement, hnextActual,
      hcontinuation⟩ :=
      ReferenceCorrectedSuccessorAssignedNumericalStep.internal_complete_accepted_up_original_prefix_replay_of_initial_replay
        rewards C_star C_h source k i reply hacc
    have htimeBirth := ReferenceAssignmentPayloadChronology.installationBirth_time_eq
      (R[bN.val]'bN.isLt) c.payload hbirth
    have htimeInstalled := ReferenceAssignmentPayloadChronology.installationBirth_time_eq
      (R[b.val]'b.isLt) payload hinstalledBirth
    have hpayloadSigma : c.payload.sigma.val = payload.sigma.val :=
      Nat.add_right_cancel (hUsigma.symm.trans hselectorPayload)
    have htime : (R[bN.val]'bN.isLt).input.time.val =
        (R[b.val]'b.isLt).input.time.val :=
      htimeBirth.symm.trans (hpayloadSigma.trans htimeInstalled)
    have hnodup : (R.map (fun record => record.input.time.val)).Nodup := by
      rw [ReferenceCompletePhysicalHistory.completeSuffixRecords_time_values]
      exact List.nodup_range'
    have hindex : bN = b := by
      apply Fin.ext
      apply (hnodup.getElem_inj_iff
        (hi := by simpa only [List.length_map] using bN.isLt)
        (hj := by simpa only [List.length_map] using b.isLt)).mp
      simpa only [List.getElem_map] using htime
    subst bN
    have hpayload : c.payload = payload :=
      ReferenceAssignmentPayloadChronology.installationBirth_payload_unique
        (R[b.val]'b.isLt) c.payload payload hbirth hinstalledBirth
    have hbaseRead : (match (R[b.val]'b.isLt).output.preparation.coordinator with
        | .first (.chosen installation _) => some installation.followerBaseScore
        | .collection _ _ _ _ (.laterChosen _ _ _ _ _ _ _ _ _ installation _) =>
            some installation.retainedBaseScore
        | _ => none) = some c.preLedger.baseScore := by
      have hbaseProv' : c.preLedger.baseScore = installation.retainedBaseScore := by
        simpa only [hprepared] using hbaseProv
      rw [hprepared]
      exact congrArg some hbaseProv'.symm
    have hbaseEq : c.preLedger.baseScore = base := by
      exact Option.some.inj (hbaseRead.symm.trans hbase)
    have hqueueE : (c.payload.downRecord i).val.q =
        (QueueReplay.replay (4 * rate.n) (0, 0) E).2 := by
      rw [hpayload]
      exact hqueue
    have hscoreE : I.base i =
        (QueueReplay.replay (4 * rate.n) (0, 0) E).1 := by
      rw [hIbase, hbaseEq]
      exact hscore
    have hinitialized := hcontinuation E hqueueE hscoreE
    refine ⟨c, b, j, logged, after, cut, raw, scan, registers, lastService,
      rfl, hpayload, hc, hbj, hjk, hbirth, hretainedDown, hlogged, hdown,
      houtcome, hscan, hchecked, hq, hUsigma, hdpos, hdle, htimes, hLlen,
      v, ho, hselected, hpreparedLive, hQ, hEd, hAlen, hAenabled,
      hregisters, hlastService, seg, done, c0, I, hok, hoR, hn, hsegment,
      hentry, hsegContext, hc0, hP0, hI, hIchecked, hIarm, hIsigma, hIcutoff,
      hIbase, hbaseProv, hrecord, hdone, hcontext, haccepted, hparsed,
      hsender, hacceptedEndpoint, recording, started, decoded, bank,
      hrecording, hstart, hreceive, hdecode, hfinish, hassignment,
      hunknownStarted, hgammaStarted, hgammaDecoded, hfinishIncrement,
      hnextActual, hqueueE, hscoreE, hinitialized⟩

  exact ⟨P0, hP0len, hP0slots, hP0prefix, hinitProof, payload, base, E,
    hinstalledBirth, hbase, rfl, hqueues, hretainedOutput, happlication⟩

end Bandits.Support.ReferenceCompleteInstallationAssignedOriginReplay

end
