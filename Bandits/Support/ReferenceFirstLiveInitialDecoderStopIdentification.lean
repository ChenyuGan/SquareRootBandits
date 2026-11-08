/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceOriginalFirstBadStrictPrefix

/-!
# Initial first-window decoder stop identification

On the original whole source, this module identifies the decoder-only stop
test on each record of the actual first-live window. Numerical overflow is a
separate stop component and is not included here.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions
open scoped Classical

namespace Bandits.Support.ReferenceFirstLiveInitialDecoderStopIdentification

variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ)
  (z : BootstrapPrivateRoundStreams.SourceInput p)

private theorem takeWhile_take_eq {α : Type*} (pred : α → Bool) (xs : List α)
    (n : ℕ) (hn : n ≤ (xs.takeWhile pred).length) :
    xs.take n = (xs.takeWhile pred).take n := by
  induction n generalizing xs with
  | zero => simp
  | succ n ih =>
      cases xs with
      | nil => simp at hn
      | cons x xs =>
          have hp : pred x = true := by
            by_contra h
            have hf : pred x = false := Bool.eq_false_of_not_eq_true h
            simp [List.takeWhile, hf] at hn
          have hn' : n ≤ (xs.takeWhile pred).length := by
            simpa [List.takeWhile, hp] using hn
          simp only [List.take_succ_cons]
          simp [List.takeWhile, hp, ih xs hn']

private theorem list_get_congr_of_eq {α : Type*} {xs ys : List α}
    (h : xs = ys) (i : Fin xs.length) (j : Fin ys.length)
    (hv : i.val = j.val) : xs.get i = ys.get j := by
  let e := congrArg List.length h
  have hi : Fin.cast e i = j := by
    apply Fin.ext
    exact hv
  calc
    xs.get i = ys.get (Fin.cast e i) := by
      cases h
      rfl
    _ = ys.get j := congrArg ys.get hi

private theorem actual_positive_origin
    (i : Fin (p.m - 1))
    (records : List (ReferenceFirstLiveDownCompletionReadout.Record (rate := rate)))
    (e : AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p)) :
    e ∈ ReferenceFollowerDownDecoderReplay.actualDownPositives i records ↔
      ∃ r ∈ records, ∃ call : ReferenceFollowerDownDecoderReplay.Call p,
        ReferenceFollowerDownDecoderReplay.actualDownCall i r = some call ∧
        e ∈ AffineBatchDecoder.positiveAt p
          (ActiveFollowerDownAcceptance.currentInputExtension p call.2) call.1 := by
  simp only [ReferenceFollowerDownDecoderReplay.actualDownPositives,
    ReferenceFollowerDownDecoderReplay.positiveCallEntries,
    ReferenceFollowerDownDecoderReplay.actualDownCalls,
    List.mem_flatMap, List.mem_filterMap]
  constructor
  · rintro ⟨call, ⟨r, hr, hcall⟩, he⟩
    exact ⟨r, hr, call, hcall, he⟩
  · rintro ⟨r, hr, call, hcall, he⟩
    exact ⟨call, ⟨r, hr, hcall⟩, he⟩

private theorem downSelected_of_selectedChannel
    (row : CompletePublicTable.CompleteRow p) (time : Fin p.T)
    (i : Fin (p.m - 1))
    (h : ReferenceSelectedAffinePairLaw.selectedChannel p
      (row.2 time).1 = some (0, i)) :
    ActiveFollowerDownAcceptance.downSelected p i row time := by
  have hdown : PublicDiscreteDraws.slotDraw (row.2 time).1 = PublicDiscreteDraws.downSlot := by
    by_contra hn
    unfold ReferenceSelectedAffinePairLaw.selectedChannel
      ReferenceSelectedAffinePairLaw.channelFromDraws at h
    simp only [ite_eq_right hn] at h
    by_cases hup : PublicDiscreteDraws.slotDraw (row.2 time).1 = PublicDiscreteDraws.upSlot
    · simp only [ite_eq_left hup] at h
      have hf := congrArg Prod.fst (Option.some.inj h)
      cases hf
    · simp only [ite_eq_right hup] at h
      cases h
  rw [ReferenceSelectedAffinePairLaw.selectedChannel_of_down p (row.2 time).1 hdown] at h
  exact ⟨hdown, (Prod.mk.inj (Option.some.inj h)).2⟩

private theorem crossing_of_window_index
    (k : Fin (ReferenceFirstLiveSourceStoppedHandoverEndpoint.window
      rate rewards C_star C_h z).length) :
    (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true := by
  by_contra hnot
  let I := ReferenceInitializationRun.output
    (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)
  have hnone : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate z rewards C_star C_h = none := by
    cases hc : ReferenceCorrectedInitializationLaunch.correctedLaunch
        rate z rewards C_star C_h with
    | none => rfl
    | some active =>
        have hsome : (ReferenceCorrectedInitializationLaunch.correctedLaunch
            rate z rewards C_star C_h).isSome = true := by rw [hc]; rfl
        have hcross' := (ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
          rate z rewards C_star C_h).mp hsome
        exact False.elim (hnot (by simpa [I] using hcross'))
  have hwindow : ReferenceFirstLiveSourceStoppedHandoverEndpoint.window
      rate rewards C_star C_h z = [] :=
    ReferenceFirstLiveSourceStoppedHandoverEndpoint.window_eq_nil_of_no_launch
      rate rewards C_star C_h z hnone
  have hk := k.isLt
  simp [hwindow] at hk

private theorem actual_record_input_fields
    (t : Fin p.T) (r : ReferenceFirstLiveDownCompletionReadout.Record (rate := rate))
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some r)
    (hs : ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h ≤ t.val)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true) :
    r.input.rows = z.1.2 ∧
      r.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p z ∧
      r.input.time = t ∧ r.input.rewards = rewards := by
  have hlaunch := ReferenceLocalReleaseGateChronology.sourceSeed_launch
    rate z rewards C_star C_h hc
  have hactual := ReferenceSourcePrefixHistoryFiltration.actualRecord_on_launch
    rate rewards C_star C_h t z
    (ReferenceLocalReleaseGateChronology.sourceSeed rate z rewards C_star C_h hc)
    hlaunch hs
  have heq := Option.some.inj (hr.symm.trans hactual)
  subst r
  refine ⟨rfl, rfl, ?_, rfl⟩
  apply Fin.ext
  dsimp only [ReferenceAssignmentPayloadChronology.actualRunRecordAt,
    ReferenceActivePhysicalHorizon.roundInputAt]
  omega

private theorem first_window_fixed_up_false
    (k : Fin (ReferenceFirstLiveSourceStoppedHandoverEndpoint.window
      rate rewards C_star C_h z).length) :
    ¬ ReferenceCollectionUpFailureReadoutV2.fixedAwaitedUpFailureAt
      rate rewards C_star C_h z
      ((ReferenceFirstLiveSourceStoppedHandoverEndpoint.window
        rate rewards C_star C_h z).get k).input.time := by
  classical
  let W := ReferenceFirstLiveSourceStoppedHandoverEndpoint.window rate rewards C_star C_h z
  let r := W.get k
  let t := r.input.time
  let I := ReferenceInitializationRun.output
    (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)
  let s := ReferenceInitializationRun.elapsed p I.completed
  let count := p.T - s
  have hcross : I.crossing.isSome = true := by
    simpa only [I] using crossing_of_window_index rate rewards C_star C_h z k
  have hs : s ≤ p.T := by
    dsimp [s]
    exact ReferenceInitializationRun.elapsed_le_T p I.completed
  have hspan : s + count ≤ p.T := by dsimp [count]; omega
  let R := ReferenceLocalReleaseGateChronology.sourceRun rate z rewards C_star C_h
    hcross s count rfl hspan
  have hrun : R.records =
      ReferenceFirstLiveSourceStoppedHandoverEndpoint.completeRecords rate rewards C_star C_h z := by
    have hlaunch := ReferenceLocalReleaseGateChronology.sourceSeed_launch
      rate z rewards C_star C_h hcross
    simpa [R, count, ReferenceLocalReleaseGateChronology.sourceRun,
      ReferenceFirstLiveSourceStoppedHandoverEndpoint.completeRecords,
      ReferenceFirstLiveSourceStoppedReleaseEndpoint.completeRecords,
      ReferenceCompletePhysicalHistory.physicalStart,
      ReferenceCompletePhysicalHistory.generatedBoundary,
      ReferenceCompletePhysicalHistory.generatedInput] using
      (ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
        rate z rewards C_star C_h
        (ReferenceLocalReleaseGateChronology.sourceSeed rate z rewards C_star C_h hcross)
        hlaunch).symm
  have hW : ReferenceFirstLiveConfirmationHistory.firstLiveWindow R.records = W := by
    dsimp [W, ReferenceFirstLiveSourceStoppedHandoverEndpoint.window]
    rw [← hrun]
  let kR : Fin (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R.records).length :=
    ⟨k.val, by rw [hW]; exact k.isLt⟩
  have hup := ReferenceFirstLiveReleaseDecoderSilence.first_live_up_diagnostic_eq_none
    z rewards C_star C_h count hspan hcross
  have hupK : (W[k.val]).output.coordinator.up = none := by
    have hgetFin := list_get_congr_of_eq hW kR k rfl
    have hget :
        (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R.records)[kR.val] = W[k.val] := by
      simpa only [List.get_eq_getElem] using hgetFin
    have htmp := hup kR
    rw [hget] at htmp
    exact htmp
  have hrecord := ReferenceFirstLiveSourceStoppedHandoverEndpoint.source_window_record_calendar
    rate rewards C_star C_h z k
  have hrecordReal : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t z = some r := by
    simpa only [r, W, t, List.get_eq_getElem] using hrecord.2
  intro hbad
  have hliteral :=
    (ReferenceLiteralAwaitedAmbiguityRowObservation.literalUpAmbiguityAt_iff_fixedAwaitedUpFailureAt
      rate rewards C_star C_h z t).2 hbad
  rcases hliteral with ⟨ru, i, U, B, a, hru, hcompleted, _, _, _, _, _⟩
  have hruTime : ru.input.time = t := by
    have heq := Option.some.inj (hru.symm.trans hrecordReal)
    exact congrArg (fun q => q.input.time) heq
  have hdiag : ru.output.coordinator.up = none := by
    have hruEq : ru = r := Option.some.inj (hru.symm.trans hrecordReal)
    rw [hruEq]
    simpa only [r, List.get_eq_getElem] using hupK
  rcases hcompleted with ⟨d, hd, _⟩
  rw [hdiag] at hd
  cases hd

private theorem first_window_local_ambiguous_iff_global_down
    (k : Fin (ReferenceFirstLiveSourceStoppedHandoverEndpoint.window
      rate rewards C_star C_h z).length) :
    let W := ReferenceFirstLiveSourceStoppedHandoverEndpoint.window rate rewards C_star C_h z
    let r := W.get k
    (∃ i : Fin (p.m - 1),
      ReferenceFirstLiveDownCompletionReadout.completedAmbiguousAfterStart
        (ReferenceFirstLiveSourceStoppedReleaseEndpoint.physicalStart
          rate rewards C_star C_h z) r i) ↔
      ReferenceFirstCollectionAwaitedDownFailureReadout.fixedAwaitedDownFailureAt
        rate rewards C_star C_h z r.input.time := by
  intro W r
  classical
  let t := r.input.time
  let I := ReferenceInitializationRun.output
    (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)
  let s := ReferenceInitializationRun.elapsed p I.completed
  let count := p.T - s
  have hcross : I.crossing.isSome = true := by
    simpa only [I] using crossing_of_window_index rate rewards C_star C_h z k
  have hs : s ≤ p.T := by
    dsimp [s]
    exact ReferenceInitializationRun.elapsed_le_T p I.completed
  have hspan : s + count ≤ p.T := by dsimp [count]; omega
  have hElapsed : ReferenceInitializationRun.elapsed p I.completed = s := rfl
  let R := ReferenceLocalReleaseGateChronology.sourceRun rate z rewards C_star C_h
    hcross (ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed)
    count rfl hspan
  have hlaunch := ReferenceLocalReleaseGateChronology.sourceSeed_launch
    rate z rewards C_star C_h hcross
  have hrun : R.records =
      ReferenceFirstLiveSourceStoppedHandoverEndpoint.completeRecords
        rate rewards C_star C_h z := by
    simpa [R, count, ReferenceLocalReleaseGateChronology.sourceRun,
      ReferenceFirstLiveSourceStoppedHandoverEndpoint.completeRecords,
      ReferenceFirstLiveSourceStoppedReleaseEndpoint.completeRecords,
      ReferenceCompletePhysicalHistory.physicalStart,
      ReferenceCompletePhysicalHistory.generatedBoundary,
      ReferenceCompletePhysicalHistory.generatedInput] using
      (ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
        rate z rewards C_star C_h
        (ReferenceLocalReleaseGateChronology.sourceSeed rate z rewards C_star C_h hcross)
        hlaunch).symm
  have hsStart : ReferenceFirstLiveSourceStoppedReleaseEndpoint.physicalStart
      rate rewards C_star C_h z = s := by
    dsimp [s, ReferenceFirstLiveSourceStoppedReleaseEndpoint.physicalStart,
      ReferenceCompletePhysicalHistory.physicalStart,
      ReferenceCompletePhysicalHistory.generatedBoundary,
      ReferenceCompletePhysicalHistory.generatedInput]
  have hwindow : ReferenceFirstLiveConfirmationHistory.firstLiveWindow R.records = W := by
    dsimp [W, ReferenceFirstLiveSourceStoppedHandoverEndpoint.window]
    rw [← hrun]
  have htake : R.records.take (k.val + 1) = W.take (k.val + 1) := by
    rw [← hwindow]
    exact takeWhile_take_eq
      (fun q => !ReferenceCollectionPhaseHistory.cutoffChosen q.input)
      R.records (k.val + 1) (by
        have hk : k.val + 1 ≤ W.length := Nat.succ_le_of_lt k.isLt
        have hk' : k.val + 1 ≤
            (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R.records).length := by
          rw [hwindow]
          exact hk
        simpa only [ReferenceFirstLiveConfirmationHistory.firstLiveWindow] using hk')
  have hcalendar := ReferenceFirstLiveSourceStoppedHandoverEndpoint.source_window_record_calendar
    rate rewards C_star C_h z k
  have hrecord : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t z = some r := by
    simpa only [W, r, t, List.get_eq_getElem] using hcalendar.2
  constructor
  · rintro ⟨i, hamb⟩
    have hamb' :
        ReferenceFirstLiveDownCompletionReadout.completedAmbiguousAfterStart s
          (W[k.val]) i := by
      simpa only [W, r, List.get_eq_getElem, hsStart] using hamb
    let kR : Fin (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R.records).length :=
      ⟨k.val, by rw [hwindow]; exact k.isLt⟩
    have hambForAPI :
        ReferenceFirstLiveDownCompletionReadout.completedAmbiguousAfterStart s
          (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R.records)[kR.val] i := by
      have hgetFin := list_get_congr_of_eq hwindow kR k rfl
      have hget :
          (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R.records)[kR.val] = W[k.val] := by
        simpa only [List.get_eq_getElem] using hgetFin
      rw [hget]
      exact hamb'
    obtain ⟨M, birth, B, hsigma, hbirth, hbirthtime, hborn, hfirst,
      hB, horig, hsolves, hmulti, hcalls⟩ :=
      (ReferenceFirstLiveDownCompletionReadout.actual_first_live_completedAmbiguousAfterStart_iff
        rate z rewards C_star C_h count hcross hspan kR i).mp hambForAPI
    have htime : t.val = s + k.val := by
      simpa only [t, r, W, List.get_eq_getElem, hsStart] using hcalendar.1
    let a : Fin p.T := ⟨s, by omega⟩
    let hword : AffineChannelLaw.Word (AffineBatchDecoder.width p) :=
      CoordinatorLocalArmChoice.storedDownFlatWord M i
    have hAwaitPrefix := hcalls
    have hfirstRecord :
        (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R.records)[kR.val] = r := by
      have hgetFin := list_get_congr_of_eq hwindow kR k rfl
      have hget :
          (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R.records)[kR.val] = W[k.val] := by
        simpa only [List.get_eq_getElem] using hgetFin
      calc
        (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R.records)[kR.val] = W[k.val] := hget
        _ = r := by simp only [r, List.get_eq_getElem]
    refine ⟨r, i, hword, B, a, hrecord, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [R, hfirstRecord] using hB
    · dsimp [a]
      omega
    · exact (ReferenceFirstLiveDownCompletionReadout.multipleSolutions_iff B).mpr hmulti
    · intro e he
      obtain ⟨Blocal, hBlocal, hstamp, hmultiLocal⟩ := hamb'
      have horig' := ReferenceFirstLiveDownCompletionReadout.actual_first_live_batch_origins
        rate z rewards C_star C_h count hcross hspan kR i B hB e he
      have hBroot : ReferenceFirstLiveDownCompletionReadout.completedDownBatch r i = some B := by
        simpa only [R, hfirstRecord] using hB
      have hBmatch : B = Blocal := Option.some.inj (hBroot.symm.trans hBlocal)
      have hstampRoot : ∀ e ∈ B, s ≤ e.time.val := by
        intro e he
        rw [hBmatch] at he
        exact hstamp e he
      have hepositive : e ∈ ReferenceFollowerDownDecoderReplay.actualDownPositives i
          (R.records.take (k.val + 1)) := by
        simpa only [kR] using horig'.mp (hstampRoot e he)
      obtain ⟨q, hq, call, hcall, hentry⟩ :=
        (actual_positive_origin rate i (R.records.take (k.val + 1)) e).mp hepositive
      have hqwindow : q ∈ W.take (k.val + 1) := by rw [← htake]; exact hq
      obtain ⟨j, hj, hqj⟩ := List.mem_take_iff_getElem.mp hqwindow
      have hjk : j ≤ k.val := by omega
      have hjFin : j < W.length := by omega
      have qeq : q = W[j] := hqj.symm
      let l : Fin W.length := ⟨j, hjFin⟩
      have hcalJ := ReferenceFirstLiveSourceStoppedHandoverEndpoint.source_window_record_calendar
        rate rewards C_star C_h z l
      have hrecJ : ReferenceSourcePrefixHistoryFiltration.actualRecord
          rate rewards C_star C_h (W[j]).input.time z = some (W[j]) := by
        simpa only [l, List.get_eq_getElem] using hcalJ.2
      have hcallFields := ReferenceDownCompletedAmbiguityMeasurability.actualDownCall_fields
        q i call hcall
      have heligible : AffineBatchDecoder.eligible call.2 := by
        unfold AffineBatchDecoder.positiveAt at hentry
        split at hentry
        · assumption
        · simp at hentry
      have hentryTime := by
        unfold AffineBatchDecoder.positiveAt at hentry
        split at hentry
        · have heq := List.mem_singleton.mp hentry
          have heTime : e.time = call.1 := congrArg AffineBatchDecoder.Entry.time heq
          exact heTime.trans hcallFields.1
        · cases hentry
      have hrecordEntry : ReferenceSourcePrefixHistoryFiltration.actualRecord
          rate rewards C_star C_h e.time z = some q := by
        rw [hentryTime, qeq]
        exact hrecJ
      have hrecordEntry' :
          ReferenceFirstCollectionAwaitedDownFailureReadout.actualRecord
            rate rewards C_star C_h e.time z = some q := by
        simpa only [ReferenceFirstCollectionAwaitedDownFailureReadout.actualRecord] using hrecordEntry
      have hqtime : q.input.time.val = s + j := by
        simpa only [qeq, l, List.get_eq_getElem, hsStart] using hcalJ.1
      have heqTime : e.time.val = s + j := by
        have hcallTime : e.time = q.input.time := hentryTime
        rw [hcallTime]
        exact hqtime
      have hdown : ActiveFollowerDownAcceptance.downSelected p i q.input.row q.input.time :=
        hcallFields.2.2.mp heligible.1
      obtain ⟨logged, cut, hi, hd, hc, hcutword, hsent, haccept, hposEquation⟩ :=
        hAwaitPrefix q hq hdown
      have hequation : AffineBatchDecoder.equation e.sample hword :=
        (AffineBatchDecoder.satisfies_samples_iff B hword).mp
          (by simpa only [hword] using hsolves) e he
      have hsingle : e ∈ ReferenceFollowerDownDecoderReplay.actualDownPositives i [q] := by
        exact (actual_positive_origin rate i [q] e).2
          ⟨q, by simp, call, hcall, hentry⟩
      have haw : ReferenceFirstCollectionAwaitedDownFailureReadout.awaitedDownAt
          rate q i hword := ⟨logged, cut, hi, hd, hc, hcutword, haccept⟩
      refine ⟨by dsimp [a]; omega, ?_, hequation, q, hrecordEntry', hsingle, haw⟩
      rw [heqTime, htime]
      exact Nat.add_le_add_left hjk s
    · intro v hav hvt hchannel
      have hstartV : s ≤ v.val := by simpa only [a] using hav
      have hvle : v.val ≤ s + k.val := by rw [← htime]; exact hvt
      have hindex : v.val - s ≤ k.val := by omega
      have hindexStrict : v.val - s < W.length := Nat.lt_of_le_of_lt hindex k.isLt
      let l : Fin W.length := ⟨v.val - s, hindexStrict⟩
      have hcalL := ReferenceFirstLiveSourceStoppedHandoverEndpoint.source_window_record_calendar
        rate rewards C_star C_h z l
      have hdate : (W[l.val]).input.time = v := by
        apply Fin.ext
        have htimeL := hcalL.1
        have htimeL' : (W[l.val]).input.time.val =
            ReferenceFirstLiveSourceStoppedReleaseEndpoint.physicalStart rate rewards C_star C_h z + l.val := by
          simpa only [W, List.get_eq_getElem] using htimeL
        rw [htimeL']
        rw [hsStart]
        have hlval : l.val = v.val - s := rfl
        rw [hlval]
        omega
      have hrecL : ReferenceSourcePrefixHistoryFiltration.actualRecord
          rate rewards C_star C_h v z = some (W[l.val]) := by
        simpa only [hdate, W, List.get_eq_getElem] using hcalL.2
      have hphysicalStartV : ReferenceCompletePhysicalHistory.physicalStart
          rate z rewards C_star C_h ≤ v.val := by
        change ReferenceFirstLiveSourceStoppedReleaseEndpoint.physicalStart
          rate rewards C_star C_h z ≤ v.val
        rw [hsStart]
        exact hstartV
      have hfieldsL := actual_record_input_fields rate rewards C_star C_h z v
        (W[l.val]) hrecL hphysicalStartV hcross
      have hrowL : (W[l.val]).input.row =
          z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) := by
        change (W[l.val]).input.rows (W[l.val]).input.selected = _
        rw [hfieldsL.1, hfieldsL.2.1]
      have hchannelL : ReferenceSelectedAffinePairLaw.selectedChannel p
          ((W[l.val]).input.row.2 (W[l.val]).input.time).1 = some (0, i) := by
        rw [hrowL, hdate]
        exact hchannel
      have hqprefix : W[l.val] ∈ R.records.take (k.val + 1) := by
        rw [htake]
        have hlval : l.val = v.val - s := rfl
        have hlk : l.val ≤ k.val := by rw [hlval]; exact hindex
        have hlprefix : l.val < min (k.val + 1) W.length := by omega
        exact List.mem_take_iff_getElem.mpr ⟨l.val, hlprefix, rfl⟩
      have hdown : ActiveFollowerDownAcceptance.downSelected p i
          (W[l.val]).input.row (W[l.val]).input.time := by
        exact downSelected_of_selectedChannel (W[l.val]).input.row
          (W[l.val]).input.time i hchannelL
      obtain ⟨logged, cut, hi, hd, hc, hcutword, hsent, haccept, _⟩ :=
        hAwaitPrefix W[l.val] hqprefix hdown
      have haw : ReferenceFirstCollectionAwaitedDownFailureReadout.awaitedDownAt
          rate (W[l.val]) i hword := ⟨logged, cut, hi, hd, hc, hcutword, haccept⟩
      exact ⟨W[l.val], hrecL, haw⟩
  · intro hglobal
    rcases hglobal with ⟨rg, i, word, B, a, hrg, hB, ha, hmulti, hentries, hcalendar⟩
    have hrgEq : rg = r := by
      exact Option.some.inj (hrg.symm.trans hrecord)
    subst rg
    have hsourceComplete : ReferenceCompleteAwaitedBatchSourceCoverage.sourceDownCompletedAt
        rate rewards C_star C_h z i t B := by
      simp only [ReferenceCompleteAwaitedBatchSourceCoverage.sourceDownCompletedAt,
        hrecord]
      exact (ReferenceLiteralAwaitedAmbiguityRowObservation.physicalDownCompletedAt_iff_completedDownBatch
        rate r i B).mpr hB
    have hsent : ∀ e ∈ B,
        e.time.val ≤ t.val ∧
          ReferenceCompleteAwaitedBatchSourceCoverage.sourceDownSentAt
            rate rewards C_star C_h z i e.time = some word := by
      intro e he
      obtain ⟨heA, heT, _, re, hre, _, haw⟩ := hentries e he
      obtain ⟨logged, cut, hi, hd, hc, hword, _⟩ := haw
      have hactualSent := ReferenceSourceRawDecoderDecision.retained_down_sent
        re i logged cut hi hd hc
      have hsent' : ReferenceActiveAffinePositiveTest.downSent re.input = some word := by
        rw [hword] at hactualSent
        exact hactualSent.symm
      refine ⟨heT, ?_⟩
      simp only [ReferenceCompleteAwaitedBatchSourceCoverage.sourceDownSentAt, hre]
      exact hsent'
    have hpost := ReferenceCompleteAwaitedBatchSourceCoverage.sourceDownCompletedAt_fixed_sent_no_prelaunch_entries
      rate rewards C_star C_h z i t B word hsourceComplete hsent
    have hamb :
        ReferenceFirstLiveDownCompletionReadout.completedAmbiguousAfterStart
          (ReferenceFirstLiveSourceStoppedReleaseEndpoint.physicalStart rate rewards C_star C_h z)
          r i := by
      refine ⟨B, hB, ?_, ?_⟩
      · intro e he
        exact hpost e he
      · exact hmulti
    exact ⟨i, by simpa [r, W, s] using hamb⟩

private theorem first_window_retained_flag_iff_failure
    (k : Fin (ReferenceFirstLiveSourceStoppedHandoverEndpoint.window
      rate rewards C_star C_h z).length) :
    ReferenceFirstLiveDecoderPastMeasurability.retainedDecoderRecordFlag
        (ReferenceFirstLiveSourceStoppedReleaseEndpoint.physicalStart rate rewards C_star C_h z)
        ((ReferenceFirstLiveSourceStoppedHandoverEndpoint.window
          rate rewards C_star C_h z).get k) = true ↔
      ReferenceFirstCollectionAwaitedDownFailureReadout.failureAt rate rewards C_star C_h z
        ((ReferenceFirstLiveSourceStoppedHandoverEndpoint.window
          rate rewards C_star C_h z).get k).input.time := by
  classical
  let W := ReferenceFirstLiveSourceStoppedHandoverEndpoint.window rate rewards C_star C_h z
  let r := W.get k
  let t := r.input.time
  have hcalendar := ReferenceFirstLiveSourceStoppedHandoverEndpoint.source_window_record_calendar
    rate rewards C_star C_h z k
  have hrecord : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t z = some r := by
    simpa only [W, r, t, List.get_eq_getElem] using hcalendar.2
  constructor
  · intro hret
    rcases (ReferenceFirstLiveDecoderPastMeasurability.retainedDecoderRecordFlag_eq_true_iff
      (ReferenceFirstLiveSourceStoppedReleaseEndpoint.physicalStart rate rewards C_star C_h z) r).mp
      hret with hwrong | hamb
    · have hOrdinary :=
        (ReferenceCompleteOrdinaryWrongCompletionCharacterization.ordinaryWrongCompletionAt_iff
          rate rewards C_star C_h t z).2 (Or.inr ⟨r, hrecord, hwrong⟩)
      have hbranches :=
        (ReferenceCompleteOrdinaryWrongCompletionCharacterization.ordinaryWrongCompletionAt_iff
          rate rewards C_star C_h t z).1 hOrdinary
      have hwrongProp : ReferenceActiveStoppedPrefixCoupling.saved_wrong_unique_accepted r := by
        simpa only [ReferenceGeneratedSavedWrongEvent.savedWrongRecordFlag,
          decide_eq_true_eq] using hwrong
      have hsaved : ∃ q, ReferenceSourcePrefixHistoryFiltration.actualRecord
          rate rewards C_star C_h t z = some q ∧
          ReferenceActiveStoppedPrefixCoupling.saved_wrong_unique_accepted q := by
        rcases hbranches with hpre | hsaved
        · exact ⟨r, hrecord, hwrongProp⟩
        · exact ⟨r, hrecord, hwrongProp⟩
      exact Or.inl hsaved
    · exact Or.inr (Or.inl
        ((first_window_local_ambiguous_iff_global_down rate rewards C_star C_h z k).mp hamb))
  · intro hfailure
    rcases hfailure with hwrong | hdown | hup
    · rcases hwrong with ⟨q, hq, hwrong⟩
      have hqeq : q = r := Option.some.inj (hq.symm.trans hrecord)
      subst q
      apply (ReferenceFirstLiveDecoderPastMeasurability.retainedDecoderRecordFlag_eq_true_iff
        (ReferenceFirstLiveSourceStoppedReleaseEndpoint.physicalStart rate rewards C_star C_h z) r).2
      left
      simpa only [ReferenceGeneratedSavedWrongEvent.savedWrongRecordFlag,
        decide_eq_true_eq] using hwrong
    · apply (ReferenceFirstLiveDecoderPastMeasurability.retainedDecoderRecordFlag_eq_true_iff
        (ReferenceFirstLiveSourceStoppedReleaseEndpoint.physicalStart rate rewards C_star C_h z) r).2
      right
      exact (first_window_local_ambiguous_iff_global_down rate rewards C_star C_h z k).mpr hdown
    · exact False.elim (first_window_fixed_up_false rate rewards C_star C_h z k hup)

private theorem first_window_record_event_iff_retained
    (k : Fin (ReferenceFirstLiveSourceStoppedHandoverEndpoint.window
      rate rewards C_star C_h z).length)
    (u : Fin p.T)
    (hu : u.val < ((ReferenceFirstLiveSourceStoppedHandoverEndpoint.window
      rate rewards C_star C_h z).get k).input.time.val) :
    (∃ r, ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h u z = some r ∧
      ReferenceFirstLiveDecoderPastMeasurability.retainedDecoderRecordFlag
        (ReferenceFirstLiveSourceStoppedReleaseEndpoint.physicalStart rate rewards C_star C_h z)
        r = true) ↔
      ReferenceFirstCollectionAwaitedDownFailureReadout.failureAt rate rewards C_star C_h z u := by
  classical
  let W := ReferenceFirstLiveSourceStoppedHandoverEndpoint.window rate rewards C_star C_h z
  let r := W.get k
  let t := r.input.time
  by_cases hbefore : u.val < ReferenceFirstLiveSourceStoppedReleaseEndpoint.physicalStart
      rate rewards C_star C_h z
  · have hnone := ReferenceSourcePrefixHistoryFiltration.actualRecord_eq_none_of_future_start
      rate rewards C_star C_h u z hbefore
    constructor
    · rintro ⟨q, hq, _⟩
      rw [hnone] at hq
      cases hq
    · intro hfailure
      unfold ReferenceFirstCollectionAwaitedDownFailureReadout.failureAt at hfailure
      rcases hfailure with ⟨q, hq, _⟩ | hdown | hup
      · have hq' : ReferenceSourcePrefixHistoryFiltration.actualRecord
            rate rewards C_star C_h u z = some q := by
          simpa only [ReferenceFirstCollectionAwaitedDownFailureReadout.actualRecord] using hq
        rw [hnone] at hq'
        cases hq'
      · rcases hdown with ⟨q, _, _, _, _, hq, _⟩
        have hq' : ReferenceSourcePrefixHistoryFiltration.actualRecord
            rate rewards C_star C_h u z = some q := by
          simpa only [ReferenceFirstCollectionAwaitedDownFailureReadout.actualRecord] using hq
        rw [hnone] at hq'
        cases hq'
      · unfold ReferenceCollectionUpFailureReadoutV2.fixedAwaitedUpFailureAt at hup
        rcases hup with ⟨q, _, _, _, _, hq, _⟩
        have hq' : ReferenceSourcePrefixHistoryFiltration.actualRecord
            rate rewards C_star C_h u z = some q := by
          simpa only [ReferenceCollectionUpFailureReadoutV2.lookup] using hq
        rw [hnone] at hq'
        cases hq'
  · have hstart : ReferenceFirstLiveSourceStoppedReleaseEndpoint.physicalStart
        rate rewards C_star C_h z ≤ u.val := Nat.le_of_not_gt hbefore
    have hu' : u.val < t.val := by
      simpa only [W, r, t, List.get_eq_getElem] using hu
    have hcalendar := ReferenceFirstLiveSourceStoppedHandoverEndpoint.source_window_record_calendar
      rate rewards C_star C_h z k
    have htime : t.val =
        ReferenceFirstLiveSourceStoppedReleaseEndpoint.physicalStart rate rewards C_star C_h z + k.val := by
      simpa only [W, r, t, List.get_eq_getElem] using hcalendar.1
    have hindex : u.val - ReferenceFirstLiveSourceStoppedReleaseEndpoint.physicalStart
        rate rewards C_star C_h z < k.val := by omega
    have hindexFin : u.val - ReferenceFirstLiveSourceStoppedReleaseEndpoint.physicalStart
        rate rewards C_star C_h z < W.length := Nat.lt_trans hindex k.isLt
    let l : Fin W.length := ⟨u.val -
      ReferenceFirstLiveSourceStoppedReleaseEndpoint.physicalStart rate rewards C_star C_h z,
      hindexFin⟩
    have hcalL := ReferenceFirstLiveSourceStoppedHandoverEndpoint.source_window_record_calendar
      rate rewards C_star C_h z l
    have hdate : (W[l.val]).input.time = u := by
      apply Fin.ext
      have htimeL := hcalL.1
      have htimeL' : (W[l.val]).input.time.val =
          ReferenceFirstLiveSourceStoppedReleaseEndpoint.physicalStart rate rewards C_star C_h z + l.val := by
        simpa only [W, List.get_eq_getElem] using htimeL
      rw [htimeL']
      dsimp [l]
      omega
    have hrecord : ReferenceSourcePrefixHistoryFiltration.actualRecord
        rate rewards C_star C_h u z = some (W[l.val]) := by
      simpa only [hdate, W, List.get_eq_getElem] using hcalL.2
    have hfailureIff := first_window_retained_flag_iff_failure rate rewards C_star C_h z l
    have htimeL : (W.get l).input.time = u := by
      simpa only [List.get_eq_getElem] using hdate
    rw [htimeL] at hfailureIff
    constructor
    · rintro ⟨q, hq, hret⟩
      have hqeq : q = W[l.val] := Option.some.inj (hq.symm.trans hrecord)
      subst q
      apply hfailureIff.mp
      simpa only [W, l, List.get_eq_getElem] using hret
    · intro hfailure
      have hret := hfailureIff.mpr hfailure
      exact ⟨W[l.val], hrecord, by simpa only [W, l, List.get_eq_getElem] using hret⟩

private theorem strictPast_false_iff_pastFailure_false
    (k : Fin (ReferenceFirstLiveSourceStoppedHandoverEndpoint.window
      rate rewards C_star C_h z).length)
    (n : Fin (((ReferenceFirstLiveSourceStoppedHandoverEndpoint.window
      rate rewards C_star C_h z).get k).input.time.val + 1)) :
    ReferenceFirstLiveDecoderPastMeasurability.strictPastDecoderFlag rate rewards C_star C_h
      (ReferenceFirstLiveSourceStoppedReleaseEndpoint.physicalStart rate rewards C_star C_h z)
      n.val (by have hn := n.isLt; omega) z = false ↔
    ReferenceFirstCollectionAwaitedDownFailureReadout.pastFailureFlag
      rate rewards C_star C_h n.val z = false := by
  classical
  let t := (ReferenceFirstLiveSourceStoppedHandoverEndpoint.window
    rate rewards C_star C_h z).get k |>.input.time
  have hnT : n.val ≤ p.T := by omega
  rw [ReferenceFirstLiveDecoderPastMeasurability.strictPastDecoderFlag_eq_false_iff
    rate rewards C_star C_h
    (ReferenceFirstLiveSourceStoppedReleaseEndpoint.physicalStart rate rewards C_star C_h z)
    n.val hnT z,
    ReferenceFirstCollectionAwaitedDownFailureReadout.pastFailureFlag_false_iff_no_earlier_failure
      rate rewards C_star C_h z n.val]
  constructor
  · intro h u hu hfailure
    let j : Fin n.val := ⟨u.val, hu⟩
    have hcast : Fin.castLE hnT j = u := by
      apply Fin.ext
      simp [j]
    obtain ⟨r, hr, hret⟩ :=
      (first_window_record_event_iff_retained rate rewards C_star C_h z k u (by omega)).2
        hfailure
    have hretFalse := h j r (by simpa only [hcast] using hr)
    rw [hret] at hretFalse
    cases hretFalse
  · intro h j r hr
    let u : Fin p.T := Fin.castLE hnT j
    have hu : u.val < n.val := by simpa only [u, Fin.val_castLE] using j.isLt
    cases hret : ReferenceFirstLiveDecoderPastMeasurability.retainedDecoderRecordFlag
        (ReferenceFirstLiveSourceStoppedReleaseEndpoint.physicalStart rate rewards C_star C_h z) r with
    | false => rfl
    | true =>
        have hr' : ReferenceSourcePrefixHistoryFiltration.actualRecord
            rate rewards C_star C_h u z = some r := by simpa only [u] using hr
        have hfailure :=
          (first_window_record_event_iff_retained rate rewards C_star C_h z k u (by omega)).mp
            ⟨r, hr', hret⟩
        exact False.elim (h u hu hfailure)

private theorem prelaunchPast_false_iff_no_failure
    (k : Fin (ReferenceFirstLiveSourceStoppedHandoverEndpoint.window
      rate rewards C_star C_h z).length)
    (n : Fin (((ReferenceFirstLiveSourceStoppedHandoverEndpoint.window
      rate rewards C_star C_h z).get k).input.time.val + 1)) :
    ReferencePrelaunchDownDecisionReadout.prelaunchPastDecoderFlag
      rate rewards C_star C_h z n.val (by have hn := n.isLt; omega) = false ↔
      ∀ j : Fin p.T, j.val < n.val → ∀ i : Fin (p.m - 1),
        ReferencePrelaunchDownDecisionReadout.prelaunchDownFailureAt
          rate rewards C_star C_h z i j = false := by
  classical
  have hnT : n.val ≤ p.T := by omega
  unfold ReferencePrelaunchDownDecisionReadout.prelaunchPastDecoderFlag
  rw [decide_eq_false_iff_not]
  simp only [not_exists]
  constructor
  · intro h j hj i
    cases hb : ReferencePrelaunchDownDecisionReadout.prelaunchDownFailureAt
        rate rewards C_star C_h z i j with
    | false => rfl
    | true =>
        let jn : Fin n.val := ⟨j.val, hj⟩
        have hcast : Fin.castLE hnT jn = j := by
          apply Fin.ext
          simp [jn]
        exact (h jn i (by simpa only [hcast] using hb)).elim
  · intro h v i hb
    have hv : (Fin.castLE hnT v).val < n.val := by simpa only [Fin.val_castLE] using v.isLt
    have hfalse := h (Fin.castLE hnT v) hv i
    rw [hfalse] at hb
    cases hb

/-- Exact decoder-only stop identification on the actual original first-live
window. The current detecting date remains included in the comparison. -/
public theorem first_window_decoder_stop_iff
    (k : Fin (ReferenceFirstLiveSourceStoppedHandoverEndpoint.window
      rate rewards C_star C_h z).length) :
    let t := ((ReferenceFirstLiveSourceStoppedHandoverEndpoint.window
      rate rewards C_star C_h z).get k).input.time
    t.val + 1 < ReferenceFirstLiveSourceStoppedReleaseEndpoint.decoderFirstExcluded
        rate rewards C_star C_h z ↔
      ((∀ j : Fin p.T, j.val < t.val → ∀ i : Fin (p.m - 1),
        ReferencePrelaunchDownDecisionReadout.prelaunchDownFailureAt
          rate rewards C_star C_h z i j = false) ∧
       ReferenceFirstCollectionAwaitedDownFailureReadout.pastFailureFlag
          rate rewards C_star C_h t.val z = false) := by
  dsimp only
  let W := ReferenceFirstLiveSourceStoppedHandoverEndpoint.window rate rewards C_star C_h z
  let t := (W.get k).input.time
  have hcut := ReferenceFirstLiveSourceStoppedReleaseEndpoint.decoder_cutoff_after_current_iff
    rate rewards C_star C_h t z
  constructor
  · intro hstop
    have hall := hcut.mp hstop
    let n : Fin (t.val + 1) := ⟨t.val, Nat.lt_succ_self _⟩
    have hflag := hall n
    have hparts :
        ReferencePrelaunchDownDecisionReadout.prelaunchPastDecoderFlag
            rate rewards C_star C_h z n.val (by omega) = false ∧
        ReferenceFirstLiveDecoderPastMeasurability.strictPastDecoderFlag
          rate rewards C_star C_h
          (ReferenceFirstLiveSourceStoppedReleaseEndpoint.physicalStart rate rewards C_star C_h z)
          n.val (by omega) z = false := by
      simpa only [ReferenceFirstLiveSourceStoppedReleaseEndpoint.actualDecoderFlag,
        Bool.or_eq_false_iff] using hflag
    refine ⟨?_, ?_⟩
    · have hpre := (prelaunchPast_false_iff_no_failure rate rewards C_star C_h z k n).mp hparts.1
      intro j hj i
      exact hpre j hj i
    · exact (strictPast_false_iff_pastFailure_false rate rewards C_star C_h z k n).mp hparts.2
  · rintro ⟨hpre, hfailure⟩
    apply hcut.mpr
    intro n
    have hnle : n.val ≤ t.val := by have hn := n.isLt; omega
    have hpreN : ∀ j : Fin p.T, j.val < n.val → ∀ i : Fin (p.m - 1),
        ReferencePrelaunchDownDecisionReadout.prelaunchDownFailureAt
          rate rewards C_star C_h z i j = false := by
      intro j hj i
      exact hpre j (lt_of_lt_of_le hj hnle) i
    have hpreFlag := (prelaunchPast_false_iff_no_failure rate rewards C_star C_h z k n).2 hpreN
    have hfailureN : ReferenceFirstCollectionAwaitedDownFailureReadout.pastFailureFlag
        rate rewards C_star C_h n.val z = false := by
      cases hf : ReferenceFirstCollectionAwaitedDownFailureReadout.pastFailureFlag
          rate rewards C_star C_h n.val z with
      | false => rfl
      | true =>
          have hmono := ReferenceFirstCollectionAwaitedDownFailureReadout.pastFailureFlag_mono
            rate rewards C_star C_h z n.val t.val hnle hf
          rw [hfailure] at hmono
          cases hmono
    have hstrict :=
      (strictPast_false_iff_pastFailure_false rate rewards C_star C_h z k n).2 hfailureN
    simpa only [ReferenceFirstLiveSourceStoppedReleaseEndpoint.actualDecoderFlag,
      Bool.or_eq_false_iff] using And.intro hpreFlag hstrict

end Bandits.Support.ReferenceFirstLiveInitialDecoderStopIdentification

end
