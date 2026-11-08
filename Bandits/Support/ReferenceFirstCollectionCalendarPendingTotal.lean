/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionCalendarPendingSplit
public import Bandits.Support.ReferenceFirstCollectionCorrectedCallAdmissibility

import Lean.Elab.Tactic.Omega

/-!
# Nonempty pending on the original first collection calendar

The actual initialized stream cannot end at an empty-pending boundary inside
the first raw collection window: its next selector would be the first global
collection call, whose corrected admissibility contradicts the window's
literal `takeWhile` endpoint.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions
open BootstrapPrivateRoundStreams
open ReferenceActivePhysicalStep
open ReferenceActivePhysicalHorizon
open scoped Classical

namespace Bandits.Support.ReferenceFirstCollectionCalendarPendingTotal

variable {p : ConstructorDimensions.Parameters}

abbrev Record (rate : ReferenceActivePhysicalStep.RateInput p) :=
  ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)

private theorem takeWhile_member_true {α : Type*} (pred : α → Bool)
    (xs : List α) (x : α) (h : x ∈ xs.takeWhile pred) : pred x = true := by
  induction xs with
  | nil => simp at h
  | cons a tail ih =>
      by_cases hp : pred a = true
      · simp [List.takeWhile, hp] at h
        rcases h with rfl | h
        · exact hp
        · exact ih h
      · simp [List.takeWhile, hp] at h

private theorem collectionWindow_laterChosen_false_of_pos
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (records : List (Record rate)) (w index : ℕ)
    (hpos : 0 < index)
    (hindex : index < (ReferenceCollectionPhaseHistory.collectionWindow records w).length) :
    ReferenceCollectionPhaseHistory.laterChosen
      ((ReferenceCollectionPhaseHistory.collectionWindow records w)[index]'hindex).input =
        false := by
  classical
  let head := (records.drop w).take 1
  let tail := (records.drop (w + 1)).takeWhile
    (fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input)
  let window := head ++ tail
  have hwindow : ReferenceCollectionPhaseHistory.collectionWindow records w = window := by
    rfl
  have hnonempty : records.drop w ≠ [] := by
    intro hnil
    have hdrop : records.drop (w + 1) = [] := by
      apply List.drop_eq_nil_of_le
      have hlen := congrArg List.length hnil
      simp at hlen
      omega
    have hzero : ReferenceCollectionPhaseHistory.collectionWindow records w = [] := by
      simp [ReferenceCollectionPhaseHistory.collectionWindow, hnil, hdrop]
    simp [hzero] at hindex
  have hhead : head.length = 1 := by
    rcases hdrop : records.drop w with _ | ⟨a, rest⟩
    · exact (hnonempty hdrop).elim
    · simp [head, hdrop]
  have hright : head.length ≤ index := by omega
  have hget : window[index]? = some (window[index]'(by
      simpa [hwindow] using hindex)) := by
    exact List.getElem?_eq_getElem (by simpa [hwindow] using hindex)
  have htailGet : tail[index - head.length]? = some (window[index]'(by
      simpa [hwindow] using hindex)) := by
    dsimp only [window] at hget
    rw [List.getElem?_append_right hright] at hget
    exact hget
  obtain ⟨htailIndex, htailValue⟩ := List.getElem?_eq_some_iff.mp htailGet
  have hmem : window[index]'(by simpa [hwindow] using hindex) ∈ tail := by
    rw [← htailValue]
    exact List.getElem_mem htailIndex
  have hpred := takeWhile_member_true _ _ _ hmem
  have hnot : !ReferenceCollectionPhaseHistory.laterChosen
      (window[index]'(by simpa [hwindow] using hindex)).input = true := hpred
  simpa [window, ReferenceCollectionPhaseHistory.collectionWindow] using hnot

/-- Every record of the unchanged original first collection calendar has a
nonempty incoming pending set on the same complete physical source. -/
public theorem original_raw_calendar_pending_nonempty
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let b := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
    let B := ReferenceCollectionPhaseHistory.collectionWindow R w
    ∀ k : Fin B.length,
      (ReferenceFirstCollectionPendingObservation.Q rate rewards C_star C_h b
        B[k.val].input.time z).Nonempty := by
  classical
  dsimp only
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let b := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
  let B := ReferenceCollectionPhaseHistory.collectionWindow R w
  change ∀ k : Fin B.length,
    (ReferenceFirstCollectionPendingObservation.Q rate rewards C_star C_h b
      B[k.val].input.time z).Nonempty
  intro k
  have hBpos : 0 < B.length := Nat.zero_lt_of_lt k.isLt
  have hR : R ≠ [] := by
    intro hnil
    have hzero : B.length = 0 := by
      simp [B, ReferenceCollectionPhaseHistory.collectionWindow, hnil]
    omega
  have hw : w < R.length := by
    by_contra hnot
    have hdrop : R.drop w = [] := List.drop_eq_nil_of_le (Nat.le_of_not_gt hnot)
    have hlen := congrArg List.length hdrop
    simp only [List.length_drop, List.length_nil] at hlen
    have hdrop' : R.drop (w + 1) = [] :=
      List.drop_eq_nil_of_le (by omega)
    have hzero : B.length = 0 := by
      simp [B, ReferenceCollectionPhaseHistory.collectionWindow, hdrop, hdrop']
    omega
  let launch := ReferenceCorrectedInitializationLaunch.correctedLaunch
    rate z rewards C_star C_h
  have hlaunchNone : launch ≠ none := by
    intro hnone
    have hno := ReferenceCompletePhysicalHistory.no_launch_complete_history
      rate z rewards C_star C_h hnone
    exact hR (by simpa [R] using hno.2.1)
  obtain ⟨active, hlaunchActive⟩ : ∃ active, launch = some active := by
    cases h : launch with
    | none => exact False.elim (hlaunchNone h)
    | some active => exact ⟨active, rfl⟩
  have hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome =
        true := by
    exact (ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
      rate z rewards C_star C_h).mp (by simp [launch, hlaunchActive])
  have hsome := (ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
    rate z rewards C_star C_h).2 hcross
  let initial := ReferenceFirstCollectionEpochAlignment.actualLaunchState
    rate z rewards C_star C_h hcross
  have hinitialEq : initial = active :=
    Option.get_of_eq_some hsome (by simpa [launch] using hlaunchActive)
  have hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate z rewards C_star C_h = some initial := by
    simpa [launch] using hlaunchActive.trans (congrArg some hinitialEq.symm)
  have hstart : ReferenceFirstCollectionReadyStream.startTime
      (rate := rate) z rewards C_star C_h = b := rfl
  have hphysicalStart :
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h =
        ReferenceInitializationRun.elapsed p
          (ReferenceInitializationRun.output
            (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed := by
    simpa [b, ReferenceFirstCollectionReadyStream.startTime] using hstart.symm
  let count := p.T - b
  have hspan : ReferenceFirstCollectionReadyStream.startTime
      (rate := rate) z rewards C_star C_h + count ≤ p.T := by
    have hb : b ≤ p.T := by
      simpa [b] using ReferenceCompletePhysicalHistory.physicalStart_le_T
        rate z rewards C_star C_h
    rw [hstart]
    simp only [count]
    omega
  let E := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
    rate z rewards C_star C_h hcross count hspan
  have hRE : R = E.records := by
    change ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h =
      (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
        rate z rewards C_star C_h hcross count hspan).records
    rw [ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
      rate z rewards C_star C_h initial hlaunch]
    rfl
  have hRlen : R.length = count := by
    rw [hRE]
    exact ReferenceActivePhysicalHorizon.run_record_count _ _ _ _ _ _ _ _
  have hwRun : w =
      (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
          rate z rewards C_star C_h hcross count hspan).records).length := by
    dsimp [w]
    rw [hRE]
  have hshortRun :
      (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
          rate z rewards C_star C_h hcross count hspan).records).length < count := by
    rw [← hwRun]
    exact Nat.lt_of_lt_of_eq hw hRlen
  have hwEpoch : w =
      (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
          z rewards C_star C_h hcross count hspan).records).length := by
    simpa only [ReferenceFirstCollectionReadyStream.actualEpoch] using hwRun
  have hshortEpoch :
      (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
          z rewards C_star C_h hcross count hspan).records).length < count := by
    simpa only [ReferenceFirstCollectionReadyStream.actualEpoch] using hshortRun
  obtain ⟨stream⟩ :=
    ReferenceFirstCollectionStreamEmptyDispatch.actual_initialized_first_collection_stream_empty_dispatch
      rate z rewards C_star C_h count hcross hspan hshortEpoch
  let out := stream.stream
  have hwindow : out.window = B := by
    simpa [out, E, w, B, hRE,
      ReferenceFirstCollectionReadyStream.actualWindow,
      ReferenceFirstCollectionReadyStream.actualEpoch] using out.windowIsActual
  have hsuffix := ReferenceFirstCollectionEmptyStreamSuffix.actual_first_collection_empty_stream_suffix
    rate z rewards C_star C_h count hcross hspan hshortRun stream
  dsimp only at hsuffix
  obtain ⟨_hb, hBbound, _hprefixFinal, _hprefixCoordinator, _hrecordsSplit,
    _hfinal, _hdrop, hemptyTail, htail⟩ := hsuffix
  have hQwindow := ReferenceFirstCollectionPendingObservation.Q_window
    (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
    z count hcross hspan hshortEpoch stream
  let actualB := ReferenceCollectionPhaseHistory.collectionWindow E.records
    (ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records).length
  have hBactual : B = actualB := by
    simp [B, actualB, w, hRE]
  have hBboundLocal : w + B.length ≤ count := by
    simpa [actualB, B, w, hRE] using hBbound
  have hQwindow' (j : Fin B.length) :
      ReferenceFirstCollectionPendingObservation.Q rate rewards C_star C_h b
        B[j.val].input.time z =
      if j.val = 0 then Finset.univ else
        if hj : j.val < out.ell then
          (out.ledgers ⟨j.val - 1, by omega⟩).pending else ∅ := by
    have hj' : j.val < actualB.length := by
      rw [← hBactual]
      exact j.isLt
    let j' : Fin actualB.length := ⟨j.val, hj'⟩
    have hq := hQwindow j'
    simpa [b, actualB, B, w, hRE, j'] using hq
  have hEllLe : out.ell ≤ B.length := by
    rw [← hwindow]
    exact out.withinWindow
  have hEllEq : out.ell = B.length := by
    by_contra hneq
    have hEllB : out.ell < B.length := by omega
    have hEllActual : out.ell < actualB.length := by
      rw [← hBactual]
      exact hEllB
    have hlastEmpty : stream.ledger.pending = ∅ := hemptyTail hEllActual
    have hlastWindowIndex : stream.last.val < out.window.length :=
      Nat.lt_of_lt_of_le stream.last.isLt out.withinWindow
    have hlastWindowRecord : out.window[stream.last.val] = stream.record :=
      Option.some.inj ((List.getElem?_eq_getElem hlastWindowIndex).symm.trans
        stream.recordAt)
    cases houtcome : stream.outcome with
    | exhausted hnonempty hwindowExhausted _ _ _ =>
        have hpending : stream.ledger.pending.Nonempty := by
          simpa [houtcome] using hnonempty
        have hlen : out.ell = B.length := by
          rw [hwindow] at hwindowExhausted
          exact hwindowExhausted
        omega
    | empty data =>
        cases hboundary : data.nextBoundary with
        | terminal htime _hcursor =>
            have hlastAligned := out.alignment ⟨stream.last.val, hlastWindowIndex⟩
            have hlastTime : stream.record.input.time.val + 1 =
                ReferenceFirstCollectionReadyStream.startTime (rate := rate)
                  z rewards C_star C_h + w + out.ell := by
              calc
                stream.record.input.time.val + 1 =
                    out.window[stream.last.val].input.time.val + 1 := by
                  rw [hlastWindowRecord]
                _ = ReferenceFirstCollectionReadyStream.startTime (rate := rate)
                    z rewards C_star C_h + w + 1 + stream.last.val := by
                  have ht := hlastAligned.2
                  rw [← hwEpoch] at ht
                  exact ht
                _ = ReferenceFirstCollectionReadyStream.startTime (rate := rate)
                    z rewards C_star C_h + w + out.ell := by
                  have hlast : stream.last.val + 1 = out.ell := stream.lastIsLast
                  omega
            have hprefix : w + out.ell < count :=
              Nat.lt_of_lt_of_le (Nat.add_lt_add_left hEllB w) hBboundLocal
            have hstrict : ReferenceFirstCollectionReadyStream.startTime
                (rate := rate) z rewards C_star C_h + w + out.ell < p.T := by
              calc
                _ < ReferenceFirstCollectionReadyStream.startTime (rate := rate)
                    z rewards C_star C_h + count := by omega
                _ ≤ p.T := hspan
            rw [hlastTime] at htime
            omega
        | next _before _currentStart x _input _stateIsPrior _timeIsNext _rows
            _selected _rewards equalsWindow _equalsRun dispatchData =>
            let rEll : Record (rate := rate) := B[out.ell]
            have hgetWindow : out.window[out.ell]? = some rEll := by
              rw [hwindow]
              exact List.getElem?_eq_getElem hEllB
            have hx : x = rEll.input := equalsWindow rEll hgetWindow
            have hnotLater := collectionWindow_laterChosen_false_of_pos R w out.ell
              (by have hp := out.positiveLength; omega) hEllB
            have hnotLater' : ReferenceCollectionPhaseHistory.laterChosen rEll.input = false := by
              simpa [B, rEll] using hnotLater
            have hstateCoord : rEll.input.state.coordinator =
                .collection out.payload stream.ledger out.saved := by
              simpa [hx, stream.ledgerIsLast] using dispatchData.actualState
            have hEllOut : out.ell < out.window.length := by
              rw [hwindow]
              exact hEllB
            have hrecordE : E.records[w + out.ell]? = some rEll := by
              have ha := out.alignment ⟨out.ell, hEllOut⟩
              simpa [E, w, B, hRE, hwindow, rEll,
                ReferenceFirstCollectionReadyStream.actualEpoch] using ha.1
            have hrecordR : R[w + out.ell]? = some rEll := by
              rw [hRE]
              exact hrecordE
            have hparamTrue :
                (ReferenceLaterSamplerParameterMeasurability.parameters? rEll.input).isSome = true := by
              have hsplitEll :=
                ReferenceFirstCollectionCalendarPendingSplit.original_raw_calendar_pending_split
                  rate rewards C_star C_h z ⟨out.ell, hEllB⟩
              rcases hsplitEll with hQ | hrest
              · have hQempty : ReferenceFirstCollectionPendingObservation.Q
                    rate rewards C_star C_h b B[out.ell].input.time z = ∅ := by
                  rw [hQwindow' ⟨out.ell, hEllB⟩]
                  have hpos : 0 < out.ell := by
                    have hp := out.positiveLength
                    omega
                  have hne : out.ell ≠ 0 := by omega
                  have hnotlt : ¬ out.ell < out.ell := Nat.lt_irrefl _
                  simp only [ite_eq_right hne, dite_eq_right hnotlt]
                exact False.elim
                  ((Finset.not_nonempty_iff_eq_empty.mpr hQempty) (by simpa [rEll] using hQ))
              · rcases hrest with hfailure | hdagger
                · rcases hfailure with ⟨⟨_payload, _ledger, _saved, _hcoord, _hpending⟩,
                    hparam, _hnext, _hfuture⟩
                  exact hparam
                · rw [hstateCoord] at hdagger
                  cases hdagger
            have hfirstNe :
                ReferenceFirstCollectionSamplerCall.firstCollectionCall
                    rate rewards C_star C_h z ≠ none := by
              intro hnone
              have hnoneAll :=
                (ReferenceFirstCollectionSamplerCall.firstCollectionCall_none_iff
                  (rate := rate) rewards C_star C_h z).mp hnone
              have hmem : rEll ∈ R := List.mem_of_getElem? hrecordR
              have hparamNone := hnoneAll rEll hmem
              cases h : ReferenceLaterSamplerParameterMeasurability.parameters? rEll.input with
              | none => simp [h] at hparamTrue
              | some theta => simp [h] at hparamNone
            have hcallExists : ∃ call,
                ReferenceFirstCollectionSamplerCall.firstCollectionCall
                  rate rewards C_star C_h z = some call := by
              cases hfirst : ReferenceFirstCollectionSamplerCall.firstCollectionCall
                  rate rewards C_star C_h z with
              | none => exact False.elim (hfirstNe hfirst)
              | some call => exact ⟨call, rfl⟩
            let call := Classical.choose hcallExists
            have hfirst := Classical.choose_spec hcallExists
            let u := call.1
            let t := call.2.1
            let theta := call.2.2
            have hfirstCall :
                ReferenceFirstCollectionSamplerCall.firstCollectionCall
                  rate rewards C_star C_h z = some (u, (t, theta)) := by
              simpa [u, t, theta, call] using hfirst
            have hfirstSpec :=
              (ReferenceFirstCollectionSamplerCall.firstCollectionCall_spec
                (rate := rate) rewards C_star C_h z u t theta).mp hfirstCall
            rcases hfirstSpec with ⟨n0, r0, hr0, htime0, hcall0, hearlier0⟩
            have hzCell : z ∈ ReferenceCalendarCollectionCallControlLaw.firstCell
                rate rewards C_star C_h u t := by
              change (ReferenceFirstCollectionSamplerCall.firstCollectionCall
                rate rewards C_star C_h z).map (fun c => (c.1, c.2.1)) = some (u, t)
              rw [hfirstCall]
              rfl
            have hA :=
              ReferenceFirstCollectionCorrectedCallAdmissibility.firstCell_corrected_parameters_admissible
                rate rewards C_star C_h u t z hzCell
            dsimp only at hA
            let nA := Classical.choose hA
            have hA1 := Classical.choose_spec hA
            let rA := Classical.choose hA1
            have hA2 := Classical.choose_spec hA1
            let thetaA := Classical.choose hA2
            have hA3 := Classical.choose_spec hA2
            let oldA := Classical.choose hA3
            have hA4 := Classical.choose_spec hA3
            let ledgerA := Classical.choose hA4
            have hA5 := Classical.choose_spec hA4
            let savedA := Classical.choose hA5
            have hA6 := Classical.choose_spec hA5
            let registersA := Classical.choose hA6
            have hA7 := Classical.choose_spec hA6
            have hA8 := hA7.2
            have hA9 := hA8.2
            have hA10 := hA9.2
            have hA11 := hA10.2
            have hA12 := hA11.2
            have hA13 := hA12.2
            have hA14 := hA13.2
            have hA15 := hA14.2
            have hA16 := hA15.2
            have hA17 := hA16.2
            have hA18 := hA17.2
            have hA19 := hA18.2
            have hA20 := hA19.2
            have hA21 := hA20.2
            have hactualA := hA9.1
            have hLaterA := hA21.1
            have hbounds :=
              ReferenceFirstCollectionCallStoredBounds.firstCell_stored_bounds
                rate rewards C_star C_h u t z hzCell
            dsimp only at hbounds
            rcases hbounds with ⟨nB, rB, thetaB, hrB, htimeB, hactualB, hcallB,
              _hrowsB, _hselectedB, _hrewardsB, hearlierB, _hstartN,
              hcrossB, hspanB, hrecordsB, hshortB, f, _e, _houtcomeB,
              _hcutoffStartB, hnB, _hrestB⟩
            have hparamB :
                ReferenceLaterSamplerParameterMeasurability.parameters? rB.input ≠ none := by
              obtain ⟨_payload, _ledger, _saved, _hcoord, _hcut, hparam⟩ :=
                (ReferenceFirstCollectionSamplerCall.collectionCallAt_spec
                  rB u thetaB).mp hcallB
              rw [hparam]
              exact Option.some_ne_none _
            have hparam0 :
                ReferenceLaterSamplerParameterMeasurability.parameters? r0.input ≠ none := by
              obtain ⟨_payload, _ledger, _saved, _hcoord, _hcut, hparam⟩ :=
                (ReferenceFirstCollectionSamplerCall.collectionCallAt_spec
                  r0 u theta).mp hcall0
              rw [hparam]
              exact Option.some_ne_none _
            have hn0_le_nB : n0 ≤ nB := by
              by_contra hlt
              have hnone := hearlier0 nB (by omega) rB hrB
              exact hparamB hnone
            have hnB_le_n0 : nB ≤ n0 := by
              by_contra hlt
              have hnone := hearlierB n0 (by omega) r0 hr0
              exact hparam0 hnone
            have hnEq : nB = n0 := by omega
            have hn0_le_boundary : n0 ≤ w + out.ell := by
              by_contra hlt
              have hnone := hearlier0 (w + out.ell) (by omega) rEll hrecordR
              have hparamNone :
                  ReferenceLaterSamplerParameterMeasurability.parameters? rEll.input = none := hnone
              rw [hparamNone] at hparamTrue
              cases hparamTrue
            have hnB_le_boundary : nB ≤ w + out.ell := by omega
            have hrecordAeqB : rA = rB := Option.some.inj (hactualA.symm.trans hactualB)
            have hLaterB : ReferenceCollectionPhaseHistory.laterChosen rB.input = true := by
              rw [← hrecordAeqB]
              exact hLaterA
            have hstreamPositive : 0 < f.stream.ell := f.stream.positiveLength
            have hsum : w + f.stream.ell ≤ w + out.ell := by
              rw [← hnB]
              exact hnB_le_boundary
            have hellf_le : f.stream.ell ≤ out.ell := by
              omega
            have hellf_window : f.stream.ell < B.length := by omega
            have hrecordBoundE : E.records[w + f.stream.ell]? =
                some B[f.stream.ell] := by
              have ha := out.alignment ⟨f.stream.ell, by
                rw [hwindow]
                exact hellf_window⟩
              simpa [E, w, B, hRE, hwindow,
                ReferenceFirstCollectionReadyStream.actualEpoch] using ha.1
            have hrecordBoundR : R[w + f.stream.ell]? = some B[f.stream.ell] := by
              rw [hRE]
              exact hrecordBoundE
            have hrecordIndexEq : rB = B[f.stream.ell] := by
              have hnB' : nB = w + f.stream.ell := hnB
              rw [hnB'] at hrB
              exact Option.some.inj (hrB.symm.trans hrecordBoundR)
            have hnotLater := collectionWindow_laterChosen_false_of_pos R w
              f.stream.ell hstreamPositive hellf_window
            have hnotLater' :
                ReferenceCollectionPhaseHistory.laterChosen B[f.stream.ell].input = false := by
              simpa [B] using hnotLater
            have hLaterIndex :
                ReferenceCollectionPhaseHistory.laterChosen B[f.stream.ell].input = true := by
              rw [← hrecordIndexEq]
              exact hLaterB
            rw [hnotLater'] at hLaterIndex
            cases hLaterIndex
  have hQwindowK := hQwindow' k
  by_cases hk0 : k.val = 0
  · rw [hQwindowK]
    simp only [hk0, ↓reduceIte]
    exact Finset.univ_nonempty_iff.mpr ⟨⟨0, by have hp := p.two_le_m; omega⟩⟩
  · have hkpos : 0 < k.val := Nat.pos_of_ne_zero hk0
    have hklt : k.val < out.ell := by rw [hEllEq]; exact k.isLt
    have hsub : k.val - 1 + 1 = k.val := by omega
    have hpendingIndex : k.val - 1 < out.ell := by
      exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) hklt
    have hpending := out.pending_before_last
      ⟨k.val - 1, hpendingIndex⟩ (by rw [hsub]; exact hklt)
    rw [hQwindowK]
    simpa [hk0, hklt] using hpending

end Bandits.Support.ReferenceFirstCollectionCalendarPendingTotal
