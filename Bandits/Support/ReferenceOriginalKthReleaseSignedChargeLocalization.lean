/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceOriginalKthReleaseGateAlignment
public import Bandits.Support.ReferenceOriginalInstallationReleaseSignedCharge
public import Bandits.Support.ReferenceOriginalInstallationStoppedReleasePhase

import Mathlib.Tactic

/-!
# Signed charge localization for one original ranked stopped release

This module identifies the signed physical charge on one original stopped
transfer with the fixed-label signed observable on the same actual
installation. The identity retains the complete rounded reward row, the actual
coordinator action, every player's actual own observation, empty-pending
signed terms, and the inclusive first detecting update. It proves no waiting
bound or conditional-expectation statement.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapPrivateRoundStreams
open scoped Classical BigOperators

namespace Bandits.Support.ReferenceOriginalKthReleaseSignedChargeLocalization

abbrev Parameters := ConstructorDimensions.Parameters

variable {p : Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)

/-- The literal signed release contribution of one original ranked stopped
transfer, summed over its existing actual release dates. -/
public def kthReleaseSignedCharge (k : Fin (p.T + 1)) : ℝ :=
  ∑ t ∈ ReferenceOriginalKthReleaseGateAlignment.kthReleaseDates
      rate rewards C_star C_h z k,
    ReferenceOriginalCalendarTransferPhaseCover.actualDateSignedDelta
      rate rewards C_star C_h z t

private theorem completeSuffixRecord_time
    (j : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length) :
    ((ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[j.val]'j.isLt).input.time.val =
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + j.val := by
  have htimes := ReferenceCompletePhysicalHistory.completeSuffixRecords_time_values
    rate z rewards C_star C_h
  have hget := congrArg (fun xs : List ℕ => xs[j.val]?) htimes
  have hj' : j.val < p.T - ReferenceCompletePhysicalHistory.physicalStart
      rate z rewards C_star C_h := by
    simpa only [ReferenceCompletePhysicalHistory.completeSuffixRecords_length] using j.isLt
  have hrange := List.getElem?_range'
    (s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
    (step := 1) hj'
  simpa [ReferenceActivePhysicalHorizon.calendar, List.getElem?_map,
    List.getElem?_eq_getElem j.isLt, hrange] using hget

private theorem releaseDelta_eq_fixedSignedDeficit
    (ell : ℕ) (t : Fin p.T)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (selected : ReferenceActivePhysicalStep.Selection r.input)
    (M : ReferenceActivePhysicalStep.Payload rate)
    (hrecord : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t z = some r)
    (hentry : (ReferenceSourcePrefixHistoryFiltration.entry
      rate rewards C_star C_h ell t z).map Prod.fst = some true)
    (hpayload : selected.view.payload = M)
    (hstored : ReferenceAssignmentPayloadPersistence.storedPayload
      r.input.state.coordinator = some M) :
    ReferenceOriginalCalendarTransferPhaseCover.releaseDelta rate rewards t r selected =
      ReferenceOriginalInstallationReleaseSignedCharge.actualFixedReleaseSignedDeficit
        rate rewards C_star C_h ell t z := by
  classical
  simp only [ReferenceOriginalCalendarTransferPhaseCover.releaseDelta,
    ReferenceOriginalCalendarTransferPhaseCover.releaseRaw,
    ReferenceActivePhysicalHorizon.RoundRecord.totalReward,
    ReferenceActivePhysicalHorizon.observationValue]
  simp [ReferenceOriginalInstallationReleaseSignedCharge.actualFixedReleaseSignedDeficit,
    hrecord, hentry, hpayload, hstored]

/-- The signed release charge of the original kth stopped transfer is either
zero on its actual empty-date branch, or is the exact stopped fixed-label
signed observable of the same actual installation. In the latter branch the
initial installation and genuine later births retain their original witnesses;
the prefix identity holds for every calendar prefix, including `v = T`. -/
public theorem kthReleaseSignedCharge_empty_or_actual_installation
    (k : Fin (p.T + 1)) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
    (ReferenceOriginalKthReleaseGateAlignment.kthReleaseDates
        rate rewards C_star C_h z k = ∅ ∧
      kthReleaseSignedCharge rate rewards C_star C_h z k = 0) ∨
    ∃ (b : Fin R.length) (M : ReferenceActivePhysicalStep.Payload rate),
      ((b.val = 0 ∧ R[b.val].input.state.coordinator = .first) ∨
        ReferenceCollectionPhaseHistory.laterChosen R[b.val].input = true) ∧
      ReferenceAssignmentPayloadPersistence.InstallationBirth R[b.val] M ∧
      R[b.val].input.time.val = s + b.val ∧
      M.sigma.val = s + b.val ∧
      ReferenceOriginalKthReleaseGateAlignment.kthReleaseDates
        rate rewards C_star C_h z k =
          ReferenceOriginalKthReleaseGateAlignment.fixedLabelReleaseDates
            rate rewards C_star C_h z (s + b.val) ∧
      (∀ t ∈ ReferenceOriginalKthReleaseGateAlignment.kthReleaseDates
          rate rewards C_star C_h z k,
        ReferenceOriginalCalendarTransferPhaseCover.actualDateSignedDelta
            rate rewards C_star C_h z t =
          ReferenceOriginalInstallationReleaseSignedCharge.actualFixedReleaseSignedDeficit
            rate rewards C_star C_h (s + b.val) t z) ∧
      (∀ v : ℕ,
        (∑ t ∈ (ReferenceOriginalKthReleaseGateAlignment.kthReleaseDates
            rate rewards C_star C_h z k).filter fun t => t.val < v,
          ReferenceOriginalCalendarTransferPhaseCover.actualDateSignedDelta
            rate rewards C_star C_h z t) =
        ∑ t ∈ (Finset.univ.filter fun t : Fin p.T => t.val < v),
          if ReferenceOriginalInstallationStoppedReleasePhase.supportAt
              rate rewards C_star C_h (s + b.val) t.val z then
            ReferenceOriginalInstallationReleaseSignedCharge.actualFixedReleaseSignedDeficit
              rate rewards C_star C_h (s + b.val) t z
          else 0) := by
  classical
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  rcases ReferenceOriginalKthReleaseGateAlignment.kthReleaseDates_eq_empty_or_actual_installation
      rate rewards C_star C_h z k with hempty |
    ⟨b, M, hbirth, hinstallation, htime, hsigma, hdates, hloc⟩
  · exact Or.inl ⟨hempty, by simp [kthReleaseSignedCharge, hempty]⟩
  · right
    have hpoint :
        ∀ t ∈ ReferenceOriginalKthReleaseGateAlignment.kthReleaseDates
          rate rewards C_star C_h z k,
          ReferenceOriginalCalendarTransferPhaseCover.actualDateSignedDelta
              rate rewards C_star C_h z t =
            ReferenceOriginalInstallationReleaseSignedCharge.actualFixedReleaseSignedDeficit
              rate rewards C_star C_h (s + b.val) t z := by
      intro t ht
      obtain ⟨j, hjtime, hrecord, selected, hselected, hpayload, _hpendingChoice,
        hstored, _hgate, _hpending, hentry, _⟩ := hloc t ht
      let r := (ReferenceOriginalCalendarTransferPhaseCover.actualRecords
        rate rewards C_star C_h z)[j.val]'j.isLt
      change ReferenceSourcePrefixHistoryFiltration.actualRecord
          rate rewards C_star C_h t z = some r at hrecord
      change r.output.preparation.coordinator.selection = some selected at hselected
      change selected.view.payload = M at hpayload
      change ReferenceAssignmentPayloadPersistence.storedPayload
          r.input.state.coordinator = some M at hstored
      have hentryTrue : (ReferenceSourcePrefixHistoryFiltration.entry
          rate rewards C_star C_h (s + b.val) t z).map Prod.fst = some true := by
        rw [hentry]
        rfl
      have hphase : t ∈ ReferenceOriginalCalendarTransferPhaseCover.releasePhaseDates
          rate rewards C_star C_h z :=
        (ReferenceOriginalKthReleaseGateAlignment.mem_kthReleaseDates_iff
          rate rewards C_star C_h z k t).mp ht |>.2
      obtain ⟨j', _hj', selected', hselected', hj'time, hdelta, _⟩ :=
        ReferenceOriginalCalendarTransferPhaseCover.actual_release_date_signed_diagnostic
          rate rewards C_star C_h z t hphase
      have htimej := completeSuffixRecord_time rate rewards C_star C_h z j
      have htimej' :
          ((ReferenceOriginalCalendarTransferPhaseCover.actualRecords
            rate rewards C_star C_h z)[j'.val]'j'.isLt).input.time.val =
            ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + j'.val := by
        simpa only [ReferenceOriginalCalendarTransferPhaseCover.actualRecords] using
          completeSuffixRecord_time rate rewards C_star C_h z j'
      have htimeEq := congrArg Fin.val (hjtime.trans hj'time.symm)
      rw [htimej, htimej'] at htimeEq
      have hindices : j = j' := Fin.ext (by omega)
      subst j'
      have hselectedEq : selected' = selected :=
        Option.some.inj (hselected'.symm.trans hselected)
      have hdelta' := hdelta
      rw [hselectedEq] at hdelta'
      have hfixed := releaseDelta_eq_fixedSignedDeficit rate rewards C_star C_h z
        (s + b.val) t r selected M hrecord hentryTrue hpayload hstored
      change ReferenceOriginalCalendarTransferPhaseCover.releaseDelta rate rewards t
          ((ReferenceOriginalCalendarTransferPhaseCover.actualRecords
            rate rewards C_star C_h z)[j.val]'j.isLt) selected =
        ReferenceOriginalInstallationReleaseSignedCharge.actualFixedReleaseSignedDeficit
          rate rewards C_star C_h (s + b.val) t z at hfixed
      exact hdelta'.trans hfixed
    refine ⟨b, M, hbirth, hinstallation, htime, hsigma, hdates, hpoint, ?_⟩
    intro v
    let dates := ReferenceOriginalKthReleaseGateAlignment.kthReleaseDates
      rate rewards C_star C_h z k
    let labelDates := ReferenceOriginalKthReleaseGateAlignment.fixedLabelReleaseDates
      rate rewards C_star C_h z (s + b.val)
    let isBefore := fun t : Fin p.T => t.val < v
    let delta := ReferenceOriginalCalendarTransferPhaseCover.actualDateSignedDelta
      rate rewards C_star C_h z
    let fixedDelta := fun t : Fin p.T =>
      ReferenceOriginalInstallationReleaseSignedCharge.actualFixedReleaseSignedDeficit
        rate rewards C_star C_h (s + b.val) t z
    have hleft :
        (∑ t ∈ dates.filter isBefore, delta t) =
          ∑ t : Fin p.T, if t ∈ dates.filter isBefore then delta t else 0 :=
      (Finset.sum_ite_mem_eq (dates.filter isBefore) delta).symm
    have hright :
        (∑ t ∈ Finset.univ.filter isBefore,
          if ReferenceOriginalInstallationStoppedReleasePhase.supportAt
              rate rewards C_star C_h (s + b.val) t.val z then fixedDelta t else 0) =
          ∑ t : Fin p.T,
            if t ∈ Finset.univ.filter isBefore then
              if ReferenceOriginalInstallationStoppedReleasePhase.supportAt
                  rate rewards C_star C_h (s + b.val) t.val z then fixedDelta t else 0
            else 0 :=
      (Finset.sum_ite_mem_eq (Finset.univ.filter isBefore) _).symm
    calc
      (∑ t ∈ dates.filter isBefore, delta t) =
          ∑ t : Fin p.T, if t ∈ dates.filter isBefore then delta t else 0 := hleft
      _ = ∑ t ∈ Finset.univ.filter isBefore,
            if ReferenceOriginalInstallationStoppedReleasePhase.supportAt
                rate rewards C_star C_h (s + b.val) t.val z then fixedDelta t else 0 := by
        rw [hright]
        apply Finset.sum_congr rfl
        intro t _
        by_cases hprefix : t.val < v
        · by_cases hdate : t ∈ dates
          · have hlabel : t ∈ labelDates := by
              change t ∈ ReferenceOriginalKthReleaseGateAlignment.fixedLabelReleaseDates
                rate rewards C_star C_h z (s + b.val)
              rw [← hdates]
              exact hdate
            have hsupport : ReferenceOriginalInstallationStoppedReleasePhase.supportAt
                rate rewards C_star C_h (s + b.val) t.val z := by
              rw [ReferenceOriginalInstallationStoppedReleasePhase.supportAt_iff
                rate rewards C_star C_h (s + b.val) t.val z t.isLt]
              exact (ReferenceOriginalKthReleaseGateAlignment.mem_fixedLabelReleaseDates_iff
                rate rewards C_star C_h z (s + b.val) t).mp hlabel
            simp [isBefore, Finset.mem_filter, hprefix, hdate, hsupport]
            exact hpoint t hdate
          · have hnotSupport : ¬ ReferenceOriginalInstallationStoppedReleasePhase.supportAt
                rate rewards C_star C_h (s + b.val) t.val z := by
              intro hsupp
              have hlabel : t ∈ labelDates := by
                apply (ReferenceOriginalKthReleaseGateAlignment.mem_fixedLabelReleaseDates_iff
                  rate rewards C_star C_h z (s + b.val) t).mpr
                exact (ReferenceOriginalInstallationStoppedReleasePhase.supportAt_iff
                  rate rewards C_star C_h (s + b.val) t.val z t.isLt).mp hsupp
              have hdateFromSupport : t ∈ dates := by
                change t ∈ ReferenceOriginalKthReleaseGateAlignment.kthReleaseDates
                  rate rewards C_star C_h z k
                rw [hdates]
                exact hlabel
              exact hdate hdateFromSupport
            simp [isBefore, Finset.mem_filter, hprefix, hdate, hnotSupport]
        · simp [isBefore, Finset.mem_filter, hprefix]

/-- The signed-release summand in the existing stopped-window identity is
exactly the literal charge defined here; the collection and handover summand
is unchanged. -/
public theorem kthWindowSignedCharge_eq_collection_handover_add_kthReleaseSignedCharge
    (k : Fin (p.T + 1)) :
    ReferenceOriginalStoppedTransferSignedReindex.kthWindowSignedCharge
        rate rewards C_star C_h z k =
      (∑ t ∈ ReferenceOriginalStoppedTransferSignedReindex.kthStoppedTransferWindowDates
          rate rewards C_star C_h z k ∩
          (ReferenceOriginalCalendarTransferPhaseCover.collectionPhaseDates
              rate rewards C_star C_h z ∪
            ReferenceOriginalCalendarTransferPhaseCover.handoverPhaseDates
              rate rewards C_star C_h z),
        ReferenceActualLiveEmptySignedRewardCalendar.liveEmptyCap rewards t) +
      kthReleaseSignedCharge rate rewards C_star C_h z k := by
  rw [ReferenceOriginalStoppedTransferSignedReindex.kthWindowSignedCharge_eq_signed_phase_sums]
  rfl

end Bandits.Support.ReferenceOriginalKthReleaseSignedChargeLocalization
