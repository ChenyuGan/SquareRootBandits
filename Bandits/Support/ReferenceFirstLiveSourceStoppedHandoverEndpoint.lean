/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveStoppedReleaseSignedCost

/-!
# Actual stopped first-handover support

This module reads missing confirmations from the original corrected-source
physical run. Its support is cut by the literal decoder and overflow endpoint
already used by the first-live release analysis. The physical run itself still
continues through the horizon.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open scoped Classical

namespace Bandits.Support.ReferenceFirstLiveSourceStoppedHandoverEndpoint

variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ)

abbrev Source (p₀ : ConstructorDimensions.Parameters) :=
  BootstrapPrivateRoundStreams.SourceInput p₀
abbrev Record := ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)

/-- The original complete physical suffix, including every round after an
analytical decoder or overflow stop. -/
def completeRecords (z : Source p) :=
  ReferenceFirstLiveSourceStoppedReleaseEndpoint.completeRecords
    rate rewards C_star C_h z

/-- The actual first-live record prefix, ending before the first chosen
cutoff. -/
def window (z : Source p) :=
  ReferenceFirstLiveConfirmationHistory.firstLiveWindow (completeRecords rate rewards C_star C_h z)

/-- The actual coordinator selection retained in one physical record. -/
def actualSelection (r : Record (rate := rate)) :=
  r.output.preparation.coordinator.selection

/-- The missing set is the actual choice-time pending set when a selection is
present, and empty only when this record has no coordinator selection. -/
def missing (r : Record (rate := rate)) : Finset (Fin (p.m - 1)) :=
  ((actualSelection rate r).map fun selected => selected.view.pendingAtChoice).getD ∅

/-- The first assignment payload, read only from the first actual record and
its actual coordinator selection. -/
def payload0 (z : Source p) : Option (ReferenceActivePhysicalStep.Payload rate) :=
  (window rate rewards C_star C_h z).head?.bind fun r =>
    (actualSelection rate r).map fun selected => selected.view.payload

/-- Source dates with a nonempty actual missing-confirmation set, before the
literal first excluded date. -/
def supportDates (z : Source p) : Finset ℕ := by
  classical
  exact (((window rate rewards C_star C_h z).toFinset.filter fun r =>
    (missing rate r).Nonempty).filter fun r =>
      r.input.time.val + 1 <
        ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstExcluded
          rate rewards C_star C_h z).image fun r => r.input.time.val + 1

/-- The actual pending set on the original source calendar, masked only by
the literal stopped handover support. -/
def pendingNat (k : ℕ) (z : Source p) : Finset (Fin (p.m - 1)) :=
  if hk : k < p.T then
    if k + 1 ∈ supportDates rate rewards C_star C_h z then
      ((ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
        ⟨k, hk⟩ z).map (missing rate)).getD ∅
    else ∅
  else ∅

/-- Literal finite minimum with the terminal source-date sentinel adjoined. -/
def sigma (z : Source p) : ℕ := by
  classical
  exact (supportDates rate rewards C_star C_h z ∪ {p.T + 1}).min'
    ⟨p.T + 1, Finset.mem_union_right _ (Finset.mem_singleton_self _)⟩

/-- One past the last supported source date, or the terminal sentinel when
the actual missing-confirmation support is empty. -/
def theta (z : Source p) : ℕ := by
  classical
  exact if h : (supportDates rate rewards C_star C_h z).Nonempty then
    (supportDates rate rewards C_star C_h z).max' h + 1 else p.T + 1

/-- No corrected launch gives the actual empty first-live window. -/
theorem window_eq_nil_of_no_launch (z : Source p)
    (hnone : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate z rewards C_star C_h = none) :
    window rate rewards C_star C_h z = [] := by
  have hno := ReferenceCompletePhysicalHistory.no_launch_complete_history
    rate z rewards C_star C_h hnone
  have hrecords : completeRecords rate rewards C_star C_h z = [] := by
    simpa only [completeRecords,
      ReferenceFirstLiveSourceStoppedReleaseEndpoint.completeRecords] using hno.2.1
  change ReferenceFirstLiveConfirmationHistory.firstLiveWindow
    (completeRecords rate rewards C_star C_h z) = []
  rw [hrecords]
  simp [ReferenceFirstLiveConfirmationHistory.firstLiveWindow]

/-- The Option payload readout preserves absence on the no-launch branch. -/
theorem payload0_none_of_no_launch (z : Source p)
    (hnone : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate z rewards C_star C_h = none) :
    payload0 rate rewards C_star C_h z = none := by
  simp [payload0, window_eq_nil_of_no_launch rate rewards C_star C_h z hnone]

/-- Every supported source date is a genuine one-based round in the horizon. -/
theorem supportDates_member_bounds (z : Source p) (d : ℕ)
    (hd : d ∈ supportDates rate rewards C_star C_h z) : 1 ≤ d ∧ d ≤ p.T := by
  classical
  unfold supportDates at hd
  obtain ⟨r, hr, hd⟩ := Finset.mem_image.mp hd
  obtain ⟨hr, _hbeforeExcluded⟩ := Finset.mem_filter.mp hr
  obtain ⟨hr, _hnonempty⟩ := Finset.mem_filter.mp hr
  have hrtime := r.input.time.isLt
  have hrdate := congrArg (fun n => n) hd
  constructor <;> omega

/-- The literal minimum and one-past-maximum sentinels lie in the source
calendar, including the empty-support branch. -/
theorem sigma_theta_bounds (z : Source p) :
    1 ≤ sigma rate rewards C_star C_h z ∧
      sigma rate rewards C_star C_h z ≤ theta rate rewards C_star C_h z ∧
      theta rate rewards C_star C_h z ≤ p.T + 1 := by
  classical
  let S := supportDates rate rewards C_star C_h z
  let U := S ∪ {p.T + 1}
  have hUnonempty : U.Nonempty := ⟨p.T + 1, Finset.mem_union_right _
    (Finset.mem_singleton_self _)⟩
  have hUlower : ∀ d ∈ U, 1 ≤ d := by
    intro d hd
    rcases Finset.mem_union.mp hd with hS | hsentinel
    · exact (supportDates_member_bounds rate rewards C_star C_h z d hS).1
    · simp only [Finset.mem_singleton] at hsentinel
      omega
  have hsiglower : 1 ≤ U.min' hUnonempty := (Finset.le_min'_iff U hUnonempty).2 hUlower
  have hsigupper : U.min' hUnonempty ≤ p.T + 1 :=
    Finset.min'_le U (p.T + 1) (Finset.mem_union_right _ (Finset.mem_singleton_self _))
  by_cases hS : S.Nonempty
  · have hmaxmem : S.max' hS ∈ S := Finset.max'_mem _ _
    have hmaxbound := (supportDates_member_bounds rate rewards C_star C_h z _ hmaxmem).2
    have hsigma : sigma rate rewards C_star C_h z = U.min' hUnonempty := rfl
    have htheta : theta rate rewards C_star C_h z = S.max' hS + 1 := by
      simp [theta, S, hS]
    have hsigtheta : U.min' hUnonempty ≤ S.max' hS + 1 := by
      exact Nat.le_succ_of_le (Finset.min'_le U (S.max' hS)
        (Finset.mem_union_left _ hmaxmem))
    have hthetaUpper : S.max' hS + 1 ≤ p.T + 1 := by omega
    refine ⟨?_, ?_, ?_⟩
    · rw [hsigma]
      exact hsiglower
    · rw [hsigma, htheta]
      exact hsigtheta
    · rw [htheta]
      exact hthetaUpper
  · have hsig : U.min' hUnonempty = p.T + 1 := by
      apply le_antisymm
      · exact hsigupper
      · apply (Finset.le_min'_iff U hUnonempty).2
        intro d hd
        rcases Finset.mem_union.mp hd with hmem | hsentinel
        · exact False.elim (hS ⟨d, hmem⟩)
        · simp only [Finset.mem_singleton] at hsentinel
          omega
    have hsigma : sigma rate rewards C_star C_h z = U.min' hUnonempty := rfl
    have htheta : theta rate rewards C_star C_h z = p.T + 1 := by
      simp [theta, S, hS]
    refine ⟨?_, ?_, ?_⟩
    · rw [hsigma]
      exact hsiglower
    · rw [hsigma, htheta]
      exact hsig.le
    · exact htheta.le

/-- The literal support lies between its finite minimum and one-past-maximum
sentinels. -/
theorem supportDates_subset_interval (z : Source p) :
    supportDates rate rewards C_star C_h z ⊆
      Finset.Ico (sigma rate rewards C_star C_h z) (theta rate rewards C_star C_h z) := by
  classical
  let S := supportDates rate rewards C_star C_h z
  let U := S ∪ {p.T + 1}
  have hUnonempty : U.Nonempty := ⟨p.T + 1, Finset.mem_union_right _
    (Finset.mem_singleton_self _)⟩
  intro d hd
  have hlow : sigma rate rewards C_star C_h z ≤ d := by
    simpa only [sigma, S, U] using
      (Finset.min'_le U d (Finset.mem_union_left _ hd))
  by_cases hS : S.Nonempty
  · have htheta : theta rate rewards C_star C_h z = S.max' hS + 1 := by
      simp [theta, S, hS]
    have hhigh : d < theta rate rewards C_star C_h z := by
      rw [htheta]
      exact Nat.lt_succ_of_le (Finset.le_max' S d hd)
    exact Finset.mem_Ico.mpr ⟨hlow, hhigh⟩
  · exact False.elim (hS ⟨d, hd⟩)

/-- Away from the literal confirmation support, the endpoint pending readout
is exactly empty. -/
theorem pendingNat_empty_when_date_not_supported (z : Source p) (k : ℕ)
    (hdate : k + 1 ∉ supportDates rate rewards C_star C_h z) :
    pendingNat rate rewards C_star C_h k z = ∅ := by
  by_cases hk : k < p.T
  · simp [pendingNat, hk, hdate]
  · simp [pendingNat, hk]

/-- On a supported source date the readout is the actual filtration record's
literal selection-time missing set. -/
theorem pendingNat_eq_actual_missing_on_support (z : Source p) (k : ℕ)
    (hk : k < p.T) (hdate : k + 1 ∈ supportDates rate rewards C_star C_h z) :
    pendingNat rate rewards C_star C_h k z =
      ((ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
        ⟨k, hk⟩ z).map (missing rate)).getD ∅ := by
  simp [pendingNat, hk, hdate]

/-- The pending set vanishes outside the literal finite endpoint interval. -/
theorem pendingNat_empty_outside_interval (z : Source p) (k : ℕ)
    (hout : ¬ (sigma rate rewards C_star C_h z ≤ k + 1 ∧
      k + 1 < theta rate rewards C_star C_h z)) :
    pendingNat rate rewards C_star C_h k z = ∅ := by
  apply pendingNat_empty_when_date_not_supported
  intro hdate
  have hinterval := supportDates_subset_interval rate rewards C_star C_h z hdate
  exact hout (Finset.mem_Ico.mp hinterval)

/-- Every nonempty pending observation lies inside the literal finite
endpoint interval. -/
theorem pendingNat_nonempty_inside_interval (z : Source p) (k : ℕ)
    (hne : (pendingNat rate rewards C_star C_h k z).Nonempty) :
    sigma rate rewards C_star C_h z ≤ k + 1 ∧
      k + 1 < theta rate rewards C_star C_h z := by
  by_contra hout
  have hempty := pendingNat_empty_outside_interval rate rewards C_star C_h z k hout
  rw [hempty] at hne
  exact Finset.not_nonempty_empty hne

theorem source_window_record_calendar (z : Source p)
    (k : Fin (window rate rewards C_star C_h z).length) :
    let r := (window rate rewards C_star C_h z)[k.val]
    r.input.time.val =
        ReferenceFirstLiveSourceStoppedReleaseEndpoint.physicalStart
          rate rewards C_star C_h z + k.val ∧
      ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
        r.input.time z = some r := by
  dsimp only
  classical
  let launch := ReferenceCorrectedInitializationLaunch.correctedLaunch
    rate z rewards C_star C_h
  cases hlaunch : launch with
  | none =>
      have hno := ReferenceCompletePhysicalHistory.no_launch_complete_history
        rate z rewards C_star C_h hlaunch
      have hrecords : completeRecords rate rewards C_star C_h z = [] := by
        simpa only [completeRecords,
          ReferenceFirstLiveSourceStoppedReleaseEndpoint.completeRecords] using hno.2.1
      have hwindow : window rate rewards C_star C_h z = [] := by
        change ReferenceFirstLiveConfirmationHistory.firstLiveWindow
          (completeRecords rate rewards C_star C_h z) = []
        rw [hrecords]
        simp [ReferenceFirstLiveConfirmationHistory.firstLiveWindow]
      have hfalse : False := by
        have hk : k.val < 0 := by
          simpa only [hwindow, List.length_nil] using k.isLt
        omega
      exact hfalse.elim
  | some active =>
      have hsome : launch.isSome = true := by simp [hlaunch]
      have hcross := (ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
        rate z rewards C_star C_h).mp (by simpa [launch] using hsome)
      have hlaunchSeed := ReferenceLocalReleaseGateChronology.sourceSeed_launch
        rate z rewards C_star C_h hcross
      let s := ReferenceFirstLiveSourceStoppedReleaseEndpoint.physicalStart rate rewards C_star C_h z
      let count := p.T - s
      have hs : s ≤ p.T := by
        simpa only [s, ReferenceFirstLiveSourceStoppedReleaseEndpoint.physicalStart] using
          ReferenceCompletePhysicalHistory.physicalStart_le_T rate z rewards C_star C_h
      have hspan : s + count ≤ p.T := by dsimp [count]; omega
      let E := ReferenceLocalReleaseGateChronology.sourceRun rate z rewards C_star C_h
        hcross s count (by
          dsimp [s, ReferenceFirstLiveSourceStoppedReleaseEndpoint.physicalStart]
          rfl) hspan
      have hcomplete : E.records =
          ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h := by
        exact (ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
          rate z rewards C_star C_h
          (ReferenceLocalReleaseGateChronology.sourceSeed rate z rewards C_star C_h hcross)
          hlaunchSeed).symm
      let predicate : Record (rate := rate) → Bool := fun r =>
        !ReferenceCollectionPhaseHistory.cutoffChosen r.input
      have hwindowEq : window rate rewards C_star C_h z = (E.records.takeWhile predicate) := by
        change ReferenceFirstLiveConfirmationHistory.firstLiveWindow
          (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h) =
            (E.records.takeWhile predicate)
        unfold ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        rw [← hcomplete]
      have hkW : k.val < (E.records.takeWhile predicate).length := by
        simpa only [hwindowEq] using k.isLt
      have hprefixTake : E.records.takeWhile predicate <+: E.records :=
        List.takeWhile_prefix _
      have hkRecords : k.val < E.records.length := by
        exact Nat.lt_of_lt_of_le hkW hprefixTake.length_le
      have hwindowOpt :
          some ((window rate rewards C_star C_h z)[k.val]) =
            some ((E.records.takeWhile predicate)[k.val]) := by
        have h := congrArg (fun xs : List (Record (rate := rate)) => xs[k.val]?) hwindowEq
        rw [List.getElem?_eq_getElem k.isLt,
          List.getElem?_eq_getElem hkW] at h
        exact h
      have htakeOpt :
          some ((E.records.takeWhile predicate)[k.val]) = some (E.records[k.val]) := by
        have hgetTake := hprefixTake.getElem hkW
        exact congrArg some hgetTake
      have hget : (window rate rewards C_star C_h z)[k.val] = E.records[k.val] :=
        Option.some.inj (hwindowOpt.trans htakeOpt)
      have hcount : E.records.length = count := by
        exact ReferenceActivePhysicalHorizon.run_record_count
          (ReferenceLocalReleaseGateChronology.sourceSeed rate z rewards C_star C_h hcross)
          z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s count hspan
          ((ReferenceLocalReleaseGateChronology.canonical_seed_release_inputs
            rate z rewards C_star C_h hcross).2.1)
      have htime : (window rate rewards C_star C_h z)[k.val].input.time.val = s + k.val := by
        rw [hget]
        have hactive := (ReferenceLocalReleaseGateChronology.canonical_seed_release_inputs
          rate z rewards C_star C_h hcross).2.1
        have hindex := ReferenceLocalReleaseGateChronology.run_record_at
          (ReferenceLocalReleaseGateChronology.sourceSeed rate z rewards C_star C_h hcross)
          z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s hactive
          count hspan ⟨k.val, by rw [← hcount]; exact hkRecords⟩
        have hkCount : k.val < count := by rw [← hcount]; exact hkRecords
        have hindexE : E.records[k.val] =
            ReferenceAssignmentPayloadChronology.actualRunRecordAt
              (ReferenceLocalReleaseGateChronology.sourceSeed rate z rewards C_star C_h hcross)
              z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s k.val
              (by have hk := hkCount; omega) hactive := by
          simpa only [E, ReferenceLocalReleaseGateChronology.sourceRun] using hindex
        rw [hindexE]
        simp [ReferenceAssignmentPayloadChronology.actualRunRecordAt,
          ReferenceActivePhysicalHorizon.roundInputAt]
      have hactual : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
          ((window rate rewards C_star C_h z)[k.val].input.time) z =
          some ((window rate rewards C_star C_h z)[k.val]) := by
        have hstart : ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h ≤
            (window rate rewards C_star C_h z)[k.val].input.time.val := by
          have hphysical : ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h = s := rfl
          rw [hphysical, htime]
          omega
        have hindexNat :
            (window rate rewards C_star C_h z)[k.val].input.time.val -
              ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h = k.val := by
          have hphysical : ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h = s := rfl
          rw [hphysical, htime]
          omega
        have hindexBound : k.val <
            (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).length := by
          rw [← hcomplete]
          exact hkRecords
        have hkCount : k.val < count := by
          rw [← hcount]
          exact hkRecords
        have hlookup := ReferenceSourcePrefixHistoryFiltration.actualRecord_on_launch
          rate rewards C_star C_h ((window rate rewards C_star C_h z)[k.val].input.time) z
          (ReferenceLocalReleaseGateChronology.sourceSeed rate z rewards C_star C_h hcross)
          (ReferenceLocalReleaseGateChronology.sourceSeed_launch rate z rewards C_star C_h hcross)
          hstart
        have hlookup' : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
            ((window rate rewards C_star C_h z)[k.val].input.time) z =
            some (ReferenceAssignmentPayloadChronology.actualRunRecordAt
              (ReferenceLocalReleaseGateChronology.sourceSeed rate z rewards C_star C_h hcross)
              z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s k.val
              (by have hk' := hkCount; omega)
              ((ReferenceLocalReleaseGateChronology.canonical_seed_release_inputs
                rate z rewards C_star C_h hcross).2.1)) := by
          simpa only [s, ReferenceFirstLiveSourceStoppedReleaseEndpoint.physicalStart,
            hindexNat] using hlookup
        rw [hlookup']
        have hrunAt := ReferenceLocalReleaseGateChronology.run_record_at
          (ReferenceLocalReleaseGateChronology.sourceSeed rate z rewards C_star C_h hcross)
          z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s
          (ReferenceLocalReleaseGateChronology.canonical_seed_release_inputs
            rate z rewards C_star C_h hcross).2.1 count hspan
          ⟨k.val, by rw [← hcount]; exact hkRecords⟩
        apply congrArg some
        calc
          ReferenceAssignmentPayloadChronology.actualRunRecordAt
              (ReferenceLocalReleaseGateChronology.sourceSeed rate z rewards C_star C_h hcross)
              z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s k.val
              (by have hk' := hkCount; omega)
              ((ReferenceLocalReleaseGateChronology.canonical_seed_release_inputs
                rate z rewards C_star C_h hcross).2.1) = E.records[k.val] := by
            exact hrunAt.symm
          _ = (window rate rewards C_star C_h z)[k.val] := hget.symm
      refine ⟨?_, hactual⟩
      · simpa only [s] using htime

theorem source_window_provenance (z : Source p)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true) :
    let W := window rate rewards C_star C_h z
    W.length = 0 ∨
      ∃ hW : 0 < W.length,
      ∃ firstInstalled : CoordinatorAssignmentRegisterInstall.FirstInstallation
        (CoordinatorRoundDispatch.firstLaunchInput
          (ReferenceActivePhysicalStep.firstInput (W.get ⟨0, hW⟩).input)),
      ∃ firstSelected : ReferenceActivePhysicalStep.Selection (W.get ⟨0, hW⟩).input,
        (W.get ⟨0, hW⟩).output.preparation.coordinator.selection = some firstSelected ∧
        firstInstalled = CoordinatorAssignmentRegisterInstall.installFirst
          (CoordinatorRoundDispatch.firstLaunchInput
            (ReferenceActivePhysicalStep.firstInput ((W.get ⟨0, hW⟩).input))) ∧
        firstSelected.view.payload = firstInstalled.registers.payload ∧
        firstSelected.view.pendingAtChoice = Finset.univ ∧
        payload0 rate rewards C_star C_h z = some firstInstalled.registers.payload ∧
        (∀ k : Fin W.length,
          let r := W.get k
          ∃ selected : ReferenceActivePhysicalStep.Selection r.input,
            r.output.preparation.coordinator.selection = some selected ∧
            selected.view.payload = firstInstalled.registers.payload ∧
            (match r.input.state.coordinator with
              | .first => selected.view.pendingAtChoice = Finset.univ
              | .live incoming _ _ =>
                  selected.view.payload = incoming.payload ∧
                  selected.view.pendingAtChoice = incoming.pendingAtChoice
              | _ => False) ∧
            ∃ next : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta,
            ∃ owned : CoordinatorLiveServiceFinish.OwnedRegisters next,
            ∃ base : Fin (p.m - 1) → ℕ,
              r.output.next.coordinator = .live next owned base ∧
              next.payload = selected.view.payload ∧
              next.pendingAtChoice =
                (if ReferenceFirstLiveMissingSetProvenance.actualDownConfirmationEvent r selected then
                  selected.view.pendingAtChoice.erase
                    (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
                      (r.input.row.2 r.input.time).1)
                else selected.view.pendingAtChoice) ∧
              r.output.coordinator.failure = none ∧
              (∀ i : Fin (p.m - 1),
                ∃ choice choiceMemory nextFollower nextMemory,
                  (r.output.preparation.followers.followers i).configuration =
                    .ordinary choice choiceMemory ∧
                  (r.output.followers i).configuration =
                    .ordinary nextFollower nextMemory ∧
                  (r.output.followers i).failure = none)) := by
  classical
  dsimp
  let initial := ReferenceLocalReleaseGateChronology.sourceSeed rate z rewards C_star C_h hcross
  let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed rate z rewards C_star C_h hcross
  let s := ReferenceFirstLiveSourceStoppedReleaseEndpoint.physicalStart rate rewards C_star C_h z
  let count := p.T - s
  have hs : s ≤ p.T := by
    simpa only [s, ReferenceFirstLiveSourceStoppedReleaseEndpoint.physicalStart] using
      ReferenceCompletePhysicalHistory.physicalStart_le_T rate z rewards C_star C_h
  have hspan : s + count ≤ p.T := by dsimp [count]; omega
  have hlaunch := ReferenceLocalReleaseGateChronology.sourceSeed_launch rate z rewards C_star C_h hcross
  have hlaunch' := ReferenceFirstLaunchNumericalCell.correctedLaunch_eq_some_launchState
    rate z rewards C_star C_h hcross
  have hstate : ReferenceFirstLaunchNumericalCell.launchState rate z rewards C_star C_h hcross = initial := by
    apply Option.some.inj
    exact hlaunch'.symm.trans hlaunch
  let hcanonical := ReferenceLocalReleaseGateChronology.canonical_seed_release_inputs
    rate z rewards C_star C_h hcross
  let hactive := hcanonical.2.1
  let hfirst := hcanonical.1
  have hdecoder := ReferenceFirstLiveDownCompletionReadout.actual_corrected_decoder_seed
    rate z rewards C_star C_h hcross
  have hseedConfig : ∀ i, initial.followers i = .ordinary (seed.followers i) (seed.memory i) := by
    intro i
    simpa only [initial, seed, hstate] using seed.configuration i
  have hseedLastDown : ∀ i, (seed.followers i).lastDown = none := by
    intro i
    obtain ⟨st, mem, hst, hnone, _hunocc, _hwell, _hchron, _hstamp⟩ := hdecoder i
    have heq : st = seed.followers i := by
      exact (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
        (hst.symm.trans (hseedConfig i))).1
    rw [← heq]
    exact hnone
  have hseedUnoccupied : ∀ i, (seed.followers i).status = .unoccupied := by
    intro i
    obtain ⟨st, mem, hst, _hnone, hunocc, _hwell, _hchron, _hstamp⟩ := hdecoder i
    have heq : st = seed.followers i := by
      exact (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
        (hst.symm.trans (hseedConfig i))).1
    rw [← heq]
    exact hunocc
  let E := ReferenceActivePhysicalHorizon.run initial z.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s count hspan hactive
  let W := ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records
  have hfollower := ReferenceFirstLiveFollowerSafety.run_first_live_follower_safety
    initial z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s count hspan
    hactive hfirst seed.followers seed.memory hseedConfig seed.S_zero seed.delta_zero
    seed.backlog_zero hseedLastDown hseedUnoccupied seed.bufferValid
    seed.chronologicalBuffer seed.bufferStamps seed.decoderValid
  have hcoordinator := ReferenceFirstLiveCoordinatorSafety.run_first_live_coordinator_safety
    initial z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s count hspan
    hactive hfirst
  have hprovenance := ReferenceFirstLiveMissingSetProvenance.run_first_live_missing_set_provenance
    initial z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s count hspan
    hactive hfirst
  have hlaunch := ReferenceLocalReleaseGateChronology.sourceSeed_launch
    rate z rewards C_star C_h hcross
  have hcomplete : E.records = completeRecords rate rewards C_star C_h z := by
    change E.records = ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    exact (ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
      rate z rewards C_star C_h initial hlaunch).symm
  have hwindow : W = window rate rewards C_star C_h z := by
    change ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records =
      ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (completeRecords rate rewards C_star C_h z)
    rw [hcomplete]
  dsimp only [ReferenceActivePhysicalStep.firstInput]
  rw [← hwindow]
  rcases hprovenance with hzero | ⟨hW, firstSelected, firstInstalled, firstArm,
      hrow0first, hdispatch, hinstalled, hinitialPending, hstartPending,
      hselected0, hpayload0, hpending0, hrows⟩
  · exact Or.inl hzero
  · right
    refine ⟨hW, firstInstalled, firstSelected, hselected0, hinstalled, hpayload0,
      hpending0, ?_, ?_⟩
    · rw [payload0, ← hwindow, List.head?_eq_getElem?]
      rw [List.getElem?_eq_getElem (by omega)]
      change Option.map (fun selected => selected.view.payload)
        (W[0].output.preparation.coordinator.selection) = _
      rw [hselected0]
      simp only [Option.map_some]
      exact congrArg some hpayload0
    · intro k
      rcases hrows with ⟨_hstarted, hrows⟩
      obtain ⟨record, hrecord, selected, hselected, hpayload, hphase,
        next, nextOwned, nextBase, hnext, hnextPayload, hupdate, _hcoverage⟩ := hrows k
      subst record
      have hcoord := hcoordinator.1 k
      have hfollower' := hfollower.2 k
      refine ⟨selected, hselected, hpayload, ?_, ?_⟩
      · change (match W[k.val].input.state.coordinator with
          | .first => selected.view.pendingAtChoice = Finset.univ ∧
              selected.started.pending = Finset.univ
          | .live incoming _ _ => selected.view.payload = incoming.payload ∧
              selected.view.pendingAtChoice = incoming.pendingAtChoice ∧
              selected.started.pending = incoming.pendingAtChoice
          | _ => False) at hphase
        cases hc : (W[k.val].input.state.coordinator) <;> simp only [hc] at hphase ⊢
        · exact hphase.1
        · exact ⟨hphase.1, hphase.2.1⟩
      · refine ⟨next, nextOwned, nextBase, hnext, hnextPayload, hupdate, hcoord.1, ?_⟩
        intro i
        obtain ⟨choice, choiceMemory, nextFollower, nextMemory, hc, hn, hf⟩ := hfollower' i
        simpa only [initial, s, count] using
          (⟨choice, choiceMemory, nextFollower, nextMemory, hc, hn, hf.1⟩ : _)

private theorem crossing_of_window_nonempty (z : Source p)
    (hne : 0 < (window rate rewards C_star C_h z).length) :
    (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true := by
  cases hl : ReferenceCorrectedInitializationLaunch.correctedLaunch rate z rewards C_star C_h with
  | none =>
      rw [window_eq_nil_of_no_launch rate rewards C_star C_h z hl] at hne
      simp at hne
  | some active =>
      apply (ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
        rate z rewards C_star C_h).mp
      simp [hl]

/-- Consecutive records of the actual first-live window share the literal
computed successor state. No trace or state-chain premise is supplied. -/
theorem source_window_successor (z : Source p) (k : ℕ)
    (hk : k + 1 < (window rate rewards C_star C_h z).length) :
    (window rate rewards C_star C_h z)[k + 1].input.state =
      (window rate rewards C_star C_h z)[k].output.next := by
  have hcross := crossing_of_window_nonempty rate rewards C_star C_h z (by omega)
  let initial := ReferenceLocalReleaseGateChronology.sourceSeed rate z rewards C_star C_h hcross
  let s := ReferenceFirstLiveSourceStoppedReleaseEndpoint.physicalStart rate rewards C_star C_h z
  let count := p.T - s
  have hs : s ≤ p.T := ReferenceCompletePhysicalHistory.physicalStart_le_T
    rate z rewards C_star C_h
  have hspan : s + count ≤ p.T := by dsimp [count]; omega
  let E := ReferenceActivePhysicalHorizon.run initial z.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s count hspan
    (ReferenceLocalReleaseGateChronology.canonical_seed_release_inputs
      rate z rewards C_star C_h hcross).2.1
  have hcomplete : E.records = completeRecords rate rewards C_star C_h z :=
    (ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
      rate z rewards C_star C_h initial
      (ReferenceLocalReleaseGateChronology.sourceSeed_launch rate z rewards C_star C_h hcross)).symm
  have hprefix : window rate rewards C_star C_h z <+: E.records := by
    rw [hcomplete]
    exact List.takeWhile_prefix _
  have hk0 : k < (window rate rewards C_star C_h z).length := by omega
  have hkE : k < E.records.length := lt_of_lt_of_le hk0 hprefix.length_le
  have hkE1 : k + 1 < E.records.length := lt_of_lt_of_le hk hprefix.length_le
  have hchain := ReferenceFollowerReplyChronology.connected_drop_from_output E.connected k hkE
  rw [List.drop_eq_getElem_cons hkE1] at hchain
  have hlink := hchain.1
  calc
    _ = E.records[k + 1].input.state := congrArg
      (fun r : Record (rate := rate) => r.input.state) (hprefix.getElem hk)
    _ = E.records[k].output.next := hlink
    _ = _ := congrArg (fun r : Record (rate := rate) => r.output.next) (hprefix.getElem hk0).symm

/-- The actual next choice-time set is precisely the preceding set with the
selected follower erased on its actual positive confirmation event. -/
theorem source_window_missing_step (z : Source p) (k : ℕ)
    (hk : k + 1 < (window rate rewards C_star C_h z).length) :
    let a := (window rate rewards C_star C_h z)[k]
    let b := (window rate rewards C_star C_h z)[k + 1]
    ∃ selected : ReferenceActivePhysicalStep.Selection a.input,
      actualSelection rate a = some selected ∧
      payload0 rate rewards C_star C_h z = some selected.view.payload ∧
      missing rate b =
        if ReferenceFirstLiveMissingSetProvenance.actualDownConfirmationEvent a selected then
          (missing rate a).erase (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
            (a.input.row.2 a.input.time).1)
        else missing rate a := by
  classical
  dsimp only
  have hcross := crossing_of_window_nonempty rate rewards C_star C_h z (by omega)
  have hprov := source_window_provenance rate rewards C_star C_h z hcross
  dsimp only at hprov
  rcases hprov with hzero | ⟨hW, installed, firstSelected, _, _, _, _, hpayload0, hrows⟩
  · omega
  · simp only [List.get_eq_getElem] at hrows
    obtain ⟨sa, hsa, hpa, _hphaseA, next, owned, base, hnext, _hpnext, hupdate, _⟩ :=
      hrows ⟨k, by omega⟩
    obtain ⟨sb, hsb, _hpb, hphaseB, _⟩ := hrows ⟨k + 1, hk⟩
    have hlink := source_window_successor rate rewards C_star C_h z k hk
    have hinput : (window rate rewards C_star C_h z)[k + 1].input.state.coordinator =
        .live next owned base := (congrArg (fun st => st.coordinator) hlink).trans hnext
    rw [hinput] at hphaseB
    refine ⟨sa, hsa, ?_, ?_⟩
    · exact hpayload0.trans (congrArg some hpa.symm)
    · have hma : missing rate (window rate rewards C_star C_h z)[k] =
          sa.view.pendingAtChoice := by
        unfold missing actualSelection
        rw [hsa]
        rfl
      have hmb : missing rate (window rate rewards C_star C_h z)[k + 1] =
          sb.view.pendingAtChoice := by
        unfold missing actualSelection
        rw [hsb]
        rfl
      rw [hmb, hma]
      exact hphaseB.2.trans hupdate

/-- One-step antitonicity on the actual first-live window. -/
theorem source_window_missing_succ_subset (z : Source p) (k : ℕ)
    (hk : k + 1 < (window rate rewards C_star C_h z).length) :
    missing rate (window rate rewards C_star C_h z)[k + 1] ⊆
      missing rate (window rate rewards C_star C_h z)[k] := by
  obtain ⟨selected, _, _, hstep⟩ := source_window_missing_step rate rewards C_star C_h z k hk
  rw [hstep]
  split
  · exact Finset.erase_subset _ _
  · exact Finset.Subset.refl _

/-- Multi-step antitonicity derived from the original run's erasure updates. -/
theorem source_window_missing_antitone (z : Source p)
    (a b : Fin (window rate rewards C_star C_h z).length) (hab : a.val ≤ b.val) :
    missing rate (window rate rewards C_star C_h z)[b.val] ⊆
      missing rate (window rate rewards C_star C_h z)[a.val] := by
  have h : ∀ n, a.val ≤ n → (hn : n < (window rate rewards C_star C_h z).length) →
      missing rate (window rate rewards C_star C_h z)[n] ⊆
        missing rate (window rate rewards C_star C_h z)[a.val] := by
    intro n han
    induction n, han using Nat.le_induction with
    | base => intro _; exact Finset.Subset.refl _
    | succ n han ih =>
        intro hn
        exact (source_window_missing_succ_subset rate rewards C_star C_h z n hn).trans
          (ih (by omega))
  exact h b.val hab b.isLt

/-- Once every confirmation has arrived, the actual first-window missing
set remains empty through all its later records. -/
theorem source_window_missing_empty_persistent (z : Source p)
    (a b : Fin (window rate rewards C_star C_h z).length) (hab : a.val ≤ b.val)
    (ha : missing rate (window rate rewards C_star C_h z)[a.val] = ∅) :
    missing rate (window rate rewards C_star C_h z)[b.val] = ∅ := by
  apply Finset.subset_empty.mp
  rw [← ha]
  exact source_window_missing_antitone rate rewards C_star C_h z a b hab

/-- Supported dates retain an index in the original first-live window, the
actual nonempty incoming set, and the original first-excluded cutoff. -/
theorem supportDates_mem_iff (z : Source p) (d : ℕ) :
    d ∈ supportDates rate rewards C_star C_h z ↔
      ∃ k : Fin (window rate rewards C_star C_h z).length,
        (window rate rewards C_star C_h z)[k.val].input.time.val + 1 = d ∧
        (missing rate (window rate rewards C_star C_h z)[k.val]).Nonempty ∧
        d < ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstExcluded rate rewards C_star C_h z := by
  classical
  constructor
  · intro hd
    obtain ⟨r, hr, hdate⟩ := Finset.mem_image.mp hd
    obtain ⟨hr, hstop⟩ := Finset.mem_filter.mp hr
    obtain ⟨hr, hmissing⟩ := Finset.mem_filter.mp hr
    obtain ⟨n, hn, heq⟩ := List.mem_iff_getElem.mp (List.mem_toFinset.mp hr)
    refine ⟨⟨n, hn⟩, ?_, ?_, ?_⟩
    · exact (congrArg (fun r : Record (rate := rate) => r.input.time.val + 1) heq).trans hdate
    · simpa only [heq] using hmissing
    · simpa only [hdate] using hstop
  · rintro ⟨k, hdate, hmissing, hstop⟩
    apply Finset.mem_image.mpr
    refine ⟨(window rate rewards C_star C_h z)[k.val], ?_, hdate⟩
    apply Finset.mem_filter.mpr
    refine ⟨?_, by simpa only [hdate] using hstop⟩
    apply Finset.mem_filter.mpr
    exact ⟨List.mem_toFinset.mpr (List.getElem_mem k.isLt), hmissing⟩

/-- The actual stopped support has no calendar holes. This follows from
consecutive source dates and actual pending-set erasure, including truncation. -/
theorem supportDates_order_connected (z : Source p) (a b c : ℕ)
    (ha : a ∈ supportDates rate rewards C_star C_h z)
    (hc : c ∈ supportDates rate rewards C_star C_h z) (hab : a ≤ b) (hbc : b ≤ c) :
    b ∈ supportDates rate rewards C_star C_h z := by
  obtain ⟨i, hi, _hmi, _⟩ := (supportDates_mem_iff rate rewards C_star C_h z a).mp ha
  obtain ⟨j, hj, hmj, hstop⟩ := (supportDates_mem_iff rate rewards C_star C_h z c).mp hc
  have htimeI := (source_window_record_calendar rate rewards C_star C_h z i).1
  have htimeJ := (source_window_record_calendar rate rewards C_star C_h z j).1
  let s := ReferenceFirstLiveSourceStoppedReleaseEndpoint.physicalStart rate rewards C_star C_h z
  let n := b - (s + 1)
  have hnDate : s + n + 1 = b := by dsimp [s, n]; omega
  have hnj : n ≤ j.val := by dsimp [s] at hnDate; omega
  have hn : n < (window rate rewards C_star C_h z).length := lt_of_le_of_lt hnj j.isLt
  let k : Fin (window rate rewards C_star C_h z).length := ⟨n, hn⟩
  have htimeK := (source_window_record_calendar rate rewards C_star C_h z k).1
  have hsubset := source_window_missing_antitone rate rewards C_star C_h z k j hnj
  apply (supportDates_mem_iff rate rewards C_star C_h z b).mpr
  refine ⟨k, ?_, ?_, by omega⟩
  · dsimp [k] at htimeK ⊢
    dsimp [s] at hnDate
    omega
  · obtain ⟨f, hf⟩ := hmj
    exact ⟨f, hsubset hf⟩

/-- A nonempty stopped support contains its literal finite minimum; the
terminal sentinel cannot be its minimum in this branch. -/
theorem sigma_mem_supportDates (z : Source p)
    (hne : (supportDates rate rewards C_star C_h z).Nonempty) :
    sigma rate rewards C_star C_h z ∈ supportDates rate rewards C_star C_h z := by
  classical
  obtain ⟨d, hd⟩ := hne
  have hsigle : sigma rate rewards C_star C_h z ≤ d :=
    Finset.min'_le _ _ (Finset.mem_union_left _ hd)
  have hdT := (supportDates_member_bounds rate rewards C_star C_h z d hd).2
  have hmem := Finset.min'_mem (supportDates rate rewards C_star C_h z ∪ {p.T + 1})
    ⟨p.T + 1, Finset.mem_union_right _ (Finset.mem_singleton_self _)⟩
  rcases Finset.mem_union.mp hmem with hS | hsentinel
  · exact hS
  · have heq : sigma rate rewards C_star C_h z = p.T + 1 :=
      Finset.mem_singleton.mp hsentinel
    omega

/-- Empty support uses the original terminal sentinel for both endpoints. -/
theorem empty_support_endpoints (z : Source p)
    (hempty : supportDates rate rewards C_star C_h z = ∅) :
    sigma rate rewards C_star C_h z = p.T + 1 ∧
      theta rate rewards C_star C_h z = p.T + 1 := by
  simp [sigma, theta, hempty]

/-- Exact finite-prefix chronology of the actual stopped handover support. -/
theorem supportDates_eq_interval (z : Source p) :
    supportDates rate rewards C_star C_h z =
      Finset.Ico (sigma rate rewards C_star C_h z) (theta rate rewards C_star C_h z) := by
  classical
  apply Finset.Subset.antisymm (supportDates_subset_interval rate rewards C_star C_h z)
  intro d hd
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hd
  by_cases hne : (supportDates rate rewards C_star C_h z).Nonempty
  · have hsigmem := sigma_mem_supportDates rate rewards C_star C_h z hne
    have hmaxmem := Finset.max'_mem (supportDates rate rewards C_star C_h z) hne
    have htheta : theta rate rewards C_star C_h z =
        (supportDates rate rewards C_star C_h z).max' hne + 1 := by simp [theta, hne]
    exact supportDates_order_connected rate rewards C_star C_h z _ d _ hsigmem hmaxmem hlo
      (by rw [htheta] at hhi; omega)
  · have hempty := Finset.not_nonempty_iff_eq_empty.mp hne
    have hend := empty_support_endpoints rate rewards C_star C_h z hempty
    omega

/-- The original source calendar is injective on this same window. -/
theorem source_window_date_injective (z : Source p)
    (a b : Fin (window rate rewards C_star C_h z).length)
    (hdate : (window rate rewards C_star C_h z)[a.val].input.time.val =
      (window rate rewards C_star C_h z)[b.val].input.time.val) : a = b := by
  have ha := (source_window_record_calendar rate rewards C_star C_h z a).1
  have hb := (source_window_record_calendar rate rewards C_star C_h z b).1
  apply Fin.ext
  omega

/-- A window date is supported exactly while its actual incoming missing set
is nonempty and that same source date precedes the inherited stop. -/
theorem source_window_date_mem_support_iff (z : Source p)
    (k : Fin (window rate rewards C_star C_h z).length) :
    (window rate rewards C_star C_h z)[k.val].input.time.val + 1 ∈
        supportDates rate rewards C_star C_h z ↔
      (missing rate (window rate rewards C_star C_h z)[k.val]).Nonempty ∧
      (window rate rewards C_star C_h z)[k.val].input.time.val + 1 <
        ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstExcluded rate rewards C_star C_h z := by
  constructor
  · intro hd
    obtain ⟨j, hj, hmj, hstop⟩ := (supportDates_mem_iff rate rewards C_star C_h z _).mp hd
    have heq := source_window_date_injective rate rewards C_star C_h z j k (by omega)
    subst j
    exact ⟨hmj, hstop⟩
  · rintro ⟨hm, hstop⟩
    exact (supportDates_mem_iff rate rewards C_star C_h z _).mpr ⟨k, rfl, hm, hstop⟩

/-- On the original supported record date, the masked pending set is exactly
that record's actual choice-time missing set. -/
theorem pendingNat_eq_window_missing (z : Source p)
    (k : Fin (window rate rewards C_star C_h z).length)
    (hd : (window rate rewards C_star C_h z)[k.val].input.time.val + 1 ∈
      supportDates rate rewards C_star C_h z) :
    pendingNat rate rewards C_star C_h
        (window rate rewards C_star C_h z)[k.val].input.time.val z =
      missing rate (window rate rewards C_star C_h z)[k.val] := by
  rw [pendingNat_eq_actual_missing_on_support rate rewards C_star C_h z _
    (window rate rewards C_star C_h z)[k.val].input.time.isLt hd]
  rw [(source_window_record_calendar rate rewards C_star C_h z k).2]
  rfl

/-- Nonemptiness of the stopped pending readout is exactly membership in its
literal source-date support. -/
theorem pendingNat_nonempty_iff (z : Source p) (k : ℕ) :
    (pendingNat rate rewards C_star C_h k z).Nonempty ↔
      k + 1 ∈ supportDates rate rewards C_star C_h z := by
  constructor
  · intro hm
    by_contra hd
    rw [pendingNat_empty_when_date_not_supported rate rewards C_star C_h z k hd] at hm
    exact Finset.not_nonempty_empty hm
  · intro hd
    obtain ⟨j, hj, hmj, _⟩ := (supportDates_mem_iff rate rewards C_star C_h z _).mp hd
    have htime : (window rate rewards C_star C_h z)[j.val].input.time.val = k := by omega
    rw [← htime, pendingNat_eq_window_missing rate rewards C_star C_h z j (by simpa [htime] using hd)]
    exact hmj

/-- Actual pending-set nesting on the source phase interval. All run,
initialization, selection, and chronology facts are proved internally. -/
theorem pendingNat_antitone (z : Source p) (a b : ℕ) (hab : a ≤ b) (hb : b < p.T)
    (hstart : sigma rate rewards C_star C_h z ≤ a + 1)
    (hend : b + 1 < theta rate rewards C_star C_h z) :
    pendingNat rate rewards C_star C_h b z ⊆ pendingNat rate rewards C_star C_h a z := by
  have haS : a + 1 ∈ supportDates rate rewards C_star C_h z := by
    rw [supportDates_eq_interval]
    exact Finset.mem_Ico.mpr ⟨hstart, by omega⟩
  have hbS : b + 1 ∈ supportDates rate rewards C_star C_h z := by
    rw [supportDates_eq_interval]
    exact Finset.mem_Ico.mpr ⟨by omega, hend⟩
  obtain ⟨i, hi, _, _⟩ := (supportDates_mem_iff rate rewards C_star C_h z _).mp haS
  obtain ⟨j, hj, _, _⟩ := (supportDates_mem_iff rate rewards C_star C_h z _).mp hbS
  have hia : (window rate rewards C_star C_h z)[i.val].input.time.val = a := by omega
  have hjb : (window rate rewards C_star C_h z)[j.val].input.time.val = b := by omega
  have hical := (source_window_record_calendar rate rewards C_star C_h z i).1
  have hjcal := (source_window_record_calendar rate rewards C_star C_h z j).1
  have hij : i.val ≤ j.val := by omega
  have hpa := pendingNat_eq_window_missing rate rewards C_star C_h z i (by simpa [hia] using haS)
  have hpb : pendingNat rate rewards C_star C_h b z =
      missing rate (window rate rewards C_star C_h z)[j.val] := by
    rw [pendingNat_eq_actual_missing_on_support rate rewards C_star C_h z b hb hbS]
    have ht : (⟨b, hb⟩ : Fin p.T) =
        (window rate rewards C_star C_h z)[j.val].input.time := Fin.ext hjb.symm
    rw [ht, (source_window_record_calendar rate rewards C_star C_h z j).2]
    rfl
  rw [hia] at hpa
  rw [hpa, hpb]
  exact source_window_missing_antitone rate rewards C_star C_h z i j hij

/-- Empty windows, including no launch, have empty support and terminal
sentinels; no hypothetical live history is inserted. -/
theorem empty_window_endpoints (z : Source p)
    (hwindow : window rate rewards C_star C_h z = []) :
    supportDates rate rewards C_star C_h z = ∅ ∧
      sigma rate rewards C_star C_h z = p.T + 1 ∧
      theta rate rewards C_star C_h z = p.T + 1 := by
  have hS : supportDates rate rewards C_star C_h z = ∅ := by simp [supportDates, hwindow]
  exact ⟨hS, empty_support_endpoints rate rewards C_star C_h z hS⟩

/-- A launch at the terminal boundary has no physical handover rounds. -/
theorem terminal_launch_endpoints (z : Source p)
    (hs : ReferenceFirstLiveSourceStoppedReleaseEndpoint.physicalStart rate rewards C_star C_h z = p.T) :
    supportDates rate rewards C_star C_h z = ∅ ∧
      sigma rate rewards C_star C_h z = p.T + 1 ∧
      theta rate rewards C_star C_h z = p.T + 1 := by
  apply empty_window_endpoints
  apply List.length_eq_zero_iff.mp
  by_contra hlen
  have hn : 0 < (window rate rewards C_star C_h z).length := by omega
  let k : Fin (window rate rewards C_star C_h z).length := ⟨0, hn⟩
  have htime := (source_window_record_calendar rate rewards C_star C_h z k).1
  have hbound := (window rate rewards C_star C_h z)[k.val].input.time.isLt
  rw [hs] at htime
  omega

/-- An inherited stop at or before the first assignment date yields the
actual empty truncated branch, while physical records remain unchanged. -/
theorem prior_stop_endpoints (z : Source p)
    (hstop : ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstExcluded rate rewards C_star C_h z ≤
      ReferenceFirstLiveSourceStoppedReleaseEndpoint.physicalStart rate rewards C_star C_h z + 1) :
    supportDates rate rewards C_star C_h z = ∅ ∧
      sigma rate rewards C_star C_h z = p.T + 1 ∧
      theta rate rewards C_star C_h z = p.T + 1 := by
  have hS : supportDates rate rewards C_star C_h z = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro d hd
    obtain ⟨k, hdate, _, hbefore⟩ := (supportDates_mem_iff rate rewards C_star C_h z d).mp hd
    have htime := (source_window_record_calendar rate rewards C_star C_h z k).1
    omega
  exact ⟨hS, empty_support_endpoints rate rewards C_star C_h z hS⟩

/-- The internal deterministic handover endpoint theorem on the original
whole source, with no supplied run, law, or phase premise. -/
theorem actual_handover_interval (z : Source p) :
    supportDates rate rewards C_star C_h z =
        Finset.Ico (sigma rate rewards C_star C_h z) (theta rate rewards C_star C_h z) ∧
      1 ≤ sigma rate rewards C_star C_h z ∧
      sigma rate rewards C_star C_h z ≤ theta rate rewards C_star C_h z ∧
      theta rate rewards C_star C_h z ≤ p.T + 1 :=
  ⟨supportDates_eq_interval rate rewards C_star C_h z,
    sigma_theta_bounds rate rewards C_star C_h z⟩

/-- Every supported date retains the same actual window index, original
record lookup, first installed payload readout, and literal successor update. -/
theorem supportDates_member_provenance (z : Source p) (d : ℕ)
    (hd : d ∈ supportDates rate rewards C_star C_h z) :
    ∃ k : Fin (window rate rewards C_star C_h z).length,
      let r := (window rate rewards C_star C_h z).get k
      r.input.time.val + 1 = d ∧
      ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h r.input.time z = some r ∧
      ∃ selected : ReferenceActivePhysicalStep.Selection r.input,
        actualSelection rate r = some selected ∧
        payload0 rate rewards C_star C_h z = some selected.view.payload ∧
        missing rate r = selected.view.pendingAtChoice ∧
        (match r.input.state.coordinator with
          | .first => selected.view.pendingAtChoice = Finset.univ
          | .live incoming _ _ => selected.view.payload = incoming.payload ∧
              selected.view.pendingAtChoice = incoming.pendingAtChoice
          | _ => False) ∧
        ∃ next : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta,
        ∃ owned : CoordinatorLiveServiceFinish.OwnedRegisters next,
        ∃ base : Fin (p.m - 1) → ℕ,
          r.output.next.coordinator = .live next owned base ∧
          next.payload = selected.view.payload ∧
          next.pendingAtChoice =
            (if ReferenceFirstLiveMissingSetProvenance.actualDownConfirmationEvent r selected then
              (missing rate r).erase (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
                (r.input.row.2 r.input.time).1)
            else missing rate r) := by
  obtain ⟨k, hkdate, _, _⟩ := (supportDates_mem_iff rate rewards C_star C_h z d).mp hd
  have hcross := crossing_of_window_nonempty rate rewards C_star C_h z (by have := k.isLt; omega)
  have hprov := source_window_provenance rate rewards C_star C_h z hcross
  dsimp only at hprov
  rcases hprov with hzero | ⟨hW, installed, firstSelected, _, _, _, _, hpayload, hrows⟩
  · have := k.isLt
    omega
  · obtain ⟨selected, hselected, hp, hphase, next, owned, base, hnext, hpnext, hupdate, _⟩ := hrows k
    have hm : missing rate ((window rate rewards C_star C_h z).get k) =
        selected.view.pendingAtChoice := by
      unfold missing actualSelection
      rw [hselected]
      rfl
    refine ⟨k, hkdate, (source_window_record_calendar rate rewards C_star C_h z k).2,
      selected, hselected, hpayload.trans (congrArg some hp.symm), hm, hphase,
      next, owned, base, hnext, hpnext, ?_⟩
    rw [hm]
    exact hupdate

/-- The decoder boundary is the existing strict-past test, including the
prelaunch detector, and overflow is clipped only after its update round. -/
theorem source_window_stopped_support_iff (z : Source p)
    (k : Fin (window rate rewards C_star C_h z).length) :
    let r := (window rate rewards C_star C_h z).get k
    r.input.time.val + 1 ∈ supportDates rate rewards C_star C_h z ↔
      (missing rate r).Nonempty ∧
      (∀ n : Fin (r.input.time.val + 1),
        ReferenceFirstLiveSourceStoppedReleaseEndpoint.actualDecoderFlag rate rewards C_star C_h z
          n.val (by have hn := n.isLt; omega) = false) ∧
      r.input.time.val + 1 < ReferenceFirstLiveSourceStoppedReleaseEndpoint.overflowFirstExcluded
        rate rewards C_star C_h z := by
  dsimp only
  simp only [List.get_eq_getElem]
  rw [source_window_date_mem_support_iff]
  simp only [ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstExcluded, lt_min_iff]
  rw [ReferenceFirstLiveSourceStoppedReleaseEndpoint.decoder_cutoff_after_current_iff]

/-- At an actual first overflow date the overflow update itself remains
eligible; the next source date is excluded. -/
theorem source_window_support_at_overflow (z : Source p)
    (k : Fin (window rate rewards C_star C_h z).length) (v : ℕ)
    (hover : ReferenceFirstLiveOverflowReadout.wholeFirstLiveOverflowRound rate rewards C_star C_h z = some v) :
    let r := (window rate rewards C_star C_h z).get k
    r.input.time.val + 1 ∈ supportDates rate rewards C_star C_h z ↔
      (missing rate r).Nonempty ∧
      r.input.time.val + 1 < ReferenceFirstLiveSourceStoppedReleaseEndpoint.decoderFirstExcluded
        rate rewards C_star C_h z ∧ r.input.time.val + 1 ≤ v := by
  dsimp only
  simp only [List.get_eq_getElem]
  rw [source_window_date_mem_support_iff]
  simp only [ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstExcluded,
    ReferenceFirstLiveSourceStoppedReleaseEndpoint.overflowFirstExcluded, hover,
    Option.elim_some, lt_min_iff]
  have ht := ((window rate rewards C_star C_h z).get k).input.time.isLt
  constructor
  · rintro ⟨hm, hdec, _hT, hv⟩
    exact ⟨hm, hdec, by omega⟩
  · rintro ⟨hm, hdec, hv⟩
    exact ⟨hm, hdec, by omega, by omega⟩

/-- A supported date is the last one exactly when its successor is absent;
the endpoint is one past that date, including the terminal date. -/
theorem theta_eq_succ_of_last_supported (z : Source p) (d : ℕ)
    (hd : d ∈ supportDates rate rewards C_star C_h z)
    (hnext : d + 1 ∉ supportDates rate rewards C_star C_h z) :
    theta rate rewards C_star C_h z = d + 1 := by
  have hinside := Finset.mem_Ico.mp (supportDates_subset_interval rate rewards C_star C_h z hd)
  have hnot : ¬ (sigma rate rewards C_star C_h z ≤ d + 1 ∧
      d + 1 < theta rate rewards C_star C_h z) := by
    intro h
    apply hnext
    rw [supportDates_eq_interval]
    exact Finset.mem_Ico.mpr h
  omega

/-- The final confirmation round belongs to the support. Its actual update
erases the sole remaining follower, and the next date is the endpoint. -/
theorem last_confirmation_endpoint (z : Source p) (k : ℕ)
    (hk : k + 1 < (window rate rewards C_star C_h z).length)
    (hd : (window rate rewards C_star C_h z)[k].input.time.val + 1 ∈
      supportDates rate rewards C_star C_h z)
    (hempty : missing rate (window rate rewards C_star C_h z)[k + 1] = ∅) :
    theta rate rewards C_star C_h z = (window rate rewards C_star C_h z)[k].input.time.val + 2 ∧
      ∃ selected : ReferenceActivePhysicalStep.Selection
        (window rate rewards C_star C_h z)[k].input,
        actualSelection rate (window rate rewards C_star C_h z)[k] = some selected ∧
        ReferenceFirstLiveMissingSetProvenance.actualDownConfirmationEvent
          (window rate rewards C_star C_h z)[k] selected ∧
        missing rate (window rate rewards C_star C_h z)[k] =
          {PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
            ((window rate rewards C_star C_h z)[k].input.row.2
              (window rate rewards C_star C_h z)[k].input.time).1} := by
  classical
  have hcur := (source_window_date_mem_support_iff rate rewards C_star C_h z ⟨k, by omega⟩).mp hd
  obtain ⟨selected, hs, _, hstep⟩ := source_window_missing_step rate rewards C_star C_h z k hk
  have hevent : ReferenceFirstLiveMissingSetProvenance.actualDownConfirmationEvent
      (window rate rewards C_star C_h z)[k] selected := by
    by_contra hno
    rw [ite_eq_right hno, hempty] at hstep
    exact hcur.1.ne_empty hstep.symm
  have hsingle : missing rate (window rate rewards C_star C_h z)[k] =
      {PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
        ((window rate rewards C_star C_h z)[k].input.row.2
          (window rate rewards C_star C_h z)[k].input.time).1} := by
    rw [ite_eq_left hevent, hempty] at hstep
    exact ((Finset.erase_eq_empty_iff _ _).mp hstep.symm).resolve_left hcur.1.ne_empty
  refine ⟨?_, selected, hs, hevent, hsingle⟩
  have hcal0 := (source_window_record_calendar rate rewards C_star C_h z ⟨k, by omega⟩).1
  have hcal1 := (source_window_record_calendar rate rewards C_star C_h z ⟨k + 1, hk⟩).1
  dsimp only [Fin.val_mk] at hcal0 hcal1
  have hnext : (window rate rewards C_star C_h z)[k + 1].input.time.val + 1 ∉
      supportDates rate rewards C_star C_h z := by
    intro hn
    have hm := ((source_window_date_mem_support_iff rate rewards C_star C_h z ⟨k + 1, hk⟩).mp hn).1
    rw [hempty] at hm
    exact Finset.not_nonempty_empty hm
  have heq : (window rate rewards C_star C_h z)[k].input.time.val + 1 + 1 =
      (window rate rewards C_star C_h z)[k + 1].input.time.val + 1 := by omega
  apply theta_eq_succ_of_last_supported rate rewards C_star C_h z _ hd
  rw [heq]
  exact hnext

/-- Every retained window record precedes the first chosen cutoff, even
when a confirmation never arrives. -/
theorem source_window_no_cutoff (z : Source p)
    (k : Fin (window rate rewards C_star C_h z).length) :
    ReferenceCollectionPhaseHistory.cutoffChosen
      (window rate rewards C_star C_h z)[k.val].input = false := by
  have hmem : (window rate rewards C_star C_h z)[k.val] ∈
      (completeRecords rate rewards C_star C_h z).takeWhile
        (fun r => !ReferenceCollectionPhaseHistory.cutoffChosen r.input) :=
    List.getElem_mem k.isLt
  have hpred := List.mem_takeWhile_imp hmem
  cases hc : ReferenceCollectionPhaseHistory.cutoffChosen
      (window rate rewards C_star C_h z)[k.val].input with
  | false => rfl
  | true => simp [hc] at hpred

/-- The last physical window record ends its supported phase regardless of
whether confirmation occurs; a missing confirmation is truncated there. -/
theorem last_window_record_endpoint (z : Source p)
    (k : Fin (window rate rewards C_star C_h z).length)
    (hlast : k.val + 1 = (window rate rewards C_star C_h z).length)
    (hd : (window rate rewards C_star C_h z)[k.val].input.time.val + 1 ∈
      supportDates rate rewards C_star C_h z) :
    theta rate rewards C_star C_h z = (window rate rewards C_star C_h z)[k.val].input.time.val + 2 := by
  apply theta_eq_succ_of_last_supported rate rewards C_star C_h z _ hd
  intro hnext
  obtain ⟨j, hj, _, _⟩ := (supportDates_mem_iff rate rewards C_star C_h z _).mp hnext
  have htimeK := (source_window_record_calendar rate rewards C_star C_h z k).1
  have htimeJ := (source_window_record_calendar rate rewards C_star C_h z j).1
  have hjlt := j.isLt
  omega

/-- A supported terminal round always retains the original `T+1` sentinel. -/
theorem terminal_supported_endpoint (z : Source p)
    (hT : p.T ∈ supportDates rate rewards C_star C_h z) :
    theta rate rewards C_star C_h z = p.T + 1 := by
  have hinside := Finset.mem_Ico.mp (supportDates_subset_interval rate rewards C_star C_h z hT)
  have hbound := (sigma_theta_bounds rate rewards C_star C_h z).2.2
  omega

private theorem theta_eq_after_stop (z : Source p) (d : ℕ)
    (hd : d ∈ supportDates rate rewards C_star C_h z)
    (hstop : ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstExcluded rate rewards C_star C_h z ≤ d + 1) :
    theta rate rewards C_star C_h z = d + 1 := by
  apply theta_eq_succ_of_last_supported rate rewards C_star C_h z d hd
  intro hnext
  obtain ⟨_, _, _, hbefore⟩ := (supportDates_mem_iff rate rewards C_star C_h z _).mp hnext
  omega

/-- An actual decoder flag first visible after the supported round ends the
support after that round, including a detector inherited from initialization. -/
theorem decoder_detection_endpoint (z : Source p) (t : Fin p.T)
    (hd : t.val + 1 ∈ supportDates rate rewards C_star C_h z)
    (hflag : ReferenceFirstLiveSourceStoppedReleaseEndpoint.actualDecoderFlag rate rewards C_star C_h z
      (t.val + 1) (by have ht := t.isLt; omega) = true) :
    theta rate rewards C_star C_h z = t.val + 2 := by
  apply theta_eq_after_stop rate rewards C_star C_h z _ hd
  have hdec : ReferenceFirstLiveSourceStoppedReleaseEndpoint.decoderFirstExcluded
      rate rewards C_star C_h z ≤ t.val + 2 := by
    by_cases hnext : t.val + 1 < p.T
    · apply Finset.min'_le
      apply Finset.mem_union_left
      apply Finset.mem_image.mpr
      refine ⟨⟨t.val + 1, hnext⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hflag⟩, rfl⟩
    · have hbound := (ReferenceFirstLiveSourceStoppedReleaseEndpoint.decoderFirstExcluded_bounds
        rate rewards C_star C_h z).2
      have ht := t.isLt
      omega
  exact (min_le_left _ _).trans hdec

/-- A retained original decoder failure is counted in its detecting round;
its flag enters only the next strict-past test. Original inherited batches
and all their stamps remain those of the actual source record. -/
theorem source_window_decoder_detection_endpoint (z : Source p)
    (k : Fin (window rate rewards C_star C_h z).length)
    (hd : (window rate rewards C_star C_h z)[k.val].input.time.val + 1 ∈
      supportDates rate rewards C_star C_h z)
    (hflag : ReferenceFirstLiveDecoderPastMeasurability.retainedDecoderRecordFlag
      (ReferenceFirstLiveSourceStoppedReleaseEndpoint.physicalStart rate rewards C_star C_h z)
      (window rate rewards C_star C_h z)[k.val] = true) :
    theta rate rewards C_star C_h z = (window rate rewards C_star C_h z)[k.val].input.time.val + 2 := by
  apply decoder_detection_endpoint rate rewards C_star C_h z
    (window rate rewards C_star C_h z)[k.val].input.time hd
  simp only [ReferenceFirstLiveSourceStoppedReleaseEndpoint.actualDecoderFlag, Bool.or_eq_true]
  right
  apply (ReferenceFirstLiveDecoderPastMeasurability.strictPastDecoderFlag_eq_true_iff
    rate rewards C_star C_h _ _ _ z).mpr
  refine ⟨⟨(window rate rewards C_star C_h z)[k.val].input.time.val, by omega⟩,
    (window rate rewards C_star C_h z)[k.val], ?_, hflag⟩
  exact (source_window_record_calendar rate rewards C_star C_h z k).2

/-- The first overflowing update is included whenever its date is supported,
and the exact next source date is excluded. -/
theorem overflow_detection_endpoint (z : Source p) (v : ℕ)
    (hover : ReferenceFirstLiveOverflowReadout.wholeFirstLiveOverflowRound rate rewards C_star C_h z = some v)
    (hv : v ∈ supportDates rate rewards C_star C_h z) :
    theta rate rewards C_star C_h z = v + 1 := by
  apply theta_eq_after_stop rate rewards C_star C_h z v hv
  have hbound : ReferenceFirstLiveSourceStoppedReleaseEndpoint.overflowFirstExcluded
      rate rewards C_star C_h z ≤ v + 1 := by
    simp only [ReferenceFirstLiveSourceStoppedReleaseEndpoint.overflowFirstExcluded, hover,
      Option.elim_some]
    exact min_le_right _ _
  exact (min_le_right _ _).trans hbound

/-- The actual first installation starts with every follower missing. -/
theorem source_window_initial_missing (z : Source p)
    (hW : 0 < (window rate rewards C_star C_h z).length) :
    missing rate ((window rate rewards C_star C_h z).get ⟨0, hW⟩) = Finset.univ := by
  have hcross := crossing_of_window_nonempty rate rewards C_star C_h z hW
  have hprov := source_window_provenance rate rewards C_star C_h z hcross
  dsimp only at hprov
  rcases hprov with hzero | ⟨_, installed, selected, hselected, _, _, hpending, _⟩
  · omega
  · unfold missing actualSelection
    rw [hselected]
    exact hpending

/-- Whenever stopped handover support exists, its minimum is the actual
first assignment source date, rather than an independently chosen launch. -/
theorem sigma_eq_physicalStart_succ (z : Source p)
    (hne : (supportDates rate rewards C_star C_h z).Nonempty) :
    sigma rate rewards C_star C_h z =
      ReferenceFirstLiveSourceStoppedReleaseEndpoint.physicalStart rate rewards C_star C_h z + 1 := by
  classical
  obtain ⟨d, hd⟩ := hne
  obtain ⟨j, hj, _, hstop⟩ := (supportDates_mem_iff rate rewards C_star C_h z d).mp hd
  have htimeJ := (source_window_record_calendar rate rewards C_star C_h z j).1
  have hW : 0 < (window rate rewards C_star C_h z).length := by have := j.isLt; omega
  let k : Fin (window rate rewards C_star C_h z).length := ⟨0, hW⟩
  have htime0 : (window rate rewards C_star C_h z)[k.val].input.time.val =
      ReferenceFirstLiveSourceStoppedReleaseEndpoint.physicalStart rate rewards C_star C_h z := by
    exact (source_window_record_calendar rate rewards C_star C_h z k).1.trans (Nat.add_zero _)
  have hm0 : (missing rate (window rate rewards C_star C_h z)[k.val]).Nonempty := by
    have hm := source_window_initial_missing rate rewards C_star C_h z hW
    change missing rate (window rate rewards C_star C_h z)[k.val] = Finset.univ at hm
    rw [hm]
    exact ⟨⟨0, by have := p.two_le_m; omega⟩, Finset.mem_univ _⟩
  have hfirst := (supportDates_mem_iff rate rewards C_star C_h z
    ((window rate rewards C_star C_h z)[k.val].input.time.val + 1)).mpr
      ⟨k, rfl, hm0, by omega⟩
  have hlow := (Finset.mem_Ico.mp
    (supportDates_subset_interval rate rewards C_star C_h z hfirst)).1
  have hminmem := sigma_mem_supportDates rate rewards C_star C_h z ⟨d, hd⟩
  obtain ⟨i, hi, _, _⟩ := (supportDates_mem_iff rate rewards C_star C_h z _).mp hminmem
  have htimeI := (source_window_record_calendar rate rewards C_star C_h z i).1
  omega

/-- The outgoing update completes confirmation exactly on an actual
confirmation of the sole missing follower. This also covers the final
window/horizon record, where there is no subsequent window index. -/
theorem source_window_last_confirmation_update (z : Source p)
    (k : Fin (window rate rewards C_star C_h z).length)
    (hd : ((window rate rewards C_star C_h z).get k).input.time.val + 1 ∈
      supportDates rate rewards C_star C_h z) :
    let r := (window rate rewards C_star C_h z).get k
    ∃ selected : ReferenceActivePhysicalStep.Selection r.input,
    ∃ next : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta,
    ∃ owned : CoordinatorLiveServiceFinish.OwnedRegisters next,
    ∃ base : Fin (p.m - 1) → ℕ,
      actualSelection rate r = some selected ∧
      r.output.next.coordinator = .live next owned base ∧
      (next.pendingAtChoice = ∅ ↔
        ReferenceFirstLiveMissingSetProvenance.actualDownConfirmationEvent r selected ∧
          missing rate r = {(PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
            (r.input.row.2 r.input.time).1)}) := by
  classical
  dsimp only
  have hcross := crossing_of_window_nonempty rate rewards C_star C_h z (by have := k.isLt; omega)
  have hprov := source_window_provenance rate rewards C_star C_h z hcross
  dsimp only at hprov
  rcases hprov with hzero | ⟨_, installed, firstSelected, _, _, _, _, _, hrows⟩
  · have := k.isLt
    omega
  · obtain ⟨selected, hselected, _, _, next, owned, base, hnext, _, hupdate, _⟩ := hrows k
    have hm : missing rate ((window rate rewards C_star C_h z).get k) =
        selected.view.pendingAtChoice := by
      unfold missing actualSelection
      rw [hselected]
      rfl
    have hnonempty := ((source_window_date_mem_support_iff rate rewards C_star C_h z k).mp hd).1
    refine ⟨selected, next, owned, base, hselected, hnext, ?_⟩
    rw [hm]
    by_cases hevent : ReferenceFirstLiveMissingSetProvenance.actualDownConfirmationEvent
        ((window rate rewards C_star C_h z).get k) selected
    · rw [hupdate, ite_eq_left hevent, Finset.erase_eq_empty_iff]
      constructor
      · rintro (hzero | hsingle)
        · exact (hnonempty.ne_empty (hm.trans hzero)).elim
        · exact ⟨hevent, hsingle⟩
      · rintro ⟨_, hsingle⟩
        exact Or.inr hsingle
    · rw [hupdate, ite_eq_right hevent]
      constructor
      · intro hzero
        exact (hnonempty.ne_empty (hm.trans hzero)).elim
      · rintro ⟨hyes, _⟩
        exact (hevent hyes).elim

end Bandits.Support.ReferenceFirstLiveSourceStoppedHandoverEndpoint
